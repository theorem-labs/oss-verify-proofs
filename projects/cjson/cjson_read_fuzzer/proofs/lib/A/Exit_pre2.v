(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RegsEquiv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_base.
Module Exit_pre1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RegsEquiv.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.Startup_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_base.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition funcs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x5fd2a0, 0x5fd2b8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'   (* [comment removed for export] *)
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma funcs_on_exit_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 : word),
  stk asegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp < 2^47 ->
  ATEX m ->                                                                                   (* [comment removed for export] *)
  rw_cells asegs m 0x5fd3c0 [C8 (wz 0x71918)] ->                                             (* [comment removed for export] *)
  rw_cells asegs m 0x5fd4e0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->             (* [comment removed for export] *)
  cells_at asegs m 0x13c120 [C1 (Z_to_bv 8 0)] ->                                            (* [comment removed for export] *)
  mem_inv asegs m ->
  evt asegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8e034) fc None m (seg_rom asegs)).
Proof.
  intros until tm1. intros ST LO CEIL SPH AT BA LIBC PCG MI. unfold wz in *. try rewrite alloc_ceiling_lit in CEIL.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x5fd2a0, 0x5fd2b8)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  change (cells_at asegs m 0x13c120 [C1 (Z_to_bv 8 0)]) with (ro_cells asegs m 0x13c120 [C1 (Z_to_bv 8 0)]) in PCG.
  unfold ATEX, ATEX1, ATEX2, atex_cells, A_ATEXIT, A_ATEXIT_CALL, A_AEF_GUARD, A_AEF_INIT, AINCB in AT. cbn [app] in AT.
  change (6279840 + 24) with 6279864 in AT. change (6279840 + 296) with 6280136 in AT.
  destruct AT as [((f1 & f2 & f3 & pad & j1 & AT) & _ & _)|((f1 & f2 & f3 & pad & AT) & G1 & _ & CB)].
  - (* [comment removed for export] *)
    carve_frame 48%nat ST.
    do 6 lstep. do 4 lstep.
    lstep. (* [comment removed for export] *) lstep. lstep. lstep. if_true. lstep. (* [comment removed for export] *)
    lstep. lstep. if_false. lstep. (* [comment removed for export] *)
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by reflexivity.
    steps_to 0x8e0a8%Z. (* [comment removed for export] *)
    lstep. lstep. lstep. if_false. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. if_true. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. if_true. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by reflexivity.
    lstep. lstep. lstep. if_false. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. if_true. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    do 6 lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    lstep. (* [comment removed for export] *) lstep. lstep. if_false. lstep. (* [comment removed for export] *)
    apply evt_done. unfold funcs_on_exit_post.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact ST.
  - (* [comment removed for export] *)
    carve_frame 48%nat ST.
    do 6 lstep. do 4 lstep.
    lstep. (* [comment removed for export] *) lstep. lstep. lstep. if_true. lstep. (* [comment removed for export] *)
    lstep. lstep. if_false. lstep. (* [comment removed for export] *)
    replace (sx32 (Z_to_bv 64 2)) with (Z_to_bv 64 2) by reflexivity.
    steps_to 0x8e0a8%Z. (* [comment removed for export] *)
    lstep. lstep. lstep. if_false. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. if_false. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. if_true. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by reflexivity.
    lstep. lstep. lstep. if_true. (* [comment removed for export] *)
    steps_to 0x8e0a8%Z. (* [comment removed for export] *)
    lstep. lstep. lstep. if_false. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. if_true. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. if_true. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by reflexivity.
    lstep. lstep. lstep. if_false. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. if_true. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    do 6 lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    lstep. (* [comment removed for export] *) lstep. lstep. if_false. lstep. (* [comment removed for export] *)
    apply evt_done. unfold funcs_on_exit_post.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact ST.
Time Qed.
(* [comment removed for export] *)


End CeilWrap.
(* [comment removed for export] *)
Notation mem := (word -> option byte).
End Exit_pre1.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require InitMem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module Exit_unreg.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RegsEquiv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.Startup_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.InitMem.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition unreg_cells (m : mem) : Prop :=
  ro_cells asegs m 0xaaf58 [C1 (Z_to_bv 8 1)]                 (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa7a90 [C4 (Z_to_bv 64 1)]             (* [comment removed for export] *)
  /\ ro_cells asegs m 0xaa278 [C8 (Z_to_bv 64 0x7fff8000)]    (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa9adc [C1 (Z_to_bv 8 1)]              (* [comment removed for export] *)
  /\ ro_cells asegs m 0x13be20 [C8 (Z_to_bv 64 0xffffffffffffffff)]   (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa3e08 [C8 (Z_to_bv 64 0x9b5f4)].     (* [comment removed for export] *)

Definition unreg_cell_ivs : list (Z * Z) :=
  [(0xaaf58, 0xaaf59); (0xa7a90, 0xa7a94); (0xaa278, 0xaa280); (0xa9adc, 0xa9add); (0x13be20, 0x13be28); (0xa3e08, 0xa3e10)].

Lemma unreg_cells_munch : forall W m m', unreg_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => snd iv <= 0xa3e08 \/ 0x13be28 <= fst iv
                    \/ (0xa3e10 <= fst iv /\ snd iv <= 0xa7a90) \/ (0xa7a94 <= fst iv /\ snd iv <= 0xa9adc)
                    \/ (0xa9add <= fst iv /\ snd iv <= 0xaa278) \/ (0xaa280 <= fst iv /\ snd iv <= 0xaaf58)
                    \/ (0xaaf59 <= fst iv /\ snd iv <= 0x13be20)) W ->
  unreg_cells m'.
Proof.
  intros W m m' (C1' & C2 & C3 & C4' & C5 & C6) MU WM FW.
  Ltac tr H MU WM FW := eapply ro_cells_transport; [exact H| exact MU| eapply disjoint_from_Forall; [exact FW|]; cbn; intros lo hi HH; lia].
  split; [tr C1' MU WM FW|]. split; [tr C2 MU WM FW|]. split; [tr C3 MU WM FW|].
  split; [tr C4' MU WM FW|]. split; [tr C5 MU WM FW|]. tr C6 MU WM FW.
Qed.


(* [comment removed for export] *)
Definition memset_postZ (ra : word) (sp : word) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D C N : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + N)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))].
Lemma memset_callZ : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (D C N : Z) (junk : list byte),
  rw_cells asegs m D [CB (Z.to_nat N) junk] ->
  mem_inv asegs m ->
  0 <= D < 2^64 -> 0 <= C < 2^64 -> 0 <= N < 2^64 ->
  evt asegs (memset_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D C N m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9b5f4) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros DST MI HD HC HN.
  assert (Ed : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (Ec : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (memset_spec ra sp); rewrite ?Ed, ?En; eauto. }
  intros ms' P. unfold memset_post in P. rewrite !Ed, !Ec, !En in P. exact P.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unreg_iter_post (sp gp tp s3 s5 s6 s8 : word) (F : bvmap 5 word) (fc : bv 32) (g k shb len lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (shb + len)) (Z_to_bv 64 0x13bda8) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2) s3
                  (Z_to_bv 64 (g + 64)) s5 s6 (Z_to_bv 64 0xa3e08) s8 (Z_to_bv 64 0xa7a78) (Z_to_bv 64 0xaa278) (Z_to_bv 64 (k - 1)) t3 t4 t5 t6)
             F (Z_to_bv 64 (if k =? 1 then 0x40200 else 0x3fffc)) fc None m' (seg_rom asegs)
    /\ munch [(shb, shb + len)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' shb [CB (Z.to_nat len) (repeat (Z_to_bv 8 0) (Z.to_nat len))].

Lemma unreg_iter : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (g k beg sz szrz nm md dy lc len shb lo : Z) (junk : list byte),
  unreg_cells m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp < 2^47 ->
  cells_at asegs m g [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 szrz); C8 (Z_to_bv 64 nm);
                      C8 (Z_to_bv 64 md); C8 (Z_to_bv 64 dy); C8 (Z_to_bv 64 lc); C8 (Z_to_bv 64 (2^64 - 1))] ->
  cells_at asegs m (g + 16) [C1 (Z_to_bv 8 szrz)] ->      (* [comment removed for export] *)
  0xa68a0 <= g -> g + 64 <= 0xa6ba0 -> 1 <= k <= 12 ->
  0 <= beg -> beg mod 8 = 0 -> beg + szrz <= 0x5ff000 -> (szrz = 32 \/ szrz = 64) -> len = szrz / 8 -> shb = SH beg ->
  0 <= sz < 2^64 -> 0 <= nm < 2^64 -> 0 <= md < 2^64 -> 0 <= dy < 2^64 -> 0 <= lc < 2^64 ->
  rw_cells asegs m shb [CB (Z.to_nat len) junk] ->
  evt asegs (unreg_iter_post sp gp tp s3 s5 s6 s8 F fc g k shb len lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x13bda8) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2) s3 (Z_to_bv 64 g) s5 s6
               (Z_to_bv 64 0xa3e08) s8 (Z_to_bv 64 0xa7a78) (Z_to_bv 64 0xaa278) (Z_to_bv 64 k) t3 t4 t5 t6)
          F (Z_to_bv 64 0x3fffc) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros UC MI ST CEIL LOSP SPH REC REC1 G1 G2 HK B0 B8 BHI SZRZ LEN SHE R1 R2 R3 R4 R5 SHJ.
  try rewrite alloc_ceiling_lit in CEIL.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  (nelim UC 6%nat; intros CI CR CB0 CP CT CM).
  change (cells_at asegs m g ?cs) with (ro_cells asegs m g cs) in REC.
  change (cells_at asegs m (g + 16) ?cs) with (ro_cells asegs m (g + 16) cs) in REC1.
  pose proof (munch_refl [(shb, shb + len)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHB : 0x7fff8000 <= shb /\ shb + len <= 0x7fff8000 + 0x5ff000 / 8) by (subst shb; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia).
  assert (SHE' : shb = 2147450880 + beg / 8) by (subst shb; reflexivity). clear SHE.
    lstep. (* [comment removed for export] *)
    lstep. lstep. fl. do 4 lstep. fl. (* [comment removed for export] *)
    lstep. if_false. (* [comment removed for export] *)
    lstep. fl. (* [comment removed for export] *)
    lstep. if_true. (* [comment removed for export] *)
    lstep. if_false. (* [comment removed for export] *)
    do 6 lstep. fl. (* [comment removed for export] *)
    lstep. if_cases K; zify_cond K; [ | exfalso; lia ]. clear K. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    replace (Z.land beg 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; lia).
    lstep. if_false. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    replace (Z.land (bv_unsigned (Z_to_bv 8 szrz)) 7) with 0 by (destruct SZRZ as [E|E]; rewrite E; reflexivity).
    lstep. if_false. (* [comment removed for export] *)
    lstep. lstep. lstep. fl. lstep. lstep. fl. lstep. (* [comment removed for export] *)
    lstep. if_false. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *) rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    do 4 lstep. (* [comment removed for export] *) rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    do 4 lstep. (* [comment removed for export] *)
    replace (2147450880 + (beg + szrz + -8) / 8 + 1 - (2147450880 + beg / 8)) with len by (subst len; Z.div_mod_to_equations; lia).
    replace (2147450880 + (beg + szrz + -8) / 8 + 1) with (shb + len) by (subst len shb; Z.div_mod_to_equations; lia).
    rewrite <- SHE'.
    assert (LEN8 : len = 4 \/ len = 8) by (subst len; destruct SZRZ as [-> | ->]; [left|right]; reflexivity).
    lstep. if_cases K; zify_cond K; [ | exfalso; lia ]. clear K. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    call memset_callZ; [exact SHJ | exact MI | lia | lia | lia | ].
    lstep. lstep. fl. (* [comment removed for export] *)
    lstep. if_false. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    replace (k + -1) with (k - 1) by lia.
    lstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      apply evt_done. unfold unreg_iter_post. replace (k =? 1) with true by (symmetry; apply Z.eqb_eq; lia).
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
    - apply evt_done. unfold unreg_iter_post. replace (k =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
Time Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AGLOBALS : Z := 0xa68a0.
Definition ag_beg (i : nat) : Z := nth i [0x211c0; 0x211e0; 0x21200; 0x21220; 0x21240; 0x21260; 0x21280; 0x212a0; 0x212c0; 0xa6540; 0x5dc900; 0x5dc920] 0.
Definition ag_size (i : nat) : Z := nth i [5; 6; 5; 3; 7; 4; 7; 3; 6; 24; 8; 8] 0.
Definition ag_szrz (i : nat) : Z := nth i [32; 32; 32; 32; 32; 32; 32; 32; 32; 64; 32; 32] 0.
Definition ag_name (i : nat) : Z := nth i [0x205d7; 0x1484f; 0x1374a; 0x1d0d1; 0x1880e; 0x1a556; 0x113c4; 0x166e8; 0x1f913; 0x1af14; 0x19780; 0x1b963] 0.
Definition ag_cells (i : nat) : list cell :=
  [C8 (Z_to_bv 64 (ag_beg i)); C8 (Z_to_bv 64 (ag_size i)); C8 (Z_to_bv 64 (ag_szrz i)); C8 (Z_to_bv 64 (ag_name i));
   C8 (Z_to_bv 64 0x212e0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (2^64 - 1))].

(* [comment removed for export] *)
Lemma ag_records : forall m, (forall a, AGLOBALS <= a < AGLOBALS + 768 -> m (wa a) = None) ->
  forall i, (i < 12)%nat ->
    cells_at asegs m (AGLOBALS + 64 * Z.of_nat i) (ag_cells i)
    /\ cells_at asegs m (AGLOBALS + 64 * Z.of_nat i + 16) [C1 (Z_to_bv 8 (ag_szrz i))].
Proof.
  intros m NONE i Hi.
  assert (REC : forall A cs, AGLOBALS <= A -> A + Z.of_nat (cells_size cs) <= AGLOBALS + 768 ->
            rw_bytes_b asegs A (cells_bytes cs) = true -> cells_wf cs -> cells_at asegs m A cs).
  { intros A cs HA HB Hb Hwf.
    assert (L : length (cells_bytes cs) = cells_size cs) by (apply cells_bytes_length; exact Hwf).
    pose proof (rw_cells_image0 asegs m A (cells_bytes cs)) as R. rewrite L in R.
    specialize (R ltac:(intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)); apply NONE; unfold AGLOBALS in *; lia) Hb ltac:(unfold AGLOBALS in *; lia) ltac:(unfold AGLOBALS in *; lia)).
    apply (rw_cells_recast asegs m A _ cs) in R; [exact (proj1 R)| exact Hwf| cbn; rewrite app_nil_r; reflexivity| cbn; lia]. }
  do 12 (destruct i as [|i]; [split; (apply REC; [cbn; unfold AGLOBALS; lia| cbn; unfold AGLOBALS; lia| vm_compute; reflexivity| cbn; repeat split; reflexivity])|]).
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unreg_cells2 (m : mem) : Prop :=
  ro_cells asegs m 0xa1f78 [C8 (Z_to_bv 64 0xa7a78)]           (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa1f80 [C8 (Z_to_bv 64 0xaa278)]        (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa1f88 [C8 (Z_to_bv 64 0xaaf68)]        (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa1f90 [C8 (Z_to_bv 64 0xaaf70)]        (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa1f98 [C8 (Z_to_bv 64 0xaaf60)]        (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa1f70 [C8 (Z_to_bv 64 0x13bda8)]        (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa1fa0 [C8 (Z_to_bv 64 0xa3e08)]        (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa1f60 [C8 (Z_to_bv 64 0x139d20)].       (* [comment removed for export] *)

Definition UNREG_DEPTH : Z := 176 + 1024.   (* [comment removed for export] *)

Definition unreg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - UNREG_DEPTH, bv_unsigned sp); (0xa7b30, 0xa7b38);
              (0x7fffc238, 0x7fffc25c); (0x8000cca8, 0x8000ccb0); (0x800b3920, 0x800b3928); (0x8000cd14, 0x8000cd74)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0xa7b30 [C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0x7fffc238 [CB 36 (repeat (Z_to_bv 8 0) 36)]
    /\ rw_cells asegs m' 0x8000cca8 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' 0x800b3920 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' 0x8000cd14 [CB 96 (repeat (Z_to_bv 8 0) 96)].

Lemma unreg_globals_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (jA jB jC jD : list byte),
  unreg_cells m -> unreg_cells2 m -> icpt_cells m -> poison_cells m -> mem_inv asegs m ->
  (forall a, AGLOBALS <= a < AGLOBALS + 768 -> m (wa a) = None) ->          (* [comment removed for export] *)
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + UNREG_DEPTH <= bv_unsigned sp -> bv_unsigned sp < 2^47 ->
  a0 = Z_to_bv 64 AGLOBALS -> a1 = Z_to_bv 64 12 ->
  rw_cells asegs m 0xa7b30 [C8 (Z_to_bv 64 0)] ->                          (* [comment removed for export] *)
  rw_cells asegs m 0x7fffc238 [CB 36 jA] -> rw_cells asegs m 0x8000cca8 [CB 8 jB] ->
  rw_cells asegs m 0x800b3920 [CB 8 jC] -> rw_cells asegs m 0x8000cd14 [CB 96 jD] ->
  evt asegs (unreg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3fe40) fc None m (seg_rom asegs)).
Proof.
  intros until jD. intros UC UC2 IC PC MI NONE ST CEIL LO SPH -> -> MU0 SHA SHB SHC SHD.
  try rewrite alloc_ceiling_lit in CEIL. unfold UNREG_DEPTH in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  (nelim UC2 8%nat; intros G28 G30 G38 G40 G48 G20 G50 G10).
  pose proof UC as UC0. (nelim UC 6%nat; intros CI CR CB0 CP CT CM).
  pose proof (munch_refl [(bv_unsigned sp - UNREG_DEPTH, bv_unsigned sp); (0xa7b30, 0xa7b38);
              (0x7fffc238, 0x7fffc25c); (0x8000cca8, 0x8000ccb0); (0x800b3920, 0x800b3928); (0x8000cd14, 0x8000cd74)] m) as MU.
  unfold UNREG_DEPTH in MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 176%nat ST.
  do 14 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. if_false. (* [comment removed for export] *)
  do 9 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 8 lstep. fl. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  lstep. if_false. (* [comment removed for export] *)
  lstep. fl. lstep. fl. (* [comment removed for export] *)
  amo_step. (* [comment removed for export] *)
  lstep. if_false. (* [comment removed for export] *)
  amo_step. (* [comment removed for export] *)
  lstep. if_false. (* [comment removed for export] *)
  lstep. if_true. (* [comment removed for export] *)
  lstep. lstep. lstep. if_false. (* [comment removed for export] *)
  do 7 lstep. (* [comment removed for export] *)
  do 12 lstep. (* [comment removed for export] *)
  steps_to 0x3fffc%Z.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB asegs _ _ [] 36 jA [] [4;4;4;4;4;4;4;4;4]%nat) in SHA; [| reflexivity]. cbn [mk_CB_cells app] in SHA.
  apply rw_cells_uncons in SHA as [SA0 SHA]. apply rw_cells_uncons in SHA as [SA1 SHA]. apply rw_cells_uncons in SHA as [SA2 SHA].
  apply rw_cells_uncons in SHA as [SA3 SHA]. apply rw_cells_uncons in SHA as [SA4 SHA]. apply rw_cells_uncons in SHA as [SA5 SHA].
  apply rw_cells_uncons in SHA as [SA6 SHA]. apply rw_cells_uncons in SHA as [SA7 SA8].
  apply (rw_cells_split_CB asegs _ _ [] 8 jC [] [4;4]%nat) in SHC; [| reflexivity]. cbn [mk_CB_cells app] in SHC.
  apply rw_cells_uncons in SHC as [SC0 SC1].
  Ltac fold_addr H := repeat match type of H with context [?a + Z.of_nat ?n] =>
     let v := eval vm_compute in (a + Z.of_nat n)%Z in change (a + Z.of_nat n)%Z with v in H end.
  fold_addr SA1; fold_addr SA2; fold_addr SA3; fold_addr SA4; fold_addr SA5; fold_addr SA6; fold_addr SA7; fold_addr SA8; fold_addr SC1.
  cbn [firstn skipn] in SA0, SA1, SA2, SA3, SA4, SA5, SA6, SA7, SA8, SC0, SC1.
  pose proof (ag_records m NONE) as AGR.
  Ltac call_with tac := lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ tac | post_call segs m ] end.
  (* [comment removed for export] *)
  destruct (AGR 0%nat ltac:(lia)) as [REC REC1]. cbn [ag_cells ag_beg ag_size ag_szrz ag_name nth AGLOBALS Z.of_nat Z.mul Z.add Pos.mul Pos.add Pos.of_succ_nat Pos.succ] in REC, REC1.
  name_sp sp (-176)%Z.
  call_with ltac:(eapply unreg_iter with (g := 682144) (k := 12) (beg := 135616) (sz := 5) (szrz := 32) (nm := 132567)
                      (md := 0x212e0) (dy := 0) (lc := 0) (len := 4) (shb := 2147467832) (lo := lo)).
  all: unname_sp.
  1: (eapply unreg_cells_munch; [exact UC0 | exact MU | exact WM | ]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  1: match goal with H : mem_inv asegs _ |- _ => exact H end.
  1: exact ST.
  1,2,3: first [lia | try rewrite alloc_ceiling_lit; lia].
  1: (eapply ro_cells_transport; [exact REC| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1: (eapply ro_cells_transport; [exact REC1| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1,2,3,4,5,6,7,8,9,10,11,12,13,14: first [lia | reflexivity | left; reflexivity | right; reflexivity].
  1: exact SA0.
  clear REC REC1. fl.
  change (if 12 =? 1 then 262656 else 262140) with 262140.
  match goal with H : rw_cells asegs _ 2147467832 _ |- _ => rename H into ZZ0 end.
  (* [comment removed for export] *)
  destruct (AGR 1%nat ltac:(lia)) as [REC REC1]. cbn [ag_cells ag_beg ag_size ag_szrz ag_name nth AGLOBALS Z.of_nat Z.mul Z.add Pos.mul Pos.add Pos.of_succ_nat Pos.succ] in REC, REC1.
  name_sp sp (-176)%Z.
  call_with ltac:(eapply unreg_iter with (g := 682208) (k := 11) (beg := 135648) (sz := 6) (szrz := 32) (nm := 84047)
                      (md := 0x212e0) (dy := 0) (lc := 0) (len := 4) (shb := 2147467836) (lo := lo)).
  all: unname_sp.
  1: (eapply unreg_cells_munch; [exact UC0 | exact MU | exact WM | ]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  1: match goal with H : mem_inv asegs _ |- _ => exact H end.
  1: exact ST.
  1,2,3: first [lia | try rewrite alloc_ceiling_lit; lia].
  1: (eapply ro_cells_transport; [exact REC| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1: (eapply ro_cells_transport; [exact REC1| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1,2,3,4,5,6,7,8,9,10,11,12,13,14: first [lia | reflexivity | left; reflexivity | right; reflexivity].
  1: exact SA1.
  clear REC REC1. fl.
  change (if 11 =? 1 then 262656 else 262140) with 262140.
  match goal with H : rw_cells asegs _ 2147467836 _ |- _ => rename H into ZZ1 end.
  (* [comment removed for export] *)
  destruct (AGR 2%nat ltac:(lia)) as [REC REC1]. cbn [ag_cells ag_beg ag_size ag_szrz ag_name nth AGLOBALS Z.of_nat Z.mul Z.add Pos.mul Pos.add Pos.of_succ_nat Pos.succ] in REC, REC1.
  name_sp sp (-176)%Z.
  call_with ltac:(eapply unreg_iter with (g := 682272) (k := 10) (beg := 135680) (sz := 5) (szrz := 32) (nm := 79690)
                      (md := 0x212e0) (dy := 0) (lc := 0) (len := 4) (shb := 2147467840) (lo := lo)).
  all: unname_sp.
  1: (eapply unreg_cells_munch; [exact UC0 | exact MU | exact WM | ]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  1: match goal with H : mem_inv asegs _ |- _ => exact H end.
  1: exact ST.
  1,2,3: first [lia | try rewrite alloc_ceiling_lit; lia].
  1: (eapply ro_cells_transport; [exact REC| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1: (eapply ro_cells_transport; [exact REC1| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1,2,3,4,5,6,7,8,9,10,11,12,13,14: first [lia | reflexivity | left; reflexivity | right; reflexivity].
  1: exact SA2.
  clear REC REC1. fl.
  change (if 10 =? 1 then 262656 else 262140) with 262140.
  match goal with H : rw_cells asegs _ 2147467840 _ |- _ => rename H into ZZ2 end.
  (* [comment removed for export] *)
  destruct (AGR 3%nat ltac:(lia)) as [REC REC1]. cbn [ag_cells ag_beg ag_size ag_szrz ag_name nth AGLOBALS Z.of_nat Z.mul Z.add Pos.mul Pos.add Pos.of_succ_nat Pos.succ] in REC, REC1.
  name_sp sp (-176)%Z.
  call_with ltac:(eapply unreg_iter with (g := 682336) (k := 9) (beg := 135712) (sz := 3) (szrz := 32) (nm := 118993)
                      (md := 0x212e0) (dy := 0) (lc := 0) (len := 4) (shb := 2147467844) (lo := lo)).
  all: unname_sp.
  1: (eapply unreg_cells_munch; [exact UC0 | exact MU | exact WM | ]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  1: match goal with H : mem_inv asegs _ |- _ => exact H end.
  1: exact ST.
  1,2,3: first [lia | try rewrite alloc_ceiling_lit; lia].
  1: (eapply ro_cells_transport; [exact REC| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1: (eapply ro_cells_transport; [exact REC1| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1,2,3,4,5,6,7,8,9,10,11,12,13,14: first [lia | reflexivity | left; reflexivity | right; reflexivity].
  1: exact SA3.
  clear REC REC1. fl.
  change (if 9 =? 1 then 262656 else 262140) with 262140.
  match goal with H : rw_cells asegs _ 2147467844 _ |- _ => rename H into ZZ3 end.
  (* [comment removed for export] *)
  destruct (AGR 4%nat ltac:(lia)) as [REC REC1]. cbn [ag_cells ag_beg ag_size ag_szrz ag_name nth AGLOBALS Z.of_nat Z.mul Z.add Pos.mul Pos.add Pos.of_succ_nat Pos.succ] in REC, REC1.
  name_sp sp (-176)%Z.
  call_with ltac:(eapply unreg_iter with (g := 682400) (k := 8) (beg := 135744) (sz := 7) (szrz := 32) (nm := 100366)
                      (md := 0x212e0) (dy := 0) (lc := 0) (len := 4) (shb := 2147467848) (lo := lo)).
  all: unname_sp.
  1: (eapply unreg_cells_munch; [exact UC0 | exact MU | exact WM | ]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  1: match goal with H : mem_inv asegs _ |- _ => exact H end.
  1: exact ST.
  1,2,3: first [lia | try rewrite alloc_ceiling_lit; lia].
  1: (eapply ro_cells_transport; [exact REC| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1: (eapply ro_cells_transport; [exact REC1| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1,2,3,4,5,6,7,8,9,10,11,12,13,14: first [lia | reflexivity | left; reflexivity | right; reflexivity].
  1: exact SA4.
  clear REC REC1. fl.
  change (if 8 =? 1 then 262656 else 262140) with 262140.
  match goal with H : rw_cells asegs _ 2147467848 _ |- _ => rename H into ZZ4 end.
  (* [comment removed for export] *)
  destruct (AGR 5%nat ltac:(lia)) as [REC REC1]. cbn [ag_cells ag_beg ag_size ag_szrz ag_name nth AGLOBALS Z.of_nat Z.mul Z.add Pos.mul Pos.add Pos.of_succ_nat Pos.succ] in REC, REC1.
  name_sp sp (-176)%Z.
  call_with ltac:(eapply unreg_iter with (g := 682464) (k := 7) (beg := 135776) (sz := 4) (szrz := 32) (nm := 107862)
                      (md := 0x212e0) (dy := 0) (lc := 0) (len := 4) (shb := 2147467852) (lo := lo)).
  all: unname_sp.
  1: (eapply unreg_cells_munch; [exact UC0 | exact MU | exact WM | ]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  1: match goal with H : mem_inv asegs _ |- _ => exact H end.
  1: exact ST.
  1,2,3: first [lia | try rewrite alloc_ceiling_lit; lia].
  1: (eapply ro_cells_transport; [exact REC| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1: (eapply ro_cells_transport; [exact REC1| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1,2,3,4,5,6,7,8,9,10,11,12,13,14: first [lia | reflexivity | left; reflexivity | right; reflexivity].
  1: exact SA5.
  clear REC REC1. fl.
  change (if 7 =? 1 then 262656 else 262140) with 262140.
  match goal with H : rw_cells asegs _ 2147467852 _ |- _ => rename H into ZZ5 end.
  (* [comment removed for export] *)
  destruct (AGR 6%nat ltac:(lia)) as [REC REC1]. cbn [ag_cells ag_beg ag_size ag_szrz ag_name nth AGLOBALS Z.of_nat Z.mul Z.add Pos.mul Pos.add Pos.of_succ_nat Pos.succ] in REC, REC1.
  name_sp sp (-176)%Z.
  call_with ltac:(eapply unreg_iter with (g := 682528) (k := 6) (beg := 135808) (sz := 7) (szrz := 32) (nm := 70596)
                      (md := 0x212e0) (dy := 0) (lc := 0) (len := 4) (shb := 2147467856) (lo := lo)).
  all: unname_sp.
  1: (eapply unreg_cells_munch; [exact UC0 | exact MU | exact WM | ]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  1: match goal with H : mem_inv asegs _ |- _ => exact H end.
  1: exact ST.
  1,2,3: first [lia | try rewrite alloc_ceiling_lit; lia].
  1: (eapply ro_cells_transport; [exact REC| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1: (eapply ro_cells_transport; [exact REC1| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1,2,3,4,5,6,7,8,9,10,11,12,13,14: first [lia | reflexivity | left; reflexivity | right; reflexivity].
  1: exact SA6.
  clear REC REC1. fl.
  change (if 6 =? 1 then 262656 else 262140) with 262140.
  match goal with H : rw_cells asegs _ 2147467856 _ |- _ => rename H into ZZ6 end.
  (* [comment removed for export] *)
  destruct (AGR 7%nat ltac:(lia)) as [REC REC1]. cbn [ag_cells ag_beg ag_size ag_szrz ag_name nth AGLOBALS Z.of_nat Z.mul Z.add Pos.mul Pos.add Pos.of_succ_nat Pos.succ] in REC, REC1.
  name_sp sp (-176)%Z.
  call_with ltac:(eapply unreg_iter with (g := 682592) (k := 5) (beg := 135840) (sz := 3) (szrz := 32) (nm := 91880)
                      (md := 0x212e0) (dy := 0) (lc := 0) (len := 4) (shb := 2147467860) (lo := lo)).
  all: unname_sp.
  1: (eapply unreg_cells_munch; [exact UC0 | exact MU | exact WM | ]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  1: match goal with H : mem_inv asegs _ |- _ => exact H end.
  1: exact ST.
  1,2,3: first [lia | try rewrite alloc_ceiling_lit; lia].
  1: (eapply ro_cells_transport; [exact REC| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1: (eapply ro_cells_transport; [exact REC1| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1,2,3,4,5,6,7,8,9,10,11,12,13,14: first [lia | reflexivity | left; reflexivity | right; reflexivity].
  1: exact SA7.
  clear REC REC1. fl.
  change (if 5 =? 1 then 262656 else 262140) with 262140.
  match goal with H : rw_cells asegs _ 2147467860 _ |- _ => rename H into ZZ7 end.
  (* [comment removed for export] *)
  destruct (AGR 8%nat ltac:(lia)) as [REC REC1]. cbn [ag_cells ag_beg ag_size ag_szrz ag_name nth AGLOBALS Z.of_nat Z.mul Z.add Pos.mul Pos.add Pos.of_succ_nat Pos.succ] in REC, REC1.
  name_sp sp (-176)%Z.
  call_with ltac:(eapply unreg_iter with (g := 682656) (k := 4) (beg := 135872) (sz := 6) (szrz := 32) (nm := 129299)
                      (md := 0x212e0) (dy := 0) (lc := 0) (len := 4) (shb := 2147467864) (lo := lo)).
  all: unname_sp.
  1: (eapply unreg_cells_munch; [exact UC0 | exact MU | exact WM | ]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  1: match goal with H : mem_inv asegs _ |- _ => exact H end.
  1: exact ST.
  1,2,3: first [lia | try rewrite alloc_ceiling_lit; lia].
  1: (eapply ro_cells_transport; [exact REC| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1: (eapply ro_cells_transport; [exact REC1| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1,2,3,4,5,6,7,8,9,10,11,12,13,14: first [lia | reflexivity | left; reflexivity | right; reflexivity].
  1: exact SA8.
  clear REC REC1. fl.
  change (if 4 =? 1 then 262656 else 262140) with 262140.
  match goal with H : rw_cells asegs _ 2147467864 _ |- _ => rename H into ZZ8 end.
  (* [comment removed for export] *)
  destruct (AGR 9%nat ltac:(lia)) as [REC REC1]. cbn [ag_cells ag_beg ag_size ag_szrz ag_name nth AGLOBALS Z.of_nat Z.mul Z.add Pos.mul Pos.add Pos.of_succ_nat Pos.succ] in REC, REC1.
  name_sp sp (-176)%Z.
  call_with ltac:(eapply unreg_iter with (g := 682720) (k := 3) (beg := 681280) (sz := 24) (szrz := 64) (nm := 110356)
                      (md := 0x212e0) (dy := 0) (lc := 0) (len := 8) (shb := 2147536040) (lo := lo)).
  all: unname_sp.
  1: (eapply unreg_cells_munch; [exact UC0 | exact MU | exact WM | ]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  1: match goal with H : mem_inv asegs _ |- _ => exact H end.
  1: exact ST.
  1,2,3: first [lia | try rewrite alloc_ceiling_lit; lia].
  1: (eapply ro_cells_transport; [exact REC| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1: (eapply ro_cells_transport; [exact REC1| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1,2,3,4,5,6,7,8,9,10,11,12,13,14: first [lia | reflexivity | left; reflexivity | right; reflexivity].
  1: exact SHB.
  clear REC REC1. fl.
  change (if 3 =? 1 then 262656 else 262140) with 262140.
  match goal with H : rw_cells asegs _ 2147536040 _ |- _ => rename H into ZZ9 end.
  (* [comment removed for export] *)
  destruct (AGR 10%nat ltac:(lia)) as [REC REC1]. cbn [ag_cells ag_beg ag_size ag_szrz ag_name nth AGLOBALS Z.of_nat Z.mul Z.add Pos.mul Pos.add Pos.of_succ_nat Pos.succ] in REC, REC1.
  name_sp sp (-176)%Z.
  call_with ltac:(eapply unreg_iter with (g := 682784) (k := 2) (beg := 6146304) (sz := 8) (szrz := 32) (nm := 104320)
                      (md := 0x212e0) (dy := 0) (lc := 0) (len := 4) (shb := 2148219168) (lo := lo)).
  all: unname_sp.
  1: (eapply unreg_cells_munch; [exact UC0 | exact MU | exact WM | ]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  1: match goal with H : mem_inv asegs _ |- _ => exact H end.
  1: exact ST.
  1,2,3: first [lia | try rewrite alloc_ceiling_lit; lia].
  1: (eapply ro_cells_transport; [exact REC| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1: (eapply ro_cells_transport; [exact REC1| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1,2,3,4,5,6,7,8,9,10,11,12,13,14: first [lia | reflexivity | left; reflexivity | right; reflexivity].
  1: exact SC0.
  clear REC REC1. fl.
  change (if 2 =? 1 then 262656 else 262140) with 262140.
  match goal with H : rw_cells asegs _ 2148219168 _ |- _ => rename H into ZZ10 end.
  (* [comment removed for export] *)
  destruct (AGR 11%nat ltac:(lia)) as [REC REC1]. cbn [ag_cells ag_beg ag_size ag_szrz ag_name nth AGLOBALS Z.of_nat Z.mul Z.add Pos.mul Pos.add Pos.of_succ_nat Pos.succ] in REC, REC1.
  name_sp sp (-176)%Z.
  call_with ltac:(eapply unreg_iter with (g := 682848) (k := 1) (beg := 6146336) (sz := 8) (szrz := 32) (nm := 112995)
                      (md := 0x212e0) (dy := 0) (lc := 0) (len := 4) (shb := 2148219172) (lo := lo)).
  all: unname_sp.
  1: (eapply unreg_cells_munch; [exact UC0 | exact MU | exact WM | ]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  1: match goal with H : mem_inv asegs _ |- _ => exact H end.
  1: exact ST.
  1,2,3: first [lia | try rewrite alloc_ceiling_lit; lia].
  1: (eapply ro_cells_transport; [exact REC| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1: (eapply ro_cells_transport; [exact REC1| exact MU|]; cbn [disjoint_from cells_size Cells.csize Nat.add fst snd]; repeat split; lia).
  1,2,3,4,5,6,7,8,9,10,11,12,13,14: first [lia | reflexivity | left; reflexivity | right; reflexivity].
  1: exact SC1.
  clear REC REC1. fl.
  change (if 1 =? 1 then 262656 else 262140) with 262656.
  match goal with H : rw_cells asegs _ 2148219172 _ |- _ => rename H into ZZ11 end.
  (* [comment removed for export] *)
  do 6 lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  name_sp sp (-176)%Z.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply poison_shadow_ok with (a := AGLOBALS) (sz := 768) (v := 0) (lo := lo)
                    | unfold poison_shadow_post, APOISON_STACK; change (SH AGLOBALS) with 2147536148; change (768 / 8) with 96; post_call segs mm ] end.
  all: unname_sp.
  1: (eapply icpt_cells_munch; [exact IC | exact MU | ]; unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn [fst snd disjoint_from]; lia|]); apply Forall_nil).
  1: (eapply poison_cells_munch; [exact PC | exact MU | ]; unfold poison_cell_ivs; repeat (apply Forall_cons; [cbn [fst snd disjoint_from]; lia|]); apply Forall_nil).
  1: match goal with H : mem_inv asegs _ |- _ => exact H end.
  1: exact ST.
  all: try (unfold APOISON_STACK; first [lia | try rewrite alloc_ceiling_lit; lia | reflexivity]).
  all: try (unfold AGLOBALS; first [lia | reflexivity | left; unfold lowmem_range, KLOWSHADOW_BEG; lia]).
  1: (change (SH AGLOBALS) with 2147536148; change (Z.to_nat (768 / 8)) with 96%nat; exact SHD).
  match goal with H : rw_cells asegs _ 2147536148 _ |- _ => rename H into ZZ12 end.
  (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  do 6 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RO98 : ro_cells asegs mm 0x103c8 [CB 8 [Z_to_bv 8 0xff; Z_to_bv 8 0xff; Z_to_bv 8 0x0f; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0xff; Z_to_bv 8 0xff; Z_to_bv 8 0xaf]])
      by (apply ro_cells_image; [match goal with H : mem_inv asegs _ |- _ => exact H end| vm_compute; reflexivity| lia| cbn; lia]) end.
  lstep. fl. (* [comment removed for export] *)
  do 5 lstep. fl. (* [comment removed for export] *)
  lstep. fl. lstep. fl. (* [comment removed for export] *)
  lstep. if_false. (* [comment removed for export] *)
  lstep. fl. lstep. if_true. (* [comment removed for export] *)
  do 7 lstep. fl. (* [comment removed for export] *)
  lstep. if_true. (* [comment removed for export] *)
  amo_step. (* [comment removed for export] *)
  lstep. if_false. (* [comment removed for export] *)
  amo_step. (* [comment removed for export] *)
  lstep. if_false. (* [comment removed for export] *)
  lstep. if_true. (* [comment removed for export] *)
  lstep. if_false. (* [comment removed for export] *)
  do 14 lstep. (* [comment removed for export] *)
  repeat match goal with H : stk asegs ?mm lo ?x, H' : stk asegs ?mm' lo ?x' |- _ => constr_eq mm mm'; clear H' end.
  match goal with H : stk asegs _ lo _ |- _ => rename H into STF end.
  release_frame FR STF (bv_unsigned sp).
  lstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (rw_cells_glue _ _ _ _ _ ZZ0 (rw_cells_glue _ _ _ _ _ ZZ1 (rw_cells_glue _ _ _ _ _ ZZ2 (rw_cells_glue _ _ _ _ _ ZZ3
              (rw_cells_glue _ _ _ _ _ ZZ4 (rw_cells_glue _ _ _ _ _ ZZ5 (rw_cells_glue _ _ _ _ _ ZZ6 (rw_cells_glue _ _ _ _ _ ZZ7 ZZ8
               eq_refl) eq_refl) eq_refl) eq_refl) eq_refl) eq_refl) eq_refl) eq_refl) as ZA.
  apply (rw_cells_recast asegs _ _ _ [CB 36 (repeat (Z_to_bv 8 0) 36)]) in ZA; [| cbn; repeat split; reflexivity| vm_compute; reflexivity| vm_compute; reflexivity].
  pose proof (rw_cells_glue _ _ _ _ _ ZZ10 ZZ11 eq_refl) as ZC.
  apply (rw_cells_recast asegs _ _ _ [CB 8 (repeat (Z_to_bv 8 0) 8)]) in ZC; [| cbn; repeat split; reflexivity| vm_compute; reflexivity| vm_compute; reflexivity].
  apply evt_done. unfold unreg_post.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [match goal with H : mem_inv asegs _ |- _ => exact H end|].
  split; [exact STF|]. split; [exact MU0|]. split; [exact ZA|]. split; [exact ZZ9|]. split; [exact ZC|]. exact ZZ12.
Time Qed.




End CeilWrap.
(* [comment removed for export] *)
Notation mem := (word -> option byte).
End Exit_unreg.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes Decode RegsEquiv SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.Startup_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_memset ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Exit Drv_base Drv_tac.
Import Exit_pre1.
Import Exit_unreg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

Lemma none_range_munch : forall W m m' lo hi,
  (forall a, lo <= a < hi -> m (wa a) = None) -> munch W m m' -> 0 <= lo -> hi <= 2^64 ->
  (forall a, lo <= a < hi -> outside W a) -> forall a, lo <= a < hi -> m' (wa a) = None.
Proof.
  intros W m m' lo hi HN MU Hlo Hhi HO a Ha. rewrite (MU (wa a)); [apply HN; exact Ha|].
  unfold wa. rewrite unsigned_lit by lia. apply HO. exact Ha.
Qed.

Lemma unreg_cells2_munch : forall W m m', unreg_cells2 m -> munch W m m' ->
  Forall (fun iv => snd iv <= 0xa1f60 \/ 0xa1fa8 <= fst iv) W -> unreg_cells2 m'.
Proof.
  intros W m m' (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) MU FW.
  Ltac tr H MU FW := eapply ro_cells_transport; [exact H| exact MU| eapply disjoint_from_Forall; [exact FW|]; cbn; intros lo hi HH; lia].
  split; [tr G1 MU FW|]. split; [tr G2 MU FW|]. split; [tr G3 MU FW|]. split; [tr G4 MU FW|].
  split; [tr G5 MU FW|]. split; [tr G6 MU FW|]. split; [tr G7 MU FW|]. tr G8 MU FW.
Qed.

(* [comment removed for export] *)
Definition fini_cells (m : mem) : Prop :=
  ro_cells asegs m 0xa2c38 [C8 (Z_to_bv 64 0xa19b8); C8 (Z_to_bv 64 0xa19a8)]     (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa19a8 [C8 (Z_to_bv 64 0x87654); C8 (Z_to_bv 64 0x30d6c)]   (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa1f50 [C8 (Z_to_bv 64 0x8e0fc); C8 (Z_to_bv 64 0)]        (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa3c80 [C8 (Z_to_bv 64 0xa3c80)]                             (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa2bf8 [C8 (Z_to_bv 64 0xa68a0); C8 (Z_to_bv 64 0xa6ba0)].  (* [comment removed for export] *)

Lemma fini_cells_munch : forall W m m', fini_cells m -> munch W m m' ->
  Forall (fun iv => snd iv <= 0xa19a8 \/ 0xa3c88 <= fst iv \/ (0xa19b8 <= fst iv /\ snd iv <= 0xa1f50)
                    \/ (0xa1f60 <= fst iv /\ snd iv <= 0xa2bf8) \/ (0xa2c08 <= fst iv /\ snd iv <= 0xa2c38)
                    \/ (0x149e08 <= fst iv /\ snd iv <= 0xa3c80)) W ->
  fini_cells m'.
Proof.
  intros W m m' (G1 & G2 & G3 & G4 & G5) MU FW.
  split; [tr G1 MU FW|]. split; [tr G2 MU FW|]. split; [tr G3 MU FW|]. split; [tr G4 MU FW|]. tr G5 MU FW.
Qed.

Definition FINI_DEPTH : Z := 64 + UNREG_DEPTH.   (* [comment removed for export] *)

Definition libc_exit_fini_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - FINI_DEPTH, bv_unsigned sp); (0xa6c10, 0xa6c11); (0xa6bc0, 0xa6bc8); (0xa7b30, 0xa7b38);
              (0x7fffc238, 0x7fffc25c); (0x8000cca8, 0x8000ccb0); (0x800b3920, 0x800b3928); (0x8000cd14, 0x8000cd74)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0xa6c10 [C1 (Z_to_bv 8 1)]
    /\ rw_cells asegs m' 0xa6bc0 [C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0xa7b30 [C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0x7fffc238 [CB 36 (repeat (Z_to_bv 8 0) 36)]
    /\ rw_cells asegs m' 0x8000cca8 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' 0x800b3920 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' 0x8000cd14 [CB 96 (repeat (Z_to_bv 8 0) 96)].

Lemma libc_exit_fini_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (jA jB jC jD : list byte),
  fini_cells m -> unreg_cells m -> unreg_cells2 m -> icpt_cells m -> poison_cells m -> mem_inv asegs m ->
  (forall a, AGLOBALS <= a < AGLOBALS + 768 -> m (wa a) = None) ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + FINI_DEPTH <= bv_unsigned sp -> bv_unsigned sp < 2^47 ->
  rw_cells asegs m 0xa6c10 [C1 (Z_to_bv 8 0)] ->                                 (* [comment removed for export] *)
  rw_cells asegs m 0xa6bc0 [C8 (Z_to_bv 64 1)] ->                                (* [comment removed for export] *)
  rw_cells asegs m 0xa7b30 [C8 (Z_to_bv 64 0)] ->                                (* [comment removed for export] *)
  rw_cells asegs m 0x7fffc238 [CB 36 jA] -> rw_cells asegs m 0x8000cca8 [CB 8 jB] ->
  rw_cells asegs m 0x800b3920 [CB 8 jC] -> rw_cells asegs m 0x8000cd14 [CB 96 jD] ->
  evt asegs (libc_exit_fini_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8e1cc) fc None m (seg_rom asegs)).
Proof.
  intros until jD. intros FC UC UC2 IC PC MI NONE ST CEIL LO SPH FIN REG MUT SHA SHB SHC SHD.
  try rewrite alloc_ceiling_lit in CEIL. unfold FINI_DEPTH, UNREG_DEPTH in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  (nelim FC 5%nat; intros GFA FAR GCX DSO GAG).
  pose proof (munch_refl [(bv_unsigned sp - FINI_DEPTH, bv_unsigned sp); (0xa6c10, 0xa6c11); (0xa6bc0, 0xa6bc8); (0xa7b30, 0xa7b38);
              (0x7fffc238, 0x7fffc25c); (0x8000cca8, 0x8000ccb0); (0x800b3920, 0x800b3928); (0x8000cd14, 0x8000cd74)] m) as MU.
  unfold FINI_DEPTH, UNREG_DEPTH in MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 32%nat ST.
  sepM. do 4 lstep. (* [comment removed for export] *)
  do 4 lstep. (* [comment removed for export] *)
  lstep. if_false. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 4 lstep. (* [comment removed for export] *)
  do 3 lstep. fl. lstep. fl. (* [comment removed for export] *)
  lstep. if_true. (* [comment removed for export] *)
  do 4 lstep. (* [comment removed for export] *)
  do 2 lstep. (* [comment removed for export] *)
  lstep. if_false. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) do 3 lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) do 2 lstep. (* [comment removed for export] *)
  lstep. if_true. (* [comment removed for export] *)
  do 3 lstep. (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -32).
  lstep. (* [comment removed for export] *)
  lstep. lstep. if_true. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 2 lstep. (* [comment removed for export] *)
  do 6 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 3 lstep. (* [comment removed for export] *)
  lstep. if_false. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. if_false. (* [comment removed for export] *)
  lstep. fl. lstep. fl. (* [comment removed for export] *)
  lstep. if_false. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  name_sp sp (-64)%Z.
  sepM. callxp ltac:(eapply unreg_globals_spec with (lo := lo)) ltac:(unfold unreg_post, UNREG_DEPTH; clear SHD SHC SHB SHA MUT).
  all: unname_sp.
  1: (eapply unreg_cells_munch; [exact UC | exact MU | exact WM | ]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  1: (eapply unreg_cells2_munch; [exact UC2 | exact MU | ]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  1: (eapply icpt_cells_munch; [exact IC | exact MU | ]; unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn [fst snd disjoint_from]; (lia_on CEIL LO)|]); apply Forall_nil).
  1: (eapply poison_cells_munch; [exact PC | exact MU | ]; unfold poison_cell_ivs; repeat (apply Forall_cons; [cbn [fst snd disjoint_from]; (lia_on CEIL LO)|]); apply Forall_nil).
  1: match goal with H : mem_inv asegs _ |- _ => exact H end.
  1: (eapply none_range_munch; [exact NONE | exact MU | unfold AGLOBALS; lia | unfold AGLOBALS; lia | unfold AGLOBALS; cbn [outside fst snd]; intros; lia]).
  1: exact ST.
  1,2,3: first [lia | try rewrite alloc_ceiling_lit; lia | unfold UNREG_DEPTH; lia].
  1,2: reflexivity.
  1: exact MUT. 1: exact SHA. 1: exact SHB. 1: exact SHC. 1: exact SHD.
  restk lo ST.
  match goal with H : rw_cells asegs _ 0xa7b30 _ |- _ => rename H into MUT' end.
  match goal with H : rw_cells asegs _ 0x7fffc238 _ |- _ => rename H into SHA' end.
  match goal with H : rw_cells asegs _ 0x8000cca8 _ |- _ => rename H into SHB' end.
  match goal with H : rw_cells asegs _ 0x800b3920 _ |- _ => rename H into SHC' end.
  match goal with H : rw_cells asegs _ 0x8000cd14 _ |- _ => rename H into SHD' end.
  (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 3 lstep. (* [comment removed for export] *)
  release_frame FR1 ST (bv_unsigned sp + -48).
  lstep. (* [comment removed for export] *)
  do 2 lstep. release_frame FR0 ST (bv_unsigned sp + -32). lstep. (* [comment removed for export] *)
  lstep. lstep. if_false. (* [comment removed for export] *)
  do 4 lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  lstep. lstep. (* [comment removed for export] *)
  apply evt_done. unfold libc_exit_fini_post.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [match goal with H : mem_inv asegs _ |- _ => exact H end|].
  split; [exact ST|]. split; [exact FIN|]. split; [exact REG|]. split; [exact MUT'|]. split; [exact SHA'|]. split; [exact SHB'|]. split; [exact SHC'|]. exact SHD'.
Time Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AEXIT_PRE_DEPTH : Z := 16 + FINI_DEPTH.

Definition aexit_prefix_post (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code t : Z) (ra : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x8e284) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 code) s1
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 AF_STDIO_EXIT) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - AEXIT_PRE_DEPTH, bv_unsigned sp); (0x5fd4c0, 0x5fd4c4); (0x5fd2a0, 0x5fd2b8);
              (0xa6c10, 0xa6c11); (0xa6bc0, 0xa6bc8); (0xa7b30, 0xa7b38);
              (0x7fffc238, 0x7fffc25c); (0x8000cca8, 0x8000ccb0); (0x800b3920, 0x800b3928); (0x8000cd14, 0x8000cd74)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -16)
    /\ rw_cells asegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells asegs m' ATIDCELL [C4 (Z_to_bv 64 t)]
    /\ rw_cells asegs m' 0x5fd4c0 [C4 (Z_to_bv 64 t)]
    /\ rw_cells asegs m' 0xa6c10 [C1 (Z_to_bv 8 1)]
    /\ rw_cells asegs m' 0xa6bc0 [C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0xa7b30 [C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0x7fffc238 [CB 36 (repeat (Z_to_bv 8 0) 36)]
    /\ rw_cells asegs m' 0x8000cca8 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' 0x800b3920 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' 0x8000cd14 [CB 96 (repeat (Z_to_bv 8 0) 96)].

Lemma aexit_prefix_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo code t : Z) (cdt thr sec : byte) (tm1 : word)
    (jA jB jC jD : list byte),
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AEXIT_PRE_DEPTH <= bv_unsigned sp -> bv_unsigned sp < 2^47 ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 code -> 0 <= code < 2^32 -> 0 < t < 2^22 ->
  rw_cells asegs m ATIDCELL [C4 (Z_to_bv 64 t)] ->                                               (* [comment removed for export] *)
  rw_cells asegs m 0x5fd4c0 [C4 (Z_to_bv 64 0)] ->                                               (* [comment removed for export] *)
  ATEX m ->                                                                                      (* [comment removed for export] *)
  rw_cells asegs m 0x5fd3c0 [C8 (Z_to_bv 64 0x71918)] ->                                         (* [comment removed for export] *)
  rw_cells asegs m 0x5fd4e0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->                (* [comment removed for export] *)
  cells_at asegs m 0x13c120 [C1 (Z_to_bv 8 0)] ->                                               (* [comment removed for export] *)
  fini_cells m -> unreg_cells m -> unreg_cells2 m -> icpt_cells m -> poison_cells m ->
  (forall a, AGLOBALS <= a < AGLOBALS + 768 -> m (wa a) = None) ->
  rw_cells asegs m 0xa6c10 [C1 (Z_to_bv 8 0)] -> rw_cells asegs m 0xa6bc0 [C8 (Z_to_bv 64 1)] -> rw_cells asegs m 0xa7b30 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x7fffc238 [CB 36 jA] -> rw_cells asegs m 0x8000cca8 [CB 8 jB] ->
  rw_cells asegs m 0x800b3920 [CB 8 jC] -> rw_cells asegs m 0x8000cd14 [CB 96 jD] ->
  mem_inv asegs m ->
  evt asegs (aexit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t ra m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AEXIT) fc None m (seg_rom asegs)).
Proof.
  intros until jD. intros ST CEIL LO SPH -> -> CODE TID TIDC EXL ATX BA LIBC PCG FC UC UC2 IC PC NONE FIN REG MUT SHA SHB SHC SHD MI.
  try rewrite alloc_ceiling_lit in CEIL. unfold AEXIT_PRE_DEPTH, FINI_DEPTH, UNREG_DEPTH in LO. unfold ATIDCELL in TIDC. unfold AEXIT, ATP.
  change (cells_at asegs m 0x13c120 ?cs) with (ro_cells asegs m 0x13c120 cs) in PCG.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - AEXIT_PRE_DEPTH, bv_unsigned sp); (0x5fd4c0, 0x5fd4c4); (0x5fd2a0, 0x5fd2b8);
              (0xa6c10, 0xa6c11); (0xa6bc0, 0xa6bc8); (0xa7b30, 0xa7b38);
              (0x7fffc238, 0x7fffc25c); (0x8000cca8, 0x8000ccb0); (0x800b3920, 0x800b3928); (0x8000cd14, 0x8000cd74)] m) as MU.
  unfold AEXIT_PRE_DEPTH, FINI_DEPTH, UNREG_DEPTH in MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (0x5fd4c0, 0x5fd4c0 + 4)] m) as MU2.   (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 3 lstep. (* [comment removed for export] *)
  do 3 lstep. (* [comment removed for export] *)
  replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t) by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
  do 2 lstep. (* [comment removed for export] *)
  amo_step. (* [comment removed for export] *) fl.
  lstep. if_false. (* [comment removed for export] *)
  amo_step. (* [comment removed for export] *)
  lstep. if_false. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. (* [comment removed for export] *)
  lstep. if_true. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  name_sp sp (-16)%Z.
  callxp ltac:(eapply funcs_on_exit_spec with (lo := lo)) ltac:(unfold funcs_on_exit_post; clear ATX MU2).
  all: unname_sp.
  1: exact ST.
  1,2,3: first [lia | try rewrite alloc_ceiling_lit; lia].
  1: (eapply ATEX_munch; [exact ATX| exact MU2| exact WM|];
      repeat (apply Forall_cons; [cbn [fst snd]; unfold atex_addr, A_ATEXIT, A_AEF_INIT, AINCB; intros; lia|]); apply Forall_nil).
  1: exact BA. 1: exact LIBC. 1: exact PCG.
  1: match goal with H : mem_inv asegs _ |- _ => exact H end.
  restk lo ST1.
  lstep. (* [comment removed for export] *)
  name_sp sp (-16)%Z.
  sepM. callxp ltac:(eapply libc_exit_fini_spec with (lo := lo)) ltac:(unfold libc_exit_fini_post, FINI_DEPTH, UNREG_DEPTH; clear SHD SHC SHB SHA MUT REG FIN).
  all: unname_sp.
  1: (eapply fini_cells_munch; [exact FC | exact MU | ]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  1: (eapply unreg_cells_munch; [exact UC | exact MU | exact WM | ]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  1: (eapply unreg_cells2_munch; [exact UC2 | exact MU | ]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  1: (eapply icpt_cells_munch; [exact IC | exact MU | ]; unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn [fst snd disjoint_from]; (lia_on CEIL LO)|]); apply Forall_nil).
  1: (eapply poison_cells_munch; [exact PC | exact MU | ]; unfold poison_cell_ivs; repeat (apply Forall_cons; [cbn [fst snd disjoint_from]; (lia_on CEIL LO)|]); apply Forall_nil).
  1: match goal with H : mem_inv asegs _ |- _ => exact H end.
  1: (eapply none_range_munch; [exact NONE | exact MU | unfold AGLOBALS; lia | unfold AGLOBALS; lia | unfold AGLOBALS; cbn [outside fst snd]; intros; lia]).
  1: exact ST1.
  1,2,3: first [lia | try rewrite alloc_ceiling_lit; lia | unfold FINI_DEPTH, UNREG_DEPTH; lia].
  1: exact FIN. 1: exact REG. 1: exact MUT. 1: exact SHA. 1: exact SHB. 1: exact SHC. 1: exact SHD.
  restk lo ST2.
  lstep. (* [comment removed for export] *)
  apply evt_done. unfold aexit_prefix_post.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [match goal with H : mem_inv asegs _ |- _ => exact H end|].
  split; [exact ST2|]. split; [exact FR|]. split; [exact TIDC|]. split; [exact EXL|].
  repeat match goal with |- _ /\ _ => split end.
  all: match goal with |- rw_cells asegs _ ?a _ => match goal with H : rw_cells asegs _ a _ |- _ => exact H end end.
Time Qed.


End CeilWrap.
(* [comment removed for export] *)
Notation mem := (word -> option byte).
