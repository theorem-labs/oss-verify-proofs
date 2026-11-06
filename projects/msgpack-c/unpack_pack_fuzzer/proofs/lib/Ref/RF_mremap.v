(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import Tac ITree Nodes SysStep SysCopy Decode.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Malloc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_F_mm_syscalls PgArith ProgR.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import F_syscalls RMallocRep.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition rmremap_entry : Z := 0x4a00c.

Definition rmremap_same_mem (B OL NL : Z) (m2 : word -> option byte) : word -> option byte :=
  if (NL <? OL)%Z then apply_unmaps m2 [(wa (B + NL), Z_to_bv 64 (OL - NL))]
  else apply_zeros m2 [(wa (B + OL), Z_to_bv 64 (NL - OL))].
Definition rmremap_move_mem (B OL NL nb : Z) (m2 : word -> option byte) : word -> option byte :=
  apply_copies m2 (apply_zeros (apply_unmaps m2 [(wa B, Z_to_bv 64 OL)]) [(wa (nb + OL), Z_to_bv 64 (NL - OL))])
               [mkCopy (wa B) (Z_to_bv 64 nb) (Z_to_bv 64 OL)].

Definition rmremap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B OL NL : Z) (avoidx avoid : list (Z * Z)) (errv canary : word) (lo : Z) (m : word -> option byte) (a : remap_ans)
    : machine_state -> Prop :=
  fun ms' =>
    match a with
    | RmErr e => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom rsegs)
        /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
        /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo (bv_unsigned sp)
        /\ rw_cells rsegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)]
        /\ (1 <= e <= 4095)%Z
    | RmSame => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None (rmremap_same_mem B OL NL m2) (seg_rom rsegs)
        /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m2
        /\ wmono rsegs m m2 /\ mem_inv rsegs m2 /\ mem_inv rsegs (rmremap_same_mem B OL NL m2)
        /\ stk rsegs (rmremap_same_mem B OL NL m2) lo (bv_unsigned sp)
        /\ rw_cells rsegs m2 (errno_addr tp) [C4 errv]
        /\ (OL <= NL -> B + NL <= alloc_ceiling /\ ranges_free avoidx (B + OL) (NL - OL) = true)%Z
    | RmAt nb => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 nb) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None (rmremap_move_mem B OL NL nb m2) (seg_rom rsegs)
        /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m2
        /\ wmono rsegs m m2 /\ mem_inv rsegs m2 /\ mem_inv rsegs (rmremap_move_mem B OL NL nb m2)
        /\ stk rsegs (rmremap_move_mem B OL NL nb m2) lo (bv_unsigned sp)
        /\ rw_cells rsegs m2 (errno_addr tp) [C4 errv]
        /\ (nb <> B /\ nb mod 4096 = 0 /\ 0 < nb /\ nb + NL <= alloc_ceiling /\ ranges_free avoid nb NL = true /\ OL < NL)%Z
    end.

Lemma rmremap_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (B OL NL : Z) (avoidx avoid : list (Z * Z)) (errv canary : word) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  rw_cells rsegs m RGOT_SSP [C8 (wz RSSP_GUARD)] ->
  rw_cells rsegs m RSSP_GUARD [C8 canary] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 B -> a1 = Z_to_bv 64 OL -> a2 = Z_to_bv 64 NL -> a3 = Z_to_bv 64 1 ->
  (0 < OL)%Z -> (0 < NL < 2^62)%Z -> OL <> NL -> (0 <= B)%Z -> (B + OL <= alloc_ceiling)%Z ->
  (B + OL <= 0x10000 \/ 0x88000 <= B)%Z ->
  (forall x k, ranges_free avoidx x k = true -> 0 < k -> x + k <= 0x10000 \/ 0x88000 <= x)%Z ->
  (forall x k, ranges_free avoid x k = true -> 0 < k -> x + k <= 0x10000 \/ 0x88000 <= x)%Z ->
  (lo <= bv_unsigned sp - 112)%Z -> (alloc_ceiling <= lo)%Z ->
  tp = Z_to_bv 64 RATP ->
  impl rsegs (at_node rsegs) (enode (NMremap B OL NL) (dec_mremap avoidx avoid B OL NL))
       (epost (rmremap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B OL NL avoidx avoid errv canary lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmremap_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST ERR GOT GRD MI -> -> -> -> OL0 NL0 ONE B0 BC BIMG AVX AV LO CEIL TPE.
  assert (TP : bv_unsigned tp = RATP) by (rewrite TPE; apply unsigned_lit; unfold RATP; lia). unfold RATP in TP. clear TPE.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU1.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
  pose proof CEIL as CEILv. pose_ceil. pose proof BC as BCv. pose_ceil.
  unfold rmremap_entry, RGOT_SSP, RSSP_GUARD in *. apply impl_enode.
  carve_frame 96%nat ST.

  do 7 step.

  step. step. change (wz 554752) with (Z_to_bv 64 554752).

  do 4 step.

  step. step. step. step.

  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. clear - K0 NL0. lia. }
  clear K0.

  step. step. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }

  step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. pose proof (dec_mremap_Some _ _ _ _ _ _ _ Hdec) as D. clear Hdec.

  assert (TAIL : forall (rv : Z) (mm : word -> option byte) (Q : machine_state -> Prop),
    (0 <= rv <= alloc_ceiling)%Z ->
    rw_cells rsegs mm (bv_unsigned sp + -96) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk))))))); C8 canary;
                                            C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra; C8 a4; C8 a5; C8 a6; C8 a7] ->
    rw_cells rsegs mm 554752 [C8 canary] ->
    stk rsegs mm lo (bv_unsigned sp + -96) ->
    (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3',
       stk rsegs mm lo (bv_unsigned sp) ->
       Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 rv) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
             F (ret_pc ra) fc None mm (seg_rom rsegs))) ->
    forall (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x28 : word),
    evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 (Z_to_bv 64 554752)
                         (Z_to_bv 64 rv) x11 x12 x13 x14 x15 x16 x17
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
                    F (Z_to_bv 64 0x4a0a4) fc None mm (seg_rom rsegs))).
  { intros rv mm Q RV FRm GRDm STm HQ. intros. pose proof CEILv as CC. pose_ceil.

    step. step. step. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
    step.

    step. step. step. step. if_cases K3; zify_cond K3. { exfalso. apply K3. reflexivity. }

    do 9 step. release_frame FRm STm (bv_unsigned sp). apply evt_done. apply HQ. exact STm. }
  destruct ans as [e| |nb].
  -
    clear MU1 TAIL. destruct D as [-> He]. unfold efferr, eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.

    step. step. step. step. if_cases K3; zify_cond K3. { exfalso. apply K3. reflexivity. }
    do 9 step. release_frame FR ST (bv_unsigned sp).
    unfold rmremap_post. finish; lia.
  -
    clear MU. destruct D as (-> & BR & COND).
    destruct (Z.ltb_spec NL OL) as [LT|GE].
    +
      rewrite nret_MSsvc, ?mkR_set_a0. simp_regs.
      lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
        let p' := eval vm_compute in (p + 4)%Z in
        replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity) end.
      rewrite apply_mem_unmaps.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (apply_unmaps ?mm _) _) => rename mm into m2 end.
      assert (Hza : (0 <= B + NL < 2^64)%Z) by lia. assert (Hzn : (0 <= OL - NL < 2^64)%Z) by lia. assert (Hzan : (B + NL + (OL - NL) <= 2^64)%Z) by lia.
      pose proof (rw_cells_unmaps_other rsegs _ _ _ Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR'.
      pose proof (rw_cells_unmaps_other rsegs _ _ _ Hza Hzn Hzan _ _ GRD ltac:(cbn; lia)) as GRD'.
      pose proof (stk_unmaps_other rsegs _ _ _ Hza Hzn Hzan _ _ ST ltac:(lia)) as ST'.
      pose proof (mem_inv_unmaps rsegs _ _ _ Hza Hzn Hzan MI) as MI'.
      set (m' := apply_unmaps m2 _) in *.
      apply (TAIL B m' _ ltac:(lia) FR' GRD' ST'). intros until t3'. intros ST2.
      unfold rmremap_post, rmremap_same_mem. replace (NL <? OL)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      do 15 eexists. split; [subst m'; reflexivity|].
      split; [exact MU1|]. split; [exact WM|]. split; [exact MI|]. split; [exact MI'|]. split; [exact ST2|]. split; [exact ERR| exact COND].
    +
      destruct (COND GE) as [BNL RFX]. pose proof (AVX _ _ RFX ltac:(lia)) as DX. pose proof BNL as BNLv. pose_ceil.
      rewrite nret_MSsvc, ?mkR_set_a0. simp_regs.
      lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
        let p' := eval vm_compute in (p + 4)%Z in
        replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity) end.
      unfold remap_tail_zs. replace (OL <? NL)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite apply_mem_zeros.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (apply_zeros ?mm _) _) => rename mm into m2 end.
      assert (Hza : (0 <= B + OL < 2^64)%Z) by lia. assert (Hzn : (0 <= NL - OL < 2^64)%Z) by lia. assert (Hzan : (B + OL + (NL - OL) <= 2^64)%Z) by lia.
      pose proof (rw_cells_zeros_other rsegs _ _ _ Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR'.
      pose proof (rw_cells_zeros_other rsegs _ _ _ Hza Hzn Hzan _ _ GRD ltac:(cbn; lia)) as GRD'.
      pose proof (stk_zeros rsegs _ _ _ Hza Hzn Hzan _ _ ST) as ST'.
      pose proof (mem_inv_zeros rsegs _ _ _ Hza Hzn Hzan MI ltac:(intros x Hx; apply ref_ro_addr_false; lia)) as MI'.
      set (m' := apply_zeros m2 _) in *.
      apply (TAIL B m' _ ltac:(lia) FR' GRD' ST'). intros until t3'. intros ST2.
      unfold rmremap_post, rmremap_same_mem. replace (NL <? OL)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      do 15 eexists. split; [subst m'; reflexivity|].
      split; [exact MU1|]. split; [exact WM|]. split; [exact MI|]. split; [exact MI'|]. split; [exact ST2|]. split; [exact ERR| exact COND].
  -
    clear MU. destruct D as (-> & NE & PG & NB0 & NBC & RF & GROW). pose proof (AV _ _ RF ltac:(lia)) as DN. pose proof NBC as NBCv. pose_ceil.
    rewrite nret_MSsvc_gen, ?mkR_set_a0. simp_regs.
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
      let p' := eval vm_compute in (p + 4)%Z in
      replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity) end.
    cbn [apply_writes].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (apply_copies ?mm _ _) _) => rename mm into m2 end.

    assert (Hua : (0 <= B < 2^64)%Z) by lia. assert (Hun : (0 <= OL < 2^64)%Z) by lia. assert (Huan : (B + OL <= 2^64)%Z) by lia.
    pose proof (rw_cells_unmaps_other rsegs _ _ _ Hua Hun Huan _ _ FR ltac:(cbn; lia)) as FRu.
    pose proof (rw_cells_unmaps_other rsegs _ _ _ Hua Hun Huan _ _ GRD ltac:(cbn; lia)) as GRDu.
    pose proof (stk_unmaps_other rsegs _ _ _ Hua Hun Huan _ _ ST ltac:(lia)) as STu.
    pose proof (mem_inv_unmaps rsegs _ _ _ Hua Hun Huan MI) as MIu.
    set (mu := apply_unmaps m2 _) in *.

    assert (Hza : (0 <= nb + OL < 2^64)%Z) by lia. assert (Hzn : (0 <= NL - OL < 2^64)%Z) by lia. assert (Hzan : (nb + OL + (NL - OL) <= 2^64)%Z) by lia.
    pose proof (rw_cells_zeros_other rsegs _ _ _ Hza Hzn Hzan _ _ FRu ltac:(cbn; lia)) as FRz.
    pose proof (rw_cells_zeros_other rsegs _ _ _ Hza Hzn Hzan _ _ GRDu ltac:(cbn; lia)) as GRDz.
    pose proof (stk_zeros rsegs _ _ _ Hza Hzn Hzan _ _ STu) as STz.
    pose proof (mem_inv_zeros rsegs _ _ _ Hza Hzn Hzan MIu ltac:(intros x Hx; apply ref_ro_addr_false; lia)) as MIz.
    set (mz := apply_zeros mu _) in *.

    assert (Hcs : (0 <= B /\ B + OL <= 2^64)%Z) by lia. assert (Hcd : (0 <= nb /\ nb + OL <= 2^64)%Z) by lia. assert (Hcl : (0 < OL < 2^64)%Z) by lia.
    pose proof (rw_cells_copies_other rsegs m2 mz _ _ _ Hcs Hcd Hcl _ _ FRz ltac:(cbn; lia)) as FR'.
    pose proof (rw_cells_copies_other rsegs m2 mz _ _ _ Hcs Hcd Hcl _ _ GRDz ltac:(cbn; lia)) as GRD'.
    pose proof (stk_copies_other rsegs m2 mz _ _ _ Hcs Hcd Hcl _ _ STz ltac:(lia)) as ST'.
    pose proof (mem_inv_copies rsegs m2 mz _ _ _ Hcs Hcd Hcl MIz ltac:(intros x Hx; apply ref_ro_addr_false; lia)) as MI'.
    set (m' := apply_copies m2 mz _) in *.
    apply (TAIL nb m' _ ltac:(lia) FR' GRD' ST'). intros until t3'. intros ST2.
    unfold rmremap_post, rmremap_move_mem.
    do 15 eexists. split; [subst m' mz mu; reflexivity|].
    split; [exact MU1|]. split; [exact WM|]. split; [exact MI|]. split; [exact MI'|]. split; [exact ST2|]. split; [exact ERR|].
    repeat split; assumption || lia.
Qed.

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysCopy OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_mm_syscalls OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.PgArith OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.ProgR.
Import F_syscalls.TwinB RMallocRep.TwinB.

Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition rmremap_entry : Z := 0x4b810.

Definition rmremap_same_mem (B OL NL : Z) (m2 : word -> option byte) : word -> option byte :=
  if (NL <? OL)%Z then apply_unmaps m2 [(wa (B + NL), Z_to_bv 64 (OL - NL))]
  else apply_zeros m2 [(wa (B + OL), Z_to_bv 64 (NL - OL))].
Definition rmremap_move_mem (B OL NL nb : Z) (m2 : word -> option byte) : word -> option byte :=
  apply_copies m2 (apply_zeros (apply_unmaps m2 [(wa B, Z_to_bv 64 OL)]) [(wa (nb + OL), Z_to_bv 64 (NL - OL))])
               [mkCopy (wa B) (Z_to_bv 64 nb) (Z_to_bv 64 OL)].

Definition rmremap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B OL NL : Z) (avoidx avoid : list (Z * Z)) (errv canary : word) (lo : Z) (m : word -> option byte) (a : remap_ans)
    : machine_state -> Prop :=
  fun ms' =>
    match a with
    | RmErr e => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom rsegs)
        /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
        /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo (bv_unsigned sp)
        /\ rw_cells rsegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)]
        /\ (1 <= e <= 4095)%Z
    | RmSame => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None (rmremap_same_mem B OL NL m2) (seg_rom rsegs)
        /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m2
        /\ wmono rsegs m m2 /\ mem_inv rsegs m2 /\ mem_inv rsegs (rmremap_same_mem B OL NL m2)
        /\ stk rsegs (rmremap_same_mem B OL NL m2) lo (bv_unsigned sp)
        /\ rw_cells rsegs m2 (errno_addr tp) [C4 errv]
        /\ (OL <= NL -> B + NL <= alloc_ceiling /\ ranges_free avoidx (B + OL) (NL - OL) = true)%Z
    | RmAt nb => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 nb) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None (rmremap_move_mem B OL NL nb m2) (seg_rom rsegs)
        /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m2
        /\ wmono rsegs m m2 /\ mem_inv rsegs m2 /\ mem_inv rsegs (rmremap_move_mem B OL NL nb m2)
        /\ stk rsegs (rmremap_move_mem B OL NL nb m2) lo (bv_unsigned sp)
        /\ rw_cells rsegs m2 (errno_addr tp) [C4 errv]
        /\ (nb <> B /\ nb mod 4096 = 0 /\ 0 < nb /\ nb + NL <= alloc_ceiling /\ ranges_free avoid nb NL = true /\ OL < NL)%Z
    end.

Lemma rmremap_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (B OL NL : Z) (avoidx avoid : list (Z * Z)) (errv canary : word) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  rw_cells rsegs m RGOT_SSP [C8 (wz RSSP_GUARD)] ->
  rw_cells rsegs m RSSP_GUARD [C8 canary] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 B -> a1 = Z_to_bv 64 OL -> a2 = Z_to_bv 64 NL -> a3 = Z_to_bv 64 1 ->
  (0 < OL)%Z -> (0 < NL < 2^62)%Z -> OL <> NL -> (0 <= B)%Z -> (B + OL <= alloc_ceiling)%Z ->
  (B + OL <= 0x10000 \/ 0x8a000 <= B)%Z ->
  (forall x k, ranges_free avoidx x k = true -> 0 < k -> x + k <= 0x10000 \/ 0x8a000 <= x)%Z ->
  (forall x k, ranges_free avoid x k = true -> 0 < k -> x + k <= 0x10000 \/ 0x8a000 <= x)%Z ->
  (lo <= bv_unsigned sp - 112)%Z -> (alloc_ceiling <= lo)%Z ->
  tp = Z_to_bv 64 RATP ->
  impl rsegs (at_node rsegs) (enode (NMremap B OL NL) (dec_mremap avoidx avoid B OL NL))
       (epost (rmremap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B OL NL avoidx avoid errv canary lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmremap_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST ERR GOT GRD MI -> -> -> -> OL0 NL0 ONE B0 BC BIMG AVX AV LO CEIL TPE.
  assert (TP : bv_unsigned tp = RATP) by (rewrite TPE; apply unsigned_lit; unfold RATP; lia). unfold RATP in TP. clear TPE.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU1.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
  pose proof CEIL as CEILv. pose_ceil. pose proof BC as BCv. pose_ceil.
  unfold rmremap_entry, RGOT_SSP, RSSP_GUARD in *. apply impl_enode.
  carve_frame 96%nat ST.

  do 7 step.

  step. step. change (wz 560896) with (Z_to_bv 64 560896).

  do 4 step.

  step. step. step. step.

  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. clear - K0 NL0. lia. }
  clear K0.

  step. step. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }

  step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. pose proof (dec_mremap_Some _ _ _ _ _ _ _ Hdec) as D. clear Hdec.

  assert (TAIL : forall (rv : Z) (mm : word -> option byte) (Q : machine_state -> Prop),
    (0 <= rv <= alloc_ceiling)%Z ->
    rw_cells rsegs mm (bv_unsigned sp + -96) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk))))))); C8 canary;
                                            C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra; C8 a4; C8 a5; C8 a6; C8 a7] ->
    rw_cells rsegs mm 560896 [C8 canary] ->
    stk rsegs mm lo (bv_unsigned sp + -96) ->
    (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3',
       stk rsegs mm lo (bv_unsigned sp) ->
       Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 rv) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
             F (ret_pc ra) fc None mm (seg_rom rsegs))) ->
    forall (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x28 : word),
    evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 (Z_to_bv 64 560896)
                         (Z_to_bv 64 rv) x11 x12 x13 x14 x15 x16 x17
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
                    F (Z_to_bv 64 0x4b8a8) fc None mm (seg_rom rsegs))).
  { intros rv mm Q RV FRm GRDm STm HQ. intros. pose proof CEILv as CC. pose_ceil.

    step. step. step. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
    step.

    step. step. step. step. if_cases K3; zify_cond K3. { exfalso. apply K3. reflexivity. }

    do 9 step. release_frame FRm STm (bv_unsigned sp). apply evt_done. apply HQ. exact STm. }
  destruct ans as [e| |nb].
  -
    clear MU1 TAIL. destruct D as [-> He]. unfold efferr, eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.

    step. step. step. step. if_cases K3; zify_cond K3. { exfalso. apply K3. reflexivity. }
    do 9 step. release_frame FR ST (bv_unsigned sp).
    unfold rmremap_post. finish; lia.
  -
    clear MU. destruct D as (-> & BR & COND).
    destruct (Z.ltb_spec NL OL) as [LT|GE].
    +
      rewrite nret_MSsvc, ?mkR_set_a0. simp_regs.
      lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
        let p' := eval vm_compute in (p + 4)%Z in
        replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity) end.
      rewrite apply_mem_unmaps.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (apply_unmaps ?mm _) _) => rename mm into m2 end.
      assert (Hza : (0 <= B + NL < 2^64)%Z) by lia. assert (Hzn : (0 <= OL - NL < 2^64)%Z) by lia. assert (Hzan : (B + NL + (OL - NL) <= 2^64)%Z) by lia.
      pose proof (rw_cells_unmaps_other rsegs _ _ _ Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR'.
      pose proof (rw_cells_unmaps_other rsegs _ _ _ Hza Hzn Hzan _ _ GRD ltac:(cbn; lia)) as GRD'.
      pose proof (stk_unmaps_other rsegs _ _ _ Hza Hzn Hzan _ _ ST ltac:(lia)) as ST'.
      pose proof (mem_inv_unmaps rsegs _ _ _ Hza Hzn Hzan MI) as MI'.
      set (m' := apply_unmaps m2 _) in *.
      apply (TAIL B m' _ ltac:(lia) FR' GRD' ST'). intros until t3'. intros ST2.
      unfold rmremap_post, rmremap_same_mem. replace (NL <? OL)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      do 15 eexists. split; [subst m'; reflexivity|].
      split; [exact MU1|]. split; [exact WM|]. split; [exact MI|]. split; [exact MI'|]. split; [exact ST2|]. split; [exact ERR| exact COND].
    +
      destruct (COND GE) as [BNL RFX]. pose proof (AVX _ _ RFX ltac:(lia)) as DX. pose proof BNL as BNLv. pose_ceil.
      rewrite nret_MSsvc, ?mkR_set_a0. simp_regs.
      lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
        let p' := eval vm_compute in (p + 4)%Z in
        replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity) end.
      unfold remap_tail_zs. replace (OL <? NL)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite apply_mem_zeros.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (apply_zeros ?mm _) _) => rename mm into m2 end.
      assert (Hza : (0 <= B + OL < 2^64)%Z) by lia. assert (Hzn : (0 <= NL - OL < 2^64)%Z) by lia. assert (Hzan : (B + OL + (NL - OL) <= 2^64)%Z) by lia.
      pose proof (rw_cells_zeros_other rsegs _ _ _ Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR'.
      pose proof (rw_cells_zeros_other rsegs _ _ _ Hza Hzn Hzan _ _ GRD ltac:(cbn; lia)) as GRD'.
      pose proof (stk_zeros rsegs _ _ _ Hza Hzn Hzan _ _ ST) as ST'.
      pose proof (mem_inv_zeros rsegs _ _ _ Hza Hzn Hzan MI ltac:(intros x Hx; apply ref_ro_addr_false; lia)) as MI'.
      set (m' := apply_zeros m2 _) in *.
      apply (TAIL B m' _ ltac:(lia) FR' GRD' ST'). intros until t3'. intros ST2.
      unfold rmremap_post, rmremap_same_mem. replace (NL <? OL)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      do 15 eexists. split; [subst m'; reflexivity|].
      split; [exact MU1|]. split; [exact WM|]. split; [exact MI|]. split; [exact MI'|]. split; [exact ST2|]. split; [exact ERR| exact COND].
  -
    clear MU. destruct D as (-> & NE & PG & NB0 & NBC & RF & GROW). pose proof (AV _ _ RF ltac:(lia)) as DN. pose proof NBC as NBCv. pose_ceil.
    rewrite nret_MSsvc_gen, ?mkR_set_a0. simp_regs.
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
      let p' := eval vm_compute in (p + 4)%Z in
      replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity) end.
    cbn [apply_writes].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (apply_copies ?mm _ _) _) => rename mm into m2 end.

    assert (Hua : (0 <= B < 2^64)%Z) by lia. assert (Hun : (0 <= OL < 2^64)%Z) by lia. assert (Huan : (B + OL <= 2^64)%Z) by lia.
    pose proof (rw_cells_unmaps_other rsegs _ _ _ Hua Hun Huan _ _ FR ltac:(cbn; lia)) as FRu.
    pose proof (rw_cells_unmaps_other rsegs _ _ _ Hua Hun Huan _ _ GRD ltac:(cbn; lia)) as GRDu.
    pose proof (stk_unmaps_other rsegs _ _ _ Hua Hun Huan _ _ ST ltac:(lia)) as STu.
    pose proof (mem_inv_unmaps rsegs _ _ _ Hua Hun Huan MI) as MIu.
    set (mu := apply_unmaps m2 _) in *.

    assert (Hza : (0 <= nb + OL < 2^64)%Z) by lia. assert (Hzn : (0 <= NL - OL < 2^64)%Z) by lia. assert (Hzan : (nb + OL + (NL - OL) <= 2^64)%Z) by lia.
    pose proof (rw_cells_zeros_other rsegs _ _ _ Hza Hzn Hzan _ _ FRu ltac:(cbn; lia)) as FRz.
    pose proof (rw_cells_zeros_other rsegs _ _ _ Hza Hzn Hzan _ _ GRDu ltac:(cbn; lia)) as GRDz.
    pose proof (stk_zeros rsegs _ _ _ Hza Hzn Hzan _ _ STu) as STz.
    pose proof (mem_inv_zeros rsegs _ _ _ Hza Hzn Hzan MIu ltac:(intros x Hx; apply ref_ro_addr_false; lia)) as MIz.
    set (mz := apply_zeros mu _) in *.

    assert (Hcs : (0 <= B /\ B + OL <= 2^64)%Z) by lia. assert (Hcd : (0 <= nb /\ nb + OL <= 2^64)%Z) by lia. assert (Hcl : (0 < OL < 2^64)%Z) by lia.
    pose proof (rw_cells_copies_other rsegs m2 mz _ _ _ Hcs Hcd Hcl _ _ FRz ltac:(cbn; lia)) as FR'.
    pose proof (rw_cells_copies_other rsegs m2 mz _ _ _ Hcs Hcd Hcl _ _ GRDz ltac:(cbn; lia)) as GRD'.
    pose proof (stk_copies_other rsegs m2 mz _ _ _ Hcs Hcd Hcl _ _ STz ltac:(lia)) as ST'.
    pose proof (mem_inv_copies rsegs m2 mz _ _ _ Hcs Hcd Hcl MIz ltac:(intros x Hx; apply ref_ro_addr_false; lia)) as MI'.
    set (m' := apply_copies m2 mz _) in *.
    apply (TAIL nb m' _ ltac:(lia) FR' GRD' ST'). intros until t3'. intros ST2.
    unfold rmremap_post, rmremap_move_mem.
    do 15 eexists. split; [subst m' mz mu; reflexivity|].
    split; [exact MU1|]. split; [exact WM|]. split; [exact MI|]. split; [exact MI'|]. split; [exact ST2|]. split; [exact ERR|].
    repeat split; assumption || lia.
Qed.

End CEIL.
End TwinB.
