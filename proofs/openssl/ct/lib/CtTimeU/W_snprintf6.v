(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad PrintfModel PrintfModelX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib F_pop_arg F_printf_iface F_vsnprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac W_snprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma snprintf_gen_spec6 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D n A lo : Z) (dn : nat) (junkd : list byte) (canary : word) (fmt : list Z) (args : list parg) (o : list Z)
    (st0 : word),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - SNPRINTF_STACK)%Z -> (bv_unsigned sp + 8 <= 2^63)%Z ->
  ssp_cells m canary -> frm0 fc ->
  rw_cells ctusegs m D [CB dn junkd] -> (D + Z.of_nat dn <= lo \/ bv_unsigned sp + 8 <= D)%Z -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D)%Z -> (D + Z.of_nat dn <= 2^63)%Z ->
  (zlength o <= n - 1)%Z -> (1 <= n < 2^63)%Z ->
  rw_cells ctusegs m (bv_unsigned sp) [C8 st0] ->
  sng_call_ok m lo (bv_unsigned sp) D dn A fmt [a3; a4; a5; a6; a7; st0] args o ->
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A ->
  evt ctusegs (sng_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo D dn canary (zlength o)
                 (fun m' => rw_cells ctusegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)]) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SNPRINTF) fc None m (seg_rom ctusegs)).
Proof.
  intros until st0. intros ST MI GLO LO SP63 [SSP1 SSP2] FRM HD DLO DGT DHI ON NR HST (HF & FB & P1 & AR & AOK & MODEL & FPC & OLEN) -> -> ->.
  unfold SNPRINTF_STACK, VSN_DEPTH, SNPRINTF, GLOBALS_TOP, STATIC_SPLIT in *.
  pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]%Z m) as MU1. pose proof (wmono_refl ctusegs m) as WM.   (* [comment removed for export] *)
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (bytes_at_bound _ _ _ _ HF) as FBD. unfold zb in FBD. rewrite length_map in FBD.
  assert (SEPF : A + Z.of_nat (length (zb fmt)) <= lo \/ bv_unsigned sp <= A) by (unfold zb; rewrite length_map; unfold zlength in AR; lia).
  unfold got_ssp, ssp_guard in SSP1, SSP2.
  assert (SEPG : 2986896 + 8 <= lo \/ bv_unsigned sp <= 2986896) by lia.
  assert (SEPC : 3486312 + 8 <= lo \/ bv_unsigned sp <= 3486312) by lia.
  assert (SEPD : D + Z.of_nat dn <= lo \/ bv_unsigned sp <= D) by lia.
  (* [comment removed for export] *)
  carve_frame 80%nat ST. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  name_mem m1.
  (* [comment removed for export] *)
  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
    pose proof (proj1 (rw_cells_app m1 _ [c0; c1; c2; c3; c4] rest) FR) as [FRp HVA]; clear FR end.
  cbn [cells_size csize Nat.add] in HVA. replace (bv_unsigned sp + -80 + Z.of_nat 40) with (bv_unsigned sp + -40) in HVA by lia.
  (* [comment removed for export] *)
  pose proof HST as HST0.
  replace (bv_unsigned sp) with (bv_unsigned sp + -40 + Z.of_nat 40) in HST0 at 1 by lia.
  pose proof (proj2 (rw_cells_app m1 _ _ _) (conj HVA HST0)) as HVA6. cbn [app] in HVA6. clear HST0.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  pose proof vsnprintf_proof as VS. unfold vsnprintf_stmt in VS.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (VS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1
              D n A (bv_unsigned sp + -40) dn junkd fmt [a3; a4; a5; a6; a7; st0] args lo canary (zlength o) o);
    rewrite ?ESP;
      [reflexivity| reflexivity| reflexivity| reflexivity| exact HD| exact HF| exact FB| exact P1
      | exact (proj2 (proj1 HVA6))
      | intros m' MU'; apply AOK; eapply munch_trans; [exact MU1| eapply munch_weaken; [| exact MU']; unfold VSN_W, sub_fp; cbn [outside]; intros y Hy; lia]
      | exact MODEL| exact FPC| exact OLEN| exact ON| exact NR
      | exact ST| unfold VSN_DEPTH; lia| unfold GLOBALS_TOP; lia| lia
      | split; [exact SSP1| exact SSP2]| eassumption| exact FRM
      | lia| unfold STATIC_SPLIT; lia| lia| change (zlength [a3; a4; a5; a6; a7; st0]) with 6; lia
      | lia| change (zlength [a3; a4; a5; a6; a7; st0]) with 6; lia| unfold GLOBALS_TOP; lia]. }
  clear VS HD HVA6. post_call_esp ESP m1. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -80) |- _ => rename H into ST end.
  match goal with H : frm0 _ |- _ => rename H into FRM' end.
  match goal with H : forall k : reg, _ -> reg_get _ k = reg_get F k |- _ => rename H into FREG end.
  match goal with H : ssp_cells _ canary |- _ => pose proof H as SSP'; destruct H as [SSP1' SSP2'] end.
  match goal with H : rw_cells ctusegs _ D _ |- _ => rename H into HD' end.
  unfold got_ssp, ssp_guard in SSP1', SSP2'.
  name_mem m2.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity| try clear K].
  (* [comment removed for export] *)
  replace (bv_unsigned sp + -40) with (bv_unsigned sp + -80 + Z.of_nat 40) in HVA by lia.
  pose proof (proj2 (rw_cells_app m2 _ _ _) (conj FRp HVA)) as FR. cbn [app] in FR. clear FRp HVA.
  zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. unfold sng_post.
  do 13 eexists. eexists. eexists. eexists. eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact FRM'|]. split; [exact FREG|].
  split; [eassumption|]. split; [exact SSP'| exact HD'].
Qed.
End WithCeiling0.
