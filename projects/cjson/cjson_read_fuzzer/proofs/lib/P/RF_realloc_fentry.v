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
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_free_C.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMallocKit_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_am_E.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_realloc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_mm_syscalls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require SspGuard.
From Stdlib Require Zify.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Module RF_free_C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_free_C.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_mm_syscalls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Local Ltac tclose_core :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; tclose_core
  | |- _ \/ _ => first [ left; tclose_core | right; tclose_core ]
  | |- _ = _ => reflexivity
  | |- _ => assumption
  end.
Local Ltac tclose := first [ tclose_core | tauto ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition rffin_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (W : list (Z * Z)) (m : word -> option byte) (st : mstate) (errv : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch W m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv]
    /\ rmrep st m'.

Lemma rfree_fin0 : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv psegs m ->
  rw_cells psegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  stk psegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt psegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m st errv)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz 0) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15498) fc None m (seg_rom psegs)).
Proof using .
  intros until errv. intros TP MR MI FR ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
  unfold alloc_ceiling, RMLOCK, RNEED_LOCKS, RATP in *. subst tp.
  rewrite (unsigned_lit 211088) in ERR by lia. change (211088 + -164) with 210924 in ERR.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x154ac)) with (Z_to_bv 64 0x154ac) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
  rewrite (unsigned_lit 211088) by lia. change (211088 + -164) with 210924. exact ERR.
Qed.

(* [comment removed for export] *)
Definition rfmun_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (junk : list byte) (m : word -> option byte) (st : mstate) (errv bw lw : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x154c8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw bw lw a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 (errno_addr tp)) (sx32 errv) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmunmap_entry) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells psegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv]
    /\ rmrep st m'.

Lemma rfree_tomunmap : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
    (m : word -> option byte) (junk : list byte) (lo len : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv psegs m -> 0 < len < 2^64 ->
  rw_cells psegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  stk psegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt psegs (rfmun_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo junk m st errv bw (wz len))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz len) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15498) fc None m (seg_rom psegs)).
Proof using .
  intros until errv. intros TP MR MI HL FR ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
  unfold alloc_ceiling, RMLOCK, RNEED_LOCKS, RATP in *. subst tp.
  rewrite (unsigned_lit 211088) in ERR by lia. change (211088 + -164) with 210924 in ERR.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x154ac)) with (Z_to_bv 64 0x154ac) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K. { exfalso. rewrite wz_unsigned in K by lia. lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  replace (ret_pc (Z_to_bv 64 0x154b4)) with (Z_to_bv 64 0x154b4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
  apply evt_done. unfold rfmun_post. do 14 eexists. split; [rewrite (unsigned_lit 211088) by lia; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
  split; [rewrite (unsigned_lit 211088) by lia; change (211088 + -164) with 210924; exact ERR| exact MR2].
Qed.

(* [comment removed for export] *)
Lemma rerrno_avoids_repfoot : forall st m a, rmrep st m -> 210924 <= a < 210928 -> ~ rrepfoot st a.
Proof.
  intros st m a MR Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
  - unfold RCTX in C. lia.
  - unfold RMLOCK in C. lia.
  - unfold RNEED_LOCKS in C. lia.
  - unfold RPAGE_SIZE in C. lia.
  - destruct C as (ak & ar & Hak & Hin).
    destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len ra)). lia.
  - destruct C as (b & gh & Hb & Hin).
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len rb)). lia.
  - destruct C as (rid & r & v & Hr & Hk & Hin & HC).
    destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. lia.
  - unfold RGOT_SSP in C. lia.
  - unfold RSSP_GUARD in C. lia.
Qed.

Lemma rmrep_transport_frame_errno : forall st m m' (sp : Z),
  rmrep st m -> munch [(sp - 48, sp); (210924, 210928)]%Z m m' -> wmono psegs m m' -> alloc_ceiling <= sp - 48 -> rmrep st m'.
Proof.
  intros st m m' sp MR MU WM HS. eapply rmrep_transport_unowned; [exact MR | exact MU | exact WM |].
  apply ivs_avoid_cons; [| apply ivs_avoid_cons; [| apply ivs_avoid_nil]].
  - intros a Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in HS.
    intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
    + unfold RCTX in C. lia.
    + unfold RMLOCK in C. lia.
    + unfold RNEED_LOCKS in C. lia.
    + unfold RPAGE_SIZE in C. lia.
    + destruct C as (ak & ar & Hak & Hin).
      destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). unfold alloc_ceiling in RBC. lia.
    + destruct C as (b & gh & Hb & Hin).
      destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC). unfold alloc_ceiling in RBC. lia.
    + destruct C as (rid & r & v & Hr & Hk & Hin & HC).
      destruct (WR _ _ Hr) as (_ & _ & _ & RBC & _). unfold alloc_ceiling in RBC. lia.
    + unfold RGOT_SSP in C. lia.
    + unfold RSSP_GUARD in C. lia.
  - intros a Ha. eapply rerrno_avoids_repfoot; [exact MR | exact Ha].
Qed.

(* [comment removed for export] *)
Lemma rfree_fin1 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra ew bw lw e' : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv psegs m ->
  rw_cells psegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  le4 ew = le4 errv ->
  rw_cells psegs m (errno_addr tp) [C4 e'] ->
  stk psegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt psegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp); (210924, 210928)]%Z m st errv)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (errno_addr tp)) ew s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x154c8) fc None m (seg_rom psegs)).
Proof using .
  intros until errv. intros TP MR MI FR EW ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (210924, 210928)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  unfold alloc_ceiling, RATP in *. subst tp.
  rewrite (unsigned_lit 211088) in ERR by lia. change (211088 + -164) with 210924 in ERR.
  rewrite (unsigned_lit 211088) by lia. change (211088 + -164) with 210924.
  (* [comment removed for export] *)
  st1.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX) by (eapply (rmrep_transport_frame_errno st m mX (bv_unsigned sp)); [exact MR | exact MU | exact WM | unfold alloc_ceiling; lia]) end.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
  rewrite (unsigned_lit 211088) by lia. change (211088 + -164) with 210924.
  eapply rw_cells_congr; [| | | exact ERR]; [cbn [cells_bytes cbytes app]; rewrite EW; reflexivity| reflexivity| cbn; tclose].
Qed.


End CeilWrap.
End RF_free_C.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_enframe.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocBlocks.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_ntf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_mm_syscalls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocBlocksR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_ntf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_free_K.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module RF_free.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.MallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_free_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.F_free_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_mm_syscalls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_free_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_free_B RF_free_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_ntf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_free_K.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rfree_end (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (LB' : list block) (m : mem) (errv : word) (s : PState)
    (st' : mstate) (s' : PState) : machine_state -> Prop :=
  fun ms' => s' = s /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv]
    /\ rmrep st' m'
    /\ rpres_except (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st' a \/ 210924 <= a < 210928) m m'
    /\ (forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r')
    /\ (forall blk', In blk' LB' -> exists r', (s_regions st') !! (fst (blk_slot blk')) = Some r')
    /\ c_brk (ctx st') = c_brk (ctx st)
    /\ (forall brid boff, c_brk (ctx st) = BrkLive brid boff -> (s_regions st') !! brid = (s_regions st) !! brid).

Lemma rerrno_not_free_fp st m lo (sp : Z) a : rmrep st m -> alloc_ceiling <= lo -> 210924 <= a < 210928 -> ~ rfree_fp st lo sp a.
Proof.
  intros MR LO Ha. pose proof MR as (WF & _). (nelimp WF 5%nat; intros Hres WR DJ WA WG). unfold alloc_ceiling in LO.
  intros [[A|[A|A]]|[A|A]].
  - lia.
  - unfold RCTX in A. lia.
  - (nelim A 5%nat; intros rid r Hr _ Hin). (nelim (WR _ _ Hr) 5%nat; intros _ _ _ _ RF). (nelimp (rreserved_disjoint _ _ RF) 4%nat; intros ? ? ? ?). pose proof (lr_lo_ge r). lia.
  - (nelim A 4%nat; intros b gh Hb Hin). (nelim (rgroup_conc st b gh WF Hb) 7%nat; intros rb Hrb Cb _ Sb0 Sb1 _).
    (nelim (WR _ _ Hrb) 5%nat; intros _ _ _ _ RF). (nelimp (rreserved_disjoint _ _ RF) 4%nat; intros ? ? ? ?). lia.
  - (nelim A 7%nat; intros rid r v Hr _ Hin _). (nelim (WR _ _ Hr) 5%nat; intros _ _ _ _ RF). (nelimp (rreserved_disjoint _ _ RF) 4%nat; intros ? ? ? ?). lia.
Qed.

(* [comment removed for export] *)
Lemma rmrep_after_munmap st2 rid r2 m4 m5 (slo shi : Z) :
  rmrep (drop_region rid st2) m4 -> rmrep st2 m4 ->
  (s_regions st2) !! rid = Some r2 -> r_kind r2 = RKGroup ->
  munch [(slo, shi); (210924, 210928); (r_base r2, r_base r2 + round_up_pg (r_len r2))]%Z m4 m5 ->
  alloc_ceiling <= slo ->
  rmrep (drop_region rid st2) m5.
Proof.
  intros MRd MR Hr Kr MU LO. pose proof MR as (WF & _). (nelimp WF 5%nat; intros Hres WR DJ WA WG). unfold alloc_ceiling in LO.
  (nelimp (WR _ _ Hr) 5%nat; intros RB0 RBAL RL0 RBC RF). (nelimp (rreserved_disjoint _ _ RF) 4%nat; intros D1 D2 D3 D4). unfold alloc_ceiling in RBC.
  eapply rmrep_transport_agree'; [exact MRd|]. intros a Ha HF. apply MU. rewrite wa_unsigned by lia.
  assert (LOW : a < alloc_ceiling /\ ~ (210924 <= a < 210928) /\ ~ (r_base r2 <= a < r_base r2 + round_up_pg (r_len r2))).
  { destruct HF as [HF|HF].
    - split; [| split].
      + destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
        * unfold RCTX in C; lia. * unfold RMLOCK in C; lia. * unfold RNEED_LOCKS in C; lia. * unfold RMallocRep.RPAGE_SIZE in C; lia.
        * (nelim C 4%nat; intros ak ar Hak Hin). (nelim (rarea_conc (drop_region rid st2) ak ar (proj1 MRd) Hak) 10%nat; intros ra Hra Ca Sa0 Sa1 _ _ _ _ RC). unfold alloc_ceiling in RC. lia.
        * (nelim C 4%nat; intros b gh Hb Hin). (nelim (rgroup_conc (drop_region rid st2) b gh (proj1 MRd) Hb) 9%nat; intros rb Hrb Cb _ _ Sb1 _ _ RC). unfold alloc_ceiling in RC. lia.
        * (nelim C 7%nat; intros k rk v Hk _ Hin _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [_ Hk].
          (nelim (WR _ _ Hk) 5%nat; intros _ _ _ RC _). unfold alloc_ceiling in RC. lia.
        * unfold RGOT_SSP in C; lia. * unfold RSSP_GUARD in C; lia.
      + intros Hea. exact (rerrno_avoids_repfoot _ _ a MRd Hea HF).
      + intros Hin. destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
        * unfold RCTX in C; lia. * unfold RMLOCK in C; lia. * unfold RNEED_LOCKS in C; lia. * unfold RMallocRep.RPAGE_SIZE in C; lia.
        * (nelim C 4%nat; intros ak ar Hak Ha'). cbn [drop_region s_areas set_shadow set_regions] in Hak.
          (nelim (WA ak ar Hak) 7%nat; intros ra Hra Sa0 Sa1 _ NK ALR).
          assert (NE : fst ak <> rid) by (intros E; rewrite E, Hr in Hra; assert (ra = r2) by congruence; subst; exact (NK Kr)).
          rewrite (rconc_drop st2 rid ak NE) in Ha'. rewrite (conc_region' st2 ak ra Hra) in Ha'.
          pose proof (lr_lo_group r2 Kr). destruct (DJ _ _ _ _ Hra Hr NE); lia.
        * (nelim C 4%nat; intros b gh Hb Ha'). cbn [drop_region s_groups set_shadow set_regions] in Hb.
          (nelim (WG b gh Hb) 6%nat; intros rb Hrb Krb Sb0 Sb1 _).
          assert (NE : fst b <> rid).
          { intros E. (nelimp (proj1 MRd) 5%nat; intros _ _ _ _ WG'). (nelim (WG' b gh Hb) 3%nat; intros rb' Hrb' _).
            cbn [drop_region s_regions set_shadow set_regions] in Hrb'. rewrite E, lookup_delete_eq in Hrb'. discriminate. }
          rewrite (rconc_drop st2 rid b NE) in Ha'. rewrite (conc_region' st2 b rb Hrb) in Ha'.
          pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
        * (nelim C 7%nat; intros k rk v Hk Kk Ha' _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
          pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia.
        * unfold RGOT_SSP in C. lia.
        * unfold RSSP_GUARD in C. lia.
    - (nelim HF 5%nat; intros k rk Hk Kk Ha'). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
      (nelim (WR _ _ Hk) 5%nat; intros _ _ _ RC RFk). (nelimp (rreserved_disjoint _ _ RFk) 4%nat; intros ? ? ? ?). unfold alloc_ceiling in RC.
      split; [lia|]. split; [lia|].
      pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia. }
  (nelim LOW 3%nat; intros L1 L2 L3). cbn [outside]. split; [lia|]. split; [exact L2|]. split; [exact L3| exact I].
Qed.

(* [comment removed for export] *)
Lemma byte_zero_list (x : byte) : bv_unsigned x = 0 -> [x] = [b8 0].
Proof using . intros Hx. f_equal. rewrite <- (definitions.Z_to_bv_bv_unsigned 8 x). rewrite Hx. reflexivity. Qed.

Lemma bytes4_range (x0 x1 x2 x3 : byte) :
  0 <= bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3 < 2^32.
Proof using .
  pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
  pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
  unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *. lia.
Qed.

Lemma le4_of_bytes (x0 x1 x2 x3 : byte) :
  le4 (wz (bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3)) = [x0; x1; x2; x3].
Proof using .
  pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
  pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
  unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *.
  rewrite le4_bytes by lia. unfold b8.
  (* [comment removed for export] *)
  f_equal; [|f_equal; [|f_equal; [|f_equal]]];
    (apply bv_eq; rewrite Z_to_bv_unsigned;
     match goal with |- bv_wrap 8 ?a = _ => change (bv_wrap 8 a) with (a mod 256)%Z end;
     Z.div_mod_to_equations; lia).
Qed.

Lemma shiftr5_ge v : 0 <= v < 256 -> 5 <= Z.shiftr v 5 -> 160 <= v.
Proof using . intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
Lemma shiftr5_lt v : 0 <= v < 256 -> Z.shiftr v 5 < 5 -> v < 160.
Proof using . intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
Lemma shiftr5_range v : 0 <= v < 256 -> 0 <= Z.shiftr v 5 < 8.
Proof using . intros Hv. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

Section FREE.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis TP : tp = Z_to_bv 64 RATP.

Theorem rlibc_free_implT : forall (ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (s : PState)
    (st : mstate) (blk : block) (off : Z) (errv : word),
  CINV st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  rmrep st m -> mem_inv psegs m ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 8192 ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  a0 = Z_to_bv 64 (blk_addr blk) ->
  rimplT m (free st (Some (aadd (blk_slot blk) (UNIT * off)))) s
        (rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB blk) m errv s)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rfree_entry) fc None m (seg_rom psegs)).
Proof using LO TP.
  intros until errv. intros C Hin Hoff HA MR MI ST SLO ERR A0.
  pose proof (ci_ticks _ _ C) as TK.
  pose proof (KINV_of_CINV _ _ C) as K0.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin) as BK.
  pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
  destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
  assert (off' = off) as ->.
  { rewrite HA in OA. unfold UNIT in OA. lia. }
  clear OA.
  set (c0 := blk_slot blk) in *. set (pf := aadd c0 (UNIT * off)) in *. set (LB' := lbrm LB blk) in *.
  pose proof (ci_gmetas _ _ C b g HB) as GO.
  (nelim (go_region _ _ _ GO) 7%nat; intros r Hr Kr B0 B16 SPAN TOP).
  (nelimp MR 6%nat; intros WF CX GL AR GR SH). (nelimp WF 5%nat; intros Hres WR DJ WA WG).
  (nelim (WR _ _ Hr) 5%nat; intros RB0 RBAL RL0 RBC RF).
  destruct BC as [(r0 & Hr0 & _ & A16 & AEND & AL & UNK) HD BB].
  rewrite <- FB, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
  (nelim (ki_slts _ _ _ K0 _ _ _ SL) 3%nat; intros GMg Ec _). fold c0 in Ec.
  (nelim HK 8%nat; intros v3 lo8 hi C3 V31 C2 C1 OFF). fold c0 in C3, C2, C1, OFF.
  cbn [aadd fst snd] in C3, C2, C1, OFF.
  (* [comment removed for export] *)
  assert (Fp : fst pf = fst b) by (unfold pf; cbn; symmetry; exact FB).
  assert (Cp : conc st pf = r_base r + snd pf) by (apply conc_region'; rewrite Fp; exact Hr).
  assert (Cc : conc st c0 = r_base r + snd c0) by (apply conc_region'; rewrite <- FB; exact Hr).
  assert (Sp : snd pf = snd c0 + 16 * off) by (unfold pf, UNIT; cbn; lia).
  assert (HAp : blk_addr blk = r_base r + snd pf) by (rewrite HA, Cc, Sp; unfold UNIT; lia).
  assert (Sc : snd c0 = snd b + 16 + get_stride (get_meta_rec st g) * i).
  { rewrite Ec. rewrite (slot_start'_mem _ b i (go_mem _ _ _ GO)). cbn. unfold UNIT. lia. }
  pose proof (go_stride _ _ _ GO) as [S16 SM]. pose proof (go_li _ _ _ GO) as LI.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (ETP : bv_unsigned tp + -164 = 210924) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  pose proof LO as LOv. unfold alloc_ceiling in LOv.
  (* [comment removed for export] *)
  assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
  { unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
  assert (SI0 : 0 <= get_stride (get_meta_rec st g) * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SIL : get_stride (get_meta_rec st g) * (i + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
  { apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
  unfold sstart_of in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN.
  assert (P16m : snd pf mod 16 = 0).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. unfold UNIT, IB in *. clear - SIM B16 Hoff. Z.div_mod_to_equations. lia. }
  assert (PHI : snd pf + 16 <= round_up_pg (r_len r)).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. set (stq := get_stride (get_meta_rec st g)) in *.
    unfold UNIT, IB in *.
    assert (16 * off + 16 <= stq) by (clear - OS SZ SM Hoff S16; Z.div_mod_to_equations; lia).
    rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. fold si in SIL. lia. }
  assert (HAR : 0 <= r_base r + snd pf /\ r_base r + snd pf + 16 <= 2^64) by (unfold alloc_ceiling in RBC; pose proof (round_up_pg_ge (r_len r)); lia).
  assert (DRr : r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x55000 <= r_base r) by (apply (rreserved_disjoint1 _ _ RF); lia).
  (* [comment removed for export] *)
  clear SIM SM B16 RBAL AL. change (frozen (snd pf mod 16 = 0)) in P16m.
  assert (EB : aadd pf (- (UNIT * (lo8 + 256 * hi)) - UNIT) = b).
  { unfold aadd. apply injective_projections; cbn; [exact Fp| unfold UNIT in *; lia]. }
  destruct HB as [ai Hgh].
  (* [comment removed for export] *)
  assert (Cb : conc st b = r_base r + snd b) by (apply conc_region'; exact Hr).
  pose proof (shiftr5_range v3) as SR5.
  destruct (rmrep_shadow_read st m (fst c0) r (snd c0 + UNIT * off - 3) v3 MR ltac:(rewrite <- FB; exact Hr) Kr ltac:(unfold UNIT, IB in *; lia) C3) as [_ V3R].
  (* [comment removed for export] *)
  assert (RDB : forall q : aptr, fst q = fst b -> 0 <= snd q < round_up_pg (r_len r) ->
            exists x : byte, bytes_at psegs m (r_base r + snd q) [x] /\ rdv pans_mem m st q = bv_unsigned x).
  { intros q Fq Hq.
    assert (Hrq : s_regions st !! fst q = Some r) by (rewrite Fq; exact Hr).
    destruct (SH _ r Hr Kr) as [WRr _].
    assert (W1 : wr_at psegs m (r_base r + snd q) 1).
    { (nelim WRr 3%nat; intros W0 Wn W). split; [lia|]. split; [pose proof (round_up_pg_ge (r_len r)); unfold alloc_ceiling in RBC; lia|].
      intros j Hj. replace (r_base r + snd q + j) with (r_base r + (snd q + j)) by lia. apply W. lia. }
    (nelim (rwr_at_bytes_exist m _ 1 W1 ltac:(lia) ltac:(pose proof (round_up_pg_ge (r_len r)); lia)) 3%nat; intros bs L B).
    destruct bs as [|x [|]]; try discriminate. exists x. split; [exact B|].
    eapply (rrdv_cur m st m q r x MR Hrq Kr Hq); [intros; reflexivity| exact B]. }
  (* [comment removed for export] *)
  unfold free.
  eapply (rimplT_bind m (free_hdr st pf) _ s
           (fun r1 s' ms' => s' = s /\ r1 = Some (hdr_st st pf, g, i) /\
              rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')).
  { unfold free_hdr, get_meta. apply rimplT_guard. intros _.
    apply rimplT_rd16. apply rimplT_rd8. cbv zeta. apply rimplT_rd8.
    rewrite (rdv_known m st (aadd pf (-4)) 0) by (cbn [aadd fst snd]; replace (snd pf + -4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia); exact OK).
    rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
    rewrite (rdv_known m st (aadd pf (-2)) lo8) by (cbn [aadd fst snd]; replace (snd pf + -2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia); exact C2).
    rewrite (rdv_known m st (aadd (aadd pf (-2)) 1) hi) by (cbn [aadd fst snd]; replace (snd pf + -2 + 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia); exact C1).
    cbn [Z.eqb negb]. rewrite EB. unfold get_group. rewrite Hgh. cbn [g_meta].
    apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
    destruct (s_areas st !! area_of g) as [ar|] eqn:AR1; [| apply rimplT_guard; intros; discriminate].
    apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
    unfold slot_start. rewrite (go_mem _ _ _ GO). cbv beta zeta.
    apply Z.eqb_eq in G15. apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
    rewrite V31 in G12, G13, G14, G16.
    set (e := aadd (aadd b (UNIT + get_stride (get_meta_rec st g) * Z.land v3 31)) (get_stride (get_meta_rec st g) - IB)).
    assert (Fe : fst e = fst b) by reflexivity.
    assert (Se : snd e = snd b + 16 + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - 4).
    { unfold e. cbn [aadd snd]. rewrite V31. unfold UNIT, IB. lia. }
    (* [comment removed for export] *)
    pose proof (go_sc _ _ _ GO) as GSC.
    assert (WALK : forall r32 : Z,
      (160 <= v3 -> Z.shiftr v3 5 = 5 /\ 5 <= r32 < 2^32
          /\ bytes_at psegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 4) (le4 (wz r32))
          /\ bytes_at psegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 5) [b8 0]) ->
      (if 160 <=? v3 then r32 else Z.shiftr v3 5) <= conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf) ->
      bytes_at psegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (if 160 <=? v3 then r32 else Z.shiftr v3 5)) [b8 0] ->
      bytes_at psegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB) [b8 0] ->
      evt psegs (fun ms' => s = s /\ Some (hdr_st st pf, g, i) = Some (hdr_st st pf, g, i) /\
                 rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom psegs))).
    { intros r32 BIG RSVLE RB0r RE0.
      eapply evt_mono.
      { eapply (rfree_head ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo st pf r g (mkGhdr (Some g) ai) ar v3 lo8 hi r32);
          first [exact MR | exact MI | exact TK | exact ST | exact LO | exact Kr | idtac].
        all: rewrite ?EB, ?V31.
        - lia.
        - rewrite Fp. exact Hr.
        - rewrite A0, HAp. apply unsigned_lit. lia.
        - exact P16m.
        - rewrite Sp, Sc. lia.
        - unfold pf in OFF |- *. cbn [aadd snd] in OFF |- *. lia.
        - exact PHI.
        - replace (snd pf - 4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia). unfold pf; cbn [aadd fst]. exact OK.
        - replace (snd pf - 3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C3.
        - replace (snd pf - 2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C2.
        - replace (snd pf - 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C1.
        - exact Hgh.
        - reflexivity.
        - exact (go_slot _ _ _ GO).
        - (nelim (go_slot _ _ _ GO) 6%nat; intros a ara k Ha Hk ->). (nelim (WA a ara Ha) 4%nat; intros rg0 _ A00 _). cbn. unfold AREA_HDR, META_SIZE. lia.
        - exact (go_mem _ _ _ GO).
        - exact AR1.
        - exact G15.
        - exact (go_avail _ _ _ GO).
        - exact (go_freed _ _ _ GO).
        - exact (proj2 (proj2 (proj2 (ki_cx _ _ _ K0)))).
        - lia.
        - rewrite (go_freeable _ _ _ GO). lia.
        - lia.
        - pose proof (go_maplen _ _ _ GO). lia.
        - exact G12.
        - exact G13.
        - exact G14.
        - intros Hsc. apply Z.ltb_lt in Hsc. rewrite Hsc in G16. apply andb_true_iff in G16. destruct G16 as [G16a G16b].
          apply Z.leb_le in G16a. apply Z.ltb_lt in G16b. lia.
        - intros Hsc. destruct (Z.ltb_spec (m_sizeclass (get_meta_rec st g)) 48); [lia|]. apply Z.eqb_eq in G16. exact G16.
        - intros Hml. destruct (Z.eqb_spec (m_maplen (get_meta_rec st g)) 0); [lia|]. cbn [negb] in G17. apply Z.leb_le in G17.
          unfold UNIT in G17.
          replace (m_maplen (get_meta_rec st g) * 4096) with (m_maplen (get_meta_rec st g) * 256 * 16) in G17 by lia.
          rewrite Z.div_mul in G17 by lia. lia.
        - lia.
        - exact S16.
        - rewrite Cb, Sp, Sc. unfold UNIT, IB in *. lia.
        - rewrite Cb. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia.
        - exact BIG.
        - exact RSVLE.
        - exact RB0r.
        - exact RE0.
        - intros b' gh' Hb' Fb'. specialize (HD b' gh' Hb' ltac:(rewrite Fb', Fp; exact FB)).
          rewrite (conc_region' st b' r) in HD by (rewrite Fb', Fp; exact Hr). unfold IB in HD.
          clear - HD HAp SZ. lia. (* [comment removed for export] *) }
      intros ms' FP. split; [reflexivity|]. split; [reflexivity|]. unfold hdr_st. rewrite <- V31. exact FP. }
    (* [comment removed for export] *)
    assert (EQE : forall k, r_base r + snd (aadd e (- k)) = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - k).
    { intros k. cbn [aadd snd]. rewrite Se, Cb. unfold UNIT, IB. lia. }
    assert (EQE0 : r_base r + snd e = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB).
    { rewrite Se, Cb. unfold UNIT, IB. lia. }
    assert (ERNG : snd e + 1 <= round_up_pg (r_len r) /\ snd pf <= snd e /\ 16 <= snd e).
    { rewrite Se, Sp, Sc. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia. }
    assert (DIFF : snd e - snd pf = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf)).
    { rewrite Se, Cb. unfold UNIT, IB. lia. }
    
    unfold get_nominal_size. apply rimplT_rd8. cbv zeta.
    rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
    apply rimplT_if; intros HR5.
    - (* [comment removed for export] *)
      apply Z.leb_le in HR5.
      apply rimplT_guard; intros G20. apply Z.eqb_eq in G20.
      apply rimplT_rd32. 
      (nelim (RDB (aadd e (-4)) Fe ltac:(cbn [aadd snd]; lia)) 3%nat; intros x0 BX0 RX0). rewrite RX0. 
      (nelim (RDB (aadd (aadd e (-4)) 1) Fe ltac:(cbn [aadd snd]; lia)) 3%nat; intros x1 BX1 RX1). rewrite RX1. 
      (nelim (RDB (aadd (aadd e (-4)) 2) Fe ltac:(cbn [aadd snd]; lia)) 3%nat; intros x2 BX2 RX2). rewrite RX2.
      (nelim (RDB (aadd (aadd e (-4)) 3) Fe ltac:(cbn [aadd snd]; lia)) 3%nat; intros x3 BX3 RX3). rewrite RX3.
      pose proof (bytes4_range x0 x1 x2 x3) as U32. pose proof (le4_of_bytes x0 x1 x2 x3) as LE4.
      set (r32 := bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3) in *.
      apply rimplT_guard; intros G21. apply Z.leb_le in G21.
      apply rimplT_rd8. (nelim (RDB (aadd e (-5)) Fe ltac:(cbn [aadd snd]; lia)) 3%nat; intros x5 BX5 RX5). rewrite RX5.
      apply rimplT_guard; intros G25. apply Z.eqb_eq in G25.
      apply rimplT_guard; intros G22. apply Z.leb_le in G22.
      apply rimplT_rd8. (nelim (RDB (aadd e (- r32)) Fe ltac:(cbn [aadd snd]; lia)) 3%nat; intros xc BXc RXc). rewrite RXc.
      apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
      apply rimplT_rd8. (nelim (RDB e Fe ltac:(lia)) 3%nat; intros xe BXe RXe). rewrite RXe.
      apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
      apply rimplT_ret. rewrite V31.
      specialize (SR5 V3R). pose proof (shiftr5_ge v3 V3R HR5) as V160.
      assert (H160 : (160 <=? v3) = true) by (apply Z.leb_le; exact V160).
      
      apply (WALK r32).
      + intros _. split; [exact G20|]. split; [lia|]. split.
        * rewrite <- (EQE 4). rewrite LE4. change [x0; x1; x2; x3] with ([x0] ++ ([x1] ++ ([x2] ++ [x3]))).
          apply bytes_at_app. split; [exact BX0|]. apply bytes_at_app. split; [cbn [length Z.of_nat Pos.of_succ_nat]; cbn [aadd snd] in BX1 |- *; replace (r_base r + (snd e + -4) + 1) with (r_base r + (snd e + -4 + 1)) by lia; exact BX1|].
          apply bytes_at_app. split; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; cbn [aadd snd] in BX2, BX3 |- *.
          -- replace (r_base r + (snd e + -4) + 1 + 1) with (r_base r + (snd e + -4 + 2)) by lia. exact BX2.
          -- replace (r_base r + (snd e + -4) + 1 + 1 + 1) with (r_base r + (snd e + -4 + 3)) by lia. exact BX3.
        * rewrite <- (EQE 5), <- (byte_zero_list x5 G25). exact BX5.
      + rewrite H160, <- DIFF. exact G22.
      + rewrite H160, <- (EQE r32), <- (byte_zero_list xc G23). exact BXc.
      + rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe.
    - (* [comment removed for export] *)
      apply Z.leb_gt in HR5.
      apply rimplT_guard; intros G22. apply Z.leb_le in G22.
      apply rimplT_rd8. (nelim (RDB (aadd e (- Z.shiftr v3 5)) Fe ltac:(cbn [aadd snd]; clear - ERNG HR5 SR5 V3R; first [heap_lia_imp | lia])) 3%nat; intros xc BXc RXc).  (* [comment removed for export] *) rewrite RXc.
      apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
      apply rimplT_rd8. (nelim (RDB e Fe ltac:(lia)) 3%nat; intros xe BXe RXe). rewrite RXe.
      apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
      apply rimplT_ret. rewrite V31.
      specialize (SR5 V3R). pose proof (shiftr5_lt v3 V3R HR5) as V160.
      assert (H160 : (160 <=? v3) = false) by (apply Z.leb_gt; exact V160).
      
      apply (WALK 0).
      + intros H. exfalso. clear -H V160. lia.
      + rewrite H160, <- DIFF. exact G22.
      + rewrite H160, <- (EQE (Z.shiftr v3 5)), <- (byte_zero_list xc G23). exact BXc.
      + rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe. }

  intros r1 s' ms1 nelH_; (nelim nelH_ 3%nat; intros -> -> FH). cbv beta iota.
  (nelim FH 13%nat; intros x1 x5 x6 x7 junk m1 -> PE1 WM1 MI1 ST1 FR1 MR1).
  set (st1 := hdr_st st pf) in *.
  assert (TK1 : ticks_ok st1) by (unfold st1; apply ticks_ok_hdr_st; exact TK).
  assert (MSL1 : meta_slot st1 g) by (exact (go_slot _ _ _ GO)).
  assert (HK123 : forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w).
  { intros k Hk. unfold pf; cbn [aadd fst snd].
    assert (CS : k = 1 \/ k = 2 \/ k = 3) by lia.
    destruct CS as [-> |[-> | ->]];
      [exists hi; replace (snd c0 + UNIT * off - 1) with (snd c0 + UNIT * off - 1) by lia
      |exists lo8|exists v3];
      [rewrite <- C1 | rewrite <- C2 | rewrite <- C3]; f_equal; unfold UNIT; lia. }
  assert (FP1 : forall a, rfree_fp st1 lo (bv_unsigned sp - 48) a -> rfree_fp st lo (bv_unsigned sp) a).
  { intros a Ha. eapply (rfree_fp_hdr_st st pf lo (bv_unsigned sp) (bv_unsigned sp - 48) a TK HK123); [lia| exact Ha]. }
  assert (ERR1 : rw_cells psegs m1 (errno_addr tp) [C4 errv]).
  { eapply rpres_except_rw_cells; [exact PE1 | exact ERR |]. cbn [cells_size csize Nat.add]. intros a Ha.
    rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
  assert (TF : Z.testbit (m_freed (get_meta_rec st g)) i = false).
  { destruct (Z.testbit (m_freed (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; left; exact E| reflexivity]. }
  assert (TA : Z.testbit (m_avail (get_meta_rec st g)) i = false).
  { destruct (Z.testbit (m_avail (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; right; exact E| reflexivity]. }
  (* [comment removed for export] *)
  assert (BLKR : forall stX blk', s_regions stX = s_regions st -> In blk' (lbrm LB blk) -> exists r', s_regions stX !! fst (blk_slot blk') = Some r').
  { intros stX blk' ERX Hb'. rewrite ERX. unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hb' _].
    destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' Hb') as [(r' & Hr' & _) _ _]. exists r'. exact Hr'. }
  unfold free_tail. cbv zeta. change (get_meta_rec st1 g) with (get_meta_rec st g).
  apply rimplT_guard. intros _.
  apply rimplT_if; intros HC.
  - (* [comment removed for export] *)
    apply negb_true_iff in HC. apply orb_false_iff in HC. destruct HC as [Hfz Hall]. apply Z.eqb_neq in Hfz. apply Z.eqb_neq in Hall.
    apply rimplT_ret.
    eapply evt_mono.
    { eapply (rfree_triv ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 junk lo st st1 g i);
        first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact Hfz | exact Hall | exact FR1 | exact ST1 | exact LO | reflexivity | idtac].
      all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
    intros ms' TPo. unfold rftriv_post in TPo.
    (nelim TPo 22%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 m' -> PE' WM' MI' ST' MR').
    split; [reflexivity|]. nexists 16%nat. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE' | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
             rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
    split; [exact MR'|].
    split. { eapply rpres_except_mono; [eapply rpres_except_trans; [exact PE1| exact PE']|]. intros a Ha. left. exact Ha. }
    split; [intros rid r' H; exact H|].
    split; [intros blk' Hb'; apply (BLKR _ blk' eq_refl Hb')|].
    split; reflexivity.
  - (* [comment removed for export] *)
    
    assert (HNT : m_freed (get_meta_rec st g) = 0 \/ Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) + bit i = mask_upto (m_last_idx (get_meta_rec st g))).
    { apply negb_false_iff in HC. apply orb_true_iff in HC. destruct HC as [HC|HC]; apply Z.eqb_eq in HC; auto. }
    eapply rimplT_evt.
    { eapply (rfree_tocall ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 st1 g i);
        first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact HNT | idtac].
      all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
    intros ms2 nelH_; (nelim nelH_ 7%nat; intros y2 y3 y4 y5 y6 y7 ->).
    assert (HLB : forall b', In b' LB' -> In b' LB /\ blk_slot b' <> blk_slot blk).
    { intros b' Hb'. unfold LB', lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [H1 H2]. split; [exact H1|].
      intros E. rewrite E, aptr_eqb_refl in H2. exact H2. }
    assert (K1 : KINV st1 LB' 0).
    { unfold st1. eapply (KINV_hdr_st st LB LB' 0 pf blk r C Hin); [| exact HLB | rewrite Fp, FB; reflexivity | rewrite Fp; exact Hr | symmetry; exact HAp | exact P16m].
      unfold LB', lbrm. apply (KINV_filter_slot st LB 0 (fun s => negb (aptr_eqb s (blk_slot blk)))). exact K0. }
    assert (L1 : LPRE st1 LB' 0 g b i).
    { unfold LB', lbrm. apply (LPRE_intro st1 LB 0 g b i blk); [exact (ki_slts _ _ _ K0) | exists ai; exact Hgh | exact SL | exact NFR | exact NG | pose proof (go_sc _ _ _ GO); change (get_meta_rec st1 g) with (get_meta_rec st g); lia]. }
    assert (Z1 : ZINV st1 []) by (unfold st1; apply ZINV_hdr_st; apply (ZINV_of_CINV _ _ C)).
    assert (OOK1 : oracle_ok m m1 st1).
    { unfold st1. apply oracle_ok_hdr_st; [exact TK|]. eapply (roracle_ok_pres m m m1 st lo (bv_unsigned sp) m); [apply oracle_ok_refl | exact MR | exact LO | exact PE1]. }
    change (wz (conc st g)) with (Z_to_bv 64 (conc st1 g)). change (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc st1 g)).
    eapply (rntf_implT gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc m LB' lo LO);
      [exact K1 | exact L1 | exact Z1 | exact MR1 | exact MI1 | exact OOK1 | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; unfold FUEL; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]; lia |].
    (* [comment removed for export] *)
    
    intros st2 mi ms3 NQ. unfold rntf_q in NQ.
    (nelim NQ 26%nat; intros u0 u1 u2 a0v a1v u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 m3 -> MI3 ST3 MR3 PE3 [c3 KI3] ZI3 FR3 RES3 OOK3).
    rewrite unsigned_lit in ST3, PE3 by lia.
    replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in PE3 by lia.
    replace (ret_pc (Z_to_bv 64 0x15498)) with (Z_to_bv 64 0x15498) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (PE13 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
    { eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_mono; [exact PE3| exact FP1]. }
    assert (FR3' : rw_cells psegs m3 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rpres_except_rw_cells; [exact PE3 | exact FR1 |]. cbn [cells_size csize Nat.add length]. intros a Ha Hfp.
      pose proof (rfree_fp_lt st1 m1 lo (bv_unsigned sp - 48) a MR1 LO ltac:(lia) Hfp). lia. }
    assert (ERR3 : rw_cells psegs m3 (errno_addr tp) [C4 errv]).
    { eapply rpres_except_rw_cells; [exact PE3 | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
      rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR1 | exact LO | lia]. }
    pose proof (nf_regions _ _ FR3) as ER3. change (s_regions st1) with (s_regions st) in ER3.
    pose proof (nf_brk _ _ FR3) as EB3. change (ctx st1) with (ctx st) in EB3.
    destruct mi as [[bm len]|].
    + (* [comment removed for export] *)
      cbv beta iota.
      destruct RES3 as (-> & -> & LEN & SND & (r2 & Hr2 & Kr2 & Lr2) & NOG).
      replace (negb (len =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
      pose proof Hr2 as Hr2'. rewrite ER3 in Hr2'.
      (nelim (WR _ _ Hr2') 5%nat; intros R2B0 R2AL R2L R2C R2F). unfold alloc_ceiling in R2C.
      assert (R2D : r_base r2 + round_up_pg (r_len r2) <= 0x10000 \/ 0x55000 <= r_base r2) by (apply (rreserved_disjoint1 _ _ R2F); lia).
      assert (CB2 : conc st2 bm = r_base r2) by (rewrite (conc_region' st2 bm r2 Hr2); lia).
      pose proof (round_up_pg_ge (r_len r2)) as RU2.
      eapply rimplT_evt.
      { eapply (rfree_tomunmap sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra (wz (conc st2 bm)) _ _ F fc m3 junk lo len st2 errv);
          first [exact TP | exact MR3 | exact MI3 | exact LEN | exact FR3' | exact ERR3 | exact ST3 | exact LO | lia]. }
      intros ms4 FM. unfold rfmun_post in FM.
      (nelim FM 22%nat; intros w0 w1 w2 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 m4 -> MU4 WM4 MI4 ST4 FR4 ERR4 MR4).
      eapply (rimplT_munmap m (conc st2 bm) len _ s).
      { eapply rmunmap_spec.
        - rewrite unsigned_lit by lia. exact ST4.
        - exact ERR4.
        - exact MI4.
        - unfold wz. reflexivity.
        - unfold wz. reflexivity.
        - lia.
        - rewrite Lr2, mmap_len_round. lia.
        - lia.
        - rewrite unsigned_lit by lia. lia.
        - rewrite ETP, unsigned_lit by lia. lia.
        - rewrite Lr2, mmap_len_round, unsigned_lit by lia. lia.
        - rewrite ETP, Lr2, mmap_len_round. lia.
        - rewrite TP; unfold RATP; rewrite unsigned_lit by lia. lia. }
      intros a ms5 MP. cbv beta. unfold rmunmap_post in MP.
      (nelim MP 22%nat; intros z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 m5 -> MU5 _ MI5 ST5 ERR5 ERNG).
      rewrite (munmap_ok_range_val a ERNG).
      apply rimplT_ret.
      replace (ret_pc (Z_to_bv 64 0x154c8)) with (Z_to_bv 64 0x154c8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      rewrite unsigned_lit in MU5, ST5 by lia. rewrite Lr2, mmap_len_round, ETP in MU5.
      (* [comment removed for export] *)
      assert (AMC2 : amc (ctx st2) = amc (ctx st)) by (rewrite (nf_amc _ _ FR3); reflexivity).
      assert (MP2 : ci_mptrs st2) by (eapply (ci_mptrs_frame st st2 (ci_mp _ _ C) AMC2); [rewrite (nf_areas _ _ FR3); reflexivity| exact ER3]).
      assert (NOG' : forall b' gh, s_groups st2 !! b' = Some gh -> fst b' <> fst bm) by (intros b' gh Hb'; exact (NOG b' gh Hb')).
      pose proof (rptrs_in_norid st2 LB' c3 (fst bm) r2 m4 KI3 ZI3 MR4 Hr2 Kr2 NOG' MP2) as PTR.
      pose proof (rmrep_drop_region st2 (fst bm) PTR m4 MR4) as MRd4.
      assert (MRd5 : rmrep (drop_region (fst bm) st2) m5).
      { eapply (rmrep_after_munmap st2 (fst bm) r2 m4 m5); [exact MRd4 | exact MR4 | exact Hr2 | exact Kr2 | rewrite <- CB2; exact MU5 | lia]. }
      assert (FR5 : rw_cells psegs m5 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rrw_cells_agree'; [exact FR4|]. cbn [cells_size csize Nat.add length]. intros x Hx. apply MU5. rewrite wa_unsigned by lia.
        rewrite ?ETP. cbn [outside]. repeat split; lia. }
      eapply evt_mono.
      { eapply (rfree_fin1 sp gp tp z0 z1 z2 s0 s1 (munmap_ret a) z3 z4 z5 z6 z7 z8 z9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z10 z11 z12 z13 _ ra (sx32 errv) (wz (conc st2 bm)) (wz len) (rg_errno a errv) F fc m5 junk lo (drop_region (fst bm) st2) errv);
          first [exact TP | exact MRd5 | exact MI5 | exact FR5 | apply le4_sx32 | exact ERR5 | exact ST5 | exact LO | lia]. }
      intros ms' FIN. unfold rffin_post in FIN.
      (nelim FIN 23%nat; intros v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 m' -> MUf WMf MIf STf ERRf MRf).
      split; [reflexivity|]. nexists 16%nat. split; [reflexivity|].
      split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
      split.
      { (* [comment removed for export] *)
        assert (DR : forall x, r_base r2 <= x < r_base r2 + round_up_pg (r_len r2) -> DROPPED st (drop_region (fst bm) st2) x).
        { intros x Hx. exists (fst bm), r2. split; [exact Hr2'|]. split; [| split; [exact Kr2| exact Hx]].
          cbn [drop_region s_regions set_shadow set_regions]. apply lookup_delete_eq. }
        eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
        eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m3 m4 MU4)|].
        { intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 210924 <= a < 210928)); [| exact NC].
          cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
        eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m4 m5 MU5)|].
        { intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 210924 <= a < 210928)); [| exact NC].
          cover_intervals ltac:(fun y Hy => first [left; apply rfree_fp_stack; heap_lia_pruned | right; right; heap_lia_pruned | right; left; apply DR; heap_lia_pruned]). }
        eapply (rpres_except_of_munch_nw _ _ m5 m' MUf).
        intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 210924 <= a < 210928)); [| exact NC].
        cover_intervals ltac:(fun y Hy => first [left; apply rfree_fp_stack; heap_lia_pruned | right; right; heap_lia_pruned]). }
      split.
      { intros rid r' H. cbn [drop_region s_regions set_shadow set_regions] in H. apply lookup_delete_Some in H. destruct H as [_ H]. rewrite <- ER3. exact H. }
      split.
      { intros blk' Hb'. pose proof (proj1 (List.Forall_forall _ _) (ki_blks _ _ _ KI3) blk' Hb') as BK'.
        destruct BK' as [(g' & i' & bb & SL' & HB' & FB' & _) _ _].
        (nelim (go_region _ _ _ (ki_gmetas _ _ _ KI3 bb g' HB')) 3%nat; intros rr Hrr _).
        exists rr. cbn [drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne; [rewrite <- FB'; exact Hrr|].
        intros E. destruct HB' as [ai' Hbb]. apply (NOG bb _ Hbb). rewrite E. exact FB'. }
      split; [exact EB3|].
      intros brid boff HB0. cbn [drop_region s_regions set_shadow set_regions ctx s_ctx].
      rewrite <- EB3 in HB0. (nelim (ki_bk _ _ _ KI3 brid boff HB0) 3%nat; intros rb Hrb Krb).
      rewrite lookup_delete_ne; [rewrite ER3; reflexivity |].
      intros E. rewrite <- E, Hr2 in Hrb. assert (rb = r2) by congruence. subst rb. rewrite Kr2 in Krb. discriminate.
    + (* [comment removed for export] *)
      
      cbv beta iota. cbn in RES3. subst a1v.
      apply rimplT_ret.
      eapply evt_mono.
      { eapply (rfree_fin0 sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra a0v _ _ F fc m3 junk lo st2 errv);
          first [exact TP | exact MR3 | exact MI3 | exact FR3' | exact ERR3 | exact ST3 | exact LO | lia]. }
      intros ms' FIN. unfold rffin_post in FIN.
      (nelim FIN 23%nat; intros v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 m' -> MUf WMf MIf STf ERRf MRf).
      split; [reflexivity|]. nexists 16%nat. split; [reflexivity|].
      split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
      split.
      { eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
        eapply (rpres_except_of_munch_nw _ _ m3 m' MUf).
        intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st2 a \/ 210924 <= a < 210928)); [| exact NC].
        cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
      split; [intros rid r' H; rewrite <- ER3; exact H|].
      split; [intros blk' Hb'; apply (BLKR st2 blk' ER3 Hb')|].
      split; [exact EB3|].
      intros brid boff _. rewrite ER3. reflexivity.
Qed.
End FREE.


End CeilWrap.
End RF_free.

(* [comment removed for export] *)
From Stdlib Require Permutation.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Malloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv3.
Module RF_free_spec.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.MallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.F_free_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free_spec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_ntf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_free_K RF_free.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma rauxv_ok_pres_B : forall C m m' B,
  rauxv_ok m B -> rpres_except C m m' ->
  (forall a, B <= a -> ~ C a) -> (forall a, RAUXV_CELL <= a < RAUXV_CELL + 8 -> ~ C a) ->
  rauxv_ok m' B.
Proof using .
  intros C m m' B (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C1 & A1 & A2 & H) HP HB HC.
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rpres_except_rw_cells; [exact HP| exact C1|]. cbn. intros a Ha. apply HC. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A1|]. intros a Ha. apply HB. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A2|]. intros a Ha. apply HB. lia.
Qed.

(* [comment removed for export] *)
Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis MR : rmrep st m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.
Hypothesis PE : rpres_except (fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 210924 <= a < 210928) m m'.

Let FPT := fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 210924 <= a < 210928.

(* [comment removed for export] *)
Lemma rfp_not_high a : sp <= a -> ~ FPT a.
Proof using LO LS MR st'.
  intros Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in LO.
  intros [FP|[DR|ER]].
  - pose proof (rfree_fp_lt st m lo sp a MR ltac:(unfold alloc_ceiling; lia) LS FP). lia.
  - destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
  - lia.
Qed.

Lemma rfp_not_img a : 0x22000 <= a < 0x55000 -> ~ (RCTX <= a < RCTX + 928) -> ~ (210924 <= a < 210928) -> ~ FPT a.
Proof using LO MR sp st'.
  intros Ha N1 N2. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in LO.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + lia.
    + exact (N1 X).
    + destruct X as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
    + destruct X as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
      destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
    + destruct X as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
  - destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
  - exact (N2 ER).
Qed.

Lemma rfp_not_image a : 0x22000 <= a < 0x55000 -> ~ ralloc_static a -> ~ FPT a.
Proof using LO MR sp st'.
  intros Ha NS. apply rfp_not_img; [exact Ha| |]; intros X; apply NS; unfold ralloc_static, RLIBC, RCTX, RERRNO, RATP, RSSP_GUARD, RGOT_SSP in *; lia.
Qed.

Lemma rfp_not_block blk' a : In blk' (lbrm LB0 blk) -> blk_addr blk' <= a < blk_addr blk' + blk_size blk' -> ~ FPT a.
Proof using BLKR C LO MR SHR sp.
  intros Hb' Hab. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in LO.
  pose proof Hb' as Hb0. unfold lbrm in Hb0. apply In_filter_iff in Hb0. destruct Hb0 as [HinL _].
  destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
  destruct (UNK a Hab) as [h UNKa].
  destruct (WR _ _ Hrg) as (_ & _ & _ & RGC & RGF). pose proof (rreserved_disjoint _ _ RGF) as (?&?&?&?). unfold alloc_ceiling in RGC.
  pose proof (lr_lo_group rg Krg) as LRG.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + lia.
    + unfold RCTX in X. lia.
    + destruct X as (rid & r & Hr & NK & Hin).
      assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hrg in Hr; assert (r = rg) by congruence; subst; exact (NK Krg)).
      destruct (DJ _ _ _ _ Hr Hrg NE); lia.
    + destruct X as (b & gh & Hb & Hin). destruct (N.eq_dec (fst b) (fst (blk_slot blk'))) as [E|NE].
      * specialize (HD b gh Hb E). unfold IB in HD. lia.
      * destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
        pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hrg NE); lia.
    + destruct X as (rid & r & v & Hr & Kr & Hin & HC). destruct (N.eq_dec rid (fst (blk_slot blk'))) as [->|NE].
      * rewrite Hrg in Hr. assert (r = rg) by congruence. subst r. rewrite UNKa in HC. discriminate.
      * pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
  - destruct DR as (rid & r & Hr & Hr' & Kr & Hin).
    destruct (BLKR blk' Hb') as [r' Hr'']. pose proof (SHR _ _ Hr'') as HrgS. rewrite Hrg in HrgS. assert (r' = rg) by congruence. subst r'.
    assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hr'' in Hr'; discriminate).
    pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
  - lia.
Qed.

Lemma rheap_pres_free LB' : (forall b, In b LB' -> In b (lbrm LB0 blk)) -> rheap_pres LB' sp m m'.
Proof using BLKR C FPT LO LS MR PE SHR.
  intros HLB a Ha CA. apply PE; [exact Ha|].
  destruct CA as [CA|[[CA NS]|(blk' & Hb' & Hab)]].
  - apply rfp_not_high. exact CA.
  - apply rfp_not_image; assumption.
  - apply (rfp_not_block blk' a); [apply HLB; exact Hb'| exact Hab].
Qed.

Lemma rauxv_ok_free B : rauxv_ok m B -> sp <= B -> rauxv_ok m' B.
Proof using FPT LO LS MR PE.
  intros AV HB. eapply rauxv_ok_pres_B; [exact AV | exact PE | |].
  - intros a Ha. apply rfp_not_high. lia.
  - intros a Ha. apply rfp_not_img; unfold RAUXV_CELL, RLIBC, RCTX in *; lia.
Qed.
End FP.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rfree_spec_proof : rfree_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
         HP Hin AV HB ST LO SLO ERR MI TP A0.
  destruct HP as (st & LB0 & PERM & Hst & MR & [BL AR]).
  assert (Hin0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, n) Hin0) as BK.
  destruct BK as [(g & i & b & SL & HBg & FB & Ii & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
  cbn [blk_addr blk_slot fst snd] in OA.
  pose proof (MallocFacts_inv.areach_hdr_ok_proof st LB0 (p, A, n) off AR Hin0 O0 OA) as HOK.
  (* [comment removed for export] *)
  eapply (implM_evt psegs _ _ _ (fun ms1 => ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                  F (Z_to_bv 64 rfree_entry) fc None m (seg_rom psegs))).
  { unfold RFREE_SYM. step. apply evt_done. reflexivity. }
  cbv beta. intros ms' ->.
  eapply (rraw_free_bridge st s p (aadd (blk_slot (p, A, n)) (UNIT * off)) m
            (fun st' s' ms' => rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB0 (p, A, n)) m errv s st' s' ms'
                               /\ leaf_of m (free st (Some (aadd (blk_slot (p, A, n)) (UNIT * off)))) st')).
  - exact Hst.
  - exact HOK.
  - apply rimplT_reach.
    apply (rlibc_free_implT gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB0 lo LO TP ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s st (p, A, n) off errv C Hin0 O0 OA MR MI ST);
      [unfold RFREE_STACK in SLO; lia | exact ERR | exact A0].
  - intros st' s' ms'' [[-> FE] LEAF]. cbv beta.
    destruct FE as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & MI' & ST' & ERR' & MR' & PE & SHR & BLKR & EB & BRKR).
    pose proof (lb_remove_lbrm LB p A n (NoDup_map_perm blk_slot LB0 LB PERM (ci_nodup _ _ C)) Hin) as ELB.
    assert (SLO' : lo <= bv_unsigned sp) by (unfold RFREE_STACK in SLO; lia).
    unfold rfree_post. do 16 eexists. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|].
    split; [exact (rauxv_ok_free st st' lo (bv_unsigned sp) m m' MR LO SLO' PE B AV HB)|].
    split. { apply (rheap_pres_free st st' LB0 (p, A, n) lo (bv_unsigned sp) m m' C MR LO SLO' BLKR SHR PE).
             intros b' Hb'. rewrite ELB in Hb'. eapply In_lbrm_perm; [apply Permutation_sym; exact PERM| exact Hb']. }
    split; [reflexivity|]. split; [reflexivity|].
    exists st', (lbrm LB0 (p, A, n)). split; [rewrite ELB; apply lbrm_perm; exact PERM|].
    split; [reflexivity|]. split; [exact MR'|]. split.
    + (* [comment removed for export] *) unfold brk_link. cbn [ps_brk set_m]. rewrite EB. unfold brk_link in BL.
      destruct (c_brk (ctx st)) as [| |brid boff] eqn:HB0; [exact Logic.I| exact Logic.I|].
      rewrite ?HB0 in BL. unfold conc, get_region. rewrite (BRKR brid boff ltac:(first [exact HB0 | reflexivity])). exact BL.
    + destruct LEAF as (ans & o' & FO).
      eapply (areach_free st LB0 (p, A, n) (aadd (blk_slot (p, A, n)) (UNIT * off)) m o' ans st' AR Hin0); [reflexivity| | exact FO].
      cbn [blk_addr blk_slot fst snd]. rewrite OA, conc_aadd; [reflexivity|].
      cbn [fst]. rewrite <- FB. destruct (go_region _ _ _ (ci_gmetas _ _ C b g HBg)) as (r & Hr & _). rewrite Hr. eexists; reflexivity.
Qed.


End CeilWrap.
End RF_free_spec.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Export PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import F_malloc_enframe MallocBlocks.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocFacts_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_ntf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.MallocKit_B2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocFacts_Bpres F_mm_syscalls F_ntf F_free_C.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_ntf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.F_free_K.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocBlocksR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RMallocKit_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMallocKit_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_realloc_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RF_mm_syscalls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_realloc_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_free_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_realloc_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_free_B.
Import RF_free_C.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RF_ntf RF_free_K.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Import RF_free.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import Malloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocBlocksR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free_spec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMalloc_iface.
Import RF_free_spec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv3.
Import ITree.Exc.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
(* [comment removed for export] *)
From Stdlib Require Import Zify Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import HeapLiaImp.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition RFREE_ESTACK : Z := 8128.

(* [comment removed for export] *)
Definition rfree_entry_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
  RHEAP s LB m -> In (p, A, n) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_ESTACK ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  mem_inv psegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 A ->
  implM psegs (raw_free p) s
        (rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rfree_entry) fc None m (seg_rom psegs)).

Section FREE8128.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis TP : tp = Z_to_bv 64 RATP.

Theorem rlibc_free_implT8128 : forall (ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (s : PState)
    (st : mstate) (blk : block) (off : Z) (errv : word),
  CINV st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  rmrep st m -> mem_inv psegs m ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 8128 ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  a0 = Z_to_bv 64 (blk_addr blk) ->
  rimplT m (free st (Some (aadd (blk_slot blk) (UNIT * off)))) s
        (rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB blk) m errv s)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rfree_entry) fc None m (seg_rom psegs)).
Proof using LO TP.
  intros until errv. intros C Hin Hoff HA MR MI ST SLO ERR A0.
  pose proof (ci_ticks _ _ C) as TK.
  pose proof (KINV_of_CINV _ _ C) as K0.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin) as BK.
  pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
  destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
  assert (off' = off) as ->.
  { rewrite HA in OA. unfold UNIT in OA. lia. }
  clear OA.
  set (c0 := blk_slot blk) in *. set (pf := aadd c0 (UNIT * off)) in *. set (LB' := lbrm LB blk) in *.
  pose proof (ci_gmetas _ _ C b g HB) as GO.
  (nelim (go_region _ _ _ GO) 7%nat; intros r Hr Kr B0 B16 SPAN TOP).
  (nelimp MR 6%nat; intros WF CX GL AR GR SH). (nelimp WF 5%nat; intros Hres WR DJ WA WG).
  (nelim (WR _ _ Hr) 5%nat; intros RB0 RBAL RL0 RBC RF).
  destruct BC as [(r0 & Hr0 & _ & A16 & AEND & AL & UNK) HD BB].
  rewrite <- FB, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
  (nelim (ki_slts _ _ _ K0 _ _ _ SL) 3%nat; intros GMg Ec _). fold c0 in Ec.
  (nelim HK 8%nat; intros v3 lo8 hi C3 V31 C2 C1 OFF). fold c0 in C3, C2, C1, OFF.
  cbn [aadd fst snd] in C3, C2, C1, OFF.
  (* [comment removed for export] *)
  assert (Fp : fst pf = fst b) by (unfold pf; cbn; symmetry; exact FB).
  assert (Cp : conc st pf = r_base r + snd pf) by (apply conc_region'; rewrite Fp; exact Hr).
  assert (Cc : conc st c0 = r_base r + snd c0) by (apply conc_region'; rewrite <- FB; exact Hr).
  assert (Sp : snd pf = snd c0 + 16 * off) by (unfold pf, UNIT; cbn; lia).
  assert (HAp : blk_addr blk = r_base r + snd pf) by (rewrite HA, Cc, Sp; unfold UNIT; lia).
  assert (Sc : snd c0 = snd b + 16 + get_stride (get_meta_rec st g) * i).
  { rewrite Ec. rewrite (slot_start'_mem _ b i (go_mem _ _ _ GO)). cbn. unfold UNIT. lia. }
  pose proof (go_stride _ _ _ GO) as [S16 SM]. pose proof (go_li _ _ _ GO) as LI.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (ETP : bv_unsigned tp + -164 = 210924) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  pose proof LO as LOv. unfold alloc_ceiling in LOv.
  (* [comment removed for export] *)
  assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
  { unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
  assert (SI0 : 0 <= get_stride (get_meta_rec st g) * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SIL : get_stride (get_meta_rec st g) * (i + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
  { apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
  unfold sstart_of in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN.
  assert (P16m : snd pf mod 16 = 0).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. unfold UNIT, IB in *. clear - SIM B16 Hoff. Z.div_mod_to_equations. lia. }
  assert (PHI : snd pf + 16 <= round_up_pg (r_len r)).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. set (stq := get_stride (get_meta_rec st g)) in *.
    unfold UNIT, IB in *.
    assert (16 * off + 16 <= stq) by (clear - OS SZ SM Hoff S16; Z.div_mod_to_equations; lia).
    rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. fold si in SIL. lia. }
  assert (HAR : 0 <= r_base r + snd pf /\ r_base r + snd pf + 16 <= 2^64) by (unfold alloc_ceiling in RBC; pose proof (round_up_pg_ge (r_len r)); lia).
  assert (DRr : r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x55000 <= r_base r) by (apply (rreserved_disjoint1 _ _ RF); lia).
  (* [comment removed for export] *)
  clear SIM SM B16 RBAL AL. change (frozen (snd pf mod 16 = 0)) in P16m.
  assert (EB : aadd pf (- (UNIT * (lo8 + 256 * hi)) - UNIT) = b).
  { unfold aadd. apply injective_projections; cbn; [exact Fp| unfold UNIT in *; lia]. }
  destruct HB as [ai Hgh].
  (* [comment removed for export] *)
  assert (Cb : conc st b = r_base r + snd b) by (apply conc_region'; exact Hr).
  pose proof (shiftr5_range v3) as SR5.
  destruct (rmrep_shadow_read st m (fst c0) r (snd c0 + UNIT * off - 3) v3 MR ltac:(rewrite <- FB; exact Hr) Kr ltac:(unfold UNIT, IB in *; lia) C3) as [_ V3R].
  (* [comment removed for export] *)
  assert (RDB : forall q : aptr, fst q = fst b -> 0 <= snd q < round_up_pg (r_len r) ->
            exists x : byte, bytes_at psegs m (r_base r + snd q) [x] /\ rdv pans_mem m st q = bv_unsigned x).
  { intros q Fq Hq.
    assert (Hrq : s_regions st !! fst q = Some r) by (rewrite Fq; exact Hr).
    destruct (SH _ r Hr Kr) as [WRr _].
    assert (W1 : wr_at psegs m (r_base r + snd q) 1).
    { (nelim WRr 3%nat; intros W0 Wn W). split; [lia|]. split; [pose proof (round_up_pg_ge (r_len r)); unfold alloc_ceiling in RBC; lia|].
      intros j Hj. replace (r_base r + snd q + j) with (r_base r + (snd q + j)) by lia. apply W. lia. }
    (nelim (rwr_at_bytes_exist m _ 1 W1 ltac:(lia) ltac:(pose proof (round_up_pg_ge (r_len r)); lia)) 3%nat; intros bs L B).
    destruct bs as [|x [|]]; try discriminate. exists x. split; [exact B|].
    eapply (rrdv_cur m st m q r x MR Hrq Kr Hq); [intros; reflexivity| exact B]. }
  (* [comment removed for export] *)
  unfold free.
  eapply (rimplT_bind m (free_hdr st pf) _ s
           (fun r1 s' ms' => s' = s /\ r1 = Some (hdr_st st pf, g, i) /\
              rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')).
  { unfold free_hdr, get_meta. apply rimplT_guard. intros _.
    apply rimplT_rd16. apply rimplT_rd8. cbv zeta. apply rimplT_rd8.
    rewrite (rdv_known m st (aadd pf (-4)) 0) by (cbn [aadd fst snd]; replace (snd pf + -4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia); exact OK).
    rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
    rewrite (rdv_known m st (aadd pf (-2)) lo8) by (cbn [aadd fst snd]; replace (snd pf + -2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia); exact C2).
    rewrite (rdv_known m st (aadd (aadd pf (-2)) 1) hi) by (cbn [aadd fst snd]; replace (snd pf + -2 + 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia); exact C1).
    cbn [Z.eqb negb]. rewrite EB. unfold get_group. rewrite Hgh. cbn [g_meta].
    apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
    destruct (s_areas st !! area_of g) as [ar|] eqn:AR1; [| apply rimplT_guard; intros; discriminate].
    apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
    unfold slot_start. rewrite (go_mem _ _ _ GO). cbv beta zeta.
    apply Z.eqb_eq in G15. apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
    rewrite V31 in G12, G13, G14, G16.
    set (e := aadd (aadd b (UNIT + get_stride (get_meta_rec st g) * Z.land v3 31)) (get_stride (get_meta_rec st g) - IB)).
    assert (Fe : fst e = fst b) by reflexivity.
    assert (Se : snd e = snd b + 16 + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - 4).
    { unfold e. cbn [aadd snd]. rewrite V31. unfold UNIT, IB. lia. }
    (* [comment removed for export] *)
    pose proof (go_sc _ _ _ GO) as GSC.
    assert (WALK : forall r32 : Z,
      (160 <= v3 -> Z.shiftr v3 5 = 5 /\ 5 <= r32 < 2^32
          /\ bytes_at psegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 4) (le4 (wz r32))
          /\ bytes_at psegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 5) [b8 0]) ->
      (if 160 <=? v3 then r32 else Z.shiftr v3 5) <= conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf) ->
      bytes_at psegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (if 160 <=? v3 then r32 else Z.shiftr v3 5)) [b8 0] ->
      bytes_at psegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB) [b8 0] ->
      evt psegs (fun ms' => s = s /\ Some (hdr_st st pf, g, i) = Some (hdr_st st pf, g, i) /\
                 rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom psegs))).
    { intros r32 BIG RSVLE RB0r RE0.
      eapply evt_mono.
      { eapply (rfree_head ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo st pf r g (mkGhdr (Some g) ai) ar v3 lo8 hi r32);
          first [exact MR | exact MI | exact TK | exact ST | exact LO | exact Kr | idtac].
        all: rewrite ?EB, ?V31.
        - lia.
        - rewrite Fp. exact Hr.
        - rewrite A0, HAp. apply unsigned_lit. lia.
        - exact P16m.
        - rewrite Sp, Sc. lia.
        - unfold pf in OFF |- *. cbn [aadd snd] in OFF |- *. lia.
        - exact PHI.
        - replace (snd pf - 4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia). unfold pf; cbn [aadd fst]. exact OK.
        - replace (snd pf - 3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C3.
        - replace (snd pf - 2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C2.
        - replace (snd pf - 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C1.
        - exact Hgh.
        - reflexivity.
        - exact (go_slot _ _ _ GO).
        - (nelim (go_slot _ _ _ GO) 6%nat; intros a ara k Ha Hk ->). (nelim (WA a ara Ha) 4%nat; intros rg0 _ A00 _). cbn. unfold AREA_HDR, META_SIZE. lia.
        - exact (go_mem _ _ _ GO).
        - exact AR1.
        - exact G15.
        - exact (go_avail _ _ _ GO).
        - exact (go_freed _ _ _ GO).
        - exact (proj2 (proj2 (proj2 (ki_cx _ _ _ K0)))).
        - lia.
        - rewrite (go_freeable _ _ _ GO). lia.
        - lia.
        - pose proof (go_maplen _ _ _ GO). lia.
        - exact G12.
        - exact G13.
        - exact G14.
        - intros Hsc. apply Z.ltb_lt in Hsc. rewrite Hsc in G16. apply andb_true_iff in G16. destruct G16 as [G16a G16b].
          apply Z.leb_le in G16a. apply Z.ltb_lt in G16b. lia.
        - intros Hsc. destruct (Z.ltb_spec (m_sizeclass (get_meta_rec st g)) 48); [lia|]. apply Z.eqb_eq in G16. exact G16.
        - intros Hml. destruct (Z.eqb_spec (m_maplen (get_meta_rec st g)) 0); [lia|]. cbn [negb] in G17. apply Z.leb_le in G17.
          unfold UNIT in G17.
          replace (m_maplen (get_meta_rec st g) * 4096) with (m_maplen (get_meta_rec st g) * 256 * 16) in G17 by lia.
          rewrite Z.div_mul in G17 by lia. lia.
        - lia.
        - exact S16.
        - rewrite Cb, Sp, Sc. unfold UNIT, IB in *. lia.
        - rewrite Cb. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia.
        - exact BIG.
        - exact RSVLE.
        - exact RB0r.
        - exact RE0.
        - intros b' gh' Hb' Fb'. specialize (HD b' gh' Hb' ltac:(rewrite Fb', Fp; exact FB)).
          rewrite (conc_region' st b' r) in HD by (rewrite Fb', Fp; exact Hr). unfold IB in HD.
          clear - HD HAp SZ. lia. (* [comment removed for export] *) }
      intros ms' FP. split; [reflexivity|]. split; [reflexivity|]. unfold hdr_st. rewrite <- V31. exact FP. }
    (* [comment removed for export] *)
    assert (EQE : forall k, r_base r + snd (aadd e (- k)) = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - k).
    { intros k. cbn [aadd snd]. rewrite Se, Cb. unfold UNIT, IB. lia. }
    assert (EQE0 : r_base r + snd e = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB).
    { rewrite Se, Cb. unfold UNIT, IB. lia. }
    assert (ERNG : snd e + 1 <= round_up_pg (r_len r) /\ snd pf <= snd e /\ 16 <= snd e).
    { rewrite Se, Sp, Sc. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia. }
    assert (DIFF : snd e - snd pf = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf)).
    { rewrite Se, Cb. unfold UNIT, IB. lia. }
    
    unfold get_nominal_size. apply rimplT_rd8. cbv zeta.
    rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
    apply rimplT_if; intros HR5.
    - (* [comment removed for export] *)
      apply Z.leb_le in HR5.
      apply rimplT_guard; intros G20. apply Z.eqb_eq in G20.
      apply rimplT_rd32. 
      (nelim (RDB (aadd e (-4)) Fe ltac:(cbn [aadd snd]; lia)) 3%nat; intros x0 BX0 RX0). rewrite RX0. 
      (nelim (RDB (aadd (aadd e (-4)) 1) Fe ltac:(cbn [aadd snd]; lia)) 3%nat; intros x1 BX1 RX1). rewrite RX1. 
      (nelim (RDB (aadd (aadd e (-4)) 2) Fe ltac:(cbn [aadd snd]; lia)) 3%nat; intros x2 BX2 RX2). rewrite RX2.
      (nelim (RDB (aadd (aadd e (-4)) 3) Fe ltac:(cbn [aadd snd]; lia)) 3%nat; intros x3 BX3 RX3). rewrite RX3.
      pose proof (bytes4_range x0 x1 x2 x3) as U32. pose proof (le4_of_bytes x0 x1 x2 x3) as LE4.
      set (r32 := bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3) in *.
      apply rimplT_guard; intros G21. apply Z.leb_le in G21.
      apply rimplT_rd8. (nelim (RDB (aadd e (-5)) Fe ltac:(cbn [aadd snd]; lia)) 3%nat; intros x5 BX5 RX5). rewrite RX5.
      apply rimplT_guard; intros G25. apply Z.eqb_eq in G25.
      apply rimplT_guard; intros G22. apply Z.leb_le in G22.
      apply rimplT_rd8. (nelim (RDB (aadd e (- r32)) Fe ltac:(cbn [aadd snd]; lia)) 3%nat; intros xc BXc RXc). rewrite RXc.
      apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
      apply rimplT_rd8. (nelim (RDB e Fe ltac:(lia)) 3%nat; intros xe BXe RXe). rewrite RXe.
      apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
      apply rimplT_ret. rewrite V31.
      specialize (SR5 V3R). pose proof (shiftr5_ge v3 V3R HR5) as V160.
      assert (H160 : (160 <=? v3) = true) by (apply Z.leb_le; exact V160).
      
      apply (WALK r32).
      + intros _. split; [exact G20|]. split; [lia|]. split.
        * rewrite <- (EQE 4). rewrite LE4. change [x0; x1; x2; x3] with ([x0] ++ ([x1] ++ ([x2] ++ [x3]))).
          apply bytes_at_app. split; [exact BX0|]. apply bytes_at_app. split; [cbn [length Z.of_nat Pos.of_succ_nat]; cbn [aadd snd] in BX1 |- *; replace (r_base r + (snd e + -4) + 1) with (r_base r + (snd e + -4 + 1)) by lia; exact BX1|].
          apply bytes_at_app. split; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; cbn [aadd snd] in BX2, BX3 |- *.
          -- replace (r_base r + (snd e + -4) + 1 + 1) with (r_base r + (snd e + -4 + 2)) by lia. exact BX2.
          -- replace (r_base r + (snd e + -4) + 1 + 1 + 1) with (r_base r + (snd e + -4 + 3)) by lia. exact BX3.
        * rewrite <- (EQE 5), <- (byte_zero_list x5 G25). exact BX5.
      + rewrite H160, <- DIFF. exact G22.
      + rewrite H160, <- (EQE r32), <- (byte_zero_list xc G23). exact BXc.
      + rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe.
    - (* [comment removed for export] *)
      apply Z.leb_gt in HR5.
      apply rimplT_guard; intros G22. apply Z.leb_le in G22.
      apply rimplT_rd8. (nelim (RDB (aadd e (- Z.shiftr v3 5)) Fe ltac:(cbn [aadd snd]; clear - ERNG HR5 SR5 V3R; first [heap_lia_imp | lia])) 3%nat; intros xc BXc RXc).  (* [comment removed for export] *) rewrite RXc.
      apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
      apply rimplT_rd8. (nelim (RDB e Fe ltac:(lia)) 3%nat; intros xe BXe RXe). rewrite RXe.
      apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
      apply rimplT_ret. rewrite V31.
      specialize (SR5 V3R). pose proof (shiftr5_lt v3 V3R HR5) as V160.
      assert (H160 : (160 <=? v3) = false) by (apply Z.leb_gt; exact V160).
      
      apply (WALK 0).
      + intros H. exfalso. clear -H V160. lia.
      + rewrite H160, <- DIFF. exact G22.
      + rewrite H160, <- (EQE (Z.shiftr v3 5)), <- (byte_zero_list xc G23). exact BXc.
      + rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe. }

  intros r1 s' ms1 nelH_; (nelim nelH_ 3%nat; intros -> -> FH). cbv beta iota.
  (nelim FH 13%nat; intros x1 x5 x6 x7 junk m1 -> PE1 WM1 MI1 ST1 FR1 MR1).
  set (st1 := hdr_st st pf) in *.
  assert (TK1 : ticks_ok st1) by (unfold st1; apply ticks_ok_hdr_st; exact TK).
  assert (MSL1 : meta_slot st1 g) by (exact (go_slot _ _ _ GO)).
  assert (HK123 : forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w).
  { intros k Hk. unfold pf; cbn [aadd fst snd].
    assert (CS : k = 1 \/ k = 2 \/ k = 3) by lia.
    destruct CS as [-> |[-> | ->]];
      [exists hi; replace (snd c0 + UNIT * off - 1) with (snd c0 + UNIT * off - 1) by lia
      |exists lo8|exists v3];
      [rewrite <- C1 | rewrite <- C2 | rewrite <- C3]; f_equal; unfold UNIT; lia. }
  assert (FP1 : forall a, rfree_fp st1 lo (bv_unsigned sp - 48) a -> rfree_fp st lo (bv_unsigned sp) a).
  { intros a Ha. eapply (rfree_fp_hdr_st st pf lo (bv_unsigned sp) (bv_unsigned sp - 48) a TK HK123); [lia| exact Ha]. }
  assert (ERR1 : rw_cells psegs m1 (errno_addr tp) [C4 errv]).
  { eapply rpres_except_rw_cells; [exact PE1 | exact ERR |]. cbn [cells_size csize Nat.add]. intros a Ha.
    rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
  assert (TF : Z.testbit (m_freed (get_meta_rec st g)) i = false).
  { destruct (Z.testbit (m_freed (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; left; exact E| reflexivity]. }
  assert (TA : Z.testbit (m_avail (get_meta_rec st g)) i = false).
  { destruct (Z.testbit (m_avail (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; right; exact E| reflexivity]. }
  (* [comment removed for export] *)
  assert (BLKR : forall stX blk', s_regions stX = s_regions st -> In blk' (lbrm LB blk) -> exists r', s_regions stX !! fst (blk_slot blk') = Some r').
  { intros stX blk' ERX Hb'. rewrite ERX. unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hb' _].
    destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' Hb') as [(r' & Hr' & _) _ _]. exists r'. exact Hr'. }
  unfold free_tail. cbv zeta. change (get_meta_rec st1 g) with (get_meta_rec st g).
  apply rimplT_guard. intros _.
  apply rimplT_if; intros HC.
  - (* [comment removed for export] *)
    apply negb_true_iff in HC. apply orb_false_iff in HC. destruct HC as [Hfz Hall]. apply Z.eqb_neq in Hfz. apply Z.eqb_neq in Hall.
    apply rimplT_ret.
    eapply evt_mono.
    { eapply (rfree_triv ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 junk lo st st1 g i);
        first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact Hfz | exact Hall | exact FR1 | exact ST1 | exact LO | reflexivity | idtac].
      all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
    intros ms' TPo. unfold rftriv_post in TPo.
    (nelim TPo 22%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 m' -> PE' WM' MI' ST' MR').
    split; [reflexivity|]. nexists 16%nat. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE' | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
             rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
    split; [exact MR'|].
    split. { eapply rpres_except_mono; [eapply rpres_except_trans; [exact PE1| exact PE']|]. intros a Ha. left. exact Ha. }
    split; [intros rid r' H; exact H|].
    split; [intros blk' Hb'; apply (BLKR _ blk' eq_refl Hb')|].
    split; reflexivity.
  - (* [comment removed for export] *)
    
    assert (HNT : m_freed (get_meta_rec st g) = 0 \/ Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) + bit i = mask_upto (m_last_idx (get_meta_rec st g))).
    { apply negb_false_iff in HC. apply orb_true_iff in HC. destruct HC as [HC|HC]; apply Z.eqb_eq in HC; auto. }
    eapply rimplT_evt.
    { eapply (rfree_tocall ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 st1 g i);
        first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact HNT | idtac].
      all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
    intros ms2 nelH_; (nelim nelH_ 7%nat; intros y2 y3 y4 y5 y6 y7 ->).
    assert (HLB : forall b', In b' LB' -> In b' LB /\ blk_slot b' <> blk_slot blk).
    { intros b' Hb'. unfold LB', lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [H1 H2]. split; [exact H1|].
      intros E. rewrite E, aptr_eqb_refl in H2. exact H2. }
    assert (K1 : KINV st1 LB' 0).
    { unfold st1. eapply (KINV_hdr_st st LB LB' 0 pf blk r C Hin); [| exact HLB | rewrite Fp, FB; reflexivity | rewrite Fp; exact Hr | symmetry; exact HAp | exact P16m].
      unfold LB', lbrm. apply (KINV_filter_slot st LB 0 (fun s => negb (aptr_eqb s (blk_slot blk)))). exact K0. }
    assert (L1 : LPRE st1 LB' 0 g b i).
    { unfold LB', lbrm. apply (LPRE_intro st1 LB 0 g b i blk); [exact (ki_slts _ _ _ K0) | exists ai; exact Hgh | exact SL | exact NFR | exact NG | pose proof (go_sc _ _ _ GO); change (get_meta_rec st1 g) with (get_meta_rec st g); lia]. }
    assert (Z1 : ZINV st1 []) by (unfold st1; apply ZINV_hdr_st; apply (ZINV_of_CINV _ _ C)).
    assert (OOK1 : oracle_ok m m1 st1).
    { unfold st1. apply oracle_ok_hdr_st; [exact TK|]. eapply (roracle_ok_pres m m m1 st lo (bv_unsigned sp) m); [apply oracle_ok_refl | exact MR | exact LO | exact PE1]. }
    change (wz (conc st g)) with (Z_to_bv 64 (conc st1 g)). change (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc st1 g)).
    eapply (rntf_implT gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc m LB' lo LO);
      [exact K1 | exact L1 | exact Z1 | exact MR1 | exact MI1 | exact OOK1 | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; unfold FUEL; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]; lia |].
    (* [comment removed for export] *)
    
    intros st2 mi ms3 NQ. unfold rntf_q in NQ.
    (nelim NQ 26%nat; intros u0 u1 u2 a0v a1v u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 m3 -> MI3 ST3 MR3 PE3 [c3 KI3] ZI3 FR3 RES3 OOK3).
    rewrite unsigned_lit in ST3, PE3 by lia.
    replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in PE3 by lia.
    replace (ret_pc (Z_to_bv 64 0x15498)) with (Z_to_bv 64 0x15498) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (PE13 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
    { eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_mono; [exact PE3| exact FP1]. }
    assert (FR3' : rw_cells psegs m3 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rpres_except_rw_cells; [exact PE3 | exact FR1 |]. cbn [cells_size csize Nat.add length]. intros a Ha Hfp.
      pose proof (rfree_fp_lt st1 m1 lo (bv_unsigned sp - 48) a MR1 LO ltac:(lia) Hfp). lia. }
    assert (ERR3 : rw_cells psegs m3 (errno_addr tp) [C4 errv]).
    { eapply rpres_except_rw_cells; [exact PE3 | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
      rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR1 | exact LO | lia]. }
    pose proof (nf_regions _ _ FR3) as ER3. change (s_regions st1) with (s_regions st) in ER3.
    pose proof (nf_brk _ _ FR3) as EB3. change (ctx st1) with (ctx st) in EB3.
    destruct mi as [[bm len]|].
    + (* [comment removed for export] *)
      cbv beta iota.
      destruct RES3 as (-> & -> & LEN & SND & (r2 & Hr2 & Kr2 & Lr2) & NOG).
      replace (negb (len =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
      pose proof Hr2 as Hr2'. rewrite ER3 in Hr2'.
      (nelim (WR _ _ Hr2') 5%nat; intros R2B0 R2AL R2L R2C R2F). unfold alloc_ceiling in R2C.
      assert (R2D : r_base r2 + round_up_pg (r_len r2) <= 0x10000 \/ 0x55000 <= r_base r2) by (apply (rreserved_disjoint1 _ _ R2F); lia).
      assert (CB2 : conc st2 bm = r_base r2) by (rewrite (conc_region' st2 bm r2 Hr2); lia).
      pose proof (round_up_pg_ge (r_len r2)) as RU2.
      eapply rimplT_evt.
      { eapply (rfree_tomunmap sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra (wz (conc st2 bm)) _ _ F fc m3 junk lo len st2 errv);
          first [exact TP | exact MR3 | exact MI3 | exact LEN | exact FR3' | exact ERR3 | exact ST3 | exact LO | lia]. }
      intros ms4 FM. unfold rfmun_post in FM.
      (nelim FM 22%nat; intros w0 w1 w2 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 m4 -> MU4 WM4 MI4 ST4 FR4 ERR4 MR4).
      eapply (rimplT_munmap m (conc st2 bm) len _ s).
      { eapply rmunmap_spec.
        - rewrite unsigned_lit by lia. exact ST4.
        - exact ERR4.
        - exact MI4.
        - unfold wz. reflexivity.
        - unfold wz. reflexivity.
        - lia.
        - rewrite Lr2, mmap_len_round. lia.
        - lia.
        - rewrite unsigned_lit by lia. lia.
        - rewrite ETP, unsigned_lit by lia. lia.
        - rewrite Lr2, mmap_len_round, unsigned_lit by lia. lia.
        - rewrite ETP, Lr2, mmap_len_round. lia.
        - rewrite TP; unfold RATP; rewrite unsigned_lit by lia. lia. }
      intros a ms5 MP. cbv beta. unfold rmunmap_post in MP.
      (nelim MP 22%nat; intros z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 m5 -> MU5 _ MI5 ST5 ERR5 ERNG).
      rewrite (munmap_ok_range_val a ERNG).
      apply rimplT_ret.
      replace (ret_pc (Z_to_bv 64 0x154c8)) with (Z_to_bv 64 0x154c8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      rewrite unsigned_lit in MU5, ST5 by lia. rewrite Lr2, mmap_len_round, ETP in MU5.
      (* [comment removed for export] *)
      assert (AMC2 : amc (ctx st2) = amc (ctx st)) by (rewrite (nf_amc _ _ FR3); reflexivity).
      assert (MP2 : ci_mptrs st2) by (eapply (ci_mptrs_frame st st2 (ci_mp _ _ C) AMC2); [rewrite (nf_areas _ _ FR3); reflexivity| exact ER3]).
      assert (NOG' : forall b' gh, s_groups st2 !! b' = Some gh -> fst b' <> fst bm) by (intros b' gh Hb'; exact (NOG b' gh Hb')).
      pose proof (rptrs_in_norid st2 LB' c3 (fst bm) r2 m4 KI3 ZI3 MR4 Hr2 Kr2 NOG' MP2) as PTR.
      pose proof (rmrep_drop_region st2 (fst bm) PTR m4 MR4) as MRd4.
      assert (MRd5 : rmrep (drop_region (fst bm) st2) m5).
      { eapply (rmrep_after_munmap st2 (fst bm) r2 m4 m5); [exact MRd4 | exact MR4 | exact Hr2 | exact Kr2 | rewrite <- CB2; exact MU5 | lia]. }
      assert (FR5 : rw_cells psegs m5 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rrw_cells_agree'; [exact FR4|]. cbn [cells_size csize Nat.add length]. intros x Hx. apply MU5. rewrite wa_unsigned by lia.
        rewrite ?ETP. cbn [outside]. repeat split; lia. }
      eapply evt_mono.
      { eapply (rfree_fin1 sp gp tp z0 z1 z2 s0 s1 (munmap_ret a) z3 z4 z5 z6 z7 z8 z9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z10 z11 z12 z13 _ ra (sx32 errv) (wz (conc st2 bm)) (wz len) (rg_errno a errv) F fc m5 junk lo (drop_region (fst bm) st2) errv);
          first [exact TP | exact MRd5 | exact MI5 | exact FR5 | apply le4_sx32 | exact ERR5 | exact ST5 | exact LO | lia]. }
      intros ms' FIN. unfold rffin_post in FIN.
      (nelim FIN 23%nat; intros v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 m' -> MUf WMf MIf STf ERRf MRf).
      split; [reflexivity|]. nexists 16%nat. split; [reflexivity|].
      split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
      split.
      { (* [comment removed for export] *)
        assert (DR : forall x, r_base r2 <= x < r_base r2 + round_up_pg (r_len r2) -> DROPPED st (drop_region (fst bm) st2) x).
        { intros x Hx. exists (fst bm), r2. split; [exact Hr2'|]. split; [| split; [exact Kr2| exact Hx]].
          cbn [drop_region s_regions set_shadow set_regions]. apply lookup_delete_eq. }
        eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
        eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m3 m4 MU4)|].
        { intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 210924 <= a < 210928)); [| exact NC].
          cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
        eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m4 m5 MU5)|].
        { intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 210924 <= a < 210928)); [| exact NC].
          cover_intervals ltac:(fun y Hy => first [left; apply rfree_fp_stack; heap_lia_pruned | right; right; heap_lia_pruned | right; left; apply DR; heap_lia_pruned]). }
        eapply (rpres_except_of_munch_nw _ _ m5 m' MUf).
        intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 210924 <= a < 210928)); [| exact NC].
        cover_intervals ltac:(fun y Hy => first [left; apply rfree_fp_stack; heap_lia_pruned | right; right; heap_lia_pruned]). }
      split.
      { intros rid r' H. cbn [drop_region s_regions set_shadow set_regions] in H. apply lookup_delete_Some in H. destruct H as [_ H]. rewrite <- ER3. exact H. }
      split.
      { intros blk' Hb'. pose proof (proj1 (List.Forall_forall _ _) (ki_blks _ _ _ KI3) blk' Hb') as BK'.
        destruct BK' as [(g' & i' & bb & SL' & HB' & FB' & _) _ _].
        (nelim (go_region _ _ _ (ki_gmetas _ _ _ KI3 bb g' HB')) 3%nat; intros rr Hrr _).
        exists rr. cbn [drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne; [rewrite <- FB'; exact Hrr|].
        intros E. destruct HB' as [ai' Hbb]. apply (NOG bb _ Hbb). rewrite E. exact FB'. }
      split; [exact EB3|].
      intros brid boff HB0. cbn [drop_region s_regions set_shadow set_regions ctx s_ctx].
      rewrite <- EB3 in HB0. (nelim (ki_bk _ _ _ KI3 brid boff HB0) 3%nat; intros rb Hrb Krb).
      rewrite lookup_delete_ne; [rewrite ER3; reflexivity |].
      intros E. rewrite <- E, Hr2 in Hrb. assert (rb = r2) by congruence. subst rb. rewrite Kr2 in Krb. discriminate.
    + (* [comment removed for export] *)
      
      cbv beta iota. cbn in RES3. subst a1v.
      apply rimplT_ret.
      eapply evt_mono.
      { eapply (rfree_fin0 sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra a0v _ _ F fc m3 junk lo st2 errv);
          first [exact TP | exact MR3 | exact MI3 | exact FR3' | exact ERR3 | exact ST3 | exact LO | lia]. }
      intros ms' FIN. unfold rffin_post in FIN.
      (nelim FIN 23%nat; intros v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 m' -> MUf WMf MIf STf ERRf MRf).
      split; [reflexivity|]. nexists 16%nat. split; [reflexivity|].
      split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
      split.
      { eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
        eapply (rpres_except_of_munch_nw _ _ m3 m' MUf).
        intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st2 a \/ 210924 <= a < 210928)); [| exact NC].
        cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
      split; [intros rid r' H; rewrite <- ER3; exact H|].
      split; [intros blk' Hb'; apply (BLKR st2 blk' ER3 Hb')|].
      split; [exact EB3|].
      intros brid boff _. rewrite ER3. reflexivity.
Qed.
End FREE8128.

Theorem rfree_entry_spec : rfree_entry_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
         HP Hin AV HB ST LO SLO ERR MI TP A0.
  (nelim HP 6%nat; intros st LB0 PERM Hst MR [BL AR]).
  assert (Hin0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, n) Hin0) as BK.
  destruct BK as [(g & i & b & SL & HBg & FB & Ii & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
  cbn [blk_addr blk_slot fst snd] in OA.
  pose proof (MallocFacts_inv.areach_hdr_ok_proof st LB0 (p, A, n) off AR Hin0 O0 OA) as HOK.
  eapply (rraw_free_bridge st s p (aadd (blk_slot (p, A, n)) (UNIT * off)) m
            (fun st' s' ms' => rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB0 (p, A, n)) m errv s st' s' ms'
                               /\ leaf_of m (free st (Some (aadd (blk_slot (p, A, n)) (UNIT * off)))) st')).
  - exact Hst.
  - exact HOK.
  - apply rimplT_reach.
    apply (rlibc_free_implT8128 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB0 lo LO TP ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s st (p, A, n) off errv C Hin0 O0 OA MR MI ST);
      [unfold RFREE_ESTACK in SLO; lia | exact ERR | exact A0].
  - intros st' s' ms'' [[-> FE] LEAF]. cbv beta.
    (nelim FE 26%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 m' -> MI' ST' ERR' MR' PE SHR BLKR EB BRKR).
    pose proof (lb_remove_lbrm LB p A n (NoDup_map_perm blk_slot LB0 LB PERM (ci_nodup _ _ C)) Hin) as ELB.
    assert (SLO' : lo <= bv_unsigned sp) by (unfold RFREE_ESTACK in SLO; lia).
    unfold rfree_post. nexists 16%nat. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|].
    split; [exact (rauxv_ok_free st st' lo (bv_unsigned sp) m m' MR LO SLO' PE B AV HB)|].
    split. { apply (rheap_pres_free st st' LB0 (p, A, n) lo (bv_unsigned sp) m m' C MR LO SLO' BLKR SHR PE).
             intros b' Hb'. rewrite ELB in Hb'. eapply In_lbrm_perm; [apply Permutation_sym; exact PERM| exact Hb']. }
    split; [reflexivity|]. split; [reflexivity|].
    exists st', (lbrm LB0 (p, A, n)). split; [rewrite ELB; apply lbrm_perm; exact PERM|].
    split; [reflexivity|]. split; [exact MR'|]. split.
    + (* [comment removed for export] *) unfold brk_link. cbn [ps_brk set_m]. rewrite EB. unfold brk_link in BL.
      destruct (c_brk (ctx st)) as [| |brid boff] eqn:HB0; [exact Logic.I| exact Logic.I|].
      rewrite ?HB0 in BL. unfold conc, get_region. rewrite (BRKR brid boff ltac:(first [exact HB0 | reflexivity])). exact BL.
    + (nelim LEAF 3%nat; intros ans o' FO).
      eapply (areach_free st LB0 (p, A, n) (aadd (blk_slot (p, A, n)) (UNIT * off)) m o' ans st' AR Hin0); [reflexivity| | exact FO].
      cbn [blk_addr blk_slot fst snd]. rewrite OA, conc_aadd; [reflexivity|].
      cbn [fst]. rewrite <- FB. (nelim (go_region _ _ _ (ci_gmetas _ _ C b g HBg)) 3%nat; intros r Hr _). rewrite Hr. eexists; reflexivity.
Qed.


End CeilWrap.
