(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_F_malloc_free A_F_malloc_fast A_F_free A_F_free_spec A_MallocKit_AB A_MallocKit_A A_MallocBlocks A_MallocHINV A_MallocFacts_B A_Malloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl MallocInv MI_Arith MI_Inv MI_Kit MI_Read MI_Geom MI_Pres2 MI_Cnt MI_WFree MI_WGroup Realloc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog ProgR A_Realloc A_Realloc2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RMallocRep RMallocTree RMallocKit_A RMallocKit_B RMalloc_iface RMalloc_ifaceP RF_free_spec RRealloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RF_realloc_hdr RF_realloc_hdrS RF_realloc_dec RF_realloc_stc RF_realloc_inplS RF_realloc_moveS RF_realloc_remapS.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Section NULL.
Hypothesis HMAL : rmalloc_impl_stmt.
Theorem rrealloc_null_spec_proof : rrealloc_null_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
  intros HEAP AUXB SB ST CLO LO ERR MI TP HA0 HA1 HN. subst a0 a1. unfold RREALLOC_SYM. unfold RREALLOC_STACK in LO.

  eapply (implM_evt rsegs _ _ _ (fun ms1 => ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                  F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs))).
  { step. step. if_true. step. step. apply evt_done. reflexivity. }
  cbv beta. intros ms' ->. eapply HMAL; try eassumption; [lia| reflexivity].
Qed.
End NULL.

Section TOP.
Hypothesis HMAL : rmalloc_impl_stmt.
Hypothesis HFREE : rfree_impl_stmt.

Theorem rrealloc_spec_proof : rrealloc_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A old n lo B errv oldbs.
  intros HP Hin OLDB OLEN AUXB SB ST CLO LO ERR MI TP HA0 HA1 HN. subst a0 a1.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof CLO as CLOv. pose_ceil. pose proof LO as LOv. unfold RREALLOC_STACK, RMALLOC_STACK in LOv.
  assert (ETP : bv_unsigned tp + -164 = 422892) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  pose proof (RHEAP_block_range_proof s LB m _ HP Hin) as BR. cbn [blk_addr blk_size fst snd] in BR. destruct BR as (Ap & A16 & _ & ACE & AIMG).
  pose_ceil.
  destruct HP as (st & LB0 & PERM & Hst & RMR & [HBL AR]).
  assert (Hin0 : In (p, A, old) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (OLDB0 : id (bytes_at rsegs m A oldbs)) by exact OLDB.
  unfold RREALLOC_SYM. unfold implM. iprefix.

  step. step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. clear - K0 Ap. lia. } clear K0.

  carve_frame 64%nat ST.
  step. step. step. step. step. step. step. step. step.

  step. step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. clear - K1 HN. cbn in K1. lia. }
  clear K1. apply evt_done.
  lazymatch goal with |- impl _ _ _ _ (MS _ _ _ _ _ ?mX _) => rename mX into m1 end.
  set (sp1 := bv_unsigned sp + -64) in *.
  assert (RMR1 : rmrep st m1).
  { eapply rmrep_transport_unowned; [exact RMR| exact MU| exact WM|].
    intros lo' hi' a Hin' Ha RF. destruct (rrepfoot_where st m a RMR RF) as [AC _]. pose_ceil.
    destruct Hin' as [E'|[]]. inversion E'; subst lo' hi'. clear - Ha AC CLOv LOv. lia. }
  assert (PRES1 : rpres_except (fun a => (lo <= a < bv_unsigned sp) \/ (RERRNO <= a < RERRNO + 4)) m m1).
  { eapply rpres_except_of_munch'; [exact MU| exact WM|]. intros lo' hi' [E'|[]] x Hx. inversion E'; subst lo' hi'. left. clear - Hx LOv. lia. }
  assert (AUX1 : rauxv_ok m1 B).
  { eapply rauxv_ok_frame; [exact AUXB| exact MU| exact WM|]. constructor; [| constructor]. cbn [fst snd]. unfold RAUXV_CELL, RLIBC. clear - SB CLOv LOv. lia. }
  lazymatch goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
  clear MU WM.

  evar (a2w : word).
  destruct (hdr_spec ra (Z_to_bv 64 sp1) gp tp t0 t1 t2 s0 s1 a2w a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 st LB0 p old A n RMR1 MI1 AR Hin0 HN)
    as (g & bg & idx & r & SL & HM & Hr & Kr & FC & CC & CB & HO & FITA & SPc & RCEIL & SCR & SC63 & WALK).
  destruct (realloc_geo_facts ref_reserved st LB0 p A old AR Hin0 g bg idx SL HM)
    as (off & r' & Hoff & HA & FIT & _ & S16 & SMOD & SSTR & Hr' & _ & _ & Ec & B0 & BG16 & Hidx & LI31 & SPAN & _ & RB0 & K3).
  rewrite Hr in Hr'. assert (r' = r) as -> by congruence.
  cbv delta [MR] in S16, SMOD, SSTR, Ec, Hidx, LI31, SPAN, K3, FIT.
  set (mr := get_meta_rec st g) in *. set (stride := get_stride mr) in *.
  set (Bg := conc st bg) in *. set (E := Bg + 16 + stride * (idx + 1) - 4).
  set (sc := m_sizeclass mr) in *. set (mword := m_last_idx mr + 32 * m_freeable mr + 64 * sc + 4096 * m_maplen mr).
  assert (SK0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; clear - S16 Hidx; lia).
  assert (SK1 : stride * (idx + 1) = stride * idx + stride) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; reflexivity).
  assert (HE : E = conc st (fst p) + stride - 4) by (subst E; rewrite CC, SK1; fold Bg; clear; lia).
  pose proof (round_up_pg_ge (r_len r)) as RUP.

  eapply (impl_evt _ _ _ _ _ (fun ms2 : machine_state =>
     (exists t1v y7 a2v a4v a5v a7v y28 y29, n <= E - A /\ n < MMAP_THRESHOLD /\ sc <= size_to_class n + 1 /\
        ms2 = MS (mkR ra (Z_to_bv 64 sp1) gp tp (Z_to_bv 64 E) t1v y7 s0 (wz (conc st g)) (Z_to_bv 64 A) (Z_to_bv 64 n) a2v (Z_to_bv 64 sc) a4v a5v
                      (Z_to_bv 64 (E + 4)) a7v (Z_to_bv 64 (A + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6) F (Z_to_bv 64 0x49dd8) fc None m1 (seg_rom rsegs))
     \/ (exists y7 a5v y28 y29, MMAP_THRESHOLD <= n /\ sc = 63 /\
        ms2 = MS (mkR ra (Z_to_bv 64 sp1) gp tp (Z_to_bv 64 E) (Z_to_bv 64 (Bg + stride * idx + 16)) y7 s0 (wz (conc st g)) (Z_to_bv 64 A) (Z_to_bv 64 n)
                      (wz Bg) (Z_to_bv 64 sc) (wz mword) a5v (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - A)) (Z_to_bv 64 (A + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
                 F (Z_to_bv 64 0x49cb0) fc None m1 (seg_rom rsegs))
     \/ (exists t0v t1v y7 s0v s1v a2v a3v a4v a5v a6v a7v s3v s4v s5v s6v y28 y29, move_cond A n E sc /\
        ms2 = MS (mkR ra (Z_to_bv 64 sp1) gp tp t0v t1v y7 s0v s1v (Z_to_bv 64 A) (Z_to_bv 64 n) a2v a3v a4v a5v a6v a7v
                      (Z_to_bv 64 (A + old)) s3v s4v s5v s6v s7 s8 s9 s10 s11 y28 y29 t5 t6) F (Z_to_bv 64 0x49d98) fc None m1 (seg_rom rsegs)))).
  { eapply evt_cut; [exact WALK|]. cbv beta. intros ms2 (y7 & y28 & y29 & ->).
    assert (EE : Bg + 16 + stride * (idx + 1) - 4 = E) by reflexivity.
    eapply dec_5b4; rewrite ?EE.
    - exact HN.
    - exact HO.
    - rewrite HE. clear - FITA. unfold IB in FITA. lia.
    - rewrite HE. pose_ceil. clear - SPc RCEIL RUP. lia.
    - exact Ap.
    - exact SCR.
    - exact SC63.
    -   intros y7' a5' y28' MC. apply evt_done. right. right. do 17 eexists. split; [exact MC| reflexivity].
    -   intros y7' a5' y28' T1 T2. apply evt_done. right. left. do 4 eexists. split; [exact T1|]. split; [exact T2| reflexivity].
    -
      intros y7' y28' T1 T2. eapply stc_5c4; rewrite ?EE.
      + exact HN.
      + exact SCR.
      + exact MI1.
      + intros. apply evt_done. right. right. do 17 eexists. split; [eassumption| reflexivity].
      + intros. apply evt_done. left. do 8 eexists. split; [eassumption|]. split; [eassumption|]. split; [eassumption| reflexivity].
      + exact T1.
      + exact T2. }
  cbv beta. intros ms2 HD.

  eapply (implM_bind rsegs _ _ _ (fun a sx ms1 => a = s /\ sx = s /\ ms1 = ms2)).
  { apply implM_get. apply evt_done. auto. }
  cbv beta. intros a sx ms1 (-> & -> & ->).
  unfold id in OLDB0.
  destruct HD as [(t1v & y7 & a2v & a4v & a5v & a7v & y28 & y29 & F1 & F2 & F3 & ->)|[(y7 & a5v & y28 & y29 & F1 & F2 & ->)|HD3]].
  -   eapply inpl_armB; eassumption.
  -   eapply (remap_arm_proof HMAL HFREE); try eassumption. exact I.
  -   destruct HD3 as (t0v & t1v & y7 & s0v & s1v & a2v & a3v & a4v & a5v & a6v & a7v & s3v & s4v & s5v & s6v & y28 & y29 & MC & ->).
    eapply move_armB; try eassumption. all: exact I.
Qed.
End TOP.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RF_malloc_spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem rrealloc_spec : rrealloc_stmt.
Proof. exact (rrealloc_spec_proof rmalloc_impl_spec rfree_impl_spec). Qed.

Theorem rrealloc_null_spec : rrealloc_null_stmt.
Proof. exact (rrealloc_null_spec_proof rmalloc_impl_spec). Qed.

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_free OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_fast OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_free OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_free_spec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_AB OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_A OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocBlocks OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocHINV OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_B OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Malloc_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocInv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Arith OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Inv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Kit OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Read OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Geom OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Pres2 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Cnt OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_WFree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_WGroup OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Realloc.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.ProgR OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Realloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Realloc2.
Import RMallocRep.TwinB RMallocTree.TwinB RMallocKit_A.TwinB RMallocKit_B.TwinB RMalloc_iface.TwinB RMalloc_ifaceP.TwinB RF_free_spec.TwinB RRealloc_iface.TwinB.
Import RF_realloc_hdr.TwinB RF_realloc_hdrS.TwinB RF_realloc_dec.TwinB RF_realloc_stc.TwinB RF_realloc_inplS.TwinB RF_realloc_moveS.TwinB RF_realloc_remapS.TwinB.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Section NULL.
Hypothesis HMAL : rmalloc_impl_stmt.
Theorem rrealloc_null_spec_proof : rrealloc_null_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
  intros HEAP AUXB SB ST CLO LO ERR MI TP HA0 HA1 HN. subst a0 a1. unfold RREALLOC_SYM. unfold RREALLOC_STACK in LO.

  eapply (implM_evt rsegs _ _ _ (fun ms1 => ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                  F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs))).
  { step. step. if_true. step. step. apply evt_done. reflexivity. }
  cbv beta. intros ms' ->. eapply HMAL; try eassumption; [lia| reflexivity].
Qed.
End NULL.

Section TOP.
Hypothesis HMAL : rmalloc_impl_stmt.
Hypothesis HFREE : rfree_impl_stmt.

Theorem rrealloc_spec_proof : rrealloc_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A old n lo B errv oldbs.
  intros HP Hin OLDB OLEN AUXB SB ST CLO LO ERR MI TP HA0 HA1 HN. subst a0 a1.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof CLO as CLOv. pose_ceil. pose proof LO as LOv. unfold RREALLOC_STACK, RMALLOC_STACK in LOv.
  assert (ETP : bv_unsigned tp + -164 = 429036) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  pose proof (RHEAP_block_range_proof s LB m _ HP Hin) as BR. cbn [blk_addr blk_size fst snd] in BR. destruct BR as (Ap & A16 & _ & ACE & AIMG).
  pose_ceil.
  destruct HP as (st & LB0 & PERM & Hst & RMR & [HBL AR]).
  assert (Hin0 : In (p, A, old) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (OLDB0 : id (bytes_at rsegs m A oldbs)) by exact OLDB.
  unfold RREALLOC_SYM. unfold implM. iprefix.

  step. step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. clear - K0 Ap. lia. } clear K0.

  carve_frame 64%nat ST.
  step. step. step. step. step. step. step. step. step.

  step. step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. clear - K1 HN. cbn in K1. lia. }
  clear K1. apply evt_done.
  lazymatch goal with |- impl _ _ _ _ (MS _ _ _ _ _ ?mX _) => rename mX into m1 end.
  set (sp1 := bv_unsigned sp + -64) in *.
  assert (RMR1 : rmrep st m1).
  { eapply rmrep_transport_unowned; [exact RMR| exact MU| exact WM|].
    intros lo' hi' a Hin' Ha RF. destruct (rrepfoot_where st m a RMR RF) as [AC _]. pose_ceil.
    destruct Hin' as [E'|[]]. inversion E'; subst lo' hi'. clear - Ha AC CLOv LOv. lia. }
  assert (PRES1 : rpres_except (fun a => (lo <= a < bv_unsigned sp) \/ (RERRNO <= a < RERRNO + 4)) m m1).
  { eapply rpres_except_of_munch'; [exact MU| exact WM|]. intros lo' hi' [E'|[]] x Hx. inversion E'; subst lo' hi'. left. clear - Hx LOv. lia. }
  assert (AUX1 : rauxv_ok m1 B).
  { eapply rauxv_ok_frame; [exact AUXB| exact MU| exact WM|]. constructor; [| constructor]. cbn [fst snd]. unfold RAUXV_CELL, RLIBC. clear - SB CLOv LOv. lia. }
  lazymatch goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
  clear MU WM.

  evar (a2w : word).
  destruct (hdr_spec ra (Z_to_bv 64 sp1) gp tp t0 t1 t2 s0 s1 a2w a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 st LB0 p old A n RMR1 MI1 AR Hin0 HN)
    as (g & bg & idx & r & SL & HM & Hr & Kr & FC & CC & CB & HO & FITA & SPc & RCEIL & SCR & SC63 & WALK).
  destruct (realloc_geo_facts ref_reserved st LB0 p A old AR Hin0 g bg idx SL HM)
    as (off & r' & Hoff & HA & FIT & _ & S16 & SMOD & SSTR & Hr' & _ & _ & Ec & B0 & BG16 & Hidx & LI31 & SPAN & _ & RB0 & K3).
  rewrite Hr in Hr'. assert (r' = r) as -> by congruence.
  cbv delta [MR] in S16, SMOD, SSTR, Ec, Hidx, LI31, SPAN, K3, FIT.
  set (mr := get_meta_rec st g) in *. set (stride := get_stride mr) in *.
  set (Bg := conc st bg) in *. set (E := Bg + 16 + stride * (idx + 1) - 4).
  set (sc := m_sizeclass mr) in *. set (mword := m_last_idx mr + 32 * m_freeable mr + 64 * sc + 4096 * m_maplen mr).
  assert (SK0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; clear - S16 Hidx; lia).
  assert (SK1 : stride * (idx + 1) = stride * idx + stride) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; reflexivity).
  assert (HE : E = conc st (fst p) + stride - 4) by (subst E; rewrite CC, SK1; fold Bg; clear; lia).
  pose proof (round_up_pg_ge (r_len r)) as RUP.

  eapply (impl_evt _ _ _ _ _ (fun ms2 : machine_state =>
     (exists t1v y7 a2v a4v a5v a7v y28 y29, n <= E - A /\ n < MMAP_THRESHOLD /\ sc <= size_to_class n + 1 /\
        ms2 = MS (mkR ra (Z_to_bv 64 sp1) gp tp (Z_to_bv 64 E) t1v y7 s0 (wz (conc st g)) (Z_to_bv 64 A) (Z_to_bv 64 n) a2v (Z_to_bv 64 sc) a4v a5v
                      (Z_to_bv 64 (E + 4)) a7v (Z_to_bv 64 (A + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6) F (Z_to_bv 64 0x4b5dc) fc None m1 (seg_rom rsegs))
     \/ (exists y7 a5v y28 y29, MMAP_THRESHOLD <= n /\ sc = 63 /\
        ms2 = MS (mkR ra (Z_to_bv 64 sp1) gp tp (Z_to_bv 64 E) (Z_to_bv 64 (Bg + stride * idx + 16)) y7 s0 (wz (conc st g)) (Z_to_bv 64 A) (Z_to_bv 64 n)
                      (wz Bg) (Z_to_bv 64 sc) (wz mword) a5v (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - A)) (Z_to_bv 64 (A + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
                 F (Z_to_bv 64 0x4b4b4) fc None m1 (seg_rom rsegs))
     \/ (exists t0v t1v y7 s0v s1v a2v a3v a4v a5v a6v a7v s3v s4v s5v s6v y28 y29, move_cond A n E sc /\
        ms2 = MS (mkR ra (Z_to_bv 64 sp1) gp tp t0v t1v y7 s0v s1v (Z_to_bv 64 A) (Z_to_bv 64 n) a2v a3v a4v a5v a6v a7v
                      (Z_to_bv 64 (A + old)) s3v s4v s5v s6v s7 s8 s9 s10 s11 y28 y29 t5 t6) F (Z_to_bv 64 0x4b59c) fc None m1 (seg_rom rsegs)))).
  { eapply evt_cut; [exact WALK|]. cbv beta. intros ms2 (y7 & y28 & y29 & ->).
    assert (EE : Bg + 16 + stride * (idx + 1) - 4 = E) by reflexivity.
    eapply dec_5b4; rewrite ?EE.
    - exact HN.
    - exact HO.
    - rewrite HE. clear - FITA. unfold IB in FITA. lia.
    - rewrite HE. pose_ceil. clear - SPc RCEIL RUP. lia.
    - exact Ap.
    - exact SCR.
    - exact SC63.
    -   intros y7' a5' y28' MC. apply evt_done. right. right. do 17 eexists. split; [exact MC| reflexivity].
    -   intros y7' a5' y28' T1 T2. apply evt_done. right. left. do 4 eexists. split; [exact T1|]. split; [exact T2| reflexivity].
    -
      intros y7' y28' T1 T2. eapply stc_5c4; rewrite ?EE.
      + exact HN.
      + exact SCR.
      + exact MI1.
      + intros. apply evt_done. right. right. do 17 eexists. split; [eassumption| reflexivity].
      + intros. apply evt_done. left. do 8 eexists. split; [eassumption|]. split; [eassumption|]. split; [eassumption| reflexivity].
      + exact T1.
      + exact T2. }
  cbv beta. intros ms2 HD.

  eapply (implM_bind rsegs _ _ _ (fun a sx ms1 => a = s /\ sx = s /\ ms1 = ms2)).
  { apply implM_get. apply evt_done. auto. }
  cbv beta. intros a sx ms1 (-> & -> & ->).
  unfold id in OLDB0.
  destruct HD as [(t1v & y7 & a2v & a4v & a5v & a7v & y28 & y29 & F1 & F2 & F3 & ->)|[(y7 & a5v & y28 & y29 & F1 & F2 & ->)|HD3]].
  -   eapply inpl_armB; eassumption.
  -   eapply (remap_arm_proof HMAL HFREE); try eassumption. exact I.
  -   destruct HD3 as (t0v & t1v & y7 & s0v & s1v & a2v & a3v & a4v & a5v & a6v & a7v & s3v & s4v & s5v & s6v & y28 & y29 & MC & ->).
    eapply move_armB; try eassumption. all: exact I.
Qed.
End TOP.

Import RF_malloc_spec.TwinB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem rrealloc_spec : rrealloc_stmt.
Proof. exact (rrealloc_spec_proof rmalloc_impl_spec rfree_impl_spec). Qed.

Theorem rrealloc_null_spec : rrealloc_null_stmt.
Proof. exact (rrealloc_null_spec_proof rmalloc_impl_spec). Qed.

End CEIL.
End TwinB.
