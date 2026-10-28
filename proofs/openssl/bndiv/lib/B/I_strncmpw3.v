(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_small R_m2s R_thread I_consts I_qck X_atexit. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import IcptSpec. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import I_pck D_kit I_ikit I_strncmpw I_strncmpw2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma cmpx_b2z : forall x1 x2, Z.b2z (x2 <? x1) - Z.b2z (x1 <? x2) = cmpx x1 x2.
Proof. intros x1 x2. unfold cmpx. destruct (x1 <? x2) eqn:E1, (x2 <? x1) eqn:E2; cbn; lia. Qed.

Definition istrncmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - ISTRNCMP_DEPTH, bv_unsigned sp)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Lemma isc_prologue : forall (sp p1 p2 n : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk bsegs m lo sp -> lo <= sp - ISTRNCMP_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (m' : mem) (junk : list byte),
      ms' = MS (mkR ra (Z_to_bv 64 (sp + -2176)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 n)
                    (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 n) a3 a4 a5 a6 a7 (Z_to_bv 64 p2) (Z_to_bv 64 p1) ra
                    s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1a80dc) fc None m' (seg_rom bsegs)
      /\ munch [(sp - 2176, sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells bsegs m' (sp + -2176) [CB 2072 junk]
      /\ stk bsegs m' lo (sp + -2176))
    (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a808c) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2176, sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  carve_frame 104%nat ST. rename FR into FRs. carve_frame 2072%nat ST.
  do 20 lstep.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRs|]. split; [exact FR| exact ST].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Lemma isc_tail2 : forall (usp p2 sz x1 x2 : Z)
    (ra ra' gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s0' s1' s3' s4' s6' s7' s10' s11' : word) F fc (m0 m : mem) (lo : Z) (junk : list byte),
  stk bsegs m lo (usp + -2176) -> lo <= usp - ISTRNCMP_DEPTH -> kHighShadowEnd + 8 <= lo -> usp < 2^63 ->
  rw_cells bsegs m (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m (usp + -2176) [CB 2072 junk] ->
  munch [(usp - 2256, usp)] m0 m -> wmono bsegs m0 m ->
  0 <= p2 -> 1 <= sz -> p2 + sz <= 2^47 -> 0 <= x1 < 256 -> 0 <= x2 < 256 ->
  chk_ok m p2 sz -> m2s_cells m -> icells_sc m -> mem_inv bsegs m ->
  evt bsegs (istrncmp_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (cmpx x1 x2) lo m0)
    (MS (mkR ra' (Z_to_bv 64 (usp + -2176)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p2) s3' s4' (Z_to_bv 64 sz) s6' s7' (Z_to_bv 64 x1) (Z_to_bv 64 x2) s10' s11' t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a8294) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until junk. intros ST LO LOLO SPH FRs FR MU WM P0 SZ0 R2 X1 X2 CS2 M2S IC MI.
  unfold kHighShadowEnd in *.
  call (isc_chk2 RIP usp p2 sz); [exact ST| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact CS2| exact M2S| exact IC
        | assumption|].
  lazymatch goal with H : stk bsegs _ lo (usp + -2176) |- _ => rename H into ST3 end.
  do 3 lstep.
  rewrite cmpx_b2z.
  do 23 lstep.
  release_frame FR ST3 (usp + -104). release_frame FRs ST3 usp.
  lstep.
  unfold istrncmp_post. sys_finish.
  + rewrite (unsigned_lit usp) by lia. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
  + rewrite (unsigned_lit usp) by lia. assumption.
Qed.


(* [comment removed for export] *)
End WithRIP.
