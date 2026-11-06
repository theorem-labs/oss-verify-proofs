(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Theorem Labs, 2026-10-28: copied from proofs/leptonica/fhmtgen_fuzzer/lib/K5/B10/I_strcmp.v at origin/ossv/recipes c8557374ad2e, with its module paths changed to fuzz_preset's. Its address literals are still fhmtgen_fuzzer.asan-ubsan's. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib Require Import SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10 Require Import R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit I_strcmp_spec I_strcmpw I_strcmpw2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma cmpx_b2z : forall x1 x2, Z.b2z (x2 <? x1) - Z.b2z (x1 <? x2) = cmpx x1 x2.
Proof. intros x1 x2. unfold cmpx. destruct (x1 <? x2) eqn:E1, (x2 <? x1) eqn:E2; cbn; lia. Qed.

Definition istrcmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - ISTRCMP_DEPTH, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Lemma iscmp_prologue : forall (sp p1 p2 : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo sp -> lo <= sp - ISTRCMP_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (junk : list byte),
      ms' = MS (mkR ra (Z_to_bv 64 (sp + -2192)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 p2)
                    (Z_to_bv 64 p1) (Z_to_bv 64 p2) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p1) ra s4
                    s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x4340c) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2192, sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m' (sp + -2192) [CB 2088 junk]
      /\ stk asegs m' lo (sp + -2192))
    (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p1) (Z_to_bv 64 p2) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x433c0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2192, sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  carve_frame 104%nat ST. rename FR into FRs. carve_frame 2088%nat ST.
  do 19 lstep.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRs|]. split; [exact FR| exact ST].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Theorem istrcmp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p1 p2 : Z) (b1 b2 : list byte) (lo : Z),
  a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRCMP_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
  Z.of_nat (length b1) < 2^40 -> Z.of_nat (length b2) < 2^40 ->
  bytes_at asegs m p1 b1 -> bytes_at asegs m p2 b2 -> strcmp_ok b1 b2 ->
  p1 + strcmp_sz b1 b2 <= 2^47 -> p2 + strcmp_sz b1 b2 <= 2^47 ->
  (p1 + strcmp_sz b1 b2 <= lo \/ bv_unsigned sp <= p1) -> (p2 + strcmp_sz b1 b2 <= lo \/ bv_unsigned sp <= p2) ->
  chk_ok m p1 (strcmp_sz b1 b2) -> chk_ok m p2 (strcmp_sz b1 b2) -> m2s_cells m -> icells_scmp m -> mem_inv asegs m ->
  evt asegs (istrcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (strcmp_res b1 b2) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x433c0) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros -> -> ST LO LOLO SPH L1 L2 B1 B2 OK R1 R2 SEP1 SEP2 CS1 CS2 M2S IC MI.
  unfold kHighShadowEnd in *.
  destruct (sc_trunc b1 b2 OK) as (EI & ER & ES & OKc & LC1 & LC2).
  rewrite <- ER.
  set (sz := strcmp_sz b1 b2) in *.
  set (c1 := firstn (Z.to_nat sz) b1) in *. set (c2 := firstn (Z.to_nat sz) b2) in *.
  assert (SZ1 : 1 <= sz) by (unfold sz, strcmp_sz, strcmp_idx; lia).
  assert (SZL : sz < 2^40) by (destruct OK as [OK1 _]; fold sz in OK1; lia).
  assert (BC1 : keep (bytes_at asegs m p1 c1)).
  { unfold keep, c1. rewrite <- (firstn_skipn (Z.to_nat sz) b1) in B1. apply bytes_at_app in B1. exact (proj1 B1). }
  assert (BC2 : keep (bytes_at asegs m p2 c2)).
  { unfold keep, c2. rewrite <- (firstn_skipn (Z.to_nat sz) b2) in B2. apply bytes_at_app in B2. exact (proj1 B2). }
  pose proof (bytes_at_bound _ _ _ _ B1) as BB1. pose proof (bytes_at_bound _ _ _ _ B2) as BB2.
  clear B1 B2 EI ER OK. clearbody c1 c2.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - ISTRCMP_DEPTH, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2192 : bv_unsigned (Z_to_bv 64 (usp + -2192)) = usp + -2192) by (apply unsigned_lit; lia).
  call (iscmp_prologue usp p1 p2); [exact ST| lia| unfold kHighShadowEnd; lia| lia| exact MI|].
  rename PC into FRs. rename PC0 into FR. rename POST into ST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (IC1 : icells_scmp mm)
      by (apply (icells_scmp_agree m mm IC); [apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]
                                            | exact WM]) end.
  pose proof IC1 as (G70 & G2 & SHC & AI & SSC & ISC). clear IC1.
  lstep.
  call try_init_spec; [exact AI| rewrite EU2192; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2192 in H; rename H into ST2 end.
  xsteps_to 0x43420%Z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BM1 : bytes_at asegs mm p1 c1)
      by (unfold keep in BC1; apply (bytes_at_agree asegs m mm _ _ BC1); apply (agree_of_munch _ _ _ _ MU); intros y Hy;
          cbn [outside]; rewrite LC1, Z2Nat.id in Hy by lia; (split; [lia| exact I]));
    assert (BM2 : bytes_at asegs mm p2 c2)
      by (unfold keep in BC2; apply (bytes_at_agree asegs m mm _ _ BC2); apply (agree_of_munch _ _ _ _ MU); intros y Hy;
          cbn [outside]; rewrite LC2, Z2Nat.id in Hy by lia; (split; [lia| exact I]));
    assert (CM1 : chk_ok mm p1 sz)
      by (apply (chk_ok_agree m mm p1 sz CS1 ltac:(lia) ltac:(lia));
          apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]);
    assert (CM2 : chk_ok mm p2 sz)
      by (apply (chk_ok_agree m mm p2 sz CS2 ltac:(lia) ltac:(lia));
          apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]);
    assert (M2S' : m2s_cells mm)
      by (apply (m2s_cells_agree m mm M2S); [apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]
                                           | exact WM]);
    assert (IC' : icells_scmp mm) by (split; [exact G70| split; [exact G2| split; [exact SHC| split; [exact AI| split; [exact SSC| exact ISC]]]]])
  end.
  clear BC1 BC2 CS1 CS2 M2S IC.
  eapply evt_cut.
  { apply (iscmp_loop (strcmp_idx_aux c1 c2) 0 p1 p2 c1 c2); [lia| lia| lia| exact BM1| exact BM2| exact OKc| intros j Hj; lia| assumption]. }
  intros ms' (c1x & c2x & -> & X1R & X2R & RES).
  rewrite <- RES.
  replace (strcmp_idx c1 c2 + 1) with sz by (rewrite <- ES; reflexivity).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(usp - ISTRCMP_DEPTH, usp)] mm) as MUl; pose proof (wmono_refl asegs mm) as WMl end.
  call (iscmp_chk1 RIP usp p1 p2 sz); [exact ST2| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact CM1| exact M2S'| exact IC'
        | assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2192) |- _ => rename H into ST3 end.
  lazymatch goal with MUx : munch _ ?m1 ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of CM2 with chk_ok m1 _ _ =>
    assert (CM2' : chk_ok mm p2 sz)
      by (apply (chk_ok_agree m1 mm p2 sz CM2 ltac:(lia) ltac:(lia));
          apply (agree_of_munch _ _ _ _ MUx); intros y Hy; cbn [outside]; split; [lia| exact I]);
    assert (M2S'' : m2s_cells mm)
      by (apply (m2s_cells_agree m1 mm M2S'); [apply (agree_of_munch _ _ _ _ MUx); intros y Hy; cbn [outside]; split; [lia| exact I]
                                              | assumption]);
    assert (IC'' : icells_scmp mm)
      by (apply (icells_scmp_agree m1 mm IC'); [apply (agree_of_munch _ _ _ _ MUx); intros y Hy; cbn [outside]; split; [lia| exact I]
                                              | assumption])
    end end.
  call (iscmp_chk2 RIP usp p1 p2 sz); [exact ST3| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact CM2'| exact M2S''| exact IC''
        | assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2192) |- _ => rename H into ST4 end.
  assert (EUx1 : bv_unsigned (Z_to_bv 64 c1x) = c1x) by (apply unsigned_lit; lia).
  assert (EUx2 : bv_unsigned (Z_to_bv 64 c2x) = c2x) by (apply unsigned_lit; lia).
  do 3 lstep.
  rewrite cmpx_b2z.
  do 22 lstep.
  release_frame FR ST4 (usp + -104). release_frame FRs ST4 usp.
  lstep.
  unfold istrcmp_post. sys_finish.
  + rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
  + rewrite EU. assumption.
Qed.

End WithRIP.
