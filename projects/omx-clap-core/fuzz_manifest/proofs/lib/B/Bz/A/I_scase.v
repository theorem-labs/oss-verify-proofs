(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bndiv/lib/A/I_strncmp.v, with its module paths, addresses and numbers changed; 182 of its 307 lines of code are new or changed and 65 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/Bz/A/I_scase.v: ported from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/B/Bz/A/I_scase.v, which equals the A->B relocation (Theorem Labs tools) of lib/A/Bz/A/I_scase.v at a working branch 5d8d8a15571 modulo module paths; module paths for this tree. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck X_atexit IcptSpec D_kit
  I_ikit I_strncmpw I_strncmpw3 I_strncmp I_scasem I_scasew.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma cc_trunc : forall n b1 b2, 0 < n -> scase_ok n b1 b2 ->
  let j := Z.to_nat (scase_sz n b1 b2) in
  scase_idx n (firstn j b1) (firstn j b2) = scase_idx n b1 b2
  /\ scase_res n (firstn j b1) (firstn j b2) = scase_res n b1 b2
  /\ scase_sz n (firstn j b1) (firstn j b2) = scase_sz n b1 b2
  /\ scase_ok n (firstn j b1) (firstn j b2)
  /\ length (firstn j b1) = j /\ length (firstn j b2) = j.
Proof.
  intros n b1 b2 N0 (L1 & L2) j.
  pose proof (cc_idx_le (Z.to_nat n) b1 b2) as LE.
  assert (HJ : (scase_idx_aux b1 b2 (Z.to_nat n) < j \/ Z.to_nat n <= j)%nat).
  { unfold j, scase_sz, scase_idx. destruct (Nat.eq_dec (scase_idx_aux b1 b2 (Z.to_nat n)) (Z.to_nat n)) as [E|NE].
    - right. rewrite E. lia.
    - left. lia. }
  assert (EI : scase_idx n (firstn j b1) (firstn j b2) = scase_idx n b1 b2).
  { unfold scase_idx. rewrite (cc_idx_firstn _ b1 b2 j HJ). reflexivity. }
  assert (ES : scase_sz n (firstn j b1) (firstn j b2) = scase_sz n b1 b2) by (unfold scase_sz; rewrite EI; reflexivity).
  assert (LJ1 : length (firstn j b1) = j) by (rewrite firstn_length; unfold j; lia).
  assert (LJ2 : length (firstn j b2) = j) by (rewrite firstn_length; unfold j; lia).
  split; [exact EI|]. split.
  - unfold scase_res. rewrite EI. destruct (scase_idx n b1 b2 =? n) eqn:EN; [reflexivity|].
    apply Z.eqb_neq in EN. unfold scase_idx in EN |- *.
    rewrite !nth_error_firstn_lt by (rewrite Nat2Z.id; destruct HJ as [HJ|HJ]; [exact HJ| lia]). reflexivity.
  - split; [exact ES|]. split; [unfold scase_ok; rewrite ES, LJ1, LJ2; unfold j; split; lia|]. split; [exact LJ1| exact LJ2].
Qed.

Lemma iscc_prologue : forall (sp p1 p2 n : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo sp -> lo <= sp - ISTRNCMP_DEPTH -> kHighShadowEnd < lo -> sp < 2^63 -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (junk : list byte),
      ms' = MS (mkR ra (Z_to_bv 64 (sp + -2176)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 n)
                    (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 n) a3 a4 a5 a6 a7 (Z_to_bv 64 p2) (Z_to_bv 64 p1) ra
                    s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x42450) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2176, sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m' (sp + -2176) [CB 2072 junk]
      /\ stk asegs m' lo (sp + -2176))
    (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x42400) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2176, sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  carve_frame 104%nat ST. rename FR into FRs. carve_frame 2072%nat ST.
  do 20 lstep.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRs|]. split; [exact FR| exact ST].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Lemma iscc_tail2 : forall (usp p2 sz x1 x2 : Z)
    (ra ra' gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s0' s1' s3' s4' s6' s7' s10' s11' : word) F fc (m0 m : mem) (lo : Z) (junk : list byte),
  stk asegs m lo (usp + -2176) -> lo <= usp - ISTRNCMP_DEPTH -> kHighShadowEnd < lo -> usp < 2^63 ->
  rw_cells asegs m (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (usp + -2176) [CB 2072 junk] ->
  munch [(usp - 2256, usp)] m0 m -> wmono asegs m0 m ->
  0 <= p2 -> 1 <= sz -> p2 + sz <= 2^47 -> 0 <= x1 < 256 -> 0 <= x2 < 256 ->
  chk_ok m p2 sz -> m2s_cells m -> icells_sc m -> mem_inv asegs m ->
  evt asegs (istrncmp_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (zlw x1 - zlw x2) lo m0)
    (MS (mkR ra' (Z_to_bv 64 (usp + -2176)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p2) s3' s4' (Z_to_bv 64 sz) s6' s7' (Z_to_bv 64 x2) (Z_to_bv 64 x1) s10' s11' t3 t4 t5 t6)
        F (Z_to_bv 64 0x425d0) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until junk. intros ST LO LOLO SPH FRs FR MU WM P0 SZ0 R2 X1 X2 CS2 M2S IC MI.
  unfold kHighShadowEnd in *.
  assert (EUx1 : bv_unsigned (Z_to_bv 64 x1) = x1) by (apply unsigned_lit; lia).
  assert (EUx2 : bv_unsigned (Z_to_bv 64 x2) = x2) by (apply unsigned_lit; lia).
  call (iscc_chk2 RIP usp p2 sz); [exact ST| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact CS2| exact M2S| exact IC
        | assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2176) |- _ => rename H into ST3 end.
  do 9 lstep.
  rewrite (lw_expr x1 X1), (lw_expr x2 X2).
  pose proof (zlw_range x1 X1) as LX1. pose proof (zlw_range x2 X2) as LX2.
  rewrite ?(Z.mod_small (zlw x1) 18446744073709551616), ?(Z.mod_small (zlw x2) 18446744073709551616) by lia.
  do 23 lstep.
  release_frame FR ST3 (usp + -104). release_frame FRs ST3 usp.
  lstep.
  rewrite ?(Z.mod_small (zlw x1) 18446744073709551616), ?(Z.mod_small (zlw x2) 18446744073709551616) by lia.
  unfold istrncmp_post. sys_finish.
  + rewrite (unsigned_lit usp) by lia. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
  + rewrite (unsigned_lit usp) by lia. assumption.
Qed.

Lemma iscc_tail : forall (usp p1 p2 n sz idx x1 x2 : Z)
    (ra ra' gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s0' s4' s6' s7' s10' : word) F fc (m0 m : mem) (lo : Z) (junk : list byte),
  stk asegs m lo (usp + -2176) -> lo <= usp - ISTRNCMP_DEPTH -> kHighShadowEnd < lo -> usp < 2^63 ->
  rw_cells asegs m (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (usp + -2176) [CB 2072 junk] ->
  munch [(usp - 2256, usp)] m0 m -> wmono asegs m0 m ->
  0 <= p1 -> 0 <= p2 -> 0 <= idx <= n -> n < 2^64 -> sz = Z.min (idx + 1) n -> 1 <= sz ->
  p1 + sz <= 2^47 -> p2 + sz <= 2^47 -> 0 <= x1 < 256 -> 0 <= x2 < 256 ->
  chk_ok m p1 sz -> chk_ok m p2 sz -> m2s_cells m -> icells_sc m -> mem_inv asegs m ->
  evt asegs (istrncmp_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (zlw x1 - zlw x2) lo m0)
    (MS (mkR ra' (Z_to_bv 64 (usp + -2176)) gp tp t0 t1 t2 s0' (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p2) (Z_to_bv 64 p1) s4' (Z_to_bv 64 sz) s6' s7' (Z_to_bv 64 x2) (Z_to_bv 64 x1) s10' (Z_to_bv 64 idx)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x42578) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until junk. intros ST LO LOLO SPH FRs FR MU WM P1 P2 IDX NH SZD SZ0 R1 R2 X1 X2 CS1 CS2 M2S IC MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(usp - 2256, usp)] m) as MUl. pose proof (wmono_refl asegs m) as WMl.
  pose proof IC as (G70 & G2 & SHC & AI & SSC).
  call (iscc_chk1 RIP usp p1 sz); [exact ST| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact CS1| exact M2S| exact IC
        | assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2176) |- _ => rename H into ST2 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CS2' : chk_ok mm p2 sz)
      by (apply (chk_ok_agree m mm p2 sz CS2 ltac:(lia) ltac:(lia));
          apply (agree_of_munch _ _ _ _ MUl); intros y Hy; cbn [outside]; split; [lia| exact I]);
    assert (M2S' : m2s_cells mm)
      by (apply (m2s_cells_agree m mm M2S); [apply (agree_of_munch _ _ _ _ MUl); intros y Hy; cbn [outside]; split; [lia| exact I]
                                           | exact WMl]);
    assert (IC' : icells_sc mm) by (split; [exact G70| split; [exact G2| split; [exact SHC| split; [exact AI| exact SSC]]]])
  end.
  clear CS1 CS2 M2S IC.
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (EUi1 : bv_unsigned (Z_to_bv 64 (idx + 1)) = idx + 1) by (apply unsigned_lit; lia).
  assert (EUp2 : bv_unsigned (Z_to_bv 64 p2) = p2) by (apply unsigned_lit; lia).
  assert (EUnp2 : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p2)) = 18446744073709551615 - p2) by (apply unsigned_lit; lia).
  lstep. lstep. if_cases K; zify_cond K.
  - lstep. lstep. rewrite (lxor_ones64 p2) by lia. lstep. if_true.
    replace (Z_to_bv 64 n) with (Z_to_bv 64 sz) by (f_equal; lia).
    eapply iscc_tail2; try eassumption; lia.
  - lstep. rewrite (lxor_ones64 p2) by lia. lstep. if_false.
    replace (Z_to_bv 64 (idx + 1)) with (Z_to_bv 64 sz) by (f_equal; lia).
    eapply iscc_tail2; try eassumption; lia.
Qed.

Theorem istrncasecmp_pos : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p1 p2 n : Z) (b1 b2 : list byte) (lo : Z),
  a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 -> a2 = Z_to_bv 64 n ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRNCMP_DEPTH -> kHighShadowEnd < lo -> bv_unsigned sp < 2^63 ->
  0 < n < 2^64 -> bytes_at asegs m p1 b1 -> bytes_at asegs m p2 b2 -> scase_ok n b1 b2 ->
  p1 + scase_sz n b1 b2 <= 2^47 -> p2 + scase_sz n b1 b2 <= 2^47 ->
  (p1 + scase_sz n b1 b2 <= bv_unsigned sp - ISTRNCMP_DEPTH \/ bv_unsigned sp <= p1) ->
  (p2 + scase_sz n b1 b2 <= bv_unsigned sp - ISTRNCMP_DEPTH \/ bv_unsigned sp <= p2) ->
  chk_ok m p1 (scase_sz n b1 b2) -> chk_ok m p2 (scase_sz n b1 b2) -> m2s_cells m -> icells_sc m -> mem_inv asegs m ->
  evt asegs (istrncmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (scase_res n b1 b2) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x42400) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros -> -> -> ST LO LOLO SPH N0 B1 B2 OK R1 R2 SEP1 SEP2 CS1 CS2 M2S IC MI.
  unfold kHighShadowEnd in *.
  destruct (cc_trunc n b1 b2 ltac:(lia) OK) as (EI & ER & ES & OKc & LC1 & LC2).
  rewrite <- ER.
  set (sz := scase_sz n b1 b2) in *.
  set (c1 := firstn (Z.to_nat sz) b1) in *. set (c2 := firstn (Z.to_nat sz) b2) in *.
  assert (BC1 : keep (bytes_at asegs m p1 c1)) by (apply bytes_at_firstn_a; exact B1).
  assert (BC2 : keep (bytes_at asegs m p2 c2)) by (apply bytes_at_firstn_a; exact B2).
  pose proof (bytes_at_bound _ _ _ _ B1) as BB1. pose proof (bytes_at_bound _ _ _ _ B2) as BB2.
  clear B1 B2 EI ER OK. clearbody c1 c2.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - 2256, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2176 : bv_unsigned (Z_to_bv 64 (usp + -2176)) = usp + -2176) by (apply unsigned_lit; lia).
  call (iscc_prologue usp p1 p2 n); [exact ST| lia| unfold kHighShadowEnd; lia| lia| exact MI|].
  rename PC into FRs. rename PC0 into FR. rename POST into ST.
  lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (IC1 : icells_sc mm)
      by (apply (icells_sc_agree m mm IC); [apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]
                                          | exact WM]) end.
  pose proof IC1 as (G70 & G2 & SHC & AI & SSC). clear IC1.
  call try_init_spec; [exact AI| rewrite EU2176; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2176 in H; rename H into ST2 end.
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  xsteps_to 0x42460%Z.
  assert (SZ1 : 1 <= sz <= n).
  { rewrite <- ES. unfold scase_sz, scase_idx. lia. }
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
    assert (IC' : icells_sc mm) by (split; [exact G70| split; [exact G2| split; [exact SHC| split; [exact AI| exact SSC]]]])
  end.
  clear BC1 BC2 CS1 CS2 M2S IC.
  eapply evt_cut.
  { apply (iscc_cmp_loop (Z.to_nat n - 1) 0 n p1 p2 c1 c2); [lia| lia| exact BM1| exact BM2| exact OKc| intros j Hj; lia| assumption]. }
  intros ms' (a0' & a1' & y1 & y2 & -> & X1R & X2R & RES).
  rewrite <- RES.
  set (idx := scase_idx n c1 c2) in *.
  assert (IDX : 0 <= idx <= n) by (unfold idx, scase_idx; pose proof (cc_idx_le (Z.to_nat n) c1 c2); lia).
  assert (SZD : sz = Z.min (idx + 1) n) by (rewrite <- ES; reflexivity).
  assert (EUi : bv_unsigned (Z_to_bv 64 idx) = idx) by (apply unsigned_lit; lia).
  assert (EUi1 : bv_unsigned (Z_to_bv 64 (idx + 1)) = idx + 1) by (apply unsigned_lit; lia).
  assert (EUp1 : bv_unsigned (Z_to_bv 64 p1) = p1) by (apply unsigned_lit; lia).
  assert (EUnp1 : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p1)) = 18446744073709551615 - p1) by (apply unsigned_lit; lia).
  lstep. if_cases K; zify_cond K.
  - lstep. lstep. if_false.
    lstep. lstep. rewrite (lxor_ones64 p1) by lia. lstep. lstep. lstep. if_true.
    replace (Z_to_bv 64 n) with (Z_to_bv 64 sz) by (f_equal; lia).
    eapply iscc_tail; try eassumption; lia.
  - do 6 lstep. if_true. lstep. lstep. if_cases K2; zify_cond K2.
    + lstep. lstep. rewrite (lxor_ones64 p1) by lia. lstep. lstep. lstep. if_true.
      replace (Z_to_bv 64 n) with (Z_to_bv 64 sz) by (f_equal; lia).
      eapply iscc_tail; try eassumption; lia.
    + lstep. rewrite (lxor_ones64 p1) by lia. lstep. lstep. lstep. if_false.
      replace (Z_to_bv 64 (idx + 1)) with (Z_to_bv 64 sz) by (f_equal; lia).
      eapply iscc_tail; try eassumption; lia.
Qed.

Lemma iscc_zero : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p1 p2 : Z) (lo : Z),
  a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 -> a2 = Z_to_bv 64 0 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRNCMP_DEPTH -> kHighShadowEnd < lo -> bv_unsigned sp < 2^63 ->
  0 <= p1 < 2^64 -> 0 <= p2 < 2^64 -> icells_sc m -> mem_inv asegs m ->
  evt asegs (istrncmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x42400) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros -> -> -> ST LO LOLO SPH P1 P2 IC MI.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - 2256, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2176 : bv_unsigned (Z_to_bv 64 (usp + -2176)) = usp + -2176) by (apply unsigned_lit; lia).
  assert (EUp1 : bv_unsigned (Z_to_bv 64 p1) = p1) by (apply unsigned_lit; lia).
  assert (EUp2 : bv_unsigned (Z_to_bv 64 p2) = p2) by (apply unsigned_lit; lia).
  assert (EUnp1 : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p1)) = 18446744073709551615 - p1) by (apply unsigned_lit; lia).
  assert (EUnp2 : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p2)) = 18446744073709551615 - p2) by (apply unsigned_lit; lia).
  call (iscc_prologue usp p1 p2 0); [exact ST| lia| unfold kHighShadowEnd; lia| lia| exact MI|].
  rename PC into FRs. rename PC0 into FR. rename POST into ST.
  lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (IC1 : icells_sc mm)
      by (apply (icells_sc_agree m mm IC); [apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]
                                          | exact WM]) end.
  pose proof IC1 as (G70 & G2 & SHC & AI & SSC). clear IC1.
  call try_init_spec; [exact AI| rewrite EU2176; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2176 in H; rename H into ST2 end.
  lstep. if_false. lstep. if_true.
  do 4 lstep.
  lstep. lstep. if_true.
  lstep. lstep. rewrite (lxor_ones64 p1) by lia. lstep. lstep. lstep. if_true.
  lstep. lstep. lstep. if_true.
  lstep. if_false. lstep.
  lstep. lstep. if_true.
  lstep. lstep. rewrite (lxor_ones64 p2) by lia. lstep. if_true.
  lstep. lstep. lstep. if_true.
  lstep. if_false. lstep.
  do 9 lstep.
  do 23 lstep.
  release_frame FR ST2 (usp + -104). release_frame FRs ST2 usp.
  lstep.
  unfold istrncmp_post. sys_finish.
  + rewrite (unsigned_lit usp) by lia. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
  + rewrite (unsigned_lit usp) by lia. assumption.
Qed.

Theorem istrncasecmp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p1 p2 n : Z) (b1 b2 : list byte) (lo : Z),
  a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 -> a2 = Z_to_bv 64 n ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRNCMP_DEPTH -> kHighShadowEnd < lo -> bv_unsigned sp < 2^63 ->
  0 <= n < 2^64 -> bytes_at asegs m p1 b1 -> bytes_at asegs m p2 b2 -> scase_ok n b1 b2 ->
  p1 + scase_sz n b1 b2 <= 2^47 -> p2 + scase_sz n b1 b2 <= 2^47 ->
  (p1 + scase_sz n b1 b2 <= bv_unsigned sp - ISTRNCMP_DEPTH \/ bv_unsigned sp <= p1) ->
  (p2 + scase_sz n b1 b2 <= bv_unsigned sp - ISTRNCMP_DEPTH \/ bv_unsigned sp <= p2) ->
  chk_ok m p1 (scase_sz n b1 b2) -> chk_ok m p2 (scase_sz n b1 b2) -> m2s_cells m -> icells_sc m -> mem_inv asegs m ->
  evt asegs (istrncmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (scase_res n b1 b2) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x42400) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros E0 E1 E2 ST LO LOLO SPH N0 B1 B2 OK R1 R2 SEP1 SEP2 CS1 CS2 M2S IC MI.
  destruct (Z.eq_dec n 0) as [Z0|NZ].
  - subst n.
    assert (EI0 : scase_idx 0 b1 b2 = 0) by reflexivity.
    assert (ER0 : scase_res 0 b1 b2 = 0) by (unfold scase_res; rewrite EI0; reflexivity).
    assert (SZ0 : scase_sz 0 b1 b2 = 0) by (unfold scase_sz; rewrite EI0; reflexivity).
    rewrite ER0.
    pose proof (bytes_at_bound _ _ _ _ B1) as BB1. pose proof (bytes_at_bound _ _ _ _ B2) as BB2.
    apply (iscc_zero ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p1 p2 lo);
      try assumption; lia.
  - apply (istrncasecmp_pos ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             p1 p2 n b1 b2 lo); try assumption; lia.
Qed.

End WithRIP.
