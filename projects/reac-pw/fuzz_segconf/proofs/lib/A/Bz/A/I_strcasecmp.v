(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bndiv/lib/A/I_strncmp.v, with its module paths and addresses changed; 130 of its 221 lines of code are new or changed and 99 lines of the source are left out. *)
(* reac-pw/fuzz_segconf image A (fuzz_segconf.asan, sha256 48c5355bdacb...): the strcasecmp wrapper
   ___interceptor_strcasecmp (0x44af8, 0x500 bytes) from its entry to its return, and the trampoline
   __interceptor_trampoline_strcasecmp (0x43a1c, `j 0x44af8`). Written for this unit on fuzz_command's kit
   (lib/A/Bz/A/I_strncmp*.v); the shape is fuzz_manifest's strncasecmp walk (lib/A/Bz/A/I_scase.v at
   origin/ossv/recipes 501c0d516c69) without the length bound.

   The path:
   - 0x44af8-0x44b40: the frame (2176 bytes; ra, s0-s11 saved at sp - 104 .. sp - 8), s2 := x, s1 := y, s3 := ra;
   - 0x44b44 jal 0x5dd7c (TryAsanInitFromRtl, I_ikit.try_init_spec): it answers 1 when the asan-inited byte 0xaccd8
     is 1 (I_strncmpw.icells_sc), so 0x44b48 `beqz a0, 0x44ca4` is not taken. The other arm (0x44ca4: restore the
     frame and jump through real_strcasecmp 0xa4768 to musl strcasecmp 0x9a920) is never reached here;
   - 0x44b58-0x44b94: the comparison loop (I_strcasecmpm.v);
   - 0x44b98-0x44bb8: s11 := the flags pointer (0xa2a40 -> 0x13db28), the strict-string flag 0x13dc1d is 0 (so the
     strlen arms 0x44cf4 / 0x44d7c are not taken), no address overflow (so 0x44d08 / 0x44d94 are not taken);
   - the two range checks (I_strcasecmpw.v), each over sz = i + 1 bytes;
   - 0x44c4c-0x44ca0: the hook __sanitizer_weak_hook_strcasecmp (0x44af4, `ret`), a0 := the answer, the frame
     restored, ret. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck
  X_atexit IcptSpec D_kit I_ikit I_strncmpw I_strncmpw3 I_strncmp I_strcasecmpm I_strcasecmpw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* __interceptor_trampoline_strcasecmp: 0x43a1c `j 0x44af8` (the statement of the kit's I_tramp.tramp_step 0x43a1c
   0x44af8, written out) *)
Lemma tramp_strcasecmp :
  forall (Q : machine_state -> Prop) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x44af8) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x43a1c) fc None m (seg_rom asegs)).
Proof. intros. lstep. assumption. Qed.

(* ---- the strings, cut to the bytes the wrapper reads ---- *)

Lemma scc_idx_firstn : forall b1 b2 j, (scc_idx b1 b2 < j)%nat ->
  scc_idx (firstn j b1) (firstn j b2) = scc_idx b1 b2.
Proof.
  induction b1 as [|x b1 IH]; intros b2 j HJ; [rewrite firstn_nil; reflexivity|].
  destruct j as [|j]; [lia|].
  destruct b2 as [|y b2]; [rewrite firstn_nil; cbn [firstn scc_idx]; reflexivity|].
  cbn [firstn scc_idx]. cbn [scc_idx] in HJ.
  destruct (_ || _); [reflexivity|]. f_equal. apply IH. lia.
Qed.

Lemma scc_trunc : forall b1 b2, scc_ok b1 b2 ->
  let j := Z.to_nat (scc_sz b1 b2) in
  scc_idx (firstn j b1) (firstn j b2) = scc_idx b1 b2
  /\ scc_res (firstn j b1) (firstn j b2) = scc_res b1 b2
  /\ scc_sz (firstn j b1) (firstn j b2) = scc_sz b1 b2
  /\ scc_ok (firstn j b1) (firstn j b2)
  /\ length (firstn j b1) = j /\ length (firstn j b2) = j.
Proof.
  intros b1 b2 (L1 & L2) j.
  assert (HJ : j = S (scc_idx b1 b2)) by (unfold j, scc_sz; lia).
  assert (EI : scc_idx (firstn j b1) (firstn j b2) = scc_idx b1 b2) by (apply scc_idx_firstn; lia).
  assert (LJ1 : length (firstn j b1) = j) by (rewrite length_firstn; lia).
  assert (LJ2 : length (firstn j b2) = j) by (rewrite length_firstn; lia).
  split; [exact EI|]. split.
  - unfold scc_res. rewrite EI. rewrite !nth_error_firstn_lt by lia. reflexivity.
  - split; [unfold scc_sz; rewrite EI; reflexivity|]. split; [unfold scc_ok; rewrite EI, LJ1, LJ2; lia|].
    split; [exact LJ1| exact LJ2].
Qed.

(* ---- the frame ---- *)

Lemma icase_prologue : forall (sp p1 p2 : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo sp -> lo <= sp - ISTRNCMP_DEPTH -> kHighShadowEnd < lo -> sp < 2^63 -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (junk : list byte),
      ms' = MS (mkR ra (Z_to_bv 64 (sp + -2176)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 p2)
                    (Z_to_bv 64 p1) (Z_to_bv 64 p2) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p1) ra
                    s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x44b44) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2176, sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m' (sp + -2176) [CB 2072 junk]
      /\ stk asegs m' lo (sp + -2176))
    (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p1) (Z_to_bv 64 p2) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44af8) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2176, sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  carve_frame 104%nat ST. rename FR into FRs. carve_frame 2072%nat ST.
  do 19 lstep.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRs|]. split; [exact FR| exact ST].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* from the end of the first check (0x44bfc) to the return *)
Lemma icase_tail2 : forall (usp p1 p2 sz r : Z)
    (ra ra' gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s7' s10' : word) F fc (m0 m : mem) (lo : Z) (junk : list byte),
  stk asegs m lo (usp + -2176) -> lo <= usp - ISTRNCMP_DEPTH -> kHighShadowEnd < lo -> usp < 2^63 ->
  rw_cells asegs m (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (usp + -2176) [CB 2072 junk] ->
  munch [(usp - 2256, usp)] m0 m -> wmono asegs m0 m ->
  0 <= p2 -> 1 <= sz -> p2 + sz <= 2^47 ->
  chk_ok m p2 sz -> m2s_cells m -> icells_sc m -> mem_inv asegs m ->
  evt asegs (istrncmp_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r lo m0)
    (MS (mkR ra' (Z_to_bv 64 (usp + -2176)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 p2) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p1) ra (Z_to_bv 64 sz) (Z_to_bv 64 r) (Z_to_bv 64 (sz - 1)) s7' s8 s9 s10'
             (Z_to_bv 64 0x13db28) t3 t4 t5 t6)
        F (Z_to_bv 64 0x44bfc) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until junk. intros ST LO LOLO SPH FRs FR MU WM P2 SZ0 R2 CS2 M2S IC MI.
  unfold kHighShadowEnd in *.
  pose proof IC as (G70 & G2 & SHC & AI & SSC).
  assert (EUp2 : bv_unsigned (Z_to_bv 64 p2) = p2) by (apply unsigned_lit; lia).
  assert (EUsz : bv_unsigned (Z_to_bv 64 sz) = sz) by (apply unsigned_lit; lia).
  assert (EUnp2 : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p2)) = 18446744073709551615 - p2) by (apply unsigned_lit; lia).
  lstep. lstep. if_false.
  lstep. rewrite (lxor_ones64 p2) by lia. lstep. if_false.
  call (icase_chk2 RIP usp p2 sz); [exact ST| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact CS2| exact M2S| exact IC
        | assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2176) |- _ => rename H into ST3 end.
  do 22 lstep.
  release_frame FR ST3 (usp + -104). release_frame FRs ST3 usp.
  lstep.
  unfold istrncmp_post. sys_finish.
  + rewrite (unsigned_lit usp) by lia. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
  + rewrite (unsigned_lit usp) by lia. assumption.
Qed.

(* from the end of the loop (0x44b98) to the return *)
Lemma icase_tail : forall (usp p1 p2 sz r : Z)
    (ra ra' gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s6' s7' s10' s11' : word) F fc (m0 m : mem) (lo : Z) (junk : list byte),
  stk asegs m lo (usp + -2176) -> lo <= usp - ISTRNCMP_DEPTH -> kHighShadowEnd < lo -> usp < 2^63 ->
  rw_cells asegs m (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (usp + -2176) [CB 2072 junk] ->
  munch [(usp - 2256, usp)] m0 m -> wmono asegs m0 m ->
  0 <= p1 -> 0 <= p2 -> 1 <= sz -> p1 + sz <= 2^47 -> p2 + sz <= 2^47 ->
  chk_ok m p1 sz -> chk_ok m p2 sz -> m2s_cells m -> icells_sc m -> mem_inv asegs m ->
  evt asegs (istrncmp_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r lo m0)
    (MS (mkR ra' (Z_to_bv 64 (usp + -2176)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 p2) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p1) ra (Z_to_bv 64 sz) (Z_to_bv 64 r) s6' s7' s8 s9 s10' s11' t3 t4 t5 t6)
        F (Z_to_bv 64 0x44b98) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until junk. intros ST LO LOLO SPH FRs FR MU WM P1 P2 SZ0 R1 R2 CS1 CS2 M2S IC MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(usp - 2256, usp)] m) as MUl. pose proof (wmono_refl asegs m) as WMl.
  pose proof IC as (G70 & G2 & SHC & AI & SSC).
  assert (EUp1 : bv_unsigned (Z_to_bv 64 p1) = p1) by (apply unsigned_lit; lia).
  assert (EUsz : bv_unsigned (Z_to_bv 64 sz) = sz) by (apply unsigned_lit; lia).
  assert (EUsz1 : bv_unsigned (Z_to_bv 64 (sz + -1)) = sz - 1) by (apply unsigned_lit; lia).
  assert (EUnp1 : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p1)) = 18446744073709551615 - p1) by (apply unsigned_lit; lia).
  lstep. lstep. lstep. lstep. lstep. lstep. lstep. if_false.
  lstep. rewrite (lxor_ones64 p1) by lia. lstep. if_false.
  replace (sz + -1) with (sz - 1) by lia.
  call (icase_chk1 RIP usp p1 sz); [exact ST| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact CS1| exact M2S| exact IC
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
  eapply icase_tail2; try eassumption; lia.
Qed.

(* the wrapper, entered with x in a0 and y in a1: it answers scc_res of the two byte lists, reading the scc_sz bytes
   of each (both lists hold at least that many: scc_ok) *)
Theorem istrcasecmp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p1 p2 : Z) (b1 b2 : list byte) (lo : Z),
  a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRNCMP_DEPTH -> kHighShadowEnd < lo -> bv_unsigned sp < 2^63 ->
  bytes_at asegs m p1 b1 -> bytes_at asegs m p2 b2 -> scc_ok b1 b2 ->
  p1 + scc_sz b1 b2 <= 2^47 -> p2 + scc_sz b1 b2 <= 2^47 ->
  (p1 + scc_sz b1 b2 <= bv_unsigned sp - ISTRNCMP_DEPTH \/ bv_unsigned sp <= p1) ->
  (p2 + scc_sz b1 b2 <= bv_unsigned sp - ISTRNCMP_DEPTH \/ bv_unsigned sp <= p2) ->
  chk_ok m p1 (scc_sz b1 b2) -> chk_ok m p2 (scc_sz b1 b2) -> m2s_cells m -> icells_sc m -> mem_inv asegs m ->
  evt asegs (istrncmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (scc_res b1 b2) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44af8) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros -> -> ST LO LOLO SPH B1 B2 OK R1 R2 SEP1 SEP2 CS1 CS2 M2S IC MI.
  unfold kHighShadowEnd in *.
  destruct (scc_trunc b1 b2 OK) as (EI & ER & ES & OKc & LC1 & LC2).
  rewrite <- ER.
  set (sz := scc_sz b1 b2) in *.
  set (c1 := firstn (Z.to_nat sz) b1) in *. set (c2 := firstn (Z.to_nat sz) b2) in *.
  assert (BC1 : keep (bytes_at asegs m p1 c1)) by (apply bytes_at_firstn_a; exact B1).
  assert (BC2 : keep (bytes_at asegs m p2 c2)) by (apply bytes_at_firstn_a; exact B2).
  pose proof (bytes_at_bound _ _ _ _ B1) as BB1. pose proof (bytes_at_bound _ _ _ _ B2) as BB2.
  assert (SZ1 : 1 <= sz) by (unfold sz, scc_sz; lia).
  clear B1 B2 EI ER OK. clearbody c1 c2.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - 2256, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2176 : bv_unsigned (Z_to_bv 64 (usp + -2176)) = usp + -2176) by (apply unsigned_lit; lia).
  call (icase_prologue usp p1 p2); [exact ST| lia| unfold kHighShadowEnd; lia| lia| exact MI|].
  rename PC into FRs. rename PC0 into FR. rename POST into ST.
  lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (IC1 : icells_sc mm)
      by (apply (icells_sc_agree m mm IC); [apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]
                                          | exact WM]) end.
  pose proof IC1 as (G70 & G2 & SHC & AI & SSC). clear IC1.
  call try_init_spec; [exact AI| rewrite EU2176; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2176 in H; rename H into ST2 end.
  lstep. if_false.
  lstep. lstep. lstep.
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
  { apply (icase_cmp_loop (scc_idx c1 c2) 0 p1 p2 c1 c2);
      [lia| exact OKc| exact BM1| exact BM2| rewrite LC1, Z2Nat.id by lia; lia| rewrite LC2, Z2Nat.id by lia; lia
      | apply ccp_0| assumption]. }
  intros ms' (a0' & a1' & a2' & a3' & ->).
  rewrite ES.
  eapply icase_tail; try eassumption; lia.
Qed.

End WithRIP.
