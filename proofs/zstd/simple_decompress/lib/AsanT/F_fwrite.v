(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import F_syscalls F_printf_iface F_stdio_write F_fwritex_gen Stdio_iface StdioFiles Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import MonadF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Lemma bv_eqb_refl' : forall (x : word), bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.

End CANSEC1.
Ltac if_lit :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

Section CANSEC2. Context {rc : runConstT}.
Section WithTowrite.
  Hypothesis TW : towrite_stmt.

  (* [comment removed for export] *)
  Lemma fwx_nofit0 : forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (Fp : Z) (flags : word) (wpos wbase wfn bufp fd : Z) (mode : word) (lbf : Z) (tail : list byte) (S l lo : Z),
    rw_cells bsegs m Fp (file_cells flags 0 wpos wbase wfn bufp 0 fd mode lbf tail) ->
    Z.land (bv_unsigned flags) 8 = 0 ->
    a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
    (0 < bufp < 2^63) -> (0 < l < 2^64) -> (0 <= S < 2^64) -> (0 <= wfn < 2^64) -> (wfn mod 2 = 0) ->
    stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) ->
    mem_inv bsegs m ->
    (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
    rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 ->
    evtF bsegs RNG (fun ms' => exists (t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' (Z_to_bv 64 wfn) t2' s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 l) a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (Z_to_bv 64 wfn) fc None m' (seg_rom bsegs)
                 /\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
                 /\ stk bsegs m' lo (bv_unsigned sp)
                 /\ rw_cells bsegs m' Fp (file_cells flags bufp bufp bufp wfn bufp 0 fd mode' lbf tail))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xbcab8) fc None m (seg_rom bsegs)).
  Proof.
    intros until lo. intros FC FL8 -> -> -> BUFP L SR WFN WFE ST LO LO0 MI Fp0 SEPF RSTK RFP.
    pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size file_cells csize Nat.add length] in BF.
    unfold file_cells in FC.
    carve_frame 64%nat ST.
    do 13 step.
    if_lit.
    step. step.
    eapply evtF_cut.
    { eapply (TW RNG _ (Z_to_bv 64 (bv_unsigned sp + -64))) with (buf := bufp) (bufsize := 0);
        [ rewrite unsigned_lit by (clear - BF Fp0; lia); exact FC | exact FL8 | lia | lia | lia | exact MI | rewrite unsigned_lit by (clear - BF Fp0; lia); exact RFP ]. }
    cbv beta. intros ms1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode' & m1 & -> & MU1 & WM1 & MI1 & FC1).
    rewrite unsigned_lit in MU1, FC1 by lia.
    change (ret_pc (Z_to_bv 64 0xbcb74)) with (ret_pc (Z_to_bv 64 0xbcb74)).
    rewrite (ret_pc_even 0xbcb74) by (cbn; lia).
    transport_after_call bsegs m0 m1 MU1 WM1.
    unfold file_cells in FC1.
    step. if_lit.
    do 5 step.
    if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite ?land_W64, ?Z.mod_small in Hr by lia. clear - Hr L. lia. }
    do 13 step.
    rewrite (ret_pc_even wfn) by (first [lia | exact WFE]).
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. do 12 eexists. exists m1.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST|].
    unfold file_cells. rewrite ?Z.add_0_r in FC1. exact FC1.
  Qed.
End WithTowrite.

Lemma zb_length' : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.

Lemma land8_of_land40 : forall f, Z.land f 40 = 0 -> Z.land f 8 = 0.
Proof.
  intros f H. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec i 3) as [->|NE].
  - pose proof (f_equal (fun z => Z.testbit z 3) H) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
    change (Z.testbit 8 3) with true. change (Z.testbit 40 3) with true in T. exact T.
  - change 8 with (2^3). rewrite Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 3 i); [lia|]. apply Bool.andb_false_r.
Qed.

Theorem fwrite_diag_proof {St : Type} : @fwrite_diag_stmt St.
Proof.
  unfold fwrite_diag_stmt. intros until s. intros TW W0 SRC BYT LS -> -> -> ST LO GLO SEPS1 SEPS2 SSP MI RSTK RIMG RSRC SP47 S47.
  destruct W0 as (flags & mode & e & wend & tail & FC & FL40 & WEND & HE).
  pose proof (land8_of_land40 _ FL40) as FL8.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length' in BS.
  assert (LSB : length (zb s) = length s) by apply zb_length'.
  set (S := bv_unsigned a0) in *.
  assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
  unfold FWRITE_DEPTH, GLOBALS_TOP in *. unfold zlength in *.
  change bsegs with bsegs in *.
  destruct SSP as [GOT GUARD]. change bsegs with bsegs in GOT, GUARD. unfold got_ssp, ssp_guard in GOT, GUARD.
  unfold stderr_fwrite. unfold zlength.
  replace (0 <? Z.of_nat (length s)) with true by (symmetry; apply Z.ltb_lt; lia).
  pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  unfold file_cells in FC.
  rewrite EA0.
  eapply implAM_evt. 2:{ intros ms' H; exact H. } cbv beta.
  carve_frame 64%nat ST.
  do 8 step. do 3 step. step. step. step. if_lit.
  step. step. step.
  rewrite (unsigned_lit (Z.of_nat (length s))) by (clear - LS; lia). rewrite Z.mul_1_l.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - RSP LO GLO; lia).
  (* [comment removed for export] *)
  eapply (evtF_cut bsegs RNG (fun ms' => exists (t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode1 : word) (m1 : mem),
      ms' = MS (mkR (Z_to_bv 64 0xbcc78) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' (Z_to_bv 64 F_STDIO_WRITE) t2'
                    (Z_to_bv 64 1) (Z_to_bv 64 (Z.of_nat (length s)))
                    (Z_to_bv 64 RSTDERR) (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length s))) a3' a4' a5' a6' a7'
                    (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 RSTDERR) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 F_STDIO_WRITE) fc None m1 (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp + -64); (RSTDERR, RSTDERR + 232)] m0 m1 /\ wmono bsegs m0 m1 /\ mem_inv bsegs m1
      /\ stk bsegs m1 lo (bv_unsigned sp + -64)
      /\ rw_cells bsegs m1 RSTDERR (file_cells flags 0x6233b8 0x6233b8 0x6233b8 F_STDIO_WRITE 0x6233b8 0 2 mode1 0xffffffff tail))).
  { destruct WEND as [-> | [-> ->]].
    - eapply evtF_mono.
      { eapply (fwx_nofit0 TW RNG) with (lo := lo); [exact FC | exact FL8 | reflexivity | reflexivity | reflexivity | try (rewrite ?ESP; clear - HE LS RSP LO GLO BS; cbn; lia) .. ];
          first [rewrite ESP; exact ST | exact MI | rewrite ESP; solve_rng | eapply rng_sub; [exact RIMG| cbn; lia| cbn; lia] ]. }
      cbv beta. intros ms1 (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode1 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FC1).
      rewrite ESP in MU1, ST1.
      do 12 eexists. exists m1. split; [reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. exact FC1.
    - eapply evtF_mono.
      { eapply (fwx_nofit RNG) with (lo := lo); [exact FC | reflexivity | reflexivity | reflexivity | try (rewrite ?ESP; clear - HE LS RSP LO GLO BS; cbn; lia) .. ];
          first [rewrite ESP; exact ST | exact MI | rewrite ESP; solve_rng | eapply rng_sub; [exact RIMG| cbn; lia| cbn; lia] ]. }
      cbv beta. intros ms1 (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1).
      rewrite ESP in MU1, ST1.
      do 11 eexists. exists mode, m1. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia. }
      split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
      eapply (rw_cells_transport bsegs _ m0 m1); [exact FC | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
  cbv beta. intros ms1 (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode1 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FC1).
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0. cbn in RA0. fold S in RA0.
  assert (SRC1 : bytes_at bsegs m1 S (to_bytes s)).
  { eapply (bytes_at_transport bsegs _ m0 m1); [exact SRC | exact MU1 | cbn; rewrite ?LSB; unfold to_bytes; rewrite ?length_map; clear - SEPS1 SEPS2 LO GLO; lia]. }
  assert (GOT1 : rw_cells bsegs m1 819168 [C8 (Z_to_bv 64 6434032)]).
  { eapply (rw_cells_transport bsegs _ m0 m1); [exact GOT | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
  assert (GUARD1 : rw_cells bsegs m1 6434032 [C8 canary]).
  { eapply (rw_cells_transport bsegs _ m0 m1); [exact GUARD | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
  assert (FC1' : rw_cells bsegs m1 RSTDERR (file_cells flags 0x6233b8 (0x6233b8 + zlength (@nil Z)) 0x6233b8 F_STDIO_WRITE 0x6233b8 0 2 mode1 0xffffffff tail)).
  { unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r. exact FC1. }
  clear FC1 GOT GUARD SRC.
  apply evtF_done.
  eapply implAM_post_evt''.
  { eapply (stdio_write_spec (St:=St) RNG) with (lo := lo) (S := S) (canary := canary) (buf := []) (fd := 2);
      [ exact FC1'
      | apply bytes_at_nil; clear; lia
      | exact SRC1
      | reflexivity | reflexivity | reflexivity
      | right; reflexivity
      | rewrite ESP; exact ST1 | rewrite ESP; unfold STDIO_WRITE_DEPTH; clear - LO; lia | exact GLO
      | split; [exact GOT1 | exact GUARD1] | exact MI1
      | try (rewrite ?ESP; unfold got_ssp, ssp_guard, zlength; cbn [length Z.of_nat]; clear - LO GLO RA0 BS LS SEPS1 SEPS2 SP47 S47 RSP; lia) .. ];
      first [ rewrite ESP; solve_rng | exact RIMG | unfold zlength; exact RSRC
            | eapply rng_sub; [exact RIMG| cbn; lia| unfold zlength; cbn; lia] ]. }
  cbv beta. intros [] st2 ms2 PO2.
  destruct PO2 as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
  rewrite ESP in MU2, ST2. unfold STDIO_WRITE_DEPTH in MU2.
  rewrite (ret_pc_even 0xbcc78) by (cbn; lia).
  assert (FR2 : rw_cells bsegs m2 (bv_unsigned sp + -64) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply (rw_cells_transport bsegs _ m1 m2); [| exact MU2 | exact WM2 | cbn; clear - LO GLO RSP; lia].
    eapply (rw_cells_transport bsegs _ m0 m1); [exact FR | exact MU1 | exact WM1 | cbn; clear - LO GLO RSP; lia]. }
  clear FR. unfold file_cells in FC2.
  (* [comment removed for export] *)
  step. step. unfold zlength. rewrite (bv_eqb_refl' (Z_to_bv 64 (Z.of_nat (length s)))). cbv iota.
  do 4 step.
  do 9 step.
  release_frame FR2 ST2 (bv_unsigned sp).
  apply evtF_done. unfold fwrite_diag_post.
  (* [comment removed for export] *)
  rewrite v_sltiu_b2z. replace (bv_unsigned (Z_to_bv 64 (Z.of_nat (length s))) <? bv_wrap 64 1) with false
    by (symmetry; apply Z.ltb_ge; rewrite unsigned_lit by (clear -LS; lia); change (bv_wrap 64 1) with 1; clear -LS; lia).
  cbn [Z.b2z]. rewrite (unsigned_lit 0) by lia.
  replace (Z.land (bv_unsigned (Z_to_bv 64 (0 + -1))) 1) with 1 by (vm_compute; reflexivity).
  do 14 eexists. exists m2.
  split; [reflexivity|].
  split. { apply (munch_trans _ m m0 m2); [| apply (munch_trans _ m0 m1 m2)].
           - eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia.
           - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia.
           - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia. }
  split. { eapply wmono_trans; [exact WM | eapply wmono_trans; [exact WM1 | exact WM2]]. }
  split; [exact MI2|]. split; [exact ST2|].
  split.
  { exists flags, mode1, 0x6233b8, 0x6233b8, tail. split; [| split; [exact FL40 | split; [right; split; reflexivity | clear; lia]]].
    unfold file_cells. rewrite ?Z.add_0_r in FC2. exact FC2. }
  split; [exact SSP2 | reflexivity].
Qed.

(* [comment removed for export] *)
End CANSEC2.
