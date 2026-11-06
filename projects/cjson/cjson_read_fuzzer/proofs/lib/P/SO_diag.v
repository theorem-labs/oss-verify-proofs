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
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_syscalls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_stdout_write.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Module SO_stdio_flush.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_stdout_write.SO_stdio_write.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_piface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Theorem stdio_write_flush_proof : stdio_write_flush_stmt.
Proof.
  unfold stdio_write_flush_stmt. intros until canary. intros SINK -> A1 -> ST LO GLO SPHI SEPB SSP MI.
  destruct SINK as (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BGLO). cbn [fst] in FC, BUF, LEN.
  unfold OUT_DEPTH, GLOBALS_TOP in *.
  pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
  assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
  assert (LR : 0 <= zlength rest) by (unfold zlength; lia).
  pose proof (rw_cells_bytes_at _ _ _ _ BUF) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
  apply bytes_at_app in BY as [BY _].
  rewrite <- (Z_to_bv_bv_unsigned a1).
  pose proof (bv_unsigned_in_range 64 a1) as RA1. unfold bv_modulus in RA1.
  eapply implM_mono.
  { eapply (stdio_write_spec (St:=St)) with (B := B) (fd := 2) (Fp := 144704) (buf := buf) (s := []) (S := bv_unsigned a1) (lo := lo) (canary := canary)
      (wend := B + 80) (bufsize := 80) (mode := mode) (lbf := 0xffffffff) (tail := tail) (flags := flags) (wfn := F_STDIO_WRITE);
      try reflexivity; try lia.
    - exact FC.
    - exact BY.
    - apply bytes_at_nil. unfold zlength; cbn [length]. lia.
    - exact ST.
    - unfold STDIO_WRITE_DEPTH. lia.
    - exact SSP.
    - exact MI.
    - unfold got_ssp. lia.
    - unfold ssp_guard. lia.
    - unfold zlength in *; cbn [length]. lia.
    - unfold zlength; cbn [length]. lia.
    - left. reflexivity.
    - intros _. rewrite A1, unsigned_lit by lia. unfold TASK_SIZE. lia. }
  cbv beta. intros [] st' ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & FC' & SSP' & ->).
  unfold STDIO_WRITE_DEPTH in MU.
  unfold stdio_write_flush_post. do 16 eexists. split; [reflexivity|].
  split. { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. unfold STDIO_WRITE_DEPTH in *. intros; lia. }
  split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [| exact SSP'].
  (* [comment removed for export] *)
  exists flags, mode, tail, (zb buf ++ rest). cbn [fst].
  split. { rewrite Z.add_0_r. exact FC'. }
  split; [exact FL32|]. split; [exact FL8|].
  split.
  { (* [comment removed for export] *)
    eapply (rw_cells_transport _ _ m m'); [exact BUF | exact MU | exact WM |].
    cbn. unfold zlength in *. lia. }
  split; [| split; [exact BHI| exact BGLO]]. unfold zlength in *. cbn [length]. rewrite length_app. unfold zb. rewrite length_map. lia.
Qed.
End SO_stdio_flush.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MonadX.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require JunkAbs.
Module SO_fwrite.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MonadX.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_stdout_write.SO_stdio_write OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_fwritex_gen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.Stdio_iface.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_piface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.JunkAbs.split_for_access_raw H segs m A cs kn n.
Lemma bv_eqb_refl' : forall (x : word), bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.

Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

(* [comment removed for export] *)
Lemma impl_post_evt'' : forall {R} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
  impl psegs (at_node psegs) t Q ms -> (forall r ms', Q r ms' -> evt psegs (Q' r) ms') ->
  impl psegs (at_node psegs) t Q' ms.
Proof.
  induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; [exact H|]. intros ms' H'. apply HQ. exact H'.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.
Lemma implM_post_evt'' : forall {St A} (c : M St A) s Q Q' ms,
  implM psegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt psegs (Q' a s') ms') ->
  implM psegs c s Q' ms.
Proof.
  intros St A c s Q Q' ms H HQ. unfold implM in *. eapply impl_post_evt''; [exact H|].
  intros [|[a s']] ms' H'; cbn in *; [apply evt_done; exact I| apply HQ; exact H'].
Qed.

Section WithTowrite.
  Hypothesis TW : towrite_stmt.

  (* [comment removed for export] *)
  Lemma fwx_nofit0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (Fp : Z) (flags : word) (wpos wbase wfn bufp fd : Z) (mode : word) (lbf : Z) (tail : list byte) (S l lo : Z),
    rw_cells psegs m Fp (file_cells flags 0 wpos wbase wfn bufp 0 fd mode lbf tail) ->
    Z.land (bv_unsigned flags) 8 = 0 ->
    a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
    (0 < bufp < 2^63) -> (0 < l < 2^64) -> (0 <= S < 2^64) -> (0 <= wfn < 2^64) -> (wfn mod 2 = 0) ->
    stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) ->
    mem_inv psegs m ->
    (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
    evt psegs (fun ms' => exists (t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' (Z_to_bv 64 wfn) t2' s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 l) a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (Z_to_bv 64 wfn) fc None m' (seg_rom psegs)
                 /\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
                 /\ stk psegs m' lo (bv_unsigned sp)
                 /\ rw_cells psegs m' Fp (file_cells flags bufp bufp bufp wfn bufp 0 fd mode' lbf tail))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x17554) fc None m (seg_rom psegs)).
  Proof.
    intros until lo. intros FC FL8 -> -> -> BUFP L SR WFN WFE ST LO LO0 MI Fp0 SEPF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232)] m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size file_cells csize Nat.add length] in BF.
    unfold file_cells in FC.
    carve_frame 64%nat ST.
    do 13 step.
    if_lit.
    step. step.
    eapply evt_cut.
    { eapply (TW _ (Z_to_bv 64 (bv_unsigned sp + -64))) with (buf := bufp) (bufsize := 0);
        [ rewrite unsigned_lit by (clear - BF Fp0; lia); exact FC | exact FL8 | lia | lia | lia | exact MI ]. }
    cbv beta. intros ms1 nelH_; (nelim nelH_ 21%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mode' m1 -> MU1 WM1 MI1 FC1).
    rewrite unsigned_lit in MU1, FC1 by lia.
    change (ret_pc (Z_to_bv 64 0x17610)) with (ret_pc (Z_to_bv 64 0x17610)).
    rewrite (ret_pc_even 0x17610) by (cbn; lia).
    transport_after_call psegs m0 m1 MU1 WM1.
    unfold file_cells in FC1.
    step. if_lit.
    do 5 step.
    if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite ?land_W64, ?Z.mod_small in Hr by lia. clear - Hr L. lia. }
    do 13 step.
    rewrite (ret_pc_even wfn) by (first [lia | exact WFE]).
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. nexists 12%nat. exists m1.
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
  unfold fwrite_diag_stmt. intros until s. intros TW W0 SRC BYT LS -> -> -> ST LO GLO SEPS1 SEPS2 SSP MI.
  (nelim W0 9%nat; intros flags mode e wend tail FC FL40 WEND HE).
  pose proof (land8_of_land40 _ FL40) as FL8.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length' in BS.
  assert (LSB : length (zb s) = length s) by apply zb_length'.
  set (S := bv_unsigned a0) in *.
  assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
  unfold FWRITE_DEPTH, GLOBALS_TOP in *. unfold zlength in *.
  change psegs with psegs in *.
  destruct SSP as [GOT GUARD]. change psegs with psegs in GOT, GUARD. unfold got_ssp, ssp_guard in GOT, GUARD.
  unfold stderr_fwrite. unfold zlength.
  replace (0 <? Z.of_nat (length s)) with true by (symmetry; apply Z.ltb_lt; lia).
  pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  unfold file_cells in FC.
  rewrite EA0.
  eapply (implM_evt psegs). 2:{ intros ms' H; exact H. } cbv beta.
  carve_frame 64%nat ST.
  do 8 step. do 3 step. step. step. step. if_lit.
  step. step. step.
  rewrite (unsigned_lit (Z.of_nat (length s))) by (clear - LS; lia). rewrite Z.mul_1_l.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - RSP LO GLO; lia).
  (* [comment removed for export] *)
  eapply (evt_cut psegs (fun ms' => exists (t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode1 : word) (m1 : mem),
      ms' = MS (mkR (Z_to_bv 64 0x17714) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' (Z_to_bv 64 F_STDIO_WRITE) t2'
                    (Z_to_bv 64 1) (Z_to_bv 64 (Z.of_nat (length s)))
                    (Z_to_bv 64 RSTDERR) (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length s))) a3' a4' a5' a6' a7'
                    (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 RSTDERR) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 F_STDIO_WRITE) fc None m1 (seg_rom psegs)
      /\ munch [(lo, bv_unsigned sp + -64); (RSTDERR, RSTDERR + 232)] m0 m1 /\ wmono psegs m0 m1 /\ mem_inv psegs m1
      /\ stk psegs m1 lo (bv_unsigned sp + -64)
      /\ rw_cells psegs m1 RSTDERR (file_cells flags 0x53f58 0x53f58 0x53f58 F_STDIO_WRITE 0x53f58 0 2 mode1 0xffffffff tail))).
  { destruct WEND as [-> | [-> ->]].
    - eapply evt_mono.
      { eapply (fwx_nofit0 TW) with (lo := lo); [exact FC | exact FL8 | reflexivity | reflexivity | reflexivity | try (rewrite ?ESP; clear - HE LS RSP LO GLO BS; cbn; lia) .. ];
          [rewrite ESP; exact ST | exact MI]. }
      cbv beta. intros ms1 nelH_; (nelim nelH_ 19%nat; intros t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mode1 m1 -> MU1 WM1 MI1 ST1 FC1).
      rewrite ESP in MU1, ST1.
      nexists 12%nat. exists m1. split; [reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. exact FC1.
    - eapply evt_mono.
      { eapply fwx_nofit with (lo := lo); [exact FC | reflexivity | reflexivity | reflexivity | try (rewrite ?ESP; clear - HE LS RSP LO GLO BS; cbn; lia) .. ];
          [rewrite ESP; exact ST | exact MI]. }
      cbv beta. intros ms1 nelH_; (nelim nelH_ 17%nat; intros t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 -> MU1 WM1 MI1 ST1).
      rewrite ESP in MU1, ST1.
      nexists 11%nat. exists mode, m1. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia. }
      split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
      eapply (rw_cells_transport psegs _ m0 m1); [exact FC | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
  cbv beta. intros ms1 nelH_; (nelim nelH_ 19%nat; intros t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mode1 m1 -> MU1 WM1 MI1 ST1 FC1).
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0. cbn in RA0. fold S in RA0.
  assert (SRC1 : bytes_at psegs m1 S (to_bytes s)).
  { eapply (bytes_at_transport psegs _ m0 m1); [exact SRC | exact MU1 | cbn; rewrite ?LSB; unfold to_bytes; rewrite ?length_map; clear - SEPS1 SEPS2 LO GLO; lia]. }
  assert (GOT1 : rw_cells psegs m1 140520 [C8 (Z_to_bv 64 342776)]).
  { eapply (rw_cells_transport psegs _ m0 m1); [exact GOT | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
  assert (GUARD1 : rw_cells psegs m1 342776 [C8 canary]).
  { eapply (rw_cells_transport psegs _ m0 m1); [exact GUARD | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
  assert (FC1' : rw_cells psegs m1 RSTDERR (file_cells flags 0x53f58 (0x53f58 + zlength (@nil Z)) 0x53f58 F_STDIO_WRITE 0x53f58 0 2 mode1 0xffffffff tail)).
  { unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r. exact FC1. }
  clear FC1 GOT GUARD SRC.
  apply evt_done.
  eapply implM_post_evt''.
  { eapply (stdio_write_spec (St:=St)) with (lo := lo) (S := S) (canary := canary) (buf := []) (fd := 2);
      [ exact FC1'
      | apply bytes_at_nil; clear; lia
      | exact SRC1
      | reflexivity | reflexivity | reflexivity
      | right; reflexivity
      | rewrite ESP; exact ST1 | rewrite ESP; unfold STDIO_WRITE_DEPTH; clear - LO; lia | exact GLO
      | split; [exact GOT1 | exact GUARD1] | exact MI1
      | first [ (rewrite ?ESP; unfold got_ssp, ssp_guard, zlength; cbn [length Z.of_nat]; clear - LO GLO RA0 BS LS SEPS1 SEPS2; lia)
              | (let E := fresh in intros E; rewrite E in *; unfold zlength in *; cbn [length Z.of_nat] in *; lia) ] .. ]. }
  cbv beta. intros [] st2 ms2 PO2.
  (nelim PO2 23%nat; intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m2 -> MU2 WM2 MI2 ST2 FC2 SSP2 ->).
  rewrite ESP in MU2, ST2. unfold STDIO_WRITE_DEPTH in MU2.
  rewrite (ret_pc_even 0x17714) by (cbn; lia).
  assert (FR2 : rw_cells psegs m2 (bv_unsigned sp + -64) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply (rw_cells_transport psegs _ m1 m2); [| exact MU2 | exact WM2 | cbn; clear - LO GLO RSP; lia].
    eapply (rw_cells_transport psegs _ m0 m1); [exact FR | exact MU1 | exact WM1 | cbn; clear - LO GLO RSP; lia]. }
  clear FR. unfold file_cells in FC2.
  (* [comment removed for export] *)
  step. step. unfold zlength. rewrite (bv_eqb_refl' (Z_to_bv 64 (Z.of_nat (length s)))). cbv iota.
  do 4 step.
  do 9 step.
  release_frame FR2 ST2 (bv_unsigned sp).
  apply evt_done. unfold fwrite_diag_post.
  nexists 15%nat. exists m2.
  split; [reflexivity|].
  split. { apply (munch_trans _ m m0 m2); [| apply (munch_trans _ m0 m1 m2)].
           - eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia.
           - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia.
           - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia. }
  split. { eapply wmono_trans; [exact WM | eapply wmono_trans; [exact WM1 | exact WM2]]. }
  split; [exact MI2|]. split; [exact ST2|].
  split.
  { exists flags, mode1, 0x53f58, 0x53f58, tail. split; [| split; [exact FL40 | split; [right; split; reflexivity | clear; lia]]].
    unfold file_cells. rewrite ?Z.add_0_r in FC2. exact FC2. }
  split; [exact SSP2 | reflexivity].
Qed.
End SO_fwrite.

(* [comment removed for export] *)
Module SO_fwritex_stderr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_stdout_write.SO_stdio_write OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_fwritex_gen.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_piface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma zb_length : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.

Theorem fwritex_stderr_proof : fwritex_stderr_stmt.
Proof.
  unfold fwritex_stderr_stmt, out_stmt. intros St B. intros until canary.
  intros SINK SRC BYT BSL -> -> ST LO GLO SPHI TOP SSP MI SEPF SEPB SEPS1 SEPS2 SEPS3.
  destruct st as [buf st].
  destruct SINK as (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BGLO). cbn [fst] in FC, BUF, LEN.
  unfold OUT_DEPTH, GLOBALS_TOP, INTERNAL_BUFSIZ in *.
  change psegs with psegs in *.
  destruct SSP as [GOT GUARD]. change psegs with psegs in GOT, GUARD. unfold got_ssp, ssp_guard in GOT, GUARD.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length in BS.
  assert (LSB : length (zb bs) = length bs) by apply zb_length.
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0.
  assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
  assert (LR : 0 <= zlength rest) by (unfold zlength; lia).
  assert (LS : 0 <= zlength bs) by (unfold zlength; lia).
  unfold zlength in *.
  set (S := bv_unsigned a0) in *.
  assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  pose proof BUF as BUF0.
  apply (rw_cells_split_CB psegs _ _ [] 80 (zb buf ++ rest) [] [length buf; 80 - length buf]%nat) in BUF; [| cbn; unfold zlength in *; lia].
  cbn [mk_CB_cells app] in BUF.
  rewrite firstn_app, zb_length, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in BUF by (rewrite zb_length; lia).
  rewrite skipn_app, zb_length, Nat.sub_diag, skipn_O, skipn_all2 in BUF by (rewrite zb_length; lia). cbn [app] in BUF.
  apply (proj1 (F_fwritex.rw_cells_app psegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUFb].
  cbn [cells_size csize Nat.add] in BUFb. rewrite Nat.add_0_r in BUFb. rewrite ?firstn_all2 in BUFb by lia.
  unfold implM, OUT_stderr.
  destruct (80 - zlength buf <? zlength bs) eqn:CMP.
  - (* [comment removed for export] *)
    pose proof (proj1 (Z.ltb_lt _ _) CMP) as CMP'. unfold zlength in CMP'.
    eapply impl_evt.
    { eapply fwx_nofit with (lo := lo); [exact FC | exact EA0 | reflexivity | reflexivity | lia | lia | unfold zlength in *; lia | lia | lia | reflexivity | exact ST | lia | lia | exact MI | lia]. }
    cbv beta. intros ms1 PO.
    destruct PO as (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1).
    unfold file_cells in FC.
    transport_after_call psegs m m1 MU1 WM1.
    unfold INTERNAL_BUFSIZ. cbv beta iota zeta. match goal with |- context [if ?c then _ else _] => replace c with true by (symmetry; exact CMP) end. cbv beta iota zeta.
    eapply impl_ebind.
    { eapply (stdio_write_spec (St:=St)) with (B := B) (fd := 2) (Fp := 144704) (buf := buf) (s := bs) (S := S) (lo := lo) (canary := canary)
        (wend := B + 80) (bufsize := 80) (mode := mode) (lbf := 0xffffffff) (tail := tail) (flags := flags) (wfn := F_STDIO_WRITE);
        try reflexivity.
      - exact FC.
      - apply (bytes_at_ext _ _ _ _ _ (rw_cells_bytes_at _ _ _ _ BUFa)). cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
      - exact SRC.
      - lia.
      - exact ST1.
      - unfold STDIO_WRITE_DEPTH. lia.
      - lia.
      - split; [exact GOT | exact GUARD].
      - exact MI1.
      - lia. - lia.
      - unfold got_ssp. lia.
      - unfold ssp_guard. lia.
      - lia. - lia.
      - unfold zlength. lia.
      - lia.
      - unfold zlength. lia.
      - lia.
      - unfold zlength. lia.
      - right. unfold zlength. lia.
      - unfold zlength. lia.
      - intros E. rewrite E in CMP'. cbn [length Z.of_nat] in CMP'. lia. }
    cbv beta. intros [[] st'] ms' PO. cbn [fst snd] in PO.
    destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
    unfold STDIO_WRITE_DEPTH in MU2.
    apply impl_ret_ok. cbn [fst snd]. apply evt_done.
    (* [comment removed for export] *)
    pose proof (rw_cells_transport psegs _ m1 m2 _ _ BUF0 MU2 WM2 ltac:(cbn; lia)) as BUF2.
    pose proof (bytes_at_transport psegs _ m1 m2 _ _ SRC MU2 ltac:(cbn; rewrite LSB; lia)) as SRC2.
    unfold out_post, SR. do 16 eexists. split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m2).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | exact WM2] |]. split; [exact MI2|]. split; [exact ST2|].
    split.
    { (* [comment removed for export] *)
      exists flags, mode, tail, (zb buf ++ rest). cbn [fst].
      split; [rewrite Z.add_0_r; exact FC2|]. split; [exact FL32|]. split; [exact FL8|].
      split; [exact BUF2|]. split; [| split; [exact BHI| exact BGLO]].
      unfold zlength. cbn [length]. rewrite length_app, zb_length. lia. }
    split; [exact SSP2 | exact SRC2].
  - (* [comment removed for export] *)
    pose proof (proj1 (Z.ltb_ge _ _) CMP) as CMP'. unfold zlength in CMP'.
    cbv beta iota zeta. match goal with |- context [if ?c then _ else _] => replace c with false by (symmetry; exact CMP) end. cbv beta iota zeta.
    apply impl_ret_ok. cbn [fst snd].
    unfold file_cells in FC.
    eapply evt_mono.
    { eapply (fwx_fit_plain ra sp gp tp t0 t1 t2 s0 s1 a0) with (lo := lo) (cap := (80 - length buf)%nat) (src := zb bs) (S := S)
        (Fp := 144704) (wend := B + 80) (wpos := B + Z.of_nat (length buf)) (junk := rest);
        [ exact FC | exact BUFb | lia | exact SRC | rewrite LSB; reflexivity | exact EA0 | reflexivity | reflexivity | try lia .. ];
        [exact ST | exact MI].
    }
    cbv beta. intros ms' PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & DST2 & SRC2).
    unfold out_post, SR. do 16 eexists.
    split. { reflexivity. }
    split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
    assert (GOT2 : rw_cells psegs m2 140520 [C8 (Z_to_bv 64 342776)]).
    { eapply (rw_cells_transport psegs _ m m2); [exact GOT | exact MU2 | exact WM2 | cbn; lia]. }
    assert (GUARD2 : rw_cells psegs m2 342776 [C8 canary]).
    { eapply (rw_cells_transport psegs _ m m2); [exact GUARD | exact MU2 | exact WM2 | cbn; lia]. }
    assert (BUFa2 : rw_cells psegs m2 B [CB (length buf) (zb buf)]).
    { eapply (rw_cells_transport psegs _ m m2); [exact BUFa | exact MU2 | exact WM2 | cbn; lia]. }
    split.
    { (* [comment removed for export] *)
      exists flags, mode, tail, (skipn (length (zb bs)) rest). cbn [fst].
      split. { unfold zlength. rewrite length_app, Nat2Z.inj_add, Z.add_assoc. exact FC2. }
      split; [exact FL32|]. split; [exact FL8|].
      split.
      { (* [comment removed for export] *)
        assert (J : rw_cells psegs m2 B ([] ++ [CB (length buf) (zb buf); CB (length (zb bs)) (zb bs); CB (80 - length buf - length (zb bs))%nat (skipn (length (zb bs)) rest)] ++ [])).
        { cbn [app]. apply (proj2 (F_fwritex.rw_cells_app psegs _ _ [_] _)); split; [exact BUFa2|].
          cbn [cells_size csize]. rewrite Nat.add_0_r. exact DST2. }
        apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite app_nil_r in J.
        rewrite zb_app, <- app_assoc. rewrite LSB in J |- *.
        replace (length buf + (length bs + (80 - length buf - length bs + 0)))%nat with 80%nat in J by lia. exact J. }
      split; [| split; [exact BHI| exact BGLO]].
      unfold zlength. rewrite length_app, length_skipn, LSB. lia. }
    split; [split; [exact GOT2 | exact GUARD2] | exact SRC2].
Qed.
End SO_fwritex_stderr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RelSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac PropExec MState Mem Exec ITree Nodes Decode SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import RzNodesImpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad FmtFp Stdio Driver.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_fmt_fp_lib F_pad Exit Printf_model F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_vsnprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_vsnprintf.F_vfprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_vsnprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_piface.   (* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_rz.
Import SO_fwritex_stderr.
Import SO_stdio_flush.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_fprintf.
Import SO_fwrite.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
      (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).
Local Notation rzt := (SO_rz.rzt psegs).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zlength_app' : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rzt_stderr_pieces : forall {St} (ps : list (list Z)) (buf : list Z) (st : St) mo,
  chan_ok mo 2 -> Forall (fun p => zlength p <= 2^25) ps -> zlength buf <= INTERNAL_BUFSIZ ->
  exists e buf', buf ++ concat ps = e ++ buf' /\ zlength buf' <= INTERNAL_BUFSIZ /\
    rzt (stderr_pieces buf ps st) mo (map (WriteEv (Z_to_bv 64 2)) (to_bytes e)) (fun r => r = (buf', st)).
Proof.
  intros St ps. induction ps as [|p ps IH]; intros buf st mo CH SM HB.
  - exists [], buf. cbn [concat]. rewrite app_nil_r. split; [reflexivity|]. split; [exact HB|].
    cbn [stderr_pieces to_bytes map]. apply rzt_mret. reflexivity.
  - apply Forall_cons_iff in SM. destruct SM as [SP SM]. cbn [stderr_pieces concat].
    destruct (Z.ltb_spec (INTERNAL_BUFSIZ - zlength buf) (zlength p)) as [LT|GE].
    + destruct (IH [] st mo CH SM ltac:(unfold INTERNAL_BUFSIZ, zlength; cbn; lia)) as (e2 & buf2 & E2 & HB2 & RZ2).
      exists ((buf ++ p) ++ e2), buf2. split; [cbn [app] in E2; rewrite E2, !app_assoc; reflexivity|]. split; [exact HB2|].
      rewrite to_bytes_app, map_app.
      eapply rzt_mbind.
      * apply (rzt_stdio_writev psegs st mo 2 buf p CH). unfold INTERNAL_BUFSIZ in *. lia.
      * intros [] s' Hs. cbn [snd] in Hs. subst s'. exact RZ2.
    + destruct (IH (buf ++ p) st mo CH SM ltac:(rewrite zlength_app'; lia)) as (e2 & buf2 & E2 & HB2 & RZ2).
      exists e2, buf2. split; [rewrite <- E2, app_assoc; reflexivity|]. split; [exact HB2| exact RZ2].
Qed.

Lemma rzt_stderr_fprintf : forall {St} (ps : list (list Z)) (st : St) mo,
  chan_ok mo 2 -> Forall (fun p => zlength p <= 2^25) ps ->
  rzt (stderr_fprintf ps st) mo (map (WriteEv (Z_to_bv 64 2)) (to_bytes (concat ps))) (fun r => snd r = st).
Proof.
  intros St ps st mo CH SM.
  destruct (rzt_stderr_pieces ps [] st mo CH SM ltac:(unfold INTERNAL_BUFSIZ, zlength; cbn; lia)) as (e & buf' & E & HB & RZ).
  cbn [app] in E. rewrite E, to_bytes_app, map_app. unfold stderr_fprintf.
  eapply rzt_mbind; [exact RZ|]. intros b s' Hs. injection Hs as -> ->.
  replace (to_bytes buf') with (to_bytes (buf' ++ [])) by (rewrite app_nil_r; reflexivity).
  apply (rzt_stdio_writev psegs st mo 2 buf' [] CH).
  unfold INTERNAL_BUFSIZ, zlength in *. cbn [length]. lia.
Qed.

Lemma rzt_stderr_fwrite : forall {St} (s : list Z) (st : St) mo,
  chan_ok mo 2 -> 0 < zlength s <= 2^25 ->
  rzt (stderr_fwrite s st) mo (map (WriteEv (Z_to_bv 64 2)) (to_bytes s)) (fun r => snd r = st).
Proof.
  intros St s st mo CH LEN. unfold stderr_fwrite. rewrite (proj2 (Z.ltb_lt 0 (zlength s))) by lia.
  change (to_bytes s) with (to_bytes ([] ++ s)). apply (rzt_stdio_writev psegs st mo 2 [] s CH).
  unfold zlength in *. cbn [length]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fdiag_pieces_small : forall d, diag_small d -> Forall (fun p => zlength p <= 2^25) (fdiag_pieces d).
Proof.
  intros d SM. destruct d as [s|s|s| | | |]; cbn [fdiag_pieces diag_small] in *;
    unfold pieces_usage, pieces_cannot_open, pieces_read_error, pieces_too_big, pieces_oom, pieces_short_hdr, pieces_cfg_overrun;
    repeat (apply Forall_cons; [first [exact SM | (apply Z.leb_le; vm_compute; reflexivity)] |]); apply Forall_nil.
Qed.

Theorem so_fprintf_diag_proof : so_fprintf_diag_stmt.
Proof.
  unfold so_fprintf_diag_stmt. intros until K. intros HM CH SEF Ha0 DA SM ST LO GLO QHI SSP MI FRM HK HC.
  pose proof (@fprintf_diag_proof unit d ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m tt lo canary fwritex_stderr_proof stdio_write_flush_proof SEF Ha0 DA ST LO GLO QHI SSP MI FRM) as H.
  unfold implM in H.
  assert (RZ : rzt (s_diag (St:=unit) d tt) mo (W 2 (fdiag_bytes d)) (fun r => snd r = tt)).
  { pose proof (rzt_stderr_fprintf (fdiag_pieces d) tt mo CH (fdiag_pieces_small d SM)) as R.
    destruct d; cbn [diag_args] in DA; try contradiction; exact R. }
  apply (RZ _ _ K HM H HK). intros [[] []] ms' PO _. cbn [fst snd] in PO. unfold fprintf_diag_post in PO.
  destruct PO as (x5 & x6 & x7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & SF' & SSP' & _).
  eapply HC; eassumption.
Qed.

Theorem so_fwrite_diag_proof : so_fwrite_diag_stmt.
Proof.
  unfold so_fwrite_diag_stmt. intros until K. intros HM CH SEF BY HF LEN Ha1 Ha2 Ha3 ST LO GLO DJ1 DJ2 SSP MI HK HC.
  pose proof (@fwrite_diag_proof unit ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m tt lo canary s towrite_proof SEF BY HF ltac:(lia) Ha1 Ha2 Ha3 ST LO GLO DJ1 DJ2 SSP MI) as H.
  unfold implM in H.
  pose proof (rzt_stderr_fwrite s tt mo CH ltac:(lia)) as RZ.
  change (zb s) with (to_bytes s). unfold W.
  apply (RZ _ _ K HM H HK). intros [[] []] ms' PO _. cbn [fst snd] in PO. unfold fwrite_diag_post in PO.
  destruct PO as (x5 & x6 & x7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & SF' & SSP' & _).
  eapply HC; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_Forall_pos : forall s : list byte, ~ In (Z_to_bv 8 0) s -> Forall (fun c => 0 < c < 256) (map bv_unsigned s).
Proof.
  intros s NI. apply Forall_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as (b & <- & Hb).
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE]; [|lia].
  exfalso. apply NI. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite Z_to_bv_unsigned. rewrite E. reflexivity.
Qed.

Lemma zb_of_bytes : forall s : list byte, zb (map bv_unsigned s) = s.
Proof. intros s. change (zb (map bv_unsigned s)) with (to_bytes (map bv_unsigned s)). apply to_bytes_of_bytes. Qed.

Lemma zlength_map' : forall {A B} (f : A -> B) l, zlength (map f l) = zlength l.
Proof. intros. unfold zlength. rewrite length_map. reflexivity. Qed.

Section StrDiag.
  Variable d_of : list Z -> diag_msg.
  Variable fmt : Z.
  Variable msg : list byte -> list byte.
  Hypothesis d_of_shape : forall s, d_of s = DUsage s \/ d_of s = DCannotOpen s \/ d_of s = DReadError s.
  Hypothesis fmt_eq : forall s, match d_of s with DUsage _ => A_FMT_usage | DCannotOpen _ => A_FMT_cannot_open | _ => A_FMT_read_error end = fmt.
  Hypothesis msg_eq : forall s : list byte, fdiag_bytes (d_of (map bv_unsigned s)) = msg s.

  Lemma so_diag_str_of : so_fprintf_diag_stmt -> so_diag_str_stmt fmt msg.
  Proof.
    intros FP. unfold so_diag_str_stmt. intros until K. intros HM CH SEF Ha0 Ha1 BY NI SLK LEN DJ GA ST LO GLO QHI SSP MI FRM HK HC.
    rewrite <- msg_eq. unfold so_fprintf_diag_stmt in FP.
    eapply FP; [exact HM | exact CH | exact SEF | exact Ha0 | | | exact ST | exact LO | exact GLO | exact QHI | exact SSP | exact MI | exact FRM | exact HK | exact HC].
    - pose proof (d_of_shape (map bv_unsigned s)) as SH. pose proof (fmt_eq (map bv_unsigned s)) as FE.
      assert (BODY : exists slack0 : list byte,
             bytes_at psegs m (bv_unsigned a2) (zb (map bv_unsigned s) ++ Z_to_bv 8 0 :: slack0)
             /\ Forall (fun c => 0 < c < 256) (map bv_unsigned s)
             /\ ((- (bv_unsigned a2 + zlength (map bv_unsigned s) + 1)) mod 8 <= zlength slack0)
             /\ (zlength (map bv_unsigned s) < INT_MAX - 256)
             /\ (bv_unsigned a2 + zlength (map bv_unsigned s) + 1 + zlength slack0 <= lo \/ bv_unsigned sp <= bv_unsigned a2)
             /\ (GLOBALS_TOP <= bv_unsigned a2)).
      { exists slack. rewrite zb_of_bytes, zlength_map'. split; [exact BY|]. split; [apply bytes_Forall_pos; exact NI|].
        split; [exact SLK|]. split; [unfold INT_MAX; lia|]. split; [exact DJ| exact GA]. }
      unfold diag_args. destruct SH as [E|[E|E]]; rewrite E in FE |- *; (split; [rewrite Ha1, <- FE; reflexivity| exact BODY]).
    - unfold diag_small. destruct (d_of_shape (map bv_unsigned s)) as [E|[E|E]]; rewrite E, zlength_map'; lia.
  Qed.
End StrDiag.

Theorem so_diag_usage_proof : so_diag_usage_stmt.
Proof. apply (so_diag_str_of DUsage); [intros; left; reflexivity | intros; reflexivity | apply msg_usage_eq | apply so_fprintf_diag_proof]. Qed.
Theorem so_diag_cannot_open_proof : so_diag_cannot_open_stmt.
Proof. apply (so_diag_str_of DCannotOpen); [intros; right; left; reflexivity | intros; reflexivity | apply msg_cannot_open_eq | apply so_fprintf_diag_proof]. Qed.
Theorem so_diag_read_error_proof : so_diag_read_error_stmt.
Proof. apply (so_diag_str_of DReadError); [intros; right; right; reflexivity | intros; reflexivity | apply msg_read_error_eq | apply so_fprintf_diag_proof]. Qed.

Theorem so_diag_refused_proof : so_diag_refused_stmt.
Proof.
  unfold so_diag_refused_stmt. intros until K. intros HM CH SEF Ha0 Ha1 Ha2 ST LO GLO QHI SSP MI FRM HK HC.
  rewrite <- msg_refused_eq.
  eapply so_fprintf_diag_proof; [exact HM | exact CH | exact SEF | exact Ha0 | | exact I | exact ST | exact LO | exact GLO | exact QHI | exact SSP | exact MI | exact FRM | exact HK | exact HC].
  cbn [diag_args]. split; [exact Ha1| exact Ha2].
Qed.

Section LitDiag.
  Variable A n : Z.
  Variable lit : list Z.          (* [comment removed for export] *)
  Variable msg : list byte.
  Hypothesis msg_eq : zb lit = msg.
  Hypothesis lit_len : zlength lit = n.
  Hypothesis lit_range : Forall (fun c => 0 <= c < 256) lit.
  Hypothesis n_rng : 0 < n < 256.
  Hypothesis ro : ro_bytes_b psegs A (zb lit) = true.
  Hypothesis A_rng : 65536 <= A /\ A + n <= 0x12000.

  Lemma so_diag_lit_of : so_fwrite_diag_stmt -> so_diag_lit_stmt A n msg.
  Proof.
    intros FW. unfold so_diag_lit_stmt. intros until K. intros HM CH SEF Ha0 Ha1 Ha2 Ha3 ST LO GLO SSP MI HK HC.
    rewrite <- msg_eq. unfold so_fwrite_diag_stmt in FW.
    pose proof A_rng as AR. unfold FWRITE_DEPTH, GLOBALS_TOP in *.
    assert (EA : bv_unsigned a0 = A) by (rewrite Ha0, unsigned_lit; lia).
    eapply FW; [exact HM | exact CH | exact SEF | | exact lit_range | lia | rewrite lit_len; exact Ha1 | exact Ha2 | exact Ha3 | exact ST | exact LO | unfold GLOBALS_TOP; exact GLO | left; rewrite EA; lia | left; rewrite EA; lia | exact SSP | exact MI | exact HK | exact HC].
    rewrite EA. apply fmt_bytes_at; [exact MI | exact ro | lia | lia].
  Qed.
End LitDiag.

Theorem so_diag_oom_proof : so_diag_oom_stmt.
Proof.
  apply (so_diag_lit_of A_MSG_oom 19 (concat pieces_oom));
    [apply msg_oom_eq | reflexivity | | lia | vm_compute; reflexivity | unfold A_MSG_oom; lia | apply so_fwrite_diag_proof].
  apply forall_range_b. vm_compute. reflexivity.
Qed.
Theorem so_diag_short_proof : so_diag_short_stmt.
Proof.
  apply (so_diag_lit_of A_MSG_short 31 (concat pieces_short_hdr));
    [apply msg_short_eq | reflexivity | | lia | vm_compute; reflexivity | unfold A_MSG_short; lia | apply so_fwrite_diag_proof].
  apply forall_range_b. vm_compute. reflexivity.
Qed.
Theorem so_diag_overrun_proof : so_diag_overrun_stmt.
Proof.
  apply (so_diag_lit_of A_MSG_overrun 31 (concat pieces_cfg_overrun));
    [apply msg_overrun_eq | reflexivity | | lia | vm_compute; reflexivity | unfold A_MSG_overrun; lia | apply so_fwrite_diag_proof].
  apply forall_range_b. vm_compute. reflexivity.
Qed.
