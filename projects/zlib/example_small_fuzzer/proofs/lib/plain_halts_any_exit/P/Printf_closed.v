(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim Monad PrintfModel PrintfFormats Stdio Driver.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_printf_iface Printf_stdio_iface F_stdio_write F_stdout_write.

Module F_fwritex_stderr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_printf_iface Printf_stdio_iface F_fwritex_gen.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_printf_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_fwritex_gen.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_fwritex.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia_nd := first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia | lia ].
Import ListNotations.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Open Scope Z_scope.

Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma zb_length : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.

Theorem fwritex_stderr_proof : (forall St : Type, @stdio_write_stmt St) -> fwritex_stderr_stmt.
Proof.
  intros stdio_write_spec.
  unfold fwritex_stderr_stmt, out_stmt. intros St B. intros until canary.
  intros SINK SRC BYT BSL -> -> ST LO GLO SPHI TOP SSP MI SEPF SEPB SEPS1 SEPS2 SEPS3.
  destruct st as [buf st].
  destruct SINK as (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BGLO). cbn [fst] in FC, BUF, LEN.
  unfold OUT_DEPTH, GLOBALS_TOP, INTERNAL_BUFSIZ in *.
  destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length in BS.
  assert (LSB : length (zb bs) = length bs) by apply zb_length.
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0.
  assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
  assert (LR : 0 <= zlength rest) by (unfold zlength; lia).
  assert (LS : 0 <= zlength bs) by (unfold zlength; lia).
  unfold zlength in *.
  set (S := bv_unsigned a0) in *.
  assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
  pose proof BUF as BUF0.
  apply (rw_cells_split_CB psegs _ _ [] 80 (zb buf ++ rest) [] [length buf; 80 - length buf]%nat) in BUF; [| cbn; unfold zlength in *; lia].
  cbn [mk_CB_cells app] in BUF.
  rewrite firstn_app, zb_length, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in BUF by (rewrite zb_length; lia).
  rewrite skipn_app, zb_length, Nat.sub_diag, skipn_O, skipn_all2 in BUF by (rewrite zb_length; lia). cbn [app] in BUF.
  apply (proj1 (F_fwritex.rw_cells_app psegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUFb].
  cbn [cells_size csize Nat.add] in BUFb. rewrite Nat.add_0_r in BUFb. rewrite ?firstn_all2 in BUFb by lia.
  unfold implM, OUT_stderr.
  destruct (Z.ltb_spec0 OUT_MAX (zlength bs)) as [BIG|SMALL]; [apply impl_ret_unr|]. unfold OUT_MAX, zlength in SMALL.
  destruct (80 - zlength buf <? zlength bs) eqn:CMP.
  -
    pose proof (proj1 (Z.ltb_lt _ _) CMP) as CMP'. unfold zlength in CMP'.
    eapply impl_evt.
    { eapply fwx_nofit with (lo := lo); [exact FC | exact EA0 | reflexivity | reflexivity | lia | lia | unfold zlength in *; lia | lia | lia | reflexivity | exact ST | lia | lia | exact MI | lia]. }
    cbv beta. intros ms1 PO.
    destruct PO as (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1).
    unfold file_cells in FC.
    transport_after_call psegs m m1 MU1 WM1.
    unfold INTERNAL_BUFSIZ. cbv beta iota zeta. match goal with |- context [if ?c then _ else _] => replace c with true by (symmetry; exact CMP) end. cbv beta iota zeta.
    eapply impl_ebind.
    { eapply (stdio_write_spec St) with (B := B) (fd := 2) (Fp := 172352) (buf := buf) (s := bs) (S := S) (lo := lo) (canary := canary)
        (wend := B + 80) (bufsize := 80) (mode := mode) (lbf := 0xffffffff) (tail := tail) (flags := flags) (wfn := F_STDIO_WRITE);
        try reflexivity.
      - exact FC.
      - apply (bytes_at_ext _ _ _ _ _ (rw_cells_bytes_at _ _ _ _ BUFa)). cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
      - exact SRC.
      - lia.
      - exact ST1.
      - unfold STDIO_WRITE_DEPTH. lia.
      - unfold GLOBALS_TOP. lia.
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
      - right. unfold zlength. lia.
      - unfold zlength. lia. }
    cbv beta. intros [[] st'] ms' PO. cbn [fst snd] in PO.
    destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
    unfold STDIO_WRITE_DEPTH in MU2.
    apply impl_ret_ok. cbn [fst snd]. apply evt_done.
    pose proof (rw_cells_transport psegs _ m1 m2 _ _ BUF0 MU2 WM2 ltac:(cbn; lia)) as BUF2.
    pose proof (bytes_at_transport psegs _ m1 m2 _ _ SRC MU2 ltac:(cbn; rewrite LSB; lia)) as SRC2.
    unfold out_post, SR. do 16 eexists. split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m2).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia_nd.
             - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia_nd. }
    split; [eapply wmono_trans; [exact WM1 | exact WM2] |]. split; [exact MI2|]. split; [exact ST2|].
    split.
    {
      exists flags, mode, tail, (zb buf ++ rest). cbn [fst].
      split; [rewrite Z.add_0_r; exact FC2|]. split; [exact FL32|]. split; [exact FL8|].
      split; [exact BUF2|]. split; [| split; [exact BHI| exact BGLO]].
      unfold zlength. cbn [length]. rewrite length_app, zb_length. lia. }
    split; [exact SSP2 | exact SRC2].
  -
    pose proof (proj1 (Z.ltb_ge _ _) CMP) as CMP'. unfold zlength in CMP'.
    cbv beta iota zeta. match goal with |- context [if ?c then _ else _] => replace c with false by (symmetry; exact CMP) end. cbv beta iota zeta.
    apply impl_ret_ok. cbn [fst snd].
    unfold file_cells in FC.
    eapply evt_mono.
    { eapply (fwx_fit_plain ra sp gp tp t0 t1 t2 s0 s1 a0) with (lo := lo) (cap := (80 - length buf)%nat) (src := zb bs) (S := S)
        (Fp := 172352) (wend := B + 80) (wpos := B + Z.of_nat (length buf)) (junk := rest);
        [ exact FC | exact BUFb | lia | exact SRC | rewrite LSB; reflexivity | exact EA0 | reflexivity | reflexivity | try lia .. ];
        [exact ST | exact MI].
    }
    cbv beta. intros ms' PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & DST2 & SRC2).
    unfold out_post, SR. do 16 eexists.
    split. { reflexivity. }
    split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia_nd. }
    split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
    assert (GOT2 : rw_cells psegs m2 168192 [C8 (Z_to_bv 64 370424)]).
    { eapply (rw_cells_transport psegs _ m m2); [exact GOT | exact MU2 | exact WM2 | cbn; lia]. }
    assert (GUARD2 : rw_cells psegs m2 370424 [C8 canary]).
    { eapply (rw_cells_transport psegs _ m m2); [exact GUARD | exact MU2 | exact WM2 | cbn; lia]. }
    assert (BUFa2 : rw_cells psegs m2 B [CB (length buf) (zb buf)]).
    { eapply (rw_cells_transport psegs _ m m2); [exact BUFa | exact MU2 | exact WM2 | cbn; lia]. }
    split.
    {
      exists flags, mode, tail, (skipn (length (zb bs)) rest). cbn [fst].
      split. { unfold zlength. rewrite length_app, Nat2Z.inj_add, Z.add_assoc. exact FC2. }
      split; [exact FL32|]. split; [exact FL8|].
      split.
      {
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
End F_fwritex_stderr.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_fwritex_stdout.

Module F_stdio_flush.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_printf_iface Printf_stdio_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_printf_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Printf_stdio_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.

Theorem stdio_write_flush_proof : (forall St : Type, @stdio_write_stmt St) -> stdio_write_flush_stmt.
Proof.
  intros stdio_write_spec.
  unfold stdio_write_flush_stmt. intros until canary. intros SINK -> -> -> ST LO GLO SPHI SEPB SSP MI.
  destruct SINK as (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BGLO). cbn [fst] in FC, BUF, LEN.
  unfold OUT_DEPTH, GLOBALS_TOP in *.
  pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
  assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
  assert (LR : 0 <= zlength rest) by (unfold zlength; lia).
  pose proof (rw_cells_bytes_at _ _ _ _ BUF) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
  apply bytes_at_app in BY as [BY _].
  eapply implM_mono.
  { eapply (stdio_write_spec St) with (B := B) (fd := 2) (Fp := RSTDERR) (buf := buf) (s := []) (S := 0) (lo := lo) (canary := canary)
      (wend := B + 80) (bufsize := 80) (mode := mode) (lbf := 0xffffffff) (tail := tail) (flags := flags) (wfn := F_STDIO_WRITE);
      try reflexivity; try lia.
    - exact FC.
    - exact BY.
    - apply bytes_at_nil. unfold zlength; cbn [length]. lia.
    - exact ST.
    - unfold STDIO_WRITE_DEPTH. lia.
    - unfold GLOBALS_TOP. lia.
    - exact SSP.
    - exact MI.
    - unfold got_ssp. lia.
    - unfold ssp_guard. lia.
    - unfold zlength in *; cbn [length]. lia.
    - unfold zlength; cbn [length]. lia.
    - left. reflexivity. }
  cbv beta. intros [] st' ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & FC' & SSP' & ->).
  unfold STDIO_WRITE_DEPTH in MU.
  unfold stdio_write_flush_post. do 16 eexists. split; [reflexivity|].
  split. { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. unfold STDIO_WRITE_DEPTH in *. intros; lia. }
  split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [| exact SSP'].
  exists flags, mode, tail, (zb buf ++ rest). cbn [fst].
  split. { rewrite Z.add_0_r. exact FC'. }
  split; [exact FL32|]. split; [exact FL8|].
  split.
  {
    eapply (rw_cells_transport _ _ m m'); [exact BUF | exact MU | exact WM |].
    cbn. unfold zlength in *. lia. }
  split; [| split; [exact BHI| exact BGLO]]. unfold zlength in *. cbn [length]. rewrite length_app. unfold zb. rewrite length_map. lia.
Qed.
End F_stdio_flush.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_fprintf.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_fprintf.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_printf_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_stdio_write OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_stdout_write OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Printf_closed.F_fwritex_stderr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_fwritex_stdout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Printf_closed.F_stdio_flush OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_fprintf.F_vfprintf_stdout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_fprintf.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Printf_stdio_iface F_vsnprintf.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_fprintf.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_fprintf.
Export OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_vsnprintf OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_fprintf.F_vfprintf_stdout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_fprintf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma fwritex_stderr_ok : fwritex_stderr_stmt.
Proof. apply fwritex_stderr_proof. intros St. apply (@stdio_write_proof St). Qed.

Lemma stdio_write_flush_ok : stdio_write_flush_stmt.
Proof. apply stdio_write_flush_proof. intros St. apply (@stdio_write_proof St). Qed.

Lemma fwritex_stdout_ok : fwritex_stdout_stmt.
Proof. apply fwritex_stdout_proof. intros St get_so set_so GS SS. apply (stdout_writefn_proof get_so set_so GS SS). Qed.

Section Closed.
  Context {St : Type}.

  Lemma vfprintf_stderr_ok : vfprintf_stderr_stmt (St:=St).
  Proof. exact (vfprintf_stderr_proof fwritex_stderr_ok stdio_write_flush_ok). Qed.

  Lemma fprintf_gen_ok : fprintf_gen_stmt (St:=St).
  Proof. exact (fprintf_gen_proof fwritex_stderr_ok stdio_write_flush_ok). Qed.

  Lemma fprintf_diag_ok :
    forall (d : diag_msg)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (lo : Z) (canary : word),
      stderr_wfile m ->
      a0 = Z_to_bv 64 RSTDERR -> diag_args d m a1 a2 lo (bv_unsigned sp) ->
      stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) ->
      ssp_cells m canary -> mem_inv psegs m -> frm0 fc ->
      Monad.implM psegs (s_diag (St:=St) d) st
            (fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x22448) fc None m (seg_rom psegs)).
  Proof. intros. eapply (fprintf_diag_proof St); eauto using fwritex_stderr_ok, stdio_write_flush_ok. Qed.

  Context (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis GS : forall x so, get_so (set_so so x) = so.
  Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.

  Lemma vfprintf_stdout_ok : vfprintf_stdout_stmt get_so set_so.
  Proof. exact (vfprintf_stdout_proof get_so set_so GS SS fwritex_stdout_ok). Qed.

  Lemma emit_printf_ok :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (lo : Z) (canary : word),
      stdout_file m (get_so st) ->
      bv_unsigned a1 mod 2^32 = 0 ->
      stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - EMIT_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) ->
      ssp_cells m canary -> mem_inv psegs m -> frm0 fc ->
      Monad.implM psegs (stdout_vprintf get_so set_so pieces_emit_0) st
            (emit_printf_post get_so ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15da0) fc None m (seg_rom psegs)).
  Proof. intros. eapply (emit_printf_proof St get_so set_so); eauto using fwritex_stdout_ok. Qed.
End Closed.
