(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Lib Require Bytes PropExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import Stdio Driver HarnessC PState.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Common Require Import SFW1_lemmas.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Plain Require Import F_memset F_memcpy Stdio_kit F_syscalls StdioFiles.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Plain Require Import F_pop_arg.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Common Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Plain Require Import F_printf_iface F_printf_core F_vfprintf.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Common Require Import Printf_pieces Printf_fmts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Plain Require Import F_vfprintf_stdout Printf_bridge PImg Stdio_kit2 F_fprintf Stdio_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition PFPRINTF_fl : Z := 0x22750.
Definition A_FMT_zerr_fl : Z := 0x102f2.
Definition ZERR_MSGS : list (Z * list Z) :=
  [(0x1030b, HarnessC.MSG_DEFLATEEND); (0x10570, HarnessC.MSG_INFLATE); (0x103f9, HarnessC.MSG_INFLATESYNC)].

Definition IMG_deflateEnd : list Z := [100; 101; 102; 108; 97; 116; 101; 69; 110; 100; 0; 105; 110; 118; 97].
Definition IMG_inflate : list Z := [105; 110; 102; 108; 97; 116; 101; 0; 105; 110; 118; 97; 108; 105].
Definition IMG_inflateSync : list Z := [105; 110; 102; 108; 97; 116; 101; 83; 121; 110; 99; 0; 105; 110; 102].
Definition SLACK_deflateEnd : list byte := map (Z_to_bv 8) [105; 110; 118; 97].
Definition SLACK_inflate : list byte := map (Z_to_bv 8) [105; 110; 118; 97; 108; 105].
Definition SLACK_inflateSync : list byte := map (Z_to_bv 8) [105; 110; 102].

Definition zerr_len (msg : list Z) (e : Z) : Z := zlength msg + 8 + pct_d_conv_len e + 1.


Local Ltac ppz msg L L8 :=
  intros e He; unfold printf_pieces;
  change (Datatypes.length FMT_zerr) with 14%nat;
  ppl_step; change Printf_model.T_PTR with T_PTR; rewrite conv_pieces_s; [| lia | vm_compute; reflexivity];
  match goal with |- context [0 + zlength ?l] => change (0 + zlength l) with L end;
  ppl_step; ppl_step; change 10 with T_INT at 1;
  pose proof (zlength_nonneg' (dec_digits e)); pose proof (zlength_nonneg' (dec_digits (- e)));
  pose proof (dec_digits_length e); pose proof (dec_digits_length (- e));
  rewrite conv_pieces_d by (unfold INT_MAX in *; lia);
  rewrite (ppl_noargs_shift 11 [10; 0] (L8 + pct_d_conv_len e) [[10]] 1 ltac:(vm_compute; reflexivity))
    by (unfold pct_d_conv_len, INT_MAX in *; destruct (e =? 0); [lia|]; destruct (e <? 0); lia);
  unfold pieces_zerr, zerr_len, zconv_pieces, pct_d_conv_pieces, pct_d_conv_len; rewrite <- ?dec_digits_fmt_u;
  change (zlength msg) with L;
  destruct (e =? 0); [cbn -[zlength Z.add]; reflexivity|];
  destruct (e <? 0); cbn -[zlength Z.add dec_digits]; do 2 f_equal; lia.

Lemma printf_pieces_deflateEnd : forall e, -2^31 <= e < 2^31 ->
  printf_pieces FMT_zerr [PA_s MSG_DEFLATEEND; PA_i e] = Some (pieces_zerr MSG_DEFLATEEND e, zerr_len MSG_DEFLATEEND e).
Proof. ppz MSG_DEFLATEEND 10 18. Qed.
Lemma printf_pieces_inflate : forall e, -2^31 <= e < 2^31 ->
  printf_pieces FMT_zerr [PA_s MSG_INFLATE; PA_i e] = Some (pieces_zerr MSG_INFLATE e, zerr_len MSG_INFLATE e).
Proof. ppz MSG_INFLATE 7 15. Qed.
Lemma printf_pieces_inflateSync : forall e, -2^31 <= e < 2^31 ->
  printf_pieces FMT_zerr [PA_s MSG_INFLATESYNC; PA_i e] = Some (pieces_zerr MSG_INFLATESYNC e, zerr_len MSG_INFLATESYNC e).
Proof. ppz MSG_INFLATESYNC 11 19. Qed.

Lemma pass1_ok_zerr : pass1_ok FMT_zerr = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp_calls_zerr : forall msg e, fp_calls (Datatypes.length FMT_zerr) FMT_zerr [PA_s msg; PA_i e] = [].
Proof. intros msg e. reflexivity. Qed.

Section ZErrFl.
  Context {St : Type}.
  Definition fprintf_zerr_post_fl (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom psegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
      /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ stderr_wfile0 m'
      /\ ssp_cells m' canary
      /\ st' = st.
  Definition fprintf_zerr_stmt_fl (amsg : Z) (msg : list Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (e : Z) (lo : Z) (canary : word),
      fwritex_stderr_stmt -> stdio_write_flush_stmt ->
      stderr_wfile m ->
      a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A_FMT_zerr_fl -> a2 = Z_to_bv 64 amsg ->
      (-2^31 <= e < 2^31) -> bv_unsigned a3 mod 2^32 = e mod 2^32 ->
      stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^47) ->
      ssp_cells m canary -> mem_inv psegs m -> frm0 fc ->
      implM psegs (stderr_fprintf (HarnessC.pieces_zerr msg e) : M St unit) st
            (fprintf_zerr_post_fl ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 PFPRINTF_fl) fc None m (seg_rom psegs)).

  Lemma vf_to_zerr_post : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (st st' : St) ms,
    vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st' ms -> st' = st ->
    fprintf_zerr_post_fl ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt st' ms.
  Proof.
    intros until ms. intros (x5 & x6 & x7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & E & MU & WM & MI & FRM & FOK & ST & SF & SSP) Est.
    exists x5, x6, x7, b0, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, Ft, fc', m'.
    repeat (split; [assumption|]). split; [| split; [exact SSP| exact Est]].
    destruct SF as (flags & mode & tail & FC & FL). exists flags, mode, 0, 0, tail. split; [exact FC|]. split; [exact FL|]. split; [left; reflexivity| lia].
  Qed.

  Lemma fprintf_zerr_gen : forall (amsg : Z) (msg img : list Z) (slack : list byte),
    zb msg ++ Z_to_bv 8 0 :: slack = zb img -> ro_bytes_b psegs amsg (zb img) = true -> 0 < amsg -> amsg + zlength img <= 0x12000 ->
    Forall (fun c => 0 < c < 256) msg -> (- (amsg + zlength msg + 1)) mod 8 <= zlength slack -> zlength img = zlength msg + 1 + zlength slack ->
    (forall e, -2^31 <= e < 2^31 -> printf_pieces FMT_zerr [PA_s msg; PA_i e] = Some (pieces_zerr msg e, zerr_len msg e)) ->
    fprintf_zerr_stmt_fl amsg msg.
  Proof.
    intros amsg msg img slack Himg RB A0 AHI MSGB SLK LEN PP.
    unfold fprintf_zerr_stmt_fl. intros until canary. intros FWE FLS SF Ha0 Ha1 Ha2 He VA3 ST LO GLO QHI SSP MI FRM.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    unfold FPRINTF_DEPTH, GLOBALS_TOP, PFPRINTF_fl in *.
    assert (BR : forall ps, Monad.implM psegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
                              (fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
                              (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x22750) fc None m (seg_rom psegs)) ->
                 Monad.implM psegs (stderr_fprintf ps) st
                              (fprintf_zerr_post_fl ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
                              (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x22750) fc None m (seg_rom psegs))).
    { intros ps H. unfold stderr_fprintf, Monad.implM in *.
      eapply impl_epost_mono.
      - eapply (stderr_bridge psegs ps [] st (fun s' ms' => fprintf_zerr_post_fl ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt s' ms')).
        eapply impl_mono; [eapply (impl_tforall psegs (at_node psegs) _ _ _ _ (outsk_flush_leaves ps [] st)); exact H|].
        intros [|[[] [b s']]] ms' [H1 H2]; cbn in H1, H2 |- *; [exact I|]. eapply vf_to_zerr_post; [exact H1 | exact H2].
      - intros [[] s'] ms' H'. exact H'. }
    pose proof (@fprintf_gen_proof St FWE FLS) as FG. unfold fprintf_gen_stmt in FG. cbv zeta in FG. unfold VF_FRAME, FPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT in FG.
    apply BR; clear BR.
    pose proof (zlength_nonneg' msg) as L0. pose proof (zlength_nonneg' slack) as L1.
    assert (BY : bytes_at psegs m amsg (zb img)).
    { apply fmt_bytes_at; [exact MI | exact RB | lia | lia]. }
    eapply FG with (fmt := FMT_zerr) (args := [PA_s msg; PA_i e]) (A := A_FMT_zerr) (ps := pieces_zerr msg e) (r := zerr_len msg e); clear FG.
    all: try exact Ha0. all: try exact SF. all: try exact ST. all: try exact MI. all: try exact FRM.
    all: try (split; [exact (proj1 SSP) | exact (proj2 SSP)]).
    all: try lia.
    - exact Ha1.
    - apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_zerr; lia | vm_compute; discriminate].
    - apply forall_range_b; vm_compute; reflexivity.
    - exact pass1_ok_zerr.
    - cbn [args_ok arg_ok]. split; [| split; [split; [exact He| exact VA3]| exact I]].
      exists slack. subst a2. rewrite unsigned_lit by lia. rewrite Himg.
      split; [exact BY|]. split; [exact MSGB|]. lia.
    - apply PP; exact He.
    - apply fp_calls_zerr.
    - unfold A_FMT_zerr; lia.
    - unfold A_FMT_zerr. change (zlength FMT_zerr) with 14. lia.
  Qed.

  Theorem fprintf_zerr_deflateEnd : fprintf_zerr_stmt_fl 0x1030b MSG_DEFLATEEND.
  Proof.
    apply (fprintf_zerr_gen 0x1030b MSG_DEFLATEEND IMG_deflateEnd SLACK_deflateEnd).
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - lia.
    - vm_compute. discriminate.
    - unfold MSG_DEFLATEEND; cbn; repeat (constructor; [lia|]); apply Forall_nil.
    - vm_compute. discriminate.
    - vm_compute. reflexivity.
    - apply printf_pieces_deflateEnd.
  Qed.
  Theorem fprintf_zerr_inflate : fprintf_zerr_stmt_fl 0x10570 MSG_INFLATE.
  Proof.
    apply (fprintf_zerr_gen 0x10570 MSG_INFLATE IMG_inflate SLACK_inflate).
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - lia.
    - vm_compute. discriminate.
    - unfold MSG_INFLATE; cbn; repeat (constructor; [lia|]); apply Forall_nil.
    - vm_compute. discriminate.
    - vm_compute. reflexivity.
    - apply printf_pieces_inflate.
  Qed.
  Theorem fprintf_zerr_inflateSync : fprintf_zerr_stmt_fl 0x103f9 MSG_INFLATESYNC.
  Proof.
    apply (fprintf_zerr_gen 0x103f9 MSG_INFLATESYNC IMG_inflateSync SLACK_inflateSync).
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - lia.
    - vm_compute. discriminate.
    - unfold MSG_INFLATESYNC; cbn; repeat (constructor; [lia|]); apply Forall_nil.
    - vm_compute. discriminate.
    - vm_compute. reflexivity.
    - apply printf_pieces_inflateSync.
  Qed.

  Theorem fprintf_zerr_fl : forall amsg msg, In (amsg, msg) ZERR_MSGS -> fprintf_zerr_stmt_fl amsg msg.
  Proof.
    intros amsg msg H. cbn in H. destruct H as [E|[E|[E|[]]]]; injection E as <- <-.
    - apply fprintf_zerr_deflateEnd.
    - apply fprintf_zerr_inflate.
    - apply fprintf_zerr_inflateSync.
  Qed.
End ZErrFl.
