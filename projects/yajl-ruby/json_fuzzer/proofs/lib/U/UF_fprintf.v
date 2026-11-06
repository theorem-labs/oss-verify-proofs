(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio Driver.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UF_memset UF_memcpy UF_fwritex UF_pad.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RF_stdio_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UF_pop_arg U_Exit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UF_printf_iface UF_printf_core UF_vfprintf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_pieces.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UF_vfprintf_stdout.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_bridge.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.  (* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Export UF_fprintf1.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Stderr.
  Context {St : Type}.
  Hypothesis FWE : fwritex_stderr_stmt.
  Hypothesis FLS : stdio_write_flush_stmt.

  (* [comment removed for export] *)
  Local Notation vfprintf_stderr_post := (UF_fprintf1.vfprintf_stderr_post (St:=St)).
  Local Notation vfprintf_stderr_stmt := (UF_fprintf1.vfprintf_stderr_stmt (St:=St)).
  Local Notation vfp_stderr_after_prologue := (UF_fprintf1.vfp_stderr_after_prologue (St:=St) FWE FLS).

  Theorem vfprintf_stderr_proof : vfprintf_stderr_stmt.
  Proof using FLS FWE.
    unfold vfprintf_stderr_stmt. intros until canary. cbv zeta.
    intros -> -> -> SF BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI.
    unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
    pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [usegs] in SSP1, SSP2. fold usegs in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU1.
    destruct SF as (flags & mode & e & wend & tail & FC & FL40). unfold file_cells in FC.
    (* [comment removed for export] *)
    apply (printf_model_outs usegs OUT_stderr (OUTFP_stderr (St:=St)) fmt args ps r (fun _ => FLUSH_stderr) _ _ _ PP).
    match goal with |- Monad.implM _ _ _ ?Q _ => set (QQ := Q) end.
    ienter.
    carve_frame 368%nat ST.
    do 12 zs. do 14 zs.
    (* [comment removed for export] *)
    eapply vfp_stderr_after_prologue; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fprintf_gen_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (A : Z) (fmt : list Z) (args : list parg) (ps : list (list Z)) (r : Z) (lo : Z) (canary : word),
      let q := bv_unsigned sp in
      a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A ->
      stderr_wfile m ->
      bytes_at usegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      args_ok RSTDERR (q - 80 - 352) 80 m lo q (q - 80 - VF_FRAME) [a2; a3; a4; a5; a6; a7] args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk usegs m lo q -> (lo <= q - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 0x800000000000) ->
      ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      Monad.implM usegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
        (fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1a510) fc None m (seg_rom usegs)).

  Theorem fprintf_gen_proof : fprintf_gen_stmt.
  Proof using FLS FWE.
    unfold fprintf_gen_stmt. intros until canary. cbv zeta.
    intros -> -> SF BY HF P1 AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA.
    unfold FPRINTF_DEPTH, VF_FRAME, GLOBALS_TOP, STATIC_SPLIT in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [usegs] in SSP1, SSP2. fold usegs in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
    destruct SF as (flags & mode & e & wend & tail & FC & FL40). unfold file_cells in FC.
    match goal with |- Monad.implM _ _ _ ?Q _ => set (QQ := Q) end.
    ienter.
    carve_frame 80%nat ST.
    do 17 zs.
    apply (proj1 (rw_cells_app usegs _ _ [_;_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
    replace (bv_unsigned sp + -80 + Z.of_nat 32)%Z with (bv_unsigned sp + -48)%Z in VAC by lia.
    pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
    change (le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a2; a3; a4; a5; a6; a7]) in VAA.
    (* [comment removed for export] *)
    ileave.
    pose proof vfprintf_stderr_proof as VF. unfold vfprintf_stderr_stmt in VF. cbv zeta in VF.
    eapply implM_post_evt.
    { eapply VF with (A := A) (VA := bv_unsigned sp + -48) (fmt := fmt) (slots := [a2; a3; a4; a5; a6; a7]) (args := args) (lo := lo) (canary := canary);
        clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
      all: try reflexivity. all: try lia.
      - exists flags, mode, e, wend, tail. split; [unfold file_cells; exact FC | exact FL40].
      - exact BY.
      - exact HF.
      - exact P1.
      - exact VAA.
      - eapply args_ok_vf; [| | exact MU]; [|lia].
        replace (bv_unsigned sp + -80 - 352)%Z with (bv_unsigned sp - 80 - 352)%Z by lia.
        replace (bv_unsigned sp + -80 - 368)%Z with (bv_unsigned sp - 80 - 368)%Z by lia. exact AOK.
      - exact PP.
      - exact FPC.
      - exact ST.
      - split; [exact SSP1 | exact SSP2].
      - exact MI.
      - exact FRM. }
    cbv beta. intros [] [b4 st4] ms' P. clear VF MU1. cbn [snd] in P.
    unfold vfprintf_stderr_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    change usegs with usegs in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    zs. zs. zs. zs.
    lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?hd, VAC : rw_cells _ ?mm (bv_unsigned sp + -48)%Z ?rest |- _ =>
      assert (FALL : rw_cells usegs mm (bv_unsigned sp + -80) (hd ++ rest));
      [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
      | clear FR VAC ] end.
    cbn [app] in FALL.
    release_frame FALL ST3 (bv_unsigned sp).
    apply evt_done. subst QQ. cbn [fst snd]. unfold vfprintf_stderr_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST3|]. split; [exact SF3|]. split; [exact SSP1 | exact SSP2].
  Qed.
End Stderr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma forall_range_b : forall l, forallb (fun c => (0 <=? c) && (c <? 256))%bool l = true -> Forall (fun c => 0 <= c < 256) l.
Proof.
  intros l H. rewrite forallb_forall in H. apply Forall_forall. intros c Hc. specialize (H c Hc).
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma vf_to_diag_post : forall St ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (st st' : St) ms,
  vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st' ms -> st' = st ->
  fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt st' ms.
Proof.
  intros until ms. intros (x5 & x6 & x7 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & E & MU & WM & MI & FRM & FOK & ST & SF & SSP) Est.
  exists x5, x6, x7, a0, a1, a2, a3, a4, a5, a6, a7, x28, x29, x30, x31, Ft, fc', m'.
  repeat (split; [assumption|]). exact Est.
Qed.

Theorem fprintf_diag_proof : forall St : Type, @fprintf_diag_stmt St.
Proof.
  intros St. unfold fprintf_diag_stmt. intros d. intros until canary. intros FWE FLS SF Ha0 DA ST LO GLO QHI SSP MI FRM.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  unfold FPRINTF_DEPTH, GLOBALS_TOP in *.
  (* [comment removed for export] *)
  assert (BR : forall ps, Monad.implM usegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
                            (fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
                            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1a510) fc None m (seg_rom usegs)) ->
               Monad.implM usegs (stderr_fprintf ps) st
                            (fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
                            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1a510) fc None m (seg_rom usegs))).
  { intros ps H. unfold stderr_fprintf, Monad.implM in *.
    eapply impl_epost_mono.
    - eapply (stderr_bridge usegs ps [] st (fun s' ms' => fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt s' ms')).
      eapply impl_mono; [eapply (impl_tforall usegs (at_node usegs) _ _ _ _ (outsk_flush_leaves ps [] st)); exact H|].
      intros [|[[] [b s']]] ms' [H1 H2]; cbn in H1, H2 |- *; [exact I|]. eapply vf_to_diag_post; [exact H1 | exact H2].
    - intros [[] s'] ms' H'. exact H'. }
  pose proof (@fprintf_gen_proof St FWE FLS) as FG. unfold fprintf_gen_stmt in FG. cbv zeta in FG. unfold VF_FRAME, FPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT in FG.
  destruct d as [argv0 | path | path | | | |]; cbn [diag_args] in DA; try contradiction; unfold s_diag; apply BR; clear BR.
  - destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA). unfold GLOBALS_TOP in GA.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length argv0) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB. unfold zlength in *.
    eapply FG with (fmt := FMT_usage) (args := [PA_s argv0]) (A := A_FMT_usage); clear FG;
      first [ exact Ha0 | exact Ha1 | exact SF | exact ST | exact MI | exact FRM
            | apply printf_pieces_usage; unfold zlength, INT_MAX in *; lia
            | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_usage; lia | vm_compute; discriminate]
            | apply forall_range_b; vm_compute; reflexivity
            | cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; repeat (split; [first [exact BY | exact HF | exact SLK | lia] |]); lia
            | split; [exact (proj1 SSP) | exact (proj2 SSP)]
            | lia
            | reflexivity
            | vm_compute; discriminate ].
  - destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA). unfold GLOBALS_TOP in GA.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length path) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB. unfold zlength in *.
    eapply FG with (fmt := FMT_cannot_open) (args := [PA_s path]) (A := A_FMT_cannot_open); clear FG;
      first [ exact Ha0 | exact Ha1 | exact SF | exact ST | exact MI | exact FRM
            | apply printf_pieces_cannot_open; unfold zlength, INT_MAX in *; lia
            | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_cannot_open; lia | vm_compute; discriminate]
            | apply forall_range_b; vm_compute; reflexivity
            | cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; repeat (split; [first [exact BY | exact HF | exact SLK | lia] |]); lia
            | split; [exact (proj1 SSP) | exact (proj2 SSP)]
            | lia
            | reflexivity
            | vm_compute; discriminate ].
  - destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA). unfold GLOBALS_TOP in GA.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length path) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB. unfold zlength in *.
    eapply FG with (fmt := FMT_read_error) (args := [PA_s path]) (A := A_FMT_read_error); clear FG;
      first [ exact Ha0 | exact Ha1 | exact SF | exact ST | exact MI | exact FRM
            | apply printf_pieces_read_error; unfold zlength, INT_MAX in *; lia
            | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_read_error; lia | vm_compute; discriminate]
            | apply forall_range_b; vm_compute; reflexivity
            | cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; repeat (split; [first [exact BY | exact HF | exact SLK | lia] |]); lia
            | split; [exact (proj1 SSP) | exact (proj2 SSP)]
            | lia
            | reflexivity
            | vm_compute; discriminate ].
  - destruct DA as [Ha1 Hu]. pose proof (bv_unsigned_in_range 64 a2) as R2.
    eapply FG with (fmt := FMT_too_big) (args := [PA_u 67108864]) (A := A_FMT_too_big); clear FG;
      first [ exact Ha0 | exact Ha1 | exact SF | exact ST | exact MI | exact FRM
            | apply printf_pieces_too_big
            | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_too_big; lia | vm_compute; discriminate]
            | apply forall_range_b; vm_compute; reflexivity
            | cbn [args_ok arg_ok]; split; [split; [lia | exact Hu] | exact I]
            | split; [exact (proj1 SSP) | exact (proj2 SSP)]
            | lia
            | reflexivity
            | vm_compute; discriminate ].
Qed.
End RC__1.
