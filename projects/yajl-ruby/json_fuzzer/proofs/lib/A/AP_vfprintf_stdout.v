(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 AImages ITreeA MonadA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit AM_monadx AM_syscalls AM_memset AM_memcpy AM_stdio_lib AX_file AM_fwrite AP_policy AP_mjx AP_fwritex AP_fwritex_gen AP_pop_arg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model Printf_mlib Printf_pieces.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AP_printf_iface AP_mlibA AP_piecesA AP_printf_core AP_vfprintf AP_fwritex_stdout.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evtA _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section StdoutSinkProofs.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Let SINK := SINK_stdout (St:=St) get_so.

  Lemma stdout_sink_frame : sink_frame_stmt RSTDOUT RSTDOUT_BUF 1024 SINK.
  Proof using get_so.
    unfold sink_frame_stmt. intros W m m' st (ACT & flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN & MJ) MU WM D1 D2 D3.
    split; [exact ACT|]. exists flags, mode, tail, bufbytes.
    split; [|split; [exact FL | split; [| split; [exact PFX | split; [exact LEN|]]]]].
    - eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
    - eapply mjx_transport; [exact MJ | exact MU | exact WM | exact D3].
  Qed.

  Lemma stdout_sink_flags : sink_flags_stmt RSTDOUT SINK.
  Proof using get_so.
    unfold sink_flags_stmt. intros m st (ACT & flags & mode & tail & bufbytes & FC & FL & _).
    exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|].
    rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned flags)) with ((bv_unsigned flags) mod 2^8).
    rewrite <- land_mod_low by lia. eapply land_sub_mask; [|exact FL]. reflexivity.
  Qed.

  Lemma stdout_sink_mjx : sink_mjx_stmt SINK.
  Proof using . unfold sink_mjx_stmt. intros m st (ACT & flags & mode & tail & bufbytes & H). tauto. Qed.
End StdoutSinkProofs.

Lemma topok_stk_hi' : topok_hi_stmt TOPOK_stk.
Proof. unfold topok_hi_stmt, TOPOK_stk. intros; assumption. Qed.

Lemma implMA_upd_l {St B} (P : acc -> Prop) : forall (f : St -> St) (k : unit -> M St B) s Q ms,
  implMA asegs P (k tt) (f s) Q ms -> implMA asegs P (mbind (mupd f) k) s Q ms.
Proof. intros. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stdout.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Variable P : acc -> Prop.
  Hypothesis PSTK : POL_STACK P.
  Hypothesis PIMG : POL_IMG P.
  Hypothesis PHSH : POL_HSH P.
  Hypothesis PLSH : POL_LSH P.
  Hypothesis PNUL : POL_NUL P.
  Hypothesis GS : forall x so, get_so (set_so so x) = so.
  Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.
  Hypothesis FWX : fwritex_stdout_stmt P.

  Let OUT := stdout_fwritex get_so set_so.
  Let SINK := SINK_stdout (St:=St) get_so.

  Definition vfprintf_stdout_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ stdout_file m' (get_so st')
      /\ ssp_cells m' canary
      /\ mjx m'.

  Definition vfprintf_stdout_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
           (lo : Z) (canary : word),
      let q := bv_unsigned sp in
      a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
      stdout_file m (get_so st) ->
      bytes_at asegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      va_area m VA slots -> args_ok RSTDOUT RSTDOUT_BUF 1024 m lo q (q - VF_FRAME) slots args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] -> sp_ok (length fmt) fmt args ->
      stk asegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) -> (q <= A_STK_HI) ->
      ssp_cells m canary -> mem_inv asegs m -> frm0 fc -> mjx m ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      (q <= VA) -> (VA + 8 * zlength slots <= A_STK_HI) ->
      implMA asegs P (stdout_towrite get_so set_so ;;; outsk OUT ps (mret tt)) st
        (vfprintf_stdout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x98008) fc None m (seg_rom asegs)).

  Lemma vfp_stdout_active :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    forall (F : bvmap 5 word),
    forall (fc : bv 32),
    forall (m : mem),
    forall (st : St),
    forall (A VA : Z),
    forall (fmt : list Z),
    forall (slots : list word),
    forall (args : list parg),
    forall (ps : list (list Z)),
    forall (r lo : Z),
    forall (canary flags mode : word),
    forall (tail bufbytes : list byte),
    forall (m0 : mem),
    (Z.land (bv_unsigned flags) 72 = 0) ->
    forall (m1 : mem),
    (rw_cells asegs m1 6296096 [CB 1024 bufbytes]) ->
    (firstn (length (so_buf (get_so st))) bufbytes = to_bytes (so_buf (get_so st))) ->
    (zlength (so_buf (get_so st)) <= 1024) ->
    (so_active (get_so st) = true) ->
    (true = false -> so_buf (get_so st) = []) ->
    (bytes_at asegs m1 A (zb fmt)) ->
    (Forall (fun c : Z => 0 <= c < 256) fmt) ->
    (pass1_ok fmt = true) ->
    (bytes_at asegs m1 VA (u64s slots)) ->
    (args_ok 692600 6296096 1024 m lo (bv_unsigned sp) (bv_unsigned sp + -368) slots args) ->
    (printf_pieces fmt args = Some (ps, r)) ->
    (fp_calls (length fmt) fmt args = []) ->
    (sp_ok (length fmt) fmt args) ->
    (lo <= bv_unsigned sp - 5552) ->
    ((Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo) ->
    (bv_unsigned sp < 2 ^ 63) ->
    (bv_unsigned sp <= 140737488355328) ->
    (frm0 fc) ->
    (mjx m) ->
    (65536 <= A) ->
    (A + Z.of_nat (length fmt) <= 135168) ->
    (bv_unsigned sp <= VA) ->
    (VA + 8 * Z.of_nat (length slots) <= 140737488355328) ->
    (0 <= bv_unsigned sp < 2 ^ 64) ->
    (0 <= A /\ A + Z.of_nat (length fmt) <= 2 ^ 64) ->
    (length (zb fmt) = length fmt) ->
    (length (u64s slots) = (8 * length slots)%nat) ->
    (munch [(lo, bv_unsigned sp); (692600, 692600 + 232); (6296096, 6296096 + 1024)] m m1) ->
    (wmono asegs m m1) ->
    (munch [(lo, bv_unsigned sp); (692600, 692600 + 232)] m m1) ->
    (length bufbytes = 1024%nat) ->
    forall (junk : list byte),
    (rw_cells asegs m1 (bv_unsigned sp + -368) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 248 (firstn 248 (firstn 280 (skipn 16 (firstn 304 (firstn 312 (firstn 320 (firstn 328 (firstn 336 (firstn 344 (firstn 352 (firstn 360 junk))))))))))); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
    forall (x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 : word),
    (mem_inv asegs m1) ->
    (stk asegs m1 lo (bv_unsigned sp + -368)) ->
    (rw_cells asegs m1 677432 [C8 (Z_to_bv 64 6294352)]) ->
    (rw_cells asegs m1 6294352 [C8 canary]) ->
    (rw_cells asegs m1 692600 [C4 (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 619384); C8 (Z_to_bv 64 (6296096 + 1024)); C8 (Z_to_bv 64 (6296096 + zlength (so_buf (get_so st)))); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 6296096); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (if so_first (get_so st) then 622280 else 619716)); C8 (Z_to_bv 64 619708); C8 (Z_to_bv 64 6296096); C8 (Z_to_bv 64 1024); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 (if so_lbf_nl (get_so st) then 10 else 4294967295)); C4 (Z_to_bv 64 0); CB 80 tail]) ->
    evtA asegs P (fun ms' : machine_state => implA asegs (NodesA.at_nodeA asegs) P ((printf_model OUT OUTFP_stdout fmt args;;; mret ()) (set_so (get_so st) st)) (epost (fun p : () * St => vfprintf_stdout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m p.1 p.2)) ms') (MS (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some b5) TEmpty) (Some x7) (TNode TEmpty (Some s7) TEmpty)) (Some gp) (TNode (TNode TEmpty (Some (Z_to_bv 64 1)) TEmpty) (Some (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) (TNode TEmpty (Some s11) TEmpty))) (Some (Z_to_bv 64 622704)) (TNode (TNode (TNode TEmpty (Some b7) TEmpty) (Some (Z_to_bv 64 A)) (TNode TEmpty (Some s9) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some (sx32 flags)) TEmpty) (Some b3) (TNode TEmpty (Some x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some b6) TEmpty) (Some (Z_to_bv 64 692600)) (TNode TEmpty (Some s8) TEmpty)) (Some tp) (TNode (TNode TEmpty (Some (Z_to_bv 64 0)) TEmpty) (Some b2) (TNode TEmpty (Some x28) TEmpty))) (Some (Z_to_bv 64 (bv_unsigned sp + -368))) (TNode (TNode (TNode TEmpty (Some (Z_to_bv 64 6294352)) TEmpty) (Some (Z_to_bv 64 6297120)) (TNode TEmpty (Some s10) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some s6) TEmpty) (Some b4) (TNode TEmpty (Some x30) TEmpty))))) F (if negb (bv_eqb (Z_to_bv 64 6297120) (Z_to_bv 64 0)) then Z_to_bv 64 622840 else Z_to_bv 64 622776) fc None m1 (seg_rom asegs)).
  Proof using FWX GS SS PSTK PIMG PHSH PLSH PNUL.
    intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st A VA fmt slots args ps r lo canary flags mode tail bufbytes m0 FL72 m1 BUF PFX BLEN ACT INACT BY HF P1 VAA AOK PP FPC SPOK LO GLO QHI SPTOP FRM MJ0 HA0 HA QVA VAHI Rq AB LZB LU MU WM MU1 LBB junk FR x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 MIc STc SSP1 SSP2 FC.
    (* [comment removed for export] *)
    if_lit. cbv beta iota in FC.
    zs. zs. zs. zs. zs. zs.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
    replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
    ileave.
    pose proof (printf_core_proof St P RSTDOUT RSTDOUT_BUF 1024 SINK TOPOK_stk OUT (OUTFP_stdout (St:=St))
                  PSTK PIMG PHSH PLSH PNUL (stdout_sink_frame get_so) (stdout_sink_flags get_so) (stdout_sink_mjx get_so) topok_stk topok_stk_hi' (FWX St get_so set_so GS SS)) as PC2.
    unfold printf_core_stmt in PC2.
    assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
    { rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
      pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    lazymatch goal with |- implMA _ _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (MJ2 : mjx mm) by (eapply mjx_transport; [exact MJ0 | exact MU | exact WM |];
        unfold mjx_ok_iv, A_CEIL, A_STK_HI; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil) end.
    eapply implMA_bind.
    { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
        clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_stk, A_STK_HI, zlength.
      all: try lia.
      1:{ unfold SINK, SINK_stdout. rewrite GS, ACT. split; [reflexivity|].
          exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode, tail, bufbytes.
          split; [unfold file_cells; exact FC|]. split; [exact FL'|]. split; [exact BUF|]. split; [exact PFX |]. split; [exact BLEN | exact MJ2]. }
      all: first [ exact BY | exact HF | reflexivity | replace (VA + 8 * 0) with VA by lia; exact APC | exact VAA
                 | cbn [skipn Z.to_nat]; eapply args_ok_vf; [exact AOK | lia | exact MU1]
                 | rewrite FPC; apply Forall_nil | exact SPOK | exact STc
                 | split; [exact SSP1 | exact SSP2] | exact FRM | assumption ]. }
    cbv beta. intros r' st' ms' PO. clear PC2 MU1.
    unfold printf_core_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
    unfold SR in MUc. cbn [app] in MUc.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
    apply implMA_ret. fix_ret.
    destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3 & MJ3). unfold file_cells in FC3.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [asegs] in SSP1, SSP2. fold asegs in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. zs. zs. if_lit.
    zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    (* [comment removed for export] *)
    replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
      by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
    change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
    rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.
    (* [comment removed for export] *)
    lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
      assert (FALL : rw_cells asegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
      [ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
      | clear AP FR ] end.
    cbn [app] in FALL.
    release_frame FALL ST3 (bv_unsigned sp).
    apply evtA_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST3|].
    split.
    { exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode2, tail2, bufbytes2.
      rewrite ACT3. split; [unfold file_cells; exact FC3|].
      split; [| split; [exact BUF3 | split; [exact PFX3 | split; [exact BLEN3 | intros; discriminate]]]].
      rewrite unsigned_lit; [apply flags_olderr_72; exact FL3|].
      pose proof (bv_unsigned_in_range 64 (sx32 flags2)) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2.
      unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R1, R2.
      pose proof (Z_land_range (bv_unsigned (sx32 flags)) 32).
      split; [apply Z.lor_nonneg; lia|].
      apply (lor_lt_pow2 _ _ 64); lia. }
    split; [split; [exact SSP1 | exact SSP2]|].
    eapply mjx_transport; [exact MJ0 | exact MU | exact WM |].
    unfold mjx_ok_iv, A_CEIL, A_STK_HI; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil.
  Qed.

  Lemma vfp_stdout_inactive :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    forall (F : bvmap 5 word),
    forall (fc : bv 32),
    forall (m : mem),
    forall (st : St),
    forall (A VA : Z),
    forall (fmt : list Z),
    forall (slots : list word),
    forall (args : list parg),
    forall (ps : list (list Z)),
    forall (r lo : Z),
    forall (canary flags mode : word),
    forall (tail bufbytes : list byte),
    forall (m0 : mem),
    (Z.land (bv_unsigned flags) 72 = 0) ->
    forall (m1 : mem),
    (rw_cells asegs m1 6296096 [CB 1024 bufbytes]) ->
    (firstn (length (so_buf (get_so st))) bufbytes = to_bytes (so_buf (get_so st))) ->
    (zlength (so_buf (get_so st)) <= 1024) ->
    (so_active (get_so st) = false) ->
    (false = false -> so_buf (get_so st) = []) ->
    (bytes_at asegs m1 A (zb fmt)) ->
    (Forall (fun c : Z => 0 <= c < 256) fmt) ->
    (pass1_ok fmt = true) ->
    (bytes_at asegs m1 VA (u64s slots)) ->
    (args_ok 692600 6296096 1024 m lo (bv_unsigned sp) (bv_unsigned sp + -368) slots args) ->
    (printf_pieces fmt args = Some (ps, r)) ->
    (fp_calls (length fmt) fmt args = []) ->
    (sp_ok (length fmt) fmt args) ->
    (lo <= bv_unsigned sp - 5552) ->
    ((Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo) ->
    (bv_unsigned sp < 2 ^ 63) ->
    (bv_unsigned sp <= 140737488355328) ->
    (frm0 fc) ->
    (mjx m) ->
    (65536 <= A) ->
    (A + Z.of_nat (length fmt) <= 135168) ->
    (bv_unsigned sp <= VA) ->
    (VA + 8 * Z.of_nat (length slots) <= 140737488355328) ->
    (0 <= bv_unsigned sp < 2 ^ 64) ->
    (0 <= A /\ A + Z.of_nat (length fmt) <= 2 ^ 64) ->
    (length (zb fmt) = length fmt) ->
    (length (u64s slots) = (8 * length slots)%nat) ->
    (munch [(lo, bv_unsigned sp); (692600, 692600 + 232); (6296096, 6296096 + 1024)] m m1) ->
    (wmono asegs m m1) ->
    (munch [(lo, bv_unsigned sp); (692600, 692600 + 232)] m m1) ->
    (length bufbytes = 1024%nat) ->
    forall (junk : list byte),
    (rw_cells asegs m1 (bv_unsigned sp + -368) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 248 (firstn 248 (firstn 280 (skipn 16 (firstn 304 (firstn 312 (firstn 320 (firstn 328 (firstn 336 (firstn 344 (firstn 352 (firstn 360 junk))))))))))); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
    forall (x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 : word),
    (mem_inv asegs m1) ->
    (stk asegs m1 lo (bv_unsigned sp + -368)) ->
    (rw_cells asegs m1 677432 [C8 (Z_to_bv 64 6294352)]) ->
    (rw_cells asegs m1 6294352 [C8 canary]) ->
    (rw_cells asegs m1 692600 [C4 (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 619384); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (if so_first (get_so st) then 622280 else 619716)); C8 (Z_to_bv 64 619708); C8 (Z_to_bv 64 6296096); C8 (Z_to_bv 64 1024); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 (if so_lbf_nl (get_so st) then 10 else 4294967295)); C4 (Z_to_bv 64 0); CB 80 tail]) ->
    evtA asegs P (fun ms' : machine_state => implA asegs (NodesA.at_nodeA asegs) P ((printf_model OUT OUTFP_stdout fmt args;;; mret ()) (set_so {| so_active := true; so_buf := []; so_lbf_nl := so_lbf_nl (get_so st); so_first := so_first (get_so st) |} st)) (epost (fun p : () * St => vfprintf_stdout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m p.1 p.2)) ms') (MS (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some b5) TEmpty) (Some x7) (TNode TEmpty (Some s7) TEmpty)) (Some gp) (TNode (TNode TEmpty (Some (Z_to_bv 64 1)) TEmpty) (Some (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) (TNode TEmpty (Some s11) TEmpty))) (Some (Z_to_bv 64 622704)) (TNode (TNode (TNode TEmpty (Some b7) TEmpty) (Some (Z_to_bv 64 A)) (TNode TEmpty (Some s9) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some (sx32 flags)) TEmpty) (Some b3) (TNode TEmpty (Some x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some b6) TEmpty) (Some (Z_to_bv 64 692600)) (TNode TEmpty (Some s8) TEmpty)) (Some tp) (TNode (TNode TEmpty (Some (Z_to_bv 64 0)) TEmpty) (Some b2) (TNode TEmpty (Some x28) TEmpty))) (Some (Z_to_bv 64 (bv_unsigned sp + -368))) (TNode (TNode (TNode TEmpty (Some (Z_to_bv 64 6294352)) TEmpty) (Some (Z_to_bv 64 0)) (TNode TEmpty (Some s10) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some s6) TEmpty) (Some b4) (TNode TEmpty (Some x30) TEmpty))))) F (if negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) then Z_to_bv 64 622840 else Z_to_bv 64 622776) fc None m1 (seg_rom asegs)).
  Proof using FWX GS SS PSTK PIMG PHSH PLSH PNUL.
    intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st A VA fmt slots args ps r lo canary flags mode tail bufbytes m0 FL72 m1 BUF PFX BLEN ACT INACT BY HF P1 VAA AOK PP FPC SPOK LO GLO QHI SPTOP FRM MJ0 HA0 HA QVA VAHI Rq AB LZB LU MU WM MU1 LBB junk FR x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 MIc STc SSP1 SSP2 FC.
    (* [comment removed for export] *)
    if_lit. cbv beta iota in FC. zs. zs. zs.
    pose proof towrite_proof as TW. unfold towrite_stmt in TW.
    eapply evtA_cut.
    { eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ intros a k H1 H2; apply PIMG; lia | exact FC | | lia | lia | lia | assumption ].
      rewrite unsigned_lit; [apply flags_noerr_nowr; exact FL72|].
      pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    cbv beta. intros ms' PO. clear TW.
    destruct PO as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt).
    rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
    fix_ret.
    zs. if_lit. zs. zs. zs. zs. zs. zs.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
    replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
    ileave.
    pose proof (printf_core_proof St P RSTDOUT RSTDOUT_BUF 1024 SINK TOPOK_stk OUT (OUTFP_stdout (St:=St))
                  PSTK PIMG PHSH PLSH PNUL (stdout_sink_frame get_so) (stdout_sink_flags get_so) (stdout_sink_mjx get_so) topok_stk topok_stk_hi' (FWX St get_so set_so GS SS)) as PC2.
    unfold printf_core_stmt in PC2.
    assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
    { rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
      pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    lazymatch goal with |- implMA _ _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (MJ2 : mjx mm) by (eapply mjx_transport; [exact MJ0 | exact MU | exact WM |];
        unfold mjx_ok_iv, A_CEIL, A_STK_HI; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil) end.
    eapply implMA_bind.
    { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
        clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_stk, A_STK_HI, zlength.
      all: try lia.
      1:{ unfold SINK, SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [reflexivity|].
          exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, bufbytes.
          change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
          split; [exact FCt|]. split; [exact FL'|]. split; [exact BUF|]. split; [reflexivity |]. split; [lia | exact MJ2]. }
      all: first [ exact BY | exact HF | reflexivity | replace (VA + 8 * 0) with VA by lia; exact APC | exact VAA
                 | cbn [skipn Z.to_nat]; eapply args_ok_vf; [exact AOK | lia | exact MU1]
                 | rewrite FPC; apply Forall_nil | exact SPOK | exact STc
                 | split; [exact SSP1 | exact SSP2] | exact FRM | assumption ]. }
    cbv beta. intros r' st' ms' PO. clear PC2 MU1.
    unfold printf_core_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
    unfold SR in MUc. cbn [app] in MUc.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
    apply implMA_ret. fix_ret.
    destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3 & MJ3). unfold file_cells in FC3.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [asegs] in SSP1, SSP2. fold asegs in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. zs. zs. if_lit.
    zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    (* [comment removed for export] *)
    replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
      by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
    change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
    rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.
    (* [comment removed for export] *)
    lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
      assert (FALL : rw_cells asegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
      [ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
      | clear AP FR ] end.
    cbn [app] in FALL.
    release_frame FALL ST3 (bv_unsigned sp).
    apply evtA_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST3|].
    split.
    { exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode2, tail2, bufbytes2.
      rewrite ACT3. split; [unfold file_cells; exact FC3|].
      split; [| split; [exact BUF3 | split; [exact PFX3 | split; [exact BLEN3 | intros; discriminate]]]].
      rewrite unsigned_lit; [apply flags_olderr_72; exact FL3|].
      pose proof (bv_unsigned_in_range 64 (sx32 flags2)) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2.
      unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R1, R2.
      pose proof (Z_land_range (bv_unsigned (sx32 flags)) 32).
      split; [apply Z.lor_nonneg; lia|].
      apply (lor_lt_pow2 _ _ 64); lia. }
    split; [split; [exact SSP1 | exact SSP2]|].
    eapply mjx_transport; [exact MJ0 | exact MU | exact WM |].
    unfold mjx_ok_iv, A_CEIL, A_STK_HI; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil.
  Qed.

  Theorem vfprintf_stdout_proof : vfprintf_stdout_stmt.
  Proof using FWX GS SS PSTK PIMG PHSH PLSH PNUL.
    unfold vfprintf_stdout_stmt. intros until canary. cbv zeta.
    intros -> -> -> SF BY HF P1 VAA AOK PP FPC SPOK ST LO GLO QHI SPTOP SSP MI FRM MJ0 HA0 HA QVA VAHI.
    unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, A_STK_HI in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
    pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [asegs] in SSP1, SSP2. fold asegs in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z m) as MU1.
    destruct SF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & PFX & BLEN & INACT). unfold file_cells in FC.
    pose proof (rw_CB_length _ _ _ _ BUF) as LBB.
    (* [comment removed for export] *)
    unfold stdout_towrite, upd_so. apply implMA_upd_l.
    apply (printf_model_outsA asegs P OUT (OUTFP_stdout (St:=St)) fmt args ps r (fun _ => mret tt) _ _ _ PP).
    ienter.
    carve_frame 368%nat ST.
    do 12 zs. do 14 zs.
    (* [comment removed for export] *)
    pose proof (printf_core1_proof P PSTK PIMG PHSH PLSH PNUL) as PC1. unfold printf_core1_stmt in PC1.
    eapply evtA_cut.
    { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, A_STK_HI, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | match goal with H : stk _ _ lo _ |- _ => exact H end | lia | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | exact FRM | lia | lia | lia | lia ]. }
    cbv beta. intros ms' PO. clear PC1. unfold printf_core1_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [asegs] in SSP1, SSP2. fold asegs in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit. zs. zs. zs.
    destruct (so_active (get_so st)) eqn:ACT.
    + eapply vfp_stdout_active; eassumption.
    + eapply vfp_stdout_inactive; eassumption.
  Qed.
End Stdout.
End RC__1.
