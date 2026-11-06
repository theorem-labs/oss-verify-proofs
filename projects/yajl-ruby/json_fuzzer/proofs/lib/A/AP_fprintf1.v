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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model Printf_mlib Printf_pieces Printf_bridge.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AP_printf_iface AP_mlibA AP_piecesA AP_printf_core AP_vfprintf AP_stdio_flush AP_fwritex_stderr.
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
Section StderrSinkProofs.
  Context {St : Type}.
  Variable B : Z.
  Let SINK := SINK_stderr (St:=St) B.

  Lemma stderr_sink_frame : sink_frame_stmt RSTDERR B 80 SINK.
  Proof using .
    unfold sink_frame_stmt. intros W m m' [buf st] (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BLO & BSTK & MJ) MU WM D1 D2 D3.
    exists flags, mode, tail, rest.
    split; [|split; [exact FL32 | split; [exact FL8 | split; [| split; [exact LEN | split; [exact BHI | split; [exact BLO | split; [exact BSTK|]]]]]]]].
    - eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
    - eapply mjx_transport; [exact MJ | exact MU | exact WM | exact D3].
  Qed.

  Lemma stderr_sink_flags : sink_flags_stmt RSTDERR SINK.
  Proof using B.
    unfold sink_flags_stmt. intros m [buf st] (flags & mode & tail & rest & FC & FL32 & _).
    exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|].
    rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned flags)) with ((bv_unsigned flags) mod 2^8).
    rewrite <- land_mod_low by lia. exact FL32.
  Qed.

  Lemma stderr_sink_mjx : sink_mjx_stmt SINK.
  Proof using . unfold sink_mjx_stmt. intros m [buf st] H. destruct H as (flags & mode & tail & rest & H). tauto. Qed.
End StderrSinkProofs.

Lemma topok_stk_hi : topok_hi_stmt TOPOK_stk.
Proof. unfold topok_hi_stmt, TOPOK_stk. intros; assumption. Qed.

(* [comment removed for export] *)
Lemma flags40_8 : forall f, Z.land f 40 = 0 -> Z.land f 8 = 0.
Proof. intros f. apply land_sub_mask. reflexivity. Qed.
Lemma flags40_32 : forall f, Z.land f 40 = 0 -> Z.land f 32 = 0.
Proof. intros f. apply land_sub_mask. reflexivity. Qed.
Lemma sflags_noerr_8 : forall (flags : word), Z.land (bv_unsigned flags) 40 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 8 = 0.
Proof.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 8) with 8.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. apply flags40_8. exact H.
Qed.
Lemma sflags_noerr_32 : forall (flags : word),
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 32 = 0.
Proof.
  intros flags. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 32) with 0. apply Z.land_0_r.
Qed.
Lemma sflags_olderr0 : forall (flags : word), Z.land (bv_unsigned flags) 40 = 0 -> Z.land (bv_unsigned (sx32 flags)) 32 = 0.
Proof. intros flags H. rewrite land_low7, sx32_mod128, <- land_low7 by lia. apply flags40_32. exact H. Qed.
Lemma sflags_final_40 : forall (flags2 : word), Z.land (bv_unsigned flags2) 32 = 0 -> Z.land (bv_unsigned flags2) 8 = 0 ->
  Z.land (Z.lor (bv_unsigned (sx32 flags2)) 0) 40 = 0.
Proof.
  intros flags2 H32 H8. rewrite Z.lor_0_r. rewrite land_low7, sx32_mod128, <- land_low7 by lia.
  replace 40 with (Z.lor 32 8) by reflexivity. rewrite Z.land_lor_distr_r, H32, H8. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stderr.
  Context {St : Type}.
  Variable P : acc -> Prop.
  Hypothesis PSTK : POL_STACK P.
  Hypothesis PIMG : POL_IMG P.
  Hypothesis PHSH : POL_HSH P.
  Hypothesis PLSH : POL_LSH P.
  Hypothesis PNUL : POL_NUL P.
  Hypothesis FWE : fwritex_stderr_stmt P.
  Hypothesis FLS : stdio_write_flush_stmt P.

  Definition vfprintf_stderr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : St -> machine_state -> Prop :=
    fun st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ stderr_wfile0 m'
      /\ ssp_cells m' canary
      /\ mjx m'.

  (* [comment removed for export] *)
  Definition vfprintf_stderr_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
           (lo : Z) (canary : word),
      let q := bv_unsigned sp in
      a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
      stderr_wfile m ->
      bytes_at asegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      va_area m VA slots -> args_ok RSTDERR (q - 352) 80 m lo q (q - VF_FRAME) slots args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] -> sp_ok (length fmt) fmt args ->
      stk asegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 0x800000000000) -> (q <= A_STK_HI) ->
      ssp_cells m canary -> mem_inv asegs m -> frm0 fc -> mjx m ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      (q <= VA) -> (VA + 8 * zlength slots <= A_STK_HI) ->
      implMA asegs P (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
        (fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x98008) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma vfp_stderr_after_prologue :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r lo : Z) (canary flags mode : word) (e wend : Z) (tail : list byte) (m0 : mem),
    (rw_cells asegs m0 692360 [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 619384); C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 619716); C8 (Z_to_bv 64 619708); C8 (Z_to_bv 64 6296088); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 0); CB 80 tail]) ->
    (Z.land (bv_unsigned flags) 40 = 0) ->
    (bytes_at asegs m0 A (zb fmt)) ->
    (Forall (fun c : Z => 0 <= c < 256) fmt) ->
    (pass1_ok fmt = true) ->
    (bytes_at asegs m0 VA (u64s slots)) ->
    (args_ok 692360 (bv_unsigned sp - 352) 80 m lo (bv_unsigned sp) (bv_unsigned sp + -368) slots args) ->
    (printf_pieces fmt args = Some (ps, r)) ->
    (fp_calls (length fmt) fmt args = []) ->
    (sp_ok (length fmt) fmt args) ->
    (lo <= bv_unsigned sp - 5552) ->
    ((Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo) ->
    (bv_unsigned sp < 0x800000000000) ->
    (bv_unsigned sp <= 140737488355328) ->
    (rw_cells asegs m0 677432 [C8 (Z_to_bv 64 6294352)]) ->
    (rw_cells asegs m0 6294352 [C8 canary]) ->
    (mem_inv asegs m0) ->
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
    (munch [(lo, bv_unsigned sp); (692360, 692360 + 232)] m m0) ->
    (wmono asegs m m0) ->
    (munch [(lo, bv_unsigned sp); (692360, 692360 + 232)] m m0) ->
    (stk asegs m0 lo (bv_unsigned sp + -368)) ->
    forall (junk : list byte),
    (rw_cells asegs m0 (bv_unsigned sp + -368) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 248 (firstn 248 (firstn 280 (skipn 16 (firstn 304 (firstn 312 (firstn 320 (firstn 328 (firstn 336 (firstn 344 (firstn 352 (firstn 360 junk))))))))))); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
    evtA asegs P (fun ms' : machine_state => implA asegs (NodesA.at_nodeA asegs) P ((printf_model OUT_stderr OUTFP_stderr fmt args;;; FLUSH_stderr) ((@nil Z), st)) (epost (fun p : unit * (list Z * St) => (fun (_ : unit) (bs : list Z * St) (ms' : machine_state) => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms') (fst p) (snd p))) ms') (MS (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some t6) TEmpty) (Some a5) TEmpty) (Some t2) (TNode TEmpty (Some s7) TEmpty)) (Some gp) (TNode (TNode TEmpty (Some s3) TEmpty) (Some (Z_to_bv 64 A)) (TNode TEmpty (Some s11) TEmpty))) (Some (Z_to_bv 64 622704)) (TNode (TNode (TNode TEmpty (Some a7) TEmpty) (Some (Z_to_bv 64 A)) (TNode TEmpty (Some s9) TEmpty)) (Some t0) (TNode (TNode TEmpty (Some s5) TEmpty) (Some (Z_to_bv 64 (bv_unsigned sp + -272))) (TNode TEmpty (Some t4) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some a6) TEmpty) (Some (Z_to_bv 64 692360)) (TNode TEmpty (Some s8) TEmpty)) (Some tp) (TNode (TNode TEmpty (Some s4) TEmpty) (Some (Z_to_bv 64 (bv_unsigned sp + -368))) (TNode TEmpty (Some t3) TEmpty))) (Some (Z_to_bv 64 (bv_unsigned sp + -368))) (TNode (TNode (TNode TEmpty (Some (Z_to_bv 64 6294352)) TEmpty) (Some (Z_to_bv 64 0)) (TNode TEmpty (Some s10) TEmpty)) (Some t1) (TNode (TNode TEmpty (Some s6) TEmpty) (Some (Z_to_bv 64 (bv_unsigned sp + -104))) (TNode TEmpty (Some t5) TEmpty))))) F (Z_to_bv 64 623032) fc None m0 (seg_rom asegs)).
  Proof using FLS FWE PSTK PIMG PHSH PLSH PNUL.
    intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st A VA fmt slots args ps r lo canary flags mode e wend tail m0 FC FL40 BY HF P1 VAA AOK PP FPC SPOK LO GLO QHI SPTOP SSP1 SSP2 MI FRM MJ0 HA0 HA QVA VAHI Rq AB LZB LU MU WM MU1 ST junk FR.
    set (QQ := fun (_ : unit) (bs : list Z * St) (ms' : machine_state) => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms').

    (* [comment removed for export] *)
    pose proof (printf_core1_proof P PSTK PIMG PHSH PLSH PNUL) as PC1. unfold printf_core1_stmt in PC1.
    eapply evtA_cut.
    { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, A_STK_HI, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | exact FRM | lia | lia | lia | lia ]. }
    cbv beta. intros ms' PO. clear PC1. unfold printf_core1_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [asegs] in SSP1, SSP2. fold asegs in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit.
    do 10 zs.
    pose proof towrite_proof as TW. unfold towrite_stmt in TW.
    eapply evtA_cut.
    { eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ intros a k H1 H2; apply PIMG; lia | exact FC | | lia | lia | lia | assumption ].
      rewrite unsigned_lit; [apply sflags_noerr_8; exact FL40|].
      pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    cbv beta. intros ms' PO. clear TW.
    destruct PO as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt).
    rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
    fix_ret.
    zs. if_lit. do 6 zs.
    set (B := bv_unsigned sp + -352) in *.
    (* [comment removed for export] *)
    match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
    apply (rw_cells_split_CB asegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [BUFc FRv]. cbn [cells_size csize Nat.add app] in FRv.
    replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8)%Z with B in BUFc by lia.
    replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 80)%Z with (bv_unsigned sp + -272)%Z in FRv by lia.
    replace (bv_unsigned sp + -368 + Z.of_nat 8)%Z with (bv_unsigned sp + -360)%Z in AP2 by lia.
    match type of BUFc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in BUFc end. clearbody jb.
    match type of FRv with rw_cells _ _ _ (CB 168 ?b :: _) => set (jn := b) in FRv end. clearbody jn.
    pose proof (rw_CB_length _ _ _ _ BUFc) as LJB.
    replace (Z_to_bv 64 VA) with (Z_to_bv 64 (VA + 8 * 0)) in APC by (f_equal; lia).
    (* [comment removed for export] *)
    lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (MJ2 : mjx mm) by (eapply mjx_transport; [exact MJ0 | exact MU | exact WM |];
        unfold mjx_ok_iv, A_CEIL, A_STK_HI; apply Forall_cons; [cbn [fst snd]; lia|]; apply Forall_cons; [cbn [fst snd]; lia|]; apply Forall_nil) end.
    (* [comment removed for export] *)
    ileave.
    pose proof (printf_core_proof (list Z * St) P RSTDERR B 80 (SINK_stderr B) TOPOK_stk OUT_stderr (OUTFP_stderr (St:=St))
                  PSTK PIMG PHSH PLSH PNUL (stderr_sink_frame B) (stderr_sink_flags B) (stderr_sink_mjx B) topok_stk topok_stk_hi (FWE St B)) as PC2.
    unfold printf_core_stmt in PC2.
    assert (FR3 : 0 <= Z.land (bv_unsigned (sx32 flags)) 18446744073709551583 < 2^64).
    { pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    eapply implMA_bind.
    { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
        clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_stk, A_STK_HI, zlength.
      all: try lia.
      1:{ unfold SINK_stderr. cbn [fst].
          exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, jb.
          change (zlength (@nil Z)) with 0. rewrite Z.add_0_r. cbn [zb map app].
          split; [exact FCt|]. rewrite unsigned_lit by lia.
          split; [apply sflags_noerr_32|]. split; [apply sflags_noerr_8; exact FL40|]. split; [exact BUFc|].
          split; [unfold zlength; rewrite LJB; lia|]. split; [subst B; lia|]. split; [unfold GLOBALS_TOP; subst B; lia|].
          split; [unfold in_stackw, A_CEIL, A_STK_HI; subst B; lia|]. exact MJ2. }
      all: first [ exact BY | exact HF | reflexivity | exact APC | exact VAA
                 | cbn [skipn Z.to_nat]; eapply args_ok_vf; [exact AOK | lia | exact MU1]
                 | rewrite FPC; apply Forall_nil | exact SPOK | exact STc
                 | split; [exact SSP1 | exact SSP2] | exact FRM | assumption ]. }
    cbv beta. intros r' [buf3 st3] ms' PO. clear PC2 MU1.
    unfold printf_core_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
    unfold SR in MUc. cbn [app] in MUc.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
    ienter. fix_ret.
    pose proof SNK3 as SNK3'. destruct SNK3' as (flags2 & mode2 & tail2 & rest2 & FC3 & FL32 & FL8 & BUF3 & LEN3 & BHI3 & BLO3 & BSTK3 & MJ3). cbn [fst] in FC3, BUF3, LEN3.
    unfold file_cells in FC3.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [asegs] in SSP1, SSP2. fold asegs in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. zs. zs. if_lit.
    zs. zs. zs. zs. zs.
    ileave. unfold FLUSH_stderr, implMA. cbv beta iota.
    pose proof (FLS St B) as FL. unfold stdio_write_flush_stmt in FL.
    match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => destruct (stk_split _ _ _ (bv_unsigned sp + -368 - 2368) _ H ltac:(lia)) as [ST4a ST4b]; clear H end.
    eapply implA_ebind.
    { unfold implMA in FL.
      eapply FL with (lo := bv_unsigned sp + -368 - 2368) (canary := canary); clear FL; rewrite ?unsigned_lit by lia; unfold OUT_DEPTH, GLOBALS_TOP, TOPOK_stk, A_STK_HI.
      all: try lia.
      all: first [ exact SNK3 | reflexivity | exact ST4b | split; [exact SSP1 | exact SSP2] | assumption ]. }
    cbv beta. intros [[] st4] ms' PO.
    unfold stdio_write_flush_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (z5 & z6 & z7 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z28 & z29 & z30 & z31 & m4 & -> & MUc & WMc & MI4 & ST4b' & SNK4 & SSP4).
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m4 MUc WMc; clear MUc WMc end.
    apply implA_ret_intro. cbn [snd]. fix_ret.
    cbn [fst snd] in SNK4 |- *. clear SNK3 FL.
    destruct SNK4 as (flags4 & mode4 & tail4 & rest4 & FC4 & FL32' & FL8' & BUF4 & LEN4 & _ & _ & _ & MJ4). cbn [fst snd] in FC4, BUF4, LEN4.
    unfold file_cells in FC4. change (zlength (@nil Z)) with 0 in FC4. rewrite Z.add_0_r in FC4.
    clear SSP1 SSP2. destruct SSP4 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [asegs] in SSP1, SSP2. fold asegs in SSP1, SSP2.
    (* [comment removed for export] *)
    do 9 zs.
    (* [comment removed for export] *)
    zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    (* [comment removed for export] *)
    match goal with H : stk _ ?mm lo (bv_unsigned sp + -368 - 2368)%Z, H' : stk _ ?mm (bv_unsigned sp + -368 - 2368)%Z _ |- _ =>
      pose proof (stk_merge _ _ _ _ _ H H' ltac:(lia)) as ST5; clear H H' end.
    pose proof (rw_CB_length _ _ _ _ BUF4) as LB4.
    lazymatch goal with A1 : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, A2 : rw_cells _ ?mm (bv_unsigned sp + -360)%Z _,
                        BU : rw_cells _ ?mm B [CB 80 ?bb], FR : rw_cells _ ?mm (bv_unsigned sp + -272)%Z ?rest |- _ =>
      assert (FALL : rw_cells asegs mm (bv_unsigned sp + -368) ([C8 apv] ++ [C8 (Z_to_bv 64 VA)] ++ [CB 80 bb] ++ rest));
      [ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact A1|];
        apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact A2 | lia] |];
        apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact BU | subst B; lia] |];
        cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
      | clear A1 A2 BU FR ] end.
    cbn [app] in FALL.
    release_frame FALL ST5 (bv_unsigned sp).
    apply evtA_done. subst QQ. cbn [epost fst snd]. unfold vfprintf_stderr_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST5|].
    split.
    { exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags4)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode4, 0, 0, tail4.
      split; [unfold file_cells; exact FC4|].
      rewrite (sflags_olderr0 flags FL40). rewrite unsigned_lit; [| rewrite Z.lor_0_r; pose proof (bv_unsigned_in_range 64 (sx32 flags4)) as R4; unfold bv_modulus in R4; change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R4; lia].
      split; [apply sflags_final_40; [exact FL32' | exact FL8']|]. split; [left; reflexivity | lia]. }
    split; [split; [exact SSP1 | exact SSP2]|].
    lazymatch goal with |- mjx ?mm =>
      eapply mjx_transport; [exact MJ0 | exact MU | exact WM | ];
      [ unfold mjx_ok_iv, A_CEIL, A_STK_HI; apply Forall_cons; [cbn [fst snd]; lia|]; apply Forall_cons; [cbn [fst snd]; lia|]; apply Forall_nil ] end.
  Qed.

  Theorem vfprintf_stderr_proof : vfprintf_stderr_stmt.
  Proof using FLS FWE PSTK PIMG PHSH PLSH PNUL.
    unfold vfprintf_stderr_stmt. intros until canary. cbv zeta.
    intros -> -> -> SF BY HF P1 VAA AOK PP FPC SPOK ST LO GLO QHI SPTOP SSP MI FRM MJ0 HA0 HA QVA VAHI.
    unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, A_STK_HI in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
    pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [asegs] in SSP1, SSP2. fold asegs in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU1.
    destruct SF as (flags & mode & e & wend & tail & FC & FL40). unfold file_cells in FC.
    (* [comment removed for export] *)
    apply (printf_model_outsA asegs P OUT_stderr (OUTFP_stderr (St:=St)) fmt args ps r (fun _ => FLUSH_stderr) _ _ _ PP).
    match goal with |- implMA _ _ _ _ ?Q _ => set (QQ := Q) end.
    ienter.
    carve_frame 368%nat ST.
    do 12 zs. do 14 zs.
    (* [comment removed for export] *)
    eapply vfp_stderr_after_prologue; eassumption.
  Qed.
End Stderr.
End RC__1.
