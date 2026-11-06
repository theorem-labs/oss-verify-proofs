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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Driver.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require NumFacts_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_pop_arg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_printf_core.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_printf_snsink.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_vfprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_vsnprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_vfprintf_stdout.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_mlib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_pieces.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_printf_bridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_piface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module SO_fprintf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Driver.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_snsink OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_vfprintf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_vsnprintf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_vfprintf_stdout.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_pieces.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_printf_bridge.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_model.   (* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac arith_goal := lazymatch goal with
  | |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ >= _)%Z => idtac | |- (_ > _)%Z => idtac
  | |- @eq Z _ _ => idtac | |- @eq nat _ _ => idtac | |- (_ <= _)%nat => idtac | |- (_ < _)%nat => idtac
  | |- ~ _ => idtac | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- False => idtac | |- True => idtac
  end.   (* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac ienter := lazymatch goal with |- Monad.implM _ _ _ _ _ => unfold Monad.implM; apply impl_from_evt | |- ITree.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
               lazymatch goal with |- ITree.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM usegs c s Q ms) | _ => idtac end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section StderrSinkProofs.
  Context {St : Type}.
  Variable B : Z.
  Let SINK := SINK_stderr (St:=St) B.

  Lemma stderr_sink_frame : sink_frame_stmt RSTDERR B 80 SINK.
  Proof using .
    unfold sink_frame_stmt. intros W m m' [buf st] (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BLO) MU WM D1 D2.
    exists flags, mode, tail, rest.
    split; [|split; [exact FL32 | split; [exact FL8 | split; [| split; [exact LEN | split; [exact BHI | exact BLO]]]]]].
    - eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
  Qed.

  Lemma stderr_sink_flags : sink_flags_stmt RSTDERR SINK.
  Proof using B.
    unfold sink_flags_stmt. intros m [buf st] (flags & mode & tail & rest & FC & FL32 & _).
    exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|].
    rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned flags)) with ((bv_unsigned flags) mod 2^8).
    rewrite <- land_mod_low by lia. exact FL32.
  Qed.
End StderrSinkProofs.

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
  Hypothesis FWE : fwritex_stderr_stmt.
  Hypothesis FLS : stdio_write_flush_stmt.

  Definition vfprintf_stderr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : St -> machine_state -> Prop :=
    fun st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ stderr_wfile m'
      /\ ssp_cells m' canary.

  Definition vfprintf_stderr_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
           (lo : Z) (canary : word),
      let q := bv_unsigned sp in
      a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
      stderr_wfile m ->
      bytes_at usegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      va_area m VA slots -> args_ok RSTDERR (q - 352) 80 m lo q (q - VF_FRAME) slots args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk usegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
      ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
      Monad.implM usegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
        (fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x18dec) fc None m (seg_rom usegs)).

  Theorem vfprintf_stderr_proof : vfprintf_stderr_stmt.
  Proof using FLS FWE.
    unfold vfprintf_stderr_stmt. intros until canary. cbv zeta.
    intros -> -> -> SF BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI.
    unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
    pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. idtac. fold usegs in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU1.
    (nelim SF 7%nat; intros flags mode e wend tail FC FL40). unfold file_cells in FC.
    (* [comment removed for export] *)
    apply (printf_model_outs usegs OUT_stderr (OUTFP_stderr (St:=St)) fmt args ps r (fun _ => FLUSH_stderr) _ _ _ PP).
    match goal with |- Monad.implM _ _ _ ?Q _ => set (QQ := Q) end.
    ienter.
    carve_frame 368%nat ST.
    do 12 zs. do 14 zs.
    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    eapply evt_cut.
    { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
    cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
    (nelim P 21%nat; intros x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 m' -> MUc WMc MIc STc SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. idtac. fold usegs in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit.
    do 10 zs.
    pose proof towrite_proof as TW. unfold towrite_stmt in TW.
    eapply evt_cut.
    { eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ exact FC | | lia | lia | lia | assumption ].
      rewrite unsigned_lit; [apply sflags_noerr_8; exact FL40|].
      pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    cbv beta. intros ms' P. clear TW.
    (nelim P 21%nat; intros x5' x6' x7' c1 c2 c3 c4 c5 c6 c7 x28' x29' x30' x31' mode' m'' -> MUc WMc MIt FCt).
    rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
    fix_ret.
    zs. if_lit. do 6 zs.
    set (B := bv_unsigned sp + -352) in *.
    (* [comment removed for export] *)
    match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
    apply (rw_cells_split_CB usegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FRv. destruct FRv as [BUFc FRv]. cbn [cells_size csize Nat.add app] in FRv.
    replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8)%Z with B in BUFc by lia.
    replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 80)%Z with (bv_unsigned sp + -272)%Z in FRv by lia.
    replace (bv_unsigned sp + -368 + Z.of_nat 8)%Z with (bv_unsigned sp + -360)%Z in AP2 by lia.
    match type of BUFc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in BUFc end. clearbody jb.
    match type of FRv with rw_cells _ _ _ (CB 168 ?b :: _) => set (jn := b) in FRv end. clearbody jn.
    pose proof (rw_CB_length _ _ _ _ BUFc) as LJB.
    replace (Z_to_bv 64 VA) with (Z_to_bv 64 (VA + 8 * 0)) in APC by (f_equal; lia).
    (* [comment removed for export] *)
    ileave.
    pose proof (printf_core_proof (list Z * St) RSTDERR B 80 (SINK_stderr B) TOPOK_none OUT_stderr (OUTFP_stderr (St:=St))
                  (stderr_sink_frame B) (stderr_sink_flags B) (topok_none) (FWE St B)) as PC2.
    unfold printf_core_stmt in PC2.
    assert (FR3 : 0 <= Z.land (bv_unsigned (sx32 flags)) 18446744073709551583 < 2^64).
    { pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
      unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
    eapply implM_bind.
    { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
        clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
      all: try (arith_goal; lia). all: try exact I.
      - unfold SINK_stderr. cbn [fst].
        exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, jb.
        change (zlength (@nil Z)) with 0. rewrite Z.add_0_r. cbn [zb map app].
        split; [exact FCt|]. rewrite unsigned_lit by lia.
        split; [apply sflags_noerr_32|]. split; [apply sflags_noerr_8; exact FL40|]. split; [exact BUFc|].
        unfold zlength. rewrite LJB. unfold GLOBALS_TOP. subst B. lia.
      - exact BY.
      - exact HF.
      - reflexivity.
      - exact APC.
      - exact VAA.
      - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1].
      - rewrite FPC. apply Forall_nil.
      - exact STc.
      - split; [exact SSP1 | exact SSP2].
      - assumption.
      - exact FRM. }
    cbv beta. intros r' [buf3 st3] ms' P. clear PC2 MU1.
    unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
    (nelim P 29%nat; intros y5 y6 y7 d1 d2 d3 d4 d5 d6 d7 y28 y29 y30 y31 Ft fc' apv m3 -> MUc WMc MI3 FRM' FOK ST3 SNK3 SSP3 APC3 Hr).
    unfold SR in MUc. cbn [app] in MUc.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc end.
    ienter. fix_ret.
    pose proof SNK3 as SNK3'. (nelim SNK3' 11%nat; intros flags2 mode2 tail2 rest2 FC3 FL32 FL8 BUF3 LEN3 BHI3 BLO3). cbn [fst] in FC3, BUF3, LEN3.
    unfold file_cells in FC3.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. idtac. fold usegs in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. zs. zs. if_lit.
    zs. zs. zs. zs. zs.
    ileave. unfold FLUSH_stderr, Monad.implM. cbv beta iota.
    pose proof (FLS St B) as FL. unfold stdio_write_flush_stmt in FL.
    match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => destruct (stk_split _ _ _ (bv_unsigned sp + -368 - 1024) _ H ltac:(lia)) as [ST4a ST4b]; clear H end.
    eapply impl_ebind.
    { unfold Monad.implM in FL.
      eapply FL with (lo := bv_unsigned sp + -368 - 1024) (canary := canary); clear FL; rewrite ?unsigned_lit by lia; unfold OUT_DEPTH, GLOBALS_TOP.
      all: try (arith_goal; lia).
      - exact SNK3.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact ST4b.
      - split; [exact SSP1 | exact SSP2].
      - assumption. }
    cbv beta. intros [[] st4] ms' P.
    unfold stdio_write_flush_post in P. rewrite !unsigned_lit in P by lia.
    (nelim P 23%nat; intros z5 z6 z7 e0 e1 e2 e3 e4 e5 e6 e7 z28 z29 z30 z31 m4 -> MUc WMc MI4 ST4b' SNK4 SSP4).
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m4 MUc WMc; clear MUc WMc end.
    apply impl_ret_intro. cbn [snd]. fix_ret.
    cbn [fst snd] in SNK4 |- *. clear SNK3 FL.
    (nelim SNK4 11%nat; intros flags4 mode4 tail4 rest4 FC4 FL32' FL8' BUF4 LEN4 _ _). cbn [fst snd] in FC4, BUF4, LEN4.
    unfold file_cells in FC4. change (zlength (@nil Z)) with 0 in FC4. rewrite Z.add_0_r in FC4.
    clear SSP1 SSP2. destruct SSP4 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. idtac. fold usegs in SSP1, SSP2.
    (* [comment removed for export] *)
    do 9 zs.
    (* [comment removed for export] *)
    zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    (* [comment removed for export] *)
    match goal with H : stk _ ?mm lo (bv_unsigned sp + -368 - 1024)%Z, H' : stk _ ?mm (bv_unsigned sp + -368 - 1024)%Z _ |- _ =>
      pose proof (stk_merge _ _ _ _ _ H H' ltac:(lia)) as ST5; clear H H' end.
    pose proof (rw_CB_length _ _ _ _ BUF4) as LB4.
    lazymatch goal with A1 : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, A2 : rw_cells _ ?mm (bv_unsigned sp + -360)%Z _,
                        BU : rw_cells _ ?mm B [CB 80 ?bb], FR : rw_cells _ ?mm (bv_unsigned sp + -272)%Z ?rest |- _ =>
      assert (FALL : rw_cells usegs mm (bv_unsigned sp + -368) ([C8 apv] ++ [C8 (Z_to_bv 64 VA)] ++ [CB 80 bb] ++ rest));
      [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact A1|];
        apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact A2 | lia] |];
        apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact BU | subst B; lia] |];
        cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
      | clear A1 A2 BU FR ] end.
    cbn [app] in FALL.
    release_frame FALL ST5 (bv_unsigned sp).
    apply evt_done. subst QQ. cbn [epost fst snd]. unfold vfprintf_stderr_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST5|].
    split.
    { exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags4)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode4, 0, 0, tail4.
      split; [unfold file_cells; exact FC4|].
      rewrite (sflags_olderr0 flags FL40). rewrite unsigned_lit; [apply sflags_final_40; [exact FL32' | exact FL8']|].
      rewrite Z.lor_0_r. pose proof (bv_unsigned_in_range 64 (sx32 flags4)) as R4. unfold bv_modulus in R4. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R4. lia. }
    split; [exact SSP1 | exact SSP2].
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
      stk usegs m lo q -> (lo <= q - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
      ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      Monad.implM usegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
        (fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x18634) fc None m (seg_rom usegs)).

  Theorem fprintf_gen_proof : fprintf_gen_stmt.
  Proof using FLS FWE.
    unfold fprintf_gen_stmt. intros until canary. cbv zeta.
    intros -> -> SF BY HF P1 AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA.
    unfold FPRINTF_DEPTH, VF_FRAME, GLOBALS_TOP, STATIC_SPLIT in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. idtac. fold usegs in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
    (nelim SF 7%nat; intros flags mode e wend tail FC FL40). unfold file_cells in FC.
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
      all: try reflexivity. all: try (arith_goal; lia).
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
    (nelim P 27%nat; intros y5 y6 y7 d0 d1 d2 d3 d4 d5 d6 d7 y28 y29 y30 y31 Ft fc' m3 -> MUc WMc MI3 FRM' FOK ST3 SF3 SSP3).
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
                            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x18634) fc None m (seg_rom usegs)) ->
               Monad.implM usegs (stderr_fprintf ps) st
                            (fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
                            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x18634) fc None m (seg_rom usegs))).
  { intros ps H. unfold stderr_fprintf, Monad.implM in *.
    eapply impl_epost_mono.
    - eapply (stderr_bridge usegs ps [] st (fun s' ms' => fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt s' ms')).
      eapply impl_mono; [eapply (impl_tforall usegs (at_node usegs) _ _ _ _ (outsk_flush_leaves ps [] st)); exact H|].
      intros [|[[] [b s']]] ms' [H1 H2]; cbn in H1, H2 |- *; [exact I|]. eapply vf_to_diag_post; [exact H1 | exact H2].
    - intros [[] s'] ms' H'. exact H'. }
  pose proof (@fprintf_gen_proof St FWE FLS) as FG. unfold fprintf_gen_stmt in FG. cbv zeta in FG. unfold VF_FRAME, FPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT in FG.
  destruct d as [argv0 | path | path | | | |]; cbn [diag_args] in DA; try contradiction; unfold s_diag; apply BR; clear BR.
  - (nelim DA 8%nat; intros Ha1 slack BY HF SLK LEN DJ GA). unfold GLOBALS_TOP in GA.
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
  - (nelim DA 8%nat; intros Ha1 slack BY HF SLK LEN DJ GA). unfold GLOBALS_TOP in GA.
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
  - (nelim DA 8%nat; intros Ha1 slack BY HF SLK LEN DJ GA). unfold GLOBALS_TOP in GA.
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
End SO_fprintf.

(* [comment removed for export] *)
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_fmt_fp_lib F_pad Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Printf_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_piface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_vfprintf F_vsnprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import SO_piface.   (* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_rz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import SO_fwritex_stderr SO_stdio_flush.
Import SO_fprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import SO_fwrite.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_piface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
      (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).
Local Notation rzt := (SO_rz.rzt usegs).

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
      * apply (rzt_stdio_writev usegs st mo 2 buf p CH). unfold INTERNAL_BUFSIZ in *. lia.
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
  apply (rzt_stdio_writev usegs st mo 2 buf' [] CH).
  unfold INTERNAL_BUFSIZ, zlength in *. cbn [length]. lia.
Qed.

Lemma rzt_stderr_fwrite : forall {St} (s : list Z) (st : St) mo,
  chan_ok mo 2 -> 0 < zlength s <= 2^25 ->
  rzt (stderr_fwrite s st) mo (map (WriteEv (Z_to_bv 64 2)) (to_bytes s)) (fun r => snd r = st).
Proof.
  intros St s st mo CH LEN. unfold stderr_fwrite. rewrite (proj2 (Z.ltb_lt 0 (zlength s))) by lia.
  change (to_bytes s) with (to_bytes ([] ++ s)). apply (rzt_stdio_writev usegs st mo 2 [] s CH).
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
             bytes_at usegs m (bv_unsigned a2) (zb (map bv_unsigned s) ++ Z_to_bv 8 0 :: slack0)
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
  Hypothesis ro : ro_bytes_b usegs A (zb lit) = true.
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
