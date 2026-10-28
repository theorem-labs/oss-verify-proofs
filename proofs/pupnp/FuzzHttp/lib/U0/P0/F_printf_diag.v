(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memset F_memcpy.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Stdio_base Printf_lib F_pop_arg.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Printf_model Printf_mlib Printf_pieces.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import F_printf_iface F_printf_core F_vfprintf F_vfprintf_stdout Printf_bridge F_fprintf.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import F_fwritex_stdout F_fwritex_stderr F_stdio_flush.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import StoreFast.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Lemma fmt_bytes_at : forall m A f, mem_inv rsegs m -> ro_bytes_b rsegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
  bytes_at rsegs m A (zb f).
Proof.
  intros m A f MI RB H0 H1.
  pose proof (ro_cells_bytes_at rsegs m A _ (ro_cells_image rsegs m A (zb f) MI RB H0 ltac:(rewrite zb_length; unfold zlength in H1; lia))) as B.
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.

Section Emit.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis GS : forall x so, get_so (set_so so x) = so.
  Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.

  Definition emit_printf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ stdout_file m' (get_so st')
      /\ ssp_cells m' canary.

  Definition emit_printf_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
      stdout_file m (get_so st) ->
      bv_unsigned a1 mod 2^32 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - EMIT_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp <= 2^47) ->
      ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
      implM rsegs (stdout_vprintf get_so set_so pieces_emit) st
            (emit_printf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13f74) fc None m (seg_rom rsegs)).

  Theorem emit_printf_proof : emit_printf_stmt.
  Proof using GS SS.
    unfold emit_printf_stmt. intros until canary. intros SF A1 ST LO GLO QHI SSP MI FRM.
    pose proof fwritex_stdout_proof as FWX.
    unfold EMIT_DEPTH, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.

    unfold stdout_vprintf.
    change (out_pieces get_so set_so pieces_emit) with (outsk (stdout_fwritex get_so set_so) pieces_emit (mret tt)).
    ienter.
    carve_frame 80%nat ST.
    do 15 zs.

    do 7 zs.
    apply (proj1 (rw_cells_app rsegs _ _ [_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
    replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in VAC by lia.
    pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
    change (le8 a1 ++ le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a1; a2; a3; a4; a5; a6; a7]) in VAA.
    ileave.
    pose proof (vfprintf_stdout_proof get_so set_so GS SS FWX) as VF. unfold vfprintf_stdout_stmt in VF. cbv zeta in VF.
    eapply implM_post_evt.
    { eapply VF with (A := A_FMT_emit) (VA := bv_unsigned sp + -56) (fmt := FMT_emit) (slots := [a1; a2; a3; a4; a5; a6; a7]) (args := [PA_i 0])
                     (r := 2) (lo := lo) (canary := canary);
        clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
      all: first [ reflexivity | lia
                 | eapply stdout_file_stk; [exact SF | exact MU1 | exact WM | lia]
                 | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_emit; lia | vm_compute; discriminate]
                 | unfold FMT_emit; forall_range
                 | exact VAA
                 | cbn [args_ok arg_ok]; split; [|exact I]; split; [lia|]; rewrite A1; reflexivity
                 | apply printf_pieces_emit
                 | exact ST
                 | split; [exact SSP1 | exact SSP2]
                 | exact MI
                 | exact FRM
                 | unfold A_FMT_emit, FMT_emit; cbn [length]; lia ]. }
    cbv beta. intros [] st' ms' P. clear MU1.
    unfold vfprintf_stdout_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    zs. zs. zs.
    lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?hd, VAC : rw_cells _ ?mm (bv_unsigned sp + -56)%Z ?rest |- _ =>
      assert (FALL : rw_cells rsegs mm (bv_unsigned sp + -80) (hd ++ rest));
      [ apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
      | clear FR VAC ] end.
    cbn [app] in FALL.
    release_frame FALL ST3 (bv_unsigned sp).
    apply evt_done. unfold emit_printf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST3|]. split; [exact SF3|]. exact SSP3.
  Qed.
End Emit.

Inductive pdiag : Type :=
| PDUsage (argv0 : list Z)
| PDCannotOpen (path : list Z)
| PDReadError (path : list Z)
| PDTooBig.

Definition pdiag_pieces (d : pdiag) : list (list Z) :=
  match d with
  | PDUsage s => pieces_usage s
  | PDCannotOpen s => pieces_cannot_open s
  | PDReadError s => pieces_read_error s
  | PDTooBig => pieces_too_big
  end.

Section Diag.
  Context {St : Type}.

  Definition diag_args (d : pdiag) (m : mem) (fmtp argw : word) (lo sp : Z) : Prop :=
    match d with
    | PDUsage s | PDCannotOpen s | PDReadError s =>
        fmtp = Z_to_bv 64 (match d with PDUsage _ => A_FMT_usage | PDCannotOpen _ => A_FMT_cannot_open | _ => A_FMT_read_error end)
        /\ exists slack : list byte,
             bytes_at rsegs m (bv_unsigned argw) (zb s ++ Z_to_bv 8 0 :: slack)
             /\ Forall (fun c => 0 < c < 256) s
             /\ ((- (bv_unsigned argw + zlength s + 1)) mod 8 <= zlength slack)
             /\ (zlength s < 2^23 - 256)
             /\ (bv_unsigned argw + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned argw)
             /\ (GLOBALS_TOP <= bv_unsigned argw)
             /\ (bv_unsigned argw + zlength s + 1 <= 2^47)
    | PDTooBig => fmtp = Z_to_bv 64 A_FMT_too_big /\ bv_unsigned argw mod 2^32 = 67108864
    end.

  Definition fprintf_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ stderr_wfile m'
      /\ ssp_cells m' canary
      /\ st' = st.

  Definition fprintf_diag_stmt : Prop :=
    forall (d : pdiag)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
      stderr_wfile m ->
      a0 = Z_to_bv 64 RSTDERR -> diag_args d m a1 a2 lo (bv_unsigned sp) ->
      stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp <= 2^47) ->
      ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
      implM rsegs (stderr_fprintf (St:=St) (pdiag_pieces d)) st
            (fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1ae8c) fc None m (seg_rom rsegs)).

  #[using="Type"] Lemma vf_to_diag_post : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (st st' : St) ms,
    vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st' ms -> st' = st ->
    fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt st' ms.
  Proof.
    intros until ms. intros (x5 & x6 & x7 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & E & MU & WM & MI & FRM & FOK & ST & SF & SSP) Est.
    exists x5, x6, x7, a0, a1, a2, a3, a4, a5, a6, a7, x28, x29, x30, x31, Ft, fc', m'.
    repeat (split; [assumption|]). exact Est.
  Qed.

  #[using="Type"] Theorem fprintf_diag_proof : fprintf_diag_stmt.
  Proof.
    unfold fprintf_diag_stmt. intros d. intros until canary. intros SF Ha0 DA ST LO GLO QHI SSP MI FRM.
    pose proof fwritex_stderr_proof as FWE. pose proof stdio_write_flush_proof as FLS.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    unfold FPRINTF_DEPTH, GLOBALS_TOP in *.

    assert (BR : forall ps, Monad.implM rsegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
                              (fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
                              (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1ae8c) fc None m (seg_rom rsegs)) ->
                 Monad.implM rsegs (stderr_fprintf ps) st
                              (fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
                              (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1ae8c) fc None m (seg_rom rsegs))).
    { intros ps H. unfold stderr_fprintf, Monad.implM in *.
      eapply impl_epost_mono.
      - eapply (stderr_bridge rsegs ps [] st (fun s' ms' => fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt s' ms')).
        eapply impl_mono; [eapply (impl_tforall rsegs (at_node rsegs) _ _ _ _ (outsk_flush_leaves ps [] st)); exact H|].
        intros [|[[] [b s']]] ms' [H1 H2]; cbn in H1, H2 |- *; [exact I|]. eapply vf_to_diag_post; [exact H1 | exact H2].
      - intros [[] s'] ms' H'. exact H'. }
    pose proof (@fprintf_gen_proof St FWE FLS) as FG. unfold fprintf_gen_stmt in FG. cbv zeta in FG. unfold VF_FRAME, FPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT in FG.
    destruct d as [argv0 | path | path | ]; cbn [diag_args] in DA; unfold pdiag_pieces; apply BR; clear BR.
    - destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA & U47). unfold GLOBALS_TOP in GA.
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
    - destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA & U47). unfold GLOBALS_TOP in GA.
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
    - destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA & U47). unfold GLOBALS_TOP in GA.
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
End Diag.
