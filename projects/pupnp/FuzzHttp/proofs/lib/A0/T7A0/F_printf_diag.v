(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode Tac Agree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFW1_lemmas Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit Stdio_base Printf_lib F_pop_arg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Printf_model Printf_mlib Printf_pieces.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import F_printf_iface F_printf_core F_vfprintf F_vfprintf_stdout F_vfprintf_stderr Printf_bridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import F_fwritex_stdout F_fwritex_stderr F_stdio_flush Stdio_iface.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import StoreFast.
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

Lemma fmt_bytes_at : forall m A f, mem_inv asegs m -> ro_bytes_b asegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
  bytes_at asegs m A (zb f).
Proof.
  intros m A f MI RB H0 H1.
  pose proof (ro_cells_bytes_at asegs m A _ (ro_cells_image asegs m A (zb f) MI RB H0 ltac:(rewrite zb_length; unfold zlength in H1; lia))) as B.
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.

Definition A0A_FMT_emit : Z := 0x1493b.
Definition A0A_FMT_usage : Z := 0x159c4.
Definition A0A_FMT_too_big : Z := 0x1998a.
Definition A0A_FMT_cannot_open : Z := 0x1da9d.
Definition A0A_FMT_read_error : Z := 0x1dab2.

Lemma zb_pos_no_nul : forall s, Forall (fun c => 0 < c < 256) s -> ~ In (Z_to_bv 8 0) (zb s).
Proof.
  intros s HF. unfold zb. rewrite in_map_iff. intros (c & E & Hin).
  pose proof (proj1 (Forall_forall _ _) HF c Hin) as Hc.
  assert (bv_unsigned (Z_to_bv 8 c) = 0) as U by (rewrite E; reflexivity).
  rewrite Z_to_bv_unsigned in U. cbn beta in Hc. rewrite bv_wrap_small in U by (unfold bv_modulus; cbn; lia). lia.
Qed.

Lemma shw_acc : forall m A n, shw m A n -> accessible m A n /\ sh_readable m A n.
Proof. intros m A n (H1 & H2 & _). split; assumption. Qed.

Section Emit.
  Context {HC : HasCeiling} {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis GS : forall x so, get_so (set_so so x) = so.
  Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.

  Hypothesis MCI : memcpy_i_stmt.
  Hypothesis MSI : memset_i_stmt.
  Hypothesis SNI : strnlen_i_stmt.
  Hypothesis VPF : vprintf_front_stmt.
  Hypothesis VPB : vprintf_back_stmt.
  Hypothesis VFF : vfprintf_front_stmt.
  Hypothesis VFB : vfprintf_back_stmt.

  Definition emit_printf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ stdout_file m' (get_so st')
      /\ ssp_cells m' canary
      /\ asan_env asegs m'.

  Definition emit_printf_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
      stdout_file m (get_so st) ->
      bv_unsigned a1 mod 2^32 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - EMIT_DEPTH) -> (GLOBALS_TOP <= lo) -> (alloc_ceiling <= lo) ->
      (bv_unsigned sp <= 2^47) -> (bv_unsigned sp mod 16 = 0) ->
      ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
      asan_env asegs m -> shw m lo (bv_unsigned sp - lo) -> shw m RSTDOUT_BUF 1024 -> shw m RO_LO RO_SZ ->
      implM asegs (stdout_vprintf get_so set_so pieces_emit) st
            (emit_printf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x864cc) fc None m (seg_rom asegs)).

  Theorem emit_printf_proof : emit_printf_stmt.
  Proof using GS SS MCI MSI SNI VPF VPB VFF VFB.
    unfold emit_printf_stmt. intros until canary. intros SF A1 ST LO GLO CLO QHI AL SSP MI FRM ENV SHK SHB SHRO.
    pose proof (fwritex_stdout_proof MCI) as FWX.
    pose proof (@alloc_ceiling_bounds HC) as CEILB.
    unfold EMIT_DEPTH, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.

    unfold stdout_vprintf.
    change (out_pieces get_so set_so pieces_emit) with (outsk (stdout_fwritex get_so set_so) pieces_emit (mret tt)).
    ienter.
    carve_frame 80%nat ST.
    do 15 zs.

    apply (proj1 (rw_cells_app asegs _ _ [_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
    replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in VAC by lia.
    pose proof VAC as VAC0. apply (proj1 (rw_cells_app asegs _ _ [_] _)) in VAC0. destruct VAC0 as [VA1 _].

    eapply evt_cut.
    { eapply (VPF _ (bv_unsigned sp + -80)) with (lo := lo) (ap := bv_unsigned sp + -56); rewrite ?unsigned_lit by lia.
      all: first [ eapply asan_env_frame; [exact ENV | exact MU | exact WM | env_safe_tac] | exact ST | exact MI | reflexivity | exact VA1 | idtac ].
      all: try lia. all: try (unfold A0_RT_STACK; lia). all: try (clear - AL Rq; Z.div_mod_to_equations; lia).
      all: apply (shw_acc m0); eapply shw_frame; [eapply shw_sub; [exact SHRO| unfold RO_LO; lia| unfold RO_LO, RO_SZ; lia| lia] | exact MU | app_ivs_tac]. }
    post_call asegs m0. rename POST into FR1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

    do 7 zs.

    eapply evt_cut.
    { eapply (VFF _ (bv_unsigned sp + -80 - 48)) with (lo := lo) (ap := bv_unsigned sp + -56) (stream := RSTDOUT); rewrite ?unsigned_lit by lia.
      all: first [ exact VA1 | reflexivity | idtac ]. all: try assumption.
      all: try lia. all: try (unfold A0_RT_STACK; lia). all: try (clear - AL Rq; Z.div_mod_to_equations; lia).
      all: apply (shw_acc m1); eapply shw_frame; [eapply shw_sub; [exact SHRO| unfold RO_LO; lia| unfold RO_LO, RO_SZ; lia| lia] | exact MU | app_ivs_tac]. }
    post_call asegs m1. rename POST into FR2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
    change (le8 a1 ++ le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a1; a2; a3; a4; a5; a6; a7]) in VAA.

    ileave.
    pose proof (vfprintf_stdout_proof get_so set_so GS SS FWX MSI SNI) as VF. unfold vfprintf_stdout_stmt in VF. cbv zeta in VF.
    eapply implM_post_evt.
    { eapply VF with (A := A0A_FMT_emit) (VA := bv_unsigned sp + -56) (fmt := FMT_emit) (slots := [a1; a2; a3; a4; a5; a6; a7]) (args := [PA_i 0])
                     (r := 2) (lo := lo) (canary := canary);
        clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
      all: first [ reflexivity | lia | unfold A0A_FMT_emit; lia
                 | eapply stdout_file_stk; [exact SF | exact MU1 | exact WM | lia]
                 | apply fmt_bytes_at; [assumption | vm_compute; reflexivity | unfold A0A_FMT_emit; lia | vm_compute; discriminate]
                 | unfold FMT_emit; forall_range
                 | exact VAA
                 | cbn [args_ok arg_ok]; split; [|exact I]; split; [lia|]; rewrite A1; reflexivity
                 | apply printf_pieces_emit
                 | assumption
                 | split; [exact SSP1 | exact SSP2]
                 | unfold A0A_FMT_emit, FMT_emit; cbn [length]; lia
                 | idtac ].
      all: eapply shw_frame; [| exact MU | app_ivs_tac].
      all: first [ eapply shw_sub; [exact SHK | lia | lia | lia] | exact SHB | exact SHRO
                 | eapply shw_sub; [exact SHRO| unfold RO_LO, A0A_FMT_emit; lia| unfold RO_LO, RO_SZ, A0A_FMT_emit, FMT_emit; cbn [length]; lia| unfold FMT_emit; cbn [length]; lia] ]. }
    cbv beta. intros [] st' ms' P.
    clear MU1.
    unfold vfprintf_stdout_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3 & ENV3).
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.

    rewrite <- (Z_to_bv_bv_unsigned d0).
    eapply evt_cut.
    { eapply (VFB _ _ _ _ (bv_unsigned sp + -80 - 48)) with (lo := lo); rewrite ?unsigned_lit by lia.
      all: first [ exact FR2 | exact ST3 | exact ENV3 | exact MI3 | lia | idtac ]. }
    destruct SF3 as (fl3 & md3 & tl3 & bb3 & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6). unfold file_cells in SOF1.
    post_call asegs m3.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.

    eapply evt_cut.
    { eapply (VPB _ _ _ (bv_unsigned sp + -80)) with (lo := lo); rewrite ?unsigned_lit by lia.
      all: first [ exact FR1 | lia | idtac ]. all: try assumption. }
    post_call asegs m4.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.

    clear VA1. zs. zs.
    lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?hd, VAC : rw_cells _ ?mm (bv_unsigned sp + -56)%Z ?rest |- _ =>
      assert (FALL : rw_cells asegs mm (bv_unsigned sp + -80) (hd ++ rest));
      [ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
      | clear FR VAC ] end.
    cbn [app] in FALL.
    lazymatch goal with ST5 : stk asegs _ lo _ |- _ => release_frame FALL ST5 (bv_unsigned sp) end.
    zs.
    apply evt_done. unfold emit_printf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [assumption|]. split; [| split; [split; [exact SSP1| exact SSP2] | assumption]].
    exists fl3, md3, tl3, bb3. unfold file_cells. repeat (split; [assumption|]). assumption.
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

Definition pdiag_fmt (d : pdiag) : Z :=
  match d with PDUsage _ => A0A_FMT_usage | PDCannotOpen _ => A0A_FMT_cannot_open | PDReadError _ => A0A_FMT_read_error | PDTooBig => A0A_FMT_too_big end.

Section Diag.
  Context {HC : HasCeiling} {St : Type}.
  Hypothesis MCI : memcpy_i_stmt.
  Hypothesis MSI : memset_i_stmt.
  Hypothesis SNI : strnlen_i_stmt.
  Hypothesis FPS : forall fmt flen, fprintf_s_front_stmt fmt flen.
  Hypothesis FPU : fprintf_u_front_stmt.
  Hypothesis FPB : fprintf_back_stmt.

  Definition diag_args (d : pdiag) (m : mem) (fmtp argw : word) (lo sp : Z) : Prop :=
    fmtp = Z_to_bv 64 (pdiag_fmt d) /\
    match d with
    | PDUsage s | PDCannotOpen s | PDReadError s =>
        exists slack : list byte,
             bytes_at asegs m (bv_unsigned argw) (zb s ++ Z_to_bv 8 0 :: slack)
             /\ Forall (fun c => 0 < c < 256) s
             /\ ((- (bv_unsigned argw + zlength s + 1)) mod 8 <= zlength slack)
             /\ (zlength s < 2^23 - 256)
             /\ (bv_unsigned argw + zlength s + 1 + zlength slack <= alloc_ceiling \/ sp <= bv_unsigned argw)
             /\ (GLOBALS_TOP <= bv_unsigned argw)
             /\ (bv_unsigned argw + zlength s + 1 < 2^47)
             /\ shw m (bv_unsigned argw) (zlength s + 1)
    | PDTooBig => bv_unsigned argw mod 2^32 = 67108864
    end.

  Definition fprintf_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ stderr_wfile m'
      /\ ssp_cells m' canary
      /\ asan_env asegs m'
      /\ st' = st.

  Definition fprintf_diag_stmt : Prop :=
    forall (d : pdiag)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
      stderr_wfile m ->
      a0 = Z_to_bv 64 RSTDERR -> diag_args d m a1 a2 lo (bv_unsigned sp) ->
      stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (alloc_ceiling <= lo) ->
      (bv_unsigned sp <= 2^47) ->
      ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
      asan_env asegs m -> shw m lo (bv_unsigned sp - lo) -> shw m RO_LO RO_SZ ->
      implM asegs (stderr_fprintf (St:=St) (pdiag_pieces d)) st
            (fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 A0_fprintf) fc None m (seg_rom asegs)).

  #[using="Type"] Lemma vf_to_diag_post : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (st st' : St) ms,
    vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st' ms -> st' = st ->
    fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt st' ms.
  Proof.
    intros until ms. intros (x5 & x6 & x7 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & E & MU & WM & MI & FRM & FOK & ST & SF & SSP & ENV) Est.
    exists x5, x6, x7, a0, a1, a2, a3, a4, a5, a6, a7, x28, x29, x30, x31, Ft, fc', m'.
    repeat (split; [assumption|]). exact Est.
  Qed.

  Lemma fprintf_icpt : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (q lo : Z) (canary : word)
      (A : Z) (fmt : list Z) (args : list parg) (ps : list (list Z)) (r : Z),
      evt asegs (fprintf_front_post q gp tp RSTDERR A a2 a3 a4 a5 a6 a7 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
          (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 A0_fprintf) fc None m (seg_rom asegs)) ->
      stderr_wfile m ->
      ro_bytes_b asegs A (zb fmt) = true -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      (forall m', munch [(lo, q)] m m' -> args_ok RSTDERR (q - 112 - 352) 80 m' lo (q - 112) (q - 112 - VF_FRAME) [a2; a3; a4; a5; a6; a7] args) ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk asegs m lo q -> (lo <= q - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (alloc_ceiling <= lo) -> (0 <= q <= 2^47) ->
      ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
      asan_env asegs m -> shw m lo (q - lo) -> shw m RO_LO RO_SZ ->
      implM asegs (stderr_fprintf (St:=St) ps) st
            (fprintf_diag_post ra (Z_to_bv 64 q) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
            (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 A0_fprintf) fc None m (seg_rom asegs)).
  Proof using MCI MSI SNI FPB.
    intros until r. intros FRONT SF RB HF P1 HA0 HA AOK PP FPC ST LO GLO CLO QHI SSP MI FRM ENV SHK SHRO.
    pose proof (fwritex_stderr_proof MCI) as FWE. pose proof stdio_write_flush_proof as FLS.
    pose proof (@alloc_ceiling_bounds HC) as CEILB.
    unfold FPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.

    assert (BR : forall (Q1 : St -> machine_state -> Prop) ms0,
                 Monad.implM asegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st) (fun _ bs ms' => Q1 (snd bs) ms') ms0 ->
                 Monad.implM asegs (stderr_fprintf ps) st (fun _ s' ms' => Q1 s' ms' /\ s' = st) ms0).
    { intros Q1 ms0 H. unfold stderr_fprintf, Monad.implM in *.
      eapply impl_epost_mono.
      - eapply (stderr_bridge asegs ps [] st (fun s' ms' => Q1 s' ms' /\ s' = st)).
        eapply impl_mono; [eapply (impl_tforall asegs (at_node asegs) _ _ _ _ (outsk_flush_leaves ps [] st)); exact H|].
        intros [|[[] [b s']]] ms' [H1 H2]; cbn in H1, H2 |- *; [exact I|]. split; [exact H1 | exact H2].
      - intros [[] s'] ms' H'. exact H'. }

    eapply implM_evt; [exact FRONT|]. cbv beta. intros ms1 PO.
    destruct PO as (u0 & u1 & u2 & x13 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & m1 & junk & aq & -> & MU1 & WM1 & MI1 & ST1 & ENV1 & FR1).
    pose proof (@vfprintf_stderr_proof HC St FWE FLS MSI SNI) as VF. unfold vfprintf_stderr_stmt in VF. cbv zeta in VF.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (rw_cells_transport asegs _ m m1 _ _ SSP1 MU1 WM1 ltac:(cbn [disjoint_from]; simpl_sizes; lia)) as SSP1'.
    pose proof (rw_cells_transport asegs _ m m1 _ _ SSP2 MU1 WM1 ltac:(cbn [disjoint_from]; simpl_sizes; lia)) as SSP2'.

    pose proof FR1 as VAC. apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_] _)) in VAC. destruct VAC as [_ VAC]. cbn [cells_size csize Nat.add app] in VAC.
    replace (q - 112 + Z.of_nat 64)%Z with (q - 48)%Z in VAC by lia.
    pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
    change (le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a2; a3; a4; a5; a6; a7]) in VAA.

    eapply implM_post_evt.
    { apply BR. eapply VF with (A := A) (VA := q - 48) (fmt := fmt) (slots := [a2; a3; a4; a5; a6; a7]) (args := args)
                     (lo := lo) (canary := canary);
        clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength in *; cbn [length].
      all: first [ reflexivity | lia
                 | exact HF | exact P1 | exact VAA | apply AOK; exact MU1 | exact PP | exact FPC | exact ST1
                 | split; [exact SSP1' | exact SSP2'] | exact MI1 | exact FRM | exact ENV1
                 | idtac ].
      1: { destruct SF as (fl0 & md0 & e0 & we0 & tl0 & FC0 & FL0). exists fl0, md0, e0, we0, tl0. split; [| exact FL0].
           eapply rw_cells_transport; [exact FC0 | exact MU1 | exact WM1 | cbn [disjoint_from cells_size file_cells csize Nat.add]; lia]. }
      1: { apply fmt_bytes_at; [exact MI1 | exact RB | lia | unfold zlength; lia]. }
      all: eapply shw_frame; [| exact MU1 | app_ivs_tac].
      all: first [ eapply shw_sub; [exact SHK | lia | lia | lia] | exact SHRO
                 | eapply shw_sub; [exact SHRO| unfold RO_LO; lia| unfold RO_LO, RO_SZ; lia| pose proof (zb_length fmt); unfold zlength in *; lia] ]. }
    cbv beta. intros [] st' ms' [P ->].
    unfold vfprintf_stderr_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m2 & -> & MU2 & WM2 & MI2 & FRM' & FOK & ST2 & SF2 & SSP2x & ENV2).
    destruct SF2 as (fl2 & md2 & e2 & we2 & tl2 & FC2 & FL2). unfold file_cells in FC2.
    destruct SSP2x as [SP1 SP2]. unfold got_ssp, ssp_guard in SP1, SP2.
    pose proof (rw_cells_transport asegs _ m1 m2 _ _ FR1 MU2 WM2 ltac:(cbn [disjoint_from]; simpl_sizes; lia)) as FR2.
    fix_ret.

    rewrite <- (Z_to_bv_bv_unsigned d0).
    eapply evt_cut.
    { eapply (FPB _ _ _ _ q) with (lo := lo); rewrite ?unsigned_lit by lia.
      all: first [ exact FR2 | reflexivity | exact ST2 | exact ENV2 | exact MI2 | lia | idtac ]. }
    intros ms3 PO. destruct PO as (v5 & v6 & v7 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & v28 & v29 & v30 & v31 & m3 & -> & MU3 & WM3 & MI3 & ST3 & ENV3).
    pose proof (rw_cells_transport asegs _ m2 m3 _ _ FC2 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FC3.
    pose proof (rw_cells_transport asegs _ m2 m3 _ _ SP1 MU3 WM3 ltac:(cbn [disjoint_from]; simpl_sizes; lia)) as SP1'.
    pose proof (rw_cells_transport asegs _ m2 m3 _ _ SP2 MU3 WM3 ltac:(cbn [disjoint_from]; simpl_sizes; lia)) as SP2'.
    apply evt_done. unfold fprintf_diag_post. rewrite !unsigned_lit by lia. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MU3]]];
             unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]]|].
    split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|]. split; [exact ST3|].
    split; [exists fl2, md2, e2, we2, tl2; split; [exact FC3 | exact FL2]|].
    split; [split; [exact SP1' | exact SP2']|]. split; [exact ENV3 | reflexivity].
  Qed.

  Theorem fprintf_diag_proof : fprintf_diag_stmt.
  Proof using MCI MSI SNI FPS FPU FPB.
    unfold fprintf_diag_stmt. intros d. intros until canary. intros SF Ha0 [Ha1 DA] ST LO GLO CLO QHI SSP MI FRM ENV SHK SHRO.
    pose proof (@alloc_ceiling_bounds HC) as CEILB.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    set (q := bv_unsigned sp) in *. assert (Esp : sp = Z_to_bv 64 q) by (symmetry; apply Z_to_bv_bv_unsigned). clearbody q. subst sp.
    unfold FPRINTF_DEPTH, GLOBALS_TOP in *.
    destruct d as [argv0 | path | path | ]; cbn [pdiag_fmt pdiag_pieces] in *.
    - destruct DA as (slack & BY & HFp & SLK & LEN & DJ & GA & U47 & SHS).
      pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length argv0) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB. unfold zlength in *.
      assert (BY0 : bytes_at asegs m (bv_unsigned a2) (zb argv0 ++ [Z_to_bv 8 0])).
      { change (zb argv0 ++ Z_to_bv 8 0 :: slack) with (zb argv0 ++ ([Z_to_bv 8 0] ++ slack)) in BY. rewrite app_assoc in BY.
        exact (proj1 (proj1 (bytes_at_app asegs m _ _ _) BY)). }
      eapply fprintf_icpt with (A := A0A_FMT_usage) (fmt := FMT_usage) (args := [PA_s argv0]);
      [ eapply (FPS A0A_FMT_usage 17) with (stream := RSTDERR) (S := bv_unsigned a2) (sbuf := zb argv0) (lo := lo); rewrite ?unsigned_lit by lia;
        first [ unfold fmt_pct_s, A0A_FMT_usage; lia | exact ENV | exact ST | exact MI | exact Ha0 | exact Ha1 | symmetry; apply Z_to_bv_bv_unsigned
              | exact BY0 | apply zb_pos_no_nul; exact HFp | lia | unfold A0_RT_STACK; lia | rewrite LZS; lia
              | apply (shw_acc m); eapply shw_sub; [exact SHRO| unfold RO_LO, A0A_FMT_usage; lia| unfold RO_LO, RO_SZ, A0A_FMT_usage; lia| lia]
              | rewrite LZS; apply (shw_acc m); exact SHS
              | rewrite LZS; eapply icpt_rng_of_shw; [exact SHS | unfold zlength in *; lia | unfold zlength in *; lia] ]
      | exact SF
      | vm_compute; reflexivity
      | apply forall_range_b; vm_compute; reflexivity
      | vm_compute; reflexivity
      | unfold A0A_FMT_usage; lia
      | replace (zlength FMT_usage) with 17 by (vm_compute; reflexivity); unfold A0A_FMT_usage, STATIC_SPLIT; lia
      | intros m' MU'; cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; rewrite ?unsigned_lit by lia;
        pose proof (bytes_at_transport asegs _ m m' _ _ BY MU' ltac:(cbn [disjoint_from]; rewrite length_app, LZS; cbn [length]; lia)) as BY';
        repeat match goal with |- _ /\ _ => split end;
        first [ exact BY' | exact HFp | unfold VF_FRAME; lia | eapply shw_frame; [exact SHS | exact MU' | app_ivs_tac] ]
      | apply printf_pieces_usage; unfold zlength, INT_MAX in *; lia
      | vm_compute; reflexivity
      | exact ST
      | unfold FPRINTF_DEPTH; lia
      | unfold GLOBALS_TOP; lia
      | lia | lia | exact SSP | exact MI | exact FRM | exact ENV | exact SHK | exact SHRO ].
    - destruct DA as (slack & BY & HFp & SLK & LEN & DJ & GA & U47 & SHS).
      pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length path) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB. unfold zlength in *.
      assert (BY0 : bytes_at asegs m (bv_unsigned a2) (zb path ++ [Z_to_bv 8 0])).
      { change (zb path ++ Z_to_bv 8 0 :: slack) with (zb path ++ ([Z_to_bv 8 0] ++ slack)) in BY. rewrite app_assoc in BY.
        exact (proj1 (proj1 (bytes_at_app asegs m _ _ _) BY)). }
      eapply fprintf_icpt with (A := A0A_FMT_cannot_open) (fmt := FMT_cannot_open) (args := [PA_s path]);
      [ eapply (FPS A0A_FMT_cannot_open 21) with (stream := RSTDERR) (S := bv_unsigned a2) (sbuf := zb path) (lo := lo); rewrite ?unsigned_lit by lia;
        first [ unfold fmt_pct_s, A0A_FMT_cannot_open; lia | exact ENV | exact ST | exact MI | exact Ha0 | exact Ha1 | symmetry; apply Z_to_bv_bv_unsigned
              | exact BY0 | apply zb_pos_no_nul; exact HFp | lia | unfold A0_RT_STACK; lia | rewrite LZS; lia
              | apply (shw_acc m); eapply shw_sub; [exact SHRO| unfold RO_LO, A0A_FMT_cannot_open; lia| unfold RO_LO, RO_SZ, A0A_FMT_cannot_open; lia| lia]
              | rewrite LZS; apply (shw_acc m); exact SHS
              | rewrite LZS; eapply icpt_rng_of_shw; [exact SHS | unfold zlength in *; lia | unfold zlength in *; lia] ]
      | exact SF
      | vm_compute; reflexivity
      | apply forall_range_b; vm_compute; reflexivity
      | vm_compute; reflexivity
      | unfold A0A_FMT_cannot_open; lia
      | replace (zlength FMT_cannot_open) with 21 by (vm_compute; reflexivity); unfold A0A_FMT_cannot_open, STATIC_SPLIT; lia
      | intros m' MU'; cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; rewrite ?unsigned_lit by lia;
        pose proof (bytes_at_transport asegs _ m m' _ _ BY MU' ltac:(cbn [disjoint_from]; rewrite length_app, LZS; cbn [length]; lia)) as BY';
        repeat match goal with |- _ /\ _ => split end;
        first [ exact BY' | exact HFp | unfold VF_FRAME; lia | eapply shw_frame; [exact SHS | exact MU' | app_ivs_tac] ]
      | apply printf_pieces_cannot_open; unfold zlength, INT_MAX in *; lia
      | vm_compute; reflexivity
      | exact ST
      | unfold FPRINTF_DEPTH; lia
      | unfold GLOBALS_TOP; lia
      | lia | lia | exact SSP | exact MI | exact FRM | exact ENV | exact SHK | exact SHRO ].
    - destruct DA as (slack & BY & HFp & SLK & LEN & DJ & GA & U47 & SHS).
      pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length path) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB. unfold zlength in *.
      assert (BY0 : bytes_at asegs m (bv_unsigned a2) (zb path ++ [Z_to_bv 8 0])).
      { change (zb path ++ Z_to_bv 8 0 :: slack) with (zb path ++ ([Z_to_bv 8 0] ++ slack)) in BY. rewrite app_assoc in BY.
        exact (proj1 (proj1 (bytes_at_app asegs m _ _ _) BY)). }
      eapply fprintf_icpt with (A := A0A_FMT_read_error) (fmt := FMT_read_error) (args := [PA_s path]);
      [ eapply (FPS A0A_FMT_read_error 23) with (stream := RSTDERR) (S := bv_unsigned a2) (sbuf := zb path) (lo := lo); rewrite ?unsigned_lit by lia;
        first [ unfold fmt_pct_s, A0A_FMT_read_error; lia | exact ENV | exact ST | exact MI | exact Ha0 | exact Ha1 | symmetry; apply Z_to_bv_bv_unsigned
              | exact BY0 | apply zb_pos_no_nul; exact HFp | lia | unfold A0_RT_STACK; lia | rewrite LZS; lia
              | apply (shw_acc m); eapply shw_sub; [exact SHRO| unfold RO_LO, A0A_FMT_read_error; lia| unfold RO_LO, RO_SZ, A0A_FMT_read_error; lia| lia]
              | rewrite LZS; apply (shw_acc m); exact SHS
              | rewrite LZS; eapply icpt_rng_of_shw; [exact SHS | unfold zlength in *; lia | unfold zlength in *; lia] ]
      | exact SF
      | vm_compute; reflexivity
      | apply forall_range_b; vm_compute; reflexivity
      | vm_compute; reflexivity
      | unfold A0A_FMT_read_error; lia
      | replace (zlength FMT_read_error) with 23 by (vm_compute; reflexivity); unfold A0A_FMT_read_error, STATIC_SPLIT; lia
      | intros m' MU'; cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; rewrite ?unsigned_lit by lia;
        pose proof (bytes_at_transport asegs _ m m' _ _ BY MU' ltac:(cbn [disjoint_from]; rewrite length_app, LZS; cbn [length]; lia)) as BY';
        repeat match goal with |- _ /\ _ => split end;
        first [ exact BY' | exact HFp | unfold VF_FRAME; lia | eapply shw_frame; [exact SHS | exact MU' | app_ivs_tac] ]
      | apply printf_pieces_read_error; unfold zlength, INT_MAX in *; lia
      | vm_compute; reflexivity
      | exact ST
      | unfold FPRINTF_DEPTH; lia
      | unfold GLOBALS_TOP; lia
      | lia | lia | exact SSP | exact MI | exact FRM | exact ENV | exact SHK | exact SHRO ].
    -
      pose proof (bv_unsigned_in_range 64 a2) as R2.
      eapply fprintf_icpt with (A := A0A_FMT_too_big) (fmt := FMT_too_big) (args := [PA_u 67108864]);
      [ eapply FPU with (stream := RSTDERR) (lo := lo); rewrite ?unsigned_lit by lia;
        first [ exact ENV | exact ST | exact MI | exact Ha0 | exact Ha1 | lia | unfold A0_RT_STACK; lia
              | apply (shw_acc m); eapply shw_sub; [exact SHRO| unfold RO_LO; lia| unfold RO_LO, RO_SZ; lia| lia] ]
      | exact SF
      | vm_compute; reflexivity
      | apply forall_range_b; vm_compute; reflexivity
      | vm_compute; reflexivity
      | unfold A0A_FMT_too_big; lia
      | replace (zlength FMT_too_big) with 33 by (vm_compute; reflexivity); unfold A0A_FMT_too_big, STATIC_SPLIT; lia
      | intros m' MU'; cbn [args_ok arg_ok]; split; [split; [lia | exact DA] | exact I]
      | apply printf_pieces_too_big
      | vm_compute; reflexivity
      | exact ST
      | unfold FPRINTF_DEPTH; lia
      | unfold GLOBALS_TOP; lia
      | lia | lia | exact SSP | exact MI | exact FRM | exact ENV | exact SHK | exact SHRO ].
  Qed.
End Diag.

Section Fwrite.
  Context {HC : HasCeiling} {St : Type}.
  Hypothesis FWR : @fwrite_diag_stmt St.
  Hypothesis TOW : towrite_stmt.
  Hypothesis FWF : fwrite_front_stmt.
  Hypothesis FWB : fwrite_back_stmt.

  #[using="Type"] Lemma stderr_wfile0_munch1 : forall lo hi m m', munch [(lo, hi)] m m' -> wmono asegs m m' -> RSTDERR + 232 <= lo ->
    stderr_wfile0 m -> stderr_wfile0 m'.
  Proof.
    intros lo hi m m' MU WM H (flags & mode & e & wend & tail & F1 & F2 & F3 & F4).
    exists flags, mode, e, wend, tail. split; [| split; [exact F2| split; [exact F3| exact F4]]].
    eapply rw_cells_transport; [exact F1 | exact MU | exact WM | cbn [disjoint_from cells_size file_cells csize Nat.add]; lia].
  Qed.

  Definition fwrite_diagA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ stderr_wfile0 m'
      /\ ssp_cells m' canary
      /\ asan_env asegs m'
      /\ st' = st.

  Definition fwrite_diagA_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z),
      stderr_wfile0 m ->
      ro_bytes_b asegs (bv_unsigned a0) (zb s) = true -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s < 2^23 ->
      a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
      (RO_LO <= bv_unsigned a0) -> (bv_unsigned a0 + zlength s <= RO_LO + RO_SZ) ->
      stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2128 - A0_RT_STACK - FWRITE_DEPTH) -> (GLOBALS_TOP <= lo) -> (alloc_ceiling <= lo) ->
      (bv_unsigned sp <= 2^47) ->
      ssp_cells m canary -> mem_inv asegs m ->
      asan_env asegs m -> shw m RO_LO RO_SZ ->
      implM asegs (stderr_fwrite s : M St unit) st
            (fwrite_diagA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 A0_fwrite) fc None m (seg_rom asegs)).

  Theorem fwrite_diagA_proof : fwrite_diagA_stmt.
  Proof using FWR TOW FWF FWB.
    unfold fwrite_diagA_stmt. intros until s. intros SE RB HF LS Ha1 Ha2 Ha3 RLO RHI ST LO GLO CLO QHI SSP MI ENV SHRO.
    pose proof (@alloc_ceiling_bounds HC) as CEILB. unfold FWRITE_DEPTH, GLOBALS_TOP, RO_LO, RO_SZ, A0_RT_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra0.
    set (q := bv_unsigned sp) in *. assert (Esp : sp = Z_to_bv 64 q) by (symmetry; apply Z_to_bv_bv_unsigned). clearbody q. subst sp.
    set (S := bv_unsigned a0) in *. assert (Ea0 : a0 = Z_to_bv 64 S) by (symmetry; apply Z_to_bv_bv_unsigned). clearbody S. subst a0.

    eapply implM_evt.
    { eapply (FWF _ q) with (lo := lo) (p := S) (sz := zlength s) (nm := 1) (f := RSTDERR); rewrite ?unsigned_lit by lia;
        first [exact ENV | exact ST | exact MI | exact Ha1 | exact Ha2 | exact Ha3 | reflexivity | lia]. }
    cbv beta. intros ms1 PO.
    destruct PO as (u0 & u1 & u2 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & m1 & junk & -> & MU1 & WM1 & MI1 & ST1 & ENV1 & FR1).
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (rw_cells_transport asegs _ m m1 _ _ SSP1 MU1 WM1 ltac:(cbn [disjoint_from]; simpl_sizes; lia)) as SSP1'.
    pose proof (rw_cells_transport asegs _ m m1 _ _ SSP2 MU1 WM1 ltac:(cbn [disjoint_from]; simpl_sizes; lia)) as SSP2'.

    eapply implM_post_evt.
    { eapply (FWR _ (Z_to_bv 64 (q - 2128))) with (lo := lo) (canary := canary) (s := s); rewrite ?unsigned_lit by lia.
      all: first [ exact TOW | reflexivity | exact RB | exact HF | exact LS | exact ST1 | exact MI1 | lia
                 | unfold FWRITE_DEPTH, GLOBALS_TOP; lia
                 | split; [exact SSP1' | exact SSP2'] | idtac ].
      - eapply stderr_wfile0_munch1; [exact MU1 | exact WM1 | lia | exact SE].
      - apply fmt_bytes_at; [exact MI1 | exact RB | lia | lia]. }
    cbv beta. intros [] st' ms' P.
    destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & m2 & -> & MU2 & WM2 & MI2 & ST2 & SE2 & SSP3 & ->).
    rewrite !unsigned_lit in MU2 by lia. rewrite !unsigned_lit in ST2 by lia.
    assert (ENV2 : asan_env asegs m2) by (eapply asan_env_frame; [exact ENV1 | exact MU2 | exact WM2 | pose proof CEILB; env_safe_tac]).
    destruct SSP3 as [SP1 SP2]. unfold got_ssp, ssp_guard in SP1, SP2.
    pose proof (rw_cells_transport asegs _ m1 m2 _ _ FR1 MU2 WM2 ltac:(cbn [disjoint_from]; simpl_sizes; lia)) as FR2.
    fix_ret.

    assert (SHRO2 : shw m2 S (zlength s)).
    { eapply (shw_frame [(lo, q); (RSTDERR, RSTDERR + 232)]); [eapply shw_sub; [exact SHRO | lia | lia | lia] | | app_ivs_tac].
      eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros; lia. }
    eapply evt_cut.
    { eapply (FWB _ _ _ _ _ _ _ q) with (lo := lo) (r := 1); rewrite ?unsigned_lit by lia.
      all: first [ exact FR2 | exact ENV2 | exact ST2 | exact MI2 | lia | unfold A0_RT_STACK; lia | idtac ].
      intros _. rewrite Z.mul_1_l. destruct (shw_acc m2 _ _ SHRO2) as [AC2 RD2]. split; [exact AC2 | split; [exact RD2 |]].
      eapply icpt_rng_of_shw; [exact SHRO2 | unfold zlength in *; lia | unfold zlength in *; lia]. }
    intros ms3 PO. destruct PO as (v5 & v6 & v7 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & v28 & v29 & v30 & v31 & m3 & -> & MU3 & WM3 & MI3 & ST3 & ENV3).
    pose proof (rw_cells_transport asegs _ m2 m3 _ _ SP1 MU3 WM3 ltac:(cbn [disjoint_from]; simpl_sizes; lia)) as SP1'.
    pose proof (rw_cells_transport asegs _ m2 m3 _ _ SP2 MU3 WM3 ltac:(cbn [disjoint_from]; simpl_sizes; lia)) as SP2'.
    apply evt_done. unfold fwrite_diagA_post. rewrite !unsigned_lit by lia. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MU3]]];
             unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]]|].
    split; [exact MI3|]. split; [exact ST3|].
    split; [eapply stderr_wfile0_munch1; [exact MU3 | exact WM3 | lia | exact SE2]|].
    split; [split; [exact SP1' | exact SP2']|]. split; [exact ENV3 | reflexivity].
  Qed.
End Fwrite.
