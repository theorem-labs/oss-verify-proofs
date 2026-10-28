(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad Stdio Driver AsanCtrl AsanEmbed ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import Printf_model Printf_mlib Printf_pieces Printf_fmts F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow ITreeA SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells Stdio_kit Stdio_kit2 F_syscalls StdioFiles MonadF MonadF2 Strnlen_iface
     F_printf_iface F_fwritex_stdout F_vfprintf F_vfprintf_stdout I_printf_formats I_printf_icpt AProto AMalloc_iface AProg_kit ADriver_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
(* [comment removed for export] *)
Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac lit_frames :=
  repeat match goal with
  | H : context [(bv_unsigned ?sp + ?a - ?b)%Z] |- _ =>
      is_zlit a; is_zlit b; let v := eval vm_compute in (a - b)%Z in replace (bv_unsigned sp + a - b)%Z with (bv_unsigned sp + v)%Z in H by lia
  | |- context [(bv_unsigned ?sp + ?a - ?b)%Z] =>
      is_zlit a; is_zlit b; let v := eval vm_compute in (a - b)%Z in replace (bv_unsigned sp + a - b)%Z with (bv_unsigned sp + v)%Z by lia
  | H : context [(bv_unsigned ?sp + ?a + ?b)%Z] |- _ =>
      is_zlit a; is_zlit b; let v := eval vm_compute in (a + b)%Z in replace (bv_unsigned sp + a + b)%Z with (bv_unsigned sp + v)%Z in H by lia
  | |- context [(bv_unsigned ?sp + ?a + ?b)%Z] =>
      is_zlit a; is_zlit b; let v := eval vm_compute in (a + b)%Z in replace (bv_unsigned sp + a + b)%Z with (bv_unsigned sp + v)%Z by lia
  end.
Ltac fix_ret := lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Section CANSEC1. Context {rc : runConstT}.
Definition AEMIT_DEPTH : Z := 5728.

Lemma out_pieces_outsk : forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St) ps,
  out_pieces get_so set_so ps = outsk (stdout_fwritex get_so set_so) ps (mret tt).
Proof. intros St get_so set_so ps. induction ps as [|p ps IH]; cbn [out_pieces outsk]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Section Emit.
  Hypothesis HSTRN : strnlen_a_stmt.     (* [comment removed for export] *)
  Notation get_so := aps_so.
  Notation set_so := aset_so.

  Definition emit_printf_postA (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : amem) : unit -> APS -> footprint -> machine_state -> Prop :=
    fun _ st' RNG' ms' => RNG' = RNG /\ exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : amem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ stdout_file m' (get_so st')
      /\ ssp_cells m' canary.

  (* [comment removed for export] *)
  Definition emit_printf_stmtA : Prop :=
    forall RNG (rstk : region) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : APS) (lo : Z) (canary : word) (v : Z),
      stdout_file m (get_so st) ->
      (-2^31 <= v < 2^31) -> bv_unsigned a1 mod 2^32 = v mod 2^32 ->
      stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - AEMIT_DEPTH) -> (KHIGH <= lo) -> (bv_unsigned sp < 2^47) ->
      ssp_cells m canary -> mem_inv bsegs m -> frm0 fc ->
      (* [comment removed for export] *)
      ashenv m -> rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> rodata_sh0 m -> rclean m RBstdout ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rrng RNG rstk -> rrng RNG RFMT -> rrng RNG RBstdout ->
      implMA RNG (s_emit get_so set_so v) st
             (emit_printf_postA RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 AEMIT_PRINTF) fc None m (seg_rom bsegs)).

  Theorem emit_printf_proofA : emit_printf_stmtA.
  Proof.
    unfold emit_printf_stmtA. intros until v. intros SF VR VA1 ST LO KH SPHI SSP MI FRM ENV RCS RSlo RShi ROD RCB RGstk RGimg RRS RRF RRB.
    unfold AEMIT_DEPTH in *. pose proof KH as KH'. unfold KHIGH in KH'.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
    (* [comment removed for export] *)
    unfold s_emit, stdout_vprintf.
    rewrite (out_pieces_outsk APS get_so set_so (pieces_pct_d v)).
    apply implMA_fold. unfold AEMIT_PRINTF. ienter.
    carve_frame 80%nat ST.
    do 15 zs.
    (* [comment removed for export] *)
    zs.
    (* [comment removed for export] *)
    assert (AW : appW [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z) by solve_appW.
    assert (AS : ashsafe [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z) by solve_ashsafe.
    xport_env ENV MU WM as ENV1. pose proof (rodata_sh0_frame _ _ _ ROD MU WM AW) as ROD1.
    pose proof ENV1 as (Hgot & _ & Hshb & Hini & _ & _ & Hrpf & _ & _ & _ & _ & _ & Hckp & _).
    (* [comment removed for export] *)
    assert (FZ : shadow_bytes m0 (shad (FMT_D - 64)) (shad (FMT_D + 3 + 64)) (fun _ => 0)) by (apply (rodata_sh0_fmt _ FMT_D 3 ROD1); unfold FMT_D; lia).
    assert (RSHF : rng RNG (shad (FMT_D - 64)) (shad (FMT_D + 3 + 64) - shad (FMT_D - 64))).
    { unfold rrng, RFMT in RRF. cbn [r_rlo r_rhi] in RRF. eapply rng_sub'; [exact RRF|]. rewrite !shad_div. unfold FMT_D, ASHOFF. lia. }
    call_sp (vprintf_i_pre_d RNG).
    all: lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- stk _ _ _ _ => exact ST
         | |- rng _ _ _ => first [assumption | eapply rng_sub'; [exact RGstk | lia]]
         | |- _ => first [assumption | reflexivity | lia]
         end.
    lit_frames.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app bsegs _ _ [_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
    replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in VAC by lia.
    pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
    change (le8 a1 ++ le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a1; a2; a3; a4; a5; a6; a7]) in VAA.
    (* [comment removed for export] *)
    clear ENV1 ROD1 Hgot Hshb Hini Hrpf Hckp FZ RSHF.
    xport_env ENV MU WM as ENV2. pose proof (rodata_sh0_frame _ _ _ ROD MU WM AW) as ROD2.
    pose proof (rclean_transport _ _ _ _ RCS MU WM AW) as RCS2. pose proof (rclean_transport _ _ _ _ RCB MU WM AW) as RCB2.
    apply evtF_done.
    pose proof (vfprintf_stdout_proof get_so set_so aps_get_set' aps_set_set' fwritex_stdout_proof HSTRN) as VF.
    unfold vfprintf_stdout_stmt in VF. cbv zeta in VF.
    eapply implF_epost_evtF.
    { eapply VF with (A := FMT_D) (VA := (bv_unsigned sp + -56)%Z) (fmt := FMT_pct_d) (slots := [a1; a2; a3; a4; a5; a6; a7]) (args := [PA_i v])
                     (r := pct_d_len v) (lo := lo) (canary := canary) (rstk := rstk) (rfmt := RFMT);
        clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
      all: try reflexivity. all: try lia.
      - eapply stdout_file_stk; [exact SF | exact MU1 | exact WM | unfold GLOBALS_TOP; lia].
      - apply fmt_bytes_at; [assumption | vm_compute; reflexivity | unfold FMT_D; lia | vm_compute; discriminate].
      - unfold FMT_pct_d. forall_range.
      - exact VAA.
      - cbn [args_ok arg_ok]. split; [|exact I]. split; [lia | exact VA1].
      - apply printf_pieces_pct_d. lia.
      - assumption.
      - split; assumption.
      - assumption.
      - exact FRM.
      - unfold FMT_D. lia.
      - unfold FMT_D, FMT_pct_d. cbn [length]. lia.
      - exact ENV2.
      - exact RCS2.
      - apply rodata_sh0_rclean. exact ROD2.
      - unfold inreg, RFMT, FMT_D, FMT_pct_d. cbn. lia.
      - unfold inreg, RFMT. cbn. lia.
      - exact RCB2.
      - eapply rng_sub'; [exact RGstk | lia].
      - exact RGimg.
      - eapply rng_sub'; [exact RGstk | cbn; lia].
      - exact RRS.
      - exact RRF.
      - exact RRB. }
    cbv beta. intros [[] st'] RNG' ms' [-> P]. clear MU1.
    unfold vfprintf_stdout_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret. clear VF. cbn [fst snd] in *.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (vfprintf_i_post RNG); rewrite ?unsigned_lit by lia; [exact MI3 | exact PC1 | eapply rng_sub'; [exact RGstk | lia]]. }
    cbv beta. intros ms' ->. rewrite !unsigned_lit by lia. lit_frames. fix_ret.
    eapply evtF_cut.
    { eapply (vprintf_i_post RNG); rewrite ?unsigned_lit by lia; [exact MI3 | eassumption | eapply rng_sub'; [exact RGstk | lia]]. }
    cbv beta. intros ms' ->. rewrite !unsigned_lit by lia. lit_frames. fix_ret.
    (* [comment removed for export] *)
    zs. zs. zs.
    (* [comment removed for export] *)
    lazymatch goal with P1 : rw_cells _ ?mm (bv_unsigned sp + -176)%Z _, S : stk _ _ lo _ |- _ => release_frame P1 S (bv_unsigned sp + -128)%Z end.
    lazymatch goal with P0 : rw_cells _ ?mm (bv_unsigned sp + -128)%Z _, S : stk _ _ lo _ |- _ => release_frame P0 S (bv_unsigned sp + -80)%Z end.
    lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?hd, VAC : rw_cells _ ?mm (bv_unsigned sp + -56)%Z ?rest |- _ =>
      assert (FALL : rw_cells bsegs mm (bv_unsigned sp + -80) (hd ++ rest));
      [ apply (proj2 (rw_cells_app bsegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
      | clear FR VAC ] end.
    cbn [app] in FALL.
    lazymatch goal with S : stk _ _ lo _ |- _ => release_frame FALL S (bv_unsigned sp) end.
    apply evtF_done. unfold emit_printf_postA. split; [reflexivity|]. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [assumption|]. split; [exact SF3|]. exact SSP3.
  Qed.
End Emit.
End CANSEC1.
