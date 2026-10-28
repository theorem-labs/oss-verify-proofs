(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Stdio Driver.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import Stdio_kit F_syscalls StdioFiles MonadF MonadF2 RtCells Strnlen_iface Printf_outsA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import F_pop_arg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import Printf_model Printf_mlib.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import F_printf_iface F_printf_core F_vfprintf.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import Printf_pieces Printf_fmts.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg Stdio_kit2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac ienter := ienterF.
Ltac ileave := ileaveF.
(* [comment removed for export] *)
Ltac hide_low :=
  repeat match goal with H : rw_cells bsegs _ ?A _ |- _ =>
    lazymatch A with Zpos _ => idtac | _ => fail end;
    lazymatch eval vm_compute in (A <? 0x1fb740)%Z with true => idtac | false => fail end;
    lazymatch type of H with ?T => change T with (sf_hide T) in H end
  end.
Ltac zs_canary := hide_low; zs; sf_unhide.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma land_mod_low : forall f c k, 0 <= k -> 0 <= c < 2^k -> Z.land f c = Z.land (f mod 2^k) c.
Proof.
  intros f c k Hk Hc. rewrite <- (Z.land_ones f k) by lia. rewrite <- Z.land_assoc, (Z.land_comm (Z.ones k) c), Z.land_ones by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma dec128 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 128)) = true -> forall x, 0 <= x < 128 -> P x = true.
Proof.
  intros P H x Hx. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

Lemma land_sub_mask : forall u a b, Z.land a b = b -> Z.land u a = 0 -> Z.land u b = 0.
Proof. intros u a b Hab Hu. rewrite <- Hab, Z.land_assoc, Hu. apply Z.land_0_l. Qed.
Lemma mod_128_of_32 : forall a, (a mod 2^32) mod 128 = a mod 128.
Proof.
  intros a. change 128 with (2^7). rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.
Lemma sx32_mod128 : forall w : word, bv_unsigned (sx32 w) mod 128 = bv_unsigned w mod 128.
Proof.
  intros w. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R. change (2^64)%Z with 18446744073709551616%Z.
  rewrite <- (mod_128_of_32 (bv_unsigned w)). change (2^32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.
Lemma land_low7 : forall a c, 0 <= c < 128 -> Z.land a c = Z.land (a mod 128) c.
Proof. intros a c Hc. change 128 with (2^7). apply land_mod_low; lia. Qed.

(* [comment removed for export] *)
Lemma flags_noerr_nowr : forall (flags : word), Z.land (bv_unsigned flags) 72 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 8 = 0.
Proof.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 8) with 8.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. revert H. apply land_sub_mask. reflexivity.
Qed.
Lemma flags_noerr_104 : forall (flags : word), Z.land (bv_unsigned flags) 72 = 0 ->
  Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 104 = 0.
Proof.
  intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 104) with 72.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. exact H.
Qed.
Lemma flags_olderr_72 : forall (flags2 flags : word), Z.land (bv_unsigned flags2) 104 = 0 ->
  Z.land (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32)) 72 = 0.
Proof.
  intros flags2 flags H. rewrite Z.land_lor_distr_l. rewrite <- (Z.land_assoc _ 32 72). change (Z.land 32 72) with 0. rewrite Z.land_0_r, Z.lor_0_r.
  rewrite land_low7, sx32_mod128, <- land_low7 by lia. revert H. apply land_sub_mask. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section StdoutSinkProofs.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Let SINK := SINK_stdout (St:=St) get_so.

  Lemma stdout_sink_frame : sink_frame_stmt RSTDOUT RSTDOUT_BUF 1024 SINK.
  Proof using get_so.
    unfold sink_frame_stmt. intros W m m' st (ACT & flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN) MU WM D1 D2.
    split; [exact ACT|]. exists flags, mode, tail, bufbytes.
    split; [|split; [exact FL | split; [| split; [exact PFX | exact LEN]]]].
    - eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
  Qed.

  Lemma file_cells_flags_byte : forall m A flags wend wpos wbase writefn buf bufsize fd mode lbf tail,
    rw_cells bsegs m A (file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail) ->
    rw_cells bsegs m A [CB 1 [Z_to_bv 8 (bv_unsigned flags)]].
  Proof using .
    intros until tail. intros FC. unfold file_cells in FC.
    apply (proj1 (rw_cells_app bsegs m A [_] _)) in FC. destruct FC as [F0 _].
    pose proof (rw_cells_recast3 m A _ [CB 1 [Z_to_bv 8 (bv_unsigned flags)]; CB 3 (Z_to_le_bytes 3 (Z.shiftr (bv_unsigned flags) 8))] F0
                  ltac:(cbn; repeat split) ltac:(reflexivity)) as F1.
    apply (proj1 (rw_cells_app bsegs m A [_] _)) in F1. exact (proj1 F1).
  Qed.

  Lemma stdout_sink_flags : sink_flags_stmt RSTDOUT SINK.
  Proof using get_so.
    unfold sink_flags_stmt. intros m st (ACT & flags & mode & tail & bufbytes & FC & FL & _).
    exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|].
    rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned flags)) with ((bv_unsigned flags) mod 2^8).
    rewrite <- land_mod_low by lia. eapply land_sub_mask; [|exact FL]. reflexivity.
  Qed.

  Lemma topok_none : topok_stmt TOPOK_none.
  Proof using . unfold topok_stmt, TOPOK_none. intros. exact I. Qed.
End StdoutSinkProofs.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stdout.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis GS : forall x so, get_so (set_so so x) = so.
  Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.
  Hypothesis FWX : fwritex_stdout_stmt.
  Hypothesis HSTRN : strnlen_a_stmt.

  Let OUT := stdout_fwritex get_so set_so.
  Let SINK := SINK_stdout (St:=St) get_so.

  Definition vfprintf_stdout_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ stdout_file m' (get_so st')
      /\ ssp_cells m' canary.

  Definition vfprintf_stdout_stmt : Prop :=
    forall RNG (rstk rfmt : region) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
           (lo : Z) (canary : word),
      let q := bv_unsigned sp in
      a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
      stdout_file m (get_so st) ->
      bytes_at bsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      va_area m VA slots -> args_ok RSTDOUT RSTDOUT_BUF 1024 RNG m lo q (q - VF_FRAME) slots args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk bsegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^47) ->       (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv bsegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
      (* [comment removed for export] *)
      (KHIGH <= lo) -> ashenv m ->
      rclean m rstk -> r_lo rstk <= lo -> q <= r_hi rstk ->
      rclean m rfmt -> inreg rfmt A (zlength fmt) -> inreg rfmt 68508 9 ->
      rclean m RBstdout ->
      rng RNG lo (q - lo) -> rng_aimg RNG -> rng RNG VA (8 * zlength slots) ->
      rrng RNG rstk -> rrng RNG rfmt -> rrng RNG RBstdout ->
      implAM RNG (stdout_towrite get_so set_so ;;; outsk OUT ps (mret tt)) st
        (vfprintf_stdout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xbce78) fc None m (seg_rom bsegs)).

  Theorem vfprintf_stdout_proof : vfprintf_stdout_stmt.
  Proof using FWX GS SS HSTRN.
    unfold vfprintf_stdout_stmt. intros until canary. cbv zeta.
    intros -> -> -> SF BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI
           KH ENV RCS RSlo RShi RCF RFM RPF RCB RGstk RGimg RGva RRS RRF RRB.
    unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
    assert (RGfmt : rng RNG A (Z.of_nat (length fmt))) by (eapply rng_sub'; [exact RGimg | unfold zlength in *; lia]).
    assert (RGF : rng RNG RSTDOUT 232) by (eapply rng_sub'; [exact RGimg | lia]).
    assert (RGB : rng RNG RSTDOUT_BUF 1024) by (eapply rng_sub'; [exact RGimg | lia]).
    assert (RBI : inreg RBstdout RSTDOUT_BUF 1024) by (unfold inreg, RBstdout; cbn; lia).
    assert (AW : appW [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z) by solve_appW.
    assert (AS : ashsafe [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z) by solve_ashsafe.
    assert (AW1 : appW [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z) by solve_appW.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
    pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z m) as MU1.
    destruct SF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & PFX & BLEN & INACT). unfold file_cells in FC.
    pose proof (rw_CB_length _ _ _ _ BUF) as LBB.
    (* [comment removed for export] *)
    unfold stdout_towrite, upd_so. apply implAM_upd_l.
    apply (printf_model_outsA OUT (OUTFP_stdout (St:=St)) RNG fmt args ps r (fun _ => mret tt) _ _ _ PP).
    ienter.
    carve_frame 368%nat ST.
    do 12 zs. do 14 zs.
    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    (* [comment removed for export] *)
    pose proof (ashenv_transport _ _ _ ENV MU WM AS) as ENV1.
    pose proof (rclean_transport _ _ _ _ RCS MU WM AW) as RCS1. pose proof (rclean_transport _ _ _ _ RCF MU WM AW) as RCF1.
    eapply evtF_cut.
    { eapply (PC1 RNG rstk rfmt); rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia
        | exact KH | exact ENV1 | exact RCS1 | lia | lia | exact RCF1 | exact RFM | exact RPF
        | eapply rng_sub'; [exact RGstk | lia] | exact RGimg | exact RGfmt | eapply rng_sub'; [exact RGstk | lia] | exact RRS | exact RRF ]. }
    clear ENV1 RCS1 RCF1.
    cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit. zs. zs. zs.
    destruct (so_active (get_so st)) eqn:ACT.
    - (* [comment removed for export] *)
      if_lit. cbv beta iota in FC.
      zs. zs. zs. zs. zs. zs.
      apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
      replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
      ileave.
      pose proof (printf_core_proof St RSTDOUT RSTDOUT_BUF 1024 RBstdout SINK TOPOK_none OUT (OUTFP_stdout (St:=St))
                    (stdout_sink_frame get_so) (stdout_sink_flags get_so) topok_none (FWX St get_so set_so GS SS) HSTRN) as PC2.
      (* [comment removed for export] *)
      pose proof (ashenv_transport _ _ _ ENV MU WM AS) as ENV2.
      pose proof (rclean_transport _ _ _ _ RCS MU WM AW) as RCS2. pose proof (rclean_transport _ _ _ _ RCF MU WM AW) as RCF2.
      pose proof (rclean_transport _ _ _ _ RCB MU WM AW) as RCB2.
      unfold printf_core_stmt in PC2.
      assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
      { rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
        unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
      eapply implAM_bind.
      { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt) (RNG := RNG) (rstk := rstk) (rfmt := rfmt);
          clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
        all: try lia. all: try exact I.
        all: try first [ exact ENV2 | exact RCS2 | exact RCF2 | exact RCB2 | exact RFM | exact RPF | exact RBI | exact RGimg | exact RGva | exact RGF | exact RGB | exact RGfmt
                       | exact RRS | exact RRF | exact RRB
                       | lazymatch goal with |- rng _ _ _ => eapply rng_sub'; [exact RGstk | lia] end ].
        - unfold SINK, SINK_stdout. rewrite GS, ACT. split; [reflexivity|].
          exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode, tail, bufbytes.
          split; [unfold file_cells; exact FC|]. split; [exact FL'|]. split; [exact BUF|]. split; [exact PFX | exact BLEN].
        - exact BY.
        - exact HF.
        - reflexivity.
        - replace (VA + 8 * 0) with VA by lia. exact APC.
        - exact VAA.
        - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1 | exact WM | exact AW1].
        - rewrite FPC. apply Forall_nil.
        - exact STc.
        - split; [exact SSP1 | exact SSP2].
        - assumption.
        - exact FRM. }
      cbv beta. intros r' st' ms' P. clear PC2 MU1 ENV2 RCS2 RCF2 RCB2.
      unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
      destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
      unfold SR in MUc. cbn [app] in MUc.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m3 MUc WMc; clear MUc WMc end.
      apply implAM_ret. fix_ret.
      destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3). unfold file_cells in FC3.
      clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
      (* [comment removed for export] *)
      zs. zs. zs. if_lit.
      zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
      zs_canary. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
      do 9 zs.
      (* [comment removed for export] *)
      replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
        by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
      change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
      rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.
      (* [comment removed for export] *)
      lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
        assert (FALL : rw_cells bsegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
        [ apply (proj2 (rw_cells_app bsegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
        | clear AP FR ] end.
      cbn [app] in FALL.
      release_frame FALL ST3 (bv_unsigned sp).
      apply evtF_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
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
      split; [exact SSP1 | exact SSP2].
    - (* [comment removed for export] *)
      if_lit. cbv beta iota in FC. zs. zs. zs.
      pose proof towrite_proof as TW. unfold towrite_stmt in TW.
      eapply evtF_cut.
      { eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ exact FC | | lia | lia | lia | assumption | exact RGF ].
        rewrite unsigned_lit; [apply flags_noerr_nowr; exact FL72|].
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
        unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
      cbv beta. intros ms' P. clear TW.
      destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt).
      rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
      fix_ret.
      zs. if_lit. zs. zs. zs. zs. zs. zs.
      apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
      replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
      ileave.
      pose proof (printf_core_proof St RSTDOUT RSTDOUT_BUF 1024 RBstdout SINK TOPOK_none OUT (OUTFP_stdout (St:=St))
                    (stdout_sink_frame get_so) (stdout_sink_flags get_so) topok_none (FWX St get_so set_so GS SS) HSTRN) as PC2.
      (* [comment removed for export] *)
      pose proof (ashenv_transport _ _ _ ENV MU WM AS) as ENV2.
      pose proof (rclean_transport _ _ _ _ RCS MU WM AW) as RCS2. pose proof (rclean_transport _ _ _ _ RCF MU WM AW) as RCF2.
      pose proof (rclean_transport _ _ _ _ RCB MU WM AW) as RCB2.
      unfold printf_core_stmt in PC2.
      assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
      { rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
        unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
      eapply implAM_bind.
      { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt) (RNG := RNG) (rstk := rstk) (rfmt := rfmt);
          clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
        all: try lia. all: try exact I.
        all: try first [ exact ENV2 | exact RCS2 | exact RCF2 | exact RCB2 | exact RFM | exact RPF | exact RBI | exact RGimg | exact RGva | exact RGF | exact RGB | exact RGfmt
                       | exact RRS | exact RRF | exact RRB
                       | lazymatch goal with |- rng _ _ _ => eapply rng_sub'; [exact RGstk | lia] end ].
        - unfold SINK, SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [reflexivity|].
          exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, bufbytes.
          change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
          split; [exact FCt|]. split; [exact FL'|]. split; [exact BUF|]. split; [reflexivity | lia].
        - exact BY.
        - exact HF.
        - reflexivity.
        - replace (VA + 8 * 0) with VA by lia. exact APC.
        - exact VAA.
        - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1 | exact WM | exact AW1].
        - rewrite FPC. apply Forall_nil.
        - exact STc.
        - split; [exact SSP1 | exact SSP2].
        - assumption.
        - exact FRM. }
      cbv beta. intros r' st' ms' P. clear PC2 MU1 ENV2 RCS2 RCF2 RCB2.
      unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
      destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
      unfold SR in MUc. cbn [app] in MUc.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m3 MUc WMc; clear MUc WMc end.
      apply implAM_ret. fix_ret.
      destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3). unfold file_cells in FC3.
      clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
      (* [comment removed for export] *)
      zs. zs. zs. if_lit.
      zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
      zs_canary. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
      do 9 zs.
      (* [comment removed for export] *)
      replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
        by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
      change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
      rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.
      (* [comment removed for export] *)
      lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
        assert (FALL : rw_cells bsegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
        [ apply (proj2 (rw_cells_app bsegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
        | clear AP FR ] end.
      cbn [app] in FALL.
      release_frame FALL ST3 (bv_unsigned sp).
      apply evtF_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
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
      split; [exact SSP1 | exact SSP2].
  Qed.
End Stdout.

(* [comment removed for export] *)

Lemma stdout_file_stk : forall m m' so lo hi, stdout_file m so -> munch [(lo, hi)] m m' -> wmono bsegs m m' -> GLOBALS_TOP <= lo -> stdout_file m' so.
Proof.
  unfold GLOBALS_TOP.
  intros m m' so lo hi (flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN & INACT) MU WM Hlo.
  exists flags, mode, tail, bufbytes. split; [|split; [exact FL | split; [| split; [exact PFX | split; [exact LEN | exact INACT]]]]].
  - eapply rw_cells_transport; [exact FC | exact MU | exact WM | cbn [disjoint_from cells_size file_cells csize Nat.add]; lia].
  - eapply rw_cells_transport; [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia].
Qed.
End CANSEC1.
