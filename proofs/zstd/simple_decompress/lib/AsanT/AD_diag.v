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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode Bytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad Stdio Driver.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FmtFp Printf_model Printf_mlib Printf_pieces Printf_fmts F_fmt_fp_lib DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow ITreeA SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells Stdio_kit Stdio_kit2 F_syscalls StdioFiles MonadF MonadF2 Strnlen_iface
     F_printf_iface F_fwritex_stderr F_stdio_flush F_vfprintf F_vfprintf_stderr Printf_bridge Stdio_iface F_fwrite
     I_printf_formats I_printf_icpt I_fwrite AProto ABase ADriver_iface.
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
  | H : context [(bv_unsigned ?sp - ?a)%Z] |- _ =>
      is_zlit a; let v := eval vm_compute in (- a)%Z in replace (bv_unsigned sp - a)%Z with (bv_unsigned sp + v)%Z in H by lia
  | |- context [(bv_unsigned ?sp - ?a)%Z] =>
      is_zlit a; let v := eval vm_compute in (- a)%Z in replace (bv_unsigned sp - a)%Z with (bv_unsigned sp + v)%Z by lia
  end.
Ltac fix_ret := lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Section CANSEC1. Context {rc : runConstT}.
Definition AFPRINTF : Z := 0x44230.      (* [comment removed for export] *)
Definition AFWRITE : Z := 0x44218.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AFWRITE_DEPTH : Z := 2368.
Definition AFPRINTF_DEPTH : Z := 5664.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Fwrite.
  Context {St : Type}.

  Definition afwrite_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (canary : word) (m : amem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : amem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ stderr_wfile0 m'
      /\ ssp_cells m' canary
      /\ st' = st.

  (* [comment removed for export] *)
  Definition afwrite_diag_stmt : Prop :=
    forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : St) (lo : Z) (canary : word) (A : Z) (s : list Z),
      stderr_wfile0 m ->
      bytes_at bsegs m A (zb s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s < 2^31 ->
      a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
      0x10000 + 64 <= A -> A + zlength s + 64 <= 0x210c0 ->
      stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - AFWRITE_DEPTH) -> (KHIGH <= lo) -> (bv_unsigned sp < 2^47) ->
      ssp_cells m canary -> mem_inv bsegs m ->
      ashenv m -> rodata_sh0 m ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rrng RNG RFMT ->
      implAM RNG (stderr_fwrite s : M St unit) st
             (afwrite_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 AFWRITE) fc None m (seg_rom bsegs)).

  Theorem afwrite_diag_proof : afwrite_diag_stmt.
  Proof.
    unfold afwrite_diag_stmt. intros until s. intros SF BY HF LEN -> -> -> -> ALO AHI ST LO KH SPHI SSP MI ENV ROD RGstk RGimg RRF.
    unfold AFWRITE_DEPTH in *. pose proof KH as KH'. unfold KHIGH in KH'.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof ENV as (Hgot & Hric & Hshb & Hini & Hlay & Hrmem & Hrpf & Hrwcs & Hrread & Hrfw & _).
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB. unfold zlength in *.
    unfold AFWRITE. ienterF.
    (* [comment removed for export] *)
    zs.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (fwrite_i_pre RNG); first [exact MI | exact ST | lia | exact KH | exact Hini | exact Hrfw | exact RGimg | exact RGstk]. }
    cbv beta. intros ms1 MID.
    destruct MID as (u0 & u1 & u2 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & STM1 & FR1 & INI1).
    apply evtF_done.
    (* [comment removed for export] *)
    pose proof (magree_of_munch bsegs _ _ _ MU1 WM1) as AG1.
    assert (OUT1 : forall a, a < bv_unsigned sp - 2144 -> outside [(bv_unsigned sp - 2144, bv_unsigned sp)] a) by (intros a Ha; cbn; lia).
    assert (SF1 : stderr_wfile0 m1).
    { destruct SF as (flags & mode & e & wend & tail & Hc & HR). exists flags, mode, e, wend, tail. split; [| exact HR].
      eapply rw_cells_magree; [exact AG1 | exact Hc | intros a Ha; apply OUT1; cbn in Ha; lia]. }
    assert (BY1 : bytes_at bsegs m1 A (zb s)).
    { eapply bytes_at_magree; [exact AG1 | exact BY | intros a Ha; apply OUT1; rewrite zb_length in Ha; lia]. }
    assert (SSP1 : ssp_cells m1 canary).
    { destruct SSP as [G1 G2]. split; (eapply rw_cells_magree; [exact AG1 | eassumption | intros a Ha; apply OUT1; unfold got_ssp, ssp_guard in Ha; cbn in Ha; lia]). }
    (* [comment removed for export] *)
    eapply implAM_post_evt.
    { eapply (fwrite_diag_proof (St:=St) RNG) with (lo := lo) (s := s); first
        [ exact towrite_proof | exact SF1 | exact BY1 | exact HF | reflexivity | exact ST1 | exact SSP1 | exact MI1 | exact RGimg | idtac ];
        rewrite ?unsigned_lit by lia; unfold zlength, FWRITE_DEPTH, GLOBALS_TOP;
        first [ exact BY1 | exact ST1 | reflexivity | lia | eapply rng_sub'; [exact RGstk | lia] | eapply rng_sub'; [exact RGimg | lia] ]. }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (v0 & v1 & v2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & SF2 & SSP2 & ->).
    rewrite ?unsigned_lit in MU2, ST2 by lia. fix_ret.
    (* [comment removed for export] *)
    pose proof (magree_of_munch bsegs _ _ _ MU2 WM2) as AG2.
    assert (OUT2 : forall a, (bv_unsigned sp - 2128 <= a /\ a < 2^47) \/ (a < 0x625000 /\ ~ (RSTDERR <= a < RSTDERR + 232)) ->
                             outside [(lo, bv_unsigned sp - 2128); (RSTDERR, RSTDERR + 232)] a) by (intros a Ha; cbn; lia).
    assert (FR2 : rw_cells bsegs m2 (bv_unsigned sp - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_magree; [exact AG2 | exact FR1 | intros a Ha; apply OUT2; cbn in Ha; lia]. }
    assert (STM2 : stk bsegs m2 (bv_unsigned sp - 2128) (bv_unsigned sp - 56)).
    { eapply stk_transport_disjoint; [exact STM1 | exact MU2 | exact WM2 | cbn; lia]. }
    (* [comment removed for export] *)
    assert (MU02 : munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m2).
    { apply (munch_trans _ m m1 m2).
      - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
      - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    pose proof (wmono_trans _ _ _ _ WM1 WM2) as WM02.
    assert (AW : appW [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]) by solve_appW.
    xport_env ENV MU02 WM02 as ENV2. pose proof (rodata_sh0_frame _ _ _ ROD MU02 WM02 AW) as ROD2.
    pose proof ENV2 as (Hgot2 & _ & Hshb2 & _ & Hlay2 & _).
    pose proof (rodata_sh0_rclean _ ROD2) as RCF2. destruct (rclean_shclean _ _ RCF2) as (UNP2 & _ & _ & APB2). cbn [r_lo r_hi r_rlo r_rhi RFMT] in UNP2, APB2.
    destruct ROD2 as [_ WRF2].
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (fwrite_i_post RNG) with (lo := lo) (res := 1) (size := Z.of_nat (length s)) (N := Z.of_nat (length s)) (RLO := 0x10000) (RHI := 0x210c0);
        rewrite ?unsigned_lit by lia;
        first [ exact MI2 | exact ST2 | exact STM2 | exact FR2 | exact Hgot2 | exact Hshb2 | exact Hlay2 | exact WRF2 | exact RGimg | exact RGstk
              | reflexivity | idtac ].
      all: first [ lia | exact KH | unfold KEND; lia
                 | eapply app_blk_sub; [exact APB2 | lia | lia | lia]
                 | eapply unpoisoned_sub; [exact UNP2 | lia | lia]
                 | unfold rrng, RFMT in RRF; cbn [r_rlo r_rhi] in RRF; exact RRF
                 | (eapply wr_at_sub; [exact WRF2| rewrite !shad_div; lia| rewrite !shad_div; lia| rewrite !shad_div; lia])
                 | (eapply wr_at_sub; [exact WRF2| rewrite !shad_div; lia| rewrite !shad_div; lia]) ]. }
    cbv beta. intros ms3 PO3.
    destruct PO3 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m3 & -> & MU3 & WM3 & MI3 & ST3).
    rewrite ?unsigned_lit in MU3 by lia.
    pose proof (magree_of_munch bsegs _ _ _ MU3 WM3) as AG3.
    assert (OUT3 : forall a, (bv_unsigned sp - 2128 <= a \/ a < lo) -> outside [(bv_unsigned sp - 2208, bv_unsigned sp - 2128)] a) by (intros a Ha; cbn; lia).
    apply evtF_done. unfold afwrite_diag_post.
    do 15 eexists. exists m3. split; [reflexivity|].
    split. { apply (munch_trans _ m m2 m3); [exact MU02|]. eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM02 | exact WM3]|]. split; [exact MI3|]. split; [exact ST3|].
    split. { destruct SF2 as (flags & mode & e & wend & tail & Hc & HR). exists flags, mode, e, wend, tail. split; [| exact HR].
             eapply rw_cells_magree; [exact AG3 | exact Hc | intros a Ha; apply OUT3; cbn in Ha; lia]. }
    split; [| reflexivity].
    destruct SSP2 as [G1 G2]. split; (eapply rw_cells_magree; [exact AG3 | eassumption | intros a Ha; apply OUT3; unfold got_ssp, ssp_guard in Ha; cbn in Ha; lia]).
  Qed.
End Fwrite.

Lemma forall_range_b : forall l, forallb (fun c => (0 <=? c) && (c <? 256))%bool l = true -> Forall (fun c => 0 <= c < 256) l.
Proof.
  intros l H. rewrite forallb_forall in H. apply Forall_forall. intros c Hc. specialize (H c Hc).
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Fprintf.
  Context {St : Type}.
  Hypothesis HSTRN : strnlen_a_stmt.     (* [comment removed for export] *)

  Definition afprintf_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : amem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : amem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ stderr_wfile m'
      /\ ssp_cells m' canary
      /\ st' = st.

  (* [comment removed for export] *)
  Lemma afprintf_core : forall RNG (rstk : region)
      (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x13 x14 x15 x16 x17 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m m1 : amem) (st : St) (A : Z) (fmt : list Z) (args : list parg) (ps : list (list Z)) (r : Z)
      (lo : Z) (canary : word) (j32 : list byte),
    let q := bv_unsigned sp - 112 in
    munch [(bv_unsigned sp - 2432, bv_unsigned sp)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo q ->
    rw_cells bsegs m1 q [CB 32 j32; C8 s2; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
    a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A ->
    stderr_wfile m1 -> ssp_cells m1 canary -> frm0 fc ->
    0x10000 + 64 <= A -> A + zlength fmt + 64 <= 0x210c0 ->
    bytes_at bsegs m1 A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    args_ok RSTDERR (q - 352) 80 RNG m1 lo q (q - VF_FRAME) [a2; a3; a4; a5; a6; a7] args ->
    printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
    (lo <= bv_unsigned sp - AFPRINTF_DEPTH) -> (KHIGH <= lo) -> (bv_unsigned sp < 2^47) ->
    ashenv m1 -> rclean m1 rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> rodata_sh0 m1 ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng0 RNG -> rrng RNG rstk -> rrng RNG RFMT ->
    implAM RNG (stderr_fprintf ps) st (afprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
           (MS (mkR (Z_to_bv 64 0x47a14) (Z_to_bv 64 q) gp tp t0 t1 t2 a1 a0 a0 a1 (Z_to_bv 64 (bv_unsigned sp - 48)) x13 x14 x15 x16 x17
                    (Z_to_bv 64 (bv_unsigned sp - 48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0xbce78) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until j32. cbv zeta.
    intros MU1 WM1 MI1 ST1 FR1 -> -> SF1 SSP1 FRM ALO AHI BYF HFF P1 AOK PP FPC LO KH SPHI ENV1 RCS1 RSlo RShi ROD1 RGstk RGimg RG0 RRS RRF.
    unfold AFPRINTF_DEPTH in *. pose proof KH as KH'. unfold KHIGH in KH'.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BYF) as AB. rewrite zb_length in AB. unfold zlength in *.
    (* [comment removed for export] *)
    unfold stderr_fprintf.
    apply (implAM_mono RNG _ st (fun _ st' ms' => afprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt st' ms'));
      [| intros [] st' ms' H; exact H].
    apply (stderr_bridgeA RNG ps [] st (fun st' ms' => afprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt st' ms')).
    (* [comment removed for export] *)
    pose proof (vfprintf_stderr_proof (St:=St) fwritex_stderr_proof stdio_write_flush_proof HSTRN) as VF.
    unfold vfprintf_stderr_stmt in VF. cbv zeta in VF.
    (* [comment removed for export] *)
    pose proof FR1 as FR1'.
    apply (proj1 (rw_cells_app bsegs _ _ [_;_;_;_;_] _)) in FR1'. destruct FR1' as [FRlo VAC]. cbn [cells_size csize Nat.add app] in VAC.
    replace (bv_unsigned sp - 112 + Z.of_nat 64)%Z with (bv_unsigned sp - 48)%Z in VAC by lia.
    pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
    change (le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a2; a3; a4; a5; a6; a7]) in VAA.
    (* [comment removed for export] *)
    eapply implAM_post_evt with
      (Q := fun _ bs ms' => vfprintf_stderr_post (Z_to_bv 64 0x47a14) (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp (Z_to_bv 64 A) (Z_to_bv 64 RSTDERR) (Z_to_bv 64 (bv_unsigned sp - 48))
                               s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m1 (snd bs) ms' /\ snd bs = st).
    { apply implAM_fold. eapply implF_mono.
      - eapply (implF_tforall bsegs (at_nodeA bsegs) fstepS RNG (fun rr => match rr with Ok qq => snd (snd qq) = st | Unr => True end));
          [apply outsk_flush_leaves|].
        apply implAM_unfold.
        eapply VF with (A := A) (VA := (bv_unsigned sp - 48)%Z) (fmt := fmt) (slots := [a2; a3; a4; a5; a6; a7]) (args := args)
                       (r := r) (lo := lo) (canary := canary) (rstk := rstk) (rfmt := RFMT);
          clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
        all: try reflexivity. all: try lia.
        all: try assumption.
        all: first [ exact VAA
                   | apply rodata_sh0_rclean; exact ROD1
                   | unfold inreg, RFMT; cbn; lia
                   | eapply rng_sub'; [exact RGstk | cbn; lia] ].
      - intros [|[[] [b st']]] RNG' ms'; cbn; intros [X EST]; [exact I | destruct X as [E P]; exact (conj E (conj P EST))]. }
    cbv beta. intros [] [buf st'] ms' [P EST]. cbn [snd] in P, EST. subst st'.
    unfold vfprintf_stderr_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MU3 & WM3 & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
    fix_ret.
    (* [comment removed for export] *)
    assert (FR3 : rw_cells bsegs m3 (bv_unsigned sp - 112) [CB 32 j32; C8 s2; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]).
    { eapply rw_cells_transport; [exact FR1 | exact MU3 | exact WM3 | cbn; lia]. }
    eapply evtF_cut.
    { eapply (fprintf_i_post RNG); rewrite ?unsigned_lit by lia; [exact MI3 | exact FR3 | reflexivity | eapply rng_sub'; [exact RGstk | lia]]. }
    cbv beta. intros ms' ->. rewrite !unsigned_lit by lia.
    replace (bv_unsigned sp - 112 + 112)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    (* [comment removed for export] *)
    release_frame FR3 ST3 (bv_unsigned sp).
    apply evtF_done. unfold afprintf_diag_post. cbn [fst snd].
    do 17 eexists. exists m3. split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m3).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | exact WM3]|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [assumption|]. split; [exact SF3|]. split; [exact SSP3| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Definition adiag_args (RNG : footprint) (d : diag_msg) (m : amem) (fmtp argw : word) (lo sp : Z) : Prop :=
    match d with
    | DUsage s | DCannotOpen s | DReadError s =>
        fmtp = Z_to_bv 64 (match d with DUsage _ => FMT_USAGE | DCannotOpen _ => FMT_CANTOPEN | _ => FMT_READERR end)
        /\ exists (slack : list byte) (r : region),
             bytes_at bsegs m (bv_unsigned argw) (zb s ++ Z_to_bv 8 0 :: slack)
             /\ Forall (fun c => 0 < c < 256) s
             /\ ((- (bv_unsigned argw + zlength s + 1)) mod 8 <= zlength slack)
             /\ (zlength s < INT_MAX - 256)
             /\ (bv_unsigned argw + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned argw)
             /\ (bv_unsigned argw + zlength s + 1 <= 2^47)                  (* [comment removed for export] *)
             /\ (GLOBALS_TOP <= bv_unsigned argw)
             /\ rclean m r /\ inreg r (bv_unsigned argw) (zlength s + 1 + zlength slack)
             /\ rng RNG (bv_unsigned argw) (zlength s + 1 + zlength slack) /\ rrng RNG r
    | DTooBig => fmtp = Z_to_bv 64 FMT_TOOBIG /\ bv_unsigned argw mod 2^32 = 67108864
    | _ => False
    end.

  Definition afprintf_diag_stmt : Prop :=
    forall RNG (rstk : region) (d : diag_msg)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : St) (lo : Z) (canary : word),
      stderr_wfile m ->
      a0 = Z_to_bv 64 RSTDERR -> adiag_args RNG d m a1 a2 lo (bv_unsigned sp) ->
      stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - AFPRINTF_DEPTH) -> (KHIGH <= lo) -> (bv_unsigned sp < 2^47) ->
      ssp_cells m canary -> mem_inv bsegs m -> frm0 fc ->
      ashenv m -> rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> rodata_sh0 m ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng0 RNG -> rrng RNG rstk -> rrng RNG RFMT ->
      implAM RNG (s_diag d) st
             (afprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 AFPRINTF) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma afprintf_s : forall (A n : Z) (fmt : list Z) (PIECES : list Z -> list (list Z)) (nf : Z),
    fprintf_i_pre_s_stmt A n ->
    0x10000 + 64 <= A -> A + zlength fmt + 64 <= 0x210c0 -> zlength fmt = n + 1 -> 0 <= n ->
    ro_bytes_b bsegs A (zb fmt) = true -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    (forall sarg, zlength sarg < INT_MAX - 256 -> printf_pieces fmt [PA_s sarg] = Some (PIECES sarg, nf + zlength sarg)) ->
    (forall sarg, fp_calls (length fmt) fmt [PA_s sarg] = []) ->
    forall RNG (rstk : region) (sarg : list Z)
           (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : St) (lo : Z) (canary : word),
      stderr_wfile m ->
      (exists (slack : list byte) (r : region),
             bytes_at bsegs m (bv_unsigned a2) (zb sarg ++ Z_to_bv 8 0 :: slack)
             /\ Forall (fun c => 0 < c < 256) sarg
             /\ ((- (bv_unsigned a2 + zlength sarg + 1)) mod 8 <= zlength slack)
             /\ (zlength sarg < INT_MAX - 256)
             /\ (bv_unsigned a2 + zlength sarg + 1 + zlength slack <= lo \/ bv_unsigned sp <= bv_unsigned a2)
             /\ (bv_unsigned a2 + zlength sarg + 1 <= 2^47)                  (* [comment removed for export] *)
             /\ (GLOBALS_TOP <= bv_unsigned a2)
             /\ rclean m r /\ inreg r (bv_unsigned a2) (zlength sarg + 1 + zlength slack)
             /\ rng RNG (bv_unsigned a2) (zlength sarg + 1 + zlength slack) /\ rrng RNG r) ->
      stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - AFPRINTF_DEPTH) -> (KHIGH <= lo) -> (bv_unsigned sp < 2^47) ->
      ssp_cells m canary -> mem_inv bsegs m -> frm0 fc ->
      ashenv m -> rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> rodata_sh0 m ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng0 RNG -> rrng RNG rstk -> rrng RNG RFMT ->
      evtF bsegs RNG (fun ms' => implAM RNG (stderr_fprintf (PIECES sarg)) st
                                        (afprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st) ms')
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 RSTDERR) (Z_to_bv 64 A) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x47954) fc None m (seg_rom bsegs)).
  Proof.
    intros A n fmt PIECES nf PRE ALO AHI NLEN N0 ROB HFF P1 PP FPC.
    intros RNG rstk sarg. intros until canary.
    intros SF DA ST LO KH SPHI SSP MI FRM ENV RCS RSlo RShi ROD RGstk RGimg RG0 RRS RRF.
    unfold AFPRINTF_DEPTH in *. pose proof KH as KH'. unfold KHIGH in KH'.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof ENV as (Hgot & Hric & Hshb & Hini & Hlay & Hrmem & Hrpf & Hrwcs & Hrread & Hrfw & Hrsl & Hrmc & Hckp & Hisl).
    assert (AW1 : appW [(bv_unsigned sp - 2432, bv_unsigned sp)]) by solve_appW.
    pose proof (zb_length fmt) as LZF. unfold zlength in *.
    destruct DA as (slack & r & BY & HF & SLK & LEN & DJ & T47 & GA & RC & IR & RGs & RRr).
    pose proof (rclean_shclean _ _ RC) as (UNPr & HULr & WRr & APBr). unfold hull64 in HULr. unfold inreg in IR.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite length_app, zb_length in AB. cbn [length] in AB.
    pose proof (zlength_nonneg' slack) as SL0. unfold GLOBALS_TOP in GA. unfold zlength in *.
    (* [comment removed for export] *)
    assert (FZ : shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0)) by (apply (rodata_sh0_fmt _ A n ROD); lia).
    assert (RSHF : rng RNG (shad (A - 64)) (shad (A + n + 64) - shad (A - 64))).
    { unfold rrng, RFMT in RRF. cbn [r_rlo r_rhi] in RRF. eapply rng_sub'; [exact RRF|]. rewrite !shad_div. unfold ASHOFF. lia. }
    (* [comment removed for export] *)
    assert (BY0 : bytes_at bsegs m (bv_unsigned a2) (zb sarg ++ [Z_to_bv 8 0])).
    { pose proof BY as BY'. rewrite <- (firstn_skipn (length (zb sarg) + 1) (zb sarg ++ Z_to_bv 8 0 :: slack)) in BY'.
      apply bytes_at_app in BY'. destruct BY' as [BY' _].
      rewrite firstn_app, firstn_all2, Nat.add_comm, Nat.add_sub in BY' by lia. cbn [firstn Nat.add] in BY'. exact BY'. }
    assert (NZ : Forall (fun b : byte => bv_unsigned b <> 0) (zb sarg)).
    { unfold zb. apply Forall_forall. intros b Hb. apply in_map_iff in Hb. destruct Hb as (c & <- & Hc).
      pose proof (proj1 (Forall_forall _ _) HF c Hc) as Hc'. cbv beta in Hc'.
      rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Z.mod_small by (unfold bv_modulus; cbn; lia). lia. }
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (PRE RNG) with (lo := lo) (sstr := zb sarg) (RLO := r_rlo r) (RHI := r_rhi r);
        rewrite ?length_app, ?zb_length; cbn [length];
        first [ exact MI | exact ST | exact KH | exact FZ | exact BY0 | exact NZ | exact WRr | exact RGimg | exact RGstk | exact RSHF | exact RRr
              | reflexivity | idtac ].
      all: first [ assumption
                 | lia
                 | unfold INT_MAX in *; lia
                 | eapply app_blk_sub; [exact APBr | lia | lia | lia]
                 | eapply unpoisoned_sub; [exact UNPr | lia | lia]
                 | unfold KEND in *; lia
                 | eapply rng_sub'; [exact RGs | lia] ]. }
    cbv beta. intros ms1 MID.
    destruct MID as (u0 & u1 & u2 & x13 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & m1 & j32 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & INI1).
    apply evtF_done.
    (* [comment removed for export] *)
    pose proof (magree_of_munch bsegs _ _ _ MU1 WM1) as AG1.
    assert (OUT1 : forall a, (a < lo \/ bv_unsigned sp <= a \/ a < 0x625000) -> outside [(bv_unsigned sp - 2432, bv_unsigned sp)] a) by (intros a Ha; cbn; lia).
    xport_env ENV MU1 WM1 as ENV1. xport_reg RCS MU1 WM1 as RCS1. xport_reg RC MU1 WM1 as RC1.
    pose proof (rodata_sh0_frame _ _ _ ROD MU1 WM1 AW1) as ROD1.
    eapply (afprintf_core RNG rstk) with (m := m) (m1 := m1) (A := A) (fmt := fmt) (args := [PA_s sarg]) (ps := PIECES sarg)
             (r := nf + Z.of_nat (length sarg)) (lo := lo) (canary := canary) (j32 := j32);
      first [ exact MU1 | exact WM1 | exact MI1 | exact ST1 | exact FR1 | reflexivity | exact FRM | exact ENV1 | exact RCS1 | exact ROD1 | exact HFF | exact P1
            | idtac ].
    all: try assumption.
    all: try (unfold zlength, AFPRINTF_DEPTH in *; lia).
    - destruct SF as (flags & mode & e & wend & tail & Hc & HR). exists flags, mode, e, wend, tail. split; [| exact HR].
      eapply rw_cells_magree; [exact AG1 | exact Hc | intros a Ha; apply OUT1; cbn in Ha; lia].
    - destruct SSP as [G1 G2]. split; (eapply rw_cells_magree; [exact AG1 | eassumption | intros a Ha; apply OUT1; unfold got_ssp, ssp_guard in Ha; cbn in Ha; lia]).
    - apply fmt_bytes_at; [exact MI1 | exact ROB | lia | unfold zlength; lia].
    - cbn [args_ok arg_ok]. split; [|exact I]. exists slack. unfold zlength. rewrite ?unsigned_lit by lia. unfold VF_FRAME.
      repeat match goal with |- _ /\ _ => split end;
        first [ assumption | lia
              | eapply bytes_at_magree; [exact AG1 | exact BY | intros a Ha; apply OUT1; rewrite length_app, zb_length in Ha; cbn [length] in Ha; lia]
              | exists r; split; [exact RC1|]; split; [unfold inreg; lia| exact RRr] ].
    - unfold zlength in PP. apply PP. lia.
    - apply FPC.
  Qed.

  Theorem afprintf_diag_proof : afprintf_diag_stmt.
  Proof.
    intros RNG rstk d. intros until canary. intros SF -> DA ST LO KH SPHI SSP MI FRM ENV RCS RSlo RShi ROD RGstk RGimg RG0 RRS RRF.
    unfold AFPRINTF. ienterF. zs.
    destruct d as [argv0 | path | path | | | |]; cbn [adiag_args] in DA; try contradiction; unfold s_diag.
    - (* [comment removed for export] *)
      destruct DA as [-> DA].
      eapply (afprintf_s FMT_USAGE 16 FMT_usage pieces_usage 14 fprintf_i_pre_usage); try eassumption; try reflexivity;
        first [ unfold FMT_USAGE; lia | lia | replace (zlength FMT_usage) with 17 by reflexivity; unfold FMT_USAGE; lia
              | apply forall_range_b; vm_compute; reflexivity | intros; apply printf_pieces_usage; assumption ].
    - (* [comment removed for export] *)
      destruct DA as [-> DA].
      eapply (afprintf_s FMT_CANTOPEN 20 FMT_cannot_open pieces_cannot_open 18 fprintf_i_pre_cantopen); try eassumption; try reflexivity;
        first [ unfold FMT_CANTOPEN; lia | lia | replace (zlength FMT_cannot_open) with 21 by reflexivity; unfold FMT_CANTOPEN; lia
              | apply forall_range_b; vm_compute; reflexivity | intros; apply printf_pieces_cannot_open; assumption ].
    - (* [comment removed for export] *)
      destruct DA as [-> DA].
      eapply (afprintf_s FMT_READERR 22 FMT_read_error pieces_read_error 20 fprintf_i_pre_readerr); try eassumption; try reflexivity;
        first [ unfold FMT_READERR; lia | lia | replace (zlength FMT_read_error) with 23 by reflexivity; unfold FMT_READERR; lia
              | apply forall_range_b; vm_compute; reflexivity | intros; apply printf_pieces_read_error; assumption ].
    - (* [comment removed for export] *)
      destruct DA as [-> Hu].
      unfold AFPRINTF_DEPTH in *. pose proof KH as KH'. unfold KHIGH in KH'.
      pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
      pose proof ENV as (Hgot & Hric & Hshb & Hini & Hlay & Hrmem & Hrpf & Hrwcs & Hrread & Hrfw & Hrsl & Hrmc & Hckp & Hisl).
      assert (AW1 : appW [(bv_unsigned sp - 2432, bv_unsigned sp)]) by solve_appW.
      assert (FZ : shadow_bytes m (shad (FMT_TOOBIG - 64)) (shad (FMT_TOOBIG + 32 + 64)) (fun _ => 0)) by (apply (rodata_sh0_fmt _ FMT_TOOBIG 32 ROD); unfold FMT_TOOBIG; lia).
      assert (RSHF : rng RNG (shad (FMT_TOOBIG - 64)) (shad (FMT_TOOBIG + 32 + 64) - shad (FMT_TOOBIG - 64))).
      { unfold rrng, RFMT in RRF. cbn [r_rlo r_rhi] in RRF. eapply rng_sub'; [exact RRF|]. rewrite !shad_div. unfold ASHOFF, FMT_TOOBIG. lia. }
      eapply evtF_cut.
      { eapply (fprintf_i_pre_toobig RNG) with (lo := lo);
          first [ exact MI | exact ST | exact KH | exact FZ | exact RGimg | exact RGstk | exact RSHF | reflexivity | assumption | lia ]. }
      cbv beta. intros ms1 MID.
      destruct MID as (u0 & u1 & u2 & x13 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & m1 & j32 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & INI1).
      apply evtF_done.
      pose proof (magree_of_munch bsegs _ _ _ MU1 WM1) as AG1.
      assert (OUT1 : forall a, (a < lo \/ bv_unsigned sp <= a \/ a < 0x625000) -> outside [(bv_unsigned sp - 2432, bv_unsigned sp)] a) by (intros a Ha; cbn; lia).
      xport_env ENV MU1 WM1 as ENV1. xport_reg RCS MU1 WM1 as RCS1.
      pose proof (rodata_sh0_frame _ _ _ ROD MU1 WM1 AW1) as ROD1.
      eapply (afprintf_core RNG rstk) with (m := m) (m1 := m1) (A := FMT_TOOBIG) (fmt := FMT_too_big) (args := [PA_u 67108864]) (ps := pieces_too_big)
               (r := 38) (lo := lo) (canary := canary) (j32 := j32);
        first [ exact MU1 | exact WM1 | exact MI1 | exact ST1 | exact FR1 | reflexivity | exact FRM | exact ENV1 | exact RCS1 | exact ROD1
              | exact printf_pieces_too_big | idtac ].
      all: try assumption.
      all: try (replace (zlength FMT_too_big) with 33 by reflexivity; unfold FMT_TOOBIG, AFPRINTF_DEPTH in *; lia).
      + destruct SF as (flags & mode & e & wend & tail & Hc & HR). exists flags, mode, e, wend, tail. split; [| exact HR].
        eapply rw_cells_magree; [exact AG1 | exact Hc | intros a Ha; apply OUT1; cbn in Ha; lia].
      + destruct SSP as [G1 G2]. split; (eapply rw_cells_magree; [exact AG1 | eassumption | intros a Ha; apply OUT1; unfold got_ssp, ssp_guard in Ha; cbn in Ha; lia]).
      + apply fmt_bytes_at; [exact MI1 | vm_compute; reflexivity | unfold FMT_TOOBIG; lia | replace (zlength FMT_too_big) with 33 by reflexivity; unfold FMT_TOOBIG; lia].
      + apply forall_range_b. vm_compute. reflexivity.
      + cbn [args_ok arg_ok]. split; [|exact I]. split; [lia | exact Hu].
  Qed.
End Fprintf.
End CANSEC1.
