(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image MState Frame SysStep RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg Shapi1s PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j AIcpnnp AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img A_ImgAny.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require DA_Se7o DA_S5tv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Walk.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Se7o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_S5tv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk.DA_Hbsz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Eg3i DA_Cells DA_Ldix DA_Entry DA_Mib4 DA_Inv DA_Ejgo DA_Main DA_Am90 DA_FKit.

Module DA_Fpom.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr SysStep RzBridge MState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec RelSpec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct Lazyiq4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Se7o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Eg3i DA_Cells DA_Ldix DA_S5p6.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes.DA_Myrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ldix OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_S5p6.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac icall_consts_in H ::= unfold tryinit_post, region_is_poisoned_post in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma a0_frame_join : forall m A B cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 -> B = (A + Z.of_nat (cells_size cs1))%Z -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] R1] [[W2 B2] R2] ->. split; [split|].
  - apply cells_wf_app. tauto.
  - rewrite cells_bytes_app. apply bytes_at_app. rewrite (cells_bytes_length cs1 W1). tauto.
  - rewrite cells_size_app, Nat2Z.inj_add. destruct R1 as (R10 & R11 & R12), R2 as (R20 & R21 & R22).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))); [apply R12; lia|].
    replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply R22. lia.
Qed.
Ltac a0_join :=
  match goal with
  | F0 : rw_cells _ ?m ?A [CB 1976 ?j], F1 : rw_cells _ ?m ?B (C8 _ :: _) |- _ =>
      let FRJ := fresh "FRJ" in
      pose proof (a0_frame_join m A B _ _ F0 F1 ltac:(cbn [cells_size csize Nat.add]; repeat match goal with H : _ |- _ => clear H end; lia)) as FRJ;
      cbn [app] in FRJ; clear F0 F1
  end.

Section Walks.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (lo : Z) (pa len : Z).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + 2600 <= bv_unsigned sp.
  Hypothesis PAR : 0x10000 <= pa /\ pa + len <= 0x35000.
  Hypothesis LENR : 1 <= len <= 64.
  #[local] Notation rom := (seg_rom rsegs).
  #[local] Notation FRAME m1 junk s0v s1v s2v s3v s4v s5v :=
    (rw_cells rsegs m1 (bv_unsigned sp + -2032) [CB 1976 junk; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]).
  #[local] Notation FRAME0 m1 junk0 := (rw_cells rsegs m1 (bv_unsigned sp + -2128) [CB 96 junk0]).
  #[local] Notation FRAME1 m1 junk1 := (rw_cells rsegs m1 (bv_unsigned sp + -2192)
      [CB 8 junk1; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 STDERR_F); C8 (Z_to_bv 64 pa); C8 (Z_to_bv 64 len); C8 sp; C8 (Z_to_bv 64 0x498d0)]).

  (* [comment removed for export] *)
  Definition fw1_post (s0 s1 s2 s3 s4 s5 : word) (mo : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mo' junk junk0 junk1 m',
      ms' = MS (mkR (Z_to_bv 64 0x9e1c8) (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 len)
                    (Z_to_bv 64 STDERR_F) (Z_to_bv 64 pa) (Z_to_bv 64 len) a3' a4' a5' a6' a7'
                    (Z_to_bv 64 len) (Z_to_bv 64 STDERR_F) (Z_to_bv 64 1) (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 STDIO_WRITE) fc None m' rom
      /\ munch [(bv_unsigned sp - 2600, bv_unsigned sp); (STDERR_F, STDERR_F + 152)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp + -2192)
      /\ FRAME m' junk s0 s1 s2 s3 s4 s5 /\ FRAME0 m' junk0 /\ FRAME1 m' junk1
      /\ file_at m' STDERR_F (mf_set_mode (mf_set_w stderr0 (Z_to_bv 64 STDERR_BUFP) (Z_to_bv 64 STDERR_BUFP) (Z_to_bv 64 STDERR_BUFP)) mo').

  #[using="LENR PAR LO CEIL Clg"] Lemma fw_walk1 : forall (t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) (m : word -> option byte) (w : word) (mo : Z),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> asan_inited_cell m ->
    ro_cells rsegs m REAL_FWRITE_CELL [C8 (Z_to_bv 64 MUSL_FWRITE)] ->
    file_at m STDERR_F (mf_set_mode (mf_set_w stderr0 w w w) mo) -> (w = w0 \/ w = Z_to_bv 64 STDERR_BUFP) ->
    evt rsegs (fw1_post s0 s1 s2 s3 s4 s5 mo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pa) (Z_to_bv 64 len) (Z_to_bv 64 1) (Z_to_bv 64 STDERR_F) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FWRITE_ICPT_ENTRY) fc None m rom).
  Proof.
    pose proof PAR as PARdep. pose proof LENR as LENRdep.   (* [comment removed for export] *)
    intros until mo. intros MI ST INI RR FILE WR.
    unfold asan_inited_cell in INI. unfold REAL_FWRITE_CELL, MUSL_FWRITE, FWRITE_ICPT_ENTRY in *.
    (* [comment removed for export] *)
    cbv [file_at file_cells stderr0 mf_set_mode mf_set_w mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148] in FILE.
    unfold file_at, file_cells, stderr0, mf_set_mode, mf_set_w, STDERR_F, STDERR_BUFP, STDIO_WRITE, w0 in *.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 2600, bv_unsigned sp); (0xad308, 0xad308 + 152)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    bstep. carve_frame 56%nat ST. carve_frame 1976%nat ST. run_to 0x49898. at_pc 0x49898. a0_join. carve_frame 96%nat ST.
    run_to 0x5fce0. at_pc 0x5fce0.
    icall tryinit_spec by (rewrite ?unsigned_lit by lia; first [exact INI | exact ST | exact CEIL | eassumption | lia]).
    run_to 0x9e140. at_pc 0x9e140.
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST1 end.
    carve_frame 64%nat ST1.
    run_to 0x9e174. at_pc 0x9e174. azstep. if_cases K0; zify_cond K0. 2:{ exfalso. try (generalize alloc_ceiling_val); clear -K0. lia. } clear K0.
    run_to 0x9e008. at_pc 0x9e008. carve_frame 64%nat ST1.
    run_to 0x9e038. at_pc 0x9e038.
    destruct WR as [-> | ->].
    - azstep. br_taken. run_to 0x9e210. at_pc 0x9e210. azstep. br_not_taken. run_to 0x9e0c4. at_pc 0x9e0c4. azstep. br_taken.
      run_to 0x9e044. at_pc 0x9e044. azstep. br_not_taken. run_to 0x9e078. at_pc 0x9e078.
      lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -2256) _ |- _ => release_frame H ST1 (bv_unsigned sp + -2192) end.
      azstep. replace (1 * len) with len by lia. apply evt_done. cbv [fw1_post file_at file_cells stderr0 mf_set_mode mf_set_w mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148].
      unfold fw1_post, file_at, file_cells, stderr0, mf_set_mode, mf_set_w, STDERR_F, STDERR_BUFP, STDIO_WRITE, w0.
      hot_eexists_all. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
    - azstep. br_not_taken. run_to 0x9e044. at_pc 0x9e044. azstep. br_not_taken. run_to 0x9e078. at_pc 0x9e078.
      lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -2256) _ |- _ => release_frame H ST1 (bv_unsigned sp + -2192) end.
      azstep. replace (1 * len) with len by lia. apply evt_done. cbv [fw1_post file_at file_cells stderr0 mf_set_mode mf_set_w mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148].
      unfold fw1_post, file_at, file_cells, stderr0, mf_set_mode, mf_set_w, STDERR_F, STDERR_BUFP, STDIO_WRITE, w0.
      hot_eexists_all. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition fw2_post (s0v s1v s2v s3v s4v s5v : word) (m1 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' rom
      /\ munch [(bv_unsigned sp - 2600, bv_unsigned sp)] m1 m' /\ wmono rsegs m1 m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp).

  Section Tail.
    Variables (s0v s1v s2v s3v s4v s5v : word) (m1 : word -> option byte) (junk junk0 junk1 : list byte) (ng : nat) (lastb : Z) (w1 w2 : word).
    Hypothesis MI1 : mem_inv rsegs m1.
    Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2192).
    Hypothesis FR : FRAME m1 junk s0v s1v s2v s3v s4v s5v.  Hypothesis FR0 : FRAME0 m1 junk0.  Hypothesis FR1 : FRAME1 m1 junk1.
    Hypothesis Gsh : ro_cells rsegs m1 0xa8b70 [C8 (Z_to_bv 64 0xb4bb8)].
    Hypothesis Csh : ro_cells rsegs m1 0xb4bb8 [C8 (Z_to_bv 64 0x7fff8000)].
    Hypothesis Gmb : ro_cells rsegs m1 0xa8b78 [C8 (Z_to_bv 64 0xb58a8)].
    Hypothesis Cmb : ro_cells rsegs m1 0xb58a8 [C8 (Z_to_bv 64 0)].
    Hypothesis Gme : ro_cells rsegs m1 0xa8b80 [C8 (Z_to_bv 64 0xb58b0)].
    Hypothesis Cme : ro_cells rsegs m1 0xb58b0 [C8 (Z_to_bv 64 0)].
    Hypothesis Ghe : ro_cells rsegs m1 0xa8b88 [C8 (Z_to_bv 64 0xb58a0)].
    Hypothesis Che : ro_cells rsegs m1 0xb58a0 [C8 (Z_to_bv 64 0x7fffffffffff)].
    Hypothesis IR : inmem_range pa len.
    Hypothesis NG : ((pa + len - 1) / 8 - pa / 8 = Z.of_nat ng)%Z.
    Hypothesis SH1 : bytes_at rsegs m1 (pa / 8 + shadow_off) (zeros ng ++ [Z_to_bv 8 lastb]).
    Hypothesis LB : (lastb = 0 \/ ((pa + len - 1) mod 8 < lastb <= 7))%Z.
    Hypothesis QB1 : bytes_at rsegs m1 (sha pa - sha pa mod 8) (le8 w1).
    Hypothesis QB2 : bytes_at rsegs m1 (sha (pa + len + -1) - sha (pa + len + -1) mod 8) (le8 w2).
    #[local] Notation POST := (fw2_post s0v s1v s2v s3v s4v s5v m1).

    (* [comment removed for export] *)
    #[using="ng LENR PAR LO CEIL len pa Clg"] Lemma fw_exit : forall m2 x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
      mem_inv rsegs m2 -> munch [(bv_unsigned sp - 2600, bv_unsigned sp)] m1 m2 -> wmono rsegs m1 m2 ->
      stk rsegs m2 lo (bv_unsigned sp + -2128) -> FRAME m2 junk s0v s1v s2v s3v s4v s5v -> FRAME0 m2 junk0 ->
      evt rsegs POST
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x49934) fc None m2 rom).
    Proof.
      intros until x31. intros MI2 MU2 WM2 ST2 FR2 FR02.
      assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
      azstep. release_frame FR02 ST2 (bv_unsigned sp + -2032).
      run_to 0x49958. at_pc 0x49958. release_frame FR2 ST2 (bv_unsigned sp).
      bstep. apply evt_done. unfold fw2_post.
      hot_eexists_all. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
    Qed.

    (* [comment removed for export] *)
    #[using="LB SH1 NG IR Che Ghe Cme Gme Cmb Gmb Csh Gsh FR1 FR0 FR ST1 MI1 lastb ng junk1 junk0 junk LENR PAR LO CEIL Clg"] Lemma fw_region : forall x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31,
      evt rsegs POST
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp (Z_to_bv 64 len) (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 pa) (Z_to_bv 64 STDERR_F) (Z_to_bv 64 (bv_unsigned sp + -2128)) x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x49a10) fc None m1 rom).
    Proof.
      intros. assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
      pose proof ST1 as ST1'. release_frame FR1 ST1' (bv_unsigned sp + -2128).
      pose proof (munch_refl [(bv_unsigned sp - 2600, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
      azstep. azstep. azstep. azstep.
      try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_QB1); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_QB2); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_SH1); icall region_is_poisoned_spec by (rewrite ?unsigned_lit by lia;
        first [ repeat (split; [assumption|]); assumption
              | exact ST1' | exact CEIL | exact MI1 | exact IR
              | first [ hotw_ex2 ng lastb | exists ng, lastb ]; split; [exact NG| split; [exact SH1| exact LB]]
              | lia ]).
      azstep. br_taken. azstep. azstep.
      eapply fw_exit; eassumption.
    Qed.

    Section Slow.
      Variables (sf sl : Z).
      Hypothesis ESF : (sf = pa / 8 + shadow_off)%Z.
      Hypothesis ESL : (sl = sf + Z.of_nat ng)%Z.
      #[local] Notation ATS pc x11 x13 x14 x1 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 :=
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp (Z_to_bv 64 len) (Z_to_bv 64 1)
                 x11 (Z_to_bv 64 sl) x13 x14 x15 x16 x17 (Z_to_bv 64 pa) (Z_to_bv 64 STDERR_F) (Z_to_bv 64 (bv_unsigned sp + -2128))
                 (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 pc) fc None m1 rom) (only parsing).

      #[using="FR1 FR0 FR ST1 MI1 ng junk1 junk0 junk LENR PAR LO CEIL Clg"] Lemma fw_slow_end : forall x11 x14 x1 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31,
        evt rsegs POST (ATS 0x49a08 x11 (Z_to_bv 64 0) x14 x1 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31).
      Proof.
        intros. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
        azstep. azstep. if_cases K; zify_cond K.
        - pose proof ST1 as ST1'. release_frame FR1 ST1' (bv_unsigned sp + -2128).
          eapply fw_exit; try eassumption; [apply munch_refl | apply wmono_refl].
        - exfalso. clear -K. cbv in K. first [lia | congruence].
      Qed.

      #[using="ESL ESF SH1 FR1 FR0 FR ST1 MI1 lastb junk1 junk0 junk LENR PAR LO CEIL Clg"] Lemma fw_slow_loop : forall (cc : nat) (j : Z) x11 x14 x1 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31,
        Z.to_nat (Z.of_nat ng - j) = cc -> (0 <= j < Z.of_nat ng)%Z -> x11 = Z_to_bv 64 (sf + j) ->
        evt rsegs POST (ATS 0x499f8 x11 (Z_to_bv 64 0) x14 x1 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31).
      Proof.
        induction cc as [|cc IH]; intros j x11 x14 x1 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 Hc Hj ->; [lia|].
        pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (bytes_at_bound _ _ _ _ SH1) as SB.
        rewrite length_app, zeros_length in SB. cbn [length] in SB.
        pose proof (u8ro_read rsegs m1 (pa / 8 + shadow_off) _ j (Z_to_bv 8 0) (Z_to_bv 64 (sf + j)) SH1) as RD.
        specialize (RD ltac:(rewrite (shadow_nth ng lastb (Z.to_nat j)) by lia;
                               replace (Z.to_nat j <? ng)%nat with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity)
                       ltac:(lia) ltac:(unfold wa; f_equal; lia)).
        azstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        azstep. azstep.
        azstep. if_cases K; zify_cond K.
        - apply (IH (j + 1)%Z); [lia|lia|f_equal; lia].
        - apply fw_slow_end.
      Qed.
    End Slow.

    (* [comment removed for export] *)
    #[using="QB2 QB1 LB SH1 NG IR Che Ghe Cme Gme Cmb Gmb Csh Gsh FR1 FR0 FR ST1 MI1 w2 w1 lastb ng junk1 junk0 junk LENR PAR LO CEIL pa Clg"] Lemma fw_tail : forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      evt rsegs POST
        (MS (mkR (Z_to_bv 64 0x9e1c8) (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 len)
                 (Z_to_bv 64 len) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 len) (Z_to_bv 64 STDERR_F) (Z_to_bv 64 1) (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x9e1c8) fc None m1 rom).
    Proof.
      pose proof PAR as PARdep. pose proof LENR as LENRdep.
      intros. unfold STDERR_F.
      assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
      assert (AF : (0 <= pa /\ pa + len + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
      pose proof (bytes_at_bound _ _ _ _ SH1) as SB. rewrite length_app, zeros_length in SB. cbn [length] in SB.
      assert (QH1 : (sha pa - sha pa mod 8 + Z.of_nat (length (le8 w1)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
      assert (QH2 : (sha (pa + len + -1) - sha (pa + len + -1) mod 8 + Z.of_nat (length (le8 w2)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
      pose proof ST1 as ST1'. pose proof FR1 as FR1'. unfold STDERR_F in FR1'.
      azstep. azstep. br_taken. run_to 0x9e1f4. at_pc 0x9e1f4. release_frame FR1' ST1' (bv_unsigned sp + -2128). azstep.
      replace (Z.b2z (len <? 1)) with 0 by (rewrite (proj2 (Z.ltb_ge len 1)) by lia; reflexivity).
      change (Z.land ((0 + -1) mod 18446744073709551616) 1) with 1.
      azstep. br_not_taken. azstep. br_not_taken. azstep. replace (1 * len) with len by lia. azstep. azstep. azstep.
      azstep. if_cases Kb; zify_cond Kb. { exfalso. rewrite zb_lxor_ones in Kb by lia. lia. } clear Kb.
      azstep. azstep. azstep. if_cases K2; zify_cond K2.
      - (* [comment removed for export] *)
        azstep. br_taken. unfold STDERR_F in *. apply fw_region.
      - (* [comment removed for export] *)
        assert (HS1 : (0 <= Z.shiftr pa 3 <= pa)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
        assert (HS2 : (0 <= Z.shiftr (pa + len + -1) 3 <= pa + len - 1)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
        do 9 azstep.
        pose proof (qc_read _ _ _ QB1 ltac:(lia)) as RD1.
        pose proof (qc_read _ _ _ QB2 ltac:(lia)) as RD2.
        azstep. azstep. azstep. azstep. azstep.
        azstep. if_cases K7; zify_cond K7.
        + (* [comment removed for export] *)
          assert (LBR : (0 <= lastb < 128)%Z) by lia.
          pose proof (u8ro_read rsegs _ (pa / 8 + shadow_off) _ (Z.of_nat ng) (Z_to_bv 8 lastb)
                        (Z_to_bv 64 (2147450880 + Z.shiftr (pa + len + -1) 3)) SH1) as RD.
          specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ng lastb ng), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                         ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
          azstep. rewrite sxb_small by lia.
          azstep. azstep. azstep. azstep. azstep.
          rewrite (poisoned_last_zero (pa + len + -1) lastb) by
            (first [lia | destruct LB as [LB0|LB1]; [left; exact LB0| right; replace (pa + len + -1)%Z with (pa + len - 1)%Z by lia; lia]]).
          rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
          set (sf := (2147450880 + pa / 8)%Z). set (sl := (2147450880 + (pa + len + -1) / 8)%Z).
          assert (ESF : (sf = pa / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
          assert (ESL : (sl = sf + Z.of_nat ng)%Z) by (unfold sf, sl; mlia).
          clearbody sf sl. unfold STDERR_F in *.
          azstep. if_cases K8; zify_cond K8.
          * eapply fw_slow_end; eassumption.
          * eapply fw_slow_loop with (j := 0%Z); try eassumption; try reflexivity; try lia. f_equal; lia.
        + (* [comment removed for export] *)
          unfold STDERR_F in *. eapply fw_exit; try eassumption; [apply munch_refl | apply wmono_refl].
    Qed.
  End Tail.
End Walks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac icall_consts_in H ::= unfold tryinit_post, region_is_poisoned_post, fw1_post, fw2_post, STDERR_F, STDIO_WRITE in H.

Section Leaves.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)

  Lemma fwrite_icpt_cells_of_consts : forall v, consts_hold LPA v -> (exists g, ro_cells rsegs v SSP_GUARD [C8 g]) -> fwrite_icpt_cells v.
  Proof.
    intros v CH CAN. split; [apply asan_inited_cell_of_bytes; apply (consts_lookup v _ _ CH); vm_compute; reflexivity|].
    split; [apply ro_C8_of_bytes; apply (consts_lookup v _ _ CH); vm_compute; reflexivity|].
    split; [exact (map_cells_of_consts v CH)|]. split; [exact CAN|].
    apply ro_C8_of_bytes. apply (consts_lookup v _ _ CH). vm_compute. reflexivity.
  Qed.

  Lemma fwrite_diag_ok : fwrite_diag_stmt.
  Proof.
    unfold fwrite_diag_stmt. intros until K. cbv zeta.
    intros AINV MI CELLS A0 A1 A2 A3 LEN PALO PAHI PB RNG FILE SOK FDL ST LO CEIL SPHI HK HKONT.
    (first [ dand5 CELLS as INI RR MC [g CAN] GOT | destruct CELLS as (INI & RR & MC & [g CAN] & GOT) ]). (first [ dex2 SOK as w mo; destruct SOK as [-> WR] | dand4 SOK as w mo -> WR | destruct SOK as (w & mo & -> & WR) ]).
    unfold FWRITE_ICPT_STACK in *. subst a0 a1 a2 a3.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    pose proof INI as INI'. unfold asan_inited_cell in INI'. pose proof RR as RR'. unfold REAL_FWRITE_CELL, MUSL_FWRITE in RR'.
    pose proof MC as MC'. open_map_cells MC'. pose proof CAN as CAN'. unfold SSP_GUARD in CAN'. pose proof GOT as GOT'. unfold SSP_GOT, SSP_GUARD in GOT'.
    pose proof (munch_refl [(bv_unsigned sp - 2600, bv_unsigned sp); (STDERR_F, STDERR_F + 152)] (aview A m)) as MU. unfold STDERR_F in MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) [(bv_unsigned sp - 2600, bv_unsigned sp); (709384, 709384 + 152)]).
    { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|]. eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]. }
      split; [| exact I]. right. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
    (* [comment removed for export] *)
    ago AINV. fold_cl_segs.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_CAN); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_GOT); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_RR); icall (fw_walk1 ra sp gp tp s6 s7 s8 s9 s10 s11 F fc lo pa (Z.of_nat (length msg)) CEIL LO (conj PALO PAHI) ltac:(lia)
             t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 (aview A m) w mo)
      by (first [exact MI | exact ST | exact INI' | exact RR' | exact FILE | exact WR | lia]).
    lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -2032) _ |- _ => rename H into FRa end.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -2128) _ |- _ => rename H into FRb end.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -2192) _ |- _ => rename H into FRc end.
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    lazymatch goal with H : file_at _ _ _ |- _ => rename H into FILE1 end.
    astopx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_3; dand3 dR_3 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    (* [comment removed for export] *)
    lazymatch type of FILE1 with file_at _ _ ?fr =>
    eapply (stdio_write_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 md1 A
              STDERR_F fr [] msg pa STDERR_BUFP lo K AINV1 MI1 eq_refl eq_refl eq_refl FILE1) end;
      [ right; reflexivity
      | unfold STDERR_F; lia | unfold STDERR_F, SSP_GUARD; lia
      | unfold STDERR_F; split; [cbn; lia|]; split; [cbn; lia|]; intros a Ha; cbn [cl_static cl_shared LPA]; unfold pa_static, pa_shared; lia
      | cbn [mf_fd mf_set_mode mf_set_w stderr0]; rewrite FDS1; exact FDL
      | reflexivity | reflexivity | cbn; lia
      | split; [cbn; unfold STDERR_BUFP; lia|]; split; [cbn; unfold STDERR_BUFP; lia|]; intros i Hi; cbn in Hi; lia
      | exact PB
      | cbn; lia | cbn; lia
      | cbn; unfold STDERR_BUFP; lia | cbn; unfold STDERR_BUFP; lia | cbn; lia | cbn; lia
      | lia | lia
      | cbn [mf_buf mf_set_mode mf_set_w stderr0 length Z.of_nat]; unfold STDERR_BUFP, STDIO_WRITE_STACK; rewrite unsigned_lit by lia; lia
      | unfold STDIO_WRITE_STACK; rewrite unsigned_lit by lia; lia
      | eexists; exact CAN' | exact GOT'
      | rewrite unsigned_lit by lia; exact ST1 | unfold STDIO_WRITE_STACK; rewrite unsigned_lit by lia; lia | exact CEIL | rewrite unsigned_lit by lia; lia | exact HK | ].
    (* [comment removed for export] *)
    (intros m2 md2 AINV2; (first [ intro dR_7; dand3 dR_7 as FS2 FDS2 HH2 | intros (FS2 & FDS2 & HH2) ]); intros FILE2 ms' PO).
    (first [ dex14 PO as y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13; dand5 PO as -> MU2 WM2 MI2 ST2 | dand19 PO as y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 -> MU2 WM2 MI2 ST2 | destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & -> & MU2 & WM2 & MI2 & ST2) ]).
    unfold STDIO_WRITE_STACK, STDERR_F in MU2. rewrite unsigned_lit in MU2 by lia. rewrite unsigned_lit in ST2 by lia.
    pose proof FILE2 as FILE2f.
    unfold file_at, file_cells in FILE2.
    cbn [mf_buf mf_bufsize mf_set_mode mf_set_w stderr0 mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148] in FILE2.
    unfold STDERR_F, STDERR_BUFP, STDIO_WRITE in FILE2. cbn [Z.add Pos.add] in FILE2.
    unfold file_at in FILE1. transport_after_call rsegs (aview A m1) (aview A m2) MU2 WM2. clear MU2 WM2.
    (first [ pose proof ((RNG (aview A m2) (consts_hold_ainv LPA A m2 md2 AINV2))) as dR_5; dand4 dR_5 as IR (ng & lastb & NG & SH & LBl) QW1 QW2 | destruct (RNG (aview A m2) (consts_hold_ainv LPA A m2 md2 AINV2)) as (IR & (ng & lastb & NG & SH & LBl) & QW1 & QW2) ]).
    assert (AF : (0 <= pa /\ pa + Z.of_nat (length msg) + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
    replace (pa + Z.of_nat (length msg) - 1)%Z with (pa + Z.of_nat (length msg) + -1)%Z in QW2 by lia.
    destruct (mapped8_le8 _ _ QW1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1 QB1].
    destruct (mapped8_le8 _ _ QW2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2 QB2].
    pose proof (munch_refl [(bv_unsigned sp - 2600, bv_unsigned sp)] (aview A m2)) as MU3. pose proof (wmono_refl rsegs (aview A m2)) as WM3.
    assert (CF3 : client_fpx (L:=LPA) A (aview A m2) [(bv_unsigned sp - 2600, bv_unsigned sp)]).
    { cbn. split; [| exact I]. left. split; [| exact I]. left. split; [lia|]. split; [lia|].
      pose proof ST2 as STx. pose proof FRc as FRcx. pose proof FRb as FRbx. pose proof FRa as FRax.
      release_frame FRcx STx (bv_unsigned sp + -2128). release_frame FRbx STx (bv_unsigned sp + -2032). release_frame FRax STx (bv_unsigned sp).
      eapply (stk_mapped (L:=LPA)); [exact STx | exact CEIL | lia | lia]. }
    ago AINV2. fold_cl_segs. fix_ret_pc.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRa); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRb); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRc); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_QB1); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_QB2); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_SH); icall (fw_tail ra sp gp tp s6 s7 s8 s9 s10 s11 F fc lo pa (Z.of_nat (length msg)) CEIL LO (conj PALO PAHI) ltac:(lia)
             s0 s1 s2 s3 s4 s5 (aview A m2) _ _ _ ng lastb w1 w2)
      by (first [exact MI2 | exact ST2 | exact FRa | exact FRb | exact FRc | exact IR | exact NG | exact SH | exact LBl | exact QB1 | exact QB2 | eassumption]).
    astopx AINV2 MU3 WM3 CF3. rename m0 into m3. rename md0 into md3. rename AINV0 into AINV3.
    pose proof (as_minv LPA A m3 md3 AINV3) as [_ HH3].
    (first [ pose proof ((sbm_io _ md3 SBM0)) as dR_6; dand3 dR_6 as FS3 FDS3 _ | pose proof (sbm_io _ md3 SBM0) as (FS3 & FDS3 & _) ]).
    lazymatch type of FILE2f with file_at _ _ (mf_set_w (mf_set_mode _ ?mo2) _ _ _) =>
      eapply (HKONT m3 md3 (mf_set_mode (mf_set_w stderr0 (Z_to_bv 64 STDERR_BUFP) (Z_to_bv 64 STDERR_BUFP) (Z_to_bv 64 STDERR_BUFP)) mo2) AINV3) end.
    { split; [| split; [| exact HH3]]. rewrite FS3, FS2, FS1; reflexivity. rewrite FDS3, FDS2, FDS1; reflexivity. }
    { eexists (Z_to_bv 64 STDERR_BUFP), _. split; [reflexivity| right; reflexivity]. }
    { exact FILE2. }
    hot_eexists_all. split; [reflexivity|].
    split. { exact MU. }
    split. { exact WM. }
    split; [assumption|]. assumption.
  Qed.
End Leaves.

End DA_Fpom.

Module DA_Tails.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image SysStep RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j AIcpnnp AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img A_ImgAny.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Se7o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Eg3i DA_Cells DA_Ldix DA_Entry DA_Mib4 DA_Inv DA_Ejgo DA_Main.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes.DA_Myrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ldix OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Entry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Mib4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ejgo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Main OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.DA_R1e4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Fpom.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Section Walks.
  Variables (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32).
  #[local] Notation rom := (seg_rom rsegs).

  (* [comment removed for export] *)
  Definition tail2_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x86a88) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 2) a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 EXIT_ENTRY) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma diag_walk : forall (ra : word) (m : word -> option byte),
    mem_inv rsegs m ->
    evt rsegs (tail2_post m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86a5c) fc None m rom).
  Proof.
    intros ra m MI.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    bstep. bstep. bstep. apply evt_done. unfold tail2_post, EXIT_ENTRY.
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

End Walks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Tails.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  Variable usp : Z.
  Hypothesis HCEIL : alloc_ceiling = usp - 0x800000.   (* [comment removed for export] *)
  Variables argv envp : list (list byte).
  Hypothesis EXIT : exit_spec_stmt.
  #[local] Notation rom := (seg_rom rsegs).

  Ltac ulit := rewrite ?unsigned_lit by (unfold SPF, STK_LO in *; lia).

  (* [comment removed for export] *)
  #[using="EXIT HCEIL"] Lemma exit2_fin :
    forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           m md A tid ini,
      sp_window_lo <= usp -> usp <= 2^47 ->
      ainv A m md -> mem_inv rsegs (aview A m) -> ccells (aview A m) tid SO_pristine ini ->
      stk rsegs (aview A m) (STK_LO usp) (SPF usp) ->
      srealizes rsegs
        (mkCfg (MS (mkR ra (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) t0 t1 t2 s0 s1 (Z_to_bv 64 2) a1 a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 EXIT_ENTRY) fc None m rom) md)
        (t_exit (exit_code 2) (m_fs md)).
  Proof.
    intros until ini. intros U1 U2 AINV MI CC ST. unfold sp_window_lo in U1.
    apply (srz_conseq _ _ (t_emit (W 1 (pending_of SO_pristine)) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs md)))).
    - eapply (exit_via EXIT); try eassumption.
      all: lazymatch goal with
           | |- ro_cells _ _ SSP_GOT _ => exact (mc_sspgot _ _ (proj1 CC))
           | |- @eq word _ _ => reflexivity
           | |- stk _ _ _ _ => ulit; exact ST
           | |- pending_of _ <> [] -> _ => cbn [pending_of]; intros NE; exfalso; apply NE; reflexivity
           | |- _ => ulit; rewrite ?alloc_ceiling_val; unfold EXIT_STACK, STK_LO, SPF in *; lia
           end.
    - cbn [pending_of W map].
      replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; vm_compute; reflexivity).
      apply t_emit_nil_eq. apply t_emit_has_nil.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="EXIT HCEIL"] Lemma diag_tail :
    forall (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           m md A tid ini,
      sp_window_lo <= usp -> usp <= 2^47 ->
      ainv A m md -> mem_inv rsegs (aview A m) -> ccells (aview A m) tid SO_pristine ini ->
      stk rsegs (aview A m) (STK_LO usp) (SPF usp) ->
      srealizes rsegs
        (mkCfg (MS (mkR ra (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x86a5c) fc None m rom) md)
        (t_exit (exit_code 2) (m_fs md)).
  Proof.
    intros until ini. intros U1 U2 AINV MI CC ST. pose proof U1 as U1'. unfold sp_window_lo in U1'.
    pose proof (munch_refl [] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) []) by exact I.
    ago AINV. fold_cl_segs.
    icall (diag_walk (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc ra (aview A m)) by (exact MI).
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    astopx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_2; dand3 dR_2 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    assert (CC1 : ccells (aview A m1) tid SO_pristine ini).
    { eapply ccells_agree; [| exact CC]. apply (agree_of_munch _ _ _ _ MU). ranges_outside. }
    lazymatch goal with H : stk _ (aview A m1) _ _ |- _ => rename H into ST1 end.
    rewrite <- FS1. eapply exit2_fin; [exact U1| exact U2| exact AINV1| exact MI1| exact CC1| ulit; exact ST1].
  Qed.

End Tails.
End DA_Tails.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.

Module DA_Open.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr SysStep RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec RelSpec RefNodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct Lazyiq4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Nodes DA_Se7o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Eg3i DA_Cells DA_Ldix.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes.DA_Myrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ldix.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Walks.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (lo : Z) (g : word).
  Hypothesis CEIL : alloc_ceiling <= lo.
  #[local] Notation rom := (seg_rom rsegs).

  (* [comment removed for export] *)
  Definition open1_post (p1 : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists junk m',
      ms' = MSsvc (mkR (Z_to_bv 64 0x98668) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 p1) t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 SSP_GUARD)
                       (Z_to_bv 64 (-100)) (Z_to_bv 64 p1) (Z_to_bv 64 32768) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 56)
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 SYSCALL_ECALL) (Z_to_bv 64 56) fc None m' rom
      /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp + -96)
      /\ rw_cells rsegs m' (bv_unsigned sp + -96) [CB 16 junk; C8 g; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7].

  #[using="CEIL Clg"] Lemma open_walk1 : forall (a0 a1 : word) (m : word -> option byte) (p1 : Z),
    lo + 112 <= bv_unsigned sp -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
    ro_cells rsegs m SSP_GOT [C8 (Z_to_bv 64 SSP_GUARD)] -> ro_cells rsegs m SSP_GUARD [C8 g] ->
    0 <= p1 < 2^64 -> a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 0 ->
    evt rsegs (open1_post p1 m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 OPEN_ENTRY) fc None m rom).
  Proof.
    intros a0 a1 m p1 LO MI ST GOT CAN P1 -> ->. unfold SSP_GOT, SSP_GUARD, OPEN_ENTRY in *.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 96%nat ST.
    run_to 0xa285c. at_pc 0xa285c.
    step_ecall. unfold open1_post, SYSCALL_ECALL, SSP_GUARD.
    eexists _, _. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition open2_post (res : word) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0' a1' a2' a3' m',
      ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 res a1' a2' a3' (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 56)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' rom
      /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp).

  #[using="CEIL Clg"] Lemma open_walk2_ok : forall (m : word -> option byte) (p1 r : Z) (junk : list byte),
    lo + 112 <= bv_unsigned sp -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp + -96) ->
    ro_cells rsegs m SSP_GUARD [C8 g] ->
    rw_cells rsegs m (bv_unsigned sp + -96) [CB 16 junk; C8 g; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
    0 <= r < 2^31 ->
    evt rsegs (open2_post (Z_to_bv 64 r) m)
        (MS (mkR (Z_to_bv 64 0x98668) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 p1) t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 SSP_GUARD)
                 (Z_to_bv 64 r) (Z_to_bv 64 p1) (Z_to_bv 64 32768) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 56)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (SYSCALL_ECALL + 4)) fc None m rom).
  Proof.
    intros m p1 r junk LO MI ST CAN FR HR. unfold SSP_GUARD, SYSCALL_ECALL in *. lit_addrs_goal.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    run_to 0x98670. at_pc 0x98670. bstep.
    run_to 0x986a0. at_pc 0x986a0. rewrite (swrap32_small0 r) by lia.
    run_to 0x986d4. at_pc 0x986d4. azstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; blia].
    run_to 0x986ac. at_pc 0x986ac. bstep.
    run_to 0x986c4. at_pc 0x986c4. rewrite (swrap32_small0 r) by lia.
    release_frame FR ST (bv_unsigned sp).
    bstep. apply evt_done. unfold open2_post.
    eexists _, _, _, _, _. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition open2e_post (r : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0' a1' a2' a3' m',
      ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 56)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' rom
      /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (ERRNO_CELL, ERRNO_CELL + 4)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' ERRNO_CELL [C4 (Z_to_bv 64 r)].

  #[using="CEIL Clg"] Lemma open_walk2_err : forall (m : word -> option byte) (p1 r : Z) (junk : list byte) (e0 : word),
    lo + 112 <= bv_unsigned sp -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp + -96) ->
    ro_cells rsegs m SSP_GUARD [C8 g] ->
    rw_cells rsegs m (bv_unsigned sp + -96) [CB 16 junk; C8 g; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
    rw_cells rsegs m ERRNO_CELL [C4 e0] -> tp = cl_tp LPA ->
    1 <= r <= 4095 ->
    evt rsegs (open2e_post r m)
        (MS (mkR (Z_to_bv 64 0x98668) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 p1) t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 SSP_GUARD)
                 (Z_to_bv 64 (18446744073709551616 - r)) (Z_to_bv 64 p1) (Z_to_bv 64 32768) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 56)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (SYSCALL_ECALL + 4)) fc None m rom).
  Proof.
    intros m p1 r junk e0 LO MI ST CAN FR ERR TP HR. unfold SSP_GUARD, SYSCALL_ECALL, ERRNO_CELL in *. cbn [cl_tp LPA] in TP. rewrite TP. lit_addrs_goal.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (0x5e7b34, 0x5e7b34 + 4)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    run_to 0x98670. at_pc 0x98670. bstep.
    run_to 0x986a0. at_pc 0x986a0. rewrite (swrap32_neg r) by lia.
    run_to 0x986d4. at_pc 0x986d4. azstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; blia| clear K].
    carve_frame 16%nat ST.
    run_to 0x986ec. at_pc 0x986ec. rewrite (swrap32_negneg r) by lia.
    bstep.
    run_to 0x98700. at_pc 0x98700. release_frame FR0 ST (bv_unsigned sp + -96).
    bstep.
    run_to 0x986ac. at_pc 0x986ac. bstep.
    run_to 0x986c4. at_pc 0x986c4.
    release_frame FR ST (bv_unsigned sp).
    bstep. apply evt_done. unfold open2e_post, ERRNO_CELL. rewrite TP.
    eexists _, _, _, _, _. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition close1_post (fd : word) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists junk m',
      ms' = MSsvc (mkR (Z_to_bv 64 0xa72c4) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1
                       fd (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 57)
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 SYSCALL_ECALL) (Z_to_bv 64 57) fc None m' rom
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp + -16)
      /\ rw_cells rsegs m' (bv_unsigned sp + -16) [CB 8 junk; C8 ra].

  #[using="CEIL Clg"] Lemma close_walk1 : forall (a0 a1 : word) (m : word -> option byte),
    lo + 32 <= bv_unsigned sp -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
    evt rsegs (close1_post a0 m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 CLOSE_ENTRY) fc None m rom).
  Proof.
    intros a0 a1 m LO MI ST. unfold CLOSE_ENTRY in *.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 16%nat ST.
    run_to 0xa285c. at_pc 0xa285c.
    step_ecall. unfold close1_post, SYSCALL_ECALL.
    eexists _, _. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.
  (* [comment removed for export] *)
  Definition close2_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (-4095)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 57)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' rom
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp).

  #[using="CEIL Clg"] Lemma close_walk2 : forall (m : word -> option byte) (junk : list byte),
    lo + 32 <= bv_unsigned sp -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp + -16) ->
    rw_cells rsegs m (bv_unsigned sp + -16) [CB 8 junk; C8 ra] ->
    evt rsegs (close2_post m)
        (MS (mkR (Z_to_bv 64 0xa72c4) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 57)
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (SYSCALL_ECALL + 4)) fc None m rom).
  Proof.
    intros m junk LO MI ST FR. unfold SYSCALL_ECALL in *. lit_addrs_goal.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    run_to 0x986d4. at_pc 0x986d4. azstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; blia].
    run_to 0xa72e8. at_pc 0xa72e8. release_frame FR ST (bv_unsigned sp). bstep.
    apply evt_done. unfold close2_post. eexists _. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.
End Walks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac icall_consts_in H ::= unfold ERRNO_CELL, SSP_GUARD, SSP_GOT, SYSCALL_ECALL in H.

Section Leaves.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)

  Lemma close_ok : close_stmt.
  Proof.
    unfold close_stmt. intros until K. cbv zeta. intros AINV MI A0 FDS ST LO CEIL [e0 ERR] HK. unfold CLOSE_STACK in LO.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). unfold ERRNO_CELL in ERR.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) [(bv_unsigned sp - 32, bv_unsigned sp)]).
    { cbn. split; [| exact I]. left. split; [| exact I]. left. split; [lia|]. split; [lia|].
      eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]. }
    (* [comment removed for export] *)
    ago AINV. fold_cl_segs.
    icall (close_walk1 ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo CEIL)
      by (first [exact MI | exact ST | lia]).
    rename x0 into v1. rename PC into ST1. rename POST into FR1.
    astop_svcx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
    (* [comment removed for export] *)
    pose proof (as_minv LPA A m1 md1 AINV1) as [HMI1 HH1].
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_1; dand3 dR_1 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    eapply (srz_close_hull (cl_segs LPA)) with (x8 := Z_to_bv 64 57) (fd := a0) (e := e);
      [exact HH1 | reflexivity | reflexivity | reflexivity | rewrite A0, unsigned_lit by lia; lia | rewrite FDS1, FDS, A0; reflexivity |].
    rewrite advance_set_gpr0_MSsvc. simp_regs.
    replace (fd_remove (m_fds md1) a0) with fds_std by (rewrite FDS1, FDS, A0; reflexivity).
    pose proof (ainv_fds (L:=LPA) A m1 md1 fds_std AINV1) as AINV2.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] (aview A m1)) as MU2. pose proof (wmono_refl rsegs (aview A m1)) as WM2.
    assert (CF2 : client_fpx (L:=LPA) A (aview A m1) [(bv_unsigned sp - 32, bv_unsigned sp)]).
    { cbn. split; [| exact I]. left. split; [| exact I]. left. split; [lia|]. split; [lia|].
      replace (bv_unsigned sp - (bv_unsigned sp - 32)) with 32 by lia.
      eapply (window_mapped LPA _ lo); [exact ST1 | exact FR1 | cbn; lia | exact CEIL | lia | lia]. }
    ago AINV2. fold_cl_segs. unfold SYSCALL_ECALL. 
    icall (close_walk2 ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo CEIL)
      by (first [exact MI0 | exact ST1 | exact FR1 | lia]).
    rename x into v2.
    astopx AINV2 MU2 WM2 CF2. rename m0 into m2. rename md0 into md2. rename AINV0 into AINV3.
    pose proof (as_minv LPA A m2 md2 AINV3) as [_ HH2].
    (first [ pose proof ((sbm_io _ md2 SBM0)) as dR_2; dand3 dR_2 as FS2 FDS2 _ | pose proof (sbm_io _ md2 SBM0) as (FS2 & FDS2 & _) ]).
    apply (HK m2 md2 AINV3).
    { split; [| split; [exact FDS2 | exact HH2]]. rewrite FS2. cbn. exact FS1. }
    unfold open_post, OPEN_STACK, ERRNO_CELL.
    hot_eexists_all. split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia. }
    split. { exact WM. }
    split; [assumption|]. split; [assumption|]. eexists; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma view_bytes_real : forall A m md p1 bs n,
    ainv A m md -> bytes_at rsegs (aview A m) p1 bs -> (n <= length bs)%nat ->
    rdn rsegs m (Z_to_bv 64 p1) n = Some (firstn n bs) /\ bytes_in_hull (ahull A) (Z_to_bv 64 p1) n.
  Proof.
    intros A m md p1 bs n AINV PB HN.
    pose proof (bytes_at_rdn rsegs (aview A m) p1 bs 0 n PB ltac:(lia)) as RD.
    change (skipn 0 bs) with bs in RD. cbn [Z.of_nat] in RD. rewrite Z.add_0_r in RD.
    destruct (view_rdn_real (L:=LPA) A m md _ _ _ AINV RD) as [R1 R2]. split; [| exact R2].
    rewrite <- OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.ov_rdn, Lib.PropExec.ov_rdn. exact R1.
  Qed.

  Lemma path_real : forall A m md p1 path,
    ainv A m md -> bytes_at rsegs (aview A m) p1 (path ++ [Z_to_bv 8 0]) ->
    rdn rsegs m (Z_to_bv 64 p1) (length path + 1) = Some (path ++ [Z_to_bv 8 0])
    /\ bytes_in_hull (ahull A) (Z_to_bv 64 p1) (S (length path)).
  Proof.
    intros A m md p1 path AINV PB.
    assert (HL : length (path ++ [Z_to_bv 8 0]) = (length path + 1)%nat) by (rewrite length_app; reflexivity).
    destruct (view_bytes_real A m md p1 _ (length path + 1) AINV PB ltac:(rewrite HL; lia)) as [R1 R2].
    rewrite firstn_all2 in R1 by (rewrite HL; lia). split; [exact R1|]. rewrite <- Nat.add_1_r. exact R2.
  Qed.

  Lemma path_real_toolong : forall A m md p1 path,
    ainv A m md -> bytes_at rsegs (aview A m) p1 (path ++ [Z_to_bv 8 0]) -> (4096 <= length path)%nat -> ~ In (Z_to_bv 8 0) path ->
    rdn rsegs m (Z_to_bv 64 p1) 4096 = Some (firstn 4096 path) /\ ~ In (Z_to_bv 8 0) (firstn 4096 path)
    /\ bytes_in_hull (ahull A) (Z_to_bv 64 p1) 4096.
  Proof.
    intros A m md p1 path AINV PB HL NZ.
    destruct (view_bytes_real A m md p1 _ 4096 AINV PB ltac:(rewrite length_app; lia)) as [R1 R2].
    rewrite firstn_app in R1. replace (4096 - length path)%nat with 0%nat in R1 by lia. cbn [firstn] in R1. rewrite app_nil_r in R1.
    split; [exact R1|]. split; [| exact R2].
    intros HIN. apply NZ. rewrite <- (firstn_skipn 4096 path). apply in_or_app. left. exact HIN.
  Qed.

  Lemma openat_errnos_range : forall er, In er openat_errnos -> 1 <= er <= 4095.
  Proof.
    intros er Hin. unfold openat_errnos, State.ENOMEM, EACCES, EMFILE, ENFILE in Hin. cbn in Hin. lia.
  Qed.

  Lemma open_ok_ok : open_ok_stmt.
  Proof.
    unfold open_ok_stmt. intros until KB. cbv zeta. intros AINV PRE FDS LEN CASE HKA HKB.
    (first [ dand12 PRE as A0 A1 TP PB NZ SPP MI [GOT [g CAN]] ST LO CEIL [e0 ERR] | destruct PRE as (A0 & A1 & TP & PB & NZ & SPP & MI & [GOT [g CAN]] & ST & LO & CEIL & [e0 ERR]) ]).
    unfold OPEN_STACK in LO. unfold ERRNO_CELL in ERR. unfold SSP_GOT, SSP_GUARD in GOT, CAN.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    pose proof (bytes_at_bound _ _ _ _ PB) as PBB. rewrite length_app in PBB; cbn [length] in PBB.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) [(bv_unsigned sp - 112, bv_unsigned sp)]).
    { cbn. split; [| exact I]. left. split; [| exact I]. left. split; [lia|]. split; [lia|].
      eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]. }
    (* [comment removed for export] *)
    ago AINV. fold_cl_segs.
    icall (open_walk1 ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo g CEIL a0 a1 (aview A m) p1)
      by (first [exact MI | exact ST | exact GOT | exact CAN | exact A0 | exact A1 | lia]).
    lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -96) _ |- _ => rename H into FR1 end.
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    astop_svcx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
    (* [comment removed for export] *)
    pose proof (as_minv LPA A m1 md1 AINV1) as [HMI1 HH1].
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_4; dand3 dR_4 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    destruct (path_real A m1 md1 p1 path AINV1 PB) as [RD1 HULL1].
    eapply (srz_openat_open_hull (cl_segs LPA) (ahull A) (alhull A) (aeager A) _ md1 (Z_to_bv 64 56)) with (p := path) (e := e);
      [ exact HH1 | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact HMI1 | reflexivity
      | split; [exact LEN| split; [exact NZ| exact RD1]]
      | exact HULL1
      | rewrite FDS1, FDS; reflexivity
      | rewrite FS1; exact CASE
      | | ].
    - (* [comment removed for export] *)
      intros er md2 Her HMI2 SB2. pose proof (openat_errnos_range er Her) as HER.
      rewrite advance_set_gpr0_MSsvc. simp_regs. rewrite (errno_ret_neg er HER).
      pose proof (ainv_mat (L:=LPA) A m1 md1 md2 AINV1 HMI2 SB2) as AINV2.
      (first [ pose proof ((sbm_io md1 md2 SB2)) as dR_5; dand3 dR_5 as FS2 FDS2 _ | pose proof (sbm_io md1 md2 SB2) as (FS2 & FDS2 & _) ]).
      apply (munch_weaken _ [(bv_unsigned sp - 112, bv_unsigned sp); (6191924, 6191924 + 4)]) in MU; [| unfold sub_fp; cbn [outside]; intros; lia].
      pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (6191924, 6191924 + 4)] (aview A m1)) as MU2. pose proof (wmono_refl rsegs (aview A m1)) as WM2.
      assert (CF2 : client_fpx (L:=LPA) A (aview A m1) [(bv_unsigned sp - 112, bv_unsigned sp); (6191924, 6191924 + 4)]).
      { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|].
          replace (bv_unsigned sp - (bv_unsigned sp - 112)) with 112 by lia.
          eapply (window_mapped LPA _ lo); [exact ST1 | exact FR1 | cbn; lia | exact CEIL | lia | lia]. }
        split; [| exact I]. right. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
      ago AINV2. fold_cl_segs. unfold SYSCALL_ECALL.
      icall (open_walk2_err ra sp gp tp t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo g CEIL (aview A m1) p1 er)
        by (first [exact MI1 | exact ST1 | exact CAN | exact FR1 | exact ERR | exact TP | lia]).
      lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST2 end.
      lazymatch goal with H : rw_cells _ _ 6191924 _ |- _ => rename H into ERR2 end.
      astopx AINV2 MU2 WM2 CF2. rename m0 into m2. rename md0 into md3. rename AINV0 into AINV3.
      pose proof (as_minv LPA A m2 md3 AINV3) as [_ HH3].
      (first [ pose proof ((sbm_io _ md3 SBM0)) as dR_6; dand3 dR_6 as FS3 FDS3 _ | pose proof (sbm_io _ md3 SBM0) as (FS3 & FDS3 & _) ]).
      apply (HKA m2 md3 AINV3).
      { split; [| split; [| exact HH3]]. rewrite FS3, FS2; exact FS1. rewrite FDS3, FDS2, FDS1; exact FDS. }
      unfold open_post, OPEN_STACK, ERRNO_CELL.
      hot_eexists_all. split; [reflexivity|].
      split. { exact MU. }
      split. { exact WM. }
      split; [assumption|]. split; [assumption|]. eexists; eassumption.
    - (* [comment removed for export] *)
      intros md2 HMI2 SB2.
      rewrite advance_set_gpr0_MSsvc. simp_regs.
      replace (alloc_fd (m_fds md1)) with (Z_to_bv 64 3) by (rewrite FDS1, FDS; reflexivity).
      replace (fd_insert (m_fds md1) (alloc_fd (m_fds md1)) e) with (fds3 e) in SB2 by (rewrite FDS1, FDS; reflexivity).
      pose proof (ainv_mat (L:=LPA) A m1 _ md2 (ainv_fds (L:=LPA) A m1 md1 (fds3 e) AINV1) HMI2 SB2) as AINV2.
      (first [ pose proof ((sbm_io _ md2 SB2)) as dR_7; dand3 dR_7 as FS2 FDS2 _ | pose proof (sbm_io _ md2 SB2) as (FS2 & FDS2 & _) ]).
      pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] (aview A m1)) as MU2. pose proof (wmono_refl rsegs (aview A m1)) as WM2.
      assert (CF2 : client_fpx (L:=LPA) A (aview A m1) [(bv_unsigned sp - 112, bv_unsigned sp)]).
      { cbn. split; [| exact I]. left. split; [| exact I]. left. split; [lia|]. split; [lia|].
        replace (bv_unsigned sp - (bv_unsigned sp - 112)) with 112 by lia.
        eapply (window_mapped LPA _ lo); [exact ST1 | exact FR1 | cbn; lia | exact CEIL | lia | lia]. }
      ago AINV2. fold_cl_segs. unfold SYSCALL_ECALL.
      icall (open_walk2_ok ra sp gp tp t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo g CEIL (aview A m1) p1 3)
        by (first [exact MI1 | exact ST1 | exact CAN | exact FR1 | lia]).
      lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST2 end.
      astopx AINV2 MU2 WM2 CF2. rename m0 into m2. rename md0 into md3. rename AINV0 into AINV3.
      pose proof (as_minv LPA A m2 md3 AINV3) as [_ HH3].
      (first [ pose proof ((sbm_io _ md3 SBM0)) as dR_8; dand3 dR_8 as FS3 FDS3 _ | pose proof (sbm_io _ md3 SBM0) as (FS3 & FDS3 & _) ]).
      apply (HKB m2 md3 AINV3).
      { split; [| split; [| exact HH3]]. rewrite FS3, FS2; cbn; exact FS1. rewrite FDS3, FDS2; reflexivity. }
      unfold open_post, OPEN_STACK, ERRNO_CELL.
      hot_eexists_all. split; [reflexivity|].
      split. { exact MU. }
      split. { exact WM. }
      split; [assumption|]. split; [assumption|]. eexists; eassumption.
  Qed.

  Lemma open_fail_ok : open_fail_stmt.
  Proof.
    unfold open_fail_stmt. intros until K. cbv zeta. intros AINV PRE CASE HK.
    (first [ dand12 PRE as A0 A1 TP PB NZ SPP MI [GOT [g CAN]] ST LO CEIL [e0 ERR] | destruct PRE as (A0 & A1 & TP & PB & NZ & SPP & MI & [GOT [g CAN]] & ST & LO & CEIL & [e0 ERR]) ]).
    unfold OPEN_STACK in LO. unfold ERRNO_CELL in ERR. unfold SSP_GOT, SSP_GUARD in GOT, CAN.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    pose proof (bytes_at_bound _ _ _ _ PB) as PBB. rewrite length_app in PBB; cbn [length] in PBB.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) [(bv_unsigned sp - 112, bv_unsigned sp)]).
    { cbn. split; [| exact I]. left. split; [| exact I]. left. split; [lia|]. split; [lia|].
      eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]. }
    (* [comment removed for export] *)
    ago AINV. fold_cl_segs.
    icall (open_walk1 ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo g CEIL a0 a1 (aview A m) p1)
      by (first [exact MI | exact ST | exact GOT | exact CAN | exact A0 | exact A1 | lia]).
    lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -96) _ |- _ => rename H into FR1 end.
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    astop_svcx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
    pose proof (as_minv LPA A m1 md1 AINV1) as [HMI1 HH1].
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_10; dand3 dR_10 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    (* [comment removed for export] *)
    lazymatch goal with |- srealizes _ (mkCfg ?ms _) _ =>
      assert (TAIL : forall er md2, 1 <= er <= 4095 -> MInv (ahull A) (alhull A) (aeager A) md2 -> same_but_materialized md1 md2 ->
                     srealizes (cl_segs LPA) (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret er))) md2) K) end.
    { intros er md2 HER HMI2 SB2.
      rewrite advance_set_gpr0_MSsvc. simp_regs. rewrite (errno_ret_neg er HER).
      pose proof (ainv_mat (L:=LPA) A m1 md1 md2 AINV1 HMI2 SB2) as AINV2.
      (first [ pose proof ((sbm_io md1 md2 SB2)) as dR_11; dand3 dR_11 as FS2 FDS2 _ | pose proof (sbm_io md1 md2 SB2) as (FS2 & FDS2 & _) ]).
      apply (munch_weaken _ [(bv_unsigned sp - 112, bv_unsigned sp); (6191924, 6191924 + 4)]) in MU; [| unfold sub_fp; cbn [outside]; intros; lia].
      pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (6191924, 6191924 + 4)] (aview A m1)) as MU2. pose proof (wmono_refl rsegs (aview A m1)) as WM2.
      assert (CF2 : client_fpx (L:=LPA) A (aview A m1) [(bv_unsigned sp - 112, bv_unsigned sp); (6191924, 6191924 + 4)]).
      { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|].
          replace (bv_unsigned sp - (bv_unsigned sp - 112)) with 112 by lia.
          eapply (window_mapped LPA _ lo); [exact ST1 | exact FR1 | cbn; lia | exact CEIL | lia | lia]. }
        split; [| exact I]. right. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
      ago AINV2. fold_cl_segs. unfold SYSCALL_ECALL.
      icall (open_walk2_err ra sp gp tp t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo g CEIL (aview A m1) p1 er)
        by (first [exact MI1 | exact ST1 | exact CAN | exact FR1 | exact ERR | exact TP | lia]).
      astopx AINV2 MU2 WM2 CF2. rename m0 into m2. rename md0 into md3. rename AINV0 into AINV3.
      pose proof (as_minv LPA A m2 md3 AINV3) as [_ HH3].
      (first [ pose proof ((sbm_io _ md3 SBM0)) as dR_12; dand3 dR_12 as FS3 FDS3 _ | pose proof (sbm_io _ md3 SBM0) as (FS3 & FDS3 & _) ]).
      apply (HK m2 md3 AINV3).
      { split; [| split; [| exact HH3]]. rewrite FS3, FS2; exact FS1. rewrite FDS3, FDS2; exact FDS1. }
      unfold open_post, OPEN_STACK, ERRNO_CELL.
      hot_eexists_all. split; [reflexivity|].
      split. { exact MU. }
      split. { exact WM. }
      split; [assumption|]. split; [assumption|]. eexists; eassumption. }
    (* [comment removed for export] *)
    destruct CASE as [LONG | REST].
    - (first [ pose proof ((path_real_toolong A m1 md1 p1 path AINV1 PB LONG NZ)) as dR_13; dand3 dR_13 as RD1 NZ1 HULL1 | destruct (path_real_toolong A m1 md1 p1 path AINV1 PB LONG NZ) as (RD1 & NZ1 & HULL1) ]).
      eapply (srz_openat_toolong_hull (cl_segs LPA) (ahull A) (alhull A) (aeager A) _ md1 (Z_to_bv 64 56));
        [ exact HH1 | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact HMI1 | reflexivity
        | exact RD1 | exact NZ1 | exact HULL1 | ].
      intros md2 HMI2 SB2. apply (TAIL ENAMETOOLONG md2); [unfold ENAMETOOLONG; lia | exact HMI2 | exact SB2].
    - assert (LEN : (length path <= 4095)%nat) by (destruct REST as [->|(_ & _ & _ & _ & L & _)]; [cbn; lia| exact L]).
      destruct (path_real A m1 md1 p1 path AINV1 PB) as [RD1 HULL1].
      eapply (srz_openat_enoent_hull (cl_segs LPA) (ahull A) (alhull A) (aeager A) _ md1 (Z_to_bv 64 56)) with (p := path);
        [ exact HH1 | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact HMI1 | reflexivity
        | split; [exact LEN| split; [exact NZ| exact RD1]]
        | exact HULL1
        | rewrite FS1; destruct REST as [E|(N1 & N2 & N2a & N2b & _ & N4)]; [left; exact E| right; exact (conj N1 (conj N2 (conj N2a (conj N2b N4))))]
        | ].
      intros md2 HMI2 SB2. apply (TAIL State.ENOENT md2); [unfold State.ENOENT; lia | exact HMI2 | exact SB2].
  Qed.
End Leaves.
End DA_Open.


Module DA_Read.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr SysStep RzBridge MState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec RelSpec RefNodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct Lazyiq4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Nodes DA_Se7o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Eg3i DA_Cells DA_Ldix.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes.DA_Myrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ldix OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.DA_R1e4.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac icall_consts_in H ::= unfold tryinit_post, region_is_poisoned_post, ERRNO_CELL in H.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma a0_frame_join : forall m A B cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 -> B = (A + Z.of_nat (cells_size cs1))%Z -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] R1] [[W2 B2] R2] ->. split; [split|].
  - apply cells_wf_app. tauto.
  - rewrite cells_bytes_app. apply bytes_at_app. rewrite (cells_bytes_length cs1 W1). tauto.
  - rewrite cells_size_app, Nat2Z.inj_add. destruct R1 as (R10 & R11 & R12), R2 as (R20 & R21 & R22).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))); [apply R12; lia|].
    replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply R22. lia.
Qed.
Ltac a0_join :=
  match goal with
  | F0 : rw_cells _ ?m ?A [CB 1984 ?j], F1 : rw_cells _ ?m ?B (C8 _ :: _) |- _ =>
      let FRJ := fresh "FRJ" in
      pose proof (a0_frame_join m A B _ _ F0 F1 ltac:(cbn [cells_size csize Nat.add]; repeat match goal with H : _ |- _ => clear H end; lia)) as FRJ;
      cbn [app] in FRJ; clear F0 F1
  end.

Section Walks.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (lo : Z) (dst cnt : Z).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + 2400 <= bv_unsigned sp.
  Hypothesis DSTR : 0 <= dst /\ dst + cnt <= 2^47.
  Hypothesis CNTR : 1 <= cnt <= 65536.
  #[local] Notation rom := (seg_rom rsegs).
  (* [comment removed for export] *)
  #[local] Notation FRAME m1 junk := (rw_cells rsegs m1 (bv_unsigned sp + -2032) [CB 1984 junk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  #[local] Notation FRAME0 m1 junk0 := (rw_cells rsegs m1 (bv_unsigned sp + -2128) [CB 96 junk0]).
  #[local] Notation FRAME1 m1 junk1 := (rw_cells rsegs m1 (bv_unsigned sp + -2144) [CB 8 junk1; C8 (Z_to_bv 64 0x49654)]).

  (* [comment removed for export] *)
  Definition read1_post (fd : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0' t1' t2' t3' t4' t5' t6' junk junk0 junk1 m',
      ms' = MSsvc (mkR (Z_to_bv 64 0xa73a0) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0' t1' t2' sp (Z_to_bv 64 dst)
                       (Z_to_bv 64 fd) (Z_to_bv 64 dst) (Z_to_bv 64 cnt) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 63)
                       (Z_to_bv 64 cnt) (Z_to_bv 64 fd) (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 SYSCALL_ECALL) (Z_to_bv 64 63) fc None m' rom
      /\ munch [(bv_unsigned sp - 2400, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp + -2144)
      /\ FRAME m' junk /\ FRAME0 m' junk0 /\ FRAME1 m' junk1.

  #[using="LO CEIL Clg"] Lemma read_walk1 : forall (a0 a1 a2 : word) (m : word -> option byte) (fd : Z),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
    asan_inited_cell m -> ro_cells rsegs m REAL_READ_CELL [C8 (Z_to_bv 64 MUSL_READ)] ->
    0 <= fd < 16 -> a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 dst -> a2 = Z_to_bv 64 cnt ->
    evt rsegs (read1_post fd m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 READ_ICPT_ENTRY) fc None m rom).
  Proof.
    intros a0 a1 a2 m fd MI ST INI RR FD -> -> ->. unfold REAL_READ_CELL, MUSL_READ, READ_ICPT_ENTRY in *. unfold asan_inited_cell in INI.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 2400, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    bstep.
    carve_frame 48%nat ST. carve_frame 1984%nat ST.
    run_to 0x49624. at_pc 0x49624. a0_join.
    carve_frame 96%nat ST.
    run_to 0x5fce0. at_pc 0x5fce0.
    icall tryinit_spec by (rewrite ?unsigned_lit by lia; first [exact INI | exact ST | exact CEIL | eassumption | lia]).
    run_to 0xa7378. at_pc 0xa7378.
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST1 end.
    carve_frame 16%nat ST1.
    run_to 0xa285c. at_pc 0xa285c.
    step_ecall. unfold read1_post, SYSCALL_ECALL.
    hot_eexists_all. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.
  #[local] Notation AT pc r spx m1 t0' t1' t2' t3' t4' t5' t6' :=
    (MS (mkR (Z_to_bv 64 0xa73a0) (Z_to_bv 64 (bv_unsigned sp + spx)) gp tp t0' t1' t2' sp (Z_to_bv 64 dst)
             r (Z_to_bv 64 dst) (Z_to_bv 64 cnt) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 63)
             (Z_to_bv 64 cnt) (Z_to_bv 64 3) (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 pc) fc None m1 rom) (only parsing).

  (* [comment removed for export] *)
  Definition read2_post (res : word) (W : list (Z * Z)) (m1 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 res a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' rom
      /\ munch ((bv_unsigned sp - 2400, bv_unsigned sp) :: W) m1 m' /\ wmono rsegs m1 m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp).

  (* [comment removed for export] *)
  #[local] Notation POSTn n m1 := (read2_post (Z_to_bv 64 n) [] m1).

  Section Pos.
    Variables (m1 : word -> option byte) (junk junk0 junk1 : list byte) (n : Z) (ng : nat) (lastb : Z) (w1 w2 : word).
    Hypothesis NR : 1 <= n <= cnt.
    Hypothesis MI1 : mem_inv rsegs m1.
    Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2144).
    Hypothesis FR : FRAME m1 junk.  Hypothesis FR0 : FRAME0 m1 junk0.  Hypothesis FR1 : FRAME1 m1 junk1.
    Hypothesis Gsh : ro_cells rsegs m1 0xa8b70 [C8 (Z_to_bv 64 0xb4bb8)].
    Hypothesis Csh : ro_cells rsegs m1 0xb4bb8 [C8 (Z_to_bv 64 0x7fff8000)].
    Hypothesis Gmb : ro_cells rsegs m1 0xa8b78 [C8 (Z_to_bv 64 0xb58a8)].
    Hypothesis Cmb : ro_cells rsegs m1 0xb58a8 [C8 (Z_to_bv 64 0)].
    Hypothesis Gme : ro_cells rsegs m1 0xa8b80 [C8 (Z_to_bv 64 0xb58b0)].
    Hypothesis Cme : ro_cells rsegs m1 0xb58b0 [C8 (Z_to_bv 64 0)].
    Hypothesis Ghe : ro_cells rsegs m1 0xa8b88 [C8 (Z_to_bv 64 0xb58a0)].
    Hypothesis Che : ro_cells rsegs m1 0xb58a0 [C8 (Z_to_bv 64 0x7fffffffffff)].
    Hypothesis IR : inmem_range dst n.
    Hypothesis NG : ((dst + n - 1) / 8 - dst / 8 = Z.of_nat ng)%Z.
    Hypothesis SH1 : bytes_at rsegs m1 (dst / 8 + shadow_off) (zeros ng ++ [Z_to_bv 8 lastb]).
    Hypothesis LB : (lastb = 0 \/ ((dst + n - 1) mod 8 < lastb <= 7))%Z.
    Hypothesis QB1 : bytes_at rsegs m1 (sha dst - sha dst mod 8) (le8 w1).
    Hypothesis QB2 : bytes_at rsegs m1 (sha (dst + n + -1) - sha (dst + n + -1) mod 8) (le8 w2).

    (* [comment removed for export] *)
    #[using="ng DSTR LO CEIL cnt dst Clg"] Lemma rd_exit : forall m2 x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
      mem_inv rsegs m2 -> munch [(bv_unsigned sp - 2400, bv_unsigned sp)] m1 m2 -> wmono rsegs m1 m2 ->
      stk rsegs m2 lo (bv_unsigned sp + -2128) -> FRAME m2 junk -> FRAME0 m2 junk0 ->
      evt rsegs (POSTn n m1)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x496b4) fc None m2 rom).
    Proof.
      intros until x31. intros MI2 MU2 WM2 ST2 FR2 FR02.
      assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
      azstep. release_frame FR02 ST2 (bv_unsigned sp + -2032).
      run_to 0x496d4. at_pc 0x496d4. release_frame FR2 ST2 (bv_unsigned sp).
      bstep. apply evt_done. unfold read2_post.
      hot_eexists_all. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
    Qed.

    (* [comment removed for export] *)
    #[using="LB SH1 NG IR Che Ghe Cme Gme Cmb Gmb Csh Gsh FR1 FR0 FR ST1 MI1 NR lastb ng junk1 junk0 junk CNTR DSTR LO CEIL cnt Clg"] Lemma rd_region : forall x1 x5 x6 x7 x11 x12 x13 x14 x15 x18 x28 x29 x30 x31,
      evt rsegs (POSTn n m1)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp (Z_to_bv 64 dst) (Z_to_bv 64 n) x11 x12 x13 x14 x15
                 (Z_to_bv 64 0) (Z_to_bv 64 63) x18 (Z_to_bv 64 3) (Z_to_bv 64 (bv_unsigned sp + -2120)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x49750) fc None m1 rom).
    Proof.
      intros. assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
      pose proof ST1 as ST1'. release_frame FR1 ST1' (bv_unsigned sp + -2128).
      pose proof (munch_refl [(bv_unsigned sp - 2400, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
      azstep. azstep. azstep. azstep.
      try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_QB1); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_QB2); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_SH1); icall region_is_poisoned_spec by (rewrite ?unsigned_lit by lia;
        first [ repeat (split; [assumption|]); assumption
              | exact ST1' | exact CEIL | exact MI1 | exact IR
              | first [ hotw_ex2 ng lastb | exists ng, lastb ]; split; [exact NG| split; [exact SH1| exact LB]]
              | lia ]).
      azstep. azstep. azstep. br_taken.
      eapply rd_exit; eassumption.
    Qed.

    Section Slow.
      Variables (sf sl : Z).
      Hypothesis ESF : (sf = dst / 8 + shadow_off)%Z.
      Hypothesis ESL : (sl = sf + Z.of_nat ng)%Z.
      #[local] Notation ATS pc x11 x13 x14 x1 x5 x6 x7 x15 x28 x29 x30 x31 :=
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp (Z_to_bv 64 dst) (Z_to_bv 64 n)
                 x11 (Z_to_bv 64 sl) x13 x14 x15 (Z_to_bv 64 0) (Z_to_bv 64 63) (Z_to_bv 64 cnt) (Z_to_bv 64 3) (Z_to_bv 64 (bv_unsigned sp + -2120))
                 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 pc) fc None m1 rom) (only parsing).

      #[using="FR1 FR0 FR ST1 MI1 ng junk1 junk0 junk DSTR LO CEIL Clg"] Lemma rd_slow_end : forall x11 x14 x1 x5 x6 x7 x15 x28 x29 x30 x31,
        evt rsegs (POSTn n m1) (ATS 0x49828 x11 (Z_to_bv 64 0) x14 x1 x5 x6 x7 x15 x28 x29 x30 x31).
      Proof.
        intros. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
        azstep. azstep. if_cases K; zify_cond K.
        - pose proof ST1 as ST1'. release_frame FR1 ST1' (bv_unsigned sp + -2128).
          eapply rd_exit; try eassumption; [apply munch_refl | apply wmono_refl].
        - exfalso. clear -K. cbv in K. first [lia | congruence].
      Qed.

      #[using="ESL ESF SH1 FR1 FR0 FR ST1 MI1 NR lastb junk1 junk0 junk DSTR LO CEIL Clg"] Lemma rd_slow_loop : forall (cc : nat) (j : Z) x11 x14 x1 x5 x6 x7 x15 x28 x29 x30 x31,
        Z.to_nat (Z.of_nat ng - j) = cc -> (0 <= j < Z.of_nat ng)%Z -> x11 = Z_to_bv 64 (sf + j) ->
        evt rsegs (POSTn n m1) (ATS 0x49818 x11 (Z_to_bv 64 0) x14 x1 x5 x6 x7 x15 x28 x29 x30 x31).
      Proof.
        induction cc as [|cc IH]; intros j x11 x14 x1 x5 x6 x7 x15 x28 x29 x30 x31 Hc Hj ->; [lia|].
        pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (bytes_at_bound _ _ _ _ SH1) as SB.
        rewrite length_app, zeros_length in SB. cbn [length] in SB.
        pose proof (u8ro_read rsegs m1 (dst / 8 + shadow_off) _ j (Z_to_bv 8 0) (Z_to_bv 64 (sf + j)) SH1) as RD.
        specialize (RD ltac:(rewrite (shadow_nth ng lastb (Z.to_nat j)) by lia;
                               replace (Z.to_nat j <? ng)%nat with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity)
                       ltac:(lia) ltac:(unfold wa; f_equal; lia)).
        azstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        azstep. azstep.
        azstep. if_cases K; zify_cond K.
        - apply (IH (j + 1)%Z); [lia|lia|f_equal; lia].
        - apply rd_slow_end.
      Qed.
    End Slow.

    (* [comment removed for export] *)
    #[using="QB2 QB1 LB SH1 NG IR Che Ghe Cme Gme Cmb Gmb Csh Gsh FR1 FR0 FR ST1 MI1 NR w2 w1 lastb ng junk1 junk0 junk CNTR DSTR LO CEIL Clg"] Lemma rd_tail_pos : forall t0' t1' t2' t3' t4' t5' t6',
      evt rsegs (POSTn n m1) (AT 0xa2860 (Z_to_bv 64 n) (-2144) m1 t0' t1' t2' t3' t4' t5' t6').
    Proof.
      intros.
      assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
      assert (AF : (0 <= dst /\ dst + n + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
      pose proof (bytes_at_bound _ _ _ _ SH1) as SB. rewrite length_app, zeros_length in SB. cbn [length] in SB.
      assert (QH1 : (sha dst - sha dst mod 8 + Z.of_nat (length (le8 w1)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
      assert (QH2 : (sha (dst + n + -1) - sha (dst + n + -1) mod 8 + Z.of_nat (length (le8 w2)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
      pose proof ST1 as ST1'. pose proof FR1 as FR1'.
      bstep. run_to 0xa73a8. at_pc 0xa73a8. release_frame FR1' ST1' (bv_unsigned sp + -2128).
      run_to 0x986d4. at_pc 0x986d4. azstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; blia].
      bstep.
      run_to 0x49654. at_pc 0x49654. azstep. br_not_taken.
      azstep. if_cases Ka; zify_cond Ka.
      { exfalso. apply Bool.andb_false_iff in Ka. destruct Ka as [Ka|Ka]; apply Z.ltb_ge in Ka; lia. }
      try clear Ka; try clear Ka0; try clear Ka1.
      azstep. azstep. azstep.
      azstep. if_cases Kb; zify_cond Kb. { exfalso. rewrite zb_lxor_ones in Kb by lia. lia. } clear Kb.
      azstep. azstep.
      azstep. if_cases K2; zify_cond K2.
      - (* [comment removed for export] *)
        apply rd_region.
      - (* [comment removed for export] *)
        assert (N64 : n <= 64) by blia.
        assert (HS1 : (0 <= Z.shiftr dst 3 <= dst)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
        assert (HS2 : (0 <= Z.shiftr (dst + n + -1) 3 <= dst + n - 1)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
        do 9 azstep.
        pose proof (qc_read _ _ _ QB1 ltac:(lia)) as RD1.
        pose proof (qc_read _ _ _ QB2 ltac:(lia)) as RD2.
        azstep. azstep. azstep. azstep. azstep.
        azstep. if_cases K7; zify_cond K7.
        + (* [comment removed for export] *)
          assert (LBR : (0 <= lastb < 128)%Z) by lia.
          pose proof (u8ro_read rsegs _ (dst / 8 + shadow_off) _ (Z.of_nat ng) (Z_to_bv 8 lastb)
                        (Z_to_bv 64 (2147450880 + Z.shiftr (dst + n + -1) 3)) SH1) as RD.
          specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ng lastb ng), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                         ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
          azstep. rewrite sxb_small by lia.
          azstep. azstep. azstep. azstep. azstep.
          rewrite (poisoned_last_zero (dst + n + -1) lastb) by
            (first [lia | destruct LB as [LB0|LB1]; [left; exact LB0| right; replace (dst + n + -1)%Z with (dst + n - 1)%Z by lia; lia]]).
          rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
          set (sf := (2147450880 + dst / 8)%Z). set (sl := (2147450880 + (dst + n + -1) / 8)%Z).
          assert (ESF : (sf = dst / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
          assert (ESL : (sl = sf + Z.of_nat ng)%Z) by (unfold sf, sl; mlia).
          clearbody sf sl.
          azstep. if_cases K8; zify_cond K8.
          * eapply rd_slow_end; eassumption.
          * eapply rd_slow_loop with (j := 0%Z); try eassumption; try reflexivity; try lia. f_equal; lia.
        + (* [comment removed for export] *)
          pose proof ST1 as ST1''. release_frame FR1 ST1'' (bv_unsigned sp + -2128).
          eapply rd_exit; try eassumption; [apply munch_refl | apply wmono_refl].
    Qed.
  End Pos.
  (* [comment removed for export] *)
  Definition read2e_post (e : Z) (m1 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' rom
      /\ munch [(bv_unsigned sp - 2400, bv_unsigned sp); (ERRNO_CELL, ERRNO_CELL + 4)] m1 m' /\ wmono rsegs m1 m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' ERRNO_CELL [C4 (Z_to_bv 64 e)].

  (* [comment removed for export] *)
  #[using="LO CEIL Clg"] Lemma rd_tail_zero : forall m1 junk junk0 junk1 t0' t1' t2' t3' t4' t5' t6',
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -2144) -> FRAME m1 junk -> FRAME0 m1 junk0 -> FRAME1 m1 junk1 ->
    evt rsegs (read2_post (Z_to_bv 64 0) [] m1) (AT (SYSCALL_ECALL + 4) (Z_to_bv 64 0) (-2144) m1 t0' t1' t2' t3' t4' t5' t6').
  Proof.
    intros until t6'. intros MI1 ST1 FR FR0 FR1. unfold SYSCALL_ECALL. lit_addrs_goal.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 2400, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
    bstep. run_to 0xa73a8. at_pc 0xa73a8. release_frame FR1 ST1 (bv_unsigned sp + -2128).
    run_to 0x986d4. at_pc 0x986d4. azstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; blia].
    bstep.
    run_to 0x49654. at_pc 0x49654. azstep. br_not_taken. azstep. br_taken.
    run_to 0x496b8. at_pc 0x496b8. release_frame FR0 ST1 (bv_unsigned sp + -2032).
    run_to 0x496d4. at_pc 0x496d4. release_frame FR ST1 (bv_unsigned sp).
    bstep. apply evt_done. unfold read2_post.
    hot_eexists_all. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="LO CEIL Clg"] Lemma rd_tail_neg : forall m1 junk junk0 junk1 t0' t1' t2' t3' t4' t5' t6' (e : Z) (e0 : word),
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -2144) -> FRAME m1 junk -> FRAME0 m1 junk0 -> FRAME1 m1 junk1 ->
    rw_cells rsegs m1 ERRNO_CELL [C4 e0] -> tp = cl_tp LPA -> 1 <= e <= 4095 ->
    evt rsegs (read2e_post e m1) (AT (SYSCALL_ECALL + 4) (Z_to_bv 64 (18446744073709551616 - e)) (-2144) m1 t0' t1' t2' t3' t4' t5' t6').
  Proof.
    intros until e0. intros MI1 ST1 FR FR0 FR1 ERR TP HE. unfold SYSCALL_ECALL, ERRNO_CELL in *. cbn [cl_tp LPA] in TP. rewrite TP. lit_addrs_goal.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 2400, bv_unsigned sp); (0x5e7b34, 0x5e7b34 + 4)] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
    bstep. run_to 0xa73a8. at_pc 0xa73a8. release_frame FR1 ST1 (bv_unsigned sp + -2128).
    run_to 0x986d4. at_pc 0x986d4. azstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; blia| clear K].
    carve_frame 16%nat ST1.
    run_to 0x986ec. at_pc 0x986ec. rewrite (swrap32_negneg2 e) by lia.
    bstep.
    run_to 0x98700. at_pc 0x98700.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -2144) _ |- _ => release_frame H ST1 (bv_unsigned sp + -2128) end.
    bstep.
    run_to 0x49654. at_pc 0x49654. azstep. br_not_taken. azstep.
    br_taken.
    run_to 0x496b8. at_pc 0x496b8. release_frame FR0 ST1 (bv_unsigned sp + -2032).
    run_to 0x496d4. at_pc 0x496d4. release_frame FR ST1 (bv_unsigned sp).
    bstep. apply evt_done. unfold read2e_post, ERRNO_CELL. rewrite TP.
    hot_eexists_all. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.
End Walks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac icall_consts_in H ::= unfold tryinit_post, region_is_poisoned_post, read1_post, read2_post, read2e_post, ERRNO_CELL in H.

Section Leaves.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)

  Lemma read_icpt_cells_of_consts : forall v, consts_hold LPA v -> read_icpt_cells v.
  Proof.
    intros v CH. split; [apply asan_inited_cell_of_bytes; apply (consts_lookup v _ _ CH); vm_compute; reflexivity|].
    split; [| exact (map_cells_of_consts v CH)].
    apply ro_C8_of_bytes. apply (consts_lookup v _ _ CH). vm_compute. reflexivity.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma read_icpt_stage_file_ok : read_icpt_stage_file_stmt.
  Proof.
    unfold read_icpt_stage_file_stmt. intros until K. cbv zeta. intros AINV MI CELLS TP A0 A1 A2 CNT DST FDS FSL OFF ST LO CEIL [e0 ERR] HK.
    (first [ dand3 CELLS as INI RR MC | destruct CELLS as (INI & RR & MC) ]). unfold READ_ICPT_STACK in LO. unfold ERRNO_CELL in ERR.
    pose proof INI as INI'. unfold asan_inited_cell in INI'. pose proof RR as RR'. unfold REAL_READ_CELL, MUSL_READ in RR'.
    pose proof MC as MC'. open_map_cells MC'.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    remember READ_STAGE as dst eqn:Edst. unfold READ_STAGE in Edst.
    pose proof alloc_ceiling_val as ACV.
    assert (DSTR : 0 <= dst /\ dst + cnt <= 2^47) by lia.
    assert (IMGS : img_client (L:=LPA) dst (dst + cnt)).
    { rewrite Edst. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
    pose proof (munch_refl [(bv_unsigned sp - 2400, bv_unsigned sp)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) [(bv_unsigned sp - 2400, bv_unsigned sp)]).
    { cbn. split; [| exact I]. left. split; [| exact I]. left. split; [lia|]. split; [lia|].
      eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]. }
    (* [comment removed for export] *)
    ago AINV. fold_cl_segs.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_RR); icall (read_walk1 ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo dst cnt CEIL LO a0 a1 a2 (aview A m) 3)
      by (rewrite ?unsigned_lit by lia; first [exact MI | exact ST | exact INI' | exact RR' | exact A0 | exact A1 | exact A2 | lia]).
    lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -2032) _ |- _ => rename H into FRa end.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -2128) _ |- _ => rename H into FRb end.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -2144) _ |- _ => rename H into FRc end.
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    astop_svcx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
    pose proof (as_minv LPA A m1 md1 AINV1) as [HMI1 HH1].
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_17; dand3 dR_17 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    (first [ pose proof ((view_rw_cells_real (L:=LPA) A m1 md1 dst (Z.to_nat cnt) junk AINV1 DST)) as dR_18; dand3 dR_18 as SOK HULL VIS | destruct (view_rw_cells_real (L:=LPA) A m1 md1 dst (Z.to_nat cnt) junk AINV1 DST) as (SOK & HULL & VIS) ]).
    eapply (srz_read_file_hull (cl_segs LPA) (ahull A) (alhull A) (aeager A) _ md1 (Z_to_bv 64 63)) with
        (fd := Z_to_bv 64 3) (p := path) (off := Z_to_bv 64 off) (data := data) (cnt := cnt);
      [ exact HH1 | reflexivity | reflexivity | reflexivity
      | rewrite unsigned_lit by lia; lia
      | rewrite FDS1, FDS; reflexivity
      | rewrite FS1; exact FSL
      | reflexivity
      | unfold MAX_RW_COUNT; lia
      | rewrite ms_gpr_MSsvc; simp_regs; rewrite ?unsigned_lit by lia; unfold TASK_SIZE; lia
      | rewrite ms_gpr_MSsvc; simp_regs; exact SOK
      | exact HMI1
      | rewrite ms_gpr_MSsvc; simp_regs; exact HULL
      | ].
    cbv zeta. rewrite !ms_gpr_MSsvc. simp_regs.
    rewrite !file_read_unguarded. unfold word_to_nat. rewrite !unsigned_lit by lia.
    set (bs := firstn (Z.to_nat cnt) (skipn (Z.to_nat off) data)) in *.
    unfold len_word.
    pose proof (firstn_le_length (Z.to_nat cnt) (skipn (Z.to_nat off) data)) as LEN. fold bs in LEN.
    set (nb := Z.of_nat (length bs)) in *.
    intros md2 HMI2 SB2.
    rewrite advance_apply_MSsvc, apply_mem_delivered. simp_regs.
    replace (fd_insert (m_fds md1) (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 off + Z_to_bv 64 nb)))
       with (fds3 (FdFile path (Z_to_bv 64 (off + nb)))) in SB2
       by (rewrite FDS1, FDS, lit_add_lit; reflexivity).
    (* [comment removed for export] *)
    set (m1w := write_to_mem m1 (Z_to_bv 64 dst) bs).
    assert (LBS : Z.of_nat (length bs) <= cnt) by lia.
    assert (VISb : forall i, 0 <= i < Z.of_nat (length bs) -> hidc (ahull A) (Z_to_bv 64 (dst + i)) = false) by (intros i Hi; apply VIS; lia).
    pose proof (aview_write_visible (L:=LPA) A m1 dst bs ltac:(lia) ltac:(lia) VISb) as EVW. fold m1w in EVW.
    pose proof (ainv_fds (L:=LPA) A m1 md1 (fds3 (FdFile path (Z_to_bv 64 (off + nb)))) AINV1) as AINV1'.
    assert (AINV2 : ainv A m1w md2).
    { apply (ainv_framex (L:=LPA) A m1 m1w _ md2 [(dst, dst + cnt)] AINV1').
      - intros a Ha. unfold m1w. apply (write_hidden_same (L:=LPA) A m1 dst bs a); [lia|lia|exact VISb|exact Ha].
      - rewrite EVW. apply munch_write_inside; lia.
      - rewrite EVW. apply (wmono_write_self (L:=LPA)).
      - cbn. split; [| exact I]. right. exact IMGS.
      - exact HMI2.
      - exact SB2. }
    (* [comment removed for export] *)
    pose proof (rw_cells_CB_prefix_write rsegs (aview A m1) dst (Z.to_nat cnt) junk bs DST ltac:(lia)) as DSTw.
    change (wa dst) with (Z_to_bv 64 dst) in DSTw. rewrite <- EVW in DSTw.
    pose proof (mem_inv_store rsegs (aview A m1) (wa dst) bs MI1 (rw_cells_CB_store_ok rsegs (aview A m1) dst (Z.to_nat cnt) junk (length bs) DST ltac:(lia))) as MIw.
    change (wa dst) with (Z_to_bv 64 dst) in MIw. rewrite <- EVW in MIw.
    assert (MUk : munch [(dst, dst + cnt)] (aview A m1) (aview A m1w)) by (rewrite EVW; apply munch_write_inside; lia).
    assert (WMk : wmono rsegs (aview A m1) (aview A m1w)) by (rewrite EVW; apply (wmono_write_self (L:=LPA))).
    clear DST SOK HULL.
    apply (munch_weaken _ [(bv_unsigned sp - 2400, bv_unsigned sp); (dst, dst + cnt)]) in MU; [| unfold sub_fp; cbn [outside]; intros; lia].
    transport_after_call rsegs (aview A m1) (aview A m1w) MUk WMk. clear MUk WMk.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 2400, bv_unsigned sp)] (aview A m1w)) as MU2. pose proof (wmono_refl rsegs (aview A m1w)) as WM2.
    assert (CF2 : client_fpx (L:=LPA) A (aview A m1w) [(bv_unsigned sp - 2400, bv_unsigned sp)]).
    { cbn. split; [| exact I]. left. split; [| exact I]. left. split; [lia|]. split; [lia|].
      pose proof ST1 as STx. pose proof FRc as FRcx. pose proof FRb as FRbx. pose proof FRa as FRax.
      release_frame FRcx STx (bv_unsigned sp + -2128). release_frame FRbx STx (bv_unsigned sp + -2032). release_frame FRax STx (bv_unsigned sp).
      eapply (stk_mapped (L:=LPA)); [exact STx | exact CEIL | lia | lia]. }
    ago AINV2. fold_cl_segs.
    destruct (Z.eq_dec nb 0) as [NB0 | NBpos].
    - (* [comment removed for export] *)
      assert (EBS : bs = []) by (destruct bs; [reflexivity| exfalso; unfold nb in NB0; cbn [length] in NB0; lia]).
      rewrite NB0.
      try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRa); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRb); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRc); icall (rd_tail_zero ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo dst cnt CEIL LO (aview A m1w))
        by (first [exact MIw | exact ST1 | exact FRa | exact FRb | exact FRc | eassumption]).
      lazymatch goal with H : stk _ _ lo (bv_unsigned sp) |- _ => rename H into ST2 end.
      astopx AINV2 MU2 WM2 CF2. rename m0 into m3. rename md0 into md3. rename AINV0 into AINV3.
      pose proof (as_minv LPA A m3 md3 AINV3) as [_ HH3].
      (first [ pose proof ((sbm_io _ md3 SBM0)) as dR_19; dand3 dR_19 as FS3 FDS3 _ | pose proof (sbm_io _ md3 SBM0) as (FS3 & FDS3 & _) ]).
      (first [ pose proof ((sbm_io _ md2 SB2)) as dR_20; dand3 dR_20 as FS2 FDS2 _ | pose proof (sbm_io _ md2 SB2) as (FS2 & FDS2 & _) ]).
      apply (HK m3 md3 AINV3).
      { split; [| split; [| exact HH3]]. rewrite FS3, FS2, m_fs_with_fds; exact FS1. rewrite FDS3, FDS2, m_fds_with_fds. reflexivity. }
      { exact DSTw. }
      unfold read_icpt_post, READ_ICPT_STACK, ERRNO_CELL. rewrite NB0.
      hot_eexists_all. split; [reflexivity|].
      split. { exact MU. }
      split. { exact WM. }
      split; [assumption|]. split; [assumption|]. eexists; eassumption.
    - (* [comment removed for export] *)
      assert (NB1 : 1 <= nb <= cnt) by lia.
      (first [ pose proof ((stage_range_ok (aview A m1w) dst nb (consts_hold_ainv LPA A m1w md2 AINV2) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_21; dand4 dR_21 as IR SOKb QW1 QW2 | destruct (stage_range_ok (aview A m1w) dst nb (consts_hold_ainv LPA A m1w md2 AINV2) ltac:(lia) ltac:(lia) ltac:(lia)) as (IR & SOKb & QW1 & QW2) ]).
      assert (AF : (0 <= dst /\ dst + nb + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
      replace (dst + nb - 1)%Z with (dst + nb + -1)%Z in QW2 by lia.
      destruct (mapped8_le8 _ _ QW1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1 QB1].
      destruct (mapped8_le8 _ _ QW2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2 QB2].
      (first [ dex2 SOKb as ng lastb; dand3 SOKb as NG SH LBl | dand5 SOKb as ng lastb NG SH LBl | destruct SOKb as (ng & lastb & NG & SH & LBl) ]).
      try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRa); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRb); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRc); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_QB1); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_QB2); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_SH); icall (rd_tail_pos ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo dst cnt CEIL LO DSTR CNT (aview A m1w) _ _ _ nb ng lastb w1 w2)
        by (first [exact NB1 | exact MIw | exact ST1 | exact FRa | exact FRb | exact FRc | exact IR | exact NG | exact SH | exact LBl | exact QB1 | exact QB2 | eassumption]).
      astopx AINV2 MU2 WM2 CF2. rename m0 into m3. rename md0 into md3. rename AINV0 into AINV3.
      pose proof (as_minv LPA A m3 md3 AINV3) as [_ HH3].
      (first [ pose proof ((sbm_io _ md3 SBM0)) as dR_23; dand3 dR_23 as FS3 FDS3 _ | pose proof (sbm_io _ md3 SBM0) as (FS3 & FDS3 & _) ]).
      (first [ pose proof ((sbm_io _ md2 SB2)) as dR_24; dand3 dR_24 as FS2 FDS2 _ | pose proof (sbm_io _ md2 SB2) as (FS2 & FDS2 & _) ]).
      apply (HK m3 md3 AINV3).
      { split; [| split; [| exact HH3]]. rewrite FS3, FS2, m_fs_with_fds; exact FS1. rewrite FDS3, FDS2, m_fds_with_fds. reflexivity. }
      { exact DSTw. }
      unfold read_icpt_post, READ_ICPT_STACK, ERRNO_CELL.
      hot_eexists_all. split; [reflexivity|].
      split. { exact MU. }
      split. { exact WM. }
      split; [assumption|]. split; [assumption|]. eexists; eassumption.
  Qed.

  Lemma read_icpt_stage_dir_ok : read_icpt_stage_dir_stmt.
  Proof.
    unfold read_icpt_stage_dir_stmt. intros until K. cbv zeta. intros AINV MI CELLS TP A0 A1 A2 CNT DST FDS ST LO CEIL [e0 ERR] HK.
    (first [ dand3 CELLS as INI RR MC | destruct CELLS as (INI & RR & MC) ]). unfold READ_ICPT_STACK in LO. unfold ERRNO_CELL in ERR.
    pose proof INI as INI'. unfold asan_inited_cell in INI'. pose proof RR as RR'. unfold REAL_READ_CELL, MUSL_READ in RR'.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    remember READ_STAGE as dst eqn:Edst. unfold READ_STAGE in Edst.
    pose proof alloc_ceiling_val as ACV.
    assert (DSTR : 0 <= dst /\ dst + cnt <= 2^47) by lia.
    assert (IMGS : img_client (L:=LPA) dst (dst + cnt)).
    { rewrite Edst. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
    pose proof (munch_refl [(bv_unsigned sp - 2400, bv_unsigned sp)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) [(bv_unsigned sp - 2400, bv_unsigned sp)]).
    { cbn. split; [| exact I]. left. split; [| exact I]. left. split; [lia|]. split; [lia|].
      eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]. }
    (* [comment removed for export] *)
    ago AINV. fold_cl_segs.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_RR); icall (read_walk1 ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo dst cnt CEIL LO a0 a1 a2 (aview A m) 3)
      by (rewrite ?unsigned_lit by lia; first [exact MI | exact ST | exact INI' | exact RR' | exact A0 | exact A1 | exact A2 | lia]).
    lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -2032) _ |- _ => rename H into FRa end.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -2128) _ |- _ => rename H into FRb end.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -2144) _ |- _ => rename H into FRc end.
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    astop_svcx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
    pose proof (as_minv LPA A m1 md1 AINV1) as [HMI1 HH1].
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_26; dand3 dR_26 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    (first [ pose proof ((view_rw_cells_real (L:=LPA) A m1 md1 dst (Z.to_nat cnt) junk AINV1 DST)) as dR_27; dand3 dR_27 as SOK HULL VIS | destruct (view_rw_cells_real (L:=LPA) A m1 md1 dst (Z.to_nat cnt) junk AINV1 DST) as (SOK & HULL & VIS) ]).
    eapply (srz_read_dir_hull (cl_segs LPA) _ md1 (Z_to_bv 64 63)) with (fd := Z_to_bv 64 3) (cnt := cnt);
      [ exact HH1 | reflexivity | reflexivity | reflexivity
      | rewrite unsigned_lit by lia; lia
      | rewrite FDS1, FDS; reflexivity
      | reflexivity
      | unfold MAX_RW_COUNT; lia
      | rewrite ms_gpr_MSsvc; simp_regs; rewrite ?unsigned_lit by lia; unfold TASK_SIZE; lia
      | rewrite ms_gpr_MSsvc; simp_regs; exact SOK
      | ].
    rewrite advance_set_gpr0_MSsvc. simp_regs. rewrite (errno_ret_neg EISDIR) by (unfold EISDIR; lia).
    (* [comment removed for export] *)
    apply (munch_weaken _ [(bv_unsigned sp - 2400, bv_unsigned sp); (6191924, 6191924 + 4)]) in MU; [| unfold sub_fp; cbn [outside]; intros; lia].
    pose proof (munch_refl [(bv_unsigned sp - 2400, bv_unsigned sp); (6191924, 6191924 + 4)] (aview A m1)) as MU2. pose proof (wmono_refl rsegs (aview A m1)) as WM2.
    assert (CF2 : client_fpx (L:=LPA) A (aview A m1) [(bv_unsigned sp - 2400, bv_unsigned sp); (6191924, 6191924 + 4)]).
    { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|].
        pose proof ST1 as STx. pose proof FRc as FRcx. pose proof FRb as FRbx. pose proof FRa as FRax.
        release_frame FRcx STx (bv_unsigned sp + -2128). release_frame FRbx STx (bv_unsigned sp + -2032). release_frame FRax STx (bv_unsigned sp).
        replace (bv_unsigned sp - (bv_unsigned sp - 2400)) with 2400 by lia.
        eapply (stk_mapped (L:=LPA)); [exact STx | exact CEIL | lia | lia]. }
      split; [| exact I]. right. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
    ago AINV1. fold_cl_segs.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRa); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRb); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRc); icall (rd_tail_neg ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo dst cnt CEIL LO (aview A m1) _ _ _ _ _ _ _ _ _ _ EISDIR e0)
      by (first [exact MI1 | exact ST1 | exact FRa | exact FRb | exact FRc | exact ERR | exact TP | unfold EISDIR; lia | eassumption]).
    lazymatch goal with H : rw_cells _ _ 6191924 _ |- _ => rename H into ERR2 end.
    astopx AINV1 MU2 WM2 CF2. rename m0 into m3. rename md0 into md3. rename AINV0 into AINV3.
    pose proof (as_minv LPA A m3 md3 AINV3) as [_ HH3].
    (first [ pose proof ((sbm_io _ md3 SBM0)) as dR_28; dand3 dR_28 as FS3 FDS3 _ | pose proof (sbm_io _ md3 SBM0) as (FS3 & FDS3 & _) ]).
    apply (HK m3 md3 AINV3).
    { split; [| split; [| exact HH3]]. rewrite FS3; exact FS1. rewrite FDS3, FDS1; exact FDS. }
    { exact DST. }
    { exact ERR2. }
    unfold read_icpt_post, READ_ICPT_STACK, ERRNO_CELL.
    hot_eexists_all. split; [reflexivity|].
    split. { exact MU. }
    split. { exact WM. }
    split; [assumption|]. split; [assumption|]. eexists; eassumption.
  Qed.
End Leaves.
End DA_Read.

Module DA_Ouhu.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr SysStep RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img A_ImgAny.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Se7o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Eg3i DA_Cells DA_Ldix DA_Entry DA_Mib4 DA_Inv DA_Ejgo DA_Main.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes.DA_Myrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ldix OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Entry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Mib4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ejgo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Main OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Open.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)


Section Walks.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (lo : Z).
  Hypothesis CEIL : alloc_ceiling <= lo.
  #[local] Notation rom := (seg_rom rsegs).

  (* [comment removed for export] *)
  Definition openA_post (p1 : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m' j8,
      ms' = MS (mkR (Z_to_bv 64 0x86838) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 2) s1
                    (Z_to_bv 64 p1) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 OPEN_ENTRY) fc None m' rom
      /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp + -80)
      /\ rw_cells rsegs m' (bv_unsigned sp + -80) [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 RA_MAIN)].

  #[using="CEIL Clg"] Lemma open_walkA : forall (ap p1 : Z) (m : word -> option byte),
    lo + 80 <= bv_unsigned sp -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
    bv_unsigned sp <= ap -> ap + 16 <= 2^64 -> 0 <= p1 < 2^64 ->
    ro_cells rsegs m (ap + 8) [C8 (Z_to_bv 64 p1)] ->
    evt rsegs (openA_post p1 m)
        (MS (mkR (Z_to_bv 64 RA_MAIN) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 2) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MAIN_PC) fc None m rom).
  Proof.
    intros ap p1 m LO MI ST AP0 AP1 P1 AV. unfold MAIN_PC, RA_MAIN in *.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 80%nat ST.
    run_to 0x86824. at_pc 0x86824.
    azstep. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    run_to 0x86834. at_pc 0x86834. bstep. apply evt_done. unfold openA_post, OPEN_ENTRY.
    eexists _, _. split; [reflexivity|]. repeat (split; [eassumption|]). exact FR.
  Qed.

  (* [comment removed for export] *)
  Definition openBq_post (spf : word) (p1 : Z) (y0 y1 y2 : word) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x86a5c) spf gp tp y0 y1 y2 (Z_to_bv 64 2) s1
                    (Z_to_bv 64 STDERR_F) (Z_to_bv 64 0x1de96) (Z_to_bv 64 p1) a3 a4 a5 a6 a7 (Z_to_bv 64 p1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 FPRINTF_ICPT_ENTRY) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

  Lemma open_walkB : forall (spf : word) (p1 r : Z) (y0 y1 y2 ya1 ya2 : word) (m : word -> option byte),
    mem_inv rsegs m -> r < 0 -> -4096 <= r ->
    ro_cells rsegs m 0xa97d8 [C8 (Z_to_bv 64 0xa8a68)] ->
    ro_cells rsegs m STDERR_CELL [C8 (Z_to_bv 64 STDERR_F)] ->
    evt rsegs (openBq_post spf p1 y0 y1 y2 m)
        (MS (mkR (Z_to_bv 64 0x86838) spf gp tp y0 y1 y2 (Z_to_bv 64 2) s1 (Z_to_bv 64 r) ya1 ya2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 p1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86838) fc None m rom).
  Proof.
    intros spf p1 r y0 y1 y2 ya1 ya2 m MI R1 R2 GOT SC. unfold STDERR_CELL, STDERR_F in *.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    azstep. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. blia. } clear K.
    run_to 0x86a58. at_pc 0x86a58. bstep. apply evt_done. unfold openBq_post, FPRINTF_ICPT_ENTRY.
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

  (* [comment removed for export] *)
  Definition openC_post (spf : word) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 : word) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x86a88) spf gp tp y0 y1 y2 (Z_to_bv 64 2) s1 (Z_to_bv 64 2) y3 y4 y5 y6 y7 y8 y9
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y10 y11 y12 y13)
               F (Z_to_bv 64 EXIT_ENTRY) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

  Lemma open_walkC : forall (spf r y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 : word) (m : word -> option byte),
    mem_inv rsegs m ->
    evt rsegs (openC_post spf y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 m)
        (MS (mkR (Z_to_bv 64 0x86a5c) spf gp tp y0 y1 y2 (Z_to_bv 64 2) s1 r y3 y4 y5 y6 y7 y8 y9
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y10 y11 y12 y13)
            F (Z_to_bv 64 0x86a5c) fc None m rom).
  Proof.
    intros spf r y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 m MI.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    bstep. bstep. bstep. apply evt_done. unfold openC_post, EXIT_ENTRY.
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.
End Walks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section OpenPhase.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  Variable usp : Z.
  Hypothesis HCEIL : alloc_ceiling = usp - 0x800000.   (* [comment removed for export] *)
  Variables argv envp : list (list byte).
  Variable fs : Fs.
  Hypothesis Hva : valid_argv argv.
  Hypothesis FPRINTF : fprintf_diag_stmt.
  Hypothesis EXIT : exit_spec_stmt.
  #[local] Notation rom := (seg_rom rsegs).
  #[local] Notation p1a := (e_p1a usp argv envp).

  Lemma fds_std_2 : fd_lookup fds_std (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Ltac ulit := rewrite ?unsigned_lit by (unfold SPF, STK_LO in *; lia).

  #[using="EXIT FPRINTF Hva HCEIL"] Lemma cannot_open_tail :
    forall (gp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word)
           (F : bvmap 5 word) (fc : bv 32) (r : Z) m md A tid,
      r < 0 -> -4096 <= r -> 2 <= e_argc argv ->
      ainv A m md -> mem_inv rsegs (aview A m) -> m_fs md = fs -> m_fds md = fds_std ->
      ccells (aview A m) tid SO_pristine 0 -> args_at usp argv envp (aview A m) ->
      (forall a, in_stksh a -> aview A m (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) ->
      stk rsegs (aview A m) (STK_LO usp) (SPF usp) ->
      srealizes rsegs
        (mkCfg (MS (mkR (Z_to_bv 64 0x86838) (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) y0 y1 y2 (Z_to_bv 64 2) s1 (Z_to_bv 64 r)
                        ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 p1a) s3 s4 s5 s6 s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6)
                   F (Z_to_bv 64 0x86838) fc None m rom) md)
        (t_die (msg_cannot_open (nth 1 argv [])) fs).
  Proof.
    intros until tid. intros R1 R2 A2 AINV MI FS FDS CC AR SH ST.
    (first [ pose proof (CC) as dR_1; dand4 dR_1 as MC [fe [FOK FE]] SO TR | pose proof CC as (MC & [fe [FOK FE]] & SO & TR) ]). pose proof AR as [P0 P1 S0 S1 K0 K1 B0 B1 (U1 & U2 & U3 & U4)].
    unfold sp_window_lo in U1.
    pose proof Hva as (AC & _ & ALEN & ANUL & APATH).
    assert (CEIL : alloc_ceiling <= STK_LO usp) by (unfold STK_LO; rewrite HCEIL; lia).
    assert (L1B : Z.of_nat (length (nth 1 argv [])) <= 131071).
    { destruct argv as [|a [|b l]]; cbn; try lia. exact (Forall_inv (Forall_inv_tail ALEN)). }
    assert (N1 : ~ In (Z_to_bv 8 0) (nth 1 argv [])).
    { destruct argv as [|a [|b l]]; cbn; try tauto. exact (Forall_inv (Forall_inv_tail ANUL)). }
    pose proof (consts_hold_ainv LPA A m md AINV) as CH.
    assert (GOTC : ro_cells rsegs (aview A m) 0xa97d8 [C8 (Z_to_bv 64 0xa8a68)]).
    { apply ro_C8_of_bytes. apply (consts_lookup _ 0xa97d8 _ CH). vm_compute. reflexivity. }
    pose proof (mc_stderrp _ _ MC) as SC. unfold STDERR_CELL in SC.
    (* [comment removed for export] *)
    pose proof (munch_refl [] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) []) by exact I.
    ago AINV. fold_cl_segs.
    icall (open_walkB gp (Z_to_bv 64 TPV) s1 ya3 ya4 ya5 ya6 ya7 s3 s4 s5 s6 s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6 F fc
             (Z_to_bv 64 (SPF usp)) p1a r y0 y1 y2 ya1 ya2 (aview A m))
      by (first [exact MI | exact GOTC | exact SC | lia]).
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    astopx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_2; dand3 dR_2 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    assert (SO1 : stack_only usp []) by apply stack_only_nil.
    (first [ pose proof ((bundle_stack usp argv envp HCEIL _ _ _ tid SO_pristine 0 MU SO1 ltac:(unfold sp_window_lo; lia) U2 CC AR SH)) as dR_3; dand4 dR_3 as CC1 AR1 SH1 GOT1 | destruct (bundle_stack usp argv envp HCEIL _ _ _ tid SO_pristine 0 MU SO1 ltac:(unfold sp_window_lo; lia) U2 CC AR SH) as (CC1 & AR1 & SH1 & GOT1) ]).
    lazymatch goal with H : stk _ (aview A m1) _ _ |- _ => rename H into ST1 end.
    clear CC AR SH MC FE SO.
    (first [ pose proof (CC1) as dR_4; dand4 dR_4 as MC1 [fe1 [FOK1 FE1]] SOUT1 TR1 | pose proof CC1 as (MC1 & [fe1 [FOK1 FE1]] & SOUT1 & TR1) ]).
    (first [ pose proof ((aa_s1k _ _ _ _ AR1 A2)) as dR_5; dex1 dR_5 as sl1; destruct dR_5 as [SL1 SB1] | pose proof ((aa_s1k _ _ _ _ AR1 A2)) as dR_5; dand3 dR_5 as sl1 SL1 SB1 | destruct (aa_s1k _ _ _ _ AR1 A2) as (sl1 & SL1 & SB1) ]).
    (* [comment removed for export] *)
    unfold t_die.
    pose proof FPRINTF as FP. unfold fprintf_diag_stmt in FP. cbv zeta in FP.
    eapply FP with (d := DF_cannot_open) (arg := nth 1 argv []) (slack := sl1) (pa := p1a) (fe := fe1) (lo := STK_LO usp); clear FP.
    6:{ cbn [diag_fmt_addr]. split; [reflexivity|]. split; [exact SB1|]. split; [exact N1|].
        pose proof (aa_b1 _ _ _ _ AR1 A2) as B1'. pose proof (aa_b0 _ _ _ _ AR1) as B0'.
        (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). ulit. rewrite SL1.
        unfold e_p1a, e_p0a, e_L0, e_L1, e_argc, e_envc, e_span, SPF in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [lia | Z.div_mod_to_equations; lia]. }
    all: lazymatch goal with
         | |- ainv _ _ _ => exact AINV1
         | |- mem_inv _ _ => exact MI1
         | |- stk _ _ _ _ => ulit; exact ST1
         | |- file_at _ _ _ => exact FE1
         | |- stderr_ok _ => exact FOK1
         | |- fd_lookup _ _ = _ => rewrite FDS1, FDS; apply fds_std_2
         | |- bytes_at _ _ (sh _) _ => apply stksh_bytes; exact SH1
         | |- (exists j8, rw_cells _ _ STDERR_BUFP _) => apply errbuf_any
         | |- (exists g, ro_cells _ _ SSP_GUARD _) => exact (mc_canary _ _ MC1)
         | |- ro_cells _ _ SSP_GOT _ => exact GOT1
         | |- @eq word _ _ => reflexivity
         | |- _ /\ _ => cbn [diag_fmt_addr]; split; [reflexivity|]; split; [exact SB1|]; split; [exact N1|];
                        pose proof (aa_b1 _ _ _ _ AR1 A2) as B1'; pose proof (aa_b0 _ _ _ _ AR1) as B0';
                        (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); ulit; rewrite SL1;
                        unfold e_p1a, e_p0a, e_L0, e_L1, e_argc, e_envc, e_span, SPF in *; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [lia | Z.div_mod_to_equations; lia]
         | |- t_exit _ _ [] => apply t_emit_has_nil
         | |- forall m', _ => idtac
         | |- _ => ulit; unfold FPRINTF_ICPT_STACK, STK_LO, SPF in *; first [lia | Z.div_mod_to_equations; lia]
         end.
    (* [comment removed for export] *)
    (intros m2 md2 fe2 rr AINV2; (first [ intro dR_19; dand3 dR_19 as FS2 FDS2 HH2 | intros (FS2 & FDS2 & HH2) ]); intros FOK2 FE2 ms' POST).
    (first [ dex14 POST as z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13; dand5 POST as -> MU2 WM2 MI2 ST2 | dand19 POST as z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 -> MU2 WM2 MI2 ST2 | destruct POST as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & -> & MU2 & WM2 & MI2 & ST2) ]).
    rewrite ?unsigned_lit in MU2, ST2 by (unfold SPF, STK_LO in *; lia).
    replace (ret_pc (Z_to_bv 64 0x86a5c)) with (Z_to_bv 64 0x86a5c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (AGM : agree_on (in_ranges MC_RANGES) (aview A m1) (aview A m2)).
    { apply (agree_of_munch _ _ _ _ MU2). unfold SPF in *. ranges_outside. }
    assert (AGO : agree_on (in_ranges STDOUT_RANGES) (aview A m1) (aview A m2)).
    { apply (agree_of_munch _ _ _ _ MU2). unfold SPF in *. ranges_outside. }
    assert (AGT : agree_on (in_ranges TR_RANGES) (aview A m1) (aview A m2)).
    { apply (agree_of_munch _ _ _ _ MU2). unfold SPF in *. ranges_outside. }
    assert (CC2 : ccells (aview A m2) tid SO_pristine 0).
    { split; [eapply mcells_agree; [exact AGM| exact MC1]|]. split; [exists fe2; split; assumption|].
      split; [eapply stdout_at_agree; [exact AGO| exact SOUT1]|]. revert TR1 AGT. clear. intros TR1 AGT.
      exact (trcells_agree _ _ _ AGT TR1).   (* [comment removed for export] *) }
    pose proof (munch_refl [] (aview A m2)) as MU3. pose proof (wmono_refl rsegs (aview A m2)) as WM3.
    assert (CF3 : client_fpx (L:=LPA) A (aview A m2) []) by exact I.
    ago AINV2. fold_cl_segs.
    icall (open_walkC gp (Z_to_bv 64 TPV) s1 (Z_to_bv 64 p1a) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
             (Z_to_bv 64 (SPF usp)) rr z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 (aview A m2))
      by (exact MI2).
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
    astopx AINV2 MU3 WM3 CF3. rename m0 into m3. rename md0 into md3. rename AINV0 into AINV3.
    (first [ pose proof ((sbm_io md2 md3 SBM0)) as dR_7; dand3 dR_7 as FS3 FDS3 _ | pose proof (sbm_io md2 md3 SBM0) as (FS3 & FDS3 & _) ]).
    assert (CC3 : ccells (aview A m3) tid SO_pristine 0).
    { eapply ccells_agree; [| exact CC2]. apply (agree_of_munch _ _ _ _ MU3). ranges_outside. }
    lazymatch goal with H : stk _ (aview A m3) _ _ |- _ => rename H into ST3 end.
    (* [comment removed for export] *)
    apply (srz_conseq _ _ (t_emit (W 1 (pending_of SO_pristine)) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs md3)))).
    - eapply (exit_via EXIT); try eassumption.
      all: lazymatch goal with
           | |- ro_cells _ _ SSP_GOT _ => exact (mc_sspgot _ _ (proj1 CC3))
           | |- @eq word _ _ => reflexivity
           | |- stk _ _ _ _ => ulit; exact ST3
           | |- pending_of _ <> [] -> _ => cbn [pending_of]; intros NE; exfalso; apply NE; reflexivity
           | |- _ => ulit; unfold EXIT_STACK, STK_LO, SPF in *; lia
           end.
    - cbn [pending_of W map]. rewrite FS3, FS2, FS1, FS.
      replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; vm_compute; reflexivity).
      apply t_emit_nil_eq. apply t_emit_has_nil.
  Qed.

  (* [comment removed for export] *)
  #[using="HCEIL"] Lemma to_open_call :
    forall (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           m md A (T : TSet),
      dinv usp argv envp fs A m md usp fds_std SO_pristine 0 -> e_argc argv = 2 ->
      (forall m1 md1 tid j8,
          ainv A m1 md1 -> mem_inv rsegs (aview A m1) -> m_fs md1 = fs -> m_fds md1 = fds_std ->
          ccells (aview A m1) tid SO_pristine 0 -> args_at usp argv envp (aview A m1) ->
          (forall a, in_stksh a -> aview A m1 (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) ->
          stk rsegs (aview A m1) (STK_LO usp) (SPF usp) ->
          rw_cells rsegs (aview A m1) (SPF usp) [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 RA_MAIN)] ->
          srealizes rsegs
            (mkCfg (MS (mkR (Z_to_bv 64 0x86838) (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) t0 t1 t2 (Z_to_bv 64 2) s1
                            (Z_to_bv 64 p1a) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p1a) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 OPEN_ENTRY) fc None m1 rom) md1) T) ->
      srealizes rsegs (main_cfg usp argv gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md) T.
  Proof.
    intros until T. intros DI A2 K.
    pose proof DI as DI'. destruct DI' as [AINV MI FS FDS FRN ST SPC SH [tid CC] GOT AR].
    pose proof AR as [P0 P1 S0 S1 K0 K1 B0 B1 (U1 & U2 & U3 & U4)]. unfold sp_window_lo in U1.
    assert (CEIL : alloc_ceiling <= STK_LO usp) by (unfold STK_LO; rewrite HCEIL; lia).
    assert (AV : ro_cells rsegs (aview A m) (usp + 8 + 8) [C8 (Z_to_bv 64 p1a)]).
    { apply ro_C8_of_bytes. replace (usp + 8 + 8) with (usp + 16) by lia. exact (P1 ltac:(lia)). }
    unfold main_cfg, MAIN_PC, RA_MAIN, SPM.
    pose proof (munch_refl [(usp - 48 - 80, usp - 48)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (ST0 : stk rsegs (aview A m) (STK_LO usp) (bv_unsigned (Z_to_bv 64 (usp - 48)))).
    { rewrite unsigned_lit by lia. (first [ dand3 ST as X0 X1 X | destruct ST as (X0 & X1 & X) ]). split; [exact X0|]. split; [lia|]. intros a Ha. apply X. lia. }
    assert (CF : client_fpx (L:=LPA) A (aview A m) [(usp - 48 - 80, usp - 48)]).
    { cbn. split; [| exact I]. left. split; [| exact I]. left. split; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold STK_LO in *; lia|]. split; [lia|].
      eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | unfold STK_LO in *; lia | lia]. }
    rewrite A2.
    ago AINV. fold_cl_segs.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_GOT); icall (open_walkA (Z_to_bv 64 (usp - 48)) gp (Z_to_bv 64 TPV) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc (STK_LO usp) CEIL (usp + 8) p1a (aview A m))
      by (first [exact MI | exact ST0 | exact AV | rewrite ?unsigned_lit by lia; unfold e_argc, e_p1a, e_p0a, e_envc, e_L0, e_L1, e_span, STK_LO in *; lia]).
    lazymatch goal with H : stk _ _ _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : rw_cells _ _ _ [CB 8 _; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 _] |- _ => rename H into FR1 end.
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    astopx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_9; dand3 dR_9 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    assert (SO1 : stack_only usp [(usp - 48 - 80, usp - 48)]) by (apply stack_only_cons; [unfold STK_LO; lia| lia| apply stack_only_nil]).
    (first [ pose proof ((bundle_stack usp argv envp HCEIL _ _ _ tid SO_pristine 0 MU SO1 ltac:(unfold sp_window_lo; lia) U2 CC AR SH)) as dR_10; dand4 dR_10 as CC1 AR1 SH1 GOT1 | destruct (bundle_stack usp argv envp HCEIL _ _ _ tid SO_pristine 0 MU SO1 ltac:(unfold sp_window_lo; lia) U2 CC AR SH) as (CC1 & AR1 & SH1 & GOT1) ]).
    rewrite ?unsigned_lit in ST1, FR1 by lia.
    replace (usp - 48 + -80) with (SPF usp) in ST1, FR1 |- * by (unfold SPF; lia).
    apply (K m1 md1 tid _ AINV1 MI1 ltac:(rewrite FS1; exact FS) ltac:(rewrite FDS1; exact FDS) CC1 AR1 SH1 ST1 FR1).
  Qed.

  #[using="EXIT FPRINTF Hva HCEIL"] Theorem open_fail_ok2 : open_fail_stmt' usp argv envp fs.
  Proof.
    unfold open_fail_stmt'. intros until md. intros A a0s path DI EA AV CASE.
    assert (A2 : e_argc argv = 2) by (rewrite AV; reflexivity).
    assert (P1E : nth 1 argv [] = path) by (rewrite AV; reflexivity).
    pose proof Hva as (AC & _ & ALEN & ANUL & APATH).
    assert (N1 : ~ In (Z_to_bv 8 0) path) by (rewrite <- P1E, AV; cbn; rewrite AV in ANUL; exact (Forall_inv (Forall_inv_tail ANUL))).
    apply (to_open_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md A _ DI A2).
    intros m1 md1 tid j8 AINV1 MI1 FS1 FDS1 CC1 AR1 SH1 ST1 FR1.
    pose proof AR1 as [P0 P1 S0 S1 K0 K1 B0 B1 (U1 & U2 & U3 & U4)]. unfold sp_window_lo in U1.
    assert (CEIL : alloc_ceiling <= STK_LO usp) by (unfold STK_LO; rewrite HCEIL; lia).
    (first [ pose proof (CC1) as dR_11; dand4 dR_11 as MC1 _ _ _ | pose proof CC1 as (MC1 & _ & _ & _) ]).
    (* [comment removed for export] *)
    pose proof (open_fail_ok (AI:=AI)) as OF. unfold open_fail_stmt in OF. cbv zeta in OF.
    eapply OF with (p1 := p1a) (path := path) (lo := STK_LO usp); clear OF.
    - exact AINV1.
    - unfold open_pre. rewrite <- P1E. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try reflexivity.
      + exact (aa_s1 _ _ _ _ AR1 ltac:(lia)).
      + rewrite P1E. exact N1.
      + ulit. pose proof (aa_b0 _ _ _ _ AR1). unfold e_p1a, e_p0a, e_L0, SPF in *. lia.
      + exact MI1.
      + split; [exact (mc_sspgot _ _ MC1)| exact (mc_canary _ _ MC1)].
      + ulit. exact ST1.
      + ulit. unfold OPEN_STACK, STK_LO, SPF in *. lia.
      + exact CEIL.
      + apply rw_errno_any.
    - rewrite FS1. assert (PP : path_has_slash path = false /\ path_eqb path dotdot_path = false)
        by (rewrite AV in APATH; exact (Forall_inv APATH)).
      destruct PP as [PS PD].
      destruct CASE as [C|[C|(C1 & C2 & C3 & C4)]]; [left; exact C| right; left; exact C| right; right; exact (conj C1 (conj C2 (conj PD (conj PS (conj C3 C4)))))].
    - (intros m2 md2 AINV2; (first [ intro dR_20; dand3 dR_20 as FS2 FDS2 HH2 | intros (FS2 & FDS2 & HH2) ]); intros ms' POST).
      (first [ dex14 POST as y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6; dand6 POST as -> MU2 WM2 MI2 ST2 _ | dand20 POST as y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 -> MU2 WM2 MI2 ST2 _ | destruct POST as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6 & -> & MU2 & WM2 & MI2 & ST2 & _) ]).
      cbn [OPEN_STACK] in MU2. rewrite ?unsigned_lit in MU2, ST2 by (unfold SPF, STK_LO in *; lia).
      replace (ret_pc (Z_to_bv 64 0x86838)) with (Z_to_bv 64 0x86838) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (SO2 : stack_only usp [(SPF usp - 112, SPF usp); (ERRNO_CELL, ERRNO_CELL + 4)]).
      { apply stack_only_cons; [unfold SPF, STK_LO; lia| unfold SPF; lia|]. unfold ERRNO_CELL. apply stack_only_cons_errno. apply stack_only_nil. }
      (first [ pose proof ((bundle_stack usp argv envp HCEIL _ _ _ tid SO_pristine 0 MU2 SO2 ltac:(unfold sp_window_lo; lia) U2 CC1 AR1 SH1)) as dR_13; dand4 dR_13 as CC2 AR2 SH2 GOT2 | destruct (bundle_stack usp argv envp HCEIL _ _ _ tid SO_pristine 0 MU2 SO2 ltac:(unfold sp_window_lo; lia) U2 CC1 AR1 SH1) as (CC2 & AR2 & SH2 & GOT2) ]).
      rewrite <- P1E.
      apply (cannot_open_tail gp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 F fc (-1) m2 md2 A tid);
        try assumption; try lia.
      + rewrite FS2. exact FS1.
      + rewrite FDS2. exact FDS1.
  Qed.

  (* [comment removed for export] *)
  #[using="EXIT FPRINTF Hva HCEIL"] Lemma open_phase :
    forall (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           m md A (e : FdEntry) (TB : TSet),
      dinv usp argv envp fs A m md usp fds_std SO_pristine 0 -> e_argc argv = 2 ->
      (length (nth 1 argv []) <= 4095)%nat ->
      (   (nth 1 argv [] = dot_path /\ e = FdDir)
       \/ (nth 1 argv [] <> [] /\ nth 1 argv [] <> dot_path /\ path_eqb (nth 1 argv []) dotdot_path = false /\ path_has_slash (nth 1 argv []) = false /\
           (exists d, fs_lookup fs (nth 1 argv []) = Some d) /\ e = FdFile (nth 1 argv []) (Z_to_bv 64 0))) ->
      (forall m2 md2 tid j8 (y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
          ainv A m2 md2 -> mem_inv rsegs (aview A m2) -> m_fs md2 = fs -> m_fds md2 = fds3 e ->
          ccells (aview A m2) tid SO_pristine 0 -> args_at usp argv envp (aview A m2) ->
          (forall a, in_stksh a -> aview A m2 (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) ->
          stk rsegs (aview A m2) (STK_LO usp) (SPF usp) ->
          rw_cells rsegs (aview A m2) (SPF usp) [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 RA_MAIN)] ->
          srealizes rsegs
            (mkCfg (MS (mkR (Z_to_bv 64 0x86838) (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) y0 y1 y2 (Z_to_bv 64 2) s1 (Z_to_bv 64 3)
                            ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 p1a) s3 s4 s5 s6 s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6)
                       F (Z_to_bv 64 0x86838) fc None m2 rom) md2) TB) ->
      srealizes rsegs (main_cfg usp argv gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md)
                (t_alt2 (t_die (msg_cannot_open (nth 1 argv [])) fs) TB).
  Proof.
    intros until TB. intros DI A2 LEN CASE KB.
    pose proof Hva as (AC & _ & ALEN & ANUL & APATH).
    assert (N1 : ~ In (Z_to_bv 8 0) (nth 1 argv [])).
    { destruct argv as [|a [|b l]]; cbn; try tauto. exact (Forall_inv (Forall_inv_tail ANUL)). }
    apply (to_open_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md A _ DI A2).
    intros m1 md1 tid j8 AINV1 MI1 FS1 FDS1 CC1 AR1 SH1 ST1 FR1.
    pose proof AR1 as [P0 P1 S0 S1 K0 K1 B0 B1 (U1 & U2 & U3 & U4)]. unfold sp_window_lo in U1.
    assert (CEIL : alloc_ceiling <= STK_LO usp) by (unfold STK_LO; rewrite HCEIL; lia).
    (first [ pose proof (CC1) as dR_14; dand4 dR_14 as MC1 _ _ _ | pose proof CC1 as (MC1 & _ & _ & _) ]).
    pose proof (open_ok_ok (AI:=AI)) as OK. unfold open_ok_stmt in OK. cbv zeta in OK.
    eapply OK with (p1 := p1a) (path := nth 1 argv []) (lo := STK_LO usp) (e := e); clear OK.
    - exact AINV1.
    - unfold open_pre. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try reflexivity.
      + exact (aa_s1 _ _ _ _ AR1 ltac:(lia)).
      + exact N1.
      + ulit. pose proof (aa_b0 _ _ _ _ AR1). unfold e_p1a, e_p0a, e_L0, SPF in *. lia.
      + exact MI1.
      + split; [exact (mc_sspgot _ _ MC1)| exact (mc_canary _ _ MC1)].
      + ulit. exact ST1.
      + ulit. unfold OPEN_STACK, STK_LO, SPF in *. lia.
      + exact CEIL.
      + apply rw_errno_any.
    - exact FDS1.
    - exact LEN.
    - rewrite FS1. exact CASE.
    - (* [comment removed for export] *)
      (intros m2 md2 AINV2; (first [ intro dR_21; dand3 dR_21 as FS2 FDS2 HH2 | intros (FS2 & FDS2 & HH2) ]); intros ms' POST).
      (first [ dex14 POST as y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6; dand6 POST as -> MU2 WM2 MI2 ST2 _ | dand20 POST as y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 -> MU2 WM2 MI2 ST2 _ | destruct POST as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6 & -> & MU2 & WM2 & MI2 & ST2 & _) ]).
      cbn [OPEN_STACK] in MU2. rewrite ?unsigned_lit in MU2, ST2 by (unfold SPF, STK_LO in *; lia).
      replace (ret_pc (Z_to_bv 64 0x86838)) with (Z_to_bv 64 0x86838) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (SO2 : stack_only usp [(SPF usp - 112, SPF usp); (ERRNO_CELL, ERRNO_CELL + 4)]).
      { apply stack_only_cons; [unfold SPF, STK_LO; lia| unfold SPF; lia|]. unfold ERRNO_CELL. apply stack_only_cons_errno. apply stack_only_nil. }
      (first [ pose proof ((bundle_stack usp argv envp HCEIL _ _ _ tid SO_pristine 0 MU2 SO2 ltac:(unfold sp_window_lo; lia) U2 CC1 AR1 SH1)) as dR_16; dand4 dR_16 as CC2 AR2 SH2 GOT2 | destruct (bundle_stack usp argv envp HCEIL _ _ _ tid SO_pristine 0 MU2 SO2 ltac:(unfold sp_window_lo; lia) U2 CC1 AR1 SH1) as (CC2 & AR2 & SH2 & GOT2) ]).
      apply (cannot_open_tail gp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 F fc (-1) m2 md2 A tid);
        try assumption; try lia.
      all: first [rewrite FS2; exact FS1 | rewrite FDS2; exact FDS1].
    - (* [comment removed for export] *)
      (intros m2 md2 AINV2; (first [ intro dR_22; dand3 dR_22 as FS2 FDS2 HH2 | intros (FS2 & FDS2 & HH2) ]); intros ms' POST).
      (first [ dex14 POST as y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6; dand6 POST as -> MU2 WM2 MI2 ST2 _ | dand20 POST as y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 -> MU2 WM2 MI2 ST2 _ | destruct POST as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6 & -> & MU2 & WM2 & MI2 & ST2 & _) ]).
      cbn [OPEN_STACK] in MU2. rewrite ?unsigned_lit in MU2, ST2 by (unfold SPF, STK_LO in *; lia).
      replace (ret_pc (Z_to_bv 64 0x86838)) with (Z_to_bv 64 0x86838) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (SO2 : stack_only usp [(SPF usp - 112, SPF usp)]).
      { apply stack_only_cons; [unfold SPF, STK_LO; lia| unfold SPF; lia| apply stack_only_nil]. }
      (first [ pose proof ((bundle_stack usp argv envp HCEIL _ _ _ tid SO_pristine 0 MU2 SO2 ltac:(unfold sp_window_lo; lia) U2 CC1 AR1 SH1)) as dR_18; dand4 dR_18 as CC2 AR2 SH2 GOT2 | destruct (bundle_stack usp argv envp HCEIL _ _ _ tid SO_pristine 0 MU2 SO2 ltac:(unfold sp_window_lo; lia) U2 CC1 AR1 SH1) as (CC2 & AR2 & SH2 & GOT2) ]).
      assert (FR2 : rw_cells rsegs (aview A m2) (SPF usp) [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 RA_MAIN)]).
      { eapply (rw_cells_transport rsegs); [exact FR1| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add]. cbn. unfold SPF. lia. }
      apply (KB m2 md2 tid j8 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6); try assumption.
      all: first [rewrite FS2; exact FS1 | rewrite FDS2; reflexivity].
  Qed.
End OpenPhase.
End DA_Ouhu.

Module DA_M0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image MState Frame SysStep RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img A_ImgAny.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Se7o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Eg3i DA_Cells DA_Ldix DA_Entry DA_Mib4 DA_Inv DA_Ejgo DA_Main DA_Am90 DA_FKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes.DA_Myrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ldix OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Entry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Mib4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ejgo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Main OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Am90 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_FKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Tails.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Section Walks.
  Variables (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32).
  #[local] Notation rom := (seg_rom rsegs).

  (* [comment removed for export] *)
  Definition m0A_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x8684c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 65536) a1 a2 a3 a4 a5 a6 a7
                    s2 s3 (Z_to_bv 64 3) (Z_to_bv 64 65536) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (cl_malloc_pc LPA) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

  Lemma m0A_walk : forall (ra : word) (m : word -> option byte),
    mem_inv rsegs m ->
    evt rsegs (m0A_post m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 3) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86838) fc None m rom).
  Proof.
    intros ra m MI.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    azstep. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    run_to 0x86848. at_pc 0x86848. bstep. apply evt_done. unfold m0A_post. cbn [cl_malloc_pc LPA].
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

  (* [comment removed for export] *)
  Definition m0B_post (ra : word) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m' (x10 : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 r) x10 a1 a2 a3 a4 a5 a6 a7
                    s2 (Z_to_bv 64 0) s4 (Z_to_bv 64 65536) (Z_to_bv 64 READ_STAGE) (Z_to_bv 64 r) s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x868c4) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

  Lemma m0B_walk : forall (ra : word) (r : Z) (m : word -> option byte),
    mem_inv rsegs m -> 0 < r < 2^64 -> s5 = Z_to_bv 64 65536 ->
    evt rsegs (m0B_post ra r m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x8684c) fc None m rom).
  Proof.
    intros ra r m MI R S5. subst s5.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    azstep. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    run_to 0x86860. at_pc 0x86860.
    azstep. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    bstep. bstep. apply evt_done. unfold m0B_post, READ_STAGE.
    eexists _, _. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.
End Walks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section M0.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  Variable usp : Z.
  Hypothesis HCEIL : alloc_ceiling = usp - 0x800000.   (* [comment removed for export] *)
  Variables argv envp : list (list byte).
  Variable fs : Fs.
  Variables (e0 e1 e2 e3 e4 e5 e6 e7 : word) (j8 : list byte).
  Hypothesis MALLOC1 : malloc1_stmt.   (* [comment removed for export] *)
  #[local] Notation rom := (seg_rom rsegs).
  #[local] Notation p1a := (e_p1a usp argv envp).
  #[local] Notation FV := (fview usp argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8).

  Ltac ulit := rewrite ?unsigned_lit by (unfold SPF, STK_LO in *; lia).

  #[using="MALLOC1 HCEIL"] Lemma m0_phase :
    forall (gp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word)
           (F : bvmap 5 word) (fc : bv 32) m md A (e : FdEntry) tid (TL : TSet),
      FV A m md (fds3 e) SO_pristine 0 tid ->
      (forall p, a_live A p = None) -> a_livebytes A = 0 -> a_nlive A = 0 -> 1 <= a_tinycred A -> a_seccred A = SECCRED0 -> a_primcred A = PRIMCRED0 (* [comment removed for export] *) ->
      (forall ff, a_frame A ff = None) ->
      (forall A' m' md' (b : Z) (zra z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 : word),
          FV A' m' md' (fds3 e) SO_pristine 0 tid ->
          b <> 0 -> a_live A' b = Some 65536 -> (forall q, q <> b -> a_live A' q = None) ->
          a_livebytes A' = 65536 -> a_nlive A' = 1 -> 1 <= a_tinycred A' -> SECCRED0 - 1 <= a_seccred A' -> a_primcred A' = PRIMCRED0 (* [comment removed for export] *) ->
          (forall ff, a_frame A' ff = None) ->
          srealizes rsegs
            (mkCfg (MS (mkR zra (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) z0 z1 z2 (Z_to_bv 64 2) (Z_to_bv 64 b) za0
                            za1 za2 za3 za4 za5 za6 za7 (Z_to_bv 64 p1a) (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 65536) (Z_to_bv 64 READ_STAGE)
                            (Z_to_bv 64 b) s8 s9 s10 s11 zt3 zt4 zt5 zt6)
                       F (Z_to_bv 64 0x868c4) fc None m' rom) md') TL) ->
      srealizes rsegs
        (mkCfg (MS (mkR (Z_to_bv 64 0x86838) (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) y0 y1 y2 (Z_to_bv 64 2) s1 (Z_to_bv 64 3)
                        ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 p1a) s3 s4 s5 s6 s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6)
                   F (Z_to_bv 64 0x86838) fc None m rom) md)
        TL.
  Proof.
    intros until TL. intros FV0 L0 LB0 NL0 TC0 SC0 PC0 FR0 KBUF.   (* [comment removed for export] *)
    (first [ pose proof ((fv_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0)) as dR_1; dand4 dR_1 as U1 U2 U3 U4 | pose proof (fv_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0) as (U1 & U2 & U3 & U4) ]). pose proof U1 as U1'. unfold sp_window_lo in U1'.
    pose proof (fv_ceil _ HCEIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0) as CEIL.
    pose proof FV0 as [AINV MI FS FDS CC AR SH ST FR].
    (* [comment removed for export] *)
    pose proof (munch_refl [] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) []) by exact I.
    ago AINV. fold_cl_segs.
    icall (m0A_walk (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) y0 y1 y2 (Z_to_bv 64 2) s1 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 p1a) s3 s4 s5 s6 s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6
             F fc (Z_to_bv 64 0x86838) (aview A m)) by (exact MI).
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    astopx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_2; dand3 dR_2 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    lazymatch goal with H : stk _ (aview A m1) _ _ |- _ => rename H into ST1 end.
    assert (FV1 : FV A m1 md1 (fds3 e) SO_pristine 0 tid).
    { eapply (fview_stack usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A m md); try eassumption.
      all: first [rewrite FS1; exact FS | rewrite FDS1; exact FDS | apply stack_only_nil | exact I]. }
    clear CC AR SH FR MU WM CF.
    pose proof FV1 as [_ _ _ _ CC1 AR1 SH1 _ FR1].
    (* [comment removed for export] *)
    pose proof MALLOC1 as MA. unfold malloc1_stmt in MA. cbv zeta in MA.
    eapply MA with (n := 65536) (T := TL); clear MA.
    all: lazymatch goal with
         | |- ainv _ _ _ => exact AINV1
         | |- mem_inv _ _ => exact MI1
         | |- @eq word _ _ => reflexivity
         | |- 1 <= 65536 < REQ_MAX => unfold REQ_MAX; lia
         | |- _ <= NREQ_CAP => rewrite NREQ_CAP_eq; lia
         | |- a_livebytes _ + _ <= LIVE_MAX => rewrite LB0, LIVE_MAX_eq; lia
         | |- a_nlive _ + 1 <= NLIVE_MAX => rewrite NL0, NLIVE_MAX_eq; lia
         | |- _ < 16 -> _ => lia
         | |- kMaxPrimaryUser < _ -> _ => rewrite SC0, SECCRED0_eq; lia
         | |- prim_cost _ <= a_primcred _ => rewrite prim_cost_secondary by (unfold kMaxPrimaryUser; lia); rewrite PC0, PRIMCRED0_eq; lia   (* [comment removed for export] *)
         | |- In _ (cl_sites LPA) => rewrite unsigned_lit by lia; cbn; tauto
         | |- mapped _ _ _ => ulit; eapply (stk_mapped (L:=LPA)); [exact ST1| exact CEIL| unfold ASTK, STK_LO, SPF; lia| lia]
         | |- forall t0', _ => idtac
         | |- _ => ulit; rewrite ?alloc_ceiling_val; unfold ASTK, STK_LO, SPF in *; first [lia | Z.div_mod_to_equations; lia]
         end.
    - (* [comment removed for export] *)
      intros z0 z1 z2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 r A' m' md' AINV' MI' MDF HLE FRS RNZ LVA LV' LVO LB TC NL SCR PCR FRK.   (* [comment removed for export] *)
      (first [ pose proof ((amd_frame_io md1 md' MDF)) as dR_5; dand3 dR_5 as FS' FDS' _ | pose proof (amd_frame_io md1 md' MDF) as (FS' & FDS' & _) ]).
      replace (ret_pc (Z_to_bv 64 0x8684c)) with (Z_to_bv 64 0x8684c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      (first [ pose proof ((as_live_ok LPA A' m' md' r 65536 AINV' LV')) as dR_6; dand5 dR_6 as _ RAL RLO RHI _ | destruct (as_live_ok LPA A' m' md' r 65536 AINV' LV') as (_ & RAL & RLO & RHI & _) ]).
      apply (cframe_of_frame_ok LPA) in FRK. rewrite ?unsigned_lit in FRK by (unfold SPF, STK_LO in *; lia).
      assert (FV' : FV A' m' md' (fds3 e) SO_pristine 0 tid).
      { eapply (fview_ccall usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A A' m1 md1 m' md'); try eassumption.
        all: first [rewrite FS'; rewrite FS1; exact FS | rewrite FDS'; rewrite FDS1; exact FDS | apply heapish_nowhere
                   | unfold ASTK, STK_LO, SPF; lia]. }
      pose proof FV' as [_ _ FSq FDSq CC' AR' SH' ST' FR'].
      pose proof (munch_refl [] (aview A' m')) as MU. pose proof (wmono_refl rsegs (aview A' m')) as WM.
      assert (CF : client_fpx (L:=LPA) A' (aview A' m') []) by exact I.
      ago AINV'. fold_cl_segs.
      icall (m0B_walk (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) z0 z1 z2 (Z_to_bv 64 2) s1 za1 za2 za3 za4 za5 za6 za7 (Z_to_bv 64 p1a) s3 (Z_to_bv 64 3) (Z_to_bv 64 65536) s6 s7 s8 s9 s10 s11 zt3 zt4 zt5 zt6
               F fc (Z_to_bv 64 0x8684c) r (aview A' m')) by (first [exact MI' | reflexivity | (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in RLO; cbn [cl_image_lo cl_image_hi LPA] in RLO; lia]).
      lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI2 end.
      astopx AINV' MU WM CF. rename m0 into m2. rename md0 into md2. rename AINV0 into AINV2.
      (first [ pose proof ((sbm_io md' md2 SBM0)) as dR_7; dand3 dR_7 as FS2 FDS2 _ | pose proof (sbm_io md' md2 SBM0) as (FS2 & FDS2 & _) ]).
      lazymatch goal with H : stk _ (aview A' m2) _ _ |- _ => rename H into ST2 end.
      assert (FV2 : FV A' m2 md2 (fds3 e) SO_pristine 0 tid).
      { eapply (fview_stack usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A' m' md'); try eassumption.
        all: first [rewrite FS2; exact FSq | rewrite FDS2; exact FDSq | apply stack_only_nil | exact I]. }
      apply (KBUF A' m2 md2 r); try assumption.
      + intros q Hq. rewrite (LVO q Hq). apply L0.
      + rewrite LB, LB0. reflexivity.
      + rewrite NL, NL0. reflexivity.
      + rewrite TC. change (Z.ltb 65536 16) with false. lia.
      + rewrite SCR, SC0. replace (if Z.ltb kMaxPrimaryUser 65536 then 1 else 0) with 1 by reflexivity. rewrite SECCRED0_eq. lia.
      + rewrite PCR, PC0. rewrite prim_cost_secondary by (unfold kMaxPrimaryUser; lia). lia.   (* [comment removed for export] *)
      + intros ff. rewrite FRS. apply FR0.
  Qed.
End M0.
End DA_M0.

Module DA_Dir.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image MState Frame SysStep RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img A_ImgAny.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Se7o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Eg3i DA_Cells DA_Stage DA_Ldix DA_Entry DA_Mib4 DA_Inv DA_Ejgo DA_Main DA_Am90 DA_FKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes.DA_Myrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Stage OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ldix OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Entry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Mib4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ejgo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Main OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Am90 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_FKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Tails OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Ouhu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_M0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Read.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Definition MSG_RDERR_FMT : Z := 0x1deab.

Section Walks.
  Variables (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32).
  #[local] Notation rom := (seg_rom rsegs).

  (* [comment removed for export] *)
  Definition rd_post (len cap : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x868e0) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 3) (Z_to_bv 64 READ_STAGE)
                    (Z_to_bv 64 (Z.min (cap - len) 65536)) a3 a4 a5 a6 a7
                    s2 (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 READ_STAGE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 READ_ICPT_ENTRY) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

  Lemma rd_walk : forall (ra : word) (len cap : Z) (m : word -> option byte),
    mem_inv rsegs m -> 0 <= len -> len < cap -> cap <= 2^40 ->
    evt rsegs (rd_post len cap m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 READ_STAGE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x868c4) fc None m rom).
  Proof.
    intros ra len cap m MI L0 LC CB. unfold READ_STAGE.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    azstep. azstep.
    azstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in K by lia.
      run_to 0x868dc. at_pc 0x868dc. bstep. apply evt_done. unfold rd_post, READ_ICPT_ENTRY, READ_STAGE. rewrite Z.min_l by lia.
      eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
    - rewrite ?unsigned_lit in K by lia.
      run_to 0x868dc. at_pc 0x868dc. bstep. apply evt_done. unfold rd_post, READ_ICPT_ENTRY, READ_STAGE. rewrite Z.min_r by lia.
      eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

  (* [comment removed for export] *)
  Definition rderr_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x86a5c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STDERR_F) (Z_to_bv 64 MSG_RDERR_FMT) s2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 FPRINTF_ICPT_ENTRY) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

  Lemma rderr_walk : forall (ra : word) (r : Z) (m : word -> option byte),
    mem_inv rsegs m -> -4096 <= r < 0 ->
    ro_cells rsegs m 0xa97d8 [C8 (Z_to_bv 64 0xa8a68)] ->
    ro_cells rsegs m STDERR_CELL [C8 (Z_to_bv 64 STDERR_F)] ->
    evt rsegs (rderr_post m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x868e0) fc None m rom).
  Proof.
    intros ra r m MI R GOT SC. unfold STDERR_CELL, STDERR_F in *.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    azstep. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. blia. } clear K.
    run_to 0x86a58. at_pc 0x86a58. bstep. apply evt_done. unfold rderr_post, FPRINTF_ICPT_ENTRY, MSG_RDERR_FMT, STDERR_F.
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.
End Walks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Dir.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  Variable usp : Z.
  Hypothesis HCEIL : alloc_ceiling = usp - 0x800000.   (* [comment removed for export] *)
  Variables argv envp : list (list byte).
  Variable fs : Fs.
  Hypothesis Hva : valid_argv argv.
  Hypothesis MALLOC1 : malloc1_stmt.   (* [comment removed for export] *)
  Hypothesis FPRINTF : fprintf_diag_stmt.
  Hypothesis EXIT : exit_spec_stmt.
  #[local] Notation rom := (seg_rom rsegs).
  #[local] Notation p1a := (e_p1a usp argv envp).

  Ltac ulit := rewrite ?unsigned_lit by (unfold SPF, STK_LO in *; lia).
  (* [comment removed for export] *)
  Ltac name_state m md AI :=
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mm _) ?mdd) _ =>
      lazymatch goal with H : ainv _ mm mdd |- _ => rename H into AI end; rename mm into m; rename mdd into md end.

  (* [comment removed for export] *)

  #[using="EXIT FPRINTF MALLOC1 Hva HCEIL"] Theorem dir_ok : dir_stmt usp argv envp fs.
  Proof.
    unfold dir_stmt. intros until md. intros A a0s DI EA AV.
    pose proof DI as DI'. destruct DI' as [AINV MI FS FDS FRN ST SPC SH [tid CC] GOT AR].
    pose proof AR as [P0 P1 S0 S1 K0 K1 B0 B1 (U1 & U2 & U3 & U4)]. pose proof U1 as U1'. unfold sp_window_lo in U1'.
    assert (A2 : e_argc argv = 2) by (rewrite AV; reflexivity).
    assert (P1E : nth 1 argv [] = dot_path) by (rewrite AV; reflexivity).
    assert (CEIL : alloc_ceiling <= STK_LO usp) by (unfold STK_LO; rewrite HCEIL; lia).
    (* [comment removed for export] *)
    rewrite <- P1E.
    apply (open_phase usp HCEIL argv envp fs Hva FPRINTF EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md A FdDir _ DI A2);
      [rewrite P1E; cbn; lia| left; split; [exact P1E| reflexivity]|].
    intros m2 md2 tid2 j8 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 AINV2 MI2 FS2 FDS2 CC2 AR2 SH2 ST2 FR2.
    assert (FV2 : fview usp argv envp fs s0 s1 s2 s3 s4 s5 s6 s7 j8 A m2 md2 (fds3 FdDir) SO_pristine 0 tid2) by (constructor; assumption).
    (* [comment removed for export] *)
    unfold t_opened_dir.
    apply (m0_phase usp HCEIL argv envp fs s0 s1 s2 s3 s4 s5 s6 s7 j8 MALLOC1
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 md2 A FdDir tid2 _ FV2
             (ea_live _ _ _ EA) (ea_bytes _ _ _ EA) (ea_nlive _ _ _ EA) ltac:(rewrite (ea_tiny _ _ _ EA), TINYCRED0_eq; lia) (ea_secc _ _ _ EA) (ea_primc _ _ _ EA) (ea_frames _ _ _ EA)).   (* [comment removed for export] *)
    intros A' m3 md3 b zra z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 FV3 BNZ LV LVO LB NL TC SCC PCC FRS.   (* [comment removed for export] *)
    clear dependent m2. clear dependent md2. clear AINV MI FS FDS ST SH CC GOT AR.
    pose proof FV3 as [AINV3 MI3 FS3 FDS3 CC3 AR3 SH3 ST3 FR3].
    (first [ pose proof ((as_live_ok LPA A' m3 md3 b 65536 AINV3 LV)) as dR_1; dand7 dR_1 as _ BAL BLO BHI _ BMP _ | destruct (as_live_ok LPA A' m3 md3 b 65536 AINV3 LV) as (_ & BAL & BLO & BHI & _ & BMP & _) ]).
    unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in BLO; cbn [cl_image_lo cl_image_hi LPA] in BLO. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    (* [comment removed for export] *)
    pose proof (munch_refl [] (aview A' m3)) as MU. pose proof (wmono_refl rsegs (aview A' m3)) as WM.
    assert (CF : client_fpx (L:=LPA) A' (aview A' m3) []) by exact I.
    ago AINV3. fold_cl_segs.
    icall (rd_walk (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) z0 z1 z2 (Z_to_bv 64 2) (Z_to_bv 64 b) za0 za1 za2 za3 za4 za5 za6 za7 (Z_to_bv 64 p1a)
             (Z_to_bv 64 b) s8 s9 s10 s11 zt3 zt4 zt5 zt6 F fc zra 0 65536 (aview A' m3)) by (first [exact MI3 | lia]).
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI4 end.
    astopx AINV3 MU WM CF. name_state m4 md4 AINV4.
    (first [ pose proof ((sbm_io md3 md4 SBM)) as dR_2; dand3 dR_2 as FS4 FDS4 _ | pose proof (sbm_io md3 md4 SBM) as (FS4 & FDS4 & _) ]).
    lazymatch goal with H : stk _ (aview A' m4) _ _ |- _ => rename H into ST4 end.
    assert (FV4 : fview usp argv envp fs s0 s1 s2 s3 s4 s5 s6 s7 j8 A' m4 md4 (fds3 FdDir) SO_pristine 0 tid2).
    { eapply (fview_stack usp HCEIL argv envp fs s0 s1 s2 s3 s4 s5 s6 s7 j8 A' m3 md3); try eassumption.
      all: first [rewrite FS4; exact FS3 | rewrite FDS4; exact FDS3 | apply stack_only_nil | exact I]. }
    clear CC3 AR3 SH3 FR3 MU WM CF.
    pose proof FV4 as [_ _ FS4q FDS4q CC4 AR4 SH4 _ FR4].
    (* [comment removed for export] *)
    destruct (stage_cells (aview A' m4) 65536 ltac:(lia)) as [junk RWB].
    (* [comment removed for export] *)
    pose proof (read_icpt_stage_dir_ok (AI:=AI)) as RD. unfold read_icpt_stage_dir_stmt in RD. cbv zeta in RD.
    change (Z.min (65536 - 0) 65536) with 65536.
    eapply RD with (cnt := 65536) (junk := junk) (lo := STK_LO usp); clear RD.
    all: lazymatch goal with
         | |- ainv _ _ _ => exact AINV4
         | |- mem_inv _ _ => exact MI4
         | |- read_icpt_cells _ => apply read_icpt_cells_of_consts; exact (consts_hold_ainv LPA A' m4 md4 AINV4)
         | |- @eq word _ _ => reflexivity
         | |- a_live _ _ = _ => exact LV
         | |- rw_cells _ _ _ [CB _ _] => exact RWB
         | |- m_fds _ = _ => exact FDS4q
         | |- stk _ _ _ _ => ulit; exact ST4
         | |- (exists e, rw_cells _ _ ERRNO_CELL _) => apply rw_errno_any
         | |- forall m', _ => idtac
         | |- _ => ulit; rewrite ?alloc_ceiling_val; unfold READ_ICPT_STACK, STK_LO, SPF in *; lia
         end.
    (intros m5 md5 AINV5; (first [ intro dR_8; dand3 dR_8 as FS5 FDS5 HH5 | intros (FS5 & FDS5 & HH5) ]); intros RWB5 ERR5 ms' POST).
    (first [ dex14 POST as w0 w1 w2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6; dand6 POST as -> MU5 WM5 MI5 ST5 _ | dand20 POST as w0 w1 w2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 -> MU5 WM5 MI5 ST5 _ | destruct POST as (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & wt3 & wt4 & wt5 & wt6 & -> & MU5 & WM5 & MI5 & ST5 & _) ]).
    rewrite ?unsigned_lit in MU5, ST5 by (unfold SPF, STK_LO in *; lia).
    replace (ret_pc (Z_to_bv 64 0x868e0)) with (Z_to_bv 64 0x868e0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (FV5 : fview usp argv envp fs s0 s1 s2 s3 s4 s5 s6 s7 j8 A' m5 md5 (fds3 FdDir) SO_pristine 0 tid2).
    { eapply (fview_stack usp HCEIL argv envp fs s0 s1 s2 s3 s4 s5 s6 s7 j8 A' m4 md4); try eassumption.
      all: first [rewrite FS5; exact FS4q | exact FDS5
                 | unfold READ_ICPT_STACK, ERRNO_CELL; apply stack_only_cons; [unfold SPF, STK_LO; lia| unfold SPF; lia| apply stack_only_cons_errno; apply stack_only_nil]
                 | unfold READ_ICPT_STACK, ERRNO_CELL, SPF; cbn; lia]. }
    clear CC4 AR4 SH4 FR4 RWB RWB5.
    pose proof FV5 as [_ _ FS5q FDS5q CC5 AR5 SH5 _ FR5].
    (* [comment removed for export] *)
    pose proof (munch_refl [] (aview A' m5)) as MU. pose proof (wmono_refl rsegs (aview A' m5)) as WM.
    assert (CF : client_fpx (L:=LPA) A' (aview A' m5) []) by exact I.
    pose proof (fv_gotc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV5) as GOTC. pose proof (fv_stderrp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV5) as SC.
    ago AINV5. fold_cl_segs.
    icall (rderr_walk (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) w0 w1 w2 (Z_to_bv 64 2) (Z_to_bv 64 b) wa1 wa2 wa3 wa4 wa5 wa6 wa7 (Z_to_bv 64 p1a)
             (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 65536) (Z_to_bv 64 READ_STAGE) (Z_to_bv 64 b) s8 s9 s10 s11 wt3 wt4 wt5 wt6 F fc (Z_to_bv 64 0x868e0) (-1) (aview A' m5))
      by (first [exact MI5 | exact GOTC | exact SC | lia]).
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI6 end.
    astopx AINV5 MU WM CF. name_state m6 md6 AINV6.
    (first [ pose proof ((sbm_io md5 md6 SBM0)) as dR_4; dand3 dR_4 as FS6 FDS6 _ | pose proof (sbm_io md5 md6 SBM0) as (FS6 & FDS6 & _) ]).
    lazymatch goal with H : stk _ (aview A' m6) _ _ |- _ => rename H into ST6 end.
    assert (FV6 : fview usp argv envp fs s0 s1 s2 s3 s4 s5 s6 s7 j8 A' m6 md6 (fds3 FdDir) SO_pristine 0 tid2).
    { eapply (fview_stack usp HCEIL argv envp fs s0 s1 s2 s3 s4 s5 s6 s7 j8 A' m5 md5); try eassumption.
      all: first [rewrite FS6; exact FS5q | rewrite FDS6; exact FDS5q | apply stack_only_nil | exact I]. }
    clear CC5 AR5 SH5 FR5 MU WM CF GOTC SC.
    pose proof FV6 as [_ _ FS6q FDS6q CC6 AR6 SH6 _ FR6].
    (first [ pose proof (CC6) as dR_5; dand4 dR_5 as MC6 [fe6 [FOK6 FE6]] SOUT6 TR6 | pose proof CC6 as (MC6 & [fe6 [FOK6 FE6]] & SOUT6 & TR6) ]).
    (first [ pose proof ((aa_s1k _ _ _ _ AR6 ltac:(lia))) as dR_6; dex1 dR_6 as sl1; destruct dR_6 as [SL1 SB1] | pose proof ((aa_s1k _ _ _ _ AR6 ltac:(lia))) as dR_6; dand3 dR_6 as sl1 SL1 SB1 | destruct (aa_s1k _ _ _ _ AR6 ltac:(lia)) as (sl1 & SL1 & SB1) ]).
    pose proof Hva as (AC & _ & ALEN & ANUL & APATH).
    (* [comment removed for export] *)
    unfold t_die.
    pose proof FPRINTF as FP. unfold fprintf_diag_stmt in FP. cbv zeta in FP.
    eapply FP with (d := DF_read_error) (arg := nth 1 argv []) (slack := sl1) (pa := p1a) (fe := fe6) (lo := STK_LO usp); clear FP.
    all: lazymatch goal with
         | |- ainv _ _ _ => exact AINV6
         | |- mem_inv _ _ => exact MI6
         | |- stk _ _ _ _ => ulit; exact ST6
         | |- file_at _ _ _ => exact FE6
         | |- stderr_ok _ => exact FOK6
         | |- fd_lookup _ _ = _ => rewrite FDS6q; vm_compute; reflexivity
         | |- bytes_at _ _ (sh _) _ => apply stksh_bytes; exact SH6
         | |- (exists j8, rw_cells _ _ STDERR_BUFP _) => apply errbuf_any
         | |- (exists g, ro_cells _ _ SSP_GUARD _) => exact (mc_canary _ _ MC6)
         | |- ro_cells _ _ SSP_GOT _ => exact (mc_sspgot _ _ MC6)
         | |- @eq word _ _ => reflexivity
         | |- _ /\ _ => cbn [diag_fmt_addr]; split; [reflexivity|]; split; [exact SB1|]; split; [rewrite P1E; cbn; intuition discriminate|];
                        pose proof (aa_b1 _ _ _ _ AR6 ltac:(lia)) as B1'; pose proof (aa_b0 _ _ _ _ AR6) as B0';
                        (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); ulit; rewrite SL1;
                        unfold e_p1a, e_p0a, e_L0, e_L1, e_argc, e_envc, e_span, SPF in *; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [lia | Z.div_mod_to_equations; lia]
         | |- (Z.of_nat (length _) <= _) => rewrite P1E; cbn; lia
         | |- t_exit _ _ [] => apply t_emit_has_nil
         | |- forall m', _ => idtac
         | |- _ => ulit; unfold FPRINTF_ICPT_STACK, STK_LO, SPF in *; first [lia | Z.div_mod_to_equations; lia]
         end.
    (* [comment removed for export] *)
    (intros m7 md7 fe7 rr AINV7; (first [ intro dR_9; dand3 dR_9 as FS7 FDS7 HH7 | intros (FS7 & FDS7 & HH7) ]); intros FOK7 FE7 ms' POST).
    (first [ dex14 POST as v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13; dand5 POST as -> MU7 WM7 MI7 ST7 | dand19 POST as v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 -> MU7 WM7 MI7 ST7 | destruct POST as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & -> & MU7 & WM7 & MI7 & ST7) ]).
    rewrite ?unsigned_lit in MU7, ST7 by (unfold SPF, STK_LO in *; lia).
    replace (ret_pc (Z_to_bv 64 0x86a5c)) with (Z_to_bv 64 0x86a5c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (CC7 : ccells (aview A' m7) tid2 SO_pristine 0).
    { eapply (ccells_after_fprintf (aview A' m6)); [exact CC6| | exact MU7| exact FOK7| exact FE7]. unfold FPRINTF_ICPT_STACK, SPF, STK_LO in *. lia. }
    rewrite <- FS6q, <- FS7.
    eapply diag_tail; try exact HCEIL; [exact EXIT| exact U1| lia| exact AINV7| exact MI7| exact CC7| exact ST7].
  Qed.
End Dir.
End DA_Dir.

Module DA_Loop.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image MState Frame SysStep RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg Shapi1s PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j AIcpnnp AIcpghc AIcp3q7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpwpz.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpwpz.AIcpdm8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img A_ImgAny.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Se7o DA_S5tv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Eg3i DA_Cells DA_Ldix DA_Entry DA_Mib4 DA_Inv DA_Ejgo DA_Main DA_Am90 DA_FKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Stage.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes.DA_Myrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ldix OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Entry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Mib4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ejgo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Main OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Am90 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_FKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Tails OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.DA_R1e4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Stage OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Dir.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

Definition MSG_REFUSED_FMT : Z := 0x19c98.
Definition MEMCPY_ICPT_ENTRY : Z := 0x574f8.

Section Walks.
  Variables (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32).
  #[local] Notation rom := (seg_rom rsegs).

  (* [comment removed for export] *)
  Definition more_post (len n b : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x86878) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 b) (Z_to_bv 64 (b + len)) s6 (Z_to_bv 64 n) a3 a4 a5 a6 a7
                    s2 (Z_to_bv 64 len) s4 s5 s6 (Z_to_bv 64 n) s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 MEMCPY_ICPT_ENTRY) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

  Lemma more_walk : forall (len n b : Z) (m : word -> option byte),
    mem_inv rsegs m -> 0 <= len -> 0 < n < 2^40 -> 0 <= b -> b + len < 2^64 ->
    evt rsegs (more_post len n b m)
        (MS (mkR (Z_to_bv 64 0x868e0) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 b) (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 len) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x868e0) fc None m rom).
  Proof.
    intros len n b m MI L0 N0 B0 B1.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    azstep. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. blia. } clear K.
    azstep. azstep. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    run_to 0x86874. at_pc 0x86874. bstep. apply evt_done. unfold more_post, MEMCPY_ICPT_ENTRY.
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

  (* [comment removed for export] *)
  Definition done_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x868e0) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 (Z_to_bv 64 0) s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x868ec) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

  Lemma done_walk : forall (m : word -> option byte),
    mem_inv rsegs m ->
    evt rsegs (done_post m)
        (MS (mkR (Z_to_bv 64 0x868e0) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x868e0) fc None m rom).
  Proof.
    intros m MI.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    azstep. if_cases K; zify_cond K. { exfalso. clear -K. lia. } clear K.
    azstep. azstep. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
    apply evt_done. unfold done_post.
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

  (* [comment removed for export] *)
  Definition cont_post (ra : word) (len n b cap : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 b) a0 a1 a2 a3 a4 a5 a6 a7
                    s2 (Z_to_bv 64 (len + n)) s4 (Z_to_bv 64 cap) s6 (Z_to_bv 64 b) s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x868c4) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.
  Lemma cont_walk : forall (ra : word) (len n b cap : Z) (m : word -> option byte),
    mem_inv rsegs m -> 0 <= len -> 0 <= n -> len + n < cap -> cap <= 2^40 ->
    evt rsegs (cont_post ra len n b cap m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 b) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 len) s4 (Z_to_bv 64 cap) s6 (Z_to_bv 64 n) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86878) fc None m rom).
  Proof.
    intros ra len n b cap m MI L0 N0 LT CB.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    azstep. azstep. azstep. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    azstep. azstep. apply evt_done. unfold cont_post. rewrite (Z.add_comm n len).
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

  (* [comment removed for export] *)
  Definition growM_post (cap b : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x868a0) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 b) (Z_to_bv 64 (2 * cap)) a1 a2 a3 a4 a5 a6 a7
                    s2 (Z_to_bv 64 cap) s4 (Z_to_bv 64 (2 * cap)) s6 (Z_to_bv 64 b) s8 s9 s10 s11 t3 t4 t5 t6)
               F (cl_malloc_pc LPA) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

  Lemma growM_walk : forall (ra : word) (len n b cap : Z) (m : word -> option byte),
    mem_inv rsegs m -> 0 <= len -> 0 <= n -> len + n = cap -> cap < 2^26 ->
    evt rsegs (growM_post cap b m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 b) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 len) s4 (Z_to_bv 64 cap) s6 (Z_to_bv 64 n) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86878) fc None m rom).
  Proof.
    intros ra len n b cap m MI L0 N0 E CB.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    azstep. azstep. azstep. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    rewrite (Z.add_comm n len), E.
    azstep. azstep. if_cases K; zify_cond K.
    { exfalso. revert K. rewrite ?unsigned_lit by lia. rewrite Z.shiftr_div_pow2, Z.div_small by lia. lia. }
    clear K.
    run_to 0x8689c. at_pc 0x8689c. bstep. apply evt_done. unfold growM_post. cbn [cl_malloc_pc LPA].
    rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite (Z.mul_comm cap 2).
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

  (* [comment removed for export] *)
  Definition refused_post (b : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x86a5c) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 b) (Z_to_bv 64 STDERR_F) (Z_to_bv 64 MSG_REFUSED_FMT) (Z_to_bv 64 67108864) a3 a4 a5 a6 a7
                    s2 (Z_to_bv 64 67108864) s4 (Z_to_bv 64 67108864) s6 (Z_to_bv 64 b) s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 FPRINTF_ICPT_ENTRY) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

  Lemma refused_walk : forall (ra : word) (len n b : Z) (m : word -> option byte),
    mem_inv rsegs m ->
    ro_cells rsegs m 0xa97d8 [C8 (Z_to_bv 64 0xa8a68)] ->
    ro_cells rsegs m STDERR_CELL [C8 (Z_to_bv 64 STDERR_F)] ->
    0 <= len -> 0 <= n -> len + n = 67108864 ->
    evt rsegs (refused_post b m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 b) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 len) s4 (Z_to_bv 64 67108864) s6 (Z_to_bv 64 n) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86878) fc None m rom).
  Proof.
    intros ra len n b m MI GOT SC L0 N0 E. unfold STDERR_CELL, STDERR_F in *.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    azstep. azstep. azstep. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    rewrite (Z.add_comm n len), E.
    azstep. azstep. if_cases K; zify_cond K. 2:{ exfalso. revert K. vm_compute. discriminate. } clear K.
    run_to 0x86a58. at_pc 0x86a58. bstep. apply evt_done. unfold refused_post, FPRINTF_ICPT_ENTRY, MSG_REFUSED_FMT, STDERR_F.
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

  (* [comment removed for export] *)
  Definition growC_post (len r : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x868bc) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 r) (Z_to_bv 64 r) s7 (Z_to_bv 64 len) a3 a4 a5 a6 a7
                    s2 (Z_to_bv 64 len) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 MEMCPY_ICPT_ENTRY) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

  Lemma growC_walk : forall (ra : word) (len r : Z) (m : word -> option byte),
    mem_inv rsegs m -> 0 < len < 2^40 -> 0 < r < 2^64 ->
    evt rsegs (growC_post len r m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 len) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x868a0) fc None m rom).
  Proof.
    intros ra len r m MI L R.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    azstep. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    azstep. azstep. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    run_to 0x868b8. at_pc 0x868b8. bstep. apply evt_done. unfold growC_post, MEMCPY_ICPT_ENTRY.
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

  (* [comment removed for export] *)
  Definition growF_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x868c4) sp gp tp t0 t1 t2 s0 s1 s7 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (cl_free_pc LPA) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

  Lemma growF_walk : forall (ra x10 : word) (m : word -> option byte),
    mem_inv rsegs m ->
    evt rsegs (growF_post m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x868bc) fc None m rom).
  Proof.
    intros ra x10 m MI.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    bstep. bstep. apply evt_done. unfold growF_post. cbn [cl_free_pc LPA].
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.
End Walks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lshape_unfold : forall data fs f k len,
  lshape data fs (S f) k len =
    (if (len =? cap k)%Z then
       if (10 <=? Z.of_nat k)%Z then t_die msg_refused fs
       else lshape data fs f (S k) len
     else
       if (Z.min (Z.min (cap k - len) 65536) (Z.of_nat (length data) - len) =? 0)%Z then t_body data fs
       else lshape data fs f k (len + Z.min (Z.min (cap k - len) 65536) (Z.of_nat (length data) - len))).
Proof. reflexivity. Qed.

Section Loop.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.
  Variable usp : Z.
  Hypothesis HCEIL : alloc_ceiling = usp - 0x800000.   (* [comment removed for export] *)
  Variables argv envp : list (list byte).
  Variable fs : Fs.
  Variables (e0 e1 e2 e3 e4 e5 e6 e7 : word) (j8 : list byte).
  Variables (path data : list byte).
  (* [comment removed for export] *)
  Variables (gp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Hypothesis MALLOC1 : malloc1_stmt.   (* [comment removed for export] *)
  Hypothesis FREE1 : free1_stmt.
  Hypothesis FPRINTF : fprintf_diag_stmt.
  Hypothesis EXIT : exit_spec_stmt.
  Hypothesis DATA : fs_lookup fs path = Some data.
  #[local] Notation rom := (seg_rom rsegs).
  #[local] Notation p1a := (e_p1a usp argv envp).
  #[local] Notation L := (Z.of_nat (length data)).
  #[local] Notation FV := (fview usp argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8).

  Ltac ulit := rewrite ?unsigned_lit by (unfold SPF, STK_LO in *; lia).
  (* [comment removed for export] *)
  Ltac split_assum := first [assumption | split; [assumption | split_assum]].
  (* [comment removed for export] *)
  Local Ltac icall_consts_in H ::= change (bv_unsigned (Z_to_bv 64 READ_STAGE)) with READ_STAGE in H; unfold MEMCPY_ICPT_STACK in H.   (* [comment removed for export] *)
  Ltac name_state m md AI :=
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mm _) ?mdd) _ =>
      lazymatch goal with H : ainv _ mm mdd |- _ => rename H into AI end; rename mm into m; rename mdd into md end.

  (* [comment removed for export] *)
  Record lst (A : AS) (m : word -> option byte) (md : Model) (tid : Z) (k : nat) (len b : Z) : Prop := {
    ls_fv     : FV A m md (fds3 (FdFile path (Z_to_bv 64 len))) SO_pristine 0 tid;
    ls_bnz    : b <> 0;
    ls_live   : a_live A b = Some (cap k);
    ls_only   : forall q, q <> b -> a_live A q = None;
    ls_bytes  : a_livebytes A = cap k;
    ls_nlive  : a_nlive A = 1;
    ls_tiny   : 1 <= a_tinycred A;
    ls_secc   : SECCRED0 - 1 - Z.of_nat k <= a_seccred A;     (* [comment removed for export] *)
    ls_primc  : a_primcred A = PRIMCRED0;                    (* [comment removed for export] *)
    ls_frames : forall ff, a_frame A ff = None;
    ls_data   : rw_cells rsegs (aview A m) b [CB (Z.to_nat len) (firstn (Z.to_nat len) data)];
    ls_len    : 0 <= len <= cap k /\ len <= L;
    ls_k      : (k <= 10)%nat;
    ls_grown  : k = 0%nat \/ cap k <= 2 * L    (* [comment removed for export] *)
  }.

  (* [comment removed for export] *)
  Definition body_stmt : Prop :=
    forall A m md tid k b (z0 z1 z2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 : word),
      lst A m md tid k L b -> L < cap k ->
      srealizes rsegs
        (mkCfg (MS (mkR (Z_to_bv 64 0x868e0) (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) z0 z1 z2 (Z_to_bv 64 2) (Z_to_bv 64 b) (Z_to_bv 64 0)
                        za1 za2 za3 za4 za5 za6 za7 (Z_to_bv 64 p1a) (Z_to_bv 64 L) (Z_to_bv 64 3) (Z_to_bv 64 (cap k)) (Z_to_bv 64 READ_STAGE)
                        (Z_to_bv 64 0) s8 s9 s10 s11 zt3 zt4 zt5 zt6)
                   F (Z_to_bv 64 0x868ec) fc None m rom) md)
        (t_body data fs).
  Hypothesis BODY : body_stmt.

  (* [comment removed for export] *)
  Definition P_lr (f : nat) : Prop :=
    forall A m md tid k len b (zra z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 x7 : word),
      lst A m md tid k len b -> len < cap k -> L - len + 11 - Z.of_nat k < Z.of_nat f ->
      srealizes rsegs
        (mkCfg (MS (mkR zra (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) z0 z1 z2 (Z_to_bv 64 2) (Z_to_bv 64 b) za0
                        za1 za2 za3 za4 za5 za6 za7 (Z_to_bv 64 p1a) (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 (cap k)) (Z_to_bv 64 READ_STAGE)
                        x7 s8 s9 s10 s11 zt3 zt4 zt5 zt6)
                   F (Z_to_bv 64 0x868c4) fc None m rom) md)
        (lshape data fs f k len).

  (* [comment removed for export] *)
  Definition P_grow (f : nat) : Prop :=
    forall A m md tid k len n b (z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 : word),
      lst A m md tid k (len + n) b -> 0 <= len -> 0 <= n -> len + n = cap k -> L - (len + n) + 11 - Z.of_nat k < Z.of_nat f ->
      srealizes rsegs
        (mkCfg (MS (mkR (Z_to_bv 64 0x86878) (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) z0 z1 z2 (Z_to_bv 64 2) (Z_to_bv 64 b) za0
                        za1 za2 za3 za4 za5 za6 za7 (Z_to_bv 64 p1a) (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 (cap k)) (Z_to_bv 64 READ_STAGE)
                        (Z_to_bv 64 n) s8 s9 s10 s11 zt3 zt4 zt5 zt6)
                   F (Z_to_bv 64 0x86878) fc None m rom) md)
        (lshape data fs f k (len + n)).
  #[using="BODY DATA HCEIL"] Lemma read_step : forall f, P_lr f -> P_grow f -> P_lr (S f).
  Proof.
    intros f IH IHG. unfold P_lr. intros A m md tid k len b zra z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 x7 LS LT FUEL.
    pose proof LS as [FV0 BNZ LV LVO LB NL TC SCC PCC FRS DAT (LEN & LENL) K10 GRW].   (* [comment removed for export] *)
    (first [ pose proof ((fv_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0)) as dR_1; dand4 dR_1 as U1 U2 U3 U4 | pose proof (fv_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0) as (U1 & U2 & U3 & U4) ]). pose proof U1 as U1'. unfold sp_window_lo in U1'.
    pose proof (fv_ceil _ HCEIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0) as CEIL.
    pose proof FV0 as [AINV MI FS FDS CC AR SH ST FR].
    pose proof (cap_range k K10) as CR.
    (first [ pose proof ((as_live_ok LPA A m md b (cap k) AINV LV)) as dR_2; dand7 dR_2 as _ BAL BAPP BHI _ BMP _ | destruct (as_live_ok LPA A m md b (cap k) AINV LV) as (_ & BAL & BAPP & BHI & _ & BMP & _) ]).
    (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    (* [comment removed for export] *)
    assert (BLO : 0x60a000 <= b).
    { clear - BAPP CR. unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in BAPP; cbn [cl_image_lo cl_image_hi LPA] in BAPP. lia. }
    set (cnt := Z.min (cap k - len) 65536) in *.
    assert (CNT : 1 <= cnt <= 65536 /\ len + cnt <= cap k) by (subst cnt; lia).
    rewrite lshape_unfold. replace (len =? cap k) with false by (symmetry; apply Z.eqb_neq; lia).
    fold cnt.
    (* [comment removed for export] *)
    pose proof (munch_refl [] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) []) by exact I.
    ago AINV. fold_cl_segs.
    icall (rd_walk (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) z0 z1 z2 (Z_to_bv 64 2) (Z_to_bv 64 b) za0 za1 za2 za3 za4 za5 za6 za7 (Z_to_bv 64 p1a)
             x7 s8 s9 s10 s11 zt3 zt4 zt5 zt6 F fc zra len (cap k) (aview A m)) by (first [exact MI | lia]).
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    astopx AINV MU WM CF. name_state m1 md1 AINV1.
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_3; dand3 dR_3 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    lazymatch goal with H : stk _ (aview A m1) _ _ |- _ => rename H into ST1 end.
    assert (FV1 : FV A m1 md1 (fds3 (FdFile path (Z_to_bv 64 len))) SO_pristine 0 tid).
    { eapply (fview_stack usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A m md); try eassumption.
      all: first [rewrite FS1; exact FS | rewrite FDS1; exact FDS | apply stack_only_nil | exact I]. }
    clear CC AR SH FR MU WM CF.
    pose proof FV1 as [_ _ FS1q FDS1q CC1 AR1 SH1 _ FR1].
    fold cnt.
    (* [comment removed for export] *)
    destruct (stage_cells (aview A m1) cnt ltac:(lia)) as [junk RWB].
    (* [comment removed for export] *)
    pose proof (read_icpt_stage_file_ok (AI:=AI)) as RD. unfold read_icpt_stage_file_stmt in RD. cbv zeta in RD.
    eapply RD with (cnt := cnt) (path := path) (off := len) (data := data) (junk := junk) (lo := STK_LO usp); clear RD.
    all: lazymatch goal with
         | |- ainv _ _ _ => exact AINV1
         | |- mem_inv _ _ => exact MI1
         | |- read_icpt_cells _ => apply read_icpt_cells_of_consts; exact (consts_hold_ainv LPA A m1 md1 AINV1)
         | |- @eq word _ _ => reflexivity
         | |- rw_cells _ _ _ [CB _ _] => exact RWB
         | |- m_fds _ = _ => exact FDS1q
         | |- fs_lookup _ _ = _ => rewrite FS1q; exact DATA
         | |- stk _ _ _ _ => ulit; exact ST1
         | |- (exists e, rw_cells _ _ ERRNO_CELL _) => apply rw_errno_any
         | |- forall m', _ => idtac
         | |- _ => ulit; rewrite ?alloc_ceiling_val; unfold READ_ICPT_STACK, STK_LO, SPF in *; lia
         end.
    (intros m5 md5 AINV5; (first [ intro dR_25; dand3 dR_25 as FS5 FDS5 HH5 | intros (FS5 & FDS5 & HH5) ]); intros RWB5 ms' POST).
    (first [ dex14 POST as w0 w1 w2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6; dand6 POST as -> MU5 WM5 MI5 ST5 _ | dand20 POST as w0 w1 w2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 -> MU5 WM5 MI5 ST5 _ | destruct POST as (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & wt3 & wt4 & wt5 & wt6 & -> & MU5 & WM5 & MI5 & ST5 & _) ]).
    rewrite ?unsigned_lit in MU5, ST5 by (unfold SPF, STK_LO in *; lia).
    replace (ret_pc (Z_to_bv 64 0x868e0)) with (Z_to_bv 64 0x868e0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    set (bs := firstn (Z.to_nat cnt) (skipn (Z.to_nat len) data)) in *.
    set (n := Z.of_nat (length bs)) in *.
    assert (NE : n = Z.min cnt (L - len)).
    { subst n bs. rewrite length_firstn, length_skipn. lia. }
    assert (FV5 : FV A m5 md5 (fds3 (FdFile path (Z_to_bv 64 (len + n)))) SO_pristine 0 tid).
    { eapply (fview_stack usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A m1 md1); try eassumption.
      all: first [rewrite FS5; exact FS1q | exact FDS5
                 | unfold READ_ICPT_STACK, READ_STAGE; apply stack_only_cons; [unfold SPF, STK_LO; lia| unfold SPF; lia|];
                   apply stack_only_cons_stage; [lia| apply stack_only_nil]
                 | unfold READ_ICPT_STACK, READ_STAGE, SPF; cbn; lia]. }
    (* [comment removed for export] *)
    assert (DAT5 : rw_cells rsegs (aview A m5) b [CB (Z.to_nat len) (firstn (Z.to_nat len) data)]).
    { eapply (rw_cells_transport rsegs); [exact DAT| exact MU5| exact WM5|]. unfold READ_ICPT_STACK, READ_STAGE, SPF. cbn. lia. }
    rewrite <- NE.
    destruct (Z.eq_dec n 0) as [N0|N0].
    - (* [comment removed for export] *)
      assert (LL : len = L) by lia.
      rewrite N0, Z.add_0_r in *. cbn [Z.eqb].
      pose proof FV5 as [_ _ FS5q FDS5q CC5 AR5 SH5 _ FR5].
      pose proof (munch_refl [] (aview A m5)) as MU. pose proof (wmono_refl rsegs (aview A m5)) as WM.
      assert (CF : client_fpx (L:=LPA) A (aview A m5) []) by exact I.
      ago AINV5. fold_cl_segs.
      icall done_walk by (exact MI5).
      lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI6 end.
      astopx AINV5 MU WM CF. name_state m6 md6 AINV6.
      (first [ pose proof ((sbm_io md5 md6 SBM0)) as dR_5; dand3 dR_5 as FS6 FDS6 _ | pose proof (sbm_io md5 md6 SBM0) as (FS6 & FDS6 & _) ]).
      lazymatch goal with H : stk _ (aview A m6) _ _ |- _ => rename H into ST6 end.
      assert (FV6 : FV A m6 md6 (fds3 (FdFile path (Z_to_bv 64 len))) SO_pristine 0 tid).
      { eapply (fview_stack usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A m5 md5); try eassumption.
        all: first [rewrite FS6; exact FS5q | rewrite FDS6; exact FDS5q | apply stack_only_nil | exact I]. }
      rewrite LL in *.
      apply (BODY A m6 md6 tid k b); [| exact LT].
      constructor; try assumption. split; lia.
    - (* [comment removed for export] *)
      replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; exact N0).
      assert (NP : 0 < n /\ len + n <= cap k /\ len + n <= L) by lia.
      pose proof FV5 as [_ _ FS5q FDS5q CC5 AR5 SH5 _ FR5].
      (* [comment removed for export] *)
      destruct (rwCB2_split _ _ _ _ _ _ RWB5) as [RWS _].
      (first [ pose proof ((rwCB_elim _ _ _ _ RWS)) as dR_6; dand3 dR_6 as _ SB _ | destruct (rwCB_elim _ _ _ _ RWS) as (_ & SB & _) ]). clear RWS.
      clear MU5 WM5 RWB5 MI1 ST1 FR1 CC1 AR1 SH1.   (* [comment removed for export] *)
      pose proof (conj DAT5 BNZ) as DAT5h. clear DAT5.   (* [comment removed for export] *)
      (* [comment removed for export] *)
      (first [ pose proof ((as_live_ok LPA A m5 md5 b (cap k) AINV5 LV)) as dR_7; dand7 dR_7 as _ _ _ _ _ BMP5 _ | destruct (as_live_ok LPA A m5 md5 b (cap k) AINV5 LV) as (_ & _ & _ & _ & _ & BMP5 & _) ]).
      assert (JMP : mapped (aview A m5) (b + len) n).
      { intros i Hi. replace (b + len + i) with (b + (len + i)) by lia. apply BMP5. lia. }
      destruct (mapped_rw_cells (aview A m5) (b + len) n JMP ltac:(lia) ltac:(lia) ltac:(lia)) as [junk2 RWJ].
      (* [comment removed for export] *)
      pose proof (munch_refl [(b + len, b + len + n); (SPF usp - MEMCPY_ICPT_STACK, SPF usp)] (aview A m5)) as MU.
      pose proof (wmono_refl rsegs (aview A m5)) as WM.
      assert (CF : client_fpx (L:=LPA) A (aview A m5) [(b + len, b + len + n); (SPF usp - MEMCPY_ICPT_STACK, SPF usp)]).
      { cbn. split; [| split; [| exact I]].
        - left. split; [| exact I]. right. left. exists b, (cap k). split; [exact LV| lia].
        - left. split; [| exact I]. left. split; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold MEMCPY_ICPT_STACK, STK_LO, SPF in *; lia|]. split; [unfold SPF; lia|].
          replace (SPF usp - (SPF usp - MEMCPY_ICPT_STACK)) with MEMCPY_ICPT_STACK by lia.
          eapply (stk_mapped (L:=LPA)); [exact ST5 | exact CEIL | unfold MEMCPY_ICPT_STACK, STK_LO, SPF in *; lia | lia]. }
      unfold MEMCPY_ICPT_STACK in MU, CF.   (* [comment removed for export] *)
      (first [ pose proof ((asan_memcpy_cells_of_consts _ (consts_hold_ainv LPA A m5 md5 AINV5))) as dR_8; dand11 dR_8 as MCC1 MCC2 MCC3 MP1 MP2 MP3 MP4 MP5 MP6 MP7 MP8 | pose proof (asan_memcpy_cells_of_consts _ (consts_hold_ainv LPA A m5 md5 AINV5)) as (MCC1 & MCC2 & MCC3 & MP1 & MP2 & MP3 & MP4 & MP5 & MP6 & MP7 & MP8) ]).
      assert (RS5 : range_ok (aview A m5) READ_STAGE n).
      { apply stage_range_ok; [exact (consts_hold_ainv LPA A m5 md5 AINV5)| lia| unfold READ_STAGE; lia| unfold READ_STAGE; lia]. }
      assert (RD5 : range_ok (aview A m5) (b + len) n).
      { eapply (live_range_ok A m5 md5 b (cap k)); [exact AINV5| exact LV| lia| lia| lia]. }
      assert (SPFV : SPF usp = usp - 128) by reflexivity.
      ago AINV5. fold_cl_segs.
      icall more_walk by (first [assumption | lia]).
      lazymatch goal with H : mem_inv _ _ |- _ => rename H into MIa end.
      assert (SLEN' : length bs = Z.to_nat n) by (unfold n; rewrite Nat2Z.id; reflexivity).
      try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_SB); icall (memcpy_icpt_ok (Z_to_bv 64 0x86878) (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) w0 w1 w2 (Z_to_bv 64 2) (Z_to_bv 64 b)
               (Z_to_bv 64 (b + len)) (Z_to_bv 64 READ_STAGE) (Z_to_bv 64 n) wa3 wa4 wa5 wa6 wa7 (Z_to_bv 64 p1a) (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 (cap k)) (Z_to_bv 64 READ_STAGE)
               (Z_to_bv 64 n) s8 s9 s10 s11 wt3 wt4 wt5 wt6 F fc _ bs junk2 (STK_LO usp))
        by (rewrite ?unsigned_lit by (unfold READ_STAGE; lia);
            first [ exact SB | exact SLEN' | exact RWJ | exact MIa
                  | lazymatch goal with |- asan_memcpy_cells _ => split_assum end
                  | ulit; assumption
                  | ulit; unfold READ_STAGE, MEMCPY_ICPT_STACK, STK_LO, SPF in *; lia
                  | right; split; (eapply (range_ok_high_munch _ (aview A m5)); [eassumption| eassumption| unfold READ_STAGE; lia| lia| unfold READ_STAGE; lia|
                      apply Forall_cons; [cbn [fst snd]; clear - BAPP LEN NP CR; unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in BAPP; cbn [cl_image_lo cl_image_hi LPA] in BAPP; unfold SHMAX; lia
                                         | apply Forall_cons; [cbn [fst snd]; clear - ACV U1' SPFV; unfold SHMAX, MEMCPY_ICPT_STACK, SPF, STK_LO in *; lia| apply Forall_nil]]]) ]).
      lazymatch goal with H : mem_inv _ _ |- _ => rename H into MIb end.
      lazymatch goal with H : rw_cells _ _ (b + len) [CB _ bs] |- _ => rename H into RNEW end.
      lazymatch goal with H : stk _ _ (STK_LO usp) (SPF usp) |- _ => rename H into STc end.
      lazymatch goal with H : bytes_at _ _ READ_STAGE bs |- _ => clear H end.
      destruct (Z_lt_le_dec (len + n) (cap k)) as [LT2|GE2].
      + (* [comment removed for export] *)
        icall cont_walk by (first [assumption | lia]).
        lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI6 end.
        astopx AINV5 MU WM CF. name_state m6 md6 AINV6.
        (first [ pose proof ((sbm_io md5 md6 SBM0)) as dR_9; dand3 dR_9 as FS6 FDS6 _ | pose proof (sbm_io md5 md6 SBM0) as (FS6 & FDS6 & _) ]).
        lazymatch goal with H : stk _ (aview A m6) _ _ |- _ => rename H into ST6 end.
        assert (FV6 : FV A m6 md6 (fds3 (FdFile path (Z_to_bv 64 (len + n)))) SO_pristine 0 tid).
        { eapply (fview_stack usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A m5 md5); try eassumption.
          all: first [rewrite FS6; exact FS5q | rewrite FDS6; exact FDS5q
                     | apply (stack_only_cons_heap usp HCEIL); [eapply app_range_sub; [exact BAPP| lia| lia| lia]|];
                       unfold MEMCPY_ICPT_STACK; apply stack_only_cons; [unfold SPF, STK_LO; lia| unfold SPF; lia| apply stack_only_nil]
                     | unfold MEMCPY_ICPT_STACK, SPF; cbn; lia]. }
        destruct DAT5h as [DAT5 _].
        assert (DAT6 : rw_cells rsegs (aview A m6) b [CB (Z.to_nat (len + n)) (firstn (Z.to_nat (len + n)) data)]).
        { assert (DAT' : rw_cells rsegs (aview A m6) b [CB (Z.to_nat len) (firstn (Z.to_nat len) data)]).
          { eapply (rw_cells_transport rsegs); [exact DAT5| exact MU| exact WM|]. unfold MEMCPY_ICPT_STACK, SPF, STK_LO in *. cbn. lia. }
          pose proof (rwCB_app _ _ _ _ _ _ DAT' ltac:(rewrite Z2Nat.id by lia; exact RNEW)) as X.
          unfold bs in X. rewrite firstn_extend in X. fold bs in X. fold n in X.
          replace (Z.to_nat len + length bs)%nat with (Z.to_nat (len + n)) in X by (subst n; lia).
          replace (Z.to_nat len + Z.to_nat n)%nat with (Z.to_nat (len + n)) in X by (subst n; lia). exact X. }
        apply (IH A m6 md6 tid k (len + n) b); [| exact LT2| lia].
        constructor; try assumption. split; lia.
      + (* [comment removed for export] *)
        assert (E : len + n = cap k) by lia.
        astopx AINV5 MU WM CF. name_state m6 md6 AINV6.
        (first [ pose proof ((sbm_io md5 md6 SBM0)) as dR_10; dand3 dR_10 as FS6 FDS6 _ | pose proof (sbm_io md5 md6 SBM0) as (FS6 & FDS6 & _) ]).
        lazymatch goal with H : stk _ (aview A m6) _ _ |- _ => rename H into ST6 end.
        assert (FV6 : FV A m6 md6 (fds3 (FdFile path (Z_to_bv 64 (len + n)))) SO_pristine 0 tid).
        { eapply (fview_stack usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A m5 md5); try eassumption.
          all: first [rewrite FS6; exact FS5q | rewrite FDS6; exact FDS5q
                     | apply (stack_only_cons_heap usp HCEIL); [eapply app_range_sub; [exact BAPP| lia| lia| lia]|];
                       unfold MEMCPY_ICPT_STACK; apply stack_only_cons; [unfold SPF, STK_LO; lia| unfold SPF; lia| apply stack_only_nil]
                     | unfold MEMCPY_ICPT_STACK, SPF; cbn; lia]. }
        destruct DAT5h as [DAT5 _].
        assert (DAT6 : rw_cells rsegs (aview A m6) b [CB (Z.to_nat (len + n)) (firstn (Z.to_nat (len + n)) data)]).
        { assert (DAT' : rw_cells rsegs (aview A m6) b [CB (Z.to_nat len) (firstn (Z.to_nat len) data)]).
          { eapply (rw_cells_transport rsegs); [exact DAT5| exact MU| exact WM|]. unfold MEMCPY_ICPT_STACK, SPF, STK_LO in *. cbn. lia. }
          pose proof (rwCB_app _ _ _ _ _ _ DAT' ltac:(rewrite Z2Nat.id by lia; exact RNEW)) as X.
          unfold bs in X. rewrite firstn_extend in X. fold bs in X. fold n in X.
          replace (Z.to_nat len + length bs)%nat with (Z.to_nat (len + n)) in X by (subst n; lia).
          replace (Z.to_nat len + Z.to_nat n)%nat with (Z.to_nat (len + n)) in X by (subst n; lia). exact X. }
        apply (IHG A m6 md6 tid k len n b); [| lia| lia| exact E| lia].
        constructor; try assumption. split; lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="EXIT FPRINTF FREE1 MALLOC1 HCEIL"] Lemma grow_step : forall f, P_lr f -> P_grow (S f).
  Proof.
    intros f IH. unfold P_grow. intros A m md tid k len0 n b z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 LS L0 N0 E FUEL.
    pose proof LS as [FV0 BNZ LV LVO LB NL TC SCC PCC FRS DAT (LEN & LENL) K10 GRW].   (* [comment removed for export] *)
    (first [ pose proof ((fv_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0)) as dR_11; dand4 dR_11 as U1 U2 U3 U4 | pose proof (fv_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0) as (U1 & U2 & U3 & U4) ]). pose proof U1 as U1'. unfold sp_window_lo in U1'.
    pose proof (fv_ceil _ HCEIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0) as CEIL.
    pose proof FV0 as [AINV MI FS FDS CC AR SH ST FR].
    pose proof (cap_range k K10) as CR.
    (first [ pose proof ((as_live_ok LPA A m md b (cap k) AINV LV)) as dR_12; dand7 dR_12 as _ BAL BAPP BHI _ BMP _ | destruct (as_live_ok LPA A m md b (cap k) AINV LV) as (_ & BAL & BAPP & BHI & _ & BMP & _) ]).
    (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    assert (BLO : 0x60a000 <= b).
    { clear - BAPP CR. unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in BAPP; cbn [cl_image_lo cl_image_hi LPA] in BAPP. lia. }
    assert (SPFV : SPF usp = usp - 128) by reflexivity.
    rewrite lshape_unfold. replace (len0 + n =? cap k) with true by (symmetry; apply Z.eqb_eq; exact E).
    destruct (Nat.eq_dec k 10) as [K|K].
    - (* [comment removed for export] *)
      replace (10 <=? Z.of_nat k) with true by (symmetry; apply Z.leb_le; lia).
      assert (EC : cap k = 67108864) by (rewrite K; reflexivity).
      rewrite EC in *.
      pose proof (munch_refl [] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
      assert (CF : client_fpx (L:=LPA) A (aview A m) []) by exact I.
      pose proof (fv_gotc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0) as GOTC. pose proof (fv_stderrp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0) as SC.
      ago AINV. fold_cl_segs.
      icall refused_walk by (first [assumption | lia]).
      lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
      astopx AINV MU WM CF. name_state m1 md1 AINV1.
      (first [ pose proof ((sbm_io md md1 SBM)) as dR_13; dand3 dR_13 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
      lazymatch goal with H : stk _ (aview A m1) _ _ |- _ => rename H into ST1 end.
      assert (FV1 : FV A m1 md1 (fds3 (FdFile path (Z_to_bv 64 (len0 + n)))) SO_pristine 0 tid).
      { eapply (fview_stack usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A m md); try eassumption.
        all: first [rewrite FS1; exact FS | rewrite FDS1; exact FDS | apply stack_only_nil | exact I]. }
      clear CC AR SH FR MU WM CF GOTC SC.
      pose proof FV1 as [_ _ FS1q FDS1q CC1 AR1 SH1 _ FR1].
      (first [ pose proof (CC1) as dR_14; dand4 dR_14 as MC1 [fe1 [FOK1 FE1]] SOUT1 TR1 | pose proof CC1 as (MC1 & [fe1 [FOK1 FE1]] & SOUT1 & TR1) ]).
      (* [comment removed for export] *)
      unfold t_die.
      pose proof FPRINTF as FP. unfold fprintf_diag_stmt in FP. cbv zeta in FP.
      eapply FP with (d := DF_refused) (arg := []) (slack := []) (pa := 0) (fe := fe1) (lo := STK_LO usp); clear FP.
      all: lazymatch goal with
           | |- ainv _ _ _ => exact AINV1
           | |- mem_inv _ _ => exact MI1
           | |- stk _ _ _ _ => ulit; exact ST1
           | |- file_at _ _ _ => exact FE1
           | |- stderr_ok _ => exact FOK1
           | |- fd_lookup _ _ = _ => rewrite FDS1q; vm_compute; reflexivity
           | |- bytes_at _ _ (sh _) _ => apply stksh_bytes; exact SH1
           | |- (exists j8, rw_cells _ _ STDERR_BUFP _) => apply errbuf_any
           | |- (exists g, ro_cells _ _ SSP_GUARD _) => exact (mc_canary _ _ MC1)
           | |- ro_cells _ _ SSP_GOT _ => exact (mc_sspgot _ _ MC1)
           | |- @eq word _ _ => reflexivity
           | |- _ /\ _ => cbn [diag_fmt_addr]; split; reflexivity
           | |- (Z.of_nat (length _) <= _) => cbn; lia
           | |- t_exit _ _ [] => apply t_emit_has_nil
           | |- forall m', _ => idtac
           | |- _ => ulit; unfold FPRINTF_ICPT_STACK, STK_LO, SPF in *; first [lia | Z.div_mod_to_equations; lia]
           end.
      (intros m7 md7 fe7 rr AINV7; (first [ intro dR_26; dand3 dR_26 as FS7 FDS7 HH7 | intros (FS7 & FDS7 & HH7) ]); intros FOK7 FE7 ms' POST).
      (first [ dex14 POST as v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13; dand5 POST as -> MU7 WM7 MI7 ST7 | dand19 POST as v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 -> MU7 WM7 MI7 ST7 | destruct POST as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & -> & MU7 & WM7 & MI7 & ST7) ]).
      rewrite ?unsigned_lit in MU7, ST7 by (unfold SPF, STK_LO in *; lia).
      replace (ret_pc (Z_to_bv 64 0x86a5c)) with (Z_to_bv 64 0x86a5c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (CC7 : ccells (aview A m7) tid SO_pristine 0).
      { eapply (ccells_after_fprintf (aview A m1)); [exact CC1| | exact MU7| exact FOK7| exact FE7]. unfold FPRINTF_ICPT_STACK, SPF, STK_LO in *. lia. }
      rewrite <- FS1q, <- FS7.
      eapply diag_tail; try exact HCEIL; [exact EXIT| exact U1| lia| exact AINV7| exact MI7| exact CC7| exact ST7].
    - (* [comment removed for export] *)
      replace (10 <=? Z.of_nat k) with false by (symmetry; apply Z.leb_gt; lia).
      set (c := cap k) in *.
      assert (CS : cap (S k) = 2 * c) by (subst c; rewrite cap_S; lia).
      assert (L26 : c < 2 ^ 26).
      { subst c. unfold cap. assert (2 ^ Z.of_nat k <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia). change (2 ^ 26) with (65536 * (2 * 2 ^ 9)). lia. }
      rewrite E in *.
      pose proof (munch_refl [] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
      assert (CF : client_fpx (L:=LPA) A (aview A m) []) by exact I.
      ago AINV. fold_cl_segs.
      icall growM_walk by (first [assumption | lia]).
      lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
      astopx AINV MU WM CF. name_state m1 md1 AINV1.
      (first [ pose proof ((sbm_io md md1 SBM)) as dR_16; dand3 dR_16 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
      lazymatch goal with H : stk _ (aview A m1) _ _ |- _ => rename H into ST1 end.
      assert (FV1 : FV A m1 md1 (fds3 (FdFile path (Z_to_bv 64 c))) SO_pristine 0 tid).
      { eapply (fview_stack usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A m md); try eassumption.
        all: first [rewrite FS1; exact FS | rewrite FDS1; exact FDS | apply stack_only_nil | exact I]. }
      clear CC AR SH FR MU WM CF.
      pose proof FV1 as [_ _ FS1q FDS1q CC1 AR1 SH1 _ FR1].
      (* [comment removed for export] *)
      pose proof MALLOC1 as MA. unfold malloc1_stmt in MA. cbv zeta in MA.
      eapply MA with (n := 2 * c) (T := lshape data fs f (S k) c); clear MA.
      all: lazymatch goal with
           | |- ainv _ _ _ => exact AINV1
           | |- mem_inv _ _ => exact MI1
           | |- @eq word _ _ => reflexivity
           | |- 1 <= _ < REQ_MAX => unfold REQ_MAX; lia
           | |- _ <= NREQ_CAP => rewrite NREQ_CAP_eq; lia
           | |- a_livebytes _ + _ <= LIVE_MAX => rewrite LB, LIVE_MAX_eq; lia
           | |- a_nlive _ + 1 <= NLIVE_MAX => rewrite NL, NLIVE_MAX_eq; lia
           | |- _ < 16 -> _ => lia
           | |- kMaxPrimaryUser < _ -> _ => rewrite SECCRED0_eq in SCC; lia
           | |- prim_cost _ <= a_primcred _ => rewrite prim_cost_secondary by (unfold kMaxPrimaryUser; lia); rewrite PCC, PRIMCRED0_eq; lia   (* [comment removed for export] *)
           | |- In _ (cl_sites LPA) => rewrite unsigned_lit by lia; cbn; tauto
           | |- mapped _ _ _ => ulit; eapply (stk_mapped (L:=LPA)); [exact ST1| exact CEIL| unfold ASTK, STK_LO, SPF; lia| lia]
           | |- forall t0', _ => idtac
           | |- _ => ulit; rewrite ?alloc_ceiling_val; unfold ASTK, STK_LO, SPF in *; first [lia | Z.div_mod_to_equations; lia]
           end.
      * (* [comment removed for export] *)
        intros w0 w1 w2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 r A' m' md' AINV' MI' MDF HLE FRS' RNZ LVA LV' LVO' LB' TC' NL' SC' PC' FRK.   (* [comment removed for export] *)
        (first [ pose proof ((amd_frame_io md1 md' MDF)) as dR_19; dand3 dR_19 as FS' FDS' _ | pose proof (amd_frame_io md1 md' MDF) as (FS' & FDS' & _) ]).
        replace (ret_pc (Z_to_bv 64 0x868a0)) with (Z_to_bv 64 0x868a0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        (first [ pose proof ((as_live_ok LPA A' m' md' r (2 * c) AINV' LV')) as dR_20; dand7 dR_20 as _ RAL RAPP RHI _ RMP _ | destruct (as_live_ok LPA A' m' md' r (2 * c) AINV' LV') as (_ & RAL & RAPP & RHI & _ & RMP & _) ]).
        assert (RLO : 0x60a000 <= r).
        { clear - RAPP CR. unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in RAPP; cbn [cl_image_lo cl_image_hi LPA] in RAPP. lia. }
        assert (BR : b <> r) by (intros X; rewrite X in LV; rewrite LV in LVA; discriminate).
        assert (LVb' : a_live A' b = Some c) by (rewrite (LVO' b BR); exact LV).
        pose proof (as_live_disjoint LPA A' m' md' r (2 * c) b c AINV' LV' LVb' (fun X => BR (eq_sym X))) as DISJ.
        apply (cframe_of_frame_ok LPA) in FRK. rewrite ?unsigned_lit in FRK by (unfold SPF, STK_LO in *; lia).
        assert (FV' : FV A' m' md' (fds3 (FdFile path (Z_to_bv 64 c))) SO_pristine 0 tid).
        { eapply (fview_ccall usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A A' m1 md1 m' md'); try eassumption.
          all: first [rewrite FS'; exact FS1q | rewrite FDS'; exact FDS1q | apply heapish_nowhere | unfold ASTK, STK_LO, SPF; lia]. }
        assert (DAT' : rw_cells rsegs (aview A' m') b [CB (Z.to_nat c) (firstn (Z.to_nat c) data)]).
        { apply (rw_cells_blk_cframe A A' m1 md1 _ _ _ _ _ b c _ _ AINV1 FRK LV DAT); [lia| cbn [cells_size csize Nat.add]; lia| | intros x _ X; exact X].
          unfold ASTK, STK_LO, SPF in *. lia. }
        pose proof FV' as [_ _ FSq FDSq CC' AR' SH' ST' FR'].
        (* [comment removed for export] *)
        destruct (mapped_rw_cells (aview A' m') r (2 * c) RMP ltac:(lia) ltac:(lia) ltac:(lia)) as [junkr RWR].
        destruct (rwCB_split _ _ _ _ (Z.to_nat c) RWR ltac:(lia)) as [RWR1 _].
        (first [ pose proof ((rwCB_elim _ _ _ _ DAT')) as dR_21; dand3 dR_21 as PLEN PB _ | destruct (rwCB_elim _ _ _ _ DAT') as (PLEN & PB & _) ]).
        pose proof (munch_refl [(r, r + c); (SPF usp - MEMCPY_ICPT_STACK, SPF usp)] (aview A' m')) as MU.
        pose proof (wmono_refl rsegs (aview A' m')) as WM.
        assert (CF : client_fpx (L:=LPA) A' (aview A' m') [(r, r + c); (SPF usp - MEMCPY_ICPT_STACK, SPF usp)]).
        { cbn. split; [| split; [| exact I]].
          - left. split; [| exact I]. right. left. exists r, (2 * c). split; [exact LV'| lia].
          - left. split; [| exact I]. left. split; [unfold MEMCPY_ICPT_STACK, STK_LO, SPF in *; lia|]. split; [unfold SPF; lia|].
            replace (SPF usp - (SPF usp - MEMCPY_ICPT_STACK)) with MEMCPY_ICPT_STACK by lia.
            eapply (stk_mapped (L:=LPA)); [exact ST' | exact CEIL | unfold MEMCPY_ICPT_STACK, STK_LO, SPF in *; lia | lia]. }
        unfold MEMCPY_ICPT_STACK in MU, CF.   (* [comment removed for export] *)
        (first [ pose proof ((asan_memcpy_cells_of_consts _ (consts_hold_ainv LPA A' m' md' AINV'))) as dR_22; dand11 dR_22 as MCC1 MCC2 MCC3 MP1 MP2 MP3 MP4 MP5 MP6 MP7 MP8 | pose proof (asan_memcpy_cells_of_consts _ (consts_hold_ainv LPA A' m' md' AINV')) as (MCC1 & MCC2 & MCC3 & MP1 & MP2 & MP3 & MP4 & MP5 & MP6 & MP7 & MP8) ]).
        assert (RSb : range_ok (aview A' m') b c) by (eapply (live_range_ok A' m' md' b c); [exact AINV'| exact LVb'| lia| lia| lia]).
        assert (RDr : range_ok (aview A' m') r c) by (eapply (live_range_ok A' m' md' r (2 * c)); [exact AINV'| exact LV'| lia| lia| lia]).
        ago AINV'. fold_cl_segs.
        icall growC_walk by (first [assumption | lia]).
        lazymatch goal with H : mem_inv _ _ |- _ => rename H into MIa end.
        icall (memcpy_icpt_ok (Z_to_bv 64 0x868bc) (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) w0 w1 w2 (Z_to_bv 64 2) (Z_to_bv 64 r)
                 (Z_to_bv 64 r) (Z_to_bv 64 b) (Z_to_bv 64 c) wa3 wa4 wa5 wa6 wa7 (Z_to_bv 64 p1a) (Z_to_bv 64 c) (Z_to_bv 64 3) (Z_to_bv 64 (2 * c)) (Z_to_bv 64 READ_STAGE)
                 (Z_to_bv 64 b) s8 s9 s10 s11 wt3 wt4 wt5 wt6 F fc _ (firstn (Z.to_nat c) data) (firstn (Z.to_nat c) junkr) (STK_LO usp))
          by (rewrite ?unsigned_lit by lia;
              first [ exact PB | exact PLEN | exact RWR1 | exact MIa | lia
                    | lazymatch goal with |- asan_memcpy_cells _ => split_assum end
                    | ulit; assumption
                    | ulit; unfold MEMCPY_ICPT_STACK, STK_LO, SPF in *; lia
                    | right; split;
                      (eapply (range_ok_high_munch _ (aview A' m')); [eassumption| eassumption| lia| lia| lia|
                        apply Forall_cons; [cbn [fst snd]; clear - RAPP CR; unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in RAPP; cbn [cl_image_lo cl_image_hi LPA] in RAPP; unfold SHMAX; lia
                                           | apply Forall_cons; [cbn [fst snd]; clear - ACV U1' SPFV; unfold SHMAX, MEMCPY_ICPT_STACK, SPF, STK_LO in *; lia| apply Forall_nil]]]) ]).
        lazymatch goal with H : mem_inv _ _ |- _ => rename H into MIb end.
        lazymatch goal with H : rw_cells _ _ r [CB _ (firstn _ data)] |- _ => rename H into RDAT end.
        lazymatch goal with H : bytes_at _ _ b (firstn _ data) |- _ => clear H end.
        icall growF_walk by (exact MIb).
        lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI2 end.
        astopx AINV' MU WM CF. name_state m2 md2 AINV2.
        (first [ pose proof ((sbm_io md' md2 SBM0)) as dR_23; dand3 dR_23 as FS2 FDS2 _ | pose proof (sbm_io md' md2 SBM0) as (FS2 & FDS2 & _) ]).
        lazymatch goal with H : stk _ (aview A' m2) _ _ |- _ => rename H into ST2 end.
        assert (FV2 : FV A' m2 md2 (fds3 (FdFile path (Z_to_bv 64 c))) SO_pristine 0 tid).
        { eapply (fview_stack usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A' m' md'); try eassumption.
          all: first [rewrite FS2; exact FSq | rewrite FDS2; exact FDSq
                     | apply (stack_only_cons_heap usp HCEIL); [eapply app_range_sub; [exact RAPP| lia| lia| lia]|];
                       unfold MEMCPY_ICPT_STACK; apply stack_only_cons; [unfold SPF, STK_LO; lia| unfold SPF; lia| apply stack_only_nil]
                     | unfold MEMCPY_ICPT_STACK, SPF; cbn; lia]. }
        clear CC' AR' SH' FR' CF WM MU.
        (* [comment removed for export] *)
        pose proof FREE1 as FRE. unfold free1_stmt in FRE. cbv zeta in FRE.
        eapply FRE with (p := b) (n0 := c); clear FRE.
        all: lazymatch goal with
             | |- ainv _ _ _ => exact AINV2
             | |- mem_inv _ _ => exact MI2
             | |- @eq word _ _ => reflexivity
             | |- _ \/ a_live _ _ = Some _ => right; exact LVb'
             | |- In _ (cl_sites LPA) => rewrite unsigned_lit by lia; cbn; tauto
             | |- mapped _ _ _ => ulit; eapply (stk_mapped (L:=LPA)); [exact ST2| exact CEIL| unfold ASTK, STK_LO, SPF; lia| lia]
             | |- forall t0', _ => idtac
             | |- _ => ulit; rewrite ?alloc_ceiling_val; unfold ASTK, STK_LO, SPF in *; first [lia | Z.div_mod_to_equations; lia]
             end.
        intros v0 v1 v2 va0 va1 va2 va3 va4 va5 va6 va7 vt3 vt4 vt5 vt6 A'' m3 md3 AINV3 MI3 MDF3 FRS3 LVb3 LVO3 LB3 TC3 NL3 SC3 PC3 FRK3.   (* [comment removed for export] *)
        (first [ pose proof ((amd_frame_io md2 md3 MDF3)) as dR_24; dand3 dR_24 as FS3 FDS3 _ | pose proof (amd_frame_io md2 md3 MDF3) as (FS3 & FDS3 & _) ]).
        replace (ret_pc (Z_to_bv 64 0x868c4)) with (Z_to_bv 64 0x868c4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        apply (cframe_of_frame_ok LPA) in FRK3. rewrite ?unsigned_lit in FRK3 by (unfold SPF, STK_LO in *; lia).
        pose proof (heapish_newblk A' m2 md2 b c AINV2 LVb') as HVB.
        assert (FV3 : FV A'' m3 md3 (fds3 (FdFile path (Z_to_bv 64 c))) SO_pristine 0 tid).
        { eapply (fview_ccall usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A' A'' m2 md2 m3 md3); try eassumption.
          all: first [rewrite FS3; rewrite FS2; exact FSq | rewrite FDS3; rewrite FDS2; exact FDSq | unfold ASTK, STK_LO, SPF; lia]. }
        assert (LVr3 : a_live A'' r = Some (2 * c)) by (rewrite (LVO3 r (fun X => BR (eq_sym X))); exact LV').
        assert (RDAT3 : rw_cells rsegs (aview A'' m3) r [CB (Z.to_nat c) (firstn (Z.to_nat c) data)]).
        { apply (rw_cells_blk_cframe A' A'' m2 md2 _ _ _ _ _ r (2 * c) _ _ AINV2 FRK3 LV' RDAT); [lia| cbn [cells_size csize Nat.add]; lia| |].
          - unfold ASTK, STK_LO, SPF in *. lia.
          - intros x Hx [[_ X]|[_ X]]; [lia|]. clear - Hx X RAPP BAPP ACV CR BHI RHI.
            unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in RAPP, BAPP; cbn [cl_image_lo cl_image_hi LPA] in RAPP, BAPP.
            unfold sh, kShadowOffset in X. Z.div_mod_to_equations. lia. }
        pose proof FV3 as [_ _ FS3q FDS3q CC3 AR3 SH3 ST3 FR3].
        (* [comment removed for export] *)
        rewrite <- CS.
        apply (IH A'' m3 md3 tid (S k) c r); [| rewrite CS; lia| lia].
        constructor; try assumption.
        -- rewrite CS. exact LVr3.
        -- intros q Hq. destruct (Z.eq_dec q b) as [->|NB]; [exact LVb3|]. rewrite (LVO3 q NB), (LVO' q Hq). apply LVO. exact NB.
        -- rewrite LB3, LB', LB, CS. lia.
        -- rewrite NL3, NL', NL. replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; exact BNZ). reflexivity.
        -- rewrite TC3, TC'. replace (2 * c <? 16) with false by (symmetry; apply Z.ltb_ge; lia). lia.
        -- rewrite SC3, SC'. rewrite Nat2Z.inj_succ. destruct (Z.ltb kMaxPrimaryUser (2 * c)); lia.
        -- rewrite PC3, PC'. rewrite prim_cost_secondary by (unfold kMaxPrimaryUser; lia). rewrite Z.sub_0_r. exact PCC.   (* [comment removed for export] *)
        -- intros ff. rewrite FRS3, FRS'. apply FRS.
        -- rewrite CS. split; lia.
        -- lia.
        -- right. rewrite CS. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="BODY DATA EXIT FPRINTF FREE1 MALLOC1 HCEIL"] Theorem loop_ok : forall f, P_lr f /\ P_grow f.
  Proof.
    induction f as [|f [IHL IHG]].
    - split.
      + unfold P_lr. intros until x7. intros LS LT FUEL. pose proof LS as [_ _ _ _ _ _ _ _ _ _ _ (LEN & LENL) K10 _]. exfalso. lia.   (* [comment removed for export] *)
      + unfold P_grow. intros until zt6. intros LS L0 N0 E FUEL. pose proof LS as [_ _ _ _ _ _ _ _ _ _ _ (LEN & LENL) K10 _]. exfalso. lia.   (* [comment removed for export] *)
    - split; [exact (read_step f IHL IHG)| exact (grow_step f IHL)].
  Qed.

  #[using="BODY DATA EXIT FPRINTF FREE1 MALLOC1 HCEIL"] Corollary read_loop : forall f, P_lr f.
  Proof. intros f. exact (proj1 (loop_ok f)). Qed.
End Loop.
End DA_Loop.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes.DA_Myrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ldix OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Entry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Mib4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ejgo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Main OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Am90 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_FKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Tails OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.DA_R1e4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Fpom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Open OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Loop.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.

Module DA_Usage.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr SysStep RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img A_ImgAny.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Se7o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Eg3i DA_Cells DA_Ldix DA_Entry DA_Mib4 DA_Inv DA_Ejgo DA_Main.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes.DA_Myrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ldix OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Entry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Mib4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ejgo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Main.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Walks.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (lo : Z).
  Hypothesis CEIL : alloc_ceiling <= lo.
  #[local] Notation rom := (seg_rom rsegs).

  (* [comment removed for export] *)
  Definition usage1_post (p0 : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m' j8,
      ms' = MS (mkR (Z_to_bv 64 0x869ac) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 2) s1
                    (Z_to_bv 64 STDERR_F) (Z_to_bv 64 0x15abe) (Z_to_bv 64 p0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 FPRINTF_ICPT_ENTRY) fc None m' rom
      /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp + -80)
      /\ rw_cells rsegs m' (bv_unsigned sp + -80) [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 RA_MAIN)].

  #[using="CEIL Clg"] Lemma usage_walk1 : forall (argc ap p0 : Z) (m : word -> option byte),
    lo + 80 <= bv_unsigned sp -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
    1 <= argc <= 1024 -> argc <> 2 -> bv_unsigned sp <= ap -> ap + 8 <= 2^64 -> 0 <= p0 < 2^64 ->
    ro_cells rsegs m 0xa97d8 [C8 (Z_to_bv 64 0xa8a68)] ->
    ro_cells rsegs m STDERR_CELL [C8 (Z_to_bv 64 STDERR_F)] ->
    ro_cells rsegs m ap [C8 (Z_to_bv 64 p0)] ->
    evt rsegs (usage1_post p0 m)
        (MS (mkR (Z_to_bv 64 RA_MAIN) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 argc) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MAIN_PC) fc None m rom).
  Proof.
    intros argc ap p0 m LO MI ST AR A2 AP0 AP1 P0 GOT SC AV. unfold STDERR_CELL, STDERR_F, MAIN_PC, RA_MAIN in *.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 80%nat ST.
    run_to 0x86824. at_pc 0x86824.
    azstep. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    run_to 0x869a8. at_pc 0x869a8. bstep. apply evt_done. unfold usage1_post, FPRINTF_ICPT_ENTRY.
    eexists _, _. split; [reflexivity|]. repeat (split; [eassumption|]). exact FR.
  Qed.

  (* [comment removed for export] *)
  Definition usage2_post (spf y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 : word) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x97c78) (Z_to_bv 64 (bv_unsigned spf + 80)) gp tp y0 y1 y2 s0 s1 (Z_to_bv 64 2) y3 y4 y5 y6 y7 y8 y9
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y10 y11 y12 y13)
               F (Z_to_bv 64 EXIT_ENTRY) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned spf + 80).

  #[using="CEIL Clg"] Lemma usage_walk2 : forall (spf r y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 : word) (m : word -> option byte) (j8 : list byte),
    lo <= bv_unsigned spf -> bv_unsigned spf + 80 <= 2^64 -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned spf) ->
    rw_cells rsegs m (bv_unsigned spf) [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 RA_MAIN)] ->
    evt rsegs (usage2_post spf y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 m)
        (MS (mkR (Z_to_bv 64 0x869ac) spf gp tp y0 y1 y2 (Z_to_bv 64 2) s1 r y3 y4 y5 y6 y7 y8 y9
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y10 y11 y12 y13)
            F (Z_to_bv 64 0x869ac) fc None m rom).
  Proof.
    intros spf r y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 m j8 LO HI MI ST FR. unfold RA_MAIN in *.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    pose proof (munch_refl [(bv_unsigned spf, bv_unsigned spf + 80)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    run_to 0x86a1c. at_pc 0x86a1c.
    release_frame FR ST (bv_unsigned spf + 80).
    bstep. bstep. bstep. apply evt_done. unfold usage2_post, EXIT_ENTRY. exists m. split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI| assumption].
  Qed.
End Walks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Usage.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  Variable usp : Z.
  Hypothesis HCEIL : alloc_ceiling = usp - 0x800000.   (* [comment removed for export] *)
  Variables argv envp : list (list byte).
  Variable fs : Fs.
  Hypothesis Hva : valid_argv argv.
  Hypothesis FPRINTF : fprintf_diag_stmt.
  Hypothesis EXIT : exit_spec_stmt.

  Lemma hd_nth0 : forall l : list (list byte), hd [] l = nth 0 l [].
  Proof. intros [|a l]; reflexivity. Qed.

  Lemma fds_std_2 : fd_lookup fds_std (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. vm_compute. reflexivity. Qed.

  #[using="EXIT FPRINTF Hva HCEIL"] Theorem usage_ok : usage_stmt usp argv envp fs.
  Proof.
    unfold usage_stmt. intros until md. intros A DI EA NE2.
    pose proof DI as DI'. destruct DI' as [AINV MI FS FDS FRN ST SPC SH [tid CC] GOT AR].
    (first [ pose proof (CC) as dR_1; dand4 dR_1 as MC [fe [FOK FE]] SO TR | pose proof CC as (MC & [fe [FOK FE]] & SO & TR) ]). pose proof AR as [P0 P1 S0 S1 K0 K1 B0 B1 (U1 & U2 & U3 & U4)].
    unfold sp_window_lo in U1.
    pose proof Hva as (AC & _ & ALEN & ANUL & APATH).
    assert (CEIL : alloc_ceiling <= STK_LO usp) by (unfold STK_LO; rewrite HCEIL; lia).
    assert (L0B : Z.of_nat (length (nth 0 argv [])) <= 131071).
    { destruct argv as [|a l]; [cbn; lia|]. cbn. exact (Forall_inv ALEN). }
    assert (N0 : ~ In (Z_to_bv 8 0) (nth 0 argv [])).
    { destruct argv as [|a l]; [cbn; tauto|]. cbn. exact (Forall_inv ANUL). }
    (* [comment removed for export] *)
    pose proof (consts_hold_ainv LPA A m md AINV) as CH.
    assert (GOTC : ro_cells rsegs (aview A m) 0xa97d8 [C8 (Z_to_bv 64 0xa8a68)]).
    { apply ro_C8_of_bytes. apply (consts_lookup _ 0xa97d8 _ CH). vm_compute. reflexivity. }
    pose proof (mc_stderrp _ _ MC) as SC. unfold STDERR_CELL in SC.
    assert (AV : ro_cells rsegs (aview A m) (usp + 8) [C8 (Z_to_bv 64 (e_p0a usp argv envp))]) by (apply ro_C8_of_bytes; exact P0).
    (* [comment removed for export] *)
    unfold main_cfg, MAIN_PC, RA_MAIN, SPM.
    pose proof (munch_refl [(usp - 48 - 80, usp - 48)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (ST0 : stk rsegs (aview A m) (STK_LO usp) (bv_unsigned (Z_to_bv 64 (usp - 48)))).
    { rewrite unsigned_lit by lia. (first [ dand3 ST as S0' S1' S' | destruct ST as (S0' & S1' & S') ]). split; [exact S0'|]. split; [lia|]. intros a Ha. apply S'. lia. }
    assert (CF : client_fpx (L:=LPA) A (aview A m) [(usp - 48 - 80, usp - 48)]).
    { cbn. split; [| exact I]. left. split; [| exact I]. left. split; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold STK_LO in *; lia|]. split; [lia|].
      eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | unfold STK_LO in *; lia | lia]. }
    ago AINV. fold_cl_segs.
    icall (usage_walk1 (Z_to_bv 64 (usp - 48)) gp (Z_to_bv 64 TPV) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc (STK_LO usp) CEIL (e_argc argv) (usp + 8) (e_p0a usp argv envp) (aview A m))
      by (first [exact MI | exact ST0 | exact GOTC | exact SC | exact AV | rewrite ?unsigned_lit by lia; unfold e_argc, e_p0a, e_envc, e_L0, e_span, STK_LO in *; lia]).
    lazymatch goal with H : stk _ _ _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : rw_cells _ _ _ [CB 8 _; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 _] |- _ => rename H into FR1 end.
    lazymatch type of FR1 with rw_cells _ _ _ (CB 8 ?j :: _) => set (j8 := j) in FR1 end.
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    astopx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_3; dand3 dR_3 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    (* [comment removed for export] *)
    assert (SO1 : stack_only usp [(usp - 48 - 80, usp - 48)]) by (apply stack_only_cons; [unfold STK_LO; lia| lia| apply stack_only_nil]).
    (first [ pose proof ((bundle_stack usp argv envp HCEIL _ _ _ tid SO_pristine 0 MU SO1 ltac:(unfold sp_window_lo; lia) U2 CC AR SH)) as dR_4; dand4 dR_4 as CC1 AR1 SH1 GOT1 | destruct (bundle_stack usp argv envp HCEIL _ _ _ tid SO_pristine 0 MU SO1 ltac:(unfold sp_window_lo; lia) U2 CC AR SH) as (CC1 & AR1 & SH1 & GOT1) ]).
    clear CC AR SH MC FE SO.
    (first [ pose proof (CC1) as dR_5; dand4 dR_5 as MC1 [fe1 [FOK1 FE1]] SOUT1 TR1 | pose proof CC1 as (MC1 & [fe1 [FOK1 FE1]] & SOUT1 & TR1) ]).
    (first [ pose proof ((aa_s0k _ _ _ _ AR1)) as dR_6; dex1 dR_6 as sl0; destruct dR_6 as [SL0 SB0] | pose proof ((aa_s0k _ _ _ _ AR1)) as dR_6; dand3 dR_6 as sl0 SL0 SB0 | destruct (aa_s0k _ _ _ _ AR1) as (sl0 & SL0 & SB0) ]).
    (* [comment removed for export] *)
    rewrite hd_nth0. unfold t_die.
    pose proof FPRINTF as FP. unfold fprintf_diag_stmt in FP. cbv zeta in FP.
    eapply FP with (d := DF_usage) (arg := nth 0 argv []) (slack := sl0) (pa := e_p0a usp argv envp) (fe := fe1) (lo := STK_LO usp); clear FP.
    all: lazymatch goal with
         | |- ainv _ _ _ => exact AINV1
         | |- mem_inv _ _ => exact MI1
         | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST1
         | |- file_at _ _ _ => exact FE1
         | |- stderr_ok _ => exact FOK1
         | |- fd_lookup _ _ = _ => rewrite FDS1, FDS; apply fds_std_2
         | |- bytes_at _ _ (sh _) _ => apply stksh_bytes; exact SH1
         | |- (exists j8, rw_cells _ _ STDERR_BUFP _) => apply errbuf_any
         | |- (exists g, ro_cells _ _ SSP_GUARD _) => exact (mc_canary _ _ MC1)
         | |- ro_cells _ _ SSP_GOT _ => exact GOT1
         | |- @eq word _ _ => reflexivity
         | |- _ /\ _ => cbn [diag_fmt_addr]; split; [reflexivity|]; split; [exact SB0|]; split; [exact N0|];
                        pose proof (aa_b0 _ _ _ _ AR1) as B0'; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); rewrite ?unsigned_lit by lia; rewrite SL0;
                        unfold e_p0a, e_L0, e_argc, e_envc, e_span in *; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [lia | Z.div_mod_to_equations; lia]
         | |- t_exit _ _ [] => apply t_emit_has_nil
         | |- forall m', _ => idtac
         | |- _ => rewrite ?unsigned_lit by lia; unfold FPRINTF_ICPT_STACK, STK_LO in *; first [lia | Z.div_mod_to_equations; lia]
         end.
    (* [comment removed for export] *)
    (intros m2 md2 fe2 r AINV2; (first [ intro dR_9; dand3 dR_9 as FS2 FDS2 HH2 | intros (FS2 & FDS2 & HH2) ]); intros FOK2 FE2 ms' POST).
    (first [ dex14 POST as y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13; dand5 POST as -> MU2 WM2 MI2 ST2 | dand19 POST as y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 -> MU2 WM2 MI2 ST2 | destruct POST as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & -> & MU2 & WM2 & MI2 & ST2) ]).
    rewrite ?unsigned_lit in MU2, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 551340)) with (Z_to_bv 64 551340) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (FR2 : rw_cells rsegs (aview A m2) (usp - 48 + -80) [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 RA_MAIN)]).
    { eapply (rw_cells_transport rsegs); [exact FR1| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add]. cbn. unfold FPRINTF_ICPT_STACK, STDERR_F, STDERR_BUFP. lia. }
    assert (AGM : agree_on (in_ranges MC_RANGES) (aview A m1) (aview A m2)).
    { apply (agree_of_munch _ _ _ _ MU2). ranges_outside. }
    assert (AGO : agree_on (in_ranges STDOUT_RANGES) (aview A m1) (aview A m2)).
    { apply (agree_of_munch _ _ _ _ MU2). ranges_outside. }
    assert (AGT : agree_on (in_ranges TR_RANGES) (aview A m1) (aview A m2)).
    { apply (agree_of_munch _ _ _ _ MU2). ranges_outside. }
    assert (CC2 : ccells (aview A m2) tid SO_pristine 0).
    { split; [eapply mcells_agree; [exact AGM| exact MC1]|]. split; [exists fe2; split; assumption|].
      split; [eapply stdout_at_agree; [exact AGO| exact SOUT1]|]. revert TR1 AGT. clear. intros TR1 AGT.
      exact (trcells_agree _ _ _ AGT TR1).   (* [comment removed for export] *) }
    pose proof (munch_refl [] (aview A m2)) as MU3. pose proof (wmono_refl rsegs (aview A m2)) as WM3.
    assert (CF3 : client_fpx (L:=LPA) A (aview A m2) []) by exact I.
    ago AINV2. fold_cl_segs.
    icall (usage_walk2 gp (Z_to_bv 64 TPV) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             F fc (STK_LO usp) CEIL (Z_to_bv 64 (usp - 48 + -80)) r y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 (aview A m2))
      by (first [exact MI2 | rewrite ?unsigned_lit by lia; first [exact ST2 | exact FR2 | unfold STK_LO in *; lia]]).
    lazymatch goal with H : stk _ _ _ _ |- _ => rename H into ST3 end.
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
    astopx AINV2 MU3 WM3 CF3. rename m0 into m3. rename md0 into md3. rename AINV0 into AINV3.
    (first [ pose proof ((sbm_io md2 md3 SBM0)) as dR_8; dand3 dR_8 as FS3 FDS3 _ | pose proof (sbm_io md2 md3 SBM0) as (FS3 & FDS3 & _) ]).
    assert (CC3 : ccells (aview A m3) tid SO_pristine 0).
    { eapply ccells_agree; [| exact CC2]. apply (agree_of_munch _ _ _ _ MU3). ranges_outside. }
    (* [comment removed for export] *)
    apply (srz_conseq _ _ (t_emit (W 1 (pending_of SO_pristine)) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs md3)))).
    - eapply (exit_via EXIT); try eassumption.
      all: lazymatch goal with
           | |- ro_cells _ _ SSP_GOT _ => exact (mc_sspgot _ _ (proj1 CC3))
           | |- @eq word _ _ => reflexivity
           | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST3
           | |- pending_of _ <> [] -> _ => cbn [pending_of]; intros NE; exfalso; apply NE; reflexivity
           | |- _ => rewrite ?unsigned_lit by lia; unfold EXIT_STACK, STK_LO in *; lia
           end.
    - cbn [pending_of W map]. rewrite FS3, FS2, FS1, FS.
      replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; vm_compute; reflexivity).
      apply t_emit_nil_eq. apply t_emit_has_nil.
  Qed.

End Usage.
End DA_Usage.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Definition MSG_SHORT_ADDR : Z := 0x200f9.
Definition MSG_OVERRUN_ADDR : Z := 0x15acf.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma msg_short_rodata : ro_bytes_b rsegs MSG_SHORT_ADDR msg_short = true. Proof. vm_compute. reflexivity. Qed.
Lemma msg_overrun_rodata : ro_bytes_b rsegs MSG_OVERRUN_ADDR msg_overrun = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition dbyte (data : list byte) (i : nat) : Z := bv_unsigned (nth i data (Z_to_bv 8 0)).
Definition cfg_of (data : list byte) : Z := dbyte data 0 + 256 * dbyte data 1.
Definition clen_of (data : list byte) : Z := cfgv (dbyte data 0) (dbyte data 1).
Lemma clen_of_cfg : forall data, clen_of data = cfg_of data mod 32768.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Definition t_tail (data : list byte) (fs : Fs.Fs) : TSet :=
  let b2 := bv_unsigned (nth 2 data (Z_to_bv 8 0)) in
  let cfg := cfg_of data in
  let config_len := Z.to_nat (cfg mod 32768) in
  let calls := match config_len with O => 1%nat | _ => S (Z.to_nat (b2 mod 4)) end in
  t_emit (W 1 (zero_lines calls)) (t_exit (exit_code 0) fs).

Lemma t_body_tail : forall data fs,
  Z.of_nat (length data) < MAX_INPUT -> (6 <= length data)%nat -> (6 + Z.to_nat (clen_of data) <= length data)%nat ->
  t_body data fs = t_tail data fs.
Proof.
  intros data fs H1 H2 H3. unfold t_body, t_tail. rewrite clen_of_cfg in H3. unfold cfg_of, dbyte in *.
  replace (MAX_INPUT <=? Z.of_nat (length data))%Z with false by (symmetry; apply Z.leb_gt; lia).
  replace (length data <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  match goal with |- (if ?x then _ else _) = _ => replace x with false by (symmetry; apply Nat.ltb_ge; lia) end.
  reflexivity.
Qed.

Section Walks.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32).
  #[local] Notation rom := (seg_rom rsegs).

  (* [comment removed for export] *)
  Definition close_call_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x868f4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 3) a1 a2 a3 a4 a5 a6 a7
                    s2 s3 (Z_to_bv 64 3) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 CLOSE_ENTRY) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.
  Lemma close_call_walk : forall (ra : word) (m : word -> option byte),
    mem_inv rsegs m ->
    evt rsegs (close_call_post m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 3) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x868ec) fc None m rom).
  Proof.
    intros ra m MI.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    bstep. bstep. apply evt_done. unfold close_call_post, CLOSE_ENTRY.
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

  (* [comment removed for export] *)
  Definition die31_post (pa : Z) (x9 x18 x19 x21 : word) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x869ec) sp gp tp t0 t1 t2 s0 x9 (Z_to_bv 64 pa) (Z_to_bv 64 31) (Z_to_bv 64 1) (Z_to_bv 64 STDERR_F) a4 a5 a6 a7
                    x18 x19 s4 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 FWRITE_ICPT_ENTRY) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

  Lemma short_walk : forall (L : Z) (m : word -> option byte),
    mem_inv rsegs m -> 0 <= L <= 5 ->
    ro_cells rsegs m 0xa97d8 [C8 (Z_to_bv 64 0xa8a68)] ->
    ro_cells rsegs m STDERR_CELL [C8 (Z_to_bv 64 STDERR_F)] ->
    evt rsegs (die31_post MSG_SHORT_ADDR s1 s2 (Z_to_bv 64 L) s5 m)
        (MS (mkR (Z_to_bv 64 0x868f4) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 L) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x868f4) fc None m rom).
  Proof.
    intros L m MI HL GOT SC. unfold STDERR_CELL, STDERR_F in *.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    azstep. azstep. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    run_to 0x869e8. at_pc 0x869e8. bstep. apply evt_done. unfold die31_post, FWRITE_ICPT_ENTRY, MSG_SHORT_ADDR, STDERR_F.
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

  (* [comment removed for export] *)
  Lemma data_read : forall (m : word -> option byte) b data i,
    bytes_at rsegs m b data -> 0 <= i < Z.of_nat (length data) ->
    ov_read_bytes rsegs m (Z_to_bv 64 (b + i)) 1 = Some [nth (Z.to_nat i) data (Z_to_bv 8 0)].
  Proof.
    intros m b data i BS Hi. change (Z_to_bv 64 (b + i)) with (wa (b + i)). rewrite (bytes_at_read rsegs m b data i 1 BS) by lia. f_equal.
    rewrite <- (firstn_skipn_step data (Z.to_nat i) 0 (nth (Z.to_nat i) data (Z_to_bv 8 0))); [reflexivity|].
    apply nth_error_nth'. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma overrun_walk : forall (L b : Z) (data : list byte) (m : word -> option byte),
    mem_inv rsegs m -> 6 <= L < 2^26 -> 0x60a000 <= b -> b + L <= 2^47 ->
    bytes_at rsegs m b data -> Z.of_nat (length data) = L -> L < clen_of data + 6 ->
    ro_cells rsegs m 0xa97d8 [C8 (Z_to_bv 64 0xa8a68)] ->
    ro_cells rsegs m STDERR_CELL [C8 (Z_to_bv 64 STDERR_F)] ->
    evt rsegs (die31_post MSG_OVERRUN_ADDR (Z_to_bv 64 b) (Z_to_bv 64 (clen_of data)) (Z_to_bv 64 L) (sxb (nth 1 data (Z_to_bv 8 0))) m)
        (MS (mkR (Z_to_bv 64 0x868f4) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 b) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 L) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x868f4) fc None m rom).
  Proof.
    intros L b data m MI HL B0 B1 BS DL CL GOT SC. unfold STDERR_CELL, STDERR_F in *.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (data_read m b data 0 BS ltac:(lia)) as HR0. rewrite Z.add_0_r in HR0. change (Z.to_nat 0) with 0%nat in HR0.
    pose proof (data_read m b data 1 BS ltac:(lia)) as HR1. change (Z.to_nat 1) with 1%nat in HR1.
    set (d0 := nth 0 data (Z_to_bv 8 0)) in *. set (d1 := nth 1 data (Z_to_bv 8 0)) in *.
    pose proof (cfgv_range (bv_unsigned d0) (bv_unsigned d1)) as CR. unfold clen_of, dbyte in CL |- *. fold d0 d1 in CL |- *.
    set (c := cfgv (bv_unsigned d0) (bv_unsigned d1)) in *.
    azstep. azstep. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    azstep. azstep. azstep. azstep. azstep.
    change (Z.lor (Z.shiftr ((Z.shiftl (bv_unsigned (sxb d1)) 57) mod 18446744073709551616) 49) (bv_unsigned d0)) with (cfglen_expr d0 d1).
    rewrite (cfglen_val d0 d1). fold c.
    azstep. azstep. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
    run_to 0x869e8. at_pc 0x869e8. bstep. apply evt_done. unfold die31_post, FWRITE_ICPT_ENTRY, MSG_OVERRUN_ADDR, STDERR_F.
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

  (* [comment removed for export] *)
  Definition trun_post (L b c : Z) (d1 : byte) (x14 : word) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x8696c) sp gp tp t0 t1 t2 (Z_to_bv 64 (b + 2)) (Z_to_bv 64 b)
                    (Z_to_bv 64 (b + 2)) (Z_to_bv 64 c) (Z_to_bv 64 (b + 2 + c + 4)) (Z_to_bv 64 (L - c + -6)) x14 a5 a6 a7
                    (Z_to_bv 64 c) (Z_to_bv 64 (b + 2 + c + 4)) (Z_to_bv 64 (L - c + -6)) (sxb d1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x86ac8) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

  Lemma hdr_walk : forall (L b : Z) (data : list byte) (m : word -> option byte),
    mem_inv rsegs m -> 6 <= L < 2^26 -> 0x60a000 <= b -> b + L <= 2^47 ->
    bytes_at rsegs m b data -> Z.of_nat (length data) = L -> clen_of data + 6 <= L ->
    evt rsegs (trun_post L b (clen_of data) (nth 1 data (Z_to_bv 8 0))
                 (Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (2 + clen_of data + 3)) data (Z_to_bv 8 0)))) m)
        (MS (mkR (Z_to_bv 64 0x868f4) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 b) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 L) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x868f4) fc None m rom).
  Proof.
    intros L b data m MI HL B0 B1 BS DL CL.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (data_read m b data 0 BS ltac:(lia)) as HR0. rewrite Z.add_0_r in HR0. change (Z.to_nat 0) with 0%nat in HR0.
    pose proof (data_read m b data 1 BS ltac:(lia)) as HR1. change (Z.to_nat 1) with 1%nat in HR1.
    set (d0 := nth 0 data (Z_to_bv 8 0)) in *. set (d1 := nth 1 data (Z_to_bv 8 0)) in *.
    pose proof (cfgv_range (bv_unsigned d0) (bv_unsigned d1)) as CR. unfold clen_of, dbyte in CL |- *. fold d0 d1 in CL |- *.
    set (c := cfgv (bv_unsigned d0) (bv_unsigned d1)) in *.
    pose proof (data_read m b data (2 + c + 1) BS ltac:(lia)) as HR2. pose proof (data_read m b data (2 + c + 0) BS ltac:(lia)) as HR3.
    pose proof (data_read m b data (2 + c + 2) BS ltac:(lia)) as HR4. pose proof (data_read m b data (2 + c + 3) BS ltac:(lia)) as HR5.
    azstep. azstep. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    azstep. azstep. azstep. azstep. azstep.
    change (Z.lor (Z.shiftr ((Z.shiftl (bv_unsigned (sxb d1)) 57) mod 18446744073709551616) 49) (bv_unsigned d0)) with (cfglen_expr d0 d1).
    rewrite (cfglen_val d0 d1). fold c.
    azstep. azstep. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
    run_to 0x86968. at_pc 0x86968. bstep. apply evt_done. unfold trun_post.
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

  (* [comment removed for export] *)
  Definition retA_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x869f4) sp gp tp t0 t1 t2 s0 s1 s1 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (cl_free_pc LPA) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.
  Lemma retA_walk : forall (ra : word) (m : word -> option byte),
    mem_inv rsegs m ->
    evt rsegs (retA_post m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x869ec) fc None m rom).
  Proof.
    intros ra m MI.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    bstep. bstep. apply evt_done. unfold retA_post. cbn [cl_free_pc LPA].
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

  (* [comment removed for export] *)
  Definition retB_post (e0 e1 e2 e3 e4 e5 e6 e7 : word) (j8 : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x97c78) (Z_to_bv 64 (bv_unsigned sp + 80)) gp tp t0 t1 t2 e0 e1 s0 a1 a2 a3 a4 a5 a6 a7
                    e2 e3 e4 e5 e6 e7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 EXIT_ENTRY) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + 80).
  Lemma retB_walk : forall (ra : word) (e0 e1 e2 e3 e4 e5 e6 e7 : word) (j8 : list byte) (lo : Z) (m : word -> option byte),
    alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 80 <= 2^64 -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
    rw_cells rsegs m (bv_unsigned sp) [CB 8 j8; C8 e7; C8 e6; C8 e5; C8 e4; C8 e3; C8 e2; C8 e1; C8 e0; C8 (Z_to_bv 64 RA_MAIN)] ->
    evt rsegs (retB_post e0 e1 e2 e3 e4 e5 e6 e7 j8 lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x869f4) fc None m rom).
  Proof.
    intros ra e0 e1 e2 e3 e4 e5 e6 e7 j8 lo m CEIL LO HI MI ST FR. unfold RA_MAIN in *.
    assert (CEILv : alloc_ceiling <= lo) by ((let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); exact CEIL).
    pose proof (munch_refl [(bv_unsigned sp, bv_unsigned sp + 80)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    run_to 0x86a1c. at_pc 0x86a1c.
    release_frame FR ST (bv_unsigned sp + 80).
    bstep. bstep. bstep. apply evt_done. unfold retB_post, EXIT_ENTRY. exists m. split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI| assumption].
  Qed.
End Walks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Header.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  Variable usp : Z.
  Hypothesis HCEIL : alloc_ceiling = usp - 0x800000.   (* [comment removed for export] *)
  Variables argv envp : list (list byte).
  Variable fs : Fs.
  Variables (e0 e1 e2 e3 e4 e5 e6 e7 : word) (j8 : list byte).
  Variables (path data : list byte).
  Variables (gp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).   (* [comment removed for export] *)
  Hypothesis FREE1 : free1_stmt.   (* [comment removed for export] *)
  Hypothesis FWRITE : fwrite_diag_stmt.
  Hypothesis EXIT : exit_spec_stmt.
  Hypothesis DATA : fs_lookup fs path = Some data.
  #[local] Notation rom := (seg_rom rsegs).
  #[local] Notation p1a := (e_p1a usp argv envp).
  #[local] Notation L := (Z.of_nat (length data)).
  #[local] Notation FV := (fview usp argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8).
  #[local] Notation LST := (lst usp argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 path data).

  Ltac ulit := rewrite ?unsigned_lit by (unfold SPF, STK_LO in *; lia).
  Ltac name_state m md AI :=
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mm _) ?mdd) _ =>
      lazymatch goal with H : ainv _ mm mdd |- _ => rename H into AI end; rename mm into m; rename mdd into md end.

  (* [comment removed for export] *)
  #[using="EXIT FREE1 HCEIL"] Lemma ret_tail :
    forall A m md tid (fds : list (word * FdEntry)) (sof : stdout_form) (ini : Z) (b n0 : Z) (st : word)
           (zra z0 z1 z2 xa0 za1 za2 za3 za4 za5 za6 za7 x2 x3 x4 x5 x6 x7 zt3 zt4 zt5 zt6 : word),
      FV A m md fds sof ini tid -> a_live A b = Some n0 -> bv_unsigned st < 4096 ->
      (pending_of sof <> [] -> fd_lookup fds (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ->
      srealizes rsegs
        (mkCfg (MS (mkR zra (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) z0 z1 z2 st (Z_to_bv 64 b) xa0
                        za1 za2 za3 za4 za5 za6 za7 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 zt3 zt4 zt5 zt6)
                   F (Z_to_bv 64 0x869ec) fc None m rom) md)
        (t_emit (W 1 (pending_of sof)) (t_exit (bv_and st (Z_to_bv 64 255)) fs)).
  Proof.
    intros until zt6. intros FV0 LV STB FD1.
    (first [ pose proof ((fv_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0)) as dR_1; dand4 dR_1 as U1 U2 U3 U4 | pose proof (fv_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0) as (U1 & U2 & U3 & U4) ]). pose proof U1 as U1'. unfold sp_window_lo in U1'.
    pose proof (fv_ceil _ HCEIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0) as CEIL.
    pose proof FV0 as [AINV MI FS FDS CC AR SH ST FR].
    (* [comment removed for export] *)
    pose proof (munch_refl [] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) []) by exact I.
    ago AINV. fold_cl_segs.
    icall retA_walk by (exact MI).
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    astopx AINV MU WM CF. name_state m1 md1 AINV1.
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_2; dand3 dR_2 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    lazymatch goal with H : stk _ (aview A m1) _ _ |- _ => rename H into ST1 end.
    assert (FV1 : FV A m1 md1 fds sof ini tid).
    { eapply (fview_stack usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A m md); try eassumption.
      all: first [rewrite FS1; exact FS | rewrite FDS1; exact FDS | apply stack_only_nil | exact I]. }
    clear CC AR SH FR MU WM CF. pose proof FV1 as [_ _ FS1q FDS1q CC1 AR1 SH1 _ FR1].
    (* [comment removed for export] *)
    pose proof FREE1 as FRE. unfold free1_stmt in FRE. cbv zeta in FRE.
    eapply FRE with (p := b) (n0 := n0); clear FRE.
    all: lazymatch goal with
         | |- ainv _ _ _ => exact AINV1
         | |- mem_inv _ _ => exact MI1
         | |- @eq word _ _ => reflexivity
         | |- _ \/ a_live _ _ = Some _ => right; exact LV
         | |- In _ (cl_sites LPA) => rewrite unsigned_lit by lia; cbn; tauto
         | |- mapped _ _ _ => ulit; eapply (stk_mapped (L:=LPA)); [exact ST1| exact CEIL| unfold ASTK, STK_LO, SPF; lia| lia]
         | |- forall t0', _ => idtac
         | |- _ => ulit; rewrite ?alloc_ceiling_val; unfold ASTK, STK_LO, SPF in *; first [lia | Z.div_mod_to_equations; lia]
         end.
    intros v0 v1 v2 va0 va1 va2 va3 va4 va5 va6 va7 vt3 vt4 vt5 vt6 A' m2 md2 AINV2 MI2 MDF FRS LV2 LVO2 LB2 TC2 NL2 SC2 PC2 FRK.   (* [comment removed for export] *)
    (first [ pose proof ((amd_frame_io md1 md2 MDF)) as dR_3; dand3 dR_3 as FS2 FDS2 _ | pose proof (amd_frame_io md1 md2 MDF) as (FS2 & FDS2 & _) ]).
    replace (ret_pc (Z_to_bv 64 0x869f4)) with (Z_to_bv 64 0x869f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (cframe_of_frame_ok LPA) in FRK. rewrite ?unsigned_lit in FRK by (unfold SPF, STK_LO in *; lia).
    pose proof (heapish_newblk A m1 md1 b n0 AINV1 LV) as HVB.
    assert (FV2 : FV A' m2 md2 fds sof ini tid).
    { eapply (fview_ccall usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A A' m1 md1 m2 md2); try eassumption.
      all: first [rewrite FS2; exact FS1q | rewrite FDS2; exact FDS1q | unfold ASTK, STK_LO, SPF; lia]. }
    pose proof FV2 as [_ _ FS2q FDS2q CC2 AR2 SH2 ST2 FR2].
    (* [comment removed for export] *)
    pose proof (munch_refl [(SPF usp, SPF usp + 80)] (aview A' m2)) as MU. pose proof (wmono_refl rsegs (aview A' m2)) as WM.
    assert (CF : client_fpx (L:=LPA) A' (aview A' m2) [(SPF usp, SPF usp + 80)]).
    { cbn. split; [| exact I]. left. split; [| exact I]. left. split; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold STK_LO, SPF in *; lia|]. split; [unfold SPF; lia|].
      replace (SPF usp + 80 - SPF usp) with 80 by lia.
      destruct FR2 as [[_ _] (W0 & W1 & W)]. intros i Hi E. apply (W i); [cbn; lia|]. unfold wa.
      rewrite pa_wview_overlay by (rewrite unsigned_lit by (unfold SPF, STK_LO in *; lia); unfold SPF, STK_LO in *; lia). exact E. }
    assert (SPFV : SPF usp = usp - 128) by reflexivity.
    ago AINV2. fold_cl_segs.
    icall (retB_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ e0 e1 e2 e3 e4 e5 e6 e7 j8 (STK_LO usp) (aview A' m2))
      by (first [exact CEIL | exact MI2 | ulit; first [exact ST2 | exact FR2 | unfold STK_LO, SPF in *; lia]]).
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
    lazymatch goal with H : stk _ _ _ _ |- _ => rename H into ST3 end.
    astopx AINV2 MU WM CF. name_state m3 md3 AINV3.
    (first [ pose proof ((sbm_io md2 md3 SBM0)) as dR_4; dand3 dR_4 as FS3 FDS3 _ | pose proof (sbm_io md2 md3 SBM0) as (FS3 & FDS3 & _) ]).
    rewrite ?unsigned_lit in ST3 by (unfold SPF, STK_LO in *; lia).
    assert (SO3 : stack_only usp [(SPF usp, SPF usp + 80)]) by (apply stack_only_cons; [unfold SPF, STK_LO; lia| unfold SPF; lia| apply stack_only_nil]).
    (first [ pose proof ((bundle_stack usp argv envp HCEIL _ _ _ tid sof ini MU SO3 U1 U2 CC2 AR2 SH2)) as dR_5; dand4 dR_5 as CC3 AR3 SH3 GOT3 | destruct (bundle_stack usp argv envp HCEIL _ _ _ tid sof ini MU SO3 U1 U2 CC2 AR2 SH2) as (CC3 & AR3 & SH3 & GOT3) ]).
    rewrite <- FS2q, <- FS3.
    eapply (exit_via EXIT); try eassumption.
    all: lazymatch goal with
         | |- @eq word _ _ => reflexivity
         | |- stk _ _ _ _ => ulit; exact ST3
         | |- pending_of _ <> [] -> _ => intros NE; rewrite FDS3, FDS2q; exact (FD1 NE)
         | |- _ => ulit; rewrite ?alloc_ceiling_val; unfold EXIT_STACK, STK_LO, SPF in *; lia
         end.
  Qed.

  (* [comment removed for export] *)
  #[using="EXIT FWRITE FREE1 HCEIL"] Lemma die31_core :
    forall (pa : Z) (msg : list byte) A m md tid k b (x5 z1 z2 xa4 xa5 xa6 xa7 x18 x19 x20 x21 x22 x23 zt3 zt4 zt5 zt6 : word),
      FV A m md fds_std SO_pristine 0 tid -> a_live A b = Some (cap k) ->
      length msg = 31%nat -> ro_bytes_b rsegs pa msg = true -> 0x10000 <= pa -> pa + 31 <= 0x216d8 ->
      srealizes rsegs
        (mkCfg (MS (mkR (Z_to_bv 64 0x869ec) (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) x5 z1 z2 (Z_to_bv 64 2) (Z_to_bv 64 b)
                        (Z_to_bv 64 pa) (Z_to_bv 64 31) (Z_to_bv 64 1) (Z_to_bv 64 STDERR_F) xa4 xa5 xa6 xa7
                        x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 zt3 zt4 zt5 zt6)
                   F (Z_to_bv 64 FWRITE_ICPT_ENTRY) fc None m rom) md)
        (t_die msg fs).
  Proof.
    intros until zt6. intros FV1 LV ML MR PLO PHI.
    (first [ pose proof ((fv_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV1)) as dR_6; dand4 dR_6 as U1 U2 U3 U4 | pose proof (fv_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV1) as (U1 & U2 & U3 & U4) ]). pose proof U1 as U1'. unfold sp_window_lo in U1'.
    pose proof (fv_ceil _ HCEIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV1) as CEIL.
    pose proof FV1 as [AINV1 MI1 FS1 FDS1 CC1 AR1 SH1 ST1 FR1].
    (first [ pose proof (CC1) as dR_7; dand4 dR_7 as MC1 [fe1 [FOK1 FE1]] SOUT1 TR1 | pose proof CC1 as (MC1 & [fe1 [FOK1 FE1]] & SOUT1 & TR1) ]).
    rename m into m1. rename md into md1.
    unfold t_die.
    pose proof FWRITE as FW. unfold fwrite_diag_stmt in FW. cbv zeta in FW.
    eapply FW with (msg := msg) (pa := pa) (fe := fe1) (lo := STK_LO usp); clear FW.
    all: lazymatch goal with
         | |- ainv _ _ _ => exact AINV1
         | |- mem_inv _ _ => exact MI1
         | |- fwrite_icpt_cells _ => apply fwrite_icpt_cells_of_consts; [exact (consts_hold_ainv LPA A m1 md1 AINV1)| exact (mc_canary _ _ MC1)]
         | |- stk _ _ _ _ => ulit; exact ST1
         | |- file_at _ _ _ => exact FE1
         | |- stderr_ok _ => exact FOK1
         | |- fd_lookup _ _ = _ => rewrite FDS1; vm_compute; reflexivity
         | |- bytes_at _ _ _ _ => apply rodata_bytes; [exact MI1| exact MR| lia| rewrite ML; lia]
         | |- forall v', consts_hold LPA v' -> _ => intros v' CH'; rewrite ML; apply rodata_range_ok; [exact CH'| lia| lia| lia]
         | |- @eq word _ _ => rewrite ?ML; reflexivity
         | |- (_ <= length _ <= _)%nat => rewrite ML; lia
         | |- t_exit _ _ [] => apply t_emit_has_nil
         | |- forall m', _ => idtac
         | |- _ => rewrite ?ML; ulit; rewrite ?alloc_ceiling_val; unfold FWRITE_ICPT_STACK, STK_LO, SPF in *; lia
         end.
    (intros m2 md2 fe2 AINV2; (first [ intro dR_18; dand3 dR_18 as FS2 FDS2 HH2 | intros (FS2 & FDS2 & HH2) ]); intros FOK2 FE2 ms' POST).
    (first [ dex14 POST as y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13; dand5 POST as -> MU2 WM2 MI2 ST2 | dand19 POST as y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 -> MU2 WM2 MI2 ST2 | destruct POST as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & -> & MU2 & WM2 & MI2 & ST2) ]).
    rewrite ?unsigned_lit in MU2, ST2 by (unfold SPF, STK_LO in *; lia).
    replace (ret_pc (Z_to_bv 64 0x869ec)) with (Z_to_bv 64 0x869ec) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (FV2 : FV A m2 md2 fds_std SO_pristine 0 tid).
    { eapply (fview_after_fwrite usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A m1 md1 m2 md2); try eassumption.
      all: first [rewrite FS2; exact FS1 | rewrite FDS2; exact FDS1 | unfold FWRITE_ICPT_STACK; lia | unfold FWRITE_ICPT_STACK, STK_LO, SPF in *; lia]. }
    apply (srz_conseq _ _ (t_emit (W 1 (pending_of SO_pristine)) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) fs))).
    - eapply (ret_tail A m2 md2 tid fds_std SO_pristine 0 b (cap k)); [exact FV2| exact LV| rewrite unsigned_lit by lia; lia| cbn [pending_of]; intros NE; exfalso; apply NE; reflexivity].
    - cbn [pending_of W map]. replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; vm_compute; reflexivity).
      apply t_emit_nil_eq. apply t_emit_has_nil.
  Qed.

  (* [comment removed for export] *)
  Record bst (A : AS) (m : word -> option byte) (md : Model) (tid : Z) (k : nat) (b : Z) : Prop := {
    bs_fv     : FV A m md fds_std SO_pristine 0 tid;
    bs_bnz    : b <> 0;
    bs_live   : a_live A b = Some (cap k);
    bs_only   : forall q, q <> b -> a_live A q = None;
    bs_bytes  : a_livebytes A = cap k;
    bs_nlive  : a_nlive A = 1;
    bs_tiny   : 1 <= a_tinycred A;
    bs_secc   : SECCRED0 - 1 - Z.of_nat k <= a_seccred A;     (* [comment removed for export] *)
    bs_primc  : a_primcred A = PRIMCRED0;                    (* [comment removed for export] *)
    bs_frames : forall ff, a_frame A ff = None;
    bs_data   : rw_cells rsegs (aview A m) b [CB (Z.to_nat L) data];
    bs_len    : L < cap k;
    bs_k      : (k <= 10)%nat;
    bs_grown  : k = 0%nat \/ cap k <= 2 * L
  }.

  (* [comment removed for export] *)
  Definition trun_stmt : Prop :=
    forall A m md tid k b (z0 z1 z2 x14 za5 za6 za7 zt3 zt4 zt5 zt6 : word),
      bst A m md tid k b -> 6 <= L -> clen_of data + 6 <= L ->
      srealizes rsegs
        (mkCfg (MS (mkR (Z_to_bv 64 0x8696c) (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) z0 z1 z2
                        (Z_to_bv 64 (b + 2)) (Z_to_bv 64 b)
                        (Z_to_bv 64 (b + 2)) (Z_to_bv 64 (clen_of data)) (Z_to_bv 64 (b + 2 + clen_of data + 4)) (Z_to_bv 64 (L - clen_of data + -6))
                        x14 za5 za6 za7
                        (Z_to_bv 64 (clen_of data)) (Z_to_bv 64 (b + 2 + clen_of data + 4)) (Z_to_bv 64 (L - clen_of data + -6))
                        (sxb (nth 1 data (Z_to_bv 8 0))) (Z_to_bv 64 READ_STAGE) (Z_to_bv 64 0) s8 s9 s10 s11 zt3 zt4 zt5 zt6)
                   F (Z_to_bv 64 0x86ac8) fc None m rom) md)
        (t_tail data fs).
  Hypothesis TRUN : trun_stmt.

  #[using="TRUN EXIT FWRITE FREE1 HCEIL"] Theorem body_ok : body_stmt usp argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 path data gp s8 s9 s10 s11 F fc.
  Proof.
    unfold body_stmt. intros A m md tid k b z0 z1 z2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 LS LT.
    pose proof LS as [FV0 BNZ LV LVO LB NL TC SCC PCC FRS DAT (LEN & LENL) K10 GRW].   (* [comment removed for export] *)
    (first [ pose proof ((fv_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0)) as dR_9; dand4 dR_9 as U1 U2 U3 U4 | pose proof (fv_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0) as (U1 & U2 & U3 & U4) ]). pose proof U1 as U1'. unfold sp_window_lo in U1'.
    pose proof (fv_ceil _ HCEIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0) as CEIL.
    pose proof FV0 as [AINV MI FS FDS CC AR SH ST FR].
    pose proof (cap_range k K10) as CR.
    (first [ pose proof ((as_live_ok LPA A m md b (cap k) AINV LV)) as dR_10; dand7 dR_10 as _ BAL BAPP BHI _ BMP _ | destruct (as_live_ok LPA A m md b (cap k) AINV LV) as (_ & BAL & BAPP & BHI & _ & BMP & _) ]).
    (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    assert (BLO : 0x60a000 <= b).
    { clear - BAPP CR. unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in BAPP; cbn [cl_image_lo cl_image_hi LPA] in BAPP. lia. }
    rewrite firstn_all2 in DAT by lia.
    (* [comment removed for export] *)
    pose proof (munch_refl [] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) []) by exact I.
    ago AINV. fold_cl_segs.
    icall close_call_walk by (exact MI).
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    astopx AINV MU WM CF. name_state m1 md1 AINV1.
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_11; dand3 dR_11 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    lazymatch goal with H : stk _ (aview A m1) _ _ |- _ => rename H into ST1 end.
    assert (FV1 : FV A m1 md1 (fds3 (FdFile path (Z_to_bv 64 L))) SO_pristine 0 tid).
    { eapply (fview_stack usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A m md); try eassumption.
      all: first [rewrite FS1; exact FS | rewrite FDS1; exact FDS | apply stack_only_nil | exact I]. }
    clear CC AR SH FR MU WM CF. pose proof FV1 as [_ _ FS1q FDS1q CC1 AR1 SH1 _ FR1].
    pose proof (close_ok (AI:=AI)) as CL. unfold close_stmt in CL. cbv zeta in CL.
    eapply CL with (lo := STK_LO usp); clear CL.
    all: lazymatch goal with
         | |- ainv _ _ _ => exact AINV1
         | |- mem_inv _ _ => exact MI1
         | |- @eq word _ _ => reflexivity
         | |- m_fds _ = _ => exact FDS1q
         | |- stk _ _ _ _ => ulit; exact ST1
         | |- (exists e, rw_cells _ _ ERRNO_CELL _) => apply rw_errno_any
         | |- forall m', _ => idtac
         | |- _ => ulit; rewrite ?alloc_ceiling_val; unfold CLOSE_STACK, STK_LO, SPF in *; lia
         end.
    (intros m2 md2 AINV2; (first [ intro dR_19; dand3 dR_19 as FS2 FDS2 HH2 | intros (FS2 & FDS2 & HH2) ]); intros ms' POST).
    (first [ dex14 POST as w0 w1 w2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6; dand6 POST as -> MU2 WM2 MI2 ST2 _ | dand20 POST as w0 w1 w2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 -> MU2 WM2 MI2 ST2 _ | destruct POST as (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & wt3 & wt4 & wt5 & wt6 & -> & MU2 & WM2 & MI2 & ST2 & _) ]).
    cbn [OPEN_STACK] in MU2. rewrite ?unsigned_lit in MU2, ST2 by (unfold SPF, STK_LO in *; lia).
    replace (ret_pc (Z_to_bv 64 0x868f4)) with (Z_to_bv 64 0x868f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (FV2 : FV A m2 md2 fds_std SO_pristine 0 tid).
    { eapply (fview_stack usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A m1 md1); try eassumption.
      all: first [rewrite FS2; exact FS1q | exact FDS2
                 | unfold OPEN_STACK; apply stack_only_cons; [unfold SPF, STK_LO; lia| unfold SPF; lia| apply stack_only_nil]
                 | unfold OPEN_STACK, SPF; cbn; lia]. }
    assert (DAT2 : rw_cells rsegs (aview A m2) b [CB (Z.to_nat L) data]).
    { eapply (rw_cells_transport rsegs); [exact DAT| exact MU2| exact WM2|]. unfold OPEN_STACK, SPF in *. cbn. lia. }
    clear CC1 AR1 SH1 FR1. pose proof FV2 as [_ _ FS2q FDS2q CC2 AR2 SH2 _ FR2].
    assert (BS2 : bst A m2 md2 tid k b) by (constructor; assumption).
    (* [comment removed for export] *)
    destruct (Z_lt_le_dec L 6) as [SHORT|L6].
    - (* [comment removed for export] *)
      unfold t_body. replace (MAX_INPUT <=? L)%Z with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
      replace (length data <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
      pose proof (munch_refl [] (aview A m2)) as MU. pose proof (wmono_refl rsegs (aview A m2)) as WM.
      assert (CF : client_fpx (L:=LPA) A (aview A m2) []) by exact I.
      pose proof (fv_gotc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV2) as GOTC. pose proof (fv_stderrp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV2) as SC.
      ago AINV2. fold_cl_segs.
      icall short_walk by (first [exact MI2 | exact GOTC | exact SC | lia]).
      lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
      astopx AINV2 MU WM CF. name_state m3 md3 AINV3.
      (first [ pose proof ((sbm_io md2 md3 SBM0)) as dR_13; dand3 dR_13 as FS3 FDS3 _ | pose proof (sbm_io md2 md3 SBM0) as (FS3 & FDS3 & _) ]).
      lazymatch goal with H : stk _ (aview A m3) _ _ |- _ => rename H into ST3 end.
      assert (FV3 : FV A m3 md3 fds_std SO_pristine 0 tid).
      { eapply (fview_stack usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A m2 md2); try eassumption.
        all: first [rewrite FS3; exact FS2q | rewrite FDS3; exact FDS2q | apply stack_only_nil | exact I]. }
      eapply (die31_core MSG_SHORT_ADDR msg_short A m3 md3 tid k b); [exact FV3| exact LV| reflexivity| exact msg_short_rodata| unfold MSG_SHORT_ADDR; lia| unfold MSG_SHORT_ADDR; lia].
    - destruct (Z_lt_le_dec L (clen_of data + 6)) as [OVR|HOK].
      + (* [comment removed for export] *)
        unfold t_body. replace (MAX_INPUT <=? L)%Z with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
        replace (length data <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
        match goal with |- srealizes _ _ (if ?x then _ else _) =>
          replace x with true by (symmetry; apply Nat.ltb_lt; pose proof (clen_of_cfg data); unfold cfg_of, dbyte in *; lia) end.
        pose proof (munch_refl [] (aview A m2)) as MU. pose proof (wmono_refl rsegs (aview A m2)) as WM.
        assert (CF : client_fpx (L:=LPA) A (aview A m2) []) by exact I.
        pose proof (fv_gotc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV2) as GOTC. pose proof (fv_stderrp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV2) as SC.
        (first [ pose proof ((rwCB_elim _ _ _ _ DAT2)) as dR_14; dand3 dR_14 as DLEN DB _ | destruct (rwCB_elim _ _ _ _ DAT2) as (DLEN & DB & _) ]).
        ago AINV2. fold_cl_segs.
        icall (overrun_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc L b data (aview A m2))
          by (first [exact MI2 | exact DB | exact GOTC | exact SC | lia]).
        lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
        astopx AINV2 MU WM CF. name_state m3 md3 AINV3.
        (first [ pose proof ((sbm_io md2 md3 SBM0)) as dR_15; dand3 dR_15 as FS3 FDS3 _ | pose proof (sbm_io md2 md3 SBM0) as (FS3 & FDS3 & _) ]).
        lazymatch goal with H : stk _ (aview A m3) _ _ |- _ => rename H into ST3 end.
        assert (FV3 : FV A m3 md3 fds_std SO_pristine 0 tid).
        { eapply (fview_stack usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A m2 md2); try eassumption.
          all: first [rewrite FS3; exact FS2q | rewrite FDS3; exact FDS2q | apply stack_only_nil | exact I]. }
        eapply (die31_core MSG_OVERRUN_ADDR msg_overrun A m3 md3 tid k b); [exact FV3| exact LV| reflexivity| exact msg_overrun_rodata| unfold MSG_OVERRUN_ADDR; lia| unfold MSG_OVERRUN_ADDR; lia].
      + (* [comment removed for export] *)
        rewrite (t_body_tail data fs); [| unfold MAX_INPUT; lia| lia| pose proof (clen_of_cfg data); lia].
        pose proof (munch_refl [] (aview A m2)) as MU. pose proof (wmono_refl rsegs (aview A m2)) as WM.
        assert (CF : client_fpx (L:=LPA) A (aview A m2) []) by exact I.
        (first [ pose proof ((rwCB_elim _ _ _ _ DAT2)) as dR_16; dand3 dR_16 as DLEN DB _ | destruct (rwCB_elim _ _ _ _ DAT2) as (DLEN & DB & _) ]).
        ago AINV2. fold_cl_segs.
        icall (hdr_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc L b data (aview A m2))
          by (first [exact MI2 | exact DB | lia]).
        lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
        astopx AINV2 MU WM CF. name_state m3 md3 AINV3.
        (first [ pose proof ((sbm_io md2 md3 SBM0)) as dR_17; dand3 dR_17 as FS3 FDS3 _ | pose proof (sbm_io md2 md3 SBM0) as (FS3 & FDS3 & _) ]).
        lazymatch goal with H : stk _ (aview A m3) _ _ |- _ => rename H into ST3 end.
        assert (FV3 : FV A m3 md3 fds_std SO_pristine 0 tid).
        { eapply (fview_stack usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A m2 md2); try eassumption.
          all: first [rewrite FS3; exact FS2q | rewrite FDS3; exact FDS2q | apply stack_only_nil | exact I]. }
        apply (TRUN A m3 md3 tid k b); [| lia| lia].
        constructor; try assumption.
  Qed.
End Header.
