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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr SysStep RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec RelSpec RefNodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct Lazyiq4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcp3q7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpwpz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpwpz.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpwpz.AIcpdm8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpwpz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Nodes DA_Se7o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Eg3i DA_Cells DA_Ldix DA_S5p6.

Module DA_Sfwc.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Eg3i DA_Cells DA_Ldix DA_S5p6.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes.DA_Myrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ldix OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_S5p6.
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

Definition IOCTL_ECALL : Z := 0x9e2e4.
Definition SW_RET : Z := 0x9e308.

(* [comment removed for export] *)
Lemma rw_cells_recast : forall segs m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[W B] WR] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact WR.
Qed.

(* [comment removed for export] *)
Definition file_cells5 (f : mfile) : list cell :=
  C1 (Z_to_bv 8 5) :: C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: tl (file_cells f).

Lemma file_cells5_wf : forall f, cells_wf (file_cells5 f).
Proof. intros f. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit. Qed.
Lemma file_cells5_bytes : forall f, mf_flags f = 5 -> cells_bytes (file_cells5 f) = cells_bytes (file_cells f).
Proof. intros f FL. unfold file_cells5, file_cells. rewrite FL. cbn [tl cells_bytes cbytes]. rewrite <- (le4_lit 5) by lia. reflexivity. Qed.
Lemma file_at5 : forall m Fa f, mf_flags f = 5 -> file_at m Fa f -> rw_cells rsegs m Fa (file_cells5 f).
Proof. intros m Fa f FL H. exact (rw_cells_recast rsegs m Fa _ _ H (file_cells5_wf f) (file_cells5_bytes f FL)). Qed.
Lemma file_at5_inv : forall m Fa f, mf_flags f = 5 -> rw_cells rsegs m Fa (file_cells5 f) -> file_at m Fa f.
Proof.
  intros m Fa f FL H. refine (rw_cells_recast rsegs m Fa _ _ H _ (eq_sym (file_cells5_bytes f FL))).
  cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Walks.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (lo : Z) (g : word) (f : mfile) (sa l : Z).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + 144 <= bv_unsigned sp.
  Hypothesis FD : mf_fd f = 1.
  Hypothesis FL : mf_flags f = 5.
  #[local] Notation rom := (seg_rom rsegs).
  #[local] Notation FRAME m1 j := (rw_cells rsegs m1 (bv_unsigned sp + -32) [CB 8 j; C8 g; C8 s0; C8 ra]).

  (* [comment removed for export] *)
  Definition so1_post (t0 t1 t2 t3 t4 t5 t6 : word) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists junk m',
      ms' = MSsvc (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 SSP_GUARD) s1
                       (Z_to_bv 64 1) (Z_to_bv 64 0x5413) (Z_to_bv 64 (bv_unsigned sp + -32)) (Z_to_bv 64 sa) (Z_to_bv 64 0x5413)
                       (Z_to_bv 64 l) (Z_to_bv 64 STDOUT_F) (Z_to_bv 64 29)
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 IOCTL_ECALL) (Z_to_bv 64 29) fc None m' rom
      /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (STDOUT_F, STDOUT_F + 152)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp + -32)
      /\ FRAME m' junk
      /\ rw_cells rsegs m' STDOUT_F (file_cells5 (mf_set_write_lbf f STDIO_WRITE (mf_lbf f))).

  #[using="FL FD LO CEIL Clg"] Lemma so_walk1 : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> file_at m STDOUT_F f ->
    ro_cells rsegs m SSP_GOT [C8 (Z_to_bv 64 SSP_GUARD)] -> ro_cells rsegs m SSP_GUARD [C8 g] ->
    evt rsegs (so1_post t0 t1 t2 t3 t4 t5 t6 m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STDOUT_F) (Z_to_bv 64 sa) (Z_to_bv 64 l) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STDOUT_WRITE_ENTRY) fc None m rom).
  Proof.
    intros until m. intros MI ST FILE GOT CAN.
    apply (file_at5 m _ f FL) in FILE. unfold file_cells5, file_cells in FILE. rewrite FD in FILE. cbn [tl] in FILE.
    unfold SSP_GOT, SSP_GUARD, STDOUT_F, STDOUT_WRITE_ENTRY in *.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (0xad3f8, 0xad3f8 + 152)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 32%nat ST.
    run_to 0x9e2e4. at_pc 0x9e2e4.
    step_ecall. unfold so1_post, IOCTL_ECALL, SSP_GUARD, STDOUT_F, file_cells5, file_cells, mf_set_write_lbf, STDIO_WRITE.
    cbn [tl mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148].
    rewrite FD.
    eexists _, _. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition so2_post (t0 t1 t2 t3 t4 t5 t6 : word) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 SW_RET) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 SSP_GUARD) s1
                    (Z_to_bv 64 STDOUT_F) (Z_to_bv 64 sa) (Z_to_bv 64 l) (Z_to_bv 64 (-1)) (Z_to_bv 64 0x5413)
                    (Z_to_bv 64 l) (Z_to_bv 64 STDOUT_F) (Z_to_bv 64 29)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 STDIO_WRITE_ENTRY) fc None m' rom
      /\ munch [(STDOUT_F, STDOUT_F + 152)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ file_at m' STDOUT_F (mf_set_write_lbf f STDIO_WRITE (-1)).

  #[using="FL FD"] Lemma so_walk2 : forall (t0 t1 t2 t3 t4 t5 t6 : word) (m : word -> option byte),
    mem_inv rsegs m ->
    rw_cells rsegs m STDOUT_F (file_cells5 (mf_set_write_lbf f STDIO_WRITE (mf_lbf f))) ->
    evt rsegs (so2_post t0 t1 t2 t3 t4 t5 t6 m)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 SSP_GUARD) s1
                 (Z_to_bv 64 (18446744073709551616 - 25)) (Z_to_bv 64 0x5413) (Z_to_bv 64 (bv_unsigned sp + -32)) (Z_to_bv 64 sa) (Z_to_bv 64 0x5413)
                 (Z_to_bv 64 l) (Z_to_bv 64 STDOUT_F) (Z_to_bv 64 29)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (IOCTL_ECALL + 4)) fc None m rom).
  Proof.
    intros until m. intros MI FILE.
    unfold file_cells5, file_cells, mf_set_write_lbf in FILE.
    cbn [tl mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148] in FILE.
    rewrite FD in FILE.
    unfold SSP_GUARD, STDOUT_F, STDIO_WRITE, STDIO_WRITE_ENTRY, IOCTL_ECALL in *. lit_addrs_goal.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl [(0xad3f8, 0xad3f8 + 152)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    run_to 0x9e2f8. at_pc 0x9e2f8. bstep.
    run_to 0x9e304. at_pc 0x9e304. bstep.
    apply evt_done. unfold so2_post, SW_RET, SSP_GUARD, STDOUT_F, STDIO_WRITE_ENTRY.
    eexists _. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    apply (file_at5_inv _ _ (mf_set_write_lbf f STDIO_WRITE (-1))); [exact FL|]. unfold file_cells5, file_cells, mf_set_write_lbf, STDIO_WRITE.
    cbn [tl mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148].
    rewrite FD. exact FILE.
  Qed.

  (* [comment removed for export] *)
  Definition so3_post (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) g g a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m rom
      /\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m /\ stk rsegs m lo (bv_unsigned sp).

  #[using="LO CEIL Clg"] Lemma so_walk3 : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (j : list byte),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp + -32) -> FRAME m j -> ro_cells rsegs m SSP_GUARD [C8 g] ->
    evt rsegs (so3_post t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m)
        (MS (mkR (Z_to_bv 64 SW_RET) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 SSP_GUARD) s1
                 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SW_RET) fc None m rom).
  Proof.
    intros until j. intros MI ST FR CAN. unfold SSP_GUARD, SW_RET in *.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    run_to 0x9e310. at_pc 0x9e310. bstep.
    run_to 0x9e320. at_pc 0x9e320. release_frame FR ST (bv_unsigned sp).
    bstep. apply evt_done. unfold so3_post. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.
End Walks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Leaf.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  Ltac icall_consts_in H ::= unfold STDOUT_F, IOCTL_ECALL in H.

  Lemma stdout_write_ok : stdout_write_stmt.
  Proof.
    unfold stdout_write_stmt. intros until K. cbv zeta.
    intros AINV MI A0 A1 A2 FILE FDf FLf BUF BSZ FDL WB WP PB PS LPOS PLE LS S0 S1 SEP SEPF [g CAN] GOT ST LO CEIL SPHI HK HKONT.
    unfold STDOUT_WRITE_STACK in *. subst a0 a1 a2.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    pose proof CAN as CAN'. unfold SSP_GUARD in CAN'. pose proof GOT as GOT'. unfold SSP_GOT, SSP_GUARD in GOT'.
    pose proof PB as PB'. unfold STDOUT_BUF in PB'. unfold STDOUT_F in SEPF.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (STDOUT_F, STDOUT_F + 152)] (aview A m)) as MU. unfold STDOUT_F in MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (IMGC : img_client (L:=LPA) STDOUT_F (STDOUT_F + 152)).
    { unfold STDOUT_F. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
    assert (CF : client_fpx (L:=LPA) A (aview A m) [(bv_unsigned sp - 144, bv_unsigned sp); (709624, 709624 + 152)]).
    { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|]. eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]. }
      split; [| exact I]. right. exact IMGC. }
    (* [comment removed for export] *)
    ago AINV. fold_cl_segs.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_CAN); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_GOT); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_PB); icall (so_walk1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo g f sa (Z.of_nat (length s)) CEIL LO FDf FLf
             t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (aview A m))
      by (first [exact MI | exact ST | exact FILE | exact GOT | exact CAN | lia]).
    lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -32) _ |- _ => rename H into FR1 end.
    lazymatch goal with H : rw_cells _ _ 709624 _ |- _ => rename H into FILE1 end.
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    astop_svcx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
    (* [comment removed for export] *)
    pose proof (as_minv LPA A m1 md1 AINV1) as [HMI1 HH1].
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_1; dand3 dR_1 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    eapply (srz_ioctl_winsz_hull (cl_segs LPA)) with (x8 := Z_to_bv 64 29) (fd := Z_to_bv 64 1) (c := Z_to_bv 64 1);
      [exact HH1 | reflexivity | reflexivity | reflexivity | rewrite unsigned_lit by lia; lia | rewrite FDS1; exact FDL | reflexivity |].
    rewrite advance_set_gpr0_MSsvc. simp_regs. rewrite (errno_ret_neg ENOTTY) by (unfold ENOTTY; lia). unfold ENOTTY.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (709624, 709624 + 152)] (aview A m1)) as MU2. pose proof (wmono_refl rsegs (aview A m1)) as WM2.
    assert (CF2 : client_fpx (L:=LPA) A (aview A m1) [(bv_unsigned sp - 144, bv_unsigned sp); (709624, 709624 + 152)]).
    { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|].
        replace (bv_unsigned sp - (bv_unsigned sp - 144)) with (112 + 32) by lia.
        eapply (window_mapped LPA _ lo); [exact ST1 | exact FR1 | cbn; lia | exact CEIL | lia | lia]. }
      split; [| exact I]. right. exact IMGC. }
    ago AINV1. fold_cl_segs. unfold IOCTL_ECALL.
    icall (so_walk2 ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f sa (Z.of_nat (length s)) FDf FLf
             _ _ _ _ _ _ _ (aview A m1))
      by (first [exact MI1 | exact FILE1 | lia]).
    lazymatch goal with H : file_at _ _ _ |- _ => rename H into FILE2 end.
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI2 end.
    astopx AINV1 MU2 WM2 CF2. rename m0 into m2. rename md0 into md2. rename AINV0 into AINV2.
    (first [ pose proof ((sbm_io md1 md2 SBM0)) as dR_2; dand3 dR_2 as FS2 FDS2 _ | pose proof (sbm_io md1 md2 SBM0) as (FS2 & FDS2 & _) ]).
    (* [comment removed for export] *)
    replace (W 1 (pend ++ s)) with (W (mf_fd (mf_set_write_lbf f STDIO_WRITE (-1))) (pend ++ s)) by (cbn [mf_fd mf_set_write_lbf]; rewrite FDf; reflexivity).
    eapply (stdio_write_ok _ _ gp tp _ _ _ _ s1 _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 md2 A
              STDOUT_F (mf_set_write_lbf f STDIO_WRITE (-1)) pend s sa (STDOUT_BUF + Z.of_nat (length pend)) lo K AINV2 MI2 eq_refl eq_refl eq_refl FILE2);
      [ left; exact FDf
      | unfold STDOUT_F; lia | unfold STDOUT_F, SSP_GUARD; lia
      | exact IMGC
      | cbn [mf_fd mf_set_write_lbf]; rewrite FDf, FDS2, FDS1; exact FDL
      | cbn [mf_wbase mf_buf mf_set_write_lbf]; rewrite BUF; exact WB
      | cbn [mf_wpos mf_set_write_lbf]; exact WP
      | cbn [mf_buf mf_set_write_lbf]; rewrite BUF; reflexivity
      | cbn [mf_buf mf_set_write_lbf]; rewrite BUF; exact PB'
      | exact PS
      | lia | lia
      | cbn [mf_buf mf_bufsize mf_set_write_lbf]; rewrite BUF; unfold STDOUT_BUF; lia
      | cbn [mf_buf mf_bufsize mf_set_write_lbf]; rewrite BUF, BSZ; unfold STDOUT_BUF; lia
      | cbn [mf_bufsize mf_set_write_lbf]; rewrite BSZ; lia
      | cbn [mf_bufsize mf_set_write_lbf]; rewrite BSZ; lia
      | lia | lia
      | cbn [mf_buf mf_set_write_lbf]; rewrite BUF; unfold STDOUT_BUF, STDIO_WRITE_STACK; rewrite unsigned_lit by lia; lia
      | unfold STDIO_WRITE_STACK; rewrite unsigned_lit by lia; lia
      | eexists; eassumption | eassumption
      | rewrite unsigned_lit by lia; exact ST1 | unfold STDIO_WRITE_STACK; rewrite unsigned_lit by lia; lia | exact CEIL | rewrite unsigned_lit by lia; lia | exact HK | ].
    (* [comment removed for export] *)
    (intros m3 md3 AINV3; (first [ intro dR_5; dand3 dR_5 as FS3 FDS3 HH3 | intros (FS3 & FDS3 & HH3) ]); intros FILE3 ms' PO).
    (first [ dex14 PO as y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13; dand5 PO as -> MU3 WM3 MI3 ST3 | dand19 PO as y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 -> MU3 WM3 MI3 ST3 | destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & -> & MU3 & WM3 & MI3 & ST3) ]).
    unfold STDIO_WRITE_STACK, STDOUT_F in MU3. rewrite unsigned_lit in MU3 by lia. rewrite unsigned_lit in ST3 by lia.
    transport_after_call rsegs (aview A m2) (aview A m3) MU3 WM3. clear MU3 WM3.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] (aview A m3)) as MU4. pose proof (wmono_refl rsegs (aview A m3)) as WM4.
    assert (CF4 : client_fpx (L:=LPA) A (aview A m3) [(bv_unsigned sp - 144, bv_unsigned sp)]).
    { cbn. split; [| exact I]. left. split; [| exact I]. left. split; [lia|]. split; [lia|].
      pose proof ST3 as STx. pose proof FR1 as FRx. release_frame FRx STx (bv_unsigned sp).
      eapply (stk_mapped (L:=LPA)); [exact STx | exact CEIL | lia | lia]. }
    ago AINV3. fold_cl_segs. unfold SW_RET. fix_ret_pc.
    icall (so_walk3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo g (Z.of_nat (length s)) CEIL LO
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A m3) _)
      by (first [exact MI3 | exact ST3 | exact FR1 | eassumption]).
    astopx AINV3 MU4 WM4 CF4. rename m0 into m4. rename md0 into md4. rename AINV0 into AINV4.
    pose proof (as_minv LPA A m4 md4 AINV4) as [_ HH4].
    (first [ pose proof ((sbm_io _ md4 SBM1)) as dR_4; dand3 dR_4 as FS4 FDS4 _ | pose proof (sbm_io _ md4 SBM1) as (FS4 & FDS4 & _) ]).
    eapply (HKONT m4 md4 AINV4).
    { split; [| split; [| exact HH4]]. rewrite FS4, FS3, FS2, FS1; reflexivity. rewrite FDS4, FDS3, FDS2, FDS1; reflexivity. }
    { cbn [mf_buf mf_bufsize mf_set_write_lbf] in FILE3. rewrite BUF, BSZ in FILE3. exact FILE3. }
    repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
    split. { exact MU. }
    split. { exact WM. }
    split; [assumption|]. assumption.
  Qed.
End Leaf.
End DA_Sfwc.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes.DA_Myrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ldix OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_S5p6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Fh3h.DA_Sfwc.
Import ListNotations.
(* [comment removed for export] *)
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
Lemma sx32_neg : forall z, -2^31 <= z < 0 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 (18446744073709551616 + z).
Proof.
  intros z Hz. unfold sx32. apply Z_to_bv_eqm. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (2^32) with 4294967296 by reflexivity. replace (2^31) with 2147483648 by reflexivity.
  change (Z.of_N 64) with 64. change (Z.of_N 32) with 32.
  replace (2^64) with 18446744073709551616 by reflexivity. replace (2 ^ (32 - 1)) with 2147483648 by reflexivity. replace (2^32) with 4294967296 by reflexivity.
  Z.div_mod_to_equations. nia.
Qed.

Section Loop.
  Variables (ra sp gp tp t0 t1 t2 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (Fa wp sa : Z) (s : list byte) (m : word -> option byte).
  Hypothesis PS : bytes_at rsegs m sa s.
  Hypothesis NONL : ~ In (Z_to_bv 8 10) s.
  Hypothesis SR : 0 <= sa /\ sa + Z.of_nat (length s) < 2^47.
  Hypothesis MI : mem_inv rsegs m.
  #[local] Notation rom := (seg_rom rsegs).
  #[local] Notation l := (Z.of_nat (length s)).
  #[local] Notation LST i a1v a3v pc :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fa) (Z_to_bv 64 l)
             (Z_to_bv 64 wp) a1v (Z_to_bv 64 10) a3v a4 a5 a6 a7
             (Z_to_bv 64 sa) (Z_to_bv 64 0) (Z_to_bv 64 i) (Z_to_bv 64 (sa + l)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m rom) (only parsing).
  Definition nl_post : machine_state -> Prop :=
    fun ms' => exists a1v a3v, ms' = LST l a1v a3v 0x9e100 /\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.

  #[using="MI SR NONL PS"] Lemma nl_loop : forall (k : nat) (i : Z) (a3v : word),
    (Z.of_nat k = l - i)%Z -> 0 <= i < l ->
    evt rsegs nl_post (LST i (Z_to_bv 64 (18446744073709551615 - i)) a3v 0x9e09c).
  Proof.
    induction k as [|k IH]; intros i a3v HK HI; [lia|].
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    destruct (nth_error s (Z.to_nat (l - 1 - i))) as [b|] eqn:NB.
    2:{ exfalso. apply nth_error_None in NB. lia. }
    assert (HR : ov_read_bytes rsegs m (Z_to_bv 64 (sa + l + (18446744073709551615 - i))) 1 = Some [b]).
    { replace (Z_to_bv 64 (sa + l + (18446744073709551615 - i))) with (wa (sa + (l - 1 - i))) by (unfold wa; apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
      rewrite (bytes_at_read rsegs m sa s (l - 1 - i) 1 PS) by lia.
      f_equal. rewrite <- (firstn_skipn_step s _ 0 b NB). reflexivity. }
    assert (NB10 : bv_unsigned b <> 10).
    { intros E. apply NONL. replace (Z_to_bv 8 10) with b; [eapply nth_error_In; exact NB|].
      apply bv_eq. rewrite unsigned_lit8 by lia. exact E. }
    pose proof (byte_range b) as BR.
    azstep. azstep.
    azstep. if_cases K0; zify_cond K0. { exfalso. exact (NB10 K0). }
    azstep. azstep. azstep. if_cases K1; zify_cond K1.
    - replace (Z_to_bv 64 (18446744073709551615 - i + -1)) with (Z_to_bv 64 (18446744073709551615 - (i + 1))) by (f_equal; lia).
      apply (IH (i + 1)); lia.
    - azstep. azstep. apply evt_done. unfold nl_post. replace (i + 1) with l by lia.
      eexists _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM| exact MI].
  Qed.
End Loop.

(* [comment removed for export] *)
Lemma rw_cells_CB_split2 : forall segs m A n junk k,
  rw_cells segs m A [CB n junk] -> (k <= n)%nat ->
  rw_cells segs m A [CB k (firstn k junk)] /\ rw_cells segs m (A + Z.of_nat k) [CB (n - k)%nat (skipn k junk)].
Proof.
  intros segs m A n junk k H Hk.
  pose proof (rw_cells_bound segs m A _ H) as HB. cbn [cells_size csize Nat.add] in HB.
  destruct H as [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hl _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  rewrite <- (firstn_skipn k junk) in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2]. rewrite firstn_length_le in B2 by lia.
  (first [ dand3 Hw as Ha Hsz Hw | destruct Hw as (Ha & Hsz & Hw) ]). cbn [cells_size csize Nat.add] in Hsz, Hw.
  split; (split; [split|]).
  - cbn. split; [| exact I]. rewrite firstn_length_le; lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B1.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - cbn. split; [| exact I]. rewrite skipn_length; lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B2.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat k + i) with (A + (Z.of_nat k + i)) by lia. apply Hw. lia.
Qed.

Section Fit.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (lo : Z) (Fa : Z) (f : mfile) (pend s rest : list byte) (sa : Z).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + 2400 <= bv_unsigned sp.
  Hypothesis FAR : 0xaa000 <= Fa /\ Fa + 152 <= 0x60a000.
  Hypothesis BR : 0 < mf_buf f /\ mf_buf f + mf_bufsize f < 2^47 /\ 0 <= mf_bufsize f < 2^31.
  Hypothesis FIT : Z.of_nat (length pend) + Z.of_nat (length s) <= mf_bufsize f.
  Hypothesis RST : Z.of_nat (length pend) + Z.of_nat (length rest) = mf_bufsize f.
  Hypothesis SR : 0 <= sa /\ sa + Z.of_nat (length s) < 2^47.
  Hypothesis BUFF : Fa + 152 <= mf_buf f \/ mf_buf f + mf_bufsize f <= Fa.
  Hypothesis BUFL : mf_buf f + mf_bufsize f <= lo \/ bv_unsigned sp <= mf_buf f.
  Hypothesis SL : sa + Z.of_nat (length s) <= lo \/ bv_unsigned sp <= sa.
  Hypothesis SD : sa + Z.of_nat (length s) <= mf_buf f + Z.of_nat (length pend) \/ mf_buf f + Z.of_nat (length pend) + Z.of_nat (length s) <= sa.
  #[local] Notation rom := (seg_rom rsegs).
  #[local] Notation l := (Z.of_nat (length s)).
  #[local] Notation wp := (mf_buf f + Z.of_nat (length pend)).
  #[local] Notation FRAME m1 j := (rw_cells rsegs m1 (bv_unsigned sp + -64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  #[local] Notation FILEW m1 w :=
    (rw_cells rsegs m1 Fa
       [C4 (Z_to_bv 64 (mf_flags f)); C4 (Z_to_bv 64 0); C8 (mf_rpos f); C8 (mf_rend f); C8 (mf_close f);
        C8 (Z_to_bv 64 (mf_buf f + mf_bufsize f)); C8 (Z_to_bv 64 w); C8 (mf_mbz1 f); C8 (Z_to_bv 64 (mf_buf f));
        C8 (mf_read f); C8 (Z_to_bv 64 (mf_write f)); C8 (mf_seek f);
        C8 (Z_to_bv 64 (mf_buf f)); C8 (Z_to_bv 64 (mf_bufsize f)); C8 (mf_prev f); C8 (mf_next f);
        C4 (Z_to_bv 64 (mf_fd f)); C4 (mf_pipepid f); C8 (mf_lockcount f);
        C4 (Z_to_bv 64 (mf_mode f)); C4 (Z_to_bv 64 (mf_lock f)); C4 (Z_to_bv 64 (mf_lbf f)); C4 (mf_pad148 f)]).

  Definition fxt_post (m1 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 l) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' rom
      /\ munch [(bv_unsigned sp - 2400, bv_unsigned sp); (Fa, Fa + 152); (wp, wp + l)] m1 m' /\ wmono rsegs m1 m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ FILEW m' (wp + l)
      /\ bytes_at rsegs m' (mf_buf f) (pend ++ s)
      /\ rw_cells rsegs m' (wp + l) [CB (length rest - length s)%nat (skipn (length s) rest)].

  Ltac icall_consts_in H ::= unfold MEMCPY_ICPT_STACK in H.

  #[using="SD SL BUFL BUFF SR RST FIT BR FAR LO CEIL Clg"] Lemma fx_tail : forall (t0 t1 t2 a1v a2v a3v a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 : word) (m1 : word -> option byte) (junk : list byte),
    mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -64) -> FRAME m1 junk -> FILEW m1 wp ->
    bytes_at rsegs m1 (mf_buf f) pend -> rw_cells rsegs m1 wp [CB (length rest) rest] -> bytes_at rsegs m1 sa s ->
    asan_memcpy_cells m1 -> (l = 0 \/ (range_ok m1 sa l /\ range_ok m1 wp l)) ->
    evt rsegs (fxt_post m1)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fa) (Z_to_bv 64 l)
               (Z_to_bv 64 wp) a1v a2v a3v a4 a5 a6 a7
               (Z_to_bv 64 sa) (Z_to_bv 64 0) s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9e100) fc None m1 rom).
  Proof.
    intros until junk. intros MI1 ST1 FR FILE PB DST PS MC RNG.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 2400, bv_unsigned sp); (Fa, Fa + 152); (wp, wp + l)] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
    destruct (rw_cells_CB_split2 rsegs m1 wp (length rest) rest (length s) DST ltac:(lia)) as [DST1 DST2]. clear DST.
    run_to 0x574f8. at_pc 0x574f8.
    icall (memcpy_icpt_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 s (firstn (length s) rest) lo)
      by (rewrite ?unsigned_lit by lia; rewrite ?Nat2Z.id; unfold MEMCPY_ICPT_STACK;
          first [exact PS | exact DST1 | exact MI1 | exact MC | exact ST1 | exact CEIL | exact RNG | reflexivity | lia]).
    lazymatch goal with H : rw_cells _ _ wp [CB (Z.to_nat l) s] |- _ => rename H into DSTs end. rewrite Nat2Z.id in DSTs.
    lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST2 end.
    run_to 0x9e13c. at_pc 0x9e13c.
    release_frame FR ST2 (bv_unsigned sp).
    azstep. replace (0 + l) with l by lia. apply evt_done. unfold fxt_post.
    hot_eexists_all. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split. { apply bytes_at_app. split; [eassumption|]. eapply bytes_at_ext; [apply (rw_cells_bytes_at _ _ _ _ DSTs)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity. }
    eassumption.
  Qed.

  #[using="rest s pend"] Lemma asan_memcpy_cells_low : lowP asan_memcpy_cells.
  Proof.
    unfold asan_memcpy_cells. do 3 (apply lowP_and; [apply lowP_ro_cells; cbn; unfold in_zone, kHighMemBeg_z; lia|]). exact lowP_map_cells.
  Qed.

  #[using="SD SL BUFL BUFF SR RST FIT BR FAR LO CEIL Clg"] Lemma fx_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte),
    file_at m Fa f -> mf_wbase f = Z_to_bv 64 (mf_buf f) -> mf_wpos f = Z_to_bv 64 wp -> mf_wend f = Z_to_bv 64 (mf_buf f + mf_bufsize f) ->
    -2^31 <= mf_lbf f < 2^31 -> (mf_lbf f < 0 \/ ~ In (Z_to_bv 8 10) s) ->
    bytes_at rsegs m (mf_buf f) pend -> rw_cells rsegs m wp [CB (length rest) rest] -> bytes_at rsegs m sa s ->
    mem_inv rsegs m -> asan_memcpy_cells m -> stk rsegs m lo (bv_unsigned sp) ->
    (l = 0 \/ (range_ok m sa l /\ range_ok m wp l)) ->
    evt rsegs (fxt_post m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sa) (Z_to_bv 64 l) (Z_to_bv 64 Fa) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FWRITEX_ENTRY) fc None m rom).
  Proof.
    intros until m. intros FILE WB WP WE LBR LBF PB DST PS MI MC ST RNG. unfold FWRITEX_ENTRY.
    unfold file_at, file_cells in FILE. rewrite WB, WP, WE in FILE.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 2400, bv_unsigned sp); (Fa, Fa + 152); (wp, wp + l)] m) as MU.
    pose proof (munch_refl [(bv_unsigned sp - 2400, bv_unsigned sp)] m) as MUlow.
    pose proof (wmono_refl rsegs m) as WM.
    hide MC. hide RNG.
    carve_frame 64%nat ST.
    run_to 0x9e038. at_pc 0x9e038. azstep. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    run_to 0x9e044. at_pc 0x9e044. azstep. if_cases K1; zify_cond K1; [clear K1| exfalso; lia].
    azstep. azstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      unhide MC; unhide RNG;
      assert (WL : wlow [(bv_unsigned sp - 2400, bv_unsigned sp)]) by solve_wlow;
      pose proof (asan_memcpy_cells_low _ m mc MUlow WL MC) as MC1;
      assert (RNG1 : l = 0 \/ (range_ok mc sa l /\ range_ok mc wp l))
        by (destruct RNG as [Z0|[R1 R2]]; [left; exact Z0| right; split; refine (lowP_range_ok _ _ _ _ m mc MUlow WL _); [lia| exact R1| lia| exact R2]]);
      clear MC RNG MUlow WL
    end.
    lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    destruct (Z_lt_le_dec (mf_lbf f) 0) as [NEG|NNEG].
    - rewrite (sx32_neg (mf_lbf f)) by lia. azstep. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
     
      try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FR); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_PS); icall fx_tail by (first [exact MI1 | exact ST1 | exact MC1 | exact RNG1 | eassumption]).
      apply evt_done. unfold fxt_post. hot_eexists_all. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
    - rewrite (sx32_small (mf_lbf f)) by lia. azstep. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
      azstep. if_cases K3; zify_cond K3.
      +
        try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FR); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_PS); icall fx_tail by (first [exact MI1 | exact ST1 | exact MC1 | exact RNG1 | eassumption]).
        apply evt_done. unfold fxt_post. hot_eexists_all. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
      + destruct LBF as [LBF|NONL]; [exfalso; lia|].
        run_to 0x9e09c. at_pc 0x9e09c.
        replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (18446744073709551615 - 0)) by (apply Z_to_bv_eqm; reflexivity).
        icall (nl_loop ra sp gp tp _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc Fa wp sa s _ PS NONL SR MI1 (length s) 0 _)
          by (first [lia | eassumption]).
       
        try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FR); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_PS); icall fx_tail by (first [exact MI1 | exact ST1 | exact MC1 | exact RNG1 | eassumption]).
        apply evt_done. unfold fxt_post. hot_eexists_all. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.
End Fit.

Section Leaf.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  Lemma fwritex_fit_ok : fwritex_fit_stmt.
  Proof.
    unfold fwritex_fit_stmt. intros until lo. cbv zeta.
    intros A0 A1 A2 FILE WB WP WE B0 B1 BS LBR LBF FIT RST PB DST PS S0 S1 MI MC ST LO CEIL FAlo FAhi BUFF BUFL SL SD RNG.
    subst a0 a1 a2. unfold memcpy_icpt_cells in MC.
    eapply evt_mono.
    { apply (fx_main ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo Fa f pend s rest sa CEIL);
        first [assumption | lia | split; [lia|]; split; lia | split; lia]. }
    intros ms' PO. unfold fxt_post in PO. unfold fwritex_fit_post, FWRITEX_STACK, file_at, file_cells, mf_set_w.
    cbn [mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148].
    exact PO.
  Qed.
End Leaf.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WalkB.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (lo : Z) (Fa : Z) (f : mfile) (pend s : list byte) (sa : Z).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + 2400 <= bv_unsigned sp.
  Hypothesis FAR : 0xaa000 <= Fa /\ Fa + 152 <= 0x60a000.
  Hypothesis BR : 0 < mf_buf f /\ mf_buf f + mf_bufsize f < 2^47 /\ 0 <= mf_bufsize f.
  Hypothesis NOFIT : mf_bufsize f - Z.of_nat (length pend) < Z.of_nat (length s).
  Hypothesis PLE : Z.of_nat (length pend) <= mf_bufsize f.
  Hypothesis SR : 0 <= sa /\ sa + Z.of_nat (length s) < 2^47.
  Hypothesis WRH : mf_write f = STDIO_WRITE.
  #[local] Notation rom := (seg_rom rsegs).
  #[local] Notation l := (Z.of_nat (length s)).
  #[local] Notation wp := (mf_buf f + Z.of_nat (length pend)).

  Definition fxf_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 STDIO_WRITE) t2 s0 s1 (Z_to_bv 64 Fa) (Z_to_bv 64 sa) (Z_to_bv 64 l) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 STDIO_WRITE_ENTRY) fc None m' rom
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

  #[using="WRH SR PLE NOFIT BR FAR LO CEIL Clg"] Lemma fxf_walk : forall (m : word -> option byte),
    file_at m Fa f -> mf_wbase f = Z_to_bv 64 (mf_buf f) -> mf_wpos f = Z_to_bv 64 wp -> mf_wend f = Z_to_bv 64 (mf_buf f + mf_bufsize f) ->
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
    evt rsegs (fxf_post m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sa) (Z_to_bv 64 l) (Z_to_bv 64 Fa) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FWRITEX_ENTRY) fc None m rom).
  Proof.
    pose proof NOFIT as NOFITdep. pose proof PLE as PLEdep. pose proof SR as SRdep. pose proof BR as BRdep. pose proof FAR as FARdep. pose proof LO as LOdep.
    intros m FILE WB WP WE MI ST. unfold FWRITEX_ENTRY.
    unfold file_at, file_cells in FILE. rewrite WB, WP, WE, WRH in FILE. unfold STDIO_WRITE in *.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 64%nat ST.
    run_to 0x9e038. at_pc 0x9e038. azstep. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    run_to 0x9e044. at_pc 0x9e044. azstep. if_cases K1; zify_cond K1; [exfalso; lia|]. clear K1.
    run_to 0x9e078. at_pc 0x9e078.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => release_frame H ST (bv_unsigned sp) end.
    azstep. apply evt_done. unfold fxf_post, STDIO_WRITE_ENTRY.
    eexists _. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.
End WalkB.

Section LeafB.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  #[local] Notation rom := (seg_rom rsegs).

  Lemma fwritex_flush_ok : fwritex_flush_stmt.
  Proof.
    unfold fwritex_flush_stmt. intros until K. cbv zeta.
    intros AINV MI A0 A1 A2 FILE FDR WRH WB WP WE B0 B1 B2 NOFIT PLE L26 FAlo FAhi IMGC FDL PB PS S0 S1 SEPB SEPS [g CAN] GOT ST LO CEIL SPHI HK HKONT.
    unfold FWRITEX_STACK in *. subst a0 a1 a2.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    assert (FAhi' : Fa + 152 <= 0x60a000) by (unfold SSP_GUARD in FAhi; lia).
    pose proof (munch_refl [(bv_unsigned sp - 2400, bv_unsigned sp); (Fa, Fa + 152)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) [(bv_unsigned sp - 2400, bv_unsigned sp); (Fa, Fa + 152)]).
    { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|]. eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]. }
      split; [| exact I]. right. exact IMGC. }
    unfold file_at, file_cells in FILE.
    pose proof CAN as CAN'. unfold SSP_GUARD in CAN'. pose proof GOT as GOT'. unfold SSP_GOT, SSP_GUARD in GOT'.
    ago AINV. fold_cl_segs.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_CAN); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_GOT); icall (fxf_walk ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo Fa f pend s sa
             CEIL LO (conj FAlo FAhi') (conj B0 (conj B1 B2)) NOFIT PLE (conj S0 S1) WRH (aview A m))
      by (first [exact FILE | exact WB | exact WP | exact WE | exact MI | exact ST]).
    lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    astopx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_2; dand3 dR_2 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    unfold STDIO_WRITE_ENTRY.
    eapply (stdio_write_ok _ _ gp tp _ _ _ _ s1 _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 md1 A
              Fa f pend s sa (mf_buf f + Z.of_nat (length pend)) lo K AINV1 MI1 eq_refl eq_refl eq_refl);
      [ eassumption | exact FDR | exact FAlo | exact FAhi | exact IMGC
      | rewrite FDS1; exact FDL
      | exact WB | exact WP | reflexivity
      | eassumption | eassumption
      | exact L26 | lia | lia | lia | lia | exact PLE | lia | lia
      | unfold STDIO_WRITE_STACK; lia | unfold STDIO_WRITE_STACK; lia
      | eexists; eassumption | eassumption
      | exact ST1 | unfold STDIO_WRITE_STACK; lia | exact CEIL | rewrite ?unsigned_lit by lia; lia | exact HK | ].
    (intros m2 md2 AINV2; (first [ intro dR_8; dand3 dR_8 as FS2 FDS2 HH2 | intros (FS2 & FDS2 & HH2) ]); intros FILE2 ms' PO).
    (first [ dex14 PO as y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13; dand5 PO as -> MU2 WM2 MI2 ST2 | dand19 PO as y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 -> MU2 WM2 MI2 ST2 | destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & -> & MU2 & WM2 & MI2 & ST2) ]).
    unfold STDIO_WRITE_STACK in MU2.
    eapply (HKONT m2 md2 AINV2).
    { split; [| split; [| exact HH2]]. rewrite FS2, FS1; reflexivity. rewrite FDS2, FDS1; reflexivity. }
    { exact FILE2. }
    hot_eexists_all. split; [reflexivity|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split. { eapply wmono_trans; [exact WM| exact WM2]. }
    split; [exact MI2| exact ST2].
  Qed.
End LeafB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FX_WRET : Z := 0x9e0f0.   (* [comment removed for export] *)

Section WalkD.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (lo : Z) (f : mfile) (pend : list byte) (sa : Z).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + 2400 <= bv_unsigned sp.
  Hypothesis FL : mf_flags f = 5.
  Hypothesis BUF : mf_buf f = STDOUT_BUF.
  Hypothesis BSZ : mf_bufsize f = 1024.
  Hypothesis WRH : mf_write f = STDOUT_WRITE.
  Hypothesis LBF : 0 <= mf_lbf f < 2^31.
  Hypothesis FIT : (length pend + 1 <= 1024)%nat.
  Hypothesis SR : 0 <= sa /\ sa + 1 < 2^47.
  Hypothesis SL : sa + 1 <= lo \/ bv_unsigned sp <= sa.
  #[local] Notation rom := (seg_rom rsegs).
  #[local] Notation wp := (STDOUT_BUF + Z.of_nat (length pend)).
  #[local] Notation FRAME m1 j := (rw_cells rsegs m1 (bv_unsigned sp + -64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  (* [comment removed for export] *)
  Definition fxd1_post (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists junk m',
      ms' = MS (mkR (Z_to_bv 64 FX_WRET) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 STDOUT_F) (Z_to_bv 64 1)
                    (Z_to_bv 64 STDOUT_F) (Z_to_bv 64 sa) (Z_to_bv 64 1) (Z_to_bv 64 STDOUT_WRITE) a4 a5 a6 a7
                    (Z_to_bv 64 sa) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 (sa + 1)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 STDOUT_WRITE_ENTRY) fc None m' rom
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp + -64) /\ FRAME m' junk.

  #[using="SL SR FIT LBF WRH BSZ BUF FL LO CEIL Clg"] Lemma fxd_walk1 : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte),
    file_at m STDOUT_F f -> mf_wpos f = Z_to_bv 64 wp -> mf_wend f = Z_to_bv 64 (STDOUT_BUF + 1024) ->
    bytes_at rsegs m sa [Z_to_bv 8 10] ->
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
    evt rsegs (fxd1_post t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sa) (Z_to_bv 64 1) (Z_to_bv 64 STDOUT_F) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FWRITEX_ENTRY) fc None m rom).
  Proof.
    pose proof CEIL as CEILdep. pose proof LO as LOdep. pose proof FL as FLdep. pose proof BUF as BUFdep. pose proof BSZ as BSZdep. pose proof WRH as WRHdep. pose proof LBF as LBFdep. pose proof FIT as FITdep. pose proof SR as SRdep. pose proof SL as SLdep.
    intros until m. intros FILE WP WE PS MI ST. unfold FWRITEX_ENTRY.
    unfold file_at, file_cells in FILE. rewrite WP, WE, WRH in FILE. unfold STDOUT_F, STDOUT_BUF, STDOUT_WRITE in *.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 64%nat ST.
    run_to 0x9e038. at_pc 0x9e038. azstep. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    run_to 0x9e044. at_pc 0x9e044. azstep. if_cases K1; zify_cond K1; [clear K1| exfalso; lia].
    azstep. azstep. rewrite (sx32_small (mf_lbf f)) by lia.
    azstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia| clear K2].
    azstep. if_cases K3; zify_cond K3; [exfalso; lia| clear K3].
    run_to 0x9e09c. at_pc 0x9e09c.
    replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (HR : ov_read_bytes rsegs mc (Z_to_bv 64 (sa + 18446744073709551616)) 1 = Some [Z_to_bv 8 10])
        by (replace (Z_to_bv 64 (sa + 18446744073709551616)) with (wa (sa + 0)) by (unfold wa; apply Z_to_bv_eqm; Z.div_mod_to_equations; lia);
            rewrite (bytes_at_read rsegs mc sa [Z_to_bv 8 10] 0 1 PS) by (cbn; lia); reflexivity)
    end.
    azstep. azstep.
    azstep. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?unsigned_lit8 in K4 by lia. rewrite ?unsigned_lit in K4 by lia. lia. }
    run_to 0x9e0ec. at_pc 0x9e0ec. azstep.
    apply evt_done. unfold fxd1_post, FX_WRET, STDOUT_F, STDOUT_WRITE, STDOUT_WRITE_ENTRY.
    eexists _, _. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition fxd2_post (m2 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' rom
      /\ munch [(bv_unsigned sp - 2400, bv_unsigned sp); (STDOUT_F, STDOUT_F + 152); (STDOUT_BUF, STDOUT_BUF + 0)] m2 m' /\ wmono rsegs m2 m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ file_at m' STDOUT_F (mf_set_write_lbf (mf_set_w f (Z_to_bv 64 STDOUT_BUF) (Z_to_bv 64 STDOUT_BUF) (Z_to_bv 64 (STDOUT_BUF + 1024))) STDIO_WRITE (-1))
      /\ (exists junk', rw_cells rsegs m' STDOUT_BUF [CB 1024 junk']).

  Ltac icall_consts_in H ::= unfold MEMCPY_ICPT_STACK in H.

  #[using="SL SR FIT LBF WRH BSZ BUF FL LO CEIL pend Clg"] Lemma fxd_walk2 : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m2 : word -> option byte) (junk bj : list byte),
    mem_inv rsegs m2 -> stk rsegs m2 lo (bv_unsigned sp + -64) -> FRAME m2 junk ->
    file_at m2 STDOUT_F (mf_set_write_lbf (mf_set_w f (Z_to_bv 64 STDOUT_BUF) (Z_to_bv 64 STDOUT_BUF) (Z_to_bv 64 (STDOUT_BUF + 1024))) STDIO_WRITE (-1)) ->
    rw_cells rsegs m2 STDOUT_BUF [CB 1024 bj] -> asan_memcpy_cells m2 ->
    evt rsegs (fxd2_post m2)
      (MS (mkR (Z_to_bv 64 FX_WRET) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 STDOUT_F) (Z_to_bv 64 1)
               (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 sa) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 (sa + 1)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FX_WRET) fc None m2 rom).
  Proof.
    pose proof CEIL as CEILdep. pose proof LO as LOdep. pose proof FL as FLdep. pose proof BUF as BUFdep. pose proof BSZ as BSZdep. pose proof WRH as WRHdep. pose proof LBF as LBFdep. pose proof FIT as FITdep. pose proof SR as SRdep. pose proof SL as SLdep.
    intros until bj. intros MI2 ST2 FR FILE BJ MC. unfold FX_WRET.
    unfold file_at, file_cells, mf_set_write_lbf, mf_set_w in FILE.
    cbn [mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148] in FILE.
    rewrite BUF, BSZ in FILE. unfold STDOUT_F, STDOUT_BUF, STDIO_WRITE in *.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 2400, bv_unsigned sp); (709624, 709624 + 152); (6324968, 6324968 + 0)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
    destruct (rw_cells_CB_split2 rsegs m2 6324968 1024 bj 0 BJ ltac:(lia)) as [DST0 DST1]. cbn [firstn] in DST0. clear BJ.
    azstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia| clear K0].
    run_to 0x574f8. at_pc 0x574f8.
    replace (sa + 1 - 0) with (sa + 1) by lia.
    icall (memcpy_icpt_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 [] [] lo)
      by (rewrite ?unsigned_lit by lia; unfold MEMCPY_ICPT_STACK;
          first [exact DST0 | exact MI2 | exact MC | exact ST2 | exact CEIL | apply bytes_at_nil; lia | left; reflexivity | reflexivity | lia
                ]).
    lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST3 end.
    run_to 0x9e13c. at_pc 0x9e13c.
    release_frame FR ST3 (bv_unsigned sp).
    azstep. apply evt_done. unfold fxd2_post, file_at, file_cells, mf_set_write_lbf, mf_set_w, STDOUT_F, STDOUT_BUF, STDIO_WRITE.
    cbn [mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148].
    rewrite BUF, BSZ. replace (6324968 + 0) with 6324968 by lia. replace (1 + 0) with 1 by lia.
    cbn [skipn Nat.sub] in DST1. rewrite Z.add_0_r in DST1.
    hot_eexists_all. split; [reflexivity|]. repeat (split; [eassumption|]). eexists; exact DST1.
  Qed.
End WalkD.

Section LeafD.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  #[local] Notation rom := (seg_rom rsegs).

  Ltac icall_consts_in H ::= unfold FX_WRET, STDOUT_F, STDOUT_BUF in H.

  Lemma fwritex_nl_ok : fwritex_nl_stmt.
  Proof.
    unfold fwritex_nl_stmt. intros until K. cbv zeta.
    intros AINV MI A0 A1 A2 FILE FDf FLf BUF BSZ WRH LBF WB WP WE FIT FDL BJ PEND PS S0 S1 SL SEPF MC [g CAN] GOT ST LO CEIL SPHI HK HKONT.
    unfold FWRITEX_STACK in *. subst a0 a1 a2.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    pose proof CAN as CAN'. unfold SSP_GUARD in CAN'. pose proof GOT as GOT'. unfold SSP_GOT, SSP_GUARD in GOT'.
    pose proof FILE as FILE'. unfold file_at, file_cells in FILE'. unfold STDOUT_F in FILE'.
    pose proof BJ as BJ'. unfold STDOUT_BUF in BJ'. unfold STDOUT_F in SEPF.
    pose proof MC as MC'. (first [ dand4 MC' as MCa MCb MCc MCd | destruct MC' as (MCa & MCb & MCc & MCd) ]). open_map_cells MCd.
    pose proof (munch_refl [(bv_unsigned sp - 2400, bv_unsigned sp); (STDOUT_F, STDOUT_F + 152); (STDOUT_BUF, STDOUT_BUF + 0)] (aview A m)) as MU.
    unfold STDOUT_F, STDOUT_BUF in MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (IMGC : img_client (L:=LPA) STDOUT_F (STDOUT_F + 152)).
    { unfold STDOUT_F. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
    assert (IMGB : img_client (L:=LPA) STDOUT_BUF (STDOUT_BUF + 0)).
    { unfold STDOUT_BUF. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. lia. }
    assert (CF : client_fpx (L:=LPA) A (aview A m) [(bv_unsigned sp - 2400, bv_unsigned sp); (709624, 709624 + 152); (6324968, 6324968 + 0)]).
    { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|]. eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]. }
      split. { right. exact IMGC. } split; [| exact I]. right. exact IMGB. }
    (* [comment removed for export] *)
    ago AINV. fold_cl_segs.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_BJ); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_CAN); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_GOT); icall (fxd_walk1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo f pend sa CEIL LO FLf BUF BSZ WRH LBF FIT (conj S0 S1) SL
             t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (aview A m))
      by (first [exact FILE | exact WP | exact WE | exact PS | exact MI | exact ST]).
    lazymatch goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => rename H into FR1 end.
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    astopx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_5; dand3 dR_5 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).

    (* [comment removed for export] *)
    change (W 1 (pend ++ [Z_to_bv 8 10])) with (W 1 (pend ++ [Z_to_bv 8 10])).
    unfold STDOUT_WRITE_ENTRY.
    eapply (stdout_write_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 md1 A
              f pend [Z_to_bv 8 10] sa lo K AINV1 MI1 eq_refl eq_refl eq_refl);
      [ exact FILE' | exact FDf | exact FLf | exact BUF | exact BSZ
      | rewrite FDS1; exact FDL
      | exact WB | exact WP
      | (* [comment removed for export] *) eapply bytes_at_ext; [| exact PEND]; pose proof (rw_cells_bytes_at _ _ _ _ BJ') as BB; cbn [cells_bytes cbytes] in BB; rewrite app_nil_r in BB;
          rewrite <- (firstn_skipn (length pend) bj) in BB; apply bytes_at_app in BB; destruct BB as [BB _]; exact BB
      | eassumption
      | cbn [length Nat.add]; lia | lia | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia
      | unfold STDOUT_WRITE_STACK; rewrite unsigned_lit by lia; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia
      | unfold STDOUT_F; cbn [length]; lia
      | eexists; eassumption | eassumption
      | rewrite unsigned_lit by lia; exact ST1 | unfold STDOUT_WRITE_STACK; rewrite unsigned_lit by lia; lia | exact CEIL | rewrite ?unsigned_lit by lia; lia | exact HK | ].
    (intros m2 md2 AINV2; (first [ intro dR_9; dand3 dR_9 as FS2 FDS2 HH2 | intros (FS2 & FDS2 & HH2) ]); intros FILE2 ms' PO).
    (first [ dex14 PO as y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13; dand5 PO as -> MU2 WM2 MI2 ST2 | dand19 PO as y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 -> MU2 WM2 MI2 ST2 | destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & -> & MU2 & WM2 & MI2 & ST2) ]).
    unfold STDOUT_WRITE_STACK, STDOUT_F in MU2. rewrite unsigned_lit in MU2 by lia. rewrite unsigned_lit in ST2 by lia.
    transport_after_call rsegs (aview A m1) (aview A m2) MU2 WM2. clear MU2 WM2.

    pose proof (conj MCa (conj MCb (conj MCc (conj Gsh (conj Csh (conj Gmb (conj Cmb (conj Gme (conj Cme (conj Ghe Che))))))))) : asan_memcpy_cells (aview A m2)) as MC2.
    pose proof (munch_refl [(bv_unsigned sp - 2400, bv_unsigned sp); (709624, 709624 + 152); (6324968, 6324968 + 0)] (aview A m2)) as MU3.
    pose proof (wmono_refl rsegs (aview A m2)) as WM3.
    assert (CF3 : client_fpx (L:=LPA) A (aview A m2) [(bv_unsigned sp - 2400, bv_unsigned sp); (709624, 709624 + 152); (6324968, 6324968 + 0)]).
    { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|].
        pose proof ST2 as STx. pose proof FR1 as FRx. release_frame FRx STx (bv_unsigned sp).
        eapply (stk_mapped (L:=LPA)); [exact STx | exact CEIL | lia | lia]. }
      split. { right. exact IMGC. } split; [| exact I]. right. exact IMGB. }
    ago AINV2. fold_cl_segs. unfold FX_WRET. fix_ret_pc.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FR1); icall (fxd_walk2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo f pend sa CEIL LO FLf BUF BSZ WRH LBF FIT (conj S0 S1) SL
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A m2) _ _)
      by (first [exact MI2 | exact ST2 | exact FR1 | exact FILE2 | exact MC2 | eassumption]).
    lazymatch goal with H : (exists _, rw_cells _ _ _ _) |- _ => destruct H as [bj3 BJ3] end.
    astopx AINV2 MU3 WM3 CF3. rename m0 into m3. rename md0 into md3. rename AINV0 into AINV3.
    pose proof (as_minv LPA A m3 md3 AINV3) as [_ HH3].
    (first [ pose proof ((sbm_io _ md3 SBM0)) as dR_7; dand3 dR_7 as FS3 FDS3 _ | pose proof (sbm_io _ md3 SBM0) as (FS3 & FDS3 & _) ]).
    eapply (HKONT m3 md3 AINV3).
    { split; [| split; [| exact HH3]]. rewrite FS3, FS2, FS1; reflexivity. rewrite FDS3, FDS2, FDS1; reflexivity. }
    { eassumption. }
    { eexists; exact BJ3. }
    hot_eexists_all. split; [reflexivity|].
    split. { exact MU. }
    split. { exact WM. }
    split; [assumption|]. assumption.
  Qed.
End LeafD.
