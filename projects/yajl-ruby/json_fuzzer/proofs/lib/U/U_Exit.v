(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import STRW_tac.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import U_StartupLib U_StartupLib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UF_memset U_Startup_A U_Startup_B.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UX_atexit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0x1a99c);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 z64;
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x1ab58); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 z64; C8 z64; C4 (Z_to_bv 64 fd); C4 z64; C8 z64; C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 z64;
   CB 80 tail].

End RC__1.
Notation RSTDOUT := 0x25458%Z (only parsing).       (* [comment removed for export] *)
Notation RSTDOUT_BUF := 0x55d78%Z (only parsing).   (* [comment removed for export] *)
Notation RSTDERR := 0x25368%Z (only parsing).       (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0x1ab60%Z (only parsing).
Notation F_STDIO_WRITE := 0x1a9c8%Z (only parsing).

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition stdout_file (m : word -> option byte) (so : stdout_st) : Prop :=
  exists (flags mode : word) (tail bufbytes : list byte),
    rw_cells usegs m RSTDOUT
      (file_cells flags
         (if so_active so then RSTDOUT_BUF + 1024 else 0)%Z
         (if so_active so then RSTDOUT_BUF + zlength (so_buf so) else 0)%Z
         (if so_active so then RSTDOUT_BUF else 0)%Z
         (if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
         RSTDOUT_BUF 1024 1 mode
         (if so_lbf_nl so then 10 else 0xffffffff)%Z tail)
    /\ Z.land (bv_unsigned flags) 72 = 0%Z
    /\ rw_cells usegs m RSTDOUT_BUF [CB 1024 bufbytes]
    /\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
    /\ (zlength (so_buf so) <= 1024)%Z
    /\ (so_active so = false -> so_buf so = []).

(* [comment removed for export] *)
Definition stderr_file (m : word -> option byte) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells usegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x55d70 0 2 mode 0xffffffff tail).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section StdioExitStatement.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  Definition stdio_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (m : word -> option byte) (s : St) : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 so' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0x25540); (RSTDOUT_BUF, 0x56178)]%Z m m'
      /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ s' = set_so so' s
      /\ stdout_file m' so' /\ so_buf so' = [] 
      /\ stderr_file m'
      /\ rw_cells usegs m' 0x24290 [C8 (Z_to_bv 64 0x55910)] /\ rw_cells usegs m' 0x55910 [C8 guard].

  Definition stdio_exit_spec_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
           (cdt thr sec : byte) (tm1 : word),
      stk usegs m lo (bv_unsigned sp) ->
      rw_cells usegs m 0x55930 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->   (* [comment removed for export] *)
      rw_cells usegs m 0x55d60 [C8 z64] ->                                            (* [comment removed for export] *)
      rw_cells usegs m 0x55d50 [C8 z64] ->                                            (* [comment removed for export] *)
      rw_cells usegs m 0x25540 [C8 (Z_to_bv 64 RSTDOUT)] ->                          (* [comment removed for export] *)
      rw_cells usegs m 0x25450 [C8 (Z_to_bv 64 RSTDERR)] ->                          (* [comment removed for export] *)
      stdout_file m (get_so s) -> stderr_file m ->
      rw_cells usegs m 0x24290 [C8 (Z_to_bv 64 0x55910)] -> rw_cells usegs m 0x55910 [C8 guard] ->   (* [comment removed for export] *)
      mem_inv usegs m ->
      tp = Z_to_bv 64 RTP ->
      (lo <= bv_unsigned sp - 160)%Z -> (0x57000 <= lo)%Z ->
      (bv_unsigned sp < 0x800000000000)%Z (* [comment removed for export] *) ->
      implM usegs (stdout_exit_flush get_so set_so) s
            (stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1a7b8) fc None m (seg_rom usegs)).
End StdioExitStatement.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rexit_prefix_post (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code t : Z) (td0 td1 td2 td3 ra : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x17fa0) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 code) s1
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1a7b8) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (0x55908, 0x55910); (0x25598, 0x25599); (RATX, RATX + 544)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp + -16)
    /\ rw_cells usegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells usegs m' RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
    /\ rw_cells usegs m' 0x55908 [C4 (Z_to_bv 64 t)]
    /\ rw_cells usegs m' 0x25598 [C1 (Z_to_bv 8 1)].

Lemma rexit_prefix_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 : word)
    (reg : bool) (p3 p4 FJ AJ : list byte) (cdt thr sec : byte) (tm1 : word),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->      (* [comment removed for export] *)
  rw_cells usegs m 0x55908 [C4 z64] ->                                              (* [comment removed for export] *)
  rw_cells usegs m 0x24298 [C8 (Z_to_bv 64 0x24200); C8 (Z_to_bv 64 0x241f8)] ->    (* [comment removed for export] *)
  rw_cells usegs m 0x241f8 [C8 (Z_to_bv 64 0x13470)] ->                            (* [comment removed for export] *)
  rw_cells usegs m 0x25598 [C1 (Z_to_bv 8 0)] ->                                    (* [comment removed for export] *)
  rw_cells usegs m 0x24240 [C8 (Z_to_bv 64 0x17e18); C8 z64] ->                     (* [comment removed for export] *)
  rw_cells usegs m 0x252a8 [C8 (Z_to_bv 64 0x252a8)] ->                             (* [comment removed for export] *)
  rw_cells usegs m RATX (atx_cells reg p3 p4 FJ AJ) ->                              (* [comment removed for export] *)
  rw_cells usegs m 0x355a4 [C1 (Z_to_bv 8 0)] ->                                    (* [comment removed for export] *)
  rw_cells usegs m 0x55930 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->    (* [comment removed for export] *)
  mem_inv usegs m ->
  tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
  (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 64)%Z -> (0x57000 <= lo)%Z ->
  evt usegs (rexit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t td0 td1 td2 td3 ra m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x17f34) fc None m (seg_rom usegs)).
Proof.
  intros until tm1. intros ST TDa EXL GF FA FIN GCX DSO ATX FLG LCH MI -> -> Ht LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (0x55908, 0x55910); (0x25598, 0x25599); (RATX, RATX + 544)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold atx_cells in ATX.
  carve_frame 16%nat ST.
  do 6 lstep.
  replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
    by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
  lstep. lstep.
  (* [comment removed for export] *)
  amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
  lstep. if_false. amo_step. lstep. if_false.
  lstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
  lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. lstep. if_true.
  steps_to 0x17d50%Z.
  (* [comment removed for export] *)
  name_sp sp (-16)%Z.
  call (rfoe_spec reg); [rewrite Hsp; exact ST | exact ATX | exact FLG | exact LCH | exact MI | lia | lia | ].
  unname_sp. rename POST into ST.
  steps_to 0x17ee8%Z.
  (* [comment removed for export] *)
  carve_frame 32%nat ST. steps_to 0x13470%Z.
  carve_frame 16%nat ST. steps_to 0x134fc%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. astep.
  steps_to 0x17f30%Z. release_frame FR0 ST (bv_unsigned sp + -16)%Z. astep. astep.
  astep.
  unfold rexit_prefix_post. sys_finish.
Time Qed.

Section ExitProof.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  (* [comment removed for export] *)
  Hypothesis stdio_exit_spec : stdio_exit_spec_stmt get_so set_so.

  Lemma exit_spec : forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 guard : word)
      (cdt thr sec : byte) (tm1 : word) (reg : bool) (p3 p4 FJ AJ : list byte),
    stk usegs m lo (bv_unsigned sp) ->
    rw_cells usegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->      (* [comment removed for export] *)
    rw_cells usegs m 0x55908 [C4 z64] ->                                              (* [comment removed for export] *)
    rw_cells usegs m 0x24298 [C8 (Z_to_bv 64 0x24200); C8 (Z_to_bv 64 0x241f8)] ->    (* [comment removed for export] *)
    rw_cells usegs m 0x241f8 [C8 (Z_to_bv 64 0x13470)] ->                            (* [comment removed for export] *)
    rw_cells usegs m 0x25598 [C1 (Z_to_bv 8 0)] ->                                    (* [comment removed for export] *)
    rw_cells usegs m 0x24240 [C8 (Z_to_bv 64 0x17e18); C8 z64] ->                     (* [comment removed for export] *)
    rw_cells usegs m 0x252a8 [C8 (Z_to_bv 64 0x252a8)] ->                             (* [comment removed for export] *)
    rw_cells usegs m RATX (atx_cells reg p3 p4 FJ AJ) ->                              (* [comment removed for export] *)
    rw_cells usegs m 0x355a4 [C1 (Z_to_bv 8 0)] ->                                    (* [comment removed for export] *)
    rw_cells usegs m 0x55930 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells usegs m 0x55d60 [C8 z64] -> rw_cells usegs m 0x55d50 [C8 z64] ->
    rw_cells usegs m 0x25540 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells usegs m 0x25450 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m (get_so s) -> stderr_file m ->
    rw_cells usegs m 0x24290 [C8 (Z_to_bv 64 0x55910)] -> rw_cells usegs m 0x55910 [C8 guard] ->
    mem_inv usegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 176)%Z -> (0x57000 <= lo)%Z ->
    (bv_unsigned sp < 0x800000000000)%Z (* [comment removed for export] *) ->
    implM usegs (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x17f34) fc None m (seg_rom usegs)).
  Proof.
    intros until AJ. intros ST TDa EXL GF FA FIN GCX DSO ATX FLG LCH OFL SIN SOU SEU SOF SEF GG GU MI -> -> Ht LO LOLO SPTS.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    (* [comment removed for export] *)
    destruct SOF as (flg & mode & tail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
    destruct SEF as (flg' & mode' & ee & wend' & tail' & SEF1).
    unfold file_cells in SOF1, SEF1.
    unfold Driver.exit_model.
    eapply (implM_bind usegs _ _ s
              (fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
                 ms' = MS (mkR (Z_to_bv 64 0x17fa0) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x17fa0) fc None m' (seg_rom usegs))).
    - (* [comment removed for export] *)
      change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
      unfold implM. iprefix.
      call rexit_prefix_spec; [exact ST | exact TDa | exact EXL | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact ATX | exact FLG | exact LCH | exact MI
                              | reflexivity | reflexivity | lia | lia | lia | ].
      name_sp sp (-16)%Z.
      pose proof stdio_exit_spec as SE. unfold stdio_exit_spec_stmt, implM in SE.
      apply evt_done. eapply impl_epost_mono; [eapply SE|].
      all: lazymatch goal with
           | |- forall _, _ =>
               intros [[] s'] ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
               destruct_exs PO; destruct PO as (E & PO); subst ms'; cbn [fst snd];
               replace (ret_pc (Z_to_bv 64 0x17fa0)) with (Z_to_bv 64 0x17fa0) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
               repeat eexists; cbv delta [mkR]; reflexivity
           | |- stdout_file _ _ => exists flg, mode, tail, bufb; exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6)))))
           | |- stderr_file _ => exists flg', mode', ee, wend', tail'; exact SEF1
           | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | lia ]
           end.
    - (* [comment removed for export] *)
      clear SOF1 SOF2 SOF3 SOF4 SOF5 SOF6 SEF1.
      intros [] s' ms' PO. destruct_exs PO. subst ms'.
      apply implM_sys. do 4 lstep. step_ecall.
      split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
  Time Qed.
End ExitProof.
End RC__2.
