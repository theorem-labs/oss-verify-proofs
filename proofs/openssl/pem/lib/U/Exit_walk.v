(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Monad Stdio Driver.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.  (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Notation usegs := Image.usegs.

From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Exit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Exit_ax.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma AXSTAT_cells : forall k m,
  AXSTAT k m <->
  (rw_cells usegs m RAEF_INCB [C1 (Z_to_bv 8 0)]
   /\ rw_cells usegs m RATEXIT (ax_cells 0 (if k then 1 else 0) (if k then RATEXIT + 24 else 0) 0 (if k then RATEXIT_CALL else 0))
   /\ rw_cells usegs m RATEXIT_A0 [C8 (Z_to_bv 64 (if k then RAEF_GUARD else 0))]).
Proof. intros [|] m; unfold AXSTAT; cbv beta iota; tauto. Qed.

(* [comment removed for export] *)
Notation RSTDIN := 0x31dba0%Z (only parsing).
Definition stdin_file (m : word -> option byte) : Prop :=
  exists (j0 j1 j2 j3 j4 : list byte),
    rw_cells usegs m RSTDIN [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 j1; C8 (Z_to_bv 64 0); CB 8 j2;
                             C8 (Z_to_bv 64 0); CB 76 j3; C4 (Z_to_bv 64 0xffffffff); CB 88 j4].

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
      /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0x31dd78); (RSTDOUT_BUF, 0x3520d8)]%Z m m'
      /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ s' = set_so so' s
      /\ stdout_file m' so' /\ so_buf so' = [] 
      /\ stderr_file m'
      /\ rw_cells usegs m' 0x31c468 [C8 (Z_to_bv 64 0x3509a8)] /\ rw_cells usegs m' 0x3509a8 [C8 guard].

  Definition stdio_exit_spec_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
           (cdt thr sec : byte) (tm1 : word),
      stk usegs m lo (bv_unsigned sp) ->
      rw_cells usegs m 0x350bf8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->   (* [comment removed for export] *)
      rw_cells usegs m 0x351030 [C8 z64] ->                                            (* [comment removed for export] *)
      rw_cells usegs m 0x31dc88 [C8 (Z_to_bv 64 RSTDIN)] -> stdin_file m ->            (* [comment removed for export] *)
      rw_cells usegs m 0x31dd78 [C8 (Z_to_bv 64 RSTDOUT)] ->                          (* [comment removed for export] *)
      rw_cells usegs m 0x31db98 [C8 (Z_to_bv 64 RSTDERR)] ->                          (* [comment removed for export] *)
      stdout_file m (get_so s) -> stderr_file m ->
      rw_cells usegs m 0x31c468 [C8 (Z_to_bv 64 0x3509a8)] -> rw_cells usegs m 0x3509a8 [C8 guard] ->   (* [comment removed for export] *)
      mem_inv usegs m ->
      tp = Z_to_bv 64 RTP ->
      (lo <= bv_unsigned sp - 160)%Z -> (0x353000 <= lo)%Z ->
      implM usegs (stdout_exit_flush get_so set_so) s
            (stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x2b3f40) fc None m (seg_rom usegs)).
End StdioExitStatement.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition exit_prefix_post (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code t : Z) (td0 td1 td2 td3 ra : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x2b0764) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 code) s1
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x2b3f40) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (0x350bd8, 0x350bdc); (0x31dde8, 0x31dde9); (0x3509b8, 0x3509e0)]%Z m m'   (* [comment removed for export] *)
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp + -16)
    /\ rw_cells usegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells usegs m' RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
    /\ rw_cells usegs m' 0x350bd8 [C4 (Z_to_bv 64 t)]
    /\ rw_cells usegs m' 0x31dde8 [C1 (Z_to_bv 8 1)].

Lemma exit_prefix_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 : word)
    (cdt thr sec : byte) (tm1 : word) (k : bool) (bi : byte),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->      (* [comment removed for export] *)
  rw_cells usegs m 0x350bd8 [C4 z64] ->                                              (* [comment removed for export] *)
  rw_cells usegs m 0x31c498 [C8 (Z_to_bv 64 0x2c0650); C8 (Z_to_bv 64 0x2c0640)] ->    (* [comment removed for export] *)
  rw_cells usegs m 0x2c0640 [C8 (Z_to_bv 64 0xe1528); C8 (Z_to_bv 64 0xe1c74)] ->   (* [comment removed for export] *)
  rw_cells usegs m 0x32de20 [C1 bi] ->                                               (* [comment removed for export] *)
  rw_cells usegs m 0x32de24 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
  rw_cells usegs m 0x31dde8 [C1 (Z_to_bv 8 0)] ->                                    (* [comment removed for export] *)
  rw_cells usegs m 0x31bec0 [C8 (Z_to_bv 64 RCXA_FINALIZE); C8 z64] ->               (* [comment removed for export] *)
  mem_inv usegs m ->
  tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
  (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 80)%Z -> (0x353000 <= lo)%Z ->
  rw_cells usegs m RLIBC_HEAD [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->  (* [comment removed for export] *)
  AXSTAT k m ->                                                                      (* [comment removed for export] *)
  rw_cells usegs m RDSO [C8 (Z_to_bv 64 RDSO)] ->                                    (* [comment removed for export] *)
  evt usegs (exit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t td0 td1 td2 td3 ra m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b06f8) fc None m (seg_rom usegs)).
Proof.
  intros until bi. intros ST TDa EXL GF FA BI CF0 FIN GCX MI -> -> Ht LO LOLO LCH AX DSO.
  apply AXSTAT_cells in AX. destruct AX as (INCB & AX & AX0).
  unfold RCXA_FINALIZE, RLIBC_HEAD, RDSO, RAEF_INCB, RATEXIT, RATEXIT_A0, ax_cells in *. cbn [Z.add] in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (0x350bd8, 0x350bdc); (0x31dde8, 0x31dde9); (0x3509b8, 0x3509e0)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
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
  (* [comment removed for export] *)
  lstep. lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (AX1 : AXSTAT k m1) by (apply AXSTAT_cells; unfold RAEF_INCB, RATEXIT, RATEXIT_A0, ax_cells; cbn [Z.add];
                                   split; [exact INCB | split; [exact AX | exact AX0]]) end.
  clear INCB AX AX0.
  (* [comment removed for export] *)
  name_sp sp (-16)%Z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    eapply evt_cut;
      [ eapply (funcs_on_exit_spec k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo cdt thr sec tm1)
      | cbv beta delta [funcs_on_exit_post RATEXIT]; cbn [Z.add]; post_call usegs m1 ]
  end.
  all: unname_sp.
  all: lazymatch goal with
       | |- evt _ _ _ => idtac
       | |- AXSTAT _ _ => exact AX1
       | |- ?g => try unfold RLIBC_HEAD; first [ hyp_by_addr | reflexivity | lia ]
       end.
  try clear AX1.
  match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
  steps_to 0x2b06ac%Z.
  (* [comment removed for export] *)
  carve_frame 32%nat ST. steps_to 0xe1c74%Z.
  (* [comment removed for export] *)
  carve_frame 32%nat ST. steps_to 0xe1c94%Z.
  lstep. if_cases KB;
    (steps_to 0xe1d54%Z; release_frame FR1 ST (bv_unsigned sp + -48)%Z; astep;
     steps_to 0xe1528%Z;
     carve_frame 16%nat ST; steps_to 0xe15b8%Z; release_frame FR1 ST (bv_unsigned sp + -48)%Z; astep;
     steps_to 0x2b06f4%Z; release_frame FR0 ST (bv_unsigned sp + -16)%Z; astep; astep;
     astep;
     unfold exit_prefix_post; sys_finish).
Qed.

Section ExitProof.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  (* [comment removed for export] *)
  Hypothesis stdio_exit_spec : stdio_exit_spec_stmt get_so set_so.

  Lemma exit_spec : forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 guard : word)
      (cdt thr sec : byte) (tm1 : word) (k : bool) (bi : byte),
    stk usegs m lo (bv_unsigned sp) ->
    rw_cells usegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->      (* [comment removed for export] *)
    rw_cells usegs m 0x350bd8 [C4 z64] ->                                              (* [comment removed for export] *)
    rw_cells usegs m 0x31c498 [C8 (Z_to_bv 64 0x2c0650); C8 (Z_to_bv 64 0x2c0640)] ->    (* [comment removed for export] *)
    rw_cells usegs m 0x2c0640 [C8 (Z_to_bv 64 0xe1528); C8 (Z_to_bv 64 0xe1c74)] ->   (* [comment removed for export] *)
    rw_cells usegs m 0x32de20 [C1 bi] -> rw_cells usegs m 0x32de24 [C1 (Z_to_bv 8 0)] ->   (* [comment removed for export] *)
    rw_cells usegs m 0x31dde8 [C1 (Z_to_bv 8 0)] ->                                    (* [comment removed for export] *)
    rw_cells usegs m 0x31bec0 [C8 (Z_to_bv 64 RCXA_FINALIZE); C8 z64] ->               (* [comment removed for export] *)
    rw_cells usegs m 0x350bf8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells usegs m 0x351030 [C8 z64] -> rw_cells usegs m 0x31dc88 [C8 (Z_to_bv 64 RSTDIN)] -> stdin_file m ->
    rw_cells usegs m 0x31dd78 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells usegs m 0x31db98 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m (get_so s) -> stderr_file m ->
    rw_cells usegs m 0x31c468 [C8 (Z_to_bv 64 0x3509a8)] -> rw_cells usegs m 0x3509a8 [C8 guard] ->
    mem_inv usegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 176)%Z -> (0x353000 <= lo)%Z ->
    AXSTAT k m ->                                                                      (* [comment removed for export] *)
    rw_cells usegs m RDSO [C8 (Z_to_bv 64 RDSO)] ->                                    (* [comment removed for export] *)
    implM usegs (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x2b06f8) fc None m (seg_rom usegs)).
  Proof.
    intros until bi. intros ST TDa EXL GF FA BI CF0 FIN GCX LCH OFL SIN SINF SOU SEU SOF SEF GG GU MI -> -> Ht LO LOLO AX DSO.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    (* [comment removed for export] *)
    destruct SOF as (flg & mode & tail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
    destruct SEF as (flg' & mode' & ee & wend' & tail' & SEF1).
    destruct SINF as (ij0 & ij1 & ij2 & ij3 & ij4 & SINC).
    unfold file_cells in SOF1, SEF1.
    unfold Driver.exit_model.
    eapply (implM_bind usegs _ _ s
              (fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
                 ms' = MS (mkR (Z_to_bv 64 0x2b0764) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x2b0764) fc None m' (seg_rom usegs))).
    - (* [comment removed for export] *)
      change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
      unfold implM. iprefix.
      call exit_prefix_spec; [exact ST | exact TDa | exact EXL | exact GF | exact FA | exact BI | exact CF0 | exact FIN | exact GCX | exact MI
                              | reflexivity | reflexivity | lia | lia | lia | exact LCH | exact AX | exact DSO | ].
      name_sp sp (-16)%Z.
      pose proof stdio_exit_spec as SE. unfold stdio_exit_spec_stmt, implM in SE.
      apply evt_done. eapply impl_epost_mono; [eapply SE|].
      all: lazymatch goal with
           | |- forall _, _ =>
               intros [[] s'] ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
               destruct_exs PO; destruct PO as (E & PO); subst ms'; cbn [fst snd];
               replace (ret_pc (Z_to_bv 64 0x2b0764)) with (Z_to_bv 64 0x2b0764) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
               repeat eexists; cbv delta [mkR]; reflexivity
           | |- stdout_file _ _ => exists flg, mode, tail, bufb; exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6)))))
           | |- stderr_file _ => exists flg', mode', ee, wend', tail'; exact SEF1
           | |- stdin_file _ => exists ij0, ij1, ij2, ij3, ij4; exact SINC
           | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | lia ]
           end.
    - (* [comment removed for export] *)
      clear SOF1 SOF2 SOF3 SOF4 SOF5 SOF6 SEF1.
      intros [] s' ms' PO. destruct_exs PO. subst ms'.
      apply implM_sys. do 4 lstep. step_ecall.
      split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
  Qed.
End ExitProof.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition at_exit {St : Type} (get_so : St -> stdout_st) (code : Z) (s : St) (ms : machine_state) : Prop :=
  exists (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo t : Z) (td0 td1 td2 td3 guard : word)
         (cdt thr sec : byte) (tm1 : word) (k : bool),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2b06f8) fc None m (seg_rom usegs)
    /\ stk usegs m lo (bv_unsigned sp)
    /\ rw_cells usegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
    /\ rw_cells usegs m 0x350bd8 [C4 z64]
    /\ rw_cells usegs m 0x31c498 [C8 (Z_to_bv 64 0x2c0650); C8 (Z_to_bv 64 0x2c0640)]
    /\ rw_cells usegs m 0x2c0640 [C8 (Z_to_bv 64 0xe1528); C8 (Z_to_bv 64 0xe1c74)]
    /\ (exists bi : byte, rw_cells usegs m 0x32de20 [C1 bi]) /\ rw_cells usegs m 0x32de24 [C1 (Z_to_bv 8 0)]
    /\ rw_cells usegs m 0x31dde8 [C1 (Z_to_bv 8 0)]
    /\ rw_cells usegs m 0x31bec0 [C8 (Z_to_bv 64 RCXA_FINALIZE); C8 z64]
    /\ rw_cells usegs m 0x350bf8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
    /\ rw_cells usegs m 0x351030 [C8 z64] /\ rw_cells usegs m 0x31dc88 [C8 (Z_to_bv 64 RSTDIN)] /\ stdin_file m
    /\ rw_cells usegs m 0x31dd78 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells usegs m 0x31db98 [C8 (Z_to_bv 64 RSTDERR)]
    /\ stdout_file m (get_so s) /\ stderr_file m
    /\ rw_cells usegs m 0x31c468 [C8 (Z_to_bv 64 0x3509a8)] /\ rw_cells usegs m 0x3509a8 [C8 guard]
    /\ mem_inv usegs m
    /\ tp = Z_to_bv 64 RTP /\ a0 = Z_to_bv 64 code
    /\ (0 < t < 4194304)%Z /\ (lo <= bv_unsigned sp - 176)%Z /\ (0x353000 <= lo)%Z
    /\ AXSTAT k m /\ rw_cells usegs m RDSO [C8 (Z_to_bv 64 RDSO)].                 (* [comment removed for export] *)

Lemma exit_from_at_exit {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St) :
  stdio_exit_spec_stmt get_so set_so ->
  forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop) code ms,
    at_exit get_so code s ms -> implM usegs (Driver.exit_model (io_S get_so set_so) code) s Q ms.
Proof.
  intros STDIO_EXIT s Q code ms H.
  destruct H as (ra & sp & gp & tp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 &
                 s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & lo & t &
                 td0 & td1 & td2 & td3 & guard & cdt & thr & sec & tm1 & k & -> & H).
  destruct H as (ST & TD & EXL & GF & FA & [bi BI] & CF0 & FIN & GCX & LCH & OFL & SIN & SINF & SOU & SEU & SOF & SEF & GG & GU & MI & Htp & Ha0 & Ht & LO & LOLO & AX & DSO).
  eapply (exit_spec get_so set_so STDIO_EXIT s Q);
    [exact ST | exact TD | exact EXL | exact GF | exact FA | exact BI | exact CF0 | exact FIN | exact GCX | exact LCH | exact OFL | exact SIN | exact SINF | exact SOU | exact SEU | exact SOF | exact SEF | exact GG | exact GU | exact MI | exact Htp | exact Ha0 | exact Ht | exact LO | exact LOLO | exact AX | exact DSO].
Qed.

(* [comment removed for export] *)
Lemma impl_msys_of_enode : forall segs {St A} (n : node) (pl : resp -> option A) (Q : A -> machine_state -> Prop) (s : St) ms,
  impl segs (at_node segs) (enode n pl) (epost Q) ms ->
  impl segs (at_node segs) (Monad.msys n pl s) (epost (fun p ms' => Q (fst p) ms' /\ snd p = s)) ms.
Proof.
  intros segs St A n pl Q s ms H. unfold Monad.msys, enode in *. cbn in *.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn in *; [|exact Hk].
  eapply evt_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
Qed.
