(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree Startup_kit STRW_tac F_fmt_fp_lib Printf_fmts.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg F_syscalls StdioFiles Startup Exit F_printf_iface Stdio_iface.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_facts RDriver_kit RDriver_ctx RF_main_A.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ua := idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       end).
Ltac zst := zstep; fix_lit_store.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition S_OOM : Z := 0x102b5.    Definition s_oom : list Z := (str "cli: out of memory"%string ++ [10])%list.
Definition S_SHORT : Z := 0x1035e.  Definition s_short : list Z := (str "cli: input shorter than header"%string ++ [10])%list.
Definition S_OVER : Z := 0x102e1.   Definition s_over : list Z := (str "cli: config_len overruns input"%string ++ [10])%list.
#[using="Type"] Lemma s_oom_ro : ro_bytes_b usegs S_OOM (zbytes s_oom) = true. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma s_short_ro : ro_bytes_b usegs S_SHORT (zbytes s_short) = true. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma s_over_ro : ro_bytes_b usegs S_OVER (zbytes s_over) = true. Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma rodata_bytes : forall m A (s : list Z),
  mem_inv usegs m -> ro_bytes_b usegs A (zbytes s) = true -> 0x10000 <= A -> A + zlength s <= 0x4f000 ->
  bytes_at usegs m A (zbytes s).
Proof.
  intros m A s MI RO LO HI. apply ro_bytes_at; [exact MI| lia| rewrite zbytes_length; unfold zlength in HI; lia| apply (ro_bytes_b_sound usegs); exact RO].
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma stderr_file0_wfile0 : forall m, stderr_file0 m -> stderr_wfile0 m.
Proof.
  intros m H. exists (Z_to_bv 64 5), (wz 0), 0, 0, (repeat (Z_to_bv 8 0) 80). split; [exact H|].
  split; [vm_compute; reflexivity|]. Local Ltac2 Set LiaHints.tbl := fun () => "0010=50083006106.3000001S".
split; [left; reflexivity| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma stderr_wfile0_agree : forall (P : Z -> Prop) m m',
  magree usegs P m m' -> (forall a, stderr_addr a -> P a) -> stderr_wfile0 m -> stderr_wfile0 m'.
Proof.
  intros P m m' AG HP (flags & mode & e & wend & tail & F1 & F2 & F3 & F4).
  exists flags, mode, e, wend, tail. split; [| split; [exact F2| split; [exact F3| exact F4]]].
  eapply rw_cells_magree; [exact AG| exact F1|]. intros a Ha. apply HP. unfold stderr_addr. cbn in Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0010>46430868464.17000004S2Ha".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma stderr_wfile0_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> stderr_wfile0 m -> stderr_wfile0 m'.
Proof.
  intros LB SP m m' HP. apply (stderr_wfile0_agree _ _ _ HP). intros a Ha. right; left.
  unfold stderr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010=32162264840.8000004S2Ha".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma stderr_wfile0_munch : forall W m m', munch W m m' -> wmono usegs m m' -> (forall a, stderr_addr a -> outside W a) -> stderr_wfile0 m -> stderr_wfile0 m'.
Proof. intros W m m' MU WM HW. apply (stderr_wfile0_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.

#[using="Type"] Lemma str_range : forall s, Forall (fun c => 0 <= c < 256) (str s).
Proof.
  intros s. unfold str. induction (list_ascii_of_string s) as [|a l IH]; cbn; constructor; [| exact IH].
  pose proof (Ascii.N_ascii_bounded a). Local Ltac2 Set LiaHints.tbl := fun () => "0010=10316425019.6000003S1H".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma implM_get_bind : forall {A} (f : PState -> M PState A) s Q ms,
  implM usegs (f s) s Q ms -> implM usegs (mbind mget f) s Q ms.
Proof. intros A f s Q ms H. unfold implM, mbind, mget in *. cbn. exact H. Qed.
#[using="Type"] Lemma implM_mret_bind : forall {A B} (a : A) (f : A -> M PState B) s Q ms,
  implM usegs (f a) s Q ms -> implM usegs (mbind (mret a) f) s Q ms.
Proof. intros A B a f s Q ms H. unfold implM, mbind, mret in *. cbn. exact H. Qed.

Section B.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (arg0 arg1 : list byte) (TID : Z)
            (J8 : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : dvalid_sp sp0 argv envp.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWX : fwritex_stderr_stmt.
  Hypothesis SWF : stdio_write_flush_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.
  Hypothesis TOW : towrite_stmt.

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes pph sp0 argv envp uid hw draw).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid hw draw TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm J8 S7 S6 S5 S4).
  Ltac hyps := first [exact VSP | exact VARGV | exact VENVP | exact EARGV | exact HT | exact MALLOC | exact FREE | exact FPR | exact FWX | exact SWF | exact FWR | exact TOW].

  (* [comment removed for export] *)
  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition BUF (mm : mem) (s : PState) (bufp : bptr) (A cap : Z) (DATA junk : list byte) : Prop :=
    RHEAP s [(bufp, A, cap)] mm /\ ps_fa s = tt /\ ps_so s = stdout_init /\ True
    /\ rw_cells usegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
    /\ (65536 <= cap <= MAX_INPUT /\ exists k, 0 <= k /\ cap = 2 ^ k) /\ Z.of_nat (length DATA) <= cap /\ rblock_range A cap.

  (* [comment removed for export] *)
  Definition STAGE (mm : mem) (sj : list byte) : Prop := rw_cells usegs mm UREAD_STAGE [CB PSTAGE_LEN sj].

  (* [comment removed for export] *)
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 UREAD_STAGE) x23 t3 t4 t5 t6 F fc mm).

  (* [comment removed for export] *)
  Definition RDINV (fd P1v : Z) (st : rd_st) (s : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (A : Z) (DATA junk : list byte) (errv : word) (sj : list byte) (pc : Z),
      ms = RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength (rd_content st)) fd (rd_cap st) (Z_to_bv 64 A) t3 t4 t5 t6 F fc mm
      /\ ((pc = 0x12874 /\ x9 = Z_to_bv 64 A) \/ (pc = 0x12854 /\ rd_content st = []))
      /\ rd_content st = map bv_unsigned DATA
      /\ BUF mm s (rd_buf st) A (rd_cap st) DATA junk /\ STAGE mm sj
      /\ FRAME' mm /\ BASE' mm /\ rw_cells usegs mm RERRNO [C4 errv] /\ frm0 fc.

  (* [comment removed for export] *)
  Definition RDBRK (fd P1v : Z) (bufp : bptr) (content : list Z) (s : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x23 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (A cap : Z) (DATA junk : list byte) (errv : word),
      ms = RST 0x128e0 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength content) fd cap x23 t3 t4 t5 t6 F fc mm
      /\ content = map bv_unsigned DATA
      /\ BUF mm s bufp A cap DATA junk
      /\ FRAME' mm /\ BASE' mm /\ rw_cells usegs mm RERRNO [C4 errv] /\ frm0 fc.

  Definition POSTBODY (fd P1v : Z) (r : rd_st + rd_result) (s : PState) (ms : machine_state) : Prop :=
    match r with
    | inl st' => RDINV fd P1v st' s ms
    | inr RdExit => pat_exit 2 s ms
    | inr (RdDone b c) => RDBRK fd P1v b c s ms
    end.

  (* [comment removed for export] *)
  Notation ioS := Prog.io.
  Definition rd_read_part (fd : Z) (path : list Z) (st1 : rd_st (ptr:=bptr)) : M PState (rd_st + rd_result (ptr:=bptr)) :=
    let len := zlength (rd_content st1) in
    let want0 := rd_cap st1 - len in
    let cnt := if 65536 <? want0 then 65536 else want0 in
    a <- msys (NRead fd UREAD_STAGE cnt) (dec_read UREAD_STAGE cnt) ;;
    match a with
    | RdErr _ => io_diag ioS (DReadError path) ;;; mret (inr RdExit)
    | RdData bs =>
        if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
        else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
    end.

  Definition rd_grow_part (st : rd_st) : M PState (option rd_st) :=
    if zlength (rd_content st) =? rd_cap st then
      if MAX_INPUT <=? rd_cap st then io_diag ioS DTooBig ;;; mret None
      else
        nb <- raw_malloc (rd_cap st * 2) ;;
        match nb with
        | None => io_diag ioS DOom ;;; mret None
        | Some nb' => raw_free (rd_buf st) ;;; mret (Some (mkRd nb' (rd_cap st * 2) (rd_content st)))
        end
    else mret (Some st).

  #[using="Type"] Lemma read_loop_body_eq : forall fd path st,
    read_loop_body ioS raw_malloc raw_free UREAD_STAGE fd path st
    = (g <- rd_grow_part st ;; match g with None => mret (inr RdExit) | Some st1 =>
         let want0 := rd_cap st1 - zlength (rd_content st) in
         let cnt := if 65536 <? want0 then 65536 else want0 in
         a <- msys (NRead fd UREAD_STAGE cnt) (dec_read UREAD_STAGE cnt) ;;
         match a with
         | RdErr _ => io_diag ioS (DReadError path) ;;; mret (inr RdExit)
         | RdData bs =>
             if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
             else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
         end end).
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="VSP HT FPR FWX SWF"] Lemma fprintf_exit : forall (d : diag_msg) {R} (K : M PState R) (Q : R -> PState -> machine_state -> Prop) (s : PState) (LB : list block)
      x1 t0 t1 t2 x9 (a1v a2v : word) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    diag_args d mm a1v a2v (usp0 - 8388608) (usp0 - 128) ->
    BASE' mm -> RHEAP s LB mm -> ps_so s = stdout_init -> frm0 fc ->
    (forall ms', pat_exit 2 s ms' -> implM usegs K s Q ms') ->
    implM usegs (s_diag d ;;; K) s Q
      (GST 0x12a4c x1 t0 t1 t2 x9 (Z_to_bv 64 0x1dcf8) a1v a2v x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros DA BA HP SO FRM HK.
    pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & TR). unfold LO in ST.
    unfold implM. iprefix. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s Q msx) end.
    eapply implM_bind.
    { Local Ltac2 Set LiaHints.tbl := fun () => "00<0?16800608486.10617381815389.10617834302352.10424361825921.78 25546104465.78 49364486404.10655404301650.78 56323174152.78 57614170466.10766026193812.10466026193812.78 6667549001.108 00000100200300700800<00=00A00H00L00P00TSSSS2SFSS2SFSS2SFS2SF2HaS2SFS2SFS2Ha".
eapply (FPR d) with (lo := usp0 - 8388608) (canary := CAN);
        [exact FWX| exact SWF| apply stderr_file0_wfile; exact SE| reflexivity| rewrite unsigned_lit by lia; replace (usp0 + -128) with (usp0 - 128) by lia; exact DA
        | rewrite unsigned_lit by lia; exact ST
        | rewrite unsigned_lit by lia; unfold FPRINTF_DEPTH; lia| unfold GLOBALS_TOP; lia| rewrite unsigned_lit by lia; lia
        | apply (RHEAP_ssp _ _ _ HP)| exact MI| exact FRM]. }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m2 & -> & MUc & WMc & MI2 & FRM2 & FEQ & ST2 & SEW & SSP2 & ->).
    ua. rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x12a50)) with (Z_to_bv 64 0x12a50) by (symmetry; rpc).
    pose proof (magree_of_munch usegs _ _ _ MUc WMc) as AG.
    assert (OUT2 : forall a, (0x10000 <= a < 0x4f000 /\ ~ (0x1dcf8 <= a < 0x1dcf8 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x1dcf8, 0x1dcf8 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    eapply implM_evt; [| intros ms'' H; apply HK; exact H].
    zstep.
    eapply (exit2_tail sp0 argv envp TID VSP HT s LB).
    - unfold LO. replace (usp0 - 8388608) with (usp0 + -8388608) in ST2 by lia. first [exact ST2 | replace (usp0 + -8388608) with (usp0 - 8388608) in ST2 by lia; exact ST2].
    - eapply (RSTAT_agree TID _ _ _ AG); [intros a Ha; apply OUT2; unfold rstat_addr in Ha; lia| exact RS].
    - eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MUc| exact WMc|].
      constructor; [left; cbn [fst snd]; atop_facts; lia|]. constructor; [| constructor].
      right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia.
    - rewrite SO. eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT2; unfold stdout_addr in Ha; lia| exact SOF].
    - apply stderr_wfile_file. exact SEW.
    - exact MI2.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="VSP HT FWR TOW"] Lemma fwrite_exit : forall {R} (K : M PState R) (Q : R -> PState -> machine_state -> Prop) (s : PState) (LB : list block)
      x1 t0 t1 t2 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    BASE' mm -> RHEAP s LB mm -> ps_so s = stdout_init ->
    (forall ms', pat_exit 2 s ms' -> implM usegs K s Q ms') ->
    implM usegs (s_diag DOom ;;; K) s Q
      (GST 0x12a70 x1 t0 t1 t2 x9 (Z_to_bv 64 S_OOM) (Z_to_bv 64 19) (Z_to_bv 64 1) (Z_to_bv 64 0x1dcf8) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros BA HP SO HK.
    pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & TR). unfold LO in ST.
    unfold implM. iprefix. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s Q msx) end.
    cbn [s_diag]. change (concat pieces_oom) with s_oom.
    eapply implM_bind.
    { Local Ltac2 Set LiaHints.tbl := fun () => "00C0>16800608486.9617381815389.961884925113.72 23757625104.9424361825921.7228478377432.7230500528912.7231283991625.7232059271057.7240811235735.7242832693700.7243441166616.7249364486404.9656323174152.7257614170466.9766026193812.7266026193812.946667549001.98 68907608.72   00000100200300400800900:00;00<00=00>00?00C00G00N00R00V00Z00^SSSSS2SFSSSSSSSS2SFS2SFS2SF2HaS2SFS2SFS2HaS2SF".
eapply (FWR) with (lo := usp0 - 8388608) (canary := CAN) (s := s_oom);
        [exact TOW| apply stderr_file0_wfile0; exact SE| rewrite unsigned_lit by (unfold S_OOM; lia); apply rodata_bytes; [exact MI| apply s_oom_ro| unfold S_OOM; lia| unfold S_OOM, s_oom, zlength; cbn; lia]
        | apply str_range || (unfold s_oom; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]])
        | unfold s_oom, zlength; cbn; lia| reflexivity| reflexivity| reflexivity
        | rewrite unsigned_lit by lia; exact ST
        | rewrite unsigned_lit by lia; unfold FWRITE_DEPTH; lia| unfold GLOBALS_TOP; lia
        | rewrite unsigned_lit by lia; lia
        | rewrite !unsigned_lit by (unfold S_OOM; lia); unfold S_OOM, s_oom, zlength; cbn; lia
        | rewrite !unsigned_lit by (unfold S_OOM; lia); unfold S_OOM, s_oom, zlength; cbn; lia
        | rewrite !unsigned_lit by (unfold S_OOM; lia); unfold S_OOM, s_oom, zlength; cbn; lia
        | apply (RHEAP_ssp _ _ _ HP)| exact MI]. }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MI2 & ST2 & SEW & SSP2 & ->).
    ua. rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x12a74)) with (Z_to_bv 64 0x12a74) by (symmetry; rpc).
    pose proof (magree_of_munch usegs _ _ _ MUc WMc) as AG.
    assert (OUT2 : forall a, (0x10000 <= a < 0x4f000 /\ ~ (0x1dcf8 <= a < 0x1dcf8 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x1dcf8, 0x1dcf8 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    eapply implM_evt; [| intros ms'' H; apply HK; exact H].
    eapply (exit2_tail sp0 argv envp TID VSP HT s LB).
    - unfold LO. replace (usp0 - 8388608) with (usp0 + -8388608) in ST2 by lia. first [exact ST2 | replace (usp0 + -8388608) with (usp0 - 8388608) in ST2 by lia; exact ST2].
    - eapply (RSTAT_agree TID _ _ _ AG); [intros a Ha; apply OUT2; unfold rstat_addr in Ha; lia| exact RS].
    - eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MUc| exact WMc|].
      constructor; [left; cbn [fst snd]; atop_facts; lia|]. constructor; [| constructor].
      right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia.
    - rewrite SO. eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT2; unfold stdout_addr in Ha; lia| exact SOF].
    - apply stderr_wfile0_file. exact SEW.
    - exact MI2.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End B.
End CANSEC1.
