(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Malloc Require Import InitMem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Startup_lib.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Stdio_base Printf_lib Startup RefImpl F_printf_iface Stdio_iface Stdio_init F_printf_diag RDriver_lib RDriver_kit RDriver_ctx RF_main_A.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Segs RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Segs F_memset F_memcpy F_strlen.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
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

Definition S_OOM : Z := 0x1038b.    Definition s_oom : list Z := (str "cli: out of memory"%string ++ [10])%list.
Definition S_SHORT : Z := 0x1069b.  Definition s_short : list Z := (str "cli: input shorter than header"%string ++ [10])%list.
Definition S_OVER : Z := 0x103f5.   Definition s_over : list Z := (str "cli: config_len overruns input"%string ++ [10])%list.
Lemma s_oom_ro : ro_bytes_b rsegs S_OOM (zb s_oom) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s_short_ro : ro_bytes_b rsegs S_SHORT (zb s_short) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s_over_ro : ro_bytes_b rsegs S_OVER (zb s_over) = true. Proof. vm_compute. reflexivity. Qed.

Lemma rodata_bytes : forall m A (s : list Z),
  mem_inv rsegs m -> ro_bytes_b rsegs A (zb s) = true -> 0x10000 <= A -> A + zlength s <= 0x5d000 ->
  bytes_at rsegs m A (zb s).
Proof.
  intros m A s MI RO LO HI. apply ro_bytes_at; [exact MI| lia| rewrite zb_length; unfold zlength in HI; lia| apply (ro_bytes_b_sound rsegs); exact RO].
Qed.

Lemma str_range : forall s, Forall (fun c => 0 <= c < 256) (str s).
Proof.
  intros s. unfold str. induction (list_ascii_of_string s) as [|a l IH]; cbn; constructor; [| exact IH].
  pose proof (Ascii.N_ascii_bounded a). lia.
Qed.

Lemma implM_get_bind : forall {A} (f : PState -> M PState A) s Q ms,
  implM rsegs (f s) s Q ms -> implM rsegs (mbind mget f) s Q ms.
Proof. intros A f s Q ms H. unfold implM, mbind, mget in *. cbn. exact H. Qed.
Lemma implM_mret_bind : forall {A B} (a : A) (f : A -> M PState B) s Q ms,
  implM rsegs (f a) s Q ms -> implM rsegs (mbind (mret a) f) s Q ms.
Proof. intros A B a f s Q ms H. unfold implM, mbind, mret in *. cbn. exact H. Qed.

Section B.
  Context {HGW : HasGuard} {HCEIL : HasCeiling}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte) (TID : Z)
            (MPAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis EXK : exit_k_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.
  Hypothesis TOW : towrite_stmt.

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid hw rnd TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm MPAD S7 S6 S5 S4).
  Ltac hyps := first [exact VSP | exact CEIL | exact VARGV | exact VENVP | exact EARGV | exact HT | exact MALLOC | exact FREE | exact FPR | exact EXK | exact FWR | exact TOW].

  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  Definition BUF (mm : mem) (s : PState) (bufp : bptr) (A cap : Z) (DATA junk : list byte) : Prop :=
    RHEAP s [(bufp, A, cap)] mm /\ ps_fa s = (0, 0) /\ ps_so s = stdout_init
    /\ rw_cells rsegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
    /\ (65536 <= cap <= MAX_INPUT /\ exists k, 0 <= k /\ cap = 2 ^ k) /\ Z.of_nat (length DATA) <= cap /\ rblock_range A cap.

  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 RSV) (Z_to_bv 64 x23) t3 t4 t5 t6 F fc mm).

  Definition rd_pc (st : rd_st (ptr:=bptr)) : Z := if zlength (rd_content st) =? rd_cap st then 0x13bb0 else 0x13ba8.

  Definition RDINV (fd P1v : Z) (st : rd_st) (s : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (A : Z) (DATA junk : list byte) (errv : word),
      ms = RST (rd_pc st) x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength (rd_content st)) fd (rd_cap st) A t3 t4 t5 t6 F fc mm
      /\ rd_content st = map bv_unsigned DATA
      /\ BUF mm s (rd_buf st) A (rd_cap st) DATA junk
      /\ FRAME' mm /\ BASE' mm /\ CJ0 mm /\ rw_cells rsegs mm RERRNO [C4 errv] /\ frm0 fc.

  Definition RDBRK (fd P1v : Z) (bufp : bptr) (content : list Z) (s : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (A cap : Z) (DATA junk : list byte) (errv : word),
      ms = RST 0x13c10 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength content) fd cap 0 t3 t4 t5 t6 F fc mm
      /\ content = map bv_unsigned DATA
      /\ BUF mm s bufp A cap DATA junk
      /\ FRAME' mm /\ BASE' mm /\ CJ0 mm /\ rw_cells rsegs mm RERRNO [C4 errv] /\ frm0 fc.

  Definition POSTBODY (fd P1v : Z) (r : rd_st + rd_result) (s : PState) (ms : machine_state) : Prop :=
    match r with
    | inl st' => RDINV fd P1v st' s ms
    | inr RdExit => rat_exit 2 s ms
    | inr (RdDone b c) => RDBRK fd P1v b c s ms
    end.

  Notation ioS := (io_S ps_so set_so_ps).
  Definition rd_read_part (fd : Z) (path : list Z) (st1 : rd_st (ptr:=bptr)) : M PState (rd_st + rd_result) :=
    let len := zlength (rd_content st1) in
    let cnt := Z.min (rd_cap st1 - len) READ_CHUNK in
    a <- msys (NRead fd RSV cnt) (dec_read RSV cnt) ;;
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
    read_loop_body ioS raw_malloc raw_free RSV fd path st
    = (g <- rd_grow_part st ;; match g with None => mret (inr RdExit) | Some st1 =>
         let cnt := Z.min (rd_cap st1 - zlength (rd_content st)) READ_CHUNK in
         a <- msys (NRead fd RSV cnt) (dec_read RSV cnt) ;;
         match a with
         | RdErr _ => io_diag ioS (DReadError path) ;;; mret (inr RdExit)
         | RdData bs =>
             if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
             else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
         end end).
  Proof. intros. reflexivity. Qed.

  Definition diag_of_pdiag (d : pdiag) : diag_msg :=
    match d with PDUsage a => DUsage a | PDCannotOpen p => DCannotOpen p | PDReadError p => DReadError p | PDTooBig => DTooBig end.
  #[using="Type"] Lemma s_diag_pdiag : forall d, io_diag ioS (diag_of_pdiag d) = stderr_fprintf (pdiag_pieces d).
  Proof. intros []; reflexivity. Qed.

  #[using="VSP CEIL HT FPR"] Lemma fprintf_exit : forall (d : pdiag) {R} (K : M PState R) (Q : R -> PState -> machine_state -> Prop) (s : PState) (LB : list block)
      x1 t0 t1 t2 x9 (a1v a2v : word) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    diag_args d mm a1v a2v (usp0 - 8388608) (usp0 - 128) ->
    BASE' mm -> RHEAP s LB mm -> ps_so s = stdout_init -> frm0 fc ->
    (forall ms', rat_exit 2 s ms' -> implM rsegs K s Q ms') ->
    implM rsegs (io_diag ioS (diag_of_pdiag d) ;;; K) s Q
      (GST 0x13d7c x1 t0 t1 t2 x9 (Z_to_bv 64 0x2b480) a1v a2v x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros DA BA HP SO FRM HK. rewrite s_diag_pdiag.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & RSS). unfold LO in ST.
    unfold implM. iprefix. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s Q msx) end.
    eapply implM_bind.
    { eapply (FPR d) with (lo := usp0 - 8388608) (canary := guard_word);
        [apply stderr_wfile0_wfile; exact SE| reflexivity| rewrite unsigned_lit by lia; replace (usp0 + -128) with (usp0 - 128) by lia; exact DA
        | rewrite unsigned_lit by lia; exact ST
        | rewrite unsigned_lit by lia; unfold FPRINTF_DEPTH; lia| unfold GLOBALS_TOP; lia| rewrite unsigned_lit by lia; lia
        | apply (RHEAP_ssp _ _ _ HP)| exact MI| exact FRM]. }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m2 & -> & MUc & WMc & MI2 & FRM2 & FEQ & ST2 & SEW & SSP2 & ->).
    ua. rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x13d80)) with (Z_to_bv 64 0x13d80) by (symmetry; rpc).
    pose proof (agree_on_of_munch rsegs _ _ _ MUc WMc) as AG.
    assert (OUT2 : forall a, (0x10000 <= a < 0x5d000 /\ ~ (0x2b480 <= a < 0x2b480 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x2b480, 0x2b480 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    eapply implM_evt; [| intros ms'' H; apply HK; exact H].
    zstep.
    eapply (exit2_tail sp0 TID VSP CEIL HT s LB).
    - unfold LO. replace (usp0 - 8388608) with (usp0 + -8388608) in ST2 by lia. first [exact ST2 | replace (usp0 + -8388608) with (usp0 - 8388608) in ST2 by lia; exact ST2].
    - eapply (RSTAT_agree TID _ _ _ AG); [intros a Ha; apply OUT2; unfold rstat_addr in Ha; lia| exact RS].
    - eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MUc| exact WMc|].
      constructor; [left; cbn [fst snd]; lia|]. constructor; [| constructor].
      right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK. lia.
    - rewrite SO. eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT2; unfold stdout_addr in Ha; lia| exact SOF].
    - apply stderr_wfile_file. exact SEW.
    - exact MI2.
  Qed.

  #[using="VSP CEIL HT FWR TOW"] Lemma fwrite_exit : forall {R} (K : M PState R) (Q : R -> PState -> machine_state -> Prop) (s : PState) (LB : list block)
      x1 t0 t1 t2 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    BASE' mm -> RHEAP s LB mm -> ps_so s = stdout_init ->
    (forall ms', rat_exit 2 s ms' -> implM rsegs K s Q ms') ->
    implM rsegs (io_diag ioS DOom ;;; K) s Q
      (GST 0x13da0 x1 t0 t1 t2 x9 (Z_to_bv 64 S_OOM) (Z_to_bv 64 19) (Z_to_bv 64 1) (Z_to_bv 64 0x2b480) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros BA HP SO HK.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & RSS). unfold LO in ST.
    unfold implM. iprefix. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s Q msx) end.
    cbn [io_diag io_S s_diag]. change (concat pieces_oom) with s_oom.
    eapply implM_bind.
    { eapply (FWR) with (lo := usp0 - 8388608) (canary := guard_word) (s := s_oom);
        [exact TOW| exact SE| rewrite unsigned_lit by (unfold S_OOM; lia); apply rodata_bytes; [exact MI| apply s_oom_ro| unfold S_OOM; lia| unfold S_OOM, s_oom, zlength; cbn; lia]
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
    replace (ret_pc (Z_to_bv 64 0x13da4)) with (Z_to_bv 64 0x13da4) by (symmetry; rpc).
    pose proof (agree_on_of_munch rsegs _ _ _ MUc WMc) as AG.
    assert (OUT2 : forall a, (0x10000 <= a < 0x5d000 /\ ~ (0x2b480 <= a < 0x2b480 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x2b480, 0x2b480 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    eapply implM_evt; [| intros ms'' H; apply HK; exact H].
    eapply (exit2_tail sp0 TID VSP CEIL HT s LB).
    - unfold LO. replace (usp0 - 8388608) with (usp0 + -8388608) in ST2 by lia. first [exact ST2 | replace (usp0 + -8388608) with (usp0 - 8388608) in ST2 by lia; exact ST2].
    - eapply (RSTAT_agree TID _ _ _ AG); [intros a Ha; apply OUT2; unfold rstat_addr in Ha; lia| exact RS].
    - eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MUc| exact WMc|].
      constructor; [left; cbn [fst snd]; lia|]. constructor; [| constructor].
      right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK. lia.
    - rewrite SO. eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT2; unfold stdout_addr in Ha; lia| exact SOF].
    - apply stderr_wfile0_file. exact SEW.
    - exact MI2.
  Qed.
End B.
