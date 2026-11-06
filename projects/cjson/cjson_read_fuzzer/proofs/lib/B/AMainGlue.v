(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require StepTac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kitL.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require SO_base.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Drv_base.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Drv_icpt_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Drv_dicpt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require DrvTop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require MainExport.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AMainEntry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AEntryLib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require BothPlanImages.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module AEntry.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kitL OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.SO_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Drv_icpt_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Drv_dicpt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.DrvTop.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.MainExport.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AMainEntry.MainFactsBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AMainEntry.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AEntryLib.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation BPH := AsanUbsan.M.phdrs (only parsing).
Local Notation wz := (Z_to_bv 64) (only parsing).
Local Notation zb := (Z_to_bv 8) (only parsing).

Lemma find_segment_in : forall segs a n s, find_segment segs a n = Some s ->
  In s segs /\ Z.of_N (seg_base s) <= a /\ a + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  induction segs as [|s0 r IH]; intros a n s H; cbn [find_segment] in H; [discriminate|].
  destruct ((Z.of_N (seg_base s0) <=? a) && (a + n <=? Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool eqn:E.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. split; [left; reflexivity| lia].
  - destruct (IH _ _ _ H) as (Hin & Hr). split; [right; exact Hin| exact Hr].
Qed.

Module F := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.
Module CE := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.WallSim.CatExec.
Module RL := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.RefLayout.
Module FS := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.FileSim.

(* [comment removed for export] *)
Lemma rdn_flat : forall segs mm a n, F.rdn segs mm a n = rdn segs mm a n.
Proof. intros segs mm a n. revert a. induction n as [|n IH]; intros a; [reflexivity|]. cbn [rdn F.rdn]. rewrite IH. reflexivity. Qed.

Lemma rdn_bytes_at : forall segs mm (a : Z) bs,
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  rdn segs mm (wa a) (length bs) = Some bs -> bytes_at segs mm a bs.
Proof.
  intros segs mm a bs Ha Hb H. split; [exact Ha|]. split; [exact Hb|].
  revert a Ha Hb H. induction bs as [|b bs IH]; intros a Ha Hb H i Hi; [cbn in Hi; lia|].
  cbn [length] in Hb, Hi. rewrite rdn_unfold in H. cbn [length] in H.
  destruct (mrd segs mm (wa a)) as [b'|] eqn:Eb; [|discriminate].
  rewrite wa_succ in H.
  destruct (rdn segs mm (wa (a + 1)) (length bs)) as [r|] eqn:Er; [|discriminate].
  injection H as Hbb Hr. subst b' r.
  destruct i as [|i].
  - rewrite Z.add_0_r. exact Eb.
  - cbn [nth_error]. replace (a + Z.of_nat (S i)) with ((a + 1) + Z.of_nat i) by lia.
    apply (IH (a + 1)); [lia| lia| exact Er| lia].
Qed.

Lemma bytes_at_agree : forall segs (m1 m2 : word -> option byte) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> m2 (wa (a + i)) = m1 (wa (a + i))) ->
  bytes_at segs m1 a bs -> bytes_at segs m2 a bs.
Proof.
  intros segs m1 m2 a bs AG nelH_; (nelim nelH_ 3%nat; intros H1 H2 H). split; [exact H1|]. split; [exact H2|].
  intros i Hi. unfold mrd. rewrite (AG (Z.of_nat i)) by lia. apply H. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma pvar_find : forall V l k lo hi, Forall (pfact_ok V) l ->
  existsb (fun f => match f with PVar n l0 h0 => Nat.eqb n k && (lo <=? l0) && (h0 <=? hi) | _ => false end) l = true -> lo <= V k <= hi.
Proof.
  intros V l k lo hi HF HE. apply existsb_exists in HE as (f & Hin & Hf). destruct f as [n l0 h0| | |]; try discriminate.
  apply andb_prop in Hf as [Hf H3]. apply andb_prop in Hf as [H1 H2]. apply Nat.eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. subst n.
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as K. cbn [pfact_ok] in K. lia.
Qed.

(* [comment removed for export] *)
Lemma mzero_cover : forall segs V m l lo hi, Forall (mfact_ok segs V m) l ->
  existsb (fun f => match f with MZero (ZLit a0) n => (a0 <=? lo) && (hi <=? a0 + n) | _ => false end) l = true ->
  forall x, lo <= x < hi -> m (wa x) = Some (Z_to_bv 8 0).
Proof.
  intros segs V m l lo hi HF HE x Hx. apply existsb_exists in HE as (f & Hin & Hf). destruct f as [| | |a n| | | | |]; try discriminate.
  destruct a as [a0| | | | |]; try discriminate. apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as K. cbn [mfact_ok zv] in K.
  specialize (K (x - a0) ltac:(lia)). replace (a0 + (x - a0)) with x in K by lia. exact K.
Qed.

Section CeilWrap.
Context {ACEIL : Ceil}.

Section Entry.
  Variables (w : bool) (V : nat -> Z) (sp0 brk0 : word) (rdraw : EntryDraw) (argv envp : list (list byte)) (uid hw : word) (fs : Fs.Fs)
            (regs : bvmap 5 word) (m : word -> option byte) (mo : Model) (g : lghost).
  Hypothesis ME : a_main_entry w V sp0 brk0 rdraw argv envp uid hw fs regs m mo g.
  Hypothesis VA : valid_argv argv.
  Hypothesis VE : valid_envp envp.
  Hypothesis VSP : valid_sp sp0.
  Hypothesis VFIT : entry_stack_fits sp0 argv envp.
  Hypothesis HCEIL : alloc_ceiling = bv_unsigned sp0 - 8388608.

  Let usp := bv_unsigned sp0.

  Lemma usp_lo : 0x7fff80000000 <= usp.
  Proof. (nelimp VSP 3%nat; intros H _ _). unfold sp_window_lo in H. exact H. Qed.
  Lemma usp_hi : usp <= 0x800000000000.
  Proof. (nelimp VSP 3%nat; intros _ H _). unfold sp_window_hi in H. exact H. Qed.
  Lemma usp_al : usp mod 16 = 0.
  Proof. (nelimp VSP 3%nat; intros _ _ H). exact H. Qed.

  Lemma ME_vars : amain_vars V sp0 brk0 rdraw argv envp uid hw. Proof. exact (proj1 ME). Qed.
  Lemma ME_facts_w : Forall (mfact_ok bsegs V m) (both_mem_facts ++ both_mem_facts_w w). Proof. exact (proj1 (proj2 (proj2 ME))). Qed.
  Lemma ME_facts : Forall (mfact_ok bsegs V m) both_mem_facts. Proof. exact (proj1 (proj1 (Forall_app _ _ _) ME_facts_w)). Qed.
  Lemma ME_pure_w : Forall (pfact_ok V) (both_pure_facts ++ both_pure_facts_w w). Proof. exact (proj1 (proj2 (proj2 (proj2 ME)))). Qed.
  Lemma ME_pure : Forall (pfact_ok V) both_pure_facts. Proof. exact (proj1 (proj1 (Forall_app _ _ _) ME_pure_w)). Qed.
  Lemma ME_args : amain_args sp0 rdraw argv envp uid hw m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 ME))))). Qed.
  Lemma ME_model : amodel V sp0 fs mo. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 ME)))))). Qed.
  Lemma ME_top : forall a : word, 0x800000000000 <= bv_unsigned a -> m a = None.
  Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ME)))))))). Qed.

  Lemma usp_V : usp = 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat.
  Proof. (nelimp ME_vars 6%nat; intros _ _ _ _ H _). unfold IX_S1, IX_SP, IX_S2 in H. unfold usp. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma entry_pristine_ro : forall i, 0x10000 <= i < 0xa1000 -> m (wa i) = None.
  Proof. exact (mimg_cover bsegs V m both_mem_facts 0x10000 0xa1000 ME_facts ltac:(vm_compute; reflexivity)). Qed.

  Lemma entry_mem_inv : mem_inv bsegs m.
  Proof.
    apply mem_inv_intro. intros a b Hab.
    assert (Hlt : bv_unsigned a < TASK_SIZE).
    { destruct (Z.lt_ge_cases (bv_unsigned a) 0x800000000000) as [L|G]; [exact L|]. rewrite (ME_top a G) in Hab. discriminate. }
    split; [| right; exact Hlt].
    unfold ro_addr. destruct (find_segment bsegs (bv_unsigned a) 1) as [seg|] eqn:F; [|reflexivity].
    destruct (seg_writable seg) eqn:W; [reflexivity|]. exfalso.
    (nelim (find_segment_in _ _ _ _ F) 3%nat; intros Hin Hr1 Hr2).
    assert (Hro : 0x10000 <= bv_unsigned a < 0xa1000).
    { destruct (bsegs_In seg Hin) as [(B & S & _)|[(B & S & _)|[(_ & _ & X)|(_ & _ & X)]]]; try congruence; lia. }
    pose proof (entry_pristine_ro (bv_unsigned a) Hro) as N. unfold wa in N. rewrite Z_to_bv_bv_unsigned in N. congruence.
  Qed.

  (* [comment removed for export] *)
  Lemma entry_stk : stk bsegs m (usp - 8388608) usp.
  Proof.
    pose proof (mwr_find bsegs V m both_mem_facts
                  (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 8388608
                  ME_facts ltac:(vm_compute; reflexivity)) as W.
    cbn [zv] in W. replace (32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat) + -8388608) with (usp - 8388608) in W by (rewrite usp_V; lia).
    pose proof usp_lo as LO. pose proof usp_hi as HI.
    apply wr_at_stk; [replace (usp - (usp - 8388608)) with 8388608 by lia; exact W|].
    intros a Ha. destruct (find_segment bsegs a 1) as [seg|] eqn:F; [|reflexivity]. exfalso.
    (nelim (find_segment_in _ _ _ _ F) 3%nat; intros Hin Hr1 Hr2).
    destruct (bsegs_In seg Hin) as [(B & S & _)|[(B & S & _)|[(B & S & _)|(B & S & _)]]]; lia.
  Qed.

  Lemma entry_dmod : DMOD fs FDS0 mo.
  Proof. destruct ME_model. split; assumption. Qed.

  Lemma entry_tid_range : 0 < V IX_TID < 2^22.
  Proof.
    pose proof (pvar_find V both_pure_facts IX_TID 1 4194303 ME_pure ltac:(vm_compute; reflexivity)) as P. lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Local Ltac chunk := apply (chunk_of_facts bsegs V m both_mem_facts _ _ ME_facts); [cbn; repeat split; exact I | vm_compute; reflexivity | lia | cbn; lia].

  (* [comment removed for export] *)
  Lemma rw_window_wr : forall A n, 0xa1000 <= A -> A + n <= 0x5ff000 -> wr_at bsegs m A n.
  Proof.
    intros A n H0 H1. split; [lia|]. split; [lia|]. intros i Hi.
    apply (AS.BothPlanImages.both_rw_window m (wa (A + i))). rewrite wa_unsigned by lia. lia.
  Qed.

  Lemma entry_dicpt : DICPT m.
  Proof.
    assert (H1 : rw_cells bsegs m 0xa3440 [C8 (wz 0xa00d4)]) by chunk.
    assert (H2 : rw_cells bsegs m 0xa3448 [C8 (wz 0x93b5c)]) by chunk.
    assert (H3 : rw_cells bsegs m 0xa3530 [C8 (wz 0x9b25c)]) by chunk.
    unfold DICPT, ro_cells. split; [exact (proj1 H1)|]. split; [exact (proj1 H2)| exact (proj1 H3)].
  Qed.

  Lemma entry_adstat : ADSTAT (wz (V IX_TID)) m.
  Proof.
    unfold ADSTAT, ATIDCELL, AOFL_HEAD, ASTDIN_USED, ASTDOUT_USED, ASTDERR_USED, AGOT_STDERR, ASTDERR_VAR, AGOT_GUARD, AGUARD,
           ASTDIN, ASTDOUT, ASTDERR, ATP.
    split. { pose proof (mfact_find bsegs V m _ (MCell (ZLit 0x5dc8c8) 4 (ZV IX_TID)) ME_facts ltac:(vm_compute; reflexivity)) as H. exact H. }
    split. { chunk. }
    split. { exists (zb 1), (zb 0), (zb 0). exists (wz 0). chunk. }
    split. { (* [comment removed for export] *)
             left. unfold ATEX1, atex_cells, A_ATEXIT, A_ATEXIT_CALL, AINCB. cbn [app Z.add Pos.add Pos.succ].
             split; [exists (zb 0), (zb 0), (zb 0), (wz 0), (wz 0); chunk|]. split; [exists (wz 0); chunk| chunk]. }
    split. { chunk. } split. { chunk. } split. { chunk. } split. { chunk. } split. { chunk. } split. { chunk. }
    split. { chunk. } split. { chunk. } split. { chunk. } split. { chunk. } split. { chunk. } split. { chunk. }
    split. { chunk. } split. { chunk. }
    (* [comment removed for export] *)
    exists (wz (V IX_CANARY)).
    pose proof (mfact_find bsegs V m _ (MRo (ZLit 0x5fc9b0) 8 (ZV IX_CANARY)) ME_facts ltac:(vm_compute; reflexivity)) as H.
    cbn [mfact_ok zv] in H. split; [split; [cbn; exact (conj I I) | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact H]|].
    apply rw_window_wr; cbn; lia.
  Qed.

  Lemma entry_errno : rw_cells bsegs m AERRNO [C4 (wz 0)].
  Proof. unfold AERRNO, ATP. chunk. Qed.

  Lemma entry_initflag : rw_cells bsegs m AINITFLAG [C1 (zb 0)].
  Proof. unfold AINITFLAG. chunk. Qed.


  (* [comment removed for export] *)
  Lemma entry_stdout : stdout_file m stdout_init.
  Proof.
    unfold stdout_file, stdout_init. cbn [so_active so_buf so_first so_lbf_nl zlength length Z.of_nat].
    exists (wz 5), (wz 0), (repeat (zb 0) 80), (repeat (zb 0) 1024).
    split. { unfold ASTDOUT. chunk. }
    split. { reflexivity. }
    split. { unfold ASTDOUT_BUF. chunk. }
    split; [reflexivity|]. split; [unfold zlength; cbn; lia|]. intros _; reflexivity.
  Qed.

  Lemma entry_stderr : stderr_wfile0 m.
  Proof.
    unfold stderr_wfile0. exists (wz 5), (wz 0), 0, 0, (repeat (zb 0) 80).
    split. { chunk. }
    split; [reflexivity|]. split; [left; reflexivity| lia].
  Qed.

  Lemma entry_stdin : stdin_file m.
  Proof. unfold stdin_file. exists (repeat (zb 0) 80). unfold ASTDIN. chunk. Qed.

  (* [comment removed for export] *)
  Lemma entry_rs : rw_cells bsegs m ARS [CB RSN (repeat (zb 0) RSN)].
  Proof. unfold ARS. apply (chunk_of_facts bsegs V m both_mem_facts _ _ ME_facts); [split; [apply repeat_length| exact I] | vm_compute; reflexivity | lia |].
    replace (Z.of_nat (cells_size [CB RSN (repeat (zb 0) RSN)])) with 65536 by (vm_compute; reflexivity). lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma entry_ssz : stack_shadow_zero m.
  Proof.
    pose proof usp_lo as LO. pose proof usp_hi as HI. pose proof usp_V as UV.
    (nelimp ME_vars 5%nat; intros VR _ P6 P10 _). unfold IX_S2, IX_SP in *.
    assert (R6 : 0 <= V 6%nat < 256) by (rewrite P6; Z.div_mod_to_equations; lia).
    assert (R10 : 0 <= V 10%nat < 8) by (rewrite P10; Z.div_mod_to_equations; lia).
    split.
    - pose proof (mfact_find bsegs V m _
                    (MZeroS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304))
                            (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992)))
                    ME_facts ltac:(vm_compute; reflexivity)) as H.
      cbn [mfact_ok zv] in H.
      intros a Ha. unfold shb, SH, SHADOW_OFFSET. rewrite HCEIL in Ha. fold usp in Ha.
      specialize (H (SHADOW_OFFSET + a / 8 - (4096 * V 0%nat + 512 * V 10%nat + 2146402304))). unfold SHADOW_OFFSET in H.
      replace (4096 * V 0%nat + 512 * V 10%nat + 2146402304 + (2147450880 + a / 8 - (4096 * V 0%nat + 512 * V 10%nat + 2146402304)))
        with (2147450880 + a / 8) in H by lia.
      apply H. Z.div_mod_to_equations. lia.
    - intros a Ha. unfold shb. unfold SBUF_LO, SBUF_HI in Ha.
      apply (mzero_cover bsegs V m both_mem_facts 0x800b7a04 0x800b7a9c ME_facts ltac:(vm_compute; reflexivity)).
      unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bsb : list byte := build_stack_bytes BPH sp0 argv envp uid hw rdraw.
  Definition LB : Z := Z.of_nat (length bsb).
  Definition SIMG : list byte := entry_stack_image BPH sp0 argv envp uid hw rdraw.

  Lemma img_len_ge : LB <= Z.of_nat (length SIMG).
  Proof. unfold LB, SIMG, entry_stack_image. cbv zeta. fold bsb. rewrite length_app. lia. Qed.

  Lemma img_top : usp + Z.of_nat (length SIMG) <= 0x800000000000.
  Proof.
    unfold SIMG, usp. rewrite (entry_stack_image_top BPH sp0 argv envp uid hw rdraw).
    pose proof (F.entry_page_top_within_window BPH sp0 argv envp uid hw rdraw VFIT) as T. unfold sp_window_hi in T. exact T.
  Qed.

  Lemma bsb_len_bound : 0 <= LB <= 2240000.
  Proof. split; [unfold LB; lia|]. unfold LB, bsb. apply (RL.lay_bsb_len _ sp0 rdraw argv envp _ hw VA VE). Qed.

  Lemma bsb_len_mod8 : LB mod 8 = 0.
  Proof.
    unfold LB, bsb. (nelim (RL.bsb_random_split BPH sp0 rdraw argv envp uid hw) 4%nat; intros pre E _ Hm).
    rewrite E, length_app, length_at_random_bytes, Nat2Z.inj_add. rewrite Z.add_mod, Hm by lia. reflexivity.
  Qed.

  Lemma struct_size_val : Z.of_nat (CE.cat_struct_size argv envp) = 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184.
  Proof. unfold CE.cat_struct_size, auxv_size. lia. Qed.

  Lemma W_val : 8 * amain_W sp0 rdraw argv envp uid hw = LB - 16 - Z.of_nat (CE.cat_struct_size argv envp).
  Proof.
    unfold amain_W. fold bsb. fold LB. rewrite struct_size_val.
    pose proof bsb_len_mod8 as M8.
    pose proof (RL.auxv_off_bound BPH sp0 rdraw argv envp uid hw) as AB. fold bsb in AB. unfold RL.auxv_off in AB. unfold LB in *.
    Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma in_string_block : forall a : word,
    usp + Z.of_nat (CE.cat_struct_size argv envp) <= bv_unsigned a < usp + LB - 16 ->
    m a = stack_to_mem sp0 SIMG a.
  Proof.
    intros a Ha. rewrite (ME_args a).
    - unfold wrap_mem. fold SIMG. destruct (stack_to_mem sp0 SIMG a) eqn:E; [reflexivity|]. exfalso.
      unfold stack_to_mem in E. fold usp in E. rewrite (proj2 (Z.leb_le _ _)) in E by lia.
      pose proof img_len_ge as IL. rewrite (proj2 (Z.ltb_lt _ _)) in E by lia.
      destruct (nth_error SIMG (Z.to_nat (bv_unsigned a - usp))) eqn:En; [discriminate|]. apply nth_error_None in En. lia.
    - unfold amain_argblock. cbv zeta. right. pose proof W_val as WV. rewrite struct_size_val in *. fold usp. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma block_bytes : forall (a : word) bs,
    usp + Z.of_nat (CE.cat_struct_size argv envp) <= bv_unsigned a -> bv_unsigned a + Z.of_nat (length bs) <= usp + LB - 16 ->
    F.rdn bsegs (stack_to_mem sp0 SIMG) a (length bs) = Some bs -> bytes_at bsegs m (bv_unsigned a) bs.
  Proof.
    intros a bs H1 H2 H. pose proof usp_lo. pose proof usp_hi. pose proof bsb_len_bound.
    apply (bytes_at_agree bsegs (stack_to_mem sp0 SIMG)).
    { intros i Hi. apply in_string_block. rewrite wa_unsigned by lia. lia. }
    apply rdn_bytes_at; [lia| lia|]. rewrite <- rdn_flat. unfold wa. rewrite Z_to_bv_bv_unsigned. exact H.
  Qed.


  (* [comment removed for export] *)
  Lemma bsb_len_eq : LB = Z.of_nat (CE.cat_struct_size argv envp) + Z.of_nat (F.total_arg_bytes_nat argv) + Z.of_nat (F.total_arg_bytes_nat envp)
                          + ((8 - (Z.of_nat (CE.cat_struct_size argv envp + F.total_arg_bytes_nat argv + F.total_arg_bytes_nat envp)) mod 8) mod 8) + 16.
  Proof.
    unfold LB, bsb. set (ph := BPH). clearbody ph. unfold build_stack_bytes. cbv zeta.
    rewrite (F.string_addrs_pair argv). cbv beta iota. rewrite (F.string_addrs_pair envp). cbv beta iota.
    unfold at_random_bytes.
    set (AUX := auxv_bytes ph _ _ _). pose proof (length_auxv_bytes ph (at_random_ptr sp0 argv envp) uid hw) as LA. fold AUX in LA. clearbody AUX.
    unfold auxv_size in LA.
    rewrite !length_app, !repeat_length, !F.length_flat_map_le8, !F.length_string_addrs_fst, !F.length_n_to_le_8, !LA, !F.length_flatten_strings.
    unfold CE.cat_struct_size, auxv_size.
    set (T := F.total_arg_bytes_nat argv). set (U := F.total_arg_bytes_nat envp). clearbody T U.
    replace (8 + (length argv + 1) * 8 + (length envp + 1) * 8 + 160 + T + U)%nat
      with (8 + (8 * length argv + (8 + (8 * length envp + (8 + (160 + (T + U)))))))%nat by lia.
    replace (Z.of_nat (8 + (length argv + 1) * 8 + (length envp + 1) * 8 + 160) + Z.of_nat T + Z.of_nat U)
      with (Z.of_nat (8 + (8 * length argv + (8 + (8 * length envp + (8 + (160 + (T + U)))))))) by lia.
    set (X := (8 + (8 * length argv + (8 + (8 * length envp + (8 + (160 + (T + U)))))))%nat). clearbody X.
    pose proof (Z.mod_pos_bound (8 - Z.of_nat X mod 8) 8 ltac:(lia)).
    rewrite !Nat2Z.inj_add, Z2Nat.id by lia. cbn [length]. lia.
  Qed.

  Lemma total_firstn_nth : forall (l : list (list byte)) k, (k < length l)%nat ->
    (F.total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1 <= F.total_arg_bytes_nat l)%nat.
  Proof.
    induction l as [|x l IH]; intros k Hk; [cbn in Hk; lia|].
    destruct k as [|k]; cbn [firstn nth]; rewrite ?CE.total_arg_bytes_cons; [cbn; lia|].
    cbn [length] in Hk. specialize (IH k ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma entry_argv_str : forall k, (k < length argv)%nat ->
    exists slack : list byte,
      bytes_at bsegs m (bv_unsigned (CE.cat_argv_ptr sp0 argv envp k)) (nth k argv [] ++ Z_to_bv 8 0 :: slack)
      /\ (- (bv_unsigned (CE.cat_argv_ptr sp0 argv envp k) + Z.of_nat (length (nth k argv [])) + 1)) mod 8 <= Z.of_nat (length slack)
      /\ bv_unsigned (CE.cat_argv_ptr sp0 argv envp k) = usp + Z.of_nat (CE.cat_struct_size argv envp) + Z.of_nat (F.total_arg_bytes_nat (firstn k argv))
      /\ bv_unsigned (CE.cat_argv_ptr sp0 argv envp k) + Z.of_nat (length (nth k argv [])) + 1 + Z.of_nat (length slack) <= usp + LB - 16.
  Proof.
    intros k Hk. pose proof usp_lo as LO. pose proof usp_hi as HI. pose proof bsb_len_bound as BL. pose proof usp_al as AL. pose proof bsb_len_mod8 as M8.
    set (P := bv_unsigned (CE.cat_argv_ptr sp0 argv envp k)). set (str := nth k argv []).
    pose proof (RL.u_cat_argv_ptr BPH sp0 rdraw argv envp uid hw VA VE usp_lo usp_hi k Hk) as HP. fold P in HP. fold usp in HP.
    pose proof (total_firstn_nth argv k Hk) as TF. fold str in TF.
    pose proof bsb_len_eq as LE.
    assert (ROOM : P + Z.of_nat (length str) + 1 + 16 <= usp + LB).
    { rewrite LE, HP. pose proof (Z.mod_pos_bound (8 - Z.of_nat (CE.cat_struct_size argv envp + F.total_arg_bytes_nat argv + F.total_arg_bytes_nat envp) mod 8) 8 ltac:(lia)). lia. }
    clear LE TF.
    set (x := P + Z.of_nat (length str) + 1). set (pad := (- x) mod 8).
    pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as PB. fold pad in PB.
    assert (XP : x + pad <= usp + LB - 16) by (unfold pad; fold x in ROOM; Z.div_mod_to_equations; lia).
    pose proof img_len_ge as IL. pose proof img_top as IT.
    exists (firstn (Z.to_nat pad) (skipn (Z.to_nat (x - usp)) SIMG)).
    assert (LS : length (firstn (Z.to_nat pad) (skipn (Z.to_nat (x - usp)) SIMG)) = Z.to_nat pad).
    { rewrite length_firstn, length_skipn. unfold LB in *. lia. }
    rewrite LS.
    split; [| split; [lia| split; [rewrite HP; lia| lia]]].
    replace (str ++ Z_to_bv 8 0 :: firstn (Z.to_nat pad) (skipn (Z.to_nat (x - usp)) SIMG))
      with ((str ++ [Z_to_bv 8 0]) ++ firstn (Z.to_nat pad) (skipn (Z.to_nat (x - usp)) SIMG)) by (rewrite <- app_assoc; reflexivity).
    apply (proj2 (bytes_at_app _ _ _ _ _)). split.
    - apply block_bytes; [fold P; lia| fold P; rewrite length_app; cbn [length]; lia|].
      rewrite length_app. cbn [length]. fold str.
      apply (FS.read_argv_cstr_k BPH bsegs sp0 argv envp k uid hw rdraw Hk).
      fold bsb. unfold LB in BL. lia.
    - rewrite length_app. cbn [length]. fold str.
      pose proof (block_bytes (Z_to_bv 64 x) (firstn (Z.to_nat pad) (skipn (Z.to_nat (x - usp)) SIMG))) as B.
      rewrite unsigned_lit in B by lia. rewrite LS in B.
      replace (P + Z.of_nat (length str + 1)) with x by lia. apply B; [lia| lia|].
      rewrite F.rdn_stack; rewrite ?unsigned_lit by lia; [reflexivity| lia| unfold LB in *; lia| unfold LB in *; lia].
  Qed.


  (* [comment removed for export] *)
  Lemma high_bytes_wr : forall a bs, bytes_at bsegs m a bs -> AIMG_HI <= a -> wr_at bsegs m a (Z.of_nat (length bs)).
  Proof.
    intros a bs (H0 & H1 & H) Ha. split; [exact H0|]. split; [exact H1|]. intros i Hi.
    specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia.
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [| apply nth_error_None in E; lia].
    unfold mrd in H. destruct (m (wa (a + i))) as [b'|] eqn:Em; [unfold wview; rewrite Em; discriminate|]. exfalso.
    apply (seg_rom_seg bsegs) in H. apply H.
    destruct (find_segment bsegs (bv_unsigned (wa (a + i))) 1) as [seg|] eqn:F; [|reflexivity]. exfalso.
    (nelim (find_segment_in _ _ _ _ F) 3%nat; intros Hin Hr1 Hr2). rewrite wa_unsigned in Hr1, Hr2 by lia. unfold AIMG_HI in Ha.
    destruct (bsegs_In seg Hin) as [(B & S & _)|[(B & S & _)|[(B & S & _)|(B & S & _)]]]; lia.
  Qed.

  Lemma V_argc : V 1%nat = Z.of_nat (length argv). Proof. (nelimp ME_vars 7%nat; intros _ _ _ _ _ H _). exact H. Qed.
  Lemma V_envc : V 2%nat = Z.of_nat (length envp). Proof. (nelimp ME_vars 8%nat; intros _ _ _ _ _ _ H _). exact H. Qed.
  Lemma V_L0 : V 3%nat = Z.of_nat (length (nth 0 argv [])). Proof. (nelimp ME_vars 9%nat; intros _ _ _ _ _ _ _ H _). exact H. Qed.

  Lemma argc_pos : (1 <= length argv)%nat.
  Proof. pose proof VA as [H _]. lia. Qed.

  (* [comment removed for export] *)
  Lemma entry_argv0 : argv_str_at m (usp - 48) 0 (hd [] argv).
  Proof.
    pose proof usp_lo as LO. pose proof usp_hi as HI. pose proof bsb_len_bound as BL. pose proof img_len_ge as IL. pose proof img_top as IT.
    pose proof argc_pos as AP.
    (nelim (entry_argv_str 0 ltac:(lia)) 5%nat; intros slack BY SLK HP HEND).
    change (firstn 0 argv) with (@nil (list byte)) in HP. change (F.total_arg_bytes_nat []) with 0%nat in HP. rewrite struct_size_val in HP.
    replace (nth 0 argv []) with (hd [] argv) in * by (destruct argv; reflexivity).
    set (P := bv_unsigned (CE.cat_argv_ptr sp0 argv envp 0)) in *.
    exists P, slack. unfold zlength.
    split; [| split; [exact BY| split; [exact SLK| split; [lia| lia]]]].
    pose proof (mfact_find bsegs V m _
      (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit 8)) 8
           (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 184)))
      ME_facts ltac:(vm_compute; reflexivity)) as H.
    cbn [mfact_ok zv] in H. rewrite V_argc, V_envc in H.
    replace (32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat) + 8) with (usp - 48 + 56 + 8 * Z.of_nat 0) in H by (pose proof usp_V as UV; lia).
    replace (32768 * V 0%nat + (8 * Z.of_nat (length argv) + (8 * Z.of_nat (length envp) + (16 * V 6%nat + 4096 * V 10%nat))) + 184) with P in H by (pose proof usp_V as UV; clearbody P; lia).
    split; [split; [cbn; exact (conj I I) | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact H]|].
    apply (high_bytes_wr _ _ H). unfold AIMG_HI. lia.
  Qed.


  (* [comment removed for export] *)
  Lemma entry_argv1 : length argv = 2%nat -> argv_str_at m (usp - 48) 1 (nth 1 argv []).
  Proof.
    intros Hlen.
    pose proof usp_lo as LO. pose proof usp_hi as HI. pose proof bsb_len_bound as BL. pose proof img_len_ge as IL. pose proof img_top as IT.
    (nelim (entry_argv_str 1 ltac:(lia)) 5%nat; intros slack BY SLK HP HEND).
    assert (TF : Z.of_nat (F.total_arg_bytes_nat (firstn 1 argv)) = Z.of_nat (length (nth 0 argv [])) + 1).
    { clear BY SLK HP HEND. destruct argv as [|a0 r]; [discriminate|]. change (firstn 1 (a0 :: r)) with [a0]. rewrite CE.total_arg_bytes_cons.
      change (F.total_arg_bytes_nat []) with 0%nat. cbn [nth]. lia. }
    rewrite TF, struct_size_val in HP. clear TF.
    set (P := bv_unsigned (CE.cat_argv_ptr sp0 argv envp 1)) in *.
    exists P, slack. unfold zlength.
    split; [| split; [exact BY| split; [exact SLK| split; [lia| lia]]]].
    pose proof (mfact_find bsegs V m _
      (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit 16)) 8
           (ZMul (ZLtu (ZLit 1) (ZV 1)) (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZV 3) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))))) (ZLit 185))))
      ME_facts ltac:(vm_compute; reflexivity)) as H.
    cbn [mfact_ok zv] in H. rewrite V_argc, V_envc, V_L0, Hlen in H.
    change (Z.b2z (1 mod two64 <? Z.of_nat 2 mod two64)) with 1 in H. rewrite Z.mul_1_l in H.
    replace (32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat) + 16) with (usp - 48 + 56 + 8 * Z.of_nat 1) in H by (pose proof usp_V as UV; lia).
    replace (32768 * V 0%nat + (8 * Z.of_nat 2 + (8 * Z.of_nat (length envp) + (Z.of_nat (length (nth 0 argv [])) + (16 * V 6%nat + 4096 * V 10%nat)))) + 185)
      with P in H by (pose proof usp_V as UV; rewrite Hlen in HP; clearbody P; lia).
    split; [split; [cbn; exact (conj I I) | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact H]|].
    apply (high_bytes_wr _ _ H). unfold AIMG_HI. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition entry_lo : Z := Z.max (usp - 8388608) (ASTACK_BOTTOM usp).

  Lemma entry_lo_facts : stk bsegs m entry_lo (usp - 48) /\ entry_lo + 2^22 <= usp - 48 /\ alloc_ceiling <= entry_lo
                         /\ ASTACK_BOTTOM usp <= entry_lo.
  Proof.
    pose proof usp_lo as LO. pose proof usp_hi as HI.
    assert (B : usp - 8388608 - 4096 <= ASTACK_BOTTOM usp <= usp - 8388608 + 4096).
    { unfold ASTACK_BOTTOM, ASTACK_TOP, roundup. Z.div_mod_to_equations. lia. }
    unfold entry_lo. split.
    - destruct (stk_split bsegs m (usp - 8388608) (Z.max (usp - 8388608) (ASTACK_BOTTOM usp)) usp entry_stk ltac:(lia)) as [_ S2].
      destruct (stk_split bsegs m _ (usp - 48) usp S2 ltac:(lia)) as [S3 _]. exact S3.
    - split; [lia|]. split; [rewrite HCEIL; fold usp; lia | lia].
  Qed.

End Entry.
End CeilWrap.
End AEntry.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require RealizesEqv.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RealizesEqv.RegsEqv0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RealizesEqv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Ceil FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface Drv_base Drv_iface2 Drv_stmt DrvTop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import MainExport.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AMainEntry.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AMainEntry.MainFactsBoth.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import AMainEntry.
Import AEntry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section PerCeil.
Context {ACEIL : Ceil}.
Variables (AI : art_iface) (DI : drv_iface2 AI).

(* [comment removed for export] *)
Definition art_init_stmt : Prop :=
  forall (w : bool) (V : nat -> Z) (sp0 brk0 mbase : word) (rdraw : EntryDraw) (argv envp : list (list byte))
         (uid hw : word) (fs : Fs.Fs) (regs : bvmap 5 word) (m : word -> option byte) (mo : Model) (g : lghost),
    valid_sp sp0 -> valid_brk bsegs brk0 -> valid_mmap_base mbase ->
    valid_argv argv -> valid_envp envp -> valid_fs fs -> entry_stack_fits sp0 argv envp -> valid_id uid -> valid_hwcap hw ->
    alloc_ceiling = bv_unsigned sp0 - 8388608 ->
    a_main_entry w V sp0 brk0 rdraw argv envp uid hw fs regs m mo g ->
    LOK bsegs mo -> BINV mo g ->
    exists B0, DRV_B_MAIN <= B0
               /\ CJ_iface.ART AI (bv_unsigned sp0) (bv_unsigned sp0 - 48) [] [] [] B0 m mo g
               /\ Drv_iface2.ADRV AI DI DRV_CALLS m mo g.

(* [comment removed for export] *)
Definition a_main_at : Prop :=
  forall (w : bool) (V : nat -> Z) (sp0 brk0 mbase : word) (rdraw : EntryDraw) (argv envp : list (list byte))
         (uid hw : word) (fs : Fs.Fs) (regs : bvmap 5 word) (m : word -> option byte) (mo : Model) (g : lghost),
    valid_sp sp0 -> valid_brk bsegs brk0 -> valid_mmap_base mbase ->
    valid_argv argv -> valid_envp envp -> valid_fs fs -> entry_stack_fits sp0 argv envp -> valid_id uid -> valid_hwcap hw ->
    alloc_ceiling = bv_unsigned sp0 - 8388608 ->
    a_main_entry w V sp0 brk0 rdraw argv envp uid hw fs regs m mo g ->
    LRZ bsegs (MS (mkR_of regs) bvmap_empty (Z_to_bv 64 AM_MAIN) (Z_to_bv 32 0) None m (seg_rom bsegs)) mo g (spec04 argv fs).

Theorem a_main_at_of : art_init_stmt -> a_main_stmt04 AI DI -> a_main_at.
Proof.
  intros HART HDRV w V sp0 brk0 mbase rdraw argv envp uid hw fs regs m mo g Hsp Hbrk Hmb Hva Hve Hfs Hfit Huid Hhw HCEIL ME.
  apply lrz_assume. intros _ HLOK HBINV.
  destruct (HART w V sp0 brk0 mbase rdraw argv envp uid hw fs regs m mo g Hsp Hbrk Hmb Hva Hve Hfs Hfit Huid Hhw HCEIL ME HLOK HBINV)
    as (B0 & HB0 & HA & HD).
  apply (HDRV argv fs _ mo g Hva).
  pose proof ME as (MV & MR & _).
  destruct MR as (R1 & R2 & R3 & R4 & R8 & R9 & R10 & R11 & _).
  (* [comment removed for export] *)
  change (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.PropExec.getr regs) with (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.getr regs) in R1, R2, R3, R4, R8, R9, R10, R11.
  pose proof MV as (_ & _ & _ & _ & _ & PARGC & _).
  pose proof (usp_lo sp0 Hsp) as LO. pose proof (usp_hi sp0 Hsp) as HI. pose proof (usp_al sp0 Hsp) as AL.
  destruct (entry_lo_facts w V sp0 brk0 rdraw argv envp uid hw fs regs m mo g ME Hsp HCEIL) as (STK & ROOM & CL & BOT).
  pose proof (entry_tid_range w V sp0 brk0 rdraw argv envp uid hw fs regs m mo g ME) as TID.
  unfold a_main_ready, mkR_of. cbv zeta.
  do 31 eexists. exists bvmap_empty, (Z_to_bv 32 0), m, (entry_lo sp0), (Z_to_bv 64 (V IX_TID)), (Z_to_bv 64 0), B0.
  split; [reflexivity|].
  split; [exact R1|]. split; [exact R4|].
  split; [rewrite R10, PARGC; reflexivity|].
  split; [rewrite R11, R2; f_equal; rewrite unsigned_lit by lia; lia|].
  split; [reflexivity|].
  rewrite R2. rewrite (unsigned_lit (bv_unsigned sp0 - 48)) by lia.
  replace (bv_unsigned sp0 - 48 + 48) with (bv_unsigned sp0) by lia.
  split; [exact HA|]. split; [exact HB0|]. split; [exact HD|].
  split; [exact (entry_dmod w V sp0 brk0 rdraw argv envp uid hw fs regs m mo g ME)|].
  split; [exact STK|]. split; [exact ROOM|]. split; [exact CL|]. split; [lia|].
  split; [unfold sp_window_lo; lia|]. split; [Z.div_mod_to_equations; lia|]. split; [exact BOT|].
  split; [exact (entry_mem_inv w V sp0 brk0 rdraw argv envp uid hw fs regs m mo g ME)|].
  split; [exact (entry_adstat w V sp0 brk0 rdraw argv envp uid hw fs regs m mo g ME)|].
  split; [rewrite unsigned_lit by lia; exact TID|].
  split; [exact (entry_dicpt w V sp0 brk0 rdraw argv envp uid hw fs regs m mo g ME)|].
  split; [exact (entry_errno w V sp0 brk0 rdraw argv envp uid hw fs regs m mo g ME)|].
  split; [exact (entry_initflag w V sp0 brk0 rdraw argv envp uid hw fs regs m mo g ME)|].
  split; [exact (entry_stdout w V sp0 brk0 rdraw argv envp uid hw fs regs m mo g ME)|].
  split; [exact (entry_stderr w V sp0 brk0 rdraw argv envp uid hw fs regs m mo g ME)|].
  split; [exact (entry_stdin w V sp0 brk0 rdraw argv envp uid hw fs regs m mo g ME)|].
  split; [exact (entry_ssz w V sp0 brk0 rdraw argv envp uid hw fs regs m mo g ME Hsp HCEIL)|].
  split; [eexists; exact (entry_rs w V sp0 brk0 rdraw argv envp uid hw fs regs m mo g ME)|].
  split; [exact (entry_argv0 w V sp0 brk0 rdraw argv envp uid hw fs regs m mo g ME Hva Hve Hsp Hfit HCEIL)|].
  exact (entry_argv1 w V sp0 brk0 rdraw argv envp uid hw fs regs m mo g ME Hva Hve Hsp Hfit HCEIL).
Qed.
End PerCeil.

(* [comment removed for export] *)
Theorem a_main_stmt_of :
  (forall ACEIL : Ceil, exists (AI : art_iface) (DI : drv_iface2 AI), art_init_stmt AI DI /\ a_main_stmt04 AI DI) -> a_main_stmt.
Proof.
  intros H ACEIL. destruct (H ACEIL) as (AI & DI & HA & HD). exact (a_main_at_of AI DI HA HD).
Qed.
