(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the entry section takes the launch's ProcInput, mmap base, valid_launch and entry_launch_ok_va; the stack below sp is the model's stack_window_depth deep; the argv strings are read from the launch's block (StackLayout's entry image, ending at ed_top), each NUL at least 9 bytes below 2^47; art_init_stmt and a_main_at are stated over the launch's ProcInput. *)
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kitL.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require SO_base.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_base.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_icpt_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_dicpt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require DrvTop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require MainExport.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AMainEntry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AEntryLib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanPlanImages.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require PropExec MemSplit AsanPlanCore.
Module AEntry.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kitL OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.SO_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_icpt_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_dicpt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.DrvTop OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.MainExport OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AMainEntry.MainFactsAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AMainEntry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AEntryLib.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation APH := Asan.M.phdrs (only parsing).
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
Module ASP := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.PropExec.
Module SWS := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.MemSplit.StoreOk.
(* the writable window below sp: the model's stack_window_depth *)
Local Notation SWD := SWS.stack_window_depth (only parsing).
Module APCm := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore.APC.

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
  (* every lemma takes the whole section context, so a_main_at_of calls them uniformly *)
  Set Default Proof Using "All".
  Variables (w : bool) (V : nat -> Z) (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (fs : Fs.Fs)
            (regs : bvmap 5 word) (m : word -> option byte) (mo : Model) (g : lghost).
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation xfn := (in_execfn inp) (only parsing).
  Local Notation RB := (kb_rseq (in_kernel inp)) (only parsing).
  Local Notation RENT := (wz (Z.of_N Asan.M.init_pc)) (only parsing).
  Hypothesis ME : a_main_entry w V sp0 brk0 mbase rdraw inp fs regs m mo g.
  Hypothesis VA : valid_argv av.
  Hypothesis VE : valid_envp ev.
  Hypothesis VSP : valid_sp sp0.
  Hypothesis VL : valid_launch inp.
  Hypothesis LAU : entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp.
  Hypothesis HCEIL : alloc_ceiling = bv_unsigned sp0 - 8388608.

  Let usp := bv_unsigned sp0.

  Lemma usp_lo : 0x7fff80000000 <= usp.
  Proof. (nelimp VSP 3%nat; intros H _ _). unfold sp_window_lo in H. exact H. Qed.
  Lemma usp_hi : usp <= 0x800000000000.
  Proof. (nelimp VSP 3%nat; intros _ H _). unfold sp_window_hi in H. exact H. Qed.
  Lemma usp_al : usp mod 16 = 0.
  Proof. (nelimp VSP 3%nat; intros _ _ H). exact H. Qed.

  Lemma ME_vars : amain_vars V sp0 brk0 rdraw inp. Proof. exact (proj1 ME). Qed.
  Lemma ME_facts_w : Forall (mfact_ok asegs V m) (asan_mem_facts ++ asan_mem_facts_w w). Proof. exact (proj1 (proj2 (proj2 ME))). Qed.
  Lemma ME_facts : Forall (mfact_ok asegs V m) asan_mem_facts. Proof. exact (proj1 (proj1 (Forall_app _ _ _) ME_facts_w)). Qed.
  Lemma ME_pure_w : Forall (pfact_ok V) (asan_pure_facts ++ asan_pure_facts_w w). Proof. exact (proj1 (proj2 (proj2 (proj2 ME)))). Qed.
  Lemma ME_pure : Forall (pfact_ok V) asan_pure_facts. Proof. exact (proj1 (proj1 (Forall_app _ _ _) ME_pure_w)). Qed.
  Lemma ME_args : amain_args sp0 mbase rdraw inp m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 ME))))). Qed.
  Lemma ME_model : amodel V sp0 fs mo. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 ME)))))). Qed.
  Lemma ME_top : forall a : word, 0x800000000000 <= bv_unsigned a -> m a = None.
  Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ME))))))))). Qed.
  (* the facts on the launch's own variables that depend on its rseq flag *)
  Lemma ME_facts_r : Forall (mfact_ok asegs V m) (asan_mem_facts_r RB).
  Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ME)))))))))). Qed.

  Lemma usp_V : usp = 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat.
  Proof. (nelimp ME_vars 6%nat; intros _ _ _ _ H _). unfold IX_S1, IX_SP, IX_S2 in H. unfold usp. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma entry_pristine_ro : forall i, 0x10000 <= i < 0xa1000 -> m (wa i) = None.
  Proof. exact (mimg_cover asegs V m asan_mem_facts 0x10000 0xa1000 ME_facts ltac:(vm_compute; reflexivity)). Qed.

  Lemma entry_mem_inv : mem_inv asegs m.
  Proof.
    apply mem_inv_intro. intros a b Hab.
    assert (Hlt : bv_unsigned a < TASK_SIZE).
    { destruct (Z.lt_ge_cases (bv_unsigned a) 0x800000000000) as [L|G]; [exact L|]. rewrite (ME_top a G) in Hab. discriminate. }
    split; [| right; exact Hlt].
    unfold ro_addr. destruct (find_segment asegs (bv_unsigned a) 1) as [seg|] eqn:F; [|reflexivity].
    destruct (seg_writable seg) eqn:W; [reflexivity|]. exfalso.
    (nelim (find_segment_in _ _ _ _ F) 3%nat; intros Hin Hr1 Hr2).
    assert (Hro : 0x10000 <= bv_unsigned a < 0xa1000).
    { destruct (asegs_In seg Hin) as [(B & S & _)|[(B & S & _)|[(_ & _ & X)|(_ & _ & X)]]]; try congruence; lia. }
    pose proof (entry_pristine_ro (bv_unsigned a) Hro) as N. unfold wa in N. rewrite Z_to_bv_bv_unsigned in N. congruence.
  Qed.

  (* [comment removed for export] *)
  (* the writable stack window below sp, the model's stack_window_depth deep *)
  Lemma SWD_range : 2 ^ 22 + 48 <= SWD <= 8388608 - 4096.
  Proof. unfold SWS.stack_window_depth, SWS.stack_window_reach. rewrite CE.stack_max_size_val. lia. Qed.

  Lemma entry_stk : stk asegs m (usp - SWD) usp.
  Proof.
    pose proof (mwr_find asegs V m asan_mem_facts
                  (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (- SWD))) SWD
                  ME_facts ltac:(vm_compute; reflexivity)) as W.
    cbn [zv] in W. replace (32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat) + - SWD) with (usp - SWD) in W by (rewrite usp_V; lia).
    pose proof usp_lo as LO. pose proof usp_hi as HI. pose proof SWD_range as SR.
    apply wr_at_stk; [replace (usp - (usp - SWD)) with SWD by lia; exact W|].
    intros a Ha. destruct (find_segment asegs a 1) as [seg|] eqn:F; [|reflexivity]. exfalso.
    (nelim (find_segment_in _ _ _ _ F) 3%nat; intros Hin Hr1 Hr2).
    destruct (asegs_In seg Hin) as [(B & S & _)|[(B & S & _)|[(B & S & _)|(B & S & _)]]]; lia.
  Qed.

  Lemma entry_dmod : DMOD fs FDS0 mo.
  Proof. destruct ME_model. split; assumption. Qed.

  Lemma entry_tid_range : 0 < V IX_TID < 2^22.
  Proof.
    pose proof (pvar_find V asan_pure_facts IX_TID 1 4194303 ME_pure ltac:(vm_compute; reflexivity)) as P. lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Local Ltac chunk := apply (chunk_of_facts asegs V m asan_mem_facts _ _ ME_facts); [cbn; repeat split; exact I | vm_compute; reflexivity | lia | cbn; lia].

  (* [comment removed for export] *)
  Lemma rw_window_wr : forall A n, 0xa1000 <= A -> A + n <= 0x5ff000 -> wr_at asegs m A n.
  Proof.
    intros A n H0 H1. split; [lia|]. split; [lia|]. intros i Hi.
    apply (AS.AsanPlanImages.asan_rw_window m (wa (A + i))). rewrite wa_unsigned by lia. lia.
  Qed.

  Lemma entry_dicpt : DICPT m.
  Proof.
    assert (H1 : rw_cells asegs m 0xa3cc0 [C8 (wz 0xa0954)]) by chunk.
    assert (H2 : rw_cells asegs m 0xa3cc8 [C8 (wz 0x943dc)]) by chunk.
    assert (H3 : rw_cells asegs m 0xa3db0 [C8 (wz 0x9badc)]) by chunk.
    unfold DICPT, ro_cells. split; [exact (proj1 H1)|]. split; [exact (proj1 H2)| exact (proj1 H3)].
  Qed.

  Lemma entry_adstat : ADSTAT (wz (V IX_TID)) m.
  Proof.
    unfold ADSTAT, ATIDCELL, AOFL_HEAD, ASTDIN_USED, ASTDOUT_USED, ASTDERR_USED, AGOT_STDERR, ASTDERR_VAR, AGOT_GUARD, AGUARD,
           ASTDIN, ASTDOUT, ASTDERR, ATP.
    split. { pose proof (mfact_find asegs V m _ (MCell (ZLit 0x5dd1a8) 4 (ZV IX_TID)) ME_facts ltac:(vm_compute; reflexivity)) as H. exact H. }
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
    pose proof (mfact_find asegs V m _ (MRo (ZLit 0x5fd290) 8 (ZV IX_CANARY)) ME_facts ltac:(vm_compute; reflexivity)) as H.
    cbn [mfact_ok zv] in H. split; [split; [cbn; exact (conj I I) | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact H]|].
    apply rw_window_wr; cbn; lia.
  Qed.

  Lemma entry_errno : rw_cells asegs m AERRNO [C4 (wz 0)].
  Proof. unfold AERRNO, ATP. chunk. Qed.

  Lemma entry_initflag : rw_cells asegs m AINITFLAG [C1 (zb 0)].
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
  Lemma entry_rs : rw_cells asegs m ARS [CB RSN (repeat (zb 0) RSN)].
  Proof. unfold ARS. apply (chunk_of_facts asegs V m asan_mem_facts _ _ ME_facts); [split; [apply repeat_length| exact I] | vm_compute; reflexivity | lia |].
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
    - pose proof (mfact_find asegs V m _
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
      apply (mzero_cover asegs V m asan_mem_facts 0x800b7b20 0x800b7bb8 ME_facts ltac:(vm_compute; reflexivity)).
      unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac lctx := first [ exact VA | exact VE | exact VL | exact LAU | exact usp_lo | exact usp_hi | exact usp_al ].

  (* the entry block: StackLayout's image from sp to the stack VMA's top (ed_top) *)
  Definition SIMG : list byte := entry_stack_image inp mbase APH RENT sp0 rdraw.
  Definition LB : Z := Z.of_nat (length SIMG).

  Lemma lb_top : usp + LB = bv_unsigned (ed_top rdraw).
  Proof. unfold LB, SIMG, usp. rewrite (F.length_entry_stack_image_launch Sv48 inp mbase APH RENT sp0 brk0 rdraw LAU). lia. Qed.

  Lemma top_facts : bv_unsigned (ed_top rdraw) <= 0x800000000000 /\ bv_unsigned (ed_top rdraw) mod 8 = 0.
  Proof.
    destruct LAU as ((T1 & T2 & _) & _). cbn [va_stack_top] in T2. unfold sp_window_hi, page_size in *.
    split; [lia|]. rewrite <- (Z.mod_mod (bv_unsigned (ed_top rdraw)) 8) by lia.
    replace (bv_unsigned (ed_top rdraw)) with (4096 * (bv_unsigned (ed_top rdraw) / 4096) + bv_unsigned (ed_top rdraw) mod 4096)
      by (symmetry; apply Z.div_mod; lia).
    rewrite T1, Z.add_0_r. replace (4096 * (bv_unsigned (ed_top rdraw) / 4096)) with ((512 * (bv_unsigned (ed_top rdraw) / 4096)) * 8) by lia.
    rewrite Z_mod_mult. reflexivity.
  Qed.

  (* the lowest string byte is the head and the pad above sp *)
  Lemma STR0_eq : amain_STR0 sp0 rdraw inp = usp + Z.of_nat (CE.cat_string_off RB sp0 (ed_top rdraw) av ev xfn).
  Proof. unfold amain_STR0, amain_W, CE.cat_string_off, usp. lia. Qed.

  (* the pad fills the room between the head and the strings: the strings and the 8-byte slot end at ed_top *)
  Lemma str0_strings : amain_STR0 sp0 rdraw inp + Z.of_nat (launch_string_bytes av ev xfn) + 8 = bv_unsigned (ed_top rdraw).
  Proof.
    destruct LAU as (_ & (_ & _ & HI) & _). unfold launch_sp_hi, align_down16 in HI.
    pose proof (Z.mod_pos_bound (bv_unsigned (ed_top rdraw) - 8 - Z.of_nat (launch_string_bytes av ev xfn)) 16 ltac:(lia)) as MB.
    unfold amain_STR0, amain_W, block_pad_len. rewrite Z2Nat.id by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* the strings are read as the launch wrote them (amain_args) *)
  Lemma in_string_block : forall a : word,
    amain_STR0 sp0 rdraw inp <= bv_unsigned a < bv_unsigned (ed_top rdraw) -> m a = stack_to_mem sp0 SIMG a.
  Proof.
    intros a Ha. rewrite (ME_args a) by (unfold amain_argblock; cbv zeta; right; exact Ha).
    unfold SIMG. apply ASP.wrap_above_sp. unfold amain_STR0, amain_W in Ha. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma block_bytes : forall (a : word) bs,
    amain_STR0 sp0 rdraw inp <= bv_unsigned a -> bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned (ed_top rdraw) ->
    F.rdn asegs (stack_to_mem sp0 SIMG) a (length bs) = Some bs -> bytes_at asegs m (bv_unsigned a) bs.
  Proof.
    intros a bs H1 H2 H. pose proof usp_lo as LO. pose proof top_facts as (TT & _). pose proof STR0_eq as SE. unfold usp in *.
    apply (bytes_at_agree asegs (stack_to_mem sp0 SIMG)).
    { intros i Hi. apply in_string_block. rewrite wa_unsigned by lia. lia. }
    apply rdn_bytes_at; [lia| lia|]. rewrite <- rdn_flat. unfold wa. rewrite Z_to_bv_bv_unsigned. exact H.
  Qed.

  Lemma total_firstn_nth : forall (l : list (list byte)) k, (k < length l)%nat ->
    (F.total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1 <= F.total_arg_bytes_nat l)%nat.
  Proof.
    induction l as [|x l IH]; intros k Hk; [cbn in Hk; lia|].
    destruct k as [|k]; cbn [firstn nth]; rewrite ?CE.total_arg_bytes_cons; [cbn; lia|].
    cbn [length] in Hk. specialize (IH k ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  (* argv[k] with its NUL and the bytes up to the next multiple of 8, in the launch's string block; the string's
     NUL is at least 9 bytes (the exec name's NUL and the 8-byte slot) below ed_top *)
  Lemma entry_argv_str : forall k, (k < length av)%nat ->
    exists slack : list byte,
      bytes_at asegs m (bv_unsigned (CE.cat_argv_ptr (ed_top rdraw) av ev xfn k)) (nth k av [] ++ Z_to_bv 8 0 :: slack)
      /\ (- (bv_unsigned (CE.cat_argv_ptr (ed_top rdraw) av ev xfn k) + Z.of_nat (length (nth k av [])) + 1)) mod 8 <= Z.of_nat (length slack)
      /\ bv_unsigned (CE.cat_argv_ptr (ed_top rdraw) av ev xfn k) = amain_STR0 sp0 rdraw inp + Z.of_nat (F.total_arg_bytes_nat (firstn k av))
      /\ bv_unsigned (CE.cat_argv_ptr (ed_top rdraw) av ev xfn k) + Z.of_nat (length (nth k av [])) + 1 + 9
         <= bv_unsigned (ed_top rdraw).
  Proof.
    intros k Hk. pose proof usp_lo as LO. pose proof usp_hi as HI. pose proof top_facts as (TT & T8). pose proof lb_top as LT.
    pose proof str0_strings as SS. pose proof STR0_eq as SE.
    set (P := bv_unsigned (CE.cat_argv_ptr (ed_top rdraw) av ev xfn k)). set (str := nth k av []).
    assert (HP : P = bv_unsigned sp0 + Z.of_nat (CE.cat_string_off RB sp0 (ed_top rdraw) av ev xfn + F.total_arg_bytes_nat (firstn k av)))
      by (subst P; eapply RL.u_cat_argv_ptr with (v := Sv48) (brk := brk0) (ph := APH) (entry := RENT); first [lctx | exact Hk]).
    pose proof (total_firstn_nth av k Hk) as TF. fold str in TF.
    assert (LS : Z.of_nat (launch_string_bytes av ev xfn)
                 = Z.of_nat (F.total_arg_bytes_nat av) + Z.of_nat (F.total_arg_bytes_nat ev) + Z.of_nat (length xfn) + 1)
      by (unfold launch_string_bytes; rewrite !F.length_flatten_strings; lia).
    unfold usp in *.
    set (x := P + Z.of_nat (length str) + 1). set (pad := (- x) mod 8).
    assert (XT : x + 9 <= bv_unsigned (ed_top rdraw)) by (subst x; lia).
    pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as PB. fold pad in PB.
    pose proof (Z.div_mod (- x) 8 ltac:(lia)) as DX. fold pad in DX.
    pose proof (Z.div_mod (bv_unsigned (ed_top rdraw)) 8 ltac:(lia)) as DT. rewrite T8, Z.add_0_r in DT.
    assert (ROOM2 : x + pad + 8 <= bv_unsigned (ed_top rdraw)) by lia.
    clear TF.
    exists (firstn (Z.to_nat pad) (skipn (Z.to_nat (x - bv_unsigned sp0)) SIMG)).
    assert (LSL : length (firstn (Z.to_nat pad) (skipn (Z.to_nat (x - bv_unsigned sp0)) SIMG)) = Z.to_nat pad).
    { rewrite length_firstn, length_skipn. unfold LB in *. lia. }
    rewrite LSL.
    split; [| split; [lia| split; [rewrite HP, SE; lia| lia]]].
    replace (str ++ Z_to_bv 8 0 :: firstn (Z.to_nat pad) (skipn (Z.to_nat (x - bv_unsigned sp0)) SIMG))
      with ((str ++ [Z_to_bv 8 0]) ++ firstn (Z.to_nat pad) (skipn (Z.to_nat (x - bv_unsigned sp0)) SIMG)) by (rewrite <- app_assoc; reflexivity).
    apply (proj2 (bytes_at_app _ _ _ _ _)). split.
    - apply block_bytes; [rewrite SE; fold P; lia| rewrite length_app; cbn [length]; fold P; lia|].
      rewrite length_app. cbn [length]. fold str.
      unfold SIMG. eapply FS.read_argv_cstr_k; [exact LAU| exact Hk].
    - rewrite length_app. cbn [length]. fold str.
      pose proof (block_bytes (Z_to_bv 64 x) (firstn (Z.to_nat pad) (skipn (Z.to_nat (x - bv_unsigned sp0)) SIMG))) as B.
      rewrite unsigned_lit in B by lia. rewrite LSL in B.
      replace (P + Z.of_nat (length str + 1)) with x by lia. apply B; [rewrite SE; lia| lia|].
      rewrite F.rdn_stack; rewrite ?unsigned_lit by lia; [reflexivity| lia| unfold LB in *; lia| unfold LB in *; lia].
  Qed.


  (* [comment removed for export] *)
  Lemma high_bytes_wr : forall a bs, bytes_at asegs m a bs -> AIMG_HI <= a -> wr_at asegs m a (Z.of_nat (length bs)).
  Proof.
    intros a bs (H0 & H1 & H) Ha. split; [exact H0|]. split; [exact H1|]. intros i Hi.
    specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia.
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [| apply nth_error_None in E; lia].
    unfold mrd in H. destruct (m (wa (a + i))) as [b'|] eqn:Em; [unfold wview; rewrite Em; discriminate|]. exfalso.
    apply (seg_rom_seg asegs) in H. apply H.
    destruct (find_segment asegs (bv_unsigned (wa (a + i))) 1) as [seg|] eqn:F; [|reflexivity]. exfalso.
    (nelim (find_segment_in _ _ _ _ F) 3%nat; intros Hin Hr1 Hr2). rewrite wa_unsigned in Hr1, Hr2 by lia. unfold AIMG_HI in Ha.
    destruct (asegs_In seg Hin) as [(B & S & _)|[(B & S & _)|[(B & S & _)|(B & S & _)]]]; lia.
  Qed.

  Lemma V_argc : V 1%nat = Z.of_nat (length av). Proof. (nelimp ME_vars 7%nat; intros _ _ _ _ _ H _). exact H. Qed.
  Lemma V_envc : V 2%nat = Z.of_nat (length ev). Proof. (nelimp ME_vars 8%nat; intros _ _ _ _ _ _ H _). exact H. Qed.
  Lemma V_L0 : V 3%nat = Z.of_nat (length (nth 0 av [])). Proof. (nelimp ME_vars 9%nat; intros _ _ _ _ _ _ _ H _). exact H. Qed.
  Lemma V_W : V 4%nat = amain_W sp0 rdraw inp. Proof. (nelimp ME_vars 11%nat; intros _ _ _ _ _ _ _ _ _ H _). exact H. Qed.
  Lemma V_G : V 11%nat = Z.of_nat (block_items av ev mod 2).
  Proof. (nelimp ME_vars 15%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ H _). exact H. Qed.

  Lemma argc_pos : (1 <= length av)%nat.
  Proof. pose proof VA as [H _]. lia. Qed.

  (* the lowest string byte in the launch variables: the head is 8 (argc + envc + 3) bytes, the auxv
     (AUXSZ at the run's rseq flag), the gap 8 G and the 16 AT_RANDOM bytes, then the pad W *)
  Lemma STR0_V : amain_STR0 sp0 rdraw inp
                 = 32768 * V 0%nat + 16 * V 6%nat + 4096 * V 10%nat + 8 * V 1%nat + 8 * V 2%nat + 8 * V 11%nat + V 4%nat
                   + 40 + APCm.AUXSZ (APCm.rseq_z RB).
  Proof.
    pose proof usp_V as UV. pose proof V_argc as VA1. pose proof V_envc as VE1. pose proof V_G as VG. pose proof V_W as VW.
    unfold amain_STR0. rewrite <- VW. unfold block_head_size. cbv zeta.
    rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul, <- VG, <- APCm.AUXSZ_of.
    unfold block_items. unfold usp in UV. lia.
  Qed.

  (* argv[0]'s word at sp + 8 holds the lowest string address: the run's own fact, the first of the
     facts that depend on its rseq flag *)
  Lemma argv0_word : bytes_at asegs m (usp + 8) (word_to_le_bytes 8 (wz (amain_STR0 sp0 rdraw inp))).
  Proof.
    pose proof ME_facts_r as HF. pose proof STR0_V as SV. pose proof usp_V as UV.
    revert HF SV. generalize (kb_rseq (in_kernel inp)). intros [|] HF SV;
      pose proof (mfacts_nth asegs V m _ 0%nat _ HF eq_refl) as H; cbn [mfact_ok zv] in H;
      unfold APCm.AUXSZ, APCm.rseq_z in SV;
      match type of H with bytes_at _ _ ?A (word_to_le_bytes _ (Z_to_bv _ ?X)) =>
        replace (usp + 8) with A by lia; replace (amain_STR0 sp0 rdraw inp) with X by lia; exact H end.
  Qed.

  (* argv[1]'s word at sp + 16: the second of the facts that depend on the rseq flag, (1 < argc) times the
     address after argv[0]'s string *)
  Lemma argv1_word : length av = 2%nat ->
    bytes_at asegs m (usp + 16) (word_to_le_bytes 8 (wz (amain_STR0 sp0 rdraw inp + Z.of_nat (length (nth 0 av [])) + 1))).
  Proof.
    intros Hlen. pose proof ME_facts_r as HF. pose proof STR0_V as SV. pose proof usp_V as UV.
    pose proof V_argc as VA1. pose proof V_L0 as VL0. rewrite Hlen in VA1.
    revert HF SV. generalize (kb_rseq (in_kernel inp)). intros [|] HF SV;
      pose proof (mfacts_nth asegs V m _ 1%nat _ HF eq_refl) as H; cbn [mfact_ok zv] in H;
      unfold APCm.AUXSZ, APCm.rseq_z in SV; rewrite VA1 in H;
      change (Z.b2z (1 mod two64 <? Z.of_nat 2 mod two64)) with 1 in H; rewrite Z.mul_1_l in H;
      match type of H with bytes_at _ _ ?A (word_to_le_bytes _ (Z_to_bv _ ?X)) =>
        replace (usp + 16) with A by lia;
        replace (amain_STR0 sp0 rdraw inp + Z.of_nat (length (nth 0 av [])) + 1) with X by lia; exact H end.
  Qed.

  (* [comment removed for export] *)
  Lemma entry_argv0 : argv_str_at m (usp - 48) 0 (hd [] av).
  Proof.
    pose proof usp_lo as LO. pose proof usp_hi as HI. pose proof top_facts as (TT & _). pose proof STR0_eq as SE.
    pose proof argc_pos as AP.
    (nelim (entry_argv_str 0 ltac:(lia)) 5%nat; intros slack BY SLK HP HEND).
    change (firstn 0 av) with (@nil (list byte)) in HP. change (F.total_arg_bytes_nat []) with 0%nat in HP.
    assert (HD : nth 0 av [] = hd [] av) by (case (in_argv inp); [reflexivity| intros; reflexivity]).
    rewrite HD in BY, SLK, HEND.
    set (P := bv_unsigned (CE.cat_argv_ptr (ed_top rdraw) av ev xfn 0)) in *.
    exists P, slack. unfold zlength.
    split; [| split; [exact BY| split; [exact SLK| split; [unfold usp in *; lia| unfold usp in *; lia]]]].
    pose proof argv0_word as H.
    replace (amain_STR0 sp0 rdraw inp) with P in H by lia.
    replace (usp + 8) with (usp - 48 + 56 + 8 * Z.of_nat 0) in H by lia.
    split; [split; [cbn; exact (conj I I) | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact H]|].
    apply (high_bytes_wr _ _ H). unfold AIMG_HI. lia.
  Qed.


  (* [comment removed for export] *)
  Lemma entry_argv1 : length av = 2%nat -> argv_str_at m (usp - 48) 1 (nth 1 av []).
  Proof.
    intros Hlen.
    pose proof usp_lo as LO. pose proof usp_hi as HI. pose proof top_facts as (TT & _). pose proof STR0_eq as SE.
    (nelim (entry_argv_str 1 ltac:(lia)) 5%nat; intros slack BY SLK HP HEND).
    assert (TF : Z.of_nat (F.total_arg_bytes_nat (firstn 1 av)) = Z.of_nat (length (nth 0 av [])) + 1).
    { clear BY SLK HP HEND. revert Hlen. case (in_argv inp); [intros Hl; discriminate| intros a0 r Hl].
      change (firstn 1 (a0 :: r)) with [a0].
      rewrite CE.total_arg_bytes_cons. change (F.total_arg_bytes_nat []) with 0%nat. cbn [nth]. lia. }
    rewrite TF in HP. clear TF.
    set (P := bv_unsigned (CE.cat_argv_ptr (ed_top rdraw) av ev xfn 1)) in *.
    exists P, slack. unfold zlength.
    split; [| split; [exact BY| split; [exact SLK| split; [unfold usp in *; lia| unfold usp in *; lia]]]].
    pose proof (argv1_word Hlen) as H.
    replace (amain_STR0 sp0 rdraw inp + Z.of_nat (length (nth 0 av [])) + 1) with P in H by lia.
    replace (usp + 16) with (usp - 48 + 56 + 8 * Z.of_nat 1) in H by lia.
    split; [split; [cbn; exact (conj I I) | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact H]|].
    apply (high_bytes_wr _ _ H). unfold AIMG_HI. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition entry_lo : Z := usp - SWD.

  Lemma entry_lo_facts : stk asegs m entry_lo (usp - 48) /\ entry_lo + 2^22 <= usp - 48 /\ alloc_ceiling <= entry_lo
                         /\ ASTACK_BOTTOM usp <= entry_lo.
  Proof.
    pose proof usp_lo as LO. pose proof usp_hi as HI. pose proof SWD_range as SR.
    assert (B : usp - 8388608 - 4096 <= ASTACK_BOTTOM usp <= usp - 8388608 + 4096).
    { unfold ASTACK_BOTTOM, ASTACK_TOP, roundup. Z.div_mod_to_equations. lia. }
    unfold entry_lo. split.
    - destruct (stk_split asegs m (usp - SWD) (usp - 48) usp entry_stk ltac:(lia)) as [S3 _]. exact S3.
    - split; [lia|]. split; [rewrite HCEIL; fold usp; lia | lia].
  Qed.

End Entry.
End CeilWrap.
End AEntry.

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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface Drv_base Drv_iface2 Drv_stmt DrvTop MainExport.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AMainEntry.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AMainEntry.MainFactsAsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AMainEntry.
Import AEntry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section PerCeil.
Context {ACEIL : Ceil}.
Variables (AI : art_iface) (DI : drv_iface2 AI).

(* [comment removed for export] *)
Definition art_init_stmt : Prop :=
  forall (w : bool) (V : nat -> Z) (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput)
         (fs : Fs.Fs) (regs : bvmap 5 word) (m : word -> option byte) (mo : Model) (g : lghost),
    valid_sp sp0 -> valid_brk asegs brk0 -> valid_mmap_base mbase ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs fs -> entry_stack_fits sp0 (in_argv inp) (in_envp inp) ->
    valid_id (in_uid inp) -> valid_hwcap (in_hwcap inp) ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp ->
    alloc_ceiling = bv_unsigned sp0 - 8388608 ->
    a_main_entry w V sp0 brk0 mbase rdraw inp fs regs m mo g ->
    LOK asegs mo -> BINV mo g ->
    exists B0, DRV_B_MAIN <= B0
               /\ CJ_iface.ART AI (bv_unsigned sp0) (bv_unsigned sp0 - 48) [] [] [] B0 m mo g
               /\ Drv_iface2.ADRV AI DI DRV_CALLS m mo g.

(* [comment removed for export] *)
Definition a_main_at : Prop :=
  forall (w : bool) (V : nat -> Z) (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput)
         (fs : Fs.Fs) (regs : bvmap 5 word) (m : word -> option byte) (mo : Model) (g : lghost),
    valid_sp sp0 -> valid_brk asegs brk0 -> valid_mmap_base mbase ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs fs -> entry_stack_fits sp0 (in_argv inp) (in_envp inp) ->
    valid_id (in_uid inp) -> valid_hwcap (in_hwcap inp) ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp ->
    alloc_ceiling = bv_unsigned sp0 - 8388608 ->
    a_main_entry w V sp0 brk0 mbase rdraw inp fs regs m mo g ->
    LRZ asegs (MS (mkR_of regs) bvmap_empty (Z_to_bv 64 AM_MAIN) (Z_to_bv 32 0) None m (seg_rom asegs)) mo g (spec04 (in_argv inp) fs).

Theorem a_main_at_of : art_init_stmt -> a_main_stmt04 AI DI -> a_main_at.
Proof.
  intros HART HDRV w V sp0 brk0 mbase rdraw inp fs regs m mo g Hsp Hbrk Hmb Hva Hve Hfs Hfit Huid Hhw Hvl Hlau HCEIL ME.
  apply lrz_assume. intros _ HLOK HBINV.
  destruct (HART w V sp0 brk0 mbase rdraw inp fs regs m mo g Hsp Hbrk Hmb Hva Hve Hfs Hfit Huid Hhw Hvl Hlau HCEIL ME HLOK HBINV)
    as (B0 & HB0 & HA & HD).
  apply (HDRV (in_argv inp) fs _ mo g Hva).
  pose proof ME as (MV & MR & _).
  destruct MR as (R1 & R2 & R3 & R4 & R8 & R9 & R10 & R11 & _).
  (* [comment removed for export] *)
  change (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.PropExec.getr regs) with (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.getr regs) in R1, R2, R3, R4, R8, R9, R10, R11.
  pose proof MV as (_ & _ & _ & _ & _ & PARGC & _).
  (* every entry lemma takes the whole section context *)
  pose proof (usp_lo w V sp0 brk0 mbase rdraw inp fs regs m mo g ME Hva Hve Hsp Hvl Hlau HCEIL) as LO.
  pose proof (usp_hi w V sp0 brk0 mbase rdraw inp fs regs m mo g ME Hva Hve Hsp Hvl Hlau HCEIL) as HI.
  pose proof (usp_al w V sp0 brk0 mbase rdraw inp fs regs m mo g ME Hva Hve Hsp Hvl Hlau HCEIL) as AL.
  destruct (entry_lo_facts w V sp0 brk0 mbase rdraw inp fs regs m mo g ME Hva Hve Hsp Hvl Hlau HCEIL) as (STK & ROOM & CL & BOT).
  pose proof (entry_tid_range w V sp0 brk0 mbase rdraw inp fs regs m mo g ME Hva Hve Hsp Hvl Hlau HCEIL) as TID.
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
  split; [exact (entry_dmod w V sp0 brk0 mbase rdraw inp fs regs m mo g ME Hva Hve Hsp Hvl Hlau HCEIL)|].
  split; [exact STK|]. split; [exact ROOM|]. split; [exact CL|]. split; [lia|].
  split; [unfold sp_window_lo; lia|]. split; [Z.div_mod_to_equations; lia|]. split; [exact BOT|].
  split; [exact (entry_mem_inv w V sp0 brk0 mbase rdraw inp fs regs m mo g ME Hva Hve Hsp Hvl Hlau HCEIL)|].
  split; [exact (entry_adstat w V sp0 brk0 mbase rdraw inp fs regs m mo g ME Hva Hve Hsp Hvl Hlau HCEIL)|].
  split; [rewrite unsigned_lit by lia; exact TID|].
  split; [exact (entry_dicpt w V sp0 brk0 mbase rdraw inp fs regs m mo g ME Hva Hve Hsp Hvl Hlau HCEIL)|].
  split; [exact (entry_errno w V sp0 brk0 mbase rdraw inp fs regs m mo g ME Hva Hve Hsp Hvl Hlau HCEIL)|].
  split; [exact (entry_initflag w V sp0 brk0 mbase rdraw inp fs regs m mo g ME Hva Hve Hsp Hvl Hlau HCEIL)|].
  split; [exact (entry_stdout w V sp0 brk0 mbase rdraw inp fs regs m mo g ME Hva Hve Hsp Hvl Hlau HCEIL)|].
  split; [exact (entry_stderr w V sp0 brk0 mbase rdraw inp fs regs m mo g ME Hva Hve Hsp Hvl Hlau HCEIL)|].
  split; [exact (entry_stdin w V sp0 brk0 mbase rdraw inp fs regs m mo g ME Hva Hve Hsp Hvl Hlau HCEIL)|].
  split; [exact (entry_ssz w V sp0 brk0 mbase rdraw inp fs regs m mo g ME Hva Hve Hsp Hvl Hlau HCEIL)|].
  split; [eexists; exact (entry_rs w V sp0 brk0 mbase rdraw inp fs regs m mo g ME Hva Hve Hsp Hvl Hlau HCEIL)|].
  split; [exact (entry_argv0 w V sp0 brk0 mbase rdraw inp fs regs m mo g ME Hva Hve Hsp Hvl Hlau HCEIL)|].
  exact (entry_argv1 w V sp0 brk0 mbase rdraw inp fs regs m mo g ME Hva Hve Hsp Hvl Hlau HCEIL).
Qed.
End PerCeil.

(* [comment removed for export] *)
Theorem a_main_stmt_of :
  (forall ACEIL : Ceil, exists (AI : art_iface) (DI : drv_iface2 AI), art_init_stmt AI DI /\ a_main_stmt04 AI DI) -> a_main_stmt.
Proof.
  intros H ACEIL. destruct (H ACEIL) as (AI & DI & HA & HD). exact (a_main_at_of AI DI HA HD).
Qed.
