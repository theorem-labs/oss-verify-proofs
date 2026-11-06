(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ModelAmb.
From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require DispatchCompute.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RefStartupDefs.   (* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes Hoare Frame SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibStdioCall Spec ShapeLaws LibWritev RefExitBase RefStdioDefs RefExit RefMainEntry LibTail RefReadBase RefWorld RefReadErr_defs RefReadErr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require RefPilotOOM RefW65x.
From Stdlib Require ZArith NArith List Lia Bool.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SymExec SymExec2 SymExec2Sound SymDriveX Spec RefReadBase RefWorld RefReadStage RefReadErr RefRefused.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes ShapeLaws MmapSim AllocSim FileSim AgentLib MemSplit Frame SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib RefNodes LibKnowFrame LibKnowXfer RefReadLib RefReadBase RefReadStage RefReadChunk RefRead0 RefReadG0 RefReadG1 RefReadG4 RefReadG7 RefReadF1.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Spec RefReadBase RefWorld RefTargetPre RefReadStage RefWorldK RefTargetPreK RefHeaderK SymPlanSoundA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module RefOomTail.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.DispatchCompute.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SimInv OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ExitSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeAlg OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Nodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Hoare OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Frame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SpecConsts OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2Sound OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymRun OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDrive OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDriveX OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDriveH4 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibKnowFrame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibStdioCall OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Spec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeLaws OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibWritev OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefExitBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefStdioDefs OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefExit OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMainEntry OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibTail OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefWorld OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadErr_defs OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadErr.RefReadErr_tail OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadErr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPW_1. Context {fx : PropExec.FPState}.

Definition KEPT_OOM : list nat := [2; 3; 4]%nat.
Definition srOOM0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_OOM 6.

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x327dc srOOM0 [] knRE0 39.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA knRE0.
Definition ssA0' : sym_state := SS 0x3281c srOOM0 [] knRE0 39.
Definition rA' := Eval vm_compute in run scr0 ssA0'.
(* [comment removed for export] *)
Definition resB : stdio_res :=
  Eval vm_compute in match stdio_call 39 srA knA with Some r => r
                     | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Lemma resB_eq : stdio_call 39 srA knA = Some resB.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition srB0 : list expr := Eval vm_compute in sc_sr resB.
Definition knB0 : list kentry := Eval vm_compute in sc_kn resB.
Definition ssB0 : sym_state := SS 0x9b8d4 srB0 [] knB0 71.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knB0.

Lemma itinerary_oom :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0x9ba34%Z, [])
  /\ (fst (fst rA')) = (fst (fst rA)) /\ snd (fst rA') = []
  /\ (sc_ret resB, sc_f resB, sc_fd resB) = (0x9b8d4%Z, 0xb2ca0%Z, 2%Z)
  /\ (s_pc (fst (fst rB)), snd (fst rB)) = (0x96094%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section OomTail.
  Variable sp0 : word.
  Variable BL : list (list byte).
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  (* [comment removed for export] *)
  Lemma oom_sym : forall (pc : Z) vals R M,
    (pc = 0x327dc \/ pc = 0x3281c)%Z ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srOOM0 R -> know_ok RSEGS (ENV BL vals) M knRE0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model)
               (t_die msg_oom (m_fs model)).
  Proof.
    intros pc vals R M Hpc HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    assert (STEP : forall T,
      (forall R' M', regs_ok (ENV BL vals) srA R' -> know_ok RSEGS (ENV BL vals) M' knA ->
         realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x9ba34) M' (seg_rom RSEGS)) model) T) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model) T).
    { intros T HT. destruct Hpc as [-> | ->].
      - run_blk scr0 39%nat. apply HT; assumption.
      - run_blk scr0 39%nat. apply HT; assumption. }
    apply STEP. clear STEP HR HK R M. intros R M HR HK.
    (* [comment removed for export] *)
    RefW65x.RefW65.oom_stdio_exit HL P0 resB_eq Hfd2 (@eq_refl _ (m_fs model)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variables (tid : Z) (R : bvmap 5 word) (M : word -> option byte).
  Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).   (* [comment removed for export] *)
  Hypothesis Rgp : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis Rtp : getr R 4 = Z_to_bv 64 0xc4918.
  Hypothesis Mstack : stack_writable M sp0.
  Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
  Hypothesis Mtid : cell M 0xc4870 4 tid.
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  Hypothesis Mself : cell M 0xc4850 8 0xc4850.
  Variable can : Z.                              (* [comment removed for export] *)
  Hypothesis Hcan : (0 <= can < 2 ^ 64)%Z.
  Hypothesis Mcanary : cell M 0xe4b88 8 can.
  Hypothesis Mpagesz : cell M 0xe4bd8 8 4096.

  Definition valsOOM : list word := valsRE sp0 sp0 tid R can.
  Let E : env := ENV BL valsOOM.

  Lemma valsOOM_len : length valsOOM = 39%nat.
  Proof. apply valsRE_len. Qed.

  Lemma evOOM_junk : forall i, (1 <= i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof. intros i Hi. apply (evRE_junk sp0 BL sp0 tid R can i Hi). Qed.

  Ltac reg_caseOOM :=
    cbn [nth srOOM0 all_regs];
    first [ lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot E (EVar n)) with (ev E n);
              first [ rewrite (evOOM_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact Rgp | exact Rtp
          | rewrite Rsp, alu_add; change (ev E 0) with sp0; unfold v_add; apply bv_eq;
            rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia
          | idtac ].

  Lemma regs_okOOM : regs_ok E srOOM0 R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply (regs_ok_by_index1 sp0 Hvsp).
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ lia | .. | lia]; reg_caseOOM.
  Qed.

  Lemma know_okOOM : know_ok RSEGS E M knRE0.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply (know_okRE sp0 BL Hvsp sp0 tid R M Mstack Mimg Mtid Htid Mself can Hcan Mcanary Mpagesz); lia.
  Qed.

  Theorem ref_oom_tail : forall pc : Z, (pc = 0x327dc \/ pc = 0x3281c)%Z ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model)
               (t_die msg_oom (m_fs model)).
  Proof.
    intros pc Hpc.
    eapply (oom_sym pc valsOOM R M Hpc valsOOM_len eq_refl regs_okOOM know_okOOM).
  Qed.
End OomTail.
End FPW_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefOomTail.

(* [comment removed for export] *)
Module RefBigLeaves.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeAlg OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2Sound OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDriveX OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Spec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefWorld OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadStage OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadErr RefOomTail OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefRefused.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPW_2. Context {fx : PropExec.FPState}.

Lemma pres_cell : forall M0 M sp0 a n v,
  pres M0 M sp0 -> (0x10000 <= a)%Z -> (a + Z.of_nat n <= 0xe6000)%Z ->
  (forall i, (a <= i < a + Z.of_nat n)%Z -> ~ rd_cell i) ->
  cell M0 a n v -> cell M a n v.
Proof.
  intros M0 M sp0 a n v P Ha Hn Hrd C. unfold cell in *. rewrite <- C.
  apply rdn_agree. intros j Hj. rewrite (u_small a) by lia. apply P. left. rewrite u_small by lia.
  split; [lia|]. apply Hrd. lia.
Qed.

Lemma pres_img_clear : forall M0 M sp0 lo hi,
  pres M0 M sp0 -> (0x10000 <= lo)%Z -> (hi <= 0xe6000)%Z ->
  (forall i, (lo <= i < hi)%Z -> ~ rd_cell i) ->
  img_clear M0 lo hi -> img_clear M lo hi.
Proof.
  intros M0 M sp0 lo hi P Hlo Hhi Hrd C i Hi. rewrite (P (Z_to_bv 64 i)); [apply C; exact Hi|].
  left. rewrite u_small by lia. split; [lia|]. apply Hrd. exact Hi.
Qed.

Lemma re_ivs_pres : forall M0 M sp0,
  pres M0 M sp0 ->
  Forall (fun iv => img_clear M0 (fst iv) (snd iv)) re_ivs ->
  Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
Proof.
  intros M0 M sp0 P H. unfold re_ivs in *.
  repeat (apply Forall_cons_iff in H as [?C H]).
  repeat (apply Forall_cons; [eapply pres_img_clear; [exact P | cbn; lia | cbn; lia | unfold rd_cell; cbn; intros; lia | assumption] |]).
  apply Forall_nil.
Qed.

Section BigLeaves.
  Variables (sp0 gm : word) (area brkv mas sec : Z) (tid : word) (M0 : word -> option byte).   (* [comment removed for export] *)
  Variables (path : list byte) (stdin0 : AmbIn) (fs0 : Fs).
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis W : world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas (bv_unsigned tid) sec M0.

  Lemma leaf_facts : forall R M, oom_leaf sp0 M0 R M ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) /\ getr R 3 = Z_to_bv 64 0x10800 /\ getr R 4 = Z_to_bv 64 0xc4918
    /\ stack_writable M sp0
    /\ Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs
    /\ cell M 0xc4870 4 (bv_unsigned tid) /\ (0 < bv_unsigned tid < 2 ^ 22)%Z
    /\ cell M 0xc4850 8 0xc4850 /\ (exists c, (0 <= c < 2 ^ 64)%Z /\ cell M 0xe4b88 8 c) /\ cell M 0xe4bd8 8 4096.
  Proof.
    intros R M (Rsp & Rgp & Rtp & P & STK).
    destruct (w_canary _ _ _ _ _ _ _ _ W) as (c & Hc & Wc).
    repeat split; try assumption.
    - eapply re_ivs_pres; [exact P|]. apply re_ivs_of_world. exact (w_img _ _ _ _ _ _ _ _ W).
    - eapply pres_cell; [exact P | lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact (w_tid _ _ _ _ _ _ _ _ W)].
    - pose proof (w_tidr _ _ _ _ _ _ _ _ W). lia.
    - pose proof (w_tidr _ _ _ _ _ _ _ _ W). lia.
    - eapply pres_cell; [exact P | lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact (w_self _ _ _ _ _ _ _ _ W)].
    - exists c. split; [exact Hc|].
      eapply pres_cell; [exact P | lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact Wc].
    - eapply pres_cell; [exact P | lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact (w_pagesz _ _ _ _ _ _ _ _ W)].
  Qed.

  (* [comment removed for export] *)
  Theorem big_oom_branch : oom_branch sp0 path stdin0 fs0 tid M0 (t_die msg_oom fs0).
  Proof.
    intros R M off V HL.
    destruct (leaf_facts R M HL) as (Rsp & Rgp & Rtp & STK & IMG & Ctid & Htid & Cself & (c & Hc & Ccan) & Cpg).
    change fs0 with (m_fs (modelG path stdin0 fs0 tid off V)).
    apply (ref_oom_tail sp0 [] (modelG path stdin0 fs0 tid off V) Hvsp eq_refl eq_refl eq_refl (bv_unsigned tid) R M
             Rsp Rgp Rtp STK IMG Ctid Htid Cself c Hc Ccan Cpg 0x327dc).
    left. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem big_refused_leaf : forall R M off V, oom_leaf sp0 M0 R M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x327bc) M (seg_rom RSEGS)) (modelG path stdin0 fs0 tid off V))
               (t_die msg_refused fs0).
  Proof.
    intros R M off V HL.
    destruct (leaf_facts R M HL) as (Rsp & Rgp & Rtp & STK & IMG & Ctid & Htid & Cself & (c & Hc & Ccan) & Cpg).
    change fs0 with (m_fs (modelG path stdin0 fs0 tid off V)).
    apply (ref_refused_tail sp0 [] (modelG path stdin0 fs0 tid off V) Hvsp eq_refl eq_refl eq_refl (bv_unsigned tid) R M
             Rsp Rgp Rtp STK IMG Ctid Htid Cself c Hc Ccan Cpg).
  Qed.
End BigLeaves.
End FPW_2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefBigLeaves.

(* [comment removed for export] *)
Module RefReadBig.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeAlg OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Nodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeLaws OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MmapSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.AllocSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.FileSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.AgentLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MemSplit OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Frame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2Sound OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymRun OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDrive OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDriveX OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefNodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibKnowFrame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibKnowXfer OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadStage OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadChunk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefRead0 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadG0 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadG1 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadG1.RefReadG2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadG1.RefReadG3 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadG4 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadG4.RefReadG5 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadG4.RefReadG6 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadG7 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadG7.RefReadG8 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadG7.RefReadG9 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadF1 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadF1.RefReadF2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadF1.RefReadF3 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadF1.RefReadF4 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadF1.RefReadF5 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadF1.RefReadF6 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadF1.RefReadF7 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadF1.RefReadF8 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadF1.RefReadF9 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadF1.RefReadF10.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := ImgP.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPW_3. Context {fx : PropExec.FPState}.


Section Big.
  Variables (sp0 p1 mb gm can sec : word) (path content : list byte).   (* [comment removed for export] *)
  Variables (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadStage.modelG path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Definition post_cont (k : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post k sp0 p1 mb gm B e can sec content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32670) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)) K.

  Section Stages.
    Variables (M0 : word -> option byte) (K TOOM TREF : TSet).
    Hypothesis Hmb0 : (0x1000 <= bv_unsigned mb)%Z.
    Hypothesis Hmb1 : (bv_unsigned mb + 8192 <= bv_unsigned sp0 - 8388608)%Z.   (* [comment removed for export] *)
    Hypothesis Hmba : (bv_unsigned mb mod 4096 = 0)%Z.
    Hypothesis HspR : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z.
    Hypothesis HOOM : RefReadStage.oom_branch sp0 path stdin0 fs0 tid M0 TOOM.
    Hypothesis HREF : forall R' M' off V', oom_leaf sp0 M0 R' M' ->
      realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x327bc) M' (seg_rom RSEGS)) (modelG off V')) TREF.
    Hypothesis HPOST : forall k, (1 <= k <= 10)%Z -> (65536 * 2 ^ (k - 1) <= L < 65536 * 2 ^ k)%Z -> post_cont k M0 K.

    (* [comment removed for export] *)
    Definition SH10 : TSet := if (L <? 67108864)%Z then K else TREF.
    Definition SH9 : TSet := if (L <? 33554432)%Z then K else t_alt2 TOOM SH10.
    Definition SH8 : TSet := if (L <? 16777216)%Z then K else t_alt2 TOOM SH9.
    Definition SH7 : TSet := if (L <? 8388608)%Z then K else t_alt2 TOOM SH8.
    Definition SH6 : TSet := if (L <? 4194304)%Z then K else t_alt2 TOOM SH7.
    Definition SH5 : TSet := if (L <? 2097152)%Z then K else t_alt2 TOOM SH6.
    Definition SH4 : TSet := if (L <? 1048576)%Z then K else t_alt2 TOOM SH5.
    Definition SH3 : TSet := if (L <? 524288)%Z then K else t_alt2 TOOM SH4.
    Definition SH2 : TSet := if (L <? 262144)%Z then K else t_alt2 TOOM SH3.
    Definition SH1 : TSet := if (L <? 131072)%Z then K else t_alt2 TOOM SH2.


    Lemma HS10 : forall R M V B e, half 10 sp0 p1 mb gm L B e can sec content M0 R M V -> (33554432 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32640) M (seg_rom RSEGS)) (modelG (held_of 10) V)) SH10.
    Proof.
      intros R M V B e ST HGE. unfold SH10. change (held_of 10) with 33554432%Z.
      destruct (Z.ltb_spec L 67108864) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (RefReadF1.RefReadF10.fin10 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF1.RefReadF10.post_branch. apply (HPOST 10); [lia|].
        change (65536 * 2 ^ (10 - 1))%Z with 33554432%Z. change (65536 * 2 ^ 10)%Z with 67108864%Z. lia.
      - (* [comment removed for export] *)
        apply (RefReadF1.RefReadF10.fill10 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 TREF ST ltac:(lia) HspR).
        unfold RefReadF1.RefReadF10.full_branch. intros R' M' V' B' e' ST'. change (cap_of 10) with 67108864%Z.
        exact (RefReadF1.RefReadF10.refused10 sp0 p1 mb gm can sec path content stdin0 fs0 tid R' M' V' B' e' M0 TREF ST' HspR HREF).
    Qed.

    Lemma HS9 : forall R M V B e, half 9 sp0 p1 mb gm L B e can sec content M0 R M V -> (16777216 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32640) M (seg_rom RSEGS)) (modelG (held_of 9) V)) SH9.
    Proof.
      intros R M V B e ST HGE. unfold SH9. change (held_of 9) with 16777216%Z.
      destruct (Z.ltb_spec L 33554432) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (RefReadF1.RefReadF9.fin9 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF1.RefReadF9.post_branch. apply (HPOST 9); [lia|].
        change (65536 * 2 ^ (9 - 1))%Z with 16777216%Z. change (65536 * 2 ^ 9)%Z with 33554432%Z. lia.
      - (* [comment removed for export] *)
        apply (RefReadF1.RefReadF9.fill9 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 (t_alt2 TOOM SH10) ST ltac:(lia) HspR).
        unfold RefReadF1.RefReadF9.full_branch. intros R' M' V' B' e' ST'. change (cap_of 9) with 33554432%Z.
        apply (RefReadG7.RefReadG9.grow9 sp0 p1 mb gm can sec path content stdin0 fs0 tid R' M' V' B' e' M0 SH10 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold RefReadG7.RefReadG9.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS10 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS8 : forall R M V B e, half 8 sp0 p1 mb gm L B e can sec content M0 R M V -> (8388608 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32640) M (seg_rom RSEGS)) (modelG (held_of 8) V)) SH8.
    Proof.
      intros R M V B e ST HGE. unfold SH8. change (held_of 8) with 8388608%Z.
      destruct (Z.ltb_spec L 16777216) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (RefReadF1.RefReadF8.fin8 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF1.RefReadF8.post_branch. apply (HPOST 8); [lia|].
        change (65536 * 2 ^ (8 - 1))%Z with 8388608%Z. change (65536 * 2 ^ 8)%Z with 16777216%Z. lia.
      - (* [comment removed for export] *)
        apply (RefReadF1.RefReadF8.fill8 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 (t_alt2 TOOM SH9) ST ltac:(lia) HspR).
        unfold RefReadF1.RefReadF8.full_branch. intros R' M' V' B' e' ST'. change (cap_of 8) with 16777216%Z.
        apply (RefReadG7.RefReadG8.grow8 sp0 p1 mb gm can sec path content stdin0 fs0 tid R' M' V' B' e' M0 SH9 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold RefReadG7.RefReadG8.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS9 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS7 : forall R M V B e, half 7 sp0 p1 mb gm L B e can sec content M0 R M V -> (4194304 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32640) M (seg_rom RSEGS)) (modelG (held_of 7) V)) SH7.
    Proof.
      intros R M V B e ST HGE. unfold SH7. change (held_of 7) with 4194304%Z.
      destruct (Z.ltb_spec L 8388608) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (RefReadF1.RefReadF7.fin7 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF1.RefReadF7.post_branch. apply (HPOST 7); [lia|].
        change (65536 * 2 ^ (7 - 1))%Z with 4194304%Z. change (65536 * 2 ^ 7)%Z with 8388608%Z. lia.
      - (* [comment removed for export] *)
        apply (RefReadF1.RefReadF7.fill7 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 (t_alt2 TOOM SH8) ST ltac:(lia) HspR).
        unfold RefReadF1.RefReadF7.full_branch. intros R' M' V' B' e' ST'. change (cap_of 7) with 8388608%Z.
        apply (RefReadG7.grow7 sp0 p1 mb gm can sec path content stdin0 fs0 tid R' M' V' B' e' M0 SH8 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold RefReadG7.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS8 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS6 : forall R M V B e, half 6 sp0 p1 mb gm L B e can sec content M0 R M V -> (2097152 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32640) M (seg_rom RSEGS)) (modelG (held_of 6) V)) SH6.
    Proof.
      intros R M V B e ST HGE. unfold SH6. change (held_of 6) with 2097152%Z.
      destruct (Z.ltb_spec L 4194304) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (RefReadF1.RefReadF6.fin6 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF1.RefReadF6.post_branch. apply (HPOST 6); [lia|].
        change (65536 * 2 ^ (6 - 1))%Z with 2097152%Z. change (65536 * 2 ^ 6)%Z with 4194304%Z. lia.
      - (* [comment removed for export] *)
        apply (RefReadF1.RefReadF6.fill6 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 (t_alt2 TOOM SH7) ST ltac:(lia) HspR).
        unfold RefReadF1.RefReadF6.full_branch. intros R' M' V' B' e' ST'. change (cap_of 6) with 4194304%Z.
        apply (RefReadG4.RefReadG6.grow6 sp0 p1 mb gm can sec path content stdin0 fs0 tid R' M' V' B' e' M0 SH7 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold RefReadG4.RefReadG6.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS7 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS5 : forall R M V B e, half 5 sp0 p1 mb gm L B e can sec content M0 R M V -> (1048576 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32640) M (seg_rom RSEGS)) (modelG (held_of 5) V)) SH5.
    Proof.
      intros R M V B e ST HGE. unfold SH5. change (held_of 5) with 1048576%Z.
      destruct (Z.ltb_spec L 2097152) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (RefReadF1.RefReadF5.fin5 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF1.RefReadF5.post_branch. apply (HPOST 5); [lia|].
        change (65536 * 2 ^ (5 - 1))%Z with 1048576%Z. change (65536 * 2 ^ 5)%Z with 2097152%Z. lia.
      - (* [comment removed for export] *)
        apply (RefReadF1.RefReadF5.fill5 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 (t_alt2 TOOM SH6) ST ltac:(lia) HspR).
        unfold RefReadF1.RefReadF5.full_branch. intros R' M' V' B' e' ST'. change (cap_of 5) with 2097152%Z.
        apply (RefReadG4.RefReadG5.grow5 sp0 p1 mb gm can sec path content stdin0 fs0 tid R' M' V' B' e' M0 SH6 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold RefReadG4.RefReadG5.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS6 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS4 : forall R M V B e, half 4 sp0 p1 mb gm L B e can sec content M0 R M V -> (524288 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32640) M (seg_rom RSEGS)) (modelG (held_of 4) V)) SH4.
    Proof.
      intros R M V B e ST HGE. unfold SH4. change (held_of 4) with 524288%Z.
      destruct (Z.ltb_spec L 1048576) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (RefReadF1.RefReadF4.fin4 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF1.RefReadF4.post_branch. apply (HPOST 4); [lia|].
        change (65536 * 2 ^ (4 - 1))%Z with 524288%Z. change (65536 * 2 ^ 4)%Z with 1048576%Z. lia.
      - (* [comment removed for export] *)
        apply (RefReadF1.RefReadF4.fill4 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 (t_alt2 TOOM SH5) ST ltac:(lia) HspR).
        unfold RefReadF1.RefReadF4.full_branch. intros R' M' V' B' e' ST'. change (cap_of 4) with 1048576%Z.
        apply (RefReadG4.grow4 sp0 p1 mb gm can sec path content stdin0 fs0 tid R' M' V' B' e' M0 SH5 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold RefReadG4.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS5 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS3 : forall R M V B e, half 3 sp0 p1 mb gm L B e can sec content M0 R M V -> (262144 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32640) M (seg_rom RSEGS)) (modelG (held_of 3) V)) SH3.
    Proof.
      intros R M V B e ST HGE. unfold SH3. change (held_of 3) with 262144%Z.
      destruct (Z.ltb_spec L 524288) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (RefReadF1.RefReadF3.fin3 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF1.RefReadF3.post_branch. apply (HPOST 3); [lia|].
        change (65536 * 2 ^ (3 - 1))%Z with 262144%Z. change (65536 * 2 ^ 3)%Z with 524288%Z. lia.
      - (* [comment removed for export] *)
        apply (RefReadF1.RefReadF3.fill3 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 (t_alt2 TOOM SH4) ST ltac:(lia) HspR).
        unfold RefReadF1.RefReadF3.full_branch. intros R' M' V' B' e' ST'. change (cap_of 3) with 524288%Z.
        apply (RefReadG1.RefReadG3.grow3 sp0 p1 mb gm can sec path content stdin0 fs0 tid R' M' V' B' e' M0 SH4 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold RefReadG1.RefReadG3.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS4 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS2 : forall R M V B e, half 2 sp0 p1 mb gm L B e can sec content M0 R M V -> (131072 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32640) M (seg_rom RSEGS)) (modelG (held_of 2) V)) SH2.
    Proof.
      intros R M V B e ST HGE. unfold SH2. change (held_of 2) with 131072%Z.
      destruct (Z.ltb_spec L 262144) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (RefReadF1.RefReadF2.fin2 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF1.RefReadF2.post_branch. apply (HPOST 2); [lia|].
        change (65536 * 2 ^ (2 - 1))%Z with 131072%Z. change (65536 * 2 ^ 2)%Z with 262144%Z. lia.
      - (* [comment removed for export] *)
        apply (RefReadF1.RefReadF2.fill2 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 (t_alt2 TOOM SH3) ST ltac:(lia) HspR).
        unfold RefReadF1.RefReadF2.full_branch. intros R' M' V' B' e' ST'. change (cap_of 2) with 262144%Z.
        apply (RefReadG1.RefReadG2.grow2 sp0 p1 mb gm can sec path content stdin0 fs0 tid R' M' V' B' e' M0 SH3 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold RefReadG1.RefReadG2.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS3 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS1 : forall R M V B e, half 1 sp0 p1 mb gm L B e can sec content M0 R M V -> (65536 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32640) M (seg_rom RSEGS)) (modelG (held_of 1) V)) SH1.
    Proof.
      intros R M V B e ST HGE. unfold SH1. change (held_of 1) with 65536%Z.
      destruct (Z.ltb_spec L 131072) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (RefReadF1.fin1 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF1.post_branch. apply (HPOST 1); [lia|].
        change (65536 * 2 ^ (1 - 1))%Z with 65536%Z. change (65536 * 2 ^ 1)%Z with 131072%Z. lia.
      - (* [comment removed for export] *)
        apply (RefReadF1.fill1 sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M V B e M0 (t_alt2 TOOM SH2) ST ltac:(lia) HspR).
        unfold RefReadF1.full_branch. intros R' M' V' B' e' ST'. change (cap_of 1) with 131072%Z.
        apply (RefReadG1.grow1 sp0 p1 mb gm can sec path content stdin0 fs0 tid R' M' V' B' e' M0 SH2 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold RefReadG1.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS2 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    (* [comment removed for export] *)
    Definition FINAL : TSet := if (L <? 67108864)%Z then K else TREF.

    Lemma SH10_norm : t_eq (t_alt2 TOOM SH10) (t_alt2 TOOM FINAL).
    Proof. unfold SH10, FINAL. apply t_eq_refl. Qed.

    Lemma SH9_norm : t_eq (t_alt2 TOOM SH9) (t_alt2 TOOM FINAL).
    Proof.
      unfold SH9. destruct (Z.ltb_spec L 33554432) as [HLT|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - eapply t_eq_trans; [apply t_alt2_absorb | apply SH10_norm].
    Qed.

    Lemma SH8_norm : t_eq (t_alt2 TOOM SH8) (t_alt2 TOOM FINAL).
    Proof.
      unfold SH8. destruct (Z.ltb_spec L 16777216) as [HLT|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - eapply t_eq_trans; [apply t_alt2_absorb | apply SH9_norm].
    Qed.

    Lemma SH7_norm : t_eq (t_alt2 TOOM SH7) (t_alt2 TOOM FINAL).
    Proof.
      unfold SH7. destruct (Z.ltb_spec L 8388608) as [HLT|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - eapply t_eq_trans; [apply t_alt2_absorb | apply SH8_norm].
    Qed.

    Lemma SH6_norm : t_eq (t_alt2 TOOM SH6) (t_alt2 TOOM FINAL).
    Proof.
      unfold SH6. destruct (Z.ltb_spec L 4194304) as [HLT|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - eapply t_eq_trans; [apply t_alt2_absorb | apply SH7_norm].
    Qed.

    Lemma SH5_norm : t_eq (t_alt2 TOOM SH5) (t_alt2 TOOM FINAL).
    Proof.
      unfold SH5. destruct (Z.ltb_spec L 2097152) as [HLT|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - eapply t_eq_trans; [apply t_alt2_absorb | apply SH6_norm].
    Qed.

    Lemma SH4_norm : t_eq (t_alt2 TOOM SH4) (t_alt2 TOOM FINAL).
    Proof.
      unfold SH4. destruct (Z.ltb_spec L 1048576) as [HLT|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - eapply t_eq_trans; [apply t_alt2_absorb | apply SH5_norm].
    Qed.

    Lemma SH3_norm : t_eq (t_alt2 TOOM SH3) (t_alt2 TOOM FINAL).
    Proof.
      unfold SH3. destruct (Z.ltb_spec L 524288) as [HLT|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - eapply t_eq_trans; [apply t_alt2_absorb | apply SH4_norm].
    Qed.

    Lemma SH2_norm : t_eq (t_alt2 TOOM SH2) (t_alt2 TOOM FINAL).
    Proof.
      unfold SH2. destruct (Z.ltb_spec L 262144) as [HLT|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - eapply t_eq_trans; [apply t_alt2_absorb | apply SH3_norm].
    Qed.

    Lemma SH1_norm : t_eq (t_alt2 TOOM SH1) (t_alt2 TOOM FINAL).
    Proof.
      unfold SH1. destruct (Z.ltb_spec L 131072) as [HLT|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - eapply t_eq_trans; [apply t_alt2_absorb | apply SH2_norm].
    Qed.

  End Stages.

  Theorem read_big : forall R M VM K TOOM TREF,
    read_pre sp0 p1 mb gm can sec R M -> vm_pre VM sp0 mb gm ->   (* [comment removed for export] *)
    (forall i, (0 <= i < 0x1000)%Z -> M (Z_to_bv 64 i) = None) ->
    (65536 <= L)%Z ->
    RefReadStage.oom_branch sp0 path stdin0 fs0 tid M TOOM ->
    (forall R' M' off V', oom_leaf sp0 M R' M' ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x327bc) M' (seg_rom RSEGS)) (modelG off V')) TREF) ->
    (forall k, (1 <= k <= 10)%Z -> (65536 * 2 ^ (k - 1) <= L < 65536 * 2 ^ k)%Z -> post_cont k M K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x325c8) M (seg_rom RSEGS)) (modelG 0 VM))
             (t_alt2 TOOM (if (L <? 67108864)%Z then K else TREF)).
  Proof.
    intros R M VM K TOOM TREF RP VP Hpage0 HL64 HOOM HREF HPOST.
    pose proof (rp_sp0 _ _ _ _ _ _ _ _ RP) as Hsp. pose proof (rp_b _ _ _ _ _ _ _ _ RP) as Hmb. pose proof (rp_gm _ _ _ _ _ _ _ _ RP) as Hgm.
    destruct (rp_errno _ _ _ _ _ _ _ _ RP) as [e He].
    apply (rz_conseq RSEGS _ (t_alt2 TOOM (SH1 K TOOM TREF))).
    - change (modelG 0 VM) with (model_pre path VM stdin0 fs0 tid).
      apply (RefRead0.read_full0 sp0 p1 mb gm can sec path content VM stdin0 fs0 tid Hfile R M _ e RP HL64 He Hpage0).
      intros R' M' F0 _.
      apply (RefReadG0.grow0 sp0 p1 mb gm can sec path content VM stdin0 fs0 tid R' M' e M (SH1 K TOOM TREF) TOOM F0 VP HL64
               (proj1 Hsp) (proj1 Hmb) (proj1 (proj2 Hmb)) (proj2 (proj2 Hmb)) (proj1 Hgm) (proj1 (proj2 Hgm)) (proj2 (proj2 Hgm)) HOOM).
      unfold RefReadG0.half1_branch. intros R'' M'' V'' B'' e'' ST''.
      apply (HS1 M K TOOM TREF (proj1 Hmb) (proj1 (proj2 Hmb)) (proj2 (proj2 Hmb)) (proj1 Hsp) HOOM HREF HPOST R'' M'' V'' B'' e'' ST''). lia.
    - change (if (L <? 67108864)%Z then K else TREF) with (FINAL K TREF).
      apply (SH1_norm K TOOM TREF).
  Qed.
End Big.
End FPW_3.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefReadBig.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeAlg OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Spec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefWorld OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefTargetPre OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadStage RefReadBig RefBigLeaves OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefWorldK OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefTargetPreK OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefHeaderK OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymPlanSoundA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Section FPW_4. Context {fx : PropExec.FPState}.


Section BigFile.
  (* [comment removed for export] *)
  Hypothesis target_phase_k : forall (k : Z), (1 <= k <= 10)%Z ->
    forall (sp0 B area brkv mas tid sec : Z) (content : list byte)
           (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (model : Model),
      target_pre_k k sp0 B area brkv mas tid sec content R M -> target_vm_k k sp0 B area VM -> SPSA.std_model VM model ->   (* [comment removed for export] *)
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32844) M (seg_rom RSEGS)) model) (t_target content (m_fs model)).

Lemma ref_big_file : forall (sp0 p1 mb gm can sec : word) (R : bvmap 5 word) (M : word -> option byte)   (* [comment removed for export] *)
    (area brkv mas : Z) (VM : VmMaps) (path content : list byte) (stdin0 : AmbIn) (fs0 : Fs) (tid : word),
  fs_lookup fs0 path = Some content -> (65536 <= Z.of_nat (length content))%Z ->
  area = (bv_unsigned mb + 4096)%Z ->
  read_pre sp0 p1 mb gm can sec R M ->
  world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned sec) M ->
  main_frame (bv_unsigned sp0) M ->
  vm_pre VM sp0 mb gm ->
  vm_reserved VM = segments_reserved RSEGS /\ (2 ^ 31 <= vm_limit VM)%Z
  /\ (length (vm_maps VM) <= 4)%nat /\ In (gm, Z_to_bv 64 69632) (vm_maps VM)
  /\ Forall (fun p => (0 < bv_unsigned (snd p) <= 69632)%Z /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) (vm_maps VM)
  /\ seps (vm_maps VM) ->
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x325c8) M (seg_rom RSEGS))
                          (model_pre path VM stdin0 fs0 tid))
             (t_alt2 (t_die msg_oom fs0) (t_body content fs0)).
Proof.
  intros sp0 p1 mb gm can sec R M area brkv mas VM path content stdin0 fs0 tid Hfile HL Harea RP W MF VP VS.
  set (L := Z.of_nat (length content)) in *.
  assert (Hvsp : valid_sp sp0).
  { pose proof (rp_sp0 _ _ _ _ _ _ _ _ RP) as Hs. unfold valid_sp, sp_window_lo, sp_window_hi. lia. }
  assert (Hpage0 : forall i, (0 <= i < 0x1000)%Z -> M (Z_to_bv 64 i) = None).
  { pose proof (w_img _ _ _ _ _ _ _ _ W) as Wi. apply (proj1 (Forall_forall _ _) Wi (0%Z, 0x1000%Z)). cbn. left. reflexivity. }
  (* [comment removed for export] *)
  apply (rz_conseq RSEGS _ (t_alt2 (t_die msg_oom fs0) (if (L <? 67108864)%Z then t_body content fs0 else t_die msg_refused fs0))).
  2:{ destruct (Z.ltb_spec0 L 67108864) as [Hs|Hb]; [apply t_eq_refl|].
      unfold t_body, MAX_INPUT. subst L. rewrite (proj2 (Z.leb_le _ _)) by lia. apply t_eq_refl. }
  change (model_pre path VM stdin0 fs0 tid) with (RefReadStage.modelG path stdin0 fs0 tid 0 VM).
  apply (read_big sp0 p1 mb gm can sec path content stdin0 fs0 tid Hfile R M VM
           (t_body content fs0) (t_die msg_oom fs0) (t_die msg_refused fs0) RP VP Hpage0 HL).
  - (* [comment removed for export] *)
    apply (big_oom_branch sp0 gm area brkv mas (bv_unsigned sec) tid M path stdin0 fs0 Hvsp W).
  - (* [comment removed for export] *)
    apply (big_refused_leaf sp0 gm area brkv mas (bv_unsigned sec) tid M path stdin0 fs0 Hvsp W).
  - (* [comment removed for export] *)
    intros k Hk Hrange. unfold post_cont. intros R' M' V' B e RQ.
    apply (header_phase_k k sp0 p1 mb gm B e can sec tid area brkv mas content M R' M' V' stdin0 fs0 Hk Hvsp RQ W MF).
    + unfold capk. subst L. exact Hrange.
    + intros R'' M'' TPK TVK.
      pose proof (target_phase_k k Hk (bv_unsigned sp0) (bv_unsigned B) area brkv mas (bv_unsigned tid) (bv_unsigned sec) content
                    R'' M'' V' (model_post V' stdin0 fs0 tid) TPK TVK (SPSA.std_model_mk _ _ _ _ _)) as X.
      exact X.
Qed.
End BigFile.

End FPW_4.
