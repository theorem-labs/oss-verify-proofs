(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb.
From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes Hoare Frame SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame HULibStdioCall Spec ShapeLaws LibWritev HUExitBase HUStdioDefs HUExit HUMainEntryDefs LibTail HUReadBase HUWorld HUReadErr_defs HUReadErr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require HUPilotOOM HUW65x.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SymExec SymExec2 SymExec2Sound SymDriveX Spec HUReadBase HUWorld HUReadStage HUReadErr HURefused.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)

Module HUOomTail.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PropExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SeqExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StoreOk OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SimInv OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ExitSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ShapeAlg OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Nodes OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Hoare OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Frame OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SpecConsts OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2 OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2Sound OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymRun OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDrive OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDriveX OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDriveH4 OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibKnowFrame HULibStdioCall Spec ShapeLaws OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibWritev HUExitBase HUStdioDefs HUExit HUMainEntryDefs OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibTail HUReadBase HUWorld HUReadErr_defs HUReadErr.H0ReadErr_tail HUReadErr.
Import ConeCfg.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
  (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition KEPT_OOM : list nat := [2; 3; 4]%nat.
Definition srOOM0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_OOM 6.

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0xe1c1c srOOM0 [] knRE0 39.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA knRE0.
Definition ssA0' : sym_state := SS 0xe1c64 srOOM0 [] knRE0 39.
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
Definition ssB0 : sym_state := SS 0x2b5f50 srB0 [] knB0 71.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knB0.

Lemma itinerary_oom :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0x2b55ac%Z, [])
  /\ (fst (fst rA')) = (fst (fst rA)) /\ snd (fst rA') = []
  /\ (sc_ret resB, sc_f resB, sc_fd resB) = (0x2b5f50%Z, 0x31ebd0%Z, 2%Z)
  /\ (s_pc (fst (fst rB)), snd (fst rB)) = (0x2b17ec%Z, []).
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
    (pc = 0xe1c1c \/ pc = 0xe1c64)%Z ->
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
         realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x2b55ac) M' (seg_rom RSEGS)) model) T) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model) T).
    { intros T HT. destruct Hpc as [-> | ->].
      - run_blk scr0 39%nat. apply HT; assumption.
      - run_blk scr0 39%nat. apply HT; assumption. }
    apply STEP. clear STEP HR HK R M. intros R M HR HK.
    (* [comment removed for export] *)
    HUW65x.H0W65.oom_stdio_exit HL P0 resB_eq Hfd2 (@eq_refl _ (m_fs model)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variables (tid can : Z) (R : bvmap 5 word) (M : word -> option byte).   (* [comment removed for export] *)
  Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
  Hypothesis Rgp : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis Rtp : getr R 4 = Z_to_bv 64 0x331ae8.
  Hypothesis Mstack : stack_writable M sp0.
  Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
  Hypothesis Mtid : cell M 0x331a40 4 tid.
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  Hypothesis Mself : cell M 0x331a20 8 0x331a20.
  Hypothesis Mcanary : cell M 0x351b28 8 can.
  Hypothesis Hcan : (0 <= can < 2 ^ 64)%Z.
  Hypothesis Mpagesz : cell M 0x351da8 8 4096.

  Definition valsOOM : list word := valsRE sp0 sp0 tid can R.
  Let E : env := ENV BL valsOOM.

  Lemma valsOOM_len : length valsOOM = 39%nat.
  Proof. apply valsRE_len. Qed.

  Lemma evOOM_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof. intros i Hi. apply (evRE_junk sp0 BL sp0 tid can R i Hi). Qed.

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
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseOOM.
  Qed.

  Lemma know_okOOM : know_ok RSEGS E M knRE0.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply (know_okRE sp0 BL Hvsp sp0 tid can R M Mstack Mimg Mtid Htid Mself Mcanary Hcan Mpagesz); lia.
  Qed.

  Theorem ref_oom_tail : forall pc : Z, (pc = 0xe1c1c \/ pc = 0xe1c64)%Z ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model)
               (t_die msg_oom (m_fs model)).
  Proof.
    intros pc Hpc.
    eapply (oom_sym pc valsOOM R M Hpc valsOOM_len eq_refl regs_okOOM know_okOOM).
  Qed.
End OomTail.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End HUOomTail.

(* [comment removed for export] *)
Module H0BigLeaves.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PropExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SeqExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StoreOk OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ShapeAlg OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2 OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2Sound OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDriveX Spec HUReadBase HUWorld HUReadStage HUReadErr HUOomTail HURefused.
Import ConeCfg.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma pres_cell : forall M0 M sp0 a n v,
  pres M0 M sp0 -> (0x10000 <= a)%Z -> (a + Z.of_nat n <= 0x354000)%Z ->
  (forall i, (a <= i < a + Z.of_nat n)%Z -> ~ rd_cell i) ->
  cell M0 a n v -> cell M a n v.
Proof.
  intros M0 M sp0 a n v P Ha Hn Hrd C. unfold cell in *. rewrite <- C.
  apply rdn_agree. intros j Hj. rewrite (u_small a) by lia. apply P. left. rewrite u_small by lia.
  split; [lia|]. apply Hrd. lia.
Qed.

Lemma pres_img_clear : forall M0 M sp0 lo hi,
  pres M0 M sp0 -> (0x10000 <= lo)%Z -> (hi <= 0x354000)%Z ->
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
  Variables (sp0 gm : word) (area brkv mas : Z) (tid can sec : word) (M0 : word -> option byte).
  Variables (path : list byte) (stdin0 : AmbIn) (fs0 : Fs).
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis W : world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned can) (bv_unsigned sec) M0.

  Lemma leaf_facts : forall R M, oom_leaf sp0 M0 R M ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) /\ getr R 3 = Z_to_bv 64 0x10800 /\ getr R 4 = Z_to_bv 64 0x331ae8
    /\ stack_writable M sp0
    /\ Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs
    /\ cell M 0x331a40 4 (bv_unsigned tid) /\ (0 < bv_unsigned tid < 2 ^ 22)%Z
    /\ cell M 0x331a20 8 0x331a20 /\ cell M 0x351b28 8 (bv_unsigned can) /\ cell M 0x351da8 8 4096.
  Proof.
    intros R M (Rsp & Rgp & Rtp & P & STK).
    repeat split; try assumption.
    - eapply re_ivs_pres; [exact P|]. apply re_ivs_of_world. exact (w_img _ _ _ _ _ _ _ _ _ W).
    - eapply pres_cell; [exact P | lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact (w_tid _ _ _ _ _ _ _ _ _ W)].
    - pose proof (w_tidr _ _ _ _ _ _ _ _ _ W). lia.
    - pose proof (w_tidr _ _ _ _ _ _ _ _ _ W). lia.
    - eapply pres_cell; [exact P | lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact (w_self _ _ _ _ _ _ _ _ _ W)].
    - eapply pres_cell; [exact P | lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact (w_canary _ _ _ _ _ _ _ _ _ W)].
    - eapply pres_cell; [exact P | lia | cbn; lia | unfold rd_cell; cbn; intros; lia | exact (w_pagesz _ _ _ _ _ _ _ _ _ W)].
  Qed.

  (* [comment removed for export] *)
  Theorem big_oom_branch : oom_branch sp0 path stdin0 fs0 tid M0 (t_die msg_oom fs0).
  Proof.
    intros R M off V HL. pose proof (u64_range can) as Hcan.
    destruct (leaf_facts R M HL) as (Rsp & Rgp & Rtp & STK & IMG & Ctid & Htid & Cself & Ccan & Cpg).
    change fs0 with (m_fs (modelG path stdin0 fs0 tid off V)).
    apply (ref_oom_tail sp0 [] (modelG path stdin0 fs0 tid off V) Hvsp eq_refl eq_refl eq_refl (bv_unsigned tid) (bv_unsigned can) R M
             Rsp Rgp Rtp STK IMG Ctid Htid Cself Ccan Hcan Cpg 0xe1c1c).
    left. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem big_refused_leaf : forall R M off V, oom_leaf sp0 M0 R M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xe1bf8) M (seg_rom RSEGS)) (modelG path stdin0 fs0 tid off V))
               (t_die msg_refused fs0).
  Proof.
    intros R M off V HL. pose proof (u64_range can) as Hcan.
    destruct (leaf_facts R M HL) as (Rsp & Rgp & Rtp & STK & IMG & Ctid & Htid & Cself & Ccan & Cpg).
    change fs0 with (m_fs (modelG path stdin0 fs0 tid off V)).
    apply (ref_refused_tail sp0 [] (modelG path stdin0 fs0 tid off V) Hvsp eq_refl eq_refl eq_refl (bv_unsigned tid) (bv_unsigned can) R M
             Rsp Rgp Rtp STK IMG Ctid Htid Cself Ccan Hcan Cpg).
  Qed.
End BigLeaves.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End H0BigLeaves.
