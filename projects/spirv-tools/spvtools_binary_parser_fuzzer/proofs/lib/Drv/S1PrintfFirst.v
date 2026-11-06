(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk MemSplit Frame Hoare ShapeAlg ShapeLaws Nodes RefNodes
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymAux RefMemcpyLib SRealizes SNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1StartInit S1SpecConsts S1Spec S1StdioDefs S1StdioWrite S1PrintfBufBase S1KnCut2 S1_code_d6138_d7138.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FXDEFS.
Context {fx : FPState}.

Definition PF1_ENTRY : Z := 0x65a40.
Definition PF1_RET : Z := 0x65994.
Definition PF1_IOCTL : Z := 0xd6430.
Definition PF1_SW : Z := 0xd537c.
Definition PF1_SWRET : Z := 0xd6454.
Definition PF1_FR : Z := 2048.
Definition pf1_stops : list Z := [PF1_RET; PF1_SW].

Definition pf1_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0 | 1 => ELit PF1_RET | 2 => EVar 0 | 3 => ELit 0x10800 | 4 => ELit 0x1006b8
                          | 10 => ELit 0 | 11 => ELit 0
                          | _ => EVar (3 + i) end)%nat (seq 0 32)).
Definition pf1_kn : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x100010000 0x7fffffffffff;
   KWr (SA (EVar 0) (- PF1_FR)) PF1_FR;
   KImg 0x10000 0xee000;
   KImg 0xee1b0 0xee480;
   KWord (SA (ELit 0) 0x120928) 8 (EVar 2);
   KWr (SA (ELit 0) 0xee000) 0x34000].

Definition runA := sym_exec RSEGS 5000 true pf1_stops (SCR [] [] []) (SS PF1_ENTRY pf1_sr [] pf1_kn 40) [].
Definition ssA := Eval vm_compute in fst (fst runA).
Definition scrA := Eval vm_compute in snd runA.
Definition knB0 : list kentry := Eval vm_compute in fst (fst (carry (s_log ssA) pf1_kn [])).
Definition hsA := Eval vm_compute in snd (carry (s_log ssA) pf1_kn []).
Definition srB0 : list expr := Eval vm_compute in sr_upd (s_regs ssA) (ridx 10) (ELit (2^64 - 25)).
Definition runB := sym_exec RSEGS 5000 true pf1_stops (SCR [] [] []) (SS (PF1_IOCTL + 4) srB0 [] knB0 40) [].
Definition ssB := Eval vm_compute in fst (fst runB).
Definition scrB := Eval vm_compute in snd runB.
Definition srB : list expr := Eval vm_compute in s_regs ssB.
Definition knB : list kentry := Eval vm_compute in fst (fst (carry (s_log ssB) knB0 [])).
Definition hsB := Eval vm_compute in snd (carry (s_log ssB) knB0 []).
Definition PF1_ABS : list (Z * Z) := [(0xee3b0, 0xee3c0); (0xee3c8, 0xee3d0)].
Definition PF1_KEPT : list nat := [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat.
Definition knC0 : list kentry := Eval vm_compute in
  (kn_cut2 0 (-1088-112) (-1088) PF1_ABS 0x122000 knB
   ++ [KWord (SA (ELit 0) 0xee3b0) 8 (ELit 0x1216a8); KWord (SA (ELit 0) 0xee3b8) 8 (ELit 0x1212a8);
       KWord (SA (ELit 0) 0xee3c8) 8 (ELit 0x1212a8)]).
Definition srC0 : list expr := Eval vm_compute in sr_upd (sr_after_call_j srB PF1_KEPT 40) (ridx 10) (ELit 1).
Definition runC := sym_exec RSEGS 5000 true pf1_stops (SCR [] [] []) (SS PF1_SWRET srC0 [] knC0 72) [].
Definition ssC := Eval vm_compute in fst (fst runC).
Definition scrC := Eval vm_compute in snd runC.
Definition knC : list kentry := Eval vm_compute in fst (fst (carry (s_log ssC) knC0 [])).
Definition hsC := Eval vm_compute in snd (carry (s_log ssC) knC0 []).

Lemma rA_eq : sym_exec RSEGS 5000 true pf1_stops (SCR [] [] []) (SS PF1_ENTRY pf1_sr [] pf1_kn 40) [] = (ssA, [], scrA).
Proof. vm_compute. reflexivity. Qed.
Lemma cA_eq : carry (s_log ssA) pf1_kn [] = (knB0, [], hsA). Proof. vm_compute. reflexivity. Qed.
Lemma rB_eq : sym_exec RSEGS 5000 true pf1_stops (SCR [] [] []) (SS (PF1_IOCTL + 4) srB0 [] knB0 40) [] = (ssB, [], scrB).
Proof. vm_compute. reflexivity. Qed.
Lemma cB_eq : carry (s_log ssB) knB0 [] = (knB, [], hsB). Proof. vm_compute. reflexivity. Qed.
Lemma rC_eq : sym_exec RSEGS 5000 true pf1_stops (SCR [] [] []) (SS PF1_SWRET srC0 [] knC0 72) [] = (ssC, [], scrC).
Proof. vm_compute. reflexivity. Qed.
Lemma cC_eq : carry (s_log ssC) knC0 [] = (knC, [], hsC). Proof. vm_compute. reflexivity. Qed.
Lemma knC0_eq : knC0 = kn_cut2 0 (-1088-112) (-1088) PF1_ABS 0x122000 knB
   ++ [KWord (SA (ELit 0) 0xee3b0) 8 (ELit 0x1216a8); KWord (SA (ELit 0) 0xee3b8) 8 (ELit 0x1212a8);
       KWord (SA (ELit 0) 0xee3c8) 8 (ELit 0x1212a8)].
Proof. vm_compute. reflexivity. Qed.
Lemma srC0_eq : srC0 = sr_upd (sr_after_call_j srB PF1_KEPT 40) (ridx 10) (ELit 1). Proof. vm_compute. reflexivity. Qed.

Lemma rA_pc : s_pc ssA = PF1_IOCTL. Proof. reflexivity. Qed.
Lemma rB_pc : s_pc ssB = PF1_SW. Proof. reflexivity. Qed.
Lemma rC_pc : s_pc ssC = PF1_RET. Proof. reflexivity. Qed.
Lemma knB_vars : kn_vars_lt 40 knB = true. Proof. vm_compute. reflexivity. Qed.
Lemma srB_vars : sr_vars_lt 40 srB = true. Proof. vm_compute. reflexivity. Qed.

Definition pf1_regions : list sregion :=
  [(SA (EVar 0) (- PF1_FR), PF1_FR); (SA (ELit 0) 0xee390, 4); (SA (ELit 0) 0xee398, 16); (SA (ELit 0) 0xee3b0, 16);
   (SA (ELit 0) 0xee3c8, 8); (SA (ELit 0) 0xee3d8, 8); (SA (ELit 0) 0xee418, 4); (SA (ELit 0) 0xee420, 4);
   (SA (ELit 0) 0x1212a8, 1)].
Lemma rA_cov : log_covered pf1_regions (s_log ssA) = true. Proof. vm_compute. reflexivity. Qed.
Lemma rB_cov : log_covered pf1_regions (s_log ssB) = true. Proof. vm_compute. reflexivity. Qed.
Lemma rC_cov : log_covered pf1_regions (s_log ssC) = true. Proof. vm_compute. reflexivity. Qed.

Lemma fetch_ioctl : fetch_word RSEGS (Z_to_bv 64 PF1_IOCTL) = Some ECALLW. Proof. vm_compute. reflexivity. Qed.
End FXDEFS.

Record pf1_pre {AMB : Amb} (mem : word -> option byte) (sp can : word) (model : Model) : Prop := {
  p1_splo  : 0x100010000 <= bv_unsigned sp;
  p1_sphi  : bv_unsigned sp <= 0x7fffffffffff;
  p1_sp16  : bv_unsigned sp mod 16 = 0;
  p1_stack : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - PF1_FR)) (Z.to_nat PF1_FR) = true;
  p1_img   : forall i, 0x10000 <= i < 0xee000 -> mem (Z_to_bv 64 i) = None;
  p1_stdio : forall i, 0xee1b0 <= i < 0xee480 -> mem (Z_to_bv 64 i) = None;
  p1_can   : rdn RSEGS mem (Z_to_bv 64 0x120928) 8 = Some (word_to_le_bytes 8 can);
  p1_fd1   : fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
  p1_halt  : m_halted model = None;
  p1_lazy  : m_vm_lazy model = []
}.

Record stdout_t0 (mem : word -> option byte) : Prop := {
  so_flags : rdn RSEGS mem (Z_to_bv 64 0xee390) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  so_rpos  : rdn RSEGS mem (Z_to_bv 64 0xee398) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  so_rend  : rdn RSEGS mem (Z_to_bv 64 0xee3a0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  so_wend  : rdn RSEGS mem (Z_to_bv 64 0xee3b0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1216a8));
  so_wpos  : rdn RSEGS mem (Z_to_bv 64 0xee3b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1212a8));
  so_wbase : rdn RSEGS mem (Z_to_bv 64 0xee3c8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1212a8));
  so_write : rdn RSEGS mem (Z_to_bv 64 0xee3d8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xd537c));
  so_mode  : rdn RSEGS mem (Z_to_bv 64 0xee418) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0xffffffff));
  so_lbf   : rdn RSEGS mem (Z_to_bv 64 0xee420) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0xffffffff))
}.

Definition pf1_post (regs : bvmap 5 word) (mem : word -> option byte) (sp : word)
           (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  (forall r : reg, In r [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
  /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - PF1_FR), PF1_FR); (Z_to_bv 64 0xee390, 4); (Z_to_bv 64 0xee398, 16);
                         (Z_to_bv 64 0xee3b0, 16); (Z_to_bv 64 0xee3c8, 8); (Z_to_bv 64 0xee3d8, 8); (Z_to_bv 64 0xee418, 4);
                         (Z_to_bv 64 0xee420, 4); (Z_to_bv 64 0x1212a8, 1)]
  /\ stdout_t0 mem'.

Section PF1.
  Context {fx : FPState} {AMB : Amb}.
  Variables (regs : bvmap 5 word) (mem : word -> option byte) (sp can : word) (model : Model).
  Hypothesis PRE : pf1_pre mem sp can model.
  Hypothesis R1  : getr regs 1 = Z_to_bv 64 PF1_RET.
  Hypothesis R2  : getr regs 2 = sp.
  Hypothesis R3  : getr regs 3 = Z_to_bv 64 0x10800.
  Hypothesis R4  : getr regs 4 = Z_to_bv 64 0x1006b8.
  Hypothesis R10 : getr regs 10 = Z_to_bv 64 0.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 0.

Definition vals : list word := [sp; Z_to_bv 64 0; can] ++ junk_vals regs ++ [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0].
  Let E : env := Env (vals_ev vals) (blobs_ev []).

  Ltac evl := lazy [edenot ev eb vals_ev vals junk_vals blobs_ev nth app map seq length].

  Lemma vals_len : length vals = 40%nat.
  Proof. reflexivity. Qed.

  Lemma E0 : vals_ev vals 0 = sp. Proof. reflexivity. Qed.

  Lemma pf1_regs_ok : regs_ok E pf1_sr regs.
  Proof.
    apply regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth pf1_sr allregs32]; subst E; evl;
      first [ apply getr_zero | assumption | f_equal; apply bv_eq; reflexivity ].
  Qed.

  Lemma pf1_know_ok : know_ok RSEGS E mem pf1_kn.
  Proof.
    destruct PRE as [SPlo SPhi SP16 STK IMG STD CAN _ _ _].
    unfold pf1_kn. repeat apply Forall_cons; try apply Forall_nil.
    - cbn [kentry_ok]. subst E; evl. split; [lia | exact SP16].
    - cbn [kentry_ok]. subst E; evl. lia.
    - cbn [kentry_ok a_base a_off]. unfold flat, estart. cbn [a_base a_off]. subst E; evl.
      unfold PF1_FR in *. split; [lia|]. intros d m Hd Hm.
      eapply store_ok_sub; [ | exact STK | | ]; rewrite ?u_small by lia; rewrite ?Z2Nat.id by lia; lia.
    - cbn [kentry_ok]. repeat split; [lia | lia | exact IMG].
    - cbn [kentry_ok]. repeat split; [lia | lia | exact STD].
    - cbn [kentry_ok a_base a_off]. split; [lia|]. unfold flat, estart, adenot. cbn [a_base a_off]. subst E; evl.
      rewrite (u_small 0) by lia. split; [lia|]. unfold v_addi. rewrite (u_small 0) by lia. exact CAN.
    - cbn [kentry_ok a_base a_off]. unfold flat, estart. cbn [a_base a_off edenot].
      rewrite (u_small 0) by lia. split; [lia|]. intros d m Hd Hm.
      apply store_ok_of_all; [rewrite u_small by lia; lia|]. intros x Hx. rewrite u_small in Hx by lia.
      apply S1StartInit.rw_wview. lia.
  Qed.

  Lemma kword_lit2 : forall E0 M (a : Z) (v : Z) (vw : word),
    (0 <= a /\ a + 8 <= 2 ^ 64)%Z /\ vw = Z_to_bv 64 v ->
    rdn RSEGS M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 vw) ->
    kentry_ok RSEGS E0 M (KWord (SA (ELit 0) a) 8 (ELit v)).
  Proof.
    intros E0 M a v vw [[Ha Hb] ->] H. cbn [kentry_ok a_base a_off edenot]. split; [lia|].
    unfold flat, estart, adenot. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
    split; [lia|]. unfold v_addi. rewrite (u_small 0) by lia. rewrite Z.add_0_l. exact H.
  Qed.

  Lemma regs_ok_set_have : forall E0 sr R (rd : reg) v e,
    regs_ok E0 sr R -> getr R rd = v -> edenot E0 e = v -> rd <> 0%bv ->
    regs_ok E0 (sr_upd sr (ridx rd) e) R.
  Proof.
    intros E0 sr R rd v e HR0 Hv He Hrd r.
    pose proof (regs_ok_set E0 sr R rd v e HR0 Hrd He r) as H.
    rewrite <- H. destruct (decide (r = rd)) as [->|Hne].
    - rewrite getr_same by exact Hrd. exact Hv.
    - rewrite getr_other by exact Hne. reflexivity.
  Qed.

  Theorem printf0_first : forall K,
    K [] ->
    (forall regs' mem', pf1_post regs mem sp regs' mem' ->
       srealizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 PF1_RET) mem' (seg_rom RSEGS)) model) K) ->
    srealizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 PF1_ENTRY) mem (seg_rom RSEGS)) model)
              (t_emit (W 1 [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]) K).
  Proof.
    intros K HKnil CONT.
    pose proof pf1_regs_ok as HR. pose proof pf1_know_ok as HK.
    destruct PRE as [SPlo SPhi SP16 STK IMG STD CAN FD1 Hh Hlazy]. pose proof (u64_range sp) as Usp.

    destruct (run_sound RSEGS 5000 pf1_stops (SCR [] [] []) PF1_ENTRY pf1_sr pf1_kn 40 ssA [] scrA
                E mem (seg_rom RSEGS) regs rA_eq HR HK ltac:(constructor)) as (RA & HRA & HlfA & HmsA).
    rewrite rA_pc in HmsA.
    pose proof (carry_after RSEGS E mem _ pf1_kn [] _ _ _ cA_eq HlfA HK ltac:(constructor)) as HKA.
    pose proof (log_covered_frame E mem pf1_regions _ rA_cov) as FRA.
    eapply srz_msteps; [exact Hh | exact Hlazy | exact HmsA |].

    eapply (srz_ioctl_winsz RSEGS RA (Z_to_bv 64 PF1_IOCTL) _ model ECALLW (Z_to_bv 64 1));
      [ exact fetch_ioctl | apply is_ecall_ECALLW | exact Hh | exact Hlazy
      | rewrite (reg_val E _ RA 17 HRA); reflexivity
      | rewrite (reg_val E _ RA 10 HRA); reflexivity
      | rewrite u_small by lia; lia
      | exact FD1
      | discriminate
      | rewrite (reg_val E _ RA 11 HRA); reflexivity | ].
    rewrite v_addi_pc4 by (unfold PF1_IOCTL; lia).
    pose proof (regs_set_a0 E _ RA (errno_ret ENOTTY) (ELit (2^64 - 25)) HRA ltac:(apply bv_eq; reflexivity)) as HRB0.
    change (sr_upd (s_regs ssA) (ridx 10) (ELit (2 ^ 64 - 25))) with srB0 in HRB0.

    destruct (run_sound RSEGS 5000 pf1_stops (SCR [] [] []) (PF1_IOCTL + 4) srB0 knB0 40 ssB [] scrB
                E _ (seg_rom RSEGS) _ rB_eq HRB0 HKA ltac:(constructor)) as (RB & HRB & HlfB & HmsB).
    rewrite rB_pc in HmsB.
    pose proof (carry_after RSEGS E _ _ knB0 [] _ _ _ cB_eq HlfB HKA ltac:(constructor)) as HKB.
    change (s_regs ssB) with srB in HRB.
    pose proof (log_covered_frame E (mem_denot E mem (s_log ssA)) pf1_regions _ rB_cov) as FRB.
    eapply srz_msteps; [exact Hh | exact Hlazy | exact HmsB |].
    set (MA := mem_denot E mem (s_log ssA)) in *. set (MB := mem_denot E MA (s_log ssB)) in *.

    assert (G2 : getr RB 2 = Z_to_bv 64 (bv_unsigned sp - 1088)).
    { rewrite (reg_val E _ RB 2 HRB). change (sr_get srB 2) with (EAlu ALU_ADD (EVar 0) (ELit (-1088))).
      rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. evl. f_equal; lia. }
    krd HKB 0x1212a8%Z 1%nat PEND.
    replace (Z_to_bv 64 PF1_SW) with (0xd537c%bv : word) by (apply bv_eq; reflexivity).
    unfold W. change (map (WriteEv (Z_to_bv 64 1)) [Z_to_bv 8 48; Z_to_bv 8 10])
      with (map (WriteEv (Z_to_bv 64 1)) ([Z_to_bv 8 48] ++ [Z_to_bv 8 10])).
    eapply (ref_stdio_write RB MB model (bv_unsigned sp - 1088) 0xee390 0x1212a8 0x1212a9 1
              (Z_to_bv 64 0x11093) (Z_to_bv 64 1) (Z_to_bv 64 0x1212a8) (Z_to_bv 64 1024) can (Z_to_bv 64 PF1_SWRET)
              [Z_to_bv 8 48] [Z_to_bv 8 10] K).
    + exact G2.
    + rewrite (reg_val E _ RB 10 HRB); reflexivity.
    + rewrite (reg_val E _ RB 11 HRB); reflexivity.
    + rewrite (reg_val E _ RB 12 HRB); reflexivity.
    + rewrite (reg_val E _ RB 1 HRB); reflexivity.
    + lia. + lia.
    +
      eapply store_ok_mono; [subst MB; apply mem_denot_grows|]. eapply store_ok_mono; [subst MA; apply mem_denot_grows|].
      eapply store_ok_sub; [ | exact STK | | ]; unfold PF1_FR; rewrite ?u_small by lia; rewrite ?Z2Nat.id by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    + lia. + lia.
    + constructor; krd_solve HKB.
    + split; [krd_solve HKB | krd_solve HKB].
    + lia.
    + exact FD1.
    + exact Hh. + exact Hlazy.
    + lia. + lia.
    + reflexivity.
    + rewrite u_small by lia. reflexivity.
    + cbn. lia.
    + left. lia.
    + left. rewrite !u_small by lia. lia.
    + rewrite !u_small by lia. lia.
    + exact PEND.
    + cbn [length]. krd_solve HKB.
    + apply bv_eq. vm_compute. reflexivity.
    + exact HKnil.
    + clear HmsA HmsB. intros RC MC Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 SWP.

      set (vals2 := vals ++ junk_vals RC). set (E2 := Env (vals_ev vals2) (blobs_ev [])).
      assert (AG : env_agree 40 E E2).
      { subst E E2 vals2. rewrite <- vals_len. apply (vals_app_agree vals (junk_vals RC) (blobs_ev [])). }
      assert (HRC0 : regs_ok E2 srC0 RC).
      { rewrite srC0_eq. apply (regs_ok_set_have E2 _ RC 10 (Z_to_bv 64 1) (ELit 1)); [ | exact Q10 | reflexivity | discriminate].
        subst E2 vals2. replace 40%nat with (length vals) by (rewrite vals_len; reflexivity).
        apply (regs_after_call vals (blobs_ev []) srB RB RC PF1_KEPT); [rewrite vals_len; exact srB_vars | exact HRB | | cbv [PF1_KEPT In]; lia].
        intros i Hi. cbv [PF1_KEPT In] in Hi.
        repeat (destruct Hi as [<-|Hi]; [split; [lia | rewrite <- nth_allregs32 by lia; cbn [nth allregs32];
          first [ assumption
                | rewrite Q1; rewrite (reg_val E _ RB 1 HRB); reflexivity
                | rewrite Q2, G2; reflexivity ] ] |]).
        destruct Hi. }
      assert (HKC0 : know_ok RSEGS E2 MC knC0).
      { rewrite knC0_eq. apply know_ok_app. split.
        - apply (know_cut2_sound 0 (-1088-112) (-1088) PF1_ABS 0x122000 RSEGS E2 MB MC).
          + unfold LOGWIN. lia.
          + subst E2 vals2. cbn [ev]. unfold vals_ev. rewrite app_nth1 by (rewrite vals_len; lia).
            change (nth 0 vals (Z_to_bv 64 0)) with sp. unfold LOGWIN. lia.
          + intros x Hx Habs. apply (swp_agree _ _ _ _ _ _ SWP).
            * subst E2 vals2. cbn [ev] in Hx. unfold vals_ev in Hx. rewrite app_nth1 in Hx by (rewrite vals_len; lia).
              change (nth 0 vals (Z_to_bv 64 0)) with sp in Hx. lia.
            * unfold PF1_ABS in Habs. apply Forall_cons_iff in Habs as [H1 Habs]. cbn [fst snd] in H1. lia.
            * unfold PF1_ABS in Habs. apply Forall_cons_iff in Habs as [_ Habs]. apply Forall_cons_iff in Habs as [H2 _]. cbn [fst snd] in H2. lia.
          + exact (swp_grows _ _ _ _ _ _ SWP).
          + unfold PF1_ABS. repeat (apply Forall_cons; [cbn [snd]; lia|]). apply Forall_nil.
          + eapply know_ok_agree; [exact AG | exact knB_vars | exact HKB].
        - repeat apply Forall_cons; try apply Forall_nil.
          + eapply kword_lit2; [ | exact (swp_wend _ _ _ _ _ _ SWP)]. split; [lia | apply bv_eq; vm_compute; reflexivity].
          + eapply kword_lit2; [ | exact (swp_wpos _ _ _ _ _ _ SWP)]. split; [lia | reflexivity].
          + eapply kword_lit2; [ | exact (swp_wbase _ _ _ _ _ _ SWP)]. split; [lia | reflexivity]. }
      destruct (run_sound RSEGS 5000 pf1_stops (SCR [] [] []) PF1_SWRET srC0 knC0 72 ssC [] scrC
                  E2 MC (seg_rom RSEGS) RC rC_eq HRC0 HKC0 ltac:(constructor)) as (RD & HRD & HlfC & HmsC).
      rewrite rC_pc in HmsC.
      pose proof (carry_after RSEGS E2 MC _ knC0 [] _ _ _ cC_eq HlfC HKC0 ltac:(constructor)) as HKD.
      pose proof (log_covered_frame E2 MC pf1_regions _ rC_cov) as FRC.
      eapply srz_msteps; [exact Hh | exact Hlazy | exact HmsC |].
      apply CONT. split; [|split].
      *
        intros r Hr. cbv [In] in Hr.
        repeat (destruct Hr as [<-|Hr]; [rewrite (reg_val E2 _ RD _ HRD); subst E2 vals2; evl;
                 first [ reflexivity | symmetry; assumption | f_equal; apply bv_eq; reflexivity ] |]).
        destruct Hr.
      *
        assert (RG : map (rdenot E) pf1_regions = [(Z_to_bv 64 (bv_unsigned sp - PF1_FR), PF1_FR); (Z_to_bv 64 0xee390, 4); (Z_to_bv 64 0xee398, 16);
                         (Z_to_bv 64 0xee3b0, 16); (Z_to_bv 64 0xee3c8, 8); (Z_to_bv 64 0xee3d8, 8); (Z_to_bv 64 0xee418, 4);
                         (Z_to_bv 64 0xee420, 4); (Z_to_bv 64 0x1212a8, 1)]).
        { unfold pf1_regions, rdenot, estart. cbn [map fst snd a_base a_off edenot ev]. subst E. evl.
          rewrite (u_small 0) by lia. repeat f_equal; lia. }
        assert (RG2 : map (rdenot E2) pf1_regions = map (rdenot E) pf1_regions).
        { unfold pf1_regions, rdenot, estart. cbn [map fst snd a_base a_off edenot ev]. subst E E2 vals2. evl. reflexivity. }
        assert (RF : regions_flat E pf1_regions).
        { intros rg Hrg. unfold pf1_regions in Hrg. unfold flat, estart.
          repeat (destruct Hrg as [<-|Hrg]; [cbn [fst snd a_base a_off edenot ev]; subst E; evl; rewrite ?(u_small 0) by lia; unfold PF1_FR; lia|]); destruct Hrg. }
        assert (RF2 : regions_flat E2 pf1_regions).
        { intros rg Hrg. unfold pf1_regions in Hrg. unfold flat, estart.
          repeat (destruct Hrg as [<-|Hrg]; [cbn [fst snd a_base a_off edenot ev]; subst E2 vals2; evl; rewrite ?(u_small 0) by lia; unfold PF1_FR; lia|]); destruct Hrg. }
        rewrite <- RG. eapply frame_mod_trans_same; [exact (FRA RF HlfA)|].
        eapply frame_mod_trans_same; [exact (FRB RF HlfB)|].
        eapply frame_mod_trans_same.
        --
           split; [|exact (swp_grows _ _ _ _ _ _ SWP)]. intros a Ha. rewrite RG in Ha. cbn [outside] in Ha.
           destruct Ha as (O1 & _ & _ & O4 & O5 & _). unfold in_rng in O1, O4, O5.
           rewrite (u_small (bv_unsigned sp - PF1_FR)) in O1 by (unfold PF1_FR; lia). rewrite u_small in O4 by lia. rewrite u_small in O5 by lia.
           apply (swp_agree _ _ _ _ _ _ SWP); unfold PF1_FR in *; lia.
        -- rewrite <- RG2. exact (FRC RF2 HlfC).
      *
        constructor; krd_solve HKD.
  Qed.
End PF1.
