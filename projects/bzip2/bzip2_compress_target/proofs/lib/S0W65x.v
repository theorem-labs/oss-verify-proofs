(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the place_declined_b premise of mmap proved for the NULL hint, Linux's mmap placement, the launch input ProcInput, the CONFIG_RSEQ flag, the new auxv, the vDSO and the init stack window; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ModelAmb.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW StartupRnd.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Prelude Instr.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Plain.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec SymExec2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun SymDrive SymDriveX RefMemcpyLib S0MainEntry S0LibStdioCall.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec SymExec2. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun SymDrive SymDriveX RefMemcpyLib S0MainEntry S0LibStdioCall.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymFold.
Module S0PilotOOM_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.bzip2.bzip2_compress_target.images.Plain.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0MainEntry OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0LibStdioCall.
   (* [comment removed for export] *)

Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Definition kn_exec : list kentry := kn_main.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STOPS : list Z := [0x26be8; 0x26fec; 0x270e4; 0x27128; 0x13208; 0x20fe4; 0x1f6fc; 0x21650]%Z.

Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].

Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x13548 sr_main [] kn_exec 38.
Definition rA__t := run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA__t)).
Definition rA := ltac:(SymFold.sf_def rA__t (srA, (kn_exec, tt))).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_exec.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0x27510 srB0 [] knA 38.
Definition rB__t := run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB__t)).
Definition rB := ltac:(SymFold.sf_def rB__t (srB, (knA, tt))).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.

(* [comment removed for export] *)
Definition mc_store : sentry := SE (SA (EVar 0) (-384)) 8 (EBlob false 2 8 8).   (* [comment removed for export] *)
Definition knB2 : list kentry := Eval vm_compute in fst (fst (carry [mc_store] knB [])).
(* [comment removed for export] *)
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB (map ridx callee_kept) 38.

(* Block C: from the AT_RANDOM memcpy's return (ra = 0x20174, set by [jal ra] at 0x20170)
   to the brk(0) ecall at 0x2023c.  The scan reads pair 25 (AT_EXECFN) and then the
   [kb_rseq]-dependent terminator (pairs 26..28 with CONFIG_RSEQ, pair 26 without), so C
   runs once per value of that FREE kernel field, each arm with its terminator rows
   ([kn_termT] / [kn_termF], S0MainEntry) appended.  Both arms reach 0x2023c with s0 = 4096
   and a1 = 4095 produced by the walk (0x2019c ld s0,48(s0); 0x201a8 lui s0,1; 0x20238
   addi a1,s0,-1), and they differ only in a2 (auxvp + 448 vs + 416), which the first
   instruction of block D (0x20240 neg a2,a0) overwrites.  So D is shared.
   All of this is measured (QWB3). *)
Definition ssCT0 : sym_state := SS 0x20174 srC0 [] (knB2 ++ kn_termT) 70.
Definition rCT__t := run scr0 ssCT0.
Definition srCT : list expr := Eval vm_compute in s_regs (fst (fst rCT__t)).
Definition rCT := ltac:(SymFold.sf_def rCT__t (srCT, (knB2, tt))).
Definition knCT : list kentry := Eval vm_compute in kn_after rCT (knB2 ++ kn_termT).
Definition ssCF0 : sym_state := SS 0x20174 srC0 [] (knB2 ++ kn_termF) 70.
Definition rCF__t := run scr0 ssCF0.
Definition srCF : list expr := Eval vm_compute in s_regs (fst (fst rCF__t)).
Definition rCF := ltac:(SymFold.sf_def rCF__t (srCF, (knB2, tt))).
Definition knCF : list kentry := Eval vm_compute in kn_after rCF (knB2 ++ kn_termF).
(* What D starts from: the knowledge with the terminator rows dropped (the same list for
   both arms, checked below), and the F arm's registers.  D's run from the T arm's
   registers is the same run (a2 is dead).  [oom_segC] covers both arms. *)
Definition not_term (K : kentry) : bool :=
  match K with KWord (SA (EVar 3) o) _ _ => (o <? 416)%Z | _ => true end.
Definition knC : list kentry := Eval vm_compute in List.filter not_term knCF.
Lemma knC_T : List.filter not_term knCT = knC.
Proof. vm_compute. reflexivity. Qed.
Lemma knC_F : List.filter not_term knCF = knC.
Proof. vm_compute. reflexivity. Qed.
Definition srC : list expr := srCF.

(* [comment removed for export] *)
Definition b_expr : expr := EVar 70.
Definition knD0 : list kentry := KAlign b_expr 4096 :: KRange b_expr 0x5c000 0x8005c000 :: knC.
Definition srD0 : list expr := sr_upd srC (ridx 10) b_expr.
Definition ssD0 : sym_state := SS 0x20240 srD0 [] knD0 71.
Definition rD__t := run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD__t)).
Definition rD := ltac:(SymFold.sf_def rD__t (srD, (knD0, tt))).
Definition knD : list kentry := Eval vm_compute in kn_after rD knD0.
(* [comment removed for export] *)
Definition ugly_b : expr :=
  EAlu ALU_ADD b_expr (EAlu ALU_AND (ELit 4095) (EMd M_MUL (ELit (-1)) b_expr)).
Definition srD2 : list expr := Eval vm_compute in map (esub ugly_b b_expr) srD.
Definition knD2 : list kentry := Eval vm_compute in map (ksub ugly_b b_expr) knD.

(* [comment removed for export] *)
Definition srE0 : list expr := sr_upd srD2 (ridx 10) b_expr.
Definition ssE0 : sym_state := SS 0x20264 srE0 [] knD2 71.
Definition scrE : scripts := SCR [true] [] [].     (* [comment removed for export] *)
Definition rE__t := run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE__t)).
Definition rE := ltac:(SymFold.sf_def rE__t (srE, (knD2, tt))).
Definition knE : list kentry := Eval vm_compute in kn_after rE knD2.

(* [comment removed for export] *)
Definition srF0 : list expr := sr_upd srE (ridx 10) (ELit (2 ^ 64 - 12)).
Definition ssF0 : sym_state := SS 0x21378 srF0 [] knE 71.
Definition rF__t := run scr0 ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF__t)).
Definition rF := ltac:(SymFold.sf_def rF__t (srF, (knE, tt))).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.

(* [comment removed for export] *)
Definition resG_opt : option stdio_res := Eval vm_compute in stdio_call 71 srF knF.
Definition resG : stdio_res :=
  Eval vm_compute in match resG_opt with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition srG0 : list expr := Eval vm_compute in sc_sr resG.
Definition knG0 : list kentry := Eval vm_compute in sc_kn resG.
Definition ssG0 : sym_state := SS 0x220e8 srG0 [] knG0 103.
Definition rG__t := run scr0 ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG__t)).
Definition rG := ltac:(SymFold.sf_def rG__t (srG, (knG0, tt))).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.

(* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)
End S0PilotOOM_defs.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymXfer.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StoreOk SimInv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require CatSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ShapeAlg ShapeLaws Nodes MmapSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require MmapSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require FileSim AgentLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ModelAmb.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymExec SymExec2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun SymDrive SymDriveX LibKnowFrame S0LibStdioCall Spec LibWritev RefNodes S0ExitBase S0StdioDefs S0Exit RefMemcpyLib S0Startup S0MainEntry Hoare Frame MallocDefs S0EnframeBase S0Enframe S0ReadBase.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require CatSim. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require MmapSim. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ModelAmb. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require S0MemcpyBase S0Memcpy MemSplit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymHide.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require MmapBase.
Module S0PilotOOM.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ModelAmb.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.MiniExec.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.bzip2.bzip2_compress_target.images.Plain.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SimInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim.ExitSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ShapeLaws OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Nodes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim.AllocSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.FileSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.AgentLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ModelAmb.SpecConsts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.LibKnowFrame OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0LibStdioCall OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.LibWritev OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefNodes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0ExitBase OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0StdioDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Exit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0MemcpyBase OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Memcpy OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Startup OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0MainEntry OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Hoare OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MemSplit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0W65x.S0PilotOOM_defs.
(* [comment removed for export] *)

Import SymHide.OptIn.
(* [comment removed for export] *)
Local Ltac SymHide.sc_cands ::= constr:((S0PilotOOM_defs.kn_exec, (S0PilotOOM_defs.srA, (S0PilotOOM_defs.knA, (S0PilotOOM_defs.srB0, (S0PilotOOM_defs.srB, (S0PilotOOM_defs.knB, (S0PilotOOM_defs.knB2, (S0PilotOOM_defs.srC0, (S0PilotOOM_defs.srC, (S0PilotOOM_defs.knC, (S0PilotOOM_defs.knD0, (S0PilotOOM_defs.srD0, (S0PilotOOM_defs.srD, (S0PilotOOM_defs.knD, (S0PilotOOM_defs.srD2, (S0PilotOOM_defs.knD2, (S0PilotOOM_defs.srE0, (S0PilotOOM_defs.srE, (S0PilotOOM_defs.knE, (S0PilotOOM_defs.srF0, (S0PilotOOM_defs.srF, (S0PilotOOM_defs.knF, (S0PilotOOM_defs.srG0, (S0PilotOOM_defs.knG0, (S0PilotOOM_defs.srG, (S0PilotOOM_defs.knG, tt))))))))))))))))))))))))))).
Import ListNotations.

Local Ltac Lia.lia ::= NatLitLia.lia_natlit.   (* [comment removed for export] *)
Local Open Scope bv_scope.
Import SX2. Import SX2S.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition LIM : Z := source_alloc_limit.
Lemma LIM_ge : (2 ^ 34 <= LIM)%Z.
Proof. unfold LIM. rewrite source_alloc_limit_val. apply Z.leb_le. reflexivity. Qed.

(* At the revision [init_model]'s reserved list is the binary's segments
   followed by the vDSO/vvar pair ([State.init_reserved]). *)
Notation RESX mb sp kb := (init_reserved (segments_reserved RSEGS) mb sp kb).

Lemma segres_eq : segments_reserved RSEGS =
  [(Z_to_bv 64 65536, Z_to_bv 64 12288); (Z_to_bv 64 77824, Z_to_bv 64 86016);
   (Z_to_bv 64 163840, Z_to_bv 64 4096); (Z_to_bv 64 167936, Z_to_bv 64 208896)].
Proof. vm_compute. reflexivity. Qed.

Lemma segres_small : Forall small_ent (segments_reserved RSEGS).
Proof. rewrite segres_eq. unfold small_ent. repeat constructor; cbn [fst snd]; rewrite ?u_small by lia; lia. Qed.

Lemma segres_below : forall a sz, In (a, sz) (segments_reserved RSEGS) ->
  (bv_unsigned a + bv_unsigned sz <= 0x5c000)%Z.
Proof.
  intros a sz Hin. rewrite segres_eq in Hin. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; rewrite ?u_small by lia; lia.
Qed.

Lemma segres_len : length (segments_reserved RSEGS) = 4%nat.
Proof. rewrite segres_eq. reflexivity. Qed.

Lemma RESX_seg_in : forall mbase sp kb e, In e (segments_reserved RSEGS) -> In e (RESX mbase sp kb).
Proof. intros mbase sp kb e H. unfold init_reserved. apply in_or_app. left. exact H. Qed.

Section Pilot.
  Context {ACEIL__ : ACeil}.   (* [comment removed for export] *)
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable hw : word.    (* [comment removed for export] *)
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_launch (mkProcInputA [a0s; path] envv fs0 stdin0) hw mbase sp0 brk rnd tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hceil : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.   (* [comment removed for export] *)
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpnd : openat_plain_name path = true.   (* [comment removed for export] *)
  Hypothesis Hplen : (length path <= 4095)%nat.

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rnd)).

  (* [comment removed for export] *)
  Definition fds0 : list (word * FdEntry) :=
    [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
     (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
  (* [comment removed for export] *)
  Definition model0 : Model :=
    with_tid tid (with_vdso (ia_vdso stdin0) (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputA [a0s; path] envv fs0 stdin0))).
  (* [comment removed for export] *)
  Definition fds1g (fd3 : FdEntry) : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) fd3.
  Definition model1g (fd3 : FdEntry) : Model :=
    mkModelA (fds1g fd3) (mkVmMapsFull (RESX mbase sp0 (ia_kernel stdin0)) [] [] brk brk LIM mbase sp0) stdin0 fs0 None (Some tid) None.
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition above_sp0 (M : word -> option byte) : Prop :=
    forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma m1_vmmaps : forall fd3, m_vmmaps (model1g fd3) = mkVmMapsFull (RESX mbase sp0 (ia_kernel stdin0)) [] [] brk brk LIM mbase sp0.
  Proof. intros. reflexivity. Qed.
  (* the launch's mmap base is in the covered band ([Run.valid_mmap_base]) *)
  Lemma mbase_lo : (mmap_base_min <= bv_unsigned mbase)%Z.
  Proof.
    destruct ME as (_ & _ & Hl & _). cbn [entry_launch_ok_va] in Hl. destruct Hl as (_ & _ & Hb).
    exact (proj1 (MmapBase.valid_launch_base_sv48_in_band _ _ Hb)).
  Qed.
  (* [comment removed for export] *)
  Lemma atop_sp0 : forall r m na sb b l mb, atop_ok (mkVmMapsFull r m na sb b l mb sp0).
  Proof. intros. unfold atop_ok, alloc_top. cbn [vm_init_sp]. rewrite Hceil. unfold stack_max_size. lia. Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma m0_fds : m_fds model0 = fds0.
  Proof. reflexivity. Qed.
  Lemma m0_fs : m_fs model0 = fs0.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma above_sp0_block : forall vals log M,
    vals_ev vals 0 = sp0 -> log_below_b 0 0x5c000 log = true -> above_sp0 M ->
    above_sp0 (mem_denot (ENV vals) M log).
  Proof.
    intros vals log M P0 Hb HA a Ha. pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo.
    rewrite (mem_denot_above (ENV vals) M log 0%nat 0x5c000 a Hb); [apply HA; exact Ha | | |];
      cbn [ev ENV]; rewrite ?P0; lia.
  Qed.

  Lemma alloc_fd_fds0 : alloc_fd fds0 = Z_to_bv 64 3.
  Proof. exact (alloc_fd_init _ _ _). Qed.
  Lemma fd_lookup_fds0_3 : fd_lookup fds0 (Z_to_bv 64 3) = None.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Ltac refresh_above vals P0 HA :=
    lazymatch type of HA with above_sp0 ?Mo =>
      lazymatch goal with EQ : ?Mn = mem_denot _ Mo ?log |- _ =>
        let HA' := fresh "HA" in
        pose proof (above_sp0_block vals log Mo P0 ltac:(vm_compute; reflexivity) HA) as HA';
        rewrite <- EQ in HA'; clear HA EQ; rename HA' into HA
      end
    end.
  (* [comment removed for export] *)
  Ltac name_state R M :=
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rn _ ?Mn _) _) _ => rename Rn into R; rename Mn into M end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma rtop : reserved_top (segments_reserved RSEGS) = 0x5c000%Z.
  Proof. vm_compute. reflexivity. Qed.

  Lemma brk_lo : (0x5c000 <= bv_unsigned brk)%Z.
  Proof. pose proof (proj1 Hbrk) as H. rewrite rtop in H. exact H. Qed.
  Lemma brk_hi : (bv_unsigned brk <= 0x8005c000)%Z.
  Proof. pose proof (proj1 (proj2 Hbrk)) as H. rewrite rtop, brk_aslr_max_val in H. cbn in H. lia. Qed.
  Lemma brk_al : (bv_unsigned brk mod 4096 = 0)%Z.
  Proof. exact (proj2 (proj2 Hbrk)). Qed.

  (* [comment removed for export] *)
  Lemma ugly_b_sem : forall vals, vals_ev vals 70 = brk ->
    edenot (ENV vals) ugly_b = edenot (ENV vals) b_expr.
  Proof.
    intros vals P70. cbn [edenot ugly_b b_expr ev ENV]. rewrite P70.
    rewrite alu_add, alu_and, m_mul. unfold v_add, v_and, v_mul.
    pose proof brk_al as Hal. pose proof (u64_range brk) as Hb.
    set (y := bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (-1)) * bv_unsigned brk))).
    assert (Hy : (y mod 4096 = 0)%Z).
    { subst y. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
      rewrite Z.mod_mod_divide by (exists (2 ^ 52)%Z; reflexivity).
      destruct (proj1 (Z.mod_divide (bv_unsigned brk) 4096 ltac:(lia)) Hal) as [q Hq]. rewrite Hq.
      rewrite Z.mul_assoc. apply Z_mod_mult. }
    assert (Hand : Z.land (bv_unsigned (Z_to_bv 64 4095)) y = 0%Z).
    { change (bv_unsigned (Z_to_bv 64 4095)) with (Z.ones 12). rewrite Z.land_comm, Z.land_ones by lia.
      change (2 ^ 12)%Z with 4096%Z. exact Hy. }
    rewrite Hand. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
  Qed.

  (* [comment removed for export] *)
  Lemma brk_ne_req : forall vals, vals_ev vals 70 = brk ->
    branch_taken BC_NE (edenot (ENV vals) b_expr) (edenot (ENV vals) (EAlu ALU_ADD b_expr (ELit 8192))) = true.
  Proof.
    intros vals P70. cbn [edenot b_expr ev ENV]. rewrite P70, alu_add. unfold v_add.
    cbn [branch_taken]. unfold bv_eqb. pose proof brk_hi. pose proof (u64_range brk).
    change (bv_unsigned (Z_to_bv 64 8192)) with 8192%Z. rewrite u_small by lia.
    apply Bool.negb_true_iff. apply Z.eqb_neq. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
  Proof.
    cps_destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition mmap_ok_branch_g (fd3 : FdEntry) (KB : TSet) : Prop :=
    forall vals R M (hint a : word),
      length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 70 = brk ->
      vals_ev vals 1 = p0 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 -> vals_ev vals 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV vals) srE R -> know_ok RSEGS (ENV vals) M knE -> above_sp0 M ->
      grant_ok_na hint (model1g fd3) a 8192 = true ->      (* [comment removed for export] *)
      realizes RSEGS (mkCfg (mkst (regupd R 10 a) (Z_to_bv 64 0x21378)
                                    (unfill a (Z_to_bv 64 8192) M) (seg_rom RSEGS))
                              (noaccess_model a (Z_to_bv 64 8192) (model1g fd3))) KB.
  Definition mmap_ok_branch : TSet -> Prop := mmap_ok_branch_g (FdFile path (Z_to_bv 64 0)).

  Lemma oom_seg3 : forall fd3 KB vals R M,
    mmap_ok_branch_g fd3 KB ->
    length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 70 = brk ->
    vals_ev vals 1 = p0 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 -> vals_ev vals 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 -> vals_ev vals 5 = tid ->
    regs_ok (ENV vals) srE0 R -> know_ok RSEGS (ENV vals) M knD2 -> above_sp0 M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x20264) M (seg_rom RSEGS)) (model1g fd3))
               KB.
  Proof.
    intros fd3 KB vals R M HKB HL P0 P70 P1 P2 P3 P4 P5t HR HK HA.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    (* [comment removed for export] *)
    run_block_keep scrE 71%nat.
    { (* [comment removed for export] *) unfold sc_denot. apply brk_ne_req. exact P70. }
    refresh_above vals P0 HA. clear R M. name_state R M.
    (* [comment removed for export] *)
    eapply (rz_mmap_noaccess04 RSEGS _ _ _ (model1g fd3) ECALLW 8192).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (11 : reg). reflexivity.
    - lia.
    - regv HR (12 : reg). reflexivity.
    - regv HR (13 : reg). reflexivity.
    - regv HR (14 : reg). apply bv_eq. reflexivity.
    - regv HR (15 : reg). reflexivity.
    - (* [comment removed for export] *)
      change (page_round_up_Z 8192) with 8192%Z.
      destruct (init_reserved_shape _ mbase sp0 (ia_kernel stdin0) mbase_lo ltac:(lia) segres_small) as [RS RL].
      rewrite segres_len in RL.
      apply grant_exists_na; rewrite ?m1_vmmaps; cbn [vm_reserved vm_maps vm_limit]; rewrite ?app_nil_r.
      + (* [comment removed for export] *) apply atop_sp0.
      + lia.
      + (* the length is a whole number of pages *) reflexivity.
      + eapply Forall_impl; [|exact RS]. unfold small_ent. cbn beta. intros p [[X1 X2] X3]. lia.
      + lia.
    - (* LPS 727298f3 (#144/#146): the hint is this call's own a0, the literal NULL *)
      regv HR (10 : reg). apply place_declined_b_null.
    - (* [comment removed for export] *)
      intros a Hg. rewrite v_addi_pc4 by lia. change (0x21374 + 4)%Z with 0x21378%Z.
      change (page_round_up_Z 8192) with 8192%Z in Hg |- *.
      eapply (HKB vals); try eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition brk_ok_branch_g (fd3 : FdEntry) (KB : TSet) : Prop :=
    forall vals R M,
      length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 70 = brk ->
      vals_ev vals 1 = p0 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 -> vals_ev vals 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV vals) srD2 R -> know_ok RSEGS (ENV vals) M knD2 -> above_sp0 M ->
      realizes RSEGS
        (mkCfg (mkst (regupd R 10 (Z_to_bv 64 (bv_unsigned brk + 8192))) (Z_to_bv 64 0x20264)
                     (zfill brk (Z_to_bv 64 8192) M) (seg_rom RSEGS))
               (mkModelA (fds1g fd3) (mkVmMapsFull (RESX mbase sp0 (ia_kernel stdin0)) [(brk, Z_to_bv 64 8192)] [] brk
                                            (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0)
                        stdin0 fs0 None (Some tid) None)) KB.
  Definition brk_ok_branch : TSet -> Prop := brk_ok_branch_g (FdFile path (Z_to_bv 64 0)).

  (* Knowledge-list plumbing for the block-C terminator split below. *)
  Lemma w65_kn_app : forall segs E M k1 k2,
    know_ok segs E M k1 -> know_ok segs E M k2 -> know_ok segs E M (k1 ++ k2).
  Proof. intros segs E M k1 k2 H1 H2. unfold know_ok in *. apply Forall_app. split; assumption. Qed.
  Lemma w65_kn_app_r : forall segs E M k1 k2, know_ok segs E M (k1 ++ k2) -> know_ok segs E M k2.
  Proof. intros segs E M k1 k2 H. unfold know_ok in *. apply Forall_app in H. exact (proj2 H). Qed.
  Lemma w65_kn_filter : forall segs E M f kn, know_ok segs E M kn -> know_ok segs E M (List.filter f kn).
  Proof.
    intros segs E M f kn H. unfold know_ok in *. apply List.Forall_forall. intros x Hx.
    apply List.filter_In in Hx. exact (proj1 (List.Forall_forall _ _) H x (proj1 Hx)).
  Qed.

  (* An auxv a_type row read on the initial memory still holds on any later memory that
     agrees with it above sp0: the auxv sits above sp0 and nothing the program stores
     reaches there. *)
  Lemma kw3_above : forall E E' M o t,
    ev E' 3 = ev E 3 -> (bv_unsigned sp0 <= bv_unsigned (ev E 3))%Z -> (0 <= o)%Z -> above_sp0 M ->
    kentry_ok RSEGS E mem0 (KWord (SA (EVar 3) o) 8 (ELit t)) ->
    kentry_ok RSEGS E' M (KWord (SA (EVar 3) o) 8 (ELit t)).
  Proof.
    intros E E' M o t H3 Hsp Ho HA HK. cbn [kentry_ok] in HK |- *. destruct HK as (Hw & Hfl & Hrd).
    unfold flat, estart in Hfl. cbn [a_base a_off edenot] in Hfl.
    assert (Ha : adenot E' (SA (EVar 3) o) = adenot E (SA (EVar 3) o)).
    { unfold adenot. cbn [a_base a_off edenot]. rewrite H3. reflexivity. }
    assert (Hu : bv_unsigned (adenot E (SA (EVar 3) o)) = (bv_unsigned (ev E 3) + o)%Z).
    { unfold adenot, v_addi. cbn [a_base a_off edenot]. apply u_small. lia. }
    split; [exact Hw|]. split.
    - unfold flat, estart. cbn [a_base a_off edenot]. rewrite H3. exact Hfl.
    - rewrite Ha. cbn [edenot] in Hrd |- *. rewrite <- Hrd. apply rdn_agree.
      intros j Hj. apply HA. rewrite Hu. rewrite u_small by lia. lia.
  Qed.

  Lemma kw3_list_above : forall E E' M kn,
    ev E' 3 = ev E 3 -> (bv_unsigned sp0 <= bv_unsigned (ev E 3))%Z -> above_sp0 M ->
    know_ok RSEGS E mem0 kn ->
    Forall (fun K => exists o t, K = KWord (SA (EVar 3) o) 8 (ELit t) /\ (0 <= o)%Z) kn ->
    know_ok RSEGS E' M kn.
  Proof.
    intros E E' M kn H3 Hsp HA HK Hs. unfold know_ok in *.
    induction kn as [|K kn IH]; [constructor|].
    inversion Hs as [|? ? (o & t & -> & Ho) Hs']; subst.
    inversion HK as [|? ? HK1 HKr]; subst.
    constructor; [eapply kw3_above; eassumption | apply IH; assumption].
  Qed.

  (* From the brk grow ecall at 0x20260 (after block D) on: shared by both terminator arms. *)
  Lemma oom_segE : forall fd3 KBb KBm vals2 R M,
    brk_ok_branch_g fd3 KBb -> (forall tr, KBm tr -> KBb tr) ->
    length vals2 = 71%nat -> vals_ev vals2 0 = sp0 -> vals_ev vals2 70 = brk ->
    vals_ev vals2 1 = p0 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals2 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals2 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 -> vals_ev vals2 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 ->
    vals_ev vals2 5 = tid ->
    regs_ok (ENV vals2) srD R -> know_ok RSEGS (ENV vals2) M knD -> above_sp0 M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x20260) M (seg_rom RSEGS)) (model1g fd3))
               (t_alt2 KBm KBb).
  Proof.
    intros fd3 KBb KBm vals2 R M HKBb HKmb HL P0 P70 P1 P2 P3 P4 P5t HR HK HA.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (regs_ok_esub (ENV vals2) ugly_b b_expr _ _ (ugly_b_sem vals2 P70) HR) as HR2.
    pose proof (know_ok_ksub RSEGS (ENV vals2) _ ugly_b b_expr _ (ugly_b_sem vals2 P70) HK) as HK2.
    clear HR HK. rename HR2 into HR. rename HK2 into HK.
    lazymatch type of HR with regs_ok _ ?sr _ => let sr' := eval vm_compute in sr in change sr with sr' in HR end.
    lazymatch type of HK with know_ok _ _ _ ?kn => let kn' := eval vm_compute in kn in change kn with kn' in HK end.
    eapply (rz_brk_grow RSEGS _ _ _ (model1g fd3) ECALLW 8192).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - rewrite m1_vmmaps; cbn [vm_brk]. exact brk_al.
    - reflexivity.
    - lia.
    - rewrite m1_vmmaps; cbn [vm_brk]. pose proof brk_lo. lia.
    - rewrite m1_vmmaps; cbn [vm_brk]. pose proof brk_hi. lia.
    - rewrite m1_vmmaps; cbn [vm_brk vm_start_brk]. lia.
    - rewrite m1_vmmaps; cbn [vm_brk]. regv HR (10 : reg). rewrite edenot_add_lit.
      unfold adenot, v_addi. cbn [a_base a_off edenot b_expr ev ENV]. rewrite P70. reflexivity.
    - rewrite m1_vmmaps. cbn [vm_brk]. unfold model1g.
      apply (brk_grow_admissible_init_rf (RESX mbase sp0 (ia_kernel stdin0)) brk mbase sp0 LIM fs0 stdin0 (fds1g fd3) (Some tid) None 8192 (atop_sp0 _ _ _ _ _ _ _));
        try (pose proof alloc_ceiling_range);
        first [exact brk_al | reflexivity
              | apply init_reserved_low_free;
                  [exact mbase_lo | lia
                  | intros ra rs Hin; pose proof (segres_below ra rs Hin); pose proof brk_lo; lia
                  | unfold page_size; rewrite u_small by lia; pose proof brk_hi; lia]
              | pose proof brk_lo; pose proof brk_hi; pose proof LIM_ge; lia].
    - exact HKmb.
    - rewrite v_addi_pc4 by lia. change (0x20260 + 4)%Z with 0x20264%Z.
      rewrite m1_vmmaps; cbn [vm_brk vm_reserved vm_maps vm_noaccess vm_start_brk vm_limit vm_mmap_base vm_init_sp].
      eapply (HKBb vals2); try eassumption.
  Qed.

  (* From the brk(0) ecall at 0x2023c, for either terminator arm's registers ([srCT] or
     [srCF]).  The two differ only in a2, which block D's first instruction overwrites, so
     D's run from either is the same run and lands in [oom_segE]. *)
  Lemma oom_segC : forall fd3 KBb KBm srX vals1 R M,
    In srX [srCT; srCF] ->
    brk_ok_branch_g fd3 KBb -> (forall tr, KBm tr -> KBb tr) ->
    length vals1 = 70%nat -> vals_ev vals1 0 = sp0 ->
    vals_ev vals1 1 = p0 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals1 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals1 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 -> vals_ev vals1 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 ->
    vals_ev vals1 5 = tid ->
    regs_ok (ENV vals1) srX R -> know_ok RSEGS (ENV vals1) M knC -> above_sp0 M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2023c) M (seg_rom RSEGS)) (model1g fd3))
               (t_alt2 KBm KBb).
  Proof.
    intros fd3 KBb KBm srX vals1 R M HX HKBb HKmb HL P0 P1 P2 P3 P4 P5t HR HK HA.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    assert (Hsv : sr_vars_lt (length vals1) srX = true)
      by (rewrite HL; destruct HX as [EX|[EX|[]]]; subst srX; vm_compute; reflexivity).
    eapply (rz_brk_query RSEGS _ _ _ (model1g fd3) ECALLW).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - destruct HX as [EX|[EX|[]]]; subst srX; regv HR (17 : reg); reflexivity.
    - destruct HX as [EX|[EX|[]]]; subst srX; regv HR (10 : reg); reflexivity.
    - rewrite v_addi_pc4 by lia. change (0x2023c + 4)%Z with 0x20240%Z.
      rewrite m1_vmmaps; cbn [vm_brk].
      pose proof (env_app_regs vals1 [brk] _ srX R Hsv HR) as HR2.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals1 [brk] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      clear HR HK.
      set (vals2 := vals1 ++ [brk]) in *.
      assert (HL2 : length vals2 = 71%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
      assert (P0' : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (P70 : vals_ev vals2 70 = brk).
      { subst vals2. rewrite <- HL. rewrite <- (Nat.add_0_r (length vals1)). rewrite vals_ev_app_r. reflexivity. }
      assert (P1' : vals_ev vals2 1 = p0 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
      assert (P2' : vals_ev vals2 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
      assert (P3' : vals_ev vals2 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P3).
      assert (P4' : vals_ev vals2 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P4).
      assert (P5' : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5t).
      clearbody vals2. clear HL P0 P1 P2 P3 P4 P5t. rename HL2 into HL. rename P0' into P0. rename P1' into P1. rename P2' into P2. rename P3' into P3. rename P4' into P4. rename P5' into P5t.
      change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path hw rnd))) with (ENV vals2) in HR2, HK2.
      pose proof (regs_set_a0 (ENV vals2) _ _ brk b_expr HR2 ltac:(cbn [edenot b_expr ev ENV]; exact P70)) as HR.
      clear HR2.
      lazymatch type of HK2 with know_ok _ _ ?Mc _ =>
        assert (HK : know_ok RSEGS (ENV vals2) Mc knD0) end.
      { unfold knD0. apply know_ok_cons; [|apply know_ok_cons; [|exact HK2]].
        - apply kalign_intro; [lia|]. cbn [edenot b_expr ev ENV]. rewrite P70. exact brk_al.
        - apply krange_intro. cbn [edenot b_expr ev ENV]. rewrite P70. pose proof brk_lo. pose proof brk_hi. lia. }
      clear HK2.
      (* block D, from either arm's registers *)
      destruct HX as [EX|[EX|[]]]; subst srX.
      all: run_block_keep scr0 71%nat.
      all: refresh_above vals2 P0 HA.
      all: clear R M.
      all: name_state R M.
      all: eapply (oom_segE fd3 KBb KBm vals2); eassumption.
  Qed.

  Lemma oom_seg2 : forall fd3 KBb KBm vals R M,
    brk_ok_branch_g fd3 KBb -> mmap_ok_branch_g fd3 KBm -> (forall tr, KBm tr -> KBb tr) ->
    length vals = 38%nat -> vals_ev vals 0 = sp0 ->
    vals_ev vals 1 = p0 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 -> vals_ev vals 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 -> vals_ev vals 5 = tid ->
    regs_ok (ENV vals) srB0 R -> know_ok RSEGS (ENV vals) M knA -> above_sp0 M ->
    (* the [kb_rseq]-split auxv terminator rows on the initial memory ([main_know_term]) *)
    ((bv_unsigned sp0 <= bv_unsigned (auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0))%Z /\
     exists E0e : env, ev E0e 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 /\
       (know_ok RSEGS E0e mem0 kn_termT \/ know_ok RSEGS E0e mem0 kn_termF)) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x27510) M (seg_rom RSEGS)) (model1g fd3))
               (t_alt2 KBm KBb).
  Proof.
    intros fd3 KBb KBm vals R M HKBb HKBm HKmb HL P0 P1 P2 P3 P4 P5t HR HK HA HTF.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    (* [comment removed for export] *)
    run_block_keep scr0 38%nat.
    refresh_above vals P0 HA. clear R M. name_state R M.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ knB ltac:(let i := kidx knB (is_krange (EVar 4)) in exact i) _ HK eq_refl)
      as Krnd; cbn [kentry_ok edenot ev ENV] in Krnd.
    pose proof (know_nth RSEGS _ _ knB ltac:(let i := kidx knB (is_kdisj (EVar 0) (EVar 4)) in exact i) _ HK eq_refl)
      as Kdj; cbn [kentry_ok] in Kdj; unfold estart in Kdj; cbn [a_base a_off edenot ev ENV] in Kdj; rewrite P0 in Kdj.
    krdv HK 4%nat 8%Z 8%nat Hrd8.
    { apply flat_intro; cbn [edenot ev ENV]; lia. }
    pose proof (kwr_store_ok RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-384) 8) in exact i)
                  _ _ _ (-384) 8 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hwr8.
    set (dst := adenot (ENV vals) (SA (EVar 0) (-384))) in *.
    set (src := adenot (ENV vals) (SA (EVar 4) 8)) in *.
    assert (Hudst : bv_unsigned dst = (bv_unsigned sp0 - 384)%Z).
    { subst dst. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0, u_small by lia. lia. }
    assert (Husrc : bv_unsigned src = (bv_unsigned (vals_ev vals 4) + 8)%Z).
    { subst src. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite u_small by lia. lia. }
    assert (MC : mcH M dst src 8 (word_to_le_bytes 8 (blob_val false (eb (ENV vals) 2) 8 8))).
    { constructor.
      - lia.
      - reflexivity.
      - exact Hrd8.
      - exact Hwr8.
      - lia.
      - lia.
      - lia. }
    assert (RT : Hoare.ret_ok (Z_to_bv 64 0x20174)) by (apply bv_eq; vm_compute; reflexivity).
    assert (G1 : getr R 1 = Z_to_bv 64 0x20174) by (regv HR (1:reg); reflexivity).
    assert (G10 : getr R 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit).
    assert (G11 : getr R 11 = src) by (regv HR (11:reg); subst src; apply edenot_add_lit).
    assert (G12 : getr R 12 = Z_to_bv 64 8) by (regv HR (12:reg); reflexivity).
    cps_destruct (ref_memcpy M dst src 8 _ (seg_rom RSEGS) MC R (Z_to_bv 64 0x20174) RT G1 G10 G11 G12)
      as (R2 & Hms & Hkeep). clear RT G1 G10 G11 G12.
    replace (Z_to_bv 64 158696) with (0x26be8 : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
    (* [comment removed for export] *)
    assert (HA' : above_sp0 (wbytes M dst (word_to_le_bytes 8 (blob_val false (eb (ENV vals) 2) 8 8)))).
    { intros a Ha. rewrite wbytes_outside; [apply HA; exact Ha | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; right; lia]. }
    clear HA. rename HA' into HA.
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok _ ?sr _ =>
      pose proof (regs_after_keeps vals _ sr _ R2 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep
                    callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?M0 ?kn =>
      let c := eval vm_compute in (carry [mc_store] kn []) in
      lazymatch c with (?kn', ?scs, ?hs) =>
        pose proof (know_after_store RSEGS E M0 kn (SA (EVar 0) (-384)) 8 (EBlob false 2 8 8) (word_to_le_bytes 8 (blob_val false (eb (ENV vals) 2) 8 8))
                      kn' scs hs ltac:(vm_compute; reflexivity) eq_refl HK ltac:(lia)
                      ltac:(apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia) eq_refl) as HK2
      end end.
    clear HK. subst dst.
    lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 70%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (P0' : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (P1' : vals_ev vals1 1 = p0 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    assert (P2' : vals_ev vals1 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (P3' : vals_ev vals1 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P3).
    assert (P4' : vals_ev vals1 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P4).
    assert (P5' : vals_ev vals1 5 = tid) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5t).
    clearbody vals1. clear HL P0 P1 P2 P3 P4 P5t. rename HL1 into HL. rename P0' into P0. rename P1' into P1. rename P2' into P2. rename P3' into P3. rename P4' into P4. rename P5' into P5t.
    change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path hw rnd))) with (ENV vals1) in HR, HK.
    (* Block C, split on the FREE kernel field [kb_rseq] (never fixed): [main_know_term]
       gives the terminator rows of whichever case holds, on the initial memory. They sit
       above sp0, so [kw3_list_above] carries them to the current memory.  Each arm walks
       to the brk(0) ecall at 0x2023c, drops its terminator rows ([knC_T] / [knC_F]) and
       continues in [oom_segC]. *)
    destruct HTF as (Hasp & E0e & HE3 & HT0).
    assert (E3 : ev (ENV vals1) 3 = ev E0e 3) by (cbn [ev ENV]; rewrite P3, HE3; reflexivity).
    assert (S3 : (bv_unsigned sp0 <= bv_unsigned (ev E0e 3))%Z) by (rewrite HE3; exact Hasp).
    destruct HT0 as [HT0|HT0].
    all: pose proof (kw3_list_above _ _ _ _ E3 S3 HA HT0
                       ltac:(cbv [kn_termT kn_termF]; repeat apply Forall_cons; try apply Forall_nil;
                             (do 2 eexists; split; [reflexivity | lia]))) as HT.
    all: clear HT0.
    all: pose proof (w65_kn_app _ _ _ _ _ HK HT) as HKt.
    all: clear HK HT.
    all: rename HKt into HK.
    all: run_block_keep scr0 70%nat.
    all: refresh_above vals1 P0 HA.
    all: clear Hrd8 Hwr8 Hudst Husrc MC Krnd Kdj.
    all: clear R2 M.
    all: try clear R.
    all: name_state R M.
    - (* CONFIG_RSEQ: AT_NULL at pair 28 *)
      change (know_ok RSEGS (ENV vals1) M knCT) in HK. apply (w65_kn_filter _ _ _ not_term) in HK.
      rewrite knC_T in HK. change (regs_ok (ENV vals1) srCT R) in HR.
      apply (oom_segC fd3 KBb KBm srCT vals1 R M ltac:(hnf; left; reflexivity)); assumption.
    - (* no CONFIG_RSEQ: AT_NULL at pair 26 *)
      change (know_ok RSEGS (ENV vals1) M knCF) in HK. apply (w65_kn_filter _ _ _ not_term) in HK.
      rewrite knC_F in HK. change (regs_ok (ENV vals1) srCF R) in HR.
      apply (oom_segC fd3 KBb KBm srCF vals1 R M ltac:(hnf; right; hnf; left; reflexivity)); assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition open_err_branch (KA : TSet) : Prop :=
    forall e vals R M,
      In e openat_errnos ->
      length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 38 = errno_ret e ->
      vals_ev vals 1 = p0 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 -> vals_ev vals 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV vals) M knA ->
      (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x27510) M (seg_rom RSEGS)) model0) KA.

  Lemma oom_seg1 : forall KA KBb KBm,
    open_err_branch KA -> brk_ok_branch KBb -> mmap_ok_branch KBm -> (forall tr, KBm tr -> KBb tr) ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x13548) mem0 (seg_rom RSEGS)) model0)
               (t_alt2 KA (t_alt2 KBm KBb)).
  Proof.
    intros KA KBb KBm HKA HKBb HKBm HKmb.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof ME as (Hhw & Hvl & Hlau & ME').
    assert (HR : regs_ok (E0 (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 a0s path rnd tid regs0) sr_main regs0)
      by (eapply (main_regs_ok (mkProcInputA [a0s; path] envv fs0 stdin0) mbase (0x133fc : word) sp0 a0s path rnd tid regs0 mem0); try eassumption; reflexivity).
    assert (HK : know_ok RSEGS (E0 (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 a0s path rnd tid regs0) mem0 kn_main)
      by (eapply (main_know_ok (mkProcInputA [a0s; path] envv fs0 stdin0) mbase (0x133fc : word) sp0 brk a0s path rnd tid regs0 mem0); try eassumption; reflexivity).
    assert (HTF : (bv_unsigned sp0 <= bv_unsigned (auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0))%Z /\
                  exists E0e : env, ev E0e 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 /\
                    (know_ok RSEGS E0e mem0 kn_termT \/ know_ok RSEGS E0e mem0 kn_termF)).
    { edestruct (main_know_term (mkProcInputA [a0s; path] envv fs0 stdin0) mbase (0x133fc : word) sp0 brk a0s path rnd tid regs0 mem0)
        as [Hasp HT0]; try eassumption; try reflexivity.
      split; [exact Hasp|].
      destruct HT0 as [HT0|HT0]; apply w65_kn_app_r in HT0;
        lazymatch type of HT0 with know_ok _ ?E0e _ _ => exists E0e end;
        (split; [reflexivity | first [left; exact HT0 | right; exact HT0]]). }
    unfold E0 in HR, HK. rewrite Hhw in HR, HK.
    change (Env (vals_ev (vals0 (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 rnd tid regs0)) (blobs_ev (blobs0 a0s path hw rnd))) with (ENV (vals0 (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 rnd tid regs0)) in HR, HK.
    set (vals := vals0 (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 rnd tid regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd) by reflexivity.
    assert (P3 : vals_ev vals 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0) by reflexivity.
    assert (P4 : vals_ev vals 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0) by reflexivity.
    assert (P5t : vals_ev vals 5 = tid) by reflexivity.
    edestruct (main_str (mkProcInputA [a0s; path] envv fs0 stdin0) mbase (0x133fc : word) sp0 brk a0s path rnd tid regs0 mem0) as (Sr & Slo & Shi & Slen);
      try eassumption; try reflexivity.
    1:{ instantiate (1 := 1%nat). lia. }
    cbn [nth in_argv in_envp in_execfn mkProcInputA] in Sr, Slo, Shi, Slen.
    clearbody vals.
    (* [comment removed for export] *)
    run_block_keep scr0 38%nat.
    (* [comment removed for export] *)
    assert (Sr' : rdn RSEGS M (p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd) (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM. unfold p1. cbn [in_argv in_envp in_execfn mkProcInputA]. rewrite (rdn_mem_denot_above RSEGS (ENV vals) mem0 _ 0%nat 0x5c000);
        [exact Sr | vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia
        | pose proof (u64_range (cat_argv_ptr (ed_top rnd) [a0s; path] envv (ia_execfn stdin0) 1)); lia]. }
    (* [comment removed for export] *)
    eapply (rz_openat_file RSEGS _ _ _ model0 ECALLW); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). apply bv_eq. reflexivity.
    - regv HR (12 : reg). vm_compute. reflexivity.
    - (* [comment removed for export] *) rewrite m0_fds. rewrite alloc_fd_fds0. apply fd_lookup_fds0_3.
    - (* [comment removed for export] *) split; [exact Hplen|]. split; [apply path_nonul|]. split.
      { (* the path lies below TASK_SIZE: argv strings end below the stack top *)
        pose proof (argv_ptr_fits _ mbase sp0 brk rnd 1%nat Hlau ltac:(cbn; lia)) as Hf.
        cbn [nth in_argv in_envp in_execfn mkProcInputA] in Hf.
        regv HR (11 : reg). cbn [edenot ev ENV]. rewrite P2. unfold p1.
        cbn [nth in_argv in_envp in_execfn mkProcInputA]. unfold TASK_SIZE. lia. }
      regv HR (11 : reg). cbn [edenot ev ENV]. rewrite P2. exact Sr'.
    - exact Hpne.
    - exact Hpnd.
    - rewrite m0_fs. exact Hfile.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0x2750c + 4)%Z with 0x27510%Z.
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path hw rnd))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
      eapply (HKA e (vals ++ [errno_ret e])); try eassumption.
      + rewrite length_app, HL. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      + rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P3.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P4.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P5t.
      + apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x5c000);
          [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x2750c + 4)%Z with 0x27510%Z.
      rewrite m0_fds. rewrite alloc_fd_fds0.
      change (with_fds (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0))) model0)
        with (model1g (FdFile path (Z_to_bv 64 0))).
      pose proof (regs_set_a0 (ENV vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2.
      assert (HA : above_sp0 M).
      { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x5c000);
          [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
      eapply (oom_seg2 (FdFile path (Z_to_bv 64 0)) KBb KBm vals); try eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem oom_pilot : forall KA KBb KBm,
    open_err_branch KA -> brk_ok_branch KBb -> mmap_ok_branch KBm -> (forall tr, KBm tr -> KBb tr) ->
    realizes RSEGS
      (mkCfg (mkst regs0 (Z_to_bv 64 0x13548) mem0 (seg_rom RSEGS))
             (with_tid tid (with_vdso (ia_vdso stdin0) (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputA [a0s; path] envv fs0 stdin0)))))
      (t_alt2 KA (t_alt2 KBm KBb)).
  Proof. intros. apply oom_seg1; assumption. Qed.

End Pilot.
End S0PilotOOM.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymXfer SymAbove.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StoreOk SimInv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require CatSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ShapeAlg ShapeLaws Nodes MmapSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require MmapSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require FileSim AgentLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ModelAmb.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymExec SymExec2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun SymDrive SymDriveX LibKnowFrame S0LibStdioCall Spec LibWritev RefNodes S0ExitBase S0StdioDefs S0Exit RefMemcpyLib S0Startup S0MainEntry Hoare Frame MallocDefs RefEnframeArith S0EnframeBase S0Enframe S0ReadBase.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StoreOk SimInv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require CatSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ShapeAlg Nodes MmapSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require MmapSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require FileSim AgentLib SymExec SymExec2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun SymDrive SymDriveX Spec LibWritev RefNodes S0ExitBase S0Exit RefMemcpyLib RefLayout S0Startup S0MainEntry Hoare Frame MallocDefs S0EnframeBase S0Enframe S0ReadBase S0World S0TargetPre.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require S0TargetPre.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymHide.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymFold.   (* [comment removed for export] *)
Import SymHide.OptIn.
(* [comment removed for export] *)
Local Ltac SymHide.sc_cands ::= constr:((S0PilotOOM_defs.kn_exec, (S0PilotOOM_defs.srA, (S0PilotOOM_defs.knA, (S0PilotOOM_defs.srB0, (S0PilotOOM_defs.srB, (S0PilotOOM_defs.knB, (S0PilotOOM_defs.knB2, (S0PilotOOM_defs.srC0, (S0PilotOOM_defs.srC, (S0PilotOOM_defs.knC, (S0PilotOOM_defs.knD0, (S0PilotOOM_defs.srD0, (S0PilotOOM_defs.srD, (S0PilotOOM_defs.knD, (S0PilotOOM_defs.srD2, (S0PilotOOM_defs.knD2, (S0PilotOOM_defs.srE0, (S0PilotOOM_defs.srE, (S0PilotOOM_defs.knE, (S0PilotOOM_defs.srF0, (S0PilotOOM_defs.srF, (S0PilotOOM_defs.knF, (S0PilotOOM_defs.srG0, (S0PilotOOM_defs.knG0, (S0PilotOOM_defs.srG, (S0PilotOOM_defs.knG, tt))))))))))))))))))))))))))).
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Module S7W65_defs.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0MainEntry OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0LibStdioCall OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0W65x.S0PilotOOM_defs.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymXfer.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations. Import SX2. Import SX2S.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STOPS_W : list Z := 0x20284%Z :: STOPS.
Definition runW (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_W scr ss [].

Definition bx : expr := EVar 70.

(* [comment removed for export] *)
Definition sc_of (o : option stdio_res) : stdio_res :=
  match o with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.

(* [comment removed for export] *)
Definition knW0 : list kentry := Eval vm_compute in
  (KZero (SA bx 0) (ELit 4096) :: KZero (SA bx 4096) (ELit 4096)
   :: KWr (SA bx 0) 4096 :: KWr (SA bx 4096) 4096
   :: kn_xfer knD2 bx 0 8192 true).
Definition srW0 : list expr := Eval vm_compute in sr_upd srD2 (ridx 10) (EAlu ALU_ADD bx (ELit 8192)).
Definition rW1__t := run scr0 (SS 0x20264 srW0 [] knW0 71).
Definition srW1 : list expr := Eval vm_compute in s_regs (fst (fst rW1__t)).
Definition rW1 := ltac:(SymFold.sf_def rW1__t (srW1, (knW0, tt))).
Definition knW1 : list kentry := Eval vm_compute in kn_after rW1 knW0.

(* [comment removed for export] *)
Definition ENOMEMv : expr := ELit (2 ^ 64 - 12).
Definition srK0 := Eval vm_compute in sr_upd srW1 (ridx 10) ENOMEMv.
Definition rK__t := runW scr0 (SS 0x21378 srK0 [] knW1 71).
Definition srK1 : list expr := Eval vm_compute in s_regs (fst (fst rK__t)).
Definition rK := ltac:(SymFold.sf_def rK__t (srK1, (knW1, tt))).
Definition knK1 : list kentry := Eval vm_compute in kn_after rK knW1.

Definition knU : list kentry := Eval vm_compute in kn_xfer knW1 bx 0 4096 false.
Definition srO0 := Eval vm_compute in sr_upd srW1 (ridx 10) bx.
Definition rO__t := runW scr0 (SS 0x21378 srO0 [] knU 71).
Definition srO1 : list expr := Eval vm_compute in s_regs (fst (fst rO__t)).
Definition rO := ltac:(SymFold.sf_def rO__t (srO1, (knU, tt))).
Definition knO1 : list kentry := Eval vm_compute in kn_after rO knU.

Definition rDd__t := runW scr0 (SS 0x21378 srK0 [] knU 71).
Definition srDd1 : list expr := Eval vm_compute in s_regs (fst (fst rDd__t)).
Definition rDd := ltac:(SymFold.sf_def rDd__t (srDd1, (knU, tt))).
Definition knDd1 : list kentry := Eval vm_compute in kn_after rDd knU.


(* [comment removed for export] *)
Definition kn_inter3 (k1 k2 k3 : list kentry) : list kentry :=
  List.filter (fun K => existsb (kentry_eqb K) k2 && existsb (kentry_eqb K) k3) k1.
Definition srM : list expr := Eval vm_compute in sr_upd srO1 (ridx 10) (EVar 71).
Definition knM : list kentry := Eval vm_compute in kn_inter3 knO1 knK1 knDd1.

(* [comment removed for export] *)
Definition rW2__t := run scr0 (SS 0x20284 srM [] knM 72).
Definition srW2 : list expr := Eval vm_compute in s_regs (fst (fst rW2__t)).
Definition rW2 := ltac:(SymFold.sf_def rW2__t (srW2, (knM, tt))).
Definition knW2 : list kentry := Eval vm_compute in kn_after rW2 knM.


(* [comment removed for export] *)
Definition srN0 : list expr := Eval vm_compute in sr_upd srW2 (ridx 10) ENOMEMv.
Definition rN__t := run scr0 (SS 0x21378 srN0 [] knW2 72).
Definition srN : list expr := Eval vm_compute in s_regs (fst (fst rN__t)).
Definition rN := ltac:(SymFold.sf_def rN__t (srN, (knW2, tt))).
Definition knN : list kentry := Eval vm_compute in kn_after rN knW2.
(* [comment removed for export] *)
Definition resX : stdio_res := Eval vm_compute in sc_of (stdio_call 72 srN knN).
(* [comment removed for export] *)
Definition srX0 : list expr := Eval vm_compute in sc_sr resX.
Definition knX0 : list kentry := Eval vm_compute in sc_kn resX.
Definition rX__t := run scr0 (SS 0x220e8 srX0 [] knX0 104).
Definition srX : list expr := Eval vm_compute in s_regs (fst (fst rX__t)).
Definition rX := ltac:(SymFold.sf_def rX__t (srX, (knX0, tt))).
Definition knX : list kentry := Eval vm_compute in kn_after rX knX0.

(* [comment removed for export] *)
Definition gx : expr := EVar 72.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knG00 : list kentry :=
  KAlign gx 4096 :: KRange gx 0x5c000 (0x7fffff800000 - 69632)
  :: KDisj (SA gx 0) 69632 (SA (EVar 0) (-8388608)) 18446744073709551616
  :: KDisj (SA gx 0) 69632 (SA (EVar 3) 0) 160 :: KDisj (SA gx 0) 69632 (SA (EVar 4) 0) 16
  :: KDisj (SA bx 4096) 4096 (SA gx 0) 69632 :: knW2.
Definition knG0 : list kentry := Eval vm_compute in
  (KZero (SA gx 0) (ELit 69632) :: KWr (SA gx 0) 69632 :: kn_xfer knG00 gx 0 69632 true).
Definition srG0 : list expr := Eval vm_compute in sr_upd srW2 (ridx 10) gx.
Definition scrG : scripts := SCR [true] [] [].   (* [comment removed for export] *)
Definition rG__t := run scrG (SS 0x21378 srG0 [] knG0 73).
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG__t)).
Definition rG := ltac:(SymFold.sf_def rG__t (srG, (knG0, tt))).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ax : expr := EVar 71.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knP00 : list kentry :=
  KAlign ax 4096 :: KRange ax 0x1000 (0x7fffff800000 - 8192)
  :: KDisj (SA ax 0) 8192 (SA (EVar 0) (-8388608)) 18446744073709551616
  :: KDisj (SA ax 0) 8192 (SA (EVar 3) 0) 160 :: KDisj (SA ax 0) 8192 (SA (EVar 4) 0) 16
  :: KDisj (SA (ELit 0) 0x10000) 0x4c000 (SA ax 0) 8192 :: knE.
Definition knP0 : list kentry := Eval vm_compute in kn_xfer knP00 ax 0 8192 false.
Definition srP0 : list expr := Eval vm_compute in sr_upd srE (ridx 10) ax.
Definition scrP : scripts := SCR [true] [] [].   (* [comment removed for export] *)
Definition rP__t := run scrP (SS 0x21378 srP0 [] knP0 72).
Definition srP : list expr := Eval vm_compute in s_regs (fst (fst rP__t)).
Definition rP := ltac:(SymFold.sf_def rP__t (srP, (knP0, tt))).
Definition knP : list kentry := Eval vm_compute in kn_after rP knP0.

(* [comment removed for export] *)
Definition srQ0 : list expr := Eval vm_compute in sr_upd srP (ridx 10) ENOMEMv.
Definition rQ__t := run scr0 (SS 0x213d0 srQ0 [] knP 72).
Definition srQ : list expr := Eval vm_compute in s_regs (fst (fst rQ__t)).
Definition rQ := ltac:(SymFold.sf_def rQ__t (srQ, (knP, tt))).
Definition knQ : list kentry := Eval vm_compute in kn_after rQ knP.
Definition resQX : stdio_res := Eval vm_compute in sc_of (stdio_call 72 srQ knQ).
(* [comment removed for export] *)
Definition srQX0 : list expr := Eval vm_compute in sc_sr resQX.
Definition knQX0 : list kentry := Eval vm_compute in sc_kn resQX.
Definition rQX__t := run scr0 (SS 0x220e8 srQX0 [] knQX0 104).
Definition srQX : list expr := Eval vm_compute in s_regs (fst (fst rQX__t)).
Definition rQX := ltac:(SymFold.sf_def rQX__t (srQX, (knQX0, tt))).
Definition knQX : list kentry := Eval vm_compute in kn_after rQX knQX0.

(* [comment removed for export] *)
Definition knR0 : list kentry := Eval vm_compute in
  (KZero (SA ax 4096) (ELit 4096) :: KWr (SA ax 4096) 4096 :: kn_xfer knP ax 4096 4096 true).
Definition srR0 : list expr := Eval vm_compute in sr_upd srP (ridx 10) (ELit 0).
Definition rR__t := run scr0 (SS 0x213d0 srR0 [] knR0 72).
Definition srR : list expr := Eval vm_compute in s_regs (fst (fst rR__t)).
Definition rR := ltac:(SymFold.sf_def rR__t (srR, (knR0, tt))).
Definition knR : list kentry := Eval vm_compute in kn_after rR knR0.

(* [comment removed for export] *)
Definition srS0 : list expr := Eval vm_compute in sr_upd srR (ridx 10) ENOMEMv.
Definition rS__t := run scr0 (SS 0x21378 srS0 [] knR 72).
Definition srS : list expr := Eval vm_compute in s_regs (fst (fst rS__t)).
Definition rS := ltac:(SymFold.sf_def rS__t (srS, (knR, tt))).
Definition knS : list kentry := Eval vm_compute in kn_after rS knR.
Definition resSX : stdio_res := Eval vm_compute in sc_of (stdio_call 72 srS knS).
(* [comment removed for export] *)
Definition srSX0 : list expr := Eval vm_compute in sc_sr resSX.
Definition knSX0 : list kentry := Eval vm_compute in sc_kn resSX.
Definition rSX__t := run scr0 (SS 0x220e8 srSX0 [] knSX0 104).
Definition srSX : list expr := Eval vm_compute in s_regs (fst (fst rSX__t)).
Definition rSX := ltac:(SymFold.sf_def rSX__t (srSX, (knSX0, tt))).
Definition knSX : list kentry := Eval vm_compute in kn_after rSX knSX0.

(* [comment removed for export] *)
Definition knT00 : list kentry :=
  KAlign gx 4096 :: KRange gx 0x5c000 (0x7fffff800000 - 69632)
  :: KDisj (SA gx 0) 69632 (SA (EVar 0) (-8388608)) 18446744073709551616
  :: KDisj (SA gx 0) 69632 (SA (EVar 3) 0) 160 :: KDisj (SA gx 0) 69632 (SA (EVar 4) 0) 16
  :: KDisj (SA ax 0) 8192 (SA gx 0) 69632 :: knR.
Definition knT0 : list kentry := Eval vm_compute in
  (KZero (SA gx 0) (ELit 69632) :: KWr (SA gx 0) 69632 :: kn_xfer knT00 gx 0 69632 true).
Definition srT0 : list expr := Eval vm_compute in sr_upd srR (ridx 10) gx.
Definition rT__t := run scrG (SS 0x21378 srT0 [] knT0 73).
Definition srT : list expr := Eval vm_compute in s_regs (fst (fst rT__t)).
Definition rT := ltac:(SymFold.sf_def rT__t (srT, (knT0, tt))).
Definition knT : list kentry := Eval vm_compute in kn_after rT knT0.


(* [comment removed for export] *)
Definition LOGE : list sentry :=
  [SE (SA gx 29) 1 (ELit 160); SE (SA gx 69624) 4 (ELit 4060); SE (SA gx 69623) 1 (ELit 0);
   SE (SA gx 65568) 1 (ELit 0); SE (SA gx 30) 2 (ELit 1); SE (SA gx 29) 1 (ELit 0);
   SE (SA gx 28) 1 (ELit 0); SE (SA gx 14) 2 (ELit 1); SE (SA gx 13) 1 (ELit 224)].
(* [comment removed for export] *)
Definition knZ : list kentry := Eval vm_compute in fst (fst (carry LOGE knG [])).
Definition srZ : list expr := Eval vm_compute in
  sr_upd (sr_after_call_j srG (map ridx callee_saved) 73) (ridx 10) (EAlu ALU_ADD gx (ELit 32)).
Definition knZm : list kentry := Eval vm_compute in fst (fst (carry LOGE knT [])).
Definition srZm : list expr := Eval vm_compute in
  sr_upd (sr_after_call_j srT (map ridx callee_saved) 73) (ridx 10) (EAlu ALU_ADD gx (ELit 32)).

(* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)

(* [comment removed for export] *)   (* [comment removed for export] *)
End S7W65_defs.
(* [comment removed for export] *)
Local Ltac SymHide.sc_cands ::= constr:((S0PilotOOM_defs.kn_exec, (S0PilotOOM_defs.srA, (S0PilotOOM_defs.knA, (S0PilotOOM_defs.srB0, (S0PilotOOM_defs.srB, (S0PilotOOM_defs.knB, (S0PilotOOM_defs.knB2, (S0PilotOOM_defs.srC0, (S0PilotOOM_defs.srC, (S0PilotOOM_defs.knC, (S0PilotOOM_defs.knD0, (S0PilotOOM_defs.srD0, (S0PilotOOM_defs.srD, (S0PilotOOM_defs.knD, (S0PilotOOM_defs.srD2, (S0PilotOOM_defs.knD2, (S0PilotOOM_defs.srE0, (S0PilotOOM_defs.srE, (S0PilotOOM_defs.knE, (S0PilotOOM_defs.srF0, (S0PilotOOM_defs.srF, (S0PilotOOM_defs.knF, (S0PilotOOM_defs.srG0, (S0PilotOOM_defs.knG0, (S0PilotOOM_defs.srG, (S0PilotOOM_defs.knG, (S7W65_defs.knW0, (S7W65_defs.srW0, (S7W65_defs.srW1, (S7W65_defs.knW1, (S7W65_defs.srK0, (S7W65_defs.srK1, (S7W65_defs.knK1, (S7W65_defs.knU, (S7W65_defs.srO0, (S7W65_defs.srO1, (S7W65_defs.knO1, (S7W65_defs.srDd1, (S7W65_defs.knDd1, (S7W65_defs.srM, (S7W65_defs.knM, (S7W65_defs.srW2, (S7W65_defs.knW2, (S7W65_defs.srN0, (S7W65_defs.srN, (S7W65_defs.knN, (S7W65_defs.srX0, (S7W65_defs.knX0, (S7W65_defs.srX, (S7W65_defs.knX, (S7W65_defs.knG00, (S7W65_defs.knG0, (S7W65_defs.srG0, (S7W65_defs.srG, (S7W65_defs.knG, (S7W65_defs.knP00, (S7W65_defs.knP0, (S7W65_defs.srP0, (S7W65_defs.srP, (S7W65_defs.knP, (S7W65_defs.srQ0, (S7W65_defs.srQ, (S7W65_defs.knQ, (S7W65_defs.srQX0, (S7W65_defs.knQX0, (S7W65_defs.srQX, (S7W65_defs.knQX, (S7W65_defs.knR0, (S7W65_defs.srR0, (S7W65_defs.srR, (S7W65_defs.knR, (S7W65_defs.srS0, (S7W65_defs.srS, (S7W65_defs.knS, (S7W65_defs.srSX0, (S7W65_defs.knSX0, (S7W65_defs.srSX, (S7W65_defs.knSX, (S7W65_defs.knT00, (S7W65_defs.knT0, (S7W65_defs.srT0, (S7W65_defs.srT, (S7W65_defs.knT, (S7W65_defs.knZ, (S7W65_defs.srZ, (S7W65_defs.knZm, (S7W65_defs.srZm, tt)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Module S7W65.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.MiniExec.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SimInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim.ExitSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ShapeLaws OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Nodes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim.AllocSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.FileSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.AgentLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ModelAmb.SpecConsts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.LibKnowFrame OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0LibStdioCall OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.LibWritev OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefNodes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0ExitBase OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0StdioDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Exit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Startup OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0MainEntry OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Hoare OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Frame OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MallocDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0EnframeBase OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Enframe OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0ReadBase.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0W65x.S0PilotOOM_defs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0W65x.S0PilotOOM.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymXfer OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymAbove S7W65_defs.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit.   (* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.
Tactic Notation "run_blockW" constr(scr) constr(NX) := run_block_gen FUEL STOPS_W scr NX false.
Tactic Notation "run_blockW_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_W scr NX true.

(* [comment removed for export] *)
Definition is_kdisj_at0 (b1 : expr) (o1 : Z) (b2 : expr) (K : kentry) : bool :=
  match K with
  | KDisj (SA c1 k1) _ (SA c2 _) _ => expr_eqb b1 c1 && Z.eqb k1 o1 && expr_eqb b2 c2
  | _ => false
  end.
Ltac auxv_above HK Q0 :=
  lazymatch type of HK with know_ok _ _ _ ?kn =>
    pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kdisj_at0 (EVar 0) (-4294967296) (EVar 3)) in exact i) _ HK eq_refl) as A3;
    pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kdisj_at0 (EVar 0) (-4294967296) (EVar 4)) in exact i) _ HK eq_refl) as A4;
    pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_krange (EVar 3)) in exact i) _ HK eq_refl) as R3;
    pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_krange (EVar 4)) in exact i) _ HK eq_refl) as R4;
    cbn [kentry_ok] in A3, A4, R3, R4; unfold estart in A3, A4; cbn [a_base a_off edenot ev ENV] in A3, A4, R3, R4;
    rewrite Q0 in A3, A4
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bt_ne_not : forall (x : word), (bv_unsigned x < 2 ^ 64 - 1)%Z ->
  branch_taken BC_NE (alu64 ALU_XOR x (Z_to_bv 64 (-1))) (Z_to_bv 64 0) = true.
Proof.
  intros x Hx. cbn [branch_taken]. apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq.
  change (alu64 ALU_XOR x (Z_to_bv 64 (-1))) with (bv_xor x (Z_to_bv 64 (-1))).
  pose proof (u64_range x).
  rewrite bv_xor_unsigned. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  change ((-1) mod 2 ^ 64)%Z with (2 ^ 64 - 1)%Z. change (0 mod 2 ^ 64)%Z with 0%Z.
  intros E. apply Z.lxor_eq in E. lia.
Qed.

(* [comment removed for export] *)
Lemma regs_ok_set_have : forall E sr R (rd : reg) v e,
  regs_ok E sr R -> getr R rd = v -> edenot E e = v -> rd <> 0%bv ->
  regs_ok E (sr_upd sr (ridx rd) e) R.
Proof.
  intros E sr R rd v e HR Hv He Hrd r.
  pose proof (regs_ok_set E sr R rd v e HR Hrd He r) as H.
  rewrite <- H. destruct (decide (r = rd)) as [->|Hne].
  - rewrite getr_same by exact Hrd. exact Hv.
  - rewrite getr_other by exact Hne. reflexivity.
Qed.

Lemma callee_saved_no0 : ~ In (0%bv : reg) callee_saved.
Proof.
  unfold callee_saved. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.

Definition is_kzero_cov (b : expr) (k n : Z) (K : kentry) : bool :=
  match K with
  | KZero (SA b' k') (ELit n') => expr_eqb b b' && Z.leb k' k && Z.leb (k + n) (k' + n')
  | _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Section World.
  Context {ACEIL__ : ACeil} {RUNW__ : RunW}.   (* [comment removed for export] *)
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable hw : word.    (* [comment removed for export] *)
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_launch (mkProcInputA [a0s; path] envv fs0 stdin0) hw mbase sp0 brk rnd tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hceil : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma atop_sp0 : forall r m na sb b l mb, atop_ok (mkVmMapsFull r m na sb b l mb sp0).
  Proof. intros. unfold atop_ok, alloc_top. cbn [vm_init_sp]. rewrite Hceil. unfold stack_max_size. lia. Qed.
  (* the launch's own record ([main_launch]'s third part) *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rnd) (mkProcInputA [a0s; path] envv fs0 stdin0).
  (* the launch's mmap base is in the covered band ([Run.valid_mmap_base]) *)
  Lemma mbase_lo : (mmap_base_min <= bv_unsigned mbase)%Z.
  Proof.
    pose proof Hlau as Hl. cbn [entry_launch_ok_va] in Hl. destruct Hl as (_ & _ & Hb).
    exact (proj1 (MmapBase.valid_launch_base_sv48_in_band _ _ Hb)).
  Qed.
  Lemma sp0_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Proof. exact (proj1 Hvsp). Qed.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpnd : openat_plain_name path = true.   (* [comment removed for export] *)
  Hypothesis Hplen : (length path <= 4095)%nat.
  (* [comment removed for export] *)
  Variable fd3 : FdEntry.
  (* [comment removed for export] *)
  Variable SI : (word -> option byte) -> Prop.
  Hypothesis SI_step : forall M M' : word -> option byte,
    (forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M' a = M a) -> SI M -> SI M'.

  #[local] Notation ENVv := (ENV a0s path hw rnd).
  (* [comment removed for export] *)
  (* the run's reserved ledger ([State.init_reserved]) *)
  #[local] Notation RES := (init_reserved (segments_reserved RSEGS) mbase sp0 (ia_kernel stdin0)).
  Lemma RES_shape : Forall small_ent RES /\ (length RES <= 6)%nat.
  Proof.
    destruct (init_reserved_shape _ mbase sp0 (ia_kernel stdin0) mbase_lo sp0_lo S0PilotOOM.segres_small) as [A B].
    rewrite S0PilotOOM.segres_len in B. split; [exact A| lia].
  Qed.
  (* a window from the segments' top to 2^44 is free of the ledger *)
  Lemma RES_low_free : forall b n : word, (0x5c000 <= bv_unsigned b)%Z -> (bv_unsigned b + bv_unsigned n <= 2 ^ 44)%Z ->
    region_free RES b n = true.
  Proof.
    intros b n Hb Hn. apply init_reserved_low_free; [exact mbase_lo | exact sp0_lo | | exact Hn].
    intros ra rs Hin. pose proof (S0PilotOOM.segres_below ra rs Hin). lia.
  Qed.

  (* [comment removed for export] *)
  Ltac si_block HSI Rn Mn :=
    lazymatch goal with
    | EQM : ?M' = mem_denot ?E ?Mo ?log, HK : know_ok ?segs ?E ?M' ?kn, HR : regs_ok ?E _ ?R' |- _ =>
        let H := fresh "HSI" in
        assert (H : SI M');
        [ apply (SI_step Mo M'); [| exact HSI]; intros xa Hxa; rewrite EQM;
          apply (mem_denot_above_kb segs E M' Mo kn log 0%nat 0x5c000 0x7fff7f800000 xa HK);
          [ vm_compute; reflexivity | lia | cbn [ev ENV]; pins; lia | cbn [ev ENV]; pins; lia | lia | lia ]
        | clear HSI EQM; try clear Mn; rename H into HSI; try rename M' into Mn; try clear Rn; try rename R' into Rn ]
    end.

  (* [comment removed for export] *)
  Ltac si_fill HSI :=
    lazymatch goal with
    | |- SI (zfill ?a ?n ?M) => apply (SI_step M); [| exact HSI]; intros xa Hxa; apply zfill_out; rewrite ?u64_lit by lia; lia
    | |- SI (unfill ?a ?n ?M) => apply (SI_step M); [| exact HSI]; intros xa Hxa; apply unfill_outside; rewrite ?u64_lit by lia; lia
    end.

  (* [comment removed for export] *)
  Definition fdsV : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) fd3.
  Definition modelV (VM : VmMaps) : Model := mkModelA fdsV VM stdin0 fs0 None (Some tid) None.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mV_vmmaps : forall VM, m_vmmaps (modelV VM) = VM.  Proof. reflexivity. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition model1V : Model := mkModelA fdsV (mkVmMapsFull RES [] [] brk brk LIM mbase sp0) stdin0 fs0 None (Some tid) None.

  Definition brk_ok_entry (KB : TSet) : Prop :=
    forall vals R M,
      length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 70 = brk ->
      vals_ev vals 1 = p0 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 -> vals_ev vals 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 ->
      vals_ev vals 5 = tid ->
      regs_ok (ENVv vals) srD2 R -> know_ok RSEGS (ENVv vals) M knD2 -> SI M ->
      realizes RSEGS
        (mkCfg (mkst (regupd R 10 (Z_to_bv 64 (bv_unsigned brk + 8192))) (Z_to_bv 64 0x20264)
                     (zfill brk (Z_to_bv 64 8192) M) (seg_rom RSEGS))
               (mkModelA fdsV (mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [] brk
                                            (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0)
                        stdin0 fs0 None (Some tid) None)) KB.

  Definition mmap_ok_entry (KB : TSet) : Prop :=
    forall vals R M (hint a : word),
      length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 70 = brk ->
      vals_ev vals 1 = p0 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 -> vals_ev vals 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 ->
      vals_ev vals 5 = tid ->
      regs_ok (ENVv vals) srE R -> know_ok RSEGS (ENVv vals) M knE -> SI M ->
      grant_ok_na hint model1V a 8192 = true ->
      realizes RSEGS (mkCfg (mkst (regupd R 10 a) (Z_to_bv 64 0x21378)
                                    (unfill a (Z_to_bv 64 8192) M) (seg_rom RSEGS))
                              (noaccess_model a (Z_to_bv 64 8192) model1V)) KB.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variable K : TSet.

  (* [comment removed for export] *)
(* [comment removed for export] *)
  Definition w65_vm (VM : VmMaps) (mb gm : word) : Prop :=
    vm_reserved VM = RES /\ vm_limit VM = LIM /\
    ((vm_maps VM = [(gm, Z_to_bv 64 69632); (mb, Z_to_bv 64 8192)]
      /\ (bv_unsigned gm + 69632 <= bv_unsigned mb \/ bv_unsigned mb + 8192 <= bv_unsigned gm)%Z)
     \/ (vm_maps VM = [(gm, Z_to_bv 64 69632); (Z_to_bv 64 (bv_unsigned mb + 4096), Z_to_bv 64 4096)]
      /\ (bv_unsigned gm + 69632 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned gm)%Z)).

  (* [comment removed for export] *)
  Definition w65_xG (VM : VmMaps) (gm : word) : Prop :=
    exists (maps na : list (word * word)),
      VM = mkVmMapsFull RES ((gm, Z_to_bv 64 69632) :: maps) na brk (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0
      /\ ((maps = [(brk, Z_to_bv 64 8192)] /\ (na = [] \/ na = [(brk, Z_to_bv 64 4096)]))
          \/ (maps = [(Z_to_bv 64 (bv_unsigned brk + 4096), Z_to_bv 64 4096)] /\ na = [])).

  Definition exitG_branch : Prop :=
    forall vals R M VM,
      length vals = 105%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 -> vals_ev vals 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 ->
      vals_ev vals 70 = brk -> vals_ev vals 5 = tid ->
      regs_ok (ENVv vals) srZ R -> know_ok RSEGS (ENVv vals) M knZ ->
      vm_pre VM brk (vals_ev vals 72) -> w65_vm VM brk (vals_ev vals 72) -> w65_xG VM (vals_ev vals 72) -> SI M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1359c) M (seg_rom RSEGS)) (modelV VM)) K.

  Lemma w65_G : forall vals R M VM,
    exitG_branch ->
    length vals = 73%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 -> vals_ev vals 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 ->
    vals_ev vals 70 = brk -> vals_ev vals 5 = tid ->
    regs_ok (ENVv vals) srG0 R -> know_ok RSEGS (ENVv vals) M knG0 ->
    vm_pre VM brk (vals_ev vals 72) -> w65_vm VM brk (vals_ev vals 72) -> w65_xG VM (vals_ev vals 72) -> SI M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x21378) M (seg_rom RSEGS)) (modelV VM)) K.
  Proof.
    intros vals R M VM EXIT HL P0 P2 P3 P4 P70 P5 HR HK HVM HVS HVX HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ knG0 ltac:(let i := kidx knG0 (is_krange gx) in exact i) _ HK eq_refl)
      as Kgm; cbn [kentry_ok edenot ev ENV] in Kgm.
    pose proof (know_nth RSEGS _ _ knG0 ltac:(let i := kidx knG0 (is_kalign gx) in exact i) _ HK eq_refl)
      as Kga; cbn [kentry_ok edenot ev ENV] in Kga.
    pose proof (know_nth RSEGS _ _ knG0 ltac:(let i := kidx knG0 (is_kdisj bx gx) in exact i) _ HK eq_refl)
      as Kgd; cbn [kentry_ok] in Kgd; unfold estart in Kgd; cbn [a_base a_off edenot ev ENV] in Kgd; rewrite P70 in Kgd.
    set (gm := vals_ev vals 72) in *.
    (* [comment removed for export] *)
    run_block_keep scrG 73%nat.
    { unfold sc_denot. cbn [edenot ev ENV]. apply bt_ne_not. subst gm. lia. }
    si_block HSI R M.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?MG ?kn =>
      krdv HK 70%nat 4136%Z 8%nat Hmem; [apply flat_intro; cbn [edenot ev ENV]; rewrite ?P70; lia|];
      krdv HK 70%nat 4152%Z 8%nat Hmw; [apply flat_intro; cbn [edenot ev ENV]; rewrite ?P70; lia|];
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kzero_cov gx 9 8) in exact i) _ HK eq_refl) as Kz;
      cbn [kentry_ok] in Kz; unfold elenZ, estart in Kz; cbn [a_base a_off edenot ev ENV] in Kz;
      pose proof (kwr_store_ok RSEGS E _ kn ltac:(let i := kidx kn (is_kwr_cov gx 13 69615) in exact i)
                    _ _ _ 13 (Z.to_nat 69615) HK eq_refl ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as Hok;
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kimg_cov 69328 96) in exact i) _ HK eq_refl) as Kimg;
      cbn [kentry_ok] in Kimg
    end.
    fold gm in Kz, Hmem, Hmw, Hok.
    unfold adenot, v_addi in Hmem, Hmw, Hok. cbn [a_base a_off edenot ev ENV] in Hmem, Hmw, Hok.
    rewrite P70 in Hmem, Hmw. fold gm in Hok.
    change (bv_unsigned (Z_to_bv 64 69623)) with 69623%Z in Kz.
    assert (EF : efH M (Z_to_bv 64 1) (bv_unsigned brk + 4120) (bv_unsigned gm) 72480 0 65536 0 0 69616
                     (bv_unsigned gm + 16) 1).
    { constructor.
      - vm_compute. reflexivity.
      - unfold slot_start, UNIT. lia.
      - vm_compute. reflexivity.
      - pose proof (u64_range brk). lia.
      - pose proof (u64_range gm). lia.
      - lia.
      - lia.
      - lia.
      - intros _. vm_compute. reflexivity.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - replace (bv_unsigned brk + 4120 + 16)%Z with (bv_unsigned brk + 4136)%Z by lia.
        rewrite Hmem. subst gm. rewrite Z_to_bv_bv_unsigned. reflexivity.
      - replace (bv_unsigned brk + 4120 + 32)%Z with (bv_unsigned brk + 4152)%Z by lia. exact Hmw.
      - replace (bv_unsigned gm + 16 - 4)%Z with (bv_unsigned gm + 9 + 3)%Z by lia. apply (proj2 Kz). lia.
      - replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 9 + 4)%Z by lia. apply (proj2 Kz). lia.
      - intros C. exfalso. apply C. reflexivity.
      - replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 13)%Z by lia.
        replace (Z.to_nat (69616 - 1)) with (Z.to_nat 69615) by reflexivity. exact Hok.
      - intros j Hj. unfold SCT. apply (proj2 (proj2 Kimg)). lia. }
    assert (RT : Hoare.ret_ok (Z_to_bv 64 0x1359c)) by (apply bv_eq; vm_compute; reflexivity).
    assert (G1 : getr R 1 = Z_to_bv 64 0x1359c) by (regv HR (1:reg); reflexivity).
    assert (G10 : getr R 10 = Z_to_bv 64 (bv_unsigned brk + 4120)).
    { regv HR (10:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
      rewrite P70. reflexivity. }
    assert (G11 : getr R 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity).
    assert (G12 : getr R 12 = Z_to_bv 64 65536) by (regv HR (12:reg); reflexivity).
    assert (G13 : getr R 13 = Z_to_bv 64 1) by (regv HR (13:reg); reflexivity).
    cps_destruct (enframe_run M (Z_to_bv 64 1) _ _ _ _ _ _ _ _ _ _ EF R (seg_rom RSEGS) (Z_to_bv 64 0x1359c)
                G1 RT G10 G11 G12 G13) as (R2 & Hms & Hkeep & HA0).
    clear RT G1 G10 G11 G12 G13.
    replace (Z_to_bv 64 135140) with (0x20fe4 : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
    (* [comment removed for export] *)
    replace (memF M 0 65536 69616 (bv_unsigned gm + 16) 1) with (mem_denot (ENVv vals) M LOGE).
    2:{ unfold memF. cbv delta [mF mE mE1 mD] beta zeta.
        replace (69616 - 4 - 65536 - 16 * 1)%Z with 4060%Z by reflexivity.
        replace (69616 * 0 / 16 + 1)%Z with 1%Z by reflexivity.
        change (1 =? 0)%Z with false. change (4060 =? 0)%Z with false. change (4060 <? 5)%Z with false.
        cbv iota.
        replace (0 + 32 * res_code 4060)%Z with 160%Z by reflexivity.
        replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 13)%Z by lia.
        replace (bv_unsigned gm + 16 - 2)%Z with (bv_unsigned gm + 14)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 - 4)%Z with (bv_unsigned gm + 28)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 - 3)%Z with (bv_unsigned gm + 29)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 - 2)%Z with (bv_unsigned gm + 30)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 + 65536)%Z with (bv_unsigned gm + 65568)%Z by lia.
        replace (bv_unsigned gm + 16 + 69616 - 4 - 5)%Z with (bv_unsigned gm + 69623)%Z by lia.
        replace (bv_unsigned gm + 16 + 69616 - 4 - 4)%Z with (bv_unsigned gm + 69624)%Z by lia.
        unfold LOGE. cbn [mem_denot]. unfold adenot. cbn [a_base a_off edenot gx ev ENV]. fold gm. unfold v_addi.
        change (word_to_le_bytes 1 (Z_to_bv 64 160)) with [Z_to_bv 8 160].
        change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
        change (word_to_le_bytes 1 (Z_to_bv 64 224)) with [Z_to_bv 8 224].
        reflexivity. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?MG ?kn =>
      pose proof (carry_after RSEGS E MG LOGE kn [] knZ [] _ ltac:(vm_compute; reflexivity)
                    ltac:(cbn [log_flat LOGE]; unfold flat, estart; cbn [a_base a_off edenot gx ev ENV]; fold gm;
                          repeat split; lia)
                    HK ltac:(constructor)) as HK2
    end.
    (* [comment removed for export] *)
    assert (HSI2 : SI (mem_denot (ENVv vals) M LOGE)).
    { apply (SI_step M); [|exact HSI]. intros xa Hxa.
      apply (mem_denot_above_kb RSEGS (ENVv vals) _ M knZ LOGE 0%nat 0x5c000 0x7fff7f800000 xa HK2);
        [vm_compute; reflexivity | lia | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia | lia]. }
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok _ ?sr _ =>
      pose proof (regs_after_keeps vals _ sr R R2 callee_saved ltac:(rewrite HL; vm_compute; reflexivity)
                    HR Hkeep callee_saved_no0) as HR2 end.
    rewrite HL in HR2. clear HR.
    set (vals2 := vals ++ junk_vals R2) in *.
    assert (HL2 : length vals2 = 105%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals2 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (Q3 : vals_ev vals2 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P3).
    assert (Q4 : vals_ev vals2 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P4).
    assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
    assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
    assert (Q72 : vals_ev vals2 72 = gm) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); reflexivity).
    change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path hw rnd))) with (ENVv vals2) in HR2.
    pose proof (regs_ok_set_have (ENVv vals2) _ R2 10 _ (EAlu ALU_ADD gx (ELit 32)) HR2 HA0
                  ltac:(rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot gx ev ENV];
                        rewrite Q72; f_equal; lia) ltac:(discriminate)) as HR3.
    clear HR2.
    lazymatch type of HR3 with regs_ok _ ?sr _ => replace sr with srZ in HR3 by (vm_compute; reflexivity) end.
    lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
    clear HK2 HK.
    change (Env (vals_ev (vals ++ junk_vals R2)) (blobs_ev (blobs0 a0s path hw rnd))) with (ENVv vals2) in HK3.
    change (mem_denot (Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rnd))) M LOGE) with (mem_denot (ENVv vals) M LOGE) in HSI2.
    apply (EXIT vals2 R2 _ VM HL2 Q0 Q2 Q3 Q4 Q70 Q5 HR3 HK3); [rewrite Q72; exact HVM | rewrite Q72; exact HVS | rewrite Q72; exact HVX | exact HSI2].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition VMk : VmMaps :=
    mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [] brk (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0.
  Definition VMo : VmMaps :=
    mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [(brk, Z_to_bv 64 4096)] brk (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0.
  Definition VMd : VmMaps :=
    mkVmMapsFull RES [(Z_to_bv 64 (bv_unsigned brk + 4096), Z_to_bv 64 4096)] [] brk
                 (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0.
  Definition vm_mid (VM : VmMaps) : Prop := VM = VMk \/ VM = VMo \/ VM = VMd.


  Lemma vm_mid_shape : forall VM, vm_mid VM ->
    vm_reserved VM = RES /\ vm_limit VM = LIM
    /\ exists mp ms, vm_maps VM = [(mp, ms)]
       /\ (bv_unsigned ms = 8192 /\ mp = brk \/ bv_unsigned ms = 4096 /\ bv_unsigned mp = bv_unsigned brk + 4096)%Z.
  Proof.
    intros VM HV. pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi.
    destruct HV as [-> | [-> | ->]]; cbn [VMk VMo VMd vm_reserved vm_limit vm_maps];
      (split; [reflexivity|]); (split; [reflexivity|]); eexists _, _; (split; [reflexivity|]);
      rewrite ?u64_lit by lia.
    - left. split; [reflexivity | reflexivity].
    - left. split; [reflexivity | reflexivity].
    - right. split; reflexivity.
  Qed.

  Lemma vm_mid_grant_exists : forall hint VM, vm_mid VM -> exists a, grant_ok hint (modelV VM) a (page_round_up_Z 69632) = true.
  Proof.
    intros hint VM HV. pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi.
    cps_destruct (vm_mid_shape VM HV) as (Hr & Hl & mp & ms & Hm & Hms).
    change (page_round_up_Z 69632) with 69632%Z.
    apply grant_exists.
    - (* [comment removed for export] *) rewrite mV_vmmaps. destruct HV as [-> | [-> | ->]]; apply atop_sp0.
    - lia.
    - (* the length is a whole number of pages *) reflexivity.
    - rewrite mV_vmmaps, Hr, Hm. destruct RES_shape as [RS _]. apply Forall_app. split.
      + eapply Forall_impl; [|exact RS]. unfold small_ent. cbn beta. intros p [[X1 X2] X3]. lia.
      + destruct Hms as [[Hms1 _] | [Hms1 _]]; repeat constructor; cbn [snd]; lia.
    - rewrite mV_vmmaps, Hr, Hm. destruct RES_shape as [_ RL]. rewrite length_app. cbn [length]. lia.
    - apply grant_budget_intro; [reflexivity | reflexivity |]. rewrite mV_vmmaps.
      unfold vm_live_bytes. rewrite Hm, Hl. cbn [live_bytes]. pose proof LIM_ge. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma vm_mid_atop : forall VM, vm_mid VM -> atop_ok VM.
  Proof. intros VM [-> | [-> | ->]]; apply atop_sp0. Qed.

  Lemma vm_mid_grant : forall hint VM a, vm_mid VM -> grant_ok hint (modelV VM) a 69632 = true ->
    (bv_unsigned a mod 4096 = 0 /\ 0x5c000 <= bv_unsigned a /\ bv_unsigned a + 69632 <= alloc_ceiling
     /\ (bv_unsigned brk + 8192 <= bv_unsigned a \/ bv_unsigned a + 69632 <= bv_unsigned brk + 4096))%Z
    /\ (forall mp ms, vm_maps VM = [(mp, ms)] ->
          (bv_unsigned a + 69632 <= bv_unsigned mp \/ bv_unsigned mp + bv_unsigned ms <= bv_unsigned a)%Z)
    /\ region_free RES a (Z_to_bv 64 69632) = true.
  Proof.
    intros hint VM a HV Hg. pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi.
    cps_destruct (vm_mid_shape VM HV) as (Hr & Hl & mp & ms & Hm & Hms).
    cps_destruct (grant_ok_unpack _ _ _ _ Hg) as (Hal & Hpos & Hce & Hrf & Hlive).
    rewrite mV_vmmaps in Hrf. rewrite Hr, Hm in Hrf. rewrite mV_vmmaps in Hce.
    assert (Grf : region_free RES a (Z_to_bv 64 69632) = true)
      by (rewrite region_free_app_split in Hrf; apply andb_prop in Hrf; exact (proj1 Hrf)).
    pose proof (atop_ok_grant _ _ _ (vm_mid_atop VM HV) Hce) as Hce'. clear Hce. rename Hce' into Hce.
    pose proof alloc_ceiling_range as Hcr.
    unfold page_size in Hal. pose proof (u64_range a) as Ha.
    assert (Hn : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by (apply u64_lit; lia).
    (* the segment entries sit first in the ledger *)
    assert (RSin : forall e, In e (segments_reserved RSEGS) -> In e (RES ++ [(mp, ms)])).
    { intros e He. apply in_or_app. left. apply S0PilotOOM.RESX_seg_in. exact He. }
    pose proof (region_free_In _ _ _ (Z_to_bv 64 65536) (Z_to_bv 64 12288) Hrf ltac:(apply RSin; rewrite S0PilotOOM.segres_eq; cbn [In]; tauto)) as D1.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 77824) (Z_to_bv 64 86016) Hrf ltac:(apply RSin; rewrite S0PilotOOM.segres_eq; cbn [In]; tauto)) as D2.   (* [comment removed for export] *)
    pose proof (region_free_In _ _ _ (Z_to_bv 64 167936) (Z_to_bv 64 208896) Hrf ltac:(apply RSin; rewrite S0PilotOOM.segres_eq; cbn [In]; tauto)) as D4.
    pose proof (region_free_In _ _ _ mp ms Hrf ltac:(apply in_or_app; right; left; reflexivity)) as D5.
    rewrite Hn in D1, D2, D4, D5. rewrite !u64_lit in D1 by lia. rewrite !u64_lit in D2 by lia. rewrite !u64_lit in D4 by lia.
    assert (Ha4096 : (4096 <= bv_unsigned a)%Z).
    { destruct (proj1 (Z.mod_divide (bv_unsigned a) 4096 ltac:(lia)) Hal) as [q Hq]. lia. }
    pose proof (u64_range mp).
    split.
    2:{ split; [| exact Grf]. intros mp' ms' Hm'. rewrite Hm in Hm'. injection Hm' as <- <-. exact D5. }
    destruct Hms as [[Hms1 ->] | [Hms1 Hmp]]; rewrite ?Hms1, ?Hmp in D5; repeat split; lia.
  Qed.

  Lemma w65_mid : forall vals R M VM,
    exitG_branch ->
    length vals = 72%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 -> vals_ev vals 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 ->
    vals_ev vals 70 = brk -> vals_ev vals 5 = tid ->
    regs_ok (ENVv vals) srM R -> know_ok RSEGS (ENVv vals) M knM -> vm_mid VM -> SI M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x20284) M (seg_rom RSEGS)) (modelV VM))
               K.
  Proof.
    intros vals R M VM EXIT HL P0 P2 P3 P4 P70 P5 HR HK HV HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    (* [comment removed for export] *)
    run_block_keep scr0 72%nat. si_block HSI R M.
    (* [comment removed for export] *)
    eapply (rz_mmap_anon04 RSEGS _ _ _ (modelV VM) ECALLW 69632).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (11 : reg). reflexivity.
    - lia.
    - regv HR (12 : reg). reflexivity.
    - regv HR (13 : reg). reflexivity.
    - regv HR (14 : reg). apply bv_eq. reflexivity.
    - regv HR (15 : reg). reflexivity.
    - (* LPS 727298f3 (#144/#146): the hint is this call's own a0, the literal NULL *)
      regv HR (10 : reg). apply place_declined_b_null.
    - apply vm_mid_grant_exists. exact HV.
    - (* [comment removed for export] *)
      intros a Hg. rewrite v_addi_pc4 by lia. change (0x21374 + 4)%Z with 0x21378%Z.
      change (page_round_up_Z 69632) with 69632%Z in Hg |- *.
      destruct (vm_mid_grant _ VM a HV Hg) as ((Gal & Glo & Ghi & Gdj) & Gsep & Grf).
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [a] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [a] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      clear HR HK.
      set (vals2 := vals ++ [a]) in *.
      assert (HL2 : length vals2 = 73%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (Q2 : vals_ev vals2 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
      assert (Q3 : vals_ev vals2 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P3).
      assert (Q4 : vals_ev vals2 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P4).
      assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
      assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
      assert (Q72 : vals_ev vals2 72 = a).
      { subst vals2. rewrite <- HL. rewrite <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
      clearbody vals2. clear HL P0 P2 P3 P4 P70 P5 vals. rename HL2 into HL.
      change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path hw rnd))) with (ENVv vals2) in HR2, HK2.
      pose proof (regs_set_a0 (ENVv vals2) _ _ a gx HR2 ltac:(cbn [edenot gx ev ENV]; exact Q72)) as HR. clear HR2.
      (* [comment removed for export] *)
      lazymatch type of HK2 with know_ok _ _ ?Mc _ =>
        assert (HK3 : know_ok RSEGS (ENVv vals2) Mc knG00) end.
      { pose proof alloc_ceiling_range as Hcr. auxv_above HK2 Q0.
        unfold knG00. apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|exact HK2]]]]]].
        - apply kalign_intro; [lia|]. cbn [edenot gx ev ENV]. rewrite Q72. exact Gal.
        - apply krange_intro. cbn [edenot gx ev ENV]. rewrite Q72. lia.
        - (* [comment removed for export] *) cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot gx ev ENV]. rewrite Q0, Q72. lia.
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot gx ev ENV]. rewrite Q72. lia.
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot gx ev ENV]. rewrite Q72. lia.
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot bx gx ev ENV]. rewrite Q70, Q72. lia. }
      clear HK2.
      pose proof (xfer_zfill RSEGS (ENVv vals2) _ knG00 gx 0 a 69632 HK3
                    ltac:(unfold estart; cbn [a_base a_off edenot gx ev ENV]; rewrite Q72; lia)
                    ltac:(lia) ltac:(lia)) as HK.
      clear HK3.
      lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knG0 in HK by (vm_compute; reflexivity) end.
      apply (w65_G vals2 _ _ _ EXIT HL Q0 Q2 Q3 Q4 Q70 Q5 HR HK).
      4:{ si_fill HSI. }
      3:{ rewrite Q72. unfold w65_xG, mmap_model. rewrite ?with_vmmaps_vm, ?mV_vmmaps.
          destruct HV as [-> | [-> | ->]]; cbn [VMk VMo VMd vm_reserved vm_limit vm_maps vm_noaccess vm_start_brk vm_brk vm_mmap_base].
          - eexists _, _. split; [reflexivity|]. left. split; [reflexivity| left; reflexivity].
          - eexists _, _. split; [reflexivity|]. left. split; [reflexivity| right; reflexivity].
          - eexists _, _. split; [reflexivity|]. right. split; reflexivity. }
      2:{ rewrite Q72. cps_destruct (vm_mid_shape VM HV) as (Hr & Hl & mp & ms & Hm & Hms).
          unfold w65_vm, mmap_model. rewrite ?with_vmmaps_vm, ?mV_vmmaps. cbn [vm_reserved vm_limit vm_maps]. rewrite Hr, Hl, Hm.
          split; [reflexivity|]. split; [reflexivity|].
          specialize (Gsep mp ms Hm). pose proof (u64_range mp).
          destruct Hms as [[Hms1 ->] | [Hms1 Hmp]].
          - left. split; [rewrite <- (Z_to_bv_bv_unsigned 64 ms), Hms1; reflexivity | lia].
          - right. split; [rewrite <- (Z_to_bv_bv_unsigned 64 ms), Hms1, <- (Z_to_bv_bv_unsigned 64 mp), Hmp; reflexivity | lia]. }
      (* [comment removed for export] *)
      rewrite Q72. cps_destruct (vm_mid_shape VM HV) as (Hr & Hl & mp & ms & Hm & Hms).
      unfold vm_pre, mmap_model. rewrite ?with_vmmaps_vm, ?mV_vmmaps. cbn [vm_reserved vm_limit vm_maps vm_noaccess vm_start_brk vm_brk].
      rewrite Hr, Hl, Hm.
      assert (Hn : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by (apply u64_lit; lia).
      split.
      { (* the ledger is the run's; the new grant and the break page miss it *)
        apply (res_ok_init _ mbase sp0 (ia_kernel stdin0)); [exact mbase_lo | exact sp0_lo | exact S0PilotOOM.segres_small | reflexivity |].
        intros e He. cbn [vm_maps In] in He. destruct He as [<- | [<- | []]]; cbn [fst snd].
        - exact Grf.
        - apply RES_low_free; destruct Hms as [[Hms1 ->] | [Hms1 Hmp]]; lia. }
      split; [reflexivity|]. split; [apply map_has_head|].
      pose proof (u64_range mp) as Hmpr. pose proof (Gsep mp ms Hm) as Gsp.
      split.
      { constructor; [cbn [fst snd]; rewrite ?Hn; lia|]. constructor; [|constructor].
        cbn [fst snd]. destruct Hms as [[Hms1 ->] | [Hms1 Hmp]]; lia. }
      split; [cbn; lia|].
      split; [cbn [live_bytes]; rewrite Hn; lia|].
      split.
      { exists (mp, ms). split; [cbn [In]; tauto|]. cbn [fst snd].
        split; [intros Emp; apply (f_equal bv_unsigned) in Emp; destruct Hms as [[Hms1 ->] | [Hms1 Hmp]]; lia|].
        destruct Hms as [[Hms1 ->] | [Hms1 Hmp]]; lia. }
      (* [comment removed for export] *)
      constructor; [|constructor; [constructor | constructor]].
      constructor; [|constructor]. unfold S0TargetPre.iv_disjoint. cbn [fst snd]. rewrite Hn. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac guard_tail EXIT HL P0 P1 P2 P3 P4 P70 P5 VMX HSI Rn Mn :=
    run_blockW_keep scr0 71%nat; si_block HSI Rn Mn;
    lazymatch goal with
    | HR' : regs_ok _ ?sr ?R', HK' : know_ok _ _ ?M' ?kn |- _ =>
      (* [comment removed for export] *)
      pose proof (env_app_regs _ [getr R' 10] _ sr R' ltac:(rewrite HL; vm_compute; reflexivity) HR') as HR2;
      pose proof (env_app_know RSEGS _ [getr R' 10] _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK') as HK2;
      clear HR' HK';
      lazymatch goal with
      | |- realizes _ (mkCfg (mkst _ _ _ _) _) _ =>
        lazymatch type of HL with length ?vals = _ =>
        set (vals2 := vals ++ [getr R' 10]) in *;
        assert (HL2 : length vals2 = 72%nat) by (subst vals2; rewrite length_app, HL; reflexivity);
        assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0);
        assert (Q2 : vals_ev vals2 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2);
        assert (Q3 : vals_ev vals2 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P3);
        assert (Q4 : vals_ev vals2 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P4);
        assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70);
        assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5);
        assert (Q71 : vals_ev vals2 71 = getr R' 10)
          by (subst vals2; rewrite <- HL; rewrite <- (Nat.add_0_r (length vals)); rewrite vals_ev_app_r; reflexivity);
        change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path hw rnd))) with (ENVv vals2) in HR2, HK2;
        pose proof (regs_ok_set_have (ENVv vals2) _ R' 10 _ (EVar 71) HR2 eq_refl
                      ltac:(cbn [edenot ev ENV]; exact Q71) ltac:(discriminate)) as HR3;
        clear HR2;
        lazymatch type of HR3 with regs_ok _ ?sr3 _ => replace sr3 with srM in HR3 by (vm_compute; reflexivity) end;
        pose proof (know_ok_sub RSEGS (ENVv vals2) M' kn knM ltac:(vm_compute; reflexivity) HK2) as HK3;
        clear HK2;
        apply (w65_mid vals2 R' M' VMX EXIT HL2 Q0 Q2 Q3 Q4 Q70 Q5 HR3 HK3); [ | exact HSI ]
        end
      end
    end.

  Theorem brk_ok_worldV : exitG_branch -> brk_ok_entry K.
  Proof.
    intros EXIT vals R M HL P0 P70 P1 P2 P3 P4 P5 HR HK HSI0.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    assert (HSI : SI (zfill brk (Z_to_bv 64 8192) M)) by si_fill HSI0. clear HSI0.
    (* [comment removed for export] *)
    pose proof (regs_set_a0 (ENVv vals) _ _ (Z_to_bv 64 (bv_unsigned brk + 8192)) (EAlu ALU_ADD bx (ELit 8192)) HR
                  ltac:(rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot bx ev ENV];
                        rewrite P70; reflexivity)) as HR1. clear HR.
    lazymatch type of HR1 with regs_ok _ ?sr _ => replace sr with srW0 in HR1 by (vm_compute; reflexivity) end.
    (* [comment removed for export] *)
    pose proof (xfer_zfill RSEGS (ENVv vals) M knD2 bx 0 brk 8192 HK
                  ltac:(unfold estart; cbn [a_base a_off edenot bx ev ENV]; rewrite P70; lia) ltac:(lia)
                  ltac:(pose proof (u64_range brk); lia)) as HK0. clear HK.
    pose proof (kderive_all_sound RSEGS (ENVv vals) _ _ knW0 HK0 ltac:(vm_compute; reflexivity)) as HK1. clear HK0.
    rename HR1 into HR. rename HK1 into HK.
    change (mkModelA fdsV (mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [] brk (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0)
                    stdin0 fs0 None (Some tid) None) with (modelV VMk).
    (* [comment removed for export] *)
    run_block_keep scr0 71%nat. si_block HSI R M.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    eapply (rz_mmap_fixed_noaccess04 RSEGS _ _ _ (modelV VMk) ECALLW brk 4096).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - (* [comment removed for export] *) rewrite mV_vmmaps. apply atop_sp0.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). cbn [edenot bx ev ENV]. exact P70.
    - exact Bal.
    - lia.
    - regv HR (11 : reg). reflexivity.
    - lia.
    - change (page_round_up_Z 4096) with 4096%Z. pose proof alloc_ceiling_range. lia.
    - regv HR (12 : reg). reflexivity.
    - regv HR (13 : reg). reflexivity.
    - regv HR (14 : reg). apply bv_eq. reflexivity.
    - regv HR (15 : reg). reflexivity.
    - (* #38: the ledger is [init_reserved] (segments ++ vDSO pair), not the segments alone *)
      rewrite mV_vmmaps. cbn [VMk vm_reserved]. try change (page_round_up_Z 4096) with 4096%Z.
      apply RES_low_free; [lia | rewrite ?u64_lit by lia; lia].
    - rewrite mV_vmmaps. cbn [VMk vm_maps]. change (page_round_up_Z 4096) with 4096%Z.
      apply map_contains_head; rewrite ?u64_lit by lia; lia.
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x21374 + 4)%Z with 0x21378%Z.
      change (page_round_up_Z 4096) with 4096%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc brk bx HR ltac:(cbn [edenot bx ev ENV]; exact P70)) as HR1 end.
      clear HR. rename HR1 into HR.
      lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
        pose proof (xfer_unfill RSEGS E Mc kn bx 0 brk 4096 HK
                      ltac:(unfold estart; cbn [a_base a_off edenot bx ev ENV]; rewrite P70; lia) ltac:(lia)
                      ltac:(pose proof (u64_range brk); lia)) as HK1 end.
      clear HK. rename HK1 into HK.
      lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knU in HK by (vm_compute; reflexivity) end.
      change (fixed_noaccess_model brk (Z_to_bv 64 4096) (modelV VMk)) with (modelV VMo).
      lazymatch type of HK with know_ok _ _ ?Mc _ => assert (HSI2 : SI Mc) by si_fill HSI end.
      clear HSI. rename HSI2 into HSI.
      guard_tail EXIT HL P0 P1 P2 P3 P4 P70 P5 VMo HSI R M. right. left. reflexivity.
  Qed.
End World.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End S7W65.

(* [comment removed for export] *)
Module S7W65m.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.MiniExec.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SimInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim.ExitSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ShapeLaws OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Nodes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim.AllocSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.FileSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.AgentLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ModelAmb.SpecConsts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.LibKnowFrame OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0LibStdioCall OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.LibWritev OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefNodes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0ExitBase OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0StdioDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Exit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Startup OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0MainEntry OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Hoare OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Frame OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MallocDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefEnframeArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0EnframeBase OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Enframe OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0ReadBase.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0W65x.S0PilotOOM_defs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0W65x.S0PilotOOM.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymXfer OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymAbove S7W65_defs S7W65.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit.   (* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_blockW" constr(scr) constr(NX) := run_block_gen FUEL STOPS_W scr NX false.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mprotect_len_val : forall (a : word),
  (bv_unsigned a mod 4096 = 0)%Z -> (bv_unsigned a + 12288 < 2 ^ 64)%Z ->
  alu64 ALU_ADD (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) a)
                   (alu64 ALU_AND (alu64 ALU_ADD a (Z_to_bv 64 12287)) (Z_to_bv 64 18446744073709547520)))
        (Z_to_bv 64 (-4096)) = Z_to_bv 64 4096.
Proof.
  intros a Hal Hb. pose proof (u64_range a) as Ha.
  apply bv_eq. cbn [alu64 alu mul_div].
  rewrite ?bv_add_unsigned, ?bv_and_unsigned, ?bv_mul_unsigned, ?bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  change ((-1) mod 2 ^ 64)%Z with (2 ^ 64 - 1)%Z.
  change (18446744073709547520 mod 2 ^ 64)%Z with (2 ^ 64 - 4096)%Z.
  change (12287 mod 2 ^ 64)%Z with 12287%Z. change (4096 mod 2 ^ 64)%Z with 4096%Z.
  rewrite (Z.mod_small (bv_unsigned a + 12287)) by lia.
  rewrite fld_hi by lia.
  destruct (proj1 (Z.mod_divide (bv_unsigned a) 4096 ltac:(lia)) Hal) as [q Hq].
  replace ((bv_unsigned a + 12287) / 4096)%Z with (q + 2)%Z by (rewrite Hq; lia).
  nia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* the noaccess grant is now Linux's placement, and the four facts come
   from it ([Placement.linux_place_is_admissible]) *)
Lemma grant_ok_na_unpack : forall hint m a n,
  (0 < n)%Z -> (n mod page_size = 0)%Z ->
  grant_ok_na hint m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
  (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
  intros hint m a n Hn Hnal H.
  exact (Placement.linux_place_is_admissible _ _ _ _ _ Hn Hnal H).
Qed.

Section World.
  Context {ACEIL__ : ACeil} {RUNW__ : RunW}.   (* [comment removed for export] *)
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable hw : word.    (* [comment removed for export] *)
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_launch (mkProcInputA [a0s; path] envv fs0 stdin0) hw mbase sp0 brk rnd tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hceil : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma atop_sp0 : forall r m na sb b l mb, atop_ok (mkVmMapsFull r m na sb b l mb sp0).
  Proof. intros. unfold atop_ok, alloc_top. cbn [vm_init_sp]. rewrite Hceil. unfold stack_max_size. lia. Qed.
  (* the launch's own record ([main_launch]'s third part) *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rnd) (mkProcInputA [a0s; path] envv fs0 stdin0).
  (* the launch's mmap base is in the covered band ([Run.valid_mmap_base]) *)
  Lemma mbase_ok : valid_mmap_base mbase.
  Proof.
    pose proof Hlau as Hl. cbn [entry_launch_ok_va] in Hl. destruct Hl as (_ & _ & Hb).
    exact (MmapBase.valid_launch_base_sv48_in_band _ _ Hb).
  Qed.
  Lemma mbase_lo : (mmap_base_min <= bv_unsigned mbase)%Z.
  Proof. exact (proj1 mbase_ok). Qed.
  Lemma mbase_al : (bv_unsigned mbase mod page_size = 0)%Z.
  Proof. exact (proj2 (proj2 mbase_ok)). Qed.
  Lemma sp0_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Proof. exact (proj1 Hvsp). Qed.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpnd : openat_plain_name path = true.   (* [comment removed for export] *)
  Hypothesis Hplen : (length path <= 4095)%nat.
  Variable fd3 : FdEntry.
  Variable SI : (word -> option byte) -> Prop.
  Hypothesis SI_step : forall M M' : word -> option byte,
    (forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M' a = M a) -> SI M -> SI M'.

  #[local] Notation ENVv := (ENV a0s path hw rnd).
  (* [comment removed for export] *)
  (* the run's reserved ledger ([State.init_reserved]) *)
  #[local] Notation RES := (init_reserved (segments_reserved RSEGS) mbase sp0 (ia_kernel stdin0)).
  Lemma RES_shape : Forall small_ent RES /\ (length RES <= 6)%nat.
  Proof.
    destruct (init_reserved_shape _ mbase sp0 (ia_kernel stdin0) mbase_lo sp0_lo S0PilotOOM.segres_small) as [A B].
    rewrite S0PilotOOM.segres_len in B. split; [exact A| lia].
  Qed.
  Lemma RES_seg_in : forall e l, In e (segments_reserved RSEGS) -> In e (RES ++ l).
  Proof. intros e l He. apply in_or_app. left. apply S0PilotOOM.RESX_seg_in. exact He. Qed.

  #[local] Notation modelV := (modelV tid fs0 stdin0 fd3).
  #[local] Notation model1V := (model1V sp0 tid brk mbase fs0 stdin0 fd3).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac si_block HSI Rn Mn :=
    lazymatch goal with
    | EQM : ?M' = mem_denot ?E ?Mo ?log, HK : know_ok ?segs ?E ?M' ?kn, HR : regs_ok ?E _ ?R' |- _ =>
        let H := fresh "HSI" in
        assert (H : SI M');
        [ apply (SI_step Mo M'); [| exact HSI]; intros xa Hxa; rewrite EQM;
          apply (mem_denot_above_kb segs E M' Mo kn log 0%nat 0x5c000 0x7fff7f800000 xa HK);
          [ vm_compute; reflexivity | lia | cbn [ev ENV]; pins; lia | cbn [ev ENV]; pins; lia | lia | lia ]
        | clear HSI EQM; try clear Mn; rename H into HSI; try rename M' into Mn; try clear Rn; try rename R' into Rn ]
    end.
  Ltac si_fill HSI :=
    lazymatch goal with
    | |- SI (zfill ?a ?n ?M) => apply (SI_step M); [| exact HSI]; intros xa Hxa; apply zfill_out; rewrite ?u64_lit by lia; lia
    | |- SI (unfill ?a ?n ?M) => apply (SI_step M); [| exact HSI]; intros xa Hxa; apply unfill_outside; rewrite ?u64_lit by lia; lia
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable K : TSet.

  (* [comment removed for export] *)
  Definition exitT_branch : Prop :=
    forall vals R M VM,
      length vals = 105%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 -> vals_ev vals 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 ->
      vals_ev vals 70 = brk -> vals_ev vals 5 = tid ->
      regs_ok (ENVv vals) srZm R -> know_ok RSEGS (ENVv vals) M knZm ->
      vm_pre VM (vals_ev vals 71) (vals_ev vals 72) -> w65_vm sp0 mbase stdin0 VM (vals_ev vals 71) (vals_ev vals 72) ->
      VM = mkVmMapsFull RES [(vals_ev vals 72, Z_to_bv 64 69632); (vals_ev vals 71, Z_to_bv 64 8192)] [(vals_ev vals 71, Z_to_bv 64 4096)] brk brk LIM mbase sp0 -> SI M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1359c) M (seg_rom RSEGS)) (modelV VM)) K.

  Lemma w65_T : forall vals R M VM,
    exitT_branch ->
    length vals = 73%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 -> vals_ev vals 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 ->
    vals_ev vals 70 = brk -> vals_ev vals 5 = tid ->
    regs_ok (ENVv vals) srT0 R -> know_ok RSEGS (ENVv vals) M knT0 ->
    vm_pre VM (vals_ev vals 71) (vals_ev vals 72) -> w65_vm sp0 mbase stdin0 VM (vals_ev vals 71) (vals_ev vals 72) ->
      VM = mkVmMapsFull RES [(vals_ev vals 72, Z_to_bv 64 69632); (vals_ev vals 71, Z_to_bv 64 8192)] [(vals_ev vals 71, Z_to_bv 64 4096)] brk brk LIM mbase sp0 -> SI M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x21378) M (seg_rom RSEGS)) (modelV VM)) K.
  Proof.
    intros vals R M VM EXIT HL P0 P2 P3 P4 P70 P5 HR HK HVM HVS HVX HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ knT0 ltac:(let i := kidx knT0 (is_krange gx) in exact i) _ HK eq_refl)
      as Kgm; cbn [kentry_ok edenot ev ENV] in Kgm.
    pose proof (know_nth RSEGS _ _ knT0 ltac:(let i := kidx knT0 (is_kalign gx) in exact i) _ HK eq_refl)
      as Kga; cbn [kentry_ok edenot ev ENV] in Kga.
    pose proof (know_nth RSEGS _ _ knT0 ltac:(let i := kidx knT0 (is_krange ax) in exact i) _ HK eq_refl)
      as Kar; cbn [kentry_ok edenot ev ENV] in Kar.
    pose proof (know_nth RSEGS _ _ knT0 ltac:(let i := kidx knT0 (is_kdisj ax gx) in exact i) _ HK eq_refl)
      as Kgd; cbn [kentry_ok] in Kgd; unfold estart in Kgd; cbn [a_base a_off edenot ax gx ev ENV] in Kgd.
    set (gm := vals_ev vals 72) in *. set (av := vals_ev vals 71) in *.
    (* [comment removed for export] *)
    run_block_keep scrG 73%nat.
    { unfold sc_denot. cbn [edenot ev ENV]. apply bt_ne_not. subst gm. lia. }
    si_block HSI R M.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?MG ?kn =>
      krdv HK 71%nat 4136%Z 8%nat Hmem; [apply flat_intro; cbn [edenot ev ENV]; fold av; lia|];
      krdv HK 71%nat 4152%Z 8%nat Hmw; [apply flat_intro; cbn [edenot ev ENV]; fold av; lia|];
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kzero_cov gx 9 8) in exact i) _ HK eq_refl) as Kz;
      cbn [kentry_ok] in Kz; unfold elenZ, estart in Kz; cbn [a_base a_off edenot ev ENV] in Kz;
      pose proof (kwr_store_ok RSEGS E _ kn ltac:(let i := kidx kn (is_kwr_cov gx 13 69615) in exact i)
                    _ _ _ 13 (Z.to_nat 69615) HK eq_refl ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as Hok;
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kimg_cov 69328 96) in exact i) _ HK eq_refl) as Kimg;
      cbn [kentry_ok] in Kimg
    end.
    fold gm in Kz, Hmem, Hmw, Hok.
    unfold adenot, v_addi in Hmem, Hmw, Hok. cbn [a_base a_off edenot ev ENV] in Hmem, Hmw, Hok.
    fold av in Hmem, Hmw. fold gm in Hok.
    change (bv_unsigned (Z_to_bv 64 69623)) with 69623%Z in Kz.
    assert (EF : efH M (Z_to_bv 64 1) (bv_unsigned av + 4120) (bv_unsigned gm) 72480 0 65536 0 0 69616
                     (bv_unsigned gm + 16) 1).
    { constructor.
      - vm_compute. reflexivity.
      - unfold slot_start, UNIT. lia.
      - vm_compute. reflexivity.
      - pose proof (u64_range av). lia.
      - pose proof (u64_range gm). lia.
      - lia.
      - lia.
      - lia.
      - intros _. vm_compute. reflexivity.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - replace (bv_unsigned av + 4120 + 16)%Z with (bv_unsigned av + 4136)%Z by lia.
        rewrite Hmem. subst gm. rewrite Z_to_bv_bv_unsigned. reflexivity.
      - replace (bv_unsigned av + 4120 + 32)%Z with (bv_unsigned av + 4152)%Z by lia. exact Hmw.
      - replace (bv_unsigned gm + 16 - 4)%Z with (bv_unsigned gm + 9 + 3)%Z by lia. apply (proj2 Kz). lia.
      - replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 9 + 4)%Z by lia. apply (proj2 Kz). lia.
      - intros C. exfalso. apply C. reflexivity.
      - replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 13)%Z by lia.
        replace (Z.to_nat (69616 - 1)) with (Z.to_nat 69615) by reflexivity. exact Hok.
      - intros j Hj. unfold SCT. apply (proj2 (proj2 Kimg)). lia. }
    assert (RT : Hoare.ret_ok (Z_to_bv 64 0x1359c)) by (apply bv_eq; vm_compute; reflexivity).
    assert (G1 : getr R 1 = Z_to_bv 64 0x1359c) by (regv HR (1:reg); reflexivity).
    assert (G10 : getr R 10 = Z_to_bv 64 (bv_unsigned av + 4120)).
    { regv HR (10:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
      reflexivity. }
    assert (G11 : getr R 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity).
    assert (G12 : getr R 12 = Z_to_bv 64 65536) by (regv HR (12:reg); reflexivity).
    assert (G13 : getr R 13 = Z_to_bv 64 1) by (regv HR (13:reg); reflexivity).
    cps_destruct (enframe_run M (Z_to_bv 64 1) _ _ _ _ _ _ _ _ _ _ EF R (seg_rom RSEGS) (Z_to_bv 64 0x1359c)
                G1 RT G10 G11 G12 G13) as (R2 & Hms & Hkeep & HA0).
    clear RT G1 G10 G11 G12 G13.
    replace (Z_to_bv 64 135140) with (0x20fe4 : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
    (* [comment removed for export] *)
    replace (memF M 0 65536 69616 (bv_unsigned gm + 16) 1) with (mem_denot (ENVv vals) M LOGE).
    2:{ unfold memF. cbv delta [mF mE mE1 mD] beta zeta.
        replace (69616 - 4 - 65536 - 16 * 1)%Z with 4060%Z by reflexivity.
        replace (69616 * 0 / 16 + 1)%Z with 1%Z by reflexivity.
        change (1 =? 0)%Z with false. change (4060 =? 0)%Z with false. change (4060 <? 5)%Z with false.
        cbv iota.
        replace (0 + 32 * res_code 4060)%Z with 160%Z by reflexivity.
        replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 13)%Z by lia.
        replace (bv_unsigned gm + 16 - 2)%Z with (bv_unsigned gm + 14)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 - 4)%Z with (bv_unsigned gm + 28)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 - 3)%Z with (bv_unsigned gm + 29)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 - 2)%Z with (bv_unsigned gm + 30)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 + 65536)%Z with (bv_unsigned gm + 65568)%Z by lia.
        replace (bv_unsigned gm + 16 + 69616 - 4 - 5)%Z with (bv_unsigned gm + 69623)%Z by lia.
        replace (bv_unsigned gm + 16 + 69616 - 4 - 4)%Z with (bv_unsigned gm + 69624)%Z by lia.
        unfold LOGE. cbn [mem_denot]. unfold adenot. cbn [a_base a_off edenot gx ev ENV]. fold gm. unfold v_addi.
        change (word_to_le_bytes 1 (Z_to_bv 64 160)) with [Z_to_bv 8 160].
        change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
        change (word_to_le_bytes 1 (Z_to_bv 64 224)) with [Z_to_bv 8 224].
        reflexivity. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?MG ?kn =>
      pose proof (carry_after RSEGS E MG LOGE kn [] knZm [] _ ltac:(vm_compute; reflexivity)
                    ltac:(cbn [log_flat LOGE]; unfold flat, estart; cbn [a_base a_off edenot gx ev ENV]; fold gm;
                          repeat split; lia)
                    HK ltac:(constructor)) as HK2
    end.
    assert (HSI2 : SI (mem_denot (ENVv vals) M LOGE)).
    { apply (SI_step M); [|exact HSI]. intros xa Hxa.
      apply (mem_denot_above_kb RSEGS (ENVv vals) _ M knZm LOGE 0%nat 0x5c000 0x7fff7f800000 xa HK2);
        [vm_compute; reflexivity | lia | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia | lia]. }
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok _ ?sr _ =>
      pose proof (regs_after_keeps vals _ sr R R2 callee_saved ltac:(rewrite HL; vm_compute; reflexivity)
                    HR Hkeep callee_saved_no0) as HR2 end.
    rewrite HL in HR2. clear HR.
    set (vals2 := vals ++ junk_vals R2) in *.
    assert (HL2 : length vals2 = 105%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals2 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (Q3 : vals_ev vals2 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P3).
    assert (Q4 : vals_ev vals2 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P4).
    assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
    assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
    assert (Q71 : vals_ev vals2 71 = av) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); reflexivity).
    assert (Q72 : vals_ev vals2 72 = gm) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); reflexivity).
    change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path hw rnd))) with (ENVv vals2) in HR2.
    pose proof (regs_ok_set_have (ENVv vals2) _ R2 10 _ (EAlu ALU_ADD gx (ELit 32)) HR2 HA0
                  ltac:(rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot gx ev ENV];
                        rewrite Q72; f_equal; lia) ltac:(discriminate)) as HR3.
    clear HR2.
    lazymatch type of HR3 with regs_ok _ ?sr _ => replace sr with srZm in HR3 by (vm_compute; reflexivity) end.
    lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
    clear HK2 HK.
    change (Env (vals_ev (vals ++ junk_vals R2)) (blobs_ev (blobs0 a0s path hw rnd))) with (ENVv vals2) in HK3.
    change (mem_denot (Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rnd))) M LOGE) with (mem_denot (ENVv vals) M LOGE) in HSI2.
    apply (EXIT vals2 R2 _ VM HL2 Q0 Q2 Q3 Q4 Q70 Q5 HR3 HK3);
      [rewrite Q71, Q72; exact HVM | rewrite Q71, Q72; exact HVS | rewrite Q71, Q72; exact HVX | exact HSI2].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition VMn (a : word) : VmMaps :=
    mkVmMapsFull RES [(a, Z_to_bv 64 8192)] [(a, Z_to_bv 64 8192)] brk brk LIM mbase sp0.
  Definition VMp (a : word) : VmMaps :=
    mkVmMapsFull RES [(a, Z_to_bv 64 8192)] [(a, Z_to_bv 64 4096)] brk brk LIM mbase sp0.
  Definition VMt (a gm : word) : VmMaps :=
    mkVmMapsFull RES [(gm, Z_to_bv 64 69632); (a, Z_to_bv 64 8192)] [(a, Z_to_bv 64 4096)] brk brk LIM mbase sp0.


  Lemma VMp_grant_exists : forall hint a, exists g, grant_ok hint (modelV (VMp a)) g (page_round_up_Z 69632) = true.
  Proof.
    intros hint a. change (page_round_up_Z 69632) with 69632%Z.
    apply grant_exists.
    - (* [comment removed for export] *) rewrite mV_vmmaps. apply atop_sp0.
    - lia.
    - (* the length is a whole number of pages *) reflexivity.
    - rewrite mV_vmmaps. cbn [VMp vm_reserved vm_limit vm_maps]. destruct RES_shape as [RS _].
      apply Forall_app. split.
      + eapply Forall_impl; [|exact RS]. unfold small_ent. cbn beta. intros p [[X1 X2] X3]. lia.
      + repeat constructor; cbn [snd]; rewrite ?u64_lit by lia; lia.
    - rewrite mV_vmmaps. cbn [VMp vm_reserved vm_limit vm_maps]. destruct RES_shape as [_ RL].
      rewrite length_app. cbn [length]. lia.
    - apply grant_budget_intro; [reflexivity | reflexivity |]. rewrite mV_vmmaps.
      unfold vm_live_bytes. cbn [VMp vm_maps vm_limit live_bytes]. rewrite ?u64_lit by lia. pose proof LIM_ge. lia.
  Qed.

  Lemma VMp_grant : forall hint a g, grant_ok hint (modelV (VMp a)) g 69632 = true ->
    (bv_unsigned g mod 4096 = 0 /\ 0x5c000 <= bv_unsigned g /\ bv_unsigned g + 69632 <= alloc_ceiling
     /\ (bv_unsigned a + 8192 <= bv_unsigned g \/ bv_unsigned g + 69632 <= bv_unsigned a))%Z
    /\ region_free RES g (Z_to_bv 64 69632) = true.
  Proof.
    intros hint a g Hg.
    cps_destruct (grant_ok_unpack _ _ _ _ Hg) as (Hal & Hpos & Hce & Hrf & Hlive).
    rewrite mV_vmmaps in Hrf. cbn [VMp vm_reserved vm_maps] in Hrf. rewrite mV_vmmaps in Hce.
    assert (Grf : region_free RES g (Z_to_bv 64 69632) = true)
      by (rewrite region_free_app_split in Hrf; apply andb_prop in Hrf; exact (proj1 Hrf)).
    apply (atop_ok_grant _ _ _ (atop_sp0 _ _ _ _ _ _ _)) in Hce. pose proof alloc_ceiling_range as Hcr.
    unfold page_size in Hal. pose proof (u64_range g) as Hgr. pose proof (u64_range a) as Har.
    assert (Hn : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by (apply u64_lit; lia).
    pose proof (region_free_In _ _ _ (Z_to_bv 64 65536) (Z_to_bv 64 12288) Hrf ltac:(apply RES_seg_in; rewrite S0PilotOOM.segres_eq; cbn [In]; tauto)) as D1.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 77824) (Z_to_bv 64 86016) Hrf ltac:(apply RES_seg_in; rewrite S0PilotOOM.segres_eq; cbn [In]; tauto)) as D2.   (* [comment removed for export] *)
    pose proof (region_free_In _ _ _ (Z_to_bv 64 167936) (Z_to_bv 64 208896) Hrf ltac:(apply RES_seg_in; rewrite S0PilotOOM.segres_eq; cbn [In]; tauto)) as D4.
    pose proof (region_free_In _ _ _ a (Z_to_bv 64 8192) Hrf ltac:(apply in_or_app; right; left; reflexivity)) as D5.
    rewrite Hn in D1, D2, D4, D5. rewrite !u64_lit in D1 by lia. rewrite !u64_lit in D2 by lia. rewrite !u64_lit in D4 by lia. rewrite !u64_lit in D5 by lia.
    assert (Hg4096 : (4096 <= bv_unsigned g)%Z).
    { destruct (proj1 (Z.mod_divide (bv_unsigned g) 4096 ltac:(lia)) Hal) as [q Hq]. lia. }
    split; [repeat split; lia| exact Grf].
  Qed.

  Lemma w65_R : forall vals R M,
    exitT_branch ->
    length vals = 72%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd -> vals_ev vals 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 -> vals_ev vals 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0 ->
    vals_ev vals 70 = brk -> vals_ev vals 5 = tid ->
    (0x1000 <= bv_unsigned (vals_ev vals 71))%Z -> (bv_unsigned (vals_ev vals 71) + 8192 <= alloc_ceiling)%Z ->
    region_free RES (vals_ev vals 71) (Z_to_bv 64 8192) = true ->
    regs_ok (ENVv vals) srR0 R -> know_ok RSEGS (ENVv vals) M knR0 -> SI M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x213d0) M (seg_rom RSEGS)) (modelV (VMp (vals_ev vals 71))))
               K.
  Proof.
    intros vals R M EXIT HL P0 P2 P3 P4 P70 P5 Alo Ahi Arf HR HK HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    set (av := vals_ev vals 71) in *.
    (* [comment removed for export] *)
    run_block_keep scr0 72%nat. si_block HSI R M.
    eapply (rz_mmap_anon04 RSEGS _ _ _ (modelV (VMp av)) ECALLW 69632).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (11 : reg). reflexivity.
    - lia.
    - regv HR (12 : reg). reflexivity.
    - regv HR (13 : reg). reflexivity.
    - regv HR (14 : reg). apply bv_eq. reflexivity.
    - regv HR (15 : reg). reflexivity.
    - (* LPS 727298f3 (#144/#146): the hint is this call's own a0, the literal NULL *)
      regv HR (10 : reg). apply place_declined_b_null.
    - apply VMp_grant_exists.
    - (* [comment removed for export] *)
      intros g Hg. rewrite v_addi_pc4 by lia. change (0x21374 + 4)%Z with 0x21378%Z.
      change (page_round_up_Z 69632) with 69632%Z in Hg |- *.
      cps_destruct (VMp_grant _ av g Hg) as ((Gal & Glo & Ghi & Gdj) & Grf).
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [g] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [g] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      clear HR HK.
      set (vals2 := vals ++ [g]) in *.
      assert (HL2 : length vals2 = 73%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (Q2 : vals_ev vals2 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
      assert (Q3 : vals_ev vals2 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P3).
      assert (Q4 : vals_ev vals2 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P4).
      assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
      assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
      assert (Q71 : vals_ev vals2 71 = av) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); reflexivity).
      assert (Q72 : vals_ev vals2 72 = g).
      { subst vals2. rewrite <- HL. rewrite <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
      clearbody vals2. clearbody av. clear HL P0 P2 P3 P4 P70 P5 vals. rename HL2 into HL.
      change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path hw rnd))) with (ENVv vals2) in HR2, HK2.
      pose proof (regs_set_a0 (ENVv vals2) _ _ g gx HR2 ltac:(cbn [edenot gx ev ENV]; exact Q72)) as HR. clear HR2.
      lazymatch type of HK2 with know_ok _ _ ?Mc _ =>
        assert (HK3 : know_ok RSEGS (ENVv vals2) Mc knT00) end.
      { pose proof alloc_ceiling_range as Hcr. auxv_above HK2 Q0.
        unfold knT00. apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|exact HK2]]]]]].
        - apply kalign_intro; [lia|]. cbn [edenot gx ev ENV]. rewrite Q72. exact Gal.
        - apply krange_intro. cbn [edenot gx ev ENV]. rewrite Q72. lia.
        - (* [comment removed for export] *) cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot gx ev ENV]. rewrite Q0, Q72. lia.
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot gx ev ENV]. rewrite Q72. lia.
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot gx ev ENV]. rewrite Q72. lia.
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ax gx ev ENV]. rewrite Q71, Q72. lia. }
      clear HK2.
      pose proof (xfer_zfill RSEGS (ENVv vals2) _ knT00 gx 0 g 69632 HK3
                    ltac:(unfold estart; cbn [a_base a_off edenot gx ev ENV]; rewrite Q72; lia)
                    ltac:(lia) ltac:(lia)) as HK.
      clear HK3.
      lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knT0 in HK by (vm_compute; reflexivity) end.
      apply (w65_T vals2 _ _ (VMt av g) EXIT HL Q0 Q2 Q3 Q4 Q70 Q5 HR HK).
      4:{ si_fill HSI. }
      3:{ rewrite Q71, Q72. reflexivity. }
      2:{ rewrite Q71, Q72. unfold w65_vm. cbn [vm_reserved vm_limit vm_maps VMt].
          split; [reflexivity|]. split; [reflexivity|]. left. split; [reflexivity | lia]. }
      rewrite Q71, Q72. pose proof (u64_range av).
      unfold vm_pre, mmap_model. rewrite ?with_vmmaps_vm, ?mV_vmmaps. cbn [VMt VMp vm_reserved vm_limit vm_maps vm_noaccess vm_start_brk vm_brk].
      assert (Hn : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by (apply u64_lit; lia).
      assert (H8 : bv_unsigned (Z_to_bv 64 8192) = 8192%Z) by (apply u64_lit; lia).
      split.
      { (* the ledger is the run's; both grants miss it *)
        apply (res_ok_init _ mbase sp0 (ia_kernel stdin0)); [exact mbase_lo | exact sp0_lo | exact S0PilotOOM.segres_small | reflexivity |].
        intros e He. cbn [vm_maps In] in He. destruct He as [<- | [<- | []]]; cbn [fst snd]; assumption. }
      split; [reflexivity|]. split; [apply map_has_head|].
      split.
      { constructor; [cbn [fst snd]; rewrite ?Hn; lia|]. constructor; [|constructor]. cbn [fst snd]. rewrite ?H8. lia. }
      split; [cbn; lia|].
      split; [cbn [live_bytes]; rewrite Hn, H8; lia|].
      split.
      { exists (av, Z_to_bv 64 8192). split; [cbn [In]; tauto|]. cbn [fst snd]. rewrite H8.
        split; [intros Eav; apply (f_equal bv_unsigned) in Eav; lia | lia]. }
      (* [comment removed for export] *)
      constructor; [|constructor; [constructor | constructor]].
      constructor; [|constructor]. unfold S0TargetPre.iv_disjoint. cbn [fst snd]. rewrite Hn, H8. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem mmap_ok_worldV : exitT_branch ->
    mmap_ok_entry sp0 a0s path envv hw rnd tid brk mbase fs0 stdin0 fd3 SI K.
  Proof.
    intros EXIT vals R M hint a HL P0 P70 P1 P2 P3 P4 P5 HR HK HSI0 Hg.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    (* [comment removed for export] *)
    cps_destruct (grant_ok_na_unpack _ _ _ 8192 ltac:(lia) ltac:(reflexivity) Hg) as (Hal & Hpos & Hce & Hrf).
    unfold S7W65.model1V in Hrf, Hce. rewrite m_vmmaps_mkModelA in Hrf, Hce. cbn [vm_reserved vm_maps] in Hrf.
    rewrite app_nil_r in Hrf.
    (* the grant misses the whole ledger, the vDSO pair included *)
    assert (HrfR : region_free RES a (Z_to_bv 64 8192) = true) by exact Hrf.
    assert (HrfV : region_free (vdso_reserved (ia_kernel stdin0)
                     (page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp0 - stack_max_size)))) a (Z_to_bv 64 8192) = true).
    { pose proof HrfR as X. unfold init_reserved in X. rewrite region_free_app_split in X.
      apply andb_prop in X. exact (proj2 X). }
    apply (atop_ok_grant _ _ _ (atop_sp0 _ _ _ _ _ _ _)) in Hce. pose proof alloc_ceiling_range as Hcr.
    unfold page_size in Hal. pose proof (u64_range a) as Har.
    change (page_round_up_Z 8192) with 8192%Z in Hce, Hrf.
    assert (H8 : bv_unsigned (Z_to_bv 64 8192) = 8192%Z) by (apply u64_lit; lia).
    pose proof (region_free_In _ _ _ (Z_to_bv 64 65536) (Z_to_bv 64 12288) Hrf ltac:(apply S0PilotOOM.RESX_seg_in; rewrite S0PilotOOM.segres_eq; cbn [In]; tauto)) as D1.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 77824) (Z_to_bv 64 86016) Hrf ltac:(apply S0PilotOOM.RESX_seg_in; rewrite S0PilotOOM.segres_eq; cbn [In]; tauto)) as D2.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 163840) (Z_to_bv 64 4096) Hrf ltac:(apply S0PilotOOM.RESX_seg_in; rewrite S0PilotOOM.segres_eq; cbn [In]; tauto)) as D3.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 167936) (Z_to_bv 64 208896) Hrf ltac:(apply S0PilotOOM.RESX_seg_in; rewrite S0PilotOOM.segres_eq; cbn [In]; tauto)) as D4.
    rewrite H8 in D1, D2, D3, D4.
    rewrite !u64_lit in D1 by lia. rewrite !u64_lit in D2 by lia. rewrite !u64_lit in D3 by lia. rewrite !u64_lit in D4 by lia.
    assert (Ha4096 : (4096 <= bv_unsigned a)%Z).
    { destruct (proj1 (Z.mod_divide (bv_unsigned a) 4096 ltac:(lia)) Hal) as [q Hq]. lia. }
    assert (Aimg : (bv_unsigned a + 8192 <= 0x10000 \/ 0x5c000 <= bv_unsigned a)%Z) by lia.
    clear D1 D2 D3 D4 Hrf.
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
      pose proof (env_app_regs vals [a] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
    lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
      pose proof (env_app_know RSEGS vals [a] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
    clear HR HK.
    set (vals2 := vals ++ [a]) in *.
    assert (HL2 : length vals2 = 72%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
    assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals2 2 = p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (Q3 : vals_ev vals2 3 = auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P3).
    assert (Q4 : vals_ev vals2 4 = rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P4).
    assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
    assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
    assert (Q71 : vals_ev vals2 71 = a).
    { subst vals2. rewrite <- HL. rewrite <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
    clearbody vals2. clear HL P0 P2 P3 P4 P70 P1 P5 vals. rename HL2 into HL.
    change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path hw rnd))) with (ENVv vals2) in HR2, HK2.
    pose proof (regs_set_a0 (ENVv vals2) _ _ a ax HR2 ltac:(cbn [edenot ax ev ENV]; exact Q71)) as HR. clear HR2.
    lazymatch type of HR with regs_ok _ ?sr _ => replace sr with srP0 in HR by (vm_compute; reflexivity) end.
    lazymatch type of HK2 with know_ok _ _ ?Mc _ =>
      assert (HK3 : know_ok RSEGS (ENVv vals2) Mc knP00) end.
    { auxv_above HK2 Q0.
      unfold knP00. apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|exact HK2]]]]]].
      - apply kalign_intro; [lia|]. cbn [edenot ax ev ENV]. rewrite Q71. exact Hal.
      - apply krange_intro. cbn [edenot ax ev ENV]. rewrite Q71. lia.
      - (* [comment removed for export] *) cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ax ev ENV]. rewrite Q0, Q71. lia.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ax ev ENV]. rewrite Q71. lia.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ax ev ENV]. rewrite Q71. lia.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ax ev ENV]. rewrite Q71.
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia. }
    clear HK2.
    pose proof (xfer_unfill RSEGS (ENVv vals2) _ knP00 ax 0 a 8192 HK3
                  ltac:(unfold estart; cbn [a_base a_off edenot ax ev ENV]; rewrite Q71; lia) ltac:(lia) ltac:(lia)) as HK.
    clear HK3.
    lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knP0 in HK by (vm_compute; reflexivity) end.
    change (page_round_up_Z 8192) with 8192%Z.
    change (noaccess_model a (Z_to_bv 64 8192) model1V) with (modelV (VMn a)).
    assert (HSI : SI (unfill a (Z_to_bv 64 8192) M)) by si_fill HSI0. clear HSI0.
    (* [comment removed for export] *)
    run_block_keep scrP 72%nat.
    { unfold sc_denot. cbn [edenot ax ev ENV]. rewrite Q71. apply bt_ne_not. lia. }
    si_block HSI R M.
    (* [comment removed for export] *)
    eapply (rz_mprotect04 RSEGS _ _ _ (modelV (VMn a)) ECALLW (Z_to_bv 64 (bv_unsigned a + 4096)) 4096).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ax ev ENV].
      rewrite Q71. reflexivity.
    - unfold page_size. rewrite u64_lit by lia.
      replace (bv_unsigned a + 4096)%Z with (bv_unsigned a + 1 * 4096)%Z by lia. rewrite Z.mod_add by lia. exact Hal.
    - regv HR (11 : reg). cbn [edenot ax ev ENV]. rewrite Q71. apply mprotect_len_val; lia.
    - lia.
    - change (page_round_up_Z 4096) with 4096%Z. unfold two_pow_64. rewrite u64_lit by lia. lia.
    - regv HR (12 : reg). reflexivity.
    - (* the protected half lies in the grant, which misses the vDSO pair *)
      change (m_kernel (modelV (VMn a))) with (ia_kernel stdin0). rewrite mV_vmmaps.
      rewrite (vdso_top_launch (VMn a) mbase_al). cbn [VMn vm_mmap_base vm_init_sp].
      change (page_round_up_Z 4096) with 4096%Z.
      apply (region_free_within _ a (Z_to_bv 64 8192)); [exact HrfV | rewrite ?u64_lit by lia; lia | rewrite ?u64_lit by lia; lia].
    - rewrite mV_vmmaps. cbn [VMn vm_noaccess]. change (page_round_up_Z 4096) with 4096%Z.
      apply map_contains_head; rewrite ?u64_lit by lia; lia.
    - rewrite mV_vmmaps. cbn [VMn vm_maps]. change (page_round_up_Z 4096) with 4096%Z.
      apply map_contains_head; rewrite ?u64_lit by lia; lia.
    - (* [comment removed for export] *)
      apply mprotect_budget_ok_intro; [reflexivity | reflexivity |]. rewrite mV_vmmaps.
      unfold vm_live_bytes. cbn [VMn vm_maps vm_limit live_bytes]. rewrite H8. pose proof LIM_ge. lia.
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x213cc + 4)%Z with 0x213d0%Z.
      change (page_round_up_Z 4096) with 4096%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
      clear HR. rename HR2 into HR.
      lazymatch type of HR with regs_ok _ ?sr _ => replace sr with srR0 in HR by (vm_compute; reflexivity) end.
      lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
        pose proof (xfer_zfill RSEGS E Mc kn ax 4096 (Z_to_bv 64 (bv_unsigned a + 4096)) 4096 HK
                      ltac:(unfold estart; cbn [a_base a_off edenot ax ev ENV]; rewrite Q71, u64_lit by lia; lia)
                      ltac:(lia) ltac:(rewrite u64_lit by lia; lia)) as HK2 end.
      clear HK. rename HK2 into HK.
      lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knR0 in HK by (vm_compute; reflexivity) end.
      (* [comment removed for export] *)
      unfold mprotect_model. rewrite mV_vmmaps.
      cbn [VMn vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit].
      rewrite maps_subtract_cons, maps_subtract_nil, app_nil_r.
      rewrite !u64_lit by lia.
      rewrite iv_subtract_suffix by (rewrite ?u64_lit, ?H8 by lia; lia).
      replace (bv_unsigned a + 4096 - bv_unsigned a)%Z with 4096%Z by lia.
      change (with_vmmaps (mkVmMapsFull RES [(a, Z_to_bv 64 8192)] [(a, Z_to_bv 64 4096)] brk brk LIM mbase sp0) (modelV (VMn a)))
        with (modelV (VMp a)).
      rewrite <- Q71.
      lazymatch type of HK with know_ok _ _ ?Mc _ => assert (HSI2 : SI Mc) by si_fill HSI end.
      apply (w65_R vals2 _ _ EXIT HL Q0 Q2 Q3 Q4 Q70 Q5); rewrite ?Q71; [lia | lia | exact HrfR | exact HR | exact HK | exact HSI2].
  Qed.
End World.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End S7W65m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.MiniExec.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SimInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim.ExitSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Nodes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim.AllocSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.FileSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.AgentLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.LibWritev OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefNodes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0ExitBase OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Exit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefLayout OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Startup OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0MainEntry OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Hoare OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Frame OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MallocDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0EnframeBase OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0Enframe OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0ReadBase OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0World OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0TargetPre OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0TargetPre.S0WorldVM.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0W65x.S0PilotOOM_defs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0W65x.S0PilotOOM.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymXfer OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymAbove S7W65_defs S7W65 S7W65m.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit.   (* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition off_image (x : Z) : Prop := (x + 1 <= 0x10000 \/ 0x5c000 <= x)%Z.

Lemma find_segment_skip : forall seg rest a n,
  (0 < n)%Z ->
  (a < Z.of_N (seg_base seg) \/ Z.of_N (seg_base seg) + Z.of_N (seg_size seg) < a + n)%Z ->
  find_segment (seg :: rest) a n = find_segment rest a n.
Proof.
  intros seg rest a n Hn H. cbn [find_segment].
  destruct (Z.leb_spec (Z.of_N (seg_base seg)) a); destruct (Z.leb_spec (a + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)));
    cbn [andb]; try reflexivity. lia.
Qed.

Lemma find_segment_off : forall a n, (0 < n)%Z -> (a + n <= 0x10000 \/ 0x5c000 <= a)%Z ->
  find_segment RSEGS a n = None.
Proof.
  intros a n Hn H. unfold Plain.M.loaded_segments, Plain_loaded_segments.
  rewrite 4 find_segment_skip; [reflexivity | exact Hn | | exact Hn | | exact Hn | | exact Hn |];
    cbn [seg_base seg_size Plain_segment_000 Plain_segment_001 Plain_segment_002 Plain_segment_003]; lia.
Qed.

Lemma seg_rom_off : forall x : word, off_image (bv_unsigned x) -> seg_rom RSEGS x = None.
Proof.
  intros x Hx. unfold seg_rom, memory_read. rewrite find_segment_off; [reflexivity | cbn; lia | unfold off_image in Hx; cbn; lia].
Qed.

Lemma wview_off : forall M (x : word), off_image (bv_unsigned x) -> wview RSEGS M x = M x.
Proof.
  intros M x Hx. unfold wview. destruct (M x); [reflexivity|].
  rewrite find_segment_off; [reflexivity | lia | unfold off_image in Hx; lia].
Qed.

Lemma rdn1_off : forall M (x : word) b, off_image (bv_unsigned x) ->
  rdn RSEGS M x 1 = Some [b] -> M x = Some b.
Proof.
  intros M x b Hx H. cbn [rdn] in H. rewrite (seg_rom_off x Hx) in H.
  destruct (M x) as [b0|]; [|discriminate]. injection H as ->. reflexivity.
Qed.

Lemma store_ok1_off : forall M (x : word), off_image (bv_unsigned x) ->
  store_ok RSEGS M x 1 = true -> M x <> None.
Proof.
  intros M x Hx H. cbn [store_ok] in H. rewrite (wview_off M x Hx) in H.
  destruct (M x); [discriminate | discriminate].
Qed.

Lemma u64_lit' : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

Lemma u0 : bv_unsigned (Z_to_bv 64 0) = 0%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cell_intro : forall M (x : word) n (v : word) (a z : Z),
  rdn RSEGS M x n = Some (word_to_le_bytes n v) ->
  x = Z_to_bv 64 a -> v = Z_to_bv 64 z -> cell M a n z.
Proof. intros M x n v a z H -> ->. exact H. Qed.

Lemma zero_bytes_intro : forall E M b k n a,
  kentry_ok RSEGS E M (KZero (SA b k) (ELit n)) -> (0 <= n < 2 ^ 64)%Z ->
  (bv_unsigned (edenot E b) + k)%Z = a -> zero_bytes M a n.
Proof.
  intros E M b k n a [Hf Hz] Hn Ha i Hi. unfold estart, elenZ in Hz. cbn [a_base a_off edenot] in Hz.
  rewrite u64_lit' in Hz by lia. rewrite <- Ha. apply Hz. lia.
Qed.

Lemma def_intro : forall E M b kk len a n,
  kentry_ok RSEGS E M (KWr (SA b kk) len) ->
  (bv_unsigned (edenot E b) + kk <= a)%Z -> (a + n <= bv_unsigned (edenot E b) + kk + len)%Z ->
  (a + n <= 0x10000 \/ 0x5c000 <= a)%Z -> (0 <= a)%Z -> (a + n <= 2 ^ 64)%Z ->
  forall i, (0 <= i < n)%Z -> M (Z_to_bv 64 (a + i)) <> None.
Proof.
  intros E M b kk len a n [Hf Hst] H1 H2 Hoff H0 H64 i Hi.
  unfold estart in Hst. cbn [a_base a_off] in Hst.
  specialize (Hst (a + i - (bv_unsigned (edenot E b) + kk))%Z 1%nat ltac:(lia) ltac:(cbn; lia)).
  replace (bv_unsigned (edenot E b) + kk + (a + i - (bv_unsigned (edenot E b) + kk)))%Z with (a + i)%Z in Hst by lia.
  refine (store_ok1_off M _ _ Hst). unfold off_image; rewrite u64_lit' by lia; lia.
Qed.

Lemma byte_intro : forall M a v,
  cell M a 1 v -> word_to_le_bytes 1 (Z_to_bv 64 v) = [Z_to_bv 8 v] ->
  (0 <= a)%Z -> (a + 1 <= 2 ^ 64)%Z -> (a + 1 <= 0x10000 \/ 0x5c000 <= a)%Z ->
  M (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof.
  intros M a v Hc Hw H0 H64 Hoff. unfold cell in Hc. rewrite Hw in Hc.
  apply rdn1_off; [unfold off_image; rewrite u64_lit' by lia; lia | exact Hc].
Qed.

Lemma img_clear_of_know : forall E M ivs,
  know_ok RSEGS E M (map (fun iv => KImg (fst iv) (snd iv)) ivs) ->
  Forall (fun iv => img_clear M (fst iv) (snd iv)) ivs.
Proof.
  intros E M ivs HK. unfold know_ok in HK. rewrite Forall_map in HK.
  eapply Forall_impl; [|exact HK]. (intros [lo hi]; cps_intros (A & B & C)). exact C.
Qed.

(* [comment removed for export] *)
Lemma errno_some : forall M, exists bs,
  rdn RSEGS M (Z_to_bv 64 0x3a63c) 4 = Some bs /\ length bs = 4%nat.
Proof.
  intros M. cbn [rdn].
  repeat match goal with
  | |- context [match M ?x with _ => _ end] =>
      destruct (M x); [| let r := eval vm_compute in (seg_rom RSEGS x) in change (seg_rom RSEGS x) with r]
  end; eexists; split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma blob2_secret : forall a0s path hw rnd, blob_val false (blobs_ev (blobs0 a0s path hw rnd) 2) 8 8 = secret_word rnd.
Proof.
  intros. unfold blob_val, blob_bytes. cbn [blobs_ev blobs0 nth]. change (Z.to_nat 8) with 8%nat.
  rewrite <- rnd_bytes_eq. apply secret_word_of_Z.
Qed.
Lemma blob3_canary : forall a0s path hw rnd, blob_val false (blobs_ev (blobs0 a0s path hw rnd) 3) 0 8 = canary_w rnd.
Proof.
  intros. unfold blob_val, blob_bytes. cbn [blobs_ev blobs0 nth]. change (Z.to_nat 0) with 0%nat. rewrite skipn_O.
  rewrite firstn_all2 by (rewrite length_canary_bytes; lia). rewrite canary_ok. apply Z_to_bv_bv_unsigned.
Qed.
Lemma blob4_hw : forall a0s path hw rnd, blob_val false (blobs_ev (blobs0 a0s path hw rnd) 4) 0 8 = hw.
Proof.
  intros. unfold blob_val, blob_bytes. cbn [blobs_ev blobs0 nth]. change (Z.to_nat 0) with 0%nat. rewrite skipn_O.
  rewrite firstn_all2 by (rewrite length_N_to_le_bytes; lia).
  rewrite bytes_le_N. change (8 * Z.of_nat 8)%Z with 64%Z.
  pose proof (u64_range hw). rewrite Z.mod_small by lia. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac addr_split a :=
  lazymatch a with
  | bv_unsigned ?x =>
      lazymatch x with
      | vals_ev _ ?i => constr:((EVar i, 0%Z))
      | _ => lazymatch goal with P : vals_ev _ ?i = x |- _ => constr:((EVar i, 0%Z)) end
      end
  | (?y + ?c)%Z =>
      lazymatch y with
      | context [bv_unsigned _] =>
          lazymatch addr_split y with (?b, ?k) => let k' := eval vm_compute in (k + c)%Z in constr:((b, k')) end
      | _ => let a' := eval vm_compute in a in constr:((ELit 0, a'))
      end
  | (?y - ?c)%Z =>
      lazymatch y with
      | context [bv_unsigned _] =>
          lazymatch addr_split y with (?b, ?k) => let k' := eval vm_compute in (k - c)%Z in constr:((b, k')) end
      | _ => let a' := eval vm_compute in a in constr:((ELit 0, a'))
      end
  | _ => let a' := eval vm_compute in a in constr:((ELit 0, a'))
  end.

(* [comment removed for export] *)
Ltac kside :=
  rewrite ?edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev eb ENV ENVr gx bx ax]; rewrite ?u0; pins;
  rewrite ?ext_val_zx_id by (cbn; lia);
  (* [comment removed for export] *)
  rewrite ?blob3_canary, ?blob2_secret, ?blob4_hw;
  try match goal with H : run_guard = _ |- _ => rewrite H end;
  try match goal with H : run_secret = _ |- _ => rewrite H end;
  first [ reflexivity
        | symmetry; apply Z_to_bv_bv_unsigned
        | rewrite Z_to_bv_bv_unsigned; (reflexivity || assumption || (symmetry; assumption))
        | f_equal; lia
        | lia ].

(* [comment removed for export] *)
Ltac kcell HK :=
  lazymatch goal with |- cell ?M ?a ?n ?z =>
  lazymatch type of HK with know_ok ?segs ?E M ?kn =>
  lazymatch addr_split a with (?b, ?k) =>
    let r := eval vm_compute in (kread segs kn b k n) in
    lazymatch r with
    | Some ?v =>
        apply (cell_intro M (adenot E (SA b k)) n (edenot E v) a z);
        [ apply (kread_rdn segs E M kn b k n v HK); [vm_compute; reflexivity | cbn; lia | cbn; lia
          | apply flat_intro; cbn [edenot ev ENV ENVr gx bx ax]; rewrite ?u0; pins; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ]
        | kside
        | kside ]
    | None => fail "kcell: knowledge does not determine" b k n
    end end end end.

(* [comment removed for export] *)
Ltac krdn HK :=
  lazymatch goal with |- rdn _ ?M (Z_to_bv 64 ?a) ?n = Some (word_to_le_bytes _ (Z_to_bv 64 ?z)) =>
    change (cell M a n z); kcell HK end.

(* [comment removed for export] *)
Ltac kzero HK :=
  lazymatch goal with |- zero_bytes ?M ?a ?n =>
  lazymatch type of HK with know_ok ?segs ?E M ?kn =>
  lazymatch addr_split a with (?b, ?k) =>
    let n' := eval vm_compute in n in
    apply (zero_bytes_intro E M b k n' a);
    [ apply (kderive_sound segs E M kn (KZero (SA b k) (ELit n')) HK); vm_compute; reflexivity
    | lia
    | cbn [edenot ev ENV ENVr gx bx ax]; rewrite ?u0; pins; lia ]
  end end end.

(* [comment removed for export] *)
Ltac kbyte HK :=
  lazymatch goal with |- ?M (Z_to_bv 64 ?a) = Some (Z_to_bv 8 ?v) =>
    apply (byte_intro M a v); [kcell HK | reflexivity | pins; lia | pins; lia | pins; lia] end.

(* [comment removed for export] *)
Ltac kdef HK b kk len :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
    apply (def_intro E M b kk len);
    [ apply (kderive_sound segs E M kn (KWr (SA b kk) len) HK); vm_compute; reflexivity
    | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia
    | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia
    | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia
    | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia
    | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia ]
  end.

(* [comment removed for export] *)
Definition is_kdisj_at (b1 : expr) (o1 : Z) (b2 : expr) (K : kentry) : bool :=
  match K with
  | KDisj (SA c1 k1) _ (SA c2 _) _ => expr_eqb b1 c1 && Z.eqb k1 o1 && expr_eqb b2 c2
  | _ => false
  end.

(* [comment removed for export] *)
Ltac kauxv HK kn P0 P3 P4 AUXC :=
  let Xa := fresh "Xa" in let Xr := fresh "Xr" in let Da := fresh "Da" in let Dr := fresh "Dr" in
  pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_krange (EVar 3)) in exact i) _ HK eq_refl) as Xa;
  cbn [kentry_ok edenot ev ENV ENVr] in Xa;
  pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_krange (EVar 4)) in exact i) _ HK eq_refl) as Xr;
  cbn [kentry_ok edenot ev ENV ENVr] in Xr;
  pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kdisj_at (EVar 0) (-4294967296) (EVar 3)) in exact i) _ HK eq_refl) as Da;
  cbn [kentry_ok] in Da; unfold estart in Da; cbn [a_base a_off edenot ev ENV ENVr] in Da; rewrite P0 in Da;
  pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kdisj_at (EVar 0) (-4294967296) (EVar 4)) in exact i) _ HK eq_refl) as Dr;
  cbn [kentry_ok] in Dr; unfold estart in Dr; cbn [a_base a_off edenot ev ENV ENVr] in Dr; rewrite P0 in Dr;
  lazymatch type of Xa with (_ <= bv_unsigned ?av <= _)%Z =>
  lazymatch type of Xr with (_ <= bv_unsigned ?rnd <= _)%Z =>
    exists (bv_unsigned av), (bv_unsigned rnd);
    split; [kcell HK|];
    split; [rewrite P3, P4; exact AUXC|];
    repeat match goal with |- _ /\ _ => split end;
    first [ kcell HK | kzero HK | lia
          | (* [pins] states the goal over [rndp]/[auxvp]; the range facts are over [vals_ev] *)
            (let Xr4 := fresh "Xr4" in pose proof Xr as Xr4; rewrite ?P4 in Xr4;
             let Xa3 := fresh "Xa3" in pose proof Xa as Xa3; rewrite ?P3 in Xa3; kcell HK) ]
  end end.

(* [comment removed for export] *)
Lemma cell_join : forall M a n1 n2 v1 v2 v,
  cell M a n1 v1 -> cell M (a + Z.of_nat n1) n2 v2 ->
  word_to_le_bytes n1 (Z_to_bv 64 v1) ++ word_to_le_bytes n2 (Z_to_bv 64 v2) = word_to_le_bytes (n1 + n2) (Z_to_bv 64 v) ->
  (0 <= a)%Z -> (a + Z.of_nat n1 < 2 ^ 64)%Z -> cell M a (n1 + n2) v.
Proof.
  unfold cell. intros M a n1 n2 v1 v2 v H1 H2 Hw Ha Hn. rewrite <- Hw.
  apply rdn_app; [exact H1|]. rewrite w_add_nat, u_small by lia. exact H2.
Qed.

(* [comment removed for export] *)
Lemma kwr_window : forall E M kn b kk len base,
  know_ok RSEGS E M kn -> kderive RSEGS kn (KWr (SA b kk) len) = true ->
  (bv_unsigned (edenot E b) + kk)%Z = base ->
  forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= len)%Z -> store_ok RSEGS M (Z_to_bv 64 (base + d)) m = true.
Proof.
  intros E M kn b kk len base HK Hd Hb d m H0 Hm.
  destruct (kderive_sound RSEGS E M kn _ HK Hd) as [Hf Hst]. unfold estart in Hst. cbn [a_base a_off] in Hst.
  rewrite Hb in Hst. apply Hst; assumption.
Qed.

(* [comment removed for export] *)
Definition fG (i : nat) : nat := if Nat.eqb i 2 then 70%nat else 72%nat.
Definition fT (i : nat) : nat := if Nat.eqb i 2 then 71%nat else 72%nat.

(* [comment removed for export] *)
Ltac kreg HR :=
  lazymatch goal with |- getr ?R ?r = _ =>
  lazymatch type of HR with regs_ok ?E ?sr R =>
    let e := eval vm_compute in (sr_get sr r) in
    rewrite (reg_val E sr R r HR); change (sr_get sr r) with e; kside
  end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* LPS 08b1429: the auxv of the main entry's memory, in [S0TargetPre.auxv_cells]' form, over
   both CONFIG_RSEQ layouts (the launch's [kb_rseq] is case-split, never fixed). *)
Lemma auxv_cells_launch : forall (a0s path : list byte) (envv : list (list byte)) fs0 stdin0
    (hw mbase sp0 brk : word) (rnd : EntryDraw) (tid : word) regs0 (mem0 : word -> option byte),
  valid_argv [a0s; path] -> valid_envp envv -> valid_sp sp0 ->
  main_launch (mkProcInputA [a0s; path] envv fs0 stdin0) hw mbase sp0 brk rnd tid regs0 mem0 ->
  auxv_cells mem0 (bv_unsigned (auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0))
                  (bv_unsigned (rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0))
  /\ (bv_unsigned sp0 <= bv_unsigned (auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0))%Z
  /\ (bv_unsigned (auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0) + 464 <= 2 ^ 64)%Z.
Proof.
  intros a0s path envv fs0 stdin0 hw mbase sp0 brk rnd tid regs0 mem0 Hva Hve Hvsp ME.
  destruct ME as (Hhw & Hvl & Hlau & ME').
  set (inp := mkProcInputA [a0s; path] envv fs0 stdin0) in *.
  assert (RD : forall j z a, (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat ->
     nth j (auxv_words (launch_auxv inp sp0 mbase) RPH (0x133fc : word) (in_uid inp) (in_gid inp) (in_hwcap inp)
              (rndp inp sp0) (at_execfn_ptr (ed_top rnd) (in_execfn inp))) (Z_to_bv 64 0) = Z_to_bv 64 z ->
     a = (bv_unsigned (auxvp inp sp0) + 8 * Z.of_nat j)%Z ->
     cell mem0 a 8 z).
  { intros j z a Hj Hw Ha. unfold cell.
    (* [inp] given up front: otherwise the [in_argv ?inp = [?a0s; ?path]] premise comes first
       with ?inp open and no alternative closes it (a run printed it) *)
    eapply rd_auxv_main with (inp := inp);
      first [ exact Hj | exact Hw | exact Ha | exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hvsp
            | exact ME' | reflexivity | eassumption ]. }
  assert (AB : (bv_unsigned sp0 <= bv_unsigned (auxvp inp sp0))%Z /\ (bv_unsigned (auxvp inp sp0) + 464 <= 2 ^ 64)%Z).
  { eapply auxvp_bounds with (inp := inp);
      first [ exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hvsp | exact ME' | reflexivity | eassumption ]. }
  split; [|exact AB].
  Ltac auxNTH := unfold auxv_words, auxv_entries; cbn [flat_map app nth fst snd]; reflexivity.
  unfold auxv_cells.
  split; [apply (RD 0%nat 33%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 2%nat 40%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 4%nat 41%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 6%nat 42%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 8%nat 43%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 10%nat 44%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 12%nat 45%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 14%nat 46%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 16%nat 47%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 18%nat 51%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 20%nat 16%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 22%nat 6%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 24%nat 17%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 26%nat 3%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 28%nat 4%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 30%nat 5%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 32%nat 7%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 34%nat 8%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 36%nat 9%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 38%nat 11%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 40%nat 12%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 42%nat 13%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 44%nat 14%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 46%nat 23%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 48%nat 25%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  split; [apply (RD 49%nat (bv_unsigned (rndp inp sp0)));
          [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia
          | unfold auxv_words, auxv_entries; cbn [flat_map app nth fst snd]; symmetry; apply Z_to_bv_bv_unsigned | lia]|].
  split; [apply (RD 50%nat 31%Z); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | auxNTH | lia]|].
  (* [inp] / [mbase] are proof-local, so the Ltac takes them as arguments (an Ltac body cannot
     name a proof's local variables: "The reference inp was not found",
     as a run printed it). *)
  Ltac auxNTHR ER inp mbase := unfold auxv_words, auxv_entries;
    change (la_rseq (launch_auxv inp _ mbase)) with (kb_rseq (in_kernel inp)); rewrite ER;
    cbn [flat_map app nth fst snd]; reflexivity.
  destruct (kb_rseq (in_kernel inp)) eqn:ER; [left | right].
  (* [destruct ... eqn:ER] also rewrote [RD]'s bound, so it may already read [auxv_count true] *)
  - split; [apply (RD 52%nat 27%Z); [unfold auxv_count; try rewrite ER; lia | auxNTHR ER inp mbase | lia]|].
    split; [apply (RD 54%nat 28%Z); [unfold auxv_count; try rewrite ER; lia | auxNTHR ER inp mbase | lia]|].
    apply (RD 56%nat 0%Z); [unfold auxv_count; try rewrite ER; lia | auxNTHR ER inp mbase | lia].
  - apply (RD 52%nat 0%Z); [unfold auxv_count; try rewrite ER; lia | auxNTHR ER inp mbase | lia].
Qed.

Section World.
  Context {ACEIL__ : ACeil} {RUNW__ : RunW}.   (* [comment removed for export] *)
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable hw : word.    (* [comment removed for export] *)
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_launch (mkProcInputA [a0s; path] envv fs0 stdin0) hw mbase sp0 brk rnd tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hceil : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma atop_sp0 : forall r m na sb b l mb, atop_ok (mkVmMapsFull r m na sb b l mb sp0).
  Proof. intros. unfold atop_ok, alloc_top. cbn [vm_init_sp]. rewrite Hceil. unfold stack_max_size. lia. Qed.
  (* [comment removed for export] *)
  Hypothesis Hguard : run_guard = bv_unsigned (canary_w rnd).
  Hypothesis Hsec : run_secret = bv_unsigned (secret_word rnd).
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpnd : openat_plain_name path = true.   (* [comment removed for export] *)
  Hypothesis Hplen : (length path <= 4095)%nat.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rnd) (mkProcInputA [a0s; path] envv fs0 stdin0).
  (* the launch's mmap base is page aligned ([Run.valid_mmap_base]) *)
  Lemma mbase_al : (bv_unsigned mbase mod page_size = 0)%Z.
  Proof.
    pose proof Hlau as Hl. cbn [entry_launch_ok_va] in Hl. destruct Hl as (_ & _ & Hb).
    exact (proj2 (proj2 (MmapBase.valid_launch_base_sv48_in_band _ _ Hb))).
  Qed.
  Variable fd3 : FdEntry.      (* [comment removed for export] *)
  Variable SI : (word -> option byte) -> Prop.   (* [comment removed for export] *)
  Hypothesis SI_step : forall M M' : word -> option byte,
    (forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M' a = M a) -> SI M -> SI M'.
  (* LPS 08b1429: [SI] keeps the memory above sp0 the launch's ([SymAbove.above_eq], which is how
     every instance is built).  It carries the auxv, whose layout follows the kernel build, to the
     malloc entry ([auxv_cells_SI]). *)
  Hypothesis SI_above : forall M, SI M -> forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a.

  Lemma auxv_cells_SI : forall M, SI M ->
    auxv_cells M (bv_unsigned (auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0))
                 (bv_unsigned (rndp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0)).
  Proof.
    intros M HSI.
    destruct (auxv_cells_launch a0s path envv fs0 stdin0 hw mbase sp0 brk rnd tid regs0 mem0 Hva Hve Hvsp ME)
      as (AC & B1 & B2).
    pose proof (u64_range (auxvp (mkProcInputA [a0s; path] envv fs0 stdin0) sp0)) as Hau.
    apply (auxv_cells_agree mem0 M _ _ AC); [lia | exact B2 |].
    intros i Hi. apply (SI_above M HSI). rewrite u64_lit by lia. lia.
  Qed.

  #[local] Notation ENVv := (ENV a0s path hw rnd).
  #[local] Notation modelV := (modelV tid fs0 stdin0 fd3).

  (* [comment removed for export] *)
  Definition vm_small (VM : VmMaps) (gm : word) : Prop :=
    (* the run's vDSO/vvar pair is in the ledger ([State.init_reserved]) *)
    incl (vdso_reserved (ia_kernel stdin0) (vdso_top VM)) (vm_reserved VM) /\ vm_limit VM = LIM
    /\ (length (vm_maps VM) <= 4)%nat
    /\ In (gm, Z_to_bv 64 69632) (vm_maps VM)
    /\ Forall (fun p => (0 < bv_unsigned (snd p) <= 69632)%Z /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) (vm_maps VM)
    /\ seps (vm_maps VM).

  (* [comment removed for export] *)
  Definition after_malloc (K : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (mb gm : word) (area brkv mas : Z),
      area = (bv_unsigned mb + 4096)%Z ->
      read_pre sp0 (p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd) mb gm R M ->
      world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned hw) M ->
      main_frame (bv_unsigned sp0) M ->
      vm_pre VM mb gm -> vm_small VM gm ->
      target_vmx (bv_unsigned sp0) (bv_unsigned gm) area brkv mas VM -> auxv0 (bv_unsigned sp0) M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1359c) M (seg_rom RSEGS))
                              (model_pre path VM stdin0 fs0 tid)) K.

  (* [comment removed for export] *)
  Definition after_malloc_gen (K : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (mb gm : word) (area brkv mas : Z),
      area = (bv_unsigned mb + 4096)%Z ->
      read_pre sp0 (p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd) mb gm R M ->
      world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned hw) M ->
      main_frame (bv_unsigned sp0) M ->
      vm_pre VM mb gm -> vm_small VM gm ->
      target_vmx (bv_unsigned sp0) (bv_unsigned gm) area brkv mas VM -> auxv0 (bv_unsigned sp0) M -> SI M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1359c) M (seg_rom RSEGS))
                              (mkModelA (fdsV fd3) VM stdin0 fs0 None (Some tid) None)) K.

  Lemma modelV_eq : forall VM, modelV VM = mkModelA (fdsV fd3) VM stdin0 fs0 None (Some tid) None.
  Proof. intros VM. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma p1_range : (0x7fff80000000 <= bv_unsigned (p1 (mkProcInputA [a0s; path] envv fs0 stdin0) rnd) <= 0x800000400000)%Z.
  Proof.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. unfold sp_window_lo, sp_window_hi in *.
    pose proof (argv_ptr_bounds Sv48 (mkProcInputA [a0s; path] envv fs0 stdin0) mbase sp0 brk rnd 1 Hlau ltac:(cbn; lia)) as [B1 _].
    pose proof (argv_ptr_fits (mkProcInputA [a0s; path] envv fs0 stdin0) mbase sp0 brk rnd 1 Hlau ltac:(cbn; lia)) as B2.
    unfold p1. lia.
  Qed.

  Variable K : TSet.

  Lemma w65_exitG : after_malloc_gen K -> exitG_branch sp0 a0s path envv hw rnd tid brk mbase fs0 stdin0 fd3 SI K.
  Proof.
    intros AM vals R M VM HL P0 P2 P3 P4 P70 P5 HR HK HVM HVS HVX HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    pose proof (know_nth RSEGS _ _ knZ ltac:(let i := kidx knZ (is_krange gx) in exact i) _ HK eq_refl)
      as Kgm; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kgm.
    pose proof (know_nth RSEGS _ _ knZ ltac:(let i := kidx knZ (is_kalign gx) in exact i) _ HK eq_refl)
      as Kga; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kga.
    pose proof (know_nth RSEGS _ _ knZ ltac:(let i := kidx knZ (is_kdisj bx gx) in exact i) _ HK eq_refl)
      as Kgd; cbn [kentry_ok] in Kgd; unfold estart in Kgd; cbn [a_base a_off edenot ev ENV ENVr gx bx ax] in Kgd; rewrite P70 in Kgd.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ knZ ltac:(let i := kidx knZ (is_kdisj gx (EVar 0)) in exact i) _ HK eq_refl)
      as Kgs; cbn [kentry_ok] in Kgs; unfold estart in Kgs; cbn [a_base a_off edenot ev ENV ENVr gx bx ax] in Kgs; rewrite P0 in Kgs.
    pose proof alloc_ceiling_range as Hcr. pose proof (u64_range hw) as Hhw.
    pose proof p1_range as P1r.
    pose proof (u64_range brk) as Bu. pose proof (u64_range sp0) as Su.
    rewrite modelV_eq.
    apply (AM R M VM brk (vals_ev vals 72) (bv_unsigned brk + 4096)%Z (bv_unsigned brk + 8192)%Z 0%Z).
    - reflexivity.
    - (* [comment removed for export] *)
      constructor.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + lia.
      + exact P1r.
      + (* [comment removed for export] *) exact Hceil.
      + lia.
      + lia.
      + lia.
      + lia.
      + unfold stack_writable. apply (kwr_window (ENVv vals) M knZ (EVar 0) (-6144513) 6144513); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia].
      + unfold group_writable. apply (kwr_window (ENVv vals) M knZ gx 0 69632); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia].
      + unfold meta_writable. apply (kwr_window (ENVv vals) M knZ bx 4096 4096); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia].
      + cps_destruct (errno_some M) as (bs & Hbs & Hlen). exists (Z_to_bv 64 (bytes_le_to_Z bs)).
        rewrite Hbs, word_to_le_bytes_of_lez by (assumption || lia). reflexivity.
      + intros x0 x1 x4 x5 x6 x7 extra ebs.
        apply (know_ok_ren RSEGS (ENVv vals) _ M fG [2;3]%nat kn_M1).
        * intros i Hi. destruct Hi as [<-|[<-|[]]]; cbn [ev ENV fG Nat.eqb vals_ev nth app]; pins; reflexivity.
        * vm_compute. reflexivity.
        * apply (kderive_all_sound RSEGS _ M knZ); [exact HK | vm_compute; reflexivity].
    - (* [comment removed for export] *)
      constructor.
      all: try kcell HK.
      all: try kzero HK.
      + apply (cell_join M _ 4 4 101 0); [kcell HK | kcell HK | reflexivity | lia | lia].
      + apply (cell_join M _ 4 4 0 0); [kcell HK | kcell HK | reflexivity | lia | lia].
      + kdef HK bx 4096%Z 4096%Z.
      + (* [comment removed for export] *)
        constructor; cbn zeta.
        * kbyte HK.
        * kbyte HK.
        * krdn HK.
        * intros _. kbyte HK.
        * intros _. kbyte HK.
        * intros _. krdn HK.
        * intros _. kbyte HK.
        * intros _. krdn HK.
        * change (69616 * 0 / 16 + 1)%Z with 1%Z. lia.
      + kdef HK gx 0%Z 69632%Z.
      + replace (bv_unsigned brk + 4096)%Z with (bv_unsigned brk + 1 * 4096)%Z by lia. rewrite Z_mod_plus_full. exact Bal.
      + exact (proj2 Kga).
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + (* [comment removed for export] *) exact Hhw.
      + exact Htid.
      + cps_destruct (errno_some M) as (bs & Hbs & Hlen). exists (bytes_le_to_Z bs).
        pose proof (SX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb.
        split; [cbn in Hb; lia|]. unfold cell. rewrite Hbs, word_to_le_bytes_of_lez by (assumption || lia). reflexivity.
      + apply (img_clear_of_know (ENVv vals)). apply (kderive_all_sound RSEGS _ M knZ); [exact HK | vm_compute; reflexivity].
    - (* [comment removed for export] *)
      constructor. all: kcell HK.
    - exact HVM.
    - (* [comment removed for export] *)
      cps_destruct HVS as (Hr & Hl & Hm). unfold vm_small.
      split.
      { pose proof HVX as (mx & nx & EVx & _). rewrite EVx. exact (vdso_in_init_reserved _ _ _ _ _ _ _ _ _ mbase_al). }
      rewrite Hl. split; [reflexivity|].
      assert (U1 : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by reflexivity.
      assert (U2 : bv_unsigned (Z_to_bv 64 8192) = 8192%Z) by reflexivity.
      assert (U3 : bv_unsigned (Z_to_bv 64 4096) = 4096%Z) by reflexivity.
      destruct Hm as [[-> Hdj] | [-> Hdj]]; cbn [length In fst snd];
        (split; [lia|]); (split; [left; reflexivity|]); split;
        [ repeat constructor; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia
        | apply seps_cons; [constructor; [unfold iv_disjoint; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia | constructor]
                          | apply seps_cons; [constructor | apply seps_nil]]
        | repeat constructor; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia
        | apply seps_cons; [constructor; [unfold iv_disjoint; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia | constructor]
                          | apply seps_cons; [constructor | apply seps_nil]] ].
    - (* [comment removed for export] *)
      (* [target_vmx] gained the reserved list [rs] at #38; it is whatever [EVM] says *)
      cps_destruct HVX as (maps & na & EVM & Hmn). exists brk, mbase. eexists. split; [exact Hbrk|]. left.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists maps, na. split; [rewrite !Z_to_bv_bv_unsigned; exact EVM| exact Hmn].
    - (* [comment removed for export] *) kauxv HK knZ P0 P3 P4 (auxv_cells_SI _ HSI).
    - exact HSI.
  Qed.

  Lemma w65_exitT : after_malloc_gen K -> exitT_branch sp0 a0s path envv hw rnd tid brk mbase fs0 stdin0 fd3 SI K.
  Proof.
    intros AM vals R M VM HL P0 P2 P3 P4 P70 P5 HR HK HVM HVS HVX HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_krange gx) in exact i) _ HK eq_refl)
      as Kgm; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kgm.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_kalign gx) in exact i) _ HK eq_refl)
      as Kga; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kga.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_kdisj ax gx) in exact i) _ HK eq_refl)
      as Kgd; cbn [kentry_ok] in Kgd; unfold estart in Kgd; cbn [a_base a_off edenot ev ENV ENVr gx bx ax] in Kgd.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_krange ax) in exact i) _ HK eq_refl)
      as Kam; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kam.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_kalign ax) in exact i) _ HK eq_refl)
      as Kaa; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kaa.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_kdisj (ELit 0) ax) in exact i) _ HK eq_refl)
      as Kai; cbn [kentry_ok] in Kai; unfold estart in Kai; cbn [a_base a_off edenot ev ENV ENVr gx bx ax] in Kai; rewrite u0 in Kai.
    pose proof (u64_range (vals_ev vals 71)) as Au.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_kdisj gx (EVar 0)) in exact i) _ HK eq_refl)
      as Kgs; cbn [kentry_ok] in Kgs; unfold estart in Kgs; cbn [a_base a_off edenot ev ENV ENVr gx bx ax] in Kgs; rewrite P0 in Kgs.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_kdisj ax (EVar 0)) in exact i) _ HK eq_refl)
      as Kas; cbn [kentry_ok] in Kas; unfold estart in Kas; cbn [a_base a_off edenot ev ENV ENVr gx bx ax] in Kas; rewrite P0 in Kas.
    pose proof alloc_ceiling_range as Hcr. pose proof (u64_range hw) as Hhw.
    pose proof p1_range as P1r.
    pose proof (u64_range brk) as Bu. pose proof (u64_range sp0) as Su.
    rewrite modelV_eq.
    apply (AM R M VM (vals_ev vals 71) (vals_ev vals 72) (bv_unsigned (vals_ev vals 71) + 4096)%Z (2 ^ 64 - 1)%Z 1%Z).
    - reflexivity.
    - (* [comment removed for export] *)
      constructor.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + lia.
      + exact P1r.
      + (* [comment removed for export] *) exact Hceil.
      + lia.
      + lia.
      + lia.
      + lia.
      + unfold stack_writable. apply (kwr_window (ENVv vals) M knZm (EVar 0) (-6144513) 6144513); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia].
      + unfold group_writable. apply (kwr_window (ENVv vals) M knZm gx 0 69632); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia].
      + unfold meta_writable. apply (kwr_window (ENVv vals) M knZm ax 4096 4096); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia].
      + cps_destruct (errno_some M) as (bs & Hbs & Hlen). exists (Z_to_bv 64 (bytes_le_to_Z bs)).
        rewrite Hbs, word_to_le_bytes_of_lez by (assumption || lia). reflexivity.
      + intros x0 x1 x4 x5 x6 x7 extra ebs.
        apply (know_ok_ren RSEGS (ENVv vals) _ M fT [2;3]%nat kn_M1).
        * intros i Hi. destruct Hi as [<-|[<-|[]]]; cbn [ev ENV fT Nat.eqb vals_ev nth app]; pins; reflexivity.
        * vm_compute. reflexivity.
        * apply (kderive_all_sound RSEGS _ M knZm); [exact HK | vm_compute; reflexivity].
    - (* [comment removed for export] *)
      constructor.
      all: try kcell HK.
      all: try kzero HK.
      + apply (cell_join M _ 4 4 101 0); [kcell HK | kcell HK | reflexivity | pins; lia | pins; lia].
      + apply (cell_join M _ 4 4 0 0); [kcell HK | kcell HK | reflexivity | pins; lia | pins; lia].
      + kdef HK ax 4096%Z 4096%Z.
      + (* [comment removed for export] *)
        constructor; cbn zeta.
        * kbyte HK.
        * kbyte HK.
        * krdn HK.
        * intros _. kbyte HK.
        * intros _. kbyte HK.
        * intros _. krdn HK.
        * intros _. kbyte HK.
        * intros _. krdn HK.
        * change (69616 * 0 / 16 + 1)%Z with 1%Z. lia.
      + kdef HK gx 0%Z 69632%Z.
      + replace (bv_unsigned (vals_ev vals 71) + 4096)%Z with (bv_unsigned (vals_ev vals 71) + 1 * 4096)%Z by lia. rewrite Z_mod_plus_full. exact (proj2 Kaa).
      + exact (proj2 Kga).
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + (* [comment removed for export] *) exact Hhw.
      + exact Htid.
      + cps_destruct (errno_some M) as (bs & Hbs & Hlen). exists (bytes_le_to_Z bs).
        pose proof (SX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb.
        split; [cbn in Hb; lia|]. unfold cell. rewrite Hbs, word_to_le_bytes_of_lez by (assumption || lia). reflexivity.
      + apply (img_clear_of_know (ENVv vals)). apply (kderive_all_sound RSEGS _ M knZm); [exact HK | vm_compute; reflexivity].
    - (* [comment removed for export] *)
      constructor. all: kcell HK.
    - exact HVM.
    - (* [comment removed for export] *)
      cps_destruct HVS as (Hr & Hl & Hm). unfold vm_small.
      split.
      { rewrite HVX. exact (vdso_in_init_reserved _ _ _ _ _ _ _ _ _ mbase_al). }
      rewrite Hl. split; [reflexivity|].
      assert (U1 : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by reflexivity.
      assert (U2 : bv_unsigned (Z_to_bv 64 8192) = 8192%Z) by reflexivity.
      assert (U3 : bv_unsigned (Z_to_bv 64 4096) = 4096%Z) by reflexivity.
      destruct Hm as [[-> Hdj] | [-> Hdj]]; cbn [length In fst snd];
        (split; [lia|]); (split; [left; reflexivity|]); split;
        [ repeat constructor; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia
        | apply seps_cons; [constructor; [unfold iv_disjoint; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia | constructor]
                          | apply seps_cons; [constructor | apply seps_nil]]
        | repeat constructor; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia
        | apply seps_cons; [constructor; [unfold iv_disjoint; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia | constructor]
                          | apply seps_cons; [constructor | apply seps_nil]] ].
    - (* [comment removed for export] *)
      (* [target_vmx] gained the reserved list [rs] at #38; it is whatever [HVX] says *)
      lazymatch type of HVX with _ = mkVmMapsFull ?rs _ _ _ _ _ _ _ => exists brk, mbase, rs end.
      split; [exact Hbrk|]. right.
      split; [reflexivity|]. split; [reflexivity|]. exists (vals_ev vals 71). split; [reflexivity|].
      rewrite !Z_to_bv_bv_unsigned. exact HVX.
    - (* [comment removed for export] *) kauxv HK knZm P0 P3 P4 (auxv_cells_SI _ HSI).
    - exact HSI.
  Qed.

  (* [comment removed for export] *)
  Theorem brk_ok_semV : after_malloc_gen K ->
    brk_ok_entry sp0 a0s path envv hw rnd tid brk mbase fs0 stdin0 fd3 SI K.
  Proof. intros AM. apply brk_ok_worldV; try assumption. apply w65_exitG, AM. Qed.

  Theorem mmap_ok_semV : after_malloc_gen K ->
    mmap_ok_entry sp0 a0s path envv hw rnd tid brk mbase fs0 stdin0 fd3 SI K.
  Proof. intros AM. apply mmap_ok_worldV; try assumption. apply w65_exitT, AM. Qed.
End World.

(* [comment removed for export] *)
Theorem brk_ok_sem_g {ACEIL__ : ACeil} {RUNW__ : RunW} sp0 a0s path envv hw rnd tid mem0 brk mbase fs0 stdin0
  (Hva : valid_argv [a0s; path]) (Hve : valid_envp envv)
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hceil : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z)
  (Hguard : run_guard = bv_unsigned (canary_w rnd)) (Hsec : run_secret = bv_unsigned (secret_word rnd))
  (Hplen : (length path <= 4095)%nat)
  (Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rnd) (mkProcInputA [a0s; path] envv fs0 stdin0))
  regs0 (ME : main_launch (mkProcInputA [a0s; path] envv fs0 stdin0) hw mbase sp0 brk rnd tid regs0 mem0) fd3 K :
  after_malloc_gen sp0 a0s path envv hw rnd tid fs0 stdin0 fd3 (above_eq sp0 mem0) K ->
  brk_ok_branch_g sp0 a0s path envv hw rnd tid mem0 brk mbase fs0 stdin0 fd3 K.
Proof.
  intros AM. exact (brk_ok_semV sp0 a0s path envv hw rnd tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hbrk Hceil Hguard Hsec Hplen Hlau fd3
                      (above_eq sp0 mem0) (above_eq_step sp0 mem0) (fun M H => H) K AM).
Qed.

Theorem mmap_ok_sem_g {ACEIL__ : ACeil} {RUNW__ : RunW} sp0 a0s path envv hw rnd tid mem0 brk mbase fs0 stdin0
  (Hva : valid_argv [a0s; path]) (Hve : valid_envp envv)
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hceil : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z)
  (Hguard : run_guard = bv_unsigned (canary_w rnd)) (Hsec : run_secret = bv_unsigned (secret_word rnd))
  (Hplen : (length path <= 4095)%nat)
  (Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rnd) (mkProcInputA [a0s; path] envv fs0 stdin0))
  regs0 (ME : main_launch (mkProcInputA [a0s; path] envv fs0 stdin0) hw mbase sp0 brk rnd tid regs0 mem0) fd3 K :
  after_malloc_gen sp0 a0s path envv hw rnd tid fs0 stdin0 fd3 (above_eq sp0 mem0) K ->
  mmap_ok_branch_g sp0 a0s path envv hw rnd tid mem0 brk mbase fs0 stdin0 fd3 K.
Proof.
  intros AM. exact (mmap_ok_semV sp0 a0s path envv hw rnd tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hbrk Hceil Hguard Hsec Hplen Hlau fd3
                      (above_eq sp0 mem0) (above_eq_step sp0 mem0) (fun M H => H) K AM).
Qed.

(* [comment removed for export] *)
Theorem brk_ok_sem {ACEIL__ : ACeil} {RUNW__ : RunW} sp0 a0s path envv hw rnd tid mem0 brk mbase fs0 stdin0
  (Hva : valid_argv [a0s; path]) (Hve : valid_envp envv)
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hceil : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z)
  (Hguard : run_guard = bv_unsigned (canary_w rnd)) (Hsec : run_secret = bv_unsigned (secret_word rnd))
  (Hplen : (length path <= 4095)%nat)
  (Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rnd) (mkProcInputA [a0s; path] envv fs0 stdin0))
  regs0 (ME : main_launch (mkProcInputA [a0s; path] envv fs0 stdin0) hw mbase sp0 brk rnd tid regs0 mem0) K :
  after_malloc sp0 a0s path envv hw rnd tid fs0 stdin0 K ->
  brk_ok_branch sp0 a0s path envv hw rnd tid mem0 brk mbase fs0 stdin0 K.
Proof.
  intros AM. apply (brk_ok_sem_g sp0 a0s path envv hw rnd tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hceil Hguard Hsec Hplen Hlau regs0 ME).
  intros R M VM mb gm area brkv mas EA RP W MF VP VS VX AX _. exact (AM R M VM mb gm area brkv mas EA RP W MF VP VS VX AX).
Qed.

Theorem mmap_ok_sem {ACEIL__ : ACeil} {RUNW__ : RunW} sp0 a0s path envv hw rnd tid mem0 brk mbase fs0 stdin0
  (Hva : valid_argv [a0s; path]) (Hve : valid_envp envv)
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hceil : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z)
  (Hguard : run_guard = bv_unsigned (canary_w rnd)) (Hsec : run_secret = bv_unsigned (secret_word rnd))
  (Hplen : (length path <= 4095)%nat)
  (Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rnd) (mkProcInputA [a0s; path] envv fs0 stdin0))
  regs0 (ME : main_launch (mkProcInputA [a0s; path] envv fs0 stdin0) hw mbase sp0 brk rnd tid regs0 mem0) K :
  after_malloc sp0 a0s path envv hw rnd tid fs0 stdin0 K ->
  mmap_ok_branch sp0 a0s path envv hw rnd tid mem0 brk mbase fs0 stdin0 K.
Proof.
  intros AM. apply (mmap_ok_sem_g sp0 a0s path envv hw rnd tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hceil Hguard Hsec Hplen Hlau regs0 ME).
  intros R M VM mb gm area brkv mas EA RP W MF VP VS VX AX _. exact (AM R M VM mb gm area brkv mas EA RP W MF VP VS VX AX).
Qed.
