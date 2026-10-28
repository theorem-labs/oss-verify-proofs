(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.varnish.esi_parse_fuzzer.images Require Import Plain.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Amb.

Module D_Re2vu.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.varnish.esi_parse_fuzzer.images Require Import Plain.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec SymExec2.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 RefMocc D_Manqc SymDqus D_Li6dm.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Amb OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDqus OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Li6dm.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Definition STOPS : list Z := [0x2ac54; 0x2b058; 0x2b41c; 0x2ab58; 0x12a44; 0x12bd0; 0x24568; 0x2299c; 0x25d58]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition KEPT_MC : list nat := map ridx callee_kept.     (* [comment removed for export] *)
Definition KEPT_CS : list nat := map ridx callee_saved.    (* [comment removed for export] *)
Definition IHI : Z := 0x63000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

(* [comment removed for export] *)
Definition srRE_base : list expr :=
  [ELit 0; ELit 0; spx (-128); ELit 0x10800; ELit 0x42158; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; EVar 2; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].
Definition KEPT_RE : list nat := [2; 3; 4; 18]%nat.
Definition srRE0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RE 6.

(* [comment removed for export] *)
Definition knRE0 : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) 8388608;
   KRange (EVar 2) 0x7fff80000000 0x800000400000;
   KWr (SA (ELit 0) 0x31000) 0x32000;   (* [comment removed for export] *)
   KImg 0x10000 0x317b0; KImg 0x317b1 0x317f9; KImg 0x417f9 0x42088; KImg 0x62160 0x62180;   (* [comment removed for export] *)
   KWord (SA (ELit 0) 0x42090) 8 (ELit 0x42090);
   KWord (SA (ELit 0) 0x420b0) 4 (EVar 5);
   KImg 0x420bc 0x42108; KImg 0x42110 0x42128; KImg 0x42130 0x42148;
   KImg 0x42158 0x42168; KImg 0x42170 0x62160; KImg 0x62198 0x623c8;
   KBlob (SA (ELit 0) 0x623c8) (ELit 8) 2;   (* [comment removed for export] *)
   KImg 0x623d0 0x623d8; KImg 0x623e9 0x623f0; KImg 0x623f8 0x62400; KImg 0x62410 0x62418;
   KWord (SA (ELit 0) 0x62418) 8 (ELit 4096);
   KImg 0x62420 0x62450; (* [comment removed for export] *)
   KImg 0x62830 0x63000;
   KRange (EVar 5) 1 4194303].

(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x17d90 srRE0 [] knRE0 39.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.
(* [comment removed for export] *)
Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-542)) 1 (ELit 32);
   SE (SA (EVar 0) (-544)) 2 (ELit 28271);
   SE (SA (EVar 0) (-552)) 8 (ELit 2338053693894893668);
   SE (SA (EVar 0) (-560)) 8 (ELit 7018141077071293539)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0x259a8 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0x259a8 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0x267f8 srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0x259a8 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0x259a8 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0x259a8 srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scRE : stdio_res := Eval vm_compute in
  match stdio_call 231 srH knH with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srI0 : list expr := Eval vm_compute in sc_sr scRE.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scRE.

(* [comment removed for export] *)
Definition ssI0 : sym_state := SS (sc_ret scRE) srI0 [] knI0 263.
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

Lemma itinerary_re :
  (s_pc (fst (fst rB)), snd (fst rB)) = (0x2ac54%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x2ac54%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x2b41c%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0x2ac54%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0x2ac54%Z, [SCBr true BC_GEU (ELit 61) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0x2ac54%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 61)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x25d58%Z, [])
  /\ stdio_call 231 srH knH = Some scRE
  /\ (sc_ret scRE, sc_f scRE, sc_fd scRE) = (0x26158%Z, 0x315a8%Z, 2%Z)
  /\ (sc_wb scRE, sc_wp scRE, sc_l scRE) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-540)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0x2299c%Z, []).
(* [comment removed for export] *)
Proof.
  OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  lazymatch goal with |- @eq ?T ?a ?b => vm_cast_no_check (@eq_refl T b) end.
Qed.

End D_Re2vu.


Module D_Rec7j.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.varnish.esi_parse_fuzzer.images Require Import Plain.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk ShapeAlg Nodes.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Frame Shapi1s.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim AllocSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require AgentLib SymExec SymExec2.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 SymDqus Spec LibWbxd D_Exvwg D_Stqgu D_Exit D_Li6dm RefMocc D_Me92w.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Opzpl.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Memchr.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Opzpl.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Stmwg D_Manqc LibTail.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Amb OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Frame OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Shapi1s OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDqus OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Spec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibWbxd OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Exvwg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Stqgu OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Exit OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Li6dm OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Me92w OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Opzpl.D_Memcpy OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Memchr OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Opzpl.D_Stln6 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Stmwg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibTail.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_Re2vu.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

Section Tail.
  Context {BW : BWorld}.
  Variable sp0 : word.
  Variable BL : list (list byte).          (* [comment removed for export] *)
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev BL).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma re_segI : forall vals R M,
    length vals = 263%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) srI0 R -> know_ok RSEGS (ENV vals) M knI0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x26158) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 263%nat.
    (* [comment removed for export] *)
    apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model)))).
    2:{ cbn [W map].
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity).
        apply t_eq_sym. apply t_emit_nil_exit. }
    apply ref_exit_Z.
    pose proof (know_nth RSEGS _ _ knI ltac:(let i := kidx knI (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid.
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x42158), (bv_unsigned (vals_ev vals 5)),
           (Z_to_bv 64 0), (Z_to_bv 64 0), false.
    split; [|split; [unfold atexit_st; krd_solve HK|split; [exact Hh|split; [exact Hlazy|]]]].
    + constructor.
      * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
        rewrite P0. f_equal; lia.
      * regv HR (4 : reg). reflexivity.
      * regv HR (10 : reg). reflexivity.
      * rewrite u_small by lia. lia.
      * rewrite u_small by lia. lia.
      * rewrite u_small by lia.
        pose proof (kwr_store_ok RSEGS (ENV vals) _ knI ltac:(let i := kidx knI (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia. exact Hst.
      * lit_u. lia.
      * lit_u. lia.
      * lia.
      * lit_u. change (270680 - 168)%Z with 0x420b0%Z.
        krd HK 0x420b0%Z 4%nat Htc. rewrite Htc. cbn [ev ENV].
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia).
        rewrite Z_to_bv_bv_unsigned. reflexivity.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.   (* [comment removed for export] *)
      * krd_solve HK.   (* [comment removed for export] *)
      * repeat split; krd_solve HK.
      * repeat split; krd_solve HK.
    + left. split; [reflexivity|].
      exists (Z_to_bv 64 0), (Z_to_bv 64 0). repeat split; krd_solve HK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition PRE19 : list byte := s2b "cli: read error on "%string.

  Lemma PRE19_words :
    word_to_le_bytes 8 (Z_to_bv 64 7018141077071293539)
    ++ word_to_le_bytes 8 (Z_to_bv 64 2338053693894893668)
    ++ word_to_le_bytes 2 (Z_to_bv 64 28271)
    ++ word_to_le_bytes 1 (Z_to_bv 64 32) = PRE19.
  Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.

  Lemma re_segH : forall (path : list byte) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 60)%Z ->
    length vals = 231%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srH0 R -> know_ok RSEGS (ENV vals) M knH0 ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541 + P)) 1%nat = Some [Z_to_bv 8 10] ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x259a8) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_read_error path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path P vals R M HP HPr HL P0 P113 HR HK SBp SBn.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scr0 231%nat.
    (* [comment removed for export] *)
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    assert (SBn' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 541 + P)) 1 = Some [Z_to_bv 8 10]).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBn | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; cbn; lia]. }
    clear EQM SBp SBn. rename M0 into M'. 
    (* [comment removed for export] *)
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-544)%Z 2%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-542)%Z 1%nat Hw3. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2, Hw3. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2, Hw3.
    rewrite P0 in Hw0, Hw1, Hw2, Hw3.
    assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 19 = Some PRE19).
    { rewrite <- PRE19_words. change 19%nat with (8 + (8 + (2 + 1)))%nat.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [ | | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
      + apply rdn_app_Z; [ | | lia | lia].
        * replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2.
        * replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 2)%Z with (bv_unsigned sp0 + -542)%Z by lia.
          exact Hw3. }
    assert (MSG : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (19 + (length path + 1))
                  = Some (msg_read_error path)).
    { unfold msg_read_error. change (s2b _) with PRE19.
      apply rdn_app_Z; [exact H17 | | lia | lia].
      apply rdn_app_Z; [| | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 19)%Z with (bv_unsigned sp0 - 541)%Z by lia. exact SBp'.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 19 + Z.of_nat (length path))%Z
          with (bv_unsigned sp0 - 541 + P)%Z by lia. exact SBn'. }
    (* [comment removed for export] *)
    assert (LEN : length (msg_read_error path) = (19 + (length path + 1))%nat)
      by (unfold msg_read_error; rewrite !length_app; reflexivity).
    replace (W 2 (msg_read_error path)) with (map (WriteEv (Z_to_bv 64 2)) (msg_read_error path ++ []))
      by (unfold W; rewrite app_nil_r; reflexivity).
    pose proof itinerary_re as (_ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH knH Rc Mc model scRE (msg_read_error path) []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH knH) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scRE]; rewrite ?LEN end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot length]. reflexivity.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z in MSG by lia. exact MSG.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (re_segI (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma re_nl_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x12008) 1 = Some [Z_to_bv 8 10].
  Proof. vm_compute. reflexivity. Qed.

  Lemma re_segG : forall (path : list byte) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 60)%Z ->
    length vals = 199%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
    regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knG0 ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x259a8) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_read_error path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path P vals R M HP HPr HL P0 P113 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scrG 199%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113).
      replace (-1 * P + 61)%Z with (61 - P)%Z by lia.
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541 + P)).
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x12008) 1 = Some [Z_to_bv 8 10]).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kimg_cov 0x12008 1) in exact i)
                 _ _ 0x12008 1 HK eq_refl) by (cbn; lia). apply re_nl_img. }
    assert (Hdst : store_ok RSEGS M' dst 1 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kwr_cov (EVar 0) (-541) 64) in exact i)
                    _ _ _ (-541 + P) 1 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 541 + P)%Z with (bv_unsigned sp0 + (-541 + P))%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x12008) 1 [Z_to_bv 8 10]).
    { constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x259a8 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x12008) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 1) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M' dst (Z_to_bv 64 0x12008) 1 _ (seg_rom RSEGS) MC Rc (0x259a8 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 175188) with (0x2ac54 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x259a8 : word) with (Z_to_bv 64 0x259a8) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst [Z_to_bv 8 10]) 0 (-541) BUF_HI IHI knG
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst [Z_to_bv 8 10] (ENV vals) 0 (-541) BUF_HI);
                        cbn [ev ENV length]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-541) BUF_HI IHI knG) with knH0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) _ knH0 ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 231%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P113).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (re_segH path P vals1); try eassumption.
    - (* [comment removed for export] *)
      rewrite rdn_wbytes_out; [exact SBp' | | |]; cbn [length]; subst dst; rewrite ?u_small by lia; lia.
    - (* [comment removed for export] *)
      subst dst. pose proof (rdn_wbytes_hit RSEGS [Z_to_bv 8 10] M' (Z_to_bv 64 (bv_unsigned sp0 - 541 + P))) as Hn.
      cbn [length] in Hn. apply Hn. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition reG0 (path : list byte) (P : Z) (T : TSet) : Prop :=
    forall vals R M,
      length vals = 199%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 113 = Z_to_bv 64 P ->
      regs_ok (ENV vals) srG0 R -> know_ok RSEGS (ENV vals) M knG0 ->
      rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x259a8) M (seg_rom RSEGS)) model) T.

  (* [comment removed for export] *)
  Lemma re_segF_gen : forall (path : list byte) (pp : word) (P : Z) (T : TSet) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 61)%Z ->
    length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    reG0 path P T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x259a8) M (seg_rom RSEGS)) model) T.
  Proof.
    intros path pp P T vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 HR HK Hstr HG0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Psmall : (bv_unsigned (edenot (ENV vals) PX) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV PX]. rewrite P113, u_small by lia. lia. }
    unfold PX in Psmall.
    (* [comment removed for export] *)
    run_blk_keep scrF 167%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P113).
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken].
      rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia
        | cbn [ev ENV]; rewrite P0; lia]. }
    clear EQM Hstr. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541)).
    assert (Hsrc : rdn RSEGS M' pp (length path) = Some path).
    { rewrite <- (firstn_app_l _ path [Z_to_bv 8 0]) at 2 || idtac.
      replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    assert (Hdst : store_ok RSEGS M' dst (length path) = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knF ltac:(let i := kidx knF (is_kwr_cov (EVar 0) (-541) 63) in exact i)
                    _ _ _ (-541) (length path) HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 541)%Z with (bv_unsigned sp0 + -541)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst pp P path).
    { constructor; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x259a8 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = pp) by (regv HR (11 : reg); cbn [edenot ev ENV]; exact P2);
      assert (A12 : getr Rc 12 = Z_to_bv 64 P) by (regv HR (12 : reg); cbn [edenot ev ENV]; exact P113);
      destruct (ref_memcpy M' dst pp P _ (seg_rom RSEGS) MC Rc (0x259a8 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 175188) with (0x2ac54 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x259a8 : word) with (Z_to_bv 64 0x259a8) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst path) 0 (-541) BUF_HI IHI knF
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst path (ENV vals) 0 (-541) BUF_HI);
                        cbn [ev ENV]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-541) BUF_HI IHI knF) with knG0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) _ knG0 ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P113).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (HG0 vals1); try eassumption.
    (* [comment removed for export] *)
    subst dst. rewrite <- HP at 1 || idtac.
    pose proof (rdn_wbytes_hit RSEGS path M' (Z_to_bv 64 (bv_unsigned sp0 - 541))) as Hc.
    apply Hc. rewrite u_small by lia. lia.
  Qed.

  Lemma re_segF : forall (path : list byte) (pp : word) (P : Z) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 60)%Z ->
    length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x259a8) M (seg_rom RSEGS)) model)
               (t_emit (W 2 (msg_read_error path)) (t_exit (exit_code 2) (m_fs model))).
  Proof.
    intros path pp P vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 HR HK Hstr.
    eapply (re_segF_gen path pp P _ vals); try eassumption; [lia|].
    intros vals' R' M' HL' Q0 Q113 HR' HK' SB. eapply (re_segG path P vals'); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition reF0 (path : list byte) (pp : word) (P : Z) (T : TSet) : Prop :=
    forall vals R M,
      length vals = 167%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 113 = Z_to_bv 64 P ->
      regs_ok (ENV vals) srF0 R -> know_ok RSEGS (ENV vals) M knE ->
      rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x259a8) M (seg_rom RSEGS)) model) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma re_segDE : forall (path : list byte) (pp : word) (P : Z) (T : TSet) (t8 : list byte) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 131071)%Z -> ~ In (Z_to_bv 8 0) path ->
    length vals = 103%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srD0 R -> know_ok RSEGS (ENV vals) M knC ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8 ->
    reF0 path pp P T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x259a8) M (seg_rom RSEGS)) model) T.
  Proof.
    intros path pp P T t8 vals R M HP HPr Hnonul HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8 HF0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 103%nat.
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
        | cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
    clear EQM Hstr Ht8. rename M0 into M'.
    (* [comment removed for export] *)
    set (spS := Z_to_bv 64 (bv_unsigned sp0 - 1120)).
    assert (Hbuf : rdn RSEGS M' pp (length (path ++ t8)) = Some (path ++ t8)).
    { rewrite length_app. rewrite (word_Z pp). apply rdn_app_Z; [ | | lia | lia].
      - rewrite <- (word_Z pp). replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
          by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
        eapply rdn_firstn; [exact Hstr' | lia].
      - pose proof (rdn_length _ _ _ _ _ Ht8') as L8. rewrite L8, HP. exact Ht8'. }
    assert (Hz : nth (length path) (path ++ t8) (Z_to_bv 8 0) = Z_to_bv 8 0).
    { pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
      rewrite app_nth2, Nat.sub_diag by lia.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp) (length path + 1) _ (length path)
                    ltac:(rewrite <- (word_Z pp); exact Hstr') ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp + P) 8 t8 0 Ht8' ltac:(lia) ltac:(lia) ltac:(lia)) as B2.
      replace (bv_unsigned pp + Z.of_nat (length path))%Z with (bv_unsigned pp + P)%Z in B1 by lia.
      replace (bv_unsigned pp + P + Z.of_nat 0)%Z with (bv_unsigned pp + P)%Z in B2 by lia.
      rewrite B1 in B2. injection B2 as E. rewrite <- E. rewrite app_nth2, Nat.sub_diag by lia. reflexivity. }
    assert (MC : mchrH M' pp (path ++ t8) P 0x7fffffff).
    { pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
      constructor.
      - exact Hbuf.
      - rewrite length_app, L8.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      - rewrite length_app, L8. lia.
      - lia.
      - rewrite <- HP, Nat2Z.id, Hz. reflexivity.
      - intros j Hj. rewrite <- HP, Nat2Z.id in Hj. rewrite nth_app_l by exact Hj.
        intros E. apply (In_nth_neq path (Z_to_bv 8 0) (Z_to_bv 8 0) j Hnonul Hj). apply bv_eq. exact E.
      - lia.
      - lia.
      - intros i Hi.
        pose proof (know_nth RSEGS _ _ knD ltac:(let k := kidx knD (is_kimg_cov 0x12950 24) in exact k) _ HK eq_refl)
          as (_ & _ & Hnone). apply Hnone. lia. }
    assert (Hstk : store_ok RSEGS M' (Z_to_bv 64 (bv_unsigned spS - 32)) 32 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knD ltac:(let i := kidx knD (is_kwr_cov (EVar 0) (-1152) 32) in exact i)
                    _ _ _ (-1152) 32 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst spS. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 1120 - 32)%Z with (bv_unsigned sp0 + -1152)%Z by lia. exact Hst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x267f8 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A2 : getr Rc 2 = spS)
        by (regv HR (2 : reg); subst spS; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A10 : getr Rc 10 = pp) by (regv HR (10 : reg); cbn [edenot ev ENV]; exact P2);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x7fffffff) by (regv HR (11 : reg); reflexivity);
      destruct (ref_strnlen M' pp spS (path ++ t8) P 0x7fffffff (seg_rom RSEGS) Rc (0x267f8 : word) MC
                  ltac:(lia) Hstk ltac:(subst spS; rewrite u_small by lia; lia)
                  ltac:(right; subst spS; rewrite u_small by lia; lia)
                  ltac:(apply ret_ok_even; reflexivity) A1 A2 A10 A11) as (R2 & M2 & Hms & Hkeep & HresP & Hfr);
      clear A1 A2 A10 A11
    end.
    replace (Z_to_bv 64 177180) with (0x2b41c : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x267f8 : word) with (Z_to_bv 64 0x267f8) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_saved
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_saved_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    destruct Hfr as [Hagree Hgrow].
    pose proof (know_cut_sound RSEGS (ENV vals) M' M2 0 (-1152) (-1120) IHI knD
                  ltac:(unfold win_ok, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(intros x Hx; apply Hagree; cbn [outside]; split; [|exact I];
                        unfold in_rng; subst spS; unorm;
                        cbn [ev ENV] in Hx; rewrite P0 in Hx; lia)
                  Hgrow HK) as HK2.
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) M2 (kn_cut 0 (-1152) (-1120) IHI knD)
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 135%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P).
    { subst vals1. change 113%nat with (103 + 10)%nat. rewrite <- HL. rewrite vals_ev_junk by lia. exact HresP. }
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK3.
    assert (HK : know_ok RSEGS (ENV vals1) M2 knE0).
    { unfold knE0. apply know_ok_cons; [|exact HK3].
      apply krange_intro. cbn [edenot ev ENV PX]. rewrite Q113, u_small by lia. lia. }
    clear HK3.
    (* [comment removed for export] *)
    assert (Hstr2 : rdn RSEGS M2 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite (frame_mod_rdn RSEGS M' M2 _ _ pp (conj Hagree Hgrow)); [exact Hstr' | | lia].
      intros i Hi. cbn [outside]. split; [|exact I]. unfold in_rng. subst spS. unorm. lia. }
    clear Hstr' Ht8' Hbuf Hz MC Hstk Hagree Hgrow HresP.
    assert (Psmall : (bv_unsigned (edenot (ENV vals1) (EVar 113)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite Q113, u_small by lia. lia. }
    (* [comment removed for export] *)
    run_blk_keep scrE 135%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. rewrite (edenot_addw0_r _ _ Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    { (* [comment removed for export] *)
      unfold sc_denot. exists [Z_to_bv 8 0]. split.
      - unfold adenot, v_addi. cbn [a_base a_off]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
        ed_lin ltac:(cbn [ev ENV]; rewrite ?Q2, ?Q113). rewrite <- HP.
        pose proof (rdn_byte_Z RSEGS M2 (bv_unsigned pp) (length path + 1) _ (length path)
                      ltac:(rewrite <- (word_Z pp); exact Hstr2) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
        rewrite app_nth2, Nat.sub_diag in B1 by lia. cbn [nth] in B1. exact B1.
      - reflexivity. }
    assert (Hstr3 : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M2 _ 0 0 4194304 IHI);
        [exact Hstr2 | vm_compute; reflexivity | unfold win_ok, IHI; cbn [ev ENV]; rewrite Q0; lia
        | cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
    clear EQM Hstr2. rename M0 into M3.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x1036f) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x259a8 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x1036f) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x1036f) 0 _ (seg_rom RSEGS) MC Rc (0x259a8 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 175188) with (0x2ac54 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    change (wbytes M3 dst []) with M3.
    replace (0x259a8 : word) with (Z_to_bv 64 0x259a8) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R4 callee_kept
                    ltac:(rewrite HL1; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL1 in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev BL) M3 knE ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    set (vals2 := vals1 ++ junk_vals R4) in *.
    assert (HL2 : length vals2 = 167%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
    assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
    assert (W2 : vals_ev vals2 2 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q2).
    assert (W113 : vals_ev vals2 113 = Z_to_bv 64 P) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q113).
    clearbody vals2.
    change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
    eapply (HF0 vals2); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma pre19_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x11ff3) 19 = Some PRE19.
  Proof. vm_compute. reflexivity. Qed.

  Lemma PRE19_len : length PRE19 = 19%nat.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma re_memcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV vals) M logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE19.
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- PRE19_words. cbn [mem_denot logM1]. rewrite !wbytes_app.
    unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
    rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
    repeat (f_equal; try (f_equal; lia)).
  Qed.

  Lemma re_segBC : forall (path : list byte) (pp : word) (P : Z) (T : TSet) (t8 : list byte) vals R M,
    Z.of_nat (length path) = P -> (0 <= P <= 131071)%Z -> ~ In (Z_to_bv 8 0) path ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z -> (bv_unsigned pp + P + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV vals) srRE0 R -> know_ok RSEGS (ENV vals) M knRE0 ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8 ->
    reF0 path pp P T ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17d90) M (seg_rom RSEGS)) model) T.
  Proof.
    intros path pp P T t8 vals R M HP HPr Hnonul HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8 HF0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 39%nat.
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
        | cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
    clear EQM Hstr Ht8. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x11ff3) 19 = Some PRE19).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kimg_cov 0x11ff3 19) in exact i)
                 _ _ 0x11ff3 19 HK eq_refl) by (cbn; lia). apply pre19_img. }
    assert (Hdst : store_ok RSEGS M' dst 19 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-560) 19) in exact i)
                    _ _ _ (-560) 19 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x11ff3) 19 PRE19).
    { constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x259a8 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x11ff3) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 19) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M' dst (Z_to_bv 64 0x11ff3) 19 _ (seg_rom RSEGS) MC Rc (0x259a8 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 175188) with (0x2ac54 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x259a8 : word) with (Z_to_bv 64 0x259a8) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M' dst PRE19) knC0).
    { subst dst. rewrite <- (re_memcpy1_denot vals M' P0).
      eapply (carry_after RSEGS (ENV vals) M' logM1 knB [] knC0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat logM1].
      repeat match goal with
             | |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
             | |- (_ <= _)%nat => lia
             | |- True => exact I
             | |- _ /\ _ => split
             end. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M' dst PRE19) knC0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 71%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    (* [comment removed for export] *)
    assert (Hstr2 : rdn RSEGS (wbytes M' dst PRE19) pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite rdn_wbytes_out; [exact Hstr' | | |]; subst dst; rewrite ?PRE19_len; unorm; lia. }
    assert (Ht82 : rdn RSEGS (wbytes M' dst PRE19) (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite rdn_wbytes_out; [exact Ht8' | | |]; subst dst; rewrite ?PRE19_len; unorm; lia. }
    clear Hstr' Ht8' Hsrc Hdst MC. clearbody dst.
    set (M1 := wbytes M' dst PRE19) in *. clearbody M1. clear M' dst.
    assert (WOKS1 : win_ok (ENV vals1) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite Q0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 71%nat.
    assert (Hstr3 : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M1 _ 0 0 4194304 IHI);
        [exact Hstr2 | vm_compute; reflexivity | exact WOKS1 | cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
    assert (Ht83 : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M1 _ 0 0 4194304 IHI);
        [exact Ht82 | vm_compute; reflexivity | exact WOKS1 | cbn [ev ENV]; rewrite Q0, u_small by lia; lia
        | cbn [ev ENV]; rewrite Q0, u_small by lia; lia]. }
    clear EQM Hstr2 Ht82. rename M0 into M3.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x12006) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x259a8 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x12006) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x12006) 0 _ (seg_rom RSEGS) MC Rc (0x259a8 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 175188) with (0x2ac54 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    change (wbytes M3 dst []) with M3.
    replace (0x259a8 : word) with (Z_to_bv 64 0x259a8) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R4 callee_kept
                    ltac:(rewrite HL1; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL1 in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev BL) M3 knC ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    set (vals2 := vals1 ++ junk_vals R4) in *.
    assert (HL2 : length vals2 = 103%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
    assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
    assert (W2 : vals_ev vals2 2 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q2).
    clearbody vals2.
    change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
    eapply (re_segDE path pp P T t8 vals2); eassumption.
  Qed.

End Tail.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End D_Rec7j.

Module D_Rea7z.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.varnish.esi_parse_fuzzer.images Require Import Plain.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk ShapeAlg Nodes.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Frame SymExec SymExec2.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 SymDqus Spec D_Exvwg D_Manqc LibTail.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Amb OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Frame OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDqus OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Spec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Exvwg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibTail.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_Re2vu OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_Rec7j.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ReadErr.
  Context {BW : BWorld}.
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
  Theorem re_tail : forall (path : list byte) (pp : word) (t8 : list byte) vals R M,
    ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) <= 60)%Z ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z ->
    (bv_unsigned pp + Z.of_nat (length path) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV BL vals) srRE0 R -> know_ok RSEGS (ENV BL vals) M knRE0 ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17d90) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error path) (m_fs model)).
  Proof.
    intros path pp t8 vals R M Hnonul HPl HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8.
    unfold t_die.
    eapply (re_segBC sp0 BL model Hvsp Hh Hlazy path pp (Z.of_nat (length path)) _ t8 vals);
      try eassumption; try lia.
    intros vals' R' M' HL' Q0 Q2 Q113 HR' HK' Hstr'.
    eapply (re_segF sp0 BL model Hvsp Hh Hlazy Hfd2 path pp _ vals'); try eassumption; lia.
  Qed.

End ReadErr.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End D_Rea7z.

From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk SimInv.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg Shapi1s Nodes MmapSim AllocSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require AgentLib.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Frame SymExec SymExec2.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 LibK2dm D_Li6dm Spec LibWbxd RefNodes RefNfmt D_Exvwg D_Stqgu D_Exit RefMocc RefPl89 D_Stmwg D_Manqc.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Usk9e.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require MemSplit D_Kn21w.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Alu7n.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Wamxh SymAux.

Module D_Reu44.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.varnish.esi_parse_fuzzer.images Require Import Plain.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk SimInv ShapeAlg Shapi1s Nodes MmapSim AllocSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require AgentLib Frame SymExec SymExec2.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 SymAux LibK2dm RefMocc D_Kn21w MemSplit Spec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require RefNodes RefPl89 D_Stmwg D_Manqc.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Alu7n D_Wamxh.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Me92w.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Opzpl.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Exvwg.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Amb OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Shapi1s OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Frame OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymAux OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Kn21w OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MemSplit OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Spec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefNodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefPl89 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Stmwg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u.D_MainA OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Alu7n OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Wamxh OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Dr084 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Me92w OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Opzpl.D_Memcpy OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Exvwg.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0 DriverKit.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaMunch.
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); timeout 8 (Zify.zify; xlia zchecker).   (* timeout-ok: fast tier: hot2_mid's caller catches its failure and runs zify; xlia without it *)
Local Ltac hot_lia_prev := first [ OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dl_first | tryif OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then first [ hot2_mid | Zify.zify; xlia zchecker ] else first [ solve [OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Zify.zify; xlia zchecker] | hot2_mid | Zify.zify; xlia zchecker ] ].
Local Ltac hot_lia_rest := first [ OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
Local Ltac lia ::= first [ solve [ OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.hplen_pre; hot_lia_rest ] | hot_lia_rest ].
(* [comment removed for export] *)

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Definition STOPS_L : list Z := [0x17c30; 0x17bf8; 0x17c60; 0x22fc4; 0x22e84; 0x2ac54; 0x25d58; 0x2299c; 0x17e34]%Z.
Definition FUEL_L : nat := 5000.
Definition runL (dirs : list bool) (ss : sym_state) := sym_exec RSEGS FUEL_L true STOPS_L (SCR dirs [] []) ss [].
Definition kn_afterL (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

Tactic Notation "run_blockL" constr(dirs) constr(NX) := run_block_gen FUEL_L STOPS_L (SCR dirs [] []) NX false.
Tactic Notation "run_blockL_keep" constr(dirs) constr(NX) := run_block_gen FUEL_L STOPS_L (SCR dirs [] []) NX true.

(* [comment removed for export] *)
Definition rR1a := Eval vm_compute in runL [true] (SS 0x17c30 sr_drv [] knD 70).   (* [comment removed for export] *)
Definition rR1b := Eval vm_compute in runL [false] (SS 0x17c30 sr_drv [] knD 70).  (* [comment removed for export] *)
Definition srR1a : list expr := Eval vm_compute in s_regs (fst (fst rR1a)).
Definition srR1b : list expr := Eval vm_compute in s_regs (fst (fst rR1b)).
Definition knR1 : list kentry := Eval vm_compute in kn_afterL rR1a knD.
Lemma knR1b_eq : kn_afterL rR1b knD = knR1. Proof. vm_compute. reflexivity. Qed.
Definition logR1 : list sentry := Eval vm_compute in s_log (fst (fst rR1a)).
Lemma logR1b_eq : s_log (fst (fst rR1b)) = logR1. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition srR2_0 : list expr := Eval vm_compute in sr_upd (sr_upd srR1a (ridx 10) (EVar 70)) (ridx 12) (EVar 71).
(* [comment removed for export] *)
Definition SR12 : list expr := Eval vm_compute in sr_upd srR1a (ridx 12) (EVar 71).
Lemma SR12_b : sr_upd srR1b (ridx 12) (EVar 71) = SR12. Proof. vm_compute. reflexivity. Qed.
Lemma SR2_eq : sr_upd SR12 (ridx 10) (EVar 70) = srR2_0. Proof. vm_compute. reflexivity. Qed.
Definition rR2n := Eval vm_compute in runL [true; false; true] (SS 0x2b77c srR2_0 [] knR1 72).
Definition rR2z := Eval vm_compute in runL [true; false; false] (SS 0x2b77c srR2_0 [] knR1 72).
Definition srR2n : list expr := Eval vm_compute in s_regs (fst (fst rR2n)).
Definition srR2z : list expr := Eval vm_compute in s_regs (fst (fst rR2z)).
Definition knR2n : list kentry := Eval vm_compute in kn_afterL rR2n knR1.
Definition knR2z : list kentry := Eval vm_compute in kn_afterL rR2z knR1.
(* [comment removed for export] *)
Definition srR3_0 : list expr := Eval vm_compute in sr_upd srR2z (ridx 10) (ELit 0).
Definition rR3 := Eval vm_compute in runL [] (SS 0x2b77c srR3_0 [] knR2z 72).
Definition srR3 : list expr := Eval vm_compute in s_regs (fst (fst rR3)).
Definition knR3 : list kentry := Eval vm_compute in kn_afterL rR3 knR2z.
(* [comment removed for export] *)
Definition srC2_0 : list expr := Eval vm_compute in sr_after_call_j srR2n (map ridx callee_kept) 72.
Definition rC2r := Eval vm_compute in runL [false] (SS 0x17be4 srC2_0 [] knR2n 104).
Definition rC2g := Eval vm_compute in runL [true] (SS 0x17be4 srC2_0 [] knR2n 104).
Definition srC2r : list expr := Eval vm_compute in s_regs (fst (fst rC2r)).
Definition srC2g : list expr := Eval vm_compute in s_regs (fst (fst rC2g)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma knD_in_R2n : kn_incl knD knR2n = true. Proof. vm_compute. reflexivity. Qed.
Lemma knD_in_R3 : kn_incl knD knR3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pins_C2r : pins_expr_ok srC2r = true. Proof. vm_compute. reflexivity. Qed.
Lemma pins_C2g : pins_expr_ok srC2g = true. Proof. vm_compute. reflexivity. Qed.
Lemma pins_R3 : pins_expr_ok srR3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma covR2z : log_covered [(SA (EVar 0) (-8388608), 8388608%Z)] (s_log (fst (fst rR2z))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma w18R2z : log_w18 (s_log (fst (fst rR2z))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma belowR2z : log_below_b 0 0x63000 (s_log (fst (fst rR2z))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma srR1a_vars : sr_vars_lt 70 srR1a = true. Proof. vm_compute. reflexivity. Qed.
Lemma srR1b_vars : sr_vars_lt 70 srR1b = true. Proof. vm_compute. reflexivity. Qed.
Lemma srR2n_vars : sr_vars_lt 72 srR2n = true. Proof. vm_compute. reflexivity. Qed.
Lemma covR1 : log_covered [(SA (EVar 0) (-8388608), 8388608%Z)] logR1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma w18R1 : log_w18 logR1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma belowR1 : log_below_b 0 0x63000 logR1 = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma knR1_stage_incl : kn_incl knR1 (kn_keep2 knR1 RS_stage []) = true. Proof. vm_compute. reflexivity. Qed.
Lemma knR2n_heap_incl : kn_incl knR2n (kn_keep2 knR2n RS_heap []) = true. Proof. vm_compute. reflexivity. Qed.
Lemma knR1_vars : kn_vars_lt 70 knR1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma knR2n_vars : kn_vars_lt 72 knR2n = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma know_knR1_stage : forall E M M',
  know_ok RSEGS E M knR1 ->
  (forall x : word, ~ (STAGE <= bv_unsigned x < STAGE + 65536)%Z -> M' x = M x) ->
  mem_grows M M' -> know_ok RSEGS E M' knR1.
Proof.
  intros E M M' HK OUT G. apply (know_ok_incl RSEGS E M' knR1 _ knR1_stage_incl).
  apply (know_ok_keep2 RSEGS E M M'); [exact HK | | |].
  - unfold RS_stage, STAGE. repeat constructor; unfold estart; cbn [a_base a_off edenot];
      try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
  - intros x Hx. apply OUT.
    pose proof (Hx (ELit 0) STAGE 65536%Z ltac:(left; reflexivity)) as H1.
    unfold estart in H1. cbn [a_base a_off edenot] in H1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in H1. unfold STAGE in H1 |- *. lia.
  - intros x _ Hm. apply G in Hm. exact Hm.
Qed.

(* [comment removed for export] *)
Lemma know_knR2n_heap : forall E M M',
  know_ok RSEGS E M knR2n ->
  (0x7fff80000000 <= bv_unsigned (ev E 0))%Z ->
  (forall x : word, out_heap (ev E 0) x -> M' x = M x) ->
  mem_grows M M' -> know_ok RSEGS E M' knR2n.
Proof.
  intros E M M' HK Hsp OUT G. apply (know_ok_incl RSEGS E M' knR2n _ knR2n_heap_incl).
  pose proof (u64_range (ev E 0)) as Hr.
  apply (know_ok_keep2 RSEGS E M M'); [exact HK | | |].
  - unfold RS_heap, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI, CSLACK. repeat constructor; unfold estart; cbn [a_base a_off edenot];
      try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
  - intros x Hx. apply OUT.
    pose proof (Hx (ELit 0) HEAP_LO (HEAP_HI - HEAP_LO)%Z ltac:(left; reflexivity)) as H1.
    pose proof (Hx (EVar 0) (-8388608 - CSLACK)%Z CSLACK ltac:(right; left; reflexivity)) as H3.
    pose proof (Hx (ELit 0) LOW_LO (LOW_HI - LOW_LO)%Z ltac:(right; right; left; reflexivity)) as H2.
    unfold estart in H1, H2, H3. cbn [a_base a_off edenot] in H1, H2, H3. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in H1, H2.
    unfold CSLACK in H3. unfold out_heap, CSLACK. split; [lia|split; lia].
  - intros x _ Hm. apply G in Hm. exact Hm.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ReadStep.
  Context {AMB : Amb} {Clg : Ceiling} {AI : AllocSpec LayoutP0} {DK : DriverKit LayoutP0 InitP0}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable mem0 : word -> option byte.
  Variable fs0 : Fs.
  Variable data : list byte.
  Hypothesis Hvsp : valid_sp sp0.
  (* [comment removed for export] *)
  Hypothesis HCEIL : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.
  Hypothesis Hfile : fs_lookup fs0 path = Some data.
  Hypothesis Hplen : (length path <= 4095)%nat.

  Let L : Z := Z.of_nat (length data).

  Record MDok (md : Model) (off : Z) : Prop := MDOK {
    mo_fs  : m_fs md = fs0;
    mo_fd3 : fd_lookup (m_fds md) (Z_to_bv 64 3) = Some (FdFile path (Z_to_bv 64 off));
    mo_fd1 : fd_lookup (m_fds md) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    mo_fd2 : fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2));
    mo_h   : m_halted md = None;
    mo_lz  : m_vm_lazy md = [] }.

  (* [comment removed for export] *)
  Record MDcl (md : Model) : Prop := MDCL {
    mc_fs  : m_fs md = fs0;
    mc_fd1 : fd_lookup (m_fds md) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    mc_fd2 : fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2));
    mc_h   : m_halted md = None;
    mc_lz  : m_vm_lazy md = [] }.

  (* [comment removed for export] *)
  Record buf_ok (k : nat) (len b : Z) (M : word -> option byte) (A : AS) : Prop := BUFOK {
    bo_live : a_live A b = Some (cap k);
    bo_only : forall q, q <> b -> a_live A q = None;
    bo_ds   : a_livebytes A = cap k /\ a_nlive A = 1%Z;   (* [comment removed for export] *)
    bo_data : forall i, (0 <= i < len)%Z -> M (Z_to_bv 64 (b + i)) = Some (nth (Z.to_nat i) data (Z_to_bv 8 0));
    bo_k    : (k <= 10)%nat;
    bo_len  : (0 <= len <= cap k)%Z;
    bo_L    : (len <= L)%Z }.

  (* [comment removed for export] *)
  Record rd_st (k : nat) (len b : Z) (vals : list word) (R : bvmap 5 word) (M : word -> option byte)
         (md : Model) (A : AS) : Prop := RDST {
    rs_base : base_ok sp0 a0s path envv tid vals;
    rs_junk : junk_at vals R;
    rs_pins : pins_main sp0 (p1 sp0 a0s path envv) R;
    rs_know : know_ok RSEGS (ENV a0s path rdraw vals) M knD;
    rs_above : above_sp0 sp0 mem0 M;
    rs_s1 : getr R 9 = Z_to_bv 64 b;
    rs_s3 : getr R 19 = Z_to_bv 64 len;
    rs_s5 : getr R 21 = Z_to_bv 64 (cap k);
    rs_s6 : getr R 22 = Z_to_bv 64 STAGE;
    rs_ainv : ainv A M md;
    rs_mi : Mem.mem_inv RSEGS M;
    rs_buf : buf_ok k len b M A;
    rs_md : MDok md len }.

  (* [comment removed for export] *)
  Record grow_st (k : nat) (b : Z) (vals : list word) (R : bvmap 5 word) (M : word -> option byte)
         (md : Model) (A : AS) : Prop := GROWST {
    gs_base : base_ok sp0 a0s path envv tid vals;
    gs_junk : junk_at vals R;
    gs_pins : pins_main sp0 (p1 sp0 a0s path envv) R;
    gs_know : know_ok RSEGS (ENV a0s path rdraw vals) M knD;
    gs_above : above_sp0 sp0 mem0 M;
    gs_s1 : getr R 9 = Z_to_bv 64 b;
    gs_s3 : getr R 19 = Z_to_bv 64 (cap k);
    gs_s5 : getr R 21 = Z_to_bv 64 (cap k);
    gs_s6 : getr R 22 = Z_to_bv 64 STAGE;
    gs_s7 : getr R 23 = Z_to_bv 64 b;
    gs_ainv : ainv A M md;
    gs_mi : Mem.mem_inv RSEGS M;
    gs_buf : buf_ok k (cap k) b M A;
    gs_md : MDok md (cap k) }.

  (* [comment removed for export] *)
  Record hdr_st (k : nat) (b : Z) (vals : list word) (R : bvmap 5 word) (M : word -> option byte)
         (md : Model) (A : AS) : Prop := HDRST {
    hs_base : base_ok sp0 a0s path envv tid vals;
    hs_junk : junk_at vals R;
    hs_pins : pins_main sp0 (p1 sp0 a0s path envv) R;
    hs_know : know_ok RSEGS (ENV a0s path rdraw vals) M knD;
    hs_above : above_sp0 sp0 mem0 M;
    hs_s1 : getr R 9 = Z_to_bv 64 b;
    hs_s3 : getr R 19 = Z_to_bv 64 L;
    hs_s5 : getr R 21 = Z_to_bv 64 (cap k);
    hs_s6 : getr R 22 = Z_to_bv 64 STAGE;
    hs_s7 : getr R 23 = Z_to_bv 64 0;
    hs_ainv : ainv A M md;
    hs_mi : Mem.mem_inv RSEGS M;
    hs_buf : buf_ok k L b M A;
    hs_md : MDcl md }.

  #[using="L Hplen data path"] Lemma cap_range : forall k, (k <= 10)%nat -> (65536 <= cap k <= 67108864)%Z.
  Proof.
    intros k Hk. unfold cap.
    assert (H1 : (0 < 2 ^ Z.of_nat k)%Z) by (apply Z.pow_pos_nonneg; lia).
    assert (H2 : (2 ^ Z.of_nat k <= 2 ^ 10)%Z) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 10)%Z with 1024%Z in H2. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma u64 : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
  Proof. intros. apply u_small. assumption. Qed.

  Lemma block_mapped : forall A M md b c i, ainv A M md -> a_live A b = Some c -> (0 <= i < c)%Z ->
    M (Z_to_bv 64 (b + i)) <> None.
  Proof. intros A M md b c i AI0 HL Hi. (first [ pose proof ((as_live_ok A M md b c AI0 HL)) as dR_1; dand7 dR_1 as _ _ _ _ _ MP _ | destruct (as_live_ok A M md b c AI0 HL) as (_ & _ & _ & _ & _ & MP & _) ]). apply MP. exact Hi. Qed.

  (* [comment removed for export] *)
  #[using="L Hplen HCEIL data path"] Lemma block_range : forall A M md b c, ainv A M md -> a_live A b = Some c ->
    (0 <= c)%Z /\ (b mod 16 = 0)%Z /\ (4096 <= b /\ (b + c <= LOW_HI \/ HEAP_LO <= b))%Z /\ (b + c <= bv_unsigned sp0 - 8388608)%Z.
  Proof.
    intros A M md b c AI0 HL. (first [ pose proof ((as_live_ok A M md b c AI0 HL)) as dR_2; dand6 dR_2 as N0 AL P1 HI IMG _ | destruct (as_live_ok A M md b c AI0 HL) as (N0 & AL & P1 & HI & IMG & _) ]).
    rewrite HCEIL in HI. cbn [al_image_lo al_image_hi LayoutP0] in IMG. unfold HEAP_LO, LOW_LO, LOW_HI. OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
  Qed.

  #[using="L Hplen HCEIL Hvsp data path sp0"] Lemma block_store_ok : forall A M md b c a n, ainv A M md -> a_live A b = Some c ->
    (b <= a)%Z -> (a + Z.of_nat n <= b + c)%Z ->
    store_ok RSEGS M (Z_to_bv 64 a) n = true.
  Proof.
    intros A M md b c a n AI0 HL Ha Hn. (first [ pose proof ((block_range A M md b c AI0 HL)) as dR_3; dand4 dR_3 as C0 _ LO HI | destruct (block_range A M md b c AI0 HL) as (C0 & _ & LO & HI) ]).
    pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. pose proof (u64_range sp0).
    unfold HEAP_LO, LOW_LO, LOW_HI in *.
    apply store_ok_of_all; [rewrite u64 by lia; lia|]. intros x Hx. rewrite u64 in Hx by lia.
    unfold wview. destruct (M x) eqn:EM; [discriminate|]. exfalso.
    apply (block_mapped A M md b c (bv_unsigned x - b) AI0 HL ltac:(lia)).
    replace (b + (bv_unsigned x - b))%Z with (bv_unsigned x) by lia. rewrite Z_to_bv_bv_unsigned. exact EM.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="L Hplen data path"] Lemma bt_lt0_false : forall z, (0 <= z < 2 ^ 63)%Z -> branch_taken BC_LT (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
  Proof.
    intros z Hz. cbn [branch_taken]. unfold bv_lts, bv_signed. rewrite !u64 by lia.
    rewrite !bv_swrap_small by (unfold bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 64 / 2)%Z with (2 ^ 63)%Z; lia).
    apply Z.ltb_ge. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="L Hplen HCEIL Hvsp data path"] Lemma client_step : forall A M M' md md' b c,
    ainv A M md -> a_live A b = Some c ->
    (forall x : word, ~ (bv_unsigned sp0 - 8388608 <= bv_unsigned x < bv_unsigned sp0)%Z ->
                      ~ (STAGE <= bv_unsigned x < STAGE + 65536)%Z ->
                      ~ (b <= bv_unsigned x < b + c)%Z -> M' x = M x) ->
    mem_grows M M' -> m_vm md' = m_vm md -> m_halted md' = None ->
    Mem.mem_inv RSEGS M -> above_sp0 sp0 mem0 M ->
    ainv A M' md' /\ Mem.mem_inv RSEGS M' /\ above_sp0 sp0 mem0 M'.
  Proof.
    intros A M M' md md' b c AI0 LIVE OUT G VM Hh MI HA.
    pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. pose proof (u64_range sp0).
    (first [ pose proof ((as_live_ok A M md b c AI0 LIVE)) as dR_4; dand7 dR_4 as C0 _ P1 HI LO MP NO | destruct (as_live_ok A M md b c AI0 LIVE) as (C0 & _ & P1 & HI & LO & MP & NO) ]).
    rewrite HCEIL in HI. cbn [al_image_lo al_image_hi LayoutP0] in LO.
    assert (OUTZ : forall a, (0 <= a < 2 ^ 64)%Z ->
              ~ (bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0)%Z -> ~ (STAGE <= a < STAGE + 65536)%Z -> ~ (b <= a < b + c)%Z ->
              M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N1 N2 N3. apply OUT; rewrite u64 by lia; assumption. }
    assert (STG : STAGE = 0x317f9%Z) by reflexivity.
    split; [|split].
    - apply (as_frame A M M' md md' AI0).
      + intros a Ho. pose proof (owned_azone A M md a AI0 Ho) as ZZ. unfold azone, STATICS_LO, STATICS_HI, HEAP_LO, LOW_LO, LOW_HI in ZZ.
        pose proof alloc_ceiling_val.
        apply OUTZ; [lia|lia|lia|]. intros Hin. apply (NO (a - b)%Z ltac:(lia)). replace (b + (a - b))%Z with a by lia. exact Ho.
      + intros a Hs. cbn [al_shared LayoutP0] in Hs. unfold p0_shared in Hs. apply OUTZ; lia.
      + intros p n i HL Hi. (first [ pose proof ((as_live_ok A M md p n AI0 HL)) as dR_5; dand7 dR_5 as _ _ _ _ _ MPp _ | destruct (as_live_ok A M md p n AI0 HL) as (_ & _ & _ & _ & _ & MPp & _) ]). apply G. apply MPp. exact Hi.
      + intros a [Ha Hni] Hm. rewrite HCEIL in Ha. unfold in_image in Hni. cbn [al_image_lo al_image_hi LayoutP0] in Hni.
        destruct (Z_lt_le_dec a b) as [L1|L1]; [rewrite OUTZ in Hm by lia; exact Hm|].
        destruct (Z_lt_le_dec a (b + c)) as [L2|L2]; [|rewrite OUTZ in Hm by lia; exact Hm].
        replace a with (b + (a - b))%Z by lia. apply MP. lia.
      + exact VM.
      + exact Hh.
    - intros x v Hx. destruct (Mem.ro_addr RSEGS x) eqn:RO; [|reflexivity]. exfalso.
      pose proof (proj1 (as_ro_addr_iff (AI:=AI) x) RO) as RA. cbn [al_image_lo al_rw_lo LayoutP0] in RA.
      rewrite OUT in Hx by lia. pose proof (MI x v Hx) as RO'. rewrite RO' in RO. discriminate.
    - intros x Hx. rewrite OUT by lia. apply HA. exact Hx.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="L Hplen data path"] Lemma rebase_AG : forall vals (R' : bvmap 5 word) n, length vals = n -> (NB <= n)%nat ->
    forall i, (i < NB)%nat -> vals_ev (firstn NB vals ++ junk_vals R') i = vals_ev vals i.
  Proof.
    intros vals R' n HL Hn i Hi. unfold vals_ev at 1. rewrite app_nth1 by (rewrite length_firstn, HL; unfold NB in *; lia).
    rewrite nth_firstn. apply Nat.ltb_lt in Hi. rewrite Hi. reflexivity.
  Qed.

  #[using="Hplen Hfile HCEIL Hvsp"] Theorem rd_step : forall k len b vals R M md A T,
    rd_st k len b vals R M md A -> (len < cap k)%Z ->
    let want := Z.min (cap k - len) 65536 in
    let n := Z.min want (L - len) in
    ((0 < n)%Z -> (len + n < cap k)%Z -> forall vals' R' M' md', rd_st k (len + n) b vals' R' M' md' A ->
        realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x17c30) M' (seg_rom RSEGS)) md') T) ->
    ((0 < n)%Z -> (len + n = cap k)%Z -> forall vals' R' M' md', grow_st k b vals' R' M' md' A ->
        realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x17bf8) M' (seg_rom RSEGS)) md') T) ->
    (n = 0%Z -> forall vals' R' M' md', hdr_st k b vals' R' M' md' A ->
        realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x17c60) M' (seg_rom RSEGS)) md') T) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17c30) M (seg_rom RSEGS)) md) T.
  Proof.
    intros k len b vals R M md A T ST Hlt want n KLOOP KGROW KCLOSE.
    destruct ST as [HB HJ HP HK HA S1 S3 S5 S6 AI0 MI BUF MD].
    (first [ pose proof (HB) as dR_6; dand5 dR_6 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]).
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp.
    assert (STG : STAGE = 0x317f9%Z) by reflexivity.
    destruct BUF as [LIVE ONLY DS DATA Hk Hlen HlenL]. destruct MD as [Mfs Mfd3 Mfd1 Mfd2 Mh Mlz].
    pose proof (cap_range k Hk) as Hcap.
    (first [ pose proof ((block_range A M md b (cap k) AI0 LIVE)) as dR_7; dand4 dR_7 as _ Hb16 HbLO HbHI | destruct (block_range A M md b (cap k) AI0 LIVE) as (_ & Hb16 & HbLO & HbHI) ]). unfold HEAP_LO, LOW_LO, LOW_HI in HbLO.
    pose proof (sr_drv_ok sp0 a0s path envv rdraw tid Hvsp vals R HB HJ HP) as HR.
    (* [comment removed for export] *)
    assert (E57 : vals_ev vals 57 = Z_to_bv 64 len) by (rewrite <- S3; exact (HJ 19%nat ltac:(lia))).
    assert (E59 : vals_ev vals 59 = Z_to_bv 64 (cap k)) by (rewrite <- S5; exact (HJ 21%nat ltac:(lia))).
    assert (E47 : vals_ev vals 47 = Z_to_bv 64 b) by (rewrite <- S1; exact (HJ 9%nat ltac:(lia))).
    assert (E60 : vals_ev vals 60 = Z_to_bv 64 STAGE) by (rewrite <- S6; exact (HJ 22%nat ltac:(lia))).
    assert (LINV : edenot (ENV a0s path rdraw vals) (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar 57)) (EVar 59)) = Z_to_bv 64 (cap k - len)).
    { cbn [edenot ev ENV]. rewrite E57, E59. rewrite lin_neg1_val. rewrite u64 by lia. reflexivity. }
    (* [comment removed for export] *)
    assert (CONT : forall (R0 : bvmap 5 word) (M0 : word -> option byte),
      regs_ok (ENV a0s path rdraw (vals ++ [Z_to_bv 64 n; Z_to_bv 64 want])) SR12 R0 ->
      getr R0 12 = Z_to_bv 64 want ->
      know_ok RSEGS (ENV a0s path rdraw vals) M0 knR1 ->
      M0 = mem_denot (ENV a0s path rdraw vals) M logR1 ->
      realizes RSEGS (mkCfg (mkst R0 (Z_to_bv 64 0x2b778) M0 (seg_rom RSEGS)) md) T).
    2:{ (* [comment removed for export] *)
      destruct (Z.ltb_spec (cap k - len) 65536) as [Hw|Hw].
      - run_blockL_keep [true] 70%nat.
        { cbn [sc_denot]. rewrite LINV. apply (bt_ltu_Z _ _ true); [lia|lia|apply Z.ltb_lt; lia]. }
        assert (G12 : getr R0 12 = Z_to_bv 64 want).
        { regv HR (12%bv : reg). rewrite LINV. f_equal. subst want. lia. }
        apply (CONT R0 M0); [| exact G12 | exact HK | exact EQM].
        change SR12 with (sr_upd srR1a (ridx 12) (EVar 71)).
        eapply regs_ok_pin; [apply env_app_regs; [rewrite HL; exact srR1a_vars | exact HR] |].
        rewrite G12. cbn [edenot ev ENV]. replace 71%nat with (length vals + 1)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity.
      - run_blockL_keep [false] 70%nat.
        { cbn [sc_denot]. rewrite LINV. apply (bt_ltu_Z _ _ false); [lia|lia|apply Z.ltb_ge; lia]. }
        assert (G12 : getr R0 12 = Z_to_bv 64 want).
        { regv HR (12%bv : reg). f_equal. subst want. lia. }
        apply (CONT R0 M0); [| exact G12 | rewrite <- knR1b_eq; exact HK | rewrite <- logR1b_eq; exact EQM].
        rewrite <- SR12_b.
        eapply regs_ok_pin; [apply env_app_regs; [rewrite HL; exact srR1b_vars | exact HR] |].
        rewrite G12. cbn [edenot ev ENV]. replace 71%nat with (length vals + 1)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    (* [comment removed for export] *)
    intros R0 M0 HR0 G12 HK0 EQM0.
    set (vals2 := vals ++ [Z_to_bv 64 n; Z_to_bv 64 want]) in *.
    assert (HL2 : length vals2 = 72%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
    assert (AG2 : forall i, (i < 70)%nat -> vals_ev vals2 i = vals_ev vals i).
    { intros i Hi. subst vals2. apply vals_ev_app_l. rewrite HL. exact Hi. }
    assert (E70 : vals_ev vals2 70 = Z_to_bv 64 n).
    { subst vals2. replace 70%nat with (length vals + 0)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (Hwant : (1 <= want <= 65536)%Z) by (subst want; lia).
    assert (Hn : (0 <= n <= want)%Z /\ (n <= L - len)%Z) by (subst n; lia).
    (* [comment removed for export] *)
    assert (RF1 : regions_flat (ENV a0s path rdraw vals) [(SA (EVar 0) (-8388608), 8388608%Z)]).
    { intros r [<-|[]]. unfold flat, estart. cbn [fst snd a_base a_off edenot ev ENV]. rewrite V0. lia. }
    assert (OUT0 : forall x : word, ~ (bv_unsigned sp0 - 8388608 <= bv_unsigned x < bv_unsigned sp0)%Z -> M0 x = M x).
    { intros x Hx. rewrite EQM0. apply (mem_denot_frame _ M _ logR1 x covR1 w18R1 RF1).
      cbn [map outside rdenot fst snd]. unfold in_rng, estart. cbn [a_base a_off edenot ev ENV]. rewrite V0.
      rewrite u64 by lia. split; [lia| exact I]. }
    assert (G0 : mem_grows M M0) by (rewrite EQM0; apply mem_denot_grows).
    assert (HA0 : above_sp0 sp0 mem0 M0).
    { rewrite EQM0. apply (above_sp0_block sp0 a0s path rdraw mem0 Hvsp Hplen vals logR1 M V0 belowR1 HA). }
    (* [comment removed for export] *)
    assert (A11 : getr R0 11 = Z_to_bv 64 STAGE).
    { regv HR0 (11%bv : reg). cbn [edenot ev ENV]. rewrite !AG2 by lia. exact E60. }
    assert (STOK : store_ok RSEGS M0 (getr R0 11) (Z.to_nat want) = true).
    { rewrite A11. apply store_ok_data; unfold STAGE; rewrite u64 by lia; lia. }
    (* [comment removed for export] *)
    eapply (rz_read_file RSEGS R0 (Z_to_bv 64 0x2b778) M0 md ECALLW (Z_to_bv 64 3) path (Z_to_bv 64 len) data want);
      [ vm_compute; reflexivity | apply is_ecall_ECALLW | exact Mh | exact Mlz
      | regv HR0 (17%bv : reg); reflexivity
      | regv HR0 (10%bv : reg); reflexivity
      | rewrite u64 by lia; lia
      | exact Mfd3
      | rewrite Mfs; exact Hfile
      | exact G12
      | lia | unfold MAX_RW_COUNT; lia | lia
      | rewrite A11, u64 by (unfold STAGE; lia); unfold TASK_SIZE, STAGE; lia
      | exact STOK | ].
    cbv zeta. rewrite v_addi_pc4 by lia. change (0x2b778 + 4)%Z with 0x2b77c%Z.
    set (bs := file_read data (Z_to_bv 64 len) (getr R0 12)).
    assert (LBS : length bs = Z.to_nat n).
    { subst bs. rewrite length_file_read, G12. unfold word_to_nat. rewrite !u64 by lia. subst n want. unfold L in *. lia. }
    assert (NBS : forall i, (i < length bs)%nat -> nth i bs (Z_to_bv 8 0) = nth (Z.to_nat len + i) data (Z_to_bv 8 0)).
    { intros i Hi. subst bs. rewrite file_read_unguarded in *. rewrite G12 in *. unfold word_to_nat in *. rewrite !u64 in * by lia.
      rewrite nth_firstn. rewrite length_firstn in Hi.
      destruct (Nat.ltb_spec i (Z.to_nat want)); [| lia]. rewrite nth_skipn. reflexivity. }
    rewrite (len_word_of_nat bs), LBS, Z2Nat.id by lia.
    set (M2 := wbytes M0 (getr R0 11) bs).
    set (md2 := with_fds (fd_insert (m_fds md) (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 len + Z_to_bv 64 n)%bv)) md).
    (* [comment removed for export] *)
    assert (HR2 : regs_ok (ENV a0s path rdraw vals2) srR2_0 (regupd R0 10 (Z_to_bv 64 n))).
    { rewrite <- SR2_eq. apply regs_set_a0; [exact HR0|]. cbn [edenot ev ENV]. exact E70. }
    (* [comment removed for export] *)
    assert (OUT2 : forall x : word, ~ (STAGE <= bv_unsigned x < STAGE + n)%Z -> M2 x = M0 x).
    { intros x Hx. subst M2. apply wbytes_outside; rewrite A11, u64 by (unfold STAGE; lia); rewrite ?LBS; lia. }
    assert (IN2 : forall i, (0 <= i < n)%Z -> M2 (Z_to_bv 64 (STAGE + i)) = Some (nth (Z.to_nat (len + i)) data (Z_to_bv 8 0))).
    { intros i Hi. subst M2. rewrite wbytes_inside by (rewrite A11, ?LBS, !u64 by (unfold STAGE; lia); lia).
      rewrite A11, !u64 by (unfold STAGE; lia). rewrite NBS by (rewrite LBS; lia). f_equal. f_equal. lia. }
    assert (STG2 : rdn RSEGS M2 (Z_to_bv 64 STAGE) (length bs) = Some bs).
    { subst M2. rewrite A11. apply rdn_wbytes_hit. rewrite u64 by (unfold STAGE; lia). rewrite LBS. unfold STAGE. lia. }
    assert (G2 : mem_grows M0 M2) by (subst M2; apply wbytes_grows).
    assert (HK2 : know_ok RSEGS (ENV a0s path rdraw vals2) M2 knR1).
    { subst vals2. apply env_app_know; [rewrite HL; exact knR1_vars|].
      apply (know_knR1_stage _ M0 M2 HK0); [| exact G2]. intros x Hx. apply OUT2. lia. }
    (* [comment removed for export] *)
    assert (W2 : ainv A M2 md2 /\ Mem.mem_inv RSEGS M2 /\ above_sp0 sp0 mem0 M2).
    { refine (client_step A M M2 md md2 b (cap k) AI0 LIVE _ _ _ _ MI HA).
      - intros x N1 N2 N3. rewrite OUT2 by lia. apply OUT0. exact N1.
      - eapply mem_grows_trans; eassumption.
      - reflexivity.
      - subst md2. rewrite with_fds_halted. exact Mh. }
    (first [ dand3 W2 as AI2 MI2 HA2 | destruct W2 as (AI2 & MI2 & HA2) ]).
    assert (BUF2 : buf_ok k len b M2 A).
    { split; try assumption; try lia. intros i Hi.
      rewrite OUT2 by (rewrite u64 by lia; unfold STAGE; lia). rewrite OUT0 by (rewrite u64 by lia; lia). apply DATA. lia. }
    clear HR0 HK0 HR HK.
    destruct (Z.eq_dec n 0) as [N0|N0].
    - (* [comment removed for export] *)
      assert (HEOF : len = L) by (subst n want; lia).
      rename HR2 into HR. rename HK2 into HK.
      run_blockL_keep [true; false; false] 72%nat.
      { cbn [sc_denot edenot ev ENV]. rewrite E70. rewrite bt_ne0_Z by lia. rewrite N0. reflexivity. }
      { cbn [sc_denot edenot ev ENV]. rewrite E70. apply bt_lt0_false. lia. }
      { cbn [sc_denot edenot ev ENV]. rewrite E70. apply (bt_ltu_Z _ _ true); [lia| lia| apply Z.ltb_lt; lia]. }
      rename EQM into EQM3.
      (* [comment removed for export] *)
      assert (RF2 : regions_flat (ENV a0s path rdraw vals2) [(SA (EVar 0) (-8388608), 8388608%Z)]).
      { intros r [<-|[]]. unfold flat, estart. cbn [fst snd a_base a_off edenot ev ENV]. rewrite AG2 by lia. rewrite V0. lia. }
      assert (OUT3 : forall x : word, ~ (bv_unsigned sp0 - 8388608 <= bv_unsigned x < bv_unsigned sp0)%Z -> M1 x = M2 x).
      { intros x Hx. rewrite EQM3. apply (mem_denot_frame _ M2 _ _ x covR2z w18R2z RF2).
        cbn [map outside rdenot fst snd]. unfold in_rng, estart. cbn [a_base a_off edenot ev ENV]. rewrite AG2 by lia. rewrite V0.
        rewrite u64 by lia. split; [lia| exact I]. }
      assert (G3 : mem_grows M2 M1) by (rewrite EQM3; apply mem_denot_grows).
      assert (HA1 : above_sp0 sp0 mem0 M1).
      { rewrite EQM3. apply (above_sp0_block sp0 a0s path rdraw mem0 Hvsp Hplen vals2 _ M2 ltac:(rewrite AG2 by lia; exact V0) belowR2z HA2). }
      (* [comment removed for export] *)
      eapply (rz_close RSEGS R1 (Z_to_bv 64 0x2b778) M1 md2 ECALLW (Z_to_bv 64 3));
        [ vm_compute; reflexivity | apply is_ecall_ECALLW
        | subst md2; rewrite with_fds_halted; exact Mh | subst md2; rewrite with_fds_lazy; exact Mlz
        | regv HR (17%bv : reg); reflexivity
        | regv HR (10%bv : reg); reflexivity
        | rewrite u64 by lia; lia
        | subst md2; rewrite with_fds_fds, fd_lookup_insert_eq; reflexivity | ].
      rewrite v_addi_pc4 by lia. change (0x2b778 + 4)%Z with 0x2b77c%Z.
      set (md3 := with_fds (fd_remove (m_fds md2) (Z_to_bv 64 3)) md2).
      pose proof (regs_set_a0 (ENV a0s path rdraw vals2) _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR3.
      change (sr_upd srR2z (ridx 10) (ELit 0)) with srR3_0 in HR3. clear HR. rename HR3 into HR.
      run_blockL_keep (@nil bool) 72%nat.
      cbn [mem_denot] in EQM. subst M3.
      (* [comment removed for export] *)
      assert (W3 : ainv A M1 md3 /\ Mem.mem_inv RSEGS M1 /\ above_sp0 sp0 mem0 M1).
      { refine (client_step A M2 M1 md2 md3 b (cap k) AI2 LIVE _ G3 _ _ MI2 HA2).
        - intros x N1 N2 N3. apply OUT3. exact N1.
        - reflexivity.
        - subst md3 md2. rewrite !with_fds_halted. exact Mh. }
      (first [ dand3 W3 as AI3 MI3 HA3 | destruct W3 as (AI3 & MI3 & HA3) ]).
      apply (KCLOSE N0 (firstn NB vals2 ++ junk_vals R2) R2 M1 md3).
      pose proof (rebase_AG vals2 R2 72%nat HL2 ltac:(unfold NB; lia)) as AG3.
      assert (AG3' : forall i, (i < NB)%nat -> vals_ev (firstn NB vals2 ++ junk_vals R2) i = vals_ev vals i)
        by (intros i Hi; rewrite AG3 by exact Hi; apply AG2; unfold NB in Hi; lia).
      split.
      + split; [rewrite length_app, junk_vals_length, length_firstn, HL2; reflexivity|].
        rewrite !AG3' by (unfold NB; lia). OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
      + apply junk_at_app. rewrite length_firstn, HL2. reflexivity.
      + apply (pins_of_sr sp0 a0s path envv rdraw Hvsp vals2 R2 srR3); [rewrite AG2 by lia; exact V0 | rewrite AG2 by lia; exact V2 | exact pins_R3 | exact HR].
      + apply (know_ok_agree RSEGS NB (ENV a0s path rdraw vals2)); [apply env_agree_rejunk; rewrite HL2; unfold NB; lia | exact knD_vars |].
        eapply know_ok_incl; [exact knD_in_R3 | exact HK].
      + exact HA3.
      + regv HR (9%bv : reg). cbn [edenot ev ENV]. rewrite AG2 by lia. exact E47.
      + regv HR (19%bv : reg). cbn [edenot ev ENV]. rewrite AG2 by lia. rewrite E57. f_equal. lia.
      + regv HR (21%bv : reg). cbn [edenot ev ENV]. rewrite AG2 by lia. exact E59.
      + regv HR (22%bv : reg). cbn [edenot ev ENV]. rewrite AG2 by lia. exact E60.
      + regv HR (23%bv : reg). cbn [edenot ev ENV]. rewrite E70, N0. reflexivity.
      + exact AI3.
      + exact MI3.
      + destruct BUF2 as [B1 B2 B3 B4 B5 B6 B7]. rewrite <- HEOF. split; try assumption; try lia.
        intros i Hi. rewrite OUT3 by (rewrite u64 by lia; lia). apply B4. lia.
      + subst md3 md2. split.
        * rewrite !with_fds_fs. exact Mfs.
        * rewrite with_fds_fds, fd_lookup_remove_neq, with_fds_fds, fd_lookup_insert_neq; [exact Mfd1| |];
            intros E; apply (f_equal bv_unsigned) in E; rewrite !u64 in E by lia; lia.
        * rewrite with_fds_fds, fd_lookup_remove_neq, with_fds_fds, fd_lookup_insert_neq; [exact Mfd2| |];
            intros E; apply (f_equal bv_unsigned) in E; rewrite !u64 in E by lia; lia.
        * rewrite !with_fds_halted. exact Mh.
        * rewrite !with_fds_lazy. exact Mlz.
    - (* [comment removed for export] *)
      rename HR2 into HR. rename HK2 into HK.
      run_blockL_keep [true; false; true] 72%nat.
      { cbn [sc_denot edenot ev ENV]. rewrite E70. rewrite bt_ne0_Z by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
      { cbn [sc_denot edenot ev ENV]. rewrite E70. apply bt_lt0_false. lia. }
      { cbn [sc_denot edenot ev ENV]. rewrite E70. apply (bt_ltu_Z _ _ true); [lia| lia| apply Z.ltb_lt; lia]. }
      cbn [mem_denot] in EQM. subst M1.
      (* [comment removed for export] *)
      assert (MCH : mcH M2 (Z_to_bv 64 (b + len)) (Z_to_bv 64 STAGE) n bs).
      { split.
        - lia.
        - exact LBS.
        - exact STG2.
        - rewrite LBS. eapply (block_store_ok A M2 md2 b (cap k)); [exact AI2| exact LIVE| lia| lia].
        - rewrite !u64 by lia. lia.
        - rewrite u64 by lia. lia.
        - rewrite u64 by lia. lia. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?RR _ _ _) _) _ => rename RR into R2 end.
      destruct (ref_memcpy M2 (Z_to_bv 64 (b + len)) (Z_to_bv 64 STAGE) n bs (seg_rom RSEGS) MCH R2 (Z_to_bv 64 0x17be4))
        as [R3 [MS KEEPS]].
      { unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
      { regv HR (1%bv : reg). reflexivity. }
      { regv HR (10%bv : reg). cbn [edenot ev ENV]. rewrite !AG2 by lia. rewrite E47, E57, alu_add. unfold v_add.
        rewrite !u64 by lia. reflexivity. }
      { regv HR (11%bv : reg). cbn [edenot ev ENV]. rewrite AG2 by lia. exact E60. }
      { regv HR (12%bv : reg). cbn [edenot ev ENV]. exact E70. }
      replace (Z_to_bv 64 0x2ac54) with (0x2ac54 : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [subst md2; rewrite with_fds_halted; exact Mh | subst md2; rewrite with_fds_lazy; exact Mlz | exact MS |].
      set (M3 := wbytes M2 (Z_to_bv 64 (b + len)) bs) in *.
      (* [comment removed for export] *)
      pose proof (regs_after_keeps vals2 (blobs_ev (blobs0 a0s path rdraw)) srR2n R2 R3 callee_kept
                    ltac:(rewrite HL2; exact srR2n_vars) HR KEEPS callee_kept_no0) as HR3.
      rewrite HL2 in HR3. change (sr_after_call_j srR2n (map ridx callee_kept) 72) with srC2_0 in HR3.
      set (vals3 := vals2 ++ junk_vals R3) in *.
      assert (HL3 : length vals3 = 104%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL2; reflexivity).
      assert (AG3 : forall i, (i < 72)%nat -> vals_ev vals3 i = vals_ev vals2 i) by (intros i Hi; subst vals3; apply vals_ev_app_l; rewrite HL2; exact Hi).
      assert (OUT3 : forall x : word, ~ (b + len <= bv_unsigned x < b + len + n)%Z -> M3 x = M2 x).
      { intros x Hx. subst M3. apply wbytes_outside; rewrite u64, ?LBS by lia; lia. }
      assert (IN3 : forall i, (len <= i < len + n)%Z -> M3 (Z_to_bv 64 (b + i)) = Some (nth (Z.to_nat i) data (Z_to_bv 8 0))).
      { intros i Hi. subst M3. rewrite wbytes_inside by (rewrite ?LBS, !u64 by lia; lia).
        rewrite !u64 by lia. rewrite NBS by (rewrite LBS; lia). f_equal. f_equal. lia. }
      assert (G3 : mem_grows M2 M3) by (subst M3; apply wbytes_grows).
      assert (HK3 : know_ok RSEGS (ENV a0s path rdraw vals3) M3 knR2n).
      { subst vals3. apply env_app_know; [rewrite HL2; exact knR2n_vars|].
        apply (know_knR2n_heap _ M2 M3 HK); [cbn [ev ENV]; rewrite AG2 by lia; rewrite V0; lia | | exact G3].
        intros x [Hx1 [Hx2 Hx3]]. cbn [ev ENV] in Hx2. rewrite AG2 in Hx2 by lia. rewrite V0 in Hx2.
        apply OUT3. unfold HEAP_LO, HEAP_HI, LOW_LO, LOW_HI, CSLACK in Hx1, Hx2, Hx3. lia. }
      clear HK HR. rename HR3 into HR. rename HK3 into HK.
      (* [comment removed for export] *)
      assert (W3 : ainv A M3 md2 /\ Mem.mem_inv RSEGS M3 /\ above_sp0 sp0 mem0 M3).
      { refine (client_step A M2 M3 md2 md2 b (cap k) AI2 LIVE _ G3 _ _ MI2 HA2).
        - intros x N1 N2 N3. apply OUT3. lia.
        - reflexivity.
        - subst md2. rewrite with_fds_halted. exact Mh. }
      (first [ dand3 W3 as AI3 MI3 HA3 | destruct W3 as (AI3 & MI3 & HA3) ]).
      assert (BUF3 : forall i, (0 <= i < len + n)%Z -> M3 (Z_to_bv 64 (b + i)) = Some (nth (Z.to_nat i) data (Z_to_bv 8 0))).
      { intros i Hi. destruct (Z_lt_le_dec i len) as [Hi2|Hi2].
        - rewrite OUT3 by (rewrite u64 by lia; lia). apply (bo_data _ _ _ _ _ BUF2). lia.
        - apply IN3. lia. }
      assert (E70' : vals_ev vals3 70 = Z_to_bv 64 n) by (rewrite AG3 by lia; exact E70).
      assert (AG3' : forall i, (i < 70)%nat -> vals_ev vals3 i = vals_ev vals i) by (intros i Hi; rewrite AG3 by lia; apply AG2; exact Hi).
      (* [comment removed for export] *)
      destruct (Z.eq_dec (len + n) (cap k)) as [FULL|NOTFULL].
      + (* [comment removed for export] *)
        run_blockL_keep [true] 104%nat.
        { cbn [sc_denot edenot ev ENV]. rewrite E70', !AG3' by lia. rewrite E57, E59, alu_add. unfold v_add. rewrite !u64 by lia.
          cbn [branch_taken]. unfold bv_eqb. rewrite !u64 by lia. apply Z.eqb_eq. lia. }
        cbn [mem_denot] in EQM. subst M1.
        apply (KGROW ltac:(lia) FULL (firstn NB vals3 ++ junk_vals R1) R1 M3 md2).
        pose proof (rebase_AG vals3 R1 104%nat HL3 ltac:(unfold NB; lia)) as AG4.
        assert (AG4' : forall i, (i < NB)%nat -> vals_ev (firstn NB vals3 ++ junk_vals R1) i = vals_ev vals i)
          by (intros i Hi; rewrite AG4 by exact Hi; apply AG3'; unfold NB in Hi; lia).
        split.
        * split; [rewrite length_app, junk_vals_length, length_firstn, HL3; reflexivity|].
          rewrite !AG4' by (unfold NB; lia). OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
        * apply junk_at_app. rewrite length_firstn, HL3. reflexivity.
        * apply (pins_of_sr sp0 a0s path envv rdraw Hvsp vals3 R1 srC2g); [rewrite AG3' by lia; exact V0 | rewrite AG3' by lia; exact V2 | exact pins_C2g | exact HR].
        * apply (know_ok_agree RSEGS NB (ENV a0s path rdraw vals3)); [apply env_agree_rejunk; rewrite HL3; unfold NB; lia | exact knD_vars |].
          eapply know_ok_incl; [exact knD_in_R2n | exact HK].
        * exact HA3.
        * regv HR (9%bv : reg). cbn [edenot ev ENV]. rewrite AG3' by lia. exact E47.
        * regv HR (19%bv : reg). cbn [edenot ev ENV]. rewrite E70', AG3' by lia. rewrite E57, alu_add. unfold v_add.
          rewrite !u64 by lia. f_equal. lia.
        * regv HR (21%bv : reg). cbn [edenot ev ENV]. rewrite AG3' by lia. exact E59.
        * regv HR (22%bv : reg). cbn [edenot ev ENV]. rewrite AG3' by lia. exact E60.
        * regv HR (23%bv : reg). cbn [edenot ev ENV]. rewrite AG3' by lia. exact E47.
        * exact AI3.
        * exact MI3.
        * split; try assumption; try lia. rewrite <- FULL. exact BUF3.
        * subst md2. split.
          -- rewrite with_fds_fs. exact Mfs.
          -- rewrite with_fds_fds, fd_lookup_insert_eq. f_equal. f_equal. apply bv_eq.
             rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite <- Z.add_mod by lia. rewrite FULL. reflexivity.
          -- rewrite with_fds_fds, fd_lookup_insert_neq by (intros E; apply (f_equal bv_unsigned) in E; rewrite !u64 in E by lia; lia). exact Mfd1.
          -- rewrite with_fds_fds, fd_lookup_insert_neq by (intros E; apply (f_equal bv_unsigned) in E; rewrite !u64 in E by lia; lia). exact Mfd2.
          -- rewrite with_fds_halted. exact Mh.
          -- rewrite with_fds_lazy. exact Mlz.
      + (* [comment removed for export] *)
        run_blockL_keep [false] 104%nat.
        { cbn [sc_denot edenot ev ENV]. rewrite E70', !AG3' by lia. rewrite E57, E59, alu_add. unfold v_add. rewrite !u64 by lia.
          cbn [branch_taken]. unfold bv_eqb. rewrite !u64 by lia. apply Z.eqb_neq. lia. }
        cbn [mem_denot] in EQM. subst M1.
        apply (KLOOP ltac:(lia) ltac:(lia) (firstn NB vals3 ++ junk_vals R1) R1 M3 md2).
        pose proof (rebase_AG vals3 R1 104%nat HL3 ltac:(unfold NB; lia)) as AG4.
        assert (AG4' : forall i, (i < NB)%nat -> vals_ev (firstn NB vals3 ++ junk_vals R1) i = vals_ev vals i)
          by (intros i Hi; rewrite AG4 by exact Hi; apply AG3'; unfold NB in Hi; lia).
        split.
        * split; [rewrite length_app, junk_vals_length, length_firstn, HL3; reflexivity|].
          rewrite !AG4' by (unfold NB; lia). OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
        * apply junk_at_app. rewrite length_firstn, HL3. reflexivity.
        * apply (pins_of_sr sp0 a0s path envv rdraw Hvsp vals3 R1 srC2r); [rewrite AG3' by lia; exact V0 | rewrite AG3' by lia; exact V2 | exact pins_C2r | exact HR].
        * apply (know_ok_agree RSEGS NB (ENV a0s path rdraw vals3)); [apply env_agree_rejunk; rewrite HL3; unfold NB; lia | exact knD_vars |].
          eapply know_ok_incl; [exact knD_in_R2n | exact HK].
        * exact HA3.
        * regv HR (9%bv : reg). cbn [edenot ev ENV]. rewrite AG3' by lia. exact E47.
        * regv HR (19%bv : reg). cbn [edenot ev ENV]. rewrite E70', AG3' by lia. rewrite E57, alu_add. unfold v_add.
          rewrite !u64 by lia. reflexivity.
        * regv HR (21%bv : reg). cbn [edenot ev ENV]. rewrite AG3' by lia. exact E59.
        * regv HR (22%bv : reg). cbn [edenot ev ENV]. rewrite AG3' by lia. exact E60.
        * exact AI3.
        * exact MI3.
        * split; try assumption; try lia.
        * subst md2. split.
          -- rewrite with_fds_fs. exact Mfs.
          -- rewrite with_fds_fds, fd_lookup_insert_eq. f_equal. f_equal. apply bv_eq.
             rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite <- Z.add_mod by lia. reflexivity.
          -- rewrite with_fds_fds, fd_lookup_insert_neq by (intros E; apply (f_equal bv_unsigned) in E; rewrite !u64 in E by lia; lia). exact Mfd1.
          -- rewrite with_fds_fds, fd_lookup_insert_neq by (intros E; apply (f_equal bv_unsigned) in E; rewrite !u64 in E by lia; lia). exact Mfd2.
          -- rewrite with_fds_halted. exact Mh.
          -- rewrite with_fds_lazy. exact Mlz.
  Qed.
End ReadStep.
End D_Reu44.


Module D_MainM0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.varnish.esi_parse_fuzzer.images Require Import Plain.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk SimInv ShapeAlg Shapi1s Nodes MmapSim AllocSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require AgentLib Frame SymExec SymExec2.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 SymAux LibK2dm RefMocc D_Kn21w Spec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Stmwg D_Manqc.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Alu7n.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Amb OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Shapi1s OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Frame OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymAux OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Kn21w OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Spec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Stmwg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u.D_MainA OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Alu7n OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Dr084.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0 DriverKit.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Section MemInv.
  Context {Clg : Ceiling} {AI : AllocSpec LayoutP0}.
  Lemma mem_inv_of_kimg : forall E M kn i lo hi,
    know_ok RSEGS E M kn -> nth_error kn i = Some (KImg lo hi) -> (lo <= 0x10000)%Z -> (0x30000 <= hi)%Z ->
    Mem.mem_inv RSEGS M.
  Proof.
    intros E M kn i lo hi HK Hn Hlo Hhi a b Hab.
    (first [ pose proof ((know_nth RSEGS E M kn i _ HK Hn)) as dR_1; dand3 dR_1 as _ _ NONE | destruct (know_nth RSEGS E M kn i _ HK Hn) as (_ & _ & NONE) ]).
    destruct (Mem.ro_addr RSEGS a) eqn:RO; [|reflexivity]. exfalso.
    pose proof (proj1 (as_ro_addr_iff (AI:=AI) a) RO) as RA. cbn [al_image_lo al_rw_lo LayoutP0] in RA.
    pose proof (NONE (bv_unsigned a) ltac:(lia)) as N. rewrite Z_to_bv_bv_unsigned in N. congruence.
  Qed.
End MemInv.

Lemma knBx_img : nth_error knBx 50 = Some (KImg 0x10000 0x317b0). Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)

Section M0.
  Context {AMB : Amb} {Clg : Ceiling} {AI : AllocSpec LayoutP0} {DK : DriverKit LayoutP0 InitP0}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable mem0 : word -> option byte.
  Variables brk mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable fd3 : FdEntry.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  (* [comment removed for export] *)
  Hypothesis HCEIL : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.

  Let MD1 := model1g sp0 tid brk mbase fs0 stdin0 fd3.

  (* [comment removed for export] *)
  Definition post_M0 (K : TSet) : Prop :=
    forall vals R M md A (b : Z),
      base_ok sp0 a0s path envv tid vals -> junk_at vals R ->
      pins_main sp0 (p1 sp0 a0s path envv) R ->
      know_ok RSEGS (ENV a0s path rdraw vals) M knD ->
      getr R 10 = Z_to_bv 64 b -> b <> 0%Z -> getr R 21 = Z_to_bv 64 65536 ->
      ainv A M md -> Mem.mem_inv RSEGS M -> md_frame MD1 md ->
      a_livebytes A = 65536%Z -> a_nlive A = 1%Z -> a_live A b = Some 65536%Z -> (forall q, q <> b -> a_live A q = None) ->
      above_sp0 sp0 mem0 M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17bb8) M (seg_rom RSEGS)) md) K.

  (* [comment removed for export] *)
  Definition PXI (M : word -> option byte) : Prop := init_ok LayoutP0 InitP0 (bv_unsigned sp0) M MD1.

  Theorem main_M0 : forall K,
    post_M0 K ->
    after_open_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 PXI fd3 K.
  Proof.
    intros K PK vals R M HL P0 P1 P2 P5 HR HK HA IO. unfold PXI in IO.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp.
    assert (HKx : know_ok RSEGS (ENV a0s path rdraw vals) M knBx).
    { unfold knBx. apply know_ok_app; [exact HK|].
      eapply (know_ok_kimg_pieces RSEGS _ M knB STATICS_LO HEAP_LO); [exact HK | exact knB_has_img |].
      constructor; [| constructor]. cbn [fst snd]. unfold ALLOC_STATICS_HI, STATICS_LO, STATICS_HI, HEAP_LO. lia. }
    assert (MI : Mem.mem_inv RSEGS M) by (eapply (mem_inv_of_kimg _ M knBx 50); [exact HKx | exact knBx_img | lia | lia]).
    assert (CH : callH vals (blobs_ev (blobs0 a0s path rdraw)) srB knBx 65536 (-128) 0x17bb8).
    { split; rewrite ?HL, ?P0; try reflexivity; try lia.
      exists 21%nat. reflexivity. }
    change (model1g sp0 tid brk mbase fs0 stdin0 fd3) with MD1.
    eapply (W_malloc_first vals (blobs_ev (blobs0 a0s path rdraw)) srB knBx R M MD1 (bv_unsigned sp0) 65536 (-128) 0x17bb8
              K HR HKx CH IO ltac:(rewrite P0; lia) MI ltac:(lia)).
    - (* [comment removed for export] *)
      intros R' M' md' A' b Hb Hv10 HR' HK' AI' MI' MF LIVE NONE LB' NL' FR.
      apply (PK (vals ++ junk_vals R') R' M' md' A' b).
      + OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try (rewrite vals_ev_app_l by (rewrite HL; lia); assumption).
        rewrite length_app, junk_vals_length, HL. reflexivity.
      + apply junk_at_app. exact HL.
      + apply (pins_of_sr_drv sp0 a0s path envv rdraw tid Hvsp (vals ++ junk_vals R') R').
        * OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try (rewrite vals_ev_app_l by (rewrite HL; lia); assumption).
          rewrite length_app, junk_vals_length, HL. reflexivity.
        * (* [comment removed for export] *)
          rewrite HL in HR'. eapply (regs_ok_junkify a0s path rdraw (vals ++ junk_vals R') R' _ sr_drv);
            [apply junk_at_app; exact HL | exact HR' | vm_compute; reflexivity].
      + lazymatch goal with |- know_ok _ ?EE ?MM knD =>
          change (know_ok RSEGS EE MM (kn_keep2 knBx (RS_call (-128) MALLOC_STACK) VICT ++ [kwr_data])) end.
        apply know_ok_app; [exact HK' | constructor; [apply kwr_data_ok | constructor]].
      + rewrite <- Hv10. symmetry. rewrite HL. exact (junk_at_app vals R' HL 10%nat ltac:(lia)).
      + exact Hb.
      + rewrite HL in HR'. regv HR' (21%bv : reg). reflexivity.
      + exact AI'.
      + exact MI'.
      + exact MF.
      + exact LB'.
      + exact NL'.
      + exact LIVE.
      + exact NONE.
      + (* [comment removed for export] *)
        intros x Hx. rewrite <- (HA x Hx).
        pose proof FR as (F1 & _). rewrite <- (Z_to_bv_bv_unsigned 64 x). pose proof (u64_range x).
        apply F1; try lia.
        * intros Hs. cbn [al_static LayoutP0] in Hs. unfold p0_static in Hs. lia.
        * intros Ho. destruct (owned_azone A' M' md' _ AI' Ho) as [Z1|[Z2|Z3]]; unfold STATICS_LO, STATICS_HI, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI in *; lia.
        * unfold MALLOC_STACK. rewrite P0. lia.
        * unfold al_errno. cbn [al_tp LayoutP0]. rewrite u_small by lia. lia.
        * intros Hv. exact Hv.
        * intros [_ Hr]. (first [ pose proof ((as_live_ok A' M' md' b 65536 AI' LIVE)) as dR_3; dand5 dR_3 as _ _ _ HI _ | destruct (as_live_ok A' M' md' b 65536 AI' LIVE) as (_ & _ & _ & HI & _) ]).
          rewrite HCEIL in HI. lia.
  Qed.
End M0.
End D_MainM0.


Module D_MkStep.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.varnish.esi_parse_fuzzer.images Require Import Plain.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk SimInv ShapeAlg Shapi1s Nodes MmapSim AllocSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require AgentLib Frame SymExec SymExec2.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 SymAux LibK2dm RefMocc D_Kn21w MemSplit Spec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require RefNodes RefPl89 D_Stmwg D_Manqc.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Alu7n D_Wamxh.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Me92w.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Opzpl.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Amb OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Shapi1s OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Frame OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymAux OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Kn21w OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MemSplit OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Spec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefNodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefPl89 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Stmwg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u.D_MainA OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Alu7n OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Wamxh OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Dr084 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_Reu44 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Me92w OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Opzpl.D_Memcpy OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0 DriverKit.
From stdpp Require Import base list.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaMunch.
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); timeout 8 (Zify.zify; xlia zchecker).   (* timeout-ok: fast tier: hot2_mid's caller catches its failure and runs zify; xlia without it *)
Local Ltac hot_lia_prev := first [ OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dl_first | tryif OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then first [ hot2_mid | Zify.zify; xlia zchecker ] else first [ solve [OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Zify.zify; xlia zchecker] | hot2_mid | Zify.zify; xlia zchecker ] ].
Local Ltac hot_lia_rest := first [ OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
Local Ltac lia ::= first [ solve [ OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.hplen_pre; hot_lia_rest ] | hot_lia_rest ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rK1 := Eval vm_compute in runL [false] (SS 0x17bf8 sr_drv [] knD 70).
Definition srK1 : list expr := Eval vm_compute in s_regs (fst (fst rK1)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition srK2_0 : list expr := Eval vm_compute in sr_post srK1 70.
Definition rK2 := Eval vm_compute in runL [false; false] (SS 0x17c0c srK2_0 [] knD 102).
Definition srK2 : list expr := Eval vm_compute in s_regs (fst (fst rK2)).
(* [comment removed for export] *)
Definition srK3_0 : list expr := Eval vm_compute in sr_after_call_j srK2 (map ridx callee_kept) 102.
Definition rK3 := Eval vm_compute in runL [] (SS 0x17c28 srK3_0 [] knD 134).
Definition srK3 : list expr := Eval vm_compute in s_regs (fst (fst rK3)).
(* [comment removed for export] *)
Definition srK4 : list expr := Eval vm_compute in sr_post srK3 134.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pins_K4 : pins_expr_ok srK4 = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma knD_vars102 : kn_vars_lt 102 knD = true. Proof. vm_compute. reflexivity. Qed.
Lemma srK2_vars : sr_vars_lt 102 srK2 = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)


Section MkStep.
  Context {AMB : Amb} {Clg : Ceiling} {AI : AllocSpec LayoutP0} {DK : DriverKit LayoutP0 InitP0}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable mem0 : word -> option byte.
  Variable fs0 : Fs.
  Variable data : list byte.
  Hypothesis Hvsp : valid_sp sp0.
  (* [comment removed for export] *)
  Hypothesis HCEIL : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hfile : fs_lookup fs0 path = Some data.
  Hypothesis Hplen : (length path <= 4095)%nat.

  Let L : Z := Z.of_nat (length data).

  (* [comment removed for export] *)
  #[using="L Hplen HCEIL Hvsp data path"] Lemma above_acall : forall (O O' : Z -> Prop) spk win victim newb M M',
    (forall a, O a -> azone a) -> (forall a, O' a -> azone a) ->
    (forall a, victim a -> azone a) -> (forall a, newb a -> azone a) ->
    frame_ok LayoutP0 O O' (bv_unsigned sp0 + spk) win victim newb M M' ->
    (spk <= 0)%Z -> above_sp0 sp0 mem0 M -> above_sp0 sp0 mem0 M'.
  Proof.
    intros O O' spk win victim newb M M' HO HO' HV HN FR Hspk HA x Hx.
    pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. pose proof (u64_range x). pose proof (u64_range sp0).
    pose proof alloc_ceiling_val as CV.
    rewrite <- (HA x Hx). pose proof FR as (F1 & _). rewrite <- (Z_to_bv_bv_unsigned 64 x). apply F1; try lia.
    - intros Ho. pose proof (HO _ Ho) as ZZ; unfold azone, STATICS_LO, STATICS_HI, HEAP_LO, LOW_LO, LOW_HI in *; lia.
    - intros Ho. pose proof (HO' _ Ho) as ZZ; unfold azone, STATICS_LO, STATICS_HI, HEAP_LO, LOW_LO, LOW_HI in *; lia.
    - unfold al_errno. cbn [al_tp LayoutP0]. rewrite u_small by lia. lia.
    - intros Hv. pose proof (HV _ Hv) as ZZ; unfold azone, STATICS_LO, STATICS_HI, HEAP_LO, LOW_LO, LOW_HI in *; lia.
    - intros Hn. pose proof (HN _ Hn) as ZZ; unfold azone, STATICS_LO, STATICS_HI, HEAP_LO, LOW_LO, LOW_HI in *; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="L Hplen HCEIL Hvsp data path"] Lemma block_acall : forall A A' M M' md md' spk win victim newb p c,
    ainv A M md -> ainv A' M' md' -> a_live A p = Some c ->
    frame_ok LayoutP0 (owned A) (owned A') (bv_unsigned sp0 + spk) win victim newb M M' ->
    (bv_unsigned sp0 - 8388608 <= bv_unsigned sp0 + spk - win)%Z ->
    (forall i, (0 <= i < c)%Z -> ~ victim (p + i)%Z) -> (forall i, (0 <= i < c)%Z -> ~ newb (p + i)%Z) ->
    forall i, (0 <= i < c)%Z -> M' (Z_to_bv 64 (p + i)%Z) = M (Z_to_bv 64 (p + i)%Z).
  Proof.
    intros A A' M M' md md' spk win victim newb p c AI0 AI1 LIVE FR Hspk NV NN i Hi.
    pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. pose proof (u64_range sp0).
    (first [ pose proof ((as_live_ok A M md p c AI0 LIVE)) as dR_1; dand7 dR_1 as C0 _ P1 HI LO MP NO | destruct (as_live_ok A M md p c AI0 LIVE) as (C0 & _ & P1 & HI & LO & MP & NO) ]).
    rewrite HCEIL in HI. cbn [al_image_lo al_image_hi LayoutP0] in LO.
    (first [ pose proof (FR) as dR_2; dand7 dR_2 as F1 F2 F3 F4 F5 F6 F7 | pose proof FR as (F1 & F2 & F3 & F4 & F5 & F6 & F7) ]).
    apply F1.
    - lia.
    - apply NO. exact Hi.
    - intros Ho'. destruct (F5 (p + i)%Z ltac:(lia) Ho') as [Ho|[Hv|[Hn _]]]; [exact (NO i Hi Ho)| exact (NV i Hi Hv)| exact (MP i Hi Hn)].
    - lia.
    - unfold al_errno. cbn [al_tp LayoutP0]. rewrite u_small by lia. lia.
    - apply NV. exact Hi.
    - apply NN. exact Hi.
  Qed.

  Lemma u64 : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
  Proof. intros. apply u_small. assumption. Qed.

  #[using="L Hplen HCEIL Hvsp"] Theorem mk_step : forall k b vals R M md A T,
    grow_st sp0 a0s path envv rdraw tid mem0 fs0 data k b vals R M md A -> (k < 10)%nat ->
    (forall vals' R' M' md' A' b', rd_st sp0 a0s path envv rdraw tid mem0 fs0 data (S k) (cap k) b' vals' R' M' md' A' ->
        realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x17c30) M' (seg_rom RSEGS)) md') T) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17bf8) M (seg_rom RSEGS)) md) T.
  Proof.
    intros k b vals R M md A T ST Hk KCORE.
    destruct ST as [HB HJ HP HK HA S1 S3 S5 S6 S7 AI0 MI BUF MD].
    (first [ pose proof (HB) as dR_3; dand5 dR_3 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]).
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp. pose proof alloc_ceiling_val as CV.
    assert (STG : STAGE = 0x317f9%Z) by reflexivity.
    pose proof BUF as [LIVE ONLY DS DATA Hk10 Hlen2 HlenL]. pose proof MD as [Mfs Mfd3 Mfd1 Mfd2 Mh Mlz].
    pose proof (cap_range path data Hplen k Hk10) as Hcap. pose proof (cap_range path data Hplen (S k) ltac:(lia)) as Hcap2.
    assert (CAP2 : cap (S k) = (2 * cap k)%Z).
    { unfold cap. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. }
    assert (CAPhi : (cap k <= 2 ^ 25)%Z).
    { unfold cap. assert (2 ^ Z.of_nat k <= 2 ^ 9)%Z by (apply Z.pow_le_mono_r; lia). change (2 ^ 9)%Z with 512%Z in H. lia. }
    (first [ pose proof ((block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE)) as dR_4; dand4 dR_4 as _ Hb16 HbLO HbHI | destruct (block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE) as (_ & Hb16 & HbLO & HbHI) ]). unfold HEAP_LO, LOW_LO, LOW_HI in HbLO.
    pose proof (sr_drv_ok sp0 a0s path envv rdraw tid Hvsp vals R HB HJ HP) as HR.
    assert (E57 : vals_ev vals 57 = Z_to_bv 64 (cap k)) by (rewrite <- S3; exact (HJ 19%nat ltac:(lia))).
    assert (E59 : vals_ev vals 59 = Z_to_bv 64 (cap k)) by (rewrite <- S5; exact (HJ 21%nat ltac:(lia))).
    assert (E47 : vals_ev vals 47 = Z_to_bv 64 b) by (rewrite <- S1; exact (HJ 9%nat ltac:(lia))).
    assert (E60 : vals_ev vals 60 = Z_to_bv 64 STAGE) by (rewrite <- S6; exact (HJ 22%nat ltac:(lia))).
    assert (E61 : vals_ev vals 61 = Z_to_bv 64 b) by (rewrite <- S7; exact (HJ 23%nat ltac:(lia))).
    assert (A0V : edenot (ENV a0s path rdraw vals) (EMd M_MUL (ELit 2) (EVar 57)) = Z_to_bv 64 (cap (S k))).
    { apply bv_eq. cbn [edenot ev ENV]. rewrite E57, u_mul64, !u64 by lia. rewrite CAP2, Z.mod_small; lia. }
    clear HJ HP.
    (* [comment removed for export] *)
    run_blockL_keep [false] 70%nat.
    { cbn [sc_denot edenot ev ENV]. rewrite E57.
      replace (alu64 ALU_SRL (Z_to_bv 64 (cap k)) (Z_to_bv 64 26)) with (Z_to_bv 64 0).
      2:{ apply bv_eq. rewrite u_srl64, !u64 by lia. change (26 mod 64)%Z with 26%Z. rewrite Z.div_small; [reflexivity|].
          change (2 ^ 26)%Z with 67108864%Z. lia. }
      rewrite bt_ne0_Z by lia. reflexivity. }
    cbn [mem_denot] in EQM. subst M0.
    assert (CH : callH vals (blobs_ev (blobs0 a0s path rdraw)) srK1 knD (cap (S k)) (-128) 0x17c0c).
    { split; rewrite ?HL, ?V0; try reflexivity; try lia; [exact A0V | exists knD_iw; exact knD_win]. }
    destruct DS as [DSlb DSnl].
    apply (W_malloc_nf vals (blobs_ev (blobs0 a0s path rdraw)) srK1 knD R0 M md A (cap (S k)) (-128) 0x17c0c
             T HR HK CH AI0 (ex_intro _ b (ex_intro _ (cap k) LIVE)) MI ltac:(lia)
             ltac:(rewrite NREQ_CAP_eq; lia) ltac:(rewrite LIVE_MAX_eq, DSlb; lia) ltac:(rewrite NLIVE_MAX_eq, DSnl; lia)).
    - (* [comment removed for export] *)
      clear HR HK. intros R1 M1 md1 A1 r Hr Hv80 HR HK1 AI1 MI1 MF1 NONE1 LIVE1 OTHER1 LB1 NL1 FR1.
      pose proof (know_knD_main_call _ M1 kwr_data_ok HK1) as HK. clear HK1.
      assert (Hh1 : m_halted md1 = None) by (destruct (as_lazy_nil A1 M1 md1 AI1) as [_ X]; exact X).
      assert (Hl1 : m_vm_lazy md1 = []) by (destruct (as_lazy_nil A1 M1 md1 AI1) as [X _]; exact X).
      rewrite HL in HR, Hv80. change (sr_post srK1 70) with srK2_0 in HR. change (70 + 10)%nat with 80%nat in Hv80.
      set (vals1 := vals ++ junk_vals R1) in *.
      assert (HL1 : length vals1 = 102%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (AG1 : forall i, (i < 70)%nat -> vals_ev vals1 i = vals_ev vals i) by (intros i Hi; subst vals1; apply vals_ev_app_l; rewrite HL; exact Hi).
      (first [ pose proof ((block_range sp0 path data HCEIL Hplen A1 M1 md1 r (cap (S k)) AI1 LIVE1)) as dR_6; dand4 dR_6 as _ Hr16 HrLO HrHI | destruct (block_range sp0 path data HCEIL Hplen A1 M1 md1 r (cap (S k)) AI1 LIVE1) as (_ & Hr16 & HrLO & HrHI) ]). unfold HEAP_LO, LOW_LO, LOW_HI in HrLO.
      assert (LIVEb1 : a_live A1 b = Some (cap k)) by (rewrite (OTHER1 b) by (intros ->; rewrite LIVE in NONE1; discriminate); exact LIVE).
      assert (Hrb : r <> b) by (intros ->; rewrite LIVE in NONE1; discriminate).
      pose proof (as_live_disjoint A1 M1 md1 b (cap k) r (cap (S k)) AI1 LIVEb1 LIVE1 ltac:(congruence)) as DISJ.
      (* [comment removed for export] *)
      assert (DATA1 : forall i, (0 <= i < cap k)%Z -> M1 (Z_to_bv 64 (b + i)) = Some (nth (Z.to_nat i) data (Z_to_bv 8 0))).
      { intros i Hi. rewrite <- (DATA i Hi).
        apply (block_acall A A1 M M1 md md1 (-128) MALLOC_STACK nowhere (blk r (cap (S k))) b (cap k) AI0 AI1 LIVE);
          [rewrite V0 in FR1; exact FR1 | unfold MALLOC_STACK; lia | intros j Hj Hv; exact Hv | | lia].
        intros j Hj [_ Hin]. lia. }
      assert (HA1 : above_sp0 sp0 mem0 M1).
      { rewrite V0 in FR1.
        apply (above_acall (owned A) (owned A1) (-128) MALLOC_STACK nowhere (blk r (cap (S k))) M M1); try assumption; try lia.
        - intros a Ho. exact (owned_azone A M md a AI0 Ho).
        - intros a Ho. exact (owned_azone A1 M1 md1 a AI1 Ho).
        - intros a Hv. destruct Hv.
        - intros a [_ Ha]. replace a with (r + (a - r))%Z by lia. eapply (live_azone A1 M1 md1 r); [exact AI1| exact LIVE1| lia]. }
      (* [comment removed for export] *)
      run_blockL_keep [false; false] 102%nat.
      { cbn [sc_denot edenot ev ENV]. rewrite AG1 by lia. rewrite E57, bt_eq0_Z by lia. apply Z.eqb_neq. lia. }
      { cbn [sc_denot edenot ev ENV]. rewrite Hv80, bt_eq0_Z by lia. apply Z.eqb_neq. lia. }
      cbn [mem_denot] in EQM. subst M0.
      (* [comment removed for export] *)
      set (bs := firstn (Z.to_nat (cap k)) data).
      assert (LBS : length bs = Z.to_nat (cap k)) by (subst bs; rewrite length_firstn; unfold L in HlenL; lia).
      assert (MCH : mcH M1 (Z_to_bv 64 r) (Z_to_bv 64 b) (cap k) bs).
      { split.
        - lia.
        - exact LBS.
        - apply rdn_pointwise; [reflexivity | rewrite u64, LBS by lia; lia |].
          intros j Hj. rewrite u64 by lia. rewrite LBS in Hj. rewrite (DATA1 (Z.of_nat j)) by lia.
          subst bs. rewrite nth_firstn, Nat2Z.id. apply Nat.ltb_lt in Hj. rewrite Hj. reflexivity.
        - rewrite LBS. eapply (block_store_ok sp0 path data Hvsp HCEIL Hplen A1 M1 md1 r (cap (S k))); [exact AI1| exact LIVE1| lia| lia].
        - rewrite !u64 by lia. lia.
        - rewrite u64 by lia. lia.
        - rewrite u64 by lia. lia. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?RR _ _ _) _) _ => rename RR into R2 end.
      destruct (ref_memcpy M1 (Z_to_bv 64 r) (Z_to_bv 64 b) (cap k) bs (seg_rom RSEGS) MCH R2 (Z_to_bv 64 0x17c28))
        as [R3 [MS KEEPS]].
      { unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
      { regv HR (1%bv : reg). reflexivity. }
      { regv HR (10%bv : reg). cbn [edenot ev ENV]. exact Hv80. }
      { regv HR (11%bv : reg). cbn [edenot ev ENV]. rewrite AG1 by lia. exact E61. }
      { regv HR (12%bv : reg). cbn [edenot ev ENV]. rewrite AG1 by lia. exact E57. }
      replace (Z_to_bv 64 0x2ac54) with (0x2ac54 : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [exact Hh1 | exact Hl1 | exact MS |].
      set (M3 := wbytes M1 (Z_to_bv 64 r) bs) in *.
      (* [comment removed for export] *)
      pose proof (regs_after_keeps vals1 (blobs_ev (blobs0 a0s path rdraw)) srK2 R2 R3 callee_kept
                    ltac:(rewrite HL1; exact srK2_vars) HR KEEPS callee_kept_no0) as HR3.
      rewrite HL1 in HR3. change (sr_after_call_j srK2 (map ridx callee_kept) 102) with srK3_0 in HR3.
      set (vals2 := vals1 ++ junk_vals R3) in *.
      assert (HL2 : length vals2 = 134%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
      assert (AG2 : forall i, (i < 102)%nat -> vals_ev vals2 i = vals_ev vals1 i) by (intros i Hi; subst vals2; apply vals_ev_app_l; rewrite HL1; exact Hi).
      assert (OUT3 : forall x : word, ~ (r <= bv_unsigned x < r + cap k)%Z -> M3 x = M1 x).
      { intros x Hx. subst M3. apply wbytes_outside; rewrite u64, ?LBS by lia; lia. }
      assert (IN3 : forall i, (0 <= i < cap k)%Z -> M3 (Z_to_bv 64 (r + i)) = Some (nth (Z.to_nat i) data (Z_to_bv 8 0))).
      { intros i Hi. subst M3. rewrite wbytes_inside by (rewrite ?LBS, !u64 by lia; lia). rewrite !u64 by lia.
        subst bs. rewrite nth_firstn. replace (Z.to_nat (r + i - r)) with (Z.to_nat i) by lia.
        destruct (Nat.ltb_spec (Z.to_nat i) (Z.to_nat (cap k))); [reflexivity | lia]. }
      assert (G3 : mem_grows M1 M3) by (subst M3; apply wbytes_grows).
      assert (HK3 : know_ok RSEGS (ENV a0s path rdraw vals2) M3 knD).
      { subst vals2. apply env_app_know; [rewrite HL1; exact knD_vars102 |].
        apply (know_knD_heap _ M1 M3 HK); [cbn [ev ENV]; rewrite AG1 by lia; rewrite V0; lia | | exact G3].
        intros x [Hx1 [Hx2 Hx3]]. cbn [ev ENV] in Hx2. rewrite AG1 in Hx2 by lia. rewrite V0 in Hx2.
        apply OUT3. unfold HEAP_LO, HEAP_HI, LOW_LO, LOW_HI, CSLACK in Hx1, Hx2, Hx3. lia. }
      assert (W3 : ainv A1 M3 md1 /\ Mem.mem_inv RSEGS M3 /\ above_sp0 sp0 mem0 M3).
      { refine (client_step sp0 path mem0 data Hvsp HCEIL Hplen A1 M1 M3 md1 md1 r (cap (S k)) AI1 LIVE1 _ G3 eq_refl Hh1 MI1 HA1).
        intros x N1 N2 N3. apply OUT3. lia. }
      (first [ dand3 W3 as AI3 MI3 HA3 | destruct W3 as (AI3 & MI3 & HA3) ]).
      clear HR HK. rename HR3 into HR. rename HK3 into HK.
      (* [comment removed for export] *)
      run_blockL_keep (@nil bool) 134%nat.
      cbn [mem_denot] in EQM. subst M0.
      assert (CH2 : callH vals2 (blobs_ev (blobs0 a0s path rdraw)) srK3 knD b (-128) 0x17c30).
      { split; rewrite ?HL2; try reflexivity; try lia.
        - change (sr_get srK3 10) with (EVar 61). cbn [edenot ev]. rewrite AG2, AG1 by lia. exact E61.
        - rewrite AG2, AG1 by lia. rewrite V0. exact SPal.
        - rewrite AG2, AG1 by lia. rewrite V0. lia.
        - rewrite AG2, AG1 by lia. rewrite V0. lia.
        - exists knD_iw. exact knD_win. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?RR _ _ _) _) _ => rename RR into R4a end.
      change (regs_ok (ENV a0s path rdraw vals2) srK3 R4a) in HR.
      apply (W_free_as vals2 (blobs_ev (blobs0 a0s path rdraw)) srK3 knD R4a M3 md1 A1 b (cap k) (-128) 0x17c30
               T HR HK CH2 AI3 (or_intror LIVEb1) MI3).
      clear HR HK. intros R5 M5 md5 A5 HR HK5 AI5 MI5 MF5 GONE5 OTHER5 LB5 NL5 FR5.
      pose proof (know_knD_main_call _ M5 kwr_data_ok HK5) as HK. clear HK5.
      assert (Hh5 : m_halted md5 = None) by (destruct (as_lazy_nil A5 M5 md5 AI5) as [_ X]; exact X).
      assert (Hl5 : m_vm_lazy md5 = []) by (destruct (as_lazy_nil A5 M5 md5 AI5) as [X _]; exact X).
      rewrite HL2 in HR. change (sr_post srK3 134) with srK4 in HR.
      rewrite AG2, AG1, V0 in FR5 by lia.
      (* [comment removed for export] *)
      assert (DATA5 : forall i, (0 <= i < cap k)%Z -> M5 (Z_to_bv 64 (r + i)) = Some (nth (Z.to_nat i) data (Z_to_bv 8 0))).
      { intros i Hi. rewrite <- (IN3 i Hi).
        apply (block_acall A1 A5 M3 M5 md1 md5 (-128) FREE_STACK (blk b (cap k)) nowhere r (cap (S k)) AI3 AI5 LIVE1 FR5);
          [unfold FREE_STACK; lia | | intros j Hj Hv; exact Hv | lia].
        intros j Hj [_ Hin]. lia. }
      assert (HA5 : above_sp0 sp0 mem0 M5).
      { apply (above_acall (owned A1) (owned A5) (-128) FREE_STACK (blk b (cap k)) nowhere M3 M5); try assumption; try lia.
        - intros a Ho. exact (owned_azone A1 M3 md1 a AI3 Ho).
        - intros a Ho. exact (owned_azone A5 M5 md5 a AI5 Ho).
        - intros a [_ Ha]. replace a with (b + (a - b))%Z by lia. eapply (live_azone A1 M3 md1 b); [exact AI3| exact LIVEb1| lia].
        - intros a Hv. destruct Hv. }
      set (vals3 := vals2 ++ junk_vals R5) in *.
      assert (HL3 : length vals3 = 166%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL2; reflexivity).
      assert (AG3 : forall i, (i < 134)%nat -> vals_ev vals3 i = vals_ev vals2 i) by (intros i Hi; subst vals3; apply vals_ev_app_l; rewrite HL2; exact Hi).
      (* [comment removed for export] *)
      apply (KCORE (firstn NB vals3 ++ junk_vals R5) R5 M5 md5 A5 r).
      assert (AG4 : forall i, (i < NB)%nat -> vals_ev (firstn NB vals3 ++ junk_vals R5) i = vals_ev vals i).
      { intros i Hi. rewrite <- AG1, <- AG2, <- AG3 by (unfold NB in Hi; lia). unfold vals_ev at 1.
        rewrite app_nth1 by (rewrite length_firstn, HL3; unfold NB in *; lia).
        rewrite nth_firstn. apply Nat.ltb_lt in Hi. rewrite Hi. reflexivity. }
      split.
      + split; [rewrite length_app, junk_vals_length, length_firstn, HL3; reflexivity|].
        rewrite !AG4 by (unfold NB; lia). OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
      + apply junk_at_app. rewrite length_firstn, HL3. reflexivity.
      + apply (pins_of_sr sp0 a0s path envv rdraw Hvsp vals3 R5 srK4); [rewrite AG3, AG2, AG1 by lia; exact V0 | rewrite AG3, AG2, AG1 by lia; exact V2 | exact pins_K4 | exact HR].
      + apply (know_ok_agree RSEGS NB (ENV a0s path rdraw vals3)); [apply env_agree_rejunk; rewrite HL3; unfold NB; lia | exact knD_vars | exact HK].
      + exact HA5.
      + regv HR (9%bv : reg). cbn [edenot ev ENV]. rewrite AG3, AG2 by lia. exact Hv80.
      + regv HR (19%bv : reg). cbn [edenot ev ENV]. rewrite AG3, AG2, AG1 by lia. exact E57.
      + regv HR (21%bv : reg). rewrite <- A0V. apply (edenot_agree 70); [| reflexivity].
        split; [| reflexivity]. intros i Hi. cbn [ev ENV]. rewrite AG3, AG2, AG1 by lia. reflexivity.
      + regv HR (22%bv : reg). cbn [edenot ev ENV]. rewrite AG3, AG2, AG1 by lia. exact E60.
      + exact AI5.
      + exact MI5.
      + split.
        * rewrite (OTHER5 r Hrb). exact LIVE1.
        * intros q Hq. destruct (Z.eq_dec q b) as [->|Hqb]; [exact GONE5|]. rewrite (OTHER5 q Hqb), (OTHER1 q Hq). apply ONLY. exact Hqb.
        * split; [rewrite LB5, LB1, DSlb; lia | rewrite NL5, NL1, DSnl; destruct (Z.eqb_spec b 0); lia].
        * exact DATA5.
        * lia.
        * lia.
        * exact HlenL.
      + (first [ dand4 MF1 as FD1 _ FS1 _ | destruct MF1 as (FD1 & _ & FS1 & _) ]). (first [ dand4 MF5 as FD5 _ FS5 _ | destruct MF5 as (FD5 & _ & FS5 & _) ]). split.
        * unfold m_fs in *. rewrite FS5, FS1. exact Mfs.
        * unfold m_fds in *. rewrite FD5, FD1. exact Mfd3.
        * unfold m_fds in *. rewrite FD5, FD1. exact Mfd1.
        * unfold m_fds in *. rewrite FD5, FD1. exact Mfd2.
        * exact Hh5.
        * exact Hl5.
  Qed.
End MkStep.
End D_MkStep.

Module D_Loop.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.varnish.esi_parse_fuzzer.images Require Import Plain.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk SimInv ShapeAlg Shapi1s Nodes MmapSim AllocSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require AgentLib Frame SymExec SymExec2.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 SymAux LibK2dm RefMocc D_Kn21w MemSplit Spec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require RefNodes RefPl89 D_Stmwg D_Manqc.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Alu7n D_Wamxh.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Amb OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Shapi1s OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Frame OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymAux OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Kn21w OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MemSplit OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Spec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefNodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefPl89 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Stmwg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u.D_MainA OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Alu7n OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Wamxh OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Dr084 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_Reu44 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_MkStep.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0 DriverKit.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.
(* [comment removed for export] *)
Lemma natz_len_range : forall (A : Type) (l : list A) (a b : nat) (za zb : Z),
  Z.of_nat a = za -> Z.of_nat b = zb -> (a <= length l <= b)%nat -> (za <= Z.of_nat (length l) <= zb)%Z.
Proof. intros A l a b za zb <- <- H. split; apply Nat2Z.inj_le; apply H. Qed.
Lemma natz_len_le : forall (A : Type) (l : list A) (b : nat) (zb : Z), Z.of_nat b = zb -> (length l <= b)%nat -> (Z.of_nat (length l) <= zb)%Z.
Proof. intros A l b zb <- H. apply Nat2Z.inj_le; exact H. Qed.
Local Ltac natz_pos_lit p := lazymatch p with xH => idtac | xO ?q => natz_pos_lit q | xI ?q => natz_pos_lit q end.
Local Ltac natz_z_lit z := lazymatch z with Z0 => idtac | Zpos ?p => natz_pos_lit p end.   (* [comment removed for export] *)
Local Ltac natz_kl :=
  repeat match goal with
  | H : (?a <= @length ?A ?l <= ?b)%nat |- _ =>
      let za := eval vm_compute in (Z.of_nat a) in let zb := eval vm_compute in (Z.of_nat b) in
      natz_z_lit za; natz_z_lit zb;
      let Hz := fresh "KLz" in
      pose proof (natz_len_range A l a b za zb (@eq_refl Z za) (@eq_refl Z zb) H) as Hz; clear H
  | H : (@length ?A ?l <= ?b)%nat |- _ =>
      let zb := eval vm_compute in (Z.of_nat b) in
      natz_z_lit zb;
      let Hz := fresh "KLz" in
      pose proof (natz_len_le A l b zb (@eq_refl Z zb) H) as Hz; clear H
  end.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Zifyk6b.   (* [comment removed for export] *)
Local Ltac Zify.zify_pre_hook ::= natz_kl; OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Zifyk6b.zon_hook.
(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition rQ := Eval vm_compute in sym_exec RSEGS FUEL_L true [0x17dac]%Z (SCR [true] [] []) (SS 0x17bf8 sr_drv [] knD 70) [].
Definition srQ : list expr := Eval vm_compute in s_regs (fst (fst rQ)).
(* [comment removed for export] *)
Lemma pins_Q : pins_expr_ok srQ = true. Proof. vm_compute. reflexivity. Qed.

Section Loop.
  Context {AMB : Amb} {Clg : Ceiling} {AI : AllocSpec LayoutP0} {DK : DriverKit LayoutP0 InitP0}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable mem0 : word -> option byte.
  Variable fs0 : Fs.
  Variable data : list byte.
  Hypothesis Hvsp : valid_sp sp0.
  (* [comment removed for export] *)
  Hypothesis HCEIL : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hfile : fs_lookup fs0 path = Some data.
  Hypothesis Hplen : (length path <= 4095)%nat.

  Let L : Z := Z.of_nat (length data).

  (* [comment removed for export] *)
  Definition body_ok : Prop :=
    forall k b vals R M md A,
      hdr_st sp0 a0s path envv rdraw tid mem0 fs0 data k b vals R M md A -> (L < cap k)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17c60) M (seg_rom RSEGS)) md) (t_body data fs0).

  Lemma u64 : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
  Proof. intros. apply u_small. assumption. Qed.

  (* [comment removed for export] *)
  Theorem read_loop_gen : forall f, body_ok ->
    (forall k len b vals R M md A,
      rd_st sp0 a0s path envv rdraw tid mem0 fs0 data k len b vals R M md A -> (len < cap k)%Z ->
      (L - len + 11 - Z.of_nat k < Z.of_nat f)%Z -> m_fs md = fs0 ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17c30) M (seg_rom RSEGS)) md) (lshape data fs0 f k len))
    /\ (forall k b vals R M md A,
      grow_st sp0 a0s path envv rdraw tid mem0 fs0 data k b vals R M md A ->
      (L - cap k + 11 - Z.of_nat k < Z.of_nat f)%Z -> m_fs md = fs0 ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17bf8) M (seg_rom RSEGS)) md) (lshape data fs0 f k (cap k))).
  Proof.
    intros f KBODY. induction f as [|f IH].
    { split.
      - intros k len b vals R M md A ST Hlt Hf. exfalso. destruct ST as [_ _ _ _ _ _ _ _ _ _ _ [_ _ _ _ Hk Hlen HlenL] _]. lia.
      - intros k b vals R M md A ST Hf. exfalso. destruct ST as [_ _ _ _ _ _ _ _ _ _ _ _ [_ _ _ _ Hk Hlen HlenL] _]. lia. }
    destruct IH as [IHa IHb]. split.
    - (* [comment removed for export] *)
      intros k len b vals R M md A ST Hlt Hf Hfs.
      pose proof ST as [HB HJ HP HK HA S1 S3 S5 S6 AI0 MI BUF MD].
      pose proof BUF as [LIVE ONLY DS DATA Hk Hlen HlenL].
      cbn [lshape]. fold L.
      replace (len =? cap k)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      set (n := Z.min (Z.min (cap k - len) 65536) (L - len)).
      apply (rd_step sp0 a0s path envv rdraw tid mem0 fs0 data Hvsp HCEIL Hfile Hplen k len b vals R M md A _ ST Hlt).
      + intros Hn Hnf vals2 R2 M2 md2 ST2. fold L in Hn, Hnf. fold n in Hn, Hnf. fold L. fold n.
        replace (n =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
        apply (IHa k (len + n)%Z b vals2 R2 M2 md2 A ST2); [lia | subst n; lia|].
        destruct ST2 as [_ _ _ _ _ _ _ _ _ _ _ _ MD2]. destruct MD2 as [X _ _ _ _ _]. exact X.
      + intros Hn Hnf vals2 R2 M2 md2 ST2. fold L in Hn, Hnf. fold n in Hn, Hnf. fold L. fold n.
        replace (n =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
        rewrite Hnf. apply (IHb k b vals2 R2 M2 md2 A ST2); [subst n; lia|].
        destruct ST2 as [_ _ _ _ _ _ _ _ _ _ _ _ _ MD2]. destruct MD2 as [X _ _ _ _ _]. exact X.
      + intros Hn vals2 R2 M2 md2 ST2. fold L in Hn. fold n in Hn. fold L. fold n. rewrite Hn. cbn [Z.eqb].
        apply (KBODY k b vals2 R2 M2 md2 A ST2). subst n. lia.
    - (* [comment removed for export] *)
      intros k b vals R M md A ST Hf Hfs.
      pose proof ST as [HB HJ HP HK HA S1 S3 S5 S6 S7 AI0 MI BUF MD].
      pose proof HB as (HL & V0 & V1 & V2 & V5).
      pose proof BUF as [LIVE ONLY DS DATA Hk Hlen HlenL]. pose proof MD as [Mfs Mfd3 Mfd1 Mfd2 Mh Mlz].
      pose proof (cap_range path data Hplen k Hk) as Hcap.
      cbn [lshape]. fold L. rewrite Z.eqb_refl.
      destruct (Z.leb_spec 10 (Z.of_nat k)) as [K10|K10].
      + (* [comment removed for export] *)
        assert (k = 10%nat) by lia. subst k.
        pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo.
        pose proof (sr_drv_ok sp0 a0s path envv rdraw tid Hvsp vals R HB HJ HP) as HR.
        assert (E57 : vals_ev vals 57 = Z_to_bv 64 (cap 10)) by (rewrite <- S3; exact (HJ 19%nat ltac:(lia))).
        change (cap 10) with 67108864%Z in *.
        clear HJ HP.
        run_block_gen FUEL_L [0x17dac]%Z (SCR [true] [] []) 70%nat true.
        { cbn [sc_denot edenot ev ENV]. rewrite E57.
          replace (alu64 ALU_SRL (Z_to_bv 64 67108864) (Z_to_bv 64 26)) with (Z_to_bv 64 1).
          2:{ apply bv_eq. rewrite u_srl64, !u64 by lia. reflexivity. }
          rewrite bt_ne0_Z by lia. reflexivity. }
        cbn [mem_denot] in EQM. subst M0. rewrite <- Hfs.
        assert (AG : forall i, (i < NB)%nat -> vals_ev (firstn NB vals ++ junk_vals R0) i = vals_ev vals i).
        { intros i Hi. unfold vals_ev at 1. rewrite app_nth1 by (rewrite length_firstn, HL; unfold NB in *; lia).
          rewrite nth_firstn. apply Nat.ltb_lt in Hi. rewrite Hi. reflexivity. }
        apply (refused_tail sp0 a0s path envv rdraw tid Hvsp (firstn NB vals ++ junk_vals R0) R0 M md).
        * split; [rewrite length_app, junk_vals_length, length_firstn, HL; reflexivity|].
          rewrite !AG by (unfold NB; lia). repeat split; assumption.
        * apply junk_at_app. rewrite length_firstn, HL. reflexivity.
        * apply (pins_of_sr sp0 a0s path envv rdraw Hvsp vals R0 srQ V0 V2 pins_Q HR).
        * apply (know_ok_agree RSEGS NB (ENV a0s path rdraw vals)); [apply env_agree_rejunk; rewrite HL; unfold NB; lia | exact knD_vars | exact HK].
        * exact Mh.
        * exact Mlz.
        * exact Mfd2.
      + (* [comment removed for export] *)
        apply (mk_step sp0 a0s path envv rdraw tid mem0 fs0 data Hvsp HCEIL Hplen k b vals R M md A _ ST ltac:(lia)).
        intros vals' R' M' md' A' b' ST'.
        pose proof ST' as [_ _ _ _ _ _ _ _ _ _ _ BUF' MD'].
        pose proof BUF' as [_ _ _ _ Hk' Hlen' _]. pose proof (cap_range path data Hplen (S k) Hk') as Hcap'.
        assert (CAP2 : cap (S k) = (2 * cap k)%Z) by (unfold cap; rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; lia).
        apply (IHa (S k) (cap k) b' vals' R' M' md' A' ST'); [lia | lia | destruct MD' as [X _ _ _ _ _]; exact X].
  Qed.

  Theorem read_loop : forall f k len b vals R M md A,
    body_ok ->
    rd_st sp0 a0s path envv rdraw tid mem0 fs0 data k len b vals R M md A -> (len < cap k)%Z ->
    (L - len + 11 - Z.of_nat k < Z.of_nat f)%Z -> m_fs md = fs0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17c30) M (seg_rom RSEGS)) md) (lshape data fs0 f k len).
  Proof. intros f k len b vals R M md A KBODY. exact (proj1 (read_loop_gen f KBODY) k len b vals R M md A). Qed.
End Loop.
End D_Loop.

Module D_InitOk.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.varnish.esi_parse_fuzzer.images Require Import Plain.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk SimInv ShapeAlg Nodes MmapSim AgentLib Frame SymExec SymExec2.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 ArgvEnv RefL1zx Star5ef MemSplit StepTac D_St4s2.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Manqc.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Stmwg D_Manqc.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u D_Alu7n Img0.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Amb OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Frame OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.ArgvEnv OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefL1zx OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MemSplit OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_St4s2 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc.D_Stw4n OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Stmwg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u.D_MainA OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Alu7n OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Img0.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0 DriverKit.
Import ListNotations. Import SX2. Import SX2S.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rom_zero_b (lo : Z) (n : nat) : bool :=
  match rdn RSEGS (fun _ => None) (Z_to_bv 64 lo) n with
  | Some bs => forallb (fun b => bv_eqb b (Z_to_bv 8 0)) bs
  | None => false
  end.

Lemma rdn1_rom : forall (a : word) b, rdn RSEGS (fun _ => None) a 1 = Some [b] -> seg_rom RSEGS a = Some b.
Proof. intros a b H. cbn [rdn] in H. destruct (seg_rom RSEGS a); [injection H as ->; reflexivity| discriminate]. Qed.

Lemma rom_zero_sound : forall lo n, rom_zero_b lo n = true -> (0 <= lo)%Z -> (lo + Z.of_nat n <= 2 ^ 64)%Z ->
  forall i, (0 <= i < Z.of_nat n)%Z -> seg_rom RSEGS (Z_to_bv 64 (lo + i)) = Some (Z_to_bv 8 0).
Proof.
  intros lo n Hb H0 H1 i Hi. unfold rom_zero_b in Hb.
  destruct (rdn RSEGS (fun _ => None) (Z_to_bv 64 lo) n) as [bs|] eqn:Hr; [|discriminate].
  assert (HL : length bs = n) by (eapply rdn_length; exact Hr).
  pose proof (rdn_nth RSEGS (fun _ => None) n (Z_to_bv 64 lo) bs (Z.to_nat i) Hr ltac:(lia)) as Hn.
  rewrite word_add_nat, u_small, Z2Nat.id in Hn by lia.
  apply rdn1_rom in Hn. rewrite Hn. f_equal.
  rewrite forallb_forall in Hb. apply bv_eqb_eq. apply Hb. apply nth_In. lia.
Qed.

(* [comment removed for export] *)
Lemma nth_Z_to_le_bytes : forall n z i, (i < n)%nat ->
  nth i (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat i)).
Proof.
  induction n as [|n IH]; intros z i Hi; [lia|].
  cbn [Z_to_le_bytes]. destruct i as [|i].
  - cbn [nth]. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma byte_window : forall v k, (0 <= v)%Z -> (0 <= k <= 7)%Z ->
  (((v mod 2 ^ 64) / 2 ^ (8 * k)) mod 256 = (v / 2 ^ (8 * k)) mod 256)%Z.
Proof.
  intros v k Hv Hk.
  assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7)%Z as C by lia.
  change (2 ^ 64)%Z with 18446744073709551616%Z.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; cbn [Z.mul Z.pow Z.pow_pos Pos.iter Pos.mul]; lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma nth_le8 : forall v i, (0 <= v)%Z -> (0 <= i < 8)%Z ->
  nth (Z.to_nat i) (word_to_le_bytes 8 (Z_to_bv 64 v)) (Z_to_bv 8 0) = le8 v i.
Proof.
  intros v i Hv Hi. unfold word_to_le_bytes, le8. rewrite nth_Z_to_le_bytes by lia.
  rewrite Z2Nat.id by lia. rewrite Z.shiftr_div_pow2 by lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. cbn [bv_modulus Z.of_N].
  change (2 ^ 8)%Z with 256%Z. rewrite Zmod_mod. apply byte_window; lia.
Qed.

(* [comment removed for export] *)
Lemma rom_cell8 : forall (a v : Z), rdn RSEGS (fun _ => None) (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)) ->
  (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z -> (0 <= v)%Z ->
  forall i, (0 <= i < 8)%Z -> seg_rom RSEGS (Z_to_bv 64 (a + i)) = Some (le8 v i).
Proof.
  intros a v Hr H0 H1 Hv i Hi.
  pose proof (rdn_nth RSEGS (fun _ => None) 8 (Z_to_bv 64 a) _ (Z.to_nat i) Hr ltac:(lia)) as Hn.
  rewrite word_add_nat, u_small, Z2Nat.id in Hn by lia. apply rdn1_rom in Hn. rewrite Hn. f_equal.
  apply nth_le8; lia.
Qed.

Lemma statics_rom : rom_zero_b 0x62458 940 = true. Proof. vm_compute. reflexivity. Qed.
Lemma needlocks_rom : rom_zero_b 0x623eb 1 = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma got_rom : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x30428) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x623c8)).
Proof. vm_refl_bv. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Init.
  Context {AMB : Amb} {Clg : Ceiling} {AI : AllocSpec LayoutP0}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv rdraw tid regs mem.
  (* [comment removed for export] *)
  Hypothesis HCEIL : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.
  Local Notation R16 := (at_random_bytes (ed_random rdraw)) (only parsing).
  Local Notation DM := (D_main sp0 av envv a_hwcap (at_random_bytes (ed_random rdraw)) tid).

  Lemma u64 : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
  Proof. intros. apply u_small. assumption. Qed.

  (* [comment removed for export] *)
  Lemma D_none_range : forall a, (0 <= a < 2 ^ 64)%Z ->
    (a < 0x317b0 \/ (0x317b1 <= a < 0x42088) \/ 0x62458 <= a)%Z ->
    DM (Z_to_bv 64 a) = None.
  Proof.
    intros a Ha Hr. pose proof (u64_range tid) as Ht. pose proof (u64_range a_hwcap) as Hhw.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. unfold sp_window_lo, sp_window_hi in *.
    assert (Hui : bv_unsigned (Z_to_bv 64 a) = a) by (apply u_small; lia).
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite MemSplit.wbytes_outside;
      [ | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by (cbn; lia); cbn; lia
        | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Hui; rewrite u_small by (cbn; lia); lia ]).
    reflexivity.
  Qed.

  Lemma mem_low : forall a, (0 <= a < bv_unsigned sp0 - 8388608)%Z -> mem (Z_to_bv 64 a) = DM (Z_to_bv 64 a).
  Proof.
    intros a Ha. pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. pose proof (u64_range sp0).
    apply (main_entry_mem_data sp0 av envv rdraw tid regs mem ME). rewrite stack_max_size_val, u64 by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_cell8 : forall (c v : Z),
    rdn RSEGS DM (Z_to_bv 64 c) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)) ->
    (forall i, (0 <= i < 8)%Z -> DM (Z_to_bv 64 (c + i)) <> None) ->
    (0x31458 <= c)%Z -> (c + 8 <= 0x63000)%Z -> (0 <= v)%Z ->
    cell8 mem c v.
  Proof.
    intros c v Hr Hd Hc0 Hc1 Hv i Hi. pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. rewrite mem_low by lia.
    pose proof (rdn_nth RSEGS _ 8 (Z_to_bv 64 c) _ (Z.to_nat i) Hr ltac:(lia)) as Hn.
    rewrite word_add_nat, u_small, Z2Nat.id in Hn by lia. cbn [rdn] in Hn.
    destruct (DM (Z_to_bv 64 (c + i))) as [b|] eqn:E.
    - injection Hn as Hb. rewrite Hb. f_equal. apply nth_le8; lia.
    - exfalso. exact (Hd i Hi E).
  Qed.

  Lemma wbytes_some_in : forall m (a x : word) bs,
    (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
    (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs))%Z ->
    wbytes m a bs x <> None.
  Proof. intros m a x bs H1 H2. rewrite wbytes_inside by assumption. discriminate. Qed.
  Lemma wbytes_some_mono : forall m (a x : word) bs, m x <> None -> wbytes m a bs x <> None.
  Proof. intros m a x bs H. apply (wbytes_grows bs m a x). exact H. Qed.

  Ltac d_some Hui :=
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc;
    repeat (first [ apply wbytes_some_in; rewrite ?length_N_to_le_bytes, ?length_guard_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?Hui; rewrite u_small by (cbn; lia); lia
                  | apply wbytes_some_mono ]).

  Lemma D_some_pagesize : forall i, (0 <= i < 8)%Z -> DM (Z_to_bv 64 (0x62418 + i)) <> None.
  Proof.
    intros i Hi. pose proof (u64_range tid).
    assert (Hui : bv_unsigned (Z_to_bv 64 (0x62418 + i)) = (0x62418 + i)%Z) by (apply u_small; lia).
    d_some Hui.
  Qed.
  Lemma D_some_auxv : forall i, (0 <= i < 8)%Z -> DM (Z_to_bv 64 (0x623f0 + i)) <> None.
  Proof.
    intros i Hi. pose proof (u64_range tid).
    assert (Hui : bv_unsigned (Z_to_bv 64 (0x623f0 + i)) = (0x623f0 + i)%Z) by (apply u_small; lia).
    d_some Hui.
  Qed.
  Lemma D_some_guard : forall i, (0 <= i < 8)%Z -> DM (Z_to_bv 64 (0x623c8 + i)) <> None.
  Proof.
    intros i Hi. rewrite (D_main_guard_at sp0 av envv rdraw tid i Hi). discriminate.
  Qed.

  (* [comment removed for export] *)
  Lemma stack_cell8 : forall (a v : Z),
    rdn RSEGS mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)) ->
    (0x63000 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z -> (0 <= v)%Z -> cell8 mem a v.
  Proof.
    intros a v Hr H0 H1 Hv i Hi.
    pose proof (rdn_pointwise_inv RSEGS mem 8 (Z_to_bv 64 a) _
                  ltac:(intros j Hj; apply seg_rom_high; rewrite (u_small a) by lia; rewrite u_small by lia; lia)
                  ltac:(rewrite u_small by lia; lia) Hr (Z.to_nat i) ltac:(lia)) as Hp.
    rewrite u_small, Z2Nat.id in Hp by lia. rewrite Hp. f_equal. apply nth_le8; lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma cell8_addr : forall (m : word -> option byte) a a' v, a = a' -> cell8 m a' v -> cell8 m a v.
  Proof. intros m a a' v -> H. exact H. Qed.

  (* [comment removed for export] *)
  Theorem init_ok_entry : forall md,
    vm_maps (m_vmmaps md) = [] -> vm_noaccess (m_vmmaps md) = [] -> m_vm_lazy md = [] -> m_vm_materialized md = [] ->
    vm_brk (m_vmmaps md) = vm_start_brk (m_vmmaps md) -> (0x63000 <= bv_unsigned (vm_start_brk (m_vmmaps md)))%Z ->
    (bv_unsigned (vm_start_brk (m_vmmaps md)) mod 4096 = 0)%Z -> bw_limit (vm_limit (m_vmmaps md)) ->
    m_halted md = None ->
    map (fun e => (bv_unsigned (fst e), bv_unsigned (snd e))) (vm_reserved (m_vmmaps md)) = il_resv InitP0 ->
    (bv_unsigned (vm_start_brk (m_vmmaps md)) + 4 * 4096 <= alloc_ceiling)%Z ->
    ceil_ok md ->
    init_ok LayoutP0 InitP0 (bv_unsigned sp0) mem md.
  Proof.
    intros md V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp. pose proof (u64_range tid) as Ht.
    pose proof alloc_ceiling_val as CV.
    destruct (auxvp_u sp0 a0s path envv rdraw Hva Hve Hvsp) as [Hau Hab].
    (first [ pose proof ((rnd_u sp0 a0s path envv rdraw Hva Hve Hvsp)) as dR_1; dand4 dR_1 as Hr1 Hr2 Hr3 Hr4 | destruct (rnd_u sp0 a0s path envv rdraw Hva Hve Hvsp) as (Hr1 & Hr2 & Hr3 & Hr4) ]).
    pose proof (u64_range (auxvp sp0 a0s path envv)) as Hauv. pose proof (u64_range (rnd sp0 a0s path envv)) as Hrnv.
    pose proof (u64_range a_uid) as Huid. pose proof (u64_range a_hwcap) as Hhw.
    unfold init_ok. cbn [il_static_lo il_static_hi il_libc il_got il_guard InitP0 al_image_hi LayoutP0].
    change (al_rom LayoutP0) with (seg_rom RSEGS).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption]]]]]]].
    - (* [comment removed for export] *)
      intros a Ha. right. split.
      + rewrite mem_low by lia. apply D_none_range; lia.
      + left. replace a with (0x62458 + (a - 0x62458))%Z by lia. apply (rom_zero_sound 0x62458 940 statics_rom); lia.
    - (* [comment removed for export] *)
      right. split.
      + rewrite mem_low by lia. apply (D_main_none sp0 av envv a_hwcap R16 tid); [exact Hva| lia| lia| vm_compute; reflexivity].
      + left. replace (0x623e8 + 3)%Z with (0x623eb + 0)%Z by reflexivity. apply (rom_zero_sound 0x623eb 1 needlocks_rom); lia.
    - (* [comment removed for export] *)
      replace (0x623e8 + 48)%Z with 0x62418%Z by reflexivity.
      apply D_cell8; [apply (D_main_pagesize sp0 av envv rdraw tid Hva)| apply D_some_pagesize| lia| lia| lia].
    - (* [comment removed for export] *)
      set (uid := bv_unsigned a_uid). set (hw := bv_unsigned a_hwcap).
      set (rp := bv_unsigned (rnd sp0 a0s path envv)). set (avp := bv_unsigned (auxvp sp0 a0s path envv)).
        assert (WAT : forall j, (j < 20)%nat ->
                  rdn RSEGS mem (Z_to_bv 64 (avp + 8 * Z.of_nat j)) 8 =
                  Some (word_to_le_bytes 8 (nth j (auxv_words Plain.M.phdrs (rnd sp0 a0s path envv) a_uid a_hwcap) (Z_to_bv 64 0))))
          by (intros j Hj; subst avp; apply (auxv_word_at sp0 a0s path envv rdraw tid regs mem Hva Hve Hvsp ME j Hj)).
        assert (C8 : forall j (v : Z), (j < 20)%nat -> (0 <= v)%Z ->
                  nth j (auxv_words Plain.M.phdrs (rnd sp0 a0s path envv) a_uid a_hwcap) (Z_to_bv 64 0) = Z_to_bv 64 v ->
                  cell8 mem (avp + 8 * Z.of_nat j) v).
        { intros j v Hj Hv Hn. apply stack_cell8; [| subst avp; lia| subst avp; lia| exact Hv]. rewrite (WAT j Hj), Hn. reflexivity. }
        assert (Hr : rdn RSEGS mem (rnd sp0 a0s path envv) 16 = Some (firstn 16 (skipn 0 R16))).
        { rewrite (main_entry_rdn_above sp0 av envv rdraw tid regs mem ME) by lia.
          pose proof (rdn_wmem_stack RSEGS Plain.M.phdrs sp0 av envv a_uid a_hwcap rdraw) as Hw. unfold wmem in Hw.
          rewrite Hw by lia.
          pose proof (Hr4 0%nat 16%nat ltac:(lia)) as H16. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H16. exact H16. }
      exists avp, rp, 0x10040%Z, 56%Z, 10%Z, hw, 4096%Z, uid, uid, 0%Z.
      split.
      { subst avp.
        replace (0x623e8 + 8)%Z with 0x623f0%Z by reflexivity.
        apply D_cell8; [| apply D_some_auxv| lia| lia| lia]. rewrite Z_to_bv_bv_unsigned. apply (D_main_auxvp sp0 a0s path envv rdraw tid Hvsp).
      }
      split; [subst avp; lia|].
      split.
        { subst avp. rewrite Hau. destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) SPal) as [q Hq].
          replace (bv_unsigned sp0 + Z.of_nat (auxv_off [a0s; path] envv))%Z with ((2 * q + 5 + Z.of_nat (length envv)) * 8)%Z
            by (unfold auxv_off; cbn [length]; lia).
          apply Z_mod_mult. }
      split; [subst avp; lia|]. split; [subst rp; lia|]. split; [subst rp; lia|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [subst hw; lia|]. split; [lia|]. split; [subst uid; lia|]. split; [subst uid; lia|]. split; [lia|].
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul] in C8.
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 0)); [lia| apply (C8 0%nat); [lia|lia|reflexivity]]|].
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 1)); [lia| apply (C8 1%nat); [lia|lia|reflexivity]]|].
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 2)); [lia| apply (C8 2%nat); [lia|lia|reflexivity]]|].
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 3)); [lia| apply (C8 3%nat); [lia|lia|reflexivity]]|].
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 4)); [lia| apply (C8 4%nat); [lia|lia|reflexivity]]|].
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 5)); [lia| apply (C8 5%nat); [lia|lia|reflexivity]]|].
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 6)); [lia| apply (C8 6%nat); [lia|lia|reflexivity]]|].
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 7)); [lia| apply (C8 7%nat); [lia|subst hw; lia| subst hw; cbn [nth auxv_words auxv_entries flat_map fst snd app]; rewrite Z_to_bv_bv_unsigned; reflexivity]]|].
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 8)); [lia| apply (C8 8%nat); [lia|lia|reflexivity]]|].
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 9)); [lia| apply (C8 9%nat); [lia|lia|reflexivity]]|].
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 10)); [lia| apply (C8 10%nat); [lia|lia|reflexivity]]|].
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 11)); [lia| apply (C8 11%nat); [lia|subst uid; lia| subst uid; cbn [nth auxv_words auxv_entries flat_map fst snd app]; rewrite Z_to_bv_bv_unsigned; reflexivity]]|].
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 12)); [lia| apply (C8 12%nat); [lia|lia|reflexivity]]|].
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 13)); [lia| apply (C8 13%nat); [lia|subst uid; lia| subst uid; cbn [nth auxv_words auxv_entries flat_map fst snd app]; rewrite Z_to_bv_bv_unsigned; reflexivity]]|].
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 14)); [lia| apply (C8 14%nat); [lia|lia|reflexivity]]|].
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 15)); [lia| apply (C8 15%nat); [lia|lia|reflexivity]]|].
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 16)); [lia| apply (C8 16%nat); [lia|lia|reflexivity]]|].
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 17)); [lia| apply (C8 17%nat); [lia|subst rp; lia| subst rp; cbn [nth auxv_words auxv_entries flat_map fst snd app]; rewrite Z_to_bv_bv_unsigned; reflexivity]]|].
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 18)); [lia| apply (C8 18%nat); [lia|lia|reflexivity]]|].
      split; [eapply (cell8_addr mem _ (avp + 8 * Z.of_nat 19)); [lia| apply (C8 19%nat); [lia|lia|reflexivity]]|].
      split.
      { intros i Hi.
        pose proof (rdn_pointwise_inv RSEGS mem 16 (rnd sp0 a0s path envv) _
                      ltac:(intros j Hj; apply seg_rom_high; rewrite u_small by lia; lia)
                      ltac:(lia) Hr (Z.to_nat i) ltac:(lia)) as Hp.
        rewrite Z2Nat.id in Hp by lia. subst rp. rewrite Hp. discriminate. }
      subst avp rp. lia.
    - (* [comment removed for export] *)
      intros i Hi. right. split.
      + rewrite mem_low by lia. apply D_none_range; lia.
      + apply (rom_cell8 0x30428 0x623c8 got_rom); lia.
    - (* [comment removed for export] *)
      exists (bytes_le_to_Z (guard_bytes R16)).
      pose proof (bytes_le_to_Z_bound (guard_bytes R16)) as GB. rewrite length_guard_bytes in GB.
      pose proof (bytes_le_to_Z_nonneg (guard_bytes R16)) as G0.
      change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in GB.
      split; [lia|].
      assert (GZ : rdn RSEGS DM (Z_to_bv 64 0x623c8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bytes_le_to_Z (guard_bytes R16))))).
      { rewrite (D_main_guard sp0 av envv rdraw tid). f_equal. symmetry.
        apply word_to_le_bytes_of_lez; [apply length_guard_bytes | lia]. }
      exact (D_cell8 0x623c8 _ GZ D_some_guard ltac:(lia) ltac:(lia) G0).
    - (* [comment removed for export] *)
      intros a [Ha Hni]. unfold in_image in Hni. cbn [al_image_lo al_image_hi LayoutP0] in Hni.
      rewrite mem_low by lia. apply D_none_range; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma init_ok_frame_win : forall (M M' : word -> option byte) md,
    (forall x : word, ~ (bv_unsigned sp0 - 8388608 <= bv_unsigned x < bv_unsigned sp0)%Z -> M' x = M x) ->
    init_ok LayoutP0 InitP0 (bv_unsigned sp0) M md -> init_ok LayoutP0 InitP0 (bv_unsigned sp0) M' md.
  Proof.
    intros M M' md AG IO.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp.
    pose proof alloc_ceiling_val as CV.
    assert (AGZ : forall a, (0 <= a < 2 ^ 64)%Z -> ~ (bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0)%Z -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hn. apply AG. rewrite u64 by lia. exact Hn. }
    unfold init_ok in *. cbn [il_static_lo il_static_hi il_libc il_got il_guard InitP0 al_image_hi LayoutP0] in *.
    (first [ dand8 IO as S1 S2 S3 S4 S5 S6 S7 REST | destruct IO as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & REST) ]).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|exact REST]]]]]]].
    - intros a Ha. unfold zero_img in *. rewrite AGZ by lia. apply S1. exact Ha.
    - unfold zero_img in *. rewrite AGZ by lia. exact S2.
    - intros i Hi. rewrite AGZ by lia. apply S3. exact Hi.
    - (first [ dex10 S4 as avv rp x3 x4 x5 hw x6 x11 x12 x23; dand15 S4 as C1 B1 B2 B3 B4 B5 R3 R4 R5 Rhw R6 R11 R12 R23 REST4 | dand25 S4 as avv rp x3 x4 x5 hw x6 x11 x12 x23 C1 B1 B2 B3 B4 B5 R3 R4 R5 Rhw R6 R11 R12 R23 REST4 | destruct S4 as (avv & rp & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & C1 & B1 & B2 & B3 & B4 & B5 & R3 & R4 & R5 & Rhw & R6 & R11 & R12 & R23 & REST4) ]).
      exists avv, rp, x3, x4, x5, hw, x6, x11, x12, x23.
      split; [intros i Hi; rewrite AGZ by lia; apply C1; exact Hi|].
      split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|].
      split; [exact R3|]. split; [exact R4|]. split; [exact R5|]. split; [exact Rhw|]. split; [exact R6|]. split; [exact R11|]. split; [exact R12|]. split; [exact R23|].
      (first [ dand23 REST4 as E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15 E16 E17 E18 E19 ZR L1 L2 | destruct REST4 as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & ZR & L1 & L2) ]).
      assert (T8 : forall a v, (bv_unsigned sp0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z -> cell8 M a v -> cell8 M' a v)
        by (intros a v Ha Hb C i Hi; rewrite AGZ by lia; apply C; exact Hi).
      repeat match goal with |- cell8 _ _ _ /\ _ => split; [apply T8; [lia| lia| assumption]|] end.
      split; [| split; [exact L1| exact L2]].
      intros i Hi. rewrite AGZ by lia. apply ZR. exact Hi.
    - intros i Hi. unfold cell8_img in *. rewrite AGZ by lia. apply S5. exact Hi.
    - (first [ dex1 S6 as g; destruct S6 as [Hg C6] | dand3 S6 as g Hg C6 | destruct S6 as (g & Hg & C6) ]). exists g. split; [exact Hg|]. intros i Hi. rewrite AGZ by lia. apply C6. exact Hi.
    - intros a [Ha Hni]. unfold in_image in Hni. cbn [al_image_lo al_image_hi LayoutP0] in Hni.
      rewrite AGZ by lia. apply S7. split; [exact Ha| exact Hni].
  Qed.
End Init.
End D_InitOk.

Module D_Main.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.varnish.esi_parse_fuzzer.images Require Import Plain.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk SimInv ShapeAlg Shapi1s Nodes MmapSim AllocSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require AgentLib Frame SymExec SymExec2.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 SymAux LibK2dm RefMocc D_Kn21w MemSplit Spec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require RefNodes RefPl89 D_Stmwg D_Manqc.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Alu7n D_Wamxh.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Usage.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Opxmp.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Opxmp.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Amb OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Shapi1s OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Frame OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymAux OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Kn21w OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MemSplit OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Spec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefNodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefPl89 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Stmwg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u.D_MainA OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Alu7n OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Wamxh OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Dr084 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_Reu44 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_MkStep OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_Loop OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_MainM0 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Usage OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Opxmp.D_Op42l OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Opxmp OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_InitOk.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0 DriverKit.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.
(* [comment removed for export] *)
Lemma natz_len_range : forall (A : Type) (l : list A) (a b : nat) (za zb : Z),
  Z.of_nat a = za -> Z.of_nat b = zb -> (a <= length l <= b)%nat -> (za <= Z.of_nat (length l) <= zb)%Z.
Proof. intros A l a b za zb <- <- H. split; apply Nat2Z.inj_le; apply H. Qed.
Lemma natz_len_le : forall (A : Type) (l : list A) (b : nat) (zb : Z), Z.of_nat b = zb -> (length l <= b)%nat -> (Z.of_nat (length l) <= zb)%Z.
Proof. intros A l b zb <- H. apply Nat2Z.inj_le; exact H. Qed.
Local Ltac natz_pos_lit p := lazymatch p with xH => idtac | xO ?q => natz_pos_lit q | xI ?q => natz_pos_lit q end.
Local Ltac natz_z_lit z := lazymatch z with Z0 => idtac | Zpos ?p => natz_pos_lit p end.   (* [comment removed for export] *)
Local Ltac natz_kl :=
  repeat match goal with
  | H : (?a <= @length ?A ?l <= ?b)%nat |- _ =>
      let za := eval vm_compute in (Z.of_nat a) in let zb := eval vm_compute in (Z.of_nat b) in
      natz_z_lit za; natz_z_lit zb;
      let Hz := fresh "KLz" in
      pose proof (natz_len_range A l a b za zb (@eq_refl Z za) (@eq_refl Z zb) H) as Hz; clear H
  | H : (@length ?A ?l <= ?b)%nat |- _ =>
      let zb := eval vm_compute in (Z.of_nat b) in
      natz_z_lit zb;
      let Hz := fresh "KLz" in
      pose proof (natz_len_le A l b zb (@eq_refl Z zb) H) as Hz; clear H
  end.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Zifyk6b.   (* [comment removed for export] *)
Local Ltac Zify.zify_pre_hook ::= natz_kl; OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Zifyk6b.zon_hook.
(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition rsegs := Plain.M.loaded_segments.
Definition rpc := Plain.M.init_pc.
Definition rph := Plain.M.phdrs.

(* [comment removed for export] *)
Definition rE := Eval vm_compute in runL [false; true] (SS 0x17bb8 sr_drv [] knD 70).
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
(* [comment removed for export] *)
Lemma pins_E : pins_expr_ok srE = true. Proof. vm_compute. reflexivity. Qed.

Lemma ref_list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
  intros p; induction p as [|a p IH]; intros [|b q]; cbn; split; try discriminate; try reflexivity.
  - intros H. apply andb_prop in H as [H1 H2]. apply bv_eqb_eq in H1. apply IH in H2. subst. reflexivity.
  - intros H. injection H as -> ->. rewrite bv_eqb_refl. cbn. apply IH. reflexivity.
Qed.

Section Main.
  Context {Clg : Ceiling} {AI : AllocSpec LayoutP0} {DK : DriverKit LayoutP0 InitP0}.

  Section FileExists.
    Context {AMB : Amb}.
    Variable sp0 : word.
    Variables a0s path : list byte.
    Variable envv : list (list byte).
    Variable rdraw : EntryDraw.
    Variable tid : word.
    Variable regs0 : bvmap 5 word.
    Variable mem0 : word -> option byte.
    Variables brk mbase : word.
    Variable fs0 : Fs.
    Variable stdin0 : InputStream.
    Variable fdata : list byte.
    Hypothesis Hva : valid_argv [a0s; path].
    Hypothesis Hve : valid_envp envv.
    Hypothesis Hvsp : valid_sp sp0.
    (* [comment removed for export] *)
    Hypothesis HCEIL : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.
    Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
    Hypothesis ME : main_entry sp0 [a0s; path] envv rdraw tid regs0 mem0.
    Hypothesis Hfit : entry_stack_fits sp0 [a0s; path] envv.   (* [comment removed for export] *)
    Hypothesis Hbrk : valid_brk RSEGS brk.
    Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
    Hypothesis Hpne : path <> [].
    Hypothesis Hpnd : path <> dot_path.
    Hypothesis Hplen : (length path <= 4095)%nat.
    Hypothesis BODY : body_ok sp0 a0s path envv rdraw tid mem0 fs0 fdata.

    Let L : Z := Z.of_nat (length fdata).
    Let FUELF : nat := (length fdata + 12)%nat.

    (* [comment removed for export] *)
    Lemma after_M0 : post_M0 sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 (FdFile path (Z_to_bv 64 0)) (lshape fdata fs0 FUELF 0 0).
    Proof.
      intros vals R M md A b HB HJ HP HK G10 Hb G21 AI0 MI MF LB NL LIVE ONLY HA.   (* [comment removed for export] *)
      (first [ pose proof (HB) as dR_1; dand5 dR_1 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]).
      pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. pose proof (u64_range sp0) as Hsp.
      (first [ pose proof ((block_range sp0 path fdata HCEIL Hplen A M md b 65536 AI0 LIVE)) as dR_2; dand4 dR_2 as _ _ HbLO HbHI | destruct (block_range sp0 path fdata HCEIL Hplen A M md b 65536 AI0 LIVE) as (_ & _ & HbLO & HbHI) ]). unfold HEAP_LO, LOW_LO, LOW_HI in HbLO.
      pose proof (sr_drv_ok sp0 a0s path envv rdraw tid Hvsp vals R HB HJ HP) as HR.
      assert (E48 : vals_ev vals 48 = Z_to_bv 64 b) by (rewrite <- G10; exact (HJ 10%nat ltac:(lia))).
      assert (E59 : vals_ev vals 59 = Z_to_bv 64 65536) by (rewrite <- G21; exact (HJ 21%nat ltac:(lia))).
      assert (Hh : m_halted md = None) by (destruct (as_lazy_nil A M md AI0) as [_ X]; exact X).
      assert (Hl : m_vm_lazy md = []) by (destruct (as_lazy_nil A M md AI0) as [X _]; exact X).
      clear HJ HP.
      run_blockL_keep [false; true] 70%nat.
      { cbn [sc_denot edenot ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV D_Mah0u.ENV]. rewrite E59. cbn [branch_taken]. unfold bv_eqb. rewrite !u_small by lia. reflexivity. }
      { cbn [sc_denot edenot ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV D_Mah0u.ENV]. rewrite E48, bt_eq0_Z by lia. apply Z.eqb_neq. exact Hb. }
      cbn [mem_denot] in EQM. subst M0.
      (first [ dand4 MF as FD _ FS _ | destruct MF as (FD & _ & FS & _) ]).
      apply (read_loop sp0 a0s path envv rdraw tid mem0 fs0 fdata Hvsp HCEIL Hfile Hplen FUELF 0 0 b (firstn NB vals ++ junk_vals R0) R0 M md A BODY);
        [| change (cap 0) with 65536%Z; lia | unfold FUELF; change (cap 0) with 65536%Z; lia | unfold m_fs; rewrite FS; reflexivity].
      assert (AG : forall i, (i < NB)%nat -> vals_ev (firstn NB vals ++ junk_vals R0) i = vals_ev vals i).
      { intros i Hi. unfold vals_ev at 1. rewrite app_nth1 by (rewrite length_firstn, HL; unfold NB in *; lia).
        rewrite nth_firstn. apply Nat.ltb_lt in Hi. rewrite Hi. reflexivity. }
      split.
      - split; [rewrite length_app, junk_vals_length, length_firstn, HL; reflexivity|].
        rewrite !AG by (unfold NB; lia). OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
      - apply junk_at_app. rewrite length_firstn, HL. reflexivity.
      - apply (pins_of_sr sp0 a0s path envv rdraw Hvsp vals R0 srE V0 V2 pins_E HR).
      - apply (know_ok_agree RSEGS NB (ENV a0s path rdraw vals)); [apply env_agree_rejunk; rewrite HL; unfold NB; lia | exact knD_vars | exact HK].
      - exact HA.
      - regv HR (9%bv : reg). cbn [edenot ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV D_Mah0u.ENV]. exact E48.
      - regv HR (19%bv : reg). reflexivity.
      - regv HR (21%bv : reg). cbn [edenot ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV D_Mah0u.ENV]. exact E59.
      - regv HR (22%bv : reg). reflexivity.
      - exact AI0.
      - exact MI.
      - split; [exact LIVE | exact ONLY | change (cap 0) with 65536%Z; exact (conj LB NL) | intros i Hi; lia | lia | change (cap 0) with 65536%Z; lia | lia].
      - split.
        + unfold m_fs. rewrite FS. reflexivity.
        + unfold m_fds. rewrite FD. reflexivity.
        + unfold m_fds. rewrite FD. reflexivity.
        + unfold m_fds. rewrite FD. reflexivity.
        + exact Hh.
        + exact Hl.
    Qed.

    Theorem ref_file_exists :
      realizes RSEGS (mkCfg (mkst regs0 (0x17b64 : word) mem0 (seg_rom RSEGS))
                            (D_Mah0u.model0 sp0 a0s path envv tid brk mbase fs0 stdin0))
               (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened fdata fs0)).
    Proof.
      replace (0x17b64 : word) with (Z_to_bv 64 0x17b64) by (apply bv_eq; reflexivity).
      eapply rz_conseq.
      - apply (main_seg1 sp0 a0s path envv rdraw tid regs0 mem0 brk mbase fs0 stdin0 fdata Hva Hve Hvsp Htid ME Hfile Hpne Hpnd Hplen
                 (PXI sp0 tid brk mbase fs0 stdin0 (FdFile path (Z_to_bv 64 0)))).
        + (* [comment removed for export] *)
          intros M M' AG. unfold PXI. apply (init_ok_frame_win sp0 Hvsp HCEIL M M'). exact AG.
        + (* [comment removed for export] *)
          unfold PXI. pose proof Hbrk as (B1 & B2 & B3).
          apply (init_ok_entry sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp ME HCEIL); try reflexivity;
            try exact bw_limit_lim;   (* [comment removed for export] *)
            unfold model1, ceil_ok; rewrite m1_vmmaps; cbn [vm_start_brk vm_limit].
          * change (reserved_top (segments_reserved RSEGS)) with 405504%Z in B1. lia.
          * unfold page_size in B3. exact B3.
          all: try (unfold LIM; lia).
          * change (reserved_top (segments_reserved RSEGS)) with 405504%Z in B2. unfold brk_aslr_max in B2.
            rewrite HCEIL. pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. lia.
          * (* [comment removed for export] *)
            rewrite HCEIL. unfold alloc_top. cbn [vm_init_sp]. rewrite stack_max_size_val. reflexivity.
        + apply (open_err_branch_cannot_open sp0 a0s path envv rdraw tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp ME Hfit).
        + apply (main_M0 sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 (FdFile path (Z_to_bv 64 0)) Hvsp HCEIL _ after_M0).
      - apply t_alt2_congr_r. apply lshape_opened; unfold FUELF; change (cap 0) with 65536%Z; lia.
    Qed.
  End FileExists.

  (* [comment removed for export] *)
  Definition dir_ok : Prop :=
    forall (AMB : Amb) sp0 a0s envv rdraw tid regs0 mem0 brk mbase fs0 stdin0,
      valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 ->
      alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
      main_entry sp0 [a0s; dot_path] envv rdraw tid regs0 mem0 -> entry_stack_fits sp0 [a0s; dot_path] envv ->
      valid_brk RSEGS brk ->
      realizes RSEGS (mkCfg (mkst regs0 (0x17b64 : word) mem0 (seg_rom RSEGS))
                            (@D_Mah0u.model0 AMB _ sp0 a0s dot_path envv tid brk mbase fs0 stdin0))
               (t_alt2 (t_die (msg_cannot_open dot_path) fs0) (t_opened_dir dot_path fs0)).

  (* [comment removed for export] *)
  Definition body_all : Prop :=
    forall (AMB : Amb) sp0 a0s path envv rdraw tid regs0 mem0 fs0 fdata,
      valid_argv [a0s; path] -> valid_envp envv -> valid_sp sp0 ->
      alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
      main_entry sp0 [a0s; path] envv rdraw tid regs0 mem0 ->
      fs_lookup fs0 path = Some fdata -> (length path <= 4095)%nat ->
      @body_ok Clg AI sp0 a0s path envv rdraw tid mem0 fs0 fdata.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Theorem ref_realizes_spec :
    dir_ok -> body_all ->
    forall sp brk mbase rdraw (inp : ProcInput),
      valid_sp sp -> alloc_ceiling = (bv_unsigned sp - 8388608)%Z ->
      valid_brk rsegs brk ->
      valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
      entry_stack_fits sp (in_argv inp) (in_envp inp) ->
      in_abort_terminal inp = false ->
      realizes rsegs
        (init_config rsegs rpc rph sp brk mbase rdraw LIM inp)   (* [comment removed for export] *)
        (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros DIR BODYA sp brk mbase rdraw inp Hsp HCE Hbrk Hva Hve Hfit Hab.
    apply ref_startup; try assumption.
    intros tid regs mem Htid ME.
    replace (init_model (segments_reserved RSEGS) brk mbase sp LIM inp)
      with (init_model (segments_reserved RSEGS) brk mbase sp LIM
              (@mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)))
      by (rewrite (init_model_C_of _ _ _ _ _ inp Hab); reflexivity).   (* [comment removed for export] *)
    pose (AMB := amb_of inp). change (amb_of inp) with AMB in ME |- *.
    set (argv := in_argv inp) in *. set (envp := in_envp inp) in *. set (fs0 := in_fs inp) in *. set (stdin0 := in_stdin inp) in *.
    clearbody argv envp fs0 stdin0 AMB. clear Hab.
    destruct argv as [|a0s [|path [|x l]]].
    - apply (ref_usage_w sp [] envp rdraw tid regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Htid ME Hfit). cbn; lia.
    - apply (ref_usage_w sp [a0s] envp rdraw tid regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Htid ME Hfit). cbn; lia.
    - cbn [spec].
      destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort].
      + apply (ref_open_fail_toolong_w sp a0s path envp rdraw tid regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Htid ME Hfit Hlong).
      + destruct (list_byte_eqb path []) eqn:Hemp.
        * apply ref_list_byte_eqb_eq in Hemp.
          apply (ref_open_fail_empty_w sp a0s path envp rdraw tid regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Htid ME Hfit Hemp).
        * assert (Hne : path <> []) by (intros E; apply ref_list_byte_eqb_eq in E; rewrite E in Hemp; discriminate).
          destruct (list_byte_eqb path dot_path) eqn:Hdot.
          -- apply ref_list_byte_eqb_eq in Hdot. rewrite Hdot in *.
             apply (DIR AMB sp a0s envp rdraw tid regs mem brk mbase fs0 stdin0 Hva Hve Hsp HCE Htid ME Hfit Hbrk).
          -- assert (Hnd : path <> dot_path)
               by (intros E; apply ref_list_byte_eqb_eq in E; rewrite E in Hdot; discriminate).
             destruct (fs_lookup fs0 path) as [data|] eqn:Hlk.
             ++ apply (ref_file_exists sp a0s path envp rdraw tid regs mem brk mbase fs0 stdin0 data
                         Hva Hve Hsp HCE Htid ME Hfit Hbrk Hlk Hne Hnd ltac:(lia)
                         (BODYA AMB sp a0s path envp rdraw tid regs mem fs0 data Hva Hve Hsp HCE Htid ME Hlk ltac:(lia))).
             ++ apply (ref_open_fail_absent_w sp a0s path envp rdraw tid regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Htid ME Hfit
                         ltac:(lia) Hne Hnd Hlk).
    - apply (ref_usage_w sp (a0s :: path :: x :: l) envp rdraw tid regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Htid ME Hfit). cbn; lia.
  Qed.
End Main.
End D_Main.

From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Opxmp.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Amb OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_Re2vu OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_Rea7z OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Shapi1s OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Frame OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Li6dm OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Spec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibWbxd OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefNodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefNfmt OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Exvwg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Stqgu OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Exit OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefPl89 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Stmwg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Usk9e.D_Maca4 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MemSplit OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Kn21w OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u.D_MainA OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Alu7n OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Dr084 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Wamxh OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymAux OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_Reu44 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_MainM0 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_Main OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_InitOk OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Opxmp.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0 DriverKit.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)

Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

(* [comment removed for export] *)
Definition STOPS_D : list Z := [0x22fc4; 0x17d90; 0x25d58; 0x2299c]%Z.
Definition runD (dirs : list bool) (ss : sym_state) := sym_exec RSEGS 5000 true STOPS_D (SCR dirs [] []) ss [].
Definition knDd : list kentry := knD ++ [KRange (EVar 2) 0x7fff80000000 0x800000400000; KImg 0x62830 0x63000].
Definition rD1 := Eval vm_compute in runD [false; true; false] (SS 0x17bb8 sr_drv [] knDd 70).   (* [comment removed for export] *)
Definition srD1 : list expr := Eval vm_compute in s_regs (fst (fst rD1)).
Definition knD1 : list kentry := Eval vm_compute in fst (fst (carry (s_log (fst (fst rD1))) knDd [])).
Definition PC_RD : Z := Eval vm_compute in s_pc (fst (fst rD1)).
Definition srD2_0 : list expr := Eval vm_compute in sr_upd srD1 (ridx 10) (ELit (bv_unsigned (errno_ret EISDIR))).
Definition rD2 := Eval vm_compute in runD [] (SS (PC_RD + 4) srD2_0 [] knD1 70).
Definition srD2 : list expr := Eval vm_compute in s_regs (fst (fst rD2)).
Definition knD2 : list kentry := Eval vm_compute in fst (fst (carry (s_log (fst (fst rD2))) knD1 [])).
Lemma rD1_pc : PC_RD = 0x2b778%Z. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma knRE0_incl : kn_incl knRE0 knD2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma fetch_rd : fetch_word RSEGS (Z_to_bv 64 PC_RD) = Some ECALLW. Proof. vm_compute. reflexivity. Qed.

Section Dir.
  Context {AMB : Amb} {Clg : Ceiling} {AI : AllocSpec LayoutP0} {DK : DriverKit LayoutP0 InitP0}.
  Variable sp0 : word.
  Variable a0s : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variables brk mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Let path : list byte := dot_path.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  (* [comment removed for export] *)
  Hypothesis HCEIL : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv rdraw tid regs0 mem0.
  Hypothesis Hfit : entry_stack_fits sp0 [a0s; path] envv.   (* [comment removed for export] *)
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Lemma Hplen : (length path <= 4095)%nat. Proof. cbn. lia. Qed.

  (* [comment removed for export] *)
  Definition PX : (word -> option byte) -> Prop := PXI sp0 tid brk mbase fs0 stdin0 FdDir.
  #[using="HCEIL Hvsp"] Lemma PX_frame : forall M M' : word -> option byte,
    (forall x : word, ~ (bv_unsigned sp0 - 8388608 <= bv_unsigned x < bv_unsigned sp0)%Z -> M' x = M x) -> PX M -> PX M'.
  Proof. intros M M' AG. unfold PX, PXI. apply (init_ok_frame_win sp0 Hvsp HCEIL M M'). exact AG. Qed.
  #[using="Hbrk ME HCEIL Hvsp Hve Hva path regs0 rdraw envv a0s"] Lemma PX0 : PX mem0.
  Proof.
    unfold PX, PXI. pose proof Hbrk as (B1 & B2 & B3).
    apply (init_ok_entry sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp ME HCEIL); try reflexivity;
      try exact bw_limit_lim;   (* [comment removed for export] *)
      unfold ceil_ok; rewrite m1_vmmaps; cbn [vm_start_brk vm_limit].
    - change (reserved_top (segments_reserved RSEGS)) with 0x63000%Z in B1. lia.
    - unfold page_size in B3. exact B3.
    all: try (unfold LIM; lia).
    - change (reserved_top (segments_reserved RSEGS)) with 0x63000%Z in B2. unfold brk_aslr_max in B2.
      rewrite HCEIL. pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. lia.
    - rewrite HCEIL. unfold alloc_top. cbn [vm_init_sp]. rewrite stack_max_size_val. reflexivity.
  Qed.

  #[using="Hbrk ME Htid HCEIL Hvsp Hve Hva"] Lemma dir_seg1 : forall KA KB,
    open_err_branch sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 KA ->
    after_open_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 PX FdDir KB ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x17b64) mem0 (seg_rom RSEGS)) (model0 sp0 a0s path envv tid brk mbase fs0 stdin0))
               (t_alt2 KA KB).
  Proof.
    intros KA KB HKA HKB.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (main_regs_ok sp0 a0s path envv rdraw tid regs0 mem0 Hvsp Htid ME) as HR.
    pose proof (main_know_ok sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
    change (E0 sp0 a0s path envv rdraw tid regs0) with (ENV a0s path rdraw (vals0 sp0 a0s path envv tid regs0)) in HR, HK.
    set (vals := vals0 sp0 a0s path envv tid regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 sp0 a0s path envv) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 sp0 a0s path envv) by reflexivity.
    assert (P5t : vals_ev vals 5 = tid) by reflexivity.
    (first [ pose proof ((main_str sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia))) as dR_1; dand4 dR_1 as Sr Slo Shi Slen | destruct (main_str sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen) ]).
    cbn [nth] in Sr, Slo, Shi, Slen.
    clearbody vals.
    (* [comment removed for export] *)
    run_block_keep scr0 38%nat.
    (* [comment removed for export] *)
    assert (Sr' : rdn RSEGS M (p1 sp0 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM. unfold p1. rewrite (rdn_mem_denot_above RSEGS (ENV a0s path rdraw vals) mem0 _ 0%nat 0x63000);
        [exact Sr | vm_compute; reflexivity | cbn [ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV D_Mah0u.ENV]; rewrite P0; lia | cbn [ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV D_Mah0u.ENV]; rewrite P0; lia | lia
        | pose proof (u64_range (cat_argv_ptr sp0 [a0s; path] envv 1)); lia]. }
    (* [comment removed for export] *)
    eapply (rz_openat_dot RSEGS _ _ _ (model0 sp0 a0s path envv tid brk mbase fs0 stdin0) ECALLW); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). apply bv_eq. reflexivity.
    - regv HR (12 : reg). vm_compute. reflexivity.
    - (* [comment removed for export] *) rewrite (m0_fds sp0 a0s path envv tid brk mbase fs0 stdin0). rewrite alloc_fd_fds0. apply fd_lookup_fds0_3.
    - (* [comment removed for export] *) split; [exact Hplen|]. split; [apply (path_nonul a0s path Hva)|].
      regv HR (11 : reg). cbn [edenot ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV D_Mah0u.ENV]. rewrite P2. exact Sr'.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0x2b778 + 4)%Z with 0x2b77c%Z.
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path rdraw))) with (ENV a0s path rdraw (vals ++ [errno_ret e])) in HR2, HK2.
      eapply (HKA e (vals ++ [errno_ret e])); try eassumption.
      + rewrite length_app, HL. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      + rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P5t.
      + apply regs_set_a0; [exact HR2|]. cbn [edenot ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV D_Mah0u.ENV].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + intros x Hx. rewrite EQM. apply (mem_denot_above (ENV a0s path rdraw vals) mem0 _ 0%nat 0x63000);
          [vm_compute; reflexivity | cbn [ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV D_Mah0u.ENV]; rewrite P0; lia | cbn [ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV D_Mah0u.ENV]; rewrite P0; lia | lia].
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x2b778 + 4)%Z with 0x2b77c%Z.
      rewrite (m0_fds sp0 a0s path envv tid brk mbase fs0 stdin0). rewrite alloc_fd_fds0.
      change (with_fds (fd_insert fds0 (Z_to_bv 64 3) FdDir) (model0 sp0 a0s path envv tid brk mbase fs0 stdin0))
        with (model1g sp0 tid brk mbase fs0 stdin0 FdDir).
      pose proof (regs_set_a0 (ENV a0s path rdraw vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2.
      assert (HA : above_sp0 sp0 mem0 M).
      { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV a0s path rdraw vals) mem0 _ 0%nat 0x63000);
          [vm_compute; reflexivity | cbn [ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV D_Mah0u.ENV]; rewrite P0; lia | cbn [ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV D_Mah0u.ENV]; rewrite P0; lia | lia]. }
      lazymatch goal with EQ : ?Mn = mem_denot _ ?Mo ?lg |- _ =>
        assert (HP : PX Mn) by (rewrite EQ; apply (PX_block sp0 a0s path rdraw Hvsp Hplen PX PX_frame vals Mo lg P0 (proj1 logA_cov) (proj2 logA_cov) PX0)) end.
      eapply (main_segB_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 Hvsp Hplen PX PX_frame FdDir KB vals); try eassumption.
  Qed.


  (* [comment removed for export] *)
  #[using="Hvsp"] Lemma srRE0_ok : forall (vals6 : list word) R,
    length vals6 = 6%nat -> nth 0 vals6 (Z_to_bv 64 0) = sp0 ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0x42158 ->
    getr R 18 = nth 2 vals6 (Z_to_bv 64 0) ->
    regs_ok (OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV a0s path rdraw (vals6 ++ junk_vals R ++ [Z_to_bv 64 0])) srRE0 R.
  Proof.
    intros vals6 R HL V0 P2 P3 P4 P18.
    pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. pose proof (u64_range sp0).
    destruct vals6 as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 l]]]]]]]; cbn in HL; try lia. cbn [nth] in V0, P18. subst x0.
    assert (HJ : forall i, (i < 32)%nat -> vals_ev ([sp0; x1; x2; x3; x4; x5] ++ junk_vals R ++ [Z_to_bv 64 0]) (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i))).
    { intros i Hi. unfold vals_ev. change (6 + i)%nat with (length [sp0; x1; x2; x3; x4; x5] + i)%nat.
      rewrite app_nth2_plus, app_nth1 by (rewrite junk_vals_length; exact Hi). unfold junk_vals.
      rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity. }
    apply regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth srRE0 all_regs];
      try (lazymatch goal with |- _ = edenot _ (EVar ?n) =>
             change (edenot (OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV a0s path rdraw ([sp0; x1; x2; x3; x4; x5] ++ junk_vals R ++ [Z_to_bv 64 0])) (EVar n))
               with (vals_ev ([sp0; x1; x2; x3; x4; x5] ++ junk_vals R ++ [Z_to_bv 64 0]) n);
             first [ let i := eval vm_compute in (n - 6)%nat in
                     etransitivity; [| symmetry; exact (HJ i ltac:(lia))]; f_equal; apply bv_eq; reflexivity
                   | exact P18 ] end).
    - rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV]. change (vals_ev _ 0) with sp0. rewrite P2. f_equal; lia.
    - exact P3.
    - exact P4.
  Qed.

  Lemma knRE0_vars : kn_vars_lt 6 knRE0 = true. Proof. vm_compute. reflexivity. Qed.
  #[using="Htid tid"] Lemma knD_img_top : In (KImg 0x62804 0x63000) knD. Proof. vm_compute. tauto. Qed.

  (* [comment removed for export] *)
  #[using="ME Htid HCEIL Hvsp Hve Hva regs0"] Lemma dir_body : post_M0 sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 FdDir (t_die (msg_read_error path) fs0).
  Proof.
    intros vals R M md A b HB HJ HP HK0 G10 Hb G21 AI0 MI MF _ _ LIVE ONLY HA.   (* [comment removed for export] *)
    (first [ pose proof (HB) as dR_2; dand5 dR_2 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]).
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp.
    (first [ pose proof ((block_range sp0 path [] HCEIL ltac:(cbn; lia) A M md b 65536 AI0 LIVE)) as dR_3; dand4 dR_3 as _ Hb16 HbLO HbHI | destruct (block_range sp0 path [] HCEIL ltac:(cbn; lia) A M md b 65536 AI0 LIVE) as (_ & Hb16 & HbLO & HbHI) ]). unfold HEAP_LO, LOW_HI in HbLO.
    pose proof (sr_drv_ok sp0 a0s path envv rdraw tid Hvsp vals R HB HJ HP) as HR.
    assert (E48 : vals_ev vals 48 = Z_to_bv 64 b) by (rewrite <- G10; exact (HJ 10%nat ltac:(lia))).
    assert (E59 : vals_ev vals 59 = Z_to_bv 64 65536) by (rewrite <- G21; exact (HJ 21%nat ltac:(lia))).
    assert (Hh : m_halted md = None) by (destruct (as_lazy_nil A M md AI0) as [_ X]; exact X).
    assert (Hl : m_vm_lazy md = []) by (destruct (as_lazy_nil A M md AI0) as [X _]; exact X).
    (first [ dand4 MF as FD _ FS _ | destruct MF as (FD & _ & FS & _) ]).
    assert (Hfd3 : fd_lookup (m_fds md) (Z_to_bv 64 3) = Some FdDir) by (unfold m_fds; rewrite FD; reflexivity).
    assert (Hfd2 : fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by (unfold m_fds; rewrite FD; reflexivity).
    assert (Hfs : m_fs md = fs0) by (unfold m_fs; rewrite FS; reflexivity).
    (first [ pose proof ((main_strN sp0 [a0s; path] envv rdraw tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(cbn; lia))) as dR_5; dand6 dR_5 as Sr Slo Shi Slen t8 Ht8 | destruct (main_strN sp0 [a0s; path] envv rdraw tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(cbn; lia)) as (Sr & Slo & Shi & Slen & t8 & Ht8) ]).
    cbn [nth length Nat.add app] in Sr, Slo, Shi, Ht8. change (cat_argv_ptr sp0 [a0s; path] envv 1) with (p1 sp0 a0s path envv) in Sr, Slo, Shi, Ht8.
    pose proof (u64_range (p1 sp0 a0s path envv)) as Hpp.
    (* [comment removed for export] *)
    assert (HK : know_ok RSEGS (OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV a0s path rdraw vals) M knDd).
    { unfold knDd. apply know_ok_app; [exact HK0|]. constructor; [| constructor; [| constructor]].
      - apply krange_intro. cbn [edenot ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV]. rewrite V2. lia.
      - eapply kimg_sub; [eapply know_ok_In; [exact HK0| exact knD_img_top] | lia | lia]. }
    clear HK0 HJ HP.
    (* [comment removed for export] *)
    run_block_gen 5000%nat STOPS_D (SCR [false; true; false] [] []) 70%nat true.
    { cbn [sc_denot edenot ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV]. rewrite E59. apply bt_ltu_Z; [lia| lia|]. apply Z.ltb_ge. lia. }
    { cbn [sc_denot edenot ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV]. rewrite E59. cbn [branch_taken]. unfold bv_eqb. rewrite !u_small by lia. reflexivity. }
    { cbn [sc_denot edenot ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV]. rewrite E48, bt_eq0_Z by lia. apply Z.eqb_neq. lia. }
    rename EQM into EQM1.
    assert (G1 : mem_grows M M0) by (rewrite EQM1; apply mem_denot_grows).
    eapply (rz_read_dir_mapped RSEGS R0 (Z_to_bv 64 PC_RD) M0 md ECALLW (Z_to_bv 64 3) 65536).
    - exact fetch_rd.
    - apply is_ecall_ECALLW.
    - exact Hh.
    - exact Hl.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). reflexivity.
    - rewrite u_small by lia. lia.
    - exact Hfd3.
    - regv HR (12 : reg). reflexivity.
    - lia.
    - lia.
    - (* [comment removed for export] *) regv HR (11 : reg). cbn [edenot ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV]. rewrite u_small by lia. unfold TASK_SIZE. lia.
    - regv HR (11 : reg). cbn [edenot ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV]. apply store_ok_data; rewrite u_small by lia; lia.
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by (rewrite rD1_pc; lia).
      pose proof (regs_ok_upd (OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV a0s path rdraw vals) srD1 R0 10 (errno_ret EISDIR) (ELit (bv_unsigned (errno_ret EISDIR))) HR
                    ltac:(cbn [edenot]; apply Z_to_bv_bv_unsigned)) as HR2.
      lazymatch type of HR2 with regs_ok ?E (if _ then _ else _) (if _ then _ else ?R') =>
        change (regs_ok E srD2_0 R') in HR2 end.
      clear HR. rename HR2 into HR.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?RR (Z_to_bv 64 ?pcv) _ _) _) _ => change pcv with (PC_RD + 4)%Z end.
      run_block_gen 5000%nat STOPS_D (SCR [] [] []) 70%nat true.
      rename EQM into EQM2.
      (* [comment removed for export] *)
      assert (HA2 : forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M1 x = mem0 x).
      { intros x Hx. rewrite EQM2. rewrite (mem_denot_above (OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV a0s path rdraw vals) M0 _ 0%nat 0x63000);
          [| vm_compute; reflexivity | cbn [ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV]; rewrite V0; lia | cbn [ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV]; rewrite V0; lia | lia].
        rewrite EQM1. rewrite (mem_denot_above (OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV a0s path rdraw vals) M _ 0%nat 0x63000);
          [| vm_compute; reflexivity | cbn [ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV]; rewrite V0; lia | cbn [ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV]; rewrite V0; lia | lia].
        apply HA. exact Hx. }
      rewrite <- Hfs. unfold path.
      change path with dot_path in Slo. change path with dot_path in Shi. change path with dot_path in Hpp.
      change path with dot_path in Sr. change path with dot_path in Ht8.
      change (length dot_path) with 1%nat in Sr. change (Z.of_nat (length dot_path)) with 1%Z in Ht8.
      apply (re_tail sp0 (blobs0 a0s dot_path rdraw) md Hvsp Hh Hl Hfd2 dot_path (p1 sp0 a0s dot_path envv) t8
               (firstn 6 vals ++ junk_vals R1 ++ [Z_to_bv 64 0]) R1 M1).
      + cbn. intros [E|[]]. apply (f_equal bv_unsigned) in E. vm_compute in E. lia.
      + cbn. lia.
      + rewrite !length_app, length_firstn, junk_vals_length, HL. reflexivity.
      + unfold vals_ev. rewrite app_nth1 by (rewrite length_firstn, HL; lia). rewrite nth_firstn. exact V0.
      + unfold vals_ev. rewrite app_nth1 by (rewrite length_firstn, HL; lia). rewrite nth_firstn. exact V2.
      + exact Slo.
      + change (Z.of_nat (length dot_path)) with 1%Z. lia.
      + apply (srRE0_ok (firstn 6 vals) R1); rewrite ?length_firstn, ?HL, ?nth_firstn; try reflexivity.
        * exact V0.
        * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV]. rewrite V0. f_equal; lia.
        * regv HR (3 : reg). reflexivity.
        * regv HR (4 : reg). reflexivity.
        * regv HR (18 : reg). cbn [edenot ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV]. reflexivity.
      + apply (know_ok_agree RSEGS 6 (OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV a0s path rdraw vals)).
        * split; [|reflexivity]. intros i Hi. cbn [ev OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0.ENV D_Rec7j.ENV]. unfold vals_ev. rewrite app_nth1 by (rewrite length_firstn, HL; lia). rewrite nth_firstn.
          apply Nat.ltb_lt in Hi. rewrite Hi. reflexivity.
        * exact knRE0_vars.
        * apply (know_ok_incl RSEGS _ M1 knRE0 knD2 knRE0_incl). exact HK.
      + change (length dot_path) with 1%nat. rewrite <- Sr. apply rdn_agree. intros j Hj. apply HA2. rewrite u_small by lia. lia.
      + change (Z.of_nat (length dot_path)) with 1%Z. rewrite <- Ht8. apply rdn_agree. intros j Hj. apply HA2.
        rewrite (u_small (bv_unsigned (p1 sp0 a0s dot_path envv) + 1)) by lia. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Hbrk Hfit ME Htid HCEIL Hvsp Hve Hva rdraw DK AI Clg"] Theorem dir_run :
    realizes RSEGS (mkCfg (mkst regs0 (0x17b64 : word) mem0 (seg_rom RSEGS)) (model0 sp0 a0s path envv tid brk mbase fs0 stdin0))
             (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir path fs0)).
  Proof.
    replace (0x17b64 : word) with (Z_to_bv 64 0x17b64) by (apply bv_eq; reflexivity).
    unfold t_opened_dir.
    apply dir_seg1.
    - apply (open_err_branch_cannot_open sp0 a0s path envv rdraw tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp ME Hfit).
    - apply (main_M0 sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 FdDir Hvsp HCEIL _ dir_body).
  Qed.
End Dir.

(* [comment removed for export] *)
Theorem dir_ok_holds {Clg : Ceiling} {AI : AllocSpec LayoutP0} {DK : DriverKit LayoutP0 InitP0} : dir_ok.
Proof.
  intros AMB sp0 a0s envv rdraw tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp HCEIL Htid ME Hfit Hbrk.
  exact (dir_run sp0 a0s envv rdraw tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp HCEIL Htid ME Hfit Hbrk).
Qed.
