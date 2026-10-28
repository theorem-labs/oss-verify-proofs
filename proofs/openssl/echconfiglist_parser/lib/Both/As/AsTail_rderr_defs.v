(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4 SymAux.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AsShadow AsPrintfFirst AsSxKit AsStdioCall.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Definition AMEMCPY : Z := 0x5699dc.          (* [comment removed for export] *)
Definition AMEMCPY_RET : Z := 0x1be8ec.       (* [comment removed for export] *)
Definition ASTRNLEN_TR : Z := 0x1a86fc.       (* [comment removed for export] *)
Definition ASTRNLEN_RET : Z := 0x1a8b78.      (* [comment removed for export] *)
Definition ASTDIO_WRITE : Z := 0x56407c.
Definition AEXIT : Z := 0x55e55c.
Definition AMAINEPI : Z := 0x1eef20.          (* [comment removed for export] *)
Definition ARIP : Z := 0x1c1068.              (* [comment removed for export] *)
Definition STOPT : list Z := [AMEMCPY; ASTRNLEN_TR; ASTDIO_WRITE; AEXIT; AMAINEPI; ARIP].
Definition FUELT : nat := 20000.
Definition scr0 : scripts := SCR [] [] [].
Definition runT (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUELT true STOPT scr ss [].
Definition kn_afterT (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition sc_of (nv : nat) (sr : list expr) (kn : list kentry) : stdio_res :=
  match stdio_call nv sr kn with
  | Some r => r
  | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] []
  end.
Definition KEPT_MC : list nat := map ridx callee_kept.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition KEPT_MCI : list nat := List.filter (fun i => negb (Nat.eqb i 19 || Nat.eqb i 20)) KEPT_MC.
Definition KEPT_CS : list nat := map ridx callee_saved.    (* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
(* [comment removed for export] *)
Definition rip_clob (i : nat) : bool :=
  match i with 5 | 11 | 12 | 13 | 14 | 15 | 16 | 17 => true | _ => false end%nat.
Definition after_rip (base : nat) (sr : list expr) : list expr :=
  map (fun i => if rip_clob i then EVar (base + i) else match i with 10%nat => ELit 0 | _ => nth i sr (ELit 0) end) (seq 0 32).
Definition RIP_FR : Z := 80.
Definition OT_FR : Z := 6000.                (* [comment removed for export] *)
Definition FMT : Z := 0x3d339.
Definition NPRE : Z := 19.
Definition NSUF : Z := 1.                (* [comment removed for export] *)
Definition IHI : Z := 0x80000000.            (* [comment removed for export] *)
Definition BUF_LO : Z := (-592).
Definition BUF_HI : Z := (-512).
Definition PX : expr := EVar 141.            (* [comment removed for export] *)

(* [comment removed for export] *)
Definition srV0 : list expr :=
  map (fun i => match i with
    | 0 => ELit 0 | 1 => ELit 0x1ad98c | 2 => spx (-240) | 4 => ELit 0xbe1c90
    | 8 => ELit FMT | 9 => ELit 0x5edca8 | 10 => ELit 0x5edca8 | 11 => ELit FMT | 12 => spx (-176) | 18 => spx (-176)
    | _ => EVar (35 + i) end)%nat (seq 0 32).

(* [comment removed for export] *)
Definition ot_cells : list (Z * nat * Z) :=
  [(0x5ea8e0, 8%nat, 0x56571c); (0x5eaa68, 8%nat, 0x5699dc); (0x5eaa70, 8%nat, 0x569e10); (0x5eaa18, 8%nat, 0x56a5b0); (0x5ea890, 8%nat, 0x5698e0);
   (0x6aa8f8, 8%nat, 0x7fff8000); (0x6ab5d8, 1%nat, 0x1); (0x6ab5d9, 1%nat, 0x1); (0x73c47c, 1%nat, 0x1); (0x73c523, 1%nat, 0x1);
   (0x5edca8, 4%nat, 0x5); (0x5edcc8, 8%nat, 0x0); (0x5edcd0, 8%nat, 0x0); (0x5edce0, 8%nat, 0x0); (0x5edcf0, 8%nat, 0x56407c);
   (0x5edd00, 8%nat, 0xc02398); (0x5edd08, 8%nat, 0x0); (0x5edd20, 4%nat, 0x2); (0x5edd30, 4%nat, 0x0); (0x5edd34, 4%nat, 0xffffffff); (0x5edd38, 4%nat, 0xffffffff);
   (0x7ffffa58, 8%nat, 0x0); (0x7ffffa60, 8%nat, 0x0); (0x7ffffa68, 8%nat, 0x0)].

(* [comment removed for export] *)
Definition OT_SHOFFS : list Z := [(-592); (-574)].
Definition OT_SHOFFS2 : list Z := [(-592); (-574); (-573)].
Definition OT_SHX : list expr := [(EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EVar 2) (EVar 141)) (ELit (-1))) (ELit 3)) (ELit 2147450880)) (ELit (-8))); (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EVar 2) (ELit 3)) (ELit 2147450880)) (ELit (-8))); (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) (EVar 141)) (ELit (-574))) (ELit 3)) (ELit 2147450880)) (ELit (-8))); (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) (EVar 141)) (ELit (-573))) (ELit 3)) (ELit 2147450880)) (ELit (-8)))].
Fixpoint shxkn (l : list expr) : list kentry :=
  match l with [] => [] | e :: r => KRange e 0x20000000000 0x10007fff8000 :: KZero (SA e 0) (ELit 8) :: shxkn r end.

Definition knV0 : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000; KWr (SA (EVar 0) (-128 - OT_FR)) OT_FR;
   KRange (EVar 2) AHI_LO AAPP_HI;
   KImg 0x10000 0x195000; KImg 0x571000 0x5ea000;
   KWord (SA (EVar 0) (-176)) 8 (EVar 2); KWord (SA (EVar 0) (-184)) 8 (ELit 0x1eef88);
   KWord (SA (EVar 0) (-192)) 8 (EVar 11); KWord (SA (EVar 0) (-200)) 8 (EVar 12); KWord (SA (EVar 0) (-208)) 8 (EVar 21);
   KWord (SA (ELit 0) 0xc01cd0) 8 (EVar 1); KWr (SA (ELit 0) 0x5edca8) 232]
  ++ shkn OT_SHOFFS
  ++ kn_cells ot_cells.
(* [comment removed for export] *)
Definition not_px_range (k : kentry) : bool := match k with KRange (EVar 141) _ _ => false | _ => true end.
Definition px_range (lo hi : Z) (kn : list kentry) : list kentry := KRange PX lo hi :: List.filter not_px_range kn.
(* [comment removed for export] *)
Definition kn_readd (plo phi : Z) (kn : list kentry) : list kentry := px_range plo phi (shxkn OT_SHX ++ shkn OT_SHOFFS2 ++ kn).

(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x56571c srV0 [] knV0 67.
Definition rB := Eval vm_compute in runT (SCR [false] [] []) ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_afterT rB knV0.
(* [comment removed for export] *)
Definition logM1 : list sentry := [SE (SA (EVar 0) (-574)) 1 (ELit 32);
   SE (SA (EVar 0) (-576)) 2 (ELit 28271);
   SE (SA (EVar 0) (-584)) 8 (ELit 2338053693894893668);
   SE (SA (EVar 0) (-592)) 8 (ELit 7018141077071293539)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 67.
(* [comment removed for export] *)
Definition ssC0 : sym_state := SS AMEMCPY_RET srC0 [] knC0 99.
Definition rC := Eval vm_compute in runT (SCR [] [] []) ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_afterT rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 99.
(* [comment removed for export] *)
Definition ssD0 : sym_state := SS AMEMCPY_RET srD0 [] knC 131.
Definition rD := Eval vm_compute in runT (SCR [] [] []) ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_afterT rD knC.
(* [comment removed for export] *)
Definition knE0 : list kentry := Eval vm_compute in kn_readd 0 131071 (kn_cut 0 (-1152 - 4400) (-1152) IHI knD).
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 131.
(* [comment removed for export] *)
Definition ssE0 : sym_state := SS ASTRNLEN_RET srE0 [] knE0 163.
Definition rE := Eval vm_compute in runT (SCR [false] [ELit 0] []) ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_afterT rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 163.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FQMAX : Z := 61.
Definition knF0_ : list kentry := Eval vm_compute in px_range 1 FQMAX knE.
Definition ssF0 : sym_state := SS AMEMCPY_RET srF0 [] knF0_ 195.
Definition rF := Eval vm_compute in runT (SCR [true; false; true; false; false] [] []) ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_afterT rF knF0_.
Definition knG0 : list kentry := Eval vm_compute in kn_readd 0 60 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF).
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MCI 195.
(* [comment removed for export] *)
Definition knF00 : list kentry := Eval vm_compute in px_range 0 0 knE.
Definition rF0 := Eval vm_compute in runT (SCR [false; true] [] []) (SS AMEMCPY_RET srF0 [] knF00 195).
Definition srF0' : list expr := Eval vm_compute in s_regs (fst (fst rF0)).
Definition knF0' : list kentry := Eval vm_compute in kn_afterT rF0 knF00.
Definition knG00 : list kentry := Eval vm_compute in kn_readd 0 60 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF0').
(* [comment removed for export] *)
Definition ssG0 : sym_state := SS AMEMCPY_RET srG0 [] knG0 227.
Definition rG := Eval vm_compute in runT (SCR [false] [] []) ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_afterT rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_readd 0 60 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knG).
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 227.
(* [comment removed for export] *)
Definition ssH0 : sym_state := SS AMEMCPY_RET srH0 [] knH0 259.
Definition rH := Eval vm_compute in runT (SCR [] [] []) ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_afterT rH knH0.
Definition scOF : stdio_res := Eval vm_compute in sc_of 259 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.
(* [comment removed for export] *)
Definition ssI0 : sym_state := SS 0x565844 srI0 [] knI0 291.
Definition rI := Eval vm_compute in runT (SCR [] [] []) ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_afterT rI knI0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knG30 : list kentry := Eval vm_compute in kn_readd (60 + 1) (60 + NSUF) (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF).
Definition ssG30 : sym_state := SS AMEMCPY_RET srG0 [] knG30 227.
Definition rG3 := Eval vm_compute in runT (SCR [] [] []) ssG30.
Definition srG3 : list expr := Eval vm_compute in s_regs (fst (fst rG3)).
Definition knG3 : list kentry := Eval vm_compute in kn_afterT rG3 knG30.
Definition scG3 : stdio_res := Eval vm_compute in sc_of 227 srG3 knG3.
Definition srH30 : list expr := Eval vm_compute in sc_sr scG3.
Definition knH30 : list kentry := Eval vm_compute in sc_kn scG3.
(* [comment removed for export] *)
Definition ssH30 : sym_state := SS (sc_ret scG3) srH30 [] knH30 259.
Definition rH3 := Eval vm_compute in runT (SCR [] [] []) ssH30.
Definition srH3 : list expr := Eval vm_compute in s_regs (fst (fst rH3)).
Definition knH3 : list kentry := Eval vm_compute in kn_afterT rH3 knH30.
Definition scH3 : stdio_res := Eval vm_compute in sc_of 259 srH3 knH3.
Definition srI30 : list expr := Eval vm_compute in sc_sr scH3.
Definition knI30 : list kentry := Eval vm_compute in sc_kn scH3.
(* [comment removed for export] *)
Definition ssI30 : sym_state := SS 0x565844 srI30 [] knI30 291.
Definition rI3 := Eval vm_compute in runT (SCR [] [] []) ssI30.
Definition srI3 : list expr := Eval vm_compute in s_regs (fst (fst rI3)).
Definition knI3 : list kentry := Eval vm_compute in kn_afterT rI3 knI30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knF40 : list kentry := Eval vm_compute in px_range (60 + NSUF + 1) 131071 knE.
Definition ssF40 : sym_state := SS AMEMCPY_RET srF0 [] knF40 195.
Definition rF4 := Eval vm_compute in runT (SCR [true] [] []) ssF40.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_afterT rF4 knF40.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 195 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in kn_readd (60 + NSUF + 1) 131071 (sc_kn scF4).
(* [comment removed for export] *)
Definition ssG40 : sym_state := SS (sc_ret scF4) srG40 [] knG40 227.
Definition rG4 := Eval vm_compute in runT (SCR [false] [] []) ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 : list kentry := Eval vm_compute in kn_afterT rG4 knG40.
(* [comment removed for export] *)
Definition logNL : list sentry := [SE (SA (EVar 0) (-592)) 1 (ELit 10)].
Definition knH40 : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 227.
(* [comment removed for export] *)
Definition ssH40 : sym_state := SS AMEMCPY_RET srH40 [] knH40 259.
Definition rH4 := Eval vm_compute in runT (SCR [] [] []) ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_afterT rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 259 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.
(* [comment removed for export] *)
Definition ssI40 : sym_state := SS 0x565844 srI40 [] knI40 291.
Definition rI4 := Eval vm_compute in runT (SCR [] [] []) ssI40.
Definition srI4 : list expr := Eval vm_compute in s_regs (fst (fst rI4)).
Definition knI4 : list kentry := Eval vm_compute in kn_afterT rI4 knI40.

(* [comment removed for export] *)
Definition ot_regions : list sregion := [(SA (EVar 0) (-128 - OT_FR), OT_FR); (SA (ELit 0) 0x5edca8, 232)].
Definition scsB : list sidecond := Eval vm_compute in (snd (fst rB)).
Lemma factsB : snd (fst rB) = scsB /\ snd (fst (carry (s_log (fst (fst rB))) knV0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rB))) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition scsC : list sidecond := Eval vm_compute in (snd (fst rC)).
Lemma factsC : snd (fst rC) = scsC /\ snd (fst (carry (s_log (fst (fst rC))) knC0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rC))) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition scsD : list sidecond := Eval vm_compute in (snd (fst rD)).
Lemma factsD : snd (fst rD) = scsD /\ snd (fst (carry (s_log (fst (fst rD))) knC [])) = [] /\ log_covered ot_regions (s_log (fst (fst rD))) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition scsE : list sidecond := Eval vm_compute in (snd (fst rE)).
Lemma factsE : snd (fst rE) = scsE /\ snd (fst (carry (s_log (fst (fst rE))) knE0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rE))) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition scsF : list sidecond := Eval vm_compute in (snd (fst rF)).
Lemma factsF : snd (fst rF) = scsF /\ snd (fst (carry (s_log (fst (fst rF))) knF0_ [])) = [] /\ log_covered ot_regions (s_log (fst (fst rF))) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition scsF0 : list sidecond := Eval vm_compute in (snd (fst rF0)).
Lemma factsF0 : snd (fst rF0) = scsF0 /\ snd (fst (carry (s_log (fst (fst rF0))) knF00 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rF0))) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition scsG : list sidecond := Eval vm_compute in (snd (fst rG)).
Lemma factsG : snd (fst rG) = scsG /\ snd (fst (carry (s_log (fst (fst rG))) knG0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rG))) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition scsH : list sidecond := Eval vm_compute in (snd (fst rH)).
Lemma factsH : snd (fst rH) = scsH /\ snd (fst (carry (s_log (fst (fst rH))) knH0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rH))) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition scsI : list sidecond := Eval vm_compute in (snd (fst rI)).
Lemma factsI : snd (fst rI) = scsI /\ snd (fst (carry (s_log (fst (fst rI))) knI0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rI))) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition scsG3 : list sidecond := Eval vm_compute in (snd (fst rG3)).
Lemma factsG3 : snd (fst rG3) = scsG3 /\ snd (fst (carry (s_log (fst (fst rG3))) knG30 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rG3))) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition scsH3 : list sidecond := Eval vm_compute in (snd (fst rH3)).
Lemma factsH3 : snd (fst rH3) = scsH3 /\ snd (fst (carry (s_log (fst (fst rH3))) knH30 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rH3))) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition scsI3 : list sidecond := Eval vm_compute in (snd (fst rI3)).
Lemma factsI3 : snd (fst rI3) = scsI3 /\ snd (fst (carry (s_log (fst (fst rI3))) knI30 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rI3))) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition scsF4 : list sidecond := Eval vm_compute in (snd (fst rF4)).
Lemma factsF4 : snd (fst rF4) = scsF4 /\ snd (fst (carry (s_log (fst (fst rF4))) knF40 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rF4))) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition scsG4 : list sidecond := Eval vm_compute in (snd (fst rG4)).
Lemma factsG4 : snd (fst rG4) = scsG4 /\ snd (fst (carry (s_log (fst (fst rG4))) knG40 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rG4))) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition scsH4 : list sidecond := Eval vm_compute in (snd (fst rH4)).
Lemma factsH4 : snd (fst rH4) = scsH4 /\ snd (fst (carry (s_log (fst (fst rH4))) knH40 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rH4))) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition scsI4 : list sidecond := Eval vm_compute in (snd (fst rI4)).
Lemma factsI4 : snd (fst rI4) = scsI4 /\ snd (fst (carry (s_log (fst (fst rI4))) knI40 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rI4))) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma ot_itinerary :
  (s_pc (fst (fst rB)), s_pc (fst (fst rC)), s_pc (fst (fst rD)), s_pc (fst (fst rE))) = (AMEMCPY, AMEMCPY, ASTRNLEN_TR, AMEMCPY)
  /\ (s_pc (fst (fst rF)), s_pc (fst (fst rF0)), s_pc (fst (fst rG)), s_pc (fst (fst rH)), s_pc (fst (fst rI))) = (AMEMCPY, AMEMCPY, AMEMCPY, ASTDIO_WRITE, AEXIT)
  /\ (s_pc (fst (fst rG3)), s_pc (fst (fst rH3)), s_pc (fst (fst rI3))) = (ASTDIO_WRITE, ASTDIO_WRITE, AEXIT)
  /\ (s_pc (fst (fst rF4)), s_pc (fst (fst rG4)), s_pc (fst (fst rH4)), s_pc (fst (fst rI4))) = (ASTDIO_WRITE, AMEMCPY, ASTDIO_WRITE, AEXIT)
  /\ stdio_call 259 srH knH = Some scOF /\ stdio_call 227 srG3 knG3 = Some scG3 /\ stdio_call 259 srH3 knH3 = Some scH3
  /\ stdio_call 195 srF4 knF4 = Some scF4 /\ stdio_call 259 srH4 knH4 = Some scH4.
Proof. repeat apply conj; lazymatch goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.   (* [comment removed for export] *)
