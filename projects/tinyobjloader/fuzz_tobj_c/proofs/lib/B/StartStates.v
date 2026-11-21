(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start state per CONFIG_RSEQ: every state of the start-up chain computed in the build from the start state for r = false and r = true, in place of the recorded literals; the checks and entailments per r). *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "false"; "None"; "pair"; "true"; "bool"; "prod"; "Some"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "cell"; "mkCell"; "sv"; "SAlu"; "sprop"; "SVar"; "SPUle"; "sobj"; "mkObj"; "DUnknown"; "SPAlign"; "DList"; "SExt"; "DImage"; "DZero"; "FcsrFrm0"; "mkSS"; "sstate"; "SPBranch"; "SLBytes"; "SPNot"; "SPEq"; "SPUlt"; "ss_objs"; "ss_pc"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_OR"; "ALU_SRL"; "BC_NE"; "BC_EQ"; "ALU_AND"; "instr"; "Ecall"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vnode"; "mkVN"; "add_facts"; "check_cfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartStates"; "E_ecall"; "C_env"; "C_pn"; "C_pn0"; "E_env0"; "E_env1"; "E_pn_other"; "E_pn_slash"; "FUEL_START"; "S_aux"; "var_pnx"; "C_env0"; "GSTART"; "S0_A_lit"; "S_tid"; "cutpcs_start"; "var_envx"; "F_env"; "F_pn"; "F_tid"; "PC_CTOR"; "S_ctor"; "cuts_start"; "e_auxp"; "e_auxp_leaf"; "exits_start"; "s_env0"; "s_pn_other"; "s_pn_slash"; "var_env"; "var_pn"; "vcuts_start"; "vexits_start"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsCut"; "instr_at"; "mkLeaf"; "sym_run"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue"; "check_ecfgI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CfgGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Init.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* LPS 727298f3: the start state depends on the run's CONFIG_RSEQ ([S0_A r], Lib/InitState.v), so
   every state of the start-up chain below is made per value of [r], IN THE BUILD, from [S0_A r] and
   the symbolic engine; none is a recorded literal.  The cut states are the engine's first arrival at a
   loop head, generalized as the earlier recorded ones were: the loop counter and the registers that
   change round the loop become fresh variables ([gen_env], [gen_pn]). *)
Definition cutpcs_start : list Z := [0xd07e4; 0xd08a8].
Definition GSTART : positive := 20%positive.
Definition FUEL_START : nat := (30 * 1000)%nat.
Definition PC_AUX : Z := 0xd07fc.
Definition PC_ECALL : Z := 0xd0e00.
Definition PC_CTOR : Z := 0x8c9c8.

Definition leaf_at (pc : Z) (r : option (list leaf)) (d : sstate) : sstate :=
  match r with
  | Some ls => match List.find (fun l => Z.eqb (ss_pc (lf_state l)) pc) ls with
               | Some l => lf_state l
               | None => d
               end
  | None => d
  end.

Definition leaf_by (p : sstate -> bool) (r : option (list leaf)) (d : sstate) : sstate :=
  match r with
  | Some ls => match List.find (fun l => p (lf_state l)) ls with
               | Some l => lf_state l
               | None => d
               end
  | None => d
  end.

Definition run_start (S : sstate) : option (list leaf) :=
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.sym_run_fast segsA FUEL_START cutpcs_start S true.

(* The env loop's head: the scanned offset into envp is [SVar 20], the loaded word [SVar 21]. *)
Definition gen_env (S : sstate) : sstate :=
  mkSS (ss_pc S)
    (list_set (list_set (ss_regs S) 9
       (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SVar 1) (SAlu ALU_SLL (SVar 2) (SLit 3))) (SLit 16)) (SVar 20)))
       10 (SVar 21))
    (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S) (ss_facts S) 22%positive (ss_lenient S).

(* The program-name loop's head: the index into argv[0] is [SVar 21], [__progname] [SVar 22], the
   last loaded byte [SVar 23]. *)
Definition gen_pn (S : sstate) : sstate :=
  mkSS (ss_pc S)
    (list_set (list_set (ss_regs S) 11 (SAlu ALU_ADD (SAlu ALU_ADD (SVar 4) (SLit 1)) (SVar 21))) 13 (SVar 23))
    (ss_fregs S) (ss_fcsr S) (ss_resv S)
    (map (fun o => mkObj (ob_base o) (ob_lo o) (ob_hi o)
                     (map (fun c => if sv_eqb (ob_base o) (SLit 0) && sv_eqb (c_off c) (SLit 6558968)
                                    then mkCell (c_off c) (c_width c) (SVar 22) else c) (ob_cells o))
                     (ob_dflt o)) (ss_objs S))
    (ss_facts S) 24%positive (ss_lenient S).

Definition e_auxp_leaf : sv := ltac2:(tb__ "0|0|
SfS25SfS25SfS25SfS25S11P1A1SfS26S11P2A1SbZ3A1A3A3SbZ10A1A3S11P14A1A3SbZ8A1A3").
Definition e_auxp : sv := ltac2:(tb__ "0|1|
SfS25SfS25SfS25S11P1A1SfS26S11P2A1SbZ3A1M0A3A3SfS26S11P3A1G0A3A3SbZ18A1A3").

(* After the env loop the auxv pointer [envp + 8 * i + 8] is the address [aux_base] names. *)
Definition rep_aux (e : sv) : sv := if sv_eqb e e_auxp_leaf then e_auxp else e.
Definition mk_S_aux (E : sstate) (F : list sprop) : sstate :=
  mkSS (ss_pc E) (map rep_aux (ss_regs E)) (ss_fregs E) (ss_fcsr E) (ss_resv E)
    (map (fun o => mkObj (ob_base o) (ob_lo o) (ob_hi o)
                     (map (fun c => mkCell (c_off c) (c_width c) (rep_aux (c_val c))) (ob_cells o))
                     (ob_dflt o)) (ss_objs E))
    F (ss_next E) (ss_lenient E).

Definition pn_slash (S : sstate) : bool :=
  match ss_facts S with SPBranch BC_EQ _ _ :: _ => true | _ => false end.
Definition pn_other (S : sstate) : bool :=
  match ss_facts S with SPBranch BC_NE _ _ :: _ => true | _ => false end.

Definition F_env : list sprop := ltac2:(tb__ "0|1|
S0S10S12S11P14A1M0SfS26S11P3A1SbZ3A1A3A2S0S10S12G0SbZ800A1A2S0S10S21SfS2bG0SbZ7A1A3SbZ0A1A2S1S10A1A3A3A3").
Definition F_pn : list sprop := ltac2:(tb__ "0|1|
S0S10S12S11P15A1M0S11P5A1A2S0S10S12G0SbZ1ffffA1A2S1S10A1A3A3").
Definition F_tid : list sprop := ltac2:(tb__ "0|1|
S0S10S12SbZ1A1S11P18A1M0A2S0S10S22G0SbZ400000A1A2S1S10A1A3A3").

Definition S0_A_lit_0 : sstate := Eval vm_compute in S0_A false.
Definition S0_A_lit_1 : sstate := Eval vm_compute in S0_A true.
Definition S0_A_lit (r : bool) : sstate := if r then S0_A_lit_1 else S0_A_lit_0.
Lemma S0_A_lit_eq : forall r, S0_A r = S0_A_lit r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
(* The start state's facts do not depend on [r] (InitState's F0). *)
Lemma S0_facts_r : forall r, ss_facts (S0_A_lit r) = ss_facts S0_A_lit_0.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Definition L_start_0 : sstate := Eval vm_compute in leaf_at 0xd07e4 (run_start S0_A_lit_0) S0_A_lit_0.
Definition L_start_1 : sstate := Eval vm_compute in leaf_at 0xd07e4 (run_start S0_A_lit_1) S0_A_lit_1.
Definition L_start (r : bool) : sstate := if r then L_start_1 else L_start_0.
Definition C_env0_0 : sstate := Eval vm_compute in gen_env L_start_0.
Definition C_env0_1 : sstate := Eval vm_compute in gen_env L_start_1.
Definition C_env0 (r : bool) : sstate := if r then C_env0_1 else C_env0_0.
Definition C_env_0 : sstate := Eval vm_compute in add_facts F_env C_env0_0.
Definition C_env_1 : sstate := Eval vm_compute in add_facts F_env C_env0_1.
Definition C_env (r : bool) : sstate := if r then C_env_1 else C_env_0.
Definition E_env0_0 : sstate := Eval vm_compute in leaf_at 0xd07e4 (run_start C_env_0) C_env_0.
Definition E_env0_1 : sstate := Eval vm_compute in leaf_at 0xd07e4 (run_start C_env_1) C_env_1.
Definition E_env0 (r : bool) : sstate := if r then E_env0_1 else E_env0_0.
Definition E_env1_0 : sstate := Eval vm_compute in leaf_at PC_AUX (run_start C_env_0) C_env_0.
Definition E_env1_1 : sstate := Eval vm_compute in leaf_at PC_AUX (run_start C_env_1) C_env_1.
Definition E_env1 (r : bool) : sstate := if r then E_env1_1 else E_env1_0.
Definition S_aux_0 : sstate := Eval vm_compute in mk_S_aux E_env1_0 (ss_facts S0_A_lit_0).
Definition S_aux_1 : sstate := Eval vm_compute in mk_S_aux E_env1_1 (ss_facts S0_A_lit_1).
Definition S_aux (r : bool) : sstate := if r then S_aux_1 else S_aux_0.
Definition L_pn_0 : sstate := Eval vm_compute in leaf_at 0xd08a8 (run_start S_aux_0) S_aux_0.
Definition L_pn_1 : sstate := Eval vm_compute in leaf_at 0xd08a8 (run_start S_aux_1) S_aux_1.
Definition L_pn (r : bool) : sstate := if r then L_pn_1 else L_pn_0.
Definition C_pn0_0 : sstate := Eval vm_compute in gen_pn L_pn_0.
Definition C_pn0_1 : sstate := Eval vm_compute in gen_pn L_pn_1.
Definition C_pn0 (r : bool) : sstate := if r then C_pn0_1 else C_pn0_0.
Definition C_pn_0 : sstate := Eval vm_compute in add_facts F_pn C_pn0_0.
Definition C_pn_1 : sstate := Eval vm_compute in add_facts F_pn C_pn0_1.
Definition C_pn (r : bool) : sstate := if r then C_pn_1 else C_pn_0.
Definition E_pn_slash_0 : sstate := Eval vm_compute in leaf_by pn_slash (run_start C_pn_0) C_pn_0.
Definition E_pn_slash_1 : sstate := Eval vm_compute in leaf_by pn_slash (run_start C_pn_1) C_pn_1.
Definition E_pn_slash (r : bool) : sstate := if r then E_pn_slash_1 else E_pn_slash_0.
Definition E_pn_other_0 : sstate := Eval vm_compute in leaf_by pn_other (run_start C_pn_0) C_pn_0.
Definition E_pn_other_1 : sstate := Eval vm_compute in leaf_by pn_other (run_start C_pn_1) C_pn_1.
Definition E_pn_other (r : bool) : sstate := if r then E_pn_other_1 else E_pn_other_0.
Definition E_ecall_0 : sstate := Eval vm_compute in leaf_at PC_ECALL (run_start C_pn_0) C_pn_0.
Definition E_ecall_1 : sstate := Eval vm_compute in leaf_at PC_ECALL (run_start C_pn_1) C_pn_1.
Definition E_ecall (r : bool) : sstate := if r then E_ecall_1 else E_ecall_0.
Definition S_tid_0 : sstate := Eval vm_compute in SymCFG.add_facts F_tid (SymCall.S_after E_ecall_0 (SVar 24%positive) (ss_objs E_ecall_0) 25%positive).
Definition S_tid_1 : sstate := Eval vm_compute in SymCFG.add_facts F_tid (SymCall.S_after E_ecall_1 (SVar 24%positive) (ss_objs E_ecall_1) 25%positive).
Definition S_tid (r : bool) : sstate := if r then S_tid_1 else S_tid_0.
Definition S_ctor_0 : sstate := Eval vm_compute in leaf_at PC_CTOR (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.sym_run_fast segsA FUEL_START [PC_CTOR] S_tid_0 true) S_tid_0.
Definition S_ctor_1 : sstate := Eval vm_compute in leaf_at PC_CTOR (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.sym_run_fast segsA FUEL_START [PC_CTOR] S_tid_1 true) S_tid_1.
Definition S_ctor (r : bool) : sstate := if r then S_ctor_1 else S_ctor_0.

Lemma C_env_eq : forall r, C_env r = add_facts F_env (C_env0 r).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma C_pn_eq : forall r, C_pn r = add_facts F_pn (C_pn0 r).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma S_tid_eq : forall r, S_tid r = add_facts F_tid (S_after (E_ecall r) (SVar 24%positive) (ss_objs (E_ecall r)) 25%positive).
Proof. intros [|]; vm_compute; reflexivity. Qed.

Definition cuts_start (r : bool) : list sstate := [S0_A_lit r; C_env r; S_aux r; C_pn r].
Definition exits_start (r : bool) : list sstate := [E_env0 r; E_env1 r; E_pn_slash r; E_pn_other r; E_ecall r].

Lemma check_start_A : forall r, check_cfg segsA FUEL_START cutpcs_start GSTART (cuts_start r) (exits_start r) = true.
Proof.
  intros [|]; apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok; vm_cast_no_check (@eq_refl bool true).
Qed.

Definition var_env : sv := SVar 20%positive.
Definition var_envx : sv := SAlu ALU_ADD (SVar 20%positive) (SLit 8).
Definition var_pn : sv := SAlu ALU_ADD (SVar 21%positive) (SLit 8192).
Definition var_pnx : sv := SAlu ALU_ADD (SVar 21%positive) (SLit 8193).
(* The ranks and measures of the recorded plan, unchanged. *)
Definition vcuts_start (r : bool) : list vnode :=
  [mkVN (S0_A_lit r) 200 (SLit 0); mkVN (C_env r) 100 var_env; mkVN (S_aux r) 90 (SLit 4096); mkVN (C_pn r) 80 var_pn].
Definition vexits_start (r : bool) : list vnode :=
  [mkVN (E_env0 r) 150 var_envx; mkVN (E_env1 r) 150 var_envx; mkVN (E_pn_slash r) 150 var_pnx;
   mkVN (E_pn_other r) 150 var_pnx; mkVN (E_ecall r) 150 var_pnx].

Lemma echeck_start_A : forall r, check_ecfgI segsA FUEL_START cutpcs_start GSTART (vcuts_start r) (vexits_start r) = true.
Proof.
  intros [|]; apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.check_ecfgI_fast_ok; vm_cast_no_check (@eq_refl bool true).
Qed.

Definition s_env0 : wsub := ltac2:(tb__ "0|4|
S0S7S2fSeA2M0S4S2fSeP14M1SfS25S11G1A1M2SbZ8M3A1A3A4S0G0S4S2fSeP15S1fP1G2G3A3A4S1G0A1A3A3").
Lemma ent_env0 : forall r, entails (E_env0 r) (C_env0 r) s_env0 = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Definition s_pn_slash : wsub := ltac2:(tb__ "0|5|
S0S7S2fSeA2M0S4S2fSeP17S18S2Q8S1fP2S11P15M1A1M2Z1M3A3A3A4S0G0S4S2fSeP16SfS25SfS25S11P4A1SbG3A1M4A3G2A3A4S0G0S4S2fSeG1SfS25G2G4A3A4S1G0A1A3A3A3").
Lemma ent_pn_slash : forall r, entails (E_pn_slash r) (C_pn0 r) s_pn_slash = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Definition s_pn_other : wsub := ltac2:(tb__ "0|5|
S0S7S2fSeA2M0S4S2fSeP17S18S2Q8S1fP2S11P15M1A1M2Z1M3A3A3A4S0G0S4S2fSeP16M4S11G4A1A4S0G0S4S2fSeG1SfS25G2SbG3A1A3A4S1G0A1A3A3A3").
Lemma ent_pn_other : forall r, entails (E_pn_other r) (C_pn0 r) s_pn_other = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Lemma diff_env1 : forall r, state_diff (E_env1 r) (S_aux r) = Some ([(e_auxp_leaf, e_auxp); (e_auxp_leaf, e_auxp)], []).
Proof. intros [|]; vm_compute; reflexivity. Qed.

Lemma ecall_at_A : forall r, instr_at segsA (ss_pc (E_ecall r)) = Some Ecall.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Lemma run_tid_A : forall r, sym_run segsA FUEL_START [PC_CTOR] (S_tid r) true = Some [mkLeaf (S_ctor r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast. Qed.
