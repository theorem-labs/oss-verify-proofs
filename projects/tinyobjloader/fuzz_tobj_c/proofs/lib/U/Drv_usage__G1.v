(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the usage path per CONFIG_RSEQ: every state computed in the build from the start-up's main entry for r = false and r = true; its loop-head cut states, recorded before, remade from the new run's first arrival at each loop head by a fixed rule (the loop's registers and iovec stack words as fresh variables, the leaf's facts below them kept), and its two entry states over argv[0]'s length by joining the run's arrivals at the two largest lengths of the range; the strings fact of the main entry over the new layout, argv[0] plus 10 bytes; the first writev's checks over every leaf of the run, argv[0] being no longer aligned; sub_ok_n, written as plain text, also keeping variable 13, AT_EXECFN's address, which Jinit now fixes). *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "pair"; "false"; "true"; "option"; "list"; "None"; "bool"; "Some"; "prod"; "andb"; "nat"; "negb"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "cell"; "mkCell"; "sv"; "SAlu"; "sprop"; "SVar"; "SPUle"; "sobj"; "mkObj"; "SExt"; "SPBranch"; "SPNot"; "DUnknown"; "SPAlign"; "DList"; "SLBytes"; "sstate"; "mkSS"; "DImage"; "FcsrFrm0"; "SPUlt"; "SPEq"; "reg_sv"; "ss_facts"; "ss_next"; "sv_eqb"; "ss_objs"; "dflt_writable"; "is_arr"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "sprop_below"; "sprop_eqb"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "DZero"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_SUB"; "BC_EQ"; "ALU_OR"; "ALU_SRL"; "BC_NE"; "BC_LTU"; "ALU_XOR"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "sym_run"; "RsEcall"; "RsCut"; "RsFuel"; "lf_state"; "list_set"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "BLit"; "BSrc"; "bexp_eqb"; "cells_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_states"; "FUEL"; "T_sn"; "E_snX"; "E_sn"; "s_sn"; "T_imp"; "R_sn"; "CB1"; "obj_main"; "CB2"; "CB3"; "D1"; "T_sn1"; "lf0"; "xs_post"; "D2"; "E_A1"; "E_A2"; "E_exit"; "S_use"; "F_use"; "L_PA1a"; "L_PA1b_0"; "L_PA1b_1"; "L_PA2_0"; "L_PA2_1"; "L_PB1_0"; "L_PB1_1"; "L_PB2a"; "L_PB2b_0"; "L_PB2b_1"; "L_PB3_0"; "L_PB3_1"; "PA1"; "PB2"; "S_main_rc"; "s_PA1a_CB2"; "s_PA1b_CB1"; "s_PA2_CB3"; "s_PB1_CB1"; "s_PB2a_CB2"; "s_PB2b_CB1"; "s_PB3_CB3"; "xs_pre"; "PA1a"; "PA1b"; "PA2"; "PB1"; "PB2a"; "PB2b"; "PB3"; "T_sn74"; "X_ovf"; "s_PA1b_D1"; "s_PA2_D2"; "s_PB1_D1"; "s_PB2b_D1"; "s_PB3_D2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "entails_fr"; "dummy_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "subst_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "XSplit"; "XMerge"; "XRebase"; "XSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_states.UAddr"; "sw_done"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "S_after_write"; "list_eqb"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates"; "S_main"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_mid_states"; "Dm"; "E_Zm"; "CB1m"; "CB2m"; "E_Mg"; "PZm"; "E_exitm"; "L_PAma_0"; "L_PAmb_0"; "L_PAmb_1"; "L_PB1m_0"; "L_PB1m_1"; "L_PB2ma_0"; "L_PB2mb_0"; "L_PB2mb_1"; "PAm"; "PB2m"; "s_PAma_CB2m"; "s_PAmb_CB1m"; "s_PB1m_CB1m"; "s_PB2ma_CB2m"; "s_PB2mb_CB1m"; "BLm"; "GLm"; "MEMO_1"; "MEMO_2"; "PAma"; "PAmb"; "PB1m"; "PB2ma"; "PB2mb"; "check_core_m"; "s_PAmb_Dm"; "s_PB1m_Dm"; "s_PB2mb_Dm"; "xs_ibuf2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_small_states"; "Dg"; "CBg"; "E_Wg"; "Tn"; "E_exitg"; "BNZ3"; "FUELn"; "L_PAg_0";
"L_PAg_1"; "L_PBg_0"; "L_PBg_1"; "s_PAg_CBg"; "s_PBg_CBg"; "sub_ok_n"; "BLn"; "GLg"; "MEMO_1"; "PAg"; "PBg"; "check_core"; "s_PAg_Dg"; "s_PBg_Dg"; "xs_ibuf"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "nth_error"; "In"; "@Corelib.Lists.ListDef"; "seq"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_strnlen"; "Pre_strnlen"; "P_strnlen"; "Posts_strnlen"; "@Stdlib.ZArith.BinInt.Z"; "of_nat"; "sub"; "to_nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "import_post"; "call_check"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "state_has_rl"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs"; "O_strs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast"; "apply_xforms_fast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.StrAddr"; "strnlen_entry"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require stdpp.bitvector.bitvector.
Require LinuxProcessSemantics.LinuxProcessSem.BvBase.
Require LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Require LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.State.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require LinuxProcessSemantics.Riscv.Prelude.
Require LinuxProcessSemantics.Riscv.Instr.
Require LinuxProcessSemantics.Riscv.Decode.
Require LinuxProcessSemantics.Riscv.DecodeC.
Require LinuxProcessSemantics.Riscv.Sem.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memchr.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_strnlen.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Drv_usage_states.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memchr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_strnlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates.
Import ListNotations.

Import StrAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module UAddr.
  Definition sw_ecallA : Z := 0x222ac.
  Definition sw_ecallB : Z := 0x22334.
  Definition sw_done   : Z := 0x222b8.
  Definition exit_ecall : Z := 0x20150.
End UAddr.
Import UAddr.

Definition FUEL : nat := (8 * 1000)%nat.
Definition lf0 (S : sstate) (r : option (list leaf)) (i : nat) : sstate := ltac2:(tb__ "0|1|
S5S6S46A1M0A1S20Lr;Vr;G0S4cSe3S46Vi;R1S47VS;S4bA2A4A1Lls;VS;X5x2").

Local Ltac vmrefl := match goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end.
Local Ltac vmtrue := vm_cast_no_check (@eq_refl bool true).
Local Ltac runc := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast.
Local Ltac fastl := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit.

Definition runF (cuts : list Z) (S : sstate) : option (list leaf) :=
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.sym_run_fast segs FUEL cuts S true.
Definition xfF (S : sstate) (xs : list xform) : sstate :=
  match OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast S xs with
  | Some X => X
  | None => S
  end.

(* LPS 727298f3: the main entry depends on the run's CONFIG_RSEQ ([S_main r], U/StartStates.v, whose
   object 3 is the launch's auxv), so every state of the usage path below is made per value of [r], IN
   THE BUILD ([X_0], [X_1] by [Eval vm_compute], [X r := if r then X_1 else X_0]), and every lemma about
   them is [forall r], proved after [destruct r].

   The loop heads (the writev retry loops of the three message lengths) were recorded literals; they are
   now made from the run's first arrival at each loop head (the leaf its entailment lemma reads) by one
   fixed rule, [ug_gen_cut]: the registers [rs] and the stack words [cs] that change round the loop become
   the fresh variables from [gl] on (the stack words at the offsets [drop] are the loop's iovec words),
   the loop's own facts [fl] come first, and the leaf's facts and cells over the variables below [gl]
   are kept, as they hold round the loop; every other register, cell and object is the leaf's own.  The
   generalized parts and the counters [gl], [nx] are the recorded literals' (this rule gives them back
   from the old run's leaves).  The two entry states over argv[0]'s length ([E_Wg], [E_Mg]) are made by
   [ug_join_n] from the run's arrivals at the two largest lengths of their range: the registers, stack
   words and bounds that move with the length are the recorded ones over [SVar 5], the other cells are
   the ones both arrivals hold, and the facts are the session source's facts that do not mention the
   length. *)
Definition ug_set_regs (rs : list (nat * sv)) (regs : list sv) : list sv :=
  fold_left (fun acc p => list_set acc (fst p) (snd p)) rs regs.
Definition ug_cell_at (offs : list Z) (c : cell) : bool :=
  match c_off c with SLit z => existsb (Z.eqb z) offs | _ => false end.
Definition ug_cell_lo (gl : positive) (c : cell) : bool := sv_below gl (c_off c) && sv_below gl (c_val c).
Definition ug_obj_cells (o : sobj) (cells : list cell) : sobj :=
  mkObj (ob_base o) (ob_lo o) (ob_hi o) cells (ob_dflt o).

Definition ug_gen_cut (gl nx : positive) (rs : list (nat * sv)) (drop : list Z) (cs : list cell)
    (fl : list sprop) (L : sstate) : sstate :=
  mkSS (ss_pc L) (ug_set_regs rs (ss_regs L)) (ss_fregs L) (ss_fcsr L) (ss_resv L)
    (match ss_objs L with
     | o :: os =>
         ug_obj_cells o (cs ++ filter (fun c => negb (ug_cell_at drop c) && ug_cell_lo gl c) (ob_cells o))
         :: map (fun o' => ug_obj_cells o' (filter (ug_cell_lo gl) (ob_cells o'))) os
     | [] => []
     end)
    (fl ++ filter (sprop_below gl) (ss_facts L)) nx (ss_lenient L).

Definition ug_sv_no (i : positive) (e : sv) : bool := sv_vars_ok (fun j => negb (Pos.eqb j i)) e.
Fixpoint ug_sprop_no (i : positive) (p : sprop) : bool :=
  match p with
  | SPBranch _ a b | SPUlt a b | SPUle a b | SPEq a b => ug_sv_no i a && ug_sv_no i b
  | SPNot q => ug_sprop_no i q
  | SPTrue => true
  | SPAlign j _ => negb (Pos.eqb j i)
  end.
Definition ug_is_img (o : sobj) : bool := match ob_dflt o with DImage => true | _ => false end.

Definition ug_join_n (gl nx : positive) (rs : list (nat * sv)) (dr0 : list Z) (cs0 : list cell)
    (o1 : sobj) (lo2 : sv) (img : cell) (F : list sprop) (A B : sstate) : sstate :=
  let keep (j : nat) (drop : list Z) (c : cell) : bool :=
    negb (ug_cell_at drop c) && ug_cell_lo gl c
    && existsb (cell_eqb c) (ob_cells (nth j (ss_objs B) dummy_obj)) in
  let img_off : list Z := match c_off img with SLit z => [z] | _ => [] end in
  let fix go (j : nat) (os : list sobj) : list sobj :=
    match os with
    | [] => []
    | o :: os' =>
        (match j with
         | O => ug_obj_cells o (cs0 ++ filter (keep j dr0) (ob_cells o))
         | S O => o1
         | S (S O) => mkObj (ob_base o) lo2 (ob_hi o) (filter (keep j []) (ob_cells o)) (ob_dflt o)
         | _ => if ug_is_img o then ug_obj_cells o (img :: filter (keep j img_off) (ob_cells o))
                else ug_obj_cells o (filter (keep j []) (ob_cells o))
         end) :: go (S j) os'
    end in
  mkSS (ss_pc A) (ug_set_regs rs (ss_regs A)) (ss_fregs A) (ss_fcsr A) (ss_resv A)
    (go O (ss_objs A)) F nx (ss_lenient A).

(* LPS 727298f3: the strings object from argv[0]'s address holds argv[0], its NUL, the other strings,
   AT_EXECFN's name and 9 zero bytes, so at least argv[0]'s length plus 10 bytes (it was 17, when the
   random bytes lay in it); argv[0] ends at most [STR0_END_HI] (Lib/InitState.v), checked below. *)
Definition F_use : list sprop :=
  [SPNot (SPBranch BC_EQ (SVar 2) (SLit 2)); SPUle (SAlu ALU_ADD (SVar 5) (SLit 10)) (SVar 25);
   SPUle (SVar 25) (SLit 4194304); SPUle (SVar 4) (SLit 140737488355318)].
Lemma F_use_hi : STR0_END_HI = 140737488355318.
Proof. vm_compute. reflexivity. Qed.

Definition obj_main (r : bool) (i : nat) : sobj := nth i (ss_objs (S_main r)) dummy_obj.
Definition S_main_rc (r : bool) : sstate :=
  mkSS (ss_pc (S_main r)) (ss_regs (S_main r)) (ss_fregs (S_main r)) (ss_fcsr (S_main r)) (ss_resv (S_main r))
    [obj_main r 0; obj_main r 1; obj_main r 2; obj_main r 3; O_strs 25 3; obj_main r 6]
    (ss_facts (S_main r)) 26 (ss_lenient (S_main r)).
Definition S_use_0 : sstate := Eval vm_compute in add_facts F_use (S_main_rc false).
Definition S_use_1 : sstate := Eval vm_compute in add_facts F_use (S_main_rc true).
Definition S_use (r : bool) : sstate := if r then S_use_1 else S_use_0.
Lemma S_use_eq : forall r, add_facts F_use (S_main_rc r) = S_use r.
Proof. intros [|]; vmrefl. Qed.

Definition E_sn_0 : sstate := Eval vm_compute in lf0 (S_use false) (runF [strnlen_entry] (S_use false)) 0.
Definition E_sn_1 : sstate := Eval vm_compute in lf0 (S_use true) (runF [strnlen_entry] (S_use true)) 0.
Definition E_sn (r : bool) : sstate := if r then E_sn_1 else E_sn_0.
Lemma run_use : forall r, sym_run segs FUEL [strnlen_entry] (S_use r) true = Some [mkLeaf (E_sn r) RsCut].
Proof. intros [|]; runc. Qed.

Definition xs_pre : list xform := ltac2:(tb__ "0|1|
S0S97S99U0M0SfN460A1A2S0S97S99G0SfN480A1A2S1S97A1A3A3").
Definition E_snX_0 : sstate := Eval vm_compute in xfF (E_sn false) xs_pre.
Definition E_snX_1 : sstate := Eval vm_compute in xfF (E_sn true) xs_pre.
Definition E_snX (r : bool) : sstate := if r then E_snX_1 else E_snX_0.
Lemma xs_pre_ok : forall r, apply_xforms (E_sn r) xs_pre = Some (E_snX r).
Proof. intros [|]; fastl. Qed.
Definition s_sn_0 : wsub := Eval vm_compute in
  (16%positive, SVar 5) :: (17%positive, SVar 25) :: infer_sub 10 (E_snX false) Pre_strnlen.
Definition s_sn_1 : wsub := Eval vm_compute in
  (16%positive, SVar 5) :: (17%positive, SVar 25) :: infer_sub 10 (E_snX true) Pre_strnlen.
Definition s_sn (r : bool) : wsub := if r then s_sn_1 else s_sn_0.
Definition R_sn_0 : list sobj := Eval vm_compute in
  match entails_fr (E_snX false) Pre_strnlen (s_sn false) with Some R => R | None => [] end.
Definition R_sn_1 : list sobj := Eval vm_compute in
  match entails_fr (E_snX true) Pre_strnlen (s_sn true) with Some R => R | None => [] end.
Definition R_sn (r : bool) : list sobj := if r then R_sn_1 else R_sn_0.
Lemma efr_sn : forall r, entails_fr (E_snX r) Pre_strnlen (s_sn r) = Some (R_sn r).
Proof. intros [|]; vmrefl. Qed.
Lemma chk_sn : forall r, call_check (E_snX r) Pre_strnlen (s_sn r) (R_sn r) Posts_strnlen = true.
Proof. intros [|]; vmtrue. Qed.
Lemma fb_sn : forall r, forallb (sprop_below (ss_next (E_snX r))) (ss_facts (E_sn r)) = true.
Proof. intros [|]; vmtrue. Qed.
Lemma s_sn_16 : forall r, wsub_get (s_sn r) 16 = SVar 5.
Proof. intros [|]; reflexivity. Qed.
Definition T_imp_0 : sstate := Eval vm_compute in
  import_post (s_sn false) NF P_strnlen (ss_next (E_snX false)) (R_sn false).
Definition T_imp_1 : sstate := Eval vm_compute in
  import_post (s_sn true) NF P_strnlen (ss_next (E_snX true)) (R_sn true).
Definition T_imp (r : bool) : sstate := if r then T_imp_1 else T_imp_0.
Lemma T_imp_eq : forall r, import_post (s_sn r) NF P_strnlen (ss_next (E_snX r)) (R_sn r) = T_imp r.
Proof. intros [|]; vmrefl. Qed.
Definition xs_post : list xform := ltac2:(tb__ "0|3|
S0S97S9bU1M0A1S0S97S9cS0ScU2S0ScG0S0ScU3S0ScU0M1S0ScU4S0ScU5S0ScU6S0ScU7S1ScA1A3A3A3A3A3A3A3A3A1S0S97S9aG1A1M2S0S97G2S1S97A1A3A3A3A3").
Definition T_sn_0 : sstate := Eval vm_compute in xfF (add_facts (ss_facts (E_sn false)) (T_imp false)) xs_post.
Definition T_sn_1 : sstate := Eval vm_compute in xfF (add_facts (ss_facts (E_sn true)) (T_imp true)) xs_post.
Definition T_sn (r : bool) : sstate := if r then T_sn_1 else T_sn_0.
Lemma xs_post_ok : forall r, apply_xforms (add_facts (ss_facts (E_sn r)) (T_imp r)) xs_post = Some (T_sn r).
Proof. intros [|]; fastl. Qed.
Lemma fb_sn2 : forall r, forallb (sprop_below (ss_next (T_imp r))) (ss_facts (E_sn r)) = true.
Proof. intros [|]; vmtrue. Qed.

Definition T_sn1 (r : bool) : sstate :=
  mkSS (ss_pc (T_sn r)) (list_set (ss_regs (T_sn r)) 10 (SVar 5)) (ss_fregs (T_sn r)) (ss_fcsr (T_sn r))
    (ss_resv (T_sn r)) (ss_objs (T_sn r)) (ss_facts (T_sn r)) (ss_next (T_sn r)) (ss_lenient (T_sn r)).
Lemma fact_T_sn : forall r, In (SPEq (SVar 66) (SVar 5)) (ss_facts (T_sn r)).
Proof. intros [|]; cbn; tauto. Qed.
Lemma diff_sn : forall r, state_diff (T_sn r) (T_sn1 r) = Some ([(SVar 66, SVar 5)], @nil sprop).
Proof. intros [|]; vmrefl. Qed.
Lemma swf_T_sn1 : forall r, swf (T_sn1 r) = true.
Proof. intros [|]; vmtrue. Qed.

Definition T_sn74 (r : bool) : sstate := add_facts [SPUle (SLit 74) (SVar 5)] (T_sn1 r).

Definition X_ovf_0 : sstate := Eval vm_compute in lf0 (T_sn74 false) (runF [] (T_sn74 false)) 0.
Definition X_ovf_1 : sstate := Eval vm_compute in lf0 (T_sn74 true) (runF [] (T_sn74 true)) 0.
Definition X_ovf (r : bool) : sstate := if r then X_ovf_1 else X_ovf_0.
Definition E_A1_0 : sstate := Eval vm_compute in lf0 (T_sn74 false) (runF [] (T_sn74 false)) 1.
Definition E_A1_1 : sstate := Eval vm_compute in lf0 (T_sn74 true) (runF [] (T_sn74 true)) 1.
Definition E_A1 (r : bool) : sstate := if r then E_A1_1 else E_A1_0.
Lemma run2 : forall r,
  sym_run segs FUEL [] (T_sn74 r) true = Some [mkLeaf (X_ovf r) RsEcall; mkLeaf (E_A1 r) RsEcall].
Proof. intros [|]; runc. Qed.

(* The first message's session: writev of the buffer ("usage: ") and argv[0], retried while short. *)
Definition PA1 (r : bool) : sstate := S_after_write (E_A1 r) (reg_sv (E_A1 r) 22).
Definition PA1a (r : bool) : sstate := add_facts [SPUle (SVar 67) (SLit 7)] (PA1 r).
Definition PA1b (r : bool) : sstate := add_facts [SPUle (SLit 8) (SVar 67)] (PA1 r).
Definition L_PA1a_0 : sstate := Eval vm_compute in lf0 (PA1a false) (runF [sw_done] (PA1a false)) 0.
Definition L_PA1a_1 : sstate := Eval vm_compute in lf0 (PA1a true) (runF [sw_done] (PA1a true)) 0.
Definition L_PA1a (r : bool) : sstate := if r then L_PA1a_1 else L_PA1a_0.
Definition L_PA1b_0_0 : sstate := Eval vm_compute in lf0 (PA1b false) (runF [sw_done] (PA1b false)) 0.
Definition L_PA1b_0_1 : sstate := Eval vm_compute in lf0 (PA1b true) (runF [sw_done] (PA1b true)) 0.
Definition L_PA1b_0 (r : bool) : sstate := if r then L_PA1b_0_1 else L_PA1b_0_0.
Definition L_PA1b_1_0 : sstate := Eval vm_compute in lf0 (PA1b false) (runF [sw_done] (PA1b false)) 1.
Definition L_PA1b_1_1 : sstate := Eval vm_compute in lf0 (PA1b true) (runF [sw_done] (PA1b true)) 1.
Definition L_PA1b_1 (r : bool) : sstate := if r then L_PA1b_1_1 else L_PA1b_1_0.
Lemma run_PA1a : forall r, sym_run segs FUEL [sw_done] (PA1a r) true = Some [mkLeaf (L_PA1a r) RsEcall].
Proof. intros [|]; runc. Qed.
Lemma run_PA1b : forall r,
  sym_run segs FUEL [sw_done] (PA1b r) true = Some [mkLeaf (L_PA1b_0 r) RsEcall; mkLeaf (L_PA1b_1 r) RsCut].
Proof. intros [|]; runc. Qed.

(* The loop heads of the first session, by [ug_gen_cut] from their first arrivals: [CB2] (both iovecs
   left, from [L_PA1a]), [CB1] (the second iovec left, from [L_PA1b_0]) and the session's end [D1]
   (from [L_PA1b_1]); the iovec words are at sp-1224 .. sp-1200. *)
Definition iovA : list Z := [-1224; -1216; -1208; -1200].
Definition CB2_rs : list (nat * sv) :=
  [(1%nat, SVar 68); (13%nat, SVar 70); (15%nat, SVar 67); (22%nat, SAlu ALU_ADD (SVar 5) (SVar 67))].
Definition CB2_cs : list cell :=
  [mkCell (SLit (-1216)) 8 (SVar 67);
   mkCell (SLit (-1224)) 8 (SAlu ALU_SUB (SAlu ALU_ADD (SVar 1) (SLit (-553))) (SVar 67))].
Definition CB2_fl : list sprop := [SPUle (SVar 67) (SLit 6)].
Definition CB2_0 : sstate := Eval vm_compute in ug_gen_cut 67 71 CB2_rs [-1224; -1216] CB2_cs CB2_fl (L_PA1a false).
Definition CB2_1 : sstate := Eval vm_compute in ug_gen_cut 67 71 CB2_rs [-1224; -1216] CB2_cs CB2_fl (L_PA1a true).
Definition CB2 (r : bool) : sstate := if r then CB2_1 else CB2_0.
Definition CB1_rs : list (nat * sv) :=
  [(1%nat, SVar 67); (13%nat, SVar 70); (15%nat, SVar 68); (19%nat, SVar 71); (22%nat, SVar 68)].
Definition CB1_cs : list cell :=
  [mkCell (SLit (-1200)) 8 (SVar 68);
   mkCell (SLit (-1208)) 8 (SAlu ALU_SUB (SAlu ALU_ADD (SVar 4) (SVar 5)) (SVar 68))].
Definition CB1_fl : list sprop := [SPUle (SLit 1) (SVar 68); SPBranch BC_LTU (SVar 68) (SVar 5)].
Definition CB1_0 : sstate := Eval vm_compute in ug_gen_cut 67 72 CB1_rs iovA CB1_cs CB1_fl (L_PA1b_0 false).
Definition CB1_1 : sstate := Eval vm_compute in ug_gen_cut 67 72 CB1_rs iovA CB1_cs CB1_fl (L_PA1b_0 true).
Definition CB1 (r : bool) : sstate := if r then CB1_1 else CB1_0.
Definition D1_rs : list (nat * sv) :=
  [(1%nat, SVar 83); (10%nat, SVar 70); (12%nat, SVar 71); (13%nat, SVar 72); (14%nat, SVar 82);
   (15%nat, SVar 73); (18%nat, SVar 74); (19%nat, SVar 75); (20%nat, SVar 76); (22%nat, SVar 77)].
Definition D1_0 : sstate := Eval vm_compute in ug_gen_cut 67 90 D1_rs iovA [] [] (L_PA1b_1 false).
Definition D1_1 : sstate := Eval vm_compute in ug_gen_cut 67 90 D1_rs iovA [] [] (L_PA1b_1 true).
Definition D1 (r : bool) : sstate := if r then D1_1 else D1_0.

Definition PB2 (r : bool) : sstate :=
  add_facts [SPUle (SVar 71) (SLit 131078)] (S_after_write (CB2 r) (reg_sv (CB2 r) 22)).
Definition PB2a (r : bool) : sstate := add_facts [SPUle (SVar 71) (SVar 67)] (PB2 r).
Definition PB2b (r : bool) : sstate := add_facts [SPUle (SAlu ALU_ADD (SVar 67) (SLit 1)) (SVar 71)] (PB2 r).
Definition PB1 (r : bool) : sstate :=
  add_facts [SPUle (SVar 72) (SLit 131071)] (S_after_write (CB1 r) (reg_sv (CB1 r) 22)).
Definition L_PB2a_0 : sstate := Eval vm_compute in lf0 (PB2a false) (runF [sw_done] (PB2a false)) 0.
Definition L_PB2a_1 : sstate := Eval vm_compute in lf0 (PB2a true) (runF [sw_done] (PB2a true)) 0.
Definition L_PB2a (r : bool) : sstate := if r then L_PB2a_1 else L_PB2a_0.
Definition L_PB2b_0_0 : sstate := Eval vm_compute in lf0 (PB2b false) (runF [sw_done] (PB2b false)) 0.
Definition L_PB2b_0_1 : sstate := Eval vm_compute in lf0 (PB2b true) (runF [sw_done] (PB2b true)) 0.
Definition L_PB2b_0 (r : bool) : sstate := if r then L_PB2b_0_1 else L_PB2b_0_0.
Definition L_PB2b_1_0 : sstate := Eval vm_compute in lf0 (PB2b false) (runF [sw_done] (PB2b false)) 1.
Definition L_PB2b_1_1 : sstate := Eval vm_compute in lf0 (PB2b true) (runF [sw_done] (PB2b true)) 1.
Definition L_PB2b_1 (r : bool) : sstate := if r then L_PB2b_1_1 else L_PB2b_1_0.
Definition L_PB1_0_0 : sstate := Eval vm_compute in lf0 (PB1 false) (runF [sw_done] (PB1 false)) 0.
Definition L_PB1_0_1 : sstate := Eval vm_compute in lf0 (PB1 true) (runF [sw_done] (PB1 true)) 0.
Definition L_PB1_0 (r : bool) : sstate := if r then L_PB1_0_1 else L_PB1_0_0.
Definition L_PB1_1_0 : sstate := Eval vm_compute in lf0 (PB1 false) (runF [sw_done] (PB1 false)) 1.
Definition L_PB1_1_1 : sstate := Eval vm_compute in lf0 (PB1 true) (runF [sw_done] (PB1 true)) 1.
Definition L_PB1_1 (r : bool) : sstate := if r then L_PB1_1_1 else L_PB1_1_0.
Lemma run_PB2a : forall r, sym_run segs FUEL [sw_done] (PB2a r) true = Some [mkLeaf (L_PB2a r) RsEcall].
Proof. intros [|]; runc. Qed.
Lemma run_PB2b : forall r,
  sym_run segs FUEL [sw_done] (PB2b r) true = Some [mkLeaf (L_PB2b_0 r) RsCut; mkLeaf (L_PB2b_1 r) RsEcall].
Proof. intros [|]; runc. Qed.
Lemma run_PB1 : forall r,
  sym_run segs FUEL [sw_done] (PB1 r) true = Some [mkLeaf (L_PB1_0 r) RsCut; mkLeaf (L_PB1_1 r) RsEcall].
Proof. intros [|]; runc. Qed.

Definition GL : positive := 67.
Definition s_PA1a_CB2 : wsub := ltac2:(tb__ "0|3|
S0SaS44S12A2M0S2S44S12P43M1S13S3dSfZ7A1S15G1A1M2A3A4S0G0S2S44S12P46G2A4S0G0S2S44S12P44SfZ222b4A1A4S1G0A1A3A3A3").
Definition s_PA1b_CB1 : wsub := ltac2:(tb__ "0|3|
S0SaS44S12A2M0S2S44S12P47S13S3bS15P1A1SfN4c8A1A3A4S0G0S2S44S12P44S13S3dS15P5A1S13S3bS15P43M1A1SfN7A1A3M2A3A4S0G0S2S44S12P46G2A4S0G0S2S44S12G1SfZ222b4A1A4S1G0A1A3A3A3A3").
Definition s_PA1b_D1_0 : wsub := Eval vm_compute in infer_sub GL (L_PA1b_1 false) (D1 false).
Definition s_PA1b_D1_1 : wsub := Eval vm_compute in infer_sub GL (L_PA1b_1 true) (D1 true).
Definition s_PA1b_D1 (r : bool) : wsub := if r then s_PA1b_D1_1 else s_PA1b_D1_0.
Definition s_PB2a_CB2 : wsub := ltac2:(tb__ "0|3|
S0SaS44S12A2M0S2S44S12P43M1S13S3dS15G1A1S15P47A1M2A3A4S0G0S2S44S12P46G2A4S0G0S2S44S12P44SfZ2233cA1A4S1G0A1A3A3A3").
Definition s_PB2b_D1_0 : wsub := Eval vm_compute in infer_sub GL (L_PB2b_0 false) (D1 false).
Definition s_PB2b_D1_1 : wsub := Eval vm_compute in infer_sub GL (L_PB2b_0 true) (D1 true).
Definition s_PB2b_D1 (r : bool) : wsub := if r then s_PB2b_D1_1 else s_PB2b_D1_0.
Definition s_PB2b_CB1 : wsub := ltac2:(tb__ "0|4|
S0SaS44S12A2M0S2S44S12P47M1S13S3bS15P1A1SfN4c8A1A3A4S0G0S2S44S12P44S13S3dS15P5A1S13S3dS15G1A1S15P43M2A1A3M3A3A4S0G0S2S44S12P46G3A4S0G0S2S44S12G2SfZ2233cA1A4S1G0A1A3A3A3A3").
Definition s_PB1_D1_0 : wsub := Eval vm_compute in infer_sub GL (L_PB1_0 false) (D1 false).
Definition s_PB1_D1_1 : wsub := Eval vm_compute in infer_sub GL (L_PB1_0 true) (D1 true).
Definition s_PB1_D1 (r : bool) : wsub := if r then s_PB1_D1_1 else s_PB1_D1_0.
Definition s_PB1_CB1  : wsub := ltac2:(tb__ "0|3|
S0SaS44S12A2M0S2S44S12P47S13S3bS15P1A1SfN4b8A1A3A4S0G0S2S44S12P44M1S13S3dS15G1A1S15P48A1M2A3A4S0G0S2S44S12P46G2A4S0G0S2S44S12P43SfZ2233cA1A4S1G0A1A3A3A3A3").
Lemma ent_PA1a_CB2 : forall r, entails (L_PA1a r) (CB2 r) s_PA1a_CB2 = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PA1b_CB1 : forall r, entails (L_PA1b_0 r) (CB1 r) s_PA1b_CB1 = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PA1b_D1 : forall r, entails (L_PA1b_1 r) (D1 r) (s_PA1b_D1 r) = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PB2a_CB2 : forall r, entails (L_PB2a r) (CB2 r) s_PB2a_CB2 = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PB2b_D1 : forall r, entails (L_PB2b_0 r) (D1 r) (s_PB2b_D1 r) = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PB2b_CB1 : forall r, entails (L_PB2b_1 r) (CB1 r) s_PB2b_CB1 = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PB1_D1 : forall r, entails (L_PB1_0 r) (D1 r) (s_PB1_D1 r) = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PB1_CB1 : forall r, entails (L_PB1_1 r) (CB1 r) s_PB1_CB1 = true.
Proof. intros [|]; vmtrue. Qed.

Lemma sv_PA1a_67 : ltac2:(tb__ "0|1|
S4eS12S95S7aP43M0A2S13S3dSfZ7A1S15G0A1A3A3"). Proof. reflexivity. Qed.
Lemma sv_PA1b_68 : ltac2:(tb__ "0|0|
S4eS12S95S7bP44A2S13S3dS15P5A1S13S3bS15P43A1SfN7A1A3A3A3"). Proof. reflexivity. Qed.
Lemma sv_PB2a_67 : ltac2:(tb__ "0|1|
S4eS12S95S7eP43M0A2S13S3dS15G0A1S15P47A1A3A3"). Proof. reflexivity. Qed.
Lemma sv_PB2b_68 : ltac2:(tb__ "0|0|
S4eS12S95S7fP44A2S13S3dS15P5A1S13S3dS15P47A1S15P43A1A3A3A3"). Proof. reflexivity. Qed.
Lemma sv_PB1_68 : ltac2:(tb__ "0|1|
S4eS12S95S7dP44M0A2S13S3dS15G0A1S15P48A1A3A3"). Proof. reflexivity. Qed.

Definition E_A2_0 : sstate := Eval vm_compute in lf0 (D1 false) (runF [] (D1 false)) 0.
Definition E_A2_1 : sstate := Eval vm_compute in lf0 (D1 true) (runF [] (D1 true)) 0.
Definition E_A2 (r : bool) : sstate := if r then E_A2_1 else E_A2_0.
Lemma run_D1 : forall r, sym_run segs FUEL [] (D1 r) true = Some [mkLeaf (E_A2 r) RsEcall].
Proof. intros [|]; runc. Qed.

(* The second message's session: writev of " INPUT\n" from the buffer, retried while short. *)
Definition PA2 (r : bool) : sstate := S_after_write (E_A2 r) (reg_sv (E_A2 r) 22).
Definition L_PA2_0_0 : sstate := Eval vm_compute in lf0 (PA2 false) (runF [sw_done] (PA2 false)) 0.
Definition L_PA2_0_1 : sstate := Eval vm_compute in lf0 (PA2 true) (runF [sw_done] (PA2 true)) 0.
Definition L_PA2_0 (r : bool) : sstate := if r then L_PA2_0_1 else L_PA2_0_0.
Definition L_PA2_1_0 : sstate := Eval vm_compute in lf0 (PA2 false) (runF [sw_done] (PA2 false)) 1.
Definition L_PA2_1_1 : sstate := Eval vm_compute in lf0 (PA2 true) (runF [sw_done] (PA2 true)) 1.
Definition L_PA2_1 (r : bool) : sstate := if r then L_PA2_1_1 else L_PA2_1_0.
Lemma run_PA2 : forall r,
  sym_run segs FUEL [sw_done] (PA2 r) true = Some [mkLeaf (L_PA2_0 r) RsEcall; mkLeaf (L_PA2_1 r) RsCut].
Proof. intros [|]; runc. Qed.

(* Its loop head [CB3] (from [L_PA2_0]) and end [D2] (from [L_PA2_1]) by [ug_gen_cut]; the iovec
   words are at sp-680 and sp-672. *)
Definition CB3_rs : list (nat * sv) := [(1%nat, SVar 91); (13%nat, SVar 92); (15%nat, SVar 90); (22%nat, SVar 90)].
Definition CB3_cs : list cell :=
  [mkCell (SLit (-672)) 8 (SVar 90);
   mkCell (SLit (-680)) 8 (SAlu ALU_SUB (SAlu ALU_ADD (SVar 1) (SLit (-553))) (SVar 90))].
Definition CB3_fl : list sprop := [SPUle (SLit 1) (SVar 90); SPUle (SVar 90) (SLit 6)].
Definition CB3_0 : sstate := Eval vm_compute in ug_gen_cut 90 93 CB3_rs [-680; -672] CB3_cs CB3_fl (L_PA2_0 false).
Definition CB3_1 : sstate := Eval vm_compute in ug_gen_cut 90 93 CB3_rs [-680; -672] CB3_cs CB3_fl (L_PA2_0 true).
Definition CB3 (r : bool) : sstate := if r then CB3_1 else CB3_0.
Definition D2_rs : list (nat * sv) :=
  [(1%nat, SVar 100); (10%nat, SVar 101); (12%nat, SVar 102); (13%nat, SVar 103); (14%nat, SVar 109);
   (15%nat, SVar 104); (18%nat, SVar 105); (19%nat, SVar 106); (20%nat, SVar 107); (22%nat, SVar 108)].
Definition D2_0 : sstate := Eval vm_compute in ug_gen_cut 90 110 D2_rs [-680; -672] [] [] (L_PA2_1 false).
Definition D2_1 : sstate := Eval vm_compute in ug_gen_cut 90 110 D2_rs [-680; -672] [] [] (L_PA2_1 true).
Definition D2 (r : bool) : sstate := if r then D2_1 else D2_0.

Definition PB3 (r : bool) : sstate := S_after_write (CB3 r) (reg_sv (CB3 r) 22).
Definition L_PB3_0_0 : sstate := Eval vm_compute in lf0 (PB3 false) (runF [sw_done] (PB3 false)) 0.
Definition L_PB3_0_1 : sstate := Eval vm_compute in lf0 (PB3 true) (runF [sw_done] (PB3 true)) 0.
Definition L_PB3_0 (r : bool) : sstate := if r then L_PB3_0_1 else L_PB3_0_0.
Definition L_PB3_1_0 : sstate := Eval vm_compute in lf0 (PB3 false) (runF [sw_done] (PB3 false)) 1.
Definition L_PB3_1_1 : sstate := Eval vm_compute in lf0 (PB3 true) (runF [sw_done] (PB3 true)) 1.
Definition L_PB3_1 (r : bool) : sstate := if r then L_PB3_1_1 else L_PB3_1_0.
Lemma run_PB3 : forall r,
  sym_run segs FUEL [sw_done] (PB3 r) true = Some [mkLeaf (L_PB3_0 r) RsCut; mkLeaf (L_PB3_1 r) RsEcall].
Proof. intros [|]; runc. Qed.
Definition GL2 : positive := 90.
Definition s_PA2_CB3 : wsub := ltac2:(tb__ "0|3|
S0SaS44S12A2M0S2S44S12P5aM1S13S3dSfZ7A1S15G1A1M2A3A4S0G0S2S44S12P5cG2A4S0G0S2S44S12P5bSfZ222b4A1A4S1G0A1A3A3A3").
Definition s_PA2_D2_0 : wsub := Eval vm_compute in infer_sub GL2 (L_PA2_1 false) (D2 false).
Definition s_PA2_D2_1 : wsub := Eval vm_compute in infer_sub GL2 (L_PA2_1 true) (D2 true).
Definition s_PA2_D2 (r : bool) : wsub := if r then s_PA2_D2_1 else s_PA2_D2_0.
Definition s_PB3_CB3 : wsub := ltac2:(tb__ "0|3|
S0SaS44S12A2M0S2S44S12P5aM1S13S3dS15G1A1S15P5dA1M2A3A4S0G0S2S44S12P5cG2A4S0G0S2S44S12P5bSfZ2233cA1A4S1G0A1A3A3A3").
Definition s_PB3_D2_0 : wsub := Eval vm_compute in infer_sub GL2 (L_PB3_0 false) (D2 false).
Definition s_PB3_D2_1 : wsub := Eval vm_compute in infer_sub GL2 (L_PB3_0 true) (D2 true).
Definition s_PB3_D2 (r : bool) : wsub := if r then s_PB3_D2_1 else s_PB3_D2_0.
Lemma ent_PA2_CB3 : forall r, entails (L_PA2_0 r) (CB3 r) s_PA2_CB3 = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PA2_D2 : forall r, entails (L_PA2_1 r) (D2 r) (s_PA2_D2 r) = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PB3_CB3 : forall r, entails (L_PB3_1 r) (CB3 r) s_PB3_CB3 = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PB3_D2 : forall r, entails (L_PB3_0 r) (D2 r) (s_PB3_D2 r) = true.
Proof. intros [|]; vmtrue. Qed.
Lemma sv_PA2_90 : ltac2:(tb__ "0|1|
S4eS12S95S7cP5aM0A2S13S3dSfZ7A1S15G0A1A3A3"). Proof. reflexivity. Qed.
Lemma sv_PB3_90 : ltac2:(tb__ "0|1|
S4eS12S95S80P5aM0A2S13S3dS15G0A1S15P5dA1A3A3"). Proof. reflexivity. Qed.

Definition E_exit_0 : sstate := Eval vm_compute in lf0 (D2 false) (runF [] (D2 false)) 0.
Definition E_exit_1 : sstate := Eval vm_compute in lf0 (D2 true) (runF [] (D2 true)) 0.
Definition E_exit (r : bool) : sstate := if r then E_exit_1 else E_exit_0.
Lemma run_D2 : forall r, sym_run segs FUEL [] (D2 r) true = Some [mkLeaf (E_exit r) RsEcall].
Proof. intros [|]; runc. Qed.
Lemma E_exit_regs : forall r, reg_sv (E_exit r) 17 = SLit 94 /\ reg_sv (E_exit r) 10 = SLit 2.
Proof. intros [|]; split; reflexivity. Qed.
End Drv_usage_states.

Module Drv_usage_small_states.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_states.
Import ListNotations.

Import UAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition FUELn : nat := (20 * 1000)%nat.
Local Ltac vmtrue := vm_cast_no_check (@eq_refl bool true).
Local Ltac runc := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast.

Definition Tn (r : bool) (n : Z) : sstate := subst_state [(5%positive, SLit n)] (T_sn1 r) (ss_next (T_sn1 r)).
Definition xs_ibuf (n : Z) : list xform := ltac2:(tb__ "0|0|
S0S97S99U0SfN230A1A2S0S97S99U1SfSe8Vn;Z222A2A1A2S1S97A1A3A3").

Definition BLn (n : Z) : list bexp := ltac2:(tb__ "0|2|
SeS50S0S50S51Z75A1S0S50S51Z73A1S0S50S51Z61A1S0S50S51Z67A1S0S50S51Z65A1S0S50S51Z3aA1S0S50S51Z20A1M0S1S50A1M1A3A3A3A3A3A3A3SeS50Se2ScS50ScS52P3Se7R1A1A2Lj;Se1U0Se9Vn;A1A2A4S0S50G0S0S50S51Z49A1S0S50S51Z4eA1S0S50S51Z50A1S0S50S51Z55A1S0S50S51Z54A1S0S50S51ZaA1G1A3A3A3A3A3A3A3A3A3").

(* The run's arrival at the first writev for argv[0]'s length [n], its buffer split off by [xs] and read
   as the list variable 4: the state [check_core] reads. *)
Definition wl_of (xs : list xform) (t : sstate) : sstate :=
  let w := lf0 t (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.sym_run_fast segs FUELn [] t true) 1 in
  match OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast w xs with
  | Some wx => obj_to_list wx 1 4
  | None => t
  end.

(* The first writev of a message of at most 80 bytes (argv[0] at most 66 bytes), over the length
   [SVar 5]: [ug_join_n] of the arrivals at lengths 66 and 65 (Drv_usage_states); the buffer is
   [sp-560, sp+v5-546). *)
Definition EW_hi : sv := SAlu ALU_ADD (SVar 5) (SLit 18446744073709551070).
Definition EW_rs : list (nat * sv) :=
  [(5%nat, SVar 100); (6%nat, SVar 101); (7%nat, SVar 102);
   (13%nat, SAlu ALU_XOR (SAlu ALU_ADD (SVar 1) EW_hi) (SAlu ALU_ADD (SVar 1) (SLit (-560))));
   (15%nat, SVar 103); (16%nat, SVar 104); (22%nat, SAlu ALU_ADD (SVar 5) (SLit 14)); (28%nat, SVar 105)].
Definition EW_dr0 : list Z := [-1088; -1104; -1152; -1160; -600; -672].
Definition EW_cs0 : list cell :=
  [mkCell (SLit (-1088)) 8 (SVar 5); mkCell (SLit (-1104)) 8 (SVar 5);
   mkCell (SLit (-1152)) 8 (SAlu ALU_SUB (SLit 2147483640) (SVar 5));
   mkCell (SLit (-1160)) 8 (SAlu ALU_ADD (SVar 5) (SLit 7));
   mkCell (SLit (-600)) 8 (SAlu ALU_ADD (SVar 5) (SLit 14));
   mkCell (SLit (-672)) 8 (SAlu ALU_ADD (SVar 5) (SLit 14))].
Definition EW_o1 : sobj := mkObj (SVar 1) (SLit (-560)) EW_hi [] (DList 4).
Definition EW_img : cell := mkCell (SLit 171448) 8 (SAlu ALU_ADD (SVar 1) EW_hi).
Definition EW_F (r : bool) : list sprop :=
  SPUle (SVar 5) (SLit 66) :: filter (ug_sprop_no 5) (ss_facts (T_sn1 r)).
Definition E_Wg_0 : sstate := Eval vm_compute in
  ug_join_n (ss_next (T_sn1 false)) 106 EW_rs EW_dr0 EW_cs0 EW_o1 EW_hi EW_img (EW_F false)
    (wl_of (xs_ibuf 66) (Tn false 66)) (wl_of (xs_ibuf 65) (Tn false 65)).
Definition E_Wg_1 : sstate := Eval vm_compute in
  ug_join_n (ss_next (T_sn1 true)) 106 EW_rs EW_dr0 EW_cs0 EW_o1 EW_hi EW_img (EW_F true)
    (wl_of (xs_ibuf 66) (Tn true 66)) (wl_of (xs_ibuf 65) (Tn true 65)).
Definition E_Wg (r : bool) : sstate := if r then E_Wg_1 else E_Wg_0.

Definition PAg (r : bool) : sstate := S_after_write (E_Wg r) (reg_sv (E_Wg r) 22).
Definition L_PAg_0_0 : sstate := Eval vm_compute in lf0 (PAg false) (runF [sw_done] (PAg false)) 0.
Definition L_PAg_0_1 : sstate := Eval vm_compute in lf0 (PAg true) (runF [sw_done] (PAg true)) 0.
Definition L_PAg_0 (r : bool) : sstate := if r then L_PAg_0_1 else L_PAg_0_0.
Definition L_PAg_1_0 : sstate := Eval vm_compute in lf0 (PAg false) (runF [sw_done] (PAg false)) 1.
Definition L_PAg_1_1 : sstate := Eval vm_compute in lf0 (PAg true) (runF [sw_done] (PAg true)) 1.
Definition L_PAg_1 (r : bool) : sstate := if r then L_PAg_1_1 else L_PAg_1_0.
Lemma run_PAg : forall r,
  sym_run segs FUEL [sw_done] (PAg r) true = Some [mkLeaf (L_PAg_0 r) RsEcall; mkLeaf (L_PAg_1 r) RsCut].
Proof. intros [|]; runc. Qed.

(* Its loop head [CBg] (from [L_PAg_0]) and end [Dg] (from [L_PAg_1]) by [ug_gen_cut]; the iovec words
   are at sp-680 and sp-672. *)
Definition iovG : list Z := [-680; -672].
Definition CBg_rs : list (nat * sv) :=
  [(1%nat, SVar 107); (5%nat, SVar 100); (6%nat, SVar 101); (7%nat, SVar 102); (13%nat, SVar 108);
   (15%nat, SVar 106); (16%nat, SVar 104); (22%nat, SVar 106); (28%nat, SVar 105)].
Definition CBg_cs : list cell :=
  [mkCell (SLit (-672)) 8 (SVar 106);
   mkCell (SLit (-680)) 8 (SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_ADD (SVar 1) (SLit (-546))) (SVar 5)) (SVar 106))].
Definition CBg_fl : list sprop := [SPUle (SLit 1) (SVar 106); SPUle (SVar 106) (SAlu ALU_ADD (SVar 5) (SLit 13))].
Definition CBg_0 : sstate := Eval vm_compute in ug_gen_cut 100 109 CBg_rs iovG CBg_cs CBg_fl (L_PAg_0 false).
Definition CBg_1 : sstate := Eval vm_compute in ug_gen_cut 100 109 CBg_rs iovG CBg_cs CBg_fl (L_PAg_0 true).
Definition CBg (r : bool) : sstate := if r then CBg_1 else CBg_0.
Definition Dg_rs : list (nat * sv) :=
  [(1%nat, SVar 120); (5%nat, SVar 100); (6%nat, SVar 101); (7%nat, SVar 102); (10%nat, SVar 121);
   (12%nat, SVar 122); (13%nat, SVar 123); (14%nat, SVar 129); (15%nat, SVar 124); (16%nat, SVar 104);
   (18%nat, SVar 125); (19%nat, SVar 126); (20%nat, SVar 127); (22%nat, SVar 128); (28%nat, SVar 105)].
Definition Dg_0 : sstate := Eval vm_compute in ug_gen_cut 100 130 Dg_rs iovG [] [] (L_PAg_1 false).
Definition Dg_1 : sstate := Eval vm_compute in ug_gen_cut 100 130 Dg_rs iovG [] [] (L_PAg_1 true).
Definition Dg (r : bool) : sstate := if r then Dg_1 else Dg_0.

Definition PBg (r : bool) : sstate := S_after_write (CBg r) (reg_sv (CBg r) 22).
Definition L_PBg_0_0 : sstate := Eval vm_compute in lf0 (PBg false) (runF [sw_done] (PBg false)) 0.
Definition L_PBg_0_1 : sstate := Eval vm_compute in lf0 (PBg true) (runF [sw_done] (PBg true)) 0.
Definition L_PBg_0 (r : bool) : sstate := if r then L_PBg_0_1 else L_PBg_0_0.
Definition L_PBg_1_0 : sstate := Eval vm_compute in lf0 (PBg false) (runF [sw_done] (PBg false)) 1.
Definition L_PBg_1_1 : sstate := Eval vm_compute in lf0 (PBg true) (runF [sw_done] (PBg true)) 1.
Definition L_PBg_1 (r : bool) : sstate := if r then L_PBg_1_1 else L_PBg_1_0.
Lemma run_PBg : forall r,
  sym_run segs FUEL [sw_done] (PBg r) true = Some [mkLeaf (L_PBg_0 r) RsCut; mkLeaf (L_PBg_1 r) RsEcall].
Proof. intros [|]; runc. Qed.
Definition GLg : positive := 100.
Definition s_PAg_CBg_0 : wsub := Eval vm_compute in infer_sub GLg (L_PAg_0 false) (CBg false).
Definition s_PAg_CBg_1 : wsub := Eval vm_compute in infer_sub GLg (L_PAg_0 true) (CBg true).
Definition s_PAg_CBg (r : bool) : wsub := if r then s_PAg_CBg_1 else s_PAg_CBg_0.
Definition s_PAg_Dg_0 : wsub := Eval vm_compute in infer_sub GLg (L_PAg_1 false) (Dg false).
Definition s_PAg_Dg_1 : wsub := Eval vm_compute in infer_sub GLg (L_PAg_1 true) (Dg true).
Definition s_PAg_Dg (r : bool) : wsub := if r then s_PAg_Dg_1 else s_PAg_Dg_0.
Definition s_PBg_CBg_0 : wsub := Eval vm_compute in infer_sub GLg (L_PBg_1 false) (CBg false).
Definition s_PBg_CBg_1 : wsub := Eval vm_compute in infer_sub GLg (L_PBg_1 true) (CBg true).
Definition s_PBg_CBg (r : bool) : wsub := if r then s_PBg_CBg_1 else s_PBg_CBg_0.
Definition s_PBg_Dg_0 : wsub := Eval vm_compute in infer_sub GLg (L_PBg_0 false) (Dg false).
Definition s_PBg_Dg_1 : wsub := Eval vm_compute in infer_sub GLg (L_PBg_0 true) (Dg true).
Definition s_PBg_Dg (r : bool) : wsub := if r then s_PBg_Dg_1 else s_PBg_Dg_0.
Lemma ent_PAg_CBg : forall r, entails (L_PAg_0 r) (CBg r) (s_PAg_CBg r) = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PAg_Dg : forall r, entails (L_PAg_1 r) (Dg r) (s_PAg_Dg r) = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PBg_CBg : forall r, entails (L_PBg_1 r) (CBg r) (s_PBg_CBg r) = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PBg_Dg : forall r, entails (L_PBg_0 r) (Dg r) (s_PBg_Dg r) = true.
Proof. intros [|]; vmtrue. Qed.
Lemma sv_PAg_106 : forall r, wsub_get (s_PAg_CBg r) 106 = SAlu ALU_SUB (SAlu ALU_ADD (SVar 5) (SLit 14)) (SVar 106).
Proof. intros [|]; reflexivity. Qed.
Lemma sv_PBg_106 : forall r, wsub_get (s_PBg_CBg r) 106 = SAlu ALU_SUB (SVar 106) (SVar 109).
Proof. intros [|]; reflexivity. Qed.
Definition E_exitg_0 : sstate := Eval vm_compute in lf0 (Dg false) (runF [] (Dg false)) 0.
Definition E_exitg_1 : sstate := Eval vm_compute in lf0 (Dg true) (runF [] (Dg true)) 0.
Definition E_exitg (r : bool) : sstate := if r then E_exitg_1 else E_exitg_0.
Lemma run_Dg : forall r, sym_run segs FUEL [] (Dg r) true = Some [mkLeaf (E_exitg r) RsEcall].
Proof. intros [|]; runc. Qed.

(* LPS 727298f3: [Jinit] also fixes variable 13 (AT_EXECFN's address), so the leaf's substitution keeps it
   too (as [sub_id7] in Drv_usage__G3.v).  Written as plain text; the list is the old one with 13 appended. *)
Definition sub_ok_n (s : wsub) (n : Z) : bool :=
  forallb (fun i : positive => sv_eqb (wsub_get s i) (SVar i)) [1; 2; 3; 4; 6; 25; 7; 8; 9; 10; 13]%positive
  && sv_eqb (wsub_get s 5%positive) (SLit n).
Definition BNZ3 (e : sv) : sprop := ltac2:(tb__ "0|0|
S1aS41S19S3Q8S1fP3Ve;Z1A3A3SfZ0A1A3").

(* LPS 727298f3: the launch packs the strings down from the stack top with a pad, so argv[0] has no
   alignment fact, and the copy of argv[0] into the message branches on the alignment of its
   address, byte by byte: the run from [Tn r n] reaches the first writev on several paths.  The
   check covers every leaf of the run, as the run returns them, with no filter: the first leaf holds
   the fact that byte [n] of argv[0] is nonzero (it contradicts the length [n]); each of the others,
   at least one, passes the per-leaf check [check_wleaf]. *)
Definition check_wleaf (r : bool) (n : Z) (w : sstate) : bool :=
  match apply_xforms w (xs_ibuf n) with
  | Some wx =>
      match nth_error (ss_objs wx) 1 with
      | Some o =>
          sv_eqb (ob_lo o) (SLit (-560)) && sv_eqb (ob_hi o) (SLit (n - 546))
          && dflt_writable (ob_dflt o) && negb (is_arr (ob_dflt o))
          && match cells_bytes (ob_cells o) (SLit (-560)) 0 (Z.to_nat (14 + n)) with
             | Some bl => list_eqb bexp_eqb bl (BLn n)
             | None => false
             end
      | None => false
      end
      && negb (state_has_rl 4 wx)
      && (let wl := obj_to_list wx 1 4 in
          let s := (5%positive, SLit n) :: infer_sub GLg wl (E_Wg r) in
          entails wl (E_Wg r) s && sub_ok_n s n)
  | None => false
  end.

Definition check_core (r : bool) (n : Z) (res : option (list leaf)) : bool :=
  swf (Tn r n)
  && match res with
     | Some (a :: ((_ :: _) as ws)) =>
         existsb (sprop_eqb (BNZ3 (SLit n))) (ss_facts (lf_state a))
         && forallb (fun l => check_wleaf r n (lf_state l)) ws
     | _ => false
     end.

Definition check_range (r : bool) (a len : nat) : bool :=
  forallb (fun k => check_core r (Z.of_nat k) (sym_run segs FUELn [] (Tn r (Z.of_nat k)) true)) (seq a len).
End Drv_usage_small_states.

Module Drv_usage_mid_states.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_small_states.
Import ListNotations.

Import UAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition xs_ibuf2 (n : Z) : list xform := ltac2:(tb__ "0|0|
S0S97S99U0SfN230A1A2S0S97S99U1SfSe8Vn;Z229A2A1A2S1S97A1A3A3").
Definition BLm (n : Z) : list bexp := ltac2:(tb__ "0|0|
SeS50S0S50S51Z75A1S0S50S51Z73A1S0S50S51Z61A1S0S50S51Z67A1S0S50S51Z65A1S0S50S51Z3aA1S0S50S51Z20A1S1S50A1A3A3A3A3A3A3A3Se2ScS50ScS52P3Se7R1A1A2Lj;Se1U0Se9Vn;A1A2A4A3").

Local Ltac vmtrue := vm_cast_no_check (@eq_refl bool true).
Local Ltac runc := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast.

(* The first writev of a message of 81 to 87 bytes (argv[0] of 67 to 73 bytes), over the length
   [SVar 5]: [ug_join_n] of the arrivals at lengths 73 and 72 (Drv_usage_states); the buffer is
   [sp-560, sp+v5-553). *)
Definition EM_hi : sv := SAlu ALU_ADD (SVar 5) (SLit 18446744073709551063).
Definition EM_rs : list (nat * sv) :=
  [(5%nat, SVar 100); (7%nat, SVar 101);
   (13%nat, SAlu ALU_XOR (SAlu ALU_ADD (SVar 1) EM_hi) (SAlu ALU_ADD (SVar 1) (SLit (-560))));
   (14%nat, SVar 102); (15%nat, SVar 103); (16%nat, SVar 104); (22%nat, SAlu ALU_ADD (SVar 5) (SLit 14));
   (25%nat, SVar 5); (27%nat, SVar 5); (28%nat, SVar 105)].
Definition EM_dr0 : list Z := [-1088; -1104; -1152; -1160; -1216].
Definition EM_cs0 : list cell :=
  [mkCell (SLit (-1088)) 8 (SVar 5); mkCell (SLit (-1104)) 8 (SVar 5);
   mkCell (SLit (-1152)) 8 (SAlu ALU_SUB (SLit 2147483640) (SVar 5));
   mkCell (SLit (-1160)) 8 (SAlu ALU_ADD (SVar 5) (SLit 7));
   mkCell (SLit (-1216)) 8 (SAlu ALU_ADD (SVar 5) (SLit 7))].
Definition EM_o1 : sobj := mkObj (SVar 1) (SLit (-560)) EM_hi [] (DList 4).
Definition EM_img : cell := mkCell (SLit 171448) 8 (SAlu ALU_ADD (SVar 1) EM_hi).
Definition EM_F (r : bool) : list sprop :=
  SPUle (SLit 67) (SVar 5) :: SPUle (SVar 5) (SLit 73) :: filter (ug_sprop_no 5) (ss_facts (T_sn1 r)).
Definition E_Mg_0 : sstate := Eval vm_compute in
  ug_join_n (ss_next (T_sn1 false)) 106 EM_rs EM_dr0 EM_cs0 EM_o1 EM_hi EM_img (EM_F false)
    (wl_of (xs_ibuf2 73) (Tn false 73)) (wl_of (xs_ibuf2 72) (Tn false 72)).
Definition E_Mg_1 : sstate := Eval vm_compute in
  ug_join_n (ss_next (T_sn1 true)) 106 EM_rs EM_dr0 EM_cs0 EM_o1 EM_hi EM_img (EM_F true)
    (wl_of (xs_ibuf2 73) (Tn true 73)) (wl_of (xs_ibuf2 72) (Tn true 72)).
Definition E_Mg (r : bool) : sstate := if r then E_Mg_1 else E_Mg_0.

Definition GLm : positive := 100.

Definition RO_INPUT : Z := ltac2:(tb__ "0|0|
Z10421").
Definition PAm (r : bool) : sstate := S_after_write (E_Mg r) (reg_sv (E_Mg r) 22).
Definition PAma (r : bool) : sstate := add_facts [SPUle (SVar 106) (SAlu ALU_ADD (SVar 5) (SLit 7))] (PAm r).
Definition PAmb (r : bool) : sstate := add_facts [SPUle (SAlu ALU_ADD (SVar 5) (SLit 8)) (SVar 106)] (PAm r).
Definition L_PAma_0_0 : sstate := Eval vm_compute in lf0 (PAma false) (runF [sw_done] (PAma false)) 0.
Definition L_PAma_0_1 : sstate := Eval vm_compute in lf0 (PAma true) (runF [sw_done] (PAma true)) 0.
Definition L_PAma_0 (r : bool) : sstate := if r then L_PAma_0_1 else L_PAma_0_0.
Lemma run_PAma : forall r, sym_run segs FUEL [sw_done] (PAma r) true = Some [mkLeaf (L_PAma_0 r) RsEcall].
Proof. intros [|]; runc. Qed.
Definition L_PAmb_0_0 : sstate := Eval vm_compute in lf0 (PAmb false) (runF [sw_done] (PAmb false)) 0.
Definition L_PAmb_0_1 : sstate := Eval vm_compute in lf0 (PAmb true) (runF [sw_done] (PAmb true)) 0.
Definition L_PAmb_0 (r : bool) : sstate := if r then L_PAmb_0_1 else L_PAmb_0_0.
Definition L_PAmb_1_0 : sstate := Eval vm_compute in lf0 (PAmb false) (runF [sw_done] (PAmb false)) 1.
Definition L_PAmb_1_1 : sstate := Eval vm_compute in lf0 (PAmb true) (runF [sw_done] (PAmb true)) 1.
Definition L_PAmb_1 (r : bool) : sstate := if r then L_PAmb_1_1 else L_PAmb_1_0.
Lemma run_PAmb : forall r,
  sym_run segs FUEL [sw_done] (PAmb r) true = Some [mkLeaf (L_PAmb_0 r) RsEcall; mkLeaf (L_PAmb_1 r) RsCut].
Proof. intros [|]; runc. Qed.

(* Its loop heads [CB2m] (both iovecs left, from [L_PAma_0]), [CB1m] (the second left, from
   [L_PAmb_0]) and end [Dm] (from [L_PAmb_1]) by [ug_gen_cut]; the iovec words are at sp-1224 ..
   sp-1200 ([iovA]). *)
Definition CB2m_rs : list (nat * sv) :=
  [(1%nat, SVar 107); (5%nat, SVar 100); (7%nat, SVar 101); (13%nat, SVar 108); (15%nat, SVar 106);
   (16%nat, SVar 104); (22%nat, SAlu ALU_ADD (SVar 106) (SLit 7)); (28%nat, SVar 105)].
Definition CB2m_cs : list cell :=
  [mkCell (SLit (-1216)) 8 (SVar 106);
   mkCell (SLit (-1224)) 8 (SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_ADD (SVar 1) (SLit (-553))) (SVar 5)) (SVar 106))].
Definition CB2m_fl : list sprop := [SPUle (SVar 106) (SAlu ALU_ADD (SVar 5) (SLit 6))].
Definition CB2m_0 : sstate := Eval vm_compute in ug_gen_cut 100 109 CB2m_rs [-1224; -1216] CB2m_cs CB2m_fl (L_PAma_0 false).
Definition CB2m_1 : sstate := Eval vm_compute in ug_gen_cut 100 109 CB2m_rs [-1224; -1216] CB2m_cs CB2m_fl (L_PAma_0 true).
Definition CB2m (r : bool) : sstate := if r then CB2m_1 else CB2m_0.
Definition CB1m_rs : list (nat * sv) :=
  [(1%nat, SVar 107); (5%nat, SVar 100); (7%nat, SVar 101); (13%nat, SVar 108); (15%nat, SVar 106);
   (16%nat, SVar 104); (19%nat, SVar 109); (22%nat, SVar 106); (28%nat, SVar 105)].
Definition CB1m_cs : list cell :=
  [mkCell (SLit (-1200)) 8 (SVar 106); mkCell (SLit (-1208)) 8 (SAlu ALU_SUB (SLit 66600) (SVar 106))].
Definition CB1m_fl : list sprop := [SPUle (SLit 1) (SVar 106); SPUle (SVar 106) (SLit 6)].
Definition CB1m_0 : sstate := Eval vm_compute in ug_gen_cut 100 110 CB1m_rs iovA CB1m_cs CB1m_fl (L_PAmb_0 false).
Definition CB1m_1 : sstate := Eval vm_compute in ug_gen_cut 100 110 CB1m_rs iovA CB1m_cs CB1m_fl (L_PAmb_0 true).
Definition CB1m (r : bool) : sstate := if r then CB1m_1 else CB1m_0.
Definition Dm_rs : list (nat * sv) :=
  [(1%nat, SVar 120); (5%nat, SVar 100); (7%nat, SVar 101); (10%nat, SVar 121); (12%nat, SVar 122);
   (13%nat, SVar 123); (14%nat, SVar 129); (15%nat, SVar 124); (16%nat, SVar 104); (18%nat, SVar 125);
   (19%nat, SVar 126); (20%nat, SVar 127); (22%nat, SVar 128); (28%nat, SVar 105)].
Definition Dm_0 : sstate := Eval vm_compute in ug_gen_cut 100 130 Dm_rs iovA [] [] (L_PAmb_1 false).
Definition Dm_1 : sstate := Eval vm_compute in ug_gen_cut 100 130 Dm_rs iovA [] [] (L_PAmb_1 true).
Definition Dm (r : bool) : sstate := if r then Dm_1 else Dm_0.

Definition PB2m (r : bool) : sstate :=
  add_facts [SPUle (SVar 109) (SLit 131078)] (S_after_write (CB2m r) (reg_sv (CB2m r) 22)).
Definition PB2ma (r : bool) : sstate := add_facts [SPUle (SVar 109) (SVar 106)] (PB2m r).
Definition PB2mb (r : bool) : sstate := add_facts [SPUle (SAlu ALU_ADD (SVar 106) (SLit 1)) (SVar 109)] (PB2m r).
Definition PB1m (r : bool) : sstate := S_after_write (CB1m r) (reg_sv (CB1m r) 22).
Definition L_PB2ma_0_0 : sstate := Eval vm_compute in lf0 (PB2ma false) (runF [sw_done] (PB2ma false)) 0.
Definition L_PB2ma_0_1 : sstate := Eval vm_compute in lf0 (PB2ma true) (runF [sw_done] (PB2ma true)) 0.
Definition L_PB2ma_0 (r : bool) : sstate := if r then L_PB2ma_0_1 else L_PB2ma_0_0.
Lemma run_PB2ma : forall r, sym_run segs FUEL [sw_done] (PB2ma r) true = Some [mkLeaf (L_PB2ma_0 r) RsEcall].
Proof. intros [|]; runc. Qed.
Definition L_PB2mb_0_0 : sstate := Eval vm_compute in lf0 (PB2mb false) (runF [sw_done] (PB2mb false)) 0.
Definition L_PB2mb_0_1 : sstate := Eval vm_compute in lf0 (PB2mb true) (runF [sw_done] (PB2mb true)) 0.
Definition L_PB2mb_0 (r : bool) : sstate := if r then L_PB2mb_0_1 else L_PB2mb_0_0.
Definition L_PB2mb_1_0 : sstate := Eval vm_compute in lf0 (PB2mb false) (runF [sw_done] (PB2mb false)) 1.
Definition L_PB2mb_1_1 : sstate := Eval vm_compute in lf0 (PB2mb true) (runF [sw_done] (PB2mb true)) 1.
Definition L_PB2mb_1 (r : bool) : sstate := if r then L_PB2mb_1_1 else L_PB2mb_1_0.
Lemma run_PB2mb : forall r,
  sym_run segs FUEL [sw_done] (PB2mb r) true = Some [mkLeaf (L_PB2mb_0 r) RsCut; mkLeaf (L_PB2mb_1 r) RsEcall].
Proof. intros [|]; runc. Qed.
Definition L_PB1m_0_0 : sstate := Eval vm_compute in lf0 (PB1m false) (runF [sw_done] (PB1m false)) 0.
Definition L_PB1m_0_1 : sstate := Eval vm_compute in lf0 (PB1m true) (runF [sw_done] (PB1m true)) 0.
Definition L_PB1m_0 (r : bool) : sstate := if r then L_PB1m_0_1 else L_PB1m_0_0.
Definition L_PB1m_1_0 : sstate := Eval vm_compute in lf0 (PB1m false) (runF [sw_done] (PB1m false)) 1.
Definition L_PB1m_1_1 : sstate := Eval vm_compute in lf0 (PB1m true) (runF [sw_done] (PB1m true)) 1.
Definition L_PB1m_1 (r : bool) : sstate := if r then L_PB1m_1_1 else L_PB1m_1_0.
Lemma run_PB1m : forall r,
  sym_run segs FUEL [sw_done] (PB1m r) true = Some [mkLeaf (L_PB1m_0 r) RsCut; mkLeaf (L_PB1m_1 r) RsEcall].
Proof. intros [|]; runc. Qed.

Definition s_PAma_CB2m_0 : wsub := Eval vm_compute in infer_sub GLm (L_PAma_0 false) (CB2m false).
Definition s_PAma_CB2m_1 : wsub := Eval vm_compute in infer_sub GLm (L_PAma_0 true) (CB2m true).
Definition s_PAma_CB2m (r : bool) : wsub := if r then s_PAma_CB2m_1 else s_PAma_CB2m_0.
Definition s_PAmb_CB1m_0 : wsub := Eval vm_compute in infer_sub GLm (L_PAmb_0 false) (CB1m false).
Definition s_PAmb_CB1m_1 : wsub := Eval vm_compute in infer_sub GLm (L_PAmb_0 true) (CB1m true).
Definition s_PAmb_CB1m (r : bool) : wsub := if r then s_PAmb_CB1m_1 else s_PAmb_CB1m_0.
Definition s_PAmb_Dm_0 : wsub := Eval vm_compute in infer_sub GLm (L_PAmb_1 false) (Dm false).
Definition s_PAmb_Dm_1 : wsub := Eval vm_compute in infer_sub GLm (L_PAmb_1 true) (Dm true).
Definition s_PAmb_Dm (r : bool) : wsub := if r then s_PAmb_Dm_1 else s_PAmb_Dm_0.
Definition s_PB2ma_CB2m_0 : wsub := Eval vm_compute in infer_sub GLm (L_PB2ma_0 false) (CB2m false).
Definition s_PB2ma_CB2m_1 : wsub := Eval vm_compute in infer_sub GLm (L_PB2ma_0 true) (CB2m true).
Definition s_PB2ma_CB2m (r : bool) : wsub := if r then s_PB2ma_CB2m_1 else s_PB2ma_CB2m_0.
Definition s_PB2mb_CB1m_0 : wsub := Eval vm_compute in infer_sub GLm (L_PB2mb_1 false) (CB1m false).
Definition s_PB2mb_CB1m_1 : wsub := Eval vm_compute in infer_sub GLm (L_PB2mb_1 true) (CB1m true).
Definition s_PB2mb_CB1m (r : bool) : wsub := if r then s_PB2mb_CB1m_1 else s_PB2mb_CB1m_0.
Definition s_PB2mb_Dm_0 : wsub := Eval vm_compute in infer_sub GLm (L_PB2mb_0 false) (Dm false).
Definition s_PB2mb_Dm_1 : wsub := Eval vm_compute in infer_sub GLm (L_PB2mb_0 true) (Dm true).
Definition s_PB2mb_Dm (r : bool) : wsub := if r then s_PB2mb_Dm_1 else s_PB2mb_Dm_0.
Definition s_PB1m_CB1m_0 : wsub := Eval vm_compute in infer_sub GLm (L_PB1m_1 false) (CB1m false).
Definition s_PB1m_CB1m_1 : wsub := Eval vm_compute in infer_sub GLm (L_PB1m_1 true) (CB1m true).
Definition s_PB1m_CB1m (r : bool) : wsub := if r then s_PB1m_CB1m_1 else s_PB1m_CB1m_0.
Definition s_PB1m_Dm_0 : wsub := Eval vm_compute in infer_sub GLm (L_PB1m_0 false) (Dm false).
Definition s_PB1m_Dm_1 : wsub := Eval vm_compute in infer_sub GLm (L_PB1m_0 true) (Dm true).
Definition s_PB1m_Dm (r : bool) : wsub := if r then s_PB1m_Dm_1 else s_PB1m_Dm_0.
Lemma ent_PAma_CB2m : forall r, entails (L_PAma_0 r) (CB2m r) (s_PAma_CB2m r) = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PAmb_CB1m : forall r, entails (L_PAmb_0 r) (CB1m r) (s_PAmb_CB1m r) = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PAmb_Dm : forall r, entails (L_PAmb_1 r) (Dm r) (s_PAmb_Dm r) = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PB2ma_CB2m : forall r, entails (L_PB2ma_0 r) (CB2m r) (s_PB2ma_CB2m r) = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PB2mb_CB1m : forall r, entails (L_PB2mb_1 r) (CB1m r) (s_PB2mb_CB1m r) = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PB2mb_Dm : forall r, entails (L_PB2mb_0 r) (Dm r) (s_PB2mb_Dm r) = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PB1m_CB1m : forall r, entails (L_PB1m_1 r) (CB1m r) (s_PB1m_CB1m r) = true.
Proof. intros [|]; vmtrue. Qed.
Lemma ent_PB1m_Dm : forall r, entails (L_PB1m_0 r) (Dm r) (s_PB1m_Dm r) = true.
Proof. intros [|]; vmtrue. Qed.
Lemma sv_PAma : forall r, wsub_get (s_PAma_CB2m r) 106 = SAlu ALU_SUB (SAlu ALU_ADD (SVar 5) (SLit 7)) (SVar 106).
Proof. intros [|]; reflexivity. Qed.
Lemma sv_PAmb : forall r,
  wsub_get (s_PAmb_CB1m r) 106 = SAlu ALU_SUB (SLit 7) (SAlu ALU_SUB (SVar 106) (SAlu ALU_ADD (SVar 5) (SLit 7))).
Proof. intros [|]; reflexivity. Qed.
Lemma sv_PB2ma : forall r, wsub_get (s_PB2ma_CB2m r) 106 = SAlu ALU_SUB (SVar 106) (SVar 109).
Proof. intros [|]; reflexivity. Qed.
Lemma sv_PB2mb : forall r, wsub_get (s_PB2mb_CB1m r) 106 = SAlu ALU_SUB (SLit 7) (SAlu ALU_SUB (SVar 109) (SVar 106)).
Proof. intros [|]; reflexivity. Qed.
Lemma sv_PB1m : forall r, wsub_get (s_PB1m_CB1m r) 106 = SAlu ALU_SUB (SVar 106) (SVar 110).
Proof. intros [|]; reflexivity. Qed.

Definition E_Zm_0 : sstate := Eval vm_compute in lf0 (Dm false) (runF [] (Dm false)) 0.
Definition E_Zm_1 : sstate := Eval vm_compute in lf0 (Dm true) (runF [] (Dm true)) 0.
Definition E_Zm (r : bool) : sstate := if r then E_Zm_1 else E_Zm_0.
Lemma run_Dm : forall r, sym_run segs FUEL [] (Dm r) true = Some [mkLeaf (E_Zm r) RsEcall].
Proof. intros [|]; runc. Qed.
Definition PZm (r : bool) : sstate := S_after (E_Zm r) (SLit 0) (ss_objs (E_Zm r)) (ss_next (E_Zm r)).
Definition E_exitm_0 : sstate := Eval vm_compute in lf0 (PZm false) (runF [] (PZm false)) 0.
Definition E_exitm_1 : sstate := Eval vm_compute in lf0 (PZm true) (runF [] (PZm true)) 0.
Definition E_exitm (r : bool) : sstate := if r then E_exitm_1 else E_exitm_0.
Lemma run_PZm : forall r, sym_run segs FUEL [] (PZm r) true = Some [mkLeaf (E_exitm r) RsEcall].
Proof. intros [|]; runc. Qed.

(* As [check_core], over every leaf of the run (see there). *)
Definition check_wleaf_m (r : bool) (n : Z) (w : sstate) : bool :=
  match apply_xforms w (xs_ibuf2 n) with
  | Some wx =>
      match nth_error (ss_objs wx) 1 with
      | Some o =>
          sv_eqb (ob_lo o) (SLit (-560)) && sv_eqb (ob_hi o) (SLit (n - 553))
          && dflt_writable (ob_dflt o) && negb (is_arr (ob_dflt o))
          && match cells_bytes (ob_cells o) (SLit (-560)) 0 (Z.to_nat (7 + n)) with
             | Some bl => list_eqb bexp_eqb bl (BLm n)
             | None => false
             end
      | None => false
      end
      && negb (state_has_rl 4 wx)
      && (let wl := obj_to_list wx 1 4 in
          let s := (5%positive, SLit n) :: infer_sub GLm wl (E_Mg r) in
          entails wl (E_Mg r) s && sub_ok_n s n)
  | None => false
  end.

Definition check_core_m (r : bool) (n : Z) (res : option (list leaf)) : bool :=
  swf (Tn r n)
  && match res with
     | Some (a :: ((_ :: _) as ws)) =>
         existsb (sprop_eqb (BNZ3 (SLit n))) (ss_facts (lf_state a))
         && forallb (fun l => check_wleaf_m r n (lf_state l)) ws
     | _ => false
     end.
Definition check_range_m (r : bool) (a len : nat) : bool :=
  forallb (fun k => check_core_m r (Z.of_nat k) (sym_run segs FUELn [] (Tn r (Z.of_nat k)) true)) (seq a len).
End Drv_usage_mid_states.

Module Drv_usage_small_chk1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_small_states.

Lemma check_range_1 : forall r, check_range r 0 17 = true.
Proof. intros [|]; unfold check_range; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.fast_forallb. Qed.
End Drv_usage_small_chk1.

Module Drv_usage_small_chk3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_small_states.

Lemma check_range_3 : forall r, check_range r 34 17 = true.
Proof. intros [|]; unfold check_range; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.fast_forallb. Qed.
End Drv_usage_small_chk3.
