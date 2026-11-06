(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StoreOk SimInv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require CatSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ShapeAlg MmapSim SymExec SymExec2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun SymDrive MemSplit RefMemcpyLib.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SimInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim.ExitSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MemSplit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import SymDriveX.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Ltac1 Control List Constr Array Int Env Std Ident.
Set Default Proof Mode "Classic".
Import ListNotations.
Local Open Scope bv_scope.
Import SX2. Import SX2S.

(* [comment removed for export] *)
Ltac sc_cands := constr:(tt).

(* [comment removed for export] *)
Ltac2 sc2_body (c : constr) : constr option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constant cst _ => Some (Std.eval_unfold [(Std.ConstRef cst, Std.AllOccurrences)] c)
  | _ => None
  end.
(* [comment removed for export] *)
Ltac2 sc2_var_body (c : constr) : constr option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var id =>
      (match List.find_opt (fun (j, _, _) => Ident.equal id j) (Control.hyps ()) with
       | Some (_, b, _) => b
       | None => None
       end)
  | _ => None
  end.
Ltac2 rec sc2_find (lit : constr) (cands : constr) : constr option :=
  match Constr.Unsafe.kind cands with
  | Constr.Unsafe.App _ args =>
      if Int.equal (Array.length args) 4 then
        (let c := Array.get args 2 in
         match sc2_body c with
         | Some b => if Constr.equal b lit then Some c else sc2_find lit (Array.get args 3)
         | None => sc2_find lit (Array.get args 3)
         end)
      else None
  | _ => None
  end.
(* [comment removed for export] *)
Ltac2 sc2_resolve (lit : constr) (pref : constr) (cands : constr) (k : Ltac1.t) : unit :=
  let hit :=
    match sc2_body pref with
    | Some b => if Constr.equal b lit then Some pref else None
    | None => (match sc2_var_body pref with
               | Some b => if Constr.equal b lit then Some pref else None
               | None => None
               end)
    end in
  let r := match hit with Some c => Some c | None => sc2_find lit cands end in
  match r with
  | Some c => Ltac1.apply k [Ltac1.of_constr c] Ltac1.run
  | None => Ltac1.apply k [Ltac1.of_constr lit] Ltac1.run
  end.
(* [comment removed for export] *)
Ltac sc_resolve lit pref k :=
  let cands := sc_cands in
  let f := ltac2:(l p c kk |- sc2_resolve (Option.get (Ltac1.to_constr l)) (Option.get (Ltac1.to_constr p)) (Option.get (Ltac1.to_constr c)) kk) in
  f lit pref cands k.
(* [comment removed for export] *)
Ltac sc_name V t k :=
  tryif first [ is_const t | is_var t ] then k t
  else (pose (V := t); k V).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac sc_input_regs HR :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
      tryif first [ is_const sr | is_var sr ] then idtac
      else (let V := fresh "WH_SR" in
            sc_resolve sr sr ltac:(fun t => sc_name V t ltac:(fun SRi => change_no_check (regs_ok E SRi R) in HR)))
  end.
Ltac sc_input_know HK :=
  lazymatch type of HK with
  | know_ok ?segs ?E ?M ?kn =>
      tryif first [ is_const kn | is_var kn ] then idtac
      else (let V := fresh "WH_KN" in
            sc_resolve kn kn ltac:(fun t => sc_name V t ltac:(fun KNi => change_no_check (know_ok segs E M KNi) in HK)))
  end.

Ltac run_block_with_hid HR HK fuel stops scr NX keep :=
  sc_input_regs HR; sc_input_know HK;
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- realizes _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (SS ?pc' ?sr' ?log' ?skn' ?nx', ?scs, ?scr') =>
          let c := eval vm_compute in (carry log' kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            let SRv := fresh "WH_SR" in let LG := fresh "WH_LG" in let SKv := fresh "WH_SK" in let KNv := fresh "WH_KN" in
            sc_resolve sr' sr ltac:(fun srt => sc_name SRv srt ltac:(fun SR =>
            pose (LG := log');
            sc_resolve skn' kn ltac:(fun skt => sc_name SKv skt ltac:(fun SK =>
            sc_resolve kn' kn ltac:(fun knt => sc_name KNv knt ltac:(fun KN =>
            eapply (rz_run segs fuel stops scr pc sr kn NX (SS pc' SR LG SK nx') scs scr' KN scs2 hs2 E M rom R model T);
            [ vm_cast_no_check (@eq_refl _ (SS pc' SR LG SK nx', scs, scr'))
            | vm_cast_no_check (@eq_refl _ (KN, scs2, hs2))
            | exact HR | exact HK
            | split_foralls
            | split_foralls
            | try reflexivity; try assumption
            | try reflexivity; try assumption
            | clear HR HK;
              let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in
              intros R' M' HR HK EQM; cbn [s_pc s_regs s_log] in HR, EQM |- *;
              lazymatch keep with
              | true => idtac
              | false => clear EQM; try clear R; try clear M;
                         try rename R' into R; try rename M' into M
              end ]))))))
          end
        end
      end
    end
  end.

Module OptIn.
#[export] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_hid HR HK fuel stops scr NX keep.
End OptIn.
