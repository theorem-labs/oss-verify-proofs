(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb PropExec HUWorld HUWorldK HUReadBase HUReadStage HUTargetFull HUHandoff HUInitPcs.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeCfg NodesCfg LedgerCfg AllocCfg MiscCfg.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxRn FxImage FxHandoff FxHoBuild FxSys FxMisc FxDrive FxDriveId FxHb.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HoBridge HoDrive HoDriveX.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import H0Lim.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require ConeCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition odflt {A : Type} (d : A) (o : option A) : A := match o with Some x => x | None => d end.
Definition is_some {A : Type} (o : option A) : bool := match o with Some _ => true | None => false end.
Lemma odflt_some : forall (A : Type) (d : A) (o : option A), is_some o = true -> o = Some (odflt d o).
Proof. intros A d [x|] H; [reflexivity | discriminate H]. Qed.
Definition IMH : fimage := odflt [] (mk_fimage RSEGS).
Lemma IMH_some : is_some (mk_fimage RSEGS) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma IMH_eq : mk_fimage RSEGS = Some IMH.
Proof. exact (odflt_some _ [] _ IMH_some). Qed.

Definition CODE : itrie finstr := odflt iempty (build_code RSEGS init_pcs).
Lemma CODE_some : is_some (build_code RSEGS init_pcs) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma CODE_eq : build_code RSEGS init_pcs = Some CODE.
Proof. exact (odflt_some _ iempty _ CODE_some). Qed.
Lemma CODE_ok : code_ok RSEGS CODE.
Proof. exact (build_code_ok RSEGS init_pcs CODE CODE_eq). Qed.

(* [comment removed for export] *)
Definition KEEP : list int := [3%uint63].
Definition on_kept (f : hfact) : bool :=
  match f with
  | HCell t _ _ _ | HVal t _ _ | HBytes t _ _ _ | HZero t _ _ | HWr t _ _ => existsb (fun u => (t =? u)%uint63) KEEP
  | _ => false
  end.
Definition hfacts_all (k : Z) : list hfact := if k =? 0 then facts_k0b else facts_kb k.   (* [comment removed for export] *)
Definition hfacts (k : Z) : list hfact := List.filter (fun f => negb (on_kept f)) (hfacts_all k).
Definition kfacts (k : Z) : list hfact := List.filter on_kept (hfacts_all k).
Definition hnb (k : Z) : Z := if k =? 0 then 69632 else nbk k.
Definition hshapes (k : Z) := shapes4 (ioz 0x10000) (ioz 0x354000) (ioz (hnb k)) (Some PKUnk).
Definition HD (k : Z) : sdesc := ho_build IMH (hfacts k) (ioz PC_TARGET) (hshapes k).
Definition F0 (k : Z) : fstate := state_of (HD k).
Definition L0 (k : Z) : fledger := ledger4 (ioz (hnb k)) (hnb k).

Definition RB : Z := 2 ^ 26.      (* [comment removed for export] *)
Definition RC : Z := 8.           (* [comment removed for export] *)
Definition BP : Z := 0xe1df0.     (* [comment removed for export] *)
Definition XS : fstate -> fledger -> int -> option dres := xsys_none.
Definition the_tree (k : Z) (fuel : nat) : dtree :=
  drive IMH CODE RB RC LIM RTgt KEEP XS (xask_b5 IMH CODE) (ioz BP) 20 fuel (F0 k) (L0 k) 200%uint63.
(* [comment removed for export] *)
Definition leaf_bp (F : fstate) (r : stop) : bool :=
  match r with SBreak => (f_pc F =? ioz BP)%uint63 | _ => false end.
Definition tree_ok (k : Z) (fuel : nat) : Prop := tree_all leaf_bp (the_tree k fuel) = true.

Definition KS : list Z := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10].
(* [comment removed for export] *)
Lemma pre_all : forallb (fun k => ho_check IMH (hfacts k) (HD k) && forallb (fact_tags_lt 200) (hfacts k)
                                  && forallb (pristine_b (f_mem (F0 k))) KEEP) KS = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma res_bounds : live_bytes (segments_reserved RSEGS) <= RB /\ Z.of_nat (length (segments_reserved RSEGS)) <= RC
  /\ chain_cover (res_pairs (segments_reserved RSEGS)) (to_Z (ioz 0x10000)) (to_Z (ioz 0x354000)) = true.
Proof. vm_compute. repeat split; congruence. Qed.
