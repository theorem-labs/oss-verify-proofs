(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import Fs.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec StoreOk Frame MallocDefs AgentLib MmapSim ShapeAlg Spec
  HUEnframeBase HUTargetPre HUWorld HUWorldK HUReadBase HUReadStage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope Z_scope.

Record tgt_entry_full (sp0 : word) (k : Z) (buf : Z) (can : word) (content : list byte) (VM : VmMaps)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := TGT_ENTRY_FULL {
  tf_entry : tgt_entry (bv_unsigned sp0) buf (bv_unsigned can) content R M;
  tf_frame : main_frame (bv_unsigned sp0) M;
  tf_world : exists (mb bw B : word) (brkv mas tid sec : Z),
      bv_unsigned bw = brkv /\
      ( (k = 0 /\ Z.of_nat (length content) < 65536 /\ buf = bv_unsigned B + 32
           /\ world0 (bv_unsigned sp0) (bv_unsigned mb + 4096) (bv_unsigned B) brkv mas tid (bv_unsigned can) sec M
           /\ vm_pre VM sp0 mb bw B)
      \/ (1 <= k <= 10 /\ capk (k - 1) <= Z.of_nat (length content) < capk k /\ buf = bv_unsigned B + offk k
           /\ world_k (bv_unsigned sp0) k (bv_unsigned mb + 4096) (bv_unsigned B) brkv mas tid (bv_unsigned can) sec M
           /\ vm_stage VM sp0 mb bw B (nbk k)) )
}.

(* [comment removed for export] *)
Lemma tgt_entry_of_full : forall sp0 k buf can content VM R M,
  tgt_entry_full sp0 k buf can content VM R M -> tgt_entry (bv_unsigned sp0) buf (bv_unsigned can) content R M.
Proof. intros. apply (tf_entry _ _ _ _ _ _ _ _ H). Qed.
