(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import Fs.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import MallocDefs.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import EnframeDefs UbWorld.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec TargetSpec TargetKDefs UbTargetPre UbWorldK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Record target_pre_k (k sp0 B area brkv mas tid : Z) (content : list byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := TARGET_PRE_K {
  (* [comment removed for export] *)
  tk_ra : getr R 1 = Z_to_bv 64 0x13c34;
  tk_sp : getr R 2 = Z_to_bv 64 (sp0 - 128);
  tk_gp : getr R 3 = Z_to_bv 64 0x10800;
  tk_tp : getr R 4 = Z_to_bv 64 0x36c60;
  tk_a0 : getr R 10 = Z_to_bv 64 (B + offk k + 2);                         (* [comment removed for export] *)
  tk_a1 : getr R 11 = Z_to_bv 64 (hdr_cfglen content);                      (* [comment removed for export] *)
  tk_a2 : getr R 12 = Z_to_bv 64 (B + offk k + 6 + hdr_cfglen content);     (* [comment removed for export] *)
  tk_a3 : getr R 13 = Z_to_bv 64 (hdr_paylen content);                      (* [comment removed for export] *)
  tk_s0 : getr R 8 = Z_to_bv 64 (B + offk k + 2);
  tk_s1 : getr R 9 = Z_to_bv 64 (B + offk k);                              (* [comment removed for export] *)
  tk_s2 : getr R 18 = Z_to_bv 64 (hdr_cfglen content);
  tk_s3 : getr R 19 = Z_to_bv 64 (B + offk k + 6 + hdr_cfglen content);
  tk_s4 : getr R 20 = Z_to_bv 64 (hdr_paylen content);
  tk_s5 : getr R 21 = Z_to_bv 64 (if hdr_b1 content <? 128 then hdr_b1 content else hdr_b1 content - 256 + 2 ^ 64);
            (* [comment removed for export] *)
  tk_s6 : getr R 22 = Z_to_bv 64 READ_STAGE;                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  tk_sp0 : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0;
  tk_len : 6 + hdr_cfglen content <= Z.of_nat (length content);
  tk_L   : capk (k - 1) <= Z.of_nat (length content) < capk k;              (* [comment removed for export] *)
  (* [comment removed for export] *)
  tk_stack : stack_writableZ M sp0;
  tk_frame : main_frame sp0 M;
  tk_world : world_k k area B brkv mas tid M;                                (* [comment removed for export] *)
  tk_content : rdn RSEGS M (Z_to_bv 64 (B + offk k)) (length content) = Some content
}.

(* [comment removed for export] *)
Record target_vm_k (k sp0 B area : Z) (VM : VmMaps) : Prop := TARGET_VM_K {
  tvk_res   : vm_reserved VM = segments_reserved RSEGS;
  tvk_limit : 2 ^ 31 <= vm_limit VM;
  tvk_has   : In (Z_to_bv 64 B, Z_to_bv 64 (nbk k)) (vm_maps VM);
  tvk_area  : exists lo sz, In (lo, sz) (vm_maps VM)
                /\ bv_unsigned lo <= area /\ area + 4096 <= bv_unsigned lo + bv_unsigned sz;
  tvk_len   : (length (vm_maps VM) <= 9)%nat;
  tvk_small : Forall (fun p => 0 < bv_unsigned (snd p) <= 2 ^ 30
                               /\ bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64) (vm_maps VM);
  tvk_seps  : seps (vm_maps VM);
  tvk_live  : live_bytes (vm_maps VM) <= nbk k + 2 ^ 20;
  (* [comment removed for export] *)
  tvk_sp    : vm_init_sp VM = Z_to_bv 64 sp0;
  tvk_B_top : B + nbk k <= alloc_top VM;
  tvk_area_top : area + 4096 <= alloc_top VM
}.

(* [comment removed for export] *)
Lemma t_body_target_k : forall k content fs,
  1 <= k <= 10 ->
  capk (k - 1) <= Z.of_nat (length content) < capk k ->
  t_body content fs = t_target content fs.
Proof.
  intros k content fs Hk HL.
  pose proof (capk_pos (k - 1) ltac:(lia)). pose proof (capk_le k ltac:(lia)).
  pose proof (Z.mod_pos_bound (hdr_cfg content) 32768 ltac:(lia)).
  apply t_body_target; [unfold MAX_INPUT; lia | lia].
Qed.
