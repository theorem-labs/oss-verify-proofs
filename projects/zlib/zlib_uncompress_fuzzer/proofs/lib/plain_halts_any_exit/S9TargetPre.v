(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_zlib_uncompress_fuzzer_repro.
From LinuxProcessSemantics.LinuxProcessSem Require Import Fs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import
  PropExec CatExec StoreOk Frame MallocDefs S9EnframeBase S9World ShapeAlg Spec.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import S9ReadBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

Abbreviation RSEGS := Src_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments.

Definition hdr_b0 (content : list byte) : Z := bv_unsigned (nth 0 content (Z_to_bv 8 0)).
Definition hdr_b1 (content : list byte) : Z := bv_unsigned (nth 1 content (Z_to_bv 8 0)).
Definition hdr_cfg (content : list byte) : Z := hdr_b0 content + 256 * hdr_b1 content.
Definition hdr_cfglen (content : list byte) : Z := hdr_cfg content mod 32768.
Definition hdr_paylen (content : list byte) : Z := Z.of_nat (length content) - 6 - hdr_cfglen content.

Definition stack_writableZ {RCa1 : RunCtx}  (M : word -> option byte) (sp0 : Z) : Prop :=
  forall d m, 0 <= d -> d + Z.of_nat m <= 6144513 ->
    store_ok (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (sp0 - 6144513 + d)) m = true.

Record target_pre {RCa1 : RunCtx}  (sp0 gm area brkv mas tid can sec : Z) (content : list byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := TARGET_PRE {
  tp_ra : getr R 1 = Z_to_bv 64 0x14a40;
  tp_sp : getr R 2 = Z_to_bv 64 (sp0 - 128);
  tp_gp : getr R 3 = Z_to_bv 64 0x10800;
  tp_tp : getr R 4 = Z_to_bv 64 0x72f60;
  tp_a0 : getr R 10 = Z_to_bv 64 (gm + 34);
  tp_a1 : getr R 11 = Z_to_bv 64 (hdr_cfglen content);
  tp_a2 : getr R 12 = Z_to_bv 64 (gm + 38 + hdr_cfglen content);
  tp_a3 : getr R 13 = Z_to_bv 64 (hdr_paylen content);
  tp_s0 : getr R 8 = Z_to_bv 64 (gm + 34);
  tp_s1 : getr R 9 = Z_to_bv 64 (gm + 32);
  tp_s2 : getr R 18 = Z_to_bv 64 (hdr_cfglen content);
  tp_s3 : getr R 19 = Z_to_bv 64 (gm + 38 + hdr_cfglen content);
  tp_s4 : getr R 20 = Z_to_bv 64 (hdr_paylen content);
  tp_s5 : getr R 21 = Z_to_bv 64 (if hdr_b1 content <? 128 then hdr_b1 content else hdr_b1 content - 256 + 2 ^ 64);
  tp_s6 : getr R 22 = Z_to_bv 64 0x22e59;
  tp_sp0 : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0;
  tp_len : 6 + hdr_cfglen content <= Z.of_nat (length content) < 65536;
  tp_stack : stack_writableZ M sp0;
  tp_frame : main_frame sp0 M;
  tp_world : world0 sp0 area gm brkv mas tid can sec M;
  tp_content : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (gm + 32)) (length content) = Some content
}.
Arguments TARGET_PRE {RCa1}.

Abbreviation iv_disjoint := S9ReadBase.iv_disjoint.
Abbreviation seps := S9ReadBase.seps.
Abbreviation seps_nil := S9ReadBase.seps_nil.
Abbreviation seps_cons := S9ReadBase.seps_cons.

Record target_vm (sp0 gm area : Z) (VM : VmMaps) : Prop := TARGET_VM {
  tv_res   : vm_reserved VM = segments_reserved RSEGS;
  tv_isp   : vm_init_sp VM = Z_to_bv 64 sp0;
  tv_has   : In (Z_to_bv 64 gm, Z_to_bv 64 69632) (vm_maps VM);
  tv_area  : exists lo sz, In (lo, sz) (vm_maps VM)
               /\ bv_unsigned lo <= area /\ area + 4096 <= bv_unsigned lo + bv_unsigned sz;
  tv_len   : (length (vm_maps VM) <= 4)%nat;
  tv_small : Forall (fun p => 0 < bv_unsigned (snd p) <= 69632
                              /\ bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64) (vm_maps VM);
  tv_seps  : seps (vm_maps VM);
  tv_limit : vm_limit VM = source_alloc_limit
}.

Definition t_target (content : list byte) (fs : Fs.Fs) : TSet :=
  let b2 := bv_unsigned (nth 2 content (Z_to_bv 8 0)) in
  let cfg := hdr_cfg content in
  let config_len := Z.to_nat (cfg mod 32768) in
  let counting := (32768 <=? cfg) in
  let payload_len := (length content - 6 - config_len)%nat in
  let calls := match config_len with O => 1%nat | _ => S (Z.to_nat (b2 mod 4)) end in
  let succ := t_emit (W 1 (zero_lines calls)) (t_exit (exit_code 0) fs) in
  match payload_len with
  | O => succ
  | _ => t_alt2 (t_exit (exit_code (if counting then 0 else 2)) fs) succ
  end.

Lemma t_body_target : forall content fs,
  (Z.of_nat (length content) < MAX_INPUT) ->
  (6 + Z.to_nat (hdr_cfg content mod 32768) <= length content)%nat ->
  t_body content fs = t_target content fs.
Proof.
  intros content fs Hmax Hlen. unfold t_body, t_target, hdr_cfg, hdr_b0, hdr_b1 in *.
  destruct (MAX_INPUT <=? Z.of_nat (length content)) eqn:E1; [apply Z.leb_le in E1; lia|].
  destruct (length content <? 6)%nat eqn:E2; [apply Nat.ltb_lt in E2; lia|].
  destruct (length content <? 6 + Z.to_nat ((bv_unsigned (nth 0 content (Z_to_bv 8 0)) +
             256 * bv_unsigned (nth 1 content (Z_to_bv 8 0))) mod 32768))%nat eqn:E3;
    [apply Nat.ltb_lt in E3; lia|].
  reflexivity.
Qed.
