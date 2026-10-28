(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Lia. 
From Stdlib Require ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0World RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0WorldVM.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0World OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Import ListNotations.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Definition target_vmx (sp0 gm area brkv mas : Z) (VM : VmMaps) : Prop :=
  exists (brk0 mbase : word), valid_brk Ubsan.M.loaded_segments brk0 /\
  ( (mas = 0 /\ area = bv_unsigned brk0 + 4096 /\ brkv = bv_unsigned brk0 + 8192 /\
     exists (maps na : list (word * word)),
       VM = mkVmMapsFull (segments_reserved Ubsan.M.loaded_segments)
              ((Z_to_bv 64 gm, Z_to_bv 64 69632) :: maps) na brk0 (Z_to_bv 64 (bv_unsigned brk0 + 8192))
              target_alloc_limit mbase (Z_to_bv 64 sp0)
       /\ ((maps = [(brk0, Z_to_bv 64 8192)] /\ (na = [] \/ na = [(brk0, Z_to_bv 64 4096)]))
           \/ (maps = [(Z_to_bv 64 (bv_unsigned brk0 + 4096), Z_to_bv 64 4096)] /\ na = [])))
  \/ (mas = 1 /\ brkv = 2 ^ 64 - 1 /\ exists a : word, area = bv_unsigned a + 4096 /\
       VM = mkVmMapsFull (segments_reserved Ubsan.M.loaded_segments)
              [(Z_to_bv 64 gm, Z_to_bv 64 69632); (a, Z_to_bv 64 8192)] [(a, Z_to_bv 64 4096)] brk0 brk0
              target_alloc_limit mbase (Z_to_bv 64 sp0))).

Lemma target_vmx_init_sp : forall sp0 gm area brkv mas VM,
  target_vmx sp0 gm area brkv mas VM -> vm_init_sp VM = Z_to_bv 64 sp0.
Proof.
  (intros sp0 gm area brkv mas VM; cps_intros (brk0 & mbase & _ & [(_ & _ & _ & maps & na & -> & _)|(_ & _ & a & _ & ->)])); reflexivity.
Qed.

Lemma target_vmx_alloc_top : forall sp0 gm area brkv mas VM,
  0 <= sp0 < 2 ^ 64 -> target_vmx sp0 gm area brkv mas VM -> alloc_top VM = sp0 - 8388608.
Proof.
  intros sp0 gm area brkv mas VM H TX. unfold alloc_top. rewrite (target_vmx_init_sp _ _ _ _ _ _ TX).
  rewrite Z_to_bv_small by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section AuxV.
Context {RUNW__ : RunW}.

Definition auxv0 (sp0 : Z) (M : word -> option byte) : Prop :=
  exists av rnd : Z,
    cell M 0x64478 8 av /\
    cell M av 8 3 /\ cell M (av + 16) 8 4 /\ cell M (av + 32) 8 5 /\ cell M (av + 48) 8 16 /\
    cell M (av + 64) 8 6 /\ cell M (av + 80) 8 11 /\ cell M (av + 96) 8 12 /\ cell M (av + 112) 8 23 /\
    cell M (av + 128) 8 25 /\ cell M (av + 136) 8 rnd /\ cell M (av + 144) 8 0 /\
    cell M (rnd + 8) 8 run_secret /\
    sp0 <= av /\ av + 160 <= 2 ^ 64 /\ sp0 <= rnd + 8 /\ rnd + 16 < 2 ^ 64.

(* [comment removed for export] *)
Lemma auxv0_agree : forall sp0 M M',
  auxv0 sp0 M ->
  (forall i, sp0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (forall i, 0x64478 <= i < 0x64480 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  0 <= sp0 ->
  auxv0 sp0 M'.
Proof.
  (intros sp0 M M'; cps_intros (av & rnd & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & SB & B1 & B2 & B3 & B4); intros AB AL SP).
  exists av, rnd.
  repeat match goal with |- _ /\ _ => split end; try lia;
    try (eapply cell_agree; [ | | | eassumption]; [cbn; lia | lia | intros i Hi; cbn in Hi; first [apply AB; lia | apply AL; lia]]).
Qed.
End AuxV.
End S0WorldVM.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import Fs.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import
  PropExec CatExec StoreOk Frame MallocDefs U.S0EnframeBase U.S0World ShapeAlg Spec Spec04.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition hdr_b0 (content : list byte) : Z := bv_unsigned (nth 0 content (Z_to_bv 8 0)).
Definition hdr_b1 (content : list byte) : Z := bv_unsigned (nth 1 content (Z_to_bv 8 0)).
Definition hdr_cfg (content : list byte) : Z := hdr_b0 content + 256 * hdr_b1 content.
Definition hdr_cfglen (content : list byte) : Z := hdr_cfg content mod 32768.
Definition hdr_paylen (content : list byte) : Z := Z.of_nat (length content) - 6 - hdr_cfglen content.

(* [comment removed for export] *)
Definition stack_writableZ (M : word -> option byte) (sp0 : Z) : Prop :=
  forall d m, 0 <= d -> d + Z.of_nat m <= 8388608 ->
    store_ok RSEGS M (Z_to_bv 64 (sp0 - 8388608 + d)) m = true.

(* [comment removed for export] *)
Record target_pre (sp0 gm area brkv mas tid hw : Z) (content : list byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := TARGET_PRE {
  (* [comment removed for export] *)
  tp_ra : getr R 1 = Z_to_bv 64 0x136f4;
  tp_sp : getr R 2 = Z_to_bv 64 (sp0 - 128);
  tp_gp : getr R 3 = Z_to_bv 64 0x10800;
  tp_tp : getr R 4 = Z_to_bv 64 0x441e0;
  tp_a0 : getr R 10 = Z_to_bv 64 (gm + 34);                              (* [comment removed for export] *)
  tp_a1 : getr R 11 = Z_to_bv 64 (hdr_cfglen content);                   (* [comment removed for export] *)
  tp_a2 : getr R 12 = Z_to_bv 64 (gm + 38 + hdr_cfglen content);         (* [comment removed for export] *)
  tp_a3 : getr R 13 = Z_to_bv 64 (hdr_paylen content);                   (* [comment removed for export] *)
  tp_s0 : getr R 8 = Z_to_bv 64 (gm + 34);
  tp_s1 : getr R 9 = Z_to_bv 64 (gm + 32);                               (* [comment removed for export] *)
  tp_s2 : getr R 18 = Z_to_bv 64 (hdr_cfglen content);
  tp_s3 : getr R 19 = Z_to_bv 64 (gm + 38 + hdr_cfglen content);
  tp_s4 : getr R 20 = Z_to_bv 64 (hdr_paylen content);
  tp_s5 : getr R 21 = Z_to_bv 64 (if hdr_b1 content <? 128 then hdr_b1 content else hdr_b1 content - 256 + 2 ^ 64);
            (* [comment removed for export] *)
  tp_s6 : getr R 22 = Z_to_bv 64 0x340d9;                                (* [comment removed for export] *)
  tp_s7 : getr R 23 = Z_to_bv 64 0;
  (* [comment removed for export] *)
  tp_sp0 : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0;
  tp_ceil : alloc_ceiling = sp0 - 8388608;     (* [comment removed for export] *)
  tp_len : 6 + hdr_cfglen content <= Z.of_nat (length content) < 65536;
  (* [comment removed for export] *)
  tp_stack : stack_writableZ M sp0;
  tp_frame : main_frame sp0 M;
  tp_world : world0 area gm brkv mas tid hw M;
  tp_content : rdn RSEGS M (Z_to_bv 64 (gm + 32)) (length content) = Some content
}.

(* [comment removed for export] *)
Definition iv_disjoint (p q : word * word) : Prop :=
  bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q)
  \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p).

Inductive seps : list (word * word) -> Prop :=
| seps_nil : seps []
| seps_cons : forall p l, Forall (iv_disjoint p) l -> seps l -> seps (p :: l).

(* [comment removed for export] *)
Record target_vm (gm area : Z) (VM : VmMaps) : Prop := TARGET_VM {
  tv_res   : vm_reserved VM = segments_reserved RSEGS;
  tv_has   : In (Z_to_bv 64 gm, Z_to_bv 64 69632) (vm_maps VM);
  tv_area  : exists lo sz, In (lo, sz) (vm_maps VM)
               /\ bv_unsigned lo <= area /\ area + 4096 <= bv_unsigned lo + bv_unsigned sz;
  tv_len   : (length (vm_maps VM) <= 4)%nat;
  tv_small : Forall (fun p => 0 < bv_unsigned (snd p) <= 69632
                              /\ bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64) (vm_maps VM);
  tv_seps  : seps (vm_maps VM);
  tv_limit : vm_limit VM = target_alloc_limit
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition t_target (content : list byte) (fs : Fs.Fs) : TSet :=
  let b2 := bv_unsigned (nth 2 content (Z_to_bv 8 0)) in
  let cfg := hdr_cfg content in
  let config_len := Z.to_nat (cfg mod 32768) in
  let calls := match config_len with O => 1%nat | _ => S (Z.to_nat (b2 mod 4)) end in
  t_emit (W 1 (zero_lines calls)) (t_exit (exit_code 0) fs).

Lemma t_body_target : forall content fs,
  (Z.of_nat (length content) < MAX_INPUT) ->
  (6 + Z.to_nat (hdr_cfg content mod 32768) <= length content)%nat ->
  t_body04 content fs = t_target content fs.
Proof.
  intros content fs Hmax Hlen. unfold t_body04, t_target, hdr_cfg, hdr_b0, hdr_b1 in *.
  destruct (MAX_INPUT <=? Z.of_nat (length content)) eqn:E1; [apply Z.leb_le in E1; lia|].
  destruct (length content <? 6)%nat eqn:E2; [apply Nat.ltb_lt in E2; lia|].
  destruct (length content <? 6 + Z.to_nat ((bv_unsigned (nth 0 content (Z_to_bv 8 0)) +
             256 * bv_unsigned (nth 1 content (Z_to_bv 8 0))) mod 32768))%nat eqn:E3;
    [apply Nat.ltb_lt in E3; lia|].
  reflexivity.
Qed.

End ACeilS1.
