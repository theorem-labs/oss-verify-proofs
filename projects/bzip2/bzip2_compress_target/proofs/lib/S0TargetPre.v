(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the new auxv for both values of the CONFIG_RSEQ flag, the vDSO and the 6144513-byte init stack window). *)
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
From OSSVerify.bzip2.bzip2_compress_target.images Require Plain.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require S0World RunW ModelAmb.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0WorldVM.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import OSSVerify.bzip2.bzip2_compress_target.images.Plain.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.S0World OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Import ListNotations.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Definition target_vmx (sp0 gm area brkv mas : Z) (VM : VmMaps) : Prop :=
  exists (brk0 mbase : word) (rs : list (word * word)), valid_brk Plain.M.loaded_segments brk0 /\
  ( (mas = 0 /\ area = bv_unsigned brk0 + 4096 /\ brkv = bv_unsigned brk0 + 8192 /\
     exists (maps na : list (word * word)),
       VM = mkVmMapsFull rs
              ((Z_to_bv 64 gm, Z_to_bv 64 69632) :: maps) na brk0 (Z_to_bv 64 (bv_unsigned brk0 + 8192))
              source_alloc_limit mbase (Z_to_bv 64 sp0)
       /\ ((maps = [(brk0, Z_to_bv 64 8192)] /\ (na = [] \/ na = [(brk0, Z_to_bv 64 4096)]))
           \/ (maps = [(Z_to_bv 64 (bv_unsigned brk0 + 4096), Z_to_bv 64 4096)] /\ na = [])))
  \/ (mas = 1 /\ brkv = 2 ^ 64 - 1 /\ exists a : word, area = bv_unsigned a + 4096 /\
       VM = mkVmMapsFull rs
              [(Z_to_bv 64 gm, Z_to_bv 64 69632); (a, Z_to_bv 64 8192)] [(a, Z_to_bv 64 4096)] brk0 brk0
              source_alloc_limit mbase (Z_to_bv 64 sp0))).

Lemma target_vmx_init_sp : forall sp0 gm area brkv mas VM,
  target_vmx sp0 gm area brkv mas VM -> vm_init_sp VM = Z_to_bv 64 sp0.
Proof.
  (intros sp0 gm area brkv mas VM; cps_intros (brk0 & mbase & rs & _ & [(_ & _ & _ & maps & na & -> & _)|(_ & _ & a & _ & ->)])); reflexivity.
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

(* LPS 08b1429: the auxv as [StackLayout.auxv_entries] writes it.  24 fixed-key pairs come first
   (AT_SYSINFO_EHDR 33 .. AT_SECURE 23), then AT_RANDOM (25) and AT_EXECFN (31); the two
   AT_RSEQ_* pairs (27, 28) follow only when the kernel build has CONFIG_RSEQ, then AT_NULL.
   musl's [__init_malloc] walks every key up to AT_NULL, so both layouts are carried: the
   vector ends at [av + 432] (27 pairs) or at [av + 464] (29 pairs). *)
Definition auxv_cells (M : word -> option byte) (av rnd : Z) : Prop :=
    cell M av 8 33 /\ cell M (av + 16) 8 40 /\ cell M (av + 32) 8 41 /\ cell M (av + 48) 8 42 /\
    cell M (av + 64) 8 43 /\ cell M (av + 80) 8 44 /\ cell M (av + 96) 8 45 /\ cell M (av + 112) 8 46 /\
    cell M (av + 128) 8 47 /\ cell M (av + 144) 8 51 /\ cell M (av + 160) 8 16 /\ cell M (av + 176) 8 6 /\
    cell M (av + 192) 8 17 /\ cell M (av + 208) 8 3 /\ cell M (av + 224) 8 4 /\ cell M (av + 240) 8 5 /\
    cell M (av + 256) 8 7 /\ cell M (av + 272) 8 8 /\ cell M (av + 288) 8 9 /\ cell M (av + 304) 8 11 /\
    cell M (av + 320) 8 12 /\ cell M (av + 336) 8 13 /\ cell M (av + 352) 8 14 /\ cell M (av + 368) 8 23 /\
    cell M (av + 384) 8 25 /\ cell M (av + 392) 8 rnd /\ cell M (av + 400) 8 31 /\
    ((cell M (av + 416) 8 27 /\ cell M (av + 432) 8 28 /\ cell M (av + 448) 8 0) \/ cell M (av + 416) 8 0).

Definition auxv0 (sp0 : Z) (M : word -> option byte) : Prop :=
  exists av rnd : Z,
    cell M 0x5a978 8 av /\ auxv_cells M av rnd /\
    cell M (rnd + 8) 8 run_secret /\
    sp0 <= av /\ av + 464 <= 2 ^ 64 /\ sp0 <= rnd + 8 /\ rnd + 16 < 2 ^ 64.

(* the auxv cells move with a memory that agrees on [av .. av + 464) *)
Lemma auxv_cells_agree : forall M M' av rnd,
  auxv_cells M av rnd -> 0 <= av -> av + 464 <= 2 ^ 64 ->
  (forall i, av <= i < av + 464 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  auxv_cells M' av rnd.
Proof.
  intros M M' av rnd H Ha Hb Hag. unfold auxv_cells in *.
  assert (CA : forall k v, 0 <= k -> k + 8 < 464 -> cell M (av + k) 8 v -> cell M' (av + k) 8 v)
    by (intros k v Hk1 Hk2 Hc; eapply cell_agree; [cbn; lia | lia | intros i Hi; cbn in Hi; apply Hag; lia | exact Hc]).
  assert (CA0 : forall v, cell M av 8 v -> cell M' av 8 v)
    by (intros v Hc; rewrite <- (Z.add_0_r av) in Hc |- *; apply CA; [lia | lia | exact Hc]).
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end;
    try (apply CA0; assumption); try (apply CA; [lia | lia | assumption]).
  match goal with H : _ \/ _ |- _ => destruct H as [(T1 & T2 & T3) | T1] end;
    [left; repeat split; apply CA; first [lia | assumption] | right; apply CA; first [lia | assumption]].
Qed.

(* [comment removed for export] *)
Lemma auxv0_agree : forall sp0 M M',
  auxv0 sp0 M ->
  (forall i, sp0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (forall i, 0x5a978 <= i < 0x5a980 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  0 <= sp0 ->
  auxv0 sp0 M'.
Proof.
  (intros sp0 M M'; cps_intros (av & rnd & C0 & AC & SB & B1 & B2 & B3 & B4); intros AB AL SP).
  exists av, rnd.
  split; [eapply cell_agree; [cbn; lia | lia | intros i Hi; cbn in Hi; apply AL; lia | exact C0]|].
  split; [apply (auxv_cells_agree M M' av rnd AC); [lia | lia | intros i Hi; apply AB; lia]|].
  split; [eapply cell_agree; [cbn; lia | lia | intros i Hi; cbn in Hi; apply AB; lia | exact SB]|].
  lia.
Qed.
End AuxV.
End S0WorldVM.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Plain.
From LinuxProcessSemantics.LinuxProcessSem Require Import Fs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import
  PropExec CatExec StoreOk Frame MallocDefs S0EnframeBase S0World ShapeAlg Spec Spec04.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Definition hdr_b0 (content : list byte) : Z := bv_unsigned (nth 0 content (Z_to_bv 8 0)).
Definition hdr_b1 (content : list byte) : Z := bv_unsigned (nth 1 content (Z_to_bv 8 0)).
Definition hdr_cfg (content : list byte) : Z := hdr_b0 content + 256 * hdr_b1 content.
Definition hdr_cfglen (content : list byte) : Z := hdr_cfg content mod 32768.
Definition hdr_paylen (content : list byte) : Z := Z.of_nat (length content) - 6 - hdr_cfglen content.

(* LPS 75d69e00 (#38): the OLD 8 MiB span, kept for reference and used by nothing.  FALSE for
   some launches: init maps only [stack_window_depth] = 6144513 bytes below sp, and
   [store_ok] needs mapped bytes.  See [S0ReadBase.stack_writable]. *)
Definition stack_writableZ_8M (M : word -> option byte) (sp0 : Z) : Prop :=
  forall d m, 0 <= d -> d + Z.of_nat m <= 8388608 ->
    store_ok RSEGS M (Z_to_bv 64 (sp0 - 8388608 + d)) m = true.

(* The writable span #38's init guarantees: [kn_stack]'s 6144513. *)
Definition stack_writableZ (M : word -> option byte) (sp0 : Z) : Prop :=
  forall d m, 0 <= d -> d + Z.of_nat m <= 6144513 ->
    store_ok RSEGS M (Z_to_bv 64 (sp0 - 6144513 + d)) m = true.

(* [comment removed for export] *)
Record target_pre (sp0 gm area brkv mas tid hw : Z) (content : list byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := TARGET_PRE {
  (* [comment removed for export] *)
  tp_ra : getr R 1 = Z_to_bv 64 0x136bc;
  tp_sp : getr R 2 = Z_to_bv 64 (sp0 - 128);
  tp_gp : getr R 3 = Z_to_bv 64 0x10800;
  tp_tp : getr R 4 = Z_to_bv 64 0x3a6e0;
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
  tp_s6 : getr R 22 = Z_to_bv 64 0x2a5d9;                                (* [comment removed for export] *)
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
  (* the reserved ledger at the revision: the segments and the vDSO/vvar pair
     ([ModelAmb.res_ok]) *)
  tv_res   : ModelAmb.res_ok (segments_reserved RSEGS) VM;
  tv_has   : In (Z_to_bv 64 gm, Z_to_bv 64 69632) (vm_maps VM);
  tv_area  : exists lo sz, In (lo, sz) (vm_maps VM)
               /\ bv_unsigned lo <= area /\ area + 4096 <= bv_unsigned lo + bv_unsigned sz;
  tv_len   : (length (vm_maps VM) <= 4)%nat;
  tv_small : Forall (fun p => 0 < bv_unsigned (snd p) <= 69632
                              /\ bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64) (vm_maps VM);
  tv_seps  : seps (vm_maps VM);
  tv_limit : vm_limit VM = source_alloc_limit
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
