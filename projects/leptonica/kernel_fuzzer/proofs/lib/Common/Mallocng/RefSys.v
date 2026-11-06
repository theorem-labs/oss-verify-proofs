(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil AgentLib RefNodes RefNodesMF.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocTree MallocOps MallocShape RefStep RefStmts.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section Sys.
Context {fx : FPState} {ML : MallocLayout}.

Lemma pru_u : forall (len : word),
  page_round_up_Z (bv_unsigned len) < 2^64 ->
  bv_unsigned (page_round_up len) = page_round_up_Z (bv_unsigned len).
Proof.
  intros len H. unfold page_round_up. apply Z_to_bv_small_unsigned.
  pose proof (u64_range len) as Hr.
  pose proof (page_round_up_Z_bounds (bv_unsigned len) (proj1 Hr)). lia.
Qed.

Lemma alloc_top_lt64 : forall h, alloc_top h + stack_max_size < 2^64.
Proof. intros h. pose proof (alloc_top_room h). unfold two_pow_64 in H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_sys_munmap_at : forall md (R : bvmap 5 word) (pc : word) w mm rom (s : mstate) (addr len : word)
    (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> fetch_word ml_segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr R 17) = 215 -> getr R 10 = addr -> getr R 11 = len ->
  alloc_top (ms_vm s) <= TASK_SIZE ->
  tsafe (sys_munmap addr len s) P ->
  (let n := page_round_up len in
   let s' := upd s (unfill addr n (ms_mem s)) (vm_munmap addr n (ms_vm s)) in
   tsafe (MallocTree.mret (Z_to_bv 64 0) s') P ->
   bv_unsigned addr + bv_unsigned n <= alloc_top (ms_vm s) -> bv_unsigned n = page_round_up_Z (bv_unsigned len) ->
   realizes ml_segs (mkCfg (mkst (regupd R 10 (Z_to_bv 64 0)) (v_addi pc 4) (unfill addr n mm) rom)
                         (with_vmmaps (ms_vm s') md)) (tshape (MallocTree.mret (Z_to_bv 64 0) s') L)) ->
  realizes ml_segs (mkCfg (mkst R pc mm rom) (with_vmmaps (ms_vm s) md)) (tshape (sys_munmap addr len s) L).
Proof.
  intros md R pc w mm rom s addr len P L Hp HF HE H17 H10 H11 Hct HS HK.
  unfold sys_munmap in HS |- *.
  destruct (bv_unsigned addr mod page_size =? 0) eqn:E1; [|cbn in HS; contradiction].
  destruct (0 <? bv_unsigned len) eqn:E2; [|cbn in HS; contradiction].
  destruct (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <=? alloc_top (ms_vm s)) eqn:E3; [|cbn in HS; contradiction].
  destruct (map_has (vm_maps (ms_vm s)) addr (page_round_up len)) eqn:E4; [|cbn in HS; contradiction].
  cbn [andb tsafe tshape] in HS |- *.
  apply Z.eqb_eq in E1. apply Z.ltb_lt in E2. apply Z.leb_le in E3.
  pose proof (u64_range addr) as Har. unfold TASK_SIZE in Hct.
  pose proof (alloc_top_lt64 (ms_vm s)) as Htop. unfold stack_max_size in Htop.
  assert (Hn : bv_unsigned (page_round_up len) = page_round_up_Z (bv_unsigned len)) by (apply pru_u; alia).
  eapply (rz_munmap_at ml_segs R pc mm rom (with_vmmaps (ms_vm s) md) w addr len);
    [ apply md_pure_vmmaps; exact Hp | exact HF | exact HE | exact H17 | exact H10 | exact H11
    | exact E1 | exact E2 | unfold TASK_SIZE; alia | rewrite with_vmmaps_vmmaps; exact E4 | ].
  rewrite with_vmmaps_vmmaps, with_vmmaps_twice. apply HK; [exact HS | rewrite Hn; exact E3 | exact Hn].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_sys_mmap_at : forall k md (R : bvmap 5 word) (pc : word) w mm rom (s : mstate) (len : word)
    (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> fetch_word ml_segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr R 17) = 222 -> getr R 11 = len ->
  bv_unsigned (getr R 12) = mmap_prot k -> bv_unsigned (getr R 13) = 34 ->
  bv_unsigned (getr R 14) = 2^64 - 1 -> bv_unsigned (getr R 15) = 0 ->
  tsafe (sys_mmap k len s) P ->
  (* [comment removed for export] *)
  (tsafe (MallocTree.mbind (set_errno ENOMEM) (fun _ => MallocTree.mret MAP_FAILED) s) P ->
   0 < bv_unsigned len < 2^62 ->
   realizes ml_segs (mkCfg (mkst (regupd R 10 (errno_ret ENOMEM)) (v_addi pc 4) mm rom) (with_vmmaps (ms_vm s) md))
            (tshape (MallocTree.mbind (set_errno ENOMEM) (fun _ => MallocTree.mret MAP_FAILED) s) L)) ->
  (* [comment removed for export] *)
  (forall a : word,
   let n := page_round_up len in
   let mm' := match k with MMrw => zfill a n mm | MMnone => unfill a n mm end in
   let s' := match k with
             | MMrw => upd s (zfill a n (ms_mem s)) (vm_mmap a n (ms_vm s))
             | MMnone => upd s (unfill a n (ms_mem s)) (vm_noacc a n (ms_vm s))
             end in
   tsafe (MallocTree.mret a s') P ->
   bv_unsigned a mod 4096 = 0 -> 0 < bv_unsigned a ->
   bv_unsigned a + bv_unsigned n <= alloc_top (ms_vm s) ->
   bv_unsigned n = page_round_up_Z (bv_unsigned len) -> 0 < bv_unsigned len < 2^62 ->
   realizes ml_segs (mkCfg (mkst (regupd R 10 a) (v_addi pc 4) mm' rom) (with_vmmaps (ms_vm s') md))
            (tshape (MallocTree.mret a s') L)) ->
  realizes ml_segs (mkCfg (mkst R pc mm rom) (with_vmmaps (ms_vm s) md)) (tshape (sys_mmap k len s) L).
Proof.
  intros k md R pc w mm rom s len P L Hp HF HE H17 H11 H12 H13 H14 H15 HS HKf HKo.
  unfold sys_mmap in HS |- *.
  destruct (0 <? bv_unsigned len) eqn:E1; [|cbn in HS; contradiction].
  destruct (bv_unsigned len <? 2^62) eqn:E2; [|cbn in HS; contradiction].
  apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
  cbn [andb tsafe tshape] in HS |- *. destruct HS as [HSf HSo].
  pose proof (alloc_top_lt64 (ms_vm s)) as Htop. unfold stack_max_size in Htop.
  pose proof (md_pure_vmmaps (ms_vm s) md Hp) as Hp'.
  destruct k; cbn [mmap_grant_ok mmap_prot mmap_refusable_k] in *.
  - apply (rz_mmap_ix_at ml_segs R pc mm rom (with_vmmaps (ms_vm s) md) w len _ _ Hp' HF HE H17 H11 E1 H12 H13 H14 H15).
    + intros Hr (* [comment removed for export] *). apply HKf; [exact (HSf Hr) | alia].
    + intros a Ha. rewrite with_vmmaps_vmmaps in Ha. rewrite with_vmmaps_vmmaps, with_vmmaps_twice.
      pose proof (grant_ok_vm_unpack _ _ _ Ha) as (Hal & Ha0 & Hceil & _ & _).
      pose proof (u64_range a) as Har.
      assert (Hn : bv_unsigned (page_round_up len) = page_round_up_Z (bv_unsigned len)) by (apply pru_u; alia).
      apply (HKo a); [apply HSo; exact Ha | exact Hal | exact Ha0 | rewrite Hn; exact Hceil | exact Hn | alia].
  - apply (rz_mmap_noaccess_ix_at ml_segs R pc mm rom (with_vmmaps (ms_vm s) md) w len _ _ Hp' HF HE H17 H11 E1 H12 H13 H14 H15).
    + intros Hr. apply HKf; [exact (HSf Hr) | alia].
    + intros a Ha. rewrite with_vmmaps_vmmaps in Ha. rewrite with_vmmaps_vmmaps, with_vmmaps_twice.
      pose proof (grant_ok_na_vm_unpack _ _ _ Ha) as (Hal & Ha0 & Hceil & _).
      pose proof (u64_range a) as Har.
      assert (Hn : bv_unsigned (page_round_up len) = page_round_up_Z (bv_unsigned len)) by (apply pru_u; alia).
      apply (HKo a); [apply HSo; exact Ha | exact Hal | exact Ha0 | rewrite Hn; exact Hceil | exact Hn | alia].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_sys_brk_query_at : forall md (R : bvmap 5 word) (pc : word) w mm rom (s : mstate)
    (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> fetch_word ml_segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr R 17) = 214 -> bv_unsigned (getr R 10) = 0 ->
  tsafe (sys_brk_query s) P ->
  (tsafe (MallocTree.mret (vm_brk (ms_vm s)) s) P ->
   realizes ml_segs (mkCfg (mkst (regupd R 10 (vm_brk (ms_vm s))) (v_addi pc 4) mm rom) (with_vmmaps (ms_vm s) md))
            (tshape (MallocTree.mret (vm_brk (ms_vm s)) s) L)) ->
  realizes ml_segs (mkCfg (mkst R pc mm rom) (with_vmmaps (ms_vm s) md)) (tshape (sys_brk_query s) L).
Proof.
  intros md R pc w mm rom s P L Hp HF HE H17 H10 HS HK.
  unfold sys_brk_query in HS |- *. cbn [tsafe tshape] in HS |- *.
  eapply (rz_brk_query_at ml_segs R pc mm rom (with_vmmaps (ms_vm s) md) w);
    [apply md_pure_vmmaps; exact Hp | exact HF | exact HE | exact H17 | exact H10 |].
  rewrite with_vmmaps_vmmaps. apply HK. exact HS.
Qed.

Lemma rz_sys_brk_grow_at : forall md (R : bvmap 5 word) (pc : word) w mm rom (s : mstate) (req : word)
    (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> fetch_word ml_segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr R 17) = 214 -> getr R 10 = req ->
  tsafe (sys_brk_grow req s) P ->
  (* [comment removed for export] *)
  (tsafe (MallocTree.mret (vm_brk (ms_vm s)) s) P ->
   0 < bv_unsigned (vm_brk (ms_vm s)) < bv_unsigned req ->
   realizes ml_segs (mkCfg (mkst (regupd R 10 (vm_brk (ms_vm s))) (v_addi pc 4) mm rom) (with_vmmaps (ms_vm s) md))
            (tshape (MallocTree.mret (vm_brk (ms_vm s)) s) L)) ->
  (* [comment removed for export] *)
  (let s' := upd s (apply_zeros (ms_mem s) (brk_zeros req req (vm_brk (ms_vm s)))) (vm_brk_grow req (ms_vm s)) in
   tsafe (MallocTree.mret req s') P ->
   brk_grow_ok_vm (ms_vm s) req req = true ->
   0 < bv_unsigned (vm_brk (ms_vm s)) < bv_unsigned req ->
   realizes ml_segs (mkCfg (mkst (regupd R 10 req) (v_addi pc 4)
                          (apply_zeros mm (brk_zeros req req (vm_brk (ms_vm s)))) rom) (with_vmmaps (ms_vm s') md))
            (tshape (MallocTree.mret req s') L)) ->
  realizes ml_segs (mkCfg (mkst R pc mm rom) (with_vmmaps (ms_vm s) md)) (tshape (sys_brk_grow req s) L).
Proof.
  intros md R pc w mm rom s req P L Hp HF HE H17 H10 HS HKf HKo.
  unfold sys_brk_grow in HS |- *.
  destruct (0 <? bv_unsigned (vm_brk (ms_vm s))) eqn:E1; [|cbn in HS; contradiction].
  destruct (bv_unsigned (vm_start_brk (ms_vm s)) <=? bv_unsigned req) eqn:E2; [|cbn in HS; contradiction].
  destruct (bv_unsigned (vm_brk (ms_vm s)) <? bv_unsigned req) eqn:E3; [|cbn in HS; contradiction].
  apply Z.ltb_lt in E1. apply Z.leb_le in E2. apply Z.ltb_lt in E3.
  cbn [andb tsafe tshape] in HS |- *. destruct HS as [HSf HSo].
  pose proof (md_pure_vmmaps (ms_vm s) md Hp) as Hp'.
  pose proof (rz_brk_grow_at ml_segs R pc mm rom (with_vmmaps (ms_vm s) md) w req
                (L (vm_brk (ms_vm s)) s)
                (L req (upd s (apply_zeros (ms_mem s) (brk_zeros req req (vm_brk (ms_vm s)))) (vm_brk_grow req (ms_vm s))))
                Hp' HF HE H17 H10) as RZ.
  cbv zeta in RZ. rewrite !with_vmmaps_vmmaps, !with_vmmaps_twice in RZ.
  apply RZ; [exact E1 | exact E2 | exact E3 | intros Hg; apply HKf; [exact (HSf Hg) | alia] |].
  intros Hg. apply HKo; [apply HSo; exact Hg | exact Hg | alia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pruZ_idem : forall z, 0 <= z -> page_round_up_Z (page_round_up_Z z) = page_round_up_Z z.
Proof.
  intros z Hz. apply page_round_up_Z_aligned.
  - pose proof (page_round_up_Z_bounds z Hz). lia.
  - apply page_round_up_Z_aligned'.
Qed.

Lemma rz_sys_mprotect_at : forall md (R : bvmap 5 word) (pc : word) w mm rom (s : mstate) (addr len a0v n1 : word)
    (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> fetch_word ml_segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr R 17) = 226 ->
  getr R 10 = a0v -> a0v = addr ->
  getr R 11 = n1 -> bv_unsigned n1 = page_round_up_Z (bv_unsigned len) ->
  bv_unsigned (getr R 12) = 3 ->
  tsafe (sys_mprotect_rw addr len s) P ->
  let n := page_round_up len in
  (* [comment removed for export] *)
  (tsafe (MallocTree.mbind (set_errno ENOMEM) (fun _ => MallocTree.mret MAP_FAILED) s) P ->
   bv_unsigned addr + bv_unsigned n <= alloc_top (ms_vm s) -> bv_unsigned n = page_round_up_Z (bv_unsigned len) ->
   realizes ml_segs (mkCfg (mkst (regupd R 10 (errno_ret ENOMEM)) (v_addi pc 4) mm rom) (with_vmmaps (ms_vm s) md))
            (tshape (MallocTree.mbind (set_errno ENOMEM) (fun _ => MallocTree.mret MAP_FAILED) s) L)) ->
  (* [comment removed for export] *)
  (let s' := upd s (zfill addr n (ms_mem s)) (vm_unprotect addr n (ms_vm s)) in
   tsafe (MallocTree.mret (Z_to_bv 64 0) s') P ->
   bv_unsigned addr + bv_unsigned n <= alloc_top (ms_vm s) -> bv_unsigned n = page_round_up_Z (bv_unsigned len) ->
   realizes ml_segs (mkCfg (mkst (regupd R 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill addr n mm) rom) (with_vmmaps (ms_vm s') md))
            (tshape (MallocTree.mret (Z_to_bv 64 0) s') L)) ->
  (* [comment removed for export] *)
  (tsafe (MallocTree.mret (Z_to_bv 64 0) s) P ->
   bv_unsigned addr + bv_unsigned n <= alloc_top (ms_vm s) -> bv_unsigned n = page_round_up_Z (bv_unsigned len) ->
   realizes ml_segs (mkCfg (mkst (regupd R 10 (Z_to_bv 64 0)) (v_addi pc 4) mm rom) (with_vmmaps (ms_vm s) md))
            (tshape (MallocTree.mret (Z_to_bv 64 0) s) L)) ->
  realizes ml_segs (mkCfg (mkst R pc mm rom) (with_vmmaps (ms_vm s) md)) (tshape (sys_mprotect_rw addr len s) L).
Proof.
  intros md R pc w mm rom s addr len a0v n1 P L Hp HF HE H17 H10 Ha0 H11 Hn1 H12 HS n HKf HKo HKrw. subst n.
  rewrite Ha0 in H10.
  unfold sys_mprotect_rw in HS |- *.
  destruct (0 <? bv_unsigned len) eqn:E1; [|cbn in HS; contradiction].
  destruct (bv_unsigned addr mod page_size =? 0) eqn:E2; [|cbn in HS; contradiction].
  destruct (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <=? alloc_top (ms_vm s)) eqn:E3; [|cbn in HS; contradiction].
  destruct (map_contains (vm_maps (ms_vm s)) addr (page_round_up len)) eqn:E4; [|cbn in HS; contradiction].
  apply Z.ltb_lt in E1. apply Z.eqb_eq in E2. apply Z.leb_le in E3.
  cbn [andb] in HS |- *.
  pose proof (u64_range addr) as Har. pose proof E3 as E3'.
  pose proof (alloc_top_lt64 (ms_vm s)) as Htop. unfold stack_max_size in Htop.
  assert (Hn : bv_unsigned (page_round_up len) = page_round_up_Z (bv_unsigned len)) by (apply pru_u; alia).
  pose proof (u64_range len) as Hlr. pose proof (page_round_up_Z_bounds (bv_unsigned len) (proj1 Hlr)) as Hpb.
  assert (E1' : 0 < bv_unsigned n1) by (rewrite Hn1; lia).
  assert (Hpn : page_round_up n1 = page_round_up len).
  { unfold page_round_up. rewrite Hn1, pruZ_idem by lia. reflexivity. }
  assert (Hnw : bv_unsigned addr + page_round_up_Z (bv_unsigned n1) < 2^64) by (rewrite Hn1, pruZ_idem by lia; alia).
  pose proof (md_pure_vmmaps (ms_vm s) md Hp) as Hp'.
  destruct (map_contains (vm_noaccess (ms_vm s)) addr (page_round_up len)) eqn:E5.
  - cbn [tsafe tshape] in HS |- *. destruct HS as [HSf HSo].
    pose proof (rz_mprotect_unprotect_at ml_segs R pc mm rom (with_vmmaps (ms_vm s) md) w addr n1
                  (tshape (MallocTree.mbind (set_errno ENOMEM) (fun _ => MallocTree.mret MAP_FAILED) s) L)
                  (L (Z_to_bv 64 0) (upd s (zfill addr (page_round_up len) (ms_mem s)) (vm_unprotect addr (page_round_up len) (ms_vm s))))
                  Hp' HF HE H17 H10 H11 E1' H12 E2 Hnw) as RZ.
    cbv zeta in RZ. rewrite !with_vmmaps_vmmaps, !with_vmmaps_twice, !Hpn in RZ.
    apply RZ; [exact E5 | exact E4 | intros Hb; apply HKf; [exact (HSf Hb) | rewrite Hn; exact E3' | exact Hn] |].
    intros Hb. apply HKo; [apply HSo; exact Hb | rewrite Hn; exact E3' | exact Hn].
  - destruct (region_free (vm_noaccess (ms_vm s)) addr (page_round_up len)) eqn:E6; [|cbn in HS; contradiction].
    cbn [tsafe tshape] in HS |- *.
    pose proof (rz_mprotect_already_rw_at ml_segs R pc mm rom (with_vmmaps (ms_vm s) md) w addr n1
                  (L (Z_to_bv 64 0) s) Hp' HF HE H17 H10 H11 E1' H12 E2 Hnw) as RZ.
    cbv zeta in RZ. rewrite !with_vmmaps_vmmaps, !Hpn in RZ.
    apply RZ; [exact E5 | exact E4 | exact E6 |].
    apply HKrw; [exact HS | rewrite Hn; exact E3' | exact Hn].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_sys_mmap_fixed_at : forall md (R : bvmap 5 word) (pc : word) w mm rom (s : mstate) (addr len : word)
    (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> fetch_word ml_segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr R 17) = 222 -> getr R 10 = addr -> getr R 11 = len ->
  bv_unsigned (getr R 12) = 0 -> bv_unsigned (getr R 13) = 50 ->
  bv_unsigned (getr R 14) = 2^64 - 1 -> bv_unsigned (getr R 15) = 0 ->
  tsafe (sys_mmap_fixed_none addr len s) P ->
  let n := page_round_up len in
  (* [comment removed for export] *)
  (tsafe (MallocTree.mbind (set_errno ENOMEM) (fun _ => MallocTree.mret MAP_FAILED) s) P ->
   bv_unsigned addr + bv_unsigned n <= alloc_top (ms_vm s) -> bv_unsigned n = page_round_up_Z (bv_unsigned len) ->
   0 < bv_unsigned len < 2^62 ->
   realizes ml_segs (mkCfg (mkst (regupd R 10 (errno_ret ENOMEM)) (v_addi pc 4) mm rom) (with_vmmaps (ms_vm s) md))
            (tshape (MallocTree.mbind (set_errno ENOMEM) (fun _ => MallocTree.mret MAP_FAILED) s) L)) ->
  (* [comment removed for export] *)
  (let s' := upd s (unfill addr n (ms_mem s)) (vm_fixed_ok addr n (ms_vm s)) in
   tsafe (MallocTree.mret addr s') P ->
   bv_unsigned addr + bv_unsigned n <= alloc_top (ms_vm s) -> bv_unsigned n = page_round_up_Z (bv_unsigned len) ->
   0 < bv_unsigned len < 2^62 ->
   realizes ml_segs (mkCfg (mkst (regupd R 10 addr) (v_addi pc 4) (unfill addr n mm) rom) (with_vmmaps (ms_vm s') md))
            (tshape (MallocTree.mret addr s') L)) ->
  (* [comment removed for export] *)
  (let s1 := upd s (unfill addr n (ms_mem s)) (vm_fixed_destroy addr n (ms_vm s)) in
   tsafe (MallocTree.mbind (set_errno ENOMEM) (fun _ => MallocTree.mret MAP_FAILED) s1) P ->
   bv_unsigned addr + bv_unsigned n <= alloc_top (ms_vm s) -> bv_unsigned n = page_round_up_Z (bv_unsigned len) ->
   0 < bv_unsigned len < 2^62 ->
   realizes ml_segs (mkCfg (mkst (regupd R 10 (errno_ret ENOMEM)) (v_addi pc 4) (unfill addr n mm) rom) (with_vmmaps (ms_vm s1) md))
            (tshape (MallocTree.mbind (set_errno ENOMEM) (fun _ => MallocTree.mret MAP_FAILED) s1) L)) ->
  realizes ml_segs (mkCfg (mkst R pc mm rom) (with_vmmaps (ms_vm s) md)) (tshape (sys_mmap_fixed_none addr len s) L).
Proof.
  intros md R pc w mm rom s addr len P L Hp HF HE H17 H10 H11 H12 H13 H14 H15 HS n HKa HKb HKc. subst n.
  unfold sys_mmap_fixed_none in HS |- *.
  destruct (0 <? bv_unsigned len) eqn:E1; [|cbn in HS; contradiction].
  destruct (bv_unsigned len <? 2^62) eqn:E2; [|cbn in HS; contradiction].
  destruct (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <=? alloc_top (ms_vm s)) eqn:E3; [|cbn in HS; contradiction].
  destruct (bv_unsigned addr mod page_size =? 0) eqn:E4; [|cbn in HS; contradiction].
  destruct (0 <? bv_unsigned addr) eqn:E0; [|cbn in HS; contradiction].
  destruct (region_free (vm_reserved (ms_vm s)) addr (page_round_up len)) eqn:E5; [|cbn in HS; contradiction].
  destruct (map_contains (vm_maps (ms_vm s)) addr (page_round_up len)) eqn:E6; [|cbn in HS; contradiction].
  apply Z.ltb_lt in E1. apply Z.ltb_lt in E2. apply Z.leb_le in E3. apply Z.eqb_eq in E4. apply Z.ltb_lt in E0.
  cbn [andb tsafe tshape] in HS |- *.
  (* [comment removed for export] *)
  pose proof (u64_range addr) as Har. pose proof E3 as E3'.
  pose proof (alloc_top_lt64 (ms_vm s)) as Htop. unfold stack_max_size in Htop.
  assert (Hn : bv_unsigned (page_round_up len) = page_round_up_Z (bv_unsigned len)) by (apply pru_u; alia).
  pose proof (md_pure_vmmaps (ms_vm s) md Hp) as Hp'.
  pose proof (rz_mmap_fixed_noaccess_at ml_segs R pc mm rom (with_vmmaps (ms_vm s) md) w addr len
                (L addr (upd s (unfill addr (page_round_up len) (ms_mem s)) (vm_fixed_ok addr (page_round_up len) (ms_vm s))))
                Hp' HF HE H17 H10 H11 E1 H12 H13 H14 H15) as RZ.
  cbv zeta in RZ. rewrite !with_vmmaps_vmmaps, !with_vmmaps_twice in RZ.
  apply RZ; [exact E4 | exact E0 | exact E3 | exact E5 | exact E6 |].
  apply HKb; [exact HS | rewrite Hn; exact E3' | exact Hn | alia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tsafe_sys_mmap_len : forall k len s P, tsafe (sys_mmap k len s) P -> 0 < bv_unsigned len < 2^62.
Proof.
  intros k len s P HS. unfold sys_mmap in HS.
  destruct (0 <? bv_unsigned len) eqn:E1; [|cbn in HS; contradiction].
  destruct (bv_unsigned len <? 2^62) eqn:E2; [|cbn in HS; contradiction].
  apply Z.ltb_lt in E1. apply Z.ltb_lt in E2. lia.
Qed.

Lemma tsafe_sys_mmap_fixed_facts : forall addr len s P, tsafe (sys_mmap_fixed_none addr len s) P ->
  0 < bv_unsigned len < 2^62 /\ 0 < bv_unsigned addr /\
  bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= alloc_top (ms_vm s).
Proof.
  intros addr len s P HS. unfold sys_mmap_fixed_none in HS.
  destruct (0 <? bv_unsigned len) eqn:E1; [|cbn in HS; contradiction].
  destruct (bv_unsigned len <? 2^62) eqn:E2; [|cbn in HS; contradiction].
  destruct (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <=? alloc_top (ms_vm s)) eqn:E3; [|cbn in HS; contradiction].
  destruct (bv_unsigned addr mod page_size =? 0) eqn:E4; [|cbn in HS; contradiction].
  destruct (0 <? bv_unsigned addr) eqn:E0; [|cbn in HS; contradiction].
  apply Z.ltb_lt in E1. apply Z.ltb_lt in E2. apply Z.leb_le in E3. apply Z.ltb_lt in E0. lia.
Qed.

Lemma tsafe_sys_mprotect_facts : forall addr len s P, tsafe (sys_mprotect_rw addr len s) P ->
  0 < bv_unsigned len /\ bv_unsigned addr mod page_size = 0 /\
  bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= alloc_top (ms_vm s).
Proof.
  intros addr len s P HS. unfold sys_mprotect_rw in HS.
  destruct (0 <? bv_unsigned len) eqn:E1; [|cbn in HS; contradiction].
  destruct (bv_unsigned addr mod page_size =? 0) eqn:E2; [|cbn in HS; contradiction].
  destruct (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <=? alloc_top (ms_vm s)) eqn:E3; [|cbn in HS; contradiction].
  apply Z.ltb_lt in E1. apply Z.eqb_eq in E2. apply Z.leb_le in E3. lia.
Qed.

(* [comment removed for export] *)
Lemma eperm_skip : forall (s r : word),
  bv_unsigned r <> 2^64 - 1 ->
  c_eq (v_or s (v_xori r (-1))) (Z_to_bv 64 0) = false.
Proof.
  intros s r Hr. unfold c_eq, bv_eqb. apply Z.eqb_neq.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  pose proof (u64_range s) as Hs. pose proof (u64_range r) as Hr'.
  assert (Hx : 0 <= Z.lxor (bv_unsigned r) (bv_wrap 64 (-1)) < 2^64).
  { apply Z_lxor_range; [lia|]. change (bv_wrap 64 (-1)) with (2^64 - 1)%Z. lia. }
  unfold v_or, v_xori. rewrite (Z_to_bv_small_unsigned (Z.lxor _ _)) by lia.
  rewrite Z_to_bv_small_unsigned by (apply Z_lor_range; lia).
  intros H0. apply Z.lor_eq_0_iff in H0 as [_ H0]. apply Z.lxor_eq in H0.
  change (bv_wrap 64 (-1)) with (2^64 - 1)%Z in H0. lia.
Qed.

(* [comment removed for export] *)
Lemma sysret_addr : forall (a : word) h nZ,
  bv_unsigned a + nZ <= alloc_top h -> 0 <= nZ ->
  c_ltu a (Z_to_bv 64 18446744073709547521) = true.
Proof.
  intros a h nZ Ha Hn. unfold c_ltu, bv_ltu. rewrite u64_lit by lia.
  pose proof (alloc_top_lt64 h). unfold stack_max_size in H. apply Z.ltb_lt. lia.
Qed.

Lemma u_errno_ret : forall e, 0 < e < 4096 -> bv_unsigned (errno_ret e) = 2^64 - e.
Proof.
  intros e He. unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^64)%Z.
  rewrite <- (Z.mod_add (-e) 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma mmap_len_ok : forall (len : word),
  bv_unsigned len < 2^62 -> c_ltu len (Z_to_bv 64 9223372036854775807) = true.
Proof. intros len H. unfold c_ltu, bv_ltu. rewrite u64_lit by lia. apply Z.ltb_lt. pose proof (u64_range len). lia. Qed.

(* [comment removed for export] *)
Lemma page_mask_val : 18446744073709547520 = Z.ones 52 * 2^12.
Proof. reflexivity. Qed.

Lemma land_page_mask : forall v, 0 <= v < 2^64 ->
  Z.land v 18446744073709547520 = (v / 2^12) * 2^12.
Proof.
  intros v Hv. rewrite page_mask_val. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec.
  destruct (Z_lt_le_dec n 12).
  - rewrite !Z.mul_pow2_bits_low by lia. rewrite andb_false_r. reflexivity.
  - rewrite !Z.mul_pow2_bits by lia.
    rewrite Z.div_pow2_bits by lia. rewrite Z.testbit_ones by lia.
    replace (n - 12 + 12) with n by lia.
    destruct (Z_lt_le_dec n 64).
    + replace ((0 <=? n - 12) && (n - 12 <? 52))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
      rewrite andb_true_r. reflexivity.
    + replace ((0 <=? n - 12) && (n - 12 <? 52))%bool with false
        by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; lia).
      rewrite andb_false_r.
      destruct Hv as [H0 H1].
      destruct (Z.eq_dec v 0) as [->|Hnz]; [rewrite Z.testbit_0_l; reflexivity|].
      rewrite (Z.bits_above_log2 v n); [reflexivity|lia|].
      apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma mod_as_div4096 : forall v, v mod 4096 = v - (v / 2^12) * 2^12.
Proof. intros v. change (2^12) with 4096. pose proof (Z.div_mod v 4096 ltac:(lia)). lia. Qed.

Lemma and_pagemask_aligned : forall x : word,
  bv_unsigned x mod 4096 = 0 -> v_and (Z_to_bv 64 18446744073709547520) x = x.
Proof.
  intros x Hx. pose proof (u64_range x) as Hr. apply bv_eq. unfold v_and.
  rewrite (u64_lit 18446744073709547520) by lia.
  rewrite Z.land_comm, land_page_mask by lia.
  pose proof (mod_as_div4096 (bv_unsigned x)).
  rewrite u64_lit by lia. lia.
Qed.

Lemma mprotect_len_u : forall addr len : word,
  bv_unsigned addr mod 4096 = 0 -> bv_unsigned addr + bv_unsigned len + 8192 <= 2^64 ->
  bv_unsigned (v_sub (v_and (v_addi (v_add (v_add addr len) (Z_to_bv 64 4096)) (-1))
                            (Z_to_bv 64 18446744073709547520))
                     (v_and (Z_to_bv 64 18446744073709547520) addr))
  = page_round_up_Z (bv_unsigned len).
Proof.
  intros addr len Hal Hb. pose proof (u64_range addr) as Ha. pose proof (u64_range len) as Hl.
  rewrite (and_pagemask_aligned addr Hal).
  unfold v_sub, v_and, v_addi, v_add.
  rewrite (u64_lit 4096) by lia. rewrite (u64_lit 18446744073709547520) by lia.
  rewrite (u64_lit (bv_unsigned addr + bv_unsigned len)) by lia.
  rewrite (u64_lit (bv_unsigned addr + bv_unsigned len + 4096)) by lia.
  rewrite (u64_lit (bv_unsigned addr + bv_unsigned len + 4096 + -1)) by lia.
  rewrite land_page_mask by lia.
  pose proof (mod_as_div4096 (bv_unsigned addr + bv_unsigned len + 4096 + -1)) as Hm.
  pose proof (mod_as_div4096 (bv_unsigned addr)) as Hma.
  assert (Hq : (bv_unsigned addr + bv_unsigned len + 4096 + -1) / 2^12 * 2^12
               = bv_unsigned addr + page_round_up_Z (bv_unsigned len)).
  { unfold page_round_up_Z, page_size. change (2^12) with 4096 in *.
    replace (bv_unsigned addr + bv_unsigned len + 4096 + -1) with (bv_unsigned len + 4096 - 1 + (bv_unsigned addr / 4096) * 4096) by lia.
    rewrite Z.div_add by lia. lia. }
  rewrite Hq. pose proof (page_round_up_Z_bounds (bv_unsigned len) (proj1 Hl)).
  rewrite (u64_lit (bv_unsigned addr + page_round_up_Z (bv_unsigned len))) by lia.
  rewrite u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma brk_zeros_out : forall h (req : word) m (x : word),
  brk_grow_ok_vm h req req = true ->
  0 < bv_unsigned (vm_brk h) < bv_unsigned req ->
  alloc_top h <= bv_unsigned x ->
  apply_zeros m (brk_zeros req req (vm_brk h)) x = m x.
Proof.
  intros h req m x Hok [H0 Hlt] Hx.
  assert (Hreq : req <> Z_to_bv 64 0).
  { intros E. rewrite E in Hlt. rewrite Z_to_bv_small_unsigned in Hlt by lia. pose proof (u64_range (vm_brk h)). lia. }
  rewrite (brk_zeros_grow req req (vm_brk h) Hreq H0 Hlt).
  unfold brk_grow_ok_vm in Hok.
  rewrite (proj2 (Z.ltb_lt _ _) H0), (proj2 (Z.ltb_lt _ _) Hlt) in Hok. cbn [andb] in Hok.
  unfold brk_page_range.
  destruct (page_round_up_Z (bv_unsigned (vm_brk h)) <? page_round_up_Z (bv_unsigned req)) eqn:El; [|reflexivity].
  apply andb_prop in Hok as [Hok _]. apply andb_prop in Hok as [Hc _]. apply Z.leb_le in Hc.
  apply Z.ltb_lt in El.
  pose proof (u64_range (vm_brk h)) as Hbr.
  pose proof (page_round_up_Z_bounds (bv_unsigned (vm_brk h)) (proj1 Hbr)) as Hn0.
  pose proof (alloc_top_lt64 h) as Htop. unfold stack_max_size in Htop.
  cbn [apply_zeros zeros_cover existsb fst snd].
  rewrite !Z_to_bv_small_unsigned by lia.
  destruct (page_round_up_Z (bv_unsigned (vm_brk h)) <=? bv_unsigned x) eqn:E1;
  destruct (bv_unsigned x <? page_round_up_Z (bv_unsigned (vm_brk h)) + (page_round_up_Z (bv_unsigned req) - page_round_up_Z (bv_unsigned (vm_brk h)))) eqn:E2;
    cbn [andb orb]; try reflexivity.
  apply Z.ltb_lt in E2. lia.
Qed.

Lemma apply_zeros_nn : forall m zs (x : word), m x <> None -> apply_zeros m zs x <> None.
Proof.
  intros m zs x H. unfold apply_zeros. destruct zs; [exact H|].
  destruct (zeros_cover _ x); [discriminate | exact H].
Qed.

End Sys.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sys_reg :=
  regnorm; imm_norm; rewrite ?v_addi_0; cbn [mmap_prot];
  first [ assumption | reflexivity
        | klitsg; first [ assumption | reflexivity | bveq
                        | lazymatch goal with
                          | |- bv_unsigned ?x = _ => check_closed_term x; vm_compute; reflexivity
                          end ]
        | match goal with H : ?x = _ |- bv_unsigned ?x = _ => rewrite H; vm_compute; reflexivity end
        | match goal with |- ?g => fail 1 "sys_reg:" g end ].

(* [comment removed for export] *)
Ltac sys_focus HS :=
  lazymatch goal with
  | |- realizes _ _ (tshape (MallocTree.mbind _ _ _) _) =>
      apply rz_bind_shape; apply tsafe_bind_inv in HS
  | |- _ => idtac
  end.

Ltac sys_unfocus HS :=
  try (lazymatch goal with
       | |- realizes ?segs ?C (tshape (MallocTree.mret ?r ?s1) ?F) =>
           lazymatch F with
           | (fun _ _ => _) => change (realizes segs C (F r s1)); cbv beta
           end
       end);
  try (lazymatch type of HS with
       | tsafe (MallocTree.mret ?r ?s1) ?Q =>
           lazymatch Q with
           | (fun _ _ => _) => change (Q r s1) in HS; cbv beta in HS
           end
       end).

(* [comment removed for export] *)
Ltac sys_rethread Hag HI HS magree_tac top_lemma :=
  let HInew := fresh "HI" in let Hag' := fresh "Hag" in
  lazymatch type of HS with
  | tsafe (_ ?s1) _ =>
      first [ pose proof (minv_same _ _ s1 HI eq_refl eq_refl (top_lemma)) as HInew
            | pose proof (minv_same _ _ s1 HI eq_refl eq_refl eq_refl) as HInew ];
      magree_tac Hag';
      clear Hag HI; rename Hag' into Hag; rename HInew into HI; note_win HI
  end.

(* [comment removed for export] *)
Ltac mach_sys_munmap Hp HS Hag HI :=
  sys_focus HS;
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst ?R ?pc ?mm ?rom) (with_vmmaps _ ?md)) (tshape (sys_munmap ?a ?l ?s) _) =>
      eapply (rz_sys_munmap_at md R pc _ mm rom s a l);
      [ mpure Hp | solveF | reflexivity | sys_reg | sys_reg | sys_reg
      | exact (wtop_task _ (minv_ceil _ _ HI))
      | exact HS
      | ];
      let HS' := fresh "HS" in let Hc := fresh "Hktop" in let Hn := fresh "Hkn" in
      cbv zeta; intros HS' Hc Hn; rz_norm;
      clear HS; rename HS' into HS; cbn [ms_lo ms_hi ms_mem ms_vm upd] in Hc; pose proof (u64_range (page_round_up l));
      sys_rethread Hag HI HS
        ltac:(fun Hag' => pose proof (magree_unfill s mm a (page_round_up l) (vm_munmap a (page_round_up l) (ms_vm s)) Hag) as Hag')
        (alloc_top_vm_munmap a (page_round_up l) (ms_vm s))
  end;
  sys_unfocus HS; mnorm HS.

(* [comment removed for export] *)
Ltac mach_sys_brk_query Hp HS Hag HI :=
  sys_focus HS;
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst ?R ?pc ?mm ?rom) (with_vmmaps _ ?md)) (tshape (sys_brk_query ?s) _) =>
      eapply (rz_sys_brk_query_at md R pc _ mm rom s);
      [ mpure Hp | solveF | reflexivity | sys_reg | sys_reg | exact HS | ];
      let HS' := fresh "HS" in
      intros HS'; rz_norm; clear HS; rename HS' into HS
  end;
  sys_unfocus HS; mnorm HS.

(* [comment removed for export] *)
Ltac mach_sys_brk_grow Hp HS Hag HI :=
  sys_focus HS;
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst ?R ?pc ?mm ?rom) (with_vmmaps _ ?md)) (tshape (sys_brk_grow ?rq ?s) _) =>
      eapply (rz_sys_brk_grow_at md R pc _ mm rom s rq);
      [ mpure Hp | solveF | reflexivity | sys_reg | sys_reg | exact HS
      | let HS' := fresh "HS" in let Hb := fresh "Hbrk" in
        intros HS' Hb; rz_norm; clear HS; rename HS' into HS; cbn [ms_lo ms_hi ms_mem ms_vm upd] in Hb;
        sys_unfocus HS; mnorm HS
      | let HS' := fresh "HS" in let Hg := fresh "Hgrow" in let Hb := fresh "Hbrk" in
        cbv zeta; intros HS' Hg Hb; rz_norm; clear HS; rename HS' into HS;
        cbn [ms_lo ms_hi ms_mem ms_vm upd] in Hg, Hb;
        sys_rethread Hag HI HS
          ltac:(fun Hag' => pose proof (magree_apply_zeros s mm (brk_zeros rq rq (vm_brk (ms_vm s))) (vm_brk_grow rq (ms_vm s)) Hag) as Hag';
                            cbn [ms_lo ms_hi ms_mem ms_vm upd] in Hag')
          (alloc_top_vm_brk_grow rq (ms_vm s));
        sys_unfocus HS; mnorm HS ]
  end.

(* [comment removed for export] *)
Ltac mach_sys_mmap Hp HS Hag HI :=
  sys_focus HS;
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst ?R ?pc ?mm ?rom) (with_vmmaps _ ?md)) (tshape (sys_mmap ?k ?l ?s) _) =>
      eapply (rz_sys_mmap_at k md R pc _ mm rom s l);
      [ mpure Hp | solveF | reflexivity | sys_reg | sys_reg | sys_reg | sys_reg | sys_reg | sys_reg | exact HS
      | let HS' := fresh "HS" in let Hlen := fresh "Hlen" in
        intros HS' Hlen; rz_norm; clear HS; rename HS' into HS;
        unfold set_errno in HS |- *; sys_unfocus HS; mnorm HS
      | let a := fresh "ma" in let HS' := fresh "HS" in let Hal := fresh "Hmal" in let Ha0 := fresh "Hma0" in
        let Htop := fresh "Hmtop" in let Hn := fresh "Hmn" in let Hlen := fresh "Hlen" in
        intros a; cbv zeta; intros HS' Hal Ha0 Htop Hn Hlen; rz_norm; clear HS; rename HS' into HS;
        cbn [ms_lo ms_hi ms_mem ms_vm upd] in Htop;
        pose proof (u64_range a); pose proof (u64_range (page_round_up l));
        lazymatch k with
        | MMrw =>
            sys_rethread Hag HI HS
              ltac:(fun Hag' => pose proof (magree_zfill s mm a (page_round_up l) (vm_mmap a (page_round_up l) (ms_vm s)) Hag) as Hag')
              (alloc_top_vm_mmap a (page_round_up l) (ms_vm s))
        | MMnone =>
            sys_rethread Hag HI HS
              ltac:(fun Hag' => pose proof (magree_unfill s mm a (page_round_up l) (vm_noacc a (page_round_up l) (ms_vm s)) Hag) as Hag')
              (alloc_top_vm_noacc a (page_round_up l) (ms_vm s))
        end;
        sys_unfocus HS; mnorm HS ]
  end.

(* [comment removed for export] *)
Ltac mach_sys_mmap_fixed Hp HS Hag HI :=
  sys_focus HS;
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst ?R ?pc ?mm ?rom) (with_vmmaps _ ?md)) (tshape (sys_mmap_fixed_none ?a ?l ?s) _) =>
      eapply (rz_sys_mmap_fixed_at md R pc _ mm rom s a l);
      [ mpure Hp | solveF | reflexivity | sys_reg | sys_reg | sys_reg | sys_reg | sys_reg | sys_reg | sys_reg
      | exact HS
      | let HS' := fresh "HS" in let Hc := fresh "Hktop" in let Hn := fresh "Hkn" in let Hlen := fresh "Hlen" in
        intros HS' Hc Hn Hlen; rz_norm; clear HS; rename HS' into HS; cbn [ms_lo ms_hi ms_mem ms_vm upd] in Hc;
        unfold set_errno in HS |- *; sys_unfocus HS; mnorm HS
      | let HS' := fresh "HS" in let Hc := fresh "Hktop" in let Hn := fresh "Hkn" in let Hlen := fresh "Hlen" in
        cbv zeta; intros HS' Hc Hn Hlen; rz_norm; clear HS; rename HS' into HS; cbn [ms_lo ms_hi ms_mem ms_vm upd] in Hc;
        sys_rethread Hag HI HS
          ltac:(fun Hag' => pose proof (magree_unfill s mm a (page_round_up l) (vm_fixed_ok a (page_round_up l) (ms_vm s)) Hag) as Hag')
          (alloc_top_vm_fixed_ok a (page_round_up l) (ms_vm s));
        sys_unfocus HS; mnorm HS
      | let HS' := fresh "HS" in let Hc := fresh "Hktop" in let Hn := fresh "Hkn" in let Hlen := fresh "Hlen" in
        cbv zeta; intros HS' Hc Hn Hlen; rz_norm; clear HS; rename HS' into HS; cbn [ms_lo ms_hi ms_mem ms_vm upd] in Hc;
        sys_rethread Hag HI HS
          ltac:(fun Hag' => pose proof (magree_unfill s mm a (page_round_up l) (vm_fixed_destroy a (page_round_up l) (ms_vm s)) Hag) as Hag')
          (alloc_top_vm_fixed_destroy a (page_round_up l) (ms_vm s));
        unfold set_errno in HS |- *; sys_unfocus HS; mnorm HS ]
  end.

(* [comment removed for export] *)
Ltac mach_sys_mprotect Hp HS Hag HI :=
  sys_focus HS;
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst ?R ?pc ?mm ?rom) (with_vmmaps _ ?md)) (tshape (sys_mprotect_rw ?a ?l ?s) _) =>
      eapply (rz_sys_mprotect_at md R pc _ mm rom s a l);
      [ mpure Hp | solveF | reflexivity | sys_reg
      | regnorm; reflexivity
      | first [ reflexivity | apply and_pagemask_aligned; alia ]
      | regnorm; reflexivity
      | first [ apply mprotect_len_u; alia
              | match goal with |- ?g => fail 1 "mprotect a1:" g end ]
      | sys_reg | exact HS
      | let HS' := fresh "HS" in let Hc := fresh "Hktop" in let Hn := fresh "Hkn" in
        intros HS' Hc Hn; rz_norm; clear HS; rename HS' into HS; cbn [ms_lo ms_hi ms_mem ms_vm upd] in Hc;
        unfold set_errno in HS |- *; sys_unfocus HS; mnorm HS
      | let HS' := fresh "HS" in let Hc := fresh "Hktop" in let Hn := fresh "Hkn" in
        cbv zeta; intros HS' Hc Hn; rz_norm; clear HS; rename HS' into HS; cbn [ms_lo ms_hi ms_mem ms_vm upd] in Hc;
        sys_rethread Hag HI HS
          ltac:(fun Hag' => pose proof (magree_zfill s mm a (page_round_up l) (vm_unprotect a (page_round_up l) (ms_vm s)) Hag) as Hag')
          (alloc_top_vm_unprotect a (page_round_up l) (ms_vm s));
        sys_unfocus HS; mnorm HS
      | let HS' := fresh "HS" in let Hc := fresh "Hktop" in let Hn := fresh "Hkn" in
        intros HS' Hc Hn; rz_norm; clear HS; rename HS' into HS; cbn [ms_lo ms_hi ms_mem ms_vm upd] in Hc;
        sys_unfocus HS; mnorm HS ]
  end.

(* [comment removed for export] *)
Ltac eperm_tac :=
  apply eperm_skip;
  first [ lazymatch goal with
          | |- bv_unsigned ?x <> _ => check_closed_term x; vm_compute; lia
          end
        | alia ].

(* [comment removed for export] *)
Ltac sysret_addr_tac :=
  idtac;  (* [comment removed for export] *)
  match goal with
  | Ht : (_ <= alloc_top _)%Z |- c_ltu ?a _ = true =>
      lazymatch type of Ht with (bv_unsigned a + _ <= _)%Z => eapply sysret_addr; [exact Ht | alia] end
  end.

(* [comment removed for export] *)
Ltac unum :=
  repeat match goal with
  | |- context [bv_unsigned ?c] =>
      lazymatch c with
      | Z_to_bv _ (bv_unsigned _) => fail
      | _ => check_closed_term c;
             let v := eval vm_compute in (bv_unsigned c) in
             replace (bv_unsigned c) with v by (vm_compute; reflexivity)
      end
  end.

(* [comment removed for export] *)
Ltac mach_ld_rdn Hp Hrd Hv :=
  eapply rz_step_p; [ mpure Hp | reflexivity
    | eapply step_ld_at; [ solveF | reflexivity | solveD | reflexivity
                         | regnorm; imm_norm; rewrite ?v_addi_0; klitsg; first [reflexivity | bveq]
                         | repeat (first [ exact Hrd
                                         | rewrite rdn_wbytes_out by (rewrite ?length_w2l; unum; uaddr; alia)
                                         | rewrite rdn_unfill_out by (unum; uaddr; alia)
                                         | rewrite rdn_zfill_out by (unum; uaddr; alia) ])
                         | exact Hv ]
    | rz_norm ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac peel1 x ::=
  first
    [ match goal with
      | Hf : forall a : word, in_frame _ _ a -> ?m1 a = ?m0 a |- ?m1 x = _ =>
          peel_by (Hf x) ltac:(unfold in_frame; uaddr; alia)
      end
    | match goal with
      | Hok : acc_ok ?s ?a (Z.of_nat ?n) = true |- wbytes ?m ?a ?bs x = _ =>
          peel_by (wbytes_win_out s a n bs m x Hok (length_w2l _ _)) ltac:(uaddr; alia)
      | Hok : acc_ok ?s ?a ?z = true |- wbytes ?m ?a ?bs x = _ =>
          peel_by (wbytes_win_out s a (Z.to_nat z) bs m x Hok (length_w2l _ _)) ltac:(uaddr; alia)
      end
    | lazymatch goal with
      | |- wbytes ?m ?a ?bs x = _ =>
          peel_by (wbytes_out bs m a x) ltac:(rewrite ?length_w2l; uaddr; alia)
      end
    | lazymatch goal with
      | |- unfill ?a ?n ?m x = _ => peel_by (unfill_out a n m x) ltac:(uaddr; alia)
      end
    | lazymatch goal with
      | |- zfill ?a ?n ?m x = _ => peel_by (zfill_out a n m x) ltac:(uaddr; alia)
      | |- apply_zeros ?m [(?a, ?n)] x = _ => peel_by (apply_zeros1_out a n m x) ltac:(uaddr; alia)
      | |- apply_zeros ?m [] x = _ => rewrite (apply_zeros0 m)
      | |- apply_zeros ?m (brk_zeros ?rq ?rq (vm_brk ?h)) x = _ =>
          match goal with
          | Hg : brk_grow_ok_vm h rq rq = true, Hb : (0 < bv_unsigned (vm_brk h) < bv_unsigned rq)%Z |- _ =>
              peel_by (brk_zeros_out h rq m x Hg Hb) ltac:(uaddr; alia)
          end
      end
    | match goal with
      | HWb : mwin _ ?m0 _ _ ?mb |- ?mb x = _ =>
          peel_by (proj1 HWb x) ltac:(uaddr; alia)
      end
    | match goal with
      | Hj : forall a : word, _ -> ?m1 a = ?m0 a |- ?m1 x = _ =>
          peel_by (Hj x) ltac:(uaddr; alia)
      end
    | match goal with
      | Hp : forall a : word, _ -> _ -> ?m1 a = ?m0 a |- ?m1 x = _ =>
          peel_by (Hp x) ltac:(uaddr; alia)
      end ].

Ltac nn_at x ::=
  repeat first
    [ lazymatch goal with
      | |- wbytes _ _ _ x <> None => apply wbytes_nn
      | |- unfill ?a ?n ?m x <> None => nn_by (unfill_out a n m x) ltac:(uaddr; alia)
      | |- zfill ?a ?n ?m x <> None => apply zfill_nn
      | |- apply_zeros ?m _ x <> None => apply apply_zeros_nn
      end
    | match goal with
      | Hn : forall a : word, in_frame _ _ a -> ?m1 a <> None |- ?m1 x <> None =>
          apply Hn; unfold in_frame; uaddr; alia
      end
    | match goal with
      | HWb : mwin _ _ _ _ ?mb |- ?mb x <> None =>
          first [ apply (proj2 HWb); uaddr; alia
                | nn_by (proj1 HWb x) ltac:(uaddr; alia) ]
      | Hn : forall a : word, (?lo <= bv_unsigned a < ?hi)%Z -> ?m1 a <> None |- ?m1 x <> None =>
          first [ apply Hn; uaddr; alia
                | match goal with
                  | Hp : forall a : word, _ -> _ -> m1 a = ?m0 a |- _ =>
                      first [ nn_by (Hp x) ltac:(uaddr; alia)
                            | destruct (Z_lt_le_dec (bv_unsigned x) lo);
                              [ nn_by (Hp x) ltac:(uaddr; alia)
                              | destruct (Z_lt_le_dec (bv_unsigned x) hi);
                                [ apply Hn; uaddr; alia
                                | nn_by (Hp x) ltac:(uaddr; alia) ] ] ]
                  end ]
      | Hj : forall a : word, _ -> ?m1 a = ?m0 a |- ?m1 x <> None =>
          nn_by (Hj x) ltac:(uaddr; alia)
      | Hp : forall a : word, _ -> _ -> ?m1 a = ?m0 a |- ?m1 x <> None =>
          nn_by (Hp x) ltac:(uaddr; alia)
      end ].
