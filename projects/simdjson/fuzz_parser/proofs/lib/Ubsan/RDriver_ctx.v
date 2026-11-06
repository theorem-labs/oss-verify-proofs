(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree Startup_kit STRW_tac.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg F_syscalls StdioFiles PStartU.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface PU_iface PIosX_iface RDriver_iface RDriver_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver PState ProgP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section CTX.
  Variables (sp0 : word) (argv envp : list (list byte)) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).

  Definition LO : Z := usp0 - 8388608.

  (* [comment removed for export] *)
  Definition MFRAME (mm : mem) (j8 : list byte) (s7v s6v s5v s4v : word) : Prop :=
    rw_cells usegs mm (usp0 + -128)
      [CB 8 j8; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 (Z_to_bv 64 (envp_addr sp0 argv)); C8 (Z_to_bv 64 PMAIN);
       C8 (Z_to_bv 64 (argc argv)); C8 (Z_to_bv 64 (usp0 + 8)); C8 (Z_to_bv 64 PSTAGE2_RET)].

  (* [comment removed for export] *)
  Definition RSTAT (mm : mem) : Prop :=
    rw_cells usegs mm 0x91d18 [C8 (Z_to_bv 64 0x91d18); C8 (Z_to_bv 64 0x91d18); C8 (Z_to_bv 64 0x91d18); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 TID)]
    /\ rw_cells usegs mm 0xb2048 [C4 (Z_to_bv 64 0)]
    /\ rw_cells usegs mm 0x7fbf0 [C8 (Z_to_bv 64 0x7c7b8); C8 (Z_to_bv 64 0x7c7b0)]
    /\ rw_cells usegs mm 0x7c7b0 [C8 (Z_to_bv 64 0x265c8)]
    /\ rw_cells usegs mm 0x811a8 [C1 (Z_to_bv 8 0)]
    /\ rw_cells usegs mm 0x7fad0 [C8 (Z_to_bv 64 0x6c9a0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs mm 0xb24a0 [C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs mm 0xb2490 [C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs mm 0x81140 [C8 (Z_to_bv 64 0x81058)]
    /\ rw_cells usegs mm 0x81050 [C8 (Z_to_bv 64 0x80f68)]
    /\ rw_cells usegs mm 0x7fae0 [C8 (Z_to_bv 64 0x7fa30)]
    /\ rw_cells usegs mm 0x7fa30 [C8 (Z_to_bv 64 0x80f68)]
    /\ ios_cells mm
    /\ rw_cells usegs mm 0x80c00 [C8 (Z_to_bv 64 0x80c00)].

  Definition rstat_addr (a : Z) : Prop :=
    (0x91d18 <= a < 0x91d3c) \/ (0xb2048 <= a < 0xb204c) \/ (0x7fbf0 <= a < 0x7fc00) \/ (0x7c7b0 <= a < 0x7c7b8)
    \/ (0x811a8 <= a < 0x811a9) \/ (0x7fad0 <= a < 0x7fae0) \/ (0xb2490 <= a < 0xb2498) \/ (0xb24a0 <= a < 0xb24a8)
    \/ (0x81140 <= a < 0x81148) \/ (0x81050 <= a < 0x81058) \/ (0x7fae0 <= a < 0x7fae8) \/ (0x7fa30 <= a < 0x7fa40)
    \/ (0x80c00 <= a < 0x80c08) \/ ios_addr a.

  Ltac tr AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold rstat_addr, ios_addr; cbn in Ha; lia].

  Lemma RSTAT_agree : forall (P : Z -> Prop) m m', magree usegs P m m' -> (forall a, rstat_addr a -> P a) -> RSTAT m -> RSTAT m'.
  Proof.
    intros P m m' AG HP (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A14 & A15). unfold RSTAT.
    split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3|]. split; [tr AG HP A4|].
    split; [tr AG HP A5|]. split; [tr AG HP A6|]. split; [tr AG HP A7|]. split; [tr AG HP A8|].
    split; [tr AG HP A9|]. split; [tr AG HP A10|]. split; [tr AG HP A11|]. split; [tr AG HP A12|].
    split; [exact I|].
    tr AG HP A15.
  Qed.

  (* [comment removed for export] *)
  Lemma RSTAT_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> RSTAT m -> RSTAT m'.
  Proof.
    intros LB SP m m' HP. apply (RSTAT_agree _ _ _ HP). intros a Ha. right; left.
    unfold rstat_addr, ios_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
  Qed.

  Lemma RSTAT_drv_pres : forall LB SP m m', pdrv_pres LB SP m m' -> RSTAT m -> RSTAT m'.
  Proof.
    intros LB SP m m' HP. apply (RSTAT_agree _ _ _ (pdrv_pres_agree _ _ _ _ HP)). intros a Ha. split.
    - right; left. unfold rstat_addr, ios_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
    - unfold rstat_addr, ios_addr, pstdout_ivs, client_wr, PINIT_FLAG, PNEWH in *. cbn. lia.
  Qed.

  Lemma RSTAT_munch : forall W m m', munch W m m' -> wmono usegs m m' -> (forall a, rstat_addr a -> outside W a) -> RSTAT m -> RSTAT m'.
  Proof.
    intros W m m' MU WM HW. apply (RSTAT_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha.
  Qed.
End CTX.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition stdout_addr (a : Z) : Prop := (0x81058 <= a < 0x81140) \/ (0xb24b8 <= a < 0xb28b8).
Definition stderr_addr (a : Z) : Prop := 0x80f68 <= a < 0x81050.
(* [comment removed for export] *)
Definition cstat_addr (a : Z) : Prop :=
  (0x7c7c8 <= a < 0x7c7f8) \/ (0x7c830 <= a < 0x7c880) \/ (0x911f8 <= a < 0x91202) \/ (0x91228 <= a < 0x9122a) \/ (0x91270 <= a < 0x9129c)
  \/ (0x7fb20 <= a < 0x7fb28) \/ (0x80f30 <= a < 0x80f34).      (* [comment removed for export] *)
Definition trun0_addr (a : Z) : Prop :=
  (PINIT_FLAG <= a < PINIT_FLAG + 1) \/ (PGOT_FUZZ_INIT <= a < PGOT_FUZZ_INIT + 8) \/ cstat_addr a \/ patx_addr a \/ pincb_addr a.

(* [comment removed for export] *)
Definition client_static0 (m : mem) : Prop := client_img m /\ cstat_image m.
Definition TRUN0 (m : mem) : Prop := trun_cells0 m /\ client_static0 m.
Definition XT (m : mem) : Prop := (patexit_main m \/ patexit_reg m) /\ pincb 0 m.

Lemma patx_table_agree : forall (P : Z -> Prop) n hd f0 a0 m m',
  magree usegs P m m' -> (forall a, patx_addr a -> P a) -> patx_table n hd f0 a0 m -> patx_table n hd f0 a0 m'.
Proof.
  intros P n hd f0 a0 m m' AG HP (A1 & A2 & A3). unfold patx_table.
  split; [|split]; (eapply rw_cells_magree; [exact AG| eassumption| intros a Ha; apply HP; unfold patx_addr; cbn in Ha; lia]).
Qed.
Lemma pincb_agree : forall (P : Z -> Prop) cb m m',
  magree usegs P m m' -> (forall a, pincb_addr a -> P a) -> pincb cb m -> pincb cb m'.
Proof.
  intros P cb m m' AG HP A. unfold pincb in *.
  eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold pincb_addr; cbn in Ha; lia].
Qed.
Lemma XT_agree : forall (P : Z -> Prop) m m',
  magree usegs P m m' -> (forall a, patx_addr a \/ pincb_addr a -> P a) -> XT m -> XT m'.
Proof.
  intros P m m' AG HP (T & C). split.
  - destruct T as [T|T]; [left| right]; exact (patx_table_agree _ _ _ _ _ _ _ AG (fun a Ha => HP a (or_introl Ha)) T).
  - exact (pincb_agree _ _ _ _ AG (fun a Ha => HP a (or_intror Ha)) C).
Qed.
Lemma XT_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> XT m -> XT m'.
Proof.
  intros LB SP m m' HP. apply (XT_agree _ _ _ HP). intros a Ha. right; left.
  unfold patx_addr, pincb_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma XT_munch : forall W m m', munch W m m' -> wmono usegs m m' -> (forall a, patx_addr a \/ pincb_addr a -> outside W a) -> XT m -> XT m'.
Proof. intros W m m' MU WM HW. apply (XT_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma XT_of_TRUN0 : forall m, TRUN0 m -> XT m.
Proof. intros m [(_ & _ & T & C) _]. split; [left; exact T| exact C]. Qed.
Lemma XT_of_reg : forall m, patexit_reg m -> pincb 0 m -> XT m.
Proof. intros m T C. split; [right; exact T| exact C]. Qed.

(* [comment removed for export] *)
Lemma client_static0_init : forall (m : mem),
  (forall a : word, (0x7c000 <= bv_unsigned a < 0xb3000)%Z -> outside (pcrt_written) (bv_unsigned a) -> m a = None) ->
  client_static0 m.
Proof.
  intros m NONE.
  pimg_chunk0 NONE m 0x7c7c8 vtab_impl_cells H1.
  pimg_chunk0 NONE m 0x7c830 vtab_dom_cells H2.
  pimg_chunk0 NONE m 0x7fb20 got_nothrow_cells H3.
  pimg_chunk0 NONE m 0x80f30 fmin_cells H4.
  split; [split; [exact H1| split; [exact H2| split; [exact H3| exact H4]]]|].
  intros a Ha. apply NONE; [lia| cbn [outside pcrt_written]; lia].
Qed.

Lemma client_static0_intro : forall s LB m, ps_fa s = None -> client_static0 m -> client_static s LB m.
Proof. intros s LB m E (CI & NO). unfold client_static. split; [exact CI|]. split; [exact E| left; exact NO]. Qed.

Lemma client_img_agree : forall (P : Z -> Prop) m m', magree usegs P m m' -> (forall a, cstat_addr a -> P a) -> client_img m -> client_img m'.
Proof.
  intros P m m' AG HP (C1 & C2 & C3 & C4).
  unfold client_img, PVTAB_IMPL, PVTAB_DOM, PGOT_NOTHROW, PFMIN, vtab_impl_cells, vtab_dom_cells, got_nothrow_cells, fmin_cells in *.
  repeat match goal with |- _ /\ _ => split end;
    (eapply rw_cells_magree; [exact AG| eassumption| intros a Ha; apply HP; unfold cstat_addr; cbn in Ha; lia]).
Qed.
Lemma cstat_image_agree : forall (P : Z -> Prop) m m', magree usegs P m m' -> (forall a, cstat_addr a -> P a) -> cstat_image m -> cstat_image m'.
Proof.
  intros P m m' AG HP NO a Ha. pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with (2^64) in RA.
  destruct (AG (bv_unsigned a) ltac:(lia) ltac:(apply HP; unfold cstat_addr; lia)) as [E _].
  rewrite wa_unsigned_id in E. rewrite E. exact (NO a Ha).
Qed.
Lemma cstat_built_agree : forall (P : Z -> Prop) m m', magree usegs P m m' -> (forall a, cstat_addr a -> P a) -> cstat_built m -> cstat_built m'.
Proof.
  intros P m m' AG HP (C1 & C2 & C3 & C4). unfold cstat_built, PACTIVE, PACTIVE_GUARD, PFALLBACK, PFALLBACK_GUARD, guard1, fallback_cells in *.
  repeat match goal with |- _ /\ _ => split end;
    (eapply rw_cells_magree; [exact AG| eassumption| intros a Ha; apply HP; unfold cstat_addr; cbn in Ha; lia]).
Qed.
Lemma client_static0_agree : forall (P : Z -> Prop) m m', magree usegs P m m' -> (forall a, cstat_addr a -> P a) -> client_static0 m -> client_static0 m'.
Proof.
  intros P m m' AG HP (CI & NO).
  split; [exact (client_img_agree _ _ _ AG HP CI)| exact (cstat_image_agree _ _ _ AG HP NO)].
Qed.
(* [comment removed for export] *)
Lemma client_static_agree : forall (P : Z -> Prop) s LB m m', magree usegs P m m' -> (forall a, cstat_addr a -> P a) ->
  (forall p V a, ps_fa s = Some p -> In (p, V, 8) LB -> V <= a < V + 8 -> P a) -> client_static s LB m -> client_static s LB m'.
Proof.
  intros P s LB m m' AG HP _ (CI & FA & CS). split; [exact (client_img_agree _ _ _ AG HP CI)|]. split; [exact FA|].
  destruct CS as [CS|CS]; [left; exact (cstat_image_agree _ _ _ AG HP CS)| right; exact (cstat_built_agree _ _ _ AG HP CS)].
Qed.
(* [comment removed for export] *)
Lemma client_static_fa : forall s s' LB m, ps_fa s' = ps_fa s -> client_static s LB m -> client_static s' LB m.
Proof. intros s s' LB m E (CI & FA & CS). split; [exact CI|]. split; [rewrite E; exact FA| exact CS]. Qed.
Lemma client_static_lb : forall s LB LB' m, (forall p V, ps_fa s = Some p -> In (p, V, 8) LB -> In (p, V, 8) LB') -> client_static s LB m -> client_static s LB' m.
Proof. intros s LB LB' m _ H. exact H. Qed.

Lemma stdout_file_agree : forall (P : Z -> Prop) m m' so,
  magree usegs P m m' -> (forall a, stdout_addr a -> P a) -> stdout_file m so -> stdout_file m' so.
Proof.
  intros P m m' so AG HP (flags & mode & tail & bufbytes & F1 & F2 & F3 & F4 & F5 & F6).
  exists flags, mode, tail, bufbytes. split; [| split; [exact F2| split; [| split; [exact F4| split; [exact F5| exact F6]]]]].
  - eapply rw_cells_magree; [exact AG| exact F1|]. intros a Ha. apply HP. left. cbn in Ha. lia.
  - eapply rw_cells_magree; [exact AG| exact F3|]. intros a Ha. apply HP. right. cbn in Ha. lia.
Qed.

Lemma stderr_file0_agree : forall (P : Z -> Prop) m m',
  magree usegs P m m' -> (forall a, stderr_addr a -> P a) -> stderr_file0 m -> stderr_file0 m'.
Proof.
  intros P m m' AG HP H. unfold stderr_file0 in *.
  eapply rw_cells_magree; [exact AG| exact H|]. intros a Ha. apply HP. unfold stderr_addr. cbn in Ha. lia.
Qed.

(* [comment removed for export] *)
Lemma blk_id_unique : forall (L : list block) p V n V' n', List.NoDup (map blk_id L) -> In (p, V, n) L -> In (p, V', n') L -> V = V' /\ n = n'.
Proof.
  induction L as [|b L IH]; intros p V n V' n' ND H1 H2; [destruct H1|].
  cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI ND].
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - rewrite E1 in E2. injection E2; intros; subst; split; reflexivity.
  - exfalso. apply NI. subst b. apply (in_map blk_id) in H2. exact H2.
  - exfalso. apply NI. subst b. apply (in_map blk_id) in H1. exact H1.
  - exact (IH p V n V' n' ND H1 H2).
Qed.
Lemma client_static_in : forall s LB m p, client_static s LB m -> ps_fa s = Some p -> exists V, In (p, V, 8) LB.
Proof. intros s LB m p (_ & FA & _) E. rewrite E in FA. discriminate FA. Qed.     (* [comment removed for export] *)
Lemma client_static_sub : forall s LB LB' m, client_static s LB m -> List.NoDup (map blk_id LB) -> (forall b, In b LB' -> In b LB) ->
  (forall p, ps_fa s = Some p -> exists V, In (p, V, 8) LB') -> client_static s LB' m.
Proof. intros s LB LB' m H _ _ _. exact H. Qed.

Lemma trun_cells0_agree : forall (P : Z -> Prop) m m',
  magree usegs P m m' -> (forall a, trun0_addr a -> P a) -> trun_cells0 m -> trun_cells0 m'.
Proof.
  intros P m m' AG HP (A1 & A2 & A3 & A4). unfold trun_cells0.
  Ltac tr2 AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold trun0_addr; cbn in Ha; lia].
  split; [tr2 AG HP A1|]. split; [tr2 AG HP A2|].
  split; [eapply patx_table_agree; [exact AG| | exact A3]; intros a Ha; apply HP; unfold trun0_addr; right; right; right; left; exact Ha|].
  eapply pincb_agree; [exact AG| | exact A4]. intros a Ha. apply HP. unfold trun0_addr. right; right; right; right. exact Ha.
Qed.
Lemma TRUN0_agree : forall (P : Z -> Prop) m m',
  magree usegs P m m' -> (forall a, trun0_addr a -> P a) -> TRUN0 m -> TRUN0 m'.
Proof.
  intros P m m' AG HP [T C]. split; [exact (trun_cells0_agree _ _ _ AG HP T)|].
  apply (client_static0_agree _ _ _ AG); [| exact C]. intros a Ha. apply HP. unfold trun0_addr. right; right; left. exact Ha.
Qed.

Lemma stdout_file_heap_pres : forall LB SP m m' so, rheap_pres LB SP m m' -> stdout_file m so -> stdout_file m' so.
Proof.
  intros LB SP m m' so HP. apply (stdout_file_agree _ _ _ _ HP). intros a Ha. right; left.
  unfold stdout_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma stderr_file0_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> stderr_file0 m -> stderr_file0 m'.
Proof.
  intros LB SP m m' HP. apply (stderr_file0_agree _ _ _ HP). intros a Ha. right; left.
  unfold stderr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma stderr_file0_drv_pres : forall LB SP m m', pdrv_pres LB SP m m' -> stderr_file0 m -> stderr_file0 m'.
Proof.
  intros LB SP m m' HP. apply (stderr_file0_agree _ _ _ (pdrv_pres_agree _ _ _ _ HP)). intros a Ha. split.
  - right; left. unfold stderr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
  - unfold stderr_addr, pstdout_ivs, PINIT_FLAG, PNEWH in *. cbn. lia.
Qed.
Lemma TRUN0_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> TRUN0 m -> TRUN0 m'.
Proof.
  intros LB SP m m' HP. apply (TRUN0_agree _ _ _ HP). intros a Ha. right; left.
  unfold trun0_addr, cstat_addr, patx_addr, pincb_addr, PINIT_FLAG, PGOT_FUZZ_INIT, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma stdout_file_munch : forall W m m' so, munch W m m' -> wmono usegs m m' -> (forall a, stdout_addr a -> outside W a) -> stdout_file m so -> stdout_file m' so.
Proof. intros W m m' so MU WM HW. apply (stdout_file_agree _ _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma stderr_file0_munch : forall W m m', munch W m m' -> wmono usegs m m' -> (forall a, stderr_addr a -> outside W a) -> stderr_file0 m -> stderr_file0 m'.
Proof. intros W m m' MU WM HW. apply (stderr_file0_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma TRUN0_munch : forall W m m', munch W m m' -> wmono usegs m m' -> (forall a, trun0_addr a -> outside W a) -> TRUN0 m -> TRUN0 m'.
Proof. intros W m m' MU WM HW. apply (TRUN0_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section EXITS.
  Variables (sp0 : word) (argv envp : list (list byte)) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Hypothesis VSP : dvalid_sp sp0 argv envp.
  Hypothesis HT : 0 < TID < 4194304.

  Lemma sp_facts : 0x7fff80000000 <= usp0 <= 0x800000000000 /\ usp0 mod 16 = 0 /\ ATOP <= LO sp0 /\ LO sp0 + 8388608 = usp0 /\ 0xb3000 <= LO sp0.
  Proof. destruct VSP as ((A & B & C) & HATOP & _). unfold LO, sp_window_lo, sp_window_hi, stack_max_size in *. repeat split; lia. Qed.
  Lemma sp_atop : ATOP = LO sp0.
  Proof. destruct VSP as (_ & HATOP & _). unfold LO. exact HATOP. Qed.

  (* [comment removed for export] *)
  Lemma pat_exit_intro : forall (code : Z) (s : PState) (LB : list block) (SP : Z) (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo AB : Z) (errv : word),
    stk usegs m lo SP -> lo <= SP - PEXITU_STACK -> ATOP <= lo -> 0xb3000 <= lo -> 0 <= SP < 2^47 -> SP mod 16 = 0 ->
    RSTAT TID m -> RHEAP s LB m -> client_static s LB m -> rauxv_ok m AB -> SP <= AB -> rw_cells usegs m RERRNO [C4 errv] ->
    stdout_file m (ps_so s) -> stderr_file m -> mem_inv usegs m -> XT m ->
    pat_exitU code s (MS (mkR ra (Z_to_bv 64 SP) gpv tpv t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 PEXIT) fc None m (seg_rom usegs)).
  Proof.
    intros until errv. intros ST LOS LOAT LOLO SPR SP16 (TD & EXL & GF & FA & FIN & GCX & OFL & SIN & SOU & SEU & _ & _ & IOS & DSO) HP CS AUX SPAB ERR SOF SEF MI (XTT & XCB).
    unfold pat_exitU. do 33 eexists. exists m, lo, TID, AB, (Z_to_bv 64 0x91d18), (Z_to_bv 64 0x91d18), (Z_to_bv 64 0x91d18), (Z_to_bv 64 0), errv, (Z_to_bv 64 0x80c00), LB.
    split; [reflexivity|]. rewrite !unsigned_lit by lia. split; [exact ST|]. split; [exact TD|]. split; [exact EXL|]. split; [exact GF|]. split; [exact FA|].
    split; [exact FIN|]. split; [exact GCX|]. split; [exact DSO|]. split; [exact OFL|]. split; [exact SIN|]. split; [exact SOU|]. split; [exact SEU|].
    split; [exact SOF|]. split; [exact SEF|]. split; [exact IOS|]. split; [exact HP|]. split; [exact CS|]. split; [exact XTT|]. split; [exact XCB|].
    split; [exact AUX|]. split; [exact SPAB|].
    split; [exact ERR|]. split; [exact MI|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HT|]. split; [exact LOS|]. split; [exact LOAT|]. split; [exact LOLO|]. split; [exact SP16|]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma main_return : forall (code : Z) (s : PState) (LB : list block) (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (j8 : list byte) (s7v s6v s5v s4v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    MFRAME sp0 argv m j8 s7v s6v s5v s4v ->
    stk usegs m (LO sp0) (usp0 + -128) ->
    RSTAT TID m -> RHEAP s LB m -> client_static s LB m -> rauxv_ok m usp0 ->
    stdout_file m (ps_so s) -> stderr_file m -> mem_inv usegs m -> XT m ->
    evt usegs (pat_exitU code s)
      (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x26854) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros FR ST RS HP CS AUX SOF SEF MI XTH. destruct (errno_cell_any m) as [errv ERR]. pose proof sp_facts as SF. pose proof sp_atop as SA. unfold LO in *. unfold MFRAME, PMAIN, PSTAGE2_RET in FR.
    do 11 zstep. release_frame FR ST (usp0 + -48). zstep.
    replace (ret_pc (Z_to_bv 64 0x6c538)) with (Z_to_bv 64 0x6c538) by (symmetry; rpc).
    zstep.
    apply evt_done. eapply (pat_exit_intro code s LB) with (AB := usp0) (errv := errv);
      [exact ST| unfold PEXITU_STACK; lia| lia| lia| lia| clear -SF; Z.div_mod_to_equations; lia| exact RS| exact HP| exact CS| exact AUX| lia| exact ERR| exact SOF| exact SEF| exact MI| exact XTH].
  Qed.

  (* [comment removed for export] *)
  Lemma exit2_tail : forall (s : PState) (LB : list block) (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    stk usegs m (LO sp0) (usp0 + -128) ->
    RSTAT TID m -> RHEAP s LB m -> client_static s LB m -> rauxv_ok m usp0 ->
    stdout_file m (ps_so s) -> stderr_file m -> mem_inv usegs m -> XT m ->
    evt usegs (pat_exitU 2 s)
      (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x268e0) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros ST RS HP CS AUX SOF SEF MI XTH. destruct (errno_cell_any m) as [errv ERR]. pose proof sp_facts as SF. pose proof sp_atop as SA. unfold LO in *.
    zstep. zstep.
    apply evt_done. eapply (pat_exit_intro 2 s LB) with (AB := usp0) (errv := errv);
      [exact ST| unfold PEXITU_STACK; lia| lia| lia| lia| clear -SF; Z.div_mod_to_equations; lia| exact RS| exact HP| exact CS| exact AUX| lia| exact ERR| exact SOF| exact SEF| exact MI| exact XTH].
  Qed.
End EXITS.
End CANSEC1.
