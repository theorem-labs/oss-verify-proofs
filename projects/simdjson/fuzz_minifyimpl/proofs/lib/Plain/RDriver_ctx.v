(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree Startup_kit STRW_tac.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg F_syscalls StdioFiles PStartU.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface PU_iface PIosX_iface PAtexit_cells RDriver_iface RDriver_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require PIosKit PIosCert.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver PState ProgP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import RunDraw.
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
    rw_cells psegs mm (usp0 + -128)
      [CB 8 j8; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 (Z_to_bv 64 (envp_addr sp0 argv)); C8 (Z_to_bv 64 PMAIN);
       C8 (Z_to_bv 64 (argc argv)); C8 (Z_to_bv 64 (usp0 + 8)); C8 (Z_to_bv 64 PSTAGE2_RET)].

  Definition RSTAT (mm : mem) : Prop :=
    rw_cells psegs mm 0xe3960 [C8 (Z_to_bv 64 0xe3960); C8 (Z_to_bv 64 0xe3960); C8 (Z_to_bv 64 0xe3960); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 TID)]
    /\ rw_cells psegs mm 0x103c90 [C4 (Z_to_bv 64 0)]
    /\ rw_cells psegs mm 0xd0340 [C8 (Z_to_bv 64 0xca418); C8 (Z_to_bv 64 0xca410)]
    /\ rw_cells psegs mm 0xca410 [C8 (Z_to_bv 64 0x3b7e4)]
    /\ rw_cells psegs mm 0xd1778 [C1 (Z_to_bv 8 0)]
    /\ rw_cells psegs mm 0xd0198 [C8 (Z_to_bv 64 0xb346c); C8 (Z_to_bv 64 0)]      (* [comment removed for export] *)
    /\ rw_cells psegs mm 0x1041f8 [C8 (Z_to_bv 64 0)]
    /\ rw_cells psegs mm 0xd1610 [C8 (Z_to_bv 64 0xd1528)]                          (* [comment removed for export] *)
    /\ rw_cells psegs mm 0xd1700 [C8 (Z_to_bv 64 0xd1618)]
    /\ rw_cells psegs mm 0xd1520 [C8 (Z_to_bv 64 0xd1438)]
    /\ rw_cells psegs mm 0xd01b0 [C8 (Z_to_bv 64 0xd0150)]
    /\ rw_cells psegs mm 0xd0150 [C8 (Z_to_bv 64 0xd1438)]
    /\ rw_cells psegs mm 0xd1528 pstdin_cells                                         (* [comment removed for export] *)
    /\ ios_cells mm                                                                   (* [comment removed for export] *)
    /\ rw_cells psegs mm 0xd1368 [C8 (Z_to_bv 64 0xd1368)].                           (* [comment removed for export] *)

  Definition rstat_addr (a : Z) : Prop :=
    (0xe3960 <= a < 0xe3984) \/ (0x103c90 <= a < 0x103c94) \/ (0xd0340 <= a < 0xd0350) \/ (0xca410 <= a < 0xca418)
    \/ (0xd1778 <= a < 0xd1779) \/ (0xd0198 <= a < 0xd01a8) \/ (0xd1610 <= a < 0xd1618) \/ (0x1041f8 <= a < 0x104200)
    \/ (0xd1700 <= a < 0xd1708) \/ (0xd1520 <= a < 0xd1528) \/ (0xd01b0 <= a < 0xd01b8) \/ (0xd0150 <= a < 0xd0158)
    \/ (0xd1528 <= a < 0xd1610) \/ (0xd1368 <= a < 0xd1370) \/ ios_addr a.

  Ltac tr AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold rstat_addr, ios_addr; cbn in Ha; lia].

  Lemma RSTAT_agree : forall (P : Z -> Prop) m m', magree psegs P m m' -> (forall a, rstat_addr a -> P a) -> RSTAT m -> RSTAT m'.
  Proof.
    intros P m m' AG HP (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15). unfold RSTAT.
    split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3|]. split; [tr AG HP A4|].
    split; [tr AG HP A5|]. split; [tr AG HP A6|]. split; [tr AG HP A7|]. split; [tr AG HP A8|].
    split; [tr AG HP A9|]. split; [tr AG HP A10|]. split; [tr AG HP A11|]. split; [tr AG HP A12|].
    split; [unfold pstdin_cells in *; tr AG HP A13|].
    split; [eapply ios_cells_magree; [exact AG| | exact A14]; intros a Ha; apply HP; unfold rstat_addr; do 14 right; exact Ha|].
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

  Lemma RSTAT_munch : forall W m m', munch W m m' -> wmono psegs m m' -> (forall a, rstat_addr a -> outside W a) -> RSTAT m -> RSTAT m'.
  Proof.
    intros W m m' MU WM HW. apply (RSTAT_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha.
  Qed.
End CTX.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition stdout_addr (a : Z) : Prop := (0xd1618 <= a < 0xd1700) \/ (0x104618 <= a < 0x104a18).
Definition stderr_addr (a : Z) : Prop := 0xd1438 <= a < 0xd1520.
(* [comment removed for export] *)
Definition cstat_addr (a : Z) : Prop :=
  (0xca648 <= a < 0xca650) \/ (0xca658 <= a < 0xca660) \/ (0xd01c8 <= a < 0xd01d0) \/ (0xca510 <= a < 0xca518)      (* [comment removed for export] *)
  \/ (0xe17b0 <= a < 0xe1890)
  \/ (0x103a70 <= a < 0x103aa8) \/ (0x103b90 <= a < 0x103ba8).
(* [comment removed for export] *)
Definition trun0_addr (a : Z) : Prop :=
  (PINIT_FLAG <= a < PINIT_FLAG + 1) \/ (PGOT_FUZZ_INIT <= a < PGOT_FUZZ_INIT + 8) \/ cstat_addr a \/ (0xe1784 <= a < 0xe1785).

(* [comment removed for export] *)
Definition TRUN0 (m : mem) : Prop := trun_cells0 m /\ client_static0 m.

(* [comment removed for export] *)
Definition exit_table (s : PState) (LB : list block) (m : mem) : Prop := client_static s LB m \/ (ps_fa s = None /\ client_static0 m).
Lemma exit_table_of_static : forall s LB m, client_static s LB m -> exit_table s LB m.
Proof. intros s LB m H. left. exact H. Qed.
Lemma exit_table_of_static0 : forall s LB m, ps_fa s = None -> client_static0 m -> exit_table s LB m.
Proof. intros s LB m E H. right. split; [exact E| exact H]. Qed.

(* [comment removed for export] *)
Lemma client_static0_init : forall (m : mem),
  (forall a : word, (0xca000 <= bv_unsigned a < 0x105000)%Z -> outside (pcrt_written) (bv_unsigned a) -> m a = None) ->
  rw_cells psegs m 0x103a70 [CB 544 PIosCert.ios_exp3] -> client_static0 m.
Proof.
  intros m NONE ATX.
  pimg_chunk0 NONE m 0xca648 [C8 (Z_to_bv 64 0x4e108)] H1.
  pimg_chunk0 NONE m 0xca658 [C8 (Z_to_bv 64 0x3ecb4)] H2.      (* [comment removed for export] *)
  pimg_chunk0 NONE m 0xd01c8 [C8 (Z_to_bv 64 0xca418)] H3.
  pimg_chunk0 NONE m 0xca510 [C8 (Z_to_bv 64 0x11e1a)] H4.
  split; [unfold client_img; split; [exact H1| split; [exact H2| split; [exact H3| exact H4]]]|]. split.
  - intros a Ha. apply NONE; [lia| cbn [outside pcrt_written]; lia].
  - (* [comment removed for export] *)
    unfold patexit_main, patx_table. split; [| split; [| split; [| split]]].
    + eapply (PIosKit.rw_cells_sub_u psegs m 0x103a70 544 PIosCert.ios_exp3 0); [exact ATX| cbn; repeat split; exact I| vm_compute; reflexivity| cbn; lia].
    + eapply (PIosKit.rw_cells_sub_u psegs m 0x103a70 544 PIosCert.ios_exp3 16); [exact ATX| cbn; repeat split; exact I| vm_compute; reflexivity| cbn; lia].
    + eapply (PIosKit.rw_cells_sub_u psegs m 0x103a70 544 PIosCert.ios_exp3 48); [exact ATX| cbn; repeat split; exact I| vm_compute; reflexivity| cbn; lia].
    + eapply (PIosKit.rw_cells_sub_u psegs m 0x103a70 544 PIosCert.ios_exp3 288); [exact ATX| cbn; repeat split; exact I| vm_compute; reflexivity| cbn; lia].
    + eapply (PIosKit.rw_cells_sub_u psegs m 0x103a70 544 PIosCert.ios_exp3 304); [exact ATX| cbn; repeat split; exact I| vm_compute; reflexivity| cbn; lia].
Qed.

Lemma client_img_agree : forall (P : Z -> Prop) m m', magree psegs P m m' -> (forall a, cstat_addr a -> P a) -> client_img m -> client_img m'.
Proof.
  intros P m m' AG HP (C1 & C2 & C3 & C4).      (* [comment removed for export] *)
  repeat split; (eapply rw_cells_magree; [exact AG| eassumption| intros a Ha; apply HP; unfold cstat_addr; cbn in Ha; lia]).
Qed.
(* [comment removed for export] *)
Lemma patexit_agree : forall (P : Z -> Prop) n f1 a1 m m', magree psegs P m m' -> (forall a, cstat_addr a -> P a) -> patexit n f1 a1 m -> patexit n f1 a1 m'.
Proof.
  intros P n f1 a1 m m' AG HP PA. unfold patexit in *.
  eapply patx_table_agree; [exact AG| | exact PA]. intros a Ha. apply HP. unfold patx_addr in Ha. unfold cstat_addr. lia.
Qed.
Lemma patexit_main_agree_c : forall (P : Z -> Prop) m m', magree psegs P m m' -> (forall a, cstat_addr a -> P a) -> patexit_main m -> patexit_main m'.
Proof.
  intros P m m' AG HP PA. eapply patexit_main_agree; [exact AG| | exact PA]. intros a Ha. apply HP. unfold patx_addr in Ha. unfold cstat_addr. lia.
Qed.
Lemma client_static0_agree : forall (P : Z -> Prop) m m', magree psegs P m m' -> (forall a, cstat_addr a -> P a) -> client_static0 m -> client_static0 m'.
Proof.
  intros P m m' AG HP (CI & NO & PA).
  split; [exact (client_img_agree _ _ _ AG HP CI)|]. split; [| exact (patexit_main_agree_c _ _ _ AG HP PA)].
  intros a Ha. pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with (2^64) in RA.
  destruct (AG (bv_unsigned a) ltac:(lia) ltac:(apply HP; unfold cstat_addr; lia)) as [E _].
  rewrite wa_unsigned_id in E. rewrite E. exact (NO a Ha).
Qed.
(* [comment removed for export] *)
Lemma client_static_agree : forall (P : Z -> Prop) s LB m m', magree psegs P m m' -> (forall a, cstat_addr a -> P a) ->
  (forall p V a, ps_fa s = Some p -> In (p, V, 8) LB -> V <= a < V + 8 -> P a) -> client_static s LB m -> client_static s LB m'.
Proof.
  intros P s LB m m' AG HP HV [CI CS]. split; [exact (client_img_agree _ _ _ AG HP CI)|].
  destruct (ps_fa s) as [p|].
  - destruct CS as (V & HIN & C0 & C1 & C2 & C3 & PA). exists V. split; [exact HIN|].
    split; [eapply rw_cells_magree; [exact AG| exact C0| intros a Ha; cbn in Ha; apply (HV p V a eq_refl HIN); lia]|].
    unfold PVEC_GUARD, guard1, PVEC, PFALLBACK in *.
    split; [eapply rw_cells_magree; [exact AG| exact C1| intros a Ha; apply HP; unfold cstat_addr; cbn in Ha; lia]|].
    split; [eapply rw_cells_magree; [exact AG| exact C2| intros a Ha; apply HP; unfold cstat_addr; cbn in Ha; lia]|].
    split; [eapply rw_cells_magree; [exact AG| exact C3| intros a Ha; apply HP; unfold cstat_addr; cbn in Ha; lia]|].
    exact (patexit_agree _ _ _ _ _ _ AG HP PA).
  - destruct CS as [NO PA]. split; [| exact (patexit_agree _ _ _ _ _ _ AG HP PA)].
    intros a Ha. pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with (2^64) in RA.
    destruct (AG (bv_unsigned a) ltac:(lia) ltac:(apply HP; unfold cstat_addr; lia)) as [E _].
    rewrite wa_unsigned_id in E. rewrite E. exact (NO a Ha).
Qed.
(* [comment removed for export] *)
Lemma client_static_after_reg : forall (P : Z -> Prop) s LB m m', magree psegs P m m' ->
  (forall a, (0xca000 <= a < 0xd1000) \/ (0xe17b0 <= a < 0xe1890) -> P a) ->
  ps_fa s = None -> client_static0 m -> patexit 2 0 0 m' -> client_static s LB m'.
Proof.
  intros P s LB m m' AG HP E (CI & NO & _) PA. unfold client_static. rewrite E. split; [| split; [| exact PA]].
  - destruct CI as (C1 & C2 & C3 & C4).
    repeat split; (eapply rw_cells_magree; [exact AG| eassumption| intros a Ha; apply HP; cbn in Ha; lia]).
  - intros a Ha. pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with (2^64) in RA.
    destruct (AG (bv_unsigned a) ltac:(lia) ltac:(apply HP; lia)) as [E' _].
    rewrite wa_unsigned_id in E'. rewrite E'. exact (NO a Ha).
Qed.
(* [comment removed for export] *)
Lemma exit_table_agree : forall (P : Z -> Prop) s LB m m', magree psegs P m m' -> (forall a, cstat_addr a -> P a) ->
  (forall p V a, ps_fa s = Some p -> In (p, V, 8) LB -> V <= a < V + 8 -> P a) -> exit_table s LB m -> exit_table s LB m'.
Proof.
  intros P s LB m m' AG HP HV [CS|[E CS0]].
  - left. exact (client_static_agree _ _ _ _ _ AG HP HV CS).
  - right. split; [exact E| exact (client_static0_agree _ _ _ AG HP CS0)].
Qed.
(* [comment removed for export] *)
Lemma client_static_fa : forall s s' LB m, ps_fa s' = ps_fa s -> client_static s LB m -> client_static s' LB m.
Proof. intros s s' LB m E H. unfold client_static in *. rewrite E. exact H. Qed.
Lemma client_static_lb : forall s LB LB' m, (forall p V, ps_fa s = Some p -> In (p, V, 8) LB -> In (p, V, 8) LB') -> client_static s LB m -> client_static s LB' m.
Proof.
  intros s LB LB' m HL [CI CS]. split; [exact CI|].
  destruct (ps_fa s) as [p|]; [| exact CS]. destruct CS as (V & HIN & CS). exists V. split; [exact (HL p V eq_refl HIN)| exact CS].
Qed.

Lemma stdout_file_agree : forall (P : Z -> Prop) m m' so,
  magree psegs P m m' -> (forall a, stdout_addr a -> P a) -> stdout_file m so -> stdout_file m' so.
Proof.
  intros P m m' so AG HP (flags & mode & tail & bufbytes & F1 & F2 & F3 & F4 & F5 & F6).
  exists flags, mode, tail, bufbytes. split; [| split; [exact F2| split; [| split; [exact F4| split; [exact F5| exact F6]]]]].
  - eapply rw_cells_magree; [exact AG| exact F1|]. intros a Ha. apply HP. left. cbn in Ha. lia.
  - eapply rw_cells_magree; [exact AG| exact F3|]. intros a Ha. apply HP. right. cbn in Ha. lia.
Qed.

Lemma stderr_file0_agree : forall (P : Z -> Prop) m m',
  magree psegs P m m' -> (forall a, stderr_addr a -> P a) -> stderr_file0 m -> stderr_file0 m'.
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
Proof. intros s LB m p [_ CS] E. rewrite E in CS. destruct CS as (V & HIN & _). exists V. exact HIN. Qed.
Lemma client_static_sub : forall s LB LB' m, client_static s LB m -> List.NoDup (map blk_id LB) -> (forall b, In b LB' -> In b LB) ->
  (forall p, ps_fa s = Some p -> exists V, In (p, V, 8) LB') -> client_static s LB' m.
Proof.
  intros s LB LB' m [CI CS] ND SUB HIN. split; [exact CI|].
  destruct (ps_fa s) as [p|]; [| exact CS]. destruct CS as (V & HV & CS). destruct (HIN p eq_refl) as [V' HV'].
  destruct (blk_id_unique LB p V 8 V' 8 ND HV (SUB _ HV')) as [-> _]. exists V'. split; [exact HV'| exact CS].
Qed.

Lemma trun_cells0_agree : forall (P : Z -> Prop) m m',
  magree psegs P m m' -> (forall a, trun0_addr a -> P a) -> trun_cells0 m -> trun_cells0 m'.
Proof.
  intros P m m' AG HP (A1 & A2 & A3). unfold trun_cells0.
  Ltac tr2 AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold trun0_addr; cbn in Ha; lia].
  split; [tr2 AG HP A1|]. split; [tr2 AG HP A2|].
  eapply pincb_agree; [exact AG| | exact A3]. intros a Ha. apply HP. pose proof (pincb_addr_range a Ha). unfold trun0_addr. lia.
Qed.
(* [comment removed for export] *)
Lemma pincb_heap_pres : forall cb LB SP m m', rheap_pres LB SP m m' -> pincb cb m -> pincb cb m'.
Proof.
  intros cb LB SP m m' HP. apply (pincb_agree _ _ _ _ HP). intros a Ha. pose proof (pincb_addr_range a Ha). right; left.
  unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma pincb_of_trun0 : forall m, TRUN0 m -> pincb 0 m.
Proof. intros m [(_ & _ & T) _]. exact T. Qed.
Lemma TRUN0_agree : forall (P : Z -> Prop) m m',
  magree psegs P m m' -> (forall a, trun0_addr a -> P a) -> TRUN0 m -> TRUN0 m'.
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
  unfold trun0_addr, cstat_addr, PINIT_FLAG, PGOT_FUZZ_INIT, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma stdout_file_munch : forall W m m' so, munch W m m' -> wmono psegs m m' -> (forall a, stdout_addr a -> outside W a) -> stdout_file m so -> stdout_file m' so.
Proof. intros W m m' so MU WM HW. apply (stdout_file_agree _ _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma stderr_file0_munch : forall W m m', munch W m m' -> wmono psegs m m' -> (forall a, stderr_addr a -> outside W a) -> stderr_file0 m -> stderr_file0 m'.
Proof. intros W m m' MU WM HW. apply (stderr_file0_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma TRUN0_munch : forall W m m', munch W m m' -> wmono psegs m m' -> (forall a, trun0_addr a -> outside W a) -> TRUN0 m -> TRUN0 m'.
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

  Lemma sp_facts : 0x7fff80000000 <= usp0 <= 0x800000000000 /\ usp0 mod 16 = 0 /\ ATOP <= LO sp0 /\ LO sp0 + 8388608 = usp0 /\ 0x105000 <= LO sp0.
  Proof. destruct VSP as ((A & B & C) & HATOP & _). unfold LO, sp_window_lo, sp_window_hi, stack_max_size in *. repeat split; lia. Qed.
  Lemma sp_atop : ATOP = LO sp0.
  Proof. destruct VSP as (_ & HATOP & _). unfold LO. exact HATOP. Qed.

  (* [comment removed for export] *)
  Lemma pat_exit_intro : forall (code : Z) (s : PState) (LB : list block) (SP : Z) (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo AB : Z) (errv : word),
    stk psegs m lo SP -> lo <= SP - PEXITU_STACK -> ATOP <= lo -> 0x105000 <= lo -> 0 <= SP < 2^47 -> SP mod 16 = 0 ->
    RSTAT TID m -> RHEAP s LB m -> exit_table s LB m -> rauxv_ok m AB -> SP <= AB -> rw_cells psegs m RERRNO [C4 errv] ->
    stdout_file m (ps_so s) -> stderr_file m -> mem_inv psegs m ->
    pincb 0 m ->                                                     (* [comment removed for export] *)
    pat_exitU code s (MS (mkR ra (Z_to_bv 64 SP) gpv tpv t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 PEXIT) fc None m (seg_rom psegs)).
  Proof.
    intros until errv. intros ST LOS LOAT LOLO SPR SP16 (TD & EXL & GF & FA & FIN & GCX & OFL & SIN & SOU & SEU & _ & _ & SIF & IOS & DSO) HP CS AUX SPAB ERR SOF SEF MI CB.
    unfold pat_exitU. do 33 eexists. exists m, lo, TID, AB, (Z_to_bv 64 0xe3960), (Z_to_bv 64 0xe3960), (Z_to_bv 64 0xe3960), (Z_to_bv 64 0), errv, (Z_to_bv 64 0xd1368), LB.
    split; [reflexivity|]. rewrite !unsigned_lit by lia. split; [exact ST|]. split; [exact TD|]. split; [exact EXL|]. split; [exact GF|]. split; [exact FA|].
    split; [exact FIN|]. split; [exact GCX|]. split; [exact DSO|]. split; [exact OFL|]. split; [exact SIN|]. split; [exact SIF|]. split; [exact SOU|]. split; [exact SEU|].
    split; [exact SOF|]. split; [exact SEF|]. split; [exact IOS|]. split; [exact HP|]. split; [exact CS|]. split; [exact CB|]. split; [exact AUX|]. split; [exact SPAB|].
    split; [exact ERR|]. split; [exact MI|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HT|]. split; [exact LOS|]. split; [exact LOAT|]. split; [exact LOLO|]. split; [exact SP16|]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma main_return : forall (code : Z) (s : PState) (LB : list block) (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (j8 : list byte) (s7v s6v s5v s4v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    MFRAME sp0 argv m j8 s7v s6v s5v s4v ->
    stk psegs m (LO sp0) (usp0 + -128) ->
    RSTAT TID m -> RHEAP s LB m -> exit_table s LB m -> rauxv_ok m usp0 ->
    stdout_file m (ps_so s) -> stderr_file m -> mem_inv psegs m ->
    pincb 0 m ->                                                     (* [comment removed for export] *)
    evt psegs (pat_exitU code s)
      (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3ba70) fc None m (seg_rom psegs)).
  Proof.
    intros until m. intros FR ST RS HP CS AUX SOF SEF MI CB. destruct (errno_cell_any m) as [errv ERR]. pose proof sp_facts as SF. pose proof sp_atop as SA. unfold LO in *. unfold MFRAME, PMAIN, PSTAGE2_RET in FR.
    do 11 zstep. release_frame FR ST (usp0 + -48). zstep.
    replace (ret_pc (Z_to_bv 64 0xb3004)) with (Z_to_bv 64 0xb3004) by (symmetry; rpc).
    zstep.
    apply evt_done. eapply (pat_exit_intro code s LB) with (AB := usp0) (errv := errv);
      [exact ST| unfold PEXITU_STACK; lia| lia| lia| lia| clear -SF; Z.div_mod_to_equations; lia| exact RS| exact HP| exact CS| exact AUX| lia| exact ERR| exact SOF| exact SEF| exact MI| exact CB].
  Qed.

  (* [comment removed for export] *)
  Lemma exit2_tail : forall (s : PState) (LB : list block) (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    stk psegs m (LO sp0) (usp0 + -128) ->
    RSTAT TID m -> RHEAP s LB m -> exit_table s LB m -> rauxv_ok m usp0 ->
    stdout_file m (ps_so s) -> stderr_file m -> mem_inv psegs m ->
    pincb 0 m ->                                                     (* [comment removed for export] *)
    evt psegs (pat_exitU 2 s)
      (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3bafc) fc None m (seg_rom psegs)).
  Proof.
    intros until m. intros ST RS HP CS AUX SOF SEF MI CB. destruct (errno_cell_any m) as [errv ERR]. pose proof sp_facts as SF. pose proof sp_atop as SA. unfold LO in *.
    zstep. zstep.
    apply evt_done. eapply (pat_exit_intro 2 s LB) with (AB := usp0) (errv := errv);
      [exact ST| unfold PEXITU_STACK; lia| lia| lia| lia| clear -SF; Z.div_mod_to_equations; lia| exact RS| exact HP| exact CS| exact AUX| lia| exact ERR| exact SOF| exact SEF| exact MI| exact CB].
  Qed.
End EXITS.
End CANSEC1.
