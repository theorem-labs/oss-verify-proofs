(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRecs LeptSlots PFLib LeptNuma LeptNumaW LeptRoom LeptRoom9.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9LeptBase.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9Kit.
Import V9Kit.V9MemcpyBase. Import V9Kit.V9Memcpy.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9LeptEdge_iface V9LeptNumaSegs.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Numa.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V9Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma W_sok_blk : forall {fx : FPState} C A m md (p : word) (k a : Z) (n : nat), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + Z.of_nat n <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros fx C A m md p k a n CK HW L Hlo Hhi Hk. pose proof (u64_range p). rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
  destruct (blk_byte C A m md p k x CK HW L ltac:(lia)) as (_ & D & _). exact (D E).
Qed.

(* [comment removed for export] *)
Lemma calloc_blk : forall C (res : word) (n : Z), (0 <= n)%Z -> u res <> 0%Z -> (u res mod 16 = 0)%Z ->
  (u res + round16 n <= alloc_top (c_vm C))%Z -> (1 <= u res)%Z /\ (u res + n <= alloc_top (c_vm C))%Z /\ (u res mod 16 = 0)%Z.
Proof. intros C res n Hn Hnz Hal TOP. pose proof (u64_range res). pose proof (round16_ge n Hn). repeat split; [lia | lia | exact Hal]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem numaCreate_W : numaCreate_contract.
Proof.
  intros fx C A m md regs s n ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 Hn kR bR Hrm Hrk Hrb HK.
  unfold PC_numaCreate. replace (Z_to_bv 64 0x61688) with (0x61688 : word) by (apply bv_eq; reflexivity). unfold TP9 in H4.
  pose proof (numa_n0_range n Hn) as Hn0. set (na0 := numa_n0 n) in *.
  pose proof (alloc_margin_small (1 * 32) ltac:(lia)) as MG1. pose proof (alloc_margin_le (na0 * 4)) as MG2.
  pose proof (alloc_margin_ge (na0 * 4) ltac:(lia)) as MG3.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold NCR_STACK, CALLOC_STACK, ALLOC_STACK in Hlo. unfold RK_numa, RB_numa in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct (nc_A al_rom regs m s n ret ltac:(lia) ltac:(lia) Hn (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & AG1). fold na0 in Q8.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := NCF m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold NCF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (nccells_NCF m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1. rewrite <- H1 in CE1.
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x10a858) by (csr; reflexivity).
  replace (0xe2480 : word) with (Z_to_bv 64 0xe2480) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A M1 md r1 1 32 kR bR (Z_to_bv 64 0x616c0) (s - 32) S CK HW1 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           Hrm ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa Hroom1.
  replace (Z_to_bv 64 0x616c0) with (0x616c0 : word) by (apply bv_eq; reflexivity).
  assert (E8a : getr r2 8 = Z_to_bv 64 na0) by (csr; reflexivity).
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  destruct (calloc_blk C res (1 * 32) ltac:(lia) Hnz AL16 TOP) as (Gpa & TOPpa & ALpa).
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (pa := u res) in *. clearbody pa.
  rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO.
  assert (REC0 : RECat m1 pa (zflds [4; 4; 4; 4; 4; 4; 8]%nat)).
  { apply RECat_zero; [lia | cbn; lia | repeat constructor |]. cbn [flds_len zflds Nat.add]. intros i Hi.
    unfold at_ in ZERO. rewrite u_Z2bv in ZERO by lia. apply ZERO. lia. }
  destruct (nc_B al_rom r2 m1 pa na0 Hres E8a) as (r3 & RUN3 & P1 & P10 & P11 & P9 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
  assert (P4 : getr r3 4 = Z_to_bv 64 0x10a858) by (csr; reflexivity).
  assert (P2 : getr r3 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  replace (0xe2480 : word) with (Z_to_bv 64 0xe2480) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A1 m1 _ r3 na0 4 (kR - 1) (bR - alloc_margin (1 * 32)) (Z_to_bv 64 0x616d0) (s - 32) S CK HWa P10 P11 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(rewrite with_vmmaps_vmmaps; exact Hroom1) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) P1
           ltac:(red; apply bv_eq; reflexivity) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m2 vm2 r4 res2 HWb Hres2 CSb Hnz2 K0 K1 K00 KEQ ZERO2 AL16b TOPb PMb Hroom2. rewrite with_vmmaps_twice in HWb. rewrite with_vmmaps_twice.
  replace (Z_to_bv 64 0x616d0) with (0x616d0 : word) by (apply bv_eq; reflexivity).
  destruct (calloc_blk C res2 (na0 * 4) ltac:(lia) Hnz2 AL16b TOPb) as (Garr & TOParr & ALarr).
  assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
  set (arr := u res2) in *. clearbody arr.
  rewrite Eres2 in Hres2, K0, K1, K00, KEQ.
  assert (NE : arr <> pa) by (intros E; rewrite E in K0; rewrite K0 in L1; discriminate L1).
  assert (REC2 : RECat m2 pa (zflds [4; 4; 4; 4; 4; 4; 8]%nat)).
  { apply (RECat_POSTM C A1 (s - 32) m1 m2 (Z_to_bv 64 pa) 32 _ _ REC0 PMb L1); rewrite u_Z2bv by lia; [lia | cbn; lia]. }
  assert (SOKp2 : store_ok SEGS m2 (Z_to_bv 64 pa) 32 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m2 x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined m2 pa _ x REC2 ltac:(cbn; lia) E). }
  assert (CE2 : nccells m2 s (getr regs 1) (getr regs 8) (getr regs 9)).
  { destruct CE1 as (C1 & C2 & C3). unfold nccells.
    rewrite !(FRM_rdn16 C (s - 32) m1 m2 _ _ CK (proj1 PMb)) by lia.
    rewrite !(FRM_rdn16 C (s - 32) M1 m1 _ _ CK (proj1 PMa)) by lia. repeat split; assumption. }
  assert (PMb' : POSTM C A s m m2).
  { eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1 _ _ _ SUBa). eapply POSTM_mono; [|exact PMb]. lia. }
  assert (F2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (F9 : getr r4 9 = Z_to_bv 64 pa) by (csr; reflexivity).
  assert (F8 : getr r4 8 = Z_to_bv 64 na0) by (csr; reflexivity).
  destruct (nc_C al_rom r4 m2 s pa na0 arr ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (mod16_mod8 _ ALpa) Hret SOKp2 ltac:(lia)
              ltac:(rewrite <- H1; exact CE2) F2 Hres2 F9 F8) as (r5 & RUN5 & V2 & V1 & V10 & V8 & V9 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN5 |].
  set (M4 := NCH m2 pa na0 arr).
  assert (SUBb : sub_live A A2) by (eapply sub_live_trans; [exact SUBa | eapply sub_live_new; eassumption]).
  assert (Lpa2 : live A2 (Z_to_bv 64 pa) = Some 32%Z) by (rewrite (KEQ _ (zneq_w pa arr ltac:(lia) ltac:(lia) (not_eq_sym NE))); exact L1).
  assert (WP4 : W C A2 M4 (with_vmmaps vm2 md) /\ POSTM C A s m M4).
  { subst M4. unfold NCH.
    do 6 (apply (WP_blk C A A2 m _ _ (Z_to_bv 64 pa) _ 32); [exact CK | | exact Lpa2 | exact L0 | exact L00 | exact SUBb | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
    split; [exact HWb | exact PMb']. }
  destruct WP4 as [HW4 PM4].
  assert (REC4 : RECat M4 pa (numa_flds na0 0 1 arr)).
  { subst M4. unfold NCH, numa_flds.
    eapply (REC_wr' _ _ [(4%nat, na0); (4%nat, 0%Z); (4%nat, 1%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, arr)] _ 4 4);
      [ | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ].
    eapply (REC_wr' _ _ [(4%nat, na0); (4%nat, 0%Z); (4%nat, 1%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, arr)] _ 3 4);
      [ | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ].
    eapply (REC_wr' _ _ [(4%nat, na0); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, arr)] _ 2 4);
      [ | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ].
    eapply (REC_wr' _ _ [(4%nat, na0); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, arr)] _ 1 4);
      [ | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ].
    eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, arr)] _ 0 4);
      [ | cbn; lia | cbn; lia | reflexivity | cbn [fld_off Z.of_nat]; f_equal; lia | reflexivity ].
    eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z)] _ 6 8);
      [ exact REC2 | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ]. }
  rewrite H1 in *. apply (HK A2 M4 vm2 r5 pa arr HW4).
  - apply cs_kept_intro; csr; try reflexivity. all: rewrite ?V8, ?V9; csr; reflexivity.
  - exact PM4.
  - exact V10.
  - split; [|split; [exact L0 | split]].
    + split; [exact REC4|]. split; [exact ALpa|]. split; [lia|]. split; [exact ALarr|]. split; [exact NE|].
      split; [unfold NUMA_NMAX; lia|]. split; [lia|]. split; [exact Lpa2|]. split; [exact L00|].
      split; [replace (4 * na0)%Z with (na0 * 4)%Z by lia; exact K1 | exact K00].
    + rewrite <- (LEQ _ (zneq_w arr pa ltac:(lia) ltac:(lia) NE)). exact K0.
    + intros q N1 N2. rewrite (KEQ q N2). exact (LEQ q N1).
  - apply (aroom_mono A2 vm2 _ _ _ _ Hroom2); lia.
Qed.

(* [comment removed for export] *)
Lemma blk_apart : forall {fx : FPState} C A m md (p q : word) (n k : Z), Cok C -> W C A m md ->
  live A p = Some n -> live A q = Some k -> p <> q -> (0 <= n)%Z -> (0 <= k)%Z ->
  (u p + n <= u q \/ u q + k <= u p)%Z.
Proof.
  intros fx C A m md p q n k CK HW Lp Lq NE Hn Hk.
  destruct (ai_live_disjoint A m (m_vmmaps md) p n q k (w_inv _ _ _ _ HW) Lp Lq NE) as [X|X];
    [left; pose proof (round16_ge n Hn); lia | right; pose proof (round16_ge k Hk); lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem numaDestroy_W : numaDestroy_contract.
Proof.
  intros fx C A m md regs s pp na nalloc n arr ret S CK HW H2 Hs16 Hlo Hpp Hpphi ALpp H1 Hret H4 H10 Rpp NA HK.
  unfold PC_numaDestroy. replace (Z_to_bv 64 0x61794) with (0x61794 : word) by (apply bv_eq; reflexivity). unfold TP9 in H4.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold NDS_STACK, ALLOC_STACK in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof NA as (R & Hal & Harr & Hala & NEan & Hnal & Hn & L1 & L01 & L2 & L02).
  destruct (blk_range C A m md (Z_to_bv 64 na) 32 CK HW L1 ltac:(lia)) as [Gna TOPna].
  pose proof (NUMA_wf m na nalloc n 1 arr R) as (_ & _ & _ & Warr & Wna0 & Wna).
  rewrite u_Z2bv in Gna, TOPna by lia.
  destruct (blk_range C A m md (Z_to_bv 64 arr) (4 * nalloc) CK HW L2 ltac:(lia)) as [Garr TOParr]. rewrite u_Z2bv in Garr, TOParr by lia.
  destruct (nd_A al_rom regs m s pp na arr ret ltac:(lia) Hpp ltac:(lia) ltac:(lia) ltac:(lia) Hal ltac:(lia) ALpp
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia))
              (W_sok_blk C A m md (Z_to_bv 64 na) 32 (na + 8) 4 CK HW L1 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia))
              Rpp (NUMA_rd_rc SEGS m na nalloc n 1 arr R) (NUMA_rd_arr SEGS m na nalloc n 1 arr R) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M0 := NDF m s ret regs).
  set (M1 := wbytes M0 _ _).
  assert (WP0 : W C A M0 md /\ POSTM C A s m M0) by (subst M0; unfold NDF; wp_win CK).
  destruct WP0 as [HW0 PM0].
  assert (HW1 : W C A M1 md).
  { subst M1. apply (W_store_blk C A M0 md (Z_to_bv 64 na) _ 32 _ CK HW0 L1 L01); [rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
  assert (F1 : FRM C s m M1).
  { eapply FRM_trans; [exact (proj1 PM0)|]. subst M1.
    refine (proj1 (POSTM_blk C (c_A0 C) A M0 md (Z_to_bv 64 na) _ 32 _ s CK HW0 L1 L01 (W_sub0 _ _ _ _ HW0) _ _));
      [rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
  assert (K1 : forall q k i, live A q = Some k -> q <> Z_to_bv 64 na -> (0 <= i < k)%Z -> M1 (at_ q i) = m (at_ q i)).
  { intros q k i Lq NEq Hi. rewrite <- (proj2 PM0 q k i Lq Hi). subst M1.
    pose proof (blk_apart C A m md _ _ _ _ CK HW Lq L1 NEq ltac:(lia) ltac:(lia)) as D. rewrite u_Z2bv in D by lia.
    destruct (blk_range C A m md q k CK HW Lq ltac:(lia)) as [Gq TOPq].
    apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; [cbn; lia|]. unfold at_. pose proof (u64_range q). rewrite u_Z2bv by lia. cbn. lia. }
  pose proof (ndcells_NDF m s ret regs ltac:(lia) ltac:(lia)) as CE0. fold M0 in CE0.
  assert (CE1 : ndcells M1 s ret (getr regs 8) (getr regs 9)).
  { destruct CE0 as (C1 & C2 & C3). unfold ndcells. subst M1.
    rewrite !rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). repeat split; assumption. }
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x10a858) by (csr; reflexivity).
  (* [comment removed for export] *)
  replace (0xe25b8 : word) with (Z_to_bv 64 0xe25b8) by (apply bv_eq; reflexivity).
  rewrite <- (with_vmmaps_same md) in HW1 |- *.
  apply (W_free16 C A M1 _ r1 (Z_to_bv 64 arr) (Z_to_bv 64 0x617e4) (4 * nalloc) (s - 32) S CK HW1 Q10 L2 L02 Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 HWa CSa La LEQa PMa HRTa. rewrite ?with_vmmaps_twice in HWa |- *.
  replace (Z_to_bv 64 0x617e4) with (0x617e4 : word) by (apply bv_eq; reflexivity).
  assert (NEna : Z_to_bv 64 na <> Z_to_bv 64 arr) by (apply zneq_w; [lia | lia |]; intros E; apply NEan; symmetry; exact E).
  assert (L1a : live A1 (Z_to_bv 64 na) = Some 32%Z) by (rewrite (LEQa _ NEna); exact L1).
  assert (E8 : getr r2 8 = Z_to_bv 64 na) by (csr; reflexivity).
  destruct (nd_B al_rom r2 m1 na E8) as (r3 & RUN3 & P1 & P10 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  assert (P4 : getr r3 4 = Z_to_bv 64 0x10a858) by (csr; reflexivity).
  assert (P2 : getr r3 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  (* [comment removed for export] *)
  replace (0xe25b8 : word) with (Z_to_bv 64 0xe25b8) by (apply bv_eq; reflexivity).
  apply (W_free16 C A1 m1 _ r3 (Z_to_bv 64 na) (Z_to_bv 64 0x617ec) 32 (s - 32) S CK HWa P10 L1a L01 P1
           ltac:(red; apply bv_eq; reflexivity) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m2 vm2 r4 HWb CSb Lb LEQb PMb HRTb. rewrite ?with_vmmaps_twice in HWb |- *.
  replace (Z_to_bv 64 0x617ec) with (0x617ec : word) by (apply bv_eq; reflexivity).
  assert (Z2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (Z9 : getr r4 9 = Z_to_bv 64 pp) by (csr; reflexivity).
  assert (FR12 : FRM C s m m2).
  { eapply FRM_trans; [exact F1|]. eapply FRM_trans; [eapply FRM_mono; [exact (proj1 PMa) | lia] | eapply FRM_mono; [exact (proj1 PMb) | lia]]. }
  assert (CE2 : ndcells m2 s ret (getr regs 8) (getr regs 9)).
  { destruct CE1 as (C1 & C2 & C3). unfold ndcells.
    rewrite !(FRM_rdn16 C (s - 32) m1 m2 _ _ CK (proj1 PMb)) by lia.
    rewrite !(FRM_rdn16 C (s - 32) M1 m1 _ _ CK (proj1 PMa)) by lia. repeat split; assumption. }
  destruct (nd_C al_rom r4 m2 s pp ret (getr regs 8) (getr regs 9) ltac:(lia) Hpp ltac:(lia) Hret
              (W_sok_win C A2 m2 _ pp 8 CK HWb ltac:(lia) ltac:(cbn; lia)) CE2 Z2 Z9) as (r5 & RUN5 & V2 & V1 & V8 & V9 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN5 |].
  set (M3 := wbytes m2 _ _).
  assert (WP3 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C A2 (pp + 8) m2 M3) by (subst M3; wp_win CK).
  destruct WP3 as [HW3 PM3].
  assert (La2 : live A2 (Z_to_bv 64 arr) = None) by (rewrite (LEQb _ (not_eq_sym NEna)); exact La).
  apply (HK A2 M3 vm2 r5 HW3).
  - apply cs_kept_intro; csr; try reflexivity. all: rewrite ?V8, ?V9; csr; reflexivity.
  - exact Lb.
  - exact La2.
  - intros q N1 N2. rewrite (LEQb q N1). exact (LEQa q N2).
  - split; [eapply FRM_trans; [eapply FRM_mono; [exact FR12 | lia] | exact (proj1 PM3)]|].
    intros q k i Lq Hi.
    assert (N1 : q <> Z_to_bv 64 na) by (intros ->; congruence).
    assert (N2 : q <> Z_to_bv 64 arr) by (intros ->; congruence).
    assert (Lq1 : live A1 q = Some k) by (rewrite <- (LEQb q N1); exact Lq).
    assert (Lq0 : live A q = Some k) by (rewrite <- (LEQa q N2); exact Lq1).
    rewrite (proj2 PM3 q k i Lq Hi). rewrite (proj2 PMb q k i Lq Hi). rewrite (proj2 PMa q k i Lq1 Hi).
    exact (K1 q k i Lq0 N1 Hi).
  - subst M3. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
  - apply (roomtr_trans A (m_vmmaps md) A1 vm1 A2 vm2 0 0 0 0 HRTa (roomtr_wv _ _ _ _ _ _ _ HRTb)); lia.
Qed.

(* [comment removed for export] *)
Lemma blk_rdn : forall {fx : FPState} C A m md (p : Z) (n : Z) (k : nat), Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some n ->
  (0 <= p)%Z -> (p + n < 2 ^ 64)%Z -> (Z.of_nat k <= n)%Z -> exists bs, rdn SEGS m (Z_to_bv 64 p) k = Some bs /\ length bs = k.
Proof.
  intros fx C A m md p n k CK HW L Hp Hpn Hk. apply rdn_defined; [lia | lia |]. intros i Hi.
  destruct (blk_byte C A m _ (Z_to_bv 64 p) _ (Z_to_bv 64 (p + i)) CK HW L ltac:(rewrite !u_Z2bv by lia; lia)) as (_ & D & _). exact D.
Qed.

Ltac in_kept := unfold callee_kept; cbn [In]; repeat (first [left; reflexivity | right]).

(* [comment removed for export] *)
Lemma rncells_ext : forall {fx : FPState} M M' s ret s0v s1v s2v s3v, (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rncells M s ret s0v s1v s2v s3v -> (forall x : word, (s - 48 <= u x < s)%Z -> M' x = M x) -> rncells M' s ret s0v s1v s2v s3v.
Proof.
  intros fx M M' s ret s0v s1v s2v s3v Hs Hs64 (C1 & C2 & C3 & C4 & C5) E.
  unfold rncells. repeat split; [rewrite <- C1 | rewrite <- C2 | rewrite <- C3 | rewrite <- C4 | rewrite <- C5];
    (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]; intros x Hx; cbn in Hx; apply E; lia).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem reallocNew_W : forall {fx : FPState} C Ar A m md regs (s pp ind old new : Z) (q : word) (k : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + RNW_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x10a858 ->
  getr regs 10 = Z_to_bv 64 pp -> getr regs 11 = Z_to_bv 64 old -> getr regs 12 = Z_to_bv 64 new ->
  live A q = Some k -> live (c_A0 C) q = None -> live Ar q = None -> (u q <= pp)%Z -> (pp + 8 <= u q + k)%Z -> (pp mod 8 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 ind) ->
  live A (Z_to_bv 64 ind) = Some old -> live (c_A0 C) (Z_to_bv 64 ind) = None -> live Ar (Z_to_bv 64 ind) = None -> q <> Z_to_bv 64 ind ->
  (1 <= ind < 2 ^ 64)%Z -> (1 <= old < new)%Z -> (new <= ROOM_NMAX)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (1 <= kR)%Z -> (alloc_margin (1 * new) <= bR)%Z ->
  (forall A' m' vm' regs' (nb : Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C Ar s m m' ->
     getr regs' 10 = Z_to_bv 64 nb ->
     (1 <= nb)%Z -> (nb mod 16 = 0)%Z -> (nb + new <= alloc_top (c_vm C))%Z ->
     live A (Z_to_bv 64 nb) = None -> live A' (Z_to_bv 64 nb) = Some new -> live (c_A0 C) (Z_to_bv 64 nb) = None ->
     live A' (Z_to_bv 64 ind) = None ->
     (forall x, x <> Z_to_bv 64 ind -> x <> Z_to_bv 64 nb -> live A' x = live A x) ->
     rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     (forall b kb i, live A b = Some kb -> b <> Z_to_bv 64 ind -> (0 <= i < kb)%Z -> ~ inslot pp (at_ b i) -> m' (at_ b i) = m (at_ b i)) ->
     aroom A' vm' (kR - 1) (bR - alloc_margin (1 * new)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x5e334 : word) m al_rom) md) S.
Proof.
  intros fx C Ar A m md regs s pp ind old new q k ret S CK HW SUBr H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Lq Lq0 LqR Hq1 Hq2 ALpp Rpp Li Li0 LiR NEqi
         Hind Hold Hnew kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold RNW_STACK, CALLOC_STACK, ALLOC_STACK in Hlo. unfold ROOM_NMAX in Hnew.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct (blk_range C A m md q k CK HW Lq ltac:(lia)) as [Gq TOPq].
  destruct (blk_range C A m md (Z_to_bv 64 ind) old CK HW Li ltac:(lia)) as [Gi TOPi]. rewrite u_Z2bv in Gi, TOPi by lia.
  destruct (rn_A al_rom regs m s pp ind old new ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALpp
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & Q18 & Q19 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := RNF m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold RNF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (rncells_RNF m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x10a858) by (csr; reflexivity).
  (* [comment removed for export] *)
  replace (0xe2480 : word) with (Z_to_bv 64 0xe2480) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A M1 md r1 1 new kR bR (Z_to_bv 64 0x5e378) (s - 48) S CK HW1 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           Hrm ltac:(lia) Hrb ltac:(unfold ROOM_NMAX; lia) Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa Hroom1.
  replace (Z_to_bv 64 0x5e378) with (0x5e378 : word) by (apply bv_eq; reflexivity).
  destruct (calloc_blk C res (1 * new) ltac:(lia) Hnz AL16 TOP) as (Gnb & TOPnb & ALnb).
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (nb := u res) in *. clearbody nb.
  rewrite Eres in Hres, L0, L1, L00, LEQ. clear ZERO.
  replace (1 * new)%Z with new in L1, TOPnb by lia.
  assert (NEin : Z_to_bv 64 ind <> Z_to_bv 64 nb) by (intros E; rewrite E in Li; rewrite Li in L0; discriminate).
  assert (NEqn : q <> Z_to_bv 64 nb) by (intros E; rewrite E in Lq; rewrite Lq in L0; discriminate).
  assert (Li1 : live A1 (Z_to_bv 64 ind) = Some old) by (rewrite (LEQ _ NEin); exact Li).
  assert (Lq1 : live A1 q = Some k) by (rewrite (LEQ _ NEqn); exact Lq).
  assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
  assert (SUBr1 : sub_live Ar A1) by (eapply sub_live_trans; eassumption).
  assert (LnbR : live Ar (Z_to_bv 64 nb) = None).
  { destruct (live Ar (Z_to_bv 64 nb)) as [z|] eqn:E; [|reflexivity]. rewrite (SUBr _ _ E) in L0. discriminate. }
  assert (PMr1 : POSTM C Ar s m m1).
  { apply (POSTM_sub C Ar A _ _ _ SUBr). eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]. }
  assert (CEa : rncells m1 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { destruct CE1 as (C1 & C2 & C3 & C4 & C5). unfold rncells.
    rewrite !(FRM_rdn16 C (s - 48) M1 m1 _ _ CK (proj1 PMa)) by lia. repeat split; assumption. }
  assert (E9 : getr r2 9 = Z_to_bv 64 ind) by (csr; reflexivity).
  assert (E18 : getr r2 18 = Z_to_bv 64 old) by (csr; reflexivity).
  assert (E19 : getr r2 19 = Z_to_bv 64 new) by (csr; reflexivity).
  destruct (rn_B al_rom r2 m1 ind old new nb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hres E9 E18 E19) as (r3 & RUN3 & P1 & P10 & P11 & P12 & P19 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  (* [comment removed for export] *)
  destruct (blk_rdn C A1 m1 _ ind old (Z.to_nat old) CK HWa Li1 ltac:(lia) ltac:(lia) ltac:(lia)) as (bs & Hsrc & Hlen).
  pose proof (blk_apart C A1 m1 _ _ _ _ _ CK HWa Li1 L1 NEin ltac:(lia) ltac:(lia)) as APin. rewrite !u_Z2bv in APin by lia.
  assert (HOKm : mcH m1 (Z_to_bv 64 nb) (Z_to_bv 64 ind) old bs).
  { constructor; rewrite ?u_Z2bv by lia; [lia | exact Hlen | rewrite Hlen; exact Hsrc | rewrite Hlen | lia | lia | lia].
    exact (W_sok_blk C A1 m1 _ (Z_to_bv 64 nb) new nb (Z.to_nat old) CK HWa L1 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia)). }
  destruct (ref_memcpy m1 _ _ old bs al_rom HOKm r3 (Z_to_bv 64 0x5e398) ltac:(red; apply bv_eq; reflexivity) P1 P10 P11 P12) as (r4 & RUN4 & KP4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN4 |].
  replace (Z_to_bv 64 0x5e398) with (0x5e398 : word) by (apply bv_eq; reflexivity).
  set (M2 := wbytes m1 (Z_to_bv 64 nb) bs) in *.
  pose proof (keeps_cs_kept _ _ KP4) as CS4.
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C Ar s m M2).
  { subst M2. apply (WP_blk C Ar A1 m m1 _ (Z_to_bv 64 nb) (Z_to_bv 64 nb) new bs s CK (conj HWa PMr1) L1 LnbR L00 SUBr1); rewrite ?u_Z2bv by lia; [lia | rewrite Hlen; lia]. }
  destruct WP2 as [HW2 PM2].
  assert (OUT2 : forall x : word, ~ (nb <= u x < nb + old)%Z -> M2 x = m1 x).
  { intros x Hx. subst M2. apply wbytes_outside; rewrite Hlen, u_Z2bv by lia; lia. }
  assert (CE2 : rncells M2 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { apply (rncells_ext m1 M2 s); [lia | lia | exact CEa |]. intros x Hx. apply OUT2. lia. }
  assert (K9 : getr r4 9 = Z_to_bv 64 ind) by (csr; reflexivity).
  destruct (rn_C al_rom r4 M2 ind K9) as (r5 & RUN5 & X1 & X10 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN5 |].
  assert (X4 : getr r5 4 = Z_to_bv 64 0x10a858) by (csr; reflexivity).
  assert (X2 : getr r5 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  (* [comment removed for export] *)
  replace (0xe25b8 : word) with (Z_to_bv 64 0xe25b8) by (apply bv_eq; reflexivity).
  apply (W_free16 C A1 M2 _ r5 (Z_to_bv 64 ind) (Z_to_bv 64 0x5e3a0) old (s - 48) S CK HW2 X10 Li1 Li0 X1
           ltac:(red; apply bv_eq; reflexivity) X4 X2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m2 vm2 r6 HWb CSb Lib LEQb PMb HRTb. rewrite ?with_vmmaps_twice in HWb |- *.
  replace (Z_to_bv 64 0x5e3a0) with (0x5e3a0 : word) by (apply bv_eq; reflexivity).
  assert (Lq2 : live A2 q = Some k) by (rewrite (LEQb _ NEqi); exact Lq1).
  assert (Lnb2 : live A2 (Z_to_bv 64 nb) = Some new) by (rewrite (LEQb _ (not_eq_sym NEin)); exact L1).
  assert (SUBr2 : sub_live Ar A2).
  { intros x kx Lx. assert (NEx : x <> Z_to_bv 64 ind) by (intros ->; congruence). rewrite (LEQb x NEx). exact (SUBr1 x kx Lx). }
  assert (SUB21 : sub_live A2 A1).
  { intros x kx Lx. destruct (bv_eq_dec _ x (Z_to_bv 64 ind)) as [->|NE]; [rewrite Lib in Lx; discriminate | rewrite <- (LEQb x NE); exact Lx]. }
  assert (PMr2 : POSTM C Ar s m m2).
  { eapply POSTM_trans; [exact PM2|]. apply (POSTM_sub C Ar A2 _ _ _ SUBr2). eapply POSTM_mono; [|exact PMb]. lia. }
  assert (CEb : rncells m2 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { destruct CE2 as (C1 & C2 & C3 & C4 & C5). unfold rncells.
    rewrite !(FRM_rdn16 C (s - 48) M2 m2 _ _ CK (proj1 PMb)) by lia. repeat split; assumption. }
  assert (Y2 : getr r6 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  assert (Y8 : getr r6 8 = Z_to_bv 64 pp) by (csr; reflexivity).
  assert (Y19 : getr r6 19 = Z_to_bv 64 nb) by (csr; reflexivity).
  destruct (rn_D al_rom r6 m2 s pp nb ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret
              (W_sok_blk C A2 m2 _ q k pp 8 CK HWb Lq2 Hq1 ltac:(cbn; lia) ltac:(lia)) CEb Y2 Y8 Y19)
    as (r7 & RUN7 & V2 & V1 & V10 & V8 & V9 & V18 & V19 & AG7).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN7 |].
  set (M3 := wbytes m2 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (WP3 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C Ar s m M3).
  { subst M3. apply (WP_blk C Ar A2 m m2 _ q (Z_to_bv 64 pp) k _ s CK (conj HWb PMr2) Lq2 LqR Lq0 SUBr2); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; [lia | cbn; lia]. }
  destruct WP3 as [HW3 PM3].
  apply (HK A2 M3 vm2 r7 nb HW3).
  - assert (REST : forall x, In x [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r7 x = getr regs x).
    { intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]). destruct Hx. }
    apply cs_kept_intro; first [ rewrite V2; symmetry; exact H2 | exact V8 | exact V9 | exact V18 | exact V19 | apply REST; in_lit ].
  - exact PM3.
  - exact V10.
  - exact Gnb.
  - exact ALnb.
  - exact TOPnb.
  - exact L0.
  - exact Lnb2.
  - exact L00.
  - exact Lib.
  - intros x N1 N2. rewrite (LEQb x N1). exact (LEQ x N2).
  - subst M3. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
  - intros b kb i Lb NEb Hi NS.
    assert (NEbn : b <> Z_to_bv 64 nb) by (intros ->; congruence).
    assert (Lb1 : live A1 b = Some kb) by (rewrite (LEQ _ NEbn); exact Lb).
    assert (Lb2 : live A2 b = Some kb) by (rewrite (LEQb _ NEb); exact Lb1).
    destruct (blk_range C A1 m1 _ b kb CK HWa Lb1 ltac:(lia)) as [Gb TOPb].
    assert (Rb : (u b <= u (at_ b i) < u b + kb)%Z) by (unfold at_; pose proof (u64_range b); rewrite u_Z2bv by lia; lia).
    subst M3. rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; unfold inslot in NS; cbn; lia).
    rewrite (proj2 PMb b kb i Lb2 Hi).
    pose proof (blk_apart C A1 m1 _ _ _ _ _ CK HWa Lb1 L1 NEbn ltac:(lia) ltac:(lia)) as APb. rewrite u_Z2bv in APb by lia.
    rewrite OUT2 by lia.
    rewrite (proj2 PMa b kb i Lb Hi). exact (proj2 PM1 b kb i Lb Hi).
  - pose proof (roomtr_wv _ _ _ _ _ _ _ HRTb (kR - 1)%Z (bR - alloc_margin (1 * new))%Z Hroom1 ltac:(lia) ltac:(lia)) as X.
    rewrite !Z.sub_0_r in X. exact X.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem numaExtendArray_W : numaExtendArray_contract.
Proof.
  intros fx C Ar A m md regs s na nalloc n arr ret S CK HW SUBr H2 Hs16 Hlo Hhi H1 Hret H4 H10 NA Hmax LnaR LarrR kR bR Hrm Hrk Hrb HK.
  unfold PC_numaExtendArray. replace (Z_to_bv 64 0x619bc) with (0x619bc : word) by (apply bv_eq; reflexivity). unfold TP9 in H4.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK in Hlo. unfold NUMA_NMAX in Hmax.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof NA as (R & Hal & Harr & Hala & NEan & Hnal & Hn & L1 & L01 & L2 & L02).
  destruct (blk_range C A m md (Z_to_bv 64 na) 32 CK HW L1 ltac:(lia)) as [Gna TOPna].
  pose proof (NUMA_wf m na nalloc n 1 arr R) as (_ & _ & _ & Warr & Wna0 & Wna).
  rewrite u_Z2bv in Gna, TOPna by lia.
  destruct (blk_range C A m md (Z_to_bv 64 arr) (4 * nalloc) CK HW L2 ltac:(lia)) as [Garr TOParr]. rewrite u_Z2bv in Garr, TOParr by lia.
  pose proof (RB_numagrow_margin nalloc ltac:(lia)) as MG.
  destruct (ne_A al_rom regs m s na nalloc ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (mod16_mod8 _ Hal)
              (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) (NUMA_rd_nalloc SEGS m na nalloc n 1 arr R) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := NEF m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold NEF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (necells_NEF m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (R1 : RECat M1 na (numa_flds nalloc n 1 arr)).
  { apply (RECat_POSTM C A s m M1 (Z_to_bv 64 na) 32 _ _ R PM1 L1); rewrite u_Z2bv by lia; [lia | cbn; lia]. }
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x10a858) by (csr; reflexivity).
  assert (NEna : Z_to_bv 64 na <> Z_to_bv 64 arr) by (apply zneq_w; [lia | lia |]; intros E; apply NEan; symmetry; exact E).
  apply (reallocNew_W C Ar A M1 md r1 (s - 16) (na + 24) arr (4 * nalloc) (8 * nalloc) (Z_to_bv 64 na) 32 (Z_to_bv 64 0x61a54) S CK HW1 SUBr Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold RNW_STACK, CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)
           Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 L1 L01 LnaR ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia)
           (mod16_plus_mod8 na 24 Hal eq_refl)
           (NUMA_rd_arr SEGS M1 na nalloc n 1 arr R1) L2 L02 LarrR NEna ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia)
           kR bR Hrm Hrk ltac:(replace (1 * (8 * nalloc))%Z with (8 * nalloc)%Z by lia; lia)).
  intros A2 m2 vm2 r2 nb HW2 CS2 PM2 R10 Gnb ALnb TOPnb LnbA Lnb2 Lnb0 Larr2 LEQ2 RD0 KEEP Hroom2.
  replace (Z_to_bv 64 0x61a54) with (0x61a54 : word) by (apply bv_eq; reflexivity).
  assert (NEnn : Z_to_bv 64 na <> Z_to_bv 64 nb) by (intros E; rewrite E in L1; rewrite L1 in LnbA; discriminate).
  assert (Lna2 : live A2 (Z_to_bv 64 na) = Some 32%Z) by (rewrite (LEQ2 _ NEna NEnn); exact L1).
  assert (SUBr2 : sub_live Ar A2).
  { intros x kx Lx. assert (N1 : x <> Z_to_bv 64 arr) by (intros ->; congruence).
    assert (N2 : x <> Z_to_bv 64 nb) by (intros ->; rewrite (SUBr _ _ Lx) in LnbA; discriminate).
    rewrite (LEQ2 x N1 N2). exact (SUBr x kx Lx). }
  (* [comment removed for export] *)
  assert (R2 : RECat m2 na (numa_flds nalloc n 1 0)).
  { change (numa_flds nalloc n 1 0) with (fld_set (numa_flds nalloc n 1 arr) 6 0).
    apply (RECat_set_rdn SEGS M1 m2 na _ 6 0 R1); [cbn; lia | cbn; lia | | | exact RD0].
    - intros x Hx Hoff. cbn in Hx, Hoff.
      assert (E : at_ (Z_to_bv 64 na) (u x - na) = x) by (pose proof (u64_range x); unfold at_; apply bv_eq; rewrite (u_Z2bv na) by lia; rewrite u_Z2bv by lia; lia).
      rewrite <- E. apply (KEEP (Z_to_bv 64 na) 32%Z (u x - na)%Z L1 NEna ltac:(lia)). rewrite E. unfold inslot. lia.
    - intros x Hx. cbn in Hx.
      destruct (blk_byte C A2 m2 _ (Z_to_bv 64 na) 32 x CK HW2 Lna2 ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact D. }
  pose proof (necells_frm := CE1). destruct CE1 as (C1 & C2).
  assert (CE2 : necells m2 s ret (getr regs 8)).
  { unfold necells. rewrite !(FRM_rdn16 C (s - 16) M1 m2 _ _ CK (proj1 PM2)) by lia. split; assumption. }
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  assert (E8 : getr r2 8 = Z_to_bv 64 na) by (csr; reflexivity).
  destruct (ne_B al_rom r2 m2 s na nalloc nb ret (getr regs 8) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret
              (W_sok_blk C A2 m2 _ (Z_to_bv 64 na) 32 na 32 CK HW2 Lna2 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia))
              (NUMA_rd_nalloc SEGS m2 na nalloc n 1 0 R2) CE2 E2 R10 E8) as (r3 & RUN3 & V2 & V1 & V10 & V8 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  set (M3 := wbytes (wbytes m2 _ _) _ _).
  assert (PMr2 : POSTM C Ar s m m2).
  { eapply POSTM_trans; [apply (POSTM_sub C Ar A _ _ _ SUBr); exact PM1 | eapply POSTM_mono; [|exact PM2]; lia]. }
  assert (WP3 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C Ar s m M3).
  { subst M3.
    do 2 (apply (WP_blk C Ar A2 m _ _ (Z_to_bv 64 na) _ 32); [exact CK | | exact Lna2 | exact LnaR | exact L01 | exact SUBr2 | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
    split; [exact HW2 | exact PMr2]. }
  destruct WP3 as [HW3 PM3].
  assert (R3 : RECat M3 na (numa_flds (2 * nalloc) n 1 nb)).
  { subst M3. unfold numa_flds.
    eapply (REC_wr' _ _ [(4%nat, nalloc); (4%nat, n); (4%nat, 1%Z); (4%nat, 0%Z); (4%nat, 1065353216%Z); (4%nat, 0%Z); (8%nat, nb)] _ 0 4);
      [ | cbn; lia | cbn; lia | reflexivity | cbn [fld_off Z.of_nat]; f_equal; lia | reflexivity ].
    eapply (REC_wr' _ _ [(4%nat, nalloc); (4%nat, n); (4%nat, 1%Z); (4%nat, 0%Z); (4%nat, 1065353216%Z); (4%nat, 0%Z); (8%nat, 0%Z)] _ 6 8);
      [ exact R2 | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ]. }
  apply (HK A2 M3 vm2 r3 nb HW3).
  - apply cs_kept_intro; csr; try reflexivity. all: rewrite ?V8; csr; reflexivity.
  - exact PM3.
  - split; [exact R3|]. split; [exact Hal|]. split; [lia|]. split; [exact ALnb|].
    split; [intros E; rewrite E in LnbA; rewrite L1 in LnbA; discriminate|].
    split; [unfold NUMA_NMAX; lia|]. split; [lia|]. split; [exact Lna2|]. split; [exact L01|].
    split; [replace (4 * (2 * nalloc))%Z with (8 * nalloc)%Z by lia; exact Lnb2 | exact Lnb0].
  - exact LnbA.
  - exact Larr2.
  - exact LEQ2.
  - exact V10.
  - apply (aroom_mono A2 vm2 _ _ _ _ Hroom2); [lia|]. replace (1 * (8 * nalloc))%Z with (8 * nalloc)%Z by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem numaAddNumber_store_W : numaAddNumber_store_contract.
Proof.
  intros fx C Ar A m md regs s na nalloc n arr ret S FZ CK HW SUBr H2 Hs16 Hlo Hhi H1 Hret H10 NA Hlt LnaR LarrR HK.
  unfold PC_numaAddNumber. replace (Z_to_bv 64 0x61848) with (0x61848 : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (Hlo' : (c_top C - LSTK + 32 <= s)%Z) by (unfold NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK in Hlo; lia).
  assert (HNS : (32 <= NAN_STACK)%Z) by (unfold NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK; lia).
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof NA as (R & Hal & Harr & Hala & NEan & Hnal & Hn & L1 & L01 & L2 & L02). unfold NUMA_NMAX in Hnal.
  destruct (blk_range C A m md (Z_to_bv 64 na) 32 CK HW L1 ltac:(lia)) as [Gna TOPna].
  pose proof (NUMA_wf m na nalloc n 1 arr R) as (_ & _ & _ & Warr & Wna0 & Wna).
  rewrite u_Z2bv in Gna, TOPna by lia.
  destruct (blk_range C A m md (Z_to_bv 64 arr) (4 * nalloc) CK HW L2 ltac:(lia)) as [Garr TOParr]. rewrite u_Z2bv in Garr, TOParr by lia.
  assert (NEna : Z_to_bv 64 na <> Z_to_bv 64 arr) by (apply zneq_w; [lia | lia |]; intros E; apply NEan; symmetry; exact E).
  pose proof (blk_apart C A m md _ _ _ _ CK HW L1 L2 NEna ltac:(lia) ltac:(lia)) as AP. rewrite !u_Z2bv in AP by lia.
  destruct (na_P_lt al_rom regs m s na nalloc n ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (mod16_mod8 _ Hal)
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia))
              (NUMA_rd_nalloc SEGS m na nalloc n 1 arr R) (NUMA_rd_n SEGS m na nalloc n 1 arr R) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q10 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := NAF m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold NAF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (nacells_NAF m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (R1 : RECat M1 na (numa_flds nalloc n 1 arr)).
  { apply (RECat_POSTM C A s m M1 (Z_to_bv 64 na) 32 _ _ R PM1 L1); rewrite u_Z2bv by lia; [lia | cbn; lia]. }
  destruct (na_T al_rom r1 M1 s na arr n ret (getr regs 8) (getr regs 9) (word_to_le_bytes 8 (reg_get (@fp_regs fx) 8))
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (mod16_mod4 _ Hala) Hret ltac:(rewrite length_N_to_le_bytes; reflexivity)
              (NUMA_rd_arr SEGS M1 na nalloc n 1 arr R1) (NUMA_rd_n SEGS M1 na nalloc n 1 arr R1)
              (W_sok_blk C A M1 md (Z_to_bv 64 arr) (4 * nalloc) (arr + 4 * n) 4 CK HW1 L2 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia))
              (W_sok_blk C A M1 md (Z_to_bv 64 na) 32 (na + 4) 4 CK HW1 L1 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia))
              CE1 Q2 Q10 Q9) as (r2 & RUN2 & V2 & V1 & V10 & V8 & V9 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  set (cv := u (low32 (reg_get (@fp_regs fx) 10))) in *.
  assert (Hcv : (0 <= cv < 2 ^ 32)%Z) by (subst cv; apply fp_u32_range).
  set (M2 := wbytes M1 (Z_to_bv 64 (arr + 4 * n)) (Z_to_le_bytes 4 cv)).
  set (M3 := wbytes M2 (Z_to_bv 64 (na + 4)) (word_to_le_bytes 4 (Z_to_bv 64 (n + 1)))).
  assert (PMr1 : POSTM C Ar s m M1) by (apply (POSTM_sub C Ar A _ _ _ SUBr); exact PM1).
  assert (WP2 : W C A M2 md /\ POSTM C Ar s m M2).
  { subst M2. apply (WP_blk C Ar A m M1 _ (Z_to_bv 64 arr) _ (4 * nalloc) _ s CK (conj HW1 PMr1) L2 LarrR L02 SUBr); rewrite ?length_Z_to_le_bytes, !u_Z2bv by lia; cbn; lia. }
  assert (WP3 : W C A M3 md /\ POSTM C Ar s m M3).
  { subst M3. apply (WP_blk C Ar A m M2 _ (Z_to_bv 64 na) _ 32 _ s CK WP2 L1 LnaR L01 SUBr); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia. }
  apply (HK (mkFP (bvmap_set 8 (bv_extract 0 64 (le_bytes_to_word (word_to_le_bytes 8 (reg_get (@fp_regs fx) 8)))) (@fp_regs fx)) (@fp_csr fx)) M3 r2).
  - exact FZ.
  - exact (proj1 WP3).
  - apply cs_kept_intro; csr; try reflexivity. all: rewrite ?V8, ?V9; csr; reflexivity.
  - exact (proj2 WP3).
  - split; [|do 5 (split; [assumption|]); split; [lia|]; repeat split; assumption].
    subst M3. unfold numa_flds.
    eapply (REC_wr' _ _ [(4%nat, nalloc); (4%nat, n); (4%nat, 1%Z); (4%nat, 0%Z); (4%nat, 1065353216%Z); (4%nat, 0%Z); (8%nat, arr)] _ 1 4);
      [ | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ].
    subst M2. apply RECat_out; [exact R1 | rewrite length_Z_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_Z_to_le_bytes, u_Z2bv by lia; cbn; lia].
  - unfold ncell. subst M3.
    rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    subst M2. pose proof (rdn_wbytes_hit SEGS (Z_to_le_bytes 4 cv) M1 (Z_to_bv 64 (arr + 4 * n))) as X. rewrite length_Z_to_le_bytes in X.
    apply X. rewrite u_Z2bv by lia. cbn. lia.
  - intros a N1 N2 N3. subst M3 M2 M1. unfold NAF.
    rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?length_Z_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity.
  - exact V10.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem numaAddNumber_grow_W : numaAddNumber_grow_contract.
Proof.
  intros fx C Ar A m md regs s na nalloc arr ret S FZ CK HW SUBr H2 Hs16 Hlo Hhi H1 Hret H4 H10 NA Hmax LnaR LarrR kR bR Hrm Hrk Hrb HK.
  unfold PC_numaAddNumber. replace (Z_to_bv 64 0x61848) with (0x61848 : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (Hlo' : (c_top C - LSTK + 32 + NEX_STACK <= s)%Z) by (unfold NAN_STACK in Hlo; lia).
  assert (Hlo'' : (c_top C - LSTK + 32 <= s)%Z) by (unfold NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK in Hlo'; lia).
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof NA as (R & Hal & Harr & Hala & NEan & Hnal & Hn & L1 & L01 & L2 & L02). unfold NUMA_NMAX in Hnal, Hmax.
  destruct (blk_range C A m md (Z_to_bv 64 na) 32 CK HW L1 ltac:(lia)) as [Gna TOPna].
  pose proof (NUMA_wf m na nalloc nalloc 1 arr R) as (_ & _ & _ & Warr & Wna0 & Wna).
  rewrite u_Z2bv in Gna, TOPna by lia.
  destruct (na_P_ge al_rom regs m s na nalloc nalloc ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (mod16_mod8 _ Hal)
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia))
              (NUMA_rd_nalloc SEGS m na nalloc nalloc 1 arr R) (NUMA_rd_n SEGS m na nalloc nalloc 1 arr R) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q10 & Q9 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := NAF m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold NAF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (nacells_NAF m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (NA1 : numa_at C A M1 na nalloc nalloc arr) by (exact (numa_at_keep C A A m M1 na nalloc nalloc arr NA (sub_live_refl A) (proj2 PM1))).
  (* [comment removed for export] *)
  destruct (na_F1 al_rom r1 M1) as (fr1 & RUNF1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUNF1 |].
  destruct (@na_G1 (mkFP fr1 (@fp_csr fx)) al_rom r1 M1 na Q10) as (r2 & RUN2 & P1 & P10 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  assert (P4 : getr r2 4 = Z_to_bv 64 TP9) by (csr; reflexivity).
  assert (P2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  replace (0x619bc : word) with (Z_to_bv 64 PC_numaExtendArray) by (apply bv_eq; reflexivity).
  apply (numaExtendArray_W (mkFP fr1 (@fp_csr fx)) C Ar A M1 md r2 (s - 32)%Z na nalloc nalloc arr (Z_to_bv 64 0x61880) S CK HW1 SUBr P2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(lia) ltac:(lia) P1 ltac:(red; apply bv_eq; reflexivity) P4 P10 NA1
           ltac:(unfold NUMA_NMAX; lia) LnaR LarrR kR bR Hrm Hrk Hrb).
  intros A2 m2 vm2 r3 arr' HW2 CS2 PM2 NA2 Larr'A Larr2 LEQ2 R10 Hroom2.
  replace (Z_to_bv 64 0x61880) with (0x61880 : word) by (apply bv_eq; reflexivity).
  pose proof NA2 as (R2 & _ & Harr' & Hala' & NEan' & _ & _ & L1' & _ & L2' & L02').
  destruct (blk_range C A2 m2 _ (Z_to_bv 64 arr') (4 * (2 * nalloc)) CK HW2 L2' ltac:(lia)) as [Garr' TOParr'].
  pose proof (NUMA_wf m2 na (2 * nalloc) nalloc 1 arr' R2) as (_ & _ & _ & Warr' & _ & _).
  rewrite u_Z2bv in Garr', TOParr' by lia.
  assert (NEna' : Z_to_bv 64 na <> Z_to_bv 64 arr') by (apply zneq_w; [lia | lia |]; intros E; apply NEan'; symmetry; exact E).
  pose proof (blk_apart C A2 m2 _ _ _ _ _ CK HW2 L1' L2' NEna' ltac:(lia) ltac:(lia)) as AP. rewrite !u_Z2bv in AP by lia.
  (* [comment removed for export] *)
  destruct (@na_F2 (mkFP fr1 (@fp_csr fx)) al_rom r3 m2) as (fr2 & RUNF2). cbn [fp_csr] in RUNF2.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUNF2 |].
  assert (E8 : getr r3 8 = Z_to_bv 64 na) by (csr; reflexivity).
  destruct (@na_G2 (mkFP fr2 (@fp_csr fx)) al_rom r3 m2 na R10 E8) as (r4 & RUN4 & X10 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN4 |].
  assert (CE2 : nacells m2 s ret (getr regs 8) (getr regs 9) (word_to_le_bytes 8 (reg_get (@fp_regs fx) 8))).
  { destruct CE1 as (C1 & C2 & C3 & C4). unfold nacells.
    rewrite !(FRM_rdn16 C (s - 32) M1 m2 _ _ CK (proj1 PM2)) by lia. repeat split; assumption. }
  assert (X2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (X9n : getr r4 9 = Z_to_bv 64 nalloc) by (csr; reflexivity).
  destruct (@na_T (mkFP fr2 (@fp_csr fx)) al_rom r4 m2 s na arr' nalloc ret (getr regs 8) (getr regs 9) (word_to_le_bytes 8 (reg_get (@fp_regs fx) 8))
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (mod16_mod4 _ Hala') Hret ltac:(rewrite length_N_to_le_bytes; reflexivity)
              (NUMA_rd_arr SEGS m2 na (2 * nalloc) nalloc 1 arr' R2) (NUMA_rd_n SEGS m2 na (2 * nalloc) nalloc 1 arr' R2)
              (W_sok_blk C A2 m2 _ (Z_to_bv 64 arr') (4 * (2 * nalloc)) (arr' + 4 * nalloc) 4 CK HW2 L2' ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia))
              (W_sok_blk C A2 m2 _ (Z_to_bv 64 na) 32 (na + 4) 4 CK HW2 L1' ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia))
              CE2 X2 X10 X9n) as (r5 & RUN5 & V2 & V1 & V10 & V8 & V9 & AG5).
  cbn [fp_regs fp_csr] in RUN5.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN5 |].
  set (cv := u (low32 (reg_get fr2 10))) in *.
  assert (Hcv : (0 <= cv < 2 ^ 32)%Z) by (subst cv; apply fp_u32_range).
  set (M3 := wbytes m2 (Z_to_bv 64 (arr' + 4 * nalloc)) (Z_to_le_bytes 4 cv)).
  set (M4 := wbytes M3 (Z_to_bv 64 (na + 4)) (word_to_le_bytes 4 (Z_to_bv 64 (nalloc + 1)))).
  assert (SUBr2 : sub_live Ar A2).
  { intros x kx Lx. assert (N1 : x <> Z_to_bv 64 arr) by (intros ->; congruence).
    assert (N2 : x <> Z_to_bv 64 arr') by (intros ->; rewrite (SUBr _ _ Lx) in Larr'A; discriminate).
    rewrite (LEQ2 x N1 N2). exact (SUBr x kx Lx). }
  assert (Larr'R : live Ar (Z_to_bv 64 arr') = None).
  { destruct (live Ar (Z_to_bv 64 arr')) as [z|] eqn:E; [|reflexivity]. rewrite (SUBr _ _ E) in Larr'A. discriminate. }
  assert (PMr2 : POSTM C Ar s m m2).
  { eapply POSTM_trans; [apply (POSTM_sub C Ar A _ _ _ SUBr); exact PM1 | eapply POSTM_mono; [|exact PM2]; lia]. }
  assert (WP3 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C Ar s m M3).
  { subst M3. apply (WP_blk C Ar A2 m m2 _ (Z_to_bv 64 arr') _ (4 * (2 * nalloc)) _ s CK (conj HW2 PMr2) L2' Larr'R L02' SUBr2); rewrite ?length_Z_to_le_bytes, !u_Z2bv by lia; cbn; lia. }
  assert (WP4 : W C A2 M4 (with_vmmaps vm2 md) /\ POSTM C Ar s m M4).
  { subst M4. apply (WP_blk C Ar A2 m M3 _ (Z_to_bv 64 na) _ 32 _ s CK WP3 L1' LnaR L01 SUBr2); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia. }
  apply (HK (mkFP (bvmap_set 8 (bv_extract 0 64 (le_bytes_to_word (word_to_le_bytes 8 (reg_get (@fp_regs fx) 8)))) fr2) (@fp_csr fx)) A2 M4 vm2 r5 arr').
  - exact FZ.
  - exact (proj1 WP4).
  - apply cs_kept_intro; csr; try reflexivity. all: rewrite ?V8, ?V9; csr; reflexivity.
  - exact (proj2 WP4).
  - pose proof NA2 as (_ & X1 & X2' & X3 & X4 & X5 & X6 & X7 & X8' & X9 & X10').
    split; [|do 5 (split; [assumption|]); split; [lia|]; repeat split; assumption].
    subst M4. unfold numa_flds.
    eapply (REC_wr' _ _ [(4%nat, (2 * nalloc)%Z); (4%nat, nalloc); (4%nat, 1%Z); (4%nat, 0%Z); (4%nat, 1065353216%Z); (4%nat, 0%Z); (8%nat, arr')] _ 1 4);
      [ | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ].
    subst M3. apply RECat_out; [exact R2 | rewrite length_Z_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_Z_to_le_bytes, u_Z2bv by lia; cbn; lia].
  - exact Larr'A.
  - exact Larr2.
  - exact LEQ2.
  - exact V10.
  - exact Hroom2.
Qed.

End Numa.
