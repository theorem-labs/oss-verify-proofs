(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRecs LeptSlots PFLib LeptNuma LeptNumaW LeptRoom LeptRoom9 LeptEdgeFP.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require Import O9LeptBase O9LeptEdge_iface O9LeptNuma O9LeptEdgeSegs.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Nfe.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O9Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma W_rdn_win : forall C A m md (a : Z) (k : nat), Cok C -> W C A m md ->
  (c_top C - LSTK <= a)%Z -> (a + Z.of_nat k <= c_top C)%Z -> exists bs, rdn SEGS m (Z_to_bv 64 a) k = Some bs /\ length bs = k.
Proof.
  intros C A m md a k CK HW Hlo Hhi. pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  apply rdn_defined; [lia | lia |]. intros i Hi. apply (w_win _ _ _ _ HW). unfold win. rewrite u_Z2bv by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma blk_rdn_in : forall C A m md (p n a : Z) (k : nat), Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some n ->
  (0 <= p)%Z -> (p + n < 2 ^ 64)%Z -> (p <= a)%Z -> (a + Z.of_nat k <= p + n)%Z -> exists bs, rdn SEGS m (Z_to_bv 64 a) k = Some bs /\ length bs = k.
Proof.
  intros C A m md p n a k CK HW L Hp Hpn Ha Hk. apply rdn_defined; [lia | lia |]. intros i Hi.
  destruct (blk_byte C A m _ (Z_to_bv 64 p) _ (Z_to_bv 64 (a + i)) CK HW L ltac:(rewrite !u_Z2bv by lia; lia)) as (_ & D & _). exact D.
Qed.

(* [comment removed for export] *)
Lemma numa_at_geom : forall C A m md na nalloc n arr, Cok C -> W C A m md -> numa_at C A m na nalloc n arr ->
  (4096 <= na)%Z /\ (na + 32 <= alloc_top (c_vm C))%Z /\ (4096 <= arr)%Z /\ (arr + 4 * nalloc <= alloc_top (c_vm C))%Z.
Proof.
  intros C A m md na nalloc n arr CK HW (R & Hal & Harr & Hala & NEan & Hnal & Hn & L1 & L01 & L2 & L02).
  pose proof (NUMA_wf m na nalloc n 1 arr R) as (_ & _ & _ & Warr & Wna0 & Wna).
  destruct (blk_range C A m md (Z_to_bv 64 na) 32 CK HW L1 ltac:(lia)) as [Gna TOPna]. rewrite u_Z2bv in Gna, TOPna by lia.
  destruct (blk_range C A m md (Z_to_bv 64 arr) (4 * nalloc) CK HW L2 ltac:(lia)) as [Garr TOParr]. rewrite u_Z2bv in Garr, TOParr by lia.
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nfe_cl (s : Z) (ret : word) (regs fr : bvmap 5 word) : list (Z * word) :=
  [((s - 8)%Z, ret); ((s - 16)%Z, getr regs 8); ((s - 24)%Z, getr regs 9); ((s - 32)%Z, getr regs 18); ((s - 40)%Z, getr regs 19);
   ((s - 48)%Z, getr regs 20); ((s - 56)%Z, getr regs 21); ((s - 64)%Z, getr regs 22); ((s - 72)%Z, getr regs 23); ((s - 80)%Z, getr regs 24);
   ((s - 88)%Z, getr regs 25); ((s - 96)%Z, reg_get fr 8); ((s - 104)%Z, reg_get fr 9); ((s - 112)%Z, reg_get fr 18)].

Lemma nfe_cl_NFEF : forall m s ret regs fr, (128 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (NFEF m s ret regs fr) (nfe_cl s ret regs fr).
Proof. intros m s ret regs fr Hs Hs64. unfold nfe_cl, NFEF. cbn [cellsZ]. repeat split; rdn_chain. Qed.

Lemma nfe_cl_above : forall s ret regs fr (lo : Z), (lo <= s - 112)%Z -> (s < 2 ^ 64)%Z ->
  Forall (fun av : Z * word => (lo <= fst av /\ fst av + 8 <= 2 ^ 64)%Z) (nfe_cl s ret regs fr).
Proof. intros s ret regs fr lo Hlo Hs. unfold nfe_cl. repeat constructor; cbn [fst]; lia. Qed.

Lemma nfe_cl_apart : forall s ret regs fr (lo hi : Z), (112 <= s)%Z -> (hi <= s - 112)%Z -> (s < 2 ^ 64)%Z ->
  Forall (fun av : Z * word => (0 <= fst av /\ fst av + 8 <= 2 ^ 64 /\ (hi <= fst av \/ fst av + 8 <= lo))%Z) (nfe_cl s ret regs fr).
Proof. intros s ret regs fr lo hi Hs0 Hhi Hs. unfold nfe_cl. repeat constructor; cbn [fst]; lia. Qed.

(* [comment removed for export] *)
Definition nfe_keep (regs0 regs : bvmap 5 word) : Prop :=
  getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\ getr regs 26 = getr regs0 26 /\ getr regs 27 = getr regs0 27.

(* [comment removed for export] *)
Definition nfe_inv (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (s nad : Z) (cl : list (Z * word)) (kR bR cmax : Z)
                   (Ak : AS) (mk : word -> option byte) (vmk : VmMaps) : Prop :=
  W C Ak mk (with_vmmaps vmk md) /\ POSTM C A s m mk /\ cellsZ mk cl /\ sub_live A Ak /\
  exists k c arrd, (0 <= k <= NFE_GROWS)%Z /\ (0 <= c <= cmax)%Z /\
    numa_at C Ak mk nad (50 * 2 ^ k) c arrd /\
    live A (Z_to_bv 64 nad) = None /\ live A (Z_to_bv 64 arrd) = None /\
    (forall q, q <> Z_to_bv 64 nad -> q <> Z_to_bv 64 arrd -> live Ak q = live A q) /\
    aroom Ak vmk (kR - RK_numa - k) (bR - RB_numa 50 - grow_cost k).

Lemma nfe_inv_weaken : forall C A m md s nad cl kR bR cmax cmax' Ak mk vmk, (cmax <= cmax')%Z ->
  nfe_inv C A m md s nad cl kR bR cmax Ak mk vmk -> nfe_inv C A m md s nad cl kR bR cmax' Ak mk vmk.
Proof.
  intros C A m md s nad cl kR bR cmax cmax' Ak mk vmk Hc (HW & PM & CE & SUB & k & c & arrd & Hk & Hcc & REST).
  split; [exact HW|]. split; [exact PM|]. split; [exact CE|]. split; [exact SUB|]. exists k, c, arrd. split; [exact Hk|]. split; [lia | exact REST].
Qed.

(* [comment removed for export] *)
Lemma nfe_inv_win : forall C A m md s nad ret regs0 fr0 kR bR cmax Ak mk vmk (a : Z) (bs : list byte),
  Cok C -> (c_top C - LSTK + 128 <= s)%Z -> (s <= c_top C)%Z -> (s - 128 <= a)%Z -> (a + Z.of_nat (length bs) <= s - 112)%Z ->
  nfe_inv C A m md s nad (nfe_cl s ret regs0 fr0) kR bR cmax Ak mk vmk ->
  nfe_inv C A m md s nad (nfe_cl s ret regs0 fr0) kR bR cmax Ak (wbytes mk (Z_to_bv 64 a) bs) vmk.
Proof.
  intros C A m md s nad ret regs0 fr0 kR bR cmax Ak mk vmk a bs CK Hlo Hhi Ha Hb (HW & PM & CE & SUB & k & c & arrd & Hk & Hcc & NA & REST).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct (WP_win C Ak A m mk _ (Z_to_bv 64 a) bs s CK (conj HW PM) SUB ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia) Hhi) as [HW' PM'].
  destruct (WP_win C Ak Ak mk mk _ (Z_to_bv 64 a) bs s CK (conj HW (POSTM_refl C Ak s mk)) (sub_live_refl Ak) ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia) Hhi) as [_ PMk].
  split; [exact HW'|]. split; [exact PM'|]. split.
  - apply (cellsZ_out mk _ a (a + Z.of_nat (length bs)) _); [| apply nfe_cl_apart; lia | exact CE].
    intros x Hx. apply wbytes_outside; rewrite u_Z2bv by lia; lia.
  - split; [exact SUB|]. exists k, c, arrd. split; [exact Hk|]. split; [exact Hcc|]. split; [|exact REST].
    exact (numa_at_keep C Ak Ak mk _ nad _ c arrd NA (sub_live_refl Ak) (proj2 PMk)).
Qed.

Ltac rzs HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
(* [comment removed for export] *)
Ltac r2_tac HR :=
  let H2 := fresh "H2" in let H8 := fresh "H8" in let H9 := fresh "H9" in let H18 := fresh "H18" in let H19 := fresh "H19" in let H20 := fresh "H20" in
  let H21 := fresh "H21" in let H22 := fresh "H22" in let H23 := fresh "H23" in let H25 := fresh "H25" in
  pose proof HR as (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25); unfold nfe_R2; repeat split; csr; reflexivity.
Ltac r1_tac HR :=
  let H2 := fresh "H2" in let H8 := fresh "H8" in let H9 := fresh "H9" in let H18 := fresh "H18" in let H19 := fresh "H19" in let H21 := fresh "H21" in
  pose proof HR as (H2 & H8 & H9 & H18 & H19 & H21); unfold nfe_R1; repeat split; csr; reflexivity.
Ltac keep_tac HKP :=
  let K3 := fresh "K3" in let K4 := fresh "K4" in let K26 := fresh "K26" in let K27 := fresh "K27" in
  pose proof HKP as (K3 & K4 & K26 & K27); unfold nfe_keep; repeat split; csr; reflexivity.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nfe_ngf_W : forall (fx : FPState) C A m md regs (s nas nalloc n arr nad : Z) (ret0 : word) regs0 fr0 kR bR cmax Ak mk vmk (i pv : Z) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + NFE_STACK <= s)%Z -> (s <= c_top C)%Z ->
  numa_at C A m nas nalloc n arr -> (0 <= i < n)%Z -> (n <= 20000)%Z -> (pv = s - 120 \/ pv = s - 116)%Z ->
  nfe_inv C A m md s nad (nfe_cl s ret0 regs0 fr0) kR bR cmax Ak mk vmk ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 nas -> getr regs 11 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 pv ->
  (forall (fx' : FPState) mk' regs', frm_zero (@fp_csr fx') -> nfe_inv C A m md s nad (nfe_cl s ret0 regs0 fr0) kR bR cmax Ak mk' vmk ->
     regs_agree (fun r => In r [10; 11; 13]%list) regs regs' ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret mk' al_rom) (with_vmmaps vmk md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (0x60db4 : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros fx C A m md regs s nas nalloc n arr nad ret0 regs0 fr0 kR bR cmax Ak mk vmk i pv ret S FZ CK Hs16 Hlo Hhi NA Hi Hn Hpv INV H1 Hret H10 H11 H12 HK.
  pose proof INV as (HW & PM & CE & SUB & _).
  pose proof (numa_at_keep C A Ak m mk nas nalloc n arr NA SUB (proj2 PM)) as NAk.
  destruct (numa_at_geom C Ak mk _ nas nalloc n arr CK HW NAk) as (Gna & TOPna & Garr & TOParr).
  pose proof NAk as (R & Hal & _ & Hala & _ & Hnal & Hnn & _ & _ & L2 & _).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  unfold NFE_STACK, NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK in Hlo.
  destruct (blk_rdn_in C Ak mk _ arr (4 * nalloc) (arr + 4 * i) 4 CK HW L2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (bs & RC & LEN).
  destruct (ngf_run al_rom fx regs mk nas nalloc n 1 arr i pv bs ret R Hi ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(lia) ltac:(lia) RC (W_sok_win C Ak mk _ pv 4 CK HW ltac:(lia) ltac:(cbn; lia)) Hret H1 H10 H11 H12) as (fr' & regs' & RUN & _ & AG).
  rzs HW RUN.
  apply (HK (mkFP fr' (@fp_csr fx)) _ regs' FZ); [|exact AG].
  apply nfe_inv_win; [exact CK | lia | exact Hhi | lia | rewrite LEN; cbn; lia |].
  apply nfe_inv_win; [exact CK | lia | exact Hhi | lia | rewrite length_N_to_le_bytes; cbn; lia | exact INV].
Qed.

(* [comment removed for export] *)
Lemma nfe_add_W : forall (fx : FPState) C A m md regs (s nad : Z) cl kR bR cmax Ak mk vmk (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + NFE_STACK <= s)%Z -> (s <= c_top C)%Z ->
  (RK_nfe <= kR)%Z -> (RB_nfe <= bR)%Z -> (cmax <= 19997)%Z ->
  Forall (fun av : Z * word => (s - 128 <= fst av /\ fst av + 8 <= 2 ^ 64)%Z) cl ->
  nfe_inv C A m md s nad cl kR bR cmax Ak mk vmk ->
  getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 TP9 -> getr regs 10 = Z_to_bv 64 nad ->
  (forall (fx' : FPState) Ak' mk' vmk' regs', frm_zero (@fp_csr fx') -> nfe_inv C A m md s nad cl kR bR (cmax + 1) Ak' mk' vmk' -> cs_kept regs regs' ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret mk' al_rom) (with_vmmaps vmk' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (0x60b90 : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros fx C A m md regs s nad cl kR bR cmax Ak mk vmk ret S FZ CK Hs16 Hlo Hhi HkR HbR Hcm HCL
    (HW & PM & CE & SUB & k & c & arrd & Hk & Hc & NA & LnA & LaA & LEQ & ROOM) H2 H1 Hret H4 H10 HK.
  replace (0x60b90 : word) with (Z_to_bv 64 PC_numaAddNumber) by (apply bv_eq; reflexivity).
  pose proof NA as (_ & _ & _ & _ & _ & Hnal & Hn & _).
  assert (Hlo' : (c_top C - LSTK + NAN_STACK <= s - 128)%Z) by (unfold NFE_STACK in Hlo; lia).
  assert (Hlo'' : (c_top C - LSTK <= s - 128)%Z) by (unfold NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK in Hlo'; lia).
  assert (Hs16' : ((s - 128) mod 16 = 0)%Z) by (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity).
  unfold NFE_GROWS in Hk.
  destruct (Z_lt_ge_dec c (50 * 2 ^ k)) as [Hlt|Hge].
  - (* [comment removed for export] *)
    apply (numaAddNumber_store_W fx C A Ak mk (with_vmmaps vmk md) regs (s - 128)%Z nad (50 * 2 ^ k)%Z c arrd ret S FZ CK HW SUB H2 Hs16' Hlo' ltac:(lia) H1 Hret H10 NA Hlt LnA LaA).
    intros fx' m' regs' FZ' HW' CS' PM' NA' _ _ _.
    apply (HK fx' Ak m' vmk regs' FZ'); [|exact CS'].
    split; [exact HW'|]. split; [eapply POSTM_trans; [exact PM | eapply POSTM_mono; [|exact PM']; lia]|].
    split; [exact (cellsZ_frm C (s - 128) mk m' cl CK (proj1 PM') Hlo'' HCL CE)|].
    split; [exact SUB|]. exists k, (c + 1)%Z, arrd.
    split; [unfold NFE_GROWS; lia|]. split; [lia|]. split; [exact NA'|]. split; [exact LnA|]. split; [exact LaA|]. split; [exact LEQ | exact ROOM].
  - (* [comment removed for export] *)
    assert (Ec : c = (50 * 2 ^ k)%Z) by lia. subst c.
    assert (Hk8 : (k <= 8)%Z).
    { destruct (Z_le_gt_dec k 8) as [X|X]; [exact X|]. exfalso. assert (P9 : (2 ^ 9 <= 2 ^ k)%Z) by (apply Z.pow_le_mono_r; lia). change (2 ^ 9)%Z with 512%Z in P9. lia. }
    assert (P8 : (2 ^ k <= 2 ^ 8)%Z) by (apply Z.pow_le_mono_r; lia). change (2 ^ 8)%Z with 256%Z in P8.
    pose proof (grow_cost_step k ltac:(lia)) as GS. pose proof (grow_cost_mono (k + 1) 9 ltac:(lia)) as GM.
    unfold RK_nfe, RB_nfe, NFE_GROWS, RK_numa in *.
    apply (numaAddNumber_grow_W fx C A Ak mk (with_vmmaps vmk md) regs (s - 128)%Z nad (50 * 2 ^ k)%Z arrd ret S FZ CK HW SUB H2 Hs16' Hlo' ltac:(lia) H1 Hret H4 H10 NA
             ltac:(unfold NUMA_NMAX; change (2 ^ 24)%Z with 16777216%Z; lia) LnA LaA (kR - 2 - k)%Z (bR - RB_numa 50 - grow_cost k)%Z
             ltac:(rewrite with_vmmaps_vmmaps; exact ROOM) ltac:(lia) ltac:(lia)).
    intros fx' A' m' vm' regs' arr' FZ' HW' CS' PM' NA' LarrA Larr' LEQ' _ ROOM'. rewrite with_vmmaps_twice in HW' |- *.
    apply (HK fx' A' m' vm' regs' FZ'); [|exact CS'].
    split; [exact HW'|]. split; [eapply POSTM_trans; [exact PM | eapply POSTM_mono; [|exact PM']; lia]|].
    split; [exact (cellsZ_frm C (s - 128) mk m' cl CK (proj1 PM') Hlo'' HCL CE)|].
    assert (LaA' : live A (Z_to_bv 64 arr') = None).
    { destruct (live A (Z_to_bv 64 arr')) as [z|] eqn:E; [|reflexivity]. rewrite (SUB _ _ E) in LarrA. discriminate. }
    split.
    { intros q kq Lq. assert (N1 : q <> Z_to_bv 64 arrd) by (intros ->; congruence). assert (N2 : q <> Z_to_bv 64 arr') by (intros ->; congruence).
      rewrite (LEQ' q N1 N2). exact (SUB q kq Lq). }
    exists (k + 1)%Z, (50 * 2 ^ k + 1)%Z, arr'.
    split; [unfold NFE_GROWS; lia|]. split; [lia|].
    split. { replace (50 * 2 ^ (k + 1))%Z with (2 * (50 * 2 ^ k))%Z by (rewrite Z.pow_add_r by lia; change (2 ^ 1)%Z with 2%Z; lia). exact NA'. }
    split; [exact LnA|]. split; [exact LaA'|]. split.
    { intros q N1 N2. destruct (bv_eq_dec _ q (Z_to_bv 64 arrd)) as [->|N3]; [rewrite Larr'; symmetry; exact LaA|]. rewrite (LEQ' q N3 N2). exact (LEQ q N1 N3). }
    apply (aroom_mono A' vm' _ _ _ _ ROOM'); unfold RK_numa; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nfe_loop2_W : forall (j : nat) (fx : FPState) C A m md regs0 fr0 (s nas nalloc n arr nad : Z) (ret0 : word) kR bR Ak mk vmk regs (i loc : Z) (d : bool) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + NFE_STACK <= s)%Z -> (s <= c_top C)%Z ->
  numa_at C A m nas nalloc n arr -> (n <= 20000)%Z -> (RK_nfe <= kR)%Z -> (RB_nfe <= bR)%Z ->
  (Z.of_nat j = n - i)%Z -> (2 <= i < n)%Z -> (0 <= loc < n)%Z ->
  nfe_inv C A m md s nad (nfe_cl s ret0 regs0 fr0) kR bR (i - 2) Ak mk vmk ->
  nfe_R2 regs s nas nad n i loc d -> nfe_keep regs0 regs -> getr regs0 4 = Z_to_bv 64 TP9 ->
  (forall (fx' : FPState) Ak' mk' vmk' regs', frm_zero (@fp_csr fx') -> nfe_inv C A m md s nad (nfe_cl s ret0 regs0 fr0) kR bR (n - 2) Ak' mk' vmk' ->
      getr regs' 2 = Z_to_bv 64 (s - 128) -> getr regs' 9 = Z_to_bv 64 nad -> nfe_keep regs0 regs' ->
      realizes SEGS (mkCfg (@mkst fx' regs' (0x609a8 : word) mk' al_rom) (with_vmmaps vmk' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (0x608f0 : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  induction j as [|j IH]; intros fx C A m md regs0 fr0 s nas nalloc n arr nad ret0 kR bR Ak mk vmk regs i loc d S
    FZ CK Hs16 Hlo Hhi NA Hn HkR HbR Hj Hi Hloc INV HR2 KEEP H4 HK; [lia|].
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (Hs128 : (128 <= s)%Z) by (unfold NFE_STACK, NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK in Hlo; lia).
  assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  assert (Hlow : (c_top C - LSTK <= s - 128)%Z) by (unfold NFE_STACK, NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK in Hlo; lia).
  (* [comment removed for export] *)
  assert (LATCH : forall (fx1 : FPState) Ak1 mk1 vmk1 regs1 loc1 (d1 d' : bool), frm_zero (@fp_csr fx1) ->
            nfe_inv C A m md s nad (nfe_cl s ret0 regs0 fr0) kR bR (i - 1) Ak1 mk1 vmk1 ->
            nfe_R2 regs1 s nas nad n i loc1 d1 -> (0 <= loc1 < n)%Z -> getr regs1 24 = (if d' then Z_to_bv 64 1 else Z_to_bv 64 MONE) ->
            nfe_keep regs0 regs1 ->
            realizes SEGS (mkCfg (@mkst fx1 regs1 (0x608e4 : word) mk1 al_rom) (with_vmmaps vmk1 md)) S).
  { intros fx1 Ak1 mk1 vmk1 regs1 loc1 d1 d' FZ1 INV1 R2a Hloc1 E24 KEEP1. pose proof INV1 as (HW1 & _).
    destruct (Z_lt_ge_dec (i + 1) n) as [Hnx|Hlast].
    - destruct (nfe_LATn al_rom fx1 regs1 mk1 s nas nad n i loc1 d1 d' ltac:(lia) Hnx ltac:(lia) R2a E24) as (regs2 & RUN & R2b & AG).
      rzs HW1 RUN.
      apply (IH fx1 C A m md regs0 fr0 s nas nalloc n arr nad ret0 kR bR Ak1 mk1 vmk1 regs2 (i + 1)%Z loc1 d' S FZ1 CK Hs16 Hlo Hhi NA Hn HkR HbR
               ltac:(lia) ltac:(lia) Hloc1 ltac:(replace (i + 1 - 2)%Z with (i - 1)%Z by lia; exact INV1) R2b ltac:(keep_tac KEEP1) H4 HK).
    - destruct (nfe_LATx al_rom fx1 regs1 mk1 s nas nad n i loc1 d1 ltac:(lia) ltac:(lia) ltac:(lia) R2a) as (regs2 & RUN & E2 & E9 & AG).
      rzs HW1 RUN.
      apply (HK fx1 Ak1 mk1 vmk1 regs2 FZ1); [apply (nfe_inv_weaken _ _ _ _ _ _ _ _ _ (i - 1)%Z); [lia | exact INV1] | exact E2 | exact E9 | keep_tac KEEP1]. }
  pose proof INV as (HW & _).
  (* [comment removed for export] *)
  destruct (nfe_L2h al_rom fx regs mk s nas nad n i loc d Hs128 Hs64 HR2) as (regs1 & RUN1 & R2_1 & Q1 & Q10 & Q11 & Q12 & AG1).
  rzs HW RUN1.
  apply (nfe_ngf_W fx C A m md regs1 s nas nalloc n arr nad ret0 regs0 fr0 kR bR (i - 2)%Z Ak mk vmk i (s - 120)%Z (Z_to_bv 64 0x60900) S FZ CK Hs16 Hlo Hhi NA
           ltac:(lia) Hn ltac:(left; reflexivity) INV Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12).
  intros fx2 mk2 regs2 FZ2 INV2 AG2. replace (Z_to_bv 64 0x60900) with (0x60900 : word) by (apply bv_eq; reflexivity).
  pose proof INV2 as (HW2 & _).
  destruct (W_rdn_win C Ak mk2 _ (s - 120) 4 CK HW2 ltac:(lia) ltac:(cbn; lia)) as (b8 & R8 & _).
  assert (R2_2 : nfe_R2 regs2 s nas nad n i loc d) by (r2_tac R2_1).
  assert (KEEP2 : nfe_keep regs0 regs2) by (keep_tac KEEP).
  assert (INV2' : nfe_inv C A m md s nad (nfe_cl s ret0 regs0 fr0) kR bR (i - 1) Ak mk2 vmk) by (apply (nfe_inv_weaken _ _ _ _ _ _ _ _ _ (i - 2)%Z); [lia | exact INV2]).
  assert (HCL : Forall (fun av : Z * word => (s - 128 <= fst av /\ fst av + 8 <= 2 ^ 64)%Z) (nfe_cl s ret0 regs0 fr0)) by (apply nfe_cl_above; lia).
  destruct d.
  - (* [comment removed for export] *)
    destruct (nfe_L2a al_rom fx2 regs2 mk2 s nas nad n i loc b8 FZ2 Hs128 Hs64 ltac:(lia) ltac:(lia) ltac:(lia) R8 R2_2) as (fr3 & cs3 & regs3 & b' & RUN3 & FZ3 & E10 & AG3).
    rzs HW2 RUN3.
    assert (R2_3 : nfe_R2 regs3 s nas nad n i loc true) by (r2_tac R2_2).
    assert (KEEP3 : nfe_keep regs0 regs3) by (keep_tac KEEP2).
    destruct b'.
    + (* [comment removed for export] *)
      destruct (nfe_L2a1 al_rom (mkFP fr3 cs3) regs3 mk2 s nas nad n i loc FZ3 Hs128 Hs64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R2_3 E10)
        as (fr4 & cs4 & regs4 & RUN4 & FZ4 & R2_4 & E24 & AG4).
      rzs HW2 RUN4.
      apply (LATCH (mkFP fr4 cs4) Ak mk2 vmk regs4 i true true FZ4 INV2' R2_4 ltac:(lia) E24 ltac:(keep_tac KEEP3)).
    + destruct (nfe_L2a0 al_rom (mkFP fr3 cs3) regs3 mk2 s nas nad n i loc FZ3 Hs128 Hs64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R2_3 E10)
        as (fr4 & cs4 & regs4 & b'' & RUN4 & FZ4 & E10' & E24 & AG4).
      rzs HW2 RUN4.
      assert (R2_4 : nfe_R2 regs4 s nas nad n i loc true) by (r2_tac R2_3).
      assert (KEEP4 : nfe_keep regs0 regs4) by (keep_tac KEEP3).
      destruct b''.
      * (* [comment removed for export] *)
        destruct (nfe_L2a01 al_rom (mkFP fr4 cs4) regs4 mk2 s nas nad n i loc FZ4 Hs128 Hs64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R2_4 E10' E24)
          as (fr5 & cs5 & regs5 & RUN5 & FZ5 & R2_5 & E24_5 & Q1_5 & Q10_5 & _ & AG5).
        rzs HW2 RUN5.
        assert (KEEP5 : nfe_keep regs0 regs5) by (keep_tac KEEP4).
        apply (nfe_add_W (mkFP fr5 cs5) C A m md regs5 s nad _ kR bR (i - 2)%Z Ak mk2 vmk (Z_to_bv 64 0x60948) S FZ5 CK Hs16 Hlo Hhi HkR HbR ltac:(lia) HCL INV2
                 (proj1 R2_5) Q1_5 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite (proj1 (proj2 KEEP5)); exact H4) Q10_5).
        intros fx6 Ak6 mk6 vmk6 regs6 FZ6 INV6 CS6. replace (Z_to_bv 64 0x60948) with (0x60948 : word) by (apply bv_eq; reflexivity).
        pose proof INV6 as (HW6 & _).
        destruct (W_rdn_win C Ak6 mk6 _ (s - 120) 4 CK HW6 ltac:(lia) ltac:(cbn; lia)) as (b8' & R8' & _).
        assert (R2_6 : nfe_R2 regs6 s nas nad n i loc true) by (r2_tac R2_5).
        assert (E24_6 : getr regs6 24 = Z_to_bv 64 MONE) by (csr; reflexivity).
        destruct (nfe_L2aR al_rom fx6 regs6 mk6 s nas nad n i loc b8' FZ6 Hs128 Hs64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R8' R2_6 E24_6)
          as (fr7 & cs7 & regs7 & RUN7 & FZ7 & R2_7 & E24_7 & AG7).
        rzs HW6 RUN7.
        apply (LATCH (mkFP fr7 cs7) Ak6 mk6 vmk6 regs7 i true false FZ7 ltac:(replace (i - 1)%Z with (i - 2 + 1)%Z by lia; exact INV6) R2_7 ltac:(lia) E24_7
                 ltac:(keep_tac KEEP5)).
      * (* [comment removed for export] *)
        destruct (nfe_L2a00 al_rom (mkFP fr4 cs4) regs4 mk2 s nas nad n i loc Hs128 Hs64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R2_4 E10' E24)
          as (regs5 & RUN5 & R2_5 & E24_5 & AG5).
        rzs HW2 RUN5.
        apply (LATCH (mkFP fr4 cs4) Ak mk2 vmk regs5 loc true true FZ4 INV2' R2_5 Hloc E24_5 ltac:(keep_tac KEEP4)).
  - (* [comment removed for export] *)
    destruct (nfe_L2b al_rom fx2 regs2 mk2 s nas nad n i loc b8 FZ2 Hs128 Hs64 ltac:(lia) ltac:(lia) ltac:(lia) R8 R2_2) as (fr3 & cs3 & regs3 & b' & RUN3 & FZ3 & E10 & E24 & AG3).
    rzs HW2 RUN3.
    assert (R2_3 : nfe_R2 regs3 s nas nad n i loc false) by (r2_tac R2_2).
    assert (KEEP3 : nfe_keep regs0 regs3) by (keep_tac KEEP2).
    destruct b'.
    + (* [comment removed for export] *)
      destruct (nfe_L2b1 al_rom (mkFP fr3 cs3) regs3 mk2 s nas nad n i loc FZ3 Hs128 Hs64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R2_3 E10 E24)
        as (fr4 & cs4 & regs4 & RUN4 & FZ4 & R2_4 & E24_4 & AG4).
      rzs HW2 RUN4.
      apply (LATCH (mkFP fr4 cs4) Ak mk2 vmk regs4 i false false FZ4 INV2' R2_4 ltac:(lia) E24_4 ltac:(keep_tac KEEP3)).
    + destruct (nfe_L2b0 al_rom (mkFP fr3 cs3) regs3 mk2 s nas nad n i loc FZ3 Hs128 Hs64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R2_3 E10 E24)
        as (fr4 & cs4 & regs4 & b'' & RUN4 & FZ4 & E10' & E24' & AG4).
      rzs HW2 RUN4.
      assert (R2_4 : nfe_R2 regs4 s nas nad n i loc false) by (r2_tac R2_3).
      assert (KEEP4 : nfe_keep regs0 regs4) by (keep_tac KEEP3).
      destruct b''.
      * (* [comment removed for export] *)
        destruct (nfe_L2b01 al_rom (mkFP fr4 cs4) regs4 mk2 s nas nad n i loc FZ4 Hs128 Hs64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R2_4 E10' E24')
          as (fr5 & cs5 & regs5 & RUN5 & FZ5 & R2_5 & Q1_5 & Q10_5 & _ & AG5).
        rzs HW2 RUN5.
        assert (KEEP5 : nfe_keep regs0 regs5) by (keep_tac KEEP4).
        apply (nfe_add_W (mkFP fr5 cs5) C A m md regs5 s nad _ kR bR (i - 2)%Z Ak mk2 vmk (Z_to_bv 64 0x60988) S FZ5 CK Hs16 Hlo Hhi HkR HbR ltac:(lia) HCL INV2
                 (proj1 R2_5) Q1_5 ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite (proj1 (proj2 KEEP5)); exact H4) Q10_5).
        intros fx6 Ak6 mk6 vmk6 regs6 FZ6 INV6 CS6. replace (Z_to_bv 64 0x60988) with (0x60988 : word) by (apply bv_eq; reflexivity).
        pose proof INV6 as (HW6 & _).
        destruct (W_rdn_win C Ak6 mk6 _ (s - 120) 4 CK HW6 ltac:(lia) ltac:(cbn; lia)) as (b8' & R8' & _).
        assert (R2_6 : nfe_R2 regs6 s nas nad n i loc false) by (r2_tac R2_5).
        destruct (nfe_L2bR al_rom fx6 regs6 mk6 s nas nad n i loc b8' FZ6 Hs128 Hs64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R8' R2_6)
          as (fr7 & cs7 & regs7 & RUN7 & FZ7 & R2_7 & E24_7 & AG7).
        rzs HW6 RUN7.
        apply (LATCH (mkFP fr7 cs7) Ak6 mk6 vmk6 regs7 i false true FZ7 ltac:(replace (i - 1)%Z with (i - 2 + 1)%Z by lia; exact INV6) R2_7 ltac:(lia) E24_7
                 ltac:(keep_tac KEEP5)).
      * destruct (nfe_L2b00 al_rom (mkFP fr4 cs4) regs4 mk2 s nas nad n i loc Hs128 Hs64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R2_4 E10' E24')
          as (regs5 & RUN5 & R2_5 & E24_5 & AG5).
        rzs HW2 RUN5.
        apply (LATCH (mkFP fr4 cs4) Ak mk2 vmk regs5 loc false false FZ4 INV2' R2_5 Hloc E24_5 ltac:(keep_tac KEEP4)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nfe_loop1_W : forall (j : nat) (fx : FPState) C A m md regs0 fr0 (s nas nalloc n arr nad : Z) (ret0 : word) kR bR Ak mk vmk regs (i : Z) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + NFE_STACK <= s)%Z -> (s <= c_top C)%Z ->
  numa_at C A m nas nalloc n arr -> (n <= 20000)%Z -> (RK_nfe <= kR)%Z -> (RB_nfe <= bR)%Z ->
  (Z.of_nat j = n - i)%Z -> (1 <= i < n)%Z ->
  nfe_inv C A m md s nad (nfe_cl s ret0 regs0 fr0) kR bR 0 Ak mk vmk ->
  nfe_R1 regs s nas nad n i -> nfe_keep regs0 regs -> getr regs0 4 = Z_to_bv 64 TP9 ->
  (forall (fx' : FPState) Ak' mk' vmk' regs', frm_zero (@fp_csr fx') -> nfe_inv C A m md s nad (nfe_cl s ret0 regs0 fr0) kR bR (n - 2) Ak' mk' vmk' ->
      getr regs' 2 = Z_to_bv 64 (s - 128) -> getr regs' 9 = Z_to_bv 64 nad -> nfe_keep regs0 regs' ->
      realizes SEGS (mkCfg (@mkst fx' regs' (0x609a8 : word) mk' al_rom) (with_vmmaps vmk' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (0x60878 : word) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  induction j as [|j IH]; intros fx C A m md regs0 fr0 s nas nalloc n arr nad ret0 kR bR Ak mk vmk regs i S
    FZ CK Hs16 Hlo Hhi NA Hn HkR HbR Hj Hi INV HR1 KEEP H4 HK; [lia|].
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (Hs128 : (128 <= s)%Z) by (unfold NFE_STACK, NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK in Hlo; lia).
  assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  assert (Hlow : (c_top C - LSTK <= s - 128)%Z) by (unfold NFE_STACK, NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK in Hlo; lia).
  pose proof INV as (HW & _).
  destruct (nfe_L1h al_rom fx regs mk s nas nad n i Hs128 Hs64 HR1) as (regs1 & RUN1 & R1_1 & Q1 & Q10 & Q11 & Q12 & AG1).
  rzs HW RUN1.
  apply (nfe_ngf_W fx C A m md regs1 s nas nalloc n arr nad ret0 regs0 fr0 kR bR 0%Z Ak mk vmk i (s - 120)%Z (Z_to_bv 64 0x60888) S FZ CK Hs16 Hlo Hhi NA
           ltac:(lia) Hn ltac:(left; reflexivity) INV Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12).
  intros fx2 mk2 regs2 FZ2 INV2 AG2. replace (Z_to_bv 64 0x60888) with (0x60888 : word) by (apply bv_eq; reflexivity).
  pose proof INV2 as (HW2 & _).
  destruct (W_rdn_win C Ak mk2 _ (s - 120) 4 CK HW2 ltac:(lia) ltac:(cbn; lia)) as (b8 & R8 & _).
  destruct (W_rdn_win C Ak mk2 _ (s - 116) 4 CK HW2 ltac:(lia) ltac:(cbn; lia)) as (b12 & R12 & _).
  assert (R1_2 : nfe_R1 regs2 s nas nad n i) by (r1_tac R1_1).
  assert (KEEP2 : nfe_keep regs0 regs2) by (keep_tac KEEP).
  destruct (nfe_L1a al_rom fx2 regs2 mk2 s b8 b12 FZ2 Hs128 Hs64 R8 R12 (proj1 R1_2)) as (fr3 & cs3 & regs3 & b & RUN3 & FZ3 & E10 & AG3).
  rzs HW2 RUN3.
  destruct (nfe_L1b al_rom (mkFP fr3 cs3) regs3 mk2 b FZ3 E10) as (fr4 & cs4 & regs4 & b' & RUN4 & FZ4 & E10' & AG4).
  rzs HW2 RUN4.
  assert (R1_4 : nfe_R1 regs4 s nas nad n i) by (r1_tac R1_2).
  assert (KEEP4 : nfe_keep regs0 regs4) by (keep_tac KEEP2).
  destruct b'.
  - (* [comment removed for export] *)
    destruct (Z_lt_ge_dec (i + 1) n) as [Hnx|Hlast].
    + destruct (nfe_L1cF al_rom (mkFP fr4 cs4) regs4 mk2 s nas nad n i FZ4 ltac:(lia) Hnx ltac:(lia) R1_4 E10') as (fr5 & cs5 & regs5 & bd & RUN5 & FZ5 & R2_5 & AG5).
      rzs HW2 RUN5.
      apply (nfe_loop2_W (Z.to_nat (n - (i + 1))) (mkFP fr5 cs5) C A m md regs0 fr0 s nas nalloc n arr nad ret0 kR bR Ak mk2 vmk regs5 (i + 1)%Z i bd S FZ5 CK Hs16 Hlo Hhi
               NA Hn HkR HbR ltac:(rewrite Z2Nat.id by lia; reflexivity) ltac:(lia) ltac:(lia)
               ltac:(apply (nfe_inv_weaken _ _ _ _ _ _ _ _ _ 0%Z); [lia | exact INV2]) R2_5 ltac:(keep_tac KEEP4) H4 HK).
    + destruct (nfe_L1cX al_rom (mkFP fr4 cs4) regs4 mk2 s nas nad n i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R1_4 E10') as (regs5 & RUN5 & E2 & E9 & AG5).
      rzs HW2 RUN5.
      apply (HK (mkFP fr4 cs4) Ak mk2 vmk regs5 FZ4); [apply (nfe_inv_weaken _ _ _ _ _ _ _ _ _ 0%Z); [lia | exact INV2] | exact E2 | exact E9 | keep_tac KEEP4].
  - (* [comment removed for export] *)
    destruct (Z_lt_ge_dec (i + 1) n) as [Hnx|Hlast].
    + destruct (nfe_L1cN al_rom (mkFP fr4 cs4) regs4 mk2 s nas nad n i ltac:(lia) Hnx ltac:(lia) R1_4 E10') as (regs5 & RUN5 & R1_5 & AG5).
      rzs HW2 RUN5.
      apply (IH (mkFP fr4 cs4) C A m md regs0 fr0 s nas nalloc n arr nad ret0 kR bR Ak mk2 vmk regs5 (i + 1)%Z S FZ4 CK Hs16 Hlo Hhi NA Hn HkR HbR
               ltac:(lia) ltac:(lia) INV2 R1_5 ltac:(keep_tac KEEP4) H4 HK).
    + destruct (nfe_L1cE al_rom (mkFP fr4 cs4) regs4 mk2 s nas nad n i ltac:(lia) ltac:(lia) ltac:(lia) R1_4 E10') as (regs5 & RUN5 & E2 & E9 & AG5).
      rzs HW2 RUN5.
      apply (HK (mkFP fr4 cs4) Ak mk2 vmk regs5 FZ4); [apply (nfe_inv_weaken _ _ _ _ _ _ _ _ _ 0%Z); [lia | exact INV2] | exact E2 | exact E9 | keep_tac KEEP4].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem numaFindExtrema_W : numaFindExtrema_contract.
Proof.
  intros fx C A m md regs s nas nalloc n arr ret S FZ CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 Hfa0 NA Hn kR bR Hrm HkR HbR HK.
  unfold PC_numaFindExtrema. replace (Z_to_bv 64 0x60738) with (0x60738 : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (Hs128 : (128 <= s)%Z) by (unfold NFE_STACK, NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK in Hlo; lia).
  assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  assert (Hlow : (c_top C - LSTK + NCR_STACK <= s - 128)%Z) by (unfold NFE_STACK, NAN_STACK, NEX_STACK, RNW_STACK, NCR_STACK in *; lia).
  assert (Hlow' : (c_top C - LSTK <= s - 128)%Z) by (unfold NCR_STACK, CALLOC_STACK, ALLOC_STACK in Hlow; lia).
  assert (Hs16' : ((s - 128) mod 16 = 0)%Z) by (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity).
  destruct (numa_at_geom C A m md nas nalloc n arr CK HW NA) as (Gna & TOPna & Garr & TOParr).
  pose proof NA as (R & Hal & _ & _ & _ & Hnal & Hnn & L1 & _ & L2 & _).
  (* [comment removed for export] *)
  destruct (nfe_A al_rom fx regs m s nas n ret FZ Hfa0 Hs128 Hs64 ltac:(lia) ltac:(lia) ltac:(lia) (NUMA_rd_n SEGS m nas nalloc n 1 arr R)
              (W_sok_win C A m md (s - 128) 128 CK HW Hlow' ltac:(cbn; lia)) H2 H1 H10 H11)
    as (fr1 & cs1 & regs1 & RUN1 & FZ1 & Q2 & Q1 & Q10 & Q8 & Q18 & Q20 & AG1).
  rzs HW RUN1.
  set (M1 := NFEF m s ret regs (@fp_regs fx)).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold NFEF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (nfe_cl_NFEF m s ret regs (@fp_regs fx) Hs128 Hs64) as CE1. fold M1 in CE1.
  set (cl := nfe_cl s ret regs (@fp_regs fx)) in *.
  assert (HCL : Forall (fun av : Z * word => (s - 128 <= fst av /\ fst av + 8 <= 2 ^ 64)%Z) cl) by (apply nfe_cl_above; lia).
  assert (Q4 : getr regs1 4 = Z_to_bv 64 TP9) by (csr; reflexivity).
  assert (KEEP1 : nfe_keep regs regs1) by (unfold nfe_keep; repeat split; csr; reflexivity).
  pose proof (grow_cost_mono 0 9 ltac:(lia)) as GM0. change (grow_cost 0) with 0%Z in GM0.
  replace (0x609ec : word) with (Z_to_bv 64 PC_numaCreate) by (apply bv_eq; reflexivity).
  apply (numaCreate_W (mkFP fr1 cs1) C A M1 md regs1 (s - 128)%Z 0%Z (Z_to_bv 64 0x6083c) S CK HW1 Q2 Hs16' Hlow ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10
           ltac:(lia) kR bR Hrm ltac:(unfold RK_nfe, NFE_GROWS in HkR; lia) ltac:(rewrite numa_n0_0; unfold RB_nfe, NFE_GROWS in HbR; lia)).
  intros A2 m2 vm2 regs2 nad arrd HW2 CS2 PM2 R10 (NA2 & LnA & LaA & LEQ) ROOM2. rewrite numa_n0_0 in NA2, ROOM2.
  replace (Z_to_bv 64 0x6083c) with (0x6083c : word) by (apply bv_eq; reflexivity).
  pose proof NA2 as (_ & _ & _ & _ & _ & _ & _ & Ln2 & _ & La2 & _).
  assert (SUB2 : sub_live A A2) by (exact (sub_live_new2 A A2 _ _ _ _ LnA LaA Ln2 La2 LEQ)).
  assert (INV2 : nfe_inv C A m md s nad cl kR bR 0 A2 m2 vm2).
  { split; [exact HW2|]. split; [eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PM2]; lia]|].
    split; [exact (cellsZ_frm C (s - 128) M1 m2 cl CK (proj1 PM2) Hlow' HCL CE1)|]. split; [exact SUB2|].
    exists 0%Z, 0%Z, arrd. split; [unfold NFE_GROWS; lia|]. split; [lia|]. split; [exact NA2|]. split; [exact LnA|]. split; [exact LaA|]. split; [exact LEQ|].
    change (grow_cost 0) with 0%Z. apply (aroom_mono A2 vm2 _ _ _ _ ROOM2); unfold RK_nfe, RB_nfe, NFE_GROWS in *; lia. }
  (* [comment removed for export] *)
  assert (E2 : getr regs2 2 = Z_to_bv 64 (s - 128)) by (csr; reflexivity).
  assert (E8 : getr regs2 8 = Z_to_bv 64 nas) by (csr; reflexivity).
  assert (E18 : getr regs2 18 = Z_to_bv 64 n) by (csr; reflexivity).
  assert (E20 : getr regs2 20 = Z_to_bv 64 0) by (csr; reflexivity).
  assert (KEEP2 : nfe_keep regs regs2) by (keep_tac KEEP1).
  destruct (nfe_B1 al_rom (mkFP fr1 cs1) regs2 m2 s nas nad n Hs128 Hs64 E2 R10 E8 E18 E20) as (regs3 & RUN3 & P2 & P8 & P9 & P18 & P19 & P1 & P10 & P11 & P12 & AG3).
  rzs HW2 RUN3.
  apply (nfe_ngf_W (mkFP fr1 cs1) C A m md regs3 s nas nalloc n arr nad ret regs (@fp_regs fx) kR bR 0%Z A2 m2 vm2 0%Z (s - 116)%Z (Z_to_bv 64 0x6086c) S FZ1 CK Hs16 Hlo Hhi NA
           ltac:(lia) ltac:(lia) ltac:(right; reflexivity) INV2 P1 ltac:(red; apply bv_eq; reflexivity) P10 P11 P12).
  intros fx4 mk4 regs4 FZ4 INV4 AG4. replace (Z_to_bv 64 0x6086c) with (0x6086c : word) by (apply bv_eq; reflexivity).
  pose proof INV4 as (HW4 & _).
  assert (F2 : getr regs4 2 = Z_to_bv 64 (s - 128)) by (csr; reflexivity).
  assert (F8 : getr regs4 8 = Z_to_bv 64 nas) by (csr; reflexivity).
  assert (F9 : getr regs4 9 = Z_to_bv 64 nad) by (csr; reflexivity).
  assert (F18 : getr regs4 18 = Z_to_bv 64 n) by (csr; reflexivity).
  assert (F19 : getr regs4 19 = Z_to_bv 64 0) by (csr; reflexivity).
  assert (KEEP4 : nfe_keep regs regs4) by (keep_tac KEEP2).
  destruct (nfe_B2 al_rom fx4 regs4 mk4 s nas nad n ltac:(lia) F2 F8 F9 F18 F19) as (regs5 & RUN5 & R1_5 & AG5).
  rzs HW4 RUN5.
  apply (nfe_loop1_W (Z.to_nat (n - 1)) fx4 C A m md regs (@fp_regs fx) s nas nalloc n arr nad ret kR bR A2 mk4 vm2 regs5 1%Z S FZ4 CK Hs16 Hlo Hhi NA ltac:(lia) HkR HbR
           ltac:(rewrite Z2Nat.id by lia; reflexivity) ltac:(lia) INV4 R1_5 ltac:(keep_tac KEEP4) H4).
  (* [comment removed for export] *)
  intros fx6 A6 mk6 vm6 regs6 FZ6 (HW6 & PM6 & CE6 & SUB6 & k & c & arrd6 & Hk & Hc & NA6 & LnA6 & LaA6 & LEQ6 & ROOM6) G2 G9 KEEP6.
  subst cl. unfold nfe_cl in CE6. cbn [cellsZ] in CE6.
  destruct CE6 as (C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & CF8 & CF9 & CF18 & _).
  destruct (nfe_exit al_rom fx6 regs6 mk6 s nad ret _ _ _ _ _ _ _ _ _ _ _ _ _ Hs128 Hs64 Hret C1 C8 C9 C18 C19 C20 C21 C22 C23 C24 C25 CF8 CF9 CF18 G2 G9)
    as (fr7 & regs7 & RUN7 & V2 & V10 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & AG7).
  rzs HW6 RUN7.
  pose proof (grow_cost_mono k 9 ltac:(unfold NFE_GROWS in Hk; lia)) as GMk.
  apply (HK (mkFP fr7 (@fp_csr fx6)) A6 mk6 vm6 regs7 nad (50 * 2 ^ k)%Z c arrd6 FZ6 HW6).
  - pose proof KEEP6 as (K3 & K4 & K26 & K27). apply cs_kept_intro; csr; reflexivity.
  - exact PM6.
  - exact V10.
  - exact NA6.
  - exact LnA6.
  - exact LaA6.
  - exact LEQ6.
  - apply (aroom_mono A6 vm6 _ _ _ _ ROOM6); unfold RK_nfe, RB_nfe, NFE_GROWS, RK_numa in *; lia.
Qed.

End Nfe.
