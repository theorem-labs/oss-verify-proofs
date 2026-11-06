(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure AllocCredit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17LeptStderr O17LeptBase.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17CL7a.
Import O17CL7a.O17LeptErr. Import O17CL7a.O17LeptKernSegs2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17LeptDeser O17LeptKernC2d O17LeptKernCreate O17_code_15000_16000 O17_code_16000_17000.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptCredit LeptRoomK.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section KernDestroy.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LL17} {P16 : O17Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition kobj (C : lctx) (A : AS) (m : word -> option byte) (kel arr h w : Z) (rows : Z -> Z) : Prop :=
  (1 <= kel)%Z /\ (kel + 24 <= alloc_top (c_vm C))%Z /\ live A (Z_to_bv 64 kel) = Some 24%Z /\ live (c_A0 C) (Z_to_bv 64 kel) = None /\
  rdn SEGS m (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) /\
  rdn SEGS m (Z_to_bv 64 (kel + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) /\
  rdn SEGS m (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr)) /\
  (1 <= arr)%Z /\ (arr + 8 * h <= alloc_top (c_vm C))%Z /\ kel <> arr /\ live A (Z_to_bv 64 arr) = Some (8 * h)%Z /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\
  (forall i, (0 <= i < h)%Z ->
      (1 <= rows i)%Z /\ (rows i + 4 * w <= alloc_top (c_vm C))%Z /\ rows i <> arr /\ rows i <> kel /\
      live A (Z_to_bv 64 (rows i)) = Some (4 * w)%Z /\ live (c_A0 C) (Z_to_bv 64 (rows i)) = None /\
      rdn SEGS m (Z_to_bv 64 (arr + 8 * i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (rows i)))) /\
  (forall i j, (0 <= i < h)%Z -> (0 <= j < h)%Z -> i <> j -> rows i <> rows j).

Lemma kern_kobj : forall C A0 A m kel arr h w rows, kern C A0 A m kel arr h w rows -> kobj C A m kel arr h w rows.
Proof.
  intros C A0 A m kel arr h w rows (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & ROWS & DIST & RQ).
  do 12 (split; [assumption|]). split; [|exact DIST].
  intros i Hi. destruct (ROWS i Hi) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma kdcells_FRM : forall C M M' s ret s0v s1v s2v s3v, Cok C -> FRM C (s - 48) M M' ->
  (c_top C - LSTK <= s - 48)%Z -> (s <= c_top C)%Z ->
  kdcells M s ret s0v s1v s2v s3v -> kdcells M' s ret s0v s1v s2v s3v.
Proof.
  intros C M M' s ret s0v s1v s2v s3v CK F Hlo Hhi (C1 & C2 & C3 & C4 & C5).
  pose proof CK as [T1 T2 T3 T4 T5]. unfold kdcells.
  rewrite !(FRM_rdn16 C (s - 48) M M' _ _ CK F) by lia. repeat split; assumption.
Qed.

Lemma kd_rdn_pp : forall C M M' (s pp : Z) bs, Cok C -> FRM C (s - 48) M M' -> (c_top C - LSTK <= s - 48)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  rdn SEGS M (Z_to_bv 64 pp) 8 = Some bs -> rdn SEGS M' (Z_to_bv 64 pp) 8 = Some bs.
Proof.
  intros C M M' s pp bs CK F Hlo Hpp Hhi R. pose proof CK as [T1 T2 T3 T4 T5]. rewrite (FRM_rdn16 C (s - 48) M M' pp 8 CK F) by (cbn; lia). exact R.
Qed.

#[local] Definition kd_rest : list (bv 5) := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Definition KDK (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s pp kel arr h : Z) (rows : Z -> Z) (S : TSet) (kR bR : Z) : Prop :=
  forall A' m' vm' r, W C A' m' (with_vmmaps vm' md) ->
    live A' (Z_to_bv 64 kel) = Some 24%Z -> live A' (Z_to_bv 64 arr) = None -> (forall i, (0 <= i < h)%Z -> live A' (Z_to_bv 64 (rows i)) = None) ->
    (forall q, q <> Z_to_bv 64 arr -> (forall i, (0 <= i < h)%Z -> q <> Z_to_bv 64 (rows i)) -> live A' q = live A q) ->
    POSTM C (c_A0 C) s m m' -> kdcells m' s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ->
    rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 kel)) ->
    getr r 2 = Z_to_bv 64 (s - 48) -> getr r 8 = Z_to_bv 64 pp -> getr r 9 = Z_to_bv 64 kel -> (forall x, In x kd_rest -> getr r x = getr regs x) ->
    aroom A' vm' kR bR ->
    realizes SEGS (mkCfg (mkst r (0x157ac : word) m' al_rom) (with_vmmaps vm' md)) S.

(* [comment removed for export] *)
Lemma kd_loop : forall (k : nat) C A m md regs (s pp kel arr h w : Z) (rows : Z -> Z) (S : TSet) (kR bR : Z) A1 M1 vm1 r (i : Z),
  Cok C -> KDK C A m md regs s pp kel arr h rows S kR bR ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x30520 ->
  (1 <= h < 2 ^ 31)%Z -> (0 <= w)%Z -> (Z.of_nat k = h - 1 - i)%Z -> (0 <= i < h)%Z ->
  (* [comment removed for export] *)
  (1 <= kel)%Z /\ (kel + 24 <= alloc_top (c_vm C))%Z /\ live (c_A0 C) (Z_to_bv 64 kel) = None /\
  (1 <= arr)%Z /\ (arr + 8 * h <= alloc_top (c_vm C))%Z /\ kel <> arr /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\
  (forall j, (0 <= j < h)%Z -> (1 <= rows j)%Z /\ (rows j + 4 * w <= alloc_top (c_vm C))%Z /\ rows j <> arr /\ rows j <> kel /\ live (c_A0 C) (Z_to_bv 64 (rows j)) = None) /\
  (forall j j', (0 <= j < h)%Z -> (0 <= j' < h)%Z -> j <> j' -> rows j <> rows j') ->
  (* [comment removed for export] *)
  W C A1 M1 (with_vmmaps vm1 md) -> POSTM C (c_A0 C) s m M1 -> aroom A1 vm1 kR bR ->
  kdcells M1 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ->
  rdn SEGS M1 (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 kel)) ->
  live A1 (Z_to_bv 64 kel) = Some 24%Z /\ live A1 (Z_to_bv 64 arr) = Some (8 * h)%Z /\
  rdn SEGS M1 (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) /\
  rdn SEGS M1 (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr)) /\
  (forall j, (i <= j < h)%Z -> live A1 (Z_to_bv 64 (rows j)) = Some (4 * w)%Z /\ rdn SEGS M1 (Z_to_bv 64 (arr + 8 * j)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (rows j)))) /\
  (forall j, (0 <= j < i)%Z -> live A1 (Z_to_bv 64 (rows j)) = None) /\
  (forall q, q <> Z_to_bv 64 arr -> (forall j, (0 <= j < h)%Z -> q <> Z_to_bv 64 (rows j)) -> live A1 q = live A q) ->
  getr r 2 = Z_to_bv 64 (s - 48) -> getr r 8 = Z_to_bv 64 pp -> getr r 9 = Z_to_bv 64 kel -> getr r 18 = Z_to_bv 64 (8 * i) -> getr r 19 = Z_to_bv 64 i ->
  getr r 4 = Z_to_bv 64 0x30520 -> (forall x, In x kd_rest -> getr r x = getr regs x) ->
  realizes SEGS (mkCfg (mkst r (0x15784 : word) M1 al_rom) (with_vmmaps vm1 md)) S.
Proof.
  induction k as [|k IH]; intros C A m md regs s pp kel arr h w rows S kR bR A1 M1 vm1 r i CK HK Hs16 Hlo Hpp Hpphi H4 Hh Hw Hk Hi
    (Gk & TOPk & Lk0 & Ga & TOPa & NEka & La0 & ROWB & DIST) HW PM HRM CE Rpp (Lk & La & Rsy & Rarr & ROWS & DONE & RQ) R2 R8 R9 R18 R19 R4 RR;
    pose proof CK as [T1 T2 T3 T4 T5]; laypins; cbn [fst snd ll_img LL17] in *; unfold ALLOC_STACK in Hlo; unfold kd_rest in RR;
    pose proof (alloc_top_lt (c_vm C)) as AT; unfold two_pow_64 in AT;
    destruct (ROWB i ltac:(lia)) as (Gi & TOPi & NEia & NEik & Li0); destruct (ROWS i ltac:(lia)) as [Li Ri];
    destruct (kd_H al_rom r M1 kel arr h i (rows i) Gk ltac:(lia) Ga ltac:(lia) ltac:(lia) ltac:(lia) Rarr Ri R9 R18 R19)
      as (r1 & RUN1 & Q2 & Q1 & Q10 & Q8 & Q9 & Q18 & Q19 & AG1);
    (eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]);
    replace (0x16604 : word) with (Z_to_bv 64 0x16604) by (apply bv_eq; reflexivity);
    (apply (W_free16 C A1 M1 _ r1 (Z_to_bv 64 (rows i)) (Z_to_bv 64 0x15794) (4 * w) (s - 48) S CK HW Q10 Li Li0 Q1
             ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite (AG1 4) by (cbv; intuition discriminate); exact R4)
             ltac:(rewrite Q2; exact R2) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)));
    intros A2 m2 vm2 r2 HW2 CS2 Li2 LEQ2 PM2 HRT2; rewrite ?with_vmmaps_twice in HW2 |- *;
    pose proof (HRT2 kR bR HRM (proj1 (aroom_nonneg _ _ _ _ HRM)) (proj2 (aroom_nonneg _ _ _ _ HRM))) as HRM2; rewrite !Z.sub_0_r in HRM2;
    replace (Z_to_bv 64 0x15794) with (0x15794 : word) by (apply bv_eq; reflexivity);
    assert (NEki : Z_to_bv 64 kel <> Z_to_bv 64 (rows i)) by (apply zbv_ne; lia);
    assert (NEai : Z_to_bv 64 arr <> Z_to_bv 64 (rows i)) by (apply zbv_ne; lia);
    assert (NEji : forall j, (0 <= j < h)%Z -> j <> i -> Z_to_bv 64 (rows j) <> Z_to_bv 64 (rows i))
      by (intros j Hj NE; destruct (ROWB j Hj) as (? & ? & _); apply zbv_ne; [lia | lia | apply (DIST j i); lia]);
    assert (Lk2 : live A2 (Z_to_bv 64 kel) = Some 24%Z) by (rewrite (LEQ2 _ NEki); exact Lk);
    assert (La2 : live A2 (Z_to_bv 64 arr) = Some (8 * h)%Z) by (rewrite (LEQ2 _ NEai); exact La);
    assert (PM2' : POSTM C (c_A0 C) s m m2)
      by (eapply POSTM_trans; [exact PM|]; apply (POSTM_sub C (c_A0 C) A2); [exact (w_keep _ _ _ _ HW2) | eapply POSTM_mono; [|exact PM2]; lia]);
    pose proof (kdcells_FRM C M1 m2 s _ _ _ _ _ CK (proj1 PM2) ltac:(lia) ltac:(lia) CE) as CE2;
    pose proof (kd_rdn_pp C M1 m2 s pp _ CK (proj1 PM2) ltac:(lia) Hpp Hpphi Rpp) as Rpp2;
    assert (Rsy2 : rdn SEGS m2 (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)))
      by (rewrite <- Rsy; apply rdn_ext; rewrite u_Z2bv by lia; [lia|]; intros x Hx; exact (LIVK_at A2 M1 m2 kel 24 x (proj2 PM2) Lk2 ltac:(lia) ltac:(lia) ltac:(lia)));
    assert (Rarr2 : rdn SEGS m2 (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr)))
      by (rewrite <- Rarr; apply rdn_ext; rewrite u_Z2bv by lia; [lia|]; intros x Hx; exact (LIVK_at A2 M1 m2 kel 24 x (proj2 PM2) Lk2 ltac:(lia) ltac:(lia) ltac:(lia)));
    assert (DONE2 : forall j, (0 <= j < i + 1)%Z -> live A2 (Z_to_bv 64 (rows j)) = None)
      by (intros j Hj; destruct (Z.eq_dec j i) as [->|NE]; [exact Li2|]; rewrite (LEQ2 _ (NEji j ltac:(lia) NE)); apply DONE; lia);
    assert (RQ2 : forall q, q <> Z_to_bv 64 arr -> (forall j, (0 <= j < h)%Z -> q <> Z_to_bv 64 (rows j)) -> live A2 q = live A q)
      by (intros q NQa NQr; rewrite (LEQ2 q (NQr i ltac:(lia))); exact (RQ q NQa NQr));
    assert (E9 : getr r2 9 = Z_to_bv 64 kel) by (csr; reflexivity);
    assert (E18 : getr r2 18 = Z_to_bv 64 (8 * i)) by (csr; reflexivity);
    assert (E19 : getr r2 19 = Z_to_bv 64 i) by (csr; reflexivity).
  - (* [comment removed for export] *)
    destruct (kd_Nl al_rom r2 m2 kel arr h i Gk ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Rsy2 Rarr2 E9 E18 E19) as (r3 & RUN3 & P2 & P1 & P10 & P8 & P9 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
    replace (0x16604 : word) with (Z_to_bv 64 0x16604) by (apply bv_eq; reflexivity).
    apply (W_free16 C A2 m2 _ r3 (Z_to_bv 64 arr) (Z_to_bv 64 0x157ac) (8 * h) (s - 48) S CK HW2 P10 La2 La0 P1
             ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity)
             ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A3 m3 vm3 r4 HW3 CS3 La3 LEQ3 PM3 HRT3. rewrite ?with_vmmaps_twice in HW3 |- *.
    replace (Z_to_bv 64 0x157ac) with (0x157ac : word) by (apply bv_eq; reflexivity).
    assert (NEka' : Z_to_bv 64 kel <> Z_to_bv 64 arr) by (apply zbv_ne; lia).
    apply (HK A3 m3 vm3 r4 HW3).
    + rewrite (LEQ3 _ NEka'). exact Lk2.
    + exact La3.
    + intros j Hj. destruct (ROWB j Hj) as (G1 & G2 & G3 & _). rewrite (LEQ3 (Z_to_bv 64 (rows j)) ltac:(apply zbv_ne; lia)). apply DONE2. lia.
    + intros q NQa NQr. rewrite (LEQ3 q NQa). exact (RQ2 q NQa NQr).
    + eapply POSTM_trans; [exact PM2'|]. apply (POSTM_sub C (c_A0 C) A3); [exact (w_keep _ _ _ _ HW3) | eapply POSTM_mono; [|exact PM3]; lia].
    + exact (kdcells_FRM C m2 m3 s _ _ _ _ _ CK (proj1 PM3) ltac:(lia) ltac:(lia) CE2).
    + exact (kd_rdn_pp C m2 m3 s pp _ CK (proj1 PM3) ltac:(lia) Hpp Hpphi Rpp2).
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + unfold kd_rest; rest_solve.
    + pose proof (HRT3 kR bR HRM2 (proj1 (aroom_nonneg _ _ _ _ HRM2)) (proj2 (aroom_nonneg _ _ _ _ HRM2))) as X. rewrite !Z.sub_0_r in X. exact X.
  - (* [comment removed for export] *)
    destruct (kd_Nn al_rom r2 m2 kel h i Gk ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Rsy2 E9 E18 E19) as (r3 & RUN3 & P2 & P18 & P19 & P8 & P9 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
    apply (IH C A m md regs s pp kel arr h w rows S kR bR A2 m2 vm2 r3 (i + 1)%Z CK HK Hs16 ltac:(unfold ALLOC_STACK; lia) Hpp Hpphi H4 Hh Hw ltac:(lia) ltac:(lia)
             (conj Gk (conj TOPk (conj Lk0 (conj Ga (conj TOPa (conj NEka (conj La0 (conj ROWB DIST)))))))) HW2 PM2' HRM2 CE2 Rpp2); try (csr; reflexivity).
    + split; [exact Lk2|]. split; [exact La2|]. split; [exact Rsy2|]. split; [exact Rarr2|]. split; [|split; [exact DONE2 | exact RQ2]].
      intros j Hj. destruct (ROWS j ltac:(lia)) as [G5 G7].
      split; [rewrite (LEQ2 _ (NEji j ltac:(lia) ltac:(lia))); exact G5|].
      rewrite <- G7. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx.
      exact (LIVK_at A2 M1 m2 arr (8 * h) x (proj2 PM2) La2 ltac:(lia) ltac:(lia) ltac:(lia)).
    + unfold kd_rest; rest_solve.
Qed.

(* [comment removed for export] *)
Theorem kernelDestroy_null_W : forall C A m md regs (s pp : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pp ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C (c_A0 C) s m m' ->
     rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x1574c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp ret S CK HW H2 Hs16 Hlo Hpp Hpphi H1 Hret H10 Rpp HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL17] in *. unfold ALLOC_STACK in Hlo.
  destruct (kd_A0 al_rom regs m s pp ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp H2 H1 H10) as (r1 & RUN1 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP : W C A (KDF m s ret regs) md /\ POSTM C (c_A0 C) s m (KDF m s ret regs)) by (unfold KDF; wp_win CK).
  destruct WP as [HW1 PM1].
  apply (HK _ r1 HW1).
  - apply cs_kept_intro; csr; reflexivity.
  - exact PM1.
  - rewrite <- Rpp. unfold KDF. repeat rdn_peel1. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem kernelDestroy_W : forall C A m md regs (s pp kel arr h w : Z) (rows : Z -> Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x30520 -> getr regs 10 = Z_to_bv 64 pp ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 kel)) ->
  kobj C A m kel arr h w rows -> (1 <= h < 2 ^ 31)%Z -> (0 <= w)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 kel) = None -> live A' (Z_to_bv 64 arr) = None -> (forall i, (0 <= i < h)%Z -> live A' (Z_to_bv 64 (rows i)) = None) ->
     (forall q, q <> Z_to_bv 64 kel -> q <> Z_to_bv 64 arr -> (forall i, (0 <= i < h)%Z -> q <> Z_to_bv 64 (rows i)) -> live A' q = live A q) ->
     POSTM C (c_A0 C) (pp + 8) m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
     aroom A' vm' kR bR ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x1574c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp kel arr h w rows ret S CK HW H2 Hs16 Hlo Hpp Hpphi H1 Hret H4 H10 Rpp KO Hh Hw kR bR HRM HK.
  pose proof KO as (Gk & TOPk & Lk & Lk0 & Rsy & Rsx & Rarr & Ga & TOPa & NEka & La & La0 & ROWS & DIST).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL17] in *. unfold ALLOC_STACK in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  destruct (kd_A1 al_rom regs m s pp kel h ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Gk ltac:(lia) Hh
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp Rsy H2 H1 H10) as (r1 & RUN1 & Q2 & Q8 & Q9 & Q18 & Q19 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := KDF m s ret regs).
  assert (WP : W C A M1 md /\ POSTM C (c_A0 C) s m M1) by (subst M1; unfold KDF; wp_win CK).
  destruct WP as [HW1 PM1].
  assert (OUT1 : forall x : word, ~ (s - 48 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold KDF. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (LOW : forall (a : Z) (n : nat) bs, (0 <= a)%Z -> (a + Z.of_nat n <= s - 48)%Z -> rdn SEGS m (Z_to_bv 64 a) n = Some bs -> rdn SEGS M1 (Z_to_bv 64 a) n = Some bs).
  { intros a n bs Ha Hn R. rewrite <- R. destruct n; [reflexivity|]. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply OUT1. lia. }
  pose proof (kdcells_KDF m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1. rewrite <- H1 in CE1.
  assert (Rpp1 : rdn SEGS M1 (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 kel))).
  { rewrite <- Rpp. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. apply OUT1. cbn in Hx. lia. }
  rewrite <- (with_vmmaps_same md) in HW1 |- *.
  (* [comment removed for export] *)
  assert (HKDK : KDK C A m md regs s pp kel arr h rows S kR bR).
  { intros A' m' vm' r HW' Lk' La' LR' RQ' PM' CE' Rpp' R2' R8' R9' RR' HRM'. unfold kd_rest in RR'. rewrite ?with_vmmaps_twice in HW' |- *.
    destruct (kd_P al_rom r m' (Z_to_bv 64 kel) R9') as (r5 & RUN5 & V2 & V1 & V10 & V8 & V9 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN5 |].
    replace (0x16604 : word) with (Z_to_bv 64 0x16604) by (apply bv_eq; reflexivity).
    apply (W_free16 C A' m' _ r5 (Z_to_bv 64 kel) (Z_to_bv 64 0x157b4) 24 (s - 48) S CK HW' V10 Lk' Lk0 V1
             ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite (AG5 4) by (cbv; intuition discriminate); rewrite (RR' 4) by in_lit; exact H4)
             ltac:(rewrite V2; exact R2') ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A5 m5 vm5 r6 HW5 CS5 Lk5 LEQ5 PM5 HRT5. rewrite ?with_vmmaps_twice in HW5 |- *.
    replace (Z_to_bv 64 0x157b4) with (0x157b4 : word) by (apply bv_eq; reflexivity).
    pose proof (kdcells_FRM C m' m5 s _ _ _ _ _ CK (proj1 PM5) ltac:(lia) ltac:(lia) CE') as CE5.
    destruct (kd_Q al_rom r6 m5 s pp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(rewrite H1; exact Hret) (W_sok_win C A5 m5 _ pp 8 CK HW5 ltac:(lia) ltac:(cbn; lia)) CE5 ltac:(csr; reflexivity) ltac:(csr; reflexivity))
      as (r7 & RUN7 & Z2 & Z1 & Z8 & Z9 & Z18 & Z19 & AG7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN7 |].
    assert (PMall : POSTM C (c_A0 C) s m m5).
    { eapply POSTM_trans; [exact PM'|]. apply (POSTM_sub C (c_A0 C) A5); [exact (w_keep _ _ _ _ HW5) | eapply POSTM_mono; [|exact PM5]; lia]. }
    assert (WP : W C A5 (wbytes m5 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) (with_vmmaps vm5 md) /\
                 POSTM C (c_A0 C) (pp + 8) m (wbytes m5 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0)))).
    { apply (WP_win C A5 (c_A0 C) m m5 _ _ _ (pp + 8) CK); [| exact (w_keep _ _ _ _ HW5) | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia].
      split; [exact HW5|]. eapply POSTM_mono; [|exact PMall]. lia. }
    destruct WP as [HW6 PM6]. rewrite H1.
    apply (HK A5 _ vm5 r7 HW6).
    - apply cs_kept_intro; csr; reflexivity.
    - exact Lk5.
    - rewrite (LEQ5 (Z_to_bv 64 arr) ltac:(apply not_eq_sym; apply zbv_ne; lia)). exact La'.
    - intros i Hi. destruct (ROWS i Hi) as (G1 & G2 & G3 & G4 & _). rewrite (LEQ5 (Z_to_bv 64 (rows i)) ltac:(apply zbv_ne; lia)). exact (LR' i Hi).
    - intros q NQk NQa NQr. rewrite (LEQ5 q NQk). exact (RQ' q NQa NQr).
    - exact PM6.
    - apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
    - pose proof (HRT5 kR bR HRM' (proj1 (aroom_nonneg _ _ _ _ HRM')) (proj2 (aroom_nonneg _ _ _ _ HRM'))) as X. rewrite !Z.sub_0_r in X. exact X. }
  apply (kd_loop (Z.to_nat (h - 1)) C A m md regs s pp kel arr h w rows S kR bR A M1 (m_vmmaps md) r1 0 CK HKDK Hs16 ltac:(unfold ALLOC_STACK; lia) Hpp Hpphi H4 Hh Hw
           ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia)).
  - split; [exact Gk|]. split; [exact TOPk|]. split; [exact Lk0|]. split; [exact Ga|]. split; [exact TOPa|]. split; [exact NEka|]. split; [exact La0|]. split; [|exact DIST].
    intros j Hj. destruct (ROWS j Hj) as (G1 & G2 & G3 & G4 & G5 & G6 & G7). repeat split; assumption.
  - exact HW1.
  - exact PM1.
  - exact HRM.
  - exact CE1.
  - exact Rpp1.
  - split; [exact Lk|]. split; [exact La|]. split; [apply (LOW kel 4%nat); [lia | cbn; lia | exact Rsy]|]. split; [apply (LOW (kel + 16)%Z 8%nat); [lia | cbn; lia | exact Rarr]|].
    split; [|split; [intros j Hj; lia | intros q _ _; reflexivity]].
    intros j Hj. destruct (ROWS j ltac:(lia)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7). split; [exact G5|]. apply (LOW (arr + 8 * j)%Z 8%nat); [lia | cbn; lia | exact G7].
  - exact Q2.
  - exact Q8.
  - exact Q9.
  - rewrite Q18. reflexivity.
  - exact Q19.
  - rewrite (AG1 4) by (cbv; intuition discriminate). exact H4.
  - unfold kd_rest; rest_solve.
Qed.

End KernDestroy.
