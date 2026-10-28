(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure AllocCredit.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptBaseK V2LeptErr V2KernUb V2LeptKernSegs2 V2LeptKernCreateS V2_code_kern.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptCredit LeptRoomK.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section KernDestroy.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
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
  intros C A0 A m kel arr h w rows (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19).
  refine (conj K1 (conj K2 (conj K4 (conj K6 (conj K7 (conj K8 (conj K9 (conj K10 (conj K11 (conj K13 (conj K14 (conj K16 (conj _ K18))))))))))))).
  intros j Hj. destruct (K17 j Hj) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9). repeat split; assumption.
Qed.

Lemma livk_rdn : forall A M M' (p k a : Z) (n : nat), LIVK A M M' -> live A (Z_to_bv 64 p) = Some k ->
  (0 <= p)%Z -> (p + k < 2 ^ 64)%Z -> (p <= a)%Z -> (a + Z.of_nat n <= p + k)%Z ->
  rdn SEGS M' (Z_to_bv 64 a) n = rdn SEGS M (Z_to_bv 64 a) n.
Proof.
  intros A M M' p k a n HL Lp Hp Hpk Ha Han. apply rdn_ext; [rewrite u_Z2bv by lia; lia|].
  intros x Hx. rewrite u_Z2bv in Hx by lia.
  pose proof (HL (Z_to_bv 64 p) k (u x - p)%Z Lp ltac:(lia)) as E. unfold at_ in E. rewrite u_Z2bv in E by lia.
  replace (p + (u x - p))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E.
Qed.

(* [comment removed for export] *)
Lemma kdcells_FRM : forall C M M' s ret s0v s1v s2v s3v, Cok C -> FRM C (s - 48) M M' ->
  (c_top C - LSTK <= s - 48)%Z -> (s <= c_top C)%Z ->
  kdcells M s ret s0v s1v s2v s3v -> kdcells M' s ret s0v s1v s2v s3v.
Proof.
  intros C M M' s ret s0v s1v s2v s3v CK F Hlo Hhi (C1 & C2 & C3 & C4 & C5).
  pose proof CK as [T1 T2 T3 T4 T5]. unfold kdcells.
  rewrite !(FRM_rdn16 C (s - 48) M M' _ 8 CK F) by (cbn; lia). repeat split; assumption.
Qed.

Lemma kd_rdn_pp : forall C M M' (s pp : Z) bs, Cok C -> FRM C (s - 48) M M' -> (c_top C - LSTK <= s - 48)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  rdn SEGS M (Z_to_bv 64 pp) 8 = Some bs -> rdn SEGS M' (Z_to_bv 64 pp) 8 = Some bs.
Proof.
  intros C M M' s pp bs CK F Hlo Hpp Hpphi R. pose proof CK as [T1 T2 T3 T4 T5].
  rewrite (FRM_rdn16 C (s - 48) M M' pp 8 CK F) by (cbn; lia). exact R.
Qed.

#[local] Definition kd_rest : list (bv 5) := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Local Ltac kd_rest_solve :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; unfold kd_rest in Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]); destruct Hx.

(* [comment removed for export] *)
Definition KDK (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s pp kel arr h : Z) (rows : Z -> Z) (S : TSet) (kR bR : Z) : Prop :=
  forall A' m' vm' r, W C A' m' (with_vmmaps vm' md) ->
    live A' (Z_to_bv 64 kel) = Some 24%Z -> live A' (Z_to_bv 64 arr) = None -> (forall i, (0 <= i < h)%Z -> live A' (Z_to_bv 64 (rows i)) = None) ->
    (forall q, q <> Z_to_bv 64 arr -> (forall i, (0 <= i < h)%Z -> q <> Z_to_bv 64 (rows i)) -> live A' q = live A q) ->
    POSTM C (c_A0 C) s m m' -> kdcells m' s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ->
    rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 kel)) ->
    getr r 2 = Z_to_bv 64 (s - 48) -> getr r 8 = Z_to_bv 64 pp -> getr r 9 = Z_to_bv 64 kel -> (forall x, In x kd_rest -> getr r x = getr regs x) ->
    aroom A' vm' kR bR ->
    realizes SEGS (mkCfg (mkst r (0x38604 : word) m' al_rom) (with_vmmaps vm' md)) S.

(* [comment removed for export] *)
Lemma kd_loop : forall (k : nat) C A m md regs (s pp kel arr h w : Z) (rows : Z -> Z) (S : TSet) (kR bR : Z) A1 M1 vm1 r (i : Z),
  Cok C -> KDK C A m md regs s pp kel arr h rows S kR bR ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x56270 ->
  (1 <= h < 2 ^ 31)%Z -> (0 <= w)%Z -> (Z.of_nat k = h - 1 - i)%Z -> (0 <= i < h)%Z ->
  (* [comment removed for export] *)
  (1 <= kel)%Z /\ (kel + 24 <= alloc_top (c_vm C))%Z /\ live (c_A0 C) (Z_to_bv 64 kel) = None /\
  (1 <= arr)%Z /\ (arr + 8 * h <= alloc_top (c_vm C))%Z /\ (arr mod 8 = 0)%Z /\ kel <> arr /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\
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
  getr r 4 = Z_to_bv 64 0x56270 -> (forall x, In x kd_rest -> getr r x = getr regs x) ->
  realizes SEGS (mkCfg (mkst r (0x385b8 : word) M1 al_rom) (with_vmmaps vm1 md)) S.
Proof.
  induction k as [|k IH]; intros C A m md regs s pp kel arr h w rows S kR bR A1 M1 vm1 r i
    CK HK Hs16 Hlo Hpp Hpphi H4 Hh Hw Hk Hi STAT HW1 PM1 Hroom1 CE1 Rpp1 DYN E2 E8 E9 E18 E19 E4 ER.
  all: pose proof CK as [T1 T2 T3 T4 T5]; pose proof LSTK_val as HLS; unfold ALLOC_STACK in Hlo; unfold kd_rest in ER;
  pose proof STAT as (Gk & TOPk & L0k & Ga & TOPa & ALa & NEka & L0a & ROWS & DIST);
  destruct DYN as (Lk & La & Rh & Ra & DROWS & FREED & LEQ);
  destruct (DROWS i ltac:(lia)) as (Lr & Rr); destruct (ROWS i Hi) as (Gr & TOPr & NEra & NErk & L0r);
  destruct (kd_H al_rom r M1 kel arr h i (rows i) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALa ltac:(lia) ltac:(lia) Ra Rr E9 E18 E19)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q8 & Q9 & Q18 & Q19 & AG1);
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN1 |];
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x56270) by (csr; reflexivity);
  assert (Q2' : getr r1 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity);
  replace (0x3c230 : word) with (Z_to_bv 64 0x3c230) by (apply bv_eq; reflexivity);
  apply (W_free16 C A1 M1 _ r1 (Z_to_bv 64 (rows i)) (Z_to_bv 64 0x385ec) (4 * w) (s - 48) S CK HW1 Q10 Lr L0r Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia));
  intros A2 m2 vm2 r2 HWa CSa La2 LEQa PMa HRTa; rewrite ?with_vmmaps_twice in HWa |- *;
  replace (Z_to_bv 64 0x385ec) with (0x385ec : word) by (apply bv_eq; reflexivity);
  assert (NEkr : Z_to_bv 64 kel <> Z_to_bv 64 (rows i)) by (apply zneq_w; lia);
  assert (NEar : Z_to_bv 64 arr <> Z_to_bv 64 (rows i)) by (apply zneq_w; lia);
  assert (Lk2 : live A2 (Z_to_bv 64 kel) = Some 24%Z) by (rewrite (LEQa _ NEkr); exact Lk);
  assert (La2' : live A2 (Z_to_bv 64 arr) = Some (8 * h)%Z) by (rewrite (LEQa _ NEar); exact La);
  assert (Rh2 : rdn SEGS m2 (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)))
    by (rewrite (livk_rdn A2 M1 m2 kel 24 kel 4 (proj2 PMa) Lk2) by (cbn; lia); exact Rh);
  assert (Ra2 : rdn SEGS m2 (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr)))
    by (rewrite (livk_rdn A2 M1 m2 kel 24 (kel + 16) 8 (proj2 PMa) Lk2) by (cbn; lia); exact Ra);
  assert (CE2 : kdcells m2 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19))
    by (eapply kdcells_FRM; [exact CK | exact (proj1 PMa) | lia | lia | exact CE1]);
  assert (Rpp2 : rdn SEGS m2 (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 kel)))
    by (apply (kd_rdn_pp C M1 m2 s pp _ CK (proj1 PMa)); [lia | lia | lia | exact Rpp1]);
  assert (PM2 : POSTM C (c_A0 C) s m m2)
    by (eapply POSTM_trans; [exact PM1|]; apply (POSTM_sub C (c_A0 C) A2); [eapply W_sub0; exact HWa | eapply POSTM_mono; [|exact PMa]; lia]);
  assert (Hroom2 : aroom A2 vm2 kR bR) by (pose proof (aroom_nonneg _ _ _ _ Hroom1); room_tac);
  assert (E9' : getr r2 9 = Z_to_bv 64 kel) by (csr; reflexivity);
  assert (E18' : getr r2 18 = Z_to_bv 64 (8 * i)) by (csr; reflexivity);
  assert (E19' : getr r2 19 = Z_to_bv 64 i) by (csr; reflexivity).
  - (* [comment removed for export] *)
    destruct (kd_Nl al_rom r2 m2 kel arr h i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Rh2 Ra2 E9' E18' E19')
      as (r3 & RUN3 & P2 & P1 & P10 & P8 & P9 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    assert (P4 : getr r3 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
    assert (P2' : getr r3 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    replace (0x3c230 : word) with (Z_to_bv 64 0x3c230) by (apply bv_eq; reflexivity).
    apply (W_free16 C A2 m2 _ r3 (Z_to_bv 64 arr) (Z_to_bv 64 0x38604) (8 * h) (s - 48) S CK HWa P10 La2' L0a P1
             ltac:(red; apply bv_eq; reflexivity) P4 P2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A3 m3 vm3 r4 HWb CSb La3 LEQb PMb HRTb. rewrite ?with_vmmaps_twice in HWb |- *.
    replace (Z_to_bv 64 0x38604) with (0x38604 : word) by (apply bv_eq; reflexivity).
    assert (NEka' : Z_to_bv 64 kel <> Z_to_bv 64 arr) by (apply zneq_w; lia).
    apply (HK A3 m3 vm3 r4 HWb).
    + rewrite (LEQb _ NEka'). exact Lk2.
    + exact La3.
    + intros j Hj. assert (NEja : Z_to_bv 64 (rows j) <> Z_to_bv 64 arr) by (destruct (ROWS j Hj) as (? & ? & ? & ? & ?); apply zneq_w; lia).
      rewrite (LEQb _ NEja). destruct (Z.eq_dec j i) as [->|NEji]; [exact La2|].
      assert (NEjr : Z_to_bv 64 (rows j) <> Z_to_bv 64 (rows i)) by (destruct (ROWS j Hj) as (? & ? & ? & ? & ?); apply zneq_w; [lia | lia | apply DIST; lia]).
      rewrite (LEQa _ NEjr). apply FREED. lia.
    + intros q N1 N2. rewrite (LEQb q N1). rewrite (LEQa q (N2 i Hi)). exact (LEQ q N1 N2).
    + eapply POSTM_trans; [exact PM2|]. apply (POSTM_sub C (c_A0 C) A3); [eapply W_sub0; exact HWb | eapply POSTM_mono; [|exact PMb]; lia].
    + eapply kdcells_FRM; [exact CK | exact (proj1 PMb) | lia | lia | exact CE2].
    + apply (kd_rdn_pp C m2 m3 s pp _ CK (proj1 PMb)); [lia | lia | lia | exact Rpp2].
    + csr; reflexivity.
    + csr; reflexivity.
    + csr; reflexivity.
    + kd_rest_solve.
    + pose proof (aroom_nonneg _ _ _ _ Hroom2). room_tac.
  - (* [comment removed for export] *)
    destruct (kd_Nn al_rom r2 m2 kel h i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Rh2 E9' E18' E19')
      as (r3 & RUN3 & P2 & P18 & P19 & P8 & P9 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    apply (IH C A m md regs s pp kel arr h w rows S kR bR A2 m2 vm2 r3 (i + 1)%Z CK HK Hs16 ltac:(unfold ALLOC_STACK; lia) Hpp Hpphi H4 Hh Hw ltac:(lia) ltac:(lia)
             STAT HWa PM2 Hroom2 CE2 Rpp2).
    + split; [exact Lk2|]. split; [exact La2'|]. split; [exact Rh2|]. split; [exact Ra2|]. split; [|split].
      * intros j Hj. destruct (DROWS j ltac:(lia)) as (Lj & Rj). destruct (ROWS j ltac:(lia)) as (Gj & TOPj & NEja & NEjk & L0j).
        assert (NEjr : Z_to_bv 64 (rows j) <> Z_to_bv 64 (rows i)) by (apply zneq_w; [lia | lia | apply DIST; lia]).
        split; [rewrite (LEQa _ NEjr); exact Lj|].
        rewrite (livk_rdn A2 M1 m2 arr (8 * h) (arr + 8 * j) 8 (proj2 PMa) La2') by (cbn; lia). exact Rj.
      * intros j Hj. destruct (Z.eq_dec j i) as [->|NEji]; [exact La2|].
        destruct (ROWS j ltac:(lia)) as (Gj & TOPj & NEja & NEjk & L0j).
        assert (NEjr : Z_to_bv 64 (rows j) <> Z_to_bv 64 (rows i)) by (apply zneq_w; [lia | lia | apply DIST; lia]).
        rewrite (LEQa _ NEjr). apply FREED. lia.
      * intros q N1 N2. rewrite (LEQa q (N2 i Hi)). exact (LEQ q N1 N2).
    + csr; reflexivity.
    + csr; reflexivity.
    + csr; reflexivity.
    + exact P18.
    + exact P19.
    + csr; reflexivity.
    + kd_rest_solve.
Qed.

Theorem kernelDestroy_null_S_W : forall C A m md regs (s pp : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> (pp mod 8 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pp ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C (c_A0 C) s m m' ->
     rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x38570 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp ret S CK HW H2 Hs16 Hlo Hpp Hpphi ALpp H1 Hret H10 Rpp HK.
  pose proof CK as [T1 T2 T3 T4 T5]. cbn [snd ll_img LLU16] in T5. pose proof LSTK_val as HLS. unfold ALLOC_STACK in Hlo.
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (kd_A0 al_rom regs m s pp ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALpp Hret SOK Rpp H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (KDF m s ret regs) md /\ POSTM C (c_A0 C) s m (KDF m s ret regs)) by (unfold KDF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  apply (HK _ r1 HW1).
  - apply cs_kept_intro; csr; reflexivity.
  - exact PM1.
  - unfold KDF. repeat rdn_peel1. exact Rpp.
Qed.

Theorem kernelDestroy_S_W : forall C A m md regs (s pp kel arr h w : Z) (rows : Z -> Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> (pp mod 8 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 -> getr regs 10 = Z_to_bv 64 pp ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 kel)) ->
  kobj C A m kel arr h w rows -> (1 <= h < 2 ^ 31)%Z -> (0 <= w)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 kel) = None -> live A' (Z_to_bv 64 arr) = None -> (forall i, (0 <= i < h)%Z -> live A' (Z_to_bv 64 (rows i)) = None) ->
     (forall q, q <> Z_to_bv 64 kel -> q <> Z_to_bv 64 arr -> (forall i, (0 <= i < h)%Z -> q <> Z_to_bv 64 (rows i)) -> live A' q = live A q) ->
     POSTM C (c_A0 C) (pp + 8) m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
     aroom A' vm' kR bR ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x38570 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp kel arr h w rows ret S CK HW H2 Hs16 Hlo Hpp Hpphi ALpp H1 Hret H4 H10 Rpp KO Hh Hw kR bR Hroom HK.
  pose proof CK as [T1 T2 T3 T4 T5]. cbn [snd ll_img LLU16] in T5. pose proof LSTK_val as HLS. unfold ALLOC_STACK in Hlo.
  destruct KO as (Gk & TOPk & Lk & L0k & Rh & Rw & Ra & Ga & TOPa & NEka & La & L0a & ROWS & DIST).
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lk) as (_ & ALk & _). rewrite u_Z2bv in ALk by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) La) as (_ & ALa & _). rewrite u_Z2bv in ALa by lia.
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (kd_A1 al_rom regs m s pp kel h ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALpp ltac:(lia) ltac:(lia) (al16_mod8 _ ALk) ltac:(lia)
              SOK Rpp Rh H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q8 & Q9 & Q18 & Q19 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := KDF m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C (c_A0 C) s m M1) by (subst M1; unfold KDF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (kdcells_KDF m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1. rewrite <- H1 in CE1.
  assert (Rpp1 : rdn SEGS M1 (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 kel))) by (subst M1; unfold KDF; repeat rdn_peel1; exact Rpp).
  assert (Rh1 : rdn SEGS M1 (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h))) by (subst M1; unfold KDF; repeat rdn_peel1; exact Rh).
  assert (Ra1 : rdn SEGS M1 (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr))) by (subst M1; unfold KDF; repeat rdn_peel1; exact Ra).
  rewrite <- (with_vmmaps_same md) in HW1 |- *.
  apply (kd_loop (Z.to_nat (h - 1)) C A m md regs s pp kel arr h w rows S kR bR A M1 (m_vmmaps md) r1 0 CK).
  - unfold KDK. intros A' m' vm' r' HW' Lk' La' Lr' LEQ' PM' CE' Rpp' E2' E8' E9' ER' Hroom'.
    unfold kd_rest in ER'.
    destruct (kd_P al_rom r' m' (Z_to_bv 64 kel) E9') as (r2 & RUN2 & P2 & P1 & P10 & P8 & P9 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN2 |].
    assert (P4 : getr r2 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
    assert (P2' : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    replace (0x3c230 : word) with (Z_to_bv 64 0x3c230) by (apply bv_eq; reflexivity).
    apply (W_free16 C A' m' _ r2 (Z_to_bv 64 kel) (Z_to_bv 64 0x3860c) 24 (s - 48) S CK HW' P10 Lk' L0k P1
             ltac:(red; apply bv_eq; reflexivity) P4 P2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A4 m4 vm4 r3 HWc CSc Lk4 LEQc PMc HRTc. rewrite ?with_vmmaps_twice in HWc |- *.
    replace (Z_to_bv 64 0x3860c) with (0x3860c : word) by (apply bv_eq; reflexivity).
    assert (V2' : getr r3 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (V8' : getr r3 8 = Z_to_bv 64 pp) by (csr; reflexivity).
    assert (CE4 : kdcells m4 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19))
      by (eapply kdcells_FRM; [exact CK | exact (proj1 PMc) | lia | lia | exact CE']).
    rewrite H1 in CE4.
    destruct (kd_Q al_rom r3 m4 s pp ret _ _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret
                (W_sok_win C A4 m4 _ pp 8 CK HWc ltac:(lia) ltac:(cbn; lia)) CE4 V2' V8')
      as (r4 & RUN4 & V2 & V1 & V8 & V9 & V18 & V19 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWc)) | exact (mp_lazy _ (w_pure _ _ _ _ HWc)) | exact RUN4 |].
    set (M5 := wbytes m4 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    assert (WP5 : W C A4 M5 (with_vmmaps vm4 md) /\ POSTM C A4 (pp + 8) m4 M5) by (subst M5; wp_win CK).
    destruct WP5 as [HW5 PM5].
    assert (NEka' : Z_to_bv 64 arr <> Z_to_bv 64 kel) by (apply zneq_w; lia).
    apply (HK A4 M5 vm4 r4 HW5).
    + apply cs_kept_intro; csr; reflexivity.
    + exact Lk4.
    + rewrite (LEQc _ NEka'). exact La'.
    + intros i Hi. destruct (ROWS i Hi) as (Gr & TOPr & NEra & NErk & Lr & L0r & Rr).
      assert (NErk' : Z_to_bv 64 (rows i) <> Z_to_bv 64 kel) by (apply zneq_w; lia).
      rewrite (LEQc _ NErk'). exact (Lr' i Hi).
    + intros q N1 N2 N3. rewrite (LEQc q N1). exact (LEQ' q N2 N3).
    + eapply POSTM_trans; [eapply POSTM_mono; [|exact PM']; lia|].
      eapply POSTM_trans; [apply (POSTM_sub C (c_A0 C) A4); [eapply W_sub0; exact HWc | eapply POSTM_mono; [|exact PMc]; lia]|].
      apply (POSTM_sub C (c_A0 C) A4); [eapply W_sub0; exact HW5 | exact PM5].
    + subst M5. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
    + pose proof (aroom_nonneg _ _ _ _ Hroom'). room_tac.
  - exact Hs16.
  - unfold ALLOC_STACK. lia.
  - exact Hpp.
  - exact Hpphi.
  - exact H4.
  - exact Hh.
  - exact Hw.
  - rewrite Z2Nat.id by lia. lia.
  - lia.
  - split; [lia|]. split; [lia|]. split; [exact L0k|]. split; [lia|]. split; [lia|]. split; [exact (al16_mod8 _ ALa)|].
    split; [exact NEka|]. split; [exact L0a|]. split; [|exact DIST].
    intros j Hj. destruct (ROWS j Hj) as (Gr & TOPr & NEra & NErk & Lr & L0r & Rr). repeat split; assumption.
  - exact HW1.
  - exact PM1.
  - exact Hroom.
  - exact CE1.
  - exact Rpp1.
  - split; [exact Lk|]. split; [exact La|]. split; [exact Rh1|]. split; [exact Ra1|]. split; [|split].
    + intros j Hj. destruct (ROWS j ltac:(lia)) as (Gr & TOPr & NEra & NErk & Lr & L0r & Rr).
      split; [exact Lr|]. subst M1. unfold KDF. repeat rdn_peel1. exact Rr.
    + intros j Hj. lia.
    + intros q N1 N2. reflexivity.
  - csr; reflexivity.
  - csr; reflexivity.
  - csr; reflexivity.
  - rewrite Q18; f_equal; lia.
  - rewrite Q19. reflexivity.
  - csr; reflexivity.
  - kd_rest_solve.
Qed.

End KernDestroy.
