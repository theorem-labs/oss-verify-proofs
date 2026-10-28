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
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr V2KernUb V2LeptKernSegs2 V2_code_kern.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptCredit LeptRoomK LeptRoomBL.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section KernC2d.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition krows_n (C : lctx) (A A' : AS) (m' : word -> option byte) (arr sy sx n : Z) (rows : Z -> Z) : Prop :=
  (1 <= arr)%Z /\ (arr + 8 * sy <= alloc_top (c_vm C))%Z /\ (arr mod 16 = 0)%Z /\
  live A' (Z_to_bv 64 arr) = Some (8 * sy)%Z /\ live A (Z_to_bv 64 arr) = None /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\
  (forall i, (0 <= i < n)%Z ->
      (1 <= rows i)%Z /\ (rows i + 4 * sx <= alloc_top (c_vm C))%Z /\ (rows i mod 16 = 0)%Z /\ rows i <> arr /\
      live A' (Z_to_bv 64 (rows i)) = Some (4 * sx)%Z /\ live A (Z_to_bv 64 (rows i)) = None /\ live (c_A0 C) (Z_to_bv 64 (rows i)) = None /\
      rdn SEGS m' (Z_to_bv 64 (arr + 8 * i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (rows i)))) /\
  (forall i j, (0 <= i < n)%Z -> (0 <= j < n)%Z -> i <> j -> rows i <> rows j) /\
  (forall q, q <> Z_to_bv 64 arr -> (forall i, (0 <= i < n)%Z -> q <> Z_to_bv 64 (rows i)) -> live A' q = live A q).

(* [comment removed for export] *)
#[local] Definition c2_rest : list (bv 5) := [3; 4; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Lemma LIVK_at : forall A M M' (p k : Z) (x : word), LIVK A M M' -> live A (Z_to_bv 64 p) = Some k ->
  (0 <= p)%Z -> (p + k < 2 ^ 64)%Z -> (p <= u x < p + k)%Z -> M' x = M x.
Proof.
  intros A M M' p k x L Lp G0 TP Hx.
  pose proof (L (Z_to_bv 64 p) k (u x - p)%Z Lp ltac:(lia)) as E.
  replace (at_ (Z_to_bv 64 p) (u x - p)) with x in E by (unfold at_; apply bv_eq; rewrite !u_Z2bv; rewrite ?u_Z2bv; pose proof (u64_range x); lia).
  exact E.
Qed.

(* [comment removed for export] *)
Lemma W_sok_blk : forall C A m md (p : word) (k a : Z) (n : nat), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + Z.of_nat n <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros C A m md p k a n CK HW L Hlo Hhi Hk. pose proof (u64_range p). rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
  destruct (blk_byte C A m md p k x CK HW L ltac:(lia)) as (_ & D & _). exact (D E).
Qed.

(* [comment removed for export] *)
Lemma c2cells_FRM : forall C M M' s ret s0v s1v s2v s3v s4v s5v s6v, Cok C -> FRM C (s - 64) M M' ->
  (c_top C - LSTK <= s - 64)%Z -> (s <= c_top C)%Z ->
  c2cells M s ret s0v s1v s2v s3v s4v s5v s6v -> c2cells M' s ret s0v s1v s2v s3v s4v s5v s6v.
Proof.
  intros C M M' s ret s0v s1v s2v s3v s4v s5v s6v CK F Hlo Hhi (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  pose proof CK as [T1 T2 T3 T4 T5]. unfold c2cells.
  rewrite !(FRM_rdn16 C (s - 64) M M' _ _ CK F) by lia. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Definition KR (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s sx sy kP pP : Z) (S : TSet) : Prop :=
  forall A' m' vm' r arr rows, W C A' m' (with_vmmaps vm' md) -> cs_kept regs r -> POSTM C A s m m' ->
    getr r 10 = Z_to_bv 64 arr -> krows_n C A A' m' arr sy sx sy rows ->
    aroom A' vm' (kP - sy) (pP - sy * alloc_margin (sx * 4)) ->
    realizes SEGS (mkCfg (mkst r (getr regs 1) m' al_rom) (with_vmmaps vm' md)) S.

(* [comment removed for export] *)
Lemma c2d_loop : forall (k : nat) C A m md regs (s sx sy kP pP : Z) (S : TSet) A1 M1 vm1 r (n arr : Z) (rows : Z -> Z),
  Cok C -> KR C A m md regs s sx sy kP pP S ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x56270 -> ret_ok (getr regs 1) ->
  (1 <= sx <= 100000)%Z -> (1 <= sy <= 100000)%Z -> (Z.of_nat k = sy - 1 - n)%Z -> (0 <= n < sy)%Z -> getr regs 2 = Z_to_bv 64 s ->
  (sy <= kP)%Z -> (sy * alloc_margin (sx * 4) <= pP)%Z ->
  W C A1 M1 (with_vmmaps vm1 md) -> POSTM C A s m M1 ->
  c2cells M1 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) ->
  krows_n C A A1 M1 arr sy sx n rows ->
  aroom A1 vm1 (kP - n) (pP - n * alloc_margin (sx * 4)) ->
  getr r 2 = Z_to_bv 64 (s - 64) -> getr r 8 = Z_to_bv 64 sx -> getr r 9 = Z_to_bv 64 (sy - n) -> getr r 18 = Z_to_bv 64 arr ->
  getr r 19 = Z_to_bv 64 1 -> getr r 20 = Z_to_bv 64 1 -> getr r 21 = Z_to_bv 64 (arr + 8 * n) -> getr r 22 = Z_to_bv 64 (arr + 8 * n) ->
  getr r 4 = Z_to_bv 64 0x56270 ->
  (forall x, In x c2_rest -> getr r x = getr regs x) ->
  realizes SEGS (mkCfg (mkst r (0x3850c : word) M1 al_rom) (with_vmmaps vm1 md)) S.
Proof.
  induction k as [|k IH]; intros C A m md regs s sx sy kP pP S A1 M1 vm1 r n arr rows CK HKR Hs16 Hlo Hhi H4 Hret Hsx Hsy Hk Hn H2 HkP HpP HW PM CE
    KRW HRM R2 R8 R9 R18 R19 R20 R21 R22 R4 RR;
    pose proof KRW as (Ga & TOPa & ALa & La & LaA & La0 & ROWS & DIST & RQ);
    pose proof CK as [T1 T2 T3 T4 T5]; laypins; cbn [fst snd ll_img LLU16] in *; unfold LSF in *; unfold c2_rest in RR;
    pose proof (alloc_top_lt (c_vm C)) as AT; unfold two_pow_64 in AT;
    pose proof (alloc_margin_ge (sx * 4) ltac:(lia)) as HC0;
    (* [comment removed for export] *)
    destruct (c2d_H al_rom r M1 sx R8) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & AG1);
    (eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]);
    replace (0x3c0f8 : word) with (Z_to_bv 64 0x3c0f8) by (apply bv_eq; reflexivity);
    (apply (W_calloc16_sure C A1 M1 _ r1 sx 4 (kP - n) (pP - n * alloc_margin (sx * 4)) (Z_to_bv 64 0x38518) (s - 64) S CK HW Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
             HRM ltac:(lia) ltac:(nia) ltac:(unfold ROOM_NMAX; lia) Q1
             ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite (AG1 4) by (cbv; intuition discriminate); exact R4)
             ltac:(rewrite Q2; exact R2) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)));
    intros A2 m2 vm2 r2 res HW2 Hres CS2 Hnz L1 L2 L00 LEQ ZERO AL16 TOP PM2 HRM2; rewrite with_vmmaps_twice in HW2 |- *;
    replace (Z_to_bv 64 0x38518) with (0x38518 : word) by (apply bv_eq; reflexivity);
    pose proof (c2cells_FRM C M1 m2 s _ _ _ _ _ _ _ _ CK (proj1 PM2) ltac:(lia) ltac:(lia) CE) as CE2;
    assert (E2 : getr r2 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity);
    assert (E8 : getr r2 8 = Z_to_bv 64 sx) by (csr; reflexivity);
    assert (E9 : getr r2 9 = Z_to_bv 64 (sy - n)) by (csr; reflexivity);
    assert (E18 : getr r2 18 = Z_to_bv 64 arr) by (csr; reflexivity);
    assert (E19 : getr r2 19 = Z_to_bv 64 1) by (csr; reflexivity);
    assert (E20 : getr r2 20 = Z_to_bv 64 1) by (csr; reflexivity);
    assert (E21 : getr r2 21 = Z_to_bv 64 (arr + 8 * n)) by (csr; reflexivity);
    assert (E22 : getr r2 22 = Z_to_bv 64 (arr + 8 * n)) by (csr; reflexivity);
    assert (E4 : getr r2 4 = Z_to_bv 64 0x56270) by (csr; reflexivity);
    assert (RR2 : forall x, In x c2_rest -> getr r2 x = getr regs x) by (unfold c2_rest; rest_solve);
    (* [comment removed for export] *)
    assert (ROWS2 : forall i, (0 <= i < n)%Z ->
              (1 <= rows i)%Z /\ (rows i + 4 * sx <= alloc_top (c_vm C))%Z /\ (rows i mod 16 = 0)%Z /\ rows i <> arr /\
              live A1 (Z_to_bv 64 (rows i)) = Some (4 * sx)%Z /\ live A (Z_to_bv 64 (rows i)) = None /\ live (c_A0 C) (Z_to_bv 64 (rows i)) = None /\
              rdn SEGS m2 (Z_to_bv 64 (arr + 8 * i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (rows i))))
      by (intros i Hi; destruct (ROWS i Hi) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8);
          do 7 (split; [assumption|]);
          rewrite <- G8; apply rdn_ext; rewrite u_Z2bv by lia; [lia|]; intros x Hx;
          exact (LIVK_at A1 M1 m2 arr (8 * sy) x (proj2 PM2) La ltac:(lia) ltac:(lia) ltac:(lia)));
    assert (SUB1 : sub_live A A1)
      by (intros q kq Lq; rewrite (RQ q); [exact Lq | intros ->; rewrite Lq in LaA; discriminate |];
          intros i Hi ->; destruct (ROWS i Hi) as (_ & _ & _ & _ & _ & LA & _); rewrite Lq in LA; discriminate);
    assert (PM2' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM|]; apply (POSTM_sub C A A1 _ _ _ SUB1); eapply POSTM_mono; [|exact PM2]; lia);
    (* [comment removed for export] *)
    pose proof (u64_range res) as Hru;
    assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self);
    set (rw := u res) in *;
    rewrite Eres in Hres, L1, L2, L00, LEQ;
    assert (Hrw : (1 <= rw)%Z /\ (rw + 4 * sx <= alloc_top (c_vm C))%Z) by (pose proof (round16_ge (sx * 4) ltac:(lia)); lia);
    clearbody rw;
    assert (NEra : Z_to_bv 64 rw <> Z_to_bv 64 arr) by (intros E; rewrite E in L1; rewrite L1 in La; discriminate);
    assert (La2 : live A2 (Z_to_bv 64 arr) = Some (8 * sy)%Z) by (rewrite (LEQ _ (not_eq_sym NEra)); exact La);
    assert (NErr : forall i, (0 <= i < n)%Z -> Z_to_bv 64 (rows i) <> Z_to_bv 64 rw)
      by (intros i Hi E; destruct (ROWS i Hi) as (_ & _ & _ & _ & G5 & _); rewrite E, L1 in G5; discriminate);
    assert (SOKn : store_ok SEGS m2 (Z_to_bv 64 (arr + 8 * n)) 8 = true)
      by (apply (W_sok_blk C A2 m2 _ _ _ (arr + 8 * n) 8 CK HW2 La2); rewrite u_Z2bv by lia; cbn; lia);
    assert (SUB2 : sub_live A A2)
      by (intros q kq Lq; rewrite (LEQ q); [exact (SUB1 q kq Lq)|]; intros ->; rewrite (SUB1 _ _ Lq) in L1; discriminate);
    set (rows' := fun i : Z => if (i =? n)%Z then rw else rows i);
    set (m3 := wbytes m2 (Z_to_bv 64 (arr + 8 * n)) (word_to_le_bytes 8 (Z_to_bv 64 rw)));
    assert (WP3 : W C A2 m3 (with_vmmaps vm2 md) /\ POSTM C A s m m3)
      by (subst m3; apply (WP_blk C A A2 m m2 _ (Z_to_bv 64 arr) _ (8 * sy) _ s CK (conj HW2 PM2') La2 LaA La0 SUB2); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia);
    assert (CE3 : c2cells m3 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22))
      by (apply (c2cells_frame m2 m3 s); [lia | lia | exact CE2 |]; intros x Hx; subst m3; apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia);
    assert (KR3 : krows_n C A A2 m3 arr sy sx (n + 1) rows').
  1,3: split; [exact Ga|]; split; [exact TOPa|]; split; [exact ALa|]; split; [exact La2|]; split; [exact LaA|]; split; [exact La0|]; split; [|split].
  1,4: intros i Hi; unfold rows'; destruct (Z.eqb_spec i n) as [->|NEi];
       [ split; [lia|]; split; [lia|]; split; [exact AL16|]; split; [intros E; apply NEra; rewrite E; reflexivity|];
         split; [rewrite L2; f_equal; lia|]; split; [rewrite <- (RQ _ NEra (fun i' Hi' => not_eq_sym (NErr i' Hi'))); exact L1|];
         split; [exact L00|]; subst m3; apply rdn_wbytes_hit8; rewrite u_Z2bv by lia; lia
       | destruct (ROWS2 i ltac:(lia)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8);
         do 4 (split; [assumption|]); split; [rewrite (LEQ _ (NErr i ltac:(lia))); exact G5|]; do 2 (split; [assumption|]);
         subst m3; rewrite rdn_wbytes_out_Z; [exact G8|]; rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia ].
  1,3: intros i i' Hi Hi' NE; unfold rows'; destruct (Z.eqb_spec i n) as [->|N1], (Z.eqb_spec i' n) as [->|N2];
       [ lia
       | intros E; apply (NErr i' ltac:(lia)); rewrite E; reflexivity
       | intros E; apply (NErr i ltac:(lia)); rewrite E; reflexivity
       | apply DIST; lia ].
  1,2: intros q NQa NQr; pose proof (NQr n ltac:(lia)) as X; unfold rows' in X; rewrite Z.eqb_refl in X;
       rewrite (LEQ q X); apply RQ; [exact NQa|]; intros i Hi; pose proof (NQr i ltac:(lia)) as Y; unfold rows' in Y;
       destruct (Z.eqb_spec i n); [lia | exact Y].
  - (* [comment removed for export] *)
    destruct (c2d_I2 al_rom r2 m2 s arr sy n rw (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                ltac:(lia) ltac:(lia) Ga ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret SOKn ltac:(lia) CE2 E2 Hres E9 E18 E19 E20 E21 E22)
      as (r3 & RUN3 & P2 & P1 & P10 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |]. fold m3.
    assert (En : (n + 1)%Z = sy) by lia.
    apply (HKR A2 m3 vm2 r3 arr rows' (proj1 WP3)).
    + apply cs_kept_intro; csr; reflexivity.
    + exact (proj2 WP3).
    + exact P10.
    + rewrite En in KR3. exact KR3.
    + replace (kP - sy)%Z with (kP - n - 1)%Z by lia. replace (pP - sy * alloc_margin (sx * 4))%Z with (pP - n * alloc_margin (sx * 4) - alloc_margin (sx * 4))%Z by (rewrite <- En; ring).
      exact HRM2.
  - (* [comment removed for export] *)
    destruct (c2d_I1 al_rom r2 m2 arr sy n rw Ga ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOKn Hres E9 E18 E19 E20 E21 E22)
      as (r3 & RUN3 & P2 & P9 & P21 & P22 & P8 & P18 & P19 & P20 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |]. fold m3.
    apply (IH C A m md regs s sx sy kP pP S A2 m3 vm2 r3 (n + 1)%Z arr rows' CK HKR Hs16 ltac:(unfold LSF; lia) Hhi H4 Hret Hsx Hsy ltac:(lia) ltac:(lia) H2 HkP HpP
             (proj1 WP3) (proj2 WP3) CE3 KR3); try (csr; reflexivity).
    + replace (kP - (n + 1))%Z with (kP - n - 1)%Z by lia. replace (pP - (n + 1) * alloc_margin (sx * 4))%Z with (pP - n * alloc_margin (sx * 4) - alloc_margin (sx * 4))%Z by ring.
      exact HRM2.
    + unfold c2_rest; rest_solve.
Qed.

(* [comment removed for export] *)
Theorem create2dFloatArray_W : forall C A m md regs (s sx sy : Z) (ret : word) (S : TSet) (kR bR : Z),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 ->
  getr regs 10 = Z_to_bv 64 sy -> getr regs 11 = Z_to_bv 64 sx -> (1 <= sx <= 100000)%Z -> (1 <= sy <= 100000)%Z ->
  aroom A (m_vmmaps md) kR bR -> (RK_c2d sy <= kR)%Z -> (RB_c2dS sy sx <= bR)%Z ->
  (forall A' m' vm' regs' arr rows, W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 arr -> krows_n C A A' m' arr sy sx sy rows ->
     aroom A' vm' (kR - RK_c2d sy) (bR - RB_c2dS sy sx) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x38428 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s sx sy ret S kR bR CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 Hsx Hsy HRM HRK HRB HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  unfold RK_c2d in HRK. unfold RB_c2dS in HRB.
  pose proof (alloc_margin_ge (sy * 8) ltac:(lia)) as G8h. pose proof (alloc_margin_ge (sx * 4) ltac:(lia)) as G4w.
  assert (GHC : (0 <= sy * alloc_margin (sx * 4))%Z) by (apply Z.mul_nonneg_nonneg; lia).
  destruct (c2d_A al_rom regs m s sx sy ret ltac:(lia) ltac:(lia) Hsx Hsy (W_sok_win C A m md (s - 64) 64 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := C2F m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold C2F; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (c2cells_C2F m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1. rewrite <- H1 in CE1.
  rewrite <- (with_vmmaps_same md) in HW1 |- *.
  (* [comment removed for export] *)
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x56270) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  replace (0x3c0f8 : word) with (Z_to_bv 64 0x3c0f8) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A M1 _ r1 sy 8 kR bR (Z_to_bv 64 0x384f0) (s - 64) S CK HW1 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           HRM ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m2 vm2 r2 res HW2 Hres CS2 Hnz L1 L2 L00 LEQ ZERO AL16 TOP PM2 HRM2. rewrite ?with_vmmaps_twice in HW2 |- *.
  replace (Z_to_bv 64 0x384f0) with (0x384f0 : word) by (apply bv_eq; reflexivity).
  pose proof (c2cells_FRM C M1 m2 s _ _ _ _ _ _ _ _ CK (proj1 PM2) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (PM2' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PM2]; lia]).
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity).
  assert (E4 : getr r2 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
  assert (E8 : getr r2 8 = Z_to_bv 64 sx) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 sy) by (csr; reflexivity).
  assert (RR2 : forall x, In x c2_rest -> getr r2 x = getr regs x) by (unfold c2_rest; rest_solve).
  pose proof (u64_range res) as Hru.
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (arr := u res) in *. rewrite Eres in Hres, L1, L2, L00, LEQ.
  assert (Harr : (1 <= arr)%Z /\ (arr + 8 * sy <= alloc_top (c_vm C))%Z) by (pose proof (round16_ge (sy * 8) ltac:(lia)); lia).
  clearbody arr.
  destruct (c2d_B al_rom r2 m2 arr ltac:(lia) ltac:(rewrite <- (Z.add_0_r arr); apply mod16_plus_mod8; [exact AL16 | reflexivity]) Hres)
    as (r3 & RUN3 & P2 & P18 & P19 & P20 & P21 & P22 & P8 & P9 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  (* [comment removed for export] *)
  set (kP := (kR - 1)%Z) in *. set (pP := (bR - alloc_margin (sy * 8))%Z) in *.
  assert (HKR : KR C A m md regs s sx sy kP pP S).
  { intros A' m' vm' r arr' rows' HW' CS PM' R10' KRW' HRP'. rewrite H1. rewrite ?with_vmmaps_twice in HW' |- *.
    apply (HK A' m' vm' r arr' rows' HW' CS PM' R10' KRW').
    apply (aroom_mono _ _ _ _ _ _ HRP'); subst kP pP; unfold RK_c2d, RB_c2dS; pose proof (aroom_nonneg _ _ _ _ HRP'); lia. }
  apply (c2d_loop (Z.to_nat (sy - 1)) C A m md regs s sx sy kP pP S A2 m2 vm2 r3 0 arr (fun _ => 0%Z) CK HKR Hs16 ltac:(unfold LSF; lia) Hhi H4
           ltac:(rewrite H1; exact Hret) Hsx Hsy ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia) H2 ltac:(subst kP; lia) ltac:(subst pP; lia) HW2 PM2' CE2); try (csr; reflexivity).
  - split; [lia|]. split; [lia|]. split; [exact AL16|]. split; [rewrite L2; f_equal; lia|]. split; [exact L1|]. split; [exact L00|].
    split; [intros i Hi; lia|]. split; [intros i j Hi; lia|].
    intros q NQa _. exact (LEQ q NQa).
  - rewrite Z.sub_0_r, Z.mul_0_l, Z.sub_0_r. exact HRM2.
  - rewrite P9, Z.sub_0_r. exact E9.
  - rewrite P21. f_equal. lia.
  - rewrite P22. f_equal. lia.
  - unfold c2_rest; rest_solve.
Qed.

End KernC2d.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
