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
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17LeptDeser O17_code_15000_16000 O17_code_16000_17000.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptCredit LeptRoomK.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section KernC2d.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LL17} {P16 : O17Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition kpart (C : lctx) (A A' : AS) (m' : word -> option byte) (kel arr h w n : Z) (rows : Z -> Z) : Prop :=
  (1 <= kel)%Z /\ (kel + 24 <= alloc_top (c_vm C))%Z /\ (kel mod 16 = 0)%Z /\
  live A' (Z_to_bv 64 kel) = Some 24%Z /\ live A (Z_to_bv 64 kel) = None /\ live (c_A0 C) (Z_to_bv 64 kel) = None /\
  rdn SEGS m' (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) /\
  rdn SEGS m' (Z_to_bv 64 (kel + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) /\
  (1 <= arr)%Z /\ (arr + 8 * h <= alloc_top (c_vm C))%Z /\ (arr mod 16 = 0)%Z /\ kel <> arr /\
  live A' (Z_to_bv 64 arr) = Some (8 * h)%Z /\ live A (Z_to_bv 64 arr) = None /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\
  (forall i, (0 <= i < n)%Z ->
      (1 <= rows i)%Z /\ (rows i + 4 * w <= alloc_top (c_vm C))%Z /\ (rows i mod 16 = 0)%Z /\ rows i <> arr /\ rows i <> kel /\
      live A' (Z_to_bv 64 (rows i)) = Some (4 * w)%Z /\ live A (Z_to_bv 64 (rows i)) = None /\ live (c_A0 C) (Z_to_bv 64 (rows i)) = None /\
      rdn SEGS m' (Z_to_bv 64 (arr + 8 * i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (rows i)))) /\
  (forall i j, (0 <= i < n)%Z -> (0 <= j < n)%Z -> i <> j -> rows i <> rows j) /\
  (forall q, q <> Z_to_bv 64 kel -> q <> Z_to_bv 64 arr -> (forall i, (0 <= i < n)%Z -> q <> Z_to_bv 64 (rows i)) -> live A' q = live A q).

(* [comment removed for export] *)
#[local] Definition k_rest : list (bv 5) := [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv.

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
Lemma c2cells_FRM : forall C M M' s ret s0v s1v s2v s3v s4v, Cok C -> FRM C (s - 48) M M' ->
  (c_top C - LSTK <= s - 48)%Z -> (s <= c_top C)%Z ->
  c2cells M s ret s0v s1v s2v s3v s4v -> c2cells M' s ret s0v s1v s2v s3v s4v.
Proof.
  intros C M M' s ret s0v s1v s2v s3v s4v CK F Hlo Hhi (C1 & C2 & C3 & C4 & C5 & C6).
  pose proof CK as [T1 T2 T3 T4 T5]. unfold c2cells.
  rewrite !(FRM_rdn16 C (s - 48) M M' _ _ CK F) by lia. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Definition KRK (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s w h kel kP pP : Z) (S : TSet) : Prop :=
  forall A' m' vm' r arr rows, W C A' m' (with_vmmaps vm' md) -> cs_kept regs r -> POSTM C A s m m' ->
    getr r 10 = Z_to_bv 64 kel -> kpart C A A' m' kel arr h w h rows ->
    rdn SEGS m' (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr)) ->
    aroomP A' vm' (kP - h) (pP - h * alloc_cost (w * 4)) ->
    realizes SEGS (mkCfg (mkst r (getr regs 1) m' al_rom) (with_vmmaps vm' md)) S.

(* [comment removed for export] *)
Lemma kc_loop : forall (k : nat) C A m md regs (s w h kel kP pP : Z) (S : TSet) A1 M1 vm1 r (n arr : Z) (rows : Z -> Z),
  Cok C -> KRK C A m md regs s w h kel kP pP S ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + CALLOC_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x30520 -> ret_ok (getr regs 1) ->
  (1 <= w <= 100000)%Z -> (1 <= h <= 100000)%Z -> (Z.of_nat k = h - 1 - n)%Z -> (0 <= n < h)%Z -> getr regs 2 = Z_to_bv 64 s ->
  (h <= kP)%Z -> (h * alloc_cost (w * 4) + alloc_margin (w * 4) + ROOM_CREDMAX <= pP)%Z ->
  W C A1 M1 (with_vmmaps vm1 md) -> POSTM C A s m M1 ->
  c2cells M1 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) ->
  kpart C A A1 M1 kel arr h w n rows ->
  aroomP A1 vm1 (kP - n) (pP - n * alloc_cost (w * 4)) ->
  getr r 2 = Z_to_bv 64 (s - 48) -> getr r 8 = Z_to_bv 64 w -> getr r 9 = Z_to_bv 64 arr -> getr r 18 = Z_to_bv 64 (arr + 8 * h) ->
  getr r 19 = Z_to_bv 64 kel -> getr r 20 = Z_to_bv 64 (arr + 8 * n) -> getr r 4 = Z_to_bv 64 0x30520 ->
  (forall x, In x k_rest -> getr r x = getr regs x) ->
  realizes SEGS (mkCfg (mkst r (0x15728 : word) M1 al_rom) (with_vmmaps vm1 md)) S.
Proof.
  induction k as [|k IH]; intros C A m md regs s w h kel kP pP S A1 M1 vm1 r n arr rows CK HKR Hs16 Hlo Hhi H4 Hret Hw Hh Hk Hn H2 HkP HpP HW PM CE
    KP HRM R2 R8 R9 R18 R19 R20 R4 RR;
    pose proof KP as (Gk & TOPk & ALk & Lk & LkA & Lk0 & Ksy & Ksx & Ga & TOPa & ALa & NEka & La & LaA & La0 & ROWS & DIST & RQ);
    pose proof CK as [T1 T2 T3 T4 T5]; laypins; cbn [fst snd ll_img LL17] in *; unfold k_rest in RR; unfold CALLOC_STACK, ALLOC_STACK in Hlo;
    pose proof (alloc_top_lt (c_vm C)) as AT; unfold two_pow_64 in AT;
    pose proof (alloc_cost_ge (w * 4)) as [HC0 _];
    (* [comment removed for export] *)
    destruct (kc_H al_rom r M1 w R8) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & Q18 & Q19 & Q20 & AG1);
    (eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]);
    replace (0x164cc : word) with (Z_to_bv 64 0x164cc) by (apply bv_eq; reflexivity);
    (apply (W_calloc16_psure C A1 M1 _ r1 w 4 (kP - n) (pP - n * alloc_cost (w * 4)) (Z_to_bv 64 0x15734) (s - 48) S CK HW Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
             HRM ltac:(lia) ltac:(apply (aroomP_loop_ok (w * 4) n h pP); lia) ltac:(unfold ROOM_NMAX; lia) Q1
             ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite (AG1 4) by (cbv; intuition discriminate); exact R4)
             ltac:(rewrite Q2; exact R2) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)));
    intros A2 m2 vm2 r2 res HW2 Hres CS2 Hnz L1 L2 L00 LEQ ZERO AL16 TOP PM2 HRM2; rewrite with_vmmaps_twice in HW2 |- *;
    replace (Z_to_bv 64 0x15734) with (0x15734 : word) by (apply bv_eq; reflexivity);
    pose proof (c2cells_FRM C M1 m2 s _ _ _ _ _ _ CK (proj1 PM2) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia) CE) as CE2;
    assert (E2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity);
    assert (E8 : getr r2 8 = Z_to_bv 64 w) by (csr; reflexivity);
    assert (E9 : getr r2 9 = Z_to_bv 64 arr) by (csr; reflexivity);
    assert (E18 : getr r2 18 = Z_to_bv 64 (arr + 8 * h)) by (csr; reflexivity);
    assert (E19 : getr r2 19 = Z_to_bv 64 kel) by (csr; reflexivity);
    assert (E20 : getr r2 20 = Z_to_bv 64 (arr + 8 * n)) by (csr; reflexivity);
    assert (E4 : getr r2 4 = Z_to_bv 64 0x30520) by (csr; reflexivity);
    assert (RR2 : forall x, In x k_rest -> getr r2 x = getr regs x) by (unfold k_rest; rest_solve);
    (* [comment removed for export] *)
    assert (ROWS2 : forall i, (0 <= i < n)%Z ->
              (1 <= rows i)%Z /\ (rows i + 4 * w <= alloc_top (c_vm C))%Z /\ (rows i mod 16 = 0)%Z /\ rows i <> arr /\ rows i <> kel /\
              live A1 (Z_to_bv 64 (rows i)) = Some (4 * w)%Z /\ live A (Z_to_bv 64 (rows i)) = None /\ live (c_A0 C) (Z_to_bv 64 (rows i)) = None /\
              rdn SEGS m2 (Z_to_bv 64 (arr + 8 * i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (rows i))))
      by (intros i Hi; destruct (ROWS i Hi) as (G1 & G2 & G3 & G4 & G4k & G5 & G6 & G7 & G8);
          do 8 (split; [assumption|]);
          rewrite <- G8; apply rdn_ext; rewrite u_Z2bv by lia; [lia|]; intros x Hx;
          exact (LIVK_at A1 M1 m2 arr (8 * h) x (proj2 PM2) La ltac:(lia) ltac:(lia) ltac:(lia)));
    assert (SUB1 : sub_live A A1)
      by (intros q kq Lq; rewrite (RQ q); [exact Lq | intros ->; rewrite Lq in LkA; discriminate | intros ->; rewrite Lq in LaA; discriminate |];
          intros i Hi ->; destruct (ROWS i Hi) as (_ & _ & _ & _ & _ & _ & LA & _); rewrite Lq in LA; discriminate);
    assert (PM2' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM|]; apply (POSTM_sub C A A1 _ _ _ SUB1); eapply POSTM_mono; [|exact PM2]; lia);
    (* [comment removed for export] *)
    pose proof (u64_range res) as Hru;
    assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self);
    set (rw := u res) in *;
    rewrite Eres in Hres, L1, L2, L00, LEQ;
    assert (Hrw : (1 <= rw)%Z /\ (rw + 4 * w <= alloc_top (c_vm C))%Z) by (pose proof (round16_ge (w * 4) ltac:(lia)); lia);
    clearbody rw;
    assert (NEra : Z_to_bv 64 rw <> Z_to_bv 64 arr) by (intros E; rewrite E in L1; rewrite L1 in La; discriminate);
    assert (NErk : Z_to_bv 64 rw <> Z_to_bv 64 kel) by (intros E; rewrite E in L1; rewrite L1 in Lk; discriminate);
    assert (La2 : live A2 (Z_to_bv 64 arr) = Some (8 * h)%Z) by (rewrite (LEQ _ (not_eq_sym NEra)); exact La);
    assert (Lk2 : live A2 (Z_to_bv 64 kel) = Some 24%Z) by (rewrite (LEQ _ (not_eq_sym NErk)); exact Lk);
    assert (NErr : forall i, (0 <= i < n)%Z -> Z_to_bv 64 (rows i) <> Z_to_bv 64 rw)
      by (intros i Hi E; destruct (ROWS i Hi) as (_ & _ & _ & _ & _ & G5 & _); rewrite E, L1 in G5; discriminate);
    assert (SOKn : store_ok SEGS m2 (Z_to_bv 64 (arr + 8 * n)) 8 = true)
      by (apply (W_sok_blk C A2 m2 _ _ _ (arr + 8 * n) 8 CK HW2 La2); rewrite u_Z2bv by lia; cbn; lia);
    assert (SUB2 : sub_live A A2)
      by (intros q kq Lq; rewrite (LEQ q); [exact (SUB1 q kq Lq)|]; intros ->; rewrite (SUB1 _ _ Lq) in L1; discriminate);
    (* [comment removed for export] *)
    assert (Ksy2 : rdn SEGS m2 (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)))
      by (rewrite <- Ksy; apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]; intros x Hx; cbn in Hx;
          exact (LIVK_at A1 M1 m2 kel 24 x (proj2 PM2) Lk ltac:(lia) ltac:(lia) ltac:(lia)));
    assert (Ksx2 : rdn SEGS m2 (Z_to_bv 64 (kel + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)))
      by (rewrite <- Ksx; apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]; intros x Hx; cbn in Hx;
          exact (LIVK_at A1 M1 m2 kel 24 x (proj2 PM2) Lk ltac:(lia) ltac:(lia) ltac:(lia)));
    pose proof (live_apart C A2 m2 _ _ _ _ _ CK HW2 Lk2 La2 ltac:(apply zbv_ne; lia) ltac:(lia) ltac:(lia)) as APka; rewrite !u_Z2bv in APka by lia;
    set (rows' := fun i : Z => if (i =? n)%Z then rw else rows i);
    set (m3 := wbytes m2 (Z_to_bv 64 (arr + 8 * n)) (word_to_le_bytes 8 (Z_to_bv 64 rw)));
    assert (WP3 : W C A2 m3 (with_vmmaps vm2 md) /\ POSTM C A s m m3)
      by (subst m3; apply (WP_blk C A A2 m m2 _ (Z_to_bv 64 arr) _ (8 * h) _ s CK (conj HW2 PM2') La2 LaA La0 SUB2); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia);
    assert (CE3 : c2cells m3 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20))
      by (apply (c2cells_frame m2 m3 s); [lia | lia | exact CE2 |]; intros x Hx; subst m3; apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn;
          pose proof (blk_range C A2 m2 _ (Z_to_bv 64 arr) _ CK HW2 La2 ltac:(lia)) as [_ X]; rewrite u_Z2bv in X by lia; lia);
    assert (KP3 : kpart C A A2 m3 kel arr h w (n + 1) rows').
  1,3: split; [exact Gk|]; split; [exact TOPk|]; split; [exact ALk|]; split; [exact Lk2|]; split; [exact LkA|]; split; [exact Lk0|];
       split; [subst m3; rewrite rdn_wbytes_out_Z; [exact Ksy2 | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia]|];
       split; [subst m3; rewrite rdn_wbytes_out_Z; [exact Ksx2 | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia]|];
       split; [exact Ga|]; split; [exact TOPa|]; split; [exact ALa|]; split; [exact NEka|]; split; [exact La2|]; split; [exact LaA|]; split; [exact La0|]; split; [|split].
  1,4: intros i Hi; unfold rows'; destruct (Z.eqb_spec i n) as [->|NEi];
       [ split; [lia|]; split; [lia|]; split; [exact AL16|]; split; [intros E; apply NEra; rewrite E; reflexivity|];
         split; [intros E; apply NErk; rewrite E; reflexivity|];
         split; [rewrite L2; f_equal; lia|];
         split; [rewrite <- (RQ _ NErk NEra (fun i' Hi' => not_eq_sym (NErr i' Hi'))); exact L1|];
         split; [exact L00|]; subst m3; apply rdn_wbytes_hit8; rewrite u_Z2bv by lia; lia
       | destruct (ROWS2 i ltac:(lia)) as (G1 & G2 & G3 & G4 & G4k & G5 & G6 & G7 & G8);
         do 5 (split; [assumption|]); split; [rewrite (LEQ _ (NErr i ltac:(lia))); exact G5|]; do 2 (split; [assumption|]);
         subst m3; rewrite rdn_wbytes_out_Z; [exact G8|]; rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia ].
  1,3: intros i i' Hi Hi' NE; unfold rows'; destruct (Z.eqb_spec i n) as [->|N1], (Z.eqb_spec i' n) as [->|N2];
       [ lia
       | intros E; apply (NErr i' ltac:(lia)); rewrite E; reflexivity
       | intros E; apply (NErr i ltac:(lia)); rewrite E; reflexivity
       | apply DIST; lia ].
  1,2: intros q NQk NQa NQr; pose proof (NQr n ltac:(lia)) as X; unfold rows' in X; rewrite Z.eqb_refl in X;
       rewrite (LEQ q X); apply RQ; [exact NQk | exact NQa|]; intros i Hi; pose proof (NQr i ltac:(lia)) as Y; unfold rows' in Y;
       destruct (Z.eqb_spec i n); [lia | exact Y].
  - (* [comment removed for export] *)
    assert (SOKk : store_ok SEGS m2 (Z_to_bv 64 (kel + 16)) 8 = true)
      by (apply (W_sok_blk C A2 m2 _ _ _ (kel + 16) 8 CK HW2 Lk2); rewrite u_Z2bv by lia; cbn; lia).
    pose proof (blk_range C A2 m2 _ (Z_to_bv 64 arr) _ CK HW2 La2 ltac:(lia)) as [_ Xa]. rewrite u_Z2bv in Xa by lia.
    pose proof (blk_range C A2 m2 _ (Z_to_bv 64 kel) _ CK HW2 Lk2 ltac:(lia)) as [_ Xk]. rewrite u_Z2bv in Xk by lia.
    destruct (kc_I2 al_rom r2 m2 s arr h n rw kel (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
                ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia) Ga ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Gk ltac:(lia) Hret SOKn SOKk
                ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) CE2 E2 Hres E9 E18 E19 E20)
      as (r3 & RUN3 & P2 & P1 & P10 & P8 & P9 & P18 & P19 & P20 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |]. fold m3.
    set (m4 := wbytes m3 (Z_to_bv 64 (kel + 16)) (word_to_le_bytes 8 (Z_to_bv 64 arr))).
    assert (WP4 : W C A2 m4 (with_vmmaps vm2 md) /\ POSTM C A s m m4)
      by (subst m4; apply (WP_blk C A A2 m m3 _ (Z_to_bv 64 kel) _ 24 _ s CK WP3 Lk2 LkA Lk0 SUB2); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia).
    assert (En : (n + 1)%Z = h) by lia.
    apply (HKR A2 m4 vm2 r3 arr rows' (proj1 WP4)).
    + apply cs_kept_intro; csr; reflexivity.
    + exact (proj2 WP4).
    + exact P10.
    + (* [comment removed for export] *)
      rewrite En in KP3. destruct KP3 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & BR & BD & BQ).
      do 6 (split; [assumption|]).
      split; [subst m4; rewrite rdn_wbytes_out_Z; [exact B7 | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia]|].
      split; [subst m4; rewrite rdn_wbytes_out_Z; [exact B8 | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia]|].
      do 7 (split; [assumption|]). split; [| split; [exact BD | exact BQ]].
      intros i Hi. destruct (BR i Hi) as (G1 & G2 & G3 & G4 & G4k & G5 & G6 & G7 & G8). do 8 (split; [assumption|]).
      subst m4. rewrite rdn_wbytes_out_Z; [exact G8|]. rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]. lia.
    + subst m4. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
    + replace (kP - h)%Z with (kP - n - 1)%Z by lia. replace (pP - h * alloc_cost (w * 4))%Z with (pP - n * alloc_cost (w * 4) - alloc_cost (w * 4))%Z by (rewrite <- En; ring).
      exact HRM2.
  - (* [comment removed for export] *)
    destruct (kc_I1 al_rom r2 m2 arr h n rw Ga ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOKn Hres E18 E20)
      as (r3 & RUN3 & P2 & P20 & P8 & P9 & P18 & P19 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |]. fold m3.
    apply (IH C A m md regs s w h kel kP pP S A2 m3 vm2 r3 (n + 1)%Z arr rows' CK HKR Hs16 Hlo Hhi H4 Hret Hw Hh ltac:(lia) ltac:(lia) H2 HkP HpP
             (proj1 WP3) (proj2 WP3) CE3 KP3); try (csr; reflexivity).
    + replace (kP - (n + 1))%Z with (kP - n - 1)%Z by lia. replace (pP - (n + 1) * alloc_cost (w * 4))%Z with (pP - n * alloc_cost (w * 4) - alloc_cost (w * 4))%Z by ring.
      exact HRM2.
    + unfold k_rest; rest_solve.
Qed.

End KernC2d.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
