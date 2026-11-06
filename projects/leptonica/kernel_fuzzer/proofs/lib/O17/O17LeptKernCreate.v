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
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17LeptDeser O17LeptKernC2d O17_code_15000_16000 O17_code_16000_17000.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptCredit LeptRoomK.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section KernCreate.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LL17} {P16 : O17Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition kern (C : lctx) (A A' : AS) (m' : word -> option byte) (kel arr h w : Z) (rows : Z -> Z) : Prop :=
  (1 <= kel)%Z /\ (kel + 24 <= alloc_top (c_vm C))%Z /\ (kel mod 16 = 0)%Z /\
  live A' (Z_to_bv 64 kel) = Some 24%Z /\ live A (Z_to_bv 64 kel) = None /\ live (c_A0 C) (Z_to_bv 64 kel) = None /\
  rdn SEGS m' (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) /\
  rdn SEGS m' (Z_to_bv 64 (kel + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) /\
  rdn SEGS m' (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr)) /\
  (1 <= arr)%Z /\ (arr + 8 * h <= alloc_top (c_vm C))%Z /\ (arr mod 16 = 0)%Z /\ kel <> arr /\
  live A' (Z_to_bv 64 arr) = Some (8 * h)%Z /\ live A (Z_to_bv 64 arr) = None /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\
  (forall i, (0 <= i < h)%Z ->
      (1 <= rows i)%Z /\ (rows i + 4 * w <= alloc_top (c_vm C))%Z /\ (rows i mod 16 = 0)%Z /\ rows i <> arr /\ rows i <> kel /\
      live A' (Z_to_bv 64 (rows i)) = Some (4 * w)%Z /\ live A (Z_to_bv 64 (rows i)) = None /\ live (c_A0 C) (Z_to_bv 64 (rows i)) = None /\
      rdn SEGS m' (Z_to_bv 64 (arr + 8 * i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (rows i)))) /\
  (forall i j, (0 <= i < h)%Z -> (0 <= j < h)%Z -> i <> j -> rows i <> rows j) /\
  (forall q, q <> Z_to_bv 64 kel -> q <> Z_to_bv 64 arr -> (forall i, (0 <= i < h)%Z -> q <> Z_to_bv 64 (rows i)) -> live A' q = live A q).

Theorem kernelCreate_W : forall C A m md regs (s w h : Z) (ret : word) (S : TSet) (kR bR : Z),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x30520 ->
  getr regs 10 = Z_to_bv 64 h -> getr regs 11 = Z_to_bv 64 w -> (1 <= w <= 100000)%Z -> (1 <= h <= 100000)%Z -> (w * h < 2 ^ 29)%Z ->
  aroom A (m_vmmaps md) kR bR -> (RK_kern h <= kR)%Z -> (RB_kern h w <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists kel arr rows, getr regs' 10 = Z_to_bv 64 kel /\ kern C A A' m' kel arr h w rows) ) ->
     aroom A' vm' (kR - RK_kern h) (bR - RB_kern h w) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x15528 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h ret S kR bR CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 Hw Hh Hwh HRM HRK HRB HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL17] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  unfold RK_kern in HRK. unfold RB_kern in HRB.
  pose proof (alloc_margin_ge 24 ltac:(lia)) as G24. pose proof (alloc_margin_ge (h * 8) ltac:(lia)) as G8h. pose proof (alloc_margin_ge (w * 4) ltac:(lia)) as G4w.
  pose proof (alloc_cost_ge (w * 4)) as [GC _].
  assert (GHC : (0 <= h * alloc_cost (w * 4))%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (GCM : (0 <= ROOM_CREDMAX)%Z) by (unfold ROOM_CREDMAX; lia).
  (* [comment removed for export] *)
  destruct (kc_A al_rom regs m s w h ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hwh (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & Q18 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := C2F m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold C2F; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (c2cells_C2F m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1. rewrite <- H1 in CE1.
  rewrite <- (with_vmmaps_same md) in HW1 |- *.
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x30520) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  replace (0x164cc : word) with (Z_to_bv 64 0x164cc) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A M1 _ r1 1 24 kR bR (Z_to_bv 64 0x15614) (s - 48) S CK HW1 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           HRM ltac:(lia) ltac:(change (1 * 24)%Z with 24%Z; lia) ltac:(unfold ROOM_NMAX; lia) Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa HRMa. rewrite ?with_vmmaps_twice in HWa |- *.
  change (1 * 24)%Z with 24%Z in *.
  replace (Z_to_bv 64 0x15614) with (0x15614 : word) by (apply bv_eq; reflexivity).
  pose proof (c2cells_FRM C M1 m1 s _ _ _ _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) CE1) as CEa.
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  assert (E4 : getr r2 4 = Z_to_bv 64 0x30520) by (csr; reflexivity).
  assert (E8 : getr r2 8 = Z_to_bv 64 w) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 (2 ^ 64 - 100001)) by (csr; reflexivity).
  assert (E18 : getr r2 18 = Z_to_bv 64 h) by (csr; reflexivity).
  (* [comment removed for export] *)
  pose proof (u64_range res) as Hru.
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (kel := u res) in *. rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO.
  assert (Hkel : (1 <= kel)%Z /\ (kel + 24 <= alloc_top (c_vm C))%Z) by (unfold round16 in TOP; change ((24 + 15) / 16)%Z with 2%Z in TOP; lia).
  clearbody kel.
  assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
  destruct (kc_B al_rom r2 m1 w h kel ltac:(lia) ltac:(lia) Hw Hh
              (W_sok_blk C A1 m1 _ _ _ kel 8 CK HWa L1 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia))
              Hres E8 E9 E18) as (r3 & RUN3 & P2 & P1 & P10 & P11 & P8 & P18 & P19 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  set (M2 := wbytes (wbytes m1 _ _) _ _).
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A s m M2).
  { subst M2.
    apply (WP_blk C A A1 m _ _ (Z_to_bv 64 kel) _ 24); [exact CK | | exact L1 | exact L0 | exact L00 | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    apply (WP_blk C A A1 m _ _ (Z_to_bv 64 kel) _ 24); [exact CK | | exact L1 | exact L0 | exact L00 | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    split; [exact HWa | exact PMa']. }
  destruct WP2 as [HW2 PM2].
  pose proof (blk_range C A1 m1 _ (Z_to_bv 64 kel) _ CK HWa L1 ltac:(lia)) as [_ Xk]. rewrite u_Z2bv in Xk by lia.
  assert (OUT2 : forall x : word, ~ (kel <= u x < kel + 8)%Z -> M2 x = m1 x).
  { intros x Hx. subst M2. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (CE2 : c2cells M2 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)).
  { apply (c2cells_frame m1 M2 s); [lia | lia | exact CEa |]. intros x Hx. apply OUT2. lia. }
  assert (Ksy : rdn SEGS M2 (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h))) by (subst M2; rdn_chain).
  assert (Ksx : rdn SEGS M2 (Z_to_bv 64 (kel + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w))) by (subst M2; rdn_chain).
  assert (P4 : getr r3 4 = Z_to_bv 64 0x30520) by (rewrite (AG3 4) by (cbv; intuition discriminate); exact E4).
  assert (P2' : getr r3 2 = Z_to_bv 64 (s - 48)) by (rewrite P2; exact E2).
  replace (0x164cc : word) with (Z_to_bv 64 0x164cc) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A1 M2 _ r3 h 8 (kR - 1) (bR - alloc_margin 24) (Z_to_bv 64 0x15718) (s - 48) S CK HW2 P10 P11 ltac:(lia) ltac:(lia) ltac:(lia)
           HRMa ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) P1
           ltac:(red; apply bv_eq; reflexivity) P4 P2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A3 m3 vm3 r4 res3 HW3 Hres3 CS3 Hnz3 La0' La1 La00 LEQ3 ZERO3 AL163 TOP3 PM3 HRM3. rewrite ?with_vmmaps_twice in HW3 |- *.
  replace (Z_to_bv 64 0x15718) with (0x15718 : word) by (apply bv_eq; reflexivity).
  pose proof (u64_range res3) as Hru3.
  assert (Eres3 : res3 = Z_to_bv 64 (u res3)) by (symmetry; apply zbv_self).
  set (arr := u res3) in *. rewrite Eres3 in Hres3, La0', La1, La00, LEQ3, ZERO3.
  assert (Harr : (1 <= arr)%Z /\ (arr + 8 * h <= alloc_top (c_vm C))%Z) by (pose proof (round16_ge (h * 8) ltac:(lia)); lia).
  clearbody arr.
  assert (NEak : Z_to_bv 64 arr <> Z_to_bv 64 kel) by (intros E; rewrite E in La0'; rewrite La0' in L1; discriminate).
  assert (NEka : kel <> arr) by (intros E; apply NEak; rewrite E; reflexivity).
  assert (Lk3 : live A3 (Z_to_bv 64 kel) = Some 24%Z) by (rewrite (LEQ3 _ (not_eq_sym NEak)); exact L1).
  assert (LaA : live A (Z_to_bv 64 arr) = None) by (rewrite <- (LEQ _ NEak); exact La0').
  assert (SUB3 : sub_live A A3).
  { intros q kq Lq. rewrite (LEQ3 q); [exact (SUBa q kq Lq)|]. intros ->. rewrite (SUBa _ _ Lq) in La0'. discriminate. }
  assert (PM3' : POSTM C A s m m3) by (eapply POSTM_trans; [exact PM2 | apply (POSTM_sub C A A1 _ _ _ SUBa); eapply POSTM_mono; [|exact PM3]; lia]).
  pose proof (c2cells_FRM C M2 m3 s _ _ _ _ _ _ CK (proj1 PM3) ltac:(lia) ltac:(lia) CE2) as CE3.
  assert (Ksy3 : rdn SEGS m3 (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h))).
  { rewrite <- Ksy. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    exact (LIVK_at A1 M2 m3 kel 24 x (proj2 PM3) L1 ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (Ksx3 : rdn SEGS m3 (Z_to_bv 64 (kel + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w))).
  { rewrite <- Ksx. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    exact (LIVK_at A1 M2 m3 kel 24 x (proj2 PM3) L1 ltac:(lia) ltac:(lia) ltac:(lia)). }
  (* [comment removed for export] *)
  assert (Y18 : getr r4 18 = Z_to_bv 64 h) by (csr; reflexivity).
  destruct (kc_C al_rom r4 m3 h arr ltac:(lia) ltac:(lia) ltac:(lia) Hres3 Y18) as (r5 & RUN5 & V2 & V9 & V18 & V20 & V8 & V19 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
  (* [comment removed for export] *)
  set (kP := (kR - 1 - 1)%Z). set (pP := (bR - alloc_margin 24 - alloc_margin (h * 8))%Z).
  pose proof (aroomP_of_aroom _ _ _ _ HRM3) as HRP. fold kP pP in HRP.
  apply (kc_loop (Z.to_nat (h - 1)) C A m md regs s w h kel kP pP S A3 m3 vm3 r5 0 arr (fun _ => 0%Z) CK); try assumption.
  - (* [comment removed for export] *)
    intros A' m' vm' r arr' rows W' CS' PM' R10' KP' KD' HRP'.
    rewrite H1. apply (HK A' m' vm' r W' CS' PM').
    + right. exists kel, arr', rows. split; [exact R10'|].
      destruct KP' as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & BR & BD & BQ).
      unfold kern. do 8 (split; [assumption|]). split; [exact KD'|]. do 7 (split; [assumption|]). split; [exact BR | split; [exact BD | exact BQ]].
    + pose proof (aroom_of_aroomP _ _ _ _ HRP' ltac:(subst pP; lia)) as HR'.
      apply (aroom_mono _ _ _ _ _ _ HR'); subst kP pP; unfold RK_kern, RB_kern; lia.
  - unfold CALLOC_STACK, ALLOC_STACK. lia.
  - rewrite H1. exact Hret.
  - rewrite Z2Nat.id by lia. lia.
  - lia.
  - subst kP. lia.
  - subst pP. lia.
  - (* [comment removed for export] *)
    split; [lia|]. split; [lia|]. split; [exact AL16|]. split; [exact Lk3|]. split; [exact L0|]. split; [exact L00|].
    split; [exact Ksy3|]. split; [exact Ksx3|]. split; [lia|]. split; [lia|]. split; [exact AL163|]. split; [exact NEka|].
    split; [rewrite La1; f_equal; lia|]. split; [exact LaA|]. split; [exact La00|].
    split; [intros i Hi; lia|]. split; [intros i j Hi; lia|].
    intros q NQk NQa _. rewrite (LEQ3 q NQa). exact (LEQ q NQk).
  - replace (kP - 0)%Z with kP by lia. replace (pP - 0 * alloc_cost (w * 4))%Z with pP by lia. exact HRP.
  - rewrite V2. csr. reflexivity.
  - rewrite V8. csr. reflexivity.
  - rewrite V19. csr. reflexivity.
  - replace (arr + 8 * 0)%Z with arr by lia. exact V20.
  - csr. reflexivity.
  - unfold O17LeptKernC2d.k_rest. rest_solve.
Qed.

End KernCreate.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
