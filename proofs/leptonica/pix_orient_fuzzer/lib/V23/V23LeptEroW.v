(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop LeptRop2Arith LeptRecs LeptSel LeptSlots.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptDilW O23LeptDilArm.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptRop_iface V23LeptRopP8 V23LeptRopUC V23LeptDilW V23LeptEroSegs.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section EroW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition ero_reads (m : word -> option byte) (s sel pixd pixs : Z) (sv : selv) (c : Z -> Z -> Z) (vd vs : pixv) : Prop :=
  rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 (v_data sv)) /\
  (forall i, (0 <= i < v_sy sv)%Z -> rdn SEGS m (Z_to_bv 64 (v_data sv + 8 * i)) 8 = Some (Z_to_le_bytes 8 (v_rows sv i))) /\
  (forall i j, (0 <= i < v_sy sv)%Z -> (0 <= j < v_sx sv)%Z -> rdn SEGS m (Z_to_bv 64 (v_rows sv i + 4 * j)) 4 = Some (Z_to_le_bytes 4 (c i j))) /\
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 pixs) /\
  rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 (v_cy sv)) /\
  rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (Z_to_le_bytes 4 (v_cx sv)) /\
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 (v_sy sv)) /\
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 (v_sx sv)) /\
  rdn SEGS m (Z_to_bv 64 (s - 104)) 4 = Some (Z_to_le_bytes 4 (p_h vd)) /\
  rdn SEGS m (Z_to_bv 64 (s - 100)) 4 = Some (Z_to_le_bytes 4 (p_w vd)) /\
  PIXat m pixd vd /\ PIXat m pixs vs.

Definition ERO_STACK : Z := 160 + 3408.

Ltac ero_kc KP := let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [csr; apply KP; cbn; tauto|]); destruct Hx.

Lemma ero_sare_rd : forall m (s : Z), (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rdn SEGS (SARE m s) (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
  intros m s Hs Hs64. unfold SARE.
  pose proof (rdn_wbytes_hit SEGS (word_to_le_bytes 8 (Z_to_bv 64 0)) m (Z_to_bv 64 (s - 160))) as X.
  rewrite length_N_to_le_bytes in X. apply X. rewrite u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

Lemma ero_sare_out : forall m (s : Z) (x : word), (160 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 160 <= u x < s - 152)%Z -> SARE m s x = m x.
Proof.
  intros m s x Hs Hs64 Hx. unfold SARE.
  rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia |].
  rewrite length_N_to_le_bytes, u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

Section Loop.
Variables (C : lctx) (A A1 : AS) (md1 : Model) (M0 : word -> option byte) (s sel pixd pixs : Z) (sv : selv) (c : Z -> Z -> Z)
          (vd vs : pixv) (St : TSet) (r0 : bvmap 5 word).
Hypothesis CK : Cok C.
Hypothesis SUB : sub_live A A1.
Hypothesis Hs16 : (s mod 16 = 0)%Z.
Hypothesis Hlo : (c_top C - LSTK + ERO_STACK <= s)%Z.
Hypothesis Hhi : (s <= c_top C)%Z.
Hypothesis Hsy : (1 <= v_sy sv <= 10000)%Z.
Hypothesis Hsx : (1 <= v_sx sv <= 10000)%Z.
Hypothesis Hcx : (0 <= v_cx sv < v_sx sv)%Z.
Hypothesis Hcy : (0 <= v_cy sv < v_sy sv)%Z.
Hypothesis Bsel : (0 <= sel)%Z /\ (sel + 32 < 2 ^ 64)%Z.
Hypothesis Bdata : (0 <= v_data sv)%Z /\ (v_data sv + 8 * v_sy sv < 2 ^ 64)%Z.
Hypothesis Brows : forall i, (0 <= i < v_sy sv)%Z -> (0 <= v_rows sv i)%Z /\ (v_rows sv i + 4 * v_sx sv < 2 ^ 64)%Z.
Hypothesis Bc : forall i j, (0 <= i < v_sy sv)%Z -> (0 <= j < v_sx sv)%Z -> (0 <= c i j < 2 ^ 31)%Z.
Hypothesis Adata : (1 <= v_data sv)%Z /\ (v_data sv mod 8 = 0)%Z.
Hypothesis Arows : forall i, (0 <= i < v_sy sv)%Z -> (1 <= v_rows sv i)%Z /\ (v_rows sv i mod 4 = 0)%Z.
Hypothesis Bpixs : (0 <= pixs < 2 ^ 64)%Z.
Hypothesis Edd : p_d vs = p_d vd.
Hypothesis Hd1 : p_d vd = 1%Z.
Hypothesis SHd : rop_shape (p_w vd) (p_h vd) (p_d vd) (p_wpl vd).
Hypothesis SHs : rop_shape (p_w vs) (p_h vs) (p_d vs) (p_wpl vs).
Hypothesis Ew : p_w vs = p_w vd.
Hypothesis Eh : p_h vs = p_h vd.
Hypothesis Lpd : live A1 (Z_to_bv 64 pixd) = Some 64%Z.
Hypothesis Lps : live A1 (Z_to_bv 64 pixs) = Some 64%Z.
Hypothesis NEpd : Z_to_bv 64 pixd <> Z_to_bv 64 (p_data vd).
Hypothesis NEps : Z_to_bv 64 pixs <> Z_to_bv 64 (p_data vd).
Hypothesis Ld : live A1 (Z_to_bv 64 (p_data vd)) = Some (4 * (p_wpl vd * p_h vd))%Z.
Hypothesis Ld0 : live A (Z_to_bv 64 (p_data vd)) = None.
Hypothesis Ld00 : live (c_A0 C) (Z_to_bv 64 (p_data vd)) = None.
Hypothesis Ls : live A1 (Z_to_bv 64 (p_data vs)) = Some (4 * (p_wpl vs * p_h vs))%Z.
Hypothesis NEds : Z_to_bv 64 (p_data vs) <> Z_to_bv 64 (p_data vd).
Hypothesis HRD : forall m, O23LeptDilW.dil_frame C (s - 144) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m -> ero_reads m s sel pixd pixs sv c vd vs.

Definition ero_keep (r : bvmap 5 word) : Prop := forall x, In x [3; 4; 27]%list -> getr r x = getr r0 x.

Definition ero_KL : Prop :=
  forall m r, W C A1 m md1 -> POSTM C A (s - 144) M0 m -> O23LeptDilW.dil_frame C (s - 144) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m ->
    getr r 2 = Z_to_bv 64 (s - 160) -> getr r 8 = Z_to_bv 64 pixd -> getr r 9 = Z_to_bv 64 sel -> ero_keep r ->
    realizes SEGS (mkCfg (mkst r (0xa1f10 : word) m al_rom) md1) St.
Hypothesis KL : ero_KL.

Definition ero_LP (n : nat) : Prop :=
  forall (i j : Z) (r : bvmap 5 word) (m : word -> option byte),
    W C A1 m md1 -> POSTM C A (s - 144) M0 m -> O23LeptDilW.dil_frame C (s - 144) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m ->
    (0 <= i < v_sy sv)%Z -> (0 <= j < v_sx sv)%Z -> Z.of_nat n = ((v_sy sv - 1 - i) * v_sx sv + (v_sx sv - 1 - j))%Z ->
    getr r 2 = Z_to_bv 64 (s - 160) -> getr r 9 = Z_to_bv 64 sel -> getr r 8 = Z_to_bv 64 pixd ->
    getr r 18 = Z_to_bv 64 i -> getr r 19 = Z_to_bv 64 1 -> getr r 20 = Z_to_bv 64 0 -> getr r 21 = Z_to_bv 64 0x7fffffff ->
    getr r 22 = Z_to_bv 64 (4 * j) -> getr r 23 = Z_to_bv 64 j -> getr r 24 = Z_to_bv 64 j ->
    getr r 25 = Z_to_bv 64 (8 * i) -> getr r 26 = Z_to_bv 64 i -> getr r 10 = Z_to_bv 64 (v_sx sv) -> ero_keep r ->
    realizes SEGS (mkCfg (mkst r (0xa1e94 : word) m al_rom) md1) St.

Lemma ero_next : forall n (i j : Z) (r : bvmap 5 word) (m : word -> option byte),
  (forall n', n = S n' -> ero_LP n') ->
  W C A1 m md1 -> POSTM C A (s - 144) M0 m -> O23LeptDilW.dil_frame C (s - 144) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m ->
  (0 <= i < v_sy sv)%Z -> (0 <= j < v_sx sv)%Z -> Z.of_nat n = ((v_sy sv - 1 - i) * v_sx sv + (v_sx sv - 1 - j))%Z ->
  getr r 2 = Z_to_bv 64 (s - 160) -> getr r 9 = Z_to_bv 64 sel -> getr r 8 = Z_to_bv 64 pixd ->
  getr r 18 = Z_to_bv 64 i -> getr r 19 = Z_to_bv 64 1 -> getr r 20 = Z_to_bv 64 0 -> getr r 21 = Z_to_bv 64 0x7fffffff ->
  getr r 22 = Z_to_bv 64 (4 * j) -> getr r 23 = Z_to_bv 64 j -> getr r 24 = Z_to_bv 64 j ->
  getr r 25 = Z_to_bv 64 (8 * i) -> getr r 26 = Z_to_bv 64 i -> getr r 10 = Z_to_bv 64 (v_sx sv) -> ero_keep r ->
  realizes SEGS (mkCfg (mkst r (0xa1e84 : word) m al_rom) md1) St.
Proof.
  intros n i j r m IH HW PM DF Hi Hj Hn H2 H9 H8 H18 H19 H20 H21 H22 H23 H24 H25 H26 H10 KP.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ERO_STACK in Hlo.
  destruct (HRD m DF) as (RD & RR & RC & RT & RCY & RCX & RSY & RSX & RH & RW & PXd & PXs).
  destruct (er_L al_rom r m s (v_sy sv) (v_sx sv) i j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hi Hj RSY RSX
              H2 H10 H18 H20 H21 H22 H23 H24 H25 H26) as (r1 & pc & RUN & CS & AG).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
  destruct CS as [(Cj & -> & Q10 & Q18 & Q22 & Q23 & Q24 & Q25 & Q26)
                 | [(Cj & Ci & -> & Q10 & Q18 & Q22 & Q23 & Q24 & Q25 & Q26) | (Cj & Ci & ->)]].
  - destruct n as [|n']; [exfalso; cbn in Hn; nia|].
    apply (IH n' eq_refl i (j + 1)%Z r1 m HW PM DF Hi ltac:(lia) ltac:(rewrite Nat2Z.inj_succ in Hn; lia));
      first [ero_kc KP | csr; reflexivity].
  - destruct n as [|n']; [exfalso; cbn in Hn; nia|].
    apply (IH n' eq_refl (i + 1)%Z 0%Z r1 m HW PM DF ltac:(lia) ltac:(lia) ltac:(rewrite Nat2Z.inj_succ in Hn; nia));
      first [ero_kc KP | csr; reflexivity].
  - apply (KL m r1 HW PM DF); first [ero_kc KP | csr; reflexivity].
Qed.

Lemma ero_step : forall n, (forall n', n = S n' -> ero_LP n') -> ero_LP n.
Proof.
  intros n IH i j r m HW PM DF Hi Hj Hn H2 H9 H8 H18 H19 H20 H21 H22 H23 H24 H25 H26 H10 KP.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ERO_STACK in Hlo.
  destruct (HRD m DF) as (RD & RR & RC & RT & RCY & RCX & RSY & RSX & RH & RW & PXd & PXs).
  pose proof (RR i Hi) as RRi. pose proof (RC i j Hi Hj) as RCij.
  pose proof (Brows i Hi) as [Br0 Br1]. pose proof (Arows i Hi) as [Ar1 Ar4]. pose proof (Bc i j Hi Hj) as Bcij.
  pose proof Adata as [Ad1 Ad8]. pose proof Bdata as [Bd0 Bd1]. pose proof Bsel as [Bs0 Bs1].
  pose proof SHd as (Dd & Wd & Hd' & WPd & Szd). pose proof SHs as (Ds & Ws & Hs' & WPs & Szs).
  destruct (Z.eq_dec (c i j) 1) as [E1|E1].
  - rewrite E1 in RCij.
    destruct (er_H al_rom r m s sel (v_data sv) (v_rows sv i) i j pixd pixs (p_w vd) (p_h vd) (v_cx sv) (v_cy sv)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bpixs
                ltac:(lia) Ad8 ltac:(lia) Ar4 RD RRi RCij RCX RCY RW RH RT
                (W_sok_win C A1 m md1 (s - 160)%Z 8%nat CK HW ltac:(lia) ltac:(cbn; lia))
                H2 H9 H8 H18 H19 H22 H23 H25 H26)
      as (r1 & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & AG).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    assert (WP1 : W C A1 (SARE m s) md1 /\ POSTM C A (s - 144) M0 (SARE m s)) by (unfold SARE; wp_win CK).
    destruct WP1 as [HW1 PM1].
    assert (DF1 : O23LeptDilW.dil_frame C (s - 144) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 (SARE m s)).
    { intros a Ha Hb. rewrite ero_sare_out by (unfold scratch in Ha; lia). exact (DF a Ha Hb). }
    destruct (HRD (SARE m s) DF1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PXd1 & PXs1).
    assert (W32 : (p_w vd <= 32 * p_wpl vs)%Z).
    { rewrite WPs, Ew, Edd, Hd1. apply O23LeptDilW.wpl1_le. lia. }
    replace (0x7f13c : word) with (Z_to_bv 64 PC_pixRasterop) by (unfold PC_pixRasterop; apply bv_eq; reflexivity).
    apply (pixRasterop_op8clip_W C A A1 (SARE m s) md1 r1 (s - 160)%Z pixd (v_cx sv - j)%Z (v_cy sv - i)%Z (p_w vd) (p_h vd) pixs 0%Z 0%Z vd vs
             (Z_to_bv 64 0xa1e80) St
             CK HW1 SUB ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ROP_STACK; lia) ltac:(lia)
             Q1 ltac:(red; apply bv_eq; reflexivity)
             Q10 Q11 Q12 Q13 Q14 Q15 Q16 Q17 (ero_sare_rd m s ltac:(lia) ltac:(lia)) PXd1 PXs1 Edd Hd1 SHd SHs
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(rewrite Ew, Eh; exact (O23LeptDilArm.rop2_clip_arm_sx0 (v_cx sv - j) (v_cy sv - i) (p_w vd) (p_h vd) (p_wpl vs) ltac:(lia) W32))
             Lpd Lps NEpd NEps Ld Ld0 Ld00 Ls NEds).
    intros m' r' HW' CS' PM' PXd' PXs' FR' R10'.
    replace (Z_to_bv 64 0xa1e80) with (0xa1e80 : word) by (apply bv_eq; reflexivity).
    assert (DF2 : O23LeptDilW.dil_frame C (s - 144) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m').
    { intros a Ha Hb. rewrite (FR' a);
        [rewrite ero_sare_out by (unfold scratch in Ha; lia); exact (DF a Ha Hb) | unfold scratch in *; lia | exact Hb]. }
    assert (PM2 : POSTM C A (s - 144) M0 m') by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [| exact PM']; lia]).
    destruct (HRD m' DF2) as (_ & _ & _ & _ & _ & _ & _ & RSX2 & _).
    destruct (er_R al_rom r' m' s (v_sx sv) ltac:(lia) ltac:(lia) ltac:(lia) RSX2 ltac:(csr; reflexivity)) as (r2 & RUN2 & X10 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN2 |].
    apply (ero_next n i j r2 m' IH HW' PM2 DF2 Hi Hj Hn); first [ero_kc KP | csr; reflexivity].
  - destruct (er_M al_rom r m sel (v_data sv) (v_rows sv i) i j (c i j) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) Bcij E1 ltac:(lia) Ad8 ltac:(lia) Ar4 RD RRi RCij H9 H19 H22 H25) as (r1 & RUN & AG).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    apply (ero_next n i j r1 m IH HW PM DF Hi Hj Hn); first [ero_kc KP | csr; reflexivity].
Qed.

Lemma ero_loop : forall n, ero_LP n.
Proof using All.
  induction n as [n IH] using lt_wf_ind. apply ero_step. intros n' ->. apply IH. lia.
Qed.

End Loop.


(* [comment removed for export] *)
Section Tail.
Variables (C : lctx) (Ar A : AS) (md : Model) (M7 : word -> option byte) (s pixd : Z) (vd : pixv) (y0 y1 y2 y3 : Z) (St : TSet)
          (r0 : bvmap 5 word).
Hypothesis CK : Cok C.
Hypothesis SUB : sub_live Ar A.
Hypothesis Hs16 : (s mod 16 = 0)%Z.
Hypothesis Hlo : (c_top C - LSTK + ERO_STACK <= s)%Z.
Hypothesis Hhi : (s <= c_top C)%Z.
Hypothesis Hd1 : p_d vd = 1%Z.
Hypothesis SHd : rop_shape (p_w vd) (p_h vd) (p_d vd) (p_wpl vd).
Hypothesis Lpd : live A (Z_to_bv 64 pixd) = Some 64%Z.
Hypothesis NEpd : Z_to_bv 64 pixd <> Z_to_bv 64 (p_data vd).
Hypothesis Ld : live A (Z_to_bv 64 (p_data vd)) = Some (4 * (p_wpl vd * p_h vd))%Z.
Hypothesis Ld0 : live Ar (Z_to_bv 64 (p_data vd)) = None.
Hypothesis Ld00 : live (c_A0 C) (Z_to_bv 64 (p_data vd)) = None.
Hypothesis By0 : (0 <= y0 <= 10000)%Z.
Hypothesis By1 : (0 <= y1 <= 10000)%Z.
Hypothesis By2 : (0 <= y2 <= 10000)%Z.
Hypothesis By3 : (0 <= y3 <= 10000)%Z.
Hypothesis HRT : forall m, O23LeptDilW.dil_frame C (s - 144) (p_data vd) (4 * (p_wpl vd * p_h vd)) M7 m ->
  rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 y0) /\ rdn SEGS m (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 y1) /\
  rdn SEGS m (Z_to_bv 64 (s - 132)) 4 = Some (Z_to_le_bytes 4 y2) /\ rdn SEGS m (Z_to_bv 64 (s - 136)) 4 = Some (Z_to_le_bytes 4 y3) /\
  rdn SEGS m (Z_to_bv 64 (s - 100)) 4 = Some (Z_to_le_bytes 4 (p_w vd)) /\ rdn SEGS m (Z_to_bv 64 (s - 104)) 4 = Some (Z_to_le_bytes 4 (p_h vd)) /\
  PIXat m pixd vd.

Definition ero_TI (m : word -> option byte) (r : bvmap 5 word) : Prop :=
  W C A m md /\ O23LeptDilW.dil_frame C (s - 144) (p_data vd) (4 * (p_wpl vd * p_h vd)) M7 m /\ POSTM C Ar (s - 144) M7 m /\
  getr r 2 = Z_to_bv 64 (s - 160) /\ getr r 8 = Z_to_bv 64 pixd /\ ero_keep r0 r.

Lemma ero_TI_skip : forall (m : word -> option byte) (r r1 : bvmap 5 word) (k : bv 5),
  ero_TI m r -> regs_agree (fun x => In x [k]%list) r r1 -> In k [13; 14]%list -> ero_TI m r1.
Proof.
  intros m r r1 k (HW & DF & PM & H2 & H8 & KP) AG Hk. unfold ero_TI. cbn [In] in Hk.
  destruct Hk as [<-|[<-|[]]];
    (split; [exact HW|split; [exact DF|split; [exact PM|split; [csr; reflexivity|split; [csr; reflexivity|ero_kc KP]]]]]).
Qed.

Lemma ero_rop : forall (m : word -> option byte) (r r1 : bvmap 5 word) (ret : word) (dx dy dw dh : Z),
  (forall m' r', ero_TI m' r' -> realizes SEGS (mkCfg (mkst r' ret m' al_rom) md) St) ->
  ero_TI m r -> ret_ok ret -> getr r1 1 = ret -> getr r1 10 = Z_to_bv 64 pixd -> getr r1 11 = Z_to_bv 64 dx ->
  getr r1 12 = Z_to_bv 64 dy -> getr r1 13 = Z_to_bv 64 dw -> getr r1 14 = Z_to_bv 64 dh -> getr r1 15 = Z_to_bv 64 0 ->
  regs_agree (fun x => In x [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) r r1 ->
  (- 2 ^ 20 <= dx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= dy <= 2 ^ 20)%Z -> (0 <= dw <= 2 ^ 20)%Z -> (0 <= dh <= 2 ^ 20)%Z ->
  realizes SEGS (mkCfg (mkst r1 (0x7f13c : word) (SARE m s) al_rom) md) St.
Proof.
  intros m r r1 ret dx dy dw dh K TI RO Q1 Q10 Q11 Q12 Q13 Q14 Q15 AG Bx By Bw Bh.
  destruct TI as (HW & DF & PM & H2 & H8 & KP).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ERO_STACK in Hlo.
  assert (WP1 : W C A (SARE m s) md /\ POSTM C Ar (s - 144) M7 (SARE m s)) by (unfold SARE; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (DF1 : O23LeptDilW.dil_frame C (s - 144) (p_data vd) (4 * (p_wpl vd * p_h vd)) M7 (SARE m s)).
  { intros a Ha Hb. rewrite ero_sare_out by (unfold scratch in Ha; lia). exact (DF a Ha Hb). }
  destruct (HRT (SARE m s) DF1) as (_ & _ & _ & _ & _ & _ & PXd1).
  replace (0x7f13c : word) with (Z_to_bv 64 PC_pixRasterop) by (unfold PC_pixRasterop; apply bv_eq; reflexivity).
  apply (pixRasterop_uniclip_W C Ar A (SARE m s) md r1 (s - 160)%Z pixd dx dy dw dh 0%Z vd (Z_to_bv 64 0) ret St
           CK HW1 SUB ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ROP_STACK; lia) ltac:(lia)
           Q1 RO Q10 Q11 Q12 Q13 Q14 Q15 (ero_sare_rd m s ltac:(lia) ltac:(lia)) PXd1 Hd1 SHd Bx By Bw Bh ltac:(left; reflexivity)
           Lpd NEpd Ld Ld0 Ld00).
  intros m' r' HW' CS' PM' PXd' FR' R10'.
  apply K. unfold ero_TI. split; [exact HW'|]. split.
  { intros a Ha Hb. rewrite (FR' a);
      [rewrite ero_sare_out by (unfold scratch in Ha; lia); exact (DF a Ha Hb) | unfold scratch in *; lia | exact Hb]. }
  split; [eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [| exact PM']; lia]|].
  split; [csr; reflexivity|]. split; [csr; reflexivity|]. ero_kc KP.
Qed.

Hypothesis KX : forall m r, ero_TI m r -> realizes SEGS (mkCfg (mkst r (0xa2008 : word) m al_rom) md) St.

Lemma ero_X4W : forall m r, ero_TI m r -> realizes SEGS (mkCfg (mkst r (0xa1fcc : word) m al_rom) md) St.
Proof.
  intros m r TI. pose proof TI as (HW & DF & PM & H2 & H8 & KP).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ERO_STACK in Hlo.
  destruct (HRT m DF) as (RY0 & RY1 & RY2 & RY3 & RW & RH & PXd).
  pose proof SHd as (Dd & Wd & Hd' & WPd & Szd).
  destruct (Z.eq_dec y3 0) as [E|E].
  - rewrite E in RY3. destruct (er_X4s al_rom r m s ltac:(lia) ltac:(lia) RY3 H2) as (r1 & RUN & AG).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    apply KX. eapply ero_TI_skip; [exact TI | exact AG | cbn [In]; first [left; reflexivity | right; left; reflexivity]].
  - destruct (er_X4c al_rom r m s pixd y3 (p_w vd) (p_h vd) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RY3 RW RH
                (W_sok_win C A m md (s - 160)%Z 8%nat CK HW ltac:(lia) ltac:(cbn; lia)) H2 H8)
      as (r1 & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & AG).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    replace (Z_to_bv 64 0xa2008) with (0xa2008 : word) in Q1 by (apply bv_eq; reflexivity).
    exact (ero_rop m r r1 (0xa2008 : word) 0%Z (p_h vd - y3)%Z (p_w vd) y3 KX TI ltac:(red; apply bv_eq; reflexivity)
             Q1 Q10 Q11 Q12 Q13 Q14 Q15 AG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Lemma ero_X3W : forall m r, ero_TI m r -> realizes SEGS (mkCfg (mkst r (0xa1fa0 : word) m al_rom) md) St.
Proof.
  intros m r TI. pose proof TI as (HW & DF & PM & H2 & H8 & KP).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ERO_STACK in Hlo.
  destruct (HRT m DF) as (RY0 & RY1 & RY2 & RY3 & RW & RH & PXd).
  pose proof SHd as (Dd & Wd & Hd' & WPd & Szd).
  destruct (Z.eq_dec y1 0) as [E|E].
  - rewrite E in RY1. destruct (er_X3s al_rom r m s ltac:(lia) ltac:(lia) RY1 H2) as (r1 & RUN & AG).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    apply ero_X4W. eapply ero_TI_skip; [exact TI | exact AG | cbn [In]; first [left; reflexivity | right; left; reflexivity]].
  - destruct (er_X3c al_rom r m s pixd y1 (p_w vd) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RY1 RW
                (W_sok_win C A m md (s - 160)%Z 8%nat CK HW ltac:(lia) ltac:(cbn; lia)) H2 H8)
      as (r1 & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & AG).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    replace (Z_to_bv 64 0xa1fcc) with (0xa1fcc : word) in Q1 by (apply bv_eq; reflexivity).
    exact (ero_rop m r r1 (0xa1fcc : word) 0%Z 0%Z (p_w vd) y1 ero_X4W TI ltac:(red; apply bv_eq; reflexivity)
             Q1 Q10 Q11 Q12 Q13 Q14 Q15 AG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Lemma ero_X2W : forall m r, ero_TI m r -> realizes SEGS (mkCfg (mkst r (0xa1f64 : word) m al_rom) md) St.
Proof.
  intros m r TI. pose proof TI as (HW & DF & PM & H2 & H8 & KP).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ERO_STACK in Hlo.
  destruct (HRT m DF) as (RY0 & RY1 & RY2 & RY3 & RW & RH & PXd).
  pose proof SHd as (Dd & Wd & Hd' & WPd & Szd).
  destruct (Z.eq_dec y2 0) as [E|E].
  - rewrite E in RY2. destruct (er_X2s al_rom r m s ltac:(lia) ltac:(lia) RY2 H2) as (r1 & RUN & AG).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    apply ero_X3W. eapply ero_TI_skip; [exact TI | exact AG | cbn [In]; first [left; reflexivity | right; left; reflexivity]].
  - destruct (er_X2c al_rom r m s pixd y2 (p_w vd) (p_h vd) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RY2 RW RH
                (W_sok_win C A m md (s - 160)%Z 8%nat CK HW ltac:(lia) ltac:(cbn; lia)) H2 H8)
      as (r1 & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & AG).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    replace (Z_to_bv 64 0xa1fa0) with (0xa1fa0 : word) in Q1 by (apply bv_eq; reflexivity).
    exact (ero_rop m r r1 (0xa1fa0 : word) (p_w vd - y2)%Z 0%Z y2 (p_h vd) ero_X3W TI ltac:(red; apply bv_eq; reflexivity)
             Q1 Q10 Q11 Q12 Q13 Q14 Q15 AG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Lemma ero_X1W : forall m r, ero_TI m r -> realizes SEGS (mkCfg (mkst r (0xa1f38 : word) m al_rom) md) St.
Proof.
  intros m r TI. pose proof TI as (HW & DF & PM & H2 & H8 & KP).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ERO_STACK in Hlo.
  destruct (HRT m DF) as (RY0 & RY1 & RY2 & RY3 & RW & RH & PXd).
  pose proof SHd as (Dd & Wd & Hd' & WPd & Szd).
  destruct (Z.eq_dec y0 0) as [E|E].
  - rewrite E in RY0. destruct (er_X1s al_rom r m s ltac:(lia) ltac:(lia) RY0 H2) as (r1 & RUN & AG).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    apply ero_X2W. eapply ero_TI_skip; [exact TI | exact AG | cbn [In]; first [left; reflexivity | right; left; reflexivity]].
  - destruct (er_X1c al_rom r m s pixd y0 (p_h vd) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RY0 RH
                (W_sok_win C A m md (s - 160)%Z 8%nat CK HW ltac:(lia) ltac:(cbn; lia)) H2 H8)
      as (r1 & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & AG).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    replace (Z_to_bv 64 0xa1f64) with (0xa1f64 : word) in Q1 by (apply bv_eq; reflexivity).
    exact (ero_rop m r r1 (0xa1f64 : word) 0%Z 0%Z y0 (p_h vd) ero_X2W TI ltac:(red; apply bv_eq; reflexivity)
             Q1 Q10 Q11 Q12 Q13 Q14 Q15 AG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

End Tail.

End EroW.
