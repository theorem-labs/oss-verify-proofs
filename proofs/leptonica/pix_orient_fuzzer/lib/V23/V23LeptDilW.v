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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptDilW O23LeptPixCopyT O23LeptPixHdr O23LeptCmapValid.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptDilArm O23LeptPma1 O23LeptGrayAT O23LeptBase.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptUb V23LeptErr V23LeptRop_iface V23LeptRopP14 V23LeptDilSegs V23LeptPma1.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require V23LeptPixMisc V23LeptSelGP V23LeptClearAll.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section DilW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition sel_cont (m : word -> option byte) (sv : selv) (c : Z -> Z -> Z) : Prop :=
  forall i j, (0 <= i < v_sy sv)%Z -> (0 <= j < v_sx sv)%Z ->
    (0 <= c i j < 2 ^ 31)%Z /\ rdn SEGS m (Z_to_bv 64 (v_rows sv i + 4 * j)) 4 = Some (Z_to_le_bytes 4 (c i j)).

(* [comment removed for export] *)
Definition dil_reads (m : word -> option byte) (s sel pixd pixs : Z) (sv : selv) (c : Z -> Z -> Z) (vd vs : pixv) : Prop :=
  rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 (v_data sv)) /\
  (forall i, (0 <= i < v_sy sv)%Z -> rdn SEGS m (Z_to_bv 64 (v_data sv + 8 * i)) 8 = Some (Z_to_le_bytes 8 (v_rows sv i))) /\
  (forall i j, (0 <= i < v_sy sv)%Z -> (0 <= j < v_sx sv)%Z -> rdn SEGS m (Z_to_bv 64 (v_rows sv i + 4 * j)) 4 = Some (Z_to_le_bytes 4 (c i j))) /\
  rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 pixs) /\
  rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 (v_cy sv)) /\
  rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (Z_to_le_bytes 4 (v_cx sv)) /\
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 (v_sy sv)) /\
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 (v_sx sv)) /\
  rdn SEGS m (Z_to_bv 64 (s - 104)) 4 = Some (Z_to_le_bytes 4 (p_h vd)) /\
  rdn SEGS m (Z_to_bv 64 (s - 100)) 4 = Some (Z_to_le_bytes 4 (p_w vd)) /\
  PIXat m pixd vd /\ PIXat m pixs vs.

Definition DIL_STACK : Z := 144 + 3584.

Lemma str_dil_msg : str16 0x16ae9 24.
Proof using Type. str16_tac. Qed.
Lemma str_dil_proc : str16 0x17ee3 9.
Proof using Type. str16_tac. Qed.

Section Loop.
Variables (C : lctx) (A A1 : AS) (md1 : Model) (M0 : word -> option byte) (s sel pixd pixs : Z) (sv : selv) (c : Z -> Z -> Z)
          (vd vs : pixv) (St : TSet) (r0 : bvmap 5 word).
Hypothesis CK : Cok C.
Hypothesis SUB : sub_live A A1.
Hypothesis Hs16 : (s mod 16 = 0)%Z.
Hypothesis Hlo : (c_top C - LSTK + DIL_STACK <= s)%Z.
Hypothesis Hhi : (s <= c_top C)%Z.
Hypothesis Hsy : (1 <= v_sy sv <= 10000)%Z.
Hypothesis Hsx : (1 <= v_sx sv <= 10000)%Z.
Hypothesis Hcx : (0 <= v_cx sv < v_sx sv)%Z.
Hypothesis Hcy : (0 <= v_cy sv < v_sy sv)%Z.
Hypothesis Bsel : (0 <= sel)%Z /\ (sel + 32 < 2 ^ 64)%Z.
Hypothesis Bdata : (0 <= v_data sv)%Z /\ (v_data sv + 8 * v_sy sv < 2 ^ 64)%Z.
Hypothesis Brows : forall i, (0 <= i < v_sy sv)%Z -> (0 <= v_rows sv i)%Z /\ (v_rows sv i + 4 * v_sx sv < 2 ^ 64)%Z.
Hypothesis Bc : forall i j, (0 <= i < v_sy sv)%Z -> (0 <= j < v_sx sv)%Z -> (0 <= c i j < 2 ^ 31)%Z.
Hypothesis Asel : (1 <= sel)%Z.
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
Hypothesis HRD : forall m, O23LeptDilW.dil_frame C (s - 128) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m -> dil_reads m s sel pixd pixs sv c vd vs.

Definition dil_keep (r : bvmap 5 word) : Prop := forall x, In x [3; 4; 27]%list -> getr r x = getr r0 x.

Definition dil_KL : Prop :=
  forall m r, W C A1 m md1 -> POSTM C A (s - 128) M0 m -> O23LeptDilW.dil_frame C (s - 128) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m ->
    getr r 2 = Z_to_bv 64 (s - 144) -> getr r 8 = Z_to_bv 64 pixd -> dil_keep r ->
    realizes SEGS (mkCfg (mkst r (0xa1afc : word) m al_rom) md1) St.
Hypothesis KL : dil_KL.

Definition dil_LP (n : nat) : Prop :=
  forall (i j : Z) (r : bvmap 5 word) (m : word -> option byte),
    W C A1 m md1 -> POSTM C A (s - 128) M0 m -> O23LeptDilW.dil_frame C (s - 128) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m ->
    (0 <= i < v_sy sv)%Z -> (0 <= j < v_sx sv)%Z -> Z.of_nat n = ((v_sy sv - 1 - i) * v_sx sv + (v_sx sv - 1 - j))%Z ->
    getr r 2 = Z_to_bv 64 (s - 144) -> getr r 9 = Z_to_bv 64 sel -> getr r 8 = Z_to_bv 64 pixd ->
    getr r 18 = Z_to_bv 64 i -> getr r 19 = Z_to_bv 64 1 -> getr r 20 = Z_to_bv 64 0 -> getr r 21 = Z_to_bv 64 0x7fffffff ->
    getr r 22 = Z_to_bv 64 (4 * j) -> getr r 23 = Z_to_bv 64 j -> getr r 24 = Z_to_bv 64 j ->
    getr r 25 = Z_to_bv 64 (8 * i) -> getr r 26 = Z_to_bv 64 i -> getr r 10 = Z_to_bv 64 (v_sx sv) -> dil_keep r ->
    realizes SEGS (mkCfg (mkst r (0xa1a80 : word) m al_rom) md1) St.

Ltac keep_csr KP := let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [csr; apply KP; cbn; tauto|]); destruct Hx.

Lemma dil_next : forall n (i j : Z) (r : bvmap 5 word) (m : word -> option byte),
  (forall n', n = S n' -> dil_LP n') ->
  W C A1 m md1 -> POSTM C A (s - 128) M0 m -> O23LeptDilW.dil_frame C (s - 128) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m ->
  (0 <= i < v_sy sv)%Z -> (0 <= j < v_sx sv)%Z -> Z.of_nat n = ((v_sy sv - 1 - i) * v_sx sv + (v_sx sv - 1 - j))%Z ->
  getr r 2 = Z_to_bv 64 (s - 144) -> getr r 9 = Z_to_bv 64 sel -> getr r 8 = Z_to_bv 64 pixd ->
  getr r 18 = Z_to_bv 64 i -> getr r 19 = Z_to_bv 64 1 -> getr r 20 = Z_to_bv 64 0 -> getr r 21 = Z_to_bv 64 0x7fffffff ->
  getr r 22 = Z_to_bv 64 (4 * j) -> getr r 23 = Z_to_bv 64 j -> getr r 24 = Z_to_bv 64 j ->
  getr r 25 = Z_to_bv 64 (8 * i) -> getr r 26 = Z_to_bv 64 i -> getr r 10 = Z_to_bv 64 (v_sx sv) -> dil_keep r ->
  realizes SEGS (mkCfg (mkst r (0xa1a70 : word) m al_rom) md1) St.
Proof.
  intros n i j r m IH HW PM DF Hi Hj Hn H2 H9 H8 H18 H19 H20 H21 H22 H23 H24 H25 H26 H10 KP.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold DIL_STACK in Hlo.
  destruct (HRD m DF) as (RD & RR & RC & RT & RCY & RCX & RSY & RSX & RH & RW & PXd & PXs).
  destruct (dl_L al_rom r m s (v_sy sv) (v_sx sv) i j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hi Hj RSY RSX
              H2 H10 H18 H20 H21 H22 H23 H24 H25 H26) as (r1 & pc & RUN & CS & AG).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
  destruct CS as [(Cj & -> & Q18 & Q22 & Q23 & Q24 & Q25 & Q26 & Q10)
                 | [(Cj & Ci & -> & Q18 & Q22 & Q23 & Q24 & Q25 & Q26 & Q10) | (Cj & Ci & ->)]].
  - destruct n as [|n']; [exfalso; cbn in Hn; nia|].
    apply (IH n' eq_refl i (j + 1)%Z r1 m HW PM DF Hi ltac:(lia) ltac:(rewrite Nat2Z.inj_succ in Hn; lia));
      first [keep_csr KP | csr; reflexivity].
  - destruct n as [|n']; [exfalso; cbn in Hn; nia|].
    apply (IH n' eq_refl (i + 1)%Z 0%Z r1 m HW PM DF ltac:(lia) ltac:(lia) ltac:(rewrite Nat2Z.inj_succ in Hn; nia));
      first [keep_csr KP | csr; reflexivity].
  - apply (KL m r1 HW PM DF); first [keep_csr KP | csr; reflexivity].
Qed.

Lemma dil_step : forall n, (forall n', n = S n' -> dil_LP n') -> dil_LP n.
Proof.
  intros n IH i j r m HW PM DF Hi Hj Hn H2 H9 H8 H18 H19 H20 H21 H22 H23 H24 H25 H26 H10 KP.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold DIL_STACK in Hlo.
  destruct (HRD m DF) as (RD & RR & RC & RT & RCY & RCX & RSY & RSX & RH & RW & PXd & PXs).
  pose proof (RR i Hi) as RRi. pose proof (RC i j Hi Hj) as RCij.
  pose proof (Brows i Hi) as [Br0 Br1]. pose proof (Arows i Hi) as [Ar1 Ar4]. pose proof (Bc i j Hi Hj) as Bcij.
  pose proof Adata as [Ad1 Ad8]. pose proof Bdata as [Bd0 Bd1]. pose proof Bsel as [Bs0 Bs1].
  pose proof SHd as (Dd & Wd & Hd' & WPd & Szd). pose proof SHs as (Ds & Ws & Hs' & WPs & Szs).
  destruct (Z.eq_dec (c i j) 1) as [E1|E1].
  - rewrite E1 in RCij.
    destruct (dl_H al_rom r m s sel (v_data sv) (v_rows sv i) i j pixd pixs (p_w vd) (p_h vd) (v_cx sv) (v_cy sv)
                ltac:(lia) ltac:(lia) Asel ltac:(lia) Ad1 ltac:(lia) Ar1 ltac:(lia) Ad8 Ar4
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bpixs
                RD RRi RCij RCX RCY RW RH RT
                (W_sok_win C A1 m md1 (s - 144)%Z 8%nat CK HW ltac:(lia) ltac:(cbn; lia))
                H2 H9 H8 H18 H19 H22 H23 H24 H25 H26)
      as (r1 & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & AG).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    assert (WP1 : W C A1 (SAR m s) md1 /\ POSTM C A (s - 128) M0 (SAR m s)) by (unfold SAR; wp_win CK).
    destruct WP1 as [HW1 PM1].
    assert (OUT1 : forall x : word, ~ (s - 144 <= u x < s - 136)%Z -> SAR m s x = m x).
    { intros x Hx. unfold SAR. rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia |].
      rewrite length_N_to_le_bytes, u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    assert (DF1 : O23LeptDilW.dil_frame C (s - 128) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 (SAR m s)).
    { intros a Ha Hb. rewrite OUT1; [exact (DF a Ha Hb) | unfold scratch in Ha; lia]. }
    destruct (HRD (SAR m s) DF1) as (RD1 & RR1 & RC1 & RT1 & RCY1 & RCX1 & RSY1 & RSX1 & RH1 & RW1 & PXd1 & PXs1).
    assert (R0 : rdn SEGS (SAR m s) (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
    { unfold SAR. pose proof (rdn_wbytes_hit SEGS (word_to_le_bytes 8 (Z_to_bv 64 0)) m (Z_to_bv 64 (s - 144))) as X.
      rewrite length_N_to_le_bytes in X. apply X. rewrite u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    assert (W32 : (p_w vd <= 32 * p_wpl vs)%Z).
    { rewrite WPs, Ew, Edd, Hd1. apply O23LeptDilW.wpl1_le. lia. }
    replace (0x7f13c : word) with (Z_to_bv 64 PC_pixRasterop) by (unfold PC_pixRasterop; apply bv_eq; reflexivity).
    apply (pixRasterop_op14clip_W C A A1 (SAR m s) md1 r1 (s - 144)%Z pixd (j - v_cx sv)%Z (i - v_cy sv)%Z (p_w vd) (p_h vd) pixs 0%Z 0%Z vd vs
             (Z_to_bv 64 0xa1a6c) St
             CK HW1 SUB ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ROP_STACK; lia) ltac:(lia)
             Q1 ltac:(red; apply bv_eq; reflexivity)
             Q10 Q11 Q12 Q13 Q14 Q15 Q16 Q17 R0 PXd1 PXs1 Edd Hd1 SHd SHs
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(rewrite Ew, Eh; exact (O23LeptDilArm.rop2_clip_arm_sx0 (j - v_cx sv) (i - v_cy sv) (p_w vd) (p_h vd) (p_wpl vs) ltac:(lia) W32))
             Lpd Lps NEpd NEps Ld Ld0 Ld00 Ls NEds).
    intros m' r' HW' CS' PM' PXd' PXs' FR' R10'.
    replace (Z_to_bv 64 0xa1a6c) with (0xa1a6c : word) by (apply bv_eq; reflexivity).
    assert (DF2 : O23LeptDilW.dil_frame C (s - 128) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m').
    { intros a Ha Hb. rewrite (FR' a); [rewrite OUT1; [exact (DF a Ha Hb) | unfold scratch in Ha; lia] | unfold scratch in *; lia | exact Hb]. }
    assert (PM2 : POSTM C A (s - 128) M0 m') by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [| exact PM']; lia]).
    destruct (HRD m' DF2) as (RD2 & RR2 & RC2 & RT2 & RCY2 & RCX2 & RSY2 & RSX2 & RH2 & RW2 & PXd2 & PXs2).
    destruct (dl_R al_rom r' m' s (v_sx sv) ltac:(lia) ltac:(lia) ltac:(lia) RSX2 ltac:(csr; reflexivity)) as (r2 & RUN2 & X10 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN2 |].
    apply (dil_next n i j r2 m' IH HW' PM2 DF2 Hi Hj Hn); first [keep_csr KP | csr; reflexivity].
  - destruct (dl_M al_rom r m sel (v_data sv) (v_rows sv i) i j (c i j) Asel ltac:(lia) Ad1 ltac:(lia) Ar1 ltac:(lia) Ad8 Ar4
                ltac:(lia) ltac:(lia) Bcij E1 RD RRi RCij H9 H19 H22 H25) as (r1 & RUN & AG).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    apply (dil_next n i j r1 m IH HW PM DF Hi Hj Hn); first [keep_csr KP | csr; reflexivity].
Qed.

Lemma dil_loop : forall n, dil_LP n.
Proof.
  induction n as [|n IH]; apply dil_step; intros n' E; [discriminate E | injection E as <-; exact IH].
Qed.

End Loop.

Definition dil_cells (s : Z) (ret : word) (r0 : bvmap 5 word) : list (Z * word) :=
  [(s - 8, ret); (s - 16, getr r0 8); (s - 24, getr r0 9); (s - 32, getr r0 18); (s - 40, getr r0 19); (s - 48, getr r0 20);
   (s - 56, getr r0 21); (s - 64, getr r0 22); (s - 72, getr r0 23); (s - 80, getr r0 24); (s - 88, getr r0 25);
   (s - 96, getr r0 26)]%Z.

Lemma dil_cells_FRD : forall m s ret regs, (96 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (FRD m s ret regs) (dil_cells s ret regs).
Proof using Type. intros m s ret regs Hs Hs64. unfold dil_cells, FRD. cbn [cellsZ]. repeat split; rdn_solve. Qed.

Lemma dil_cells_out : forall m m' (lo hi s : Z) ret r0, (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) ->
  (0 <= hi)%Z -> (hi <= s - 96)%Z -> (s < 2 ^ 64)%Z -> cellsZ m (dil_cells s ret r0) -> cellsZ m' (dil_cells s ret r0).
Proof using Type.
  intros m m' lo hi s ret r0 OUT H0 H1 H2. apply (cellsZ_out m m' lo hi _ OUT).
  unfold dil_cells. repeat constructor; cbn [fst]; lia.
Qed.

Lemma dil_cells_frm : forall C s' m m' s ret r0, Cok C -> FRM C s' m m' -> (c_top C - LSTK <= s')%Z -> (s' <= s - 96)%Z ->
  (s < 2 ^ 64)%Z -> cellsZ m (dil_cells s ret r0) -> cellsZ m' (dil_cells s ret r0).
Proof using AL ASR CL P16 PINS.
  intros C s' m m' s ret r0 CK F H1 H2 H3. apply (cellsZ_frm C s' m m' _ CK F H1).
  unfold dil_cells. repeat constructor; cbn [fst]; lia.
Qed.

Local Ltac dx_rz HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
Local Ltac dx_pc RUN :=
  lazymatch type of RUN with msteps _ (mkst _ ?pc _ _) _ =>
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?gpc _ _) _) _ => replace gpc with pc by (apply bv_eq; reflexivity) end end.

Lemma dx_old : forall C A A1 m pixd w h d cd data cv q k,
  O23LeptPixCopyT.pixt_new C A A1 m pixd w h d cd data cv -> live A q = Some k -> live A1 q = Some k.
Proof.
  intros C A A1 m pixd w h d cd data cv q k PN Lq.
  destruct PN as (_ & _ & _ & _ & _ & _ & _ & L0p & L0d & _ & _ & _ & _ & _ & CR).
  assert (Np : q <> Z_to_bv 64 pixd) by (intros E; rewrite E, L0p in Lq; discriminate).
  assert (Nd : q <> Z_to_bv 64 data) by (intros E; rewrite E, L0d in Lq; discriminate).
  destruct CR as [(_ & K)|(ad & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0c & L0a & _ & _ & _ & _ & _ & K)].
  - rewrite (K q Np Nd). exact Lq.
  - assert (Nc : q <> Z_to_bv 64 cd) by (intros E; rewrite E, L0c in Lq; discriminate).
    assert (Na : q <> Z_to_bv 64 ad) by (intros E; rewrite E, L0a in Lq; discriminate).
    rewrite (K q Np Nd Nc Na). exact Lq.
Qed.

Lemma dx_apart : forall C A m md (p q n k : Z), Cok C -> W C A m md ->
  live A (Z_to_bv 64 p) = Some n -> live A (Z_to_bv 64 q) = Some k -> Z_to_bv 64 p <> Z_to_bv 64 q ->
  (0 < n)%Z -> (0 < k)%Z -> (0 <= p < 2 ^ 64)%Z -> (0 <= q < 2 ^ 64)%Z -> (p + n <= q \/ q + k <= p)%Z.
Proof.
  intros C A m md p q n k CK HW Lp Lq NE Hn Hk Hp Hq.
  pose proof (live_apart C A m md _ _ n k CK HW Lp Lq NE ltac:(lia) ltac:(lia)) as D.
  rewrite !u_Z2bv in D by lia. exact D.
Qed.

Lemma dx_rdn : forall (m1 m2 : word -> option byte) (a : Z) (n : nat) (bs : list byte),
  (0 <= a)%Z -> (a + Z.of_nat n < 2 ^ 64)%Z -> (forall x : word, (a <= u x < a + Z.of_nat n)%Z -> m1 x = m2 x) ->
  rdn SEGS m2 (Z_to_bv 64 a) n = Some bs -> rdn SEGS m1 (Z_to_bv 64 a) n = Some bs.
Proof.
  intros m1 m2 a n bs Ha Hn E R. rewrite <- R. apply rdn_ext; rewrite u_Z2bv by lia.
  - lia.
  - intros x Hx. apply E. lia.
Qed.
Lemma dil_exit : forall C A m md regs (s pixs w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet)
    (kR bR : Z) (A1 : AS) (vm1 : VmMaps) (M0 : word -> option byte) (pixd cd data : Z),
  Cok C -> W C A m md -> getr regs 2 = Z_to_bv 64 s ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + DIL_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  PIXat m pixs (O23LeptPixCopyT.hdv w h 1 cm datas) -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  W C A1 M0 (with_vmmaps vm1 md) ->
  POSTM C A s (O23LeptPma1.clone_mem (FRD m s ret regs) pixs (s - 128)) M0 ->
  cellsZ M0 (dil_cells s ret regs) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 pixs) ->
  PIXat M0 pixs (set_rc (O23LeptPixCopyT.hdv w h 1 cm datas) 2) ->
  O23LeptPixCopyT.pixt_new C A A1 M0 pixd w h 1 cd data cv ->
  aroom A1 vm1 (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm)) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ O23LeptPixCopyT.pixt_new C A A' m' pixd w h 1 cd data cv /\ POSTM C A s m m') ->
     aroom A' vm' (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  dil_KL C A A1 (with_vmmaps vm1 md) M0 s pixd (O23LeptPixCopyT.hdv w h 1 cd data) S regs.
Proof.
  intros C A m md regs s pixs w h cm datas cv ret S kR bR A1 vm1 M0 pixd cd data CK HW H2 Hs16 Hlo Hhi Hret PXs HOK Hw Hh
    Lps L0ps HW0 PM0 CE0 Rpp0 PX0 PN ROOM HK.
  unfold dil_KL, dil_keep. intros mL r HWL PML FRL R2 R8 KP.
  unfold O23LeptDilW.dil_frame in FRL. cbn [p_data p_wpl p_h O23LeptPixCopyT.hdv] in FRL.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold DIL_STACK in Hlo.
  pose proof PN as (Gp1 & Gp2 & Gp3 & Gd1 & Gd2 & Gd3 & NEpd & L0Ap & L0Ad & L00p & L00d & L1p & L1d & PXd0 & CR).
  pose proof PXs as (Hs0 & Hs64 & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Bs1 Bs2]. rewrite u_Z2bv in Bs1, Bs2 by lia.
  assert (Hwp : (1 <= wpl_of w 1)%Z) by (unfold wpl_of; apply Z.div_le_lower_bound; lia).
  assert (Hn : (0 < 4 * (wpl_of w 1 * h))%Z) by nia.
  assert (L1s : live A1 (Z_to_bv 64 pixs) = Some 64%Z) by exact (dx_old C A A1 M0 pixd w h 1 cd data cv _ _ PN Lps).
  assert (Nsd : Z_to_bv 64 pixs <> Z_to_bv 64 data) by (intros E; rewrite E, L0Ad in Lps; discriminate).
  assert (Nps : Z_to_bv 64 pixd <> Z_to_bv 64 pixs) by (intros E; rewrite <- E, L0Ap in Lps; discriminate).
  assert (Npd : Z_to_bv 64 pixd <> Z_to_bv 64 data).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. contradiction. }
  pose proof (dx_apart C A1 M0 _ pixs data 64 _ CK HW0 L1s L1d Nsd ltac:(lia) Hn ltac:(lia) ltac:(lia)) as DSD.
  pose proof (dx_apart C A1 M0 _ pixd pixs 64 64 CK HW0 L1p L1s Nps ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as DPS.
  pose proof (dx_apart C A1 M0 _ pixd data 64 _ CK HW0 L1p L1d Npd ltac:(lia) Hn ltac:(lia) ltac:(lia)) as DPD.
  destruct (dl_F al_rom r mL s ltac:(lia) ltac:(lia) R2) as (r1 & RUN1 & F1 & F10 & AG1).
  dx_rz HWL RUN1.
  assert (E2 : getr r1 2 = Z_to_bv 64 (s - 144)) by (csr; reflexivity).
  assert (RO : ret_ok (getr r1 1)) by (rewrite F1; red; apply bv_eq; reflexivity).
  assert (SL : slotok C A1 (s - 144) (s - 128) None) by (cbn; lia).
  assert (RPP : rdn SEGS mL (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 pixs)).
  { apply (dx_rdn mL M0 (s - 128) 8); [lia | cbn; lia | | exact Rpp0].
    intros x Hx. cbn in Hx. apply FRL; [unfold scratch; lia | lia]. }
  assert (PXL : PIXat mL pixs (set_rc (O23LeptPixCopyT.hdv w h 1 cm datas) 2)).
  { apply (PIXat_frame M0); [exact PX0 |]. intros x Hx. apply FRL; [unfold scratch; lia | lia]. }
  destruct (proj1 (Z.mod_divide s 16 ltac:(lia)) Hs16) as [k16 Hk16].
  assert (M144 : ((s - 144) mod 16 = 0)%Z)
    by (rewrite Hk16; replace (k16 * 16 - 144)%Z with ((k16 - 9) * 16)%Z by lia; apply Z.mod_mul; lia).
  assert (M128 : ((s - 128) mod 8 = 0)%Z)
    by (rewrite Hk16; replace (k16 * 16 - 128)%Z with ((2 * k16 - 16) * 8)%Z by lia; apply Z.mod_mul; lia).
  apply (V23LeptPixMisc.pixDestroy_dec_W C A1 mL (with_vmmaps vm1 md) r1 (s - 144) (s - 128) pixs (set_rc (O23LeptPixCopyT.hdv w h 1 cm datas) 2) None
           (getr r1 1) S CK HWL E2 M144 ltac:(lia) ltac:(lia) eq_refl RO F10 SL M128 RPP PXL eq_refl L1s L0ps
           ltac:(intros ? ? E; discriminate E)).
  intros mD rD HWD CSD PXD RD0 OUTD GRD.
  rewrite O23LeptDilW.hdv_rc in PXD.
  assert (MDX : forall x : word, (s - 96 <= u x < s)%Z -> mD x = M0 x).
  { intros x Hx. rewrite OUTD by (try unfold inslot; lia). apply FRL; [unfold scratch; lia | lia]. }
  assert (CED : cellsZ mD (dil_cells s ret regs)).
  { apply (cellsZ_keep M0 mD); [| exact CE0]. unfold dil_cells.
    repeat constructor; cbn [fst]; first [lia | intros x Hx; apply MDX; lia]. }
  cbn [cellsZ dil_cells] in CED. destruct CED as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & _).
  destruct (dl_Z al_rom rD mD s pixd ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
              (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) ltac:(lia) ltac:(lia) ltac:(lia) Hret
              C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (rZ & RUNZ & Z2 & Z10 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & AGZ).
  rewrite F1. dx_pc RUNZ. dx_rz HWD RUNZ.
  apply (HK A1 mD vm1 rZ HWD).
  - apply cs_kept_intro; csr; reflexivity.
  - exists pixd, cd, data. split; [exact Z10 | split].
    + apply (O23LeptDilW.pixt_keep C A A1 M0 mD pixd w h 1 cd data cv PN ltac:(lia)).
      * apply (PIXat_frame M0); [exact PXd0 |]. intros x Hx.
        rewrite OUTD by (try unfold inslot; lia). apply FRL; [unfold scratch; lia | lia].
      * intros q k x Lq L0q Nqd Hx.
        assert (Hk : (0 < k)%Z) by lia.
        destruct (blk_range C A1 M0 _ q k CK HW0 Lq Hk) as [Q1 Q2].
        assert (Nqs : q <> Z_to_bv 64 pixs) by (intros E; rewrite E, Lps in L0q; discriminate).
        pose proof (live_apart C A1 M0 _ q (Z_to_bv 64 pixs) k 64 CK HW0 Lq L1s Nqs ltac:(lia) ltac:(lia)) as D1.
        pose proof (live_apart C A1 M0 _ q (Z_to_bv 64 data) k _ CK HW0 Lq L1d Nqd ltac:(lia) ltac:(lia)) as D2.
        rewrite u_Z2bv in D1, D2 by lia.
        rewrite OUTD by (try unfold inslot; lia). apply FRL; [unfold scratch; lia | lia].
    + assert (WP1 : W C A (FRD m s ret regs) md /\ POSTM C A s m (FRD m s ret regs)) by (unfold FRD; wp_win CK).
      destruct WP1 as [_ P1].
      assert (KIN : forall x : word, (pixs <= u x < pixs + 64)%Z -> mD x = m x)
        by (intros x Hx; exact (O23LeptDilW.pix_same m mD pixs _ PXs PXD x Hx)).
      assert (CLO : forall x : word, ~ (pixs <= u x < pixs + 64)%Z -> ~ (s - 128 <= u x < s - 120)%Z ->
                      O23LeptPma1.clone_mem (FRD m s ret regs) pixs (s - 128) x = FRD m s ret regs x).
      { intros x X1 X2. unfold O23LeptPma1.clone_mem.
        rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
      split.
      * intros x G1 G2 G3 G4 G5. unfold scratch in G5.
        destruct (Z_le_gt_dec pixs (u x)) as [L1|L1]; [destruct (Z_lt_ge_dec (u x) (pixs + 64)) as [L2|L2] |].
        { exact (KIN x ltac:(lia)). }
        all: transitivity (mL x); [apply OUTD; [lia | lia | unfold inslot; lia] |].
        all: transitivity (M0 x); [apply (proj1 PML); [exact G1 | exact G2 | exact G3 | exact G4 | unfold scratch; lia] |].
        all: transitivity (O23LeptPma1.clone_mem (FRD m s ret regs) pixs (s - 128) x);
               [apply (proj1 PM0); [exact G1 | exact G2 | exact G3 | exact G4 | unfold scratch; lia] |].
        all: rewrite CLO by lia; apply (proj1 P1); [exact G1 | exact G2 | exact G3 | exact G4 | unfold scratch; lia].
      * intros q k i Lq Hi.
        destruct (blk_range C A m md q k CK HW Lq ltac:(lia)) as [Q1 Q2].
        assert (UX : u (at_ q i) = (u q + i)%Z) by (unfold at_; rewrite u_Z2bv by lia; reflexivity).
        destruct (Z_le_gt_dec pixs (u (at_ q i))) as [L1|L1]; [destruct (Z_lt_ge_dec (u (at_ q i)) (pixs + 64)) as [L2|L2] |].
        { apply KIN. lia. }
        all: transitivity (mL (at_ q i)); [apply OUTD; [lia | lia | unfold inslot; lia] |].
        all: rewrite (proj2 PML q k i Lq Hi), (proj2 PM0 q k i Lq Hi), CLO by lia.
        all: exact (proj2 P1 q k i Lq Hi).
  - exact ROOM.
Qed.

Lemma dil_succ_W : forall C A m md regs (s pixs sel w h cm datas : Z) (sv : selv) (c : Z -> Z -> Z) (cv : cmapv) (ret : word) (S : TSet)
    (kR bR : Z) (A1 : AS) (m2 : word -> option byte) (vm1 : VmMaps) (r2 : bvmap 5 word) (pixd cd data : Z),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + DIL_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  PIXat m pixs (O23LeptPixCopyT.hdv w h 1 cm datas) -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  sel_at (alloc_top (c_vm C)) A m sel sv -> sel_cont m sv c -> (0 <= v_cx sv < v_sx sv)%Z -> (0 <= v_cy sv < v_sy sv)%Z ->
  (forall p, sel_blk sel sv p -> Z_to_bv 64 p <> Z_to_bv 64 pixs) ->
  W C A1 m2 (with_vmmaps vm1 md) -> POSTM C A (s - 144) (O23LeptPma1.clone_mem (FRD m s ret regs) pixs (s - 128)) m2 ->
  O23LeptPixCopyT.pixt_new C A A1 m2 pixd w h 1 cd data cv ->
  getr r2 2 = Z_to_bv 64 (s - 144) -> getr r2 9 = Z_to_bv 64 sel -> getr r2 18 = Z_to_bv 64 pixs -> getr r2 10 = Z_to_bv 64 pixd ->
  (forall x, In x [3; 4; 27]%list -> getr r2 x = getr regs x) ->
  aroom A1 vm1 (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm)) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ O23LeptPixCopyT.pixt_new C A A' m' pixd w h 1 cd data cv /\ POSTM C A s m m') ->
     aroom A' vm' (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst r2 (0xa19ac : word) m2 al_rom) (with_vmmaps vm1 md)) S.
Proof using AL ASR CL P16 PINS.
  intros C A m md regs s pixs sel w h cm datas sv c cv ret S kR bR A1 m2 vm1 r2 pixd cd data
    CK HW H2 Hs16 Hlo Hhi Hret PXs HOK Hw Hh Lps L0ps Lds SA SC Hcx Hcy SD HW2 PM2 PN R2 R9 R18 R10 KP AR HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold DIL_STACK in Hlo.
  pose proof HOK as (HD1 & Hw2 & Hh2 & Hsz).
  pose proof (O23LeptDilW.wpl1_le w Hw) as W32.
  assert (WH1 : (1 <= wpl_of w 1 * h)%Z) by (clear - W32 Hw Hh; nia).
  pose proof PXs as (Hp0 & Hp64 & _ & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  assert (AL8 : (pixs mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pixs); apply mod16_plus_mod8; [exact ALp | reflexivity]).
  pose proof SA as (Hsy & Hsx & (Bs1 & Bs2 & Bs3) & Lsel & RCs & (Bd1 & Bd2 & Bd3) & Ldat & NEds0 & ROWS & DROWS).
  pose proof PN as (Pd1 & Pd2 & Pd3 & Dd1 & Dd2 & Dd3 & NEpdZ & LAd & LAdata & L0d & L0data & L1d & L1data & PXd2 & CMR).
  pose proof (O23LeptDilW.pixt_sub1 C A A1 m2 pixd w h 1 cd data cv PN) as SUB.
  assert (Lps1 : live A1 (Z_to_bv 64 pixs) = Some 64%Z) by exact (SUB _ _ Lps).
  assert (Lds1 : live A1 (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z) by exact (SUB _ _ Lds).
  assert (NEpd : Z_to_bv 64 pixd <> Z_to_bv 64 data).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. exact (NEpdZ E). }
  assert (NEps : Z_to_bv 64 pixs <> Z_to_bv 64 data) by (intros E; rewrite E in Lps; congruence).
  assert (NEds : Z_to_bv 64 datas <> Z_to_bv 64 data) by (intros E; rewrite E in Lds; congruence).
  pose proof (live_apart C A1 m2 (with_vmmaps vm1 md) _ _ 64 (4 * (wpl_of w 1 * h)) CK HW2 Lps1 L1data NEps ltac:(lia) ltac:(lia)) as DJps.
  pose proof (live_apart C A1 m2 (with_vmmaps vm1 md) _ _ 64 (4 * (wpl_of w 1 * h)) CK HW2 L1d L1data NEpd ltac:(lia) ltac:(lia)) as DJpd.
  rewrite !u_Z2bv in DJps, DJpd by lia.
  assert (M4 : forall z, (z mod 16 = 0)%Z -> (z mod 4 = 0)%Z).
  { intros z Hz. rewrite (Z.div_mod z 16) by lia. rewrite Hz, Z.add_0_r.
    replace (16 * (z / 16))%Z with (4 * (z / 16) * 4)%Z by ring. apply Z.mod_mul. lia. }
  pose proof (M4 s Hs16) as Hs4.
  assert (AL8s : (sel mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r sel); apply mod16_plus_mod8; [exact Bs3 | reflexivity]).
  assert (NEsel : Z_to_bv 64 sel <> Z_to_bv 64 pixs) by exact (SD sel (or_introl eq_refl)).
  assert (NEdat : Z_to_bv 64 (v_data sv) <> Z_to_bv 64 pixs) by exact (SD (v_data sv) (or_intror (or_introl eq_refl))).
  assert (RTR : forall (M M' : word -> option byte) (a : Z) (n : nat) bs, rdn SEGS M (Z_to_bv 64 a) n = Some bs ->
            (0 <= a)%Z -> (a + Z.of_nat n < 2 ^ 64)%Z -> (forall x : word, (a <= u x < a + Z.of_nat n)%Z -> M' x = M x) ->
            rdn SEGS M' (Z_to_bv 64 a) n = Some bs).
  { intros M M' a n bs R H0 H1 HX. rewrite <- R. apply rdn_ext; rewrite u_Z2bv by lia; [lia | exact HX]. }
  assert (WPf : W C A (FRD m s ret regs) md /\ POSTM C A s m (FRD m s ret regs)) by (unfold FRD; wp_win CK).
  destruct WPf as [HWf PMf].
  assert (PXf : PIXat (FRD m s ret regs) pixs (O23LeptPixCopyT.hdv w h 1 cm datas)).
  { apply (PIXat_frame m _ pixs _ PXs). intros x Hx. apply (LIVK_byte A m _ (Z_to_bv 64 pixs) 64 x (proj2 PMf) Lps).
    rewrite u_Z2bv by lia. lia. }
  assert (OUTc : forall x : word, ~ (pixs + 20 <= u x < pixs + 24)%Z -> ~ (s - 128 <= u x < s - 120)%Z ->
            O23LeptPma1.clone_mem (FRD m s ret regs) pixs (s - 128) x = FRD m s ret regs x).
  { intros x Hx1 Hx2. unfold O23LeptPma1.clone_mem.
    rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?length_Z_to_le_bytes, ?u_Z2bv by lia;
                                cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); reflexivity. }
  assert (PX1 : PIXat (O23LeptPma1.clone_mem (FRD m s ret regs) pixs (s - 128)) pixs (set_rc (O23LeptPixCopyT.hdv w h 1 cm datas) 2)).
  { unfold O23LeptPma1.clone_mem. apply PIXat_out.
    - rewrite <- (w2b_Z 4%nat 2%Z) by lia. apply PIX_wr_rc; [exact PXf | lia].
    - rewrite length_N_to_le_bytes, u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - rewrite length_N_to_le_bytes, u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  assert (CE1 : cellsZ (O23LeptPma1.clone_mem (FRD m s ret regs) pixs (s - 128)) (dil_cells s ret regs)).
  { apply (dil_cells_out (FRD m s ret regs) _ (pixs + 20) (s - 120) s ret regs);
      [| lia | lia | lia | exact (dil_cells_FRD m s ret regs ltac:(lia) ltac:(lia))].
    intros x Hx. apply OUTc; lia. }
  assert (RS1 : rdn SEGS (O23LeptPma1.clone_mem (FRD m s ret regs) pixs (s - 128)) (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 pixs)).
  { unfold O23LeptPma1.clone_mem. rewrite <- (w2b_Z 8%nat pixs) by lia.
    pose proof (rdn_wbytes_hit SEGS (word_to_le_bytes 8 (Z_to_bv 64 pixs)) (wbytes (FRD m s ret regs) (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 2%Z))
                  (Z_to_bv 64 (s - 128))) as X.
    rewrite length_N_to_le_bytes in X. apply X. rewrite u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  assert (CE2 : cellsZ m2 (dil_cells s ret regs)) by exact (dil_cells_frm C (s - 144) _ m2 s ret regs CK (proj1 PM2) ltac:(lia) ltac:(lia) ltac:(lia) CE1).
  assert (RS2 : rdn SEGS m2 (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 pixs)).
  { rewrite (FRM_rdn16 C (s - 144) _ m2 (s - 128) 8 CK (proj1 PM2)) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact RS1. }
  assert (PX2 : PIXat m2 pixs (set_rc (O23LeptPixCopyT.hdv w h 1 cm datas) 2)).
  { apply (PIXat_frame _ m2 pixs _ PX1). intros x Hx. apply (LIVK_byte A _ m2 (Z_to_bv 64 pixs) 64 x (proj2 PM2) Lps).
    rewrite u_Z2bv by lia. lia. }
  assert (KM2 : forall q k (x : word), live A q = Some k -> q <> Z_to_bv 64 pixs -> (u q <= u x < u q + k)%Z -> m2 x = m x).
  { intros q k x Lq NE Hx. assert (Hk : (0 < k)%Z) by lia.
    destruct (blk_range C A m md q k CK HW Lq Hk) as [Gq Tq].
    pose proof (live_apart C A m md q (Z_to_bv 64 pixs) k 64 CK HW Lq Lps NE ltac:(lia) ltac:(lia)) as DJ. rewrite u_Z2bv in DJ by lia.
    rewrite (LIVK_byte A _ m2 q k x (proj2 PM2) Lq Hx). rewrite OUTc by lia.
    exact (LIVK_byte A m _ q k x (proj2 PMf) Lq Hx). }
  destruct (dl_B al_rom r2 m2 s pixd pixs sel w h ltac:(lia) ltac:(lia) Hs16 ltac:(lia) ltac:(lia) ltac:(lia) AL8 ltac:(lia) ltac:(lia) ltac:(lia)
              (PIX_rd_w SEGS m2 pixs _ PX2) (PIX_rd_h SEGS m2 pixs _ PX2)
              (W_sok_win C A1 m2 (with_vmmaps vm1 md) (s - 104) 8 CK HW2 ltac:(lia) ltac:(cbn; lia)) R2 R10 R18 R9)
    as (r3 & RUN3 & Q2 & Q1 & Q8 & Q10 & Q11 & Q12 & Q13 & Q14 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  assert (WP3 : W C A1 (PGD m2 s w h) (with_vmmaps vm1 md) /\ POSTM C A s m2 (PGD m2 s w h)) by (unfold PGD; wp_win CK).
  destruct WP3 as [HW3 PM3].
  assert (OUTP : forall x : word, ~ (s - 104 <= u x < s - 96)%Z -> PGD m2 s w h x = m2 x).
  { intros x Hx. unfold PGD.
    rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); reflexivity. }
  assert (RH3 : rdn SEGS (PGD m2 s w h) (Z_to_bv 64 (s - 104)) 4 = Some (Z_to_le_bytes 4 h)).
  { unfold PGD. rewrite rdn_wbytes_hit4 by (rewrite u_Z2bv by lia; lia). rewrite w2b_Z by lia. reflexivity. }
  assert (RW3 : rdn SEGS (PGD m2 s w h) (Z_to_bv 64 (s - 100)) 4 = Some (Z_to_le_bytes 4 w)).
  { unfold PGD. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    rewrite rdn_wbytes_hit4 by (rewrite u_Z2bv by lia; lia). rewrite w2b_Z by lia. reflexivity. }
  assert (RC3 : RECat (PGD m2 s w h) sel (sel_flds (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv) (v_data sv) (v_name sv))).
  { apply (RECat_frame m _ sel _ RCs). intros x Hx.
    change (Z.of_nat (flds_len (sel_flds (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv) (v_data sv) (v_name sv)))) with 32%Z in Hx.
    rewrite OUTP by lia. apply (KM2 (Z_to_bv 64 sel) 32%Z x Lsel NEsel). rewrite u_Z2bv by lia. lia. }
  assert (CO : forall a, (c_top C - LSTK <= a)%Z -> (a + 4 <= c_top C)%Z -> O23LeptSelGP.cell_ok a)
    by (intros a Ha1 Ha2; unfold O23LeptSelGP.cell_ok; lia).
  destruct (V23LeptSelGP.sgp4_run al_rom r3 (PGD m2 s w h) sel (s - 112) (s - 108) (s - 120) (s - 116) (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv)
              (v_data sv) (v_name sv) (Z_to_bv 64 0xa19e0)
              RC3 Bs1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (CO (s - 112)%Z ltac:(lia) ltac:(lia)) (CO (s - 108)%Z ltac:(lia) ltac:(lia)) (CO (s - 120)%Z ltac:(lia) ltac:(lia)) (CO (s - 116)%Z ltac:(lia) ltac:(lia))
              (W_sok_win C A1 _ _ (s - 112) 4 CK HW3 ltac:(lia) ltac:(cbn; lia)) (W_sok_win C A1 _ _ (s - 108) 4 CK HW3 ltac:(lia) ltac:(cbn; lia))
              (W_sok_win C A1 _ _ (s - 120) 4 CK HW3 ltac:(lia) ltac:(cbn; lia)) (W_sok_win C A1 _ _ (s - 116) 4 CK HW3 ltac:(lia) ltac:(cbn; lia))
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) AL8s
              ltac:(rewrite <- Zminus_mod_idemp_l, Hs4; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs4; reflexivity)
              ltac:(rewrite <- Zminus_mod_idemp_l, Hs4; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs4; reflexivity)
              Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14)
    as (r4 & RUN4 & S10 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
  replace (Z_to_bv 64 0xa19e0) with (0xa19e0 : word) by (apply bv_eq; reflexivity).
  assert (WP4 : W C A1 (O23LeptSelGP.SGP4 (PGD m2 s w h) (s - 112) (s - 108) (s - 120) (s - 116) (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv))
                  (with_vmmaps vm1 md) /\
                POSTM C A s (PGD m2 s w h) (O23LeptSelGP.SGP4 (PGD m2 s w h) (s - 112) (s - 108) (s - 120) (s - 116) (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv)))
    by (unfold O23LeptSelGP.SGP4, O23LeptSelGP.wr4; wp_win CK).
  destruct WP4 as [HW4 PM4].
  assert (OUTS : forall x : word, ~ (s - 120 <= u x < s - 104)%Z ->
            O23LeptSelGP.SGP4 (PGD m2 s w h) (s - 112) (s - 108) (s - 120) (s - 116) (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv) x = PGD m2 s w h x).
  { intros x Hx. unfold O23LeptSelGP.SGP4, O23LeptSelGP.wr4.
    rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); reflexivity. }
  assert (OUT24 : forall x : word, ~ (s - 120 <= u x < s - 96)%Z ->
            O23LeptSelGP.SGP4 (PGD m2 s w h) (s - 112) (s - 108) (s - 120) (s - 116) (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv) x = m2 x).
  { intros x Hx. rewrite OUTS by lia. apply OUTP. lia. }
  destruct (V23LeptSelGP.SGP4_rd (PGD m2 s w h) (s - 112) (s - 108) (s - 120) (s - 116) (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv)
              (CO (s - 112)%Z ltac:(lia) ltac:(lia)) (CO (s - 108)%Z ltac:(lia) ltac:(lia)) (CO (s - 120)%Z ltac:(lia) ltac:(lia)) (CO (s - 116)%Z ltac:(lia) ltac:(lia))
              ltac:(unfold O23LeptSelGP.cell_apart; lia) ltac:(unfold O23LeptSelGP.cell_apart; lia) ltac:(unfold O23LeptSelGP.cell_apart; lia)
              ltac:(unfold O23LeptSelGP.cell_apart; lia) ltac:(unfold O23LeptSelGP.cell_apart; lia) ltac:(unfold O23LeptSelGP.cell_apart; lia)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (GSY & GSX & GCY & GCX).
  destruct (dl_C al_rom r4 (O23LeptSelGP.SGP4 (PGD m2 s w h) (s - 112) (s - 108) (s - 120) (s - 116) (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv))
              pixd ltac:(csr; reflexivity))
    as (r5 & RUN5 & P1 & P10 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN5 |].
  assert (PXd4 : PIXat (O23LeptSelGP.SGP4 (PGD m2 s w h) (s - 112) (s - 108) (s - 120) (s - 116) (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv))
                   pixd (O23LeptPixCopyT.hdv w h 1 cd data)).
  { apply (PIXat_frame m2 _ pixd _ PXd2). intros x Hx. apply OUT24. lia. }
  apply (V23LeptClearAll.pixClearAll_W C A A1
           (O23LeptSelGP.SGP4 (PGD m2 s w h) (s - 112) (s - 108) (s - 120) (s - 116) (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv))
           (with_vmmaps vm1 md) r5 (s - 144) pixd (4 * (wpl_of w 1 * h)) (O23LeptPixCopyT.hdv w h 1 cd data) (Z_to_bv 64 0xa19e8) S
           CK HW4 SUB ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold V23LeptClearAll.CLR_STACK, LSF; lia) ltac:(lia) P1 ltac:(red; apply bv_eq; reflexivity) P10
           PXd4 L1d NEpd ltac:(cbn [O23LeptPixCopyT.hdv p_wpl p_h]; lia) ltac:(cbn [O23LeptPixCopyT.hdv p_wpl p_h]; lia)
           L1data ltac:(cbn [O23LeptPixCopyT.hdv p_wpl p_h]; lia) LAdata L0data).
  intros m5 r6 HW5 CS6 PM5 PXd5 ZER5 FR5 V10.
  cbn [O23LeptPixCopyT.hdv p_data p_wpl p_h] in FR5.
  replace (Z_to_bv 64 0xa19e8) with (0xa19e8 : word) by (apply bv_eq; reflexivity).
  assert (K25 : forall x : word, (u x < alloc_top (c_vm C))%Z -> ~ (data <= u x < data + 4 * (wpl_of w 1 * h))%Z -> m5 x = m2 x).
  { intros x Hx1 Hx2. rewrite FR5; [| exact Hx2 | unfold scratch; lia]. apply OUT24. lia. }
  assert (PX5 : PIXat m5 pixs (set_rc (O23LeptPixCopyT.hdv w h 1 cm datas) 2)).
  { apply (PIXat_frame m2 _ pixs _ PX2). intros x Hx. apply K25; lia. }
  assert (PN5 : O23LeptPixCopyT.pixt_new C A A1 m5 pixd w h 1 cd data cv).
  { apply (O23LeptDilW.pixt_keep C A A1 m2 m5 pixd w h 1 cd data cv PN ltac:(lia) PXd5).
    intros q k x Lq L0q NEq Hx. assert (Hk : (0 < k)%Z) by lia.
    destruct (blk_range C A1 m2 (with_vmmaps vm1 md) q k CK HW2 Lq Hk) as [Gq Tq].
    pose proof (live_apart C A1 m2 (with_vmmaps vm1 md) q (Z_to_bv 64 data) k (4 * (wpl_of w 1 * h)) CK HW2 Lq L1data NEq ltac:(lia) ltac:(lia)) as DJ.
    rewrite u_Z2bv in DJ by lia. apply K25; lia. }
  assert (KM5 : forall q k (x : word), live A q = Some k -> q <> Z_to_bv 64 pixs -> (u q <= u x < u q + k)%Z -> m5 x = m x).
  { intros q k x Lq NE Hx. assert (Hk : (0 < k)%Z) by lia.
    destruct (blk_range C A m md q k CK HW Lq Hk) as [Gq Tq].
    assert (NEd : q <> Z_to_bv 64 data) by (intros E; rewrite E in Lq; congruence).
    pose proof (live_apart C A1 m2 (with_vmmaps vm1 md) q (Z_to_bv 64 data) k (4 * (wpl_of w 1 * h)) CK HW2 (SUB q k Lq) L1data NEd ltac:(lia) ltac:(lia)) as DJ.
    rewrite u_Z2bv in DJ by lia. rewrite K25 by lia. exact (KM2 q k x Lq NE Hx). }
  assert (PMX : POSTM C A s (O23LeptPma1.clone_mem (FRD m s ret regs) pixs (s - 128)) m5).
  { eapply POSTM_trans; [exact (POSTM_mono C A (s - 144) s _ _ ltac:(lia) PM2) |].
    eapply POSTM_trans; [exact PM3 |]. eapply POSTM_trans; [exact PM4 |].
    exact (POSTM_mono C A (s - 144) s _ _ ltac:(lia) PM5). }
  assert (CE5 : cellsZ m5 (dil_cells s ret regs)).
  { apply (dil_cells_frm C (s - 144) _ m5 s ret regs CK (proj1 PM5) ltac:(lia) ltac:(lia) ltac:(lia)).
    exact (dil_cells_out m2 _ (s - 120) (s - 96) s ret regs OUT24 ltac:(lia) ltac:(lia) ltac:(lia) CE2). }
  assert (RS5 : rdn SEGS m5 (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 pixs)).
  { rewrite (FRM_rdn16 C (s - 144) _ m5 (s - 128) 8 CK (proj1 PM5)) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    apply (RTR m2 _ (s - 128)%Z 8%nat _ RS2); [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. apply OUT24. lia. }
  assert (RCY5 : rdn SEGS m5 (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 (v_cy sv))).
  { rewrite (FRM_rdn16 C (s - 144) _ m5 (s - 120) 4 CK (proj1 PM5)) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact GCY. }
  assert (RCX5 : rdn SEGS m5 (Z_to_bv 64 (s - 116)) 4 = Some (Z_to_le_bytes 4 (v_cx sv))).
  { rewrite (FRM_rdn16 C (s - 144) _ m5 (s - 116) 4 CK (proj1 PM5)) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact GCX. }
  assert (RSY5 : rdn SEGS m5 (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 (v_sy sv))).
  { rewrite (FRM_rdn16 C (s - 144) _ m5 (s - 112) 4 CK (proj1 PM5)) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact GSY. }
  assert (RSX5 : rdn SEGS m5 (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 (v_sx sv))).
  { rewrite (FRM_rdn16 C (s - 144) _ m5 (s - 108) 4 CK (proj1 PM5)) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact GSX. }
  assert (RH5 : rdn SEGS m5 (Z_to_bv 64 (s - 104)) 4 = Some (Z_to_le_bytes 4 h)).
  { rewrite (FRM_rdn16 C (s - 144) _ m5 (s - 104) 4 CK (proj1 PM5)) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    apply (RTR _ _ (s - 104)%Z 4%nat _ RH3); [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. apply OUTS. lia. }
  assert (RW5 : rdn SEGS m5 (Z_to_bv 64 (s - 100)) 4 = Some (Z_to_le_bytes 4 w)).
  { rewrite (FRM_rdn16 C (s - 144) _ m5 (s - 100) 4 CK (proj1 PM5)) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    apply (RTR _ _ (s - 100)%Z 4%nat _ RW3); [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. apply OUTS. lia. }
  assert (RD0 : rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 (v_data sv)))
    by exact (REC_rd' SEGS m sel _ 4 8 (Z_to_bv 64 (sel + 16)) (v_data sv) RCs ltac:(cbn; lia) eq_refl eq_refl eq_refl).
  assert (RD5 : rdn SEGS m5 (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 (v_data sv))).
  { apply (RTR m _ (sel + 16)%Z 8%nat _ RD0); [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. apply (KM5 (Z_to_bv 64 sel) 32%Z x Lsel NEsel). rewrite u_Z2bv by lia. lia. }
  assert (RR5 : forall i, (0 <= i < v_sy sv)%Z -> rdn SEGS m5 (Z_to_bv 64 (v_data sv + 8 * i)) 8 = Some (Z_to_le_bytes 8 (v_rows sv i))).
  { intros i Hi. destruct (ROWS i Hi) as (_ & _ & _ & _ & BAr).
    pose proof (bytes_at_rdn SEGS m (v_data sv + 8 * i) (Z_to_le_bytes 8 (v_rows sv i)) ltac:(lia)
                  ltac:(rewrite length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) BAr) as X.
    rewrite length_Z_to_le_bytes in X.
    apply (RTR m _ (v_data sv + 8 * i)%Z 8%nat _ X); [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. apply (KM5 (Z_to_bv 64 (v_data sv)) (8 * v_sy sv)%Z x Ldat NEdat).
    rewrite u_Z2bv by lia. lia. }
  assert (RC5 : forall i j, (0 <= i < v_sy sv)%Z -> (0 <= j < v_sx sv)%Z ->
            rdn SEGS m5 (Z_to_bv 64 (v_rows sv i + 4 * j)) 4 = Some (Z_to_le_bytes 4 (c i j))).
  { intros i j Hi Hj. destruct (ROWS i Hi) as ((Br1 & Br2 & Br3) & Lr & _ & _ & _).
    assert (NEr : Z_to_bv 64 (v_rows sv i) <> Z_to_bv 64 pixs) by exact (SD (v_rows sv i) (or_intror (or_intror (ex_intro _ i (conj Hi eq_refl))))).
    apply (RTR m _ (v_rows sv i + 4 * j)%Z 4%nat _ (proj2 (SC i j Hi Hj))); [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. apply (KM5 (Z_to_bv 64 (v_rows sv i)) (4 * v_sx sv)%Z x Lr NEr).
    rewrite u_Z2bv by lia. lia. }
  assert (DR5 : dil_reads m5 s sel pixd pixs sv c (O23LeptPixCopyT.hdv w h 1 cd data) (set_rc (O23LeptPixCopyT.hdv w h 1 cm datas) 2))
    by exact (conj RD5 (conj RR5 (conj RC5 (conj RS5 (conj RCY5 (conj RCX5 (conj RSY5 (conj RSX5 (conj RH5 (conj RW5 (conj PXd5 PX5))))))))))).
  assert (HRDX : forall mm, O23LeptDilW.dil_frame C (s - 128) data (4 * (wpl_of w 1 * h)) m5 mm ->
            dil_reads mm s sel pixd pixs sv c (O23LeptPixCopyT.hdv w h 1 cd data) (set_rc (O23LeptPixCopyT.hdv w h 1 cm datas) 2)).
  { intros mm DF.
    assert (DFh : forall q k (x : word), live A q = Some k -> (u q <= u x < u q + k)%Z -> mm x = m5 x).
    { intros q k x Lq Hx. assert (Hk : (0 < k)%Z) by lia.
      destruct (blk_range C A m md q k CK HW Lq Hk) as [Gq Tq].
      assert (NEd : q <> Z_to_bv 64 data) by (intros E; rewrite E in Lq; congruence).
      pose proof (live_apart C A1 m2 (with_vmmaps vm1 md) q (Z_to_bv 64 data) k (4 * (wpl_of w 1 * h)) CK HW2 (SUB q k Lq) L1data NEd ltac:(lia) ltac:(lia)) as DJ.
      rewrite u_Z2bv in DJ by lia. apply DF; [unfold scratch; lia | lia]. }
    assert (DFs : forall a (n : nat) bs, rdn SEGS m5 (Z_to_bv 64 a) n = Some bs -> (s - 128 <= a)%Z -> (a + Z.of_nat n <= s - 96)%Z ->
              rdn SEGS mm (Z_to_bv 64 a) n = Some bs).
    { intros a n bs R Ha Hn. apply (RTR m5 mm a n bs R); [lia | lia |]. intros x Hx. apply DF; [unfold scratch; lia | lia]. }
    destruct DR5 as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12).
    refine (conj _ (conj _ (conj _ (conj (DFs _ _ _ D4 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
           (conj (DFs _ _ _ D5 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
           (conj (DFs _ _ _ D6 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
           (conj (DFs _ _ _ D7 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
           (conj (DFs _ _ _ D8 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
           (conj (DFs _ _ _ D9 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
           (conj (DFs _ _ _ D10 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
           (conj _ _))))))))))).
    - apply (RTR m5 mm (sel + 16)%Z 8%nat _ D1); [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. apply (DFh (Z_to_bv 64 sel) 32%Z x Lsel). rewrite u_Z2bv by lia. lia.
    - intros i Hi. apply (RTR m5 mm (v_data sv + 8 * i)%Z 8%nat _ (D2 i Hi)); [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. apply (DFh (Z_to_bv 64 (v_data sv)) (8 * v_sy sv)%Z x Ldat).
      rewrite u_Z2bv by lia. lia.
    - intros i j Hi Hj. destruct (ROWS i Hi) as ((Br1 & Br2 & Br3) & Lr & _ & _ & _).
      apply (RTR m5 mm (v_rows sv i + 4 * j)%Z 4%nat _ (D3 i j Hi Hj)); [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. apply (DFh (Z_to_bv 64 (v_rows sv i)) (4 * v_sx sv)%Z x Lr).
      rewrite u_Z2bv by lia. lia.
    - apply (PIXat_frame m5 mm pixd _ D11). intros x Hx. apply DF; [unfold scratch; lia | lia].
    - apply (PIXat_frame m5 mm pixs _ D12). intros x Hx. apply DF; [unfold scratch; lia | lia]. }
  destruct (dl_E al_rom r6 m5 s sel (v_sy sv) (v_sx sv) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) AL8s RSY5 RSX5
              ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r7 & RUN7 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E10 & AG7).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN7 |].
  assert (Bsel : (0 <= sel)%Z /\ (sel + 32 < 2 ^ 64)%Z) by lia.
  assert (Bdata : (0 <= v_data sv)%Z /\ (v_data sv + 8 * v_sy sv < 2 ^ 64)%Z) by lia.
  assert (Adata : (1 <= v_data sv)%Z /\ (v_data sv mod 8 = 0)%Z).
  { split; [lia |]. rewrite <- (Z.add_0_r (v_data sv)). apply mod16_plus_mod8; [exact Bd3 | reflexivity]. }
  assert (Brows : forall i, (0 <= i < v_sy sv)%Z -> (0 <= v_rows sv i)%Z /\ (v_rows sv i + 4 * v_sx sv < 2 ^ 64)%Z).
  { intros i Hi. destruct (ROWS i Hi) as ((Br1 & Br2 & Br3) & _). lia. }
  assert (Arows : forall i, (0 <= i < v_sy sv)%Z -> (1 <= v_rows sv i)%Z /\ (v_rows sv i mod 4 = 0)%Z).
  { intros i Hi. destruct (ROWS i Hi) as ((Br1 & Br2 & Br3) & _). split; [lia | exact (M4 _ Br3)]. }
  assert (Bc : forall i j, (0 <= i < v_sy sv)%Z -> (0 <= j < v_sx sv)%Z -> (0 <= c i j < 2 ^ 31)%Z)
    by (intros i j Hi Hj; exact (proj1 (SC i j Hi Hj))).
  assert (Bpixs : (0 <= pixs < 2 ^ 64)%Z) by lia.
  assert (SHd : rop_shape w h 1 (wpl_of w 1)) by (unfold rop_shape; split; [left; reflexivity | lia]).
  assert (Edd : p_d (set_rc (O23LeptPixCopyT.hdv w h 1 cm datas) 2) = p_d (O23LeptPixCopyT.hdv w h 1 cd data)) by reflexivity.
  assert (Hd1 : p_d (O23LeptPixCopyT.hdv w h 1 cd data) = 1%Z) by reflexivity.
  assert (Ew : p_w (set_rc (O23LeptPixCopyT.hdv w h 1 cm datas) 2) = p_w (O23LeptPixCopyT.hdv w h 1 cd data)) by reflexivity.
  assert (Eh : p_h (set_rc (O23LeptPixCopyT.hdv w h 1 cm datas) 2) = p_h (O23LeptPixCopyT.hdv w h 1 cd data)) by reflexivity.
  pose proof (dil_exit C A m md regs s pixs w h cm datas cv ret S kR bR A1 vm1 m5 pixd cd data
                CK HW H2 Hs16 Hlo Hhi Hret PXs HOK Hw Hh Lps L0ps HW5 PMX CE5 RS5 PX5 PN5 AR HK) as KLX.
  pose proof (dil_loop C A A1 (with_vmmaps vm1 md) m5 s sel pixd pixs sv c (O23LeptPixCopyT.hdv w h 1 cd data)
                (set_rc (O23LeptPixCopyT.hdv w h 1 cm datas) 2) S regs) as LP.
  repeat match type of LP with ?P -> _ => specialize (LP ltac:(assumption)) end.
  lazymatch type of LP with forall n : nat, _ => idtac | ?T => fail 0 "dil_loop premise left:" T end.
  apply (LP (Z.to_nat ((v_sy sv - 1 - 0) * v_sx sv + (v_sx sv - 1 - 0))) 0%Z 0%Z r7 m5 HW5 (POSTM_refl C A (s - 128) m5)
           (fun a _ _ => eq_refl) ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id; [reflexivity | clear - Hsy Hsx; nia])).
  all: first [ csr; reflexivity
             | unfold dil_keep; intros x Hx; cbn [In] in Hx;
               repeat (destruct Hx as [<-|Hx]; [csr; first [reflexivity | apply KP; cbn; tauto] |]); destruct Hx ].
Qed.

Local Ltac dw_rz HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
Local Ltac dw_pc RUN :=
  lazymatch type of RUN with msteps _ (mkst _ ?pc _ _) _ =>
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?gpc _ _) _) _ => replace gpc with pc by (apply bv_eq; reflexivity) end end.

(* [comment removed for export] *)
Theorem pixDilate_new_W : forall C A m md regs (s pixs sel w h cm datas : Z) (sv : selv) (c : Z -> Z -> Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + DIL_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 pixs -> getr regs 12 = Z_to_bv 64 sel ->
  PIXat m pixs (O23LeptPixCopyT.hdv w h 1 cm datas) -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ O23LeptCmapValid.cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  sel_at (alloc_top (c_vm C)) A m sel sv -> sel_cont m sv c -> (0 <= v_cx sv < v_sx sv)%Z -> (0 <= v_cy sv < v_sy sv)%Z ->
  (forall p, sel_blk sel sv p -> Z_to_bv 64 p <> Z_to_bv 64 pixs) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> ((RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm) <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ (forall q, live A' q = live A q) /\ POSTM C A s m m')
       \/ (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ O23LeptPixCopyT.pixt_new C A A' m' pixd w h 1 cd data cv /\ POSTM C A s m m') ) ->
     aroom A' vm' (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0xa1968 : word) m al_rom) md) S.
Proof using P16 PINS.
  intros C A m md regs s pixs sel w h cm datas sv c cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 PXs HOK Hw Hh Lps L0ps Lds HCM
    SA SC Hcx Hcy NEsel kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold DIL_STACK in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof SA as (Hsy & Hsx & Bsel & Lsel & RC & _).
  pose proof (RECat_range _ _ _ RC) as [Hsel0 Hsel32].
  change (Z.of_nat (flds_len (sel_flds (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv) (v_data sv) (v_name sv)))) with 32%Z in Hsel32.
  destruct (blk_range C A m md (Z_to_bv 64 sel) 32 CK HW Lsel ltac:(lia)) as [Gsel TOPsel]. rewrite u_Z2bv in Gsel, TOPsel by lia.
  destruct (dl_A al_rom regs m s 0 pixs sel ret ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 144) 144 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q9 & Q18 & Q13 & Q10 & Q11 & Q12 & AG1).
  dw_rz HW RUN1.
  assert (WP1 : W C A (FRD m s ret regs) md /\ POSTM C A s m (FRD m s ret regs)) by (unfold FRD; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (dil_cells_FRD m s ret regs ltac:(lia) ltac:(lia)) as CE1.
  assert (OUT1 : forall x : word, ~ (s - 96 <= u x < s)%Z -> FRD m s ret regs x = m x).
  { intros x Hx. unfold FRD. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  set (M1 := FRD m s ret regs) in *.
  assert (PXs1 : PIXat M1 pixs (O23LeptPixCopyT.hdv w h 1 cm datas)) by (apply (PIXat_frame m); [exact PXs | intros x Hx; apply OUT1; lia]).
  assert (RC1 : RECat M1 sel (sel_flds (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv) (v_data sv) (v_name sv))).
  { apply (RECat_frame m); [exact RC |]. intros x Hx.
    change (Z.of_nat (flds_len (sel_flds (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv) (v_data sv) (v_name sv)))) with 32%Z in Hx.
    apply OUT1. lia. }
  assert (HCM1 : cm = 0%Z \/ (CMAPat M1 cm cv /\ O23LeptCmapValid.cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\
                               live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right]. split; [| split; [exact CMOK | split; [exact Lcm | exact Larr]]].
    pose proof CM as (Hc0 & Hc64 & _). destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm].
    rewrite u_Z2bv in Gcm, TOPcm by lia.
    apply (CMAPat_frame m); [exact CM|]. intros x Hx. apply OUT1. lia. }
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
  apply (pma1_new_W C A M1 md r1 (s - 144) pixs sel (s - 128) w h cm datas (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv) (v_data sv) (v_name sv) cv
           (Z_to_bv 64 0xa19ac) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold O23LeptPma1.PMA1_STACK, O23LeptGrayAT.PCT_STACK, O23LeptBase.LSF; lia) ltac:(lia)
           Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 Q13 ltac:(lia) ltac:(lia)
           ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity])
           PXs1 HOK Hw Hh Lps L0ps HCM1 RC1 Lsel ltac:(lia) ltac:(lia) kR bR Hrm Hrk Hrb).
  intros A2 m2 vm2 r2 HW2 CS2 OR2 AR2.
  destruct OR2 as [(V10 & LV2 & PM2) | (pixd & cd & data & V10 & PT2 & PM2)].
  - destruct (dl_N al_rom r2 m2 s ltac:(lia) ltac:(lia) (W_sev_got C A2 m2 _ HW2) (W_sev C A2 m2 _ HW2) ltac:(csr; reflexivity) V10)
      as (r3 & RUN3 & V2 & V1 & W10 & W11 & W12 & AG3).
    dw_pc RUN3. dw_rz HW2 RUN3.
    apply (returnErrorPtr_W C A2 m2 _ r3 (s - 144) _ _ 24 9 _ (Z_to_bv 64 0) S CK HW2 V2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia)
             V1 ltac:(red; apply bv_eq; reflexivity) W10 W11 W12 str_dil_msg str_dil_proc).
    intros m4 r4 HW4 OUT4 GR4 CS4 A10.
    assert (CE4 : cellsZ m4 (dil_cells s ret regs)).
    { apply (dil_cells_out m2 m4 (s - 144 - (16 + LSF)) (s - 144) s ret regs OUT4); [unfold LSF; lia | lia | lia |].
      apply (dil_cells_frm C (s - 144) (O23LeptPma1.null_mem M1 (s - 128)) m2 s ret regs CK (proj1 PM2)); [lia | lia | lia |].
      apply (dil_cells_out M1 _ (s - 128) (s - 128 + 8) s ret regs); [| lia | lia | lia | exact CE1].
      intros x Hx. unfold O23LeptPma1.null_mem.
      rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    cbn [cellsZ dil_cells] in CE4. destruct CE4 as (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & _).
    destruct (dl_Nz al_rom r4 m4 s 0 ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) ltac:(lia) ltac:(lia) ltac:(lia) Hret
                R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 ltac:(csr; reflexivity) A10)
      as (r5 & RUN5 & Z2 & Z1 & Z10 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & AG5).
    dw_pc RUN5. dw_rz HW4 RUN5.
    apply (HK A2 m4 vm2 r5 HW4).
    + apply cs_kept_intro; csr; reflexivity.
    + left. split; [exact Z10 | split; [exact LV2 |]].
      eapply POSTM_trans; [exact PM1 |].
      eapply POSTM_trans;
        [exact (POSTM_wbytes_win C A M1 md (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0)) s CK HW1
                  ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia) Hhi) |].
      eapply POSTM_trans; [exact (POSTM_mono C A (s - 144) s _ _ ltac:(lia) PM2) |].
      apply (POSTM_sub C A A2); [intros q k Hq; rewrite LV2; exact Hq |].
      exact (POSTM_range C A2 m2 _ m4 _ _ s CK HW2 OUT4 ltac:(unfold LSF; lia) ltac:(lia) Hhi).
    + exact AR2.
  - replace (Z_to_bv 64 0xa19ac) with (0xa19ac : word) by (apply bv_eq; reflexivity).
    apply (dil_succ_W C A m md regs s pixs sel w h cm datas sv c cv ret S kR bR A2 m2 vm2 r2 pixd cd data
             CK HW H2 Hs16 ltac:(unfold DIL_STACK; lia) Hhi Hret PXs HOK Hw Hh Lps L0ps Lds SA SC Hcx Hcy NEsel HW2 PM2 PT2
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) V10
             ltac:(intros x Hx; cbn in Hx; destruct Hx as [E | [E | [E | []]]]; subst x; csr; reflexivity) AR2).
    intros A' m' vm' regs' HW' CS' EX' AR'. exact (HK A' m' vm' regs' HW' CS' (or_intror EX') AR').
Qed.

End DilW.
