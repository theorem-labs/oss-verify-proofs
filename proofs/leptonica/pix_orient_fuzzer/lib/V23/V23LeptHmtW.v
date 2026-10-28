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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptUb V23LeptErr V23LeptRop_iface V23LeptRop V23LeptRopClip V23LeptRop2C.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptHmtSegs V23LeptRopP8 V23LeptRopP3 V23LeptRopP2 V23LeptRopUC.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptCmap2 V23LeptClearAll V23LeptSetAll V23LeptSetAllC.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptDilW O23LeptDilArm O23LeptPixCopyT O23LeptCmapValid.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LiaRel.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_rel.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_rel.
(* [comment removed for export] *)
Local Ltac kc_clear := repeat match goal with H : _ |- _ => clear H end.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section HmtW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Ltac rzs HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
Ltac grows_chain := repeat (eapply mem_grows_trans; [| apply wbytes_grows]); apply mem_grows_refl.
Ltac pc_as RUN :=
  lazymatch type of RUN with msteps _ (mkst _ ?pc _ _) _ =>
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?gpc _ _) _) _ => replace gpc with pc by (apply bv_eq; reflexivity) end end.

(* [comment removed for export] *)
Definition hmt_keep (r0 r : bvmap 5 word) : Prop := forall x, In x [3; 4]%list -> getr r x = getr r0 x.

Definition HMT_STACK : Z := 160 + 3584.

(* [comment removed for export] *)
Section Tail.
Variables (C : lctx) (Ar A : AS) (md : Model) (M7 : word -> option byte) (s pixd : Z) (vd : pixv) (y0 y1 y2 y3 : Z) (St : TSet)
          (r0 : bvmap 5 word).
Hypothesis CK : Cok C.
Hypothesis SUB : sub_live Ar A.
Hypothesis Hs16 : (s mod 16 = 0)%Z.
Hypothesis Hlo : (c_top C - LSTK + HMT_STACK <= s)%Z.
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
Hypothesis HRT : forall m, O23LeptDilW.dil_frame C (s - 152) (p_data vd) (4 * (p_wpl vd * p_h vd)) M7 m ->
  rdn SEGS m (Z_to_bv 64 (s - 132)) 4 = Some (Z_to_le_bytes 4 y0) /\ rdn SEGS m (Z_to_bv 64 (s - 136)) 4 = Some (Z_to_le_bytes 4 y1) /\
  rdn SEGS m (Z_to_bv 64 (s - 140)) 4 = Some (Z_to_le_bytes 4 y2) /\ rdn SEGS m (Z_to_bv 64 (s - 144)) 4 = Some (Z_to_le_bytes 4 y3) /\
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 (p_w vd)) /\ rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 (p_h vd)) /\
  PIXat m pixd vd.

Definition hmt_TI (m : word -> option byte) (r : bvmap 5 word) : Prop :=
  W C A m md /\ O23LeptDilW.dil_frame C (s - 152) (p_data vd) (4 * (p_wpl vd * p_h vd)) M7 m /\ POSTM C Ar (s - 152) M7 m /\
  getr r 2 = Z_to_bv 64 (s - 160) /\ getr r 8 = Z_to_bv 64 pixd /\ hmt_keep r0 r.

Hypothesis KX : forall m r, hmt_TI m r -> realizes SEGS (mkCfg (mkst r (0xa23d0 : word) m al_rom) md) St.

Lemma hmt_sarh_rd : forall m (t : Z), (160 <= t)%Z -> (t < 2 ^ 64)%Z ->
  rdn SEGS (SARH m t) (Z_to_bv 64 (t - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
  intros m t Ht Ht64. unfold SARH.
  pose proof (rdn_wbytes_hit SEGS (word_to_le_bytes 8 (Z_to_bv 64 0)) m (Z_to_bv 64 (t - 160))) as X.
  rewrite length_N_to_le_bytes in X. apply X. rewrite u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

Lemma hmt_sarh_out : forall m (t : Z) (x : word), (160 <= t)%Z -> (t < 2 ^ 64)%Z -> ~ (t - 160 <= u x < t - 152)%Z -> SARH m t x = m x.
Proof.
  intros m t x Ht Ht64 Hx. unfold SARH.
  rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia |].
  rewrite length_N_to_le_bytes, u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

Lemma hmt_TI_skip : forall (m : word -> option byte) (r r1 : bvmap 5 word) (k : bv 5),
  hmt_TI m r -> regs_agree (fun x => In x [k]%list) r r1 -> In k [13; 14]%list -> hmt_TI m r1.
Proof.
  intros m r r1 k (HW & DF & PM & H2 & H8 & KP) AG Hk. unfold hmt_TI. cbn [In] in Hk.
  destruct Hk as [<-|[<-|[]]];
    (split; [exact HW|split; [exact DF|split; [exact PM|split; [csr; reflexivity|split; [csr; reflexivity|]]]]]);
    intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [csr; apply KP; cbn; tauto|]); destruct Hx.
Qed.

Lemma hmt_rop : forall (m : word -> option byte) (r r1 : bvmap 5 word) (ret : word) (dx dy dw dh : Z),
  (forall m' r', hmt_TI m' r' -> realizes SEGS (mkCfg (mkst r' ret m' al_rom) md) St) ->
  hmt_TI m r -> ret_ok ret -> getr r1 1 = ret -> getr r1 10 = Z_to_bv 64 pixd -> getr r1 11 = Z_to_bv 64 dx ->
  getr r1 12 = Z_to_bv 64 dy -> getr r1 13 = Z_to_bv 64 dw -> getr r1 14 = Z_to_bv 64 dh -> getr r1 15 = Z_to_bv 64 0 ->
  regs_agree (fun x => In x [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) r r1 ->
  (- 2 ^ 20 <= dx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= dy <= 2 ^ 20)%Z -> (0 <= dw <= 2 ^ 20)%Z -> (0 <= dh <= 2 ^ 20)%Z ->
  realizes SEGS (mkCfg (mkst r1 (0x7f13c : word) (SARH m s) al_rom) md) St.
Proof.
  intros m r r1 ret dx dy dw dh K TI RO Q1 Q10 Q11 Q12 Q13 Q14 Q15 AG Bx By Bw Bh.
  destruct TI as (HW & DF & PM & H2 & H8 & KP).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold HMT_STACK in Hlo.
  assert (WP1 : W C A (SARH m s) md /\ POSTM C Ar (s - 152) M7 (SARH m s)) by (unfold SARH; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (DF1 : O23LeptDilW.dil_frame C (s - 152) (p_data vd) (4 * (p_wpl vd * p_h vd)) M7 (SARH m s)).
  { intros a Ha Hb. rewrite hmt_sarh_out by (unfold scratch in Ha; lia). exact (DF a Ha Hb). }
  destruct (HRT (SARH m s) DF1) as (_ & _ & _ & _ & _ & _ & PXd1).
  replace (0x7f13c : word) with (Z_to_bv 64 PC_pixRasterop) by (unfold PC_pixRasterop; apply bv_eq; reflexivity).
  apply (pixRasterop_uniclip_W C Ar A (SARH m s) md r1 (s - 160)%Z pixd dx dy dw dh 0%Z vd (Z_to_bv 64 0) ret St
           CK HW1 SUB ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ROP_STACK; lia) ltac:(lia)
           Q1 RO Q10 Q11 Q12 Q13 Q14 Q15 (hmt_sarh_rd m s ltac:(lia) ltac:(lia)) PXd1 Hd1 SHd Bx By Bw Bh ltac:(left; reflexivity)
           Lpd NEpd Ld Ld0 Ld00).
  intros m' r' HW' CS' PM' PXd' FR' R10'.
  apply K. unfold hmt_TI. split; [exact HW'|]. split.
  { intros a Ha Hb. rewrite (FR' a);
      [rewrite hmt_sarh_out by (unfold scratch in Ha; lia); exact (DF a Ha Hb) | unfold scratch in *; lia | exact Hb]. }
  split; [eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [| exact PM']; lia]|].
  split; [csr; reflexivity|]. split; [csr; reflexivity|].
  intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [csr; apply KP; cbn; tauto|]); destruct Hx.
Qed.

Lemma hmt_X4W : forall m r, hmt_TI m r -> realizes SEGS (mkCfg (mkst r (0xa2394 : word) m al_rom) md) St.
Proof.
  intros m r TI. pose proof TI as (HW & DF & PM & H2 & H8 & KP).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold HMT_STACK in Hlo.
  destruct (HRT m DF) as (RY0 & RY1 & RY2 & RY3 & RW & RH & PXd).
  pose proof SHd as (Dd & Wd & Hd' & WPd & Szd).
  destruct (Z.eq_dec y3 0) as [E|E].
  - rewrite E in RY3. destruct (hm_X4s al_rom r m s ltac:(lia) ltac:(lia) RY3 H2) as (r1 & RUN & AG).
    rzs HW RUN.
    apply KX. eapply hmt_TI_skip; [exact TI | exact AG | cbn [In]; first [left; reflexivity | right; left; reflexivity]].
  - destruct (hm_X4c al_rom r m s pixd y3 (p_w vd) (p_h vd) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RY3 RW RH
                (W_sok_win C A m md (s - 160)%Z 8%nat CK HW ltac:(lia) ltac:(cbn; lia)) H2 H8)
      as (r1 & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & AG).
    rzs HW RUN.
    replace (Z_to_bv 64 0xa23d0) with (0xa23d0 : word) in Q1 by (apply bv_eq; reflexivity).
    exact (hmt_rop m r r1 (0xa23d0 : word) 0%Z (p_h vd - y3)%Z (p_w vd) y3 KX TI ltac:(red; apply bv_eq; reflexivity)
             Q1 Q10 Q11 Q12 Q13 Q14 Q15 AG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Lemma hmt_X3W : forall m r, hmt_TI m r -> realizes SEGS (mkCfg (mkst r (0xa2368 : word) m al_rom) md) St.
Proof.
  intros m r TI. pose proof TI as (HW & DF & PM & H2 & H8 & KP).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold HMT_STACK in Hlo.
  destruct (HRT m DF) as (RY0 & RY1 & RY2 & RY3 & RW & RH & PXd).
  pose proof SHd as (Dd & Wd & Hd' & WPd & Szd).
  destruct (Z.eq_dec y1 0) as [E|E].
  - rewrite E in RY1. destruct (hm_X3s al_rom r m s ltac:(lia) ltac:(lia) RY1 H2) as (r1 & RUN & AG).
    rzs HW RUN.
    apply hmt_X4W. eapply hmt_TI_skip; [exact TI | exact AG | cbn [In]; first [left; reflexivity | right; left; reflexivity]].
  - destruct (hm_X3c al_rom r m s pixd y1 (p_w vd) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RY1 RW
                (W_sok_win C A m md (s - 160)%Z 8%nat CK HW ltac:(lia) ltac:(cbn; lia)) H2 H8)
      as (r1 & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & AG).
    rzs HW RUN.
    replace (Z_to_bv 64 0xa2394) with (0xa2394 : word) in Q1 by (apply bv_eq; reflexivity).
    exact (hmt_rop m r r1 (0xa2394 : word) 0%Z 0%Z (p_w vd) y1 hmt_X4W TI ltac:(red; apply bv_eq; reflexivity)
             Q1 Q10 Q11 Q12 Q13 Q14 Q15 AG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Lemma hmt_X2W : forall m r, hmt_TI m r -> realizes SEGS (mkCfg (mkst r (0xa232c : word) m al_rom) md) St.
Proof.
  intros m r TI. pose proof TI as (HW & DF & PM & H2 & H8 & KP).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold HMT_STACK in Hlo.
  destruct (HRT m DF) as (RY0 & RY1 & RY2 & RY3 & RW & RH & PXd).
  pose proof SHd as (Dd & Wd & Hd' & WPd & Szd).
  destruct (Z.eq_dec y2 0) as [E|E].
  - rewrite E in RY2. destruct (hm_X2s al_rom r m s ltac:(lia) ltac:(lia) RY2 H2) as (r1 & RUN & AG).
    rzs HW RUN.
    apply hmt_X3W. eapply hmt_TI_skip; [exact TI | exact AG | cbn [In]; first [left; reflexivity | right; left; reflexivity]].
  - destruct (hm_X2c al_rom r m s pixd y2 (p_w vd) (p_h vd) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RY2 RW RH
                (W_sok_win C A m md (s - 160)%Z 8%nat CK HW ltac:(lia) ltac:(cbn; lia)) H2 H8)
      as (r1 & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & AG).
    rzs HW RUN.
    replace (Z_to_bv 64 0xa2368) with (0xa2368 : word) in Q1 by (apply bv_eq; reflexivity).
    exact (hmt_rop m r r1 (0xa2368 : word) (p_w vd - y2)%Z 0%Z y2 (p_h vd) hmt_X3W TI ltac:(red; apply bv_eq; reflexivity)
             Q1 Q10 Q11 Q12 Q13 Q14 Q15 AG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Lemma hmt_X1W : forall m r, hmt_TI m r -> realizes SEGS (mkCfg (mkst r (0xa2300 : word) m al_rom) md) St.
Proof.
  intros m r TI. pose proof TI as (HW & DF & PM & H2 & H8 & KP).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold HMT_STACK in Hlo.
  destruct (HRT m DF) as (RY0 & RY1 & RY2 & RY3 & RW & RH & PXd).
  pose proof SHd as (Dd & Wd & Hd' & WPd & Szd).
  destruct (Z.eq_dec y0 0) as [E|E].
  - rewrite E in RY0. destruct (hm_X1s al_rom r m s ltac:(lia) ltac:(lia) RY0 H2) as (r1 & RUN & AG).
    rzs HW RUN.
    apply hmt_X2W. eapply hmt_TI_skip; [exact TI | exact AG | cbn [In]; first [left; reflexivity | right; left; reflexivity]].
  - destruct (hm_X1c al_rom r m s pixd y0 (p_h vd) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RY0 RH
                (W_sok_win C A m md (s - 160)%Z 8%nat CK HW ltac:(lia) ltac:(cbn; lia)) H2 H8)
      as (r1 & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & AG).
    rzs HW RUN.
    replace (Z_to_bv 64 0xa232c) with (0xa232c : word) in Q1 by (apply bv_eq; reflexivity).
    exact (hmt_rop m r r1 (0xa232c : word) 0%Z 0%Z y0 (p_h vd) hmt_X2W TI ltac:(red; apply bv_eq; reflexivity)
             Q1 Q10 Q11 Q12 Q13 Q14 Q15 AG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

End Tail.


(* [comment removed for export] *)
Definition hmt_reads (m : word -> option byte) (s sel pixd pixs : Z) (sv : selv) (c : Z -> Z -> Z) (vd vs : pixv) : Prop :=
  rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 (v_data sv)) /\
  (forall i, (0 <= i < v_sy sv)%Z -> rdn SEGS m (Z_to_bv 64 (v_data sv + 8 * i)) 8 = Some (Z_to_le_bytes 8 (v_rows sv i))) /\
  (forall i j, (0 <= i < v_sy sv)%Z -> (0 <= j < v_sx sv)%Z -> rdn SEGS m (Z_to_bv 64 (v_rows sv i + 4 * j)) 4 = Some (Z_to_le_bytes 4 (c i j))) /\
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 pixs) /\
  rdn SEGS m (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 (v_cy sv)) /\
  rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 (v_cx sv)) /\
  rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 (v_sy sv)) /\
  rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (Z_to_le_bytes 4 (v_sx sv)) /\
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 (p_h vd)) /\
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 (p_w vd)) /\
  PIXat m pixd vd /\ PIXat m pixs vs.

(* [comment removed for export] *)
Section HLoop.
Variables (C : lctx) (A A1 : AS) (md1 : Model) (M0 : word -> option byte) (s sel pixd pixs : Z) (sv : selv) (c : Z -> Z -> Z)
          (vd vs : pixv) (St : TSet) (r0 : bvmap 5 word).
Hypothesis CK : Cok C.
Hypothesis SUB : sub_live A A1.
Hypothesis Hs16 : (s mod 16 = 0)%Z.
Hypothesis Hlo : (c_top C - LSTK + HMT_STACK <= s)%Z.
Hypothesis Hhi : (s <= c_top C)%Z.
Hypothesis Hsy : (1 <= v_sy sv <= 10000)%Z.
Hypothesis Hsx : (1 <= v_sx sv <= 10000)%Z.
Hypothesis Hcx : (0 <= v_cx sv < v_sx sv)%Z.
Hypothesis Hcy : (0 <= v_cy sv < v_sy sv)%Z.
Hypothesis Bsel : (0 <= sel)%Z /\ (sel + 32 < 2 ^ 64)%Z.
Hypothesis Asel : (sel mod 8 = 0)%Z.
Hypothesis Bdata : (0 <= v_data sv)%Z /\ (v_data sv + 8 * v_sy sv < 2 ^ 64)%Z.
Hypothesis Adata : (1 <= v_data sv)%Z /\ (v_data sv mod 8 = 0)%Z.
Hypothesis Brows : forall i, (0 <= i < v_sy sv)%Z -> (0 <= v_rows sv i)%Z /\ (v_rows sv i + 4 * v_sx sv < 2 ^ 64)%Z.
Hypothesis Arows : forall i, (0 <= i < v_sy sv)%Z -> (1 <= v_rows sv i)%Z /\ (v_rows sv i mod 4 = 0)%Z.
Hypothesis Bc : forall i j, (0 <= i < v_sy sv)%Z -> (0 <= j < v_sx sv)%Z -> (0 <= c i j < 2 ^ 31)%Z.
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
Hypothesis HCM : (p_cmap vd <> 0)%Z -> exists cv, live A1 (Z_to_bv 64 (p_cmap vd)) = Some 24%Z /\
  (forall m, O23LeptDilW.dil_frame C (s - 152) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m -> CMAPat m (p_cmap vd) cv).
Hypothesis HRD : forall m, O23LeptDilW.dil_frame C (s - 152) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m -> hmt_reads m s sel pixd pixs sv c vd vs.

(* [comment removed for export] *)
Definition hmt_KL : Prop :=
  forall m r, W C A1 m md1 -> POSTM C A (s - 152) M0 m -> O23LeptDilW.dil_frame C (s - 152) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m ->
    getr r 2 = Z_to_bv 64 (s - 160) -> getr r 8 = Z_to_bv 64 pixd -> getr r 9 = Z_to_bv 64 sel -> hmt_keep r0 r ->
    realizes SEGS (mkCfg (mkst r (0xa22e8 : word) m al_rom) md1) St.
Hypothesis KL : hmt_KL.

Definition hmt_LP (n : nat) : Prop :=
  forall (f : bool) (i j : Z) (r : bvmap 5 word) (m : word -> option byte),
    W C A1 m md1 -> POSTM C A (s - 152) M0 m -> O23LeptDilW.dil_frame C (s - 152) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m ->
    (0 <= i < v_sy sv)%Z -> (0 <= j < v_sx sv)%Z -> Z.of_nat n = ((v_sy sv - 1 - i) * v_sx sv + (v_sx sv - 1 - j))%Z ->
    getr r 2 = Z_to_bv 64 (s - 160) -> getr r 9 = Z_to_bv 64 sel -> getr r 8 = Z_to_bv 64 pixd ->
    getr r 18 = Z_to_bv 64 i -> getr r 19 = Z_to_bv 64 1 -> getr r 20 = Z_to_bv 64 2 -> getr r 21 = Z_to_bv 64 0x7fffffff ->
    getr r 22 = Z_to_bv 64 0 -> getr r 23 = Z_to_bv 64 (4 * j) -> getr r 24 = Z_to_bv 64 j -> getr r 25 = Z_to_bv 64 j ->
    getr r 26 = Z_to_bv 64 (8 * i) -> getr r 27 = Z_to_bv 64 i ->
    getr r 10 = Z_to_bv 64 (if f then 1 else 0) -> hmt_keep r0 r ->
    realizes SEGS (mkCfg (mkst r (0xa21a8 : word) m al_rom) md1) St.

Lemma hmt_keep_tr : forall r r', hmt_keep r0 r -> getr r' 3 = getr r 3 -> getr r' 4 = getr r 4 -> hmt_keep r0 r'.
Proof.
  intros r r' KP E3 E4 x Hx. cbn [In] in Hx.
  destruct Hx as [<-|[<-|[]]]; [rewrite E3 | rewrite E4]; apply KP; cbn; tauto.
Qed.

Lemma hmt_fr : forall m m', POSTM C A (s - 152) M0 m ->
  O23LeptDilW.dil_frame C (s - 152) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m -> POSTM C A (s - 160) m m' ->
  (forall x : word, ~ (p_data vd <= u x < p_data vd + 4 * (p_wpl vd * p_h vd))%Z -> ~ scratch C (s - 160) x -> m' x = m x) ->
  POSTM C A (s - 152) M0 m' /\ O23LeptDilW.dil_frame C (s - 152) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m'.
Proof.
  intros m m' PM DF PM' FR. split.
  - eapply POSTM_trans; [exact PM | eapply POSTM_mono; [| exact PM']; lia].
  - intros a Ha Hb. rewrite (FR a Hb); [exact (DF a Ha Hb) | unfold scratch in *; lia].
Qed.

Lemma hmt_next : forall n (f : bool) (i j : Z) (r : bvmap 5 word) (m : word -> option byte),
  (forall n', n = S n' -> hmt_LP n') ->
  W C A1 m md1 -> POSTM C A (s - 152) M0 m -> O23LeptDilW.dil_frame C (s - 152) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m ->
  (0 <= i < v_sy sv)%Z -> (0 <= j < v_sx sv)%Z -> Z.of_nat n = ((v_sy sv - 1 - i) * v_sx sv + (v_sx sv - 1 - j))%Z ->
  getr r 2 = Z_to_bv 64 (s - 160) -> getr r 9 = Z_to_bv 64 sel -> getr r 8 = Z_to_bv 64 pixd ->
  getr r 18 = Z_to_bv 64 i -> getr r 19 = Z_to_bv 64 1 -> getr r 20 = Z_to_bv 64 2 -> getr r 21 = Z_to_bv 64 0x7fffffff ->
  getr r 22 = Z_to_bv 64 0 -> getr r 23 = Z_to_bv 64 (4 * j) -> getr r 24 = Z_to_bv 64 j -> getr r 25 = Z_to_bv 64 j ->
  getr r 26 = Z_to_bv 64 (8 * i) -> getr r 27 = Z_to_bv 64 i ->
  getr r 10 = Z_to_bv 64 (if f then 1 else 0) -> hmt_keep r0 r ->
  realizes SEGS (mkCfg (mkst r (0xa2194 : word) m al_rom) md1) St.
Proof.
  intros n f i j r m IH HW PM DF Hi Hj Hn H2 H9 H8 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H10 KP.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold HMT_STACK in Hlo.
  destruct (HRD m DF) as (_ & _ & _ & _ & _ & _ & RSY & RSX & _).
  destruct (hm_L al_rom r m s (v_sy sv) (v_sx sv) i j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hi Hj RSY RSX
              H2 H18 H21 H22 H23 H24 H25 H26 H27) as (r1 & pc & RUN & CS & AG).
  rzs HW RUN.
  destruct CS as [(Cj & -> & Q18 & Q23 & Q24 & Q25 & Q26 & Q27)
                 | [(Cj & Ci & -> & Q18 & Q23 & Q24 & Q25 & Q26 & Q27) | (Cj & Ci & ->)]].
  - destruct n as [|n'].
    { exfalso. cbn in Hn. assert (0 <= (v_sy sv - 1 - i) * v_sx sv)%Z by (apply Z.mul_nonneg_nonneg; lia). lia. }
    apply (IH n' eq_refl f i (j + 1)%Z r1 m HW PM DF Hi ltac:(lia) ltac:(rewrite Nat2Z.inj_succ in Hn; lia));
      first [apply (hmt_keep_tr r r1 KP); csr; reflexivity | csr; reflexivity].
  - destruct n as [|n'].
    { exfalso. cbn in Hn. assert (0 < (v_sy sv - 1 - i) * v_sx sv)%Z by (apply Z.mul_pos_pos; lia). lia. }
    apply (IH n' eq_refl f (i + 1)%Z 0%Z r1 m HW PM DF ltac:(lia) ltac:(lia) ltac:(rewrite Nat2Z.inj_succ in Hn; lia));
      first [apply (hmt_keep_tr r r1 KP); csr; reflexivity | csr; reflexivity].
  - apply (KL m r1 HW PM DF); first [apply (hmt_keep_tr r r1 KP); csr; reflexivity | csr; reflexivity].
Qed.

Lemma hmt_join : forall n (op i j : Z) (r : bvmap 5 word) (m : word -> option byte),
  (forall n', n = S n' -> hmt_LP n') -> (op = 12 \/ op = 8 \/ op = 3 \/ op = 2)%Z ->
  W C A1 m md1 -> POSTM C A (s - 152) M0 m -> O23LeptDilW.dil_frame C (s - 152) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m ->
  (0 <= i < v_sy sv)%Z -> (0 <= j < v_sx sv)%Z -> Z.of_nat n = ((v_sy sv - 1 - i) * v_sx sv + (v_sx sv - 1 - j))%Z ->
  getr r 2 = Z_to_bv 64 (s - 160) -> getr r 9 = Z_to_bv 64 sel -> getr r 8 = Z_to_bv 64 pixd ->
  getr r 18 = Z_to_bv 64 i -> getr r 19 = Z_to_bv 64 1 -> getr r 20 = Z_to_bv 64 2 -> getr r 21 = Z_to_bv 64 0x7fffffff ->
  getr r 22 = Z_to_bv 64 0 -> getr r 23 = Z_to_bv 64 (4 * j) -> getr r 24 = Z_to_bv 64 j -> getr r 25 = Z_to_bv 64 j ->
  getr r 26 = Z_to_bv 64 (8 * i) -> getr r 27 = Z_to_bv 64 i ->
  getr r 11 = Z_to_bv 64 (v_cx sv - j) -> getr r 12 = Z_to_bv 64 (v_cy sv - i) -> getr r 13 = Z_to_bv 64 (p_w vd) ->
  getr r 14 = Z_to_bv 64 (p_h vd) -> getr r 15 = Z_to_bv 64 op -> getr r 16 = Z_to_bv 64 pixs -> hmt_keep r0 r ->
  realizes SEGS (mkCfg (mkst r (0xa2180 : word) m al_rom) md1) St.
Proof.
  intros n op i j r m IH Hop HW PM DF Hi Hj Hn H2 H9 H8 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H11 H12 H13 H14 H15 H16 KP.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold HMT_STACK in Hlo.
  pose proof SHd as (Dd & Wd & Hd' & WPd & Szd). pose proof SHs as (Ds & Ws & Hs' & WPs & Szs).
  destruct (hm_S al_rom r m s pixd ltac:(lia) ltac:(lia) (W_sok_win C A1 m md1 (s - 160)%Z 8%nat CK HW ltac:(lia) ltac:(cbn; lia)) H2 H8)
    as (r1 & RUN & Q1 & Q10 & Q17 & AG).
  rzs HW RUN.
  assert (WP1 : W C A1 (SARH m s) md1 /\ POSTM C A (s - 152) M0 (SARH m s)) by (unfold SARH; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (OUT1 : forall x : word, ~ (s - 160 <= u x < s - 152)%Z -> SARH m s x = m x).
  { intros x Hx. unfold SARH. rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia |].
    rewrite length_N_to_le_bytes, u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  assert (DF1 : O23LeptDilW.dil_frame C (s - 152) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 (SARH m s)).
  { intros a Ha Hb. rewrite OUT1; [exact (DF a Ha Hb) | unfold scratch in Ha; lia]. }
  destruct (HRD (SARH m s) DF1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PXd1 & PXs1).
  assert (R0 : rdn SEGS (SARH m s) (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
  { unfold SARH. pose proof (rdn_wbytes_hit SEGS (word_to_le_bytes 8 (Z_to_bv 64 0)) m (Z_to_bv 64 (s - 160))) as X.
    rewrite length_N_to_le_bytes in X. apply X. rewrite u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  assert (W32 : (p_w vd <= 32 * p_wpl vs)%Z) by (rewrite WPs, Ew, Edd, Hd1; apply O23LeptDilW.wpl1_le; lia).
  assert (ARM : rop2_clip_arm (v_cx sv - j) 0%Z (p_w vd) (p_w vd) (p_w vs) (v_cy sv - i) 0%Z (p_h vd) (p_h vd) (p_h vs) (p_wpl vs)).
  { rewrite Ew, Eh. exact (O23LeptDilArm.rop2_clip_arm_sx0 (v_cx sv - j) (v_cy sv - i) (p_w vd) (p_h vd) (p_wpl vs) ltac:(lia) W32). }
  assert (KC : forall m' r', W C A1 m' md1 -> cs_kept r1 r' -> POSTM C A (s - 160) (SARH m s) m' ->
      (forall a : word, ~ scratch C (s - 160) a -> ~ (p_data vd <= u a < p_data vd + 4 * (p_wpl vd * p_h vd))%Z -> m' a = SARH m s a) ->
      realizes SEGS (mkCfg (mkst r' (Z_to_bv 64 0xa2190) m' al_rom) md1) St).
  { intros m' r' HW' CS' PM' FR'.
    assert (DF2 : O23LeptDilW.dil_frame C (s - 152) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m').
    { intros a Ha Hb. rewrite (FR' a); [rewrite OUT1; [exact (DF a Ha Hb) | unfold scratch in Ha; lia] | unfold scratch in *; lia | exact Hb]. }
    assert (PM2 : POSTM C A (s - 152) M0 m') by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [| exact PM']; lia]).
    destruct (hm_R al_rom r' m') as (r2 & RUN2 & X10 & AG2).
    replace (Z_to_bv 64 0xa2190) with (0xa2190 : word) by (apply bv_eq; reflexivity).
    rzs HW' RUN2.
    apply (hmt_next n false i j r2 m' IH HW' PM2 DF2 Hi Hj Hn); first [apply (hmt_keep_tr r r2 KP); csr; reflexivity | csr; reflexivity]. }
  replace (0x7f13c : word) with (Z_to_bv 64 PC_pixRasterop) by (unfold PC_pixRasterop; apply bv_eq; reflexivity).
  destruct Hop as [->|[->|[->| ->]]];
    [pose proof pixRasterop_srcclip_W as K; unfold pixRasterop_srcclip_contract in K
    |pose proof pixRasterop_op8clip_W as K; unfold pixRasterop_op8clip_contract in K
    |pose proof pixRasterop_op3clip_W as K; unfold pixRasterop_op3clip_contract in K
    |pose proof pixRasterop_op2clip_W as K; unfold pixRasterop_op2clip_contract in K];
    apply (K C A A1 (SARH m s) md1 r1 (s - 160)%Z pixd (v_cx sv - j)%Z (v_cy sv - i)%Z (p_w vd) (p_h vd) pixs 0%Z 0%Z vd vs
             (Z_to_bv 64 0xa2190) St CK HW1 SUB ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold ROP_STACK; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity)
             Q10 ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) Q17 R0 PXd1 PXs1 Edd Hd1 SHd SHs
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ARM
             Lpd Lps NEpd NEps Ld Ld0 Ld00 Ls NEds (fun m' r' HW' CS' PM' _ _ FR' _ => KC m' r' HW' CS' PM' FR')).
Qed.

Lemma hmt_step : forall n, (forall n', n = S n' -> hmt_LP n') -> hmt_LP n.
Proof.
  intros n IH f i j r m HW PM DF Hi Hj Hn H2 H9 H8 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H10 KP.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold HMT_STACK in Hlo.
  destruct (HRD m DF) as (RD & RR & RC & RT & RCY & RCX & RSY & RSX & RH & RW & PXd & PXs).
  pose proof (RR i Hi) as RRi. pose proof (RC i j Hi Hj) as RCij.
  pose proof (Brows i Hi) as [Br0 Br1]. pose proof (Arows i Hi) as [Ar1 Ar4]. pose proof (Bc i j Hi Hj) as Bcij.
  pose proof Adata as [Ad1 Ad8]. pose proof Bdata as [Bd0 Bd1]. pose proof Bsel as [Bs0 Bs1].
  pose proof SHd as (Dd & Wd & Hd' & WPd & Szd).
  assert (Wp1 : (1 <= p_wpl vd)%Z) by (rewrite WPd, Hd1; unfold wpl_of; apply Z.div_le_lower_bound; lia).
  assert (NP1 : (1 <= p_wpl vd * p_h vd)%Z).
  { pose proof (Z.mul_le_mono_nonneg 1 (p_wpl vd) 1 (p_h vd) ltac:(lia) Wp1 ltac:(lia) ltac:(lia)). lia. }
  assert (NP31 : (4 * (p_wpl vd * p_h vd) < 2 ^ 31)%Z) by lia.
  destruct (Z.eq_dec (c i j) 1) as [E1|E1]; [|destruct (Z.eq_dec (c i j) 2) as [E2|E2]].
  - rewrite E1 in RCij. destruct f.
    + destruct (hm_H1f al_rom r m sel (v_data sv) (v_rows sv i) i j pixd Bs0 ltac:(lia) Ad1 ltac:(lia) Ar1 ltac:(lia) Ad8 Ar4
                  ltac:(lia) ltac:(lia) RD RRi RCij H9 H8 H19 H20 H23 H26 H10) as (r1 & RUN & Q1 & Q10 & AG).
      rzs HW RUN.
      apply (pixClearAll_W C A A1 m md1 r1 (s - 160)%Z pixd (4 * (p_wpl vd * p_h vd))%Z vd (Z_to_bv 64 0xa2210) St
               CK HW SUB ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
               ltac:(unfold CLR_STACK, LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q10 PXd Lpd NEpd
               NP1 NP31 Ld ltac:(lia) Ld0 Ld00).
      intros m' r' HW' CS' PM' _ _ FR' _.
      destruct (hmt_fr m m' PM DF PM' FR') as [PM2 DF2].
      destruct (HRD m' DF2) as (_ & _ & _ & RT2 & RCY2 & RCX2 & _ & _ & RH2 & RW2 & _).
      destruct (hm_C12 al_rom r' m' s i j (v_cx sv) (v_cy sv) (p_w vd) (p_h vd) pixs ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bpixs RCX2 RCY2 RW2 RH2 RT2
                  ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
        as (r2 & RUN2 & X11 & X12 & X13 & X14 & X15 & X16 & AG2).
      replace (Z_to_bv 64 0xa2210) with (0xa2210 : word) by (apply bv_eq; reflexivity).
      rzs HW' RUN2.
      apply (hmt_join n 12%Z i j r2 m' IH (or_introl eq_refl) HW' PM2 DF2 Hi Hj Hn);
        first [apply (hmt_keep_tr r r2 KP); csr; reflexivity | csr; reflexivity].
    + destruct (hm_H1n al_rom r m s sel (v_data sv) (v_rows sv i) i j (v_cx sv) (v_cy sv) (p_w vd) (p_h vd) pixs
                  ltac:(lia) ltac:(lia) Bs0 ltac:(lia) Ad1 ltac:(lia) Ar1 ltac:(lia) Ad8 Ar4
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bpixs
                  RD RRi RCij RCX RCY RW RH RT H2 H9 H19 H20 H23 H24 H26 H27 H10)
        as (r1 & RUN & X11 & X12 & X13 & X14 & X15 & X16 & AG).
      rzs HW RUN.
      apply (hmt_join n 8%Z i j r1 m IH (or_intror (or_introl eq_refl)) HW PM DF Hi Hj Hn);
        first [apply (hmt_keep_tr r r1 KP); csr; reflexivity | csr; reflexivity].
  - rewrite E2 in RCij. destruct f.
    + destruct (hm_H2f al_rom r m sel (v_data sv) (v_rows sv i) i j pixd Bs0 ltac:(lia) Ad1 ltac:(lia) Ar1 ltac:(lia) Ad8 Ar4
                  ltac:(lia) ltac:(lia) RD RRi RCij H9 H8 H19 H20 H23 H26 H10) as (r1 & RUN & Q1 & Q10 & AG).
      rzs HW RUN.
      apply (pixSetAll_W C A A1 m md1 r1 (s - 160)%Z pixd (4 * (p_wpl vd * p_h vd))%Z vd (Z_to_bv 64 0xa2240) St
               CK HW SUB ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
               ltac:(unfold SETALL_STACK, LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q10 PXd Lpd NEpd
               ltac:(intros Hc; destruct (HCM Hc) as (cv & Lc & CMf); exists cv; split; [exact (CMf m DF) | exact Lc])
               NP1 NP31 Ld ltac:(lia) Ld0 Ld00).
      intros m' r' HW' CS' PM' _ FR'.
      destruct (hmt_fr m m' PM DF PM' FR') as [PM2 DF2].
      destruct (HRD m' DF2) as (_ & _ & _ & RT2 & RCY2 & RCX2 & _ & _ & RH2 & RW2 & _).
      destruct (hm_C3 al_rom r' m' s i j (v_cx sv) (v_cy sv) (p_w vd) (p_h vd) pixs ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bpixs RCX2 RCY2 RW2 RH2 RT2
                  ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
        as (r2 & RUN2 & X11 & X12 & X13 & X14 & X15 & X16 & AG2).
      replace (Z_to_bv 64 0xa2240) with (0xa2240 : word) by (apply bv_eq; reflexivity).
      rzs HW' RUN2.
      apply (hmt_join n 3%Z i j r2 m' IH (or_intror (or_intror (or_introl eq_refl))) HW' PM2 DF2 Hi Hj Hn);
        first [apply (hmt_keep_tr r r2 KP); csr; reflexivity | csr; reflexivity].
    + destruct (hm_H2n al_rom r m s sel (v_data sv) (v_rows sv i) i j (v_cx sv) (v_cy sv) (p_w vd) (p_h vd) pixs
                  ltac:(lia) ltac:(lia) Bs0 ltac:(lia) Ad1 ltac:(lia) Ar1 ltac:(lia) Ad8 Ar4
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bpixs
                  RD RRi RCij RCX RCY RW RH RT H2 H9 H19 H20 H23 H24 H26 H27 H10)
        as (r1 & RUN & X11 & X12 & X13 & X14 & X15 & X16 & AG).
      rzs HW RUN.
      apply (hmt_join n 2%Z i j r1 m IH (or_intror (or_intror (or_intror eq_refl))) HW PM DF Hi Hj Hn);
        first [apply (hmt_keep_tr r r1 KP); csr; reflexivity | csr; reflexivity].
  - destruct (hm_M al_rom r m sel (v_data sv) (v_rows sv i) i j (c i j) Bs0 ltac:(lia) Ad1 ltac:(lia) Ar1 ltac:(lia) Ad8 Ar4
                ltac:(lia) ltac:(lia) Bcij E1 E2 RD RRi RCij H9 H19 H20 H23 H26) as (r1 & RUN & AG).
    rzs HW RUN.
    apply (hmt_next n f i j r1 m IH HW PM DF Hi Hj Hn); first [apply (hmt_keep_tr r r1 KP); csr; reflexivity | csr; reflexivity].
Qed.

Lemma hmt_loop : forall n, hmt_LP n.
Proof using All.
  intro n. induction n as [|n IH]; apply hmt_step; intros n' E; [discriminate | injection E as <-; exact IH].
Qed.

End HLoop.

End HmtW.
