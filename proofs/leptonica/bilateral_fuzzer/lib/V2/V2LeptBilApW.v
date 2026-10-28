(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach FPStepsB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom LeptSlots LeptExec LeptExecW LeptExecFP LeptExecX DitherLib DitherLoop LeptCmapArr LeptExecB LeptArithB LeptBracketB LeptCellsB LeptRecs LeptRoomPC LeptRoomBL SumSpecs.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptErr V2LeptPixHdr V2LeptPixCreate V2LeptPixCreateT2 V2LeptPixCopyTR V2LeptGrayATR V2LeptPixaCreate V2LeptLinePtrs V2LeptBl_iface V2LeptBilSegs V2LeptBilCW1 V2LeptBilCW2 V2LeptBilCW3 V2LeptBilCW4 V2LeptBilApRun V2_code_bilateralApply V2LeptBilApSegs.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import FpReal FpBound FpSiteB.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
(* [comment removed for export] *)
#[local] Opaque RiscvSemantics.store_ok.

Lemma str_ap_msg : str16 67429 13.
Proof. str16_tac. Qed.
Lemma str_ap_proc : str16 70815 14.
Proof. str16_tac. Qed.

Lemma apd_wr_readable : wr_readable SEGS.
Proof.
  intros seg Hin Hwr. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
Qed.

Section ApDeriv.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma apd_top47 : forall C, Cok C -> (alloc_top (c_vm C) + 8192 <= 2 ^ 47)%Z.
Proof.
  intros C CK. pose proof (ck_top C CK). pose proof (ck_sp0 C CK). pose proof (ck_sp0hi C CK). unfold LSTK in *. lia.
Qed.

Lemma apd_sok_blk : forall C A m md (p : word) (k a : Z) (n : nat), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + Z.of_nat n <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros C A m md p k a n CK HW L Hlo Hhi Hk. pose proof (u64_range p). rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
  destruct (blk_byte C A m md p k x CK HW L ltac:(lia)) as (_ & D & _). exact (D E).
Qed.

Lemma apd_blk : forall C A m md (p n : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some n -> (0 <= p < 2 ^ 64)%Z -> (0 < n)%Z ->
  (p mod 16 = 0)%Z /\ (4096 <= p)%Z /\ (p + n + 8192 <= 2 ^ 47)%Z.
Proof.
  intros C A m md p n CK HW L Hp Hn.
  pose proof (apd_top47 C CK) as T.
  destruct (blk_range C A m md (Z_to_bv 64 p) n CK HW L Hn) as [G1 G2]. rewrite u_Z2bv in G1, G2 by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) L) as (_ & A16 & _). rewrite u_Z2bv in A16 by lia.
  repeat split; lia.
Qed.

Lemma apd_rdb : forall C A m md (p n a : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some n -> (0 <= p < 2 ^ 64)%Z ->
  (p <= a < p + n)%Z -> (p + n < 2 ^ 64)%Z -> exists b, rdn SEGS m (Z_to_bv 64 a) 1 = Some [b].
Proof.
  intros C A m md p n a CK HW L Hp Ha Hn.
  assert (SOK : store_ok SEGS m (Z_to_bv 64 a) 1 = true)
    by (eapply (apd_sok_blk C A m md (Z_to_bv 64 p) n a 1 CK HW L); rewrite u_Z2bv by lia; cbn; lia).
  destruct (store_ok_rdn SEGS m 1 (Z_to_bv 64 a) apd_wr_readable SOK) as (bs & R & Lb).
  destruct bs as [|b0 [|b1 bs]]; cbn in Lb; try discriminate. exists b0. exact R.
Qed.

Lemma apd_rds : forall C Ar Af A m md bil pixs v b, Cok C -> W C A m md -> sub_live Af A -> bil_obj C Ar Af m bil pixs v b ->
  (1 <= p_w v)%Z -> (1 <= p_h v)%Z ->
  ap_rds m (bw_kx b) (bw_kf b) (bw_ls b) (4 * wpl_of (p_w v) 8) (p_h v) (bw_linesf b) (bw_datad b).
Proof.
  intros C Ar Af A m md bil pixs v b CK HW SUB BO Hw Hh.
  destruct BO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KX & KF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MEM & _ & _ & _ & _ & LINES & _).
  pose proof (apd_top47 C CK) as T.
  assert (WP : (1 <= wpl_of (p_w v) 8)%Z) by (unfold wpl_of; apply Z.div_le_lower_bound; lia).
  assert (HN : (1 <= wpl_of (p_w v) 8 * p_h v)%Z) by nia.
  unfold ap_rds. split; [exact KX|]. split; [exact KF|]. split; [|split; [|split; [|]]].
  - intros k Hk. destruct (LINES k Hk) as (_ & _ & _ & _ & _ & R & _). exact R.
  - intros k i Hk Hi. destruct (LINES k Hk) as (_ & _ & _ & _ & _ & _ & LP). exact (LP i Hi).
  - intros k p Hk Hp.
    destruct (MEM k Hk) as (_ & _ & D1 & D2 & _ & _ & _ & _ & _ & _ & Ld & _). apply SUB in Ld.
    apply (apd_rdb C A m md (bw_datad b k) (4 * (wpl_of (p_w v) 8 * p_h v)) p CK HW Ld); lia.
  - intros k Hk.
    destruct (MEM k Hk) as (_ & _ & D1 & D2 & _ & _ & _ & _ & _ & _ & Ld & _). apply SUB in Ld.
    destruct (LINES k Hk) as (R1 & Ll & _). apply SUB in Ll.
    destruct (apd_blk C A m md (bw_linesf b k) (8 * p_h v) CK HW Ll ltac:(lia) ltac:(lia)) as (L16 & L4 & L47).
    destruct (apd_blk C A m md (bw_datad b k) (4 * (wpl_of (p_w v) 8 * p_h v)) CK HW Ld ltac:(lia) ltac:(lia)) as (D16 & D4 & D47).
    repeat split; try lia.
    + apply (proj2 (Z.mod_divide _ 8 ltac:(lia))). destruct (proj1 (Z.mod_divide _ 16 ltac:(lia)) L16) as [q Hq]. exists (2 * q)%Z. lia.
    + apply mod16_mod4. exact D16.
Qed.

Lemma apd_ro : forall C A m md, Cok C -> W C A m md -> ap_ro m.
Proof.
  intros C A m md CK HW. pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *.
  unfold ap_ro.
  repeat split;
    (lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) 8 = _ =>
       rewrite <- p16_segs; rewrite (W_rdn_ro C A m md a 8 HW) by (cbn; lia); rewrite p16_segs
     end);
    first [exact ro_one | exact ro_half | exact ro_lo | exact ro_hi].
Qed.

Lemma apd_sep : forall C A m md (p k q n : Z), Cok C -> W C A m md ->
  live A (Z_to_bv 64 p) = Some k -> live A (Z_to_bv 64 q) = Some n -> Z_to_bv 64 p <> Z_to_bv 64 q ->
  (0 <= p < 2 ^ 64)%Z -> (0 <= q < 2 ^ 64)%Z -> (0 <= k)%Z -> (0 <= n)%Z -> (p + k <= q \/ q + n <= p)%Z.
Proof.
  intros C A m md p k q n CK HW Lp Lq NE Hp Hq Hk Hn.
  pose proof (round16_ge k Hk). pose proof (round16_ge n Hn).
  destruct (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lp Lq NE) as [D|D];
    rewrite !u_Z2bv in D by lia; lia.
Qed.

Lemma apd_img : forall C A m md (p n : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some n -> (0 < n)%Z ->
  (0 <= p)%Z -> (p + n < 2 ^ 64)%Z -> (p + n <= 0x12588 \/ 0x125d8 <= p)%Z.
Proof.
  intros C A m md p n CK HW L Hn Hp Hpn.
  pose proof (exW_blk_img_apart C A m md p n CK HW L Hn Hp Hpn) as HI. cbn [fst snd ll_img LLU16] in HI.
  specialize (HI ltac:(lia)). lia.
Qed.

Lemma apd_frame_img : forall C (s : Z), Cok C -> (c_top C - LSTK <= s - 160)%Z -> (0x125d8 <= s - 160)%Z.
Proof.
  intros C s CK H. pose proof (ck_img C CK). pose proof (ck_top C CK). cbn [fst snd ll_img LLU16] in *. unfold LSTK in *. lia.
Qed.

Lemma apd_fresh : forall (Ab : AS) (q dd n : Z), live Ab (Z_to_bv 64 dd) = None -> live Ab (Z_to_bv 64 q) = Some n ->
  Z_to_bv 64 q <> Z_to_bv 64 dd.
Proof. intros Ab q dd n L0 L1 E. rewrite E in L1. congruence. Qed.

Lemma apd_apart_dd : forall C Ar Af A m md bil pixs v b (dd n : Z), Cok C -> W C A m md -> sub_live Af A -> bil_obj C Ar Af m bil pixs v b ->
  (1 <= p_w v)%Z -> (1 <= p_h v)%Z ->
  live A (Z_to_bv 64 dd) = Some n -> (0 <= dd < 2 ^ 64)%Z -> (0 < n)%Z ->
  Z_to_bv 64 (bw_kx b) <> Z_to_bv 64 dd -> Z_to_bv 64 (bw_kf b) <> Z_to_bv 64 dd -> Z_to_bv 64 (bw_ls b) <> Z_to_bv 64 dd ->
  (forall k, (0 <= k < 10)%Z -> Z_to_bv 64 (bw_linesf b k) <> Z_to_bv 64 dd /\ Z_to_bv 64 (bw_datad b k) <> Z_to_bv 64 dd) ->
  ap_apart dd n (bw_kx b) (bw_kf b) (bw_ls b) (4 * wpl_of (p_w v) 8) (p_h v) (bw_linesf b) (bw_datad b).
Proof.
  intros C Ar Af A m md bil pixs v b dd n CK HW SUB BO Hw Hh Ld Hdd Hn NEx NEf NEl NEk.
  pose proof (apd_top47 C CK) as T.
  pose proof (apd_blk C A m md dd n CK HW Ld Hdd Hn) as (_ & _ & D47).
  destruct BO as (_ & _ & _ & BKX & BKF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MEM & Hls & _ & _ & Lls & LINES & _).
  destruct BKX as (KX1 & KX2 & _ & Lkx & _). destruct BKF as (KF1 & KF2 & _ & Lkf & _).
  apply SUB in Lkx. apply SUB in Lkf. apply SUB in Lls.
  assert (WP : (1 <= wpl_of (p_w v) 8)%Z) by (unfold wpl_of; apply Z.div_le_lower_bound; lia).
  assert (HN : (1 <= wpl_of (p_w v) 8 * p_h v)%Z) by nia.
  pose proof (apd_blk C A m md (bw_ls b) 80 CK HW Lls ltac:(lia) ltac:(lia)) as (_ & LS4 & LS47).
  unfold ap_apart. split; [|split; [|split; [|split]]].
  - apply (apd_sep C A m md (bw_kx b) 1024 dd n CK HW Lkx Ld NEx); lia.
  - apply (apd_sep C A m md (bw_kf b) 1024 dd n CK HW Lkf Ld NEf); lia.
  - apply (apd_sep C A m md (bw_ls b) 80 dd n CK HW Lls Ld NEl); lia.
  - intros k Hk. destruct (NEk k Hk) as [NE1 NE2].
    destruct (MEM k Hk) as (_ & _ & D1 & D2 & _ & _ & _ & _ & _ & _ & Ldk & _). apply SUB in Ldk.
    destruct (LINES k Hk) as (R1 & Llf & _). apply SUB in Llf.
    split.
    + apply (apd_sep C A m md (bw_linesf b k) (8 * p_h v) dd n CK HW Llf Ld NE1); lia.
    + pose proof (apd_sep C A m md (bw_datad b k) (4 * (wpl_of (p_w v) 8 * p_h v)) dd n CK HW Ldk Ld NE2
                    ltac:(lia) Hdd ltac:(lia) ltac:(lia)). lia.
  - apply (apd_img C A m md dd n CK HW Ld Hn ltac:(lia) ltac:(lia)).
Qed.

Lemma apd_apart_frame : forall C Ar Af A m md bil pixs v b (s : Z), Cok C -> W C A m md -> sub_live Af A -> bil_obj C Ar Af m bil pixs v b ->
  (1 <= p_w v)%Z -> (1 <= p_h v)%Z -> (c_top C - LSTK <= s - 160)%Z ->
  ap_apart (s - 160) 160 (bw_kx b) (bw_kf b) (bw_ls b) (4 * wpl_of (p_w v) 8) (p_h v) (bw_linesf b) (bw_datad b).
Proof.
  intros C Ar Af A m md bil pixs v b s CK HW SUB BO Hw Hh Hs.
  pose proof (ck_top C CK) as T1. unfold LSTK in *.
  pose proof (apd_frame_img C s CK ltac:(unfold LSTK; lia)) as FI.
  destruct BO as (_ & _ & _ & BKX & BKF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MEM & Hls & _ & _ & Lls & LINES & _).
  destruct BKX as (KX1 & KX2 & _). destruct BKF as (KF1 & KF2 & _). apply SUB in Lls.
  assert (WP : (1 <= wpl_of (p_w v) 8)%Z) by (unfold wpl_of; apply Z.div_le_lower_bound; lia).
  destruct (blk_range C A m md (Z_to_bv 64 (bw_ls b)) 80 CK HW Lls ltac:(lia)) as [LS1 LS2]. rewrite u_Z2bv in LS1, LS2 by lia.
  unfold ap_apart. split; [lia|]. split; [lia|]. split; [lia|]. split; [|lia].
  intros k Hk.
  destruct (MEM k Hk) as (_ & _ & D1 & D2 & _).
  destruct (LINES k Hk) as (R1 & Llf & _). apply SUB in Llf.
  destruct (blk_range C A m md (Z_to_bv 64 (bw_linesf b k)) (8 * p_h v) CK HW Llf ltac:(lia)) as [LF1 LF2].
  rewrite u_Z2bv in LF1, LF2 by lia.
  split; [lia | nia].
Qed.

End ApDeriv.

Section ApLoops.
Variable rom : word -> option byte.

Lemma ap_loops_core : forall fr cs regs (m : word -> option byte) (s kx kf ls wpl h w datas dd pixd : Z) (linesf datak : Z -> Z),
  frm_zero cs ->
  (4096 + 160 <= s <= 2 ^ 47)%Z -> (s mod 16 = 0)%Z ->
  (1 <= w < 2 ^ 31)%Z -> (w <= 4 * wpl)%Z -> (wpl <= 20000)%Z -> (1 <= h)%Z -> (h <= 20000)%Z ->
  (datas mod 4 = 0)%Z -> (4096 <= datas)%Z -> (datas + 4 * wpl * h <= 2 ^ 47)%Z -> (datas + 4 * wpl * h <= s - 160 \/ s <= datas)%Z ->
  (dd mod 4 = 0)%Z -> (4096 <= dd)%Z -> (dd + 4 * wpl * h <= 2 ^ 47)%Z -> (dd + 4 * wpl * h <= s - 160 \/ s <= dd)%Z ->
  (kx mod 4 = 0)%Z -> (4096 <= kx)%Z -> (kx + 1024 <= 2 ^ 47)%Z -> (kf mod 4 = 0)%Z -> (4096 <= kf)%Z -> (kf + 1024 <= 2 ^ 47)%Z ->
  (ls mod 8 = 0)%Z -> (4096 <= ls)%Z -> (ls + 80 <= 2 ^ 47)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
  (forall p, (datas <= p < datas + 4 * wpl * h)%Z -> exists b, rdn SEGS m (Z_to_bv 64 p) 1 = Some [b]) ->
  (forall p, (dd <= p < dd + 4 * wpl * h)%Z -> store_ok SEGS m (Z_to_bv 64 p) 1 = true) ->
  store_ok SEGS m (Z_to_bv 64 (s - 160)) 160 = true ->
  ap_rds m kx kf ls (4 * wpl) h linesf datak -> ap_ro m ->
  ap_apart dd (4 * wpl * h) kx kf ls (4 * wpl) h linesf datak -> ap_apart (s - 160) 160 kx kf ls (4 * wpl) h linesf datak ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 wpl) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 datas ->
  getr regs 18 = Z_to_bv 64 wpl -> getr regs 19 = Z_to_bv 64 dd ->
  getr regs 22 = Z_to_bv 64 1 -> getr regs 23 = Z_to_bv 64 kx -> getr regs 24 = Z_to_bv 64 kf -> getr regs 25 = Z_to_bv 64 ls ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a650) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3aa18) M' rom /\ frm_zero cs' /\
       rinv [(dd, (4 * wpl * h)%Z); ((s - 160)%Z, 16%Z); ((s - 136)%Z, 24%Z)] m M' /\ getr regs' 8 = Z_to_bv 64 pixd /\
       regs_agree (fun r => In r (13 :: 14 :: 15 :: API)%list) regs regs' /\ ap_fp fr fr').
Proof.
  intros fr cs regs m s kx kf ls wpl h w datas dd pixd linesf datak FZ Hs As Hw Hww Hwpl Hh1 Hh2 Ads Hds1 Hds2 Hdsf
    Add Hdd1 Hdd2 Hddf Akx Hkx1 Hkx2 Akf Hkf1 Hkf2 Als Hls1 Hls2 Hpd RDs SOKd SOKf RDS RO APd APf C144 C112 C108
    H2 H8 H9 H18 H19 H22 H23 H24 H25.
  assert (HW0 : (0 <= wpl)%Z) by lia.
  assert (Hdsn : (datas <= datas + 4 * wpl * h)%Z) by nia.
  assert (Hddn : (dd <= dd + 4 * wpl * h)%Z) by nia.
  pose proof APf as APf'. destruct APf' as (_ & _ & _ & _ & FIMG).
  eapply reach_bind.
  { apply (ap_B2 rom (mkFP fr cs) regs m s pixd datas wpl dd Hs As ltac:(lia) ltac:(lia) Hpd ltac:(lia) SOKf H2 H8 H9 H18 H19). }
  intros fin (regs1 & M1 & -> & RI1 & C160 & C152 & C136 & C128 & C120 & E11 & E12 & E13 & E14 & E15 & AG1).
  assert (G1 : mem_grows m M1) by exact (proj1 RI1).
  assert (K144 : rdn SEGS M1 (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 wpl))
    by (rewrite (rinv_rdn SEGS _ m M1 (s - 144) 8 RI1) by first [lia | (intros r Hr; cbn in Hr; destruct Hr as [<-|[<-|[]]]; cbn; lia)]; exact C144).
  assert (K112 : rdn SEGS M1 (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h))
    by (rewrite (rinv_rdn SEGS _ m M1 (s - 112) 4 RI1) by first [lia | (intros r Hr; cbn in Hr; destruct Hr as [<-|[<-|[]]]; cbn; lia)]; exact C112).
  assert (K108 : rdn SEGS M1 (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w))
    by (rewrite (rinv_rdn SEGS _ m M1 (s - 108) 4 RI1) by first [lia | (intros r Hr; cbn in Hr; destruct Hr as [<-|[<-|[]]]; cbn; lia)]; exact C108).
  eapply reach_weaken; [| eapply (ap_iloop rom (Z.to_nat h) fr cs regs1 M1 M1 s kx kf ls wpl h w 0 datas dd pixd linesf datak)].
  - intros fin (fr' & cs' & regs' & M' & -> & FZ' & RI2 & E8 & AG2 & FP).
    exists fr', cs', regs', M'. split; [reflexivity|]. split; [exact FZ'|]. split; [|split; [exact E8|split; [|exact FP]]].
    + eapply rinv_trans; [eapply rinv_incl; [exact RI1|] | eapply rinv_weaken; [exact RI2|]].
      * intros r Hr; cbn in Hr |- *; tauto.
      * intros r Hr; cbn in Hr; destruct Hr as [<-|[<-|[]]].
        -- exists (dd, (4 * wpl * h)%Z). cbn. split; [tauto | lia].
        -- exists ((s - 136)%Z, 24%Z). cbn. split; [tauto | lia].
    + unfold API in *. eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  - rewrite Z2Nat.id by lia. lia.
  - lia.
  - exact FZ.
  - apply rinv_refl.
  - exact Hs.
  - exact As.
  - exact Hw.
  - exact Hww.
  - exact Hwpl.
  - exact Hh2.
  - exact Ads.
  - exact Hds1.
  - exact Hds2.
  - exact Add.
  - exact Hdd1.
  - exact Hdd2.
  - exact Hddf.
  - exact Akx.
  - exact Hkx1.
  - exact Hkx2.
  - exact Akf.
  - exact Hkf1.
  - exact Hkf2.
  - exact Als.
  - exact Hls1.
  - exact Hls2.
  - exact Hpd.
  - intros p Hp. rewrite (rinv_rdn SEGS _ m M1 p 1 RI1) by first [lia | (intros r Hr; cbn in Hr; destruct Hr as [<-|[<-|[]]]; cbn; lia)]. apply RDs. exact Hp.
  - intros p Hp. eapply store_ok_mono; [exact G1 | apply SOKd; exact Hp].
  - eapply store_ok_mono; [exact G1|].
    eapply (store_ok_sub SEGS m (Z_to_bv 64 (s - 160)) _ 160%nat); [ | exact SOKf | | ]; rewrite ?u_Z2bv by lia; lia.
  - apply (ap_rds_keepR [((s - 160)%Z, 16%Z); ((s - 136)%Z, 24%Z)] m M1 kx kf ls (4 * wpl) h linesf datak RI1); try lia; [| exact RDS].
    constructor; [|constructor; [|constructor]]; cbn; split; try lia.
    + apply (ap_apart_sub (s - 160) 160 (s - 160) 16); [exact APf | lia | lia].
    + apply (ap_apart_sub (s - 160) 160 (s - 136) 24); [exact APf | lia | lia].
  - apply (ap_ro_keepR [((s - 160)%Z, 16%Z); ((s - 136)%Z, 24%Z)] m M1 RI1); [| exact RO].
    constructor; [|constructor; [|constructor]]; cbn; lia.
  - exact APd.
  - exact APf.
  - exact C160.
  - exact C152.
  - exact K144.
  - exact C136.
  - exact C128.
  - exact C120.
  - exact K112.
  - exact K108.
  - rewrite (AG1 2 ltac:(notin_list)). exact H2.
  - exact E11.
  - exact E12.
  - exact E13.
  - exact E14.
  - exact E15.
  - rewrite (AG1 18 ltac:(notin_list)). exact H18.
  - rewrite (AG1 22 ltac:(notin_list)). exact H22.
  - rewrite (AG1 23 ltac:(notin_list)). exact H23.
  - rewrite (AG1 24 ltac:(notin_list)). exact H24.
  - rewrite (AG1 25 ltac:(notin_list)). exact H25.
Qed.

End ApLoops.

Section ApW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Definition ap_loops_spec : Prop :=
  forall rom fr cs C Ar A0 A (M : word -> option byte) md regs (s bil pixs w h datas pixd datad : Z) (b : bilw),
  Cok C -> W C A M md -> frm_zero cs ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 160 <= s)%Z -> (s <= c_top C)%Z ->
  bil_obj C Ar A0 M bil pixs (hdv w h 8 0 datas) b -> hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A0 (Z_to_bv 64 pixs) = Some 64%Z -> live A0 (Z_to_bv 64 datas) = Some (4 * (wpl_of w 8 * h))%Z ->
  sub_live A0 A -> live A0 (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datad) = Some (4 * (wpl_of w 8 * h))%Z ->
  (0 <= pixd < 2 ^ 64)%Z -> (0 <= datad < 2 ^ 64)%Z ->
  rdn SEGS M (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 (wpl_of w 8)) ->
  rdn SEGS M (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS M (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 datas ->
  getr regs 18 = Z_to_bv 64 (wpl_of w 8) -> getr regs 19 = Z_to_bv 64 datad ->
  getr regs 22 = Z_to_bv 64 1 -> getr regs 23 = Z_to_bv 64 (bw_kx b) -> getr regs 24 = Z_to_bv 64 (bw_kf b) ->
  getr regs 25 = Z_to_bv 64 (bw_ls b) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3a650) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3aa18) M' rom /\ frm_zero cs' /\
       rinv [(datad, (4 * (wpl_of w 8 * h))%Z); ((s - 160)%Z, 16%Z); ((s - 136)%Z, 24%Z)] M M' /\
       getr regs' 8 = Z_to_bv 64 pixd /\
       regs_agree (fun r => In r (13 :: 14 :: 15 :: API)%list) regs regs' /\ ap_fp fr fr').

End ApW.

Section ApLoopsW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma ap_loops : ap_loops_spec.
Proof.
  unfold ap_loops_spec.
  intros rom fr cs C Ar A0 A M md regs s bil pixs w h datas pixd datad b CK HW FZ As Hs1 Hs2 BO HOK Hw Hh Lpx Lds SUB
    Ld0 Ldc LdA Hpd Hdd C144 C112 C108 H2 H8 H9 H18 H19 H22 H23 H24 H25.
  destruct HOK as (_ & Hw2 & Hh2 & _).
  pose proof (apd_top47 C CK) as T.
  pose proof (ck_top C CK) as T1. pose proof (ck_img C CK) as T2. pose proof (ck_sp0 C CK) as T3. pose proof (ck_sp0hi C CK) as T4.
  cbn [fst snd ll_img LLU16] in T2. unfold LSTK in *.
  assert (WP1 : (1 <= wpl_of w 8)%Z) by (unfold wpl_of; apply Z.div_le_lower_bound; lia).
  assert (WP2 : (wpl_of w 8 <= 20000)%Z) by (unfold wpl_of; apply Z.div_le_upper_bound; lia).
  assert (WW : (w <= 4 * wpl_of w 8)%Z).
  { unfold wpl_of. pose proof (Z.div_mod (w * 8 + 31) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (w * 8 + 31) 32 ltac:(lia)). lia. }
  assert (HN : (1 <= wpl_of w 8 * h)%Z) by nia.
  pose proof BO as BO'.
  destruct BO' as (_ & _ & _ & BKX & BKF & _ & _ & _ & _ & _ & _ & _ & PXs & _ & _ & _ & _ & _ & _ & _ & _ & _ & MEM & Hls & _ & _ & Lls0 & LINES & _).
  destruct BKX as (KX1 & KX2 & KX3 & Lkx0 & _). destruct BKF as (KF1 & KF2 & KF3 & Lkf0 & _).
  destruct PXs as (_ & _ & WF & _). pose proof (wf_data _ WF) as DR. cbn in DR.
  pose proof (SUB _ _ Lds) as LdsA. pose proof (SUB _ _ Lls0) as LlsA.
  destruct (apd_blk C A M md datas (4 * (wpl_of w 8 * h)) CK HW LdsA DR ltac:(lia)) as (S16 & S4 & S47).
  destruct (apd_blk C A M md datad (4 * (wpl_of w 8 * h)) CK HW LdA Hdd ltac:(lia)) as (D16 & D4 & D47).
  destruct (apd_blk C A M md (bw_ls b) 80 CK HW LlsA Hls ltac:(lia)) as (L16 & L4 & L47).
  destruct (blk_range C A M md (Z_to_bv 64 datas) _ CK HW LdsA ltac:(lia)) as [_ SR]. rewrite u_Z2bv in SR by lia.
  destruct (blk_range C A M md (Z_to_bv 64 datad) _ CK HW LdA ltac:(lia)) as [_ DRn]. rewrite u_Z2bv in DRn by lia.
  assert (RDS : ap_rds M (bw_kx b) (bw_kf b) (bw_ls b) (4 * wpl_of w 8) h (bw_linesf b) (bw_datad b))
    by exact (apd_rds C Ar A0 A M md bil pixs (hdv w h 8 0 datas) b CK HW SUB BO Hw Hh).
  assert (APd : ap_apart datad (4 * wpl_of w 8 * h) (bw_kx b) (bw_kf b) (bw_ls b) (4 * wpl_of w 8) h (bw_linesf b) (bw_datad b)).
  { replace (4 * wpl_of w 8 * h)%Z with (4 * (wpl_of w 8 * h))%Z by ring.
    apply (apd_apart_dd C Ar A0 A M md bil pixs (hdv w h 8 0 datas) b datad (4 * (wpl_of w 8 * h)) CK HW SUB BO Hw Hh LdA Hdd ltac:(lia)).
    - exact (apd_fresh A0 (bw_kx b) datad 1024 Ld0 Lkx0).
    - exact (apd_fresh A0 (bw_kf b) datad 1024 Ld0 Lkf0).
    - exact (apd_fresh A0 (bw_ls b) datad 80 Ld0 Lls0).
    - intros k Hk. destruct (MEM k Hk) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ldk & _).
      destruct (LINES k Hk) as (_ & Llf & _). split.
      + exact (apd_fresh A0 (bw_linesf b k) datad _ Ld0 Llf).
      + exact (apd_fresh A0 (bw_datad b k) datad _ Ld0 Ldk). }
  assert (APf : ap_apart (s - 160) 160 (bw_kx b) (bw_kf b) (bw_ls b) (4 * wpl_of w 8) h (bw_linesf b) (bw_datad b))
    by exact (apd_apart_frame C Ar A0 A M md bil pixs (hdv w h 8 0 datas) b s CK HW SUB BO Hw Hh ltac:(unfold LSTK; lia)).
  eapply reach_weaken;
    [| eapply (ap_loops_core rom fr cs regs M s (bw_kx b) (bw_kf b) (bw_ls b) (wpl_of w 8) h w datas datad pixd (bw_linesf b) (bw_datad b))].
  - intros fin (fr' & cs' & regs' & M' & -> & FZ' & RI & E8 & AG & FP).
    exists fr', cs', regs', M'. split; [reflexivity|]. split; [exact FZ'|]. split; [|split; [exact E8 | split; [exact AG | exact FP]]].
    replace (4 * (wpl_of w 8 * h))%Z with (4 * wpl_of w 8 * h)%Z by ring. exact RI.
  - exact FZ.
  - lia.
  - exact As.
  - lia.
  - exact WW.
  - exact WP2.
  - exact Hh.
  - exact Hh2.
  - apply mod16_mod4. exact S16.
  - exact S4.
  - lia.
  - lia.
  - apply mod16_mod4. exact D16.
  - exact D4.
  - lia.
  - lia.
  - apply mod16_mod4. exact KX3.
  - exact KX1.
  - lia.
  - apply mod16_mod4. exact KF3.
  - exact KF1.
  - lia.
  - apply (proj2 (Z.mod_divide _ 8 ltac:(lia))). destruct (proj1 (Z.mod_divide _ 16 ltac:(lia)) L16) as [q Hq]. exists (2 * q)%Z. lia.
  - exact L4.
  - lia.
  - exact Hpd.
  - intros p Hp. apply (apd_rdb C A M md datas (4 * (wpl_of w 8 * h)) p CK HW LdsA DR); lia.
  - intros p Hp. apply (apd_sok_blk C A M md (Z_to_bv 64 datad) (4 * (wpl_of w 8 * h)) p 1 CK HW LdA); rewrite ?u_Z2bv by lia; cbn; lia.
  - apply (W_sok_win C A M md (s - 160) 160 CK HW); unfold LSTK; cbn; lia.
  - exact RDS.
  - exact (apd_ro C A M md CK HW).
  - exact APd.
  - exact APf.
  - exact C144.
  - exact C112.
  - exact C108.
  - exact H2.
  - exact H8.
  - exact H9.
  - exact H18.
  - exact H19.
  - exact H22.
  - exact H23.
  - exact H24.
  - exact H25.
Qed.

End ApLoopsW.

Lemma apw_m16_8 : forall x, (x mod 16 = 0)%Z -> (x mod 8 = 0)%Z.
Proof.
  intros x H. apply (Z.mod_divide x 8 ltac:(lia)). apply (Z.mod_divide x 16 ltac:(lia)) in H.
  destruct H as [k ->]. exists (2 * k)%Z. ring.
Qed.

Lemma apw_ne : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> a <> b -> Z_to_bv 64 a <> Z_to_bv 64 b.
Proof. intros a b Ha Hb NE E. apply NE. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. exact E. Qed.

Lemma apw_fs : forall fr fr', ap_fp fr fr' -> forall r : reg, In (bv_unsigned r) fs_list -> reg_get fr' r = reg_get fr r.
Proof.
  intros fr fr' FP r Hr. unfold fs_list in Hr. cbn [In] in Hr.
  apply FP; intros ->; cbv in Hr; lia.
Qed.

Ltac apw_fr := apply Forall_forall; intros ? Hr; cbn [In] in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; lia|]); destruct Hr.

Section BilApW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Existing Instance exf_fxd | 100.

Definition apw_cells (s : Z) (regs : bvmap 5 word) : list (Z * word) :=
  [((s - 8)%Z, getr regs 1); ((s - 16)%Z, getr regs 8); ((s - 24)%Z, getr regs 9); ((s - 32)%Z, getr regs 18); ((s - 40)%Z, getr regs 19);
   ((s - 48)%Z, getr regs 20); ((s - 56)%Z, getr regs 21); ((s - 64)%Z, getr regs 22); ((s - 72)%Z, getr regs 23); ((s - 80)%Z, getr regs 24);
   ((s - 88)%Z, getr regs 25); ((s - 96)%Z, getr regs 26); ((s - 104)%Z, getr regs 27)].

Lemma apw_cz_rinv : forall (R : list (Z * Z)) (M M' : word -> option byte) (s : Z) regs, rinv R M M' -> (104 <= s <= 2 ^ 63)%Z ->
  Forall (fun r => (s <= fst r \/ fst r + snd r <= s - 104)%Z) R ->
  cellsZ M (apw_cells s regs) -> cellsZ M' (apw_cells s regs).
Proof.
  intros R M M' s regs RI Hs HR CZ.
  assert (K : forall a, (s - 104 <= a)%Z -> (a + 8 <= s)%Z -> rdn SEGS M' (Z_to_bv 64 a) 8 = rdn SEGS M (Z_to_bv 64 a) 8).
  { intros a Ha1 Ha2. eapply rinv_rdn; [exact RI | lia | cbn; lia |].
    intros r Hr. rewrite Forall_forall in HR. specialize (HR r Hr). cbn. lia. }
  cbn [cellsZ apw_cells] in CZ |- *.
  destruct CZ as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & _).
  rewrite !K by lia. exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 (conj X8 (conj X9 (conj X10 (conj X11 (conj X12 (conj X13 I))))))))))))).
Qed.

(* [comment removed for export] *)
Definition ap_saved (regs : bvmap 5 word) : list cell := [(88%Z, 8%nat, u (getr regs 1)); (80%Z, 8%nat, u (getr regs 8)); (72%Z, 8%nat, u (getr regs 9)); (64%Z, 8%nat, u (getr regs 18)); (56%Z, 8%nat, u (getr regs 19)); (48%Z, 8%nat, u (getr regs 20)); (40%Z, 8%nat, u (getr regs 21)); (32%Z, 8%nat, u (getr regs 22)); (24%Z, 8%nat, u (getr regs 23)); (16%Z, 8%nat, u (getr regs 24)); (8%Z, 8%nat, u (getr regs 25))].

Definition AP_WIN : Z := 4096.

(* [comment removed for export] *)
Lemma rinv_scr_keep : forall C A (m M : word -> option byte) md (lo n : Z), Cok C -> W C A m md -> rinv [(lo, n)] m M -> (c_top C - LSTK <= lo)%Z -> (lo + n <= c_top C)%Z ->
  forall (q : word) k (x : word), live A q = Some k -> (u q <= u x < u q + k)%Z -> M x = m x.
Proof.
  intros C A m M md lo n CK HW RI Hlo Hhi q k x L Hx.
  pose proof (ck_top C CK) as T1.
  destruct (blk_range C A m md q k CK HW L ltac:(lia)) as [G1 G2].
  destruct RI as [_ RI]. apply RI. intros r [<-|[]]. unfold inreg. cbn [fst snd]. lia.
Qed.

Lemma apw_livk : forall A (m m' : word -> option byte), LIVK A m m' ->
  forall (q : word) k (x : word), live A q = Some k -> (u q <= u x < u q + k)%Z -> m' x = m x.
Proof.
  intros A m m' LK q k x L Hx.
  pose proof (LK q k (u x - u q)%Z L ltac:(lia)) as E.
  replace (at_ q (u x - u q)%Z) with x in E by (unfold at_; apply bv_eq; pose proof (u64_range x); pose proof (u64_range q); rewrite u_Z2bv by lia; lia).
  exact E.
Qed.

Lemma apw_clr1 : forall C A m md, W C A m md -> forall j, (282176 <= j < 282336)%Z -> m (Z_to_bv 64 j) = None.
Proof.
  intros C A m md HW j Hj.
  apply (exW_clr_None C A m md 282176 282336 282176 282336 HW); [cbv [ll_clr LLU16]; cbn [In]; auto | lia | lia | lia | lia | exact Hj].
Qed.

Lemma apw_clr2 : forall C A m md, W C A m md -> forall j, (286472 <= j < 286480)%Z -> m (Z_to_bv 64 j) = None.
Proof.
  intros C A m md HW j Hj.
  apply (exW_clr_None C A m md 286472 286480 286472 286480 HW); [cbv [ll_clr LLU16]; cbn [In]; auto | lia | lia | lia | lia | exact Hj].
Qed.

(* [comment removed for export] *)
Lemma bilateralApply_W : forall fr cs C Ar A m md regs (s bil pixs w h datas : Z) (b : bilw) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + AP_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 -> getr regs 10 = Z_to_bv 64 bil ->
  bil_obj C Ar A m bil pixs (hdv w h 8 0 datas) b -> hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 8 * h))%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> (RB_pixT (4 * (wpl_of w 8 * h)) <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 0 -> (forall q, live A' q = live A q) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) ->
     aroom A' vm' (kR - RK_pixcopy) (bR - RB_pixT (4 * (wpl_of w 8 * h))) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  (forall fr' cs' A' m' vm' regs' (pixd datad : Z), W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 pixd -> pixr_new C A A' m' pixd datad (set_data (pix_hdr w h 8) datad) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) ->
     aroom A' vm' (kR - RK_pixcopy) (bR - RB_pixT (4 * (wpl_of w 8 * h))) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 238988) m al_rom) md) S.
Proof.
  intros fr cs C Ar A m md regs s bil pixs w h datas b ret S CK HW FZ H2 Hs16 Hlo Hhi H1 Hret H4 H10 BO HOK Hw Hh Lps Lds kR bR Hrm Hrk Hrb K0 K1.
  pose proof (ck_top C CK) as T1. pose proof (ck_img C CK) as T2. pose proof (ck_sp0 C CK) as T3. pose proof (ck_sp0hi C CK) as T4.
  cbn [fst snd ll_img LLU16] in T2. pose proof LSTK_val as LS. unfold AP_WIN in Hlo.
  pose proof (apd_top47 C CK) as T47.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz).
  assert (WP1 : (1 <= wpl_of w 8)%Z) by (unfold wpl_of; apply Z.div_le_lower_bound; lia).
  assert (WP2 : (wpl_of w 8 <= 20000)%Z) by (unfold wpl_of; apply Z.div_le_upper_bound; lia).
  assert (HN : (1 <= wpl_of w 8 * h)%Z) by nia.
  pose proof BO as (CA & Bbil & _ & Bkx & Bkf & _ & _ & _ & _ & _ & _ & _ & PXs & _ & _ & _ & PAC & PAB & _ & _ & _ & _ & _ & Hls & _).
  destruct Bbil as (Gb & TOPb & ALb & Lb & _).
  destruct Bkx as (Gkx & TOPkx & _). destruct Bkf as (Gkf & TOPkf & _).
  destruct PAB as (Hpa & _ & _ & _ & Lpa & _).
  destruct PAC as (PA0 & _). rewrite Z.add_0_r in PA0.
  pose proof PXs as (Hs0 & Hs64 & WFs & _). pose proof (wf_data _ WFs) as DR. cbn in DR.
  destruct (apd_blk C A m md pixs 64 CK HW Lps ltac:(lia) ltac:(lia)) as (Aps & Gps & Tps).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [_ TOPps]. rewrite u_Z2bv in TOPps by lia.
  destruct (apd_blk C A m md (bw_pa b) 32 CK HW Lpa ltac:(lia) ltac:(lia)) as (Apa & Gpa & Tpa).
  destruct (blk_range C A m md (Z_to_bv 64 (bw_pa b)) 32 CK HW Lpa ltac:(lia)) as [_ TOPpa]. rewrite u_Z2bv in TOPpa by lia.
  destruct (blk_range C A m md (Z_to_bv 64 datas) _ CK HW Lds ltac:(lia)) as [_ TOPds]. rewrite u_Z2bv in TOPds by lia.
  pose proof CA as CA'. unfold cellsAt, bc_bl2 in CA'. cbn [app] in CA'. repeat rewrite Forall_cons_iff in CA'.
  destruct CA' as (F0 & _ & F16 & _ & _ & F56 & _ & F72 & F80 & _ & _ & F88 & F96 & _).
  cbn [c_off c_len c_val fst snd] in F0, F16, F56, F72, F80, F88, F96. rewrite Z.add_0_r in F0.
  assert (SOK1 : store_ok SEGS m (Z_to_bv 64 (s - 160)) 160 = true) by (apply (W_sok_win C A m md (s - 160) 160 CK HW); cbn; lia).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) |
    exact (ap_A al_rom (mkFP fr cs) regs m s bil pixs (bw_kx b) (bw_kf b) (bw_pa b) (bw_ls b) ltac:(lia) Gb ltac:(lia) (apw_m16_8 _ ALb)
             Gpa ltac:(lia) (apw_m16_8 _ Apa) ltac:(lia) ltac:(lia) ltac:(lia) Hls F0 F16 F56 F72 F80 F88 F96 PA0 SOK1 H2 H10) |].
  intros fin (r1 & M1 & -> & RI1 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C96 & C104 &
              Q1 & Q2 & Q10 & Q21 & Q22 & Q23 & Q24 & Q25 & AG1).
  assert (LR1 : local_regions C A A s [((s - 160)%Z, 160%Z)]) by (unfold local_regions; constructor; [left; cbn [fst snd]; lia | constructor]).
  destruct (rinv_WP2 C A A m md M1 _ s CK HW (sub_live_refl A) Hhi RI1 LR1) as [HW1 PM1].
  assert (CZ1 : cellsZ M1 (apw_cells s regs)) by exact (conj C8 (conj C16 (conj C24 (conj C32 (conj C40 (conj C48 (conj C56 (conj C64 (conj C72 (conj C80 (conj C88 (conj C96 (conj C104 I))))))))))))).
  assert (PXs1 : PIXat M1 pixs (hdvr 2 w h 8 0 datas)).
  { apply (PIXat_frame m); [exact PXs |]. intros x Hx. apply (apw_livk A m M1 (proj2 PM1) (Z_to_bv 64 pixs) 64 x Lps). rewrite u_Z2bv by lia. lia. }
  assert (Q4 : getr r1 4 = Z_to_bv 64 352880) by (rewrite (AG1 4%bv) by (cbv; intuition discriminate); exact H4).
  assert (RC0 : RB_cmapT 0 = 0%Z) by (unfold RB_cmapT; rewrite Z.abs_0, Z.min_r by lia; ring).
  replace (Z_to_bv 64 104716) with (0x1990c : word) by (apply bv_eq; reflexivity).
  apply (pixCreateTemplate_szTR_W (fx := mkFP fr cs) C A M1 md r1 (s - 160) pixs 2 w h 8 0 datas cmap0 (Z_to_bv 64 239100) S CK HW1 Q2
           ltac:(rewrite Zminus_mod, Hs16; reflexivity) ltac:(unfold PCT_STACK, LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10
           PXs1 HOK Hw Hh Lps ltac:(left; reflexivity) kR bR Hrm Hrk ltac:(rewrite RC0; lia)).
  intros A1 m2 vm1 r2 HWa CSa PMa OUTa Hrm1.
  rewrite RC0, Z.add_0_r in Hrm1.
  pose proof (proj2 PMa) as LKa.
  assert (PMa' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [| exact PMa]; lia]).
  assert (CZ2 : cellsZ m2 (apw_cells s regs)).
  { apply (cellsZ_frm C (s - 160) M1 m2 _ CK (proj1 PMa) ltac:(lia)); [| exact CZ1].
    apply Forall_forall; intros ? Hr; cbn [In apw_cells] in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; lia|]); destruct Hr. }
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 160)) by (csr; reflexivity).
  destruct OUTa as [[Hres0 LIVEQ] | (pixd & cd & data & Hres & PT)].
  - pose proof CZ2 as CZ2'. cbn [cellsZ apw_cells] in CZ2'.
    destruct CZ2' as (D8 & D16 & D24 & D32 & D40 & D48 & D56 & D64 & D72 & D80 & D88 & D96 & D104 & _).
    eapply rz_reach; [exact (w_pure _ _ _ _ HWa) |
      exact (ap_Bn al_rom (mkFP fr cs) r2 m2 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
               (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
               ltac:(lia) ltac:(lia) (apw_clr1 C A1 m2 _ HWa) (apw_clr2 C A1 m2 _ HWa) D8 D16 D24 D32 D40 D48 D56 D64 D72 D80 D88 D96 D104 E2 Hres0) |].
    intros fin (r3 & M3 & -> & EM & V2 & V10 & V11 & V12 & V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & V27 & AG3).
    subst M3.
    replace (Z_to_bv 64 97988) with (0x17ec4 : word) by (apply bv_eq; reflexivity).
    apply (returnErrorPtr_W (fx := mkFP fr cs) C A1 m2 _ r3 s 67429 70815 13 14 ret (Z_to_bv 64 0) S CK HWa V2 Hs16 ltac:(unfold LSF; lia) Hhi
             ltac:(rewrite V1; exact H1) Hret V10 V11 V12 str_ap_msg str_ap_proc).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10.
    apply (K0 fr cs A1 m4 vm1 r5 HW4 FZ).
    + apply cs_kept_intro; csr; reflexivity.
    + eapply POSTM_trans; [exact PMa' |]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ |].
      eapply (POSTM_range C A1 m2 _ m4); [exact CK | exact HWa | exact OUT4 | unfold LSF; lia | lia | lia].
    + exact A10.
    + exact LIVEQ.
    + intros r _; reflexivity.
    + exact Hrm1.
  - pose proof PT as PT0.
    destruct PT as (Gp & TOPp & ALp & Gd & TOPd & ALd & NE & L0p & L0d & L00p & L00d & L1p & L1d & PXd & CMR).
    destruct CMR as [[Ecd LEQ] | (ad & CMOK & _)]; [subst cd | exfalso; destruct CMOK as [D _]; cbn in D; lia].
    pose proof (pix_fresh_sub C A A1 m2 pixd w h 8 data (pixt_new_fresh C A A1 m2 pixd w h 8 data cmap0 PT0)) as SUB.
    assert (PXs2 : PIXat m2 pixs (hdvr 2 w h 8 0 datas)).
    { apply (PIXat_frame M1); [exact PXs1 |]. intros x Hx. apply (apw_livk A M1 m2 LKa (Z_to_bv 64 pixs) 64 x Lps). rewrite u_Z2bv by lia. lia. }
    assert (E21 : getr r2 21 = Z_to_bv 64 pixs) by (csr; reflexivity).
    assert (SOK2 : store_ok SEGS m2 (Z_to_bv 64 (s - 160)) 160 = true) by (apply (W_sok_win C A1 m2 _ (s - 160) 160 CK HWa); cbn; lia).
    eapply rz_reach; [exact (w_pure _ _ _ _ HWa) |
      exact (ap_B al_rom (mkFP fr cs) r2 m2 s pixs pixd datas (wpl_of w 8) data (wpl_of w 8) w h
               ltac:(lia) Hs16 Gps ltac:(lia) (apw_m16_8 _ Aps) Gp ltac:(lia) (apw_m16_8 _ ALp) DR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               (PIX_rd_data SEGS m2 pixs _ PXs2) (PIX_rd_wpl SEGS m2 pixs _ PXs2) (PIX_rd_data SEGS m2 pixd _ PXd) (PIX_rd_wpl SEGS m2 pixd _ PXd)
               (PIX_rd_w SEGS m2 pixs _ PXs2) (PIX_rd_h SEGS m2 pixs _ PXs2) SOK2 E2 Hres E21) |].
    intros fin (r3 & M3 & -> & RI3 & B108 & B112 & B144 & V2 & V8 & V9 & V18 & V19 & V10 & AG3).
    assert (LR3 : local_regions C A1 A1 s [((s - 144)%Z, 8%Z); ((s - 112)%Z, 8%Z)]).
    { unfold local_regions. constructor; [left; cbn [fst snd]; lia | constructor; [left; cbn [fst snd]; lia | constructor]]. }
    destruct (rinv_WP2 C A1 A1 m2 _ M3 _ s CK HWa (sub_live_refl A1) Hhi RI3 LR3) as [HW3 PM3].
    assert (LK3 : LIVK A m M3).
    { eapply LIVK_trans; [exact (proj2 PM1) |]. eapply LIVK_trans; [exact LKa |].
      exact (proj2 (POSTM_sub C A A1 s m2 M3 SUB PM3)). }
    assert (BO3 : bil_obj C Ar A M3 bil pixs (hdv w h 8 0 datas) b)
      by exact (bil_obj_keep C Ar A A m M3 md bil pixs _ b CK HW BO Lps (apw_livk A m M3 LK3) (sub_live_refl A)).
    assert (V22 : getr r3 22 = Z_to_bv 64 1) by (csr; reflexivity).
    assert (V23 : getr r3 23 = Z_to_bv 64 (bw_kx b)) by (csr; reflexivity).
    assert (V24 : getr r3 24 = Z_to_bv 64 (bw_kf b)) by (csr; reflexivity).
    assert (V25 : getr r3 25 = Z_to_bv 64 (bw_ls b)) by (csr; reflexivity).
    eapply rz_reach; [exact (w_pure _ _ _ _ HW3) |
      exact (ap_loops al_rom fr cs C Ar A A1 M3 _ r3 s bil pixs w h datas pixd data b CK HW3 FZ Hs16 ltac:(lia) Hhi BO3 HOK Hw Hh Lps Lds SUB
               L0d L00d L1d ltac:(lia) ltac:(lia) B144 B112 B108 V2 V8 V9 V18 V19 V22 V23 V24 V25) |].
    intros fin (fr4 & cs4 & r4 & M4 & -> & FZ4 & RI4 & W8 & AG4 & FP4).
    assert (LR4 : local_regions C A1 A s [(data, (4 * (wpl_of w 8 * h))%Z); ((s - 160)%Z, 16%Z); ((s - 136)%Z, 24%Z)]).
    { unfold local_regions. constructor; [| constructor; [left; cbn [fst snd]; lia | constructor; [left; cbn [fst snd]; lia | constructor]]].
      right. exists (Z_to_bv 64 data), (4 * (wpl_of w 8 * h))%Z. rewrite u_Z2bv by lia. cbn [fst snd].
      split; [exact L1d | split; [exact L0d | split; [exact L00d | lia]]]. }
    destruct (rinv_WP2 C A A1 M3 _ M4 _ s CK HW3 SUB Hhi RI4 LR4) as [HW4 PM4].
    assert (CZ3 : cellsZ M3 (apw_cells s regs)) by (apply (apw_cz_rinv _ m2 M3 s regs RI3); [lia | apw_fr | exact CZ2]).
    assert (CZ4 : cellsZ M4 (apw_cells s regs)) by (apply (apw_cz_rinv _ M3 M4 s regs RI4); [lia | apw_fr | exact CZ3]).
    cbn [cellsZ apw_cells] in CZ4.
    destruct CZ4 as (D8 & D16 & D24 & D32 & D40 & D48 & D56 & D64 & D72 & D80 & D88 & D96 & D104 & _).
    assert (E2' : getr r4 2 = Z_to_bv 64 (s - 160)) by (rewrite (AG4 2%bv) by (cbv; intuition discriminate); exact V2).
    eapply rz_reach; [exact (w_pure _ _ _ _ HW4) |
      exact (ap_C al_rom (mkFP fr4 cs4) r4 M4 s ret (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
               (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
               ltac:(lia) Hret H1 D8 D16 D24 D32 D40 D48 D56 D64 D72 D80 D88 D96 D104 E2') |].
    intros fin (r6 & M6 & -> & EM6 & U2 & U10 & U8 & U9 & U18 & U19 & U20 & U21 & U22 & U23 & U24 & U25 & U26 & U27 & AG6).
    subst M6.
    assert (PXd4 : PIXat M4 pixd (hdv w h 8 0 data)).
    { apply (PIXat_frame M3).
      - apply (PIXat_frame m2); [exact PXd |]. intros x Hx.
        apply (apw_livk A1 m2 M3 (proj2 PM3) (Z_to_bv 64 pixd) 64 x L1p). rewrite u_Z2bv by lia. lia.
      - intros x Hx. destruct RI4 as [_ RI4']. apply RI4'.
        destruct (apd_sep C A1 M3 _ pixd 64 data (4 * (wpl_of w 8 * h)) CK HW3 L1p L1d (apw_ne pixd data ltac:(lia) ltac:(lia) NE)
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [D|D];
          intros r Hr; cbn [In] in Hr; repeat (destruct Hr as [<-|Hr]; [unfold inreg; cbn [fst snd]; lia|]); destruct Hr. }
    apply (K1 fr4 cs4 A1 M4 vm1 r6 pixd data HW4 FZ4).
    + apply cs_kept_intro; try (rewrite U2, H2; reflexivity); try assumption.
      all: rewrite (AG6 _) by (cbv; intuition discriminate); rewrite (AG4 _) by (cbv; intuition discriminate);
           rewrite (AG3 _) by (cbv; intuition discriminate); csr; reflexivity.
    + eapply POSTM_trans; [exact PMa' |]. eapply POSTM_trans; [exact (POSTM_sub C A A1 s m2 M3 SUB PM3) | exact PM4].
    + rewrite U10. exact W8.
    + exact (conj Gp (conj TOPp (conj ALp (conj Gd (conj TOPd (conj ALd (conj NE (conj L0p (conj L0d (conj L00p (conj L00d
               (conj L1p (conj L1d (conj LEQ (conj PXd4 eq_refl))))))))))))))).
    + exact (apw_fs fr fr4 FP4).
    + exact Hrm1.
Qed.

End BilApW.
