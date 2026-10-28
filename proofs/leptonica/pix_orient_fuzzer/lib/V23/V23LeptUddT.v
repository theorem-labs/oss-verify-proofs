(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptSlots LeptRecs LeptSel.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL LeptCmapArr.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptPixHdr O23LeptCmapValid O23LeptCmap2 O23LeptPixCopyT O23LeptPixCreateT2 O23LeptCloseSpec O23LeptCascW O23LeptTextSelW O23LeptMorphSeqSpec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptErr V23LeptPixHdr V23LeptCmapValid V23LeptCmap2 V23LeptPixDestroy V23LeptPixDestroyK V23LeptPixMisc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptPixCopyT V23LeptPixCreateT2 V23LeptSelGP V23LeptMbc V23LeptCloseSpec V23LeptCloseIface V23LeptMorphSeqSpec V23LeptSelDW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptUddSegs V23LeptUddLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptUddLib O23LeptUddSegs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptSelGP.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition UDD_STACK : Z := 256 + MSEQ_STACK.

Section UddT.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Instance udt_fxd : FPState | 100 := mkFP bvmap_empty (Z_to_bv 32 0).
Ltac rzs HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
Ltac mod16 Hs16 := rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity.
Ltac in_app := solve [repeat (first [assumption | apply in_or_app; first [left; assumption | right]])].
Ltac zl := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Ltac pcto RUN E :=
  match type of RUN with msteps _ (mkst _ ?pc _ _) _ =>
    lazymatch goal with |- realizes _ (mkCfg (mkst _ ?g _ _) _) _ => replace g with pc by (rewrite E; apply bv_eq; reflexivity) end end.

Lemma udd_tail_W : forall fr7 cs7 C A A7 (m m7 : word -> option byte) md vm7 regs r7
    (s pconf pix0 w h cd data sel1 sel2 sel3 sel4 : Z) (cvx : cmapv) (sv1 sv2 sv3 sv4 : selv) (b0 b1 : list byte)
    (ret f0 f1 : word) (S : TSet) (kR bR : Z),
  Cok C -> W C A m md -> W C A7 m7 (with_vmmaps vm7 md) -> frm_zero cs7 ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + UDD_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  (s <= pconf)%Z -> (pconf + 4 <= c_top C)%Z ->
  getr r7 2 = Z_to_bv 64 (s - 256) -> getr r7 4 = Z_to_bv 64 0x1381d0 -> getr r7 8 = Z_to_bv 64 pconf -> getr r7 9 = Z_to_bv 64 0 ->
  getr r7 18 = Z_to_bv 64 70 -> getr r7 3 = getr regs 3 -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  UDC m7 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) f0 f1 ->
  rdn SEGS m7 (Z_to_bv 64 (s - 124)) 4 = Some b0 -> length b0 = 4%nat ->
  rdn SEGS m7 (Z_to_bv 64 (s - 128)) 4 = Some b1 -> length b1 = 4%nat ->
  rdn SEGS m7 (Z_to_bv 64 (s - 136)) 8 = Some (Z_to_le_bytes 8 pix0) ->
  rdn SEGS m7 (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m7 (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 sel1) ->
  rdn SEGS m7 (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 sel2) ->
  rdn SEGS m7 (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 sel3) ->
  rdn SEGS m7 (Z_to_bv 64 (s - 200)) 8 = Some (Z_to_le_bytes 8 sel4) ->
  O23LeptUddLib.PIXC C A7 m7 pix0 w h cd data cvx -> (1 <= w)%Z -> (1 <= h)%Z ->
  sel_at (alloc_top (c_vm C)) A7 m7 sel1 sv1 -> v_name sv1 = 0%Z -> v_sy sv1 = 5%Z -> sel_off (c_A0 C) sel1 sv1 ->
  sel_at (alloc_top (c_vm C)) A7 m7 sel2 sv2 -> v_name sv2 = 0%Z -> v_sy sv2 = 5%Z -> sel_off (c_A0 C) sel2 sv2 ->
  sel_at (alloc_top (c_vm C)) A7 m7 sel3 sv3 -> v_name sv3 = 0%Z -> v_sy sv3 = 5%Z -> sel_off (c_A0 C) sel3 sv3 ->
  sel_at (alloc_top (c_vm C)) A7 m7 sel4 sv4 -> v_name sv4 = 0%Z -> v_sy sv4 = 5%Z -> sel_off (c_A0 C) sel4 sv4 ->
  O23LeptUddLib.disj (O23LeptUddLib.sel_l sel1 sv1) (O23LeptUddLib.pix_l pix0 data cd (c_arr cvx)) -> O23LeptUddLib.disj (O23LeptUddLib.sel_l sel2 sv2) (O23LeptUddLib.pix_l pix0 data cd (c_arr cvx)) ->
  O23LeptUddLib.disj (O23LeptUddLib.sel_l sel3 sv3) (O23LeptUddLib.pix_l pix0 data cd (c_arr cvx)) -> O23LeptUddLib.disj (O23LeptUddLib.sel_l sel4 sv4) (O23LeptUddLib.pix_l pix0 data cd (c_arr cvx)) ->
  O23LeptUddLib.disj (O23LeptUddLib.sel_l sel2 sv2) (O23LeptUddLib.sel_l sel1 sv1) -> O23LeptUddLib.disj (O23LeptUddLib.sel_l sel3 sv3) (O23LeptUddLib.sel_l sel1 sv1) -> O23LeptUddLib.disj (O23LeptUddLib.sel_l sel4 sv4) (O23LeptUddLib.sel_l sel1 sv1) ->
  O23LeptUddLib.disj (O23LeptUddLib.sel_l sel3 sv3) (O23LeptUddLib.sel_l sel2 sv2) -> O23LeptUddLib.disj (O23LeptUddLib.sel_l sel4 sv4) (O23LeptUddLib.sel_l sel2 sv2) -> O23LeptUddLib.disj (O23LeptUddLib.sel_l sel4 sv4) (O23LeptUddLib.sel_l sel3 sv3) ->
  O23LeptUddLib.only A A7 (O23LeptUddLib.pix_l pix0 data cd (c_arr cvx) ++ O23LeptUddLib.sel_l sel1 sv1 ++ O23LeptUddLib.sel_l sel2 sv2 ++ O23LeptUddLib.sel_l sel3 sv3 ++ O23LeptUddLib.sel_l sel4 sv4) ->
  O23LeptUddLib.offs A (O23LeptUddLib.pix_l pix0 data cd (c_arr cvx) ++ O23LeptUddLib.sel_l sel1 sv1 ++ O23LeptUddLib.sel_l sel2 sv2 ++ O23LeptUddLib.sel_l sel3 sv3 ++ O23LeptUddLib.sel_l sel4 sv4) ->
  POSTM C A s (O23LeptSelGP.wr4 m pconf 0) m7 -> aroom A7 vm7 kR bR ->
  (forall fr' cs' A' m' vm' regs' (y : Z), W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' ->
     POSTM C A s (O23LeptSelGP.wr4 m pconf y) m' -> (forall q, live A' q = live A q) -> aroom A' vm' kR bR ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr7 cs7) r7 (0xafcf4 : word) m7 al_rom) (with_vmmaps vm7 md)) S.
Proof.
  intros fr7 cs7 C A A7 m m7 md vm7 regs r7 s pconf pix0 w h cd data sel1 sel2 sel3 sel4 cvx sv1 sv2 sv3 sv4 b0 b1 ret f0 f1 S kR bR
    CK HW HW7 FZ7 Hs16 Hlo Hhi Hret H2 Hpc1 Hpc2 R2 R4 R8 R9 R18 R3 H4 UD Rb0 Lb0 Rb1 Lb1 Rp0 Rz Rs1 Rs2 Rs3 Rs4 PC Hw Hh
    SA1 N1 Y1 O1 SA2 N2 Y2 O2 SA3 N3 Y3 O3 SA4 N4 Y4 O4 D1p D2p D3p D4p D21 D31 D41 D32 D42 D43 ONLY OFFS PM7 AR7 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins.
  pose proof (u64_range (c_sp0 C)) as SP.
  assert (SB : (c_top C - LSTK + 2048 <= s - 256)%Z)
    by (cbv [UDD_STACK MSEQ_STACK V23LeptCloseSpec.CSC_STACK O23LeptCloseSpec.CSC_STACK] in Hlo; lia).
  assert (S8 : (s mod 8 = 0)%Z).
  { pose proof (Z.div_mod s 16 ltac:(lia)) as D. rewrite Hs16, Z.add_0_r in D. rewrite D.
    replace (16 * (s / 16))%Z with ((2 * (s / 16)) * 8)%Z by lia. apply Z_mod_mult. }
  assert (AL8 : forall k, (k mod 8 = 0)%Z -> ((s - k) mod 8 = 0)%Z).
  { intros k Hk. rewrite Zminus_mod, S8, Hk. reflexivity. }
  assert (M256 : ((s - 256) mod 16 = 0)%Z) by (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity).
  pose proof (aroom_nonneg A7 vm7 kR bR AR7) as [Nk Nb].
  set (PL := O23LeptUddLib.pix_l pix0 data cd (c_arr cvx)) in *.
  set (S1 := O23LeptUddLib.sel_l sel1 sv1) in *.
  set (S2 := O23LeptUddLib.sel_l sel2 sv2) in *.
  set (S3 := O23LeptUddLib.sel_l sel3 sv3) in *.
  set (S4 := O23LeptUddLib.sel_l sel4 sv4) in *.
  assert (SOK : store_ok SEGS m7 (Z_to_bv 64 pconf) 4 = true)
    by (apply (W_sok_win C A7 m7 (with_vmmaps vm7 md) pconf 4 CK HW7); zl).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW7) | apply (ud_F al_rom fr7 cs7 r7 m7 s pconf b0 b1); first [lia | assumption] |].
  intros fin (fr1 & cs1 & r1 & M1 & -> & FZ1 & HM1 & R1a & R1b & AG1).
  assert (EX : exists y0, POSTM C A s (O23LeptSelGP.wr4 m pconf y0) M1 /\ W C A7 M1 (with_vmmaps vm7 md) /\ LIVK A7 m7 M1 /\
                 (forall x : word, (u x < pconf)%Z -> M1 x = m7 x)).
  { destruct HM1 as [-> | (y & Hy & ->)].
    - exists 0%Z. split; [exact PM7 |]. split; [exact HW7 |]. split; [apply LIVK_refl | reflexivity].
    - assert (WL : W C A7 (wbytes m7 (Z_to_bv 64 pconf) (Z_to_le_bytes 4 y)) (with_vmmaps vm7 md) /\
                   POSTM C A7 (pconf + 4) m7 (wbytes m7 (Z_to_bv 64 pconf) (Z_to_le_bytes 4 y))).
      { apply (WP_win C A7 A7 m7 m7 (with_vmmaps vm7 md) (Z_to_bv 64 pconf) (Z_to_le_bytes 4 y) (pconf + 4) CK
                (conj HW7 (POSTM_refl C A7 (pconf + 4) m7)) (sub_live_refl A7));
          rewrite ?length_Z_to_le_bytes, ?u_Z2bv by lia; zl. }
      destruct WL as [WW [_ LL]].
      exists y. split; [| split; [exact WW | split; [exact LL |]]].
      + apply (POSTM_src_pw C A s (wbytes (O23LeptSelGP.wr4 m pconf 0) (Z_to_bv 64 pconf) (Z_to_le_bytes 4 y))).
        * intros x. unfold O23LeptSelGP.wr4. rewrite (w2b_Z 4 y) by lia.
          rewrite wbytes_shadow; [reflexivity | rewrite length_N_to_le_bytes, length_Z_to_le_bytes; reflexivity |].
          rewrite length_Z_to_le_bytes, u_Z2bv by lia. zl.
        * apply POSTM_both. exact PM7.
      + intros x Hx. apply wbytes_below; [rewrite length_Z_to_le_bytes, u_Z2bv by lia; zl | rewrite u_Z2bv by lia; lia]. }
  destruct EX as (y0 & PMa & W1 & LV1 & BEL1).
  assert (FM1 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z ->
                rdn SEGS M1 (Z_to_bv 64 b) n = rdn SEGS m7 (Z_to_bv 64 b) n).
  { intros b n Hb Hn. apply rdn_ext; [rewrite u_Z2bv by lia; lia |].
    intros x Hx. rewrite u_Z2bv in Hx by lia. apply BEL1. lia. }
  assert (SAM : forall sel sv, sel_at (alloc_top (c_vm C)) A7 m7 sel sv -> v_sy sv = 5%Z -> sel_at (alloc_top (c_vm C)) A7 M1 sel sv).
  { intros sel sv SA Y. apply (O23LeptUddLib.sel_at_dst C A7 A7 m7 M1 sel sv [] SA Y (O23LeptUddLib.only_refl A7 []));
      [intros q _ Hq; exact Hq | exact LV1]. }
  pose proof (O23LeptUddLib.PIXC_livk C A7 A7 m7 M1 pix0 w h cd data cvx PC (sub_live_refl A7) LV1) as PC1.
  pose proof PC1 as (PX1 & LP1 & LP01 & LD1 & LD01 & NDP & _).
  assert (RPOS : (0 < 4 * (wpl_of w 1 * h))%Z)
    by (pose proof (O23LeptUddLib.wpl_pos w Hw); apply Z.mul_pos_pos; [lia | apply Z.mul_pos_pos; lia]).
  assert (DNZ : data <> 0%Z).
  { intro E. destruct (blk_range C A7 M1 (with_vmmaps vm7 md) (Z_to_bv 64 data) _ CK W1 LD1 RPOS) as [B1 _].
    rewrite E, u_Z2bv in B1 by lia. lia. }
  apply (pixDestroy_keep_W (fx := mkFP fr1 cs1) C A7 M1 (with_vmmaps vm7 md) r1 (s - 256) (s - 136) pix0 cd (4 * c_nalloc cvx)
           (4 * (wpl_of w 1 * h)) (hdv w h 1 cd data) cvx (getr r1 1) S CK W1 ltac:(csr; reflexivity) M256 ltac:(unfold ALLOC_STACK; lia)
           ltac:(lia) ltac:(lia) eq_refl ltac:(rewrite R1a; apply ret_ok_even; reflexivity) ltac:(csr; reflexivity) (AL8 136%Z eq_refl) R1b
           ltac:(rewrite FM1 by zl; exact Rp0) PX1 eq_refl eq_refl eq_refl LP1 LP01 LD1 LD01 RPOS NDP
           (O23LeptUddLib.PIXC_dprem C A7 M1 pix0 w h cd data cvx PC1)).
  intros A8 m8 vm8 r8 W8 CS8 PP8 PM8 R08 BEL8 RT8.
  rewrite with_vmmaps_twice in W8 |- *. rewrite with_vmmaps_vmmaps in RT8.
  destruct (O23LeptUddLib.pixd_post_l A7 A8 pix0 data cd (c_arr cvx) DNZ PP8) as [ON8 OF8].
  assert (ONLY8 : O23LeptUddLib.only A A8 (PL ++ S1 ++ S2 ++ S3 ++ S4)).
  { apply (O23LeptUddLib.only_trans_l A A7 A8 _ ONLY). apply (O23LeptUddLib.only_sub A7 A8 PL); [exact ON8 | intros q Hq; in_app]. }
  pose proof (O23LeptUddLib.sub_of_only A A8 _ ONLY8 OFFS) as SUB8.
  pose proof (POSTM_trans _ _ _ _ _ _ PMa (POSTM_sub C A A8 s M1 m8 SUB8 (POSTM_mono C A8 (s - 136 + 8) s M1 m8 ltac:(lia) PM8))) as PMc8.
  assert (ST8 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= 2 ^ 64)%Z -> (b + Z.of_nat n <= s - 136 \/ s - 136 + 8 <= b)%Z ->
                rdn SEGS m8 (Z_to_bv 64 b) n = rdn SEGS M1 (Z_to_bv 64 b) n)
    by (intros b n X1 X2 X3; exact (dst_rd C A8 M1 m8 (s - 256) (s - 136) b n CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM8 BEL8 X1 X2 X3)).
  pose proof (RT8 kR bR AR7 ltac:(lia) ltac:(lia)) as AR8. rewrite !Z.sub_0_r in AR8.
  assert (SA8 : forall sel sv, sel_at (alloc_top (c_vm C)) A7 m7 sel sv -> v_sy sv = 5%Z -> O23LeptUddLib.disj (O23LeptUddLib.sel_l sel sv) PL ->
                sel_at (alloc_top (c_vm C)) A8 m8 sel sv)
    by (intros sel sv SA Y DJ; exact (O23LeptUddLib.sel_at_dst C A7 A8 M1 m8 sel sv PL (SAM sel sv SA Y) Y ON8 DJ (proj2 PM8))).
  pose proof (SA8 _ _ SA1 Y1 D1p) as SA1a. pose proof (SA8 _ _ SA2 Y2 D2p) as SA2a.
  pose proof (SA8 _ _ SA3 Y3 D3p) as SA3a. pose proof (SA8 _ _ SA4 Y4 D4p) as SA4a.
  destruct (ud_T1 al_rom (mkFP fr1 cs1) r8 m8 s ltac:(lia) ltac:(lia) ltac:(csr; reflexivity)) as (r9 & RUN9 & Q9a & Q9b & AG9).
  pcto RUN9 R1a. rzs W8 RUN9.
  apply (pixDestroy_null_W (fx := mkFP fr1 cs1) C A8 m8 (with_vmmaps vm8 md) r9 (s - 256) (s - 168) None (getr r9 1) S CK W8
           ltac:(csr; reflexivity) M256 ltac:(lia) ltac:(lia) eq_refl ltac:(rewrite Q9a; apply ret_ok_even; reflexivity) Q9b
           ltac:(cbn [slotok]; split; lia) (AL8 168%Z eq_refl) ltac:(rewrite ST8, FM1 by zl; exact Rz)).
  intros m9 r10 W9 CS10 PM9 FR9.
  pose proof (POSTM_trans _ _ _ _ _ _ PMc8 (POSTM_sub C A A8 s m8 m9 SUB8 (POSTM_mono C A8 (s - 256) s m8 m9 ltac:(lia) PM9))) as PMc9.
  assert (ST9 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z ->
                rdn SEGS m9 (Z_to_bv 64 b) n = rdn SEGS m8 (Z_to_bv 64 b) n).
  { intros b n X1 X2. apply rdn_ext; [rewrite u_Z2bv by lia; lia |].
    intros x Hx. rewrite u_Z2bv in Hx by lia. apply FR9. lia. }
  assert (SA9 : forall sel sv, sel_at (alloc_top (c_vm C)) A8 m8 sel sv -> v_sy sv = 5%Z -> sel_at (alloc_top (c_vm C)) A8 m9 sel sv)
    by (intros sel sv SA Y; exact (O23LeptUddLib.sel_at_dst C A8 A8 m8 m9 sel sv [] SA Y (O23LeptUddLib.only_refl A8 [])
                                     ltac:(intros q _ Hq; exact Hq) (proj2 PM9))).
  pose proof (SA9 _ _ SA1a Y1) as SA1b. pose proof (SA9 _ _ SA2a Y2) as SA2b.
  pose proof (SA9 _ _ SA3a Y3) as SA3b. pose proof (SA9 _ _ SA4a Y4) as SA4b.
  destruct (ud_T2 al_rom (mkFP fr1 cs1) r10 m9 s ltac:(lia) ltac:(lia) ltac:(csr; reflexivity)) as (r11 & RUN11 & Q11a & Q11b & AG11).
  pcto RUN11 Q9a. rzs W9 RUN11.
  apply (selDestroy_W (fx := mkFP fr1 cs1) C A8 m9 (with_vmmaps vm8 md) r11 (s - 256)%Z (s - 176)%Z sel1 sv1 (getr r11 1) S CK W9
           ltac:(csr; reflexivity) M256 ltac:(unfold O23LeptCloseIface.SELD_STACK, ALLOC_STACK; lia) ltac:(lia) ltac:(lia) (AL8 176%Z eq_refl)
           eq_refl ltac:(rewrite Q11a; apply ret_ok_even; reflexivity) ltac:(csr; reflexivity) Q11b
           ltac:(rewrite ST9, ST8, FM1 by zl; exact Rs1) SA1b N1 ltac:(right; right; left; exact Y1) O1).
  intros A10 m10 vm10 r12 W10 CS12 LD10 LE10 PM10 R010 BEL10 RT10.
  rewrite with_vmmaps_twice in W10 |- *. rewrite with_vmmaps_vmmaps in RT10.
  pose proof (O23LeptUddLib.only_of_sel A8 A10 sel1 sv1 Y1 LE10) as ON10.
  pose proof (O23LeptUddLib.offs_of_sel A10 sel1 sv1 Y1 LD10) as OS10.
  assert (ONLY10 : O23LeptUddLib.only A A10 (PL ++ S1 ++ S2 ++ S3 ++ S4)).
  { apply (O23LeptUddLib.only_trans_l A A8 A10 _ ONLY8). apply (O23LeptUddLib.only_sub A8 A10 S1); [exact ON10 | intros q Hq; in_app]. }
  pose proof (O23LeptUddLib.sub_of_only A A10 _ ONLY10 OFFS) as SUB10.
  pose proof (POSTM_trans _ _ _ _ _ _ PMc9 (POSTM_sub C A A10 s m9 m10 SUB10 (POSTM_mono C A10 (s - 176 + 8) s m9 m10 ltac:(lia) PM10))) as PMc10.
  assert (ST10 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= 2 ^ 64)%Z -> (b + Z.of_nat n <= s - 176 \/ s - 176 + 8 <= b)%Z ->
                rdn SEGS m10 (Z_to_bv 64 b) n = rdn SEGS m9 (Z_to_bv 64 b) n)
    by (intros b n X1 X2 X3; exact (dst_rd C A10 m9 m10 (s - 256) (s - 176) b n CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM10 BEL10 X1 X2 X3)).
  pose proof (RT10 kR bR AR8 ltac:(lia) ltac:(lia)) as AR10. rewrite !Z.sub_0_r in AR10.
  pose proof (O23LeptUddLib.offs_only A8 A10 PL S1 OF8 ON10 OS10) as OF10.
  assert (SA10 : forall sel sv, sel_at (alloc_top (c_vm C)) A8 m9 sel sv -> v_sy sv = 5%Z -> O23LeptUddLib.disj (O23LeptUddLib.sel_l sel sv) S1 ->
                sel_at (alloc_top (c_vm C)) A10 m10 sel sv)
    by (intros sel sv SA Y DJ; exact (O23LeptUddLib.sel_at_dst C A8 A10 m9 m10 sel sv S1 SA Y ON10 DJ (proj2 PM10))).
  pose proof (SA10 _ _ SA2b Y2 D21) as SA2c. pose proof (SA10 _ _ SA3b Y3 D31) as SA3c. pose proof (SA10 _ _ SA4b Y4 D41) as SA4c.
  destruct (ud_T3 al_rom (mkFP fr1 cs1) r12 m10 s ltac:(lia) ltac:(lia) ltac:(csr; reflexivity)) as (r13 & RUN13 & Q13a & Q13b & AG13).
  pcto RUN13 Q11a. rzs W10 RUN13.
  apply (selDestroy_W (fx := mkFP fr1 cs1) C A10 m10 (with_vmmaps vm10 md) r13 (s - 256)%Z (s - 184)%Z sel2 sv2 (getr r13 1) S CK W10
           ltac:(csr; reflexivity) M256 ltac:(unfold O23LeptCloseIface.SELD_STACK, ALLOC_STACK; lia) ltac:(lia) ltac:(lia) (AL8 184%Z eq_refl)
           eq_refl ltac:(rewrite Q13a; apply ret_ok_even; reflexivity) ltac:(csr; reflexivity) Q13b
           ltac:(rewrite ST10, ST9, ST8, FM1 by zl; exact Rs2) SA2c N2 ltac:(right; right; left; exact Y2) O2).
  intros A11 m11 vm11 r14 W11 CS14 LD11 LE11 PM11 R011 BEL11 RT11.
  rewrite with_vmmaps_twice in W11 |- *. rewrite with_vmmaps_vmmaps in RT11.
  pose proof (O23LeptUddLib.only_of_sel A10 A11 sel2 sv2 Y2 LE11) as ON11.
  pose proof (O23LeptUddLib.offs_of_sel A11 sel2 sv2 Y2 LD11) as OS11.
  assert (ONLY11 : O23LeptUddLib.only A A11 (PL ++ S1 ++ S2 ++ S3 ++ S4)).
  { apply (O23LeptUddLib.only_trans_l A A10 A11 _ ONLY10). apply (O23LeptUddLib.only_sub A10 A11 S2); [exact ON11 | intros q Hq; in_app]. }
  pose proof (O23LeptUddLib.sub_of_only A A11 _ ONLY11 OFFS) as SUB11.
  pose proof (POSTM_trans _ _ _ _ _ _ PMc10 (POSTM_sub C A A11 s m10 m11 SUB11 (POSTM_mono C A11 (s - 184 + 8) s m10 m11 ltac:(lia) PM11))) as PMc11.
  assert (ST11 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= 2 ^ 64)%Z -> (b + Z.of_nat n <= s - 184 \/ s - 184 + 8 <= b)%Z ->
                rdn SEGS m11 (Z_to_bv 64 b) n = rdn SEGS m10 (Z_to_bv 64 b) n)
    by (intros b n X1 X2 X3; exact (dst_rd C A11 m10 m11 (s - 256) (s - 184) b n CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM11 BEL11 X1 X2 X3)).
  pose proof (RT11 kR bR AR10 ltac:(lia) ltac:(lia)) as AR11. rewrite !Z.sub_0_r in AR11.
  pose proof (O23LeptUddLib.offs_only A10 A11 PL S2 OF10 ON11 OS11) as OF11.
  pose proof (O23LeptUddLib.offs_only A10 A11 S1 S2 OS10 ON11 OS11) as OS10b.
  assert (SA11 : forall sel sv, sel_at (alloc_top (c_vm C)) A10 m10 sel sv -> v_sy sv = 5%Z -> O23LeptUddLib.disj (O23LeptUddLib.sel_l sel sv) S2 ->
                sel_at (alloc_top (c_vm C)) A11 m11 sel sv)
    by (intros sel sv SA Y DJ; exact (O23LeptUddLib.sel_at_dst C A10 A11 m10 m11 sel sv S2 SA Y ON11 DJ (proj2 PM11))).
  pose proof (SA11 _ _ SA3c Y3 D32) as SA3d. pose proof (SA11 _ _ SA4c Y4 D42) as SA4d.
  destruct (ud_T4 al_rom (mkFP fr1 cs1) r14 m11 s ltac:(lia) ltac:(lia) ltac:(csr; reflexivity)) as (r15 & RUN15 & Q15a & Q15b & AG15).
  pcto RUN15 Q13a. rzs W11 RUN15.
  apply (selDestroy_W (fx := mkFP fr1 cs1) C A11 m11 (with_vmmaps vm11 md) r15 (s - 256)%Z (s - 192)%Z sel3 sv3 (getr r15 1) S CK W11
           ltac:(csr; reflexivity) M256 ltac:(unfold O23LeptCloseIface.SELD_STACK, ALLOC_STACK; lia) ltac:(lia) ltac:(lia) (AL8 192%Z eq_refl)
           eq_refl ltac:(rewrite Q15a; apply ret_ok_even; reflexivity) ltac:(csr; reflexivity) Q15b
           ltac:(rewrite ST11, ST10, ST9, ST8, FM1 by zl; exact Rs3) SA3d N3 ltac:(right; right; left; exact Y3) O3).
  intros A12 m12 vm12 r16 W12 CS16 LD12 LE12 PM12 R012 BEL12 RT12.
  rewrite with_vmmaps_twice in W12 |- *. rewrite with_vmmaps_vmmaps in RT12.
  pose proof (O23LeptUddLib.only_of_sel A11 A12 sel3 sv3 Y3 LE12) as ON12.
  pose proof (O23LeptUddLib.offs_of_sel A12 sel3 sv3 Y3 LD12) as OS12.
  assert (ONLY12 : O23LeptUddLib.only A A12 (PL ++ S1 ++ S2 ++ S3 ++ S4)).
  { apply (O23LeptUddLib.only_trans_l A A11 A12 _ ONLY11). apply (O23LeptUddLib.only_sub A11 A12 S3); [exact ON12 | intros q Hq; in_app]. }
  pose proof (O23LeptUddLib.sub_of_only A A12 _ ONLY12 OFFS) as SUB12.
  pose proof (POSTM_trans _ _ _ _ _ _ PMc11 (POSTM_sub C A A12 s m11 m12 SUB12 (POSTM_mono C A12 (s - 192 + 8) s m11 m12 ltac:(lia) PM12))) as PMc12.
  assert (ST12 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= 2 ^ 64)%Z -> (b + Z.of_nat n <= s - 192 \/ s - 192 + 8 <= b)%Z ->
                rdn SEGS m12 (Z_to_bv 64 b) n = rdn SEGS m11 (Z_to_bv 64 b) n)
    by (intros b n X1 X2 X3; exact (dst_rd C A12 m11 m12 (s - 256) (s - 192) b n CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM12 BEL12 X1 X2 X3)).
  pose proof (RT12 kR bR AR11 ltac:(lia) ltac:(lia)) as AR12. rewrite !Z.sub_0_r in AR12.
  pose proof (O23LeptUddLib.offs_only A11 A12 PL S3 OF11 ON12 OS12) as OF12.
  pose proof (O23LeptUddLib.offs_only A11 A12 S1 S3 OS10b ON12 OS12) as OS10c.
  pose proof (O23LeptUddLib.offs_only A11 A12 S2 S3 OS11 ON12 OS12) as OS11b.
  pose proof (O23LeptUddLib.sel_at_dst C A11 A12 m11 m12 sel4 sv4 S3 SA4d Y4 ON12 D43 (proj2 PM12)) as SA4e.
  destruct (ud_T5 al_rom (mkFP fr1 cs1) r16 m12 s ltac:(lia) ltac:(lia) ltac:(csr; reflexivity)) as (r17 & RUN17 & Q17a & Q17b & AG17).
  pcto RUN17 Q15a. rzs W12 RUN17.
  apply (selDestroy_W (fx := mkFP fr1 cs1) C A12 m12 (with_vmmaps vm12 md) r17 (s - 256)%Z (s - 200)%Z sel4 sv4 (getr r17 1) S CK W12
           ltac:(csr; reflexivity) M256 ltac:(unfold O23LeptCloseIface.SELD_STACK, ALLOC_STACK; lia) ltac:(lia) ltac:(lia) (AL8 200%Z eq_refl)
           eq_refl ltac:(rewrite Q17a; apply ret_ok_even; reflexivity) ltac:(csr; reflexivity) Q17b
           ltac:(rewrite ST12, ST11, ST10, ST9, ST8, FM1 by zl; exact Rs4) SA4e N4 ltac:(right; right; left; exact Y4) O4).
  intros A13 m13 vm13 r18 W13 CS18 LD13 LE13 PM13 R013 BEL13 RT13.
  rewrite with_vmmaps_twice in W13 |- *. rewrite with_vmmaps_vmmaps in RT13.
  pose proof (O23LeptUddLib.only_of_sel A12 A13 sel4 sv4 Y4 LE13) as ON13.
  pose proof (O23LeptUddLib.offs_of_sel A13 sel4 sv4 Y4 LD13) as OS13.
  assert (ONLY13 : O23LeptUddLib.only A A13 (PL ++ S1 ++ S2 ++ S3 ++ S4)).
  { apply (O23LeptUddLib.only_trans_l A A12 A13 _ ONLY12). apply (O23LeptUddLib.only_sub A12 A13 S4); [exact ON13 | intros q Hq; in_app]. }
  pose proof (O23LeptUddLib.sub_of_only A A13 _ ONLY13 OFFS) as SUB13.
  pose proof (POSTM_trans _ _ _ _ _ _ PMc12 (POSTM_sub C A A13 s m12 m13 SUB13 (POSTM_mono C A13 (s - 200 + 8) s m12 m13 ltac:(lia) PM13))) as PMc13.
  assert (ST13 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= 2 ^ 64)%Z -> (b + Z.of_nat n <= s - 200 \/ s - 200 + 8 <= b)%Z ->
                rdn SEGS m13 (Z_to_bv 64 b) n = rdn SEGS m12 (Z_to_bv 64 b) n)
    by (intros b n X1 X2 X3; exact (dst_rd C A13 m12 m13 (s - 256) (s - 200) b n CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM13 BEL13 X1 X2 X3)).
  pose proof (RT13 kR bR AR12 ltac:(lia) ltac:(lia)) as AR13. rewrite !Z.sub_0_r in AR13.
  pose proof (O23LeptUddLib.offs_only A12 A13 PL S4 OF12 ON13 OS13) as OF13.
  pose proof (O23LeptUddLib.offs_only A12 A13 S1 S4 OS10c ON13 OS13) as OS10d.
  pose proof (O23LeptUddLib.offs_only A12 A13 S2 S4 OS11b ON13 OS13) as OS11c.
  pose proof (O23LeptUddLib.offs_only A12 A13 S3 S4 OS12 ON13 OS13) as OS12b.
  assert (FU13 : forall (b : Z) (n : nat), (s - 120 <= b)%Z -> (b + Z.of_nat n <= s)%Z ->
                 rdn SEGS m13 (Z_to_bv 64 b) n = rdn SEGS m7 (Z_to_bv 64 b) n)
    by (intros b n X1 X2; rewrite ST13, ST12, ST11, ST10, ST9, ST8, FM1 by lia; reflexivity).
  pose proof (UDC_pw m7 m13 s ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) FU13 UD) as UD13.
  destruct UD13 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & U11 & U12 & U13 & U14 & U15).
  destruct (ud_X al_rom fr1 cs1 r18 m13 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
              (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) f0 f1 ltac:(lia) ltac:(lia) Hret
              U1 U2 U3 U4 U5 U6 U7 U8 U9 U10 U11 U12 U13 U14 U15 ltac:(csr; reflexivity))
    as (frX & rX & RUNX & X2 & X10 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27 & AGX).
  pcto RUNX Q17a. rzs W13 RUNX.
  apply (HK frX cs1 A13 m13 vm13 rX y0 W13 FZ1).
  - apply cs_kept_intro; csr; reflexivity.
  - exact PMc13.
  - exact (O23LeptUddLib.live_eq_fin A A13 _ ONLY13 OFFS
             (O23LeptUddLib.offs_app _ _ _ OF13 (O23LeptUddLib.offs_app _ _ _ OS10d (O23LeptUddLib.offs_app _ _ _ OS11c
                (O23LeptUddLib.offs_app _ _ _ OS12b OS13))))).
  - exact AR13.
Qed.

End UddT.
