(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptRoom DitherLib DitherLoop LeptCmapArr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL10a.
Import V15CL10a.V15LeptCmapValid.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptCmap2 V15LeptCmapArrSegs.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section CmapArr.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition pta_cells (s : Z) (regs : bvmap 5 word) : list (Z * word) :=
  [((s - 8)%Z, getr regs 1); ((s - 16)%Z, getr regs 8); ((s - 24)%Z, getr regs 9); ((s - 32)%Z, getr regs 18); ((s - 40)%Z, getr regs 19);
   ((s - 48)%Z, getr regs 20); ((s - 56)%Z, getr regs 21); ((s - 64)%Z, getr regs 22); ((s - 72)%Z, getr regs 23); ((s - 80)%Z, getr regs 24);
   ((s - 88)%Z, getr regs 25)].

Lemma pta_cells_PTAF : forall m s q regs, (96 <= s)%Z -> (s <= q)%Z -> (q + 32 < 2 ^ 63)%Z -> cellsZ (PTAF m s q regs) (pta_cells s regs).
Proof. intros m s q regs Hs Hq Hq63. unfold cellsZ, pta_cells, PTAF. repeat split; rdn_solve. Qed.

Lemma cell_w2z : forall (M : word -> option byte) (a : Z) (v : word),
  rdn SEGS M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v) -> rdn SEGS M (Z_to_bv 64 a) 8 = Some (Z_to_le_bytes 8 (u v)).
Proof. intros M a v R. rewrite <- (w2b_Z 8 (u v)) by (pose proof (u64_range v); lia). rewrite zbv_self. exact R. Qed.

(* [comment removed for export] *)
Lemma FRM_at : forall C s' (M M' : word -> option byte) (a : word), Cok C -> FRM C s' M M' -> (c_top C - LSTK <= s')%Z -> (s' <= u a)%Z -> (u a < c_top C)%Z -> M' a = M a.
Proof.
  intros C s' M M' a CK F Hlo Ha Htop. pose proof CK as [T1 T2 T3 T4 T5]. laypins. apply F.
  - apply above_not_gap. lia.
  - intros G; apply pin_glob in G; unfold inZ in G; lia.
  - intros G; apply pin_errno in G; unfold inZ in G; lia.
  - unfold hcell; lia.
  - unfold scratch; lia.
Qed.

Theorem pixcmapToArrays_W : forall C A m md regs (s q cm : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PTA_STACK <= s)%Z -> (s <= q)%Z -> (q + 32 <= c_top C)%Z -> (q mod 8 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x455c0 ->
  getr regs 10 = Z_to_bv 64 cm -> getr regs 11 = Z_to_bv 64 (q + 24) -> getr regs 12 = Z_to_bv 64 (q + 16) ->
  getr regs 13 = Z_to_bv 64 (q + 8) -> getr regs 14 = Z_to_bv 64 q ->
  CMAPat m cm cv -> cmap_ok cv -> live A (Z_to_bv 64 cm) = Some 24%Z -> live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pta <= kR)%Z -> (RB_pta <= bR)%Z ->
  (forall A' m' vm' regs' (rm gm bm am : Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> getr regs' 10 = Z_to_bv 64 0 ->
     POSTM C A (q + 32) m m' -> (forall a : word, (s <= u a < q)%Z -> m' a = m a) ->
     pta_new SEGS C A A' m' q rm gm bm am (c_n cv) ->
     aroom A' vm' (kR - RK_pta) (bR - RB_pta) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 0x193f8) m al_rom) md) S.
Proof.
  intros C A m md regs s q cm cv ret S CK HW H2 Hs16 Hlo Hsq Hq Hq8 H1 Hret H4 H10 H11 H12 H13 H14 CM CMOK Lcm Larr kR bR Hrm HkR HbR HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold PTA_STACK, CALLOC_STACK, ALLOC_STACK, RK_pta, RB_pta in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct CMOK as (Hd & Hna & Hn & Harr1). pose proof CM as (Hc0 & Hc64 & WFc & _).
  assert (Hna256 : (c_nalloc cv <= 256)%Z) by (clear - Hd Hna; destruct Hd as [E|[E|[E|E]]]; rewrite Hna, E; cbn; lia).
  set (n := c_n cv) in *.
  destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
  destruct (blk_range C A m md (Z_to_bv 64 (c_arr cv)) _ CK HW Larr ltac:(lia)) as [Garr TOParr]. rewrite u_Z2bv in Garr, TOParr by (destruct WFc; lia).
  pose proof (alloc_margin_small (n * 4) ltac:(lia)) as MG.
  (* [comment removed for export] *)
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lcm) as (_ & ALcm & _). rewrite u_Z2bv in ALcm by lia.
  assert (ALcm8 : (cm mod 8 = 0)%Z) by (clear - ALcm; Z.div_mod_to_equations; lia).
  destruct (pta_A al_rom fx regs m s q cm n ltac:(lia) ltac:(lia) ltac:(lia) Hq8 ltac:(lia) ALcm8 ltac:(lia)
              (W_sok_win C A m md (s - 96) 96 CK HW ltac:(lia) ltac:(cbn; lia)) (W_sok_win C A m md q 32 CK HW ltac:(lia) ltac:(cbn; lia))
              (CMAP_rd_n SEGS m cm cv CM) ltac:(lia) H2 H10 H11 H12 H13 H14)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q21 & Q20 & Q22 & Q25 & Q24 & Q23 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (PTAF m s q regs) md /\ POSTM C A (q + 32) m (PTAF m s q regs)) by (unfold PTAF; wp_win CK).
  destruct WP1 as [HW1 PM1]. pose proof (pta_cells_PTAF m s q regs ltac:(lia) Hsq ltac:(lia)) as CE1.
  assert (KP1 : forall a : word, (s <= u a < q)%Z -> PTAF m s q regs a = m a).
  { intros a Ha. unfold PTAF. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  set (M1 := PTAF m s q regs) in *.
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x455c0) by (rewrite (AG1 4%bv) by notin_list; exact H4).
  (* [comment removed for export] *)
  apply (W_calloc16_sure C A M1 md r1 n 4 kR bR (Z_to_bv 64 0x19498) (s - 96) S CK HW1 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           Hrm ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m2 vm2 r2 res1 HW2 Hres1 CS2 Hnz1 L0a L1a L00a LEQa ZEROa AL16a TOPa PMa Hrm2.
  assert (Eres1 : res1 = Z_to_bv 64 (u res1)) by (symmetry; apply zbv_self).
  pose proof (u64_range res1) as Rres1. set (rm := u res1) in *. clearbody rm. rewrite Eres1 in Hres1, L0a, L1a, L00a, LEQa, ZEROa. clear Eres1.
  replace (n * 4)%Z with (4 * n)%Z in * by lia.
  destruct (blk_range C A2 m2 _ (Z_to_bv 64 rm) _ CK HW2 L1a ltac:(lia)) as [Grm TOPrm]. rewrite u_Z2bv in Grm, TOPrm by lia.
  assert (SUB2 : sub_live A A2) by (eapply sub_live_new; eassumption).
  pose proof (cellsZ_frm C (s - 96) M1 m2 (pta_cells s regs) CK (proj1 PMa) ltac:(lia) ltac:(unfold pta_cells; repeat constructor; cbn [fst]; lia) CE1) as CE2.
  assert (PM2 : POSTM C A (q + 32) m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (KP2 : forall a : word, (s <= u a < q)%Z -> m2 a = m a).
  { intros a Ha. rewrite <- (KP1 a Ha). apply (FRM_at C (s - 96) M1 m2 a CK (proj1 PMa)); lia. }
  assert (E2r2 : getr r2 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
  assert (E21r2 : getr r2 21 = Z_to_bv 64 n) by (csr; reflexivity).
  assert (E4r2 : getr r2 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
  destruct (pta_B1 al_rom fx r2 m2 n rm ltac:(lia) ltac:(lia) Hres1 E21r2) as (r3 & RUN3 & P1 & P10 & P11 & P9 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  (* [comment removed for export] *)
  assert (P4 : getr r3 4 = Z_to_bv 64 0x455c0) by (rewrite (AG3 4%bv) by notin_list; exact E4r2).
  assert (P2 : getr r3 2 = Z_to_bv 64 (s - 96)) by (rewrite (AG3 2%bv) by notin_list; exact E2r2).
  rewrite MG in Hrm2.
  apply (W_calloc16_sure C A2 m2 _ r3 n 4 (kR - 1) (bR - 2 ^ 17) (Z_to_bv 64 0x194a8) (s - 96) S CK HW2 P10 P11 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(rewrite with_vmmaps_vmmaps; exact Hrm2) ltac:(lia) ltac:(replace (n * 4)%Z with (4 * n)%Z by lia; rewrite MG; lia) ltac:(unfold ROOM_NMAX; lia)
           P1 ltac:(red; apply bv_eq; reflexivity) P4 P2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A3 m3 vm3 r4 res2 HW3 Hres2 CS3 Hnz2 L0b L1b L00b LEQb ZEROb AL16b TOPb PMb Hrm3. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HW3.
  assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
  pose proof (u64_range res2) as Rres2. set (gm := u res2) in *. clearbody gm. rewrite Eres2 in Hres2, L0b, L1b, L00b, LEQb, ZEROb. clear Eres2.
  replace (n * 4)%Z with (4 * n)%Z in * by lia. rewrite MG in Hrm3.
  destruct (blk_range C A3 m3 _ (Z_to_bv 64 gm) _ CK HW3 L1b ltac:(lia)) as [Ggm TOPgm]. rewrite u_Z2bv in Ggm, TOPgm by lia.
  assert (SUB23 : sub_live A2 A3) by (eapply sub_live_new; eassumption).
  pose proof (cellsZ_frm C (s - 96) m2 m3 (pta_cells s regs) CK (proj1 PMb) ltac:(lia) ltac:(unfold pta_cells; repeat constructor; cbn [fst]; lia) CE2) as CE3.
  assert (PM3 : POSTM C A (q + 32) m m3).
  { eapply POSTM_trans; [exact PM2|]. apply (POSTM_sub C A A2); [exact SUB2|]. eapply POSTM_mono; [|exact PMb]. lia. }
  assert (KP3 : forall a : word, (s <= u a < q)%Z -> m3 a = m a).
  { intros a Ha. rewrite <- (KP2 a Ha). apply (FRM_at C (s - 96) m2 m3 a CK (proj1 PMb)); lia. }
  assert (ZEROa3 : forall i, (0 <= i < 4 * n)%Z -> m3 (at_ (Z_to_bv 64 rm) i) = Some (Z_to_bv 8 0)).
  { intros i Hi. rewrite ((proj2 PMb) (Z_to_bv 64 rm) _ i L1a Hi). exact (ZEROa i Hi). }
  assert (E2r4 : getr r4 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
  assert (E21r4 : getr r4 21 = Z_to_bv 64 n) by (csr; reflexivity).
  assert (E4r4 : getr r4 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
  destruct (pta_B2 al_rom fx r4 m3 n gm ltac:(lia) ltac:(lia) Hres2 E21r4) as (r5 & RUN5 & V1 & V10 & V11 & V18 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
  (* [comment removed for export] *)
  assert (V4 : getr r5 4 = Z_to_bv 64 0x455c0) by (rewrite (AG5 4%bv) by notin_list; exact E4r4).
  assert (V2 : getr r5 2 = Z_to_bv 64 (s - 96)) by (rewrite (AG5 2%bv) by notin_list; exact E2r4).
  apply (W_calloc16_sure C A3 m3 _ r5 n 4 (kR - 1 - 1) (bR - 2 ^ 17 - 2 ^ 17) (Z_to_bv 64 0x194b8) (s - 96) S CK HW3 V10 V11 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(rewrite with_vmmaps_vmmaps; exact Hrm3) ltac:(lia) ltac:(replace (n * 4)%Z with (4 * n)%Z by lia; rewrite MG; lia) ltac:(unfold ROOM_NMAX; lia)
           V1 ltac:(red; apply bv_eq; reflexivity) V4 V2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A4 m4 vm4 r6 res3 HW4 Hres3 CS4 Hnz3 L0c L1c L00c LEQc ZEROc AL16c TOPc PMc Hrm4. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HW4.
  assert (Eres3 : res3 = Z_to_bv 64 (u res3)) by (symmetry; apply zbv_self).
  pose proof (u64_range res3) as Rres3. set (bm := u res3) in *. clearbody bm. rewrite Eres3 in Hres3, L0c, L1c, L00c, LEQc, ZEROc. clear Eres3.
  replace (n * 4)%Z with (4 * n)%Z in * by lia. rewrite MG in Hrm4.
  destruct (blk_range C A4 m4 _ (Z_to_bv 64 bm) _ CK HW4 L1c ltac:(lia)) as [Gbm TOPbm]. rewrite u_Z2bv in Gbm, TOPbm by lia.
  assert (SUB34 : sub_live A3 A4) by (eapply sub_live_new; eassumption).
  pose proof (cellsZ_frm C (s - 96) m3 m4 (pta_cells s regs) CK (proj1 PMc) ltac:(lia) ltac:(unfold pta_cells; repeat constructor; cbn [fst]; lia) CE3) as CE4.
  assert (PM4 : POSTM C A (q + 32) m m4).
  { eapply POSTM_trans; [exact PM3|]. apply (POSTM_sub C A A3); [exact (sub_live_trans _ _ _ SUB2 SUB23)|]. eapply POSTM_mono; [|exact PMc]. lia. }
  assert (KP4 : forall a : word, (s <= u a < q)%Z -> m4 a = m a).
  { intros a Ha. rewrite <- (KP3 a Ha). apply (FRM_at C (s - 96) m3 m4 a CK (proj1 PMc)); lia. }
  assert (ZEROa4 : forall i, (0 <= i < 4 * n)%Z -> m4 (at_ (Z_to_bv 64 rm) i) = Some (Z_to_bv 8 0)).
  { intros i Hi. rewrite ((proj2 PMc) (Z_to_bv 64 rm) _ i (SUB23 _ _ L1a) Hi). exact (ZEROa3 i Hi). }
  assert (ZEROb4 : forall i, (0 <= i < 4 * n)%Z -> m4 (at_ (Z_to_bv 64 gm) i) = Some (Z_to_bv 8 0)).
  { intros i Hi. rewrite ((proj2 PMc) (Z_to_bv 64 gm) _ i L1b Hi). exact (ZEROb i Hi). }
  assert (E2r6 : getr r6 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
  assert (E21r6 : getr r6 21 = Z_to_bv 64 n) by (csr; reflexivity).
  assert (E4r6 : getr r6 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
  assert (E9r6 : getr r6 9 = Z_to_bv 64 rm) by (csr; reflexivity).
  assert (E18r6 : getr r6 18 = Z_to_bv 64 gm) by (csr; reflexivity).
  assert (E8r6 : getr r6 8 = Z_to_bv 64 q) by (csr; reflexivity).
  assert (E25r6 : getr r6 25 = Z_to_bv 64 (q + 24)) by (csr; reflexivity).
  assert (E23r6 : getr r6 23 = Z_to_bv 64 (q + 8)) by (csr; reflexivity).
  assert (E24r6 : getr r6 24 = Z_to_bv 64 (q + 16)) by (csr; reflexivity).
  (* [comment removed for export] *)
  destruct (pta_B3 al_rom fx r6 m4 q n rm gm bm ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A4 m4 _ q 32 CK HW4 ltac:(lia) ltac:(cbn; lia)) Hres3 E9r6 E18r6 E21r6 E8r6 E25r6 E23r6 E24r6)
    as (r7 & RUN7 & X1 & X10 & X11 & X19 & AG7).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN7 |].
  assert (SUB4 : sub_live A A4) by (exact (sub_live_trans _ _ _ SUB2 (sub_live_trans _ _ _ SUB23 SUB34))).
  assert (WP5 : W C A4 (PTA3 m4 q rm gm bm) (with_vmmaps vm4 md) /\ POSTM C A (q + 32) m (PTA3 m4 q rm gm bm)) by (unfold PTA3; wp_win CK).
  destruct WP5 as [HW5 PM5].
  assert (OUT5 : forall x : word, ~ (q + 8 <= u x < q + 32)%Z -> PTA3 m4 q rm gm bm x = m4 x).
  { intros x Hx. unfold PTA3. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (QC5 : rdn SEGS (PTA3 m4 q rm gm bm) (Z_to_bv 64 (q + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 rm))
                /\ rdn SEGS (PTA3 m4 q rm gm bm) (Z_to_bv 64 (q + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 gm))
                /\ rdn SEGS (PTA3 m4 q rm gm bm) (Z_to_bv 64 (q + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 bm))) by (unfold PTA3; repeat split; rdn_solve).
  set (M5 := PTA3 m4 q rm gm bm) in *.
  pose proof (cellsZ_out m4 M5 (q + 8) (q + 32) (pta_cells s regs) OUT5 ltac:(unfold pta_cells; repeat (apply Forall_cons; [cbn [fst]; split; [lia | split; [lia | right; lia]] |]); apply Forall_nil) CE4) as CE5.
  assert (X4 : getr r7 4 = Z_to_bv 64 0x455c0) by (rewrite (AG7 4%bv) by notin_list; exact E4r6).
  assert (X2 : getr r7 2 = Z_to_bv 64 (s - 96)) by (rewrite (AG7 2%bv) by notin_list; exact E2r6).
  (* [comment removed for export] *)
  apply (W_calloc16_sure C A4 M5 _ r7 n 4 (kR - 1 - 1 - 1) (bR - 2 ^ 17 - 2 ^ 17 - 2 ^ 17) (Z_to_bv 64 0x194d8) (s - 96) S CK HW5 X10 X11 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(rewrite with_vmmaps_vmmaps; exact Hrm4) ltac:(lia) ltac:(replace (n * 4)%Z with (4 * n)%Z by lia; rewrite MG; lia) ltac:(unfold ROOM_NMAX; lia)
           X1 ltac:(red; apply bv_eq; reflexivity) X4 X2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A5 m5 vm5 r8 res4 HW6 Hres4 CS5 Hnz4 L0d L1d L00d LEQd ZEROd AL16d TOPd PMd Hrm5. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HW6.
  assert (Eres4 : res4 = Z_to_bv 64 (u res4)) by (symmetry; apply zbv_self).
  pose proof (u64_range res4) as Rres4. set (am := u res4) in *. clearbody am. rewrite Eres4 in Hres4, L0d, L1d, L00d, LEQd, ZEROd. clear Eres4.
  replace (n * 4)%Z with (4 * n)%Z in * by lia. rewrite MG in Hrm5.
  destruct (blk_range C A5 m5 _ (Z_to_bv 64 am) _ CK HW6 L1d ltac:(lia)) as [Gam TOPam]. rewrite u_Z2bv in Gam, TOPam by lia.
  assert (SUB45 : sub_live A4 A5) by (eapply sub_live_new; eassumption).
  assert (SUB5 : sub_live A A5) by (exact (sub_live_trans _ _ _ SUB4 SUB45)).
  pose proof (cellsZ_frm C (s - 96) M5 m5 (pta_cells s regs) CK (proj1 PMd) ltac:(lia) ltac:(unfold pta_cells; repeat constructor; cbn [fst]; lia) CE5) as CE6.
  assert (PM6 : POSTM C A (q + 32) m m5).
  { eapply POSTM_trans; [exact PM5|]. apply (POSTM_sub C A A4); [exact SUB4|]. eapply POSTM_mono; [|exact PMd]. lia. }
  assert (KP6 : forall a : word, (s <= u a < q)%Z -> m5 a = m a).
  { intros a Ha. rewrite <- (KP4 a Ha). rewrite <- (OUT5 a) by lia. apply (FRM_at C (s - 96) M5 m5 a CK (proj1 PMd)); lia. }
  assert (ZERO6 : forall z, In z [rm; gm; bm] -> forall i, (0 <= i < 4 * n)%Z -> m5 (at_ (Z_to_bv 64 z) i) = Some (Z_to_bv 8 0)).
  { intros z Hz i Hi.
    assert (Lz : live A4 (Z_to_bv 64 z) = Some (4 * n)%Z /\ (4096 <= z)%Z /\ (z + 4 * n <= alloc_top (c_vm C))%Z /\ m4 (at_ (Z_to_bv 64 z) i) = Some (Z_to_bv 8 0)).
    { cbn [In] in Hz. destruct Hz as [<- | [<- | [<- | []]]].
      - split; [exact (SUB34 _ _ (SUB23 _ _ L1a)) | split; [lia | split; [lia | exact (ZEROa4 i Hi)]]].
      - split; [exact (SUB34 _ _ L1b) | split; [lia | split; [lia | exact (ZEROb4 i Hi)]]].
      - split; [exact L1c | split; [lia | split; [lia | exact (ZEROc i Hi)]]]. }
    destruct Lz as (Lz & Gz & TOPz & Zz).
    rewrite ((proj2 PMd) (Z_to_bv 64 z) _ i Lz Hi). rewrite OUT5; [exact Zz|]. unfold at_. rewrite (u_Z2bv z) by lia. rewrite u_Z2bv by lia. lia. }
  assert (QC6 : rdn SEGS m5 (Z_to_bv 64 (q + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 rm))
                /\ rdn SEGS m5 (Z_to_bv 64 (q + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 gm))
                /\ rdn SEGS m5 (Z_to_bv 64 (q + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 bm))).
  { destruct QC5 as (C1 & C2 & C3). rewrite !(FRM_rdn16 C (s - 96) M5 m5 _ 8 CK (proj1 PMd)) by (cbn; lia). repeat split; assumption. }
  assert (E2r8 : getr r8 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
  assert (E21r8 : getr r8 21 = Z_to_bv 64 n) by (csr; reflexivity).
  assert (E8r8 : getr r8 8 = Z_to_bv 64 q) by (csr; reflexivity).
  assert (E20r8 : getr r8 20 = Z_to_bv 64 cm) by (csr; reflexivity).
  assert (E22r8 : getr r8 22 = Z_to_bv 64 0) by (csr; reflexivity).
  assert (E19r8 : getr r8 19 = Z_to_bv 64 bm) by (csr; reflexivity).
  assert (E9r8 : getr r8 9 = Z_to_bv 64 rm) by (csr; reflexivity).
  assert (E18r8 : getr r8 18 = Z_to_bv 64 gm) by (csr; reflexivity).
  (* [comment removed for export] *)
  assert (CM6 : CMAPat m5 cm cv).
  { apply (CMAPat_frame m m5 cm cv CM). intros x Hx. exact (LIVK_at A m m5 cm 24 x (proj2 PM6) Lcm ltac:(lia) ltac:(lia) Hx). }
  destruct WFc as [WFarr _ _ _ _].
  destruct (pta_B4 al_rom fx r8 m5 q cm n (c_arr cv) rm gm bm am ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              AL16a AL16b AL16c AL16d
              (W_sok_win C A5 m5 _ q 8 CK HW6 ltac:(lia) ltac:(cbn; lia)) (CMAP_rd_arr SEGS m5 cm cv CM6) ltac:(lia) Hres4 E8r8 E21r8 E20r8 E22r8 E9r8 E18r8 E19r8)
    as (r9 & RUN9 & Y10 & Y11 & Y12 & Y21 & Y13 & Y14 & Y15 & Y16 & Y17 & Y5 & Y6 & Y7 & Y28 & AG9).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN9 |].
  set (M6 := wbytes m5 (Z_to_bv 64 q) (word_to_le_bytes 8 (Z_to_bv 64 am))) in *.
  assert (WP7 : W C A5 M6 (with_vmmaps vm5 md) /\ POSTM C A (q + 32) m M6) by (subst M6; wp_win CK).
  destruct WP7 as [HW7 PM7].
  assert (OUT7 : forall x : word, ~ (q <= u x < q + 8)%Z -> M6 x = m5 x).
  { intros x Hx. subst M6. apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia. }
  pose proof (cellsZ_out m5 M6 q (q + 8) (pta_cells s regs) OUT7 ltac:(unfold pta_cells; repeat (apply Forall_cons; [cbn [fst]; split; [lia | split; [lia | right; lia]] |]); apply Forall_nil) CE6) as CE7.
  (* [comment removed for export] *)
  assert (Lrm5 : live A5 (Z_to_bv 64 rm) = Some (4 * n)%Z) by (exact (SUB45 _ _ (SUB34 _ _ (SUB23 _ _ L1a)))).
  assert (Lgm5 : live A5 (Z_to_bv 64 gm) = Some (4 * n)%Z) by (exact (SUB45 _ _ (SUB34 _ _ L1b))).
  assert (Lbm5 : live A5 (Z_to_bv 64 bm) = Some (4 * n)%Z) by (exact (SUB45 _ _ L1c)).
  assert (Larr5 : live A5 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z) by (exact (SUB5 _ _ Larr)).
  assert (NErg : Z_to_bv 64 rm <> Z_to_bv 64 gm) by (intros E; rewrite E in L1a; rewrite L0b in L1a; discriminate L1a).
  assert (NErb : Z_to_bv 64 rm <> Z_to_bv 64 bm) by (intros E; pose proof (SUB23 _ _ L1a) as X; rewrite E in X; rewrite L0c in X; discriminate X).
  assert (NEra : Z_to_bv 64 rm <> Z_to_bv 64 am) by (intros E; pose proof (SUB34 _ _ (SUB23 _ _ L1a)) as X; rewrite E in X; rewrite L0d in X; discriminate X).
  assert (NEgb : Z_to_bv 64 gm <> Z_to_bv 64 bm) by (intros E; rewrite E in L1b; rewrite L0c in L1b; discriminate L1b).
  assert (NEga : Z_to_bv 64 gm <> Z_to_bv 64 am) by (intros E; pose proof (SUB34 _ _ L1b) as X; rewrite E in X; rewrite L0d in X; discriminate X).
  assert (NEba : Z_to_bv 64 bm <> Z_to_bv 64 am) by (intros E; rewrite E in L1c; rewrite L0d in L1c; discriminate L1c).
  assert (NEar : Z_to_bv 64 (c_arr cv) <> Z_to_bv 64 rm) by (intros E; rewrite E in Larr; rewrite L0a in Larr; discriminate Larr).
  assert (NEag : Z_to_bv 64 (c_arr cv) <> Z_to_bv 64 gm) by (intros E; pose proof (SUB2 _ _ Larr) as X; rewrite E in X; rewrite L0b in X; discriminate X).
  assert (NEab : Z_to_bv 64 (c_arr cv) <> Z_to_bv 64 bm) by (intros E; pose proof (SUB23 _ _ (SUB2 _ _ Larr)) as X; rewrite E in X; rewrite L0c in X; discriminate X).
  assert (NEaa : Z_to_bv 64 (c_arr cv) <> Z_to_bv 64 am) by (intros E; pose proof (SUB4 _ _ Larr) as X; rewrite E in X; rewrite L0d in X; discriminate X).
  pose proof (blk_apart C A5 m5 _ _ _ _ _ CK HW6 Lrm5 Lgm5 NErg ltac:(lia) ltac:(lia)) as APrg. rewrite !u_Z2bv in APrg by lia. apply box_i in APrg.
  pose proof (blk_apart C A5 m5 _ _ _ _ _ CK HW6 Lrm5 Lbm5 NErb ltac:(lia) ltac:(lia)) as APrb. rewrite !u_Z2bv in APrb by lia. apply box_i in APrb.
  pose proof (blk_apart C A5 m5 _ _ _ _ _ CK HW6 Lrm5 L1d NEra ltac:(lia) ltac:(lia)) as APra. rewrite !u_Z2bv in APra by lia. apply box_i in APra.
  pose proof (blk_apart C A5 m5 _ _ _ _ _ CK HW6 Lgm5 Lbm5 NEgb ltac:(lia) ltac:(lia)) as APgb. rewrite !u_Z2bv in APgb by lia. apply box_i in APgb.
  pose proof (blk_apart C A5 m5 _ _ _ _ _ CK HW6 Lgm5 L1d NEga ltac:(lia) ltac:(lia)) as APga. rewrite !u_Z2bv in APga by lia. apply box_i in APga.
  pose proof (blk_apart C A5 m5 _ _ _ _ _ CK HW6 Lbm5 L1d NEba ltac:(lia) ltac:(lia)) as APba. rewrite !u_Z2bv in APba by lia. apply box_i in APba.
  pose proof (blk_apart C A5 m5 _ _ _ _ _ CK HW6 Larr5 Lrm5 NEar ltac:(lia) ltac:(lia)) as APar. rewrite !u_Z2bv in APar by lia. apply box_i in APar.
  pose proof (blk_apart C A5 m5 _ _ _ _ _ CK HW6 Larr5 Lgm5 NEag ltac:(lia) ltac:(lia)) as APag. rewrite !u_Z2bv in APag by lia. apply box_i in APag.
  pose proof (blk_apart C A5 m5 _ _ _ _ _ CK HW6 Larr5 Lbm5 NEab ltac:(lia) ltac:(lia)) as APab. rewrite !u_Z2bv in APab by lia. apply box_i in APab.
  pose proof (blk_apart C A5 m5 _ _ _ _ _ CK HW6 Larr5 L1d NEaa ltac:(lia) ltac:(lia)) as APaa. rewrite !u_Z2bv in APaa by lia. apply box_i in APaa.
  assert (G4 : arrs4 rm gm bm am n).
  { unfold arrs4. do 8 (split; [clear - Grm TOPrm Ggm TOPgm Gbm TOPbm Gam TOPam T1 T2 T3 Hn; pose proof LSTK_val; lia|]).
    split; [exact (box_e _ APrg)|]. split; [exact (box_e _ APrb)|]. split; [exact (box_e _ APra)|]. split; [exact (box_e _ APgb)|]. split; [exact (box_e _ APga) | exact (box_e _ APba)]. }
  assert (APar' : (c_arr cv + 4 * n <= rm \/ rm + 4 * n <= c_arr cv)%Z) by (pose proof (box_e _ APar) as X; clear - X Hn Hna; lia).
  assert (APag' : (c_arr cv + 4 * n <= gm \/ gm + 4 * n <= c_arr cv)%Z) by (pose proof (box_e _ APag) as X; clear - X Hn Hna; lia).
  assert (APab' : (c_arr cv + 4 * n <= bm \/ bm + 4 * n <= c_arr cv)%Z) by (pose proof (box_e _ APab) as X; clear - X Hn Hna; lia).
  assert (APaa' : (c_arr cv + 4 * n <= am \/ am + 4 * n <= c_arr cv)%Z) by (pose proof (box_e _ APaa) as X; clear - X Hn Hna; lia).
  apply box_i in APar', APag', APab', APaa'.
  (* [comment removed for export] *)
  destruct (blk_rdn C A5 M6 _ (c_arr cv) (4 * c_nalloc cv) (Z.to_nat (4 * n)) CK HW7 Larr5 ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (bs & Hsrc & _).
  assert (RO6 : regions_ok SEGS M6 (R4 rm gm bm am n)).
  { intros r Hr. unfold R4 in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd]; (split; [lia | split; [lia | split; [lia|]]]).
    - exact (blk_sok C A5 M6 _ rm (4 * n) CK HW7 Lrm5 ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact (blk_sok C A5 M6 _ gm (4 * n) CK HW7 Lgm5 ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact (blk_sok C A5 M6 _ bm (4 * n) CK HW7 Lbm5 ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact (blk_sok C A5 M6 _ am (4 * n) CK HW7 L1d ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (AZ : forall z, In z [rm; gm; bm] -> (4096 <= z)%Z -> (z + 4 * n <= alloc_top (c_vm C))%Z -> arr255 SEGS M6 z n).
  { intros z Hz Gz TOPz. apply arr255_zero; [lia | lia|]. intros i Hi. rewrite OUT7; [exact (ZERO6 z Hz i Hi)|].
    unfold at_. rewrite (u_Z2bv z) by lia. rewrite u_Z2bv by lia. lia. }
  pose proof (AZ rm ltac:(left; reflexivity) Grm TOPrm) as Ar6. pose proof (AZ gm ltac:(right; left; reflexivity) Ggm TOPgm) as Ag6.
  pose proof (AZ bm ltac:(right; right; left; reflexivity) Gbm TOPbm) as Ab6.
  assert (M4 : forall z : Z, (z mod 16 = 0)%Z -> (z mod 4 = 0)%Z) by (clear; intros z E; Z.div_mod_to_equations; lia).
  assert (LR9 : lregs r9 q (c_arr cv) rm gm bm am (4 * n)).
  { unfold lregs. split; [rewrite (AG9 8%bv) by notin_list; exact E8r8|]. split; [exact Y12|]. split; [rewrite (AG9 9%bv) by notin_list; exact E9r8|].
    split; [rewrite (AG9 18%bv) by notin_list; exact E18r8|]. split; [rewrite (AG9 19%bv) by notin_list; exact E19r8|]. split; [exact Y10|]. split; [exact Y21|].
    repeat split; assumption. }
  assert (T47 : (alloc_top (c_vm C) + 1024 < 2 ^ 63)%Z) by (clear - T1 T2 T3; pose proof LSTK_val; lia).
  destruct (pta_loop al_rom (Z.to_nat n) fx r9 M6 M6 q (c_arr cv) rm gm bm am n 0%Z ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) G4
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (M4 _ AL16a) (M4 _ AL16b) (M4 _ AL16c) (M4 _ AL16d)
              (box_e _ APar') (box_e _ APag') (box_e _ APab') (box_e _ APaa') (ex_intro _ bs Hsrc) RO6 (rinv_refl _ _) Ar6 Ag6 Ab6 LR9 Y11)
    as (r10 & M7 & RUN10 & RI7 & Ar7 & Ag7 & Ab7 & AG10).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN10 |].
  assert (FR7 : fresh_regions C A5 A (R4 rm gm bm am n)).
  { unfold fresh_regions, R4. repeat (apply Forall_cons; [|]); [| | | | apply Forall_nil]; cbn [fst snd].
    - exists (Z_to_bv 64 rm), (4 * n)%Z. rewrite u_Z2bv by lia. split; [exact Lrm5 | split; [exact L0a | split; [exact L00a | lia]]].
    - exists (Z_to_bv 64 gm), (4 * n)%Z. rewrite u_Z2bv by lia. split; [exact Lgm5 | split; [|split; [exact L00b | lia]]].
      destruct (live A (Z_to_bv 64 gm)) as [z|] eqn:E; [|reflexivity]. rewrite (SUB2 _ _ E) in L0b. discriminate L0b.
    - exists (Z_to_bv 64 bm), (4 * n)%Z. rewrite u_Z2bv by lia. split; [exact Lbm5 | split; [|split; [exact L00c | lia]]].
      destruct (live A (Z_to_bv 64 bm)) as [z|] eqn:E; [|reflexivity]. rewrite (SUB23 _ _ (SUB2 _ _ E)) in L0c. discriminate L0c.
    - exists (Z_to_bv 64 am), (4 * n)%Z. rewrite u_Z2bv by lia. split; [exact L1d | split; [|split; [exact L00d | lia]]].
      destruct (live A (Z_to_bv 64 am)) as [z|] eqn:E; [|reflexivity]. rewrite (SUB4 _ _ E) in L0d. discriminate L0d. }
  destruct (rinv_WP C A A5 M6 _ M7 (R4 rm gm bm am n) (q + 32) CK HW7 SUB5 ltac:(lia) RI7 FR7) as [HW8 PM8a].
  assert (PM8 : POSTM C A (q + 32) m M7) by (eapply POSTM_trans; [exact PM7 | exact PM8a]).
  (* [comment removed for export] *)
  assert (OUT8 : forall x : word, (alloc_top (c_vm C) <= u x)%Z -> M7 x = M6 x).
  { intros x Hx. apply (proj2 RI7). intros r Hr. unfold R4 in Hr. cbn [In] in Hr. unfold inreg.
    destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd]; lia. }
  assert (CE8 : cellsZ M7 (pta_cells s regs)).
  { apply (cellsZ_keep M6 M7 (pta_cells s regs)); [|exact CE7]. unfold pta_cells.
    repeat (apply Forall_cons; [cbn [fst]; split; [lia | split; [lia | intros x Hx; apply OUT8; lia]] |]). apply Forall_nil. }
  assert (KP8 : forall a : word, (s <= u a < q)%Z -> M7 a = m a).
  { intros a Ha. rewrite OUT8 by lia. rewrite OUT7 by lia. exact (KP6 a Ha). }
  (* [comment removed for export] *)
  assert (E2r10 : getr r10 2 = Z_to_bv 64 (s - 96)) by (rewrite (AG10 2%bv) by notin_list; rewrite (AG9 2%bv) by notin_list; exact E2r8).
  destruct CE8 as (C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & _).
  destruct (pta_E al_rom fx r10 M7 s (u (getr regs 1)) (u (getr regs 8)) (u (getr regs 9)) (u (getr regs 18)) (u (getr regs 19)) (u (getr regs 20))
              (u (getr regs 21)) (u (getr regs 22)) (u (getr regs 23)) (u (getr regs 24)) (u (getr regs 25)) ltac:(lia)
              (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
              (cell_w2z _ _ _ C1) (cell_w2z _ _ _ C8) (cell_w2z _ _ _ C9) (cell_w2z _ _ _ C18) (cell_w2z _ _ _ C19) (cell_w2z _ _ _ C20)
              (cell_w2z _ _ _ C21) (cell_w2z _ _ _ C22) (cell_w2z _ _ _ C23) (cell_w2z _ _ _ C24) (cell_w2z _ _ _ C25) E2r10)
    as (r11 & RUN11 & Z10 & Z2 & Z1 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & AG11).
  rewrite zbv_self in Z1, Z8, Z9, Z18, Z19, Z20, Z21, Z22, Z23, Z24, Z25.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact RUN11 |].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact (pta_ret al_rom fx r11 M7 ret Hret ltac:(rewrite Z1; exact H1)) |].
  apply (HK A5 M7 vm5 r11 rm gm bm am HW8).
  - apply cs_kept_intro; try (rewrite ?Z2, ?Z8, ?Z9, ?Z18, ?Z19, ?Z20, ?Z21, ?Z22, ?Z23, ?Z24, ?Z25; first [reflexivity | (symmetry; exact H2)]).
    all: rewrite (AG11 _) by notin_list; rewrite (AG10 _) by notin_list; rewrite (AG9 _) by notin_list; csr; reflexivity.
  - exact Z10.
  - exact PM8.
  - exact KP8.
  - unfold pta_new, blk_new.
    assert (LAg : live A (Z_to_bv 64 gm) = None) by (destruct (live A (Z_to_bv 64 gm)) as [z|] eqn:E; [rewrite (SUB2 _ _ E) in L0b; discriminate L0b | reflexivity]).
    assert (LAb : live A (Z_to_bv 64 bm) = None) by (destruct (live A (Z_to_bv 64 bm)) as [z|] eqn:E; [rewrite (SUB23 _ _ (SUB2 _ _ E)) in L0c; discriminate L0c | reflexivity]).
    assert (LAa : live A (Z_to_bv 64 am) = None) by (destruct (live A (Z_to_bv 64 am)) as [z|] eqn:E; [rewrite (SUB4 _ _ E) in L0d; discriminate L0d | reflexivity]).
    split; [split; [lia | split; [lia | split; [exact AL16a | split; [exact L0a | split; [exact L00a | exact Lrm5]]]]]|].
    split; [split; [lia | split; [lia | split; [exact AL16b | split; [exact LAg | split; [exact L00b | exact Lgm5]]]]]|].
    split; [split; [lia | split; [lia | split; [exact AL16c | split; [exact LAb | split; [exact L00c | exact Lbm5]]]]]|].
    split; [split; [lia | split; [lia | split; [exact AL16d | split; [exact LAa | split; [exact L00d | exact L1d]]]]]|].
    split; [intros E; apply NErg; rewrite E; reflexivity|]. split; [intros E; apply NErb; rewrite E; reflexivity|].
    split; [intros E; apply NEra; rewrite E; reflexivity|]. split; [intros E; apply NEgb; rewrite E; reflexivity|].
    split; [intros E; apply NEga; rewrite E; reflexivity|]. split; [intros E; apply NEba; rewrite E; reflexivity|].
    split; [intros p N1 N2 N3 N4; rewrite (LEQd p N4), (LEQc p N3), (LEQb p N2), (LEQa p N1); reflexivity|].
    destruct QC6 as (QC1 & QC2 & QC3).
    assert (QK : forall (a : Z) (v : Z), (q <= a)%Z -> (a + 8 <= q + 32)%Z -> (0 <= v < 2 ^ 64)%Z ->
                 rdn SEGS M6 (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)) -> rdn SEGS M7 (Z_to_bv 64 a) 8 = Some (Z_to_le_bytes 8 v)).
    { intros a v Ha1 Ha2 Hv R. rewrite <- (w2b_Z 8 v Hv), <- R. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. apply OUT8. cbn in Hx. lia. }
    assert (QO : forall (a : Z) bsx, (q + 8 <= a)%Z -> (a + 8 <= q + 32)%Z -> rdn SEGS m5 (Z_to_bv 64 a) 8 = Some bsx -> rdn SEGS M6 (Z_to_bv 64 a) 8 = Some bsx).
    { intros a bsx Ha1 Ha2 R. rewrite <- R. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. apply OUT7. cbn in Hx. lia. }
    split; [apply QK; [lia | lia | lia | apply QO; [lia | lia | exact QC1]]|].
    split; [apply QK; [lia | lia | lia | apply QO; [lia | lia | exact QC2]]|].
    split; [apply QK; [lia | lia | lia | apply QO; [lia | lia | exact QC3]]|].
    split; [apply QK; [lia | lia | lia | subst M6; apply rdn_wbytes_hit8; rewrite u_Z2bv by lia; lia]|].
    split; [exact Ar7 | split; [exact Ag7 | exact Ab7]].
  - replace (kR - 4)%Z with (kR - 1 - 1 - 1 - 1)%Z by lia. replace (bR - 4 * 2 ^ 17)%Z with (bR - 2 ^ 17 - 2 ^ 17 - 2 ^ 17 - 2 ^ 17)%Z by lia. exact Hrm5.
Qed.

End CmapArr.
