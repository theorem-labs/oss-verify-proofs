(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptUb V23LeptErr V23LeptCmap V23LeptCmapValid V23LeptCmap2 V23LeptCmapCopyS V23LeptPixCopyAT V23_code_6e000_6f000.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptCmapValid O23LeptCmap2 O23LeptPixCopyAT O23LeptPixCopyGC.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoomBL.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Section PixCopyGC.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).







(* [comment removed for export] *)
Lemma blk_at : forall C A m md (q : word) k i, Cok C -> W C A m md -> live A q = Some k -> (0 <= i < k)%Z ->
  (u q <= u (at_ q i) < u q + k)%Z /\ (4096 <= u q)%Z /\ (u q + k <= alloc_top (c_vm C))%Z.
Proof.
  intros C A m md q k i CK HW L Hi.
  destruct (blk_range C A m md q k CK HW L ltac:(lia)) as [G0 TP].
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  unfold at_. rewrite u_Z2bv by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma KP_stack : forall C A m md X m0 ma mb (lo hi : Z), Cok C -> W C A m md -> O23LeptPixCopyGC.KP A X m0 ma ->
  (forall x : word, ~ (lo <= u x < hi)%Z -> mb x = ma x) -> (c_top C - LSTK <= lo)%Z -> O23LeptPixCopyGC.KP A X m0 mb.
Proof.
  intros C A m md X m0 ma mb lo hi CK HW KPa OUT Hlo.
  apply (O23LeptPixCopyGC.KP_out A X m0 ma mb lo hi KPa OUT).
  intros q k i L NX Hi. destruct (blk_at C A m md q k i CK HW L Hi) as (R & _ & TP).
  pose proof (ck_top C CK) as CT. lia.
Qed.

(* [comment removed for export] *)
Lemma KP_blk : forall C A m md (X : word -> Prop) m0 ma mb (p n lo hi : Z), Cok C -> W C A m md -> O23LeptPixCopyGC.KP A X m0 ma ->
  (forall x : word, ~ (lo <= u x < hi)%Z -> mb x = ma x) ->
  live A (Z_to_bv 64 p) = Some n -> X (Z_to_bv 64 p) -> (0 <= p)%Z -> (p + n < 2 ^ 64)%Z -> (p <= lo)%Z -> (hi <= p + n)%Z -> O23LeptPixCopyGC.KP A X m0 mb.
Proof.
  intros C A m md X m0 ma mb p n lo hi CK HW KPa OUT Lp Xp Hp Hpn Hlo Hhi.
  apply (O23LeptPixCopyGC.KP_out A X m0 ma mb lo hi KPa OUT).
  intros q k i L NX Hi.
  assert (NE : q <> Z_to_bv 64 p) by (intro E; subst q; exact (NX Xp)).
  destruct (blk_at C A m md q k i CK HW L Hi) as (R & _ & _).
  destruct (Z_le_gt_dec 0 n) as [Hn|Hn]; [|lia].
  destruct (blk_apart C A m md q (Z_to_bv 64 p) k n CK HW L Lp NE ltac:(lia) Hn) as [D|D];
    rewrite u_Z2bv in D by lia; lia.
Qed.


  Lemma cells3_FR4d : forall m s ret regs cmd, (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    cells3 (O23LeptPixCopyGC.FR4d m s ret regs cmd) s ret (getr regs 8) (getr regs 9).
Proof. intros m s ret regs cmd Hs Hs64. unfold cells3, O23LeptPixCopyGC.FR4d. repeat split; rdn_solve. Qed.

Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma pcm_Ad : forall regs m (s pixd pixs : Z) (vd vs : pixv) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixd)%Z -> (1 <= pixs)%Z -> pixd <> pixs -> (pixd mod 16 = 0)%Z -> (pixs mod 16 = 0)%Z ->
    PIXat m pixd vd -> PIXat m pixs vs -> p_d vd = p_d vs -> p_cmap vd <> 0%Z ->
    (pixd + 64 <= s - 48 \/ s <= pixd)%Z -> (pixs + 64 <= s - 48 \/ s <= pixs)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x6e4cc : word) m rom) (mkst regs' (0x7350c : word) (O23LeptPixCopyGC.FR4d m s ret regs (p_cmap vd)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x6e520
      /\ getr regs' 10 = Z_to_bv 64 (s - 32) /\ getr regs' 8 = Z_to_bv 64 pixd /\ getr regs' 9 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 12; 13]%list) regs regs'.
Proof.
  intros regs m s pixd pixs vd vs ret Hs Hs64 Hpd Hps NE ALd ALs PXd PXs Ed Ecm DJd DJs SOK H2 H1 H10 H11.
  assert (ALd8 : (pixd mod 8 = 0)%Z) by (apply al16_mod8; exact ALd). assert (ALs8 : (pixs mod 8 = 0)%Z) by (apply al16_mod8; exact ALs).
  pose proof PXd as (Hd0 & Hd64 & WFd & _). pose proof PXs as (Hs0 & Hs64' & WFs & _).
  pose proof (wf_d _ WFs) as Rd. pose proof (wf_cmap _ WFd) as Rcm.
  pose proof (PIX_rd_d SEGS m pixd vd PXd) as Cdd. rewrite Ed in Cdd. pose proof (PIX_rd_d SEGS m pixs vs PXs) as Cds.
  pose proof (PIX_rd_cmap SEGS m pixd vd PXd) as Ccd.
  unfold O23LeptPixCopyGC.FR4d. eexists. split.
  - zv F_6e4cc D_6e4cc (Z_to_bv 64 (s - 48)).
    stepST F_6e4d0 D_6e4d0 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_6e4d4 D_6e4d4 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_6e4d8 D_6e4d8 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepb_ft F_6e4dc D_6e4dc ltac:(condZ).
    stepb_ft F_6e4e0 D_6e4e0 ltac:(condZ).
    stepb_ft F_6e4e4 D_6e4e4 ltac:(condZ).
    guard8 F_6e4e8 D_6e4e8 ALs8. stepb_ft F_6e4ec D_6e4ec ltac:(condZ).
    guard8 F_6e4f0 D_6e4f0 ALd8. stepb_ft F_6e4f4 D_6e4f4 ltac:(condZ).
    stepLD F_6e4f8 D_6e4f8 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; repeat rdn_peel1; exact Cds) ltac:(apply lez4; lia).
    rewrite (v_lw_small (p_d vs)) by lia.
    stepLD F_6e4fc D_6e4fc (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; repeat rdn_peel1; exact Cdd) ltac:(apply lez4; lia).
    rewrite (v_lw_small (p_d vs)) by lia.
    stepb_ft F_6e500 D_6e500 ltac:(condZ).
    stepLD F_6e504 D_6e504 (Z_to_le_bytes 8 (p_cmap vd)) (Z_to_bv 64 (p_cmap vd)) ltac:(addr_norm; repeat rdn_peel1; exact Ccd) ltac:(apply lez8; lia).
    stepST F_6e508 D_6e508 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 (p_cmap vd)) ltac:(sok_in SOK).
    stepb_ft F_6e50c D_6e50c ltac:(condZ).
    sn F_6e510 D_6e510. zv F_6e514 D_6e514 (Z_to_bv 64 (s - 32)). sn F_6e518 D_6e518. sn F_6e51c D_6e51c.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

  (* [comment removed for export] *)
  Lemma pcm_Bd : forall regs m (pixd pixs : Z) (vs : pixv),
    (1 <= pixd)%Z -> (pixd + 64 < 2 ^ 64)%Z -> (1 <= pixs)%Z -> PIXat m pixs vs -> (pixd + 64 <= pixs \/ pixs + 64 <= pixd)%Z ->
    store_ok SEGS m (Z_to_bv 64 pixd) 64 = true ->
    getr regs 8 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x6e520 : word) m rom)
                  (mkst regs' (0x6e530 : word) (wbytes m (Z_to_bv 64 (pixd + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs /\ getr regs' 8 = Z_to_bv 64 (p_cmap vs)
      /\ regs_agree (fun r => In r [8; 10; 11]%list) regs regs'.
Proof.
  intros regs m pixd pixs vs Hpd Hpd64 Hps PXs DJ SOK H8 H9.
  pose proof PXs as (Hs0 & Hs64' & WFs & _). pose proof (wf_cmap _ WFs) as Rcm.
  pose proof (PIX_rd_cmap SEGS m pixs vs PXs) as Ccs.
  eexists. split.
  - sn F_6e520 D_6e520. sn F_6e524 D_6e524.
    stepST F_6e528 D_6e528 (Z_to_bv 64 (pixd + 48)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    stepLD F_6e52c D_6e52c (Z_to_le_bytes 8 (p_cmap vs)) (Z_to_bv 64 (p_cmap vs)) ltac:(addr_norm; repeat rdn_peel1; exact Ccs) ltac:(apply lez8; lia).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.
End Segs.



(* [comment removed for export] *)
Lemma pcmg_tail_W : forall C A A1 m m1 md0 md1 regs r1 (X : word -> Prop) (s pixd pixs : Z) (vd0 vs : pixv) (cvs : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md0 -> W C A1 m1 md1 -> POSTM C (c_A0 C) s m m1 -> O23LeptPixCopyGC.KP A X m m1 ->
  (forall q k, live A q = Some k -> ~ X q -> live A1 q = Some k) ->
  X (Z_to_bv 64 pixd) -> live A (Z_to_bv 64 pixd) = Some 64%Z ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  cells3 m1 s ret (getr regs 8) (getr regs 9) ->
  PIXat m1 pixd vd0 -> p_cmap vd0 = 0%Z -> PIXat m1 pixs vs -> pixd <> pixs ->
  live A1 (Z_to_bv 64 pixd) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixd) = None -> live A1 (Z_to_bv 64 pixs) = Some 64%Z ->
  (p_cmap vs = 0%Z \/ (CMAPat m1 (p_cmap vs) cvs /\ O23LeptCmapValid.cmap_ok cvs /\ live A1 (Z_to_bv 64 (p_cmap vs)) = Some 24%Z /\
                        live A1 (Z_to_bv 64 (c_arr cvs)) = Some (4 * c_nalloc cvs)%Z)) ->
  getr r1 2 = Z_to_bv 64 (s - 48) -> getr r1 8 = Z_to_bv 64 (p_cmap vs) -> getr r1 10 = Z_to_bv 64 pixd ->
  (forall x, In x cs_rest -> getr r1 x = getr regs x) -> getr regs 2 = Z_to_bv 64 s -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  forall (kR bR : Z), aroom A1 (m_vmmaps md1) kR bR -> (RK_cmapcopy <= kR)%Z -> (RB_cmapT (p_cmap vs) <= bR)%Z ->
  (forall A2 m2 vm2 r2 (cd : Z), W C A2 m2 (with_vmmaps vm2 md1) -> cs_kept regs r2 -> getr r2 10 = Z_to_bv 64 0 ->
     POSTM C (c_A0 C) s m m2 -> O23LeptPixCopyGC.KP A X m m2 -> PIXat m2 pixd (set_cmap vd0 cd) -> PIXat m2 pixs vs ->
     ( (p_cmap vs = 0%Z /\ cd = 0%Z /\ forall q, live A2 q = live A1 q)
       \/ (p_cmap vs <> 0%Z /\ exists ad, O23LeptCmap2.cmap_copy C A1 A2 m2 cd ad cvs) ) ->
     aroom A2 vm2 (kR - RK_cmapcopy) (bR - RB_cmapT (p_cmap vs)) ->
     realizes SEGS (mkCfg (mkst r2 ret m2 al_rom) (with_vmmaps vm2 md1)) S) ->
  realizes SEGS (mkCfg (mkst r1 (0x6e530 : word) m1 al_rom) md1) S.
Proof.
  intros C A A1 m m1 md0 md1 regs r1 X s pixd pixs vd0 vs cvs ret S CK HW HW1 PM1 KP1 LX Xpd LpdA Hs16 Hlo Hhi Hret CE1 PXd1 Ecm PXs1 NEds Lpd Lpd00 Lps HCM Q2 Q8 Q10 RR H2r H4 kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PXd1 as (Hd0 & Hd64 & WFd & _). pose proof PXs1 as (Hs0 & Hs64' & WFs & _). pose proof (wf_cmap _ WFs) as Rcm.
  destruct (blk_range C A1 m1 md1 (Z_to_bv 64 pixd) 64 CK HW1 Lpd ltac:(lia)) as [Gpd TOPpd]. rewrite u_Z2bv in Gpd, TOPpd by lia.
  destruct (blk_range C A1 m1 md1 (Z_to_bv 64 pixs) 64 CK HW1 Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof (W_sub0 C A1 m1 md1 HW1) as SUB1.
  assert (NEb : Z_to_bv 64 pixd <> Z_to_bv 64 pixs) by (apply O23LeptPixCopyGC.zbv_ne2; lia).
  pose proof (blk_apart C A1 m1 md1 _ _ _ _ CK HW1 Lpd Lps NEb ltac:(lia) ltac:(lia)) as APds. rewrite !u_Z2bv in APds by lia.
  destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)].
  - rewrite CM0 in Q8.
    destruct (pcm_A0 al_rom r1 m1 s ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) Hret CE1 Q2 Q8) as (r2 & RUN2 & P2 & P1 & P10 & P8 & P9 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    rewrite <- (with_vmmaps_same md1). apply (HK A1 m1 (m_vmmaps md1) r2 0%Z).
    + rewrite with_vmmaps_same. exact HW1.
    + apply cs_kept_intro; csr; try reflexivity.
    + exact P10.
    + exact PM1.
    + exact KP1.
    + replace (set_cmap vd0 0%Z) with vd0; [exact PXd1 | rewrite <- Ecm; symmetry; apply O23LeptPixCopyGC.set_cmap_same].
    + exact PXs1.
    + left. split; [exact CM0 | split; [reflexivity | intros q; reflexivity]].
    + pose proof (RB_cmapT_le (p_cmap vs)). apply (aroom_mono A1 (m_vmmaps md1) kR bR _ _ Hrm); room_consts; lia.
  -
    pose proof CM as (Hc0 & Hc64 & CWF & _). set (cm := p_cmap vs) in *.
    destruct (blk_range C A1 m1 md1 (Z_to_bv 64 cm) 24 CK HW1 Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
    assert (Ecm' : RB_cmapT cm = RB_cmapcopy) by (apply RB_cmapT_pos; lia). rewrite Ecm' in Hrb, HK.
    pose proof CM as CM1.
    destruct (pcm_A1 al_rom r1 m1 s cm pixd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Q2 Q8 Q10) as (r2 & RUN2 & P2 & P1 & P10 & P11 & P12 & P8 & P9 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    apply (pixcmapIsValid_null_W C A1 m1 md1 r2 (s - 48) cm (s - 36) cvs (Z_to_bv 64 0x6e548) S CK HW1 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply sp_slot_al4'; [exact Hs16 | reflexivity]) P1 ltac:(red; apply bv_eq; reflexivity) P10 P11 P12 CM1 CMOK Lcm).
    intros m2 r3 HW2 CS2 PV2 A10.
    replace (Z_to_bv 64 0x6e548) with (0x6e548 : word) by (apply bv_eq; reflexivity).
    pose proof PV2 as [F2 L2].
    assert (PM2 : POSTM C (c_A0 C) s m m2).
    { eapply POSTM_trans; [exact PM1|].
      unshelve (eapply (POSTM_absorb C (c_A0 C) A1 m1 _ m2 s (s - 48) _ _ CK HW1 SUB1 ltac:(lia) _ _ Hhi PV2)); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (Rv2 : rdn SEGS m2 (Z_to_bv 64 (s - 36)) 4 = Some (Z_to_le_bytes 4 1)).
    { rewrite (FRM_rdn16 C (s - 48) _ m2 (s - 36) 4 CK F2) by (cbn; lia). rewrite <- (w2l_Z4 1) by lia. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
    assert (CE2 : cells3 m2 s ret (getr regs 8) (getr regs 9)).
    { apply (cells3_frm C (s - 48) (wbytes m1 (Z_to_bv 64 (s - 36)) (word_to_le_bytes 4 (Z_to_bv 64 1))) m2 s _ _ _ CK F2 ltac:(lia) ltac:(lia) ltac:(lia)).
      eapply (cells3_out m1 _ (s - 36) (s - 32)); [intros x Hx; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia | lia | lia | exact CE1]. }
    assert (HW1v : W C A1 (wbytes m1 (Z_to_bv 64 (s - 36)) (word_to_le_bytes 4 (Z_to_bv 64 1))) md1).
    { apply (W_store_win C A1 m1 md1 _ _ CK HW1); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (EQ2 : forall (p k : Z) (x : word), live A1 (Z_to_bv 64 p) = Some k -> (0 <= p)%Z -> (p + k <= alloc_top (c_vm C))%Z -> (p <= u x < p + k)%Z -> m2 x = m1 x).
    { intros p k x L G0 TP Hx. rewrite (LIVK_byte C A1 _ m2 md1 p k x CK HW1v L2 L G0 TP Hx). apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (PXd2 : PIXat m2 pixd vd0) by (apply (PIXat_frame m1); [exact PXd1 | intros x Hx; exact (EQ2 pixd 64%Z x Lpd ltac:(lia) TOPpd Hx)]).
    assert (CM2 : CMAPat m2 cm cvs) by (apply (CMAPat_frame m1); [exact CM1 | intros x Hx; exact (EQ2 cm 24%Z x Lcm ltac:(lia) TOPcm Hx)]).
    assert (Y2 : getr r3 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (Y8 : getr r3 8 = Z_to_bv 64 cm) by (csr; reflexivity).
    destruct (pcm_B al_rom r3 m2 s cm ltac:(lia) ltac:(lia) Rv2 Y2 Y8) as (r4 & RUN4 & X2 & X1 & X10 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN4 |].
    assert (X4 : getr r4 4 = Z_to_bv 64 0x1381d0) by (rewrite (AG4 4) by (cbv; intuition discriminate); csr; reflexivity).
    apply (pixcmapCopy_sure_W C A1 m2 md1 r4 (s - 48) cm cvs (Z_to_bv 64 0x6e558) S CK HW2 X2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold LSF; lia) ltac:(lia) X1 ltac:(red; apply bv_eq; reflexivity) X4 X10 CM2 CMOK Lcm Larr kR bR Hrm Hrk Hrb).
    intros A2 m3 vm1 r5 cd ad HWa CSa PMa Hres CC Hrm1.
    replace (Z_to_bv 64 0x6e558) with (0x6e558 : word) by (apply bv_eq; reflexivity).
    pose proof (cells3_frm C (s - 48) m2 m3 s _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE2) as CE3.
    assert (PMa' : POSTM C (c_A0 C) s m m3) by (eapply POSTM_trans; [exact PM2 | apply (POSTM_sub C (c_A0 C) A1); [exact SUB1 | eapply POSTM_mono; [|exact PMa]; lia]]).
    assert (PXd3 : PIXat m3 pixd vd0) by (apply (PIXat_frame m2); [exact PXd2 | intros x Hx; exact (LIVK_byte C A1 m2 m3 md1 pixd 64 x CK HW2 (proj2 PMa) Lpd ltac:(lia) TOPpd Hx)]).
    assert (E2a : getr r5 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (E9a : getr r5 9 = Z_to_bv 64 pixd) by (csr; reflexivity).
    pose proof CC as (CMOKc & Gcd & TOPcd & ALcd & Gad & TOPad & ALad & NEcdad & L0 & LA0 & L00 & LA00 & L1 & K1 & LEQ & CD3).
    assert (NEpdcd : Z_to_bv 64 pixd <> Z_to_bv 64 cd) by (intros E; rewrite E in Lpd; rewrite Lpd in L0; discriminate).
    assert (NEpdad : Z_to_bv 64 pixd <> Z_to_bv 64 ad) by (intros E; rewrite E in Lpd; rewrite Lpd in LA0; discriminate).
    assert (Lpd1 : live A2 (Z_to_bv 64 pixd) = Some 64%Z) by (rewrite (LEQ _ NEpdcd NEpdad); exact Lpd).
    assert (SUBa : sub_live A1 A2) by (eapply sub_live_new2; [exact L0 | exact LA0 | exact L1 | exact K1 | exact LEQ]).
    assert (SUBr : sub_live (c_A0 C) A2) by (eapply sub_live_trans; [exact SUB1 | exact SUBa]).
    pose proof (blk_apart C A2 m3 _ _ _ _ _ CK HWa Lpd1 L1 NEpdcd ltac:(lia) ltac:(lia)) as APpdcd. rewrite !u_Z2bv in APpdcd by lia. apply O23LeptCmap2.box_i in APpdcd.
    destruct (pcm_C al_rom r5 m3 s cd pixd vd0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PXd3 Ecm ltac:(lia)
                (W_sok_win C A2 m3 _ (s - 48) 48 CK HWa ltac:(lia) ltac:(cbn; lia)) (blk_sok C A2 m3 _ pixd 64 CK HWa Lpd1 ltac:(lia) ltac:(lia) ltac:(lia)) E2a Hres E9a)
      as (r6 & RUN6 & V2 & V1 & V10 & V11 & V12 & V9 & AG6).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN6 |].
    set (M5 := wbytes m3 (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (M6 := wbytes M5 (Z_to_bv 64 (pixd + 48)) (word_to_le_bytes 8 (Z_to_bv 64 cd))).
    assert (WP5 : W C A2 M5 (with_vmmaps vm1 md1) /\ POSTM C (c_A0 C) s m M5).
    { subst M5. apply (WP_win C A2 (c_A0 C) m m3 _ _ _ s CK); [| exact SUBr | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia].
      split; [exact HWa | exact PMa']. }
    assert (WP6 : W C A2 M6 (with_vmmaps vm1 md1) /\ POSTM C (c_A0 C) s m M6).
    { subst M6. apply (WP_blk C (c_A0 C) A2 m M5 _ (Z_to_bv 64 pixd) _ 64); [exact CK | exact WP5 | exact Lpd1 | exact Lpd00 | exact Lpd00 | exact SUBr | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
    destruct WP6 as [HW6 PM6].
    assert (OUT5 : forall x : word, ~ (s - 32 <= u x < s - 24)%Z -> M5 x = m3 x).
    { intros x Hx. subst M5. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (OUT6 : forall x : word, ~ (pixd + 48 <= u x < pixd + 56)%Z -> M6 x = M5 x).
    { intros x Hx. subst M6. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (PXd6 : PIXat M6 pixd (set_cmap vd0 cd)).
    { subst M6. apply PIX_wr_cmap; [|lia]. apply (PIXat_frame m3); [exact PXd3|]. intros x Hx. apply OUT5. lia. }
    set (cvs' := CMAPV ad (c_d cvs) (c_nalloc cvs) (c_n cvs) 0) in *.
    assert (CD6 : CMAPat M6 cd cvs').
    { pose proof (O23LeptCmap2.box_e _ APpdcd) as U1. apply (CMAPat_frame m3); [exact CD3|]. intros x Hx. rewrite OUT6 by lia. apply OUT5. lia. }
    assert (CE6 : cells3 M6 s ret (getr regs 8) (getr regs 9)).
    { eapply (cells3_out M5 _ (pixd + 48) (pixd + 56)); [exact OUT6 | lia | lia | lia |].
      eapply (cells3_out m3 _ (s - 32) (s - 24)); [exact OUT5 | lia | lia | lia | exact CE3]. }
    pose proof (O23LeptPixCopyAT.cmap_ok_copy cvs ad CMOK ltac:(lia)) as CMOK'.
    apply (pixcmapIsValid_null_W C A2 M6 _ r6 (s - 48) cd (s - 32) cvs' (Z_to_bv 64 0x6e590) S CK HW6 V2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply sp_slot_al4'; [exact Hs16 | reflexivity]) V1 ltac:(red; apply bv_eq; reflexivity) V10 V11 V12 CD6 CMOK' L1).
    intros m7 r7 HW7 CS7 PV7 B10.
    replace (Z_to_bv 64 0x6e590) with (0x6e590 : word) by (apply bv_eq; reflexivity).
    pose proof PV7 as [F7 L7].
    assert (PM7 : POSTM C (c_A0 C) s m m7).
    { eapply POSTM_trans; [exact PM6|].
      unshelve (eapply (POSTM_absorb C (c_A0 C) A2 M6 _ m7 s (s - 48) _ _ CK HW6 SUBr ltac:(lia) _ _ Hhi PV7)); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (Rv7 : rdn SEGS m7 (Z_to_bv 64 (s - 32)) 4 = Some (Z_to_le_bytes 4 1)).
    { rewrite (FRM_rdn16 C (s - 48) _ m7 (s - 32) 4 CK F7) by (cbn; lia). rewrite <- (w2l_Z4 1) by lia. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
    assert (CE7 : cells3 m7 s ret (getr regs 8) (getr regs 9)).
    { apply (cells3_frm C (s - 48) (wbytes M6 (Z_to_bv 64 (s - 32)) (word_to_le_bytes 4 (Z_to_bv 64 1))) m7 s _ _ _ CK F7 ltac:(lia) ltac:(lia) ltac:(lia)).
      eapply (cells3_out M6 _ (s - 32) (s - 28)); [intros x Hx; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia | lia | lia | exact CE6]. }
    assert (HW6v : W C A2 (wbytes M6 (Z_to_bv 64 (s - 32)) (word_to_le_bytes 4 (Z_to_bv 64 1))) (with_vmmaps vm1 md1)).
    { apply (W_store_win C A2 M6 _ _ _ CK HW6); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (EQ7 : forall (p k : Z) (x : word), live A2 (Z_to_bv 64 p) = Some k -> (0 <= p)%Z -> (p + k <= alloc_top (c_vm C))%Z -> (p <= u x < p + k)%Z -> m7 x = M6 x).
    { intros p k x L G0 TP Hx. rewrite (LIVK_byte C A2 _ m7 _ p k x CK HW6v L7 L G0 TP Hx). apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (Y2' : getr r7 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    destruct (pcm_D al_rom r7 m7 s ret _ _ ltac:(lia) ltac:(lia) Hret CE7 Rv7 Y2') as (r8 & RUN8 & Z2 & Z1 & Z10 & Z8 & Z9 & AG8).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN8 |].
    apply (HK A2 m7 vm1 r8 cd).
    + exact HW7.
    + apply cs_kept_intro; csr; try reflexivity.
    + exact Z10.
    + exact PM7.
    + assert (LX2 : forall q k, live A q = Some k -> ~ X q -> live A2 q = Some k).
      { intros q k Lq NX. pose proof (LX q k Lq NX) as L1q.
        assert (N1 : q <> Z_to_bv 64 cd) by (intros E; rewrite E in L1q; rewrite L1q in L0; discriminate).
        assert (N2 : q <> Z_to_bv 64 ad) by (intros E; rewrite E in L1q; rewrite L1q in LA0; discriminate).
        rewrite (LEQ _ N1 N2). exact L1q. }
      assert (KQ1 : O23LeptPixCopyGC.KP A X m (wbytes m1 (Z_to_bv 64 (s - 36)) (word_to_le_bytes 4 (Z_to_bv 64 1)))).
      { apply (KP_stack C A m md0 X m m1 _ (s - 36) (s - 32) CK HW KP1); [intros x Hx; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia]. }
      pose proof (O23LeptPixCopyGC.KP_livk A A1 X m _ m2 KQ1 L2 LX) as KQ2.
      pose proof (O23LeptPixCopyGC.KP_livk A A1 X m m2 m3 KQ2 (proj2 PMa) LX) as KQ3.
      assert (KQ5 : O23LeptPixCopyGC.KP A X m M5) by (apply (KP_stack C A m md0 X m m3 M5 (s - 32) (s - 24) CK HW KQ3 OUT5); lia).
      assert (KQ6 : O23LeptPixCopyGC.KP A X m M6) by (apply (KP_blk C A m md0 X m M5 M6 pixd 64 (pixd + 48) (pixd + 56) CK HW KQ5 OUT6 LpdA Xpd); lia).
      assert (KQ7 : O23LeptPixCopyGC.KP A X m (wbytes M6 (Z_to_bv 64 (s - 32)) (word_to_le_bytes 4 (Z_to_bv 64 1)))).
      { apply (KP_stack C A m md0 X m M6 _ (s - 32) (s - 28) CK HW KQ6); [intros x Hx; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia]. }
      exact (O23LeptPixCopyGC.KP_livk A A2 X m _ m7 KQ7 L7 LX2).
    + apply (PIXat_frame M6); [exact PXd6|]. intros x Hx. exact (EQ7 pixd 64%Z x Lpd1 ltac:(lia) TOPpd Hx).
    + assert (Lps2 : live A2 (Z_to_bv 64 pixs) = Some 64%Z).
      { assert (N1 : Z_to_bv 64 pixs <> Z_to_bv 64 cd) by (intros E; rewrite E in Lps; rewrite Lps in L0; discriminate).
        assert (N2 : Z_to_bv 64 pixs <> Z_to_bv 64 ad) by (intros E; rewrite E in Lps; rewrite Lps in LA0; discriminate).
        rewrite (LEQ _ N1 N2). exact Lps. }
      assert (PXs2 : PIXat m2 pixs vs) by (apply (PIXat_frame m1); [exact PXs1 | intros x Hx; exact (EQ2 pixs 64%Z x Lps ltac:(lia) TOPps Hx)]).
      assert (PXs3 : PIXat m3 pixs vs) by (apply (PIXat_frame m2); [exact PXs2 | intros x Hx; exact (LIVK_byte C A1 m2 m3 md1 pixs 64 x CK HW2 (proj2 PMa) Lps ltac:(lia) TOPps Hx)]).
      assert (PXs6 : PIXat M6 pixs vs) by (apply (PIXat_frame m3); [exact PXs3 | intros x Hx; rewrite OUT6 by lia; apply OUT5; lia]).
      apply (PIXat_frame M6); [exact PXs6 | intros x Hx; exact (EQ7 pixs 64%Z x Lps2 ltac:(lia) TOPps Hx)].
    + right. split; [lia | exists ad].
      unfold O23LeptCmap2.cmap_copy. do 15 (split; [assumption|]). apply (CMAPat_frame M6); [exact CD6|]. intros x Hx. exact (EQ7 cd 24%Z x L1 ltac:(lia) ltac:(lia) Hx).
    + exact Hrm1.
Qed.

(* [comment removed for export] *)




Theorem pixCopyColormap_given_W : forall C A m md regs (s pixd pixs : Z) (vd vs : pixv) (cvs cvd : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs ->
  PIXat m pixd vd -> PIXat m pixs vs -> p_d vd = p_d vs -> pixd <> pixs ->
  live A (Z_to_bv 64 pixd) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixd) = None -> live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (p_cmap vs = 0%Z \/ (CMAPat m (p_cmap vs) cvs /\ O23LeptCmapValid.cmap_ok cvs /\ live A (Z_to_bv 64 (p_cmap vs)) = Some 24%Z /\
                        live A (Z_to_bv 64 (c_arr cvs)) = Some (4 * c_nalloc cvs)%Z)) ->
  (p_cmap vd = 0%Z \/ (CMAPat m (p_cmap vd) cvd /\ O23LeptCmapValid.cmap_ok cvd /\ live A (Z_to_bv 64 (p_cmap vd)) = Some 24%Z /\
                        live A (Z_to_bv 64 (c_arr cvd)) = Some (4 * c_nalloc cvd)%Z /\
                        live (c_A0 C) (Z_to_bv 64 (p_cmap vd)) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cvd)) = None /\
                        c_arr cvd <> pixd /\ c_arr cvd <> pixs /\
                        (p_cmap vs <> 0%Z -> p_cmap vd <> p_cmap vs /\ c_arr cvd <> c_arr cvs))) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_cmapcopy <= kR)%Z -> (RB_cmapT (p_cmap vs) <= bR)%Z ->
  (forall A' m' vm' regs' (cd' : Z) (cvd' : cmapv), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     POSTM C (c_A0 C) s m m' -> O23LeptPixCopyGC.KP A (O23LeptPixCopyGC.Xcm pixd (p_cmap vd) (c_arr cvd)) m m' ->
     PIXat m' pixd (set_cmap vd cd') -> PIXat m' pixs vs ->
     (forall (q : word) k, live A q = Some k -> (p_cmap vd <> 0%Z -> q <> Z_to_bv 64 (p_cmap vd) /\ q <> Z_to_bv 64 (c_arr cvd)) -> live A' q = Some k) ->
     O23LeptPixCopyGC.pcg_live C A A' m' (p_cmap vs) cvs (p_cmap vd) (c_arr cvd) cd' cvd' ->
     aroom A' vm' (kR - RK_cmapcopy) (bR - RB_cmapT (p_cmap vs)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6e4cc : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixd pixs vd vs cvs cvd ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 PXd PXs Ed NEds Lpd Lpd00 Lps HCMs HCMd kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PXd as (Hd0 & Hd64 & WFd & _). pose proof PXs as (Hs0 & Hs64' & WFs & _). pose proof (wf_cmap _ WFs) as Rcm.
  destruct (blk_range C A m md (Z_to_bv 64 pixd) 64 CK HW Lpd ltac:(lia)) as [Gpd TOPpd]. rewrite u_Z2bv in Gpd, TOPpd by lia.
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lpd) as (_ & ALpd & _). rewrite u_Z2bv in ALpd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  assert (NEb : Z_to_bv 64 pixd <> Z_to_bv 64 pixs) by (apply O23LeptPixCopyGC.zbv_ne2; lia).
  pose proof (blk_apart C A m md _ _ _ _ CK HW Lpd Lps NEb ltac:(lia) ltac:(lia)) as APds. rewrite !u_Z2bv in APds by lia.
  pose proof (W_sub0 C A m md HW) as SUB0.
  set (X := O23LeptPixCopyGC.Xcm pixd (p_cmap vd) (c_arr cvd)) in *.
  assert (Xpd : X (Z_to_bv 64 pixd)) by (left; reflexivity).
  destruct HCMd as [Ecmd | (CMd & CMOKd & Lcmd & Larrd & L0cmd & L0arrd & NEad & NEas & NEss)].
  - destruct (pcm_A al_rom regs m s pixd pixs vd vs ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) NEds ALpd ALps PXd PXs Ed Ecmd ltac:(lia) ltac:(lia)
                (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11)
      as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    assert (WP1 : W C A (O23LeptPixCopyAT.FR4c m s ret regs) md /\ POSTM C A s m (O23LeptPixCopyAT.FR4c m s ret regs)) by (unfold O23LeptPixCopyAT.FR4c; wp_win CK).
    destruct WP1 as [HW1 PM1]. set (M1 := O23LeptPixCopyAT.FR4c m s ret regs) in *.
    pose proof (cells3_FR4c m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
    assert (OUT1 : forall x : word, ~ (s - 48 <= u x < s)%Z -> M1 x = m x).
    { intros x Hx. subst M1. unfold O23LeptPixCopyAT.FR4c. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    assert (PXd1 : PIXat M1 pixd vd) by (apply (PIXat_frame m M1 _ _ PXd); intros x Hx; apply OUT1; lia).
    assert (PXs1 : PIXat M1 pixs vs) by (apply (PIXat_frame m M1 _ _ PXs); intros x Hx; apply OUT1; lia).
    assert (KP1 : O23LeptPixCopyGC.KP A X m M1) by (apply (KP_stack C A m md X m m M1 (s - 48) s CK HW (O23LeptPixCopyGC.KP_refl A X m) OUT1); lia).
    assert (HCM1 : p_cmap vs = 0%Z \/ (CMAPat M1 (p_cmap vs) cvs /\ O23LeptCmapValid.cmap_ok cvs /\ live A (Z_to_bv 64 (p_cmap vs)) = Some 24%Z /\
                         live A (Z_to_bv 64 (c_arr cvs)) = Some (4 * c_nalloc cvs)%Z)).
    { destruct HCMs as [E0 | (CMs & CMOKs & Lcms & Larrs)]; [left; exact E0 | right].
      destruct (blk_range C A m md (Z_to_bv 64 (p_cmap vs)) 24 CK HW Lcms ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by (pose proof CMs as (? & ? & _); lia).
      split; [apply (CMAPat_frame m M1 _ _ CMs); intros x Hx; apply OUT1; lia | split; [exact CMOKs | split; [exact Lcms | exact Larrs]]]. }
    assert (RR1 : forall x, In x cs_rest -> getr r1 x = getr regs x) by rest_solve.
    apply (pcmg_tail_W C A A m M1 md md regs r1 X s pixd pixs vd vs cvs ret S CK HW HW1 (POSTM_sub C (c_A0 C) A s m M1 SUB0 PM1) KP1
             ltac:(intros q k Lq _; exact Lq) Xpd Lpd Hs16 Hlo Hhi Hret CE1 PXd1 Ecmd PXs1 NEds Lpd Lpd00 Lps HCM1 Q2 Q8 Q10 RR1 H2 H4 kR bR Hrm Hrk Hrb).
    intros A2 m2 vm2 r2 cd HW2 CS2 R10 PM2 KP2 PXd2 PXs2 DISJ Hrm2.
    destruct (O23LeptPixCopyGC.pcg_live_of C A A A2 m2 (p_cmap vs) cvs (p_cmap vd) (c_arr cvd) cd
                ltac:(intros q _; reflexivity) ltac:(intros N; exfalso; exact (N Ecmd)) DISJ) as (cvd' & PCG & LV).
    exact (HK A2 m2 vm2 r2 cd cvd' HW2 CS2 PM2 KP2 PXd2 PXs2 LV PCG Hrm2).
  - pose proof CMd as (Hcd0 & Hcd64 & CWFd & _). pose proof (cf_arr _ CWFd) as Rarrd.
    set (cmd := p_cmap vd) in *. set (arrd := c_arr cvd) in *.
    destruct (blk_range C A m md (Z_to_bv 64 cmd) 24 CK HW Lcmd ltac:(lia)) as [Gcmd TOPcmd]. rewrite u_Z2bv in Gcmd, TOPcmd by lia.
    pose proof (O23LeptPixCopyGC.cmap_sz_ne cvd CMOKd) as SZd.
    assert (NEca : cmd <> arrd).
    { intros E. rewrite <- E, Lcmd in Larrd. injection Larrd as Ej. lia. }
    assert (NWpc : Z_to_bv 64 pixd <> Z_to_bv 64 cmd) by (intros E; rewrite E, Lcmd in Lpd; discriminate).
    assert (NWpa : Z_to_bv 64 pixd <> Z_to_bv 64 arrd) by (apply O23LeptPixCopyGC.zbv_ne2; lia).
    assert (NWsc : Z_to_bv 64 pixs <> Z_to_bv 64 cmd) by (intros E; rewrite E, Lcmd in Lps; discriminate).
    assert (NWsa : Z_to_bv 64 pixs <> Z_to_bv 64 arrd) by (apply O23LeptPixCopyGC.zbv_ne2; lia).
    assert (NXs : ~ X (Z_to_bv 64 pixs)).
    { unfold X, O23LeptPixCopyGC.Xcm. intros [E | (_ & [E | E])]; [exact (NEb (eq_sym E)) | exact (NWsc E) | exact (NWsa E)]. }
    destruct (pcm_Ad al_rom regs m s pixd pixs vd vs ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) NEds ALpd ALps PXd PXs Ed ltac:(lia) ltac:(lia) ltac:(lia)
                (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11)
      as (r1 & RUN1 & Q2 & Q1 & Q10 & Q8 & Q9 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    assert (WP1 : W C A (O23LeptPixCopyGC.FR4d m s ret regs cmd) md /\ POSTM C A s m (O23LeptPixCopyGC.FR4d m s ret regs cmd)) by (unfold O23LeptPixCopyGC.FR4d; wp_win CK).
    destruct WP1 as [HW1 PM1]. set (M1 := O23LeptPixCopyGC.FR4d m s ret regs cmd) in *.
    pose proof (cells3_FR4d m s ret regs cmd ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
    assert (OUT1 : forall x : word, ~ (s - 48 <= u x < s)%Z -> M1 x = m x).
    { intros x Hx. subst M1. unfold O23LeptPixCopyGC.FR4d. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    assert (CMd1 : CMAPat M1 cmd cvd) by (apply (CMAPat_frame m M1 _ _ CMd); intros x Hx; apply OUT1; lia).
    assert (Q4 : getr r1 4 = getr regs 4) by (rewrite (AG1 4) by (cbv; intuition discriminate); reflexivity). rewrite H4 in Q4.
    assert (KP1 : O23LeptPixCopyGC.KP A X m M1) by (apply (KP_stack C A m md X m m M1 (s - 48) s CK HW (O23LeptPixCopyGC.KP_refl A X m) OUT1); lia).
    apply (pixcmapDestroy_W C A M1 md r1 (s - 48) (s - 32) cmd cvd (4 * c_nalloc cvd) (Z_to_bv 64 0x6e520) S CK HW1 Q2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) Q1
             ltac:(red; apply bv_eq; reflexivity) Q4 ltac:(replace (s - 32)%Z with (s + (-32))%Z by lia; apply mod16_plus_mod8; [exact Hs16 | reflexivity]) Q10).
    { subst M1. unfold O23LeptPixCopyGC.FR4d. rewrite <- (w2b_Z 8 cmd) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. }
    { exact CMd1. } { exact Lcmd. } { exact Larrd. } { exact L0cmd. } { exact L0arrd. } { exact NEca. }
    intros A1 m1' vm1 r2 HWa CSa La1 La2 LEQa PMa RDa HRTa.
    replace (Z_to_bv 64 0x6e520) with (0x6e520 : word) by (apply bv_eq; reflexivity).
    assert (LXd : forall q k, live A q = Some k -> ~ X q -> live A1 q = Some k).
    { intros q k Lq NX.
      assert (N1 : q <> Z_to_bv 64 cmd) by (intros E; apply NX; unfold X, O23LeptPixCopyGC.Xcm; right; split; [lia | left; exact E]).
      assert (N2 : q <> Z_to_bv 64 arrd) by (intros E; apply NX; unfold X, O23LeptPixCopyGC.Xcm; right; split; [lia | right; exact E]).
      rewrite (LEQa q N1 N2). exact Lq. }
    pose proof (O23LeptPixCopyGC.KP_livk A A1 X m M1 m1' KP1 (proj2 PMa) LXd) as KPa.
    assert (Lpd1 : live A1 (Z_to_bv 64 pixd) = Some 64%Z) by (rewrite (LEQa _ NWpc NWpa); exact Lpd).
    assert (Lps1 : live A1 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQa _ NWsc NWsa); exact Lps).
    assert (LVb : forall (p k : Z) (x : word), live A1 (Z_to_bv 64 p) = Some k -> (0 <= p)%Z -> (p + k <= alloc_top (c_vm C))%Z -> (p <= u x < p + k)%Z -> m1' x = M1 x).
    { intros p k x L G0 TP Hx. pose proof (proj2 PMa (Z_to_bv 64 p) k (u x - p)%Z L ltac:(lia)) as E.
      replace (at_ (Z_to_bv 64 p) (u x - p)) with x in E by (unfold at_; apply bv_eq; rewrite !u_Z2bv; rewrite ?u_Z2bv; pose proof (u64_range x); lia).
      exact E. }
    assert (PXda : PIXat m1' pixd vd).
    { apply (PIXat_frame m); [exact PXd |]. intros x Hx. rewrite (LVb pixd 64%Z x Lpd1 ltac:(lia) TOPpd Hx). apply OUT1. lia. }
    assert (PXsa : PIXat m1' pixs vs).
    { apply (PIXat_frame m); [exact PXs |]. intros x Hx. exact (O23LeptPixCopyGC.KP_at A X m m1' pixs 64 x KPa Lps NXs ltac:(lia) ltac:(lia) Hx). }
    destruct (pcm_Bd al_rom r2 m1' pixd pixs vs ltac:(lia) ltac:(lia) ltac:(lia) PXsa ltac:(lia)
                (blk_sok C A1 m1' _ pixd 64 CK HWa Lpd1 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
      as (r3 & RUN3 & B10 & B11 & B8 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    set (Mb := wbytes m1' (Z_to_bv 64 (pixd + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    assert (PMa0 : POSTM C (c_A0 C) s m m1').
    { eapply POSTM_trans; [exact (POSTM_sub C (c_A0 C) A s m M1 SUB0 PM1) |].
      apply (POSTM_sub C (c_A0 C) A1); [exact (W_sub0 C A1 m1' _ HWa) |]. eapply POSTM_mono; [| exact PMa]; lia. }
    assert (WPb : W C A1 Mb (with_vmmaps vm1 md) /\ POSTM C (c_A0 C) s m Mb).
    { subst Mb. apply (WP_blk C (c_A0 C) A1 m m1' _ (Z_to_bv 64 pixd) _ 64); [exact CK | split; [exact HWa | exact PMa0] | exact Lpd1 | exact Lpd00 | exact Lpd00 | exact (W_sub0 C A1 m1' _ HWa) | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
    destruct WPb as [HWb PMb].
    assert (OUTb : forall x : word, ~ (pixd + 48 <= u x < pixd + 56)%Z -> Mb x = m1' x).
    { intros x Hx. subst Mb. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (KPb : O23LeptPixCopyGC.KP A X m Mb) by (apply (KP_blk C A m md X m m1' Mb pixd 64 (pixd + 48) (pixd + 56) CK HW KPa OUTb Lpd Xpd); lia).
    assert (CEb : cells3 Mb s ret (getr regs 8) (getr regs 9)).
    { eapply (cells3_out m1' _ (pixd + 48) (pixd + 56)); [exact OUTb | lia | lia | lia |].
      apply (cells3_frm C (s - 32 + 8) M1 m1' s _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1). }
    assert (PXdb : PIXat Mb pixd (set_cmap vd 0%Z)) by (subst Mb; apply PIX_wr_cmap; [exact PXda | lia]).
    assert (PXsb : PIXat Mb pixs vs).
    { apply (PIXat_frame m); [exact PXs |]. intros x Hx. exact (O23LeptPixCopyGC.KP_at A X m Mb pixs 64 x KPb Lps NXs ltac:(lia) ltac:(lia) Hx). }
    assert (HCMb : p_cmap vs = 0%Z \/ (CMAPat Mb (p_cmap vs) cvs /\ O23LeptCmapValid.cmap_ok cvs /\ live A1 (Z_to_bv 64 (p_cmap vs)) = Some 24%Z /\
                         live A1 (Z_to_bv 64 (c_arr cvs)) = Some (4 * c_nalloc cvs)%Z)).
    { destruct HCMs as [E0 | (CMs & CMOKs & Lcms & Larrs)]; [left; exact E0 | right].
      pose proof CMs as (Hc0 & Hc64 & CWFs & _). pose proof (cf_arr _ CWFs) as Rarrs.
      destruct (blk_range C A m md (Z_to_bv 64 (p_cmap vs)) 24 CK HW Lcms ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia.
      pose proof (O23LeptPixCopyGC.cmap_sz_ne cvs CMOKs) as SZs.
      destruct (NEss ltac:(lia)) as [NEs1 NEs2].
      assert (NWcc : Z_to_bv 64 (p_cmap vs) <> Z_to_bv 64 cmd) by (apply O23LeptPixCopyGC.zbv_ne2; lia).
      assert (NWca : Z_to_bv 64 (p_cmap vs) <> Z_to_bv 64 arrd) by (intros E; rewrite E, Larrd in Lcms; injection Lcms as Ej; lia).
      assert (NWac : Z_to_bv 64 (c_arr cvs) <> Z_to_bv 64 cmd) by (intros E; rewrite E, Lcmd in Larrs; injection Larrs as Ej; lia).
      assert (NWaa : Z_to_bv 64 (c_arr cvs) <> Z_to_bv 64 arrd) by (apply O23LeptPixCopyGC.zbv_ne2; lia).
      assert (NXc : ~ X (Z_to_bv 64 (p_cmap vs))).
      { unfold X, O23LeptPixCopyGC.Xcm. intros [E | (_ & [E | E])]; [rewrite E, Lpd in Lcms; discriminate | exact (NWcc E) | exact (NWca E)]. }
      split; [| split; [exact CMOKs | split; [rewrite (LEQa _ NWcc NWca); exact Lcms | rewrite (LEQa _ NWac NWaa); exact Larrs]]].
      apply (CMAPat_frame m); [exact CMs |]. intros x Hx. exact (O23LeptPixCopyGC.KP_at A X m Mb (p_cmap vs) 24 x KPb Lcms NXc ltac:(lia) ltac:(lia) Hx). }
    assert (RR3 : forall x, In x cs_rest -> getr r3 x = getr regs x) by rest_solve.
    assert (B2 : getr r3 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (Hrmb : aroom A1 (m_vmmaps (with_vmmaps vm1 md)) kR bR).
    { rewrite with_vmmaps_vmmaps. pose proof (RB_cmapT_le (p_cmap vs)).
      pose proof (HRTa kR bR Hrm ltac:(room_consts; lia) ltac:(lia)) as R. rewrite !Z.sub_0_r in R. exact R. }
    apply (pcmg_tail_W C A A1 m Mb md (with_vmmaps vm1 md) regs r3 X s pixd pixs (set_cmap vd 0%Z) vs cvs ret S CK HW HWb PMb KPb
             LXd Xpd Lpd Hs16 Hlo Hhi Hret CEb PXdb ltac:(reflexivity) PXsb NEds Lpd1 Lpd00 Lps1 HCMb B2 B8 B10 RR3 H2 H4 kR bR Hrmb Hrk Hrb).
    intros A2 m2 vm2 r4 cd HW2 CS2 R10 PM2 KP2 PXd2 PXs2 DISJ Hrm2.
    rewrite with_vmmaps_twice in HW2 |- *.
    destruct (O23LeptPixCopyGC.pcg_live_of C A A1 A2 m2 (p_cmap vs) cvs cmd arrd cd
                ltac:(intros q N; destruct (N ltac:(lia)) as [N1 N2]; exact (LEQa q N1 N2)) ltac:(intros _; split; assumption) DISJ) as (cvd' & PCG & LV).
    replace (set_cmap (set_cmap vd 0%Z) cd) with (set_cmap vd cd) in PXd2 by (destruct vd; reflexivity).
    exact (HK A2 m2 vm2 r4 cd cvd' HW2 CS2 PM2 KP2 PXd2 PXs2 LV PCG Hrm2).
Qed.

End PixCopyGC.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
