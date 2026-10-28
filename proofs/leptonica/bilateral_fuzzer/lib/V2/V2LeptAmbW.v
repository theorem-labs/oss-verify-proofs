(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2LeptAmbW.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr V2LeptPixHdr V2LeptPixCreate V2LeptCmap2 V2LeptPixCopy V2LeptGrayA V2LeptRop_iface V2LeptRop2_iface V2LeptRop2N V2LeptRop2 V2LeptBord_iface V2LeptBordW V2LeptAmbSegs V2LeptBl_iface.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoomBL LeptRop2Arith.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Section AmbW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Let ROPS : pixRasterop_src2_contract := pixRasterop_src2_W.
Let ROPN : pixRasterop_null_contract := pixRasterop_null_W.
Let ABG : pixAddBorderGeneral2_contract := pixAddBorderGeneral2_W.

(* [comment removed for export] *)
Definition armI (isnull : bool) (C : lctx) (A A1 : AS) (m : word -> option byte) (pixd Wd Hd data : Z) : Prop :=
  if isnull then pixd = 0%Z /\ (forall q, live A1 q = live A q)
  else hdr_ok Wd Hd 8 /\ pix_fresh C A A1 m pixd Wd Hd 8 data.

Lemma armI_sub : forall isnull C A A1 m pixd Wd Hd data, armI isnull C A A1 m pixd Wd Hd data -> sub_live A A1.
Proof.
  intros isnull C A A1 m pixd Wd Hd data H. unfold armI in H. destruct isnull.
  - destruct H as [_ HL]. apply sub_live_eq. exact HL.
  - destruct H as [_ HF]. exact (pix_fresh_sub _ _ _ _ _ _ _ _ _ HF).
Qed.

(* [comment removed for export] *)
Lemma armI_frame : forall isnull C A A1 m m' pixd Wd Hd data, armI isnull C A A1 m pixd Wd Hd data ->
  (forall x : word, (pixd <= u x < pixd + 64)%Z -> m' x = m x) -> armI isnull C A A1 m' pixd Wd Hd data.
Proof.
  intros isnull C A A1 m m' pixd Wd Hd data H Hfr. unfold armI in *. destruct isnull; [exact H|].
  destruct H as [Hh HF]. split; [exact Hh|].
  unfold pix_fresh in *.
  destruct HF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & PX).
  do 14 (split; [assumption|]). eapply PIXat_frame; [exact PX | exact Hfr].
Qed.

(* [comment removed for export] *)
Lemma armI_blk : forall isnull C A A1 m md pixd Wd Hd data, Cok C -> W C A1 m md -> armI isnull C A A1 m pixd Wd Hd data ->
  isnull = false -> (4096 <= pixd)%Z /\ (pixd + 64 <= alloc_top (c_vm C))%Z /\ live A1 (Z_to_bv 64 pixd) = Some 64%Z.
Proof.
  intros isnull C A A1 m md pixd Wd Hd data HC HW H Hn. subst isnull. unfold armI in H.
  destruct H as [_ (G1 & G2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & G12 & _)].
  split; [exact G1 | split; [exact G2 | exact G12]].
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma am_col_arm : forall x sx j Wd, (0 <= x)%Z -> (0 <= sx)%Z -> (sx + 1 <= Wd)%Z -> (0 <= j)%Z ->
  (x = sx + 2 * j + 1 \/ sx = x + 2 * j + 1)%Z -> rop2_arm (x * 8) (sx * 8) (1 * 8) (wpl_of Wd 8).
Proof.
  intros x sx j Wd Hx Hsx HW Hj Hd.
  assert (NE : ((x * 8) mod 32 <> (sx * 8) mod 32)%Z) by lia.
  right. split; [exact NE |].
  eapply Z.le_trans; [apply g_smax_col8; lia |].
  unfold wpl_of. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma am_col_W : forall (isnull : bool) C A A1 m md regs (s' pixd Wd Hd data x y sx hgt j : Z) (lnk : word) (S : TSet),
  Cok C -> W C A1 m md ->
  getr regs 2 = Z_to_bv 64 s' -> (s' mod 16 = 0)%Z -> (c_top C - LSTK + ROP_STACK <= s')%Z -> (c_top C - LSTK + ROPN_STACK <= s')%Z -> (s' + 8 <= c_top C)%Z ->
  getr regs 1 = lnk -> ret_ok lnk ->
  getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 x -> getr regs 12 = Z_to_bv 64 y -> getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 hgt -> getr regs 15 = Z_to_bv 64 12 -> getr regs 16 = Z_to_bv 64 pixd -> getr regs 17 = Z_to_bv 64 sx ->
  rdn SEGS m (Z_to_bv 64 s') 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 y)) ->
  armI isnull C A A1 m pixd Wd Hd data -> (1 <= Wd)%Z -> (1 <= Hd)%Z ->
  (0 <= x)%Z -> (x + 1 <= Wd)%Z -> (0 <= sx)%Z -> (sx + 1 <= Wd)%Z -> (0 <= y)%Z -> (1 <= hgt)%Z -> (y + hgt <= Hd)%Z ->
  (0 <= j)%Z -> (x = sx + 2 * j + 1 \/ sx = x + 2 * j + 1)%Z ->
  (forall m' regs', W C A1 m' md -> cs_kept regs regs' -> POSTM C A s' m m' -> armI isnull C A A1 m' pixd Wd Hd data ->
      realizes SEGS (mkCfg (mkst regs' lnk m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixRasterop) m al_rom) md) S.
Proof.
  intros isnull C A A1 m md regs s' pixd Wd Hd data x y sx hgt j lnk S CK HW H2 Hal Hlo Hlo' Hhi H1 Hret
    H10 H11 H12 H13 H14 H15 H16 H17 Ry AI HWd HHd Hx Hx' Hsx Hsx' Hy Hh Hy' Hj Hdj HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  destruct isnull; cbn [armI] in AI.
  - destruct AI as [-> LV].
    assert (SUB : sub_live A A1) by (intros q k Hq; rewrite LV; exact Hq).
    apply (ROPN C A1 m md regs s' lnk S CK HW H2 Hal Hlo' ltac:(lia) H1 Hret H10).
    intros m' regs' HW' CS FR MG R10.
    apply HK; [exact HW' | exact CS | | cbn [armI]; split; [reflexivity | exact LV]].
    apply (POSTM_sub C A A1 s' m m' SUB).
    apply (POSTM_range C A1 m md m' (c_top C - LSTK) s' s' CK HW); [| lia | lia | lia].
    intros a Ha. apply FR. exact Ha.
  - destruct AI as [HOK PF].
    pose proof PF as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & LEQ & PXd).
    assert (SUB : sub_live A A1) by (eapply pix_fresh_sub; exact PF).
    assert (Hwh : (0 <= wpl_of Wd 8 * Hd)%Z) by (apply Z.mul_nonneg_nonneg; [unfold wpl_of; apply Z.div_pos | ]; lia).
    assert (NEpdw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
    apply (ROPS C A A1 m md regs s' pixd x y 1%Z hgt pixd sx y (hdv Wd Hd 8 0 data) (hdv Wd Hd 8 0 data) lnk S CK HW SUB
             H2 Hal Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Ry PXd PXd eq_refl
             (hdr_rop_shape8 Wd Hd HOK HWd HHd) (hdr_rop_shape8 Wd Hd HOK HWd HHd)
             ltac:(cbn [hdv p_w p_h]; unfold rop_rect; lia) ltac:(cbn [hdv p_w p_h]; unfold rop_rect; lia)
             (am_col_arm x sx j Wd Hx Hsx Hsx' Hj Hdj)
             L1p L1p NEpdw NEpdw L1d L0d L00d L1d).
    intros m' regs' HW' CS PM PXd' _ _.
    apply HK; [exact HW' | exact CS | exact PM |].
    cbn [armI]. split; [exact HOK |]. unfold pix_fresh. repeat (split; [assumption |]). exact PXd'.
Qed.

(* [comment removed for export] *)
Lemma am_row_W : forall (isnull : bool) C A A1 m md regs (s' pixd Wd Hd data y sy : Z) (lnk : word) (S : TSet),
  Cok C -> W C A1 m md ->
  getr regs 2 = Z_to_bv 64 s' -> (s' mod 16 = 0)%Z -> (c_top C - LSTK + ROP_STACK <= s')%Z -> (c_top C - LSTK + ROPN_STACK <= s')%Z -> (s' + 8 <= c_top C)%Z ->
  getr regs 1 = lnk -> ret_ok lnk ->
  getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 y -> getr regs 13 = Z_to_bv 64 Wd ->
  getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 12 -> getr regs 16 = Z_to_bv 64 pixd -> getr regs 17 = Z_to_bv 64 0 ->
  rdn SEGS m (Z_to_bv 64 s') 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)) ->
  armI isnull C A A1 m pixd Wd Hd data -> (1 <= Wd)%Z -> (1 <= Hd)%Z ->
  (0 <= y)%Z -> (y + 1 <= Hd)%Z -> (0 <= sy)%Z -> (sy + 1 <= Hd)%Z ->
  (forall m' regs', W C A1 m' md -> cs_kept regs regs' -> POSTM C A s' m m' -> armI isnull C A A1 m' pixd Wd Hd data ->
      realizes SEGS (mkCfg (mkst regs' lnk m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixRasterop) m al_rom) md) S.
Proof.
  intros isnull C A A1 m md regs s' pixd Wd Hd data y sy lnk S CK HW H2 Hal Hlo Hlo' Hhi H1 Hret
    H10 H11 H12 H13 H14 H15 H16 H17 Rsy AI HWd HHd Hy Hy' Hsy Hsy' HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  destruct isnull; cbn [armI] in AI.
  - destruct AI as [-> LV].
    assert (SUB : sub_live A A1) by (intros q k Hq; rewrite LV; exact Hq).
    apply (ROPN C A1 m md regs s' lnk S CK HW H2 Hal Hlo' ltac:(lia) H1 Hret H10).
    intros m' regs' HW' CS FR MG R10.
    apply HK; [exact HW' | exact CS | | cbn [armI]; split; [reflexivity | exact LV]].
    apply (POSTM_sub C A A1 s' m m' SUB).
    apply (POSTM_range C A1 m md m' (c_top C - LSTK) s' s' CK HW); [| lia | lia | lia].
    intros a Ha. apply FR. exact Ha.
  - destruct AI as [HOK PF].
    pose proof PF as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & LEQ & PXd).
    assert (SUB : sub_live A A1) by (eapply pix_fresh_sub; exact PF).
    assert (Hwh : (0 <= wpl_of Wd 8 * Hd)%Z) by (apply Z.mul_nonneg_nonneg; [unfold wpl_of; apply Z.div_pos | ]; lia).
    assert (NEpdw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
    apply (ROPS C A A1 m md regs s' pixd 0%Z y Wd 1%Z pixd 0%Z sy (hdv Wd Hd 8 0 data) (hdv Wd Hd 8 0 data) lnk S CK HW SUB
             H2 Hal Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rsy PXd PXd eq_refl
             (hdr_rop_shape8 Wd Hd HOK HWd HHd) (hdr_rop_shape8 Wd Hd HOK HWd HHd)
             ltac:(cbn [hdv p_w p_h]; unfold rop_rect; lia) ltac:(cbn [hdv p_w p_h]; unfold rop_rect; lia)
             ltac:(cbn [hdv p_d p_wpl]; left; split; reflexivity)
             L1p L1p NEpdw NEpdw L1d L0d L00d L1d).
    intros m' regs' HW' CS PM PXd' _ _.
    apply HK; [exact HW' | exact CS | exact PM |].
    cbn [armI]. split; [exact HOK |]. unfold pix_fresh. repeat (split; [assumption |]). exact PXd'.
Qed.

(* [comment removed for export] *)
Lemma armI_below : forall isnull C A A1 m md pixd Wd Hd data, Cok C -> W C A1 m md -> armI isnull C A A1 m pixd Wd Hd data ->
  (0 <= pixd)%Z /\ (pixd + 64 <= c_top C - LSTK)%Z.
Proof.
  intros isnull C A A1 m md pixd Wd Hd data HC HW H.
  destruct HC as [Htop _ _ _ Himg].
  assert (Hpos : (0 <= snd ll_img)%Z) by (apply Z.leb_le; vm_compute; reflexivity).
  unfold armI in H. destruct isnull.
  - destruct H as [Hp _]. subst pixd. lia.
  - destruct H as [_ (G1 & G2 & _)]. lia.
Qed.

Ltac am_cs6 := let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; unfold CS6 in Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]); destruct Hx.

(* [comment removed for export] *)
Lemma am_loop1_W : forall (n : nat) (isnull : bool) C A A1 (m0 m : word -> option byte) md regs (rr : bvmap 5 word)
    (s pixd Wd Hd data w h l r t b j : Z) (ret : word) (S : TSet),
  Z.of_nat n = (l - j)%Z -> (0 <= j < l)%Z -> amb_dims w h l r t b Wd Hd ->
  Cok C -> W C A1 m md -> (s mod 16 = 0)%Z -> (c_top C - LSTK + AMB_STACK <= s)%Z -> (s <= c_top C)%Z ->
  armI isnull C A A1 m pixd Wd Hd data -> amfr m s ret rr w h -> POSTM C A s m0 m ->
  getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 t ->
  getr regs 21 = Z_to_bv 64 (l - 1 - j) -> getr regs 22 = Z_to_bv 64 j -> getr regs 23 = Z_to_bv 64 (-1) ->
  getr regs 8 = Z_to_bv 64 b -> getr regs 19 = Z_to_bv 64 l -> getr regs 18 = Z_to_bv 64 r ->
  (forall x, In x CS6 -> getr regs x = getr rr x) ->
  (forall m' regs', W C A1 m' md -> armI isnull C A A1 m' pixd Wd Hd data -> amfr m' s ret rr w h -> POSTM C A s m0 m' ->
     getr regs' 2 = Z_to_bv 64 (s - 96) -> getr regs' 20 = Z_to_bv 64 pixd -> getr regs' 9 = Z_to_bv 64 t ->
     getr regs' 8 = Z_to_bv 64 b -> getr regs' 19 = Z_to_bv 64 l -> getr regs' 18 = Z_to_bv 64 r ->
     (forall x, In x CS6 -> getr regs' x = getr rr x) ->
     realizes SEGS (mkCfg (mkst regs' (Z_to_bv 64 AM_X1) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 AM_H1) m al_rom) md) S.
Proof.
  intros n. induction n as [|n IH];
    intros isnull C A A1 m0 m md regs rr s pixd Wd Hd data w h l r t b j ret S
      Hn Hj AD CK HW Hs16 Hlo Hhi AI FR PM H2 H20 H9 H21 H22 H23 H8 H19 H18 HCS HK.
  { cbn in Hn. lia. }
  rewrite Nat2Z.inj_succ in Hn.
  pose proof AD as (Dw & Dh & Dl & Dr & Dt & Db & Dlw & Drw & Dth & Dbh & EWd & EHd).
  pose proof CK as [T1 T2 T3 T4 T5].
  pose proof (armI_below _ _ _ _ _ _ _ _ _ _ CK HW AI) as [Bp0 Bp64].
  pose proof (armI_sub _ _ _ _ _ _ _ _ _ AI) as SUB.
  unfold AMB_STACK, LSF in Hlo.
  pose proof FR as (_ & _ & Rh).
  assert (Hs16' : ((s - 96) mod 16 = 0)%Z) by (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity).
  destruct (am_L1 al_rom regs m s pixd t h (l - 1 - j) l j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Rh
              (W_sok_win C A1 m md (s - 96) 8 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H20 H9 H21 H19 H22)
    as (r1 & RUN1 & a2 & a1 & a10 & a11 & a12 & a13 & a14 & a15 & a16 & a17 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. clear RUN1.
  set (m1 := wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 t))).
  assert (WP1 : W C A1 m1 md /\ POSTM C A s m0 m1) by (subst m1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (OUT1 : forall x : word, ~ (s - 96 <= u x < s - 88)%Z -> m1 x = m x).
  { intros x Hx. subst m1. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  pose proof (amfr_out m m1 (s - 96) (s - 88) s ret rr w h OUT1 ltac:(lia) ltac:(lia) ltac:(lia) FR) as FR1.
  assert (AI1 : armI isnull C A A1 m1 pixd Wd Hd data) by (apply (armI_frame _ _ _ _ m); [exact AI | intros x Hx; apply OUT1; lia]).
  apply (am_col_W isnull C A A1 m1 md r1 (s - 96) pixd Wd Hd data (l - 1 - j) t (l + j) h j (Z_to_bv 64 AM_R1) S CK HW1
           a2 Hs16' ltac:(unfold ROP_STACK; lia) ltac:(unfold ROPN_STACK, LSF; lia) ltac:(lia)
           a1 ltac:(red; apply bv_eq; reflexivity) a10 a11 a12 a13 a14 a15 a16 a17
           ltac:(subst m1; apply (rdn_wbytes_hit8 SEGS); rewrite u_Z2bv by lia; lia)
           AI1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  intros m' r' HW' CSK PM' AI'.
  pose proof (amfr_frm C (s - 96) m1 m' s ret rr w h CK (proj1 PM') ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FR1) as FR'.
  assert (PO' : POSTM C A s m0 m') by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PM']; lia]).
  destruct (Z.eq_dec (l - 1 - j) 0) as [E0|E0].
  - destruct (am_N1 al_rom true r' m' (l - 1 - j) j ltac:(lia) ltac:(lia) E0
                ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
      as (r2 & RUN2 & e21 & e22 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN2 |]. clear RUN2.
    apply (HK m' r2 HW' AI' FR' PO'); try (csr; reflexivity).
    am_cs6.
  - assert (P0 : (0 < l - 1 - j)%Z) by lia.
    destruct (am_N1 al_rom false r' m' (l - 1 - j) j ltac:(lia) ltac:(lia) P0
                ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
      as (r2 & RUN2 & e21 & e22 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN2 |]. clear RUN2.
    apply (IH isnull C A A1 m0 m' md r2 rr s pixd Wd Hd data w h l r t b (j + 1)%Z ret S
             ltac:(lia) ltac:(lia) AD CK HW' Hs16 Hlo Hhi AI' FR' PO'); try (csr; reflexivity).
    all: first [ exact HK | am_cs6 | (rewrite e21; f_equal; lia) ].
Qed.

Lemma amw_cok : forall C, Cok C -> (8192 <= c_top C - LSTK)%Z /\ (c_top C < 2 ^ 63)%Z.
Proof.
  intros C CK. assert (Hpos : (0 <= snd ll_img)%Z) by (apply Z.leb_le; vm_compute; reflexivity).
  destruct CK as [T1 T2 T3 T4 T5]. lia.
Qed.

Ltac amw_cs6 HCS :=
  let x := fresh "x" in let Hx := fresh "Hx" in let E0 := fresh "E0" in
  intros x Hx; pose proof (HCS x Hx) as E0; unfold CS6 in Hx; cbn [In] in Hx;
  repeat destruct Hx as [<- | Hx]; first [contradiction | (csr; reflexivity)].

(* [comment removed for export] *)
Lemma am_loop2_W : forall (n : nat) (isnull : bool) C A A1 (m0 m : word -> option byte) md regs (rr : bvmap 5 word)
    (s pixd Wd Hd data w h l r t b j : Z) (ret : word) (S : TSet),
  Z.of_nat n = (r - j)%Z -> (0 <= j < r)%Z -> amb_dims w h l r t b Wd Hd ->
  Cok C -> W C A1 m md -> (s mod 16 = 0)%Z -> (c_top C - LSTK + AMB_STACK <= s)%Z -> (s <= c_top C)%Z ->
  armI isnull C A A1 m pixd Wd Hd data -> amfr m s ret rr w h -> POSTM C A s m0 m ->
  getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 t ->
  getr regs 21 = Z_to_bv 64 j ->
  getr regs 8 = Z_to_bv 64 b -> getr regs 19 = Z_to_bv 64 l -> getr regs 18 = Z_to_bv 64 r ->
  (forall x, In x CS6 -> getr regs x = getr rr x) ->
  (forall m' regs', W C A1 m' md -> armI isnull C A A1 m' pixd Wd Hd data -> amfr m' s ret rr w h -> POSTM C A s m0 m' ->
     getr regs' 2 = Z_to_bv 64 (s - 96) -> getr regs' 20 = Z_to_bv 64 pixd -> getr regs' 9 = Z_to_bv 64 t ->
     getr regs' 8 = Z_to_bv 64 b -> getr regs' 19 = Z_to_bv 64 l -> getr regs' 18 = Z_to_bv 64 r ->
     (forall x, In x CS6 -> getr regs' x = getr rr x) ->
     realizes SEGS (mkCfg (mkst regs' (Z_to_bv 64 AM_X2) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 AM_H2) m al_rom) md) S.
Proof.
  induction n as [|n IH]; intros isnull C A A1 m0 m md regs rr s pixd Wd Hd data w h l r t b j ret S
    Hn Hj HD CK HW Hs16 Hlo Hhi HI FR PM H2 H20 H9 H21 H8 H19 H18 HCS HK.
  { cbn [Z.of_nat] in Hn. lia. }
  rewrite Nat2Z.inj_succ in Hn.
  pose proof HD as HD'. unfold amb_dims in HD'. destruct HD' as (Dw & Dh & Dl & Dr & Dt & Db & Dlw & Drw & Dth & Dbh & EWd & EHd).
  pose proof (amw_cok C CK) as [Ct1 Ct2].
  pose proof (armI_below isnull C A A1 m md pixd Wd Hd data CK HW HI) as [Pb1 Pb2].
  pose proof (armI_sub isnull C A A1 m pixd Wd Hd data HI) as SUB.
  pose proof Hlo as Hlo0. unfold AMB_STACK, LSF in Hlo0.
  pose proof FR as FR'. unfold amfr in FR'. destruct FR' as (FRc & FRw & FRh).
  assert (Hs16' : ((s - 96) mod 16 = 0)%Z) by (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity).
  assert (Hrop : (c_top C - LSTK + ROP_STACK <= s - 96)%Z) by (unfold ROP_STACK; lia).
  assert (Hropn : (c_top C - LSTK + ROPN_STACK <= s - 96)%Z) by (unfold ROPN_STACK, LSF; lia).
  destruct (am_L2 al_rom regs m s pixd t w h l j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              FRw FRh (W_sok_win C A1 m md (s - 96) 8 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H20 H9 H19 H21)
    as (r1 & RUN1 & e2 & e1 & e10 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. clear RUN1.
  set (M1 := wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 t))).
  assert (WP1 : W C A1 M1 md /\ POSTM C A s m0 M1) by (unfold M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (OUT1 : forall x : word, ~ (s - 96 <= u x < s - 88)%Z -> M1 x = m x).
  { intros x Hx. unfold M1. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  pose proof (amfr_out m M1 (s - 96) (s - 88) s ret rr w h OUT1 ltac:(lia) ltac:(lia) ltac:(lia) FR) as FR1.
  pose proof (armI_frame isnull C A A1 m M1 pixd Wd Hd data HI (fun x Hx => OUT1 x ltac:(lia))) as HI1.
  refine (am_col_W isnull C A A1 M1 md r1 (s - 96) pixd Wd Hd data (l + w + j) t (l + w - 1 - j) h j (Z_to_bv 64 AM_R2) S CK HW1
           e2 Hs16' Hrop Hropn ltac:(lia) e1 ltac:(red; apply bv_eq; reflexivity) e10 e11 e12 e13 e14 e15 e16 e17
           ltac:(unfold M1; apply (rdn_wbytes_hit8 SEGS); rewrite u_Z2bv by lia; lia)
           HI1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) _).
  intros m2 r2 HW2 CS2 PN2 HI2.
  pose proof (amfr_frm C (s - 96) M1 m2 s ret rr w h CK (proj1 PN2) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FR1) as FR2.
  assert (PO2 : POSTM C A s m0 m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PN2]; lia]).
  assert (f21 : getr r2 21 = Z_to_bv 64 j) by (csr; reflexivity).
  assert (f18 : getr r2 18 = Z_to_bv 64 r) by (csr; reflexivity).
  destruct (Z.eq_dec (j + 1) r) as [Elast | Nlast].
  - destruct (am_N2 al_rom true r2 m2 j r ltac:(lia) ltac:(lia) Elast f21 f18) as (r3 & RUN3 & g21 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |]. clear RUN3.
    apply (HK m2 r3 HW2 HI2 FR2 PO2); try (csr; reflexivity).
    amw_cs6 HCS.
  - destruct (am_N2 al_rom false r2 m2 j r ltac:(lia) ltac:(lia) ltac:(simpl; lia) f21 f18) as (r3 & RUN3 & g21 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |]. clear RUN3.
    apply (IH isnull C A A1 m0 m2 md r3 rr s pixd Wd Hd data w h l r t b (j + 1)%Z ret S); try (csr; reflexivity); try assumption; try lia.
    amw_cs6 HCS.
Qed.

(* [comment removed for export] *)
Lemma am_loop3_W : forall (n : nat) (isnull : bool) C A A1 (m0 m : word -> option byte) md regs (rr : bvmap 5 word)
    (s pixd Wd Hd data w h l r t b i : Z) (ret : word) (S : TSet),
  Z.of_nat n = (t - i)%Z -> (0 <= i < t)%Z -> amb_dims w h l r t b Wd Hd ->
  Cok C -> W C A1 m md -> (s mod 16 = 0)%Z -> (c_top C - LSTK + AMB_STACK <= s)%Z -> (s <= c_top C)%Z ->
  armI isnull C A A1 m pixd Wd Hd data -> amfr m s ret rr w h -> POSTM C A s m0 m ->
  getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 t ->
  getr regs 21 = Z_to_bv 64 (t - 1 - i) -> getr regs 22 = Z_to_bv 64 i -> getr regs 23 = Z_to_bv 64 (-1) ->
  getr regs 8 = Z_to_bv 64 b -> getr regs 19 = Z_to_bv 64 l -> getr regs 18 = Z_to_bv 64 r ->
  (forall x, In x CS6 -> getr regs x = getr rr x) ->
  (forall m' regs', W C A1 m' md -> armI isnull C A A1 m' pixd Wd Hd data -> amfr m' s ret rr w h -> POSTM C A s m0 m' ->
     getr regs' 2 = Z_to_bv 64 (s - 96) -> getr regs' 20 = Z_to_bv 64 pixd -> getr regs' 9 = Z_to_bv 64 t ->
     getr regs' 8 = Z_to_bv 64 b -> getr regs' 19 = Z_to_bv 64 l -> getr regs' 18 = Z_to_bv 64 r ->
     (forall x, In x CS6 -> getr regs' x = getr rr x) ->
     realizes SEGS (mkCfg (mkst regs' (Z_to_bv 64 AM_X3) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 AM_H3) m al_rom) md) S.
Proof.
  intros n. induction n as [|n IH];
    intros isnull C A A1 m0 m md regs rr s pixd Wd Hd data w h l r t b i ret S
      Hn Hi AD CK HW Hs16 Hlo Hhi AI FR PM H2 H20 H9 H21 H22 H23 H8 H19 H18 HCS HK.
  { cbn in Hn. lia. }
  rewrite Nat2Z.inj_succ in Hn.
  pose proof AD as (Dw & Dh & Dl & Dr & Dt & Db & Dlw & Drw & Dth & Dbh & EWd & EHd).
  pose proof CK as [T1 T2 T3 T4 T5].
  pose proof (armI_below _ _ _ _ _ _ _ _ _ _ CK HW AI) as [Bp0 Bp64].
  pose proof (armI_sub _ _ _ _ _ _ _ _ _ AI) as SUB.
  unfold AMB_STACK, LSF in Hlo.
  pose proof FR as (_ & Rw & _).
  assert (Hs16' : ((s - 96) mod 16 = 0)%Z) by (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity).
  destruct (am_L3 al_rom regs m s pixd t w l r (t - 1 - i) i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(lia) ltac:(lia) ltac:(lia) Rw
              (W_sok_win C A1 m md (s - 96) 8 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H20 H9 H19 H18 H21 H22)
    as (r1 & RUN1 & a2 & a1 & a10 & a11 & a12 & a13 & a14 & a15 & a16 & a17 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. clear RUN1.
  set (m1 := wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 (t + i)))).
  assert (WP1 : W C A1 m1 md /\ POSTM C A s m0 m1) by (subst m1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (OUT1 : forall x : word, ~ (s - 96 <= u x < s - 88)%Z -> m1 x = m x).
  { intros x Hx. subst m1. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  pose proof (amfr_out m m1 (s - 96) (s - 88) s ret rr w h OUT1 ltac:(lia) ltac:(lia) ltac:(lia) FR) as FR1.
  assert (AI1 : armI isnull C A A1 m1 pixd Wd Hd data) by (apply (armI_frame _ _ _ _ m); [exact AI | intros x Hx; apply OUT1; lia]).
  apply (am_row_W isnull C A A1 m1 md r1 (s - 96) pixd Wd Hd data (t - 1 - i) (t + i)%Z (Z_to_bv 64 AM_R3) S CK HW1
           a2 Hs16' ltac:(unfold ROP_STACK; lia) ltac:(unfold ROPN_STACK, LSF; lia) ltac:(lia)
           a1 ltac:(red; apply bv_eq; reflexivity) a10 a11 a12 ltac:(rewrite a13; f_equal; lia) a14 a15 a16 a17
           ltac:(subst m1; apply (rdn_wbytes_hit8 SEGS); rewrite u_Z2bv by lia; lia)
           AI1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  intros m' r' HW' CSK PM' AI'.
  pose proof (amfr_frm C (s - 96) m1 m' s ret rr w h CK (proj1 PM') ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FR1) as FR'.
  assert (PO' : POSTM C A s m0 m') by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PM']; lia]).
  destruct (Z.eq_dec (t - 1 - i) 0) as [E0|E0].
  - destruct (am_N3 al_rom true r' m' (t - 1 - i) i ltac:(lia) ltac:(lia) E0
                ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
      as (r2 & RUN2 & e21 & e22 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN2 |]. clear RUN2.
    apply (HK m' r2 HW' AI' FR' PO'); try (csr; reflexivity).
    am_cs6.
  - assert (P0 : (0 < t - 1 - i)%Z) by lia.
    destruct (am_N3 al_rom false r' m' (t - 1 - i) i ltac:(lia) ltac:(lia) P0
                ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
      as (r2 & RUN2 & e21 & e22 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN2 |]. clear RUN2.
    apply (IH isnull C A A1 m0 m' md r2 rr s pixd Wd Hd data w h l r t b (i + 1)%Z ret S
             ltac:(lia) ltac:(lia) AD CK HW' Hs16 Hlo Hhi AI' FR' PO'); try (csr; reflexivity).
    all: first [ exact HK | am_cs6 | (rewrite e21; f_equal; lia) ].
Qed.

(* [comment removed for export] *)
Lemma am_loop4_W : forall (n : nat) (isnull : bool) C A A1 (m0 m : word -> option byte) md regs (rr : bvmap 5 word)
    (s pixd Wd Hd data w h l r t b i : Z) (ret : word) (S : TSet),
  Z.of_nat n = (b - i)%Z -> (0 <= i < b)%Z -> amb_dims w h l r t b Wd Hd ->
  Cok C -> W C A1 m md -> (s mod 16 = 0)%Z -> (c_top C - LSTK + AMB_STACK <= s)%Z -> (s <= c_top C)%Z ->
  armI isnull C A A1 m pixd Wd Hd data -> amfr m s ret rr w h -> POSTM C A s m0 m ->
  getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 t ->
  getr regs 21 = Z_to_bv 64 i ->
  getr regs 8 = Z_to_bv 64 b -> getr regs 19 = Z_to_bv 64 l -> getr regs 18 = Z_to_bv 64 r ->
  (forall x, In x CS6 -> getr regs x = getr rr x) ->
  (forall m' regs', W C A1 m' md -> armI isnull C A A1 m' pixd Wd Hd data -> amfr m' s ret rr w h -> POSTM C A s m0 m' ->
     getr regs' 2 = Z_to_bv 64 (s - 96) -> getr regs' 20 = Z_to_bv 64 pixd ->
     (forall x, In x CS6 -> getr regs' x = getr rr x) ->
     realizes SEGS (mkCfg (mkst regs' (Z_to_bv 64 AM_X4) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 AM_H4) m al_rom) md) S.
Proof.
  induction n as [|n IH]; intros isnull C A A1 m0 m md regs rr s pixd Wd Hd data w h l r t b i ret S
    Hn Hi HD CK HW Hs16 Hlo Hhi HI FR PM H2 H20 H9 H21 H8 H19 H18 HCS HK.
  { cbn [Z.of_nat] in Hn. lia. }
  rewrite Nat2Z.inj_succ in Hn.
  pose proof HD as HD'. unfold amb_dims in HD'. destruct HD' as (Dw & Dh & Dl & Dr & Dt & Db & Dlw & Drw & Dth & Dbh & EWd & EHd).
  pose proof (amw_cok C CK) as [Ct1 Ct2].
  pose proof (armI_below isnull C A A1 m md pixd Wd Hd data CK HW HI) as [Pb1 Pb2].
  pose proof (armI_sub isnull C A A1 m pixd Wd Hd data HI) as SUB.
  pose proof Hlo as Hlo0. unfold AMB_STACK, LSF in Hlo0.
  pose proof FR as FR'. unfold amfr in FR'. destruct FR' as (FRc & FRw & FRh).
  assert (Hs16' : ((s - 96) mod 16 = 0)%Z) by (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity).
  assert (Hrop : (c_top C - LSTK + ROP_STACK <= s - 96)%Z) by (unfold ROP_STACK; lia).
  assert (Hropn : (c_top C - LSTK + ROPN_STACK <= s - 96)%Z) by (unfold ROPN_STACK, LSF; lia).
  destruct (am_L4 al_rom regs m s pixd t w h l r i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(lia) ltac:(lia) ltac:(lia)
              FRw FRh (W_sok_win C A1 m md (s - 96) 8 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H20 H9 H19 H18 H21)
    as (r1 & RUN1 & e2 & e1 & e10 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. clear RUN1.
  set (M1 := wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 (t + h - 1 - i)))).
  assert (WP1 : W C A1 M1 md /\ POSTM C A s m0 M1) by (unfold M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (OUT1 : forall x : word, ~ (s - 96 <= u x < s - 88)%Z -> M1 x = m x).
  { intros x Hx. unfold M1. apply (wbytes_out_Z _ _ 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  pose proof (amfr_out m M1 (s - 96) (s - 88) s ret rr w h OUT1 ltac:(lia) ltac:(lia) ltac:(lia) FR) as FR1.
  pose proof (armI_frame isnull C A A1 m M1 pixd Wd Hd data HI (fun x Hx => OUT1 x ltac:(lia))) as HI1.
  assert (e13' : getr r1 13 = Z_to_bv 64 Wd) by (rewrite e13; f_equal; lia).
  refine (am_row_W isnull C A A1 M1 md r1 (s - 96) pixd Wd Hd data (t + h + i) (t + h - 1 - i) (Z_to_bv 64 AM_R4) S CK HW1
           e2 Hs16' Hrop Hropn ltac:(lia) e1 ltac:(red; apply bv_eq; reflexivity) e10 e11 e12 e13' e14 e15 e16 e17
           ltac:(unfold M1; apply (rdn_wbytes_hit8 SEGS); rewrite u_Z2bv by lia; lia)
           HI1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) _).
  intros m2 r2 HW2 CS2 PN2 HI2.
  pose proof (amfr_frm C (s - 96) M1 m2 s ret rr w h CK (proj1 PN2) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FR1) as FR2.
  assert (PO2 : POSTM C A s m0 m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PN2]; lia]).
  assert (f21 : getr r2 21 = Z_to_bv 64 i) by (csr; reflexivity).
  assert (f8 : getr r2 8 = Z_to_bv 64 b) by (csr; reflexivity).
  destruct (Z.eq_dec (i + 1) b) as [Elast | Nlast].
  - destruct (am_N4 al_rom true r2 m2 i b ltac:(lia) ltac:(lia) Elast f21 f8) as (r3 & RUN3 & g21 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |]. clear RUN3.
    apply (HK m2 r3 HW2 HI2 FR2 PO2); try (csr; reflexivity).
    amw_cs6 HCS.
  - destruct (am_N4 al_rom false r2 m2 i b ltac:(lia) ltac:(lia) ltac:(simpl; lia) f21 f8) as (r3 & RUN3 & g21 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |]. clear RUN3.
    apply (IH isnull C A A1 m0 m2 md r3 rr s pixd Wd Hd data w h l r t b (i + 1)%Z ret S); try (csr; reflexivity); try assumption; try lia.
    amw_cs6 HCS.
Qed.

Lemma amt_keep : forall (L : list reg) regs regs' (r : reg) (v : word),
  regs_agree (fun x => In x L) regs regs' -> existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = false ->
  getr regs r = v -> getr regs' r = v.
Proof.
  intros L regs regs' r v AG E H. rewrite AG; [exact H|]. intros Hin.
  assert (T : existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = true).
  { apply existsb_exists. exists r. split; [exact Hin | apply Z.eqb_refl]. }
  congruence.
Qed.

Lemma amt_cs : forall (L : list reg) regs regs' (rr : bvmap 5 word),
  regs_agree (fun x => In x L) regs regs' ->
  forallb (fun r => negb (existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L)) CS6 = true ->
  (forall x, In x CS6 -> getr regs x = getr rr x) -> (forall x, In x CS6 -> getr regs' x = getr rr x).
Proof.
  intros L regs regs' rr AG B H x Hx. rewrite forallb_forall in B. specialize (B x Hx). apply negb_true_iff in B.
  exact (amt_keep L regs regs' x (getr rr x) AG B (H x Hx)).
Qed.

Ltac amk AG H := apply (amt_keep _ _ _ _ _ AG); [vm_compute; reflexivity | exact H].
Ltac amc AG H := apply (amt_cs _ _ _ _ AG); [vm_compute; reflexivity | exact H].
Ltac amrz HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].

(* [comment removed for export] *)
Lemma am_tail_W : forall (isnull : bool) C A A1 (m0 m : word -> option byte) md regs (rr : bvmap 5 word)
    (s pixd Wd Hd data w h l r t b : Z) (ret : word) (S : TSet),
  amb_dims w h l r t b Wd Hd ->
  Cok C -> W C A1 m md -> (s mod 16 = 0)%Z -> (c_top C - LSTK + AMB_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  armI isnull C A A1 m pixd Wd Hd data -> amfr m s ret rr w h -> POSTM C A s m0 m ->
  getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 t ->
  getr regs 8 = Z_to_bv 64 b -> getr regs 19 = Z_to_bv 64 l -> getr regs 18 = Z_to_bv 64 r ->
  (forall x, In x CS6 -> getr regs x = getr rr x) ->
  (forall m' regs', W C A1 m' md -> armI isnull C A A1 m' pixd Wd Hd data -> POSTM C A s m0 m' ->
     getr regs' 2 = Z_to_bv 64 s -> getr regs' 1 = ret -> getr regs' 10 = Z_to_bv 64 pixd ->
     (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23]%bv -> getr regs' x = getr rr x) ->
     (forall x, In x CS6 -> getr regs' x = getr rr x) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 AM_RA) m al_rom) md) S.
Proof.
  intros isnull C A A1 m0 m md regs rr s pixd Wd Hd data w h l r t b ret S DIMS CK HW Hs16 Hlo Hhi Hret ARM AMF PM
    H2 H10 H9 H8 H19 H18 HCS HK.
  pose proof DIMS as (Dw & Dh & Dl & Dr & Dt & Db & _).
  pose proof CK as [T1 T2 T3 T4 T5].
  assert (Hpos : (0 <= snd ll_img)%Z) by (apply Z.leb_le; vm_compute; reflexivity).
  pose proof Hlo as Hlo'. unfold AMB_STACK, LSF in Hlo'.
  assert (Hs96 : (96 <= s)%Z) by lia.
  assert (Hs63 : (s < 2 ^ 63)%Z) by lia.
  destruct (am_B0 al_rom regs m pixd l ltac:(lia) H10 H19) as (r1 & RUN1 & Q20a & Q21a & Q23a & Q22a & AG1).
  amrz HW RUN1. clear RUN1.
  assert (K2a : getr r1 2 = Z_to_bv 64 (s - 96)) by (amk AG1 H2).
  assert (K9a : getr r1 9 = Z_to_bv 64 t) by (amk AG1 H9).
  assert (K8a : getr r1 8 = Z_to_bv 64 b) by (amk AG1 H8).
  assert (K19a : getr r1 19 = Z_to_bv 64 l) by (amk AG1 H19).
  assert (K18a : getr r1 18 = Z_to_bv 64 r) by (amk AG1 H18).
  assert (KCa : forall x, In x CS6 -> getr r1 x = getr rr x) by (amc AG1 HCS).
  assert (K21a : getr r1 21 = Z_to_bv 64 (l - 1 - 0)) by (rewrite Z.sub_0_r; exact Q21a).
  refine (am_loop1_W (Z.to_nat l) isnull C A A1 m0 m md r1 rr s pixd Wd Hd data w h l r t b 0 ret S
            ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia) DIMS CK HW Hs16 Hlo Hhi ARM AMF PM
            K2a Q20a K9a K21a Q22a Q23a K8a K19a K18a KCa _).
  intros m1 r2 HW1 ARM1 AMF1 PM1 G2b G20b G9b G8b G19b G18b GCb.
  destruct (am_B1 al_rom r2 m1 r ltac:(lia) G18b) as (r3 & RUN3 & Q21c & AG3).
  amrz HW1 RUN3. clear RUN3.
  assert (K2c : getr r3 2 = Z_to_bv 64 (s - 96)) by (amk AG3 G2b).
  assert (K20c : getr r3 20 = Z_to_bv 64 pixd) by (amk AG3 G20b).
  assert (K9c : getr r3 9 = Z_to_bv 64 t) by (amk AG3 G9b).
  assert (K8c : getr r3 8 = Z_to_bv 64 b) by (amk AG3 G8b).
  assert (K19c : getr r3 19 = Z_to_bv 64 l) by (amk AG3 G19b).
  assert (K18c : getr r3 18 = Z_to_bv 64 r) by (amk AG3 G18b).
  assert (KCc : forall x, In x CS6 -> getr r3 x = getr rr x) by (amc AG3 GCb).
  refine (am_loop2_W (Z.to_nat r) isnull C A A1 m0 m1 md r3 rr s pixd Wd Hd data w h l r t b 0 ret S
            ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia) DIMS CK HW1 Hs16 Hlo Hhi ARM1 AMF1 PM1
            K2c K20c K9c Q21c K8c K19c K18c KCc _).
  intros m2 r4 HW2 ARM2 AMF2 PM2 G2d G20d G9d G8d G19d G18d GCd.
  destruct (am_B2 al_rom r4 m2 t ltac:(lia) G9d) as (r5 & RUN5 & Q21e & Q23e & Q22e & AG5).
  amrz HW2 RUN5. clear RUN5.
  assert (K2e : getr r5 2 = Z_to_bv 64 (s - 96)) by (amk AG5 G2d).
  assert (K20e : getr r5 20 = Z_to_bv 64 pixd) by (amk AG5 G20d).
  assert (K9e : getr r5 9 = Z_to_bv 64 t) by (amk AG5 G9d).
  assert (K8e : getr r5 8 = Z_to_bv 64 b) by (amk AG5 G8d).
  assert (K19e : getr r5 19 = Z_to_bv 64 l) by (amk AG5 G19d).
  assert (K18e : getr r5 18 = Z_to_bv 64 r) by (amk AG5 G18d).
  assert (KCe : forall x, In x CS6 -> getr r5 x = getr rr x) by (amc AG5 GCd).
  assert (K21e : getr r5 21 = Z_to_bv 64 (t - 1 - 0)) by (rewrite Z.sub_0_r; exact Q21e).
  refine (am_loop3_W (Z.to_nat t) isnull C A A1 m0 m2 md r5 rr s pixd Wd Hd data w h l r t b 0 ret S
            ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia) DIMS CK HW2 Hs16 Hlo Hhi ARM2 AMF2 PM2
            K2e K20e K9e K21e Q22e Q23e K8e K19e K18e KCe _).
  intros m3 r6 HW3 ARM3 AMF3 PM3 G2f G20f G9f G8f G19f G18f GCf.
  destruct (am_B3 al_rom r6 m3 b ltac:(lia) G8f) as (r7 & RUN7 & Q21g & AG7).
  amrz HW3 RUN7. clear RUN7.
  assert (K2g : getr r7 2 = Z_to_bv 64 (s - 96)) by (amk AG7 G2f).
  assert (K20g : getr r7 20 = Z_to_bv 64 pixd) by (amk AG7 G20f).
  assert (K9g : getr r7 9 = Z_to_bv 64 t) by (amk AG7 G9f).
  assert (K8g : getr r7 8 = Z_to_bv 64 b) by (amk AG7 G8f).
  assert (K19g : getr r7 19 = Z_to_bv 64 l) by (amk AG7 G19f).
  assert (K18g : getr r7 18 = Z_to_bv 64 r) by (amk AG7 G18f).
  assert (KCg : forall x, In x CS6 -> getr r7 x = getr rr x) by (amc AG7 GCf).
  refine (am_loop4_W (Z.to_nat b) isnull C A A1 m0 m3 md r7 rr s pixd Wd Hd data w h l r t b 0 ret S
            ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia) DIMS CK HW3 Hs16 Hlo Hhi ARM3 AMF3 PM3
            K2g K20g K9g Q21g K8g K19g K18g KCg _).
  intros m4 r8 HW4 ARM4 AMF4 PM4 G2h G20h GCh.
  destruct (am_E al_rom r8 rr m4 s pixd ret Hs96 Hs63 Hret (proj1 AMF4) G2h G20h) as (r9 & RUN9 & E2 & E1 & E10 & E8 & AG9).
  amrz HW4 RUN9. clear RUN9.
  apply (HK m4 r9 HW4 ARM4 PM4 E2 E1 E10 E8).
  amc AG9 GCh.
Qed.

Lemma amg_v : forall v, p_d v = 8%Z -> p_cmap v = 0%Z -> p_wpl v = wpl_of (p_w v) 8 -> p_xres v = 0%Z -> p_yres v = 0%Z ->
  v = hdvg (p_w v) (p_h v) 8 (p_data v) (p_spp v) (p_rc v) (p_fmt v) (p_spec v) (p_text v).
Proof.
  intros [w h d spp wpl rc xr yr fmt spc txt cm dat]; cbn; intros Hd Hc Hw Hx Hy; subst; reflexivity.
Qed.

Lemma amg_arm : forall l w, (1 <= l)%Z -> (1 <= w)%Z -> rop2_arm (l * 8)%Z (0 * 8)%Z (w * 8)%Z (wpl_of w 8).
Proof.
  intros l w Hl Hw. unfold rop2_arm. destruct (Z.eq_dec ((l * 8) mod 32) 0) as [E|E].
  - left. split; [exact E | reflexivity].
  - right. split; [change ((0 * 8) mod 32)%Z with 0%Z; exact E|].
    pose proof (g_smax_left8 l w ltac:(lia) ltac:(lia) E) as G. unfold wpl_of. lia.
Qed.

(* [comment removed for export] *)
Theorem pixAddMirroredBorder_gen_W : forall C A m md regs (s pixs l r t b : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + AMB_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 l -> getr regs 12 = Z_to_bv 64 r -> getr regs 13 = Z_to_bv 64 t -> getr regs 14 = Z_to_bv 64 b ->
  bl_src A m pixs v -> (1 <= l <= 64)%Z -> (1 <= r <= 64)%Z -> (1 <= t <= 64)%Z -> (1 <= b <= 64)%Z ->
  (l <= p_w v)%Z -> (r <= p_w v)%Z -> (t <= p_h v)%Z -> (b <= p_h v)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix <= kR)%Z -> (RB_abg (p_w v) (p_h v) 8 l r t b <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pixd data, getr regs' 10 = Z_to_bv 64 pixd /\ hdr_ok (p_w v + l + r) (p_h v + t + b) 8 /\
                            pixr_new C A A' m' pixd data (set_data (pix_hdr (p_w v + l + r) (p_h v + t + b) 8) data))) ->
     aroom A' vm' (kR - RK_pix) (bR - RB_abg (p_w v) (p_h v) 8 l r t b) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixAddMirroredBorder) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs l r t b v ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13 H14 BL Hl Hr Ht Hb
    Hlw Hrw Hth Hbh kR bR Hrm Hrk Hrb HK.
  pose proof BL as (PXs & Hd8 & Hcm & HOK & Hw1 & Hh1 & Hwpl & Lps & Lds & Hxr & Hyr).
  pose proof HOK as (DV & Hw20 & Hh20 & Hsz).
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg].
  pose proof LSTK_val as LS.
  assert (Hpos : (0 <= snd ll_img)%Z) by (apply Z.leb_le; vm_compute; reflexivity).
  pose proof Hlo as Hlo'. unfold AMB_STACK, LSF in Hlo'.
  pose proof PXs as (Hps0 & Hps64 & WFs & _).
  pose proof (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as BRps. rewrite u_Z2bv in BRps by lia.
  pose proof (ai_live_hull _ _ _ _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  assert (Hpm8 : (pixs mod 8 = 0)%Z) by (apply mod16_mod8; exact ALps).
  assert (SOKf : store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true) by (apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia]).
  destruct (am_A al_rom regs m s pixs l r t b v ret ltac:(lia) Hs16 ltac:(lia) ltac:(lia) Hpm8 PXs ltac:(lia)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hlw Hrw Hth Hbh SOKf H2 H1 H10 H11 H12 H13 H14)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q20 & Q19 & Q18 & Q9 & Q8 & AG1).
  amrz HW RUN1. clear RUN1.
  set (M1 := O2LeptAmbSegs.DIM2 (O2LeptAmbSegs.FRM9 m s ret regs) s (p_w v) (p_h v)) in *.
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold O2LeptAmbSegs.DIM2, O2LeptAmbSegs.FRM9; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (OUT1 : forall x : word, ~ (s - 96 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold O2LeptAmbSegs.DIM2, O2LeptAmbSegs.FRM9.
    repeat (rewrite (wbytes_out_Z _ _ 4); [| rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]).
    repeat (rewrite (wbytes_out_Z _ _ 8); [| rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]).
    reflexivity. }
  assert (PXs1 : PIXat M1 pixs v) by (apply (PIXat_frame m); [exact PXs | intros x Hx; apply OUT1; lia]).
  pose proof (amfr_init m s ret regs (p_w v) (p_h v) ltac:(lia) ltac:(lia)) as FR1. fold M1 in FR1.
  pose proof (amg_v v Hd8 Hcm Hwpl Hxr Hyr) as Ev.
  assert (PXg : PIXat M1 pixs (hdvg (p_w v) (p_h v) 8 (p_data v) (p_spp v) (p_rc v) (p_fmt v) (p_spec v) (p_text v)))
    by (rewrite <- Ev; exact PXs1).
  assert (Ldg : live A (Z_to_bv 64 (p_data v)) = Some (4 * (wpl_of (p_w v) 8 * p_h v))%Z) by (rewrite <- Hwpl; exact Lds).
  assert (Q4 : getr r1 4 = Z_to_bv 64 352880) by (amk AG1 H4).
  assert (PROD : ((p_w v + l + r) * (p_h v + t + b) <= 400000000)%Z).
  { apply abg_prod_bound; try lia. apply hdr_wh_bound; try lia. unfold wpl_of in Hsz. lia. }
  apply (ABG C A M1 md r1 (s - 96)%Z pixs (p_w v) (p_h v) 8%Z (p_data v) (p_spp v) (p_rc v) (p_fmt v) (p_spec v) (p_text v)
           l r t b 0%Z (Z_to_bv 64 AM_RA) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold ABG_STACK, LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 Q13 Q14 Q15
           PXg HOK Hw1 Hh1 ltac:(right; reflexivity) Lps Ldg Hl Hr Ht Hb (amg_arm l (p_w v) ltac:(lia) Hw1)
           ltac:(left; reflexivity) PROD kR bR Hrm Hrk Hrb).
  intros A1 m1 vm1 r2 HWa CSa PMa OUTa HRTa.
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  pose proof (amfr_frm C (s - 96) M1 m1 s ret regs (p_w v) (p_h v) CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FR1) as FR2.
  assert (G2 : getr r2 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
  assert (G9 : getr r2 9 = Z_to_bv 64 t) by (csr; reflexivity).
  assert (G8 : getr r2 8 = Z_to_bv 64 b) by (csr; reflexivity).
  assert (G19 : getr r2 19 = Z_to_bv 64 l) by (csr; reflexivity).
  assert (G18 : getr r2 18 = Z_to_bv 64 r) by (csr; reflexivity).
  assert (GCS : forall x, In x CS6 -> getr r2 x = getr regs x).
  { intros x Hx. unfold CS6 in Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]). destruct Hx. }
  assert (DIMS : amb_dims (p_w v) (p_h v) l r t b (p_w v + l + r) (p_h v + t + b)) by (unfold amb_dims; lia).
  destruct OUTa as [[Hres0 LIVEQ] | (pixd & data & Hres & HOKd & PF)].
  - apply (am_tail_W true C A A1 m m1 (with_vmmaps vm1 md) r2 regs s 0 (p_w v + l + r) (p_h v + t + b) 0 (p_w v) (p_h v) l r t b ret S
             DIMS CK HWa Hs16 Hlo Hhi Hret (conj eq_refl LIVEQ) FR2 PMa' G2 Hres0 G9 G8 G19 G18 GCS).
    intros m2 r3 HW2 ARM2 PM2 E2 E1 E10 E8s ECS.
    apply (HK A1 m2 vm1 r3 HW2).
    + apply cs_kept_intro; first [ solve [rewrite E2, H2; reflexivity] | solve [apply E8s; in_lit] | solve [apply ECS; unfold CS6; in_lit] ].
    + exact PM2.
    + left. split; [exact E10 | destruct ARM2 as [_ LV]; exact LV].
    + exact HRTa.
  - apply (am_tail_W false C A A1 m m1 (with_vmmaps vm1 md) r2 regs s pixd (p_w v + l + r) (p_h v + t + b) data (p_w v) (p_h v) l r t b ret S
             DIMS CK HWa Hs16 Hlo Hhi Hret (conj HOKd PF) FR2 PMa' G2 Hres G9 G8 G19 G18 GCS).
    intros m2 r3 HW2 ARM2 PM2 E2 E1 E10 E8s ECS.
    apply (HK A1 m2 vm1 r3 HW2).
    + apply cs_kept_intro; first [ solve [rewrite E2, H2; reflexivity] | solve [apply E8s; in_lit] | solve [apply ECS; unfold CS6; in_lit] ].
    + exact PM2.
    + right. exists pixd, data. split; [exact E10|]. destruct ARM2 as [HOK2 PF2]. split; [exact HOK2|].
      destruct PF2 as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & PX).
      exact (conj F1 (conj F2 (conj F3 (conj F4 (conj F5 (conj F6 (conj F7 (conj F8 (conj F9 (conj F10 (conj F11 (conj F12
               (conj F13 (conj F14 (conj PX eq_refl))))))))))))))).
    + exact HRTa.
Qed.

(* [comment removed for export] *)
Theorem pixAddMirroredBorder_W : pixAddMirroredBorder_contract.
Proof.
  unfold pixAddMirroredBorder_contract.
  intros C A m md regs s pixs b v ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13 H14 BL Hb Hbw Hbh kR bR Hrm Hrk Hrb HK.
  assert (Ew : (p_w v + 2 * b = p_w v + b + b)%Z) by lia.
  assert (Eh : (p_h v + 2 * b = p_h v + b + b)%Z) by lia.
  assert (ERB : RB_amb (p_w v) (p_h v) b = RB_abg (p_w v) (p_h v) 8 b b b b) by (unfold RB_amb, RB_abg; rewrite Ew, Eh; reflexivity).
  rewrite ERB in Hrb.
  apply (pixAddMirroredBorder_gen_W C A m md regs s pixs b b b b v ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13 H14 BL
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hbw Hbw Hbh Hbh kR bR Hrm Hrk Hrb).
  intros A' m' vm' regs' HW' CS' PM' OUT' RM'.
  apply (HK A' m' vm' regs' HW' CS' PM').
  - rewrite Ew, Eh. exact OUT'.
  - rewrite ERB. exact RM'.
Qed.

End AmbW.
