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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptRop_iface V23LeptDilW V23LeptHmtW V23LeptMorphS V23LeptPixOr V23LeptRb2W V23LeptCascW V23LeptCountW V23LeptTextSelC V23LeptTextSelW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptUdd_iface V23LeptUddSegs V23LeptUddLib V23LeptUddT V23LeptUddB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptUddLib O23LeptUddSegs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptSelGP.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma str_udd_err : str16 0x1189d 29.
Proof. str16_tac. Qed.
Lemma str_udd_proc : str16 0x1cabf 15.
Proof. str16_tac. Qed.

(* [comment removed for export] *)
Definition RK_udd : Z := 4 * RK_selstr + RK_mseq + 2 * RK_blk.
Definition RB_udd (w h cm : Z) : Z := 4 * RB_selstr + RB_mseq w h cm + 2 * RB_blk w h.

Lemma RK_mseq_val : RK_mseq = 71%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma RK_blk_val : RK_blk = 14%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma RK_udd_nonneg : (0 <= RK_udd)%Z.
Proof. unfold RK_udd. rewrite RK_mseq_val, RK_blk_val. unfold RK_selstr. lia. Qed.
Lemma RB_blk_nonneg : forall w h, (0 <= RB_blk w h)%Z.
Proof.
  intros w h. unfold RB_blk, RB_casc, RB_cmapcopy.
  repeat match goal with |- context [RB_pixT ?n] => generalize (RB_pixT_nonneg n); generalize (RB_pixT n); intros end.
  lia.
Qed.
Lemma RB_csc_nonneg' : forall vs w h cm, (0 <= RB_csc vs w h cm)%Z.
Proof.
  intros vs w h cm. unfold RB_csc, RK_csc_sels.
  repeat match goal with |- context [RB_pixT ?n] => generalize (RB_pixT_nonneg n); generalize (RB_pixT n); intros end.
  generalize (RB_cmapT_le cm); generalize (RB_cmapT cm); intros.
  destruct (vs =? 1)%Z; lia.
Qed.
Lemma RB_mseq_nonneg : forall w h cm, (0 <= RB_mseq w h cm)%Z.
Proof.
  intros w h cm. unfold RB_mseq.
  generalize (RB_csc_nonneg' 8 w h 1) (RB_csc_nonneg' 1 w h 1) (RB_pixT_nonneg (4 * (wpl_of w 1 * h))) (RB_cmapT_le cm). lia.
Qed.
Lemma RB_udd_nonneg : forall w h cm, (0 <= RB_udd w h cm)%Z.
Proof.
  intros w h cm. unfold RB_udd, RB_selstr.
  generalize (RB_mseq_nonneg w h cm) (RB_blk_nonneg w h). lia.
Qed.
(* [comment removed for export] *)
Lemma RB_udd_le1 : forall w h cm, (RB_udd w h cm <= RB_udd w h 1)%Z.
Proof.
  intros w h cm. unfold RB_udd, RB_mseq.
  generalize (RB_cmapT_le cm) (RB_cmapT_pos 1 ltac:(lia)). lia.
Qed.

Section UddW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Instance udw_fxd : FPState | 100 := mkFP bvmap_empty (Z_to_bv 32 0).
Ltac rzs HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
Ltac mod16 Hs16 := rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity.
Ltac in_app := solve [repeat (first [assumption | apply in_or_app; first [left; assumption | right]])].
Ltac wsz := rewrite ?length_N_to_le_bytes, ?length_Z_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Ltac rk := unfold RK_udd, RB_udd, RK_selstr, RB_selstr in *.
Ltac zl := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Ltac pcto RUN E :=
  match type of RUN with msteps _ (mkst _ ?pc _ _) _ =>
    lazymatch goal with |- realizes _ (mkCfg (mkst _ ?g _ _) _) _ => replace g with pc by (rewrite E; apply bv_eq; reflexivity) end end.

(* [comment removed for export] *)
Definition mseq_udd_contract : Prop :=
  forall (fr : bvmap 5 word) (cs : bv 32) C A m md regs (s pixs w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> MBC C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + MSEQ_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 0x17f63 -> getr regs 12 = Z_to_bv 64 0 ->
  PIXat m pixs (hdv w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_mseq <= kR)%Z -> (RB_mseq w h cm <= bR)%Z ->
  (forall (fr' : bvmap 5 word) (cs' : bv 32) A' m' vm' regs' (pixd cd data : Z) (cv' : cmapv),
     frm_zero cs' -> W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> getr regs' 10 = Z_to_bv 64 pixd ->
     POSTM C A s m m' -> O23LeptUddLib.PIXC C A' m' pixd w h cd data cv' ->
     O23LeptUddLib.only A A' (O23LeptUddLib.pix_l pixd data cd (c_arr cv')) -> O23LeptUddLib.offs A (O23LeptUddLib.pix_l pixd data cd (c_arr cv')) ->
     aroom A' vm' (kR - RK_mseq) (bR - RB_mseq w h cm) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (0xa663c : word) m al_rom) md) S.

(* [comment removed for export] *)
Lemma FRM_win : forall C s' (m m' : word -> option byte) (x : word), Cok C -> FRM C s' m m' -> (c_top C - LSTK <= s')%Z -> (s' <= u x < c_top C)%Z -> m' x = m x.
Proof.
  intros C s' m m' x CK F Hlo Hx.
  assert (WN : win C x) by (unfold win; lia).
  destruct (win_facts C x CK WN) as (_ & Hat & Hg & He & Hh & _ & _).
  apply F; [exact (above_not_gap C x Hat) | exact Hg | exact He | exact Hh | unfold scratch; lia].
Qed.

Hypothesis H_mseq : mseq_udd_contract.

Theorem pixUpDownDetect_W : pixUpDownDetect_contract UDD_STACK RK_udd RB_udd.
Proof.
  pose proof H_mseq as HMS. unfold mseq_udd_contract in HMS.
  intros fr cs C A m md regs s pixs pconf w h cm datas cv ret S CK HW FZ MB H2 Hs16 Hlo Hhi Hra Hret H4
    H10 H11 H12 H13 H14 Hpc1 Hpc2 Hpc4 SRC kR bR AR HkR HbR HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins.
  pose proof (u64_range (c_sp0 C)) as SP.
  assert (SBm : (c_top C - LSTK + MSEQ_STACK <= s - 256)%Z) by (unfold UDD_STACK in Hlo; lia).
  assert (SB : (c_top C - LSTK + 3392 <= s - 256)%Z)
    by (cbv [UDD_STACK MSEQ_STACK V23LeptCloseSpec.CSC_STACK O23LeptCloseSpec.CSC_STACK] in Hlo; lia).
  assert (M256 : ((s - 256) mod 16 = 0)%Z) by (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity).
  assert (TT : (alloc_top (c_vm C) < 2 ^ 64)%Z) by lia.
  pose proof (aroom_nonneg A (m_vmmaps md) kR bR AR) as [Nk Nb].
  pose proof (RB_mseq_nonneg w h cm) as NBm. pose proof (RB_blk_nonneg w h) as NBb.
  pose proof RK_mseq_val as NKm. pose proof RK_blk_val as NKb.
  assert (EK : RK_udd = (4 * RK_selstr + RK_mseq + 2 * RK_blk)%Z) by reflexivity.
  assert (EB : RB_udd w h cm = (4 * RB_selstr + RB_mseq w h cm + 2 * RB_blk w h)%Z) by reflexivity.
  assert (KS : RK_selstr = 7%Z) by reflexivity.
  assert (BS : RB_selstr = (7 * 2 ^ 17)%Z) by reflexivity.
  assert (SOKH : forall Ax (mx : word -> option byte) mdx (b : Z) (n : nat), W C Ax mx mdx -> (s - 256 <= b)%Z ->
                 (b + Z.of_nat n <= s)%Z -> store_ok SEGS mx (Z_to_bv 64 b) n = true)
    by (intros Ax mx mdx b n HWx X1 X2; apply (W_sok_win C Ax mx mdx b n CK HWx); lia).
  assert (FW : forall Ax (mx : word -> option byte) mdx (k : Z) (v : word), W C Ax mx mdx -> (8 <= k <= 256)%Z ->
               W C Ax (O23LeptUddSegs.wr8w mx (s - k) v) mdx /\ POSTM C Ax s mx (O23LeptUddSegs.wr8w mx (s - k) v)).
  { intros Ax mx mdx k v HWx Hk. unfold O23LeptUddSegs.wr8w.
    apply (WP_win C Ax Ax mx mx mdx (Z_to_bv 64 (s - k)) (word_to_le_bytes 8 v) s CK (conj HWx (POSTM_refl C Ax s mx))
             (sub_live_refl Ax)); wsz. }
  assert (WRD : forall (mx : word -> option byte) (k : Z) (v : word) (b : Z) (n : nat), (8 <= k <= 256)%Z -> (s - 256 <= b)%Z ->
                (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - k \/ s - k + 8 <= b)%Z ->
                rdn SEGS (O23LeptUddSegs.wr8w mx (s - k) v) (Z_to_bv 64 b) n = rdn SEGS mx (Z_to_bv 64 b) n).
  { intros mx k v b n Hk X1 X2 X3. unfold O23LeptUddSegs.wr8w. apply rdn_wbytes_out_Z.
    rewrite length_N_to_le_bytes. zl. }
  assert (RB8 : forall (mx : word -> option byte) (k : Z) (v : word), (8 <= k <= 256)%Z ->
                rdn SEGS (O23LeptUddSegs.wr8w mx (s - k) v) (Z_to_bv 64 (s - k)) 8 = Some (word_to_le_bytes 8 v)).
  { intros mx k v Hk. unfold O23LeptUddSegs.wr8w.
    apply OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.SeqExec.rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
  assert (FRD : forall Ax (mx my : word -> option byte), POSTM C Ax (s - 256) mx my ->
                forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z ->
                rdn SEGS my (Z_to_bv 64 b) n = rdn SEGS mx (Z_to_bv 64 b) n).
  { intros Ax mx my PMx b n X1 X2. apply rdn_ext; [rewrite u_Z2bv by lia; lia |].
    intros x Hx. rewrite u_Z2bv in Hx by lia. apply (FRM_win C (s - 256) mx my x CK (proj1 PMx)); lia. }
  assert (PST : forall Ax (s' : Z) (m0 mx my : word -> option byte), sub_live A Ax -> (s' <= s)%Z ->
                POSTM C A s m0 mx -> POSTM C Ax s' mx my -> POSTM C A s m0 my)
    by (intros Ax s' m0 mx my SBx Hs' P1 P2;
        exact (POSTM_trans _ _ _ _ _ _ P1 (POSTM_sub C A Ax s mx my SBx (POSTM_mono C Ax s' s mx my Hs' P2)))).
  assert (KEEP : forall Ax Ay (mx my : word -> option byte) sel sv c, sub_live Ax Ay -> LIVK Ax mx my ->
                 sel_at (alloc_top (c_vm C)) Ax mx sel sv -> sel_cells mx sv c ->
                 sel_at (alloc_top (c_vm C)) Ay my sel sv /\ sel_cells my sv c).
  { intros Ax Ay mx my sel sv c SBx LK SA SC. split.
    - eapply sel_at_keep; [exact TT | exact SA | exact SBx | exact LK].
    - pose proof SA as (_ & _ & _ & _ & _ & _ & _ & _ & ROWS & _).
      eapply sel_cells_keep; [| exact LK | exact SC].
      intros i Hi. destruct (ROWS i Hi) as ((B1 & B2 & _) & Lr & _). split; [exact Lr | lia]. }
  assert (SLE : forall Ax Ay : AS, (forall q, live Ay q = live Ax q) -> sub_live Ax Ay)
    by (intros Ax Ay E q k Hq; rewrite E; exact Hq).
  assert (CC : forall (mx : word -> option byte) sv K, sel_cells mx sv (tsel K) -> sel_cont mx sv (tsel K)).
  { intros mx sv K SCx i j Hi Hj. split; [pose proof (tsel_range K i j); lia | exact (SCx i j Hi Hj)]. }
  assert (SOKf : store_ok SEGS m (Z_to_bv 64 (s - 256)) 256 = true) by (apply (SOKH A m md); [exact HW | lia | zl]).
  assert (SOKp : store_ok SEGS m (Z_to_bv 64 pconf) 4 = true) by (apply (W_sok_win C A m md pconf 4 CK HW); zl).
  destruct (ud_P al_rom fr cs regs m s pconf ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOKf SOKp H2 Hra H11 Hpc4)
    as (r1 & RUN1 & R1a & R1b & R1c & AG1).
  match type of RUN1 with msteps _ (mkst _ ?pc _ _) _ =>
    replace (Z_to_bv 64 PC_UDD) with pc by (apply bv_eq; reflexivity) end.
  rzs HW RUN1.
  assert (WU : W C A (O23LeptUddSegs.UDF m s ret regs fr) md /\ POSTM C A s m (O23LeptUddSegs.UDF m s ret regs fr)).
  { unfold O23LeptUddSegs.UDF.
    repeat (apply (WP_win C A A); [exact CK | | apply sub_live_refl | wsz | wsz | lia]).
    split; [exact HW | apply POSTM_refl]. }
  destruct WU as [WU PU].
  assert (WP1 : W C A (O23LeptSelGP.wr4 (O23LeptUddSegs.UDF m s ret regs fr) pconf 0) md).
  { unfold O23LeptSelGP.wr4.
    refine (proj1 (WP_win C A A _ _ md (Z_to_bv 64 pconf) (word_to_le_bytes 4 (Z_to_bv 64 0)) (pconf + 4) CK
                     (conj WU (POSTM_refl C A (pconf + 4) _)) (sub_live_refl A) _ _ _)); wsz. }
  assert (PM1 : POSTM C A s (O23LeptSelGP.wr4 m pconf 0) (O23LeptSelGP.wr4 (O23LeptUddSegs.UDF m s ret regs fr) pconf 0))
    by (unfold O23LeptSelGP.wr4; apply POSTM_both; exact PU).
  pose proof (POSTM_wbytes_win C A m md (Z_to_bv 64 pconf) (word_to_le_bytes 4 (Z_to_bv 64 0)) (pconf + 4) CK HW
                ltac:(wsz) ltac:(wsz) ltac:(lia)) as PMw.
  change (POSTM C A (pconf + 4) m (O23LeptSelGP.wr4 m pconf 0)) in PMw.
  assert (UD1 : UDC (O23LeptSelGP.wr4 (O23LeptUddSegs.UDF m s ret regs fr) pconf 0) s ret (getr regs 8) (getr regs 9)
                  (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
                  (getr regs 25) (getr regs 26) (getr regs 27) (reg_get fr 8) (reg_get fr 9)).
  { apply (UDC_pw (O23LeptUddSegs.UDF m s ret regs fr)); [lia | lia | | apply UDC_UDF; lia].
    intros b n X1 X2. apply wr4_rd_out; zl. }
  destruct SRC as [-> | (PX & HO & Hw & Hh & LP & LD & LP0 & LD0 & CMX)].
  - destruct UD1 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & U11 & U12 & U13 & U14 & U15).
    destruct (ud_P0 al_rom fr cs r1 (O23LeptSelGP.wr4 (O23LeptUddSegs.UDF m s ret regs fr) pconf 0) s ret
                (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (reg_get fr 8) (reg_get fr 9)
                ltac:(lia) ltac:(lia) (W_sev_got C A _ md WP1) (W_sev C A _ md WP1)
                U1 U2 U3 U4 U5 U6 U7 U8 U9 U10 U11 U12 U13 U14 U15 R1a ltac:(rewrite R1c; exact H10))
      as (fr0 & r0 & RUN0 & Z2 & Z1 & Z10 & Z11 & Z12 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27 & AG0).
    rzs WP1 RUN0.
    apply (returnErrorInt_W (fx := mkFP fr0 cs) C A _ md r0 s _ _ _ _ ret (Z_to_bv 64 1) S CK WP1 Z2 Hs16
             ltac:(cbv [LSF]; lia) Hhi Z1 Hret Z10 Z11 Z12 str_udd_err str_udd_proc).
    intros m' r' W' FR' MG' CS' RV'.
    pose proof (HK fr0 cs A m' (m_vmmaps md) r' 0%Z) as HK'. rewrite with_vmmaps_same in HK'.
    apply HK'.
    + exact W'.
    + exact FZ.
    + apply cs_kept_intro; csr; reflexivity.
    + apply (POSTM_trans _ _ _ _ _ _ PM1).
      apply (POSTM_range C A _ md m' (s - (16 + LSF)) s s CK WP1 FR'); cbv [LSF]; lia.
    + intros q; reflexivity.
    + apply (aroom_mono A (m_vmmaps md) kR bR); [exact AR | lia | lia].
  - pose proof PX as (Pp0 & Pp64 & _).
    pose proof (ai_live_hull A m (m_vmmaps md) (Z_to_bv 64 pixs) 64 (w_inv _ _ _ _ HW) LP) as (_ & AL16 & _).
    rewrite u_Z2bv in AL16 by lia.
    assert (P8 : (pixs mod 8 = 0)%Z)
      by (pose proof (mod16_plus_mod8 pixs 0 AL16 eq_refl) as E; rewrite Z.add_0_r in E; exact E).
    destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW LP ltac:(lia)) as [BP1 _].
    rewrite u_Z2bv in BP1 by lia.
    assert (LKm : forall mx, POSTM C A s (O23LeptSelGP.wr4 m pconf 0) mx -> LIVK A m mx)
      by (intros mx P; exact (proj2 (POSTM_trans _ _ _ _ _ _ PMw (POSTM_mono C A s (pconf + 4) _ _ ltac:(lia) P)))).
    assert (PXK : forall mx, LIVK A m mx -> PIXat mx pixs (hdv w h 1 cm datas)).
    { intros mx LK. apply (PIXat_frame m mx pixs _ PX). intros x Hx.
      exact (O23LeptCmap2.LIVK_at A m mx pixs 64 x LK LP ltac:(lia) ltac:(lia) Hx). }
    assert (CMK : forall Ax mx, sub_live A Ax -> LIVK A m mx ->
              cm = 0%Z \/ (CMAPat mx cm cv /\ cmap_ok cv /\ live Ax (Z_to_bv 64 cm) = Some 24%Z /\
                           live Ax (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
    { intros Ax mx SBx LK. destruct CMX as [-> | (CM & CO & LC & LA & _ & _)]; [left; reflexivity | right].
      pose proof CM as (C0 & C24 & _).
      split; [| split; [exact CO | split; [exact (SBx _ _ LC) | exact (SBx _ _ LA)]]].
      apply (CMAPat_frame m mx cm cv CM). intros x Hx.
      exact (O23LeptCmap2.LIVK_at A m mx cm 24 x LK LC ltac:(lia) ltac:(lia) Hx). }
    destruct (ud_P1 al_rom (mkFP fr cs) r1 (O23LeptSelGP.wr4 (O23LeptUddSegs.UDF m s ret regs fr) pconf 0) pixs
                ltac:(lia) ltac:(lia) P8 (PIX_rd_d SEGS _ pixs _ (PXK _ (LKm _ PM1)))
                ltac:(rewrite R1c; exact H10) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
      as (r2 & RUN2 & R2_1 & R2_10 & R2_11 & R2_12 & R2_13 & R2_9 & R2_18 & R2_26 & AG2).
    rzs WP1 RUN2.
    lazymatch goal with |- realizes _ (mkCfg (mkst _ ?g _ _) _) _ =>
      replace g with (Z_to_bv 64 PC_selstr) by (apply bv_eq; reflexivity) end.
    apply (selCreateFromString_W (fx := mkFP fr cs) 1%nat C A _ md r2 (s - 256) (getr r2 1) S ltac:(lia) CK WP1
             ltac:(csr; reflexivity) M256 ltac:(cbv [SELSTR_WIN]; lia) ltac:(lia) eq_refl
             ltac:(rewrite R2_1; apply ret_ok_even; reflexivity)
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
             kR bR AR ltac:(lia) ltac:(lia)).
    intros A1 m1 vm1 r3 sel1 sv1 W1 CS3 PS1 SUB1 R3 SA1 Y1 X1 CY1 CX1 N1 SC1 SF1 SF01 SO1 AR1.
    destruct (ud_S1 al_rom (mkFP fr cs) r3 m1 s ltac:(lia) ltac:(lia) (SOKH _ _ _ (s - 176)%Z 8%nat W1 ltac:(lia) ltac:(zl))
                ltac:(csr; reflexivity))
      as (r4 & RUN4 & R4_1 & R4_10 & R4_11 & R4_12 & R4_13 & R4_24 & AG4).
    pcto RUN4 R2_1. rzs W1 RUN4.
    destruct (FW _ _ _ 176%Z (getr r3 10) W1 ltac:(lia)) as [W2 PW2].
    pose proof (PST A (s - 256)%Z _ _ _ (sub_live_refl A) ltac:(lia) PM1 PS1) as PMc1.
    pose proof (PST A1 s _ _ _ SUB1 ltac:(lia) PMc1 PW2) as PMc2.
    destruct (KEEP _ _ _ _ _ _ _ (sub_live_refl A1) (proj2 PW2) SA1 SC1) as [SA1_2 SC1_2].
    lazymatch goal with |- realizes _ (mkCfg (mkst _ ?g _ _) _) _ =>
      replace g with (Z_to_bv 64 PC_selstr) by (apply bv_eq; reflexivity) end.
    apply (selCreateFromString_W (fx := mkFP fr cs) 2%nat C A1 _ (with_vmmaps vm1 md) r4 (s - 256) (getr r4 1) S ltac:(lia) CK W2
             ltac:(csr; reflexivity) M256 ltac:(cbv [SELSTR_WIN]; lia) ltac:(lia) eq_refl
             ltac:(rewrite R4_1; apply ret_ok_even; reflexivity)
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
             (kR - RK_selstr) (bR - RB_selstr) ltac:(rewrite with_vmmaps_vmmaps; exact AR1) ltac:(lia) ltac:(lia)).
    intros A2 m2 vm2 r5 sel2 sv2 W3 CS5 PS3 SUB2 R5 SA2 Y2 X2 CY2 CX2 N2 SC2 SF2 SF02 SO2 AR3.
    rewrite with_vmmaps_twice in W3 |- *.
    destruct (ud_S2 al_rom (mkFP fr cs) r5 m2 s ltac:(lia) ltac:(lia) (SOKH _ _ _ (s - 184)%Z 8%nat W3 ltac:(lia) ltac:(zl))
                ltac:(csr; reflexivity))
      as (r6 & RUN6 & R6_1 & R6_10 & R6_11 & R6_12 & R6_13 & R6_25 & AG6).
    pcto RUN6 R4_1. rzs W3 RUN6.
    destruct (FW _ _ _ 184%Z (getr r5 10) W3 ltac:(lia)) as [W4 PW4].
    pose proof (sub_live_trans _ _ _ SUB1 SUB2) as SUB2c.
    pose proof (PST A1 (s - 256)%Z _ _ _ SUB1 ltac:(lia) PMc2 PS3) as PMc3.
    pose proof (PST A2 s _ _ _ SUB2c ltac:(lia) PMc3 PW4) as PMc4.
    pose proof (O23LeptUddLib.disj_sym _ _ (O23LeptUddLib.disj_off_live _ _ _
                  (O23LeptUddLib.lives_of_sel _ _ _ _ _ Y1 SA1_2) (O23LeptUddLib.offs_of_sel A1 sel2 sv2 Y2 SF2))) as D21.
    destruct (KEEP _ _ _ _ _ _ _ SUB2 (proj2 PS3) SA1_2 SC1_2) as [SA1_3 SC1_3].
    destruct (KEEP _ _ _ _ _ _ _ (sub_live_refl A2) (proj2 PW4) SA1_3 SC1_3) as [SA1_4 SC1_4].
    destruct (KEEP _ _ _ _ _ _ _ (sub_live_refl A2) (proj2 PW4) SA2 SC2) as [SA2_4 SC2_4].
    lazymatch goal with |- realizes _ (mkCfg (mkst _ ?g _ _) _) _ =>
      replace g with (Z_to_bv 64 PC_selstr) by (apply bv_eq; reflexivity) end.
    apply (selCreateFromString_W (fx := mkFP fr cs) 3%nat C A2 _ (with_vmmaps vm2 md) r6 (s - 256) (getr r6 1) S ltac:(lia) CK W4
             ltac:(csr; reflexivity) M256 ltac:(cbv [SELSTR_WIN]; lia) ltac:(lia) eq_refl
             ltac:(rewrite R6_1; apply ret_ok_even; reflexivity)
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
             (kR - RK_selstr - RK_selstr) (bR - RB_selstr - RB_selstr) ltac:(rewrite with_vmmaps_vmmaps; exact AR3)
             ltac:(lia) ltac:(lia)).
    intros A3 m3 vm3 r7 sel3 sv3 W5 CS7 PS5 SUB3 R7 SA3 Y3 X3 CY3 CX3 N3 SC3 SF3 SF03 SO3 AR5.
    rewrite with_vmmaps_twice in W5 |- *.
    destruct (ud_S3 al_rom (mkFP fr cs) r7 m3 s ltac:(lia) ltac:(lia) (SOKH _ _ _ (s - 192)%Z 8%nat W5 ltac:(lia) ltac:(zl))
                ltac:(csr; reflexivity))
      as (r8 & RUN8 & R8_1 & R8_10 & R8_11 & R8_12 & R8_13 & R8_21 & AG8).
    pcto RUN8 R6_1. rzs W5 RUN8.
    destruct (FW _ _ _ 192%Z (getr r7 10) W5 ltac:(lia)) as [W6 PW6].
    pose proof (sub_live_trans _ _ _ SUB2c SUB3) as SUB3c.
    pose proof (PST A2 (s - 256)%Z _ _ _ SUB2c ltac:(lia) PMc4 PS5) as PMc5.
    pose proof (PST A3 s _ _ _ SUB3c ltac:(lia) PMc5 PW6) as PMc6.
    pose proof (O23LeptUddLib.disj_sym _ _ (O23LeptUddLib.disj_off_live _ _ _
                  (O23LeptUddLib.lives_of_sel _ _ _ _ _ Y1 SA1_4) (O23LeptUddLib.offs_of_sel A2 sel3 sv3 Y3 SF3))) as D31.
    pose proof (O23LeptUddLib.disj_sym _ _ (O23LeptUddLib.disj_off_live _ _ _
                  (O23LeptUddLib.lives_of_sel _ _ _ _ _ Y2 SA2_4) (O23LeptUddLib.offs_of_sel A2 sel3 sv3 Y3 SF3))) as D32.
    destruct (KEEP _ _ _ _ _ _ _ SUB3 (proj2 PS5) SA1_4 SC1_4) as [SA1_5 SC1_5].
    destruct (KEEP _ _ _ _ _ _ _ SUB3 (proj2 PS5) SA2_4 SC2_4) as [SA2_5 SC2_5].
    destruct (KEEP _ _ _ _ _ _ _ (sub_live_refl A3) (proj2 PW6) SA1_5 SC1_5) as [SA1_6 SC1_6].
    destruct (KEEP _ _ _ _ _ _ _ (sub_live_refl A3) (proj2 PW6) SA2_5 SC2_5) as [SA2_6 SC2_6].
    destruct (KEEP _ _ _ _ _ _ _ (sub_live_refl A3) (proj2 PW6) SA3 SC3) as [SA3_6 SC3_6].
    lazymatch goal with |- realizes _ (mkCfg (mkst _ ?g _ _) _) _ =>
      replace g with (Z_to_bv 64 PC_selstr) by (apply bv_eq; reflexivity) end.
    apply (selCreateFromString_W (fx := mkFP fr cs) 4%nat C A3 _ (with_vmmaps vm3 md) r8 (s - 256) (getr r8 1) S ltac:(lia) CK W6
             ltac:(csr; reflexivity) M256 ltac:(cbv [SELSTR_WIN]; lia) ltac:(lia) eq_refl
             ltac:(rewrite R8_1; apply ret_ok_even; reflexivity)
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
             (kR - RK_selstr - RK_selstr - RK_selstr) (bR - RB_selstr - RB_selstr - RB_selstr)
             ltac:(rewrite with_vmmaps_vmmaps; exact AR5) ltac:(lia) ltac:(lia)).
    intros A4 m4 vm4 r9 sel4 sv4 W7 CS9 PS7 SUB4 R9 SA4 Y4 X4 CY4 CX4 N4 SC4 SF4 SF04 SO4 AR7.
    rewrite with_vmmaps_twice in W7 |- *.
    destruct (ud_S4 al_rom (mkFP fr cs) r9 m4 s ltac:(lia) ltac:(lia) (SOKH _ _ _ (s - 200)%Z 8%nat W7 ltac:(lia) ltac:(zl))
                ltac:(csr; reflexivity))
      as (r10 & RUN10 & R10_1 & R10_10 & R10_11 & R10_12 & R10_22 & AG10).
    pcto RUN10 R8_1. rzs W7 RUN10.
    destruct (FW _ _ _ 200%Z (getr r9 10) W7 ltac:(lia)) as [W8 PW8].
    pose proof (sub_live_trans _ _ _ SUB3c SUB4) as SUB4c.
    pose proof (PST A3 (s - 256)%Z _ _ _ SUB3c ltac:(lia) PMc6 PS7) as PMc7.
    pose proof (PST A4 s _ _ _ SUB4c ltac:(lia) PMc7 PW8) as PMc8.
    pose proof (O23LeptUddLib.disj_sym _ _ (O23LeptUddLib.disj_off_live _ _ _
                  (O23LeptUddLib.lives_of_sel _ _ _ _ _ Y1 SA1_6) (O23LeptUddLib.offs_of_sel A3 sel4 sv4 Y4 SF4))) as D41.
    pose proof (O23LeptUddLib.disj_sym _ _ (O23LeptUddLib.disj_off_live _ _ _
                  (O23LeptUddLib.lives_of_sel _ _ _ _ _ Y2 SA2_6) (O23LeptUddLib.offs_of_sel A3 sel4 sv4 Y4 SF4))) as D42.
    pose proof (O23LeptUddLib.disj_sym _ _ (O23LeptUddLib.disj_off_live _ _ _
                  (O23LeptUddLib.lives_of_sel _ _ _ _ _ Y3 SA3_6) (O23LeptUddLib.offs_of_sel A3 sel4 sv4 Y4 SF4))) as D43.
    destruct (KEEP _ _ _ _ _ _ _ SUB4 (proj2 PS7) SA1_6 SC1_6) as [SA1_7 SC1_7].
    destruct (KEEP _ _ _ _ _ _ _ SUB4 (proj2 PS7) SA2_6 SC2_6) as [SA2_7 SC2_7].
    destruct (KEEP _ _ _ _ _ _ _ SUB4 (proj2 PS7) SA3_6 SC3_6) as [SA3_7 SC3_7].
    destruct (KEEP _ _ _ _ _ _ _ (sub_live_refl A4) (proj2 PW8) SA1_7 SC1_7) as [SA1_8 SC1_8].
    destruct (KEEP _ _ _ _ _ _ _ (sub_live_refl A4) (proj2 PW8) SA2_7 SC2_7) as [SA2_8 SC2_8].
    destruct (KEEP _ _ _ _ _ _ _ (sub_live_refl A4) (proj2 PW8) SA3_7 SC3_7) as [SA3_8 SC3_8].
    destruct (KEEP _ _ _ _ _ _ _ (sub_live_refl A4) (proj2 PW8) SA4 SC4) as [SA4_8 SC4_8].
    apply (HMS fr cs C A4 _ (with_vmmaps vm4 md) r10 (s - 256)%Z pixs w h cm datas cv (getr r10 1) S CK MB W8 FZ
             ltac:(csr; reflexivity) M256 SBm ltac:(lia) eq_refl ltac:(rewrite R10_1; apply ret_ok_even; reflexivity)
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
             (PXK _ (LKm _ PMc8)) HO Hw Hh (SUB4c _ _ LP) (SUB4c _ _ LD) (CMK _ _ SUB4c (LKm _ PMc8))
             (kR - RK_selstr - RK_selstr - RK_selstr - RK_selstr)%Z (bR - RB_selstr - RB_selstr - RB_selstr - RB_selstr)%Z
             ltac:(rewrite with_vmmaps_vmmaps; exact AR7) ltac:(lia) ltac:(lia)).
    intros fr5 cs5 A5 m5 vm5 r11 pix0 cd data cv5 FZ5 W9 CS11 R11 PS9 PC9 ON9 OF9 AR9.
    rewrite with_vmmaps_twice in W9 |- *.
    pose proof PC9 as ((P0a & P0b & _) & _).
    pose proof (O23LeptUddLib.sub_of_only _ _ _ ON9 OF9) as SUB5.
    pose proof (sub_live_trans _ _ _ SUB4c SUB5) as SUB5c.
    pose proof (O23LeptUddLib.disj_off_live _ _ _ (O23LeptUddLib.lives_of_sel _ _ _ _ _ Y1 SA1_8) OF9) as D1p.
    pose proof (O23LeptUddLib.disj_off_live _ _ _ (O23LeptUddLib.lives_of_sel _ _ _ _ _ Y2 SA2_8) OF9) as D2p.
    pose proof (O23LeptUddLib.disj_off_live _ _ _ (O23LeptUddLib.lives_of_sel _ _ _ _ _ Y3 SA3_8) OF9) as D3p.
    pose proof (O23LeptUddLib.disj_off_live _ _ _ (O23LeptUddLib.lives_of_sel _ _ _ _ _ Y4 SA4_8) OF9) as D4p.
    destruct (KEEP _ _ _ _ _ _ _ SUB5 (proj2 PS9) SA1_8 SC1_8) as [SA1_9 SC1_9].
    destruct (KEEP _ _ _ _ _ _ _ SUB5 (proj2 PS9) SA2_8 SC2_8) as [SA2_9 SC2_9].
    destruct (KEEP _ _ _ _ _ _ _ SUB5 (proj2 PS9) SA3_8 SC3_8) as [SA3_9 SC3_9].
    destruct (KEEP _ _ _ _ _ _ _ SUB5 (proj2 PS9) SA4_8 SC4_8) as [SA4_9 SC4_9].
    destruct (ud_M al_rom (mkFP fr5 cs5) r11 m5 s ltac:(lia) ltac:(lia) (SOKH _ _ _ (s - 256)%Z 256%nat W9 ltac:(lia) ltac:(zl))
                ltac:(csr; reflexivity) ltac:(csr; reflexivity))
      as (r12 & RUN12 & R12_23 & R12_20 & AG12).
    pcto RUN12 R10_1. rzs W9 RUN12.
    destruct (FW _ _ _ 136%Z (getr r11 10) W9 ltac:(lia)) as [W10a PW10a].
    destruct (FW _ _ _ 168%Z (Z_to_bv 64 0) W10a ltac:(lia)) as [W10 PW10b].
    pose proof (POSTM_trans _ _ _ _ _ _ PW10a PW10b) as PW10.
    pose proof (PST A4 (s - 256)%Z _ _ _ SUB4c ltac:(lia) PMc8 PS9) as PMc9.
    pose proof (PST A5 s _ _ _ SUB5c ltac:(lia) PMc9 PW10) as PMc10.
    pose proof (O23LeptUddLib.PIXC_livk C A5 A5 _ _ pix0 w h cd data cv5 PC9 (sub_live_refl A5) (proj2 PW10)) as PC10.
    destruct (KEEP _ _ _ _ _ _ _ (sub_live_refl A5) (proj2 PW10) SA1_9 SC1_9) as [SA1_10 SC1_10].
    destruct (KEEP _ _ _ _ _ _ _ (sub_live_refl A5) (proj2 PW10) SA2_9 SC2_9) as [SA2_10 SC2_10].
    destruct (KEEP _ _ _ _ _ _ _ (sub_live_refl A5) (proj2 PW10) SA3_9 SC3_9) as [SA3_10 SC3_10].
    destruct (KEEP _ _ _ _ _ _ _ (sub_live_refl A5) (proj2 PW10) SA4_9 SC4_9) as [SA4_10 SC4_10].
    apply (udd_blk1_W fr5 cs5 C A5 _ (with_vmmaps vm5 md) r12 s pix0 w h cd data sel1 sel2 cv5 sv1 sv2 (tsel 1%nat) (tsel 2%nat) S
             (kR - RK_selstr - RK_selstr - RK_selstr - RK_selstr - RK_mseq)
             (bR - RB_selstr - RB_selstr - RB_selstr - RB_selstr - RB_mseq w h cm)
             CK W10 FZ5 Hs16 Hlo Hhi ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
             PC10 HO Hw Hh SA1_10 (CC _ _ 1%nat SC1_10) ltac:(rewrite CX1, X1; cbn; lia) ltac:(rewrite CY1, Y1; cbn; lia) Y1
             SA2_10 (CC _ _ 2%nat SC2_10) ltac:(rewrite CX2, X2; cbn; lia) ltac:(rewrite CY2, Y2; cbn; lia) Y2 D1p D2p
             ltac:(rewrite with_vmmaps_vmmaps; exact AR9) ltac:(lia) ltac:(lia)).
    intros fr6 cs6 A6 m6 vm6 r13 bc0 W11 FZ6 CS13 LV11 PM11 RD11 Rb0 Lb0 AR11.
    rewrite with_vmmaps_twice in W11 |- *.
    pose proof (SLE _ _ LV11) as SUB6. pose proof (sub_live_trans _ _ _ SUB5c SUB6) as SUB6c.
    pose proof (PST A5 s _ _ _ SUB5c ltac:(lia) PMc10 PM11) as PMc11.
    pose proof (O23LeptUddLib.PIXC_livk C A5 A6 _ _ pix0 w h cd data cv5 PC10 SUB6 (proj2 PM11)) as PC11.
    destruct (KEEP _ _ _ _ _ _ _ SUB6 (proj2 PM11) SA1_10 SC1_10) as [SA1_11 SC1_11].
    destruct (KEEP _ _ _ _ _ _ _ SUB6 (proj2 PM11) SA2_10 SC2_10) as [SA2_11 SC2_11].
    destruct (KEEP _ _ _ _ _ _ _ SUB6 (proj2 PM11) SA3_10 SC3_10) as [SA3_11 SC3_11].
    destruct (KEEP _ _ _ _ _ _ _ SUB6 (proj2 PM11) SA4_10 SC4_10) as [SA4_11 SC4_11].
    apply (udd_blk2_W fr6 cs6 C A6 _ (with_vmmaps vm6 md) r13 s pix0 w h cd data sel3 sel4 cv5 sv3 sv4 (tsel 3%nat) (tsel 4%nat) S
             (kR - RK_selstr - RK_selstr - RK_selstr - RK_selstr - RK_mseq - RK_blk)
             (bR - RB_selstr - RB_selstr - RB_selstr - RB_selstr - RB_mseq w h cm - RB_blk w h)
             CK W11 FZ6 Hs16 Hlo Hhi ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
             PC11 HO Hw Hh SA3_11 (CC _ _ 3%nat SC3_11) ltac:(rewrite CX3, X3; cbn; lia) ltac:(rewrite CY3, Y3; cbn; lia) Y3
             SA4_11 (CC _ _ 4%nat SC4_11) ltac:(rewrite CX4, X4; cbn; lia) ltac:(rewrite CY4, Y4; cbn; lia) Y4 D3p D4p
             ltac:(rewrite with_vmmaps_vmmaps; exact AR11) ltac:(lia) ltac:(lia)).
    intros fr7 cs7 A7 m7 vm7 r14 bc1 W12 FZ7 CS14 LV12 PM12 RD12 Rb1 Lb1 AR12.
    rewrite with_vmmaps_twice in W12 |- *.
    pose proof (SLE _ _ LV12) as SUB7.
    pose proof (PST A6 s _ _ _ SUB6c ltac:(lia) PMc11 PM12) as PMc12.
    pose proof (O23LeptUddLib.PIXC_livk C A6 A7 _ _ pix0 w h cd data cv5 PC11 SUB7 (proj2 PM12)) as PC12.
    destruct (KEEP _ _ _ _ _ _ _ SUB7 (proj2 PM12) SA1_11 SC1_11) as [SA1_12 _].
    destruct (KEEP _ _ _ _ _ _ _ SUB7 (proj2 PM12) SA2_11 SC2_11) as [SA2_12 _].
    destruct (KEEP _ _ _ _ _ _ _ SUB7 (proj2 PM12) SA3_11 SC3_11) as [SA3_12 _].
    destruct (KEEP _ _ _ _ _ _ _ SUB7 (proj2 PM12) SA4_11 SC4_11) as [SA4_12 _].
    assert (Rb0' : rdn SEGS m7 (Z_to_bv 64 (s - 124)) 4 = Some bc0) by (rewrite RD12 by zl; exact Rb0).
    assert (Rp0 : rdn SEGS m7 (Z_to_bv 64 (s - 136)) 8 = Some (Z_to_le_bytes 8 pix0)).
    { rewrite RD12, RD11, WRD by zl. rewrite RB8 by lia. rewrite R11, w2b_Z by lia. reflexivity. }
    assert (Rz : rdn SEGS m7 (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 0)).
    { rewrite RD12, RD11 by zl. rewrite RB8 by lia. rewrite w2b_Z by lia. reflexivity. }
    assert (Rs1 : rdn SEGS m7 (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 sel1)).
    { pose proof SA1 as (_ & _ & (B1 & B2 & _) & _).
      rewrite RD12, RD11, WRD, WRD, (FRD _ _ _ PS9), WRD, (FRD _ _ _ PS7), WRD, (FRD _ _ _ PS5), WRD, (FRD _ _ _ PS3) by zl.
      rewrite RB8 by lia. rewrite R3, w2b_Z by lia. reflexivity. }
    assert (Rs2 : rdn SEGS m7 (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 sel2)).
    { pose proof SA2 as (_ & _ & (B1 & B2 & _) & _).
      rewrite RD12, RD11, WRD, WRD, (FRD _ _ _ PS9), WRD, (FRD _ _ _ PS7), WRD, (FRD _ _ _ PS5) by zl.
      rewrite RB8 by lia. rewrite R5, w2b_Z by lia. reflexivity. }
    assert (Rs3 : rdn SEGS m7 (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 sel3)).
    { pose proof SA3 as (_ & _ & (B1 & B2 & _) & _).
      rewrite RD12, RD11, WRD, WRD, (FRD _ _ _ PS9), WRD, (FRD _ _ _ PS7) by zl.
      rewrite RB8 by lia. rewrite R7, w2b_Z by lia. reflexivity. }
    assert (Rs4 : rdn SEGS m7 (Z_to_bv 64 (s - 200)) 8 = Some (Z_to_le_bytes 8 sel4)).
    { pose proof SA4 as (_ & _ & (B1 & B2 & _) & _).
      rewrite RD12, RD11, WRD, WRD, (FRD _ _ _ PS9) by zl.
      rewrite RB8 by lia. rewrite R9, w2b_Z by lia. reflexivity. }
    assert (UD12 : UDC m7 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                     (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
                     (reg_get fr 8) (reg_get fr 9)).
    { eapply UDC_pw; [lia | lia | | exact UD1].
      intros b n Q1 Q2.
      rewrite RD12, RD11, WRD, WRD, (FRD _ _ _ PS9), WRD, (FRD _ _ _ PS7), WRD, (FRD _ _ _ PS5), WRD, (FRD _ _ _ PS3), WRD,
        (FRD _ _ _ PS1) by zl.
      reflexivity. }
    assert (ONLY : O23LeptUddLib.only A A7 (O23LeptUddLib.pix_l pix0 data cd (c_arr cv5) ++ O23LeptUddLib.sel_l sel1 sv1 ++
                     O23LeptUddLib.sel_l sel2 sv2 ++ O23LeptUddLib.sel_l sel3 sv3 ++ O23LeptUddLib.sel_l sel4 sv4)).
    { pose proof (O23LeptUddLib.only_trans _ _ _ _ _ (O23LeptUddLib.only_of_sel A A1 sel1 sv1 Y1 SO1)
                    (O23LeptUddLib.only_of_sel A1 A2 sel2 sv2 Y2 SO2)) as OA.
      pose proof (O23LeptUddLib.only_trans _ _ _ _ _ OA (O23LeptUddLib.only_of_sel A2 A3 sel3 sv3 Y3 SO3)) as OB.
      pose proof (O23LeptUddLib.only_trans _ _ _ _ _ OB (O23LeptUddLib.only_of_sel A3 A4 sel4 sv4 Y4 SO4)) as OC.
      pose proof (O23LeptUddLib.only_trans _ _ _ _ _ OC ON9) as OD.
      pose proof (O23LeptUddLib.only_trans_l _ _ _ _ OD (O23LeptUddLib.only_eq _ _ _ LV11)) as OE.
      pose proof (O23LeptUddLib.only_trans_l _ _ _ _ OE (O23LeptUddLib.only_eq _ _ _ LV12)) as OF.
      apply (O23LeptUddLib.only_sub _ _ _ _ OF). intros q Hq. rewrite !in_app_iff in Hq |- *. tauto. }
    assert (OFFS : O23LeptUddLib.offs A (O23LeptUddLib.pix_l pix0 data cd (c_arr cv5) ++ O23LeptUddLib.sel_l sel1 sv1 ++
                     O23LeptUddLib.sel_l sel2 sv2 ++ O23LeptUddLib.sel_l sel3 sv3 ++ O23LeptUddLib.sel_l sel4 sv4)).
    { apply O23LeptUddLib.offs_app; [exact (O23LeptUddLib.offs_sub _ _ _ OF9 SUB4c) |].
      apply O23LeptUddLib.offs_app; [exact (O23LeptUddLib.offs_of_sel A sel1 sv1 Y1 SF1) |].
      apply O23LeptUddLib.offs_app; [exact (O23LeptUddLib.offs_sub _ _ _ (O23LeptUddLib.offs_of_sel A1 sel2 sv2 Y2 SF2) SUB1) |].
      apply O23LeptUddLib.offs_app; [exact (O23LeptUddLib.offs_sub _ _ _ (O23LeptUddLib.offs_of_sel A2 sel3 sv3 Y3 SF3) SUB2c) |].
      exact (O23LeptUddLib.offs_sub _ _ _ (O23LeptUddLib.offs_of_sel A3 sel4 sv4 Y4 SF4) SUB3c). }
    assert (AR12' : aroom A7 vm7 (kR - RK_udd)%Z (bR - RB_udd w h cm)%Z) by (eapply aroom_mono; [exact AR12 | lia | lia]).
    apply (udd_tail_W fr7 cs7 C A A7 m m7 md vm7 regs r14 s pconf pix0 w h cd data sel1 sel2 sel3 sel4 cv5 sv1 sv2 sv3 sv4
             bc0 bc1 ret (reg_get fr 8) (reg_get fr 9) S (kR - RK_udd) (bR - RB_udd w h cm)
             CK HW W12 FZ7 Hs16 Hlo Hhi Hret H2 Hpc1 Hpc2
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) H4
             UD12 Rb0' Lb0 Rb1 Lb1 Rp0 Rz Rs1 Rs2 Rs3 Rs4 PC12 Hw Hh
             SA1_12 N1 Y1 SF01 SA2_12 N2 Y2 SF02 SA3_12 N3 Y3 SF03 SA4_12 N4 Y4 SF04
             D1p D2p D3p D4p D21 D31 D41 D32 D42 D43 ONLY OFFS PMc12 AR12' HK).
Qed.

End UddW.
