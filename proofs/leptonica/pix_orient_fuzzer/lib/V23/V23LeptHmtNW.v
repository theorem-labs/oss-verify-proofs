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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptDilSegs V23LeptDilW V23LeptHmtSegs V23LeptHmtW V23LeptSelFMT.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptCmap2 V23LeptPixCopyT V23LeptGrayAT V23LeptPma1 V23LeptSelGP V23LeptPixMisc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixCopyT O23LeptPixHdr O23LeptCmapValid O23LeptCmap2 O23LeptSelGP O23LeptSelFMT O23LeptPma1 O23LeptDilW O23LeptHmtNW O23LeptRbordW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LiaRel.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_rel.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_rel.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition frH (s : Z) (ret : word) (r0 : bvmap 5 word) : list (Z * word) :=
  [(s - 8, ret); (s - 16, getr r0 8); (s - 24, getr r0 9); (s - 32, getr r0 18); (s - 40, getr r0 19); (s - 48, getr r0 20);
   (s - 56, getr r0 21); (s - 64, getr r0 22); (s - 72, getr r0 23); (s - 80, getr r0 24); (s - 88, getr r0 25);
   (s - 96, getr r0 26); (s - 104, getr r0 27)]%Z.

Section HmtNW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Ltac rzs HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
Ltac grows_chain := repeat (eapply mem_grows_trans; [| apply wbytes_grows]); apply mem_grows_refl.
Ltac pc_as RUN :=
  lazymatch type of RUN with msteps _ (mkst _ ?pc _ _) _ =>
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?gpc _ _) _) _ => replace gpc with pc by (apply bv_eq; reflexivity) end end.

Lemma frH_out : forall m m' (lo hi s : Z) ret r0, (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) ->
  (0 <= hi)%Z -> (hi <= s - 104)%Z -> (s < 2 ^ 64)%Z -> cellsZ m (frH s ret r0) -> cellsZ m' (frH s ret r0).
Proof.
  intros m m' lo hi s ret r0 OUT H0 H1 H2. apply (cellsZ_out m m' lo hi _ OUT).
  unfold frH. repeat constructor; cbn [fst]; lia.
Qed.

Lemma frH_frm : forall C s' m m' s ret r0, Cok C -> FRM C s' m m' -> (c_top C - LSTK <= s')%Z -> (s' <= s - 104)%Z ->
  (s < 2 ^ 64)%Z -> cellsZ m (frH s ret r0) -> cellsZ m' (frH s ret r0).
Proof.
  intros C s' m m' s ret r0 CK F H1 H2 H3. apply (cellsZ_frm C s' m m' _ CK F H1).
  unfold frH. repeat constructor; cbn [fst]; lia.
Qed.

Lemma str_hmt_proc : str16 0x16348 6.
Proof. str16_tac. Qed.     (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma SFR_rd : forall m (s y0 y1 y2 y3 : Z), (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (0 <= y0 < 2 ^ 32)%Z -> (0 <= y1 < 2 ^ 32)%Z -> (0 <= y2 < 2 ^ 32)%Z -> (0 <= y3 < 2 ^ 32)%Z ->
  rdn SEGS (O23LeptSelFMT.SFR m (s - 132) (s - 136) (s - 140) (s - 144) y0 y1 y2 y3) (Z_to_bv 64 (s - 132)) 4 = Some (Z_to_le_bytes 4 y0) /\
  rdn SEGS (O23LeptSelFMT.SFR m (s - 132) (s - 136) (s - 140) (s - 144) y0 y1 y2 y3) (Z_to_bv 64 (s - 136)) 4 = Some (Z_to_le_bytes 4 y1) /\
  rdn SEGS (O23LeptSelFMT.SFR m (s - 132) (s - 136) (s - 140) (s - 144) y0 y1 y2 y3) (Z_to_bv 64 (s - 140)) 4 = Some (Z_to_le_bytes 4 y2) /\
  rdn SEGS (O23LeptSelFMT.SFR m (s - 132) (s - 136) (s - 140) (s - 144) y0 y1 y2 y3) (Z_to_bv 64 (s - 144)) 4 = Some (Z_to_le_bytes 4 y3).
Proof.
  intros m s y0 y1 y2 y3 Hs Hs64 H0 H1 H2 H3. rewrite O23LeptHmtNW.SFR_eq.
  split; [| split; [| split]].
  - rewrite (wr4_rd_out _ (s - 144)), (wr4_rd_out _ (s - 140)), (wr4_rd_out _ (s - 136)) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    apply wr4_rd_hit; lia.
  - rewrite (wr4_rd_out _ (s - 144)), (wr4_rd_out _ (s - 140)) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    apply wr4_rd_hit; lia.
  - rewrite (wr4_rd_out _ (s - 144)) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    apply wr4_rd_hit; lia.
  - apply wr4_rd_hit; lia.
Qed.

Lemma SFR_rd_out : forall m (s y0 y1 y2 y3 b : Z) (n : nat), (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= b)%Z -> (b + Z.of_nat n < 2 ^ 64)%Z ->
  (b + Z.of_nat n <= s - 144 \/ s - 128 <= b)%Z ->
  rdn SEGS (O23LeptSelFMT.SFR m (s - 132) (s - 136) (s - 140) (s - 144) y0 y1 y2 y3) (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n.
Proof.
  intros m s y0 y1 y2 y3 b n Hs Hs64 Hb Hbn D. rewrite O23LeptHmtNW.SFR_eq.
  rewrite (wr4_rd_out _ (s - 144)), (wr4_rd_out _ (s - 140)), (wr4_rd_out _ (s - 136)), (wr4_rd_out _ (s - 132)) by lia.
  reflexivity.
Qed.

Lemma SFR_out : forall m (s y0 y1 y2 y3 : Z) (x : word), (160 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 144 <= u x < s - 128)%Z ->
  O23LeptSelFMT.SFR m (s - 132) (s - 136) (s - 140) (s - 144) y0 y1 y2 y3 x = m x.
Proof.
  intros m s y0 y1 y2 y3 x Hs Hs64 Hx. rewrite O23LeptHmtNW.SFR_eq.
  rewrite !O23LeptSelGP.wr4_out by lia. reflexivity.
Qed.

Lemma FRH_WP : forall C A m md (s s' : Z) ret regs, Cok C -> W C A m md ->
  (c_top C - LSTK <= s - 104)%Z -> (s <= s')%Z -> (s' <= c_top C)%Z ->
  W C A (FRH m s ret regs) md /\ POSTM C A s' m (FRH m s ret regs).
Proof.
  intros C A m md s s' ret regs CK HW H1 H2 H3. pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  unfold FRH, FRD. wp_win CK.
Qed.

Lemma frH_FRH : forall m s ret regs, (104 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (FRH m s ret regs) (frH s ret regs).
Proof. intros m s ret regs Hs Hs64. unfold frH, FRH, FRD. cbn [cellsZ]. repeat split; rdn_solve. Qed.

Lemma FRH_lo : forall m s ret regs (x : word), (104 <= s)%Z -> (s < 2 ^ 64)%Z -> (u x < s - 104)%Z -> FRH m s ret regs x = m x.
Proof.
  intros m s ret regs x Hs Hs64 Hx. unfold FRH, FRD.
  rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia. reflexivity.
Qed.

Lemma null_mem_out : forall m pp (x : word), (0 <= pp)%Z -> (pp + 8 < 2 ^ 64)%Z -> ~ (pp <= u x < pp + 8)%Z ->
  O23LeptPma1.null_mem m pp x = m x.
Proof.
  intros m pp x H0 H1 Hx. unfold O23LeptPma1.null_mem.
  rewrite wbytes_outside; [reflexivity | rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ..].
Qed.

Lemma hmt_al16 : forall C A m md (p n : Z), W C A m md -> live A (Z_to_bv 64 p) = Some n -> (0 <= p < 2 ^ 64)%Z -> (p mod 16 = 0)%Z.
Proof.
  intros C A m md p n HW L Hp.
  destruct (ai_live_hull A m (m_vmmaps md) _ n (w_inv _ _ _ _ HW) L) as (_ & X & _). rewrite u_Z2bv in X by lia. exact X.
Qed.

Lemma hmt_blk_disj : forall C A m md (p q : word) n k, W C A m md -> live A p = Some n -> live A q = Some k -> p <> q ->
  (u p + n <= u q \/ u q + k <= u p)%Z.
Proof.
  intros C A m md p q n k HW Lp Lq NE.
  pose proof (ai_live_disjoint A m (m_vmmaps md) p n q k (w_inv _ _ _ _ HW) Lp Lq NE) as D.
  destruct (ai_live_hull A m (m_vmmaps md) p n (w_inv _ _ _ _ HW) Lp) as (Hn & _).
  destruct (ai_live_hull A m (m_vmmaps md) q k (w_inv _ _ _ _ HW) Lq) as (Hk & _).
  pose proof (round16_ge n Hn). pose proof (round16_ge k Hk). lia.
Qed.

Lemma hsm_lay : forall C s, Cok C -> (c_top C - LSTK + HMT_STACK <= s)%Z -> (s <= c_top C)%Z ->
  (alloc_top (c_vm C) + 8192 + 3744 <= s)%Z /\ (c_top C - LSTK + 3744 <= s)%Z /\ (s < 2 ^ 64)%Z.
Proof. intros C s CK H1 H2. pose proof CK as [T1 T2 T3 T4 T5]. unfold HMT_STACK in H1. lia. Qed.

Lemma hsm_PG_out : forall m (s w h : Z) (x : word), (112 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 112 <= u x < s - 104)%Z ->
  PGDH m s w h x = m x.
Proof.
  intros m s w h x Hs Hs64 Hx. unfold PGDH.
  rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity.
Qed.

Lemma hsm_M4_out : forall m (s w h sy sx cy cx : Z) (x : word), (160 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 128 <= u x < s - 104)%Z ->
  O23LeptSelGP.SGP4 (PGDH m s w h) (s - 120) (s - 116) (s - 128) (s - 124) sy sx cy cx x = m x.
Proof.
  intros m s w h sy sx cy cx x Hs Hs64 Hx.
  rewrite O23LeptSelGP.SGP4_out by (unfold O23LeptSelGP.cell_ok; lia). apply hsm_PG_out; lia.
Qed.

Section HSucc.
Variables (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s pixs sel w h cm datas : Z)
          (sv : selv) (c : Z -> Z -> Z) (cv : cmapv) (ret : word) (S : TSet)
          (kR bR : Z) (A1 : AS) (m2 : word -> option byte) (vm1 : VmMaps) (r2 : bvmap 5 word) (pixd cd data : Z).
Hypothesis CK : Cok C.
Hypothesis HW : W C A m md.
Hypothesis H2 : getr regs 2 = Z_to_bv 64 s.
Hypothesis Hs16 : (s mod 16 = 0)%Z.
Hypothesis Hlo : (c_top C - LSTK + HMT_STACK <= s)%Z.
Hypothesis Hhi : (s <= c_top C)%Z.
Hypothesis Hret : ret_ok ret.
Hypothesis PXs : PIXat m pixs (O23LeptPixCopyT.hdv w h 1 cm datas).
Hypothesis HDR : O23LeptPixHdr.hdr_ok w h 1.
Hypothesis Hw : (1 <= w)%Z.
Hypothesis Hh : (1 <= h)%Z.
Hypothesis Lps : live A (Z_to_bv 64 pixs) = Some 64%Z.
Hypothesis Lps0 : live (c_A0 C) (Z_to_bv 64 pixs) = None.
Hypothesis Ldatas : live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z.
Hypothesis SA : sel_at (alloc_top (c_vm C)) A m sel sv.
Hypothesis SC : sel_cont m sv c.
Hypothesis Hcx : (0 <= v_cx sv < v_sx sv)%Z.
Hypothesis Hcy : (0 <= v_cy sv < v_sy sv)%Z.
Hypothesis SBLK : forall p, sel_blk sel sv p -> Z_to_bv 64 p <> Z_to_bv 64 pixs.
Hypothesis HW2 : W C A1 m2 (with_vmmaps vm1 md).
Hypothesis PM2 : POSTM C A (s - 160) (O23LeptPma1.clone_mem (FRH m s ret regs) pixs (s - 152)) m2.
Hypothesis PN : O23LeptPixCopyT.pixt_new C A A1 m2 pixd w h 1 cd data cv.
Hypothesis R2 : getr r2 2 = Z_to_bv 64 (s - 160).
Hypothesis R9 : getr r2 9 = Z_to_bv 64 sel.
Hypothesis R18 : getr r2 18 = Z_to_bv 64 pixs.
Hypothesis R10 : getr r2 10 = Z_to_bv 64 pixd.
Hypothesis K34 : forall x, In x [3; 4]%list -> getr r2 x = getr regs x.
Hypothesis AR : aroom A1 vm1 (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm)).
Hypothesis HK : forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
  (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ O23LeptPixCopyT.pixt_new C A A' m' pixd w h 1 cd data cv /\ POSTM C A s m m') ->
  aroom A' vm' (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm)) ->
  realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S.

Local Abbreviation md1 := (with_vmmaps vm1 md).
Local Abbreviation vs := (set_rc (O23LeptPixCopyT.hdv w h 1 cm datas) 2).
Local Abbreviation vd := (O23LeptPixCopyT.hdv w h 1 cd data).
Local Abbreviation nd := (4 * (wpl_of w 1 * h))%Z.
Local Abbreviation M4 := (O23LeptSelGP.SGP4 (PGDH m2 s w h) (s - 120) (s - 116) (s - 128) (s - 124) (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv)).

Definition HSM (M : word -> option byte) : Prop :=
  cellsZ M (frH s ret regs) /\ FRM C s m M /\
  (forall q k i, live A q = Some k -> q <> Z_to_bv 64 pixs -> (0 <= i < k)%Z -> M (at_ q i) = m (at_ q i)) /\
  (forall q k (x : word), live A1 q = Some k -> live A q = None -> q <> Z_to_bv 64 data -> (u q <= u x < u q + k)%Z -> M x = m2 x) /\
  PIXat M pixs vs /\ rdn SEGS M (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 pixs).

Lemma hs_x_lt : forall Ax mx mdx q k (x : word), W C Ax mx mdx -> live Ax q = Some k -> (u q <= u x < u q + k)%Z ->
  (u x < alloc_top (c_vm C))%Z.
Proof.
  intros Ax mx mdx q k x HWx Lq Hx.
  pose proof (blk_byte C Ax mx mdx q k x CK HWx Lq Hx) as [[_ HG] _]. exact HG.
Qed.


Lemma hs_at_lt : forall Ax mx mdx q k i, W C Ax mx mdx -> live Ax q = Some k -> (0 <= i < k)%Z ->
  (u q <= u (at_ q i) < u q + k)%Z /\ (u (at_ q i) < alloc_top (c_vm C))%Z.
Proof.
  intros Ax mx mdx q k i HWx Lq Hi.
  pose proof (blk_range C Ax mx mdx q k CK HWx Lq ltac:(lia)) as [B1 B2].
  pose proof (u64_range (c_sp0 C)) as SP. pose proof CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val as LV.
  rewrite at_u by lia. lia.
Qed.


Lemma hs_top : (alloc_top (c_vm C) + 8192 + LSTK <= c_top C)%Z /\ (s < 2 ^ 64)%Z /\ (c_top C - LSTK + 160 <= s)%Z /\
  (4096 <= alloc_top (c_vm C))%Z.
Proof.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof (u64_range (c_sp0 C)) as SP. pose proof LSTK_val as LV.
  pose proof (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [B1 B2].
  unfold HMT_STACK in Hlo. lia.
Qed.


Lemma HSM_2 : HSM m2.
Proof.
  pose proof hs_top as [TP [S64 [SB AT]]]. pose proof LSTK_val as LV.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof (u64_range (c_sp0 C)) as SP.
  pose proof PXs as (P0 & P64 & _).
  pose proof (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [B1 B2].
  rewrite ?u_Z2bv in B1, B2 by lia.
  unfold HMT_STACK in Hlo.
  destruct (FRH_WP C A m md s s ret regs CK HW ltac:(lia) ltac:(lia) ltac:(lia)) as [HWF [FRF LKF]].
  pose proof PM2 as [FR2 LK2].
  assert (CLO : forall x : word, ~ (pixs + 20 <= u x < pixs + 24)%Z -> ~ (s - 152 <= u x < s - 144)%Z ->
            O23LeptPma1.clone_mem (FRH m s ret regs) pixs (s - 152) x = FRH m s ret regs x).
  { intros x X1 X2. unfold O23LeptPma1.clone_mem.
    rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?length_Z_to_le_bytes, ?u_Z2bv by lia; lia).
    rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?length_Z_to_le_bytes, ?u_Z2bv by lia; lia).
    reflexivity. }
  split; [| split; [| split; [| split; [| split]]]].
  - assert (CZ1 : cellsZ (O23LeptPma1.clone_mem (FRH m s ret regs) pixs (s - 152)) (frH s ret regs)).
    { eapply (frH_out (FRH m s ret regs) _ (pixs + 20) (s - 144)); [| lia | lia | lia | apply frH_FRH; lia].
      intros x Hx. apply CLO; lia. }
    eapply frH_frm; [exact CK | exact FR2 | lia | lia | lia | exact CZ1].
  - eapply FRM_trans; [exact FRF |]. eapply FRM_trans; [| eapply FRM_mono; [exact FR2 | lia]].
    intros a NH NG NE NC NS. apply CLO.
    + intro X. apply NH. exact (proj1 (blk_byte C A m md (Z_to_bv 64 pixs) 64 a CK HW Lps ltac:(rewrite u_Z2bv by lia; lia))).
    + intro X. apply NS. unfold scratch. lia.
  - intros q k i Lq Nq Hi. pose proof (hs_at_lt A m md q k i HW Lq Hi) as [HR HA].
    pose proof (hmt_blk_disj C A m md q (Z_to_bv 64 pixs) k 64 HW Lq Lps Nq) as D. rewrite u_Z2bv in D by lia.
    rewrite (LK2 q k i Lq Hi), CLO by lia. exact (LKF q k i Lq Hi).
  - intros; reflexivity.
  - assert (PXF : PIXat (FRH m s ret regs) pixs (O23LeptPixCopyT.hdv w h 1 cm datas)).
    { eapply PIXat_frame; [exact PXs |]. intros x Hx.
      apply (LIVK_in A m _ pixs 64 x LKF Lps); lia. }
    pose proof (O23LeptPma1.PIXat_clone_mem (FRH m s ret regs) pixs (s - 152) _ PXF ltac:(lia) ltac:(lia) ltac:(lia)) as PXC.
    eapply PIXat_frame; [exact PXC |]. intros x Hx.
    apply (LIVK_in A _ _ pixs 64 x LK2 Lps); lia.
  - pose proof (FRM_rdn_above C (s - 160) _ m2 (s - 152) 8 CK FR2 ltac:(lia) ltac:(lia) ltac:(lia)) as RA.
    first [rewrite p16_segs in RA | rewrite <- p16_segs in RA]. rewrite RA.
    apply rdn_clone_mem_cell; lia.
Qed.



Lemma HSM_win : forall M M' (lo hi : Z), HSM M -> (forall x : word, ~ (lo <= u x < hi)%Z -> M' x = M x) ->
  (s - 144 <= lo)%Z -> (hi <= s - 104)%Z -> HSM M'.
Proof.
  intros M M' lo hi [HC [HF [HL [HN [HP HS]]]]] EQ Hlo' Hhi'.
  pose proof hs_top as [TP [S64 [SB AT]]]. pose proof LSTK_val as LV.
  pose proof PXs as (P0 & P64 & _).
  split; [| split; [| split; [| split; [| split]]]].
  - assert (EQ2 : forall x : word, ~ (lo <= u x < s - 104)%Z -> M' x = M x) by (intros x Hx; apply EQ; lia).
    eapply frH_out; [exact EQ2 | lia | lia | lia | exact HC].
  - intros a NH NG NE NC NS. rewrite EQ; [apply HF; assumption |].
    intro Wn. apply NS. unfold scratch. lia.
  - intros q k i Lq Nq Hi. pose proof (hs_at_lt A m md q k i HW Lq Hi) as [_ HA].
    rewrite EQ; [exact (HL q k i Lq Nq Hi) | lia].
  - intros q k x L1 L0 Nq Hx. pose proof (hs_x_lt A1 m2 md1 q k x HW2 L1 Hx) as HA.
    rewrite EQ; [exact (HN q k x L1 L0 Nq Hx) | lia].
  - eapply PIXat_frame; [exact HP |]. intros x Hx.
    pose proof (hs_x_lt A m md (Z_to_bv 64 pixs) 64 x HW Lps ltac:(rewrite u_Z2bv by lia; lia)) as HA.
    apply EQ. lia.
  - rewrite <- HS. apply rdn_ext; [rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. apply EQ. lia.
Qed.


Lemma HSM_df : forall M M', HSM M -> O23LeptDilW.dil_frame C (s - 152) data nd M M' -> HSM M'.
Proof.
  intros M M' [HC [HF [HL [HN [HP HS]]]]] DF.
  pose proof hs_top as [TP [S64 [SB AT]]]. pose proof LSTK_val as LV.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof (u64_range (c_sp0 C)) as SP.
  pose proof PXs as (P0 & P64 & _).
  pose proof PN as (PD1 & PD2 & PD3 & DA1 & DA2 & DA3 & DNE & LA0 & LAd0 & L00 & Ld00 & L1p & L1d & PXd & CMR).
  destruct (ai_live_hull A1 m2 (m_vmmaps (with_vmmaps vm1 md)) (Z_to_bv 64 data) _ (w_inv _ _ _ _ HW2) L1d) as (Hnd & _).
  pose proof (O23LeptDilW.pixt_sub1 _ _ _ _ _ _ _ _ _ _ _ PN) as SUB.
  assert (DFX : forall x : word, ~ (c_top C - LSTK <= u x < s - 152)%Z -> ~ (data <= u x < data + nd)%Z -> M' x = M x)
    by (intros x X1 X2; apply DF; [unfold scratch; lia | exact X2]).
  assert (FR : FRM C (s - 152) M M').
  { intros a NH NG NE NC NS. apply DFX; [intro X; apply NS; unfold scratch; lia |].
    intro X. apply NH. exact (proj1 (blk_byte C A1 m2 (with_vmmaps vm1 md) (Z_to_bv 64 data) nd a CK HW2 L1d ltac:(rewrite u_Z2bv by lia; lia))). }
  split; [| split; [| split; [| split; [| split]]]].
  - eapply frH_frm; [exact CK | exact FR | lia | lia | lia | exact HC].
  - eapply FRM_trans; [exact HF | eapply FRM_mono; [exact FR | lia]].
  - intros q k i Lq Nq Hi. pose proof (hs_at_lt A m md q k i HW Lq Hi) as [HR HA].
    assert (NEq : q <> Z_to_bv 64 data) by (intro E; rewrite E in Lq; rewrite LAd0 in Lq; discriminate).
    pose proof (hmt_blk_disj C A1 m2 (with_vmmaps vm1 md) q (Z_to_bv 64 data) k nd HW2 (SUB q k Lq) L1d NEq) as D. rewrite u_Z2bv in D by lia.
    rewrite DFX; [exact (HL q k i Lq Nq Hi) | lia | lia].
  - intros q k x L1 L0 Nq Hx. pose proof (hs_x_lt A1 m2 (with_vmmaps vm1 md) q k x HW2 L1 Hx) as HA.
    pose proof (hmt_blk_disj C A1 m2 (with_vmmaps vm1 md) q (Z_to_bv 64 data) k nd HW2 L1 L1d Nq) as D. rewrite u_Z2bv in D by lia.
    rewrite DFX; [exact (HN q k x L1 L0 Nq Hx) | lia | lia].
  - assert (NEq : Z_to_bv 64 pixs <> Z_to_bv 64 data) by (intro E; rewrite E in Lps; rewrite LAd0 in Lps; discriminate).
    pose proof (hmt_blk_disj C A1 m2 (with_vmmaps vm1 md) (Z_to_bv 64 pixs) (Z_to_bv 64 data) 64 nd HW2 (SUB _ _ Lps) L1d NEq) as D.
    rewrite !u_Z2bv in D by lia.
    eapply PIXat_frame; [exact HP |]. intros x Hx.
    pose proof (hs_x_lt A m md (Z_to_bv 64 pixs) 64 x HW Lps ltac:(rewrite u_Z2bv by lia; lia)) as HA.
    apply DFX; lia.
  - rewrite <- HS. apply rdn_ext; [rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. apply DFX; lia.
Qed.


Lemma HSM_post : forall M M' (s' : Z), HSM M -> POSTM C A1 s' M M' -> (c_top C - LSTK <= s')%Z -> (s' <= s - 152)%Z -> HSM M'.
Proof.
  intros M M' s' (CE & FR & KA & KN & PX & SL) [F' L'] H1 H3.
  destruct (hsm_lay C s CK Hlo Hhi) as (_ & _ & S64).
  pose proof (O23LeptDilW.pixt_sub1 _ _ _ _ _ _ _ _ _ _ _ PN) as SUB.
  pose proof PX as (P0 & P64 & _).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - exact (frH_frm C s' M M' s ret regs CK F' H1 ltac:(lia) S64 CE).
  - exact (FRM_trans C s m M M' FR (FRM_mono C s' s M M' F' ltac:(lia))).
  - intros q k i Lq NE Hi. rewrite (L' q k i (SUB q k Lq) Hi). exact (KA q k i Lq NE Hi).
  - intros q k x Lq L0 NE Hx. rewrite (LeptSlots.LIVK_byte A1 M M' q k x L' Lq Hx). exact (KN q k x Lq L0 NE Hx).
  - apply (PIXat_frame M); [exact PX |]. intros x Hx. exact (LIVK_in A1 M M' pixs 64 x L' (SUB _ _ Lps) P0 P64 Hx).
  - rewrite (FRM_rdn16 C s' M M' (s - 152) 8 CK F') by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact SL.
Qed.


Lemma hsl_rng : forall p, sel_blk sel sv p -> (1 <= p)%Z /\ (p < alloc_top (c_vm C))%Z.
Proof.
  intros p B. pose proof SA as (Hsy & Hsx & Bsel & Lsel & RC & Bdat & Ldat & Nds & ROWS & _). unfold bok in Bsel, Bdat.
  destruct B as [E | [E | (i & Hi & E)]]; subst p; [lia | lia |].
  destruct (ROWS i Hi) as (Br & _). unfold bok in Br. lia.
Qed.

Lemma hsl_pt : forall M p k (x : word), HSM M -> sel_blk sel sv p -> live A (Z_to_bv 64 p) = Some k -> (p <= u x < p + k)%Z -> M x = m x.
Proof.
  intros M p k x HS B L Hx. destruct HS as (_ & _ & KA & _).
  destruct (hsl_rng p B) as [P1 P2]. destruct (hsm_lay C s CK Hlo Hhi) as (Hs0 & Hs1 & Hs64).
  pose proof (KA (Z_to_bv 64 p) k (u x - p)%Z L (SBLK p B) ltac:(lia)) as K.
  replace (at_ (Z_to_bv 64 p) (u x - p)%Z) with x in K; [exact K |].
  unfold at_. rewrite u_Z2bv by lia. replace (p + (u x - p))%Z with (u x) by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma HSM_sel : forall M, HSM M -> sel_at (alloc_top (c_vm C)) A1 M sel sv /\ sel_cont M sv c.
Proof.
  intros M HS. destruct (hsm_lay C s CK Hlo Hhi) as (Hs0 & Hs1 & Hs64).
  pose proof (O23LeptDilW.pixt_sub1 _ _ _ _ _ _ _ _ _ _ _ PN) as SUB.
  split.
  - apply (O23LeptHmtNW.sel_at_pw (alloc_top (c_vm C)) A A1 m M sel sv ltac:(lia) SA SUB).
    intros p k x B L Hx. exact (hsl_pt M p k x HS B L Hx).
  - intros i j Hi Hj. destruct (SC i j Hi Hj) as [Rg Rd]. split; [exact Rg |].
    pose proof SA as (_ & _ & _ & _ & _ & _ & _ & _ & ROWS & _).
    destruct (ROWS i Hi) as (Br & Lr & _). unfold bok in Br.
    rewrite <- Rd. apply rdn_ext; [rewrite u_Z2bv by lia; lia |].
    intros x Hx. rewrite u_Z2bv in Hx by lia.
    apply (hsl_pt M (v_rows sv i) (4 * v_sx sv) x HS ltac:(unfold sel_blk; right; right; exists i; split; [exact Hi | reflexivity]) Lr).
    lia.
Qed.


Lemma frH_keep : forall (M M' : word -> option byte) (t : Z) (rt : word) (r0 : bvmap 5 word), (104 <= t)%Z -> (t < 2 ^ 64)%Z ->
  (forall x : word, (t - 104 <= u x < t)%Z -> M' x = M x) -> cellsZ M (frH t rt r0) -> cellsZ M' (frH t rt r0).
Proof.
  intros M M' t rt r0 H0 H1 K CE. apply (cellsZ_keep M M' _); [| exact CE].
  unfold frH. repeat constructor; cbn [fst]; first [lia | intros x Hx; apply K; lia].
Qed.

Lemma hs_fin_ar : (160 <= s)%Z /\ (s < 2 ^ 64)%Z /\ (alloc_top (c_vm C) + 11936 <= s)%Z /\ (c_top C - LSTK + 3744 <= s)%Z /\
  (4096 <= pixs)%Z /\ (pixs + 64 <= alloc_top (c_vm C))%Z.
Proof.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (Hlo' : (c_top C - LSTK + 3744 <= s)%Z) by (unfold HMT_STACK in Hlo; lia).
  pose proof PXs as (Hp0 & Hp64 & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [G1 G2]. rewrite u_Z2bv in G1, G2 by lia.
  lia.
Qed.

Lemma hs_fin_heap : forall (m7 m8 : word -> option byte) q k (x : word),
  (forall x : word, (u x < s - 160 - 32 \/ s - 160 <= u x)%Z -> ~ (pixs + 20 <= u x < pixs + 24)%Z -> ~ inslot (s - 152) x -> m8 x = m7 x) ->
  live A1 q = Some k -> q <> Z_to_bv 64 pixs -> (u q <= u x < u q + k)%Z -> m8 x = m7 x.
Proof.
  intros m7 m8 q k x OUT Lq Hq Hx.
  destruct hs_fin_ar as (Hs160 & Hs64 & Ha & Hb & Hp0 & Hp1).
  pose proof (O23LeptDilW.pixt_sub1 _ _ _ _ _ _ _ _ _ _ _ PN _ _ Lps) as Lps1.
  destruct (blk_range C A1 m2 md1 q k CK HW2 Lq ltac:(lia)) as [G1 G2].
  pose proof (hmt_blk_disj C A1 m2 md1 q (Z_to_bv 64 pixs) k 64 HW2 Lq Lps1 Hq) as DJ. rewrite u_Z2bv in DJ by lia.
  apply OUT; [left; lia | lia | unfold inslot; lia].
Qed.

Lemma hs_fin : forall m7 m8, HSM m7 -> PIXat m8 pixs (set_rc vs 1) ->
  (forall x : word, (u x < s - 160 - 32 \/ s - 160 <= u x)%Z -> ~ (pixs + 20 <= u x < pixs + 24)%Z -> ~ inslot (s - 152) x -> m8 x = m7 x) ->
  cellsZ m8 (frH s ret regs) /\ O23LeptPixCopyT.pixt_new C A A1 m8 pixd w h 1 cd data cv /\ POSTM C A s m m8.
Proof.
  intros m7 m8 HS7 PX8 OUT.
  destruct hs_fin_ar as (Hs160 & Hs64 & Ha & Hb & Hp0 & Hp1).
  pose proof HS7 as HS7'. unfold HSM in HS7'. destruct HS7' as (CE7 & F7 & K7 & N7 & PX7 & RD7).
  pose proof PN as PN'. unfold O23LeptPixCopyT.pixt_new in PN'.
  destruct PN' as (Hq0 & Hq1 & _ & Hd0 & Hd1 & _ & Hne & LApd & _ & _ & _ & L1pd & _ & PXd & _).
  assert (Hdr : (0 <= data < 2 ^ 64)%Z).
  { pose proof (O23LeptDilW.wpl1_le w Hw) as Wp.
    assert (Hwh : (0 <= wpl_of w 1 * h)%Z) by (apply Z.mul_nonneg_nonneg; lia). lia. }
  assert (NB : forall q k (x : word), live A1 q = Some k -> live A q = None -> q <> Z_to_bv 64 data -> (u q <= u x < u q + k)%Z -> m8 x = m2 x).
  { intros q k x Lq L0 Hd Hx. assert (Hq : q <> Z_to_bv 64 pixs) by (intros Q; subst q; rewrite Lps in L0; discriminate L0).
    rewrite (hs_fin_heap m7 m8 q k x OUT Lq Hq Hx). exact (N7 q k x Lq L0 Hd Hx). }
  split; [| split].
  - apply (frH_keep m7 m8 s ret regs ltac:(lia) Hs64); [| exact CE7].
    intros x Hx. apply OUT; [right; lia | lia | unfold inslot; lia].
  - apply (O23LeptDilW.pixt_keep C A A1 m2 m8 pixd w h 1 cd data cv PN Hdr); [| exact NB].
    apply (PIXat_frame m2); [exact PXd |]. intros x Hx.
    apply (NB (Z_to_bv 64 pixd) 64%Z x L1pd LApd); [| rewrite u_Z2bv by lia; lia].
    intros E. apply Hne. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. exact E.
  - unfold POSTM. split.
    + eapply FRM_trans; [exact F7 |]. intros a NH NG NE NC NS. unfold scratch in NS. apply OUT.
      * lia.
      * intros Hp. apply NH. exact (proj1 (blk_byte C A m md (Z_to_bv 64 pixs) 64 a CK HW Lps ltac:(rewrite u_Z2bv by lia; lia))).
      * unfold inslot. lia.
    + intros q k i Lq Hi.
      destruct (blk_range C A m md q k CK HW Lq ltac:(lia)) as [G1 G2].
      assert (Hat : u (at_ q i) = (u q + i)%Z) by (unfold at_; apply u_Z2bv; lia).
      destruct (Z.eq_dec (u q) pixs) as [E | NE].
      * assert (Q : q = Z_to_bv 64 pixs) by (apply bv_eq; rewrite u_Z2bv by lia; exact E). subst q.
        rewrite Lps in Lq. injection Lq as Hk. subst k.
        pose proof PX8 as PX8'. rewrite O23LeptDilW.hdv_rc in PX8'.
        apply (O23LeptDilW.pix_same m m8 pixs _ PXs PX8'). rewrite Hat, E. lia.
      * assert (Hq : q <> Z_to_bv 64 pixs) by (intros Q; subst q; rewrite u_Z2bv in NE by lia; exact (NE eq_refl)).
        rewrite (hs_fin_heap m7 m8 q k (at_ q i) OUT (O23LeptDilW.pixt_sub1 _ _ _ _ _ _ _ _ _ _ _ PN _ _ Lq) Hq ltac:(rewrite Hat; lia)).
        exact (K7 q k i Lq Hq Hi).
Qed.


Lemma hsr_pt : forall M (q : word) k (x : word), O23LeptDilW.dil_frame C (s - 152) data nd M4 M ->
  live A1 q = Some k -> q <> Z_to_bv 64 data -> (u q <= u x < u q + k)%Z -> M x = m2 x.
Proof.
  intros M q k x DF Lq NE Hx. destruct (hsm_lay C s CK Hlo Hhi) as (Hs0 & Hs1 & Hs64). pose proof CK as [T1 _ _ _ _].
  pose proof PN as (Pd1 & Pd2 & Pd3 & Pa1 & Pa2 & Pa3 & Pne & LAd & LAa & L0d & L0a & L1d & L1a & _).
  pose proof (O23LeptDilW.wpl1_le w Hw) as WPL. assert (NDp : (0 <= wpl_of w 1 * h)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  pose proof (blk_range C A1 m2 md1 q k CK HW2 Lq ltac:(lia)) as [Q1 Q2].
  pose proof (hmt_blk_disj C A1 m2 md1 q _ k _ HW2 Lq L1a NE) as D. rewrite u_Z2bv in D by lia.
  rewrite DF.
  - apply hsm_M4_out; lia.
  - unfold scratch. lia.
  - lia.
Qed.

Lemma hsr_rdn : forall M (q : word) k (b : Z) (n : nat), O23LeptDilW.dil_frame C (s - 152) data nd M4 M ->
  live A1 q = Some k -> q <> Z_to_bv 64 data -> (0 < k)%Z -> (u q <= b)%Z -> (b + Z.of_nat n <= u q + k)%Z ->
  rdn SEGS M (Z_to_bv 64 b) n = rdn SEGS m2 (Z_to_bv 64 b) n.
Proof.
  intros M q k b n DF Lq NE Hk Hb1 Hb2. destruct (hsm_lay C s CK Hlo Hhi) as (Hs0 & Hs1 & Hs64).
  pose proof (blk_range C A1 m2 md1 q k CK HW2 Lq Hk) as [Q1 Q2].
  apply rdn_ext; [rewrite u_Z2bv by lia; lia |]. intros x Hx. rewrite u_Z2bv in Hx by lia.
  apply (hsr_pt M q k x DF Lq NE). lia.
Qed.

Lemma hsr_stk : forall M (b : Z) (n : nat), O23LeptDilW.dil_frame C (s - 152) data nd M4 M ->
  (s - 152 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> rdn SEGS M (Z_to_bv 64 b) n = rdn SEGS M4 (Z_to_bv 64 b) n.
Proof.
  intros M b n DF Hb1 Hb2. destruct (hsm_lay C s CK Hlo Hhi) as (Hs0 & Hs1 & Hs64).
  pose proof PN as (Pd1 & Pd2 & Pd3 & Pa1 & Pa2 & Pa3 & _).
  pose proof (O23LeptDilW.wpl1_le w Hw) as WPL. assert (NDp : (0 <= wpl_of w 1 * h)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  apply rdn_ext; [rewrite u_Z2bv by lia; lia |]. intros x Hx. rewrite u_Z2bv in Hx by lia.
  apply DF; [unfold scratch | ]; lia.
Qed.

Lemma hs_reads : forall M, O23LeptDilW.dil_frame C (s - 152) data nd M4 M -> hmt_reads M s sel pixd pixs sv c vd vs.
Proof.
  intros M DF. destruct (hsm_lay C s CK Hlo Hhi) as (Hs0 & Hs1 & Hs64). pose proof CK as [T1 _ _ _ _].
  pose proof (O23LeptDilW.pixt_sub1 _ _ _ _ _ _ _ _ _ _ _ PN) as SUB.
  pose proof PN as (Pd1 & Pd2 & Pd3 & Pa1 & Pa2 & Pa3 & Pne & LAd & LAa & L0d & L0a & L1d & L1a & PXd & _).
  pose proof HSM_2 as (_ & _ & _ & _ & PX2 & SL2).
  destruct (HSM_sel m2 HSM_2) as [SA1 SC2].
  pose proof SA1 as (Hsy & Hsx & Bs & Ls1 & RC & Bd & Ld1 & Nd & Hrows & _).
  pose proof SA as (_ & _ & _ & Ls & _ & _ & Ld & _ & HrowsA & _).
  unfold bok in Bs, Bd.
  pose proof PXs as (Ps0 & Ps1 & _ & _).
  pose proof HDR as (_ & Hw1 & Hh1 & _).
  pose proof (O23LeptDilW.wpl1_le w Hw) as WPL. assert (NDp : (0 <= wpl_of w 1 * h)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (NEA : forall (q : word) k, live A q = Some k -> q <> Z_to_bv 64 data) by (intros q k Lq E; rewrite E in Lq; congruence).
  assert (CO : forall a, (s - 128 <= a)%Z -> (a + 4 <= s - 112)%Z -> O23LeptSelGP.cell_ok a) by (intros a Ha1 Ha2; unfold O23LeptSelGP.cell_ok; lia).
  destruct (V23LeptSelGP.SGP4_rd (PGDH m2 s w h) (s - 120) (s - 116) (s - 128) (s - 124) (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv)
              (CO (s - 120)%Z ltac:(lia) ltac:(lia)) (CO (s - 116)%Z ltac:(lia) ltac:(lia)) (CO (s - 128)%Z ltac:(lia) ltac:(lia)) (CO (s - 124)%Z ltac:(lia) ltac:(lia))
              ltac:(unfold O23LeptSelGP.cell_apart; lia) ltac:(unfold O23LeptSelGP.cell_apart; lia)
              ltac:(unfold O23LeptSelGP.cell_apart; lia) ltac:(unfold O23LeptSelGP.cell_apart; lia)
              ltac:(unfold O23LeptSelGP.cell_apart; lia) ltac:(unfold O23LeptSelGP.cell_apart; lia)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (RS1 & RS2 & RS3 & RS4).
  assert (M4PG : forall b (n : nat), (s - 112 <= b)%Z -> (b + Z.of_nat n <= s - 104)%Z ->
            rdn SEGS M4 (Z_to_bv 64 b) n = rdn SEGS (PGDH m2 s w h) (Z_to_bv 64 b) n).
  { intros b n Hb1 Hb2. apply rdn_ext; [rewrite u_Z2bv by lia; lia |]. intros x Hx. rewrite u_Z2bv in Hx by lia.
    apply O23LeptSelGP.SGP4_out; try (apply CO; lia); lia. }
  unfold hmt_reads. split.
  { rewrite (hsr_rdn M (Z_to_bv 64 sel) 32 (sel + 16) 8 DF Ls1 (NEA _ _ Ls) ltac:(lia) ltac:(rewrite u_Z2bv by lia; lia)
               ltac:(rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
    exact (REC_rd' SEGS m2 sel _ 4 8 (Z_to_bv 64 (sel + 16)) (v_data sv) RC ltac:(cbn; lia) eq_refl ltac:(f_equal; cbn; lia) eq_refl). }
  split.
  { intros i Hi. destruct (Hrows i Hi) as (Br & Lr & NErd & NErs & BA). unfold bok in Br.
    rewrite (hsr_rdn M (Z_to_bv 64 (v_data sv)) (8 * v_sy sv) (v_data sv + 8 * i) 8 DF Ld1 (NEA _ _ Ld) ltac:(lia)
                 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
    pose proof (bytes_at_rdn SEGS m2 (v_data sv + 8 * i) (Z_to_le_bytes 8 (v_rows sv i)) ltac:(lia)
      ltac:(rewrite length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) BA) as R.
    rewrite length_Z_to_le_bytes in R. exact R. }
  split.
  { intros i j Hi Hj. destruct (Hrows i Hi) as (Br & Lr & _). destruct (HrowsA i Hi) as (_ & LrA & _). unfold bok in Br.
    rewrite (hsr_rdn M (Z_to_bv 64 (v_rows sv i)) (4 * v_sx sv) (v_rows sv i + 4 * j) 4 DF Lr (NEA _ _ LrA) ltac:(lia)
                 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
    exact (proj2 (SC2 i j Hi Hj)). }
  split.
  { rewrite (hsr_stk M (s - 152) 8 DF ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
    rewrite <- SL2. apply rdn_ext; [rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. apply hsm_M4_out; lia. }
  split.
  { rewrite (hsr_stk M (s - 128) 4 DF ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)). exact RS3. }
  split.
  { rewrite (hsr_stk M (s - 124) 4 DF ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)). exact RS4. }
  split.
  { rewrite (hsr_stk M (s - 120) 4 DF ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)). exact RS1. }
  split.
  { rewrite (hsr_stk M (s - 116) 4 DF ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)). exact RS2. }
  split.
  { rewrite (hsr_stk M (s - 112) 4 DF ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
    rewrite (M4PG (s - 112)%Z 4%nat ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
    change (PGDH m2 s w h) with (O23LeptSelGP.wr4 (O23LeptSelGP.wr4 (O23LeptSelGP.wr4 (O23LeptSelGP.wr4 m2 (s - 108) 0) (s - 112) 0) (s - 108) w) (s - 112) h).
    apply V23LeptSelGP.wr4_rd_hit; cbn [p_h O23LeptPixCopyT.hdv]; lia. }
  split.
  { rewrite (hsr_stk M (s - 108) 4 DF ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
    rewrite (M4PG (s - 108)%Z 4%nat ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
    change (PGDH m2 s w h) with (O23LeptSelGP.wr4 (O23LeptSelGP.wr4 (O23LeptSelGP.wr4 (O23LeptSelGP.wr4 m2 (s - 108) 0) (s - 112) 0) (s - 108) w) (s - 112) h).
    rewrite V23LeptSelGP.wr4_rd_out by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    apply V23LeptSelGP.wr4_rd_hit; cbn [p_w O23LeptPixCopyT.hdv]; lia. }
  split.
  { apply (PIXat_frame m2 M pixd vd PXd). intros x Hx.
    assert (NEd : Z_to_bv 64 pixd <> Z_to_bv 64 data)
      by (intro E; apply Pne; apply (f_equal bv_unsigned) in E; rewrite !u_Z2bv in E by lia; exact E).
    apply (hsr_pt M (Z_to_bv 64 pixd) 64 x DF L1d NEd). rewrite u_Z2bv by lia. lia. }
  { apply (PIXat_frame m2 M pixs vs PX2). intros x Hx.
    apply (hsr_pt M (Z_to_bv 64 pixs) 64 x DF (SUB _ _ Lps) (NEA _ _ Lps)). rewrite u_Z2bv by lia. lia. }
Qed.

Lemma hs_HCM : (p_cmap vd <> 0)%Z -> exists cv', live A1 (Z_to_bv 64 (p_cmap vd)) = Some 24%Z /\
  (forall M, O23LeptDilW.dil_frame C (s - 152) data nd M4 M -> CMAPat M (p_cmap vd) cv').
Proof.
  intros NZ. destruct (hsm_lay C s CK Hlo Hhi) as (Hs0 & Hs1 & Hs64). pose proof CK as [T1 _ _ _ _].
  pose proof PN as (Pd1 & Pd2 & Pd3 & Pa1 & Pa2 & Pa3 & Pne & LAd & LAa & L0d & L0a & L1d & L1a & PXd & CMR).
  cbn [p_cmap O23LeptPixCopyT.hdv] in NZ |- *.
  destruct CMR as [[E _] | (ad & CO & C1 & C2 & C3 & C4 & N1 & N2 & N3 & N4 & N5 & LA1 & LA2 & L01 & L02 & L1c & L1ad & CM & REST)];
    [lia |].
  exists (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0). split; [exact L1c |].
  intros M DF. apply (CMAPat_frame m2 M cd _ CM). intros x Hx.
  pose proof (O23LeptDilW.wpl1_le w Hw) as WPL. assert (NDp : (0 <= wpl_of w 1 * h)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Dj : (cd + 24 <= data \/ data + 4 * (wpl_of w 1 * h) <= cd)%Z).
  { assert (NE : Z_to_bv 64 cd <> Z_to_bv 64 data)
      by (intro E; apply N3; apply (f_equal bv_unsigned) in E; rewrite !u_Z2bv in E by lia; exact E).
    pose proof (hmt_blk_disj C A1 m2 md1 _ _ _ _ HW2 L1c L1a NE) as D. rewrite !u_Z2bv in D by lia. exact D. }
  rewrite DF.
  - apply hsm_M4_out; lia.
  - unfold scratch. lia.
  - lia.
Qed.

Lemma hs_kx_side : (160 <= s)%Z /\ (s < 2 ^ 64)%Z /\ (c_top C - LSTK + 32 <= s - 160)%Z /\ (s - 160 <= c_top C)%Z /\
  slotok C A1 (s - 160) (s - 152) None /\ (0 <= pixd < 2 ^ 64)%Z.
Proof.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (Hlo' : (c_top C - LSTK + 3744 <= s)%Z) by (unfold HMT_STACK in Hlo; lia).
  pose proof PN as PN'. unfold O23LeptPixCopyT.pixt_new, PIXat in PN'.
  destruct PN' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hpd0 & Hpd64 & _) & _).
  cbn [slotok]. lia.
Qed.

Lemma hs_KX : forall m7 r7, HSM m7 -> W C A1 m7 md1 -> getr r7 2 = Z_to_bv 64 (s - 160) -> getr r7 8 = Z_to_bv 64 pixd ->
  hmt_keep regs r7 -> realizes SEGS (mkCfg (mkst r7 (0xa23d0 : word) m7 al_rom) md1) S.
Proof.
  intros m7 r7 HS7 HW7 Q2 Q8 KP. unfold hmt_keep in KP.
  destruct hs_kx_side as (Hs160 & Hs64 & Hlo1 & Hhi1 & SL1 & Hpd).
  pose proof HS7 as HS7'. unfold HSM in HS7'. destruct HS7' as (_ & _ & _ & _ & PX7 & RD7).
  destruct (hm_F al_rom r7 m7 s Hs160 Hs64 Q2) as (r8 & RUN8 & F1 & F10 & AG8).
  pc_as RUN8. rzs HW7 RUN8.
  apply (pixDestroy_dec_W C A1 m7 md1 r8 (s - 160) (s - 152) pixs vs None _ S CK HW7
           ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) Hlo1 Hhi1
           F1 ltac:(red; apply bv_eq; reflexivity) F10 SL1 ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) RD7 PX7
           eq_refl (O23LeptDilW.pixt_sub1 _ _ _ _ _ _ _ _ _ _ _ PN _ _ Lps) Lps0 ltac:(intros p k E; discriminate E)).
  intros m8 r9 HW8 CS9 PX8 _ OUT8 _.
  destruct (hs_fin m7 m8 HS7 PX8 OUT8) as (CE8 & PT8 & PM8).
  cbn [cellsZ frH] in CE8. destruct CE8 as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & _).
  destruct (hm_Z al_rom r9 m8 s pixd ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
              (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) Hs160 Hs64 Hpd Hret
              E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r10 & RUN10 & Z2 & Z10 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27 & AG10).
  pc_as RUN10. rzs HW8 RUN10.
  apply (HK A1 m8 vm1 r10 HW8).
  - apply cs_kept_intro; csr; reflexivity.
  - exists pixd, cd, data. exact (conj Z10 (conj PT8 PM8)).
  - exact AR.
Qed.


Lemma hs_sb : (160 <= s)%Z /\ (s < 2 ^ 64)%Z /\ (alloc_top (c_vm C) + 8192 + 3744 <= s)%Z /\ (c_top C - LSTK + 3744 <= s)%Z.
Proof.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold HMT_STACK in Hlo. lia.
Qed.

Lemma hs_M4o : forall x : word, ~ (s - 128 <= u x < s - 104)%Z -> M4 x = m2 x.
Proof.
  intros x Hx. destruct hs_sb as (S0 & S1 & _).
  rewrite O23LeptSelGP.SGP4_out by (first [unfold O23LeptSelGP.cell_ok; split; lia | lia]).
  unfold PGDH. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia.
  reflexivity.
Qed.

Lemma hs_HSM4 : HSM M4.
Proof. destruct hs_sb as (S0 & S1 & _). exact (HSM_win m2 _ (s - 128) (s - 104) HSM_2 hs_M4o ltac:(lia) ltac:(lia)). Qed.

Lemma hs_nd : (0 <= nd)%Z.
Proof.
  assert (W0 : (0 <= wpl_of w 1)%Z) by (unfold wpl_of; apply Z.div_pos; lia).
  pose proof (Z.mul_nonneg_nonneg (wpl_of w 1) h W0 ltac:(lia)). lia.
Qed.

Lemma hs_df_stk : forall M M' (x : word), O23LeptDilW.dil_frame C (s - 152) data nd M M' -> (s - 152 <= u x)%Z -> M' x = M x.
Proof.
  intros M M' x DF Hx. destruct hs_sb as (S0 & S1 & S2 & _).
  pose proof PN as (_ & _ & _ & _ & Td & _).
  apply DF; unfold scratch; lia.
Qed.

Lemma hs_df_pix : forall M M' (x : word), O23LeptDilW.dil_frame C (s - 152) data nd M M' -> (pixd <= u x < pixd + 64)%Z -> M' x = M x.
Proof.
  intros M M' x DF Hx. destruct hs_sb as (S0 & S1 & S2 & S3). pose proof hs_nd as N0.
  pose proof PN as (Gpd & Tpd & Apd & Gd & Td & Ad & NE & _ & _ & _ & _ & L1pd & L1d & _).
  pose proof CK as [T1 T2 T3 T4 T5].
  destruct (live_apart C A1 m2 md1 (Z_to_bv 64 pixd) (Z_to_bv 64 data) 64 nd CK HW2 L1pd L1d
              (zbv_ne pixd data ltac:(lia) ltac:(lia) NE) ltac:(lia) N0) as [D | D];
    rewrite !u_Z2bv in D by lia; (apply DF; unfold scratch; lia).
Qed.

Lemma hs_rd5 : forall M M' (b : Z) (n : nat), O23LeptDilW.dil_frame C (s - 152) data nd M M' -> (s - 152 <= b)%Z -> (b + Z.of_nat n <= s)%Z ->
  rdn SEGS M' (Z_to_bv 64 b) n = rdn SEGS M (Z_to_bv 64 b) n.
Proof.
  intros M M' b n DF Hb Hbn. destruct hs_sb as (S0 & S1 & _).
  apply rdn_ext; rewrite u_Z2bv by lia; [lia |]. intros x Hx. apply (hs_df_stk M M' x DF). lia.
Qed.

Lemma hs_KL : hmt_KL C A A1 md1 M4 s sel pixd vd S regs.
Proof.
  unfold hmt_KL; intros m3 r HWm PMm DFm Q2 Q8 Q9 KP. unfold hmt_keep in KP.
  destruct hs_sb as (S0 & S1 & S2 & S3). pose proof CK as [T1 T2 T3 T4 T5]. pose proof hs_nd as N0.
  pose proof (HSM_df M4 m3 hs_HSM4 DFm) as HS3.
  destruct (HSM_sel m3 HS3) as [SA3 _].
  pose proof (hs_reads m3 DFm) as (_ & _ & _ & _ & _ & _ & _ & _ & RH3 & RW3 & PX3 & _).
  pose proof PN as (Gpd & Tpd & Apd & Gd & Td & Ad & NE & L0pd & L0d & LA0pd & LA0d & L1pd & L1d & _).
  destruct (hm_T al_rom r m3 s sel ltac:(lia) ltac:(lia) Q2 Q9) as (r1 & RUN & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG).
  pc_as RUN. rzs HWm RUN.
  apply (selFindMaxTranslations_W C A1 m3 md1 r1 (s - 160) sel (s - 132) (s - 136) (s - 140) (s - 144) sv _ S CK HWm
           ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold SFMT_STACK; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(apply sp_slot_al4'; [exact Hs16 | reflexivity]) ltac:(apply sp_slot_al4'; [exact Hs16 | reflexivity])
           ltac:(apply sp_slot_al4'; [exact Hs16 | reflexivity]) ltac:(apply sp_slot_al4'; [exact Hs16 | reflexivity])
           SA3 Hcx Hcy).
  intros m4 r4 y0 y1 y2 y3 HW4 CS4 PM4 By0 By1 By2 By3 _.
  assert (HSF : HSM (O23LeptSelFMT.SFR m3 (s - 132) (s - 136) (s - 140) (s - 144) y0 y1 y2 y3)).
  { apply (HSM_win m3 _ (s - 144) (s - 128) HS3); [intros x Hx; apply SFR_out; lia | lia | lia]. }
  pose proof (HSM_post _ m4 (s - 160) HSF PM4 ltac:(lia) ltac:(lia)) as HS4.
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?gpc _ _) _) _ => replace gpc with (0xa2300 : word) by (apply bv_eq; reflexivity) end.
  apply (hmt_X1W C A A1 md1 m4 s pixd vd y0 y1 y2 y3 S regs CK (O23LeptDilW.pixt_sub1 _ _ _ _ _ _ _ _ _ _ _ PN) Hs16 Hlo Hhi
           eq_refl (O23LeptRbordW.hdr_rop_shape1 w h HDR Hw Hh) L1pd (zbv_ne pixd data ltac:(lia) ltac:(lia) NE) L1d L0d LA0d
           By0 By1 By2 By3).
  - intros m5 DF5.
    assert (E5 : forall (b : Z) (n : nat), (s - 152 <= b)%Z -> (b + Z.of_nat n <= s)%Z ->
                 rdn SEGS m5 (Z_to_bv 64 b) n = rdn SEGS (O23LeptSelFMT.SFR m3 (s - 132) (s - 136) (s - 140) (s - 144) y0 y1 y2 y3) (Z_to_bv 64 b) n).
    { intros b n Hb Hbn. rewrite (hs_rd5 m4 m5 b n DF5 Hb Hbn). apply (FRM_rdn16 C (s - 160) _ m4 b n CK (proj1 PM4)); lia. }
    destruct (SFR_rd m3 s y0 y1 y2 y3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (Y0 & Y1 & Y2 & Y3).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
    + rewrite E5 by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact Y0.
    + rewrite E5 by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact Y1.
    + rewrite E5 by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact Y2.
    + rewrite E5 by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact Y3.
    + rewrite E5, SFR_rd_out by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact RW3.
    + rewrite E5, SFR_rd_out by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact RH3.
    + apply (PIXat_frame m4); [| intros x Hx; exact (hs_df_pix m4 m5 x DF5 Hx)].
      apply (PIXat_frame (O23LeptSelFMT.SFR m3 (s - 132) (s - 136) (s - 140) (s - 144) y0 y1 y2 y3));
        [| intros x Hx; exact (LIVK_in A1 _ m4 pixd 64 x (proj2 PM4) L1pd ltac:(lia) ltac:(lia) Hx)].
      apply (PIXat_frame m3); [exact PX3 |]. intros x Hx. apply SFR_out; lia.
  - intros m7 r7 [W7 [DF7 [PM7 [S7 [P7 K7]]]]]. exact (hs_KX m7 r7 (HSM_df m4 m7 HS4 DF7) W7 S7 P7 K7).
  - unfold hmt_TI. split; [exact HW4 |]. split; [intros a _ _; reflexivity |]. split; [apply POSTM_refl |].
    split; [csr; reflexivity |]. split; [csr; reflexivity |].
    intros x Hx. destruct Hx as [<- | [<- | []]]; csr; reflexivity.
Qed.


Lemma hs_main : realizes SEGS (mkCfg (mkst r2 (0xa20d0 : word) m2 al_rom) (with_vmmaps vm1 md)) S.
Proof using All.
  destruct (hsm_lay C s CK Hlo Hhi) as (Hs0 & Hs1 & Hs64).
  pose proof (O23LeptDilW.pixt_sub1 _ _ _ _ _ _ _ _ _ _ _ PN) as SUB.
  pose proof PN as (Pd1 & Pd2 & Pd3 & Pa1 & Pa2 & Pa3 & Pne & LAd & LAa & L0d & L0a & L1d & L1a & PXd & CMR).
  pose proof HSM_2 as (CE2 & FR2 & LV2 & NW2 & PX2 & SL2).
  destruct (HSM_sel m2 HSM_2) as [SA1 SC2].
  pose proof SA1 as (Hsy & Hsx & Bs & Ls & RC & Bd & Ld & Nd & Hrows & Hdist).
  unfold bok in Bs, Bd.
  pose proof PXs as (Ps0 & Ps1 & _ & _).
  pose proof HDR as (_ & Hw1 & Hh1 & _).
  pose proof (O23LeptDilW.wpl1_le w Hw) as WPL.
  assert (NDp : (0 <= wpl_of w 1 * h)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  pose proof (blk_range C A m md _ 64 CK HW Lps ltac:(lia)) as [Bp1 Bp2]. rewrite u_Z2bv in Bp1, Bp2 by lia.
  pose proof (hmt_al16 C A m md pixs 64 HW Lps ltac:(lia)) as ALp.
  assert (WP3 : W C A1 (PGDH m2 s w h) md1 /\ POSTM C A1 s m2 (PGDH m2 s w h)) by (unfold PGDH; wp_win CK).
  destruct WP3 as [W3 _].
  destruct (hm_B al_rom r2 m2 s pixd pixs sel w h ltac:(lia) Hs64 Hs16 ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(apply al16_mod8; exact ALp) ltac:(lia) ltac:(lia) ltac:(lia)
              (PIX_rd_w SEGS m2 pixs vs PX2) (PIX_rd_h SEGS m2 pixs vs PX2)
              (W_sok_win C A1 m2 md1 (s - 112) 8 CK HW2 ltac:(lia) ltac:(cbn; lia)) R2 R10 R18 R9)
    as (r3 & RUN3 & Q2 & Q1 & Q8 & Q10 & Q11 & Q12 & Q13 & Q14 & AG3).
  pc_as RUN3. rzs HW2 RUN3.
  assert (RC3 : RECat (PGDH m2 s w h) sel (sel_flds (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv) (v_data sv) (v_name sv))).
  { apply (RECat_frame m2 _ _ _ RC). intros x Hx. change (Z.of_nat (flds_len (sel_flds _ _ _ _ _ _))) with 32%Z in Hx. apply hsm_PG_out; lia. }
  destruct (sgp4_run al_rom r3 (PGDH m2 s w h) sel (s - 120) (s - 116) (s - 128) (s - 124) (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv)
              (v_data sv) (v_name sv) _ RC3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold O23LeptSelGP.cell_ok; lia) ltac:(unfold O23LeptSelGP.cell_ok; lia)
              ltac:(unfold O23LeptSelGP.cell_ok; lia) ltac:(unfold O23LeptSelGP.cell_ok; lia)
              (W_sok_win C A1 _ md1 (s - 120) 4 CK W3 ltac:(lia) ltac:(cbn; lia))
              (W_sok_win C A1 _ md1 (s - 116) 4 CK W3 ltac:(lia) ltac:(cbn; lia))
              (W_sok_win C A1 _ md1 (s - 128) 4 CK W3 ltac:(lia) ltac:(cbn; lia))
              (W_sok_win C A1 _ md1 (s - 124) 4 CK W3 ltac:(lia) ltac:(cbn; lia))
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(apply al16_mod8; tauto) ltac:(apply sp_slot_al4'; [exact Hs16 | reflexivity])
              ltac:(apply sp_slot_al4'; [exact Hs16 | reflexivity]) ltac:(apply sp_slot_al4'; [exact Hs16 | reflexivity])
              ltac:(apply sp_slot_al4'; [exact Hs16 | reflexivity])
              Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14)
    as (r4 & RUN4 & V10 & AG4).
  pc_as RUN4. rzs HW2 RUN4.
  assert (WP4 : W C A1 M4 md1 /\ POSTM C A1 s m2 M4) by (unfold O23LeptSelGP.SGP4, O23LeptSelGP.wr4, PGDH; wp_win CK).
  destruct WP4 as [W4 _].
  destruct (V23LeptSelGP.SGP4_rd (PGDH m2 s w h) (s - 120) (s - 116) (s - 128) (s - 124) (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv)
              ltac:(unfold O23LeptSelGP.cell_ok; lia) ltac:(unfold O23LeptSelGP.cell_ok; lia)
              ltac:(unfold O23LeptSelGP.cell_ok; lia) ltac:(unfold O23LeptSelGP.cell_ok; lia)
              ltac:(unfold O23LeptSelGP.cell_apart; lia) ltac:(unfold O23LeptSelGP.cell_apart; lia)
              ltac:(unfold O23LeptSelGP.cell_apart; lia) ltac:(unfold O23LeptSelGP.cell_apart; lia)
              ltac:(unfold O23LeptSelGP.cell_apart; lia) ltac:(unfold O23LeptSelGP.cell_apart; lia)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (RS1 & RS2 & _ & _).
  destruct (hm_E al_rom r4 M4 s sel (v_sy sv) (v_sx sv) ltac:(lia) Hs64 ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(apply al16_mod8; tauto) RS1 RS2 ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r5 & RUN5 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E10 & E11 & AG5).
  pc_as RUN5. rzs HW2 RUN5.
  assert (NEPD : Z_to_bv 64 pixd <> Z_to_bv 64 (p_data vd)).
  { cbn [p_data O23LeptPixCopyT.hdv]. intro E. apply Pne. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. exact E. }
  assert (NEPS : Z_to_bv 64 pixs <> Z_to_bv 64 (p_data vd)).
  { cbn [p_data O23LeptPixCopyT.hdv]. intro E. pose proof Lps as X. rewrite E in X. congruence. }
  assert (NEDS : Z_to_bv 64 (p_data vs) <> Z_to_bv 64 (p_data vd)).
  { cbn [p_data set_rc O23LeptPixCopyT.hdv]. intro E. pose proof Ldatas as X. rewrite E in X. congruence. }
  pose proof (hmt_loop C A A1 md1 M4 s sel pixd pixs sv c vd vs S regs CK SUB Hs16 Hlo Hhi Hsy Hsx Hcx Hcy
                ltac:(lia) ltac:(apply al16_mod8; tauto) ltac:(lia) ltac:(split; [lia | apply al16_mod8; tauto])
                ltac:(intros i Hi; destruct (Hrows i Hi) as (Br & _); unfold bok in Br; lia)
                ltac:(intros i Hi; destruct (Hrows i Hi) as (Br & _); unfold bok in Br; split; [lia | apply al16_mod4; tauto])
                ltac:(intros i j Hi Hj; exact (proj1 (SC2 i j Hi Hj))) ltac:(lia) eq_refl eq_refl
                (O23LeptRbordW.hdr_rop_shape1 w h HDR Hw Hh) (O23LeptRbordW.hdr_rop_shape1 w h HDR Hw Hh) eq_refl eq_refl
                L1d (SUB _ _ Lps) NEPD NEPS L1a LAa L0a (SUB _ _ Ldatas) NEDS hs_HCM hs_reads hs_KL) as LOOP.
  apply (LOOP (Z.to_nat ((v_sy sv - 1 - 0) * v_sx sv + (v_sx sv - 1 - 0))) true 0%Z 0%Z r5 M4 W4 (POSTM_refl _ _ _ _)
           (fun _ _ _ => eq_refl) ltac:(lia) ltac:(lia)).
  - rewrite Z2Nat.id; [reflexivity |]. apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg |]; lia.
  - csr; reflexivity.
  - csr; reflexivity.
  - csr; reflexivity.
  - exact E18.
  - exact E19.
  - exact E20.
  - exact E21.
  - exact E22.
  - exact E23.
  - exact E24.
  - exact E25.
  - exact E26.
  - exact E27.
  - exact E10.
  - intros x Hx. cbn [In] in Hx. destruct Hx as [<- | [<- | []]]; csr; reflexivity.
Qed.

End HSucc.

(* [comment removed for export] *)
Lemma hmt_new_succ : forall C A m md regs (s pixs sel w h cm datas : Z) (sv : selv) (c : Z -> Z -> Z) (cv : cmapv) (ret : word) (S : TSet)
    (kR bR : Z) (A1 : AS) (m2 : word -> option byte) (vm1 : VmMaps) (r2 : bvmap 5 word) (pixd cd data : Z),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + HMT_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  PIXat m pixs (O23LeptPixCopyT.hdv w h 1 cm datas) -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  sel_at (alloc_top (c_vm C)) A m sel sv -> sel_cont m sv c -> (0 <= v_cx sv < v_sx sv)%Z -> (0 <= v_cy sv < v_sy sv)%Z ->
  (forall p, sel_blk sel sv p -> Z_to_bv 64 p <> Z_to_bv 64 pixs) ->
  W C A1 m2 (with_vmmaps vm1 md) -> POSTM C A (s - 160) (O23LeptPma1.clone_mem (FRH m s ret regs) pixs (s - 152)) m2 ->
  O23LeptPixCopyT.pixt_new C A A1 m2 pixd w h 1 cd data cv ->
  getr r2 2 = Z_to_bv 64 (s - 160) -> getr r2 9 = Z_to_bv 64 sel -> getr r2 18 = Z_to_bv 64 pixs -> getr r2 10 = Z_to_bv 64 pixd ->
  (forall x, In x [3; 4]%list -> getr r2 x = getr regs x) ->
  aroom A1 vm1 (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm)) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ O23LeptPixCopyT.pixt_new C A A' m' pixd w h 1 cd data cv /\ POSTM C A s m m') ->
     aroom A' vm' (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst r2 (0xa20d0 : word) m2 al_rom) (with_vmmaps vm1 md)) S.
Proof. exact hs_main. Qed.

(* [comment removed for export] *)
Theorem pixHMT_new_W : forall C A m md regs (s pixs sel w h cm datas : Z) (sv : selv) (c : Z -> Z -> Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + HMT_STACK <= s)%Z -> (s <= c_top C)%Z ->
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
  realizes SEGS (mkCfg (mkst regs (0xa2088 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs sel w h cm datas sv c cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12
    PXs HOK Hw Hh Lps L0ps Ldat HCM SA SC Hcx Hcy SB kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (Hlo' : (c_top C - LSTK + 3744 <= s)%Z) by (unfold HMT_STACK in Hlo; lia).
  pose proof SA as (Hsy & Hsx & Bsel & Lsel & RC & _). unfold bok in Bsel.
  pose proof PXs as (Hs0 & Hs64' & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  destruct (hm_A al_rom regs m s 0 pixs sel ret ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 160) 160 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q9 & Q18 & Q13 & Q10 & Q11 & Q12 & AG1).
  rzs HW RUN1.
  destruct (FRH_WP C A m md s s ret regs CK HW ltac:(lia) ltac:(lia) Hhi) as [HW1 PM1].
  pose proof (frH_FRH m s ret regs ltac:(lia) ltac:(lia)) as CE1.
  assert (PX1 : PIXat (FRH m s ret regs) pixs (O23LeptPixCopyT.hdv w h 1 cm datas)).
  { apply (PIXat_frame m); [exact PXs |]. intros x Hx. apply FRH_lo; lia. }
  assert (RC1 : RECat (FRH m s ret regs) sel (sel_flds (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv) (v_data sv) (v_name sv))).
  { apply (RECat_frame m); [exact RC |]. intros x Hx.
    change (Z.of_nat (flds_len (sel_flds (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv) (v_data sv) (v_name sv)))) with 32%Z in Hx.
    apply FRH_lo; lia. }
  assert (HCM1 : cm = 0%Z \/ (CMAPat (FRH m s ret regs) cm cv /\ O23LeptCmapValid.cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\
                              live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [E | (CM & CV & Lcm & Larr)]; [left; exact E | right].
    refine (conj _ (conj CV (conj Lcm Larr))).
    pose proof CM as (Hc0 & Hc64 & _).
    destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
    apply (CMAPat_frame m); [exact CM |]. intros x Hx. apply FRH_lo; lia. }
  apply (pma1_new_W C A (FRH m s ret regs) md r1 (s - 160) pixs sel (s - 152) w h cm datas
           (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv) (v_data sv) (v_name sv) cv _ S CK HW1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(change O23LeptPma1.PMA1_STACK with 3584%Z; lia) ltac:(lia)
           Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) Q10 Q11 Q12 Q13 ltac:(lia) ltac:(lia)
           ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) PX1 HOK Hw Hh Lps L0ps HCM1 RC1 Lsel ltac:(lia) ltac:(lia)
           kR bR Hrm Hrk Hrb).
  intros A2 m2 vm2 r2 HW2 CS2 DJ AR2.
  destruct DJ as [(V10 & LV & PM2) | (pixd & cd & data & V10 & PT & PM2)].
  - destruct (hm_N al_rom r2 m2 s ltac:(lia) ltac:(lia) (W_sev_got C A2 m2 _ HW2) (W_sev C A2 m2 _ HW2) ltac:(csr; reflexivity) V10)
      as (r3 & RUN3 & V2 & V1 & W10 & W11 & W12 & AG3).
    pc_as RUN3. rzs HW2 RUN3.
    apply (returnErrorPtr_W C A2 m2 (with_vmmaps vm2 md) r3 (s - 160) _ _ _ _ _ (Z_to_bv 64 0) S CK HW2 V2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia)
             V1 ltac:(red; apply bv_eq; reflexivity) W10 W11 W12 str_dil_msg str_hmt_proc).
    intros m4 r4 HW4 OUT4 GR4 CS4 A10.
    assert (CE4 : cellsZ m4 (frH s ret regs)).
    { apply (frH_out m2 m4 (s - 160 - (16 + LSF)) (s - 160) s ret regs OUT4); [unfold LSF; lia | lia | lia |].
      apply (frH_frm C (s - 160) (O23LeptPma1.null_mem (FRH m s ret regs) (s - 152)) m2 s ret regs CK (proj1 PM2)); [lia | lia | lia |].
      apply (frH_out (FRH m s ret regs) _ (s - 152) (s - 152 + 8) s ret regs); [| lia | lia | lia | exact CE1].
      intros x Hx. apply null_mem_out; lia. }
    cbn [cellsZ frH] in CE4. destruct CE4 as (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & _).
    destruct (hm_Nz al_rom r4 m4 s 0 ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) ltac:(lia) ltac:(lia) ltac:(lia) Hret
                R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 ltac:(csr; reflexivity) A10)
      as (r5 & RUN5 & Z2 & Z1 & Z10 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27 & AG5).
    pc_as RUN5. rzs HW4 RUN5.
    apply (HK A2 m4 vm2 r5 HW4).
    + apply cs_kept_intro; csr; reflexivity.
    + left. refine (conj Z10 (conj LV _)).
      eapply POSTM_trans; [exact PM1 |].
      eapply POSTM_trans;
        [exact (POSTM_wbytes_win C A (FRH m s ret regs) md (Z_to_bv 64 (s - 152)) (word_to_le_bytes 8 (Z_to_bv 64 0)) s CK HW1
                  ltac:(rewrite u_Z2bv by lia; lia)
                  ltac:(rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) Hhi) |].
      eapply POSTM_trans; [exact (POSTM_mono C A (s - 160) s _ _ ltac:(lia) PM2) |].
      apply (POSTM_sub C A A2 s); [intros q k Hq; rewrite LV; exact Hq |].
      exact (POSTM_range C A2 m2 (with_vmmaps vm2 md) m4 _ _ s CK HW2 OUT4 ltac:(unfold LSF; lia) ltac:(lia) Hhi).
    + exact AR2.
  - lazymatch goal with |- realizes _ (mkCfg (mkst _ ?gpc _ _) _) _ => replace gpc with (0xa20d0 : word) by (apply bv_eq; reflexivity) end.
    apply (hmt_new_succ C A m md regs s pixs sel w h cm datas sv c cv ret S kR bR A2 m2 vm2 r2 pixd cd data
             CK HW H2 Hs16 Hlo Hhi Hret PXs HOK Hw Hh Lps L0ps Ldat SA SC Hcx Hcy SB HW2 PM2 PT
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) V10).
    + intros x Hx. destruct Hx as [<- | [<- | []]]; csr; reflexivity.
    + exact AR2.
    + intros A' m' vm' regs' HW' CS' EX AR'. exact (HK A' m' vm' regs' HW' CS' (or_intror EX) AR').
Qed.

End HmtNW.
