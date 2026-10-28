(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRecs LeptSel LeptSlots LeptExecT LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptDilW V23LeptMbc V23LeptCloseSpec V23LeptCloseIface V23LeptCloseSegs V23LeptCloseA V23LeptSelDW V23LeptCloseT V23LeptCloseP V23LeptCloseR.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixHdr O23LeptPixCopyT O23LeptCloseSpec O23LeptCloseIface O23LeptCloseSegs O23LeptCloseA O23LeptCloseT O23LeptCloseP.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section CloseN1.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Ltac rzs HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
Ltac n1kpcs := first [exact cs2 | exact cs4 | exact cs8 | exact cs9 | exact cs18 | exact cs19].
Ltac n1kp := repeat match goal with
  | CS : cs_kept ?a ?b |- getr ?b ?x = _ => rewrite (cs_kept_get a b x CS) by n1kpcs
  | AG : regs_agree _ ?a ?b |- getr ?b ?x = _ => rewrite (AG x ltac:(notin_lit))
  end; assumption.
Ltac n1rkN := let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [notin_lit|]); destruct Hx.
Ltac n1rkgo RG :=
  lazymatch goal with
  | |- O23LeptCloseT.rkept RG ?b =>
      first [ assumption
            | match goal with CS : cs_kept ?a b |- _ => apply (V23LeptCloseR.cr_rkC RG a b); [n1rkgo RG | exact CS] end
            | match goal with AG : regs_agree _ ?a b |- _ => eapply (V23LeptCloseR.cr_rkA RG a b); [n1rkgo RG | exact AG | n1rkN] end ]
  end.
Ltac n1pcfix RUN :=
  lazymatch type of RUN with msteps _ (@mkst _ _ ?p _ _) _ =>
    lazymatch goal with |- realizes _ (mkCfg (@mkst _ _ ?q _ _) _) _ =>
      tryif constr_eq p q then idtac else replace q with p by (apply bv_eq; reflexivity)
    end
  end.

Lemma n1_ap : forall (A : AS) (X Y : word -> Prop), (forall q, X q -> live A q = None) ->
  (forall q, Y q -> exists n, live A q = Some n) -> forall q q', X q -> Y q' -> q <> q'.
Proof.
  intros A X Y FX LY q q' Xq Yq E. subst q'. destruct (LY q Yq) as [n Hn]. rewrite (FX q Xq) in Hn. discriminate Hn.
Qed.

Lemma n1_tbq : forall p data cd cvd (q : word), q = Z_to_bv 64 p -> O23LeptCloseA.tblk p data cd cvd q.
Proof. intros p data cd cvd q ->. unfold O23LeptCloseA.tblk. left. reflexivity. Qed.

Lemma n1_tbp : forall p data cd cvd, O23LeptCloseA.tblk p data cd cvd (Z_to_bv 64 p).
Proof. intros. unfold O23LeptCloseA.tblk. left. reflexivity. Qed.

Lemma n1_tbd : forall p data cd cvd, O23LeptCloseA.tblk p data cd cvd (Z_to_bv 64 data).
Proof. intros. unfold O23LeptCloseA.tblk. right. left. reflexivity. Qed.

Lemma n1_tbc : forall p data cd cvd, cd <> 0%Z -> O23LeptCloseA.tblk p data cd cvd (Z_to_bv 64 cd).
Proof. intros p data cd cvd H. unfold O23LeptCloseA.tblk. right. right. split; [exact H | left; reflexivity]. Qed.

Lemma n1_up_rd : forall m m' (s b z : Z), (forall a : word, (s - 112 <= u a)%Z -> m' a = m a) ->
  (s - 112 <= b)%Z -> (0 <= b)%Z -> (b + 8 <= 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 b) 8 = Some (Z_to_le_bytes 8 z) -> rdn SEGS m' (Z_to_bv 64 b) 8 = Some (Z_to_le_bytes 8 z).
Proof.
  intros m m' s b z UP H1 H2 H3 R.
  apply (cell_keep m m' b (b + 8) b z H2 H3 ltac:(lia) ltac:(lia)); [|exact R].
  intros a Ha. apply UP. lia.
Qed.

Lemma n1_tpx_st : forall C A m md (s pp v p w h cd data : Z) (cvd : cmapv),
  Cok C -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z -> W C A m md -> (s - 72 <= pp)%Z -> (pp + 8 <= s - 48)%Z ->
  O23LeptCloseA.tpx C A m p w h cd data cvd -> O23LeptCloseA.tpx C A (O23LeptCloseSegs.CW8 m pp v) p w h cd data cvd.
Proof.
  intros C A m md s pp v p w h cd data cvd CK Hlo Hhi HW H1 H2 T.
  exact (O23LeptCloseA.tpx_keep C A A (fun _ => True) m (O23LeptCloseSegs.CW8 m pp v) p w h cd data cvd T (fun q _ => eq_refl)
           (store_livk C A m md s pp v CK Hlo Hhi HW H1 H2) I (fun _ => I)).
Qed.

Lemma n1_tpx_new : forall C A A' m m' (p w h cd data : Z) (cvd : cmapv) (X : word -> Prop),
  O23LeptCloseA.tpx C A m p w h cd data cvd -> (forall q, X q -> live A q = None) -> (forall q, ~ X q -> live A' q = live A q) ->
  LIVK A m m' -> O23LeptCloseA.tpx C A' m' p w h cd data cvd.
Proof.
  intros C A A' m m' p w h cd data cvd X T FX LX LV.
  refine (O23LeptCloseA.tpx_keep C A A' (fun _ => True) m m' p w h cd data cvd T _ (O23LeptCloseA.PWK_livk A m m' LV) I (fun _ => I)).
  intros q Hq. apply LX. intros Xq.
  destruct (O23LeptCloseP.tpx_live C A m p w h cd data cvd q T Hq) as [n Hn]. rewrite (FX q Xq) in Hn. discriminate Hn.
Qed.

Lemma n1_tpx_ero : forall C A m m' (p w h cd data : Z) (cvd : cmapv) (d : word),
  O23LeptCloseA.tpx C A m p w h cd data cvd -> O23LeptCloseA.PWK A (fun q => q <> d) m m' ->
  Z_to_bv 64 p <> d -> (cd <> 0%Z -> Z_to_bv 64 cd <> d) -> O23LeptCloseA.tpx C A m' p w h cd data cvd.
Proof.
  intros C A m m' p w h cd data cvd d T PW Np Nc.
  exact (O23LeptCloseA.tpx_keep C A A (fun q => q <> d) m m' p w h cd data cvd T (fun q _ => eq_refl) PW Np Nc).
Qed.

Lemma n1_tpx_eroN : forall C A m m' (p w h cd data : Z) (cvd : cmapv) (d : word),
  O23LeptCloseA.tpx C A m p w h cd data cvd -> O23LeptCloseA.PWK A (fun q => q <> d) m m' ->
  (forall q, O23LeptCloseA.tblk p data cd cvd q -> q <> d) -> O23LeptCloseA.tpx C A m' p w h cd data cvd.
Proof.
  intros C A m m' p w h cd data cvd d T PW N.
  exact (n1_tpx_ero C A m m' p w h cd data cvd d T PW (N _ (n1_tbp p data cd cvd)) (fun Hc => N _ (n1_tbc p data cd cvd Hc))).
Qed.

Lemma n1_rst_new : forall C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m A' m' (X : word -> Prop),
  Cok C -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  RST C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m ->
  (forall q, X q -> live A q = None) -> (forall q, ~ X q -> live A' q = live A q) ->
  sub_live A A' -> POSTM C A (s - 112) m m' ->
  RST C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A' m'.
Proof.
  intros C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m A' m' X CK Hlo Hhi R FX LX SUB PM.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. unfold CSC_STACK in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof R as (_ & _ & _ & _ & _ & SUBr & _).
  apply (RST_keep C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m A' (fun _ => True) m' CK ltac:(lia) Hhi R).
  - intros q Hq. apply LX. intros Xq.
    destruct (rblk_live C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m q R Hq) as [n Hn].
    rewrite (FX q Xq) in Hn. discriminate Hn.
  - exact (O23LeptCloseA.PWK_livk A m m' (proj2 PM)).
  - intros q _. exact I.
  - intros a Ha. apply (FRM_pw C (s - 112) m m' CK (proj1 PM) ltac:(lia)). lia.
  - exact (sub_live_trans Ar A A' SUBr SUB).
  - exact (POSTM_mono C Ar (s - 112) s m m' ltac:(lia) (POSTM_sub C Ar A (s - 112) m m' SUBr PM)).
Qed.

Lemma n1_rst_ero : forall C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m m' (d : word),
  Cok C -> (112 <= s)%Z -> (s <= c_top C)%Z ->
  RST C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m ->
  (forall q, O23LeptCloseA.rblk pix1 datas cm cv sel1 sel2 sv1 sv2 q -> q <> d) ->
  O23LeptCloseA.PWK A (fun q => q <> d) m m' -> (forall a : word, (s - 112 <= u a)%Z -> m' a = m a) -> POSTM C Ar s m m' ->
  RST C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m'.
Proof.
  intros C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m m' d CK Hs Hhi R N PW UP PM.
  pose proof R as (_ & _ & _ & _ & _ & SUB & _).
  exact (RST_keep C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m A (fun q => q <> d) m' CK Hs Hhi R
           (fun q _ => eq_refl) PW N (fun a Ha => UP a ltac:(lia)) SUB PM).
Qed.

Definition ct_RG (regs r : bvmap 5 word) (s pix1 : Z) : Prop :=
  getr r 2 = Z_to_bv 64 (s - 112) /\ getr r 8 = Z_to_bv 64 pix1 /\ O23LeptCloseT.rkept regs r.

Lemma ct_nin3 : forall x : reg, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%list -> ~ In x [1; 10; 11]%list.
Proof.
  intros x Hx. cbn [In] in Hx.
  repeat (destruct Hx as [<-|Hx]; [notin_lit |]).
  destruct Hx.
Qed.

Lemma ct_RG_hop : forall regs r r' s pix1, ct_RG regs r s pix1 -> cs_kept r r' -> ct_RG regs r' s pix1.
Proof.
  intros regs r r' s pix1 (R2 & R8 & RK) CS. refine (conj _ (conj _ _)).
  - rewrite (cs_kept_get r r' 2%bv CS cs2). exact R2.
  - rewrite (cs_kept_get r r' 8%bv CS cs8). exact R8.
  - intros x Hx. rewrite (cs_kept_get r r' x CS (rk_cs x Hx)). exact (RK x Hx).
Qed.

Lemma ct_RG_run2 : forall regs r r' s pix1, ct_RG regs r s pix1 -> regs_agree (fun x => In x [1; 10]%list) r r' -> ct_RG regs r' s pix1.
Proof.
  intros regs r r' s pix1 (R2 & R8 & RK) AG. refine (conj _ (conj _ _)).
  - rewrite (AG 2%bv ltac:(notin_lit)). exact R2.
  - rewrite (AG 8%bv ltac:(notin_lit)). exact R8.
  - intros x Hx. rewrite (AG x (rk_nin x Hx)). exact (RK x Hx).
Qed.

Lemma ct_RG_run3 : forall regs r r' s pix1, ct_RG regs r s pix1 -> regs_agree (fun x => In x [1; 10; 11]%list) r r' -> ct_RG regs r' s pix1.
Proof.
  intros regs r r' s pix1 (R2 & R8 & RK) AG. refine (conj _ (conj _ _)).
  - rewrite (AG 2%bv ltac:(notin_lit)). exact R2.
  - rewrite (AG 8%bv ltac:(notin_lit)). exact R8.
  - intros x Hx. rewrite (AG x (ct_nin3 x Hx)). exact (RK x Hx).
Qed.

Lemma ct_RG_gp : forall regs r s pix1 (g : word), ct_RG regs r s pix1 -> getr regs 4 = g -> getr r 4 = g.
Proof.
  intros regs r s pix1 g (_ & _ & RK) H. rewrite (RK 4%bv ltac:(in_lit)). exact H.
Qed.

Lemma ct_keep : forall C Ar A1 A2 m1 m2 (X : word -> Prop) pix1 w h cm datas cv sel1 sel2 sv1 sv2,
  O23LeptCloseSpec.pix1_at C Ar A1 m1 pix1 w h cm datas cv ->
  sel_at (alloc_top (c_vm C)) A1 m1 sel1 sv1 -> sel_at (alloc_top (c_vm C)) A1 m1 sel2 sv2 ->
  (forall q, O23LeptCloseA.rblk pix1 datas cm cv sel1 sel2 sv1 sv2 q -> ~ X q) ->
  (forall q, ~ X q -> live A2 q = live A1 q) -> O23LeptCloseA.PWK A1 (fun q => ~ X q) m1 m2 ->
  O23LeptCloseSpec.pix1_at C Ar A2 m2 pix1 w h cm datas cv /\
  sel_at (alloc_top (c_vm C)) A2 m2 sel1 sv1 /\ sel_at (alloc_top (c_vm C)) A2 m2 sel2 sv2.
Proof.
  intros C Ar A1 A2 m1 m2 X pix1 w h cm datas cv sel1 sel2 sv1 sv2 P1 SA1 SA2 DX LE PW.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  refine (conj _ (conj _ _)).
  - apply (O23LeptCloseA.p1_keep3 C Ar A1 A2 (fun q => ~ X q) m1 m2 pix1 w h cm datas cv P1).
    + intros q Hq. apply LE. apply DX. left. exact Hq.
    + exact PW.
    + intros HX. refine (DX _ _ HX). left. left. reflexivity.
    + intros Hc HX. refine (DX _ _ HX). left. right. right. split; [exact Hc | left; reflexivity].
  - apply (O23LeptCloseA.sel_at_keepP (alloc_top (c_vm C)) A1 A2 (fun q => ~ X q) m1 m2 sel1 sv1 ATL SA1).
    + intros q Hq. apply LE. apply DX. right. left. exact Hq.
    + exact PW.
    + intros q Hq. apply DX. right. left. exact Hq.
  - apply (O23LeptCloseA.sel_at_keepP (alloc_top (c_vm C)) A1 A2 (fun q => ~ X q) m1 m2 sel2 sv2 ATL SA2).
    + intros q Hq. apply LE. apply DX. right. right. exact Hq.
    + exact PW.
    + intros q Hq. apply DX. right. right. exact Hq.
Qed.

Lemma ct_tpx_keep : forall C A1 A2 m1 m2 (X : word -> Prop) p w h cd data cvd,
  O23LeptCloseA.tpx C A1 m1 p w h cd data cvd -> (forall q, O23LeptCloseA.tblk p data cd cvd q -> ~ X q) ->
  (forall q, ~ X q -> live A2 q = live A1 q) -> O23LeptCloseA.PWK A1 (fun q => ~ X q) m1 m2 ->
  O23LeptCloseA.tpx C A2 m2 p w h cd data cvd.
Proof.
  intros C A1 A2 m1 m2 X p w h cd data cvd T DX LE PW.
  apply (O23LeptCloseA.tpx_keep C A1 A2 (fun q => ~ X q) m1 m2 p w h cd data cvd T).
  - intros q Hq. exact (LE q (DX q Hq)).
  - exact PW.
  - intros HX. refine (DX _ _ HX). left. reflexivity.
  - intros Hc HX. refine (DX _ _ HX). right. right. split; [exact Hc | left; reflexivity].
Qed.

Ltac ct_pcfix RUN := match type of RUN with context [mkst _ ?p _ _] =>
  match goal with |- context [mkst _ (Z_to_bv 64 ?n) _ _] => replace (Z_to_bv 64 n) with p by (apply bv_eq; reflexivity) end end.

Lemma csc_tail : forall (sh : bool) (fr : bvmap 5 word) C Ar A m md regs (s pix1 w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z)
    (fr1 : bvmap 5 word) (cs1 : bv 32) (A4 : AS) (m4 : word -> option byte) (vm4 : VmMaps) (r4 : bvmap 5 word) (kx bx : Z)
    (sel1 sel2 : Z) (sv1 sv2 : selv) (pixsb cdb datab : Z) (cvb : cmapv) (pixt cdt datat : Z) (cvt : cmapv) (pixdb cdd datad : Z) (cvd : cmapv),
  pcg2_contract (mkFP fr1 cs1) ->
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 4 = Z_to_bv 64 0x1381d0 -> sub_live Ar A ->
  pix1 <> datas -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z -> O23LeptPixHdr.hdr_ok (w + 64) (h + 64) 1 ->
  frm_zero cs1 -> (forall r : reg, In (u r) fs_list -> reg_get fr1 r = reg_get fr r) ->
  W C A4 m4 (with_vmmaps vm4 md) ->
  getr r4 2 = Z_to_bv 64 (s - 112) -> getr r4 8 = Z_to_bv 64 pix1 -> getr r4 9 = Z_to_bv 64 32 -> getr r4 18 = Z_to_bv 64 pixdb ->
  O23LeptCloseT.rkept regs r4 -> FCL s ret regs sh sel1 sel2 m4 ->
  rdn SEGS m4 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 pixsb) -> rdn SEGS m4 (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 pixt) ->
  rdn SEGS m4 (Z_to_bv 64 (s - 72)) 8 = Some (Z_to_le_bytes 8 pixdb) ->
  sub_live Ar A4 -> POSTM C Ar s m m4 ->
  O23LeptCloseSpec.pix1_at C Ar A4 m4 pix1 w h cm datas cv ->
  sel_at (alloc_top (c_vm C)) A4 m4 sel1 sv1 -> sel_at (alloc_top (c_vm C)) A4 m4 sel2 sv2 ->
  O23LeptCloseT.sels_static C A sh sel1 sel2 sv1 sv2 ->
  (forall q, O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q -> ~ O23LeptCloseA.tblk pix1 datas cm cv q) ->
  (forall q, O23LeptCloseA.tblk pix1 datas cm cv q -> exists n, live A q = Some n) ->
  O23LeptCloseA.tpx C A4 m4 pixsb (w + 64) (h + 64) cdb datab cvb ->
  O23LeptCloseA.tpx C A4 m4 pixt (w + 64) (h + 64) cdt datat cvt ->
  O23LeptCloseA.tpx C A4 m4 pixdb (w + 64) (h + 64) cdd datad cvd ->
  (forall q, O23LeptCloseA.tblk pixsb datab cdb cvb q \/ O23LeptCloseA.tblk pixt datat cdt cvt q \/ O23LeptCloseA.tblk pixdb datad cdd cvd q ->
     live A q = None) ->
  (forall q, O23LeptCloseA.tblk pixsb datab cdb cvb q -> ~ O23LeptCloseA.tblk pixt datat cdt cvt q) ->
  (forall q, O23LeptCloseA.tblk pixsb datab cdb cvb q -> ~ O23LeptCloseA.tblk pixdb datad cdd cvd q) ->
  (forall q, O23LeptCloseA.tblk pixt datat cdt cvt q -> ~ O23LeptCloseA.tblk pixdb datad cdd cvd q) ->
  (forall q, O23LeptCloseA.tblk pixsb datab cdb cvb q \/ O23LeptCloseA.tblk pixt datat cdt cvt q \/ O23LeptCloseA.tblk pixdb datad cdd cvd q ->
     ~ O23LeptCloseA.rblk pix1 datas cm cv sel1 sel2 sv1 sv2 q) ->
  (cm = 0%Z -> cdd = 0%Z) -> O23LeptCloseA.cmeq cdd cvd cv ->
  (forall q, ~ (O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q \/ O23LeptCloseA.tblk pixsb datab cdb cvb q \/
                O23LeptCloseA.tblk pixt datat cdt cvt q \/ O23LeptCloseA.tblk pixdb datad cdd cvd q) -> live A4 q = live A q) ->
  aroom A4 vm4 kx bx ->
  (kR - O23LeptCloseSpec.RK_csc (O23LeptCloseA.vsz sh) + (RK_pixcopy + RK_cmapcopy) <= kx)%Z ->
  (bR - O23LeptCloseSpec.RB_csc (O23LeptCloseA.vsz sh) w h cm + ((RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm) + RB_cmapT cm) <= bx)%Z ->
  (0 <= kR - O23LeptCloseSpec.RK_csc (O23LeptCloseA.vsz sh))%Z -> (0 <= bR - O23LeptCloseSpec.RB_csc (O23LeptCloseA.vsz sh) w h cm)%Z ->
  csc_K fr C Ar A m md regs s pix1 (O23LeptCloseA.vsz sh) w h cm datas cv ret S kR bR ->
  realizes SEGS (mkCfg (@mkst (mkFP fr1 cs1) r4 (0xa4be8 : word) m4 al_rom) (with_vmmaps vm4 md)) S.
Proof.
  intros sh fr C Ar A m md regs s pix1 w h cm datas cv ret S kR bR fr1 cs1 A4 m4 vm4 r4 kx bx sel1 sel2 sv1 sv2
    pixsb cdb datab cvb pixt cdt datat cvt pixdb cdd datad cvd
    PCG CK Hs16 Hlo Hhi Hret H2 H4 SUBA Hpd HO Hw Hh HO64 FZ FK HW R2 R8 R9 R18 RK FC Ssb St Sdb SUB PM P1 SA1 SA2 SS DJ LP1
    Tsb Tt Tdb Fr3 D12 D13 D23 Dr CMZ CMQ LE ROOM Hk Hb Hk0 Hb0 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. pose proof Hlo as Hlo'. unfold CSC_STACK in Hlo'.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  set (fx := mkFP fr1 cs1).
  assert (RG4 : ct_RG regs r4 s pix1) by (exact (conj R2 (conj R8 RK))).
  assert (PB : (1 <= pix1 < 2 ^ 64)%Z).
  { pose proof P1 as ((Hp0 & Hp64 & _) & Lp & _).
    destruct (blk_range C A4 m4 _ (Z_to_bv 64 pix1) 64 CK HW Lp ltac:(lia)) as [Gp _].
    rewrite u_Z2bv in Gp by lia. lia. }
  destruct (@cs_H fx al_rom r4 m4 s ltac:(lia) ltac:(lia) R2) as (r5 & RUN5 & RA5 & R10_5 & AG5).
  rzs HW RUN5.
  pose proof (ct_RG_run2 regs r4 r5 s pix1 RG4 AG5) as RG5.
  assert (RO5 : ret_ok (getr r5 1)) by (rewrite RA5; red; apply bv_eq; reflexivity).
  apply (pxd_hop fx C Ar A4 m4 vm4 md r5 s (s - 64) pixt (w + 64) (h + 64) cdt datat cvt (getr r5 1) S kx bx CK HW Hs16 Hlo Hhi
           (proj1 RG5) ltac:(lia) ltac:(lia) (m8_sub s 64 Hs16 eq_refl) eq_refl RO5 (ct_RG_gp regs r5 s pix1 _ RG5 H4) R10_5 St Tt ltac:(lia) ltac:(lia)
           (O23LeptCloseP.fresh_sub Ar A (O23LeptCloseA.tblk pixt datat cdt cvt) SUBA (fun q Hq => Fr3 q (or_intror (or_introl Hq)))) SUB ROOM).
  intros A5 m5 vm5 r6 HW5 CS6 FT5 LE5 PW5 MK5 Z5 SUB5 PM5 ROOM5.
  rewrite RA5.
  pose proof SS as (N1 & N2 & SHP & LS & DS12).
  pose proof (O23LeptCloseT.sels_sy C A sh sel1 sel2 sv1 sv2 SS) as [Y1 Y2].
  assert (SUBA4 : sub_live A A4).
  { intros q k Lq.
    assert (NX : ~ (O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q \/ O23LeptCloseA.tblk pixsb datab cdb cvb q \/
                    O23LeptCloseA.tblk pixt datat cdt cvt q \/ O23LeptCloseA.tblk pixdb datad cdd cvd q)).
    { intros [H|[H|H]].
      - rewrite (proj1 (LS q (or_introl H))) in Lq. discriminate Lq.
      - rewrite (proj1 (LS q (or_intror H))) in Lq. discriminate Lq.
      - rewrite (Fr3 q H) in Lq. discriminate Lq. }
    rewrite (LE q NX). exact Lq. }
  assert (SUBA5 : sub_live A A5).
  { intros q k Lq. pose proof (SUBA4 q k Lq) as L4.
    assert (Qt : ~ O23LeptCloseA.tblk pixt datat cdt cvt q).
    { intros H. rewrite (Fr3 q (or_intror (or_introl H))) in Lq. discriminate Lq. }
    rewrite (LE5 q Qt). exact L4. }
  assert (KP5 : forall a : word, (s - 112 <= u a)%Z -> ~ (s - 72 <= u a < s - 48)%Z -> m5 a = m4 a)
    by (intros a Ha Hn; apply MK5; lia).
  destruct (ct_keep C Ar A4 A5 m4 m5 (O23LeptCloseA.tblk pixt datat cdt cvt) pix1 w h cm datas cv sel1 sel2 sv1 sv2 P1 SA1 SA2
              (fun q Hr Ht => Dr q (or_intror (or_introl Ht)) Hr) LE5 PW5) as (P1_5 & SA1_5 & SA2_5).
  pose proof (ct_tpx_keep C A4 A5 m4 m5 (O23LeptCloseA.tblk pixt datat cdt cvt) pixsb (w + 64) (h + 64) cdb datab cvb Tsb D12 LE5 PW5) as Tsb5.
  pose proof (ct_tpx_keep C A4 A5 m4 m5 (O23LeptCloseA.tblk pixt datat cdt cvt) pixdb (w + 64) (h + 64) cdd datad cvd Tdb
                (fun q Hq Ht => D23 q Ht Hq) LE5 PW5) as Tdb5.
  assert (Ssb5 : rdn SEGS m5 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 pixsb)).
  { apply (cell_keep m4 m5 (s - 56) s (s - 56) pixsb); try lia; [intros a Ha; apply MK5; lia | exact Ssb]. }
  assert (Sdb5 : rdn SEGS m5 (Z_to_bv 64 (s - 72)) 8 = Some (Z_to_le_bytes 8 pixdb)).
  { apply (cell_keep m4 m5 (s - 72) (s - 64) (s - 72) pixdb); try lia; [intros a Ha; apply MK5; lia | exact Sdb]. }
  pose proof (POSTM_trans C Ar s m m4 m5 PM PM5) as PMa5.
  assert (KC : (0 <= RK_cmapcopy)%Z) by (unfold RK_cmapcopy; lia).
  pose proof (O23LeptCloseA.cmT_le cm cdd CMZ) as Cdd.
  assert (RB0 : (0 <= RB_cmapT cm)%Z).
  { pose proof (O23LeptCloseA.cmT_le cm 0 (fun _ => eq_refl)) as C0. change (RB_cmapT 0) with 0%Z in C0. lia. }
  pose proof (ct_RG_hop regs r5 r6 s pix1 RG5 CS6) as RG6.
  assert (R18_6 : getr r6 18 = Z_to_bv 64 pixdb)
    by (rewrite (cs_kept_get r5 r6 18%bv CS6 cs18), (AG5 18%bv ltac:(notin_lit)); exact R18).
  assert (R9_6 : getr r6 9 = Z_to_bv 64 32)
    by (rewrite (cs_kept_get r5 r6 9%bv CS6 cs9), (AG5 9%bv ltac:(notin_lit)); exact R9).
  destruct (@cs_I fx al_rom r6 m5 pixdb R18_6 R9_6) as (r7 & RUN7 & RA7 & R10_7 & R11_7 & AG7).
  ct_pcfix RUN7.
  rzs HW5 RUN7.
  pose proof (ct_RG_run3 regs r6 r7 s pix1 RG6 AG7) as RG7.
  assert (RO7 : ret_ok (getr r7 1)) by (rewrite RA7; red; apply bv_eq; reflexivity).
  apply (rb_hop fx C A5 m5 vm5 md r7 s pixdb w h cdd datad cvd (getr r7 1) S kx bx CK HW5 Hs16 Hlo Hhi
           (proj1 RG7) eq_refl RO7 (ct_RG_gp regs r7 s pix1 _ RG7 H4) R10_7 R11_7 Tdb5 HO64 HO Hw Hh ROOM5 ltac:(lia) ltac:(lia)).
  intros A6 m6 vm6 r8 pixt2 cd2 data2 cv2 HW6 CS8 R10_8 Tt2 FR2 LE6 CZ2 CQ2 SUB6 PM6 ROOM6.
  rewrite RA7.
  pose proof (ct_RG_hop regs r7 r8 s pix1 RG7 CS8) as RG8.
  pose proof PM6 as [FR6 LV6].
  assert (KP6 : forall a : word, (s - 112 <= u a)%Z -> ~ (s - 72 <= u a < s - 48)%Z -> m6 a = m4 a).
  { intros a Ha Hn. rewrite (FRM_pw C (s - 112) m5 m6 CK FR6 ltac:(lia) a ltac:(lia)). apply KP5; assumption. }
  pose proof (O23LeptCloseA.PWK_weaken A5 (fun _ => True) (fun q => ~ O23LeptCloseA.tblk pixt2 data2 cd2 cv2 q) m5 m6
                (O23LeptCloseA.PWK_livk A5 m5 m6 LV6) (fun _ _ => I)) as PW6.
  assert (RL5 : forall q, O23LeptCloseA.rblk pix1 datas cm cv sel1 sel2 sv1 sv2 q -> exists n, live A5 q = Some n).
  { intros q [H|[H|H]].
    - exact (O23LeptCloseP.p1_live3 C Ar A5 m5 pix1 w h cm datas cv q P1_5 H).
    - exact (O23LeptCloseP.sblk_live _ A5 m5 sel1 sv1 q SA1_5 H).
    - exact (O23LeptCloseP.sblk_live _ A5 m5 sel2 sv2 q SA2_5 H). }
  assert (DR2 : forall q, O23LeptCloseA.rblk pix1 datas cm cv sel1 sel2 sv1 sv2 q -> ~ O23LeptCloseA.tblk pixt2 data2 cd2 cv2 q)
    by (intros q Hr Hq2; exact (O23LeptCloseP.apart_fresh A5 _ _ FR2 RL5 q Hq2 Hr)).
  assert (Dsb2 : forall q, O23LeptCloseA.tblk pixsb datab cdb cvb q -> ~ O23LeptCloseA.tblk pixt2 data2 cd2 cv2 q)
    by (intros q Hq Hq2; exact (O23LeptCloseP.apart_fresh A5 _ _ FR2 (fun q => O23LeptCloseP.tpx_live C A5 m5 pixsb (w + 64) (h + 64) cdb datab cvb q Tsb5) q Hq2 Hq)).
  assert (Ddb2 : forall q, O23LeptCloseA.tblk pixdb datad cdd cvd q -> ~ O23LeptCloseA.tblk pixt2 data2 cd2 cv2 q)
    by (intros q Hq Hq2; exact (O23LeptCloseP.apart_fresh A5 _ _ FR2 (fun q => O23LeptCloseP.tpx_live C A5 m5 pixdb (w + 64) (h + 64) cdd datad cvd q Tdb5) q Hq2 Hq)).
  destruct (ct_keep C Ar A5 A6 m5 m6 _ pix1 w h cm datas cv sel1 sel2 sv1 sv2 P1_5 SA1_5 SA2_5 DR2 LE6 PW6) as (P1_6 & SA1_6 & SA2_6).
  pose proof (ct_tpx_keep C A5 A6 m5 m6 _ pixsb (w + 64) (h + 64) cdb datab cvb Tsb5 Dsb2 LE6 PW6) as Tsb6.
  pose proof (ct_tpx_keep C A5 A6 m5 m6 _ pixdb (w + 64) (h + 64) cdd datad cvd Tdb5 Ddb2 LE6 PW6) as Tdb6.
  assert (Ssb6 : rdn SEGS m6 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 pixsb)).
  { apply (cell_keep m5 m6 (s - 56) s (s - 56) pixsb); try lia; [intros a Ha; apply (FRM_pw C (s - 112) m5 m6 CK FR6); lia | exact Ssb5]. }
  assert (Sdb6 : rdn SEGS m6 (Z_to_bv 64 (s - 72)) 8 = Some (Z_to_le_bytes 8 pixdb)).
  { apply (cell_keep m5 m6 (s - 72) (s - 64) (s - 72) pixdb); try lia; [intros a Ha; apply (FRM_pw C (s - 112) m5 m6 CK FR6); lia | exact Sdb5]. }
  pose proof (POSTM_trans C Ar s m m5 m6 PMa5 (POSTM_sub C Ar A5 s m5 m6 SUB5 (POSTM_mono C A5 (s - 112) s m5 m6 ltac:(lia) PM6))) as PMa6.
  pose proof (sub_live_trans Ar A5 A6 SUB5 SUB6) as SUBr6.
  assert (SOK : store_ok SEGS m6 (Z_to_bv 64 (s - 64)) 8 = true).
  { apply (W_sok_win C A6 m6 (with_vmmaps vm6 md) (s - 64) 8%nat CK HW6); [lia | change (Z.of_nat 8%nat) with 8%Z; lia]. }
  destruct (@cs_J fx al_rom r8 m6 s pixt2 ltac:(lia) ltac:(lia) SOK (proj1 RG8) R10_8) as (r9 & RUN9 & RA9 & R10_9 & AG9).
  ct_pcfix RUN9.
  rzs HW6 RUN9.
  assert (WP7 : W C A6 (O23LeptCloseSegs.CW8 m6 (s - 64) pixt2) (with_vmmaps vm6 md) /\ POSTM C A6 s m6 (O23LeptCloseSegs.CW8 m6 (s - 64) pixt2))
    by (unfold O23LeptCloseSegs.CW8; apply (WP_win C A6 A6 m6 m6 (with_vmmaps vm6 md)); [exact CK | split; [exact HW6 | apply POSTM_refl] | apply sub_live_refl
        | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia]).
  pose proof (O23LeptCloseA.PWK_weaken A6 (fun _ => True) (fun q => ~ False) m6 (O23LeptCloseSegs.CW8 m6 (s - 64) pixt2)
                (store_livk C A6 m6 (with_vmmaps vm6 md) s (s - 64) pixt2 CK Hlo Hhi HW6 ltac:(lia) ltac:(lia)) (fun _ _ => I)) as PW7.
  assert (KW7 : forall a : word, ~ (s - 64 <= u a < s - 56)%Z -> O23LeptCloseSegs.CW8 m6 (s - 64) pixt2 a = m6 a)
    by (intros a Ha; apply O23LeptCloseA.CW8_out; lia).
  pose proof (CW8_rd m6 (s - 64) pixt2) as St7.
  set (m7 := O23LeptCloseSegs.CW8 m6 (s - 64) pixt2) in *.
  destruct WP7 as [HW7 PM7].
  pose proof (ct_RG_run2 regs r8 r9 s pix1 RG8 AG9) as RG9.
  assert (RO9 : ret_ok (getr r9 1)) by (rewrite RA9; red; apply bv_eq; reflexivity).
  assert (Ssb7 : rdn SEGS m7 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 pixsb)).
  { apply (cell_keep m6 m7 (s - 56) s (s - 56) pixsb); try lia; [intros a Ha; apply KW7; lia | exact Ssb6]. }
  pose proof (ct_tpx_keep C A6 A6 m6 m7 (fun _ => False) pixsb (w + 64) (h + 64) cdb datab cvb Tsb6 (fun _ _ H => H) (fun _ _ => eq_refl) PW7) as Tsb7.
  apply (pxd_hop fx C Ar A6 m7 vm6 md r9 s (s - 56) pixsb (w + 64) (h + 64) cdb datab cvb (getr r9 1) S
           (kx - RK_pixcopy) (bx - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cdd)) CK HW7 Hs16 Hlo Hhi
           (proj1 RG9) ltac:(lia) ltac:(lia) (m8_sub s 56 Hs16 eq_refl) eq_refl RO9 (ct_RG_gp regs r9 s pix1 _ RG9 H4) R10_9 Ssb7 Tsb7 ltac:(lia) ltac:(lia)
           (O23LeptCloseP.fresh_sub Ar A (O23LeptCloseA.tblk pixsb datab cdb cvb) SUBA (fun q Hq => Fr3 q (or_introl Hq))) SUBr6 ROOM6).
  intros A7 m8 vm7 r10 HW8 CS10 FT7 LE7 PW8 MK8 Z8 SUB7 PM8 ROOM7.
  rewrite RA9.
  pose proof (ct_RG_hop regs r9 r10 s pix1 RG9 CS10) as RG10.
  assert (KP8 : forall a : word, (s - 112 <= u a)%Z -> ~ (s - 72 <= u a < s - 48)%Z -> m8 a = m4 a).
  { intros a Ha Hn. rewrite (MK8 a Ha ltac:(lia)), (KW7 a ltac:(lia)). apply KP6; assumption. }
  pose proof (POSTM_trans C Ar s m m6 m8 PMa6 (POSTM_trans C Ar s m6 m7 m8 (POSTM_sub C Ar A6 s m6 m7 SUBr6 PM7) PM8)) as PMa8.
  destruct (ct_keep C Ar A6 A6 m6 m7 (fun _ => False) pix1 w h cm datas cv sel1 sel2 sv1 sv2 P1_6 SA1_6 SA2_6
              (fun _ _ H => H) (fun _ _ => eq_refl) PW7) as (P1_7 & SA1_7 & SA2_7).
  destruct (ct_keep C Ar A6 A7 m7 m8 (O23LeptCloseA.tblk pixsb datab cdb cvb) pix1 w h cm datas cv sel1 sel2 sv1 sv2 P1_7 SA1_7 SA2_7
              (fun q Hr Hs => Dr q (or_introl Hs) Hr) LE7 PW8) as (P1_8 & SA1_8 & SA2_8).
  pose proof (ct_tpx_keep C A6 A6 m6 m7 (fun _ => False) pixdb (w + 64) (h + 64) cdd datad cvd Tdb6 (fun _ _ H => H) (fun _ _ => eq_refl) PW7) as Tdb7.
  pose proof (ct_tpx_keep C A6 A7 m7 m8 (O23LeptCloseA.tblk pixsb datab cdb cvb) pixdb (w + 64) (h + 64) cdd datad cvd Tdb7
                (fun q Hq Hs => D13 q Hs Hq) LE7 PW8) as Tdb8.
  pose proof (ct_tpx_keep C A6 A6 m6 m7 (fun _ => False) pixt2 w h cd2 data2 cv2 Tt2 (fun _ _ H => H) (fun _ _ => eq_refl) PW7) as Tt2_7.
  pose proof (ct_tpx_keep C A6 A7 m7 m8 (O23LeptCloseA.tblk pixsb datab cdb cvb) pixt2 w h cd2 data2 cv2 Tt2_7
                (fun q Hq2 Hs => Dsb2 q Hs Hq2) LE7 PW8) as Tt2_8.
  pose proof (tpx_range C A6 m6 (with_vmmaps vm6 md) pixt2 w h cd2 data2 cv2 CK HW6 Tt2 Hw Hh) as (Pt2a & Pt2b & _).
  assert (Sdb8 : rdn SEGS m8 (Z_to_bv 64 (s - 72)) 8 = Some (Z_to_le_bytes 8 pixdb)).
  { apply (cell_keep m6 m8 (s - 72) (s - 64) (s - 72) pixdb); try lia; [intros a Ha; rewrite (MK8 a ltac:(lia) ltac:(lia)); apply KW7; lia | exact Sdb6]. }
  assert (St8 : rdn SEGS m8 (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 pixt2)).
  { apply (cell_keep m7 m8 (s - 64) (s - 56) (s - 64) pixt2); try lia; [intros a Ha; apply MK8; lia | exact (St7 ltac:(lia) ltac:(lia) ltac:(lia))]. }
  destruct (@cs_K fx al_rom r10 m8 s ltac:(lia) ltac:(lia) (proj1 RG10)) as (r11 & RUN11 & RA11 & R10_11 & AG11).
  ct_pcfix RUN11.
  rzs HW8 RUN11.
  pose proof (ct_RG_run2 regs r10 r11 s pix1 RG10 AG11) as RG11.
  assert (RO11 : ret_ok (getr r11 1)) by (rewrite RA11; red; apply bv_eq; reflexivity).
  apply (pxd_hop fx C Ar A7 m8 vm7 md r11 s (s - 72) pixdb (w + 64) (h + 64) cdd datad cvd (getr r11 1) S
           (kx - RK_pixcopy) (bx - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cdd)) CK HW8 Hs16 Hlo Hhi
           (proj1 RG11) ltac:(lia) ltac:(lia) (m8_sub s 72 Hs16 eq_refl) eq_refl RO11 (ct_RG_gp regs r11 s pix1 _ RG11 H4) R10_11 Sdb8 Tdb8 ltac:(lia) ltac:(lia)
           (O23LeptCloseP.fresh_sub Ar A (O23LeptCloseA.tblk pixdb datad cdd cvd) SUBA (fun q Hq => Fr3 q (or_intror (or_intror Hq)))) SUB7 ROOM7).
  intros A8 m9 vm8 r12 HW9 CS12 FT8 LE8 PW9 MK9 Z9 SUB8 PM9 ROOM8.
  rewrite RA11.
  pose proof (ct_RG_hop regs r11 r12 s pix1 RG11 CS12) as RG12.
  assert (KP9 : forall a : word, (s - 112 <= u a)%Z -> ~ (s - 72 <= u a < s - 48)%Z -> m9 a = m4 a).
  { intros a Ha Hn. rewrite (MK9 a Ha ltac:(lia)). apply KP8; assumption. }
  pose proof (POSTM_trans C Ar s m m8 m9 PMa8 PM9) as PMa9.
  destruct (ct_keep C Ar A7 A8 m8 m9 (O23LeptCloseA.tblk pixdb datad cdd cvd) pix1 w h cm datas cv sel1 sel2 sv1 sv2 P1_8 SA1_8 SA2_8
              (fun q Hr Hd => Dr q (or_intror (or_intror Hd)) Hr) LE8 PW9) as (P1_9 & SA1_9 & SA2_9).
  pose proof (ct_tpx_keep C A7 A8 m8 m9 (O23LeptCloseA.tblk pixdb datad cdd cvd) pixt2 w h cd2 data2 cv2 Tt2_8
                (fun q Hq2 Hd => Ddb2 q Hd Hq2) LE8 PW9) as Tt2_9.
  assert (St9 : rdn SEGS m9 (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 pixt2)).
  { apply (cell_keep m8 m9 (s - 64) (s - 56) (s - 64) pixt2); try lia; [intros a Ha; apply MK9; lia | exact St8]. }
  assert (E9 : forall q, ~ ((O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q) \/ O23LeptCloseA.tblk pixt2 data2 cd2 cv2 q) ->
                 live A8 q = live A q).
  { intros q NT.
    assert (NT2 : ~ O23LeptCloseA.tblk pixt2 data2 cd2 cv2 q) by (intros H; apply NT; right; exact H).
    assert (NS : ~ (O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q)) by (intros H; apply NT; left; exact H).
    destruct (O23LeptCloseA.tblk_dec pixdb datad cdd cvd q) as [Qdb|Qdb].
    { rewrite (FT8 q Qdb). symmetry. exact (Fr3 q (or_intror (or_intror Qdb))). }
    rewrite (LE8 q Qdb).
    destruct (O23LeptCloseA.tblk_dec pixsb datab cdb cvb q) as [Qsb|Qsb].
    { rewrite (FT7 q Qsb). symmetry. exact (Fr3 q (or_introl Qsb)). }
    rewrite (LE7 q Qsb), (LE6 q NT2).
    destruct (O23LeptCloseA.tblk_dec pixt datat cdt cvt q) as [Qt|Qt].
    { rewrite (FT5 q Qt). symmetry. exact (Fr3 q (or_intror (or_introl Qt))). }
    rewrite (LE5 q Qt). apply LE.
    intros [H|[H|[H|[H|H]]]];
      [exact (NS (or_introl H)) | exact (NS (or_intror H)) | exact (Qsb H) | exact (Qt H) | exact (Qdb H)]. }
  assert (F9 : forall q, (O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q) \/ O23LeptCloseA.tblk pixt2 data2 cd2 cv2 q ->
                 live A q = None).
  { intros q [H|H].
    - exact (proj1 (LS q H)).
    - exact (O23LeptCloseP.fresh_sub A A5 _ SUBA5 FR2 q H). }
  assert (L9 : forall q, (O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q) \/ O23LeptCloseA.tblk pixt2 data2 cd2 cv2 q ->
                 exists n, live A8 q = Some n).
  { intros q [[H|H]|H].
    - exact (O23LeptCloseP.sblk_live _ A8 m9 sel1 sv1 q SA1_9 H).
    - exact (O23LeptCloseP.sblk_live _ A8 m9 sel2 sv2 q SA2_9 H).
    - exact (O23LeptCloseP.tpx_live C A8 m9 pixt2 w h cd2 data2 cv2 q Tt2_9 H). }
  assert (J9 : forall q, (O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q) \/ O23LeptCloseA.tblk pixt2 data2 cd2 cv2 q ->
                 ~ O23LeptCloseA.tblk pix1 datas cm cv q).
  { intros q [H|H].
    - exact (DJ q H).
    - intros Hp. exact (DR2 q (or_introl Hp) H). }
  pose proof (O23LeptCloseA.cmT_le cm cd2 (fun H => CZ2 (CMZ H))) as Ccd2.
  destruct (@cs_L fx al_rom r12 m9 s pix1 pixt2 ltac:(lia) ltac:(lia) PB ltac:(lia) St9 (proj1 RG12) (proj1 (proj2 RG12)))
    as (r13 & RUN13 & RA13 & R10_13 & R11_13 & AG13).
  ct_pcfix RUN13.
  rzs HW9 RUN13.
  pose proof (ct_RG_run3 regs r12 r13 s pix1 RG12 AG13) as RG13.
  assert (RO13 : ret_ok (getr r13 1)) by (rewrite RA13; red; apply bv_eq; reflexivity).
  apply (copy_hop fx PCG C Ar A A8 m9 vm8 md r13 s pix1 w h cm datas cv pixt2 cd2 data2 cv2 (getr r13 1) S
           (kx - RK_pixcopy) (bx - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cdd))
           (fun q => (O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q) \/ O23LeptCloseA.tblk pixt2 data2 cd2 cv2 q)
           CK HW9 Hs16 Hlo Hhi (proj1 RG13) eq_refl RO13 (ct_RG_gp regs r13 s pix1 _ RG13 H4) R10_13 R11_13 P1_9 Hpd Tt2_9 HO Hw Hh
           (fun q Hq2 Hp => DR2 q (or_introl Hp) Hq2) SUB8 (fun H => CZ2 (CMZ H)) (O23LeptCloseA.cmeq_chain cdd cvd cd2 cv2 cv CZ2 CMQ CQ2)
           E9 F9 L9 J9 LP1 ROOM8 ltac:(lia) ltac:(lia)).
  intros A9 m10 vm9 r14 cm' cv' HW10 CS14 R10_14 P1_10 PW10 LK10 MK10 CSL10 DJ10 SUB9 PM10 ROOM9.
  rewrite RA13.
  pose proof (ct_RG_hop regs r13 r14 s pix1 RG13 CS14) as RG14.
  assert (KP10 : forall a : word, (s - 112 <= u a)%Z -> ~ (s - 72 <= u a < s - 48)%Z -> m10 a = m4 a).
  { intros a Ha Hn. rewrite (MK10 a Ha). apply KP9; assumption. }
  pose proof (POSTM_trans C Ar s m m9 m10 PMa9 PM10) as PMa10.
  pose proof (O23LeptCloseA.tpx_keep C A8 A9 (fun q => ~ O23LeptCloseA.tblk pix1 datas cm cv q) m9 m10 pixt2 w h cd2 data2 cv2 Tt2_9
                (fun q Hq => match O23LeptCloseP.tpx_live C A8 m9 pixt2 w h cd2 data2 cv2 q Tt2_9 Hq with
                             | ex_intro _ n Ln => eq_trans (LK10 q n Ln (J9 q (or_intror Hq))) (eq_sym Ln) end)
                PW10 (J9 (Z_to_bv 64 pixt2) (or_intror (or_introl eq_refl)))
                (fun Hc => J9 (Z_to_bv 64 cd2) (or_intror (or_intror (or_intror (conj Hc (or_introl eq_refl))))))) as Tt2_10.
  assert (SA1_10 : sel_at (alloc_top (c_vm C)) A9 m10 sel1 sv1).
  { apply (O23LeptCloseA.sel_at_keepP (alloc_top (c_vm C)) A8 A9 (fun q => ~ O23LeptCloseA.tblk pix1 datas cm cv q) m9 m10 sel1 sv1 ATL SA1_9).
    - intros q Hq. destruct (O23LeptCloseP.sblk_live _ A8 m9 sel1 sv1 q SA1_9 Hq) as [n Ln]. rewrite Ln. exact (LK10 q n Ln (DJ q (or_introl Hq))).
    - exact PW10.
    - intros q Hq. exact (DJ q (or_introl Hq)). }
  assert (SA2_10 : sel_at (alloc_top (c_vm C)) A9 m10 sel2 sv2).
  { apply (O23LeptCloseA.sel_at_keepP (alloc_top (c_vm C)) A8 A9 (fun q => ~ O23LeptCloseA.tblk pix1 datas cm cv q) m9 m10 sel2 sv2 ATL SA2_9).
    - intros q Hq. destruct (O23LeptCloseP.sblk_live _ A8 m9 sel2 sv2 q SA2_9 Hq) as [n Ln]. rewrite Ln. exact (LK10 q n Ln (DJ q (or_intror Hq))).
    - exact PW10.
    - intros q Hq. exact (DJ q (or_intror Hq)). }
  assert (St10 : rdn SEGS m10 (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 pixt2)).
  { apply (cell_keep m9 m10 (s - 64) (s - 56) (s - 64) pixt2); try lia; [intros a Ha; apply MK10; lia | exact St9]. }
  destruct (@cs_M fx al_rom r14 m10 s ltac:(lia) ltac:(lia) (proj1 RG14)) as (r15 & RUN15 & RA15 & R10_15 & AG15).
  ct_pcfix RUN15.
  rzs HW10 RUN15.
  pose proof (ct_RG_run2 regs r14 r15 s pix1 RG14 AG15) as RG15.
  assert (RO15 : ret_ok (getr r15 1)) by (rewrite RA15; red; apply bv_eq; reflexivity).
  apply (pxd_hop fx C Ar A9 m10 vm9 md r15 s (s - 64) pixt2 w h cd2 data2 cv2 (getr r15 1) S
           (kx - RK_pixcopy - RK_cmapcopy) (bx - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cdd) - RB_cmapT cd2) CK HW10 Hs16 Hlo Hhi
           (proj1 RG15) ltac:(lia) ltac:(lia) (m8_sub s 64 Hs16 eq_refl) eq_refl RO15 (ct_RG_gp regs r15 s pix1 _ RG15 H4) R10_15 St10 Tt2_10 Hw Hh
           (O23LeptCloseP.fresh_sub Ar A (O23LeptCloseA.tblk pixt2 data2 cd2 cv2) SUBA (fun q Hq => F9 q (or_intror Hq))) SUB9 ROOM9).
  intros A10 m11 vm10 r16 HW11 CS16 FT10 LE10 PW11 MK11 Z11 SUB10 PM11 ROOM10.
  rewrite RA15.
  pose proof (ct_RG_hop regs r15 r16 s pix1 RG15 CS16) as RG16.
  assert (KP11 : forall a : word, (s - 112 <= u a)%Z -> ~ (s - 72 <= u a < s - 48)%Z -> m11 a = m4 a).
  { intros a Ha Hn. rewrite (MK11 a Ha ltac:(lia)). apply KP10; assumption. }
  pose proof (FCL_keep s ret regs sh sel1 sel2 m4 m11 ltac:(lia) ltac:(lia) FC ltac:(intros a Ha; apply KP11; lia)) as (FS11 & C1 & C2 & Z1 & Z2).
  pose proof (POSTM_trans C Ar s m m10 m11 PMa10 PM11) as PMa11.
  destruct (ct_keep C Ar A9 A10 m10 m11 (O23LeptCloseA.tblk pixt2 data2 cd2 cv2) pix1 w h cm' datas cv' sel1 sel2 sv1 sv2 P1_10 SA1_10 SA2_10
              ltac:(intros q [Hp|Hs] Hq2; [exact (DJ10 q (or_intror Hq2) Hp) | exact (DR2 q (or_intror Hs) Hq2)]) LE10 PW11) as (P1_11 & SA1_11 & SA2_11).
  pose proof (O23LeptCloseA.cslm_free
                (fun q => (O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q) \/ O23LeptCloseA.tblk pixt2 data2 cd2 cv2 q)
                (fun q => O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q) (O23LeptCloseA.tblk pixt2 data2 cd2 cv2)
                A A9 A10 cm cv cm' cv' CSL10 FT10 LE10 (fun q Hq => F9 q (or_intror Hq)) (fun q => O23LeptCloseA.tblk_dec pixt2 data2 cd2 cv2 q)
                ltac:(intros q NS1 NS2 [Hs|Hs]; [exact (NS1 Hs) | exact (NS2 Hs)])) as CSL11.
  match goal with |- context [mkst _ (Z_to_bv 64 ?n) _ _] => replace (Z_to_bv 64 n) with (0xa4c28 : word) by (apply bv_eq; reflexivity) end.
  apply (csc_seld4 sh fr C Ar A m md regs s pix1 w h cm datas cv ret S kR bR fr1 cs1 A10 m11 vm10 r16 cm' cv'
           (kx - RK_pixcopy - RK_cmapcopy) (bx - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cdd) - RB_cmapT cd2) sel1 sel2 sv1 sv2
           CK Hs16 Hlo Hhi Hret H2 H4 SUBA FZ FK HW11 (proj1 RG16) (proj1 (proj2 RG16)) (proj2 (proj2 RG16)) FS11 C1 C2 Z1 Z2
           SUB10 PMa11 P1_11 SA1_11 SA2_11 SS (fun q H => DJ10 q (or_introl H)) CSL11 ROOM10 ltac:(lia) ltac:(lia) Hk0 Hb0 HK).
Qed.

Lemma csc_normal : forall (sh : bool) (fr : bvmap 5 word) C Ar A m md regs (s pix1 w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z)
    (fr1 : bvmap 5 word) (cs1 : bv 32) (A0 : AS) (m0 : word -> option byte) (vm0 : VmMaps) (r0 : bvmap 5 word) (kx bx : Z)
    (sel1 sel2 : Z) (sv1 sv2 : selv) (c1 c2 : Z -> Z -> Z) (pixsb cdb datab : Z) (cvb : cmapv),
  pcg2_contract (mkFP fr1 cs1) ->
  Cok C -> MBC C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 4 = Z_to_bv 64 0x1381d0 -> sub_live Ar A ->
  pix1 <> datas -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z -> O23LeptPixHdr.hdr_ok (w + 64) (h + 64) 1 ->
  frm_zero cs1 -> (forall r : reg, In (u r) fs_list -> reg_get fr1 r = reg_get fr r) ->
  W C A0 m0 (with_vmmaps vm0 md) ->
  getr r0 2 = Z_to_bv 64 (s - 112) -> getr r0 8 = Z_to_bv 64 pix1 -> getr r0 9 = Z_to_bv 64 32 ->
  getr r0 18 = Z_to_bv 64 (O23LeptCloseA.hsz sh) -> getr r0 19 = Z_to_bv 64 (O23LeptCloseA.vsz sh) -> getr r0 10 = Z_to_bv 64 pixsb -> O23LeptCloseT.rkept regs r0 ->
  RST C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 m0 ->
  O23LeptCloseT.sels_static C A sh sel1 sel2 sv1 sv2 ->
  (forall q, O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q -> ~ O23LeptCloseA.tblk pix1 datas cm cv q) ->
  (forall q, O23LeptCloseA.tblk pix1 datas cm cv q -> exists n, live A q = Some n) ->
  O23LeptCloseA.tpx C A0 m0 pixsb (w + 64) (h + 64) cdb datab cvb ->
  (forall q, O23LeptCloseA.tblk pixsb datab cdb cvb q -> live A q = None) ->
  (forall q, O23LeptCloseA.tblk pixsb datab cdb cvb q -> ~ O23LeptCloseA.rblk pix1 datas cm cv sel1 sel2 sv1 sv2 q) ->
  (cm = 0%Z -> cdb = 0%Z) -> O23LeptCloseA.cmeq cdb cvb cv ->
  sub_live A A0 ->
  (forall q, ~ (O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q \/ O23LeptCloseA.tblk pixsb datab cdb cvb q) -> live A0 q = live A q) ->
  aroom A0 vm0 kx bx ->
  (kR - O23LeptCloseSpec.RK_csc (O23LeptCloseA.vsz sh) + (3 * RK_pixcopy + RK_cmapcopy) <= kx)%Z ->
  (bR - O23LeptCloseSpec.RB_csc (O23LeptCloseA.vsz sh) w h cm + (2 * (RB_pixT (4 * (wpl_of (w + 64) 1 * (h + 64))) + RB_cmapT cm) + (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm) + RB_cmapT cm) <= bx)%Z ->
  (0 <= kR - O23LeptCloseSpec.RK_csc (O23LeptCloseA.vsz sh))%Z -> (0 <= bR - O23LeptCloseSpec.RB_csc (O23LeptCloseA.vsz sh) w h cm)%Z ->
  csc_K fr C Ar A m md regs s pix1 (O23LeptCloseA.vsz sh) w h cm datas cv ret S kR bR ->
  realizes SEGS (mkCfg (@mkst (mkFP fr1 cs1) r0 (0xa4ad0 : word) m0 al_rom) (with_vmmaps vm0 md)) S.
Proof.
  intros sh fr C Ar A m md regs s pix1 w h cm datas cv ret S kR bR fr1 cs1 A0 m0 vm0 r0 kx bx sel1 sel2 sv1 sv2 c1 c2 pixsb cdb datab cvb
    PCG CK MB Hs16 Hlo Hhi Hret H2 H4 SUBA HPD HDR Hw Hh HDR64 FZ FK HW0 R2 R8 R9 R18 R19 R10 RK RS SS DJ P1L TB TBF TBR CMB CMEQ
    SUB0 LA0 ROOM Hk Hb Hk0 Hb0 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. pose proof Hlo as Hlo'. unfold CSC_STACK in Hlo'.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (KP : (0 <= RK_pixcopy)%Z /\ (0 <= RK_cmapcopy)%Z) by (unfold RK_pixcopy, RK_pix, RK_cmapcopy; lia).
  pose proof (RB_pixT_nonneg (4 * (wpl_of w 1 * h))) as RBw.
  pose proof (RB_pixT_nonneg (4 * (wpl_of (w + 64) 1 * (h + 64)))) as RBp.
  pose proof (RB_cmapT_le cm) as RCm. pose proof (RB_cmapT_le cdb) as RCb0.
  pose proof (O23LeptCloseA.cmT_le cm cdb CMB) as RCb.
  assert (R4 : getr r0 4 = Z_to_bv 64 0x1381d0) by (rewrite (RK 4%bv ltac:(in_lit)); exact H4).
  pose proof SS as (_ & _ & SH & _ & _).
  destruct (O23LeptCloseP.shape_org _ _ _ _ SH) as (X1 & Y1 & X2 & Y2).
  pose proof RS as (_ & _ & _ & _ & _ & SUBr0 & _ & _ & SA1_0 & SA2_0 & _).
  assert (B1 : (0 <= sel1 < 2 ^ 64)%Z) by (destruct SA1_0 as (_ & _ & (B & B' & _) & _); lia).
  assert (B2 : (0 <= sel2 < 2 ^ 64)%Z) by (destruct SA2_0 as (_ & _ & (B & B' & _) & _); lia).
  destruct (tpx_range C A0 m0 _ pixsb (w + 64) (h + 64) cdb datab cvb CK HW0 TB ltac:(lia) ltac:(lia)) as (PB1 & PB2 & _).
  assert (LB0 : forall q, O23LeptCloseA.tblk pixsb datab cdb cvb q -> exists n, live A0 q = Some n)
    by (intros q Hq; exact (O23LeptCloseP.tpx_live C A0 m0 pixsb (w + 64) (h + 64) cdb datab cvb q TB Hq)).
  assert (LS1_0 : forall q, O23LeptCloseA.sblk sel1 sv1 q -> exists n, live A0 q = Some n)
    by (intros q Hq; exact (O23LeptCloseP.sblk_live _ A0 m0 sel1 sv1 q SA1_0 Hq)).
  assert (LS2_0 : forall q, O23LeptCloseA.sblk sel2 sv2 q -> exists n, live A0 q = Some n)
    by (intros q Hq; exact (O23LeptCloseP.sblk_live _ A0 m0 sel2 sv2 q SA2_0 Hq)).
  assert (LR0 : forall q, O23LeptCloseA.rblk pix1 datas cm cv sel1 sel2 sv1 sv2 q -> exists n, live A0 q = Some n)
    by (intros q Hq; exact (rblk_live C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 m0 q RS Hq)).
  assert (RD1 : rdn SEGS (O23LeptCloseSegs.CW8 m0 (s - 56) pixsb) (Z_to_bv 64 (O23LeptCloseA.co1 sh s)) 8 = Some (Z_to_le_bytes 8 sel1)).
  { pose proof (FCL_of_RST C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 m0 RS) as (_ & C1 & _).
    apply V23LeptCloseR.cr_cw8_fwd; try exact C1; destruct sh; unfold O23LeptCloseA.co1; lia. }
  destruct (@cs_D (mkFP fr1 cs1) al_rom sh r0 m0 s pixsb sel1 ltac:(lia) ltac:(lia) B1
              (W_sok_win C A0 m0 _ (s - 56) 8 CK HW0 ltac:(lia) ltac:(cbn; lia)) RD1 R2 R10 R18 R19)
    as (r1 & RUN1 & Q1_1 & Q10_1 & Q11_1 & Q12_1 & AG1).
  n1pcfix RUN1. rzs HW0 RUN1.
  destruct (RST_store C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 m0 (with_vmmaps vm0 md) (s - 56) pixsb
              CK Hlo Hhi HW0 ltac:(lia) ltac:(lia) RS) as [HW1 RS1].
  pose proof (CW8_rd m0 (s - 56) pixsb ltac:(lia) ltac:(lia) ltac:(lia)) as S56_1.
  pose proof (n1_tpx_st C A0 m0 _ s (s - 56) pixsb pixsb (w + 64) (h + 64) cdb datab cvb CK Hlo Hhi HW0 ltac:(lia) ltac:(lia) TB) as TB1.
  pose proof RS1 as (_ & _ & _ & _ & _ & _ & _ & _ & SA1_1 & _ & SC1_1 & _).
  apply (dil_hop (mkFP fr1 cs1) C A0 _ vm0 md r1 s pixsb (w + 64)%Z (h + 64)%Z cdb datab cvb sel1 sv1 c1 (Z_to_bv 64 (pcD sh)) S kx bx
           CK HW1 Hs16 Hlo Hhi ltac:(n1kp) Q1_1 (ret_ok_pcD sh) ltac:(n1kp) Q10_1 Q11_1 Q12_1 SA1_1 SC1_1 X1 Y1
           (fun q Hq E => TBR q (n1_tbq pixsb datab cdb cvb q E) (or_intror (or_introl Hq)))
           TB1 HDR64 ltac:(lia) ltac:(lia) ROOM ltac:(lia) ltac:(lia)).
  intros A2 m2 vm2 r2 pixt cdt datat cvt HW2 CS2 V10_2 TT2 FT2 LT2 CM2 CE2 SUB2 PM2 ROOM2.
  pose proof (n1_rst_new C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 _ A2 m2
                (O23LeptCloseA.tblk pixt datat cdt cvt) CK Hlo Hhi RS1 FT2 LT2 SUB2 PM2) as RS2.
  pose proof (n1_tpx_new C A0 A2 _ m2 pixsb (w + 64) (h + 64) cdb datab cvb (O23LeptCloseA.tblk pixt datat cdt cvt) TB1 FT2 LT2 (proj2 PM2)) as TB2.
  pose proof (V23LeptCloseR.cr_frm_rd C (s - 112) _ m2 (s - 56) pixsb CK (proj1 PM2) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S56_1) as S56_2.
  destruct (tpx_range C A2 m2 _ pixt (w + 64) (h + 64) cdt datat cvt CK HW2 TT2 ltac:(lia) ltac:(lia)) as (PT1 & PT2 & _).
  pose proof (O23LeptCloseA.cmT_le cm cdt (fun E => CM2 (CMB E))) as RCt. pose proof (RB_cmapT_le cdt) as RCt0.
  pose proof RS2 as (_ & _ & _ & _ & _ & SUBr2 & _ & _ & SA1_2 & SA2_2 & _).
  assert (LB2 : forall q, O23LeptCloseA.tblk pixsb datab cdb cvb q -> exists n, live A2 q = Some n)
    by (intros q Hq; exact (O23LeptCloseP.tpx_live C A2 m2 pixsb (w + 64) (h + 64) cdb datab cvb q TB2 Hq)).
  assert (LT2v : forall q, O23LeptCloseA.tblk pixt datat cdt cvt q -> exists n, live A2 q = Some n)
    by (intros q Hq; exact (O23LeptCloseP.tpx_live C A2 m2 pixt (w + 64) (h + 64) cdt datat cvt q TT2 Hq)).
  assert (LS1_2 : forall q, O23LeptCloseA.sblk sel1 sv1 q -> exists n, live A2 q = Some n)
    by (intros q Hq; exact (O23LeptCloseP.sblk_live _ A2 m2 sel1 sv1 q SA1_2 Hq)).
  assert (LS2_2 : forall q, O23LeptCloseA.sblk sel2 sv2 q -> exists n, live A2 q = Some n)
    by (intros q Hq; exact (O23LeptCloseP.sblk_live _ A2 m2 sel2 sv2 q SA2_2 Hq)).
  assert (LR2 : forall q, O23LeptCloseA.rblk pix1 datas cm cv sel1 sel2 sv1 sv2 q -> exists n, live A2 q = Some n)
    by (intros q Hq; exact (rblk_live C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A2 m2 q RS2 Hq)).
  pose proof (FCL_of_RST C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A2 m2 RS2) as (_ & _ & C2_2 & _).
  destruct (@cs_E (mkFP fr1 cs1) al_rom sh r2 m2 s pixt sel2 ltac:(lia) ltac:(lia) B2
              (W_sok_win C A2 m2 _ (s - 64) 8 CK HW2 ltac:(lia) ltac:(cbn; lia)) C2_2 ltac:(n1kp) V10_2)
    as (r3 & RUN3 & Q1_3 & Q19_3 & Q10_3 & Q11_3 & Q12_3 & AG3).
  n1pcfix RUN3. rzs HW2 RUN3.
  destruct (RST_store C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A2 m2 (with_vmmaps vm2 md) (s - 64) pixt
              CK Hlo Hhi HW2 ltac:(lia) ltac:(lia) RS2) as [HW3 RS3].
  pose proof (CW8_rd m2 (s - 64) pixt ltac:(lia) ltac:(lia) ltac:(lia)) as S64_3.
  pose proof (V23LeptCloseR.cr_cw8_fwd m2 (s - 64) (s - 56) pixt pixsb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S56_2) as S56_3.
  pose proof (n1_tpx_st C A2 m2 _ s (s - 64) pixt pixsb (w + 64) (h + 64) cdb datab cvb CK Hlo Hhi HW2 ltac:(lia) ltac:(lia) TB2) as TB3.
  pose proof (n1_tpx_st C A2 m2 _ s (s - 64) pixt pixt (w + 64) (h + 64) cdt datat cvt CK Hlo Hhi HW2 ltac:(lia) ltac:(lia) TT2) as TT3.
  pose proof RS3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SA2_3 & _ & SC2_3).
  apply (dil_hop (mkFP fr1 cs1) C A2 _ vm2 md r3 s pixt (w + 64)%Z (h + 64)%Z cdt datat cvt sel2 sv2 c2 (Z_to_bv 64 (pcE sh)) S
           (kx - RK_pixcopy)%Z (bx - (RB_pixT (4 * (wpl_of (w + 64) 1 * (h + 64))) + RB_cmapT cdb))%Z
           CK HW3 Hs16 Hlo Hhi ltac:(n1kp) Q1_3 (ret_ok_pcE sh) ltac:(n1kp) Q10_3 Q11_3 Q12_3 SA2_3 SC2_3 X2 Y2
           (fun q Hq E => n1_ap A0 _ _ FT2 LS2_0 _ _ (n1_tbp pixt datat cdt cvt) Hq (eq_sym E))
           TT3 HDR64 ltac:(lia) ltac:(lia) ROOM2 ltac:(lia) ltac:(lia)).
  intros A4 m4 vm4 r4 pixdb cdd datad cvd HW4 CS4 V10_4 TD4 FD4 LD4 CM4 CE4 SUB4 PM4 ROOM4.
  pose proof (n1_rst_new C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A2 _ A4 m4
                (O23LeptCloseA.tblk pixdb datad cdd cvd) CK Hlo Hhi RS3 FD4 LD4 SUB4 PM4) as RS4.
  pose proof (n1_tpx_new C A2 A4 _ m4 pixsb (w + 64) (h + 64) cdb datab cvb (O23LeptCloseA.tblk pixdb datad cdd cvd) TB3 FD4 LD4 (proj2 PM4)) as TB4.
  pose proof (n1_tpx_new C A2 A4 _ m4 pixt (w + 64) (h + 64) cdt datat cvt (O23LeptCloseA.tblk pixdb datad cdd cvd) TT3 FD4 LD4 (proj2 PM4)) as TT4.
  pose proof (V23LeptCloseR.cr_frm_rd C (s - 112) _ m4 (s - 56) pixsb CK (proj1 PM4) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S56_3) as S56_4.
  pose proof (V23LeptCloseR.cr_frm_rd C (s - 112) _ m4 (s - 64) pixt CK (proj1 PM4) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S64_3) as S64_4.
  destruct (tpx_range C A4 m4 _ pixdb (w + 64) (h + 64) cdd datad cvd CK HW4 TD4 ltac:(lia) ltac:(lia)) as (PD1 & PD2 & _).
  pose proof (FCL_of_RST C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A4 m4 RS4) as (_ & C1_4 & _).
  destruct (@cs_F (mkFP fr1 cs1) al_rom sh r4 m4 s pixt pixdb sel1 ltac:(lia) ltac:(lia) B1
              (W_sok_win C A4 m4 _ (s - 72) 8 CK HW4 ltac:(lia) ltac:(cbn; lia)) C1_4 ltac:(n1kp) V10_4 ltac:(n1kp))
    as (r5 & RUN5 & Q1_5 & Q18_5 & Q10_5 & Q11_5 & Q12_5 & AG5).
  n1pcfix RUN5. rzs HW4 RUN5.
  destruct (RST_store C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A4 m4 (with_vmmaps vm4 md) (s - 72) pixdb
              CK Hlo Hhi HW4 ltac:(lia) ltac:(lia) RS4) as [HW5 RS5].
  pose proof (CW8_rd m4 (s - 72) pixdb ltac:(lia) ltac:(lia) ltac:(lia)) as S72_5.
  pose proof (V23LeptCloseR.cr_cw8_fwd m4 (s - 72) (s - 56) pixdb pixsb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S56_4) as S56_5.
  pose proof (V23LeptCloseR.cr_cw8_fwd m4 (s - 72) (s - 64) pixdb pixt ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S64_4) as S64_5.
  pose proof (n1_tpx_st C A4 m4 _ s (s - 72) pixdb pixsb (w + 64) (h + 64) cdb datab cvb CK Hlo Hhi HW4 ltac:(lia) ltac:(lia) TB4) as TB5.
  pose proof (n1_tpx_st C A4 m4 _ s (s - 72) pixdb pixt (w + 64) (h + 64) cdt datat cvt CK Hlo Hhi HW4 ltac:(lia) ltac:(lia) TT4) as TT5.
  pose proof (n1_tpx_st C A4 m4 _ s (s - 72) pixdb pixdb (w + 64) (h + 64) cdd datad cvd CK Hlo Hhi HW4 ltac:(lia) ltac:(lia) TD4) as TD5.
  pose proof RS5 as (_ & _ & _ & _ & _ & SUBr5 & _ & _ & SA1_5 & _ & SC1_5 & _).
  apply (ero_hop (mkFP fr1 cs1) C Ar A4 _ (with_vmmaps vm4 md) r5 s pixt pixdb (w + 64)%Z (h + 64)%Z cdt datat cvt cdd datad cvd
           sel1 sv1 c1 (Z_to_bv 64 (pcF sh)) S CK MB HW5 SUBr5 Hs16 Hlo Hhi ltac:(n1kp) Q1_5 (ret_ok_pcF sh) Q10_5 Q11_5 Q12_5
           TT5 TD5 HDR64 ltac:(lia) ltac:(lia)
           (fun q H1 H2 => O23LeptCloseP.apart_fresh A2 _ _ FD4 LT2v q H1 H2)
           (O23LeptCloseP.fresh_sub Ar A0 _ SUBr0 FT2 _ (n1_tbd pixt datat cdt cvt))
           SA1_5 SC1_5 X1 Y1
           (fun q Hq => conj (fun E => n1_ap A2 _ _ FD4 LS1_2 _ _ (n1_tbp pixdb datad cdd cvd) Hq (eq_sym E))
                             (fun E => n1_ap A0 _ _ FT2 LS1_0 _ _ (n1_tbd pixt datat cdt cvt) Hq (eq_sym E)))).
  intros m6 r6 HW6 CS6 V10_6 PW6 UP6 PM6.
  assert (ND1 : forall q, O23LeptCloseA.rblk pix1 datas cm cv sel1 sel2 sv1 sv2 q -> q <> Z_to_bv 64 datat)
    by (intros q Hq E; exact (n1_ap A0 _ _ FT2 LR0 _ _ (n1_tbd pixt datat cdt cvt) Hq (eq_sym E))).
  pose proof (n1_rst_ero C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A4 _ m6 (Z_to_bv 64 datat)
                CK ltac:(lia) Hhi RS5 ND1 PW6 UP6 PM6) as RS6.
  pose proof (n1_tpx_eroN C A4 _ m6 pixsb (w + 64) (h + 64) cdb datab cvb (Z_to_bv 64 datat) TB5 PW6
                (fun q Hq E => n1_ap A0 _ _ FT2 LB0 _ _ (n1_tbd pixt datat cdt cvt) Hq (eq_sym E))) as TB6.
  destruct (tpx_self_ne C A4 _ _ pixt (w + 64) (h + 64) cdt datat cvt CK HW5 TT5 ltac:(lia) ltac:(lia)) as [SN1 SN2].
  pose proof (n1_tpx_ero C A4 _ m6 pixt (w + 64) (h + 64) cdt datat cvt (Z_to_bv 64 datat) TT5 PW6 SN1 SN2) as TT6.
  pose proof (n1_tpx_eroN C A4 _ m6 pixdb (w + 64) (h + 64) cdd datad cvd (Z_to_bv 64 datat) TD5 PW6
                (fun q Hq E => n1_ap A2 _ _ FD4 LT2v _ _ Hq (n1_tbd pixt datat cdt cvt) E)) as TD6.
  pose proof (n1_up_rd _ m6 s (s - 56) pixsb UP6 ltac:(lia) ltac:(lia) ltac:(lia) S56_5) as S56_6.
  pose proof (n1_up_rd _ m6 s (s - 64) pixt UP6 ltac:(lia) ltac:(lia) ltac:(lia) S64_5) as S64_6.
  pose proof (n1_up_rd _ m6 s (s - 72) pixdb UP6 ltac:(lia) ltac:(lia) ltac:(lia) S72_5) as S72_6.
  pose proof RS6 as (_ & _ & _ & _ & _ & SUBr6 & _ & _ & _ & SA2_6 & _ & SC2_6).
  pose proof (FCL_of_RST C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A4 m6 RS6) as (_ & _ & C2_6 & _).
  destruct (@cs_G (mkFP fr1 cs1) al_rom sh r6 m6 s pixt pixdb sel2 ltac:(lia) ltac:(lia) B2 C2_6 ltac:(n1kp) ltac:(n1kp) ltac:(n1kp))
    as (r7 & RUN7 & Q1_7 & Q10_7 & Q11_7 & Q12_7 & AG7).
  n1pcfix RUN7. rzs HW6 RUN7.
  apply (ero_hop (mkFP fr1 cs1) C Ar A4 m6 (with_vmmaps vm4 md) r7 s pixdb pixt (w + 64)%Z (h + 64)%Z cdd datad cvd cdt datat cvt
           sel2 sv2 c2 (Z_to_bv 64 0xa4be8) S CK MB HW6 SUBr6 Hs16 Hlo Hhi ltac:(n1kp) Q1_7 ltac:(red; apply bv_eq; reflexivity)
           Q10_7 Q11_7 Q12_7 TD6 TT6 HDR64 ltac:(lia) ltac:(lia)
           (fun q H1 H2 => O23LeptCloseP.apart_fresh A2 _ _ FD4 LT2v q H2 H1)
           (O23LeptCloseP.fresh_sub Ar A2 _ SUBr2 FD4 _ (n1_tbd pixdb datad cdd cvd))
           SA2_6 SC2_6 X2 Y2
           (fun q Hq => conj (fun E => n1_ap A0 _ _ FT2 LS2_0 _ _ (n1_tbp pixt datat cdt cvt) Hq (eq_sym E))
                             (fun E => n1_ap A2 _ _ FD4 LS2_2 _ _ (n1_tbd pixdb datad cdd cvd) Hq (eq_sym E)))).
  intros m8 r8 HW8 CS8 V10_8 PW8 UP8 PM8.
  assert (ND2 : forall q, O23LeptCloseA.rblk pix1 datas cm cv sel1 sel2 sv1 sv2 q -> q <> Z_to_bv 64 datad)
    by (intros q Hq E; exact (n1_ap A2 _ _ FD4 LR2 _ _ (n1_tbd pixdb datad cdd cvd) Hq (eq_sym E))).
  pose proof (n1_rst_ero C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A4 m6 m8 (Z_to_bv 64 datad)
                CK ltac:(lia) Hhi RS6 ND2 PW8 UP8 PM8) as RS8.
  pose proof (n1_tpx_eroN C A4 m6 m8 pixsb (w + 64) (h + 64) cdb datab cvb (Z_to_bv 64 datad) TB6 PW8
                (fun q Hq E => n1_ap A2 _ _ FD4 LB2 _ _ (n1_tbd pixdb datad cdd cvd) Hq (eq_sym E))) as TB8.
  pose proof (n1_tpx_eroN C A4 m6 m8 pixt (w + 64) (h + 64) cdt datat cvt (Z_to_bv 64 datad) TT6 PW8
                (fun q Hq E => n1_ap A2 _ _ FD4 LT2v _ _ (n1_tbd pixdb datad cdd cvd) Hq (eq_sym E))) as TT8.
  destruct (tpx_self_ne C A4 m6 _ pixdb (w + 64) (h + 64) cdd datad cvd CK HW6 TD6 ltac:(lia) ltac:(lia)) as [SN3 SN4].
  pose proof (n1_tpx_ero C A4 m6 m8 pixdb (w + 64) (h + 64) cdd datad cvd (Z_to_bv 64 datad) TD6 PW8 SN3 SN4) as TD8.
  pose proof (n1_up_rd m6 m8 s (s - 56) pixsb UP8 ltac:(lia) ltac:(lia) ltac:(lia) S56_6) as S56_8.
  pose proof (n1_up_rd m6 m8 s (s - 64) pixt UP8 ltac:(lia) ltac:(lia) ltac:(lia) S64_6) as S64_8.
  pose proof (n1_up_rd m6 m8 s (s - 72) pixdb UP8 ltac:(lia) ltac:(lia) ltac:(lia) S72_6) as S72_8.
  pose proof RS8 as (_ & _ & _ & _ & _ & SUBr8 & PMr8 & P1_8 & SA1_8 & SA2_8 & _).
  assert (FR : forall q, O23LeptCloseA.tblk pixsb datab cdb cvb q \/ O23LeptCloseA.tblk pixt datat cdt cvt q \/
                         O23LeptCloseA.tblk pixdb datad cdd cvd q -> live A q = None).
  { intros q [Hq|[Hq|Hq]].
    - exact (TBF q Hq).
    - exact (O23LeptCloseP.fresh_sub A A0 _ SUB0 FT2 q Hq).
    - exact (O23LeptCloseP.fresh_sub A A2 _ (sub_live_trans A A0 A2 SUB0 SUB2) FD4 q Hq). }
  assert (TRB : forall q, O23LeptCloseA.tblk pixsb datab cdb cvb q \/ O23LeptCloseA.tblk pixt datat cdt cvt q \/
                          O23LeptCloseA.tblk pixdb datad cdd cvd q -> ~ O23LeptCloseA.rblk pix1 datas cm cv sel1 sel2 sv1 sv2 q).
  { intros q [Hq|[Hq|Hq]].
    - exact (TBR q Hq).
    - exact (O23LeptCloseP.apart_fresh A0 _ _ FT2 LR0 q Hq).
    - exact (O23LeptCloseP.apart_fresh A2 _ _ FD4 LR2 q Hq). }
  assert (LA4 : forall q, ~ (O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q \/ O23LeptCloseA.tblk pixsb datab cdb cvb q \/
                             O23LeptCloseA.tblk pixt datat cdt cvt q \/ O23LeptCloseA.tblk pixdb datad cdd cvd q) -> live A4 q = live A q).
  { intros q N.
    rewrite (LD4 q ltac:(intros H; apply N; tauto)), (LT2 q ltac:(intros H; apply N; tauto)).
    apply LA0. intros H; apply N; tauto. }
  replace (Z_to_bv 64 0xa4be8) with (0xa4be8 : word) by (apply bv_eq; reflexivity).
  exact (csc_tail sh fr C Ar A m md regs s pix1 w h cm datas cv ret S kR bR fr1 cs1 A4 m8 vm4 r8
           (kx - RK_pixcopy - RK_pixcopy)%Z
           (bx - (RB_pixT (4 * (wpl_of (w + 64) 1 * (h + 64))) + RB_cmapT cdb) - (RB_pixT (4 * (wpl_of (w + 64) 1 * (h + 64))) + RB_cmapT cdt))%Z
           sel1 sel2 sv1 sv2 pixsb cdb datab cvb pixt cdt datat cvt pixdb cdd datad cvd
           PCG CK Hs16 Hlo Hhi Hret H2 H4 SUBA HPD HDR Hw Hh HDR64 FZ FK HW8
           ltac:(n1kp) ltac:(n1kp) ltac:(n1kp) ltac:(n1kp) ltac:(n1rkgo regs)
           (FCL_of_RST C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A4 m8 RS8)
           S56_8 S64_8 S72_8 SUBr8 PMr8 P1_8 SA1_8 SA2_8 SS DJ P1L TB8 TT8 TD8 FR
           (fun q H1 H2 => O23LeptCloseP.apart_fresh A0 _ _ FT2 LB0 q H2 H1)
           (fun q H1 H2 => O23LeptCloseP.apart_fresh A2 _ _ FD4 LB2 q H2 H1)
           (fun q H1 H2 => O23LeptCloseP.apart_fresh A2 _ _ FD4 LT2v q H2 H1)
           TRB (fun E => CM4 (CM2 (CMB E)))
           (O23LeptCloseA.cmeq_chain cdt cvt cdd cvd cv CM4 (O23LeptCloseA.cmeq_chain cdb cvb cdt cvt cv CM2 CMEQ CE2) CE4)
           LA4 ROOM4 ltac:(lia) ltac:(lia) Hk0 Hb0 HK).
Qed.

End CloseN1.
