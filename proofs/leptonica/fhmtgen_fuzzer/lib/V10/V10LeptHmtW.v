(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib LeptSel.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptStderr V10LeptBase V10LeptUb.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL7a.
Import V10CL7a.V10LeptErr. Import V10CL7a.V10LeptSel_iface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL8a.
Import V10CL8a.V10LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptPixCreate V10LeptCmapValid V10LeptCmap2 V10LeptPixCopyA V10LeptPixCopy.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL9a.
Import V10CL9a.V10LeptPixDestroy.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptPixT V10LeptPixCopyT V10LeptGrayA V10LeptGrayBorder V10LeptFhmt V10LeptFhmtW.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoom10.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section HmtW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pblk (pix data cd ad : Z) (q : word) : Prop :=
  q = Z_to_bv 64 pix \/ q = Z_to_bv 64 data \/ (cd <> 0%Z /\ (q = Z_to_bv 64 cd \/ q = Z_to_bv 64 ad)).

Definition cmf (kd kna kn : Z) : Prop := (kd = 1 \/ kd = 2 \/ kd = 4 \/ kd = 8)%Z /\ kna = (2 ^ kd)%Z /\ (1 <= kn <= kna)%Z.

Definition pown (C : lctx) (X Ak : AS) (mk : word -> option byte) (pix w h d cd data ad kd kna kn : Z) : Prop :=
  (4096 <= pix)%Z /\ (pix + 64 <= alloc_top (c_vm C))%Z /\ (pix mod 16 = 0)%Z /\
  (4096 <= data)%Z /\ (data + 4 * (wpl_of w d * h) <= alloc_top (c_vm C))%Z /\ (data mod 16 = 0)%Z /\ pix <> data /\
  (0 < 4 * (wpl_of w d * h))%Z /\ PIXat mk pix (hdv w h d cd data) /\
  live Ak (Z_to_bv 64 pix) = Some 64%Z /\ live Ak (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z /\
  (forall q, pblk pix data cd ad q -> live X q = None /\ live (c_A0 C) q = None) /\
  (cd = 0%Z \/ (cmf kd kna kn /\ (4096 <= cd)%Z /\ (cd + 32 <= alloc_top (c_vm C))%Z /\ (4096 <= ad)%Z /\ (ad + 4 * kna <= alloc_top (c_vm C))%Z /\
       cd <> ad /\ cd <> pix /\ cd <> data /\ ad <> pix /\ ad <> data /\
       live Ak (Z_to_bv 64 cd) = Some 24%Z /\ live Ak (Z_to_bv 64 ad) = Some (4 * kna)%Z /\
       CMAPat mk cd (CMAPV ad kd kna kn 0))).

Lemma pblk_dec : forall pix data cd ad q, pblk pix data cd ad q \/ ~ pblk pix data cd ad q.
Proof.
  intros pix data cd ad q. unfold pblk.
  destruct (bv_eq_dec _ q (Z_to_bv 64 pix)) as [E1|N1]; [left; left; exact E1|].
  destruct (bv_eq_dec _ q (Z_to_bv 64 data)) as [E2|N2]; [left; right; left; exact E2|].
  destruct (Z.eq_dec cd 0) as [E0|N0]; [right; intros [X|[X|[X _]]]; contradiction|].
  destruct (bv_eq_dec _ q (Z_to_bv 64 cd)) as [E3|N3]; [left; right; right; split; [exact N0 | left; exact E3]|].
  destruct (bv_eq_dec _ q (Z_to_bv 64 ad)) as [E4|N4]; [left; right; right; split; [exact N0 | right; exact E4]|].
  right. intros [X|[X|[_ [X|X]]]]; contradiction.
Qed.

Lemma pixt_new_pown : forall C A A' m' pix w h d cd data cv, pixt_new C A A' m' pix w h d cd data cv -> (0 < 4 * (wpl_of w d * h))%Z ->
  exists ad, pown C A A' m' pix w h d cd data ad (c_d cv) (c_nalloc cv) (c_n cv) /\ (forall q, ~ pblk pix data cd ad q -> live A' q = live A q).
Proof.
  intros C A A' m' pix w h d cd data cv (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & PXd & CMR) Rpos.
  destruct CMR as [[CD0 LEQ] | (ad & CMOKc & Gcd & TOPcd & Gad & TOPad & NEcdad & NEcdp & NEcdd & NEadp & NEadd & LAcd & LAad & L00cd & L00ad & L2cd & L2ad & CM4 & LEQ)].
  - exists 0%Z. split.
    + unfold pown. do 11 (split; [assumption|]). split; [| left; exact CD0].
      intros q [-> | [-> | [NZ _]]]; [split; assumption | split; assumption | contradiction].
    + intros q NB. apply LEQ; intros ->; apply NB; unfold pblk; auto.
  - exists ad. split.
    + unfold pown. do 11 (split; [assumption|]). split.
      * intros q [-> | [-> | [_ [-> | ->]]]]; split; assumption.
      * right. destruct CMOKc as (D & NA & N & _). split; [split; [exact D | split; [exact NA | exact N]]|]. do 11 (split; [assumption|]). exact CM4.
    + intros q NB. apply LEQ; intros ->; apply NB; unfold pblk; auto; right; right; (split; [lia | auto]).
Qed.

Lemma pown_keep : forall C X Ak Ak' Ax mk mk' pix w h d cd data ad kd kna kn,
  pown C X Ak mk pix w h d cd data ad kd kna kn ->
  (forall q, pblk pix data cd ad q -> live Ak' q = live Ak q) -> (forall q, pblk pix data cd ad q -> live Ax q = live Ak q) -> LIVK Ax mk mk' ->
  pown C X Ak' mk' pix w h d cd data ad kd kna kn.
Proof.
  intros C X Ak Ak' Ax mk mk' pix w h d cd data ad kd kna kn (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & Rpos & PX & Lp & Ld & FR & CMR) EQ EQx LK.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  unfold pown. do 8 (split; [assumption|]).
  assert (Lpx : live Ax (Z_to_bv 64 pix) = Some 64%Z) by (rewrite EQx by (left; reflexivity); exact Lp).
  split; [apply (PIXat_frame mk); [exact PX | intros x Hx; exact (LIVK_at Ax mk mk' pix 64 x LK Lpx ltac:(lia) ltac:(lia) Hx)]|].
  split; [rewrite EQ by (left; reflexivity); exact Lp|]. split; [rewrite EQ by (right; left; reflexivity); exact Ld|]. split; [exact FR|].
  destruct CMR as [CD0 | (CF & Gcd & TOPcd & Gad & TOPad & N1 & N2 & N3 & N4 & N5 & Lcd & Lad & CM)]; [left; exact CD0 | right].
  assert (Lcdx : live Ax (Z_to_bv 64 cd) = Some 24%Z) by (rewrite EQx by (right; right; split; [lia | left; reflexivity]); exact Lcd).
  do 10 (split; [assumption|]). split; [rewrite EQ by (right; right; split; [lia | left; reflexivity]); exact Lcd|].
  split; [rewrite EQ by (right; right; split; [lia | right; reflexivity]); exact Lad|].
  apply (CMAPat_frame mk); [exact CM | intros x Hx; exact (LIVK_at Ax mk mk' cd 24 x LK Lcdx ltac:(lia) ltac:(lia) Hx)].
Qed.

Lemma pown_sub : forall C X X' Ak mk pix w h d cd data ad kd kna kn,
  pown C X Ak mk pix w h d cd data ad kd kna kn -> sub_live X' X -> pown C X' Ak mk pix w h d cd data ad kd kna kn.
Proof.
  intros C X X' Ak mk pix w h d cd data ad kd kna kn (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & Rpos & PX & Lp & Ld & FR & CMR) SUB.
  unfold pown. do 11 (split; [assumption|]). split; [| exact CMR].
  intros q B. destruct (FR q B) as [F1 F2]. split; [| exact F2].
  destruct (live X' q) as [k|] eqn:E; [apply SUB in E; congruence | reflexivity].
Qed.

Lemma pown_live : forall C X Ak mk pix w h d cd data ad kd kna kn,
  pown C X Ak mk pix w h d cd data ad kd kna kn -> forall q, pblk pix data cd ad q -> exists k, live Ak q = Some k.
Proof.
  intros C X Ak mk pix w h d cd data ad kd kna kn (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & Rpos & PX & Lp & Ld & FR & CMR) q B.
  destruct B as [-> | [-> | [NZ B]]]; [eexists; exact Lp | eexists; exact Ld |].
  destruct CMR as [CD0 | (CF & Gcd & TOPcd & Gad & TOPad & N1 & N2 & N3 & N4 & N5 & Lcd & Lad & CM)]; [contradiction|].
  destruct B as [-> | ->]; eexists; eassumption.
Qed.

(* [comment removed for export] *)
Lemma pown_disj : forall C X1 Ak1 mk1 p1 w1 h1 d1 cd1 data1 ad1 kd1 kna1 kn1 X2 Ak2 mk2 p2 w2 h2 d2 cd2 data2 ad2 kd2 kna2 kn2,
  pown C X1 Ak1 mk1 p1 w1 h1 d1 cd1 data1 ad1 kd1 kna1 kn1 -> pown C X2 Ak2 mk2 p2 w2 h2 d2 cd2 data2 ad2 kd2 kna2 kn2 -> sub_live Ak1 X2 ->
  forall q, pblk p1 data1 cd1 ad1 q -> ~ pblk p2 data2 cd2 ad2 q.
Proof.
  intros C X1 Ak1 mk1 p1 w1 h1 d1 cd1 data1 ad1 kd1 kna1 kn1 X2 Ak2 mk2 p2 w2 h2 d2 cd2 data2 ad2 kd2 kna2 kn2 O1 O2 SUB q B1 B2.
  destruct (pown_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ O1 q B1) as [k Lk]. apply SUB in Lk.
  destruct O2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _). destruct (FR q B2) as [F _]. congruence.
Qed.

Lemma pown_cm_facts : forall C X Ak mk pix w h d cd data ad kd kna kn,
  pown C X Ak mk pix w h d cd data ad kd kna kn -> cm_facts Ak mk cd (CMAPV ad kd kna kn 0).
Proof.
  intros C X Ak mk pix w h d cd data ad kd kna kn (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & Rpos & PX & Lp & Ld & FR & CMR).
  destruct CMR as [CD0 | ((D & NA & N) & Gcd & TOPcd & Gad & TOPad & N1 & N2 & N3 & N4 & N5 & Lcd & Lad & CM)]; [left; exact CD0 | right].
  split; [exact CM|]. split; [unfold cmap_ok; cbn [c_d c_nalloc c_n c_arr]; repeat split; try assumption; lia|].
  split; [exact Lcd | exact Lad].
Qed.

(* [comment removed for export] *)
Definition oown (C : lctx) (X Ak : AS) (mk : word -> option byte) (pix w h d cd data ad kd kna kn : Z) : Prop :=
  pix = 0%Z \/ pown C X Ak mk pix w h d cd data ad kd kna kn.
Definition oblk (pix data cd ad : Z) (q : word) : Prop := pix <> 0%Z /\ pblk pix data cd ad q.

Lemma oblk_dec : forall pix data cd ad q, oblk pix data cd ad q \/ ~ oblk pix data cd ad q.
Proof.
  intros pix data cd ad q. unfold oblk. destruct (Z.eq_dec pix 0) as [E|N]; [right; intros [X _]; contradiction|].
  destruct (pblk_dec pix data cd ad q) as [B|NB]; [left; split; assumption | right; intros [_ X]; contradiction].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sp_slot_al8 : forall sp k, (sp mod 16 = 0)%Z -> (k mod 8 = 0)%Z -> ((sp - k) mod 8 = 0)%Z.
Proof.
  intros sp k H1 H2. apply Zmod_divides in H1 as [c ->]; [|lia]. apply Zmod_divides in H2 as [e ->]; [|lia].
  replace (16 * c - 8 * e)%Z with ((2 * c - e) * 8)%Z by ring. apply Z_mod_mult.
Qed.

Lemma pixDestroy_null_W : forall C A m md regs (s pp : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (c_top C - LSTK + 32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> (pp mod 8 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> (forall x : word, ~ (s - 32 <= u x < s)%Z -> m' x = m x) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x1615c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp ret S CK HW H2 Hlo Hpp Hpphi ALpp H1 Hret H10 Rpp HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  destruct (pixDestroy_null al_rom regs m s pp ret ltac:(lia) Hpp ltac:(lia) ALpp Hret (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes (wbytes m _ _) _ _) _ _).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  apply (HK M1 r1 HW1).
  - apply cs_kept_intro; csr; try reflexivity.
  - exact PM1.
  - intros x Hx. subst M1. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity.
Qed.

Lemma raster_pos : forall w h d, hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z -> (0 < 4 * (wpl_of w d * h))%Z.
Proof.
  intros w h d (DV & Hw2 & Hh2 & Hsz) Hw Hh. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwr.
  assert (1 * 1 <= wpl_of w d * h)%Z by (apply Z.mul_le_mono_nonneg; lia). lia.
Qed.

Lemma pixDestroy_opt_W : forall C X A m md regs (s pp pix w h d cd data ad kd kna kn : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 -> (pp mod 8 = 0)%Z ->
  getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
  oown C X A m pix w h d cd data ad kd kna kn ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     (forall q, oblk pix data cd ad q -> live A' q = None) -> (forall q, ~ oblk pix data cd ad q -> live A' q = live A q) ->
     POSTM C A' (pp + 8) m m' -> (forall a : word, (s <= u a < pp)%Z -> m' a = m a) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x1615c : word) m al_rom) md) S.
Proof.
  intros C X A m md regs s pp pix w h d cd data ad kd kna kn ret S CK HW H2 Hs16 Hlo Hpp Hpphi H1 Hret H4 ALpp H10 Rpp OO HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ALLOC_STACK in *.
  destruct OO as [P0 | OWN].
  - subst pix.
    apply (pixDestroy_null_W C A m md regs s pp ret S CK HW H2 ltac:(lia) Hpp Hpphi ALpp H1 Hret H10 Rpp).
    intros m' r' HW' CS' PM' OUT'. rewrite <- (with_vmmaps_same md). apply (HK A m' (m_vmmaps md) r').
    + rewrite with_vmmaps_same. exact HW'.
    + exact CS'.
    + intros q [NZ0 _]. contradiction.
    + intros q _. reflexivity.
    + eapply POSTM_mono; [|exact PM']. lia.
    + intros a Ha. apply OUT'. lia.
    + apply roomtr_refl; lia.
  - pose proof OWN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & Rpos & PX & Lp & Ld & FR & CMR).
    destruct (FR _ (or_introl eq_refl)) as [_ L0p]. destruct (FR _ (or_intror (or_introl eq_refl))) as [_ L0d].
    assert (HCM : cd = 0%Z \/ (CMAPat m cd (CMAPV ad kd kna kn 0) /\ live A (Z_to_bv 64 cd) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr (CMAPV ad kd kna kn 0))) = Some (4 * kna)%Z /\
                live (c_A0 C) (Z_to_bv 64 cd) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr (CMAPV ad kd kna kn 0))) = None /\
                cd <> c_arr (CMAPV ad kd kna kn 0) /\ cd <> pix /\ c_arr (CMAPV ad kd kna kn 0) <> pix /\ p_data (hdv w h d cd data) <> cd /\
                p_data (hdv w h d cd data) <> c_arr (CMAPV ad kd kna kn 0) /\ (0 < 4 * kna)%Z)).
    { destruct CMR as [CD0 | ((D & NA & N) & Gcd & TOPcd & Gad & TOPad & N1 & N2 & N3 & N4 & N5 & Lcd & Lad & CM)]; [left; exact CD0 | right].
      assert (NZ : cd <> 0%Z) by lia.
      destruct (FR (Z_to_bv 64 cd) (or_intror (or_intror (conj NZ (or_introl eq_refl))))) as [_ L0cd].
      destruct (FR (Z_to_bv 64 ad) (or_intror (or_intror (conj NZ (or_intror eq_refl))))) as [_ L0ad].
      cbn [c_arr p_data hdv]. repeat (split; [first [assumption | congruence | lia]|]).
      assert (0 < 2 ^ kd)%Z by (apply Z.pow_pos_nonneg; lia). lia. }
    apply (pixDestroy_keep_W C A m md regs s pp pix cd (4 * kna) (4 * (wpl_of w d * h)) (hdv w h d cd data) (CMAPV ad kd kna kn 0) ret S CK HW H2 Hs16
             ltac:(unfold ALLOC_STACK; lia) Hpp Hpphi H1 Hret H4 ALpp H10 Rpp PX eq_refl eq_refl eq_refl Lp L0p Ld L0d Rpos ltac:(cbn [p_data hdv]; congruence) HCM).
    intros A' m' vm' r' HW' CS' (P1 & P2 & P3 & P4) PM' R0' OUT' RT'. cbn [p_data hdv c_arr] in P2, P3, P4.
    apply (HK A' m' vm' r' HW' CS').
    + intros q [_ [-> | [-> | [NZ [-> | ->]]]]]; [exact P1 | apply P2; lia | exact (proj1 (P3 NZ)) | exact (proj2 (P3 NZ))].
    + intros q NB. apply P4.
      * intros ->. apply NB. split; [lia | left; reflexivity].
      * intros _ ->. apply NB. split; [lia | right; left; reflexivity].
      * intros NZ. split; intros ->; apply NB; (split; [lia|]); right; right; (split; [exact NZ|]); [left | right]; reflexivity.
    + exact PM'.
    + exact OUT'.
    + exact RT'.
Qed.

Lemma oown_range : forall C X Ak mk pix w h d cd data ad kd kna kn, oown C X Ak mk pix w h d cd data ad kd kna kn -> (0 <= pix < 2 ^ 64)%Z.
Proof.
  intros C X Ak mk pix w h d cd data ad kd kna kn [-> | (Gp & TOPp & _)]; [lia|].
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL. lia.
Qed.

Lemma oown_keep : forall C X Ak Ak' Ax mk mk' pix w h d cd data ad kd kna kn,
  oown C X Ak mk pix w h d cd data ad kd kna kn ->
  (forall q, oblk pix data cd ad q -> live Ak' q = live Ak q) -> (forall q, oblk pix data cd ad q -> live Ax q = live Ak q) -> LIVK Ax mk mk' ->
  oown C X Ak' mk' pix w h d cd data ad kd kna kn.
Proof.
  intros C X Ak Ak' Ax mk mk' pix w h d cd data ad kd kna kn [P0 | OWN] EQ EQx LK; [left; exact P0 | right].
  assert (NZ : pix <> 0%Z) by (destruct OWN as (Gp & _); lia).
  apply (pown_keep C X Ak Ak' Ax mk mk'); [exact OWN | intros q B; apply EQ; split; assumption | intros q B; apply EQx; split; assumption | exact LK].
Qed.

(* [comment removed for export] *)
Lemma oblk_fresh : forall C X Ak mk pix w h d cd data ad kd kna kn, oown C X Ak mk pix w h d cd data ad kd kna kn ->
  forall q, oblk pix data cd ad q -> live X q = None.
Proof.
  intros C X Ak mk pix w h d cd data ad kd kna kn [P0 | OWN] q [NZ B]; [contradiction|].
  destruct OWN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _). exact (proj1 (FR q B)).
Qed.

Lemma oown_sub_live : forall C X Ak mk pix w h d cd data ad kd kna kn, oown C X Ak mk pix w h d cd data ad kd kna kn ->
  (forall q, ~ oblk pix data cd ad q -> live Ak q = live X q) -> sub_live X Ak.
Proof.
  intros C X Ak mk pix w h d cd data ad kd kna kn OO LEQ q k Lq.
  destruct (oblk_dec pix data cd ad q) as [B|NB]; [rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OO q B) in Lq; discriminate | rewrite (LEQ q NB); exact Lq].
Qed.

Lemma oown_sub : forall C X X' Ak mk pix w h d cd data ad kd kna kn,
  oown C X Ak mk pix w h d cd data ad kd kna kn -> sub_live X' X -> oown C X' Ak mk pix w h d cd data ad kd kna kn.
Proof. intros C X X' Ak mk pix w h d cd data ad kd kna kn [P0 | OWN] SUB; [left; exact P0 | right; exact (pown_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWN SUB)]. Qed.

(* [comment removed for export] *)
Lemma oown_disj : forall C X1 Ak1 mk1 p1 w1 h1 d1 cd1 data1 ad1 kd1 kna1 kn1 X2 Ak2 mk2 p2 w2 h2 d2 cd2 data2 ad2 kd2 kna2 kn2,
  oown C X1 Ak1 mk1 p1 w1 h1 d1 cd1 data1 ad1 kd1 kna1 kn1 -> oown C X2 Ak2 mk2 p2 w2 h2 d2 cd2 data2 ad2 kd2 kna2 kn2 -> sub_live Ak1 X2 ->
  forall q, oblk p1 data1 cd1 ad1 q -> ~ oblk p2 data2 cd2 ad2 q.
Proof.
  intros C X1 Ak1 mk1 p1 w1 h1 d1 cd1 data1 ad1 kd1 kna1 kn1 X2 Ak2 mk2 p2 w2 h2 d2 cd2 data2 ad2 kd2 kna2 kn2 O1 O2 SUB q [NZ1 B1] B2.
  destruct O1 as [P0 | OWN1]; [contradiction|].
  destruct (pown_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWN1 q B1) as [k Lk]. apply SUB in Lk.
  rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ O2 q B2) in Lk. discriminate.
Qed.

(* [comment removed for export] *)
Lemma res_oown : forall C A2 A3 m4 (r5 : bvmap 5 word) w' h' cv',
  (0 < 4 * (wpl_of w' 1 * h'))%Z ->
  ( (getr r5 10 = Z_to_bv 64 0 /\ forall q, live A3 q = live A2 q)
    \/ (exists pixd cd data, getr r5 10 = Z_to_bv 64 pixd /\ pixt_new C A2 A3 m4 pixd w' h' 1 cd data cv') ) ->
  exists p3 cd3 data3 ad3, getr r5 10 = Z_to_bv 64 p3 /\ oown C A2 A3 m4 p3 w' h' 1 cd3 data3 ad3 (c_d cv') (c_nalloc cv') (c_n cv') /\
     (forall q, ~ oblk p3 data3 cd3 ad3 q -> live A3 q = live A2 q).
Proof.
  intros C A2 A3 m4 r5 w' h' cv' Rpos [[R10 LEQ] | (pixd & cd & data & R10 & PT)].
  - exists 0%Z, 0%Z, 0%Z, 0%Z. split; [exact R10|]. split; [left; reflexivity|]. intros q _. apply LEQ.
  - destruct (pixt_new_pown _ _ _ _ _ _ _ _ _ _ _ PT Rpos) as (ad & OWN & LEQ).
    exists pixd, cd, data, ad. split; [exact R10|]. split; [right; exact OWN|].
    intros q NB. apply LEQ. intros B. apply NB. split; [destruct OWN as (Gp & _); lia | exact B].
Qed.

Lemma rast_nn : forall w h, (0 <= w)%Z -> (0 <= h)%Z -> (0 <= rast w h 1)%Z.
Proof. intros w h Hw Hh. unfold rast, wpl_of. assert (0 <= (w * 1 + 31) / 32)%Z by (apply Z.div_pos; lia). nia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition HMT_STACK : Z := 64 + FHG_STACK.        (* [comment removed for export] *)
Abbreviation DRh := ([3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv : list (bv 5)).

Lemma cells_FRD : forall m s ret regs, (64 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (FRD m s ret regs) (frameD s ret regs).
Proof. intros m s ret regs Hs Hs64. unfold frameD, FRD. cbn [cellsZ]. repeat split; rdn_solve. Qed.
Lemma frameD_bounds : forall s ret r0, (64 <= s)%Z -> (s < 2 ^ 64)%Z -> Forall (fun av => s - 32 <= fst av /\ fst av + 8 <= s)%Z (frameD s ret r0).
Proof. intros s ret r0 Hs Hs64. unfold frameD. repeat (apply Forall_cons; [cbn [fst snd]; lia |]). apply Forall_nil. Qed.
Lemma FRD_out : forall m s ret regs (x : word), (64 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 32 <= u x < s)%Z -> FRD m s ret regs x = m x.
Proof.
  intros m s ret regs x Hs Hs64 Hx. unfold FRD.
  repeat (rewrite (wbytes_out_Z _ _ 8); [| rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]). reflexivity.
Qed.
Lemma cellsD_frm : forall C s' m m' s ret r0, Cok C -> FRM C s' m m' -> (c_top C - LSTK <= s')%Z -> (s' <= s - 32)%Z -> (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cellsZ m (frameD s ret r0) -> cellsZ m' (frameD s ret r0).
Proof.
  intros C s' m m' s ret r0 CK F H1 H2 Hs Hs64 CE. apply (cellsZ_frm C s' m m' _ CK F H1); [|exact CE].
  eapply Forall_impl; [|exact (frameD_bounds s ret r0 Hs Hs64)]. intros [a v] [X Y]; cbn [fst snd] in *. lia.
Qed.
Lemma cellsD_out : forall m m' (lo hi : Z) s ret r0, (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) -> (hi <= s - 32 \/ s <= lo)%Z -> (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cellsZ m (frameD s ret r0) -> cellsZ m' (frameD s ret r0).
Proof.
  intros m m' lo hi s ret r0 OUT Hd Hs Hs64 CE. apply (cellsZ_out m m' lo hi _ OUT); [|exact CE].
  eapply Forall_impl; [|exact (frameD_bounds s ret r0 Hs Hs64)]. intros [a v] [X Y]; cbn [fst snd] in *. lia.
Qed.
Lemma cell_frm : forall C s' m m' (a : Z) bs, Cok C -> FRM C s' m m' -> (c_top C - LSTK <= s')%Z -> (s' <= a)%Z -> (a + 8 <= 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 a) 8 = Some bs -> rdn SEGS m' (Z_to_bv 64 a) 8 = Some bs.
Proof. intros C s' m m' a bs CK F Hlo Ha Ha64 R. rewrite (FRM_rdn16 C s' m m' _ 8 CK F) by (cbn; lia). exact R. Qed.
Lemma cell_out : forall m m' (a : Z) bs, (forall x : word, (a <= u x < a + 8)%Z -> m' x = m x) -> (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 a) 8 = Some bs -> rdn SEGS m' (Z_to_bv 64 a) 8 = Some bs.
Proof.
  intros m m' a bs OUT Ha Ha64 R.
  etransitivity; [apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia | intros x Hx; apply OUT; rewrite u_Z2bv in Hx by lia; cbn in Hx; lia] | exact R].
Qed.
Lemma cell_wr : forall m (a z : Z), (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z -> (0 <= z < 2 ^ 64)%Z ->
  rdn SEGS (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 z))) (Z_to_bv 64 a) 8 = Some (Z_to_le_bytes 8 z).
Proof. intros m a z Ha Ha64 Hz. rewrite <- (w2b_Z 8 z) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. Qed.

Lemma str_pixHMTDwa_1 : str16 0x10728 11. Proof. str16_tac. Qed.
Lemma str_pixRemoveBorder : str16 0x10ced 15. Proof. str16_tac. Qed.
Lemma str_msg_1bpp : str16 0x11035 18. Proof. str16_tac. Qed.
Lemma str_msg_pixs_undef2 : str16 0x10298 16. Proof. str16_tac. Qed.

(* [comment removed for export] *)
Definition hmt_res (C : lctx) (A A' : AS) (m' : word -> option byte) (regs' : bvmap 5 word) (w h kd kna kn : Z) : Prop :=
  (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
  \/ (exists pixd cd data ad, getr regs' 10 = Z_to_bv 64 pixd /\ pown C A A' m' pixd w h 1 cd data ad kd kna kn /\
                              (forall q, ~ pblk pixd data cd ad q -> live A' q = live A q)).

Definition pixHMTDwa_1_contract : Prop :=
  forall C A m md regs (s pixs w h cm datas name j : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + HMT_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 pixs -> getr regs 12 = Z_to_bv 64 name ->
  PIXat m pixs (hdv w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z -> cm_facts A m cm cv ->
  (0 <= j < 10)%Z -> selname_at (alloc_top (c_vm C)) A m name (hm_name j) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK10_hmt 1 <= kR)%Z -> (RB10_hmt 1 w h <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     hmt_res C A A' m' regs' w h (c_d cv) (c_nalloc cv) (c_n cv) ->
     aroom A' vm' (kR - RK10_hmt 1) (bR - RB10_hmt 1 w h) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixHMTDwa_1) m al_rom) md) S.

(* [comment removed for export] *)
Definition pixHMTDwa_1_d_contract : Prop :=
  forall C A m md regs (s pixs name : Z) (vs : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + HMT_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 pixs -> getr regs 12 = Z_to_bv 64 name ->
  PIXat m pixs vs -> live A (Z_to_bv 64 pixs) = Some 64%Z -> (0 <= p_d vs < 2 ^ 32)%Z -> p_d vs <> 1%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixHMTDwa_1) m al_rom) md) S.

(* [comment removed for export] *)
Definition pixHMTDwa_1_null_contract : Prop :=
  forall C A m md regs (s name : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + HMT_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 name ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixHMTDwa_1) m al_rom) md) S.

Theorem pixHMTDwa_1_null_W : pixHMTDwa_1_null_contract.
Proof.
  unfold pixHMTDwa_1_null_contract.
  intros C A m md regs s name ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 HK.
  replace (Z_to_bv 64 PC_pixHMTDwa_1) with (0x282bc : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold HMT_STACK, FHG_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct (hd_N1 al_rom regs m s 0 ret ltac:(lia) ltac:(lia) (W_sok_win C A m md (s - 64) 64 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11) as (r1 & RUN1 & Q2 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. clear RUN1.
  assert (WP1 : W C A (FRD m s ret regs) md /\ POSTM C A s m (FRD m s ret regs)) by (unfold FRD; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FRD m s ret regs) in *.
  destruct (hd_N2 al_rom r1 regs M1 s 0 ret ltac:(lia) ltac:(lia) (W_sev_got C A M1 _ HW1) (W_sev C A M1 _ HW1) (cells_FRD m s ret regs ltac:(lia) ltac:(lia)) Q2 Q8)
    as (r2 & RUN2 & V2 & V1 & V10 & V11 & V12 & VR & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |]. clear RUN2.
  apply (returnErrorPtr_W C A M1 md r2 s 0x10298 0x10728 16 11 ret (Z_to_bv 64 0) S CK HW1 V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
           V10 V11 V12 str_msg_pixs_undef2 str_pixHMTDwa_1).
  intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
  apply (HK m4 r5 HW4).
  - apply cs_kept_intro; csr; first [reflexivity | solve [apply VR; in_lit] | (rewrite H2; reflexivity)].
  - eapply POSTM_trans; [exact PM1|]. eapply (POSTM_range C A M1 _ m4); [exact CK | exact HW1 | exact OUT4 | lia | lia | lia].
  - exact A10.
Qed.

Theorem pixHMTDwa_1_d_W : pixHMTDwa_1_d_contract.
Proof.
  unfold pixHMTDwa_1_d_contract.
  intros C A m md regs s pixs name vs ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 PXs Lps Hd Hd1 HK.
  replace (Z_to_bv 64 PC_pixHMTDwa_1) with (0x282bc : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold HMT_STACK, FHG_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by (destruct PXs as (? & ? & _); lia).
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALp16 & _). rewrite u_Z2bv in ALp16 by (destruct PXs as (? & ? & _); lia). pose proof (al16_mod8 _ ALp16) as AL8s.
  destruct (hd_A0 al_rom regs m s 0 pixs name vs ret ltac:(lia) ltac:(lia) ltac:(lia) AL8s PXs ltac:(lia)
              (W_sok_win C A m md (s - 64) 64 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12) as (r1 & RUN1 & Q2 & Q10 & Q8 & Q18 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. clear RUN1.
  assert (WP1 : W C A (FRD m s ret regs) md /\ POSTM C A s m (FRD m s ret regs)) by (unfold FRD; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FRD m s ret regs) in *.
  destruct (hd_AD al_rom r1 regs M1 s (p_d vs) 0 ret ltac:(lia) ltac:(lia) Hd Hd1 (W_sev_got C A M1 _ HW1) (W_sev C A M1 _ HW1)
              (cells_FRD m s ret regs ltac:(lia) ltac:(lia)) Q2 Q10 Q8)
    as (r2 & RUN2 & V2 & V1 & V10 & V11 & V12 & VR & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |]. clear RUN2.
  apply (returnErrorPtr_W C A M1 md r2 s 0x11035 0x10728 18 11 ret (Z_to_bv 64 0) S CK HW1 V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
           V10 V11 V12 str_msg_1bpp str_pixHMTDwa_1).
  intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
  apply (HK m4 r5 HW4).
  - apply cs_kept_intro; csr; first [reflexivity | solve [apply VR; in_lit] | (rewrite H2; reflexivity)].
  - eapply POSTM_trans; [exact PM1|]. eapply (POSTM_range C A M1 _ m4); [exact CK | exact HW1 | exact OUT4 | lia | lia | lia].
  - exact A10.
Qed.

(* [comment removed for export] *)
Section Body.
Hypothesis ABG : pixAddBorderGeneral_contract.
Hypothesis RBG : pixRemoveBorderGeneral_contract.
Hypothesis GEN : pixFHMTGen_1_contract.
Hypothesis GENN : pixFHMTGen_1_null_contract.

Variables (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s w h kd kna kn name j : Z) (ret : word) (S : TSet) (kR bR : Z).
Hypothesis CK : Cok C.
Hypothesis Hs16 : (s mod 16 = 0)%Z.
Hypothesis Hlo : (c_top C - LSTK + HMT_STACK <= s)%Z.
Hypothesis Hhi : (s <= c_top C)%Z.
Hypothesis Hret : ret_ok ret.
Hypothesis H2 : getr regs 2 = Z_to_bv 64 s.
Hypothesis H4 : getr regs 4 = Z_to_bv 64 0x45480.
Hypothesis HOK : hdr_ok w h 1.
Hypothesis Hw : (1 <= w)%Z.
Hypothesis Hh : (1 <= h)%Z.
Hypothesis Hj : (0 <= j < 10)%Z.
Hypothesis HNM : selname_at (alloc_top (c_vm C)) A m name (hm_name j).
Hypothesis Hrk : (RK10_hmt 1 <= kR)%Z.
Hypothesis Hrb : (RB10_hmt 1 w h <= bR)%Z.
Hypothesis HKF : forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     hmt_res C A A' m' regs' w h kd kna kn -> aroom A' vm' (kR - RK10_hmt 1) (bR - RB10_hmt 1 w h) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S.

Lemma RB10_hmt_pos : (0 <= RB10_hmt 1 w h)%Z.
Proof. destruct HOK as (_ & Hw2 & Hh2 & _). exact (proj1 (RB10_hmt_le 1 w h ltac:(lia) ltac:(lia))). Qed.

(* [comment removed for export] *)
Lemma hd_tail : forall A3 m3 vm3 r3 (p1 cd1 data1 ad1 p2 cd2 data2 ad2 p3 cd3 data3 ad3 k3 b3 : Z),
  W C A3 m3 (with_vmmaps vm3 md) -> POSTM C A s m m3 ->
  cellsZ m3 (frameD s ret regs) ->
  rdn SEGS m3 (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 p1) -> rdn SEGS m3 (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 p2) ->
  oown C A A3 m3 p1 (w + 64) (h + 64) 1 cd1 data1 ad1 kd kna kn -> oown C A A3 m3 p2 (w + 64) (h + 64) 1 cd2 data2 ad2 kd kna kn ->
  oown C A A3 m3 p3 w h 1 cd3 data3 ad3 kd kna kn ->
  (forall q, oblk p1 data1 cd1 ad1 q -> ~ oblk p2 data2 cd2 ad2 q) -> (forall q, oblk p1 data1 cd1 ad1 q -> ~ oblk p3 data3 cd3 ad3 q) ->
  (forall q, oblk p2 data2 cd2 ad2 q -> ~ oblk p3 data3 cd3 ad3 q) ->
  (forall q, ~ oblk p1 data1 cd1 ad1 q -> ~ oblk p2 data2 cd2 ad2 q -> ~ oblk p3 data3 cd3 ad3 q -> live A3 q = live A q) ->
  aroom A3 vm3 k3 b3 -> (kR - RK10_hmt 1 <= k3)%Z -> (bR - RB10_hmt 1 w h <= b3)%Z ->
  getr r3 2 = Z_to_bv 64 (s - 64) -> getr r3 10 = Z_to_bv 64 p3 -> getr r3 8 = Z_to_bv 64 0 -> (forall x, In x DRh -> getr r3 x = getr regs x) ->
  realizes SEGS (mkCfg (mkst r3 (0x28320 : word) m3 al_rom) (with_vmmaps vm3 md)) S.
Proof.
  intros A3 m3 vm3 r3 p1 cd1 data1 ad1 p2 cd2 data2 ad2 p3 cd3 data3 ad3 k3 b3 HW3 PM3 CE3 R1 R2 OO1 OO2 OO3 D12 D13 D23 LEQ3 Hrm3 Hk3 Hb3 Q2 Q10 Q8 RR.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold HMT_STACK, FHG_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof RB10_hmt_pos as HBpos. assert (HKpos : (0 <= RK10_hmt 1)%Z) by (cbv; discriminate).
  pose proof (oown_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ OO3) as Hp3.
  assert (Hs64 : (64 <= s)%Z) by lia. assert (Hs264 : (s < 2 ^ 64)%Z) by lia.
  assert (SUB3 : sub_live A A3).
  { intros q k Lq. rewrite LEQ3; [exact Lq | | |]; intros B;
      [rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OO1 q B) in Lq | rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OO2 q B) in Lq
      | rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OO3 q B) in Lq]; discriminate. }
  (* [comment removed for export] *)
  destruct (hd_D al_rom r3 m3 s p3 Hs64 Hs264 (W_sok_win C A3 m3 _ (s - 56) 8 CK HW3 ltac:(lia) ltac:(cbn; lia)) Q2 Q10) as (r4 & RUN4 & E1 & E10 & E9 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |]. clear RUN4.
  set (M4 := wbytes m3 (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 p3))).
  assert (WP4 : W C A3 M4 (with_vmmaps vm3 md) /\ POSTM C A3 s m3 M4) by (subst M4; wp_win CK).
  destruct WP4 as [HW4 PM4].
  assert (OUT4 : forall x : word, ~ (s - 56 <= u x < s - 48)%Z -> M4 x = m3 x).
  { intros x Hx. subst M4. apply (wbytes_out_Z _ (s - 56) 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  assert (CE4 : cellsZ M4 (frameD s ret regs)) by (apply (cellsD_out m3 M4 (s - 56) (s - 48) s); [exact OUT4 | lia | lia | lia | exact CE3]).
  assert (R1' : rdn SEGS M4 (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 p1)) by (apply (cell_out m3 M4); [intros x Hx; apply OUT4; lia | lia | lia | exact R1]).
  assert (R2' : rdn SEGS M4 (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 p2)) by (apply (cell_out m3 M4); [intros x Hx; apply OUT4; lia | lia | lia | exact R2]).
  pose proof (oown_keep C A A3 A3 A3 m3 M4 _ _ _ _ _ _ _ _ _ _ OO1 (fun _ _ => eq_refl) (fun _ _ => eq_refl) (proj2 PM4)) as OO1'.
  pose proof (oown_keep C A A3 A3 A3 m3 M4 _ _ _ _ _ _ _ _ _ _ OO2 (fun _ _ => eq_refl) (fun _ _ => eq_refl) (proj2 PM4)) as OO2'.
  pose proof (oown_keep C A A3 A3 A3 m3 M4 _ _ _ _ _ _ _ _ _ _ OO3 (fun _ _ => eq_refl) (fun _ _ => eq_refl) (proj2 PM4)) as OO3'.
  assert (PM4' : POSTM C A s m M4) by (eapply POSTM_trans; [exact PM3 | apply (POSTM_sub C A A3); [exact SUB3 | exact PM4]]).
  apply (pixDestroy_opt_W C A A3 M4 (with_vmmaps vm3 md) r4 (s - 64) (s - 40) p1 (w + 64) (h + 64) 1 cd1 data1 ad1 kd kna kn (Z_to_bv 64 0x28330) S CK HW4
           ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia)
           E1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) E10 R1' OO1').
  intros A4 m5 vm4 r5 HW5 CS5 DEAD1 LEQ4 PM5 OUT5 RT5. rewrite with_vmmaps_twice in HW5 |- *. rewrite with_vmmaps_vmmaps in RT5.
  replace (Z_to_bv 64 0x28330) with (0x28330 : word) by (apply bv_eq; reflexivity).
  replace (s - 40 + 8)%Z with (s - 32)%Z in PM5 by lia.
  pose proof (RT5 k3 b3 Hrm3 ltac:(lia) ltac:(lia)) as Hrm4. rewrite !Z.sub_0_r in Hrm4.
  assert (SUB4 : sub_live A A4).
  { intros q k Lq. rewrite LEQ4; [exact (SUB3 q k Lq) | intros B; rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OO1 q B) in Lq; discriminate]. }
  assert (PM5' : POSTM C A s m m5) by (eapply POSTM_trans; [exact PM4' | apply (POSTM_sub C A A4); [exact SUB4 | eapply POSTM_mono; [|exact PM5]; lia]]).
  assert (CE5 : cellsZ m5 (frameD s ret regs)) by (apply (cellsD_frm C (s - 32) M4 m5 s); [exact CK | exact (proj1 PM5) | lia | lia | lia | lia | exact CE4]).
  assert (R2'' : rdn SEGS m5 (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 p2)) by (apply (cell_out M4 m5); [intros x Hx; apply OUT5; lia | lia | lia | exact R2']).
  pose proof (oown_keep C A A3 A4 A4 M4 m5 _ _ _ _ _ _ _ _ _ _ OO2' (fun q B => LEQ4 q (fun B1 => D12 q B1 B)) (fun q B => LEQ4 q (fun B1 => D12 q B1 B)) (proj2 PM5)) as OO2''.
  pose proof (oown_keep C A A3 A4 A4 M4 m5 _ _ _ _ _ _ _ _ _ _ OO3' (fun q B => LEQ4 q (fun B1 => D13 q B1 B)) (fun q B => LEQ4 q (fun B1 => D13 q B1 B)) (proj2 PM5)) as OO3''.
  (* [comment removed for export] *)
  destruct (hd_E al_rom r5 m5 s Hs64 Hs264 ltac:(csr; reflexivity)) as (r6 & RUN6 & G1 & G10 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN6 |]. clear RUN6.
  apply (pixDestroy_opt_W C A A4 m5 (with_vmmaps vm4 md) r6 (s - 64) (s - 48) p2 (w + 64) (h + 64) 1 cd2 data2 ad2 kd kna kn (Z_to_bv 64 0x28338) S CK HW5
           ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia)
           G1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) G10 R2'' OO2'').
  intros A5 m6 vm5 r7 HW6 CS7 DEAD2 LEQ5 PM6 OUT6 RT6. rewrite with_vmmaps_twice in HW6 |- *. rewrite with_vmmaps_vmmaps in RT6.
  replace (Z_to_bv 64 0x28338) with (0x28338 : word) by (apply bv_eq; reflexivity).
  replace (s - 48 + 8)%Z with (s - 40)%Z in PM6 by lia.
  pose proof (RT6 k3 b3 Hrm4 ltac:(lia) ltac:(lia)) as Hrm5. rewrite !Z.sub_0_r in Hrm5.
  assert (SUB5 : sub_live A A5).
  { intros q k Lq. rewrite LEQ5; [exact (SUB4 q k Lq) | intros B; rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OO2 q B) in Lq; discriminate]. }
  assert (PM6' : POSTM C A s m m6) by (eapply POSTM_trans; [exact PM5' | apply (POSTM_sub C A A5); [exact SUB5 | eapply POSTM_mono; [|exact PM6]; lia]]).
  assert (CE6 : cellsZ m6 (frameD s ret regs)) by (apply (cellsD_frm C (s - 40) m5 m6 s); [exact CK | exact (proj1 PM6) | lia | lia | lia | lia | exact CE5]).
  pose proof (oown_keep C A A4 A5 A5 m5 m6 _ _ _ _ _ _ _ _ _ _ OO3'' (fun q B => LEQ5 q (fun B2 => D23 q B2 B)) (fun q B => LEQ5 q (fun B2 => D23 q B2 B)) (proj2 PM6)) as OO3f.
  (* [comment removed for export] *)
  destruct (hd_F al_rom r7 regs m6 s p3 ret Hs64 Hs264 Hret CE6 ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r8 & RUN8 & Y2 & Y1 & Y10 & YR & AG8).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN8 |]. clear RUN8.
  assert (LEQF : forall q, ~ oblk p3 data3 cd3 ad3 q -> live A5 q = live A q).
  { intros q NB3.
    destruct (oblk_dec p2 data2 cd2 ad2 q) as [B2|NB2]; [rewrite (DEAD2 q B2), (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OO2 q B2); reflexivity|].
    rewrite (LEQ5 q NB2).
    destruct (oblk_dec p1 data1 cd1 ad1 q) as [B1|NB1]; [rewrite (DEAD1 q B1), (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OO1 q B1); reflexivity|].
    rewrite (LEQ4 q NB1). exact (LEQ3 q NB1 NB2 NB3). }
  apply (HKF A5 m6 vm5 r8 HW6).
  - apply cs_kept_intro; first [solve [apply YR; in_lit] | (csr; reflexivity)].
  - exact PM6'.
  - destruct OO3f as [P0 | OWN3].
    + left. split; [rewrite Y10, P0; reflexivity|]. intros q. apply LEQF. intros [NZ _]. contradiction.
    + right. exists p3, cd3, data3, ad3. split; [exact Y10|]. split; [exact OWN3|].
      intros q NB. apply LEQF. intros [_ B]. contradiction.
  - apply (aroom_mono A5 vm5 k3 b3); [exact Hrm5 | lia | lia].
Qed.

Local Ltac hmt_consts :=
  change (RB10_hmt 1 w h) with (2 * RB10_pixcopy (rast (w + 64) (h + 64) 1) + RB10_pixcopy (rast w h 1))%Z in *; change (RK10_hmt 1) with 12%Z in *;
  change RK_pixcopy with 4%Z in *.

(* [comment removed for export] *)
Lemma hd_from_C : forall A2 m2 vm2 r2 (p1 cd1 data1 ad1 p2 cd2 data2 ad2 k2 b2 : Z),
  W C A2 m2 (with_vmmaps vm2 md) -> POSTM C A s m m2 ->
  cellsZ m2 (frameD s ret regs) ->
  rdn SEGS m2 (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 p1) ->
  oown C A A2 m2 p1 (w + 64) (h + 64) 1 cd1 data1 ad1 kd kna kn -> oown C A A2 m2 p2 (w + 64) (h + 64) 1 cd2 data2 ad2 kd kna kn ->
  (p2 <> 0%Z -> hdr_ok (w + 64) (h + 64) 1) ->
  (forall q, oblk p1 data1 cd1 ad1 q -> ~ oblk p2 data2 cd2 ad2 q) ->
  (forall q, ~ oblk p1 data1 cd1 ad1 q -> ~ oblk p2 data2 cd2 ad2 q -> live A2 q = live A q) ->
  aroom A2 vm2 k2 b2 -> (kR - RK10_hmt 1 + RK_pixcopy <= k2)%Z -> (bR - RB10_hmt 1 w h + RB10_pixcopy (rast w h 1) <= b2)%Z ->
  getr r2 2 = Z_to_bv 64 (s - 64) -> getr r2 10 = Z_to_bv 64 p2 -> getr r2 8 = Z_to_bv 64 0 -> (forall x, In x DRh -> getr r2 x = getr regs x) ->
  realizes SEGS (mkCfg (mkst r2 (0x28314 : word) m2 al_rom) (with_vmmaps vm2 md)) S.
Proof.
  intros A2 m2 vm2 r2 p1 cd1 data1 ad1 p2 cd2 data2 ad2 k2 b2 HW2 PM2 CE2 R1 OO1 OO2 HOK2 D12 LEQ2 Hrm2 Hk2 Hb2 Q2 Q10 Q8 RR.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold HMT_STACK, FHG_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof RB10_hmt_pos as HBpos. hmt_consts.
  pose proof (rast_nn w h ltac:(lia) ltac:(lia)) as Rnn. pose proof (raster_pos w h 1 HOK Hw Hh) as Rpos.
  assert (Hpc : (0 <= RB10_pixcopy (rast w h 1))%Z) by (unfold RB10_pixcopy, RB10_pix, RB10_cmapcopy; lia).
  pose proof (oown_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ OO2) as Hp2.
  assert (Hs64 : (64 <= s)%Z) by lia. assert (Hs264 : (s < 2 ^ 64)%Z) by lia.
  assert (SUB2 : sub_live A A2).
  { intros q k Lq. rewrite LEQ2; [exact Lq | |]; intros B;
      [rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OO1 q B) in Lq | rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OO2 q B) in Lq]; discriminate. }
  destruct (hd_C al_rom r2 m2 s p2 Hs64 Hs264 (W_sok_win C A2 m2 _ (s - 48) 8 CK HW2 ltac:(lia) ltac:(cbn; lia)) Q2 Q10) as (r3 & RUN3 & E1 & E10 & E11 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |]. clear RUN3.
  set (M3 := wbytes m2 (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 p2))).
  assert (WP3 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C A2 s m2 M3) by (subst M3; wp_win CK).
  destruct WP3 as [HW3 PM3].
  assert (OUT3 : forall x : word, ~ (s - 48 <= u x < s - 40)%Z -> M3 x = m2 x).
  { intros x Hx. subst M3. apply (wbytes_out_Z _ (s - 48) 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  assert (CE3 : cellsZ M3 (frameD s ret regs)) by (apply (cellsD_out m2 M3 (s - 48) (s - 40) s); [exact OUT3 | lia | lia | lia | exact CE2]).
  assert (R1' : rdn SEGS M3 (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 p1)) by (apply (cell_out m2 M3); [intros x Hx; apply OUT3; lia | lia | lia | exact R1]).
  assert (R2' : rdn SEGS M3 (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 p2)) by (subst M3; apply cell_wr; lia).
  pose proof (oown_keep C A A2 A2 A2 m2 M3 _ _ _ _ _ _ _ _ _ _ OO1 (fun _ _ => eq_refl) (fun _ _ => eq_refl) (proj2 PM3)) as OO1'.
  pose proof (oown_keep C A A2 A2 A2 m2 M3 _ _ _ _ _ _ _ _ _ _ OO2 (fun _ _ => eq_refl) (fun _ _ => eq_refl) (proj2 PM3)) as OO2'.
  assert (PM3' : POSTM C A s m M3) by (eapply POSTM_trans; [exact PM2 | apply (POSTM_sub C A A2); [exact SUB2 | exact PM3]]).
  destruct OO2' as [P0 | OWN2].
  - (* [comment removed for export] *)
    subst p2.
    destruct (prb_N al_rom r3 M3 (W_sev_got C A2 M3 _ HW3) (W_sev C A2 M3 _ HW3) E10) as (r4 & RUN4 & F10 & F11 & F12 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |]. clear RUN4.
    apply (returnErrorPtr_W C A2 M3 _ r4 (s - 64) 0x10298 0x10ced 16 15 (Z_to_bv 64 0x28320) (Z_to_bv 64 0) S CK HW3 ltac:(csr; reflexivity)
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) ltac:(csr; reflexivity) ltac:(red; apply bv_eq; reflexivity)
             F10 F11 F12 str_msg_pixs_undef2 str_pixRemoveBorder).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    replace (Z_to_bv 64 0x28320) with (0x28320 : word) by (apply bv_eq; reflexivity).
    assert (PM4 : POSTM C A2 (s - 64) M3 m4) by (eapply (POSTM_range C A2 M3 _ m4); [exact CK | exact HW3 | exact OUT4 | lia | lia | lia]).
    apply (hd_tail A2 m4 vm2 r5 p1 cd1 data1 ad1 0 cd2 data2 ad2 0 0 0 0 k2 b2 HW4).
    + eapply POSTM_trans; [exact PM3' | apply (POSTM_sub C A A2); [exact SUB2 | eapply POSTM_mono; [|exact PM4]; lia]].
    + apply (cellsD_out M3 m4 (s - 64 - (16 + 3376)) (s - 64) s); [exact OUT4 | lia | lia | lia | exact CE3].
    + apply (cell_out M3 m4); [intros x Hx; apply OUT4; lia | lia | lia | exact R1'].
    + apply (cell_out M3 m4); [intros x Hx; apply OUT4; lia | lia | lia | exact R2'].
    + exact (oown_keep C A A2 A2 A2 M3 m4 _ _ _ _ _ _ _ _ _ _ OO1' (fun _ _ => eq_refl) (fun _ _ => eq_refl) (proj2 PM4)).
    + left; reflexivity.
    + left; reflexivity.
    + intros q _ [NZ _]. contradiction.
    + intros q _ [NZ _]. contradiction.
    + intros q [NZ _]. contradiction.
    + intros q N1 N2 _. exact (LEQ2 q N1 N2).
    + exact Hrm2.
    + hmt_consts; lia.
    + hmt_consts; lia.
    + csr; reflexivity.
    + exact A10.
    + csr; reflexivity.
    + intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]); destruct Hx.
  - (* [comment removed for export] *)
    assert (NZ2 : p2 <> 0%Z) by (destruct OWN2 as (Gp & _); lia). specialize (HOK2 NZ2).
    pose proof OWN2 as (Gp2 & TOPp2 & ALp2 & Gd2 & TOPd2 & ALd2 & NEpd2 & Rpos2 & PX2 & Lp2 & Ld2 & FR2 & CMR2).
    destruct (prb_run al_rom r3 M3 p2 32 ltac:(lia) ltac:(lia) E10 E11) as (r4 & RUN4 & F12 & F13 & F14 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |]. clear RUN4.
    replace (0x18304 : word) with (Z_to_bv 64 PC_pixRemoveBorderGeneral) by (apply bv_eq; reflexivity).
    rewrite <- (with_vmmaps_vmmaps vm2 md) in Hrm2.
    apply (RBG C A2 M3 (with_vmmaps vm2 md) r4 (s - 64)%Z p2 (w + 64)%Z (h + 64)%Z 1%Z cd2 data2 32%Z 32%Z 32%Z 32%Z (CMAPV ad2 kd kna kn 0) (Z_to_bv 64 0x28320) S CK HW3
             ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold RBG_STACK, LSF; lia) ltac:(lia)
             ltac:(csr; reflexivity) ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
             F12 F13 F14 PX2 HOK2 (or_introl eq_refl) Lp2 Ld2 (pown_cm_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWN2)
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) ltac:(lia) k2 b2 Hrm2 ltac:(hmt_consts; lia)
             ltac:(replace (w + 64 - 32 - 32)%Z with w by lia; replace (h + 64 - 32 - 32)%Z with h by lia; fold (rast w h 1); lia)).
    replace (w + 64 - 32 - 32)%Z with w by lia. replace (h + 64 - 32 - 32)%Z with h by lia. fold (rast w h 1).
    intros A3 m4 vm3 r5 HW4 CS5 PM4 RES Hrm3. rewrite with_vmmaps_twice in HW4 |- *.
    replace (Z_to_bv 64 0x28320) with (0x28320 : word) by (apply bv_eq; reflexivity).
    assert (RES' : (getr r5 10 = Z_to_bv 64 0 /\ forall q, live A3 q = live A2 q)
                   \/ (exists pixd cd data, getr r5 10 = Z_to_bv 64 pixd /\ pixt_new C A2 A3 m4 pixd w h 1 cd data (CMAPV ad2 kd kna kn 0))).
    { destruct RES as [L | (pixd & cd & data & E & _ & PT)]; [left; exact L | right; exists pixd, cd, data; split; assumption]. }
    destruct (res_oown C A2 A3 m4 r5 w h _ Rpos RES') as (p3 & cd3 & data3 & ad3 & R10 & OO3 & LEQ3). cbn [c_d c_nalloc c_n] in OO3.
    pose proof (oown_disj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OO1' OO3 (sub_live_refl A2)) as D13.
    pose proof (oown_disj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (or_intror OWN2) OO3 (sub_live_refl A2)) as D23.
    apply (hd_tail A3 m4 vm3 r5 p1 cd1 data1 ad1 p2 cd2 data2 ad2 p3 cd3 data3 ad3 (k2 - 4) (b2 - RB10_pixcopy (rast w h 1)) HW4).
    + eapply POSTM_trans; [exact PM3' | apply (POSTM_sub C A A2); [exact SUB2 | eapply POSTM_mono; [|exact PM4]; lia]].
    + apply (cellsD_frm C (s - 64) M3 m4 s); [exact CK | exact (proj1 PM4) | lia | lia | lia | lia | exact CE3].
    + apply (cell_frm C (s - 64) M3 m4); [exact CK | exact (proj1 PM4) | lia | lia | lia | exact R1'].
    + apply (cell_frm C (s - 64) M3 m4); [exact CK | exact (proj1 PM4) | lia | lia | lia | exact R2'].
    + exact (oown_keep C A A2 A3 A2 M3 m4 _ _ _ _ _ _ _ _ _ _ OO1' (fun q B => LEQ3 q (D13 q B)) (fun _ _ => eq_refl) (proj2 PM4)).
    + exact (oown_keep C A A2 A3 A2 M3 m4 _ _ _ _ _ _ _ _ _ _ (or_intror OWN2) (fun q B => LEQ3 q (D23 q B)) (fun _ _ => eq_refl) (proj2 PM4)).
    + exact (oown_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OO3 SUB2).
    + exact D12.
    + exact D13.
    + exact D23.
    + intros q N1 N2 N3. rewrite (LEQ3 q N3). exact (LEQ2 q N1 N2).
    + exact Hrm3.
    + hmt_consts; lia.
    + hmt_consts; lia.
    + csr; reflexivity.
    + exact R10.
    + csr; reflexivity.
    + intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]); destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma hd_from_B : forall A1 m1 vm1 r1 (p1 cd1 data1 ad1 k1 b1 : Z),
  W C A1 m1 (with_vmmaps vm1 md) -> POSTM C A s m m1 ->
  cellsZ m1 (frameD s ret regs) ->
  oown C A A1 m1 p1 (w + 64) (h + 64) 1 cd1 data1 ad1 kd kna kn -> (p1 <> 0%Z -> hdr_ok (w + 64) (h + 64) 1) ->
  (forall q, ~ oblk p1 data1 cd1 ad1 q -> live A1 q = live A q) ->
  aroom A1 vm1 k1 b1 -> (kR - RK10_hmt 1 + 2 * RK_pixcopy <= k1)%Z ->
  (bR - RB10_hmt 1 w h + RB10_pixcopy (rast (w + 64) (h + 64) 1) + RB10_pixcopy (rast w h 1) <= b1)%Z ->
  getr r1 2 = Z_to_bv 64 (s - 64) -> getr r1 10 = Z_to_bv 64 p1 -> getr r1 8 = Z_to_bv 64 0 -> getr r1 9 = Z_to_bv 64 name ->
  (forall x, In x DRh -> getr r1 x = getr regs x) ->
  realizes SEGS (mkCfg (mkst r1 (0x28300 : word) m1 al_rom) (with_vmmaps vm1 md)) S.
Proof.
  intros A1 m1 vm1 r1 p1 cd1 data1 ad1 k1 b1 HW1 PM1 CE1 OO1 HOK1 LEQ1 Hrm1 Hk1 Hb1 Q2 Q10 Q8 Q9 RR.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold HMT_STACK, FHG_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof RB10_hmt_pos as HBpos. hmt_consts.
  pose proof (rast_nn w h ltac:(lia) ltac:(lia)) as Rnn. pose proof (rast_nn (w + 64) (h + 64) ltac:(lia) ltac:(lia)) as Rnnb.
  assert (Hpc : (0 <= RB10_pixcopy (rast w h 1))%Z) by (unfold RB10_pixcopy, RB10_pix, RB10_cmapcopy; lia).
  assert (Hpcb : (0 <= RB10_pixcopy (rast (w + 64) (h + 64) 1))%Z) by (unfold RB10_pixcopy, RB10_pix, RB10_cmapcopy; lia).
  pose proof (oown_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ OO1) as Hp1.
  assert (Hs64 : (64 <= s)%Z) by lia. assert (Hs264 : (s < 2 ^ 64)%Z) by lia.
  pose proof (oown_sub_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ OO1 LEQ1) as SUB1.
  destruct (hd_B al_rom r1 m1 s p1 name Hs64 Hs264 (W_sok_win C A1 m1 _ (s - 40) 8 CK HW1 ltac:(lia) ltac:(cbn; lia)) Q2 Q10 Q9) as (r2 & RUN2 & E1 & E10 & E11 & E12 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |]. clear RUN2.
  set (M2 := wbytes m1 (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 p1))).
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A1 s m1 M2) by (subst M2; wp_win CK).
  destruct WP2 as [HW2 PM2].
  assert (OUT2 : forall x : word, ~ (s - 40 <= u x < s - 32)%Z -> M2 x = m1 x).
  { intros x Hx. subst M2. apply (wbytes_out_Z _ (s - 40) 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  assert (CE2 : cellsZ M2 (frameD s ret regs)) by (apply (cellsD_out m1 M2 (s - 40) (s - 32) s); [exact OUT2 | lia | lia | lia | exact CE1]).
  assert (R1 : rdn SEGS M2 (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 p1)) by (subst M2; apply cell_wr; lia).
  pose proof (oown_keep C A A1 A1 A1 m1 M2 _ _ _ _ _ _ _ _ _ _ OO1 (fun _ _ => eq_refl) (fun _ _ => eq_refl) (proj2 PM2)) as OO1'.
  assert (PM2' : POSTM C A s m M2) by (eapply POSTM_trans; [exact PM1 | apply (POSTM_sub C A A1); [exact SUB1 | exact PM2]]).
  replace (0x283dc : word) with (Z_to_bv 64 PC_pixFHMTGen_1) by (apply bv_eq; reflexivity).
  destruct OO1' as [P0 | OWN1].
  - (* [comment removed for export] *)
    subst p1.
    apply (GENN C A1 M2 (with_vmmaps vm1 md) r2 (s - 64)%Z (Z_to_bv 64 0x28314) S CK HW2 ltac:(csr; reflexivity)
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold FHG_STACK, LSF; lia) ltac:(lia) E1 ltac:(red; apply bv_eq; reflexivity) E10 E11).
    intros m3 r3 HW3 CS3 PM3 A10.
    replace (Z_to_bv 64 0x28314) with (0x28314 : word) by (apply bv_eq; reflexivity).
    apply (hd_from_C A1 m3 vm1 r3 0 cd1 data1 ad1 0 0 0 0 k1 b1 HW3).
    + eapply POSTM_trans; [exact PM2' | apply (POSTM_sub C A A1); [exact SUB1 | eapply POSTM_mono; [|exact PM3]; lia]].
    + apply (cellsD_frm C (s - 64) M2 m3 s); [exact CK | exact (proj1 PM3) | lia | lia | lia | lia | exact CE2].
    + apply (cell_frm C (s - 64) M2 m3); [exact CK | exact (proj1 PM3) | lia | lia | lia | exact R1].
    + left; reflexivity.
    + left; reflexivity.
    + intros NZ. contradiction.
    + intros q [NZ _]. contradiction.
    + intros q N1 _. exact (LEQ1 q N1).
    + exact Hrm1.
    + hmt_consts; lia.
    + hmt_consts; lia.
    + csr; reflexivity.
    + exact A10.
    + csr; reflexivity.
    + intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]); destruct Hx.
  - (* [comment removed for export] *)
    assert (NZ1 : p1 <> 0%Z) by (destruct OWN1 as (Gp & _); lia). specialize (HOK1 NZ1).
    pose proof OWN1 as (Gp1 & TOPp1 & ALp1 & Gd1 & TOPd1 & ALd1 & NEpd1 & Rpos1 & PX1 & Lp1 & Ld1 & FR1 & CMR1).
    assert (HNM2 : selname_at (alloc_top (c_vm C)) A1 M2 name (hm_name j)).
    { apply (selname_at_keep _ A A1 m M2); [lia | exact HNM | exact SUB1 | exact (proj2 PM2')]. }
    rewrite <- (with_vmmaps_vmmaps vm1 md) in Hrm1.
    apply (GEN C A1 M2 (with_vmmaps vm1 md) r2 (s - 64)%Z p1 w h cd1 data1 name j (CMAPV ad1 kd kna kn 0) (Z_to_bv 64 0x28314) S CK HW2 ltac:(csr; reflexivity)
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold FHG_STACK, LSF; lia) ltac:(lia) E1 ltac:(red; apply bv_eq; reflexivity)
             ltac:(csr; reflexivity) E10 E11 E12 PX1 HOK1 Hw Hh Lp1 Ld1 (pown_cm_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWN1) Hj HNM2
             k1 b1 Hrm1 ltac:(hmt_consts; lia) ltac:(fold (rast (w + 64) (h + 64) 1); lia)).
    fold (rast (w + 64) (h + 64) 1).
    intros A2 m3 vm2 r3 HW3 CS3 PM3 RES Hrm2. rewrite with_vmmaps_twice in HW3 |- *.
    replace (Z_to_bv 64 0x28314) with (0x28314 : word) by (apply bv_eq; reflexivity).
    destruct (res_oown C A1 A2 m3 r3 (w + 64) (h + 64) _ Rpos1 RES) as (p2 & cd2 & data2 & ad2 & R10 & OO2 & LEQ2). cbn [c_d c_nalloc c_n] in OO2.
    pose proof (oown_disj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (or_intror OWN1) OO2 (sub_live_refl A1)) as D12.
    apply (hd_from_C A2 m3 vm2 r3 p1 cd1 data1 ad1 p2 cd2 data2 ad2 (k1 - 4) (b1 - RB10_pixcopy (rast (w + 64) (h + 64) 1)) HW3).
    + eapply POSTM_trans; [exact PM2' | apply (POSTM_sub C A A1); [exact SUB1 | eapply POSTM_mono; [|exact PM3]; lia]].
    + apply (cellsD_frm C (s - 64) M2 m3 s); [exact CK | exact (proj1 PM3) | lia | lia | lia | lia | exact CE2].
    + apply (cell_frm C (s - 64) M2 m3); [exact CK | exact (proj1 PM3) | lia | lia | lia | exact R1].
    + exact (oown_keep C A A1 A2 A1 M2 m3 _ _ _ _ _ _ _ _ _ _ (or_intror OWN1) (fun q B => LEQ2 q (D12 q B)) (fun _ _ => eq_refl) (proj2 PM3)).
    + exact (oown_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OO2 SUB1).
    + intros _. exact HOK1.
    + exact D12.
    + intros q N1 N2. rewrite (LEQ2 q N2). exact (LEQ1 q N1).
    + exact Hrm2.
    + hmt_consts; lia.
    + hmt_consts; lia.
    + csr; reflexivity.
    + exact R10.
    + csr; reflexivity.
    + intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]); destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma hd_main : forall (pixs cm datas : Z) (cv : cmapv),
  W C A m md -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 pixs -> getr regs 12 = Z_to_bv 64 name ->
  PIXat m pixs (hdv w h 1 cm datas) ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z -> cm_facts A m cm cv ->
  aroom A (m_vmmaps md) kR bR -> kd = c_d cv -> kna = c_nalloc cv -> kn = c_n cv ->
  realizes SEGS (mkCfg (mkst regs (0x282bc : word) m al_rom) md) S.
Proof.
  intros pixs cm datas cv HW H1 H10 H11 H12 PXs Lps Lds HCM Hrm Ekd Ekna Ekn.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold HMT_STACK, FHG_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof RB10_hmt_pos as HBpos. hmt_consts.
  pose proof (rast_nn w h ltac:(lia) ltac:(lia)) as Rnn. pose proof (rast_nn (w + 64) (h + 64) ltac:(lia) ltac:(lia)) as Rnnb.
  assert (Hpc : (0 <= RB10_pixcopy (rast w h 1))%Z) by (unfold RB10_pixcopy, RB10_pix, RB10_cmapcopy; lia).
  assert (Hpcb : (0 <= RB10_pixcopy (rast (w + 64) (h + 64) 1))%Z) by (unfold RB10_pixcopy, RB10_pix, RB10_cmapcopy; lia).
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALp16 & _). rewrite u_Z2bv in ALp16 by (destruct PXs as (? & ? & _); lia). pose proof (al16_mod8 _ ALp16) as AL8s.
  assert (Hs64 : (64 <= s)%Z) by lia. assert (Hs264 : (s < 2 ^ 64)%Z) by lia.
  (* [comment removed for export] *)
  destruct (hd_A0 al_rom regs m s 0 pixs name (hdv w h 1 cm datas) ret Hs64 Hs264 ltac:(lia) AL8s PXs ltac:(lia)
              (W_sok_win C A m md (s - 64) 64 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12) as (r1 & RUN1 & Q2 & Q10 & Q8 & Q18 & Q9 & AG1).
  cbn [p_d hdv] in Q10.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. clear RUN1.
  assert (WP1 : W C A (FRD m s ret regs) md /\ POSTM C A s m (FRD m s ret regs)) by (unfold FRD; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FRD m s ret regs) in *.
  pose proof (cells_FRD m s ret regs Hs64 Hs264) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 32 <= u x < s)%Z -> M1 x = m x) by (intros x Hx; subst M1; apply FRD_out; lia).
  assert (PXs1 : PIXat M1 pixs (hdv w h 1 cm datas)) by (apply (PIXat_frame m); [exact PXs | intros x Hx; apply OUT1; lia]).
  assert (HCM1 : cm_facts A M1 cm cv).
  { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right]. split; [| split; [exact CMOK | split; [exact Lcm | exact Larr]]].
    pose proof CM as (Hc0 & Hc64 & _). destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
    apply (CMAPat_frame m); [exact CM|]. intros x Hx. apply OUT1. lia. }
  (* [comment removed for export] *)
  destruct (hd_A1 al_rom r1 M1 pixs Q10 Q18) as (r2 & RUN2 & V1 & V10 & V11 & V12 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |]. clear RUN2.
  destruct (pab_run al_rom r2 M1 pixs 32 0 ltac:(lia) ltac:(lia) V10 V11 V12) as (r3 & RUN3 & X12 & X13 & X14 & X15 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |]. clear RUN3.
  replace (0x17fb8 : word) with (Z_to_bv 64 PC_pixAddBorderGeneral) by (apply bv_eq; reflexivity).
  apply (ABG C A M1 md r3 (s - 64)%Z pixs w h 1%Z cm datas 32%Z 32%Z 32%Z 32%Z 0%Z cv (Z_to_bv 64 0x28300) S CK HW1
           ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ABG_STACK, LSF; lia) ltac:(lia)
           ltac:(csr; reflexivity) ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
           X12 X13 X14 X15 PXs1 HOK Hw Hh (or_introl eq_refl) Lps Lds HCM1
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl (or_introl eq_refl) kR bR Hrm ltac:(hmt_consts; lia)
           ltac:(replace (w + 32 + 32)%Z with (w + 64)%Z by lia; replace (h + 32 + 32)%Z with (h + 64)%Z by lia; fold (rast (w + 64) (h + 64) 1); lia)).
  replace (w + 32 + 32)%Z with (w + 64)%Z by lia. replace (h + 32 + 32)%Z with (h + 64)%Z by lia. fold (rast (w + 64) (h + 64) 1).
  intros A1 m2 vm1 r4 HW2 CS4 PM2 RES Hrm1.
  replace (Z_to_bv 64 0x28300) with (0x28300 : word) by (apply bv_eq; reflexivity).
  assert (HOKb : getr r4 10 <> Z_to_bv 64 0 -> hdr_ok (w + 64) (h + 64) 1).
  { destruct RES as [[L _] | (pixd & cd & data & E & HOKb & PT)]; [intros X; contradiction | intros _; exact HOKb]. }
  assert (RES' : (getr r4 10 = Z_to_bv 64 0 /\ forall q, live A1 q = live A q)
                 \/ (exists pixd cd data, getr r4 10 = Z_to_bv 64 pixd /\ pixt_new C A A1 m2 pixd (w + 64) (h + 64) 1 cd data cv)).
  { destruct RES as [L | (pixd & cd & data & E & _ & PT)]; [left; exact L | right; exists pixd, cd, data; split; assumption]. }
  assert (RposB : forall pixd cd data, pixt_new C A A1 m2 pixd (w + 64) (h + 64) 1 cd data cv -> hdr_ok (w + 64) (h + 64) 1 -> (0 < 4 * (wpl_of (w + 64) 1 * (h + 64)))%Z).
  { intros pixd cd data _ HOKb'. apply (raster_pos _ _ _ HOKb'); lia. }
  assert (OOB : exists p1 cd1 data1 ad1, getr r4 10 = Z_to_bv 64 p1 /\ oown C A A1 m2 p1 (w + 64) (h + 64) 1 cd1 data1 ad1 kd kna kn /\
                  (p1 <> 0%Z -> hdr_ok (w + 64) (h + 64) 1) /\ (forall q, ~ oblk p1 data1 cd1 ad1 q -> live A1 q = live A q)).
  { destruct RES as [[R10 LEQ] | (pixd & cd & data & R10 & HOKb' & PT)].
    - exists 0%Z, 0%Z, 0%Z, 0%Z. split; [exact R10|]. split; [left; reflexivity|]. split; [intros X; contradiction|]. intros q _. apply LEQ.
    - destruct (pixt_new_pown _ _ _ _ _ _ _ _ _ _ _ PT (RposB _ _ _ PT HOKb')) as (ad & OWN & LEQ). rewrite <- Ekd, <- Ekna, <- Ekn in OWN.
      exists pixd, cd, data, ad. split; [exact R10|]. split; [right; exact OWN|]. split; [intros _; exact HOKb'|].
      intros q NB. apply LEQ. intros B. apply NB. split; [destruct OWN as (Gp & _); lia | exact B]. }
  destruct OOB as (p1 & cd1 & data1 & ad1 & R10 & OO1 & HOK1 & LEQ1).
  apply (hd_from_B A1 m2 vm1 r4 p1 cd1 data1 ad1 (kR - 4) (bR - RB10_pixcopy (rast (w + 64) (h + 64) 1)) HW2).
  - eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PM2]; lia].
  - apply (cellsD_frm C (s - 64) M1 m2 s); [exact CK | exact (proj1 PM2) | lia | lia | lia | lia | exact CE1].
  - exact OO1.
  - exact HOK1.
  - exact LEQ1.
  - exact Hrm1.
  - hmt_consts; lia.
  - hmt_consts; lia.
  - csr; reflexivity.
  - exact R10.
  - csr; reflexivity.
  - csr; reflexivity.
  - intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]); destruct Hx.
Qed.

End Body.

Theorem pixHMTDwa_1_W : pixAddBorderGeneral_contract -> pixRemoveBorderGeneral_contract -> pixFHMTGen_1_contract -> pixFHMTGen_1_null_contract ->
  pixHMTDwa_1_contract.
Proof.
  intros ABG RBG GEN GENN. unfold pixHMTDwa_1_contract.
  intros C A m md regs s pixs w h cm datas name j cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 PXs HOK Hw Hh Lps Lds HCM Hj HNM kR bR Hrm Hrk Hrb HK.
  replace (Z_to_bv 64 PC_pixHMTDwa_1) with (0x282bc : word) by (apply bv_eq; reflexivity).
  exact (hd_main ABG RBG GEN GENN C A m md regs s w h (c_d cv) (c_nalloc cv) (c_n cv) name j ret S kR bR CK Hs16 Hlo Hhi Hret H2 H4 HOK Hw Hh Hj HNM Hrk Hrb HK
           pixs cm datas cv HW H1 H10 H11 H12 PXs Lps Lds HCM Hrm eq_refl eq_refl eq_refl).
Qed.

End HmtW.
