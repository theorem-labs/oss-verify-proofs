(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.

Section LG.
Context {RC : run_ceil}.
Variable SEGS : list Segment.
Variable FXOK : FPState -> Prop.
Variable IA : as_addrs.
Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
Variable FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Z -> Prop.
Variable fsbase : Z.
(* [comment removed for export] *)
Hypothesis ZONE : forall h Lc FF B C K M mdl b n, AAINVH h Lc FF B C K M mdl -> In (b, n) Lc -> ablk_ok IA b n /\ 1 <= n /\ b mod 16 = 0.
Hypothesis DISJ : forall h Lc FF B C K M mdl L1 L2 b n b' n',
  AAINVH h Lc FF B C K M mdl -> Lc = L1 ++ (b, n) :: L2 -> In (b', n') (L1 ++ L2) -> b + n <= b' \/ b' + n' <= b.
(* [comment removed for export] *)
Hypothesis IMG_LO : ia_img_hi IA <= AS_LO.
Hypothesis PRIV_IMG : forall z, in_wins (ia_priv IA) z -> z < ia_img_hi IA.
Hypothesis ERRNO_IMG : ia_errno IA + 4 <= ia_img_hi IA.

Definition LG (M : mem) (L : list (Z * Z)) : Prop := forall b n, In (b, n) L -> last_gran_ok M b n.
Definition AAINV_LG (X : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop) :
  list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop :=
  fun Lc FF B C K M mdl => X Lc FF B C K M mdl /\ LG M Lc.
Definition AAINVL (h : option Z) := AAINV_LG (AAINVH h).

(* [comment removed for export] *)
Definition egb (b n : Z) : Z := SB + (b + n) / 8.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma egb_band : forall b n, ablk_ok IA b n -> 1 <= n -> SB <= egb b n /\ egb b n < AS_HEAPLO /\ egb b n < CEIL.
Proof.
  intros b n (A1 & A2 & A3 & A4) Hn. pose proof ceil_rng as CR. unfold egb, SB, AS_HEAPLO, PTRLO, AS_LO in *. lia.
Qed.
Lemma egb_in_shadow : forall b n, n mod 8 <> 0 -> b mod 16 = 0 -> 0 <= b -> 0 <= n -> sh_lo b <= egb b n < sh_hi b n.
Proof. intros b n Hm Hal Hb Hn. unfold egb, sh_lo, sh_hi. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma LG_kept : forall M M' L L',
  LG M L -> (forall x, In x L' -> In x L) ->
  (forall b n, In (b, n) L' -> n mod 8 <> 0 -> M' (Z_to_bv 64 (egb b n)) = M (Z_to_bv 64 (egb b n))) ->
  LG M' L'.
Proof.
  intros M M' L L' H Hs Hk b n Hin Hm. specialize (H b n (Hs _ Hin) Hm). unfold last_gran_ok, sbyte in *.
  fold (egb b n) in H |- *. rewrite (Hk b n Hin Hm). exact H.
Qed.

(* [comment removed for export] *)
Lemma changed_not_egb : forall stk Lc FF sp (a : word) b n,
  as_changed IA stk Lc FF sp a -> CEIL + stk <= sp -> 0 <= stk ->
  In (b, n) Lc -> ablk_ok IA b n -> 1 <= n -> b mod 16 = 0 -> n mod 8 <> 0 -> u a <> egb b n.
Proof.
  intros stk Lc FF sp a b n Hc Hsp Hstk Hin Hab Hn Hal Hm He.
  destruct (egb_band b n Hab Hn) as (E1 & E2 & E3).
  destruct Hc as [Hs|[(Hlt & Hni & Hnv)|[Hp|Her]]].
  - lia.
  - apply Hnv. right; right; left. exists b, n. split; [exact Hin|]. rewrite He. destruct Hab as (A1 & _). unfold PTRLO in A1.
    exact (egb_in_shadow b n Hm Hal ltac:(lia) ltac:(lia)).
  - pose proof (PRIV_IMG _ Hp). unfold AS_LO, SB in *. lia.
  - unfold in_errno in Her. unfold AS_LO, SB in *. lia.
Qed.

Lemma LG_changed : forall stk M M' Lc Lc' FF FFa sp h B C K mdl,
  LG M Lc -> (forall x, In x Lc' -> In x Lc) ->
  AAINVH h Lc' FFa B C K M' mdl ->
  (forall a : word, M' a <> M a -> as_changed IA stk Lc' FF sp a) -> CEIL + stk <= sp -> 0 <= stk ->
  LG M' Lc'.
Proof.
  intros stk M M' Lc Lc' FF FFa sp h B C K mdl HL Hs HA Hch Hsp Hstk.
  apply (LG_kept M M' Lc Lc' HL Hs). intros b n Hin Hm.
  destruct (ZONE h _ _ _ _ _ _ _ b n HA Hin) as (Hab & Hn & Hal).
  destruct (decide (M' (Z_to_bv 64 (egb b n)) = M (Z_to_bv 64 (egb b n)))) as [Heq|Hne]; [exact Heq|]. exfalso.
  destruct (egb_band b n Hab Hn) as (E1 & E2 & E3).
  refine (changed_not_egb stk Lc' FF sp _ b n (Hch _ Hne) Hsp Hstk Hin Hab Hn Hal Hm _).
  rewrite Spec4.AgentLib.u64_lit; [reflexivity|]. unfold SB, AS_HEAPLO in *. lia.
Qed.
(* [comment removed for export] *)

Lemma call_pre_sp : forall R M ret sp stk, call_pre SEGS IA R M ret sp stk -> CEIL + stk <= sp.
Proof. intros R M ret sp stk (_ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma malloc_pre_LG : forall h stk fpc fx R M mdl Lc FF B C K ret n sp,
  malloc_pre SEGS FXOK IA AAINVL h stk fpc fx R M mdl Lc FF B C K ret n sp ->
  malloc_pre SEGS FXOK IA AAINVH h stk fpc fx R M mdl Lc FF B C K ret n sp /\ LG M Lc /\ CEIL + stk <= sp.
Proof.
  intros h stk fpc fx R M mdl Lc FF B C K ret n sp (H1 & H2 & (HA & HL) & H4 & H5 & H6).
  split; [|split; [exact HL | exact (call_pre_sp _ _ _ _ _ H5)]].
  split; [exact H1|]. split; [exact H2|]. split; [exact HA|]. split; [exact H4|]. split; [exact H5 | exact H6].
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma malloc_ok_LG : forall stk R M mdl Lc FF B C K ret n sp c', 0 <= stk -> CEIL + stk <= sp -> 1 <= n -> LG M Lc ->
  malloc_ok SEGS FXOK IA AAINVH stk R M mdl Lc FF B C K ret n sp c' -> malloc_ok SEGS FXOK IA AAINVL stk R M mdl Lc FF B C K ret n sp c'.
Proof.
  intros stk R M mdl Lc FF B C K ret n sp c' Hstk Hsp Hn HL
    (fx' & R' & M' & mdl' & p & Ec & HFX & Hk & Hp & Hal & Hab & Hbig & Hd & Hdf & Hblk & Hz & Hlast & Hshw & Hch & Herr & Hscr & HA & Hvm & Hlz & Hh).
  exists fx', R', M', mdl', p. repeat (split; [assumption|]). split; [|repeat split; assumption].
  split; [exact HA|].
  intros b m [Heq|Hin].
  - (* [comment removed for export] *)
    injection Heq as <- <-. intros Hm. specialize (Hlast Hm). unfold last_gran_ok, sbyte.
    replace (SB + (u p + n) / 8) with (sh_lo (u p) + n / 8) by (unfold sh_lo; lia). rewrite Hlast.
    assert (S : bv_signed (Z_to_bv 8 (n mod 8)) = n mod 8).
    { unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus. rewrite Z_to_bv_unsigned. change (bv_modulus 8) with 256. unfold bv_wrap. change (bv_modulus 8) with 256.
      change (256 `div` 2) with 128. rewrite (Z.mod_small (n mod 8) 256) by lia. rewrite Z.mod_small by lia. lia. }
    rewrite S. lia.
  - (* [comment removed for export] *)
    intros Hm. specialize (HL b m Hin Hm).
    destruct (ZONE None _ _ _ _ _ _ _ b m HA ltac:(right; exact Hin)) as (Hab' & Hn' & Hal').
    destruct (egb_band b m Hab' Hn') as (E1 & E2 & E3).
    unfold last_gran_ok, sbyte in *. fold (egb b m) in HL |- *.
    destruct (decide (M' (Z_to_bv 64 (egb b m)) = M (Z_to_bv 64 (egb b m)))) as [Heq|Hne]; [rewrite Heq; exact HL|]. exfalso.
    refine (changed_not_egb stk Lc FF sp _ b m (Hch _ Hne) Hsp Hstk Hin Hab' Hn' Hal' Hm _).
    rewrite Spec4.AgentLib.u64_lit; [reflexivity|]. unfold SB, AS_HEAPLO in *. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma malloc_null_LG : forall stk R M mdl Lc FF B C K ret n sp c', 0 <= stk -> CEIL + stk <= sp -> LG M Lc ->
  malloc_null SEGS FXOK IA AAINVH stk R M mdl Lc FF B C K ret n sp c' -> malloc_null SEGS FXOK IA AAINVL stk R M mdl Lc FF B C K ret n sp c'.
Proof.
  intros stk R M mdl Lc FF B C K ret n sp c' Hstk Hsp HL (fx' & R' & M' & mdl' & Ec & HFX & Hk & Hp & Hch & Herr & Hscr & HA & Hrest).
  exists fx', R', M', mdl'. repeat (split; [assumption|]). split; [|exact Hrest].
  split; [exact HA|]. exact (LG_changed stk M M' Lc Lc FF FF sp (Some n) B C K mdl' HL (fun x H => H) HA Hch Hsp Hstk).
Qed.

Lemma MALLOC_KATW_LG : forall stk entry fpc, 0 <= stk -> MALLOC_KATW SEGS FXOK IA AAINVH stk entry fpc -> MALLOC_KATW SEGS FXOK IA AAINVL stk entry fpc.
Proof.
  intros stk entry fpc Hstk MK h fx R M mdl Lc FF B C K ret n sp PRE.
  destruct (malloc_pre_LG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as (PRE0 & HL & Hsp).
  assert (Hn : 1 <= n) by (destruct PRE0 as (_ & _ & _ & _ & _ & _ & X & _); lia).
  refine (katwD_conseq SEGS _ _ _ _ _ (MK h fx R M mdl Lc FF B C K ret n sp PRE0) _ _).
  - intros c'. exact (malloc_ok_LG stk R M mdl Lc FF B C K ret n sp c' Hstk Hsp Hn HL).
  - intros c'. exact (malloc_null_LG stk R M mdl Lc FF B C K ret n sp c' Hstk Hsp HL).
Qed.
Lemma MALLOC_ALT_LG : forall stk entry fpc, 0 <= stk -> MALLOC_ALT SEGS FXOK IA AAINVH FRESH stk entry fpc -> MALLOC_ALT SEGS FXOK IA AAINVL FRESH stk entry fpc.
Proof.
  intros stk entry fpc Hstk MK h fx R M mdl Lc FF B C K ret n sp PRE HF.
  destruct (malloc_pre_LG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as (PRE0 & HL & Hsp).
  assert (Hn : 1 <= n) by (destruct PRE0 as (_ & _ & _ & _ & _ & _ & X & _); lia).
  refine (katsD_conseq SEGS _ _ _ _ _ (MK h fx R M mdl Lc FF B C K ret n sp PRE0 HF) _ _).
  - intros c'. exact (malloc_ok_LG stk R M mdl Lc FF B C K ret n sp c' Hstk Hsp Hn HL).
  - intros c'. exact (malloc_null_LG stk R M mdl Lc FF B C K ret n sp c' Hstk Hsp HL).
Qed.

Lemma FREE_KAT_LG : forall stk entry, 0 <= stk -> FREE_KAT SEGS FXOK IA AAINVH stk entry -> FREE_KAT SEGS FXOK IA AAINVL stk entry.
Proof.
  intros stk entry Hstk FK h fx R M mdl Lc Lc' FF B C K B' C' K' ret sp p (H1 & H2 & (HA & HL) & H4 & H5 & H6 & CASES).
  assert (Hsub : forall x, In x Lc' -> In x Lc).
  { destruct CASES as [(_ & -> & _)|(m & L1 & L2 & -> & -> & _)]; intros x Hx; [exact Hx|].
    apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx]. }
  refine (katD_conseq SEGS _ _ _ (FK h fx R M mdl Lc Lc' FF B C K B' C' K' ret sp p ltac:(repeat (split; [assumption|]); assumption)) _).
  intros c' (fx' & R' & M' & mdl' & Ec & HFX & Hk & Hch & Herr & Hscr & HA' & Hrest).
  exists fx', R', M', mdl'. repeat (split; [assumption|]). split; [|exact Hrest].
  split; [exact HA'|]. exact (LG_changed stk M M' Lc Lc' FF FF sp h B' C' K' mdl' HL Hsub HA' Hch (call_pre_sp _ _ _ _ _ H4) Hstk).
Qed.

Lemma STKMAL_LG : forall k, STKMAL SEGS FXOK IA AAINVH fsbase k -> STKMAL SEGS FXOK IA AAINVL fsbase k.
Proof.
  intros k SK h fx R M mdl Lc FF B C K ret sp (H0 & H1 & H2 & (HA & HL) & H4 & H5).
  refine (katD_conseq SEGS _ _ _ (SK h fx R M mdl Lc FF B C K ret sp ltac:(repeat (split; [assumption|]); assumption)) _).
  intros c' (fx' & R' & M' & mdl' & f & flag & Ec & HFX & Hk & Hf & Hal & Hab & Hf1 & Hf2 & Hd & Hdf & Hblk & Hflag & Hz & Hshw & Hch & Herr & Hscr & HA' & Hrest).
  exists fx', R', M', mdl', f, flag. repeat (split; [assumption|]). split; [|exact Hrest].
  split; [exact HA'|]. exact (LG_changed MSTK_F M M' Lc Lc FF ((u f, k) :: FF) sp h B C K mdl' HL (fun x H => H) HA' Hch (call_pre_sp _ _ _ _ _ H4) ltac:(unfold MSTK_F; lia)).
Qed.
(* [comment removed for export] *)
Lemma LG_offband : forall M M' Lc FF h B C K mdl (P : word -> Prop),
  LG M Lc -> AAINVH h Lc FF B C K M' mdl ->
  (forall a : word, M' a <> M a -> P a) ->
  (forall a : word, P a -> u a < SB \/ AS_HEAPLO <= u a) ->
  LG M' Lc.
Proof.
  intros M M' Lc FF h B C K mdl P HL HA Hch HP.
  apply (LG_kept M M' Lc Lc HL (fun x H => H)). intros b n Hin Hm.
  destruct (ZONE h _ _ _ _ _ _ _ b n HA Hin) as (Hab & Hn & Hal).
  destruct (egb_band b n Hab Hn) as (E1 & E2 & E3).
  destruct (decide (M' (Z_to_bv 64 (egb b n)) = M (Z_to_bv 64 (egb b n)))) as [Heq|Hne]; [exact Heq|]. exfalso.
  pose proof (HP _ (Hch _ Hne)) as X. rewrite Spec4.AgentLib.u64_lit in X by (unfold SB, AS_HEAPLO in *; lia). lia.
Qed.

Lemma mem_post_LG : forall h R M mdl Lc FF B C K ret sp dst n bytes c',
  LG M Lc -> CEIL + MSTK_M <= sp -> 0 <= n <= NMAX -> addr_is_mem dst -> addr_is_mem (dst + n) ->
  mem_post SEGS FXOK AAINVH h R M mdl Lc FF B C K ret sp dst n bytes c' -> mem_post SEGS FXOK AAINVL h R M mdl Lc FF B C K ret sp dst n bytes c'.
Proof.
  intros h R M mdl Lc FF B C K ret sp dst n bytes c' HL Hsp Hn Hd1 Hd2 (fx' & R' & M' & mdl' & Ec & HFX & Hk & Ha0 & Hby & Hch & Hscr & HA & Hmat).
  exists fx', R', M', mdl'. repeat (split; [assumption|]). split; [|exact Hmat]. split; [exact HA|].
  apply (LG_offband M M' Lc FF h B C K mdl' (fun a => (dst <= u a < dst + n) \/ (sp - MSTK_M <= u a < sp)) HL HA Hch).
  intros a [Ha|Ha].
  - unfold addr_is_mem, NMAX, SB, AS_HEAPLO, PTRHI in *. lia.
  - right. pose proof ceil_rng. unfold AS_HEAPLO, MSTK_M in *. lia.
Qed.

Lemma MEMCPY_LG : forall entry, MEMCPY_AT SEGS FXOK IA AAINVH entry -> MEMCPY_AT SEGS FXOK IA AAINVL entry.
Proof.
  intros entry MC h fx R M mdl Lc FF W B C K ret sp dst src n bs HFX Hh (HA & HL) Hpre R10 R11 R12 Hn Hov D1 D2 S1 S2 A1 A2 V1 V2 Hrd Hown O1 O2 Hst.
  refine (katD_conseq SEGS _ _ _ (MC h fx R M mdl Lc FF W B C K ret sp dst src n bs HFX Hh HA Hpre R10 R11 R12 Hn Hov D1 D2 S1 S2 A1 A2 V1 V2 Hrd Hown O1 O2 Hst) _).
  intros c'. exact (mem_post_LG h R M mdl Lc FF B C K ret sp dst n _ c' HL (call_pre_sp _ _ _ _ _ Hpre) Hn D1 D2).
Qed.
Lemma MEMSET_LG : forall entry, MEMSET_AT SEGS FXOK IA AAINVH entry -> MEMSET_AT SEGS FXOK IA AAINVL entry.
Proof.
  intros entry MC h fx R M mdl Lc FF W B C K ret sp dst c n HFX Hh (HA & HL) Hpre R10 R11 R12 Hn D1 D2 A2 V2 Hown O1 Hst.
  refine (katD_conseq SEGS _ _ _ (MC h fx R M mdl Lc FF W B C K ret sp dst c n HFX Hh HA Hpre R10 R11 R12 Hn D1 D2 A2 V2 Hown O1 Hst) _).
  intros c'. exact (mem_post_LG h R M mdl Lc FF B C K ret sp dst n _ c' HL (call_pre_sp _ _ _ _ _ Hpre) Hn D1 D2).
Qed.
Lemma MEMMOVE_LG : forall entry, MEMMOVE_AT SEGS FXOK IA AAINVH entry -> MEMMOVE_AT SEGS FXOK IA AAINVL entry.
Proof.
  intros entry MC h fx R M mdl Lc FF W B C K ret sp dst src n bs HFX Hh (HA & HL) Hpre R10 R11 R12 Hn D1 D2 S1 S2 A1 A2 V1 V2 Hrd Hsame Hown O1 O2 Hst.
  refine (katD_conseq SEGS _ _ _ (MC h fx R M mdl Lc FF W B C K ret sp dst src n bs HFX Hh HA Hpre R10 R11 R12 Hn D1 D2 S1 S2 A1 A2 V1 V2 Hrd Hsame Hown O1 O2 Hst) _).
  intros c'. exact (mem_post_LG h R M mdl Lc FF B C K ret sp dst n _ c' HL (call_pre_sp _ _ _ _ _ Hpre) Hn D1 D2).
Qed.
Lemma STRLEN_LG : forall entry, STRLEN_AT SEGS FXOK IA AAINVH entry -> STRLEN_AT SEGS FXOK IA AAINVL entry.
Proof.
  intros entry MC h fx R M mdl Lc FF B C K ret sp s0 len HFX Hh (HA & HL) Hpre R10 L0 L1 BY NUL HULL M1 M2 ACC SHV SC.
  refine (katD_conseq SEGS _ _ _ (MC h fx R M mdl Lc FF B C K ret sp s0 len HFX Hh HA Hpre R10 L0 L1 BY NUL HULL M1 M2 ACC SHV SC) _).
  intros c' (fx' & R' & M' & mdl' & Ec & HFX' & Hk & Ha0 & Hch & Hscr & HA' & Hmat).
  exists fx', R', M', mdl'. repeat (split; [assumption|]). split; [|exact Hmat]. split; [exact HA'|].
  apply (LG_offband M M' Lc FF h B C K mdl' (fun a => sp - MSTK_M <= u a < sp) HL HA' Hch).
  intros a Ha. right. pose proof ceil_rng. pose proof (call_pre_sp _ _ _ _ _ Hpre). unfold AS_HEAPLO, MSTK_M in *. lia.
Qed.

Lemma FAKEREL_LG : FAKEREL SEGS FXOK IA AAINVH -> FAKEREL SEGS FXOK IA AAINVL.
Proof.
  intros FR h pc rs fx R M mdl Lc FF F1 F2 B C K f k flag HFX Hh (HA & HL) HFF Hfl Hfetch Hrs Hr Hpc0 Hpc4.
  refine (katD_conseq SEGS _ _ _ (FR h pc rs fx R M mdl Lc FF F1 F2 B C K f k flag HFX Hh HA HFF Hfl Hfetch Hrs Hr Hpc0 Hpc4) _).
  intros c' (M' & mdl' & Ec & Hch & HA' & Hmat). exists M', mdl'. split; [exact Ec|]. split; [exact Hch|]. split; [|exact Hmat].
  split; [exact HA'|].
  apply (LG_kept M M' Lc Lc HL (fun x H => H)). intros b n Hin Hm.
  destruct (ZONE h _ _ _ _ _ _ _ b n HA' Hin) as (Hab & Hn & Hal).
  destruct (egb_band b n Hab Hn) as (E1 & E2 & E3).
  destruct (decide (M' (Z_to_bv 64 (egb b n)) = M (Z_to_bv 64 (egb b n)))) as [Heq|Hne]; [exact Heq|]. exfalso.
  destruct (Hch _ Hne) as (Hua & _ & _ & Hnv). rewrite Spec4.AgentLib.u64_lit in Hua by (unfold SB, AS_HEAPLO in *; lia).
  apply Hnv. right; right; left. exists b, n. split; [exact Hin|]. rewrite <- Hua.
  destruct Hab as (A1 & _). unfold PTRLO in A1. exact (egb_in_shadow b n Hm Hal ltac:(lia) ltac:(lia)).
Qed.

(* [comment removed for export] *)
Lemma FREE_KAT_N_LG : forall stk entry, 0 <= stk -> FREE_KAT_N SEGS FXOK IA AAINVH stk entry -> FREE_KAT_N SEGS FXOK IA AAINVL stk entry.
Proof.
  intros stk entry Hstk FK fx R M mdl Lc Lc' FF B C K B' C' K' ret sp p (H1 & H2 & (HA & HL) & H4 & H5 & H6 & CASES).
  assert (Hsub : forall x, In x Lc' -> In x Lc).
  { destruct CASES as [(_ & -> & _)|(m & L1 & L2 & -> & -> & _)]; intros x Hx; [exact Hx|].
    apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx]. }
  refine (katD_conseq SEGS _ _ _ (FK fx R M mdl Lc Lc' FF B C K B' C' K' ret sp p ltac:(repeat (split; [assumption|]); assumption)) _).
  intros c' (fx' & R' & M' & mdl' & Ec & HFX & Hk & Hch & Herr & Hscr & HA' & Hrest).
  exists fx', R', M', mdl'. repeat (split; [assumption|]). split; [|exact Hrest].
  split; [exact HA'|]. exact (LG_changed stk M M' Lc Lc' FF FF sp None B' C' K' mdl' HL Hsub HA' Hch (call_pre_sp _ _ _ _ _ H4) Hstk).
Qed.
Theorem as_contracts_n_LG : as_contracts_n SEGS FXOK IA AAINVH FRESH fsbase -> as_contracts_n SEGS FXOK IA AAINVL FRESH fsbase.
Proof.
  intros [Wk Mk Mkt Ma Mat Fr Frt Od Ods Sk Frl Mc Amc Ms Ams Mm Amm Sl].
  assert (HA : 0 <= MSTK_A) by (unfold MSTK_A; lia).
  constructor.
  - intros h Lc FF B C K M mdl (H & HL). split; [exact (Wk h _ _ _ _ _ _ _ H) | exact HL].
  - exact (MALLOC_KATW_LG _ _ _ HA Mk).
  - exact (MALLOC_KATW_LG _ _ _ HA Mkt).
  - exact (MALLOC_ALT_LG _ _ _ HA Ma).
  - exact (MALLOC_ALT_LG _ _ _ HA Mat).
  - exact (FREE_KAT_N_LG _ _ HA Fr).
  - exact (FREE_KAT_N_LG _ _ HA Frt).
  - exact (FREE_KAT_N_LG _ _ HA Od).
  - exact (FREE_KAT_N_LG _ _ HA Ods).
  - intros k Hk. exact (STKMAL_LG k (Sk k Hk)).
  - exact (FAKEREL_LG Frl).
  - exact (MEMCPY_LG _ Mc).
  - exact (MEMCPY_LG _ Amc).
  - exact (MEMSET_LG _ Ms).
  - exact (MEMSET_LG _ Ams).
  - exact (MEMMOVE_LG _ Mm).
  - exact (MEMMOVE_LG _ Amm).
  - exact (STRLEN_LG _ Sl).
Qed.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma hull_apart : forall b n b' n', b mod 16 = 0 -> b' mod 16 = 0 -> 0 <= b -> 0 <= b' -> 1 <= n -> 1 <= n' ->
  (b + n <= b' \/ b' + n' <= b) -> n' mod 8 <> 0 -> ~ (sh_lo b <= egb b' n' < sh_hi b n).
Proof. intros b n b' n' A1 A2 B1 B2 N1 N2 D Hm. unfold sh_lo, sh_hi, egb. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Theorem annotate_LG : forall entry, ANNOTATE_AT SEGS FXOK IA AAINVH entry -> ANNOTATE_ATW SEGS FXOK IA AAINVL entry.
Proof.
  intros entry AN h fx R M mdl Lc FF B C K ret sp beg n om nm HFX Hh (HA & HL) Hpre Hin R10 R11 R12 R13 Hom Hnm Hacc.
  refine (katD_conseq SEGS _ _ _ (AN h fx R M mdl Lc FF B C K ret sp beg n om nm HFX Hh HA Hpre Hin R10 R11 R12 R13 Hom Hnm Hacc (HL beg n Hin)) _).
  intros c' (fx' & R' & M' & mdl' & Ec & HFX' & Hk & Hacc' & Hlg' & Hch & Hdef & Hscr & HA' & Hrest).
  exists fx', R', M', mdl'. repeat (split; [assumption|]). split; [|exact Hrest]. split; [exact HA'|].
  intros b m Hinb. destruct (Z.eq_dec b beg) as [Eb|Hnb]; [destruct (Z.eq_dec m n) as [Em|Hnm']; [subst b m; exact Hlg'|]|].
  all: intros Hm; specialize (HL b m Hinb Hm); unfold last_gran_ok, sbyte in HL |- *; fold (egb b m) in HL |- *.
  all: destruct (ZONE h _ _ _ _ _ _ _ b m HA' Hinb) as (Hab & Hn' & Hal);
       destruct (ZONE h _ _ _ _ _ _ _ beg n HA' Hin) as (Habg & Hng & Halg);
       destruct (egb_band b m Hab Hn') as (E1 & E2 & E3);
       (destruct (decide (M' (Z_to_bv 64 (egb b m)) = M (Z_to_bv 64 (egb b m)))) as [Heq|Hne]; [rewrite Heq; exact HL|]); exfalso;
       destruct (in_split _ _ Hin) as (L1 & L2 & HLc);
       (assert (Hin' : In (b, m) (L1 ++ L2));
        [rewrite HLc in Hinb; apply in_app_iff in Hinb as [X|[X|X]]; [apply in_app_iff; left; exact X | injection X as X1 X2; lia | apply in_app_iff; right; exact X]|]);
       pose proof (DISJ h _ _ _ _ _ _ _ L1 L2 beg n b m HA' HLc Hin') as DJ;
       (destruct (Hch _ Hne) as [X|X]; rewrite Spec4.AgentLib.u64_lit in X by (unfold SB, AS_HEAPLO in *; lia));
       [ destruct Hab as (P1 & _); destruct Habg as (P1g & _); unfold PTRLO in *;
         apply (hull_apart beg n b m Halg Hal ltac:(lia) ltac:(lia) Hng Hn' DJ Hm); unfold sh_lo;
         assert (beg / 8 <= Z.min om nm / 8) by (apply Z.div_le_mono; lia); lia
       | pose proof ceil_rng; pose proof (call_pre_sp _ _ _ _ _ Hpre); unfold MSTK_C in *; lia ].
Qed.
End LG.
