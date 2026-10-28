(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5CBR.
Import L5A. Import L5CA. Import L5CSA. Import L5SAR.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ffrk (k : Z) (FF LK : list fframe) (d : Z) : Prop := Z.of_nat (ff_count k (FF ++ LK)) + d <= ff_cap k.
Lemma ffrk_1 FF LK d : ffrk 1 FF LK d <-> ffr FF LK d. Proof. reflexivity. Qed.
Lemma ffrk_room k FF LK d : ffrk k FF LK d -> 2 <= d -> ff_room k FF LK. Proof. unfold ffrk, ff_room. lia. Qed.
Lemma ffrk_le k FF LK d d' : ffrk k FF LK d -> d' <= d -> ffrk k FF LK d'. Proof. unfold ffrk. lia. Qed.
Lemma ff_count_cons_other k f l : ff_class f <> k -> ff_count k (f :: l) = ff_count k l.
Proof.
  intros N. unfold ff_count. rewrite list_basics.list.filter_cons. destruct (decide _) as [E|E]; [|reflexivity].
  exfalso. apply N. apply Z.eqb_eq. destruct (ff_class f =? k); [reflexivity | exact (False_ind _ (E))].
Qed.
Lemma ffrk_push k FF LK LK' (f : fframe) d d' :
  ffrk k FF LK d -> incl LK' LK -> NoDup (map ff_addr ((f :: FF) ++ LK')) -> d' + 1 <= d -> ffrk k (f :: FF) LK' d'.
Proof.
  unfold ffrk. intros R I ND Hd. rewrite ff_count_app in R. change ((f :: FF) ++ LK') with (f :: (FF ++ LK')).
  pose proof (ff_count_cons k f (FF ++ LK')) as C1. rewrite ff_count_app in C1.
  pose proof (ff_count_incl k LK' LK I (nodup_of_map_app_r (f :: FF) LK' ND)) as C2. lia.
Qed.
Lemma ffrk_push_other k FF LK LK' (f : fframe) d :
  ff_class f <> k -> ffrk k FF LK d -> incl LK' LK -> NoDup (map ff_addr ((f :: FF) ++ LK')) -> ffrk k (f :: FF) LK' d.
Proof.
  unfold ffrk. intros N R I ND. rewrite ff_count_app in R. change ((f :: FF) ++ LK') with (f :: (FF ++ LK')).
  rewrite (ff_count_cons_other k f _ N), ff_count_app.
  pose proof (ff_count_incl k LK' LK I (nodup_of_map_app_r (f :: FF) LK' ND)) as C2. lia.
Qed.
Lemma ffrk_shrink k FF LK LK' d : ffrk k FF LK d -> incl LK' LK -> NoDup (map ff_addr (FF ++ LK')) -> ffrk k FF LK' d.
Proof.
  unfold ffrk. intros R I ND. rewrite ff_count_app in *. pose proof (ff_count_incl k LK' LK I (nodup_of_map_app_r FF LK' ND)) as C2. lia.
Qed.
Lemma ffrk_pop k FF LK (f : fframe) d : ffrk k (f :: FF) LK d -> ffrk k FF LK d.
Proof. unfold ffrk. change ((f :: FF) ++ LK) with (f :: (FF ++ LK)). intros H. unfold ff_count in *. rewrite list_basics.list.filter_cons in H. destruct (decide _); cbn [length] in H; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record as0_layout2 (L : asan_layout) : Prop := ALY2 {
  aly2_static_lo : forall a, hl_rt_static L a -> 0x139000 <= a;
  aly2_cost : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_lin L /\ 0 <= hl_b_overhead L      (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Lemma as0_layout2_of L C : L5A.as0_layout L C -> as0_layout2 L.
Proof. intros LY. split. exact (L5A.aly_static_lo L C LY). exact (L5A.aly_cost L C LY). Qed.

(* [comment removed for export] *)
Lemma credit_le_refl c : credit_le c c. Proof. unfold credit_le. lia. Qed.
Lemma credit_le_trans a b c : credit_le a b -> credit_le b c -> credit_le a c. Proof. unfold credit_le. lia. Qed.
Lemma adebit_le L c n : as0_layout2 L -> 0 <= n -> credit_le (adebit L c n) c.
Proof. intros [_ (K & B & O)] Hn. unfold credit_le, adebit. cbn [fst snd]. nia. Qed.
Lemma adebit_mono L c c' n : credit_le c c' -> credit_le (adebit L c n) (adebit L c' n).
Proof. unfold credit_le, adebit. cbn [fst snd]. lia. Qed.
Lemma adebit_le_amount L c n n' : as0_layout2 L -> n' <= n -> credit_le (adebit L c n) (adebit L c n').
Proof. intros [_ (K & B & O)] Hn. unfold credit_le, adebit. cbn [fst snd]. nia. Qed.
Lemma acredit_ok_le L c n n' : as0_layout2 L -> acredit_ok L c n -> n' <= n -> acredit_ok L c n'.
Proof. intros [_ (K & B & O)] [H1 H2] Hn. unfold acredit_ok. split. exact H1. nia. Qed.
Lemma acredit_ok_mono L c c' n : acredit_ok L c n -> credit_le c c' -> acredit_ok L c' n.
Proof. unfold acredit_ok, credit_le. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition asrc (IL : icpt_layout) (LB : list (Z * Z)) (FF : list fframe) (M : word -> option byte) (p m : Z) : Prop :=
  m = 0
  \/ (exists b n, In (b, n) LB /\ b <= p /\ p + m <= b + n)
  \/ (exists g n, In (g, n) (icl_globals IL) /\ g <= p /\ p + m <= g + n)
  \/ (exists so, aobj FF so 24 /\ so <= p /\ p + m <= so + 24 /\ shadow_zero M so 3).

Lemma asrc_sub IL LB FF M p m p' m' : asrc IL LB FF M p m -> p <= p' -> p' + m' <= p + m -> 0 <= m' -> asrc IL LB FF M p' m'.
Proof.
  intros [E|[(b & n & I & H1 & H2)|[(g & n & I & H1 & H2)|(so & AO & H1 & H2 & SZ)]]] Hp Hm Hm0.
  - left. lia.
  - right; left. exists b, n. split. exact I. lia.
  - right; right; left. exists g, n. split. exact I. lia.
  - right; right; right. exists so. split. exact AO. split. lia. split. lia. exact SZ.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma aacc_of_blk M u n p m : shadow_blk M u n -> u mod 8 = 0 -> 0 <= u -> u <= p -> p + m <= u + n -> aacc M p m.
Proof.
  intros [SZ SP] U8 U0 H1 H2 a Ha. unfold shadow_zero, byte_at in SZ, SP |- *.
  assert (E : S a = S u + (a / 8 - u / 8)) by (unfold S; lia).
  destruct (Z_lt_le_dec (a / 8 - u / 8) (n / 8)) as [LT|GE].
  - left. rewrite E. apply SZ. lia.
  - right. exists (n mod 8). assert (NZ : n mod 8 <> 0) by lia. assert (G : a / 8 - u / 8 = n / 8) by lia.
    split. rewrite E, G. apply SP. exact NZ. lia.
Qed.
Lemma aacc_of_zero M u g p m : shadow_zero M u g -> u mod 8 = 0 -> 0 <= u -> u <= p -> p + m <= u + 8 * g -> aacc M p m.
Proof.
  intros SZ U8 U0 H1 H2 a Ha. left. unfold shadow_zero, byte_at in SZ |- *.
  replace (S a) with (S u + (a / 8 - u / 8)) by (unfold S; lia). apply SZ. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma aacc_sub M p m p' m' : aacc M p m -> p <= p' -> p' + m' <= p + m -> aacc M p' m'.
Proof. intros H Hp Hm a Ha. apply H. lia. Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis LY2 : as0_layout2 L.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.

(* [comment removed for export] *)
Lemma img_client LB FF sp scr a : 0x10000 <= a < 0x139000 -> aclient L ar LB FF sp scr a.
Proof.
  intros Ha. right; right; left. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY). split. lia.
  intros X. pose proof (aly2_static_lo L LY2 a X). lia.
Qed.

Lemma globals_facts : forall g n, In (g, n) (icl_globals IL) -> 0x10000 <= g /\ g + n <= 0x139000 /\ g mod 8 = 0 /\ 0 < n.
Proof.
  rewrite (aicl_globals IL ILY). intros g n Hin. cbn [In] in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; repeat split; first [reflexivity | lia] |]). destruct Hin.
Qed.

(* [comment removed for export] *)

Lemma asrc_client LB FF M sp scr p m i : asrc IL LB FF M p m -> 0 <= i < m -> aclient L ar LB FF sp scr (p + i).
Proof.
  intros [E|[(b & n & I & H1 & H2)|[(g & n & I & H1 & H2)|(so & AO & H1 & H2 & SZ)]]] Hi.
  - lia.
  - apply (block_client L ar LB FF sp scr b n). exact I. lia.
  - pose proof (globals_facts g n I) as (G0 & G1 & _). apply img_client. lia.
  - apply (obj_client L ar LB FF sp scr so 24). exact AO. lia.
Qed.

(* [comment removed for export] *)
Lemma asrc_vis LB FF LK cr A M model p m : ri_inv HI LB FF LK cr A M (vml_of model) -> asrc IL LB FF M p m -> avis (ahid A model) p m.
Proof.
  intros HH SRC. pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (_ & _ & VIMG & _ & VBLK & _).
  destruct SRC as [E|[(b & n & I & H1 & H2)|[(g & n & I & H1 & H2)|(so & AO & H1 & H2 & SZ)]]].
  - intros i Hi. lia.
  - apply (VBLK b n p m I H1 H2).
  - pose proof (globals_facts g n I) as (G0 & G1 & _). apply VIMG. lia. lia.
  - pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model so 24 0 0 HH AO ltac:(lia) ltac:(reflexivity)) as (_ & _ & _ & OVIS & _).
    eapply avis_sub. exact OVIS. exact H1. exact H2.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma asrc_shadow_vis LB FF LK cr A M model p m a :
  ri_inv HI LB FF LK cr A M (vml_of model) -> asrc IL LB FF M p m -> p <= a < p + m -> ahid A model (Z_to_bv 64 (S a)) = false.
Proof.
  intros HH SRC Ha. pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (_ & _ & _ & _ & _ & VBSH & _).
  destruct SRC as [E|[(b & n & I & H1 & H2)|[(g & n & I & H1 & H2)|(so & AO & H1 & H2 & SZ)]]].
  - lia.
  - replace (S a) with (S a + 0) by lia. apply (VBSH b n (S a) 1 I). 2: lia. intros i Hi. unfold in_shadow_of, S.
    pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _). pose proof (WB _ I) as ((B0 & _ & B2 & _) & _). cbn [fst snd] in *. lia.
  - pose proof (aic_globals _ _ _ _ _ ICok _ _ _ _ _ _ _ HH) as G. rewrite Forall_forall in G. pose proof (G _ I) as [_ GAL]. cbn [fst snd] in GAL.
    pose proof (globals_facts g n I) as (G0 & _ & G8 & _).
    replace (S a) with (S a + 0) by lia. apply (avis_of_shadow_allowed A model g n (S a) 1 GAL). 2: lia. intros i Hi. unfold in_shadow_of, S. lia.
  - pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model so 24 0 0 HH AO ltac:(lia) ltac:(reflexivity)) as ((_ & _ & _ & O8 & _) & _ & _ & _ & OVSH & _).
    change (24 / 8) with 3 in OVSH. replace (S a) with (so / 8 + SB + (a / 8 - so / 8)) by (unfold S; lia). apply OVSH. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma asrc_range LB FF LK cr A M V p m : ri_inv HI LB FF LK cr A M V -> asrc IL LB FF M p m -> 0 < m -> 4096 <= p /\ p + m <= ahl_ceil ar.
Proof.
  intros HH SRC Hm. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & SB1 & _ & TOP & _).
  destruct SRC as [E|[(b & n & I & H1 & H2)|[(g & n & I & H1 & H2)|(so & AO & H1 & H2 & SZ)]]].
  - lia.
  - pose proof (WB _ I) as ((B0 & _ & _ & _ & B4 & _) & _). cbn [fst snd] in *. lia.
  - pose proof (globals_facts g n I) as (G0 & G1 & _). rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in FSIMG. unfold app_mem, FS_BYTES in *.
    assert (0x696000 <= ahl_ceil ar). { destruct FSIMG as [X|X]; lia. } lia.
  - destruct AO as (f & Hf & O1 & O2 & _). pose proof (WF f Hf) as (Y1 & Y2 & _). unfold app_mem, FS_BYTES in *. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in FSIMG.
    assert (HB : 0 < ff_bytes (ff_class f)). { pose proof (WF f Hf) as (_ & _ & _ & Y4 & _). destruct Y4 as [E|[E|[E|[E|[E|[E|[]]]]]]]; rewrite <- E; reflexivity. }
    lia.
Qed.

(* [comment removed for export] *)
Lemma aacc_vis H M p m : aacc M p m -> (forall a, p <= a < p + m -> H (Z_to_bv 64 (S a)) = false) -> aacc (mrestrict H M) p m.
Proof.
  intros ACC V a Ha. unfold byte_at in *. rewrite (mrestrict_visible H M _ (V a Ha)). exact (ACC a Ha).
Qed.

(* [comment removed for export] *)
Lemma asrc_keep LB LB' FF FF' M M' p m :
  asrc IL LB FF M p m -> incl LB LB' -> incl FF FF' -> (forall so, aobj FF so 24 -> shadow_zero M so 3 -> shadow_zero M' so 3) -> asrc IL LB' FF' M' p m.
Proof.
  intros [E|[(b & n & I & H1 & H2)|[(g & n & I & H1 & H2)|(so & AO & H1 & H2 & SZ)]]] IB IF KEEP.
  - left. exact E.
  - right; left. exists b, n. split. apply IB. exact I. lia.
  - right; right; left. exists g, n. split. exact I. lia.
  - right; right; right. exists so. split. { destruct AO as (f & Hf & X). exists f. split. apply IF. exact Hf. exact X. }
    split. exact H1. split. exact H2. apply KEEP. exact AO. exact SZ.
Qed.

End WithIface.
End SCFG_1.
End L5CBR.
