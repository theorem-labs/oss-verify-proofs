(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull HeapIfaceAEx.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module HAR.

Definition NREQ : Z := 2 ^ 34.
Definition NREQI : Z := 2 ^ 32.

Definition ngrant (n : Z) : Prop := n < 2 ^ 34.
Lemma ngrant_lt : forall n, ngrant n -> n < 2 ^ 34.
Proof. intros n H. exact H. Qed.
Definition NW_LO : Z := 64.
Definition NW_HI : Z := 128.

Record layoutR : Type := LR { hlr_pc_malloc : Z; hlr_pc_free : Z }.

Section Chain.
Variable L : asan_layout.
Variable ar : asan_run.

Definition fvalid (lo fp : Z) : Prop := lo < fp /\ fp < ar_stack_top ar - 16 /\ fp mod 8 = 0.

Inductive rchain (M : word -> option byte) : Z -> Z -> list Z -> Prop :=
| rc_stop : forall lo fp, ~ fvalid lo fp -> rchain M lo fp []
| rc_low  : forall lo fp pc1, fvalid lo fp -> cell_is (hl_segs L) M (fp - 8) 8 pc1 -> 0 <= pc1 < 4096 -> rchain M lo fp []
| rc_cons : forall lo fp ra fp' RC, fvalid lo fp ->
              cell_is (hl_segs L) M (fp - 8) 8 ra -> 4096 <= ra < 2 ^ 64 ->
              cell_is (hl_segs L) M (fp - 16) 8 fp' -> 0 <= fp' < 2 ^ 64 ->
              rchain M fp fp' RC -> rchain M lo fp (ra :: RC).

Definition akey (p0 : Z) (RC : list Z) : list Z := p0 :: firstn 29 (filter (fun x => negb (x =? p0)) RC).

Definition ukey (p0 : Z) (M : word -> option byte) (sp ra s0 : Z) (K : list Z) : Prop :=
  (~ fvalid (ar_stack_bottom ar) sp /\ K = [p0])
  \/ (fvalid (ar_stack_bottom ar) sp /\ 0 <= ra < 4096 /\ K = [p0])
  \/ (fvalid (ar_stack_bottom ar) sp /\ 4096 <= ra < 2 ^ 64 /\ s0 <> sp + 8 /\ exists RC, rchain M sp s0 RC /\ K = akey p0 (ra :: RC)).

Lemma cell_is_agree (M M' : word -> option byte) a v :
  0 <= a -> a + 8 < 2 ^ 64 -> (forall x : word, a <= bv_unsigned x < a + 8 -> M' x = M x) ->
  cell_is (hl_segs L) M a 8 v -> cell_is (hl_segs L) M' a 8 v.
Proof.
  intros Ha Hb AG C. unfold cell_is in *. rewrite <- C. apply rdn_ext.
  - rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by lia. change (Z.of_nat 8) with 8. lia.
  - intros x Hx. apply AG. rewrite Z_to_bv_unsigned in Hx. unfold bv_wrap, bv_modulus in Hx. rewrite Z.mod_small in Hx by lia.
    change (Z.of_nat 8) with 8 in Hx. lia.
Qed.

Lemma fvalid_dec lo fp : {fvalid lo fp} + {~ fvalid lo fp}.
Proof.
  unfold fvalid. destruct (Z_lt_dec lo fp); [|right; tauto]. destruct (Z_lt_dec fp (ar_stack_top ar - 16)); [|right; tauto].
  destruct (Z.eq_dec (fp mod 8) 0); [left; tauto | right; tauto].
Qed.
Lemma fvalid_ge8 lo fp : fvalid lo fp -> 0 <= lo -> 8 <= fp.
Proof.
  intros (V1 & V2 & V3) Hlo. pose proof (Z.div_mod fp 8 ltac:(lia)) as D. rewrite V3 in D. lia.
Qed.

Lemma rchain_frame (M M' : word -> option byte) lo fp RC :
  rchain M lo fp RC -> 16 <= lo -> ar_stack_top ar < 2 ^ 64 ->
  (forall x : word, fp - 16 <= bv_unsigned x < ar_stack_top ar -> M' x = M x) ->
  rchain M' lo fp RC.
Proof.
  intros H. induction H as [lo fp NV | lo fp pc1 V C P | lo fp ra fp' RC V C1 R1 C2 R2 H IH]; intros Hlo Htop AG.
  - apply rc_stop. exact NV.
  - pose proof V as (V1 & V2 & V3). apply (rc_low M' lo fp pc1); [exact V | | exact P].
    apply (cell_is_agree M M'); [lia | lia | | exact C]. intros x Hx. apply AG. lia.
  - pose proof V as (V1 & V2 & V3).
    apply (rc_cons M' lo fp ra fp' RC); [exact V | | exact R1 | | exact R2 | ].
    + apply (cell_is_agree M M'); [lia | lia | | exact C1]. intros x Hx. apply AG. lia.
    + apply (cell_is_agree M M'); [lia | lia | | exact C2]. intros x Hx. apply AG. lia.
    + destruct (fvalid_dec fp fp') as [V'|NV'].
      * apply IH; [lia | exact Htop |]. intros x Hx. apply AG. destruct V' as (W1 & W2 & W3). lia.
      * inversion H; subst; try contradiction. apply rc_stop. exact NV'.
Qed.

Lemma rchain_frame_sp (M M' : word -> option byte) lo fp RC :
  rchain M lo fp RC -> 16 <= lo -> lo mod 8 = 0 -> fp <> lo + 8 -> ar_stack_top ar < 2 ^ 64 ->
  (forall x : word, lo <= bv_unsigned x < ar_stack_top ar -> M' x = M x) ->
  rchain M' lo fp RC.
Proof.
  intros H Hlo Hlo8 Hne Htop AG.
  destruct (fvalid_dec lo fp) as [V'|NV'].
  - apply (rchain_frame M M' lo fp RC); [exact H | exact Hlo | exact Htop |]. intros x Hx. apply AG. destruct V' as (W1 & W2 & W3).
    pose proof (Z.div_mod fp 8 ltac:(lia)) as D1. pose proof (Z.div_mod lo 8 ltac:(lia)) as D2. rewrite W3 in D1. rewrite Hlo8 in D2. lia.
  - inversion H; subst; try contradiction. apply rc_stop. exact NV'.
Qed.

Lemma rchain_total (M : word -> option byte) :
  (forall a, 0 <= a -> a + 8 <= ar_stack_top ar -> exists v, 0 <= v < 2 ^ 64 /\ cell_is (hl_segs L) M a 8 v) ->
  forall (k : nat) lo fp, 16 <= lo -> ar_stack_top ar - fp <= Z.of_nat k -> exists RC, rchain M lo fp RC.
Proof.
  intros RD k. induction k as [|k IH]; intros lo fp Hlo Hk.
  - exists []. apply rc_stop. intros (V1 & V2 & V3). lia.
  - destruct (fvalid_dec lo fp) as [V|NV]; [|exists []; apply rc_stop; exact NV].
    pose proof V as (V1 & V2 & V3).
    destruct (RD (fp - 8) ltac:(lia) ltac:(lia)) as (ra & Rra & Cra).
    destruct (Z_lt_dec ra 4096) as [Lo|Hi]; [exists []; apply (rc_low M lo fp ra V Cra); lia|].
    destruct (RD (fp - 16) ltac:(lia) ltac:(lia)) as (fp' & Rfp & Cfp).
    assert (X : exists RC, rchain M fp fp' RC).
    { destruct (fvalid_dec fp fp') as [V'|NV']; [|exists []; apply rc_stop; exact NV'].
      apply IH; [lia|]. destruct V' as (W1 & W2 & W3). rewrite Nat2Z.inj_succ in Hk. lia. }
    destruct X as (RC & H).
    exists (ra :: RC). apply (rc_cons M lo fp ra fp' RC V Cra ltac:(lia) Cfp Rfp H).
Qed.

Lemma rchain_push (M : word -> option byte) lo fp ra s0 RC :
  fvalid lo fp -> cell_is (hl_segs L) M (fp - 8) 8 ra -> 4096 <= ra < 2 ^ 64 ->
  cell_is (hl_segs L) M (fp - 16) 8 s0 -> 0 <= s0 < 2 ^ 64 ->
  rchain M fp s0 RC -> rchain M lo fp (ra :: RC).
Proof. intros. eapply rc_cons; eassumption. Qed.

Lemma rchain_lo (M : word -> option byte) lo lo' fp RC :
  rchain M lo fp RC -> fvalid lo fp -> lo' < fp -> rchain M lo' fp RC.
Proof.
  intros H V Hlo. assert (V' : fvalid lo' fp) by (destruct V as (_ & V2 & V3); repeat split; assumption).
  inversion H; subst.
  - contradiction.
  - eapply rc_low; eassumption.
  - eapply rc_cons; eassumption.
Qed.

Lemma ukey_frame p0 (M M' : word -> option byte) sp ra s0 K :
  ukey p0 M sp ra s0 K -> 16 <= sp -> sp mod 8 = 0 -> ar_stack_top ar < 2 ^ 64 ->
  (forall x : word, sp <= bv_unsigned x < ar_stack_top ar -> M' x = M x) ->
  ukey p0 M' sp ra s0 K.
Proof.
  intros [U | [U | (V & Hra & Hne & RC & H & E)]] Hsp Hsp8 Htop AG; [left; exact U | right; left; exact U |].
  right; right. split; [exact V|]. split; [exact Hra|]. split; [exact Hne|]. exists RC. split; [|exact E].
  destruct (fvalid_dec sp s0) as [V'|NV'].
  - apply (rchain_frame M M' sp s0 RC); [exact H | exact Hsp | exact Htop |]. intros x Hx. apply AG. destruct V' as (W1 & W2 & W3).
    pose proof (Z.div_mod s0 8 ltac:(lia)) as D1. pose proof (Z.div_mod sp 8 ltac:(lia)) as D2. rewrite W3 in D1. rewrite Hsp8 in D2. lia.
  - inversion H; subst; try contradiction. apply rc_stop. exact NV'.
Qed.

Lemma ukey_intro p0 (M : word -> option byte) sp ra s0 RC :
  fvalid (ar_stack_bottom ar) sp -> 4096 <= ra < 2 ^ 64 -> s0 <> sp + 8 -> rchain M sp s0 RC -> ukey p0 M sp ra s0 (akey p0 (ra :: RC)).
Proof. intros V Hra Hne H. right; right. split; [exact V|]. split; [exact Hra|]. split; [exact Hne|]. exists RC. split; [exact H | reflexivity]. Qed.
End Chain.

Section Fam.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable scfg : SpuriousCfg.
Variable LR_ : layoutR.
Variable HIk : list (list Z) -> asan_iface.

Let cfg_at (fx : FPState) (R : bvmap 5 word) (pc : word) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R pc M (seg_rom (hl_segs L))) model.

Definition amalloc_postG (Dp : list (list Z)) (crp : credit) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (n : Z) (K : ShapeAlg.TSet) : Prop :=
  forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)) (u : Z),
    ngrant n ->
    getr R' 10%bv = Z_to_bv 64 u ->
    regs_preserved R R' ->
    ablock_range L ar u n -> blocks_apart u n LB -> fframes_apart u n (FF ++ LK) ->
    defined M' u n -> shadow_blk M' u n ->
    aheap_pres L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_malloc L) M M' ->
    model_rt model model' -> incl A A' -> MInv A' model' ->
    ri_inv (HIk Dp) ((u, n) :: LB) FF LK crp A' M' (vml_of model') ->
    srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K.
Definition afree_postG (Dp : list (list Z)) (crp : credit) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (u : Z) (K : ShapeAlg.TSet) : Prop :=
  forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)),
    regs_preserved R R' ->
    aheap_pres L ar (lb_remove u LB) FF (bv_unsigned (getr R 2%bv)) (hl_scr_free L) M M' ->
    model_rt model model' -> incl A A' -> MInv A' model' ->
    ri_inv (HIk Dp) (lb_remove u LB) FF LK crp A' M' (vml_of model') ->
    srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K.

Definition amalloc_preG (D : list (list Z)) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (n : Z) (K : ShapeAlg.TSet) : Prop :=
  ri_inv (HIk D) LB FF LK cr A M (vml_of model) /\ m_halted model = None /\ MInv A model /\
  getr R 10%bv = Z_to_bv 64 n /\
  getr R 4%bv = Z_to_bv 64 (hl_tp L) /\ Hoare.ret_ok (getr R 1%bv) /\
  astack_ok L ar M (hl_scr_malloc L) (bv_unsigned (getr R 2%bv)) /\
  K [].
Definition afree_preG (D : list (list Z)) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (u n : Z) (K : ShapeAlg.TSet) : Prop :=
  ri_inv (HIk D) LB FF LK cr A M (vml_of model) /\ m_halted model = None /\ MInv A model /\
  In (u, n) LB /\ getr R 10%bv = Z_to_bv 64 u /\
  getr R 4%bv = Z_to_bv 64 (hl_tp L) /\ Hoare.ret_ok (getr R 1%bv) /\
  astack_ok L ar M (hl_scr_free L) (bv_unsigned (getr R 2%bv)) /\
  K [].

Definition ukey_at (p0 : Z) (R : bvmap 5 word) (M : word -> option byte) (Kt : list Z) : Prop :=
  ukey L ar p0 M (bv_unsigned (getr R 2%bv)) (bv_unsigned (getr R 1%bv)) (bv_unsigned (getr R 8%bv)) Kt.

Definition amallocN_spec : Prop :=
  forall D fx R M model LB FF LK cr A n K,
    amalloc_preG D fx R M model LB FF LK cr A n K -> 0 < n <= NREQ -> acredit_ok L cr n ->
    amalloc_postG D (adebit L cr n) fx R M model LB FF LK A n K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_malloc L)) M model) K.

Definition amallocL_spec : Prop :=
  forall D fx R M model LB FF LK cr A n K Kt,
    amalloc_preG D fx R M model LB FF LK cr A n K -> 0 < n <= NREQ -> acredit_ok L cr n ->
    ukey_at (hlr_pc_malloc LR_) R M Kt ->
    amalloc_postG (Kt :: D) (adebit L cr n) fx R M model LB FF LK A n K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_malloc L)) M model) K.
Definition afreeL_spec : Prop :=
  forall D fx R M model LB FF LK cr A u n K Kt,
    afree_preG D fx R M model LB FF LK cr A u n K ->
    ukey_at (hlr_pc_free LR_) R M Kt ->
    afree_postG (Kt :: D) cr fx R M model LB FF LK A u K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_free L)) M model) K.

Definition amallocW_spec : Prop :=
  forall D fx R M model LB FF LK cr A n K Kt,
    amalloc_preG D fx R M model LB FF LK cr A n K -> NW_LO <= n <= NW_HI -> 1 <= fst cr ->
    ukey_at (hlr_pc_malloc LR_) R M Kt -> In Kt D ->
    amalloc_postG D (fst cr - 1, snd cr) fx R M model LB FF LK A n K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_malloc L)) M model) K.
Definition afreeW_spec : Prop :=
  forall D fx R M model LB FF LK cr A u n K Kt,
    afree_preG D fx R M model LB FF LK cr A u n K -> NW_LO <= n <= NW_HI ->
    ukey_at (hlr_pc_free LR_) R M Kt -> In Kt D ->
    afree_postG D (fst cr + 1, snd cr) fx R M model LB FF LK A u K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_free L)) M model) K.

Definition amemN_pre (D : list (list Z)) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (dst n : Z) (K : ShapeAlg.TSet) : Prop :=
  ri_inv (HIk D) LB FF LK cr A M (vml_of model) /\ m_halted model = None /\ MInv A model /\
  getr R 10%bv = Z_to_bv 64 dst /\ getr R 12%bv = Z_to_bv 64 n /\ 0 <= n <= NREQI /\
  getr R 4%bv = Z_to_bv 64 (hl_tp L) /\ Hoare.ret_ok (getr R 1%bv) /\
  astack_ok L ar M (hl_scr_mem L) (bv_unsigned (getr R 2%bv)) /\
  aacc M dst n /\ (forall i, 0 <= i < n -> aclientw L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_mem L) (dst + i)) /\
  (forall i (m : nat), 0 <= i -> i + Z.of_nat m <= n -> store_ok (hl_segs L) M (Z_to_bv 64 (dst + i)) m = true) /\
  K [] /\ app_rng ar dst n.
Definition amemsetN_spec : Prop :=
  forall D fx R M model LB FF LK cr A dst c n K,
    amemN_pre D fx R M model LB FF LK cr A dst n K -> getr R 11%bv = Z_to_bv 64 c ->
    amem_post L ar scfg (HIk D) fx R M model LB FF LK cr A dst n (fun _ v => v = c mod 256) K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_asan_memset L)) M model) K.
Definition amemcpyN_spec_at (pc : Z) : Prop :=
  forall D fx R M model LB FF LK cr A dst src n (bs : list byte) K,
    amemN_pre D fx R M model LB FF LK cr A dst n K -> getr R 11%bv = Z_to_bv 64 src ->
    aacc M src n -> 0 <= src /\ src + n <= 2 ^ 47 -> app_rng ar src n ->
    (forall i, 0 <= i < n -> hl_img_lo L <= src + i < hl_img_hi L \/ aclient L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_mem L) (src + i)) ->
    rdn (hl_segs L) M (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->
    (dst + n <= src \/ src + n <= dst) ->
    amem_post L ar scfg (HIk D) fx R M model LB FF LK cr A dst n (fun i v => nth_error bs (Z.to_nat i) = Some (Z_to_bv 8 v) /\ 0 <= v < 256) K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 pc) M model) K.

Definition rt_weakenR : Prop :=
  forall D0 D1 LB FF LK cr cr' A M V,
    ri_inv (HIk D1) LB FF LK cr A M V -> incl D0 D1 ->
    0 <= fst cr' <= fst cr -> 0 <= snd cr' <= snd cr ->
    ri_inv (HIk D0) LB FF LK cr' A M V.

Record asan_famR_ok : Prop := AFROK {
  fr_base    : forall D, HAJ.asan_iface_okR L ar C scfg (HIk D);
  fr_weaken  : rt_weakenR;
  fr_mallocN : amallocN_spec;
  fr_memsetN : amemsetN_spec;
  fr_memcpyN : amemcpyN_spec_at (hl_asan_memcpy L);
  fr_memmoveN : amemcpyN_spec_at (hl_asan_memmove L);
  fr_mallocL : amallocL_spec;
  fr_freeL   : afreeL_spec;
  fr_mallocW : amallocW_spec;
  fr_freeW   : afreeW_spec
}.

Definition kin (Kt : list Z) (D : list (list Z)) : bool :=
  existsb (fun k => if list_eq_dec Z.eq_dec k Kt then true else false) D.
Lemma kin_In Kt D : kin Kt D = true -> In Kt D.
Proof.
  unfold kin. rewrite existsb_exists. intros (k & Hk & E). destruct (list_eq_dec Z.eq_dec k Kt) as [->|]; [exact Hk | discriminate].
Qed.
Definition warm_ok (Kt : list Z) (D : list (list Z)) (n : Z) : bool := kin Kt D && (NW_LO <=? n) && (n <=? NW_HI).
Definition amallocU_spec : Prop :=
  forall D fx R M model LB FF LK cr A n K Kt,
    amalloc_preG D fx R M model LB FF LK cr A n K -> 0 < n <= NREQ ->
    ukey_at (hlr_pc_malloc LR_) R M Kt ->
    (if warm_ok Kt D n then 1 <= fst cr else acredit_ok L cr n) ->
    amalloc_postG (Kt :: D) (if warm_ok Kt D n then (fst cr - 1, snd cr) else adebit L cr n) fx R M model LB FF LK A n K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_malloc L)) M model) K.
Definition afreeU_spec : Prop :=
  forall D fx R M model LB FF LK cr A u n K Kt,
    afree_preG D fx R M model LB FF LK cr A u n K ->
    ukey_at (hlr_pc_free LR_) R M Kt ->
    afree_postG (Kt :: D) (if warm_ok Kt D n then (fst cr + 1, snd cr) else cr) fx R M model LB FF LK A u K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_free L)) M model) K.

Section Derived.
Hypothesis OK : asan_famR_ok.

Lemma warm_ok_facts Kt D n : warm_ok Kt D n = true -> In Kt D /\ NW_LO <= n <= NW_HI.
Proof.
  unfold warm_ok. rewrite !andb_true_iff. intros ((H1 & H2) & H3). split; [apply kin_In; exact H1|].
  apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
Qed.

Lemma amalloc_postG_known D Kt crp fx R M model LB FF LK A n K :
  In Kt D -> 0 <= fst crp -> 0 <= snd crp ->
  amalloc_postG (Kt :: D) crp fx R M model LB FF LK A n K -> amalloc_postG D crp fx R M model LB FF LK A n K.
Proof.
  intros Hin H1 H2 P R' M' model' A' u E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 RI.
  apply (P R' M' model' A' u E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11).
  apply (fr_weaken OK (Kt :: D) D _ _ _ crp crp _ _ _ RI); [|lia|lia].
  intros k [<-|Hk]; assumption.
Qed.
Lemma afree_postG_known D Kt crp fx R M model LB FF LK A u K :
  In Kt D -> 0 <= fst crp -> 0 <= snd crp ->
  afree_postG (Kt :: D) crp fx R M model LB FF LK A u K -> afree_postG D crp fx R M model LB FF LK A u K.
Proof.
  intros Hin H1 H2 P R' M' model' A' E1 E2 E3 E4 E5 RI.
  apply (P R' M' model' A' E1 E2 E3 E4 E5).
  apply (fr_weaken OK (Kt :: D) D _ _ _ crp crp _ _ _ RI); [|lia|lia].
  intros k [<-|Hk]; assumption.
Qed.

Lemma credit_nonneg D LB FF LK cr A M V : ri_inv (HIk D) LB FF LK cr A M V -> 0 <= fst cr /\ 0 <= snd cr.
Proof.
  intros RI. pose proof (HAJ.aior_wf _ _ _ _ _ (fr_base OK D) LB FF LK cr A M V RI) as W.
  destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W1 & W2 & _). split; assumption.
Qed.

Theorem amallocU_holds : amallocU_spec.
Proof.
  intros D fx R M model LB FF LK cr A n K Kt PRE Hn UK CR POST.
  destruct (warm_ok Kt D n) eqn:W.
  - destruct (warm_ok_facts Kt D n W) as (Hin & Hr).
    pose proof PRE as (RI & _). destruct (credit_nonneg _ _ _ _ _ _ _ _ RI) as (C1 & C2).
    apply (fr_mallocW OK D fx R M model LB FF LK cr A n K Kt PRE Hr CR UK Hin).
    apply (amalloc_postG_known D Kt); [exact Hin | cbn; lia | cbn; lia | exact POST].
  - exact (fr_mallocL OK D fx R M model LB FF LK cr A n K Kt PRE Hn CR UK POST).
Qed.
Theorem afreeU_holds : afreeU_spec.
Proof.
  intros D fx R M model LB FF LK cr A u n K Kt PRE UK POST.
  destruct (warm_ok Kt D n) eqn:W.
  - destruct (warm_ok_facts Kt D n W) as (Hin & Hr).
    pose proof PRE as (RI & _). destruct (credit_nonneg _ _ _ _ _ _ _ _ RI) as (C1 & C2).
    apply (fr_freeW OK D fx R M model LB FF LK cr A u n K Kt PRE Hr UK Hin).
    apply (afree_postG_known D Kt); [exact Hin | cbn; lia | cbn; lia | exact POST].
  - exact (fr_freeL OK D fx R M model LB FF LK cr A u n K Kt PRE UK POST).
Qed.
End Derived.
End Fam.

End HAR.
