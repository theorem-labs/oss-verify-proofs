(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages LazyModel NodesA Shadow CompatE2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BYajlRep BYajl_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section K.
Variable Y : ay_params.
#[local, warnings="-notation-for-abbreviation"] Notation AHK := (y_AHK Y).
#[local, warnings="-notation-for-abbreviation"] Notation aS := (y_aS Y).
#[local, warnings="-notation-for-abbreviation"] Notation aN := (y_aN Y).
#[local, warnings="-notation-for-abbreviation"] Notation aEB := (y_aEB Y).
#[local, warnings="-notation-for-abbreviation"] Notation AYSTY := (AYST Y).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition aystatics (m : mem) : Prop :=
  rw_cells bsegs m AY_CALLBACKS (callbacks_cells ayc)
  /\ rw_cells bsegs m AY_BUF_ALLOC_ERROR (buf_alloc_error_cells ayc)
  /\ rw_cells bsegs m AY_NOOP_ALLOCS anoop_allocs_cells
  /\ ay_statics m.

Lemma AYST_split : forall s LB LF m mo, AYSTY s LB LF m mo <-> AHK s LB LF m mo /\ aystatics m.
Proof. aceil. intros. unfold AYST, aystatics. tauto. Qed.

Lemma Forall_disjoint_from : forall W lo0 hi0 A n,
  Forall (fun iv : Z * Z => snd iv <= lo0 \/ hi0 <= fst iv) W -> lo0 <= A -> A + n <= hi0 -> disjoint_from W A n.
Proof. aceil.
  intros W lo0 hi0 A n FW H1 H2. induction W as [|[lo hi] W IH]; cbn; [exact I|].
  inversion FW as [|x l F1 F2]; subst. cbn in F1. split; [lia| apply IH; exact F2].
Qed.

(* [comment removed for export] *)
Lemma aystatics_munch : forall W m m',
  aystatics m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => snd iv <= 0xa5000 \/ 0xae838 <= fst iv) W -> aystatics m'.
Proof. aceil.
  intros W m m' (C1 & C2 & C3 & (G1 & G2 & G3 & G4)) MU WM FW.
  pose proof (fun A n => Forall_disjoint_from W _ _ A n FW) as D.
  split; [|split; [|split; [|split; [|split; [|split]]]]];
    (eapply rw_cells_transport; [eassumption| exact MU| exact WM| apply D;
       unfold AY_CALLBACKS, AY_BUF_ALLOC_ERROR, AY_NOOP_ALLOCS, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR; cbn; lia]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aypres_rw_cells : forall REST LF SP X m m' A cs,
  ay_pres REST LF SP X m m' -> rw_cells bsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ay_client_addr REST LF SP a /\ ~ yin_ivs X a) ->
  rw_cells bsegs m' A cs.
Proof. aceil. intros. eapply rw_cells_agree; [eapply ay_pres_agree; eassumption| eassumption| assumption]. Qed.

Lemma aypres_bytes : forall REST LF SP X m m' A bs,
  ay_pres REST LF SP X m m' -> bytes_at bsegs m A bs ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> ay_client_addr REST LF SP a /\ ~ yin_ivs X a) ->
  bytes_at bsegs m' A bs.
Proof. aceil. intros. eapply bytes_at_agree; [eapply ay_pres_agree; eassumption| eassumption| assumption]. Qed.


Lemma aypres_frame : forall REST LF SP m m' A cs,
  ay_pres REST LF SP [] m m' -> rw_cells bsegs m A cs -> SP <= A -> rw_cells bsegs m' A cs.
Proof. aceil. intros. eapply aypres_rw_cells; eauto. intros a Ha. split; [left; lia| intros F0; exact F0]. Qed.

Lemma aypres_block : forall REST LF SP m m' A cs,
  ay_pres REST LF SP [] m m' -> rw_cells bsegs m A cs ->
  (exists b, In b REST /\ ab_addr b <= A /\ A + Z.of_nat (cells_size cs) <= ab_addr b + ab_size b) ->
  rw_cells bsegs m' A cs.
Proof. aceil.
  intros REST LF SP m m' A cs HP HC (b & Hb & H1 & H2). eapply aypres_rw_cells; eauto.
  intros a Ha. split; [| intros F0; exact F0]. right; left. exists b. split; [exact Hb| lia].
Qed.

Lemma aypres_block_bytes : forall REST LF SP m m' A bs,
  ay_pres REST LF SP [] m m' -> bytes_at bsegs m A bs ->
  (exists b, In b REST /\ ab_addr b <= A /\ A + Z.of_nat (length bs) <= ab_addr b + ab_size b) ->
  bytes_at bsegs m' A bs.
Proof. aceil.
  intros REST LF SP m m' A bs HP HC (b & Hb & H1 & H2). eapply aypres_bytes; eauto.
  intros a Ha. split; [| intros F0; exact F0]. right; left. exists b. split; [exact Hb| lia].
Qed.

Lemma aypres_static : forall REST LF SP m m' A cs,
  ay_pres REST LF SP [] m m' -> rw_cells bsegs m A cs -> 0xa9b40 <= A -> A + Z.of_nat (cells_size cs) <= 0xa9c20 ->
  rw_cells bsegs m' A cs.
Proof. aceil.
  intros. eapply aypres_rw_cells; eauto. intros a Ha. split; [| intros F0; exact F0]. right; right; right. left. lia.
Qed.

Lemma aypres_fframe : forall REST LF SP m m' A cs f,
  ay_pres REST LF SP [] m m' -> rw_cells bsegs m A cs -> In f LF ->
  (snd f <= A /\ A + Z.of_nat (cells_size cs) <= snd f + ff_bytes (fst f))
  \/ (oshw_lo (snd f) <= A /\ A + Z.of_nat (cells_size cs) <= oshw_lo (snd f) + Z.shiftl 8 (fst f)) ->
  rw_cells bsegs m' A cs.
Proof. aceil.
  intros REST LF SP m m' A cs f HP HC Hf HR. eapply aypres_rw_cells; eauto. intros a Ha. split; [| intros F0; exact F0].
  right; right; left. exists f. split; [exact Hf|]. unfold oshw_lo in *. destruct HR; [left| right]; lia.
Qed.

Lemma aypres_text : forall REST LF SP m m' T txt,
  ay_pres REST LF SP [] m m' -> text_at bsegs m T txt ->
  ((exists b, In b REST /\ ab_addr b <= T /\ T + zlength txt <= ab_addr b + ab_size b) \/ zlength txt = 0) ->
  text_at bsegs m' T txt.
Proof. aceil.
  intros REST LF SP m m' T txt HP (TB & TF & T0 & TL) HR. split; [| auto].
  destruct HR as [HR| Z0].
  - eapply aypres_block_bytes; eauto. rewrite zbytes_length. unfold zlength in HR. exact HR.
  - destruct txt; [| unfold zlength in Z0; cbn in Z0; lia]. destruct TB as (B0 & B1 & _).
    split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. lia.
Qed.

(* [comment removed for export] *)
Lemma aystatics_pres : forall REST LF SP m m', aystatics m -> ay_pres REST LF SP [] m m' ->
  rw_cells bsegs m' AY_CALLBACKS (callbacks_cells ayc)
  /\ rw_cells bsegs m' AY_BUF_ALLOC_ERROR (buf_alloc_error_cells ayc)
  /\ rw_cells bsegs m' AY_NOOP_ALLOCS anoop_allocs_cells.
Proof. aceil.
  intros REST LF SP m m' (C1 & C2 & C3 & _) HP.
  split; [|split]; (eapply aypres_static; [exact HP| eassumption| unfold AY_CALLBACKS, AY_BUF_ALLOC_ERROR, AY_NOOP_ALLOCS; cbn; lia| unfold AY_CALLBACKS, AY_BUF_ALLOC_ERROR, AY_NOOP_ALLOCS; cbn; lia]).
Qed.

(* [comment removed for export] *)
Lemma ff_shadow_top : forall f : fblock, 0 <= fst f <= 1 -> 0 <= snd f -> snd f + ff_bytes (fst f) <= alloc_ceiling ->
  oshw_lo (snd f) + Z.shiftl 8 (fst f) < alloc_ceiling.
Proof. aceil.
  intros f Hc H0 H1. unfold oshw_lo, A_SB in *; aceil.
  assert (E : fst f = 0 \/ fst f = 1) by lia. destruct E as [E|E]; rewrite E in *; unfold ff_bytes in *;
    [change (Z.shiftl 8 0) with 8; change (Z.shiftl 64 0) with 64 in *| change (Z.shiftl 8 1) with 16; change (Z.shiftl 64 1) with 128 in *];
    Z.div_mod_to_equations; lia.
Qed.
Lemma ff_shadow_top2 : forall f : fblock, 0 <= fst f <= 1 -> 0 <= snd f -> snd f + ff_bytes (fst f) <= alloc_ceiling ->
  oshw_lo (snd f) + Z.shiftl 8 (fst f) <= oshw_hi 0 (2^47).
Proof. aceil.
  intros f Hc H0 H1. unfold oshw_lo, oshw_hi, A_SB, amem in *; aceil.
  assert (E : fst f = 0 \/ fst f = 1) by lia. destruct E as [E|E]; rewrite E in *; unfold ff_bytes in *;
    [change (Z.shiftl 8 0) with 8; change (Z.shiftl 64 0) with 64 in *| change (Z.shiftl 8 1) with 16; change (Z.shiftl 64 1) with 128 in *];
    cbn; Z.div_mod_to_equations; lia.
Qed.
Lemma ay_client_outside : forall REST LF SP lo hi a,
  (forall b, In b REST -> ab_addr b + ab_size b <= alloc_ceiling) ->
  (forall f, In f LF -> 0 <= fst f <= 1 /\ 0 <= snd f /\ snd f + ff_bytes (fst f) <= alloc_ceiling) ->
  alloc_ceiling <= lo -> hi <= SP -> ay_client_addr REST LF SP a -> outside [(lo, hi)] a.
Proof. aceil.
  intros REST LF SP lo hi a HB HF H1 H2 Hc. cbn. split; [| exact I].
  destruct Hc as [Hc|[(b & Hb & Hr)|[(f & Hf & Hr)|Hc]]].
  - lia.
  - pose proof (HB b Hb). lia.
  - destruct (HF f Hf) as (F1 & F2 & F3). pose proof (ff_shadow_top f F1 F2 F3) as T.
    unfold oshw_lo in *. aceil. destruct Hr; lia.
  - unfold ay_static in *; aceil. lia.
Qed.

(* [comment removed for export] *)
Lemma nbig_cons_le : forall b l, nbig (b :: l) <= 1 + nbig l.
Proof. aceil. intros b l. unfold nbig. cbn [List.filter]. destruct (64512 <? ab_size b); cbn [length]; lia. Qed.
Lemma nbig_nil : nbig [] = 0. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ab_remove_head : forall A n l, ab_remove A (mkABlock A n :: l) = l.
Proof. aceil. intros. cbn [ab_remove ab_addr]. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma ab_remove_skip : forall A B n l, B <> A -> ab_remove A (mkABlock B n :: l) = mkABlock B n :: ab_remove A l.
Proof. aceil. intros A B n l H. cbn [ab_remove ab_addr]. destruct (Z.eqb_spec B A); [lia| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma nd_head_ne : forall x l b, List.NoDup (map ab_addr (x :: l)) -> In b l -> ab_addr x <> ab_addr b.
Proof. aceil.
  intros x l b ND Hb E. cbn [map] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI _].
  apply NI. rewrite E. apply in_map. exact Hb.
Qed.
Lemma nd_tail : forall x l, List.NoDup (map ab_addr (x :: l)) -> List.NoDup (map ab_addr l).
Proof. aceil. intros x l ND. cbn [map] in ND. apply List.NoDup_cons_iff in ND. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pol.
Variables (LB : list ablock) (LF : list fblock) (L : list (word * word)) (S : word -> Prop).
Hypothesis LINK : forall x, ay_acc Y LB LF x -> acc_ok L S x.

Lemma aypol_stack : forall lo hi, alloc_ceiling <= lo -> hi <= 2^47 -> pol (acc_ok L S) lo hi.
Proof. aceil.
  intros lo hi H1 H2 a k Ha Hk. apply LINK. unfold ay_acc. cbn [fst snd]. rewrite unsigned_lit by (aceil; lia). left. lia.
Qed.
Lemma aypol_img : pol (acc_ok L S) AY_IMG_LO AY_IMG_HI.
Proof. aceil.
  intros a k Ha Hk. apply LINK. unfold ay_acc. cbn [fst snd]. unfold AY_IMG_LO, AY_IMG_HI in *. rewrite unsigned_lit by lia. right; left. lia.
Qed.
Lemma aypol_block : forall b lo hi, In b LB -> ab_addr b <= lo -> hi <= ab_addr b + ab_size b -> 0 <= lo -> ab_addr b + ab_size b < 2^64 ->
  pol (acc_ok L S) lo hi.
Proof. aceil.
  intros b lo hi Hb H1 H2 H3 H4 a k Ha Hk. apply LINK. unfold ay_acc. cbn [fst snd]. rewrite unsigned_lit by lia.
  right; right; left. exists b. split; [exact Hb| lia].
Qed.
Lemma aypol_bshadow : forall b lo hi, In b LB -> oshw_lo (ab_addr b) <= lo -> hi <= oshw_hi (ab_addr b) (ab_size b) -> 0 <= lo -> oshw_hi (ab_addr b) (ab_size b) < 2^64 ->
  pol (acc_ok L S) lo hi.
Proof. aceil.
  intros b lo hi Hb H1 H2 H3 H4 a k Ha Hk. apply LINK. unfold ay_acc. cbn [fst snd]. rewrite unsigned_lit by lia.
  right; right; right; left. exists b. split; [exact Hb| lia].
Qed.
Lemma aypol_opol_block : forall b, In b LB -> 0 <= ab_addr b -> 0 <= oshw_lo (ab_addr b) -> oshw_hi (ab_addr b) (ab_size b) < 2^64 -> ab_addr b + ab_size b < 2^64 ->
  opol (acc_ok L S) (ab_addr b) (ab_size b).
Proof. aceil.
  intros b Hb H0 H1 H2 H3. split; [eapply aypol_block; eauto; lia| eapply aypol_bshadow; eauto; lia].
Qed.
(* [comment removed for export] *)
Lemma aypol_opol_sub : forall b A n, In b LB -> ab_addr b <= A -> A + n <= ab_addr b + ab_size b -> 0 <= n -> ab_addr b mod 8 = 0 ->
  0 <= ab_addr b -> 0 <= oshw_lo (ab_addr b) -> oshw_hi (ab_addr b) (ab_size b) < 2^64 -> ab_addr b + ab_size b < 2^64 ->
  opol (acc_ok L S) A n.
Proof. aceil.
  intros b A n Hb H1 H2 Hn H8 H3 H4 H5 H6. split; [eapply aypol_block; eauto; lia|].
  eapply aypol_bshadow; eauto; unfold oshw_lo, oshw_hi in *; Z.div_mod_to_equations; lia.
Qed.
Lemma aypol_fframe : forall f lo hi, In f LF -> snd f <= lo -> hi <= snd f + ff_bytes (fst f) -> 0 <= lo -> snd f + ff_bytes (fst f) < 2^64 ->
  pol (acc_ok L S) lo hi.
Proof. aceil.
  intros f lo hi Hf H1 H2 H3 H4 a k Ha Hk. apply LINK. unfold ay_acc. cbn [fst snd]. rewrite unsigned_lit by lia.
  right; right; right; right; left. exists f. split; [exact Hf| lia].
Qed.
Lemma aypol_ffshadow : forall f lo hi, In f LF -> oshw_lo (snd f) <= lo -> hi <= oshw_lo (snd f) + Z.shiftl 8 (fst f) -> 0 <= lo -> oshw_lo (snd f) + Z.shiftl 8 (fst f) < 2^64 ->
  pol (acc_ok L S) lo hi.
Proof. aceil.
  intros f lo hi Hf H1 H2 H3 H4 a k Ha Hk. apply LINK. unfold ay_acc. cbn [fst snd]. rewrite unsigned_lit by lia.
  right; right; right; right; right; left. exists f. split; [exact Hf| lia].
Qed.
Lemma aypol_imgshadow : forall lo hi, oshw_lo AY_IMG_LO <= lo -> hi <= oshw_hi AY_IMG_LO (AY_IMG_HI - AY_IMG_LO) ->
  pol (acc_ok L S) lo hi.
Proof. aceil.
  intros lo hi H1 H2 a k Ha Hk. apply LINK. unfold ay_acc. cbn [fst snd].
  unfold oshw_lo, oshw_hi, A_SB, amem, AY_IMG_LO, AY_IMG_HI in *. rewrite unsigned_lit by lia.
  do 7 right. lia.
Qed.
(* [comment removed for export] *)
Lemma aypol_pages : forall lo hi, pages_budgeted S lo hi -> 0 <= lo -> hi < 2^64 -> pol (acc_ok L S) lo hi.
Proof. aceil.
  intros lo hi HB H0 H1 a k Ha Hk. right. eapply (pages_budgeted_acc_inS S lo hi); try eassumption; lia.
Qed.
End Pol.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition arz_post (s : y_APS Y) (mo : Model) (K : TSet) (ms' : machine_state) : Prop :=
  forall mo', magree mo mo' -> LI (aS s) (aN s) (aEB s) mo' -> m_halted mo' = None -> realizes_cfg acfg bsegs (mkCfg ms' mo') K.

Lemma arz_seg_lemma : forall s ms mo K,
  m_halted mo = None -> LI (aS s) (aN s) (aEB s) mo ->
  evtA bsegs (acc_ok (m_vm_lazy mo) (aS s)) (arz_post s mo K) ms ->
  realizes_cfg acfg bsegs (mkCfg ms mo) K.
Proof. aceil.
  intros s ms mo K Hh HLI HE. eapply (srzA_evt bsegs (aS s) (aN s) (aEB s) (m_vm_lazy mo)); [exact HE| exact Hh| exact HLI| reflexivity|].
  intros ms' mo' HQ Hag HLI' Hh'. exact (HQ mo' Hag HLI' Hh').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma asegs_find_segment_ro : forall a, 0x10000 <= a -> a + 1 <= 0x31000 ->
  find_segment bsegs a 1 = Some AsanUbsan.AsanUbsan_segment_000.
Proof. aceil.
  intros a H1 H2. unfold bsegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_000)) with 0x21000%Z by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 a); destruct (Z.leb_spec0 (a + 1) (0x10000 + 0x21000)); cbn [andb]; try lia. reflexivity.
Qed.
Lemma asegs_ro_addr : forall a, 0x10000 <= a -> a + 1 <= 0x31000 -> ro_addr bsegs (wa a) = true.
Proof. aceil.
  intros a H1 H2. unfold ro_addr. rewrite wa_unsigned by lia. rewrite asegs_find_segment_ro by lia. vm_compute. reflexivity.
Qed.
Lemma arodata_bytes_persist : forall m m' A bs,
  bytes_at bsegs m A bs -> mem_inv bsegs m -> mem_inv bsegs m' ->
  0x10000 <= A -> A + Z.of_nat (length bs) <= 0x31000 ->
  bytes_at bsegs m' A bs.
Proof. aceil.
  intros m m' A bs (H0 & H1 & HB) MI MI' HA HL. split; [exact H0|]. split; [exact H1|].
  intros i Hi. specialize (HB i Hi).
  pose proof (asegs_ro_addr (A + Z.of_nat i) ltac:(lia) ltac:(lia)) as RO.
  unfold mrd in *.
  destruct (m (wa (A + Z.of_nat i))) eqn:E. { exfalso. pose proof (MI _ _ E). congruence. }
  destruct (m' (wa (A + Z.of_nat i))) eqn:E'. { exfalso. pose proof (MI' _ _ E'). congruence. }
  exact HB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Outside.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis LAYY : AHK_y_layout_stmt Y.

(* [comment removed for export] *)
Lemma ay_client_outside_block : forall s LB LF m mo REST SP X lo hi a,
  y_AHK Y s LB LF m mo -> In X LB -> (forall b, In b REST -> In b LB /\ ab_addr b <> ab_addr X) ->
  ab_addr X <= lo -> hi <= ab_addr X + ab_size X -> lo < hi -> alloc_ceiling <= SP ->
  ay_client_addr REST LF SP a -> outside [(lo, hi)] a.
Proof. aceil.
  intros s LB LF m mo REST SP X lo hi a AHK HX HR H1 H2 H3 HSP Hc. cbn. split; [| exact I].
  destruct (BLKY _ _ _ _ _ AHK) as (RNG & SEP & ND).
  pose proof (RNG X HX) as RX. unfold ablock_range, ACONSTS in RX. cbn [c_img_hi] in RX.
  pose proof (BSHY _ _ _ _ _ X AHK HX ltac:(lia)) as [_ XS]. unfold amem in XS.
  destruct Hc as [Hc|[(b & Hb & Hr)|[(f & Hf & Hr)|Hc]]].
  - lia.
  - destruct (HR b Hb) as [HbL NE]. destruct (SEP X b HX HbL ltac:(intros E; apply NE; symmetry; exact E)); lia.
  - (* [comment removed for export] *)
    destruct (proj1 (LAYY _ _ _ _ _ AHK) f Hf) as (L1 & L2 & L3 & L4 & L5).
    destruct (proj1 (proj2 (LAYY _ _ _ _ _ AHK)) f X Hf HX) as [D1 _].
    pose proof (ff_shadow_top2 f L4 ltac:(unfold amem in L1; lia) L2) as T. unfold oshw_lo, oshw_hi, A_SB, amem in T. cbn in T.
    assert (Q : 0 <= snd f / 8) by (apply Z.div_pos; [unfold amem in L1; lia| lia]).
    unfold A_SB in Hr. destruct Hr; [lia|]. destruct XS as [_ [XS|XS]]; lia.
  - unfold ay_static in Hc. lia.
Qed.

(* [comment removed for export] *)
Lemma ay_client_outside_stack : forall s LB LF m mo REST SP lo hi a,
  y_AHK Y s LB LF m mo -> (forall b, In b REST -> In b LB) ->
  alloc_ceiling <= lo -> hi <= SP -> ay_client_addr REST LF SP a -> outside [(lo, hi)] a.
Proof. aceil.
  intros s LB LF m mo REST SP lo hi a AHK HR H1 H2 Hc.
  destruct (BLKY _ _ _ _ _ AHK) as (RNG & SEP & ND).
  eapply ay_client_outside; [ | | exact H1| exact H2| exact Hc].
  - intros b Hb. pose proof (RNG b (HR b Hb)) as Rb. unfold ablock_range in Rb. lia.
  - intros f Hf. destruct (proj1 (LAYY _ _ _ _ _ AHK) f Hf) as (L1 & L2 & L3 & L4 & L5). unfold oshw_hi, A_SB, amem in L1. lia.
Qed.

(* [comment removed for export] *)
Lemma outside_cons : forall iv W a, outside [iv] a -> outside W a -> outside (iv :: W) a.
Proof. aceil. intros [lo hi] W a [H _] HW. cbn. split; assumption. Qed.
End Outside.
End K.

(* [comment removed for export] *)
End RC__1.
Ltac arz_seg KIPY AHKx :=
  let Hh := fresh "Hh" in let Hmi := fresh "Hmi" in let HLI := fresh "HLI" in
  let LINK := fresh "LINK" in let BACK := fresh "BACK" in
  destruct (KIPY _ _ _ _ _ AHKx) as (Hh & Hmi & HLI & LINK & BACK);
  eapply arz_seg_lemma; [exact Hh| exact HLI|].
