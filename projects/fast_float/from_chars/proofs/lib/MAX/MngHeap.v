(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr.
Import ListNotations.

Module AxTry2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Fixpoint forall_from2 (f : Z -> bool) (lo : Z) (n : nat) : bool :=
  match n with O => true | S n' => f lo && forall_from2 f (lo + 1) n' end.

Lemma forall_from2_ok : forall f n lo, forall_from2 f lo n = true -> forall x, lo <= x < lo + Z.of_nat n -> f x = true.
Proof.
  intros f n. induction n as [|n IH]; intros lo H x Hx; [lia|].
  cbn [forall_from2] in H. apply andb_true_iff in H as [H1 H2].
  destruct (Z.eq_dec x lo) as [->|Hne]; [exact H1|]. apply (IH (lo + 1) H2). lia.
Qed.

(* [comment removed for export] *)
Definition srlw1_chk (x : Z) : bool :=
  Z.eqb (bv_unsigned (sext 64 (alu32 ALU_SRL (low32 (wa x)) (low32 (Z_to_bv 64 1))))) (bv_unsigned (wa (x / 2))).

Lemma srlw1_chk_all : forall_from2 srlw1_chk 0 33%nat = true.
Proof. vm_compute. reflexivity. Qed.

Lemma srlw1_small : forall x, 0 <= x <= 32 -> sext 64 (alu32 ALU_SRL (low32 (wa x)) (low32 (Z_to_bv 64 1))) = wa (x / 2).
Proof.
  intros x Hx. pose proof (forall_from2_ok _ _ _ srlw1_chk_all x ltac:(cbn; lia)) as H. unfold srlw1_chk in H.
  apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

Lemma swrap32_small : forall x, 0 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma sllw2_small : forall c, 0 <= c <= 2^28 -> bv_swrap 32 (Z.shiftl (c mod 2^64) (2 mod 32)) mod 2^64 = 4 * c.
Proof.
  intros c Hc. rewrite (Z.mod_small c) by lia. change (2 mod 32) with 2. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite swrap32_small by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition land2_chk (c : Z) : bool := Z.eqb (Z.land c 2) (2 * ((c mod 4) / 2)).
Lemma land2_chk_all : forall_from2 land2_chk 0 33%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma land2_small : forall c, 0 <= c <= 32 -> Z.land c 2 = 2 * ((c mod 4) / 2).
Proof. intros c Hc. pose proof (forall_from2_ok _ _ _ land2_chk_all c ltac:(cbn; lia)) as H. unfold land2_chk in H. apply Z.eqb_eq in H. exact H. Qed.

Lemma br_lt_z : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 -> branch_taken BC_LT (wa x) (wa y) = (x <? y).
Proof.
  intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts, wa. rewrite !Z_to_bv_signed.
  rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2^63); lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pr_land : forall x, 0 <= x < 2^60 -> Z.land ((-1 * x + 0) mod 2^64) 4095 + x = (x + 4096 - 1) / 4096 * 4096.
Proof.
  intros x Hx. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia.
  replace ((-1 * x + 0) mod 2^64 mod 2^12) with ((- x) mod 2^12).
  2:{ rewrite Z.mod_mod_divide; [f_equal; ring | exists (2^52); reflexivity]. }
  change (2^12) with 4096. pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)) as B.
  pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as B2.
  assert (E : (- x) mod 4096 = (4095 - (x + 4095) mod 4096)).
  { symmetry. apply Z.mod_unique with (q := - ((x + 4095) / 4096)); [left; lia | lia]. }
  lia.
Qed.

Lemma sltu_z : forall E a b, bv_unsigned (edenot E (EAlu ALU_SLTU a b)) = if (zeval E a mod 2^64 <? zeval E b mod 2^64) then 1 else 0.
Proof.
  intros E a b. cbn [edenot]. rewrite alu_sltu. unfold v_sltu. rewrite !zeval_sound.
  unfold c_ltu, bv_ltu. rewrite !u_wa. destruct (_ <? _); reflexivity.
Qed.

Lemma pr_land2 : forall a b, 0 <= a + b < 2^60 -> (Z.land ((-1 * a + - b) mod 2^64) 4095 + a) + b = (a + b + 4096 - 1) / 4096 * 4096.
Proof. intros a b H. rewrite <- (pr_land (a + b) H). replace (-1 * a + - b) with (-1 * (a + b) + 0) by ring. ring. Qed.

Lemma pr_land3 : forall a b, 0 <= a + b < 2^60 -> (a + Z.land ((-1 * a + - b) mod 2^64) 4095) + b = (a + b + 4096 - 1) / 4096 * 4096.
Proof. intros a b H. rewrite <- (pr_land2 a b H). ring. Qed.

Lemma sllw1_small : forall c, 0 <= c <= 2^28 -> bv_swrap 32 (Z.shiftl (c mod 2^64) (1 mod 32)) mod 2^64 = 2 * c.
Proof.
  intros c Hc. rewrite (Z.mod_small c) by lia. change (1 mod 32) with 1. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite swrap32_small by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma pr_rq : forall req, 0 <= req <= 2^26 -> (req + Z.land ((-1 * req + -20) mod 2^64) 4095) + 20 = page_round (req + 20).
Proof. intros req H. unfold page_round, PGSZ. rewrite <- (pr_land (req + 20)) by lia. replace (-1 * req + -20) with (-1 * (req + 20) + 0) by ring. ring. Qed.

Lemma pr_sz : forall x, 0 <= x < 2^40 -> (Z.land ((-1 * x + -16) mod 2^64) 4095 + x) + 16 = page_round (x + 16).
Proof. intros x H. unfold page_round, PGSZ. rewrite <- (pr_land (x + 16)) by lia. replace (-1 * x + -16) with (-1 * (x + 16) + 0) by ring. ring. Qed.
End AxTry2.

Module MngMWP.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition rgeo (HTOP : Z) (L : layout) (s : astate) : Prop :=
  forall r rg, region_of s r = Some rg -> rg_live rg = true ->
    PGSZ <= ly_reg L r /\ ly_reg L r + rg_len rg <= HTOP /\ ranges_disjoint (ly_reg L r, rg_len rg) (0x10000, 0x87000).

(* [comment removed for export] *)
Definition lext (L L' : layout) (s : astate) : Prop :=
  ly_ctx L' = ly_ctx L /\ ly_brk0 L' = ly_brk0 L /\ ly_sec L' = ly_sec L /\
  forall r, (r < length (st_regions s))%nat -> ly_reg L' r = ly_reg L r.

(* [comment removed for export] *)
Definition in_regs (L : layout) (s : astate) (x : Z) : Prop :=
  exists r rg, region_of s r = Some rg /\ rg_live rg = true /\ rg_kind rg <> RkMap /\ ly_reg L r <= x < ly_reg L r + rg_len rg.

(* [comment removed for export] *)
Definition mframe (sp0 K : Z) (L : layout) (s : astate) (L' : layout) (s' : astate) (m m' : word -> option byte) : Prop :=
  forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) ->
    (sp0 - K <= x < sp0) \/ (in_footprint L' s' x /\ ~ in_user_block L s x) \/ in_regs L' s' x.
End MngMWP.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition slot_end (am : ameta) (i : Z) : sptr := padd (slot_start am i) (stride_of am - IB).
Definition frame_rsv (am : ameta) (fr : frame) : Z := stride_of am - IB - UNIT * fr_off fr - fr_n fr.

(* [comment removed for export] *)
Definition marker_cells (am : ameta) (i : Z) (fr : frame) : list mcell :=
  let e := slot_end am i in
  let r := frame_rsv am fr in
  MCell (LMem e) 1 (VZ 0)
  :: (if 0 <? r then [MCell (LMem (padd e (- r))) 1 (VZ 0)] else [])
  ++ (if 5 <=? r then [MCell (LMem (padd e (-4))) 4 (VZ r); MCell (LMem (padd e (-5))) 1 (VZ 0)] else []).

(* [comment removed for export] *)
Definition gend_cell (am : ameta) : mcell := MCell (LMem (slot_end am (am_last am))) 1 (VZ 0).

(* [comment removed for export] *)
Definition meta_markers (am : ameta) : list mcell :=
  flat_map (fun i => match ss_fr (nth_slot am i) with
                     | Some fr => match fr_kind fr with FUser => marker_cells am i fr | FGroup => [] end
                     | None => [] end) (zseq 0 (am_last am + 1)) ++ [gend_cell am].

Definition markers (s : astate) : list mcell :=
  flat_map (fun gm : sptr * ameta => meta_markers (snd gm)) (used_metas s).

Definition markers_hold (L : layout) (s : astate) (bv : byteview) : Prop := Forall (cell_holds L bv) (markers s).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RB.
Variable segs : list Segment.

#[using="Type"] Lemma holds_rdn : forall L m c, cell_holds L (bview segs m) c -> (forall z, mc_val c <> VLo5 z) -> (mc_w c <= 8)%nat ->
  rdn segs m (wa (loc_addr L (mc_loc c))) (mc_w c) = Some (word_to_le_bytes (mc_w c) (wa (sval_num L (mc_val c)))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L m [l w v] H Hv Hw. cbn [mc_loc mc_w mc_val] in *. rewrite <- ov_rdn. apply cell_ov_read; assumption.
Qed.

#[using="Type"] Lemma repr_rdn : forall L s m c, repr L s (bview segs m) -> In c (image s) ->
  (forall z, mc_val c <> VLo5 z) -> (mc_w c <= 8)%nat ->
  rdn segs m (wa (loc_addr L (mc_loc c))) (mc_w c) = Some (word_to_le_bytes (mc_w c) (wa (sval_num L (mc_val c)))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m c (_ & HC & _) Hin Hv Hw. apply holds_rdn; [|assumption|assumption].
  exact (proj1 (Forall_forall _ _) HC c Hin).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma holds_store_ok : forall L m c, cell_holds L (bview segs m) c -> (forall z, mc_val c <> VLo5 z) ->
  forall d k, 0 <= d -> d + Z.of_nat k <= Z.of_nat (mc_w c) ->
  store_ok segs m (wa (loc_addr L (mc_loc c) + d)) k = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L m c Hc Hv d k Hd. revert d Hd. induction k as [|k IH]; intros d Hd Hk; [reflexivity|].
  cbn [store_ok]. destruct c as [l w v]; cbn [mc_loc mc_w mc_val] in *.
  assert (Hw : wview segs m (wa (loc_addr L l + d)) <> None).
  { assert (Hk' : (Z.to_nat d < w)%nat) by lia.
    pose proof (cell_wview segs L m (MCell l w v) (Z.to_nat d) Hc Hk') as H. cbn [mc_loc mc_w mc_val] in H.
    rewrite Z2Nat.id in H by lia. apply H. destruct v; try exact I. exfalso. eapply Hv. reflexivity. }
  destruct (wview segs m (wa (loc_addr L l + d))) as [b|] eqn:E; [|contradiction].
  rewrite wa_add1. replace (loc_addr L l + d + 1) with (loc_addr L l + (d + 1)) by lia.
  apply IH; lia.
Qed.

End RB.

Lemma size_classes_range : forall sc, 0 <= sc < 48 -> 1 <= znth sc size_classes <= 8191.
Proof.
  intros sc Hsc. unfold znth.
  assert (HF : Forall (fun v => 1 <= v <= 8191) size_classes) by (repeat constructor; lia).
  apply (proj1 (Forall_nth _ _) HF). cbn [length size_classes]. lia.
Qed.

Lemma In_markers : forall s g am i fr c, In (g, am, i, fr) (frames s) -> fr_kind fr = FUser ->
  In c (marker_cells am i fr) -> In c (markers s).
Proof.
  intros s g am i fr c HF Hk Hc. unfold markers, frames in *. apply in_flat_map in HF as [[g' am'] [Hg HF]].
  apply in_flat_map in HF as [j [Hj HF]]. cbn [fst snd] in HF.
  destruct (ss_fr (nth_slot am' j)) as [f|] eqn:Ef; [|destruct HF]. destruct HF as [HF|[]]. injection HF as -> -> -> ->.
  apply in_flat_map. exists (g, am). split; [exact Hg|]. cbn [snd]. unfold meta_markers. apply in_app_iff. left.
  apply in_flat_map. exists i. split; [exact Hj|]. rewrite Ef, Hk. exact Hc.
Qed.

Lemma In_gend : forall s g am, In (g, am) (used_metas s) -> In (gend_cell am) (markers s).
Proof.
  intros s g am Hu. unfold markers. apply in_flat_map. exists (g, am). split; [exact Hu|]. cbn [snd]. unfold meta_markers.
  apply in_app_iff. right. left. reflexivity.
Qed.

Lemma In_markers_inv : forall s c, In c (markers s) ->
  (exists g am i fr, In (g, am, i, fr) (frames s) /\ fr_kind fr = FUser /\ In c (marker_cells am i fr)) \/
  (exists g am, In (g, am) (used_metas s) /\ c = gend_cell am).
Proof.
  intros s c Hc. unfold markers in Hc. apply in_flat_map in Hc as [[g am] [Hu Hc]]. cbn [snd] in Hc. unfold meta_markers in Hc.
  apply in_app_iff in Hc as [Hc|[Hc|[]]].
  - left. apply in_flat_map in Hc as [i [Hi Hc]]. destruct (ss_fr (nth_slot am i)) as [fr|] eqn:Ef; [|destruct Hc].
    destruct (fr_kind fr) eqn:Kf; [|destruct Hc]. exists g, am, i, fr. split; [|split; [exact Kf | exact Hc]].
    unfold frames. apply in_flat_map. exists (g, am). split; [exact Hu|]. apply in_flat_map. exists i. split; [exact Hi|].
    cbn [fst snd]. rewrite Ef. left. reflexivity.
  - right. exists g, am. split; [exact Hu | symmetry; exact Hc].
Qed.

Section SO.
Variable segs : list Segment.

#[using="Type"] Lemma store_ok_of_bytes : forall m a n, (forall j, 0 <= j < n -> wview segs m (wa (a + j)) <> None) ->
  forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok segs m (wa (a + d)) k = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n H d k. revert d. induction k as [|k IH]; intros d Hd Hk; [reflexivity|].
  cbn [store_ok]. destruct (wview segs m (wa (a + d))) as [b|] eqn:E.
  - rewrite wa_add1. replace (a + d + 1) with (a + (d + 1)) by lia. apply IH; lia.
  - exfalso. apply (H d); [lia | exact E].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma holds_wview : forall L m c j, cell_holds L (bview segs m) c -> (forall z, mc_val c <> VLo5 z) ->
  0 <= j < Z.of_nat (mc_w c) -> wview segs m (wa (loc_addr L (mc_loc c) + j)) <> None.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L m c j Hc Hv Hj. pose proof (cell_wview segs L m c (Z.to_nat j) Hc ltac:(lia)) as W.
  rewrite Z2Nat.id in W by lia. apply W. destruct (mc_val c); try exact I. exfalso. eapply Hv. reflexivity.
Qed.
End SO.

Lemma loc_padd : forall L p d, loc_addr L (LMem (padd p d)) = loc_addr L (LMem p) + d.
Proof. intros L [r o] d. cbn. lia. Qed.
