(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsIcptLift.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition HL (mdl : Model) (AA : list (Z * Z)) : word -> bool := mkH (m_vm_lazy mdl) AA.

Lemma page_base_facts : forall a : word,
  U (page_base a) <= U a /\ U a < U (page_base a) + 4096 /\ U (page_base a) mod 4096 = 0
  /\ U (page_base a) = U a / 4096 * 4096.
Proof.
  intros a. (lazymatch goal with |- ?G => let G' := eval unfold page_base, page_base_of, page_size in G in change_no_check G' end). pose proof (u64_range a) as Ha.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (H : 0 <= U a / 4096 * 4096 <= U a) by lia.
  rewrite u_Z2bv by lia. split; [lia|]. split; [lia|]. split; [rewrite Z.mod_mul by lia; reflexivity | reflexivity].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma page_base_same : forall (a b : word) (p : Z),
  p mod 4096 = 0 -> p <= U a < p + 4096 -> p <= U b < p + 4096 -> page_base a = page_base b.
Proof.
  intros a b p Hp Ha Hb. apply bv_eq.
  destruct (page_base_facts a) as (A1 & A2 & A3 & A4). destruct (page_base_facts b) as (B1 & B2 & B3 & B4).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (U a / 4096 = p / 4096) by lia. assert (U b / 4096 = p / 4096) by lia. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma HL_page : forall mdl AA (a b : word), page_base a = page_base b -> HL mdl AA a = HL mdl AA b.
Proof. intros mdl AA a b E. (lazymatch goal with |- ?G => let G' := eval unfold HL, mkH in G in change_no_check G' end). rewrite E. reflexivity. Qed.

Lemma HL_lazy : forall mdl AA (a : word), HL mdl AA a = true -> lzb mdl (U a) = true.
Proof.
  intros mdl AA a H. unfold HL, mkH in H. apply andb_prop in H as [H _]. (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end). rewrite Z_to_bv_bv_unsigned. exact H.
Qed.

Lemma HL_notlazy : forall mdl AA z, 0 <= z < 2 ^ 64 -> lzb mdl z = false -> HL mdl AA (Z_to_bv 64 z) = false.
Proof.
  intros mdl AA z Hz L. destruct (HL mdl AA (Z_to_bv 64 z)) eqn:E; [|reflexivity].
  apply HL_lazy in E. rewrite u_Z2bv in E by lia. congruence.
Qed.

Lemma HL_allowed : forall mdl AA (a : word), page_allowedb AA (page_base a) = true -> HL mdl AA a = false.
Proof. intros mdl AA a A. (lazymatch goal with |- ?G => let G' := eval unfold HL, mkH in G in change_no_check G' end). rewrite A. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). apply andb_false_r. Qed.

(* [comment removed for export] *)
Lemma HL_allowed_page : forall mdl AA lo hi z (y : word),
  range_allowed AA lo hi -> lo <= z < hi -> page_base y = page_base (Z_to_bv 64 z) -> HL mdl AA y = false.
Proof.
  intros mdl AA lo hi z y RA Hz E. apply HL_allowed. rewrite E. apply RA. exact Hz.
Qed.

Lemma lazy_cover_HL : forall mdl AA, lazy_cover (HL mdl AA) (m_vm_lazy mdl) AA.
Proof. intros mdl AA. (lazymatch goal with |- ?G => let G' := eval unfold HL in G in change_no_check G' end). apply lazy_cover_mkH. intros x Hx; exact Hx. Qed.

Section PROPS.
  Context {RC : run_ceil}.
  Variable SEGS : list Segment.
  Variable IA : as_addrs.
  Variable AAINV : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : AAINV_props IA AAINV fsbase SEGS.
  (* [comment removed for export] *)
  Hypothesis SEGS_hull : forall a, find_segment SEGS a 1 <> None -> ia_img_lo IA <= a < ia_img_hi IA.

  (* [comment removed for export] *)
  Lemma lazy_zone : forall Lc FF B C K M mdl z,
    AAINV Lc FF B C K M mdl -> 0 <= z < 2 ^ 64 -> lzb mdl z = true ->
    0 < z < CEIL /\ ~ (ia_img_lo IA <= z < ia_img_hi IA).
  Proof using HP fsbase SEGS.
    intros Lc FF B C K M mdl z AI Hz L. pose proof (aap_lazyzone _ _ _ _ HP _ _ _ _ _ _ _ AI) as FA.
    unfold lzb, page_in_ranges in L. apply existsb_exists in L as (iv & Hin & Hb). rewrite Forall_forall in FA.
    destruct (FA iv Hin) as (A1 & A2 & A3).
    apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
    pose proof (page_base_facts (Z_to_bv 64 z)) as (P1 & P2 & P3 & P4). rewrite u_Z2bv in P1, P2, P4 by lia.
    unfold page_size in B2.
    (* [comment removed for export] *)
    split; [lia|]. intros [I1 I2].
    (* [comment removed for export] *)
    destruct A3 as [A3 | A3]; lia.
  Qed.

  Lemma HL_zone : forall Lc FF B C K M mdl AA z,
    AAINV Lc FF B C K M mdl -> 0 <= z < 2 ^ 64 ->
    (CEIL <= z \/ (ia_img_lo IA <= z < ia_img_hi IA) \/ z = 0) -> HL mdl AA (Z_to_bv 64 z) = false.
  Proof using HP fsbase SEGS.
    intros Lc FF B C K M mdl AA z AI Hz Hr. apply HL_notlazy; [exact Hz|]. destruct (lzb mdl z) eqn:E; [|reflexivity].
    exfalso. pose proof (lazy_zone _ _ _ _ _ _ _ z AI Hz E). lia.
  Qed.

  Lemma HL_off_segments : forall Lc FF B C K M mdl AA,
    AAINV Lc FF B C K M mdl -> H_off_segments SEGS (HL mdl AA).
  Proof using SEGS_hull HP fsbase IA RC.
    intros Lc FF B C K M mdl AA AI a Ha. apply HL_lazy in Ha. pose proof (u64_range a).
    destruct (lazy_zone _ _ _ _ _ _ _ (U a) AI ltac:(lia) Ha) as [Z1 Z2].
    destruct (find_segment SEGS (U a) 1) eqn:E; [|reflexivity]. exfalso. apply Z2. apply SEGS_hull. rewrite E. discriminate.
  Qed.

  (* [comment removed for export] *)
  Lemma HL_block : forall Lc FF B C K M mdl AA z,
    AAINV Lc FF B C K M mdl -> in_blocks Lc z \/ in_frames_full FF z -> 0 <= z < 2 ^ 64 -> HL mdl AA (Z_to_bv 64 z) = false.
  Proof using HP fsbase IA SEGS RC.
    intros Lc FF B C K M mdl AA z AI Hz Hr. apply HL_notlazy; [exact Hr|].
    exact (aap_nolazy _ _ _ _ HP _ _ _ _ _ _ _ z AI Hz).
  Qed.

  (* [comment removed for export] *)
  Lemma hid_off_pointwise : forall (Hd : word -> bool) lo n,
    (forall z, lo <= z < lo + n -> 0 <= z < 2 ^ 64 /\ Hd (Z_to_bv 64 z) = false) -> hid_off Hd lo n.
  Proof using.
    intros Hd lo n F x Hx. destruct (F (U x) Hx) as [R E]. rewrite Z_to_bv_bv_unsigned in E. exact E.
  Qed.
End PROPS.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sh_lo_in : forall p m z, 0 <= p -> p <= z < p + m -> sh_lo p <= sh_lo z < sh_hi p m.
Proof.
  intros p m z Hp Hz. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi in G in change_no_check G' end).
  pose proof (Z.div_mod z 8 ltac:(lia)). pose proof (Z.mod_pos_bound z 8 ltac:(lia)).
  pose proof (Z.div_mod (p + m + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p + m + 7) 8 ltac:(lia)).
  pose proof (Z.div_le_mono p z 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma sh_lo_mono : forall a b, a <= b -> sh_lo a <= sh_lo b.
Proof. intros a b H. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo in G in change_no_check G' end). pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.

Lemma sh_lo_lt47 : forall z, 0 <= z < 2 ^ 47 -> SB <= sh_lo z < SB + 2 ^ 44.
Proof.
  intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo in G in change_no_check G' end). pose proof (Z.div_pos z 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound z 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia.
Qed.


(* [comment removed for export] *)
Lemma page_base_word8 : forall (w : Z) (x y : word),
  w mod 8 = 0 -> 0 <= w -> w <= U x < w + 8 -> w <= U y < w + 8 -> page_base x = page_base y.
Proof.
  intros w x y Hw H0 Hx Hy.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  apply (page_base_same x y (w / 4096 * 4096)); [apply Z.mod_mul; lia | lia | lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma rdn_defined_ex : forall segs (m : word -> option byte) (a : word) (n : nat),
  (forall i, U a <= i < U a + Z.of_nat n -> m (Z_to_bv 64 i) <> None) ->
  U a + Z.of_nat n < 2 ^ 64 ->
  exists bs, rdn segs m a n = Some bs /\ length bs = n.
Proof.
  intros segs m a n. revert a. induction n as [|n IH]; intros a Hdef Hnw.
  - exists []. split; reflexivity.
  - pose proof (u64_range a) as Ha. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end).
    destruct (m a) as [b|] eqn:E.
    2:{ exfalso. apply (Hdef (U a)); [lia|]. rewrite Z_to_bv_bv_unsigned. exact E. }
    destruct (IH (a + 1)%bv) as [bs [Hr Hl]].
    + intros i Hi. apply Hdef. rewrite u_add1 in Hi by lia. lia.
    + rewrite u_add1 by lia. lia.
    + rewrite Hr. exists (b :: bs). split; [reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
Qed.

(* [comment removed for export] *)
Lemma down8_ge : forall x y, y mod 8 = 0 -> y <= x -> y <= down8 x.
Proof. intros x y Hy H. (lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end). pose proof (Z.div_le_mono y x 8 ltac:(lia) H). pose proof (Z.div_mod y 8 ltac:(lia)). lia. Qed.
Lemma down8_lt_top : forall x t, t mod 8 = 0 -> x < t -> down8 x + 8 <= t.
Proof.
  intros x t Ht H. (lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end). pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  pose proof (Z.div_mod t 8 ltac:(lia)). assert (x / 8 < t / 8 \/ x / 8 = t / 8) as [L|E] by (pose proof (Z.div_le_mono x t 8 ltac:(lia) ltac:(lia)); lia); [lia|].
  exfalso. lia.
Qed.
Lemma down8_le : forall x, 0 <= x -> x - 7 <= down8 x <= x /\ down8 x mod 8 = 0.
Proof. intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end). pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). split; [lia | apply Z.mod_mul; lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma munrestrict_mrestrict_same : forall (Hd : word -> bool) (M M' : mem),
  (forall a, Hd a = true -> M' a = M a) -> munrestrict Hd M (mrestrict Hd M') = M'.
Proof.
  intros Hd M M' E. apply functional_extensionality. intros a. (lazymatch goal with |- ?G => let G' := eval unfold munrestrict, mrestrict in G in change_no_check G' end).
  destruct (Hd a) eqn:Ha; [symmetry; apply E; exact Ha | reflexivity].
Qed.

Lemma unrestrict_mkst : forall {fx : FPState} (Hd : word -> bool) (M : mem) regs pc m rom,
  unrestrict Hd M (mkst regs pc m rom) = mkst regs pc (munrestrict Hd M m) rom.
Proof. intros. reflexivity. Qed.

Lemma restrict_mkst' : forall {fx : FPState} (Hd : word -> bool) regs pc m rom,
  restrict Hd (mkst regs pc m rom) = mkst regs pc (mrestrict Hd m) rom.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma store_ok1_defined : forall SEGS (M : mem) (a : word),
  find_segment SEGS (U a) 1 = None -> store_ok SEGS M a 1%nat = true -> M a <> None.
Proof.
  intros SEGS M a NS OK. cbn [store_ok] in OK. unfold wview in OK. destruct (M a) eqn:E; [congruence|].
  rewrite NS in OK. discriminate OK.
Qed.

(* [comment removed for export] *)
Lemma cellN_mrestrict : forall SEGS (Hd : word -> bool) M a n v,
  cellN SEGS M a n v -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> hid_off Hd a (Z.of_nat n) ->
  rdn SEGS (mrestrict Hd M) (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Proof.
  intros SEGS Hd M a n v C Ha Hn HO. unfold cellN in C.
  rewrite rdn_mrestrict; [exact C | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact HO].
Qed.

(* [comment removed for export] *)
Definition saved_regs : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma regs_kept_of_list : forall {fx : FPState} (R R' : bvmap 5 word),
  (forall x : reg, In x saved_regs -> getr R' x = getr R x) -> regs_kept R R'.
Proof.
  intros fx R R' H r Hr. unfold as_callee_saved in Hr. cbn [In] in Hr.
  Ltac inl := (lazymatch goal with |- ?G => let G' := eval unfold saved_regs in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]).
  repeat (destruct Hr as [<- | Hr]; [apply H; inl|]). destruct Hr.
Qed.
End AsIcptLift.
Module AsRtAccess.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma Sh_is_sh_lo : forall a, Sh a = sh_lo a.
Proof. intros a. (lazymatch goal with |- ?G => let G' := eval unfold Sh, sh_lo, SB in G in change_no_check G' end). lia. Qed.

(* [comment removed for export] *)
Lemma rdn1_of_mem : forall segs (M : word -> option byte) (a : word) (k : byte),
  M a = Some k -> rdn segs M a 1%nat = Some [k].
Proof. intros segs M a k H. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end). rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sbyte_cases : forall (k : byte),
  (bv_signed k = 0 -> bv_unsigned k = 0) /\ (0 < bv_signed k <= 7 -> bv_unsigned k = bv_signed k).
Proof.
  intros k. pose proof (bv_unsigned_in_range _ k) as Hr. change (bv_modulus 8) with 256 in Hr.
  (lazymatch goal with |- ?G => let G' := eval unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus in G in change_no_check G' end). change (bv_modulus 8) with 256. change (256 / 2) with 128.
  assert (E : (bv_unsigned k + 128) mod 256 - 128 = (if bv_unsigned k <? 128 then bv_unsigned k else bv_unsigned k - 256)).
  { destruct (Z.ltb_spec (bv_unsigned k) 128).
    - rewrite Z.mod_small by lia. lia.
    - replace (bv_unsigned k + 128) with (bv_unsigned k - 128 + 1 * 256) by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
  rewrite E. destruct (Z.ltb_spec (bv_unsigned k) 128); split; intros; lia.
Qed.

Section ACC.
  Variable segs : list Segment.
  Variable M : word -> option byte.
  Variables b n : Z.
  Hypothesis ACC : accessible M b n.

  (* [comment removed for export] *)
  Lemma acc_byte : forall a, b <= a < b + n ->
    exists k : byte, rdn segs M (Z_to_bv 64 (Sh a)) 1%nat = Some [k]
                     /\ (bv_unsigned k = 0 \/ a mod 8 < bv_unsigned k <= 7).
  Proof using ACC.
    intros a Ha. pose proof (ACC a Ha) as H. rewrite <- Sh_is_sh_lo in H. unfold sbyte in H.
    destruct (M (Z_to_bv 64 (Sh a))) as [k|] eqn:E.
    - exists k. split; [apply rdn1_of_mem; exact E|].
      pose proof (sbyte_cases k) as [C0 C1]. pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
      destruct H as [H|H]; [left; auto | right]. rewrite (C1 ltac:(lia)). lia.
    - exfalso. pose proof (Z.mod_pos_bound a 8 ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma acc_first : 0 < n ->
    exists k : byte, rdn segs M (Z_to_bv 64 (Sh b)) 1%nat = Some [k]
                     /\ (bv_unsigned k = 0 \/ b mod 8 < bv_unsigned k < 128).
  Proof using ACC.
    intros Hn. destruct (acc_byte b ltac:(lia)) as (k & R & K). exists k. split; [exact R | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma acc_last : 0 < n ->
    exists k : byte, rdn segs M (Z_to_bv 64 (Sh (b + n - 1))) 1%nat = Some [k]
                     /\ (bv_unsigned k = 0 \/ (b + n - 1) mod 8 < bv_unsigned k < 128).
  Proof using ACC.
    intros Hn. destruct (acc_byte (b + n - 1) ltac:(lia)) as (k & R & K). exists k. split; [exact R | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma acc_zero_core : 0 <= b -> forall z : word,
    b <= 8 * (bv_unsigned z - 0x7fff8000) + 7 -> 8 * (bv_unsigned z - 0x7fff8000) + 7 < b + n ->
    rdn segs M z 1%nat = Some [Z_to_bv 8 0].
  Proof using ACC.
    intros Hb z Hg1 Hg2. set (g := bv_unsigned z - 0x7fff8000) in *.
    destruct (acc_byte (8 * g + 7) ltac:(lia)) as (k & R & K).
    replace ((8 * g + 7) mod 8) with 7 in K.
    2:{ replace (8 * g + 7) with (7 + g * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
    assert (E : Z_to_bv 64 (Sh (8 * g + 7)) = z).
    { apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). rewrite Z_to_bv_unsigned. pose proof (u64_range z).
      replace ((8 * g + 7) / 8) with g.
      2:{ replace (8 * g + 7) with (7 + g * 8) by lia. rewrite Z.div_add, Z.div_small by lia. lia. }
      (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small; lia. }
    rewrite E in R. rewrite R. f_equal. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 0) with 0. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma acc_zero : 0 <= b -> forall z : word, Sh b <= bv_unsigned z < Sh (b + n - 1) ->
    rdn segs M z 1%nat = Some [Z_to_bv 8 0].
  Proof using ACC.
    intros Hb z Hz. unfold Sh in Hz. apply acc_zero_core; [exact Hb| |].
    - pose proof (Z.div_mod b 8 ltac:(lia)). pose proof (Z.mod_pos_bound b 8 ltac:(lia)). lia.
    - pose proof (Z.div_mod (b + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + n - 1) 8 ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma acc_zero_mid : 0 <= b -> forall z : word, Sh (up8 b) <= bv_unsigned z < Sh (down8 (b + n)) ->
    rdn segs M z 1%nat = Some [Z_to_bv 8 0].
  Proof using ACC.
    intros Hb z Hz. unfold Sh, up8, down8 in Hz. rewrite !Z.div_mul in Hz by lia. apply acc_zero_core; [exact Hb| |].
    - pose proof (Z.div_mod (b + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + 7) 8 ltac:(lia)). lia.
    - pose proof (Z.div_mod (b + n) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + n) 8 ltac:(lia)). lia.
  Qed.
End ACC.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End AsRtAccess.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsSetShIface OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtSetShadow. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsSetShIface OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtSetShadow AsIcptLift.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Lemma setsh_range : forall fsbase f k m,
  0 <= k <= 3 -> 0 <= fsbase -> f mod FS k = 0 -> fsbase + 0x9000 <= f -> f + FS k <= fsbase + FAKE_SIZE ->
  1 <= m -> 8 * m <= FS k ->
  sh_lo f + m <= sh_hi f (FS k) /\ sh_lo fsbase <= sh_lo f /\ sh_hi f (FS k) <= sh_hi fsbase FAKE_SIZE.
Proof.
  intros fsbase f k m Hk Hfs Hmod Hlo Hhi Hm Hm8.
  assert (FSk : FS k = 64 \/ FS k = 128 \/ FS k = 256 \/ FS k = 512).
  { (lazymatch goal with |- ?G => let G' := eval unfold FS in G in change_no_check G' end). assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia. destruct C as [-> | [-> | [-> | ->]]]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
  unfold sh_lo, sh_hi, SB, FAKE_SIZE in *.
  assert (F8 : f mod 8 = 0).
  { pose proof (Z.div_mod f (FS k) ltac:(lia)) as D. rewrite Hmod in D. set (q := f / FS k) in D. clearbody q.
    rewrite D. destruct FSk as [E | [E | [E | E]]]; rewrite E;
    [ replace (64 * q + 0) with ((q * 8) * 8) by lia
    | replace (128 * q + 0) with ((q * 16) * 8) by lia
    | replace (256 * q + 0) with ((q * 32) * 8) by lia
    | replace (512 * q + 0) with ((q * 64) * 8) by lia ]; apply Z.mod_mul; lia. }
  pose proof (Z.div_mod f 8 ltac:(lia)) as Df. rewrite F8 in Df.
  pose proof (Z.div_mod (f + FS k + 7) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (f + FS k + 7) 8 ltac:(lia)) as B1.
  pose proof (Z.div_mod fsbase 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound fsbase 8 ltac:(lia)) as B2.
  pose proof (Z.div_mod (fsbase + 11571200 + 7) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (fsbase + 11571200 + 7) 8 ltac:(lia)) as B3.
  lia.
Qed.

Section CONTRACT.
  Context {fx0 : FPState}.
  Context {RC : run_ceil}.
  Variable SEGS : list Segment.
  Variable FXOK : FPState -> Prop.
  Variable IA : as_addrs.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props IA (AAINVH h) fsbase SEGS.
  Hypothesis SEGS_hull : forall a, find_segment SEGS a 1 <> None -> ia_img_lo IA <= a < ia_img_hi IA.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis IMG_HI : ia_img_hi IA <= AS_LO.
  Hypothesis IMG_LO : 0 <= ia_img_lo IA.
  Hypothesis FSB0 : 0 <= fsbase.
  (* [comment removed for export] *)
  Variable entry : Z.
  Variables g_rms p_rms : Z.
  Variable mset : word.
  Hypothesis RUNFP : forall (fx : FPState) (mem : word -> option byte) rom (addr ra : word) (n : Z) (H : word -> bool) regs,
    rdn SEGS mem (Z_to_bv 64 g_rms) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 p_rms)) ->
    rdn SEGS mem (Z_to_bv 64 p_rms) 8 = Some (word_to_le_bytes 8 mset) ->
    0 <= n -> U addr + n < 2 ^ 64 -> store_ok SEGS mem addr (Z.to_nat n) = true -> ret_ok ra ->
    hid_off H g_rms 8 -> hid_off H p_rms 8 -> hid_off H (U addr) n ->
    getr regs 10 = addr -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 = ra ->
    exists r,
      msteps SEGS (mkst regs (Z_to_bv 64 entry) (mrestrict H mem) rom)
                  (mkst r ra (mrestrict H (wbytes mem addr (repeat (cbyte (Z_to_bv 64 245)) (Z.to_nat n)))) rom)
      /\ getr r 10 = addr /\ regs_agree (fun r => In r setsh_clob) regs r.
  (* [comment removed for export] *)
  Definition setsh_cellsL : list (Z * nat * Z) := [(g_rms, 8%nat, p_rms); (p_rms, 8%nat, U mset)].
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN SEGS M (fst (fst c)) (snd (fst c)) (snd c)) setsh_cellsL.
  Hypothesis CELLS_img : Forall (fun c => ia_img_lo IA <= fst (fst c) /\ fst (fst c) + 8 <= ia_img_hi IA) setsh_cellsL.

  Theorem C_setshadow : SETSHADOW_AT SEGS FXOK IA AAINVH entry.
  Proof using CELLS_img CELLS RUNFP mset p_rms g_rms FSB0 IMG_LO IMG_HI SEGS_wx SEGS_hull HP fsbase.
    (lazymatch goal with |- ?G => let G' := eval unfold SETSHADOW_AT in G in change_no_check G' end).
    intros h fx R M mdl Lc FF B C K ret sp f k m HFX HH AI CP HIN Ha0 Ha1 Hm1 Hm8.
    pose proof (HP h) as HPh.
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk).
    destruct (aap_lazy _ _ _ _ HPh _ _ _ _ _ _ _ AI) as (AA & Awf & MI & SHCok & BLKok & PRES).
    set (Hd := HL mdl AA).
    pose proof (HL_off_segments SEGS IA (AAINVH h) fsbase HPh SEGS_hull _ _ _ _ _ _ _ AA AI) as HOFF; fold Hd in HOFF.
    pose proof (@ceil_rng RC) as CR.
    pose proof (aap_fzone _ _ _ _ HPh _ _ _ _ _ _ _ f k AI HIN) as (K1 & (K2 & K2b & K2c & K2d) & K3 & K4 & K5).
    pose proof (aap_cells _ _ _ _ HPh _ _ _ _ _ _ _ AI) as (_ & FRM & _ & _).
    unfold KMAXCLASS in K1.
    destruct (setsh_range fsbase f k m K1 FSB0 K3 K4 K5 Hm1 Hm8) as (G1 & G2 & G3).
    assert (NZ : forall z, 0 <= z < 2 ^ 64 -> (ia_img_lo IA <= z < ia_img_hi IA) \/ CEIL <= z -> Hd (Z_to_bv 64 z) = false)
      by (intros z Hz Hr; apply (HL_zone SEGS IA (AAINVH h) fsbase HPh _ _ _ _ _ _ _ AA z AI Hz); tauto).
    assert (SHA : range_allowed AA (sh_lo fsbase) (sh_hi fsbase FAKE_SIZE)) by (apply SHCok; (lazymatch goal with |- ?G => let G' := eval unfold SHC in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
    assert (NSHD : forall z, sh_lo f <= z < sh_lo f + m -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply (HL_allowed_page mdl AA (sh_lo fsbase) (sh_hi fsbase FAKE_SIZE) z (Z_to_bv 64 z) SHA); [|reflexivity].
      clear - Hz G1 G2 G3. lia. }
    assert (FSP : 0 < FS k) by (clear - K1; (lazymatch goal with |- ?G => let G' := eval unfold FS in G in change_no_check G' end); pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)); lia).
    (* [comment removed for export] *)
    assert (SHR : SB <= sh_lo f /\ sh_lo f + m < SB + 2 ^ 44).
    { pose proof (sh_lo_lt47 f) as X. unfold PTRLO, AS_LO, AS_HEAPLO, SB in *. 
      assert (F47 : 0 <= f < 2 ^ 47) by (clear - K2 K2b CR FSP; unfold PTRLO in *; lia).
      specialize (X F47). unfold sh_hi, sh_lo, SB in *.
      pose proof (Z.div_le_mono (f + FS k + 7) 140737479966727 8 ltac:(lia) ltac:(clear - K2b CR; lia)) as W.
      change (140737479966727 / 8) with 17592184995840 in W. clear - X W G1. lia. }
    set (addrw := getr R 10) in *; set (spw := getr R 2) in *.
    pose proof (u64_range addrw) as Har; pose proof (u64_range spw) as Hsr.
    assert (R11 : getr R 11 = Z_to_bv 64 m) by (apply bv_eq; rewrite u_Z2bv by (clear - SHR Hm1; unfold SB in *; lia); exact Ha1).
    assert (RET : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_even; rewrite u_Z2bv by lia; exact CPe).
    set (raw := Z_to_bv 64 ret) in *.
    (* [comment removed for export] *)
    pose proof (CELLS _ _ _ _ _ _ _ _ AI) as CE; pose proof CELLS_img as CI; unfold setsh_cellsL in CE, CI.
    apply Forall_cons_iff in CE; destruct CE as [C1 CE]. apply Forall_cons_iff in CE; destruct CE as [C2 _].
    apply Forall_cons_iff in CI; destruct CI as [D1 CI]. apply Forall_cons_iff in CI; destruct CI as [D2 _].
    cbn [fst snd] in *.
    unfold cellN in C1, C2. rewrite Z_to_bv_bv_unsigned in C2.
    assert (HG : hid_off Hd g_rms 8).
    { apply hid_off_pointwise; intros zz Hzz; split; [clear - Hzz D1 IMG_HI IMG_LO; unfold AS_LO in *; lia | apply NZ; [clear - Hzz D1 IMG_HI IMG_LO; unfold AS_LO in *; lia | left; clear - Hzz D1; lia]]. }
    assert (HPc : hid_off Hd p_rms 8).
    { apply hid_off_pointwise; intros zz Hzz; split; [clear - Hzz D2 IMG_HI IMG_LO; unfold AS_LO in *; lia | apply NZ; [clear - Hzz D2 IMG_HI IMG_LO; unfold AS_LO in *; lia | left; clear - Hzz D2; lia]]. }
    assert (HA : hid_off Hd (U addrw) m).
    { rewrite Ha0. apply hid_off_pointwise; intros zz Hzz; split; [clear - Hzz SHR; unfold SB in *; lia | apply NSHD; exact Hzz]. }
    (* [comment removed for export] *)
    assert (WV : forall (mm : mem) (x : word), store_ok SEGS mm x 1%nat = true -> wview SEGS mm x <> None).
    { intros mm x Hx. cbn [store_ok] in Hx. destruct (wview SEGS mm x); [discriminate | discriminate Hx]. }
    assert (DOK : store_ok SEGS M addrw (Z.to_nat m) = true).
    { apply store_ok_of_all; [rewrite Z2Nat.id by lia; clear - Ha0 SHR; unfold SB in *; lia|].
      intros x Hx. rewrite Z2Nat.id in Hx by lia. apply WV.
      replace x with (Z_to_bv 64 (U x)) by apply Z_to_bv_bv_unsigned.
      apply (proj2 (FRM f k (U x) HIN ltac:(right; clear - Hx Ha0 G1; lia))). }
    (* [comment removed for export] *)
    destruct (RUNFP fx M (seg_rom SEGS) addrw raw m Hd R C1 C2 ltac:(lia) ltac:(clear - Ha0 SHR; unfold SB in *; lia) DOK RET HG HPc HA eq_refl R11 CP1)
      as (r & RUN & A10 & AG).
    set (M' := wbytes M addrw (repeat (cbyte (Z_to_bv 64 245)) (Z.to_nat m))) in *.
    assert (OUT : forall a : word, ~ (sh_lo f <= U a < sh_lo f + m) -> M' a = M a).
    { intros a Na. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply MemsetLibF.Frame.wbytes_outside; rewrite repeat_length, Z2Nat.id by lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end). rewrite Ha0. exact Na.
      - clear - Ha0 SHR. unfold SB in *. lia. }
    assert (GRW : mem_grows M M') by (apply wbytes_grows).
    assert (SOME : forall a : word, M' a <> M a -> M' a <> None).
    { intros a Ha. destruct (decide (sh_lo f <= U a < sh_lo f + m)) as [IN | NIN]; [|exfalso; apply Ha; apply OUT; exact NIN].
      apply GRW. replace a with (Z_to_bv 64 (U a)) by apply Z_to_bv_bv_unsigned.
      apply (proj1 (FRM f k (U a) HIN ltac:(right; clear - IN G1; lia))). }
    assert (CHG : forall a : word, M' a <> M a -> sh_lo f <= U a < sh_lo f + m).
    { intros a Ha. destruct (decide (sh_lo f <= U a < sh_lo f + m)) as [IN | NIN]; [exact IN | exfalso; apply Ha; apply OUT; exact NIN]. }
    assert (NH' : forall a : word, Hd a = true -> M' a = M a).
    { intros a Ha. destruct (decide (M' a = M a)) as [E|NE]; [exact E|]. exfalso.
      rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ha. rewrite (NSHD (U a) (CHG a NE)) in Ha. discriminate Ha. }
    assert (SEGnone : forall a : word, CEIL <= U a -> find_segment SEGS (U a) 1 = None).
    { intros a Ha. destruct (find_segment SEGS (U a) 1) eqn:FSE; [|reflexivity]. exfalso.
      pose proof (SEGS_hull (U a) ltac:(rewrite FSE; discriminate)) as SH. clear - Ha SH IMG_HI CR. unfold AS_LO in *. lia. }
    (* [comment removed for export] *)
    (lazymatch goal with |- ?G => let G' := eval unfold AsIface3.cfg in G in change_no_check G' end).
    apply (katD_msteps_acct SEGS Hd HOFF SEGS_wx AA (mkst R (Z_to_bv 64 entry) M (seg_rom SEGS))
             (mkst r raw (mrestrict Hd M') (seg_rom SEGS)) mdl _ (lazy_cover_HL mdl AA) Awf MI HH).
    { rewrite restrict_mkst'. exact RUN. }
    intros mdl' MI' SBM HC. rewrite unrestrict_mkst. (lazymatch goal with |- ?G => let G' := eval cbn [RiscvSemantics.ms_mem mkst] in G in change_no_check G' end).
    rewrite (munrestrict_mrestrict_same Hd M M' NH').
    apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold setsh_post in G in change_no_check G' end). exists fx, r, M', mdl'.
    assert (LZ : m_vm_lazy mdl' = m_vm_lazy mdl) by (rewrite SBM; destruct mdl; reflexivity).
    assert (HALT : m_halted mdl' = None) by (rewrite SBM; destruct mdl; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact HH).
    split; [reflexivity|]. split; [exact HFX|].
    split. { apply regs_kept_of_list. intros x Hx. apply AG. (lazymatch goal with |- ?G => let G' := eval unfold setsh_clob in G in change_no_check G' end). unfold saved_regs in Hx. cbn [In] in Hx |- *.
             intros Hc. repeat (destruct Hx as [<- | Hx]; [repeat (destruct Hc as [Hc | Hc]; [discriminate Hc|]); exact Hc |]). exact Hx. }
    split. { intros a Ha. left. exact (CHG a Ha). }
    split. { exact SOME. }
    split. { intros a Ha. unfold MSTK_SF in Ha. split.
             - apply GRW. apply (store_ok1_defined SEGS M a); [apply SEGnone; clear - Ha CPlo; unfold MSTK_SF in *; lia | apply CPstk; exact Ha].
             - eapply store_ok_mono; [exact GRW | apply CPstk; exact Ha]. }
    split. { apply (aap_frame _ _ _ _ HPh [] Lc FF B C K M M' mdl').
             - intros a (lo & hi & Hin & _). destruct Hin.
             - exact (PRES mdl' MI' SBM).
             - intros a Ha. split; [|exact (SOME a Ha)].
               right. right. right. right. right. left. exists f, k. split; [exact HIN|]. pose proof (CHG a Ha) as X. clear - X G1. lia. }
    split. { exact (same_except_vm_of_materialized _ _ SBM). }
    split. { intros a _. (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end). rewrite LZ. reflexivity. }
    exact HALT.
  Qed.
End CONTRACT.
