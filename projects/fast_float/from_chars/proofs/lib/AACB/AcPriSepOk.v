(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxMem FxFacts FxStep FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChNull FxChFix FxWvC FxChTwoC.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_nf1 AXG_nf2.

Module AcFast.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChLib FxChSep FxChNull FxChFix FxChFixNew.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint syn_grant_acc (fs : list fact) (gs : list (lin * lin * gkind)) (j i : nat) (b : lin) (z : Z) : bool :=
  match gs with
  | [] => false
  | g :: r => (negb (is_mark g) &&& negb (Nat.eqb i j) &&& match lin_off b (fst (fst g)) with Some d => (Z.leb 0 d && Z.leb (d + z) (gsz_lo fs g))%bool | None => false end)
              ||| syn_grant_acc fs r j (Datatypes.S i) b z       (* [comment removed for export] *)
  end.
Definition syn_grant (fs : list fact) (gs : list (lin * lin * gkind)) (j : nat) (R : region) : bool :=
  match is_const (rg_size R) with Some z => Z.leb 1 z &&& syn_grant_acc fs gs j O (rg_base R) z | None => false end.

Lemma syn_grant_acc_sound : forall fs gs j i R z, is_const (rg_size R) = Some z -> 1 <= z ->
  syn_grant_acc fs gs j i (rg_base R) z = true -> sep_grant_acc fs gs j i R = true.
Proof.
  intros fs gs j. induction gs as [|g r IH]; intros i R z Hz Hz1 H; cbn [syn_grant_acc] in H; [discriminate|].
  cbn [sep_grant_acc]. unfold irange. rewrite Hz. cbn [snd].
  destruct (negb (is_mark g)); destruct (negb (Nat.eqb i j)); try exact (IH (Datatypes.S i) R z Hz Hz1 H).
  destruct (lin_off (rg_base R) (fst (fst g))) as [d|] eqn:Ed.
  - destruct (Z.leb 0 d && Z.leb (d + z) (gsz_lo fs g))%bool eqn:Ec.
    + unfold contained_b. rewrite Ed, Ec. apply Z.leb_le in Hz1. rewrite Hz1. reflexivity.
    + rewrite (IH (Datatypes.S i) R z Hz Hz1 H). match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
  - rewrite (IH (Datatypes.S i) R z Hz Hz1 H). match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
Qed.

(* [comment removed for export] *)
Fixpoint syn_pgrant_acc (fs : list fact) (gs : list (lin * lin * gkind)) (j i : nat) (b : lin) (z : Z) : bool :=
  match gs with
  | [] => false
  | g :: r => (negb (is_mark g) &&& negb (Nat.eqb i j) &&& match srl_lin fs 3 (fst (fst g)) with
                                     | Some pb => match lin_off b (laddc pb SH_OFF) with Some d => (Z.leb 0 d && Z.leb (d + z) (gsz_lo fs g / 8))%bool | None => false end
                                     | None => false
                                     end)
              ||| syn_pgrant_acc fs r j (Datatypes.S i) b z
  end.
Definition syn_pgrant (fs : list fact) (gs : list (lin * lin * gkind)) (j : nat) (R : region) : bool :=
  match is_const (rg_size R) with Some z => Z.leb 1 z &&& syn_pgrant_acc fs gs j O (rg_base R) z | None => false end.

Lemma syn_pgrant_acc_sound : forall fs gs j i R z, is_const (rg_size R) = Some z -> 1 <= z ->
  syn_pgrant_acc fs gs j i (rg_base R) z = true -> sep_pgrant_acc fs gs j i R = true.
Proof.
  intros fs gs j. induction gs as [|g r IH]; intros i R z Hz Hz1 H; cbn [syn_pgrant_acc] in H; [discriminate|].
  cbn [sep_pgrant_acc]. unfold irange. rewrite Hz. cbn [snd].
  destruct (negb (is_mark g)); destruct (negb (Nat.eqb i j)); try exact (IH (Datatypes.S i) R z Hz Hz1 H).
  destruct (srl_lin fs 3 (fst (fst g))) as [pb|] eqn:Ep.
  - destruct (lin_off (rg_base R) (laddc pb SH_OFF)) as [d|] eqn:Ed.
    + destruct (Z.leb 0 d && Z.leb (d + z) (gsz_lo fs g / 8))%bool eqn:Ec.
      * unfold contained_b. rewrite Ed, Ec. apply Z.leb_le in Hz1. rewrite Hz1. reflexivity.
      * rewrite (IH (Datatypes.S i) R z Hz Hz1 H). match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
    + rewrite (IH (Datatypes.S i) R z Hz Hz1 H). match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
  - rewrite (IH (Datatypes.S i) R z Hz Hz1 H). match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
Qed.

Lemma syn_grant_sound : forall fs gs j R, syn_grant fs gs j R = true -> sep_grant_acc fs gs j O R = true.
Proof.
  intros fs gs j R H. unfold syn_grant in H. destruct (is_const (rg_size R)) as [z|] eqn:Hz; [|discriminate].
  destruct (Z.leb 1 z) eqn:E1; [|discriminate]. apply Z.leb_le in E1. exact (syn_grant_acc_sound fs gs j O R z Hz E1 H).
Qed.
Lemma syn_pgrant_sound : forall fs gs j R, syn_pgrant fs gs j R = true -> sep_pgrant_acc fs gs j O R = true.
Proof.
  intros fs gs j R H. unfold syn_pgrant in H. destruct (is_const (rg_size R)) as [z|] eqn:Hz; [|discriminate].
  destruct (Z.leb 1 z) eqn:E1; [|discriminate]. apply Z.leb_le in E1. exact (syn_pgrant_acc_sound fs gs j O R z Hz E1 H).
Qed.

(* [comment removed for export] *)
Definition fast_app2 (fs : list fact) (gs : list (lin * lin * gkind)) (j : nat) (sp a : lin) (n : Z) (R : region) : bool :=
  syn_grant fs gs j R ||| sep_band_b fs sp R ||| (sep_noshadow_b fs (RGz a n RZ TEmpty) &&& sep_shadow_b fs R) ||| sep_app2_b fs gs j sp a n R.
Lemma fast_app2_eq : forall fs gs j sp a n R, fast_app2 fs gs j sp a n R = sep_app2_b fs gs j sp a n R.
Proof.
  intros fs gs j sp a n R. unfold fast_app2. rewrite !sep_app2_b_eq.
  destruct (syn_grant fs gs j R) eqn:Hs; [rewrite (syn_grant_sound fs gs j R Hs); reflexivity|].
  destruct (sep_band_b fs sp R), (sep_grant_acc fs gs j O R), (sep_noshadow_b fs (RGz a n RZ TEmpty)), (sep_shadow_b fs R); reflexivity.
Qed.
Definition fast_pc (fs : list fact) (gs : list (lin * lin * gkind)) (j : nat) (sp : lin) (R : region) : bool :=
  syn_pgrant fs gs j R ||| sep_noshadow_b fs R ||| sep_pband_b fs sp R ||| sep_pc_b fs gs j sp R.
Lemma fast_pc_eq : forall fs gs j sp R, fast_pc fs gs j sp R = sep_pc_b fs gs j sp R.
Proof.
  intros fs gs j sp R. unfold fast_pc. rewrite !sep_pc_b_eq.
  destruct (syn_pgrant fs gs j R) eqn:Hs; [rewrite (syn_pgrant_sound fs gs j R Hs); reflexivity|].
  destruct (sep_noshadow_b fs R), (sep_pband_b fs sp R), (sep_pgrant_acc fs gs j O R); reflexivity.
Qed.

Lemma forallb_eq : forall {A} (f g : A -> bool) l, (forall x, f x = g x) -> forallb f l = forallb g l.
Proof. intros A f g l H. induction l as [|x l IH]; [reflexivity|]. cbn [forallb]. rewrite H, IH. reflexivity. Qed.

(* [comment removed for export] *)
Definition fk_body (res : list (word * word)) (fs : list fact) (M : smodel) (j : nat) (a : lin) (n : Z) (na : bool) (R : region) : bool :=
  rgs_sep fs a n R ||| sep_app2_b fs (sm_maps M) j (sm_sp M) a n R ||| sep_res_b res R ||| sep_rb_b fs (sm_maps M) j (sm_sp M) a R |||
  (negb na &&& (zero_ov fs a n R ||| zero_ov2 fs a n R)).
Definition fk_body_f (res : list (word * word)) (fs : list fact) (M : smodel) (j : nat) (a : lin) (n : Z) (na : bool) (R : region) : bool :=
  sep_res_b res R ||| rgs_sep fs a n R ||| fast_app2 fs (sm_maps M) j (sm_sp M) a n R ||| fk_body res fs M j a n na R.
Lemma fk_body_f_eq : forall res fs M j a n na R, fk_body_f res fs M j a n na R = fk_body res fs M j a n na R.
Proof.
  intros res fs M j a n na R. unfold fk_body_f, fk_body. rewrite fast_app2_eq.
  destruct (sep_res_b res R), (rgs_sep fs a n R), (sep_app2_b fs (sm_maps M) j (sm_sp M) a n R); reflexivity.
Qed.

Definition fixkeep_ok_f (LIMIT : Z) (res : list (word * word)) (L : sst) (M : smodel) (n : Z) (na : bool) (j : nat) (kd' : gkind) : bool :=
  let fs := s_facts L in let a := rget (s_regs L) (rkey a0r) in let ln := rget (s_regs L) (rkey a1r) in
  match a7c L, arg L 2, arg L 3, arg L 5, nth_error (sm_maps M) j with
  | Some c7, Some prot, Some flags, Some off, Some g =>
      (Z.eqb c7 222 && mmap_off_aligned_b (Z_to_bv 64 off) && mmap_anon_b (Z_to_bv 64 flags) && len_ok fs ln n &&
       negb (mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)) &&
       negb (mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)) &&
       (if na then mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)
        else negb (mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off))
             && mmap_fixed_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)) &&
       contained_b fs a n (fst (fst g)) (gsz_lo fs g) && lal_ok a (fst (fst g)) &&
       (gkind_eqb kd' GE || (gkind_eqb kd' (snd g) && negb (gkind_eqb kd' GN) && (na || mmap_noreserve_b (Z_to_bv 64 flags)))) &&
       (forallb (fk_body_f res fs M j a n na) (s_rgs L) ||| (negb na &&& existsb (zero_ov fs a n) (s_rgs L))) && Z.ltb n 4611686018427387904 &&
       (negb (mmap_noreserve_b (Z_to_bv 64 flags)) || allow_cov fs a n (sm_allow M)) &&
       (negb na || zr_sep_g fs (sm_maps M) j a n (sm_zr M)) && lwf (s_next L) a &&
       Z.leb (eager_sum (s_facts L) (set_kind j kd' (sm_maps M)) + allow_bound (sm_allow M)) LIMIT &&
       Z.leb (eager_sum (s_facts L) (sm_maps M) + allow_bound (sm_allow M) + (Z.of_nat (length (sm_maps M)) + mark_len (s_facts L) (sm_maps M)) * n) LIMIT &&
       negb (is_mark g))%bool        (* [comment removed for export] *)
  | _, _, _, _, _ => false
  end.

Lemma fixkeep_ok_f_eq : forall LIMIT res L M n na j kd', fixkeep_ok_f LIMIT res L M n na j kd' = fixkeep_ok LIMIT res L M n na j kd'.
Proof.
  intros LIMIT res L M n na j kd'. unfold fixkeep_ok_f, fixkeep_ok. cbv zeta.
  destruct (a7c L), (arg L 2), (arg L 3), (arg L 5), (nth_error (sm_maps M) j); try reflexivity.
  rewrite (forallb_eq _ _ _ (fk_body_f_eq res (s_facts L) M j (rget (s_regs L) (rkey a0r)) n na)). unfold fk_body. rewrite existsb_lz_eq.
  destruct (forallb _ (s_rgs L)), (negb na &&& existsb (zero_ov (s_facts L) (rget (s_regs L) (rkey a0r)) n) (s_rgs L)); reflexivity.
Qed.

Definition fn_body (res : list (word * word)) (fs : list fact) (M : smodel) (j : nat) (a pb : lin) (n : Z) (R : region) : bool :=
  (rgs_sep fs a n R ||| sep_app2_b fs (sm_maps M) j (sm_sp M) a n R ||| sep_res_b res R) &&&
  (rgs_sep fs (laddc pb SH_OFF) (n / 8) R ||| sep_pc_b fs (sm_maps M) j (sm_sp M) R ||| sep_pres_b res R).
Definition fn_body_f (res : list (word * word)) (fs : list fact) (M : smodel) (j : nat) (a pb : lin) (n : Z) (R : region) : bool :=
  (sep_res_b res R ||| rgs_sep fs a n R ||| fast_app2 fs (sm_maps M) j (sm_sp M) a n R) &&&
  (sep_pres_b res R ||| rgs_sep fs (laddc pb SH_OFF) (n / 8) R ||| fast_pc fs (sm_maps M) j (sm_sp M) R).
Lemma fn_body_f_eq : forall res fs M j a pb n R, fn_body_f res fs M j a pb n R = fn_body res fs M j a pb n R.
Proof.
  intros res fs M j a pb n R. unfold fn_body_f, fn_body. rewrite fast_app2_eq, fast_pc_eq.
  destruct (sep_res_b res R), (rgs_sep fs a n R), (sep_app2_b fs (sm_maps M) j (sm_sp M) a n R),
           (sep_pres_b res R), (rgs_sep fs (laddc pb SH_OFF) (n / 8) R), (sep_pc_b fs (sm_maps M) j (sm_sp M) R); reflexivity.
Qed.

Definition fixnew_ok_f (LIMIT : Z) (res : list (word * word)) (L : sst) (M : smodel) (n : Z) (j : nat) : bool :=
  let fs := s_facts L in let a := rget (s_regs L) (rkey a0r) in
  match arg L 3, srl_lin fs 3 a, arg L 1 with
  | Some flags, Some pb, Some len =>
      (fixkeep_ok_f LIMIT res L M n false j GE && Z.eqb n (page_round_up_Z len) && Z.ltb 0 len && negb (mmap_noreserve_b (Z_to_bv 64 flags)) &&
       forallb (fn_body_f res fs M j a pb n) (s_rgs L) &&
       Z.leb (fact_hi fs (laddc a (- SH_HI)) (snd (irange fs (laddc a (- SH_HI))))) (two64 + SH_LO - n - SH_HI) && Z.leb 4096 (fst (irange fs a)) &&
       Z.leb (snd (irange fs a) + n) TOPW && shadow_ok M && zr_ok M && lwf (s_next L) pb &&
       Z.leb (eager_sum fs (set_kind j GE (sm_maps M)) + allow_bound ((laddc pb SH_OFF, n / 8) :: sm_allow M)) LIMIT)%bool
  | _, _, _ => false
  end.

Lemma fixnew_ok_f_eq : forall LIMIT res L M n j, fixnew_ok_f LIMIT res L M n j = fixnew_ok LIMIT res L M n j.
Proof.
  intros LIMIT res L M n j. unfold fixnew_ok_f, fixnew_ok. cbv zeta.
  destruct (arg L 3), (srl_lin (s_facts L) 3 (rget (s_regs L) (rkey a0r))) as [pb|], (arg L 1); try reflexivity.
  rewrite fixkeep_ok_f_eq. rewrite (forallb_eq _ _ _ (fn_body_f_eq res (s_facts L) M j (rget (s_regs L) (rkey a0r)) pb n)). unfold fn_body. reflexivity.
Qed.

(* [comment removed for export] *)
Definition img_sep_f (fs : list fact) (gs : list (lin * lin * gkind)) (j0 : nat) (sp : lin) (R : region) : bool :=
  match is_const (rg_base R), is_const (rg_size R) with
  | Some b, Some z => ((Z.leb (b + z) DF_LO || Z.leb DF_HI b) && (Z.leb (b + z) DT_LO || Z.leb DT_HI b))%bool
  | _, _ => syn_grant fs gs j0 R ||| sep_band_b fs sp R ||| sep_shadow_b fs R ||| sep_grant_acc fs gs j0 O R
  end.
Lemma img_sep_f_eq : forall fs gs j0 sp R, img_sep_f fs gs j0 sp R = img_sep_b fs gs j0 sp R.
Proof.
  intros fs gs j0 sp R. unfold img_sep_f, img_sep_b. destruct (is_const (rg_base R)), (is_const (rg_size R)); try reflexivity;
  (destruct (syn_grant fs gs j0 R) eqn:Hs; [rewrite (syn_grant_sound fs gs j0 R Hs); reflexivity|]);
  destruct (sep_band_b fs sp R), (sep_shadow_b fs R), (sep_grant_acc fs gs j0 O R); reflexivity.
Qed.
Definition dep_sep_f (fs : list fact) (gs : list (lin * lin * gkind)) (res : list (word * word)) (jD1 jB1 : nat) (sp D1l B1l : lin)
    (R : region) : bool :=
  (img_sep_f fs gs jD1 sp R && (sep_res_b res R ||| fast_app2 fs gs jD1 sp D1l 1048576 R) &&
   (sep_res_b res R ||| fast_app2 fs gs jB1 sp B1l 8388608 R))%bool.
Lemma dep_sep_f_eq : forall fs gs res jD1 jB1 sp D1l B1l R, dep_sep_f fs gs res jD1 jB1 sp D1l B1l R = dep_sep_b fs gs res jD1 jB1 sp D1l B1l R.
Proof.
  intros fs gs res jD1 jB1 sp D1l B1l R. unfold dep_sep_f, dep_sep_b. rewrite img_sep_f_eq, !fast_app2_eq.
  destruct (sep_res_b res R), (sep_app2_b fs gs jD1 sp D1l 1048576 R), (sep_app2_b fs gs jB1 sp B1l 8388608 R); reflexivity.
Qed.

(* [comment removed for export] *)
Definition few_t (l : lin) : bool := match l_t l with _ :: _ :: _ :: _ => false | _ => true end.
Fixpoint cont_acc (fs : list fact) (gs : list (lin * lin * gkind)) (j1 j2 i : nat) (b : lin) (z : Z) : bool :=
  match gs with
  | [] => false
  | g :: r => (negb (is_mark g) &&& negb (Nat.eqb i j1) &&& negb (Nat.eqb i j2) &&&
               (match lin_off b (fst (fst g)) with Some _ => true | None => few_t (lsub b (fst (fst g))) end) &&&
               contained_b fs b z (fst (fst g)) (gsz_lo fs g)) ||| cont_acc fs r j1 j2 (Datatypes.S i) b z
  end.
Definition cont_b (fs : list fact) (gs : list (lin * lin * gkind)) (j1 j2 : nat) (R : region) : bool :=
  let zhi := snd (irange fs (rg_size R)) in Z.leb 1 zhi &&& cont_acc fs gs j1 j2 O (rg_base R) zhi.
Lemma cont_acc_sep : forall fs gs j1 j2 i R, Z.leb 1 (snd (irange fs (rg_size R))) = true ->
  cont_acc fs gs j1 j2 i (rg_base R) (snd (irange fs (rg_size R))) = true ->
  sep_grant_acc fs gs j1 i R = true /\ sep_grant_acc fs gs j2 i R = true.
Proof.
  intros fs gs j1 j2. induction gs as [|g r IH]; intros i R Hz H; cbn [cont_acc] in H; [discriminate|]. cbn [sep_grant_acc]. rewrite Hz.
  destruct (negb (is_mark g)) eqn:Hm.
  - destruct (negb (Nat.eqb i j1)) eqn:H1; destruct (negb (Nat.eqb i j2)) eqn:H2; cbn in H |- *;
      try (destruct (IH (Datatypes.S i) R Hz H) as [A B]; rewrite ?A, ?B; split;
           match goal with |- (if ?c then true else true) = true => destruct c; reflexivity | |- _ => reflexivity end).
    destruct (match lin_off (rg_base R) (fst (fst g)) with Some _ => true | None => few_t (lsub (rg_base R) (fst (fst g))) end); cbn in H.
    + destruct (contained_b fs (rg_base R) (snd (irange fs (rg_size R))) (fst (fst g)) (gsz_lo fs g)); [split; reflexivity|].
      destruct (IH (Datatypes.S i) R Hz H) as [A B]. rewrite A, B. split; reflexivity.
    + destruct (IH (Datatypes.S i) R Hz H) as [A B]. rewrite A, B.
      split; match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
  - cbn in H |- *. exact (IH (Datatypes.S i) R Hz H).
Qed.
Lemma cont_b_sep : forall fs gs j1 j2 R, cont_b fs gs j1 j2 R = true -> sep_grant_acc fs gs j1 O R = true /\ sep_grant_acc fs gs j2 O R = true.
Proof.
  intros fs gs j1 j2 R H. unfold cont_b in H. cbv zeta in H. destruct (Z.leb 1 (snd (irange fs (rg_size R)))) eqn:Hz; [|discriminate].
  exact (cont_acc_sep fs gs j1 j2 O R Hz H).
Qed.

(* [comment removed for export] *)
Fixpoint cont_accm (md : bool) (fs : list fact) (gs : list (lin * lin * gkind)) (j1 j2 i : nat) (b : lin) (z : Z) : bool :=
  match gs with
  | [] => false
  | g :: r => (negb (is_mark g) &&& negb (Nat.eqb i j1) &&& negb (Nat.eqb i j2) &&&
               (match lin_off b (fst (fst g)) with Some _ => md | None => if md then false else few_t (lsub b (fst (fst g))) end) &&&
               contained_b fs b z (fst (fst g)) (gsz_lo fs g)) ||| cont_accm md fs r j1 j2 (Datatypes.S i) b z
  end.
Definition cont_bm (md : bool) (fs : list fact) (gs : list (lin * lin * gkind)) (j1 j2 : nat) (R : region) : bool :=
  let zhi := snd (irange fs (rg_size R)) in Z.leb 1 zhi &&& cont_accm md fs gs j1 j2 O (rg_base R) zhi.
Lemma cont_accm_sep : forall md fs gs j1 j2 i R, Z.leb 1 (snd (irange fs (rg_size R))) = true ->
  cont_accm md fs gs j1 j2 i (rg_base R) (snd (irange fs (rg_size R))) = true ->
  sep_grant_acc fs gs j1 i R = true /\ sep_grant_acc fs gs j2 i R = true.
Proof.
  intros md fs gs j1 j2. induction gs as [|g r IH]; intros i R Hz H; cbn [cont_accm] in H; [discriminate|]. cbn [sep_grant_acc]. rewrite Hz.
  destruct (negb (is_mark g)) eqn:Hm.
  - destruct (negb (Nat.eqb i j1)) eqn:H1; destruct (negb (Nat.eqb i j2)) eqn:H2; cbn in H |- *;
      try (destruct (IH (Datatypes.S i) R Hz H) as [A B]; rewrite ?A, ?B; split;
           match goal with |- (if ?c then true else true) = true => destruct c; reflexivity | |- _ => reflexivity end).
    destruct (match lin_off (rg_base R) (fst (fst g)) with Some _ => md | None => if md then false else few_t (lsub (rg_base R) (fst (fst g))) end); cbn in H.
    + destruct (contained_b fs (rg_base R) (snd (irange fs (rg_size R))) (fst (fst g)) (gsz_lo fs g)); [split; reflexivity|].
      destruct (IH (Datatypes.S i) R Hz H) as [A B]. rewrite A, B. split; reflexivity.
    + destruct (IH (Datatypes.S i) R Hz H) as [A B]. rewrite A, B.
      split; match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
  - cbn in H |- *. exact (IH (Datatypes.S i) R Hz H).
Qed.
Lemma cont_bm_sep : forall md fs gs j1 j2 R, cont_bm md fs gs j1 j2 R = true -> sep_grant_acc fs gs j1 O R = true /\ sep_grant_acc fs gs j2 O R = true.
Proof.
  intros md fs gs j1 j2 R H. unfold cont_bm in H. cbv zeta in H. destruct (Z.leb 1 (snd (irange fs (rg_size R)))) eqn:Hz; [|discriminate].
  exact (cont_accm_sep md fs gs j1 j2 O R Hz H).
Qed.

(* [comment removed for export] *)
Definition sh_terms (tg tb : list (positive * Z)) : bool :=
  match tg with [] => false | _ => forallb (fun xc => existsb (fun yd => Pos.eqb (fst xc) (fst yd) &&& Z.eqb (8 * snd yd) (snd xc)) tb) tg end.
Fixpoint contp_acc (fs : list fact) (gs : list (lin * lin * gkind)) (j i : nat) (b : lin) (z : Z) : bool :=
  match gs with
  | [] => false
  | g :: r => (negb (is_mark g) &&& negb (Nat.eqb i j) &&& sh_terms (l_t (fst (fst g))) (l_t b) &&&
               match srl_lin fs 3 (fst (fst g)) with
               | Some pb => contained_b fs b z (laddc pb SH_OFF) (gsz_lo fs g / 8)
               | None => false
               end) ||| contp_acc fs r j (Datatypes.S i) b z
  end.
Definition cont_p (fs : list fact) (gs : list (lin * lin * gkind)) (j : nat) (R : region) : bool :=
  let zhi := snd (irange fs (rg_size R)) in Z.leb 1 zhi &&& contp_acc fs gs j O (rg_base R) zhi.
Lemma contp_acc_sep : forall fs gs j i R, Z.leb 1 (snd (irange fs (rg_size R))) = true ->
  contp_acc fs gs j i (rg_base R) (snd (irange fs (rg_size R))) = true -> sep_pgrant_acc fs gs j i R = true.
Proof.
  intros fs gs j. induction gs as [|g r IH]; intros i R Hz H; cbn [contp_acc] in H; [discriminate|]. cbn [sep_pgrant_acc]. rewrite Hz.
  destruct (negb (is_mark g)); [|cbn in H |- *; exact (IH (Datatypes.S i) R Hz H)].
  destruct (negb (Nat.eqb i j)); [|cbn in H |- *; exact (IH (Datatypes.S i) R Hz H)].
  destruct (sh_terms (l_t (fst (fst g))) (l_t (rg_base R))); cbn in H |- *.
  - destruct (srl_lin fs 3 (fst (fst g))) as [pb|]; [|exact (IH (Datatypes.S i) R Hz H)].
    destruct (contained_b fs (rg_base R) (snd (irange fs (rg_size R))) (laddc pb SH_OFF) (gsz_lo fs g / 8)); [reflexivity | exact (IH (Datatypes.S i) R Hz H)].
  - rewrite (IH (Datatypes.S i) R Hz H). match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
Qed.
Lemma cont_p_sep : forall fs gs j R, cont_p fs gs j R = true -> sep_pgrant_acc fs gs j O R = true.
Proof.
  intros fs gs j R H. unfold cont_p in H. cbv zeta in H. destruct (Z.leb 1 (snd (irange fs (rg_size R)))) eqn:Hz; [|discriminate].
  exact (contp_acc_sep fs gs j O R Hz H).
Qed.

(* [comment removed for export] *)
Definition band_few (fs : list fact) (sp : lin) (R : region) : bool := few_t (lsub sp (rg_base R)) &&& sep_band_b fs sp R.
Definition dep_sep_f2 (fs : list fact) (gs : list (lin * lin * gkind)) (res : list (word * word)) (jD1 jB1 : nat) (sp D1l B1l : lin)
    (nsD nsB : bool) (R : region) : bool :=
  match is_const (rg_base R), is_const (rg_size R) with
  | Some _, Some _ => dep_sep_f fs gs res jD1 jB1 sp D1l B1l R
  | _, _ => if cont_b fs gs jD1 jB1 R then true
            else if band_few fs sp R then true          (* [comment removed for export] *)
            else if (nsD &&& nsB &&& sep_shadow_b fs R) then true
            else dep_sep_f fs gs res jD1 jB1 sp D1l B1l R
  end.
Lemma dep_sep_b_grant : forall fs gs res jD1 jB1 sp D1l B1l R, sep_grant_acc fs gs jD1 O R = true -> sep_grant_acc fs gs jB1 O R = true ->
  (is_const (rg_base R) = None \/ is_const (rg_size R) = None) -> dep_sep_b fs gs res jD1 jB1 sp D1l B1l R = true.
Proof.
  intros fs gs res jD1 jB1 sp D1l B1l R A B Hn. unfold dep_sep_b, img_sep_b. rewrite !sep_app2_b_eq. rewrite A, B.
  destruct (is_const (rg_base R)), (is_const (rg_size R)); try reflexivity. destruct Hn; discriminate.
Qed.
Lemma dep_sep_b_shadow : forall fs gs res jD1 jB1 sp D1l B1l R, sep_noshadow_b fs (RGz D1l 1048576 RZ TEmpty) = true ->
  sep_noshadow_b fs (RGz B1l 8388608 RZ TEmpty) = true -> sep_shadow_b fs R = true ->
  (is_const (rg_base R) = None \/ is_const (rg_size R) = None) -> dep_sep_b fs gs res jD1 jB1 sp D1l B1l R = true.
Proof.
  intros fs gs res jD1 jB1 sp D1l B1l R N1 N2 Hs Hn. unfold dep_sep_b, img_sep_b. rewrite !sep_app2_b_eq. rewrite N1, N2, Hs.
  destruct (is_const (rg_base R)), (is_const (rg_size R)); try (destruct Hn; discriminate);
    destruct (sep_grant_acc fs gs jD1 O R), (sep_grant_acc fs gs jB1 O R), (sep_band_b fs sp R); reflexivity.
Qed.
Lemma dep_sep_b_band : forall fs gs res jD1 jB1 sp D1l B1l R, sep_band_b fs sp R = true ->
  (is_const (rg_base R) = None \/ is_const (rg_size R) = None) -> dep_sep_b fs gs res jD1 jB1 sp D1l B1l R = true.
Proof.
  intros fs gs res jD1 jB1 sp D1l B1l R Hb Hn. unfold dep_sep_b, img_sep_b. rewrite !sep_app2_b_eq. rewrite Hb.
  destruct (is_const (rg_base R)), (is_const (rg_size R)); try (destruct Hn; discriminate);
    destruct (sep_grant_acc fs gs jD1 O R), (sep_grant_acc fs gs jB1 O R); reflexivity.
Qed.
Lemma dep_sep_f2_eq : forall fs gs res jD1 jB1 sp D1l B1l nsD nsB R,
  nsD = sep_noshadow_b fs (RGz D1l 1048576 RZ TEmpty) -> nsB = sep_noshadow_b fs (RGz B1l 8388608 RZ TEmpty) ->
  dep_sep_f2 fs gs res jD1 jB1 sp D1l B1l nsD nsB R = dep_sep_b fs gs res jD1 jB1 sp D1l B1l R.
Proof.
  intros fs gs res jD1 jB1 sp D1l B1l nsD nsB R -> ->. unfold dep_sep_f2. rewrite dep_sep_f_eq.
  assert (K : (is_const (rg_base R) = None \/ is_const (rg_size R) = None) ->
              (if cont_b fs gs jD1 jB1 R then true
               else if band_few fs sp R then true
               else if (sep_noshadow_b fs (RGz D1l 1048576 RZ TEmpty) &&& sep_noshadow_b fs (RGz B1l 8388608 RZ TEmpty) &&& sep_shadow_b fs R) then true
                    else dep_sep_b fs gs res jD1 jB1 sp D1l B1l R) = dep_sep_b fs gs res jD1 jB1 sp D1l B1l R).
  { intros Hn. destruct (cont_b fs gs jD1 jB1 R) eqn:Hc.
    - destruct (cont_b_sep fs gs jD1 jB1 R Hc) as [A B]. symmetry. exact (dep_sep_b_grant fs gs res jD1 jB1 sp D1l B1l R A B Hn).
    - destruct (band_few fs sp R) eqn:Hbf.
      { unfold band_few in Hbf. destruct (few_t (lsub sp (rg_base R))); [|discriminate]. symmetry. exact (dep_sep_b_band fs gs res jD1 jB1 sp D1l B1l R Hbf Hn). }
      destruct (sep_noshadow_b fs (RGz D1l 1048576 RZ TEmpty)) eqn:N1; [|reflexivity].
      destruct (sep_noshadow_b fs (RGz B1l 8388608 RZ TEmpty)) eqn:N2; [|reflexivity].
      destruct (sep_shadow_b fs R) eqn:Hs; [|reflexivity]. cbn. symmetry. exact (dep_sep_b_shadow fs gs res jD1 jB1 sp D1l B1l R N1 N2 Hs Hn). }
  destruct (is_const (rg_base R)) as [cb|] eqn:Eb; [destruct (is_const (rg_size R)) as [cz|] eqn:Ez; [reflexivity|]|].
  - apply K. right. reflexivity.
  - apply K. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fixkeep_ok_nomark : forall LIMIT res L M n na j kd' g, fixkeep_ok LIMIT res L M n na j kd' = true ->
  nth_error (sm_maps M) j = Some g -> is_mark g = false.
Proof.
  intros LIMIT res L M n na j kd' g H Hj. unfold fixkeep_ok in H. cbv zeta in H.
  destruct (a7c L); [|discriminate]. destruct (arg L 2); [|discriminate]. destruct (arg L 3); [|discriminate]. destruct (arg L 5); [|discriminate].
  rewrite Hj in H. apply andb_prop in H as [_ H]. apply negb_true_iff in H. exact H.
Qed.
Lemma fixnew_ok_nomark : forall LIMIT res L M n j g, fixnew_ok LIMIT res L M n j = true -> nth_error (sm_maps M) j = Some g -> is_mark g = false.
Proof.
  intros LIMIT res L M n j g H Hj. unfold fixnew_ok in H. cbv zeta in H.
  destruct (arg L 3); [|discriminate]. destruct (srl_lin _ 3 _); [|discriminate]. destruct (arg L 1); [|discriminate].
  repeat (apply andb_prop in H as [H _]). exact (fixkeep_ok_nomark _ _ _ _ _ _ _ _ g H Hj).
Qed.
(* [comment removed for export] *)
End AcFast.

From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcPri AcHA.

Module AcPriSep.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxMem FxFacts FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChFix FxChTwoC.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_nf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcPri.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcFast OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Fixpoint forallb_l {A} (f : A -> bool) (l : list A) : bool := match l with [] => true | x :: r => if f x then forallb_l f r else false end.
Fixpoint existsb_l {A} (f : A -> bool) (l : list A) : bool := match l with [] => false | x :: r => if f x then true else existsb_l f r end.
Lemma forallb_l_eq : forall A (f : A -> bool) l, forallb_l f l = forallb f l.
Proof. induction l as [|x r IH]; cbn; [reflexivity|]. rewrite IH. destruct (f x); reflexivity. Qed.
Lemma existsb_l_eq : forall A (f : A -> bool) l, existsb_l f l = existsb f l.
Proof. induction l as [|x r IH]; cbn; [reflexivity|]. rewrite IH. destruct (f x); reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition live_end (R : region) (lb : lin) (zhi lim : Z) : bool :=
  match lin_off (ladd (rg_base R) (rg_size R)) lb with Some e => (Z.leb zhi e && Z.leb e lim)%bool | None => false end.
Definition live_in (fs : list fact) (a : ast) (R : region) (c : Z) : bool :=
  let jlo := fst (irange fs (p_j a c)) in let zhi := snd (irange fs (rg_size R)) in
  (match lin_off (rg_base R) (l_rb a c) with Some d => (Z.leb 0 d && Z.leb (d + zhi) (sz_tbl c * jlo) && Z.ltb d 262144)%bool
   | None => live_end R (l_rb a c) zhi (sz_tbl c * jlo) end ||
   match lin_off (rg_base R) (l_shu a c) with Some d => (Z.leb 0 d && Z.leb (d + zhi) (sz_tbl c / 8 * jlo) && Z.ltb d 32768)%bool
   | None => live_end R (l_shu a c) zhi (sz_tbl c / 8 * jlo) end)%bool.
(* [comment removed for export] *)
Definition small_t (l : lin) : bool := match l_t l with _ :: _ :: _ :: _ :: _ => false | _ => true end.   (* [comment removed for export] *)
Definition inside_lin (fs : list fact) (rb rz eb ez : lin) : bool :=
  let d := lsub rb eb in
  if few_t d then          (* [comment removed for export] *)
    let e := lsub (ladd eb ez) (ladd rb rz) in
    if small_t e then
      let dr := irange fs d in
      if (Z.leb 0 (fst dr) && Z.ltb (snd dr) 140737488355328)%bool then
        let er := irange fs e in
        if (Z.leb 0 (fst er) && Z.ltb (snd er) 140737488355328)%bool then Z.ltb (snd (irange fs rz)) 140737488355328 else false
      else false
    else false
  else false.
Definition ext_in1 (fs : list fact) (R : region) (p : lin * lin) : bool :=
  if inside_lin fs (rg_base R) (rg_size R) (fst p) (snd p) then true
  else if inside_lin fs (lscale 8 (laddc (rg_base R) (- SH_OFF))) (lscale 8 (rg_size R)) (fst p) (snd p)
       then (if Z.ltb (snd (irange fs (rg_base R))) 281474976710656 then Z.ltb (snd (irange fs (rg_size R))) 140737488355328 else false) else false.
Definition ext_in (fs : list fact) (a : ast) (R : region) : bool := existsb_l (ext_in1 fs R) (a_ext a).
(* [comment removed for export] *)
Definition terms_in (tg tb : list (positive * Z)) : bool :=
  match tg with
  | [] => false
  | _ => forallb_l (fun xc => existsb_l (fun yd => if Pos.eqb (fst xc) (fst yd) then Z.eqb (snd xc) (snd yd) else false) tb) tg
  end.
Definition shc_at (cur : Z) (g : lin * lin * gkind) : bool :=
  if is_mark g then false else
  match is_const (fst (fst g)), is_const (snd (fst g)) with
  | Some b, Some z => if Z.eqb b cur then Z.ltb 0 z else false
  | _, _ => false
  end.
Fixpoint sh_cover (gs : list (lin * lin * gkind)) (cur hi : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | Datatypes.S f =>
      if Z.leb hi cur then true else
      match List.find (shc_at cur) gs with
      | Some g => match is_const (snd (fst g)) with Some z => sh_cover gs (cur + z) hi f | None => false end
      | None => false
      end
  end.
Fixpoint grant_in_acc (fs : list fact) (gs : list (lin * lin * gkind)) (j1 j2 i : nat) (R : region) : bool :=
  match gs with
  | [] => false
  | g :: r =>
      if (if is_mark g then false else if Nat.eqb i j1 then false else if Nat.eqb i j2 then false
          else if terms_in (l_t (fst (fst g))) (l_t (rg_base R)) then inside_lin fs (rg_base R) (rg_size R) (fst (fst g)) (snd (fst g)) else false)
      then true else grant_in_acc fs r j1 j2 (Datatypes.S i) R
  end.
Definition grant_in_e (fs : list fact) (gs : list (lin * lin * gkind)) (j1 j2 : nat) (R : region) : bool :=
  if grant_in_acc fs gs j1 j2 O R then sh_cover gs SH_LO SH_HI 8 else false.
(* [comment removed for export] *)
Fixpoint grant_sh_acc (fs : list fact) (gs : list (lin * lin * gkind)) (j i : nat) (R : region) : bool :=
  match gs with
  | [] => false
  | g :: r =>
      if (if is_mark g then false else if Nat.eqb i j then false
          else if sh_terms (l_t (fst (fst g))) (l_t (rg_base R))
               then inside_lin fs (lscale 8 (laddc (rg_base R) (- SH_OFF))) (lscale 8 (rg_size R)) (fst (fst g)) (snd (fst g)) else false)
      then true else grant_sh_acc fs r j (Datatypes.S i) R
  end.
Definition grant_in_sh (fs : list fact) (gs : list (lin * lin * gkind)) (j : nat) (R : region) : bool :=
  if grant_sh_acc fs gs j O R
  then (if Z.ltb (snd (irange fs (rg_base R))) 281474976710656 then Z.ltb (snd (irange fs (rg_size R))) 140737488355328 else false)
  else false.
(* [comment removed for export] *)
Definition ri_shadow_b (fs : list fact) (a : ast) (R : region) : bool :=
  match lin_off (rg_base R) (p_sh a) with
  | Some d => (Z.leb 17179869184 d && Z.leb (d + snd (irange fs (rg_size R))) 17179869696)%bool
  | None => false
  end.
(* [comment removed for export] *)
Definition pc_ri_ref (fs : list fact) (gs : list (lin * lin * gkind)) (jP : nat) (sp : lin) (a : ast) (R : region) : bool :=
  if sep_pc_b fs gs jP sp R then true else if ri_shadow_b fs a R then true else twoc_ns fs (rg_base R) (snd (irange fs (rg_size R))).
Definition pri_sep_f (fs : list fact) (gs : list (lin * lin * gkind)) (res : list (word * word)) (jP jT : nat) (sp : lin) (a : ast) (R : region) : bool :=
  (* [comment removed for export] *)
  match is_const (rg_base R), is_const (rg_size R) with
  | Some b, Some z =>   (* [comment removed for export] *)
      if Z.leb (b + z) 2201439137792 &&& (Z.leb (b + z) 930696 ||| Z.leb 930736 b)    (* [comment removed for export] *)
      then (if sep_res_b res R then true else sep_app2_b fs gs jT sp (l_cb a) CB_SIZE R) else false
  | _, _ =>
      if existsb_l (live_in fs a R) CLS then true
      else if ext_in fs a R then true
      else if grant_in_e fs gs jP jT R then true     (* [comment removed for export] *)
      else if grant_in_sh fs gs jP R then true       (* [comment removed for export] *)
      else if sep_app2_b fs gs jP sp (p_pg a) PG_SIZE R
           then (if pc_ri_ref fs gs jP sp a R
                 then (if rgs_sep fs (l_cb a) CB_SIZE R then true else sep_app2_b fs gs jT sp (l_cb a) CB_SIZE R)
                 else false)
           else false
  end.


(* [comment removed for export] *)
Definition live_in_l (fs : list fact) (a : ast) (R : region) (c : Z) : bool :=
  (match lin_off (rg_base R) (l_rb a c) with
   | Some d => if Z.leb 0 d then (if Z.ltb d 262144 then Z.leb (d + snd (irange fs (rg_size R))) (sz_tbl c * fst (irange fs (p_j a c))) else false) else false
   | None => match lin_off (ladd (rg_base R) (rg_size R)) (l_rb a c) with
             | Some e => if Z.leb (snd (irange fs (rg_size R))) e then Z.leb e (sz_tbl c * fst (irange fs (p_j a c))) else false
             | None => false end
   end) |||
  (match lin_off (rg_base R) (l_shu a c) with
   | Some d => if Z.leb 0 d then (if Z.ltb d 32768 then Z.leb (d + snd (irange fs (rg_size R))) (sz_tbl c / 8 * fst (irange fs (p_j a c))) else false) else false
   | None => match lin_off (ladd (rg_base R) (rg_size R)) (l_shu a c) with
             | Some e => if Z.leb (snd (irange fs (rg_size R))) e then Z.leb e (sz_tbl c / 8 * fst (irange fs (p_j a c))) else false
             | None => false end
   end).
Lemma live_in_l_eq : forall fs a R c, live_in_l fs a R c = live_in fs a R c.
Proof.
  intros fs a R c. unfold live_in_l, live_in, live_end. cbv zeta.
  destruct (lin_off (rg_base R) (l_rb a c)) as [d|]; destruct (lin_off (rg_base R) (l_shu a c)) as [d'|];
    repeat match goal with |- context [lin_off (ladd (rg_base R) (rg_size R)) ?x] => destruct (lin_off (ladd (rg_base R) (rg_size R)) x) end;
    repeat match goal with |- context [Z.leb ?x ?y] => destruct (Z.leb x y) | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) end; reflexivity.
Qed.
Lemma existsb_l_ext : forall {A} (f g : A -> bool) l, (forall x, f x = g x) -> existsb_l f l = existsb_l g l.
Proof. intros A f g l H. induction l as [|x r IH]; [reflexivity|]. cbn [existsb_l]. rewrite H, IH. reflexivity. Qed.
Definition pc_or_ri_f (fs : list fact) (gs : list (lin * lin * gkind)) (jP : nat) (sp : lin) (a : ast) (R : region) : bool :=
  if sep_noshadow_b fs R then true
  else if syn_pgrant fs gs jP R then true
  else if cont_p fs gs jP R then true          (* [comment removed for export] *)
  else if sep_pband_b fs sp R then true
  else if sep_pgrant_acc fs gs jP O R then true
  else if ri_shadow_b fs a R then true
  else twoc_ns fs (rg_base R) (snd (irange fs (rg_size R))).
Lemma pc_or_ri_f_eq : forall fs gs jP sp a R, pc_or_ri_f fs gs jP sp a R = pc_ri_ref fs gs jP sp a R.
Proof.
  intros fs gs jP sp a R. unfold pc_or_ri_f, pc_ri_ref. rewrite sep_pc_b_eq.
  destruct (sep_noshadow_b fs R); [destruct (sep_pgrant_acc fs gs jP O R), (sep_pband_b fs sp R); reflexivity|].
  destruct (syn_pgrant fs gs jP R) eqn:Hs; [rewrite (syn_pgrant_sound fs gs jP R Hs); reflexivity|].
  destruct (cont_p fs gs jP R) eqn:Hc; [rewrite (cont_p_sep fs gs jP R Hc); reflexivity|].
  destruct (sep_pband_b fs sp R), (sep_pgrant_acc fs gs jP O R); reflexivity.
Qed.
Definition pri_sep_ff (fs : list fact) (gs : list (lin * lin * gkind)) (res : list (word * word)) (jP jT : nat) (sp : lin) (a : ast) (R : region) : bool :=
  match is_const (rg_base R), is_const (rg_size R) with
  | Some b, Some z =>
      if Z.leb (b + z) 2201439137792 &&& (Z.leb (b + z) 930696 ||| Z.leb 930736 b)
      then (if sep_res_b res R then true else fast_app2 fs gs jT sp (l_cb a) CB_SIZE R) else false
  | _, _ =>
      if existsb_l (live_in_l fs a R) CLS then true
      else if ext_in fs a R then true
      (* [comment removed for export] *)
      else if cont_bm true fs gs jP jT R            (* [comment removed for export] *)
           then (if pc_or_ri_f fs gs jP sp a R then true else if grant_in_e fs gs jP jT R then true else grant_in_sh fs gs jP R)
      else if grant_in_e fs gs jP jT R then true
      else if grant_in_sh fs gs jP R then true
      else if cont_bm false fs gs jP jT R then pc_or_ri_f fs gs jP sp a R     (* [comment removed for export] *)
      else if fast_app2 fs gs jP sp (p_pg a) PG_SIZE R
           then (if pc_or_ri_f fs gs jP sp a R
                 then (if rgs_sep fs (l_cb a) CB_SIZE R then true else fast_app2 fs gs jT sp (l_cb a) CB_SIZE R)
                 else false)
           else false
  end.
Lemma pri_sep_ff_eq : forall fs gs res jP jT sp a R, pri_sep_ff fs gs res jP jT sp a R = pri_sep_f fs gs res jP jT sp a R.
Proof.
  intros fs gs res jP jT sp a R. unfold pri_sep_ff, pri_sep_f. rewrite !fast_app2_eq, pc_or_ri_f_eq, (existsb_l_ext _ _ CLS (live_in_l_eq fs a R)).
  set (X := pc_ri_ref fs gs jP sp a R). set (G := grant_in_e fs gs jP jT R). set (Gs := grant_in_sh fs gs jP R).
  assert (K : (if existsb_l (live_in fs a R) CLS then true else if ext_in fs a R then true
               else if cont_bm true fs gs jP jT R then (if X then true else if G then true else Gs)
               else if G then true else if Gs then true
               else if cont_bm false fs gs jP jT R then X
               else if sep_app2_b fs gs jP sp (p_pg a) PG_SIZE R then (if X then (if rgs_sep fs (l_cb a) CB_SIZE R then true else sep_app2_b fs gs jT sp (l_cb a) CB_SIZE R) else false) else false) =
              (if existsb_l (live_in fs a R) CLS then true else if ext_in fs a R then true
               else if G then true else if Gs then true
               else if sep_app2_b fs gs jP sp (p_pg a) PG_SIZE R then (if X then (if rgs_sep fs (l_cb a) CB_SIZE R then true else sep_app2_b fs gs jT sp (l_cb a) CB_SIZE R) else false) else false)).
  { destruct (existsb_l (live_in fs a R) CLS); [reflexivity|]. destruct (ext_in fs a R); [reflexivity|].
    destruct (cont_bm true fs gs jP jT R) eqn:Hc0.
    { destruct (cont_bm_sep true fs gs jP jT R Hc0) as [A B]. rewrite !sep_app2_b_eq. rewrite A, B. cbn [orb].
      destruct X, G, Gs; try reflexivity; destruct (rgs_sep fs (l_cb a) CB_SIZE R); reflexivity. }
    destruct G; [reflexivity|]. destruct Gs; [reflexivity|].
    destruct (cont_bm false fs gs jP jT R) eqn:Hc; [|reflexivity].
    destruct (cont_bm_sep false fs gs jP jT R Hc) as [A B]. rewrite !sep_app2_b_eq. rewrite A, B. cbn [orb].
    destruct X; try reflexivity; destruct (rgs_sep fs (l_cb a) CB_SIZE R); reflexivity. }
  destruct (is_const (rg_base R)) as [b|]; [destruct (is_const (rg_size R)) as [z|]; [reflexivity | exact K] | exact K].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hd_eq (a b : lin) : bool :=
  match l_t a, l_t b with
  | [], [] => true
  | (x, _) :: _, (y, _) :: _ => Pos.eqb x y
  | _, _ => false
  end.
Definition sep_cached (a : ast) (R : region) : bool :=
  existsb_l (fun p => if hd_eq (rg_base R) (fst p) then
                    match lin_off (rg_base R) (fst p) with
                    | Some d => match is_const (rg_size R), is_const (snd p) with
                                | Some z, Some zc => (Z.leb 0 d && Z.leb (d + z) zc)%bool      (* [comment removed for export] *)
                                | _, _ => (Z.eqb d 0 && lin_eqb (rg_size R) (snd p))%bool       (* [comment removed for export] *)
                                end
                    | None => false end else false) (a_live a).
Definition pri_sep_c (fs : list fact) (gs : list (lin * lin * gkind)) (res : list (word * word)) (jP jT : nat) (sp : lin) (a : ast) (R : region) : bool :=
  if sep_cached a R then true else pri_sep_ff fs gs res jP jT sp a R.
(* [comment removed for export] *)
Definition pri_sep_t (fs : list fact) (gs : list (lin * lin * gkind)) (res : list (word * word)) (jP jT : nat) (sp : lin) (a : ast) (R : region) : bool :=
  if sep_cached a R then true
  else if existsb_l (live_in_l fs a R) CLS then false
  else pri_sep_ff fs gs res jP jT sp a R.
(* [comment removed for export] *)
Definition sep_cache (fs : list fact) (gs : list (lin * lin * gkind)) (res : list (word * word)) (jP jT : nat) (sp : lin) (a : ast) (rgs : list region) : list (lin * lin) :=
  List.map (fun R => (rg_base R, rg_size R)) (List.filter (pri_sep_ff fs gs res jP jT sp a) rgs).
(* [comment removed for export] *)
End AcPriSep.

Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcFast OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition live_sem (E : valu) (a : ast) (R : region) : Prop :=
  exists c, In c CLS /\
    ((z_sb (pden E a) + 4294967296 * c <= uE E (rg_base R) /\
      uE E (rg_base R) + rsz E R <= z_sb (pden E a) + 4294967296 * c + sz_tbl c * z_j (pden E a) c /\ sz_tbl c * z_j (pden E a) c <= 262144) \/
     (z_sh (pden E a) + 536870912 * c <= uE E (rg_base R) /\
      uE E (rg_base R) + rsz E R <= z_sh (pden E a) + 536870912 * c + sz_tbl c / 8 * z_j (pden E a) c /\ sz_tbl c / 8 * z_j (pden E a) c <= 32768)).

(* [comment removed for export] *)
Definition live_user (E : valu) (a : ast) (R : region) (c : Z) : Prop :=
  z_sb (pden E a) + 4294967296 * c <= uE E (rg_base R) /\
  uE E (rg_base R) + rsz E R <= z_sb (pden E a) + 4294967296 * c + sz_tbl c * z_j (pden E a) c /\ sz_tbl c * z_j (pden E a) c <= 262144.
Definition live_shadow (E : valu) (a : ast) (R : region) (c : Z) : Prop :=
  z_sh (pden E a) + 536870912 * c <= uE E (rg_base R) /\
  uE E (rg_base R) + rsz E R <= z_sh (pden E a) + 536870912 * c + sz_tbl c / 8 * z_j (pden E a) c /\ sz_tbl c / 8 * z_j (pden E a) c <= 32768.

(* [comment removed for export] *)
Lemma sep_cached_gen : forall E a (P : Z -> Prop) R,
  (forall p, In p (a_live a) -> uE E (fst p) + uE E (snd p) <= two64 /\ forall x, uE E (fst p) <= x < uE E (fst p) + uE E (snd p) -> ~ P x) ->
  0 <= rsz E R -> uE E (rg_base R) + rsz E R <= two64 -> sep_cached a R = true ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ P w.
Proof.
  intros E a P R Hsepc Hz Hr H w Hw. unfold sep_cached in H. rewrite existsb_l_eq in H. apply existsb_exists in H as (p & Hp & Hc).
  destruct (hd_eq (rg_base R) (fst p)); [|discriminate].
  destruct (lin_off (rg_base R) (fst p)) as [d|] eqn:Hd; [|discriminate].
  pose proof (lin_off_sound E _ _ _ Hd) as [_ Hdr].
  pose proof (u_lt (lden E (fst p))) as Rp. pose proof (u_lt (lden E (rg_base R))) as Rb.
  destruct (is_const (rg_size R)) as [z|] eqn:Ez; [destruct (is_const (snd p)) as [zc|] eqn:Ezc|].
  - apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1, C2.
    assert (Hrz : rsz E R = z) by (unfold rsz; exact (is_const_u E _ _ Ez)).
    assert (Hpz : uE E (snd p) = zc) by (unfold uE; exact (is_const_u E _ _ Ezc)).
    destruct (Hsepc p Hp) as [Hnw Hsp0]. rewrite Hpz in Hnw, Hsp0.
    assert (Hlt : bv_unsigned (lden E (fst p)) + d < two64) by (unfold uE, rsz in *; lia).
    pose proof (lin_off_u E _ _ d Hd Hlt) as Eb. apply (Hsp0 w). unfold uE in *. lia.
  - apply andb_prop in Hc as [C1 C2]. apply Z.eqb_eq in C1. apply lin_eqb_eq in C2. subst d.
    pose proof (lin_off_u E _ _ 0 Hd ltac:(unfold two64 in *; lia)) as Eb. apply (proj2 (Hsepc p Hp) w). unfold uE, rsz in *. rewrite <- C2. lia.
  - apply andb_prop in Hc as [C1 C2]. apply Z.eqb_eq in C1. apply lin_eqb_eq in C2. subst d.
    pose proof (lin_off_u E _ _ 0 Hd ltac:(unfold two64 in *; lia)) as Eb. apply (proj2 (Hsepc p Hp) w). unfold uE, rsz in *. rewrite <- C2. lia.
Qed.

Section PriSepOk.
Variable E : valu.
Variable fs : list fact.
Variable gs : list (lin * lin * gkind).
Variable model : Model.
Variable sp : lin.
Variable BL : list (word * word).        (* [comment removed for export] *)
Hypothesis HF : Forall (fact_ok E) fs.
Hypothesis Hmaps : vm_maps (m_vmmaps model) = lden_maps E BL gs.
Hypothesis Hpd : pdisj (vm_maps (m_vmmaps model)).
Hypothesis Hgsh : Forall (gshape_ok E) gs.
Hypothesis Hgtop : Forall (fun g => uE E (fst (fst g)) + gsz E g <= alloc_top (m_vmmaps model)) gs.
Hypothesis Hsp : vm_init_sp (m_vmmaps model) = lden E sp.
Hypothesis Hsphi : bv_unsigned (vm_init_sp (m_vmmaps model)) <= sp_window_hi.
Hypothesis Hspok : init_sp_ok (m_vmmaps model).
Hypothesis Hmres : forall x, covered (vm_maps (m_vmmaps model)) x = true -> covered (vm_reserved (m_vmmaps model)) x = false.
Variable res : list (word * word).
Hypothesis Hres : vm_reserved (m_vmmaps model) = res.
Hypothesis Hgqres : in_res_b res 930696 930736 = true.   (* [comment removed for export] *)
Variable a : ast.
Variable m0 : word -> option byte.
Hypothesis HI : INV_A E a m0.
Variables (jP jT : nat) (gP gT : lin * lin * gkind).
Hypothesis HjP : nth_error gs jP = Some gP.
Hypothesis HbP : fst (fst gP) = p_pg a.
Hypothesis HsP : snd (fst gP) = lconst PG_SIZE.
Hypothesis HjT : nth_error gs jT = Some gT.
Hypothesis HbT : fst (fst gT) = p_tg a.
Hypothesis HsT : snd (fst gT) = lconst TG_SIZE.
Hypothesis Hsepc : forall p, In p (a_live a) -> uE E (fst p) + uE E (snd p) <= two64 /\
  forall x, uE E (fst p) <= x < uE E (fst p) + uE E (snd p) -> ~ FPmax (pden E a) x.
Hypothesis Hext : forall p, In p (a_ext a) -> ext_sem (pden E a) (uE E (fst p)) (uE E (snd p)).   (* [comment removed for export] *)

Local Abbreviation pz := (pden E a).
(* [comment removed for export] *)
#[using="gs a jP HjP HbP HsP"] Lemma gP_nm : is_mark gP = false.
Proof. LiaFast.lf_pins (fun (gs a jP HjP HbP HsP : LiaFast.U) => LiaFast.u0). destruct gP as [[b s] k]. cbn [fst snd] in HsP. rewrite HsP. apply is_mark_csize. Qed.
#[using="gs a jT HjT HbT HsT"] Lemma gT_nm : is_mark gT = false.
Proof. LiaFast.lf_pins (fun (gs a jT HjT HbT HsT : LiaFast.U) => LiaFast.u0). destruct gT as [[b s] k]. cbn [fst snd] in HsT. rewrite HsT. apply is_mark_csize. Qed.
#[using="HsP"] Lemma gz_P : gsz E gP = PG_SIZE.
Proof. LiaFast.lf_pins (fun (HsP : LiaFast.U) => LiaFast.u0). unfold gsz. rewrite HsP. apply uE_lc. unfold PG_SIZE. lia. Qed.
#[using="HsT"] Lemma gz_T : gsz E gT = TG_SIZE.
Proof. LiaFast.lf_pins (fun (HsT : LiaFast.U) => LiaFast.u0). unfold gsz. rewrite HsT. apply uE_lc. unfold TG_SIZE. lia. Qed.
#[using="HbP"] Lemma ub_P : uE E (fst (fst gP)) = z_pg pz.
Proof. LiaFast.lf_pins (fun (HbP : LiaFast.U) => LiaFast.u0). rewrite HbP. symmetry. apply zn_pden. Qed.
#[using="HbT"] Lemma ub_T : uE E (fst (fst gT)) = z_tg pz.
Proof. LiaFast.lf_pins (fun (HbT : LiaFast.U) => LiaFast.u0). rewrite HbT. symmetry. apply zn_pden. Qed.
#[using="Type"] Lemma u_ca : uE E (p_ca a) = z_ca pz.
Proof. LiaFast.lf_pins LiaFast.u0. symmetry. apply zn_pden. Qed.
#[using="Type"] Lemma u_pg : uE E (p_pg a) = z_pg pz.
Proof. LiaFast.lf_pins LiaFast.u0. symmetry. apply zn_pden. Qed.
#[using="Type"] Lemma u_sb : uE E (p_sb a) = z_sb pz.
Proof. LiaFast.lf_pins LiaFast.u0. symmetry. apply zn_pden. Qed.

(* [comment removed for export] *)
#[using="Hsepc"] Lemma sep_cached_sound : forall R, 0 <= rsz E R -> uE E (rg_base R) + rsz E R <= two64 -> sep_cached a R = true ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ FPmax pz w.
Proof. LiaFast.lf_pins (fun (Hsepc : LiaFast.U) => LiaFast.u0).
  intros R Hz Hr H w Hw. unfold sep_cached in H. rewrite existsb_l_eq in H. apply existsb_exists in H as (p & Hp & Hc).
  destruct (hd_eq (rg_base R) (fst p)); [|discriminate].
  destruct (lin_off (rg_base R) (fst p)) as [d|] eqn:Hd; [|discriminate].
  pose proof (lin_off_sound E _ _ _ Hd) as [_ Hdr].
  pose proof (u_lt (lden E (fst p))) as Rp. pose proof (u_lt (lden E (rg_base R))) as Rb.
  destruct (is_const (rg_size R)) as [z|] eqn:Ez; [destruct (is_const (snd p)) as [zc|] eqn:Ezc|].
  - apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1, C2.
    assert (Hrz : rsz E R = z) by (unfold rsz; exact (is_const_u E _ _ Ez)).
    assert (Hpz : uE E (snd p) = zc) by (unfold uE; exact (is_const_u E _ _ Ezc)).
    destruct (Hsepc p Hp) as [Hnw Hsp0]. rewrite Hpz in Hnw, Hsp0.
    assert (Hlt : bv_unsigned (lden E (fst p)) + d < two64) by (unfold uE, rsz in *; lia).
    pose proof (lin_off_u E _ _ d Hd Hlt) as Eb. apply (Hsp0 w). unfold uE in *. lia.
  - apply andb_prop in Hc as [C1 C2]. apply Z.eqb_eq in C1. apply lin_eqb_eq in C2. subst d.
    pose proof (lin_off_u E _ _ 0 Hd ltac:(unfold two64 in *; lia)) as Eb. apply (proj2 (Hsepc p Hp) w). unfold uE, rsz in *. rewrite <- C2. lia.
  - apply andb_prop in Hc as [C1 C2]. apply Z.eqb_eq in C1. apply lin_eqb_eq in C2. subst d.
    pose proof (lin_off_u E _ _ 0 Hd ltac:(unfold two64 in *; lia)) as Eb. apply (proj2 (Hsepc p Hp) w). unfold uE, rsz in *. rewrite <- C2. lia.
Qed.
(* [comment removed for export] *)
#[using="m0 HI"] Lemma ps_geo : z_pg pz <= z_sb pz /\ z_sb pz + 137438953472 + 4096 <= z_pg pz + 137439023104 /\ z_pg pz + 137439023104 <= 2^47 /\
  17594333495296 <= z_pg pz /\ 17594333495296 <= z_sb pz /\ z_sb pz mod 8 = 0 /\ z_sh pz = z_sb pz / 8 + 2147450880 /\
  2199291686912 <= z_sb pz / 8 /\ z_sb pz / 8 <= 17592186044416 - 17179869184 /\
  z_ca pz = z_tg pz + 208 /\ 4096 <= z_tg pz /\ z_ca pz + 3888 <= 2^47.
Proof. LiaFast.lf_pins (fun (m0 HI : LiaFast.U) => LiaFast.u0).
  destruct HI as [Hlen Hsb Hsh Hca Hpg Htg Hnsh Hst Hwc Hq Hgq Hcls]. unfold PG_SIZE in Hpg.
  assert (Hm8 : z_sb pz mod 8 = 0).
  { destruct Hsb as [_ Hm]. pose proof (Z.div_mod (z_sb pz) 4096 ltac:(lia)) as Ed. rewrite Hm, Z.add_0_r in Ed. rewrite Ed.
    replace (4096 * (z_sb pz / 4096)) with (512 * (z_sb pz / 4096) * 8) by ring. apply Z.mod_mul. lia. }
  assert (Hd1 : 2199291686912 <= z_sb pz / 8) by (apply Z.div_le_lower_bound; lia).
  assert (Hd2 : z_sb pz / 8 <= 17592186044416 - 17179869184) by (apply Z.div_le_upper_bound; lia).
  repeat split; try lia.
Qed.
#[using="m0 HI"] Lemma u_lrb : forall c, 1 <= c <= 30 -> uE E (l_rb a c) = z_sb pz + 4294967296 * c.
Proof. LiaFast.lf_pins (fun (m0 HI : LiaFast.U) => LiaFast.u0). intros c Hc. pose proof ps_geo as G. unfold l_rb. rewrite uE_laddc2 by (rewrite ?u_sb; unfold two64; lia). rewrite u_sb. reflexivity. Qed.
#[using="Type"] Lemma u_sh : uE E (p_sh a) = z_sh pz.
Proof. LiaFast.lf_pins LiaFast.u0. symmetry. apply zn_pden. Qed.
#[using="m0 HI"] Lemma u_lshu : forall c, 1 <= c <= 30 -> uE E (l_shu a c) = z_sh pz + 536870912 * c.
Proof. LiaFast.lf_pins (fun (m0 HI : LiaFast.U) => LiaFast.u0). intros c Hc. pose proof ps_geo as G. unfold l_shu. rewrite uE_laddc2 by (rewrite ?u_sh; unfold two64; lia). rewrite u_sh. reflexivity. Qed.
#[using="Type"] Lemma u_pj : forall c, uE E (p_j a c) = z_j pz c.
Proof. LiaFast.lf_pins LiaFast.u0. intros c. symmetry. apply zn_pden. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma live_end_sound : forall R lb zhi lim RB, live_end R lb zhi lim = true -> uE E lb = RB -> 0 <= RB -> RB + lim < two64 ->
  0 <= rsz E R <= zhi -> RB <= uE E (rg_base R) /\ uE E (rg_base R) + rsz E R <= RB + lim.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R lb zhi lim RB H Hlb HRB Hlim Hz. unfold live_end in H.
  destruct (lin_off (ladd (rg_base R) (rg_size R)) lb) as [e|] eqn:Hd; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2.
  pose proof (lin_off_u E _ _ e Hd) as Eb. fold (uE E lb) in Eb. rewrite Hlb in Eb. specialize (Eb ltac:(lia)).
  rewrite lden_ladd, bv_add_unsigned in Eb. unfold bv_wrap, bv_modulus in Eb. change (2 ^ Z.of_N 64) with two64 in Eb.
  fold (uE E (rg_base R)) in Eb. unfold rsz in Hz |- *.
  pose proof (u_lt (lden E (rg_base R))) as Rb. fold (uE E (rg_base R)) in Rb.
  destruct (Z_lt_le_dec (uE E (rg_base R) + bv_unsigned (lden E (rg_size R))) two64) as [Hs|Hs].
  - rewrite Z.mod_small in Eb by lia. lia.
  - exfalso. assert (Hm : (uE E (rg_base R) + bv_unsigned (lden E (rg_size R))) mod two64 = uE E (rg_base R) + bv_unsigned (lden E (rg_size R)) - two64)
      by (symmetry; apply (Z.mod_unique _ _ 1); lia).
    lia.
Qed.
#[using="m0 HI"] Lemma live_in_jb : forall c, In c CLS -> 0 <= z_j pz c /\ sz_tbl c * z_j pz c <= 262144 /\ sz_tbl c / 8 * z_j pz c <= 32768.
Proof. LiaFast.lf_pins (fun (m0 HI : LiaFast.U) => LiaFast.u0).
  intros c Hc. destruct (cls_tbl c Hc) as (Hszp & Hs8 & Hsz8 & Hnw & Hnm & Hmc).
  destruct HI as [_ _ _ _ _ _ _ _ _ _ _ Hcls].
  destruct (Hcls c Hc) as [(J0 & _)|(J1 & _ & Jb & _)]; [rewrite J0; lia|].
  split; [lia|]. split; [nia|]. nia.
Qed.
#[using="HF m0 HI"] Lemma live_in_user_sound : forall R c, In c CLS -> 0 <= rsz E R ->
  match lin_off (rg_base R) (l_rb a c) with
  | Some d => (Z.leb 0 d && Z.leb (d + snd (irange fs (rg_size R))) (sz_tbl c * fst (irange fs (p_j a c))) && Z.ltb d 262144)%bool
  | None => live_end R (l_rb a c) (snd (irange fs (rg_size R))) (sz_tbl c * fst (irange fs (p_j a c))) end = true -> live_user E a R c.
Proof. LiaFast.lf_pins (fun (HF m0 HI : LiaFast.U) => LiaFast.u0).
  intros R c Hc Hz H. pose proof (in_cls_rng c Hc) as Hcr. pose proof ps_geo as G.
  pose proof (irange_sound E fs (rg_size R) HF) as Rs. pose proof (irange_sound E fs (p_j a c) HF) as Rj. fold (uE E (p_j a c)) in Rj. rewrite u_pj in Rj.
  unfold rsz in Hz. fold (rsz E R) in Rs.
  destruct (cls_tbl c Hc) as (Hszp & Hs8 & Hsz8 & Hnw & Hnm & Hmc).
  pose proof (live_in_jb c Hc) as Hjb. unfold live_user.
  destruct (lin_off (rg_base R) (l_rb a c)) as [d|] eqn:Hd.
  2:{ destruct (live_end_sound R _ _ _ _ H (u_lrb c Hcr) ltac:(lia) ltac:(unfold two64; nia) ltac:(unfold rsz in *; lia)) as [L1 L2].
      unfold rsz in *. split; [exact L1|]. split; [nia | lia]. }
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. apply Z.ltb_lt in H3.
  pose proof (lin_off_u E _ _ d Hd) as Eb. fold (uE E (l_rb a c)) in Eb. rewrite (u_lrb c Hcr) in Eb. specialize (Eb ltac:(unfold two64; lia)).
  fold (uE E (rg_base R)) in Eb. unfold rsz in *. nia.
Qed.
#[using="HF m0 HI"] Lemma live_in_shadow_sound : forall R c, In c CLS -> 0 <= rsz E R ->
  match lin_off (rg_base R) (l_shu a c) with
  | Some d => (Z.leb 0 d && Z.leb (d + snd (irange fs (rg_size R))) (sz_tbl c / 8 * fst (irange fs (p_j a c))) && Z.ltb d 32768)%bool
  | None => live_end R (l_shu a c) (snd (irange fs (rg_size R))) (sz_tbl c / 8 * fst (irange fs (p_j a c))) end = true -> live_shadow E a R c.
Proof. LiaFast.lf_pins (fun (HF m0 HI : LiaFast.U) => LiaFast.u0).
  intros R c Hc Hz H. pose proof (in_cls_rng c Hc) as Hcr. pose proof ps_geo as G.
  pose proof (irange_sound E fs (rg_size R) HF) as Rs. pose proof (irange_sound E fs (p_j a c) HF) as Rj. fold (uE E (p_j a c)) in Rj. rewrite u_pj in Rj.
  unfold rsz in Hz. fold (rsz E R) in Rs.
  destruct (cls_tbl c Hc) as (Hszp & Hs8 & Hsz8 & Hnw & Hnm & Hmc).
  pose proof (live_in_jb c Hc) as Hjb. unfold live_shadow.
  destruct (lin_off (rg_base R) (l_shu a c)) as [d|] eqn:Hd.
  2:{ destruct (live_end_sound R _ _ _ _ H (u_lshu c Hcr) ltac:(lia) ltac:(unfold two64; nia) ltac:(unfold rsz in *; lia)) as [L1 L2].
      unfold rsz in *. split; [exact L1|]. split; [nia | lia]. }
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. apply Z.ltb_lt in H3.
  pose proof (lin_off_u E _ _ d Hd) as Eb. fold (uE E (l_shu a c)) in Eb. rewrite (u_lshu c Hcr) in Eb. specialize (Eb ltac:(unfold two64; lia)).
  fold (uE E (rg_base R)) in Eb. unfold rsz in *. nia.
Qed.
#[using="HF m0 HI"] Lemma live_in_sound_c : forall R c, In c CLS -> 0 <= rsz E R -> live_in fs a R c = true -> live_user E a R c \/ live_shadow E a R c.
Proof. LiaFast.lf_pins (fun (HF m0 HI : LiaFast.U) => LiaFast.u0).
  intros R c Hc Hz H. unfold live_in in H. cbv zeta in H. apply orb_prop in H as [H|H];
    [left; exact (live_in_user_sound R c Hc Hz H) | right; exact (live_in_shadow_sound R c Hc Hz H)].
Qed.
(* [comment removed for export] *)
#[using="HF m0 HI"] Lemma live_in_shadow_c : forall R c, In c CLS -> 0 <= rsz E R -> lin_off (rg_base R) (l_rb a c) = None ->
  lin_off (ladd (rg_base R) (rg_size R)) (l_rb a c) = None -> live_in fs a R c = true -> live_shadow E a R c.
Proof. LiaFast.lf_pins (fun (HF m0 HI : LiaFast.U) => LiaFast.u0).
  intros R c Hc Hz H1 H2 H. unfold live_in in H. cbv zeta in H. rewrite H1 in H. unfold live_end at 1 in H. rewrite H2 in H.
  cbn [orb] in H. exact (live_in_shadow_sound R c Hc Hz H).
Qed.
#[using="HF m0 HI"] Lemma live_in_sound : forall R c, In c CLS -> 0 <= rsz E R -> live_in fs a R c = true -> live_sem E a R.
Proof. LiaFast.lf_pins (fun (HF m0 HI : LiaFast.U) => LiaFast.u0). intros R c Hc Hz H. exists c. split; [exact Hc|]. exact (live_in_sound_c R c Hc Hz H). Qed.
(* [comment removed for export] *)
#[using="m0 HI"] Lemma u_cb : uE E (l_cb a) = z_ca pz - 128.
Proof. LiaFast.lf_pins (fun (m0 HI : LiaFast.U) => LiaFast.u0). pose proof ps_geo as G. unfold l_cb. rewrite uE_laddc_z by (rewrite u_ca; unfold two64; lia). rewrite u_ca. reflexivity. Qed.
#[using="m0 HI HbT HsT"] Lemma cache_in_T : uE E (fst (fst gT)) <= uE E (l_cb a) /\ uE E (l_cb a) + CB_SIZE <= uE E (fst (fst gT)) + gsz E gT.
Proof. LiaFast.lf_pins (fun (m0 HI HbT HsT : LiaFast.U) => LiaFast.u0). pose proof ps_geo as G. rewrite ub_T, gz_T, u_cb. unfold TG_SIZE, CB_SIZE. lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma mod64_cases : forall t, - two64 <= t < 2 * two64 ->
  (t mod two64 = t /\ 0 <= t < two64) \/ (t mod two64 = t + two64 /\ t < 0) \/ (t mod two64 = t - two64 /\ two64 <= t).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t Ht. destruct (Z_lt_le_dec t 0) as [Hn|Hn]; [|destruct (Z_lt_le_dec t two64) as [Hs|Hs]].
  - right. left. split; [|exact Hn]. symmetry. apply (Z.mod_unique _ _ (-1)); unfold two64 in *; lia.
  - left. split; [apply Z.mod_small; lia | lia].
  - right. right. split; [|exact Hs]. symmetry. apply (Z.mod_unique _ _ 1); unfold two64 in *; lia.
Qed.
#[using="Type"] Lemma uE_ladd_mod : forall x y, uE E (ladd x y) = (uE E x + uE E y) mod two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros x y. unfold uE. rewrite lden_ladd, bv_add_unsigned. unfold bv_wrap, bv_modulus. reflexivity. Qed.
#[using="Type"] Lemma uE_lscale_mod : forall k x, uE E (lscale k x) = (k * uE E x) mod two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros k x. unfold uE. rewrite lden_lscale, u_Z_to_bv. reflexivity. Qed.
#[using="Type"] Lemma uE_laddc_mod : forall x z, uE E (laddc x z) = (uE E x + z) mod two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros x z. unfold uE. rewrite lden_laddc, u_Z_to_bv. reflexivity. Qed.
(* [comment removed for export] *)
#[using="HF"] Lemma inside_lin_sound : forall rb rz eb ez, inside_lin fs rb rz eb ez = true -> uE E eb + uE E ez < 2 ^ 48 ->
  uE E eb <= uE E rb /\ uE E rb + uE E rz <= uE E eb + uE E ez.
Proof. LiaFast.lf_pins (fun (HF : LiaFast.U) => LiaFast.u0).
  intros rb rz eb ez H Hb. unfold inside_lin in H. cbv zeta in H.
  destruct (few_t (lsub rb eb)); [|discriminate]. destruct (small_t (lsub (ladd eb ez) (ladd rb rz))); [|discriminate].
  destruct (Z.leb 0 (fst (irange fs (lsub rb eb))) && Z.ltb (snd (irange fs (lsub rb eb))) 140737488355328)%bool eqn:H1; [|discriminate].
  destruct (Z.leb 0 (fst (irange fs (lsub (ladd eb ez) (ladd rb rz)))) && Z.ltb (snd (irange fs (lsub (ladd eb ez) (ladd rb rz)))) 140737488355328)%bool eqn:H2; [|discriminate].
  apply Z.ltb_lt in H. apply andb_prop in H1 as [_ H1]. apply andb_prop in H2 as [_ H2]. apply Z.ltb_lt in H1, H2.
  pose proof (irange_sound E fs (lsub rb eb) HF) as Rd. fold (uE E (lsub rb eb)) in Rd.
  pose proof (irange_sound E fs (lsub (ladd eb ez) (ladd rb rz)) HF) as Re. fold (uE E (lsub (ladd eb ez) (ladd rb rz))) in Re.
  pose proof (irange_sound E fs rz HF) as Rz. fold (uE E rz) in Rz.
  pose proof (uE_range E rb) as B1. pose proof (uE_range E eb) as B2. pose proof (uE_range E rz) as B3. pose proof (uE_range E ez) as B4.
  assert (Hrb : uE E eb <= uE E rb /\ uE E rb < 2 ^ 48 + 2 ^ 47).
  { destruct (small_diff E rb eb _ _ Rd) as [[Hl He]|[Hl He]]; unfold two64 in *; lia. }
  split; [exact (proj1 Hrb)|].
  assert (EX : uE E (ladd eb ez) = uE E eb + uE E ez) by (rewrite uE_ladd_mod; apply Z.mod_small; unfold two64; lia).
  assert (EY : uE E (ladd rb rz) = uE E rb + uE E rz) by (rewrite uE_ladd_mod; apply Z.mod_small; unfold two64; lia).
  destruct (small_diff E (ladd eb ez) (ladd rb rz) _ _ Re) as [[Hl He]|[Hl He]]; rewrite EX, EY in *; unfold two64 in *; lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma sh_cover_sound : forall gs0 fuel cur hi, sh_cover gs0 cur hi fuel = true -> forall x, cur <= x < hi ->
  exists g cb cz, In g gs0 /\ is_mark g = false /\ is_const (fst (fst g)) = Some cb /\ is_const (snd (fst g)) = Some cz /\ cb <= x < cb + cz.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros gs0 fuel. induction fuel as [|f IH]; intros cur hi H x Hx; [discriminate|]. cbn [sh_cover] in H.
  destruct (Z.leb hi cur) eqn:Hle; [apply Z.leb_le in Hle; lia|].
  destruct (List.find (shc_at cur) gs0) as [g|] eqn:Hf; [|discriminate].
  destruct (is_const (snd (fst g))) as [z|] eqn:Hz; [|discriminate].
  apply List.find_some in Hf as [Hin Hc]. unfold shc_at in Hc. destruct (is_mark g) eqn:Hm; [discriminate|].
  destruct (is_const (fst (fst g))) as [b|] eqn:Hb; [|discriminate]. rewrite Hz in Hc.
  destruct (Z.eqb b cur) eqn:Hb1; [|discriminate]. apply Z.eqb_eq in Hb1. apply Z.ltb_lt in Hc. subst b.
  destruct (Z_lt_le_dec x (cur + z)) as [Hlt|Hge].
  - exists g, cur, z. repeat split; try assumption; lia.
  - exact (IH (cur + z) hi H x ltac:(lia)).
Qed.
#[using="Type"] Lemma terms_in_nonconst : forall l tb, terms_in (l_t l) tb = true -> is_const l = None.
Proof. LiaFast.lf_pins LiaFast.u0. intros l tb H. unfold is_const. destruct (l_t l); [discriminate H | reflexivity]. Qed.
#[using="Type"] Lemma grant_in_acc_spec : forall gs0 j1 j2 i R, grant_in_acc fs gs0 j1 j2 i R = true ->
  exists i' g, (i <= i')%nat /\ i' <> j1 /\ i' <> j2 /\ nth_error gs0 (i' - i) = Some g /\ is_mark g = false /\
    is_const (fst (fst g)) = None /\ inside_lin fs (rg_base R) (rg_size R) (fst (fst g)) (snd (fst g)) = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction gs0 as [|g r IH]; intros j1 j2 i R H; cbn [grant_in_acc] in H; [discriminate|].
  destruct (if is_mark g then false else if Nat.eqb i j1 then false else if Nat.eqb i j2 then false
            else if terms_in (l_t (fst (fst g))) (l_t (rg_base R)) then inside_lin fs (rg_base R) (rg_size R) (fst (fst g)) (snd (fst g)) else false) eqn:Hh.
  - destruct (is_mark g) eqn:Hm; [discriminate|]. destruct (Nat.eqb i j1) eqn:H1; [discriminate|]. destruct (Nat.eqb i j2) eqn:H2; [discriminate|].
    destruct (terms_in (l_t (fst (fst g))) (l_t (rg_base R))) eqn:Ht; [|discriminate].
    apply Nat.eqb_neq in H1, H2. exists i, g. rewrite Nat.sub_diag. repeat split; try assumption; [lia | exact (terms_in_nonconst _ _ Ht)].
  - destruct (IH j1 j2 (Datatypes.S i) R H) as (i' & g' & Hi & Hj1 & Hj2 & Hn & Hrest). exists i', g'. split; [lia|]. split; [exact Hj1|]. split; [exact Hj2|].
    replace (i' - i)%nat with (Datatypes.S (i' - Datatypes.S i)) by lia. cbn [nth_error]. split; [exact Hn | exact Hrest].
Qed.
(* [comment removed for export] *)
#[using="BL HF Hmaps Hpd Hgsh"] Lemma grant_in_pts : forall j1 j2 R, grant_in_e fs gs j1 j2 R = true ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R ->
    covered (vm_maps (m_vmmaps model)) w = true /\ ~ (SH_LO <= w < SH_HI) /\
    (forall j g, nth_error gs j = Some g -> is_mark g = false -> j = j1 \/ j = j2 -> ~ (uE E (fst (fst g)) <= w < uE E (fst (fst g)) + gsz E g)).
Proof. LiaFast.lf_pins (fun (BL HF Hmaps Hpd Hgsh : LiaFast.U) => LiaFast.u0).
  intros j1 j2 R H w Hw. unfold grant_in_e in H. destruct (grant_in_acc fs gs j1 j2 O R) eqn:Ha; [|discriminate].
  destruct (grant_in_acc_spec gs j1 j2 O R Ha) as (i & g & _ & Hi1 & Hi2 & Hn & Hm & Hnc & Hin). rewrite Nat.sub_0_r in Hn.
  pose proof Hgsh as Hgsh0. rewrite Forall_forall in Hgsh0. destruct (Hgsh0 g (nth_error_In _ _ Hn)) as (G1 & _ & _ & G4 & G5).
  assert (Hb48 : uE E (fst (fst g)) + uE E (snd (fst g)) < 2 ^ 48) by (unfold gsz in G4; lia).
  destruct (inside_lin_sound _ _ _ _ Hin Hb48) as [C1 C2]. fold (gsz E g) in C2. unfold rsz in Hw. fold (uE E (rg_size R)) in Hw.
  assert (Hwg : uE E (fst (fst g)) <= w < uE E (fst (fst g)) + gsz E g) by lia.
  pose proof Hpd as Hpd0. rewrite Hmaps in Hpd0.
  split; [|split].
  - exact (grant_pts_covered E gs model BL Hmaps Hgsh i g (fst (fst g)) (gsz E g) Hn Hm ltac:(lia) ltac:(lia) w Hwg).
  - intros Hsh. destruct (sh_cover_sound _ _ _ _ H w Hsh) as (g' & cb & cz & Hin' & Hm' & Hb' & Hz' & Hxc).
    destruct (In_nth_error _ _ Hin') as (i' & Hi').
    assert (Hne : i' <> i). { intros ->. rewrite Hn in Hi'. injection Hi' as <-. rewrite Hnc in Hb'. discriminate. }
    pose proof (pdisj_lden_nth E _ _ i' i g' g Hpd0 Hi' Hn Hne Hm' Hm) as Hdj.
    destruct (is_const_sound E _ cb Hb') as [Hbv Hbr']. destruct (is_const_sound E _ cz Hz') as [Hzv Hzr'].
    unfold iv_disj, FxBacking.B, FxBacking.S, gden in Hdj. cbn [fst snd] in Hdj. rewrite Hbv, Hzv in Hdj.
    rewrite (fg64' cb Hbr'), (fg64' cz Hzr') in Hdj. unfold gsz, uE in Hwg. lia.
  - intros j gj Hj Hmj Hjj Hwj.
    assert (Hne : j <> i) by (destruct Hjj as [-> | ->]; intros X; [apply Hi1 | apply Hi2]; symmetry; exact X).
    pose proof (pdisj_lden_nth E _ _ j i gj g Hpd0 Hj Hn Hne Hmj Hm) as Hdj.
    unfold iv_disj, FxBacking.B, FxBacking.S, gden in Hdj. cbn [fst snd] in Hdj. unfold gsz, uE in Hwg, Hwj. lia.
Qed.
(* [comment removed for export] *)
#[using="HF"] Lemma inside_sh_sound : forall R eb ez,
  inside_lin fs (lscale 8 (laddc (rg_base R) (- SH_OFF))) (lscale 8 (rg_size R)) eb ez = true ->
  Z.ltb (snd (irange fs (rg_base R))) 281474976710656 = true -> Z.ltb (snd (irange fs (rg_size R))) 140737488355328 = true ->
  uE E eb + uE E ez < 2 ^ 48 ->
  SH_OFF <= uE E (rg_base R) /\ uE E eb <= 8 * (uE E (rg_base R) - SH_OFF) /\
  8 * (uE E (rg_base R) - SH_OFF) + 8 * uE E (rg_size R) <= uE E eb + uE E ez.
Proof. LiaFast.lf_pins (fun (HF : LiaFast.U) => LiaFast.u0).
  intros R eb ez HB H0 H1 Hb48. apply Z.ltb_lt in H0, H1.
  pose proof (irange_sound E fs (rg_base R) HF) as Rb. fold (uE E (rg_base R)) in Rb.
  pose proof (irange_sound E fs (rg_size R) HF) as Rzz. fold (uE E (rg_size R)) in Rzz.
  destruct (inside_lin_sound _ _ _ _ HB Hb48) as [L1 L2].
  pose proof (uE_range E (rg_base R)) as B1. pose proof (uE_range E (rg_size R)) as B3.
  pose proof (uE_range E eb) as B5. pose proof (uE_range E ez) as B6.
  set (s := uE E (rg_base R)) in *. set (zv := uE E (rg_size R)) in *.
  assert (Hs : SH_OFF <= s).
  { destruct (Z_lt_le_dec s SH_OFF) as [Hlt|Hge]; [exfalso|exact Hge].
    rewrite uE_lscale_mod, uE_laddc_mod in L2. fold s in L2. rewrite Z.mul_mod_idemp_r in L2 by (unfold two64; lia).
    pose proof (Z.mod_pos_bound (8 * zv) two64 ltac:(unfold two64; lia)) as Bz. rewrite uE_lscale_mod in L2. fold zv in L2.
    destruct (mod64_cases (8 * (s + - SH_OFF)) ltac:(unfold SH_OFF, two64 in *; lia)) as [[N1 N2]|[[N1 N2]|[N1 N2]]]; rewrite N1 in L2;
      unfold SH_OFF, two64 in *; lia. }
  assert (EA : uE E (lscale 8 (laddc (rg_base R) (- SH_OFF))) = 8 * (s - SH_OFF)).
  { rewrite uE_lscale_mod, uE_laddc_mod. fold s. rewrite (Z.mod_small (s + - SH_OFF)) by (unfold SH_OFF, two64 in *; lia).
    rewrite Z.mod_small by (unfold SH_OFF, two64 in *; lia). lia. }
  assert (EZ : uE E (lscale 8 (rg_size R)) = 8 * zv) by (rewrite uE_lscale_mod; fold zv; apply Z.mod_small; unfold two64 in *; lia).
  rewrite EA, EZ in L2. rewrite EA in L1. split; [exact Hs|]. split; [exact L1 | exact L2].
Qed.
#[using="Type"] Lemma grant_sh_acc_spec : forall gs0 j i R, grant_sh_acc fs gs0 j i R = true ->
  exists i' g, (i <= i')%nat /\ i' <> j /\ nth_error gs0 (i' - i) = Some g /\ is_mark g = false /\
    inside_lin fs (lscale 8 (laddc (rg_base R) (- SH_OFF))) (lscale 8 (rg_size R)) (fst (fst g)) (snd (fst g)) = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction gs0 as [|g r IH]; intros j i R H; cbn [grant_sh_acc] in H; [discriminate|].
  destruct (if is_mark g then false else if Nat.eqb i j then false
            else if sh_terms (l_t (fst (fst g))) (l_t (rg_base R))
                 then inside_lin fs (lscale 8 (laddc (rg_base R) (- SH_OFF))) (lscale 8 (rg_size R)) (fst (fst g)) (snd (fst g)) else false) eqn:Hh.
  - destruct (is_mark g) eqn:Hm; [discriminate|]. destruct (Nat.eqb i j) eqn:H1; [discriminate|].
    destruct (sh_terms (l_t (fst (fst g))) (l_t (rg_base R))); [|discriminate].
    apply Nat.eqb_neq in H1. exists i, g. rewrite Nat.sub_diag. repeat split; try assumption. lia.
  - destruct (IH j (Datatypes.S i) R H) as (i' & g' & Hi & Hj & Hn & Hrest). exists i', g'. split; [lia|]. split; [exact Hj|].
    replace (i' - i)%nat with (Datatypes.S (i' - Datatypes.S i)) by lia. cbn [nth_error]. split; [exact Hn | exact Hrest].
Qed.
(* [comment removed for export] *)
#[using="HF Hgsh"] Lemma grant_in_sh_pts : forall j R, grant_in_sh fs gs j R = true ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R ->
    SH_OFF <= w /\ exists i g, i <> j /\ nth_error gs i = Some g /\ is_mark g = false /\
      uE E (fst (fst g)) <= 8 * (w - SH_OFF) < uE E (fst (fst g)) + gsz E g.
Proof. LiaFast.lf_pins (fun (HF Hgsh : LiaFast.U) => LiaFast.u0).
  intros j R H w Hw. unfold grant_in_sh in H. destruct (grant_sh_acc fs gs j O R) eqn:Ha; [|discriminate].
  destruct (Z.ltb (snd (irange fs (rg_base R))) 281474976710656) eqn:H0; [|discriminate].
  destruct (grant_sh_acc_spec gs j O R Ha) as (i & g & _ & Hi & Hn & Hm & Hin). rewrite Nat.sub_0_r in Hn.
  pose proof Hgsh as Hgsh0. rewrite Forall_forall in Hgsh0. destruct (Hgsh0 g (nth_error_In _ _ Hn)) as (G1 & _ & _ & G4 & G5).
  assert (Hb48 : uE E (fst (fst g)) + uE E (snd (fst g)) < 2 ^ 48) by (unfold gsz in G4; lia).
  destruct (inside_sh_sound R _ _ Hin H0 H Hb48) as (S1 & S2 & S3). fold (gsz E g) in S3. unfold rsz in Hw. fold (uE E (rg_size R)) in Hw.
  split; [lia|]. exists i, g. split; [exact Hi|]. split; [exact Hn|]. split; [exact Hm|]. lia.
Qed.
#[using="HF m0 HI Hext"] Lemma ext_in_route : forall R, 0 <= rsz E R -> ext_in fs a R = true ->
  exists p, In p (a_ext a) /\ ext_sem pz (uE E (fst p)) (uE E (snd p)) /\
    ((uE E (fst p) <= uE E (rg_base R) /\ uE E (rg_base R) + rsz E R <= uE E (fst p) + uE E (snd p)) \/
     exists c, In c CLS /\ live_shadow E a R c).
Proof. LiaFast.lf_pins (fun (HF m0 HI Hext : LiaFast.U) => LiaFast.u0).
  intros R Hz H. pose proof ps_geo as G. unfold ext_in in H. rewrite existsb_l_eq in H. apply existsb_exists in H as (p & Hp & H1).
  destruct (Hext p Hp) as ((c & Hc & X1 & X2 & X3) & _). pose proof (in_cls_rng c Hc) as Hcr.
  destruct (cls_tbl c Hc) as (Hszp & Hs8 & Hsz8 & Hnw & Hnm & Hmc).
  assert (Hjb : 0 <= z_j pz c /\ sz_tbl c * z_j pz c <= 262144 /\ sz_tbl c / 8 * z_j pz c <= 32768).
  { destruct HI as [_ _ _ _ _ _ _ _ _ _ _ Hcls]. destruct (Hcls c Hc) as [(J0 & _)|(J1 & _ & Jb & _)]; [rewrite J0; lia|]. split; [lia|]. split; nia. }
  assert (Hb48 : uE E (fst p) + uE E (snd p) < 2 ^ 48) by lia.
  exists p. split; [exact Hp|]. split; [exact (Hext p Hp)|]. unfold ext_in1 in H1.
  destruct (inside_lin fs (rg_base R) (rg_size R) (fst p) (snd p)) eqn:HA.
  - left. destruct (inside_lin_sound _ _ _ _ HA Hb48) as [L1 L2]. unfold rsz in *. fold (uE E (rg_size R)) in *. split; lia.
  - right. exists c. split; [exact Hc|]. unfold live_shadow. fold pz. destruct (inside_lin fs (lscale 8 (laddc (rg_base R) (- SH_OFF))) (lscale 8 (rg_size R)) (fst p) (snd p)) eqn:HB; [|discriminate].
    destruct (Z.ltb (snd (irange fs (rg_base R))) 281474976710656) eqn:H0; [|discriminate].
    apply Z.ltb_lt in H0, H1. pose proof (irange_sound E fs (rg_base R) HF) as Rb. fold (uE E (rg_base R)) in Rb.
    pose proof (irange_sound E fs (rg_size R) HF) as Rzz. fold (uE E (rg_size R)) in Rzz.
    destruct (inside_lin_sound _ _ _ _ HB Hb48) as [L1 L2].
    pose proof (uE_range E (rg_base R)) as B1. pose proof (uE_range E (rg_size R)) as B3.
    set (s := uE E (rg_base R)) in *. set (zv := uE E (rg_size R)) in *.
    assert (Hs : SH_OFF <= s).
    { destruct (Z_lt_le_dec s SH_OFF) as [Hlt|Hge]; [exfalso|exact Hge].
      rewrite uE_lscale_mod, uE_laddc_mod in L2. fold s in L2. rewrite Z.mul_mod_idemp_r in L2 by (unfold two64; lia).
      pose proof (Z.mod_pos_bound (8 * zv) two64 ltac:(unfold two64; lia)) as Bz. rewrite uE_lscale_mod in L2. fold zv in L2.
      destruct (mod64_cases (8 * (s + - SH_OFF)) ltac:(unfold SH_OFF, two64 in *; lia)) as [[N1 N2]|[[N1 N2]|[N1 N2]]]; rewrite N1 in L2;
        unfold SH_OFF, two64 in *; lia. }
    assert (EA : uE E (lscale 8 (laddc (rg_base R) (- SH_OFF))) = 8 * (s - SH_OFF)).
    { rewrite uE_lscale_mod, uE_laddc_mod. fold s. rewrite (Z.mod_small (s + - SH_OFF)) by (unfold SH_OFF, two64 in *; lia).
      rewrite Z.mod_small by (unfold SH_OFF, two64 in *; lia). lia. }
    assert (EZ : uE E (lscale 8 (rg_size R)) = 8 * zv) by (rewrite uE_lscale_mod; fold zv; apply Z.mod_small; unfold two64 in *; lia).
    rewrite EA, EZ in L2. rewrite EA in L1.
    assert (Hm8 : z_sb pz = 8 * (z_sb pz / 8)) by (pose proof (Z.div_mod (z_sb pz) 8 ltac:(lia)) as Ed; lia).
    unfold rsz in *. fold zv in Hz |- *. fold s.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _). rewrite G7.
    replace (sz_tbl c * z_j pz c) with (8 * (sz_tbl c / 8 * z_j pz c)) in X2 by (rewrite Hs8 at 2; ring).
    destruct Hjb as (_ & _ & Hjb3). set (PJ := sz_tbl c / 8 * z_j pz c) in *. set (K := z_sb pz / 8) in *.
    change (bv_unsigned (lden E (rg_size R))) with zv in *.
    clear -L1 L2 X1 X2 Hm8 Hjb3 Hs Hz. unfold SH_OFF in *. split; [lia|]. split; lia.
Qed.
#[using="HF m0 HI Hext"] Lemma ext_in_sound : forall R, 0 <= rsz E R -> ext_in fs a R = true -> live_sem E a R.
Proof. LiaFast.lf_pins (fun (HF m0 HI Hext : LiaFast.U) => LiaFast.u0).
  intros R Hz H. destruct (ext_in_route R Hz H) as (p & Hp & ((c & Hc & X1 & X2 & X3) & _) & [[L1 L2]|(c' & Hc' & Hl)]).
  - exists c. split; [exact Hc|]. left. pose proof (live_in_jb c Hc) as Hjb. fold pz. lia.
  - exists c'. split; [exact Hc'|]. right. exact Hl.
Qed.
(* [comment removed for export] *)
#[using="model BL HF Hmaps Hgsh Hsp Hsphi Hspok Hmres res Hres Hgqres"] Lemma sep_app2_gq : forall j a n R, 0 <= rsz E R -> uE E (rg_base R) + rsz E R <= two64 -> sep_app2_b fs gs j sp a n R = true ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (930696 <= w < 930736).
Proof. LiaFast.lf_pins (fun (model BL HF Hmaps Hgsh Hsp Hsphi Hspok Hmres res Hres Hgqres : LiaFast.U) => LiaFast.u0).
  intros j a0 n R Hz Hr H w Hw Hgq. rewrite sep_app2_b_app in H.
  pose proof (irange_sound E fs (rg_size R) HF) as Rs. unfold rsz in Rs. fold (rsz E R) in Rs.
  pose proof (alloc_top_lo _ Hspok) as Htl. unfold alloc_top, stack_max_size in Htl. rewrite Hsp in Htl. fold (uE E sp) in Htl.
  apply orb_prop in H as [H|H].
  - rewrite sep_app_b_eq in H. apply orb_prop in H as [H|H].
    + destruct (sep_grant_acc_spec fs gs j O R H) as (i' & g' & _ & Hne & Hn' & Hs1 & Hc & Hmk'). rewrite Nat.sub_0_r in Hn'.
      pose proof Hgsh as Hgsh0. rewrite Forall_forall in Hgsh0. pose proof (Hgsh0 g' (nth_error_In _ _ Hn')) as Gg'.
      pose proof (gsz_bounds E fs g' HF) as Gb.
      destruct (contained_sound E fs (rg_base R) _ (fst (fst g')) (gsz_lo fs g') HF Hc ltac:(lia)
                  ltac:(destruct Gg' as (_ & _ & _ & G4 & _); unfold two64; lia)) as [C1 C2].
      pose proof (grant_pts_covered E gs model BL Hmaps Hgsh i' g' (fst (fst g')) (gsz E g') Hn' Hmk' ltac:(lia) ltac:(lia) w ltac:(lia)) as Hcov.
      pose proof (Hmres w Hcov) as Hnr. rewrite Hres in Hnr.
      rewrite (in_res_sound res 930696 930736 w Hgqres Hgq) in Hnr. discriminate.
    + unfold sep_band_b in H. pose proof (uE_range E sp). pose proof (uE_range E (rg_base R)). unfold sp_window_hi in Hsphi. rewrite Hsp in Hsphi. fold (uE E sp) in Hsphi.
      apply orb_prop in H as [H|H].
      * apply Z.leb_le in H. pose proof (irange_sound E fs (lsub sp (rg_base R)) HF) as Rd. fold (uE E (lsub sp (rg_base R))) in Rd.
        destruct (small_diff E sp (rg_base R) _ _ Rd) as [[Hl He]|[Hl He]]; unfold two64 in *; lia.
      * apply Z.ltb_lt in H. pose proof (irange_sound E fs (lsub (rg_base R) sp) HF) as Rd. fold (uE E (lsub (rg_base R) sp)) in Rd.
        destruct (small_diff E (rg_base R) sp _ _ Rd) as [[Hl He]|[Hl He]]; unfold two64 in *; lia.
  - apply andb_prop in H as [_ H]. unfold sep_shadow_b in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply Z.leb_le in H.
    pose proof (irange_sound E fs (rg_base R) HF) as Rb. fold (uE E (rg_base R)) in Rb. unfold SH_LO in H. lia.
Qed.
(* [comment removed for export] *)
Definition sep_route (R : region) : Prop :=
  (forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ FPmax pz w) \/
  (exists c, In c CLS /\ live_in fs a R c = true) \/ ext_in fs a R = true.
#[using="HF m0 HI Hext"] Lemma sep_route_sem : forall R, 0 <= rsz E R -> sep_route R ->
  (forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ FPmax pz w) \/ live_sem E a R.
Proof. LiaFast.lf_pins (fun (HF m0 HI Hext : LiaFast.U) => LiaFast.u0).
  intros R Hz [H|[(c & Hc & H)|H]]; [left; exact H | right; exact (live_in_sound R c Hc Hz H) | right; exact (ext_in_sound R Hz H)].
Qed.
#[using="model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi Hspok Hmres res Hres Hgqres m0 HI gP gT HjP HbP HsP HjT HbT HsT"] Lemma pri_sep_gen_route : forall R, 0 <= rsz E R -> uE E (rg_base R) + rsz E R <= two64 ->
  (if existsb (live_in fs a R) CLS then true
   else if ext_in fs a R then true
   else if grant_in_e fs gs jP jT R then true
   else if grant_in_sh fs gs jP R then true
   else if sep_app2_b fs gs jP sp (p_pg a) PG_SIZE R
        then (if pc_ri_ref fs gs jP sp a R
              then (if rgs_sep fs (l_cb a) CB_SIZE R then true else sep_app2_b fs gs jT sp (l_cb a) CB_SIZE R)
              else false)
        else false) = true ->
  sep_route R.
Proof. LiaFast.lf_pins (fun (model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi Hspok Hmres res Hres Hgqres m0 HI gP gT HjP HbP HsP HjT HbT HsT : LiaFast.U) => LiaFast.u0).
  intros R Hz Hr H. pose proof ps_geo as G. destruct cache_in_T as [CT1 CT2]. unfold sep_route.
  destruct (existsb (live_in fs a R) CLS) eqn:Hlv.
  { right; left. apply existsb_exists in Hlv as (c & Hc & Hl). exists c. split; [exact Hc | exact Hl]. }
  destruct (ext_in fs a R) eqn:Hxi.
  { right; right. reflexivity. }
  destruct (grant_in_e fs gs jP jT R) eqn:Hgi.
  { (* [comment removed for export] *)
    left. intros w Hw. destruct (grant_in_pts jP jT R Hgi w Hw) as (Hcov & Hnsh & Hdj). intros [F|[F|[F|F]]].
    - apply (Hdj jP gP HjP gP_nm (or_introl eq_refl)). rewrite ub_P, gz_P. exact F.
    - apply (Hdj jT gT HjT gT_nm (or_intror eq_refl)). rewrite u_cb in CT1, CT2. unfold CB_SIZE in CT2. lia.
    - apply Hnsh. destruct G as (_ & _ & _ & _ & _ & _ & G7 & G8 & G9 & _). unfold SH_LO, SH_HI. lia.
    - pose proof (Hmres w Hcov) as Hnr. rewrite Hres in Hnr. rewrite (in_res_sound res 930696 930736 w Hgqres F) in Hnr. discriminate. }
  destruct (grant_in_sh fs gs jP R) eqn:Hgs.
  { (* [comment removed for export] *)
    left. intros w Hw. destruct (grant_in_sh_pts jP R Hgs w Hw) as (Hso & i & g & Hi & Hn & Hm & Hwg).
    pose proof Hgtop as Hgtop0. rewrite Forall_forall in Hgtop0. pose proof (Hgtop0 g (nth_error_In _ _ Hn)) as Gt.
    unfold alloc_top, stack_max_size in Gt. unfold sp_window_hi in Hsphi.
    destruct HI as [_ _ _ _ Hpg _ Hnsh _ _ _ _ _]. destruct G as (_ & _ & _ & _ & _ & G6 & G7 & _ & _ & G10 & _).
    intros [F|[F|[F|F]]].
    - unfold SH_OFF in *. lia.
    - unfold SH_OFF in *. lia.
    - (* [comment removed for export] *)
      pose proof Hpd as Hpd0. rewrite Hmaps in Hpd0.
      pose proof (pdisj_lden_nth E _ _ i jP g gP Hpd0 Hn HjP Hi Hm gP_nm) as Hdj.
      unfold iv_disj, FxBacking.B, FxBacking.S, gden in Hdj. cbn [fst snd] in Hdj.
      pose proof ub_P as UP. pose proof gz_P as ZP. unfold gsz, uE in UP, ZP, Hwg. unfold PG_SIZE in *.
      assert (Hm8 : z_sb pz = 8 * (z_sb pz / 8)) by (pose proof (Z.div_mod (z_sb pz) 8 ltac:(lia)) as Ed; lia).
      unfold SH_OFF in *. lia.
    - unfold SH_OFF in *. lia. }
  left. destruct (sep_app2_b fs gs jP sp (p_pg a) PG_SIZE R) eqn:H1; [|discriminate].
  destruct (pc_ri_ref fs gs jP sp a R) eqn:H2; [|discriminate]. unfold pc_ri_ref in H2.
  intros w Hw [F|[F|[F|F]]]; [| | | exact (sep_app2_gq jP (p_pg a) PG_SIZE R Hz Hr H1 w Hw F)].
  - (* [comment removed for export] *)
    rewrite <- u_pg in F.
    refine (sep_app2_sound E fs gs model sp BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi jP gP (p_pg a) PG_SIZE R HjP gP_nm _ _ _ Hz Hr H1 w Hw F).
    + rewrite HbP. lia.
    + rewrite HbP, gz_P. lia.
    + unfold PG_SIZE, two64. lia.
  - (* [comment removed for export] *)
    destruct (rgs_sep fs (l_cb a) CB_SIZE R) eqn:H3.
    + replace (z_ca pz - 128) with (uE E (l_cb a)) in F by exact u_cb. replace (z_ca pz + 2592) with (uE E (l_cb a) + CB_SIZE) in F by (rewrite u_cb; unfold CB_SIZE; lia).
      exact (rgs_sep_sound E fs (l_cb a) CB_SIZE R HF ltac:(unfold CB_SIZE; lia) ltac:(rewrite u_cb; unfold CB_SIZE; lia) Hr H3 w Hw F).
    + replace (z_ca pz - 128) with (uE E (l_cb a)) in F by exact u_cb. replace (z_ca pz + 2592) with (uE E (l_cb a) + CB_SIZE) in F by (rewrite u_cb; unfold CB_SIZE; lia).
      exact (sep_app2_sound E fs gs model sp BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi jT gT (l_cb a) CB_SIZE R HjT gT_nm CT1 CT2 ltac:(unfold two64, CB_SIZE; lia) Hz Hr H w Hw F).
  - (* [comment removed for export] *)
    destruct (sep_pc_b fs gs jP sp R) eqn:H4.
    + assert (X : ~ (uE E (p_sb a) / 8 + SH_OFF <= w < uE E (p_sb a) / 8 + SH_OFF + 137438953472 / 8)).
      { refine (sep_pc_sound E fs gs model sp BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi jP gP (p_sb a) 137438953472 R HjP gP_nm _ _ _ _ _ _ _ Hz Hr H4 w Hw).
        - rewrite ub_P, u_sb. lia.
        - rewrite ub_P, gz_P, u_sb. unfold PG_SIZE. lia.
        - rewrite u_sb. lia.
        - reflexivity.
        - lia.
        - rewrite u_sb. unfold SH_LO, SH_OFF. lia.
        - rewrite u_sb. unfold SH_HI, SH_OFF. change (137438953472 / 8) with 17179869184. lia. }
      apply X. rewrite u_sb. unfold SH_OFF. change (137438953472 / 8) with 17179869184. lia.
    + destruct (ri_shadow_b fs a R) eqn:H5.
      * clear H2. rename H5 into H2. unfold ri_shadow_b in H2. destruct (lin_off (rg_base R) (p_sh a)) as [d|] eqn:Hd; [|discriminate].
        apply andb_prop in H2 as [D1 D2]. apply Z.leb_le in D1, D2.
        pose proof (irange_sound E fs (rg_size R) HF) as Rs. fold (rsz E R) in Rs.
        pose proof (lin_off_u E _ _ d Hd) as Eb. fold (uE E (p_sh a)) in Eb. rewrite u_sh in Eb. specialize (Eb ltac:(unfold two64; lia)).
        fold (uE E (rg_base R)) in Eb. lia.
      * (* [comment removed for export] *)
        pose proof (irange_sound E fs (rg_size R) HF) as Rs. fold (rsz E R) in Rs.
        pose proof (twoc_ns_noshadow E fs (rg_base R) (snd (irange fs (rg_size R))) HF H2 ltac:(lia) w ltac:(lia)) as Hns.
        unfold in_shadow in Hns. apply andb_false_iff in Hns.
        destruct G as (_ & _ & _ & _ & _ & _ & G7 & G8 & G9 & _).
        destruct Hns as [Hns|Hns]; [apply Z.leb_gt in Hns | apply Z.ltb_ge in Hns]; unfold SH_LO, SH_HI in *; lia.
Qed.
#[using="model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi Hspok Hmres Hres Hgqres m0 HI gP gT HjP HbP HsP HjT HbT HsT"] Lemma pri_sep_f_route : forall R, 0 <= rsz E R -> uE E (rg_base R) + rsz E R <= two64 ->
  pri_sep_f fs gs res jP jT sp a R = true ->
  sep_route R.
Proof. LiaFast.lf_pins (fun (model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi Hspok Hmres Hres Hgqres m0 HI gP gT HjP HbP HsP HjT HbT HsT : LiaFast.U) => LiaFast.u0).
  intros R Hz Hr H. pose proof ps_geo as G. destruct cache_in_T as [CT1 CT2]. unfold pri_sep_f in H. rewrite existsb_l_eq in H.
  assert (HcaT : forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> sep_app2_b fs gs jT sp (l_cb a) CB_SIZE R = true ->
            ~ (z_ca pz - 128 <= w < z_ca pz + 2592)).
  { intros w Hw Hs. replace (z_ca pz - 128) with (uE E (l_cb a)) by exact u_cb. replace (z_ca pz + 2592) with (uE E (l_cb a) + CB_SIZE) by (rewrite u_cb; unfold CB_SIZE; lia).
    exact (sep_app2_sound E fs gs model sp BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi jT gT (l_cb a) CB_SIZE R HjT gT_nm CT1 CT2 ltac:(unfold two64, CB_SIZE; lia) Hz Hr Hs w Hw). }
  destruct (is_const (rg_base R)) as [b|] eqn:Eb; [destruct (is_const (rg_size R)) as [z|] eqn:Ez|].
  - (* [comment removed for export] *)
    unfold sep_route. left. intros w Hw. assert (Hub : uE E (rg_base R) = b) by (unfold uE; exact (is_const_u E _ _ Eb)).
    assert (Huz : rsz E R = z) by (unfold rsz; exact (is_const_u E _ _ Ez)).
    destruct (Z.leb (b + z) 2201439137792) eqn:Hlo; [|discriminate]. apply Z.leb_le in Hlo.
    destruct (if Z.leb (b + z) 930696 then true else Z.leb 930736 b) eqn:Hgq0; [|discriminate].
    assert (Hgq1 : b + z <= 930696 \/ 930736 <= b) by (destruct (Z.leb (b + z) 930696) eqn:Q1; [left; apply Z.leb_le; exact Q1 | right; apply Z.leb_le; exact Hgq0]).
    intros [F|[F|[F|F]]]; [lia | | lia | lia].
    destruct (sep_res_b res R) eqn:Hsr; [|exact (HcaT w Hw H F)].
    unfold sep_res_b in Hsr. rewrite Eb, Ez in Hsr. apply andb_prop in Hsr as [_ Hin].
    pose proof (in_res_sound res b (b + z) w Hin ltac:(lia)) as Hcr. rewrite <- Hres in Hcr.
    assert (Hcm : covered (vm_maps (m_vmmaps model)) w = true).
    { apply (grant_pts_covered E gs model BL Hmaps Hgsh jT gT (fst (fst gT)) (gsz E gT) HjT gT_nm ltac:(lia) ltac:(lia)). rewrite ub_T, gz_T. unfold TG_SIZE. lia. }
    rewrite (Hmres w Hcm) in Hcr. discriminate.
  - exact (pri_sep_gen_route R Hz Hr H).
  - exact (pri_sep_gen_route R Hz Hr H).
Qed.
#[using="model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi Hspok Hmres Hres Hgqres m0 HI gP gT HjP HbP HsP HjT HbT HsT Hext"] Lemma pri_sep_f_sound : forall R, 0 <= rsz E R -> uE E (rg_base R) + rsz E R <= two64 ->
  pri_sep_f fs gs res jP jT sp a R = true ->
  (forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ FPmax pz w) \/ live_sem E a R.
Proof. LiaFast.lf_pins (fun (model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi Hspok Hmres Hres Hgqres m0 HI gP gT HjP HbP HsP HjT HbT HsT Hext : LiaFast.U) => LiaFast.u0). intros R Hz Hr H. exact (sep_route_sem R Hz (pri_sep_f_route R Hz Hr H)). Qed.
#[using="model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi Hspok Hmres Hres Hgqres m0 HI gP gT HjP HbP HsP HjT HbT HsT Hsepc"] Lemma pri_sep_c_route : forall R, 0 <= rsz E R -> uE E (rg_base R) + rsz E R <= two64 ->
  pri_sep_c fs gs res jP jT sp a R = true -> sep_route R.
Proof. LiaFast.lf_pins (fun (model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi Hspok Hmres Hres Hgqres m0 HI gP gT HjP HbP HsP HjT HbT HsT Hsepc : LiaFast.U) => LiaFast.u0).
  intros R Hz Hr H. unfold pri_sep_c in H. destruct (sep_cached a R) eqn:Hc; [left; exact (sep_cached_sound R Hz Hr Hc) | rewrite pri_sep_ff_eq in H; exact (pri_sep_f_route R Hz Hr H)].
Qed.
#[using="model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi Hspok Hmres Hres Hgqres m0 HI gP gT HjP HbP HsP HjT HbT HsT Hsepc Hext"] Lemma pri_sep_c_sound : forall R, 0 <= rsz E R -> uE E (rg_base R) + rsz E R <= two64 ->
  pri_sep_c fs gs res jP jT sp a R = true ->
  (forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ FPmax pz w) \/ live_sem E a R.
Proof. LiaFast.lf_pins (fun (model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi Hspok Hmres Hres Hgqres m0 HI gP gT HjP HbP HsP HjT HbT HsT Hsepc Hext : LiaFast.U) => LiaFast.u0).
  intros R Hz Hr H. unfold pri_sep_c in H. destruct (sep_cached a R) eqn:Hc; [left; exact (sep_cached_sound R Hz Hr Hc) | rewrite pri_sep_ff_eq in H; exact (pri_sep_f_sound R Hz Hr H)].
Qed.
(* [comment removed for export] *)
#[using="model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi Hspok Hmres Hres Hgqres m0 HI gP gT HjP HbP HsP HjT HbT HsT Hsepc"] Lemma pri_sep_t_route : forall R, 0 <= rsz E R -> uE E (rg_base R) + rsz E R <= two64 ->
  pri_sep_t fs gs res jP jT sp a R = true ->
  (forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ FPmax pz w) \/ ext_in fs a R = true.
Proof. LiaFast.lf_pins (fun (model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi Hspok Hmres Hres Hgqres m0 HI gP gT HjP HbP HsP HjT HbT HsT Hsepc : LiaFast.U) => LiaFast.u0).
  intros R Hz Hr H. unfold pri_sep_t in H. destruct (sep_cached a R) eqn:Hc; [left; exact (sep_cached_sound R Hz Hr Hc)|].
  destruct (existsb_l (live_in_l fs a R) CLS) eqn:Hl; [discriminate|]. rewrite pri_sep_ff_eq in H.
  destruct (pri_sep_f_route R Hz Hr H) as [X|[(c & Hcin & Hlc)|X]]; [left; exact X | | right; exact X].
  exfalso. rewrite (existsb_l_ext _ _ CLS (live_in_l_eq fs a R)), existsb_l_eq in Hl.
  assert (Ht : existsb (live_in fs a R) CLS = true) by (apply existsb_exists; exists c; split; [exact Hcin | exact Hlc]). rewrite Ht in Hl. discriminate.
Qed.
(* [comment removed for export] *)
Definition alloc_part (pz0 : list Z) (x : Z) : Prop :=
  exists c, In c CLS /\ (z_sb pz0 + 4294967296 * c <= x < z_sb pz0 + 4294967296 * c + sz_tbl c * z_j pz0 c \/
                        z_sh pz0 + 536870912 * c <= x < z_sh pz0 + 536870912 * c + sz_tbl c / 8 * z_j pz0 c).
#[using="model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi Hspok Hmres Hres Hgqres m0 HI gP gT HjP HbP HsP HjT HbT HsT Hsepc Hext"] Lemma pri_outside : forall rgs, Forall (fun R => 0 <= rsz E R /\ uE E (rg_base R) + rsz E R <= two64) rgs ->
  forallb (pri_sep_c fs gs res jP jT sp a) rgs = true ->
  forall x, 0 <= x < two64 -> FPmax pz x -> ~ alloc_part pz x -> outside E rgs (Z_to_bv 64 x).
Proof. LiaFast.lf_pins (fun (model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi Hspok Hmres Hres Hgqres m0 HI gP gT HjP HbP HsP HjT HbT HsT Hsepc Hext : LiaFast.U) => LiaFast.u0).
  intros rgs Hsz Hck x Hx HF0 Hna. unfold outside. rewrite Forall_forall in Hsz |- *. rewrite forallb_forall in Hck.
  intros R HR. destruct (Hsz R HR) as [Hz Hr]. rewrite u_small64 by exact Hx. fold (uE E (rg_base R)).
  destruct (Z_lt_le_dec x (uE E (rg_base R))) as [H1|H1]; [left; exact H1|].
  destruct (Z_lt_le_dec x (uE E (rg_base R) + rsz E R)) as [H2|H2]; [|right; exact H2]. exfalso.
  destruct (pri_sep_c_sound R Hz Hr (Hck R HR)) as [Hs|(c & Hc & Hl)].
  - exact (Hs x ltac:(lia) HF0).
  - apply Hna. exists c. split; [exact Hc|]. destruct Hl as [(L1 & L2 & _)|(L1 & L2 & _)]; [left | right]; lia.
Qed.
End PriSepOk.
(* [comment removed for export] *)
