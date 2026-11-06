(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Star5ef ArgvEnv RefL1zx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RefL1zx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_St4s2 D_coj29.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require BWorld.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ArgvEnv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefL1zx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefL1zx.D_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_St4s2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_coj29 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.BWorld.D_co8nq.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.

Module D_St6k6.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Star5ef ArgvEnv RefL1zx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RefL1zx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_St4s2 D_coj29.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ArgvEnv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefL1zx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefL1zx.D_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_St4s2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_coj29.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Plain.M.phdrs.

(* [comment removed for export] *)
Definition stn_mark {A : Type} (x : A) : Prop := True.
Definition stn_markm {A : Type} (x : A) : Prop := True.      (* [comment removed for export] *)
Lemma stn_ex_by_eq : forall (A : Type) (P : A -> Prop) (w : A), (forall x, x = w -> P x) -> exists x, P x.
Proof. intros A P w H. exists w. exact (H w eq_refl). Qed.
Lemma stn_msteps_tgt : forall segs st tgt, (forall stF, stF = tgt -> msteps segs st stF) -> msteps segs st tgt.
Proof. intros segs st tgt H. exact (H tgt eq_refl). Qed.
Lemma stn_regs_agree_regupds : forall (Cl : list reg) (l : list (reg * word)) base,
  forallb (fun p : reg * word => existsb (bv_eqb (fst p)) Cl) l = true ->
  regs_agree (fun r => In r Cl) base (regupds l base).
Proof.
  intros Cl l base. induction l as [|[r v] l IH]; cbn [regupds forallb]; intro H.
  - apply regs_agree_refl.
  - apply andb_prop in H. destruct H as [H1 H2]. apply regs_agree_upd; [| apply IH; exact H2].
    cbn [fst] in H1. apply existsb_exists in H1. destruct H1 as [x [Hx E]]. apply gresl_eq_of_eqb in E. subst x. exact Hx.
Qed.
Local Ltac stn_K := constr:(4%nat).
Local Ltac stn_depth R := lazymatch R with regupd ?R' _ _ => let d := stn_depth R' in constr:(S d) | _ => constr:(O) end.
Local Ltac stn_innermost m := lazymatch m with wbytes ?m' _ _ => lazymatch m' with wbytes _ _ _ => stn_innermost m' | _ => m end end.
Local Ltac stn_set t base :=
  let x := fresh base in set (x := t); pose proof (I : stn_mark x).
Local Ltac stn_grow_fact x :=
  let body := eval unfold x in x in
  lazymatch body with wbytes ?p ?a ?bs =>
    let H := fresh "HMG" in
    first [ match goal with Hp : mem_grows ?b0 p |- _ => assert (H : mem_grows b0 x) by (exact (mem_grows_trans b0 p x Hp (wbytes_grows bs p a))) end
          | assert (H : mem_grows p x) by (exact (wbytes_grows bs p a)) ]
  end.
Local Ltac stn_setm t base :=
  let x := fresh base in set (x := t); pose proof (I : stn_markm x); try stn_grow_fact x.
Local Ltac stn_name_regs R :=
  let d := stn_depth R in let k := stn_K in
  lazymatch eval cbv in (Nat.leb k d) with true => stn_set R ident:(RN) | false => idtac end.
Local Ltac stn_name_J :=
  repeat (lazymatch goal with |- msteps _ (mkst _ _ (cmem ?s _ ?J _) _) _ =>
    lazymatch J with wbytes _ _ _ => idtac end;
    let t := stn_innermost J in
    let j := fresh "JN" in set (j := t); pose proof (I : stn_markm j);
    try (let H := fresh "HJN" in assert (H : wfJ s j) by (unfold j; apply wfJ_wbytes; assumption)) end).
Local Ltac stn_name_D :=
  repeat (lazymatch goal with |- msteps _ (mkst _ _ (cmem _ _ _ ?D) _) _ =>
    lazymatch D with wbytes _ _ _ => idtac end;
    let t := stn_innermost D in (let x := fresh "DN" in set (x := t); pose proof (I : stn_markm x)) end).
Local Ltac stn_name_M :=
  repeat (lazymatch goal with |- msteps _ (mkst _ _ ?M _) _ =>
    lazymatch M with wbytes _ _ _ => idtac end;
    let t := stn_innermost M in stn_setm t ident:(MN) end).
(* [comment removed for export] *)
Local Ltac stn_eexists :=
  lazymatch goal with
  | |- @ex (bvmap _ _) _ => eapply stn_ex_by_eq; (let x := fresh "regsW" in let E := fresh "EregsW" in intros x E; pose proof (I : stn_mark E))
  | |- _ => eexists
  end.
Local Ltac stn_wit :=
  repeat match goal with
  | M : stn_mark ?E |- ?g => lazymatch type of E with ?x = _ => lazymatch g with context [x] => rewrite E end end
  end.
Local Ltac stn_begin :=
  lazymatch goal with
  | |- msteps _ _ ?t => tryif is_var t then idtac else (apply stn_msteps_tgt; let s := fresh "stF" in let E := fresh "EstF" in intros s E)
  | |- _ => idtac
  end.
Local Ltac renm :=
  stn_begin;
  lazymatch goal with
  | |- msteps _ (mkst ?R _ (cmem _ _ _ _) _) _ => stn_name_regs R; stn_name_J; stn_name_D
  | |- msteps _ (mkst ?R _ _ _) _ => stn_name_regs R; stn_name_M
  | |- _ => idtac
  end.
Local Ltac stn_open :=
  repeat match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end;
  try lazymatch goal with E : ?s = _ |- msteps _ _ ?s => rewrite E end.
Local Ltac stn_done :=
  repeat first [ match goal with H : stn_mark ?x |- ?g => lazymatch g with context [x] => unfold x end end
               | match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end ];
  try lazymatch goal with E : ?s = _ |- msteps _ _ ?s => rewrite E end;
  stn_wit.
(* [comment removed for export] *)
Local Open Scope Z_scope.
Definition stn_rr_ok (oa ob lo d n len : Z) : bool :=
  (0 <=? lo + d + oa) && (0 <=? lo + d + ob) && (0 <=? n) && (oa + n <=? 0) && (0 <=? len) && (ob + len <=? 0)
  && ((oa + n <=? ob) || (ob + len <=? oa)).
Definition stn_lr_ok (za ob lo d n len : Z) : bool :=
  (0 <=? lo + d + ob) && (0 <=? len) && (ob + len <=? 0) && (0 <=? za) && (0 <=? n) && (za + n <=? lo + d + ob).
Definition stn_rl_ok (oa zb lo d n len : Z) : bool :=
  (0 <=? lo + d + oa) && (0 <=? n) && (oa + n <=? 0) && (0 <=? zb) && (0 <=? len) && (zb + len <=? lo + d + oa).
Definition stn_ll_ok (za zb n len : Z) : bool :=
  (0 <=? za) && (0 <=? n) && (za + n <=? 2^64) && (0 <=? zb) && (0 <=? len) && (zb + len <=? 2^64) && (za <? 2^64) && (zb <? 2^64)
  && ((za + n <=? zb) || (zb + len <=? za)).
Lemma stn_lo0 : forall x lo : Z, lo <= x -> lo <= x - 0.
Proof. intros. lia. Qed.
Lemma stn_rel0 : forall u : Z, u = u + 0.
Proof. intros. lia. Qed.
Lemma stn_rel_add : forall x u o k : Z, x = u + o -> x + k = u + (o + k).
Proof. intros. lia. Qed.
Lemma stn_rel_sub : forall x u o k : Z, x = u + o -> x - k = u + (o - k).
Proof. intros. lia. Qed.
Lemma stn_peel_gen : forall segs bs m (za zb : Z) n,
  0 <= za < 2^64 -> za + Z.of_nat n <= 2^64 -> 0 <= zb < 2^64 -> zb + Z.of_nat (length bs) <= 2^64 ->
  (za + Z.of_nat n <= zb \/ zb + Z.of_nat (length bs) <= za) ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m za zb n Ha Han Hb Hbn Hd.
  apply rdn_wbytes_out; rewrite ?u_Z2bv by lia; lia.
Qed.
Local Ltac stn_bools Hok :=
  repeat (apply andb_prop in Hok; destruct Hok as [Hok ?]);
  repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end.
Lemma stn_peel_rr : forall segs bs m (w : word) (za zb oa ob lo d : Z) n len,
  za = bv_unsigned w + oa -> zb = bv_unsigned w + ob -> lo <= bv_unsigned w - d -> length bs = len ->
  stn_rr_ok oa ob lo d (Z.of_nat n) (Z.of_nat len) = true ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m w za zb oa ob lo d n len Ea Eb Hlo HL Hok. subst len. unfold stn_rr_ok in Hok. stn_bools Hok.
  pose proof (bv_unsigned_in_range 64 w) as R; unfold bv_modulus in R; change (2 ^ Z.of_N 64) with (2^64) in R.
  match goal with H : (_ || _)%bool = true |- _ => apply orb_prop in H; destruct H as [H|H]; apply Z.leb_le in H end;
  apply stn_peel_gen; lia.
Qed.
Lemma stn_peel_lr : forall segs bs m (w : word) (za zb ob lo d : Z) n len,
  zb = bv_unsigned w + ob -> lo <= bv_unsigned w - d -> length bs = len ->
  stn_lr_ok za ob lo d (Z.of_nat n) (Z.of_nat len) = true ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m w za zb ob lo d n len Eb Hlo HL Hok. subst len. unfold stn_lr_ok in Hok. stn_bools Hok.
  pose proof (bv_unsigned_in_range 64 w) as R; unfold bv_modulus in R; change (2 ^ Z.of_N 64) with (2^64) in R.
  apply stn_peel_gen; lia.
Qed.
Lemma stn_peel_rl : forall segs bs m (w : word) (za zb oa lo d : Z) n len,
  za = bv_unsigned w + oa -> lo <= bv_unsigned w - d -> length bs = len ->
  stn_rl_ok oa zb lo d (Z.of_nat n) (Z.of_nat len) = true ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m w za zb oa lo d n len Ea Hlo HL Hok. subst len. unfold stn_rl_ok in Hok. stn_bools Hok.
  pose proof (bv_unsigned_in_range 64 w) as R; unfold bv_modulus in R; change (2 ^ Z.of_N 64) with (2^64) in R.
  apply stn_peel_gen; lia.
Qed.
Lemma stn_peel_ll : forall segs bs m (za zb : Z) n len,
  length bs = len -> stn_ll_ok za zb (Z.of_nat n) (Z.of_nat len) = true ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m za zb n len HL Hok. subst len. unfold stn_ll_ok in Hok. stn_bools Hok.
  match goal with H : (_ || _)%bool = true |- _ => apply orb_prop in H; destruct H as [H|H]; apply Z.leb_le in H end;
  apply stn_peel_gen; lia.
Qed.

(* [comment removed for export] *)
Definition stn_rrz_ok (oa ob lo hi n len : Z) : bool :=
  (0 <=? lo + oa) && (0 <=? lo + ob) && (0 <=? n) && (hi + oa + n <=? 2^64) && (hi + oa <? 2^64) && (0 <=? len) && (hi + ob + len <=? 2^64) && (hi + ob <? 2^64)
  && ((oa + n <=? ob) || (ob + len <=? oa)).
Definition stn_lrz_ok (za ob lo hi n len : Z) : bool :=
  (0 <=? lo + ob) && (0 <=? len) && (hi + ob + len <=? 2^64) && (hi + ob <? 2^64) && (0 <=? za) && (0 <=? n) && (za + n <=? lo + ob).
Definition stn_rlz_ok (oa zb lo hi n len : Z) : bool :=
  (0 <=? lo + oa) && (0 <=? n) && (hi + oa + n <=? 2^64) && (hi + oa <? 2^64) && (0 <=? zb) && (0 <=? len) && (zb + len <=? lo + oa).
Lemma stn_peel_rrz : forall segs bs m (u za zb oa ob lo hi : Z) n len,
  za = u + oa -> zb = u + ob -> lo <= u -> u <= hi -> length bs = len ->
  stn_rrz_ok oa ob lo hi (Z.of_nat n) (Z.of_nat len) = true ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m u za zb oa ob lo hi n len Ea Eb Hlo Hhi HL Hok. subst len. unfold stn_rrz_ok in Hok. stn_bools Hok.
  match goal with H : (_ || _)%bool = true |- _ => apply orb_prop in H; destruct H as [H|H]; apply Z.leb_le in H end;
  apply stn_peel_gen; lia.
Qed.
Lemma stn_peel_lrz : forall segs bs m (u za zb ob lo hi : Z) n len,
  zb = u + ob -> lo <= u -> u <= hi -> length bs = len ->
  stn_lrz_ok za ob lo hi (Z.of_nat n) (Z.of_nat len) = true ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m u za zb ob lo hi n len Eb Hlo Hhi HL Hok. subst len. unfold stn_lrz_ok in Hok. stn_bools Hok.
  apply stn_peel_gen; lia.
Qed.
Lemma stn_peel_rlz : forall segs bs m (u za zb oa lo hi : Z) n len,
  za = u + oa -> lo <= u -> u <= hi -> length bs = len ->
  stn_rlz_ok oa zb lo hi (Z.of_nat n) (Z.of_nat len) = true ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m u za zb oa lo hi n len Ea Hlo Hhi HL Hok. subst len. unfold stn_rlz_ok in Hok. stn_bools Hok.
  apply stn_peel_gen; lia.
Qed.

Local Ltac stn_len bs :=
  lazymatch bs with
  | word_to_le_bytes ?n ?v => constr:(length_N_to_le_bytes n v)
  | zeros ?n => constr:(length_zeros n)
  | repeat ?x ?n => constr:(repeat_length x n)
  | _ => constr:(@eq_refl nat (length bs))
  end.
(* [comment removed for export] *)
Local Ltac stn_rel e :=
  lazymatch e with
  | bv_unsigned ?w => constr:(stn_rel0 (bv_unsigned w))
  | (?x + ?k)%Z => let chk := ltac:(is_Z_lit k) in let p := stn_rel x in constr:(stn_rel_add _ _ _ k p)
  | (?x - ?k)%Z => let chk := ltac:(is_Z_lit k) in let p := stn_rel x in constr:(stn_rel_sub _ _ _ k p)
  | _ => let chk := ltac:(is_var e) in constr:(stn_rel0 e)
  end.
(* [comment removed for export] *)
Local Ltac stn_with_lohi u k :=
  match goal with
  | Hl : (?lo <= u)%Z, Hh : (u <= ?hi)%Z |- _ =>
      let chk := ltac:(check_closed_term lo; check_closed_term hi) in k lo hi Hl Hh
  end.
Local Ltac stn_with_lo w k :=
  match goal with
  | H : (?lo <= bv_unsigned w)%Z |- _ => is_Z_lit lo; k lo 0%Z constr:(stn_lo0 (bv_unsigned w) lo H)
  | H : (?lo <= bv_unsigned w - ?d)%Z |- _ => is_Z_lit lo; is_Z_lit d; k lo d H
  end.
Local Ltac stn_cheap_peel :=
  lazymatch goal with
  | |- rdn ?segs (wbytes ?m (Z_to_bv 64 ?zb) ?bs) (Z_to_bv 64 ?za) ?n = _ =>
      let L := stn_len bs in
      first
      [ (* [comment removed for export] *)
        is_Z_lit za; is_Z_lit zb; rewrite (stn_peel_ll segs bs m za zb n _ L (@eq_refl bool true))
      | (* [comment removed for export] *)
        let pa := stn_rel za in let pb := stn_rel zb in
        lazymatch type of pa with _ = (bv_unsigned ?w + _)%Z =>
          stn_with_lo w ltac:(fun lo d H => rewrite (stn_peel_rr segs bs m w za zb _ _ lo d n _ pa pb H L (@eq_refl bool true))) end
      | (* [comment removed for export] *)
        is_Z_lit za; let pb := stn_rel zb in
        lazymatch type of pb with _ = (bv_unsigned ?w + _)%Z =>
          stn_with_lo w ltac:(fun lo d H => rewrite (stn_peel_lr segs bs m w za zb _ lo d n _ pb H L (@eq_refl bool true))) end
      | (* [comment removed for export] *)
        is_Z_lit zb; let pa := stn_rel za in
        lazymatch type of pa with _ = (bv_unsigned ?w + _)%Z =>
          stn_with_lo w ltac:(fun lo d H => rewrite (stn_peel_rl segs bs m w za zb _ lo d n _ pa H L (@eq_refl bool true))) end
      | (* [comment removed for export] *)
        let pa := stn_rel za in let pb := stn_rel zb in
        lazymatch type of pa with _ = (?u + _)%Z =>
          stn_with_lohi u ltac:(fun lo hi Hl Hh => rewrite (stn_peel_rrz segs bs m u za zb _ _ lo hi n _ pa pb Hl Hh L (@eq_refl bool true))) end
      | is_Z_lit za; let pb := stn_rel zb in
        lazymatch type of pb with _ = (?u + _)%Z =>
          stn_with_lohi u ltac:(fun lo hi Hl Hh => rewrite (stn_peel_lrz segs bs m u za zb _ lo hi n _ pb Hl Hh L (@eq_refl bool true))) end
      | is_Z_lit zb; let pa := stn_rel za in
        lazymatch type of pa with _ = (?u + _)%Z =>
          stn_with_lohi u ltac:(fun lo hi Hl Hh => rewrite (stn_peel_rlz segs bs m u za zb _ lo hi n _ pa Hl Hh L (@eq_refl bool true))) end ]
  end.
Local Ltac stn_name_rdn :=
  repeat (lazymatch goal with |- rdn _ ?M _ _ = _ =>
    lazymatch M with wbytes ?m' _ _ => lazymatch m' with wbytes _ _ _ => idtac end end;
    let t := stn_innermost M in let x := fresh "MN" in set (x := t) end).
Local Close Scope Z_scope.
Local Ltac stn_demand1 :=
  match goal with
  | M : stn_mark ?E |- context [getr ?x _] => lazymatch type of E with x = _ => rewrite E end
  | H : getr ?b ?x = _ |- context [getr ?b ?x] => is_var b; (let body := eval unfold b in b in idtac); rewrite !H
  | |- context [getr ?b ?x] =>
      is_var b;
      let body := eval unfold b in b in
      lazymatch body with regupd _ _ _ => idtac end;
      let l := gresl_list body in
      let bb := gresl_base body in
      let v := gresl_val body x in
      let H := fresh "HGN" in
      assert (H : getr b x = v) by (exact (getr_regupds l bb x (@eq_refl bool false)));
      rewrite !H
  end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef.pin ::=
  repeat first [ match goal with H : getr ?rs ?r = _ |- context [getr ?rs ?r] => rewrite !H end | stn_demand1 ].
(* [comment removed for export] *)
Local Ltac stn_final :=
  try (lazymatch goal with |- _ (mkst ?X _ _ _) =>
         lazymatch X with regupd _ _ _ =>
           let l := gresl_list X in let b := gresl_base X in
           let H := fresh "GRF" in pose proof (getr_regupds l b) as H end end).
Local Ltac stn_final_use :=
  lazymatch goal with |- getr ?X ?r = _ =>
    lazymatch X with regupd _ _ _ =>
      match goal with GRF : (forall r0 : reg, bv_eqb r0 0 = false -> getr (regupds _ _) r0 = _) |- _ => exact (GRF r (@eq_refl bool false)) end end end.
Local Ltac stn_gres_old :=
  repeat match goal with
         | |- context [getr ?X ?r] =>
             lazymatch X with regupd _ _ _ => idtac end;
             let l := gresl_list X in
             let b := gresl_base X in
             let v := gresl_val X r in
             let p := constr:(getr_regupds l b r (@eq_refl bool false) : getr X r = v) in
             rewrite p
         end;
  match goal with |- context [getr _ 0] => rewrite ?getr_zero | _ => idtac end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac.gres ::= first [ stn_final_use | stn_gres_old; repeat (stn_demand1; stn_gres_old) ].
Local Ltac stn_sok_old :=
  lazymatch goal with
  | |- store_ok ?segs ?M ?a ?n = true =>
      let b := sokl_base M in
      lazymatch b with
      | M => idtac
      | _ => let l := sokl_list M in
             refine ((store_ok_layers segs n l b a _) : store_ok segs M a n = true)
      end
  | |- _ => idtac
  end.
Local Ltac stn_sok_named :=
  lazymatch goal with |- store_ok ?segs ?M ?a ?n = true =>
    is_var M; match goal with H : mem_grows ?b M |- _ => apply (store_ok_mono segs n b M a H) end end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk.store_ok_peel ::= stn_sok_old; try stn_sok_named.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef.peel ::=
  repeat first [ stn_cheap_peel
               | rewrite rdn_wbytes_out_Z by (len_simpl; lia)
               | rewrite rdn_wbytes_out by region_side
               | lazymatch goal with |- rdn _ ?m _ _ = _ => is_var m; unfold m end ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef.ok_win HJ ::=
  apply store_ok_cmem_win;
  [ first [ assumption
          | repeat first [ apply wfJ_wbytes | lazymatch goal with |- wfJ _ ?j => is_var j; unfold j end ]; first [ exact HJ | assumption ] ]
  | region_side | region_side ].
Local Ltac stn_in_list := cbn [In]; repeat first [ left; reflexivity | right ].
Local Ltac stn_incl_list :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr; repeat (destruct Hr as [<-|Hr]; [stn_in_list|]); destruct Hr.
Local Ltac stn_regs_agree_weaken Hag := eapply regs_agree_mono; [| exact Hag]; stn_incl_list.
Local Ltac stn_ra_old :=
  first [ apply regs_agree_refl
        | apply regs_agree_upd; [ stn_in_list | ]; stn_ra_old
        | match goal with
          | Hag : regs_agree _ _ ?r |- regs_agree _ _ ?r =>
              eapply regs_agree_trans; [ | stn_regs_agree_weaken Hag ]; stn_ra_old
          end ].
Local Ltac stn_ra_chain :=
  first [ apply regs_agree_refl
        | lazymatch goal with |- regs_agree (fun r => In r ?Cl) _ ?X =>
            lazymatch X with regupd _ _ _ => idtac end;
            let bb := gresl_base X in let l := gresl_list X in
            eapply regs_agree_trans; [ | exact (stn_regs_agree_regupds Cl l bb (@eq_refl bool true)) ]; stn_ra_chain end
        | match goal with
          | Hag : regs_agree _ _ ?r |- regs_agree _ _ ?r =>
              eapply regs_agree_trans; [ | stn_regs_agree_weaken Hag ]; stn_ra_chain
          end ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef.ra_chain ::= first [ solve [ stn_ra_chain ] | stn_ra_old ].

Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef.solve_regs_agree ::=
  first [ solve [ stn_ra_chain ] | repeat (apply regs_agree_upd; [ stn_in_list | ]); apply regs_agree_refl ].
(* [comment removed for export] *)
Section P3.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.           (* [comment removed for export] *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation mem0 := (wrap_mem RPH sp0 av ev uid hw rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).
  Local Notation stk := (stack_to_mem sp0 (entry_stack_image RPH sp0 av ev uid hw rdraw)) (only parsing).
  (* [comment removed for export] *)
  Local Notation E := (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))%Z (only parsing).
  Local Notation A := (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))%Z (only parsing).

  Local Notation pn := (cat_argv_ptr sp0 av ev 0) (only parsing).
  Local Notation rnd := (at_random_ptr sp0 av ev) (only parsing).
  Local Notation s := (nth 0 av []) (only parsing).
  Local Notation A8 := (Z_to_bv 64 0x623d8) (only parsing).

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
  Lemma len_ev : (Z.of_nat (length ev) <= 256)%Z.
  Proof. destruct Hve as [H1 _]. lia. Qed.

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma rd_above : forall J D (a : Z) n bs,
    (bv_unsigned sp0 <= a)%Z -> (a + Z.of_nat n < 2^64)%Z ->
    rdn SEGS stk (Z_to_bv 64 a) n = Some bs ->
    rdn SEGS (CM J D) (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros J D a n bs Ha Hn H. pose proof (u64_range (Z_to_bv 64 a)).
    rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). exact H.
  Qed.

  Lemma rd_envp : forall J D k, (k < length ev)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (E + 8 * Z.of_nat k)) 8
    = Some (word_to_le_bytes 8 (cat_envp_ptr sp0 av ev k)).
  Proof.
    intros J D k Hk. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (E + 8 * Z.of_nat k)) with (sp0 + nat_to_word (envp_off av + 8 * k))
      by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
    exact (read_envp_ptr_k SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_hi' k Hk).
  Qed.

  Lemma rd_envp_null : forall J D,
    rdn SEGS (CM J D) (Z_to_bv 64 (E + 8 * Z.of_nat (length ev))) 8
    = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Proof.
    intros J D. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (E + 8 * Z.of_nat (length ev)))
      with (sp0 + nat_to_word (envp_off av + 8 * length ev))
      by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
    exact (read_envp_null SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_hi').
  Qed.

  Lemma rd_auxv : forall J D j w, (j < 20)%nat ->
    nth j (auxv_words RPH rnd uid hw) (Z_to_bv 64 0) = w ->
    rdn SEGS (CM J D) (Z_to_bv 64 (A + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 w).
  Proof.
    intros J D j w Hj Hw. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (A + 8 * Z.of_nat j)) with (sp0 + nat_to_word (auxv_off av ev + 8 * j))
      by (rewrite word_add_nat; f_equal; unfold auxv_off; lia).
    rewrite <- Hw. exact (read_auxv_word SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_hi' j Hj).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma envp_loop : forall G, bwd SEGS G -> forall n k regs J D rom,
    (k + n = length ev)%nat ->
    getr regs 9 = Z_to_bv 64 (E + 8 * Z.of_nat k) ->
    (forall regs',
        getr regs' 9 = Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8) ->
        getr regs' 10 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [9; 10]%list) regs regs' ->
        G (mkst regs' (0x22104 : word) (CM J D) rom)) ->
    G (mkst regs (0x220f8 : word) (CM J D) rom).
  Proof.
    intros G HG.
    pose proof len_av as Hlen. pose proof len_ev as Hlev.
    induction n as [|n IH]; intros k regs J D rom Hkn H9 Hk0.
    - (* [comment removed for export] *)
      assert (k = length ev) by lia. subst k.
      eapply HG.
      { ld_step F_220f8 D_220f8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
          ltac:(apply rd_envp_null) ltac:(apply bytes_le_to_Z_8). renm.
        sv F_220fc D_220fc (Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8)). renm.
        stepb_ft F_22100 D_22100 ltac:(pin; cond_compute). renm.
        stn_done. apply mst_refl. }
      apply Hk0; [gres; reflexivity | gres; reflexivity | solve_regs_agree].
    - assert (Hk : (k < length ev)%nat) by lia.
      pose proof (cat_envp_ptr_nz RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' k Hk) as Hnz.
      eapply HG.
      { ld_step F_220f8 D_220f8 (word_to_le_bytes 8 (cat_envp_ptr sp0 av ev k)) (cat_envp_ptr sp0 av ev k)
          ltac:(apply rd_envp; exact Hk) ltac:(apply bytes_le_to_Z_8). renm.
        sv F_220fc D_220fc (Z_to_bv 64 (E + 8 * Z.of_nat (S k))). renm.
        stepb_tk F_22100 D_22100 ltac:(pin; apply c_eq_0_false; exact Hnz). renm.
        stn_done. apply mst_refl. }
      eapply (IH (S k)); [lia | gres; reflexivity |].
      intros regs' H9' H10' Hag. apply Hk0; [exact H9' | exact H10' |].
      eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pn_bounds :
    (bv_unsigned sp0 <= bv_unsigned pn)%Z
    /\ (bv_unsigned pn + Z.of_nat (length s) + 1 < 2^64)%Z.
  Proof.
    pose proof len_av.
    exact (argv_ptr_bounds_at sp0 av ev Hva Hve Hsp_hi' 0 ltac:(lia)).
  Qed.

  Lemma rd_argv0_byte : forall J D j b, (j <= length s)%nat ->
    nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = b ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) 1 = Some [b].
  Proof.
    intros J D j b Hj Hb. pose proof len_av. pose proof pn_bounds as [Hp1 Hp2].
    apply rd_above; [lia | lia |].
    stn_open. replace (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) with (pn + nat_to_word j)
      by (rewrite word_add_nat; reflexivity).
    stn_open. rewrite <- Hb.
    exact (read_argv_byte_k RPH SEGS sp0 av ev 0 j uid hw rdraw ltac:(lia) Hj
             (bsb_nw RPH sp0 av ev uid hw rdraw Hva Hve Hsp_hi')).
  Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof. intros; subst; reflexivity. Qed.

  Lemma c_eq_byte47 : forall b : byte,
    c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 47) = bv_eqb b (Z_to_bv 8 47).
  Proof.
    intros b. pose proof (u8_range b). stn_open. unfold c_eq, bv_eqb.
    stn_open. rewrite !u_Z2bv by lia. reflexivity.
  Qed.

  Lemma c_eq_byte0 : forall b : byte, b <> Z_to_bv 8 0 ->
    c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 0) = false.
  Proof.
    intros b Hb. pose proof (u8_range b). apply c_eq_0_false. stn_open. rewrite u_Z2bv by lia.
    intro Hz. apply Hb. apply bv_eq. stn_open. rewrite Hz. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma prog_loop : forall G, bwd SEGS G -> forall l2 j acc regs J D rom,
    skipn j s = l2 -> (j <= length s)%nat -> (acc <= j)%nat ->
    getr regs 10 = Z_to_bv 64 0x623d8 ->
    getr regs 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1) ->
    getr regs 12 = Z_to_bv 64 47 ->
    (forall regs',
        getr regs' 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat (length s) + 1) ->
        regs_agree (fun r => In r [11; 13]%list) regs regs' ->
        G (mkst regs' (0x221c8 : word)
                       (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn
                                 + Z.of_nat (after_last_slash l2 j acc)))))) rom)) ->
    G (mkst regs (0x221bc : word)
                   (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat acc))))) rom).
  Proof.
    intros G HG.
    pose proof len_av as Hlen. pose proof pn_bounds as [Hp1 Hp2].
    pose proof (valid_argv_str_nz av 0 Hva ltac:(lia)) as Hnz.
    induction l2 as [|b l2 IH]; intros j acc regs J D rom Hskip Hj Hacc H10 H11 H12 Hk0.
    - (* [comment removed for export] *)
      assert (Hjl : j = length s).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      eapply HG.
      { lb_step F_221bc D_221bc (Z_to_bv 8 0)
          ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | subst j; rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity] | f_equal; lia]). renm.
        stepb_ft F_221c0 D_221c0 ltac:(pin; cond_compute). renm.
        stepb_ft F_221c4 D_221c4 ltac:(pin; cond_compute). renm.
        stn_done. apply mst_refl. }
      apply Hk0; [gres; pin; f_equal; lia | solve_regs_agree].
    - assert (Hjlt : (j < length s)%nat).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      assert (Hb : nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = b).
      { stn_open. rewrite app_nth1 by lia. stn_open. rewrite <- (Nat.add_0_r j), <- nth_skipn, Hskip. reflexivity. }
      assert (Hbnz : b <> Z_to_bv 8 0).
      { intros Hb0. apply Hnz. stn_open. rewrite <- Hb0, <- Hb, app_nth1 by lia. apply nth_In. lia. }
      assert (Hskip' : skipn (S j) s = l2).
      { stn_open. replace (S j) with (1 + j)%nat by lia. stn_open. rewrite <- skipn_skipn, Hskip. reflexivity. }
      cbn [after_last_slash] in Hk0.
      destruct (bv_eqb b (Z_to_bv 8 47)) eqn:Eb.
      + (* [comment removed for export] *)
        eapply HG.
        { lb_step F_221bc D_221bc b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]). renm.
          stepb_tk F_221c0 D_221c0 ltac:(pin; rewrite c_eq_byte47; exact Eb). renm.
          stw F_221b4 D_221b4 (Z_to_bv 64 0x623d8) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1)) ltac:(ok_data). renm.
          stn_open. rewrite wbytes_shadow by (rewrite ?length_N_to_le_bytes; rewrite ?length_N_to_le_bytes; first [reflexivity | region_side]).
          sv F_221b8 D_221b8 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)). renm.
          stn_done. apply mst_refl. }
        stn_open. replace (bv_unsigned pn + Z.of_nat j + 1)%Z with (bv_unsigned pn + Z.of_nat (S j))%Z by lia.
        eapply (IH (S j) (S j)); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
      + eapply HG.
        { lb_step F_221bc D_221bc b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]). renm.
          stepb_ft F_221c0 D_221c0 ltac:(pin; rewrite c_eq_byte47; exact Eb). renm.
          stepb_tk F_221c4 D_221c4 ltac:(pin; apply c_eq_byte0; exact Hbnz). renm.
          sv F_221b8 D_221b8 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)). renm.
          stn_done. apply mst_refl. }
        eapply (IH (S j) acc); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac rdA j w := eapply rdn_addr; [apply (rd_auxv _ _ j w); [lia | reflexivity] | f_equal; lia].

  Lemma p3_run : forall G, bwd SEGS G -> forall regs Jf rom,
    wfJ sp0 Jf ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 8 = pn ->
    getr regs 9 = envp_w sp0 av ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
    (forall regs',
        getr regs' 1 = Z_to_bv 64 0x221d0 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
        getr regs' 18 = Z_to_bv 64 0x623e8 ->
        regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 18]%list) regs regs' ->
        G (mkst regs' (0x223e0 : word) (CM (J_aux sp0 av ev uid hw Jf) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0x220ec : word)
         (CM (wbytes Jf (Z_to_bv 64 (bv_unsigned sp0 - 368)) (zeros 304)) (fun _ => None)) rom).
  Proof.
    intros G HG regs Jf rom HJ H2 H8 H9 H10 Hk.
    pose proof len_av as Hlen. pose proof len_ev as Hlev. pose proof pn_bounds as [Hp1 Hp2].
    unfold envp_w in H9.
    eapply HG.
    { sn F_220ec D_220ec. renm.   (* [comment removed for export] *)
    ld_step F_220f0 D_220f0 (word_to_le_bytes 8 (Z_to_bv 64 0x42088)) (Z_to_bv 64 0x42088)
      ltac:(rd_img img_30400_8) ltac:(apply bytes_le_to_Z_8). renm.
    stw F_220f4 D_220f4 (Z_to_bv 64 0x42088) (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ltac:(ok_data). renm.
      stn_done. apply mst_refl. }
    (* [comment removed for export] *)
    eapply (envp_loop G HG (length ev) 0); [lia | gres; pin; f_equal; lia |].
    intros regs1 H9a H10a Hag1.
    carry Hag1 H2 (2 : reg) H2a. carry Hag1 H8 (8 : reg) H8a.
    clear H9 H10 H8 H2.
    eapply HG.
    { sn F_22104 D_22104. renm.   (* [comment removed for export] *)
    sn F_22108 D_22108. renm.   (* [comment removed for export] *)
    stw F_2210c D_2210c (Z_to_bv 64 0x623f0)
      (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))) ltac:(ok_data). renm.
    (* [comment removed for export] *)
    ld_step F_22110 D_22110 (word_to_le_bytes 8 (Z_to_bv 64 3)) (Z_to_bv 64 3) ltac:(rdA 0%nat (Z_to_bv 64 3)) ltac:(apply bytes_le_to_Z_8). renm.
    stepb_ft F_22114 D_22114 ltac:(pin; cond_compute). renm.
    sv F_22118 D_22118 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 16)). renm.
    sn F_2211c D_2211c. renm.   (* [comment removed for export] *)
    sv F_22120 D_22120 (Z_to_bv 64 (bv_unsigned sp0 - 368)). renm.  (* [comment removed for export] *)
    sn F_22124 D_22124. renm.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_22134 D_22134 ltac:(pin; cond_compute). renm.   (* [comment removed for export] *)
    ld_step F_22138 D_22138 (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040) ltac:(rdA 1%nat (Z_to_bv 64 0x10040)) ltac:(apply bytes_le_to_Z_8). renm.
    sn F_2213c D_2213c. renm.   (* [comment removed for export] *)
    sv F_22140 D_22140 (Z_to_bv 64 (bv_unsigned sp0 - 344)). renm.   (* [comment removed for export] *)
    stw F_22144 D_22144 (Z_to_bv 64 (bv_unsigned sp0 - 344)) (Z_to_bv 64 0x10040) ltac:(ok_win HJ). renm.
    sn F_22148 D_22148. renm.   (* [comment removed for export] *)
    ld_step F_22128 D_22128 (word_to_le_bytes 8 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rdA 2%nat (Z_to_bv 64 4)) ltac:(apply bytes_le_to_Z_8). renm.
    sv F_2212c D_2212c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 32)). renm.
    stepb_ft F_22130 D_22130 ltac:(pin; cond_compute). renm.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_22134 D_22134 ltac:(pin; cond_compute). renm.   (* [comment removed for export] *)
    ld_step F_22138 D_22138 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rdA 3%nat (Z_to_bv 64 56)) ltac:(apply bytes_le_to_Z_8). renm.
    sn F_2213c D_2213c. renm.   (* [comment removed for export] *)
    sv F_22140 D_22140 (Z_to_bv 64 (bv_unsigned sp0 - 336)). renm.   (* [comment removed for export] *)
    stw F_22144 D_22144 (Z_to_bv 64 (bv_unsigned sp0 - 336)) (Z_to_bv 64 56) ltac:(ok_win HJ). renm.
    sn F_22148 D_22148. renm.   (* [comment removed for export] *)
    ld_step F_22128 D_22128 (word_to_le_bytes 8 (Z_to_bv 64 5)) (Z_to_bv 64 5) ltac:(rdA 4%nat (Z_to_bv 64 5)) ltac:(apply bytes_le_to_Z_8). renm.
    sv F_2212c D_2212c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 48)). renm.
    stepb_ft F_22130 D_22130 ltac:(pin; cond_compute). renm.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_22134 D_22134 ltac:(pin; cond_compute). renm.   (* [comment removed for export] *)
    ld_step F_22138 D_22138 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rdA 5%nat (Z_to_bv 64 10)) ltac:(apply bytes_le_to_Z_8). renm.
    sn F_2213c D_2213c. renm.   (* [comment removed for export] *)
    sv F_22140 D_22140 (Z_to_bv 64 (bv_unsigned sp0 - 328)). renm.   (* [comment removed for export] *)
    stw F_22144 D_22144 (Z_to_bv 64 (bv_unsigned sp0 - 328)) (Z_to_bv 64 10) ltac:(ok_win HJ). renm.
    sn F_22148 D_22148. renm.   (* [comment removed for export] *)
    ld_step F_22128 D_22128 (word_to_le_bytes 8 (Z_to_bv 64 16)) (Z_to_bv 64 16) ltac:(rdA 6%nat (Z_to_bv 64 16)) ltac:(apply bytes_le_to_Z_8). renm.
    sv F_2212c D_2212c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 64)). renm.
    stepb_ft F_22130 D_22130 ltac:(pin; cond_compute). renm.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_22134 D_22134 ltac:(pin; cond_compute). renm.   (* [comment removed for export] *)
    ld_step F_22138 D_22138 (word_to_le_bytes 8 hw) hw ltac:(rdA 7%nat hw) ltac:(apply bytes_le_to_Z_8). renm.
    sn F_2213c D_2213c. renm.   (* [comment removed for export] *)
    sv F_22140 D_22140 (Z_to_bv 64 (bv_unsigned sp0 - 240)). renm.   (* [comment removed for export] *)
    stw F_22144 D_22144 (Z_to_bv 64 (bv_unsigned sp0 - 240)) hw ltac:(ok_win HJ). renm.
    sn F_22148 D_22148. renm.   (* [comment removed for export] *)
    ld_step F_22128 D_22128 (word_to_le_bytes 8 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rdA 8%nat (Z_to_bv 64 6)) ltac:(apply bytes_le_to_Z_8). renm.
    sv F_2212c D_2212c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 80)). renm.
    stepb_ft F_22130 D_22130 ltac:(pin; cond_compute). renm.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_22134 D_22134 ltac:(pin; cond_compute). renm.   (* [comment removed for export] *)
    ld_step F_22138 D_22138 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096) ltac:(rdA 9%nat (Z_to_bv 64 4096)) ltac:(apply bytes_le_to_Z_8). renm.
    sn F_2213c D_2213c. renm.   (* [comment removed for export] *)
    sv F_22140 D_22140 (Z_to_bv 64 (bv_unsigned sp0 - 320)). renm.   (* [comment removed for export] *)
    stw F_22144 D_22144 (Z_to_bv 64 (bv_unsigned sp0 - 320)) (Z_to_bv 64 4096) ltac:(ok_win HJ). renm.
    sn F_22148 D_22148. renm.   (* [comment removed for export] *)
    ld_step F_22128 D_22128 (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rdA 10%nat (Z_to_bv 64 11)) ltac:(apply bytes_le_to_Z_8). renm.
    sv F_2212c D_2212c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 96)). renm.
    stepb_ft F_22130 D_22130 ltac:(pin; cond_compute). renm.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_22134 D_22134 ltac:(pin; cond_compute). renm.   (* [comment removed for export] *)
    ld_step F_22138 D_22138 (word_to_le_bytes 8 uid) uid ltac:(rdA 11%nat uid) ltac:(apply bytes_le_to_Z_8). renm.
    sn F_2213c D_2213c. renm.   (* [comment removed for export] *)
    sv F_22140 D_22140 (Z_to_bv 64 (bv_unsigned sp0 - 280)). renm.   (* [comment removed for export] *)
    stw F_22144 D_22144 (Z_to_bv 64 (bv_unsigned sp0 - 280)) uid ltac:(ok_win HJ). renm.
    sn F_22148 D_22148. renm.   (* [comment removed for export] *)
    ld_step F_22128 D_22128 (word_to_le_bytes 8 (Z_to_bv 64 12)) (Z_to_bv 64 12) ltac:(rdA 12%nat (Z_to_bv 64 12)) ltac:(apply bytes_le_to_Z_8). renm.
    sv F_2212c D_2212c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 112)). renm.
    stepb_ft F_22130 D_22130 ltac:(pin; cond_compute). renm.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_22134 D_22134 ltac:(pin; cond_compute). renm.   (* [comment removed for export] *)
    ld_step F_22138 D_22138 (word_to_le_bytes 8 uid) uid ltac:(rdA 13%nat uid) ltac:(apply bytes_le_to_Z_8). renm.
    sn F_2213c D_2213c. renm.   (* [comment removed for export] *)
    sv F_22140 D_22140 (Z_to_bv 64 (bv_unsigned sp0 - 272)). renm.   (* [comment removed for export] *)
    stw F_22144 D_22144 (Z_to_bv 64 (bv_unsigned sp0 - 272)) uid ltac:(ok_win HJ). renm.
    sn F_22148 D_22148. renm.   (* [comment removed for export] *)
    ld_step F_22128 D_22128 (word_to_le_bytes 8 (Z_to_bv 64 23)) (Z_to_bv 64 23) ltac:(rdA 14%nat (Z_to_bv 64 23)) ltac:(apply bytes_le_to_Z_8). renm.
    sv F_2212c D_2212c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 128)). renm.
    stepb_ft F_22130 D_22130 ltac:(pin; cond_compute). renm.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_22134 D_22134 ltac:(pin; cond_compute). renm.   (* [comment removed for export] *)
    ld_step F_22138 D_22138 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 15%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8). renm.
    sn F_2213c D_2213c. renm.   (* [comment removed for export] *)
    sv F_22140 D_22140 (Z_to_bv 64 (bv_unsigned sp0 - 184)). renm.   (* [comment removed for export] *)
    stw F_22144 D_22144 (Z_to_bv 64 (bv_unsigned sp0 - 184)) (Z_to_bv 64 0) ltac:(ok_win HJ). renm.
    sn F_22148 D_22148. renm.   (* [comment removed for export] *)
    ld_step F_22128 D_22128 (word_to_le_bytes 8 (Z_to_bv 64 25)) (Z_to_bv 64 25) ltac:(rdA 16%nat (Z_to_bv 64 25)) ltac:(apply bytes_le_to_Z_8). renm.
    sv F_2212c D_2212c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 144)). renm.
    stepb_ft F_22130 D_22130 ltac:(pin; cond_compute). renm.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_22134 D_22134 ltac:(pin; cond_compute). renm.   (* [comment removed for export] *)
    ld_step F_22138 D_22138 (word_to_le_bytes 8 (at_random_ptr sp0 av ev)) (at_random_ptr sp0 av ev) ltac:(rdA 17%nat (at_random_ptr sp0 av ev)) ltac:(apply bytes_le_to_Z_8). renm.
    sn F_2213c D_2213c. renm.   (* [comment removed for export] *)
    sv F_22140 D_22140 (Z_to_bv 64 (bv_unsigned sp0 - 168)). renm.   (* [comment removed for export] *)
    stw F_22144 D_22144 (Z_to_bv 64 (bv_unsigned sp0 - 168)) (at_random_ptr sp0 av ev) ltac:(ok_win HJ). renm.
    sn F_22148 D_22148. renm.   (* [comment removed for export] *)
    ld_step F_22128 D_22128 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 18%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8). renm.
    sv F_2212c D_2212c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 160)). renm.
    stepb_tk F_22130 D_22130 ltac:(pin; cond_compute). renm.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    ld_step F_2214c D_2214c (word_to_le_bytes 8 hw) hw
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.
    ld_step F_22150 D_22150 (zeros 8) (Z_to_bv 64 0)
      ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)
      ltac:(reflexivity). renm.
    sn F_22154 D_22154. renm.   (* [comment removed for export] *)
    stw F_22158 D_22158 (Z_to_bv 64 0x62450) hw ltac:(ok_data). renm.
    stepb_tk F_2215c D_2215c ltac:(pin; cond_compute). renm.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    ld_step F_22174 D_22174 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.
    stw F_22178 D_22178 (Z_to_bv 64 0x62418) (Z_to_bv 64 4096) ltac:(ok_data). renm.
    stepb_tk F_2217c D_2217c ltac:(pin; apply c_eq_0_false; lia). renm.   (* [comment removed for export] *)
    stepb_tk F_22184 D_22184 ltac:(pin; apply c_eq_0_false; lia). renm.
    (* [comment removed for export] *)
    sn F_22190 D_22190. renm.
    ld_step F_22194 D_22194 (word_to_le_bytes 8 (Z_to_bv 64 0x623e0)) (Z_to_bv 64 0x623e0)
      ltac:(rd_img img_30408_8) ltac:(apply bytes_le_to_Z_8). renm.
    sn F_22198 D_22198. renm.
    ld_step F_2219c D_2219c (word_to_le_bytes 8 (Z_to_bv 64 0x623d8)) (Z_to_bv 64 0x623d8)
      ltac:(rd_img img_30410_8) ltac:(apply bytes_le_to_Z_8). renm.
    stw F_221a0 D_221a0 (Z_to_bv 64 0x623e0) (cat_argv_ptr sp0 av ev 0) ltac:(ok_data). renm.
    sv F_221a4 D_221a4 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0 + 1)). renm.   (* [comment removed for export] *)
    stw F_221a8 D_221a8 (Z_to_bv 64 0x623d8) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0)) ltac:(ok_data). renm.
    sn F_221ac D_221ac. renm.   (* [comment removed for export] *)
    sn F_221b0 D_221b0. renm.   (* [comment removed for export] *)
      stn_done. apply mst_refl. }
    (* [comment removed for export] *)
    eapply (prog_loop G HG s 0 0); [reflexivity | lia | lia | gres; reflexivity | gres; reflexivity | gres; reflexivity |].
    intros regs2 H11b Hag2.
    carry Hag2 H2a (2 : reg) H2b.
    eapply HG.
    { sv F_221c8 D_221c8 (Z_to_bv 64 (bv_unsigned sp0 - 368)). renm.   (* [comment removed for export] *)
      sn F_221cc D_221cc. renm.   (* [comment removed for export] *)
      stn_done. apply mst_refl. }
    stn_final. apply Hk.
    - gres; bveq.
    - gres; exact H2b.
    - gres; reflexivity.
    - gres. pose proof (Hag2 (18:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity.
    - ra_chain.
  Qed.

End P3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End D_St6k6.


(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition stn_mark {A : Type} (x : A) : Prop := True.
Definition stn_markm {A : Type} (x : A) : Prop := True.      (* [comment removed for export] *)
Lemma stn_ex_by_eq : forall (A : Type) (P : A -> Prop) (w : A), (forall x, x = w -> P x) -> exists x, P x.
Proof. intros A P w H. exists w. exact (H w eq_refl). Qed.
Lemma stn_msteps_tgt : forall segs st tgt, (forall stF, stF = tgt -> msteps segs st stF) -> msteps segs st tgt.
Proof. intros segs st tgt H. exact (H tgt eq_refl). Qed.
Lemma stn_regs_agree_regupds : forall (Cl : list reg) (l : list (reg * word)) base,
  forallb (fun p : reg * word => existsb (bv_eqb (fst p)) Cl) l = true ->
  regs_agree (fun r => In r Cl) base (regupds l base).
Proof.
  intros Cl l base. induction l as [|[r v] l IH]; cbn [regupds forallb]; intro H.
  - apply regs_agree_refl.
  - apply andb_prop in H. destruct H as [H1 H2]. apply regs_agree_upd; [| apply IH; exact H2].
    cbn [fst] in H1. apply existsb_exists in H1. destruct H1 as [x [Hx E]]. apply gresl_eq_of_eqb in E. subst x. exact Hx.
Qed.
Local Ltac stn_K := constr:(4%nat).
Local Ltac stn_depth R := lazymatch R with regupd ?R' _ _ => let d := stn_depth R' in constr:(S d) | _ => constr:(O) end.
Local Ltac stn_innermost m := lazymatch m with wbytes ?m' _ _ => lazymatch m' with wbytes _ _ _ => stn_innermost m' | _ => m end end.
Local Ltac stn_set t base :=
  let x := fresh base in set (x := t); pose proof (I : stn_mark x).
Local Ltac stn_grow_fact x :=
  let body := eval unfold x in x in
  lazymatch body with wbytes ?p ?a ?bs =>
    let H := fresh "HMG" in
    first [ match goal with Hp : mem_grows ?b0 p |- _ => assert (H : mem_grows b0 x) by (exact (mem_grows_trans b0 p x Hp (wbytes_grows bs p a))) end
          | assert (H : mem_grows p x) by (exact (wbytes_grows bs p a)) ]
  end.
Local Ltac stn_setm t base :=
  let x := fresh base in set (x := t); pose proof (I : stn_markm x); try stn_grow_fact x.
Local Ltac stn_name_regs R :=
  let d := stn_depth R in let k := stn_K in
  lazymatch eval cbv in (Nat.leb k d) with true => stn_set R ident:(RN) | false => idtac end.
Local Ltac stn_name_J :=
  repeat (lazymatch goal with |- msteps _ (mkst _ _ (cmem ?s _ ?J _) _) _ =>
    lazymatch J with wbytes _ _ _ => idtac end;
    let t := stn_innermost J in
    let j := fresh "JN" in set (j := t); pose proof (I : stn_markm j);
    try (let H := fresh "HJN" in assert (H : wfJ s j) by (unfold j; apply wfJ_wbytes; assumption)) end).
Local Ltac stn_name_D :=
  repeat (lazymatch goal with |- msteps _ (mkst _ _ (cmem _ _ _ ?D) _) _ =>
    lazymatch D with wbytes _ _ _ => idtac end;
    let t := stn_innermost D in (let x := fresh "DN" in set (x := t); pose proof (I : stn_markm x)) end).
Local Ltac stn_name_M :=
  repeat (lazymatch goal with |- msteps _ (mkst _ _ ?M _) _ =>
    lazymatch M with wbytes _ _ _ => idtac end;
    let t := stn_innermost M in stn_setm t ident:(MN) end).
(* [comment removed for export] *)
Local Ltac stn_eexists :=
  lazymatch goal with
  | |- @ex (bvmap _ _) _ => eapply stn_ex_by_eq; (let x := fresh "regsW" in let E := fresh "EregsW" in intros x E; pose proof (I : stn_mark E))
  | |- _ => eexists
  end.
Local Ltac stn_wit :=
  repeat match goal with
  | M : stn_mark ?E |- ?g => lazymatch type of E with ?x = _ => lazymatch g with context [x] => rewrite E end end
  end.
Local Ltac stn_begin :=
  lazymatch goal with
  | |- msteps _ _ ?t => tryif is_var t then idtac else (apply stn_msteps_tgt; let s := fresh "stF" in let E := fresh "EstF" in intros s E)
  | |- _ => idtac
  end.
Local Ltac renm :=
  stn_begin;
  lazymatch goal with
  | |- msteps _ (mkst ?R _ (cmem _ _ _ _) _) _ => stn_name_regs R; stn_name_J; stn_name_D
  | |- msteps _ (mkst ?R _ _ _) _ => stn_name_regs R; stn_name_M
  | |- _ => idtac
  end.
Local Ltac stn_open :=
  repeat match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end;
  try lazymatch goal with E : ?s = _ |- msteps _ _ ?s => rewrite E end.
Local Ltac stn_done :=
  repeat first [ match goal with H : stn_mark ?x |- ?g => lazymatch g with context [x] => unfold x end end
               | match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end ];
  try lazymatch goal with E : ?s = _ |- msteps _ _ ?s => rewrite E end;
  stn_wit.
(* [comment removed for export] *)
Local Open Scope Z_scope.
Definition stn_rr_ok (oa ob lo d n len : Z) : bool :=
  (0 <=? lo + d + oa) && (0 <=? lo + d + ob) && (0 <=? n) && (oa + n <=? 0) && (0 <=? len) && (ob + len <=? 0)
  && ((oa + n <=? ob) || (ob + len <=? oa)).
Definition stn_lr_ok (za ob lo d n len : Z) : bool :=
  (0 <=? lo + d + ob) && (0 <=? len) && (ob + len <=? 0) && (0 <=? za) && (0 <=? n) && (za + n <=? lo + d + ob).
Definition stn_rl_ok (oa zb lo d n len : Z) : bool :=
  (0 <=? lo + d + oa) && (0 <=? n) && (oa + n <=? 0) && (0 <=? zb) && (0 <=? len) && (zb + len <=? lo + d + oa).
Definition stn_ll_ok (za zb n len : Z) : bool :=
  (0 <=? za) && (0 <=? n) && (za + n <=? 2^64) && (0 <=? zb) && (0 <=? len) && (zb + len <=? 2^64) && (za <? 2^64) && (zb <? 2^64)
  && ((za + n <=? zb) || (zb + len <=? za)).
Lemma stn_lo0 : forall x lo : Z, lo <= x -> lo <= x - 0.
Proof. intros. lia. Qed.
Lemma stn_rel0 : forall u : Z, u = u + 0.
Proof. intros. lia. Qed.
Lemma stn_rel_add : forall x u o k : Z, x = u + o -> x + k = u + (o + k).
Proof. intros. lia. Qed.
Lemma stn_rel_sub : forall x u o k : Z, x = u + o -> x - k = u + (o - k).
Proof. intros. lia. Qed.
Lemma stn_peel_gen : forall segs bs m (za zb : Z) n,
  0 <= za < 2^64 -> za + Z.of_nat n <= 2^64 -> 0 <= zb < 2^64 -> zb + Z.of_nat (length bs) <= 2^64 ->
  (za + Z.of_nat n <= zb \/ zb + Z.of_nat (length bs) <= za) ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m za zb n Ha Han Hb Hbn Hd.
  apply rdn_wbytes_out; rewrite ?u_Z2bv by lia; lia.
Qed.
Local Ltac stn_bools Hok :=
  repeat (apply andb_prop in Hok; destruct Hok as [Hok ?]);
  repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end.
Lemma stn_peel_rr : forall segs bs m (w : word) (za zb oa ob lo d : Z) n len,
  za = bv_unsigned w + oa -> zb = bv_unsigned w + ob -> lo <= bv_unsigned w - d -> length bs = len ->
  stn_rr_ok oa ob lo d (Z.of_nat n) (Z.of_nat len) = true ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m w za zb oa ob lo d n len Ea Eb Hlo HL Hok. subst len. unfold stn_rr_ok in Hok. stn_bools Hok.
  pose proof (bv_unsigned_in_range 64 w) as R; unfold bv_modulus in R; change (2 ^ Z.of_N 64) with (2^64) in R.
  match goal with H : (_ || _)%bool = true |- _ => apply orb_prop in H; destruct H as [H|H]; apply Z.leb_le in H end;
  apply stn_peel_gen; lia.
Qed.
Lemma stn_peel_lr : forall segs bs m (w : word) (za zb ob lo d : Z) n len,
  zb = bv_unsigned w + ob -> lo <= bv_unsigned w - d -> length bs = len ->
  stn_lr_ok za ob lo d (Z.of_nat n) (Z.of_nat len) = true ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m w za zb ob lo d n len Eb Hlo HL Hok. subst len. unfold stn_lr_ok in Hok. stn_bools Hok.
  pose proof (bv_unsigned_in_range 64 w) as R; unfold bv_modulus in R; change (2 ^ Z.of_N 64) with (2^64) in R.
  apply stn_peel_gen; lia.
Qed.
Lemma stn_peel_rl : forall segs bs m (w : word) (za zb oa lo d : Z) n len,
  za = bv_unsigned w + oa -> lo <= bv_unsigned w - d -> length bs = len ->
  stn_rl_ok oa zb lo d (Z.of_nat n) (Z.of_nat len) = true ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m w za zb oa lo d n len Ea Hlo HL Hok. subst len. unfold stn_rl_ok in Hok. stn_bools Hok.
  pose proof (bv_unsigned_in_range 64 w) as R; unfold bv_modulus in R; change (2 ^ Z.of_N 64) with (2^64) in R.
  apply stn_peel_gen; lia.
Qed.
Lemma stn_peel_ll : forall segs bs m (za zb : Z) n len,
  length bs = len -> stn_ll_ok za zb (Z.of_nat n) (Z.of_nat len) = true ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m za zb n len HL Hok. subst len. unfold stn_ll_ok in Hok. stn_bools Hok.
  match goal with H : (_ || _)%bool = true |- _ => apply orb_prop in H; destruct H as [H|H]; apply Z.leb_le in H end;
  apply stn_peel_gen; lia.
Qed.

(* [comment removed for export] *)
Definition stn_rrz_ok (oa ob lo hi n len : Z) : bool :=
  (0 <=? lo + oa) && (0 <=? lo + ob) && (0 <=? n) && (hi + oa + n <=? 2^64) && (hi + oa <? 2^64) && (0 <=? len) && (hi + ob + len <=? 2^64) && (hi + ob <? 2^64)
  && ((oa + n <=? ob) || (ob + len <=? oa)).
Definition stn_lrz_ok (za ob lo hi n len : Z) : bool :=
  (0 <=? lo + ob) && (0 <=? len) && (hi + ob + len <=? 2^64) && (hi + ob <? 2^64) && (0 <=? za) && (0 <=? n) && (za + n <=? lo + ob).
Definition stn_rlz_ok (oa zb lo hi n len : Z) : bool :=
  (0 <=? lo + oa) && (0 <=? n) && (hi + oa + n <=? 2^64) && (hi + oa <? 2^64) && (0 <=? zb) && (0 <=? len) && (zb + len <=? lo + oa).
Lemma stn_peel_rrz : forall segs bs m (u za zb oa ob lo hi : Z) n len,
  za = u + oa -> zb = u + ob -> lo <= u -> u <= hi -> length bs = len ->
  stn_rrz_ok oa ob lo hi (Z.of_nat n) (Z.of_nat len) = true ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m u za zb oa ob lo hi n len Ea Eb Hlo Hhi HL Hok. subst len. unfold stn_rrz_ok in Hok. stn_bools Hok.
  match goal with H : (_ || _)%bool = true |- _ => apply orb_prop in H; destruct H as [H|H]; apply Z.leb_le in H end;
  apply stn_peel_gen; lia.
Qed.
Lemma stn_peel_lrz : forall segs bs m (u za zb ob lo hi : Z) n len,
  zb = u + ob -> lo <= u -> u <= hi -> length bs = len ->
  stn_lrz_ok za ob lo hi (Z.of_nat n) (Z.of_nat len) = true ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m u za zb ob lo hi n len Eb Hlo Hhi HL Hok. subst len. unfold stn_lrz_ok in Hok. stn_bools Hok.
  apply stn_peel_gen; lia.
Qed.
Lemma stn_peel_rlz : forall segs bs m (u za zb oa lo hi : Z) n len,
  za = u + oa -> lo <= u -> u <= hi -> length bs = len ->
  stn_rlz_ok oa zb lo hi (Z.of_nat n) (Z.of_nat len) = true ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m u za zb oa lo hi n len Ea Hlo Hhi HL Hok. subst len. unfold stn_rlz_ok in Hok. stn_bools Hok.
  apply stn_peel_gen; lia.
Qed.

Local Ltac stn_len bs :=
  lazymatch bs with
  | word_to_le_bytes ?n ?v => constr:(length_N_to_le_bytes n v)
  | zeros ?n => constr:(length_zeros n)
  | repeat ?x ?n => constr:(repeat_length x n)
  | _ => constr:(@eq_refl nat (length bs))
  end.
(* [comment removed for export] *)
Local Ltac stn_rel e :=
  lazymatch e with
  | bv_unsigned ?w => constr:(stn_rel0 (bv_unsigned w))
  | (?x + ?k)%Z => let chk := ltac:(is_Z_lit k) in let p := stn_rel x in constr:(stn_rel_add _ _ _ k p)
  | (?x - ?k)%Z => let chk := ltac:(is_Z_lit k) in let p := stn_rel x in constr:(stn_rel_sub _ _ _ k p)
  | _ => let chk := ltac:(is_var e) in constr:(stn_rel0 e)
  end.
(* [comment removed for export] *)
Local Ltac stn_with_lohi u k :=
  match goal with
  | Hl : (?lo <= u)%Z, Hh : (u <= ?hi)%Z |- _ =>
      let chk := ltac:(check_closed_term lo; check_closed_term hi) in k lo hi Hl Hh
  end.
Local Ltac stn_with_lo w k :=
  match goal with
  | H : (?lo <= bv_unsigned w)%Z |- _ => is_Z_lit lo; k lo 0%Z constr:(stn_lo0 (bv_unsigned w) lo H)
  | H : (?lo <= bv_unsigned w - ?d)%Z |- _ => is_Z_lit lo; is_Z_lit d; k lo d H
  end.
Local Ltac stn_cheap_peel :=
  lazymatch goal with
  | |- rdn ?segs (wbytes ?m (Z_to_bv 64 ?zb) ?bs) (Z_to_bv 64 ?za) ?n = _ =>
      let L := stn_len bs in
      first
      [ (* [comment removed for export] *)
        is_Z_lit za; is_Z_lit zb; rewrite (stn_peel_ll segs bs m za zb n _ L (@eq_refl bool true))
      | (* [comment removed for export] *)
        let pa := stn_rel za in let pb := stn_rel zb in
        lazymatch type of pa with _ = (bv_unsigned ?w + _)%Z =>
          stn_with_lo w ltac:(fun lo d H => rewrite (stn_peel_rr segs bs m w za zb _ _ lo d n _ pa pb H L (@eq_refl bool true))) end
      | (* [comment removed for export] *)
        is_Z_lit za; let pb := stn_rel zb in
        lazymatch type of pb with _ = (bv_unsigned ?w + _)%Z =>
          stn_with_lo w ltac:(fun lo d H => rewrite (stn_peel_lr segs bs m w za zb _ lo d n _ pb H L (@eq_refl bool true))) end
      | (* [comment removed for export] *)
        is_Z_lit zb; let pa := stn_rel za in
        lazymatch type of pa with _ = (bv_unsigned ?w + _)%Z =>
          stn_with_lo w ltac:(fun lo d H => rewrite (stn_peel_rl segs bs m w za zb _ lo d n _ pa H L (@eq_refl bool true))) end
      | (* [comment removed for export] *)
        let pa := stn_rel za in let pb := stn_rel zb in
        lazymatch type of pa with _ = (?u + _)%Z =>
          stn_with_lohi u ltac:(fun lo hi Hl Hh => rewrite (stn_peel_rrz segs bs m u za zb _ _ lo hi n _ pa pb Hl Hh L (@eq_refl bool true))) end
      | is_Z_lit za; let pb := stn_rel zb in
        lazymatch type of pb with _ = (?u + _)%Z =>
          stn_with_lohi u ltac:(fun lo hi Hl Hh => rewrite (stn_peel_lrz segs bs m u za zb _ lo hi n _ pb Hl Hh L (@eq_refl bool true))) end
      | is_Z_lit zb; let pa := stn_rel za in
        lazymatch type of pa with _ = (?u + _)%Z =>
          stn_with_lohi u ltac:(fun lo hi Hl Hh => rewrite (stn_peel_rlz segs bs m u za zb _ lo hi n _ pa Hl Hh L (@eq_refl bool true))) end ]
  end.
Local Ltac stn_name_rdn :=
  repeat (lazymatch goal with |- rdn _ ?M _ _ = _ =>
    lazymatch M with wbytes ?m' _ _ => lazymatch m' with wbytes _ _ _ => idtac end end;
    let t := stn_innermost M in let x := fresh "MN" in set (x := t) end).
Local Close Scope Z_scope.
Local Ltac stn_demand1 :=
  match goal with
  | M : stn_mark ?E |- context [getr ?x _] => lazymatch type of E with x = _ => rewrite E end
  | H : getr ?b ?x = _ |- context [getr ?b ?x] => is_var b; (let body := eval unfold b in b in idtac); rewrite !H
  | |- context [getr ?b ?x] =>
      is_var b;
      let body := eval unfold b in b in
      lazymatch body with regupd _ _ _ => idtac end;
      let l := gresl_list body in
      let bb := gresl_base body in
      let v := gresl_val body x in
      let H := fresh "HGN" in
      assert (H : getr b x = v) by (exact (getr_regupds l bb x (@eq_refl bool false)));
      rewrite !H
  end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef.pin ::=
  repeat first [ match goal with H : getr ?rs ?r = _ |- context [getr ?rs ?r] => rewrite !H end | stn_demand1 ].
(* [comment removed for export] *)
Local Ltac stn_final :=
  try (lazymatch goal with |- _ (mkst ?X _ _ _) =>
         lazymatch X with regupd _ _ _ =>
           let l := gresl_list X in let b := gresl_base X in
           let H := fresh "GRF" in pose proof (getr_regupds l b) as H end end).
Local Ltac stn_final_use :=
  lazymatch goal with |- getr ?X ?r = _ =>
    lazymatch X with regupd _ _ _ =>
      match goal with GRF : (forall r0 : reg, bv_eqb r0 0 = false -> getr (regupds _ _) r0 = _) |- _ => exact (GRF r (@eq_refl bool false)) end end end.
Local Ltac stn_gres_old :=
  repeat match goal with
         | |- context [getr ?X ?r] =>
             lazymatch X with regupd _ _ _ => idtac end;
             let l := gresl_list X in
             let b := gresl_base X in
             let v := gresl_val X r in
             let p := constr:(getr_regupds l b r (@eq_refl bool false) : getr X r = v) in
             rewrite p
         end;
  match goal with |- context [getr _ 0] => rewrite ?getr_zero | _ => idtac end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac.gres ::= first [ stn_final_use | stn_gres_old; repeat (stn_demand1; stn_gres_old) ].
Local Ltac stn_sok_old :=
  lazymatch goal with
  | |- store_ok ?segs ?M ?a ?n = true =>
      let b := sokl_base M in
      lazymatch b with
      | M => idtac
      | _ => let l := sokl_list M in
             refine ((store_ok_layers segs n l b a _) : store_ok segs M a n = true)
      end
  | |- _ => idtac
  end.
Local Ltac stn_sok_named :=
  lazymatch goal with |- store_ok ?segs ?M ?a ?n = true =>
    is_var M; match goal with H : mem_grows ?b M |- _ => apply (store_ok_mono segs n b M a H) end end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk.store_ok_peel ::= stn_sok_old; try stn_sok_named.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef.peel ::=
  repeat first [ stn_cheap_peel
               | rewrite rdn_wbytes_out_Z by (len_simpl; lia)
               | rewrite rdn_wbytes_out by region_side
               | lazymatch goal with |- rdn _ ?m _ _ = _ => is_var m; unfold m end ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef.ok_win HJ ::=
  apply store_ok_cmem_win;
  [ first [ assumption
          | repeat first [ apply wfJ_wbytes | lazymatch goal with |- wfJ _ ?j => is_var j; unfold j end ]; first [ exact HJ | assumption ] ]
  | region_side | region_side ].
Local Ltac stn_in_list := cbn [In]; repeat first [ left; reflexivity | right ].
Local Ltac stn_incl_list :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr; repeat (destruct Hr as [<-|Hr]; [stn_in_list|]); destruct Hr.
Local Ltac stn_regs_agree_weaken Hag := eapply regs_agree_mono; [| exact Hag]; stn_incl_list.
Local Ltac stn_ra_old :=
  first [ apply regs_agree_refl
        | apply regs_agree_upd; [ stn_in_list | ]; stn_ra_old
        | match goal with
          | Hag : regs_agree _ _ ?r |- regs_agree _ _ ?r =>
              eapply regs_agree_trans; [ | stn_regs_agree_weaken Hag ]; stn_ra_old
          end ].
Local Ltac stn_ra_chain :=
  first [ apply regs_agree_refl
        | lazymatch goal with |- regs_agree (fun r => In r ?Cl) _ ?X =>
            lazymatch X with regupd _ _ _ => idtac end;
            let bb := gresl_base X in let l := gresl_list X in
            eapply regs_agree_trans; [ | exact (stn_regs_agree_regupds Cl l bb (@eq_refl bool true)) ]; stn_ra_chain end
        | match goal with
          | Hag : regs_agree _ _ ?r |- regs_agree _ _ ?r =>
              eapply regs_agree_trans; [ | stn_regs_agree_weaken Hag ]; stn_ra_chain
          end ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef.ra_chain ::= first [ solve [ stn_ra_chain ] | stn_ra_old ].

Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef.solve_regs_agree ::=
  first [ solve [ stn_ra_chain ] | repeat (apply regs_agree_upd; [ stn_in_list | ]); apply regs_agree_refl ].
(* [comment removed for export] *)
Section P4.
  Variable sp0 : word.
  Variable Jb : word -> option byte.   (* [comment removed for export] *)
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.           (* [comment removed for export] *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

#[using="Hhi Hlo"] Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 139728 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = pn_w sp0 av ev ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 402408 ->
getr regs 19 = Z_to_bv 64 0 ->
getr regs 20 = Z_to_bv 64 0 ->
getr regs 21 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 9 = (Z_to_bv 64 402408) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 401760) ->
getr regs' 13 = (Z_to_bv 64 10) ->
getr regs' 15 = (Z_to_bv 64 65600) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 1685382481) ->
getr regs' 29 = (Z_to_bv 64 65600) ->
getr regs' 30 = (Z_to_bv 64 131072) ->
regs_agree (fun r => In r [2; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs' ->
G (mkst regs' (0x22468 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139728))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 402408))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x223e0 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_223e0 D_223e0 (Z_to_bv 64 (bv_unsigned sp0 - 480)). renm.
stw F_223e4 D_223e4 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 139728) ltac:(ok_win HJ). renm.
stw F_223e8 D_223e8 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ). renm.
stw F_223ec D_223ec (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ). renm.
stw F_223f0 D_223f0 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 402408) ltac:(ok_win HJ). renm.
stw F_223f4 D_223f4 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ). renm.
stw F_223f8 D_223f8 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ). renm.
stw F_223fc D_223fc (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ). renm.
ld_step F_22400 D_22400 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.
sn F_22404 D_22404. renm.
sn F_22408 D_22408. renm.
sn F_2240c D_2240c. renm.
sn F_22410 D_22410. renm.
stepb_ft F_22414 D_22414 ltac:(pin; cond_compute). renm.
sn F_22418 D_22418. renm.
sn F_2241c D_2241c. renm.
sn F_22420 D_22420. renm.
ld_step F_22424 D_22424 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.
ld_step F_22428 D_22428 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.
sn F_2242c D_2242c. renm.
sn F_22430 D_22430. renm.
ld_step F_22434 D_22434 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_31788_4) ltac:(vm_compute; reflexivity). renm.
ld_step F_22438 D_22438 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_30390_8) ltac:(apply bytes_le_to_Z_8). renm.
sn F_2243c D_2243c. renm.
sn F_22440 D_22440. renm.
sn F_22444 D_22444. renm.
sn F_22448 D_22448. renm.
sn F_2244c D_2244c. renm.
sn F_22450 D_22450. renm.
stn_done. apply mst_refl. }
stn_final. apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hlo"] Lemma tls_c2 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 402408 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 401760 ->
getr regs 13 = Z_to_bv 64 10 ->
getr regs 15 = Z_to_bv 64 65600 ->
getr regs 16 = Z_to_bv 64 6 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
getr regs 28 = Z_to_bv 64 1685382481 ->
getr regs 29 = Z_to_bv 64 65600 ->
getr regs 30 = Z_to_bv 64 131072 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 9 = (Z_to_bv 64 402408) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 401760) ->
getr regs' 13 = (Z_to_bv 64 5) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 1685382481) ->
getr regs' 29 = (Z_to_bv 64 65880) ->
getr regs' 30 = (Z_to_bv 64 131072) ->
regs_agree (fun r => In r [8; 12; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x22468 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139728))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 402408))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x22468 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139728))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 402408))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_22468 D_22468 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity). renm.
stepb_tk F_2246c D_2246c ltac:(pin; cond_compute). renm.
ld_step F_22454 D_22454 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8). renm.
sn F_22458 D_22458. renm.
sn F_2245c D_2245c. renm.
sn F_22460 D_22460. renm.
stepb_ft F_22464 D_22464 ltac:(pin; cond_compute). renm.
ld_step F_22468 D_22468 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity). renm.
stepb_ft F_2246c D_2246c ltac:(pin; cond_compute). renm.
stepb_tk F_22470 D_22470 ltac:(pin; cond_compute). renm.
sn F_22484 D_22484. renm.
stepb_ft F_22488 D_22488 ltac:(pin; cond_compute). renm.
sn F_2248c D_2248c. renm.
stepb_tk F_22490 D_22490 ltac:(pin; cond_compute). renm.
sn F_224b0 D_224b0. renm.
sn F_224b4 D_224b4. renm.
sn F_2245c D_2245c. renm.
sn F_22460 D_22460. renm.
stepb_ft F_22464 D_22464 ltac:(pin; cond_compute). renm.
ld_step F_22468 D_22468 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity). renm.
stepb_ft F_2246c D_2246c ltac:(pin; cond_compute). renm.
stepb_tk F_22470 D_22470 ltac:(pin; cond_compute). renm.
sn F_22484 D_22484. renm.
stepb_ft F_22488 D_22488 ltac:(pin; cond_compute). renm.
sn F_2248c D_2248c. renm.
stepb_tk F_22490 D_22490 ltac:(pin; cond_compute). renm.
sn F_224b0 D_224b0. renm.
sn F_224b4 D_224b4. renm.
sn F_2245c D_2245c. renm.
sn F_22460 D_22460. renm.
stepb_ft F_22464 D_22464 ltac:(pin; cond_compute). renm.
ld_step F_22468 D_22468 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity). renm.
stepb_ft F_2246c D_2246c ltac:(pin; cond_compute). renm.
stepb_tk F_22470 D_22470 ltac:(pin; cond_compute). renm.
sn F_22484 D_22484. renm.
stepb_ft F_22488 D_22488 ltac:(pin; cond_compute). renm.
sn F_2248c D_2248c. renm.
stepb_tk F_22490 D_22490 ltac:(pin; cond_compute). renm.
sn F_224b0 D_224b0. renm.
sn F_224b4 D_224b4. renm.
sn F_2245c D_2245c. renm.
sn F_22460 D_22460. renm.
stepb_ft F_22464 D_22464 ltac:(pin; cond_compute). renm.
ld_step F_22468 D_22468 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity). renm.
stepb_ft F_2246c D_2246c ltac:(pin; cond_compute). renm.
stepb_tk F_22470 D_22470 ltac:(pin; cond_compute). renm.
sn F_22484 D_22484. renm.
stepb_ft F_22488 D_22488 ltac:(pin; cond_compute). renm.
sn F_2248c D_2248c. renm.
stepb_tk F_22490 D_22490 ltac:(pin; cond_compute). renm.
sn F_224b0 D_224b0. renm.
sn F_224b4 D_224b4. renm.
sn F_2245c D_2245c. renm.
sn F_22460 D_22460. renm.
stepb_ft F_22464 D_22464 ltac:(pin; cond_compute). renm.
stn_done. apply mst_refl. }
stn_final. apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hlo"] Lemma tls_c3 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 402408 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 401760 ->
getr regs 13 = Z_to_bv 64 5 ->
getr regs 16 = Z_to_bv 64 6 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
getr regs 28 = Z_to_bv 64 1685382481 ->
getr regs 29 = Z_to_bv 64 65880 ->
getr regs 30 = Z_to_bv 64 131072 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 9 = (Z_to_bv 64 402408) ->
getr regs' 11 = (Z_to_bv 64 401760) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x224b8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139728))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 402408))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x22468 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139728))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 402408))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_22468 D_22468 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity). renm.
stepb_ft F_2246c D_2246c ltac:(pin; cond_compute). renm.
stepb_tk F_22470 D_22470 ltac:(pin; cond_compute). renm.
sn F_22484 D_22484. renm.
stepb_ft F_22488 D_22488 ltac:(pin; cond_compute). renm.
sn F_2248c D_2248c. renm.
stepb_tk F_22490 D_22490 ltac:(pin; cond_compute). renm.
sn F_224b0 D_224b0. renm.
sn F_224b4 D_224b4. renm.
sn F_2245c D_2245c. renm.
sn F_22460 D_22460. renm.
stepb_ft F_22464 D_22464 ltac:(pin; cond_compute). renm.
ld_step F_22468 D_22468 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity). renm.
stepb_ft F_2246c D_2246c ltac:(pin; cond_compute). renm.
stepb_tk F_22470 D_22470 ltac:(pin; cond_compute). renm.
sn F_22484 D_22484. renm.
stepb_ft F_22488 D_22488 ltac:(pin; cond_compute). renm.
sn F_2248c D_2248c. renm.
stepb_tk F_22490 D_22490 ltac:(pin; cond_compute). renm.
sn F_224b0 D_224b0. renm.
sn F_224b4 D_224b4. renm.
sn F_2245c D_2245c. renm.
sn F_22460 D_22460. renm.
stepb_ft F_22464 D_22464 ltac:(pin; cond_compute). renm.
ld_step F_22468 D_22468 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity). renm.
stepb_ft F_2246c D_2246c ltac:(pin; cond_compute). renm.
stepb_tk F_22470 D_22470 ltac:(pin; cond_compute). renm.
sn F_22484 D_22484. renm.
stepb_ft F_22488 D_22488 ltac:(pin; cond_compute). renm.
sn F_2248c D_2248c. renm.
stepb_ft F_22490 D_22490 ltac:(pin; cond_compute). renm.
ld_step F_22494 D_22494 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8). renm.
stepb_tk F_22498 D_22498 ltac:(pin; cond_compute). renm.
sn F_224b0 D_224b0. renm.
sn F_224b4 D_224b4. renm.
sn F_2245c D_2245c. renm.
sn F_22460 D_22460. renm.
stepb_ft F_22464 D_22464 ltac:(pin; cond_compute). renm.
ld_step F_22468 D_22468 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity). renm.
stepb_ft F_2246c D_2246c ltac:(pin; cond_compute). renm.
stepb_tk F_22470 D_22470 ltac:(pin; cond_compute). renm.
sn F_22484 D_22484. renm.
stepb_ft F_22488 D_22488 ltac:(pin; cond_compute). renm.
sn F_2248c D_2248c. renm.
stepb_tk F_22490 D_22490 ltac:(pin; cond_compute). renm.
sn F_224b0 D_224b0. renm.
sn F_224b4 D_224b4. renm.
sn F_2245c D_2245c. renm.
sn F_22460 D_22460. renm.
stepb_ft F_22464 D_22464 ltac:(pin; cond_compute). renm.
ld_step F_22468 D_22468 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity). renm.
stepb_ft F_2246c D_2246c ltac:(pin; cond_compute). renm.
stepb_tk F_22470 D_22470 ltac:(pin; cond_compute). renm.
sn F_22484 D_22484. renm.
stepb_ft F_22488 D_22488 ltac:(pin; cond_compute). renm.
sn F_2248c D_2248c. renm.
stepb_tk F_22490 D_22490 ltac:(pin; cond_compute). renm.
sn F_224b0 D_224b0. renm.
sn F_224b4 D_224b4. renm.
sn F_2245c D_2245c. renm.
sn F_22460 D_22460. renm.
stepb_tk F_22464 D_22464 ltac:(pin; cond_compute). renm.
stn_done. apply mst_refl. }
stn_final. apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hlo"] Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 402408 ->
getr regs 11 = Z_to_bv 64 401760 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 270680) ->
getr regs' 10 = (Z_to_bv 64 401760) ->
getr regs' 11 = (Z_to_bv 64 402464) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 270472) ->
getr regs' 14 = (Z_to_bv 64 0) ->
getr regs' 15 = (Z_to_bv 64 18446744073709280936) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 270480) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 270696) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0x2263c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139728))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 402408))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 401792) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401808) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401800) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 402432) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 402440) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 270696) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 270672) (word_to_le_bytes 8 (Z_to_bv 64 270696))) (Z_to_bv 64 270480) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 402408) ([Z_to_bv 8 1])) (Z_to_bv 64 270520) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x224b8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139728))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 402408))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk F_224b8 D_224b8 ltac:(pin; cond_compute). renm.
ld_step F_224f0 D_224f0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_62170_8) ltac:(apply bytes_le_to_Z_8). renm.
ld_step F_224f4 D_224f4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_62180_8) ltac:(apply bytes_le_to_Z_8). renm.
ld_step F_224f8 D_224f8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_62188_8) ltac:(apply bytes_le_to_Z_8). renm.
sn F_224fc D_224fc. renm.
sn F_22500 D_22500. renm.
sn F_22504 D_22504. renm.
sn F_22508 D_22508. renm.
sn F_2250c D_2250c. renm.
sn F_22510 D_22510. renm.
sn F_22514 D_22514. renm.
stw F_22518 D_22518 (Z_to_bv 64 401792) (Z_to_bv 64 0) ltac:(ok_data). renm.
stw F_2251c D_2251c (Z_to_bv 64 401808) (Z_to_bv 64 0) ltac:(ok_data). renm.
stepb_ft F_22520 D_22520 ltac:(pin; cond_compute). renm.
sn F_22524 D_22524. renm.
stw F_22528 D_22528 (Z_to_bv 64 401800) (Z_to_bv 64 8) ltac:(ok_data). renm.
sn F_2252c D_2252c. renm.
sn F_22530 D_22530. renm.
sn F_22534 D_22534. renm.
sn F_22538 D_22538. renm.
sn F_2253c D_2253c. renm.
sn F_22540 D_22540. renm.
stw F_22544 D_22544 (Z_to_bv 64 402432) (Z_to_bv 64 224) ltac:(ok_data). renm.
stw F_22548 D_22548 (Z_to_bv 64 402440) (Z_to_bv 64 8) ltac:(ok_data). renm.
stepb_tk F_2254c D_2254c ltac:(pin; cond_compute). renm.
sn F_22580 D_22580. renm.
ld_step F_22584 D_22584 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_623f8_8) ltac:(apply bytes_le_to_Z_8). renm.
ld_step F_22588 D_22588 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_62410_8) ltac:(apply bytes_le_to_Z_8). renm.
sn F_2258c D_2258c. renm.
sn F_22590 D_22590. renm.
sn F_22594 D_22594. renm.
sn F_22598 D_22598. renm.
sn F_2259c D_2259c. renm.
sn F_225a0 D_225a0. renm.
sn F_225a4 D_225a4. renm.
sn F_225a8 D_225a8. renm.
sn F_225ac D_225ac. renm.
sn F_225b0 D_225b0. renm.
sn F_225b4 D_225b4. renm.
stepb_tk F_225b8 D_225b8 ltac:(pin; cond_compute). renm.
stw F_22600 D_22600 (Z_to_bv 64 270696) (Z_to_bv 64 0) ltac:(ok_data). renm.
stw F_22604 D_22604 (Z_to_bv 64 270672) (Z_to_bv 64 270696) ltac:(ok_data). renm.
stw F_22608 D_22608 (Z_to_bv 64 270480) (Z_to_bv 64 270480) ltac:(ok_data). renm.
sn F_2260c D_2260c. renm.
sn F_22610 D_22610. renm.
sn F_2bd80 D_2bd80. renm.
sn F_2bd84 D_2bd84. renm.
stepret F_2bd88 D_2bd88 (0x22614 : word) ltac:(pin; first [reflexivity | bveq]). renm.
stepb_ft F_22614 D_22614 ltac:(pin; cond_compute). renm.
stepb_ft F_22618 D_22618 ltac:(pin; cond_compute). renm.
sn F_2261c D_2261c. renm.
stw F_22620 D_22620 (Z_to_bv 64 402408) (Z_to_bv 64 1) ltac:(ok_data). renm.
sn F_22624 D_22624. renm.
sn F_22628 D_22628. renm.
stw F_2262c D_2262c (Z_to_bv 64 270520) (Z_to_bv 64 2) ltac:(ok_data). renm.
sn F_22630 D_22630. renm.
sn F_22634 D_22634. renm.
sn F_22638 D_22638. renm.
stn_done. apply mst_refl. }
stn_final. apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hhi Hlo"] Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 270680 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 402464 ->
getr regs 18 = Z_to_bv 64 270480 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 270680) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 0) ->
getr regs' 21 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 2; 8; 9; 10; 12; 18; 19; 20; 21]%list) regs regs' ->
G (mkst regs' (0x221d0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139728))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 402408))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 401792) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401808) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401800) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 402432) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 402440) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 270696) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 270672) (word_to_le_bytes 8 (Z_to_bv 64 270696))) (Z_to_bv 64 270480) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 402408) ([Z_to_bv 8 1])) (Z_to_bv 64 270520) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 270512) (word_to_le_bytes 4 tid)) (Z_to_bv 64 270632) (word_to_le_bytes 8 (Z_to_bv 64 402464))) (Z_to_bv 64 270600) (word_to_le_bytes 8 (Z_to_bv 64 270600))) (Z_to_bv 64 270488) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 270496) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 270504) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x22640 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139728))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 402408))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 401792) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401808) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401800) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 402432) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 402440) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 270696) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 270672) (word_to_le_bytes 8 (Z_to_bv 64 270696))) (Z_to_bv 64 270480) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 402408) ([Z_to_bv 8 1])) (Z_to_bv 64 270520) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_22640 D_22640. renm.
stw F_22644 D_22644 (Z_to_bv 64 270512) tid ltac:(ok_data). renm.
stw F_22648 D_22648 (Z_to_bv 64 270632) (Z_to_bv 64 402464) ltac:(ok_data). renm.
stw F_2264c D_2264c (Z_to_bv 64 270600) (Z_to_bv 64 270600) ltac:(ok_data). renm.
sn F_22650 D_22650. renm.
ld_step F_22654 D_22654 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_623d0_8) ltac:(apply bytes_le_to_Z_8). renm.
stw F_22658 D_22658 (Z_to_bv 64 270488) (Z_to_bv 64 270480) ltac:(ok_data). renm.
stw F_2265c D_2265c (Z_to_bv 64 270496) (Z_to_bv 64 270480) ltac:(ok_data). renm.
stw F_22660 D_22660 (Z_to_bv 64 270504) (Z_to_bv 64 0) ltac:(ok_data). renm.
sn F_22664 D_22664. renm.
ld_step F_2266c D_2266c (word_to_le_bytes 8 (Z_to_bv 64 139728)) (Z_to_bv 64 139728) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.
ld_step F_22670 D_22670 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.
ld_step F_22674 D_22674 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.
ld_step F_22678 D_22678 (word_to_le_bytes 8 (Z_to_bv 64 402408)) (Z_to_bv 64 402408) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.
ld_step F_2267c D_2267c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.
ld_step F_22680 D_22680 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.
ld_step F_22684 D_22684 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.
sv F_22688 D_22688 (Z_to_bv 64 (bv_unsigned sp0 - 416)). renm.
stepret F_2268c D_2268c (0x221d0 : word) ltac:(pin; first [reflexivity | bveq]). renm.
stn_done. apply mst_refl. }
stn_final. apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
