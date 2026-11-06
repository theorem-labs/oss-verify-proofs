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
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WalkTac StoreOk Stre9ts MmapSim LibAvhx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg Nodes Spec LibWbxd D_Stqgu.

Module D_Exnq5.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WalkTac StoreOk Stre9ts MmapSim LibAvhx D_Exvwg D_co4d2 D_coj29.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Amb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require BWorld.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Stre9ts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibAvhx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Exvwg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_co4d2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_coj29 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Amb.D_co2af OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.BWorld.D_co8nq.   (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition mem_w1 (mem : word -> option byte) (sp ra s0 : word) (tid : Z) :=
  wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0x623c0) (word_to_le_bytes 4 (Z_to_bv 64 tid)).

(* [comment removed for export] *)
Definition stn_mark {A : Type} (x : A) : Prop := True.
Definition stn_markm {A : Type} (x : A) : Prop := True.      (* [comment removed for export] *)
Lemma stn_ex_by_eq : forall (A : Type) (P : A -> Prop) (w : A), (forall x, x = w -> P x) -> exists x, P x.
Proof. intros A P w H. exists w. exact (H w eq_refl). Qed.
Lemma stn_msteps_tgt : forall segs st tgt, (forall stF, stF = tgt -> msteps segs st stF) -> msteps segs st tgt.
Proof. intros segs st tgt H. exact (H tgt eq_refl). Qed.
Local Ltac stn_K := constr:(8%nat).
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
  | |- msteps _ (mkst ?R _ _ _) _ => stn_name_regs R; stn_name_M
  | |- _ => idtac
  end.
Local Ltac stn_open := repeat match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end.
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

Local Ltac stn_len bs :=
  lazymatch bs with
  | word_to_le_bytes ?n ?v => constr:(length_N_to_le_bytes n v)
  | repeat ?x ?n => constr:(repeat_length x n)
  | _ => constr:(@eq_refl nat (length bs))
  end.
(* [comment removed for export] *)
Local Ltac stn_rel e :=
  lazymatch e with
  | bv_unsigned ?w => constr:(stn_rel0 (bv_unsigned w))
  | (?x + ?k)%Z => let chk := ltac:(is_Z_lit k) in let p := stn_rel x in constr:(stn_rel_add _ _ _ k p)
  | (?x - ?k)%Z => let chk := ltac:(is_Z_lit k) in let p := stn_rel x in constr:(stn_rel_sub _ _ _ k p)
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
          stn_with_lo w ltac:(fun lo d H => rewrite (stn_peel_rl segs bs m w za zb _ lo d n _ pa H L (@eq_refl bool true))) end ]
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac.gres ::= stn_gres_old; repeat (stn_demand1; stn_gres_old).
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SumW496.rdn_peel1 ::=
  first [ stn_cheap_peel | rewrite rdn_wbytes_out_Z by (zlen; lia_fast) | rewrite rdn_wbytes_out by (zsimp; lia_fast) ].
Local Ltac stn_rdn_solve_loop :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
      tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
      else (rdn_peel1; stn_rdn_solve_loop)
  | |- rdn _ ?m _ _ = _ =>
      first [ (is_var m; (let body := eval unfold m in m in idtac); unfold m; stn_rdn_solve_loop) | rdn_hyp ]
  | |- _ => rdn_hyp
  end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SumW496.rdn_solve ::= stn_name_rdn; stn_rdn_solve_loop.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SumW496.rdn_by H ::=
  stn_name_rdn;
  repeat first [ rdn_peel1 | lazymatch goal with |- rdn _ ?m _ _ = _ => is_var m; (let body := eval unfold m in m in idtac); unfold m end ]; exact H.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SumW496.getr_hyps ::=
  repeat first [ match goal with H : getr ?rs ?n = _ |- context [getr ?rs ?n] => rewrite H end | stn_demand1 ].
(* [comment removed for export] *)
Lemma w1 : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x623c0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x2299c : word) mem rom)
                 (mkst regs' (0x227b8 : word) (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x22a00
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock.
  unfold mem_w1. stn_eexists. split.
  - (* [comment removed for export] *)
    renm. stepn F_2299c D_2299c. stn_open. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    renm. stepST F_229a0 D_229a0 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    renm. stepST F_229a4 D_229a4 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    renm. stepn F_229a8 D_229a8.
    renm. stepn F_229ac D_229ac. stn_open. rewrite Htp.
    (* [comment removed for export] *)
    renm. stepLD F_229b0 D_229b0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stn_open. rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    renm. stepn F_229b4 D_229b4.
    renm. stepn F_229b8 D_229b8.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_229bc | reflexivity | exact D_229bc
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_229c0 | reflexivity | exact D_229c0 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_229c4 | reflexivity | exact D_229c4
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    renm. stepb_ft F_229c8 D_229c8 ltac:(cond_compute).
    (* [comment removed for export] *)
    renm. stepn F_229cc D_229cc.
    (* [comment removed for export] *)
    renm. stepb_ft F_229d0 D_229d0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    renm. stepb_tk F_229d4 D_229d4 ltac:(cond_compute).
    (* [comment removed for export] *)
    renm. stepn F_229f8 D_229f8. stn_open. rewrite Ha0.
    (* [comment removed for export] *)
    renm. stepn F_229fc D_229fc.
    stn_done. apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wF0 (mem : word -> option byte) (sp code s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x22a00)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3v).
Definition mem_wFR (mem : word -> option byte) (sp code s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (mem_wF0 mem sp code s1v s2v s3v)
    (Z_to_bv 64 0x621a8) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x621a8) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))   (* [comment removed for export] *)
    (Z_to_bv 64 0x621a8) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x621b0) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x621a0) [Z_to_bv 8 1].
Definition mem_wFN (mem : word -> option byte) (sp code s1v s2v s3v : word) :=
  wbytes (mem_wF0 mem sp code s1v s2v s3v) (Z_to_bv 64 0x621a0) [Z_to_bv 8 1].
Definition mem_wF (mem : word -> option byte) (sp code s1v s2v s3v : word) (reg : bool) :=
  if reg then mem_wFR mem sp code s1v s2v s3v else mem_wFN mem sp code s1v s2v s3v.

Lemma rdn_wbytes_hit4 : forall segs m (a v : word),
  (bv_unsigned a + 4 <= 2^64)%Z ->
  rdn segs (wbytes m a (word_to_le_bytes 4 v)) a 4%nat = Some (word_to_le_bytes 4 v).
Proof.
  intros segs m a v Hnw.
  pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 v) m a) as H.
  rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
Qed.
Local Ltac rdn_hit4 := apply rdn_wbytes_hit4; u_norm; lia.
(* [comment removed for export] *)
Local Ltac walk_lock RET :=
  renm; stepn F_2b460 D_2b460;
  (chain_step; [reflexivity
    | eapply step_lb with (b := Z_to_bv 8 0);
      [exact F_2b464 | reflexivity | exact D_2b464 | gres; imm_norm; addr_norm; rdn_solve]
    | step_simpl]); vnorm;
  renm; stepb_tk F_2b468 D_2b468 ltac:(cond_compute);
  renm; stepret F_2b658 D_2b658 RET ltac:(bveq).
(* [comment removed for export] *)
Local Ltac walk_unlock RET :=
  renm; stepLD F_2b6e8 D_2b6e8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
    ltac:(rewrite v_addi_0; addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia);
  stn_open; try rewrite (v_lw_small 0) by lia;
  renm; stepb_ft F_2b6ec D_2b6ec ltac:(cond_compute);
  renm; stepret F_2b6f0 D_2b6f0 RET ltac:(bveq).

Lemma wF : forall regs mem rom (sp code s1v s2v s3v : word) (reg : bool),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x22a00 -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x623eb) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x621a4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  atexit_st mem reg ->
  exists regs',
    msteps RSEGS (mkst regs (0x227b8 : word) mem rom)
                 (mkst regs' (0x22950 : word) (mem_wF mem sp code s1v s2v s3v reg) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x22a04
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v s2v s3v reg Hsp Hs0 Hra Hs1 Hs2 Hs3 SPlo SPhi SOK Mnl Malock AT.
  destruct reg; unfold atexit_st in AT.
  - (* [comment removed for export] *)
    destruct AT as (Ahead & Aslot & Af0 & Aa0 & Anext & Aincb).
    unfold mem_wF, mem_wFR, mem_wF0. stn_eexists. split.
    + (* [comment removed for export] *)
      renm. stepn F_227b8 D_227b8. stn_open. rewrite Hsp. sp_renorm.
      renm. stepST F_227bc D_227bc (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x22a00) ltac:(sok_stack SOK).
      renm. stepST F_227c0 D_227c0 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      renm. stepST F_227c4 D_227c4 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
      renm. stepST F_227c8 D_227c8 (Z_to_bv 64 (bv_unsigned sp - 48)) s2v ltac:(sok_stack SOK).
      renm. stepST F_227cc D_227cc (Z_to_bv 64 (bv_unsigned sp - 56)) s3v ltac:(sok_stack SOK).
      (* [comment removed for export] *)
      renm. stepn F_227d0 D_227d0.
      renm. stepn F_227d4 D_227d4.
      renm. stepn F_227d8 D_227d8.
      renm. stepn F_227dc D_227dc.
      renm. stepn F_227e0 D_227e0.
      walk_lock (0x227e4 : word).
      (* [comment removed for export] *)
      renm. stepLD8 F_227e4 D_227e4 (Z_to_bv 64 0x621b8).
      renm. stepb_ft F_227e8 D_227e8 ltac:(cond_compute).
      (* [comment removed for export] *)
      renm. stepLD F_227ec D_227ec (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stn_open. try rewrite (v_lw_small 1) by lia.
      renm. stepn F_227f0 D_227f0.
      (* [comment removed for export] *)
      renm. stepiv F_22808 D_22808 (Z_to_bv 64 0) ltac:(gres; imm_norm; bveq).
      renm. stepST F_2280c D_2280c (Z_to_bv 64 0x621a8) (Z_to_bv 64 0) ltac:(sok_data).
      renm. stepb_ft F_22810 D_22810 ltac:(cond_compute).
      (* [comment removed for export] *)
      renm. stepLD8 F_22814 D_22814 (Z_to_bv 64 0x621b8).
      renm. stepiv F_22818 D_22818 (Z_to_bv 64 0) ltac:(gres; imm_norm; bveq).
      renm. stepiv F_2281c D_2281c (Z_to_bv 64 0x621b8) ltac:(gres; imm_norm; bveq).
      renm. stepLD8 F_22820 D_22820 (Z_to_bv 64 0x22948).
      renm. stepLD8 F_22824 D_22824 (Z_to_bv 64 0x17f8c).
      (* [comment removed for export] *)
      renm. stepn F_22828 D_22828.
      renm. stepn F_2282c D_2282c.
      walk_unlock (0x22830 : word).
      (* [comment removed for export] *)
      renm. stepn F_22830 D_22830.
      renm. stepjr F_22834 D_22834 (Z_to_bv 64 0x22948) ltac:(gres; reflexivity). vnorm.
      renm. stepjr F_22948 D_22948 (Z_to_bv 64 0x17f8c) ltac:(gres; reflexivity). vnorm.
      (* [comment removed for export] *)
      renm. stepn F_17f8c D_17f8c.
      stepLBU F_17f90 D_17f90 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
      renm. stepb_ft F_17f94 D_17f94 ltac:(cond_compute).
      renm. stepret F_17f98 D_17f98 (0x22838 : word) ltac:(bveq).
      (* [comment removed for export] *)
      renm. stepn F_22838 D_22838.
      renm. stepn F_2283c D_2283c.
      walk_lock (0x22840 : word).
      (* [comment removed for export] *)
      renm. stepLD F_22840 D_22840 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; repeat rdn_peel1; rdn_hit4) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stn_open. try rewrite (v_lw_small 0) by lia.
      renm. stepiv F_22844 D_22844 (Z_to_bv 64 18446744073709551615) ltac:(gres; imm_norm; bveq).
      renm. stepST F_22848 D_22848 (Z_to_bv 64 0x621a8) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
      renm. stepb_ft F_2284c D_2284c ltac:(cond_compute).
      (* [comment removed for export] *)
      renm. stepLD8 F_22850 D_22850 (Z_to_bv 64 0x621b8).
      renm. stepn F_22854 D_22854.
      renm. stepLD8 F_227f4 D_227f4 (Z_to_bv 64 0).
      renm. stepn F_227f8 D_227f8.
      renm. stepST F_227fc D_227fc (Z_to_bv 64 0x621a8) (Z_to_bv 64 32) ltac:(sok_data).
      renm. stepST F_22800 D_22800 (Z_to_bv 64 0x621b0) (Z_to_bv 64 0) ltac:(sok_data).
      renm. stepb_tk F_22804 D_22804 ltac:(cond_compute).
      (* [comment removed for export] *)
      renm. stepn F_22858 D_22858.
      renm. stepST F_2285c D_2285c (Z_to_bv 64 0x621a0) (Z_to_bv 64 1) ltac:(sok_data).
      stn_open. change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      (* [comment removed for export] *)
      renm. stepn F_22860 D_22860.
      renm. stepLD8 F_22864 D_22864 (Z_to_bv 64 0x22a00).
      renm. stepLD8 F_22868 D_22868 code.
      renm. stepLD8 F_2286c D_2286c s1v.
      renm. stepLD8 F_22870 D_22870 s2v.
      renm. stepLD8 F_22874 D_22874 s3v.
      renm. stepn F_22878 D_22878. sp_renorm.
      renm. stepn F_2287c D_2287c.
      walk_unlock (0x22a00 : word).
      renm. stepn F_22a00 D_22a00.
      stn_done. apply mst_refl.
    + repeat split; gres; try reflexivity.
  - (* [comment removed for export] *)
    rename AT into Ahead.
    unfold mem_wF, mem_wFN, mem_wF0. stn_eexists. split.
    + renm. stepn F_227b8 D_227b8. stn_open. rewrite Hsp. sp_renorm.
      renm. stepST F_227bc D_227bc (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x22a00) ltac:(sok_stack SOK).
      renm. stepST F_227c0 D_227c0 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      renm. stepST F_227c4 D_227c4 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
      renm. stepST F_227c8 D_227c8 (Z_to_bv 64 (bv_unsigned sp - 48)) s2v ltac:(sok_stack SOK).
      renm. stepST F_227cc D_227cc (Z_to_bv 64 (bv_unsigned sp - 56)) s3v ltac:(sok_stack SOK).
      renm. stepn F_227d0 D_227d0.
      renm. stepn F_227d4 D_227d4.
      renm. stepn F_227d8 D_227d8.
      renm. stepn F_227dc D_227dc.
      renm. stepn F_227e0 D_227e0.
      walk_lock (0x227e4 : word).
      (* [comment removed for export] *)
      renm. stepLD8 F_227e4 D_227e4 (Z_to_bv 64 0).
      renm. stepb_tk F_227e8 D_227e8 ltac:(cond_compute).
      renm. stepn F_22858 D_22858.
      renm. stepST F_2285c D_2285c (Z_to_bv 64 0x621a0) (Z_to_bv 64 1) ltac:(sok_data).
      stn_open. change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      renm. stepn F_22860 D_22860.
      renm. stepLD8 F_22864 D_22864 (Z_to_bv 64 0x22a00).
      renm. stepLD8 F_22868 D_22868 code.
      renm. stepLD8 F_2286c D_2286c s1v.
      renm. stepLD8 F_22870 D_22870 s2v.
      renm. stepLD8 F_22874 D_22874 s3v.
      renm. stepn F_22878 D_22878. sp_renorm.
      renm. stepn F_2287c D_2287c.
      walk_unlock (0x22a00 : word).
      renm. stepn F_22a00 D_22a00.
      stn_done. apply mst_refl.
    + repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x22a04)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x22980)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x30268)))
    (Z_to_bv 64 0x317f8) [Z_to_bv 8 1].

Lemma w2 : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x22a04 -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x30430) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x30270)) ->
  rdn RSEGS mem (Z_to_bv 64 0x30438) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x30268)) ->
  rdn RSEGS mem (Z_to_bv 64 0x30268) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x17ad4)) ->
  rdn RSEGS mem (Z_to_bv 64 0x317f8) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x303b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x22880)) ->
  rdn RSEGS mem (Z_to_bv 64 0x303c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x31458) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x31458)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x22950 : word) mem rom)
                 (mkst regs' (0x25ae8 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x22a08
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2. stn_eexists. split.
  - (* [comment removed for export] *)
    renm. stepn F_22950 D_22950. stn_open. rewrite Hsp. sp_renorm.
    renm. stepST F_22954 D_22954 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x22a04) ltac:(sok_stack SOK).
    renm. stepST F_22958 D_22958 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    renm. stepST F_2295c D_2295c (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    renm. stepn F_22960 D_22960.
    renm. stepn F_22964 D_22964.
    renm. stepLD8 F_22968 D_22968 (Z_to_bv 64 0x30270).
    renm. stepLD8 F_2296c D_2296c (Z_to_bv 64 0x30268).
    (* [comment removed for export] *)
    renm. stepb_ft F_22970 D_22970 ltac:(cond_compute).
    (* [comment removed for export] *)
    renm. stepLD8 F_22974 D_22974 (Z_to_bv 64 0x17ad4).
    renm. stepn F_22978 D_22978.
    renm. stepjr F_2297c D_2297c (Z_to_bv 64 0x17ad4) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    renm. stepn F_17ad4 D_17ad4. sp_renorm.
    renm. stepST F_17ad8 D_17ad8 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x22980) ltac:(sok_stack SOK).
    renm. stepST F_17adc D_17adc (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x30268) ltac:(sok_stack SOK).
    renm. stepn F_17ae0 D_17ae0.
    renm. stepn F_17ae4 D_17ae4.
    renm. stepn F_17ae8 D_17ae8.
    (* [comment removed for export] *)
    stepLBU F_17aec D_17aec (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    renm. stepn F_17af0 D_17af0.
    renm. stepb_tk F_17af4 D_17af4 ltac:(cond_compute).
    renm. stepn F_17b00 D_17b00.
    renm. stepn F_17b04 D_17b04.
    renm. stepn F_17b08 D_17b08.
    (* [comment removed for export] *)
    renm. stepST F_17b0c D_17b0c (Z_to_bv 64 0x317f8) (Z_to_bv 64 1) ltac:(sok_data).
    stn_open. change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    renm. stepn F_17b10 D_17b10.
    renm. stepLD8 F_17b14 D_17b14 (Z_to_bv 64 0x22880).
    renm. stepb_ft F_17b18 D_17b18 ltac:(cond_compute).
    renm. stepn F_17b1c D_17b1c.
    renm. stepn F_17b20 D_17b20.
    renm. stepn F_17b24 D_17b24.
    renm. stepLD8 F_17b28 D_17b28 (Z_to_bv 64 0x31458).
    renm. stepn F_17b2c D_17b2c.
    renm. stepret F_22880 D_22880 (0x17b30 : word) ltac:(bveq).
    renm. stepn F_17b30 D_17b30.
    (* [comment removed for export] *)
    renm. stepn F_17b34 D_17b34.
    renm. stepLD8 F_17b38 D_17b38 (Z_to_bv 64 0).
    renm. stepb_tk F_17b3c D_17b3c ltac:(cond_compute).
    (* [comment removed for export] *)
    renm. stepLD8 F_17b54 D_17b54 (Z_to_bv 64 0x22980).
    renm. stepLD8 F_17b58 D_17b58 (Z_to_bv 64 0x30268).
    renm. stepn F_17b5c D_17b5c. sp_renorm.
    renm. stepret F_17b60 D_17b60 (0x22980 : word) ltac:(bveq).
    (* [comment removed for export] *)
    renm. stepn F_22980 D_22980.
    renm. stepb_ft F_22984 D_22984 ltac:(cond_compute).
    renm. stepLD8 F_22988 D_22988 (Z_to_bv 64 0x22a04).
    renm. stepLD8 F_2298c D_2298c code.
    renm. stepLD8 F_22990 D_22990 s1v.
    renm. stepn F_22994 D_22994. sp_renorm.
    (* [comment removed for export] *)
    renm. stepn F_22998 D_22998.
    renm. stepret F_2294c D_2294c (0x22a04 : word) ltac:(bveq).
    renm. stepn F_22a04 D_22a04.
    stn_done. apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End D_Exnq5.


Module D_Ex8ka.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WalkTac StoreOk Stre9ts MmapSim LibAvhx D_Exvwg D_coj29.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Amb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require BWorld.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Stre9ts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibAvhx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Exvwg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_coj29 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Amb.D_co2af OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.BWorld.D_co8nq.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x22a08)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x25af8)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

(* [comment removed for export] *)
Definition stn_mark {A : Type} (x : A) : Prop := True.
Definition stn_markm {A : Type} (x : A) : Prop := True.      (* [comment removed for export] *)
Lemma stn_ex_by_eq : forall (A : Type) (P : A -> Prop) (w : A), (forall x, x = w -> P x) -> exists x, P x.
Proof. intros A P w H. exists w. exact (H w eq_refl). Qed.
Lemma stn_msteps_tgt : forall segs st tgt, (forall stF, stF = tgt -> msteps segs st stF) -> msteps segs st tgt.
Proof. intros segs st tgt H. exact (H tgt eq_refl). Qed.
Local Ltac stn_K := constr:(8%nat).
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
  | |- msteps _ (mkst ?R _ _ _) _ => stn_name_regs R; stn_name_M
  | |- _ => idtac
  end.
Local Ltac stn_open := repeat match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end.
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

Local Ltac stn_len bs :=
  lazymatch bs with
  | word_to_le_bytes ?n ?v => constr:(length_N_to_le_bytes n v)
  | repeat ?x ?n => constr:(repeat_length x n)
  | _ => constr:(@eq_refl nat (length bs))
  end.
(* [comment removed for export] *)
Local Ltac stn_rel e :=
  lazymatch e with
  | bv_unsigned ?w => constr:(stn_rel0 (bv_unsigned w))
  | (?x + ?k)%Z => let chk := ltac:(is_Z_lit k) in let p := stn_rel x in constr:(stn_rel_add _ _ _ k p)
  | (?x - ?k)%Z => let chk := ltac:(is_Z_lit k) in let p := stn_rel x in constr:(stn_rel_sub _ _ _ k p)
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
          stn_with_lo w ltac:(fun lo d H => rewrite (stn_peel_rl segs bs m w za zb _ lo d n _ pa H L (@eq_refl bool true))) end ]
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac.gres ::= stn_gres_old; repeat (stn_demand1; stn_gres_old).
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SumW496.rdn_peel1 ::=
  first [ stn_cheap_peel | rewrite rdn_wbytes_out_Z by (zlen; lia_fast) | rewrite rdn_wbytes_out by (zsimp; lia_fast) ].
Local Ltac stn_rdn_solve_loop :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
      tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
      else (rdn_peel1; stn_rdn_solve_loop)
  | |- rdn _ ?m _ _ = _ =>
      first [ (is_var m; (let body := eval unfold m in m in idtac); unfold m; stn_rdn_solve_loop) | rdn_hyp ]
  | |- _ => rdn_hyp
  end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SumW496.rdn_solve ::= stn_name_rdn; stn_rdn_solve_loop.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SumW496.rdn_by H ::=
  stn_name_rdn;
  repeat first [ rdn_peel1 | lazymatch goal with |- rdn _ ?m _ _ = _ => is_var m; (let body := eval unfold m in m in idtac); unfold m end ]; exact H.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SumW496.getr_hyps ::=
  repeat first [ match goal with H : getr ?rs ?n = _ |- context [getr ?rs ?n] => rewrite H end | stn_demand1 ].
(* [comment removed for export] *)
Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x22a08 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0x31698 wp1 rp1 ->
  file_clean mem 0x315a8 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x25ae8 : word) mem rom)
                 (mkst regs' (0x22774 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  (intros regs mem rom sp code wp1 rp1 wp2 rp2 Hsp Hs0 Hra SPlo SPhi SOK; (first [ intro dR_1; dand5 dR_1 as Gnl Gofl Gin Gout Gerr | intros (Gnl & Gofl & Gin & Gout & Gerr) ]); (first [ intro dR_2; dand5 dR_2 as F1l F1wp F1wb F1rp F1re | intros (F1l & F1wp & F1wb & F1rp & F1re) ]); (first [ intro dR_3; dand5 dR_3 as F2l F2wp F2wb F2rp F2re | intros (F2l & F2wp & F2wb & F2rp & F2re) ])).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  unfold mem_w3a. stn_eexists. split.
  - (* [comment removed for export] *)
    renm. stepn F_25ae8 D_25ae8. stn_open. rewrite Hsp. sp_renorm.
    renm. stepST F_25aec D_25aec (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x22a08) ltac:(sok_stack SOK).
    renm. stepST F_25af0 D_25af0 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    renm. stepn F_25af4 D_25af4.
    renm. stepn F_25c8c D_25c8c. sp_renorm.
    renm. stepST F_25c90 D_25c90 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x25af8) ltac:(sok_stack SOK).
    renm. stepST F_25c94 D_25c94 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    renm. stepn F_25c98 D_25c98.
    renm. stepn F_25c9c D_25c9c.
    renm. stepn F_25ca0 D_25ca0.
    (* [comment removed for export] *)
    renm. stepn F_25ca4 D_25ca4.
    renm. stepn F_2b460 D_2b460.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_2b464 | reflexivity | exact D_2b464 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    renm. stepb_tk F_2b468 D_2b468 ltac:(cond_compute).
    renm. stepret F_2b658 D_2b658 (0x25ca8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    renm. stepn F_25ca8 D_25ca8.
    renm. stepLD8 F_25cac D_25cac (Z_to_bv 64 0x25af8).
    renm. stepLD8 F_25cb0 D_25cb0 code.
    renm. stepn F_25cb4 D_25cb4. sp_renorm.
    renm. stepret F_25cb8 D_25cb8 (0x25af8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    renm. stepLD8 F_25af8 D_25af8 (Z_to_bv 64 0).
    renm. stepb_ft F_25afc D_25afc ltac:(cond_compute).
    (* [comment removed for export] *)
    renm. stepn F_25b00 D_25b00.
    renm. stepLD8 F_25b04 D_25b04 (Z_to_bv 64 0).
    renm. stepb_tk F_25b08 D_25b08 ltac:(cond_compute).
    (* [comment removed for export] *)
    renm. stepn F_25b5c D_25b5c.
    renm. stepLD8 F_25b60 D_25b60 (Z_to_bv 64 0x31698).
    renm. stepb_ft F_25b64 D_25b64 ltac:(cond_compute).
    (* [comment removed for export] *)
    renm. stepLD F_25b68 D_25b68 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    renm. stepb_tk F_25b6c D_25b6c ltac:(cond_compute).
    (* [comment removed for export] *)
    renm. stepLD8 F_25b78 D_25b78 wp1.
    renm. stepLD8 F_25b7c D_25b7c wp1.
    renm. stepb_tk F_25b80 D_25b80 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    renm. stepLD8 F_25b98 D_25b98 rp1.
    renm. stepLD8 F_25b9c D_25b9c rp1.
    renm. stepb_tk F_25ba0 D_25ba0 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    renm. stepn F_25bb8 D_25bb8.
    renm. stepLD8 F_25bbc D_25bbc (Z_to_bv 64 0x315a8).
    renm. stepb_ft F_25bc0 D_25bc0 ltac:(cond_compute).
    renm. stepLD F_25bc4 D_25bc4 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    renm. stepb_tk F_25bc8 D_25bc8 ltac:(cond_compute).
    renm. stepLD8 F_25bd4 D_25bd4 wp2.
    renm. stepLD8 F_25bd8 D_25bd8 wp2.
    renm. stepb_tk F_25bdc D_25bdc ltac:(apply c_eq_refl).
    renm. stepLD8 F_25bf4 D_25bf4 rp2.
    renm. stepLD8 F_25bf8 D_25bf8 rp2.
    renm. stepb_tk F_25bfc D_25bfc ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    renm. stepLD8 F_25c7c D_25c7c (Z_to_bv 64 0x22a08).
    renm. stepLD8 F_25c80 D_25c80 code.
    renm. stepn F_25c84 D_25c84. sp_renorm.
    renm. stepret F_25c88 D_25c88 (0x22a08 : word) ltac:(bveq).
    (* [comment removed for export] *)
    renm. stepn F_22a08 D_22a08.
    renm. stepn F_22a0c D_22a0c.
    renm. stepn F_2276c D_2276c.
    renm. stepn F_22770 D_22770.
    stn_done. apply mst_refl.
  - OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End D_Ex8ka.


Module D_Ex1il.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WalkTac StoreOk Stre9ts MmapSim LibAvhx D_Exvwg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_coj29.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Amb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require BWorld.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Stre9ts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibAvhx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Exvwg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Exit.D_Ex8ka OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_coj29 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Amb.D_co2af OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.BWorld.D_co8nq.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (0x31698 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x31698 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x31698 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x31698 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x25d58)).

(* [comment removed for export] *)
Definition stn_mark {A : Type} (x : A) : Prop := True.
Definition stn_markm {A : Type} (x : A) : Prop := True.      (* [comment removed for export] *)
Lemma stn_ex_by_eq : forall (A : Type) (P : A -> Prop) (w : A), (forall x, x = w -> P x) -> exists x, P x.
Proof. intros A P w H. exists w. exact (H w eq_refl). Qed.
Lemma stn_msteps_tgt : forall segs st tgt, (forall stF, stF = tgt -> msteps segs st stF) -> msteps segs st tgt.
Proof. intros segs st tgt H. exact (H tgt eq_refl). Qed.
Local Ltac stn_K := constr:(8%nat).
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
  | |- msteps _ (mkst ?R _ _ _) _ => stn_name_regs R; stn_name_M
  | |- _ => idtac
  end.
Local Ltac stn_open := repeat match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end.
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

Local Ltac stn_len bs :=
  lazymatch bs with
  | word_to_le_bytes ?n ?v => constr:(length_N_to_le_bytes n v)
  | repeat ?x ?n => constr:(repeat_length x n)
  | _ => constr:(@eq_refl nat (length bs))
  end.
(* [comment removed for export] *)
Local Ltac stn_rel e :=
  lazymatch e with
  | bv_unsigned ?w => constr:(stn_rel0 (bv_unsigned w))
  | (?x + ?k)%Z => let chk := ltac:(is_Z_lit k) in let p := stn_rel x in constr:(stn_rel_add _ _ _ k p)
  | (?x - ?k)%Z => let chk := ltac:(is_Z_lit k) in let p := stn_rel x in constr:(stn_rel_sub _ _ _ k p)
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
          stn_with_lo w ltac:(fun lo d H => rewrite (stn_peel_rl segs bs m w za zb _ lo d n _ pa H L (@eq_refl bool true))) end ]
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac.gres ::= stn_gres_old; repeat (stn_demand1; stn_gres_old).
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SumW496.rdn_peel1 ::=
  first [ stn_cheap_peel | rewrite rdn_wbytes_out_Z by (zlen; lia_fast) | rewrite rdn_wbytes_out by (zsimp; lia_fast) ].
Local Ltac stn_rdn_solve_loop :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
      tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
      else (rdn_peel1; stn_rdn_solve_loop)
  | |- rdn _ ?m _ _ = _ =>
      first [ (is_var m; (let body := eval unfold m in m in idtac); unfold m; stn_rdn_solve_loop) | rdn_hyp ]
  | |- _ => rdn_hyp
  end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SumW496.rdn_solve ::= stn_name_rdn; stn_rdn_solve_loop.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SumW496.rdn_by H ::=
  stn_name_rdn;
  repeat first [ rdn_peel1 | lazymatch goal with |- rdn _ ?m _ _ = _ => is_var m; (let body := eval unfold m in m in idtac); unfold m end ]; exact H.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SumW496.getr_hyps ::=
  repeat first [ match goal with H : getr ?rs ?n = _ |- context [getr ?rs ?n] => rewrite H end | stn_demand1 ].
(* [comment removed for export] *)
Lemma w3b1 : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x22a08 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps RSEGS (mkst regs (0x25ae8 : word) mem rom)
                 (mkst regs' (0x25d58 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0x31698
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0x25b98
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0x31698
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  (intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK; (first [ intro dR_1; dand5 dR_1 as Gnl Gofl Gin Gout Gerr | intros (Gnl & Gofl & Gin & Gout & Gerr) ]); (first [ intro dR_2; dand4 dR_2 as F1l F1wp F1wb F1wr | intros (F1l & F1wp & F1wb & F1wr) ]); intros WB WP NE).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  unfold mem_w3a. stn_eexists. split.
  - (* [comment removed for export] *)
    renm. stepn F_25ae8 D_25ae8. stn_open. rewrite Hsp. sp_renorm.
    renm. stepST F_25aec D_25aec (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x22a08) ltac:(sok_stack SOK).
    renm. stepST F_25af0 D_25af0 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    renm. stepn F_25af4 D_25af4.
    renm. stepn F_25c8c D_25c8c. sp_renorm.
    renm. stepST F_25c90 D_25c90 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x25af8) ltac:(sok_stack SOK).
    renm. stepST F_25c94 D_25c94 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    renm. stepn F_25c98 D_25c98.
    renm. stepn F_25c9c D_25c9c.
    renm. stepn F_25ca0 D_25ca0.
    (* [comment removed for export] *)
    renm. stepn F_25ca4 D_25ca4.
    renm. stepn F_2b460 D_2b460.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_2b464 | reflexivity | exact D_2b464 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    renm. stepb_tk F_2b468 D_2b468 ltac:(cond_compute).
    renm. stepret F_2b658 D_2b658 (0x25ca8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    renm. stepn F_25ca8 D_25ca8.
    renm. stepLD8 F_25cac D_25cac (Z_to_bv 64 0x25af8).
    renm. stepLD8 F_25cb0 D_25cb0 code.
    renm. stepn F_25cb4 D_25cb4. sp_renorm.
    renm. stepret F_25cb8 D_25cb8 (0x25af8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    renm. stepLD8 F_25af8 D_25af8 (Z_to_bv 64 0).
    renm. stepb_ft F_25afc D_25afc ltac:(cond_compute).
    (* [comment removed for export] *)
    renm. stepn F_25b00 D_25b00.
    renm. stepLD8 F_25b04 D_25b04 (Z_to_bv 64 0).
    renm. stepb_tk F_25b08 D_25b08 ltac:(cond_compute).
    (* [comment removed for export] *)
    renm. stepn F_25b5c D_25b5c.
    renm. stepLD8 F_25b60 D_25b60 (Z_to_bv 64 0x31698).
    renm. stepb_ft F_25b64 D_25b64 ltac:(cond_compute).
    (* [comment removed for export] *)
    renm. stepLD F_25b68 D_25b68 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    renm. stepb_tk F_25b6c D_25b6c ltac:(cond_compute).
    (* [comment removed for export] *)
    renm. stepLD8 F_25b78 D_25b78 (Z_to_bv 64 wp).
    renm. stepLD8 F_25b7c D_25b7c (Z_to_bv 64 wb).
    renm. stepb_ft F_25b80 D_25b80 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    renm. stepLD8 F_25b84 D_25b84 (Z_to_bv 64 0x25d58).
    renm. stepn F_25b88 D_25b88.
    renm. stepn F_25b8c D_25b8c.
    renm. stepn F_25b90 D_25b90.
    renm. stepjr F_25b94 D_25b94 (Z_to_bv 64 0x25d58) ltac:(gres; reflexivity). vnorm.
    stn_done. apply mst_refl.
  - OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w3b2 : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0x31698 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x22a08)) ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn RSEGS mem (Z_to_bv 64 (0x31698 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 (0x31698 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 0x31690) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x315a8)) ->
  file_clean mem 0x315a8 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x25b98 : word) mem rom)
                 (mkst regs' (0x22774 : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  (intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr; (first [ intro dR_3; dand5 dR_3 as F2l F2wp F2wb F2rp F2re | intros (F2l & F2wp & F2wb & F2rp & F2re) ])).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  stn_eexists. split.
  - (* [comment removed for export] *)
    renm. stepLD8 F_25b98 D_25b98 rp1.
    renm. stepLD8 F_25b9c D_25b9c rp1.
    renm. stepb_tk F_25ba0 D_25ba0 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    renm. stepn F_25bb8 D_25bb8.
    renm. stepLD8 F_25bbc D_25bbc (Z_to_bv 64 0x315a8).
    renm. stepb_ft F_25bc0 D_25bc0 ltac:(cond_compute).
    renm. stepLD F_25bc4 D_25bc4 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    renm. stepb_tk F_25bc8 D_25bc8 ltac:(cond_compute).
    renm. stepLD8 F_25bd4 D_25bd4 wp2.
    renm. stepLD8 F_25bd8 D_25bd8 wp2.
    renm. stepb_tk F_25bdc D_25bdc ltac:(apply c_eq_refl).
    renm. stepLD8 F_25bf4 D_25bf4 rp2.
    renm. stepLD8 F_25bf8 D_25bf8 rp2.
    renm. stepb_tk F_25bfc D_25bfc ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    renm. stepLD8 F_25c7c D_25c7c (Z_to_bv 64 0x22a08).
    renm. stepLD8 F_25c80 D_25c80 code.
    renm. stepn F_25c84 D_25c84. stn_open. rewrite Hsp. sp_renorm.
    renm. stepret F_25c88 D_25c88 (0x22a08 : word) ltac:(bveq).
    (* [comment removed for export] *)
    renm. stepn F_22a08 D_22a08.
    renm. stepn F_22a0c D_22a0c.
    renm. stepn F_2276c D_2276c.
    renm. stepn F_22770 D_22770.
    stn_done. apply mst_refl.
  - OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End D_Ex1il.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_St8vg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_St8vg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_St8vg D_co4d2 D_coj29.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Amb.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Stre9ts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibAvhx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibWbxd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Stqgu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Exit.D_Exnq5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Exit.D_Ex8ka OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Exit.D_Ex1il OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_St8vg.D_St0rr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_St8vg.D_St7f8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_St8vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_co4d2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_coj29 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Amb.D_co2af.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stn_mark {A : Type} (x : A) : Prop := True.
Definition stn_markm {A : Type} (x : A) : Prop := True.      (* [comment removed for export] *)
Lemma stn_ex_by_eq : forall (A : Type) (P : A -> Prop) (w : A), (forall x, x = w -> P x) -> exists x, P x.
Proof. intros A P w H. exists w. exact (H w eq_refl). Qed.
Lemma stn_msteps_tgt : forall segs st tgt, (forall stF, stF = tgt -> msteps segs st stF) -> msteps segs st tgt.
Proof. intros segs st tgt H. exact (H tgt eq_refl). Qed.
Local Ltac stn_K := constr:(8%nat).
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
  | |- msteps _ (mkst ?R _ _ _) _ => stn_name_regs R; stn_name_M
  | |- _ => idtac
  end.
Local Ltac stn_open := repeat match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end.
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

Local Ltac stn_len bs :=
  lazymatch bs with
  | word_to_le_bytes ?n ?v => constr:(length_N_to_le_bytes n v)
  | repeat ?x ?n => constr:(repeat_length x n)
  | _ => constr:(@eq_refl nat (length bs))
  end.
(* [comment removed for export] *)
Local Ltac stn_rel e :=
  lazymatch e with
  | bv_unsigned ?w => constr:(stn_rel0 (bv_unsigned w))
  | (?x + ?k)%Z => let chk := ltac:(is_Z_lit k) in let p := stn_rel x in constr:(stn_rel_add _ _ _ k p)
  | (?x - ?k)%Z => let chk := ltac:(is_Z_lit k) in let p := stn_rel x in constr:(stn_rel_sub _ _ _ k p)
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
          stn_with_lo w ltac:(fun lo d H => rewrite (stn_peel_rl segs bs m w za zb _ lo d n _ pa H L (@eq_refl bool true))) end ]
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac.gres ::= stn_gres_old; repeat (stn_demand1; stn_gres_old).
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SumW496.rdn_peel1 ::=
  first [ stn_cheap_peel | rewrite rdn_wbytes_out_Z by (zlen; lia_fast) | rewrite rdn_wbytes_out by (zsimp; lia_fast) ].
Local Ltac stn_rdn_solve_loop :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
      tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
      else (rdn_peel1; stn_rdn_solve_loop)
  | |- rdn _ ?m _ _ = _ =>
      first [ (is_var m; (let body := eval unfold m in m in idtac); unfold m; stn_rdn_solve_loop) | rdn_hyp ]
  | |- _ => rdn_hyp
  end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SumW496.rdn_solve ::= stn_name_rdn; stn_rdn_solve_loop.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SumW496.rdn_by H ::=
  stn_name_rdn;
  repeat first [ rdn_peel1 | lazymatch goal with |- rdn _ ?m _ _ = _ => is_var m; (let body := eval unfold m in m in idtac); unfold m end ]; exact H.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SumW496.getr_hyps ::=
  repeat first [ match goal with H : getr ?rs ?n = _ |- context [getr ?rs ?n] => rewrite H end | stn_demand1 ].
(* [comment removed for export] *)
Theorem ref_exit_clean {BW : BWorld} :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word) (reg : bool),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  atexit_st mem reg ->
  file_clean mem 0x31698 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x2299c : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 reg EC AT F1 Hh Hlazy.
  destruct EC.
  (first [ dand5 ec_glob as Gnl Gofl Gin Gout Gerr | destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr) ]).
  (* [comment removed for export] *)
  destruct (w1 regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1 & R1s2 & R1s3);
    try assumption.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  (* [comment removed for export] *)
  destruct (wF regs1 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) (seg_rom RSEGS) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19) reg)
    as (regsF & RUNF & RFsp & RFs0 & RFra & RFs1 & RFtp & RFgp); try assumption; try reflexivity.
  all: try (unfold mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
  1:{ destruct reg; unfold atexit_st in AT |- *;
      [ destruct AT as (Ahead & Aslot & Af0 & Aa0 & Anext & Aincb); OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit | ];
      unfold mem_w1; rdn_solve. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUNF |]. clear RUNF.
  (* [comment removed for export] *)
  destruct (w2 regsF (mem_wF (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19) reg) (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (destruct reg; unfold mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  (first [ dand5 ec_err as F2l F2wp F2wb F2rp F2re | destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re) ]).
  (first [ dand5 F1 as F1l F1wp F1wb F1rp F1re | destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re) ]).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  (first [ pose proof ((w3a regs2 (mem_w2 (mem_wF (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19) reg) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)) as dR_6; dex1 dR_6 as regs3; dand4 dR_6 as RUN3 R3a0 R3a7 R3sp | pose proof ((w3a regs2 (mem_w2 (mem_wF (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19) reg) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)) as dR_6; dand5 dR_6 as regs3 RUN3 R3a0 R3a7 R3sp | destruct (w3a regs2 (mem_w2 (mem_wF (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19) reg) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)
    as (regs3 & RUN3 & R3a0 & R3a7 & R3sp) ]); try assumption.
  1:{ destruct reg; unfold mem_w2, mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; store_ok_peel; exact ec_sok. }
  1:{ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; destruct reg; unfold mem_w2, mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; rdn_solve. }
  1:{ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; destruct reg; unfold mem_w2, mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; zaddr_goal; rdn_solve. }
  1:{ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; destruct reg; unfold mem_w2, mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; zaddr_goal; rdn_solve. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  eapply rz_exit_at; [exact F_22774 | exact E_22774 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ref_exit_flush {BW : BWorld} :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte) (reg : bool),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  atexit_st mem reg ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  realizes RSEGS (mkCfg (mkst regs (0x2299c : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending reg EC AT SP Hh Hlazy Hfd.
  destruct EC.
  (first [ dand5 ec_glob as Gnl Gofl Gin Gout Gerr | destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr) ]). destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  (* [comment removed for export] *)
  destruct (w1 regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1 & R1s2 & R1s3);
    try assumption.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  (* [comment removed for export] *)
  destruct (wF regs1 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) (seg_rom RSEGS) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19) reg)
    as (regsF & RUNF & RFsp & RFs0 & RFra & RFs1 & RFtp & RFgp); try assumption; try reflexivity.
  all: try (unfold mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
  1:{ destruct reg; unfold atexit_st in AT |- *;
      [ destruct AT as (Ahead & Aslot & Af0 & Aa0 & Anext & Aincb); OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit | ];
      unfold mem_w1; rdn_solve. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUNF |]. clear RUNF.
  (* [comment removed for export] *)
  destruct (w2 regsF (mem_wF (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19) reg) (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (destruct reg; unfold mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  (first [ pose proof ((w3b1 regs2 (mem_w2 (mem_wF (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19) reg) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wb wp)) as dR_10; dex1 dR_10 as regs3; dand9 dR_10 as RUN3 R3a0 R3a1 R3a2 R3ra R3sp R3s0 R3gp R3tp | pose proof ((w3b1 regs2 (mem_w2 (mem_wF (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19) reg) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wb wp)) as dR_10; dand10 dR_10 as regs3 RUN3 R3a0 R3a1 R3a2 R3ra R3sp R3s0 R3gp R3tp | destruct (w3b1 regs2 (mem_w2 (mem_wF (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19) reg) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wb wp)
    as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp) ]); try assumption; try lia.
  1:{ destruct reg; unfold mem_w2, mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; store_ok_peel; exact ec_sok. }
  1:{ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; destruct reg; unfold mem_w2, mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; rdn_solve. }
  1:{ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; destruct reg; unfold mem_w2, mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; zaddr_goal; rdn_solve. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x25b98) with (0x25b98 : word) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a (mem_w2 (mem_wF (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19) reg) sp code (getr regs1 9)) sp code).
  eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x31698 wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x25b98 : word) pending []);
    [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
    | lia | lia
    | (* [comment removed for export] *)
      subst mem3; destruct reg; unfold mem_w3a, mem_w2, mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; sok_stack ec_sok
    | lia | lia
    | (* [comment removed for export] *) split; subst mem3; destruct reg; unfold mem_w3a, mem_w2, mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; zaddr_goal; rdn_solve
    | (* [comment removed for export] *) split; subst mem3; destruct reg; unfold mem_w3a, mem_w2, mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; rdn_solve
    | lia | exact Hfd | exact Hh | exact Hlazy
    | lia | lia | exact LEN
    | cbn [length]; u_norm; reflexivity
    | cbn [length]; lia
    | lia | u_norm; lia | u_norm; lia
    | subst mem3; destruct reg; unfold mem_w3a, mem_w2, mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; repeat rdn_peel1; exact BYTES
    | reflexivity
    | apply ret_ok_even; reflexivity
    | apply t_emit_has_nil
    | ].
  intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
    rewrite R3s0 in Q8.
    (first [ dand5 ec_err as F2l F2wp F2wb F2rp F2re | destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re) ]).
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
    (first [ pose proof ((w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2)) as dR_12; dex1 dR_12 as regs5; dand4 dR_12 as RUN5 R5a0 R5a7 R5sp | pose proof ((w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2)) as dR_12; dand5 dR_12 as regs5 RUN5 R5a0 R5a7 R5sp | destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp) ]); try assumption.
    all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; destruct reg; unfold mem_w3a, mem_w2, mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
    1:{ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; destruct reg; unfold mem_w3a, mem_w2, mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
    eapply rz_exit_at; [exact F_22774 | exact E_22774 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

Theorem ref_exit {BW : BWorld} : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (0x2299c : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & reg & EC & AT & Hh & Hlazy & CASES).
  destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd)].
  - eapply rz_conseq; [ | apply t_emit_nil_exit ].
    eapply ref_exit_clean; eassumption.
  - eapply ref_exit_flush; eassumption.
Qed.

(* [comment removed for export] *)
Corollary ref_exit_Z {BW : BWorld} : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2299c) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x2299c) with (0x2299c : word) by (apply bv_eq; reflexivity).
  apply ref_exit; assumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
