(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from D_St8vg.v: the __stdio_write walk (ref_stdio_write) restated over BudgetWit.Rzb.rzb *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the section's write steps take the channel-reader premise (m_channel_reader) the model's new write arms read. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg Nodes LibWbxd Frame RefMocc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Stqgu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import D_St8vg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Amb.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Stre9ts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibAvhx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibWbxd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Stqgu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_St8vg.D_St0rr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_St8vg.D_St7f8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Amb.D_co2af.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
Import ListNotations.

Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.

Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.BudgetWit Require Import Rzb Agenxn8B NodesB LibWbxdB.

Lemma rzb_emit_nil : forall c K, rzb RSEGS c K -> rzb RSEGS c (t_emit [] K).
Proof.
  intros c K H. eapply rzb_conseq; [exact H|].
  apply t_eq_sym. apply t_emit_nil_eq. exact (rzb_nonempty _ _ _ H).
Qed.

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
Local Ltac stn_open :=
  repeat match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end;
  try lazymatch goal with E : ?s = _ |- msteps _ _ ?s => rewrite E end.
Local Ltac stn_done :=
  repeat first [ match goal with H : stn_mark ?x |- ?g => lazymatch g with context [x] => unfold x end end
               | match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end ];
  try lazymatch goal with E : ?s = _ |- msteps _ _ ?s => rewrite E end;
  stn_wit.

Local Open Scope Z_scope.
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
  | repeat ?x ?n => constr:(repeat_length x n)
  | _ => constr:(@eq_refl nat (length bs))
  end.

Local Ltac stn_rel e :=
  lazymatch e with
  | bv_unsigned ?w => constr:(stn_rel0 (bv_unsigned w))
  | (?x + ?k)%Z => let chk := ltac:(is_Z_lit k) in let p := stn_rel x in constr:(stn_rel_add _ _ _ k p)
  | (?x - ?k)%Z => let chk := ltac:(is_Z_lit k) in let p := stn_rel x in constr:(stn_rel_sub _ _ _ k p)
  | _ => let chk := ltac:(is_var e) in constr:(stn_rel0 e)
  end.

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
      [ 
        is_Z_lit za; is_Z_lit zb; rewrite (stn_peel_ll segs bs m za zb n _ L (@eq_refl bool true))
      | 
        let pa := stn_rel za in let pb := stn_rel zb in
        lazymatch type of pa with _ = (bv_unsigned ?w + _)%Z =>
          stn_with_lo w ltac:(fun lo d H => rewrite (stn_peel_rr segs bs m w za zb _ _ lo d n _ pa pb H L (@eq_refl bool true))) end
      | 
        is_Z_lit za; let pb := stn_rel zb in
        lazymatch type of pb with _ = (bv_unsigned ?w + _)%Z =>
          stn_with_lo w ltac:(fun lo d H => rewrite (stn_peel_lr segs bs m w za zb _ lo d n _ pb H L (@eq_refl bool true))) end
      | 
        is_Z_lit zb; let pa := stn_rel za in
        lazymatch type of pa with _ = (bv_unsigned ?w + _)%Z =>
          stn_with_lo w ltac:(fun lo d H => rewrite (stn_peel_rl segs bs m w za zb _ lo d n _ pa H L (@eq_refl bool true))) end
      | 
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc.solve_keeps ::=
  stn_wit; repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc.solve_keeps_cs ::=
  stn_wit;
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].

Lemma skipn_app_le : forall {A} (k : nat) (l1 l2 : list A),
  (k <= length l1)%nat -> skipn k (l1 ++ l2) = skipn k l1 ++ l2.
Proof.
  intros A k l1 l2 Hk. rewrite skipn_app. replace (k - length l1)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma skipn_app_ge : forall {A} (k : nat) (l1 l2 : list A),
  (length l1 <= k)%nat -> skipn k (l1 ++ l2) = skipn (k - length l1) l2.
Proof.
  intros A k l1 l2 Hk. rewrite skipn_app. rewrite (proj1 (skipn_all_iff k l1) Hk). reflexivity.
Qed.

Lemma u_at_le : forall (b : word) (k : Z), (0 <= k)%Z -> (bv_unsigned b + k <= 2 ^ 64)%Z ->
  bv_unsigned (at_ b k) = (bv_unsigned b + k)%Z
  \/ (bv_unsigned (at_ b k) = 0 /\ bv_unsigned b + k = 2 ^ 64)%Z.
Proof.
  intros b k Hk Hle. unfold at_. pose proof (u64_range b).
  destruct (Z.eq_dec (bv_unsigned b + k) (2 ^ 64)) as [E|NE].
  - right. split; [|exact E]. rewrite E. vm_compute. reflexivity.
  - left. u_norm. reflexivity.
Qed.

Section Loop.
  Variables (su f fd : Z) (l bufp bufsz can ret : word).
  Variables (e8 e9 e18 e19 e20 e21 e22 g3 g4 g23 g24 g25 g26 g27 : word).
  Variable mem1 : word -> option byte.
  Variable model : Model.
  Variable K : TSet.

  Hypothesis SUlo : (4294967296 + 112 <= su)%Z.
  Hypothesis SUhi : (su <= 0x800000000000)%Z.
  Hypothesis Flo : (0x31458 <= f)%Z.
  Hypothesis Fhi : (f + 232 <= 0x623c8)%Z.
  Hypothesis FD : (0 < fd < 2147483648)%Z.
  Hypothesis Hfd : fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
  Hypothesis Hrdr : m_channel_reader model = true.   (* LPS 727298f3: channel-reader premise *)
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hret : ret_ok ret.
  Hypothesis HKnil : K [].
  Hypothesis SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true.
  Hypothesis M8  : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret).
  Hypothesis M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 e8).
  Hypothesis M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 e9).
  Hypothesis M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 e18).
  Hypothesis M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 e19).
  Hypothesis M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 e20).
  Hypothesis M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 e21).
  Hypothesis M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 e22).
  Hypothesis M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can).
  Hypothesis Mcan : rdn RSEGS mem1 (Z_to_bv 64 0x623c8) 8%nat = Some (word_to_le_bytes 8 can).
  Hypothesis Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp).
  Hypothesis Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz).
  Hypothesis Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)).

  Definition LM (m : word -> option byte) : Prop :=
    (forall x : word, ~ (su - 104 <= bv_unsigned x < su - 72)%Z -> m x = mem1 x) /\ mem_grows mem1 m.

  Hypothesis HK : forall regs' m,
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = e8 -> getr regs' 9 = e9 ->
     getr regs' 18 = e18 -> getr regs' 19 = e19 -> getr regs' 20 = e20 ->
     getr regs' 21 = e21 -> getr regs' 22 = e22 -> getr regs' 23 = g23 ->
     getr regs' 24 = g24 -> getr regs' 25 = g25 -> getr regs' 26 = g26 ->
     getr regs' 27 = g27 -> getr regs' 3 = g3 -> getr regs' 4 = g4 ->
     LM m ->
     rzb RSEGS (mkCfg (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) model) K.

  Definition RI (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (su - 112) /\ getr regs 8 = l /\ getr regs 9 = Z_to_bv 64 f
    /\ getr regs 21 = Z_to_bv 64 0x623c8 /\ getr regs 3 = g3 /\ getr regs 4 = g4
    /\ getr regs 23 = g23 /\ getr regs 24 = g24 /\ getr regs 25 = g25
    /\ getr regs 26 = g26 /\ getr regs 27 = g27.

  Lemma RI_but : forall regs regs', RI regs -> sw_regs_but regs regs' -> RI regs'.
  Proof.
    (intros regs regs'; (first [ intro dR_21; dand11 dR_21 as R2 R8 R9 R21 R3 R4 R23 R24 R25 R26 R27 | intros (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27) ]); (first [ intro dR_22; dand11 dR_22 as P2 P8 P9 P21 P3 P4 P23 P24 P25 P26 P27 | intros (P2 & P8 & P9 & P21 & P3 & P4 & P23 & P24 & P25 & P26 & P27) ])).
    unfold RI. rewrite P2, P8, P9, P21, P3, P4, P23, P24, P25, P26, P27. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
  Qed.

  Lemma LM_refl : LM mem1.
  Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

  Lemma LM_rdn : forall m (a : word) n bs,
    LM m -> rdn RSEGS mem1 a n = Some bs ->
    (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
    (bv_unsigned a + Z.of_nat n <= su - 104 \/ su - 72 <= bv_unsigned a)%Z ->
    rdn RSEGS m a n = Some bs.
  Proof.
    intros m a n bs [E G] H Hnw D.
    rewrite (rdn_ext RSEGS n m mem1 a Hnw); [exact H|].
    intros x Hx. apply E. lia.
  Qed.

  Lemma LM_store_ok : forall m (a : word) n,
    LM m -> store_ok RSEGS mem1 a n = true -> store_ok RSEGS m a n = true.
  Proof. intros m a n [E G] H. eapply store_ok_mono; [exact G | exact H]. Qed.

  Lemma LM_wbytes8 : forall m (a : Z) (v : word),
    LM m -> (su - 104 <= a)%Z -> (a + 8 <= su - 72)%Z ->
    LM (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 v)).
  Proof.
    intros m a v [E G] Hlo Hhi. split.
    - intros x Hx. rewrite wbytes_outside.
      + apply E, Hx.
      + unfold in_rng. rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
      + rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - eapply mem_grows_trans; [exact G | apply wbytes_grows].
  Qed.

  Lemma finish_b : forall regs m,
    RI regs -> LM m ->
    rzb RSEGS (mkCfg (mkst regs (0x25dec : word) m (seg_rom RSEGS)) model) K.
  Proof.
    intros regs m RIr LMm.
    (first [ dand11 RIr as R2 R8 R9 R21 R3 R4 R23 R24 R25 R26 R27 | destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27) ]).
    (first [ pose proof ((sw_done regs m (seg_rom RSEGS) su f l bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22)) as dR_2; dex1 dR_2 as regs2; dand18 dR_2 as RUN Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q3 Q4 Q23 Q24 Q25 Q26 Q27 | pose proof ((sw_done regs m (seg_rom RSEGS) su f l bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22)) as dR_2; dand19 dR_2 as regs2 RUN Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q3 Q4 Q23 Q24 Q25 Q26 Q27 | destruct (sw_done regs m (seg_rom RSEGS) su f l bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22)
      as (regs2 & RUN & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q3 & Q4 & Q23 & Q24 & Q25 & Q26 & Q27) ]);
      try assumption.
    all: try (eapply LM_rdn; [exact LMm | eassumption | u_norm; lia | u_norm; lia]).
    eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
    apply HK; try assumption.
    - rewrite Q23; exact R23.
    - rewrite Q24; exact R24.
    - rewrite Q25; exact R25.
    - rewrite Q26; exact R26.
    - rewrite Q27; exact R27.
    - rewrite Q3; exact R3.
    - rewrite Q4; exact R4.
  Qed.

  Lemma finish_nil_b : forall regs m,
    RI regs -> LM m ->
    rzb RSEGS (mkCfg (mkst regs (0x25dec : word) m (seg_rom RSEGS)) model) (t_emit [] K).
  Proof. intros. apply rzb_emit_nil. apply finish_b; assumption. Qed.

  Lemma pc_25e30 : v_addi (0x25e68 : word) 4 = (0x25e6c : word).
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.

  Lemma loop1_b : forall n regs m (k : nat) (b : word) (bs : list byte),
    (length bs <= n)%nat ->
    RI regs -> LM m ->
    getr regs 10 = Z_to_bv 64 (Z.of_nat k) ->
    getr regs 22 = Z_to_bv 64 (Z.of_nat (length bs)) ->
    getr regs 18 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 (su - 88) ->
    (1 <= k < length bs)%nat ->
    rdn RSEGS m (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 b) ->
    rdn RSEGS m (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs)))) ->
    rdn RSEGS mem1 b (length bs) = Some bs ->
    (bv_unsigned b + Z.of_nat (length bs) <= su - 112 \/ su <= bv_unsigned b)%Z ->
    (bv_unsigned b + Z.of_nat (length bs) <= 0x800000000000)%Z ->   
    (Z.of_nat (length bs) <= 2 ^ 30)%Z ->   
    rzb RSEGS (mkCfg (mkst regs (0x25e78 : word) m (seg_rom RSEGS)) model)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs)) K).
  Proof.
    induction n as [|n IH]; intros regs m k b bs LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb Mb Mn Bbs DISJ NW M30.
    { exfalso. lia. }
    pose proof RIr as RIr'.
    (first [ dand11 RIr as R2 R8 R9 R21 R3 R4 R23 R24 R25 R26 R27 | destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27) ]).
    pose proof (u64_range b) as Hb.
    
    (first [ pose proof ((sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 88) 1 (Z.of_nat k)
                (Z.of_nat (length bs)) (Z.of_nat (length bs)) b)) as dR_4; dex1 dR_4 as regs1; dand10 dR_4 as RUN Q17 Q10 Q11 Q12 Q18 Q19 Q20 Q22 QB | pose proof ((sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 88) 1 (Z.of_nat k)
                (Z.of_nat (length bs)) (Z.of_nat (length bs)) b)) as dR_4; dand11 dR_4 as regs1 RUN Q17 Q10 Q11 Q12 Q18 Q19 Q20 Q22 QB | destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 88) 1 (Z.of_nat k)
                (Z.of_nat (length bs)) (Z.of_nat (length bs)) b)
      as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB) ]); try assumption; try lia.
    { eapply LM_store_ok; [exact LMm | exact SOK1]. }
    { replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact Mn. }
    { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
    eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
    replace (su - 88 + 8)%Z with (su - 80)%Z by lia.
    set (m' := wbytes (wbytes m _ _) _ _).
    assert (LMm' : LM m').
    { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
    assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
    
    eapply (rzb_writev1_wall RSEGS regs1 (0x25e68 : word) m' model W_25e68 fd
              (Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b + Z.of_nat k))
              (Z_to_bv 64 (Z.of_nat (length bs) - Z.of_nat k)) (skipn k bs) K);
      [ exact F_25e68 | exact E_25e68 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
      | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
    - subst m'. rdn_solve.
    - subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
    - rewrite word_to_nat_Z by lia.
      replace (Z.to_nat (Z.of_nat (length bs) - Z.of_nat k)) with (length bs - k)%nat by lia.
      subst m'. repeat rdn_peel1.
      change (Z_to_bv 64 (bv_unsigned b + Z.of_nat k)) with (at_ b (Z.of_nat k)).
      apply (rdn_skipn RSEGS m (length bs) b bs k); [|lia].
      eapply LM_rdn; [exact LMm | exact Bbs | lia | lia].
    - u_norm. lia.
    - u_norm. lia.
    - unfold TASK_SIZE; u_norm; lia.
    - unfold TASK_SIZE; u_norm; lia.
    - 
      intros k' K1 K2. rewrite pc_25e30. rewrite length_skipn in K2.
      destruct (Nat.eq_dec k' (length bs - k)) as [EQ|NE].
      + 
        (first [ pose proof ((sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))) as dR_5; dex1 dR_5 as regs2; dand7 dR_5 as RUN2 P10 P19 P20 P18 P22 PB | pose proof ((sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))) as dR_5; dand8 dR_5 as regs2 RUN2 P10 P19 P20 P18 P22 PB | destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB) ]).
        { gres. reflexivity. }
        { gres. rewrite Q22. f_equal. lia. }
        { lia. }
        eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        rewrite (proj1 (skipn_all_iff k' (skipn k bs))) by (rewrite length_skipn; lia).
        apply finish_nil_b; [| exact LMm'].
        eapply RI_but; [exact RI1|].
        revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
      + 
        (first [ pose proof ((sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                    (Z.of_nat (length bs) - Z.of_nat k))) as dR_6; dex1 dR_6 as regs2; dand7 dR_6 as RUN2 P10 P19 P20 P18 P22 PB | pose proof ((sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                    (Z.of_nat (length bs) - Z.of_nat k))) as dR_6; dand8 dR_6 as regs2 RUN2 P10 P19 P20 P18 P22 PB | destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                    (Z.of_nat (length bs) - Z.of_nat k))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB) ]).
        { gres. reflexivity. }
        { gres. exact Q22. }
        { lia. }
        { lia. }
        { lia. }
        eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        apply (IH regs2 m' k' (at_ b (Z.of_nat k)) (skipn k bs)).
        * rewrite length_skipn. lia.
        * eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * exact LMm'.
        * exact P10.
        * rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
        * rewrite P18. gres. exact Q18.
        * rewrite P19. gres. exact Q20.
        * rewrite length_skipn. lia.
        * subst m'. unfold at_. rdn_solve.
        * subst m'. rewrite length_skipn.
          replace (Z.of_nat (length bs - k)) with (Z.of_nat (length bs) - Z.of_nat k)%Z by lia. rdn_solve.
        * rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs) b bs k); [exact Bbs|lia].
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * rewrite length_skipn. lia.
  Qed.

  Lemma loop2_b : forall n regs m (k : nat) (b0 : word) (bs0 : list byte) (b1 : word) (bs1 : list byte),
    (length bs0 + length bs1 <= n)%nat ->
    RI regs -> LM m ->
    getr regs 10 = Z_to_bv 64 (Z.of_nat k) ->
    getr regs 22 = Z_to_bv 64 (Z.of_nat (length bs0) + Z.of_nat (length bs1)) ->
    getr regs 18 = Z_to_bv 64 2 -> getr regs 19 = Z_to_bv 64 (su - 104) ->
    (1 <= k < length bs0 + length bs1)%nat ->
    rdn RSEGS m (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 b0) ->
    rdn RSEGS m (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs0)))) ->
    rdn RSEGS m (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 b1) ->
    rdn RSEGS m (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs1)))) ->
    rdn RSEGS mem1 b0 (length bs0) = Some bs0 ->
    rdn RSEGS mem1 b1 (length bs1) = Some bs1 ->
    (bv_unsigned b0 + Z.of_nat (length bs0) <= su - 112 \/ su <= bv_unsigned b0)%Z ->
    (bv_unsigned b0 + Z.of_nat (length bs0) <= 0x800000000000)%Z ->
    (bv_unsigned b1 + Z.of_nat (length bs1) <= su - 112 \/ su <= bv_unsigned b1)%Z ->
    (bv_unsigned b1 + Z.of_nat (length bs1) <= 0x800000000000)%Z ->
    (Z.of_nat (length bs0) + Z.of_nat (length bs1) <= 2 ^ 30)%Z ->
    rzb RSEGS (mkCfg (mkst regs (0x25e78 : word) m (seg_rom RSEGS)) model)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs0 ++ bs1))) K).
  Proof.
    induction n as [|n IH]; intros regs m k b0 bs0 b1 bs1 LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb
      Mb0 Mn0 Mb1 Mn1 Bbs0 Bbs1 DISJ0 NW0 DISJ1 NW1 M30.
    { exfalso. lia. }
    pose proof RIr as RIr'.
    (first [ dand11 RIr as R2 R8 R9 R21 R3 R4 R23 R24 R25 R26 R27 | destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27) ]).
    pose proof (u64_range b0) as Hb0. pose proof (u64_range b1) as Hb1.
    destruct (Nat.le_gt_cases k (length bs0)) as [LE|GT].
    - 
      (first [ pose proof ((sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 104) 2 (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b0)) as dR_8; dex1 dR_8 as regs1; dand10 dR_8 as RUN Q17 Q10 Q11 Q12 Q18 Q19 Q20 Q22 QB | pose proof ((sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 104) 2 (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b0)) as dR_8; dand11 dR_8 as regs1 RUN Q17 Q10 Q11 Q12 Q18 Q19 Q20 Q22 QB | destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 104) 2 (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b0)
        as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB) ]); try assumption; try lia.
      { eapply LM_store_ok; [exact LMm | exact SOK1]. }
      { replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
      { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
      eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
      replace (su - 104 + 8)%Z with (su - 96)%Z by lia.
      set (m' := wbytes (wbytes m _ _) _ _).
      assert (LMm' : LM m').
      { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
      assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
      rewrite (skipn_app_le k bs0 bs1 LE).
      eapply (rzb_writev2_wall RSEGS regs1 (0x25e68 : word) m' model W_25e68 fd
                (Z_to_bv 64 (su - 104)) (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k))
                (Z_to_bv 64 (Z.of_nat (length bs0) - Z.of_nat k))
                b1 (Z_to_bv 64 (Z.of_nat (length bs1))) (skipn k bs0) bs1 K);
        [ exact F_25e68 | exact E_25e68 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
        | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | | | | | exact HKnil | ].
      + subst m'. rdn_solve.
      + subst m'. u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. rdn_solve.
      + subst m'. u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. repeat rdn_peel1. exact Mb1.
      + subst m'. u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. repeat rdn_peel1. exact Mn1.
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs0) - Z.of_nat k)) with (length bs0 - k)%nat by lia.
        destruct (Nat.eq_dec k (length bs0)) as [EK|NK].
        { replace (length bs0 - k)%nat with 0%nat by lia.
          rewrite (proj1 (skipn_all_iff k bs0)) by lia. reflexivity. }
        subst m'. repeat rdn_peel1.
        change (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k)) with (at_ b0 (Z.of_nat k)).
        apply (rdn_skipn RSEGS m (length bs0) b0 bs0 k); [|lia].
        eapply LM_rdn; [exact LMm | exact Bbs0 | lia | lia].
      + rewrite word_to_nat_Z by lia. rewrite Nat2Z.id.
        subst m'. repeat rdn_peel1.
        eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
      + u_norm. lia.
      + u_norm. lia.
      + unfold TASK_SIZE; u_norm; lia.
      + unfold TASK_SIZE; u_norm; lia.
      + unfold TASK_SIZE; u_norm; lia.
      + intros k' K1 K2. rewrite pc_25e30. rewrite length_app, length_skipn in K2.
        destruct (Nat.eq_dec k' (length bs0 - k + length bs1)) as [EQ|NE].
        * (first [ pose proof ((sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))) as dR_9; dex1 dR_9 as regs2; dand7 dR_9 as RUN2 P10 P19 P20 P18 P22 PB | pose proof ((sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))) as dR_9; dand8 dR_9 as regs2 RUN2 P10 P19 P20 P18 P22 PB | destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB) ]).
          { gres. reflexivity. }
          { gres. rewrite Q22. f_equal. lia. }
          { lia. }
          eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          rewrite (proj1 (skipn_all_iff k' (skipn k bs0 ++ bs1))) by (rewrite length_app, length_skipn; lia).
          apply finish_nil_b; [| exact LMm'].
          eapply RI_but; [exact RI1|].
          revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * (first [ pose proof ((sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))) as dR_10; dex1 dR_10 as regs2; dand7 dR_10 as RUN2 P10 P19 P20 P18 P22 PB | pose proof ((sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))) as dR_10; dand8 dR_10 as regs2 RUN2 P10 P19 P20 P18 P22 PB | destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB) ]).
          { gres. reflexivity. }
          { gres. exact Q22. }
          { lia. }
          { lia. }
          { lia. }
          eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          apply (IH regs2 m' k' (at_ b0 (Z.of_nat k)) (skipn k bs0) b1 bs1).
          -- rewrite length_skipn. lia.
          -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
          -- exact LMm'.
          -- exact P10.
          -- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
          -- rewrite P18. gres. exact Q18.
          -- rewrite P19. gres. exact Q20.
          -- rewrite length_skipn. lia.
          -- subst m'. unfold at_. rdn_solve.
          -- subst m'. rewrite length_skipn.
             replace (Z.of_nat (length bs0 - k)) with (Z.of_nat (length bs0) - Z.of_nat k)%Z by lia. rdn_solve.
          -- subst m'. repeat rdn_peel1. exact Mb1.
          -- subst m'. repeat rdn_peel1. exact Mn1.
          -- rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs0) b0 bs0 k); [exact Bbs0|lia].
          -- exact Bbs1.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- exact DISJ1.
          -- exact NW1.
          -- rewrite length_skipn. lia.
    - 
      (first [ pose proof ((sw_retry_b regs m (seg_rom RSEGS) su f fd (su - 104) (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs1))
                  (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b1)) as dR_11; dex1 dR_11 as regs1; dand10 dR_11 as RUN Q17 Q10 Q11 Q12 Q18 Q19 Q20 Q22 QB | pose proof ((sw_retry_b regs m (seg_rom RSEGS) su f fd (su - 104) (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs1))
                  (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b1)) as dR_11; dand11 dR_11 as regs1 RUN Q17 Q10 Q11 Q12 Q18 Q19 Q20 Q22 QB | destruct (sw_retry_b regs m (seg_rom RSEGS) su f fd (su - 104) (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs1))
                  (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b1)
        as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB) ]); try assumption; try lia.
      { eapply LM_store_ok; [exact LMm | exact SOK1]. }
      { replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
      { replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact Mb1. }
      { replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact Mn1. }
      { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
      eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
      replace (su - 104 + 16)%Z with (su - 88)%Z in * by lia.
      replace (su - 104 + 24)%Z with (su - 80)%Z by lia.
      replace (Z.of_nat k - Z.of_nat (length bs0))%Z with (Z.of_nat (k - length bs0)) by lia.
      set (m' := wbytes (wbytes m _ _) _ _).
      assert (LMm' : LM m').
      { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
      assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
      rewrite (skipn_app_ge k bs0 bs1) by lia.
      eapply (rzb_writev1_wall RSEGS regs1 (0x25e68 : word) m' model W_25e68 fd
                (Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0)))
                (Z_to_bv 64 (Z.of_nat (length bs1) - Z.of_nat (k - length bs0)))
                (skipn (k - length bs0) bs1) K);
        [ exact F_25e68 | exact E_25e68 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
        | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | unfold TASK_SIZE; u_norm; lia | unfold TASK_SIZE; u_norm; lia | exact HKnil | ].
      + subst m'. rdn_solve.
      + subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))) with (length bs1 - (k - length bs0))%nat by lia.
        subst m'. repeat rdn_peel1.
        change (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0))) with (at_ b1 (Z.of_nat (k - length bs0))).
        apply (rdn_skipn RSEGS m (length bs1) b1 bs1 (k - length bs0)); [|lia].
        eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
      + u_norm. lia.
      + u_norm. lia.
      + intros k' K1 K2. rewrite pc_25e30. rewrite length_skipn in K2.
        destruct (Nat.eq_dec k' (length bs1 - (k - length bs0))) as [EQ|NE].
        * (first [ pose proof ((sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))) as dR_12; dex1 dR_12 as regs2; dand7 dR_12 as RUN2 P10 P19 P20 P18 P22 PB | pose proof ((sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))) as dR_12; dand8 dR_12 as regs2 RUN2 P10 P19 P20 P18 P22 PB | destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB) ]).
          { gres. reflexivity. }
          { gres. rewrite Q22. f_equal. lia. }
          { lia. }
          eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          rewrite (proj1 (skipn_all_iff k' (skipn (k - length bs0) bs1))) by (rewrite length_skipn; lia).
          apply finish_nil_b; [| exact LMm'].
          eapply RI_but; [exact RI1|].
          revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * (first [ pose proof ((sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))) as dR_13; dex1 dR_13 as regs2; dand7 dR_13 as RUN2 P10 P19 P20 P18 P22 PB | pose proof ((sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))) as dR_13; dand8 dR_13 as regs2 RUN2 P10 P19 P20 P18 P22 PB | destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB) ]).
          { gres. reflexivity. }
          { gres. exact Q22. }
          { lia. }
          { lia. }
          { lia. }
          eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          apply (loop1_b (length bs1) regs2 m' k' (at_ b1 (Z.of_nat (k - length bs0))) (skipn (k - length bs0) bs1)).
          -- rewrite length_skipn. lia.
          -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
          -- exact LMm'.
          -- exact P10.
          -- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
          -- rewrite P18. gres. exact Q18.
          -- rewrite P19. gres. exact Q20.
          -- rewrite length_skipn. lia.
          -- subst m'. unfold at_. rdn_solve.
          -- subst m'. rewrite length_skipn.
             replace (Z.of_nat (length bs1 - (k - length bs0))) with (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))%Z by lia.
             rdn_solve.
          -- rewrite length_skipn.
             apply (rdn_skipn RSEGS mem1 (length bs1) b1 bs1 (k - length bs0)); [exact Bbs1|lia].
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- rewrite length_skipn. lia.
  Qed.

End Loop.

Ltac wout1 :=
  rewrite wbytes_outside;
  [ | unfold in_rng; rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia
    | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia ].

Lemma sw_post_of_LM : forall mem m (su f : Z) (ra s0 s1 s2 s3 s4 s5 s6 can : word) (wb n : Z) (s l bufp bufsz : word),
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0x31458 <= f)%Z -> (f + 232 <= 0x623c8)%Z ->
  LM su (mem_sw1 mem su ra s0 s1 s2 s3 s4 s5 s6 can wb n s l) m ->
  sw_post mem su f bufp bufsz (mem_sw2 m f bufp bufsz).
Proof.
  intros mem m su f ra s0 s1 s2 s3 s4 s5 s6 can wb n s l bufp bufsz SUlo SUhi Flo Fhi [E G].
  constructor.
  - intros x Hx1 Hx2 Hx3. pose proof (u64_range x) as Hx.
    unfold mem_sw2. do 3 wout1.
    rewrite (E x) by lia.
    unfold mem_sw1. do 13 wout1. reflexivity.
  - unfold mem_sw2. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
    eapply mem_grows_trans; [|exact G].
    unfold mem_sw1. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
    apply mem_grows_refl.
  - unfold mem_sw2. rdn_solve.
  - unfold mem_sw2. rdn_solve.
  - unfold mem_sw2. rdn_solve.
Qed.

Lemma pc_25da8 : v_addi (0x25de0 : word) 4 = (0x25de4 : word).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Theorem ref_stdio_write_b :
  forall regs mem model (su f wb wp fd : Z) (s l bufp bufsz can ret : word)
         (pending extra : list byte) (K : TSet),
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  (0x31458 <= f)%Z -> (f + 232 <= 0x623c8)%Z ->
  sw_file mem f wb wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (0 <= wb <= wp)%Z -> (wp <= 0x800000000000)%Z ->   
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->   
  rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS mem s (length extra) = Some extra ->
  ret_ok ret ->
  K [] ->
  (forall regs' mem',
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
     getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
     getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
     getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     sw_post mem su f bufp bufsz mem' ->
     rzb RSEGS (mkCfg (mkst regs' ret mem' (seg_rom RSEGS)) model) K) ->
  rzb RSEGS (mkCfg (mkst regs (0x25d58 : word) mem (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
Proof.
  intros regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi SWF SSP FD Hfd Hrdr Hh Hlazy WBP WPhi
         LENP LENE M30 DISJP DISJE SNW RDP RDE Hret HKnil HK.
  pose proof (u64_range s) as Hs. pose proof (u64_range l) as Hl.
  pose proof SWF as SWF'. pose proof SSP as SSP'.
  destruct SWF as [Fwp Fwb Ffd Fbuf Fbsz]. destruct SSP as [Ggot Gcan].
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  assert (HlZ : l = Z_to_bv 64 (Z.of_nat (length extra))).
  { rewrite <- LENE. symmetry. apply u64_roundtrip'. }
  
  set (mem1 := mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                       (getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l).
  assert (SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true).
  { subst mem1; unfold mem_sw1. store_ok_peel. exact SOK. }
  assert (M8 : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs 20))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs 21))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs 22))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M104 : rdn RSEGS mem1 (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M96 : rdn RSEGS mem1 (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (wp - wb)))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M88 : rdn RSEGS mem1 (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 s)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M80 : rdn RSEGS mem1 (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 l)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mcan : rdn RSEGS mem1 (Z_to_bv 64 0x623c8) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Bp : rdn RSEGS mem1 (Z_to_bv 64 wb) (length pending) = Some pending).
  { subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDP. }
  assert (Be : rdn RSEGS mem1 s (length extra) = Some extra).
  { subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDE. }
  
  assert (HK' : forall regs' m,
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
     getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
     getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
     getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     LM su mem1 m ->
     rzb RSEGS (mkCfg (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) model) K).
  { intros. apply HK. all: try assumption.
    eapply sw_post_of_LM; [exact SUlo | exact SUhi | exact Flo | exact Fhi | ].
    match goal with H : LM _ _ _ |- _ => exact H end. }
  pose proof (finish_nil_b su f l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
                SUlo SUhi Flo Fhi Hh Hlazy Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK') as FIN.
  pose proof (loop1_b su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
                SUlo SUhi Flo Fhi FD Hfd Hrdr Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L1.
  pose proof (loop2_b su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
                SUlo SUhi Flo Fhi FD Hfd Hrdr Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L2.
  pose proof (LM_refl su mem1) as LM1.
  destruct (Z.eq_dec wb wp) as [EQ|NEQ].
  - 
    destruct pending as [|p0 pending']; [| cbn [length] in LENP; lia]. cbn [app].
    subst wb.
    (first [ pose proof ((sw_enter_eq regs mem (seg_rom RSEGS) su f wp fd s l bufp bufsz can ret)) as dR_14; dex1 dR_14 as regs1; dand19 dR_14 as RUN1 R17 R10 R11 R12 R2 R8 R9 R18 R19 R21 R22 R3 R4 R23 R24 R25 R26 R27 | pose proof ((sw_enter_eq regs mem (seg_rom RSEGS) su f wp fd s l bufp bufsz can ret)) as dR_14; dand20 dR_14 as regs1 RUN1 R17 R10 R11 R12 R2 R8 R9 R18 R19 R21 R22 R3 R4 R23 R24 R25 R26 R27 | destruct (sw_enter_eq regs mem (seg_rom RSEGS) su f wp fd s l bufp bufsz can ret)
      as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27) ]);
      try assumption; try lia.
    eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    lazymatch goal with |- rzb _ (mkCfg (mkst _ _ ?M _) _) _ =>
      replace M with mem1 by (subst mem1; rewrite Z.sub_diag; reflexivity) end.
    rewrite Z.sub_diag in M96.
    assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
                     (getr regs 26) (getr regs 27) regs1).
    { unfold RI. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption. }
    destruct extra as [|x0 extra'].
    + 
      cbn [length] in HlZ. change (Z.of_nat 0) with 0%Z in HlZ. cbn [map].
      eapply (rzb_writev1_zero RSEGS regs1 (0x25de0 : word) mem1 model W_25de0 fd (Z_to_bv 64 (su - 88)) s (t_emit [] K));
        [ exact F_25de0 | exact E_25de0 | exact Hh | exact Hlazy | exact Hfd | exact FD
        | exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | apply rw_bytes_max_nonneg | unfold TASK_SIZE; u_norm; lia | unfold TASK_SIZE; u_norm; lia | ].
      { u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rewrite <- HlZ. exact M80. }
      rewrite pc_25da8.
      (first [ pose proof ((sw_c1_eq (regupd regs1 10 (Z_to_bv 64 0)) mem1 (seg_rom RSEGS) 0)) as dR_15; dex1 dR_15 as regs2; dand7 dR_15 as RUN2 P10 P19 P20 P18 P22 PB | pose proof ((sw_c1_eq (regupd regs1 10 (Z_to_bv 64 0)) mem1 (seg_rom RSEGS) 0)) as dR_15; dand8 dR_15 as regs2 RUN2 P10 P19 P20 P18 P22 PB | destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 0)) mem1 (seg_rom RSEGS) 0)
        as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB) ]).
      { gres. reflexivity. }
      { gres. rewrite R22. exact HlZ. }
      { lia. }
      eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
      apply FIN; [|exact LM1].
      eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
    + 
      eapply (rzb_writev1_wall RSEGS regs1 (0x25de0 : word) mem1 model W_25de0 fd
                (Z_to_bv 64 (su - 88)) s l (x0 :: extra') K);
        [ exact F_25de0 | exact E_25de0 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
        | exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | | | | | | exact HKnil | ].
      * u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact M80.
      * unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
      * cbn [length] in LENE. lia.
      * lia.
      * unfold TASK_SIZE; u_norm; lia.
      * unfold TASK_SIZE; u_norm; lia.
      * intros k K1 K2. rewrite pc_25da8.
        destruct (Nat.eq_dec k (length (x0 :: extra'))) as [EK|NK].
        -- (first [ pose proof ((sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))) as dR_16; dex1 dR_16 as regs2; dand7 dR_16 as RUN2 P10 P19 P20 P18 P22 PB | pose proof ((sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))) as dR_16; dand8 dR_16 as regs2 RUN2 P10 P19 P20 P18 P22 PB | destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
             as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB) ]).
           { gres. reflexivity. }
           { gres. rewrite R22, HlZ. f_equal. lia. }
           { lia. }
           eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
           rewrite (proj1 (skipn_all_iff k (x0 :: extra'))) by lia. cbn [map].
           apply FIN; [|exact LM1].
           eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        -- (first [ pose proof ((sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                       (Z.of_nat (length (x0 :: extra'))))) as dR_17; dex1 dR_17 as regs2; dand7 dR_17 as RUN2 P10 P19 P20 P18 P22 PB | pose proof ((sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                       (Z.of_nat (length (x0 :: extra'))))) as dR_17; dand8 dR_17 as regs2 RUN2 P10 P19 P20 P18 P22 PB | destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                       (Z.of_nat (length (x0 :: extra'))))
             as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB) ]).
           { gres. reflexivity. }
           { gres. rewrite R22, HlZ. reflexivity. }
           { lia. }
           { lia. }
           { lia. }
           eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
           apply (L1 (length (x0 :: extra')) regs2 mem1 k s (x0 :: extra')); try lia.
           ++ eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
           ++ exact LM1.
           ++ exact P10.
           ++ rewrite P22. gres. rewrite R22, HlZ. reflexivity.
           ++ rewrite P18. gres. exact R18.
           ++ rewrite P19. gres. exact R19.
           ++ exact M88.
           ++ rewrite <- HlZ. exact M80.
           ++ exact Be.
  - 
    (first [ pose proof ((sw_enter regs mem (seg_rom RSEGS) su f wb wp fd s l bufp bufsz can ret)) as dR_18; dex1 dR_18 as regs1; dand19 dR_18 as RUN1 R17 R10 R11 R12 R2 R8 R9 R18 R19 R21 R22 R3 R4 R23 R24 R25 R26 R27 | pose proof ((sw_enter regs mem (seg_rom RSEGS) su f wb wp fd s l bufp bufsz can ret)) as dR_18; dand20 dR_18 as regs1 RUN1 R17 R10 R11 R12 R2 R8 R9 R18 R19 R21 R22 R3 R4 R23 R24 R25 R26 R27 | destruct (sw_enter regs mem (seg_rom RSEGS) su f wb wp fd s l bufp bufsz can ret)
      as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27) ]);
      try assumption; try lia.
    eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1. fold mem1.
    assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
                     (getr regs 26) (getr regs 27) regs1).
    { unfold RI. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption. }
    eapply (rzb_writev2_wall RSEGS regs1 (0x25de0 : word) mem1 model W_25de0 fd
              (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) (Z_to_bv 64 (wp - wb)) s l pending extra K);
      [ exact F_25de0 | exact E_25de0 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
      | exact R17 | exact R10 | exact R11 | exact R12 | exact M104 | | | | | | | | | | | exact HKnil | ].
    + u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact M96.
    + u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact M88.
    + u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact M80.
    + rewrite word_to_nat_Z by lia. replace (Z.to_nat (wp - wb)) with (length pending) by lia. exact Bp.
    + unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
    + u_norm. lia.
    + u_norm. lia.
    + unfold TASK_SIZE; u_norm; lia.
    + unfold TASK_SIZE; u_norm; lia.
    + unfold TASK_SIZE; u_norm; lia.
    + intros k K1 K2. rewrite pc_25da8. rewrite length_app in K2.
      destruct (Nat.eq_dec k (length pending + length extra)) as [EK|NK].
      * (first [ pose proof ((sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))) as dR_19; dex1 dR_19 as regs2; dand7 dR_19 as RUN2 P10 P19 P20 P18 P22 PB | pose proof ((sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))) as dR_19; dand8 dR_19 as regs2 RUN2 P10 P19 P20 P18 P22 PB | destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB) ]).
        { gres. reflexivity. }
        { gres. rewrite R22. f_equal. lia. }
        { lia. }
        eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        rewrite (proj1 (skipn_all_iff k (pending ++ extra))) by (rewrite length_app; lia). cbn [map].
        apply FIN; [|exact LM1].
        eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
      * (first [ pose proof ((sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                    (wp - wb + bv_unsigned l))) as dR_20; dex1 dR_20 as regs2; dand7 dR_20 as RUN2 P10 P19 P20 P18 P22 PB | pose proof ((sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                    (wp - wb + bv_unsigned l))) as dR_20; dand8 dR_20 as regs2 RUN2 P10 P19 P20 P18 P22 PB | destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                    (wp - wb + bv_unsigned l))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB) ]).
        { gres. reflexivity. }
        { gres. exact R22. }
        { lia. }
        { lia. }
        { lia. }
        eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        apply (L2 (length pending + length extra)%nat regs2 mem1 k (Z_to_bv 64 wb) pending s extra); try lia.
        -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        -- exact LM1.
        -- exact P10.
        -- rewrite P22. gres. rewrite R22. f_equal. lia.
        -- rewrite P18. gres. exact R18.
        -- rewrite P19. gres. exact R19.
        -- exact M104.
        -- replace (Z.of_nat (length pending)) with (wp - wb)%Z by lia. exact M96.
        -- exact M88.
        -- rewrite <- HlZ. exact M80.
        -- exact Bp.
        -- exact Be.
        -- u_norm. lia.
        -- u_norm. lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
