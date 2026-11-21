(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from D_Exit.v: the exit walk (ref_exit, ref_exit_Z) restated over BudgetWit.Rzb.rzb *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the exit lemmas take the channel-reader premise (m_channel_reader) the model's new write arms read. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg Nodes Spec LibWbxd D_Stqgu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import D_Exit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_St8vg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_St8vg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_St8vg D_co4d2 D_coj29.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Amb.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Stre9ts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibAvhx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibWbxd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Stqgu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Exit.D_Exnq5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Exit.D_Ex8ka OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Exit.D_Ex1il OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_St8vg.D_St0rr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_St8vg.D_St7f8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_St8vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_co4d2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_coj29 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Amb.D_co2af.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
Import ListNotations.

Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.

Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.BudgetWit Require Import Rzb Agenxn8B NodesB LibWbxdB RefNodesB D_St8vgB.

Ltac zaddr_rec H := zaddr H.

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
Local Ltac stn_open := repeat match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end.
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

Theorem ref_exit_clean_b :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word) (reg : bool),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  atexit_st mem reg ->
  file_clean mem 0x31698 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  rzb RSEGS (mkCfg (mkst regs (0x2299c : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 reg EC AT F1 Hh Hlazy.
  destruct EC.
  (first [ dand5 ec_glob as Gnl Gofl Gin Gout Gerr | destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr) ]).
  
  destruct (w1 regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1 & R1s2 & R1s3);
    try assumption.
  eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  
  destruct (wF regs1 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) (seg_rom RSEGS) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19) reg)
    as (regsF & RUNF & RFsp & RFs0 & RFra & RFs1 & RFtp & RFgp); try assumption; try reflexivity.
  all: try (unfold mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
  1:{ destruct reg; unfold atexit_st in AT |- *;
      [ destruct AT as (Ahead & Aslot & Af0 & Aa0 & Anext & Aincb); OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit | ];
      unfold mem_w1; rdn_solve. }
  eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUNF |]. clear RUNF.
  
  destruct (w2 regsF (mem_wF (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19) reg) (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (destruct reg; unfold mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
  eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  
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
  eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  
  eapply rzb_exit_at; [exact F_22774 | exact E_22774 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.

Theorem ref_exit_flush_b :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte) (reg : bool),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  atexit_st mem reg ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  m_channel_reader model = true ->   (* LPS 727298f3: channel-reader premise *)
  rzb RSEGS (mkCfg (mkst regs (0x2299c : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending reg EC AT SP Hh Hlazy Hfd Hrdr.
  destruct EC.
  (first [ dand5 ec_glob as Gnl Gofl Gin Gout Gerr | destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr) ]). destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  
  destruct (w1 regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1 & R1s2 & R1s3);
    try assumption.
  eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  
  destruct (wF regs1 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) (seg_rom RSEGS) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19) reg)
    as (regsF & RUNF & RFsp & RFs0 & RFra & RFs1 & RFtp & RFgp); try assumption; try reflexivity.
  all: try (unfold mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
  1:{ destruct reg; unfold atexit_st in AT |- *;
      [ destruct AT as (Ahead & Aslot & Af0 & Aa0 & Anext & Aincb); OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit | ];
      unfold mem_w1; rdn_solve. }
  eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUNF |]. clear RUNF.
  
  destruct (w2 regsF (mem_wF (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19) reg) (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (destruct reg; unfold mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
  eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  
  (first [ pose proof ((w3b1 regs2 (mem_w2 (mem_wF (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19) reg) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wb wp)) as dR_10; dex1 dR_10 as regs3; dand9 dR_10 as RUN3 R3a0 R3a1 R3a2 R3ra R3sp R3s0 R3gp R3tp | pose proof ((w3b1 regs2 (mem_w2 (mem_wF (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19) reg) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wb wp)) as dR_10; dand10 dR_10 as regs3 RUN3 R3a0 R3a1 R3a2 R3ra R3sp R3s0 R3gp R3tp | destruct (w3b1 regs2 (mem_w2 (mem_wF (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19) reg) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wb wp)
    as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp) ]); try assumption; try lia.
  1:{ destruct reg; unfold mem_w2, mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; store_ok_peel; exact ec_sok. }
  1:{ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; destruct reg; unfold mem_w2, mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; rdn_solve. }
  1:{ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; destruct reg; unfold mem_w2, mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; zaddr_goal; rdn_solve. }
  eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  
  replace (Z_to_bv 64 0x25b98) with (0x25b98 : word) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a (mem_w2 (mem_wF (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19) reg) sp code (getr regs1 9)) sp code).
  eapply (ref_stdio_write_b regs3 mem3 model (bv_unsigned sp - 32) 0x31698 wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x25b98 : word) pending []);
    [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
    | lia | lia
    | 
      subst mem3; destruct reg; unfold mem_w3a, mem_w2, mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; sok_stack ec_sok
    | lia | lia
    |  split; subst mem3; destruct reg; unfold mem_w3a, mem_w2, mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; zaddr_goal; rdn_solve
    |  split; subst mem3; destruct reg; unfold mem_w3a, mem_w2, mem_wF, mem_wFR, mem_wFN, mem_wF0, mem_w1; rdn_solve
    | lia | exact Hfd | exact Hrdr | exact Hh | exact Hlazy
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
    eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
    eapply rzb_exit_at; [exact F_22774 | exact E_22774 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.

Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

Theorem ref_exit_b : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  rzb RSEGS (mkCfg (mkst regs (0x2299c : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & reg & EC & AT & Hh & Hlazy & CASES).
  destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd & Hrdr)].
  - eapply rzb_conseq; [ | apply t_emit_nil_exit ].
    eapply ref_exit_clean_b; eassumption.
  - eapply ref_exit_flush_b; eassumption.
Qed.

Corollary ref_exit_Z_b : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  rzb RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2299c) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x2299c) with (0x2299c : word) by (apply bv_eq; reflexivity).
  apply ref_exit_b; assumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
