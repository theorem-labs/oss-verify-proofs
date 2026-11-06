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
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Star5ef ArgvEnv RefL1zx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RefL1zx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_co77 DU_cb3t DU_cij8.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ArgvEnv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefL1zx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefL1zx.DU_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_co77 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_cb3t OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_cij8.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.

Module DU_T9tr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WalkTac DU_co77.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_co77.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Theorem tr_call : forall regs mem rom,
  getr regs 20 = Z_to_bv 64 0x41ba0 ->
  store_ok RSEGS mem (Z_to_bv 64 0x41ba4) 1%nat = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x17f20 : word) mem rom)
                 (mkst regs' (0x1807c : word) (wbytes mem (Z_to_bv 64 0x41ba4) [Z_to_bv 8 1]) rom)
    /\ getr regs' 10 = getr regs 9
    /\ getr regs' 11 = getr regs 8
    /\ getr regs' 1 = Z_to_bv 64 0x17f34
    /\ (forall r : reg, r <> 1 -> r <> 10 -> r <> 11 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom H20 SOK. eexists. split.
  - stepn F_17f20 D_17f20.
    chain_step; [reflexivity
      | eapply MmapSim.step_sb_at with (a := Z_to_bv 64 0x41ba4) (v := Z_to_bv 64 1);
        [ exact F_17f24 | reflexivity | exact D_17f24 | gres; imm_norm; rewrite H20; apply bv_eq; reflexivity
        | gres; reflexivity | reflexivity | exact SOK ]
      | step_simpl ].
    stepn F_17f28 D_17f28.
    stepn F_17f2c D_17f2c.
    stepn F_17f30 D_17f30.
    apply mst_refl.
  - OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; try reflexivity.
    intros r H1 H10 H11. rewrite !getr_other by assumption. reflexivity.
Qed.

Theorem tr_pf : forall regs mem rom,
  getr regs 20 = Z_to_bv 64 0x41ba0 ->
  store_ok RSEGS mem (Z_to_bv 64 0x41ba4) 1%nat = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x17f34 : word) mem rom)
                 (mkst regs' (0x17ff0 : word) (wbytes mem (Z_to_bv 64 0x41ba4) [Z_to_bv 8 0]) rom)
    /\ getr regs' 19 = getr regs 10
    /\ getr regs' 11 = getr regs 10
    /\ getr regs' 1 = Z_to_bv 64 0x17f44
    /\ (forall r : reg, r <> 1 -> r <> 19 -> r <> 11 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom H20 SOK. eexists. split.
  - stepn F_17f34 D_17f34.
    chain_step; [reflexivity
      | eapply MmapSim.step_sb_at with (a := Z_to_bv 64 0x41ba4) (v := Z_to_bv 64 0);
        [ exact F_17f38 | reflexivity | exact D_17f38 | gres; imm_norm; rewrite H20; apply bv_eq; reflexivity
        | gres; first [reflexivity | apply getr_zero] | reflexivity | exact SOK ]
      | step_simpl ].
    stepn F_17f3c D_17f3c.
    stepn F_17f40 D_17f40.
    apply mst_refl.
  - OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; try reflexivity.
    intros r H1 H19 H11. rewrite !getr_other by assumption. reflexivity.
Qed.

Lemma v_addiw_dec : forall j : nat, (Z.of_nat j < 1000)%Z ->
  v_addiw (Z_to_bv 64 (Z.of_nat (S j))) (-1) = Z_to_bv 64 (Z.of_nat j).
Proof.
  intros j Hj. apply bv_eq. unfold v_addiw. rewrite !Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 (Z.of_nat (S j))) by (change (bv_modulus 64) with (2^64)%Z; lia).
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  rewrite !bv_wrap_small by (change (bv_modulus 64) with (2^64)%Z; lia). lia.
Qed.

(* [comment removed for export] *)
Theorem tr_dec : forall regs mem rom (j : nat),
  getr regs 21 = Z_to_bv 64 (Z.of_nat (S j)) -> (Z.of_nat j < 1000)%Z ->
  getr regs 19 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 18446744073709551614 ->
  exists regs',
    msteps RSEGS (mkst regs (0x17f44 : word) mem rom)
                 (mkst regs' ((if Nat.eqb j 0 then 0x17f58 else 0x17f20) : word) mem rom)
    /\ getr regs' 21 = Z_to_bv 64 (Z.of_nat j)
    /\ (forall r : reg, r <> 19 -> r <> 21 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom j H21 Hj H19 H23.
  destruct (Nat.eqb_spec j 0) as [->|Hne].
  - eexists. split.
    + stepiwv F_17f44 D_17f44 (Z_to_bv 64 18446744073709551615) ltac:(gres; imm_norm; rewrite H19; apply bv_eq; vm_compute; reflexivity).
      stepb_tk F_17f48 D_17f48 ltac:(gres; rewrite H23; cond_compute).
      stepiwv F_17f50 D_17f50 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite H21; apply (v_addiw_dec 0); lia).
      stepb_ft F_17f54 D_17f54 ltac:(gres; cond_compute).
      apply mst_refl.
    + split; [gres; reflexivity|]. intros r Ha Hb. rewrite !getr_other by assumption. reflexivity.
  - eexists. split.
    + stepiwv F_17f44 D_17f44 (Z_to_bv 64 18446744073709551615) ltac:(gres; imm_norm; rewrite H19; apply bv_eq; vm_compute; reflexivity).
      stepb_tk F_17f48 D_17f48 ltac:(gres; rewrite H23; cond_compute).
      stepiwv F_17f50 D_17f50 (Z_to_bv 64 (Z.of_nat j)) ltac:(gres; imm_norm; rewrite H21; apply v_addiw_dec; lia).
      stepb_tk F_17f54 D_17f54 ltac:(gres; apply c_eq_0_false; rewrite u_Z2bv by lia; lia).
      apply mst_refl.
    + split; [gres; reflexivity|]. intros r Ha Hb. rewrite !getr_other by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem tr_c : forall regs mem rom,
  exists regs',
    msteps RSEGS (mkst regs (0x17ee0 : word) mem rom) (mkst regs' (0x17f20 : word) mem rom)
    /\ getr regs' 9 = getr regs 18
    /\ getr regs' 22 = Z_to_bv 64 0
    /\ getr regs' 23 = Z_to_bv 64 18446744073709551614
    /\ (forall r : reg, r <> 9 -> r <> 22 -> r <> 23 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom. eexists. split.
  - stepn F_17ee0 D_17ee0.
    stepn F_17ee4 D_17ee4.
    stepv F_17f18 D_17f18 (Z_to_bv 64 0).
    stepv F_17f1c D_17f1c (Z_to_bv 64 18446744073709551614).
    apply mst_refl.
  - OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; try reflexivity.
    intros r H9 H22 H23. rewrite !getr_other by assumption. reflexivity.
Qed.
End DU_T9tr.


(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Definition regs_init (sp0 : word) : bvmap 5 word :=
  regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp0.

(* [comment removed for export] *)
Definition stn_mark {A : Type} (x : A) : Prop := True.
Definition stn_markm {A : Type} (x : A) : Prop := True.      (* [comment removed for export] *)
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
Local Ltac stn_open := repeat match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end.
Local Ltac stn_done :=
  repeat first [ match goal with H : stn_mark ?x |- ?g => lazymatch g with context [x] => unfold x end end
               | match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end ];
  try lazymatch goal with E : ?s = _ |- msteps _ _ ?s => rewrite E end.
Local Ltac stn_demand1 :=
  match goal with
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef.peel ::=
  repeat first [ rewrite rdn_wbytes_out_Z by (len_simpl; lia)
               | rewrite rdn_wbytes_out by region_side
               | lazymatch goal with |- rdn _ ?m _ _ = _ => is_var m; unfold m end ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef.ok_win HJ ::=
  apply store_ok_cmem_win;
  [ first [ assumption
          | repeat first [ apply wfJ_wbytes | lazymatch goal with |- wfJ _ ?j => is_var j; unfold j end ]; first [ exact HJ | assumption ] ]
  | region_side | region_side ].
Local Ltac stn_ra_old :=
  first [ apply regs_agree_refl
        | apply regs_agree_upd; [ in_list | ]; stn_ra_old
        | match goal with
          | Hag : regs_agree _ _ ?r |- regs_agree _ _ ?r =>
              eapply regs_agree_trans; [ | regs_agree_weaken Hag ]; stn_ra_old
          end ].
Local Ltac stn_ra_chain :=
  first [ apply regs_agree_refl
        | lazymatch goal with |- regs_agree (fun r => In r ?Cl) _ ?X =>
            lazymatch X with regupd _ _ _ => idtac end;
            let bb := gresl_base X in let l := gresl_list X in
            eapply regs_agree_trans; [ | exact (stn_regs_agree_regupds Cl l bb (@eq_refl bool true)) ]; stn_ra_chain end
        | match goal with
          | Hag : regs_agree _ _ ?r |- regs_agree _ _ ?r =>
              eapply regs_agree_trans; [ | regs_agree_weaken Hag ]; stn_ra_chain
          end ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef.ra_chain ::= first [ solve [ stn_ra_chain ] | stn_ra_old ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef.solve_regs_agree ::=
  first [ solve [ stn_ra_chain ] | repeat (apply regs_agree_upd; [ in_list | ]); apply regs_agree_refl ].
(* [comment removed for export] *)
Section P1.
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

  Let argc : word := argcN av.
  Local Notation argvp := (Z_to_bv 64 (bv_unsigned sp0 + 8)) (only parsing).
  Let envp : word := envp_ptr sp0 av.
  Let pn : word := cat_argv_ptr sp0 av ev 0.

  #[using="Hva"] Lemma u_argc : bv_unsigned argc = Z.of_nat (length av).
  Proof. exact (u_argcN av Hva). Qed.

  #[using="Hva sp0"] Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  (* [comment removed for export] *)
  Definition J1 (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x2270c)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argvp))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x17b98)).

  #[using="Hal Hhi Hlo Hve Hva"] Lemma p1_run : forall rom (J : word -> option byte),
    wfJ sp0 J ->
    exists regs',
      msteps SEGS (mkst (regs_init sp0) (0x17a4c : word) (CM J (fun _ => None)) rom)
                  (mkst regs' (0x2b3f8 : word) (CM (J1 J) (fun _ => None)) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x2248c
      /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416)
      /\ getr regs' 3 = Z_to_bv 64 0x10800
      /\ getr regs' 4 = Z_to_bv 64 0
      /\ getr regs' 8 = pn
      /\ getr regs' 9 = envp
      /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368)
      /\ getr regs' 11 = Z_to_bv 64 0
      /\ getr regs' 12 = Z_to_bv 64 304
      /\ getr regs' 18 = Z_to_bv 64 0x17b98
      /\ (forall r : reg, In r [5;19;20;21;22;23;24;25;26;27]%list -> getr regs' r = Z_to_bv 64 0).
  Proof.
    intros rom J HJ.
    pose proof len_av as Hlen. pose proof u_argc as Hargc.
    eexists. split.
    - unfold regs_init.
      stepn F_17a4c D_17a4c. renm.    (* [comment removed for export] *)
      stepn F_17a50 D_17a50. renm.    (* [comment removed for export] *)
      stepn F_17a54 D_17a54. renm.    (* [comment removed for export] *)
      stepn F_17a58 D_17a58. renm.    (* [comment removed for export] *)
      stepn F_17a5c D_17a5c. renm.    (* [comment removed for export] *)
      stepiv F_17a60 D_17a60 sp0 ltac:(gres; imm_norm; apply v_andi_m16_aligned; exact Hal). renm.
                                (* [comment removed for export] *)
      stepn F_17a64 D_17a64. renm.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 argc) (v := argc);
        [ exact F_17a68 | reflexivity | exact D_17a68
        | addr_norm; rewrite rdn_cmem_above by region_side;
          apply (rdn_low_bytes SEGS mem0 sp0 argc 4); [lia|];
          exact (read_argc_w SEGS RPH sp0 av ev uid hw rdraw Hva Hve Hhi)
        | apply bytes_le_to_Z_4_small; rewrite Hargc; lia ]
        | step_simpl]; vnorm.
      stn_open. rewrite (v_lw_small argc) by (rewrite Hargc; lia).
      stepn F_17a6c D_17a6c. renm.    (* [comment removed for export] *)
      stepn F_17a70 D_17a70. renm.    (* [comment removed for export] *)
      stepn F_17a74 D_17a74. renm.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x17b98);
        [exact F_17a78 | reflexivity | exact D_17a78 | rd_img img_30738_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x2245c);
        [exact F_17a7c | reflexivity | exact D_17a7c | rd_img img_30740_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x22cec);
        [exact F_17a80 | reflexivity | exact D_17a80 | rd_img img_30748_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      sv F_17a84 D_17a84 (Z_to_bv 64 (bv_unsigned sp0 + 8)). renm.   (* [comment removed for export] *)
      stepn F_17a88 D_17a88. renm.    (* [comment removed for export] *)
      stepn F_17a8c D_17a8c. renm.    (* [comment removed for export] *)
      stepn F_17a90 D_17a90. renm.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_226d8 D_226d8 (Z_to_bv 64 (bv_unsigned sp0 - 32)). renm.   (* [comment removed for export] *)
      stw F_226dc D_226dc (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ). renm.
      stw F_226e0 D_226e0 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ). renm.
      stw F_226e4 D_226e4 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ). renm.
      stw F_226e8 D_226e8 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ). renm.
      stepn F_226ec D_226ec. renm.    (* [comment removed for export] *)
      stepn F_226f0 D_226f0. renm.    (* [comment removed for export] *)
      stepn F_226f4 D_226f4. renm.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 pn) (v := pn);
        [ exact F_226f8 | reflexivity | exact D_226f8
        | addr_norm; rewrite rdn_cmem_above by region_side;
          replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (sp0 + nat_to_word (8 + 8 * 0))
            by (rewrite word_add_nat; f_equal; lia);
          exact (read_argv_ptr_w SEGS RPH sp0 av ev uid hw rdraw Hva Hve Hlo Hhi 0 ltac:(lia))
        | apply bytes_le_to_Z_8 ]
        | step_simpl]; vnorm.
      stepiv F_226fc D_226fc (Z_to_bv 64 (8 * Z.of_nat (length av)))
        ltac:(gres; imm_norm; rewrite <- Hargc; unfold v_slli; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^3)%Z with 8%Z; lia). renm.
                                (* [comment removed for export] *)
      stepiv F_22700 D_22700 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))) vclose. renm.
                                (* [comment removed for export] *)
      stepiv F_22704 D_22704 envp
        ltac:(gres; imm_norm; unfold envp, envp_ptr, v_addi; unorm; f_equal; lia). renm.
                                (* [comment removed for export] *)
      stepn F_22708 D_22708. renm.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_22460 D_22460 (Z_to_bv 64 (bv_unsigned sp0 - 416)). renm.   (* [comment removed for export] *)
      stw F_22464 D_22464 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0x2270c) ltac:(ok_win HJ). renm.
      stw F_22468 D_22468 (Z_to_bv 64 (bv_unsigned sp0 - 48)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ). renm.
      stw F_2246c D_2246c (Z_to_bv 64 (bv_unsigned sp0 - 56)) argc ltac:(ok_win HJ). renm.
      stw F_22470 D_22470 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 0x17b98) ltac:(ok_win HJ). renm.
      stepn F_22474 D_22474. renm.    (* [comment removed for export] *)
      stepn F_22478 D_22478. renm.    (* [comment removed for export] *)
      sv F_2247c D_2247c (Z_to_bv 64 (bv_unsigned sp0 - 368)). renm.   (* [comment removed for export] *)
      stepn F_22480 D_22480. renm.    (* [comment removed for export] *)
      stepn F_22484 D_22484. renm.    (* [comment removed for export] *)
      stepn F_22488 D_22488. renm.    (* [comment removed for export] *)
      stn_done. apply mst_refl.
    - repeat split; gres; try reflexivity.
      intros r Hr. cbn [In] in Hr.
      repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] end;
        [ .. | contradiction]; gres; apply getr_empty.
  Qed.
End P1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
