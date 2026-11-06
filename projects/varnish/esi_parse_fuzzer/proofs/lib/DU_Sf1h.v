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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Ssji DU_co77 DU_cb3t DU_cij8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ArgvEnv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefL1zx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefL1zx.DU_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Ssji OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_co77 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_cb3t OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_cij8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.DU_cg5g.

Module DU_Mv2g.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Star5ef DU_cij8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_cij8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.DU_cg5g.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition memset304_ws : list (Z * nat) :=
  [(0,1%nat); (303,1%nat); (1,1%nat); (2,1%nat); (301,1%nat); (302,1%nat); (3,1%nat); (300,1%nat); (0,4%nat); (300,4%nat); (4,4%nat); (8,4%nat); (292,4%nat); (296,4%nat); (12,4%nat); (16,4%nat); (20,4%nat); (24,4%nat); (276,4%nat); (280,4%nat); (284,4%nat); (288,4%nat); (24,8%nat); (32,8%nat); (40,8%nat); (48,8%nat); (56,8%nat); (64,8%nat); (72,8%nat); (80,8%nat); (88,8%nat); (96,8%nat); (104,8%nat); (112,8%nat); (120,8%nat); (128,8%nat); (136,8%nat); (144,8%nat); (152,8%nat); (160,8%nat); (168,8%nat); (176,8%nat); (184,8%nat); (192,8%nat); (200,8%nat); (208,8%nat); (216,8%nat); (224,8%nat); (232,8%nat); (240,8%nat); (248,8%nat); (256,8%nat); (264,8%nat); (272,8%nat)]%Z.
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

Lemma memset304_ws_inb : ws_inb memset304_ws 304 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma memset304_ws_cover : ws_cover memset304_ws 304 = true.
Proof. vm_compute. reflexivity. Qed.

Definition memset_clob : list reg := [11; 12; 13; 14; 15; 16]%list.

(* [comment removed for export] *)
Lemma memset304_run : forall regs (mem rom : word -> option byte) (d ret : word),
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 304 ->
  (bv_unsigned d mod 8 = 0)%Z ->
  (bv_unsigned d + 304 < 2^64)%Z ->
  store_ok SEGS mem d 304 = true ->
  exists regs' mem',
    msteps SEGS (mkst regs (0x2b3f8 : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 304)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split].
  - 
    stepb_ft F_2b3f8 D_2b3f8 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b3fc D_2b3fc (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sv F_2b400 D_2b400 (Z_to_bv 64 (bv_unsigned d + 304)). renm.  (* [comment removed for export] *)
    sn F_2b404 D_2b404. renm.  (* [comment removed for export] *)
    stw F_2b408 D_2b408 (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stepb_ft F_2b40c D_2b40c ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b410 D_2b410 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b414 D_2b414 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b418 D_2b418. renm.  (* [comment removed for export] *)
    stw F_2b41c D_2b41c (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b420 D_2b420 (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stepb_ft F_2b424 D_2b424 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b428 D_2b428 (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b42c D_2b42c. renm.  (* [comment removed for export] *)
    stw F_2b430 D_2b430 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stepb_ft F_2b434 D_2b434 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    sn F_2b438 D_2b438. renm.  (* [comment removed for export] *)
    sn F_2b43c D_2b43c. renm.  (* [comment removed for export] *)
    sn F_2b440 D_2b440. renm.  (* [comment removed for export] *)
    stepiv F_2b444 D_2b444 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4). renm.  (* [comment removed for export] *)
    sn F_2b448 D_2b448. renm.  (* [comment removed for export] *)
    sn F_2b44c D_2b44c. renm.  (* [comment removed for export] *)
    sv F_2b450 D_2b450 (d). renm.  (* [comment removed for export] *)
    sn F_2b454 D_2b454. renm.  (* [comment removed for export] *)
    sn F_2b458 D_2b458. renm.  (* [comment removed for export] *)
    sn F_2b45c D_2b45c. renm.  (* [comment removed for export] *)
    stw F_2b460 D_2b460 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sv F_2b464 D_2b464 (Z_to_bv 64 (bv_unsigned d + 304)). renm.  (* [comment removed for export] *)
    stw F_2b468 D_2b468 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stepb_ft F_2b46c D_2b46c ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b470 D_2b470 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b474 D_2b474 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b478 D_2b478. renm.  (* [comment removed for export] *)
    stw F_2b47c D_2b47c (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b480 D_2b480 (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stepb_ft F_2b484 D_2b484 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b488 D_2b488 (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b48c D_2b48c (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b490 D_2b490 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b494 D_2b494 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stepiv F_2b498 D_2b498 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal). renm.  (* [comment removed for export] *)
    sn F_2b49c D_2b49c. renm.  (* [comment removed for export] *)
    sn F_2b4a0 D_2b4a0. renm.  (* [comment removed for export] *)
    sn F_2b4a4 D_2b4a4. renm.  (* [comment removed for export] *)
    stw F_2b4a8 D_2b4a8 (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4ac D_2b4ac (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4b0 D_2b4b0 (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4b4 D_2b4b4 (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stepb_ft F_2b4b8 D_2b4b8 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    sn F_2b4bc D_2b4bc. renm.  (* [comment removed for export] *)
    sv F_2b4c0 D_2b4c0 (Z_to_bv 64 (bv_unsigned d + 24)). renm.  (* [comment removed for export] *)
    sn F_2b4c4 D_2b4c4. renm.  (* [comment removed for export] *)
    sn F_2b4c8 D_2b4c8. renm.  (* [comment removed for export] *)
    sn F_2b4cc D_2b4cc. renm.  (* [comment removed for export] *)
    stw F_2b4d0 D_2b4d0 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4d4 D_2b4d4 (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4d8 D_2b4d8 (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4dc D_2b4dc (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b4e0 D_2b4e0. renm.  (* [comment removed for export] *)
    sv F_2b4e4 D_2b4e4 (Z_to_bv 64 (bv_unsigned d + 56)). renm.  (* [comment removed for export] *)
    stepb_tk F_2b4e8 D_2b4e8 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b4d0 D_2b4d0 (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4d4 D_2b4d4 (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4d8 D_2b4d8 (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4dc D_2b4dc (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b4e0 D_2b4e0. renm.  (* [comment removed for export] *)
    sv F_2b4e4 D_2b4e4 (Z_to_bv 64 (bv_unsigned d + 88)). renm.  (* [comment removed for export] *)
    stepb_tk F_2b4e8 D_2b4e8 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b4d0 D_2b4d0 (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4d4 D_2b4d4 (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4d8 D_2b4d8 (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4dc D_2b4dc (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b4e0 D_2b4e0. renm.  (* [comment removed for export] *)
    sv F_2b4e4 D_2b4e4 (Z_to_bv 64 (bv_unsigned d + 120)). renm.  (* [comment removed for export] *)
    stepb_tk F_2b4e8 D_2b4e8 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b4d0 D_2b4d0 (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4d4 D_2b4d4 (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4d8 D_2b4d8 (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4dc D_2b4dc (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b4e0 D_2b4e0. renm.  (* [comment removed for export] *)
    sv F_2b4e4 D_2b4e4 (Z_to_bv 64 (bv_unsigned d + 152)). renm.  (* [comment removed for export] *)
    stepb_tk F_2b4e8 D_2b4e8 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b4d0 D_2b4d0 (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4d4 D_2b4d4 (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4d8 D_2b4d8 (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4dc D_2b4dc (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b4e0 D_2b4e0. renm.  (* [comment removed for export] *)
    sv F_2b4e4 D_2b4e4 (Z_to_bv 64 (bv_unsigned d + 184)). renm.  (* [comment removed for export] *)
    stepb_tk F_2b4e8 D_2b4e8 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b4d0 D_2b4d0 (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4d4 D_2b4d4 (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4d8 D_2b4d8 (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4dc D_2b4dc (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b4e0 D_2b4e0. renm.  (* [comment removed for export] *)
    sv F_2b4e4 D_2b4e4 (Z_to_bv 64 (bv_unsigned d + 216)). renm.  (* [comment removed for export] *)
    stepb_tk F_2b4e8 D_2b4e8 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b4d0 D_2b4d0 (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4d4 D_2b4d4 (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4d8 D_2b4d8 (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4dc D_2b4dc (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b4e0 D_2b4e0. renm.  (* [comment removed for export] *)
    sv F_2b4e4 D_2b4e4 (Z_to_bv 64 (bv_unsigned d + 248)). renm.  (* [comment removed for export] *)
    stepb_tk F_2b4e8 D_2b4e8 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b4d0 D_2b4d0 (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4d4 D_2b4d4 (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4d8 D_2b4d8 (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b4dc D_2b4dc (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b4e0 D_2b4e0. renm.  (* [comment removed for export] *)
    sv F_2b4e4 D_2b4e4 (Z_to_bv 64 (bv_unsigned d + 280)). renm.  (* [comment removed for export] *)
    stepb_ft F_2b4e8 D_2b4e8 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stepret F_2b4ec D_2b4ec ret ltac:(pin; reflexivity). renm.  (* [comment removed for export] *)
    stn_done. apply mst_refl.
  - stn_open. rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
    reflexivity.
  - stn_open. unfold memset_clob. solve_regs_agree.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End DU_Mv2g.


Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

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
Section P6.
  Variable sp0 : word.
  Variable Jb : word -> option byte.
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
  (* [comment removed for export] *)
  Local Notation R16 := (at_random_bytes (ed_random rdraw)) (only parsing).
  Local Notation RL := (rnd_lo (at_random_bytes (ed_random rdraw))) (only parsing).
  Local Notation RH := (rnd_hi (at_random_bytes (ed_random rdraw))) (only parsing).
  Local Notation CW := (canary_w (at_random_bytes (ed_random rdraw))) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 av ev))%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) mod 8 = 0)%Z.
  Proof.
    destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + Z.of_nat j)) n = Some (firstn n (skipn j R16)).
  Proof.
    intros J D j n Hjn.
    destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
    unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
  Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof. intros; subst; reflexivity. Qed.

  Ltac RD_RND j :=
    eapply rdn_addr; [apply (rd_rnd _ _ j); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

  (* [comment removed for export] *)
  Ltac RD_GUARD :=
    rewrite rdn_cmem_data by region_side;
    apply rd_guard3; rewrite length_N_to_le_bytes; reflexivity.

  Lemma slli_argc : v_slli (argc_w av) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof.
    pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.

  Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 271608 ->
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
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 271608) ->
        getr regs' 19 = (Z_to_bv 64 0) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 10; 11; 12; 13; 14; 15]%list) regs regs' ->
        G (mkst regs' (0x22578 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 140656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 403336))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 140664))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 402720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 403360) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 403368) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 271624) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 271600) (word_to_le_bytes 8 (Z_to_bv 64 271624))) (Z_to_bv 64 271408) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 403336) ([Z_to_bv 8 1])) (Z_to_bv 64 271448) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 271440) (word_to_le_bytes 4 tid)) (Z_to_bv 64 271560) (word_to_le_bytes 8 (Z_to_bv 64 403392))) (Z_to_bv 64 271528) (word_to_le_bytes 8 (Z_to_bv 64 271528))) (Z_to_bv 64 271416) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 271424) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 271432) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 403304) (word_to_le_bytes 4 (v_lw RL))) (Z_to_bv 64 403308) (word_to_le_bytes 4 (v_lw RH))) (Z_to_bv 64 403305) ([Z_to_bv 8 0])) (Z_to_bv 64 271592) (word_to_le_bytes 8 CW))) rom)) ->
    G (mkst regs (0x22570 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 140656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 403336))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 402720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 403360) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 403368) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 271624) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 271600) (word_to_le_bytes 8 (Z_to_bv 64 271624))) (Z_to_bv 64 271408) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 403336) ([Z_to_bv 8 1])) (Z_to_bv 64 271448) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 271440) (word_to_le_bytes 4 tid)) (Z_to_bv 64 271560) (word_to_le_bytes 8 (Z_to_bv 64 403392))) (Z_to_bv 64 271528) (word_to_le_bytes 8 (Z_to_bv 64 271528))) (Z_to_bv 64 271416) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 271424) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 271432) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_22570 D_22570 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      sn F_22574 D_22574. renm.  (* [comment removed for export] *)
      sv F_22e94 D_22e94 (Z_to_bv 64 (bv_unsigned sp0 - 432)). renm.  (* [comment removed for export] *)
      stw F_22e98 D_22e98 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 140664) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      stepb_ft F_22e9c D_22e9c ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia). renm.  (* [comment removed for export] *)
      sv F_22ea0 D_22ea0 ((rnd_w sp0 av ev)). renm.  (* [comment removed for export] *)
      sn F_22ea4 D_22ea4. renm.  (* [comment removed for export] *)
      ld_step F_22ea8 D_22ea8 (word_to_le_bytes 8 (Z_to_bv 64 403304)) (Z_to_bv 64 403304) ltac:(rd_img img_307c8_8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      sn F_22eac D_22eac. renm.  (* [comment removed for export] *)
      sn F_22eb0 D_22eb0. renm.  (* [comment removed for export] *)
      stepiv F_2aff4 D_2aff4 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity). renm.  (* [comment removed for export] *)
      stepb_tk F_2aff8 D_2aff8 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      sn F_2b108 D_2b108. renm.  (* [comment removed for export] *)
      sn F_2b10c D_2b10c. renm.  (* [comment removed for export] *)
      stepb_ft F_2b110 D_2b110 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      sn F_2b114 D_2b114. renm.  (* [comment removed for export] *)
      stepb_tk F_2b118 D_2b118 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      sn F_2b150 D_2b150. renm.  (* [comment removed for export] *)
      stepb_ft F_2b154 D_2b154 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      ld_step F_2b158 D_2b158 (firstn 4 (skipn 0 R16)) (rnd_lo R16) ltac:(RD_RND 0%nat) ltac:(apply bytes_le_to_Z_u8; cbn; lia). renm.  (* [comment removed for export] *)
      ld_step F_2b15c D_2b15c (firstn 4 (skipn 4 R16)) (rnd_hi R16) ltac:(RD_RND 4%nat) ltac:(apply bytes_le_to_Z_u8; cbn; lia). renm.  (* [comment removed for export] *)
      stw F_2b160 D_2b160 (Z_to_bv 64 403304) (v_lw RL) ltac:(ok_data). renm.  (* [comment removed for export] *)
      stw F_2b164 D_2b164 (Z_to_bv 64 403308) (v_lw RH) ltac:(ok_data). renm.  (* [comment removed for export] *)
      sn F_2b168 D_2b168. renm.  (* [comment removed for export] *)
      sv F_2b16c D_2b16c (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)). renm.  (* [comment removed for export] *)
      sn F_2b170 D_2b170. renm.  (* [comment removed for export] *)
      stepb_tk F_2b174 D_2b174 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      sn F_2b3b4 D_2b3b4. renm.  (* [comment removed for export] *)
      stepb_ft F_2b3b8 D_2b3b8 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      sn F_2b3bc D_2b3bc. renm.  (* [comment removed for export] *)
      stepb_ft F_2b3c0 D_2b3c0 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      stepret F_2b3c4 D_2b3c4 (0x22eb4 : word) ltac:(pin; first [reflexivity | bveq]). renm.  (* [comment removed for export] *)
      sn F_22eb4 D_22eb4. renm.  (* [comment removed for export] *)
      sn F_22ed0 D_22ed0. renm.  (* [comment removed for export] *)
      ld_step F_22ed4 D_22ed4 (word_to_le_bytes 8 (Z_to_bv 64 403304)) (Z_to_bv 64 403304) ltac:(rd_img img_307c8_8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      stw F_22ed8 D_22ed8 (Z_to_bv 64 403305) (Z_to_bv 64 0) ltac:(ok_data). renm.  (* [comment removed for export] *)
      ld_step F_22edc D_22edc (guard_bytes R16) (canary_w R16) ltac:(RD_GUARD) ltac:(apply bytes_le_to_Z_u8; rewrite length_guard_bytes; lia). renm.  (* [comment removed for export] *)
      sn F_22ee0 D_22ee0. renm.  (* [comment removed for export] *)
      stw F_22ee4 D_22ee4 (Z_to_bv 64 271592) (canary_w R16) ltac:(ok_data). renm.  (* [comment removed for export] *)
      ld_step F_22ee8 D_22ee8 (word_to_le_bytes 8 (Z_to_bv 64 140664)) (Z_to_bv 64 140664) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      sv F_22eec D_22eec (Z_to_bv 64 (bv_unsigned sp0 - 416)). renm.  (* [comment removed for export] *)
      stepret F_22ef0 D_22ef0 (0x22578 : word) ltac:(pin; first [reflexivity | bveq]). renm.  (* [comment removed for export] *)
      stn_done. apply mst_refl. }
    stn_final. apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 271608 ->
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
        getr regs' 1 = (Z_to_bv 64 0) ->
        getr regs' 2 = sp0 ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 271608) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 97176) ->
        getr regs' 11 = (argc_w av) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 18 = (Z_to_bv 64 0) ->
        getr regs' 19 = (Z_to_bv 64 0) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 6; 8; 9; 10; 11; 12; 18]%list) regs regs' ->
        G (mkst regs' (0x22738 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 140656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 403336))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 140664))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 402720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 403360) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 403368) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 271624) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 271600) (word_to_le_bytes 8 (Z_to_bv 64 271624))) (Z_to_bv 64 271408) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 403336) ([Z_to_bv 8 1])) (Z_to_bv 64 271448) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 271440) (word_to_le_bytes 4 tid)) (Z_to_bv 64 271560) (word_to_le_bytes 8 (Z_to_bv 64 403392))) (Z_to_bv 64 271528) (word_to_le_bytes 8 (Z_to_bv 64 271528))) (Z_to_bv 64 271416) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 271424) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 271432) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 403304) (word_to_le_bytes 4 (v_lw RL))) (Z_to_bv 64 403308) (word_to_le_bytes 4 (v_lw RH))) (Z_to_bv 64 403305) ([Z_to_bv 8 0])) (Z_to_bv 64 271592) (word_to_le_bytes 8 CW))) rom)) ->
    G (mkst regs (0x22578 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 140656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 403336))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 140664))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 402720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 403360) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 403368) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 271624) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 271600) (word_to_le_bytes 8 (Z_to_bv 64 271624))) (Z_to_bv 64 271408) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 403336) ([Z_to_bv 8 1])) (Z_to_bv 64 271448) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 271440) (word_to_le_bytes 4 tid)) (Z_to_bv 64 271560) (word_to_le_bytes 8 (Z_to_bv 64 403392))) (Z_to_bv 64 271528) (word_to_le_bytes 8 (Z_to_bv 64 271528))) (Z_to_bv 64 271416) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 271424) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 271432) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 403304) (word_to_le_bytes 4 (v_lw RL))) (Z_to_bv 64 403308) (word_to_le_bytes 4 (v_lw RH))) (Z_to_bv 64 403305) ([Z_to_bv 8 0])) (Z_to_bv 64 271592) (word_to_le_bytes 8 CW))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_22578 D_22578 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_2257c D_2257c (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      stepb_ft F_22580 D_22580 ltac:(pin; apply c_eq_refl). renm.  (* [comment removed for export] *)
      ld_step F_22584 D_22584 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity). renm.  (* [comment removed for export] *)
      ld_step F_22588 D_22588 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity). renm.  (* [comment removed for export] *)
      stepb_ft F_2258c D_2258c ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      ld_step F_22590 D_22590 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      stepb_tk F_22594 D_22594 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      ld_step F_22674 D_22674 (word_to_le_bytes 8 (Z_to_bv 64 141068)) (Z_to_bv 64 141068) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_22678 D_22678 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_2267c D_2267c (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_22680 D_22680 (word_to_le_bytes 8 (Z_to_bv 64 97176)) (Z_to_bv 64 97176) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      sv F_22684 D_22684 (Z_to_bv 64 (bv_unsigned sp0 - 32)). renm.  (* [comment removed for export] *)
      stepret F_22688 D_22688 (0x2270c : word) ltac:(pin; first [reflexivity | bveq]). renm.  (* [comment removed for export] *)
      sn F_2270c D_2270c. renm.  (* [comment removed for export] *)
      sn F_22710 D_22710. renm.  (* [comment removed for export] *)
      sn F_22714 D_22714. renm.  (* [comment removed for export] *)
      sv F_22718 D_22718 (argc_w av). renm.  (* [comment removed for export] *)
      sv F_2271c D_2271c (Z_to_bv 64 (bv_unsigned sp0 + 8)). renm.  (* [comment removed for export] *)
      ld_step F_22720 D_22720 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_22724 D_22724 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_22728 D_22728 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_2272c D_2272c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      sv F_22730 D_22730 (sp0). renm.  (* [comment removed for export] *)
      stepret F_22734 D_22734 (0x22738 : word) ltac:(pin; first [reflexivity | bveq]). renm.  (* [comment removed for export] *)
      stn_done. apply mst_refl. }
    stn_final. apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 271608 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 97176 ->
    getr regs 11 = argc_w av ->
    getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
    getr regs 18 = Z_to_bv 64 0 ->
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
        getr regs' 1 = (Z_to_bv 64 140988) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 271608) ->
        getr regs' 8 = (Z_to_bv 64 198152) ->
        getr regs' 9 = (Z_to_bv 64 198144) ->
        getr regs' 18 = (Z_to_bv 64 97176) ->
        getr regs' 19 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19]%list) regs regs' ->
        G (mkst regs' (0x17a94 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 140656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 403336))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 140664))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 141164))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 402720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 403360) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 403368) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 271624) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 271600) (word_to_le_bytes 8 (Z_to_bv 64 271624))) (Z_to_bv 64 271408) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 403336) ([Z_to_bv 8 1])) (Z_to_bv 64 271448) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 271440) (word_to_le_bytes 4 tid)) (Z_to_bv 64 271560) (word_to_le_bytes 8 (Z_to_bv 64 403392))) (Z_to_bv 64 271528) (word_to_le_bytes 8 (Z_to_bv 64 271528))) (Z_to_bv 64 271416) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 271424) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 271432) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 403304) (word_to_le_bytes 4 (v_lw RL))) (Z_to_bv 64 403308) (word_to_le_bytes 4 (v_lw RH))) (Z_to_bv 64 403305) ([Z_to_bv 8 0])) (Z_to_bv 64 271592) (word_to_le_bytes 8 CW))) rom)) ->
    G (mkst regs (0x22738 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 140656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 403336))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 140664))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 402720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 403360) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 403368) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 271624) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 271600) (word_to_le_bytes 8 (Z_to_bv 64 271624))) (Z_to_bv 64 271408) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 403336) ([Z_to_bv 8 1])) (Z_to_bv 64 271448) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 271440) (word_to_le_bytes 4 tid)) (Z_to_bv 64 271560) (word_to_le_bytes 8 (Z_to_bv 64 403392))) (Z_to_bv 64 271528) (word_to_le_bytes 8 (Z_to_bv 64 271528))) (Z_to_bv 64 271416) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 271424) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 271432) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 403304) (word_to_le_bytes 4 (v_lw RL))) (Z_to_bv 64 403308) (word_to_le_bytes 4 (v_lw RH))) (Z_to_bv 64 403305) ([Z_to_bv 8 0])) (Z_to_bv 64 271592) (word_to_le_bytes 8 CW))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_22738 D_22738 (Z_to_bv 64 (bv_unsigned sp0 - 48)). renm.  (* [comment removed for export] *)
      stw F_2273c D_2273c (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      stw F_22740 D_22740 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      stw F_22744 D_22744 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      stw F_22748 D_22748 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      stw F_2274c D_2274c (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      sv F_22750 D_22750 (Z_to_bv 64 (bv_unsigned sp0 + 8)). renm.  (* [comment removed for export] *)
      sv F_22754 D_22754 (argc_w av). renm.  (* [comment removed for export] *)
      sn F_22758 D_22758. renm.  (* [comment removed for export] *)
      stepiv F_2275c D_2275c (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc). renm.  (* [comment removed for export] *)
      sv F_22760 D_22760 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))). renm.  (* [comment removed for export] *)
      sv F_22764 D_22764 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))). renm.  (* [comment removed for export] *)
      sn F_22768 D_22768. renm.  (* [comment removed for export] *)
      sv F_2268c D_2268c (Z_to_bv 64 (bv_unsigned sp0 - 80)). renm.  (* [comment removed for export] *)
      stw F_22690 D_22690 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 141164) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      stw F_22694 D_22694 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      stw F_22698 D_22698 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      sn F_2269c D_2269c. renm.  (* [comment removed for export] *)
      stepret F_2245c D_2245c (0x226a0 : word) ltac:(pin; first [reflexivity | bveq]). renm.  (* [comment removed for export] *)
      sn F_226a0 D_226a0. renm.  (* [comment removed for export] *)
      sn F_226a4 D_226a4. renm.  (* [comment removed for export] *)
      ld_step F_226a8 D_226a8 (word_to_le_bytes 8 (Z_to_bv 64 198152)) (Z_to_bv 64 198152) ltac:(rd_img img_307b8_8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_226ac D_226ac (word_to_le_bytes 8 (Z_to_bv 64 198144)) (Z_to_bv 64 198144) ltac:(rd_img img_307c0_8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      stepb_ft F_226b0 D_226b0 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      ld_step F_226b4 D_226b4 (word_to_le_bytes 8 (Z_to_bv 64 96916)) (Z_to_bv 64 96916) ltac:(rd_img img_30600_8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      stepjr F_226b8 D_226b8 (0x17a94 : word) ltac:(gres; pin; first [reflexivity | bveq]). renm.  (* [comment removed for export] *)
      stn_done. apply mst_refl. }
    stn_final. apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 140988 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 271608 ->
    getr regs 8 = Z_to_bv 64 198152 ->
    getr regs 9 = Z_to_bv 64 198144 ->
    getr regs 18 = Z_to_bv 64 97176 ->
    getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 1 = (Z_to_bv 64 141180) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 271608) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 97176) ->
        getr regs' 19 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs' ->
        G (mkst regs' (0x17b98 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 140656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 403336))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 140664))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 141164))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 140988))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 198152))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 402720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 403360) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 403368) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 271624) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 271600) (word_to_le_bytes 8 (Z_to_bv 64 271624))) (Z_to_bv 64 271408) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 403336) ([Z_to_bv 8 1])) (Z_to_bv 64 271448) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 271440) (word_to_le_bytes 4 tid)) (Z_to_bv 64 271560) (word_to_le_bytes 8 (Z_to_bv 64 403392))) (Z_to_bv 64 271528) (word_to_le_bytes 8 (Z_to_bv 64 271528))) (Z_to_bv 64 271416) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 271424) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 271432) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 403304) (word_to_le_bytes 4 (v_lw RL))) (Z_to_bv 64 403308) (word_to_le_bytes 4 (v_lw RH))) (Z_to_bv 64 403305) ([Z_to_bv 8 0])) (Z_to_bv 64 271592) (word_to_le_bytes 8 CW)) (Z_to_bv 64 203600) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x17a94 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 140656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 403336))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 140664))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 141164))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 402720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 403360) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 403368) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 271624) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 271600) (word_to_le_bytes 8 (Z_to_bv 64 271624))) (Z_to_bv 64 271408) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 403336) ([Z_to_bv 8 1])) (Z_to_bv 64 271448) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 271440) (word_to_le_bytes 4 tid)) (Z_to_bv 64 271560) (word_to_le_bytes 8 (Z_to_bv 64 403392))) (Z_to_bv 64 271528) (word_to_le_bytes 8 (Z_to_bv 64 271528))) (Z_to_bv 64 271416) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 271424) (word_to_le_bytes 8 (Z_to_bv 64 271408))) (Z_to_bv 64 271432) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 403304) (word_to_le_bytes 4 (v_lw RL))) (Z_to_bv 64 403308) (word_to_le_bytes 4 (v_lw RH))) (Z_to_bv 64 403305) ([Z_to_bv 8 0])) (Z_to_bv 64 271592) (word_to_le_bytes 8 CW))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_17a94 D_17a94 (Z_to_bv 64 (bv_unsigned sp0 - 96)). renm.  (* [comment removed for export] *)
      stw F_17a98 D_17a98 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 140988) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      stw F_17a9c D_17a9c (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 198152) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      sv F_17aa0 D_17aa0 (Z_to_bv 64 (bv_unsigned sp0 - 80)). renm.  (* [comment removed for export] *)
      sn F_17aa4 D_17aa4. renm.  (* [comment removed for export] *)
      sn F_17aa8 D_17aa8. renm.  (* [comment removed for export] *)
      lb_step F_17aac D_17aac (Z_to_bv 8 0) ltac:(rd_img img_31b50_1). renm.  (* [comment removed for export] *)
      sn F_17ab0 D_17ab0. renm.  (* [comment removed for export] *)
      stepb_tk F_17ab4 D_17ab4 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      sn F_17ac0 D_17ac0. renm.  (* [comment removed for export] *)
      sn F_17ac4 D_17ac4. renm.  (* [comment removed for export] *)
      sn F_17ac8 D_17ac8. renm.  (* [comment removed for export] *)
      stw F_17acc D_17acc (Z_to_bv 64 203600) (Z_to_bv 64 1) ltac:(ok_data). renm.  (* [comment removed for export] *)
      sn F_17ad0 D_17ad0. renm.  (* [comment removed for export] *)
      ld_step F_17ad4 D_17ad4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_30750_8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      stepb_tk F_17ad8 D_17ad8 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      ld_step F_17af8 D_17af8 (word_to_le_bytes 8 (Z_to_bv 64 140988)) (Z_to_bv 64 140988) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_17afc D_17afc (word_to_le_bytes 8 (Z_to_bv 64 198152)) (Z_to_bv 64 198152) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      sv F_17b00 D_17b00 (Z_to_bv 64 (bv_unsigned sp0 - 80)). renm.  (* [comment removed for export] *)
      stepret F_17b04 D_17b04 (0x226bc : word) ltac:(pin; first [reflexivity | bveq]). renm.  (* [comment removed for export] *)
      sn F_226bc D_226bc. renm.  (* [comment removed for export] *)
      stepb_ft F_226c0 D_226c0 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      ld_step F_226c4 D_226c4 (word_to_le_bytes 8 (Z_to_bv 64 141164)) (Z_to_bv 64 141164) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_226c8 D_226c8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_226cc D_226cc (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      sv F_226d0 D_226d0 (Z_to_bv 64 (bv_unsigned sp0 - 48)). renm.  (* [comment removed for export] *)
      stepret F_226d4 D_226d4 (0x2276c : word) ltac:(pin; first [reflexivity | bveq]). renm.  (* [comment removed for export] *)
      sv F_2276c D_2276c (argc_w av). renm.  (* [comment removed for export] *)
      sv F_22770 D_22770 (Z_to_bv 64 (bv_unsigned sp0 + 8)). renm.  (* [comment removed for export] *)
      sv F_22774 D_22774 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))). renm.  (* [comment removed for export] *)
      stepjr F_22778 D_22778 (0x17b98 : word) ltac:(gres; pin; first [reflexivity | bveq]). renm.  (* [comment removed for export] *)
      stn_done. apply mst_refl. }
    stn_final. apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
