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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_St4s2 D_co4d2 D_coj29 D_co2ld.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ArgvEnv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefL1zx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefL1zx.D_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_St4s2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_co4d2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_coj29 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_co2ld.

Module D_Memset.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Star5ef D_co2ld.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require BWorld.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_co2ld OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.BWorld.D_co8nq.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

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
    msteps SEGS (mkst regs (0x2b058 : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 304)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split].
  - 
    stepb_ft F_2b058 D_2b058 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b05c D_2b05c (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sv F_2b060 D_2b060 (Z_to_bv 64 (bv_unsigned d + 304)). renm.  (* [comment removed for export] *)
    sn F_2b064 D_2b064. renm.  (* [comment removed for export] *)
    stw F_2b068 D_2b068 (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stepb_ft F_2b06c D_2b06c ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b070 D_2b070 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b074 D_2b074 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b078 D_2b078. renm.  (* [comment removed for export] *)
    stw F_2b07c D_2b07c (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b080 D_2b080 (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stepb_ft F_2b084 D_2b084 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b088 D_2b088 (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b08c D_2b08c. renm.  (* [comment removed for export] *)
    stw F_2b090 D_2b090 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stepb_ft F_2b094 D_2b094 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    sn F_2b098 D_2b098. renm.  (* [comment removed for export] *)
    sn F_2b09c D_2b09c. renm.  (* [comment removed for export] *)
    sn F_2b0a0 D_2b0a0. renm.  (* [comment removed for export] *)
    stepiv F_2b0a4 D_2b0a4 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4). renm.  (* [comment removed for export] *)
    sn F_2b0a8 D_2b0a8. renm.  (* [comment removed for export] *)
    sn F_2b0ac D_2b0ac. renm.  (* [comment removed for export] *)
    sv F_2b0b0 D_2b0b0 (d). renm.  (* [comment removed for export] *)
    sn F_2b0b4 D_2b0b4. renm.  (* [comment removed for export] *)
    sn F_2b0b8 D_2b0b8. renm.  (* [comment removed for export] *)
    sn F_2b0bc D_2b0bc. renm.  (* [comment removed for export] *)
    stw F_2b0c0 D_2b0c0 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sv F_2b0c4 D_2b0c4 (Z_to_bv 64 (bv_unsigned d + 304)). renm.  (* [comment removed for export] *)
    stw F_2b0c8 D_2b0c8 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stepb_ft F_2b0cc D_2b0cc ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b0d0 D_2b0d0 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b0d4 D_2b0d4 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b0d8 D_2b0d8. renm.  (* [comment removed for export] *)
    stw F_2b0dc D_2b0dc (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b0e0 D_2b0e0 (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stepb_ft F_2b0e4 D_2b0e4 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b0e8 D_2b0e8 (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b0ec D_2b0ec (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b0f0 D_2b0f0 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b0f4 D_2b0f4 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stepiv F_2b0f8 D_2b0f8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal). renm.  (* [comment removed for export] *)
    sn F_2b0fc D_2b0fc. renm.  (* [comment removed for export] *)
    sn F_2b100 D_2b100. renm.  (* [comment removed for export] *)
    sn F_2b104 D_2b104. renm.  (* [comment removed for export] *)
    stw F_2b108 D_2b108 (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b10c D_2b10c (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b110 D_2b110 (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b114 D_2b114 (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stepb_ft F_2b118 D_2b118 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    sn F_2b11c D_2b11c. renm.  (* [comment removed for export] *)
    sv F_2b120 D_2b120 (Z_to_bv 64 (bv_unsigned d + 24)). renm.  (* [comment removed for export] *)
    sn F_2b124 D_2b124. renm.  (* [comment removed for export] *)
    sn F_2b128 D_2b128. renm.  (* [comment removed for export] *)
    sn F_2b12c D_2b12c. renm.  (* [comment removed for export] *)
    stw F_2b130 D_2b130 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b134 D_2b134 (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b138 D_2b138 (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b13c D_2b13c (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b140 D_2b140. renm.  (* [comment removed for export] *)
    sv F_2b144 D_2b144 (Z_to_bv 64 (bv_unsigned d + 56)). renm.  (* [comment removed for export] *)
    stepb_tk F_2b148 D_2b148 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b130 D_2b130 (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b134 D_2b134 (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b138 D_2b138 (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b13c D_2b13c (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b140 D_2b140. renm.  (* [comment removed for export] *)
    sv F_2b144 D_2b144 (Z_to_bv 64 (bv_unsigned d + 88)). renm.  (* [comment removed for export] *)
    stepb_tk F_2b148 D_2b148 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b130 D_2b130 (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b134 D_2b134 (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b138 D_2b138 (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b13c D_2b13c (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b140 D_2b140. renm.  (* [comment removed for export] *)
    sv F_2b144 D_2b144 (Z_to_bv 64 (bv_unsigned d + 120)). renm.  (* [comment removed for export] *)
    stepb_tk F_2b148 D_2b148 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b130 D_2b130 (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b134 D_2b134 (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b138 D_2b138 (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b13c D_2b13c (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b140 D_2b140. renm.  (* [comment removed for export] *)
    sv F_2b144 D_2b144 (Z_to_bv 64 (bv_unsigned d + 152)). renm.  (* [comment removed for export] *)
    stepb_tk F_2b148 D_2b148 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b130 D_2b130 (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b134 D_2b134 (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b138 D_2b138 (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b13c D_2b13c (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b140 D_2b140. renm.  (* [comment removed for export] *)
    sv F_2b144 D_2b144 (Z_to_bv 64 (bv_unsigned d + 184)). renm.  (* [comment removed for export] *)
    stepb_tk F_2b148 D_2b148 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b130 D_2b130 (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b134 D_2b134 (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b138 D_2b138 (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b13c D_2b13c (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b140 D_2b140. renm.  (* [comment removed for export] *)
    sv F_2b144 D_2b144 (Z_to_bv 64 (bv_unsigned d + 216)). renm.  (* [comment removed for export] *)
    stepb_tk F_2b148 D_2b148 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b130 D_2b130 (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b134 D_2b134 (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b138 D_2b138 (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b13c D_2b13c (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b140 D_2b140. renm.  (* [comment removed for export] *)
    sv F_2b144 D_2b144 (Z_to_bv 64 (bv_unsigned d + 248)). renm.  (* [comment removed for export] *)
    stepb_tk F_2b148 D_2b148 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stw F_2b130 D_2b130 (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b134 D_2b134 (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b138 D_2b138 (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    stw F_2b13c D_2b13c (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_sub Hok). renm.  (* [comment removed for export] *)
    sn F_2b140 D_2b140. renm.  (* [comment removed for export] *)
    sv F_2b144 D_2b144 (Z_to_bv 64 (bv_unsigned d + 280)). renm.  (* [comment removed for export] *)
    stepb_ft F_2b148 D_2b148 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
    stepret F_2b14c D_2b14c ret ltac:(pin; reflexivity). renm.  (* [comment removed for export] *)
    stn_done. apply mst_refl.
  - stn_open. rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
    reflexivity.
  - stn_open. unfold memset_clob. solve_regs_agree.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End D_Memset.

Module D_Trk7v.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WalkTac D_co4d2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_co4d2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Theorem tr_call : forall regs mem rom,
  getr regs 20 = Z_to_bv 64 0x41800 ->
  store_ok RSEGS mem (Z_to_bv 64 0x41804) 1%nat = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x17eec : word) mem rom)
                 (mkst regs' (0x18048 : word) (wbytes mem (Z_to_bv 64 0x41804) [Z_to_bv 8 1]) rom)
    /\ getr regs' 10 = getr regs 9
    /\ getr regs' 11 = getr regs 8
    /\ getr regs' 1 = Z_to_bv 64 0x17f00
    /\ (forall r : reg, r <> 1 -> r <> 10 -> r <> 11 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom H20 SOK. eexists. split.
  - stepn F_17eec D_17eec.
    chain_step; [reflexivity
      | eapply MmapSim.step_sb_at with (a := Z_to_bv 64 0x41804) (v := Z_to_bv 64 1);
        [ exact F_17ef0 | reflexivity | exact D_17ef0 | gres; imm_norm; rewrite H20; apply bv_eq; reflexivity
        | gres; reflexivity | reflexivity | exact SOK ]
      | step_simpl ].
    stepn F_17ef4 D_17ef4.
    stepn F_17ef8 D_17ef8.
    stepn F_17efc D_17efc.
    apply mst_refl.
  - OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; try reflexivity.
    intros r H1 H10 H11. rewrite !getr_other by assumption. reflexivity.
Qed.

Theorem tr_pf : forall regs mem rom,
  getr regs 20 = Z_to_bv 64 0x41800 ->
  store_ok RSEGS mem (Z_to_bv 64 0x41804) 1%nat = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x17f00 : word) mem rom)
                 (mkst regs' (0x17fbc : word) (wbytes mem (Z_to_bv 64 0x41804) [Z_to_bv 8 0]) rom)
    /\ getr regs' 19 = getr regs 10
    /\ getr regs' 11 = getr regs 10
    /\ getr regs' 1 = Z_to_bv 64 0x17f10
    /\ (forall r : reg, r <> 1 -> r <> 19 -> r <> 11 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom H20 SOK. eexists. split.
  - stepn F_17f00 D_17f00.
    chain_step; [reflexivity
      | eapply MmapSim.step_sb_at with (a := Z_to_bv 64 0x41804) (v := Z_to_bv 64 0);
        [ exact F_17f04 | reflexivity | exact D_17f04 | gres; imm_norm; rewrite H20; apply bv_eq; reflexivity
        | gres; first [reflexivity | apply getr_zero] | reflexivity | exact SOK ]
      | step_simpl ].
    stepn F_17f08 D_17f08.
    stepn F_17f0c D_17f0c.
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
    msteps RSEGS (mkst regs (0x17f10 : word) mem rom)
                 (mkst regs' ((if Nat.eqb j 0 then 0x17f24 else 0x17eec) : word) mem rom)
    /\ getr regs' 21 = Z_to_bv 64 (Z.of_nat j)
    /\ (forall r : reg, r <> 19 -> r <> 21 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom j H21 Hj H19 H23.
  destruct (Nat.eqb_spec j 0) as [->|Hne].
  - eexists. split.
    + stepiwv F_17f10 D_17f10 (Z_to_bv 64 18446744073709551615) ltac:(gres; imm_norm; rewrite H19; apply bv_eq; vm_compute; reflexivity).
      stepb_tk F_17f14 D_17f14 ltac:(gres; rewrite H23; cond_compute).
      stepiwv F_17f1c D_17f1c (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite H21; apply (v_addiw_dec 0); lia).
      stepb_ft F_17f20 D_17f20 ltac:(gres; cond_compute).
      apply mst_refl.
    + split; [gres; reflexivity|]. intros r Ha Hb. rewrite !getr_other by assumption. reflexivity.
  - eexists. split.
    + stepiwv F_17f10 D_17f10 (Z_to_bv 64 18446744073709551615) ltac:(gres; imm_norm; rewrite H19; apply bv_eq; vm_compute; reflexivity).
      stepb_tk F_17f14 D_17f14 ltac:(gres; rewrite H23; cond_compute).
      stepiwv F_17f1c D_17f1c (Z_to_bv 64 (Z.of_nat j)) ltac:(gres; imm_norm; rewrite H21; apply v_addiw_dec; lia).
      stepb_tk F_17f20 D_17f20 ltac:(gres; apply c_eq_0_false; rewrite u_Z2bv by lia; lia).
      apply mst_refl.
    + split; [gres; reflexivity|]. intros r Ha Hb. rewrite !getr_other by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem tr_c : forall regs mem rom,
  exists regs',
    msteps RSEGS (mkst regs (0x17eac : word) mem rom) (mkst regs' (0x17eec : word) mem rom)
    /\ getr regs' 9 = getr regs 18
    /\ getr regs' 22 = Z_to_bv 64 0
    /\ getr regs' 23 = Z_to_bv 64 18446744073709551614
    /\ (forall r : reg, r <> 9 -> r <> 22 -> r <> 23 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom. eexists. split.
  - stepn F_17eac D_17eac.
    stepn F_17eb0 D_17eb0.
    stepv F_17ee4 D_17ee4 (Z_to_bv 64 0).
    stepv F_17ee8 D_17ee8 (Z_to_bv 64 18446744073709551614).
    apply mst_refl.
  - OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; try reflexivity.
    intros r H9 H22 H23. rewrite !getr_other by assumption. reflexivity.
Qed.
End D_Trk7v.


Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

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
    getr regs 4 = Z_to_bv 64 270680 ->
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
        regs_agree (fun r => In r [1; 2; 10; 11; 12; 13; 14; 15]%list) regs regs' ->
        G (mkst regs' (0x221d8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139728))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 402408))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139736))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 401792) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401808) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401800) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 402432) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 402440) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 270696) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 270672) (word_to_le_bytes 8 (Z_to_bv 64 270696))) (Z_to_bv 64 270480) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 402408) ([Z_to_bv 8 1])) (Z_to_bv 64 270520) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 270512) (word_to_le_bytes 4 tid)) (Z_to_bv 64 270632) (word_to_le_bytes 8 (Z_to_bv 64 402464))) (Z_to_bv 64 270600) (word_to_le_bytes 8 (Z_to_bv 64 270600))) (Z_to_bv 64 270488) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 270496) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 270504) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402376) (word_to_le_bytes 4 (v_lw RL))) (Z_to_bv 64 402380) (word_to_le_bytes 4 (v_lw RH))) (Z_to_bv 64 402377) ([Z_to_bv 8 0])) (Z_to_bv 64 270664) (word_to_le_bytes 8 CW))) rom)) ->
    G (mkst regs (0x221d0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139728))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 402408))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 401792) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401808) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401800) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 402432) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 402440) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 270696) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 270672) (word_to_le_bytes 8 (Z_to_bv 64 270696))) (Z_to_bv 64 270480) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 402408) ([Z_to_bv 8 1])) (Z_to_bv 64 270520) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 270512) (word_to_le_bytes 4 tid)) (Z_to_bv 64 270632) (word_to_le_bytes 8 (Z_to_bv 64 402464))) (Z_to_bv 64 270600) (word_to_le_bytes 8 (Z_to_bv 64 270600))) (Z_to_bv 64 270488) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 270496) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 270504) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_221d0 D_221d0 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      sn F_221d4 D_221d4. renm.  (* [comment removed for export] *)
      sv F_22af4 D_22af4 (Z_to_bv 64 (bv_unsigned sp0 - 432)). renm.  (* [comment removed for export] *)
      stw F_22af8 D_22af8 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 139736) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      stepb_ft F_22afc D_22afc ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia). renm.  (* [comment removed for export] *)
      sv F_22b00 D_22b00 ((rnd_w sp0 av ev)). renm.  (* [comment removed for export] *)
      sn F_22b04 D_22b04. renm.  (* [comment removed for export] *)
      ld_step F_22b08 D_22b08 (word_to_le_bytes 8 (Z_to_bv 64 402376)) (Z_to_bv 64 402376) ltac:(rd_img img_30428_8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      sn F_22b0c D_22b0c. renm.  (* [comment removed for export] *)
      sn F_22b10 D_22b10. renm.  (* [comment removed for export] *)
      stepiv F_2ac54 D_2ac54 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity). renm.  (* [comment removed for export] *)
      stepb_tk F_2ac58 D_2ac58 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      sn F_2ad68 D_2ad68. renm.  (* [comment removed for export] *)
      sn F_2ad6c D_2ad6c. renm.  (* [comment removed for export] *)
      stepb_ft F_2ad70 D_2ad70 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      sn F_2ad74 D_2ad74. renm.  (* [comment removed for export] *)
      stepb_tk F_2ad78 D_2ad78 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      sn F_2adb0 D_2adb0. renm.  (* [comment removed for export] *)
      stepb_ft F_2adb4 D_2adb4 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      ld_step F_2adb8 D_2adb8 (firstn 4 (skipn 0 R16)) (rnd_lo R16) ltac:(RD_RND 0%nat) ltac:(apply bytes_le_to_Z_u8; cbn; lia). renm.  (* [comment removed for export] *)
      ld_step F_2adbc D_2adbc (firstn 4 (skipn 4 R16)) (rnd_hi R16) ltac:(RD_RND 4%nat) ltac:(apply bytes_le_to_Z_u8; cbn; lia). renm.  (* [comment removed for export] *)
      stw F_2adc0 D_2adc0 (Z_to_bv 64 402376) (v_lw RL) ltac:(ok_data). renm.  (* [comment removed for export] *)
      stw F_2adc4 D_2adc4 (Z_to_bv 64 402380) (v_lw RH) ltac:(ok_data). renm.  (* [comment removed for export] *)
      sn F_2adc8 D_2adc8. renm.  (* [comment removed for export] *)
      sv F_2adcc D_2adcc (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)). renm.  (* [comment removed for export] *)
      sn F_2add0 D_2add0. renm.  (* [comment removed for export] *)
      stepb_tk F_2add4 D_2add4 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      sn F_2b014 D_2b014. renm.  (* [comment removed for export] *)
      stepb_ft F_2b018 D_2b018 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      sn F_2b01c D_2b01c. renm.  (* [comment removed for export] *)
      stepb_ft F_2b020 D_2b020 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      stepret F_2b024 D_2b024 (0x22b14 : word) ltac:(pin; first [reflexivity | bveq]). renm.  (* [comment removed for export] *)
      sn F_22b14 D_22b14. renm.  (* [comment removed for export] *)
      sn F_22b30 D_22b30. renm.  (* [comment removed for export] *)
      ld_step F_22b34 D_22b34 (word_to_le_bytes 8 (Z_to_bv 64 402376)) (Z_to_bv 64 402376) ltac:(rd_img img_30428_8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      stw F_22b38 D_22b38 (Z_to_bv 64 402377) (Z_to_bv 64 0) ltac:(ok_data). renm.  (* [comment removed for export] *)
      ld_step F_22b3c D_22b3c (guard_bytes R16) (canary_w R16) ltac:(RD_GUARD) ltac:(apply bytes_le_to_Z_u8; rewrite length_guard_bytes; lia). renm.  (* [comment removed for export] *)
      sn F_22b40 D_22b40. renm.  (* [comment removed for export] *)
      stw F_22b44 D_22b44 (Z_to_bv 64 270664) (canary_w R16) ltac:(ok_data). renm.  (* [comment removed for export] *)
      ld_step F_22b48 D_22b48 (word_to_le_bytes 8 (Z_to_bv 64 139736)) (Z_to_bv 64 139736) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      sv F_22b4c D_22b4c (Z_to_bv 64 (bv_unsigned sp0 - 416)). renm.  (* [comment removed for export] *)
      stepret F_22b50 D_22b50 (0x221d8 : word) ltac:(pin; first [reflexivity | bveq]). renm.  (* [comment removed for export] *)
      stn_done. apply mst_refl. }
    stn_final. apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 270680 ->
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
        getr regs' 4 = (Z_to_bv 64 270680) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 97124) ->
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
        G (mkst regs' (0x22398 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139728))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 402408))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139736))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 401792) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401808) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401800) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 402432) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 402440) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 270696) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 270672) (word_to_le_bytes 8 (Z_to_bv 64 270696))) (Z_to_bv 64 270480) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 402408) ([Z_to_bv 8 1])) (Z_to_bv 64 270520) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 270512) (word_to_le_bytes 4 tid)) (Z_to_bv 64 270632) (word_to_le_bytes 8 (Z_to_bv 64 402464))) (Z_to_bv 64 270600) (word_to_le_bytes 8 (Z_to_bv 64 270600))) (Z_to_bv 64 270488) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 270496) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 270504) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402376) (word_to_le_bytes 4 (v_lw RL))) (Z_to_bv 64 402380) (word_to_le_bytes 4 (v_lw RH))) (Z_to_bv 64 402377) ([Z_to_bv 8 0])) (Z_to_bv 64 270664) (word_to_le_bytes 8 CW))) rom)) ->
    G (mkst regs (0x221d8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139728))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 402408))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139736))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 401792) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401808) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401800) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 402432) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 402440) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 270696) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 270672) (word_to_le_bytes 8 (Z_to_bv 64 270696))) (Z_to_bv 64 270480) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 402408) ([Z_to_bv 8 1])) (Z_to_bv 64 270520) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 270512) (word_to_le_bytes 4 tid)) (Z_to_bv 64 270632) (word_to_le_bytes 8 (Z_to_bv 64 402464))) (Z_to_bv 64 270600) (word_to_le_bytes 8 (Z_to_bv 64 270600))) (Z_to_bv 64 270488) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 270496) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 270504) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402376) (word_to_le_bytes 4 (v_lw RL))) (Z_to_bv 64 402380) (word_to_le_bytes 4 (v_lw RH))) (Z_to_bv 64 402377) ([Z_to_bv 8 0])) (Z_to_bv 64 270664) (word_to_le_bytes 8 CW))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_221d8 D_221d8 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_221dc D_221dc (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      stepb_ft F_221e0 D_221e0 ltac:(pin; apply c_eq_refl). renm.  (* [comment removed for export] *)
      ld_step F_221e4 D_221e4 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity). renm.  (* [comment removed for export] *)
      ld_step F_221e8 D_221e8 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity). renm.  (* [comment removed for export] *)
      stepb_ft F_221ec D_221ec ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      ld_step F_221f0 D_221f0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      stepb_tk F_221f4 D_221f4 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      ld_step F_222d4 D_222d4 (word_to_le_bytes 8 (Z_to_bv 64 140140)) (Z_to_bv 64 140140) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_222d8 D_222d8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_222dc D_222dc (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_222e0 D_222e0 (word_to_le_bytes 8 (Z_to_bv 64 97124)) (Z_to_bv 64 97124) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      sv F_222e4 D_222e4 (Z_to_bv 64 (bv_unsigned sp0 - 32)). renm.  (* [comment removed for export] *)
      stepret F_222e8 D_222e8 (0x2236c : word) ltac:(pin; first [reflexivity | bveq]). renm.  (* [comment removed for export] *)
      sn F_2236c D_2236c. renm.  (* [comment removed for export] *)
      sn F_22370 D_22370. renm.  (* [comment removed for export] *)
      sn F_22374 D_22374. renm.  (* [comment removed for export] *)
      sv F_22378 D_22378 (argc_w av). renm.  (* [comment removed for export] *)
      sv F_2237c D_2237c (Z_to_bv 64 (bv_unsigned sp0 + 8)). renm.  (* [comment removed for export] *)
      ld_step F_22380 D_22380 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_22384 D_22384 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_22388 D_22388 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_2238c D_2238c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      sv F_22390 D_22390 (sp0). renm.  (* [comment removed for export] *)
      stepret F_22394 D_22394 (0x22398 : word) ltac:(pin; first [reflexivity | bveq]). renm.  (* [comment removed for export] *)
      stn_done. apply mst_refl. }
    stn_final. apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 270680 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 97124 ->
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
        getr regs' 1 = (Z_to_bv 64 140060) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 270680) ->
        getr regs' 8 = (Z_to_bv 64 197224) ->
        getr regs' 9 = (Z_to_bv 64 197216) ->
        getr regs' 18 = (Z_to_bv 64 97124) ->
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
        G (mkst regs' (0x17a60 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139728))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 402408))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139736))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 140236))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 401792) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401808) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401800) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 402432) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 402440) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 270696) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 270672) (word_to_le_bytes 8 (Z_to_bv 64 270696))) (Z_to_bv 64 270480) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 402408) ([Z_to_bv 8 1])) (Z_to_bv 64 270520) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 270512) (word_to_le_bytes 4 tid)) (Z_to_bv 64 270632) (word_to_le_bytes 8 (Z_to_bv 64 402464))) (Z_to_bv 64 270600) (word_to_le_bytes 8 (Z_to_bv 64 270600))) (Z_to_bv 64 270488) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 270496) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 270504) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402376) (word_to_le_bytes 4 (v_lw RL))) (Z_to_bv 64 402380) (word_to_le_bytes 4 (v_lw RH))) (Z_to_bv 64 402377) ([Z_to_bv 8 0])) (Z_to_bv 64 270664) (word_to_le_bytes 8 CW))) rom)) ->
    G (mkst regs (0x22398 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139728))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 402408))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139736))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 401792) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401808) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401800) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 402432) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 402440) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 270696) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 270672) (word_to_le_bytes 8 (Z_to_bv 64 270696))) (Z_to_bv 64 270480) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 402408) ([Z_to_bv 8 1])) (Z_to_bv 64 270520) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 270512) (word_to_le_bytes 4 tid)) (Z_to_bv 64 270632) (word_to_le_bytes 8 (Z_to_bv 64 402464))) (Z_to_bv 64 270600) (word_to_le_bytes 8 (Z_to_bv 64 270600))) (Z_to_bv 64 270488) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 270496) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 270504) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402376) (word_to_le_bytes 4 (v_lw RL))) (Z_to_bv 64 402380) (word_to_le_bytes 4 (v_lw RH))) (Z_to_bv 64 402377) ([Z_to_bv 8 0])) (Z_to_bv 64 270664) (word_to_le_bytes 8 CW))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_22398 D_22398 (Z_to_bv 64 (bv_unsigned sp0 - 48)). renm.  (* [comment removed for export] *)
      stw F_2239c D_2239c (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      stw F_223a0 D_223a0 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      stw F_223a4 D_223a4 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      stw F_223a8 D_223a8 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      stw F_223ac D_223ac (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      sv F_223b0 D_223b0 (Z_to_bv 64 (bv_unsigned sp0 + 8)). renm.  (* [comment removed for export] *)
      sv F_223b4 D_223b4 (argc_w av). renm.  (* [comment removed for export] *)
      sn F_223b8 D_223b8. renm.  (* [comment removed for export] *)
      stepiv F_223bc D_223bc (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc). renm.  (* [comment removed for export] *)
      sv F_223c0 D_223c0 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))). renm.  (* [comment removed for export] *)
      sv F_223c4 D_223c4 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))). renm.  (* [comment removed for export] *)
      sn F_223c8 D_223c8. renm.  (* [comment removed for export] *)
      sv F_222ec D_222ec (Z_to_bv 64 (bv_unsigned sp0 - 80)). renm.  (* [comment removed for export] *)
      stw F_222f0 D_222f0 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 140236) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      stw F_222f4 D_222f4 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      stw F_222f8 D_222f8 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      sn F_222fc D_222fc. renm.  (* [comment removed for export] *)
      stepret F_220bc D_220bc (0x22300 : word) ltac:(pin; first [reflexivity | bveq]). renm.  (* [comment removed for export] *)
      sn F_22300 D_22300. renm.  (* [comment removed for export] *)
      sn F_22304 D_22304. renm.  (* [comment removed for export] *)
      ld_step F_22308 D_22308 (word_to_le_bytes 8 (Z_to_bv 64 197224)) (Z_to_bv 64 197224) ltac:(rd_img img_30418_8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_2230c D_2230c (word_to_le_bytes 8 (Z_to_bv 64 197216)) (Z_to_bv 64 197216) ltac:(rd_img img_30420_8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      stepb_ft F_22310 D_22310 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      ld_step F_22314 D_22314 (word_to_le_bytes 8 (Z_to_bv 64 96864)) (Z_to_bv 64 96864) ltac:(rd_img img_30260_8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      stepjr F_22318 D_22318 (0x17a60 : word) ltac:(gres; pin; first [reflexivity | bveq]). renm.  (* [comment removed for export] *)
      stn_done. apply mst_refl. }
    stn_final. apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 140060 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 270680 ->
    getr regs 8 = Z_to_bv 64 197224 ->
    getr regs 9 = Z_to_bv 64 197216 ->
    getr regs 18 = Z_to_bv 64 97124 ->
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
        getr regs' 1 = (Z_to_bv 64 140252) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 270680) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 97124) ->
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
        G (mkst regs' (0x17b64 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139728))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 402408))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139736))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 140236))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 140060))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 197224))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 401792) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401808) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401800) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 402432) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 402440) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 270696) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 270672) (word_to_le_bytes 8 (Z_to_bv 64 270696))) (Z_to_bv 64 270480) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 402408) ([Z_to_bv 8 1])) (Z_to_bv 64 270520) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 270512) (word_to_le_bytes 4 tid)) (Z_to_bv 64 270632) (word_to_le_bytes 8 (Z_to_bv 64 402464))) (Z_to_bv 64 270600) (word_to_le_bytes 8 (Z_to_bv 64 270600))) (Z_to_bv 64 270488) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 270496) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 270504) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402376) (word_to_le_bytes 4 (v_lw RL))) (Z_to_bv 64 402380) (word_to_le_bytes 4 (v_lw RH))) (Z_to_bv 64 402377) ([Z_to_bv 8 0])) (Z_to_bv 64 270664) (word_to_le_bytes 8 CW)) (Z_to_bv 64 202672) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x17a60 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139728))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 402408))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 139736))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 140236))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 401792) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401808) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 401800) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 402432) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 402440) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 270696) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 270672) (word_to_le_bytes 8 (Z_to_bv 64 270696))) (Z_to_bv 64 270480) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 402408) ([Z_to_bv 8 1])) (Z_to_bv 64 270520) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 270512) (word_to_le_bytes 4 tid)) (Z_to_bv 64 270632) (word_to_le_bytes 8 (Z_to_bv 64 402464))) (Z_to_bv 64 270600) (word_to_le_bytes 8 (Z_to_bv 64 270600))) (Z_to_bv 64 270488) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 270496) (word_to_le_bytes 8 (Z_to_bv 64 270480))) (Z_to_bv 64 270504) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 402376) (word_to_le_bytes 4 (v_lw RL))) (Z_to_bv 64 402380) (word_to_le_bytes 4 (v_lw RH))) (Z_to_bv 64 402377) ([Z_to_bv 8 0])) (Z_to_bv 64 270664) (word_to_le_bytes 8 CW))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_17a60 D_17a60 (Z_to_bv 64 (bv_unsigned sp0 - 96)). renm.  (* [comment removed for export] *)
      stw F_17a64 D_17a64 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 140060) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      stw F_17a68 D_17a68 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 197224) ltac:(ok_win HJ). renm.  (* [comment removed for export] *)
      sv F_17a6c D_17a6c (Z_to_bv 64 (bv_unsigned sp0 - 80)). renm.  (* [comment removed for export] *)
      sn F_17a70 D_17a70. renm.  (* [comment removed for export] *)
      sn F_17a74 D_17a74. renm.  (* [comment removed for export] *)
      lb_step F_17a78 D_17a78 (Z_to_bv 8 0) ltac:(rd_img img_317b0_1). renm.  (* [comment removed for export] *)
      sn F_17a7c D_17a7c. renm.  (* [comment removed for export] *)
      stepb_tk F_17a80 D_17a80 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      sn F_17a8c D_17a8c. renm.  (* [comment removed for export] *)
      sn F_17a90 D_17a90. renm.  (* [comment removed for export] *)
      sn F_17a94 D_17a94. renm.  (* [comment removed for export] *)
      stw F_17a98 D_17a98 (Z_to_bv 64 202672) (Z_to_bv 64 1) ltac:(ok_data). renm.  (* [comment removed for export] *)
      sn F_17a9c D_17a9c. renm.  (* [comment removed for export] *)
      ld_step F_17aa0 D_17aa0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_303b0_8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      stepb_tk F_17aa4 D_17aa4 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      ld_step F_17ac4 D_17ac4 (word_to_le_bytes 8 (Z_to_bv 64 140060)) (Z_to_bv 64 140060) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_17ac8 D_17ac8 (word_to_le_bytes 8 (Z_to_bv 64 197224)) (Z_to_bv 64 197224) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      sv F_17acc D_17acc (Z_to_bv 64 (bv_unsigned sp0 - 80)). renm.  (* [comment removed for export] *)
      stepret F_17ad0 D_17ad0 (0x2231c : word) ltac:(pin; first [reflexivity | bveq]). renm.  (* [comment removed for export] *)
      sn F_2231c D_2231c. renm.  (* [comment removed for export] *)
      stepb_ft F_22320 D_22320 ltac:(pin; cond_compute). renm.  (* [comment removed for export] *)
      ld_step F_22324 D_22324 (word_to_le_bytes 8 (Z_to_bv 64 140236)) (Z_to_bv 64 140236) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_22328 D_22328 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      ld_step F_2232c D_2232c (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8). renm.  (* [comment removed for export] *)
      sv F_22330 D_22330 (Z_to_bv 64 (bv_unsigned sp0 - 48)). renm.  (* [comment removed for export] *)
      stepret F_22334 D_22334 (0x223cc : word) ltac:(pin; first [reflexivity | bveq]). renm.  (* [comment removed for export] *)
      sv F_223cc D_223cc (argc_w av). renm.  (* [comment removed for export] *)
      sv F_223d0 D_223d0 (Z_to_bv 64 (bv_unsigned sp0 + 8)). renm.  (* [comment removed for export] *)
      sv F_223d4 D_223d4 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))). renm.  (* [comment removed for export] *)
      stepjr F_223d8 D_223d8 (0x17b64 : word) ltac:(gres; pin; first [reflexivity | bveq]). renm.  (* [comment removed for export] *)
      stn_done. apply mst_refl. }
    stn_final. apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
