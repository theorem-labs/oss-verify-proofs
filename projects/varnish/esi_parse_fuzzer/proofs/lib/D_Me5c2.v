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
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk WalkTac MmapSim RefMocc D_Me92w D_co2ld.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require BWorld.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Me92w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_co2ld OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.BWorld.D_co8nq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup ::= repeat (repeat match goal with | [ H : 0 <= ?x < _ |- _ ] => destruct H; try (lazymatch type of H with | 0 <= x < _ => clear H end) end; repeat match goal with | [ H : ?x <> ?x -> _ |- _ ] => clear H | [ H : ?x < ?x -> _ |- _ ] => clear H | [ H : ?T -> _, H' : ~?T |- _ ] => clear H | [ H : ~?T -> _, H' : ?T |- _ ] => clear H | [ H : ?A -> ?x <> ?x -> _ |- _ ] => clear H | [ H : ?A -> ?x < ?x -> _ |- _ ] => clear H | [ H : ?A -> ?B -> ?x <> ?x -> _ |- _ ] => clear H | [ H : ?A -> ?B -> ?x < ?x -> _ |- _ ] => clear H | [ H : 0 < ?x -> _, H' : ?x < 0 -> _ |- _ ] => clear H H' | [ H : ?A -> 0 < ?x -> _, H' : ?A -> ?x < 0 -> _ |- _ ] => clear H H' end).
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
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
Local Ltac stn_open :=
  repeat match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end;
  try lazymatch goal with E : ?s = _ |- msteps _ _ ?s => rewrite E end.
Local Ltac stn_done :=
  repeat first [ match goal with H : stn_mark ?x |- ?g => lazymatch g with context [x] => unfold x end end
               | match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end ];
  try lazymatch goal with E : ?s = _ |- msteps _ _ ?s => rewrite E end;
  stn_wit.
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

Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc.solve_keeps ::=
  stn_wit; repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc.solve_keeps_cs ::=
  stn_wit;
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
(* [comment removed for export] *)
Section AL.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  #[local] Notation MK := (memk mem0 dst bs).
  #[local] Notation SB := (sb_ bs).
  #[local] Notation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  (* [comment removed for export] *)
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK"] Lemma b1_run : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    (0 <= k)%Z -> (k + 1 = n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b04c : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k Hret H1 H11 H13 Hk Hkn.
    stn_eexists. split.
    - mlbu F_2b04c D_2b04c k.                      (* [comment removed for export] *)
      renm. msb F_2b050 D_2b050 k ltac:(apply sb_val_plain).   (* [comment removed for export] *)
      stn_open. replace (k + 1)%Z with n by lia.
      renm. stepret F_2b054 D_2b054 ret ltac:(exact H1).
      stn_done. apply mst_refl.
    - solve_keeps.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK"] Lemma t2_run : forall regs (ret : word) k m,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z ->
    (Z.land m 2 = 0 \/ Z.land m 2 = 2)%Z -> (Z.land m 1 = 0 \/ Z.land m 1 = 1)%Z ->
    (0 <= k)%Z -> (n - k = Z.land m 2 + Z.land m 1)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b014 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k m Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem.
    - (* [comment removed for export] *)
      stn_eexists. split.
      + renm. stepn F_2b014 D_2b014.                          (* [comment removed for export] *)
        renm. stepb_ft F_2b018 D_2b018 ltac:(cond).           (* [comment removed for export] *)
        renm. stepn F_2b01c D_2b01c.                          (* [comment removed for export] *)
        renm. stepb_ft F_2b020 D_2b020 ltac:(cond).           (* [comment removed for export] *)
        renm. stepret F_2b024 D_2b024 ret ltac:(exact H1).
        stn_done. mk_eq. stn_done. apply mst_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b04c : word) (MK k) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b014 D_2b014.
          renm. stepb_ft F_2b018 D_2b018 ltac:(cond).
          renm. stepn F_2b01c D_2b01c.
          renm. stepb_tk F_2b020 D_2b020 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
      + cbv beta. (intros r1; (first [ intro dR_11; dand4 dR_11 as R1 R11 R13 K1 | intros (R1 & R11 & R13 & K1) ])).
        (first [ pose proof ((b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia))) as dR_1; dex1 dR_1 as r2; destruct dR_1 as [RUN K2] | pose proof ((b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia))) as dR_1; dand3 dR_1 as r2 RUN K2 | destruct (b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2) ]).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      stn_eexists. split.
      + renm. stepn F_2b014 D_2b014.
        renm. stepb_tk F_2b018 D_2b018 ltac:(cond).           (* [comment removed for export] *)
        mlbu F_2b028 D_2b028 k.                         (* [comment removed for export] *)
        mlbu F_2b02c D_2b02c (k + 1)%Z.                 (* [comment removed for export] *)
        renm. stepn F_2b030 D_2b030.                          (* [comment removed for export] *)
        renm. stepn F_2b034 D_2b034.                          (* [comment removed for export] *)
        renm. msb F_2b038 D_2b038 k ltac:(apply sb_val_plain).          (* [comment removed for export] *)
        renm. msb F_2b03c D_2b03c (k + 1)%Z ltac:(apply sb_val_plain).  (* [comment removed for export] *)
        renm. stepn F_2b040 D_2b040.                          (* [comment removed for export] *)
        renm. stepn F_2b044 D_2b044.                          (* [comment removed for export] *)
        renm. stepb_tk F_2b048 D_2b048 ltac:(cond).           (* [comment removed for export] *)
        renm. stepret F_2b024 D_2b024 ret ltac:(exact H1).
        stn_done. mk_eq. stn_done. apply mst_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b04c : word) (MK (k + 2)) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b014 D_2b014.
          renm. stepb_tk F_2b018 D_2b018 ltac:(cond).
          mlbu F_2b028 D_2b028 k.
          mlbu F_2b02c D_2b02c (k + 1)%Z.
          renm. stepn F_2b030 D_2b030.
          renm. stepn F_2b034 D_2b034.
          renm. msb F_2b038 D_2b038 k ltac:(apply sb_val_plain).
          renm. msb F_2b03c D_2b03c (k + 1)%Z ltac:(apply sb_val_plain).
          renm. stepn F_2b040 D_2b040.
          renm. stepn F_2b044 D_2b044.
          renm. stepb_ft F_2b048 D_2b048 ltac:(cond).         (* [comment removed for export] *)
          stn_done. mk_eq. stn_done. apply mst_refl.
        * cbv beta. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [gres; exact H1 | gres; rwH; rewrite ?at_addi; reflexivity
                                 | gres; rwH; rewrite ?at_addi; reflexivity | solve_keeps].
      + cbv beta. (intros r1; (first [ intro dR_12; dand4 dR_12 as R1 R11 R13 K1 | intros (R1 & R11 & R13 & K1) ])).
        (first [ pose proof ((b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia))) as dR_2; dex1 dR_2 as r2; destruct dR_2 as [RUN K2] | pose proof ((b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia))) as dR_2; dand3 dR_2 as r2 RUN K2 | destruct (b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2) ]).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK"] Lemma al4_run : forall regs (ret : word) k m,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2add0 : word) (MK k) rom)
                   (mkst regs' (0x2b014 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 4) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]].
    - stn_eexists. split.
      + renm. stepn F_2add0 D_2add0.                          (* [comment removed for export] *)
        renm. stepb_tk F_2add4 D_2add4 ltac:(cond).           (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - stn_eexists. split.
      + renm. stepn F_2add0 D_2add0.
        renm. stepb_ft F_2add4 D_2add4 ltac:(cond).           (* [comment removed for export] *)
        renm. mlw F_2add8 D_2add8 k.                          (* [comment removed for export] *)
        renm. stepn F_2addc D_2addc.                          (* [comment removed for export] *)
        renm. msw F_2ade0 D_2ade0 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).   (* [comment removed for export] *)
        renm. stepn F_2ade4 D_2ade4.                          (* [comment removed for export] *)
        renm. stepn F_2ade8 D_2ade8.                          (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK"] Lemma al8_run : forall regs (ret : word) k m e8,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (m < 8 /\ e8 = 0 \/ 8 <= m /\ e8 = 8 /\ k + 8 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2adb0 : word) (MK k) rom)
                   (mkst regs' (0x2add0 : word) (MK (k + e8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + e8)
      /\ getr regs' 13 = at_ dst (k + e8) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m e8 H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]]; subst e8.
    - stn_eexists. split.
      + renm. stepn F_2adb0 D_2adb0.                          (* [comment removed for export] *)
        renm. stepb_tk F_2adb4 D_2adb4 ltac:(cond).           (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - stn_eexists. split.
      + renm. stepn F_2adb0 D_2adb0.
        renm. stepb_ft F_2adb4 D_2adb4 ltac:(cond).
        renm. mlw F_2adb8 D_2adb8 k.                          (* [comment removed for export] *)
        renm. mlw F_2adbc D_2adbc (k + 4)%Z.                  (* [comment removed for export] *)
        renm. msw F_2adc0 D_2adc0 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).         (* [comment removed for export] *)
        renm. msw F_2adc4 D_2adc4 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        renm. stepn F_2adc8 D_2adc8.                          (* [comment removed for export] *)
        renm. stepn F_2adcc D_2adcc.                          (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hn0 HOK"] Lemma al_loop : forall (q : nat) regs (ret : word) k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 14 = Z_to_bv 64 15 ->
    (0 <= k)%Z -> (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2ad80 : word) (MK k) rom)
                   (mkst regs' (0x2adb0 : word) (MK (k + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 13 = at_ dst (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret k H1 H11 H13 H12 H14 Hk Hq.
    - (* [comment removed for export] *)
      stn_eexists. split.
      + renm. mlw F_2ad80 D_2ad80 k.                          (* [comment removed for export] *)
        renm. mlw F_2ad84 D_2ad84 (k + 4)%Z.                  (* [comment removed for export] *)
        renm. mlw F_2ad88 D_2ad88 (k + 8)%Z.                  (* [comment removed for export] *)
        renm. mlw F_2ad8c D_2ad8c (k + 12)%Z.                 (* [comment removed for export] *)
        renm. stepn F_2ad90 D_2ad90.                          (* [comment removed for export] *)
        renm. stepn F_2ad94 D_2ad94.                          (* [comment removed for export] *)
        renm. msw F_2ad98 D_2ad98 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).          (* [comment removed for export] *)
        renm. msw F_2ad9c D_2ad9c (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        renm. msw F_2ada0 D_2ada0 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        renm. msw F_2ada4 D_2ada4 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        renm. stepn F_2ada8 D_2ada8.                          (* [comment removed for export] *)
        renm. stepb_ft F_2adac D_2adac ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
        * stn_open. unfold v_addi. unorm. f_equal. lia.
        * solve_keeps.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x2ad80 : word) (MK (k + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + stn_eexists. split.
        * renm. mlw F_2ad80 D_2ad80 k.
          renm. mlw F_2ad84 D_2ad84 (k + 4)%Z.
          renm. mlw F_2ad88 D_2ad88 (k + 8)%Z.
          renm. mlw F_2ad8c D_2ad8c (k + 12)%Z.
          renm. stepn F_2ad90 D_2ad90.
          renm. stepn F_2ad94 D_2ad94.
          renm. msw F_2ad98 D_2ad98 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          renm. msw F_2ad9c D_2ad9c (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          renm. msw F_2ada0 D_2ada0 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          renm. msw F_2ada4 D_2ada4 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          renm. stepn F_2ada8 D_2ada8.
          renm. stepb_tk F_2adac D_2adac ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          stn_done. mk_eq. stn_done. apply mst_refl.
        * cbv beta. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
          -- stn_open. unfold v_addi. unorm. f_equal. lia.
          -- solve_keeps.
      + cbv beta. (intros r1; (first [ intro dR_13; dand6 dR_13 as R1 R11 R13 R12 R14 K1 | intros (R1 & R11 & R13 & R12 & R14 & K1) ])).
        (first [ pose proof ((IH r1 ret (k + 16)%Z R1 R11 R13 R12 R14 ltac:(lia) ltac:(lia))) as dR_3; dex1 dR_3 as r2; destruct dR_3 as [RUN P] | pose proof ((IH r1 ret (k + 16)%Z R1 R11 R13 R12 R14 ltac:(lia) ltac:(lia))) as dR_3; dand3 dR_3 as r2 RUN P | destruct (IH r1 ret (k + 16)%Z R1 R11 R13 R12 R14 ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. split.
        * stn_open. replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia. exact RUN.
        * stn_open. replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
          decompose [and] P. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  #[using="Hn0 HOK"] Lemma al16_run : forall regs (ret : word) k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2ad74 : word) (MK k) rom)
                   (mkst regs' (0x2adb0 : word) (MK (n - (n - k) mod 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (n - k) mod 16)
      /\ getr regs' 13 = at_ dst (n - (n - k) mod 16)
      /\ getr regs' 12 = Z_to_bv 64 ((n - k) mod 16) /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 Hk.
    destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
    - (* [comment removed for export] *)
      stn_eexists. split.
      + renm. stepn F_2ad74 D_2ad74.                          (* [comment removed for export] *)
        renm. stepb_tk F_2ad78 D_2ad78 ltac:(cond).           (* [comment removed for export] *)
        stn_open. replace (n - (n - k) mod 16)%Z with k by (rewrite Z.mod_small; lia).
        stn_done. apply mst_refl.
      + stn_open. rewrite (Z.mod_small (n - k) 16) by lia. stn_open. replace (n - (n - k))%Z with k by lia.
        OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; try reflexivity. solve_keeps.
    - set (q := Z.to_nat ((n - k) / 16 - 1)).
      assert (Hq : (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z).
      { subst q. stn_open. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
        pose proof (Z.div_mod (n - k) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)). lia. }
      assert (Hk' : (k + 16 * (Z.of_nat q + 1) = n - (n - k) mod 16)%Z).
      { subst q. stn_open. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
        pose proof (Z.div_mod (n - k) 16 ltac:(lia)). lia. }
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2ad80 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
                         /\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2ad74 D_2ad74.                        (* [comment removed for export] *)
          renm. stepb_ft F_2ad78 D_2ad78 ltac:(cond).         (* [comment removed for export] *)
          renm. stepn F_2ad7c D_2ad7c.                        (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; try reflexivity. solve_keeps.
      + cbv beta. (intros r1; (first [ intro dR_14; dand6 dR_14 as R1 R11 R13 R12 R14 K1 | intros (R1 & R11 & R13 & R12 & R14 & K1) ])).
        (first [ pose proof ((al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq)) as dR_4; dex1 dR_4 as r2; destruct dR_4 as [RUN P] | pose proof ((al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq)) as dR_4; dand3 dR_4 as r2 RUN P | destruct (al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq) as (r2 & RUN & P) ]).
        exists r2. stn_open. rewrite <- Hk'. stn_open. replace ((n - k) mod 16)%Z with (n - (k + 16 * (Z.of_nat q + 1)))%Z by lia.
        decompose [and] P. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

End AL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
