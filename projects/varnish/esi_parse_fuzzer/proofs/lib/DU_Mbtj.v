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
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk WalkTac MmapSim RefMocc DU_M0r3.

Module DU_Mbio.
(* [comment removed for export] *)
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
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk WalkTac MmapSim RefMocc DU_M0r3 DU_cij8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_M0r3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_cij8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.DU_cg5g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
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
      msteps RSEGS (mkst regs (0x2b3ec : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k Hret H1 H11 H13 Hk Hkn.
    stn_eexists. split.
    - mlbu F_2b3ec D_2b3ec k.                      (* [comment removed for export] *)
      renm. msb F_2b3f0 D_2b3f0 k ltac:(apply sb_val_plain).   (* [comment removed for export] *)
      stn_open. replace (k + 1)%Z with n by lia.
      renm. stepret F_2b3f4 D_2b3f4 ret ltac:(exact H1).
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
      msteps RSEGS (mkst regs (0x2b3b4 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k m Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem.
    - (* [comment removed for export] *)
      stn_eexists. split.
      + renm. stepn F_2b3b4 D_2b3b4.                          (* [comment removed for export] *)
        renm. stepb_ft F_2b3b8 D_2b3b8 ltac:(cond).           (* [comment removed for export] *)
        renm. stepn F_2b3bc D_2b3bc.                          (* [comment removed for export] *)
        renm. stepb_ft F_2b3c0 D_2b3c0 ltac:(cond).           (* [comment removed for export] *)
        renm. stepret F_2b3c4 D_2b3c4 ret ltac:(exact H1).
        stn_done. mk_eq. stn_done. apply mst_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b3ec : word) (MK k) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b3b4 D_2b3b4.
          renm. stepb_ft F_2b3b8 D_2b3b8 ltac:(cond).
          renm. stepn F_2b3bc D_2b3bc.
          renm. stepb_tk F_2b3c0 D_2b3c0 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
      + cbv beta. (intros r1; (first [ intro dR_11; dand4 dR_11 as R1 R11 R13 K1 | intros (R1 & R11 & R13 & K1) ])).
        (first [ pose proof ((b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia))) as dR_1; dex1 dR_1 as r2; destruct dR_1 as [RUN K2] | pose proof ((b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia))) as dR_1; dand3 dR_1 as r2 RUN K2 | destruct (b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2) ]).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      stn_eexists. split.
      + renm. stepn F_2b3b4 D_2b3b4.
        renm. stepb_tk F_2b3b8 D_2b3b8 ltac:(cond).           (* [comment removed for export] *)
        mlbu F_2b3c8 D_2b3c8 k.                         (* [comment removed for export] *)
        mlbu F_2b3cc D_2b3cc (k + 1)%Z.                 (* [comment removed for export] *)
        renm. stepn F_2b3d0 D_2b3d0.                          (* [comment removed for export] *)
        renm. stepn F_2b3d4 D_2b3d4.                          (* [comment removed for export] *)
        renm. msb F_2b3d8 D_2b3d8 k ltac:(apply sb_val_plain).          (* [comment removed for export] *)
        renm. msb F_2b3dc D_2b3dc (k + 1)%Z ltac:(apply sb_val_plain).  (* [comment removed for export] *)
        renm. stepn F_2b3e0 D_2b3e0.                          (* [comment removed for export] *)
        renm. stepn F_2b3e4 D_2b3e4.                          (* [comment removed for export] *)
        renm. stepb_tk F_2b3e8 D_2b3e8 ltac:(cond).           (* [comment removed for export] *)
        renm. stepret F_2b3c4 D_2b3c4 ret ltac:(exact H1).
        stn_done. mk_eq. stn_done. apply mst_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b3ec : word) (MK (k + 2)) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b3b4 D_2b3b4.
          renm. stepb_tk F_2b3b8 D_2b3b8 ltac:(cond).
          mlbu F_2b3c8 D_2b3c8 k.
          mlbu F_2b3cc D_2b3cc (k + 1)%Z.
          renm. stepn F_2b3d0 D_2b3d0.
          renm. stepn F_2b3d4 D_2b3d4.
          renm. msb F_2b3d8 D_2b3d8 k ltac:(apply sb_val_plain).
          renm. msb F_2b3dc D_2b3dc (k + 1)%Z ltac:(apply sb_val_plain).
          renm. stepn F_2b3e0 D_2b3e0.
          renm. stepn F_2b3e4 D_2b3e4.
          renm. stepb_ft F_2b3e8 D_2b3e8 ltac:(cond).         (* [comment removed for export] *)
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
      msteps RSEGS (mkst regs (0x2b170 : word) (MK k) rom)
                   (mkst regs' (0x2b3b4 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 4) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]].
    - stn_eexists. split.
      + renm. stepn F_2b170 D_2b170.                          (* [comment removed for export] *)
        renm. stepb_tk F_2b174 D_2b174 ltac:(cond).           (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - stn_eexists. split.
      + renm. stepn F_2b170 D_2b170.
        renm. stepb_ft F_2b174 D_2b174 ltac:(cond).           (* [comment removed for export] *)
        renm. mlw F_2b178 D_2b178 k.                          (* [comment removed for export] *)
        renm. stepn F_2b17c D_2b17c.                          (* [comment removed for export] *)
        renm. msw F_2b180 D_2b180 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).   (* [comment removed for export] *)
        renm. stepn F_2b184 D_2b184.                          (* [comment removed for export] *)
        renm. stepn F_2b188 D_2b188.                          (* [comment removed for export] *)
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
      msteps RSEGS (mkst regs (0x2b150 : word) (MK k) rom)
                   (mkst regs' (0x2b170 : word) (MK (k + e8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + e8)
      /\ getr regs' 13 = at_ dst (k + e8) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m e8 H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]]; subst e8.
    - stn_eexists. split.
      + renm. stepn F_2b150 D_2b150.                          (* [comment removed for export] *)
        renm. stepb_tk F_2b154 D_2b154 ltac:(cond).           (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - stn_eexists. split.
      + renm. stepn F_2b150 D_2b150.
        renm. stepb_ft F_2b154 D_2b154 ltac:(cond).
        renm. mlw F_2b158 D_2b158 k.                          (* [comment removed for export] *)
        renm. mlw F_2b15c D_2b15c (k + 4)%Z.                  (* [comment removed for export] *)
        renm. msw F_2b160 D_2b160 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).         (* [comment removed for export] *)
        renm. msw F_2b164 D_2b164 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        renm. stepn F_2b168 D_2b168.                          (* [comment removed for export] *)
        renm. stepn F_2b16c D_2b16c.                          (* [comment removed for export] *)
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
      msteps RSEGS (mkst regs (0x2b120 : word) (MK k) rom)
                   (mkst regs' (0x2b150 : word) (MK (k + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 13 = at_ dst (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret k H1 H11 H13 H12 H14 Hk Hq.
    - (* [comment removed for export] *)
      stn_eexists. split.
      + renm. mlw F_2b120 D_2b120 k.                          (* [comment removed for export] *)
        renm. mlw F_2b124 D_2b124 (k + 4)%Z.                  (* [comment removed for export] *)
        renm. mlw F_2b128 D_2b128 (k + 8)%Z.                  (* [comment removed for export] *)
        renm. mlw F_2b12c D_2b12c (k + 12)%Z.                 (* [comment removed for export] *)
        renm. stepn F_2b130 D_2b130.                          (* [comment removed for export] *)
        renm. stepn F_2b134 D_2b134.                          (* [comment removed for export] *)
        renm. msw F_2b138 D_2b138 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).          (* [comment removed for export] *)
        renm. msw F_2b13c D_2b13c (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        renm. msw F_2b140 D_2b140 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        renm. msw F_2b144 D_2b144 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        renm. stepn F_2b148 D_2b148.                          (* [comment removed for export] *)
        renm. stepb_ft F_2b14c D_2b14c ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
        * stn_open. unfold v_addi. unorm. f_equal. lia.
        * solve_keeps.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b120 : word) (MK (k + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + stn_eexists. split.
        * renm. mlw F_2b120 D_2b120 k.
          renm. mlw F_2b124 D_2b124 (k + 4)%Z.
          renm. mlw F_2b128 D_2b128 (k + 8)%Z.
          renm. mlw F_2b12c D_2b12c (k + 12)%Z.
          renm. stepn F_2b130 D_2b130.
          renm. stepn F_2b134 D_2b134.
          renm. msw F_2b138 D_2b138 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          renm. msw F_2b13c D_2b13c (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          renm. msw F_2b140 D_2b140 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          renm. msw F_2b144 D_2b144 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          renm. stepn F_2b148 D_2b148.
          renm. stepb_tk F_2b14c D_2b14c ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
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
      msteps RSEGS (mkst regs (0x2b114 : word) (MK k) rom)
                   (mkst regs' (0x2b150 : word) (MK (n - (n - k) mod 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (n - k) mod 16)
      /\ getr regs' 13 = at_ dst (n - (n - k) mod 16)
      /\ getr regs' 12 = Z_to_bv 64 ((n - k) mod 16) /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 Hk.
    destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
    - (* [comment removed for export] *)
      stn_eexists. split.
      + renm. stepn F_2b114 D_2b114.                          (* [comment removed for export] *)
        renm. stepb_tk F_2b118 D_2b118 ltac:(cond).           (* [comment removed for export] *)
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
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b120 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
                         /\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b114 D_2b114.                        (* [comment removed for export] *)
          renm. stepb_ft F_2b118 D_2b118 ltac:(cond).         (* [comment removed for export] *)
          renm. stepn F_2b11c D_2b11c.                        (* [comment removed for export] *)
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
End DU_Mbio.


Module DU_M9cn.
(* [comment removed for export] *)
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
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk WalkTac MmapSim RefMocc DU_M0r3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_cij8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_M0r3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Mbtj.DU_Mbio OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_cij8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.DU_cg5g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
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

Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc.solve_keeps ::=
  stn_wit; repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc.solve_keeps_cs ::=
  stn_wit;
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
(* [comment removed for export] *)
Section MIS.
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

  Ltac post := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac sbp := apply sb_val_plain.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK"] Lemma b4_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b388 : word) (MK k) rom) (mkst regs' (0x2b3b4 : word) (MK (k + 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. stn_eexists. split.
    - mlbu F_2b388 D_2b388 k. mlbu F_2b38c D_2b38c (k+1)%Z. mlbu F_2b390 D_2b390 (k+2)%Z. mlbu F_2b394 D_2b394 (k+3)%Z.
      renm. stepn F_2b398 D_2b398.                            (* [comment removed for export] *)
      renm. stepn F_2b39c D_2b39c.                            (* [comment removed for export] *)
      renm. msb F_2b3a0 D_2b3a0 k ltac:(sbp). renm. msb F_2b3a4 D_2b3a4 (k+1)%Z ltac:(sbp).
      renm. msb F_2b3a8 D_2b3a8 (k+2)%Z ltac:(sbp). renm. msb F_2b3ac D_2b3ac (k+3)%Z ltac:(sbp).
      renm. stepn F_2b3b0 D_2b3b0.                            (* [comment removed for export] *)
      stn_done. mk_eq. stn_done. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK"] Lemma b8_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 8 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b334 : word) (MK k) rom) (mkst regs' (0x2b380 : word) (MK (k + 8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. stn_eexists. split.
    - mlbu F_2b334 D_2b334 k. mlbu F_2b338 D_2b338 (k+1)%Z. mlbu F_2b33c D_2b33c (k+2)%Z. mlbu F_2b340 D_2b340 (k+3)%Z.
      mlbu F_2b344 D_2b344 (k+4)%Z. mlbu F_2b348 D_2b348 (k+5)%Z. mlbu F_2b34c D_2b34c (k+6)%Z. mlbu F_2b350 D_2b350 (k+7)%Z.
      renm. stepn F_2b354 D_2b354.                            (* [comment removed for export] *)
      renm. msb F_2b358 D_2b358 k ltac:(sbp). renm. msb F_2b35c D_2b35c (k+1)%Z ltac:(sbp).
      renm. msb F_2b360 D_2b360 (k+2)%Z ltac:(sbp). renm. msb F_2b364 D_2b364 (k+3)%Z ltac:(sbp).
      renm. stepn F_2b368 D_2b368.                            (* [comment removed for export] *)
      renm. msb F_2b36c D_2b36c (k+4)%Z ltac:(sbp). renm. msb F_2b370 D_2b370 (k+5)%Z ltac:(sbp).
      renm. msb F_2b374 D_2b374 (k+6)%Z ltac:(sbp). renm. msb F_2b378 D_2b378 (k+7)%Z ltac:(sbp).
      renm. stepn F_2b37c D_2b37c.                            (* [comment removed for export] *)
      stn_done. mk_eq. stn_done. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK"] Lemma b16_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 16 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b2a0 : word) (MK k) rom) (mkst regs' (0x2b32c : word) (MK (k + 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. stn_eexists. split.
    - mlbu F_2b2a0 D_2b2a0 k. mlbu F_2b2a4 D_2b2a4 (k+1)%Z. mlbu F_2b2a8 D_2b2a8 (k+2)%Z. mlbu F_2b2ac D_2b2ac (k+3)%Z.
      mlbu F_2b2b0 D_2b2b0 (k+4)%Z. mlbu F_2b2b4 D_2b2b4 (k+5)%Z. mlbu F_2b2b8 D_2b2b8 (k+6)%Z. mlbu F_2b2bc D_2b2bc (k+7)%Z.
      renm. msb F_2b2c0 D_2b2c0 k ltac:(sbp). renm. msb F_2b2c4 D_2b2c4 (k+1)%Z ltac:(sbp).
      renm. msb F_2b2c8 D_2b2c8 (k+2)%Z ltac:(sbp). renm. msb F_2b2cc D_2b2cc (k+3)%Z ltac:(sbp).
      mlbu F_2b2d0 D_2b2d0 (k+8)%Z. mlbu F_2b2d4 D_2b2d4 (k+9)%Z. mlbu F_2b2d8 D_2b2d8 (k+10)%Z. mlbu F_2b2dc D_2b2dc (k+11)%Z.
      renm. msb F_2b2e0 D_2b2e0 (k+4)%Z ltac:(sbp). renm. msb F_2b2e4 D_2b2e4 (k+5)%Z ltac:(sbp).
      renm. msb F_2b2e8 D_2b2e8 (k+6)%Z ltac:(sbp). renm. msb F_2b2ec D_2b2ec (k+7)%Z ltac:(sbp).
      mlbu F_2b2f0 D_2b2f0 (k+12)%Z. mlbu F_2b2f4 D_2b2f4 (k+13)%Z. mlbu F_2b2f8 D_2b2f8 (k+14)%Z. mlbu F_2b2fc D_2b2fc (k+15)%Z.
      renm. stepn F_2b300 D_2b300.                            (* [comment removed for export] *)
      renm. msb F_2b304 D_2b304 (k+8)%Z ltac:(sbp). renm. msb F_2b308 D_2b308 (k+9)%Z ltac:(sbp).
      renm. msb F_2b30c D_2b30c (k+10)%Z ltac:(sbp). renm. msb F_2b310 D_2b310 (k+11)%Z ltac:(sbp).
      renm. stepn F_2b314 D_2b314.                            (* [comment removed for export] *)
      renm. msb F_2b318 D_2b318 (k+12)%Z ltac:(sbp). renm. msb F_2b31c D_2b31c (k+13)%Z ltac:(sbp).
      renm. msb F_2b320 D_2b320 (k+14)%Z ltac:(sbp). renm. msb F_2b324 D_2b324 (k+15)%Z ltac:(sbp).
      renm. stepn F_2b328 D_2b328.                            (* [comment removed for export] *)
      stn_done. mk_eq. stn_done. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK"] Lemma t4_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b05c : word) (MK k) rom) (mkst regs' (0x2b3b4 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - stn_eexists. split.
      + renm. stepn F_2b05c D_2b05c.                          (* [comment removed for export] *)
        renm. stepb_ft F_2b060 D_2b060 ltac:(cond).           (* [comment removed for export] *)
        renm. stepn F_2b064 D_2b064.                          (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + post.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b388 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b05c D_2b05c.
          renm. stepb_tk F_2b060 D_2b060 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_13; dand5 dR_13 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        (first [ pose proof ((b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_1; dex1 dR_1 as r2; destruct dR_1 as [RUN P] | pose proof ((b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_1; dand3 dR_1 as r2 RUN P | destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK"] Lemma b8_tail : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b380 : word) (MK k) rom) (mkst regs' (0x2b3b4 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - stn_eexists. split.
      + renm. stepn F_2b380 D_2b380.                          (* [comment removed for export] *)
        renm. stepb_tk F_2b384 D_2b384 ltac:(cond).           (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + post.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b388 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b380 D_2b380.
          renm. stepb_ft F_2b384 D_2b384 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_14; dand5 dR_14 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        (first [ pose proof ((b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_2; dex1 dR_2 as r2; destruct dR_2 as [RUN P] | pose proof ((b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_2; dand3 dR_2 as r2 RUN P | destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK"] Lemma t8_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
    (k + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b054 : word) (MK k) rom)
                   (mkst regs' (0x2b3b4 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b05c : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b054 D_2b054.                        (* [comment removed for export] *)
          renm. stepb_ft F_2b058 D_2b058 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_15; dand5 dR_15 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        (first [ pose proof ((t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia))) as dR_3; dex1 dR_3 as r2; destruct dR_3 as [RUN P] | pose proof ((t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia))) as dR_3; dand3 dR_3 as r2 RUN P | destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b334 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b054 D_2b054.
          renm. stepb_tk F_2b058 D_2b058 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_16; dand5 dR_16 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b380 : word) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * (first [ pose proof ((b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_4; dex1 dR_4 as r2; destruct dR_4 as [RUN P] | pose proof ((b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_4; dand3 dR_4 as r2 RUN P | destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2; (first [ intro dR_17; dand5 dR_17 as S1 S11 S13 S12 K2 | intros (S1 & S11 & S13 & S12 & K2) ])).
          (first [ pose proof ((b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia))) as dR_5; dex1 dR_5 as r3; destruct dR_5 as [RUN P] | pose proof ((b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia))) as dR_5; dand3 dR_5 as r3 RUN P | destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P) ]).
          exists r3. stn_open. rewrite HL8. stn_open. replace (k + 8 + Z.land m 4)%Z with (k + 8 + Z.land m 4)%Z by lia.
          split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK"] Lemma b16_tail : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
    (k + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b32c : word) (MK k) rom)
                   (mkst regs' (0x2b3b4 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b05c : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b32c D_2b32c.                        (* [comment removed for export] *)
          renm. stepb_tk F_2b330 D_2b330 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_18; dand5 dR_18 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        (first [ pose proof ((t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia))) as dR_6; dex1 dR_6 as r2; destruct dR_6 as [RUN P] | pose proof ((t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia))) as dR_6; dand3 dR_6 as r2 RUN P | destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b334 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b32c D_2b32c.
          renm. stepb_ft F_2b330 D_2b330 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_19; dand5 dR_19 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b380 : word) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * (first [ pose proof ((b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_7; dex1 dR_7 as r2; destruct dR_7 as [RUN P] | pose proof ((b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_7; dand3 dR_7 as r2 RUN P | destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2; (first [ intro dR_20; dand5 dR_20 as S1 S11 S13 S12 K2 | intros (S1 & S11 & S13 & S12 & K2) ])).
          (first [ pose proof ((b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia))) as dR_8; dex1 dR_8 as r3; destruct dR_8 as [RUN P] | pose proof ((b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia))) as dR_8; dand3 dR_8 as r3 RUN P | destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P) ]).
          exists r3. stn_open. rewrite HL8. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK"] Lemma t16_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 32)%Z -> (0 <= k)%Z ->
    (k + Z.land m 16 + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b04c : word) (MK k) rom)
                   (mkst regs' (0x2b3b4 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk Hkn.
    (first [ pose proof ((bits_lt32 m Hm)) as dR_9; dand6 dR_9 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
    assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b054 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b04c D_2b04c.                        (* [comment removed for export] *)
          renm. stepb_ft F_2b050 D_2b050 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_21; dand5 dR_21 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        (first [ pose proof ((t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia))) as dR_10; dex1 dR_10 as r2; destruct dR_10 as [RUN P] | pose proof ((t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia))) as dR_10; dand3 dR_10 as r2 RUN P | destruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b2a0 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b04c D_2b04c.
          renm. stepb_tk F_2b050 D_2b050 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_22; dand5 dR_22 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b32c : word) (MK (k + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * (first [ pose proof ((b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_11; dex1 dR_11 as r2; destruct dR_11 as [RUN P] | pose proof ((b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_11; dand3 dR_11 as r2 RUN P | destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2; (first [ intro dR_23; dand5 dR_23 as S1 S11 S13 S12 K2 | intros (S1 & S11 & S13 & S12 & K2) ])).
          (first [ pose proof ((b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia))) as dR_12; dex1 dR_12 as r3; destruct dR_12 as [RUN P] | pose proof ((b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia))) as dR_12; dand3 dR_12 as r3 RUN P | destruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P) ]).
          exists r3. stn_open. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

End MIS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End DU_M9cn.


Module DU_Mdnl.
(* [comment removed for export] *)
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
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk WalkTac MmapSim RefMocc DU_M0r3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_cij8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_M0r3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Mbtj.DU_Mbio OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Mbtj.DU_M9cn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_cij8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.DU_cg5g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
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

Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc.solve_keeps ::=
  stn_wit; repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc.solve_keeps_cs ::=
  stn_wit;
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
(* [comment removed for export] *)
Section C1.
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

  Ltac post := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac m24 := eapply (merge_s24 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  (* [comment removed for export] *)
  #[using="Hn0 HOK"] Lemma c1_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b068 : word) (MK k) rom) (mkst regs' (0x2b234 : word) (MK (k + 3)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 3)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 3)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 16 /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. stn_eexists. split.
    - renm. mlw F_2b068 D_2b068 k.                            (* [comment removed for export] *)
      renm. stepn F_2b06c D_2b06c.                            (* [comment removed for export] *)
      renm. stepb_ft F_2b070 D_2b070 ltac:(cond).             (* [comment removed for export] *)
      renm. stepn F_2b074 D_2b074.                            (* [comment removed for export] *)
      renm. stepb_tk F_2b078 D_2b078 ltac:(cond).             (* [comment removed for export] *)
      renm. stepn F_2b210 D_2b210.                            (* [comment removed for export] *)
      renm. stepn F_2b214 D_2b214.                            (* [comment removed for export] *)
      renm. stepn F_2b218 D_2b218.                            (* [comment removed for export] *)
      renm. msb F_2b21c D_2b21c k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).         (* [comment removed for export] *)
      renm. msb F_2b220 D_2b220 (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
      renm. msb F_2b224 D_2b224 (k + 2)%Z ltac:(eapply (sb_val_srli16 _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
      renm. stepn F_2b228 D_2b228.                            (* [comment removed for export] *)
      renm. stepn F_2b22c D_2b22c.                            (* [comment removed for export] *)
      renm. stepn F_2b230 D_2b230.                            (* [comment removed for export] *)
      stn_done. mk_eq. stn_done. apply mst_refl.
    - post. stn_open. unfold v_addi. unorm. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Hn0 HOK"] Lemma c1_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 16 ->
    (ja = kk + 13)%Z -> (jw = kk - 3)%Z -> (3 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 1 <= n - kk < 16 * (Z.of_nat q + 1) + 17)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b234 : word) (MK kk) rom)
                   (mkst regs' (0x2b294 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 13)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - stn_eexists. split.
      + renm. stepn F_2b234 D_2b234.                          (* [comment removed for export] *)
        renm. mlw F_2b238 D_2b238 (kk + 1)%Z.                 (* [comment removed for export] *)
        renm. mlw F_2b23c D_2b23c (kk + 5)%Z.                 (* [comment removed for export] *)
        renm. mlw F_2b240 D_2b240 (kk + 9)%Z.                 (* [comment removed for export] *)
        renm. mlw F_2b244 D_2b244 (kk + 13)%Z.                (* [comment removed for export] *)
        renm. stepn F_2b248 D_2b248. renm. stepn F_2b24c D_2b24c. renm. stepn F_2b250 D_2b250.
        renm. stepn F_2b254 D_2b254. renm. stepn F_2b258 D_2b258. renm. stepn F_2b25c D_2b25c.
        renm. stepn F_2b260 D_2b260. renm. stepn F_2b264 D_2b264. renm. stepn F_2b268 D_2b268.
        renm. stepn F_2b26c D_2b26c. renm. stepn F_2b270 D_2b270.
        renm. stepn F_2b274 D_2b274.                          (* [comment removed for export] *)
        renm. msw F_2b278 D_2b278 kk ltac:(m24).
        renm. msw F_2b27c D_2b27c (kk + 4)%Z ltac:(m24).
        renm. msw F_2b280 D_2b280 (kk + 8)%Z ltac:(m24).
        renm. msw F_2b284 D_2b284 (kk + 12)%Z ltac:(m24).
        renm. stepn F_2b288 D_2b288.                          (* [comment removed for export] *)
        renm. stepn F_2b28c D_2b28c.                          (* [comment removed for export] *)
        renm. stepb_ft F_2b290 D_2b290 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + post. stn_open. unfold v_addi. unorm. f_equal. lia.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b234 : word) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 13) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 13) 4)
                         /\ getr r 15 = Z_to_bv 64 16 /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b234 D_2b234.
          renm. mlw F_2b238 D_2b238 (kk + 1)%Z.
          renm. mlw F_2b23c D_2b23c (kk + 5)%Z.
          renm. mlw F_2b240 D_2b240 (kk + 9)%Z.
          renm. mlw F_2b244 D_2b244 (kk + 13)%Z.
          renm. stepn F_2b248 D_2b248. renm. stepn F_2b24c D_2b24c. renm. stepn F_2b250 D_2b250.
          renm. stepn F_2b254 D_2b254. renm. stepn F_2b258 D_2b258. renm. stepn F_2b25c D_2b25c.
          renm. stepn F_2b260 D_2b260. renm. stepn F_2b264 D_2b264. renm. stepn F_2b268 D_2b268.
          renm. stepn F_2b26c D_2b26c. renm. stepn F_2b270 D_2b270.
          renm. stepn F_2b274 D_2b274.
          renm. msw F_2b278 D_2b278 kk ltac:(m24).
          renm. msw F_2b27c D_2b27c (kk + 4)%Z ltac:(m24).
          renm. msw F_2b280 D_2b280 (kk + 8)%Z ltac:(m24).
          renm. msw F_2b284 D_2b284 (kk + 12)%Z ltac:(m24).
          renm. stepn F_2b288 D_2b288.
          renm. stepn F_2b28c D_2b28c.
          renm. stepb_tk F_2b290 D_2b290 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          stn_done. mk_eq. stn_done. apply mst_refl.
        * cbv beta. post. stn_open. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. (intros r1; (first [ intro dR_10; dand7 dR_10 as R1 R11 R13 R12 R14 R15 K1 | intros (R1 & R11 & R13 & R12 & R14 & R15 & K1) ])).
        (first [ pose proof ((IH r1 ret (kk + 16)%Z (kk + 16 + 13)%Z (kk + 13)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_1; dex1 dR_1 as r2; destruct dR_1 as [RUN P] | pose proof ((IH r1 ret (kk + 16)%Z (kk + 16 + 13)%Z (kk + 13)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_1; dand3 dR_1 as r2 RUN P | destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 13)%Z (kk + 13)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK"] Lemma c1_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 13) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps RSEGS (mkst regs (0x2b294 : word) (MK kk) rom)
                   (mkst regs' (0x2b3b4 : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
    (first [ pose proof ((bits_lt32 (n - kk) ltac:(lia))) as dR_2; dand6 dR_2 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b054 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b294 D_2b294.                        (* [comment removed for export] *)
          renm. stepn F_2b298 D_2b298.                        (* [comment removed for export] *)
          renm. stepb_tk F_2b29c D_2b29c ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_11; dand5 dR_11 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        (first [ pose proof ((t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia))) as dR_3; dex1 dR_3 as r2; destruct dR_3 as [RUN P] | pose proof ((t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia))) as dR_3; dand3 dR_3 as r2 RUN P | destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b2a0 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b294 D_2b294.
          renm. stepn F_2b298 D_2b298.
          renm. stepb_ft F_2b29c D_2b29c ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_12; dand5 dR_12 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b32c : word) (MK (kk + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * (first [ pose proof ((b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_4; dex1 dR_4 as r2; destruct dR_4 as [RUN P] | pose proof ((b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_4; dand3 dR_4 as r2 RUN P | destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2; (first [ intro dR_13; dand5 dR_13 as S1 S11 S13 S12 K2 | intros (S1 & S11 & S13 & S12 & K2) ])).
          (first [ pose proof ((b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia))) as dR_5; dex1 dR_5 as r3; destruct dR_5 as [RUN P] | pose proof ((b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia))) as dR_5; dand3 dR_5 as r3 RUN P | destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P) ]).
          exists r3. stn_open. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  #[using="Hn0 HOK"] Lemma c1_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs' m,
      msteps RSEGS (mkst regs (0x2b068 : word) (MK k) rom)
                   (mkst regs' (0x2b3b4 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 1 <= n - (k + 3) < 16 * (Z.of_nat q + 1) + 17)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 3 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    (first [ pose proof ((bits_lt32 m ltac:(lia))) as dR_6; dand6 dR_6 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
    (first [ pose proof ((c1_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk)) as dR_7; dex1 dR_7 as r1; dand8 dR_7 as RUN1 P1 P11 P13 P12 P14 P15 K1 | pose proof ((c1_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk)) as dR_7; dand9 dR_7 as r1 RUN1 P1 P11 P13 P12 P14 P15 K1 | destruct (c1_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1) ]).
    (first [ pose proof ((c1_loop q r1 ret (k + 3)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)) as dR_8; dex1 dR_8 as r2; dand6 dR_8 as RUN2 Q1 Q11 Q13 Q12 K2 | pose proof ((c1_loop q r1 ret (k + 3)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)) as dR_8; dand7 dR_8 as r2 RUN2 Q1 Q11 Q13 Q12 K2 | destruct (c1_loop q r1 ret (k + 3)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2) ]).
    fold kk in RUN2, Q11, Q13, Q12.
    (first [ pose proof ((c1_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_9; dex1 dR_9 as r3; dand6 dR_9 as RUN3 S1 S11 S13 S12 K3 | pose proof ((c1_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_9; dand7 dR_9 as r3 RUN3 S1 S11 S13 S12 K3 | destruct (c1_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3) ]).
    fold m in RUN3, S11, S13, S12.
    exists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End DU_Mdnl.


Module DU_Mt5b.
(* [comment removed for export] *)
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
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk WalkTac MmapSim RefMocc DU_M0r3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_cij8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_M0r3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Mbtj.DU_Mbio OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Mbtj.DU_M9cn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_cij8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.DU_cg5g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
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
Local Ltac stn_open := repeat match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end.
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

Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc.solve_keeps ::=
  stn_wit; repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc.solve_keeps_cs ::=
  stn_wit;
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
(* [comment removed for export] *)
Section C2.
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

  Ltac post := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac m16 := eapply (merge_s16 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hn0 HOK"] Lemma c2_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b068 : word) (MK k) rom) (mkst regs' (0x2b098 : word) (MK (k + 2)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 2)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 2)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 17 /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. stn_eexists. split.
    - renm. mlw F_2b068 D_2b068 k.                            (* [comment removed for export] *)
      renm. stepn F_2b06c D_2b06c.                            (* [comment removed for export] *)
      renm. stepb_ft F_2b070 D_2b070 ltac:(cond).             (* [comment removed for export] *)
      renm. stepn F_2b074 D_2b074.                            (* [comment removed for export] *)
      renm. stepb_ft F_2b078 D_2b078 ltac:(cond).             (* [comment removed for export] *)
      renm. stepn F_2b07c D_2b07c.                            (* [comment removed for export] *)
      renm. stepn F_2b080 D_2b080.                            (* [comment removed for export] *)
      renm. msb F_2b084 D_2b084 k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).        (* [comment removed for export] *)
      renm. msb F_2b088 D_2b088 (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
      renm. stepn F_2b08c D_2b08c.                            (* [comment removed for export] *)
      renm. stepn F_2b090 D_2b090.                            (* [comment removed for export] *)
      renm. stepn F_2b094 D_2b094.                            (* [comment removed for export] *)
      stn_done. mk_eq. stn_done. apply mst_refl.
    - post. stn_open. unfold v_addi. unorm. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Hn0 HOK"] Lemma c2_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 17 ->
    (ja = kk + 14)%Z -> (jw = kk - 2)%Z -> (2 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 2 <= n - kk < 16 * (Z.of_nat q + 1) + 18)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b098 : word) (MK kk) rom)
                   (mkst regs' (0x2b0f8 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 14)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - stn_eexists. split.
      + renm. stepn F_2b098 D_2b098.                          (* [comment removed for export] *)
        renm. mlw F_2b09c D_2b09c (kk + 2)%Z.                 (* [comment removed for export] *)
        renm. mlw F_2b0a0 D_2b0a0 (kk + 6)%Z.                 (* [comment removed for export] *)
        renm. mlw F_2b0a4 D_2b0a4 (kk + 10)%Z.                (* [comment removed for export] *)
        renm. mlw F_2b0a8 D_2b0a8 (kk + 14)%Z.                (* [comment removed for export] *)
        renm. stepn F_2b0ac D_2b0ac. renm. stepn F_2b0b0 D_2b0b0. renm. stepn F_2b0b4 D_2b0b4.   (* [comment removed for export] *)
        renm. stepn F_2b0b8 D_2b0b8. renm. stepn F_2b0bc D_2b0bc. renm. stepn F_2b0c0 D_2b0c0.   (* [comment removed for export] *)
        renm. stepn F_2b0c4 D_2b0c4. renm. stepn F_2b0c8 D_2b0c8. renm. stepn F_2b0cc D_2b0cc.   (* [comment removed for export] *)
        renm. stepn F_2b0d0 D_2b0d0. renm. stepn F_2b0d4 D_2b0d4.                          (* [comment removed for export] *)
        renm. stepn F_2b0d8 D_2b0d8.                          (* [comment removed for export] *)
        renm. msw F_2b0dc D_2b0dc kk ltac:(m16).              (* [comment removed for export] *)
        renm. msw F_2b0e0 D_2b0e0 (kk + 4)%Z ltac:(m16).      (* [comment removed for export] *)
        renm. msw F_2b0e4 D_2b0e4 (kk + 8)%Z ltac:(m16).      (* [comment removed for export] *)
        renm. msw F_2b0e8 D_2b0e8 (kk + 12)%Z ltac:(m16).     (* [comment removed for export] *)
        renm. stepn F_2b0ec D_2b0ec.                          (* [comment removed for export] *)
        renm. stepn F_2b0f0 D_2b0f0.                          (* [comment removed for export] *)
        renm. stepb_ft F_2b0f4 D_2b0f4 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + post. stn_open. unfold v_addi. unorm. f_equal. lia.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b098 : word) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 14) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 14) 4)
                         /\ getr r 15 = Z_to_bv 64 17 /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b098 D_2b098.
          renm. mlw F_2b09c D_2b09c (kk + 2)%Z.
          renm. mlw F_2b0a0 D_2b0a0 (kk + 6)%Z.
          renm. mlw F_2b0a4 D_2b0a4 (kk + 10)%Z.
          renm. mlw F_2b0a8 D_2b0a8 (kk + 14)%Z.
          renm. stepn F_2b0ac D_2b0ac. renm. stepn F_2b0b0 D_2b0b0. renm. stepn F_2b0b4 D_2b0b4.
          renm. stepn F_2b0b8 D_2b0b8. renm. stepn F_2b0bc D_2b0bc. renm. stepn F_2b0c0 D_2b0c0.
          renm. stepn F_2b0c4 D_2b0c4. renm. stepn F_2b0c8 D_2b0c8. renm. stepn F_2b0cc D_2b0cc.
          renm. stepn F_2b0d0 D_2b0d0. renm. stepn F_2b0d4 D_2b0d4.
          renm. stepn F_2b0d8 D_2b0d8.
          renm. msw F_2b0dc D_2b0dc kk ltac:(m16).
          renm. msw F_2b0e0 D_2b0e0 (kk + 4)%Z ltac:(m16).
          renm. msw F_2b0e4 D_2b0e4 (kk + 8)%Z ltac:(m16).
          renm. msw F_2b0e8 D_2b0e8 (kk + 12)%Z ltac:(m16).
          renm. stepn F_2b0ec D_2b0ec.
          renm. stepn F_2b0f0 D_2b0f0.
          renm. stepb_tk F_2b0f4 D_2b0f4 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          stn_done. mk_eq. stn_done. apply mst_refl.
        * cbv beta. post. stn_open. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. (intros r1; (first [ intro dR_10; dand7 dR_10 as R1 R11 R13 R12 R14 R15 K1 | intros (R1 & R11 & R13 & R12 & R14 & R15 & K1) ])).
        (first [ pose proof ((IH r1 ret (kk + 16)%Z (kk + 16 + 14)%Z (kk + 14)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_1; dex1 dR_1 as r2; destruct dR_1 as [RUN P] | pose proof ((IH r1 ret (kk + 16)%Z (kk + 16 + 14)%Z (kk + 14)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_1; dand3 dR_1 as r2 RUN P | destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 14)%Z (kk + 14)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK"] Lemma c2_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 14) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps RSEGS (mkst regs (0x2b0f8 : word) (MK kk) rom)
                   (mkst regs' (0x2b3b4 : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
    (first [ pose proof ((bits_lt32 (n - kk) ltac:(lia))) as dR_2; dand6 dR_2 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b054 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b0f8 D_2b0f8.                        (* [comment removed for export] *)
          renm. stepn F_2b0fc D_2b0fc.                        (* [comment removed for export] *)
          renm. stepb_tk F_2b100 D_2b100 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_11; dand5 dR_11 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        (first [ pose proof ((t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia))) as dR_3; dex1 dR_3 as r2; destruct dR_3 as [RUN P] | pose proof ((t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia))) as dR_3; dand3 dR_3 as r2 RUN P | destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b2a0 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b0f8 D_2b0f8.
          renm. stepn F_2b0fc D_2b0fc.
          renm. stepb_ft F_2b100 D_2b100 ltac:(cond).         (* [comment removed for export] *)
          renm. stepn F_2b104 D_2b104.                        (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_12; dand5 dR_12 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b32c : word) (MK (kk + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * (first [ pose proof ((b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_4; dex1 dR_4 as r2; destruct dR_4 as [RUN P] | pose proof ((b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_4; dand3 dR_4 as r2 RUN P | destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2; (first [ intro dR_13; dand5 dR_13 as S1 S11 S13 S12 K2 | intros (S1 & S11 & S13 & S12 & K2) ])).
          (first [ pose proof ((b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia))) as dR_5; dex1 dR_5 as r3; destruct dR_5 as [RUN P] | pose proof ((b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia))) as dR_5; dand3 dR_5 as r3 RUN P | destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P) ]).
          exists r3. stn_open. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  #[using="Hn0 HOK"] Lemma c2_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs' m,
      msteps RSEGS (mkst regs (0x2b068 : word) (MK k) rom)
                   (mkst regs' (0x2b3b4 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 2 <= n - (k + 2) < 16 * (Z.of_nat q + 1) + 18)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 2 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    (first [ pose proof ((bits_lt32 m ltac:(lia))) as dR_6; dand6 dR_6 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
    (first [ pose proof ((c2_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk)) as dR_7; dex1 dR_7 as r1; dand8 dR_7 as RUN1 P1 P11 P13 P12 P14 P15 K1 | pose proof ((c2_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk)) as dR_7; dand9 dR_7 as r1 RUN1 P1 P11 P13 P12 P14 P15 K1 | destruct (c2_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1) ]).
    (first [ pose proof ((c2_loop q r1 ret (k + 2)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)) as dR_8; dex1 dR_8 as r2; dand6 dR_8 as RUN2 Q1 Q11 Q13 Q12 K2 | pose proof ((c2_loop q r1 ret (k + 2)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)) as dR_8; dand7 dR_8 as r2 RUN2 Q1 Q11 Q13 Q12 K2 | destruct (c2_loop q r1 ret (k + 2)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2) ]).
    fold kk in RUN2, Q11, Q13, Q12.
    (first [ pose proof ((c2_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_9; dex1 dR_9 as r3; dand6 dR_9 as RUN3 S1 S11 S13 S12 K3 | pose proof ((c2_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_9; dand7 dR_9 as r3 RUN3 S1 S11 S13 S12 K3 | destruct (c2_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3) ]).
    fold m in RUN3, S11, S13, S12.
    exists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End DU_Mt5b.


Module DU_Mojz.
(* [comment removed for export] *)
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
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk WalkTac MmapSim RefMocc DU_M0r3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_cij8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_M0r3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Mbtj.DU_Mbio OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Mbtj.DU_M9cn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_cij8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.DU_cg5g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
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
Local Ltac stn_open := repeat match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end.
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

Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc.solve_keeps ::=
  stn_wit; repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc.solve_keeps_cs ::=
  stn_wit;
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
(* [comment removed for export] *)
Section C3.
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

  Ltac post := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac m8 := eapply (merge_s8 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  (* [comment removed for export] *)
  #[using="Hn0 HOK"] Lemma c3_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b068 : word) (MK k) rom) (mkst regs' (0x2b1a0 : word) (MK (k + 1)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 1)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 1)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 18 /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. stn_eexists. split.
    - renm. mlw F_2b068 D_2b068 k.                            (* [comment removed for export] *)
      renm. stepn F_2b06c D_2b06c.                            (* [comment removed for export] *)
      renm. stepb_tk F_2b070 D_2b070 ltac:(cond).             (* [comment removed for export] *)
      renm. msb F_2b18c D_2b18c k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).        (* [comment removed for export] *)
      renm. stepn F_2b190 D_2b190.                            (* [comment removed for export] *)
      renm. stepn F_2b194 D_2b194.                            (* [comment removed for export] *)
      renm. stepn F_2b198 D_2b198.                            (* [comment removed for export] *)
      renm. stepn F_2b19c D_2b19c.                            (* [comment removed for export] *)
      stn_done. mk_eq. stn_done. apply mst_refl.
    - post. stn_open. unfold v_addi. unorm. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Hn0 HOK"] Lemma c3_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 18 ->
    (ja = kk + 15)%Z -> (jw = kk - 1)%Z -> (1 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 3 <= n - kk < 16 * (Z.of_nat q + 1) + 19)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b1a0 : word) (MK kk) rom)
                   (mkst regs' (0x2b200 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 15)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - stn_eexists. split.
      + renm. stepn F_2b1a0 D_2b1a0.                          (* [comment removed for export] *)
        renm. mlw F_2b1a4 D_2b1a4 (kk + 3)%Z.                 (* [comment removed for export] *)
        renm. mlw F_2b1a8 D_2b1a8 (kk + 7)%Z.                 (* [comment removed for export] *)
        renm. mlw F_2b1ac D_2b1ac (kk + 11)%Z.                (* [comment removed for export] *)
        renm. mlw F_2b1b0 D_2b1b0 (kk + 15)%Z.                (* [comment removed for export] *)
        renm. stepn F_2b1b4 D_2b1b4. renm. stepn F_2b1b8 D_2b1b8. renm. stepn F_2b1bc D_2b1bc.
        renm. stepn F_2b1c0 D_2b1c0. renm. stepn F_2b1c4 D_2b1c4. renm. stepn F_2b1c8 D_2b1c8.
        renm. stepn F_2b1cc D_2b1cc. renm. stepn F_2b1d0 D_2b1d0. renm. stepn F_2b1d4 D_2b1d4.
        renm. stepn F_2b1d8 D_2b1d8. renm. stepn F_2b1dc D_2b1dc.
        renm. stepn F_2b1e0 D_2b1e0.                          (* [comment removed for export] *)
        renm. msw F_2b1e4 D_2b1e4 kk ltac:(m8).
        renm. msw F_2b1e8 D_2b1e8 (kk + 4)%Z ltac:(m8).
        renm. msw F_2b1ec D_2b1ec (kk + 8)%Z ltac:(m8).
        renm. msw F_2b1f0 D_2b1f0 (kk + 12)%Z ltac:(m8).
        renm. stepn F_2b1f4 D_2b1f4.                          (* [comment removed for export] *)
        renm. stepn F_2b1f8 D_2b1f8.                          (* [comment removed for export] *)
        renm. stepb_ft F_2b1fc D_2b1fc ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + post. stn_open. unfold v_addi. unorm. f_equal. lia.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b1a0 : word) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 15) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 15) 4)
                         /\ getr r 15 = Z_to_bv 64 18 /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b1a0 D_2b1a0.
          renm. mlw F_2b1a4 D_2b1a4 (kk + 3)%Z.
          renm. mlw F_2b1a8 D_2b1a8 (kk + 7)%Z.
          renm. mlw F_2b1ac D_2b1ac (kk + 11)%Z.
          renm. mlw F_2b1b0 D_2b1b0 (kk + 15)%Z.
          renm. stepn F_2b1b4 D_2b1b4. renm. stepn F_2b1b8 D_2b1b8. renm. stepn F_2b1bc D_2b1bc.
          renm. stepn F_2b1c0 D_2b1c0. renm. stepn F_2b1c4 D_2b1c4. renm. stepn F_2b1c8 D_2b1c8.
          renm. stepn F_2b1cc D_2b1cc. renm. stepn F_2b1d0 D_2b1d0. renm. stepn F_2b1d4 D_2b1d4.
          renm. stepn F_2b1d8 D_2b1d8. renm. stepn F_2b1dc D_2b1dc.
          renm. stepn F_2b1e0 D_2b1e0.
          renm. msw F_2b1e4 D_2b1e4 kk ltac:(m8).
          renm. msw F_2b1e8 D_2b1e8 (kk + 4)%Z ltac:(m8).
          renm. msw F_2b1ec D_2b1ec (kk + 8)%Z ltac:(m8).
          renm. msw F_2b1f0 D_2b1f0 (kk + 12)%Z ltac:(m8).
          renm. stepn F_2b1f4 D_2b1f4.
          renm. stepn F_2b1f8 D_2b1f8.
          renm. stepb_tk F_2b1fc D_2b1fc ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          stn_done. mk_eq. stn_done. apply mst_refl.
        * cbv beta. post. stn_open. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. (intros r1; (first [ intro dR_10; dand7 dR_10 as R1 R11 R13 R12 R14 R15 K1 | intros (R1 & R11 & R13 & R12 & R14 & R15 & K1) ])).
        (first [ pose proof ((IH r1 ret (kk + 16)%Z (kk + 16 + 15)%Z (kk + 15)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_1; dex1 dR_1 as r2; destruct dR_1 as [RUN P] | pose proof ((IH r1 ret (kk + 16)%Z (kk + 16 + 15)%Z (kk + 15)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_1; dand3 dR_1 as r2 RUN P | destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 15)%Z (kk + 15)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK"] Lemma c3_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 15) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps RSEGS (mkst regs (0x2b200 : word) (MK kk) rom)
                   (mkst regs' (0x2b3b4 : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
    (first [ pose proof ((bits_lt32 (n - kk) ltac:(lia))) as dR_2; dand6 dR_2 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b054 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b200 D_2b200.                        (* [comment removed for export] *)
          renm. stepn F_2b204 D_2b204.                        (* [comment removed for export] *)
          renm. stepb_tk F_2b208 D_2b208 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_11; dand5 dR_11 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        (first [ pose proof ((t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia))) as dR_3; dex1 dR_3 as r2; destruct dR_3 as [RUN P] | pose proof ((t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia))) as dR_3; dand3 dR_3 as r2 RUN P | destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b2a0 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b200 D_2b200.
          renm. stepn F_2b204 D_2b204.
          renm. stepb_ft F_2b208 D_2b208 ltac:(cond).
          renm. stepn F_2b20c D_2b20c.                        (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_12; dand5 dR_12 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b32c : word) (MK (kk + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * (first [ pose proof ((b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_4; dex1 dR_4 as r2; destruct dR_4 as [RUN P] | pose proof ((b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_4; dand3 dR_4 as r2 RUN P | destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2; (first [ intro dR_13; dand5 dR_13 as S1 S11 S13 S12 K2 | intros (S1 & S11 & S13 & S12 & K2) ])).
          (first [ pose proof ((b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia))) as dR_5; dex1 dR_5 as r3; destruct dR_5 as [RUN P] | pose proof ((b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia))) as dR_5; dand3 dR_5 as r3 RUN P | destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P) ]).
          exists r3. stn_open. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  #[using="Hn0 HOK"] Lemma c3_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs' m,
      msteps RSEGS (mkst regs (0x2b068 : word) (MK k) rom)
                   (mkst regs' (0x2b3b4 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 3 <= n - (k + 1) < 16 * (Z.of_nat q + 1) + 19)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 1 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    (first [ pose proof ((bits_lt32 m ltac:(lia))) as dR_6; dand6 dR_6 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
    (first [ pose proof ((c3_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk)) as dR_7; dex1 dR_7 as r1; dand8 dR_7 as RUN1 P1 P11 P13 P12 P14 P15 K1 | pose proof ((c3_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk)) as dR_7; dand9 dR_7 as r1 RUN1 P1 P11 P13 P12 P14 P15 K1 | destruct (c3_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1) ]).
    (first [ pose proof ((c3_loop q r1 ret (k + 1)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)) as dR_8; dex1 dR_8 as r2; dand6 dR_8 as RUN2 Q1 Q11 Q13 Q12 K2 | pose proof ((c3_loop q r1 ret (k + 1)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)) as dR_8; dand7 dR_8 as r2 RUN2 Q1 Q11 Q13 Q12 K2 | destruct (c3_loop q r1 ret (k + 1)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2) ]).
    fold kk in RUN2, Q11, Q13, Q12.
    (first [ pose proof ((c3_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_9; dex1 dR_9 as r3; dand6 dR_9 as RUN3 S1 S11 S13 S12 K3 | pose proof ((c3_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_9; dand7 dR_9 as r3 RUN3 S1 S11 S13 S12 K3 | destruct (c3_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3) ]).
    fold m in RUN3, S11, S13, S12.
    exists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End DU_Mojz.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_cij8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_M0r3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Mbtj.DU_Mbio OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Mbtj.DU_M9cn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Mbtj.DU_Mdnl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Mbtj.DU_Mt5b OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Mbtj.DU_Mojz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_cij8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.DU_cg5g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
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
Local Ltac stn_open := repeat match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end.
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

Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc.solve_keeps ::=
  stn_wit; repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc.solve_keeps_cs ::=
  stn_wit;
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
(* [comment removed for export] *)
Section ALL.
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

  Ltac post := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  (* [comment removed for export] *)
  Ltac conda := rwH; unfold at_; cond.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hn0 HOK"] Lemma al_finish : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b114 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k Hret H1 H11 H13 H12 Hk.
    set (m := ((n - k) mod 16)%Z).
    pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)) as Hm16.
    (first [ pose proof ((bits_lt32 m ltac:(lia))) as dR_1; dand6 dR_1 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
    assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
    assert (Hl16 : Z.land m 16 = 0%Z) by (destruct B16 as [E|E]; [exact E|exfalso; lia]).
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b150 : word) (MK (n - m)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m) /\ getr r 13 = at_ dst (n - m) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { (first [ pose proof ((al16_run _ _ _ _ _ rom HOK regs ret k H1 H11 H13 H12 Hk)) as dR_2; dex1 dR_2 as r; destruct dR_2 as [R P] | pose proof ((al16_run _ _ _ _ _ rom HOK regs ret k H1 H11 H13 H12 Hk)) as dR_2; dand3 dR_2 as r R P | destruct (al16_run _ _ _ _ _ rom HOK regs ret k H1 H11 H13 H12 Hk) as (r & R & P) ]). exists r.
      subst m. split; [exact R|]. decompose [and] P. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption. }
    cbv beta. (intros r2; (first [ intro dR_21; dand5 dR_21 as S1 S11 S13 S12 K2 | intros (S1 & S11 & S13 & S12 & K2) ])).
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b170 : word) (MK (n - m + Z.land m 8)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8) /\ getr r 13 = at_ dst (n - m + Z.land m 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { (first [ pose proof ((al8_run _ _ _ _ _ rom HOK r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_3; dex1 dR_3 as r; destruct dR_3 as [R P] | pose proof ((al8_run _ _ _ _ _ rom HOK r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_3; dand3 dR_3 as r R P | destruct (al8_run _ _ _ _ _ rom HOK r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P) ]).
      exists r. split; [exact R|]. decompose [and] P. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. (intros r3; (first [ intro dR_22; dand5 dR_22 as T1 T11 T13 T12 K3 | intros (T1 & T11 & T13 & T12 & K3) ])).
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b3b4 : word) (MK (n - m + Z.land m 8 + Z.land m 4)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8 + Z.land m 4) /\ getr r 13 = at_ dst (n - m + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { (first [ pose proof ((al4_run _ _ _ _ _ rom HOK r3 ret (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_4; dex1 dR_4 as r; destruct dR_4 as [R P] | pose proof ((al4_run _ _ _ _ _ rom HOK r3 ret (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_4; dand3 dR_4 as r R P | destruct (al4_run _ _ _ _ _ rom HOK r3 ret (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P) ]).
      exists r. split; [exact R|]. decompose [and] P. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. (intros r4; (first [ intro dR_23; dand5 dR_23 as U1 U11 U13 U12 K4 | intros (U1 & U11 & U13 & U12 & K4) ])).
    (first [ pose proof ((t2_run _ _ _ _ _ rom HOK r4 ret (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1 ltac:(lia) ltac:(lia))) as dR_5; dex1 dR_5 as r; destruct dR_5 as [R P] | pose proof ((t2_run _ _ _ _ _ rom HOK r4 ret (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1 ltac:(lia) ltac:(lia))) as dR_5; dand3 dR_5 as r R P | destruct (t2_run _ _ _ _ _ rom HOK r4 ret (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r & R & P) ]).
    exists r. split; [exact R | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hn0 HOK"] Lemma mis_run : forall regs (ret : word) k q,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 15 = Z_to_bv 64 q -> (q = 1 \/ q = 2 \/ q = 3)%Z ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b044 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k q Hret H1 H11 H13 H12 H15 Hq Hk.
    destruct (Z.lt_ge_cases (n - k) 32) as [Hsmall|Hbig].
    - (* [comment removed for export] *)
      (first [ pose proof ((bits_lt32 (n - k) ltac:(lia))) as dR_6; dand6 dR_6 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 (n - k) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
      assert (0 <= Z.land (n - k) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 4)%Z by (apply Z.land_nonneg; lia).
      assert (0 <= Z.land (n - k) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 1)%Z by (apply Z.land_nonneg; lia).
      assert (0 <= Z.land (n - k) 16)%Z by (apply Z.land_nonneg; lia).
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b04c : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b044 D_2b044.                        (* [comment removed for export] *)
          renm. stepb_ft F_2b048 D_2b048 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_24; dand5 dR_24 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        set (m := (n - k)%Z) in *.
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b3b4 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
                           /\ getr r 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * (first [ pose proof ((t16_run _ _ _ _ _ rom HOK r1 ret k m R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_7; dex1 dR_7 as r2; destruct dR_7 as [RUN P] | pose proof ((t16_run _ _ _ _ _ rom HOK r1 ret k m R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_7; dand3 dR_7 as r2 RUN P | destruct (t16_run _ _ _ _ _ rom HOK r1 ret k m R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2; (first [ intro dR_25; dand5 dR_25 as S1 S11 S13 S12 K2 | intros (S1 & S11 & S13 & S12 & K2) ])).
          (first [ pose proof ((t2_run _ _ _ _ _ rom HOK r2 ret (k + Z.land m 16 + Z.land m 8 + Z.land m 4)%Z m Hret S1 S11 S13 S12
                      ltac:(lia) B2 B1 ltac:(lia) ltac:(lia))) as dR_8; dex1 dR_8 as r3; destruct dR_8 as [RUN K3] | pose proof ((t2_run _ _ _ _ _ rom HOK r2 ret (k + Z.land m 16 + Z.land m 8 + Z.land m 4)%Z m Hret S1 S11 S13 S12
                      ltac:(lia) B2 B1 ltac:(lia) ltac:(lia))) as dR_8; dand3 dR_8 as r3 RUN K3 | destruct (t2_run _ _ _ _ _ rom HOK r2 ret (k + Z.land m 16 + Z.land m 8 + Z.land m 4)%Z m Hret S1 S11 S13 S12
                      ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN & K3) ]).
          exists r3. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b068 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
                         /\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b044 D_2b044.                        (* [comment removed for export] *)
          renm. stepb_tk F_2b048 D_2b048 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_26; dand6 dR_26 as R1 R11 R13 R12 R15 K1 | intros (R1 & R11 & R13 & R12 & R15 & K1) ])).
        assert (CASE : exists regs' m,
          msteps RSEGS (mkst r1 (0x2b068 : word) (MK k) rom)
                       (mkst regs' (0x2b3b4 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
          /\ (0 <= m < 32)%Z
          /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
          /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
          /\ getr regs' 12 = Z_to_bv 64 m /\ keeps r1 regs').
        { destruct Hq as [-> | [-> | ->]].
          - apply (c1_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
          - apply (c2_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
          - apply (c3_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia. }
        (first [ dex2 CASE as r2 m; dand7 CASE as RUN Hm S1 S11 S13 S12 K2 | dand9 CASE as r2 m RUN Hm S1 S11 S13 S12 K2 | destruct CASE as (r2 & m & RUN & Hm & S1 & S11 & S13 & S12 & K2) ]).
        (first [ pose proof ((bits_lt32 m Hm)) as dR_10; dand6 dR_10 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
        assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
        (first [ pose proof ((t2_run _ _ _ _ _ rom HOK r2 ret (n - (Z.land m 2 + Z.land m 1))%Z m Hret S1 S11 S13 S12
                    ltac:(lia) B2 B1 ltac:(lia) ltac:(lia))) as dR_11; dex1 dR_11 as r3; destruct dR_11 as [RUN3 K3] | pose proof ((t2_run _ _ _ _ _ rom HOK r2 ret (n - (Z.land m 2 + Z.land m 1))%Z m Hret S1 S11 S13 S12
                    ltac:(lia) B2 B1 ltac:(lia) ltac:(lia))) as dR_11; dand3 dR_11 as r3 RUN3 K3 | destruct (t2_run _ _ _ _ _ rom HOK r2 ret (n - (Z.land m 2 + Z.land m 1))%Z m Hret S1 S11 S13 S12
                    ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN3 & K3) ]).
        exists r3. split; [eapply msteps_trans; [exact RUN | exact RUN3] |].
        eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hnwd Hn0 HOK"] Lemma j_run : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b03c : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k Hret H1 H11 H13 H12 Hk.
    pose proof (u64_range dst).
    set (q := ((bv_unsigned dst + k) mod 4)%Z).
    pose proof (Z.mod_pos_bound (bv_unsigned dst + k) 4 ltac:(lia)) as Hq4.
    destruct (Z.eq_dec q 0) as [Hq0|Hq0].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b114 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b03c D_2b03c.                        (* [comment removed for export] *)
          renm. stepb_tk F_2b040 D_2b040 ltac:(conda).        (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_27; dand5 dR_27 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        (first [ pose proof ((al_finish r1 ret k Hret R1 R11 R13 R12 Hk)) as dR_12; dex1 dR_12 as r2; destruct dR_12 as [RUN K2] | pose proof ((al_finish r1 ret k Hret R1 R11 R13 R12 Hk)) as dR_12; dand3 dR_12 as r2 RUN K2 | destruct (al_finish r1 ret k Hret R1 R11 R13 R12 Hk) as (r2 & RUN & K2) ]).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b044 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
                         /\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_2b03c D_2b03c.
          renm. stepb_ft F_2b040 D_2b040 ltac:(conda).        (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post. stn_open. unfold v_andi, at_. subst q. stn_open. rewrite <- land_3 by lia. unorm.
          stn_open. change (bv_wrap 64 3) with 3%Z. reflexivity.
      + cbv beta. (intros r1; (first [ intro dR_28; dand6 dR_28 as R1 R11 R13 R12 R15 K1 | intros (R1 & R11 & R13 & R12 & R15 & K1) ])).
        (first [ pose proof ((mis_run r1 ret k q Hret R1 R11 R13 R12 R15 ltac:(lia) Hk)) as dR_13; dex1 dR_13 as r2; destruct dR_13 as [RUN K2] | pose proof ((mis_run r1 ret k q Hret R1 R11 R13 R12 R15 ltac:(lia) Hk)) as dR_13; dand3 dR_13 as r2 RUN K2 | destruct (mis_run r1 ret k q Hret R1 R11 R13 R12 R15 ltac:(lia) Hk) as (r2 & RUN & K2) ]).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hnwd Hnws Hn0 HOK"] Lemma hl_loop : forall (i : nat) regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 14 = at_ src (k + 1) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (k < n)%Z -> ((bv_unsigned src + k) mod 4 <> 0)%Z ->
    (Z.of_nat i + 1 = Z.min (n - k) (4 - (bv_unsigned src + k) mod 4))%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2b00c : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 H14 H15 Hk Hkn Hal Hi.
    - (* [comment removed for export] *)
      pose proof (u64_range src).
      destruct (Z.eq_dec ((bv_unsigned src + (k + 1)) mod 4) 0) as [Hz|Hz].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b03c : word) (MK (k + 1)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
        * stn_eexists. split.
          -- mlbu F_2b00c D_2b00c k.                    (* [comment removed for export] *)
             renm. stepn F_2b010 D_2b010.                    (* [comment removed for export] *)
             renm. stepn F_2b014 D_2b014.                    (* [comment removed for export] *)
             renm. stepn F_2b018 D_2b018.                    (* [comment removed for export] *)
             renm. msb F_2b01c D_2b01c k ltac:(apply sb_val_plain).   (* [comment removed for export] *)
             renm. stepn F_2b020 D_2b020.                    (* [comment removed for export] *)
             renm. stepn F_2b024 D_2b024.                    (* [comment removed for export] *)
             renm. stepb_tk F_2b028 D_2b028 ltac:(conda).    (* [comment removed for export] *)
             stn_done. apply mst_refl.
          -- cbv beta. post. stn_open. unfold v_addi. unorm. f_equal. lia.
        * cbv beta. (intros r1; (first [ intro dR_29; dand5 dR_29 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
          (first [ pose proof ((j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia))) as dR_14; dex1 dR_14 as r2; destruct dR_14 as [RUN K2] | pose proof ((j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia))) as dR_14; dand3 dR_14 as r2 RUN K2 | destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2) ]).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b03c : word) (MK (k + 1)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
        * stn_eexists. split.
          -- mlbu F_2b00c D_2b00c k.
             renm. stepn F_2b010 D_2b010.
             renm. stepn F_2b014 D_2b014.
             renm. stepn F_2b018 D_2b018.
             renm. msb F_2b01c D_2b01c k ltac:(apply sb_val_plain).
             renm. stepn F_2b020 D_2b020.
             renm. stepn F_2b024 D_2b024.
             renm. stepb_ft F_2b028 D_2b028 ltac:(conda).    (* [comment removed for export] *)
             renm. stepn F_2b02c D_2b02c.                    (* [comment removed for export] *)
             renm. stepb_ft F_2b030 D_2b030 ltac:(cond).     (* [comment removed for export] *)
             renm. stepn F_2b034 D_2b034.                    (* [comment removed for export] *)
             stn_done. apply mst_refl.
          -- cbv beta. post. stn_open. unfold v_addi. unorm. f_equal. lia.
        * cbv beta. (intros r1; (first [ intro dR_30; dand5 dR_30 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
          (first [ pose proof ((j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia))) as dR_15; dex1 dR_15 as r2; destruct dR_15 as [RUN K2] | pose proof ((j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia))) as dR_15; dand3 dR_15 as r2 RUN K2 | destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2) ]).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      pose proof (u64_range src).
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b00c : word) (MK (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1))
                         /\ getr r 14 = at_ src (k + 1 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
      + stn_eexists. split.
        * mlbu F_2b00c D_2b00c k.
          renm. stepn F_2b010 D_2b010.
          renm. stepn F_2b014 D_2b014.
          renm. stepn F_2b018 D_2b018.
          renm. msb F_2b01c D_2b01c k ltac:(apply sb_val_plain).
          renm. stepn F_2b020 D_2b020.
          renm. stepn F_2b024 D_2b024.
          renm. stepb_ft F_2b028 D_2b028 ltac:(conda).       (* [comment removed for export] *)
          renm. stepn F_2b02c D_2b02c.                       (* [comment removed for export] *)
          renm. stepb_tk F_2b030 D_2b030 ltac:(cond).        (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post. stn_open. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. (intros r1; (first [ intro dR_31; dand7 dR_31 as R1 R11 R13 R12 R14 R15 K1 | intros (R1 & R11 & R13 & R12 & R14 & R15 & K1) ])).
        (first [ pose proof ((IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_16; dex1 dR_16 as r2; destruct dR_16 as [RUN K2] | pose proof ((IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_16; dand3 dR_16 as r2 RUN K2 | destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & K2) ]).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hnwd Hnws Hn0 HOK"] Theorem ref_memcpy : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0x2aff4 : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret Hret H1 H10 H11 H12.
    pose proof (u64_range src). pose proof (u64_range dst).
    rewrite <- (memk_n _ _ _ _ _ HOK). change mem0 with (MK 0).
    assert (H11' : getr regs 11 = at_ src 0) by (rewrite at_0; exact H11).
    assert (H12' : getr regs 12 = Z_to_bv 64 (n - 0)) by (rewrite Z.sub_0_r; exact H12).
    destruct (Z.eq_dec (bv_unsigned src mod 4) 0) as [Hs4|Hs4].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec (bv_unsigned dst mod 4) 0) as [Hd4|Hd4].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b114 : word) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
        * stn_eexists. split.
          -- renm. stepn F_2aff4 D_2aff4.                     (* [comment removed for export] *)
             renm. stepb_tk F_2aff8 D_2aff8 ltac:(conda).     (* [comment removed for export] *)
             renm. stepn F_2b108 D_2b108.                     (* [comment removed for export] *)
             renm. stepn F_2b10c D_2b10c.                     (* [comment removed for export] *)
             renm. stepb_ft F_2b110 D_2b110 ltac:(cond).      (* [comment removed for export] *)
             stn_done. apply mst_refl.
          -- cbv beta. post. stn_open. rewrite at_0. reflexivity.
        * cbv beta. (intros r1; (first [ intro dR_32; dand5 dR_32 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
          (first [ pose proof ((al_finish r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia))) as dR_17; dex1 dR_17 as r2; destruct dR_17 as [RUN K2] | pose proof ((al_finish r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia))) as dR_17; dand3 dR_17 as r2 RUN K2 | destruct (al_finish r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2) ]).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b044 : word) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                           /\ getr r 15 = Z_to_bv 64 (bv_unsigned dst mod 4) /\ keeps regs r)).
        * stn_eexists. split.
          -- renm. stepn F_2aff4 D_2aff4.
             renm. stepb_tk F_2aff8 D_2aff8 ltac:(conda).
             renm. stepn F_2b108 D_2b108.
             renm. stepn F_2b10c D_2b10c.
             renm. stepb_tk F_2b110 D_2b110 ltac:(cond).      (* [comment removed for export] *)
             stn_done. apply mst_refl.
          -- cbv beta. post; try (rewrite at_0; reflexivity).
             stn_open. unfold v_andi. stn_open. rewrite <- land_3 by lia. stn_open. change (bv_wrap 64 3) with 3%Z. reflexivity.
        * cbv beta. (intros r1; (first [ intro dR_33; dand6 dR_33 as R1 R11 R13 R12 R15 K1 | intros (R1 & R11 & R13 & R12 & R15 & K1) ])).
          pose proof (Z.mod_pos_bound (bv_unsigned dst) 4 ltac:(lia)).
          (first [ pose proof ((mis_run r1 ret 0 (bv_unsigned dst mod 4) Hret R1 R11 R13 R12 R15 ltac:(lia) ltac:(lia))) as dR_18; dex1 dR_18 as r2; destruct dR_18 as [RUN K2] | pose proof ((mis_run r1 ret 0 (bv_unsigned dst mod 4) Hret R1 R11 R13 R12 R15 ltac:(lia) ltac:(lia))) as dR_18; dand3 dR_18 as r2 RUN K2 | destruct (mis_run r1 ret 0 (bv_unsigned dst mod 4) Hret R1 R11 R13 R12 R15 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2) ]).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hn0z|Hn0z].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b03c : word) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
        * stn_eexists. split.
          -- renm. stepn F_2aff4 D_2aff4.                     (* [comment removed for export] *)
             renm. stepb_ft F_2aff8 D_2aff8 ltac:(conda).     (* [comment removed for export] *)
             renm. stepb_tk F_2affc D_2affc ltac:(cond).      (* [comment removed for export] *)
             renm. stepn F_2b038 D_2b038.                     (* [comment removed for export] *)
             stn_done. apply mst_refl.
          -- cbv beta. post. stn_open. rewrite at_0. reflexivity.
        * cbv beta. (intros r1; (first [ intro dR_34; dand5 dR_34 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
          (first [ pose proof ((j_run r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia))) as dR_19; dex1 dR_19 as r2; destruct dR_19 as [RUN K2] | pose proof ((j_run r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia))) as dR_19; dand3 dR_19 as r2 RUN K2 | destruct (j_run r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2) ]).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
      + set (i := Z.to_nat (Z.min n (4 - bv_unsigned src mod 4) - 1)).
        pose proof (Z.mod_pos_bound (bv_unsigned src) 4 ltac:(lia)).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x2b00c : word) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                           /\ getr r 14 = at_ src (0 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
        * stn_eexists. split.
          -- renm. stepn F_2aff4 D_2aff4.                     (* [comment removed for export] *)
             renm. stepb_ft F_2aff8 D_2aff8 ltac:(conda).     (* [comment removed for export] *)
             renm. stepb_ft F_2affc D_2affc ltac:(cond).      (* [comment removed for export] *)
             renm. stepn F_2b000 D_2b000.                     (* [comment removed for export] *)
             renm. stepn F_2b004 D_2b004.                     (* [comment removed for export] *)
             renm. stepn F_2b008 D_2b008.                     (* [comment removed for export] *)
             stn_done. apply mst_refl.
          -- cbv beta. post. stn_open. rewrite at_0. reflexivity.
        * cbv beta. (intros r1; (first [ intro dR_35; dand7 dR_35 as R1 R11 R13 R12 R14 R15 K1 | intros (R1 & R11 & R13 & R12 & R14 & R15 & K1) ])).
          (first [ pose proof ((hl_loop i r1 ret 0 Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hs4))) as dR_20; dex1 dR_20 as r2; destruct dR_20 as [RUN K2] | pose proof ((hl_loop i r1 ret 0 Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hs4))) as dR_20; dand3 dR_20 as r2 RUN K2 | destruct (hl_loop i r1 ret 0 Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hs4)) as (r2 & RUN & K2) ]).
          { subst i. stn_open. rewrite Z.add_0_r, Z.sub_0_r. stn_open. rewrite Z2Nat.id; lia. }
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

End ALL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

