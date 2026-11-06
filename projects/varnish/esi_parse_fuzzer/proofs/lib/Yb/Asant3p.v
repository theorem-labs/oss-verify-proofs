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

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk WalkTac MmapSim RefMocc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import Memsalo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import Asan9qi.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
(* [comment removed for export] *)
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
(* [comment removed for export] *)
#[local] Ltac cond :=
  rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
(* [comment removed for export] *)
#[local] Ltac pclits :=
  repeat match goal with
         | |- context [Z_to_bv 64 (ms_base + ?o)%Z] => wlit_replace (Z_to_bv 64 (ms_base + o)%Z)
         end.
(* [comment removed for export] *)
#[local] Ltac stepat L F D vv tac :=
  chain_step; [reflexivity | eapply L with (v := vv); [exact F | reflexivity | exact D | reflexivity | tac] | step_simpl].

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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.WalkTac.gres ::= first [ stn_final_use | stn_gres_old; repeat (stn_demand1; stn_gres_old) ].
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk.store_ok_peel ::= stn_sok_old; try stn_sok_named.

Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc.solve_keeps ::=
  stn_wit; repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc.solve_keeps_cs ::=
  stn_wit;
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Memsalo.solve_ms_agree ::=
  stn_wit; repeat (apply ms_agree_upd; [| in_clob]); first [apply ms_agree_refl | assumption].
(* [comment removed for export] *)
Section Walk.
  Variable mem0 : word -> option byte.
  Variables d cv ret : word.
  Variable n : Z.
  Variable rom : word -> option byte.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hnw : (bv_unsigned d + n < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok MSEGS mem0 d (Z.to_nat n) = true.
  Hypothesis Hret : ret_ok ret.

  #[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).
  #[local] Abbreviation PC o := (Z_to_bv 64 (ms_base + o)).

  (* [comment removed for export] *)
  #[local] Ltac msb F D oo :=
    chain_step; [reflexivity
      | eapply (cf_sb MSEGS mem0 d n cv Hnw Hok) with (o := oo);
        [exact F | reflexivity | exact D
        | gres; rwH; rewrite ?at_addi; reflexivity
        | imm_norm; lia
        | gres; rwH; reflexivity
        | lia | lia]
      | step_simpl].
  #[local] Ltac msw F D oo :=
    chain_step; [reflexivity
      | eapply (cf_sw MSEGS mem0 d n cv Hnw Hok) with (o := oo);
        [exact F | reflexivity | exact D
        | gres; rwH; rewrite ?at_addi; reflexivity
        | imm_norm; lia
        | gres; rwH; reflexivity
        | apply wleb4_c32
        | lia | lia]
      | step_simpl].
  #[local] Ltac msd F D oo :=
    chain_step; [reflexivity
      | eapply (cf_sd MSEGS mem0 d n cv Hnw Hok) with (o := oo);
        [exact F | reflexivity | exact D
        | gres; rwH; rewrite ?at_addi; reflexivity
        | imm_norm; lia
        | gres; rwH; reflexivity
        | apply wleb8_c64
        | lia | lia]
      | step_simpl].
  (* [comment removed for export] *)
  #[local] Ltac mret := stepret Fo_0f4 Do_0f4 ret ltac:(rwH; reflexivity).
  (* [comment removed for export] *)
  #[local] Ltac post := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; try reflexivity; solve_ms_agree.

  (* [comment removed for export] *)
  Definition L2 : list (Z * Z) := [(n-1,1); (0,1)]%Z.
  Definition L6 : list (Z * Z) := [(n-2,1); (n-3,1); (2,1); (1,1); (n-1,1); (0,1)]%Z.
  Definition L8 : list (Z * Z) := [(n-4,1); (3,1); (n-2,1); (n-3,1); (2,1); (1,1); (n-1,1); (0,1)]%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma A_exit0 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (n = 0)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF []) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    stn_eexists. split.
    - renm. stepb_tk Fo_000 Do_000 ltac:(cond).          (* [comment removed for export] *)
      mret.
      stn_done. apply mst_refl.
    - post.
  Qed.

  Lemma A_exit2 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (1 <= n <= 2)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L2) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    stn_eexists. split.
    - renm. stepb_ft Fo_000 Do_000 ltac:(cond).          (* [comment removed for export] *)
      renm. msb Fo_004 Do_004 0%Z.                         (* [comment removed for export] *)
      renm. stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).  (* [comment removed for export] *)
      renm. stepn Fo_00c Do_00c.                           (* [comment removed for export] *)
      renm. msb Fo_010 Do_010 (n-1)%Z.                     (* [comment removed for export] *)
      renm. stepb_tk Fo_014 Do_014 ltac:(cond).          (* [comment removed for export] *)
      mret.
      stn_done. apply mst_refl.
    - post.
  Qed.

  Lemma A_exit6 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (3 <= n <= 6)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L6) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    stn_eexists. split.
    - renm. stepb_ft Fo_000 Do_000 ltac:(cond).
      renm. msb Fo_004 Do_004 0%Z.
      renm. stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
      renm. stepn Fo_00c Do_00c.
      renm. msb Fo_010 Do_010 (n-1)%Z.
      renm. stepb_ft Fo_014 Do_014 ltac:(cond).
      renm. msb Fo_018 Do_018 1%Z.                         (* [comment removed for export] *)
      renm. msb Fo_01c Do_01c 2%Z.                         (* [comment removed for export] *)
      renm. stepn Fo_020 Do_020.                           (* [comment removed for export] *)
      renm. msb Fo_024 Do_024 (n-3)%Z.                     (* [comment removed for export] *)
      renm. msb Fo_028 Do_028 (n-2)%Z.                     (* [comment removed for export] *)
      renm. stepb_tk Fo_02c Do_02c ltac:(cond).          (* [comment removed for export] *)
      mret.
      stn_done. apply mst_refl.
    - post.
  Qed.

  Lemma A_exit8 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (7 <= n <= 8)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L8) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    stn_eexists. split.
    - renm. stepb_ft Fo_000 Do_000 ltac:(cond).
      renm. msb Fo_004 Do_004 0%Z.
      renm. stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
      renm. stepn Fo_00c Do_00c.
      renm. msb Fo_010 Do_010 (n-1)%Z.
      renm. stepb_ft Fo_014 Do_014 ltac:(cond).
      renm. msb Fo_018 Do_018 1%Z.
      renm. msb Fo_01c Do_01c 2%Z.
      renm. stepn Fo_020 Do_020.
      renm. msb Fo_024 Do_024 (n-3)%Z.
      renm. msb Fo_028 Do_028 (n-2)%Z.
      renm. stepb_ft Fo_02c Do_02c ltac:(cond).
      renm. msb Fo_030 Do_030 3%Z.                         (* [comment removed for export] *)
      renm. stepn Fo_034 Do_034.                           (* [comment removed for export] *)
      renm. msb Fo_038 Do_038 (n-4)%Z.                     (* [comment removed for export] *)
      renm. stepb_tk Fo_03c Do_03c ltac:(cond).          (* [comment removed for export] *)
      mret.
      stn_done. apply mst_refl.
    - post.
  Qed.

  Lemma A_cont : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (9 <= n)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' (PC 0x40) (CF L8) rom)
      /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = cv /\ getr regs' 12 = Z_to_bv 64 n
      /\ getr regs' 13 = at_ d n /\ getr regs' 15 = Z_to_bv 64 9 /\ getr regs' 1 = ret
      /\ ms_agree regs regs'.
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    stn_eexists. split.
    - renm. stepb_ft Fo_000 Do_000 ltac:(cond).
      renm. msb Fo_004 Do_004 0%Z.
      renm. stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
      renm. stepn Fo_00c Do_00c.
      renm. msb Fo_010 Do_010 (n-1)%Z.
      renm. stepb_ft Fo_014 Do_014 ltac:(cond).
      renm. msb Fo_018 Do_018 1%Z.
      renm. msb Fo_01c Do_01c 2%Z.
      renm. stepn Fo_020 Do_020.
      renm. msb Fo_024 Do_024 (n-3)%Z.
      renm. msb Fo_028 Do_028 (n-2)%Z.
      renm. stepb_ft Fo_02c Do_02c ltac:(cond).
      renm. msb Fo_030 Do_030 3%Z.
      renm. stepn Fo_034 Do_034.
      renm. msb Fo_038 Do_038 (n-4)%Z.
      renm. stepb_ft Fo_03c Do_03c ltac:(cond).          (* [comment removed for export] *)
      stn_done. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Section Aligned.
    Variables k n1 : Z.
    Hypothesis Hk : (0 <= k <= 3)%Z.
    Hypothesis Hn1 : (n - k - 3 <= n1 <= n - k)%Z.
    Hypothesis Hkv : v_andi (v_subw (Z_to_bv 64 0) d) 3 = Z_to_bv 64 k.
    Hypothesis Hn1v : v_andi (Z_to_bv 64 (n - k)) (-4) = Z_to_bv 64 n1.

    Definition LB : list (Z * Z) := ((k+n1-4,4) :: (k,4) :: L8)%Z.
    Definition LC : list (Z * Z) := ((k+n1-8,4) :: (k+n1-12,4) :: (k+8,4) :: (k+4,4) :: LB)%Z.
    Definition LD (s4 : Z) : list (Z * Z) :=
      ((k+n1-16,4) :: (k+n1-20,4) :: (k+n1-24,4) :: (k+n1-28,4)
        :: (k+24,4) :: (k+20,4) :: (k+16,4) :: (k+12,4) :: LC)%Z.

    #[local] Ltac blockB :=
      stepn Fo_040 Do_040;                           (* [comment removed for export] *)
      stepn Fo_044 Do_044;                           (* [comment removed for export] *)
      stepn Fo_048 Do_048;                           (* [comment removed for export] *)
      stepiv Fo_04c Do_04c (Z_to_bv 64 k) ltac:(gres; rwH; imm_norm; rewrite at_0; exact Hkv);   (* [comment removed for export] *)
      stepn Fo_050 Do_050;                           (* [comment removed for export] *)
      stepiv Fo_054 Do_054 (Z_to_bv 64 (n - k)) ltac:(gres; rwH; apply ms_v_sub_ZZ; lia);          (* [comment removed for export] *)
      stepiv Fo_058 Do_058 (at_ d k) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia);  (* [comment removed for export] *)
      stepn Fo_05c Do_05c;                           (* [comment removed for export] *)
      stepiv Fo_060 Do_060 (Z_to_bv 64 n1) ltac:(gres; rwH; imm_norm; exact Hn1v);              (* [comment removed for export] *)
      stepat ms_step_mulhu_at Fo_064 Do_064 (c32 cv) ltac:(gres; rwH; apply mulhu_c32; unorm; reflexivity);  (* [comment removed for export] *)
      msw Fo_068 Do_068 k;                           (* [comment removed for export] *)
      stepiv Fo_06c Do_06c (at_ d (k + n1)) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; reflexivity);  (* [comment removed for export] *)
      msw Fo_070 Do_070 (k + n1 - 4)%Z.              (* [comment removed for export] *)

    Lemma B_exit : forall regs,
      getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n ->
      getr regs 13 = at_ d n -> getr regs 15 = Z_to_bv 64 9 -> getr regs 1 = ret ->
      (9 <= n)%Z -> (n1 < 9)%Z ->
      exists regs',
        msteps MSEGS (mkst regs (PC 0x40) (CF L8) rom) (mkst regs' ret (CF LB) rom)
        /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
    Proof.
      intros regs H10 H11 H12 H13 H15 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
      stn_eexists. split.
      - blockB.
        renm. stepb_tk Fo_074 Do_074 ltac:(cond).        (* [comment removed for export] *)
        mret.
        stn_done. apply mst_refl.
      - post.
    Qed.

    Lemma B_cont : forall regs,
      getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n ->
      getr regs 13 = at_ d n -> getr regs 15 = Z_to_bv 64 9 -> getr regs 1 = ret ->
      (9 <= n)%Z -> (9 <= n1)%Z ->
      exists regs',
        msteps MSEGS (mkst regs (PC 0x40) (CF L8) rom) (mkst regs' (PC 0x78) (CF LB) rom)
        /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d k /\ getr regs' 12 = c32 cv
        /\ getr regs' 13 = at_ d (k + n1) /\ getr regs' 14 = Z_to_bv 64 n1 /\ getr regs' 1 = ret
        /\ ms_agree regs regs'.
    Proof.
      intros regs H10 H11 H12 H13 H15 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
      stn_eexists. split.
      - blockB.
        renm. stepb_ft Fo_074 Do_074 ltac:(cond).        (* [comment removed for export] *)
        stn_done. apply mst_refl.
      - post.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    #[local] Ltac blockC :=
      msw Fo_078 Do_078 (k + 4)%Z;                   (* [comment removed for export] *)
      msw Fo_07c Do_07c (k + 8)%Z;                   (* [comment removed for export] *)
      stepn Fo_080 Do_080;                           (* [comment removed for export] *)
      msw Fo_084 Do_084 (k + n1 - 12)%Z;             (* [comment removed for export] *)
      msw Fo_088 Do_088 (k + n1 - 8)%Z.              (* [comment removed for export] *)

    Lemma C_exit : forall regs,
      getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
      getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
      (9 <= n)%Z -> (12 <= n1)%Z -> (n1 < 25)%Z ->
      exists regs',
        msteps MSEGS (mkst regs (PC 0x78) (CF LB) rom) (mkst regs' ret (CF LC) rom)
        /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
    Proof.
      intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
      stn_eexists. split.
      - blockC.
        renm. stepb_tk Fo_08c Do_08c ltac:(cond).        (* [comment removed for export] *)
        mret.
        stn_done. apply mst_refl.
      - post.
    Qed.

    Lemma C_cont : forall regs,
      getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
      getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
      (9 <= n)%Z -> (25 <= n1)%Z ->
      exists regs',
        msteps MSEGS (mkst regs (PC 0x78) (CF LB) rom) (mkst regs' (PC 0x90) (CF LC) rom)
        /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d k /\ getr regs' 12 = c32 cv
        /\ getr regs' 13 = at_ d (k + n1) /\ getr regs' 14 = Z_to_bv 64 n1 /\ getr regs' 1 = ret
        /\ ms_agree regs regs'.
    Proof.
      intros regs H10 H11 H12 H13 H14 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
      stn_eexists. split.
      - blockC.
        renm. stepb_ft Fo_08c Do_08c ltac:(cond).        (* [comment removed for export] *)
        stn_done. apply mst_refl.
      - post.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    Section D.
      Variable s4 : Z.
      Hypothesis Hs4 : (s4 = 0 \/ s4 = 4)%Z.
      Hypothesis Hs4v : v_andi (at_ d k) 4 = Z_to_bv 64 s4.

      #[local] Ltac blockD :=
        msw Fo_090 Do_090 (k + 12)%Z;                (* [comment removed for export] *)
        msw Fo_094 Do_094 (k + 16)%Z;                (* [comment removed for export] *)
        msw Fo_098 Do_098 (k + 20)%Z;                (* [comment removed for export] *)
        msw Fo_09c Do_09c (k + 24)%Z;                (* [comment removed for export] *)
        stepiv Fo_0a0 Do_0a0 (Z_to_bv 64 s4) ltac:(gres; rwH; imm_norm; exact Hs4v);          (* [comment removed for export] *)
        stepn Fo_0a4 Do_0a4;                         (* [comment removed for export] *)
        stepiv Fo_0a8 Do_0a8 (Z_to_bv 64 (s4 + 24)) ltac:(gres; rwH; imm_norm; apply ms_v_addi_Z; lia);  (* [comment removed for export] *)
        stepiv Fo_0ac Do_0ac (Z_to_bv 64 (n1 - s4 - 24)) ltac:(gres; rwH; rewrite ms_v_sub_ZZ by lia; f_equal; lia);  (* [comment removed for export] *)
        msw Fo_0b0 Do_0b0 (k + n1 - 28)%Z;           (* [comment removed for export] *)
        msw Fo_0b4 Do_0b4 (k + n1 - 24)%Z;           (* [comment removed for export] *)
        msw Fo_0b8 Do_0b8 (k + n1 - 20)%Z;           (* [comment removed for export] *)
        msw Fo_0bc Do_0bc (k + n1 - 16)%Z.           (* [comment removed for export] *)

      Lemma D_exit : forall regs,
        getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
        getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
        (9 <= n)%Z -> (28 <= n1)%Z -> (n1 - s4 - 24 < 32)%Z ->
        exists regs',
          msteps MSEGS (mkst regs (PC 0x90) (CF LC) rom) (mkst regs' ret (CF (LD s4)) rom)
          /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
      Proof.
        intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
        stn_eexists. split.
        - blockD.
          renm. stepb_tk Fo_0c0 Do_0c0 ltac:(cond).      (* [comment removed for export] *)
          mret.
          stn_done. apply mst_refl.
        - post.
      Qed.

      Lemma D_cont : forall regs,
        getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
        getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
        (9 <= n)%Z -> (28 <= n1)%Z -> (32 <= n1 - s4 - 24)%Z ->
        exists regs',
          msteps MSEGS (mkst regs (PC 0x90) (CF LC) rom) (mkst regs' (PC 0xc4) (CF (LD s4)) rom)
          /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d k /\ getr regs' 12 = c32 cv
          /\ getr regs' 14 = Z_to_bv 64 (n1 - s4 - 24) /\ getr regs' 15 = Z_to_bv 64 (s4 + 24)
          /\ getr regs' 1 = ret /\ ms_agree regs regs'.
      Proof.
        intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
        stn_eexists. split.
        - blockD.
          renm. stepb_ft Fo_0c0 Do_0c0 ltac:(cond).      (* [comment removed for export] *)
          stn_done. apply mst_refl.
        - post.
      Qed.

      (* [comment removed for export] *)
      (* [comment removed for export] *)
      (* [comment removed for export] *)

      Lemma E_run : forall regs L,
        getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
        getr regs 14 = Z_to_bv 64 (n1 - s4 - 24) -> getr regs 15 = Z_to_bv 64 (s4 + 24) -> getr regs 1 = ret ->
        (9 <= n)%Z -> (28 <= n1)%Z ->
        exists regs',
          msteps MSEGS (mkst regs (PC 0xc4) (CF L) rom) (mkst regs' (PC 0xd8) (CF L) rom)
          /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d (k + s4 + 24) /\ getr regs' 12 = c64 cv
          /\ getr regs' 13 = Z_to_bv 64 31 /\ getr regs' 14 = Z_to_bv 64 (n1 - s4 - 24)
          /\ getr regs' 1 = ret /\ ms_agree regs regs'.
      Proof.
        intros regs L H10 H11 H12 H14 H15 H1 Hn9 Hn1'. pose proof (u64_range d) as Hd. pclits.
        stn_eexists. split.
        - renm. stepiv Fo_0c4 Do_0c4 (c32h cv) ltac:(gres; rwH; imm_norm; apply slli32_c32).             (* [comment removed for export] *)
          renm. stepiv Fo_0c8 Do_0c8 (at_ d (k + s4 + 24)) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).  (* [comment removed for export] *)
          renm. stepiv Fo_0cc Do_0cc (c32 cv) ltac:(gres; rwH; imm_norm; apply srli32_c32h);             (* [comment removed for export] *)
          stepat ms_step_or_at Fo_0d0 Do_0d0 (c64 cv) ltac:(gres; rwH; apply or_c64).                 (* [comment removed for export] *)
          renm. stepn Fo_0d4 Do_0d4.                       (* [comment removed for export] *)
          stn_done. apply mst_refl.
        - post.
      Qed.
    End D.
  End Aligned.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[local] Ltac ms_cov_eq :=
    intros i Hi; rewrite !ms_cov_cons;
    match goal with |- _ = ?rhs => match rhs with context [ms_cov ?L i] => destruct (ms_cov L i) end end;
    rewrite ?orb_true_r, ?orb_false_r; [reflexivity|];
    apply eq_true_iff_eq; rewrite !orb_true_iff, !ms_inb_true; lia.

  (* [comment removed for export] *)
  Lemma loop_run : forall (q : nat) regs L a r,
    getr regs 10 = at_ d 0 -> getr regs 11 = at_ d a -> getr regs 12 = c64 cv ->
    getr regs 13 = Z_to_bv 64 31 -> getr regs 14 = Z_to_bv 64 r -> getr regs 1 = ret ->
    (0 <= a)%Z -> (a + r <= n)%Z ->
    (32 * (Z.of_nat q + 1) <= r < 32 * (Z.of_nat q + 1) + 32)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0xd8) (CF L) rom)
                   (mkst regs' (PC 0xf4) (CF ((a, 32 * (Z.of_nat q + 1))%Z :: L)) rom)
      /\ getr regs' 10 = at_ d 0 /\ getr regs' 1 = ret /\ ms_agree regs regs'.
  Proof.
    induction q as [|q IH]; intros regs L a r H10 H11 H12 H13 H14 H1 Ha Har Hq;
      pose proof (u64_range d) as Hd; pclits.
    - (* [comment removed for export] *)
      stn_eexists. split.
      + renm. msd Fo_0d8 Do_0d8 a.                         (* [comment removed for export] *)
        renm. msd Fo_0dc Do_0dc (a + 8)%Z.                 (* [comment removed for export] *)
        renm. msd Fo_0e0 Do_0e0 (a + 16)%Z.                (* [comment removed for export] *)
        renm. msd Fo_0e4 Do_0e4 (a + 24)%Z.                (* [comment removed for export] *)
        renm. stepiv Fo_0e8 Do_0e8 (Z_to_bv 64 (r - 32)) ltac:(gres; rwH; imm_norm; rewrite ms_v_addi_Z by lia; f_equal; lia).  (* [comment removed for export] *)
        renm. stepiv Fo_0ec Do_0ec (at_ d (a + 32)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).               (* [comment removed for export] *)
        renm. stepb_ft Fo_0f0 Do_0f0 ltac:(cond).        (* [comment removed for export] *)
        stn_open. replace (CF ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L))%Z
          with (CF ((a, 32 * (Z.of_nat 0 + 1))%Z :: L)) by (apply cfill_ext; ms_cov_eq).
        stn_done. apply mst_refl.
      + post.
    - eapply (runs_trans MSEGS _
                (fun rg => mkst rg (PC 0xd8) (CF ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L))%Z rom)
                (fun rg => getr rg 10 = at_ d 0 /\ getr rg 11 = at_ d (a + 32) /\ getr rg 12 = c64 cv
                           /\ getr rg 13 = Z_to_bv 64 31 /\ getr rg 14 = Z_to_bv 64 (r - 32) /\ getr rg 1 = ret
                           /\ ms_agree regs rg)).
      + cbv beta. pclits. stn_eexists. split.
        * renm. msd Fo_0d8 Do_0d8 a.
          renm. msd Fo_0dc Do_0dc (a + 8)%Z.
          renm. msd Fo_0e0 Do_0e0 (a + 16)%Z.
          renm. msd Fo_0e4 Do_0e4 (a + 24)%Z.
          renm. stepiv Fo_0e8 Do_0e8 (Z_to_bv 64 (r - 32)) ltac:(gres; rwH; imm_norm; rewrite ms_v_addi_Z by lia; f_equal; lia).
          renm. stepiv Fo_0ec Do_0ec (at_ d (a + 32)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).
          renm. stepb_tk Fo_0f0 Do_0f0 ltac:(cond).      (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * post.
      + cbv beta. intros r1 (R10 & R11 & R12 & R13 & R14 & R1 & AG).
        destruct (IH r1 ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L)%Z (a + 32)%Z (r - 32)%Z
                    R10 R11 R12 R13 R14 R1 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P10 & P1 & AG2).
        exists r2. split.
        * stn_open. replace (CF ((a, 32 * (Z.of_nat (S q) + 1))%Z :: L))
            with (CF ((a + 32, 32 * (Z.of_nat q + 1))%Z :: ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L)%Z))
            by (apply cfill_ext; ms_cov_eq).
          revert RUN. pclits. intros RUN. exact RUN.
        * OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption. eapply ms_agree_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma ret_run : forall regs (M : word -> option byte),
    getr regs 1 = ret ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0xf4) M rom) (mkst regs' ret M rom)
      /\ regs' = regs.
  Proof.
    intros regs M H1. pclits. eexists. split.
    - mret. apply mst_refl.
    - reflexivity.
  Qed.

End Walk.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
