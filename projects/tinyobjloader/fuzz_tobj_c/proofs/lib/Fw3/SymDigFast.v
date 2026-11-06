(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "ineq"; "stop_itv"; "fdig"; "i32_itv"; "dg_facts"; "lin"; "sfacts_itv"; "smeet"; "sadd32_itv"; "sadd_itv"; "srels_itv"; "add_new"; "dg_srels"; "dg_with_pool"; "endpoints"; "ifact"; "ineqs_of_rels"; "smax"; "smin"; "snorm"; "snorm32"; "stv_node"; "stv_t"; "dg_tbl"; "dg_urels"; "dg_with_tbl"; "ineq_subsumed"; "itv_t"; "lin_eqb"; "lin_round"; "mkDig"; "mk_bits"; "mk_cls"; "mk_ctx"; "mk_dig"; "mk_nes"; "mk_pool"; "ne_tighten"; "neq_prim"; "neqs_of"; "pool_round"; "rels_of"; "sat_depth"; "saturate"; "sclassify_fact"; "sfact_itv"; "sitv_of_itv"; "srels_of"; "ssub32_itv"; "ssub_itv"; "tbl_entry"; "tbl_init"; "tbl_iter"; "tbl_rounds"; "@Corelib.Init.Datatypes"; "bool"; "list"; "prod"; "fst"; "snd"; "pair"; "andb"; "false"; "nil"; "nat"; "true"; "app"; "cons"; "length"; "@Corelib.Init.Logic"; "eq"; "and"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "le"; "ltb"; "sub"; "pow"; "shiftr"; "modulo"; "of_N"; "opp"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymDigFast"; "sf_ok"; "pool_round_x"; "stv_t_x"; "add_new_lx"; "mk_ctx_x"; "mk_pool_x"; "saturate_x"; "sfilter"; "snorm32_h"; "snorm_h"; "stv_node_x"; "tbl_init_x"; "HM31"; "HM63"; "HMM31"; "HMM63"; "add_new_nx"; "existsb_lx"; "ineq_subsumed_x"; "mk_dig_x"; "s_rel"; "stv_body_x"; "@Corelib.Lists.ListDef"; "map"; "firstn"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool Lia.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition HM63 : Z := 2 ^ 63.   Definition HMM63 : Z := - 2 ^ 63.
Definition HM31 : Z := 2 ^ 31.   Definition HMM31 : Z := - 2 ^ 31.
Definition snorm_h (z : Z) : Z := ltac2:(tb__ "0|2|
S3bS0L_;M0S4bS65Vz;A2G0S4dVz;S63A2Vz;S18Vz;A1M1X3bx2G1X3bx2").
Definition snorm32_h (z : Z) : Z := ltac2:(tb__ "0|2|
S3bS0L_;M0S4bS64Vz;A2G0S4dVz;S62A2Vz;S19Vz;A1M1X3bx2G1X3bx2").
Lemma snorm_h_eq : ltac2:(tb__ "0|0|
S0S49S0S5fR1A1S18R1A1A3Fz;").
Proof.
  intros z. unfold snorm_h, HMM63, HM63.
  destruct (Z.leb_spec (- 2 ^ 63) z) as [H1|H1]; [|reflexivity].
  destruct (Z.ltb_spec z (2 ^ 63)) as [H2|H2]; [|reflexivity].
  unfold snorm. destruct (Z_lt_le_dec z 0) as [Hn|Hp].
  - assert (E : (z mod 2 ^ 64 = z + 2 ^ 64)%Z).
    { symmetry. apply (Z.mod_unique_pos z (2 ^ 64) (-1) (z + 2 ^ 64)); lia. }
    rewrite E. destruct (Z.ltb_spec (z + 2 ^ 64) (2 ^ 63)); lia.
  - rewrite (Z.mod_small z (2 ^ 64)) by lia. destruct (Z.ltb_spec z (2 ^ 63)); lia.
Qed.
Lemma snorm32_h_eq : ltac2:(tb__ "0|0|
S0S49S0S5eR1A1S19R1A1A3Fz;").
Proof.
  intros z. unfold snorm32_h, HMM31, HM31.
  destruct (Z.leb_spec (- 2 ^ 31) z) as [H1|H1]; [|reflexivity].
  destruct (Z.ltb_spec z (2 ^ 31)) as [H2|H2]; [|reflexivity].
  unfold snorm32. destruct (Z_lt_le_dec z 0) as [Hn|Hp].
  - assert (E : (z mod 2 ^ 32 = z + 2 ^ 32)%Z).
    { symmetry. apply (Z.mod_unique_pos z (2 ^ 32) (-1) (z + 2 ^ 32)); lia. }
    rewrite E. destruct (Z.ltb_spec (z + 2 ^ 32) (2 ^ 31)); lia.
  - rewrite (Z.mod_small z (2 ^ 32)) by lia. destruct (Z.ltb_spec z (2 ^ 31)); lia.
Qed.
Open Scope Z_scope.

Definition s_rel (f : sprop) : bool := ltac2:(tb__ "0|0|
S14S3bLx;S31Vf;A1S3S0S0S45Lhi;Llo;Lx;S42X14x2").
Fixpoint sfilter (facts : list sprop) : list sprop :=
  match facts with
  | [] => []
  | f :: rest => if s_rel f then f :: sfilter rest else sfilter rest
  end.

Definition sf_ok (sf facts : list sprop) : Prop := ltac2:(tb__ "0|0|
S3S49S3dS0S0A2SbVsf;R1A2SbVfacts;R1A2A3Fe;").

Lemma sfacts_itv_bounds : ltac2:(tb__ "0|1|
S3cS4A1S3S4aS4cS17S3eS0S0SbR2R1A2M0A3A2S4cS3fS0S0G0A3S16A2A2Fe;Ffacts;").
Proof.
  intros facts e. induction facts as [|f rest IH]; cbn [sfacts_itv].
  - split; apply Z.le_refl.
  - destruct IH as [I1 I2]. unfold smeet. cbn [fst snd]. split.
    + eapply Z.le_trans; [exact I1 | apply Z.le_max_r].
    + eapply Z.le_trans; [apply Z.le_min_r | exact I2].
Qed.

Lemma sfact_itv_irrel : ltac2:(tb__ "0|0|
S3S4S49S3bS6aR1A1S42A3S49S3dS0S0A2S32R3R2A2S6A3F_;Ff;Fe;").
Proof. intros e f H. unfold s_rel in H. unfold sfact_itv. destruct (sclassify_fact f); [discriminate | reflexivity]. Qed.

Lemma smeet_stop_l : ltac2:(tb__ "0|1|
S3dS0S0A2M0S4cS17S3eS0S0R1A3A2S4cS3fS0S0R2A3S16A2S49G0ScS6R3A2R3A3F_;F_;Fq;").
Proof.
  intros [l h] H1 H2. unfold smeet, stop_itv. cbn [fst snd] in *.
  rewrite (Z.max_r _ _ H1), (Z.min_r _ _ H2). reflexivity.
Qed.

Lemma sfilter_ok : ltac2:(tb__ "0|0|
S3cS4A1S56S5dR1A1R1A2Ffacts;").
Proof.
  intros facts e. induction facts as [|f rest IH]; [reflexivity|].
  cbn [sfilter]. destruct (s_rel f) eqn:E; cbn [sfacts_itv].
  - rewrite IH. reflexivity.
  - rewrite IH, (sfact_itv_irrel e f E).
    destruct (sfacts_itv_bounds rest e) as [B1 B2]. rewrite (smeet_stop_l _ B1 B2). reflexivity.
Qed.

Lemma srels_itv_sf : ltac2:(tb__ "0|1|
S3cS4A1M0G0S3cS3dS3dS3S0A2S3A2A1S3S56R4R3A2S49S3dS0S0A2SfR5R3R2A3SfR4R3R2A3A3F_;Fe;Frels;Ffacts;Fsf;").
Proof.
  intros sf facts rels e H. induction rels as [|[[x d] y] t IH]; [reflexivity|].
  cbn [srels_itv]. rewrite IH. unfold srel_itv1. rewrite !H. reflexivity.
Qed.

Definition stv_body_x (sf : list sprop) (rec : sv -> Z * Z) (dg : fdig) (e : sv) : Z * Z := ltac2:(tb__ "0|23|
S3S3dS0S0A2M0Le;Ve;S0S40S0S0S5fR1A1M1G1A4M2Lz;S1S6Li;M3S54S3S3S54G0Lop;M4R3S3G0Lb;M5R1S0SeVrec;R3A1M6G2A2Lc;S1SeG6Vrec;R2A1M7A2Li;S54S3S3SeVrec;R5A1M8Vrec;R4A1M9A2MaLb0;La0;MbLop0;McGcS55GbLop0;MdGdS3bS2S3GaLa0;Lw;Lsgn;S1S3S0GaLk;Li;Ll;X3x8S36G7Vrec;R1A1MeA2S6S6S6S6S6G5R1S0G6G0S51R2Z40MfA2S0S3bG0L_;M10S4bS3eS0S0R2A3M11S3fS0S0R2A3M12A2S40S0S0S50G11R1A2S50G12R1A2A4S6X3bx2Tk';Tp;Lk;G3S54S3S3S6Lb0;La0;M13Lop0;M14G14S55G13Lop0;M15G15S3bS2S3S6La0;Lw;Lsgn;S1S3S0S6Lk;Li;Ll;M16X3x8S6S6X54xaLb;La;Lop;S54S3S3G4R3G5R1S0SdG6S40S0S0S5eR1A1M17G17A4A2Lc;S1SdG6G7A2Li;S54S3S3SdG8G9A2M18Lb0;La0;M19Lop0;M1aG1aS55G19Lop0;M1bG1bS3bS2S3G18La0;Lw;Lsgn;S1S3S0G18Lk;Li;Ll;X3x8S35G7GeA2S8S8S8S8S8S8S8S8X54xaLb;La;Lop;S55S3S3S6Lb;La;Lop;S55S3S3S8Lb;La;Lop;S3bS2S3S3bG0Lsgn;R3S52R2A1M1cS0G10S41S4dZ0M1dR1A2S4bR1GfA2A2S40S0S0S53S4fZ2M1eS4eR1Z1M1fA2A2M20A1S4eG20G1fA2A4G0G6G0G10S41S41S4bS3eS0S0R1A3M21S3fS0S0R1A3M22A2S4bG11G21A2A2S4bG22G12A2A2R1R2X3bx2Tp;Tr;S6X3bx2Twz;G1cS0G10S41S4bG1dR1A2S4dR1GfA2A2S40S0S0G1dS4eS4fG1eR1A2G1fA2A4S6X3bx2Twz;X3bx2La;Lw;Lsgn;G16X3x8G0ScScScR1S33S20Vdg;Ve;A2A1A2SbVsf;Ve;A2A2SfVsf;S11Vdg;A1Ve;A3A2Tstructural;").

Fixpoint stv_t_x (sf : list sprop) (dg : fdig) (e : sv) : Z * Z :=
  match tbl_find (dg_tbl dg) e with
  | Some v => snd v
  | None => stv_body_x sf (fun a => stv_t_x sf dg a) dg e
  end.

Definition stv_node_x (sf : list sprop) (dg : fdig) (e : sv) : Z * Z := ltac2:(tb__ "0|0|
S6bVsf;S3S58Vsf;Vdg;R1A3La;Vdg;Ve;A4").

Lemma stv_node_t_x_eq : ltac2:(tb__ "0|1|
S3cS4A1S7S56R2S9R1A1A2S3S4aS49S3dS0S0A2M0S58R4R3R1A3S1bR3R1A2A3S49G0S60R4R3R1A3S1aR3R1A2A3A2Fe;F_;Fdg;Fsf;").
Proof.
  intros sf dg H.
  assert (TAIL : forall e s s', s = s' ->
            smeet (smeet (smeet s (sitv_of_itv (itv_t dg e))) (sfacts_itv sf e)) (srels_itv sf (dg_srels dg) e)
            = smeet (smeet (smeet s' (sitv_of_itv (itv_t dg e))) (sfacts_itv (dg_facts dg) e))
                    (srels_itv (dg_facts dg) (dg_srels dg) e)).
  { intros e s s' <-. rewrite (H e), (srels_itv_sf sf (dg_facts dg) _ e H). reflexivity. }
  assert (NODE : forall e, (forall a, stv_t_x sf dg a = stv_t dg a) -> stv_node_x sf dg e = stv_node dg e).
  { intros e Hrec. unfold stv_node_x, stv_node, stv_body_x, stv_body. cbv zeta. apply TAIL.
    destruct e as [z|i|op a b|op a b|op a b|op a b|sgn w a|l i k]; try reflexivity;
      try destruct op; try destruct sgn;
      rewrite ?snorm_h_eq, ?snorm32_h_eq;
      solve [rewrite ?Hrec; reflexivity | destruct b; rewrite ?Hrec, ?snorm_h_eq, ?snorm32_h_eq; reflexivity]. }
  assert (T : forall e, stv_t_x sf dg e = stv_t dg e).
  { induction e as [z|i|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sgn w a IHa|l i IHi k];
      cbn [stv_t_x stv_t]; (destruct (tbl_find (dg_tbl dg) _); [reflexivity|]);
      unfold stv_body_x, stv_body; cbv zeta; apply TAIL; try reflexivity;
      try destruct op; try destruct sgn;
      rewrite ?snorm_h_eq, ?snorm32_h_eq;
      solve [rewrite ?IHa, ?IHb; reflexivity | destruct b; rewrite ?IHa, ?IHb, ?snorm_h_eq, ?snorm32_h_eq; reflexivity]. }
  intros e. split; [apply T | apply NODE; exact T].
Qed.

Lemma stv_t_x_eq : ltac2:(tb__ "0|0|
S3cS4A1S7S3S56R3S9R2A1A2S49S3dS0S0A2S58R4R3R2A3S1bR3R2A2A3F_;Fe;Fdg;Fsf;").
Proof. intros sf dg e H. apply (stv_node_t_x_eq sf dg H e). Qed.
Lemma stv_node_x_eq : ltac2:(tb__ "0|0|
S3cS4A1S7S3S56R3S9R2A1A2S49S3dS0S0A2S60R4R3R2A3S1aR3R2A2A3F_;Fe;Fdg;Fsf;").
Proof. intros sf dg e H. apply (stv_node_t_x_eq sf dg H e). Qed.

Fixpoint tbl_init_x (sf : list sprop) (dg : fdig) (es : list sv) : fdig :=
  match es with
  | [] => dg
  | e :: rest =>
      let pu := itv_node dg e in
      let dg1 := dg_with_tbl dg ((e, (pu, stop_itv)) :: dg_tbl dg) in
      let ps := stv_node_x sf dg1 e in
      tbl_init_x sf (dg_with_tbl dg ((e, (itv_meet pu (u_of_s ps), smeet ps (sitv_of_itv pu))) :: dg_tbl dg)) rest
  end.

Lemma tbl_init_x_eq : ltac2:(tb__ "0|0|
S3cS4A1S3cS3A1S7S56R3S9R1A1A2S49S7S61R4R2R3A3S38R2R3A2A3F_;Fdg;Fes;Fsf;").
Proof.
  intros sf es. induction es as [|e rest IH]; intros dg H; cbn [tbl_init_x tbl_init]; [reflexivity|].
  cbv zeta. rewrite (stv_node_x_eq sf _ e); [|exact H]. apply IH. exact H.
Qed.

Definition mk_ctx_x (facts : list sprop) : fdig := ltac2:(tb__ "0|2|
S2eVfacts;A1S3cS3dS3dS3S0A2S3A2A1M0S34Vfacts;A1G0S23Vfacts;S25Vfacts;A1S28Vfacts;A1S24Vfacts;A1R2R1S43S37A1S43S5A1A8S7S3cS3A1M1S7Lx;S13R2S13R3S43S3A1A2A2R1S3G1S61S5dVfacts;A1R3S47S3R2R1A3A3S7S1eR1S39S3aR6R5S1cR1A1A4A2Tdg1;Ll;Ls;X3cx2Tdg0;Tsrels;Turels;").

Theorem mk_ctx_x_eq : ltac2:(tb__ "0|0|
S3cS4A1S49S7S5aR1A1S26R1A1A3Ffacts;").
Proof.
  intros facts. unfold mk_ctx_x, mk_ctx. cbv zeta.
  destruct (endpoints (srels_of facts) (endpoints (rels_of facts) [])) as [|e0 es]; [reflexivity|].
  rewrite (tbl_init_x_eq (sfilter facts) (e0 :: es)); [reflexivity|]. cbn [dg_facts]. apply sfilter_ok.
Qed.

Fixpoint existsb_lx {A} (f : A -> bool) (l : list A) : bool :=
  match l with [] => false | x :: t => if f x then true else existsb_lx f t end.
Lemma existsb_lx_eq : forall {A} (f : A -> bool) l, existsb_lx f l = existsb f l.
Proof. intros A f l. induction l as [|x t IH]; cbn [existsb_lx existsb]; [reflexivity|]. rewrite IH. destruct (f x); reflexivity. Qed.

Definition ineq_subsumed_x (pool : list ineq) (g : ineq) : bool := ltac2:(tb__ "0|1|
S67S3dSaS0A2M0G0S3bS3bL_;S21S3eSaS0Vg;A3S3eSaS0R1A3A2S4bS3fSaS0R1A3S3fSaS0Vg;A3A2S42X3bx2Lh;Vpool;A3").
Lemma ineq_subsumed_x_eq : ltac2:(tb__ "0|0|
S3cS5A1S5S49S3bS68R2R1A2S1fR2R1A2A3Fg;Fpool;").
Proof.
  intros pool g. unfold ineq_subsumed_x, ineq_subsumed. rewrite existsb_lx_eq.
  induction pool as [|h t IH]; cbn [existsb]; [reflexivity|]. rewrite IH.
  destruct (lin_eqb (fst g) (fst h)); reflexivity.
Qed.

Fixpoint add_new_lx (pool fresh : list ineq) : list ineq :=
  match fresh with
  | [] => []
  | g :: rest => if ineq_subsumed_x pool g then add_new_lx pool rest else g :: add_new_lx (g :: pool) rest
  end.
Lemma add_new_lx_eq : ltac2:(tb__ "0|1|
S3cS5A1M0G0S49G0S59R1R2A2S10R1R2A2A3Fpool;Ffresh;").
Proof.
  induction fresh as [|g rest IH]; intros pool; cbn [add_new_lx add_new]; [reflexivity|].
  rewrite ineq_subsumed_x_eq. destruct (ineq_subsumed pool g); rewrite IH; reflexivity.
Qed.

Fixpoint add_new_nx (n : nat) (pool fresh : list ineq) {struct fresh} : list ineq :=
  match fresh with
  | [] => []
  | g :: rest =>
      match n with
      | O => []
      | S n' => if ineq_subsumed_x pool g then add_new_nx n pool rest else g :: add_new_nx n' (g :: pool) rest
      end
  end.
Lemma add_new_nx_eq : ltac2:(tb__ "0|1|
S3cS5A1M0S44G0S49G0S66R2R1R3A3S6dS5R2S10R1R3A2A3A3Fpool;Fn;Ffresh;").
Proof.
  induction fresh as [|g rest IH]; intros n pool; cbn [add_new_nx add_new].
  - destruct n; reflexivity.
  - destruct n as [|n']; [reflexivity|]. rewrite ineq_subsumed_x_eq.
    destruct (ineq_subsumed pool g); [apply IH|]. cbn [firstn]. rewrite IH. reflexivity.
Qed.

Fixpoint saturate_x (n : nat) (neqs : list ineq) (news pool : list ineq) (base : list ineq) : list ineq :=
  match n with
  | O => pool
  | S n' => let fresh := add_new_nx pool_cap pool (map (ne_tighten (length neqs) neqs) (combine_all news base)) in
            saturate_x n' neqs fresh (pool ++ fresh) base
  end.
Lemma saturate_x_eq : ltac2:(tb__ "0|1|
S44S3cS5A1M0G0G0G0S49G0S5cR5R4R3R2R1A5S30R5R4R3R2R1A5A3Fbase;Fpool;Fnews;Fneqs;Fn;").
Proof.
  induction n as [|n IH]; intros neqs news pool base; cbn [saturate_x saturate]; [reflexivity|].
  cbv zeta. rewrite add_new_nx_eq. apply IH.
Qed.

Definition pool_round_x (dg : fdig) : list ineq := ltac2:(tb__ "0|3|
S6cS5S5S2bS2cVdg;S9Vdg;A1M0A2A4S3cS5A1M1S59S43S5A1S6cS5S5S22G0A1M2S6cS5S5S2aS48S5R1A2R1A2S6cS5S5G2S46S5S15Vdg;S42S1dVdg;A1A3S15Vdg;S45S11Vdg;A1A3A3A4A4A4A2G1S6cS5S5G2S5cS2fR2R1R1R1A5A4Tbase;Tneqs;").
Lemma pool_round_x_eq : ltac2:(tb__ "0|0|
S7S49S3cS5A1S57R1A1S2dR1A1A3Fdg;").
Proof. intros dg. unfold pool_round_x, pool_round. cbv zeta. rewrite add_new_lx_eq, saturate_x_eq. reflexivity. Qed.

Definition mk_pool_x (dg : fdig) : list ineq := ltac2:(tb__ "0|0|
S57Vdg;A1S3cS5A1S57S12Vdg;R1A2A1Tp1;").
Lemma mk_pool_x_eq : ltac2:(tb__ "0|0|
S7S49S3cS5A1S5bR1A1S29R1A1A3Fdg;").
Proof. intros dg. unfold mk_pool_x, mk_pool. cbv zeta. rewrite !pool_round_x_eq. reflexivity. Qed.

Definition mk_dig_x (facts : list sprop) : fdig := ltac2:(tb__ "0|0|
S5aVfacts;A1S7S12R1S5bR1A1A2Tdg;").

Theorem mk_dig_x_eq : ltac2:(tb__ "0|0|
S3cS4A1S49S7S69R1A1S27R1A1A3Ffacts;").
Proof. intros facts. unfold mk_dig_x, mk_dig. cbv zeta. rewrite mk_pool_x_eq, mk_ctx_x_eq. reflexivity. Qed.
