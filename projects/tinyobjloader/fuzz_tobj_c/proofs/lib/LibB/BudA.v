(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "iff"; "True"; "not"; "@Corelib.Init.Datatypes"; "bool"; "list"; "prod"; "true"; "andb"; "fst"; "snd"; "app"; "pair"; "false"; "nil"; "option"; "nat"; "Some"; "cons"; "orb"; "S"; "length"; "negb"; "None"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "leb"; "mul"; "sub"; "div"; "max"; "pow"; "eqb"; "lt"; "of_nat"; "opp"; "ge"; "min"; "ltb"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "lform"; "bsumK"; "bsumV"; "plist"; "bd_nn"; "bd_wpos"; "lfval"; "BUD"; "bxt"; "zlog_aux"; "uval"; "bi_f"; "BXok_d"; "zlog15"; "KU"; "bxV"; "BE_MAX"; "bxS"; "plogsum"; "bd_subst"; "bi_c"; "cntSZ"; "BC_MAX"; "bival"; "bxN"; "BXok"; "bud_pay"; "lf_nonneg"; "plsum"; "aval"; "bd_below"; "lf_neg"; "lf_nonneg_p"; "plexp"; "sp_nlog"; "sp_plog"; "wformK"; "wformV"; "ASv"; "BXnn"; "LARGE_MIN"; "asv"; "bxK"; "is_smallZ"; "item_le"; "item_nn"; "item_nonneg"; "lf_split"; "pay_sem"; "pl_ok"; "split"; "BI"; "TVMAX"; "bud_le"; "bud_le_pos"; "bx2"; "e_bounded"; "item_le_p"; "lf_expand"; "lf_nonneg0"; "lf_norm"; "lit_le"; "pair_logs"; "pay_okF"; "pl_le"; "pl_ok_p"; "remove_first"; "sp_c"; "sp_neg"; "sp_pos"; "AMin"; "BN_MAX"; "SECCAP"; "SP"; "bd_vars_all"; "bi_k"; "bi_v"; "bud_le_pos_lz"; "bud_le_ref"; "bud_pay_lz"; "item_nonneg_p"; "items_nn_lz"; "lf_nonneg0_p"; "pair_logs_p"; "pl_le_p"; "split_val"; "ALog"; "ZK"; "amin_fact_lin"; "amin_fact_sat"; "amin_ok"; "atom_subst"; "batom_eqb"; "bi_subst"; "e_bounded_p"; "item_nn_lz"; "lf_addc"; "lf_scale"; "lf_subst"; "lf_vars_all"; "lit_atom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sprop"; "holds"; "eval"; "SLit"; "SPUle"; "SAlu"; "sv_eqb"; "sv_below"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Stdlib.Lists.List"; "forallb"; "In"; "fold_right"; "existsb"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "mk_pf"; "pfacts"; "prove_sprop_pf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "sv_subst"; "rho_sub"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "sv_vars_all"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "VMAX"; "KMAX"; "limit_ok_alloc"; "limit_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "existsb_lazy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "prove_sprop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA"; "mk_pf_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_V"; "PRIM_LIVE_MAX"; "SEC_SLACK"; "is_large"; "large_live"; "prim_room"; "sec_room"; "small_live"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@Corelib.Init.Nat"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "M64v"; "@Stdlib.Sorting.Permutation"; "Permutation"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundW SymFrame SymEntail SymCFG SymSummary SymDigFast SymObjFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Budget Model.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition KU : Z := 65536.

Fixpoint zlog_aux (n : nat) (y x : Z) : Z :=
  match n with O => 0 | S n' => if y <=? x then 1 + zlog_aux n' (y + y / 2) x else 0 end.
Definition zlog15 (x : Z) : Z := zlog_aux 128 2 x.

Lemma zlog_aux_range : ltac2:(tb__ "0|1|
S15S0S0S4S1dZ0S38R3R2R1A3M0A2S1dG0S27R3A1A2A2Fx;Fy;Fn;").
Proof. induction n as [|n IH]; intros y x; cbn [zlog_aux]; [lia|]. destruct (y <=? x); [|lia]. specialize (IH (y + y / 2) x). lia. Qed.
Lemma zlog_aux_S : ltac2:(tb__ "0|0|
S15S0S0S3S0S38S19R3A1R2R1A3S9S0L_;S1fR2R1A2S1eZ1S38R3S1eR2S22R2Z2A2A2R1A3A2Z0X9x2A3Fx;Fy;Fn;").
Proof. intros. reflexivity. Qed.
Lemma zlog15_eq : ltac2:(tb__ "0|0|
S0S3S0S3cR1A1S38U80Z2R1A3A3Fx;").
Proof. intros. unfold zlog15. reflexivity. Qed.
Global Opaque zlog15.
Lemma zlog15_range : ltac2:(tb__ "0|1|
S0S4S1dZ0S3cR1A1M0A2S1dG0Z80A2A2Fx;").
Proof. intros x. rewrite (zlog15_eq x). pose proof (zlog_aux_range 128 2 x). change (Z.of_nat 128) with 128 in H. lia. Qed.
Lemma zlog_aux_mono : ltac2:(tb__ "0|0|
S15S0S0S0S1dR2R1A2S1dS38R5R4R3A3S38R5R4R2A3A2F_;Fx';Fx;Fy;Fn;").
Proof.
  induction n as [|n IH]; intros y x x' H; cbn [zlog_aux]; [lia|].
  destruct (Z.leb_spec y x); destruct (Z.leb_spec y x'); try lia.
  - specialize (IH (y + y / 2) x x' H). lia.
  - pose proof (zlog_aux_range n (y + y / 2) x'). lia.
Qed.
Lemma zlog15_mono : ltac2:(tb__ "0|0|
S0S0S1dR2R1A2S1dS3cR3A1S3cR2A1A2F_;Fx';Fx;").
Proof. intros x x' H. rewrite (zlog15_eq x), (zlog15_eq x'). apply zlog_aux_mono. assumption. Qed.

Lemma zlog_aux_step : ltac2:(tb__ "0|1|
S15S0S0S1dZ1R2A2S29S38R4S1eR3S22R3Z2M0A2A2S1eR2S22R2G0A2A2A3S38R4R3R2A3A2F_;Fx;Fy;Fn;").
Proof.
  induction n as [|n IH]; intros y x Hy; cbn [zlog_aux]; [lia|].
  destruct (Z.leb_spec y x) as [Hle|Hgt].
  - assert (Hle' : y + y / 2 <= x + x / 2) by (pose proof (Z.div_le_mono y x 2 ltac:(lia) Hle); lia).
    apply Z.leb_le in Hle'. rewrite Hle'.
    specialize (IH (y + y / 2) x ltac:(pose proof (Z.div_pos y 2); lia)). lia.
  - pose proof (zlog_aux_range n ((y + y / 2) + (y + y / 2) / 2) (x + x / 2)). destruct (y + y / 2 <=? x + x / 2); lia.
Qed.

Lemma grow2 : ltac2:(tb__ "0|2|
S0S1dZ2M0R1A2S1dS20G0R2A2S1eS1eR2S22R2G0A2A2M1S22G1G0A2A2A2F_;Fy;").
Proof. intros y Hy. pose proof (Z.div_mod y 2 ltac:(lia)). pose proof (Z.mod_pos_bound y 2 ltac:(lia)).
  pose proof (Z.div_mod (y + y / 2) 2 ltac:(lia)). pose proof (Z.mod_pos_bound (y + y / 2) 2 ltac:(lia)). lia. Qed.
Lemma zlog_aux_fuel : ltac2:(tb__ "0|2|
S15S0S0S1dZ2M0R2A2S26R2S20R3S24G0S27R4A1A2A2A2S3S0S38Sc2U2R5A2M1R4R3A3S38S19G1A1R4R3A3A3F_;F_;Fx;Fy;Fm;").
Proof.
  induction m as [|m IH]; intros y x Hy Hx.
  - change (2 * 0)%nat with 0%nat. rewrite Nat2Z.inj_0, Z.pow_0_r, Z.mul_1_r in Hx. cbn. destruct (Z.leb_spec y x); lia.
  - replace (2 * S m)%nat with (S (S (2 * m))) by lia. cbn [zlog_aux].
    destruct (Z.leb_spec y x) as [H1|H1]; [|reflexivity].
    destruct (Z.leb_spec (y + y / 2) x) as [H2|H2]; [|reflexivity].
    f_equal. f_equal. apply IH; [pose proof (Z.div_pos y 2); lia|].
    pose proof (grow2 y Hy). rewrite Nat2Z.inj_succ in Hx. rewrite Z.pow_succ_r in Hx by lia. nia.
Qed.

Lemma zlog_aux_grow : ltac2:(tb__ "0|1|
S15S0S1dZ2M0R1A2S29S38S19R3A1G0S1eR2S22R2G0A2A2A3S1eS38R3G0R2A3Z1A2A2F_;Fx;Fn;").
Proof.
  intros n x Hx. cbn [zlog_aux]. assert (H8 : 2 <= x + x / 2) by (pose proof (Z.div_pos x 2); lia).
  apply Z.leb_le in H8. rewrite H8. pose proof (zlog_aux_step n 2 x ltac:(lia)) as ST. set (a := zlog_aux n (2 + 2 / 2) (x + x / 2)) in *. set (b := zlog_aux n 2 x) in *. lia.
Qed.
Lemma zlog_aux_fuel_mono : ltac2:(tb__ "0|0|
S15S0S0S1dS38R3R2R1A3S38S19R3A1R2R1A3A2Fx;Fy;Fn;").
Proof.
  induction n as [|n IH]; intros y x; cbn [zlog_aux].
  - pose proof (zlog_aux_range 0 (y + y / 2) x). destruct (y <=? x); cbn; lia.
  - destruct (y <=? x); [|lia]. specialize (IH (y + y / 2) x). cbn [zlog_aux] in IH. lia.
Qed.

Lemma zlog15_small : ltac2:(tb__ "0|1|
S0S4S1dZ0R1A2S26R1S24Z2M0Z3eA2A2A2S3S0S38U7fG0R2A3S38U80G0R2A3A3F_;Fx;").
Proof.
  intros x Hx.
  assert (F1 : zlog_aux 126 2 x = zlog_aux 127 2 x).
  { change 126%nat with (2 * 63)%nat. change 127%nat with (S (2 * 63))%nat. apply zlog_aux_fuel; [lia|].
    change (Z.of_nat 63) with 63. change (2 * 2 ^ 63) with (2 ^ 64). lia. }
  assert (G : forall n y, zlog_aux n y x = zlog_aux (S n) y x -> zlog_aux (S n) y x = zlog_aux (S (S n)) y x).
  { induction n as [|n IH]; intros y HE; cbn [zlog_aux] in HE |- *; revert HE; destruct (Z.leb_spec y x); intros HE; try reflexivity.
    - exfalso. pose proof (zlog_aux_range 0 (y + y/2) x) as R0. cbn [zlog_aux Z.of_nat] in R0. set (a := zlog_aux 0 (y + y / 2) x) in *. cbn [zlog_aux] in a. lia.
    - f_equal. apply IH. cbn [zlog_aux]. set (a := zlog_aux n (y + y / 2) x) in *. lia. }
  exact (G 126%nat 2 F1).
Qed.
Lemma zlog15_grow : ltac2:(tb__ "0|1|
S0S1dZ2M0R1A2S26R2S24G0Z3dA2A2S29S3cS1eR3S22R3G0A2A2A1S1eS3cR3A1Z1A2A2F_;F_;Fx;").
Proof.
  intros x Hx Hb. rewrite (zlog15_eq x), (zlog15_eq (x + x / 2)).
  rewrite <- (zlog15_small x ltac:(lia)). apply zlog_aux_grow. exact Hx.
Qed.
Lemma zlog15_0 : zlog15 0 = 0. Proof. rewrite (zlog15_eq 0). rewrite zlog_aux_S. reflexivity. Qed.
Lemma zlog15_ge1 : ltac2:(tb__ "0|0|
S0S1dZ2R1A2S1dZ1S3cR2A1A2F_;Fx;").
Proof. intros x Hx. rewrite (zlog15_eq x), zlog_aux_S. apply Z.leb_le in Hx. rewrite Hx. pose proof (zlog_aux_range 127 (2 + 2 / 2) x). lia. Qed.
Lemma zlog15_1 : zlog15 1 = 0. Proof. rewrite (zlog15_eq 1). rewrite zlog_aux_S. reflexivity. Qed.

Definition ZK : Z := 54.
Lemma zlog15_ZK : ltac2:(tb__ "0|0|
S0S1dR1S24Z2Z20A2A2S1dS3cR2A1S86A2F_;Fx;").
Proof.
  intros x Hx. apply Z.le_trans with (zlog15 (2 ^ 32)); [apply zlog15_mono; exact Hx|].
  apply Z.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Inductive batom := ASv (e : sv) | ALog (e : sv) | AMin (e : sv) (c1 k B : Z).

Definition lform := list (Z * batom).
Record bitem := BI { bi_v : Z; bi_k : Z; bi_f : lform; bi_c : Z }.

Definition BIs (cV cK : Z) (e : sv) : bitem := ltac2:(tb__ "0|1|
S62VcV;VcK;S17SbS0S2eA2M0S11S0S2eZ1S55Ve;A1A4S13G0A1A3Z0A4").
Definition BIc (cV cK : Z) (z : Z) : bitem := ltac2:(tb__ "0|0|
S62VcV;VcK;S13SbS0S2eA2A1Vz;A4").

Definition uval (rho : valuation) (e : sv) : Z := bv_unsigned (eval rho e).
Definition asv (a : batom) : sv := match a with ASv e => e | ALog e => e | AMin e _ _ _ => e end.
Definition aval (rho : valuation) (a : batom) : Z := ltac2:(tb__ "0|1|
S2eS0La;Va;S95S39Vrho;R1A2M0Le;S95S3cG0A1Le;S95S0S0S0S23Z0S2aS1eS20R3S39Vrho;R4A2A2R2A2R1A2A2LB;Lk;Lc1;Le;X2ex3").
Fixpoint lfval (rho : valuation) (f : lform) : Z := match f with [] => 0 | (c, a) :: r => c * aval rho a + lfval rho r end.
Definition bival (rho : valuation) (it : bitem) : Z := ltac2:(tb__ "0|0|
S1eS35Vrho;S3aVit;A1A2S43Vit;A1A2").

Fixpoint bsumV (b : list bitem) (rho : valuation) : Z :=
  match b with [] => 0 | i :: r => bi_v i * bival rho i + bsumV r rho end.
Fixpoint bsumK (b : list bitem) (rho : valuation) : Z :=
  match b with [] => 0 | i :: r => bi_k i * bival rho i + bsumK r rho end.

Definition atom_subst (s : wsub) (a : batom) : batom := ltac2:(tb__ "0|1|
S2eS2eLa;Va;S95S55Sa9Vs;R1A2M0A1Le;S95S85G0A1Le;S95S0S0S0S75Sa9Vs;R4A2R3R2R1A4LB;Lk;Lc1;Le;X2ex3").
Definition lf_subst (s : wsub) (f : lform) : lform := ltac2:(tb__ "0|1|
S9fSbS0S2eA2M0G0G0S11S0S2eSeS0S2eR1A3S8aVs;SfS0S2eR1A3A2A4Lca;Vf;A4").
Definition bi_subst (s : wsub) (it : bitem) : bitem := ltac2:(tb__ "0|0|
S62S7bVit;A1S7aVit;A1S91Vs;S3aVit;A1A2S43Vit;A1A4").
Definition bd_subst (s : wsub) (b : list bitem) : list bitem := map (bi_subst s) b.
Definition lf_vars_all (f : positive -> bool) (l : lform) : bool := ltac2:(tb__ "0|1|
Sa0SbS0S2eA2M0G0SadVf;S58SfS0S2eR1A3A1A2Lca;Vl;A3").
Definition bd_vars_all (f : positive -> bool) (b : list bitem) : bool := ltac2:(tb__ "0|0|
Sa0S2dS2dS92Vf;S3aR1A1A2Lit;Vb;A3").
Definition bd_below (n : positive) (b : list bitem) : bool := ltac2:(tb__ "0|1|
Sa0S2dS2dSa0SbS0S2eA2M0G0S9dVn;S58SfS0S2eR1A3A1A2Lca;S3aR1A1A3Lit;Vb;A3").

Definition bd_wpos (b : list bitem) : bool := ltac2:(tb__ "0|1|
Sa0S2dS2dSdS1fZ0M0S7bR1A1A2S1fG0S7aR1A1A2A2Lit;Vb;A3").

Lemma uval_range : ltac2:(tb__ "0|1|
S94S95S4S1dZ0S39R2R1A2M0A2S26G0S24Z2Z40A2A2A2Fe;Frho;").
Proof. intros. unfold uval. rewrite M64v_eq. apply U_range. Qed.
Lemma aval_nonneg : ltac2:(tb__ "0|0|
S94S2eS1dZ0S4cR2R1A2A2Fa;Frho;").
Proof. intros rho [e|e|e c1 k B]; cbn [aval]; [pose proof (uval_range rho e); lia | pose proof (zlog15_range (uval rho e)); lia | lia]. Qed.

Lemma lfval_ext : ltac2:(tb__ "0|1|
SaSbS0S2eA2M0A1S94S94S2eS2eF_;S0S2eSa1G0S11S0S2eR2R1A4R6A3S3S0S4cR6R4R2A1A2S4cR5R2A2A3F_;Fa;Fc;S3S0S35R4S9fG0G0G0S11S0S2eSeS0S2eR1A3R3SfS0S2eR1A3A1A4Lca;R5A4A2S35R3R5A2A3F_;Fg;Fr2;Fr1;Ff;").
Proof.
  intros f r1 r2 g. induction f as [|[c a] r IH]; intros H; cbn; [reflexivity|].
  rewrite (H c a ltac:(left; reflexivity)). rewrite (IH ltac:(intros c' a' Hin; apply (H c'); right; exact Hin)). reflexivity.
Qed.
Lemma bsum_ext : ltac2:(tb__ "0|2|
SaS2dA1S94S94Sa8S95S5S2dS2dS5SbS0S2eA2M0G0S4Sa1S2dR2R7A3S4Sa1G0R1S3aR2A1A3S3S95S58SfS0S2eR1A3A1R3A3A2A2Lca;A2Lit;A2S3SabQ40A1S98R5Sa9R3R2A2A2S98R4R2A2A3F_;Fe;S4S3S0S31S42R2R5A2M1R4A2S31R5R3A2A3S3S0S30G1R4A2S30R5R3A2A3A2F_;Fs;Fr2;Fr1;Fb;").
Proof.
  intros b r1 r2 s H. induction b as [|it r IH]; [cbn; auto|].
  assert (E : bival r1 (bi_subst s it) = bival r2 it).
  { unfold bival, bi_subst. cbn [bi_f bi_c]. unfold lf_subst. rewrite (lfval_ext (bi_f it) r1 r2 (atom_subst s)); [reflexivity|].
    intros c a Hin. destruct a as [e|e|e c1 k B]; cbn [aval atom_subst]; unfold uval; rewrite (H e); try reflexivity;
      [exists it, (c, ASv e) | exists it, (c, ALog e) | exists it, (c, AMin e c1 k B)]; (split; [left; reflexivity|]; split; [exact Hin|reflexivity]). }
  revert IH. intros IH. destruct IH as [IH1 IH2]; [intros e (it' & ca & Hit & Hca & He); apply H; exists it', ca; repeat split; [right; exact Hit | exact Hca | exact He]|].
  change (bd_subst s (it :: r)) with (bi_subst s it :: bd_subst s r). cbn [bsumV bsumK].
  change (bi_v (bi_subst s it)) with (bi_v it). change (bi_k (bi_subst s it)) with (bi_k it).
  rewrite E, IH1, IH2. auto.
Qed.
Lemma bsumV_subst : ltac2:(tb__ "0|0|
Sa8SaS2dA1S94S3S0S31S42R3R2A2R1A2S31R2SaaR1R3A2A2A3Frho;Fb;Fs;").
Proof. intros. apply (proj1 (bsum_ext b rho (rho_sub rho s) s ltac:(intros; apply eval_subst))). Qed.
Lemma bsumK_subst : ltac2:(tb__ "0|0|
Sa8SaS2dA1S94S3S0S30S42R3R2A2R1A2S30R2SaaR1R3A2A2A3Frho;Fb;Fs;").
Proof. intros. apply (proj2 (bsum_ext b rho (rho_sub rho s) s ltac:(intros; apply eval_subst))). Qed.
Lemma rho_sub_nil : ltac2:(tb__ "0|0|
S94S3S94SaaR1S13SbS1S95A2A1A2R1A3Frho;").
Proof. intros rho. destruct rho. reflexivity. Qed.
Lemma bsum_agree : ltac2:(tb__ "0|0|
S1S94S94SaS2dA1SacR4R3R2A3S3S9S4dR5R2A2ScA3S4S3S0S31R3R4A2S31R3R5A2A3S3S0S30R3R4A2S30R3R5A2A3A2F_;F_;Fb;Frho';Frho;Fn;").
Proof.
  intros n rho rho' b Hag Hb.
  destruct (bsum_ext b rho' rho' [] ltac:(intros e _; rewrite eval_subst, rho_sub_nil; reflexivity)) as [A1 A2].
  destruct (bsum_ext b rho' rho []) as [B1 B2].
  { intros e (it & ca & Hit & Hca & <-). rewrite eval_subst, rho_sub_nil. symmetry. eapply eval_agree_vals; [exact Hag|].
    unfold bd_below in Hb. pose proof (proj1 (forallb_forall _ _) Hb it Hit) as X. exact (proj1 (forallb_forall _ _) X ca Hca). }
  split; congruence.
Qed.
Lemma bsumV_agree : ltac2:(tb__ "0|0|
S1S94S94SaS2dA1SacR4R3R2A3S3S9S4dR5R2A2ScA3S3S0S31R3R4A2S31R3R5A2A3F_;F_;Fb;Frho';Frho;Fn;").
Proof. intros. eapply (proj1 (bsum_agree _ _ _ _ H H0)). Qed.
Lemma bsumK_agree : ltac2:(tb__ "0|0|
S1S94S94SaS2dA1SacR4R3R2A3S3S9S4dR5R2A2ScA3S3S0S30R3R4A2S30R3R5A2A3F_;F_;Fb;Frho';Frho;Fn;").
Proof. intros. eapply (proj2 (bsum_agree _ _ _ _ H H0)). Qed.
Lemma bsumV_app : ltac2:(tb__ "0|1|
SaS2dA1M0G0S94S3S0S31S10S2dR3R2A3R1A2S1eS31R3R1A2S31R2R1A2A2A3Fr;Fb2;Fb1;").
Proof. intros b1 b2 r. induction b1 as [|i t IH]; cbn [bsumV app]; [lia|]. rewrite IH. lia. Qed.
Lemma bsumK_app : ltac2:(tb__ "0|1|
SaS2dA1M0G0S94S3S0S30S10S2dR3R2A3R1A2S1eS30R3R1A2S30R2R1A2A2A3Fr;Fb2;Fb1;").
Proof. intros b1 b2 r. induction b1 as [|i t IH]; cbn [bsumK app]; [lia|]. rewrite IH. lia. Qed.

Definition bd_nn (b : list bitem) (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S9eS2dS2dS1dZ0S46Vrho;R1A2A2Lit;Vb;A3").
Lemma bsum_nonneg : ltac2:(tb__ "0|1|
SaS2dA1S94S3S9S34R2A1ScA3S33R3R2A2S4S1dZ0M0S31R4R3A2A2S1dG0S30R4R3A2A2A2F_;F_;Frho;Fb;").
Proof.
  intros b rho Hw Hn. induction b as [|it r IH]; cbn; [lia|]. unfold bd_wpos in Hw. cbn in Hw. apply andb_prop in Hw as [H1 H2]. apply andb_prop in H1 as [Hv Hk].
  apply Z.leb_le in Hv. apply Z.leb_le in Hk. inversion Hn; subst. destruct (IH H2 ltac:(assumption)) as [A B]. nia.
Qed.

Definition BE_MAX : Z := 2 ^ 40.
Definition BC_MAX : Z := 2 ^ 17.
Definition BN_MAX : nat := 64.

Definition lit_le (e : sv) (m : Z) : bool := ltac2:(tb__ "0|3|
S95S9Le;Ve;S0SdS1fZ0R1A2S1fR1Vm;A2A2Lz;S1S12Li;SafS95S95S12Lb;La;M0Lop;M1G1Sb0G0Lop;M2G2S9S2S95S12La;Lw;Lsgn;S1S95S0S12Lk;Li;Ll;X95x8").
Definition e_bounded (facts : list sprop) (e : sv) : bool := ltac2:(tb__ "0|0|
S18S6cVe;S3fA2Sb6Vfacts;S9aVe;S99S3fA1A2A2A2").
Lemma lit_le_sound : ltac2:(tb__ "0|0|
S94S95S0S4S1dZ0R1A2S26R1S24Z2Z40A2A2A2S3S9S6cR3R2A2ScA3S1dS39R5R4A2R3A2F_;F_;Fm;Fe;Frho;").
Proof.
  intros rho e m Hm H. destruct e; cbn in H; try discriminate. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  unfold uval. rewrite U_lit. unfold M64v. rewrite Z.mod_small by lia. exact H2.
Qed.
Lemma e_bounded_sound : ltac2:(tb__ "0|0|
S94SaS96A1S95S9eS96S97R3A1R2A3S3S9S67R3R2A2ScA3S1dS39R5R3A2S3fA2F_;F_;Fe;Ffacts;Frho;").
Proof.
  intros rho facts e HF H. apply orb_prop in H as [H|H].
  - apply lit_le_sound; [unfold BE_MAX; lia | exact H].
  - pose proof (prove_sprop_sound rho facts _ HF H) as X. cbn [holds] in X. rewrite U_lit in X. unfold uval, BE_MAX in *. unfold M64v in X.
    rewrite Z.mod_small in X by lia. exact X.
Qed.

Definition plist := list (Z * sv).
Fixpoint plsum (rho : valuation) (l : plist) : Z := match l with [] => 0 | (c, e) :: r => c * uval rho e + plsum rho r end.
Fixpoint plexp (l : plist) : sv := match l with [] => SLit 0 | (c, e) :: r => SAlu ALU_ADD (SMd M_MUL (SLit c) e) (plexp r) end.
Definition pl_ok (facts : list sprop) (l : plist) : bool := ltac2:(tb__ "0|2|
SdSa0SbS0S95A2M0G0SdSdS1fZ0SeS0S95R1A3M1A2S1fG1S45A2A2S67Vfacts;SfS0S95R1A3A2A2Lce;Vl;A3Sc1S1aG0Vl;A2S76A2A2").

Lemma plsum_bound : ltac2:(tb__ "0|4|
SaS96A1SaSbS0S95A2M0A1S94S9eS96S97R1A1R3A3S3S9Sa0G0G0SdSdS1fZ0M1SeS0S95R1A3M2A2S1fG2S45A2A2S67R5SfS0S95R1A3A2A2Lce;R3A3ScA3S4S1dG1S4bR3R4A2M3A2S1dG3S20S27S1aG0R4A2A1S20S45S3fA2A2A2A2F_;F_;Frho;Fl;Ffacts;").
Proof.
  intros facts l rho HF H. induction l as [|[c e] r IH]; [cbn; lia|].
  cbn in H. apply andb_prop in H as [Hi Hr]. apply andb_prop in Hi as [Hi He]. apply andb_prop in Hi as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. specialize (IH Hr).
  pose proof (e_bounded_sound rho facts e HF He). pose proof (uval_range rho e). cbn [plsum length fst snd]. rewrite Nat2Z.inj_succ. nia.
Qed.
Lemma plexp_val : ltac2:(tb__ "0|0|
SaS96A1S32S94S9eS96S97R1A1R3A3S3S9S60R4R3A2ScA3S3S0S39R3S50R4A1A2S4bR3R4A2A3F_;F_;Frho;Fl;Ffacts;").
Proof.
  intros facts l rho HF H. unfold pl_ok in H. apply andb_prop in H as [H Hn]. apply Nat.leb_le in Hn.
  pose proof (plsum_bound facts l rho HF H) as G. revert H Hn G.
  induction l as [|[c e] r IH]; intros H Hn G.
  - cbn. unfold uval. rewrite U_lit. reflexivity.
  - cbn in H. apply andb_prop in H as [Hi Hr]. apply andb_prop in Hi as [Hi He]. apply andb_prop in Hi as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [length] in Hn, G. rewrite Nat2Z.inj_succ in G.
    pose proof (plsum_bound facts r rho HF Hr) as Gr. specialize (IH Hr ltac:(lia) Gr).
    pose proof (e_bounded_sound rho facts e HF He). pose proof (uval_range rho e).
    cbn [plexp plsum fst snd]. unfold uval in *. rewrite U_add, U_mul, U_lit, IH. unfold M64v, BC_MAX, BE_MAX, BN_MAX in *.
    rewrite (Z.mod_small c) by lia. rewrite (Z.mod_small (c * _)) by nia. apply Z.mod_small. nia.
Qed.

Definition pl_le (facts : list sprop) (cL : Z) (L R : plist) (cR : Z) : bool := ltac2:(tb__ "0|2|
SdSdSdSdSdSdS60Vfacts;VL;A2S60Vfacts;VR;A2A2S1fZ0M0VcL;A2A2S1fVcL;S20S45S3fA2M1A2A2S1fG0VcR;A2A2S1fVcR;G1A2A2Sb6Vfacts;S9aS9bSaeS99VcL;A1S50VL;A1A3S9bSaeS50VR;A1S99VcR;A1A3A2A2A2").
Lemma pl_le_sound : ltac2:(tb__ "0|0|
SaS96A1S0S32S32S0S94S9eS96S97R1A1R6A3S3S9S6fR7R6R5R4R3A5ScA3S1dS1eR7S4bR3R6A2A2S1eS4bR3R5A2R4A2A2F_;F_;Frho;FcR;FR;FL;FcL;Ffacts;").
Proof.
  intros facts cL L R cR rho HF H. unfold pl_le in H.
  apply andb_prop in H as [H HP]. apply andb_prop in H as [H HcR2]. apply andb_prop in H as [H HcR1]. apply andb_prop in H as [H HcL2].
  apply andb_prop in H as [H HcL1]. apply andb_prop in H as [HL HR].
  apply Z.leb_le in HcR2. apply Z.leb_le in HcR1. apply Z.leb_le in HcL2. apply Z.leb_le in HcL1.
  pose proof (prove_sprop_sound rho facts _ HF HP) as X. cbn [holds] in X. rewrite !U_add, !U_lit in X.
  change (bv_unsigned (eval rho (plexp L))) with (uval rho (plexp L)) in X. change (bv_unsigned (eval rho (plexp R))) with (uval rho (plexp R)) in X.
  rewrite (plexp_val facts L rho HF HL), (plexp_val facts R rho HF HR) in X.
  pose proof HL as HL'. pose proof HR as HR'. unfold pl_ok in HL', HR'. apply andb_prop in HL' as [HL1 HL2]. apply andb_prop in HR' as [HR1 HR2].
  apply Nat.leb_le in HL2. apply Nat.leb_le in HR2.
  pose proof (plsum_bound facts L rho HF HL1). pose proof (plsum_bound facts R rho HF HR1).
  unfold M64v, BC_MAX, BE_MAX, BN_MAX in *. rewrite (Z.mod_small cL) in X by lia. rewrite (Z.mod_small cR) in X by lia.
  rewrite !Z.mod_small in X by nia. lia.
Qed.

Record split := SP { sp_pos : plist; sp_neg : plist; sp_plog : plist; sp_nlog : plist; sp_c : Z }.
Fixpoint lf_split (f : lform) (acc : split) : split :=
  match f with
  | [] => acc
  | (c, ASv e) :: r =>
      lf_split r (if 0 <=? c then SP ((c, e) :: sp_pos acc) (sp_neg acc) (sp_plog acc) (sp_nlog acc) (sp_c acc)
                  else SP (sp_pos acc) ((- c, e) :: sp_neg acc) (sp_plog acc) (sp_nlog acc) (sp_c acc))
  | (c, ALog e) :: r =>
      lf_split r (if 0 <=? c then SP (sp_pos acc) (sp_neg acc) ((c, e) :: sp_plog acc) (sp_nlog acc) (sp_c acc)
                  else SP (sp_pos acc) (sp_neg acc) (sp_plog acc) ((- c, e) :: sp_nlog acc) (sp_c acc))
  | (c, AMin e c1 k B) :: r =>

      lf_split r (if 0 <=? c then acc
                  else SP (sp_pos acc) (sp_neg acc) (sp_plog acc) (sp_nlog acc) (sp_c acc + c * Z.max 0 B))
  end.
Definition plogsum (rho : valuation) (l : plist) : Z := ltac2:(tb__ "0|1|
Sa2S0SbS0S95A2M0G0S0S1eS20SeS0S95R2A3S3cS39Vrho;SfS0S95R2A3A2A1A2R1A2Lacc;Lce;Z0Vl;A5").
Definition split_val (rho : valuation) (sp : split) : Z := ltac2:(tb__ "0|0|
S1eS21S1eS21S4bVrho;S74Vsp;A1A2S4bVrho;S73Vsp;A1A2A2S41Vrho;S52Vsp;A1A2A2S41Vrho;S51Vsp;A1A2A2S72Vsp;A1A2").
Lemma lf_split_val : ltac2:(tb__ "0|0|
S2fS61S94S1dS84R1S5eR3R2A2A2S1eS35R1R3A2S84R1R2A2A2A2Frho;Facc;Ff;").
Proof.
  intros f. induction f as [|[c [e|e|e c1 k B]] r IH]; intros acc rho; cbn [lf_split lfval]; [lia| | |];
    destruct (Z.leb_spec 0 c); (eapply Z.le_trans; [apply IH|]); unfold split_val; cbn [sp_pos sp_neg sp_plog sp_nlog sp_c plsum plogsum fold_right aval fst snd]; unfold plogsum; try lia.
  pose proof (Z.le_max_l 0 (Z.min (c1 * uval rho e + k) B)) as M0.
  assert (M1 : Z.max 0 (Z.min (c1 * uval rho e + k) B) <= Z.max 0 B) by (apply Z.max_le_compat_l; apply Z.le_min_r).
  assert (c * Z.max 0 B <= c * Z.max 0 (Z.min (c1 * uval rho e + k) B)) by nia. lia.
Qed.

Fixpoint remove_first (p : Z * sv -> bool) (l : plist) : option plist :=
  match l with
  | [] => None
  | x :: r => if p x then Some r else match remove_first p r with Some r' => Some (x :: r') | None => None end
  end.
Lemma remove_first_spec : ltac2:(tb__ "0|2|
SbS0S95A2M0S9F_;S32S32S3S14S32A1S71R3R2A2S16S32R1A2A3S5G0G0S5SaG0A1M1G1S5G1G1S4S3S32R6S10G0R2S17G0R3R1A3A3A3S4S3S32R5S10G0R2R1A3A3S3S9R7R3A1ScA3A2A2Ll2;A2Ll1;A2Lx;A2F_;Fr;Fl;Fp;").
Proof.
  intros p l. induction l as [|y t IH]; intros r H; cbn in H; [discriminate|].
  destruct (p y) eqn:E.
  - injection H as <-. exists y, [], t. auto.
  - destruct (remove_first p t) as [r'|] eqn:E2; [|discriminate]. injection H as <-.
    destruct (IH r' eq_refl) as (x & l1 & l2 & -> & -> & Hp). exists x, (y :: l1), l2. auto.
Qed.
Lemma plogsum_app : ltac2:(tb__ "0|2|
S94SaSbS0S95A2M0A1M1G1S3S0S41R3S10G0R2R1A3A2S1eS41R3R2A2S41R3R1A2A2A3Fl2;Fl1;Frho;").
Proof. intros rho l1 l2. unfold plogsum. induction l1 as [|x t IH]; cbn; [lia|]. rewrite IH. lia. Qed.

Fixpoint pair_logs (facts : list sprop) (nl pl : plist) : plist * plist   :=
  match nl with
  | [] => ([], pl)
  | (c, e) :: r =>
      match remove_first (fun ce' => (c <=? fst ce') && prove_sprop facts (SPUle e (snd ce'))) pl with
      | Some pl' => pair_logs facts r pl'
      | None => let '(u, p) := pair_logs facts r pl in ((c, e) :: u, p)
      end
  end.
Lemma pair_logs_sound : ltac2:(tb__ "0|5|
SaS96A1SaSbS0S95A2M0A1M1G1S94S32S32S9eS96S97R3A1R6A3S3S9Sa0G0G0S1fZ0M2SeS0S95R1A3A2Lce;M3R5A3ScA3S3S9Sa0G0G3R7A3ScA3S3SbS32S32A2S6dR9R8R7A3S11S32S32R5R4A4A3S4S1dS41R7R9A2S1eS21S41R7R8A2S41R7R5A2M4A2S41R7R6A2A2A2S4S1dG2G4A2S3S9Sa0G0G3R6A3ScA3A2A2F_;F_;F_;F_;Fp;Fu;Frho;Fpl;Fnl;Ffacts;").
Proof.
  intros facts nl. induction nl as [|[c e] r IH]; intros pl rho u p HF Hpl Hnl H; cbn [pair_logs] in H.
  - injection H as <- <-. cbn. split; [unfold plogsum; cbn; lia|]. split; [|reflexivity].
    clear -Hpl. induction pl as [|[c e] t IH]; [unfold plogsum; cbn; lia|]. cbn in Hpl. apply andb_prop in Hpl as [H1 H2]. apply Z.leb_le in H1.
    specialize (IH H2). unfold plogsum in IH |- *. cbn. pose proof (zlog15_range (uval rho e)). nia.
  - cbn in Hnl. apply andb_prop in Hnl as [Hc Hr]. apply Z.leb_le in Hc.
    destruct (remove_first _ pl) as [pl'|] eqn:E.
    + apply remove_first_spec in E as ([c' e'] & l1 & l2 & -> & -> & Hp). cbn [fst snd] in Hp. apply andb_prop in Hp as [Hcc Hpe].
      apply Z.leb_le in Hcc. pose proof (prove_sprop_sound rho facts _ HF Hpe) as X. cbn [holds] in X.
      assert (Hpl' : forallb (fun ce => 0 <=? fst ce) (l1 ++ l2) = true).
      { rewrite forallb_app in Hpl |- *. cbn in Hpl. apply andb_prop in Hpl as [A B]. apply andb_prop in B as [_ B]. rewrite A, B. reflexivity. }
      destruct (IH (l1 ++ l2) rho u p HF Hpl' Hr H) as (IH1 & IH2 & IH3).
      rewrite !plogsum_app in *. unfold plogsum in IH1 |- *. cbn [fold_right fst snd] in IH1 |- *. fold (plogsum rho l1) (plogsum rho l2) (plogsum rho r) (plogsum rho p) (plogsum rho u) in IH1 |- *.
      pose proof (zlog15_mono (uval rho e) (uval rho e') X) as M. pose proof (zlog15_range (uval rho e)). pose proof (zlog15_range (uval rho e')).
      assert (PP : c * zlog15 (uval rho e) <= c' * zlog15 (uval rho e')) by nia.
      unfold plogsum in *. split; [lia|]. auto.
    + destruct (pair_logs facts r pl) as [u0 p0] eqn:E2. injection H as <- <-.
      destruct (IH pl rho u0 p0 HF Hpl Hr E2) as (IH1 & IH2 & IH3).
      unfold plogsum in IH1 |- *. cbn [fold_right fst snd]. split; [lia|]. split; [exact IH2|]. cbn. rewrite IH3. rewrite (proj2 (Z.leb_le _ _) Hc). reflexivity.
Qed.

Definition lf_nonneg0 (facts : list sprop) (f : lform) (c0 : Z) : bool := ltac2:(tb__ "0|4|
S5eVf;S78S13SbS0S95A2M0A1M1G1G1G1Vc0;A5A2S61SbS32S32A2S9Lx;S6dVfacts;S51R1A1S52R1A1A3S32S32Sa2S0G0G0S0S1eS20SeS0S95R2A3Z80A2R1A2Lacc;Lce;Z0M2R2A5S0S6fVfacts;S1eR1S23G2S28S72R4A1M3A1A2A2S73R4A1S74R4A1S23G2G3A2A5Tcu;Lp;Lu;Xbx1Tsp;").

Lemma lf_split_pos : ltac2:(tb__ "0|3|
S2fS61S3S9Sa0SbS0S95A2M0G0S1fZ0SeS0S95R1A3A2Lce;M1S52R1A1A3ScA3S3S9Sa0G0G1S51R2A1A3ScA3S4S3S9Sa0G0G1S52S5eR4R3A2M2A1A3ScA3S3S9Sa0G0G1S51G2A1A3ScA3A2F_;F_;Facc;Ff;").
Proof.
  intros f. induction f as [|[c [e|e|e c1 k B]] r IH]; intros acc H1 H2; cbn [lf_split]. 1: auto.
  all: destruct (Z.leb_spec 0 c); apply IH; cbn; rewrite ?H1, ?H2; try reflexivity;
    apply andb_true_intro; split; try reflexivity; apply Z.leb_le; lia.
Qed.

Lemma lf_nonneg0_sound : ltac2:(tb__ "0|0|
SaS96A1S2fS0S94S9eS96S97R1A1R4A3S3S9S6aR5R4R3A3ScA3S1dZ0S1eS35R3R5A2R4A2A2F_;F_;Frho;Fc0;Ff;Ffacts;").
Proof.
  intros facts f c0 rho HF H. unfold lf_nonneg0 in H.
  pose proof (lf_split_val f (SP [] [] [] [] c0) rho) as V.
  assert (V0 : split_val rho (SP [] [] [] [] c0) = c0) by (unfold split_val, plogsum; cbn; lia). rewrite V0 in V. clear V0.
  set (sp := lf_split f (SP [] [] [] [] c0)) in *.
  destruct (lf_split_pos f (SP [] [] [] [] c0) eq_refl eq_refl) as [P1 P2]. fold sp in P1, P2.
  destruct (pair_logs facts (sp_nlog sp) (sp_plog sp)) as [u p] eqn:E.
  destruct (pair_logs_sound facts _ _ rho u p HF P1 P2 E) as (Q1 & Q2 & Q3).
  pose proof (pl_le_sound facts _ _ _ _ rho HF H) as L.
  assert (U : plogsum rho u <= fold_right (fun ce acc => fst ce * 128 + acc) 0 u).
  { clear -Q3. induction u as [|[c e] t IH]; [unfold plogsum; cbn; lia|]. cbn in Q3. apply andb_prop in Q3 as [A B]. apply Z.leb_le in A.
    specialize (IH B). unfold plogsum in IH |- *. cbn. pose proof (zlog15_range (uval rho e)). nia. }
  unfold split_val in V. lia.
Qed.

Definition batom_eqb (a b : batom) : bool := ltac2:(tb__ "0|4|
S2eS9La;Va;S95S2eS9Lb;M0Vb;S95S9cR2R1A2Ly;M1S95S12Le;M2S95S0S0S0S12LB;Lk;Lc1;Le;M3X2ex3Lx;S95G0Vb;G2G1G3X2ex3Lx;S95S0S0S0G0Vb;G2G2S95S0S0S0SdSdSdS9cR8R4A2S25R7R3A2A2S25R6R2A2A2S25R5R1A2A2LB';Lk';Lc1';Ly;X2ex3LB;Lk;Lc1;Lx;X2ex3").
Lemma batom_eqb_sound : ltac2:(tb__ "0|0|
S2eS2eS3S9S8bR2R1A2ScA3S3S2eR3R2A3F_;Fb;Fa;").
Proof.
  intros [x|x|x c1 k B] [y|y|y c1' k' B'] H; cbn -[sv_eqb] in H; try discriminate; try (apply sv_eqb_sound in H; subst; reflexivity).
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
  apply sv_eqb_sound in H0. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
Qed.
Fixpoint lf_addc (c : Z) (a : batom) (f : lform) : lform :=
  match f with
  | [] => [(c, a)]
  | (c', a') :: r => if batom_eqb a a' then (c' + c, a') :: r else (c', a') :: lf_addc c a r
  end.
Lemma lfval_addc : ltac2:(tb__ "0|0|
S94S0S2eS2fS3S0S35R4S8fR3R2R1A3A2S1eS20R3S4cR4R2A2A2S35R4R1A2A2A3Ff;Fa;Fc;Frho;").
Proof.
  intros rho c a f. induction f as [|[c' a'] r IH]; cbn; [lia|].
  destruct (batom_eqb a a') eqn:E; cbn; [apply batom_eqb_sound in E; subst; lia | rewrite IH; lia].
Qed.
Definition lit_atom (a : batom) : option Z := ltac2:(tb__ "0|a|
S2eS14S0A1M0La;Va;S95S95G0Le;M1R1S0S16S0S2cR1Sc3A2M2A2Lz;S1S1cS0A1M3Li;M4SafS95S95G3Lb;La0;M5Lop;M6G6Sb0G5Lop;M7G7S9S2S95G3La0;Lw;Lsgn;M8S1S95S0G3Lk;Li;Ll;M9X95x8Le;S95G1R1S0S16S0S3cG2A1A2Lz;G4G6G6G7G7G8G9X95x8Le;S95S0S0S0G1R4S0S16S0S23Z0S2aS1eS20R4G2A2R3A2R2A2A2A2Lz;G4G6G6G7G7G8S1S95S0G3Lk0;Li;Ll;X95x8LB;Lk;Lc1;Le;X2ex3").
Lemma lit_atom_sound : ltac2:(tb__ "0|0|
S94S2eS0S3S14S0A1S93R2A1S16S0R1A2A3S3S0S4cR4R3A2R2A3F_;Fz;Fa;Frho;").
Proof.
  intros rho [e|e|e c1 k B] z H; destruct e; cbn -[Z.mul Z.add Z.max Z.min Z.modulo M64v zlog15] in H; try discriminate; injection H as <-; cbn [aval]; unfold uval; rewrite U_lit; reflexivity.
Qed.
Fixpoint lf_norm (f : lform) (acc : lform) (c0 : Z) : lform * Z :=
  match f with
  | [] => (List.filter (fun ca => negb (fst ca =? 0)) acc, c0)
  | (c, a) :: r => match lit_atom a with
                   | Some z => lf_norm r acc (c0 + c * z)
                   | None => lf_norm r (lf_addc c a acc) c0
                   end
  end.
Lemma lfval_filter0 : ltac2:(tb__ "0|1|
S94SaSbS0S2eA2M0A1S3S0S35R2Sa4G0G0S1bS25SeS0S2eR1A3Z0A2A1Lca;R1A3A2S35R2R1A2A3Ff;Frho;").
Proof. intros rho f. induction f as [|[c a] r IH]; [reflexivity|]. simpl. destruct (Z.eqb_spec c 0); simpl; rewrite IH; lia. Qed.
Lemma lf_norm_val : ltac2:(tb__ "0|0|
S2fS2fS0S94S2fS0S3SbS2fS0A2S6bR6R5R4A3S11S2fS0R2R1A4A3S3S0S1eS35R4R3A2R2A2S1eS1eS35R4R7A2S35R4R6A2A2R5A2A3F_;Fc;Fg;Frho;Fc0;Facc;Ff;").
Proof.
  intros f. induction f as [|[c1 a] r IH]; intros acc c0 rho g c H; cbn [lf_norm] in H.
  - injection H as <- <-. rewrite lfval_filter0. cbn. lia.
  - destruct (lit_atom a) as [z|] eqn:E.
    + rewrite (IH _ _ rho _ _ H). cbn. rewrite (lit_atom_sound rho a z E). lia.
    + rewrite (IH _ _ rho _ _ H). rewrite lfval_addc. cbn. lia.
Qed.

Definition amin_ok (a : batom) : bool := ltac2:(tb__ "0|2|
S2eS9La;Va;S95ScLe;M0G0S95S0S0S0SdSdSdS1fZ1R3A2S1fZ0M1R2A2A2S1fG1R1A2A2S1fR1S20S45S3fA2A2A2LB;Lk;Lc1;Le;X2ex3").

Definition amin_fact_lin (e : sv) (c1 k B : Z) : sprop := ltac2:(tb__ "0|0|
S9aVe;S99S22S21VB;Vk;A2Vc1;A2A1A2").
Definition amin_fact_sat (e : sv) (c1 k B : Z) : sprop := ltac2:(tb__ "0|0|
S9aS99S23Z0S22S21S1eS21VB;Vk;A2Vc1;A2Z1A2Vc1;A2A2A1Ve;A2").
Fixpoint lf_expand (f : lform) (accf : lform) (c0 : Z) (fs : list sprop) : list (lform * Z * list sprop) :=
  match f with
  | [] => [(accf, c0, fs)]
  | (c, a) :: r =>
      match a with
      | AMin e c1 k B =>
          if amin_ok a then
            lf_expand r ((c * c1, ASv e) :: accf) (c0 + c * k) (amin_fact_lin e c1 k B :: fs)
            ++ lf_expand r accf (c0 + c * B) (amin_fact_sat e c1 k B :: fs)
          else lf_expand r ((c, a) :: accf) c0 fs
      | _ => lf_expand r ((c, a) :: accf) c0 fs
      end
  end.
Lemma amin_facts_val : ltac2:(tb__ "0|2|
S94S95S0S0S0S3S9S89S75R4R3R2R1A4A1ScA3S4S1dZ1R4A2S4S1dZ0M0R3A2S4S1dG0R2A2S4S1dS1eS20R4S39R6R5A2A2R3A2M1R2A2S97R7S87R6R5R4R3A4A2F_;S1dR2G1A2S97R7S88R6R5R4R3A4A2F_;A2A2A2A2F_;FB;Fk;Fc1;Fe;Frho;").
Proof.
  intros rho e c1 k B H. cbn [amin_ok] in H.
  apply andb_prop in H as [H HB2]. apply andb_prop in H as [H HB1]. apply andb_prop in H as [Hc1 Hk1].
  apply Z.leb_le in Hc1. apply Z.leb_le in Hk1. apply Z.leb_le in HB1. apply Z.leb_le in HB2.
  pose proof (uval_range rho e) as Re. unfold BC_MAX, BE_MAX in HB2.
  split; [exact Hc1|]. split; [exact Hk1|]. split; [exact HB1|]. split; intros HR; cbn [holds amin_fact_lin amin_fact_sat]; unfold uval in *; rewrite U_lit; unfold M64v.
  - assert (Q : 0 <= (B - k) / c1 <= B) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; nia]).
    rewrite Z.mod_small by lia. apply Z.div_le_lower_bound; [lia | nia].
  - assert (Q : 0 <= Z.max 0 ((B - k + c1 - 1) / c1) <= B + 1).
    { split; [apply Z.le_max_l|]. apply Z.max_lub; [lia|]. apply Z.div_le_upper_bound; [lia | nia]. }
    rewrite Z.mod_small by lia. apply Z.max_lub; [lia|].
    enough ((B - k + c1 - 1) / c1 < bv_unsigned (eval rho e) + 1) by lia.
    apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
Lemma lf_expand_sound : ltac2:(tb__ "0|3|
S94S2fS2fS0SaS96A1M0S2fS0G0Sa1SbSbS2fS0A2M1G0A2S11G1G0S11S2fS0R3R2A4R1A4S69R7R6R5R4A4A3S9eS96S97R9A1R2A3S1dZ0M2S1eS35RaR5A2R4A2A2F_;F_;Fgs;Fc;Fg;S9eS96S97R6A1R2A3S1dG2S1eS1eS35R7R6A2S35R7R5A2A2R4A2A2F_;F_;Ffs;Fc0;Faccf;Ff;Frho;").
Proof.
  intros rho f. induction f as [|[c a] r IH]; intros accf c0 fs H Hfs.
  - cbn [lfval]. pose proof (H accf c0 fs ltac:(left; reflexivity) Hfs). lia.
  - cbn [lf_expand] in H. cbn [lfval].
    assert (DFL : (forall g c' gs, In (g, c', gs) (lf_expand r ((c, a) :: accf) c0 fs) -> Forall (holds rho) gs -> 0 <= lfval rho g + c') ->
                  0 <= c * aval rho a + lfval rho r + (lfval rho accf + c0)).
    { intros H'. pose proof (IH ((c, a) :: accf) c0 fs H' Hfs) as X. cbn [lfval] in X. lia. }
    destruct a as [e|e|e c1 k B].
    1-2: pose proof (DFL H); lia.
    destruct (amin_ok (AMin e c1 k B)) eqn:Hok; [|pose proof (DFL H); lia].
    destruct (amin_facts_val rho e c1 k B Hok) as (G1 & G2 & G3 & F1 & F2).
    cbn [aval]. pose proof (uval_range rho e) as Re. destruct (Z_le_dec (c1 * uval rho e + k) B) as [Hle|Hgt].
    +
      pose proof (IH ((c * c1, ASv e) :: accf) (c0 + c * k) (amin_fact_lin e c1 k B :: fs)
                    ltac:(intros g c' gs Hin Hgs; apply (H g c' gs); [apply in_or_app; left; exact Hin | exact Hgs])
                    ltac:(constructor; [exact (F1 Hle) | exact Hfs])) as X.
      cbn [lfval aval] in X. rewrite Z.max_r by nia. rewrite Z.min_l by lia. nia.
    + pose proof (IH accf (c0 + c * B) (amin_fact_sat e c1 k B :: fs)
                    ltac:(intros g c' gs Hin Hgs; apply (H g c' gs); [apply in_or_app; right; exact Hin | exact Hgs])
                    ltac:(constructor; [exact (F2 ltac:(lia)) | exact Hfs])) as X.
      rewrite Z.max_r by lia. rewrite Z.min_r by lia. lia.
Qed.
Definition lf_nonneg (facts : list sprop) (f : lform) (c0 : Z) : bool := ltac2:(tb__ "0|5|
SbS2fS0A2M0S9Lx;S6bVf;S13SbS0S2eA2A1M1Vc0;A3S2fS0Sa0SbG0SaS96A1M2A2M3G3S6aS10S96SfG0G2R1A3Vfacts;A3SeS2fS0SeG0G2R1A3M4A3SfS2fS0G4A3A3Lx;S69R2G1R1S13S96A1A4A3Lc;Lg;Xbx1").
Lemma lf_nonneg_sound : ltac2:(tb__ "0|0|
SaS96A1S2fS0S94S9eS96S97R1A1R4A3S3S9S4aR5R4R3A3ScA3S1dZ0S1eS35R3R5A2R4A2A2F_;F_;Frho;Fc0;Ff;Ffacts;").
Proof.
  intros facts f c0 rho HF H. unfold lf_nonneg in H. destruct (lf_norm f [] c0) as [g c] eqn:E.
  pose proof (lf_norm_val f [] c0 rho g c E) as V. cbn [lfval] in V.
  pose proof (lf_expand_sound rho g [] c []) as X. cbn [lfval] in X.
  assert (0 <= lfval rho g + 0 + c); [|lia]. apply X; [|constructor].
  intros g' c' gs Hin Hgs. pose proof (proj1 (forallb_forall _ _) H _ Hin) as Y. cbn [fst snd] in Y.
  apply (lf_nonneg0_sound (gs ++ facts) g' c' rho); [apply Forall_app; split; assumption | exact Y].
Qed.

Definition lf_neg (f : lform) : lform := ltac2:(tb__ "0|1|
S9fSbS0S2eA2M0G0G0S11S0S2eS28SeS0S2eR1A3A1SfS0S2eR1A3A4Lca;Vf;A4").
Lemma lfval_neg : ltac2:(tb__ "0|0|
S94S2fS3S0S35R2S4eR1A1A2S28S35R2R1A2A1A3Ff;Frho;").
Proof. intros rho f. unfold lf_neg. induction f as [|[c a] r IH]; cbn; [lia|]. rewrite IH. lia. Qed.
Lemma lfval_app : ltac2:(tb__ "0|2|
S94SaSbS0S2eA2M0A1M1G1S3S0S35R3S10G0R2R1A3A2S1eS35R3R2A2S35R3R1A2A2A3Fg;Ff;Frho;").
Proof. intros rho f g. induction f as [|[c a] r IH]; cbn; [lia|]. rewrite IH. lia. Qed.
Definition lf_scale (k : Z) (f : lform) : lform := ltac2:(tb__ "0|1|
S9fSbS0S2eA2M0G0G0S11S0S2eS20Vk;SeS0S2eR1A3A2SfS0S2eR1A3A4Lca;Vf;A4").
Lemma lfval_scale : ltac2:(tb__ "0|0|
S94S0S2fS3S0S35R3S90R2R1A2A2S20R2S35R3R1A2A2A3Ff;Fk;Frho;").
Proof. intros rho k f. unfold lf_scale. induction f as [|[c a] r IH]; cbn; [lia|]. rewrite IH. lia. Qed.

Definition item_nonneg (facts : list sprop) (it : bitem) : bool := ltac2:(tb__ "0|0|
S4aVfacts;S3aVit;A1S43Vit;A1A3").
Definition item_le (facts : list sprop) (ito ifrom : bitem) : bool := ltac2:(tb__ "0|0|
S4aVfacts;S10SbS0S2eA2S3aVifrom;A1S4eS3aVito;A1A1A3S21S43Vifrom;A1S43Vito;A1A2A3").

Lemma item_nonneg_sound : ltac2:(tb__ "0|0|
SaS96A1S2dS94S9eS96S97R1A1R3A3S3S9S5dR4R3A2ScA3S1dZ0S46R3R4A2A2F_;F_;Frho;Fit;Ffacts;").
Proof. intros facts it rho HF H. unfold bival. eapply lf_nonneg_sound; eauto. Qed.
Lemma item_le_sound : ltac2:(tb__ "0|0|
SaS96A1S2dS2dS94S9eS96S97R1A1R4A3S3S9S5bR5R4R3A3ScA3S1dS46R3R5A2S46R3R4A2A2F_;F_;Frho;Fifrom;Fito;Ffacts;").
Proof.
  intros facts ito ifrom rho HF H. pose proof (lf_nonneg_sound facts _ _ rho HF H) as X. rewrite lfval_app, lfval_neg in X. unfold bival. lia.
Qed.

Definition item_nn (facts : list sprop) (bfrom : list bitem) (i : bitem) : bool := ltac2:(tb__ "0|0|
S18S5dVfacts;Vi;A2Sa3S2dS2dS5bVfacts;R1Vi;A3Lj;Vbfrom;A3A2").
Lemma item_nn_sound : ltac2:(tb__ "0|0|
SaS96A1SaS2dA1S2dS94S9eS96S97R1A1R4A3S33R4R2A2S3S9S5cR6R5R4A3ScA3S1dZ0S46R4R5A2A2F_;F_;F_;Frho;Fi;Fbfrom;Ffacts;").
Proof.
  intros facts bfrom i rho HF Hn H. unfold item_nn in H. apply orb_prop in H as [H|H]; [eapply item_nonneg_sound; eauto|].
  apply existsb_exists in H as (j & Hj & Hle). pose proof (item_le_sound facts j i rho HF Hle).
  assert (X : 0 <= bival rho j) by exact (proj1 (Forall_forall _ _) Hn j Hj). lia.
Qed.

Fixpoint bud_le_pos (facts : list sprop) (ball bto bfrom : list bitem) : bool :=
  match bto, bfrom with
  | [], _ => bd_wpos bfrom
  | i :: r, j :: r' =>
      (0 <=? bi_v i) && (bi_v i <=? bi_v j) && (0 <=? bi_k i) && (bi_k i <=? bi_k j)
      && item_nn facts ball i && item_le facts i j && bud_le_pos facts ball r r'
  | _ :: _, [] => false
  end.

Lemma bud_le_pos_sound : ltac2:(tb__ "0|1|
SaS96A1SaS2dA1M0G0G0S94S9eS96S97R1A1R5A3S33R5R2A2S33R4R3A2S3S9S65R8R7R6R5A4ScA3S4S1dS31R7R5A2S31R6R5A2A2S4S1dS30R7R5A2S30R6R5A2A2S4S33R7R5A2S4S3S9S34R7A1ScA3S3S9S34R6A1ScA3A2A2A2A2F_;F_;F_;F_;Frho;Fbfrom;Fbto;Fball;Ffacts;").
Proof.
  intros facts ball bto. induction bto as [|i r IH]; intros [|j r'] rho HF Hall Hn H; cbn [bud_le_pos] in H; try discriminate.
  - cbn. split; [lia|]. split; [lia|]. split; [constructor|]. split; [reflexivity|]. exact H.
  - pose proof (bsum_nonneg (j :: r') rho H Hn) as [A B]. cbn [bsumV bsumK] in A, B |- *. split; [lia|]. split; [lia|]. split; [constructor|]. split; [reflexivity|]. exact H.
  - apply andb_prop in H as [H Hr]. apply andb_prop in H as [H Hle]. apply andb_prop in H as [H Hnn]. apply andb_prop in H as [H Hk2]. apply andb_prop in H as [H Hk1].
    apply andb_prop in H as [Hv1 Hv2].
    apply Z.leb_le in Hv1. apply Z.leb_le in Hv2. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2.
    pose proof (item_nn_sound facts ball i rho HF Hall Hnn) as N. pose proof (item_le_sound facts i j rho HF Hle) as L.
    inversion Hn as [|j0 r0 Hj Hr' E1]; subst.
    destruct (IH r' rho HF Hall Hr' Hr) as (IH1 & IH2 & IH3 & IH4 & IH5). cbn [bsumV bsumK].
    split; [nia|]. split; [nia|]. split; [constructor; assumption|].
    unfold bd_wpos. cbn. rewrite (proj2 (Z.leb_le _ _) Hv1), (proj2 (Z.leb_le _ _) Hk1).
    assert (Jv : 0 <= bi_v j) by lia. assert (Jk : 0 <= bi_k j) by lia.
    rewrite (proj2 (Z.leb_le _ _) Jv), (proj2 (Z.leb_le _ _) Jk). cbn.
    unfold bd_wpos in IH4, IH5. auto.
Qed.

Fixpoint wformV (b : list bitem) : lform * Z :=
  match b with [] => ([], 0) | it :: r => let '(f, c) := wformV r in (lf_scale (bi_v it) (bi_f it) ++ f, bi_v it * bi_c it + c) end.
Fixpoint wformK (b : list bitem) : lform * Z :=
  match b with [] => ([], 0) | it :: r => let '(f, c) := wformK r in (lf_scale (bi_k it) (bi_f it) ++ f, bi_k it * bi_c it + c) end.
Lemma wformV_val : ltac2:(tb__ "0|1|
SaS2dA1S94S3S0S1eS35R1SeS2fS0S54R2A1M0A3A2SfS2fS0G0A3A2S31R2R1A2A3Frho;Fb;").
Proof.
  intros b rho. induction b as [|it r IH]; cbn; [reflexivity|]. destruct (wformV r) as [f c]. cbn [fst snd] in IH |- *.
  rewrite lfval_app, lfval_scale. unfold bival. lia.
Qed.
Lemma wformK_val : ltac2:(tb__ "0|1|
SaS2dA1S94S3S0S1eS35R1SeS2fS0S53R2A1M0A3A2SfS2fS0G0A3A2S30R2R1A2A3Frho;Fb;").
Proof.
  intros b rho. induction b as [|it r IH]; cbn; [reflexivity|]. destruct (wformK r) as [f c]. cbn [fst snd] in IH |- *.
  rewrite lfval_app, lfval_scale. unfold bival. lia.
Qed.

Definition bud_pay (facts : list sprop) (costV : sv) (costK : Z) (bfrom bto : list bitem) : bool := ltac2:(tb__ "0|4|
SdSdSdSdSdS34Vbfrom;A1S34Vbto;A1A2Sa0S2dS5cVfacts;Vbfrom;A2Vbto;A3A2S1fZ0VcostK;A2A2SbS2fS0A2S9Lx;M0S54Vbfrom;A1S2fS0G0S54Vbto;A1S2fS0S4aVfacts;S10SbS0S2eA2M1R4S10G1S4eR2A1M2S17G1S11S0S2eN1S55VcostV;A1A4S13G1A1A3A3A3S21R3R1A2M3A3Ltc;Ltf;Xbx1Lfc;Lff;Xbx1A2G0S53Vbfrom;A1S2fS0G0S53Vbto;A1S2fS0S4aVfacts;S10G1R4G2A3S21G3VcostK;A2A3Ltc;Ltf;Xbx1Lfc;Lff;Xbx1A2").

Lemma bud_pay_sound : ltac2:(tb__ "0|4|
SaS96A1S95S0SaS2dA1M0G0S94S9eS96S97R1A1R6A3S33R4R2A2S3S9S49R8R7R6R5R4A5ScA3S4S1dS1eS39R4R8A2S31R5R4A2M1A2S31R6R4A2A2S4S1dS1eR7S30R5R4A2M2A2S30R6R4A2A2S4S1dZ0M3G1A2S4S1dG3G2A2S4S1dG3R7A2S4S33R5R4A2S4S3S9S34R5A1ScA3S3S9S34R6A1ScA3A2A2A2A2A2A2A2F_;F_;F_;Frho;Fbto;Fbfrom;FcostK;FcostV;Ffacts;").
Proof.
  intros facts costV costK bfrom bto rho HF Hnf H. unfold bud_pay in H.
  apply andb_prop in H as [H HK]. apply andb_prop in H as [H HV]. apply andb_prop in H as [H Hc]. apply andb_prop in H as [H Hnn]. apply andb_prop in H as [Hw1 Hw2].
  apply Z.leb_le in Hc.
  assert (NN : bd_nn bto rho).
  { unfold bd_nn. apply Forall_forall. intros it Hit. eapply item_nn_sound; [exact HF|exact Hnf|]. exact (proj1 (forallb_forall _ _) Hnn it Hit). }
  pose proof (bsum_nonneg bto rho Hw2 NN) as [N1 N2].
  destruct (wformV bfrom) as [ff fc] eqn:E1. destruct (wformV bto) as [tf tc] eqn:E2.
  destruct (wformK bfrom) as [ffk fck] eqn:E3. destruct (wformK bto) as [tfk tck] eqn:E4.
  pose proof (lf_nonneg_sound facts _ _ rho HF HV) as XV. pose proof (lf_nonneg_sound facts _ _ rho HF HK) as XK.
  rewrite !lfval_app in XV. rewrite !lfval_app in XK. rewrite lfval_neg in XV. rewrite lfval_neg in XK. cbn [lfval aval] in XV.
  pose proof (wformV_val bfrom rho) as W1. rewrite E1 in W1. pose proof (wformV_val bto rho) as W2. rewrite E2 in W2.
  pose proof (wformK_val bfrom rho) as W3. rewrite E3 in W3. pose proof (wformK_val bto rho) as W4. rewrite E4 in W4.
  cbn [fst snd] in W1, W2, W3, W4. repeat (split; [lia|]). split; [exact NN|]. auto.
Qed.

Definition bud_le_ref (facts : list sprop) (bto bfrom : list bitem) : bool := ltac2:(tb__ "0|1|
S18S65Vfacts;Vbfrom;Vbto;Vbfrom;A4S49Vfacts;S99Z0M0A1G0Vbfrom;Vbto;A5A2").

Lemma bud_le_ref_sound : ltac2:(tb__ "0|1|
SaS96A1SaS2dA1M0G0S94S9eS96S97R1A1R4A3S33R3R2A2S3S9S7dR6R5R4A3ScA3S4S1dS31R6R4A2S31R5R4A2A2S4S1dS30R6R4A2S30R5R4A2A2S4S33R6R4A2S4S3S9S34R6A1ScA3S3S9S34R5A1ScA3A2A2A2A2F_;F_;F_;Frho;Fbfrom;Fbto;Ffacts;").
Proof.
  intros facts bto bfrom rho HF Hn H. unfold bud_le_ref in H. apply orb_prop in H as [H|H].
  - eapply bud_le_pos_sound; eauto.
  - destruct (bud_pay_sound facts _ _ _ _ rho HF Hn H) as (P1 & P2 & _ & _ & _ & P6 & P7 & P8).
    pose proof (uval_range rho (SLit 0)). repeat (split; [lia|]). auto.
Qed.

Definition e_bounded_p (pf : pfacts) (e : sv) : bool := ltac2:(tb__ "0|0|
S18S6cVe;S3fA2Sa7Vpf;S9aVe;S99S3fA1A2A2A2").
Definition pl_ok_p (pf : pfacts) (l : plist) : bool := ltac2:(tb__ "0|2|
SdSa0SbS0S95A2M0G0SdSdS1fZ0SeS0S95R1A3M1A2S1fG1S45A2A2S8dVpf;SfS0S95R1A3A2A2Lce;Vl;A3Sc1S1aG0Vl;A2S76A2A2").
Definition pl_le_p (pf : pfacts) (cL : Z) (L R : plist) (cR : Z) : bool := ltac2:(tb__ "0|2|
SdSdSdSdSdSdS70Vpf;VL;A2S70Vpf;VR;A2A2S1fZ0M0VcL;A2A2S1fVcL;S20S45S3fA2M1A2A2S1fG0VcR;A2A2S1fVcR;G1A2A2Sa7Vpf;S9aS9bSaeS99VcL;A1S50VL;A1A3S9bSaeS50VR;A1S99VcR;A1A3A2A2A2").
Fixpoint pair_logs_p (pf : pfacts) (nl pl : plist) : plist * plist :=
  match nl with
  | [] => ([], pl)
  | (c, e) :: r =>
      match remove_first (fun ce' => (c <=? fst ce') && prove_sprop_pf pf (SPUle e (snd ce'))) pl with
      | Some pl' => pair_logs_p pf r pl'
      | None => let '(u, p) := pair_logs_p pf r pl in ((c, e) :: u, p)
      end
  end.
Definition lf_nonneg0_p (pf : pfacts) (f : lform) (c0 : Z) : bool := ltac2:(tb__ "0|4|
S5eVf;S78S13SbS0S95A2M0A1M1G1G1G1Vc0;A5A2S61SbS32S32A2S9Lx;S82Vpf;S51R1A1S52R1A1A3S32S32Sa2S0G0G0S0S1eS20SeS0S95R2A3Z80A2R1A2Lacc;Lce;Z0M2R2A5S0S83Vpf;S1eR1S23G2S28S72R4A1M3A1A2A2S73R4A1S74R4A1S23G2G3A2A5Tcu;Lp;Lu;Xbx1Tsp;").
Definition lf_nonneg_p (pf : pfacts) (facts : list sprop) (f : lform) (c0 : Z) : bool := ltac2:(tb__ "0|5|
SbS2fS0A2M0S9Lx;S6bVf;S13SbS0S2eA2A1M1Vc0;A3S2fS0Sa0SbG0SaS96A1M2A2M3G3S81G2Sa6Lx;SfG0G2R1A3Vpf;S96G2Sb7S10S96SfG0G2R3A3Vfacts;A3A1Ll;Ly;Xax2SeS2fS0SeG0G2R1A3M4A3SfS2fS0G4A3A3Lx;S69R2G1R1S13S96A1A4A3Lc;Lg;Xbx1").
Lemma forallb_ext_lz : forall {T} (f g : T -> bool) l, (forall x, f x = g x) -> forallb f l = forallb g l.
Proof. intros T f g l H. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite H, IH. reflexivity. Qed.
Lemma remove_first_ext_lz : ltac2:(tb__ "0|2|
SbS0S95A2M0S9F_;M1G1S32G0S3S9R4R1A1R3R1A1A3Fx;S3S14S32A1S71R4R2A2S71R3R2A2A3F_;Fl;Fg;Ff;").
Proof. intros f g l H. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite H, IH. reflexivity. Qed.
Lemma pl_ok_p_eq : ltac2:(tb__ "0|0|
SaS96A1S32S3S9S70Sa5R2A1R1A2S60R2R1A2A3Fl;Ffacts;").
Proof. reflexivity. Qed.
Lemma pl_le_p_eq : ltac2:(tb__ "0|0|
SaS96A1S0S32S32S0S3S9S83Sa5R5A1R4R3R2R1A5S6fR5R4R3R2R1A5A3FcR;FR;FL;FcL;Ffacts;").
Proof. reflexivity. Qed.
Lemma pair_logs_p_eq : ltac2:(tb__ "0|0|
SaS96A1S32S32S3SbS32S32A2S82Sa5R3A1R2R1A3S6dR3R2R1A3A3Fpl;Fnl;Ffacts;").
Proof.
  intros facts nl. induction nl as [|[c e] r IH]; intros pl; cbn [pair_logs_p pair_logs]; [reflexivity|].
  rewrite (remove_first_ext_lz _ (fun ce' => (c <=? fst ce') && prove_sprop facts (SPUle e (snd ce')))) by (intros x; rewrite prove_sprop_pf_eq; reflexivity).
  destruct (remove_first _ pl) as [pl'|]; [apply IH | rewrite IH; reflexivity].
Qed.
Lemma lf_nonneg0_p_eq : ltac2:(tb__ "0|0|
SaS96A1S2fS0S3S9S81Sa5R3A1R2R1A3S6aR3R2R1A3A3Fc0;Ff;Ffacts;").
Proof. intros. unfold lf_nonneg0_p, lf_nonneg0. cbv zeta. rewrite pair_logs_p_eq. destruct (pair_logs facts _ _) as [u p0]. apply pl_le_p_eq. Qed.
Lemma lf_nonneg_p_eq : ltac2:(tb__ "0|0|
SaS96A1S2fS0S3S9S4fSa5R3A1R3R2R1A4S4aR3R2R1A3A3Fc0;Ff;Ffacts;").
Proof.
  intros. unfold lf_nonneg_p, lf_nonneg. destruct (lf_norm f [] c0) as [g c]. apply forallb_ext_lz. intros [[g' c'] gs]. cbn [fst snd].
  destruct gs as [|q gs]; [apply lf_nonneg0_p_eq | rewrite DigFastA.mk_pf_f_eq; apply lf_nonneg0_p_eq].
Qed.
Definition item_nonneg_p (pf : pfacts) (facts : list sprop) (it : bitem) : bool := ltac2:(tb__ "0|0|
S4fVpf;Vfacts;S3aVit;A1S43Vit;A1A4").
Definition item_le_p (pf : pfacts) (facts : list sprop) (ito ifrom : bitem) : bool := ltac2:(tb__ "0|0|
S4fVpf;Vfacts;S10SbS0S2eA2S3aVifrom;A1S4eS3aVito;A1A1A3S21S43Vifrom;A1S43Vito;A1A2A4").
Lemma item_nonneg_p_eq : ltac2:(tb__ "0|0|
SaS96A1S2dS3S9S7fSa5R2A1R2R1A3S5dR2R1A2A3Fit;Ffacts;").
Proof. intros. apply lf_nonneg_p_eq. Qed.
Lemma item_le_p_eq : ltac2:(tb__ "0|0|
SaS96A1S2dS2dS3S9S68Sa5R3A1R3R2R1A4S5bR3R2R1A3A3Fj;Fi;Ffacts;").
Proof. intros. apply lf_nonneg_p_eq. Qed.

Definition item_nn_lz (pf : pfacts) (facts : list sprop) (bfrom : list bitem) (hint : option bitem) (i : bitem) : bool := ltac2:(tb__ "0|2|
S9S9L_;M0S14S2dA1S9Lhint;Vhint;S2dS68Vpf;Vfacts;R1Vi;A4Lj;M1S12X14x2ScG0S7fVpf;Vfacts;Vi;A3ScSb5S2dG1Vbfrom;A3X9x2X9x2").
Lemma existsb_item_le_p_eq : ltac2:(tb__ "0|0|
SaS96A1S2dSaS2dA1S3S9Sb5S2dS2dS68Sa5R4A1R4R1R3A4Lj;R1A3Sa3S2dS2dS5bR4R1R3A3Lj;R1A3A3Fl;Fi;Ffacts;").
Proof. intros facts i l. rewrite existsb_lazy_eq. induction l as [|b r IH]; [reflexivity|]. cbn [existsb]. rewrite item_le_p_eq, IH. reflexivity. Qed.
Lemma item_nn_lz_eq : ltac2:(tb__ "0|1|
SaS96A1SaS2dA1S14S2dA1M0S2dG0OLhint;R2S2dSa1S2dR1R4A3Lj;S7X14x2S3S9S8eSa5R5A1R5R4R3R2A5S5cR5R4R2A3A3F_;Fi;Fhint;Fbfrom;Ffacts;").
Proof.
  intros facts bfrom hint i Hh. unfold item_nn_lz, item_nn. rewrite item_nonneg_p_eq, existsb_item_le_p_eq.
  destruct hint as [j|].
  - rewrite item_le_p_eq. destruct (item_le facts j i) eqn:E.
    + cbn. symmetry. apply orb_true_intro. right. apply existsb_exists. exists j. auto.
    + cbn. destruct (item_nonneg facts i); reflexivity.
  - cbn. destruct (item_nonneg facts i); reflexivity.
Qed.
Fixpoint bud_le_pos_lz (pf : pfacts) (facts : list sprop) (ball bto bfrom : list bitem) : bool :=
  match bto, bfrom with
  | [], _ => bd_wpos bfrom
  | i :: r, j :: r' =>
      ((0 <=? bi_v i) && (bi_v i <=? bi_v j) && (0 <=? bi_k i) && (bi_k i <=? bi_k j))
      &&& (item_nn_lz pf facts ball (Some j) i &&& (item_le_p pf facts i j &&& bud_le_pos_lz pf facts ball r r'))
  | _ :: _, [] => false
  end.
Lemma lazy_andb_eq_lz : ltac2:(tb__ "0|0|
S9S9S3S9S9S9L_;R2R1S12X9x2SdR2R1A2A3Fb;Fa;"). Proof. intros [|] b; reflexivity. Qed.
Lemma lazy_orb_eq_lz : ltac2:(tb__ "0|0|
S9S9S3S9S9S9L_;R2ScR1X9x2S18R2R1A2A3Fb;Fa;"). Proof. intros [|] b; reflexivity. Qed.
Lemma bud_le_pos_lz_eq : ltac2:(tb__ "0|1|
SaS96A1SaS2dA1M0G0G0S2dSa1S2dR1R2A3Sa1S2dR2R5A3F_;Fj;S3S9S7cSa5R5A1R5R4R3R2A5S65R5R4R3R2A4A3F_;Fbfrom;Fbto;Fball;Ffacts;").
Proof.
  intros facts ball bto. induction bto as [|i r IH]; intros [|j r'] Hsub; cbn [bud_le_pos_lz bud_le_pos]; try reflexivity.
  rewrite !lazy_andb_eq_lz. rewrite (item_nn_lz_eq facts ball (Some j) i) by (apply Hsub; left; reflexivity).
  rewrite item_le_p_eq. rewrite (IH r') by (intros x Hx; apply Hsub; right; exact Hx).
  destruct ((0 <=? bi_v i) && (bi_v i <=? bi_v j) && (0 <=? bi_k i) && (bi_k i <=? bi_k j)); [|reflexivity].
  destruct (item_nn facts ball i); [|reflexivity]. destruct (item_le facts i j); reflexivity.
Qed.
Fixpoint items_nn_lz (pf : pfacts) (facts : list sprop) (bfrom : list bitem) (bto hints : list bitem) : bool :=
  match bto with
  | [] => true
  | i :: r => match hints with
              | j :: h' => item_nn_lz pf facts bfrom (Some j) i &&& items_nn_lz pf facts bfrom r h'
              | [] => item_nn_lz pf facts bfrom None i &&& items_nn_lz pf facts bfrom r []
              end
  end.
Lemma items_nn_lz_eq : ltac2:(tb__ "0|1|
SaS96A1SaS2dA1M0G0G0S2dSa1S2dR1R2A3Sa1S2dR2R5A3F_;Fj;S3S9S80Sa5R5A1R5R4R3R2A5Sa0S2dS5cR5R4A2R3A3A3F_;Fhints;Fbto;Fbfrom;Ffacts;").
Proof.
  intros facts bfrom bto. induction bto as [|i r IH]; intros hints Hh; cbn [items_nn_lz forallb]; [reflexivity|].
  destruct hints as [|j h'].
  - rewrite lazy_andb_eq_lz, (item_nn_lz_eq facts bfrom None i I), (IH [] Hh). reflexivity.
  - rewrite lazy_andb_eq_lz. rewrite (item_nn_lz_eq facts bfrom (Some j) i) by (apply Hh; left; reflexivity).
    rewrite (IH h') by (intros x Hx; apply Hh; right; exact Hx). reflexivity.
Qed.
Definition bud_pay_lz (pf : pfacts) (facts : list sprop) (costV : sv) (costK : Z) (bfrom bto : list bitem) : bool := ltac2:(tb__ "0|5|
S9S9L_;M0SdSdS34Vbfrom;A1S34Vbto;A1A2S1fZ0VcostK;A2A2G0S80Vpf;Vfacts;Vbfrom;Vbto;Vbfrom;A5G0SbS2fS0A2S9Lx;M1S54Vbfrom;A1S2fS0G1S54Vbto;A1S2fS0S4fVpf;Vfacts;S10SbS0S2eA2M2R4S10G2S4eR2A1M3S17G2S11S0S2eN1S55VcostV;A1A4S13G2A1A3A3A3S21R3R1A2M4A4Ltc;Ltf;Xbx1Lfc;Lff;Xbx1G1S53Vbfrom;A1S2fS0G1S53Vbto;A1S2fS0S4fVpf;Vfacts;S10G2R4G3A3S21G4VcostK;A2A4Ltc;Ltf;Xbx1Lfc;Lff;Xbx1S12X9x2S12X9x2S12X9x2").
Lemma bud_pay_lz_eq : ltac2:(tb__ "0|1|
SaS96A1S95S0SaS2dA1M0G0S3S9S7eSa5R5A1R5R4R3R2R1A6S49R5R4R3R2R1A5A3Fbto;Fbfrom;FcostK;FcostV;Ffacts;").
Proof.
  intros. unfold bud_pay_lz, bud_pay. rewrite !lazy_andb_eq_lz. rewrite (items_nn_lz_eq facts bfrom bto bfrom) by (intros j H; exact H).
  destruct (wformV bfrom) as [ff fc]; destruct (wformV bto) as [tf tc]; destruct (wformK bfrom) as [ffk fck]; destruct (wformK bto) as [tfk tck].
  rewrite !lf_nonneg_p_eq.
  destruct (bd_wpos bfrom), (bd_wpos bto), (forallb (item_nn facts bfrom) bto), (0 <=? costK); cbn; try reflexivity;
    destruct (lf_nonneg _ _ _); reflexivity.
Qed.
Definition bud_le (facts : list sprop) (bto bfrom : list bitem) : bool := ltac2:(tb__ "0|1|
Sb7Vfacts;A1Sa6S9S9L_;S7cR1Vfacts;Vbfrom;Vbto;Vbfrom;A5ScS7eR1Vfacts;S99Z0M0A1G0Vbfrom;Vbto;A6X9x2Tpf;").
Lemma bud_le_ref_eq : ltac2:(tb__ "0|1|
SaS96A1SaS2dA1M0G0S3S9S64R3R2R1A3S7dR3R2R1A3A3Fbfrom;Fbto;Ffacts;").
Proof.
  intros. unfold bud_le, bud_le_ref. cbv zeta. rewrite DigFastA.mk_pf_f_eq, lazy_orb_eq_lz, bud_pay_lz_eq. rewrite (bud_le_pos_lz_eq facts bfrom bto bfrom) by (intros j H; exact H). reflexivity.
Qed.
Lemma bud_le_sound : ltac2:(tb__ "0|1|
SaS96A1SaS2dA1M0G0S94S9eS96S97R1A1R4A3S33R3R2A2S3S9S64R6R5R4A3ScA3S4S1dS31R6R4A2S31R5R4A2A2S4S1dS30R6R4A2S30R5R4A2A2S4S33R6R4A2S4S3S9S34R6A1ScA3S3S9S34R5A1ScA3A2A2A2A2F_;F_;F_;Frho;Fbfrom;Fbto;Ffacts;").
Proof.
  intros facts bto bfrom rho HF Hn H. rewrite bud_le_ref_eq in H. exact (bud_le_ref_sound facts bto bfrom rho HF Hn H).
Qed.

Definition pay_sem (rho : valuation) (costV : sv) (costK : Z) (bfrom bto : list bitem) : Prop := ltac2:(tb__ "0|0|
S4S1dS1eS39Vrho;VcostV;A2S31Vbto;Vrho;A2A2S31Vbfrom;Vrho;A2A2S4S1dS1eVcostK;S30Vbto;Vrho;A2A2S30Vbfrom;Vrho;A2A2S33Vbto;Vrho;A2A2A2").
Definition pay_okF (pre : valuation -> Prop) (facts : list sprop) (costV : sv) (costK : Z) (bfrom bto : list bitem) : Prop := ltac2:(tb__ "0|0|
S4S3S9S34Vbto;A1ScA3S4S1dZ0VcostK;A2S94S9eS96S97R1A1Vfacts;A3Vpre;R2A1S3S9S34Vbfrom;A1ScA3S33Vbfrom;R4A2S5fR5VcostV;VcostK;Vbfrom;Vbto;A5F_;F_;F_;F_;Frho;A2A2").
Lemma bud_pay_okF : ltac2:(tb__ "0|1|
S94OF_;SaS96A1S95S0SaS2dA1M0G0S3S9S49R5R4R3R2R1A5ScA3S6eR7R6R5R4R3R2A6F_;Fbto;Fbfrom;FcostK;FcostV;Ffacts;Fpre;").
Proof.
  intros pre facts costV costK bfrom bto H. split; [|split].
  - unfold bud_pay in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
    apply andb_prop in H as [_ H]. exact H.
  - unfold bud_pay in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H]. apply Z.leb_le in H. exact H.
  - intros rho HF _ _ Hn. destruct (bud_pay_sound facts _ _ _ _ rho HF Hn H) as (P1 & P2 & _ & _ & _ & P6 & _). split; [exact P1|]. split; [exact P2 | exact P6].
Qed.
Lemma pay_sem_nonneg : ltac2:(tb__ "0|2|
S94S95S0SaS2dA1M0G0S3S9S34R1A1ScA3S5fR6R5R4R3R2A5S4S1dZ0M1S31R3R7A2A2S1dG1S30R3R7A2A2A2F_;F_;Fbto;Fbfrom;FcostK;FcostV;Frho;").
Proof. intros rho costV costK bfrom bto Hw (_ & _ & Hn). apply bsum_nonneg; assumption. Qed.

Definition BUD (b : list bitem) (BX : Z * Z) (V Km Kf : Z) (rho : valuation) : Prop := ltac2:(tb__ "0|3|
S4S1dZ0M0SeS0S0VBX;A3M1A2S4S1dG0SfS0S0VBX;A3M2A2S4S1dG0VV;A2S4S1dG0VKm;A2S4S1dG0VKf;A2S4S3S9S34Vb;A1ScA3S4S33Vb;Vrho;A2S4S1dS1eS1eVV;S31Vb;Vrho;A2A2G1A2Sb1A2S1dS1eS1eS20S3dS1eVKm;VKf;A2A2S30Vb;Vrho;A2A2G2A2S20S3dSb2A2A2A2A2A2A2A2A2A2A2").

Lemma BUD_sums_nonneg : ltac2:(tb__ "0|1|
SaS2dA1SbS0S0A2S0S0S0S94S36R6R5R4R3R2R1A6S4S1dZ0M0S31R7R2A2A2S1dG0S30R7R2A2A2A2F_;Frho;FKf;FKm;FV;FBX;Fb;").
Proof. intros b BX V Km Kf rho (_ & _ & _ & _ & _ & Hw & Hn & _). apply bsum_nonneg; assumption. Qed.

Lemma bd_nn_agree : ltac2:(tb__ "0|0|
S1SaS2dA1S94S94SacR4R2R1A3S3S9S4dR5R4A2ScA3S33R5R4A2S33R6R4A2F_;F_;F_;Frho';Frho;Fb;Fn;").
Proof.
  intros n b rho rho' Hag Hb Hn. unfold bd_nn in *. apply Forall_forall. intros it Hit.
  pose proof (proj1 (Forall_forall _ _) Hn it Hit) as X.
  pose proof (bsum_agree n rho rho' [BI 1 0 (bi_f it) (bi_c it)] Hag) as Y. cbn in Y.
  unfold bd_below in Hb. pose proof (proj1 (forallb_forall _ _) Hb it Hit) as Hbi.
  specialize (Y ltac:(rewrite Hbi; reflexivity)). destruct Y as [Y _]. unfold bival in *. cbn [bi_f bi_c] in Y. lia.
Qed.

Lemma BUD_agree : ltac2:(tb__ "0|0|
S1SaS2dA1SbS0S0A2S0S0S0S94S94SacR8R2R1A3S3S9S4dR9R8A2ScA3S36R9R8R7R6R5R4A6S36RaR9R8R7R6R4A6F_;F_;F_;Frho';Frho;FKf;FKm;FV;FBX;Fb;Fn;").
Proof.
  intros n b BX V Km Kf rho rho' Hag Hb H. pose proof H as (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2). unfold BUD.
  rewrite (bsumV_agree n rho rho' b Hag Hb), (bsumK_agree n rho rho' b Hag Hb).
  repeat (split; [assumption|]). split; [eapply bd_nn_agree; eauto|]. auto.
Qed.

Lemma bd_nn_subst : ltac2:(tb__ "0|0|
Sa8SaS2dA1S94S6S33S42R3R2A2R1A2S33R2SaaR1R3A2A2A2Frho;Fb;Fs;").
Proof.
  intros s b rho. unfold bd_nn, bd_subst. rewrite Forall_map. split; intros H; apply Forall_forall; intros it Hit;
    pose proof (proj1 (Forall_forall _ _) H it Hit) as X; cbv beta in X |- *;
    pose proof (bsumV_subst s [BI 1 0 (bi_f it) (bi_c it)] rho) as Y; cbn in Y; unfold bival in *; cbn [bi_subst bi_f bi_c] in X, Y |- *; lia.
Qed.
Lemma bd_wpos_subst : ltac2:(tb__ "0|0|
Sa8SaS2dA1S3S9S34S42R2R1A2A1S34R1A1A3Fb;Fs;").
Proof. intros s b. unfold bd_wpos, bd_subst. induction b as [|it r IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma bd_wpos_app : ltac2:(tb__ "0|1|
SaS2dA1M0G0S3S9S34S10S2dR2R1A3A1SdS34R2A1S34R1A1A2A3Fb2;Fb1;").
Proof. intros. unfold bd_wpos. apply forallb_app. Qed.
Lemma bd_nn_app : ltac2:(tb__ "0|1|
SaS2dA1M0G0S94S6S33S10S2dR3R2A3R1A2S4S33R3R1A2S33R2R1A2A2A2Frho;Fb2;Fb1;").
Proof. intros. unfold bd_nn. apply Forall_app. Qed.

Lemma BUD_transfer : ltac2:(tb__ "0|1|
SaS96A1Sa8SaS2dA1M0G0SbS0S0A2S0S0S0S94S9eS96S97R1A1R9A3S3S9S64RaS42R9R8A2R7A3ScA3S36R8R7R6R5R4R3A6S36RaR8R7R6R5SaaR4RbA2A6F_;F_;F_;Frho;FKf;FKm;FV;FBX;Fbfrom;Fbto;Fs;Ffacts;").
Proof.
  intros facts s bto bfrom BX V Km Kf rho HF Hle H. pose proof H as (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2).
  destruct (bud_le_sound facts _ _ rho HF Hn Hle) as (L1 & L2 & L3 & L4 & L5). rewrite bsumV_subst in L1. rewrite bsumK_subst in L2.
  rewrite bd_wpos_subst in L4. apply bd_nn_subst in L3.
  unfold BUD. repeat (split; [assumption|]). lia.
Qed.

Lemma BUD_pay_sem : ltac2:(tb__ "0|3|
S94S95S0SaS2dA1M0G0SbS0S0A2S0S0S0S0S0S0S5fRcRbRaR9R8A5S3S9S34R9A1ScA3S1dZ0M1RcA2S36RcRaR9R8R7RfA6S1dG1R7A2M2G2G2S1dRaS1eRdS39R13R12A2A2A2S1dS20S3dS1eRaR9A2A2S1eS20S3dS1eRdRcA2A2R12A2A2S36R11R10RcRbRaR15A6F_;F_;F_;F_;F_;F_;F_;F_;F_;FKf';FKm';FV';FKf;FKm;FV;FBX;Fbto;Fbfrom;FcostK;FcostV;Frho;").
Proof.
  intros rho costV costK bfrom bto BX V Km Kf V' Km' Kf' (P1 & P2 & NN) Hw Hc H HV' HKm' HKf' HV HK.
  pose proof (bsum_nonneg bto rho Hw NN) as [N1 N2].
  pose proof H as (A1 & A2 & A3 & A4 & A5 & Hwf & Hn & B1 & B2). unfold BUD. repeat (split; [assumption|]). lia.
Qed.
Lemma BUD_payF : ltac2:(tb__ "0|2|
S94OFx;SaS96A1S95S0SaS2dA1M0G0SbS0S0A2S0S0S0S0S0S0S94S9eS96S97R1A1RdA3RfR2A1S6eR10RfReRdRcRbA6S36RdRbRaR9R8R4A6S1dZ0R8A2M1G1G1S1dRbS1eReS39R8R13A2A2A2S1dS20S3dS1eRbRaA2A2S1eS20S3dS1eReRdA2A2R13A2A2S36R12R11RdRcRbRaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Frho;FKf';FKm';FV';FKf;FKm;FV;FBX;Fbto;Fbfrom;FcostK;FcostV;Ffacts;Fpre;").
Proof.
  intros pre facts costV costK bfrom bto BX V Km Kf V' Km' Kf' rho HF Hpre (Hw & Hc & HP) H.
  pose proof H as (_ & _ & _ & _ & _ & Hwf & Hn & _). apply (BUD_pay_sem rho costV costK bfrom bto); auto.
Qed.
Lemma BUD_pay : ltac2:(tb__ "0|2|
SaS96A1S95S0SaS2dA1M0G0SbS0S0A2S0S0S0S0S0S0S94S9eS96S97R1A1RdA3S3S9S49ReRdRcRbRaA5ScA3S36RcRaR9R8R7R3A6S1dZ0R7A2M1G1G1S1dRaS1eRdS39R7R12A2A2A2S1dS20S3dS1eRaR9A2A2S1eS20S3dS1eRdRcA2A2R12A2A2S36R11R10RcRbRaR9A6F_;F_;F_;F_;F_;F_;F_;F_;Frho;FKf';FKm';FV';FKf;FKm;FV;FBX;Fbto;Fbfrom;FcostK;FcostV;Ffacts;").
Proof.
  intros facts costV costK bfrom bto BX V Km Kf V' Km' Kf' rho HF HP. apply (BUD_payF (fun _ => True) facts); [exact HF | exact I |].
  apply bud_pay_okF. exact HP.
Qed.

Lemma BUD_limit_ok_alloc : ltac2:(tb__ "0|0|
SaS2dA1SbS0S0A2S0S0S0S94S0S36R7R6R5R4R3R2A6S1dZ0R2A2S1dR3S31R9R4A2A2S1dS3dS30RaR5A2A2Sb3R9R8R7R5A4F_;F_;F_;F_;Fn;Frho;FKf;FKm;FV;FBX;Fb;").
Proof.
  intros b BX V Km Kf rho n H Hn HV HK. pose proof H as (A1 & A2 & A3 & A4 & A5 & _ & _ & B1 & B2). unfold KU in *. apply limit_ok_alloc_intro; nia.
Qed.
Lemma BUD_limit_ok_free : ltac2:(tb__ "0|0|
SaS2dA1SbS0S0A2S0S0S0S94S36R6R5R4R3R2R1A6S1dS3dS30R7R2A2A2Sb4R6R5R4A3F_;F_;Frho;FKf;FKm;FV;FBX;Fb;").
Proof.
  intros b BX V Km Kf rho H HK. pose proof (BUD_sums_nonneg _ _ _ _ _ _ H) as [N1 N2].
  pose proof H as (A1 & A2 & A3 & A4 & A5 & _ & _ & B1 & B2). unfold KU in *. apply limit_ok_free_intro; nia.
Qed.

Lemma BUD_split_sem : ltac2:(tb__ "0|2|
S94SaS2dA1M0G0G0SbS0S0A2S0S0S0S5fR8S99Z0M1A1G1R7S10S2dR6R5A3A5S3S9S34S10S2dR7R6A3A1ScA3S36R9R6R5R4R3RaA6S4S36R9S11S0S0S1eS31R8RbA2SeS0S0R7A3A2S1eS30R8RbA2SfS0S0R7A3A2A4R6R5R4RbA6S4S3S9S34R8A1ScA3S33R8RbA2A2A2F_;F_;F_;FKf;FKm;FV;FBX;Fbrest;Fbc;Fbnode;Frho;").
Proof.
  intros rho bnode bc brest BX V Km Kf (P1 & P2 & NN) Hw2 H.
  unfold uval in P1. rewrite U_lit in P1. change (0 mod M64v) with 0 in P1.
  rewrite bd_wpos_app in Hw2. apply andb_prop in Hw2 as [Wc Wr]. apply bd_nn_app in NN as [Nc Nr].
  rewrite bsumV_app in P1. rewrite bsumK_app in P2.
  pose proof (bsum_nonneg bc rho Wc Nc) as [X1 X2]. pose proof (bsum_nonneg brest rho Wr Nr) as [X3 X4].
  pose proof H as (A1 & A2 & A3 & A4 & A5 & _ & _ & B1 & B2).
  split; [|auto]. unfold BUD. cbn [fst snd]. repeat (split; [first [assumption | lia]|]). lia.
Qed.
Lemma BUD_splitF : ltac2:(tb__ "0|2|
S94OFx;SaS96A1SaS2dA1M0G0G0SbS0S0A2S0S0S0S94S9eS96S97R1A1R9A3RbR2A1S6eRcRbS99Z0M1A1G1RaS10S2dR9R8A3A6S36RbR8R7R6R5R4A6S4S36RbS11S0S0S1eS31RaR5A2SeS0S0R9A3A2S1eS30RaR5A2SfS0S0R9A3A2A4R8R7R6R5A6S4S3S9S34RaA1ScA3S33RaR5A2A2A2F_;F_;F_;F_;Frho;FKf;FKm;FV;FBX;Fbrest;Fbc;Fbnode;Ffacts;Fpre;").
Proof.
  intros pre facts bnode bc brest BX V Km Kf rho HF Hpre (Hw & _ & HP) H.
  pose proof H as (_ & _ & _ & _ & _ & Hwf & Hn & _). apply (BUD_split_sem rho bnode); auto.
Qed.
Lemma BUD_split : ltac2:(tb__ "0|2|
SaS96A1SaS2dA1M0G0G0SbS0S0A2S0S0S0S94S9eS96S97R1A1R9A3S3S9S49RaS99Z0M1A1G1R9S10S2dR8R7A3A5ScA3S36RaR7R6R5R4R3A6S4S36RaS11S0S0S1eS31R9R4A2SeS0S0R8A3A2S1eS30R9R4A2SfS0S0R8A3A2A4R7R6R5R4A6S4S3S9S34R9A1ScA3S33R9R4A2A2A2F_;F_;F_;Frho;FKf;FKm;FV;FBX;Fbrest;Fbc;Fbnode;Ffacts;").
Proof.
  intros facts bnode bc brest BX V Km Kf rho HF HP. apply (BUD_splitF (fun _ => True) facts); [exact HF | exact I |].
  apply bud_pay_okF. exact HP.
Qed.

Lemma BUD_join : ltac2:(tb__ "0|2|
SaS2dA1M0G0SbS0S0A2S0S0S0S94S94S36R8S11S0S0S1eS31R7R2A2SeS0S0R6A3A2S1eS30R7R2A2SfS0S0R6A3A2A4R5R4R3R1A6S3S0S31R8R2A2S31R8R3A2A3S3S0S30R9R3A2S30R9R4A2A3S3S9S34RaA1ScA3S33RbR5A2S1dZ0M1SeS0S0RbA3A2S1dG1SfS0S0RcA3A2S36S10S2dRfReA3RdRcRbRaR8A6F_;F_;F_;F_;F_;F_;F_;Frho';Frho;FKf;FKm;FV;FBX;Fbrest;Fbp;").
Proof.
  intros bp brest BX V Km Kf rho rho' H EV EK Wr Nr HX1 HX2.
  pose proof H as (A1 & A2 & A3 & A4 & A5 & Wp & Np & B1 & B2). cbn [fst snd] in B1, B2, A1, A2.
  pose proof (bsum_nonneg brest rho' Wr Nr) as [X3 X4].
  unfold BUD. rewrite bd_wpos_app, Wp, Wr. rewrite bsumV_app, bsumK_app, EV, EK.
  repeat (split; [first [assumption | reflexivity | lia]|]). split; [apply bd_nn_app; auto|]. lia.
Qed.

Lemma bd_nn_of_check : ltac2:(tb__ "0|0|
SaS96A1SaS2dA1S94S9eS96S97R1A1R3A3S3S9Sa0S2dS5dR4A1R3A3ScA3S33R4R3A2F_;F_;Frho;Fb;Ffacts;").
Proof. intros facts b rho HF H. unfold bd_nn. apply Forall_forall. intros it Hit. eapply item_nonneg_sound; [exact HF|]. exact (proj1 (forallb_forall _ _) H it Hit). Qed.

Lemma bsum_vars_ext : ltac2:(tb__ "0|1|
S1S9F_;SaS2dA1S94S94Sa8S3S9S79R5R4A2ScA3S95S3S9SadR7R1A2ScA3S3SabQ40A1S98R6Sa9R4R2A2A2S98R5R2A2A3F_;Fe;S4S3S0S31S42R3R6A2M0R5A2S31R6R4A2A3S3S0S30G0R5A2S30R6R4A2A3A2F_;F_;Fs;Fr2;Fr1;Fb;Ff;").
Proof.
  intros f b r1 r2 s Hb He. apply bsum_ext. intros e (it & ca & Hit & Hca & <-). apply He.
  unfold bd_vars_all in Hb. pose proof (proj1 (forallb_forall _ _) Hb it Hit) as X. unfold lf_vars_all in X.
  exact (proj1 (forallb_forall _ _) X ca Hca).
Qed.

Lemma lfval_eval_ext : ltac2:(tb__ "0|0|
S2fS94S94S95S3SabQ40A1S98R3R1A2S98R2R1A2A3Fe;S3S0S35R3R4A2S35R2R4A2A3F_;Fr2;Fr1;Ff;").
Proof.
  intros f r1 r2 H. induction f as [|[c a] f' IH]; cbn; [reflexivity|]. rewrite IH.
  destruct a as [e|e|e c1 k B]; cbn [aval]; unfold uval; rewrite H; reflexivity.
Qed.
Lemma bsum_eval_ext : ltac2:(tb__ "0|0|
SaS2dA1S94S94S95S3SabQ40A1S98R3R1A2S98R2R1A2A3Fe;S4S3S0S31R4R3A2S31R4R2A2A3S3S0S30R4R3A2S30R4R2A2A3A2F_;Fr2;Fr1;Fb;").
Proof.
  intros b r1 r2 H. induction b as [|it r IH]; cbn [bsumV bsumK]; [auto|]. destruct IH as [-> ->].
  unfold bival. rewrite (lfval_eval_ext (bi_f it) r1 r2 H). auto.
Qed.
Lemma bd_nn_eval_ext : ltac2:(tb__ "0|0|
SaS2dA1S94S94S95S3SabQ40A1S98R3R1A2S98R2R1A2A3Fe;S33R4R3A2S33R5R3A2F_;F_;Fr2;Fr1;Fb;").
Proof.
  intros b r1 r2 H Hn. unfold bd_nn in *. apply Forall_forall. intros it Hit.
  pose proof (proj1 (Forall_forall _ _) Hn it Hit) as X. unfold bival in *. rewrite (lfval_eval_ext (bi_f it) r2 r1 ltac:(intros e; symmetry; apply H)). exact X.
Qed.
Lemma bival_subst_ext : ltac2:(tb__ "0|1|
S2dS94S94Sa8S0S2eSa1SbS0S2eA2S11S0S2eR2R1A4S3aR6A1A3S3SabQ40A1S98R6Sa9R4S58R2A1M0A2A2S98R5G0A2A3F_;Fa;Fc;S3S0S46R4S8cR2R5A2A2S46R3R5A2A3F_;Fs;Fr2;Fr1;Fit;").
Proof.
  intros it r1 r2 s H. unfold bival, bi_subst. cbn [bi_f bi_c]. unfold lf_subst.
  rewrite (lfval_ext (bi_f it) r1 r2 (atom_subst s)); [reflexivity|].
  intros c a Hin. pose proof (H c _ Hin) as X. destruct a as [e|e|e c1 k B]; cbn [aval atom_subst asv] in *; unfold uval; rewrite X; reflexivity.
Qed.
Lemma bd_nn_vars_ext : ltac2:(tb__ "0|0|
S1S9F_;SaS2dA1S94S94Sa8S3S9S79R5R4A2ScA3S95S3S9SadR7R1A2ScA3S3SabQ40A1S98R6Sa9R4R2A2A2S98R5R2A2A3F_;Fe;S33R6R4A2S33S42R4R7A2R6A2F_;F_;F_;Fs;Fr2;Fr1;Fb;Ff;").
Proof.
  intros f b r1 r2 s Hb He Hn. unfold bd_nn, bd_subst in *. apply Forall_forall. intros it' Hit'.
  apply in_map_iff in Hit' as (it & <- & Hit). rewrite (bival_subst_ext it r1 r2 s).
  - exact (proj1 (Forall_forall _ _) Hn it Hit).
  - intros c a Hca. apply He. unfold bd_vars_all in Hb. pose proof (proj1 (forallb_forall _ _) Hb it Hit) as X.
    unfold lf_vars_all in X. exact (proj1 (forallb_forall _ _) X (c, a) Hca).
Qed.

Record bxt : Type := mkBX { bx2 : Z * Z; bxS : Z; bxN : Z }.
Definition bxV (BX : bxt) : Z := fst (bx2 BX).
Definition bxK (BX : bxt) : Z := snd (bx2 BX).
Definition LARGE_MIN : Z := 64513.
Definition SECCAP : Z := ltac2:(tb__ "0|0|
S20S57S21S24Z2Z14A2SbbA2A2").
Definition BXnn (BX : bxt) : Prop := ltac2:(tb__ "0|1|
S4S1dZ0M0S3eVBX;A1A2S1dG0S59VBX;A1A2A2").
Definition BXok (BX : bxt) : Prop := ltac2:(tb__ "0|0|
S4S56VBX;A1S1dS21S1eS40VBX;A1Sb1A2S3eVBX;A1A2S77A2A2").
Lemma BXok_nn : ltac2:(tb__ "0|0|
S37S48R1A1S56R2A1F_;FBX;"). Proof. intros BX [H _]. exact H. Qed.
Lemma BXok_pair : ltac2:(tb__ "0|2|
S37S48R1A1S4S1dZ0M0SeS0S0S66R2A1M1A3A2S1dG0SfS0S0G1A3A2A2F_;FBX;"). Proof. intros BX [H _]. exact H. Qed.
Lemma BXnn_pair : ltac2:(tb__ "0|2|
S37S56R1A1S4S1dZ0M0SeS0S0S66R2A1M1A3A2S1dG0SfS0S0G1A3A2A2F_;FBX;"). Proof. intros BX H. exact H. Qed.

Lemma BXok_mono : ltac2:(tb__ "0|0|
S37S37S48R2A1S3S0S40R2A1S40R3A1A3S1dS3eR4A1S3eR3A1A2S1dZ0S59R4A1A2S48R5A1F_;F_;F_;F_;FBX';FBX;").
Proof. intros BX BX' [[H1 H2] H3] ES HV HK. unfold BXok, BXnn in *. rewrite ES. repeat split; lia. Qed.

Definition TVMAX : Z := 256.
Definition TVMAXn : nat := 256.
Definition BXok_d (d : Z) (BX : bxt) : Prop := ltac2:(tb__ "0|1|
S4S48VBX;A1S4S1dZ0S47VBX;A1M0A2S4S1dZ1Vd;A2S1dS1eG0S20S63Vd;A2A2SbaA2A2A2A2").
Lemma BXok_d_ok : ltac2:(tb__ "0|0|
S0S37S3bR2R1A2S48R2A1F_;FBX;Fd;"). Proof. intros d BX [H _]. exact H. Qed.
Lemma BXok_d_nn : ltac2:(tb__ "0|0|
S0S37S3bR2R1A2S56R2A1F_;FBX;Fd;"). Proof. intros d BX [[H _] _]. exact H. Qed.
Lemma BXok_d_pair : ltac2:(tb__ "0|2|
S0S37S3bR2R1A2S4S1dZ0M0SeS0S0S66R2A1M1A3A2S1dG0SfS0S0G1A3A2A2F_;FBX;Fd;"). Proof. intros d BX [[H _] _]. exact H. Qed.
Lemma BXok_d_N : ltac2:(tb__ "0|0|
S0S37S3bR2R1A2S1dZ0S47R2A1A2F_;FBX;Fd;"). Proof. intros d BX (_ & H & _). exact H. Qed.

Lemma BXok_d_le : ltac2:(tb__ "0|0|
S0S0S37S3bR3R1A2S4S1dZ1R3A2S1dR3R4A2A2S3bR4R3A2F_;F_;FBX;Fd';Fd;").
Proof. intros d d' BX (H1 & H2 & H3 & H4) Hd. unfold BXok_d, TVMAX in *. split; [exact H1|]. split; [exact H2|]. split; lia. Qed.

Lemma BXok_d_mono : ltac2:(tb__ "0|3|
S0S0S37S37S3bR4R2A2S3S0S40R2A1S40R3A1A3S1dS3eR4A1S3eR3A1A2S1dZ0S59R4A1A2S4S1dS47R6A1M0S47R5A1M1A2S1dG1S1eG0S63A2A2A2S3S9SdS1fZ1M2R8A2S1fS1eR8G2A2R9A2A2ScA3S3bR9R7A2F_;F_;F_;F_;F_;F_;FBX';FBX;FdC;FdF;").
Proof.
  intros dF dC BX BX' (H1 & H2 & H3 & H4) ES HV HK HN Hd. apply andb_prop in Hd as [Hd1 Hd2]. apply Z.leb_le in Hd1, Hd2.
  unfold BXok_d, TVMAX in *. split; [exact (BXok_mono BX BX' H1 ES HV HK)|]. split; [lia|]. split; lia.
Qed.

Lemma BXok_d_mono0 : ltac2:(tb__ "0|0|
S0S37S37S3bR3R2A2S3S0S40R2A1S40R3A1A3S1dS3eR4A1S3eR3A1A2S1dZ0S59R4A1A2S3S0S47R5A1S47R6A1A3S3bR8R6A2F_;F_;F_;F_;F_;FBX';FBX;Fd;").
Proof.
  intros d BX BX' (H1 & H2 & H3 & H4) ES HV HK HN. unfold BXok_d in *. split; [exact (BXok_mono BX BX' H1 ES HV HK)|]. rewrite HN. split; [exact H2|]. split; [exact H3 | exact H4].
Qed.

Definition is_smallZ (v : Z * Z) : bool := ltac2:(tb__ "0|0|
SdS1bS25SeS0S0Vv;A3Z0A2A1S2bSfS0S0Vv;A3S57A2A2").
Definition cntSZ (tvs : list (Z * Z)) : Z := Z.of_nat (length (List.filter is_smallZ tvs)).
Lemma is_smallZ_large : ltac2:(tb__ "0|0|
SbS0S0A2S8S3S0SeS0S0R1A3Z0A3A1S3S9S5aR2A1S1bSbcR2A1A1A3F_;Fv;").
Proof.
  intros [b n] Hb. unfold is_smallZ, is_large, LARGE_MIN. cbn [fst snd] in *. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. cbn [negb andb].
  destruct (Z.ltb_spec n 64513), (Z.leb_spec 64513 n); try reflexivity; lia.
Qed.
Lemma is_smallZ_null : ltac2:(tb__ "0|0|
SbS0S0A2S3S0SeS0S0R1A3Z0A3S3S9S5aR2A1S12A3F_;Fv;").
Proof. intros [b n] Hb. unfold is_smallZ. cbn [fst snd] in *. subst b. reflexivity. Qed.
Lemma is_smallZ_big : ltac2:(tb__ "0|0|
SbS0S0A2S1dS57SfS0S0R1A3A2S3S9S5aR2A1S12A3F_;Fv;").
Proof. intros [b n] Hn. unfold is_smallZ. cbn [fst snd] in *. destruct (Z.ltb_spec n LARGE_MIN); [lia|]. apply andb_false_r. Qed.
Lemma cntSZ_nil : cntSZ [] = 0. Proof. reflexivity. Qed.
Lemma cntSZ_cons : ltac2:(tb__ "0|1|
SbS0S0A2M0SaG0A1S3S0S44S17G0R2R1A3A1S1eS9S0L_;S5aR2A1Z1Z0X9x2S44R1A1A2A3Fl;Fv;").
Proof. intros v l. unfold cntSZ. cbn [List.filter]. destruct (is_smallZ v); cbn [length]; lia. Qed.
Lemma cntSZ_app : ltac2:(tb__ "0|2|
SaSbS0S0A2M0A1M1G1S3S0S44S10G0R2R1A3A1S1eS44R2A1S44R1A1A2A3Fl2;Fl1;").
Proof. intros l1 l2. unfold cntSZ. rewrite List.filter_app, List.length_app. lia. Qed.
Lemma cntSZ_bounds : ltac2:(tb__ "0|2|
SaSbS0S0A2M0A1S4S1dZ0S44R1A1M1A2S1dG1S27S1aG0R1A2A1A2A2Fl;").
Proof. intros l. unfold cntSZ. pose proof (List.filter_length_le is_smallZ l). lia. Qed.
Lemma cntSZ_perm : ltac2:(tb__ "0|2|
SaSbS0S0A2M0A1M1G1Sc4G0R2R1A3S3S0S44R3A1S44R2A1A3F_;Fl2;Fl1;").
Proof.
  intros l1 l2 H. induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2]; [reflexivity | rewrite !cntSZ_cons, IH; reflexivity | rewrite !cntSZ_cons; lia | lia].
Qed.

Lemma prim_room_of_capN : ltac2:(tb__ "0|0|
S0S37Sb8S0S3bR4R3A2S1dSc0R3A1S1eS47R4A1R2A2A2S1dR3S63A2SbeR5A1F_;F_;F_;Fc;FA;FBX;Fd;").
Proof. intros d BX A c (_ & H2 & H3 & H4) HS Hc. unfold prim_room, TVMAX in *. nia. Qed.

Lemma sec_room_of_cap : ltac2:(tb__ "0|0|
S37Sb8S1dS21S1eS40R2A1Sb1A2S3eR2A1A2S77A2S1dS20S57SbdR2A1A2S1eS40R3A1Sb9R2A1A2A2S1dS1eSb9R3A1S3eR4A1A2Sb1A2SbfR4A1F_;F_;F_;FA;FBX;").
Proof. intros BX A H1 H2 H3. unfold sec_room, SECCAP, LARGE_MIN in *. nia. Qed.
