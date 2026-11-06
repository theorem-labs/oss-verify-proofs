(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "soff"; "eval"; "sv_below"; "holds"; "sobj"; "SAlu"; "SLit"; "cell"; "ext_low"; "ob_base"; "SAluW"; "ob_hi"; "ob_lo"; "obj_hi_of"; "obj_holds"; "obj_lo_of"; "c_off"; "c_width"; "ob_cells"; "SMd"; "SMdW"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "not"; "True"; "iff"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "true"; "list"; "option"; "Some"; "pair"; "fst"; "nat"; "snd"; "false"; "None"; "length"; "app"; "cons"; "nil"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "modulo"; "lt"; "mul"; "sub"; "ltb"; "divide"; "of_N"; "opp"; "eqb"; "shiftr"; "abs"; "div"; "lxor"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV"; "U"; "in_itv"; "tbl_ok"; "dgv_ok"; "sumZ"; "sv_size"; "entry_ok"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "lin"; "fdig"; "ineq"; "snorm"; "i32max"; "i32min"; "tbl_entry"; "dg_srels"; "rel_offset"; "smax"; "smin"; "dg_facts"; "same_atoms"; "decision"; "lin_of0"; "in_bounds"; "lin_pos_sum"; "lin_sub"; "linz"; "snorm32"; "stv_t"; "sub_fold"; "sv_of_lin"; "wnorm"; "wnorm_t"; "cell_rel"; "crel"; "dg_pool"; "dg_urels"; "ifact"; "in_bounds_d"; "itv"; "itv0"; "itv_t"; "lin_add1"; "lin_exact_s"; "lin_exact_u"; "lin_gcd"; "lin_merge"; "lin_norm"; "lin_of"; "lin_sub_negs"; "lin_term"; "mk_ctx"; "mk_dig"; "mk_md_1"; "mk_md_f"; "mk_md_f0"; "mk_mdw_f"; "mk_op_f"; "mk_opw_f"; "mk_slt_f"; "mk_slt_f_t"; "rel_offset0"; "remove_atoms"; "tbl_init"; "C3magic"; "CDisj"; "CLit"; "add_new"; "aligned_tighten"; "atoms_of"; "bool_rels_of_fact"; "boolish"; "brels"; "combine_all"; "ctx0"; "decide_t"; "dg_tbl"; "dg_with_pool"; "dg_with_tbl"; "entry_norm"; "find_obj"; "find_obj_d"; "find_sel"; "in_i32"; "ineq_combine"; "ineq_of_rel"; "ineqs_of_rels"; "is_selmask"; "itv_lin"; "itv_sum"; "lin_add"; "lin_align"; "lin_constfold"; "lin_div"; "lin_eqb"; "lin_geq"; "lin_hi"; "lin_itv"; "lin_lo"; "lin_lo_pool"; "lin_neg"; "lin_nil"; "lin_round"; "lin_scale"; "lit_align"; "lit_is"; "mk_aluw_f"; "mk_aluw_s"; "mk_ext_f"; "mk_ext_s"; "mk_pool"; "ne_tighten"; "ne_tighten1"; "neq_of_fact"; "neq_prim"; "neqs_of"; "opp_atom"; "pool_round"; "prover_decide"; "rels_of"; "rels_of_fact"; "remu_lt"; "roundup"; "sadd32_itv"; "sadd_itv"; "same_atoms0"; "saturate"; "sclassify_fact"; "sel_case"; "sel_here"; "sfact_itv"; "sfacts_itv"; "shr_arg"; "shr_mono"; "sitv"; "sitv_d"; "sitv_of"; "sitv_of_itv"; "sleq"; "sleq_by_rel"; "sleq_d"; "sleq_lin"; "sleq_same"; "slt_xor_fold"; "small_u"; "smeet"; "srel_itv1"; "srels_itv"; "srels_of"; "srels_of_fact"; "ssub32_itv"; "ssub_itv"; "stop_itv"; "strip_zext"; "stv"; "stv_body"; "stv_node"; "sub_atoms"; "sv_equiv"; "sv_replace"; "tbl_get"; "tbl_iter"; "tbl_prop_s"; "tbl_prop_u"; "tbl_round"; "tbl_upd"; "u_of_s"; "uleq"; "uleq_by_rel"; "uleq_by_rel2"; "uleq_core"; "uleq_d"; "uleq_lin"; "uleq_same"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL"; "dg_ok"; "linZ";
"in_sitv"; "ineq_holds"; "lin_below"; "srel_holds"; "rel_holds"; "neq_holds"; "sub_fold_lin"; "@stdpp.bitvector.definitions"; "bv"; "bv_swrap"; "bv_unsigned"; "Z_to_bv"; "bv_signed"; "bv_half_modulus"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "low32"; "mul_div"; "alu32"; "branch_taken"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "ALU_SUB"; "mulop"; "M_MUL"; "ALU_ADD"; "ALU_SLL"; "ALU_SLT"; "branch_cond"; "ALU_SLTU"; "ALU_SRL"; "ALU_XOR"; "@Stdlib.Lists.List"; "filter"; "forallb"; "In"; "nth_error"; "fold_right"; "@LinuxProcessSemantics.Riscv.Prelude"; "sext"; "@Corelib.Init.Nat"; "add"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@Corelib.Init.Peano"; "lt"; "@Stdlib.Arith.PeanoNat.Nat"; "ltb"; "@Stdlib.NArith.BinNat.N"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma U_range : ltac2:(tb__ "0|1|
S4S3S1cS32Z0S42R2R1A2M0A2S36G0S34Z2Z40A2A2A2Fe;Frho;").
Proof. intros. unfold U. apply urange. Qed.

Lemma signed_big : ltac2:(tb__ "0|2|
SfaQ40M0A1S32S34Z2M1Z3fA2SfcG0R1A2A2S1bS0SfeG0R2A2S38SfcG0R2A2S34G1Z40A2A2A3F_;Fv;").
Proof.
  intros v H. pose proof (urange v). unfold bv_signed, bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63). rewrite two64.
  replace (bv_unsigned v + 2 ^ 63) with ((bv_unsigned v - 2 ^ 63) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma signed_lit : ltac2:(tb__ "0|1|
S0S1bS0SfeQ40M0SfdG0R1A2A2S4eR1A1A3Fz;").
Proof.
  intros z. pose proof (lit_unsigned z) as L. unfold snorm.
  pose proof (Z.mod_pos_bound z (2 ^ 64) ltac:(lia)).
  destruct (Z.ltb_spec (z mod 2 ^ 64) (2 ^ 63)).
  - rewrite signed_small by lia. exact L.
  - rewrite signed_big by lia. lia.
Qed.

Lemma soff_lit : ltac2:(tb__ "0|0|
S4S0S1bS0S6R2ScR1A1A2S4eR1A1A3Fz;Frho;").
Proof. intros. unfold soff. cbn [eval]. apply signed_lit. Qed.

Lemma soff_range : ltac2:(tb__ "0|2|
S4S3S1cS32S3cS34Z2Z3fA2M0A1S6R2R1A2M1A2S36G1G0A2A2Fe;Frho;").
Proof.
  intros rho e. unfold soff. pose proof (urange (eval rho e)).
  destruct (Z_lt_ge_dec (bv_unsigned (eval rho e)) (2 ^ 63)).
  - rewrite signed_small by lia. lia.
  - rewrite signed_big by lia. lia.
Qed.

Lemma soff_mod : ltac2:(tb__ "0|0|
S4S3S1bS0S35S6R2R1A2S34Z2Z40A2A2S42R2R1A2A3Fe;Frho;").
Proof.
  intros rho e. unfold soff, U. pose proof (urange (eval rho e)).
  destruct (Z_lt_ge_dec (bv_unsigned (eval rho e)) (2 ^ 63)).
  - rewrite signed_small by lia. apply Z.mod_small. lia.
  - rewrite signed_big by lia.
    replace (bv_unsigned (eval rho e) - 2 ^ 64) with (bv_unsigned (eval rho e) + (-1) * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma lazy_orb_prop : ltac2:(tb__ "0|0|
S22S22S1bS22S22S22La;R2S24R1X22x2S24A3S1eS1bS22R3S24A3S1bS22R2S24A3A2F_;Fb;Fa;").
Proof. intros [|] b H; [left; reflexivity | right; exact H]. Qed.
Lemma lazy_andb_prop : ltac2:(tb__ "0|0|
S22S22S1bS22S22S22La;R2R1S2cX22x2S24A3S1cS1bS22R3S24A3S1bS22R2S24A3A2F_;Fb;Fa;").
Proof. intros [|] b H; [split; [reflexivity | exact H] | discriminate]. Qed.

Lemma remove_atoms_sound : ltac2:(tb__ "0|1|
S4S25S3A1M0G0G0S1bS26G0A1S81R3R2A2S27G0R1A2A3S1bS0S46R5R3A2S33S46R5R4A2S46R5R2A2A2A3F_;Frest;Fatoms;Fbs;Frho;").
Proof.
  intros rho bs. induction bs as [|b bs' IH]; intros atoms rest H; cbn in H.
  - inversion H; subst. cbn [sumZ fold_right]. lia.
  - destruct (remove_atom b atoms) as [atoms'|] eqn:E; [|discriminate].
    pose proof (remove_atom_sound rho _ _ _ E) as R. specialize (IH _ _ H).
    cbn [sumZ fold_right]. unfold sumZ in *. lia.
Qed.

Lemma remove_atoms_below : ltac2:(tb__ "0|1|
S1S25S3A1M0G0G0S1bS22S111S3S8R4A1R2A3S24A3S1bS26G0A1S81R4R3A2S27G0R2A2A3S1bS22S111S3S8R6A1R3A3S24A3F_;F_;Frest;Fatoms;Fbs;Fn;").
Proof.
  intros n bs. induction bs as [|b bs' IH]; intros atoms rest Hb H; cbn in H.
  - inversion H; subst. exact Hb.
  - destruct (remove_atom b atoms) as [atoms'|] eqn:E; [|discriminate].
    eapply IH; [|exact H]. eapply remove_atom_below; eauto.
Qed.

Lemma atoms_of_sound0 : ltac2:(tb__ "0|1|
S4S3S25S3A1M0S0S1bS23G0S0A2S88R3S31S3A1Z0A3S28G0S0R2R1A4A3S1bS0S42R5R4A2S35S33S46R5R3A2R2A2S34Z2Z40A2A2A3F_;Fc;Fatoms;Fe;Frho;").
Proof.
  intros rho e atoms c H. pose proof (atoms_of_sound rho e [] 0 atoms c H) as A.
  cbn [sumZ fold_right] in A. rewrite Z.add_0_r, Z.add_0_r in A.
  unfold U. rewrite A. symmetry. apply Z.mod_small. apply urange.
Qed.

Lemma same_atoms0_sound : ltac2:(tb__ "0|0|
S4S3S3S0S1bS26S0A1Sc0R3R2A2S27S0R1A2A3S1bS0S42R5R4A2S35S33S42R5R3A2R2A2S34Z2Z40A2A2A3F_;Fd;Fx;Fa;Frho;").
Proof.
  intros rho a x d H. unfold same_atoms0 in H.
  destruct (atoms_of a [] 0) as [aa ca] eqn:Ea.
  destruct (atoms_of x [] 0) as [xa cx] eqn:Ex.
  destruct (remove_atoms xa aa) as [[|r rest]|] eqn:Er; try discriminate.
  inversion H; subst d; clear H.
  pose proof (remove_atoms_sound rho _ _ _ Er) as R. cbn [sumZ fold_right] in R.
  rewrite (atoms_of_sound0 rho a aa ca Ea), (atoms_of_sound0 rho x xa cx Ex).
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma rel_offset0_sound : ltac2:(tb__ "0|0|
S4S3S3S3S1bS26S3A1S80R3R2A2S27S3R1A2A3S1bS0S42R5R3A2S35S33S42R5R4A2S42R5R2A2A2S34Z2Z40A2A2A3F_;Foff;Fae;Fbase;Frho;").
Proof.
  intros rho base ae off H. unfold rel_offset0 in H.
  destruct (atoms_of ae [] 0) as [aa ca] eqn:Ea.
  destruct (atoms_of base [] 0) as [ba cb] eqn:Eb.
  destruct (remove_atoms ba aa) as [rest|] eqn:Er; [|discriminate].
  pose proof (remove_atoms_sound rho _ _ _ Er) as R.
  rewrite (atoms_of_sound0 rho ae aa ca Ea), (atoms_of_sound0 rho base ba cb Eb).
  rewrite Zplus_mod_idemp_l.
  pose proof (sum_of_sound rho rest (ca - cb)) as Hs.
  revert Hs H. generalize (sum_of rest (ca - cb)) as s. intros s Hs H.
  assert (E : off = match rest with [] => SLit (snorm (ca - cb)) | _ :: _ => s end)
    by (destruct rest; inversion H; reflexivity).
  subst off. clear H. unfold U.
  destruct rest as [|r rest'].
  - cbn [eval]. rewrite lit_unsigned, snorm_mod.
    rewrite Zplus_mod_idemp_r. cbn [sumZ fold_right] in R. f_equal. lia.
  - rewrite Hs, Zplus_mod_idemp_r. f_equal. lia.
Qed.

Lemma rel_offset0_below : ltac2:(tb__ "0|0|
S1S3S3S3S1bS22S8R4R2A2S24A3S1bS26S3A1S80R4R3A2S27S3R2A2A3S1bS22S8R6R3A2S24A3F_;F_;Foff;Fae;Fbase;Fn;").
Proof.
  intros n base ae off Hae H. unfold rel_offset0 in H.
  destruct (atoms_of ae [] 0) as [aa ca] eqn:Ea.
  destruct (atoms_of base [] 0) as [ba cb] eqn:Eb.
  destruct (remove_atoms ba aa) as [rest|] eqn:Er; [|discriminate].
  pose proof (atoms_of_below n ae [] 0 aa ca Hae eq_refl Ea) as Baa.
  pose proof (remove_atoms_below n _ _ _ Baa Er) as Brest.
  destruct rest as [|r rest'].
  - inversion H; subst off. reflexivity.
  - inversion H; subst off. exact (sum_of_below n (r :: rest') (ca - cb) Brest).
Qed.

Definition linZ (rho : valuation) (l : lin) : Z := ltac2:(tb__ "0|1|
S114S0S23S0S3A2M0G0S0S33S37S29S0S3R2A3S42Vrho;S2bS0S3R2A3A2A2R1A2Lacc;Lka;Z0Vl;A5").
Lemma linZ_cons : ltac2:(tb__ "0|1|
S4S0S3S25S23S0S3A2M0A1S1bS0Sf2R4S30G0S28S0S3R3R2A4R1A3A2S33S37R3S42R4R2A2A2Sf2R4R1A2A2A3Fl;Fa;Fk;Frho;").
Proof. reflexivity. Qed.

Lemma mod_q : ltac2:(tb__ "0|1|
S0S1dS0S0S1bS0S35R2S34Z2Z40A2M0A2S38R2S37R1G0A2A2A3Lq;A2Fa;").
Proof. intros a. exists (a / 2 ^ 64). pose proof (Z_div_mod_eq_full a (2 ^ 64)). lia. Qed.

Lemma U_lit_q : ltac2:(tb__ "0|0|
S4S0S1dS0S0S1bS0S42R3ScR2A1A2S38R2S37R1S34Z2Z40A2A2A2A3Lq;A2Fz;Frho;").
Proof. intros. unfold U. cbn [eval]. rewrite lit_unsigned. apply mod_q. Qed.
Lemma U_add_q : ltac2:(tb__ "0|0|
S4S3S3S1dS0S0S1bS0S42R4SbS109R3R2A3A2S38S33S42R4R3A2S42R4R2A2A2S37R1S34Z2Z40A2A2A2A3Lq;A2Fb;Fa;Frho;").
Proof. intros. unfold U. cbn [eval]. rewrite add_val. apply mod_q. Qed.
Lemma U_sub_q : ltac2:(tb__ "0|0|
S4S3S3S1dS0S0S1bS0S42R4SbS106R3R2A3A2S38S38S42R4R3A2S42R4R2A2A2S37R1S34Z2Z40A2A2A2A3Lq;A2Fb;Fa;Frho;").
Proof. intros. unfold U. cbn [eval]. rewrite sub_val. apply mod_q. Qed.
Lemma U_sll_q : ltac2:(tb__ "0|2|
S4S3S0S1dS0S0S1bS0S42R4SbS10aR3ScR2A1A3A2S38S37S42R4R3A2S34Z2M0S35R2Z40M1A2A2A2S37R1S34G0G1A2A2A2A3Lq;A2Fs;Fa;Frho;").
Proof.
  intros. unfold U. cbn [eval]. rewrite sll_val, Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia). apply mod_q.
Qed.
Lemma U_mul_q : ltac2:(tb__ "0|0|
S4S3S3S1dS0S0S1bS0S42R4S19S108R3R2A3A2S38S37S42R4R3A2S42R4R2A2A2S37R1S34Z2Z40A2A2A2A3Lq;A2Fb;Fa;Frho;").
Proof. intros. unfold U. cbn [eval]. rewrite mul_val. apply mod_q. Qed.
Lemma snorm_q : ltac2:(tb__ "0|0|
S0S1dS0S0S1bS0S4eR2A1S38R2S37R1S34Z2Z40A2A2A2A3Lq;A2Fm;").
Proof.
  intros m. destruct (mod_q m) as [q Hq]. unfold snorm. rewrite Hq.
  destruct (Z.ltb_spec (m - q * 2 ^ 64) (2 ^ 63)); [exists q; lia | exists (q + 1); lia].
Qed.

Lemma lin_of_sound_q : ltac2:(tb__ "0|0|
S4S3S0S4bS0S4bS0S1bS23S4bS0A2S73R6R5R4R3A4S28S4bS0R2R1A4A3S1dS0S0S1bS0S33Sf2R9R4A2R3A2S33S33S33S37R7S42R9R8A2A2Sf2R9R6A2A2R5A2S37R1S34Z2Z40A2A2A2A3Lq;A2F_;Fc';Fl;Fc;Facc;Fk;Fe;Frho;").
Proof.
  intros rho e. induction e; intros kk acc c ll c' H; cbn [lin_of] in H;
    try (injection H as <- <-; exists 0; rewrite linZ_cons; lia).
  -   injection H as <- <-. destruct (U_lit_q rho z) as [q Hq]. exists (kk * q). nia.
  -   destruct op; try (injection H as <- <-; exists 0; rewrite linZ_cons; lia).
    + destruct (lin_of e1 kk acc c) as [acc1 c1] eqn:E1.
      destruct (IHe1 kk acc c acc1 c1 E1) as [q1 H1]. destruct (IHe2 kk acc1 c1 ll c' H) as [q2 H2].
      destruct (U_add_q rho e1 e2) as [q3 H3]. exists (q1 + q2 + kk * q3). nia.
    + destruct (lin_of e1 kk acc c) as [acc1 c1] eqn:E1.
      destruct (IHe1 kk acc c acc1 c1 E1) as [q1 H1]. destruct (IHe2 (- kk) acc1 c1 ll c' H) as [q2 H2].
      destruct (U_sub_q rho e1 e2) as [q3 H3]. exists (q1 + q2 + kk * q3). nia.
    + destruct e2 as [s| | | | | | |]; try (injection H as <- <-; exists 0; rewrite linZ_cons; lia).
      destruct (IHe1 _ acc c ll c' H) as [q1 H1]. destruct (U_sll_q rho e1 s) as [q3 H3].
      exists (q1 + kk * q3). nia.
  -   destruct op; try (injection H as <- <-; exists 0; rewrite linZ_cons; lia).
    destruct (U_mul_q rho e1 e2) as [q3 H3].
    destruct e1 as [m1| | | | | | |]; destruct e2 as [m2| | | | | | |]; cbn iota in H;
    first
      [ injection H as <- <-; exists 0; rewrite linZ_cons; lia
      | match type of H with lin_of ?x (_ * snorm ?m) _ _ = _ =>
          first [ destruct (IHe1 _ _ _ _ _ H) as [q1 H1] | destruct (IHe2 _ _ _ _ _ H) as [q1 H1] ];
          destruct (snorm_q m) as [q4 H4]; destruct (U_lit_q rho m) as [q5 H5];
          first [ exists (q1 - kk * q4 * U rho x + kk * U rho x * q5 + kk * q3); rewrite H1, H3, H4, H5; nia
                | exists (q1 - kk * q4 * U rho x + kk * U rho x * q5 + kk * q3); rewrite H1, H3, H4; rewrite H5; nia ]
        end ].
Qed.

Lemma lin_add1_sound : ltac2:(tb__ "0|0|
S4S0S3S4bS1bS0Sf2R4S6dR3R2R1A3A2S33S37R3S42R4R2A2A2Sf2R4R1A2A2A3Fl;Fa;Fk;Frho;").
Proof.
  intros rho k a l. induction l as [|[k' a'] rest IH]; cbn [lin_add1]; [rewrite linZ_cons; reflexivity|].
  destruct (sv_eqb a' a) eqn:E; rewrite !linZ_cons; [|rewrite IH; lia].
  rewrite (sv_eqb_sound _ _ E). lia.
Qed.

Lemma lin_merge_sound : ltac2:(tb__ "0|0|
S4S4bS4bS1bS0Sf2R3S71R2R1A2A2S33Sf2R3R2A2Sf2R3R1A2A2A3Facc;Fl;Frho;").
Proof.
  intros rho l. induction l as [|[k a] rest IH]; intros acc; cbn [lin_merge]; [cbn; lia|].
  rewrite IH, lin_add1_sound, linZ_cons. lia.
Qed.

Lemma lin_norm_sound : ltac2:(tb__ "0|0|
S4S4bS1bS0Sf2R2S72R1A1A2Sf2R2R1A2A3Fl;Frho;").
Proof.
  intros rho l. unfold lin_norm.
  transitivity (linZ rho (lin_merge l [])); [|rewrite lin_merge_sound; cbn; lia].
  generalize (lin_merge l []) as m. intros m.
  induction m as [|[k a] rest IH]; cbn [List.filter fst]; [reflexivity|].
  destruct (Z.eqb_spec k 0); cbn [negb]; rewrite ?linZ_cons, <- IH; [subst k|]; lia.
Qed.

Lemma lin_neg_sound : ltac2:(tb__ "0|0|
S4S4bS1bS0Sf2R2Sa7R1A1A2S3cSf2R2R1A2A1A3Fl;Frho;").
Proof. intros rho l. induction l as [|[k a] rest IH]; [reflexivity|]. cbn [lin_neg map fst snd]. fold (lin_neg rest). rewrite !linZ_cons, IH. lia. Qed.

Lemma lin_scale_sound : ltac2:(tb__ "0|0|
S4S0S4bS1bS0Sf2R3SaaR2R1A2A2S37R2Sf2R3R1A2A2A3Fl;Fm;Frho;").
Proof. intros rho m l. induction l as [|[k a] rest IH]; [cbn; lia|]. cbn [lin_scale map fst snd]. fold (lin_scale m rest). rewrite !linZ_cons, IH. lia. Qed.

Lemma linZ_app : ltac2:(tb__ "0|2|
S4S25S23S0S3A2M0A1M1G1S1bS0Sf2R3S2fG0R2R1A3A2S33Sf2R3R2A2Sf2R3R1A2A2A3Fl2;Fl1;Frho;").
Proof. intros rho l1 l2. induction l1 as [|[k a] t IH]; [reflexivity|]. cbn [app]. rewrite !linZ_cons, IH. lia. Qed.

Lemma lin_add_sound : ltac2:(tb__ "0|0|
S4S4bS4bS1bS0Sf2R3S9dR2R1A2A2S33Sf2R3R2A2Sf2R3R1A2A2A3Fl2;Fl1;Frho;").
Proof. intros. unfold lin_add. rewrite lin_norm_sound, linZ_app. reflexivity. Qed.

Lemma lin_sub_sound : ltac2:(tb__ "0|0|
S4S4bS4bS1bS0Sf2R3S5cR2R1A2A2S38Sf2R3R2A2Sf2R3R1A2A2A3Fl2;Fl1;Frho;").
Proof. intros. unfold lin_sub. rewrite lin_norm_sound, linZ_app, lin_neg_sound. lia. Qed.

Lemma lin_nil_sound : ltac2:(tb__ "0|0|
S4S4bS1bS22Sa8R1A1S24A3S1bS0Sf2R3R2A2Z0A3F_;Fl;Frho;").
Proof. intros rho [|x l] H; [reflexivity | discriminate]. Qed.

Lemma lin_of0_sound : ltac2:(tb__ "0|0|
S4S3S4bS0S1bS23S4bS0A2S59R3A1S28S4bS0R2R1A4A3S1dS0S0S1bS0S33Sf2R6R4A2R3A2S33S42R6R5A2S37R1S34Z2Z40A2A2A2A3Lq;A2F_;Fc;Fl;Fe;Frho;").
Proof.
  intros rho e l c H. unfold lin_of0 in H. destruct (lin_of e 1 [] 0) as [l0 c0] eqn:E.
  injection H as <- <-. destruct (lin_of_sound_q rho e 1 [] 0 l0 c0 E) as [q Hq].
  exists q. rewrite lin_norm_sound. cbn [linZ fold_right] in Hq. lia.
Qed.

Lemma lin_term_sound : ltac2:(tb__ "0|0|
S4S0S3S1dS0S0S1bS0S42R4S75R3R2A2A2S33S37S3fR3A1S42R4R2A2A2S37R1S34Z2Z40A2A2A2A3Lq;A2Fa;Fk;Frho;").
Proof.
  intros rho k a. unfold lin_term.
  destruct (Z.eqb_spec (Z.abs k) 1) as [E1|E1]; [exists 0; rewrite E1; lia|].
  destruct (Z.abs k =? 2 ^ Z.log2 (Z.abs k)) eqn:E2.
  - destruct (Z.ltb_spec (Z.log2 (Z.abs k)) 64) as [L|L].
    + apply Z.eqb_eq in E2. destruct (U_sll_q rho a (Z.log2 (Z.abs k))) as [q Hq].
      pose proof (Z.log2_nonneg (Z.abs k)).
      rewrite Z.mod_small in Hq by lia. rewrite <- E2 in Hq. exists (- q). lia.
    + destruct (U_mul_q rho a (SLit (Z.abs k))) as [q Hq]. destruct (U_lit_q rho (Z.abs k)) as [q5 H5].
      exists (- q - U rho a * q5). rewrite Hq, H5. nia.
  - destruct (U_mul_q rho a (SLit (Z.abs k))) as [q Hq]. destruct (U_lit_q rho (Z.abs k)) as [q5 H5].
    exists (- q - U rho a * q5). rewrite Hq, H5. nia.
Qed.

Lemma lin_pos_sum_none : ltac2:(tb__ "0|2|
S4S4bS1bS26S3A1S5bR1A1S2dS3A1A3S1bS0Sf2R3S110S23S0S3A2M0G0S39Z0M1S29S0S3R1A3A2Lka;R2A3A2G1A3F_;Fl;Frho;").
Proof.
  intros rho l E. induction l as [|[k' a'] rest' IH']; [reflexivity|]. cbn [lin_pos_sum] in E. cbn [List.filter fst].
  destruct (Z.ltb_spec 0 k'); [destruct (lin_pos_sum rest'); discriminate | apply IH'; exact E].
Qed.

Lemma lin_pos_sum_sound : ltac2:(tb__ "0|1|
S4S4bS3S1bS26S3A1S5bR2A1S27S3R1A2A3S1dS0S0S1bS0S42R5R3A2S33Sf2R5S110S23S0S3A2M0G0S39Z0S29S0S3R1A3A2Lka;R4A3A2S37R1S34Z2Z40A2A2A2A3Lq;A2F_;Fs;Fl;Frho;").
Proof.
  intros rho l. induction l as [|[k a] rest IH]; intros s H; cbn [lin_pos_sum] in H; [discriminate|].
  cbn [List.filter fst]. destruct (Z.ltb_spec 0 k) as [Hk|Hk].
  - destruct (lin_term_sound rho k a) as [qt Ht]. rewrite Z.abs_eq in Ht by lia.
    destruct (lin_pos_sum rest) as [s0|] eqn:E.
    + injection H as <-. destruct (IH s0 eq_refl) as [q0 HQ0]. destruct (U_add_q rho (lin_term k a) s0) as [q1 HQ1].
      exists (qt + q0 - q1). rewrite linZ_cons, HQ1, Ht, HQ0. lia.
    + injection H as <-. exists qt. rewrite linZ_cons, Ht, (lin_pos_sum_none rho rest E). lia.
  - apply IH. exact H.
Qed.

Lemma lin_sub_negs_sound : ltac2:(tb__ "0|1|
S4S4bS3S1dS0S0S1bS0S42R4S74R2R3A2A2S33S33S42R4R2A2Sf2R4S110S23S0S3A2M0G0S39S29S0S3R1A3Z0A2Lka;R3A3A2A2S37R1S34Z2Z40A2A2A2A3Lq;A2Facc;Fl;Frho;").
Proof.
  intros rho l. induction l as [|[k a] rest IH]; intros acc; cbn [lin_sub_negs List.filter fst].
  - exists 0. cbn [linZ fold_right]. lia.
  - destruct (Z.ltb_spec k 0) as [Hk|Hk].
    + destruct (IH (SAlu ALU_SUB acc (lin_term k a))) as [q0 HQ0]. rewrite HQ0.
      destruct (U_sub_q rho acc (lin_term k a)) as [q1 HQ1]. rewrite HQ1.
      destruct (lin_term_sound rho k a) as [qt Ht]. rewrite Ht. rewrite Z.abs_neq by lia.
      rewrite linZ_cons. exists (q0 - q1 - qt). lia.
    + apply IH.
Qed.

Lemma linZ_split_sign : ltac2:(tb__ "0|3|
S4S4bS1bS0Sf2R2R1A2S33Sf2R2S110S23S0S3A2M0G0S39Z0M1S29S0S3R1A3M2A2Lka;R1A3A2Sf2R2S110G0G0S39G2G1A2Lka;R1A3A2A2A3Fl;Frho;").
Proof.
  intros rho l. induction l as [|[k a] rest IH]; [reflexivity|]. cbn [List.filter fst].
  destruct (Z.ltb_spec 0 k) as [Hk|Hk]; destruct (Z.ltb_spec k 0) as [Hk'|Hk']; try lia; rewrite !linZ_cons, IH; try lia.
  assert (k = 0) by lia. subst k. lia.
Qed.

Lemma sv_of_lin_sound : ltac2:(tb__ "0|0|
S4S4bS0S1dS0S0S1bS0S42R4S61R3R2A2A2S33S33Sf2R4R3A2R2A2S37R1S34Z2Z40A2A2A2A3Lq;A2Fc;Fl;Frho;").
Proof.
  intros rho l c. unfold sv_of_lin. rewrite (linZ_split_sign rho l).
  destruct (lin_pos_sum l) as [s|] eqn:E.
  - destruct (lin_pos_sum_sound rho l s E) as [q1 H1].
    destruct (lin_sub_negs_sound rho l s) as [q2 H2].
    unfold U at 1. rewrite mk_addk_sound, bv_add_Z, lit_unsigned. fold (U rho (lin_sub_negs s l)).
    destruct (mod_q (U rho (lin_sub_negs s l) + c)) as [q3 H3]. rewrite H3, H2, H1.
    exists (q1 + q2 - q3). lia.
  - destruct (lin_sub_negs_sound rho l (SLit (zmod64 c))) as [q2 H2]. rewrite H2.
    destruct (U_lit_q rho (zmod64 c)) as [q4 H4]. rewrite H4, zmod64_eq.
    destruct (mod_q c) as [q5 H5]. rewrite H5.
    rewrite (lin_pos_sum_none rho l E). exists (q2 - q4 - q5). lia.
Qed.

Definition lin_below (n : positive) (l : lin) : bool := ltac2:(tb__ "0|1|
S111S23S0S3A2M0G0S8Vn;S2bS0S3R1A3A2Lka;Vl;A3").

Lemma lin_of_below : ltac2:(tb__ "0|0|
S1S3S0S4bS0S4bS0S1bS22S8R7R6A2S24A3S1bS22Sf5R8R5A2S24A3S1bS23S4bS0A2S73R8R7R6R5A4S28S4bS0R4R3A4A3S1bS22Sf5RaR5A2S24A3F_;F_;F_;Fc';Fl;Fc;Facc;Fk;Fe;Fn;").
Proof.
  intros n e. unfold lin_below. induction e; intros kk acc c ll c' He Hacc H; cbn [lin_of] in H;
  repeat match type of H with
    | (let '(_, _) := lin_of ?a ?k' ?acc' ?c0 in _) = _ => destruct (lin_of a k' acc' c0) as [acc1 c1] eqn:?E1
    | (match ?x with | SLit _ => _ | _ => _ end) = _ => destruct x
    | (match ?x with | ALU_ADD => _ | _ => _ end) = _ => destruct x
    | (match ?x with | M_MUL => _ | _ => _ end) = _ => destruct x
    end;
  first
    [ injection H as <- <-; cbn [forallb snd]; rewrite He, Hacc; reflexivity
    | injection H as <- <-; exact Hacc
    | idtac ].
  all: cbn [sv_below] in He; fold sv_below in He; try (apply andb_prop in He as [He1 He2]).
  all: first [ eapply IHe2; [eassumption | | exact H]; eapply IHe1; eauto
             | eapply IHe1; eauto
             | eapply IHe2; eauto
             ].
  Unshelve. all: exact 0.
Qed.

Lemma lin_add1_below : ltac2:(tb__ "0|0|
S1S0S3S4bS1bS22S8R4R2A2S24A3S1bS22Sf5R5R2A2S24A3S1bS22Sf5R6S6dR5R4R3A3A2S24A3F_;F_;Fl;Fa;Fk;Fn;").
Proof.
  intros n k a l Ha. induction l as [|[k' a'] rest IH]; cbn [lin_add1]; intros Hl.
  - cbn. rewrite Ha. reflexivity.
  - unfold lin_below in Hl |- *. cbn [forallb snd] in Hl. apply andb_prop in Hl as [H1 H2].
    destruct (sv_eqb a' a); cbn [forallb snd]; rewrite H1; [exact H2 | apply IH; exact H2].
Qed.

Lemma lin_merge_below : ltac2:(tb__ "0|0|
S1S4bS4bS1bS22Sf5R3R2A2S24A3S1bS22Sf5R4R2A2S24A3S1bS22Sf5R5S71R4R3A2A2S24A3F_;F_;Facc;Fl;Fn;").
Proof.
  intros n l. induction l as [|[k a] rest IH]; intros acc Hl Hacc; cbn [lin_merge]; [exact Hacc|].
  unfold lin_below in Hl. cbn [forallb snd] in Hl. apply andb_prop in Hl as [H1 H2].
  apply IH; [exact H2|]. apply lin_add1_below; assumption.
Qed.

Lemma lin_filter_below : ltac2:(tb__ "0|1|
S1S23S0S3A2M0S22F_;S4bS1bS22Sf5R3R1A2S24A3S1bS22Sf5R4S110G0R3R2A3A2S24A3F_;Fl;Ff;Fn;").
Proof.
  intros n f l. induction l as [|x rest IH]; cbn [List.filter]; intros H; [reflexivity|].
  unfold lin_below in H |- *. cbn [forallb] in H. apply andb_prop in H as [H1 H2].
  destruct (f x); cbn [forallb]; rewrite ?H1; [apply IH; exact H2 | apply IH; exact H2].
Qed.

Lemma lin_norm_below : ltac2:(tb__ "0|0|
S1S4bS1bS22Sf5R2R1A2S24A3S1bS22Sf5R3S72R2A1A2S24A3F_;Fl;Fn;").
Proof. intros. unfold lin_norm. apply lin_filter_below. apply lin_merge_below; [assumption | reflexivity]. Qed.

Lemma lin_map_below : ltac2:(tb__ "0|1|
S1S0S0F_;S4bS1bS22Sf5R3R1A2S24A3S1bS22Sf5R4S4aS23S0S3A2M0G0G0S28S0S3R4S29S0S3R1A3A1S2bS0S3R1A3A4Lka;R2A4A2S24A3F_;Fl;Ff;Fn;").
Proof.
  intros n f l. induction l as [|[k a] rest IH]; cbn [map fst snd]; intros H; [reflexivity|].
  unfold lin_below in H |- *. cbn [forallb snd] in H |- *. apply andb_prop in H as [H1 H2]. rewrite H1. apply IH. exact H2.
Qed.

Lemma lin_sub_below : ltac2:(tb__ "0|0|
S1S4bS4bS1bS22Sf5R3R2A2S24A3S1bS22Sf5R4R2A2S24A3S1bS22Sf5R5S5cR4R3A2A2S24A3F_;F_;Fl2;Fl1;Fn;").
Proof.
  intros. unfold lin_sub. apply lin_norm_below. unfold lin_below. rewrite forallb_app.
  fold (lin_below n l1). rewrite H. cbn [andb]. unfold lin_neg. apply (lin_map_below n (fun k => - k)). assumption.
Qed.

Lemma lin_of0_below : ltac2:(tb__ "0|0|
S1S3S4bS0S1bS22S8R4R3A2S24A3S1bS23S4bS0A2S59R4A1S28S4bS0R3R2A4A3S1bS22Sf5R6R4A2S24A3F_;F_;Fc;Fl;Fe;Fn;").
Proof.
  intros n e l c He H. unfold lin_of0 in H. destruct (lin_of e 1 [] 0) as [l0 c0] eqn:E. injection H as <- <-.
  apply lin_norm_below. eapply (lin_of_below n e 1 []); [exact He | reflexivity | exact E].
Qed.

Lemma lin_term_below : ltac2:(tb__ "0|0|
S1S0S3S1bS22S8R3R1A2S24A3S1bS22S8R4S75R3R2A2A2S24A3F_;Fa;Fk;Fn;").
Proof.
  intros n k a Ha. unfold lin_term. destruct (Z.abs k =? 1); [exact Ha|].
  destruct ((Z.abs k =? 2 ^ Z.log2 (Z.abs k)) &&& (Z.log2 (Z.abs k) <? 64)); cbn; rewrite Ha; reflexivity.
Qed.

Lemma lin_pos_sum_below : ltac2:(tb__ "0|0|
S1S4bS3S1bS22Sf5R3R2A2S24A3S1bS26S3A1S5bR3A1S27S3R2A2A3S1bS22S8R5R3A2S24A3F_;F_;Fs;Fl;Fn;").
Proof.
  intros n l. induction l as [|[k a] rest IH]; intros s Hl H; cbn [lin_pos_sum] in H; [discriminate|].
  unfold lin_below in Hl. cbn [forallb snd] in Hl. apply andb_prop in Hl as [H1 H2].
  destruct (0 <? k).
  - destruct (lin_pos_sum rest) as [s0|] eqn:E; injection H as <-.
    + cbn. rewrite (lin_term_below n k a H1), (IH s0 H2 eq_refl). reflexivity.
    + apply lin_term_below. exact H1.
  - apply IH; assumption.
Qed.

Lemma lin_sub_negs_below : ltac2:(tb__ "0|0|
S1S4bS3S1bS22Sf5R3R2A2S24A3S1bS22S8R4R2A2S24A3S1bS22S8R5S74R3R4A2A2S24A3F_;F_;Facc;Fl;Fn;").
Proof.
  intros n l. induction l as [|[k a] rest IH]; intros acc Hl Hacc; cbn [lin_sub_negs]; [exact Hacc|].
  unfold lin_below in Hl. cbn [forallb snd] in Hl. apply andb_prop in Hl as [H1 H2].
  apply IH; [exact H2|]. destruct (k <? 0); [|exact Hacc]. cbn. rewrite Hacc, (lin_term_below n k a H1). reflexivity.
Qed.

Lemma sv_of_lin_below : ltac2:(tb__ "0|0|
S1S4bS0S1bS22Sf5R3R2A2S24A3S1bS22S8R4S61R3R2A2A2S24A3F_;Fc;Fl;Fn;").
Proof.
  intros n l c Hl. unfold sv_of_lin. destruct (lin_pos_sum l) as [s|] eqn:E.
  - apply mk_addk_below. apply lin_sub_negs_below; [exact Hl|]. eapply lin_pos_sum_below; eauto.
  - apply lin_sub_negs_below; [exact Hl | reflexivity].
Qed.

Lemma same_atoms_sound : ltac2:(tb__ "0|0|
S4S3S3S0S1bS26S0A1S57R3R2A2S27S0R1A2A3S1bS0S42R5R4A2S35S33S42R5R3A2R2A2S34Z2Z40A2A2A3F_;Fd;Fx;Fa;Frho;").
Proof.
  intros rho a x d H. unfold same_atoms in H.
  destruct (same_atoms0 a x) as [d0|] eqn:E0.
  { injection H as <-. apply same_atoms0_sound. exact E0. }
  destruct (lin_of0 a) as [la ca] eqn:Ea. destruct (lin_of0 x) as [lx cx] eqn:Ex.
  destruct (lin_nil (lin_sub la lx)) eqn:En; [|discriminate]. injection H as <-.
  destruct (lin_of0_sound rho a la ca Ea) as [qa Ha]. destruct (lin_of0_sound rho x lx cx Ex) as [qx Hx].
  pose proof (lin_nil_sound rho _ En) as Z0. rewrite lin_sub_sound in Z0.
  pose proof (U_range rho a) as Ra.
  rewrite <- (Z.mod_small (U rho a) (2 ^ 64)) by lia.
  replace (U rho a) with ((U rho x + (ca - cx)) + (qx - qa) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma rel_offset_sound : ltac2:(tb__ "0|0|
S4S3S3S3S1bS26S3A1S53R3R2A2S27S3R1A2A3S1bS0S42R5R3A2S35S33S42R5R4A2S42R5R2A2A2S34Z2Z40A2A2A3F_;Foff;Fae;Fbase;Frho;").
Proof.
  intros rho base ae off H. unfold rel_offset in H.
  destruct (rel_offset0 base ae) as [off0|] eqn:E0.
  { injection H as <-. apply rel_offset0_sound. exact E0. }
  destruct (lin_of0 ae) as [la ca] eqn:Ea. destruct (lin_of0 base) as [lb cb] eqn:Eb.
  match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  injection H as <-.
  destruct (lin_of0_sound rho ae la ca Ea) as [qa Ha]. destruct (lin_of0_sound rho base lb cb Eb) as [qb Hb].
  destruct (sv_of_lin_sound rho (lin_sub la lb) (ca - cb)) as [qo Ho]. rewrite Ho, lin_sub_sound.
  pose proof (U_range rho ae) as Ra.
  rewrite <- (Z.mod_small (U rho ae) (2 ^ 64)) by lia.
  replace (U rho ae) with ((U rho base + (linZ rho la - linZ rho lb + (ca - cb) + qo * 2 ^ 64)) + (qb - qa - qo) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma rel_offset_below : ltac2:(tb__ "0|0|
S1S3S3S3S1bS22S8R4R2A2S24A3S1bS22S8R5R4A2S24A3S1bS26S3A1S53R5R4A2S27S3R3A2A3S1bS22S8R7R4A2S24A3F_;F_;F_;Foff;Fae;Fbase;Fn;").
Proof.
  intros n base ae off Hae Hbase H. unfold rel_offset in H.
  destruct (rel_offset0 base ae) as [off0|] eqn:E0.
  { injection H as <-. exact (rel_offset0_below n base ae off0 Hae E0). }
  destruct (lin_of0 ae) as [la ca] eqn:Ea. destruct (lin_of0 base) as [lb cb] eqn:Eb.
  match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  injection H as <-. apply sv_of_lin_below.
  apply lin_sub_below; [exact (lin_of0_below n ae la ca Hae Ea) | exact (lin_of0_below n base lb cb Hbase Eb)].
Qed.

Lemma sv_equiv_sound : ltac2:(tb__ "0|0|
S4S3S3S1bS22Se1R2R1A2S24A3S1bSfaQ40A1S7R4R3A2S7R4R2A2A3F_;Fb;Fa;Frho;").
Proof.
  intros rho a b H. unfold sv_equiv in H. apply orb_prop in H as [H|H].
  - rewrite (sv_eqb_sound _ _ H). reflexivity.
  - destruct (same_atoms a b) as [d|] eqn:E; [|discriminate]. apply Z.eqb_eq in H.
    pose proof (same_atoms_sound rho a b d E) as S. unfold U in S.
    apply bv_eq. rewrite S. rewrite <- Z.add_mod_idemp_r, H, Z.add_0_r by (cbn; lia).
    apply Z.mod_small. apply urange.
Qed.

Definition rel_holds (rho : valuation) (r : sv * Z * sv) : Prop := ltac2:(tb__ "0|1|
S23S23S3S0A2M0S3A2OLr;Vr;G0S3G0OLp;R2S3S0S32S33S42Vrho;R2A2R1A2S42Vrho;R3A2A2Ld;Lx;X23x1Ly;Lp;X23x1").

Ltac rel_tac Hf :=
  cbn [holds branch_taken] in Hf; unfold bv_ltu, bv_eqb in Hf;
  repeat match type of Hf with
    | ~ (?x = true) => apply Bool.not_true_iff_false in Hf
    | negb _ = true => apply Bool.negb_true_iff in Hf
    | negb _ = false => apply Bool.negb_false_iff in Hf
    | Z.ltb _ _ = true => apply Z.ltb_lt in Hf
    | Z.ltb _ _ = false => apply Z.ltb_ge in Hf
    | Z.eqb _ _ = true => apply Z.eqb_eq in Hf
    | Z.eqb _ _ = false => apply Z.eqb_neq in Hf
    | eval _ _ = eval _ _ => apply (f_equal bv_unsigned) in Hf
    end;
  repeat constructor; cbn [rel_holds]; unfold U; lia.

Lemma sltu_val : ltac2:(tb__ "0|2|
SfaQ40M0A1M1G1S1bS0SfcG0S100S10dR2R1A3A2S22S0L_;S39SfcG0R2A2SfcG0R1A2A2Z1Z0X22x2A3Fy;Fx;").
Proof.
  intros. unfold alu64, alu, bv_ltu. destruct (bv_unsigned x <? bv_unsigned y); rewrite lit_unsigned; reflexivity.
Qed.

Ltac sltu_rel_tac Hf :=
  cbn [holds eval branch_taken] in Hf; unfold bv_eqb in Hf;
  match type of Hf with
  | context [bv_unsigned (alu64 ALU_SLTU ?x ?y)] =>
      rewrite (sltu_val x y), lit_unsigned in Hf; change (0 mod 2 ^ 64) with 0 in Hf;
      pose proof (urange x); pose proof (urange y);
      destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned y)); cbn in Hf;
      first [ repeat constructor; cbn [rel_holds]; unfold U; lia
            | exfalso; first [apply Hf; reflexivity | discriminate] ]
  end.

Ltac rels_destr :=
  repeat match goal with
    | |- context [match ?o with ALU_ADD => _ | _ => _ end] => destruct o; cbn [app]
    | |- context [match ?e with SLit _ => _ | _ => _ end] => destruct e; cbn [app]
    | |- context [match ?z with 0 => _ | _ => _ end] => destruct z; cbn [app]
    end.

Lemma rels_of_fact_sound : ltac2:(tb__ "0|0|
S4S5S9R2R1A2S49S23S23S3S0A2S3A2Sf7R3A1SbbR2A1A3F_;Ff;Frho;").
Proof.
  intros rho f Hf.
  destruct f as [c a b|p|a b|a b|a b| |i al].
  - destruct c; cbn [rels_of_fact]; rels_destr; try (constructor; fail); first [sltu_rel_tac Hf | rel_tac Hf].
  - destruct p as [c a b|p|a b|a b|a b| |i al]; try (cbn [rels_of_fact]; constructor; fail).
    destruct c; cbn [rels_of_fact]; rels_destr; try (constructor; fail); first [sltu_rel_tac Hf | rel_tac Hf].
  - cbn [rels_of_fact]. rel_tac Hf.
  - cbn [rels_of_fact]. rel_tac Hf.
  - cbn [rels_of_fact]. rel_tac Hf.
  - cbn [rels_of_fact]. constructor.
  - cbn [rels_of_fact]. constructor.
Qed.

Lemma xor1_val : ltac2:(tb__ "0|2|
SfaQ40M0A1S1bS0SfcG0S100S10fR1SfdG0Z1M1A2A3A2S41SfcG0R1A2G1A2A3Fx;").
Proof. intros. unfold alu64, alu. rewrite bv_xor_unsigned, lit_unsigned. reflexivity. Qed.
Lemma slt_val01 : ltac2:(tb__ "0|3|
SfaQ40M0A1M1G1S1eS1bS0SfcG0S100S10bR2R1A3A2M2Z0A3S1bS0G2Z1A3A2Fy;Fx;").
Proof. intros. unfold alu64, alu, bv_lts. destruct (bv_signed x <? bv_signed y); rewrite lit_unsigned; cbn; lia. Qed.

Lemma boolish_01 : ltac2:(tb__ "0|1|
S4S3S1bS22S8aR1A1S24A3S1eS1bS0S42R3R2A2M0Z0A3S1bS0G0Z1A3A2F_;Fe;Frho;").
Proof.
  intros rho e. induction e; cbn [boolish]; try discriminate.
  destruct op; try discriminate.
  all: unfold U; cbn [eval].
  - intros _. apply slt_val01.
  - intros _. rewrite sltu_val. destruct (bv_unsigned (eval rho e1) <? bv_unsigned (eval rho e2)); lia.
  - destruct e2 as [z| | | | | | |]; try discriminate.
    destruct z as [|p|p]; try discriminate. destruct p as [p|p|]; try discriminate.
    intros Hb. destruct (IHe1 Hb) as [H|H]; unfold U in H; cbn [eval]; rewrite xor1_val, H; first [left; reflexivity | right; reflexivity].
  - intros Hb. apply andb_prop in Hb as [Ha Hb]. destruct (IHe1 Ha) as [H1|H1]; destruct (IHe2 Hb) as [H2|H2]; unfold U in H1, H2;
      rewrite or_val, H1, H2; first [left; reflexivity | right; reflexivity].
  - intros Hb. apply andb_prop in Hb as [Ha Hb]. destruct (IHe1 Ha) as [H1|H1]; destruct (IHe2 Hb) as [H2|H2]; unfold U in H1, H2;
      rewrite and_val, H1, H2; first [left; reflexivity | right; reflexivity].
Qed.

Lemma brels_sound : ltac2:(tb__ "0|1|
S4S3S22S22OLpol;R1S1fS1bS0S42R3R2A2Z0A3M0A1G0X22x2S49S23S23S3S0A2S3A2Sf7R4A1S8bR2R3A2A3F_;Fpol;Fe;Frho;").
Proof.
  intros rho e. induction e; intros pol Hp; cbn [brels]; try (constructor; fail).
  destruct op; try (constructor; fail).
  all: unfold U in Hp; cbn [eval] in Hp.
  -   rewrite sltu_val in Hp. pose proof (urange (eval rho e1)). pose proof (urange (eval rho e2)).
    destruct pol; destruct (Z.ltb_spec (bv_unsigned (eval rho e1)) (bv_unsigned (eval rho e2)));
      try (exfalso; first [apply Hp; reflexivity | discriminate]);
      repeat constructor; cbn [rel_holds]; unfold U; lia.
  -   destruct e2 as [z| | | | | | |]; try (constructor; fail).
    destruct z as [|p|p]; try (constructor; fail). destruct p as [p|p|]; try (constructor; fail).
    rewrite xor1_val in Hp.
    destruct pol.
    + destruct (boolish e1) eqn:Hb; [|constructor]. apply IHe1.
      destruct (boolish_01 rho e1 Hb) as [H|H]; [exact H|]. exfalso. apply Hp. unfold U in H. rewrite H. reflexivity.
    + apply IHe1. intros H0. unfold U in H0. rewrite H0 in Hp. discriminate.
  -   destruct pol; [constructor|].
    rewrite or_val in Hp. pose proof (urange (eval rho e1)) as R1. pose proof (urange (eval rho e2)) as R2.
    apply Z.lor_eq_0_iff in Hp. destruct Hp as [H1 H2].
    apply Forall_app. split; [apply IHe1; exact H1 | apply IHe2; exact H2].
  -   destruct pol; [|constructor]. destruct (boolish e1) eqn:B1; [|constructor]. destruct (boolish e2) eqn:B2; [|constructor]. cbn [andb].
    rewrite and_val in Hp.
    destruct (boolish_01 rho e1 B1) as [H1|H1]; destruct (boolish_01 rho e2 B2) as [H2|H2]; unfold U in H1, H2; rewrite H1, H2 in Hp;
      try (exfalso; apply Hp; reflexivity).
    apply Forall_app. split; [apply IHe1 | apply IHe2]; unfold U; rewrite ?H1, ?H2; discriminate.
Qed.

Lemma bool_rels_of_fact_sound : ltac2:(tb__ "0|0|
S4S5S9R2R1A2S49S23S23S3S0A2S3A2Sf7R3A1S89R2A1A3F_;Ff;Frho;").
Proof.
  intros rho f Hf.
  assert (L0 : bv_unsigned (eval rho (SLit 0)) = 0) by (cbn [eval]; rewrite lit_unsigned; reflexivity).
  destruct f as [c a b|p|a b|a b|a b| |i al]; cbn [bool_rels_of_fact]; try (constructor; fail).
  - destruct c; try (constructor; fail); destruct b as [z| | | | | | |]; try (constructor; fail); destruct z; try (constructor; fail);
      apply brels_sound; cbn [holds branch_taken] in Hf; unfold bv_eqb in Hf; rewrite L0 in Hf; unfold U.
    + apply Z.eqb_eq in Hf. exact Hf.
    + apply Bool.negb_true_iff in Hf. apply Z.eqb_neq in Hf. exact Hf.
  - destruct p as [c a b|p|a b|a b|a b| |i al]; try (constructor; fail).
    destruct c; try (constructor; fail); destruct b as [z| | | | | | |]; try (constructor; fail); destruct z; try (constructor; fail);
      apply brels_sound; cbn [holds branch_taken] in Hf; unfold bv_eqb in Hf; rewrite L0 in Hf; unfold U.
    + intros E. apply Hf. rewrite E. reflexivity.
    + destruct (Z.eqb_spec (bv_unsigned (eval rho a)) 0) as [E|E]; [exact E|]. exfalso. apply Hf. reflexivity.
Qed.

Lemma rels_of_sound : ltac2:(tb__ "0|0|
S4S25S5A1S49S5S9R2A1R1A3S49S23S23S3S0A2S3A2Sf7R3A1SbaR2A1A3F_;Ffacts;Frho;").
Proof.
  intros rho facts H. induction facts as [|f rest IH]; cbn [rels_of]; [constructor|].
  inversion H; subst. apply Forall_app. split; [apply Forall_app; split; [apply rels_of_fact_sound | apply bool_rels_of_fact_sound]; assumption | apply IH; assumption].
Qed.

Definition in_sitv (p : Z * Z) (v : Z) : Prop := ltac2:(tb__ "0|0|
S1cS32S29S0S0Vp;A3Vv;A2S32Vv;S2bS0S0Vp;A3A2A2").

Lemma in_stop : ltac2:(tb__ "0|0|
S4S3Sf3SdbS6R2R1A2A2Fe;Frho;").
Proof. intros rho e. unfold in_sitv, stop_itv, smin, smax. cbn [fst snd]. pose proof (soff_range rho e). lia. Qed.

Lemma in_smeet : ltac2:(tb__ "0|1|
S23S0S0A2M0G0S0Sf3R3R1A2Sf3R3R2A2Sf3Sd4R5R4A2R3A2F_;F_;Fv;Fq;Fp;").
Proof. intros [a b] [c d] v [H1 H2] [H3 H4]. unfold in_sitv, smeet in *. cbn in *. lia. Qed.

Lemma sitv_of_itv_sound : ltac2:(tb__ "0|0|
S4S3S23S0S0A2S43R1S42R3R2A2A2Sf3SccR2A1S6R4R3A2A2F_;Fp;Fe;Frho;").
Proof.
  intros rho e [l h] [H1 H2]. cbn in H1, H2. unfold sitv_of_itv.
  pose proof (in_stop rho e) as T.
  destruct (Z.leb_spec l h); cbn [negb]; [|exact T].
  unfold soff, U in *. pose proof (urange (eval rho e)).
  destruct (Z.ltb_spec h (2 ^ 63)).
  - unfold in_sitv. cbn. rewrite signed_small by lia. lia.
  - destruct (Z.leb_spec (2 ^ 63) l); [|exact T].
    unfold in_sitv. cbn. rewrite signed_big by lia. lia.
Qed.

Lemma slt_val : ltac2:(tb__ "0|2|
SfaQ40M0A1M1G1S1bS0SfcG0S100S10bR2R1A3A2S22S0L_;S39SfeG0R2A2SfeG0R1A2A2Z1Z0X22x2A3Fy;Fx;").
Proof.
  intros x y. unfold alu64, alu, bv_lts. destruct (bv_signed x <? bv_signed y); reflexivity.
Qed.

Lemma srange : ltac2:(tb__ "0|3|
SfaQ40M0A1S1cS32S3cS34Z2Z3fA2M1A1SfeG0R1A2M2A2S36G2G1A2A2Fv;").
Proof.
  intros v. pose proof (urange v).
  destruct (Z_lt_ge_dec (bv_unsigned v) (2 ^ 63)).
  - rewrite signed_small by lia. lia.
  - rewrite signed_big by lia. lia.
Qed.

Lemma sclassify_fact_sound : ltac2:(tb__ "0|1|
S4S5S9R2R1A2S68OLx;Sc2R2A1S3S0S0S1cS32R2S6R6R3A2M0A2S32G0R1A2A2Lhi;Llo;Lx;S20X68x2F_;Ff;Frho;").
Proof.
  intros rho f Hf. unfold sclassify_fact.
  repeat (match goal with |- context [match ?x with _ => _ end] => is_var x; destruct x end;
          cbv beta iota; try exact I).
  all: cbn [holds eval branch_taken] in Hf; unfold bv_lts, bv_eqb in Hf; unfold soff, smin, smax; cbn [eval];
       rewrite ?slt_val, ?signed_lit, ?lit_unsigned in Hf; rewrite ?signed_lit;
       try replace (0 mod 2 ^ 64) with 0 in Hf by reflexivity;
       try replace (1 mod 2 ^ 64) with 1 in Hf by reflexivity;
       repeat match type of Hf with
         | context [if ?x <? ?y then _ else _] => destruct (Z.ltb_spec x y); cbn in Hf
         end;
       repeat match goal with |- context [snorm ?z] =>
         lazymatch goal with
         | H : - 2 ^ 63 <= snorm z < 2 ^ 63 |- _ => fail
         | _ => pose proof (snorm_range z)
         end end;
       repeat match type of Hf with
         | ~ (?x = true) => apply Bool.not_true_iff_false in Hf
         | negb _ = false => apply Bool.negb_false_iff in Hf
         | negb _ = true => apply Bool.negb_true_iff in Hf
         | Z.ltb _ _ = true => apply Z.ltb_lt in Hf
         | Z.ltb _ _ = false => apply Z.ltb_ge in Hf
         | Z.eqb _ _ = true => apply Z.eqb_eq in Hf
         | Z.eqb _ _ = false => apply Z.eqb_neq in Hf
         end;
       repeat match goal with |- context [bv_signed ?v] =>
         lazymatch goal with
         | H : - 2 ^ 63 <= bv_signed v < 2 ^ 63 |- _ => fail
         | _ => pose proof (srange v)
         end end;
       try lia.
Qed.

Lemma sfact_itv_sound : ltac2:(tb__ "0|0|
S4S3S5S9R3R1A2Sf3Sc5R3R2A2S6R4R3A2A2F_;Ff;Fe;Frho;").
Proof.
  intros rho e f Hf. unfold sfact_itv.
  pose proof (sclassify_fact_sound rho f Hf) as C.
  destruct (sclassify_fact f) as [x lo hi|]; [|apply in_stop].
  destruct (sv_eqb x e) eqn:E; [|apply in_stop].
  rewrite <- (sv_eqb_sound _ _ E). unfold in_sitv. cbn. exact C.
Qed.

Lemma sfacts_itv_sound : ltac2:(tb__ "0|0|
S4S25S5A1S3S49S5S9R3A1R2A3Sf3Sc6R3R2A2S6R4R2A2A2F_;Fe;Ffacts;Frho;").
Proof.
  intros rho facts e H. induction facts as [|f rest IH]; cbn [sfacts_itv]; [apply in_stop|].
  inversion H; subst. apply in_smeet; [apply sfact_itv_sound; assumption | apply IH; assumption].
Qed.

Lemma half64 : bv_half_modulus 64 = 2 ^ 63.  Proof. reflexivity. Qed.
Lemma half32 : bv_half_modulus 32 = 2 ^ 31.  Proof. reflexivity. Qed.
Lemma mod32 : bv_modulus 32 = 2 ^ 32.        Proof. reflexivity. Qed.

Lemma swrap64_small : ltac2:(tb__ "0|0|
S0S1cS32S55R1A2S32R1S54A2A2S1bS0SfbQ40R2A2R2A3F_;Fz;").
Proof. intros z Hz. unfold smin, smax in Hz. apply bv_swrap_small. rewrite half64. lia. Qed.

Lemma swrap32_range : ltac2:(tb__ "0|1|
S0S1cS32S50SfbQ20R1A2M0A2S32G0S4fA2A2Fz;").
Proof.
  intros z. unfold i32min, i32max. pose proof (bv_swrap_in_range 32 z ltac:(discriminate)) as H.
  rewrite half32 in H. lia.
Qed.

Lemma swrap32_small : ltac2:(tb__ "0|0|
S0S1cS32S50R1A2S32R1S4fA2A2S1bS0SfbQ20R2A2R2A3F_;Fz;").
Proof. intros z Hz. unfold i32min, i32max in Hz. apply bv_swrap_small. rewrite half32. lia. Qed.

Lemma mod64_mod32 : ltac2:(tb__ "0|2|
S0S1bS0S35R1S34Z2M0Z20A2M1A2S35S35R1S34G0Z40A2A2G1A2A3Fa;").
Proof.
  intros a. rewrite <- (Z.mod_add (a mod 2 ^ 64) (a / 2 ^ 64 * 2 ^ 32) (2 ^ 32)) by lia.
  f_equal. pose proof (Z_div_mod_eq_full a (2 ^ 64)). lia.
Qed.

Lemma swrap32_congr64 : ltac2:(tb__ "0|2|
S0S0S1bS0S35R2S34Z2Z40A2M0A2S35R1G0A2A3S1bS0SfbQ20M1R3A2SfbG1R2A2A3F_;Fb;Fa;").
Proof.
  intros a b H. rewrite <- (bv_swrap_wrap 32 a), <- (bv_swrap_wrap 32 b). f_equal.
  unfold bv_wrap. rewrite mod32. rewrite (mod64_mod32 a), (mod64_mod32 b), H. reflexivity.
Qed.

Lemma snorm32_swrap : ltac2:(tb__ "0|0|
S0S1bS0S5eR1A1SfbQ20R1A2A3Fz;").
Proof.
  intros z. unfold snorm32, bv_swrap, bv_wrap. rewrite half32, mod32.
  pose proof (Z.mod_pos_bound z (2 ^ 32) ltac:(lia)).
  destruct (Z.ltb_spec (z mod 2 ^ 32) (2 ^ 31)).
  - rewrite <- (Z.mod_add (z + 2 ^ 31) 0 (2 ^ 32)) by lia.
    replace (z + 2 ^ 31 + 0 * 2 ^ 32) with (z mod 2 ^ 32 + 2 ^ 31 + (z / 2 ^ 32) * 2 ^ 32)
      by (pose proof (Z_div_mod_eq_full z (2 ^ 32)); lia).
    rewrite Z.mod_add by lia. rewrite (Z.mod_small (z mod 2 ^ 32 + 2 ^ 31)) by lia. lia.
  - replace (z + 2 ^ 31) with ((z mod 2 ^ 32 - 2 ^ 31) + (z / 2 ^ 32 + 1) * 2 ^ 32)
      by (pose proof (Z_div_mod_eq_full z (2 ^ 32)); lia).
    rewrite Z.mod_add by lia. rewrite (Z.mod_small (z mod 2 ^ 32 - 2 ^ 31)) by lia. lia.
Qed.

Lemma snorm32_range : ltac2:(tb__ "0|1|
S0S1cS32S50S5eR1A1M0A2S32G0S4fA2A2Fz;").
Proof. intros z. rewrite snorm32_swrap. apply swrap32_range. Qed.

Lemma low32_signed : ltac2:(tb__ "0|2|
SfaQ40M0A1S1bS0SfeQ20M1S101R1A1A2SfbG1SfeG0R1A2A2A3Fv;").
Proof.
  intros v. unfold low32. rewrite bv_extract_signed. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  apply swrap32_congr64. symmetry. pose proof (soff_mod (mkVal (fun _ => v) (fun _ => []) (fun _ => None)) (SVar 1%positive)) as M.
  unfold soff, U in M. cbn in M. rewrite M. symmetry. apply Z.mod_small. apply urange.
Qed.

Lemma sext64_32_signed : ltac2:(tb__ "0|2|
SfaQ20M0A1S1bS0SfeQ40M1S115G0G1R1A3A2SfeG0R1A2A3Fv;").
Proof. intros v. unfold sext. apply bv_sign_extend_signed. cbv. discriminate. Qed.

Lemma srange32 : ltac2:(tb__ "0|2|
SfaQ20M0A1S1cS32S50SfeG0R1A2M1A2S32G1S4fA2A2Fv;").
Proof.
  intros v. unfold i32min, i32max. pose proof (bv_signed_in_range 32 v ltac:(discriminate)) as H.
  rewrite half32 in H. lia.
Qed.

Lemma aluw_range : ltac2:(tb__ "0|1|
S4S105S3S3S1cS32S50S6R4S10R3R2R1A3A2M0A2S32G0S4fA2A2Fb;Fa;Fop;Frho;").
Proof. intros. unfold soff. cbn [eval]. rewrite sext64_32_signed. apply srange32. Qed.

Lemma mdw_range : ltac2:(tb__ "0|1|
S4S107S3S3S1cS32S50S6R4S1aR3R2R1A3A2M0A2S32G0S4fA2A2Fb;Fa;Fop;Frho;").
Proof. intros. unfold soff. cbn [eval]. rewrite sext64_32_signed. apply srange32. Qed.

Lemma aluw_add_signed : ltac2:(tb__ "0|1|
S4S3S3S1bS0S6R3S10S109R2R1A3A2SfbQ20M0S33SfbG0S6R3R2A2A2SfbG0S6R3R1A2A2A2A2A3Fb;Fa;Frho;").
Proof.
  intros. unfold soff. cbn [eval]. rewrite sext64_32_signed. unfold alu32, alu.
  rewrite bv_add_signed, !low32_signed. reflexivity.
Qed.

Lemma aluw_sub_signed : ltac2:(tb__ "0|1|
S4S3S3S1bS0S6R3S10S106R2R1A3A2SfbQ20M0S38SfbG0S6R3R2A2A2SfbG0S6R3R1A2A2A2A2A3Fb;Fa;Frho;").
Proof.
  intros. unfold soff. cbn [eval]. rewrite sext64_32_signed. unfold alu32, alu.
  rewrite bv_sub_signed, !low32_signed. reflexivity.
Qed.

Lemma alu_add_signed : ltac2:(tb__ "0|0|
S4S3S3S1bS0S6R3SbS109R2R1A3A2SfbQ40S33S6R3R2A2S6R3R1A2A2A2A3Fb;Fa;Frho;").
Proof. intros. unfold soff. cbn [eval]. unfold alu64, alu. apply bv_add_signed. Qed.

Lemma alu_sub_signed : ltac2:(tb__ "0|0|
S4S3S3S1bS0S6R3SbS106R2R1A3A2SfbQ40S38S6R3R2A2S6R3R1A2A2A2A3Fb;Fa;Frho;").
Proof. intros. unfold soff. cbn [eval]. unfold alu64, alu. apply bv_sub_signed. Qed.

Definition srel_holds (rho : valuation) (r : sv * Z * sv) : Prop := ltac2:(tb__ "0|1|
S23S23S3S0A2M0S3A2OLr;Vr;G0S3G0OLp;R2S3S0S32S33S6Vrho;R2A2R1A2S6Vrho;R3A2A2Ld;Lx;X23x1Ly;Lp;X23x1").

Lemma srels_of_fact_sound : ltac2:(tb__ "0|0|
S4S5S9R2R1A2S49S23S23S3S0A2S3A2Sf6R3A1Sd8R2A1A3F_;Ff;Frho;").
Proof.
  intros rho f Hf. unfold srels_of_fact.
  repeat (match goal with |- context [match ?x with _ => _ end] => is_var x; destruct x end;
          cbv beta iota; try (constructor; fail)).
  all: cbn [holds eval branch_taken] in Hf; unfold bv_lts, bv_eqb in Hf;
       repeat match type of Hf with
         | ~ (?x = true) => apply Bool.not_true_iff_false in Hf
         | negb _ = false => apply Bool.negb_false_iff in Hf
         | negb _ = true => apply Bool.negb_true_iff in Hf
         | Z.ltb _ _ = true => apply Z.ltb_lt in Hf
         | Z.ltb _ _ = false => apply Z.ltb_ge in Hf
         | Z.eqb _ _ = true => apply Z.eqb_eq in Hf
         | Z.eqb _ _ = false => apply Z.eqb_neq in Hf
         | @eq (bv _) _ _ => apply (f_equal bv_unsigned) in Hf
         end;
       try match type of Hf with bv_unsigned ?X = bv_unsigned ?Y =>
             assert (HS : bv_signed X = bv_signed Y) by (apply bv_eq in Hf; rewrite Hf; reflexivity) end;
       rewrite ?slt_val, ?lit_unsigned in Hf;
       try replace (0 mod 2 ^ 64) with 0 in Hf by reflexivity;
       repeat match type of Hf with
         | context [if ?x <? ?y then _ else _] => destruct (Z.ltb_spec x y)
         end;
       try discriminate; try lia;
       repeat constructor; cbn [srel_holds]; unfold soff; cbn [eval]; try lia.
Qed.

Lemma srels_of_sound : ltac2:(tb__ "0|0|
S4S25S5A1S49S5S9R2A1R1A3S49S23S23S3S0A2S3A2Sf6R3A1Sd7R2A1A3F_;Ffacts;Frho;").
Proof.
  intros rho facts H. induction facts as [|f rest IH]; cbn [srels_of]; [constructor|].
  inversion H; subst. apply Forall_app. split; [apply srels_of_fact_sound; assumption | apply IH; assumption].
Qed.

Lemma srel_itv1_sound : ltac2:(tb__ "0|0|
S4S25S5A1S3S23S23S3S0A2S3A2S49S5S9R4A1R3A3Sf6R5R2A2Sf3Sd5R5R4R3A3S6R6R4A2A2F_;F_;Fr;Fe;Ffacts;Frho;").
Proof.
  intros rho facts e [[x d] y] Hf Hr. unfold srel_itv1. unfold srel_holds in Hr.
  pose proof (in_stop rho e) as T. unfold in_sitv, stop_itv in T. cbn [fst snd] in T.
  destruct (sv_eqb y e) eqn:Ey.
  - rewrite <- (sv_eqb_sound _ _ Ey) in *. pose proof (sfacts_itv_sound rho facts x Hf) as X.
    destruct (sfacts_itv facts x) as [lx hx]. unfold in_sitv in *. cbn [fst snd] in *. lia.
  - destruct (sv_eqb x e) eqn:Ex; [|apply in_stop].
    rewrite <- (sv_eqb_sound _ _ Ex) in *. pose proof (sfacts_itv_sound rho facts y Hf) as Y.
    destruct (sfacts_itv facts y) as [ly hy]. unfold in_sitv in *. cbn [fst snd] in *. lia.
Qed.

Lemma srels_itv_sound : ltac2:(tb__ "0|1|
S4S25S5A1S25S23S23S3S0A2S3A2M0A1S3S49S5S9R4A1R3A3S49G0Sf6R5A1R3A3Sf3Sd6R5R4R3A3S6R6R3A2A2F_;F_;Fe;Frels;Ffacts;Frho;").
Proof.
  intros rho facts rels e Hf Hr. induction rels as [|r t IH]; cbn [srels_itv]; [apply in_stop|].
  inversion Hr; subst. apply in_smeet; [apply srel_itv1_sound; assumption | apply IH; assumption].
Qed.

Lemma swrap64_range : ltac2:(tb__ "0|1|
S0S1cS32S55SfbQ40R1A2M0A2S32G0S54A2A2Fz;").
Proof.
  intros z. unfold smin, smax. pose proof (bv_swrap_in_range 64 z ltac:(discriminate)) as H.
  rewrite half64 in H. lia.
Qed.

Lemma sadd_itv_sound : ltac2:(tb__ "0|2|
S23S0S0A2M0G0S0S0Sf3R4R2A2M1G1Sf3SbfR6R5A2SfbQ40S33R4R3A2A2A2F_;F_;Fy;Fx;Fq;Fp;").
Proof.
  intros [a b] [c d] x y [H1 H2] [H3 H4]. unfold sadd_itv. cbn in *.
  pose proof (swrap64_range (x + y)) as R.
  destruct (Z.leb_spec a b); destruct (Z.leb_spec c d); destruct (Z.leb_spec smin (a + c)); destruct (Z.leb_spec (b + d) smax);
    cbn [andb]; unfold in_sitv; cbn; try (unfold stop_itv, smin, smax in *; cbn; lia).
  rewrite swrap64_small by lia. lia.
Qed.

Lemma ssub_itv_sound : ltac2:(tb__ "0|2|
S23S0S0A2M0G0S0S0Sf3R4R2A2M1G1Sf3SdaR6R5A2SfbQ40S38R4R3A2A2A2F_;F_;Fy;Fx;Fq;Fp;").
Proof.
  intros [a b] [c d] x y [H1 H2] [H3 H4]. unfold ssub_itv. cbn in *.
  pose proof (swrap64_range (x - y)) as R.
  destruct (Z.leb_spec a b); destruct (Z.leb_spec c d); destruct (Z.leb_spec smin (a - d)); destruct (Z.leb_spec (b - c) smax);
    cbn [andb]; unfold in_sitv; cbn; try (unfold stop_itv, smin, smax in *; cbn; lia).
  rewrite swrap64_small by lia. lia.
Qed.

Lemma in_i32_spec : ltac2:(tb__ "0|0|
S23S0S0A2S21S1bS22S96R1A1S24A3S1cS32S50S29S0S0R1A3A2S32S2bS0S0R1A3S4fA2A2A2Fp;").
Proof.
  intros [a b]. unfold in_i32. cbn. rewrite Bool.andb_true_iff, !Z.leb_le. tauto.
Qed.

Lemma sadd32_itv_sound : ltac2:(tb__ "0|3|
S23S0S0A2M0G0S0S0Sf3R4R2A2M1G1Sf3SbeR6R5A2SfbQ20M2S33SfbG2R4A2SfbG2R3A2A2A2A2F_;F_;Fy;Fx;Fq;Fp;").
Proof.
  intros p q x y Hx Hy. unfold sadd32_itv.
  pose proof (swrap32_range (bv_swrap 32 x + bv_swrap 32 y)) as R.
  destruct ((fst p <=? snd p) && (fst q <=? snd q) && in_i32 p && in_i32 q && in_i32 (fst p + fst q, snd p + snd q))%bool eqn:E.
  - repeat (apply andb_prop in E; destruct E as [E ?]).
    apply in_i32_spec in H. apply in_i32_spec in H0. apply in_i32_spec in H1. cbn in H.
    destruct p as [a b], q as [c d]. unfold in_sitv in *. cbn in *.
    rewrite (swrap32_small x), (swrap32_small y) by lia. rewrite swrap32_small by lia. lia.
  - unfold in_sitv, i32_itv. cbn. lia.
Qed.

Lemma ssub32_itv_sound : ltac2:(tb__ "0|3|
S23S0S0A2M0G0S0S0Sf3R4R2A2M1G1Sf3Sd9R6R5A2SfbQ20M2S38SfbG2R4A2SfbG2R3A2A2A2A2F_;F_;Fy;Fx;Fq;Fp;").
Proof.
  intros p q x y Hx Hy. unfold ssub32_itv.
  pose proof (swrap32_range (bv_swrap 32 x - bv_swrap 32 y)) as R.
  destruct ((fst p <=? snd p) && (fst q <=? snd q) && in_i32 p && in_i32 q && in_i32 (fst p - snd q, snd p - fst q))%bool eqn:E.
  - repeat (apply andb_prop in E; destruct E as [E ?]).
    apply in_i32_spec in H. apply in_i32_spec in H0. apply in_i32_spec in H1. cbn in H.
    destruct p as [a b], q as [c d]. unfold in_sitv in *. cbn in *.
    rewrite (swrap32_small x), (swrap32_small y) by lia. rewrite swrap32_small by lia. lia.
  - unfold in_sitv, i32_itv. cbn. lia.
Qed.

Lemma swrap32_idemp : ltac2:(tb__ "0|2|
S0S1bS0SfbQ20M0SfbG0R1A2M1A2G1A3Fz;").
Proof. intros z. apply swrap32_small. apply swrap32_range. Qed.

Lemma swrap32_snorm : ltac2:(tb__ "0|0|
S0S1bS0SfbQ20S4eR1A1A2S5eR1A1A3Fc;").
Proof.
  intros c. rewrite snorm32_swrap. apply swrap32_congr64. apply snorm_mod.
Qed.

Lemma mod64_modn : ltac2:(tb__ "0|3|
S0S0S1cS32Z0R1A2S32R1Z40M0A2A2S1bS0S35R3S34Z2M1R2A2M2A2S35S35R3S34G1G0A2A2G2A2A3F_;Fn;Fa;").
Proof.
  intros a n Hn.
  rewrite <- (Z.mod_add (a mod 2 ^ 64) (a / 2 ^ 64 * 2 ^ (64 - n)) (2 ^ n)) by (apply Z.pow_nonzero; lia).
  f_equal. pose proof (Z_div_mod_eq_full a (2 ^ 64)) as H.
  set (q := a / 2 ^ 64) in *. set (r := a mod 2 ^ 64) in *.
  assert (E : 2 ^ 64 = 2 ^ (64 - n) * 2 ^ n) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite E in H. lia.
Qed.

Lemma swrap_congr64 : ltac2:(tb__ "0|1|
S2S0S0S11aR3Q40A2S1bS0S35R3S34Z2Z40A2M0A2S35R2G0A2A3S1bS0SfbR5R4A2SfbR5R3A2A3F_;F_;Fb;Fa;Fn;").
Proof.
  intros n a b Hn H. rewrite <- (bv_swrap_wrap n a), <- (bv_swrap_wrap n b). f_equal.
  unfold bv_wrap, bv_modulus. rewrite (mod64_modn a), (mod64_modn b) by lia. rewrite H. reflexivity.
Qed.

Lemma sext_low_signed : ltac2:(tb__ "0|1|
S2SfaQ40M0A1S36Z0S3bR2A1A2S32S3bR3A1Z40A2S1bS0SfeG0SeS24R4R3A3A2SfbR4SfeG0R3A2A2A3F_;F_;Fv;Fw;").
Proof.
  intros w v Hw0 Hw0'.
  assert (Hw' : (w <= 64)%N) by (apply N2Z.inj_le; cbn; lia).
  unfold ext_low, sext. rewrite bv_sign_extend_signed by exact Hw'.
  rewrite bv_extract_signed. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  apply swrap_congr64; [exact Hw'|]. symmetry.
  pose proof (soff_mod (mkVal (fun _ => v) (fun _ => []) (fun _ => None)) (SVar 1%positive)) as M.
  unfold soff, U in M. cbn in M. rewrite M. symmetry. apply Z.mod_small. apply urange.
Qed.

Lemma zext_low_signed : ltac2:(tb__ "0|2|
S2SfaQ40M0A1S36S3bR2A1Z40A2S1cS32Z0SfeG0SeS2cR3R2A3A2M1A2S32G1S38S34Z2S3bR3A1A2Z1A2A2A2F_;Fv;Fw;").
Proof.
  intros w v Hw. unfold ext_low, zext.
  rewrite bv_zero_extend_signed. rewrite bv_extract_unsigned.
  pose proof (bv_wrap_in_range w (bv_unsigned v ≫ Z.of_N 0)) as R. unfold bv_modulus in R.
  assert (2 ^ Z.of_N w <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
  rewrite bv_swrap_small; [lia|]. rewrite half64. lia.
Qed.

Lemma half_pow : ltac2:(tb__ "0|0|
S2S36Z0S3bR1A1A2S1bS0SffR2A1S34Z2S38S3bR2A1Z1A2A2A3F_;Fw;").
Proof.
  intros w Hw. unfold bv_half_modulus, bv_modulus.
  replace (Z.of_N w) with (Z.of_N w - 1 + 1) at 1 by lia. rewrite Z.pow_add_r by lia.
  rewrite Z.pow_1_r. apply Z.div_mul. lia.
Qed.

Lemma stv_body_sound : ltac2:(tb__ "0|0|
S4S4cS3S23S0S0A2Fx;S3S45R4R3A2S49S23S23S3S0A2S3A2Sf6R5A1S52R4A1A3S3S118S47R1A1S47R4A1A2Sf3R6R2A1S6R8R2A2A2F_;Fa;Sf3SdeR5R6R4A3S6R7R4A2A2F_;F_;F_;Fe;Frec;Fdg;Frho;").
Proof.
  intros rho dg rec e Hv Hsr Hrec. pose proof (dgv_facts _ _ Hv) as Hf. set (facts := dg_facts dg) in *. unfold stv_body.
  apply in_smeet; [apply in_smeet; [apply in_smeet|]|].
  2: { apply sitv_of_itv_sound. apply itv_t_sound; assumption. }
  2: { apply sfacts_itv_sound. exact Hf. }
  2: { apply srels_itv_sound; [exact Hf | exact Hsr]. }
  destruct e; try apply in_stop.
  -   unfold in_sitv. cbn. rewrite soff_lit. lia.
  -   pose proof (Hrec e1 ltac:(cbn; lia)) as IHe1. pose proof (Hrec e2 ltac:(cbn; lia)) as IHe2.
    destruct op; try apply in_stop.
    +   destruct e2 as [c| | | | | | |];
        try (rewrite alu_add_signed; apply sadd_itv_sound; assumption).
      rewrite alu_add_signed. apply sadd_itv_sound; [assumption|]. unfold in_sitv. cbn. rewrite soff_lit. lia.
    +   rewrite alu_sub_signed. apply ssub_itv_sound; assumption.
    +   destruct e2 as [k| | | | | | |]; try apply in_stop.
      destruct (Z.leb_spec (fst (rec e1)) (snd (rec e1))); [|apply in_stop].
      unfold soff. cbn [eval]. unfold alu64, alu. rewrite bv_ashiftr_signed, shamt_val. fold (soff rho e1).
      pose proof (Z.mod_pos_bound k 64 ltac:(lia)) as K.
      destruct (rec e1) as [l h]. unfold in_sitv in *. cbn in *.
      rewrite !Z.shiftr_div_pow2 by lia.
      assert (P : 0 < 2 ^ (k mod 64)) by (apply Z.pow_pos_nonneg; lia).
      assert (D1 : l / 2 ^ (k mod 64) <= soff rho e1 / 2 ^ (k mod 64)) by (apply Z.div_le_mono; lia).
      assert (D2 : soff rho e1 / 2 ^ (k mod 64) <= h / 2 ^ (k mod 64)) by (apply Z.div_le_mono; lia).
      pose proof (soff_range rho e1) as SR.
      assert (D3 : - 2 ^ 63 <= soff rho e1 / 2 ^ (k mod 64)).
      { apply Z.div_le_lower_bound; [lia|]. assert (2 ^ 63 * 1 <= 2 ^ 63 * 2 ^ (k mod 64)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
      assert (D4 : soff rho e1 / 2 ^ (k mod 64) < 2 ^ 63).
      { apply Z.div_lt_upper_bound; [lia|]. assert (2 ^ 63 * 1 <= 2 ^ 63 * 2 ^ (k mod 64)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
      rewrite bv_swrap_small; [lia|]. rewrite half64. lia.
  -   pose proof (Hrec e1 ltac:(cbn; lia)) as IHe1. pose proof (Hrec e2 ltac:(cbn; lia)) as IHe2.
    pose proof (aluw_range rho op e1 e2) as AR.
    destruct op; try (unfold in_sitv, i32_itv; cbn [fst snd]; exact AR).
    +   destruct e2 as [c| | | | | | |];
        try (rewrite aluw_add_signed; apply sadd32_itv_sound; assumption).
      rewrite aluw_add_signed. replace (bv_swrap 32 (soff rho (SLit c))) with (bv_swrap 32 (snorm32 c)).
      2: { rewrite soff_lit, swrap32_snorm, snorm32_swrap, swrap32_idemp. reflexivity. }
      apply sadd32_itv_sound; [assumption|]. unfold in_sitv. cbn. lia.
    +   rewrite aluw_sub_signed. apply ssub32_itv_sound; assumption.
  -   pose proof (mdw_range rho op e1 e2) as MR. unfold in_sitv, i32_itv. cbn [fst snd]. exact MR.
  -   pose proof (Hrec e ltac:(cbn; lia)) as IHe. destruct sgn.
    + destruct ((0 <? Z.of_N w) && (Z.of_N w <=? 64))%bool eqn:E; [|apply in_stop].
      apply andb_prop in E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.leb_le in E2.
      unfold soff. cbn [eval]. rewrite sext_low_signed by lia. fold (soff rho e).
      pose proof (bv_swrap_in_range w (soff rho e) ltac:(intros X; rewrite X in E1; cbn in E1; lia)) as R. rewrite half_pow in R by lia.
      cbn [fst snd]. destruct (rec e) as [l h]. cbn [fst snd].
      match goal with |- context [if ?c then _ else _] => destruct c eqn:C end.
      * repeat (apply andb_prop in C; destruct C as [C ?]). apply Z.leb_le in C. apply Z.leb_le in H. apply Z.leb_le in H0.
        unfold in_sitv in *. cbn [fst snd] in *.
        rewrite bv_swrap_small; [lia|]. rewrite half_pow by lia. lia.
      * unfold in_sitv. cbn [fst snd]. lia.
    + destruct ((0 <=? Z.of_N w) && (Z.of_N w <? 64))%bool eqn:E; [|apply in_stop].
      apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      unfold soff. cbn [eval]. pose proof (zext_low_signed w (eval rho e) ltac:(lia)). unfold in_sitv. cbn [fst snd]. lia.
Qed.

Lemma stv_t_sound_n : ltac2:(tb__ "0|0|
S4S4cS2aS3S45R4R3A2S49S23S23S3S0A2S3A2Sf6R5A1S52R4A1A3S118S47R3A1R4A2Sf3S5fR6R4A2S6R7R4A2A2F_;F_;F_;Fe;Fn;Fdg;Frho;").
Proof.
  intros rho dg n. induction n as [|n IH]; intros e Hv Hsr Hn; [lia|]. pose proof (dgv_tbl _ _ Hv) as Ht.
  assert (STEP : stv_t dg e = match tbl_find (dg_tbl dg) e with
                                | Some v => snd v
                                | None => stv_body (fun a => stv_t dg a) dg e
                                end) by (destruct e; reflexivity).
  rewrite STEP. destruct (tbl_find (dg_tbl dg) e) as [v|] eqn:Hfind.
  - exact (proj2 (tbl_find_sound rho _ _ _ Ht Hfind)).
  - apply stv_body_sound; [exact Hv | exact Hsr |]. intros a Ha. apply IH; [exact Hv | exact Hsr | lia].
Qed.

Lemma stv_t_sound : ltac2:(tb__ "0|0|
S4S4cS3S45R3R2A2S49S23S23S3S0A2S3A2Sf6R4A1S52R3A1A3Sf3S5fR4R3A2S6R5R3A2A2F_;F_;Fe;Fdg;Frho;").
Proof. intros. apply (stv_t_sound_n rho dg (S (sv_size e))); [assumption | assumption | lia]. Qed.

Lemma stv_node_sound : ltac2:(tb__ "0|0|
S4S4cS3S45R3R2A2S49S23S23S3S0A2S3A2Sf6R4A1S52R3A1A3Sf3SdfR4R3A2S6R5R3A2A2F_;F_;Fe;Fdg;Frho;").
Proof.
  intros. unfold stv_node. apply stv_body_sound; [assumption | assumption |].
  intros a _. apply stv_t_sound; assumption.
Qed.

Definition ineq_holds (rho : valuation) (g : ineq) : Prop := ltac2:(tb__ "0|0|
S32Z0S33Sf2Vrho;S29S4bS0Vg;A3A2S2bS4bS0Vg;A3A2A2").

Definition dg_ok (rho : valuation) (dg : fdig) : Prop := ltac2:(tb__ "0|1|
S1cS45Vrho;Vdg;A2S1cS49S23S23S3S0A2S3A2M0Sf7Vrho;A1S67Vdg;A1A3S1cS49G0Sf6Vrho;A1S52Vdg;A1A3S49S4dSf4Vrho;A1S66Vdg;A1A3A2A2A2").

Lemma dg_ok_v : ltac2:(tb__ "0|0|
S4S4cSf1R2R1A2S45R3R2A2F_;Fdg;Frho;").
Proof. intros rho dg H. exact (proj1 H). Qed.
Lemma dg_ok_facts : ltac2:(tb__ "0|0|
S4S4cSf1R2R1A2S49S5S9R3A1S56R2A1A3F_;Fdg;Frho;").
Proof. intros rho dg H. exact (dgv_facts _ _ (proj1 H)). Qed.
Lemma dg_ok_tbl : ltac2:(tb__ "0|0|
S4S4cSf1R2R1A2S44R3S8fR2A1A2F_;Fdg;Frho;").
Proof. intros rho dg H. exact (dgv_tbl _ _ (proj1 H)). Qed.
Lemma dg_ok_srels : ltac2:(tb__ "0|0|
S4S4cSf1R2R1A2S49S23S23S3S0A2S3A2Sf6R3A1S52R2A1A3F_;Fdg;Frho;").
Proof. intros rho dg (_ & _ & H & _). exact H. Qed.
Lemma dg_ok_urels : ltac2:(tb__ "0|0|
S4S4cSf1R2R1A2S49S23S23S3S0A2S3A2Sf7R3A1S67R2A1A3F_;Fdg;Frho;").
Proof. intros rho dg (_ & H & _). exact H. Qed.
Lemma dg_ok_pool : ltac2:(tb__ "0|0|
S4S4cSf1R2R1A2S49S4dSf4R3A1S66R2A1A3F_;Fdg;Frho;").
Proof. intros rho dg (_ & _ & _ & H). exact H. Qed.

Lemma itv_d_sound : ltac2:(tb__ "0|0|
S4S4cS3Sf1R3R2A2S43S6cR3R2A2S42R4R2A2A2F_;Fe;Fdg;Frho;").
Proof. intros rho dg e H. apply itv_t_sound. apply dg_ok_v. exact H. Qed.

Lemma stv_d_sound : ltac2:(tb__ "0|0|
S4S4cS3Sf1R3R2A2Sf3S5fR3R2A2S6R4R2A2A2F_;Fe;Fdg;Frho;").
Proof. intros rho dg e H. apply stv_t_sound; [apply dg_ok_v | apply dg_ok_srels]; exact H. Qed.

Lemma ctx0_dg_ok : ltac2:(tb__ "0|0|
S4S25S5A1S49S5S9R2A1R1A3Sf1R3S8dR2A1A2F_;Ffacts;Frho;").
Proof.
  intros rho facts Hf. unfold dg_ok. split; [apply ctx0_ok; exact Hf|]. cbn. repeat split; try constructor.
  - apply rels_of_sound. exact Hf.
  - apply srels_of_sound. exact Hf.
Qed.

Lemma snorm_id : ltac2:(tb__ "0|0|
S0S1cS32S55R1A2S32R1S54A2A2S1bS0S4eR2A1R2A3F_;Fz;").
Proof.
  intros z Hz. unfold smin, smax in Hz. unfold snorm.
  destruct (Z_lt_ge_dec z 0).
  - rewrite <- (Z.mod_add z 1 (2 ^ 64)) by lia. rewrite (Z.mod_small (z + 1 * 2 ^ 64)) by lia.
    destruct (Z.ltb_spec (z + 1 * 2 ^ 64) (2 ^ 63)); lia.
  - rewrite (Z.mod_small z) by lia. destruct (Z.ltb_spec z (2 ^ 63)); lia.
Qed.

Lemma soff_eq_eval : ltac2:(tb__ "0|0|
S4S3S3S1bS0S6R3R2A2S6R3R1A2A3S1bSfaQ40A1S7R4R3A2S7R4R2A2A3F_;Fb;Fa;Frho;").
Proof. intros rho a b H. unfold soff in H. apply bv_eq_signed. exact H. Qed.

Lemma sll32_srl_val : ltac2:(tb__ "0|3|
SfaQ40M0A1M1S0S0S1cS32Z0R1A2S32R1R2A2A2S36R3Z40M2A2S36SfcG0R5A2S34Z2S38G2R4A2A2A2S1bG1S100S10eS100S10aR6SfdG0R5A2A3SfdG0R4A2A3S100S10aR6SfdG0S38R5R4A2A2A3A3F_;F_;F_;Fsh;Fk;Fx;").
Proof.
  intros x k sh Hsh Hk Hx. pose proof (urange x) as R. apply bv_eq.
  rewrite srl_val, !sll_val. rewrite (Z.mod_small k 64), (Z.mod_small sh 64), (Z.mod_small (k - sh) 64) by lia.
  rewrite !Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  assert (P : 2 ^ k = 2 ^ (k - sh) * 2 ^ sh) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Q : 2 ^ 64 = 2 ^ (64 - k) * 2 ^ k) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (0 < 2 ^ sh) by (apply Z.pow_pos_nonneg; lia). assert (0 < 2 ^ (k - sh)) by (apply Z.pow_pos_nonneg; lia).
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ (k - sh) <= 2 ^ k) by (apply Z.pow_le_mono_r; lia).
  rewrite (Z.mod_small (bv_unsigned x * 2 ^ k)) by (rewrite Q; nia).
  rewrite P, Z.mul_assoc, Z.div_mul by lia.
  symmetry. apply Z.mod_small. rewrite Q. nia.
Qed.

Lemma wnorm_t_sound : ltac2:(tb__ "0|0|
S4S4cS3Sf1R3R2A2S1bSfaQ40A1S7R4S63R3R2A2A2S7R4R2A2A3F_;Fe;Fdg;Frho;").
Proof.
  intros rho dg e Hd. induction e; cbn [wnorm_t]; try reflexivity.
  -   destruct op; try reflexivity.
    + cbn [eval]. rewrite IHe1, IHe2. reflexivity.
    + cbn [eval]. rewrite IHe1, IHe2. reflexivity.
    + destruct e2; try reflexivity. cbn [eval]. rewrite IHe1. reflexivity.
    +   destruct e2 as [sh| | | | | | |]; try reflexivity.
      destruct (wnorm_t dg e1) as [| |op1 x b1| | | | |] eqn:Ew; try reflexivity.
      destruct op1; try reflexivity. destruct b1 as [k| | | | | | |]; try reflexivity.
      destruct (Z.leb_spec 0 sh); [|reflexivity]. destruct (Z.leb_spec sh k); [|reflexivity].
      destruct (Z.ltb_spec k 64); [|reflexivity].
      destruct (small_u_t dg x (64 - k)) eqn:Hs; [|reflexivity].
      pose proof (small_u_t_sound rho dg x (64 - k) (dg_ok_v _ _ Hd) Hs) as Hx.
      rewrite mk_alu_sound. cbn [eval]. rewrite <- IHe1. cbn [eval]. symmetry. apply sll32_srl_val; lia.
  -
    set (a' := wnorm_t dg e1) in *. set (b' := wnorm_t dg e2) in *.
    pose proof (stv_d_sound rho dg a' Hd) as STa. pose proof (stv_d_sound rho dg b' Hd) as STb.
    assert (Ea : soff rho a' = soff rho e1) by (unfold soff; rewrite IHe1; reflexivity).
    assert (Eb : soff rho b' = soff rho e2) by (unfold soff; rewrite IHe2; reflexivity).
    destruct (stv_t dg a') as [l h]. destruct (stv_t dg b') as [l2 h2]. cbn [fst snd].
    unfold in_sitv in STa, STb. cbn [fst snd] in STa, STb.
    destruct op; try reflexivity.
    +   destruct e2 as [c| | | | | | |].
      1: { destruct ((l <=? h) && in_i32 (l, h) && in_i32 (l + snorm32 c, h + snorm32 c))%bool eqn:C; [|reflexivity].
           repeat (apply andb_prop in C; destruct C as [C ?]). apply in_i32_spec in H. apply in_i32_spec in H0. cbn [fst snd] in H, H0.
           pose proof (snorm32_range c) as CR.
           apply soff_eq_eval. rewrite alu_add_signed, aluw_add_signed, !soff_lit, swrap32_snorm.
           rewrite (snorm_id (snorm32 c)) by (unfold i32min, i32max, smin, smax in *; lia).
           rewrite Ea. rewrite (swrap32_small (soff rho e1)) by lia.
           rewrite swrap32_small by lia. rewrite swrap64_small by (unfold i32min, i32max, smin, smax in *; lia). reflexivity. }
      all: destruct ((l <=? h) && (l2 <=? h2) && in_i32 (l, h) && in_i32 (l2, h2) && in_i32 (l + l2, h + h2))%bool eqn:C; [|reflexivity];
           repeat (apply andb_prop in C; destruct C as [C ?]);
           repeat match goal with H : in_i32 _ = true |- _ => apply in_i32_spec in H; cbn [fst snd] in H end;
           apply soff_eq_eval; rewrite alu_add_signed, aluw_add_signed, Ea, Eb;
           rewrite (swrap32_small (soff rho e1)), (swrap32_small (soff rho _)) by lia;
           rewrite swrap32_small by lia; rewrite swrap64_small by (unfold i32min, i32max, smin, smax in *; lia); reflexivity.
    +
      destruct ((l <=? h) && (l2 <=? h2) && in_i32 (l, h) && in_i32 (l2, h2) && in_i32 (l - h2, h - l2))%bool eqn:C; [|reflexivity].
      repeat (apply andb_prop in C; destruct C as [C ?]).
      repeat match goal with H : in_i32 _ = true |- _ => apply in_i32_spec in H; cbn [fst snd] in H end.
      apply soff_eq_eval. rewrite alu_sub_signed, aluw_sub_signed, Ea, Eb.
      rewrite (swrap32_small (soff rho e1)), (swrap32_small (soff rho e2)) by lia.
      rewrite swrap32_small by lia. rewrite swrap64_small by (unfold i32min, i32max, smin, smax in *; lia). reflexivity.
  -   destruct op; try reflexivity. destruct e2; try reflexivity. cbn [eval]. rewrite IHe1. reflexivity.
  -   destruct sgn.
    2:{   set (a' := wnorm_t dg e) in *.
        destruct (Z.ltb_spec 0 (Z.of_N w)); [|reflexivity].
        destruct (Z.leb_spec (Z.of_N w) 64); [|reflexivity].
        destruct (small_u_t dg a' (Z.of_N w)) eqn:Hs; [|reflexivity].
        pose proof (small_u_t_sound rho dg a' (Z.of_N w) (dg_ok_v _ _ Hd) Hs) as B. rewrite IHe in B.
        cbn [eval]. rewrite IHe. symmetry. apply ext_low_small; lia. }
    destruct w as [|p]; try reflexivity.
    repeat (destruct p as [p|p|]; try reflexivity).
    set (a' := wnorm_t dg e) in *.
    pose proof (stv_d_sound rho dg a' Hd) as ST. destruct (stv_t dg a') as [l h]. cbn [fst snd].
    destruct ((l <=? h) && in_i32 (l, h))%bool eqn:C; [|reflexivity].
    apply andb_prop in C as [C1 C2]. apply in_i32_spec in C2. cbn [fst snd] in C2.
    unfold in_sitv in ST. cbn [fst snd] in ST.
    assert (Ea : soff rho a' = soff rho e) by (unfold soff; rewrite IHe; reflexivity).
    apply soff_eq_eval. rewrite Ea. unfold soff at 2. cbn [eval]. rewrite sext_low_signed by (cbn; lia).
    fold (soff rho e). rewrite swrap32_small by lia. reflexivity.
Qed.

Corollary soff_wnorm_t : ltac2:(tb__ "0|0|
S4S4cS3Sf1R3R2A2S1bS0S6R4S63R3R2A2A2S6R4R2A2A3F_;Fe;Fdg;Frho;").
Proof. intros. unfold soff. rewrite wnorm_t_sound by assumption. reflexivity. Qed.

Corollary U_wnorm_t : ltac2:(tb__ "0|0|
S4S4cS3Sf1R3R2A2S1bS0S42R4S63R3R2A2A2S42R4R2A2A3F_;Fe;Fdg;Frho;").
Proof. intros. unfold U. rewrite wnorm_t_sound by assumption. reflexivity. Qed.

Lemma u_of_s_sound : ltac2:(tb__ "0|0|
S4S3S23S0S0A2Sf3R1S6R3R2A2A2S43Se9R2A1S42R4R3A2A2F_;Fp;Fe;Frho;").
Proof.
  intros rho e [l h] [H1 H2]. cbn [fst snd] in H1, H2. unfold u_of_s, M64.
  destruct (Z.leb_spec l h); cbn [negb]; [|apply in_top].
  pose proof (urange (eval rho e)) as R. unfold soff in H1, H2. unfold U.
  destruct (Z.leb_spec 0 l).
  - unfold in_itv; cbn [fst snd].
    destruct (Z_lt_ge_dec (bv_unsigned (eval rho e)) (2 ^ 63)).
    + rewrite signed_small in H1, H2 by lia. lia.
    + rewrite signed_big in H1, H2 by lia. lia.
  - destruct (Z.ltb_spec h 0); [|apply in_top]. unfold in_itv; cbn [fst snd].
    destruct (Z_lt_ge_dec (bv_unsigned (eval rho e)) (2 ^ 63)).
    + rewrite signed_small in H1, H2 by lia. lia.
    + rewrite signed_big in H1, H2 by lia. lia.
Qed.

Lemma entry_norm_sound : ltac2:(tb__ "0|2|
S4S3S23S23S0S0A2M0G0A2S1cS43S29G0G0R1A3S42R3R2A2A2Sf3S2bG0G0R1A3S6R3R2A2A2A2S1cS43S29G0G0S92R2A1M1A3S42R4R3A2A2Sf3S2bG0G0G1A3S6R4R3A2A2A2F_;Fv;Fe;Frho;").
Proof.
  intros rho e [pu ps] [Hu Hs]. unfold entry_norm. cbn [fst snd] in *.
  assert (Hu' : in_itv (itv_meet pu (u_of_s ps)) (U rho e)) by (apply in_meet; [exact Hu | apply u_of_s_sound; exact Hs]).
  split; [exact Hu'|]. apply in_smeet; [exact Hs|]. apply sitv_of_itv_sound. exact Hu'.
Qed.

Lemma entry_ok_intro : ltac2:(tb__ "0|2|
S4S3S23S23S0S0A2M0G0A2M1S43S29G0G0R1A3S42R3R2A2A2Sf3S2bG0G0R2A3S6R4R3A2A2S48R5S28S3G1R4R3A4A2F_;F_;Fv;Fe;Frho;").
Proof. intros rho e [pu ps] Hu Hs. unfold entry_ok. cbn [fst snd]. split; [exact Hu | exact Hs]. Qed.

Lemma entry_ok_elim : ltac2:(tb__ "0|2|
S4S3S23S23S0S0A2M0G0A2M1S48R3S28S3G1R2R1A4A2S1cS43S29G0G0R2A3S42R4R3A2A2Sf3S2bG0G0R2A3S6R4R3A2A2A2F_;Fv;Fe;Frho;").
Proof. intros rho e [pu ps] [Hu Hs]. cbn [fst snd] in *. split; [exact Hu | exact Hs]. Qed.

Lemma dg_with_tbl_ok : ltac2:(tb__ "0|0|
S4S4cS25S51A1Sf1R3R2A2S44R4R2A2Sf1R5S91R4R3A2A2F_;F_;Ftbl;Fdg;Frho;").
Proof.
  intros rho dg tbl (A & B & C & D) Ht. unfold dg_ok. split; [apply dgv_with_tbl; assumption|]. cbn. repeat split; assumption.
Qed.

Lemma tbl_init_ok : ltac2:(tb__ "0|0|
S4S25S3A1S4cSf1R3R1A2Sf1R4S82R2R3A2A2F_;Fdg;Fes;Frho;").
Proof.
  intros rho es. induction es as [|e rest IH]; intros dg Hd; cbn [tbl_init]; [exact Hd|].
  apply IH.
  pose proof (itv_node_sound rho dg e (dg_ok_v _ _ Hd)) as Hu.
  set (pu := itv_node dg e) in *.
  set (dg1 := dg_with_tbl dg ((e, (pu, stop_itv)) :: dg_tbl dg)).
  assert (Hd1 : dg_ok rho dg1).
  { apply dg_with_tbl_ok; [exact Hd|]. constructor; [|apply dg_ok_tbl; exact Hd].
    apply entry_ok_intro; [exact Hu | apply in_stop]. }
  pose proof (stv_node_sound rho dg1 e (dg_ok_v _ _ Hd1) (dg_ok_srels _ _ Hd1)) as Hs.
  apply dg_with_tbl_ok; [exact Hd|]. constructor; [|apply dg_ok_tbl; exact Hd].
  apply entry_ok_intro; cbn [fst snd].
  - apply in_meet; [exact Hu | apply u_of_s_sound; exact Hs].
  - apply in_smeet; [exact Hs|]. apply sitv_of_itv_sound. exact Hu.
Qed.

Lemma tbl_get_sound : ltac2:(tb__ "0|2|
S4S25S51A1S3S44R3R2A2S1cS43S29S23S0S0A2M0G0Se3R3R2A2M1A3S42R4R2A2A2Sf3S2bG0G0G1A3S6R4R2A2A2A2F_;Fe;Ftbl;Frho;").
Proof.
  intros rho tbl e Ht. unfold tbl_get. destruct (tbl_find tbl e) as [v|] eqn:E.
  - exact (tbl_find_sound rho tbl e v Ht E).
  - cbn [fst snd]. split; [apply in_top | apply in_stop].
Qed.

Lemma tbl_upd_ok : ltac2:(tb__ "0|3|
S4S25S51A1S3S23S23S0S0A2M0G0A2M1G1Fx;S44R4R3A2G1S1cS43S29G0G0R1A3S42R6R4A2A2Sf3S2bG0G0R1A3S6R6R4A2A2A2S1cS43S29G0G0R4R2A1M2A3S42R7R5A2A2Sf3S2bG0G0G2A3S6R7R5A2A2A2F_;Fv;S44R6Se8R5R4R3A3A2F_;F_;Ff;Fe;Ftbl;Frho;").
Proof.
  intros rho tbl e f Ht Hf. induction tbl as [|[x v] rest IH]; cbn [tbl_upd]; [constructor|].
  inversion Ht as [|y l Hy Hrest]; subst.
  destruct (sv_eqb x e) eqn:E.
  - constructor; [|exact Hrest]. rewrite (sv_eqb_sound _ _ E) in Hy |- *.
    apply entry_ok_elim in Hy. destruct (Hf v Hy) as [A B]. apply entry_ok_intro; assumption.
  - constructor; [exact Hy | apply IH; exact Hrest].
Qed.

Lemma tbl_prop_u_ok : ltac2:(tb__ "0|0|
S4S25S51A1S23S23S3S0A2S3A2S44R3R2A2Sf7R4R2A2S44R5Se6R4R3A2A2F_;F_;Fr;Ftbl;Frho;").
Proof.
  intros rho tbl [[x d] y] Ht Hr. unfold tbl_prop_u. unfold rel_holds in Hr.
  pose proof (proj1 (tbl_get_sound rho tbl y Ht)) as Hy.
  set (hy := snd (fst (tbl_get tbl y))) in *.
  assert (Ht1 : tbl_ok rho (tbl_upd tbl x (fun v => entry_norm ((fst (fst v), Z.min (snd (fst v)) (hy - d)), snd v)))).
  { apply tbl_upd_ok; [exact Ht|]. intros [pu ps] [Hu Hs]. apply entry_norm_sound. cbn [fst snd] in *.
    split; [|exact Hs]. unfold in_itv in *. destruct pu as [l h]; cbn [fst snd] in *.
    destruct (fst (tbl_get tbl y)) as [ly hy0]; cbn [fst snd] in *. subst hy. lia. }
  set (tbl1 := tbl_upd tbl x _) in *.
  pose proof (proj1 (tbl_get_sound rho tbl1 x Ht1)) as Hx.
  apply tbl_upd_ok; [exact Ht1|]. intros [pu ps] [Hu Hs]. apply entry_norm_sound. cbn [fst snd] in *.
  split; [|exact Hs]. unfold in_itv in *. destruct pu as [l h]; cbn [fst snd] in *.
  destruct (fst (tbl_get tbl1 x)) as [lx hx]; cbn [fst snd] in *. lia.
Qed.

Lemma tbl_prop_s_ok : ltac2:(tb__ "0|0|
S4S25S51A1S23S23S3S0A2S3A2S44R3R2A2Sf6R4R2A2S44R5Se5R4R3A2A2F_;F_;Fr;Ftbl;Frho;").
Proof.
  intros rho tbl [[x d] y] Ht Hr. unfold tbl_prop_s. unfold srel_holds in Hr.
  pose proof (proj2 (tbl_get_sound rho tbl y Ht)) as Hy.
  set (hy := snd (snd (tbl_get tbl y))) in *.
  assert (Ht1 : tbl_ok rho (tbl_upd tbl x (fun v => entry_norm (fst v, (fst (snd v), Z.min (snd (snd v)) (hy - d)))))).
  { apply tbl_upd_ok; [exact Ht|]. intros [pu ps] [Hu Hs]. apply entry_norm_sound. cbn [fst snd] in *.
    split; [exact Hu|]. unfold in_sitv in *. destruct ps as [l h]; cbn [fst snd] in *.
    destruct (snd (tbl_get tbl y)) as [ly hy0]; cbn [fst snd] in *. subst hy. lia. }
  set (tbl1 := tbl_upd tbl x _) in *.
  pose proof (proj2 (tbl_get_sound rho tbl1 x Ht1)) as Hx.
  apply tbl_upd_ok; [exact Ht1|]. intros [pu ps] [Hu Hs]. apply entry_norm_sound. cbn [fst snd] in *.
  split; [exact Hu|]. unfold in_sitv in *. destruct ps as [l h]; cbn [fst snd] in *.
  destruct (snd (tbl_get tbl1 x)) as [lx hx]; cbn [fst snd] in *. lia.
Qed.

Lemma tbl_round_ok : ltac2:(tb__ "0|2|
S4S25S23S23S3S0A2S3A2M0A1M1G1S25S51A1S49G0Sf7R4A1R3A3S49G0Sf6R5A1R3A3S44R6R3A2S44R7Se7R6R5R4A3A2F_;F_;F_;Ftbl;Fsrels;Furels;Frho;").
Proof.
  intros rho urels srels tbl Hu Hs Ht. unfold tbl_round.
  assert (U1 : forall t, tbl_ok rho t -> tbl_ok rho (fold_left tbl_prop_u urels t)).
  { clear Ht tbl. induction urels as [|r rest IH]; intros t Ht; cbn [fold_left]; [exact Ht|].
    inversion Hu; subst. apply IH; [assumption|]. apply tbl_prop_u_ok; assumption. }
  assert (S1 : forall t, tbl_ok rho t -> tbl_ok rho (fold_left tbl_prop_s srels t)).
  { clear Ht tbl U1. induction srels as [|r rest IH]; intros t Ht; cbn [fold_left]; [exact Ht|].
    inversion Hs; subst. apply IH; [assumption|]. apply tbl_prop_s_ok; assumption. }
  apply S1. apply U1. exact Ht.
Qed.

Lemma tbl_iter_ok : ltac2:(tb__ "0|2|
S4S2aS25S23S23S3S0A2S3A2M0A1M1G1S25S51A1S49G0Sf7R5A1R3A3S49G0Sf6R6A1R3A3S44R7R3A2S44R8Se4R7R6R5R4A4A2F_;F_;F_;Ftbl;Fsrels;Furels;Fn;Frho;").
Proof.
  intros rho n. induction n as [|n IH]; intros urels srels tbl Hu Hs Ht; cbn [tbl_iter]; [exact Ht|].
  apply IH; [exact Hu | exact Hs |]. apply tbl_round_ok; assumption.
Qed.

Theorem mk_ctx_ok : ltac2:(tb__ "0|0|
S4S25S5A1S49S5S9R2A1R1A3Sf1R3S76R2A1A2F_;Ffacts;Frho;").
Proof.
  intros rho facts Hf. unfold mk_ctx.
  set (dg0 := mkDig facts (mk_cls facts) (mk_nes facts) (mk_bits facts) (rels_of facts) (srels_of facts) [] []).
  assert (H0 : dg_ok rho dg0).
  { unfold dg_ok, dgv_ok, dg0. cbn. repeat split; try constructor.
    - exact Hf.
    - apply mk_cls_sound. exact Hf.
    - apply mk_nes_sound. exact Hf.
    - apply mk_bits_sound. exact Hf.
    - apply rels_of_sound. exact Hf.
    - apply srels_of_sound. exact Hf. }
  destruct (endpoints (srels_of facts) (endpoints (rels_of facts) [])) as [|e es]; [exact H0|].
  pose proof (tbl_init_ok rho (e :: es) dg0 H0) as H1.
  apply dg_with_tbl_ok; [exact H1|].
  apply tbl_iter_ok; [| | apply dg_ok_tbl; exact H1].
  - apply dg_ok_urels in H0. exact H0.
  - apply dg_ok_srels in H0. exact H0.
Qed.

Lemma tbl_init_facts : ltac2:(tb__ "0|0|
S25S3A1S4cS1bS25S5A1S56S82R1R2A2A1S56R1A1A3Fd;Fl;").
Proof. induction l as [|x rest IH]; intros d; cbn [tbl_init]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma mk_ctx_facts : ltac2:(tb__ "0|1|
S25S5A1M0S1bG0S56S76R1A1A1R1A3Ffacts;").
Proof.
  intros facts. unfold mk_ctx.
  destruct (endpoints _ _) as [|e es]; [reflexivity|]. cbn [dg_with_tbl dg_facts].
  apply tbl_init_facts.
Qed.

Theorem stv_sound : ltac2:(tb__ "0|0|
S4S25S5A1S3S49S5S9R3A1R2A3Sf3SddR3R2A2S6R4R2A2A2F_;Fe;Ffacts;Frho;").
Proof. intros rho facts e Hf. unfold stv. apply stv_d_sound. apply mk_ctx_ok. exact Hf. Qed.

Theorem itv0_sound : ltac2:(tb__ "0|0|
S4S25S5A1S3S49S5S9R3A1R2A3S43S6bR3R2A2SfcQ40S7R4R2A2A2A2F_;Fe;Ffacts;Frho;").
Proof. intros rho facts e Hf. unfold itv0. apply (itv_d_sound rho). apply ctx0_dg_ok. exact Hf. Qed.

Lemma same_atoms_exact0 : ltac2:(tb__ "0|0|
S4S25S5A1S3S3S0S0S0S49S5S9R7A1R6A3S1bS26S0A1S57R6R5A2S27S0R4A2A3S1bS23S0S0A2S6bR8R6A2S28S0S0R4R3A4A3S32Z0S33R5R6A2A2S36S33R5R7A2S34Z2Z40A2A2S1bS0S42RcRaA2S33S42RcR9A2R8A2A3F_;F_;F_;F_;F_;Fh;Fl;Fd;Fx;Fa;Ffacts;Frho;").
Proof.
  intros rho facts a x d l h Hf Hs Hi Hl Hh.
  pose proof (itv0_sound rho facts x Hf) as I. rewrite Hi in I. unfold in_itv in I. cbn in I.
  rewrite (same_atoms_sound rho a x d Hs). unfold U in *. apply Z.mod_small. lia.
Qed.

Lemma small_u_sound : ltac2:(tb__ "0|1|
S4S25S5A1S3S0S49S5S9R4A1R3A3S1bS22Sd3R4R3R2A3S24A3S1cS32Z0SfcQ40S7R6R4A2A2M0A2S36G0S34Z2R3A2A2A2F_;F_;Fw;Fe;Ffacts;Frho;").
Proof.
  intros rho facts e w Hf H. unfold small_u in H. apply lazy_orb_prop in H as [H|H].
  - exact (small_u_t_sound rho (ctx0 facts) e w (ctx0_ok rho facts Hf) H).
  - pose proof (mk_ctx_ok rho facts Hf) as Hd.
    exact (small_u_t_sound rho _ e w (dg_ok_v _ _ Hd) H).
Qed.

Lemma swrap32_congr32 : ltac2:(tb__ "0|2|
S0S0S1bS0S35R2S34Z2Z20A2M0A2S35R1G0A2A3S1bS0SfbQ20M1R3A2SfbG1R2A2A3F_;Fb;Fa;").
Proof.
  intros a b H. rewrite <- (bv_swrap_wrap 32 a), <- (bv_swrap_wrap 32 b). f_equal.
  unfold bv_wrap. rewrite mod32. exact H.
Qed.

Lemma swrap_mod32 : ltac2:(tb__ "0|1|
S2S0S1eS1bS2R2Q20A3S1bS2R2Q40A3A2S1bS0S35SfbR3R2A2S34Z2Z20A2M0A2S35R2G0A2A3F_;Fz;Fn;").
Proof.
  intros n z Hn. unfold bv_swrap, bv_wrap.
  assert (E : exists k, bv_modulus n = k * 2 ^ 32 /\ 0 < k).
  { destruct Hn as [-> | ->]; [exists 1; split; [reflexivity|lia] | exists (2 ^ 32); split; [reflexivity|lia]]. }
  destruct E as (k & Ek & Hk). rewrite Ek.
  set (h := bv_half_modulus n).
  pose proof (Z_div_mod_eq_full (z + h) (k * 2 ^ 32)) as D.
  set (q := (z + h) / (k * 2 ^ 32)) in D.
  replace ((z + h) mod (k * 2 ^ 32) - h) with (z + (- (q * k)) * 2 ^ 32) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma mk_aluw_s_sound : ltac2:(tb__ "0|1|
S4S4cS105S3S3Sf1R5R4A2S1bSfaQ40M0A1S7R6SaeR5R4R3R2A4A2S115Q20G0S103R4S101S7R6R3A2A1S101S7R6R2A2A1A3A3A3F_;Fb;Fa;Fop;Fdg;Frho;").
Proof.
  intros rho dg op a b Hd. unfold mk_aluw_s.
  assert (ADDSUB : forall op', (op' = ALU_ADD \/ op' = ALU_SUB) ->
     eval rho (let r := mk_alu op' a b in let p := stv_t dg r in
               if (fst p <=? snd p) && in_i32 p then r else mk_aluw op' a b)
     = sext 64 (alu32 op' (low32 (eval rho a)) (low32 (eval rho b)))).
  { intros op' Hop. cbn zeta.
    pose proof (stv_d_sound rho dg (mk_alu op' a b) Hd) as ST.
    destruct (stv_t dg (mk_alu op' a b)) as [l h]. cbn [fst snd].
    destruct ((l <=? h) && in_i32 (l, h))%bool eqn:C; [|apply mk_aluw_sound].
    apply andb_prop in C as [C1 C2]. apply in_i32_spec in C2. cbn [fst snd] in C2.
    unfold in_sitv in ST. cbn [fst snd] in ST.
    change (sext 64 (alu32 op' (low32 (eval rho a)) (low32 (eval rho b)))) with (eval rho (SAluW op' a b)).
    apply soff_eq_eval. unfold soff in ST |- *. rewrite mk_alu_sound in ST |- *.
    change (bv_signed (alu64 op' (eval rho a) (eval rho b))) with (soff rho (SAlu op' a b)) in ST |- *.
    change (bv_signed (eval rho (SAluW op' a b))) with (soff rho (SAluW op' a b)).
    destruct Hop as [-> | ->].
    - rewrite alu_add_signed in ST |- *. rewrite aluw_add_signed.
      rewrite (swrap32_congr32 (bv_swrap 32 (soff rho a) + bv_swrap 32 (soff rho b)) (soff rho a + soff rho b)).
      2:{ rewrite Z.add_mod, !swrap_mod32, <- Z.add_mod by (lia || (left; reflexivity)). reflexivity. }
      rewrite (swrap32_congr32 (soff rho a + soff rho b) (bv_swrap 64 (soff rho a + soff rho b))).
      2:{ rewrite (swrap_mod32 64) by (right; reflexivity). reflexivity. }
      symmetry. apply swrap32_small. unfold i32min, i32max in *. lia.
    - rewrite alu_sub_signed in ST |- *. rewrite aluw_sub_signed.
      rewrite (swrap32_congr32 (bv_swrap 32 (soff rho a) - bv_swrap 32 (soff rho b)) (soff rho a - soff rho b)).
      2:{ rewrite Zminus_mod, !swrap_mod32, <- Zminus_mod by (lia || (left; reflexivity)). reflexivity. }
      rewrite (swrap32_congr32 (soff rho a - soff rho b) (bv_swrap 64 (soff rho a - soff rho b))).
      2:{ rewrite (swrap_mod32 64) by (right; reflexivity). reflexivity. }
      symmetry. apply swrap32_small. unfold i32min, i32max in *. lia. }
  destruct op; try apply mk_aluw_sound; apply ADDSUB; auto.
Qed.

Lemma mk_ext_s_sound : ltac2:(tb__ "0|0|
S4S4cS22S2S3Sf1R5R4A2S1bSfaQ40A1S7R6Sb0R5R4R3R2A4A2SeR4R3S7R6R2A2A3A3F_;Fa;Fw;Fsgn;Fdg;Frho;").
Proof.
  intros rho dg sgn w a Hd. unfold mk_ext_s.
  destruct sgn; [|apply mk_ext_sound]. destruct (N.eqb_spec w 32); [|apply mk_ext_sound]. subst w. cbn [andb].
  pose proof (stv_d_sound rho dg a Hd) as ST. destruct (stv_t dg a) as [l h]. cbn [fst snd].
  destruct ((l <=? h) && in_i32 (l, h))%bool eqn:C; [|apply mk_ext_sound].
  apply andb_prop in C as [C1 C2]. apply in_i32_spec in C2. cbn [fst snd] in C2.
  unfold in_sitv in ST. cbn [fst snd] in ST.
  apply bv_eq_signed. rewrite sext_low_signed by (cbn; lia). fold (soff rho a).
  symmetry. apply swrap32_small. unfold i32min, i32max in *. lia.
Qed.

Lemma mk_ext_f_sound : ltac2:(tb__ "0|0|
S4S25S5A1S22S2S3S49S5S9R5A1R4A3S1bSfaQ40A1S7R6SafR5R4R3R2A4A2SeR4R3S7R6R2A2A3A3F_;Fa;Fw;Fsgn;Ffacts;Frho;").
Proof.
  intros rho facts sgn w a Hf. unfold mk_ext_f. pose proof (mk_ctx_ok rho facts Hf) as Hd.
  pose proof (mk_ext_f_t_sound rho (ctx0 facts) sgn w a (ctx0_ok rho facts Hf)) as H0.
  destruct (mk_ext_f_t (ctx0 facts) sgn w a); try exact H0.
  pose proof (mk_ext_f_t_sound rho (mk_ctx facts) sgn w a (dg_ok_v _ _ Hd)) as H1.
  destruct (mk_ext_f_t (mk_ctx facts) sgn w a); try exact H1.
  apply mk_ext_s_sound. exact Hd.
Qed.

Lemma mk_aluw_f_sound : ltac2:(tb__ "0|1|
S4S25S5A1S105S3S3S49S5S9R5A1R4A3S1bSfaQ40M0A1S7R6SadR5R4R3R2A4A2S115Q20G0S103R4S101S7R6R3A2A1S101S7R6R2A2A1A3A3A3F_;Fb;Fa;Fop;Ffacts;Frho;").
Proof.
  intros rho facts op a b Hf. unfold mk_aluw_f. pose proof (mk_ctx_ok rho facts Hf) as Hd.
  pose proof (mk_aluw_f_t_sound rho (ctx0 facts) op a b (ctx0_ok rho facts Hf)) as H0.
  destruct (mk_aluw_f_t (ctx0 facts) op a b); try exact H0.
  pose proof (mk_aluw_f_t_sound rho (mk_ctx facts) op a b (dg_ok_v _ _ Hd)) as H1.
  destruct (mk_aluw_f_t (mk_ctx facts) op a b); try exact H1.
  apply mk_aluw_s_sound. exact Hd.
Qed.

Lemma wnorm_sound : ltac2:(tb__ "0|0|
S4S25S5A1S3S49S5S9R3A1R2A3S1bSfaQ40A1S7R4S62R3R2A2A2S7R4R2A2A3F_;Fe;Ffacts;Frho;").
Proof. intros rho facts e Hf. unfold wnorm. apply wnorm_t_sound. apply mk_ctx_ok. exact Hf. Qed.

Corollary soff_wnorm : ltac2:(tb__ "0|0|
S4S25S5A1S3S49S5S9R3A1R2A3S1bS0S6R4S62R3R2A2A2S6R4R2A2A3F_;Fe;Ffacts;Frho;").
Proof. intros. unfold soff. rewrite wnorm_sound by assumption. reflexivity. Qed.

Corollary U_wnorm : ltac2:(tb__ "0|0|
S4S25S5A1S3S49S5S9R3A1R2A3S1bS0S42R4S62R3R2A2A2S42R4R2A2A3F_;Fe;Ffacts;Frho;").
Proof. intros. unfold U. rewrite wnorm_sound by assumption. reflexivity. Qed.

Lemma lin_itv_sound : ltac2:(tb__ "0|2|
S4S4cS4bSf1R3R2A2S1cS32S29S0S0Sa4R3R2A2M0A3Sf2R4R2A2M1A2S32G1S2bS0S0G0A3A2A2F_;Fl;Fdg;Frho;").
Proof.
  intros rho dg l Hd. induction l as [|[k a] rest IH]; cbn [lin_itv]; [cbn; lia|].
  pose proof (itv_d_sound rho dg a Hd) as Ha. destruct (itv_t dg a) as [lo hi].
  destruct (lin_itv dg rest) as [l2 h2]. cbn [fst snd] in IH. unfold in_itv in Ha. cbn [fst snd] in Ha.
  rewrite linZ_cons. fold (U rho a) in Ha.
  destruct (Z.leb_spec 0 k); cbn [fst snd]; nia.
Qed.

Lemma lin_div_pos : ltac2:(tb__ "0|0|
S4bS4dS0S1bS26S0A1Sa0R3R2A2S27S0R1A2A3S36Z0R2A2F_;Fm;Fg;Fd;").
Proof.
  intros d [l c] m H. unfold lin_div in H. cbn [fst] in H. destruct l as [|[kg a] rest]; [discriminate|].
  destruct (0 <? lin_coef d a * kg) eqn:E1; [|discriminate].
  destruct (lin_coef d a mod kg =? 0) eqn:E2; [|discriminate]. injection H as <-.
  apply Z.ltb_lt in E1. apply Z.eqb_eq in E2.
  pose proof (Z_div_mod_eq_full (lin_coef d a) kg) as D. rewrite E2, Z.add_0_r in D.
  set (q := lin_coef d a / kg) in *. rewrite D in E1. nia.
Qed.

Lemma lin_lo_pool_sound : ltac2:(tb__ "0|0|
S4S4cS4bS25S4dA1S0Sf1R5R4A2S49S4dSf4R6A1R3A3S32R3Sf2R7R5A2A2S32Sa6R7R6R5R4A4Sf2R8R6A2A2F_;F_;F_;Facc;Fpool;Fd;Fdg;Frho;").
Proof.
  intros rho dg d pool. induction pool as [|g rest IH]; intros acc Hd Hp Hacc; cbn [lin_lo_pool]; [exact Hacc|].
  inversion Hp as [|g' r Hg Hrest]; subst. apply IH; [exact Hd | exact Hrest |].
  destruct (lin_div d g) as [m|] eqn:Em; [|exact Hacc]. pose proof (lin_div_pos _ _ _ Em) as M.
  unfold ineq_holds in Hg. pose proof (lin_itv_sound rho dg (lin_sub d (lin_scale m (fst g))) Hd) as R2.
  rewrite lin_sub_sound, lin_scale_sound in R2. apply Z.max_lub; [exact Hacc|]. nia.
Qed.

Lemma lin_lo_sound : ltac2:(tb__ "0|0|
S4S4cS4bSf1R3R2A2S32Sa5R3R2A2Sf2R4R2A2A2F_;Fd;Fdg;Frho;").
Proof.
  intros rho dg d Hd. unfold lin_lo. apply lin_lo_pool_sound; [exact Hd | apply dg_ok_pool; exact Hd |].
  exact (proj1 (lin_itv_sound rho dg d Hd)).
Qed.

Lemma lin_hi_sound : ltac2:(tb__ "0|0|
S4S4cS4bSf1R3R2A2S32Sf2R4R2A2Sa3R3R2A2A2F_;Fd;Fdg;Frho;").
Proof. intros rho dg d Hd. unfold lin_hi. pose proof (lin_lo_sound rho dg (lin_neg d) Hd) as L. rewrite lin_neg_sound in L. lia. Qed.

Lemma lin_geq_sound : ltac2:(tb__ "0|0|
S4S4cS4bS0Sf1R4R3A2S1bS22Sa2R4R3R2A3S24A3S32Z0S33Sf2R6R4A2R3A2A2F_;F_;Fc;Fd;Fdg;Frho;").
Proof. intros rho dg d c Hd H. unfold lin_geq in H. apply Z.leb_le in H. pose proof (lin_lo_sound rho dg d Hd). lia. Qed.

Lemma lin_exact_u_range : ltac2:(tb__ "0|1|
S4S4cS4bS0Sf1R4R3A2S1bS22S6fR4R3R2A3S24A3S1cS32Z0S33Sf2R6R4A2R3A2M0A2S36G0S34Z2Z40A2A2A2F_;F_;Fc;Fl;Fdg;Frho;").
Proof.
  intros rho dg l c Hd H. unfold lin_exact_u, M64 in H. pose proof (lin_itv_sound rho dg l Hd) as R.
  destruct (lin_itv dg l) as [lo hi]. cbn [fst snd] in R.
  apply lazy_andb_prop in H as [H1 H2]. apply Z.ltb_lt in H2. split; [|lia].
  apply lazy_orb_prop in H1 as [H1|H1]; [apply Z.leb_le in H1; lia | exact (lin_geq_sound rho dg l c Hd H1)].
Qed.

Lemma lin_exact_s_range : ltac2:(tb__ "0|1|
S4S4cS4bS0Sf1R4R3A2S1bS22S6eR4R3R2A3S24A3S1cS32S55S33Sf2R6R4A2R3A2M0A2S32G0S54A2A2F_;F_;Fc;Fl;Fdg;Frho;").
Proof.
  intros rho dg l c Hd H. unfold lin_exact_s in H. pose proof (lin_itv_sound rho dg l Hd) as R.
  destruct (lin_itv dg l) as [lo hi]. cbn [fst snd] in R.
  apply lazy_andb_prop in H as [H1 H2]. apply Z.leb_le in H2. split; [|lia].
  apply lazy_orb_prop in H1 as [H1|H1]; [apply Z.leb_le in H1; lia |].
  pose proof (lin_geq_sound rho dg l (c - smin) Hd H1). lia.
Qed.

Lemma lin_constfold_sound : ltac2:(tb__ "0|0|
S4S4cS4bS4bS0Sf1R5R4A2S1bS23S4bS0A2S9fR5R4A2S28S4bS0R3R2A4A3S1bS0Sf2R7R5A2S33Sf2R7R4A2R3A2A3F_;F_;Fc';Fl';Fl;Fdg;Frho;").
Proof.
  intros rho dg l. induction l as [|[k a] rest IH]; intros l' c' Hd H; cbn [lin_constfold] in H.
  - injection H as <- <-. cbn. lia.
  - destruct (lin_constfold dg rest) as [l0 c0] eqn:E. specialize (IH l0 c0 Hd eq_refl).
    destruct (itv_t dg a) as [lo hi] eqn:Ei.
    pose proof (itv_d_sound rho dg a Hd) as A. rewrite Ei in A. unfold in_itv in A. cbn [fst snd] in A.
    destruct (Z.eqb_spec lo hi).
    + injection H as <- <-. rewrite linZ_cons, IH. assert (U rho a = lo) by lia. rewrite H. lia.
    + injection H as <- <-. rewrite !linZ_cons, IH. lia.
Qed.

Lemma linz_sound : ltac2:(tb__ "0|0|
S4S4cS3S4bS0Sf1R5R4A2S1bS23S4bS0A2S5dR5R4A2S28S4bS0R3R2A4A3S1dS0S0S1bS0S33Sf2R8R5A2R4A2S33S42R8R6A2S37R1S34Z2Z40A2A2A2A3Lq;A2F_;F_;Fc;Fl;Fe;Fdg;Frho;").
Proof.
  intros rho dg e l c Hd H. unfold linz in H.
  destruct (lin_of0 (wnorm_t dg e)) as [l0 c0] eqn:E0. destruct (lin_constfold dg l0) as [l1 c1] eqn:E1.
  injection H as <- <-.
  destruct (lin_of0_sound rho _ l0 c0 E0) as [q Hq].
  rewrite (U_wnorm_t rho dg e Hd) in Hq. rewrite (lin_constfold_sound rho dg l0 l1 c1 Hd E1) in Hq. exists q. lia.
Qed.

Lemma linz_exact_u : ltac2:(tb__ "0|0|
S4S4cS3S4bS0Sf1R5R4A2S1bS23S4bS0A2S5dR5R4A2S28S4bS0R3R2A4A3S1bS22S6fR6R4R3A3S24A3S1bS0S42R8R6A2S33Sf2R8R5A2R4A2A3F_;F_;F_;Fc;Fl;Fe;Fdg;Frho;").
Proof.
  intros rho dg e l c Hd H He. destruct (linz_sound rho dg e l c Hd H) as [q Hq].
  pose proof (lin_exact_u_range rho dg l c Hd He). pose proof (U_range rho e). nia.
Qed.

Lemma signed_congr_eq : ltac2:(tb__ "0|2|
S0S0S1cS32S55R2A2S32R2S54A2A2M0G0S1bS0S35R4S34Z2Z40A2M1A2S35R3G1A2A3S1bS0R5R4A3F_;F_;F_;Fq;Fp;").
Proof.
  intros p q Hp Hq H. unfold smin, smax in *.
  pose proof (Z_div_mod_eq_full p (2 ^ 64)) as Dp. pose proof (Z_div_mod_eq_full q (2 ^ 64)) as Dq.
  pose proof (Z.mod_pos_bound p (2 ^ 64) ltac:(lia)).
  set (mp := p mod 2 ^ 64) in *. set (qp := p / 2 ^ 64) in *. set (qq := q / 2 ^ 64) in *.
  rewrite <- H in Dq. assert (qp = qq) by lia. lia.
Qed.

Lemma linz_exact_s : ltac2:(tb__ "0|0|
S4S4cS3S4bS0Sf1R5R4A2S1bS23S4bS0A2S5dR5R4A2S28S4bS0R3R2A4A3S1bS22S6eR6R4R3A3S24A3S1bS0S6R8R6A2S33Sf2R8R5A2R4A2A3F_;F_;F_;Fc;Fl;Fe;Fdg;Frho;").
Proof.
  intros rho dg e l c Hd H He. destruct (linz_sound rho dg e l c Hd H) as [q Hq].
  pose proof (lin_exact_s_range rho dg l c Hd He) as R. pose proof (soff_range rho e).
  apply signed_congr_eq; [unfold smin, smax; lia | exact R |].
  rewrite soff_mod. rewrite Hq. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. apply U_range.
Qed.

Lemma ineq_of_rel_sound : ltac2:(tb__ "0|0|
S4S4cS22S23S23S3S0A2S3A2S4dSf1R5R4A2S22OLsgn;R4Sf6R6R3A2Sf7R6R3A2X22x2S1bS26S4dA1S98R6R5R4A3S27S4dR3A2A3Sf4R8R4A2F_;F_;F_;Fg;Fr;Fsgn;Fdg;Frho;").
Proof.
  intros rho dg sgn [[x d] y] g Hd Hr H. unfold ineq_of_rel in H.
  destruct (lit_rel_skip dg x y); [discriminate|].
  destruct (linz dg x) as [lx cx] eqn:Ex. destruct (linz dg y) as [ly cy] eqn:Ey.
  unfold ineq_holds. destruct sgn.
  - destruct (lin_exact_s dg lx cx && lin_exact_s dg ly cy)%bool eqn:E; [|discriminate]. injection H as <-.
    apply andb_prop in E as [E1 E2]. cbn [fst snd]. rewrite lin_sub_sound.
    pose proof (linz_exact_s rho dg x lx cx Hd Ex E1). pose proof (linz_exact_s rho dg y ly cy Hd Ey E2).
    unfold srel_holds in Hr. lia.
  - destruct (lin_exact_u dg lx cx && lin_exact_u dg ly cy)%bool eqn:E; [|discriminate]. injection H as <-.
    apply andb_prop in E as [E1 E2]. cbn [fst snd]. rewrite lin_sub_sound.
    pose proof (linz_exact_u rho dg x lx cx Hd Ex E1). pose proof (linz_exact_u rho dg y ly cy Hd Ey E2).
    unfold rel_holds in Hr. lia.
Qed.

Lemma ineqs_of_rels_sound : ltac2:(tb__ "0|1|
S4S4cS22S25S23S23S3S0A2S3A2M0A1Sf1R4R3A2S49G0G0S22OLsgn;R4Sf6R6R1A2Sf7R6R1A2X22x2Lr;R2A3S49S4dSf4R6A1S99R5R4R3A3A3F_;F_;Frels;Fsgn;Fdg;Frho;").
Proof.
  intros rho dg sgn rels Hd Hr. induction rels as [|r rest IH]; cbn [ineqs_of_rels]; [constructor|].
  inversion Hr; subst. destruct (ineq_of_rel dg sgn r) as [g|] eqn:E.
  - constructor; [eapply ineq_of_rel_sound; eauto | apply IH; assumption].
  - apply IH; assumption.
Qed.

Definition neq_holds (rho : valuation) (h : ineq) : Prop := ltac2:(tb__ "0|0|
S1fS1bS0S33Sf2Vrho;S29S4bS0Vh;A3A2S2bS4bS0Vh;A3A2Z0A3A1").

Lemma neq_of_fact_sound : ltac2:(tb__ "0|1|
S4S5S3S3S9R4R3A2S1bS26S23S3S3A2M0A1Sb4R4A1S27G0S28S3S3R3R2A4A2A3S1fS1bSfaQ40A1S7R6R4A2S7R6R3A2A3A1F_;F_;Fy;Fx;Ff;Frho;").
Proof.
  intros rho f x y Hf H. unfold neq_of_fact in H.
  destruct f as [c a b|p|a b|a b|a b| |i al]; try discriminate.
  - destruct c; try discriminate. injection H as <- <-. cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf.
    apply Bool.negb_true_iff in Hf. apply Z.eqb_neq in Hf. intros X. apply Hf. rewrite X. reflexivity.
  - destruct p as [c a b|p|a b|a b|a b| |i al]; try discriminate.
    + destruct c; try discriminate. injection H as <- <-. cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf.
      intros X. apply Hf. rewrite X. apply Z.eqb_refl.
    + injection H as <- <-. cbn [holds] in Hf. exact Hf.
Qed.

Lemma neqs_of_sound : ltac2:(tb__ "0|0|
S4S4cS25S5A1Sf1R3R2A2S49S5S9R4A1R2A3S49S4dSf8R5A1Sb6R4R3A2A3F_;F_;Fall;Fdg;Frho;").
Proof.
  intros rho dg all Hd Ha. induction all as [|f rest IH]; cbn [neqs_of]; [constructor|].
  inversion Ha as [|f' l Hf Hrest]; subst. specialize (IH Hrest).
  destruct (neq_of_fact f) as [[x y]|] eqn:E; [|exact IH].
  pose proof (neq_of_fact_sound rho f x y Hf E) as NE.
  destruct (linz dg x) as [lx cx] eqn:Ex. destruct (linz dg y) as [ly cy] eqn:Ey.
  match goal with |- Forall _ (if ?c then _ else _) => destruct c eqn:C end; [|exact IH].
  constructor; [|exact IH]. unfold neq_holds. cbn [fst snd]. rewrite lin_sub_sound.
  apply orb_prop in C as [C|C]; apply andb_prop in C as [C1 C2].
  - pose proof (linz_exact_u rho dg x lx cx Hd Ex C1). pose proof (linz_exact_u rho dg y ly cy Hd Ey C2).
    intros X. apply NE. apply bv_eq. fold (U rho x) (U rho y). lia.
  - pose proof (linz_exact_s rho dg x lx cx Hd Ex C1). pose proof (linz_exact_s rho dg y ly cy Hd Ey C2).
    intros X. apply NE. apply soff_eq_eval. lia.
Qed.

Lemma lin_eqb_sound : ltac2:(tb__ "0|0|
S4S4bS4bS1bS22Sa1R2R1A2S24A3S1bS0Sf2R4R3A2Sf2R4R2A2A3F_;Fl2;Fl1;Frho;").
Proof. intros rho l1 l2 H. unfold lin_eqb in H. pose proof (lin_nil_sound rho _ H) as Z0. rewrite lin_sub_sound in Z0. lia. Qed.

Lemma ne_tighten1_sound : ltac2:(tb__ "0|0|
S4S25S4dA1S4dS49S4dSf8R3A1R2A3Sf4R4R2A2Sf4R5Sb3R4R3A2A2F_;F_;Fg;Fneqs;Frho;").
Proof.
  intros rho neqs [l c] Hn Hg. unfold ne_tighten1.
  match goal with |- ineq_holds _ (if ?b then _ else _) => destruct b eqn:E end; [|exact Hg].
  apply existsb_exists in E as [h [Hin Hh]]. rewrite Forall_forall in Hn. specialize (Hn h Hin).
  unfold ineq_holds, neq_holds in *. cbn [fst snd] in *.
  apply orb_prop in Hh as [Hh|Hh]; apply andb_prop in Hh as [H1 H2]; apply Z.eqb_eq in H2.
  - apply (lin_eqb_sound rho) in H1. lia.
  - apply (lin_nil_sound rho) in H1. rewrite lin_add_sound in H1. lia.
Qed.

Lemma ne_tighten_sound : ltac2:(tb__ "0|0|
S4S2aS25S4dA1S4dS49S4dSf8R4A1R2A3Sf4R5R2A2Sf4R6Sb2R5R4R3A3A2F_;F_;Fg;Fneqs;Fn;Frho;").
Proof.
  intros rho n. induction n as [|n IH]; intros neqs g Hn Hg; cbn [ne_tighten]; [exact Hg|].
  pose proof (ne_tighten1_sound rho neqs g Hn Hg) as H1.
  destruct (snd (ne_tighten1 neqs g) =? snd g); [exact Hg|]. apply IH; assumption.
Qed.

Lemma Forall_firstn : forall {A} (P : A -> Prop) n (l : list A), Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n l H. revert n. induction H; intros [|n]; cbn; try constructor; auto.
Qed.

Lemma opp_atom_pos : ltac2:(tb__ "0|2|
S4bS4bS0S0S1bS26S23S0S0A2M0A1Sb7R4R3A2S27G0S28S0S0R2R1A4A2A3S1cS36Z0M1R3A2S36G1R2A2A2F_;Fm2;Fm1;Fl2;Fl1;").
Proof.
  intros l1 l2 m1 m2. induction l1 as [|[k1 a] rest IH]; cbn [opp_atom]; intros H; [discriminate|].
  destruct (Z.ltb_spec (k1 * lin_coef l2 a) 0).
  - injection H as <- <-. nia.
  - apply IH. exact H.
Qed.

Lemma ineq_combine_sound : ltac2:(tb__ "0|0|
S4S4dS4dS4dSf4R4R3A2Sf4R5R3A2S1bS26S4dA1S97R5R4A2S27S4dR3A2A3Sf4R7R4A2F_;F_;F_;Fg;Fg2;Fg1;Frho;").
Proof.
  intros rho [l1 c1] [l2 c2] g H1 H2 H. unfold ineq_combine in H. cbn [fst snd] in H.
  destruct (opp_atom l1 l2) as [[m1 m2]|] eqn:E; [|discriminate].
  destruct (opp_atom_pos _ _ _ _ E) as [P1 P2]. injection H as <-.
  unfold ineq_holds in *. cbn [fst snd] in *. rewrite lin_add_sound, !lin_scale_sound.
  pose proof (Z.gcd_nonneg m1 m2) as G0.
  assert (G1 : Z.gcd m1 m2 <> 0) by (intros X; apply Z.gcd_eq_0_l in X; lia).
  assert (N1 : 0 <= m2 / Z.gcd m1 m2) by (apply Z.div_pos; lia).
  assert (N2 : 0 <= m1 / Z.gcd m1 m2) by (apply Z.div_pos; lia).
  nia.
Qed.

Lemma combine_all_sound : ltac2:(tb__ "0|1|
S4S25S4dA1M0G0S49S4dSf4R3A1R2A3S49S4dSf4R4A1R2A3S49S4dSf4R5A1S8cR4R3A2A3F_;F_;Fbase;Fnews;Frho;").
Proof.
  intros rho news base Hn Hb. induction news as [|g1 rest IH]; cbn [combine_all]; [constructor|].
  inversion Hn as [|g1' l Hg1 Hrest]; subst. specialize (IH Hrest).
  revert IH. generalize (combine_all rest base) as acc. intros acc Hacc.
  induction base as [|g2 base' IHb]; cbn [fold_right]; [exact Hacc|].
  inversion Hb as [|g2' l' Hg2 Hbase']; subst. specialize (IHb Hbase').
  destruct (ineq_combine g1 g2) as [g|] eqn:E; [|exact IHb].
  destruct (lin_nil (fst g)); [exact IHb|].
  constructor; [exact (ineq_combine_sound rho g1 g2 g Hg1 Hg2 E) | exact IHb].
Qed.

Lemma add_new_sound : ltac2:(tb__ "0|1|
S4S25S4dA1M0G0S49S4dSf4R3A1R1A3S49S4dSf4R4A1S86R3R2A2A3F_;Ffresh;Fpool;Frho;").
Proof.
  intros rho pool fresh Hf. revert pool. induction fresh as [|g rest IH]; intros pool; cbn [add_new]; [constructor|].
  inversion Hf; subst. destruct (ineq_subsumed pool g); [apply IH; assumption|].
  constructor; [assumption | apply IH; assumption].
Qed.

Lemma saturate_sound : ltac2:(tb__ "0|1|
S4S2aS25S4dA1M0G0G0G0S49S4dSf8R6A1R4A3S49S4dSf4R7A1R4A3S49S4dSf4R8A1R4A3S49S4dSf4R9A1R4A3S49S4dSf4RaA1Sc1R9R8R7R6R5A5A3F_;F_;F_;F_;Fbase;Fpool;Fnews;Fneqs;Fn;Frho;").
Proof.
  intros rho n. induction n as [|n IH]; intros neqs news pool base Hq Hn Hp Hb; cbn [saturate]; [exact Hp|].
  set (fresh := firstn pool_cap (add_new pool (map (ne_tighten (length neqs) neqs) (combine_all news base)))).
  assert (Hfresh : Forall (ineq_holds rho) fresh).
  { apply Forall_firstn. apply add_new_sound. apply Forall_map. eapply Forall_impl; [|apply combine_all_sound; [exact Hn | exact Hb]].
    intros g Hg. apply ne_tighten_sound; assumption. }
  apply IH; [exact Hq | exact Hfresh | | exact Hb]. apply Forall_app. split; assumption.
Qed.

Lemma lit_align_divide : ltac2:(tb__ "0|0|
S0S3aS34Z2SabR1A1A2R1A2Fk;").
Proof.
  intros k. pose proof (lit_align_sound k) as [A B].
  destruct B as [q Hq]. pose proof (Z_div_mod_eq_full k (2 ^ 64)) as E.
  exists (q + (k / 2 ^ 64) * 2 ^ (64 - lit_align k)).
  rewrite Z.mul_add_distr_r, <- Hq. rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia.
  replace (64 - lit_align k + lit_align k) with 64 by lia. lia.
Qed.

Lemma lin_align_sound : ltac2:(tb__ "0|1|
S4S25S5A1S4bS49S5S9R3A1R2A3S1cS1cS32Z0S9eR3R2A2M0A2S32G0Z40A2A2S3aS34Z2G0A2Sf2R4R2A2A2A2F_;Fl;Ffacts;Frho;").
Proof.
  intros rho facts l Hf. induction l as [|[k a] rest IH]; cbn [lin_align].
  - split; [lia|]. cbn. apply Z.divide_0_r.
  - destruct IH as [A D]. destruct (align_sum_sound rho facts a Hf) as [Aa Da]. pose proof (lit_align_sound k) as [Ak _].
    pose proof (lit_align_divide k) as Dk.
    split; [lia|]. rewrite linZ_cons. apply Z.divide_add_r.
    + assert (T : (2 ^ (align_sum facts a + lit_align k) | k * U rho a)%Z).
      { unfold U. destruct Dk as [qk Hk]. destruct Da as [qa Ha]. exists (qk * qa). rewrite Hk at 1. rewrite Ha.
        rewrite Z.pow_add_r by lia. lia. }
      eapply divide_pow2_le; [|exact T]. lia.
    + eapply divide_pow2_le; [|exact D]. lia.
Qed.

Lemma roundup_min : ltac2:(tb__ "0|0|
S0S0S0S36Z0R2A2S3aR3R2A2S32R5R3A2S32SbdR6R5A2R4A2F_;F_;F_;Fy;Fm;Fx;").
Proof.
  intros x m y Hm [q ->] Hxy. unfold roundup.
  apply Z.mul_le_mono_pos_r; [exact Hm|].
  assert ((x + m - 1) / m < q + 1); [|lia].
  apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Lemma lin_round_sound : ltac2:(tb__ "0|0|
S4S25S5A1S4dS49S5S9R3A1R2A3Sf4R4R2A2Sf4R5Sa9R4R3A2A2F_;F_;Fg;Ffacts;Frho;").
Proof.
  intros rho facts [l c] Hf Hg. unfold lin_round.
  destruct (Z.leb_spec 1 (lin_align facts l)); [|exact Hg]. destruct (Z.leb_spec (lin_align facts l) 64); [|exact Hg].
  unfold ineq_holds in *. cbn [fst snd] in *.
  destruct (lin_align_sound rho facts l Hf) as [A D].
  assert (P : 0 < 2 ^ lin_align facts l) by (apply Z.pow_pos_nonneg; lia).
  pose proof (roundup_min (- c) (2 ^ lin_align facts l) (linZ rho l) P D ltac:(lia)). lia.
Qed.

Lemma lin_gcd_divides : ltac2:(tb__ "0|1|
S4bS0S1cS3aS70R2R1A2R1A2S49S23S0S3A2M0G0S3aS70R3R2A2S29S0S3R1A3A2Lka;R2A3A2Facc;Fl;").
Proof.
  induction l as [|[k a] rest IH]; intros acc; cbn [lin_gcd].
  - split; [apply Z.divide_refl | constructor].
  - destruct (IH (Z.gcd k acc)) as [D F]. split.
    + eapply Z.divide_trans; [exact D | apply Z.gcd_divide_r].
    + constructor; [|exact F]. cbn [fst]. eapply Z.divide_trans; [exact D | apply Z.gcd_divide_l].
Qed.

Lemma linZ_div : ltac2:(tb__ "0|2|
S4S25S23S0S3A2M0A1S0S1fS1bS0R1Z0A3A1S49G0G0S3aR3S29S0S3R1A3M1A2Lka;R3A3S1bS0S37R3Sf2R5S4aG0G0G0S28S0S3S40G1R4A2S2bS0S3R1A3A4Lka;R4A4A2A2Sf2R5R4A2A3F_;F_;Fg;Fl;Frho;").
Proof.
  intros rho l g Hg F. induction l as [|[k a] rest IH]; [cbn; lia|].
  inversion F as [|x l' D F']; subst. cbn [fst] in D. specialize (IH F').
  destruct D as [q Hq]. subst k. cbn [map fst snd]. rewrite !linZ_cons. cbn [fst snd].
  rewrite Z.div_mul by exact Hg. rewrite <- IH. lia.
Qed.

Lemma neq_prim_sound : ltac2:(tb__ "0|0|
S4S4dSf8R2R1A2Sf8R3Sb5R2A1A2F_;Fh;Frho;").
Proof.
  intros rho [l c] H. unfold neq_prim.
  destruct (lin_gcd_divides l (Z.abs c)) as [Dc Dl]. set (g := lin_gcd l (Z.abs c)) in *.
  destruct (Z.ltb_spec 1 g); [|exact H].
  unfold neq_holds in *. cbn [fst snd] in *. intros E. apply H.
  pose proof (linZ_div rho l g ltac:(lia) Dl) as M.
  apply (proj1 (Z.divide_abs_r _ _)) in Dc. destruct Dc as [q Hq].
  assert (E' : g * (linZ rho (map (fun ka : Z * sv => (fst ka / g, snd ka)) l) + c / g) = 0) by (rewrite E; lia).
  rewrite Z.mul_add_distr_l, M in E'. rewrite Hq in E'. rewrite Z.div_mul in E' by lia. rewrite Hq. lia.
Qed.

Lemma pool_round_ok : ltac2:(tb__ "0|0|
S4S4cSf1R2R1A2S49S4dSf4R3A1Sb8R2A1A3F_;Fdg;Frho;").
Proof.
  intros rho dg Hd. unfold pool_round.
  pose proof (neqs_of_sound rho dg (dg_facts dg) Hd (dg_ok_facts _ _ Hd)) as Hq0.
  pose proof (dg_ok_facts _ _ Hd) as Hf.
  assert (Hq : Forall (neq_holds rho) (map neq_prim (neqs_of dg (dg_facts dg)))).
  { apply Forall_map. eapply Forall_impl; [intros h Hh; apply neq_prim_sound; exact Hh | exact Hq0]. }
  set (neqs := map neq_prim (neqs_of dg (dg_facts dg))) in *.
  set (base := add_new [] _).
  assert (Hb : Forall (ineq_holds rho) base).
  { apply add_new_sound. apply Forall_map.
    eapply Forall_impl; [intros g Hg; apply lin_round_sound; [exact Hf | exact Hg]|].
    apply Forall_map.
    eapply Forall_impl; [intros g Hg; apply ne_tighten_sound; [exact Hq | exact Hg]|].
    apply Forall_map.
    eapply Forall_impl; [intros g Hg; apply lin_round_sound; [exact Hf | exact Hg]|].
    apply Forall_app. split.
    - apply ineqs_of_rels_sound; [exact Hd|]. apply dg_ok_urels. exact Hd.
    - apply ineqs_of_rels_sound; [exact Hd|]. apply dg_ok_srels. exact Hd. }
  apply Forall_map. eapply Forall_impl; [intros g Hg; apply lin_round_sound; [exact Hf | exact Hg]|].
  apply saturate_sound; assumption.
Qed.

Lemma dg_with_pool_ok : ltac2:(tb__ "0|0|
S4S4cS25S4dA1Sf1R3R2A2S49S4dSf4R4A1R2A3Sf1R5S90R4R3A2A2F_;F_;Fpool;Fdg;Frho;").
Proof.
  intros rho dg pool ((A1 & A2 & A3 & A4 & A5) & B & C & D) Hp. unfold dg_ok, dgv_ok, dg_with_pool. cbn. repeat split; assumption.
Qed.

Lemma mk_pool_ok : ltac2:(tb__ "0|0|
S4S4cSf1R2R1A2S49S4dSf4R3A1Sb1R2A1A3F_;Fdg;Frho;").
Proof.
  intros rho dg Hd. unfold mk_pool. apply pool_round_ok. apply dg_with_pool_ok; [exact Hd|]. apply pool_round_ok. exact Hd.
Qed.

Theorem mk_dig_ok : ltac2:(tb__ "0|0|
S4S25S5A1S49S5S9R2A1R1A3Sf1R3S77R2A1A2F_;Ffacts;Frho;").
Proof.
  intros rho facts Hf. pose proof (mk_ctx_ok rho facts Hf) as Hd. unfold mk_dig.
  apply dg_with_pool_ok; [exact Hd|]. apply mk_pool_ok. exact Hd.
Qed.

Lemma mk_dig_facts : ltac2:(tb__ "0|1|
S25S5A1M0S1bG0S56S77R1A1A1R1A3Ffacts;").
Proof. intros. unfold mk_dig, dg_with_pool. cbn. apply mk_ctx_facts. Qed.

Lemma itv_lin_sound : ltac2:(tb__ "0|0|
S4S4cS3Sf1R3R2A2S43S9bR3R2A2S42R4R2A2A2F_;Fe;Fdg;Frho;").
Proof.
  intros rho dg e Hd. unfold itv_lin. pose proof (itv_d_sound rho dg e Hd) as I.
  destruct (linz dg e) as [l c] eqn:El.
  assert (G : in_itv (let lo := lin_lo dg l + c in let hi := lin_hi dg l + c in
                      if (0 <=? lo) &&& (hi <? M64) then itv_meet (itv_t dg e) (lo, hi) else itv_t dg e) (U rho e)).
  { cbn zeta. unfold M64. destruct (Z.leb_spec 0 (lin_lo dg l + c)); [|exact I].
    destruct (Z.ltb_spec (lin_hi dg l + c) (2 ^ 64)); [|exact I].
    apply in_meet; [exact I|]. destruct (linz_sound rho dg e l c Hd El) as [q Hq].
    pose proof (lin_lo_sound rho dg l Hd). pose proof (lin_hi_sound rho dg l Hd). pose proof (U_range rho e).
    unfold in_itv. cbn [fst snd]. nia. }
  destruct l as [|[k a] [|x rest]]; try exact G; try exact I;
    destruct k as [|[p|p|]|p]; try exact G; exact I.
Qed.

Theorem itv_sound : ltac2:(tb__ "0|0|
S4S25S5A1S3S49S5S9R3A1R2A3S43S6aR3R2A2SfcQ40S7R4R2A2A2A2F_;Fe;Ffacts;Frho;").
Proof. intros rho facts e Hf. unfold itv. apply (itv_lin_sound rho). apply mk_dig_ok. exact Hf. Qed.

Lemma uleq_lin_sound : ltac2:(tb__ "0|0|
S4S4cS3S0S3Sf1R5R4A2S1bS22SefR5R4R3R2A4S24A3S32S33S42R7R5A2R4A2S42R7R3A2A2F_;F_;Fb;Fk;Fa;Fdg;Frho;").
Proof.
  intros rho dg a k b Hd H. unfold uleq_lin in H.
  destruct (linz dg a) as [la ca] eqn:Ea. destruct (linz dg b) as [lb cb] eqn:Eb.
  apply lazy_andb_prop in H as [Xa H]. apply lazy_andb_prop in H as [Xb H].
  pose proof (linz_exact_u rho dg a la ca Hd Ea Xa). pose proof (linz_exact_u rho dg b lb cb Hd Eb Xb).
  pose proof (lin_geq_sound rho dg _ _ Hd H) as G. rewrite lin_sub_sound in G. lia.
Qed.

Lemma sleq_lin_sound : ltac2:(tb__ "0|0|
S4S4cS3S0S3Sf1R5R4A2S1bS22Sd0R5R4R3R2A4S24A3S32S33S6R7R5A2R4A2S6R7R3A2A2F_;F_;Fb;Fk;Fa;Fdg;Frho;").
Proof.
  intros rho dg a k b Hd H. unfold sleq_lin in H.
  destruct (linz dg a) as [la ca] eqn:Ea. destruct (linz dg b) as [lb cb] eqn:Eb.
  apply lazy_andb_prop in H as [Xa H]. apply lazy_andb_prop in H as [Xb H].
  pose proof (linz_exact_s rho dg a la ca Hd Ea Xa). pose proof (linz_exact_s rho dg b lb cb Hd Eb Xb).
  pose proof (lin_geq_sound rho dg _ _ Hd H) as G. rewrite lin_sub_sound in G. lia.
Qed.

Lemma same_atoms_exact_d : ltac2:(tb__ "0|0|
S4S4cS3S3S0S0S0Sf1R7R6A2S1bS26S0A1S57R6R5A2S27S0R4A2A3S1bS23S0S0A2S6cR8R6A2S28S0S0R4R3A4A3S32Z0S33R5R6A2A2S36S33R5R7A2S34Z2Z40A2A2S1bS0S42RcRaA2S33S42RcR9A2R8A2A3F_;F_;F_;F_;F_;Fh;Fl;Fd;Fx;Fa;Fdg;Frho;").
Proof.
  intros rho dg a x d l h Hd Hs Hi Hl Hh.
  pose proof (itv_d_sound rho dg x Hd) as I. rewrite Hi in I. unfold in_itv in I. cbn in I.
  rewrite (same_atoms_sound rho a x d Hs). unfold U in *. apply Z.mod_small. lia.
Qed.

Lemma same_atoms_exact : ltac2:(tb__ "0|0|
S4S25S5A1S3S3S0S0S0S49S5S9R7A1R6A3S1bS26S0A1S57R6R5A2S27S0R4A2A3S1bS23S0S0A2S6aR8R6A2S28S0S0R4R3A4A3S32Z0S33R5R6A2A2S36S33R5R7A2S34Z2Z40A2A2S1bS0S42RcRaA2S33S42RcR9A2R8A2A3F_;F_;F_;F_;F_;Fh;Fl;Fd;Fx;Fa;Ffacts;Frho;").
Proof.
  intros rho facts a x d l h Hf Hs Hi Hl Hh.
  pose proof (itv_sound rho facts x Hf) as I. rewrite Hi in I. unfold in_itv in I. cbn in I.
  rewrite (same_atoms_sound rho a x d Hs). unfold U in *. apply Z.mod_small. lia.
Qed.

Lemma uleq_by_rel_sound : ltac2:(tb__ "0|0|
S4S4cS3S0S3S23S23S3S0A2S3A2Sf1R6R5A2Sf7R7R2A2S1bS22SebR7R6R5R4R3A5S24A3S32S33S42R9R7A2R6A2S42R9R5A2A2F_;F_;F_;Fr;Fb;Fk;Fa;Fdg;Frho;").
Proof.
  intros rho dg a k b [[x d] y] Hd Hr H. unfold uleq_by_rel, M64 in H. unfold rel_holds in Hr.
  destruct (same_atoms a x) as [da|] eqn:Ea; [|discriminate].
  destruct (same_atoms b y) as [db|] eqn:Eb; [|discriminate].
  destruct (itv_t dg x) as [lx hx] eqn:Ix. destruct (itv_t dg y) as [ly hy] eqn:Iy.
  repeat (apply andb_prop in H as [H ?]).
  repeat match goal with
    | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
    | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
    end.
  rewrite (same_atoms_exact_d rho dg a x da lx hx Hd Ea Ix) by assumption.
  rewrite (same_atoms_exact_d rho dg b y db ly hy Hd Eb Iy) by assumption.
  lia.
Qed.

Lemma uleq_same_sound : ltac2:(tb__ "0|0|
S4S4cS3S0S3Sf1R5R4A2S1bS22Sf0R5R4R3R2A4S24A3S32S33S42R7R5A2R4A2S42R7R3A2A2F_;F_;Fb;Fk;Fa;Fdg;Frho;").
Proof.
  intros rho dg a k b Hd H. unfold uleq_same, M64 in H.
  destruct (same_atoms a b) as [d0|] eqn:Hs; [|discriminate].
  destruct (itv_t dg b) as [lb hb] eqn:Ib.
  repeat (apply andb_prop in H as [H ?]).
  apply Z.leb_le in H. apply Z.leb_le in H2. apply Z.ltb_lt in H1. apply Z.leb_le in H0.
  pose proof (same_atoms_sound rho a b d0 Hs) as E.
  pose proof (itv_d_sound rho dg b Hd) as I. rewrite Ib in I. unfold in_itv in I. cbn in I.
  pose proof (U_range rho a) as Ra. pose proof (U_range rho b) as Rb.
  pose proof (snorm_mod d0) as M. pose proof (snorm_range d0) as R.
  assert (E' : U rho a = (U rho b + snorm d0) mod 2 ^ 64).
  { rewrite E. rewrite <- Zplus_mod_idemp_r, <- M, Zplus_mod_idemp_r. reflexivity. }
  unfold U in *. rewrite Z.mod_small in E' by lia. lia.
Qed.

Lemma sub_atoms_sound : ltac2:(tb__ "0|2|
S4S3S3S0S25S3A1M0S1bS26S23S0G0A2M1A1Se0R4R3A2S27G1S28S0G0R2R1A4A2A3S1bS0S42R6R4A2S35S38S33S42R6R5A2S46R6R2A2A2R3A2S34Z2Z40A2A2A3F_;Fextra;Fda;Fx;Fa;Frho;").
Proof.
  intros rho a x da extra H. unfold sub_atoms in H.
  destruct (atoms_of a [] 0) as [aa ca] eqn:Ea.
  destruct (atoms_of x [] 0) as [xa cx] eqn:Ex.
  destruct (remove_atoms aa xa) as [ex|] eqn:Er; [|discriminate].
  injection H as <- <-.
  pose proof (remove_atoms_sound rho _ _ _ Er) as R.
  rewrite (atoms_of_sound0 rho a aa ca Ea), (atoms_of_sound0 rho x xa cx Ex).
  replace ((sumZ rho aa + ca) mod 2 ^ 64 + sumZ rho ex - (ca - cx))
    with ((sumZ rho aa + ca) mod 2 ^ 64 + (sumZ rho ex - (ca - cx))) by lia.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma itv_sum_sound : ltac2:(tb__ "0|1|
S4S4cS25S3A1S0S0Sf1R5R4A2S1bS23S0S0A2S9cR5R4A2S28S0S0R3R2A4A3S1cS32R4S46R7R5A2M0A2S32G0R3A2A2F_;F_;Fhi;Flo;Fl;Fdg;Frho;").
Proof.
  intros rho dg l. induction l as [|e rest IH]; intros lo hi Hd H; cbn [itv_sum] in H.
  - injection H as <- <-. cbn. lia.
  - destruct (itv_t dg e) as [l1 h1] eqn:I1. destruct (itv_sum dg rest) as [l2 h2] eqn:I2.
    injection H as <- <-. specialize (IH l2 h2 Hd eq_refl).
    pose proof (itv_d_sound rho dg e Hd) as A. rewrite I1 in A. unfold in_itv in A. cbn in A.
    cbn [sumZ fold_right]. unfold sumZ in IH. unfold U in A. lia.
Qed.

Lemma uleq_by_rel2_sound : ltac2:(tb__ "0|0|
S4S4cS3S0S3S23S23S3S0A2S3A2Sf1R6R5A2Sf7R7R2A2S1bS22SecR7R6R5R4R3A5S24A3S32S33S42R9R7A2R6A2S42R9R5A2A2F_;F_;F_;Fr;Fb;Fk;Fa;Fdg;Frho;").
Proof.
  intros rho dg a k b [[x d] y] Hd Hr H. unfold uleq_by_rel2, M64 in H. unfold rel_holds in Hr.
  destruct (sub_atoms a x) as [[da extra]|] eqn:Es; [|discriminate].
  destruct (itv_t dg a) as [la ha] eqn:Ia.
  destruct (itv_sum dg extra) as [el eh] eqn:Ie.
  destruct (itv_t dg y) as [ly hy] eqn:Iy.
  pose proof (itv_d_sound rho dg a Hd) as A. rewrite Ia in A. unfold in_itv in A. cbn in A.
  pose proof (itv_d_sound rho dg y Hd) as Y. rewrite Iy in Y. unfold in_itv in Y. cbn in Y.
  pose proof (itv_sum_sound rho dg extra el eh Hd Ie) as E.
  pose proof (sub_atoms_sound rho a x da extra Es) as X.
  pose proof (U_range rho a) as Ra. pose proof (U_range rho b) as Rb.
  pose proof (U_range rho x) as Rx. pose proof (U_range rho y) as Ry.
  apply andb_prop in H as [H Hend].
  repeat (apply andb_prop in H as [H ?]).
  repeat match goal with
    | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
    | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
    end.
  unfold U in *. rewrite Z.mod_small in X by lia.
  destruct (same_atoms b y) as [db|] eqn:Eb.
  - repeat (apply andb_prop in Hend as [Hend ?]).
    repeat match goal with
      | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
      | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
      end.
    pose proof (same_atoms_exact_d rho dg b y db ly hy Hd Eb Iy) as B. unfold U in B.
    rewrite B by assumption. lia.
  - destruct (itv_t dg b) as [lb hb] eqn:Ib.
    pose proof (itv_d_sound rho dg b Hd) as B. rewrite Ib in B. unfold in_itv, U in B. cbn in B.
    apply andb_prop in Hend as [_ Hend]. apply Z.leb_le in Hend. lia.
Qed.

Lemma strip_zext_sound : ltac2:(tb__ "0|0|
S4S4cS3Sf1R3R2A2S1bS0S42R4SdcR3R2A2A2S42R4R2A2A3F_;Fe;Fdg;Frho;").
Proof.
  intros rho dg e Hd. induction e; cbn [strip_zext]; try reflexivity.
  destruct sgn; [reflexivity|].
  destruct (Z.leb_spec (Z.of_N w) 64); [|reflexivity].
  destruct (small_u_t dg e (Z.of_N w)) eqn:Hs; [|reflexivity].
  rewrite IHe. pose proof (small_u_t_sound rho dg e (Z.of_N w) (dg_ok_v _ _ Hd) Hs) as B.
  unfold U. cbn [eval]. unfold ext_low, zext. rewrite bv_zero_extend_unsigned', bv_extract_unsigned.
  unfold bv_wrap, bv_modulus. rewrite two64 || idtac. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  rewrite (Z.mod_small _ (2 ^ Z.of_N w)) by lia.
  replace (Z.of_N 64) with 64 by reflexivity. rewrite Z.mod_small by (pose proof (urange (eval rho e)); lia). reflexivity.
Qed.

Lemma remu_lt_sound : ltac2:(tb__ "0|0|
S4S4cS3S3Sf1R4R3A2S1bS22SbcR4R3R2A3S24A3S36S42R6R4A2S42R6R3A2A2F_;F_;Fb;Fe;Fdg;Frho;").
Proof.
  intros rho dg e b Hd H. unfold remu_lt in H.
  pose proof (itv_d_sound rho dg b Hd) as Ib. destruct (itv_t dg b) as [lb hb]. unfold in_itv in Ib. cbn [fst snd] in Ib, H.
  destruct e as [| | | |op a b'|op a b'| |]; try discriminate; destruct op; try discriminate.
  - destruct (sv_eqb b' b) eqn:E; [|discriminate]. rewrite (sv_eqb_sound _ _ E).
    destruct (Z.ltb_spec 0 lb); [|discriminate].
    unfold U. cbn [eval]. unfold mul_div. destruct (Z.eqb_spec (bv_unsigned (eval rho b)) 0); [unfold U in Ib; lia|].
    rewrite bv_modu_unsigned. pose proof (Z.mod_pos_bound (bv_unsigned (eval rho a)) (bv_unsigned (eval rho b)) ltac:(unfold U in Ib; lia)). lia.
  - destruct (sv_eqb b' b) eqn:E; [|discriminate]. rewrite (sv_eqb_sound _ _ E).
    destruct (Z.ltb_spec 0 lb); [|discriminate]. destruct (Z.ltb_spec hb (2 ^ 31)); [|discriminate].
    unfold U in *. cbn [eval]. unfold mul_div. rewrite !low32_umod.
    rewrite (Z.mod_small (bv_unsigned (eval rho b))) by (pose proof (urange (eval rho b)); lia).
    destruct (Z.eqb_spec (bv_unsigned (eval rho b)) 0); [lia|].
    pose proof (Z.mod_pos_bound (bv_unsigned (eval rho a)) (2 ^ 32) ltac:(lia)) as M1.
    assert (HM : bv_unsigned (bv_modu (low32 (eval rho a)) (low32 (eval rho b))) = (bv_unsigned (eval rho a) mod 2 ^ 32) mod bv_unsigned (eval rho b)).
    { rewrite bv_modu_unsigned, !low32_umod. rewrite (Z.mod_small (bv_unsigned (eval rho b))) by (pose proof (urange (eval rho b)); lia). reflexivity. }
    pose proof (Z.mod_pos_bound (bv_unsigned (eval rho a) mod 2 ^ 32) (bv_unsigned (eval rho b)) ltac:(lia)) as MB.
    rewrite sext64_32_small by (rewrite HM; lia). rewrite HM. lia.
Qed.

Theorem uleq_core_sound : ltac2:(tb__ "0|0|
S4S4cS3S0S3Sf1R5R4A2S1bS22SedR5R4R3R2A4S24A3S32S33S42R7R5A2R4A2S42R7R3A2A2F_;F_;Fb;Fk;Fa;Fdg;Frho;").
Proof.
  intros rho dg a k b Hd H. unfold uleq_core in H.
  destruct (itv_t dg a) as [la ha] eqn:Ia. destruct (itv_t dg b) as [lb hb] eqn:Ib.
  apply lazy_orb_prop in H as [H|H].
  { pose proof (itv_d_sound rho dg a Hd) as A. rewrite Ia in A.
    pose proof (itv_d_sound rho dg b Hd) as B. rewrite Ib in B.
    unfold in_itv, U in A, B. cbn in A, B.
    repeat (apply andb_prop in H as [H ?]).
    repeat match goal with | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H end.
    unfold U. lia. }
  apply lazy_orb_prop in H as [H|H]; [exact (uleq_same_sound rho dg a k b Hd H)|].
  apply lazy_orb_prop in H as [H|H]; [exact (uleq_lin_sound rho dg a k b Hd H)|].
  pose proof (dg_ok_urels rho dg Hd) as RS. rewrite Forall_forall in RS.
  apply lazy_orb_prop in H as [H|H].
  - apply existsb_exists in H as [r [Hin Hr]]. exact (uleq_by_rel_sound rho dg a k b r Hd (RS r Hin) Hr).
  - apply lazy_orb_prop in H as [H|H].
    + apply existsb_exists in H as [r [Hin Hr]]. exact (uleq_by_rel2_sound rho dg a k b r Hd (RS r Hin) Hr).
    + apply lazy_andb_prop in H as [Hk H]. apply Z.leb_le in Hk.
      pose proof (remu_lt_sound rho dg _ b Hd H) as L. rewrite strip_zext_sound in L by exact Hd. lia.
Qed.

Lemma shr_arg_sound : ltac2:(tb__ "0|1|
S4S4cS3S3S0Sf1R5R4A2S1bS26S23S3S0A2M0A1Sc7R5R4A2S27G0S28S3S0R3R2A4A2A3S1cS1cS32Z0R3A2S36R3Z40A2A2S1bS0S42R7R5A2S3eS42R7R4A2R3A2A3A2F_;F_;Fs;Fx;Fe;Fdg;Frho;").
Proof.
  intros rho dg e x s Hd H. unfold shr_arg in H.
  destruct e as [| |op a b'|op a b'| | | |]; try discriminate; destruct op; try discriminate;
    destruct b' as [s'| | | | | | |]; try discriminate.
  - destruct (Z.leb_spec 0 s'); [|discriminate]. destruct (Z.ltb_spec s' 64); [|discriminate].
    injection H as <- <-. split; [lia|]. unfold U. cbn [eval]. rewrite srl_val.
    rewrite (Z.mod_small s') by lia. reflexivity.
  - destruct (Z.leb_spec 1 s'); [|discriminate]. destruct (Z.ltb_spec s' 32); [|discriminate].
    destruct (small_u_t dg a 32) eqn:Hs; [|discriminate].
    injection H as <- <-. split; [lia|].
    pose proof (small_u_t_sound rho dg a 32 (dg_ok_v _ _ Hd) Hs) as Ba.
    unfold U. cbn [eval]. unfold alu32, alu.
    assert (M : bv_unsigned (bv_and (low32 (Z_to_bv 64 s')) (Z_to_bv 32 31)) = s').
    { rewrite bv_and_unsigned, low32_umod. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
      change (bv_modulus 32) with (2 ^ 32).
      rewrite (Z.mod_small s' (2 ^ 64)) by lia. rewrite (Z.mod_small s' (2 ^ 32)) by lia.
      change (31 mod 2 ^ 32) with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
    assert (R : bv_unsigned (bv_shiftr (low32 (eval rho a)) (bv_and (low32 (Z_to_bv 64 s')) (Z_to_bv 32 31)))
                = Z.shiftr (bv_unsigned (eval rho a)) s').
    { rewrite bv_shiftr_unsigned, M, low32_umod. rewrite (Z.mod_small (bv_unsigned (eval rho a))) by lia. reflexivity. }
    assert (B : 0 <= Z.shiftr (bv_unsigned (eval rho a)) s' < 2 ^ 31).
    { split; [apply Z.shiftr_nonneg; lia|].
      rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
      apply (Z.lt_le_trans _ (2 ^ 32)); [lia|]. rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
    rewrite sext64_32_small by (rewrite R; lia).
    exact R.
Qed.

Lemma shr_mono_sound : ltac2:(tb__ "0|0|
S4S4cS3S0S3Sf1R5R4A2S1bS22Sc8R5R4R3R2A4S24A3S32S33S42R7R5A2R4A2S42R7R3A2A2F_;F_;Fb;Fk;Fa;Fdg;Frho;").
Proof.
  intros rho dg a k b Hd H. unfold shr_mono in H.
  destruct (shr_arg dg a) as [[x s]|] eqn:Ea; [|discriminate].
  destruct (shr_arg dg b) as [[y s']|] eqn:Eb; [|discriminate].
  destruct (Z.eqb_spec s s'); [|discriminate]. subst s'.
  destruct (Z.leb_spec 0 k); [|discriminate].
  destruct (shr_arg_sound rho dg a x s Hd Ea) as [Hs ->].
  destruct (shr_arg_sound rho dg b y s Hd Eb) as [_ ->].
  pose proof (uleq_core_sound rho dg _ (k * 2 ^ s) y Hd H) as C. rewrite strip_zext_sound in C by exact Hd.
  rewrite !Z.shiftr_div_pow2 by lia.
  assert (P : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  apply (Z.le_trans _ ((U rho x + k * 2 ^ s) / 2 ^ s)).
  - rewrite Z.div_add by lia. lia.
  - apply Z.div_le_mono; lia.
Qed.

Lemma sv_replace_sound : ltac2:(tb__ "0|1|
S4S3S3S3S1bSfaQ40A1M0S7R4R3A2S7R4R2A2A3S1bG0S7R5Se2R4R3R2A3A2S7R5R2A2A3F_;Fe;Fu;Ft;Frho;").
Proof.
  intros rho t u e Htu. induction e; cbn [sv_replace];
    (destruct (sv_eqb _ t) eqn:E; [apply sv_eqb_sound in E; rewrite E; symmetry; exact Htu|]);
    cbn [eval]; rewrite ?IHe1, ?IHe2, ?IHe; reflexivity.
Qed.

Lemma is_selmask_sound : ltac2:(tb__ "0|2|
S4S3S3S1bS26S3A1S9aR2A1S27S3R1A2A3S1bS0SfcQ40M0S7R4R3A2A2S22S0L_;S3dSfcG0S7R4R2A2A2Z0M1A2G1S38S34Z2Z40A2Z1A2X22x2A3F_;Fz;Fe;Frho;").
Proof.
  intros rho e z H. unfold is_selmask in H.
  destruct e as [| |op a b| | | | |]; try discriminate. destruct op; try discriminate.
  destruct a as [| |opa a1 a2| | | | |]; try discriminate. destruct opa; try discriminate.
  destruct a2 as [c1| | | | | | |]; try discriminate. destruct b as [m| | | | | | |]; try discriminate.
  destruct (Z.eqb_spec (zmod64 c1) 1) as [E1|]; [|discriminate]. destruct (Z.eqb_spec (zmod64 m) MAXU) as [Em|]; [|discriminate].
  injection H as <-. rewrite zmod64_eq in E1, Em. unfold MAXU in Em.
  pose proof (urange (eval rho a1)) as Rz.
  cbn [eval]. rewrite add_val. unfold alu64 at 1. unfold alu, bv_ltu.
  rewrite (Z_to_bv_unsigned 64 c1), (Z_to_bv_unsigned 64 m). unfold bv_wrap. rewrite two64, E1, Em.
  destruct (Z.eqb_spec (bv_unsigned (eval rho a1)) 0) as [Ez|Ez].
  - rewrite Ez. change (0 <? 1) with true. cbn iota. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. reflexivity.
  - destruct (Z.ltb_spec (bv_unsigned (eval rho a1)) 1); [lia|]. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. reflexivity.
Qed.

Lemma sel_here_sound : ltac2:(tb__ "0|5|
S4S3S3S3S3S1bS26S23S23S3S3A2M0S3A2M1A1Sc4R4A1S27G1S28G0S3S28S3S3R3R2A4R1A4A2A3S1cS1bS3R4R5A3S1bSfaQ40M2A1M3S7R6R5A2S22G3L_;S3dSfcG2S7R6R3A2A2Z0M4A2SfdG2G4A2S7R6R2A2X22x2A3A2F_;Fy;Fz;Fsel;Fe;Frho;").
Proof.
  intros rho e sel z y H. unfold sel_here in H.
  destruct e as [| |op a b| | | | |]; try discriminate. destruct op; try discriminate.
  pose proof (urange (eval rho a)) as Ra. pose proof (urange (eval rho b)) as Rb.
  destruct (is_selmask a) as [z'|] eqn:Ea.
  - injection H as <- -> <-. split; [reflexivity|]. pose proof (is_selmask_sound rho a z Ea) as S.
    cbn [eval]. apply bv_eq. rewrite and_val, S. destruct (bv_unsigned (eval rho z) =? 0).
    + rewrite Z.land_0_l. rewrite Z_to_bv_unsigned. reflexivity.
    + change (2 ^ 64 - 1) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
  - destruct (is_selmask b) as [z'|] eqn:Eb; [|discriminate].
    injection H as <- -> <-. split; [reflexivity|]. pose proof (is_selmask_sound rho b z Eb) as S.
    cbn [eval]. apply bv_eq. rewrite and_val, S. destruct (bv_unsigned (eval rho z) =? 0).
    + rewrite Z.land_0_r. rewrite Z_to_bv_unsigned. reflexivity.
    + change (2 ^ 64 - 1) with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma find_sel_sound : ltac2:(tb__ "0|5|
S4S3S3S3S3S1bS26S23S23S3S3A2M0S3A2M1A1S95R4A1S27G1S28G0S3S28S3S3R3R2A4R1A4A2A3S1bSfaQ40M2A1M3S7R6R4A2S22G3L_;S3dSfcG2S7R6R3A2A2Z0M4A2SfdG2G4A2S7R6R2A2X22x2A3F_;Fy;Fz;Fsel;Fe;Frho;").
Proof.
  intros rho e. induction e; intros sel zz yy H; cbn [find_sel] in H;
    (destruct (sel_here _) as [[[sel' z'] y']|] eqn:Eh;
      [ injection H as <- <- <-; destruct (sel_here_sound rho _ _ _ _ Eh) as [-> X]; exact X | ]);
    try discriminate;
    first [ destruct (find_sel e1) as [r|] eqn:E1; [injection H as ->; exact (IHe1 _ _ _ eq_refl) | exact (IHe2 _ _ _ H)]
          | exact (IHe _ _ _ H) ].
Qed.

Lemma sel_case_sound : ltac2:(tb__ "0|0|
S4S4cS3S0S3Sf1R5R4A2S1bS22Sc3R5R4R3R2A4S24A3S32S33S42R7R5A2R4A2S42R7R3A2A2F_;F_;Fb;Fk;Fa;Fdg;Frho;").
Proof.
  intros rho dg a k b Hd H. unfold sel_case in H.
  destruct (find_sel a) as [[[sel z] y]|] eqn:Ef; [|discriminate].
  apply lazy_andb_prop in H as [H0 H1].
  pose proof (find_sel_sound rho a sel z y Ef) as Hsel.
  destruct (Z.eqb_spec (bv_unsigned (eval rho z)) 0) as [Ez|Ez].
  - pose proof (uleq_core_sound rho dg _ k b Hd H0) as C.
    unfold U in C |- *. rewrite (sv_replace_sound rho sel (SLit 0) a) in C by (rewrite Hsel; reflexivity). exact C.
  - assert (Hd' : dg_ok rho (mk_dig (SPBranch BC_NE z (SLit 0) :: dg_facts dg))).
    { apply mk_dig_ok. constructor; [|exact (dg_ok_facts _ _ Hd)].
      cbn [holds branch_taken eval]. unfold bv_eqb. rewrite (Z_to_bv_unsigned 64 0). unfold bv_wrap. rewrite two64.
      rewrite Z.mod_0_l by lia. destruct (Z.eqb_spec (bv_unsigned (eval rho z)) 0); [lia|reflexivity]. }
    pose proof (uleq_core_sound rho _ _ k b Hd' H1) as C.
    unfold U in C |- *. rewrite (sv_replace_sound rho sel y a) in C by (rewrite Hsel; reflexivity). exact C.
Qed.

Lemma aligned_tighten_sound : ltac2:(tb__ "0|0|
S4S4cS3S0S3Sf1R5R4A2S1bS22S87R5R4R3R2A4S24A3S32S33S42R7R5A2R4A2S42R7R3A2A2F_;F_;Fb;Fk;Fa;Fdg;Frho;").
Proof.
  intros rho dg a k b Hd H. unfold aligned_tighten in H.
  set (j := Z.min (align_sum (dg_facts dg) a) (align_sum (dg_facts dg) b)) in H.
  destruct (Z.leb_spec 1 j); [|discriminate]. destruct (Z.leb_spec k (2 ^ j)); [|discriminate].
  pose proof (uleq_core_sound rho dg a 1 b Hd H) as C.
  pose proof (dg_ok_facts _ _ Hd) as Hf.
  destruct (align_sum_sound rho (dg_facts dg) a Hf) as [Aa [qa Da]].
  destruct (align_sum_sound rho (dg_facts dg) b Hf) as [Ab [qb Db]].
  unfold U in *.
  assert (Pa : (2 ^ j | bv_unsigned (eval rho a))%Z).
  { eapply divide_pow2_le; [|exists qa; exact Da]. lia. }
  assert (Pb : (2 ^ j | bv_unsigned (eval rho b))%Z).
  { eapply divide_pow2_le; [|exists qb; exact Db]. lia. }
  destruct Pa as [pa Ea]. destruct Pb as [pb Eb]. rewrite Ea, Eb in *.
  assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  assert (pa < pb) by nia. nia.
Qed.

Theorem uleq_d_sound : ltac2:(tb__ "0|0|
S4S4cS3S0S3Sf1R5R4A2S1bS22SeeR5R4R3R2A4S24A3S32S33S42R7R5A2R4A2S42R7R3A2A2F_;F_;Fb;Fk;Fa;Fdg;Frho;").
Proof.
  intros rho dg a k b Hd H. unfold uleq_d in H.
  rewrite <- (strip_zext_sound rho dg a Hd).
  apply lazy_orb_prop in H as [H|H]; [exact (uleq_core_sound rho dg _ k b Hd H)|].
  apply lazy_orb_prop in H as [H|H]; [exact (shr_mono_sound rho dg _ k b Hd H)|].
  apply lazy_orb_prop in H as [H|H]; [exact (sel_case_sound rho dg _ k b Hd H)|].
  exact (aligned_tighten_sound rho dg _ k b Hd H).
Qed.

Theorem uleq_sound : ltac2:(tb__ "0|0|
S4S25S5A1S3S0S3S49S5S9R5A1R4A3S1bS22SeaR5R4R3R2A4S24A3S32S33S42R7R5A2R4A2S42R7R3A2A2F_;F_;Fb;Fk;Fa;Ffacts;Frho;").
Proof.
  intros rho facts a k b Hf H. unfold uleq in H. apply lazy_orb_prop in H as [H|H].
  - eapply uleq_d_sound; [apply ctx0_dg_ok; exact Hf | exact H].
  - eapply uleq_d_sound; [apply mk_dig_ok; exact Hf | exact H].
Qed.

Lemma sitv_of_sound : ltac2:(tb__ "0|5|
S4S3S23S0S0A2M0S0S0S43R3S42R5R4A2A2S1bS26G0A1ScbR4A1S27G0S28S0S0R3R2A4A2A3S1cS1cS32R4S6R7R6A2M1A2S32G1R3A2A2S1cS32Z0M2R4A2S1bS0S6R8R7A2M3S42R8R7A2M4A3F_;S36R3G2A2S1bS0G3S38G4S34Z2Z40A2A2A3F_;A2A2F_;F_;Fh;Fl;Fp;Fe;Frho;").
Proof.
  intros rho e [l0 h0] l h I H. unfold sitv_of, M63, M64 in H. unfold in_itv in I. cbn in I.
  pose proof (urange (eval rho e)) as R.
  destruct (Z.leb_spec l0 h0); cbn [negb] in H; [|discriminate].
  unfold soff, U in *.
  destruct (Z.ltb_spec h0 (2 ^ 63)).
  - inversion H; subst l h; clear H. rewrite signed_small by lia. lia.
  - destruct (Z.leb_spec (2 ^ 63) l0); [|discriminate].
    inversion H; subst l h; clear H. rewrite signed_big by lia. lia.
Qed.

Lemma sitv_d_sound : ltac2:(tb__ "0|5|
S4S4cS3S0S0Sf1R5R4A2S1bS26S23S0S0A2M0A1ScaR5R4A2S27G0S28S0S0R3R2A4A2A3S1cS1cS32R4S6R7R5A2M1A2S32G1R3A2A2S1cS32Z0M2R4A2S1bS0S6R8R6A2M3S42R8R6A2M4A3F_;S36R3G2A2S1bS0G3S38G4S34Z2Z40A2A2A3F_;A2A2F_;F_;Fh;Fl;Fe;Fdg;Frho;").
Proof.
  intros rho dg e l h Hd H. unfold sitv_d in H.
  destruct (sitv_of (itv_lin dg e)) as [p|] eqn:E0.
  { injection H as ->. eapply sitv_of_sound; [apply itv_lin_sound; exact Hd | exact E0]. }
  pose proof (stv_d_sound rho dg e Hd) as S. destruct (stv_t dg e) as [l0 h0]. cbn [fst snd] in H.
  destruct (Z.leb_spec l0 h0); [|discriminate]. injection H as <- <-.
  unfold in_sitv in S. cbn [fst snd] in S. split; [exact S|].
  pose proof (urange (eval rho e)) as R. unfold soff, U in *.
  destruct (Z_lt_ge_dec (bv_unsigned (eval rho e)) (2 ^ 63)).
  - rewrite signed_small in * by lia. split; intros; lia.
  - rewrite signed_big in * by lia. split; intros; lia.
Qed.

Lemma sitv_sound : ltac2:(tb__ "0|5|
S4S25S5A1S3S0S0S49S5S9R5A1R4A3S1bS26S23S0S0A2M0A1Sc9R5R4A2S27G0S28S0S0R3R2A4A2A3S1cS1cS32R4S6R7R5A2M1A2S32G1R3A2A2S1cS32Z0M2R4A2S1bS0S6R8R6A2M3S42R8R6A2M4A3F_;S36R3G2A2S1bS0G3S38G4S34Z2Z40A2A2A3F_;A2A2F_;F_;Fh;Fl;Fe;Ffacts;Frho;").
Proof. intros rho facts e l h Hf H. unfold sitv in H. eapply sitv_of_sound; [apply itv_sound; exact Hf | exact H]. Qed.

Lemma same_atoms_signed : ltac2:(tb__ "0|1|
S4S3S3S0S1bS26S0A1S57R3R2A2S27S0R1A2A3S1cS32S55S33S6R5R3A2S4eR2A1A2M0A2S32G0S54A2A2S1bS0S6R6R5A2S33S6R6R4A2S4eR3A1A2A3F_;F_;Fd0;Fx;Fa;Frho;").
Proof.
  intros rho a x d0 Hs Hr.
  pose proof (same_atoms_sound rho a x d0 Hs) as E.
  apply signed_congr_eq; [pose proof (soff_range rho a); unfold smin, smax; lia | exact Hr |].
  rewrite soff_mod, E. rewrite <- (soff_mod rho x).
  rewrite Zplus_mod_idemp_l. rewrite <- Zplus_mod_idemp_r, <- (snorm_mod d0), Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma sleq_same_sound : ltac2:(tb__ "0|0|
S4S4cS3S0S3Sf1R5R4A2S1bS22Sd1R5R4R3R2A4S24A3S32S33S6R7R5A2R4A2S6R7R3A2A2F_;F_;Fb;Fk;Fa;Fdg;Frho;").
Proof.
  intros rho dg a k b Hd H. unfold sleq_same in H.
  destruct (same_atoms a b) as [d0|] eqn:Es; [|discriminate].
  pose proof (stv_d_sound rho dg b Hd) as SB. destruct (stv_t dg b) as [lb hb].
  unfold in_sitv in SB. cbn [fst snd] in SB.
  repeat (apply andb_prop in H; destruct H as [H ?]).
  apply Z.leb_le in H. apply Z.leb_le in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
  rewrite (same_atoms_signed rho a b d0 Es) by lia. lia.
Qed.

Lemma sleq_by_rel_sound : ltac2:(tb__ "0|0|
S4S4cS3S0S3S23S23S3S0A2S3A2Sf1R6R5A2Sf6R7R2A2S1bS22SceR7R6R5R4R3A5S24A3S32S33S6R9R7A2R6A2S6R9R5A2A2F_;F_;F_;Fr;Fb;Fk;Fa;Fdg;Frho;").
Proof.
  intros rho dg a k b [[x d] y] Hd Hr H. unfold sleq_by_rel in H. unfold srel_holds in Hr.
  set (x' := wnorm_t dg x) in *. set (y' := wnorm_t dg y) in *.
  destruct (same_atoms a x') as [da0|] eqn:Ea; [|discriminate].
  destruct (same_atoms b y') as [db0|] eqn:Eb; [|discriminate].
  pose proof (stv_d_sound rho dg x' Hd) as SX. pose proof (stv_d_sound rho dg y' Hd) as SY.
  destruct (stv_t dg x') as [lx hx]. destruct (stv_t dg y') as [ly hy].
  unfold in_sitv in SX, SY. cbn [fst snd] in SX, SY.
  repeat (apply andb_prop in H; destruct H as [H ?]).
  repeat match goal with
    | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
    end.
  assert (Ex : soff rho x' = soff rho x) by (apply soff_wnorm_t; exact Hd).
  assert (Ey : soff rho y' = soff rho y) by (apply soff_wnorm_t; exact Hd).
  rewrite (same_atoms_signed rho a x' da0 Ea) by lia.
  rewrite (same_atoms_signed rho b y' db0 Eb) by lia.
  lia.
Qed.

Theorem sleq_d_sound : ltac2:(tb__ "0|0|
S4S4cS3S0S3Sf1R5R4A2S1bS22ScfR5R4R3R2A4S24A3S32S33S6R7R5A2R4A2S6R7R3A2A2F_;F_;Fb;Fk;Fa;Fdg;Frho;").
Proof.
  intros rho dg a k b Hd H. unfold sleq_d in H.
  set (a' := wnorm_t dg a) in *. set (b' := wnorm_t dg b) in *.
  assert (Ea : soff rho a' = soff rho a) by (apply soff_wnorm_t; exact Hd).
  assert (Eb : soff rho b' = soff rho b) by (apply soff_wnorm_t; exact Hd).
  pose proof (stv_d_sound rho dg a' Hd) as SA. pose proof (stv_d_sound rho dg b' Hd) as SB.
  destruct (stv_t dg a') as [la ha]. destruct (stv_t dg b') as [lb hb].
  unfold in_sitv in SA, SB. cbn [fst snd] in SA, SB.
  apply lazy_orb_prop in H as [H|H].
  { repeat (apply andb_prop in H; destruct H as [H ?]).
    repeat match goal with | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H end. lia. }
  apply lazy_orb_prop in H as [H|H]; [rewrite <- Ea, <- Eb; eapply sleq_same_sound; eauto|].
  apply lazy_orb_prop in H as [H|H]; [exact (sleq_lin_sound rho dg a k b Hd H)|].
  rewrite <- Ea, <- Eb.
  apply existsb_exists in H as [r [Hin Hr]].
  pose proof (dg_ok_srels rho dg Hd) as RS. rewrite Forall_forall in RS.
  exact (sleq_by_rel_sound rho dg a' k b' r Hd (RS r Hin) Hr).
Qed.

Theorem sleq_sound : ltac2:(tb__ "0|0|
S4S25S5A1S3S0S3S49S5S9R5A1R4A3S1bS22ScdR5R4R3R2A4S24A3S32S33S6R7R5A2R4A2S6R7R3A2A2F_;F_;Fb;Fk;Fa;Ffacts;Frho;").
Proof.
  intros rho facts a k b Hf H. unfold sleq in H. apply lazy_orb_prop in H as [H|H].
  - eapply sleq_d_sound; [apply ctx0_dg_ok; exact Hf | exact H].
  - eapply sleq_d_sound; [apply mk_dig_ok; exact Hf | exact H].
Qed.

Lemma prover_decide_sound : ltac2:(tb__ "0|1|
S4S4cS10cS3S3Sf1R5R4A2S58OLx;Sb9R5R4R3R2A4S1bS22S104R4S7R6R3A2S7R6R2A2A3M0S24A3S1bS22G0S2cA3S20X58x3F_;Fb;Fa;Fc;Fdg;Frho;").
Proof.
  intros rho dg c a b Hd. unfold prover_decide.
  pose proof (fun k H => uleq_d_sound rho dg a k b Hd H) as Uab.
  pose proof (fun k H => uleq_d_sound rho dg b k a Hd H) as Uba.
  pose proof (fun k H => sleq_d_sound rho dg a k b Hd H) as Sab.
  pose proof (fun k H => sleq_d_sound rho dg b k a Hd H) as Sba.
  unfold U in Uab, Uba.
  assert (EQ : forall x y : word, bv_unsigned x = bv_unsigned y -> x = y) by (intros x y E; apply bv_eq; exact E).
  destruct c; cbn [branch_taken]; unfold bv_eqb, bv_ltu, bv_lts.
  - destruct (uleq_d dg a 1 b) eqn:E1; [specialize (Uab 1 E1); cbn; apply Bool.negb_false_iff || idtac; apply Z.eqb_neq; lia|].
    destruct (uleq_d dg b 1 a) eqn:E2; [specialize (Uba 1 E2); apply Z.eqb_neq; lia|].
    destruct (uleq_d dg a 0 b) eqn:E3; [|exact I]. destruct (uleq_d dg b 0 a) eqn:E4; [|exact I].
    specialize (Uab 0 E3). specialize (Uba 0 E4). apply Z.eqb_eq. lia.
  - destruct (uleq_d dg a 1 b) eqn:E1; [specialize (Uab 1 E1); apply Bool.negb_true_iff; apply Z.eqb_neq; lia|].
    destruct (uleq_d dg b 1 a) eqn:E2; [specialize (Uba 1 E2); apply Bool.negb_true_iff; apply Z.eqb_neq; lia|].
    destruct (uleq_d dg a 0 b) eqn:E3; [|exact I]. destruct (uleq_d dg b 0 a) eqn:E4; [|exact I].
    specialize (Uab 0 E3). specialize (Uba 0 E4). apply Bool.negb_false_iff. apply Z.eqb_eq. lia.
  - destruct (sleq_d dg a 1 b) eqn:E1; [specialize (Sab 1 E1); apply Z.ltb_lt; unfold soff in Sab; lia|].
    destruct (sleq_d dg b 0 a) eqn:E2; [specialize (Sba 0 E2); apply Z.ltb_ge; unfold soff in Sba; lia | exact I].
  - destruct (sleq_d dg a 1 b) eqn:E1; [specialize (Sab 1 E1); apply Bool.negb_false_iff; apply Z.ltb_lt; unfold soff in Sab; lia|].
    destruct (sleq_d dg b 0 a) eqn:E2; [specialize (Sba 0 E2); apply Bool.negb_true_iff; apply Z.ltb_ge; unfold soff in Sba; lia | exact I].
  - destruct (uleq_d dg a 1 b) eqn:E1; [specialize (Uab 1 E1); apply Z.ltb_lt; lia|].
    destruct (uleq_d dg b 0 a) eqn:E2; [specialize (Uba 0 E2); apply Z.ltb_ge; lia | exact I].
  - destruct (uleq_d dg a 1 b) eqn:E1; [specialize (Uab 1 E1); apply Bool.negb_false_iff; apply Z.ltb_lt; lia|].
    destruct (uleq_d dg b 0 a) eqn:E2; [specialize (Uba 0 E2); apply Bool.negb_true_iff; apply Z.ltb_ge; lia | exact I].
Qed.

Lemma decide_t_sound : ltac2:(tb__ "0|1|
S4S4cS10cS3S3Sf1R5R4A2S58OLx;S8eR5R4R3R2A4S1bS22S104R4S7R6R3A2S7R6R2A2A3M0S24A3S1bS22G0S2cA3S20X58x3F_;Fb;Fa;Fc;Fdg;Frho;").
Proof.
  intros rho dg c a b Hd. unfold decide_t.
  pose proof (itv_decide_t_sound rho dg c a b (dg_ok_v _ _ Hd)) as D.
  destruct (itv_decide_t dg c a b); [exact D | exact D | apply prover_decide_sound; exact Hd].
Qed.

Lemma mk_slt_f_t_sound : ltac2:(tb__ "0|0|
S4S4cS105S3S3Sf1R5R4A2S1bSfaQ40A1S7R6S7fR5R4R3R2A4A2S100R4S7R6R3A2S7R6R2A2A3A3F_;Fb;Fa;Fop;Fdg;Frho;").
Proof.
  intros rho dg op a b Hd. pose proof (dg_ok_facts _ _ Hd) as Hf. unfold mk_slt_f_t.
  rewrite (lit_fold_t_sound rho) by (apply dg_ok_v; exact Hd).
  destruct op; try (apply mk_alu_f_sound; exact Hf).
  -   destruct (sv_eqb a b) eqn:E.
    { rewrite (sv_eqb_sound _ _ E). cbn [eval]. unfold alu64, alu, bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    pose proof (decide_t_sound rho dg BC_LT a b Hd) as D.
    destruct (decide_t dg BC_LT a b); cbn [branch_taken] in D;
      [| | apply mk_alu_f_sound; exact Hf]; cbn [eval]; unfold alu64, alu; rewrite D; reflexivity.
  -   destruct (sv_eqb a b) eqn:E.
    { rewrite (sv_eqb_sound _ _ E). cbn [eval]. unfold alu64, alu, bv_ltu. rewrite Z.ltb_irrefl. reflexivity. }
    destruct (slt_xor_fold a b) as [r|] eqn:Ex; [apply slt_xor_fold_sound; exact Ex|].
    pose proof (decide_t_sound rho dg BC_LTU a b Hd) as D.
    destruct (decide_t dg BC_LTU a b); cbn [branch_taken] in D;
      [| | apply mk_alu_f_sound; exact Hf]; cbn [eval]; unfold alu64, alu; rewrite D; reflexivity.
  -
    destruct a as [| |op1 x b1| | | | |]; try (apply mk_alu_f_sound; exact Hf).
    destruct op1; try (apply mk_alu_f_sound; exact Hf).
    destruct b1 as [k| | | | | | |]; try (apply mk_alu_f_sound; exact Hf).
    destruct b as [sh| | | | | | |]; try (apply mk_alu_f_sound; exact Hf).
    destruct (Z.leb_spec 0 sh); [|apply mk_alu_f_sound; exact Hf].
    destruct (Z.leb_spec sh k); [|apply mk_alu_f_sound; exact Hf].
    destruct (Z.ltb_spec k 64); [|apply mk_alu_f_sound; exact Hf].
    destruct (small_u_t dg x (64 - k)) eqn:Hs; [|apply mk_alu_f_sound; exact Hf].
    pose proof (small_u_t_sound rho dg x (64 - k) (dg_ok_v _ _ Hd) Hs) as Hx.
    rewrite mk_alu_sound. cbn [eval]. symmetry. apply sll32_srl_val; lia.
Qed.

Lemma mk_slt_f_sound : ltac2:(tb__ "0|0|
S4S25S5A1S105S3S3S49S5S9R5A1R4A3S1bSfaQ40A1S7R6S7eR5R4R3R2A4A2S100R4S7R6R3A2S7R6R2A2A3A3F_;Fb;Fa;Fop;Ffacts;Frho;").
Proof.
  intros rho facts op a b Hf. unfold mk_slt_f.
  destruct (slt_retry (mk_slt_f_t (ctx0 facts) op a b)).
  - apply mk_slt_f_t_sound. apply mk_dig_ok. exact Hf.
  - apply mk_slt_f_t_sound. apply ctx0_dg_ok. exact Hf.
Qed.

Lemma slt_xor_fold_lit : ltac2:(tb__ "0|0|
S3S3S3S1bS26S3A1Sd2R3R2A2S27S3R1A2A3S1dS0S0S1bS3R3ScR1A1A3Lz;A2F_;Fr;Fb;Fa;").
Proof.
  intros a b r H. unfold slt_xor_fold in H.
  assert (CASE2 : match b with
      | SLit 1 => match xor_same_base a with
                  | Some iszero => Some (SLit (if iszero then 1 else 0))
                  | None => None end
      | _ => None end = Some r -> exists z, r = SLit z).
  { clear H. intros H. destruct b as [zb| | | | | | |]; try discriminate.
    destruct zb as [|pb|]; try discriminate; destruct pb; try discriminate.
    destruct (xor_same_base a); [injection H as <-; eexists; reflexivity|discriminate]. }
  destruct a as [za| | | | | | |]; try (apply CASE2; exact H).
  destruct za as [|pa|]; try (apply CASE2; exact H).
  destruct (xor_same_base b); [injection H as <-; eexists; reflexivity|discriminate].
Qed.

Lemma mk_slt_f_t_below : ltac2:(tb__ "0|0|
S1S4cS105S3S3S1bS22S8R5R2A2S24A3S1bS22S8R6R2A2S24A3S1bS22S8R7S7fR6R5R4R3A4A2S24A3F_;F_;Fb;Fa;Fop;Fdg;Fn;").
Proof.
  intros n dg op a b Ha Hb. unfold mk_slt_f_t. apply lit_fold_t_below.
  pose proof (mk_alu_f_below n (dg_facts dg) op a b Ha Hb) as M.
  destruct op; try exact M.
  - destruct (sv_eqb a b); [reflexivity|]. destruct (decide_t _ _ _ _); try reflexivity; exact M.
  - destruct (sv_eqb a b); [reflexivity|].
    destruct (slt_xor_fold a b) as [r|] eqn:E; [destruct (slt_xor_fold_lit _ _ _ E) as [z ->]; reflexivity|].
    destruct (decide_t _ _ _ _); try reflexivity; exact M.
  - destruct a as [| |op1 x b1| | | | |]; try exact M. destruct op1; try exact M.
    destruct b1 as [k| | | | | | |]; try exact M. destruct b as [sh| | | | | | |]; try exact M.
    assert (Hx : sv_below n x = true) by (cbn in Ha; apply andb_prop in Ha as [Ha _]; exact Ha).
    destruct ((0 <=? sh) &&& ((sh <=? k) &&& ((k <? 64) &&& small_u_t dg x (64 - k)))); [|exact M].
    apply mk_alu_below; [exact Hx | reflexivity].
Qed.

Lemma mk_slt_f_below : ltac2:(tb__ "0|0|
S1S25S5A1S105S3S3S1bS22S8R5R2A2S24A3S1bS22S8R6R2A2S24A3S1bS22S8R7S7eR6R5R4R3A4A2S24A3F_;F_;Fb;Fa;Fop;Ffacts;Fn;").
Proof. intros. unfold mk_slt_f. destruct (slt_retry _); apply mk_slt_f_t_below; assumption. Qed.

Definition sub_fold_lin (a b : sv) : option sv := ltac2:(tb__ "0|3|
S26S3A1M0G0Lx;S53Vb;Va;A2S3S27S3R1A2Loff;S23S4bS0A2G0Lx;M1S59Va;A1S4bS0G1S59Vb;A1S4bS0S5cR4R2A2S4bS22G0L_;S119S2eS23S0S3A2M2R1A2S116S2eG2R5A2S2eG2R3A2A2A2S27S3S61R1S38R4R2A2A2A2S2dS3A1X22x2Td;Lcb;Llb;X23x1Lca;Lla;X23x1X26x2").

Lemma sub_fold_eq : ltac2:(tb__ "0|5|
S3S3S1bS26S3A1M0S60R2R1A2S3G0Lb;R1S0S2dS3A1Lz;S1Sf9R3R2A2Li;S105S3S3Sf9R5R4A2M1Lb0;La0;M2Lop;M3G3S107G2Lop;M4G4S22S2S3G1La0;Lw;Lsgn;S1S3S0G1Lk;Li;Ll;X3x8A3Fb;Fa;").
Proof. intros a b. unfold sub_fold, sub_fold_lin. destruct b; reflexivity. Qed.

Lemma sub_fold_lin_sound : ltac2:(tb__ "0|0|
S4S3S3S3S1bS26S3A1Sf9R3R2A2S27S3R1A2A3S1bSfaQ40A1S100S106S7R5R4A2S7R5R3A2A3S7R5R2A2A3F_;Foff;Fb;Fa;Frho;").
Proof.
  intros rho a b off H. unfold sub_fold_lin in H.
  assert (G : forall o, U rho a = (U rho b + U rho o) mod 2 ^ 64 -> alu64 ALU_SUB (eval rho a) (eval rho b) = eval rho o).
  { intros o X. unfold U in X. apply bv_eq. rewrite sub_val, X. rewrite Zminus_mod_idemp_l.
    replace (bv_unsigned (eval rho b) + bv_unsigned (eval rho o) - bv_unsigned (eval rho b))
      with (bv_unsigned (eval rho o)) by lia.
    apply Z.mod_small. apply urange. }
  destruct (rel_offset b a) as [off0|] eqn:R.
  { injection H as <-. apply G. apply rel_offset_sound. exact R. }
  destruct (lin_of0 a) as [la ca] eqn:Ea. destruct (lin_of0 b) as [lb cb] eqn:Eb.
  match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end. injection H as <-.
  apply G. destruct (lin_of0_sound rho a la ca Ea) as [qa Ha]. destruct (lin_of0_sound rho b lb cb Eb) as [qb Hb].
  destruct (sv_of_lin_sound rho (lin_sub la lb) (ca - cb)) as [qo Ho]. rewrite Ho, lin_sub_sound.
  pose proof (U_range rho a). rewrite <- (Z.mod_small (U rho a) (2 ^ 64)) at 1 by lia.
  replace (U rho a) with ((U rho b + (linZ rho la - linZ rho lb + (ca - cb) + qo * 2 ^ 64)) + (qb - qa - qo) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma sub_fold_sound : ltac2:(tb__ "0|0|
S4S3S3S3S1bS26S3A1S60R3R2A2S27S3R1A2A3S1bSfaQ40A1S100S106S7R5R4A2S7R5R3A2A3S7R5R2A2A3F_;Foff;Fb;Fa;Frho;").
Proof.
  intros rho a b off H. rewrite sub_fold_eq in H.
  apply sub_fold_lin_sound. destruct b; try discriminate; exact H.
Qed.

Lemma sub_fold_below : ltac2:(tb__ "0|0|
S1S3S3S3S1bS22S8R4R3A2S24A3S1bS22S8R5R3A2S24A3S1bS26S3A1S60R5R4A2S27S3R3A2A3S1bS22S8R7R4A2S24A3F_;F_;F_;Foff;Fb;Fa;Fn;").
Proof.
  intros n a b off Ha Hb H. rewrite sub_fold_eq in H.
  assert (R : sub_fold_lin a b = Some off) by (destruct b; try discriminate; exact H). clear H.
  unfold sub_fold_lin in R. destruct (rel_offset b a) as [off0|] eqn:R0.
  { injection R as <-. exact (rel_offset_below n b a off0 Ha Hb R0). }
  destruct (lin_of0 a) as [la ca] eqn:Ea. destruct (lin_of0 b) as [lb cb] eqn:Eb.
  match type of R with (if ?c then _ else _) = _ => destruct c; [|discriminate] end. injection R as <-.
  apply sv_of_lin_below. apply lin_sub_below; [exact (lin_of0_below n a la ca Ha Ea) | exact (lin_of0_below n b lb cb Hb Eb)].
Qed.

Lemma mk_op_f_sound : ltac2:(tb__ "0|0|
S4S25S5A1S105S3S3S49S5S9R5A1R4A3S1bSfaQ40A1S7R6S7cR5R4R3R2A4A2S100R4S7R6R3A2S7R6R2A2A3A3F_;Fb;Fa;Fop;Ffacts;Frho;").
Proof.
  intros rho facts op a b Hf. unfold mk_op_f.
  destruct op; try (apply mk_slt_f_sound; exact Hf).
  destruct (sub_fold a b) as [off|] eqn:E; [|apply mk_slt_f_sound; exact Hf].
  rewrite (lit_fold_t_sound rho) by (apply ctx0_ok; exact Hf).
  symmetry. apply sub_fold_sound. exact E.
Qed.

Lemma mk_op_f_below : ltac2:(tb__ "0|0|
S1S25S5A1S105S3S3S1bS22S8R5R2A2S24A3S1bS22S8R6R2A2S24A3S1bS22S8R7S7cR6R5R4R3A4A2S24A3F_;F_;Fb;Fa;Fop;Ffacts;Fn;").
Proof.
  intros n facts op a b Ha Hb. unfold mk_op_f. destruct op; try (apply mk_slt_f_below; assumption).
  destruct (sub_fold a b) eqn:E; [apply lit_fold_t_below; exact (sub_fold_below n a b _ Ha Hb E) | apply mk_slt_f_below; assumption].
Qed.

Lemma low32_unsigned_mod : ltac2:(tb__ "0|1|
SfaQ40M0A1S1bS0SfcQ20S101R1A1A2S35SfcG0R1A2S34Z2Z20A2A2A3Fw;").
Proof.
  intros w. unfold low32. rewrite bv_extract_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
Qed.

Lemma subw_via_diff : ltac2:(tb__ "0|2|
SfaQ40M0A1M1G1G1S1bG1S100S106R3R2A3R1A3S1bSfaQ20A1S103S106S101R4A1S101R3A1A3S103S106S101R2A1S101SfdG0Z0A2A1A3A3F_;Fd;Fb;Fa;").
Proof.
  intros a b d H. apply (f_equal bv_unsigned) in H. rewrite sub_val in H.
  unfold alu32, alu. apply bv_eq.
  rewrite !bv_sub_unsigned, !low32_unsigned_mod, Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 32) with (2 ^ 32). rewrite two64.
  rewrite <- (Zminus_mod (bv_unsigned a) (bv_unsigned b)).
  change ((0 mod 2 ^ 64) mod 2 ^ 32) with 0. rewrite Z.sub_0_r, Z.mod_mod by lia.
  rewrite <- (mod_pow2_of_mod_2_64 (bv_unsigned a - bv_unsigned b) 32) by lia.
  rewrite H. reflexivity.
Qed.

Lemma mk_opw_f_sound : ltac2:(tb__ "0|1|
S4S25S5A1S105S3S3S49S5S9R5A1R4A3S1bSfaQ40M0A1S7R6S7dR5R4R3R2A4A2S115Q20G0S103R4S101S7R6R3A2A1S101S7R6R2A2A1A3A3A3F_;Fb;Fa;Fop;Ffacts;Frho;").
Proof.
  intros rho facts op a b Hf. unfold mk_opw_f.
  destruct op; try (apply mk_aluw_f_sound; exact Hf).
  destruct (sub_fold a b) as [off|] eqn:E; [|apply mk_aluw_f_sound; exact Hf].
  rewrite (mk_aluw_f_sound rho) by exact Hf. cbn [eval]. f_equal. symmetry.
  apply subw_via_diff. apply sub_fold_sound. exact E.
Qed.

Lemma mk_opw_f_below : ltac2:(tb__ "0|0|
S1S25S5A1S105S3S3S1bS22S8R5R2A2S24A3S1bS22S8R6R2A2S24A3S1bS22S8R7S7dR6R5R4R3A4A2S24A3F_;F_;Fb;Fa;Fop;Ffacts;Fn;").
Proof.
  intros n facts op a b Ha Hb. unfold mk_opw_f. destruct op; try (apply mk_aluw_f_below; assumption).
  destruct (sub_fold a b) eqn:E; [|apply mk_aluw_f_below; assumption].
  apply mk_aluw_f_below; [exact (sub_fold_below n a b _ Ha Hb E) | reflexivity].
Qed.

Lemma in_bounds_d_sound : ltac2:(tb__ "0|1|
S4S4cS3S3S3S0Sf1R6R5A2S32Z0R2A2S1bS22S69R7R6R5R4R3A5S24A3S1cS32S6R9R7A2S6R9R5A2M0A2S32S33G0R4A2S6R9R6A2A2A2F_;F_;F_;Fk;Foff;Fhi;Flo;Fdg;Frho;").
Proof.
  intros rho dg lo hi off k Hd Hk H. unfold in_bounds_d in H.
  destruct (sitv_d dg lo) as [[l1 h1]|] eqn:S1; [|discriminate].
  destruct (sitv_d dg hi) as [[l2 h2]|] eqn:S2; [|discriminate].
  destruct (sitv_d dg off) as [[l3 h3]|] eqn:S3; [|discriminate].
  pose proof (sitv_d_sound rho dg lo l1 h1 Hd S1) as (A1 & B1 & _).
  pose proof (sitv_d_sound rho dg hi l2 h2 Hd S2) as (A2 & B2 & _).
  pose proof (sitv_d_sound rho dg off l3 h3 Hd S3) as (A3 & B3 & _).
  apply lazy_andb_prop in H as [Hlo Hhi]. split.
  - apply lazy_orb_prop in Hlo as [Hlo|Hlo].
    + apply Z.leb_le in Hlo. lia.
    + apply lazy_orb_prop in Hlo as [Hlo|Hlo].
      * apply lazy_andb_prop in Hlo as [Hlo Hu]. apply andb_prop in Hlo as [P1 P3].
        apply Z.leb_le in P1. apply Z.leb_le in P3.
        pose proof (uleq_d_sound rho dg lo 0 off Hd Hu). rewrite B1, B3 by lia. lia.
      * pose proof (sleq_d_sound rho dg lo 0 off Hd Hlo). lia.
  - apply lazy_orb_prop in Hhi as [Hhi|Hhi].
    + apply Z.leb_le in Hhi. lia.
    + apply lazy_orb_prop in Hhi as [Hhi|Hhi].
      * apply lazy_andb_prop in Hhi as [Hhi Hu]. apply andb_prop in Hhi as [P3 P2].
        apply Z.leb_le in P3. apply Z.leb_le in P2.
        pose proof (uleq_d_sound rho dg off k hi Hd Hu). rewrite B3, B2 by lia. lia.
      * exact (sleq_d_sound rho dg off k hi Hd Hhi).
Qed.

Lemma in_bounds_sound : ltac2:(tb__ "0|1|
S4S25S5A1S3S3S3S0S49S5S9R6A1R5A3S32Z0R2A2S1bS22S5aR7R6R5R4R3A5S24A3S1cS32S6R9R7A2S6R9R5A2M0A2S32S33G0R4A2S6R9R6A2A2A2F_;F_;F_;Fk;Foff;Fhi;Flo;Ffacts;Frho;").
Proof.
  intros rho facts lo hi off k Hf Hk H. unfold in_bounds in H. apply lazy_orb_prop in H as [H|H].
  - eapply in_bounds_d_sound; [apply ctx0_dg_ok; exact Hf | exact Hk | exact H].
  - eapply in_bounds_d_sound; [apply mk_dig_ok; exact Hf | exact Hk | exact H].
Qed.

Lemma find_obj_d_spec : ltac2:(tb__ "0|2|
S25SaA1S4cS3S0S2aS2aSaS3S1bS26S23S23S2aSaA2M0S3A2M1A1S94R8R7R6R5R4A5S27G1S28G0S3S28S2aSaR3R2A4R1A4A2A3S1dS2aS2aS1cS1bS2aR5S116R6R1A2A3S1cS1bS26SaA1S113SaRaR1A3S27SaR4A2A3S1cS1bS26S3A1S53SfR4A1R8A2S27S3R3A2A3S1bS22S69R9S12R4A1S11R4A1R3R7A5S24A3A2A2A2Li;A2F_;Foff;Fo;Fn;Fn0;Fk;Fae;Fdg;Fobjs;").
Proof.
  intros objs dg ae k. induction objs as [|o0 rest IH]; intros n0 n o off H; cbn [find_obj_d] in H; [discriminate|].
  destruct (rel_offset (ob_base o0) ae) as [off0|] eqn:R.
  - destruct (in_bounds_d dg (ob_lo o0) (ob_hi o0) off0 k) eqn:B.
    + inversion H; subst. exists 0%nat. split; [lia|]. split; [reflexivity|]. split; assumption.
    + destruct (IH (S n0) n o off H) as (i & Hn & Hnth & HR & HB).
      exists (S i). split; [lia|]. split; [exact Hnth|]. split; assumption.
  - destruct (IH (S n0) n o off H) as (i & Hn & Hnth & HR & HB).
    exists (S i). split; [lia|]. split; [exact Hnth|]. split; assumption.
Qed.

Lemma find_obj_spec : ltac2:(tb__ "0|2|
S25SaA1S25S5A1S3S0S2aS2aSaS3S1bS26S23S23S2aSaA2M0S3A2M1A1S93R8R7R6R5R4A5S27G1S28G0S3S28S2aSaR3R2A4R1A4A2A3S1dS2aS2aS1cS1bS2aR5S116R6R1A2A3S1cS1bS26SaA1S113SaRaR1A3S27SaR4A2A3S1cS1bS26S3A1S53SfR4A1R8A2S27S3R3A2A3S1bS22S5aR9S12R4A1S11R4A1R3R7A5S24A3A2A2A2Li;A2F_;Foff;Fo;Fn;Fn0;Fk;Fae;Ffacts;Fobjs;").
Proof.
  intros objs facts ae k n0 n o off H. unfold find_obj in H. unfold in_bounds.
  destruct (find_obj_d objs (ctx0 facts) ae k n0) as [r|] eqn:E.
  - injection H as ->. destruct (find_obj_d_spec _ _ _ _ _ _ _ _ E) as (i & A & B & C & D).
    exists i. rewrite D. repeat split; assumption.
  - destruct (find_obj_d_spec _ _ _ _ _ _ _ _ H) as (i & A & B & C & D).
    exists i. rewrite D. repeat split; try assumption. destruct (in_bounds_d (ctx0 facts) _ _ _ _); reflexivity.
Qed.

Section WithSegs2.
Variable segs : list MemImageType.Segment.

Lemma access_in_range : ltac2:(tb__ "0|1|
S4S117SaS3S3S0S25S5A1S49S5S9R7A1R1A3S14Vsegs;R8R7R6A4S1bS26S3A1S53SfR7A1R6A2S27S3R5A2A3S1bS22S5aR4S12R8A1S11R8A1R6R5A5S24A3S36Z0R6A2S1cS1bS0S42RcR9A2S33S42RcSfRaA1A2S6RcR8A2M0A2A3S1cS32S15RcRaA2G0A2S32S33G0R7A2S13RcRaA2A2A2A2F_;F_;F_;F_;F_;Ffacts;Fk;Foff;Fae;Fo;Fms;Frho;").
Proof using .
  intros rho ms o ae off k facts Hf Hoh HR HB Hk.
  destruct Hoh as [Hrange _]. unfold obj_lo_of, obj_hi_of in *.
  pose proof (in_bounds_sound rho facts (ob_lo o) (ob_hi o) off k Hf ltac:(lia) HB) as [A B].
  split; [|split; assumption].
  pose proof (rel_offset_sound rho _ _ _ HR) as E.
  rewrite <- (soff_mod rho off), Zplus_mod_idemp_r in E.
  rewrite Z.mod_small in E; [exact E|]. unfold U in *. lia.
Qed.

Lemma narrow_diff_snorm : ltac2:(tb__ "0|4|
S0S0S0S1cS36S3cS34Z2M0Z3fA2M1A1S38R2R3A2M2A2S36G2G1A2A2S1bS0S35R3S34G0Z40A2M3A2S35S33R4R2A2G3A2A3S1bS0R4S33R5S4eR3A1A2A3F_;F_;Fd0;Fq;Fp;").
Proof using .
  intros p q d0 Hn E.
  assert (D : (q - p) mod 2 ^ 64 = d0 mod 2 ^ 64).
  { rewrite Zminus_mod, E, <- Zminus_mod. f_equal. lia. }
  unfold snorm. rewrite <- D.
  pose proof (Z.mod_pos_bound (q - p) (2 ^ 64) ltac:(lia)) as M.
  pose proof (Z_div_mod_eq_full (q - p) (2 ^ 64)) as Q.
  revert M Q. generalize ((q - p) mod 2 ^ 64) as m. generalize ((q - p) / 2 ^ 64) as t.
  intros t m M Q. destruct (Z.ltb_spec m (2 ^ 63)); lia.
Qed.

Lemma cell_rel_lit_sound : ltac2:(tb__ "0|1|
S4S25S5A1S117SaS3S0SdS0S49S5S9R8A1R7A3S14Vsegs;R9R7R6A4S112SdR4S18R7A1A3S32S15RbR8A2S6RbR7A2A2S32S33S6RcR8A2R7A2S13RcR9A2A2S32Z0M0R8A2S32G0S17R8A1A2S1bS65S64ReRbRaR9A4S85R8A1A3S1bS0S6R10S16RaA1A2S33S6R10RcA2R9A2A3F_;F_;F_;F_;F_;F_;F_;F_;Fd;Fc;Fk;Foff;Fo;Fms;Ffacts;Frho;").
Proof using .
  intros rho facts ms o off k c d Hf Hoh Hin Hlo Hhi Hk Hw H.
  unfold cell_rel in H.
  destruct (same_atoms (c_off c) off) as [d0|] eqn:Es.
  - inversion H; subst d; clear H.
    pose proof (same_atoms_sound rho _ _ _ Es) as E.
    destruct Hoh as (Hrange & _ & Hcells & _).
    pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as (C1 & C2 & _).
    unfold obj_lo_of, obj_hi_of in *.
    rewrite <- (soff_mod rho (c_off c)), <- (soff_mod rho off), Zplus_mod_idemp_l in E.
    apply narrow_diff_snorm; [lia | exact E].
  - exfalso. cbv zeta beta in H.
    match type of H with (if ?b then _ else _) = _ => destruct b end; [discriminate|].
    match type of H with (if ?b then _ else _) = _ => destruct b end; discriminate.
Qed.

Lemma cell_rel_disj_sound : ltac2:(tb__ "0|2|
S4S25S5A1S117SaS3S0SdS49S5S9R7A1R6A3S14Vsegs;R8R6R5A4S112SdR3S18R6A1A3S32S15RaR7A2S6RaR6A2A2S32S33S6RbR7A2R6A2S13RbR8A2A2S32Z0R7A2S1bS65S64RcR9R8R7A4S84A3S1eS32S33S6ReRaA2M0R9A2S6ReS16R8A1A2M1A2S32S33G1S17R8A1A2G0A2A2F_;F_;F_;F_;F_;F_;F_;Fc;Fk;Foff;Fo;Fms;Ffacts;Frho;").
Proof using .
  intros rho facts ms o off k c Hf Hoh Hin Hlo Hhi Hk H.
  unfold cell_rel in H.
  destruct (same_atoms (c_off c) off) as [d0|] eqn:Es; [discriminate|].
  cbv zeta beta in H.
  pose proof (mk_dig_ok rho facts Hf) as Hd. set (dg := mk_dig facts) in *.
  pose proof (fun Hu => uleq_d_sound rho dg off k (c_off c) Hd Hu) as U1.
  pose proof (fun Hu => uleq_d_sound rho dg (c_off c) (c_width c) off Hd Hu) as U2.
  pose proof (fun l h Hs => sitv_d_sound rho dg off l h Hd Hs) as T1.
  pose proof (fun l h Hs => sitv_d_sound rho dg (c_off c) l h Hd Hs) as T2.
  revert U1 U2 T1 T2 H.
  generalize (uleq_d dg off k (c_off c)) as u1.
  generalize (uleq_d dg (c_off c) (c_width c) off) as u2.
  generalize (sitv_d dg off) as s1. generalize (sitv_d dg (c_off c)) as s2.
  intros s2 s1 u2 u1 U1 U2 T1 T2 H.
  destruct s1 as [[l1 h1]|]; destruct s2 as [[l2 h2]|]; cbn in H.
  all: try (exfalso; rewrite ?andb_false_r in H; cbn in H; discriminate).
  specialize (T1 l1 h1 eq_refl) as (A1 & B1 & _).
  specialize (T2 l2 h2 eq_refl) as (A2 & B2 & _).
  destruct (Z.leb_spec (h1 + k) l2); [left; lia|].
  destruct (Z.leb_spec (h2 + c_width c) l1); [right; lia|].
  cbn in H.
  destruct (Z.leb_spec 0 l1); [|discriminate].
  destruct (Z.leb_spec 0 l2); [|discriminate].
  cbn in H. rewrite B1, B2 by assumption.
  destruct u1; [left; apply U1; reflexivity|].
  destruct u2; [right; apply U2; reflexivity|].
  discriminate.
Qed.

End WithSegs2.

Lemma mk_md_f0_below : ltac2:(tb__ "0|0|
S1S25S5A1S107S3S3S1bS22S8R5R2A2S24A3S1bS22S8R6R2A2S24A3S1bS22S8R7S7aR6R5R4R3A4A2S24A3F_;F_;Fb;Fa;Fop;Ffacts;Fn;").
Proof.
  intros n facts op a b Ha Hb. unfold mk_md_f0.
  destruct op; try (apply mk_md_below; assumption).
  destruct b; try (apply mk_md_below; assumption).
  destruct (zmod64 z =? C3magic); [|apply mk_md_below; assumption].
  destruct (lin_of0 a) as [l c] eqn:E.
  pose proof (lin_of0_below n a l c Ha E) as Hl.
  destruct l as [|[k v] l']; [apply mk_md_below; assumption|].
  destruct (Z.eq_dec k 3) as [->|Hk].
  2:{ destruct k as [|p|p]; try (apply mk_md_below; assumption);
      destruct p as [p|p|]; try (apply mk_md_below; assumption);
      try (destruct p as [p|p|]; try (apply mk_md_below; assumption)). exfalso; apply Hk; reflexivity. }
  destruct l'; [|apply mk_md_below; assumption].
  destruct (Z.eq_dec c 0) as [->|Hc].
  2:{ destruct c; try (apply mk_md_below; assumption). exfalso; apply Hc; reflexivity. }
  cbn [lin_below forallb snd] in Hl. rewrite Bool.andb_true_r in Hl.
  destruct (small_u facts v 62); [|apply mk_md_below; assumption].
  apply mk_alu_below; [exact Hl | reflexivity].
Qed.

Lemma mulhu_magic3 : ltac2:(tb__ "0|2|
S0S1cS32Z0R1A2S36R1S34Z2M0Z3eA2A2A2S1bS0S3eS37S37Z3R2A2S35S83S34G0Z40M1A2A2A2G1A2S37G0R2A2A3F_;Fv;").
Proof.
  intros v Hv. rewrite Z.shiftr_div_pow2 by lia.
  replace (C3magic mod 2 ^ 64) with C3magic by reflexivity.
  replace (3 * v * C3magic) with (2 * v * 2 ^ 64 + v).
  2:{ unfold C3magic. lia. }
  rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma mk_md_f0_sound : ltac2:(tb__ "0|1|
S4S25S5A1S107S3S3S49S5S9R5A1R4A3S1bSfaQ40M0A1S7R6S7aR5R4R3R2A4A2S102G0R4S7R6R3A2S7R6R2A2A4A3F_;Fb;Fa;Fop;Ffacts;Frho;").
Proof.
  intros rho facts op a b Hf. unfold mk_md_f0.
  destruct op; try apply mk_md_sound.
  destruct b; try apply mk_md_sound.
  destruct (Z.eqb_spec (zmod64 z) C3magic) as [Hz|]; [|apply mk_md_sound].
  destruct (lin_of0 a) as [l c] eqn:E.
  destruct l as [|[k v] l']; [apply mk_md_sound|].
  destruct (Z.eq_dec k 3) as [->|Hk].
  2:{ destruct k as [|p|p]; try apply mk_md_sound;
      destruct p as [p|p|]; try apply mk_md_sound;
      try (destruct p as [p|p|]; try apply mk_md_sound). exfalso; apply Hk; reflexivity. }
  destruct l'; [|apply mk_md_sound].
  destruct (Z.eq_dec c 0) as [->|Hc].
  2:{ destruct c; try apply mk_md_sound. exfalso; apply Hc; reflexivity. }
  destruct (small_u facts v 62) eqn:Hs; [|apply mk_md_sound].
  pose proof (small_u_sound rho facts v 62 Hf Hs) as Hv.
  destruct (lin_of0_sound rho a [(3, v)] 0 E) as [q Hq]. cbn [linZ fold_right fst snd] in Hq.
  pose proof (urange (eval rho a)) as Ra. unfold U in Hq.
  assert (q = 0) by nia. subst q.
  apply bv_eq. rewrite mk_alu_sound. cbn [eval]. rewrite sll_val.
  unfold mul_div, bv_mulhuu. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  change (Z.of_N 64) with 64.
  replace (bv_unsigned (eval rho a)) with (3 * bv_unsigned (eval rho v)) by lia.
  rewrite zmod64_eq in Hz. rewrite Hz.
  replace C3magic with (C3magic mod 2 ^ 64) by reflexivity.
  rewrite mulhu_magic3 by lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ (1 mod 64)) with 2.
  rewrite !Z.mod_small by lia. lia.
Qed.

Lemma lit_is_eval : ltac2:(tb__ "0|1|
S4S3S0S1bS22SacR2R1A2S24A3S1bSfaQ40M0A1S7R4R3A2SfdG0R2A2A3F_;Fk;Fa;Frho;").
Proof.
  intros rho a k H. destruct a; try discriminate. cbn [lit_is] in H. apply Z.eqb_eq in H.
  rewrite !zmod64_eq in H. cbn [eval]. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. exact H.
Qed.

Lemma mul_one_r : ltac2:(tb__ "0|2|
SfaQ40M0A1M1S1bG1S102G0S108R1SfdG0Z1A2A4R1A3Fx;").
Proof.
  intros x. unfold mul_div. apply bv_eq. rewrite bv_mul_unsigned, Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  pose proof (urange x). rewrite (Z.mod_small 1) by lia. rewrite Z.mul_1_r. apply Z.mod_small. lia.
Qed.

Lemma mul_one_l : ltac2:(tb__ "0|2|
SfaQ40M0A1M1S1bG1S102G0S108SfdG0Z1A2R1A4R1A3Fx;").
Proof.
  intros x. unfold mul_div. apply bv_eq. rewrite bv_mul_unsigned, Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  pose proof (urange x). rewrite (Z.mod_small 1) by lia. rewrite Z.mul_1_l. apply Z.mod_small. lia.
Qed.

Lemma mul_m1_r : ltac2:(tb__ "0|2|
SfaQ40M0A1M1S1bG1S102G0S108R1SfdG0N1A2A4S100S106SfdG0Z0A2R1A3A3Fx;").
Proof.
  intros x. unfold mul_div, alu64, alu. pose proof (urange x). apply bv_eq.
  rewrite bv_mul_unsigned, bv_sub_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  rewrite Zmult_mod_idemp_r. rewrite (Z.mod_0_l (2 ^ 64)) by lia. f_equal; lia.
Qed.

Lemma mul_m1_l : ltac2:(tb__ "0|2|
SfaQ40M0A1M1S1bG1S102G0S108SfdG0N1A2R1A4S100S106SfdG0Z0A2R1A3A3Fx;").
Proof.
  intros x. unfold mul_div, alu64, alu. pose proof (urange x). apply bv_eq.
  rewrite bv_mul_unsigned, bv_sub_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  rewrite Zmult_mod_idemp_l. rewrite (Z.mod_0_l (2 ^ 64)) by lia. f_equal; lia.
Qed.

Lemma mk_md_1_sound : ltac2:(tb__ "0|1|
S4S107S3S3S3S1bS26S3A1S78R4R3R2A3S27S3R1A2A3S1bSfaQ40M0A1S7R6R2A2S102G0R5S7R6R4A2S7R6R3A2A4A3F_;Fr;Fb;Fa;Fop;Frho;").
Proof.
  intros rho op a b r H. unfold mk_md_1 in H. destruct op; try discriminate.
  destruct (lit_is a 1) eqn:E1.
  { injection H as <-. rewrite (lit_is_eval rho a 1 E1). symmetry. apply mul_one_l. }
  destruct (lit_is b 1) eqn:E2.
  { injection H as <-. rewrite (lit_is_eval rho b 1 E2). symmetry. apply mul_one_r. }
  destruct (lit_is a (-1)) eqn:E3.
  { injection H as <-. rewrite (lit_is_eval rho a (-1) E3).
    transitivity (alu64 ALU_SUB (eval rho (SLit 0)) (eval rho b)); [apply (mk_alu_sound rho ALU_SUB (SLit 0) b) | cbn [eval]; symmetry; apply mul_m1_l]. }
  destruct (lit_is b (-1)) eqn:E4; [|discriminate].
  injection H as <-. rewrite (lit_is_eval rho b (-1) E4).
  transitivity (alu64 ALU_SUB (eval rho (SLit 0)) (eval rho a)); [apply (mk_alu_sound rho ALU_SUB (SLit 0) a) | cbn [eval]; symmetry; apply mul_m1_r].
Qed.

Lemma mk_md_1_below : ltac2:(tb__ "0|0|
S1S107S3S3S3S1bS22S8R5R3A2S24A3S1bS22S8R6R3A2S24A3S1bS26S3A1S78R6R5R4A3S27S3R3A2A3S1bS22S8R8R4A2S24A3F_;F_;F_;Fr;Fb;Fa;Fop;Fn;").
Proof.
  intros n op a b r Ha Hb H. unfold mk_md_1 in H. destruct op; try discriminate.
  destruct (lit_is a 1); [injection H as <-; exact Hb|].
  destruct (lit_is b 1); [injection H as <-; exact Ha|].
  destruct (lit_is a (-1)); [injection H as <-; exact (mk_alu_below n ALU_SUB (SLit 0) b eq_refl Hb)|].
  destruct (lit_is b (-1)); [injection H as <-; exact (mk_alu_below n ALU_SUB (SLit 0) a eq_refl Ha)|discriminate].
Qed.

Lemma mk_md_f_sound : ltac2:(tb__ "0|1|
S4S25S5A1S107S3S3S49S5S9R5A1R4A3S1bSfaQ40M0A1S7R6S79R5R4R3R2A4A2S102G0R4S7R6R3A2S7R6R2A2A4A3F_;Fb;Fa;Fop;Ffacts;Frho;").
Proof.
  intros rho facts op a b Hf. unfold mk_md_f.
  destruct (mk_md_1 op a b) as [r|] eqn:E; [exact (mk_md_1_sound rho op a b r E) | apply mk_md_f0_sound; exact Hf].
Qed.

Lemma mk_md_f_below : ltac2:(tb__ "0|0|
S1S25S5A1S107S3S3S1bS22S8R5R2A2S24A3S1bS22S8R6R2A2S24A3S1bS22S8R7S79R6R5R4R3A4A2S24A3F_;F_;Fb;Fa;Fop;Ffacts;Fn;").
Proof.
  intros n facts op a b Ha Hb. unfold mk_md_f.
  destruct (mk_md_1 op a b) as [r|] eqn:E; [exact (mk_md_1_below n op a b r Ha Hb E) | apply mk_md_f0_below; assumption].
Qed.

Lemma mk_mdw_f_sound : ltac2:(tb__ "0|2|
S4S25S5A1S107S3S3S49S5S9R5A1R4A3S1bSfaQ40M0A1S7R6S7bR5R4R3R2A4A2S115Q20M1G0S102G1R4S101S7R6R3A2A1S101S7R6R2A2A1A4A3A3F_;Fb;Fa;Fop;Ffacts;Frho;").
Proof.
  intros rho facts op a b Hf. unfold mk_mdw_f. destruct op; try apply mk_mdw_sound. cbn zeta.
  destruct (small_u facts (mk_md M_MUL a b) 31) eqn:Hs; [|apply mk_mdw_sound].
  pose proof (small_u_sound rho facts _ 31 Hf Hs) as Br. rewrite mk_md_sound in Br |- *.
  pose proof (urange (eval rho a)) as Ra. pose proof (urange (eval rho b)) as Rb.
  assert (D : (2 ^ 32 | 2 ^ 64)%Z) by (exists (2 ^ 32); reflexivity).
  assert (L : bv_unsigned (mul_div M_MUL (low32 (eval rho a)) (low32 (eval rho b)))
              = bv_unsigned (mul_div M_MUL (eval rho a) (eval rho b)) mod 2 ^ 32).
  { unfold mul_div. rewrite !bv_mul_unsigned, !low32_umod. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite two64.
    rewrite (Z.mod_mod_divide _ _ _ D). rewrite <- Z.mul_mod by lia. reflexivity. }
  apply bv_eq. rewrite sext64_32_small by (rewrite L, Z.mod_small; lia).
  rewrite L. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma mk_mdw_f_below : ltac2:(tb__ "0|0|
S1S25S5A1S107S3S3S1bS22S8R5R2A2S24A3S1bS22S8R6R2A2S24A3S1bS22S8R7S7bR6R5R4R3A4A2S24A3F_;F_;Fb;Fa;Fop;Ffacts;Fn;").
Proof.
  intros n facts op a b Ha Hb. unfold mk_mdw_f. destruct op; try (apply mk_mdw_below; assumption).
  cbn zeta. destruct (small_u _ _ _); [apply mk_md_below; assumption | apply mk_mdw_below; assumption].
Qed.
