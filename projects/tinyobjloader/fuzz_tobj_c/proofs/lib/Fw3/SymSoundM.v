(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "not"; "iff"; "True"; "False"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "nat"; "option"; "Some"; "length"; "prod"; "pair"; "false"; "app"; "snd"; "None"; "cons"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "valuation"; "cell"; "soff"; "sstate"; "sv_below"; "sprop"; "eval"; "obj_holds"; "rd_bytes"; "obj_wf"; "ob_base"; "smatch"; "ss_next"; "obj_lo_of"; "ext_low"; "obj_hi_of"; "tfact"; "oaddr"; "ss_pc"; "ob_cells"; "obj_range"; "agree_below"; "holds"; "ss_facts"; "c_width"; "enc_bytes"; "mkSS"; "rom_ok"; "ss_fcsr"; "ss_fregs"; "ss_objs"; "ss_regs"; "ss_resv"; "swf"; "SLit"; "c_val"; "covered"; "ob_dflt"; "odefault"; "ss_lenient"; "c_off"; "cell_wf"; "fldv"; "mem_match"; "pairwise_disjoint"; "rl"; "rw"; "sprop_below"; "SVar"; "rd"; "sublist"; "tf_below"; "tf_holds"; "ob_hi"; "ob_lo"; "outside_all"; "rm"; "cell_holds"; "dflt_wf"; "image_byte"; "ro_clear"; "sfcsr"; "DArr"; "DImage"; "DList"; "DRom"; "DZero"; "extv"; "in_cell"; "mkCell"; "mkObj"; "mkVal"; "ro_addr"; "zrel"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "bv_extract"; "bv_add"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "mul"; "of_nat"; "to_nat"; "modulo"; "to_N"; "sub"; "testbit"; "opp"; "shiftr"; "land"; "div"; "lor"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "machine_result"; "ov_read_bytes"; "MachineFault"; "ms_mem"; "step"; "width_bytes"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_ms"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@Corelib.Init.Peano"; "lt"; "le"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "cell_read"; "LROk"; "load_res"; "msz"; "crel"; "snorm"; "CLit"; "CRTile"; "cell_rel"; "sym_load"; "fld_vars"; "image_bytes"; "list_set"; "mk_addk"; "read_cells"; "tf_inst"; "tmpl_inst"; "CRNone"; "all_ro"; "extsv"; "fresh"; "get_reg"; "immI"; "instr_at"; "mk_ext"; "narrow"; "obj_add_cell"; "set_pc"; "set_reg"; "sp_rel"; "strip_ext"; "tf_mentions"; "CDisj"; "CRExact"; "CRInside"; "CRUnknown"; "arr_cells"; "find_lcell_at"; "find_obj"; "fld_index"; "in_bounds"; "lit_cells"; "lit_overlaps"; "load_arr"; "load_dflt"; "load_fresh"; "mk_alu"; "rel_offset"; "ro_span"; "tile_cells"; "@Stdlib.NArith.BinNat.N"; "mul"; "le"; "of_nat"; "lt"; "@Stdlib.Lists.List"; "In"; "forallb"; "nth_error"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "bytes_le_to_Z"; "le_bytes_to_word"; "Z_to_le_bytes"; "@Stdlib.PArith.BinPos.Pos"; "le"; "to_nat"; "of_nat"; "eqb"; "lt"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.M3"; "load_post"; "rho_exts"; "step_rel"; "rho_fresh"; "pdr"; "@Corelib.Init.Nat"; "add"; "@LinuxProcessSemantics.Riscv.Instr"; "msize"; "instr"; "Load"; "ALU_SRL"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.M"; "uncovered"; "acc_ok"; "cell_skippable";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV"; "U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SpecBridge"; "interp_eff0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI"; "next_rel"; "@LinuxProcessSemantics.Riscv.Sem"; "core"; "eff"; "load_val"; "ELoad"; "alu64"; "@Corelib.Init.Specif"; "sumbool"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymLin.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section M.
Variable segs : list Segment.

Lemma u_add1 : forall (a : word), bv_unsigned a + 1 < 2 ^ 64 -> bv_unsigned (a + 1)%bv = bv_unsigned a + 1.
Proof using .
  intros a H. rewrite bv_add_unsigned. change (bv_unsigned (1 : word)) with 1.
  apply bv_wrap_small. rewrite two64. pose proof (urange a). lia.
Qed.

Lemma ov_read_bytes_rd : ltac2:(tb__ "0|0|
S7bS66Q40A1SeS37Vsegs;R3A2S0SfScS66Q8A1A1A1S7dVsegs;S7fR4A1R3R2A4S24R4R3R2A3A3F_;Fk;Fa;Fms;").
Proof using .
  intros ms a k Hrom. revert a. induction k as [|k IH]; intros a; cbn; [reflexivity|].
  unfold rd, ms_read_byte. rewrite (Hrom a). unfold image_byte.
  destruct (ms_mem ms a) as [b|].
  - rewrite IH. reflexivity.
  - destruct (memory_read segs a 1) as [[|b rest]|]; try reflexivity.
    rewrite IH. reflexivity.
Qed.

Lemma rd_bytes_length : ltac2:(tb__ "0|2|
S7bS66Q40A1SeScS66Q8A1M0A1M1S0SfG1A1S24R4R3R2A3S10G1R1A2A3S0SeS11G0R2A2R3A3F_;Fbs;Fk;Fa;Fms;").
Proof using .
  intros ms a k. revert a. induction k as [|k IH]; intros a bs H; cbn in H.
  - inversion H. reflexivity.
  - destruct (rd ms a); [|discriminate]. destruct (rd_bytes ms _ k) eqn:E; [|discriminate].
    inversion H. cbn. f_equal. eapply IH. eauto.
Qed.

Lemma rd_bytes_nth : ltac2:(tb__ "0|4|
S7bSeS66Q40M0A1ScS66Q8M1A1M2A1M3SeS0SfG3A1S24R5R3R4A3S10G3R2A2A3S87R2R5A2S6bS6cS68G0R5A2S70R6A1A2S6eZ2Z40A2A2S0SfG2A1S4dR8S67G0S6cS68G0R6A2S70R4A1A2A2A2S10G2S8aG2R4R5S67G1Z0A2A4A2A3F_;F_;F_;Fj;Fbs;Fa;Fk;Fms;").
Proof using .
  intros ms k. induction k as [|k IH]; intros a bs j H Hj Hnw; [lia|].
  cbn in H. destruct (rd ms a) as [b|] eqn:Hb; [|discriminate].
  destruct (rd_bytes ms _ k) as [rest|] eqn:E; [|discriminate]. inversion H; subst.
  destruct j as [|j].
  - cbn. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hb.
  - cbn [nth]. rewrite Nat2Z.inj_succ.
    rewrite Nat2Z.inj_succ in Hnw.
    replace (bv_unsigned a + Z.succ (Z.of_nat j)) with (bv_unsigned (a + 1)%bv + Z.of_nat j)
      by (rewrite u_add1; lia).
    apply IH; [exact E | lia |]. rewrite u_add1; lia.
Qed.

Lemma rd_bytes_of_nth : ltac2:(tb__ "0|4|
S7bSeS66Q40M0A1ScS66Q8M1A1M2A1M3S0SeS11G2R1A2R3A3S6bS6cS68G0R3A2S70R4A1A2S6eZ2Z40A2A2SeS87R1R6A2S0SfG2A1S4dR8S67G0S6cS68G0R6A2S70R2A1A2A2A2S10G2S8aG2R2R5S67G1Z0A2A4A2A3F_;Fj;S0SfG3A1S24R7R5R6A3S10G3R4A2A3F_;F_;F_;Fbs;Fa;Fk;Fms;").
Proof using .
  intros ms k. induction k as [|k IH]; intros a bs Hlen Hnw Hall.
  - destruct bs; [reflexivity | cbn in Hlen; lia].
  - destruct bs as [|b rest]; [cbn in Hlen; lia|]. cbn in Hlen.
    rewrite Nat2Z.inj_succ in Hnw.
    cbn. pose proof (Hall 0%nat ltac:(lia)) as H0. cbn [Z.of_nat nth] in H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0.
    rewrite H0.
    destruct k as [|k'].
    + destruct rest; [reflexivity | cbn in Hlen; lia].
    + rewrite (IH (a + 1)%bv rest); [reflexivity | lia | |].
      * rewrite u_add1; [lia|]. rewrite Nat2Z.inj_succ in Hnw. lia.
      * intros j Hj. rewrite u_add1 by (rewrite Nat2Z.inj_succ in Hnw; lia).
        specialize (Hall (S j) ltac:(lia)). rewrite Nat2Z.inj_succ in Hall. cbn [nth] in Hall.
        replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.succ (Z.of_nat j)) by lia. exact Hall.
Qed.

Lemma Z_to_le_bytes_length : ltac2:(tb__ "0|0|
SeS8S0SeS11S66Q8A1Sc7R2R1A2A2R2A3Fz;Fk;").
Proof using . induction k; intros; cbn; auto. Qed.

Lemma Z_to_le_bytes_nth : ltac2:(tb__ "0|2|
SeS8SeS87R1R3A2S0S66Q8M0A1M1S8aG1R2Sc7R4R3A2S67G0Z0A2A4S67G0S77R3S6fZ8S70R2A1A2A2A2A3F_;Fj;Fz;Fk;").
Proof using .
  induction k as [|k IH]; intros z j Hj; [lia|].
  cbn [Z_to_le_bytes]. destruct j as [|j].
  - cbn. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma Z_to_bv8_eq_bits : ltac2:(tb__ "0|1|
S8S8S8S1S6bZ0R1A2S6dR1Z8A2A2S0SbS75R4R2A2S75R3R2A2A3F_;Fi;S0S66Q8M0A1S67G0R3A2S67G0R2A2A3F_;Fy;Fx;").
Proof using .
  intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 8).
  - rewrite !Z.mod_pow2_bits_low by lia. apply H. lia.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma Z_to_le_bytes_mod : ltac2:(tb__ "0|0|
SeS8S0ScS66Q8A1A1Sc7R2S72R1S6eZ2S6fZ8S70R2A1A2A2A2A2Sc7R2R1A2A3Fz;Fk;").
Proof using .
  intros k z. apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0).
  - rewrite !Z_to_le_bytes_length. reflexivity.
  - intros n Hn. rewrite Z_to_le_bytes_length in Hn.
    rewrite !Z_to_le_bytes_nth by lia. apply Z_to_bv8_eq_bits. intros i Hi.
    rewrite !Z.shiftr_spec by lia. apply Z.mod_pow2_bits_low. lia.
Qed.

Lemma bytes_le_to_Z_spec' : ltac2:(tb__ "0|3|
ScS66Q8M0A1M1A1S8S6bZ0R1A2S0SbS75Sc5R3A1R2A2SfG1A1SbLx;Sc4G1R3S71S79R2Z8M2A2A1A3G1S75S68G0R1A2S72R3G2A2A2Lb;S14Xfx2A3F_;Fi;Fbs;").
Proof using .
  induction bs as [|b rest IH]; intros i Hi; cbn [bytes_le_to_Z].
  - rewrite Z.bits_0. destruct (Z.to_nat (i / 8)); reflexivity.
  - rewrite Z.lor_spec.
    pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with (2 ^ 8) in Hb.
    destruct (Z.lt_ge_cases i 8).
    + rewrite Z.shiftl_spec_low by lia. rewrite Bool.orb_false_r.
      replace (Z.to_nat (i / 8)) with 0%nat by (rewrite Z.div_small by lia; reflexivity).
      cbn. rewrite Z.mod_small by lia. reflexivity.
    + rewrite Z.shiftl_spec_high by lia. rewrite IH by lia.
      rewrite (bv_unsigned_spec_high i 8 b) by (cbn; lia). cbn [orb].
      assert (Hd : 1 <= i / 8) by (apply Z.div_le_lower_bound; lia).
      replace (Z.to_nat (i / 8)) with (S (Z.to_nat ((i - 8) / 8))).
      * cbn [nth_error]. replace ((i - 8) mod 8) with (i mod 8); [reflexivity|].
        replace (i - 8) with (i + (-1) * 8) by lia. rewrite Z.mod_add by lia. reflexivity.
      * replace (i - 8) with (i + (-1) * 8) by lia. rewrite Z.div_add by lia.
        rewrite <- Z2Nat.inj_succ by lia. f_equal. lia.
Qed.

Lemma bytes_le_to_Z_nonneg : ltac2:(tb__ "0|0|
ScS66Q8A1A1S6bZ0Sc5R1A1A2Fbs;").
Proof using .
  induction bs; cbn; [lia|]. apply Z.lor_nonneg. split; [apply bv_unsigned_in_range|].
  apply Z.shiftl_nonneg. exact IHbs.
Qed.

Lemma bytes_le_to_Z_bits_high : ltac2:(tb__ "0|1|
ScS66Q8A1M0A1S8S6bS6fZ8S70S11G0R2A2A1A2R1A2S0SbS75Sc5R3A1R2A2S14A3F_;Fi;Fbs;").
Proof using .
  intros bs i Hi. rewrite bytes_le_to_Z_spec' by lia.
  rewrite (proj2 (nth_error_None bs (Z.to_nat (i / 8)))); [reflexivity|].
  assert (Z.of_nat (length bs) <= i / 8) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma bytes_le_to_Z_bound : ltac2:(tb__ "0|2|
ScS66Q8A1M0A1S1S6bZ0Sc5R1A1M1A2S6dG1S6eZ2S6fZ8S70S11G0R1A2A1A2A2A2A2Fbs;").
Proof using .
  intros bs. pose proof (bytes_le_to_Z_nonneg bs).
  split; [lia|].
  apply (proj2 (Z.bounded_iff_bits_nonneg (8 * Z.of_nat (length bs)) _ ltac:(lia) H)).
  intros l Hl. apply bytes_le_to_Z_bits_high. lia.
Qed.

Lemma Z_to_le_bytes_bytes_le_to_Z : ltac2:(tb__ "0|2|
ScS66Q8A1M0A1M1S0G1Sc7S11G0R1A2Sc5R1A1A2R1A3Fbs;").
Proof using .
  intros bs. apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0).
  - apply Z_to_le_bytes_length.
  - intros n Hn. rewrite Z_to_le_bytes_length in Hn.
    rewrite Z_to_le_bytes_nth by lia.
    rewrite <- (Z_to_bv_bv_unsigned 8 (nth n bs (Z_to_bv 8 0))).
    apply Z_to_bv8_eq_bits. intros i Hi.
    rewrite Z.shiftr_spec by lia. rewrite bytes_le_to_Z_spec' by lia.
    replace (Z.to_nat ((i + 8 * Z.of_nat n) / 8)) with n.
    2:{ replace (i + 8 * Z.of_nat n) with (i + Z.of_nat n * 8) by lia. rewrite Z.div_add by lia.
        rewrite Z.div_small by lia. lia. }
    rewrite (nth_error_nth' bs (Z_to_bv 8 0)) by lia.
    f_equal. replace (i + 8 * Z.of_nat n) with (i + Z.of_nat n * 8) by lia. rewrite Z.mod_add by lia.
    apply Z.mod_small. lia.
Qed.

Lemma bytes_le_to_Z_Z_to_le_bytes : ltac2:(tb__ "0|0|
SeS8S6bZ0R1A2S0S8Sc5Sc7R3R2A2A1S72R2S6eZ2S6fZ8S70R3A1A2A2A2A3F_;Fz;Fk;").
Proof using .
  intros k z Hz. apply Z.bits_inj'. intros i Hi.
  rewrite bytes_le_to_Z_spec' by lia.
  destruct (Z.lt_ge_cases i (8 * Z.of_nat k)).
  - rewrite Z.mod_pow2_bits_low by lia.
    assert (Hn : (Z.to_nat (i / 8) < k)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia). apply Z.div_lt_upper_bound; lia. }
    rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by (rewrite Z_to_le_bytes_length; exact Hn).
    rewrite Z_to_le_bytes_nth by exact Hn. rewrite Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
    rewrite Z.mod_pow2_bits_low by (apply Z.mod_pos_bound; lia).
    rewrite Z.shiftr_spec by (apply Z.mod_pos_bound; lia). f_equal.
    rewrite Z2Nat.id by (apply Z.div_pos; lia).
    rewrite (Z.div_mod i 8) at 1 by lia. lia.
  - rewrite Z.mod_pow2_bits_high by lia.
    rewrite (proj2 (nth_error_None _ _)); [reflexivity|].
    rewrite Z_to_le_bytes_length.
    apply Nat2Z.inj_le. rewrite Z2Nat.id by (apply Z.div_pos; lia). apply Z.div_le_lower_bound; lia.
Qed.

Lemma extract_le_word_enc : ltac2:(tb__ "0|2|
SaSeS66Q40M0A1S0SaR3SbeQ8Sc0R2A1A2A3S88R3U8A2S0S66R5A1S69G0Q0M1R5Sc6S35R4R3A2A1A4S69G0G1R5R3A4A3F_;F_;Fv;Fk;Fw;").
Proof using .
  intros w k v Hw Hk. subst w. unfold le_bytes_to_word, enc_bytes.
  apply bv_eq. rewrite !bv_extract_unsigned, !Z.shiftr_0_r, Z_to_bv_unsigned.
  pose proof (urange v) as Hv.
  rewrite bytes_le_to_Z_Z_to_le_bytes by lia.
  unfold bv_wrap. rewrite two64.
  replace (Z.of_N (8 * N.of_nat k)) with (8 * Z.of_nat k) by lia.
  unfold bv_modulus. replace (Z.of_N (8 * N.of_nat k)) with (8 * Z.of_nat k) by lia.
  rewrite (Z.mod_small (v.(bv_unsigned) mod 2 ^ (8 * Z.of_nat k)) (2 ^ 64)).
  - apply Z.mod_mod. apply Z.pow_nonzero; lia.
  - pose proof (Z.mod_pos_bound (bv_unsigned v) (2 ^ (8 * Z.of_nat k)) ltac:(apply Z.pow_pos_nonneg; lia)).
    assert (2 ^ (8 * Z.of_nat k) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Definition acc_ok (acc : cell_read) : Prop := ltac2:(tb__ "0|0|
S8cOLacc;Vacc;S1aS7Lv;S1aS8S7Lsh;Lv;S6S6S6X8cx5").

Lemma acc_ok_tile : ltac2:(tb__ "0|0|
S8cSdaR1A1SdaS8cS8cLacc;R2S1aS93Lv;S1aS8S93Lsh;Lv;S93S93SafX8cx5A1F_;Facc;").
Proof using . intros acc H. destruct acc; cbn in *; auto. Qed.

Lemma read_cells_exact : ltac2:(tb__ "0|0|
ScS21A1ScS1dA1S1aS8S8cS1aSdaR2A1S0S8cS9aR7R6R5R4R3A5SadR2A1A3S3S1dS1dS1Sc2S1dR1R8A3S1S0S1aS3fR1A1R4A3S1S0S8S34R1A1R6A3S0S90S94R9R7R6R1A4S92Z0A1A3A2A2A2Lc;A2F_;F_;Fv;Facc;Fk;Foff;Fcells;Ffacts;").
Proof using .
  intros facts cells off k. induction cells as [|c rest IH]; intros acc v Hacc H; cbn in H.
  - subst acc. destruct Hacc.
  - destruct (cell_rel facts off k c) as [d| |] eqn:Hcr.
    + destruct (lit_overlaps d (c_width c) k) eqn:Ho.
      * destruct ((d =? 0) && (c_width c =? k))%bool eqn:E.
        -- inversion H; subst. apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
           subst d. exists c. split; [left; reflexivity|]. auto.
        -- destruct ((d <=? 0) && (k <=? d + c_width c))%bool; [discriminate|].
           destruct (IH _ _ (acc_ok_tile acc Hacc) H) as (c' & Hin & R). exists c'. split; [right; exact Hin | exact R].
      * destruct (IH _ _ Hacc H) as (c' & Hin & R). exists c'. split; [right; exact Hin | exact R].
    + destruct (IH _ _ Hacc H) as (c' & Hin & R). exists c'. split; [right; exact Hin | exact R].
    + destruct (IH CRUnknown _ I H) as (c' & Hin & R). exists c'. split; [right; exact Hin | exact R].
Qed.

Lemma read_cells_inside : ltac2:(tb__ "0|0|
ScS21A1ScS1dA1S1aS8S8cS1aS8SdaR3A1S0S8cS9aR8R7R6R5R4A5SaeR3R2A2A3S3S1dS1dS3S8S8S1Sc2S1dR2RaA3S1S0S1aS3fR2A1R6A3S1S0S90S94RbR9R8R2A4S92R1A1A3S1S6bR1Z0A2S1S6bR8S6cR1S34R2A1A2A2S0S8R5S76R1A1A3A2A2A2A2A2Ld;A2Lc;A2F_;F_;Fsh;Fv;Facc;Fk;Foff;Fcells;Ffacts;").
Proof using .
  intros facts cells off k. induction cells as [|c rest IH]; intros acc v sh Hacc H; cbn in H.
  - subst acc. destruct Hacc.
  - destruct (cell_rel facts off k c) as [d| |] eqn:Hcr.
    + destruct (lit_overlaps d (c_width c) k) eqn:Ho.
      * destruct ((d =? 0) && (c_width c =? k))%bool eqn:E; [discriminate|].
        destruct ((d <=? 0) && (k <=? d + c_width c))%bool eqn:E2.
        -- inversion H; subst. apply andb_prop in E2 as [A B]. apply Z.leb_le in A. apply Z.leb_le in B.
           exists c, d. split; [left; reflexivity|]. repeat split; auto.
        -- destruct (IH _ _ _ (acc_ok_tile acc Hacc) H) as (c' & d' & Hin & R). exists c', d'. split; [right; exact Hin | exact R].
      * destruct (IH _ _ _ Hacc H) as (c' & d' & Hin & R). exists c', d'. split; [right; exact Hin | exact R].
    + destruct (IH _ _ _ Hacc H) as (c' & d' & Hin & R). exists c', d'. split; [right; exact Hin | exact R].
    + destruct (IH CRUnknown _ _ I H) as (c' & d' & Hin & R). exists c', d'. split; [right; exact Hin | exact R].
Qed.

Definition cell_skippable (facts : list sprop) (off : sv) (k : Z) (c : cell) : Prop := ltac2:(tb__ "0|1|
S2S0S90S94Vfacts;Voff;Vk;Vc;A4M0SacA3S3S8S8S1S0S90G0S92R1A1A3S0SbSb6R1S34Vc;A1Vk;A3S14A3A2Ld;A2A2").

Lemma read_cells_none : ltac2:(tb__ "0|0|
ScS21A1ScS1dA1S1aS8S8cS0S8cS9aR5R4R3R2R1A5S9dA3S1S0S8cR2S9dA3S1dSc2S1dR1R6A3SdbR8R6R5R2A4F_;Fc;A2F_;Facc;Fk;Foff;Fcells;Ffacts;").
Proof using .
  intros facts cells off k. induction cells as [|c rest IH]; intros acc H; cbn in H.
  - split; [exact H | intros c []].
  - destruct (cell_rel facts off k c) as [d| |] eqn:Hcr.
    + destruct (lit_overlaps d (c_width c) k) eqn:Ho.
      * destruct ((d =? 0) && (c_width c =? k))%bool; [discriminate|].
        destruct ((d <=? 0) && (k <=? d + c_width c))%bool; [discriminate|].
        destruct (IH _ H) as [Hacc _]. destruct acc; discriminate.
      * destruct (IH _ H) as [Hacc Hall]. split; [exact Hacc|].
        intros c' [<-|Hin]; [right; exists d; auto | apply Hall; exact Hin].
    + destruct (IH _ H) as [Hacc Hall]. split; [exact Hacc|].
      intros c' [<-|Hin]; [left; exact Hcr | apply Hall; exact Hin].
    + destruct (IH _ H) as [Hacc _]. discriminate.
Qed.

Lemma lit_cells_spec : ltac2:(tb__ "0|1|
ScS21A1ScS1dA1S1aS8S8S8S1aSc2S12S12S8S8A2M0S1aA2S13G0S1aS13S8S8R3R2A4R1A4Sb5R7R6R5R4A4A3S3S1dS1dS1Sc2S1dR1R8A3S1S0S90S94R9R7R6R1A4S92R5A1A3S1S0S8S34R1A1R4A3S0S1aS3fR1A1R3A3A2A2A2Lc;A2F_;Fv;Fw;Fd;Fk;Foff;Fcells;Ffacts;").
Proof using .
  intros facts cells off k d w v. induction cells as [|c rest IH]; cbn; intros H; [destruct H|].
  destruct (cell_rel facts off k c) as [d0| |] eqn:Hcr.
  - destruct H as [H|H].
    + inversion H; subst. exists c. split; [left; reflexivity|]. auto.
    + destruct (IH H) as (c' & Hin & R). exists c'. split; [right; exact Hin | exact R].
  - destruct (IH H) as (c' & Hin & R). exists c'. split; [right; exact Hin | exact R].
  - destruct (IH H) as (c' & Hin & R). exists c'. split; [right; exact Hin | exact R].
Qed.

Lemma find_lcell_at_spec : ltac2:(tb__ "0|3|
ScS12S12S8S8A2M0S1aA2M1A1S8S8S1aS0SfS12S8S1aA2M2A1Sb1R4R3A2S10G2S13S8S1aR2R1A4A2A3Sc2G1S13G0S1aS13S8S8R4R3A4R2A4R5A3F_;Fv;Fw;Fp;Fcells;").
Proof using .
  induction cells as [|[[d w0] v0] t IH]; intros p w v H; cbn in H; [discriminate|].
  destruct (Z.eqb_spec d p) as [->|Hne].
  - inversion H; subst. left. reflexivity.
  - right. apply IH. exact H.
Qed.

Lemma in_cell_dec : ltac2:(tb__ "0|1|
S1cS8S1dSe4S60R3R2R1A3M0S4G0A1A2Fc;Foff;Frho;").
Proof using .
  intros rho off c. unfold in_cell.
  destruct (Z_le_dec (soff rho (c_off c)) off); [|right; lia].
  destruct (Z_lt_dec off (soff rho (c_off c) + c_width c)); [left; lia | right; lia].
Qed.

Lemma covered_dec : ltac2:(tb__ "0|1|
S1cScS1dA1S8Se4S40R3R2R1A3M0S4G0A1A2Foff;Fcells;Frho;").
Proof using . intros rho cells off. unfold covered. apply Exists_dec. intros c. apply in_cell_dec. Qed.

Lemma covered_cons : ltac2:(tb__ "0|0|
S1cS1dScS1dA1S8S4S40R4S18S1dR3R2A3R1A3A1S4S40R5R3R2A3A1F_;Foff;Fcells;Fc;Frho;").
Proof using . intros rho c cells off H Hc. apply H. unfold covered in *. apply Exists_cons_tl. exact Hc. Qed.

Definition uncovered (rho : valuation) (cells : list cell) (off k : Z) : Prop := ltac2:(tb__ "0|0|
S8S1S6bVoff;R1A2S6dR1S6cVoff;Vk;A2A2A2S4S40Vrho;Vcells;R2A3A1F_;Fj;").

Lemma oaddr_unsigned : ltac2:(tb__ "0|2|
S1cS1aS8S1S6bZ0S6cS68Q40M0S22R3R2A2A2R1A2M1A2S6dG1S6eZ2Z40A2A2A2S0S8S68G0S2dR4R3R2A3A2S6cS68G0S22R4R3A2A2R2A2A3F_;Foff;Fbase;Frho;").
Proof using .
  intros rho base off H. unfold oaddr. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64. exact H.
Qed.

Lemma enc_bytes_length : ltac2:(tb__ "0|0|
SeS66Q40A1S0SeS11S66Q8A1S35R2R1A2A2R2A3Fv;Fk;").
Proof using . intros. unfold enc_bytes. apply Z_to_le_bytes_length. Qed.

Lemma obj_read_cell : ltac2:(tb__ "0|4|
S1cS7bS1bS1dS8S8S23Vsegs;R6R5R4A4Sc2S1dR4S2fR5A1A3S6bS34R5A1Z8M0A2S6bS1eR9S44R6A1A2R5A2S6bS6cR6R5A2S6cS1eRaS44R7A1A2S34R7A1A2A2S6dZ0R6A2S0SfScS66Q8A1A1M1A1S24RbS2dRcS26RaA1R8A3S71R7A1M2A3S10G1S35G2S67Q40M3S77S68G3S22RcS3fR9A1A2A2S6fG0S74R8S1eRcS44R9A1A2A2A2A2A2A2A2A3F_;F_;F_;F_;F_;F_;Fk;Foff;Fc;Fo;Fms;Frho;").
Proof using .
  intros rho ms o c off k (Hb & Hw & Hcells & Hd & Hdl) Hin H8 Hc1 Hc2 Hk.
  pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as (Hlo & Hhi & Hch).
  pose proof (urange (eval rho (c_val c))) as Hv.
  unfold obj_lo_of, obj_hi_of in *.
  apply rd_bytes_of_nth.
  - apply enc_bytes_length.
  - rewrite oaddr_unsigned by lia. rewrite Z2Nat.id by lia. lia.
  - intros j Hj. rewrite oaddr_unsigned by lia.
    pose proof (rd_bytes_nth ms (Z.to_nat (c_width c)) (oaddr rho (ob_base o) (soff rho (c_off c))) _
                  (Z.to_nat (off - soff rho (c_off c)) + j)%nat Hch
                 ltac:(lia) ltac:(rewrite oaddr_unsigned by lia; rewrite Z2Nat.id by lia; lia)) as R.
    rewrite oaddr_unsigned in R by lia.
    match type of R with rd ms (Z_to_bv 64 ?X) = _ =>
      replace X with (bv_unsigned (eval rho (ob_base o)) + off + Z.of_nat j) in R by lia end.
    rewrite R. f_equal. unfold enc_bytes. rewrite !Z_to_le_bytes_nth by lia.
    rewrite Z_to_bv_unsigned. apply Z_to_bv8_eq_bits. intros i Hi.
    rewrite !Z.shiftr_spec by lia. unfold bv_wrap. rewrite two64.
    rewrite Z.mod_pow2_bits_low by lia.
    rewrite Z.shiftr_spec by lia. f_equal. lia.
Qed.

Lemma obj_read_zero : ltac2:(tb__ "0|3|
S1cS7bS1bS8S8S23Vsegs;R5R4R3A4S0S42S41R4A1S5eA3S6bS29R7R5A2R4A2S6bS6cR5R4A2S2bR8R6A2A2S6dZ0M0R5A2Sd9RaS2fR8A1R7R6A4S0SfScS66Q8A1A1M1A1S24RaS2dRbS26R9A1R8A3S71R7A1M2A3S10G1S35G2S67Q40G0A2A2A2A3F_;F_;F_;F_;F_;F_;Fk;Foff;Fo;Fms;Frho;").
Proof using .
  intros rho ms o off k (Hb & Hw & Hcells & Hd & Hdl) Hz Hlo Hhi Hk Hnone.
  apply rd_bytes_of_nth.
  - apply enc_bytes_length.
  - rewrite oaddr_unsigned by lia. rewrite Z2Nat.id by lia. lia.
  - intros j Hj. rewrite oaddr_unsigned by lia.
    assert (Hcov : ~ covered rho (ob_cells o) (off + Z.of_nat j)) by (apply Hnone; lia).
    assert (Hr : obj_lo_of rho o <= off + Z.of_nat j < obj_hi_of rho o) by lia.
    specialize (Hd (off + Z.of_nat j) Hr Hcov).
    rewrite Hz in Hd. cbn in Hd. rewrite Z.add_assoc in Hd. rewrite Hd. f_equal.
    unfold enc_bytes. rewrite Z_to_le_bytes_nth by lia. rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma sublist_length : ltac2:(tb__ "0|2|
S8S8ScS66Q8A1M0A1S6bZ0R3A2M1G1S6bS6cR5R4A2S70S11G0R3A2A1A2S0SeS11G0S4eR6R5R4A3A2S71R5A1A3F_;F_;F_;Fl;Fk;Fi;").
Proof using .
  intros i k l Hi Hk Hle. unfold sublist. rewrite firstn_length, length_skipn. lia.
Qed.

Lemma sublist_nth : ltac2:(tb__ "0|1|
S8S8ScS66Q8A1M0A1SeG0S6bZ0R5A2S87R3S71R5A1A2S0G0S8aG0R4S4eR7R6R5A3R3A4S8aG0Sd3S71R7A1R4A2R5R3A4A3F_;F_;Fd;Fj;Fl;Fk;Fi;").
Proof using .
  intros i k l j d Hi Hj. unfold sublist. rewrite nth_firstn.
  destruct (Nat.ltb_spec j (Z.to_nat k)); [|lia]. rewrite nth_skipn. reflexivity.
Qed.

Lemma obj_read_list : ltac2:(tb__ "0|1|
S1cS7bS1bS8S8S9S23Vsegs;R6R5R4A4S0S42S41R5A1S5cR2A1A3S6bS29R8R6A2R5A2S6bS6cR6R5A2S2bR9R7A2A2S6dZ0R6A2Sd9RbS2fR9A1R8R7A4S0SfScS66Q8A1A1M0A1S24RbS2dRcS26RaA1R9A3S71R8A1A3S10G0S4eS74R9S29RcRaA2A2R8S49RcR7A2A3A2A3F_;F_;F_;F_;F_;F_;Fl;Fk;Foff;Fo;Fms;Frho;").
Proof using .
  intros rho ms o off k l (Hb & Hw & Hcells & Hd & Hdl) Hz Hlo Hhi Hk Hnone.
  rewrite Hz in Hdl. cbn in Hdl.
  apply rd_bytes_of_nth.
  - apply sublist_length; lia.
  - rewrite oaddr_unsigned by lia. rewrite Z2Nat.id by lia. lia.
  - intros j Hj. rewrite oaddr_unsigned by lia.
    assert (Hcov : ~ covered rho (ob_cells o) (off + Z.of_nat j)) by (apply Hnone; lia).
    assert (Hr : obj_lo_of rho o <= off + Z.of_nat j < obj_hi_of rho o) by lia.
    specialize (Hd (off + Z.of_nat j) Hr Hcov).
    rewrite Hz in Hd. cbn in Hd. rewrite Z.add_assoc in Hd. rewrite Hd. f_equal.
    rewrite sublist_nth by lia. f_equal. lia.
Qed.

Lemma obj_read_rom : ltac2:(tb__ "0|1|
S1cS7bS1bS8S8S9S23Vsegs;R6R5R4A4S0S42S41R5A1S5dR2A1A3S6bS29R8R6A2R5A2S6bS6cR6R5A2S2bR9R7A2A2S6dZ0R6A2Sd9RbS2fR9A1R8R7A4S0SfScS66Q8A1A1M0A1S24RbS2dRcS26RaA1R9A3S71R8A1A3S10G0S4eS74R9S29RcRaA2A2R8S49RcR7A2A3A2A3F_;F_;F_;F_;F_;F_;Fl;Fk;Foff;Fo;Fms;Frho;").
Proof using .
  intros rho ms o off k l (Hb & Hw & Hcells & Hd & Hdl) Hz Hlo Hhi Hk Hnone.
  rewrite Hz in Hdl. cbn in Hdl.
  apply rd_bytes_of_nth.
  - apply sublist_length; lia.
  - rewrite oaddr_unsigned by lia. rewrite Z2Nat.id by lia. lia.
  - intros j Hj. rewrite oaddr_unsigned by lia.
    assert (Hcov : ~ covered rho (ob_cells o) (off + Z.of_nat j)) by (apply Hnone; lia).
    assert (Hr : obj_lo_of rho o <= off + Z.of_nat j < obj_hi_of rho o) by lia.
    specialize (Hd (off + Z.of_nat j) Hr Hcov).
    rewrite Hz in Hd. cbn in Hd. rewrite Z.add_assoc in Hd. rewrite Hd. f_equal.
    rewrite sublist_nth by lia. f_equal. lia.
Qed.

Lemma image_bytes_spec : ltac2:(tb__ "0|3|
S8SeScS66Q8M0A1M1A1M2S0SfG2A1S97Vsegs;R3R2A3S10G2R1A2A3S1S0SeS11G1R2A2R3A3SeS87R1R4A2S0SfG1A1S57Vsegs;S67Q40S6cR6S70R2A1A2A2A2S10G1S8aG1R2R4S67G0Z0A2A4A2A3F_;Fj;A2F_;Fbs;Fk;Fa;").
Proof using .
  intros a k. revert a. induction k as [|k IH]; intros a bs H; cbn in H.
  - inversion H. split; [reflexivity | intros; lia].
  - destruct (image_byte segs (Z_to_bv 64 a)) as [b|] eqn:Hb; [|discriminate].
    destruct (image_bytes segs (a + 1) k) as [rest|] eqn:Hr; [|discriminate].
    inversion H; subst. destruct (IH _ _ Hr) as [Hlen Hall].
    split; [cbn; lia|]. intros j Hj. destruct j as [|j].
    + cbn. rewrite Z.add_0_r. exact Hb.
    + cbn [nth]. rewrite Nat2Z.inj_succ. replace (a + Z.succ (Z.of_nat j)) with (a + 1 + Z.of_nat j) by lia.
      apply Hall. lia.
Qed.

Lemma rd_rom : ltac2:(tb__ "0|2|
S7bS66Q40A1S37Vsegs;R2A2S0SfS66Q8A1M0A1M1S7fR3R2A2S17G0A1A3S0G1S4dR4R3A2S57Vsegs;R3A2A3F_;F_;Fa;Fms;").
Proof using . intros ms a Hrom Hnone. unfold rd, ms_read_byte. rewrite Hnone. apply Hrom. Qed.

Lemma obj_read_image : ltac2:(tb__ "0|3|
S1cS7bS1bS8S8ScS66Q8A1A1M0S37Vsegs;R5A2S23Vsegs;R7R6R5A4S0S42S41R6A1S5bA3S0S1aS26R7A1S3eZ0M1A1A3S6bS29RaR8A2R7A2S6bS6cR8R7A2S2bRbR9A2A2S6dG1R8A2Sd9RdS2fRbA1RaR9A4S0SfG0A1M2S97Vsegs;RbS71RaA1A3S10G0R9A2A3S0G2S24ReS2dRfS26RdA1RcA3S71RbA1A3S10G0RaA2A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fbs;Fk;Foff;Fo;Fms;Frho;").
Proof using .
  intros rho ms o off k bs Hrom (Hb & Hw & Hcells & Hd & Hdl) Hz Hbase Hlo Hhi Hk Hnone Hib.
  destruct (image_bytes_spec _ _ _ Hib) as [Hlen Hall].
  rewrite Hbase in *. cbn [eval] in *.
  assert (H0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity. rewrite H0 in *.
  apply rd_bytes_of_nth.
  - exact Hlen.
  - rewrite oaddr_unsigned by (cbn [eval]; rewrite H0; lia). cbn [eval]. rewrite H0. rewrite Z2Nat.id by lia. lia.
  - intros j Hj. rewrite oaddr_unsigned by (cbn [eval]; rewrite H0; lia). cbn [eval]. rewrite H0.
    assert (Hcov : ~ covered rho (ob_cells o) (off + Z.of_nat j)) by (apply Hnone; lia).
    assert (Hr : obj_lo_of rho o <= off + Z.of_nat j < obj_hi_of rho o) by lia.
    specialize (Hd _ Hr Hcov). rewrite Hz in Hd. cbn in Hd. destruct Hd as [Hnone' _].
    rewrite Z.add_0_l in Hnone'. rewrite Z.add_0_l. rewrite (rd_rom ms _ Hrom Hnone'). apply Hall. lia.
Qed.

Lemma all_ro_spec : ltac2:(tb__ "0|0|
S8SeSeS0SbS9eVsegs;R3R2A3SdA3S87R2R3A2S0SbS64Vsegs;S67Q40S6cR5S70R3A1A2A2A2SdA3F_;F_;Fj;Fk;Fa;").
Proof using .
  intros a k. revert a. induction k as [|k IH]; intros a j H Hj; [lia|].
  cbn in H. apply andb_prop in H as [H1 H2]. destruct j as [|j].
  - cbn. rewrite Z.add_0_r. exact H1.
  - rewrite Nat2Z.inj_succ. replace (a + Z.succ (Z.of_nat j)) with (a + 1 + Z.of_nat j) by lia. apply IH; [exact H2|lia].
Qed.

Lemma ro_read : ltac2:(tb__ "0|2|
S7bS8SeScS66Q8A1A1M0S37Vsegs;R4A2S58Vsegs;R5A2S6bZ0R5A2S6bS6cR6S70R5A1A2S6eZ2Z40A2A2S87U0R6A2S0SbS9eVsegs;R8R7A3SdA3S0SfG0A1M1S97Vsegs;R9R8A3S10G0R7A2A3S0G1S24RbS67Q40RaA2R9A3S10G0R8A2A3F_;F_;F_;F_;F_;F_;F_;Fbs;Fk;Fa;Fms;").
Proof using .
  intros ms a k bs Hrom Hroc Ha Hnw Hk Hro Hib.
  destruct (image_bytes_spec _ _ _ Hib) as [Hlen Hall].
  apply rd_bytes_of_nth; [exact Hlen | |].
  - rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; lia). lia.
  - intros j Hj. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; lia).
    rewrite (rd_rom ms _ Hrom).
    + apply Hall. lia.
    + apply Hroc. apply all_ro_spec with (k := k); [exact Hro | lia].
Qed.

Lemma ro_span_read : ltac2:(tb__ "0|1|
S1cScS21A1S7bS1aSeS37Vsegs;R3A2S58Vsegs;R4A2S89S21S32R7A1R6A3S87U0R4A2S0SbSbcVsegs;R8R6S70R5A1A4SdA3S3ScS66Q8A1A1M0G0S0SfG0A1S24R9S22RbR8A2R7A3S10G0R1A2A3Lbs;A2F_;F_;F_;F_;F_;Fk;Fae;Fms;Ffacts;Frho;").
Proof using .
  intros rho facts ms ae k Hrom Hroc Hf Hk H. unfold ro_span, M64 in H.
  pose proof (itv_sound rho facts ae Hf) as I. destruct (itv facts ae) as [lo hi]. unfold in_itv in I. cbn [fst snd] in I.
  destruct (Z.leb_spec lo hi); [|discriminate].
  destruct (Z.leb_spec (hi + Z.of_nat k - lo) ro_span_max); [|discriminate].
  destruct (Z.leb_spec (hi + Z.of_nat k) (2 ^ 64)); [|discriminate].
  destruct (all_ro segs lo (Z.to_nat (hi + Z.of_nat k - lo))) eqn:Hro; [|discriminate].
  destruct (image_bytes segs lo (Z.to_nat (hi + Z.of_nat k - lo))) as [bs0|] eqn:Hib; [|discriminate]. clear H.
  destruct (image_bytes_spec _ _ _ Hib) as [Hlen Hall].
  pose proof (urange (eval rho ae)) as R. set (a := bv_unsigned (eval rho ae)) in *.
  set (d := Z.to_nat (a - lo)).
  exists (map (fun j => nth (d + j)%nat bs0 (Z_to_bv 8 0)) (seq 0 k)).
  apply rd_bytes_of_nth.
  - rewrite length_map, length_seq. reflexivity.
  - lia.
  - intros j Hj.
    assert (NTH : nth j (map (fun j0 : nat => nth (d + j0) bs0 (Z_to_bv 8 0)) (seq 0 k)) (Z_to_bv 8 0) = nth (d + j) bs0 (Z_to_bv 8 0)).
    { apply nth_error_nth. apply (map_nth_error (fun j0 : nat => nth (d + j0) bs0 (Z_to_bv 8 0)) j (seq 0 k)).
      rewrite nth_error_seq. destruct (Nat.ltb_spec j k); [reflexivity | lia]. }
    rewrite NTH. fold a.
    assert (E : a + Z.of_nat j = lo + Z.of_nat (d + j)) by (subst d; rewrite Nat2Z.inj_add, Z2Nat.id by lia; lia).
    rewrite E. rewrite (rd_rom ms _ Hrom).
    + apply Hall. subst d. apply Nat2Z.inj_lt. rewrite Nat2Z.inj_add, !Z2Nat.id by lia. lia.
    + apply Hroc. apply all_ro_spec with (k := Z.to_nat (hi + Z.of_nat k - lo)); [exact Hro|].
      subst d. apply Nat2Z.inj_lt. rewrite Nat2Z.inj_add, !Z2Nat.id by lia. lia.
Qed.

Lemma obj_wf_parts : ltac2:(tb__ "0|0|
S9S1bS0SbS25R2R1A2SdA3S1S0SbS20R3S26R2A1A2SdA3S1S0SbS20R3S52R2A1A2SdA3S1S0SbS20R3S51R2A1A2SdA3S0SbSc3S1dS45R3A1S2fR2A1A3SdA3A2A2A2F_;Fo;Fn;").
Proof using .
  intros n o H. unfold obj_wf in H.
  apply andb_prop in H as [H Hd]. apply andb_prop in H as [H Hc]. apply andb_prop in H as [H Hhi]. apply andb_prop in H as [Hb Hlo].
  repeat split; assumption.
Qed.

Lemma obj_wf_cell : ltac2:(tb__ "0|1|
S9S1bS1dS0SbS25R3R2A2SdA3Sc2S1dR2S2fR3A1A3S1S6dZ0S34R3A1M0A2S1S6bG0Z8A2S1S0SbS20R5S44R3A1A2SdA3S0SbS20R5S3fR3A1A2SdA3A2A2A2F_;F_;Fc;Fo;Fn;").
Proof using .
  intros n o c Hwf Hin. destruct (obj_wf_parts n o Hwf) as (_ & _ & _ & Hcells).
  pose proof (proj1 (forallb_forall _ _) Hcells c Hin) as Hc. unfold cell_wf in Hc.
  apply andb_prop in Hc as [Hc E4]. apply andb_prop in Hc as [Hc E3]. apply andb_prop in Hc as [E1 E2].
  apply Z.ltb_lt in E1. apply Z.leb_le in E2. repeat split; assumption.
Qed.

Lemma soff_agree : ltac2:(tb__ "0|0|
S9S1cS1cS1aS31R4R3R2A3S0SbS20R5R2A2SdA3S0S8S1eR4R3A2S1eR5R3A2A3F_;F_;Fe;Frho';Frho;Fn;").
Proof using . intros n rho rho' e Hag Hb. unfold soff. rewrite (eval_agree n rho rho' e Hag Hb). reflexivity. Qed.

Lemma obj_range_agree : ltac2:(tb__ "0|0|
S9S1cS1cS1bS31R4R3R2A3S0SbS25R5R2A2SdA3S0S12S8S8A2S30R4R3A2S30R5R3A2A3F_;F_;Fo;Frho';Frho;Fn;").
Proof using .
  intros n rho rho' o Hag Hwf. destruct (obj_wf_parts n o Hwf) as (Hb & Hlo & Hhi & _).
  unfold obj_range, obj_lo_of, obj_hi_of.
  rewrite <- (eval_agree n rho rho' _ Hag Hb), (soff_agree n rho rho' _ Hag Hlo), (soff_agree n rho rho' _ Hag Hhi).
  reflexivity.
Qed.

Lemma covered_agree : ltac2:(tb__ "0|0|
S9S1cS1cScS1dA1S8S31R5R4R3A3S0SbSc3S1dS45R6A1R3A3SdA3S5S40R5R4R3A3S40R6R4R3A3A2F_;F_;Foff;Fcells;Frho';Frho;Fn;").
Proof using .
  intros n rho rho' cells off Hag Hcells. unfold covered. rewrite !Exists_exists.
  assert (E : forall c, In c cells -> soff rho' (c_off c) = soff rho (c_off c)).
  { intros c Hin. pose proof (proj1 (forallb_forall _ _) Hcells c Hin) as Hc. unfold cell_wf in Hc.
    apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [_ Ho]. eapply soff_agree; eauto. }
  unfold in_cell. split; intros (c & Hin & Hc); exists c; split; auto.
  - rewrite <- (E c Hin). exact Hc.
  - rewrite (E c Hin). exact Hc.
Qed.

Lemma obj_holds_agree : ltac2:(tb__ "0|0|
S9S1cS1cS7bS1bS31R5R4R3A3S0SbS25R6R2A2SdA3S23Vsegs;R6R4R3A4S23Vsegs;R6R5R4A4F_;F_;F_;Fo;Fms;Frho';Frho;Fn;").
Proof using .
  intros n rho rho' ms o Hag Hwf (Hb & Hw & Hc & Hd & Hdl).
  destruct (obj_wf_parts n o Hwf) as (Hbase & Hlo & Hhi & Hcells).
  pose proof (eval_agree n rho rho' _ Hag Hbase) as Ebase.
  pose proof Hag as (_ & HL & _).
  assert (Elo : obj_lo_of rho' o = obj_lo_of rho o) by (unfold obj_lo_of; eapply soff_agree; eauto).
  assert (Ehi : obj_hi_of rho' o = obj_hi_of rho o) by (unfold obj_hi_of; eapply soff_agree; eauto).
  unfold obj_holds. rewrite <- Ebase, Elo, Ehi. split; [exact Hb|]. split; [exact Hw|]. split; [|split].
  2:{ intros off Hoff Hcov. rewrite (covered_agree n rho rho' _ off Hag Hcells) in Hcov.
      specialize (Hd off Hoff Hcov). destruct (ob_dflt o); cbn in *; rewrite <- ?HL; exact Hd. }
  2:{ eapply dflt_inv_agree; [exact Hag | apply obj_wf_dflt; exact Hwf | exact Hdl]. }
  apply Forall_forall. intros c Hin. pose proof (proj1 (Forall_forall _ _) Hc c Hin) as Hch.
  pose proof (proj1 (forallb_forall _ _) Hcells c Hin) as Hcw.
  unfold cell_wf in Hcw. apply andb_prop in Hcw as [Hcw Hv]. apply andb_prop in Hcw as [_ Ho].
  unfold cell_holds in *. unfold oaddr in *. rewrite <- Ebase.
  rewrite (soff_agree n rho rho' _ Hag Ho), <- (eval_agree n rho rho' _ Hag Hv). exact Hch.
Qed.

Lemma pairwise_disjoint_agree : ltac2:(tb__ "0|0|
S9S1cS1cScS1bA1S31R4R3R2A3S0SbSc3S1bS25R5A1R2A3SdA3S48R5R3A2S48R5R4A2F_;F_;F_;Fobjs;Frho';Frho;Fn;").
Proof using .
  intros n rho rho' objs Hag. induction objs as [|o rest IH]; intros Hwf Hpd; [exact I|].
  cbn in Hwf. apply andb_prop in Hwf as [Ho Hrest]. destruct Hpd as [Hf Hpd].
  split; [|apply IH; assumption].
  apply Forall_forall. intros o' Hin. pose proof (proj1 (Forall_forall _ _) Hf o' Hin) as H.
  rewrite (obj_range_agree n rho rho' o Hag Ho).
  rewrite (obj_range_agree n rho rho' o' Hag (proj1 (forallb_forall _ _) Hrest o' Hin)). exact H.
Qed.

Lemma smatch_agree : ltac2:(tb__ "0|0|
S1cS1cS1fS12ScS85A1S82A2S31S28R2A1R4R3A3S27Vsegs;R5R3R2A4S27Vsegs;R5R4R3A4F_;F_;Fw;FS;Frho';Frho;").
Proof using .
  intros rho rho' S [tr [ms md]] Hag Hsm.
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  pose proof Hwf as Hwf0. unfold swf in Hwf.
  repeat (apply andb_prop in Hwf; destruct Hwf as [Hwf ?]).
  unfold smatch. cbn [fst snd cfg_ms cfg_model] in *.
  split; [exact Hwf0|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hroc|].
  split.
  { intros r Hr. rewrite (Hregs r Hr). apply (eval_agree (ss_next S)); [exact Hag|].
    unfold reg_sv. destruct (bv_unsigned r =? 0); [reflexivity|]. apply forallb_nth; [assumption|reflexivity]. }
  split.
  { intros r. rewrite (Hfregs r). apply (eval_agree (ss_next S)); [exact Hag|].
    unfold freg_sv. apply forallb_nth; [assumption|reflexivity]. }
  split.
  { destruct (ss_fcsr S); cbn in *; [exact Hfcsr|]. rewrite <- (eval_agree (ss_next S) rho rho'); assumption. }
  split.
  { unfold resv_match in *. destruct (ss_resv S); [|exact Hresv]. destruct (ms_resv ms); [|exact Hresv].
    rewrite <- (eval_agree (ss_next S) rho rho'); assumption. }
  split.
  { destruct Hmem as (Hall & Hpd & Hfr). split; [|split].
    - apply Forall_forall. intros o Hin. eapply obj_holds_agree; [exact Hag| |].
      + exact (proj1 (forallb_forall _ _) (swf_objs S Hwf0) o Hin).
      + exact (proj1 (Forall_forall _ _) Hall o Hin).
    - eapply pairwise_disjoint_agree; [exact Hag | exact (swf_objs S Hwf0) | exact Hpd].
    - intros a Ha. pose proof Hag as (_ & _ & HM). rewrite <- HM. apply Hfr.
      unfold outside_all in *. apply Forall_forall. intros o Hin.
      rewrite <- (obj_range_agree (ss_next S) rho rho' o Hag (proj1 (forallb_forall _ _) (swf_objs S Hwf0) o Hin)).
      exact (proj1 (Forall_forall _ _) Ha o Hin). }
  apply Forall_forall. intros p Hin. apply (holds_agree (ss_next S) rho rho' p Hag).
  - exact (proj1 (forallb_forall _ _) (swf_facts S Hwf0) p Hin).
  - exact (proj1 (Forall_forall _ _) Hfacts p Hin).
Qed.

Lemma mem_match_nth : ltac2:(tb__ "0|0|
S1cScS1bA1S7bSeS1bS47Vsegs;R5R4R3A4S0SfS1bA1Sc4S1bR5R3A3S10S1bR2A2A3S23Vsegs;R7R5R3A4F_;F_;Fo;Fn;Fms;Fobjs;Frho;").
Proof using .
  intros rho objs ms n o [Hall _] Hn. apply nth_error_In in Hn.
  exact (proj1 (Forall_forall _ _) Hall o Hn).
Qed.

Lemma swf_obj_nth : ltac2:(tb__ "0|0|
S1fSeS1bS0SbS3dR3A1SdA3S0SfS1bA1Sc4S1bS3aR4A1R3A3S10S1bR2A2A3S0SbS25S28R5A1R3A2SdA3F_;F_;Fo;Fn;FS;").
Proof using .
  intros S n o Hwf Hn. apply nth_error_In in Hn.
  exact (proj1 (forallb_forall _ _) (swf_objs S Hwf) o Hn).
Qed.

Lemma find_obj_sound : ltac2:(tb__ "0|5|
S1cS1fScS85A1M0S7bS86S1aS8SeS1bS1aS27Vsegs;RaR9S13G0S82R8S83R7R6A2A4A4S6dZ0R5A2S0SfS12S12SeS1bA2M1S1aA2M2A1Sb2S3aRbA1S33RbA1R7R6U0A5S10G2S13G1S1aS13SeS1bR5R4A4R3A4A2A3S1S0SfS1bA1Sc4S1bS3aRcA1R6A3S10S1bR5A2A3S1S23Vsegs;RdRaR5A4S1S0SbS25S28RcA1R5A2SdA3S1S0SfS1aA1SbbS26R5A1M3R8A2S10S1aR4A2A3S1S0SbSb4S33RcA1S52R5A1S51R5A1R4R7A5SdA3S1S0S8SdcRdR8A2S6cSdcRdG3A2S1eRdR4A2M4A2A3S1S0S66Q40A1S22RdR8A2S2dRdG3G4A3A3S1S6bS29RdR5A2G4A2S6bS6cG4R7A2S2bRdR5A2A2A2A2A2A2A2A2A2A2F_;F_;F_;Foff;Fo;Fn;Fk;Fae;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md ae k n o off Hsm Hk Hfo.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf. pose proof (smatch_facts segs _ _ _ Hsm) as Hf.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmem & _). cbn [fst snd cfg_ms] in Hmem.
  destruct (find_obj_spec _ _ _ _ _ _ _ _ Hfo) as (i & Hn & Hnth & Hro & Hib). cbn in Hn. subst i.
  pose proof (mem_match_nth _ _ _ _ _ Hmem Hnth) as Hoh.
  pose proof (swf_obj_nth _ _ _ Hwf Hnth) as Howf.
  destruct (access_in_range segs rho ms o ae off k (ss_facts S) Hf Hoh Hro Hib Hk) as (HU & Hlo & Hhi).
  repeat (split; [assumption|]). split.
  - unfold oaddr. unfold U in HU. rewrite <- HU. symmetry. apply Z_to_bv_bv_unsigned.
  - split; assumption.
Qed.

Lemma skippable_uncovered : ltac2:(tb__ "0|1|
S1cScS21A1S7bS1bS1aS8S9S89S21S32R7A1R6A3S23Vsegs;R8R6R5A4S0SbS25R3R6A2SdA3S6bS29RaR7A2S1eRaR6A2A2S6bS6cS1eRbR7A2R6A2S2bRbR8A2A2S6dZ0R7A2S1dSc2S1dR1S2fRbA1M0A3SdbReRbRaR2A4F_;Fc;Sd9ReG0S1eReRaA2R9A4F_;F_;F_;F_;F_;F_;F_;Fn;Fk;Foff;Fo;Fms;Ffacts;Frho;").
Proof using .
  intros rho facts ms o off k n Hf Ho Hwf Hlo Hhi Hk Hsk j Hj Hcov.
  unfold covered in Hcov. apply Exists_exists in Hcov as (c & Hin & Hc). unfold in_cell in Hc.
  destruct (obj_wf_cell n o c Hwf Hin) as (W1 & W2 & _ & _).
  destruct (Hsk c Hin) as [Hd | (d & Hd & Hno)].
  - pose proof (cell_rel_disj_sound segs rho facts ms o off k c Hf Ho Hin Hlo Hhi ltac:(lia) Hd). lia.
  - pose proof (cell_rel_lit_sound segs rho facts ms o off k c d Hf Ho Hin Hlo Hhi ltac:(lia) ltac:(lia) Hd) as E.
    unfold lit_overlaps in Hno. apply Bool.andb_false_iff in Hno.
    destruct Hno as [Hno|Hno]; [apply Z.ltb_ge in Hno | apply Z.ltb_ge in Hno]; lia.
Qed.

Lemma ext_of_enc : ltac2:(tb__ "0|2|
SbSeS66Q40A1M0S88R2U8A2S0G0S2aR4SbeQ8Sc0R3A1A2M1Sc6S35R3R2A2A1A3S2aR4G1R2A3A3F_;Fx;Fk;Fsgn;").
Proof using .
  intros sgn k x Hk. unfold ext_low. rewrite (extract_le_word_enc (8 * N.of_nat k)%N k x eq_refl Hk). reflexivity.
Qed.

Lemma ext_low_zero : ltac2:(tb__ "0|2|
SbSaSc1Q0R1A2S0S66Q40M0A1S2aR3R2S67G0Z0A2M1A3G1A3F_;Fw;Fsgn;").
Proof using .
  intros sgn w Hw. unfold ext_low.
  assert (E : bv_extract 0 w (Z_to_bv 64 0) = Z_to_bv w 0).
  { apply bv_eq. rewrite bv_extract_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
    pose proof (bv_modulus_pos 64). pose proof (bv_modulus_pos w).
    rewrite (Z.mod_0_l (bv_modulus 64)) by lia.
    rewrite Z.shiftr_0_l. reflexivity. }
  rewrite E. destruct sgn.
  - unfold sext. apply bv_eq. rewrite bv_sign_extend_unsigned, Z_to_bv_signed, Z_to_bv_unsigned.
    pose proof (bv_modulus_pos 64). pose proof (bv_modulus_pos w).
    pose proof (bv_half_modulus_lt_modulus w). pose proof (bv_half_modulus_nonneg w).
    unfold bv_swrap, bv_wrap. rewrite (Z.mod_0_l (bv_modulus 64)) by lia.
    rewrite Z.add_0_l. rewrite (Z.mod_small (bv_half_modulus w)) by lia.
    rewrite Z.sub_diag. reflexivity.
  - unfold zext. apply bv_eq. rewrite bv_zero_extend_unsigned', !Z_to_bv_unsigned. unfold bv_wrap.
    rewrite !Z.mod_0_l by (pose proof (bv_modulus_pos 64); pose proof (bv_modulus_pos w); lia). reflexivity.
Qed.

End M.

Section M3.
Variable segs : list Segment.

Definition load_post (S : sstate) (rho : valuation) (ms : machine_state) (a : word) (k : Z) (sgn : bool)
  (v : sv) (S' : sstate) (tr : list event) (md : Model) : Prop := ltac2:(tb__ "0|6|
S3ScS66Q8M0A1A1M1G1S3S1cS1cS1S0SfG1A1S24Vms;Va;S71Vk;A1A3S10G1R2A2A3S1S31S28VS;A1M2Vrho;R1A3S1Sc8G2S28VS';A1M3A2S1S27Vsegs;R1VS';S13ScS85A1S82Vtr;S83Vms;Vmd;A2A4A4S1S0S66Q40A1S22R1Vv;A2S2aVsgn;SbeG0S73Vk;A1A2Sc6R2A1A3A3S1S0SbS20G3Vv;A2SdA3S1S0S8S2eVS';A1S2eVS;A1A3S1S0ScS1aA1M4S3bVS';A1S3bVS;A1A3S1S0G4S39VS';A1S39VS;A1A3S1S0S59S38VS';A1S38VS;A1A3S1S0SfS1aA1S3cVS';A1S3cVS;A1A3S3ScS21A1M5G5S0G5S33VS';A1S15S21R1S33VS;A1A3A3LF;A2A2A2A2A2A2A2A2A2A2A2A2Lrho';A2Lbs;A2").

Lemma load_post_same : ltac2:(tb__ "0|4|
S1fS1cS7bS66Q40A1M0S8SbS1aScS85A1M1S86ScS66Q8M2A1A1M3S27Vsegs;R9RaS13G1S82R3S83R8R2A2A4A4S0SfG3A1S24R9R8S71R7A1A3S10G3R2A2A3S0G0S22RbR6A2S2aR7SbeG2S73R8A1A2Sc6R3A1A3A3S0SbS20S28RdA1R7A2SdA3SceReRdRcRbRaR9R8ReR7R6AaF_;F_;F_;F_;Fbs;Fmd;Ftr;Fv;Fsgn;Fk;Fa;Fms;Frho;FS;").
Proof using .
  intros. exists bs, rho. split; [assumption|]. split; [apply agree_below_refl|].
  split; [lia|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  repeat split; try reflexivity. exists []. reflexivity.
Qed.

Lemma k_cases : ltac2:(tb__ "0|4|
S8S2S0S8R1Z1A3S2S0S8R1Z2A3S2S0S8R1Z4A3S0S8R1Z8M0A3A2A2A2S1S6dZ0R2A2S1S6bR2G0A2S1S88S71R2A1M1U8A2S1S0SaSbeQ8M2S73R2A1A2M3SbeG2Sc0G1A1A2A3Sc1Q0G3A2A2A2A2A2F_;Fk;").
Proof using . intros k [->|[->|[->| ->]]]; cbn; repeat split; lia. Qed.

Lemma srl_lit_unsigned : ltac2:(tb__ "0|3|
S66Q40M0A1S8S6bZ0R1A2S6dS6fZ8M1R2A2Z40A2S0S8S68G0Se3Sd7R4S67G0S6fG1R3A2M2A2A3A2S77S68G0R4A2G2A2A3F_;F_;Fsh;Fx;").
Proof using .
  intros x sh H0 H1. unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite two64. rewrite (Z.mod_small (8 * sh)) by lia. change (63 mod 2 ^ 64) with 63.
  replace (Z.land (8 * sh) 63) with (8 * sh); [reflexivity|].
  change 63 with (Z.ones 6). rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. lia.
Qed.

Fixpoint pdr (rs : list (Z * Z)) : Prop :=
  match rs with [] => True | r :: rest => Forall (ranges_disjoint r) rest /\ pdr rest end.

Lemma pairwise_disjoint_pdr : ltac2:(tb__ "0|0|
S1cScS1bA1S5S48R2R1A2Sd2S8bS1bS12S8S8A2S30R2A1R1A4A1A2Fobjs;Frho;").
Proof using .
  intros rho objs. induction objs as [|o rest IH]; cbn; [tauto|].
  rewrite Forall_map. tauto.
Qed.

Lemma map_list_set : forall {A B} (f : A -> B) l n x, map f (list_set l n x) = list_set (map f l) n (f x).
Proof using . induction l; intros [|n] x; cbn; auto; rewrite IHl; reflexivity. Qed.

Lemma list_set_same : forall {A} (l : list A) n y, nth_error l n = Some y -> list_set l n y = l.
Proof using . induction l; intros [|n] y H; cbn in *; try discriminate; [inversion H; reflexivity| rewrite IHl; auto]. Qed.

Lemma pairwise_disjoint_set : ltac2:(tb__ "0|0|
S1cScS1bA1SeS1bS1bS0SfS1bA1Sc4S1bR4R3A3S10S1bR2A2A3S0S12S8S8A2S30R6R2A2S30R6R3A2A3S48R7R6A2S48R8S98S1bR7R6R4A4A2F_;F_;F_;Fo';Fo;Fn;Fobjs;Frho;").
Proof using .
  intros rho objs n o o' Hn Hr Hpd. apply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd.
  rewrite map_list_set, Hr. rewrite list_set_same; [exact Hpd|].
  rewrite nth_error_map, Hn. reflexivity.
Qed.

Lemma Forall_list_set : forall {A} (P : A -> Prop) l n x,
  Forall P l -> P x -> Forall P (list_set l n x).
Proof using .
  induction l as [|h t IH]; intros n x Hl Hx; cbn; [constructor|].
  inversion Hl; subst. destruct n; constructor; auto.
Qed.

Lemma outside_all_ranges : ltac2:(tb__ "0|3|
S1cScS1bA1S66Q40M0A1S5S53R3R2R1A3S89S12S8S8A2M1G1S4S1S6bS19S8S8R1A3S68G0R2A2M2A2S6dG2S16S8S8R1A3A2A2A1Lr;S8bS1bG1S30R3A1R2A4A3A2Fa;Fobjs;Frho;").
Proof using . intros rho objs a. unfold outside_all. rewrite Forall_map. reflexivity. Qed.

Lemma outside_all_set : ltac2:(tb__ "0|0|
S1cScS1bA1SeS1bS1bS66Q40A1S0SfS1bA1Sc4S1bR5R4A3S10S1bR3A2A3S0S12S8S8A2S30R7R3A2S30R7R4A2A3S5S53R8S98S1bR7R6R4A4R3A3S53R8R7R3A3A2F_;F_;Fa;Fo';Fo;Fn;Fobjs;Frho;").
Proof using .
  intros rho objs n o o' a Hn Hr. rewrite !outside_all_ranges.
  rewrite map_list_set, Hr, list_set_same; [reflexivity|]. rewrite nth_error_map, Hn. reflexivity.
Qed.

Lemma mem_match_set : ltac2:(tb__ "0|0|
S1cScS1bA1S7bSeS1bS1bS47Vsegs;R6R5R4A4S0SfS1bA1Sc4S1bR6R4A3S10S1bR3A2A3S0S12S8S8A2S30R8R3A2S30R8R4A2A3S23Vsegs;R9R7R4A4S47Vsegs;RaS98S1bR9R7R5A4R8A4F_;F_;F_;F_;Fo';Fo;Fn;Fms;Fobjs;Frho;").
Proof using .
  intros rho objs ms n o o' (Hall & Hpd & Hfr) Hn Hr Ho'. split; [|split].
  - apply Forall_list_set; assumption.
  - eapply pairwise_disjoint_set; eauto.
  - intros a Ha. apply Hfr. eapply (proj1 (outside_all_set rho objs n o o' a Hn Hr)). exact Ha.
Qed.

Lemma enc_bytes_le_word : ltac2:(tb__ "0|2|
SeScS66Q8A1M0A1M1S0SeS11G0R1A2R2A3S88R3U8A2S0G1S35R4Sc6R3A1A2R3A3F_;F_;Fbs;Fk;").
Proof using .
  intros k bs Hlen Hk. unfold enc_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb.
  assert (2 ^ (8 * Z.of_nat k) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite bv_wrap_small by (rewrite two64; lia). rewrite <- Hlen. apply Z_to_le_bytes_bytes_le_to_Z.
Qed.

Lemma smatch_set_objs_next : ltac2:(tb__ "0|1|
S1cS1fS12ScS85A1M0S82A2ScS1bA1S9SbS27Vsegs;R6R5R4A4S47Vsegs;R7R4S84S16G0S82R5A3A1A4S0SbS3dS36S2eR7A1S3bR7A1S39R7A1S38R7A1S3cR7A1R5S33R7A1R4R3A9A1SdA3S27Vsegs;R9S36S2eR8A1S3bR8A1S39R8A1S38R8A1S3cR8A1R6S33R8A1R5R4A9R7A4F_;F_;F_;Flm;Fnx;Fobjs;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] objs nx lm Hsm Hmm Hwf.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  unfold smatch; cbn [fst snd cfg_ms cfg_model ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts] in *.
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hroc|].
  split; [intros r Hr; apply Hregs; exact Hr|].
  split; [intros r; apply Hfregs|].
  split; [exact Hfcsr|]. split; [exact Hresv|]. split; [exact Hmm|]. exact Hfacts.
Qed.

Lemma forallb_mono_below : ltac2:(tb__ "0|1|
S9S9ScS1aA1Sc8R3R2A2S0SbSc3S1aS20R4A1M0R2A3SdA3S0SbSc3S1aG0R3A3SdA3F_;F_;Fl;Fm;Fn;").
Proof using .
  intros n m l Hle H. apply forallb_forall. intros x Hin. eapply sv_below_mono; [exact Hle|].
  exact (proj1 (forallb_forall _ _) H x Hin).
Qed.

Lemma sprop_below_mono : ltac2:(tb__ "0|0|
S9S9S21Sc8R3R2A2S0SbS4bR4R2A2SdA3S0SbS4bR4R3A2SdA3F_;F_;Fp;Fm;Fn;").
Proof using .
  intros n m p Hle. induction p; cbn; intros H; auto;
  try (apply andb_prop in H as [H1 H2]; rewrite (sv_below_mono _ _ _ Hle H1), (sv_below_mono _ _ _ Hle H2); reflexivity).
  apply Pos.ltb_lt in H. apply Pos.ltb_lt. lia.
Qed.

Lemma cell_wf_mono : ltac2:(tb__ "0|0|
S9S9S1dSc8R3R2A2S0SbS45R4R2A2SdA3S0SbS45R4R3A2SdA3F_;F_;Fc;Fm;Fn;").
Proof using .
  intros n m c Hle H. unfold cell_wf in *.
  apply andb_prop in H as [H Hv]. apply andb_prop in H as [H Ho].
  rewrite H. cbn. rewrite (sv_below_mono _ _ _ Hle Ho), (sv_below_mono _ _ _ Hle Hv). reflexivity.
Qed.

Lemma tf_below_mono : ltac2:(tb__ "0|0|
S9S9S2cSc8R3R2A2S0SbS4fR4R2A2SdA3S0SbS4fR4R3A2SdA3F_;F_;Ft;Fm;Fn;").
Proof using . intros n m t Hle H. unfold tf_below in *. eapply sv_below_mono; eauto. Qed.

Lemma dflt_wf_mono : ltac2:(tb__ "0|0|
S9S9S42Sc8R3R2A2S0SbS56R4R2A2SdA3S0SbS56R4R3A2SdA3F_;F_;Fd;Fm;Fn;").
Proof using .
  intros n m d Hle H. destruct d; cbn in *; try reflexivity.
  apply andb_prop in H as [Hc Ht]. rewrite (sv_below_mono _ _ _ Hle Hc). cbn.
  apply forallb_forall. intros t Hin. eapply tf_below_mono; [exact Hle|]. exact (proj1 (forallb_forall _ _) Ht t Hin).
Qed.

Lemma obj_wf_mono : ltac2:(tb__ "0|0|
S9S9S1bSc8R3R2A2S0SbS25R4R2A2SdA3S0SbS25R4R3A2SdA3F_;F_;Fo;Fm;Fn;").
Proof using .
  intros n m o Hle H. destruct (obj_wf_parts n o H) as (Hb & Hlo & Hhi & Hc). pose proof (obj_wf_dflt n o H) as Hd. unfold obj_wf.
  rewrite (sv_below_mono _ _ _ Hle Hb), (sv_below_mono _ _ _ Hle Hlo), (sv_below_mono _ _ _ Hle Hhi). cbn.
  rewrite (dflt_wf_mono _ _ _ Hle Hd), Bool.andb_true_r.
  apply forallb_forall. intros c Hin. eapply cell_wf_mono; [exact Hle|].
  exact (proj1 (forallb_forall _ _) Hc c Hin).
Qed.

Lemma swf_mono_next : ltac2:(tb__ "0|0|
S1fS9Sc8S28R2A1R1A2S0SbS3dR3A1SdA3S0SbS3dS36S2eR4A1S3bR4A1S39R4A1S38R4A1S3cR4A1S3aR4A1S33R4A1R3S43R4A1A9A1SdA3F_;F_;Fm;FS;").
Proof using .
  intros S m Hle Hwf. unfold swf in *. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next] in *.
  repeat (apply andb_prop in Hwf; destruct Hwf as [Hwf ?]).
  rewrite Hwf, H5. cbn [andb].
  rewrite (forallb_mono_below _ _ _ Hle H4), (forallb_mono_below _ _ _ Hle H3).
  repeat (apply andb_true_intro; split); try reflexivity.
  - destruct (ss_fcsr S); [reflexivity|]. eapply sv_below_mono; eauto.
  - destruct (ss_resv S); [|reflexivity]. eapply sv_below_mono; eauto.
  - apply forallb_forall. intros o Hin. eapply obj_wf_mono; [exact Hle|]. exact (proj1 (forallb_forall _ _) H0 o Hin).
  - apply forallb_forall. intros p Hin. eapply sprop_below_mono; [exact Hle|]. exact (proj1 (forallb_forall _ _) H p Hin).
Qed.

Lemma swf_lenient_irrel : ltac2:(tb__ "0|1|
S8ScS1aA1M0G0S59SfS1aA1ScS1bA1ScS21A1S9SbSbS0SbS3dS36RaR9R8R7R6R5R4R3R2A9A1S3dS36RaR9R8R7R6R5R4R3R1A9A1A3Fl2;Fl1;Fnx;Ffacts;Fobjs;Fresv;Ffcsr;Ffregs;Fregs;Fpc;").
Proof using . reflexivity. Qed.

Lemma lrok_inj : ltac2:(tb__ "0|0|
S1aS1fS1aS1fS0S8eS8dR4R3A2S8dR2R1A2A3S1S0S1aR5R3A3S0S1fR4R2A3A2F_;FS2;Fv2;FS1;Fv1;").
Proof using . intros. inversion H. auto. Qed.

Lemma obj_wf_add_cell : ltac2:(tb__ "0|0|
S9S1bS1aS8S0SbS25R4R3A2SdA3S0SbS20R5R3A2SdA3S6dZ0R3A2S6bR4Z8A2S0SbS25ScdR8A1Sa6R7R6R5S4cR8A1A4A2SdA3F_;F_;F_;F_;Fk;Foff;Fo;Fn;").
Proof using .
  intros n o off k Hwf Hoff Hk Hk8.
  pose proof (obj_wf_mono n (Pos.succ n) o ltac:(lia) Hwf) as Hwf'.
  destruct (obj_wf_parts _ _ Hwf') as (Hb & Hlo & Hhi & Hc).
  unfold obj_wf, obj_add_cell. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt forallb].
  rewrite Hb, Hlo, Hhi, Hc, (obj_wf_dflt _ _ Hwf'). unfold cell_wf. cbn [c_off c_width c_val sv_below].
  rewrite (sv_below_mono n (Pos.succ n) off ltac:(lia) Hoff).
  rewrite (proj2 (Z.ltb_lt 0 k)) by lia. rewrite (proj2 (Z.leb_le k 8)) by lia.
  rewrite (proj2 (Pos.ltb_lt n (Pos.succ n))) by lia. reflexivity.
Qed.

Lemma obj_holds_add_cell : ltac2:(tb__ "0|0|
S1cS7bS1bS1aS8S1aS23Vsegs;R6R5R4A4S55R7S26R5A1S29R7R5A2S2bR7R5A2R6S61R4R3R2A3A6S23Vsegs;R8R7Sa6R6R5R4R3A4A4F_;F_;Fv;Fk;Foff;Fo;Fms;Frho;").
Proof using .
  intros rho ms o off k v (Hb & Hw & Hc & Hd & Hdl) Hcell.
  unfold obj_holds, obj_add_cell, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  split; [exact Hb|]. split; [exact Hw|]. split; [constructor; [exact Hcell | exact Hc]|].
  split; [|exact Hdl].
  intros off' Hoff' Hcov. apply Hd; [exact Hoff'|]. eapply covered_cons. exact Hcov.
Qed.

Lemma obj_byte_readable : ltac2:(tb__ "0|2|
S1cS7bS1bS8S9S37Vsegs;R4A2S0SbS25R2R4A2SdA3S23Vsegs;R7R6R5A4S1S6bS29R8R6A2R5A2S6dR5S2bR8R6A2A2A2S3S66Q8A1M0G0S0SfG0A1S4dR9S67Q40M1S6cS68G1S22RaS26R8A1A2A2R7A2A2A2S10G0R1A2A3Lb;A2F_;F_;F_;F_;Fn;Foff;Fo;Fms;Frho;").
Proof using .
  intros rho ms o off n Hrom Hwf Ho Hoff.
  pose proof Ho as (Hb & Hw & Hcells & Hd & Hdl).
  destruct (covered_dec rho (ob_cells o) off) as [Hcov|Hcov].
  - unfold covered in Hcov. apply Exists_exists in Hcov as (c & Hin & Hc). unfold in_cell in Hc.
    pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as (W1 & W2 & Hch).
    unfold obj_lo_of, obj_hi_of in *.
    pose proof (rd_bytes_nth ms _ _ _ (Z.to_nat (off - soff rho (c_off c))) Hch ltac:(lia)) as R.
    rewrite oaddr_unsigned in R by lia.
    specialize (R ltac:(lia)).
    replace (bv_unsigned (eval rho (ob_base o)) + soff rho (c_off c) + Z.of_nat (Z.to_nat (off - soff rho (c_off c))))
      with (bv_unsigned (eval rho (ob_base o)) + off) in R by lia.
    eexists; exact R.
  - specialize (Hd off Hoff Hcov). destruct (ob_dflt o); cbn in Hd.
    + exact Hd.
    + eexists; exact Hd.
    + destruct Hd as [Hnone [b Hib]]. exists b. unfold rd, ms_read_byte. rewrite Hnone. rewrite Hrom. exact Hib.
    + eexists; exact Hd.
    + eexists; exact Hd.
    + exact Hd.
Qed.

Lemma obj_bytes_readable : ltac2:(tb__ "0|3|
S1cS7bS1bS8SeS9S37Vsegs;R5A2S0SbS25R2R5A2SdA3S23Vsegs;R8R7R6A4S6bS29R9R7A2R6A2S6bS6cR7S70R6A1A2S2bRaR8A2A2S3ScS66Q8A1M0A1M1G1S1S0SfG1A1S24RbS67Q40M2S6cS68G2S22RcS26RaA1A2A2R9A2A2R8A3S10G1R1A2A3S0SeS11G0R1A2R8A3A2Lbs;A2F_;F_;F_;F_;F_;Fn;Fk;Foff;Fo;Fms;Frho;").
Proof using .
  intros rho ms o off k n Hrom Hwf Ho. revert off.
  induction k as [|k IH]; intros off Hlo Hhi.
  - exists []. split; reflexivity.
  - cbn [rd_bytes]. rewrite Nat2Z.inj_succ in Hhi.
    destruct (obj_byte_readable rho ms o off n Hrom Hwf Ho ltac:(lia)) as [b Hb]. rewrite Hb.
    pose proof (proj1 Ho) as HB.
    replace (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off) + 1)%bv
      with (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + (off + 1))).
    2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
        change (bv_unsigned (1%bv : bv 64)) with 1. rewrite Zplus_mod_idemp_l. f_equal. lia. }
    destruct (IH (off + 1) ltac:(lia) ltac:(lia)) as (bs & Hbs & Hlen). rewrite Hbs.
    exists (b :: bs). split; [reflexivity | cbn; lia].
Qed.

Lemma lor_disjoint_add : ltac2:(tb__ "0|2|
S8S8S6bZ0M0R2A2M1G1S0S8S78R4R3A2G0A3S0S8S7aR5R4A2S6cR5R4A2A3F_;F_;F_;Fb;Fa;").
Proof using . intros a b Ha Hb H. rewrite <- Z.lxor_lor by exact H. symmetry. apply Z.add_nocarry_lxor. exact H. Qed.

Lemma land_low_high : ltac2:(tb__ "0|3|
S8S8S8S6bZ0M0R1A2S1S6bG0R4A2M1S6dR4S6eZ2M2R2A2A2A2G1S0S8S78R6S6fR5S6eG2R4A2A2A2G0A3F_;F_;F_;Fm;Fy;Fx;").
Proof using .
  intros x y m Hm Hx Hy. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i m).
  - rewrite (Z.mul_pow2_bits_low y m i) by lia. apply Bool.andb_false_r.
  - rewrite (testbit_high_small x m i) by lia. reflexivity.
Qed.

Lemma bytes_le_to_Z_app : ltac2:(tb__ "0|2|
ScS66Q8A1M0A1M1G1S0S8Sc5S15G0R2R1A3A1S6cSc5R2A1S6fSc5R1A1S6eZ2S6fZ8S70S11G0R2A2A1A2A2A2A2A3Fl2;Fl1;").
Proof using .
  induction l1 as [|b t IH]; intros l2.
  - cbn [app bytes_le_to_Z length]. rewrite Z.mul_1_r. reflexivity.
  - cbn [app bytes_le_to_Z length]. rewrite IH.
    pose proof (bv_unsigned_in_range _ b) as Rb. change (bv_modulus 8) with (2^8) in Rb.
    pose proof (bytes_le_to_Z_nonneg t). pose proof (bytes_le_to_Z_nonneg l2).
    assert (P : 0 < 2 ^ (8 * Z.of_nat (length t))) by (apply Z.pow_pos_nonneg; lia).
    rewrite !Z.shiftl_mul_pow2 by lia.
    rewrite !lor_disjoint_add; try lia; try (apply land_low_high; lia || nia).
    + rewrite Nat2Z.inj_succ. replace (8 * Z.succ (Z.of_nat (length t))) with (8 * Z.of_nat (length t) + 8) by lia.
      rewrite Z.pow_add_r by lia. lia.
Qed.

Lemma rd_bytes_app : ltac2:(tb__ "0|5|
S7bS66Q40M0A1SeSeScS66Q8A1M1A1M2G2S0SfG2A1M3S24R6R5R4A3S10G2R2A2M4A3S0G3S24R7S6aG0R6S67G0S70R5A1A2A3R4A3G4A3S0G3S24R8R7Sd3R6R5A2A3S10G2S15G1R4R3A3A2A3F_;F_;Fbs2;Fbs1;Fk2;Fk1;Fa;Fms;").
Proof using .
  intros ms a k1. revert a. induction k1 as [|k1 IH]; intros a k2 bs1 bs2 H1 H2.
  - cbn in H1. inversion H1; subst. cbn [app Nat.add]. rewrite bv_add_0_r in H2. exact H2.
  - cbn [rd_bytes Nat.add] in H1 |- *. destruct (rd ms a) as [b|]; [|discriminate].
    destruct (rd_bytes ms (a + 1)%bv k1) as [r|] eqn:E; [|discriminate]. inversion H1; subst.
    rewrite (IH (a + 1)%bv k2 r bs2 E); [reflexivity|].
    rewrite <- H2. f_equal. apply bv_eq. rewrite !bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_unsigned (1%bv : bv 64)) with 1. rewrite Nat2Z.inj_succ. rewrite two64.
    rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l, Zplus_mod_idemp_r. f_equal. lia.
Qed.

Lemma tile_cells_sound : ltac2:(tb__ "0|4|
SeS1cS7bS1bS9S8ScS12S12S8S8A2M0S1aA2M1A1S8S8S1aS23Vsegs;R9R8R7A4S0SbS25R7R8A2SdA3S8S8S1aSc2G1S13G0S1aS13S8S8R3R2A4R1A4R9A3S3S1dS1dS1Sc2S1dR1S2fReA1A3S1S0S8S1eR10S44R1A1A2S6cRcR5A2A3S1S0S8S34R1A1R4A3S0S1aS3fR1A1R3A3A2A2A2Lc;A2F_;Fval;Fw;Fd;S0SfS1aA1SbdRdR7R6R5A4S10S1aR4A2A3S6bZ0R7A2S6bR8R7A2S6bR8Z8M2A2S3ScS66Q8A1A1M3G3S1S0SfG3A1S24R10S2dR11S26RfA1S6cRdRbA2A3S71S74RaRbA2A1A3S10G3R1A2A3S1S0S8S68Q40S22R11R9A2A2S6fSc5R1A1S6eZ2S6fG2RbA2A2A2A3S0SbS20ReR9A2SdA3A2A2Lbs;A2F_;F_;F_;F_;F_;F_;F_;Fv;Fstop;Fp;Flc;FA;Fn;Fo;Fms;Frho;Ffuel;").
Proof using .
  induction fuel as [|fuel IH]; intros rho ms o n A lc p stop v Ho Hwf Hlc Ht Hp0 Hps Hs8; cbn [tile_cells] in Ht; [discriminate|].
  destruct (Z.eqb_spec p stop) as [->|Hne].
  - inversion Ht; subst. exists []. rewrite Z.sub_diag. cbn. split; [reflexivity|]. split; [|reflexivity].
    rewrite Z_to_bv_unsigned. reflexivity.
  - destruct (find_lcell_at lc p) as [[w val]|] eqn:Hfc; [|discriminate].
    pose proof (find_lcell_at_spec _ _ _ _ Hfc) as Hinl.
    destruct (Hlc _ _ _ Hinl) as (c & Hin & Hcoff & Hcw & Hcv). subst w val.
    destruct ((0 <? c_width c) && (p + c_width c <=? stop))%bool eqn:Hc; [|discriminate].
    apply andb_prop in Hc as [Hw1 Hw2]. apply Z.ltb_lt in Hw1. apply Z.leb_le in Hw2.
    destruct (tile_cells fuel lc (p + c_width c) stop) as [rest|] eqn:Hr; [|discriminate].
    inversion Ht; subst v. clear Ht.
    destruct (obj_wf_cell _ _ _ Hwf Hin) as (C1 & C2 & C3 & C4).
    destruct (IH rho ms o n A lc (p + c_width c) stop rest Ho Hwf Hlc Hr ltac:(lia) ltac:(lia) Hs8) as (bs2 & Hrd2 & Hv2 & Hb2).
    pose proof (obj_read_cell segs rho ms o c (A + p) (c_width c) Ho Hin C2 ltac:(lia) ltac:(lia) ltac:(lia)) as R1.
    rewrite Hcoff, Z.sub_diag, Z.mul_0_r, Z.shiftr_0_r, Z_to_bv_bv_unsigned in R1.
    pose proof (proj1 Ho) as HB.
    exists (enc_bytes (Z.to_nat (c_width c)) (eval rho (c_val c)) ++ bs2).
    split.
    + replace (Z.to_nat (stop - p)) with (Z.to_nat (c_width c) + Z.to_nat (stop - (p + c_width c)))%nat by lia.
      apply rd_bytes_app; [exact R1|].
      rewrite <- Hrd2. f_equal. unfold oaddr. rewrite bv_add_ZZ. f_equal. rewrite Z2Nat.id by lia. lia.
    + split.
      * rewrite mk_alu_sound. unfold alu64 at 1. unfold alu at 1. rewrite bv_or_unsigned.
        rewrite mk_alu_sound. cbn [eval]. rewrite sll_val, mk_ext_sound. rewrite Hv2.
        rewrite bytes_le_to_Z_app, enc_bytes_length, Z2Nat.id by lia.
        unfold enc_bytes. rewrite bytes_le_to_Z_Z_to_le_bytes by (pose proof (urange (eval rho (c_val c))); lia).
        rewrite Z2Nat.id by lia.
        set (u := bv_unsigned (eval rho (c_val c))). set (w := c_width c) in *. set (s := p) in *.
        pose proof (Z.mod_pos_bound u (2 ^ (8 * w)) ltac:(apply Z.pow_pos_nonneg; lia)) as Hum.
        pose proof (bytes_le_to_Z_nonneg bs2) as Hb2n.
        assert (Hz : bv_unsigned (ext_low false (8 * Z.to_N w) (eval rho (c_val c))) = u mod 2 ^ (8 * w)).
        { unfold ext_low, zext. rewrite bv_zero_extend_unsigned', bv_extract_unsigned. unfold bv_wrap.
          rewrite two64. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. unfold bv_modulus.
          replace (Z.of_N (8 * Z.to_N w)) with (8 * w) by lia.
          apply Z.mod_small. split; [lia|]. eapply Z.lt_le_trans; [apply Hum|]. apply Z.pow_le_mono_r; lia. }
        rewrite Hz. replace ((8 * s) mod 64) with (8 * s) by (symmetry; apply Z.mod_small; lia).
        rewrite Z.shiftl_mul_pow2 by lia.
        assert (P1 : 0 < 2 ^ (8 * s)) by (apply Z.pow_pos_nonneg; lia).
        assert (P2 : 0 < 2 ^ (8 * w)) by (apply Z.pow_pos_nonneg; lia).
        pose proof (rd_bytes_length _ _ _ _ Hrd2) as L2.
        pose proof (bytes_le_to_Z_bound bs2) as B2. rewrite L2, Z2Nat.id in B2 by lia.
        assert (F : u mod 2 ^ (8 * w) * 2 ^ (8 * s) < 2 ^ 64).
        { apply (Z.lt_le_trans _ (2 ^ (8 * w) * 2 ^ (8 * s))); [nia|]. rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
        rewrite (Z.mod_small (u mod 2 ^ (8 * w) * 2 ^ (8 * s))) by nia.
        replace (8 * (s + w)) with (8 * w + 8 * s) by lia. rewrite Z.pow_add_r by lia.
        rewrite lor_disjoint_add; [nia | nia | nia |].
        replace (bytes_le_to_Z bs2 * (2 ^ (8 * w) * 2 ^ (8 * s))) with ((bytes_le_to_Z bs2 * 2 ^ (8 * w)) * 2 ^ (8 * s)) by lia.
        rewrite <- !Z.shiftl_mul_pow2 by lia. rewrite <- Z.shiftl_land.
        rewrite (Z.shiftl_mul_pow2 (bytes_le_to_Z bs2)) by lia. rewrite land_low_high; [apply Z.shiftl_0_l | lia | lia | lia].
      * apply mk_alu_below; [|exact Hb2]. apply mk_alu_below; [apply mk_ext_below; exact C4 | reflexivity].
Qed.

Definition rho_fresh (rho : valuation) (n : positive) (x : word) : valuation := ltac2:(tb__ "0|0|
S63S9SbS66Q40A1L_;ScbR1Vn;A2Vx;S4aVrho;R1A2Xbx2Li;S49Vrho;A1S54Vrho;A1A3").

Lemma rho_fresh_agree : ltac2:(tb__ "0|0|
S1cS9S66Q40A1S31R2R3Sd1R3R2R1A3A3Fx;Fn;Frho;").
Proof using .
  intros rho n x. split; [|split; intros; reflexivity]. intros i Hi. unfold rho_fresh. cbn.
  destruct (Pos.eqb_spec i n); [lia|reflexivity].
Qed.

Lemma rho_fresh_at : ltac2:(tb__ "0|1|
S1cS9S66Q40A1M0S0G0S4aSd1R3R2R1A3R2A2R1A3Fx;Fn;Frho;").
Proof using . intros. unfold rho_fresh. cbn. rewrite Pos.eqb_refl. reflexivity. Qed.

Lemma load_fresh_sound : ltac2:(tb__ "0|1|
S1cS1fScS85A1M0S7bS86SeS1bS1aS8SbS1aS1fS27Vsegs;RcRbS13G0S82RaS83R9R8A2A4A4S2S0S8R5Z1A3S2S0S8R5Z2A3S2S0S8R5Z4A3S0S8R5Z8A3A2A2A2S0SfS1bA1Sc4S1bS3aRdA1R9A3S10S1bR8A2A3S23Vsegs;RfRcR9A4S0SbS25S28RfA1RaA2SdA3S0SbS20S28R10A1RaA2SdA3S6bS29R12RcA2S1eR12RbA2A2S6bS6cS1eR13RcA2RbA2S2bR13RdA2A2S0S8eSb9R13RfReRdRcRbSbeQ8S73RcA1A2A7S8dRaR9A2A3SceR14R15R12S2dR15S26RfA1S1eR15ReA2A3RdRcRbRaR13R11AaF_;F_;F_;F_;F_;F_;F_;F_;F_;FS';Fv;Fsgn;Fk;Foff;Fo;Fn;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md n o off k sgn v S' Hsm Hk Hnth Hoh Howf Hoff Hlo Hhi Hlf.
  destruct (k_cases k Hk) as (Hk0 & Hk8 & Hkn & Hw & Hwpos).
  pose proof (smatch_swf _ _ _ _ Hsm) as Hwf.
  assert (Hrom : rom_ok segs ms) by (destruct Hsm as (_ & _ & _ & _ & Hrom & _); exact Hrom).
  unfold load_fresh, fresh in Hlf.
  pose proof (proj1 Hoh) as HB.
  destruct (obj_bytes_readable rho ms o (soff rho off) (Z.to_nat k) (ss_next S) Hrom Howf Hoh Hlo
              ltac:(rewrite Z2Nat.id by lia; lia)) as (bs & Hrd & Hlen).
  destruct (dflt_writable (ob_dflt o)) eqn:Hdw; apply lrok_inj in Hlf as [<- <-].
  2:{
    set (x := le_bytes_to_word bs). set (rho' := rho_fresh rho (ss_next S) x).
    pose proof (rho_fresh_agree rho (ss_next S) x) as Hag. pose proof (rho_fresh_at rho (ss_next S) x) as Hx.
    fold rho' in Hag, Hx.
    exists bs, rho'. split; [unfold oaddr; exact Hrd|]. split; [exact Hag|].
    cbn [snd ss_next ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_facts ss_objs].
    split; [lia|]. split.
    { pose proof (smatch_agree segs rho rho' S _ Hag Hsm) as Hsm1.
      apply (smatch_set_objs_next rho' S (tr, mkCfg ms md) (ss_objs S) (Pos.succ (ss_next S)) (ss_lenient S) Hsm1).
      - destruct Hsm1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmem1 & _). exact Hmem1.
      - apply (swf_mono_next S). lia. exact Hwf. }
    split.
    { rewrite mk_ext_sound. cbn [eval]. rewrite Hx. reflexivity. }
    split.
    { apply mk_ext_below. cbn. apply Pos.ltb_lt. lia. }
    repeat split; try reflexivity. exists []. reflexivity. }
  set (x := le_bytes_to_word bs). set (rho' := rho_fresh rho (ss_next S) x).
  pose proof (rho_fresh_agree rho (ss_next S) x) as Hag. pose proof (rho_fresh_at rho (ss_next S) x) as Hx.
  fold rho' in Hag, Hx.
  exists bs, rho'. split; [unfold oaddr; exact Hrd|]. split; [exact Hag|].
  cbn [ss_next ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_facts ss_objs ss_lenient set_objs].
  split; [lia|]. split.
  { pose proof (smatch_agree segs rho rho' S _ Hag Hsm) as Hsm1.
    apply (smatch_set_objs_next rho' S (tr, mkCfg ms md)
             (list_set (ss_objs S) n (obj_add_cell o off k (SVar (ss_next S)))) (Pos.succ (ss_next S)) (ss_lenient S) Hsm1).
    - cbn [snd cfg_ms]. eapply mem_match_set.
      + destruct Hsm1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmem1 & _). exact Hmem1.
      + exact Hnth.
      + reflexivity.
      + pose proof (obj_holds_agree segs (ss_next S) rho rho' ms o Hag Howf Hoh) as Hoh'.
        apply obj_holds_add_cell; [exact Hoh'|].
        destruct (obj_wf_parts _ _ Howf) as (Hb' & Hlo' & Hhi' & _).
        unfold cell_holds. cbn [c_off c_width c_val eval]. rewrite Hx.
        unfold obj_lo_of, obj_hi_of in *.
        rewrite !(soff_agree (ss_next S) rho rho') by assumption.
        split; [exact Hlo|]. split; [exact Hhi|].
        unfold x. rewrite (enc_bytes_le_word _ _ Hlen Hkn).
        unfold oaddr. rewrite <- (eval_agree _ _ _ _ Hag Hb'). exact Hrd.
    - pose proof (swf_mono_next S (Pos.succ (ss_next S)) ltac:(lia) Hwf) as W.
      unfold swf in W |- *. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next] in W |- *.
      repeat (apply andb_prop in W; destruct W as [W ?]).
      repeat (apply andb_true_intro; split); try assumption.
      apply forallb_list_set; [assumption|].
      apply obj_wf_add_cell; [exact Howf | exact Hoff | lia | lia]. }
  split.
  { rewrite mk_ext_sound. cbn [eval]. rewrite Hx. reflexivity. }
  split.
  { apply mk_ext_below. cbn. apply Pos.ltb_lt. lia. }
  repeat split; try reflexivity. exists []. reflexivity.
Qed.

Lemma snorm_id' : ltac2:(tb__ "0|1|
S8S1S6bS76S6eZ2Z3fA2M0A1R1A2S6dR1G0A2A2S0S8S91R2A1R2A3F_;Fz;").
Proof using .
  intros z H. unfold snorm.
  destruct (Z_lt_ge_dec z 0).
  - replace (z mod 2 ^ 64) with (z + 2 ^ 64) by (symmetry; rewrite <- (Z.mod_add z 1) by lia; apply Z.mod_small; lia).
    destruct (Z.ltb_spec (z + 2 ^ 64) (2 ^ 63)); lia.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec z (2 ^ 63)); lia.
Qed.

Lemma snorm_of_mod' : ltac2:(tb__ "0|0|
S8S0S8S91S72R1S6eZ2Z40A2A2A1S91R1A1A3Fz;").
Proof using . intros z. unfold snorm. rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma soff_mk_addk_M : ltac2:(tb__ "0|2|
S1cS1aS8S1S6bS76S6eZ2Z3fA2M0A1S6cS1eR3R2A2R1A2M1A2S6dG1G0A2A2S0S8S1eR4S99R3R2A2A2S6cS1eR4R3A2R2A2A3F_;Fk;Fe;Frho;").
Proof using .
  intros rho e k H. unfold soff at 1. rewrite mk_addk_sound, bv_add_Z, signed_lit.
  rewrite <- (snorm_id' (soff rho e + k)) by exact H.
  rewrite <- (snorm_of_mod' (bv_unsigned (eval rho e) + k)), <- (snorm_of_mod' (soff rho e + k)).
  f_equal. change (bv_unsigned (eval rho e)) with (U rho e).
  rewrite <- (soff_mod rho e). apply Zplus_mod_idemp_l.
Qed.

Fixpoint rho_exts (rho : valuation) (x0 : positive) (vals : list word) : valuation :=
  match vals with
  | [] => rho
  | v :: rest => rho_exts (rho_fresh rho x0 v) (Pos.succ x0) rest
  end.

Lemma rho_exts_rl_rm : ltac2:(tb__ "0|3|
S1cS9ScS66Q40A1M0A1S1S0S9ScS66Q8A1M1A1F_;S49ScfR3R2R1A3M2A1S49R3A1A3S0G0SfG1A1F_;S54G2A1S54R3A1A3A2Fvals;Fx0;Frho;").
Proof using .
  intros rho x0 vals. revert rho x0. induction vals as [|v rest IH]; intros rho x0; cbn; [auto|].
  destruct (IH (rho_fresh rho x0 v) (Pos.succ x0)) as [A B]. rewrite A, B. cbn. auto.
Qed.

Lemma rho_exts_below : ltac2:(tb__ "0|1|
S1cS9ScS66Q40A1M0A1S9SccR1R3A2S0G0S4aScfR5R4R3A3R2A2S4aR5R2A2A3F_;Fi;Fvals;Fx0;Frho;").
Proof using .
  intros rho x0 vals. revert rho x0. induction vals as [|v rest IH]; intros rho x0 i Hi; cbn; [reflexivity|].
  rewrite IH by lia. unfold rho_fresh. cbn. destruct (Pos.eqb_spec i x0); [lia|reflexivity].
Qed.

Lemma rho_exts_agree : ltac2:(tb__ "0|0|
S1cS9ScS66Q40A1A1S31R2R3ScfR3R2R1A3A3Fvals;Fx0;Frho;").
Proof using .
  intros rho x0 vals. split; [|split].
  - intros i Hi. symmetry. apply rho_exts_below. exact Hi.
  - intros l. rewrite (proj1 (rho_exts_rl_rm rho x0 vals)). reflexivity.
  - intros a. rewrite (proj2 (rho_exts_rl_rm rho x0 vals)). reflexivity.
Qed.

Lemma rho_exts_at : ltac2:(tb__ "0|1|
S1cS9ScS66Q40A1M0A1SeS87R1S11G0R2A2A2S0G0S4aScfR5R4R3A3ScaSd3Sc9R4A1R2A2A1A2S46R3R2A2A3F_;Fj;Fvals;Fx0;Frho;").
Proof using .
  intros rho x0 vals. revert rho x0. induction vals as [|v rest IH]; intros rho x0 j Hj; cbn in Hj; [lia|].
  destruct j as [|j].
  - cbn [rho_exts]. rewrite Nat.add_0_r, Pos2Nat.id. rewrite rho_exts_below by lia.
    unfold rho_fresh, fldv. cbn. rewrite Pos.eqb_refl. reflexivity.
  - cbn [rho_exts]. unfold fldv. cbn [nth].
    replace (Pos.to_nat x0 + S j)%nat with (Pos.to_nat (Pos.succ x0) + j)%nat by lia.
    rewrite (IH (rho_fresh rho x0 v) (Pos.succ x0) j) by lia. reflexivity.
Qed.

Lemma fld_vars_length : ltac2:(tb__ "0|0|
S9SeS0SeS11S1aS96R2R1A2A2R1A3Fm;Fx0;").
Proof using . intros x0 m. revert x0. induction m; intros; cbn; [reflexivity|]. rewrite IHm. reflexivity. Qed.

Lemma fld_vars_nth : ltac2:(tb__ "0|0|
S9SeSeS87R1R2A2S0S1aS8aS1aR2S96R4R3A2S3eZ0A1A4S4cScaSd3Sc9R4A1R2A2A1A1A3F_;Fj;Fm;Fx0;").
Proof using .
  intros x0 m. revert x0. induction m as [|m IH]; intros x0 j Hj; [lia|].
  destruct j as [|j]; cbn [fld_vars nth].
  - rewrite Nat.add_0_r, Pos2Nat.id. reflexivity.
  - rewrite IH by lia. f_equal. f_equal. lia.
Qed.

Lemma fld_vars_below : ltac2:(tb__ "0|0|
S9SeS0SbSc3S1aS20ScaSd3Sc9R2A1R1A2A1A1S96R2R1A2A3SdA3Fm;Fx0;").
Proof using .
  intros x0 m. revert x0. induction m as [|m IH]; intros x0; cbn [fld_vars forallb]; [reflexivity|].
  apply andb_true_intro. split.
  - cbn. apply Pos.ltb_lt. lia.
  - replace (Pos.to_nat x0 + S m)%nat with (Pos.to_nat (Pos.succ x0) + m)%nat by lia. apply IH.
Qed.

Lemma fld_index_sound : ltac2:(tb__ "0|1|
ScS12S8S8A2M0A1S8S8SeS0SfSeA1Sb3R4R3R2A3S10SeR1A2A3S0SfG0A1Sc4G0R5R2A3S10G0S13S8S8R4R3A4A2A3F_;Fi;Fk;Fc;Fflds;").
Proof using .
  induction flds as [|f rest IH]; intros c k i H; cbn in H; [discriminate|].
  destruct ((fst f =? c) && (snd f =? k))%bool eqn:E.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
    destruct f; cbn in *; subst; reflexivity.
  - destruct (fld_index rest c k) as [i'|] eqn:E2; [|discriminate]. cbn in H. injection H as <-. cbn. eapply IH. exact E2.
Qed.

Lemma nth_error_length_lt : forall {A} (l : list A) i x, nth_error l i = Some x -> (i < length l)%nat.
Proof using . intros A l i x H. apply nth_error_Some. congruence. Qed.

Lemma mod_mod_pow2 : ltac2:(tb__ "0|2|
S8S8S8S1S6bZ0R2A2S6bR2R1A2A2S0S8S72S72R4S6eZ2M0R2A2A2S6eG0R3A2M1A2S72R4G1A2A3F_;Fb;Fa;Fx;").
Proof using .
  intros x a b H. apply Z.mod_mod_divide.
  exists (2 ^ (b - a)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma mod_add_mul_pow2 : ltac2:(tb__ "0|2|
S8S8S8S8S1S6bZ0R2A2S6bR2R1A2A2S0S8S72S6cR5S6fR4S6eZ2M0R2A2A2A2S6eG0R3A2M1A2S72R5G1A2A3F_;Fb;Fa;Fk;Fx;").
Proof using .
  intros x k a b H. replace (k * 2 ^ b) with ((k * 2 ^ (b - a)) * 2 ^ a).
  - apply Z.mod_add. apply Z.pow_nonzero; lia.
  - rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. f_equal. f_equal. lia.
Qed.

Lemma extract_low_ext_low : ltac2:(tb__ "0|2|
SbSaSaS66Q40M0A1SbfR3R2A2SbfR3G0A2S0S66R5A1S69G0Q0M1R5S2aR6R4R3A3A4S69G0G1R5R3A4A3F_;F_;Fv;Fw';Fw;Fs';").
Proof using .
  intros s' w w' v Hw Hw'. apply bv_eq. rewrite !bv_extract_unsigned. change (Z.of_N 0) with 0. rewrite !Z.shiftr_0_r.
  unfold ext_low. destruct s'.
  - unfold sext. rewrite bv_sign_extend_unsigned.
    unfold bv_signed, bv_swrap. rewrite bv_extract_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
    unfold bv_half_modulus. unfold bv_wrap, bv_modulus.
    set (x := bv_unsigned v). set (M := 2 ^ Z.of_N w'). set (h := M / 2).
    rewrite (mod_mod_pow2 _ (Z.of_N w) (Z.of_N 64)) by lia.
    assert (HM : 0 < M) by (unfold M; apply Z.pow_pos_nonneg; lia).
    pose proof (Z.div_mod (x mod M + h) M ltac:(lia)) as E.
    set (q := (x mod M + h) / M) in E.
    replace ((x mod M + h) mod M - h) with (x mod M + (- q) * M) by lia.
    subst M. rewrite (mod_add_mul_pow2 (x mod 2 ^ Z.of_N w') (- q) (Z.of_N w) (Z.of_N w')) by lia.
    apply mod_mod_pow2. lia.
  - unfold zext. rewrite bv_zero_extend_unsigned'. rewrite bv_extract_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
    unfold bv_wrap, bv_modulus.
    rewrite (mod_mod_pow2 _ (Z.of_N w) (Z.of_N 64)) by lia. apply mod_mod_pow2. lia.
Qed.

Lemma ext_low_nested : ltac2:(tb__ "0|2|
SbSbSaSaS66Q40M0A1M1SbfR3R2A2SbfR3G0A2S0G1S2aR7R5S2aR6R4R3A3A3S2aR7R5R3A3A3F_;F_;Fv;Fw';Fw;Fs';Fsgn;").
Proof using . intros. unfold ext_low at 1 3. rewrite extract_low_ext_low by assumption. reflexivity. Qed.

Lemma strip_ext_sound : ltac2:(tb__ "0|0|
S1cSbSaS1aS0S66Q40A1S2aR3R2S22R4SaaR2R1A2A2A3S2aR3R2S22R4R1A2A3A3Fx;Fw;Fsgn;Frho;").
Proof using .
  intros rho sgn w x. induction x; cbn [strip_ext]; try reflexivity.
  destruct ((w <=? w0)%N && (w0 <=? 64)%N)%bool eqn:E; [|reflexivity].
  apply andb_prop in E as [E1 E2]. apply N.leb_le in E1. apply N.leb_le in E2.
  rewrite IHx. cbn [eval]. symmetry. apply ext_low_nested; assumption.
Qed.

Lemma strip_ext_below : ltac2:(tb__ "0|0|
S9SaS1aS0SbS20R3R1A2SdA3S0SbS20R4SaaR3R2A2A2SdA3F_;Fx;Fw;Fn;").
Proof using .
  intros n w x. induction x; cbn [strip_ext]; intros H; try exact H.
  destruct (_ && _)%bool; [apply IHx; cbn in H; exact H | exact H].
Qed.

Lemma extsv_sound : ltac2:(tb__ "0|0|
S1cSfS12SbSaA2A1S1aS0S66Q40A1S22R3S9fR2R1A2A2S5fR2S22R3R1A2A2A3Fx;Fsx;Frho;").
Proof using .
  intros rho [[sgn w]|] x; cbn [extsv extv]; [|reflexivity].
  rewrite mk_ext_sound. apply strip_ext_sound.
Qed.

Lemma extsv_below : ltac2:(tb__ "0|0|
S9SfS12SbSaA2A1S1aS0SbS20R3R1A2SdA3S0SbS20R4S9fR3R2A2A2SdA3F_;Fx;Fsx;Fn;").
Proof using .
  intros n [[sgn w]|] x H; cbn [extsv]; [|exact H]. apply mk_ext_below. apply strip_ext_below. exact H.
Qed.

Lemma narrow_sound : ltac2:(tb__ "0|0|
S1cScS21A1S8S1aS89S21S32R4A1R3A3S6dZ0R3A2S0S66Q40A1S22R6Sa5R5R4R3A3A2S2aS14SbeQ8S73R4A1A2S22R6R3A2A3A3F_;F_;Fv;Fk;Ffacts;Frho;").
Proof using .
  intros rho facts k v Hf Hk. unfold narrow.
  destruct (itv facts v) as [l h] eqn:Hi.
  destruct ((l <=? h) && (h <? 2 ^ (8 * k)))%bool eqn:E; [|apply mk_ext_sound].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  pose proof (itv_sound rho facts v Hf) as Hin. rewrite Hi in Hin. unfold in_itv in Hin. cbn [fst snd] in Hin.
  symmetry. unfold ext_low, zext. apply bv_eq. rewrite bv_zero_extend_unsigned', bv_extract_unsigned.
  change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus.
  replace (Z.of_N (8 * Z.to_N k)) with (8 * k) by lia. pose proof (urange (eval rho v)).
  rewrite (Z.mod_small (bv_unsigned (eval rho v))) by lia. apply Z.mod_small. change (2 ^ Z.of_N 64) with (2 ^ 64). lia.
Qed.

Lemma narrow_below : ltac2:(tb__ "0|0|
S9ScS21A1S8S1aS0SbS20R4R1A2SdA3S0SbS20R5Sa5R4R3R2A3A2SdA3F_;Fv;Fk;Ffacts;Fn;").
Proof using .
  intros n facts k v H. unfold narrow. destruct (itv facts v) as [l h].
  destruct (_ && _)%bool; [exact H | apply mk_ext_below; exact H].
Qed.

Lemma sp_rel_holds : ltac2:(tb__ "0|1|
S1cSbS1aS1aS65R3S68Q40M0S22R4R2A2A2S68G0S22R4R1A2A2A3S32R5Sa9R4R3R2A3A2F_;Fb;Fa;Fs;Frho;").
Proof using . intros rho [|] a b H; cbn in *; exact H. Qed.

Lemma sp_rel_below : ltac2:(tb__ "0|0|
S9SbS1aS1aS0SbS20R4R2A2SdA3S0SbS20R5R2A2SdA3S0SbS4bR6Sa9R5R4R3A3A2SdA3F_;F_;Fb;Fa;Fs;Fn;").
Proof using . intros n [|] a b Ha Hb; cbn; rewrite Ha, Hb; reflexivity. Qed.

Lemma tf_inst_sound : ltac2:(tb__ "0|1|
S1cScS1aA1ScS66Q40A1M0A1S2cSeS87R1S11G0R3A2A2S0G0S22R6S8aS1aR2R5S3eZ0A1A4A2S46R4R2A2A3F_;Fj;SeS88S11G0R4A2R1A2S0SbSabR2R4A2S14A3F_;Fj;S50R6R4R3A3S89S21S32R7A1S9bR6R4A2A3F_;F_;F_;Ft;Fvals;Fxs;Frho;").
Proof using .
  intros rho xs vals t Hxs Hm Ht.
  assert (X : forall j, tf_mentions j t = true -> eval rho (nth j xs (SLit 0)) = fldv vals j).
  { intros j Hj. apply Hxs. destruct (Nat.lt_ge_cases j (length vals)) as [H|H]; [exact H|].
    rewrite (Hm j H) in Hj. discriminate. }
  destruct t as [s i sx e|s i sx e|s i j e]; cbn [tf_inst]; cbn in Ht.
  - constructor; [|constructor]. apply sp_rel_holds. rewrite extsv_sound, (X i) by (cbn; apply Nat.eqb_refl). exact Ht.
  - constructor; [|constructor]. apply sp_rel_holds. rewrite extsv_sound, (X i) by (cbn; apply Nat.eqb_refl). exact Ht.
  - pose proof (X i ltac:(cbn; rewrite Nat.eqb_refl; reflexivity)) as Xi.
    pose proof (X j ltac:(cbn; rewrite Nat.eqb_refl; apply Bool.orb_true_r)) as Xj.
    pose proof (urange (eval rho e)) as He. pose proof (urange (fldv vals i)) as Hi. pose proof (urange (fldv vals j)) as Hj.
    assert (Hsum : bv_unsigned (fldv vals i) + bv_unsigned (fldv vals j) <= bv_unsigned (eval rho e)).
    { destruct s; cbn in Ht; lia. }
    assert (Hadd : bv_unsigned (eval rho (SAlu ALU_ADD (nth i xs (SLit 0)) (nth j xs (SLit 0)))) = bv_unsigned (fldv vals i) + bv_unsigned (fldv vals j)).
    { cbn [eval]. rewrite Xi, Xj. unfold alu64, alu. rewrite bv_add_unsigned. unfold bv_wrap. rewrite two64. apply Z.mod_small. lia. }
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + apply sp_rel_holds. rewrite Hadd. exact Ht.
    + cbn [holds]. rewrite Hadd, Xi. lia.
    + cbn. rewrite Xi. lia.
    + cbn. rewrite Xj. lia.
Qed.

Lemma tf_inst_below : ltac2:(tb__ "0|0|
S9ScS1aA1S2cS0SbSc3S1aS20R3A1R2A3SdA3S0SbS4fR4R2A2SdA3S0SbSc3S21S4bR5A1S9bR4R3A2A3SdA3F_;F_;Ft;Fxs;Fn;").
Proof using .
  intros n xs t Hxs Ht.
  assert (N : forall j, sv_below n (nth j xs (SLit 0)) = true).
  { intros j. destruct (nth_in_or_default j xs (SLit 0)) as [H| ->]; [|reflexivity].
    exact (proj1 (forallb_forall _ _) Hxs _ H). }
  unfold tf_below in Ht. destruct t; cbn [tf_inst tf_expr forallb] in *.
  - rewrite sp_rel_below; [reflexivity | apply extsv_below; apply N | exact Ht].
  - rewrite sp_rel_below; [reflexivity | exact Ht | apply extsv_below; apply N].
  - rewrite sp_rel_below; [| cbn; rewrite !N; reflexivity | exact Ht]. cbn. rewrite !N, Ht. reflexivity.
Qed.

Lemma tmpl_inst_sound : ltac2:(tb__ "0|1|
S1cScS1aA1ScS66Q40A1M0A1ScS2cA1SeS87R1S11G0R3A2A2S0G0S22R6S8aS1aR2R5S3eZ0A1A4A2S46R4R2A2A3F_;Fj;S2cSeSc2S2cR2R4A3S88S11G0R6A2R2A2S0SbSabR3R4A2S14A3F_;F_;Fj;Ft;S89S2cS50R6R4A2R3A3S89S21S32R7A1S9cR6R4A2A3F_;F_;F_;Ftmpl;Fvals;Fxs;Frho;").
Proof using .
  intros rho xs vals tmpl Hxs Hm Ht. induction tmpl as [|t rest IH]; cbn; [constructor|].
  inversion Ht; subst. apply Forall_app. split.
  - eapply tf_inst_sound; eauto. intros j Hj. apply (Hm t j); [left; reflexivity | exact Hj].
  - apply IH; [|assumption]. intros t' j Hin Hj. apply (Hm t' j); [right; exact Hin | exact Hj].
Qed.

Lemma tmpl_inst_below : ltac2:(tb__ "0|0|
S9ScS1aA1ScS2cA1S0SbSc3S1aS20R3A1R2A3SdA3S0SbSc3S2cS4fR4A1R2A3SdA3S0SbSc3S21S4bR5A1S9cR4R3A2A3SdA3F_;F_;Ftmpl;Fxs;Fn;").
Proof using .
  intros n xs tmpl Hxs Ht. induction tmpl as [|t rest IH]; cbn; [reflexivity|].
  cbn in Ht. apply andb_prop in Ht as [H1 H2]. rewrite forallb_app, (tf_inst_below n xs t Hxs H1), (IH H2). reflexivity.
Qed.

Lemma obj_holds_add_cells : ltac2:(tb__ "0|0|
S1cS7bS1bScS1dA1S23Vsegs;R4R3R2A4S89S1dS55R5S26R3A1S29R5R3A2S2bR5R3A2R4A5R2A3S23Vsegs;R6R5S62S26R4A1S52R4A1S51R4A1S15S1dR3S2fR4A1A3S41R4A1A5A4F_;F_;Fcs;Fo;Fms;Frho;").
Proof using .
  intros rho ms o cs (Hb & Hw & Hc & Hd & Hdl) Hcs.
  unfold obj_holds, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  split; [exact Hb|]. split; [exact Hw|]. split; [apply Forall_app; split; assumption|].
  split; [|exact Hdl].
  intros off' Hoff' Hcov. apply Hd; [exact Hoff'|]. intros Hc'. apply Hcov.
  unfold covered in *. apply Exists_app. right. exact Hc'.
Qed.

Lemma arr_cells_wf : ltac2:(tb__ "0|2|
S9S1aScS12S8S8A2M0A1S9S0SbS20R4R3A2SdA3S88Sd3Sc9R2A1S11G0R3A2A2Sc9R5A1A2S89G0G0S1S6dZ0S16S8S8R1A3M1A2S6bG1Z8A2A2Lf;R4A3S0SbSc3S1dS45R7A1Sb0R6R5R4A3A3SdA3F_;F_;F_;Fx0;Fflds;Foff0;Fn;").
Proof using .
  intros n off0 flds. induction flds as [|f rest IH]; intros x0 Hoff Hle Hw; cbn [arr_cells forallb]; [reflexivity|].
  inversion Hw as [|f' rest' Hf Hrest]; subst. cbn in Hle.
  apply andb_true_intro. split.
  - unfold cell_wf. cbn [c_off c_width c_val].
    rewrite (proj2 (Z.ltb_lt 0 (snd f))) by lia. rewrite (proj2 (Z.leb_le (snd f) 8)) by lia.
    rewrite (mk_addk_below _ _ _ Hoff). cbn. apply Pos.ltb_lt. lia.
  - apply IH; [exact Hoff | lia | exact Hrest].
Qed.

Lemma tf_inst_sound_total : ltac2:(tb__ "0|1|
S1cScS1aA1ScS66Q40A1M0A1S2cS0SeS11S1aR3A2S11G0R2A2A3SeS87R1S11G0R4A2A2S0G0S22R7S8aS1aR2R6S3eZ0A1A4A2S46R5R2A2A3F_;Fj;S50R6R4R3A3S89S21S32R7A1S9bR6R4A2A3F_;F_;F_;Ft;Fvals;Fxs;Frho;").
Proof using .
  intros rho xs vals t Hlen Hxs Ht.
  assert (X : forall j, eval rho (nth j xs (SLit 0)) = fldv vals j).
  { intros j. destruct (Nat.lt_ge_cases j (length vals)) as [H|H]; [apply Hxs; exact H|].
    rewrite nth_overflow by lia. unfold fldv. rewrite nth_overflow by lia. reflexivity. }
  destruct t as [s i sx e|s i sx e|s i j e]; cbn [tf_inst]; cbn in Ht.
  - constructor; [|constructor]. apply sp_rel_holds. rewrite extsv_sound, (X i). exact Ht.
  - constructor; [|constructor]. apply sp_rel_holds. rewrite extsv_sound, (X i). exact Ht.
  - pose proof (X i) as Xi. pose proof (X j) as Xj.
    pose proof (urange (eval rho e)) as He. pose proof (urange (fldv vals i)) as Hi. pose proof (urange (fldv vals j)) as Hj.
    assert (Hsum : bv_unsigned (fldv vals i) + bv_unsigned (fldv vals j) <= bv_unsigned (eval rho e)).
    { destruct s; cbn in Ht; lia. }
    assert (Hadd : bv_unsigned (eval rho (SAlu ALU_ADD (nth i xs (SLit 0)) (nth j xs (SLit 0)))) = bv_unsigned (fldv vals i) + bv_unsigned (fldv vals j)).
    { cbn [eval]. rewrite Xi, Xj. unfold alu64, alu. rewrite bv_add_unsigned. unfold bv_wrap. rewrite two64. apply Z.mod_small. lia. }
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + apply sp_rel_holds. rewrite Hadd. exact Ht.
    + cbn [holds]. rewrite Hadd, Xi. lia.
    + cbn. rewrite Xi. lia.
    + cbn. rewrite Xj. lia.
Qed.

Lemma tmpl_inst_sound_total : ltac2:(tb__ "0|1|
S1cScS1aA1ScS66Q40A1M0A1ScS2cA1S0SeS11S1aR3A2S11G0R2A2A3SeS87R1S11G0R4A2A2S0G0S22R7S8aS1aR2R6S3eZ0A1A4A2S46R5R2A2A3F_;Fj;S89S2cS50R6R4A2R3A3S89S21S32R7A1S9cR6R4A2A3F_;F_;F_;Ftmpl;Fvals;Fxs;Frho;").
Proof using .
  intros rho xs vals tmpl Hlen Hxs Ht. induction tmpl as [|t rest IH]; cbn; [constructor|].
  inversion Ht; subst. apply Forall_app. split; [eapply tf_inst_sound_total; eauto | apply IH; assumption].
Qed.

Lemma le_word_of_enc : ltac2:(tb__ "0|2|
SeS66Q40M0A1M1S88R2U8A2S6dS68G0R2A2S6eZ2S6fZ8S70R3A1A2A2A2S0G1Sc6S35R4R3A2A1R3A3F_;F_;Fv;Fk;").
Proof using .
  intros k v Hk Hv.
  pose proof (ext_of_enc false k v Hk) as E.
  assert (Z8 : forall x : word, bv_unsigned x < 2 ^ (8 * Z.of_nat k) -> ext_low false (8 * N.of_nat k)%N x = x).
  { intros x Hx. unfold ext_low, zext. apply bv_eq. rewrite bv_zero_extend_unsigned', bv_extract_unsigned.
    change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus.
    replace (Z.of_N (8 * N.of_nat k)) with (8 * Z.of_nat k) by lia. pose proof (urange x).
    rewrite (Z.mod_small (bv_unsigned x)) by lia. apply Z.mod_small. change (2 ^ Z.of_N 64) with (2 ^ 64). lia. }
  rewrite (Z8 v Hv) in E. rewrite <- E at 2. symmetry. apply Z8.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_bound (enc_bytes k v)) as B. unfold enc_bytes in B |- *.
  rewrite Z_to_le_bytes_length in B. pose proof (bytes_le_to_Z_nonneg (Z_to_le_bytes k (bv_unsigned v))) as B0.
  unfold bv_wrap. rewrite two64. rewrite Z.mod_small; [lia|]. split; [lia|].
  eapply Z.lt_le_trans; [exact (proj2 B)|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma smatch_set_objs_facts_next : ltac2:(tb__ "0|1|
S1cS1fS12ScS85A1M0S82A2ScS1bA1ScS21A1S9SbS27Vsegs;R7R6R5A4S47Vsegs;R8R5S84S16G0S82R6A3A1A4S89S21S32R9A1R5A3S0SbS3dS36S2eR9A1S3bR9A1S39R9A1S38R9A1S3cR9A1R7S15S21R6S33R9A1A3R5R4A9A1SdA3S27Vsegs;RbS36S2eRaA1S3bRaA1S39RaA1S38RaA1S3cRaA1R8S15S21R7S33RaA1A3R6R5A9R9A4F_;F_;F_;F_;Flm;Fnx;FF;Fobjs;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] objs F nx lm Hsm Hmm HF Hwf.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  unfold smatch; cbn [fst snd cfg_ms cfg_model ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts] in *.
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [exact Hmm|]. apply Forall_app. split; assumption.
Qed.

Lemma arr_offset_eq : ltac2:(tb__ "0|3|
S1cS1aS1aS8S1aS8S8S1aS8S0S8SdcR9SbaSd8R8R7A3A2S72S6cS6fR6SdcR9R5A2A2R4A2S6eZ2M0Z40A2A2A3S6dZ0M1R7A2M2S6bG1R6A2S0S8R6SdcRcR8A2A3S6bS1eRdRbA2S1eRdRcA2A2S6bS6cS1eReRdA2R6A2S1eReR7A2A2G2S6dS74S1eR10R9A2S1eR10ReA2A2S6eG0Z3fA2A2S6bS6cS6cS6fReRbA2RcA2R9A2S74S1eR11RaA2S1eR11RfA2A2A2S0S8S1eR12R11A2S6cS6cS1eR12R10A2S6fRfRcA2A2RdA2A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fk;Fhi;FK;Fc;Fidx;Fesz;Flo;Foff;Frho;").
Proof using .
  intros rho off lo esz idx c K hi k Hd Hesz Hc HK Hlo Hhi Hk Hsz Hfit. subst K.
  pose proof (U_range rho idx) as Hi.
  assert (E : (soff rho off - soff rho lo) mod 2 ^ 64 = (esz * U rho idx + c) mod 2 ^ 64).
  { rewrite <- Hd. unfold U at 1. rewrite mk_alu_sound, sub_val.
    change (bv_unsigned (eval rho off)) with (U rho off). change (bv_unsigned (eval rho lo)) with (U rho lo).
    rewrite <- (soff_mod rho off), <- (soff_mod rho lo).
    rewrite <- Zminus_mod. reflexivity. }
  rewrite (Z.mod_small (soff rho off - soff rho lo)) in E by lia.
  assert (Hnn : 0 <= esz * U rho idx) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite Z.mod_small in E by lia. lia.
Qed.

Lemma load_arr_sound : ltac2:(tb__ "0|1|
S1cS1fScS85A1M0S7bS86SeS1bS1aS8SbS1aS1fS8S1aScS12S8S8A2A1ScS2cA1S27Vsegs;R10RfS13G0S82ReS83RdRcA2A4A4S2S0S8R9Z1A3S2S0S8R9Z2A3S2S0S8R9Z4A3S0S8R9Z8A3A2A2A2S0SfS1bA1Sc4S1bS3aR11A1RdA3S10S1bRcA2A3S23Vsegs;R13R10RdA4S0SbS25S28R13A1ReA2SdA3S0SbS20S28R14A1ReA2SdA3S6bS29R16R10A2S1eR16RfA2A2S6bS6cS1eR17R10A2RfA2S2bR17R11A2A2S0S42S41R12A1S5aRcRbRaR9A4A3S0S8eSb7R18R14R13R12R11R10SbeQ8S73R11A1A2RdRcRbRaAbS8dRfReA2A3SceR19R1aR17S2dR1aS26R14A1S1eR1aR13A2A3R12R11R10RfR18R16AaF_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftmpl;Fflds;Fcnt;Fesz;FS';Fv;Fsgn;Fk;Foff;Fo;Fn;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md n o off k sgn v S' esz cnt flds tmpl Hsm Hk Hnth Hoh Howf Hoff Hlo Hhi Hd Hla.
  destruct (k_cases k Hk) as (Hk0 & Hk8 & Hkn & Hw & Hwpos).
  pose proof (smatch_swf _ _ _ _ Hsm) as Hwf.
  pose proof (smatch_facts _ _ _ _ Hsm) as Hfacts.
  assert (LF : forall v' S'', load_fresh S n o off k sgn (8 * Z.to_N k)%N = LROk v' S'' ->
               load_post S rho ms (oaddr rho (ob_base o) (soff rho off)) k sgn v' S'' tr md).
  { intros v' S'' H. exact (load_fresh_sound rho S tr ms md n o off k sgn v' S'' Hsm Hk Hnth Hoh Howf Hoff Hlo Hhi H). }
  unfold load_arr in Hla.
  destruct (lin_decomp (ss_facts S) (mk_alu ALU_SUB off (ob_lo o)) esz) as [[idx c]|] eqn:Hdec; [|exact (LF _ _ Hla)].
  destruct (fld_index flds c k) as [i|] eqn:Hfi; [|exact (LF _ _ Hla)].
  destruct (uleq (ss_facts S) idx 1 cnt) eqn:Hul; [|exact (LF _ _ Hla)].
  apply lrok_inj in Hla as [<- <-].

  destruct (lin_decomp_sound rho (ss_facts S) _ esz idx c Hfacts Hdec) as (Hesz & Hc & HU).
  pose proof (uleq_sound rho (ss_facts S) idx 1 cnt Hfacts Hul) as Hidx. unfold U in Hidx.
  pose proof (fld_index_sound flds c k i Hfi) as Hfld.
  pose proof Hoh as (HB & HW & HC & HD & HDL). rewrite Hd in HDL. cbn [dflt_inv] in HDL.
  destruct HDL as (_ & Hflds & Hfit & Helems).
  pose proof (proj1 (Forall_forall _ _) Hflds _ (nth_error_In _ _ Hfld)) as Hfok. unfold fld_ok in Hfok. cbn [fst snd] in Hfok. destruct Hfok as (Hc0 & Hck & _).
  destruct HB as (HB1 & HB2 & HB3 & HB4).
  set (K := bv_unsigned (eval rho idx)) in *.
  set (b := bv_unsigned (eval rho (ob_base o))) in *.
  set (lo := obj_lo_of rho o) in *. set (hi := obj_hi_of rho o) in *.
  assert (Hmul : esz * K + esz <= esz * bv_unsigned (eval rho cnt)).
  { rewrite <- Z.mul_succ_r. apply Z.mul_le_mono_nonneg_l; [lia|]. unfold K. lia. }
  assert (HKnn : 0 <= esz * K) by (apply Z.mul_nonneg_nonneg; [lia | unfold K; apply (proj1 (urange _))]).
  assert (HoffEq : soff rho off = lo + esz * K + c).
  { unfold lo, hi, obj_lo_of, obj_hi_of in *.
    eapply (arr_offset_eq rho off (ob_lo o) esz idx c K (ob_hi o) k HU); [lia | lia | reflexivity | exact Hlo | exact Hhi | lia | lia | lia]. }
  destruct (Helems K ltac:(unfold K; pose proof (urange (eval rho idx)); lia)) as (vals & Hvlen & Hvrd & Hvt).
  set (x0 := ss_next S) in *. set (m := length flds) in *.
  set (rho' := rho_exts rho x0 vals).
  pose proof (rho_exts_agree rho x0 vals) as Hag. fold rho' in Hag.
  assert (Hxs : forall j, (j < length vals)%nat -> eval rho' (nth j (fld_vars x0 m) (SLit 0)) = fldv vals j).
  { intros j Hj. rewrite fld_vars_nth by (unfold m; lia). cbn [eval]. unfold rho'. apply rho_exts_at. exact Hj. }
  destruct (Hvrd i (c, k) Hfld) as [Hrdi Hvi]. cbn [fst snd] in Hrdi, Hvi.
  exists (enc_bytes (Z.to_nat k) (fldv vals i)), rho'.
  split.
  { unfold oaddr. rewrite HoffEq. unfold b in Hrdi.
    replace (bv_unsigned (eval rho (ob_base o)) + (lo + esz * K + c)) with (bv_unsigned (eval rho (ob_base o)) + lo + esz * K + c) by lia.
    exact Hrdi. }
  split; [exact Hag|].
  cbn [ss_next ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_facts ss_objs ss_lenient].
  split; [lia|].
  split.
  {
    pose proof (smatch_agree segs rho rho' S _ Hag Hsm) as Hsm1.
    apply (smatch_set_objs_facts_next rho' S (tr, mkCfg ms md)).
    - exact Hsm1.
    - cbn [snd cfg_ms]. eapply mem_match_set.
      + destruct Hsm1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmem1 & _). exact Hmem1.
      + exact Hnth.
      + reflexivity.
      + pose proof (obj_holds_agree segs x0 rho rho' ms o Hag Howf Hoh) as Hoh'.
        apply (obj_holds_add_cells rho' ms o). exact Hoh'.

        destruct (obj_wf_parts _ _ Howf) as (Hb' & Hlo' & Hhi' & _).
        assert (Elo : obj_lo_of rho' o = lo) by (unfold lo, obj_lo_of; eapply soff_agree; eauto).
        assert (Ehi : obj_hi_of rho' o = hi) by (unfold hi, obj_hi_of; eapply soff_agree; eauto).
        rewrite Elo, Ehi.
        assert (CELLS : forall fl j x, (forall jj f, nth_error fl jj = Some f -> nth_error flds (j + jj)%nat = Some f) ->
                  x = Pos.of_nat (Pos.to_nat x0 + j) -> (j + length fl <= m)%nat ->
                  Forall (cell_holds rho' (ob_base o) lo hi ms) (arr_cells (mk_addk off (- c)) fl x)).
        { induction fl as [|f rest IH]; intros j x Hsub Hx Hjm; cbn [arr_cells]; [constructor|].
          pose proof (Hsub 0%nat f eq_refl) as Hf. rewrite Nat.add_0_r in Hf.
          pose proof (proj1 (Forall_forall _ _) Hflds _ (nth_error_In _ _ Hf)) as Fok. unfold fld_ok in Fok. destruct Fok as (F0 & F1 & F2).
          assert (Hjv : (j < length vals)%nat) by (rewrite Hvlen; eapply nth_error_length_lt; exact Hf).
          destruct (Hvrd j f Hf) as [Rj Vj].
          constructor.
          - unfold cell_holds. cbn [c_off c_width c_val].
            assert (Hso : soff rho' (mk_addk (mk_addk off (- c)) (fst f)) = lo + esz * K + fst f).
            { rewrite (soff_agree x0 rho rho'); [| exact Hag | apply mk_addk_below; apply mk_addk_below; exact Hoff].
              assert (R1 : soff rho (mk_addk off (- c)) = lo + esz * K).
              { rewrite soff_mk_addk_M; [lia|]. pose proof (soff_range rho off). unfold lo, hi, obj_lo_of, obj_hi_of in *.
                pose proof (soff_range rho (ob_lo o)). lia. }
              rewrite soff_mk_addk_M; [lia|]. rewrite R1. pose proof (soff_range rho (ob_lo o)). pose proof (soff_range rho (ob_hi o)).
              unfold lo, hi, obj_lo_of, obj_hi_of in *. lia. }
            rewrite Hso. split; [lia|]. split.
            + unfold lo, hi, obj_lo_of, obj_hi_of in *. lia.
            + subst x. cbn [eval]. unfold rho'. rewrite rho_exts_at by exact Hjv.
              unfold oaddr. rewrite <- (eval_agree x0 rho (rho_exts rho x0 vals) _ Hag Hb'). fold b.
              replace (b + (lo + esz * K + fst f)) with (b + lo + esz * K + fst f) by lia. exact Rj.
          - apply (IH (Datatypes.S j)); [| subst x; rewrite <- Nat2Pos.inj_succ by lia; f_equal; lia | cbn in Hjm; lia].
            intros jj f' Hjj. replace (Datatypes.S j + jj)%nat with (j + Datatypes.S jj)%nat by lia. apply Hsub. exact Hjj. }
        apply (CELLS flds 0%nat x0); [intros jj f H; exact H | rewrite Nat.add_0_r, Pos2Nat.id; reflexivity | unfold m; lia].
    -
      eapply tmpl_inst_sound_total; [rewrite fld_vars_length; unfold m; symmetry; exact Hvlen | exact Hxs |].
      pose proof (obj_wf_dflt _ _ Howf) as Dw0. rewrite Hd in Dw0. cbn in Dw0. apply andb_prop in Dw0 as [_ Dw0].
      apply Forall_forall. intros t Hin.
      apply (proj1 (tf_holds_agree x0 rho rho' vals t Hag (proj1 (forallb_forall _ _) Dw0 t Hin))).
      exact (proj1 (Forall_forall _ _) Hvt t Hin).
    -
      pose proof (swf_mono_next S (Pos.of_nat (Pos.to_nat x0 + m)) ltac:(unfold x0; lia) Hwf) as W.
      unfold swf in W |- *. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next] in W |- *.
      repeat (apply andb_prop in W; destruct W as [W ?]).
      repeat (apply andb_true_intro; split); try assumption.
      + apply forallb_list_set; [assumption|].
        pose proof (obj_wf_mono x0 (Pos.of_nat (Pos.to_nat x0 + m)) o ltac:(lia) Howf) as Howf'.
        destruct (obj_wf_parts _ _ Howf') as (Qb & Qlo & Qhi & Qc). pose proof (obj_wf_dflt _ _ Howf') as Qd.
        unfold obj_wf. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. rewrite Qb, Qlo, Qhi, Qd, forallb_app, Qc. cbn [andb].
        rewrite !Bool.andb_true_r. apply arr_cells_wf.
        * apply mk_addk_below. eapply sv_below_mono; [|exact Hoff]. lia.
        * unfold m. lia.
        * apply Forall_forall. intros f Hf. pose proof (proj1 (Forall_forall _ _) Hflds f Hf) as [_ [_ F]]. lia.
      + rewrite forallb_app. apply andb_true_intro. split; [|assumption].
        apply tmpl_inst_below; [apply fld_vars_below|].
        pose proof (obj_wf_dflt _ _ Howf) as Dw. rewrite Hd in Dw. cbn in Dw. apply andb_prop in Dw as [_ Dw].
        apply forallb_forall. intros t Ht. eapply tf_below_mono; [| exact (proj1 (forallb_forall _ _) Dw t Ht)]. lia. }
  split.
  { rewrite mk_ext_sound. cbn [eval]. unfold rho'. rewrite rho_exts_at by (rewrite Hvlen; eapply nth_error_length_lt; exact Hfld).
    rewrite Hw. rewrite le_word_of_enc; [reflexivity | lia | rewrite Z2Nat.id by lia; exact Hvi]. }
  split.
  { apply mk_ext_below. cbn. apply Pos.ltb_lt. pose proof (nth_error_length_lt _ _ _ Hfld). unfold m. lia. }
  repeat split; try reflexivity.
  cbn. exists (tmpl_inst (fld_vars x0 m) tmpl). reflexivity.
Qed.

Lemma load_dflt_sound : ltac2:(tb__ "0|1|
S1cS1fScS85A1M0S7bS86SeS1bS1aS8SbS1aS1fS27Vsegs;RcRbS13G0S82RaS83R9R8A2A4A4S2S0S8R5Z1A3S2S0S8R5Z2A3S2S0S8R5Z4A3S0S8R5Z8A3A2A2A2S0SfS1bA1Sc4S1bS3aRdA1R9A3S10S1bR8A2A3S23Vsegs;RfRcR9A4S0SbS25S28RfA1RaA2SdA3S0SbS20S28R10A1RaA2SdA3S6bS29R12RcA2S1eR12RbA2A2S6bS6cS1eR13RcA2RbA2S2bR13RdA2A2S0S8eSb8R13RfReRdRcRbSbeQ8S73RcA1A2A7S8dRaR9A2A3SceR14R15R12S2dR15S26RfA1S1eR15ReA2A3RdRcRbRaR13R11AaF_;F_;F_;F_;F_;F_;F_;F_;F_;FS';Fv;Fsgn;Fk;Foff;Fo;Fn;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md n o off k sgn v S' Hsm Hk Hnth Hoh Howf Hoff Hlo Hhi H.
  unfold load_dflt in H. destruct (ob_dflt o) eqn:Hd;
    try exact (load_fresh_sound rho S tr ms md n o off k sgn v S' Hsm Hk Hnth Hoh Howf Hoff Hlo Hhi H).
  eapply load_arr_sound; eauto.
Qed.

Lemma fresh_value_sound : ltac2:(tb__ "0|3|
S1cS1fScS85A1M0S7bS86S66Q40A1S8SbScS66Q8M1A1A1M2S27Vsegs;R9R8S13G0S82R7S83R6R5A2A4A4S2S0S8R4Z1A3S2S0S8R4Z2A3S2S0S8R4Z4A3S0S8R4Z8A3A2A2A2S0SfG2A1S24R8R6S71R5A1A3S10G2R3A2A3SceRbRcR9R7R6R5Sa4R5SbeG1S73R6A1A2S4cS28RbA1A1A3S16S1aS1fSa0RbA1A3RaR8AaF_;F_;F_;Fbs;Fsgn;Fk;Fa;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md a k sgn bs Hsm Hk Hrd.
  pose proof (smatch_swf _ _ _ _ Hsm) as Hwf.
  set (x := le_bytes_to_word bs). set (rho' := rho_fresh rho (ss_next S) x).
  pose proof (rho_fresh_agree rho (ss_next S) x) as Hag. pose proof (rho_fresh_at rho (ss_next S) x) as Hx.
  fold rho' in Hag, Hx.
  exists bs, rho'. split; [exact Hrd|]. split; [exact Hag|].
  unfold fresh. cbn [snd ss_next ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_facts ss_objs].
  split; [lia|]. split.
  { pose proof (smatch_agree segs rho rho' S _ Hag Hsm) as Hsm1.
    apply (smatch_set_objs_next rho' S (tr, mkCfg ms md) (ss_objs S) (Pos.succ (ss_next S)) (ss_lenient S) Hsm1).
    - destruct Hsm1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmem1 & _). exact Hmem1.
    - apply (swf_mono_next S). lia. exact Hwf. }
  split.
  { rewrite mk_ext_sound. cbn [eval]. rewrite Hx. reflexivity. }
  split.
  { apply mk_ext_below. cbn. apply Pos.ltb_lt. lia. }
  repeat split; try reflexivity. exists []. reflexivity.
Qed.

Lemma existsb_false_in : forall {A} (f : A -> bool) l x, existsb f l = false -> In x l -> f x = false.
Proof using .
  intros A f l x H Hin. destruct (f x) eqn:E; [|reflexivity].
  assert (existsb f l = true) by (apply existsb_exists; exists x; auto). congruence.
Qed.

Lemma snorm_nonneg_mod : ltac2:(tb__ "0|0|
S8S6bZ0S91R1A1A2S0S8S91R2A1S72R2S6eZ2Z40A2A2A3F_;Fz;").
Proof using .
  intros z Hz. unfold snorm in *. pose proof (Z.mod_pos_bound z (2 ^ 64) ltac:(lia)).
  destruct (Z.ltb_spec (z mod 2 ^ 64) (2 ^ 63)); lia.
Qed.

Lemma sym_load_sound_gen : ltac2:(tb__ "0|4|
S1cS1fScS85A1M0S7bS86S1aS8SbS1aS1fS27Vsegs;RaR9S13G0S82R8S83R7R6A2A4A4S0SbS20S28RaA1R6A2SdA3S2S0S8R6Z1A3S2S0S8R6Z2A3S2S0S8R6Z4A3S0S8R6Z8A3A2A2A2S0S8eS95Vsegs;RcR8R7R6A5S8dR5R4A2A3S2S1S0SbS43RdA1SdA3S1S0SfScS66Q8M1A1A1M2A1S24RbS22ReR9A2M3S71R8A1A3S17G2A1A3S1S0S1fR5S16S1aS1fSa0RdA1A3A3S0S1aR6Sa4R7SbeG1S73R8A1A2S4cS28RdA1A1A3A3A2A2A2SceRdReRbG3R8R7R6R5RcRaAaA2F_;F_;F_;F_;FS';Fv;Fsgn;Fk;Fae;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md ae k sgn v S' Hsm Hae Hk Hload.
  destruct (k_cases k Hk) as (Hk0 & Hk8 & Hkn & Hw & Hwpos).
  pose proof (smatch_swf _ _ _ _ Hsm) as Hwf.
  pose proof (smatch_facts _ _ _ _ Hsm) as Hfacts.
  assert (Hrom : rom_ok segs ms) by (destruct Hsm as (_ & _ & _ & _ & Hrom & _); exact Hrom).
  assert (Hroc : ro_clear segs ms) by (destruct Hsm as (_ & _ & _ & _ & _ & Hroc & _); exact Hroc).
  unfold sym_load in Hload. lazy zeta in Hload.

  revert Hload.
  destruct (match ae with SLit a => ro_load segs (a mod 2 ^ 64) (Z.to_nat k) | _ => None end) as [z|] eqn:Hro; intros Hload.
  { right. destruct ae as [a| | | | | | |]; try discriminate.
    apply lrok_inj in Hload as [<- <-].
    unfold ro_load in Hro.
    destruct ((0 <=? a mod 2 ^ 64) && (a mod 2 ^ 64 + Z.of_nat (Z.to_nat k) <=? 2 ^ 64) && all_ro segs (a mod 2 ^ 64) (Z.to_nat k))%bool eqn:Hc; [|discriminate].
    apply andb_prop in Hc as [Hc Hall]. apply andb_prop in Hc as [H0 H1]. apply Z.leb_le in H0. apply Z.leb_le in H1.
    destruct (image_bytes segs (a mod 2 ^ 64) (Z.to_nat k)) as [bs|] eqn:Hib; [|discriminate]. inversion Hro; subst z.
    pose proof (ro_read segs ms (a mod 2 ^ 64) (Z.to_nat k) bs Hrom Hroc H0 H1 ltac:(lia) Hall Hib) as R.
    eapply load_post_same; [exact Hsm | | | reflexivity].
    - cbn [eval]. rewrite <- Z_to_bv64_mod. exact R.
    - rewrite mk_ext_sound. reflexivity. }
  clear Hro.

  destruct (find_obj (ss_objs S) (ss_facts S) ae k 0) as [[[n o] off]|] eqn:Hfo.
  2:{
      destruct (ss_lenient S ||| ro_span segs (ss_facts S) ae k) eqn:Hlen; [|discriminate].
      unfold fresh in Hload. apply lrok_inj in Hload as [<- <-].
      destruct (rd_bytes ms (eval rho ae) (Z.to_nat k)) as [bs|] eqn:Hrd.
      - right. exact (fresh_value_sound rho S tr ms md _ k sgn bs Hsm Hk Hrd).
      - apply lazy_orb_prop in Hlen as [Hlen|Hspan].
        + left. unfold fresh. auto.
        + exfalso. destruct (ro_span_read _ rho (ss_facts S) ms ae (Z.to_nat k) Hrom Hroc Hfacts ltac:(lia)
                                         ltac:(rewrite Z2Nat.id by lia; exact Hspan)) as [bs Hbs]. congruence. }
  right.
  destruct (find_obj_sound segs rho S tr ms md ae k n o off Hsm Hk0 Hfo)
    as (Hnth & Hoh & Howf & Hro & Hib & HU & Hea & Hlo & Hhi).
  pose proof (rel_offset_below (ss_next S) (ob_base o) ae off Hae (proj1 (obj_wf_parts _ _ Howf)) Hro) as Hoff.
  rewrite Hea.
  set (A := soff rho off) in *.
  assert (LF : forall v' S'', load_fresh S n o off k sgn (8 * Z.to_N k)%N = LROk v' S'' ->
               load_post S rho ms (oaddr rho (ob_base o) A) k sgn v' S'' tr md).
  { intros v' S'' H. exact (load_fresh_sound rho S tr ms md n o off k sgn v' S'' Hsm Hk Hnth Hoh Howf Hoff Hlo Hhi H). }
  assert (LD : forall v' S'', load_dflt S n o off k sgn (8 * Z.to_N k)%N = LROk v' S'' ->
               load_post S rho ms (oaddr rho (ob_base o) A) k sgn v' S'' tr md).
  { intros v' S'' H. exact (load_dflt_sound rho S tr ms md n o off k sgn v' S'' Hsm Hk Hnth Hoh Howf Hoff Hlo Hhi H). }
  destruct (read_cells (ss_facts S) (ob_cells o) off k CRNone) as [v0|v0 sh| | |] eqn:Hrc.
  -
    apply lrok_inj in Hload as [<- <-].
    destruct (read_cells_exact _ _ _ _ CRNone _ I Hrc) as (c & Hin & Hcv & Hcw & Hcr).
    destruct (obj_wf_cell _ _ _ Howf Hin) as (C1 & C2 & C3 & C4).
    pose proof (cell_rel_lit_sound segs rho (ss_facts S) ms o off k c 0 Hfacts Hoh Hin Hlo Hhi ltac:(lia) ltac:(lia) Hcr) as E.
    fold A in E.
    pose proof (obj_read_cell segs rho ms o c A k Hoh Hin C2 ltac:(lia) ltac:(lia) Hk0) as R.
    rewrite E, Z.add_0_r, Z.sub_diag, Z.mul_0_r, Z.shiftr_0_r, Z_to_bv_bv_unsigned, Hcv in R.
    eapply load_post_same; [exact Hsm | exact R | |].
    + rewrite (mk_ext_f_sound rho) by exact Hfacts. rewrite Hw, ext_of_enc by exact Hkn. reflexivity.
    + apply mk_ext_f_below. rewrite <- Hcv. exact C4.
  -
    apply lrok_inj in Hload as [<- <-].
    destruct (read_cells_inside _ _ _ _ CRNone _ _ I Hrc) as (c & d & Hin & Hcv & Hcr & Hd0 & Hkd & Hsh).
    destruct (obj_wf_cell _ _ _ Howf Hin) as (C1 & C2 & C3 & C4).
    pose proof (cell_rel_lit_sound segs rho (ss_facts S) ms o off k c d Hfacts Hoh Hin Hlo Hhi ltac:(lia) ltac:(lia) Hcr) as E.
    fold A in E.
    pose proof (obj_read_cell segs rho ms o c A k Hoh Hin C2 ltac:(lia) ltac:(lia) Hk0) as R.
    eapply load_post_same; [exact Hsm | exact R | |].
    + rewrite (mk_ext_f_sound rho) by exact Hfacts. rewrite Hw, ext_of_enc by exact Hkn. f_equal.
      apply bv_eq. rewrite mk_alu_sound. change (eval rho (SLit (8 * sh))) with (Z_to_bv 64 (8 * sh)).
      rewrite srl_lit_unsigned by lia. rewrite Z_to_bv_unsigned.
      rewrite Hcv. replace (A - soff rho (c_off c)) with sh by lia. symmetry. apply bv_wrap_small. rewrite two64.
      pose proof (urange (eval rho v0)) as Hu. rewrite Z.shiftr_div_pow2 by lia.
      split; [apply Z.div_pos; lia|].
      apply Z.div_lt_upper_bound; [lia|].
      assert (1 <= 2 ^ (8 * sh)) by (apply Z.pow_le_mono_r with (a:=2) (b:=0); lia). nia.
    + apply mk_ext_f_below. apply mk_alu_below; [rewrite <- Hcv; exact C4 | reflexivity].
  -
    destruct (read_cells_none _ _ _ _ _ Hrc) as [_ Hsk].
    pose proof (skippable_uncovered segs rho (ss_facts S) ms o off k (ss_next S) Hfacts Hoh Howf Hlo Hhi Hk0 Hsk) as Hunc.
    fold A in Hunc.
    destruct (ob_dflt o) eqn:Hd.
    +   exact (LF _ _ Hload).
    +
      apply lrok_inj in Hload as [<- <-].
      pose proof (obj_read_zero segs rho ms o A k Hoh Hd Hlo Hhi Hk0 Hunc) as R.
      eapply load_post_same; [exact Hsm | exact R | | reflexivity].
      cbn [eval]. rewrite Hw, ext_of_enc by exact Hkn. rewrite <- Hw. symmetry. apply ext_low_zero. exact Hwpos.
    +
      revert Hload.
      destruct (ob_base o) as [zb| | | | | | |] eqn:Hbo; try (intros Hload; exact (LF _ _ Hload)).
      destruct zb; try (intros Hload; exact (LF _ _ Hload)).
      destruct off as [zo| | | | | | |]; try (intros Hload; exact (LF _ _ Hload)).
      destruct (image_load segs (zo mod 2 ^ 64) (Z.to_nat k)) as [z|] eqn:Hil; [|discriminate].
      intros Hload. apply lrok_inj in Hload as [<- <-].
      unfold image_load in Hil. destruct (image_bytes segs (zo mod 2 ^ 64) (Z.to_nat k)) as [bs|] eqn:Hibs; [|discriminate].
      inversion Hil; subst z.
      assert (HA : A = zo mod 2 ^ 64).
      { subst A. rewrite soff_lit. apply snorm_nonneg_mod.
        pose proof (proj1 Hoh) as HB. rewrite Hbo in HB. cbn [eval] in HB. unfold obj_lo_of in *.
        change (bv_unsigned (Z_to_bv 64 0)) with 0 in HB. rewrite soff_lit in Hlo. lia. }
      rewrite <- HA in Hibs.
      pose proof (obj_read_image segs rho ms o A k bs Hrom Hoh Hd Hbo Hlo Hhi Hk0 Hunc Hibs) as R.
      rewrite Hbo in R.
      eapply load_post_same; [exact Hsm | exact R | | reflexivity].
      rewrite mk_ext_sound. reflexivity.
    +
      apply lrok_inj in Hload as [<- <-].
      pose proof (obj_read_list segs rho ms o A k l Hoh Hd Hlo Hhi Hk0 Hunc) as R.
      destruct (obj_wf_parts _ _ Howf) as (_ & Wlo & _ & _).
      eapply load_post_same; [exact Hsm | exact R | |].
      * rewrite (mk_ext_f_sound rho) by exact Hfacts. cbn [eval].
        rewrite (mk_alu_f_sound rho) by exact Hfacts.
        replace (bv_unsigned (alu64 ALU_SUB (eval rho off) (eval rho (ob_lo o)))) with (A - obj_lo_of rho o); [reflexivity|].
        unfold alu64, alu.
        subst A. pose proof (proj1 Hoh) as RNG. unfold obj_lo_of, obj_hi_of in *.
        pose proof (soff_mod rho off) as M1. pose proof (soff_mod rho (ob_lo o)) as M2.
        rewrite bv_sub_unsigned. unfold bv_wrap. rewrite two64. unfold U in M1, M2. rewrite <- M1, <- M2.
        symmetry. rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. apply Z.mod_small.
        clear - RNG Hlo Hhi Hk0. lia.
      * apply mk_ext_f_below. cbn [sv_below]. apply mk_alu_f_below; [|exact Wlo].
        eapply rel_offset_below; [exact Hae | exact (proj1 (obj_wf_parts _ _ Howf)) | exact Hro].
    +
      apply lrok_inj in Hload as [<- <-].
      pose proof (obj_read_rom segs rho ms o A k l Hoh Hd Hlo Hhi Hk0 Hunc) as R.
      destruct (obj_wf_parts _ _ Howf) as (_ & Wlo & _ & _).
      eapply load_post_same; [exact Hsm | exact R | |].
      * rewrite (mk_ext_f_sound rho) by exact Hfacts. cbn [eval].
        rewrite (mk_alu_f_sound rho) by exact Hfacts.
        replace (bv_unsigned (alu64 ALU_SUB (eval rho off) (eval rho (ob_lo o)))) with (A - obj_lo_of rho o); [reflexivity|].
        unfold alu64, alu.
        subst A. pose proof (proj1 Hoh) as RNG. unfold obj_lo_of, obj_hi_of in *.
        pose proof (soff_mod rho off) as M1. pose proof (soff_mod rho (ob_lo o)) as M2.
        rewrite bv_sub_unsigned. unfold bv_wrap. rewrite two64. unfold U in M1, M2. rewrite <- M1, <- M2.
        symmetry. rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. apply Z.mod_small.
        clear - RNG Hlo Hhi Hk0. lia.
      * apply mk_ext_f_below. cbn [sv_below]. apply mk_alu_f_below; [|exact Wlo].
        eapply rel_offset_below; [exact Hae | exact (proj1 (obj_wf_parts _ _ Howf)) | exact Hro].
    +
      exact (load_arr_sound rho S tr ms md n o off k sgn v S' _ _ _ _ Hsm Hk Hnth Hoh Howf Hoff Hlo Hhi Hd Hload).
  -
    revert Hload.
    destruct (tile_cells 9 (lit_cells (ss_facts S) (ob_cells o) off k) 0 k) as [vt|] eqn:Ht; intros Hload; [|exact (LD _ _ Hload)].
    apply lrok_inj in Hload as [<- <-].
    assert (Hlc : forall d w val, In (d, w, val) (lit_cells (ss_facts S) (ob_cells o) off k) ->
              exists c, In c (ob_cells o) /\ soff rho (c_off c) = A + d /\ c_width c = w /\ c_val c = val).
    { intros d w val Hinl. destruct (lit_cells_spec _ _ _ _ _ _ _ Hinl) as (c & Hin & Hcr & Hcw & Hcval).
      destruct (obj_wf_cell _ _ _ Howf Hin) as (C1 & _).
      exists c. split; [exact Hin|]. split; [|auto].
      exact (cell_rel_lit_sound segs rho (ss_facts S) ms o off k c d Hfacts Hoh Hin Hlo Hhi ltac:(lia) ltac:(lia) Hcr). }
    destruct (tile_cells_sound 9 rho ms o (ss_next S) A _ 0 k vt Hoh Howf Hlc Ht ltac:(lia) ltac:(lia) Hk8)
      as (bs & Hrd & Hval & Hbl).
    rewrite Z.add_0_r, Z.sub_0_r in Hrd.
    eapply load_post_same; [exact Hsm | exact Hrd | | apply mk_ext_below; exact Hbl].
    rewrite mk_ext_sound. f_equal. apply bv_eq. rewrite Hval, Z.mul_0_r, Z.pow_0_r, Z.mul_1_r.
    unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. rewrite two64.
    pose proof (bytes_le_to_Z_bound bs) as B. rewrite (rd_bytes_length _ _ _ _ Hrd), Z2Nat.id in B by lia.
    split; [lia|]. eapply Z.lt_le_trans; [apply B|]. apply Z.pow_le_mono_r; lia.
  -   exact (LD _ _ Hload).
Qed.

Lemma sym_load_sound : ltac2:(tb__ "0|1|
S1cS1fScS85A1M0S7bS86S1aS8SbS1aS1fS27Vsegs;RaR9S13G0S82R8S83R7R6A2A4A4S0SbS20S28RaA1R6A2SdA3S2S0S8R6Z1A3S2S0S8R6Z2A3S2S0S8R6Z4A3S0S8R6Z8A3A2A2A2S0SbS43RcA1S14A3S0S8eS95Vsegs;RdR9R8R7A5S8dR6R5A2A3SceReRfRcS22RfRaA2R9R8R7R6RdRbAaF_;F_;F_;F_;F_;FS';Fv;Fsgn;Fk;Fae;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md ae k sgn v S' Hsm Hae Hk Hlen Hload.
  destruct (sym_load_sound_gen rho S tr ms md ae k sgn v S' Hsm Hae Hk Hload) as [(Hl & _) | H]; [congruence | exact H].
Qed.

Lemma interp_load_val : ltac2:(tb__ "0|5|
Sd4SbS66Q40A1M0G0Se0F_;G0SfS66Q8M1A1M2A1F_;M3ScG2A1M4S0SfG4A1S7dVsegs;R2R4S71S8fR6A1A1A4S10G4R1A2A3S3G0G0S1S0S7cS12SdfG3A2A1SddVsegs;Se1R8R7R6R5A4R4A3SddVsegs;R5R1A1R4A3A3S0G0R1S2aR7SbeG1S73S8fR8A1A1A2Sc6R3A1A3A3A2LVAL;A2F_;Fbs;Fm;Fkk;Fa;Fsgn;Fsz;").
Proof using .
  intros sz sgn a kk m bs H. destruct sz.
  - change (Z.to_nat (msz SZ1)) with 1%nat in H. cbn [load_val interp_eff0 width_bytes]. rewrite H.
    eexists. split; [reflexivity|]. reflexivity.
  - change (Z.to_nat (msz SZ2)) with 2%nat in H. cbn [load_val interp_eff0 width_bytes]. rewrite H.
    eexists. split; [reflexivity|]. reflexivity.
  - change (Z.to_nat (msz SZ4)) with 4%nat in H. cbn [load_val interp_eff0 width_bytes]. rewrite H.
    eexists. split; [reflexivity|]. reflexivity.
  - change (Z.to_nat (msz SZ8)) with 8%nat in H. cbn [load_val interp_eff0 width_bytes]. rewrite H.
    eexists. split; [reflexivity|]. cbn [msz msize_bytes Z.to_N]. rewrite ext_low_64, extract_0_64. reflexivity.
Qed.

Lemma interp_load_fault : ltac2:(tb__ "0|5|
Sd4SbS66Q40A1M0G0Se0F_;G0SfS66Q8A1M1A1F_;M2S0SfScG1A1M3A1S7dVsegs;R1R3S71S8fR5A1A1A4S17G3A1A3S0S7cS12SdfG2A2M4A1SddVsegs;Se1R6R5R4R3A4R2A3S7eG4A1A3F_;Fm;Fkk;Fa;Fsgn;Fsz;").
Proof using .
  intros sz sgn a kk m H. destruct sz.
  - change (Z.to_nat (msz SZ1)) with 1%nat in H. cbn [load_val interp_eff0 width_bytes]. rewrite H. reflexivity.
  - change (Z.to_nat (msz SZ2)) with 2%nat in H. cbn [load_val interp_eff0 width_bytes]. rewrite H. reflexivity.
  - change (Z.to_nat (msz SZ4)) with 4%nat in H. cbn [load_val interp_eff0 width_bytes]. rewrite H. reflexivity.
  - change (Z.to_nat (msz SZ8)) with 8%nat in H. cbn [load_val interp_eff0 width_bytes]. rewrite H. reflexivity.
Qed.

Lemma msz_cases : ltac2:(tb__ "0|1|
Sd4S2S0S8S8fR1A1M0Z1A3S2S0S8G0Z2A3S2S0S8G0Z4A3S0S8G0Z8A3A2A2A2Fsz;").
Proof using . destruct sz; cbn; tauto. Qed.

Definition step_rel (S S' : sstate) (rho : valuation) (tr : list event) (ms : machine_state) (md : Model) : Prop := ltac2:(tb__ "0|0|
S2S1S0SbS43VS;A1SdA3S0S7cS7bA1S80Vsegs;Vms;A2S7eS7bA1A3A2SdeVsegs;VS;VS';Vrho;Vtr;Vms;Vmd;A7A2").

Lemma step_rel_of_next : ltac2:(tb__ "0|0|
S1fS1fS1cScS85A1S7bS86SdeVsegs;R6R5R4R3R2R1A7Sd0R7R6R5R4R3R2A6F_;Fmd;Fms;Ftr;Frho;FS';FS;").
Proof using . intros. right. assumption. Qed.

Lemma step_rel_strict : ltac2:(tb__ "0|0|
S1fS1fS1cScS85A1S7bS86S0SbS43R6A1S14A3Sd0R7R6R5R4R3R2A6SdeVsegs;R8R7R6R5R4R3A7F_;F_;Fmd;Fms;Ftr;Frho;FS';FS;").
Proof using . intros S S' rho tr ms md Hl [[Hl' _] | H]; [congruence | exact H]. Qed.

Lemma interp_eload_fault : ltac2:(tb__ "0|5|
SaS66Q40A1M0S66R2A1Se0F_;G0SfS66Q8A1M1A1F_;M2S0SfScG1A1M3A1S7dVsegs;R1R3S81R4A1A4S17G3A1A3S0S7cS12SdfG2A2M4A1SddVsegs;Se2R5R4R3A3R2A3S7eG4A1A3F_;Fm;Fkk;Fa;Fn;").
Proof using . intros n a kk m H. cbn [interp_eff0]. rewrite H. reflexivity. Qed.

Lemma case_load : ltac2:(tb__ "0|2|
S1fSd4SbS66Q5A1M0G0S66QcA1S1aS1fS1cScS85A1M1S7bS86S0SfSd5A1Sa3Vsegs;S2eRcA1A2S10Sd5Sd6RbRaR9R8R7A5A2A3S0S8eS95Vsegs;RdS99Sa1RdR9A2Sa2R8A1A2S8fRcA1RbA5S8dR7R6A2A3S27Vsegs;R6ReS13G1S82R5S83R4R3A2A4A4Sd0RfSa7Sa8R8RcR9A3S6cS2eRfA1Z4A2A2R7R6R5R4A6F_;F_;F_;Fmd;Fms;Ftr;Frho;FS';Fv;Fimm;Frs1;Frd;Fsgn;Fsz;FS;").
Proof using .
  intros S sz sgn rd rs1 imm v S' rho tr ms md Hi Hload Hsm.
  pose proof (smatch_swf _ _ _ _ Hsm) as Hwf.
  assert (Hae : sv_below (ss_next S) (mk_addk (get_reg S rs1) (immI imm)) = true).
  { apply mk_addk_below. apply get_reg_below. exact Hwf. }
  pose proof (smatch_pcv _ _ _ _ _ _ Hsm) as Hpc.
  assert (Hrom : rom_ok segs ms) by (destruct Hsm as (_ & _ & _ & _ & Hrom & _); exact Hrom).
  destruct (sym_load_sound_gen rho S tr ms md _ _ sgn v S' Hsm Hae (msz_cases sz) Hload)
    as [(Hlen & Hrd & _ & _) | (bs & rho' & Hrd & Hag & Hnext & Hsm' & Hev & Hbelow & Hpc' & _)].
  - left. split; [exact Hlen|].
    rewrite <- (ov_read_bytes_rd segs ms) in Hrd by exact Hrom.
    rewrite mk_addk_sound in Hrd. rewrite <- (rget_match segs rho S tr ms md rs1 Hsm) in Hrd.
    change (Z_to_bv 64 (immI imm)) with (sext 64 imm) in Hrd.
    rewrite (step_instr_at segs ms (ss_pc S) _ Hpc Hi ltac:(discriminate)).
    change (exec (Z_to_bv 64 4) (Load sz sgn rd rs1 imm) (core_of ms))
      with (load_val sz sgn (rget (core_of ms) rs1 + sext 64 imm)%bv
              (fun v0 => EDone (rset rd v0 (with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms))))).
    rewrite (interp_load_fault sz sgn _ _ (ms_mem ms) Hrd). reflexivity.
  - right.
    rewrite <- (ov_read_bytes_rd segs ms) in Hrd by exact Hrom.
    rewrite mk_addk_sound in Hrd. rewrite <- (rget_match segs rho S tr ms md rs1 Hsm) in Hrd.
    change (Z_to_bv 64 (immI imm)) with (sext 64 imm) in Hrd.
    destruct (interp_load_val sz sgn _ (fun v0 => EDone (rset rd v0 (with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms)))) (ms_mem ms) bs Hrd) as (VAL & Hint & HVAL).
    exists (ms_of ms (rset rd VAL (with_pc (Z_to_bv 64 (ss_pc S + 4)) (core_of ms))) (ms_mem ms)), rho'.
    split; [|split; [exact Hag | split; [rewrite ss_next_set_pc_reg; exact Hnext|]]].
    + rewrite (step_instr_at segs ms (ss_pc S) _ Hpc Hi ltac:(discriminate)).
      change (exec (Z_to_bv 64 4) (Load sz sgn rd rs1 imm) (core_of ms))
        with (load_val sz sgn (rget (core_of ms) rs1 + sext 64 imm)%bv
                (fun v0 => EDone (rset rd v0 (with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms))))).
      rewrite Hint. cbn [interp_eff0 lift_result].
      change (c_pc (core_of ms)) with (ms_pc_val ms). unfold ms_pc in Hpc. rewrite Hpc, pc_plus'. reflexivity.
    + eapply smatch_rd_pc; [exact Hsm' | exact Hbelow | rewrite Hev, HVAL; reflexivity].
Qed.

Lemma case_load_strict : ltac2:(tb__ "0|2|
S1fSd4SbS66Q5A1M0G0S66QcA1S1aS1fS1cScS85A1M1S7bS86S0SfSd5A1Sa3Vsegs;S2eRcA1A2S10Sd5Sd6RbRaR9R8R7A5A2A3S0S8eS95Vsegs;RdS99Sa1RdR9A2Sa2R8A1A2S8fRcA1RbA5S8dR7R6A2A3S0SbS43ReA1S14A3S27Vsegs;R7RfS13G1S82R6S83R5R4A2A4A4SdeVsegs;R10Sa7Sa8R9RdRaA3S6cS2eR10A1Z4A2A2R8R7R6R5A7F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;FS';Fv;Fimm;Frs1;Frd;Fsgn;Fsz;FS;").
Proof using .
  intros S sz sgn rd rs1 imm v S' rho tr ms md Hi Hload Hlen Hsm.
  apply (step_rel_strict _ _ _ _ _ _ Hlen). eapply case_load; eauto.
Qed.

End M3.
