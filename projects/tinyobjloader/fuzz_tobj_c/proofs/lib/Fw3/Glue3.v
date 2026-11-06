(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "iff"; "not"; "or"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sobj"; "sprop"; "sstate"; "eval"; "holds"; "reg_sv"; "SLit"; "obj_range"; "ss_facts"; "ss_next"; "smatch"; "ss_objs"; "ss_pc"; "soff"; "cell"; "outside_all"; "mem_match"; "sfcsr"; "swf"; "rm"; "ss_fcsr"; "ss_fregs"; "ss_regs"; "ss_resv"; "agree_below"; "ob_base"; "obj_holds"; "pairwise_disjoint"; "ranges_disjoint"; "ob_hi"; "ob_lo"; "rd_bytes"; "sv_eqb"; "covered"; "mkSS"; "rl"; "sprop_below"; "ss_lenient"; "SVar"; "mkObj"; "rw"; "sprop_eqb"; "DUnknown"; "SPUle"; "c_off"; "c_val"; "c_width"; "enc_bytes"; "mkCell"; "ob_cells"; "ob_dflt"; "ro_addr"; "sv_below"; "DList"; "SPNot"; "ext_low"; "image_byte"; "mkVal"; "obj_hi_of"; "obj_lo_of"; "odefault"; "rd"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "option"; "prod"; "Some"; "bool"; "pair"; "app"; "true"; "nat"; "length"; "nil"; "cons"; "false"; "andb"; "None"; "negb"; "fst"; "snd"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "of_nat"; "opp"; "modulo"; "eqb"; "to_nat"; "sub"; "ltb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "fd_lookup"; "ExitEv"; "FdChannel"; "WriteEv"; "m_fds"; "m_fs"; "page_round_up_Z"; "cstr_result"; "fd_insert"; "CstrOk"; "CstrTooLong"; "iv_overlap"; "read_cstr_aux"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "bv_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "assn"; "etriple"; "triple1"; "w_cfg"; "w_tr"; "model_idle"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "SP"; "ok_frame"; "ok_frameJ"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_ms"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "ms_rom"; "Build_machine_state"; "find_segment"; "ms_fcsr"; "ms_fregs"; "ms_pc_val"; "ms_regs"; "ms_resv"; "ms_svc_pending"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "BC_EQ"; "BC_LTU"; "BC_NE"; "@Corelib.Init.Peano"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.WithSegs"; "diffs_ok"; "svs_diff"; "win"; "cell_sem_eq"; "list_eqb"; "objs_diff"; "sv_diff1"; "win1"; "win_bytes_in_frame"; "with_facts"; "cells_diff"; "list_obj"; "osv_diff"; "osv_eqb"; "same_but_objs"; "sfcsr_diff"; "sfcsr_eqb"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "obj_rng"; "diffs_ok"; "same_but_objs"; "state_diff"; "with_facts"; "Kapp"; "with_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "smatch_pending"; "S_after"; "ok_pframe"; "ok_pframeJ"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "add_fact"; "@Stdlib.Lists.List"; "Forall2"; "forallb"; "In"; "filter"; "existsb"; "hd_error"; "nth_error"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.G2"; "S_after_write";
"@LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess"; "rw_bytes_max"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "zero_range"; "after_sys"; "after_sys_mem"; "exit_code"; "@LinuxProcessSemantics.Riscv.Sem"; "branch_taken"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "ok_halted"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@LinuxProcessSemantics.Riscv.Prelude"; "bv_eqb"; "@Stdlib.Arith.PeanoNat.Nat"; "ltb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW
  SymSoundF SymSoundR SymComplete SymCall SymEntail SymExit SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma u64_lit : ltac2:(tb__ "0|1|
S47S1S5bZ0R1A2S5dR1S5eZ2Z40A2A2A2S0S47S78Q40M0S77G0R2A2A2R2A3F_;Fz;").
Proof. exact u64_of_sum. Qed.

Lemma Z_to_bv64_neq : ltac2:(tb__ "0|2|
S47S47S1S5bZ0R2A2S5dR2S5eZ2Z40A2A2A2M0G0S4S0S47R4R3A3A1S4S0S76Q40M1A1S77G1R5A2S77G1R4A2A3A1F_;F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb Hne E. apply (f_equal bv_unsigned) in E. rewrite !u64_of_sum in E by lia. lia.
Qed.

Lemma bv_sub_ZZ : ltac2:(tb__ "0|1|
S47S47S0S76Q40M0A1S79G0S77G0R2A2S77G0R1A2A3S77G0S64R2R1A2A2A3Fy;Fx;").
Proof. intros x y. rewrite bv_sub_addneg, bv_add_ZZ. reflexivity. Qed.

Lemma zext8_small : ltac2:(tb__ "0|2|
S47S1S5bZ0R1A2S5dR1Z100A2A2S0S76Q40M0A1S40S55Q8S77G0R2A2M1A3G1A3F_;Fz;").
Proof.
  intros z Hz. unfold ext_low, zext. apply bv_eq.
  rewrite bv_zero_extend_unsigned', bv_extract_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite two64. change (bv_modulus 8) with 256.
  rewrite Z.shiftr_0_r. rewrite (Z.mod_small z (2^64)) by lia.
  rewrite (Z.mod_small z 256) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma byte_range : ltac2:(tb__ "0|2|
S76Q8M0A1S1S5bZ0S78G0R1A2M1A2S5dG1Z100A2A2Fb;").
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. lia. Qed.

Lemma enc_bytes_1_byte : ltac2:(tb__ "0|2|
S76Q8M0A1M1S0S49G1A1S38U1S77Q40S78G0R1A2A2A2S54G1R1S53G1A1A3A3Fb;").
Proof.
  intros b. pose proof (byte_range b) as Hb. unfold enc_bytes. cbn [Z_to_le_bytes].
  rewrite u64_of_sum by lia. f_equal. apply Z_to_bv_bv_unsigned.
Qed.

Lemma bt_eq_lit : ltac2:(tb__ "0|2|
S47S47S1S5bZ0R2A2S5dR2S5eZ2Z40A2A2A2M0G0S0S4dScfS9bS77Q40M1R4A2S77G1R3A2A3S62R4R3A2A3F_;F_;Fy;Fx;").
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_eqb. rewrite !u64_of_sum by lia. reflexivity. Qed.

Lemma bt_ne_lit : ltac2:(tb__ "0|2|
S47S47S1S5bZ0R2A2S5dR2S5eZ2Z40A2A2A2M0G0S0S4dScfS9dS77Q40M1R4A2S77G1R3A2A3S58S62R4R3A2A1A3F_;F_;Fy;Fx;").
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_eqb. rewrite !u64_of_sum by lia. reflexivity. Qed.

Lemma bt_ltu_lit : ltac2:(tb__ "0|2|
S47S47S1S5bZ0R2A2S5dR2S5eZ2Z40A2A2A2M0G0S0S4dScfS9cS77Q40M1R4A2S77G1R3A2A3S65R4R3A2A3F_;F_;Fy;Fx;").
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_ltu. rewrite !u64_of_sum by lia. reflexivity. Qed.

Lemma hd_nth0 : forall {A} (d : A) l, hd d l = nth 0 l d.
Proof. intros A d [|x l]; reflexivity. Qed.

Lemma iv_overlap_false : ltac2:(tb__ "0|4|
S76Q40M0A1M1G1G1G1S3S0S4dS74R4R3R2R1A4S55A3S5S5bS5cS78G0R4A2M2S78G0R3A2A2S78G0R2A2M3A2S5bS5cG3S78G0R1A2A2G2A2A2A2Fm;Fb;Fn;Fa;").
Proof.
  intros a n b m. unfold iv_overlap. rewrite andb_false_iff, !Z.ltb_ge. lia.
Qed.

Lemma page_round_up_Z_le : ltac2:(tb__ "0|0|
S47S5bS6fR1A1S5cR1ZfffA2A2Fz;").
Proof.
  intros z. unfold page_round_up_Z, page_size.
  pose proof (Z.mul_div_le (z + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.

Lemma page_round_up_Z_le_bound : ltac2:(tb__ "0|0|
S47S47S5bR2R1A2S0S47S61R2Z1000A2Z0A3S5bS6fR4A1R3A2F_;F_;Fb;Fz;").
Proof.
  intros z b Hz Hb. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod b 4096 ltac:(lia)) as E. rewrite Hb, Z.add_0_r in E.
  set (q := b / 4096) in *.
  assert (H : (z + 4096 - 1) / 4096 < q + 1) by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

Lemma page_round_up_Z_le_26 : ltac2:(tb__ "0|1|
S47S5bR1Z4000000M0A2S5bS6fR2A1G0A2F_;Fz;").
Proof. intros z Hz. apply page_round_up_Z_le_bound; [exact Hz | reflexivity]. Qed.

Lemma page_round_up_Z_pos : ltac2:(tb__ "0|0|
S47S5dZ0R1A2S5bZ1000S6fR2A1A2F_;Fz;").
Proof.
  intros z Hz. unfold page_round_up_Z, page_size.
  assert (1 <= (z + 4096 - 1) / 4096) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma triple_pre_pure : ltac2:(tb__ "0|1|
S49Sc8A1S7aOF_;S7cS7cOS7aR4R1A1R3F_;Fw;R2S7bR7R6R5R4A4M0F_;G0F_;F_;FX;FQ;FP;Fok;Fsegs;").
Proof. intros segs ok P Q X HX HT n Hg w Hp. exact (HT (HX w Hp) n Hg w Hp). Qed.

Lemma etriple_pre_pure : ltac2:(tb__ "0|2|
S49Sc8A1S7aOF_;M0G0OS7aR4R1A1R3F_;Fw;R2S7dR6R5R4A3M1F_;G1F_;F_;FX;FQ;FP;Fsegs;").
Proof. intros segs P Q X HX HT w Hp. exact (HT (HX w Hp) w Hp). Qed.

Lemma triple_False_any : ltac2:(tb__ "0|0|
S49Sc8A1S7aOF_;S7cS7cS7bR4R3R2S7aS6L_;A4S7bR5R4R3R2A4F_;FQ;FP;Fok;Fsegs;").
Proof. intros segs ok P Q H. eapply triple_conseq; [intros w Hw; exact Hw | | exact H]. intros w F. destruct F. Qed.

Definition Kapp (K : list event -> Model -> Prop) (evs : list event) : list event -> Model -> Prop := ltac2:(tb__ "0|1|
S49S66A1M0S67S2G0G0S1VK;R1R2A2S0G0R3S4fS66R1Vevs;A3A3A2Ltr;A2Lmd;Ltr';").

Lemma Kapp_intro : ltac2:(tb__ "0|1|
S49S66A1M0S67OFx0;Fx;G0G0S67R4R2R1A2Sb8R5R4S4fS66R3R4A3R2A4F_;Fmd;Ftr;Fevs;FK;").
Proof. intros K evs tr md Hk. exists tr. auto. Qed.

Lemma fd_lookup_filter_other : ltac2:(tb__ "0|3|
S49S4bS76Q40M0A1M1S68A2M2A1G1G1S4S0G1R2R1A3A1S0S4aS68A1S69Sc4G2G2S58Sd2G0S59G1S68R1A3R4A3A1Lp;R4A3R2A2S69R4R2A2A3F_;Ffd;Fk;Ffds;").
Proof.
  induction fds as [|[k' e] rest IH]; intros k fd Hne; cbn; [reflexivity|].
  unfold bv_eqb at 1. destruct (Z.eqb_spec (bv_unsigned k') (bv_unsigned k)) as [E|E]; cbn.
  - assert (k' = k) by (apply bv_eq; exact E). subst k'.
    rewrite (IH k fd Hne). unfold bv_eqb.
    destruct (Z.eqb_spec (bv_unsigned k) (bv_unsigned fd)) as [E2|E2]; [|reflexivity].
    exfalso. apply Hne. apply bv_eq. exact E2.
  - rewrite (IH k fd Hne). reflexivity.
Qed.

Lemma fd_lookup_insert_same : ltac2:(tb__ "0|1|
S49S4bS76Q40A1M0S68A2A1G0S68S0S4aS68A1S69S71R3R2R1A3R2A2S4cS68R1A2A3Fe;Ffd;Ffds;").
Proof. intros. unfold fd_insert. cbn. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma fd_lookup_insert_other : ltac2:(tb__ "0|1|
S49S4bS76Q40A1M0S68A2A1G0G0S68S4S0G0R3R2A3A1S0S4aS68A1S69S71R5R4R2A3R3A2S69R5R3A2A3F_;Fe;Ffd;Fk;Ffds;").
Proof.
  intros fds k fd e Hne. unfold fd_insert. cbn. unfold bv_eqb at 1.
  destruct (Z.eqb_spec (bv_unsigned k) (bv_unsigned fd)) as [E|E].
  - exfalso. apply Hne. apply bv_eq. exact E.
  - apply fd_lookup_filter_other. exact Hne.
Qed.

Lemma read_cstr_aux_string : ltac2:(tb__ "0|6|
S76Q40M0A1S4aS76Q8M1A1M2A1M3Fx;S49G2A1S51S47S5bZ0M4R1A2S5dS5cS5cR2S5fS52G2R4A2A1A2Z1A2S5eZ2Z40A2A2S51S9eR1S52G2R6A2A2S0G3R8S77G0S5cR5S5fR2A1A2A2A1S4cG2S84G2R2S4fG2R7S54G2S77G1G4A2M5S53G2A1A3A3G5A4A2A3F_;Fj;S4Sc3G2G5R6A3A1S0S70S75R8S77G0R5A2R6A3S4dS70L_;Sd3S52G2R7A2R6A2S72R7A1S73X4dx2A3F_;F_;F_;F_;Fz;Fk;Fs;Fmp;").
Proof.
  intros mp s. induction s as [|b s IH]; intros k z Hz Hnw Hmp Hnin.
  - destruct k as [|k]; cbn [read_cstr_aux length Nat.ltb Nat.leb]; [reflexivity|].
    specialize (Hmp 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in Hmp. cbn in Hmp. rewrite Hmp.
    unfold bv_eqb. rewrite Z.eqb_refl. reflexivity.
  - destruct k as [|k]; [reflexivity|]. cbn [read_cstr_aux].
    pose proof (Hmp 0%nat ltac:(cbn; lia)) as H0. rewrite Z.add_0_r in H0. cbn [nth app] in H0. rewrite H0.
    assert (Hb : bv_eqb b (Z_to_bv 8 0) = false).
    { unfold bv_eqb. apply Z.eqb_neq. intros E. apply Hnin. left. apply bv_eq. exact E. }
    rewrite Hb. rewrite Z_to_bv64_add1.
    cbn [length] in Hnw.
    rewrite (IH k (z + 1)); [| lia | lia | | intros Hin; apply Hnin; right; exact Hin].
    + cbn [length]. change (S (length s) <? S k)%nat with (length s <? k)%nat.
      destruct (length s <? k)%nat; reflexivity.
    + intros j Hj. replace (z + 1 + Z.of_nat j) with (z + Z.of_nat (S j)) by lia.
      rewrite (Hmp (S j)) by (cbn [length]; lia). reflexivity.
Qed.

Lemma fact_at : ltac2:(tb__ "0|0|
S8S49SaA1S51SaS82SaSdR4A1R3A3S0S4aSaA1Sc7SaR4R3A3S4cSaR2A2A3SdR6R3A2F_;F_;Ff;Fn;Fl;Frho;").
Proof. intros rho l n f H Hn. exact (proj1 (Forall_forall _ _) H f (nth_error_In _ _ Hn)). Qed.

Lemma nholds : ltac2:(tb__ "0|0|
S8SaSdR2S3fR1A1A2S4SdR3R2A2A1F_;Fq;Frho;").
Proof. intros rho q H. exact H. Qed.

Lemma holds_hd_fact : ltac2:(tb__ "0|0|
S8SbSaS0S4aSaA1Sc6SaS11R2A1A2S4cSaR1A2A3S82SaSdR4A1S11R3A1A3SdR5R3A2F_;F_;Fp;FS;Frho;").
Proof.
  intros rho S p Hh Hf. destruct (ss_facts S) as [|q l]; [discriminate|]. cbn in Hh. injection Hh as ->.
  exact (Forall_inv Hf).
Qed.

Definition obj_rng (o : sobj) : sv * sv * sv := ltac2:(tb__ "0|0|
S4eS4bS7S7A2S7S4eS7S7S22Vo;A1S27Vo;A1A4S26Vo;A1A4").

Lemma obj_range_of_rng : ltac2:(tb__ "0|2|
S8S9S7S7S7S0S4bS4bS7S7A2M0S7A2Sb3R4A1S4eG0S7S4eS7S7R3R2A4R1A4A3S0S4bS47S47A2S10R6R5A2S4eS47S47S5cS78Q40ScR6R4A2A2M1S16R6R3A2A2S5cG1S16R6R2A2A2A4A3F_;Fhi;Flo;Fb;Fo;Frho;").
Proof. intros rho [ob olo ohi cs d] b lo hi H. unfold obj_rng in H. cbn in H. inversion H; subst. reflexivity. Qed.

Lemma obj_range_rng_eq : ltac2:(tb__ "0|0|
S8S9S9S0S4bS4bS7S7A2S7A2Sb3R2A1Sb3R1A1A3S0S4bS47S47A2S10R4R3A2S10R4R2A2A3F_;Fo';Fo;Frho;").
Proof.
  intros rho [b lo hi cs d] [b' lo' hi' cs' d'] H. unfold obj_rng in H. cbn in H. inversion H; subst. reflexivity.
Qed.

Lemma outside_all_same_ranges : ltac2:(tb__ "0|2|
S8S49S9A1M0G0S76Q40A1S0S49S4bS4bS7S7A2S7A2M1A1S83S9G1Sb3R3A4S83S9G1Sb3R2A4A3S18R5R4R2A3S18R6R4R3A3F_;F_;Fa;Fobjs';Fobjs;Frho;").
Proof.
  intros rho objs. induction objs as [|o t IH]; intros [|o' t'] a Hm Hout; cbn [map] in Hm; try discriminate.
  - constructor.
  - pose proof (f_equal (hd (obj_rng o)) Hm) as Ho. pose proof (f_equal (@tl _) Hm) as Ht. cbn [hd tl] in Ho, Ht.
    inversion Hout; subst. constructor.
    + cbn zeta in *. rewrite <- (obj_range_rng_eq rho o o' Ho). assumption.
    + apply IH; assumption.
Qed.

Definition set_rm (rho : valuation) (m : word -> option byte) : valuation := ltac2:(tb__ "0|0|
S42S31Vrho;A1S2cVrho;A1Vm;A3").

Lemma eval_set_rm : ltac2:(tb__ "0|1|
S8S76Q40A1M0S4aS76Q8A1A1F_;S7S0G0ScSb2R3R2A2R1A2ScR3R1A2A3Fe;Fm;Frho;").
Proof. intros rho m e. induction e; cbn; try reflexivity; try (rewrite IHe1, IHe2; reflexivity); rewrite IHe; reflexivity. Qed.

Lemma soff_set_rm : ltac2:(tb__ "0|0|
S8S76Q40A1S4aS76Q8A1A1F_;S7S0S47S16Sb2R3R2A2R1A2S16R3R1A2A3Fe;Fm;Frho;").
Proof. intros. unfold soff. rewrite eval_set_rm. reflexivity. Qed.

Lemma holds_set_rm : ltac2:(tb__ "0|0|
S8S76Q40A1S4aS76Q8A1A1F_;SaS3SdSb2R3R2A2R1A2SdR3R1A2A2Fp;Fm;Frho;").
Proof.
  intros rho m p. induction p; cbn; rewrite ?eval_set_rm; try (split; intros H; exact H).
  rewrite IHp. split; intros H; exact H.
Qed.

Lemma obj_range_set_rm : ltac2:(tb__ "0|0|
S8S76Q40A1S4aS76Q8A1A1F_;S9S0S4bS47S47A2S10Sb2R3R2A2R1A2S10R3R1A2A3Fo;Fm;Frho;").
Proof. intros. unfold obj_range, obj_lo_of, obj_hi_of. rewrite eval_set_rm, !soff_set_rm. reflexivity. Qed.

Lemma outside_all_set_rm : ltac2:(tb__ "0|1|
S8S76Q40A1M0S4aS76Q8A1A1F_;S49S9A1G0S3S18Sb2R4R3A2R2R1A3S18R4R2R1A3A2Fx;Fobjs;Fm;Frho;").
Proof.
  intros rho m objs x. unfold outside_all. rewrite !Forall_forall.
  split; intros H o Ho; specialize (H o Ho); cbn zeta in *; rewrite ?obj_range_set_rm in *; exact H.
Qed.

Lemma pairwise_disjoint_set_rm : ltac2:(tb__ "0|0|
S8S76Q40A1S4aS76Q8A1A1F_;S49S9A1S24R3R1A2S24Sb2R4R3A2R2A2F_;Fobjs;Fm;Frho;").
Proof.
  intros rho m objs. induction objs as [|o t IH]; intros H; [exact I|].
  destruct H as [Hf Ht]. split; [|apply IH; exact Ht].
  apply Forall_forall. intros o' Hin. rewrite !obj_range_set_rm. exact (proj1 (Forall_forall _ _) Hf o' Hin).
Qed.

Lemma covered_set_rm : ltac2:(tb__ "0|0|
S8S76Q40A1S4aS76Q8A1A1F_;S49S17A1S47S3S2aSb2R4R3A2R2R1A3S2aR4R2R1A3A2Foff;Fcells;Fm;Frho;").
Proof.
  intros. unfold covered. rewrite !Exists_exists. unfold in_cell.
  split; intros (c & Hin & Hc); exists c; split; auto; revert Hc; rewrite !soff_set_rm; intros H; exact H.
Qed.

Definition with_mem (ms : machine_state) (mem : word -> option byte) : machine_state := ltac2:(tb__ "0|0|
S91S96Vms;A1S94Vms;A1S95Vms;A1S98Vms;A1S97Vms;A1S93Vms;A1Vmem;S90Vms;A1A8").

Section WithSegs.
Variable segs : list Segment.

Lemma obj_holds_set_rm_ext : ltac2:(tb__ "0|4|
S8S76Q40M0A1M1S4aS76Q8A1A1M2F_;S8eS8eS9G1S0G2S90R3R1A2S90R4R1A2A3Fa;S47S1S5bS44R7R3A2R1A2S5dR1S43R7R3A2A2A2S0G2S8fR5S77G0S5cS78G0ScR8S22R4A1A2A2R2A2A2M3A2S8fR6G3A2A3F_;Foff;S23Vsegs;R7R5R3A4S23Vsegs;Sb2R8R7A2R5R4A4F_;F_;F_;Fo;Fms';Fms;Fm;Frho;").
Proof using .
  intros rho m ms ms' o Hr Hsame Ho.
  pose proof (obj_holds_mem_ext segs rho ms ms' o Hr Hsame Ho) as (Hb & Hw & Hc & Hd & Hdl).
  unfold obj_holds, obj_lo_of, obj_hi_of in *. rewrite eval_set_rm, !soff_set_rm.
  split; [exact Hb|]. split; [exact Hw|]. split; [|split].
  - apply Forall_forall. intros c Hin. pose proof (proj1 (Forall_forall _ _) Hc c Hin) as Hch.
    unfold cell_holds, oaddr in *. rewrite !eval_set_rm, !soff_set_rm. exact Hch.
  - intros off Hoff Hcov. rewrite covered_set_rm in Hcov. specialize (Hd off Hoff Hcov).
    destruct (ob_dflt o); cbn in *; exact Hd.
  - eapply dflt_inv_exprs; [| | exact Hdl]; [intros; reflexivity|].
    destruct (ob_dflt o); try exact I. split; [symmetry; apply eval_set_rm|].
    apply Forall_forall. intros t _. symmetry. apply eval_set_rm.
Qed.

Lemma smatch_mm : ltac2:(tb__ "0|1|
S8SbS49S66A1M0S8eS67S13Vsegs;R5R4S4eG0S8bR3S8cR2R1A2A4A4S19Vsegs;R6S14R5A1R3A4F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using . intros rho S tr ms md H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))). Qed.

Lemma smatch_facts_hold : ltac2:(tb__ "0|0|
S8SbS4bS49S66A1S8bA2S13Vsegs;R3R2R1A4S82SaSdR4A1S11R3A1A3F_;Fw;FS;Frho;").
Proof using . intros rho S w Hsm. exact (smatch_facts segs rho S w Hsm). Qed.

Lemma mem_frame_rd : ltac2:(tb__ "0|3|
S8S49S9A1S8eS76Q40A1S76Q8A1M0S19Vsegs;R5R4R3A4S18R6R5R3A3S0S4aG0A1M1S1cR7R4A2S4cG0R3A2A3S1S0G1S8fR6R5A2S4cG0R4A2M2A3S0G1S46R6R5A2G2A3A2F_;F_;F_;Fb;Fa;Fms;Fobjs;Frho;").
Proof using .
  intros rho objs ms a b (_ & _ & Hfr) Hout Hrm.
  pose proof (Hfr a Hout) as E. rewrite Hrm in E.
  split; [exact E|]. unfold rd, ms_read_byte. rewrite E. reflexivity.
Qed.

Lemma rd_bytes_frame : ltac2:(tb__ "0|8|
S8S49S9A1S8eS47S49S76Q8M0A1M1A1M2S19Vsegs;R5R4R3A4S1S5bZ0M3R3A2S5dR3S5eZ2Z40A2M4A2A2S5bS5cR4S5fS52G1R3A2A1A2G4A2S51S9fR1S52G1R5A2M5A2S1S18RaR9S77Q40M6S5cR7S5fR2A1A2A2M7A3S0S4aG1A1S1cRaG7A2S4cG1S84G1R2R6S77G0G3A2A4A2A3A2F_;Fj;S0S4aG2A1S28R7S77G6R6A2G5A3S4cG2R5A2A3F_;F_;F_;F_;Fbs;Fa;Fms;Fobjs;Frho;").
Proof using .
  intros rho objs ms a bs Hmm Ha Hnw Hall.
  apply rd_bytes_of_nth; [reflexivity | rewrite u64_of_sum by lia; lia |].
  intros j Hj. rewrite u64_of_sum by lia.
  destruct (Hall j Hj) as [Hout Hrm].
  exact (proj2 (mem_frame_rd rho objs ms _ _ Hmm Hout Hrm)).
Qed.

Definition with_facts (S : sstate) (f : list sprop) : sstate := ltac2:(tb__ "0|0|
S2bS15VS;A1S1fVS;A1S1eVS;A1S1dVS;A1S20VS;A1S14VS;A1Vf;S12VS;A1S2eVS;A1A9").

Lemma swf_with_facts : ltac2:(tb__ "0|0|
SbS49SaA1S0S4dS1bR2A1S50A3S0S4dSc2SaS2dS12R3A1A1R2A3S50A3S0S4dS1bSa9R4R3A2A1S50A3F_;F_;Ff;FS;").
Proof using .
  intros S f Hwf Hf. unfold swf in *. unfold with_facts.
  cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next] in *.
  apply andb_prop in Hwf as [Hwf _]. rewrite Hwf, Hf. reflexivity.
Qed.

Lemma smatch_refacts : ltac2:(tb__ "0|0|
S8SbS49SaA1S4bS49S66A1S8bA2S13Vsegs;R4R3R1A4S0S4dSc2SaS2dS12R4A1A1R3A3S50A3S82SaSdR6A1R4A3S13Vsegs;R7Sa9R6R5A2R4A4F_;F_;F_;Fw;Ff;FS;Frho;").
Proof using .
  intros rho S f [tr [ms md]] Hsm Hb Hf.
  pose proof Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  unfold smatch; cbn [fst snd cfg_ms cfg_model] in *.
  split; [apply swf_with_facts; assumption|].
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hroc|].
  split; [intros r Hr; apply Hregs; exact Hr|].
  split; [intros r; apply Hfregs|].
  split; [exact Hfcsr|]. split; [exact Hresv|]. split; [exact Hmem|]. exact Hf.
Qed.

Fixpoint list_eqb {A} (f : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: l1, b :: l2 => f a b && list_eqb f l1 l2
  | _, _ => false
  end.

Lemma list_eqb_sound : forall {A} (f : A -> A -> bool) l1 l2,
  (forall a b, f a b = true -> a = b) -> list_eqb f l1 l2 = true -> l1 = l2.
Proof using .
  intros A f l1. induction l1 as [|a l1 IH]; intros [|b l2] Hf H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (Hf _ _ H1), (IH l2 Hf H2). reflexivity.
Qed.

Definition sfcsr_eqb (a b : sfcsr) : bool := ltac2:(tb__ "0|1|
S1aS4dLa;Va;S1aS4dLb;M0Vb;S50S7S55Lv;X1ax2S7G0Vb;S55S7S29R2R1A2Lv;X1ax2Lu;X1ax2").

Definition osv_eqb (a b : option sv) : bool := ltac2:(tb__ "0|2|
S4aS7A1M0S4dLa;Va;S7G0S4dLb;M1Vb;S7S29R2R1A2Lv;S55X4ax2Lu;G1Vb;S7S55Ls;S50X4ax2X4ax2").

Definition same_but_objs (S T : sstate) : bool := ltac2:(tb__ "0|0|
S56S56S56S56S56S56S62S15VS;A1S15VT;A1A2Sa4S7S29S1fVS;A1S1fVT;A1A4A2Sa4S7S29S1eVS;A1S1eVT;A1A4A2Sb0S1dVS;A1S1dVT;A1A2A2SadS20VS;A1S20VT;A1A2A2Sa4SaS32S11VS;A1S11VT;A1A4A2S1bVT;A1A2").

Lemma smatch_reobj : ltac2:(tb__ "0|1|
S8SbSbS49S66A1M0S8eS67S0S4dSaeR5R4A2S50A3S13Vsegs;R7R6S4eG0S8bR4S8cR3R2A2A4A4S19Vsegs;R8S14R6A1R4A4S13Vsegs;R9R7S4eG0S8bR6S8cR5R4A2A4A4F_;F_;F_;Fmd;Fms;Ftr;FT;FS;Frho;").
Proof using .
  intros rho S T tr ms md He Hsm Hmm. unfold same_but_objs in He.
  apply andb_prop in He as [He Hwf]. apply andb_prop in He as [He Hfacts]. apply andb_prop in He as [He Hresv].
  apply andb_prop in He as [He Hfcsr]. apply andb_prop in He as [He Hfregs]. apply andb_prop in He as [Hpc Hregs].
  apply Z.eqb_eq in Hpc.
  apply (list_eqb_sound sv_eqb) in Hregs; [|apply sv_eqb_sound].
  apply (list_eqb_sound sv_eqb) in Hfregs; [|apply sv_eqb_sound].
  apply (list_eqb_sound sprop_eqb) in Hfacts; [|apply sprop_eqb_sound].
  assert (Efcsr : ss_fcsr S = ss_fcsr T).
  { destruct (ss_fcsr S), (ss_fcsr T); cbn in Hfcsr; try discriminate; [reflexivity|]. rewrite (sv_eqb_sound _ _ Hfcsr). reflexivity. }
  assert (Eresv : ss_resv S = ss_resv T).
  { destruct (ss_resv S), (ss_resv T); cbn in Hresv; try discriminate; [|reflexivity]. rewrite (sv_eqb_sound _ _ Hresv). reflexivity. }
  destruct T as [pc regs fregs fcsr resv objs facts nx lm]. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in *.
  subst pc regs fregs fcsr resv facts.
  exact (smatch_set_objs_next segs rho S _ objs nx lm Hsm Hmm Hwf).
Qed.

Definition sv_diff1 (a a' : sv) (d : list (sv * sv)) : list (sv * sv) := ltac2:(tb__ "0|1|
S4dS49S4bS7S7A2M0A1L_;S29Va;Va';A2Vd;S54G0S4eS7S7Va;Va';A4Vd;A3X4dx2").

Fixpoint svs_diff (l l' : list sv) : option (list (sv * sv)) :=
  match l, l' with
  | [], [] => Some []
  | a :: t, a' :: t' =>
      match svs_diff t t' with
      | Some d => Some (sv_diff1 a a' d)
      | None => None
      end
  | _, _ => None
  end.

Fixpoint cells_diff (cs cs' : list cell) : option (list (sv * sv)) :=
  match cs, cs' with
  | [], [] => Some []
  | c :: t, c' :: t' =>
      if (c_width c =? c_width c') then
        match cells_diff t t' with
        | Some d => Some (sv_diff1 (c_off c) (c_off c') (sv_diff1 (c_val c) (c_val c') d))
        | None => None
        end
      else None
  | _, _ => None
  end.

Fixpoint objs_diff (os os' : list sobj) : option (list (sv * sv)) :=
  match os, os' with
  | [], [] => Some []
  | o :: t, o' :: t' =>
      if odefault_eqb (ob_dflt o) (ob_dflt o')
      then match cells_diff (ob_cells o) (ob_cells o'), objs_diff t t' with
           | Some d1, Some d2 =>
               Some (sv_diff1 (ob_base o) (ob_base o')
                      (sv_diff1 (ob_lo o) (ob_lo o') (sv_diff1 (ob_hi o) (ob_hi o') d1)) ++ d2)
           | _, _ => None
           end
      else None
  | _, _ => None
  end.

Definition sfcsr_diff (a b : sfcsr) : option (list (sv * sv)) := ltac2:(tb__ "0|6|
S1aS4aS49S4bS7S7A2M0A1M1A1M2La;Va;S1aG2Lb;M3Vb;S4cG1S53G0A1M4A2S7S57G1A1M5Lv;X1ax2S7G3Vb;G5S7S4cG1Sa6R2R1G4A3A2Lv;X1ax2Lu;X1ax2").

Definition osv_diff (a b : option sv) : option (list (sv * sv)) := ltac2:(tb__ "0|7|
S4aS7A1M0S4aS49S4bS7S7A2M1A1M2A1M3La;Va;S7G0G3Lb;M4Vb;S7S4cG2Sa6R2R1S53G1A1M5A3A2Lv;S57G2A1M6X4ax2Lu;G4Vb;S7G6Ls;S4cG2G5A2X4ax2X4ax2").

Definition state_diff (S S' : sstate) : option (list (sv * sv) * list sprop) := ltac2:(tb__ "0|7|
S4dS4aS4bS49S4bS7S7A2M0A1M1S49SaA1M2A2M3A1M4L_;S62S15VS;A1S15VS';A1A2S4aG1A1G4Lx;M5SafS1dVS;A1S1dVS';A1A2G1G5SacS20VS;A1S20VS';A1A2G1G5Sa1S1fVS;A1S1fVS';A1A2G1G5Sa1S1eVS;A1S1eVS';A1A2G1G5Sa5S14VS;A1S14VS';A1A2G1S4cG3S4eG1G2S4fG0R5S4fG0R4S4fG0R3S4fG0R2R1A3A3A3A3Sc4SaSaS58Sc5SaS32R1A1S11VS;A1A3A1Lp;S11VS';A1A3A4A2Ld3;S57G3A1M6X4ax2Ld2;G6X4ax2Ld1;G6X4ax2Ld0';G6X4ax2Ld0;G6X4ax2G6X4dx2").

Definition diffs_ok (rho : valuation) (d : list (sv * sv)) : Prop := ltac2:(tb__ "0|1|
S82S4bS7S7A2M0G0S0S76Q40A1ScVrho;S59S7S7R1A3A2ScVrho;S5aS7S7R1A3A2A3Lp;Vd;A3").

Ltac vm_lhs :=
  match goal with |- ?l = _ => let v := eval vm_compute in l in change l with v end.

Lemma diffs_ok_app : ltac2:(tb__ "0|2|
S8S49S4bS7S7A2M0A1M1G1S3Sa0R3S4fG0R2R1A3A2S1Sa0R3R2A2Sa0R3R1A2A2A2Fd2;Fd1;Frho;").
Proof using . intros. unfold diffs_ok. apply Forall_app. Qed.

Lemma sv_diff1_ok : ltac2:(tb__ "0|0|
S8S7S7S49S4bS7S7A2A1Sa0R4Sa6R3R2R1A3A2S1S0S76Q40A1ScR5R3A2ScR5R4A2A3Sa0R5R2A2A2F_;Fd;Fa';Fa;Frho;").
Proof using .
  intros rho a a' d H. unfold sv_diff1 in H. destruct (sv_eqb a a') eqn:E.
  - split; [|exact H]. symmetry. apply sv_eqb_eval. exact E.
  - inversion H; subst. cbn in *. split; [symmetry; assumption | assumption].
Qed.

Lemma svs_diff_nth : ltac2:(tb__ "0|2|
S8S49S7A1M0G0S49S4bS7S7A2A1M1S51S7S0S4aG1A1Sa1R5R4A2S4cG1R3A2A3Sa0R7R4A2S0S76Q40A1ScR8S84S7R4R6R3A4A2ScR8S84S7R4R7R3A4A2A3F_;F_;Fdflt;Fn;Fd;Fl';Fl;Frho;").
Proof using .
  intros rho l. induction l as [|a t IH]; intros l' d n dflt Hd Hok.
  - destruct l'; [reflexivity | discriminate].
  - destruct l' as [|a' t']; [discriminate|]. cbn in Hd.
    destruct (svs_diff t t') as [d0|] eqn:E; [|discriminate]. injection Hd as <-.
    apply sv_diff1_ok in Hok as [Ha Hd0].
    destruct n as [|n]; cbn; [exact Ha|]. eapply IH; eauto.
Qed.

Lemma svs_diff_length : ltac2:(tb__ "0|2|
S49S7A1M0G0S49S4bS7S7A2A1M1S0S4aG1A1Sa1R3R2A2S4cG1R1A2A3S0S51S52S7R3A2S52S7R4A2A3F_;Fd;Fl';Fl;").
Proof using .
  induction l as [|a t IH]; intros l' d Hd; destruct l' as [|a' t']; try discriminate; [reflexivity|].
  cbn in Hd. destruct (svs_diff t t') eqn:E; [|discriminate]. cbn. f_equal. eapply IH; eauto.
Qed.

Definition cell_sem_eq (rho : valuation) (c c' : cell) : Prop := ltac2:(tb__ "0|0|
S1S0S47S16Vrho;S35Vc';A1A2S16Vrho;S35Vc;A1A2A3S1S0S47S37Vc';A1S37Vc;A1A3S0S76Q40A1ScVrho;S36Vc';A1A2ScVrho;S36Vc;A1A2A3A2A2").

Lemma cells_diff_spec : ltac2:(tb__ "0|2|
S8S49S17A1M0G0S49S4bS7S7A2A1M1S0S4aG1A1SaaR3R2A2S4cG1R1A2A3Sa0R5R2A2Sc1S17S17Sa3R6A1R5R4A5F_;F_;Fd;Fcs';Fcs;Frho;").
Proof using .
  intros rho cs. induction cs as [|c t IH]; intros cs' d Hd Hok.
  - destruct cs'; [constructor | discriminate].
  - destruct cs' as [|c' t']; [discriminate|]. cbn in Hd.
    destruct (c_width c =? c_width c') eqn:E; [|discriminate]. apply Z.eqb_eq in E.
    destruct (cells_diff t t') as [d0|] eqn:Ed; [|discriminate]. injection Hd as <-.
    apply sv_diff1_ok in Hok as [Ho Hok]. apply sv_diff1_ok in Hok as [Hv Hok].
    constructor; [|eapply IH; eauto].
    split; [unfold soff; rewrite Ho; reflexivity|]. split; [symmetry; exact E | exact Hv].
Qed.

Lemma covered_Forall2 : ltac2:(tb__ "0|1|
S8S49S17A1M0G0S47Sc1S17S17Sa3R4A1R3R2A5S3S2aR5R3R2A3S2aR5R4R2A3A2F_;Foff;Fcs';Fcs;Frho;").
Proof using .
  intros rho cs cs' off H. unfold covered. induction H as [|c c' t t' Hc Ht IH].
  - split; intros X; inversion X.
  - destruct Hc as (E1 & E2 & _). unfold in_cell in *.
    split; intros X; inversion X; subst.
    + apply Exists_cons_hd. rewrite <- E1, <- E2. assumption.
    + apply Exists_cons_tl. apply (proj1 IH). assumption.
    + apply Exists_cons_hd. rewrite E1, E2. assumption.
    + apply Exists_cons_tl. apply (proj2 IH). assumption.
Qed.

Lemma obj_holds_sem : ltac2:(tb__ "0|0|
S8S8eS9S9S0S76Q40A1ScR4S22R1A1A2ScR4S22R2A1A2A3S0S47S16R5S27R2A1A2S16R5S27R3A1A2A3S0S47S16R6S26R3A1A2S16R6S26R4A1A2A3S0S45S3bR4A1S3bR5A1A3Sc1S17S17Sa3R8A1S3aR6A1S3aR5A1A5S23Vsegs;R9R8R7A4S23Vsegs;RaR9R7A4F_;F_;F_;F_;F_;F_;Fo';Fo;Fms;Frho;").
Proof using .
  intros rho ms o o' Eb Elo Ehi Ed HF (Hb & Hw & Hc & Hd & Hl).
  unfold obj_holds, obj_lo_of, obj_hi_of in *. rewrite Eb, Elo, Ehi, Ed.
  split; [exact Hb|]. split; [exact Hw|]. split; [|split; [|exact Hl]].
  - clear Hw Hd Hl Hb. induction HF as [|c c' t t' (E1 & E2 & E3) Ht IH]; [constructor|].
    inversion Hc; subst. constructor; [|apply IH; assumption].
    unfold cell_holds, oaddr in *. rewrite E1, E2, E3, Eb. assumption.
  - intros off Hoff Hcov. apply Hd; [exact Hoff|].
    intros C. apply Hcov. apply (proj2 (covered_Forall2 rho _ _ off HF)). exact C.
Qed.

Lemma obj_range_sem : ltac2:(tb__ "0|0|
S8S9S9S0S76Q40A1ScR3S22R1A1A2ScR3S22R2A1A2A3S0S47S16R4S27R2A1A2S16R4S27R3A1A2A3S0S47S16R5S26R3A1A2S16R5S26R4A1A2A3S0S4bS47S47A2S10R6R4A2S10R6R5A2A3F_;F_;F_;Fo';Fo;Frho;").
Proof using . intros rho o o' Eb Elo Ehi. unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, Elo, Ehi. reflexivity. Qed.

Lemma objs_diff_spec : ltac2:(tb__ "0|2|
S8S49S9A1M0G0S49S4bS7S7A2A1M1S0S4aG1A1Sa5R3R2A2S4cG1R1A2A3Sa0R5R2A2Sc1S9S9S9S9S1S0S4bS47S47A2S10R8R1A2S10R8R2A2A3S8eS23Vsegs;R9R1R3A4S23Vsegs;RaR2R3A4F_;Fms;A2Lo';Lo;R5R4A5F_;F_;Fd;Fos';Fos;Frho;").
Proof using .
  intros rho os. induction os as [|o t IH]; intros os' d Hd Hok.
  - destruct os'; [constructor | discriminate].
  - destruct os' as [|o' t']; [discriminate|]. cbn in Hd.
    destruct (odefault_eqb (ob_dflt o) (ob_dflt o')) eqn:E4; [|discriminate].
    apply odefault_eqb_sound in E4.
    destruct (cells_diff (ob_cells o) (ob_cells o')) as [d1|] eqn:Ec; [|discriminate].
    destruct (objs_diff t t') as [d2|] eqn:Eo; [|discriminate].
    injection Hd as <-. apply diffs_ok_app in Hok as [Hok1 Hok2].
    apply sv_diff1_ok in Hok1 as [Eb Hok1]. apply sv_diff1_ok in Hok1 as [Elo Hok1]. apply sv_diff1_ok in Hok1 as [Ehi Hok1].
    assert (Elo' : soff rho (ob_lo o') = soff rho (ob_lo o)) by (unfold soff; rewrite Elo; reflexivity).
    assert (Ehi' : soff rho (ob_hi o') = soff rho (ob_hi o)) by (unfold soff; rewrite Ehi; reflexivity).
    constructor; [|eapply IH; eauto].
    split; [apply obj_range_sem; assumption|].
    intros ms Ho. eapply obj_holds_sem; [exact Eb | exact Elo' | exact Ehi' | symmetry; exact E4 | | exact Ho].
    eapply cells_diff_spec; eauto.
Qed.

Lemma pairwise_disjoint_Forall2 : ltac2:(tb__ "0|1|
S8S49S9A1M0G0Sc1S9S9S9S9S0S4bS47S47A2S10R5R1A2S10R5R2A2A3Lo';Lo;R2R1A5S24R4R3A2S24R5R3A2F_;F_;Fos';Fos;Frho;").
Proof using .
  intros rho os os' H. induction H as [|o o' t t' Ho Ht IH]; intros Hpd; [exact I|].
  destruct Hpd as [Hf Hpd]. split; [|apply IH; exact Hpd].
  clear IH Hpd. induction Ht as [|x x' u u' Hx Hu IHu]; [constructor|].
  inversion Hf; subst. constructor; [|apply IHu; assumption]. rewrite Ho, Hx. assumption.
Qed.

Lemma outside_all_Forall2 : ltac2:(tb__ "0|1|
S8S49S9A1M0G0S76Q40A1Sc1S9S9S9S9S0S4bS47S47A2S10R6R1A2S10R6R2A2A3Lo';Lo;R3R2A5S18R5R3R2A3S18R6R5R3A3F_;F_;Fa;Fos';Fos;Frho;").
Proof using .
  intros rho os os' a H. unfold outside_all. induction H as [|o o' t t' Ho Ht IH]; intros Hout; [constructor|].
  inversion Hout; subst. constructor; [|apply IH; assumption]. cbn zeta in *. rewrite <- Ho. assumption.
Qed.

Lemma mem_match_objs_sem : ltac2:(tb__ "0|2|
S8S8eS49S9A1M0G0S49S4bS7S7A2A1M1S0S4aG1A1Sa5R3R2A2S4cG1R1A2A3Sa0R6R2A2S19Vsegs;R7R5R6A4S19Vsegs;R8R5R7A4F_;F_;F_;Fd;Fos';Fos;Fms;Frho;").
Proof using .
  intros rho ms os os' d Hd Hok (Hall & Hpd & Hfr).
  pose proof (objs_diff_spec rho os os' d Hd Hok) as HF.
  assert (HF1 : Forall2 (fun o o' => obj_range rho o' = obj_range rho o) os os').
  { clear -HF. induction HF; constructor; [exact (proj1 H) | assumption]. }
  split; [|split].
  - clear Hpd Hfr HF1 Hd Hok. revert Hall. induction HF as [|o o' t t' [_ Ho] Ht IH]; intros Hall; [constructor|].
    inversion Hall; subst. constructor; [apply Ho; assumption | apply IH; assumption].
  - eapply pairwise_disjoint_Forall2; eauto.
  - intros a Ha. apply Hfr. eapply outside_all_Forall2; eauto.
Qed.

Lemma filter_new_facts : ltac2:(tb__ "0|1|
S8S49SaA1M0G0S82SaSdR3A1R2A3S82SaSdR4A1Sc4SaSaS58Sc5SaS32R1A1R4A3A1Lp;R2A3A3S82SaSdR5A1R3A3F_;F_;Ffacts';Ffacts;Frho;").
Proof using .
  intros rho facts facts' Hold Hnew. apply Forall_forall. intros p Hin.
  destruct (existsb (sprop_eqb p) facts) eqn:E.
  - apply existsb_exists in E as (q & Hq & Eq). apply sprop_eqb_sound in Eq. subst q.
    exact (proj1 (Forall_forall _ _) Hold _ Hq).
  - apply (proj1 (Forall_forall _ _) Hnew). apply (proj2 (filter_In _ _ _)). split; [exact Hin|]. rewrite E. reflexivity.
Qed.

Theorem smatch_restate : ltac2:(tb__ "0|3|
S8SbSbS4bS49S66A1S8bA2S49S4bS7S7A2A1M0S49SaA1M1S13Vsegs;R6R5R3A4S0S4dS1bR5A1S50A3S0S4aS4bG0G1A2M2A1Sb1R7R6A2S4cG2S4eG0G1R4R3A4A2A3Sa0R9R5A2S82SaSdRaA1R5A3S13Vsegs;RbR9R8A4F_;F_;F_;F_;F_;Fnf;Fd;Fw;FS';FS;Frho;").
Proof using .
  intros rho S S' [tr [ms md]] d nf Hsm Hwf Hsd Hok Hnf.
  unfold state_diff in Hsd.
  destruct (ss_pc S =? ss_pc S') eqn:E1; [|discriminate]. apply Z.eqb_eq in E1.
  destruct (sfcsr_diff (ss_fcsr S) (ss_fcsr S')) as [d0|] eqn:Efc; [|discriminate].
  destruct (osv_diff (ss_resv S) (ss_resv S')) as [d0'|] eqn:Ers; [|discriminate].
  destruct (svs_diff (ss_regs S) (ss_regs S')) as [d1|] eqn:Er; [|discriminate].
  destruct (svs_diff (ss_fregs S) (ss_fregs S')) as [d2|] eqn:Ef; [|discriminate].
  destruct (objs_diff (ss_objs S) (ss_objs S')) as [d3|] eqn:Eo; [|discriminate].
  injection Hsd as <- <-.
  apply diffs_ok_app in Hok as [Hok0 Hok]. apply diffs_ok_app in Hok as [Hok0' Hok].
  apply diffs_ok_app in Hok as [Hok1 Hok]. apply diffs_ok_app in Hok as [Hok2 Hok3].
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [rewrite <- E1; exact Hpc|].
  split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hro|].
  split.
  { intros r Hr0. rewrite (Hr r Hr0). unfold reg_sv.
    destruct (bv_unsigned r =? 0); [reflexivity|]. symmetry. eapply svs_diff_nth; eauto. }
  split.
  { intros r. rewrite (Hf r). unfold freg_sv. symmetry. eapply svs_diff_nth; eauto. }
  split.
  { unfold sfcsr_diff in Efc. destruct (ss_fcsr S), (ss_fcsr S'); try discriminate; [exact Hc|].
    injection Efc as <-. apply sv_diff1_ok in Hok0 as [E _].
    cbn in Hc |- *. rewrite Hc, E. reflexivity. }
  split.
  { unfold osv_diff in Ers. unfold resv_match in *.
    destruct (ss_resv S), (ss_resv S'); try discriminate; destruct (ms_resv ms); try exact Hv; try contradiction.
    injection Ers as <-. apply sv_diff1_ok in Hok0' as [E _]. rewrite Hv, E. reflexivity. }
  split.
  { eapply mem_match_objs_sem; eauto. }
  exact (filter_new_facts rho (ss_facts S) (ss_facts S') Hfa Hnf).
Qed.

Definition win (base : sv) (off : Z) (k : nat) (v : sv) : sobj := ltac2:(tb__ "0|2|
S30Vbase;SfVoff;A1M0SfS5cVoff;S5fVk;A1M1A2A1S54S17S39G0G1Vv;A3S53S17A1A3S33A5").

Definition win_bytes_in_frame (rho : valuation) (b : Z) (off : Z) (k : nat) (v : word) : Prop := ltac2:(tb__ "0|2|
S51S9fR1Vk;A2S0S4aS76Q8M0A1M1A1S1cVrho;S77Q40S5cS5cVb;Voff;A2S5fR2A1A2A2A2S4cG1S84G1R2S38Vk;Vv;A2S77G0Z0A2A4A2A3F_;Fj;").

Lemma soff_lit_small : ltac2:(tb__ "0|1|
S8S47S1S5bS60S5eZ2Z3fA2M0A1R1A2S5dR1G0A2A2S0S47S16R3SfR2A1A2R2A3F_;Fz;Frho;").
Proof using . intros rho z Hz. rewrite soff_lit. apply snorm_id. exact Hz. Qed.

Lemma ranges_disjoint_outside : ltac2:(tb__ "0|2|
S8S49S9A1S47S47S76Q40M0A1S82S9S9S25S10R6R1A2S4eS47S47R4R3A4A2Lo';R4A3S1S5bR4S78G0R2A2M1A2S5dG1R3A2A2S18R7R6R3A3F_;F_;Fa;Fhi;Flo;Fobjs;Frho;").
Proof using .
  intros rho objs lo hi a Hf Ha. unfold outside_all.
  apply Forall_forall. intros o Hin. pose proof (proj1 (Forall_forall _ _) Hf o Hin) as Hd.
  cbn zeta. unfold ranges_disjoint in Hd. cbn [fst snd] in Hd.
  destruct (obj_range rho o) as [f s]. cbn [fst snd] in *. lia.
Qed.

Lemma outside_ranges_disjoint1 : ltac2:(tb__ "0|1|
S8S49S9A1S47S5bZ0R1A2S5bS5cR2Z1M0A2S5eZ2Z40A2A2S18R5R4S77Q40R3A2A3S82S9S9S25S10R7R1A2S4eS47S47R5S5cR5G0A2A4A2Lo';R5A3F_;F_;F_;FA;Fobjs;Frho;").
Proof using .
  intros rho objs A HA Hnw Hout. unfold outside_all in Hout.
  apply Forall_forall. intros o Hin.
  pose proof (proj1 (Forall_forall _ _) Hout o Hin) as H. cbn zeta in H.
  rewrite u64_of_sum in H by lia.
  unfold ranges_disjoint. cbn [fst snd]. destruct (obj_range rho o) as [lo hi]; cbn [fst snd] in *. lia.
Qed.

Lemma pairwise_disjoint_app_l : ltac2:(tb__ "0|1|
S8S49S9A1M0G0S24R3S4fS9R2R1A3A2S24R4R3A2F_;Fl2;Fl1;Frho;").
Proof using .
  intros rho l1 l2. induction l1 as [|o t IH]; intros H; [exact I|].
  cbn in H. destruct H as [Hf Hpd]. split; [|apply IH; exact Hpd].
  apply Forall_app in Hf as [Hf _]. exact Hf.
Qed.

Lemma obj_range_win : ltac2:(tb__ "0|2|
S8S7S47S51S7S5bS60S5eZ2Z3fA2M0A1R3A2S5dS5cR4S5fR3A1A2G0A2S0S4bS47S47A2S10R7Sa2R6R5R4R3A4A2S4eS47S47S5cS78Q40ScR7R6A2A2R5A2M1S5cG1S5fR4A1A2A4A3F_;F_;Fv;Fk;Foff;Fbase;Frho;").
Proof using .
  intros rho base off k v H1 H2. unfold obj_range, obj_lo_of, obj_hi_of, win. cbn [ob_base ob_lo ob_hi].
  rewrite !soff_lit_small by lia. rewrite Z.add_assoc. reflexivity.
Qed.

Lemma outside_with_win : ltac2:(tb__ "0|4|
S8S49S9A1S7S47S51S7S47S18R7R6S77Q40M0R1A2A3S1S5bZ0R2A2S5dR2S5eZ2M1Z40A2A2A2S5bS60S5eG1Z3fA2M2A1R6A2S5dS5cR7S5fR6A1A2G2A2S5S5dR5S5cS78G0ScRbR9A2A2R8A2M3A2S5bS5cG3S5fR7A1A2R5A2A2S18RcS4fS9RbS54S9Sa2RaR9R8R7A4S53S9A1A3A3S77G0R6A2A3F_;F_;F_;F_;F_;Fz;Fv;Fk;Foff;Fbase;Fobjs;Frho;").
Proof using .
  intros rho objs base off k v z Hout Hz H1 H2 Hne. apply outside_all_app. split; [exact Hout|].
  unfold outside_all. apply Forall_cons; [|apply Forall_nil].
  rewrite obj_range_win by lia. cbn [fst snd]. rewrite u64_of_sum by lia. lia.
Qed.

Lemma smatch_carve_win : ltac2:(tb__ "0|3|
S8SbS4bS49S66A1S8bA2S7S47S51S7S48S13Vsegs;R8R7R6A4S2bS15R8A1S1fR8A1S1eR8A1S1dR8A1S20R8A1S4fS9S14R8A1S54S9Sa2R6R5R4R3A4S53S9A1A3A3S11R8A1R2S2eR8A1A9SbS0S4dS1bR1A1S50A3S78Q40ScRbR8A2A2S47S5bS60S5eZ2M0Z3fA2M1A1R8A2S5dS5cR9S5fR8A1A2G1A2S9eR9U8A2S5bZ0S5cR4RbA2A2S5bS5cS5cR5RcA2S5fRbA1A2S5eG0Z40A2A2S82S9S9S25S10R12R1A2S4eS47S47S5cR7ReA2M2S5cG2S5fRdA1A2A4A2Lo';S14R10A1A3Sa8R12R7ReRdScR12RcA2A5S13Vsegs;R13RaR11A4F_;F_;F_;F_;F_;F_;F_;Tb;F_;TS';F_;Fnx;Fv;Fk;Foff;Fbase;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] base off k v nx Hsm S' Hwf b Hs1 Hs2 Hk8 Hlo Hhi Hdisj Hbytes.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  destruct Hm as (Hall & Hpd & Hfr).

  assert (Hmem : forall j, (j < k)%nat ->
            ms_mem ms (Z_to_bv 64 (b + off + Z.of_nat j)) = Some (nth j (enc_bytes k (eval rho v)) (Z_to_bv 8 0))).
  { intros j Hj. rewrite <- (Hbytes j Hj). apply Hfr.
    eapply ranges_disjoint_outside; [exact Hdisj|]. rewrite u64_of_sum by lia. lia. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hro|]. split; [exact Hr|]. split; [exact Hf|].
  split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs]. split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [|constructor].
    unfold obj_holds, obj_lo_of, obj_hi_of, win. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. fold b.
    rewrite !soff_lit_small by lia.
    split; [lia|]. split.
    { intros o Ho. replace o with (off + Z.of_nat (Z.to_nat (o - off))) by lia.
      unfold wview. rewrite Z.add_assoc, (Hmem (Z.to_nat (o - off))) by lia. discriminate. }
    split.
    { constructor; [|constructor]. unfold cell_holds. cbn [c_off c_width c_val].
      rewrite !soff_lit_small by lia. rewrite Nat2Z.id.
      split; [lia|]. split; [lia|].
      destruct k as [|k']; [reflexivity|]. apply rd_bytes_of_nth.
      - apply enc_bytes_length.
      - rewrite oaddr_unsigned by lia. lia.
      - intros j Hj. rewrite oaddr_unsigned by lia. fold b.
        unfold rd, ms_read_byte. rewrite (Hmem j Hj). reflexivity. }
    split; [|exact I].
    intros o Ho _. cbn. exists (nth (Z.to_nat (o - off)) (enc_bytes k (eval rho v)) (Z_to_bv 8 0)).
    unfold rd, ms_read_byte.
    replace (b + o) with (b + off + Z.of_nat (Z.to_nat (o - off))) by lia.
    rewrite (Hmem (Z.to_nat (o - off))) by lia. reflexivity.
  - apply pairwise_disjoint_app1; [exact Hpd|]. rewrite obj_range_win by lia. fold b. exact Hdisj.
  - intros a Ha. apply Hfr. apply outside_all_app in Ha as [Ha _]. exact Ha.
Qed.

Lemma smatch_release_win : ltac2:(tb__ "0|4|
S8SbS4bS49S66A1S8bA2S49S9A1M0S7S47S51S7S48S13Vsegs;R9R8R7A4S0G0S14R9A1S4fS9R7S54S9Sa2R6R5R4R3A4S53S9A1A3A3A3S2bS15RaA1S1fRaA1S1eRaA1S1dRaA1S20RaA1R8S11RaA1R3S2eRaA1A9SbS0S4dS1bR1A1S50A3S78Q40M1ScRdR9A2A2S47S5bS60S5eZ2Z3fA2M2A1R9A2S5dS5cRaS5fR9A1A2G2A2S51S9fR1RbA2S0S4aS76Q8A1M3A1S41Vsegs;S77G1S5cS5cR5RdA2S5fR2A1A2A2A2S57G3A1A3F_;Fj;Sa8R11R4RcRbScR11RaA2A5S13Vsegs;R12R7R10A4F_;F_;F_;F_;Tb;F_;TS';F_;F_;Fnx;Fv;Fk;Foff;Fbase;Fobjs;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] objs base off k v nx Hsm Hobjs S' Hwf b Hs1 Hs2 Himg Hbytes.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  rewrite Hobjs in Hm. destruct Hm as (Hall & Hpd & Hfr).
  apply Forall_app in Hall as [Hall Hwin]. inversion Hwin as [|x l Hoh _]; subst. clear Hwin.
  pose proof Hoh as (Hb & _ & Hcells & _ & _).
  unfold obj_lo_of, obj_hi_of, win in Hb, Hcells. cbn [ob_base ob_lo ob_hi ob_cells] in Hb, Hcells. fold b in Hb.
  rewrite !soff_lit_small in Hb by lia. rewrite !soff_lit_small in Hcells by lia.
  inversion Hcells as [|c l Hcell _]; subst. clear Hcells.
  unfold cell_holds in Hcell. cbn [c_off c_width c_val] in Hcell.
  rewrite !soff_lit_small in Hcell by lia. rewrite Nat2Z.id in Hcell.
  destruct Hcell as (_ & _ & Hcell).

  assert (Hmem : forall j, (j < k)%nat ->
            ms_mem ms (Z_to_bv 64 (b + off + Z.of_nat j)) = rm rho (Z_to_bv 64 (b + off + Z.of_nat j))).
  { intros j Hj. rewrite (Hbytes j Hj).
    pose proof (rd_bytes_nth ms k _ _ j Hcell Hj ltac:(rewrite oaddr_unsigned by lia; lia)) as R.
    rewrite oaddr_unsigned in R by lia. fold b in R.
    unfold rd, ms_read_byte in R.
    destruct (ms_mem ms (Z_to_bv 64 (b + off + Z.of_nat j))) as [bt|] eqn:Em; [exact R|].
    rewrite (Hrom _) , (Himg j Hj) in R. discriminate. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hro|]. split; [exact Hr|]. split; [exact Hf|].
  split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs]. split; [exact Hall|]. split; [eapply pairwise_disjoint_app_l; exact Hpd|].
  intros a Ha.
  destruct (Z_lt_dec (bv_unsigned a) (b + off)) as [Hlt|Hge];
    [|destruct (Z_lt_dec (bv_unsigned a) (b + off + Z.of_nat k)) as [Hlt2|Hge2]].
  - apply Hfr. apply outside_all_app. split; [exact Ha|]. constructor; [|constructor].
    rewrite obj_range_win by lia. cbn [fst snd]. fold b. lia.
  - pose proof (Hmem (Z.to_nat (bv_unsigned a - (b + off))) ltac:(lia)) as M.
    replace (b + off + Z.of_nat (Z.to_nat (bv_unsigned a - (b + off)))) with (bv_unsigned a) in M by lia.
    rewrite Z_to_bv_bv_unsigned in M. exact M.
  - apply Hfr. apply outside_all_app. split; [exact Ha|]. constructor; [|constructor].
    rewrite obj_range_win by lia. cbn [fst snd]. fold b. lia.
Qed.

Definition win1 (e : sv) (off : Z) (v : positive) : sobj := ltac2:(tb__ "0|2|
S30Ve;SfVoff;A1M0SfS5cVoff;Z1M1A2A1S54S17S39G0G1S2fVv;A1A3S53S17A1A3S33A5").

Lemma mem_match_carve1 : ltac2:(tb__ "0|6|
S8S49S9A1S8eS7S47S48S76Q8M0A1M1S19Vsegs;R7R6R5A4S5cS78Q40M2ScR8R5A2A2R4A2S47S5bS60S5eZ2M3Z3fA2M4A1R5A2S5dS5cR6Z1M5A2G4A2S5bZ0R3A2S5bS5cR4G5A2S5eG3Z40A2A2S18RdRcS77G2R5A2A3S0S4aG1A1S1cReS77G2R6A2A2S4cG1R8A2A3S0S76G2A1S31RfRaA2S77G2S78G0R9A2A2A3S19Vsegs;R10S4fS9RfS54S9Sa7RdRcRbA3S53S9A1A3A3ReA4F_;F_;F_;F_;F_;F_;F_;TA;F_;Fb;Fv;Foff;Fe;Fms;Fobjs;Frho;").
Proof using .
  intros rho objs ms e off v b Hmm A Hs1 Hs2 HA Hnw Hout Hrm Hv.
  destruct (mem_frame_rd rho objs ms _ _ Hmm Hout Hrm) as [Hmem Hrd].
  pose proof Hmm as (Hall & Hpd & Hfr).
  assert (Hrange : obj_range rho (win1 e off v) = (A, A + 1)).
  { unfold obj_range, obj_lo_of, obj_hi_of, win1. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
    unfold A. f_equal; lia. }
  split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [|constructor].
    unfold obj_holds, obj_lo_of, obj_hi_of, win1. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
    rewrite !soff_lit_small by lia. fold A.
    split; [lia|]. split.
    { intros off' Hoff'. replace off' with off by lia.
      change (bv_unsigned (eval rho e) + off) with A. unfold wview. rewrite Hmem. discriminate. }
    split.
    { constructor; [|constructor]. unfold cell_holds. cbn [c_off c_width c_val Z.to_nat Pos.to_nat eval].
      rewrite !soff_lit_small by lia. split; [lia|]. split; [lia|].
      rewrite Hv, enc_bytes_1_byte. unfold oaddr. change (bv_unsigned (eval rho e) + off) with A.
      change (Z.to_nat 1) with 1%nat. cbn [rd_bytes]. rewrite Hrd. reflexivity. }
    split; [|exact I].
    intros off' Hoff' Hcov. exfalso. apply Hcov. replace off' with off by lia.
    unfold covered. apply Exists_cons_hd. unfold in_cell. cbn [c_off c_width].
    rewrite soff_lit_small by lia. lia.
  - apply pairwise_disjoint_app1; [exact Hpd|]. rewrite Hrange.
    apply outside_ranges_disjoint1; assumption.
  - intros a Ha. apply outside_all_app in Ha as [Ha _]. apply Hfr. exact Ha.
Qed.

Lemma mem_match_uncarve1 : ltac2:(tb__ "0|6|
S8S49S9A1S8eS7S47S48S76Q8M0A1M1S19Vsegs;R7S4fS9R6S54S9Sa7R4R3R2A3S53S9A1A3A3R5A4S5cS78Q40M2ScR8R5A2A2R4A2S47S5bS60S5eZ2M3Z3fA2M4A1R5A2S5dS5cR6Z1M5A2G4A2S5bZ0R3A2S5bS5cR4G5A2S5eG3Z40A2A2S0S4aSc8A1S92Vsegs;R5G5A3S57Sc8A1A3S0S4aG1A1S1cReS77G2R6A2A2S4cG1R8A2A3S0S76G2A1S31RfRaA2S77G2S78G0R9A2A2A3S19Vsegs;R10RfReA4F_;F_;F_;F_;F_;F_;F_;TA;F_;Fb;Fv;Foff;Fe;Fms;Fobjs;Frho;").
Proof using .
  intros rho objs ms e off v b (Hall & Hpd & Hfr) A Hs1 Hs2 HA Hnw Hseg Hrm Hv.
  apply Forall_app in Hall as [Hall Hw]. apply Forall_inv in Hw.
  assert (Hrange : obj_range rho (win1 e off v) = (A, A + 1)).
  { unfold obj_range, obj_lo_of, obj_hi_of, win1. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
    unfold A. f_equal; lia. }
  assert (Hmem : ms_mem ms (Z_to_bv 64 A) = Some b).
  { destruct Hw as (_ & Hwv & Hcells & _ & _). unfold win1, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells] in *.
    rewrite !soff_lit_small in Hwv by lia.
    specialize (Hwv off ltac:(lia) eq_refl). change (bv_unsigned (eval rho e) + off) with A in Hwv.
    apply Forall_inv in Hcells. unfold cell_holds in Hcells. cbn [c_off c_width c_val eval] in Hcells.
    rewrite !soff_lit_small in Hcells by lia. destruct Hcells as (_ & _ & Hcells).
    change (Z.to_nat 1) with 1%nat in Hcells. cbn [rd_bytes] in Hcells.
    rewrite Hv, enc_bytes_1_byte in Hcells. unfold oaddr in Hcells. change (bv_unsigned (eval rho e) + off) with A in Hcells.
    unfold wview in Hwv. unfold rd, ms_read_byte in Hcells.
    destruct (ms_mem ms (Z_to_bv 64 A)) as [x|] eqn:E.
    - inversion Hcells. reflexivity.
    - exfalso. rewrite u64_of_sum in Hwv by lia. rewrite Hseg in Hwv. exact (Hwv eq_refl). }
  split; [exact Hall|]. split.
  - eapply pairwise_disjoint_app_l. exact Hpd.
  - intros a Ha. destruct (Z.eq_dec (bv_unsigned a) A) as [Ea|Hne].
    + assert (a = Z_to_bv 64 A) as -> by (apply bv_eq; rewrite u64_of_sum by lia; exact Ea).
      rewrite Hmem, Hrm. reflexivity.
    + apply Hfr. apply outside_all_app. split; [exact Ha|]. constructor; [|constructor].
      cbn zeta. rewrite Hrange. cbn [fst snd]. lia.
Qed.

Definition list_obj (base : sv) (lo hi : Z) (l : positive) : sobj := ltac2:(tb__ "0|0|
S30Vbase;SfVlo;A1SfVhi;A1S53S17A1S3eVl;A1A5").

Lemma smatch_carve_list : ltac2:(tb__ "0|6|
S8SbS4bS49S66A1S8bA2S7S47S47S48S48S13Vsegs;R8R7R6A4S2bS15R8A1S1fR8A1S1eR8A1S1dR8A1S20R8A1S4fS9S14R8A1S54S9SabR6R5R4R3A4S53S9A1A3A3S11R8A1R2S2eR8A1A9SbS0S4dS1bR1A1S50A3S78Q40M0ScRbR8A2A2S47S5bS60S5eZ2M1Z3fA2M2A1R8A2S1S5bR9R8A2S5dR8G2A2A2S5dS64R9RaA2G2A2S5bZ0M3S5cR4RbA2A2S5bS5cR5RbA2S5eG1Z40A2A2S0S47S5fS52S76Q8M4A1M5S2cR11RbA2A2A1S64RcRdA2A3S82S9S9S25S10R13R1A2S4eS47S47S5cR8RfA2S5cR8ReA2A4A2Lo';S14R11A1A3S51S9fR1S52G5S2cR14ReA2A2A2S0S4aG5A1S1cR15S77G0S5cS5cRaR11A2S5fR2A1A2A2A2S4cG5S84G5R2S2cR15RfA2S77G4G3A2A4A2A3F_;Fj;S13Vsegs;R14RbR12A4F_;F_;F_;F_;F_;F_;F_;F_;Tb;F_;TS';F_;Fnx;Fl;Fhi;Flo;Fbase;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] base lo hi l nx Hsm S' Hwf b Hs1 Hs2 Hs3 Hlo Hhi Hlen Hdisj Hbytes.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  destruct Hm as (Hall & Hpd & Hfr).
  assert (Hmem : forall j, (j < length (rl rho l))%nat ->
            ms_mem ms (Z_to_bv 64 (b + lo + Z.of_nat j)) = Some (nth j (rl rho l) (Z_to_bv 8 0))).
  { intros j Hj. rewrite <- (Hbytes j Hj). apply Hfr.
    eapply ranges_disjoint_outside; [exact Hdisj|]. rewrite u64_of_sum by lia. lia. }
  assert (Hrange : obj_range rho (list_obj base lo hi l) = (b + lo, b + hi)).
  { unfold obj_range, obj_lo_of, obj_hi_of, list_obj. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
    reflexivity. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hro|]. split; [exact Hr|]. split; [exact Hf|].
  split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs]. split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [|constructor].
    unfold obj_holds, obj_lo_of, obj_hi_of, list_obj. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. fold b.
    rewrite !soff_lit_small by lia.
    split; [lia|]. split.
    { intros o Ho. unfold wview.
      replace (b + o) with (b + lo + Z.of_nat (Z.to_nat (o - lo))) by lia.
      rewrite (Hmem (Z.to_nat (o - lo))) by lia. discriminate. }
    split; [constructor|].
    split.
    { intros o Ho _. cbn [dflt_holds]. unfold rd, ms_read_byte.
      replace (b + o) with (b + lo + Z.of_nat (Z.to_nat (o - lo))) by lia.
      rewrite (Hmem (Z.to_nat (o - lo))) by lia. reflexivity. }
    cbn [dflt_inv]. exact Hlen.
  - apply pairwise_disjoint_app1; [exact Hpd|]. rewrite Hrange. exact Hdisj.
  - intros a Ha. apply Hfr. apply outside_all_app in Ha as [Ha _]. exact Ha.
Qed.

End WithSegs.

Section G2.
Variable segs : list Segment.

Lemma SP_facts_hold : ltac2:(tb__ "0|0|
S49S66A1S67OF_;F_;S8SbS7aS88Vsegs;R4R2R3R1A5S82SaSdR4A1S11R3A1A3F_;Fw;FS;Frho;FK;").
Proof using . intros K rho S w [Hsm _]. eapply smatch_facts_hold; eauto. Qed.

Lemma SP_restate : ltac2:(tb__ "0|3|
S49S66A1S67OF_;F_;S8SbSbS7aS49S4bS7S7A2A1M0S49SaA1M1S0S4dS1bR4A1S50A3S0S4aS4bG0G1A2M2A1Sb6R6R5A2S4cG2S4eG0G1R3R2A4A2A3Sb4R8R4A2S82SaSdR9A1R4A3S88Vsegs;RbR9RaR7A5S88Vsegs;RcR9RbR8A5F_;F_;F_;F_;F_;Fnf;Fd;Fw;FS';FS;Frho;FK;").
Proof using .
  intros K rho S S' w d nf Hwf Hsd Hok Hnf [Hsm Hk]. split; [|exact Hk].
  eapply smatch_restate; eauto.
Qed.

Lemma SP_refacts : ltac2:(tb__ "0|0|
S49S66A1S67OF_;F_;S8SbS49SaA1S7aS88Vsegs;R5R3R4R1A5S0S4dSc2SaS2dS12R4A1A1R3A3S50A3S82SaSdR6A1S11R5A1A3S82SaSdR7A1R5A3F_;S88Vsegs;R8Sb7R6R5A2R7R4A5F_;F_;F_;Fw;Ff;FS;Frho;FK;").
Proof using .
  intros K rho S f w [Hsm Hk] Hb Hf. split; [|exact Hk].
  apply smatch_refacts; [exact Hsm | exact Hb |]. apply Hf. eapply smatch_facts_hold; eauto.
Qed.

Lemma SP_reobj : ltac2:(tb__ "0|0|
S49S66A1S67OF_;F_;S8SbSbS7aS0S4dSb5R3R2A2S50A3S88Vsegs;R6R4R5R2A5S19Vsegs;R6S14R4A1S8dS7fR3A1A1A4S88Vsegs;R8R5R7R4A5F_;F_;F_;Fw;FT;FS;Frho;FK;").
Proof using .
  intros K rho S T [tr [ms md]] He [Hsm Hk] Hmm. split; [|exact Hk].
  eapply smatch_reobj; eauto.
Qed.

Lemma triple_facts : ltac2:(tb__ "0|1|
S7aOF_;S49S66A1S67OF_;F_;SbS8S7cS82SaSdR2A1S11R3A1A3S7bVsegs;R6S88Vsegs;R5R4R3A4R2A4M0F_;G0F_;FQ;Frho;FS;FK;Fok;").
Proof using .
  intros ok K S rho Q H n Hg w Hw. apply H; [|exact Hg|exact Hw].
  eapply SP_facts_hold. exact Hw.
Qed.

Lemma etriple_facts : ltac2:(tb__ "0|1|
S49S66A1S67OF_;F_;SbS8S7aOF_;S82SaSdR2A1S11R3A1A3S7dVsegs;S88Vsegs;R5R4R3A4R2A3M0F_;G0F_;FQ;Frho;FS;FK;").
Proof using .
  intros K S rho Q H w Hw. apply H; [|exact Hw]. eapply SP_facts_hold. exact Hw.
Qed.

Lemma SPJ_facts_hold : ltac2:(tb__ "0|0|
S87S8SbS7aS86Vsegs;R4R2R3R1A5S82SaSdR4A1S11R3A1A3F_;Fw;FS;Frho;FJ;").
Proof using . intros J rho S w [Hsm _]. eapply smatch_facts_hold; eauto. Qed.

Lemma SPJ_restate : ltac2:(tb__ "0|3|
S87S8SbSbS7aS49S4bS7S7A2A1M0S49SaA1M1S0S4dS1bR4A1S50A3S0S4aS4bG0G1A2M2A1Sb6R6R5A2S4cG2S4eG0G1R3R2A4A2A3Sb4R8R4A2S82SaSdR9A1R4A3S86Vsegs;RbR9RaR7A5S86Vsegs;RcR9RbR8A5F_;F_;F_;F_;F_;Fnf;Fd;Fw;FS';FS;Frho;FJ;").
Proof using .
  intros J rho S S' w d nf Hwf Hsd Hok Hnf [Hsm Hk]. split; [|exact Hk].
  eapply smatch_restate; eauto.
Qed.

Lemma SPJ_refacts : ltac2:(tb__ "0|0|
S87S8SbS49SaA1S7aS86Vsegs;R5R3R4R1A5S0S4dSc2SaS2dS12R4A1A1R3A3S50A3S82SaSdR6A1S11R5A1A3S82SaSdR7A1R5A3F_;S86Vsegs;R8Sb7R6R5A2R7R4A5F_;F_;F_;Fw;Ff;FS;Frho;FJ;").
Proof using .
  intros J rho S f w [Hsm Hk] Hb Hf. split; [|exact Hk].
  apply smatch_refacts; [exact Hsm | exact Hb |]. apply Hf. eapply smatch_facts_hold; eauto.
Qed.

Lemma SPJ_reobj : ltac2:(tb__ "0|0|
S87S8SbSbS7aS0S4dSb5R3R2A2S50A3S86Vsegs;R6R4R5R2A5S19Vsegs;R6S14R4A1S8dS7fR3A1A1A4S86Vsegs;R8R5R7R4A5F_;F_;F_;Fw;FT;FS;Frho;FJ;").
Proof using .
  intros J rho S T [tr [ms md]] He [Hsm Hk] Hmm. split; [|exact Hk].
  eapply smatch_reobj; eauto.
Qed.

Lemma triple_factsJ : ltac2:(tb__ "0|1|
S7aOF_;S87SbS8S7cS82SaSdR2A1S11R3A1A3S7bVsegs;R6S86Vsegs;R5R4R3A4R2A4M0F_;G0F_;FQ;Frho;FS;FJ;Fok;").
Proof using .
  intros ok J S rho Q H n Hg w Hw. apply H; [|exact Hg|exact Hw].
  eapply SPJ_facts_hold. exact Hw.
Qed.

Lemma etriple_factsJ : ltac2:(tb__ "0|1|
S87SbS8S7aOF_;S82SaSdR2A1S11R3A1A3S7dVsegs;S86Vsegs;R5R4R3A4R2A3M0F_;G0F_;FQ;Frho;FS;FJ;").
Proof using .
  intros J S rho Q H w Hw. apply H; [|exact Hw]. eapply SPJ_facts_hold. exact Hw.
Qed.

Lemma triple_SPJ_pure : ltac2:(tb__ "0|1|
S7aOF_;S87SbS8S7cS49S66A1M0S67R6R4R2R1A3S7bVsegs;R8S86Vsegs;S8G0S67S1RaR3R2R1A3S1S0G0R2R6A3S0S67R1R5A3A2A2Lm;Lt;Lr;R6R5A4R4A4F_;Fmd;Ftr;S7bVsegs;R6S86Vsegs;R5R4R3A4R2A4F_;FQ;Frho;FS;FJ;Fok;").
Proof using .
  intros ok J S rho Q H n Hg w [Hsm Hk]. destruct w as [tr [ms md]].
  apply (H tr md Hk n Hg). split; [exact Hsm|]. cbn. auto.
Qed.

Lemma triple_SPJ_ex : forall (ok : world -> Prop) (A : Type) (J : A -> jpred) S rho (Q : assn),
  (forall x, triple segs ok (SPJ segs (J x) S rho) Q) ->
  triple segs ok (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q.
Proof using .
  intros ok A J S rho Q H n Hg w [Hsm [x Hx]]. exact (H x n Hg w (conj Hsm Hx)).
Qed.

Lemma triple_SPJ_pure_and : ltac2:(tb__ "0|0|
S7aOF_;OS87SbS8S7cR5S7bVsegs;R7S86Vsegs;R5R4R3A4R2A4F_;S7bVsegs;R7S86Vsegs;S8S49S66A1S67S1R9R8R3R2R1A3A2Lm;Lt;Lr;R4R3A4R2A4F_;FQ;Frho;FS;FJ;FX;Fok;").
Proof using .
  intros ok X J S rho Q H n Hg w [Hsm [HX HJ]]. exact (H HX n Hg w (conj Hsm HJ)).
Qed.

Lemma etriple_SPJ_ex : forall (A : Type) (J : A -> jpred) S rho (Q : world -> Prop),
  (forall x, etriple segs (SPJ segs (J x) S rho) Q) ->
  etriple segs (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q.
Proof using .
  intros A J S rho Q H w [Hsm [x Hx]]. exact (H x w (conj Hsm Hx)).
Qed.

Lemma etriple_SPJ_pure_and : ltac2:(tb__ "0|0|
OS87SbS8S7aOF_;R5S7dVsegs;S86Vsegs;R5R4R3A4R2A3F_;S7dVsegs;S86Vsegs;S8S49S66A1S67S1R9R8R3R2R1A3A2Lm;Lt;Lr;R4R3A4R2A3F_;FQ;Frho;FS;FJ;FX;").
Proof using .
  intros X J S rho Q H w [Hsm [HX HJ]]. exact (H HX w (conj Hsm HJ)).
Qed.

Lemma triple_SPJ_conseq_J : ltac2:(tb__ "0|0|
S7aOF_;S87S87SbS8S7cS49S66A1S67R7R4R2R1A3R7R5R3R2A3F_;Fm;Ft;S7bVsegs;R7S86Vsegs;R5R4R3A4R2A4S7bVsegs;R8S86Vsegs;R7R5R4A4R3A4F_;F_;FQ;Frho;FS;FJ';FJ;Fok;").
Proof using .
  intros ok J J' S rho Q HJ H n Hg w [Hsm Hk]. exact (H n Hg w (conj Hsm (HJ _ _ Hk))).
Qed.

Lemma sv_below_reg : ltac2:(tb__ "0|0|
SbS47S0S4dS1bR2A1S50A3S0S4dS3dS12R3A1SeR3R2A2A2S50A3F_;Fr;FS;").
Proof using .
  intros S r Hwf. unfold reg_sv. destruct (r =? 0); [reflexivity|].
  apply forallb_nth; [apply swf_regs_below; exact Hwf | reflexivity].
Qed.

Definition S_after_write (S : sstate) (e : sv) : sstate := ltac2:(tb__ "0|2|
Sc0Sc0SbbVS;S2fS12VS;A1M0A1M1S14VS;A1Sd1G0A1A4S34SfZ1A1G1A2A2S34G1Ve;A2A2").

Lemma ss_next_S_after : ltac2:(tb__ "0|0|
SbS7S49S9A1S48S0S48S12SbbR4R3R2R1A4A1R1A3Fnx;Fobjs;Fe;FS;").
Proof using . reflexivity. Qed.

Lemma ss_next_add_fact : ltac2:(tb__ "0|0|
SbSaS0S48S12Sc0R2R1A2A1S12R2A1A3Fp;FS;").
Proof using . reflexivity. Qed.

Lemma smatch_after_write : ltac2:(tb__ "0|4|
S8SbS49S66A1M0S8eS67G0S7S47S51SbaVsegs;R9R8S4eG0S8bR7S8cR6R5A2A4A4S0S4dS3dS12R9A1R4A2S50A3S0S47S78Q40M1ScRbR5A2A2R4A3S1S5bZ1S5fR4A1M2A2S5bG2R5A2A2S13Vsegs;SbeRdS12RcA1S77G1S5fR5A1A2M3A3Sc9RcR7A2S4eG0S8bR8S8cSccRaG3A2R9A2A4A4F_;F_;F_;F_;Fk;Fn;Fe;Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' e n k Hsp He Hn Hk.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (urange (eval rho e)) as Hr.
  assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k) by (apply u64_lit; lia).
  assert (Hev : eval (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat k))) e = eval rho e).
  { symmetry. apply (eval_agree (ss_next S)); [apply agree_below_set_rw; lia | exact He]. }
  unfold S_after_write.
  assert (Hlt : (ss_next S <? Pos.succ (ss_next S))%positive = true) by (apply Pos.ltb_lt; lia).
  assert (Hsm1 : smatch segs (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat k)))
                   (S_after S (SVar (ss_next S)) (ss_objs S) (Pos.succ (ss_next S)))
                   (tr', mkCfg (after_sys ms (Z_to_bv 64 (Z.of_nat k))) md)).
  { eapply smatch_after_ret; [exact Hsp | exact Hh]. }
  assert (Hsm2 : smatch segs (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat k)))
                   (add_fact (S_after S (SVar (ss_next S)) (ss_objs S) (Pos.succ (ss_next S)))
                             (SPUle (SLit 1) (SVar (ss_next S))))
                   (tr', mkCfg (after_sys ms (Z_to_bv 64 (Z.of_nat k))) md)).
  { apply smatch_add_fact; [exact Hsm1 | | ].
    - cbn -[Pos.ltb]. rewrite Hlt. reflexivity.
    - cbn [holds eval]. rewrite rho_set_rw_at, Hu. change (bv_unsigned (Z_to_bv 64 1)) with 1%Z. lia. }
  apply smatch_add_fact; [exact Hsm2 | | ].
  - cbn -[Pos.ltb sv_below]. apply andb_true_intro. split; [apply Pos.ltb_lt; lia|].
    exact (sv_below_mono _ _ _ ltac:(apply Pos.lt_le_incl; apply Pos.lt_succ_diag_r) He).
  - cbn [holds eval]. rewrite rho_set_rw_at, Hu, Hev. lia.
Qed.

Lemma triple1_write_ch : ltac2:(tb__ "0|6|
S7aOF_;S49S66A1M0S67OF_;F_;G0S67OFx0;Fx;SbS8S47S49S76Q8A1M1A1M2S7S7S89Vsegs;R9R8A3SbcVsegs;RaR9A3S0S4aS99A1SbfVsegs;S15R8A1A2S4cS99S9aA2A3S0S7SeR9Z11A2SfZ40A1A3S0S7SeRaZaA2SfR8A1A3S0S7SeRbZbA2R7A3S0S7SeRcZcA2R7A3S1S5dZ0RbA2S5dRbS5eZ2Z20A2A2A2S1S5bZ1S5fS52G1RbA2A1M3A2S5bG3ScaA2A2G0S67S51R14R3R2A2S1S9eU1R2A2S9eR2S52G1R10A2A2A2S1S0S4aS68A1S69S6dR4A1S77Q40M4R12A2M5A2S4cS68S6bG5A1A2A3R15S4fS66R5S83G1S66S6cG5A1S85G1R3R11A3A4A3R4A2A2F_;F_;Fk;Fmd;Ftr;G0S8eS67SbaVsegs;R12R13S4eG0S8bR3S8cR2R1A2A4A4R16R4R2A2S0S4aG2A1S28R4ScR14R11A2S63S78G4ScR14R10A2A2A1A3S4cG2R12A2A3F_;F_;Fmd;Fms;Ftr;S7eVsegs;R14S88Vsegs;R13R11R10A4S7aS2S8S8S1S21S12R13A1R12R1A3S88Vsegs;R14Sc9R13ReA2R1R2A5A2Lrho';A2Lw;A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fe;Fa1;Fbs;Fch;Frho;FS;FK';FK;Fok;").
Proof using .
  intros ok K K' S rho ch bs a1 e Hokf Hokp Hi H17 H10 H11 H12 Hch Hlen HK Hbs. subst a1 e.
  apply triple1_ecall_det; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2.
  destruct (HK tr md 1%nat Hk ltac:(lia)) as [Hlk _].
  assert (H64 : bv_unsigned (Z_to_bv 64 64) = 64%Z) by reflexivity.
  assert (Hfd' : fd_lookup (m_fds md) (fd32 (ms_gpr ms 0)) = Some (FdChannel (Z_to_bv 64 ch))).
  { rewrite G0, fd32_lit by lia. exact Hlk. }
  assert (Hch0 : Z_to_bv 64 ch <> Z_to_bv 64 0) by (apply Z_to_bv64_neq; lia).
  assert (Hbuf : read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some bs).
  { rewrite read_bytes_map_rd_bytes, G1, G2. exact (Hbs tr ms md Hsp Hk). }
  pose proof (rd_bytes_length _ _ _ _ (Hbs tr ms md Hsp Hk)) as Hn. rewrite <- G2 in Hn.
  pose proof (urange (ms_gpr ms 2)) as Hr2.
  assert (Hpos : (0 < bv_unsigned (ms_gpr ms 2))%Z) by lia.
  assert (Hmax : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z) by lia.
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. eapply write_only_ok; [exact Hh | exact H64 | exact Hfd' | exact Hch0 | exact Hbuf | exact Hpos | exact Hmax].
  - intros w' Hw. destruct (wstep_write_inv Hp Hh H64 Hfd' Hch0 Hbuf Hpos Hmax Hw) as (k & Hk1 & ->).
    exists (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat k))). split; [apply agree_below_set_rw; lia|].
    split; [|exact (proj2 (HK tr md k Hk Hk1))].
    eapply smatch_after_write; [exact Hsp | apply sv_below_reg; exact Hwf | rewrite <- G2; reflexivity | lia].
Qed.

Lemma etriple_write_ch : ltac2:(tb__ "0|7|
S49S66A1M0S67OFx0;Fx;M1G1SbS8S47S49S76Q8A1M2A1M3S7S7S0S4aS99A1SbfVsegs;S15R6A1A2S4cS99S9aA2A3S0S7SeR7Z11A2SfZ40A1A3S0S7SeR8ZaA2SfR6A1A3S0S7SeR9ZbA2R5A3S0S7SeRaZcA2R5A3S1S5dZ0R9A2S5dR9S5eZ2Z20A2A2A2S1S5bZ1S5fS52G2R9A2A1M4A2S5bG4ScaA2A2G0S67S51R12R3R2A2S1S9eU1R2A2S9eR2S52G2ReA2A2A2S1S0S4aS68A1S69S6dR4A1S77Q40M5R10A2M6A2S4cS68S6bG6A1A2A3R13S4fS66R5S83G2S66S6cG6A1S85G2R3RfA3A4A3R4A2A2F_;F_;Fk;Fmd;Ftr;G0S8eS67SbaVsegs;R10R11S4eG0S8bR3S8cR2R1A2A4A4R14R4R2A2S0S4aG3A1S28R4ScR12RfA2S63S78G5ScR12ReA2A2A1A3S4cG3R10A2A3F_;F_;Fmd;Fms;Ftr;S7dVsegs;S88Vsegs;R11RfReA4S7aS2S8S8S1S21S12R11A1R10R1A3S88Vsegs;R12Sc9R11RcA2R1R2A5A2Lrho';A2Lw;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fe;Fa1;Fbs;Fch;Frho;FS;FK';FK;").
Proof using .
  intros K K' S rho ch bs a1 e Hi H17 H10 H11 H12 Hch Hlen HK Hbs. subst a1 e.
  apply etriple_ecall_det; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2.
  destruct (HK tr md (length bs) Hk ltac:(lia)) as [Hlk Hk'].
  assert (H64 : bv_unsigned (Z_to_bv 64 64) = 64%Z) by reflexivity.
  assert (Hfd' : fd_lookup (m_fds md) (fd32 (ms_gpr ms 0)) = Some (FdChannel (Z_to_bv 64 ch))).
  { rewrite G0, fd32_lit by lia. exact Hlk. }
  assert (Hch0 : Z_to_bv 64 ch <> Z_to_bv 64 0) by (apply Z_to_bv64_neq; lia).
  assert (Hbuf : read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some bs).
  { rewrite read_bytes_map_rd_bytes, G1, G2. exact (Hbs tr ms md Hsp Hk). }
  pose proof (rd_bytes_length _ _ _ _ (Hbs tr ms md Hsp Hk)) as Hn. rewrite <- G2 in Hn.
  pose proof (urange (ms_gpr ms 2)) as Hr2.
  assert (Hpos : (0 < bv_unsigned (ms_gpr ms 2))%Z) by lia.
  assert (Hmax : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z) by lia.
  eexists. split.
  { exact (@wstep_write_intro_prefix segs tr ms md _ _ _ (length bs) Hp Hh H64 Hfd' Hch0 Hbuf Hpos Hmax ltac:(lia)). }
  exists (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat (length bs)))). split; [apply agree_below_set_rw; lia|].
  split; [|exact Hk'].
  eapply smatch_after_write; [exact Hsp | apply sv_below_reg; exact Hwf | rewrite <- G2; reflexivity | lia].
Qed.

Ltac ro_bytes H :=
  lazymatch goal with |- rd_bytes ?ms (Z_to_bv 64 ?a) ?k = Some ?bs =>
    lazymatch type of H with smatch_pending ?segs _ _ _ =>
      apply (ro_read segs ms a k bs);
      [ exact (smatch_pending_rom segs _ _ _ _ _ H)
      | exact (smatch_pending_ro_clear segs _ _ _ _ _ H)
      | lia | lia | lia
      | vm_compute; reflexivity
      | vm_compute; reflexivity ]
    end
  end.

Lemma exit_code_eval : ltac2:(tb__ "0|2|
S8SbS49S66A1M0S8eS67S47SbaVsegs;R6R5S4eG0S8bR4S8cR3R2A2A4A4S0S47S61S78Q40M1ScR7SeR6ZaA2A2A2Z100A2R2A3S0S76G1A1SceR5A1S77G1R3A2A3F_;F_;Fc;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md c Hsp Hc.
  unfold exit_code.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0.
  change (10 + Z.of_nat 0) with 10 in G0. rewrite G0.
  pose proof (urange (eval rho (reg_sv S 10))) as Hr.
  apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  replace (255 mod 2 ^ 64) with (Z.ones 8) by reflexivity. rewrite Z.land_ones by lia.
  change (2 ^ 8) with 256. rewrite Hc.
  pose proof (Z.mod_pos_bound (bv_unsigned (eval rho (reg_sv S 10))) 256 ltac:(lia)).
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma triple_exit_eval : ltac2:(tb__ "0|3|
S7aOF_;S49S66A1M0OF_;G0S67OF_;F_;SbS8S47S89Vsegs;R6R4A3SbcVsegs;R7R5A3Sd0R8R7A2S0S4aS99A1SbfVsegs;S15R6A1A2S4cS99S9aA2A3S5S0S7SeR7Z11A2M1SfZ5eA1A3S0S7G1SfZ5dA1A3A2S0S47S61S78Q40M2ScR7SeR8ZaA2A2A2Z100A2R6A3G0S67RcR2R1A2ReS4fS66R3S54S66S6aS77G2RaA2S6eR2A1A2S53S66A1A3A3A1F_;Fmd;Ftr;S7bVsegs;RdS88Vsegs;RbRaR9A4S7aS6L_;A4F_;F_;F_;F_;F_;F_;F_;Fc;Frho;FS;FK;FSpec;Fok;").
Proof using .
  intros ok Spec K S rho c Hokf Hokp Hokh Hi H17 Hc Hspec.
  apply (@triple_seq segs ok _ (exited_world segs K S rho)).
  - apply triple1_triple. eapply triple1_ecall_det; [exact Hokf | exact Hi |].
    intros tr ms md Hsp Hk.
    pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp.
    pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
    assert (Hno : bv_unsigned (eval rho (reg_sv S 17)) = 93 \/ bv_unsigned (eval rho (reg_sv S 17)) = 94).
    { destruct H17 as [-> | ->]; cbn; [right | left]; reflexivity. }
    split.
    + eapply Hokp; [exact Hk | exact Hp |]. apply exit_only_ok. exact Hno.
    + intros w' Hw. rewrite (wstep_exit_inv Hp (model_idle_halted Hh) Hno Hw).
      exists tr, ms, md. split; [exact Hk|]. split; [exact Hsp | reflexivity].
  - apply triple_halt. intros w' (tr & ms & md & Hk & Hsp & ->).
    split.
    + eapply Hokh; [|apply exited_halted].
      exists (tr ++ [ExitEv (Z_to_bv 64 c) (m_fs md)]). split; [exact (Hspec tr md Hk)|].
      rewrite (exit_code_eval rho S tr ms md c Hsp Hc). apply is_prefix_refl.
    + intros w'' Hw'. exact (wstep_exited_none Hw').
Qed.

Lemma etriple_exit_eval : ltac2:(tb__ "0|3|
S49S66A1M0S67OF_;F_;SbS8S47S0S4aS99A1SbfVsegs;S15R3A1A2S4cS99S9aA2A3S5S0S7SeR4Z11A2M1SfZ5eA1A3S0S7G1SfZ5dA1A3A2S0S47S61S78Q40M2ScR4SeR5ZaA2A2A2Z100A2R3A3S7dVsegs;S88Vsegs;R7R6R5A4S7aS2G0G0S2S67S67S1RaR2R1A2S0G0S80R3A1S4fS66R2S54S66S6aS77G2R7A2S6eR1A1A2S53S66A1A3A3A3A2Lmd;A2Ltr;A2Lw';A3F_;F_;F_;Fc;Frho;FS;FK;").
Proof using .
  intros K S rho c Hi H17 Hc.
  eapply etriple_ecall_det; [exact Hi|].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  assert (Hno : bv_unsigned (eval rho (reg_sv S 17)) = 93 \/ bv_unsigned (eval rho (reg_sv S 17)) = 94).
  { destruct H17 as [-> | ->]; cbn; [right | left]; reflexivity. }
  eexists. split; [exact (@wstep_exit_intro segs tr ms md _ Hp (model_idle_halted Hh) Hno)|].
  exists tr, md. split; [exact Hk|]. cbn. rewrite (exit_code_eval rho S tr ms md c Hsp Hc). reflexivity.
Qed.

Lemma triple1_write_chJ : ltac2:(tb__ "0|7|
S7aOF_;S87S87SbS8S47S49S76Q8A1M0A1M1S7S7S8aVsegs;R9R8A3SbdVsegs;RaR9A3S0S4aS99A1SbfVsegs;S15R8A1A2S4cS99S9aA2A3S0S7SeR9Z11A2SfZ40A1A3S0S7SeRaZaA2SfR8A1A3S0S7SeRbZbA2R7A3S0S7SeRcZcA2R7A3S1S5dZ0RbA2S5dRbS5eZ2Z20A2A2A2S1S5bZ1S5fS52G0RbA2A1M2A2S5bG2ScaA2A2S8S49S66A1M3S67S51S21S12R13A1M4R12R4A3R16R13R4R3A3S1S9eU1R3A2S9eR3S52G0R12A2A2A2S1S0S4aS68A1S69S6dR5A1S77Q40M5R14A2M6A2S4cS68S6bG6A1A2A3R17R7S4fS66R6S83G0S66S6cG6A1S85G0R4R13A3A4A3R5A3A2F_;F_;F_;Fk;Fmd;Ftr;Frho';G3S8eS67SbaVsegs;R12R13S4eG3S8bR3S8cR2R1A2A4A4R16R13R4R2A3S0S4aG1A1S28R4ScR14R11A2S63S78G5ScR14R10A2A2A1A3S4cG1R12A2A3F_;F_;Fmd;Fms;Ftr;S7eVsegs;R14S86Vsegs;R13R11R10A4S7aS2S8S8S1S21G4R12R1A3S86Vsegs;R14Sc9R13ReA2R1R2A5A2Lrho';A2Lw;A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fe;Fa1;Fbs;Fch;Frho;FS;FJ';FJ;Fok;").
Proof using .
  intros ok J J' S rho ch bs a1 e Hokf Hokp Hi H17 H10 H11 H12 Hch Hlen HK Hbs. subst a1 e.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2.
  destruct (HK rho tr md 1%nat (agree_below_refl _ _) Hk ltac:(lia)) as [Hlk _].
  assert (H64 : bv_unsigned (Z_to_bv 64 64) = 64%Z) by reflexivity.
  assert (Hfd' : fd_lookup (m_fds md) (fd32 (ms_gpr ms 0)) = Some (FdChannel (Z_to_bv 64 ch))).
  { rewrite G0, fd32_lit by lia. exact Hlk. }
  assert (Hch0 : Z_to_bv 64 ch <> Z_to_bv 64 0) by (apply Z_to_bv64_neq; lia).
  assert (Hbuf : read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some bs).
  { rewrite read_bytes_map_rd_bytes, G1, G2. exact (Hbs tr ms md Hsp Hk). }
  pose proof (rd_bytes_length _ _ _ _ (Hbs tr ms md Hsp Hk)) as Hn. rewrite <- G2 in Hn.
  pose proof (urange (ms_gpr ms 2)) as Hr2.
  assert (Hpos : (0 < bv_unsigned (ms_gpr ms 2))%Z) by lia.
  assert (Hmax : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z) by lia.
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. eapply write_only_ok; [exact Hh | exact H64 | exact Hfd' | exact Hch0 | exact Hbuf | exact Hpos | exact Hmax].
  - intros w' Hw. destruct (wstep_write_inv Hp Hh H64 Hfd' Hch0 Hbuf Hpos Hmax Hw) as (k & Hk1 & ->).
    assert (Hag : agree_below (ss_next S) rho (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat k)))) by (apply agree_below_set_rw; lia).
    exists (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat k))). split; [exact Hag|].
    split; [|exact (proj2 (HK _ tr md k Hag Hk Hk1))].
    eapply smatch_after_write; [exact Hsp | apply sv_below_reg; exact Hwf | rewrite <- G2; reflexivity | lia].
Qed.

Lemma etriple_write_chJ : ltac2:(tb__ "0|7|
S87S87SbS8S47S49S76Q8A1M0A1M1S7S7S0S4aS99A1SbfVsegs;S15R6A1A2S4cS99S9aA2A3S0S7SeR7Z11A2SfZ40A1A3S0S7SeR8ZaA2SfR6A1A3S0S7SeR9ZbA2R5A3S0S7SeRaZcA2R5A3S1S5dZ0R9A2S5dR9S5eZ2Z20A2A2A2S1S5bZ1S5fS52G0R9A2A1M2A2S5bG2ScaA2A2S8S49S66A1M3S67S51S21S12R11A1M4R10R4A3R14R11R4R3A3S1S9eU1R3A2S9eR3S52G0R10A2A2A2S1S0S4aS68A1S69S6dR5A1S77Q40M5R12A2M6A2S4cS68S6bG6A1A2A3R15R7S4fS66R6S83G0S66S6cG6A1S85G0R4R11A3A4A3R5A3A2F_;F_;F_;Fk;Fmd;Ftr;Frho';G3S8eS67SbaVsegs;R10R11S4eG3S8bR3S8cR2R1A2A4A4R14R11R4R2A3S0S4aG1A1S28R4ScR12RfA2S63S78G5ScR12ReA2A2A1A3S4cG1R10A2A3F_;F_;Fmd;Fms;Ftr;S7dVsegs;S86Vsegs;R11RfReA4S7aS2S8S8S1S21G4R10R1A3S86Vsegs;R12Sc9R11RcA2R1R2A5A2Lrho';A2Lw;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fe;Fa1;Fbs;Fch;Frho;FS;FJ';FJ;").
Proof using .
  intros J J' S rho ch bs a1 e Hi H17 H10 H11 H12 Hch Hlen HK Hbs. subst a1 e.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2.
  assert (Hag : agree_below (ss_next S) rho (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat (length bs))))) by (apply agree_below_set_rw; lia).
  destruct (HK _ tr md (length bs) Hag Hk ltac:(lia)) as [Hlk Hk'].
  assert (H64 : bv_unsigned (Z_to_bv 64 64) = 64%Z) by reflexivity.
  assert (Hfd' : fd_lookup (m_fds md) (fd32 (ms_gpr ms 0)) = Some (FdChannel (Z_to_bv 64 ch))).
  { rewrite G0, fd32_lit by lia. exact Hlk. }
  assert (Hch0 : Z_to_bv 64 ch <> Z_to_bv 64 0) by (apply Z_to_bv64_neq; lia).
  assert (Hbuf : read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some bs).
  { rewrite read_bytes_map_rd_bytes, G1, G2. exact (Hbs tr ms md Hsp Hk). }
  pose proof (rd_bytes_length _ _ _ _ (Hbs tr ms md Hsp Hk)) as Hn. rewrite <- G2 in Hn.
  pose proof (urange (ms_gpr ms 2)) as Hr2.
  assert (Hpos : (0 < bv_unsigned (ms_gpr ms 2))%Z) by lia.
  assert (Hmax : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z) by lia.
  eexists. split.
  { exact (@wstep_write_intro_prefix segs tr ms md _ _ _ (length bs) Hp Hh H64 Hfd' Hch0 Hbuf Hpos Hmax ltac:(lia)). }
  exists (rho_set_rw rho (ss_next S) (Z_to_bv 64 (Z.of_nat (length bs)))). split; [exact Hag|].
  split; [|exact Hk'].
  eapply smatch_after_write; [exact Hsp | apply sv_below_reg; exact Hwf | rewrite <- G2; reflexivity | lia].
Qed.

Lemma triple_exit_evalJ : ltac2:(tb__ "0|3|
S7aOF_;S49S66A1M0OF_;S87SbS8S47S8aVsegs;R6R4A3SbdVsegs;R7R5A3Sd0R8R7A2S0S4aS99A1SbfVsegs;S15R6A1A2S4cS99S9aA2A3S5S0S7SeR7Z11A2M1SfZ5eA1A3S0S7G1SfZ5dA1A3A2S0S47S61S78Q40M2ScR7SeR8ZaA2A2A2Z100A2R6A3G0S67RcRaR2R1A3ReS4fS66R3S54S66S6aS77G2RaA2S6eR2A1A2S53S66A1A3A3A1F_;Fmd;Ftr;S7bVsegs;RdS86Vsegs;RbRaR9A4S7aS6L_;A4F_;F_;F_;F_;F_;F_;F_;Fc;Frho;FS;FJ;FSpec;Fok;").
Proof using .
  intros ok Spec J S rho c Hokf Hokp Hokh Hi H17 Hc Hspec.
  apply (@triple_seq segs ok _ (exited_worldJ segs J S rho)).
  - apply triple1_triple. eapply triple1_ecall_detJ; [exact Hokf | exact Hi |].
    intros tr ms md Hsp Hk.
    pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp.
    pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
    assert (Hno : bv_unsigned (eval rho (reg_sv S 17)) = 93 \/ bv_unsigned (eval rho (reg_sv S 17)) = 94).
    { destruct H17 as [-> | ->]; cbn; [right | left]; reflexivity. }
    split.
    + eapply Hokp; [exact Hk | exact Hp |]. apply exit_only_ok. exact Hno.
    + intros w' Hw. rewrite (wstep_exit_inv Hp (model_idle_halted Hh) Hno Hw).
      exists tr, ms, md. split; [exact Hk|]. split; [exact Hsp | reflexivity].
  - apply triple_halt. intros w' (tr & ms & md & Hk & Hsp & ->).
    split.
    + eapply Hokh; [|apply exited_halted].
      exists (tr ++ [ExitEv (Z_to_bv 64 c) (m_fs md)]). split; [exact (Hspec tr md Hk)|].
      rewrite (exit_code_eval rho S tr ms md c Hsp Hc). apply is_prefix_refl.
    + intros w'' Hw'. exact (wstep_exited_none Hw').
Qed.

Lemma etriple_exit_evalJ : ltac2:(tb__ "0|3|
S87SbS8S47S0S4aS99A1SbfVsegs;S15R3A1A2S4cS99S9aA2A3S5S0S7SeR4Z11A2M0SfZ5eA1A3S0S7G0SfZ5dA1A3A2S0S47S61S78Q40M1ScR4SeR5ZaA2A2A2Z100A2R3A3S7dVsegs;S86Vsegs;R7R6R5A4S7aS2S49S66A1M2G2S2S67S67S1RaR8R2R1A3S0G2S80R3A1S4fS66R2S54S66S6aS77G1R7A2S6eR1A1A2S53S66A1A3A3A3A2Lmd;A2Ltr;A2Lw';A3F_;F_;F_;Fc;Frho;FS;FJ;").
Proof using .
  intros J S rho c Hi H17 Hc.
  eapply etriple_ecall_detJ; [exact Hi|].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  assert (Hno : bv_unsigned (eval rho (reg_sv S 17)) = 93 \/ bv_unsigned (eval rho (reg_sv S 17)) = 94).
  { destruct H17 as [-> | ->]; cbn; [right | left]; reflexivity. }
  eexists. split; [exact (@wstep_exit_intro segs tr ms md _ Hp (model_idle_halted Hh) Hno)|].
  exists tr, md. split; [exact Hk|]. cbn. rewrite (exit_code_eval rho S tr ms md c Hsp Hc). reflexivity.
Qed.

Lemma smatch_pending_rezero : ltac2:(tb__ "0|6|
S8SbS49S66A1M0S8eS67S76Q40M1A1M2G2SbaVsegs;R7R6S4eG0S8bR5S8cR4R3A2A4A4S5bS5cS78G1R3A2S78G1R2A2A2S5eZ2Z40A2A2S9Sc3S9R1S14R9A1A3S25S10RbR2A2S4eS47S47S78G1R6A2M3S5cG3S78G1R5A2A2M4A4A2F_;Fo;G2S1S5bG3S78G1R1A2M5A2S5dG5G4A2A2S0S4dS3cVsegs;R2A2S55A3F_;Fx;SbaVsegs;Sb2RbScbS1cRbA1R6R5A3A2RaS4eG0S8bR9S8cSb9R8ScbS8fR8A1R6R5A3A2R7A2A4A4F_;F_;F_;F_;Fn;Fa;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md a n Hsp Hnw Hdisj Hnro.
  pose proof Hsp as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & (Hall & Hpd & Hfr) & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (swf_objs S Hwf) as Hobjwf.
  assert (Hzr : forall mem x, zero_range mem a n x = if in_range a n x then Some (Z_to_bv 8 0) else mem x)
    by (intros; apply zero_range_at).
  unfold smatch_pending. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|].
  split; [cbn; rewrite eval_set_rm; exact Hpend|].
  split; [exact Hhalt|]. split; [exact Hrom|].
  split.
  { intros x Hro. cbn [with_mem ms_mem]. rewrite Hzr. destruct (in_range a n x) eqn:Hir.
    - apply in_range_spec in Hir. rewrite (Hnro x Hir) in Hro. discriminate.
    - apply Hroc. exact Hro. }
  split; [intros r Hr; rewrite eval_set_rm; apply Hregs; exact Hr|].
  split; [intros r; rewrite eval_set_rm; apply Hfregs|].
  split; [unfold fcsr_match in *; destruct (ss_fcsr S); [exact Hfcsr | rewrite eval_set_rm; exact Hfcsr]|].
  split; [unfold resv_match in *; cbn [with_mem ms_resv]; destruct (ss_resv S); destruct (ms_resv ms);
          rewrite ?eval_set_rm; exact Hresv|].
  split; [|apply Forall_forall; intros p Hp; apply holds_set_rm; exact (proj1 (Forall_forall _ _) Hfacts p Hp)].
  split; [|split].
  - apply Forall_forall. intros o Hin.
    pose proof (proj1 (Forall_forall _ _) Hall o Hin) as Ho.
    pose proof (proj1 (forallb_forall _ _) Hobjwf o Hin) as Howf.
    eapply (obj_holds_set_rm_ext segs rho _ ms); [intros ?; reflexivity | | exact Ho].
    intros off Hoff. cbn [with_mem ms_mem]. rewrite Hzr.
    pose proof (Hdisj o Hin) as D. pose proof (proj1 Ho) as HB.
    unfold obj_range, ranges_disjoint in D. cbn [fst snd] in D.
    destruct (in_range a n _) eqn:Hir; [|reflexivity].
    apply in_range_spec in Hir. rewrite u64_of_sum in Hir by lia. lia.
  - apply pairwise_disjoint_set_rm. exact Hpd.
  - intros x Hout. apply outside_all_set_rm in Hout. cbn [with_mem ms_mem set_rm rm]. rewrite !Hzr.
    destruct (in_range a n x); [reflexivity|]. apply Hfr. exact Hout.
Qed.

Lemma smatch_after_mmap_noobj : ltac2:(tb__ "0|7|
S8SbS49S66A1M0S8eS67G0S67S76Q40M1A1M2G2SbaVsegs;R9R8S4eG0S8bR7S8cR6R5A2A4A4S81R4A1S5bS5cS78G1R4A2S78G1R3A2A2S5eZ2Z40A2A2S9Sc3S9R1S14RcA1A3S25S10ReR2A2S4eS47S47S78G1R7A2M3S5cG3S78G1R6A2A2M4A4A2F_;Fo;G2S1S5bG3S78G1R1A2M5A2S5dG5G4A2A2S0S4dS3cVsegs;R2A2S55A3F_;Fx;S13Vsegs;SbeSb2ReScbS1cReA1R7R6A3A2S12RdA1M6R7A3SbbRdS2fG6A1S14RdA1Sd1G6A1A4S4eG0S8bR9S8cScdRbR7ScbS8fRbA1R7R6A3A3R8A2A4A4F_;F_;F_;F_;F_;Fn;Fa;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' a n Hsp Hh' Hnw Hdisj Hnro.
  pose proof (smatch_pending_rezero rho S tr ms md a n Hsp Hnw Hdisj Hnro) as Hsp'.
  exact (smatch_after_ret segs _ S tr _ md tr' md' a Hsp' Hh').
Qed.

End G2.
