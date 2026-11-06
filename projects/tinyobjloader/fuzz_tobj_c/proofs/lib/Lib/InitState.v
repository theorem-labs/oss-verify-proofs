(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "N"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "lt"; "mul"; "of_N"; "pow"; "modulo"; "sub"; "leb"; "opp"; "to_N"; "to_nat"; "ltb"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "list"; "length"; "option"; "Some"; "nat"; "nil"; "pair"; "true"; "None"; "andb"; "app"; "prod"; "false"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_extract"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.Init"; "rho0"; "ms0"; "auxv_ws"; "c0"; "rnd0"; "rnd1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "SVar"; "eval"; "sprop"; "cell"; "SAlu"; "SPUle"; "sobj"; "obj_holds"; "obj_range"; "mkObj"; "rw"; "obj_hi_of"; "DUnknown"; "SPAlign"; "ob_base"; "ob_dflt"; "DList"; "cell_holds"; "enc_bytes"; "image_byte"; "ob_cells"; "obj_lo_of"; "rd"; "rd_bytes"; "soff"; "DImage"; "DZero"; "FcsrFrm0"; "covered"; "dflt_holds"; "dflt_inv"; "dflt_writable"; "fregs_match"; "mem_match"; "mkSS"; "mkVal"; "pairwise_disjoint"; "regs_match"; "ro_addr"; "smatch"; "swf"; "valuation"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "ph_addr"; "ph_ent"; "ph_num"; "seg_base"; "seg_bytes"; "seg_writable"; "@Corelib.Lists.ListDef"; "nth"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "find_segment"; "segment_byte_at"; "wview"; "machine_state"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "@Corelib.Init.Peano"; "lt"; "le"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "word_le8"; "len_word"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "tab"; "pad_len"; "region"; "argv_ptrs"; "bsb"; "env_bytes"; "hdr_bytes"; "@Stdlib.Lists.List"; "flat_map"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "sll3"; "S0"; "cell8"; "O_env"; "O_str0"; "O_aux"; "O_data"; "O_hdr"; "O_rand"; "O_stk"; "STK_FREE"; "aux_base"; "env_base"; "fregs0"; "objs0"; "regs0"; "cells_from"; "data_ok_b"; "@Corelib.Init.Nat"; "add"; "mul"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "stack_max_size"; "sp_window_hi"; "sp_window_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.Checks"; "data_ok_from"; "segs_top"; "data_ok_b"; "@Stdlib.NArith.BinNat.N"; "add"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "entry_slack"; "entry_stack_fits"; "entry_stack_image"; "init_config"; "init_machine_state"; "total_arg_bytes"; "@LinuxProcessSemantics.LinuxProcessSem.StackLayout"; "AT_EUID"; "AT_HWCAP"; "AT_NULL"; "AT_PAGESZ"; "AT_PHDR"; "AT_PHENT"; "AT_PHNUM"; "AT_RANDOM"; "AT_SECURE"; "AT_UID"; "at_random_bytes"; "at_random_ptr"; "auxv_bytes"; "ed_slack"; "stack_to_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "w0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.Params"; "F0"; "O_aux"; "O_data"; "O_env"; "O_hdr"; "O_rand"; "O_stk"; "O_str0"; "RAND_HI"; "SP_HI"; "STR0_END_HI"; "aux_svs"; "cells_from"; "objs0"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition STK_FREE : Z := 1048576.

Definition V_SP : positive := 1.
Definition V_ARGC : positive := 2.
Definition V_ENVC : positive := 3.
Definition V_ARGV0 : positive := 4.
Definition V_LEN0 : positive := 5.
Definition V_RAND : positive := 6.
Definition V_UID : positive := 7.
Definition V_HWCAP : positive := 8.
Definition V_RND0 : positive := 9.
Definition V_RND1 : positive := 10.
Definition L_ENV : positive := 1.
Definition L_STR0 : positive := 2.

Definition regs0 : list sv := list_set (repeat (SLit 0) 32) 2 (SVar 1).
Definition fregs0 : list sv := repeat (SLit 0) 32.

Definition sll3 (i : positive) : sv := ltac2:(tb__ "0|0|
S34S6cS30Vi;A1S2eZ3A1A3").
Definition env_base : sv := ltac2:(tb__ "0|0|
S34S6bS34S6bS30P1A1S78P2A1A3S2eZ10A1A3").
Definition aux_base : sv := ltac2:(tb__ "0|0|
S34S6bS34S6bS34S6bS30P1A1S78P2A1A3S78P3A1A3S2eZ18A1A3").

Definition cell8 (off : Z) (v : sv) : cell := mkCell (SLit off) 8 v.

Section Params.
Variable pc0 : Z.
Variable ph : PhdrInfo.
Variable data_lo data_hi : Z.

Definition aux_svs : list sv := ltac2:(tb__ "0|2|
S15S2fS2eZ3A1S15S2fS2eScS5bVph;A1A1A1S15S2fS2eZ4A1S15S2fS2eScS5cVph;A1A1A1S15S2fS2eZ5A1S15S2fS2eScS5dVph;A1A1A1S15S2fS2eZ10A1S15S2fS30P8A1S15S2fS2eZ6A1S15S2fS2eZ1000A1S15S2fS2eZbA1S15S2fS30P7A1M0S15S2fS2eZcA1S15S2fG0S15S2fS2eZ17A1S15S2fS2eZ0A1M1S15S2fS2eZ19A1S15S2fS30P6A1S15S2fG1S15S2fG1S1cS2fA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Fixpoint cells_from (off : Z) (l : list sv) : list cell :=
  match l with
  | [] => []
  | v :: r => cell8 off v :: cells_from (off + 8) r
  end.

Definition O_stk : sobj := ltac2:(tb__ "0|0|
S39S30P1A1S2eS11S82A1A1S2eZ0A1S1cS33A1S4aA5").
Definition O_hdr : sobj := ltac2:(tb__ "0|1|
S39S30P1A1S2eZ0M0A1S2eZ10A1S15S33S7aG0S30P2A1A2S15S33S7aZ8S30P4A1A2S1cS33A1A3A3S3cA5").
Definition O_env : sobj := ltac2:(tb__ "0|0|
S39S84S2eZ0A1S34S6bS78P3A1S2eZ8A1A3S1cS33A1S40P1A1A5").
Definition O_aux : sobj := ltac2:(tb__ "0|1|
S39S83S2eZ0M0A1S2eZa0A1Sb6G0Sb5A2S3cA5").
Definition O_str0 : sobj := ltac2:(tb__ "0|0|
S39S30P4A1S2eZ0A1S34S6bS30P5A1S2eZ1A1A3S1cS33A1S40P2A1A5").
Definition O_rand : sobj := ltac2:(tb__ "0|1|
S39S30P6A1S2eZ0M0A1S2eZ10A1S15S33S7aG0S30P9A1A2S15S33S7aZ8S30PaA1A2S1cS33A1A3A3S3cA5").
Definition O_data : sobj := ltac2:(tb__ "0|0|
S39S2eZ0A1S2eVdata_lo;A1S2eVdata_hi;A1S1cS33A1S49A5").

Definition objs0 : list sobj := ltac2:(tb__ "0|0|
S15S36Sb0S15S36SaeS15S36SadS15S36SabS15S36Sb1S15S36SafS15S36SacS1cS36A1A3A3A3A3A3A3A3").

Definition SP_HI : Z := sp_window_hi - 224.
Definition STR0_END_HI : Z := sp_window_hi - 17.
Definition RAND_HI : Z := sp_window_hi - 16.

Definition F0 : list sprop := ltac2:(tb__ "0|a|
S15S32S3dP1M0Z4A2S15S32S35S2eS8eA1M1S30G0A1M2A2S15S32S35G2S2eSb3A1A2S15S32S35S2eZ1A1S30P2A1M3A2S15S32S35G3S2eZ400A1A2S15S32S35S30P3A1S2eZ100A1A2S15S32S35G1S30P4M4A1M5A2S15S32S35S34S6bG5S30P5A1M6A3S2eSb4A1A2S15S32S35G6S2eZ1ffffA1A2S15S32S3dG4Z3M7A2S15S32S3dP6M8G7A2S15S32S35G1S30G8A1M9A2S15S32S35G9S2eSb2A1A2S1cS32A1A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition S0 : sstate := ltac2:(tb__ "0|0|
S52Vpc0;S87S85S4bS1fS2fA1Sb7SaaP14S23A9").

End Params.

Section Checks.
Variable segs : list Segment.

Fixpoint data_ok_from (a : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match image_byte segs (Z_to_bv 64 a) with
      | Some _ =>
          match find_segment segs a 1 with
          | Some seg => seg_writable seg
                        && match segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg))) with
                           | Some _ => true | None => false end
          | None => false
          end
      | None => false
      end && data_ok_from (a + 1) n'
  end.

Definition data_ok_b (lo hi : Z) : bool := ltac2:(tb__ "0|0|
S20S20S10Z0Vlo;A2S10Vlo;Vhi;A2A2S8fVlo;S13SfVhi;Vlo;A2A1A2A2").

Fixpoint segs_top (l : list Segment) : Z :=
  match l with
  | [] => 0
  | s :: r => Z.max (Z.of_N (seg_base s) + Z.of_N (seg_size s)) (segs_top r)
  end.

Lemma find_segment_top : ltac2:(tb__ "0|0|
S17S5aA1S4S4S5aS8Z0R2A2S0S19S5aA1S64R5R4R3A3S1aS5aR2A2A3S8S7R5R4A2S90R6A1A2F_;F_;Fseg;Fn;Fa;Fl;").
Proof using .
  induction l as [|s l IH]; intros a n seg Hn H; [discriminate|].
  cbn [find_segment segs_top] in *.
  destruct (Z.leb (Z.of_N (seg_base s)) a && Z.leb (a + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) eqn:E.
  - apply andb_prop in E as [_ E2]. apply Z.leb_le in E2. lia.
  - specialize (IH a n seg Hn H). lia.
Qed.

Lemma ro_addr_top : ltac2:(tb__ "0|1|
S24Q40M0A1S0S16S56Vsegs;R1A2S1eA3S8S7S25G0R2A2Z1A2S90Vsegs;A1A2F_;Fa;").
Proof using .
  intros a H. unfold ro_addr in H.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:E; [|discriminate].
  eapply find_segment_top; [lia|exact E].
Qed.

Lemma data_ok_from_spec : ltac2:(tb__ "0|4|
S4S1bS1bS0S16S8fR3R2A2S1eA3S69R2R3A2S1S2S24Q8A1M0G0S0S19G0A1M1S43Vsegs;S26Q40S7R6S9R4A1A2A2A2S1aG0R1A2M2A3Lb;A2S2S5aS5aS2G0G0S1S0S19S5aA1S64Vsegs;S7R7S9R5A1A2M3Z1A3S1aS5aR2A2A3S1S0S16S60R2A1S1eA3S0G1S65S5fR2A1S12SfG3ScS5eR2A1A1A2A1A2G2A3A2A2Lb;A2Lseg;A2A2F_;F_;Fj;Fn;Fa;").
Proof using .
  intros a n. revert a. induction n as [|n IH]; intros a j H Hj; [lia|].
  cbn [data_ok_from] in H. apply andb_prop in H as [H1 H2].
  destruct j as [|j].
  - rewrite Z.add_0_r.
    destruct (image_byte segs (Z_to_bv 64 a)) as [b|]; [|discriminate].
    destruct (find_segment segs a 1) as [seg|]; [|discriminate].
    apply andb_prop in H1 as [Hw Hs].
    destruct (segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg)))) as [b'|] eqn:Eb; [|discriminate].
    split; [exists b; reflexivity|]. exists seg, b'. auto.
  - replace (a + Z.of_nat (S j)) with (a + 1 + Z.of_nat j) by lia. apply IH; [exact H2|lia].
Qed.

Lemma data_ok_b_spec : ltac2:(tb__ "0|3|
S4S4S4S0S16S91R3R2A2S1eA3S1S8R4R2A2SaR2R3A2A2S1S2S24Q8A1M0G0S0S19G0A1M1S43Vsegs;S26Q40R4A2A2S1aG0R1A2M2A3Lb;A2S2S5aS5aS2G0G0S1S0S19S5aA1S64Vsegs;R5Z1A3S1aS5aR2A2A3S1S0S16S60R2A1S1eA3S0G1S65S5fR2A1S12SfR5ScS5eR2A1A1A2A1A2G2A3A2A2Lb;A2Lseg;A2A2F_;F_;Fx;Fhi;Flo;").
Proof using .
  intros lo hi x H Hx. unfold data_ok_b in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  replace x with (lo + Z.of_nat (Z.to_nat (x - lo))) by lia.
  apply (data_ok_from_spec lo (Z.to_nat (hi - lo))); [exact H3|lia].
Qed.

End Checks.

Lemma pow64 : 2 ^ 64 = 18446744073709551616. Proof. reflexivity. Qed.
Lemma pow63 : 2 ^ 63 = 9223372036854775808. Proof. reflexivity. Qed.
Lemma mod64 : bv_modulus 64 = 2 ^ 64. Proof. reflexivity. Qed.

Lemma word_le8_enc : ltac2:(tb__ "0|0|
S24Q40A1S0S17S24Q8A1A1S6dR1A1S42U8R1A2A3Fw;").
Proof.
  intros w. apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)).
  { rewrite enc_bytes_length. reflexivity. }
  intros n Hn. rewrite length_word_le8 in Hn. unfold enc_bytes. rewrite Z_to_le_bytes_nth by exact Hn.
  unfold word_le8.
  destruct n as [|[|[|[|[|[|[|[|n]]]]]]]]; try lia; cbn -[Z.shiftr Z.mul Z.of_nat];
    apply bv_eq; rewrite bv_extract_unsigned, Z_to_bv_unsigned; reflexivity.
Qed.

Lemma nth_flat_map_le8 : ltac2:(tb__ "0|7|
S17S24Q40M0A1M1A1S1bS1bS69R2S18G1R3A2A2S69R2U8M2A2S0S24Q8M3A1M4S61G4S8aS8bG2R4A2R3A2S76G1G4S6dR5A4S26G3Z0M5A2M6A4S61G4R3S6dS61G1R4R5S26G0G5A2A4A1G6A4A3F_;F_;Fj;Fk;Fws;").
Proof.
  induction ws as [|w ws IH]; intros k j Hk Hj; [cbn in Hk; lia|].
  cbn [flat_map]. destruct k as [|k].
  - rewrite app_nth1 by (rewrite length_word_le8; lia). cbn [nth]. replace (8 * 0 + j)%nat with j by lia. reflexivity.
  - rewrite app_nth2 by (rewrite length_word_le8; lia). rewrite length_word_le8.
    replace (8 * S k + j - 8)%nat with (8 * k + j)%nat by lia. cbn [nth]. apply IH; [cbn in Hk; lia|exact Hj].
Qed.

Lemma obj_holds_of : ltac2:(tb__ "0|3|
S17S5aA1S59S67S36S4S4S4S0S4S25Q40M0S31R6S3eR4A1A2A2R3A3S0S4S45R7R5A2R3A3S0S4S3bR8R6A2R3A3S1S8Z0S7R6R5A2A2S1S8S7R6R4A2SdZ2M1Z40A2A2S1S8R5R4A2SaSfR4R5A2SdG1Z3fA2A2A2A2A2S4S1S8R7R1A2SaR1R6A2A2S0S16S4fS3fRaA1A1S1eA3S3S0S19S24Q8A1M2A1S66ReS63RcA1S26G0S7RaR3A2A2A3S1fG2A1A3A1F_;F_;Foff;S62S33S41RbS3eR9A1R7R6RaA5S44R9A1A3S4S1S8R9R1A2SaR1R8A2A2S3S4cReS44RcA1R2A3A1S4dR10RfS3fRdA1RbR3ReS26G0S7RcR3A2A2A7F_;F_;Foff;S4eRdS3fRbA1RaR9R8RcA6S37RfReRdRcA4F_;F_;F_;F_;F_;F_;F_;F_;Fhi;Flo;Fb;Fo;Fms;Frho;Fsegs;").
Proof.
  intros segs rho ms o b lo hi Hb Hlo Hhi H1 H2 H3 H4 H5. unfold obj_holds. rewrite Hb, Hlo, Hhi. cbn zeta.
  repeat split; try apply H1; auto.
Qed.

Lemma U_addr : ltac2:(tb__ "0|1|
S4S1S8Z0R1A2SaR1SdZ2Z40A2A2A2S0S4S25Q40M0S26G0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. apply Z_to_bv_small. rewrite mod64. exact Hz. Qed.

Lemma nth_regs0 : ltac2:(tb__ "0|1|
S1bS69R1U20A2S0S2fS61S2fR2S87S2eZ0A1M0A4S16S2fL_;Sb8R2U2A2S30P1A1G0X16x2A3F_;Fk;").
Proof.
  intros k Hk.
  do 32 (destruct k as [|k]; [reflexivity|]). lia.
Qed.

Lemma nth_fregs0 : ltac2:(tb__ "0|1|
S1bS0S2fS61S2fR1S85S2eZ0A1M0A4G0A3Fk;").
Proof.
  intros k. unfold fregs0. destruct (Nat.lt_ge_cases k 32).
  - apply nth_repeat.
  - apply nth_overflow. rewrite repeat_length. lia.
Qed.

Lemma bvmap_get_empty : forall (r : reg) (A : Type), @bvmap_get 5 A r bvmap_empty = None.
Proof. intros r A. unfold bvmap_get, bvmap_empty. destruct (bv_key r); reflexivity. Qed.

Lemma reg5_range : ltac2:(tb__ "0|2|
S24Q5M0A1S1S8Z0S25G0R1A2M1A2SaG1Z20A2A2Fr;").
Proof. intros r. pose proof (bv_unsigned_in_range 5 r) as H. change (bv_modulus 5) with 32 in H. lia. Qed.

Lemma bv_extract_extract : ltac2:(tb__ "0|1|
S5S5S5S5S24Q80M0A1S93S92R2R4A2R5A2S0S24R5A1S27R6R3R5S27G0R4R6R2A4A4S27G0S92R4R3A2R5R2A4A3F_;Fr;Fs;Fs0;Fl;Fn;").
Proof.
  intros n l s0 s r H. apply bv_eq. rewrite !bv_extract_unsigned.
  unfold bv_wrap, bv_modulus.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i (Z.of_N l)) as [Hl|Hl].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftr_spec by lia. f_equal. lia.
  - rewrite !Z.mod_pow2_bits_high; [reflexivity| lia | lia].
Qed.

Lemma at_random_bytes_words : ltac2:(tb__ "0|4|
S24Q80M0A1S0S17S24Q8A1M1A1Sa4R1A1S76S24Q40M2A1M3G1S6dS15G3S27G0Q0G2R1A4S15G3S27G0G2G2R1A4S1cG3A1A3A3A4A3Fr;").
Proof.
  intros r. unfold at_random_bytes, word_le8. cbn [flat_map app].
  rewrite !(bv_extract_extract 64) by (cbv; congruence). reflexivity.
Qed.

Section Init.
Variable segs : list Segment.
Variable pc0 : N.
Variable ph : PhdrInfo.
Variable data_lo data_hi : Z.
Hypothesis Hdata : ltac2:(tb__ "0|0|
S0S16S89Vsegs;Vdata_lo;Vdata_hi;A3S1eA3").
Hypothesis Hdata_hi : data_hi <= 2 ^ 40.
Hypothesis Htop : segs_top segs <= 2 ^ 40.

Variable sp brk mb : word.
Variable draw : EntryDraw.
Variable lim : Z.
Variable inp : ProcInput.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hinp : valid_input_either inp.

Let argv := in_argv inp.
Let envp := in_envp inp.

Let uid := in_uid inp.
Let hwcap := in_hwcap inp.

Definition rnd0 : word := bv_extract 0 64 (ed_random draw).
Definition rnd1 : word := bv_extract 64 64 (ed_random draw).

Definition ms0 : machine_state := ltac2:(tb__ "0|0|
S98Vsegs;Vpc0;Vph;Vsp;Vdraw;Vargv;Venvp;Vuid;Vhwcap;A9").
Definition c0 : config := ltac2:(tb__ "0|0|
S97Vsegs;Vpc0;Vph;Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;A9").

Lemma c0_ms : cfg_ms c0 = ms0.
Proof using . reflexivity. Qed.

Let ARGC := Z.of_nat (length argv).
Let ENVC := Z.of_nat (length envp).
Let STR := Z.of_nat (str_off argv envp).
Let RND := Z.of_nat (rand_off argv envp).
Let LEN := Z.of_nat (img_len argv envp).
Let argv0 : list byte := nth 0 argv [].

Definition rho0 : valuation := ltac2:(tb__ "0|a|
S53S6S16S24Q40M0A1L_;M1S68R1P1A2M2Vsp;G1S68R1P2A2M3S26G0VARGC;A2G1S68R1P3A2S26G0VENVC;A2G1S68R1P4A2S26G0S7S25G0Vsp;A2M4VSTR;A2A2G1S68R1P5A2S26G0S9S18S24Q8M5A1M6Vargv0;A2A1A2G1S68R1P6A2S26G0S7G4VRND;A2A2G1S68R1P7A2Vuid;G1S68R1P8A2Vhwcap;G1S68R1P9A2S2cG1S68R1PaA2S2dS26G0Z0M7A2X16x2X16x2X16x2X16x2X16x2X16x2X16x2X16x2X16x2X16x2Li;S6S16S17G6A1L_;M8G2S74Vsp;Vargv;Venvp;A3G8G3S21G6Vargv0;S15G6S26G5G7A2S1cG6A1M9A3A3G9X16x2X16x2Ll;S63S29A1A3").

Record Jinit (rho : valuation) : Prop := mkJinit {
  ji_sp    : rw rho 1 = sp;
  ji_argc  : rw rho 2 = Z_to_bv 64 (Z.of_nat (length argv));
  ji_envc  : rw rho 3 = Z_to_bv 64 (Z.of_nat (length envp));
  ji_argv0 : rw rho 4 = Z_to_bv 64 (bv_unsigned sp + Z.of_nat (str_off argv envp));
  ji_len0  : rw rho 5 = Z_to_bv 64 (Z.of_nat (length (nth 0 argv [])));
  ji_rand  : rw rho 6 = Z_to_bv 64 (bv_unsigned sp + Z.of_nat (rand_off argv envp));
  ji_uid   : rw rho 7 = uid;
  ji_hwcap : rw rho 8 = hwcap;
  ji_rnd0  : rw rho 9 = rnd0;
  ji_rnd1  : rw rho 10 = rnd1;
  ji_env   : rl rho 1 = env_bytes sp argv envp;
  ji_str0  : rl rho 2 = nth 0 argv [] ++ [Z_to_bv 8 0];
  ji_mem   : forall a, rm rho a = ms_mem ms0 a
}.

Lemma Jinit_rho0 : Jinit rho0.
Proof using . constructor; reflexivity. Qed.

Lemma argv_valid : valid_argv argv.
Proof using Hinp. exact (proj1 Hinp). Qed.
Lemma envp_valid : valid_envp envp.
Proof using Hinp. exact (proj1 (proj2 Hinp)). Qed.

Lemma tab_le : ltac2:(tb__ "0|2|
S17S17S24Q8A1M0A1M1A1S4S4S62G1G1S8S9S18G0R1A2A1R3A2La;R3A3S8S99R4A1R2A2S8S9S6fR5A1A1R3A2F_;F_;Fn;Fb;Fl;").
Proof using . intros l b n _ H. rewrite total_arg_bytes_tab in H. exact H. Qed.

Lemma ARGC_bound : 1 <= ARGC <= 1024.
Proof using ENVC Hinp LEN RND STR. pose proof argv_valid as (H & _). subst ARGC. lia. Qed.

Lemma ENVC_bound : 0 <= ENVC <= 256.
Proof using ARGC Hinp LEN RND STR. pose proof envp_valid as (H & _). subst ENVC. lia. Qed.

Lemma tab_argv_bound : Z.of_nat (tab argv) <= 2097152.
Proof using Hinp. pose proof argv_valid as (_ & H & _). rewrite total_arg_bytes_tab in H. exact H. Qed.

Lemma tab_envp_bound : Z.of_nat (tab envp) <= 131072.
Proof using Hinp. pose proof envp_valid as (_ & H & _). rewrite total_arg_bytes_tab in H. exact H. Qed.

Lemma len0_bound : Z.of_nat (length argv0) <= 131071.
Proof using ENVC Hinp argv.
  pose proof argv_valid as (H1 & _ & H3 & _). unfold argv0 in *.
  destruct argv as [|a r]; [cbn in H1; lia|]. cbn. inversion H3. exact H2.
Qed.

Lemma len0_tab : ltac2:(tb__ "0|0|
S6aS8aS18S24Q8A1Vargv0;A2U1A2S6fVargv;A1A2").
Proof using ENVC Hinp.
  pose proof argv_valid as (H1 & _). unfold argv0 in *.
  destruct argv as [|a r]; [cbn in H1; lia|]. cbn. lia.
Qed.

Lemma STR_eq : ltac2:(tb__ "0|1|
S0S4VSTR;S7S7Zb8SbZ8M0VARGC;A2A2SbG0VENVC;A2A2A3").
Proof using LEN RND. subst STR ARGC ENVC. unfold str_off, aux_off, argc, envc. lia. Qed.

Lemma RND_eq : ltac2:(tb__ "0|0|
S0S4VRND;S7S7S7VSTR;S9S6fVargv;A1A1A2S9S6fVenvp;A1A1A2S9S70Vargv;Venvp;A2A1A2A3").
Proof using ARGC ENVC LEN. subst RND STR. unfold rand_off, raw_len, env_str_off. lia. Qed.

Lemma LEN_eq : LEN = RND + 16.
Proof using ARGC ENVC STR. subst LEN RND. unfold img_len. lia. Qed.

Lemma pad_lt8 : ltac2:(tb__ "0|0|
SaS9S70Vargv;Venvp;A2A1Z8A2").
Proof using ARGC ENVC LEN RND STR. pose proof (pad_len_lt8 argv envp). lia. Qed.

Lemma LEN_bound : LEN <= 4194304 - 16.
Proof using ARGC ENVC Hinp RND STR.
  rewrite LEN_eq, RND_eq, STR_eq. pose proof ARGC_bound. pose proof ENVC_bound.
  pose proof tab_argv_bound. pose proof tab_envp_bound. pose proof pad_lt8. lia.
Qed.

Lemma sp_bound : ltac2:(tb__ "0|1|
S1S1S8S8eS25Q40Vsp;A2M0A2S8G0S8dA2A2S0S4SeG0Z10A2Z0A3A2").
Proof using Hsp. pose proof Hsp as (A & B & C). auto. Qed.

Hypothesis Hfit : ltac2:(tb__ "0|0|
S95Vsp;Vargv;Venvp;A3").

Lemma LEN_fit : ltac2:(tb__ "0|0|
S8S7S25Q40Vsp;A2VLEN;A2S8dA2").
Proof using ARGC ENVC Hfit Hinp RND STR.
  pose proof Hfit as F. unfold entry_stack_fits, entry_stack_span in F.
  rewrite LEN_eq, RND_eq, STR_eq. pose proof pad_lt8.
  rewrite !total_arg_bytes_tab in F. unfold auxv_size in F. subst ARGC ENVC argv envp. lia.
Qed.

Lemma sp_lo_val : sp_window_lo = 0x7fff80000000. Proof using . reflexivity. Qed.
Lemma sp_hi_val : sp_window_hi = 0x800000000000. Proof using . reflexivity. Qed.
Lemma stack_max_size_val : stack_max_size = 8388608. Proof using . reflexivity. Qed.

Let BSB : ltac2:(tb__ "0|0|
S17S24Q8A1A1") := ltac2:(tb__ "0|0|
S73Vph;Vsp;Vargv;Venvp;Vuid;Vhwcap;Vdraw;A7").

Lemma length_BSB : ltac2:(tb__ "0|0|
S0S4S9S18S24Q8A1VBSB;A2A1VLEN;A3").
Proof using argv envp ph sp. subst BSB LEN. rewrite length_bsb. reflexivity. Qed.

Let ESI : ltac2:(tb__ "0|0|
S17S24Q8A1A1") := ltac2:(tb__ "0|0|
S96Vph;Vsp;Vargv;Venvp;Vuid;Vhwcap;Vdraw;A7").

Lemma ms0_mem_def : ltac2:(tb__ "0|6|
S24Q40M0A1S0S19S24Q8M1A1M2A1M3S63S29R1A2G3G3Lx;Sa8Vsp;VESI;R1A3G2S1aG2R1A2Lb;S16G3L_;S20S10SfS25G0Vsp;A2M4S8cA2S25G0R1A2M5A2S14G5G4A2A2S1aG2S26G1Z0A2A2S1fG2A1X16x2X19x2A3Fa;").
Proof using . reflexivity. Qed.

Lemma ESI_eq : ltac2:(tb__ "0|1|
S0S17S24Q8A1M0A1VESI;S21G0VBSB;S94Vsp;VBSB;Sa7Vdraw;A1A3A3A3").
Proof using . reflexivity. Qed.

Lemma ms0_mem_img : ltac2:(tb__ "0|2|
S4S1S8Z0R1A2SaR1VLEN;A2A2S0S19S24Q8A1M0A1S63S29S26Q40M1S7S25G1Vsp;A2R2A2A2A2S77G0VBSB;S13R2A1A3A3F_;Foff;").
Proof using Hinp Hsp.
  intros off Hoff. rewrite ms0_mem_def.
  pose proof sp_bound as [Hs _]. rewrite sp_hi_val, sp_lo_val in Hs. pose proof LEN_bound.
  pose proof length_BSB as HL.
  subst ESI BSB. rewrite (stack_to_mem_image_in_block ph sp argv envp uid hwcap draw).
  2:{ unfold entry_block_top. rewrite Z_to_bv_small by (change (bv_modulus 64) with (2 ^ 64); lia).
      unfold bsb in HL. lia. }
  unfold stack_to_mem.
  rewrite Z_to_bv_small by (change (bv_modulus 64) with (2 ^ 64); lia).
  replace (bv_unsigned sp <=? bv_unsigned sp + off) with true by (symmetry; apply Z.leb_le; lia).
  replace (bv_unsigned sp + off - bv_unsigned sp) with off by lia.
  unfold bsb in HL |- *.
  match goal with |- context [off <? Z.of_nat (length ?B)] =>
    replace (off <? Z.of_nat (length B)) with true by (symmetry; apply Z.ltb_lt; lia);
    destruct (nth_error B (Z.to_nat off)) as [b|] eqn:E; [reflexivity|];
    apply nth_error_None in E; lia
  end.
Qed.

Lemma ms0_mem_region : ltac2:(tb__ "0|3|
S1bS17S24Q8M0A1M1A1S1bS71Vph;Vsp;Vargv;Venvp;Vuid;Vhwcap;Vdraw;R3R2A9S69R2S18G1R3A2A2S0S19G1A1S63S29S26Q40M2S7S25G2Vsp;A2S7S9R5A1S9R3A1A2A2A2A2S1aG1S61G1R3R4S26G0Z0A2A4A2A3F_;F_;Fj;Fseg;Fo;").
Proof using Hinp Hsp.
  intros o seg j Hr Hj.
  assert (Hlen : (o + length seg <= length BSB)%nat).
  { destruct Hr as (pre & post & E & L). subst BSB. rewrite E, !length_app. lia. }
  pose proof length_BSB.
  rewrite ms0_mem_img by lia.
  replace (Z.to_nat (Z.of_nat o + Z.of_nat j)) with (o + j)%nat by lia.
  subst BSB. rewrite (region_nth ph sp argv envp uid hwcap draw o seg j Hr Hj).
  apply nth_error_nth'. exact Hj.
Qed.

Lemma ms0_mem_below : ltac2:(tb__ "0|5|
S24Q40M0A1S1S8SfS25G0Vsp;A2M1S8cA2S25G0R1A2M2A2SaG2G1A2A2S0S19S24Q8M3A1M4A1S63S29R2A2S1aG4S26G3Z0A2A2A3F_;Fa;").
Proof using .
  intros a Ha. rewrite ms0_mem_def. unfold stack_to_mem.
  replace (bv_unsigned sp <=? bv_unsigned a) with false by (symmetry; apply Z.leb_gt; lia).
  replace (bv_unsigned sp - stack_max_size <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; lia).
  replace (bv_unsigned a <? bv_unsigned sp) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma ms0_mem_low : ltac2:(tb__ "0|2|
S24Q40M0A1SaS25G0R1A2SfS25G0Vsp;A2S8cA2A2S0S19S24Q8A1M1A1S63S29R2A2S1fG1A1A3F_;Fa;").
Proof using .
  intros a Ha. rewrite ms0_mem_def. unfold stack_to_mem.
  replace (bv_unsigned sp <=? bv_unsigned a) with false by (symmetry; apply Z.leb_gt; pose proof stack_max_size_val; lia).
  replace (bv_unsigned sp - stack_max_size <=? bv_unsigned a) with false by (symmetry; apply Z.leb_gt; lia).
  reflexivity.
Qed.

Lemma rd_of_mem : ltac2:(tb__ "0|2|
S24Q40A1S24Q8A1M0S0S19G0A1M1S63S29R2A2S1aG0R1A2A3S0G1S46S29R3A2S1aG0R2A2A3F_;Fb;Fa;").
Proof using . intros a b H. unfold rd, ms_read_byte. rewrite H. reflexivity. Qed.

Lemma wview_of_mem : ltac2:(tb__ "0|2|
S24Q40A1S24Q8A1M0S0S19G0A1M1S63S29R2A2S1aG0R1A2A3S3S0G1S66Vsegs;S63S29A1R3A3S1fG0A1A3A1F_;Fb;Fa;").
Proof using . intros a b H. unfold wview. rewrite H. discriminate. Qed.

Lemma rd_bytes_of : ltac2:(tb__ "0|5|
S1bS4S17S24Q8M0A1M1A1M2S0S1bS18G1R1A2R3A3S8Z0M3R3A2S8S7R4S9R5A1A2SdZ2Z40A2A2S1bS69R1R7A2S0S19G1A1S46S29S26Q40M4S7R7S9R2A1A2A2A2S1aG1S61G1R2R6S26G0G3A2A4A2A3F_;Fj;S0S19G2A1S47S29S26G4R6A2R7A3S1aG2R5A2A3F_;F_;F_;F_;Fl;Fa;Fk;").
Proof using .
  induction k as [|k IH]; intros a l Hl Ha Hk H.
  - destruct l; [reflexivity|discriminate].
  - destruct l as [|b l]; [discriminate|]. cbn [rd_bytes].
    pose proof (H 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0. cbn [nth] in H0. rewrite H0.
    replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
    2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned 1%bv) with 1.
        unfold bv_wrap. rewrite <- Zplus_mod_idemp_l. reflexivity. }
    rewrite (IH (a + 1) l); [reflexivity| cbn in Hl; lia | lia | lia |].
    intros j Hj. replace (a + 1 + Z.of_nat j) with (a + Z.of_nat (S j)) by lia.
    rewrite (H (S j)) by lia. reflexivity.
Qed.

Lemma nums : ltac2:(tb__ "0|9|
S1S1S8Z7fff80000000S25Q40Vsp;A2M0A2S8G0Z800000000000A2A2S1S0S4SeG0Z10M1A2Z0M2A3S1S1S8Z1M3VARGC;A2S8VARGC;Z400A2A2S1S1S8G2VENVC;A2S8VENVC;Z100A2A2S1S0S4VSTR;S7S7Zb8SbZ8M4VARGC;A2A2SbG4VENVC;A2A2A3S1S8S7S9S18S24Q8A1Vargv0;A2A1M5G3A2S9S6fVargv;A1A1M6A2S1S8G5Z1ffffA2S1S0S4VRND;S7S7S7VSTR;G6A2S9S6fVenvp;A1A1M7A2S9S70Vargv;Venvp;A2A1M8A2A3S1SaG8G4A2S1S8G6Z200000A2S1S8G7Z20000A2S1S0S4VLEN;S7VRND;G1A2A3S1S0S4SeVRND;G4A2G2A3S0S4SeVSTR;G4A2G2A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using Hinp Hsp.
  pose proof sp_bound as [A B]. rewrite sp_lo_val, sp_hi_val in A.
  pose proof ARGC_bound. pose proof ENVC_bound. pose proof STR_eq. pose proof len0_tab. pose proof len0_bound.
  pose proof RND_eq. pose proof pad_lt8. pose proof tab_argv_bound. pose proof tab_envp_bound. pose proof LEN_eq.
  pose proof (rand_off_mod8 argv envp). pose proof (str_off_mod8 argv envp).
  subst RND STR. repeat split; try lia.
Qed.

Ltac nums := pose proof nums; rewrite ?pow64, ?pow63 in *.

Lemma rw1 : rw rho0 1 = sp. Proof using . reflexivity. Qed.
Lemma rw2 : ltac2:(tb__ "0|1|
S0S24Q40M0A1S3aS28P2A2S26G0VARGC;A2A3"). Proof using . reflexivity. Qed.
Lemma rw3 : ltac2:(tb__ "0|1|
S0S24Q40M0A1S3aS28P3A2S26G0VENVC;A2A3"). Proof using . reflexivity. Qed.
Lemma rw4 : ltac2:(tb__ "0|1|
S0S24Q40M0A1S3aS28P4A2S26G0S7S25G0Vsp;A2VSTR;A2A2A3"). Proof using . reflexivity. Qed.
Lemma rw5 : ltac2:(tb__ "0|1|
S0S24Q40M0A1S3aS28P5A2S26G0S9S18S24Q8A1Vargv0;A2A1A2A3"). Proof using . reflexivity. Qed.
Lemma rw6 : ltac2:(tb__ "0|1|
S0S24Q40M0A1S3aS28P6A2S26G0S7S25G0Vsp;A2VRND;A2A2A3"). Proof using . reflexivity. Qed.

Lemma U_var : ltac2:(tb__ "0|1|
S6S0S4S25Q40M0S31S28S30R1A1A2A2S25G0S3aS28R1A2A2A3Fi;").
Proof using . reflexivity. Qed.

Lemma U_lit : ltac2:(tb__ "0|0|
S4S1S8Z0R1A2SaR1SdZ2Z40A2A2A2S0S4S25Q40S31S28S2eR2A1A2A2R2A3F_;Fz;").
Proof using . intros z Hz. cbn [eval]. apply Z_to_bv_small. rewrite mod64. exact Hz. Qed.

Lemma U_v1 : ltac2:(tb__ "0|1|
S0S4S25Q40M0S31S28S30P1A1A2A2S25G0Vsp;A2A3").
Proof using . reflexivity. Qed.
Lemma U_v2 : ltac2:(tb__ "0|0|
S0S4S25Q40S31S28S30P2A1A2A2VARGC;A3").
Proof using Hinp Hsp. cbn. apply Z_to_bv_small. rewrite mod64. nums. lia. Qed.
Lemma U_v3 : ltac2:(tb__ "0|0|
S0S4S25Q40S31S28S30P3A1A2A2VENVC;A3").
Proof using Hinp Hsp. cbn. apply Z_to_bv_small. rewrite mod64. nums. lia. Qed.
Lemma U_v4 : ltac2:(tb__ "0|1|
S0S4S25Q40M0S31S28S30P4A1A2A2S7S25G0Vsp;A2VSTR;A2A3").
Proof using Hinp Hsp. cbn. apply Z_to_bv_small. rewrite mod64. nums. lia. Qed.
Lemma U_v5 : ltac2:(tb__ "0|0|
S0S4S25Q40S31S28S30P5A1A2A2S9S18S24Q8A1Vargv0;A2A1A3").
Proof using Hinp Hsp. cbn. apply Z_to_bv_small. rewrite mod64. nums. lia. Qed.
Lemma U_v6 : ltac2:(tb__ "0|1|
S0S4S25Q40M0S31S28S30P6A1A2A2S7S25G0Vsp;A2VRND;A2A3").
Proof using Hinp Hsp. cbn. apply Z_to_bv_small. rewrite mod64. nums. lia. Qed.

Lemma U_sll3 : ltac2:(tb__ "0|1|
S6S4S0S4S25Q40M0S31S28S30R2A1A2A2R1A3S1S8Z0R2A2SaR2SdZ2Z32A2A2A2S0S4S25G0S31S28S78R4A1A2A2SbZ8R3A2A3F_;F_;Fx;Fi;").
Proof using .
  intros i x Hx Hr. unfold sll3. cbn [eval]. rewrite sll_val. change (3 mod 64) with 3.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  change (eval rho0 (SVar i)) with (rw rho0 i) in Hx |- *. cbn [eval] in Hx. rewrite Hx.
  rewrite Z.mod_small; [lia|]. rewrite pow64. lia.
Qed.

Lemma U_add : ltac2:(tb__ "0|3|
S2fS2fS4S4S0S4S25Q40M0S31S28R4A2A2R2A3M1G1S8Z0R4A2M2G2SaS7R6R5A2SdZ2Z40A2A2S0S4S25G0S31S28S34S6bR9R8A3A2A2S7R7R6A2A3F_;F_;F_;F_;F_;Fy;Fx;Fb;Fa;").
Proof using .
  intros a b x y Hx Hy H1 H2 H3. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Hx, Hy.
  unfold bv_wrap. rewrite mod64. apply Z.mod_small. lia.
Qed.

Lemma U_env_base : ltac2:(tb__ "0|1|
S0S4S25Q40M0S31S28S84A2A2S7S7S25G0Vsp;A2SbZ8VARGC;A2A2Z10A2A3").
Proof using Hinp Hsp.
  nums. unfold env_base.
  erewrite U_add; [reflexivity| | apply U_lit; lia | | |lia]; try lia.
  erewrite U_add; [reflexivity| apply U_v1 | apply (U_sll3 2 ARGC U_v2); lia | | |]; lia.
Qed.

Lemma U_aux_base : ltac2:(tb__ "0|2|
S0S4S25Q40M0S31S28S83A2A2S7S7S7S25G0Vsp;A2SbZ8M1VARGC;A2A2SbG1VENVC;A2A2Z18A2A3").
Proof using Hinp Hsp.
  nums. unfold aux_base.
  erewrite U_add; [reflexivity| | apply U_lit; lia | | |lia]; try lia.
  erewrite U_add; [reflexivity| | apply (U_sll3 3 ENVC U_v3); lia | | |]; try lia.
  erewrite U_add; [reflexivity| apply U_v1 | apply (U_sll3 2 ARGC U_v2); lia | | |]; lia.
Qed.

Lemma soff_small : ltac2:(tb__ "0|0|
S2fS4S0S4S25Q40S31S28R2A2A2R1A3SaR2SdZ2Z3fA2A2S0S4S48S28R4A2R3A3F_;F_;Fx;Fe;").
Proof using .
  intros e x Hx Hr. rewrite soff_snorm. unfold U. rewrite Hx. pose proof (urange (eval rho0 e)).
  apply snorm_id. unfold smin, smax. lia.
Qed.

Lemma soff_lit' : ltac2:(tb__ "0|1|
S4S1S8S11SdZ2Z3fA2M0A1R1A2SaR1G0A2A2S0S4S48S28S2eR2A1A2R2A3F_;Fz;").
Proof using . intros z Hz. rewrite soff_lit. apply snorm_id'. exact Hz. Qed.

Lemma rd_word_region : ltac2:(tb__ "0|6|
S1bS17S24Q40M0A1M1A1S1bS71Vph;Vsp;Vargv;Venvp;Vuid;Vhwcap;Vdraw;R3S76G1S24Q8A1M2S6dR2A4A9S69R2S18G1R3A2A2S8S7S9R5A1SbZ8M3S9S18G1R4A2A1A2A2VLEN;A2S0S19S17G2A1M4A1S47S29S26G0S7S7S25G0Vsp;A2S9R6A1A2SbG3S9R4A1A2A2A2U8M5A3S1aG4S42G5S61G1R4R5S26G0Z0A2A4A2A2A3F_;F_;F_;Fk;Fws;Fo;").
Proof using Hinp Hsp.
  intros o ws k Hr Hk Hlen. nums. pose proof LEN_bound.
  apply rd_bytes_of; [apply enc_bytes_length | lia | lia |].
  intros j Hj. rewrite <- word_le8_enc.
  replace (bv_unsigned sp + Z.of_nat o + 8 * Z.of_nat k + Z.of_nat j)
    with (bv_unsigned sp + (Z.of_nat o + Z.of_nat (8 * k + j))) by lia.
  apply rd_of_mem. rewrite (ms0_mem_region o (flat_map word_le8 ws) (8 * k + j) Hr)
    by (rewrite length_flat_map_le8; lia).
  f_equal. apply nth_flat_map_le8; assumption.
Qed.

Lemma cells_from_hold : ltac2:(tb__ "0|5|
S2fS4S1bS17S24Q40M0A1M1A1S17S2fA1S1bS4S4S4S0S4S25G0S31S28R9A2A2R8A3S71Vph;Vsp;Vargv;Venvp;Vuid;Vhwcap;Vdraw;R8S76G1S24Q8A1S6dR7A4A9S8S7S9R9A1SbZ8M2S9S18G1R8A2A1A2A2VLEN;A2S1bS69R1S18S2fR9A2A2S1S69S8aR9R2A2M3S18G1RbA2A2S0G1S31S28S61S2fR2RaS2eZ0M4A1A4A2S61G1G3RbS26G0G4A2A4A3A2F_;Fi;S0S4S7RcR7A2S7S7S25G0Vsp;A2S9RbA1A2SbG2S9R8A1A2A2A3S8R7R8A2S8G4R9A2S8S7RaSbG2S9S18S2fRcA2A1A2A2R8A2SaR9SdZ2Z3eA2A2S62S33S41S28R12RbRaS29A5S88RcReA2A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fhi;Flo;Foff;Fk0;Fsvs;Fws;Fo;Fb;Fbase;").
Proof using Hinp Hsp.
  intros base b o ws svs. induction svs as [|e svs IH]; intros k0 off lo hi Hb Hr Hlen HF Hoff Hlo H0 Hhi Hhi2; [constructor|].
  cbn [cells_from]. cbn [length] in Hhi.
  assert (Hb0 : 0 <= b) by (rewrite <- Hb; apply (proj1 (urange _))).
  nums.
  constructor.
  - destruct (HF 0%nat ltac:(cbn; lia)) as [Hk He]. cbn [nth] in He. rewrite Nat.add_0_r in Hk, He.
    unfold cell_holds, cell8. cbn [c_off c_width c_val].
    rewrite (soff_lit' off) by lia. split; [lia|]. split; [lia|].
    unfold oaddr. rewrite Hb, He. change (Z.to_nat 8) with 8%nat.
    rewrite Hoff. apply rd_word_region; [exact Hr | exact Hk | exact Hlen].
  - apply (IH (S k0) (off + 8) lo hi Hb Hr Hlen); try lia.
    intros i Hi. destruct (HF (S i) ltac:(cbn; lia)) as [Hk He]. cbn [nth] in He.
    replace (S k0 + i)%nat with (k0 + S i)%nat by lia. auto.
Qed.

Lemma ms0_mem_img_some : ltac2:(tb__ "0|2|
S4S1S8Z0R1A2SaR1VLEN;A2A2S2S24Q8A1M0G0S0S19G0A1S63S29S26Q40M1S7S25G1Vsp;A2R3A2A2A2S1aG0R1A2A3Lb;A2F_;Foff;").
Proof using Hinp Hsp.
  intros off Hoff. rewrite ms0_mem_img by exact Hoff.
  destruct (nth_error BSB (Z.to_nat off)) as [b|] eqn:E; [exists b; reflexivity|].
  apply nth_error_None in E. pose proof length_BSB. lia.
Qed.

Lemma O_stk_holds : ltac2:(tb__ "0|0|
S37Vsegs;S28S29S81A4").
Proof using Hinp Hsp.
  nums. pose proof stack_max_size_val.
  apply (obj_holds_of segs rho0 ms0 O_stk (bv_unsigned sp) (- STK_FREE) 0); cbn [ob_base ob_lo ob_hi ob_cells ob_dflt O_stk].
  - apply U_v1.
  - apply soff_lit'. unfold STK_FREE. lia.
  - apply soff_lit'. lia.
  - unfold STK_FREE. lia.
  - intros off Hoff _. unfold STK_FREE in Hoff.
    eapply wview_of_mem. apply ms0_mem_below. rewrite U_addr by lia. lia.
  - constructor.
  - intros off Hoff _. unfold STK_FREE in Hoff. cbn [dflt_holds].
    apply rd_of_mem. apply ms0_mem_below. rewrite U_addr by lia. lia.
  - exact I.
Qed.

Lemma hdr_bytes_flat : ltac2:(tb__ "0|4|
S0S17S24Q8A1M0A1M1S75Vsp;Vargv;Venvp;A3S76S24Q40M2A1M3G0S6dS15G3S6eG1Vargv;A2S21G3S72Vsp;Vargv;Venvp;A3S15G3S26G2Z0A2S1cG3A1A3A3A3A4A3").
Proof using inp.
  unfold hdr_bytes. cbn [flat_map]. rewrite flat_map_app. cbn [flat_map]. rewrite app_nil_r. reflexivity.
Qed.

Lemma argv_ptr0 : ltac2:(tb__ "0|2|
S0S24Q40M0A1M1S61G1U0S72Vsp;Vargv;Venvp;A3S26G0Z0A2A4S26G0S7S25G0Vsp;A2VSTR;A2A2A3").
Proof using ARGC ENVC Hinp Hsp LEN RND argv0.
  nums. unfold argv_ptrs. rewrite string_addrs_nth by (unfold ARGC in *; lia).
  cbn [firstn tab]. rewrite Z.add_0_r. unfold str_base, nat_to_word. subst STR.
  apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. rewrite mod64.
  rewrite Z.mod_mod by lia. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma O_hdr_holds : ltac2:(tb__ "0|0|
S37Vsegs;S28S29S7fA4").
Proof using Hinp Hsp.
  nums. pose proof LEN_bound.
  apply (obj_holds_of segs rho0 ms0 O_hdr (bv_unsigned sp) 0 16); cbn [ob_base ob_lo ob_hi ob_cells ob_dflt O_hdr].
  - apply U_v1.
  - apply soff_lit'. lia.
  - apply soff_lit'. lia.
  - lia.
  - intros off Hoff _. destruct (ms0_mem_img_some off ltac:(lia)) as [b Hb]. eapply wview_of_mem. exact Hb.
  - change [cell8 0 (SVar 2); cell8 8 (SVar 4)] with (cells_from 0 [SVar 2; SVar 4]).
    apply (cells_from_hold (SVar 1) (bv_unsigned sp) 0 (len_word argv :: argv_ptrs sp argv envp ++ [Z_to_bv 64 0]) _ 0);
      cbn [length]; try lia.
    + apply U_v1.
    + rewrite <- hdr_bytes_flat. apply region_hdr.
    + rewrite length_app. unfold argv_ptrs. rewrite string_addrs_fst_length. cbn [length]. subst ARGC. lia.
    + intros i Hi. destruct i as [|[|i]]; [| |lia]; cbn [nth Nat.add].
      * split; [lia|]. cbn [eval]. rewrite rw2. unfold len_word. subst ARGC. reflexivity.
      * split.
        { rewrite length_app. unfold argv_ptrs. rewrite string_addrs_fst_length. cbn [length]. subst ARGC. lia. }
        cbn [eval]. rewrite rw4. rewrite app_nth1 by (unfold argv_ptrs; rewrite string_addrs_fst_length; unfold ARGC in *; lia).
        symmetry. apply argv_ptr0.
  - intros off Hoff _. cbn [dflt_holds]. destruct (ms0_mem_img_some off ltac:(lia)) as [b Hb].
    exists b. apply rd_of_mem. exact Hb.
  - exact I.
Qed.

Lemma O_env_holds : ltac2:(tb__ "0|0|
S37Vsegs;S28S29S7bA4").
Proof using Hinp Hsp.
  nums. pose proof LEN_bound.
  apply (obj_holds_of segs rho0 ms0 O_env (bv_unsigned sp + 8 * ARGC + 16) 0 (8 * ENVC + 8)); cbn [ob_base ob_lo ob_hi ob_cells ob_dflt O_env].
  - apply U_env_base.
  - apply soff_lit'. lia.
  - unfold obj_hi_of. cbn [ob_hi O_env]. apply soff_small; [|lia].
    erewrite U_add; [reflexivity | apply (U_sll3 3 ENVC U_v3); lia | apply U_lit; lia | | |]; lia.
  - lia.
  - intros off Hoff _.
    destruct (ms0_mem_img_some (8 * ARGC + 16 + off) ltac:(lia)) as [b Hb].
    replace (bv_unsigned sp + 8 * ARGC + 16 + off) with (bv_unsigned sp + (8 * ARGC + 16 + off)) by lia.
    eapply wview_of_mem. exact Hb.
  - constructor.
  - intros off Hoff _. cbn [dflt_holds rl rho0]. rewrite Pos.eqb_refl. rewrite Z.sub_0_r.
    apply rd_of_mem.
    replace (bv_unsigned sp + 8 * ARGC + 16 + off) with (bv_unsigned sp + (Z.of_nat (16 + 8 * argc argv) + Z.of_nat (Z.to_nat off)))
      by (unfold argc; unfold ARGC in *; lia).
    rewrite (ms0_mem_region (16 + 8 * argc argv) (env_bytes sp argv envp) (Z.to_nat off) (region_env ph sp argv envp uid hwcap draw)).
    + reflexivity.
    + rewrite length_env_bytes. unfold envc. subst ENVC. lia.
  - cbn [dflt_inv rl rho0]. rewrite Pos.eqb_refl. rewrite length_env_bytes. unfold envc. subst ENVC. lia.
Qed.

Definition auxv_ws (r : word) : list word := ltac2:(tb__ "0|3|
S15S24Q40M0A1M1S9eS15G1S26G0ScS5bVph;A1A1A2S15G1S9fS15G1S26G0ScS5cVph;A1A1A2S15G1Sa0S15G1S26G0ScS5dVph;A1A1A2S15G1S9bS15G1Vhwcap;S15G1S9dS15G1S26G0Z1000A2S15G1Sa3S15G1Vuid;S15G1S9aS15G1Vuid;S15G1Sa2S15G1S26G0Z0A2M2S15G1Sa1S15G1Vr;S15G1S9cS15G1G2S1cG1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Lemma auxv_flat : ltac2:(tb__ "0|2|
S24Q40A1M0S0S17S24Q8A1M1A1Sa6Vph;R1Vuid;Vhwcap;A4S76G0G1S6dS2aR1A1A4A3Fr;").
Proof using .
  intros r. unfold auxv_bytes, build_auxv, auxv_entries, auxv_ws. cbn [flat_map fst snd].
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma rand_ptr_eq : ltac2:(tb__ "0|1|
S0S24Q40M0A1Sa5Vsp;Vargv;Venvp;A3S26G0S7S25G0Vsp;A2VRND;A2A2A3").
Proof using inp.
  rewrite at_random_ptr_eq. unfold nat_to_word. subst RND.
  apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite mod64.
  rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma O_aux_holds : ltac2:(tb__ "0|0|
S37Vsegs;S28S29S7dVph;A1A4").
Proof using Hinp Hsp.
  nums. pose proof LEN_bound.
  apply (obj_holds_of segs rho0 ms0 (O_aux ph) (bv_unsigned sp + 8 * ARGC + 8 * ENVC + 24) 0 160); cbn [ob_base ob_lo ob_hi ob_cells ob_dflt O_aux].
  - apply U_aux_base.
  - apply soff_lit'. lia.
  - apply soff_lit'. lia.
  - lia.
  - intros off Hoff _.
    destruct (ms0_mem_img_some (8 * ARGC + 8 * ENVC + 24 + off) ltac:(lia)) as [b Hb].
    replace (bv_unsigned sp + 8 * ARGC + 8 * ENVC + 24 + off) with (bv_unsigned sp + (8 * ARGC + 8 * ENVC + 24 + off)) by lia.
    eapply wview_of_mem. exact Hb.
  - apply (cells_from_hold aux_base (bv_unsigned sp + 8 * ARGC + 8 * ENVC + 24) (aux_off argv envp)
             (auxv_ws (at_random_ptr sp argv envp)) _ 0); cbn [length auxv_ws]; try lia.
    + apply U_aux_base.
    + rewrite <- auxv_flat. apply region_auxv.
    + unfold aux_off, argc, envc. subst ARGC ENVC. lia.
    + intros i Hi. cbn [length aux_svs] in Hi. split; [lia|]. rewrite Nat.add_0_l.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]; try lia; try reflexivity.
      cbn [nth auxv_ws aux_svs eval]. rewrite rw6. symmetry. apply rand_ptr_eq.
    + unfold aux_off, argc, envc. subst ARGC ENVC. lia.
    + cbn [length aux_svs]. lia.
  - intros off Hoff _. cbn [dflt_holds].
    destruct (ms0_mem_img_some (8 * ARGC + 8 * ENVC + 24 + off) ltac:(lia)) as [b Hb].
    replace (bv_unsigned sp + 8 * ARGC + 8 * ENVC + 24 + off) with (bv_unsigned sp + (8 * ARGC + 8 * ENVC + 24 + off)) by lia.
    exists b. apply rd_of_mem. exact Hb.
  - exact I.
Qed.

Lemma O_str0_holds : ltac2:(tb__ "0|0|
S37Vsegs;S28S29S7cA4").
Proof using Hinp Hsp.
  nums. pose proof LEN_bound.
  apply (obj_holds_of segs rho0 ms0 O_str0 (bv_unsigned sp + STR) 0 (Z.of_nat (length argv0) + 1)); cbn [ob_base ob_lo ob_hi ob_cells ob_dflt O_str0].
  - apply U_v4.
  - apply soff_lit'. lia.
  - unfold obj_hi_of. cbn [ob_hi O_str0]. apply soff_small; [|lia].
    erewrite U_add; [reflexivity | apply U_v5 | apply U_lit; lia | | |]; lia.
  - lia.
  - intros off Hoff _.
    destruct (ms0_mem_img_some (STR + off) ltac:(lia)) as [b Hb].
    replace (bv_unsigned sp + STR + off) with (bv_unsigned sp + (STR + off)) by lia.
    eapply wview_of_mem. exact Hb.
  - constructor.
  - intros off Hoff _. cbn [dflt_holds rl rho0]. change (2 =? 1)%positive with false. rewrite Pos.eqb_refl. cbn [negb]. rewrite Z.sub_0_r.
    apply rd_of_mem.
    replace (bv_unsigned sp + STR + off) with (bv_unsigned sp + (Z.of_nat (str_off argv envp + tab (firstn 0 argv)) + Z.of_nat (Z.to_nat off)))
      by (cbn [firstn tab]; rewrite Nat.add_0_r; subst STR; lia).
    unfold argv0 in *. rewrite (ms0_mem_region _ (nth 0 argv [] ++ [Z_to_bv 8 0]) (Z.to_nat off) (region_argv_str ph sp argv envp uid hwcap draw 0 ltac:(unfold argc; unfold ARGC in *; lia))).
    + reflexivity.
    + rewrite length_app. cbn [length]. lia.
  - cbn [dflt_inv rl rho0]. change (2 =? 1)%positive with false. rewrite Pos.eqb_refl. cbn [negb].
    rewrite length_app. cbn [length]. lia.
Qed.

Lemma O_rand_holds : ltac2:(tb__ "0|0|
S37Vsegs;S28S29S80A4").
Proof using Hinp Hsp.
  nums. pose proof LEN_bound.
  apply (obj_holds_of segs rho0 ms0 O_rand (bv_unsigned sp + RND) 0 16); cbn [ob_base ob_lo ob_hi ob_cells ob_dflt O_rand].
  - apply U_v6.
  - apply soff_lit'. lia.
  - apply soff_lit'. lia.
  - lia.
  - intros off Hoff _.
    destruct (ms0_mem_img_some (RND + off) ltac:(lia)) as [b Hb].
    replace (bv_unsigned sp + RND + off) with (bv_unsigned sp + (RND + off)) by lia.
    eapply wview_of_mem. exact Hb.
  - change [cell8 0 (SVar 9); cell8 8 (SVar 10)] with (cells_from 0 [SVar 9; SVar 10]).
    apply (cells_from_hold (SVar 6) (bv_unsigned sp + RND) (rand_off argv envp) [rnd0; rnd1] _ 0);
      cbn [length]; try lia.
    + apply U_v6.
    + pose proof (region_rand ph sp argv envp uid hwcap draw) as Hr.
      unfold rand_bytes in Hr. rewrite at_random_bytes_words in Hr. exact Hr.
    + intros i Hi. destruct i as [|[|i]]; [| |lia]; cbn [nth Nat.add]; (split; [lia|reflexivity]).
  - intros off Hoff _. cbn [dflt_holds].
    destruct (ms0_mem_img_some (RND + off) ltac:(lia)) as [b Hb].
    replace (bv_unsigned sp + RND + off) with (bv_unsigned sp + (RND + off)) by lia.
    exists b. apply rd_of_mem. exact Hb.
  - exact I.
Qed.

Lemma O_data_holds : ltac2:(tb__ "0|0|
S37Vsegs;S28S29S7eVdata_lo;Vdata_hi;A2A4").
Proof using Hdata Hdata_hi Hinp Hsp.
  nums. pose proof stack_max_size_val.
  pose proof Hdata as Hd. unfold data_ok_b in Hd. apply andb_prop in Hd as [Hd _]. apply andb_prop in Hd as [Hd1 Hd2].
  apply Z.leb_le in Hd1. apply Z.leb_le in Hd2.
  apply (obj_holds_of segs rho0 ms0 (O_data data_lo data_hi) 0 data_lo data_hi); cbn [ob_base ob_lo ob_hi ob_cells ob_dflt O_data].
  - apply U_lit. lia.
  - apply soff_lit'. lia.
  - apply soff_lit'. lia.
  - lia.
  - intros off Hoff _. rewrite Z.add_0_l.
    destruct (data_ok_b_spec segs data_lo data_hi off Hdata Hoff) as [_ (seg & b & Hf & Hw & Hb)].
    unfold wview. rewrite ms0_mem_low by (rewrite U_addr by lia; lia).
    rewrite U_addr by lia. rewrite Hf, Hw, Hb. discriminate.
  - constructor.
  - intros off Hoff _. cbn [dflt_holds]. rewrite Z.add_0_l. split.
    + apply ms0_mem_low. rewrite U_addr by lia. lia.
    + exact (proj1 (data_ok_b_spec segs data_lo data_hi off Hdata Hoff)).
  - exact I.
Qed.

Lemma obj_range_of : ltac2:(tb__ "0|0|
S36S4S4S4S0S4S25Q40S31S28S3eR4A1A2A2R3A3S0S4S45S28R5A2R3A3S0S4S3bS28R6A2R3A3S0S22S4S4A2S38S28R7A2S1dS4S4S7R6R5A2S7R6R4A2A4A3F_;F_;F_;Fhi;Flo;Fb;Fo;").
Proof using . intros o b lo hi Hb Hlo Hhi. unfold obj_range. rewrite Hb. unfold obj_lo_of, obj_hi_of in *. rewrite Hlo, Hhi. reflexivity. Qed.

Lemma hi_env : ltac2:(tb__ "0|1|
S0S4S3bS28S7bA2S7SbZ8M0VENVC;A2G0A2A3").
Proof using Hinp Hsp.
  nums. unfold obj_hi_of. cbn [ob_hi O_env]. apply soff_small; [|lia].
  erewrite U_add; [reflexivity | apply (U_sll3 3 ENVC U_v3); lia | apply U_lit; lia | | |]; lia.
Qed.

Lemma hi_str0 : ltac2:(tb__ "0|0|
S0S4S3bS28S7cA2S7S9S18S24Q8A1Vargv0;A2A1Z1A2A3").
Proof using Hinp Hsp.
  nums. unfold obj_hi_of. cbn [ob_hi O_str0]. apply soff_small; [|lia].
  erewrite U_add; [reflexivity | apply U_v5 | apply U_lit; lia | | |]; lia.
Qed.

Lemma data_lo_hi : 0 <= data_lo <= data_hi.
Proof using ARGC ENVC Hdata LEN RND STR.
  pose proof Hdata as Hd. unfold data_ok_b in Hd. apply andb_prop in Hd as [Hd _]. apply andb_prop in Hd as [Hd1 Hd2].
  apply Z.leb_le in Hd1. apply Z.leb_le in Hd2. lia.
Qed.

Lemma ranges0 : ltac2:(tb__ "0|c|
S1S0S22S4S4A2M0S38S28S81A2S1dS4S4S7S25Q40Vsp;A2M1S11S82A1A2S7G1Z0M2A2M3A4A3S1S0G0S38S28S7fA2S1dS4S4G3S7G1Z10M4A2A4A3S1S0G0S38S28S7bA2S1dS4S4S7S7S7G1SbZ8M5VARGC;A2A2M6G4A2M7G2A2S7G7S7SbG5VENVC;A2M8G5A2A2A4A3S1S0G0S38S28S7dVph;A1A2S1dS4S4S7S7S7G6G8A2Z18A2M9G2A2S7G9Za0A2A4A3S1S0G0S38S28S7cA2S1dS4S4S7S7G1VSTR;A2MaG2A2S7GaS7S9S18S24Q8A1Vargv0;A2A1Z1A2A2A4A3S1S0G0S38S28S80A2S1dS4S4S7S7G1VRND;A2MbG2A2S7GbG4A2A4A3S0G0S38S28S7eVdata_lo;Vdata_hi;A2A2S1dS4S4S7G2Vdata_lo;A2S7G2Vdata_hi;A2A4A3A2A2A2A2A2A2").
Proof using Hdata Hdata_hi Hinp Hsp.
  nums. pose proof data_lo_hi.
  split. { apply obj_range_of; [apply U_v1 | apply soff_lit'; unfold STK_FREE; lia | apply soff_lit'; lia]. }
  split. { apply obj_range_of; [apply U_v1 | apply soff_lit'; lia | apply soff_lit'; lia]. }
  split. { apply obj_range_of; [apply U_env_base | apply soff_lit'; lia | apply hi_env]. }
  split. { apply obj_range_of; [apply U_aux_base | apply soff_lit'; lia | apply soff_lit'; lia]. }
  split. { apply obj_range_of; [apply U_v4 | apply soff_lit'; lia | apply hi_str0]. }
  split. { apply obj_range_of; [apply U_v6 | apply soff_lit'; lia | apply soff_lit'; lia]. }
  apply obj_range_of; [apply U_lit; lia | apply soff_lit'; lia | apply soff_lit'; lia].
Qed.

Lemma pairwise0 : ltac2:(tb__ "0|0|
S54S28S86Vph;Vdata_lo;Vdata_hi;A3A2").
Proof using Hdata Hdata_hi Hinp Hsp.
  nums. pose proof stack_max_size_val. pose proof ranges0 as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  pose proof data_lo_hi.
  unfold objs0, pairwise_disjoint.
  repeat split; repeat (apply Forall_cons || apply Forall_nil);
    rewrite ?R1, ?R2, ?R3, ?R4, ?R5, ?R6, ?R7; unfold ranges_disjoint, STK_FREE; cbn [fst snd]; lia.
Qed.

Lemma mem_match0 : ltac2:(tb__ "0|0|
S51Vsegs;S28S86Vph;Vdata_lo;Vdata_hi;A3S29A4").
Proof using Hdata Hdata_hi Hinp Hsp.
  split; [|split].
  - repeat apply Forall_cons; [ | | | | | | | apply Forall_nil].
    + apply O_stk_holds. + apply O_hdr_holds. + apply O_env_holds. + apply O_aux_holds.
    + apply O_str0_holds. + apply O_rand_holds. + apply O_data_holds.
  - apply pairwise0.
  - intros a _. reflexivity.
Qed.

Lemma regs_match0 : ltac2:(tb__ "0|0|
S55S28S79ScVpc0;A1Vph;Vdata_lo;Vdata_hi;A4S29A3").
Proof using .
  intros r Hr. unfold reg_sv. cbn [ss_regs S0].
  pose proof (reg5_range r) as Rr.
  replace (bv_unsigned r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite nth_regs0 by lia.
  unfold ms0, init_machine_state. cbn [ms_regs]. unfold reg_get.
  destruct (Nat.eqb_spec (Z.to_nat (bv_unsigned r)) 2) as [E|E].
  - assert (r = 2%bv) as -> by (apply bv_eq; change (bv_unsigned 2%bv) with 2; lia).
    rewrite bvmap_get_set_same. reflexivity.
  - rewrite bvmap_get_set_other by (intros <-; apply E; reflexivity).
    destruct (decide (r = 10%bv)) as [->|Hne].
    + rewrite bvmap_get_set_same. reflexivity.
    + rewrite bvmap_get_set_other by (intros <-; apply Hne; reflexivity). rewrite bvmap_get_empty. reflexivity.
Qed.

Lemma fregs_match0 : ltac2:(tb__ "0|0|
S50S28S79ScVpc0;A1Vph;Vdata_lo;Vdata_hi;A4S29A3").
Proof using .
  intros r. unfold freg_sv. cbn [ss_fregs S0]. rewrite nth_fregs0.
  unfold ms0, init_machine_state. cbn [ms_fregs]. unfold reg_get. rewrite bvmap_get_empty. reflexivity.
Qed.

Lemma mod8_of16 : ltac2:(tb__ "0|2|
S4S4S0S4SeR2Z10A2Z0M0A3S0S4SeR2Z8M1A2G0A3S0S4SeS7R4R3A2G1A2G0A3F_;F_;Fb;Fa;").
Proof using ARGC ENVC LEN RND STR.
  intros a b Ha Hb.
  apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia].
  destruct Ha as [k Hk]. destruct Hb as [m Hm]. subst.
  replace (k * 16 + m * 8) with ((2 * k + m) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma facts0 : Forall (holds rho0) F0.
Proof using Hfit Hinp Hsp.
  nums. pose proof LEN_fit as LF. rewrite sp_hi_val in LF.
  unfold F0, SP_HI, STR0_END_HI, RAND_HI. rewrite sp_lo_val, sp_hi_val.
  repeat apply Forall_cons; try apply Forall_nil; cbn [holds];
    rewrite ?rw1, ?rw4, ?rw6, ?U_v1, ?U_v2, ?U_v3, ?U_v4, ?U_v5, ?U_v6; rewrite ?U_lit by lia; try lia.
  -   erewrite U_add; [ | apply U_v4 | apply U_v5 | lia | lia | lia]. lia.
  - rewrite U_addr by lia. split; [lia|]. apply mod8_of16; lia.
  - rewrite U_addr by lia. split; [lia|]. apply mod8_of16; lia.
Qed.

Lemma swf0 : ltac2:(tb__ "0|0|
S0S16S58S79ScVpc0;A1Vph;Vdata_lo;Vdata_hi;A4A1S1eA3").
Proof using . reflexivity. Qed.

Theorem init_smatch0 : ltac2:(tb__ "0|0|
S57Vsegs;S28S79ScVpc0;A1Vph;Vdata_lo;Vdata_hi;A4Sa9S2bA1A4").
Proof using Hdata Hdata_hi Hfit Hinp Hsp Htop.
  nums. pose proof stack_max_size_val.
  unfold smatch, w0. cbn [fst snd cfg_ms cfg_model c0 init_config].
  change (init_machine_state segs pc0 ph sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) with ms0.
  split; [apply swf0|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [split; reflexivity|].
  split; [intros a; reflexivity|].
  split.
  { intros a Ha. apply ms0_mem_low. pose proof (ro_addr_top segs a Ha). lia. }
  split; [apply regs_match0|].
  split; [apply fregs_match0|].
  split; [unfold fcsr_match; change (ms_fcsr ms0) with (Z_to_bv 32 0); rewrite Z_to_bv_unsigned; reflexivity|].
  split; [exact I|].
  split; [apply mem_match0|].
  apply facts0.
Qed.

End Init.
