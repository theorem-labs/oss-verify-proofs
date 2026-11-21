(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start state per CONFIG_RSEQ over the new entry-stack layout: the auxv Linux lays, 27 or 29 pairs with the gid, vDSO and exec-file-name values, cells only for the words musl reads; the launch's ProcInput in the start machine state and valuation, Jinit pinning the exec-file-name value (variable 13), which is where the argv and envp strings end; the offsets, the image's length and fit and the zero-mapped window below sp from the launch conjunct and StackBound; the start facts and object lemmas written as plain text). *)


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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require StackBound.
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
(* LPS 727298f3: three more launch values the auxv carries, numbered below [S0]'s first fresh
   variable (20), so no fresh variable of any recorded state moves: AT_GID/AT_EGID, AT_SYSINFO_EHDR
   (the vDSO text, [Run.vdso_text_base]) and AT_EXECFN ([StackLayout.at_execfn_ptr]). *)
Definition V_GID : positive := 11.
Definition V_VDSO : positive := 12.
Definition V_EXECFN : positive := 13.
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
(* CONFIG_RSEQ of the run's kernel: it alone moves the auxv's length (StackLayout.v [auxv_count]). *)
Variable rs : bool.

(* LPS 727298f3 (StackLayout.v [auxv_entries]): the auxv Linux lays, 27 pairs, 29 with CONFIG_RSEQ,
   AT_NULL last.  One entry per 8-byte word.  A word musl's [__init_libc] never reads -- the value of a
   type at or above its AUX_CNT (38): the eight cache words and AT_MINSIGSTKSZ -- has no cell ([None]).
   AT_ENTRY is the image's entry [pc0]. *)
Definition aux_svs : list (option sv) :=
  [Some (SLit 33); Some (SVar V_VDSO);
   Some (SLit 40); None; Some (SLit 41); None; Some (SLit 42); None; Some (SLit 43); None;
   Some (SLit 44); None; Some (SLit 45); None; Some (SLit 46); None; Some (SLit 47); None;
   Some (SLit 51); None;
   Some (SLit 16); Some (SVar V_HWCAP);
   Some (SLit 6); Some (SLit 4096);
   Some (SLit 17); Some (SLit 100);
   Some (SLit 3); Some (SLit (Z.of_N (ph_addr ph)));
   Some (SLit 4); Some (SLit (Z.of_N (ph_ent ph)));
   Some (SLit 5); Some (SLit (Z.of_N (ph_num ph)));
   Some (SLit 7); Some (SLit 0);
   Some (SLit 8); Some (SLit 0);
   Some (SLit 9); Some (SLit pc0);
   Some (SLit 11); Some (SVar V_UID);
   Some (SLit 12); Some (SVar V_UID);
   Some (SLit 13); Some (SVar V_GID);
   Some (SLit 14); Some (SVar V_GID);
   Some (SLit 23); Some (SLit 0);
   Some (SLit 25); Some (SVar V_RAND);
   Some (SLit 31); Some (SVar V_EXECFN)]
  ++ (if rs then [Some (SLit 27); Some (SLit 28); Some (SLit 28); Some (SLit 32)] else [])
  ++ [Some (SLit 0); Some (SLit 0)].

Fixpoint cells_from (off : Z) (l : list sv) : list cell :=
  match l with
  | [] => []
  | v :: r => cell8 off v :: cells_from (off + 8) r
  end.

Fixpoint cells_fromo (off : Z) (l : list (option sv)) : list cell :=
  match l with
  | [] => []
  | Some v :: r => cell8 off v :: cells_fromo (off + 8) r
  | None :: r => cells_fromo (off + 8) r
  end.

Definition O_stk : sobj := ltac2:(tb__ "0|0|
S39S30P1A1S2eS11S82A1A1S2eZ0A1S1cS33A1S4aA5").
Definition O_hdr : sobj := ltac2:(tb__ "0|1|
S39S30P1A1S2eZ0M0A1S2eZ10A1S15S33S7aG0S30P2A1A2S15S33S7aZ8S30P4A1A2S1cS33A1A3A3S3cA5").
Definition O_env : sobj := ltac2:(tb__ "0|0|
S39S84S2eZ0A1S34S6bS78P3A1S2eZ8A1A3S1cS33A1S40P1A1A5").
(* LPS 727298f3: [auxv_size rs] bytes (was 160, ten pairs). *)
Definition O_aux : sobj :=
  mkObj aux_base (SLit 0) (SLit (Z.of_nat (auxv_size rs))) (cells_fromo 0 aux_svs) DUnknown.
Definition O_str0 : sobj := ltac2:(tb__ "0|0|
S39S30P4A1S2eZ0A1S34S6bS30P5A1S2eZ1A1A3S1cS33A1S40P2A1A5").
Definition O_rand : sobj := ltac2:(tb__ "0|1|
S39S30P6A1S2eZ0M0A1S2eZ10A1S15S33S7aG0S30P9A1A2S15S33S7aZ8S30PaA1A2S1cS33A1A3A3S3cA5").
Definition O_data : sobj := ltac2:(tb__ "0|0|
S39S2eZ0A1S2eVdata_lo;A1S2eVdata_hi;A1S1cS33A1S49A5").

Definition objs0 : list sobj := ltac2:(tb__ "0|0|
S15S36Sb0S15S36SaeS15S36SadS15S36SabS15S36Sb1S15S36SafS15S36SacS1cS36A1A3A3A3A3A3A3A3").

Definition SP_HI : Z := sp_window_hi - 224.
(* LPS 727298f3: argv[0] ends at least the exec file name's NUL and the 8-byte slot below [ed_top]
   (was 17: the random bytes then lay above the strings). *)
Definition STR0_END_HI : Z := sp_window_hi - 10.
Definition RAND_HI : Z := sp_window_hi - 16.

(* LPS 727298f3: the strings end at [ed_top - 8] with no alignment, so argv[0]'s address [V_ARGV0]
   is no longer 8-aligned; its alignment fact is weakened to 2^0 in place, so every fact keeps its
   position. *)
Definition F0 : list sprop :=
  [SPAlign V_SP 4; SPUle (SLit sp_window_lo) (SVar V_SP); SPUle (SVar V_SP) (SLit SP_HI);
   SPUle (SLit 1) (SVar V_ARGC); SPUle (SVar V_ARGC) (SLit 1024); SPUle (SVar V_ENVC) (SLit 256);
   SPUle (SLit sp_window_lo) (SVar V_ARGV0);
   SPUle (SAlu ALU_ADD (SVar V_ARGV0) (SVar V_LEN0)) (SLit STR0_END_HI);
   SPUle (SVar V_LEN0) (SLit 131071); SPAlign V_ARGV0 0; SPAlign V_RAND 3;
   SPUle (SLit sp_window_lo) (SVar V_RAND); SPUle (SVar V_RAND) (SLit RAND_HI)].

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

Lemma auxv_size_le (b : bool) : Z.of_nat (auxv_size b) <= 464.
Proof. unfold auxv_size, auxv_count. destruct b; cbn; lia. Qed.
(* The auxv is at least its 27 pairs: [F0]'s bound on the stack pointer ([SP_HI]) rests on it. *)
Lemma auxv_size_ge (b : bool) : 432 <= Z.of_nat (auxv_size b).
Proof. unfold auxv_size, auxv_count. destruct b; cbn; lia. Qed.

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

(* LPS 75d69e00 (Run.v [init_machine_state]): the start state takes the [ProcInput] whole; argv, envp,
   uid and hwcap are read off [inp] by [entry_stack_image]. *)
Definition ms0 : machine_state := init_machine_state segs pc0 ph sp mb draw inp.
Definition c0 : config := ltac2:(tb__ "0|0|
S97Vsegs;Vpc0;Vph;Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;A9").

Lemma c0_ms : cfg_ms c0 = ms0.
Proof using . reflexivity. Qed.

Let ARGC := Z.of_nat (length argv).
Let ENVC := Z.of_nat (length envp).
(* [str_off], [rand_off] and [img_len] are Lib/InitLayout.v's, abstracted over the Section variables
   their bodies read ([inp], [sp], [draw]); each application tries the arities in turn. *)
Let STR := Z.of_nat ltac:(first [ exact (str_off inp sp draw)
                                | exact (str_off inp sp)
                                | exact (str_off inp) ]).
Let RND := Z.of_nat ltac:(first [ exact (rand_off inp)
                                | exact (rand_off inp sp draw)
                                | exact (rand_off inp sp) ]).
Let LEN := Z.of_nat ltac:(first [ exact (img_len inp sp draw)
                                | exact (img_len inp sp)
                                | exact (img_len inp) ]).
Let argv0 : list byte := nth 0 argv [].

(* [env_bytes] is Lib/InitLayout.v's, applied to [inp sp draw]. *)
Definition rho0 : valuation :=
  mkVal
    (fun i : positive =>
       if Pos.eqb i 1 then sp
       else if Pos.eqb i 2 then Z_to_bv 64 ARGC
       else if Pos.eqb i 3 then Z_to_bv 64 ENVC
       else if Pos.eqb i 4 then Z_to_bv 64 (bv_unsigned sp + STR)
       else if Pos.eqb i 5 then Z_to_bv 64 (Z.of_nat (length argv0))
       else if Pos.eqb i 6 then Z_to_bv 64 (bv_unsigned sp + RND)
       else if Pos.eqb i 7 then uid
       else if Pos.eqb i 8 then hwcap
       else if Pos.eqb i 9 then rnd0
       else if Pos.eqb i 10 then rnd1
       else if Pos.eqb i 11 then in_gid inp
       else if Pos.eqb i 12 then vdso_text_base (in_kernel inp) sp mb
       else if Pos.eqb i 13 then at_execfn_ptr (ed_top draw) (in_execfn inp)
       else Z_to_bv 64 0)
    (fun l : positive =>
       if Pos.eqb l 1 then env_bytes inp sp draw
       else if Pos.eqb l 2 then argv0 ++ [Z_to_bv 8 0]
       else [])
    (ms_mem ms0).

Record Jinit (rho : valuation) : Prop := mkJinit {
  ji_sp    : rw rho 1 = sp;
  ji_argc  : rw rho 2 = Z_to_bv 64 (Z.of_nat (length argv));
  ji_envc  : rw rho 3 = Z_to_bv 64 (Z.of_nat (length envp));
  ji_argv0 : rw rho 4 = Z_to_bv 64 (bv_unsigned sp + Z.of_nat (str_off inp sp draw));
  ji_len0  : rw rho 5 = Z_to_bv 64 (Z.of_nat (length (nth 0 argv [])));
  ji_rand  : rw rho 6 = Z_to_bv 64 (bv_unsigned sp + Z.of_nat (rand_off inp));
  ji_uid   : rw rho 7 = uid;
  ji_hwcap : rw rho 8 = hwcap;
  ji_rnd0  : rw rho 9 = rnd0;
  ji_rnd1  : rw rho 10 = rnd1;
  (* LPS 727298f3: AT_EXECFN's value, the address of the exec file name, the last string below
     [ed_top]; [rho0] gives it (so [Jinit_rho0] proves it), and A|B's [arg_layout] reads it as the
     end of the argv and envp strings. *)
  ji_execfn : rw rho 13 = at_execfn_ptr (ed_top draw) (in_execfn inp);
  ji_env   : rl rho 1 = env_bytes inp sp draw;
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
Proof using ENVC Hinp LEN RND STR draw sp. pose proof argv_valid as (H & _). subst ARGC. lia. Qed.

Lemma ENVC_bound : 0 <= ENVC <= 256.
Proof using ARGC Hinp LEN RND STR draw sp. pose proof envp_valid as (H & _). subst ENVC. lia. Qed.

Lemma tab_argv_bound : Z.of_nat (tab argv) <= 2097152.
Proof using Hinp. pose proof argv_valid as (_ & H & _). rewrite total_arg_bytes_tab in H. exact H. Qed.

Lemma tab_envp_bound : Z.of_nat (tab envp) <= 131072.
Proof using Hinp. pose proof envp_valid as (_ & H & _). rewrite total_arg_bytes_tab in H. exact H. Qed.

Lemma len0_bound : Z.of_nat (length argv0) <= 131071.
(* The Lets STR, RND and LEN read [sp] and [draw], so the [Proof using] names them. *)
Proof using ARGC ENVC Hinp LEN RND STR argv argv0 draw envp hwcap inp sp uid.
  pose proof argv_valid as (H1 & _ & H3 & _). unfold argv0 in *.
  destruct argv as [|a r]; [cbn in H1; lia|]. cbn. inversion H3. exact H2.
Qed.

Lemma len0_tab : ltac2:(tb__ "0|0|
S6aS8aS18S24Q8A1Vargv0;A2U1A2S6fVargv;A1A2").
(* Same: the closure of [ENVC] reaches STR, RND and LEN. *)
Proof using ARGC ENVC Hinp LEN RND STR argv argv0 draw envp hwcap inp sp uid.
  pose proof argv_valid as (H1 & _). unfold argv0 in *.
  destruct argv as [|a r]; [cbn in H1; lia|]. cbn. lia.
Qed.

(* LPS 727298f3 (StackLayout.v [block_head_size], [block_pad_len]): the head is
   [8 * items + auxv_size rseq + 8 * (items mod 2) + 16] bytes (AT_RANDOM's sixteen bytes at its end),
   then [arch_align_stack]'s pad, then the strings; so [STR = RND + 16 + pad], parametric in
   CONFIG_RSEQ, and [LEN] is the image's length.  [LEN_bound] is the model's [bsb_bound]
   (theories/Common/StepTac.v, copied in Lib/StackBound.v), which needs [valid_launch] (from
   [valid_input_either]) and the launch conjunct [Hlaunch] below: the fifth conjunct of
   Lib/InitLayout.v's [valid_entry48], which every consumer holds. *)
Hypothesis Hlaunch : entry_launch_ok_va Sv48 (mkEntry sp brk mb draw) inp.

(* [Lib/InitLayout.v]'s premise [Hsp_hi]: the second half of [valid_launch_sp]. *)
Lemma Hsp_hi0 : (bv_unsigned sp <= launch_sp_hi (ed_top draw) inp)%Z.
Proof using ARGC ENVC Hlaunch LEN RND STR. destruct Hlaunch as (_ & (_ & _ & H) & _). exact H. Qed.

Lemma STR_eq : STR = RND + 16 + Z.of_nat ltac:(first
  [ exact (pad_len inp sp draw) | exact (pad_len inp sp) | exact (pad_len inp) ]).
Proof using ARGC ENVC LEN RND STR draw sp.
  subst STR RND. unfold str_off, rand_off, pad_len, block_head_size.
  rewrite Nat2Z.inj_add, Nat2Z.inj_sub by lia. lia.
Qed.

Lemma RND_eq : RND = 8 * ARGC + 8 * ENVC + 24
                     + Z.of_nat (auxv_size (kb_rseq (in_kernel inp)))
                     + 8 * Z.of_nat (Nat.modulo (block_items argv envp) 2).
Proof using ARGC ENVC LEN RND STR draw sp.
  subst RND ARGC ENVC. unfold argv, envp, rand_off, block_head_size, block_items. cbv zeta.
  lia.
Qed.

Lemma LEN_eq : LEN = STR + Z.of_nat (launch_string_bytes argv envp (in_execfn inp)) + 8.
Proof using ARGC ENVC LEN RND STR draw sp.
  subst LEN STR. unfold argv, envp, img_len. rewrite !Nat2Z.inj_add. lia.
Qed.

(* [valid_launch] is the twelfth conjunct of the model's [valid_input_either] (Run.v). *)
Lemma valid_launch_of_input_either : valid_launch inp.
Proof using Hinp. pose proof Hinp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma LEN_bound : LEN <= 4194304 - 16.
Proof using ARGC ENVC Hinp Hlaunch LEN RND STR brk draw mb pc0 ph sp.
  pose proof (StackBound.bsb_bound Sv48 inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp brk draw valid_launch_of_input_either Hlaunch) as HB.
  assert (Hhi : (bv_unsigned sp <= launch_sp_hi (ed_top draw) inp)%Z).
  { destruct Hlaunch as (_ & (_ & _ & Hhi) & _). exact Hhi. }
  pose proof (length_bsb inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw Hhi) as HL. unfold bsb in HL.
  subst LEN. rewrite <- HL. lia.
Qed.

Lemma sp_bound : ltac2:(tb__ "0|1|
S1S1S8S8eS25Q40Vsp;A2M0A2S8G0S8dA2A2S0S4SeG0Z10A2Z0A3A2").
Proof using Hsp. pose proof Hsp as (A & B & C). auto. Qed.


(* LPS 727298f3: the image runs from [sp] to the stack VMA's end [ed_top] exactly (the model's
   [length_entry_stack_image_launch]), and that end is at most [sp_window_hi] ([valid_stack_top_va]). *)
Lemma LEN_fit : bv_unsigned sp + LEN <= sp_window_hi.
Proof using ARGC ENVC Hlaunch LEN RND STR pc0 ph.
  pose proof (StackBound.length_entry_stack_image_launch Sv48 inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp brk draw Hlaunch) as HE.
  pose proof (length_bsb inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw Hsp_hi0) as HL. unfold bsb in HL.
  destruct Hlaunch as ((_ & HTv & _) & _ & _). cbn [va_stack_top] in HTv.
  rewrite HL in HE. subst LEN. lia.
Qed.

Lemma sp_lo_val : sp_window_lo = 0x7fff80000000. Proof using . reflexivity. Qed.
Lemma sp_hi_val : sp_window_hi = 0x800000000000. Proof using . reflexivity. Qed.
Lemma stack_max_size_val : stack_max_size = 8388608. Proof using . reflexivity. Qed.

Let BSB : list byte := bsb inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw.

Lemma length_BSB : Z.of_nat (length BSB) = LEN.
Proof using ARGC ENVC Hlaunch LEN pc0 ph RND STR.
  pose proof (length_bsb inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw Hsp_hi0) as HL.
  subst BSB LEN. unfold bsb in *. rewrite HL. reflexivity.
Qed.


(* LPS 727298f3: no slack above the image (it runs to [ed_top]), and the zero-mapped window below
   [sp] starts at [stack_window_lo] (Run.v [init_machine_state]). *)
Lemma ms0_mem_def : forall a : word, ms_mem ms0 a =
  match stack_to_mem sp BSB a with
  | Some b => Some b
  | None => if (stack_window_lo (in_kernel inp) mb draw <=? bv_unsigned a) && (bv_unsigned a <? bv_unsigned sp)
            then Some (Z_to_bv 8 0) else None
  end.
Proof using . reflexivity. Qed.


Lemma ms0_mem_img : forall off, 0 <= off < LEN ->
  ms_mem ms0 (Z_to_bv 64 (bv_unsigned sp + off)) = nth_error BSB (Z.to_nat off).
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR.
  intros off Hoff. rewrite ms0_mem_def.
  pose proof sp_bound as [Hs _]. rewrite sp_hi_val, sp_lo_val in Hs. pose proof LEN_bound.
  pose proof length_BSB as HL.
  unfold stack_to_mem.
  rewrite Z_to_bv_small by (change (bv_modulus 64) with (2 ^ 64); lia).
  replace (bv_unsigned sp <=? bv_unsigned sp + off) with true by (symmetry; apply Z.leb_le; lia).
  replace (bv_unsigned sp + off - bv_unsigned sp) with off by lia.
  replace (off <? Z.of_nat (length BSB)) with true by (symmetry; apply Z.ltb_lt; lia).
  destruct (nth_error BSB (Z.to_nat off)) as [b|] eqn:E; [reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma ms0_mem_region : forall (o : nat) (seg : list byte) (j : nat),
  region inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw o seg -> (j < length seg)%nat ->
  ms_mem ms0 (Z_to_bv 64 (bv_unsigned sp + (Z.of_nat o + Z.of_nat j))) = Some (nth j seg (Z_to_bv 8 0)).
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR.
  intros o seg j Hr Hj.
  assert (Hlen : (o + length seg <= length BSB)%nat).
  { destruct Hr as (pre & post & E & L). subst BSB. unfold bsb in *. rewrite E, !length_app. lia. }
  pose proof length_BSB.
  rewrite ms0_mem_img by lia.
  replace (Z.to_nat (Z.of_nat o + Z.of_nat j)) with (o + j)%nat by lia.
  subst BSB. rewrite (region_nth inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw o seg j Hr Hj).
  apply nth_error_nth'. exact Hj.
Qed.

(* The zero-mapped window reaches [stack_window_depth] below [sp] for every admissible launch
   (the model's [stack_window_lo_valid]); the free-stack object needs only [STK_FREE] of it. *)
Lemma ms0_mem_below : forall a : word,
  bv_unsigned sp - STK_FREE <= bv_unsigned a < bv_unsigned sp -> ms_mem ms0 a = Some (Z_to_bv 8 0).
Proof using ARGC ENVC Hinp Hlaunch LEN RND STR.
  intros a Ha. rewrite ms0_mem_def. unfold stack_to_mem.
  pose proof (StackBound.stack_window_lo_valid inp sp brk mb draw valid_launch_of_input_either Hlaunch) as HW.
  unfold StackBound.stack_window_reach, STK_FREE in *. pose proof stack_max_size_val as SM.
  replace (bv_unsigned sp <=? bv_unsigned a) with false by (symmetry; apply Z.leb_gt; lia).
  replace (stack_window_lo (in_kernel inp) mb draw <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; lia).
  replace (bv_unsigned a <? bv_unsigned sp) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma ms0_mem_low : forall a : word,
  bv_unsigned a < bv_unsigned sp - stack_max_size -> ms_mem ms0 a = None.
Proof using ARGC ENVC Hlaunch LEN RND STR.
  intros a Ha. rewrite ms0_mem_def. unfold stack_to_mem.
  pose proof (StackBound.stack_window_lo_ge_sp inp sp brk mb draw Hlaunch) as HW. pose proof stack_max_size_val.
  replace (bv_unsigned sp <=? bv_unsigned a) with false by (symmetry; apply Z.leb_gt; lia).
  replace (stack_window_lo (in_kernel inp) mb draw <=? bv_unsigned a) with false by (symmetry; apply Z.leb_gt; lia).
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

(* The launch's numbers at LPS 727298f3 (StackLayout.v): the head [hdr ++ env ++ auxv ++ gap ++ rand]
   is [RND + 16] bytes, then [arch_align_stack]'s pad (at most 4110), then the strings and the
   exec file name, then the 8-byte slot below [ed_top], which is page-aligned. *)
Lemma nums :
  (140735340871680 <= bv_unsigned sp <= 140737488355328)
  /\ bv_unsigned sp mod 16 = 0
  /\ (1 <= ARGC <= 1024)
  /\ (0 <= ENVC <= 256)
  /\ STR = RND + 16 + Z.of_nat (pad_len inp sp draw)
  /\ Z.of_nat (length argv0) + 1 <= Z.of_nat (tab argv)
  /\ Z.of_nat (length argv0) <= 131071
  /\ RND = 8 * ARGC + 8 * ENVC + 24 + Z.of_nat (auxv_size (kb_rseq (in_kernel inp)))
           + 8 * Z.of_nat (Nat.modulo (block_items argv envp) 2)
  /\ Z.of_nat (pad_len inp sp draw) <= 4110
  /\ Z.of_nat (tab argv) <= 2097152
  /\ Z.of_nat (tab envp) <= 131072
  /\ LEN = STR + Z.of_nat (launch_string_bytes argv envp (in_execfn inp)) + 8
  /\ RND mod 8 = 0
  /\ (bv_unsigned sp + LEN) mod 4096 = 0.
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR.
  pose proof sp_bound as [A B]. rewrite sp_lo_val, sp_hi_val in A.
  pose proof ARGC_bound. pose proof ENVC_bound. pose proof STR_eq. pose proof len0_tab. pose proof len0_bound.
  pose proof RND_eq. pose proof tab_argv_bound. pose proof tab_envp_bound. pose proof LEN_eq.
  pose proof (rand_off_mod8 inp) as RM.
  assert (PB : Z.of_nat (pad_len inp sp draw) <= 4110).
  { pose proof Hsp_hi0 as Hhi. destruct Hlaunch as (_ & (_ & Hlo & _) & _).
    unfold launch_sp_lo, align_down16 in Hlo. unfold launch_sp_hi, align_down16 in Hhi.
    pose proof (Z.mod_pos_bound (bv_unsigned (ed_top draw) - 8
      - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp)) - 4095) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned (ed_top draw) - 8
      - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))) 16 ltac:(lia)).
    unfold pad_len, block_pad_len. rewrite Z2Nat.id by lia. lia. }
  assert (TOP : bv_unsigned sp + LEN = bv_unsigned (ed_top draw)).
  { pose proof (StackBound.length_entry_stack_image_launch Sv48 inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp brk draw Hlaunch) as HE.
    pose proof (length_bsb inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw Hsp_hi0) as HL. unfold bsb in HL.
    rewrite HL in HE. subst LEN. lia. }
  assert (TA : bv_unsigned (ed_top draw) mod 4096 = 0).
  { destruct Hlaunch as ((HPG & _) & _ & _). unfold page_size in HPG. exact HPG. }
  rewrite TOP. subst RND STR. repeat split; try lia; try exact TA.
Qed.

Ltac nums := pose proof nums; pose proof (auxv_size_le (kb_rseq (in_kernel inp))); rewrite ?pow64, ?pow63 in *.

(* LPS 727298f3 (StackLayout.v [at_execfn_ptr], [build_stack_bytes]): the exec file name's address,
   AT_EXECFN's value and launch variable 13, is where the argv and envp strings end, [STR] plus their
   bytes above [sp]; the name, its NUL and the 8-byte slot follow, up to [ed_top] = [sp + LEN]. *)
Lemma execfn_nums :
  bv_unsigned (at_execfn_ptr (ed_top draw) (in_execfn inp))
    = bv_unsigned sp + STR + Z.of_nat (tab argv) + Z.of_nat (tab envp)
  /\ bv_unsigned sp + STR + Z.of_nat (tab argv) + Z.of_nat (tab envp) + 9 <= bv_unsigned sp + LEN.
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR.
  pose proof sp_bound as [A B]. rewrite sp_lo_val, sp_hi_val in A.
  pose proof LEN_eq as LE. pose proof LEN_bound as LB.
  (* [Hsp_hi0] and [length_bsb] are used BEFORE [subst]: both read the section's [STR], which
     [subst] clears from the context. *)
  pose proof (StackBound.length_entry_stack_image_launch Sv48 inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp brk draw Hlaunch) as HE.
  pose proof (length_bsb inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw Hsp_hi0) as HL. unfold bsb in HL.
  rewrite HL in HE.
  unfold launch_string_bytes in LE. rewrite !length_flatten_strings in LE.
  subst LEN STR.
  pose proof (Zle_0_nat (length (in_execfn inp))).
  pose proof (Zle_0_nat (tab argv)). pose proof (Zle_0_nat (tab envp)).
  unfold at_execfn_ptr, nat_to_word. rewrite bv_sub_unsigned, Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small (Z.of_nat (8 + length (in_execfn inp) + 1)) (2 ^ 64)) by lia.
  rewrite Z.mod_small by lia.
  split; lia.
Qed.

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
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR. cbn. apply Z_to_bv_small. rewrite mod64. nums. lia. Qed.
Lemma U_v3 : ltac2:(tb__ "0|0|
S0S4S25Q40S31S28S30P3A1A2A2VENVC;A3").
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR. cbn. apply Z_to_bv_small. rewrite mod64. nums. lia. Qed.
Lemma U_v4 : ltac2:(tb__ "0|1|
S0S4S25Q40M0S31S28S30P4A1A2A2S7S25G0Vsp;A2VSTR;A2A3").
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR. cbn. apply Z_to_bv_small. rewrite mod64. nums. lia. Qed.
Lemma U_v5 : ltac2:(tb__ "0|0|
S0S4S25Q40S31S28S30P5A1A2A2S9S18S24Q8A1Vargv0;A2A1A3").
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR. cbn. apply Z_to_bv_small. rewrite mod64. nums. lia. Qed.
Lemma U_v6 : ltac2:(tb__ "0|1|
S0S4S25Q40M0S31S28S30P6A1A2A2S7S25G0Vsp;A2VRND;A2A3").
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR. cbn. apply Z_to_bv_small. rewrite mod64. nums. lia. Qed.

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
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR.
  nums. unfold env_base.
  erewrite U_add; [reflexivity| | apply U_lit; lia | | |lia]; try lia.
  erewrite U_add; [reflexivity| apply U_v1 | apply (U_sll3 2 ARGC U_v2); lia | | |]; lia.
Qed.

Lemma U_aux_base : ltac2:(tb__ "0|2|
S0S4S25Q40M0S31S28S83A2A2S7S7S7S25G0Vsp;A2SbZ8M1VARGC;A2A2SbG1VENVC;A2A2Z18A2A3").
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR.
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

Lemma rd_word_region : forall (o : nat) (ws : list word) (k : nat),
  region inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw o (flat_map word_le8 ws) ->
  (k < length ws)%nat -> Z.of_nat o + 8 * Z.of_nat (length ws) <= LEN ->
  rd_bytes ms0 (Z_to_bv 64 (bv_unsigned sp + Z.of_nat o + 8 * Z.of_nat k)) 8
  = Some (enc_bytes 8 (nth k ws (Z_to_bv 64 0))).
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR.
  intros o ws k Hr Hk Hlen. nums. pose proof LEN_bound.
  apply rd_bytes_of; [apply enc_bytes_length | lia | lia |].
  intros j Hj. rewrite <- word_le8_enc.
  replace (bv_unsigned sp + Z.of_nat o + 8 * Z.of_nat k + Z.of_nat j)
    with (bv_unsigned sp + (Z.of_nat o + Z.of_nat (8 * k + j))) by lia.
  apply rd_of_mem. rewrite (ms0_mem_region o (flat_map word_le8 ws) (8 * k + j) Hr)
    by (rewrite length_flat_map_le8; lia).
  f_equal. apply nth_flat_map_le8; assumption.
Qed.

Lemma cells_from_hold : forall (base : sv) (b : Z) (o : nat) (ws : list word) (svs : list sv) (k0 : nat)
    (off lo hi : Z),
  bv_unsigned (eval rho0 base) = b ->
  region inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw o (flat_map word_le8 ws) ->
  Z.of_nat o + 8 * Z.of_nat (length ws) <= LEN ->
  (forall i : nat, (i < length svs)%nat ->
     (k0 + i < length ws)%nat /\ eval rho0 (nth i svs (SLit 0)) = nth (k0 + i) ws (Z_to_bv 64 0)) ->
  b + off = bv_unsigned sp + Z.of_nat o + 8 * Z.of_nat k0 ->
  lo <= off -> 0 <= off -> off + 8 * Z.of_nat (length svs) <= hi -> hi < 2 ^ 62 ->
  Forall (cell_holds rho0 base lo hi ms0) (cells_from off svs).
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR.
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

(* [cells_from] over a list with holes: a [None] word gets no cell (the auxv values musl never reads). *)
Lemma cells_fromo_hold : forall (base : sv) (b : Z) (o : nat) (ws : list word) (svs : list (option sv)) (k0 : nat)
    (off lo hi : Z),
  bv_unsigned (eval rho0 base) = b ->
  region inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw o (flat_map word_le8 ws) ->
  Z.of_nat o + 8 * Z.of_nat (length ws) <= LEN ->
  (forall (i : nat) (v : sv), (i < length svs)%nat -> nth i svs None = Some v ->
     (k0 + i < length ws)%nat /\ eval rho0 v = nth (k0 + i) ws (Z_to_bv 64 0)) ->
  b + off = bv_unsigned sp + Z.of_nat o + 8 * Z.of_nat k0 ->
  lo <= off -> 0 <= off -> off + 8 * Z.of_nat (length svs) <= hi -> hi < 2 ^ 62 ->
  Forall (cell_holds rho0 base lo hi ms0) (cells_fromo off svs).
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR.
  intros base b o ws svs. induction svs as [|e svs IH]; intros k0 off lo hi Hb Hr Hlen HF Hoff Hlo H0 Hhi Hhi2; [constructor|].
  cbn [length] in Hhi.
  assert (Hb0 : 0 <= b) by (rewrite <- Hb; apply (proj1 (urange _))).
  nums.
  assert (IHr : Forall (cell_holds rho0 base lo hi ms0) (cells_fromo (off + 8) svs)).
  { apply (IH (S k0) (off + 8) lo hi Hb Hr Hlen); try lia.
    intros i v Hi Hv. destruct (HF (S i) v ltac:(cbn; lia) Hv) as [Hk He].
    replace (S k0 + i)%nat with (k0 + S i)%nat by lia. auto. }
  destruct e as [e|]; cbn [cells_fromo]; [|exact IHr].
  constructor; [|exact IHr].
  destruct (HF 0%nat e ltac:(cbn; lia) eq_refl) as [Hk He]. rewrite Nat.add_0_r in Hk, He.
  unfold cell_holds, cell8. cbn [c_off c_width c_val].
  rewrite (soff_lit' off) by lia. split; [lia|]. split; [lia|].
  unfold oaddr. rewrite Hb, He. change (Z.to_nat 8) with 8%nat.
  rewrite Hoff. apply rd_word_region; [exact Hr | exact Hk | exact Hlen].
Qed.

Lemma ms0_mem_img_some : ltac2:(tb__ "0|2|
S4S1S8Z0R1A2SaR1VLEN;A2A2S2S24Q8A1M0G0S0S19G0A1S63S29S26Q40M1S7S25G1Vsp;A2R3A2A2A2S1aG0R1A2A3Lb;A2F_;Foff;").
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR.
  intros off Hoff. rewrite ms0_mem_img by exact Hoff.
  destruct (nth_error BSB (Z.to_nat off)) as [b|] eqn:E; [exists b; reflexivity|].
  apply nth_error_None in E. pose proof length_BSB. lia.
Qed.

Lemma O_stk_holds : ltac2:(tb__ "0|0|
S37Vsegs;S28S29S81A4").
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR.
  nums. pose proof stack_max_size_val.
  apply (obj_holds_of segs rho0 ms0 O_stk (bv_unsigned sp) (- STK_FREE) 0); cbn [ob_base ob_lo ob_hi ob_cells ob_dflt O_stk].
  - apply U_v1.
  - apply soff_lit'. unfold STK_FREE. lia.
  - apply soff_lit'. lia.
  - unfold STK_FREE. lia.
  - intros off Hoff _. unfold STK_FREE in Hoff.
    eapply wview_of_mem. apply ms0_mem_below. rewrite U_addr by (unfold STK_FREE in *; lia). unfold STK_FREE in *; lia.
  - constructor.
  - intros off Hoff _. unfold STK_FREE in Hoff. cbn [dflt_holds].
    apply rd_of_mem. apply ms0_mem_below. rewrite U_addr by (unfold STK_FREE in *; lia). unfold STK_FREE in *; lia.
  - exact I.
Qed.

Lemma hdr_bytes_flat : hdr_bytes inp sp draw
  = flat_map word_le8 (len_word (in_argv inp) :: argv_ptrs inp sp draw ++ [Z_to_bv 64 0]).
Proof using .
  unfold hdr_bytes. cbn [flat_map]. rewrite flat_map_app. cbn [flat_map]. rewrite app_nil_r. reflexivity.
Qed.

Lemma argv_ptr0 : nth 0 (argv_ptrs inp sp draw) (Z_to_bv 64 0) = Z_to_bv 64 (bv_unsigned sp + STR).
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN RND argv0 pc0 ph.
  nums. unfold argv_ptrs. rewrite string_addrs_nth by (unfold ARGC, argv in *; lia).
  cbn [firstn tab]. rewrite Z.add_0_r. unfold str_base, nat_to_word. subst STR.
  apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. rewrite mod64.
  rewrite Z.mod_mod by lia. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma O_hdr_holds : obj_holds segs rho0 ms0 O_hdr.
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR.
  nums. pose proof LEN_bound.
  apply (obj_holds_of segs rho0 ms0 O_hdr (bv_unsigned sp) 0 16); cbn [ob_base ob_lo ob_hi ob_cells ob_dflt O_hdr].
  - apply U_v1.
  - apply soff_lit'. lia.
  - apply soff_lit'. lia.
  - lia.
  - intros off Hoff _. destruct (ms0_mem_img_some off ltac:(lia)) as [b Hb]. eapply wview_of_mem. exact Hb.
  - change [cell8 0 (SVar 2); cell8 8 (SVar 4)] with (cells_from 0 [SVar 2; SVar 4]).
    apply (cells_from_hold (SVar 1) (bv_unsigned sp) 0 (len_word (in_argv inp) :: argv_ptrs inp sp draw ++ [Z_to_bv 64 0]) _ 0);
      cbn [length]; try lia.
    + apply U_v1.
    + rewrite <- hdr_bytes_flat. apply (region_hdr inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw Hsp_hi0).
    + rewrite length_app. unfold argv_ptrs. rewrite string_addrs_fst_length. cbn [length]. unfold ARGC, argv in *. lia.
    + intros i Hi. destruct i as [|[|i]]; [| |lia]; cbn [nth Nat.add].
      * split; [lia|]. cbn [eval]. rewrite rw2. unfold len_word, ARGC, argv. reflexivity.
      * split.
        { rewrite length_app. unfold argv_ptrs. rewrite string_addrs_fst_length. cbn [length]. unfold ARGC, argv in *. lia. }
        cbn [eval]. rewrite rw4. rewrite app_nth1 by (unfold argv_ptrs; rewrite string_addrs_fst_length; unfold ARGC, argv in *; lia).
        symmetry. apply argv_ptr0.
  - intros off Hoff _. cbn [dflt_holds]. destruct (ms0_mem_img_some off ltac:(lia)) as [b Hb].
    exists b. apply rd_of_mem. exact Hb.
  - exact I.
Qed.

Lemma O_env_holds : obj_holds segs rho0 ms0 O_env.
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR.
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
    replace (bv_unsigned sp + 8 * ARGC + 16 + off) with (bv_unsigned sp + (Z.of_nat (16 + 8 * argc inp) + Z.of_nat (Z.to_nat off)))
      by (unfold argc, ARGC, argv in *; lia).
    rewrite (ms0_mem_region (16 + 8 * argc inp) (env_bytes inp sp draw) (Z.to_nat off) (region_env inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw Hsp_hi0)).
    + reflexivity.
    + rewrite length_env_bytes. unfold envc, ENVC, envp in *. lia.
  - cbn [dflt_inv rl rho0]. rewrite Pos.eqb_refl. rewrite length_env_bytes. unfold envc, ENVC, envp in *. lia.
Qed.

(* The auxv's bytes word by word: each entry is its type word then its value word. *)
Lemma build_auxv_words : forall l : list (word * word),
  build_auxv l = flat_map word_le8 (flat_map (fun e => [fst e; snd e]) l).
Proof using .
  intros l. unfold build_auxv. induction l as [|[t v] l IH]; [reflexivity|].
  cbn [flat_map fst snd app]. rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma auxv_words_length : forall la phx ex ux gx hx arx aex,
  length (flat_map (fun x : word * word => [fst x; snd x]) (auxv_entries la phx ex ux gx hx arx aex))
  = (2 * auxv_count (la_rseq la))%nat.
Proof using . intros [ehdr c0x msz [|]] phx ex ux gx hx arx aex; reflexivity. Qed.


Lemma rand_ptr_eq : at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp) = Z_to_bv 64 (bv_unsigned sp + RND).
Proof using .
  rewrite (at_random_ptr_eq inp sp). unfold nat_to_word. subst RND.
  apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite mod64.
  rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma O_aux_holds : obj_holds segs rho0 ms0 (O_aux (Z.of_N pc0) ph (kb_rseq (in_kernel inp))).
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR.
  nums. pose proof LEN_bound.
  assert (HA : Z.of_nat (auxv_size (kb_rseq (in_kernel inp))) = 432 \/ Z.of_nat (auxv_size (kb_rseq (in_kernel inp))) = 464)
    by (unfold auxv_size, auxv_count; destruct (kb_rseq (in_kernel inp)); cbn; lia).
  assert (Hr : region inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw (aux_off inp)
                 (flat_map word_le8 (flat_map (fun e => [fst e; snd e])
                   (auxv_entries (launch_auxv inp sp mb) ph (Z_to_bv 64 (Z.of_N pc0)) (in_uid inp) (in_gid inp) (in_hwcap inp)
                      (Z_to_bv 64 (bv_unsigned sp + RND)) (at_execfn_ptr (ed_top draw) (in_execfn inp)))))).
  { pose proof (region_auxv inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw Hsp_hi0) as R.
    unfold auxv in R. rewrite rand_ptr_eq in R. unfold auxv_bytes in R. rewrite build_auxv_words in R. exact R. }
  apply (obj_holds_of segs rho0 ms0 (O_aux (Z.of_N pc0) ph (kb_rseq (in_kernel inp)))
           (bv_unsigned sp + 8 * ARGC + 8 * ENVC + 24) 0 (Z.of_nat (auxv_size (kb_rseq (in_kernel inp)))));
    cbn [ob_base ob_lo ob_hi ob_cells ob_dflt O_aux].
  - apply U_aux_base.
  - apply soff_lit'. lia.
  - apply soff_lit'. lia.
  - lia.
  - intros off Hoff _.
    destruct (ms0_mem_img_some (8 * ARGC + 8 * ENVC + 24 + off) ltac:(lia)) as [b Hb].
    replace (bv_unsigned sp + 8 * ARGC + 8 * ENVC + 24 + off) with (bv_unsigned sp + (8 * ARGC + 8 * ENVC + 24 + off)) by lia.
    eapply wview_of_mem. exact Hb.
  - apply (cells_fromo_hold aux_base (bv_unsigned sp + 8 * ARGC + 8 * ENVC + 24) (aux_off inp) _ _ 0 0 0
             (Z.of_nat (auxv_size (kb_rseq (in_kernel inp)))) U_aux_base Hr).
    + rewrite auxv_words_length. cbn [launch_auxv la_rseq].
      unfold aux_off, block_items, auxv_size in *. unfold ARGC, ENVC, argv, envp in *. lia.
    + intros i v Hi Hv.
      unfold auxv_entries. cbn [launch_auxv la_rseq la_sysinfo_ehdr]. unfold aux_svs in Hv, Hi.
      destruct (kb_rseq (in_kernel inp));
        (do 60 (destruct i as [|i]; [cbn [nth app] in Hv; first [discriminate Hv | injection Hv as <-; split; [cbn; lia | reflexivity]] |]));
        cbn [nth app] in Hv; discriminate Hv.
    + unfold aux_off, block_items. unfold ARGC, ENVC, argv, envp in *. lia.
    + lia.
    + lia.
    + unfold aux_svs, auxv_size, auxv_count. destruct (kb_rseq (in_kernel inp)); cbn; lia.
    + lia.
  - intros off Hoff _. cbn [dflt_holds].
    destruct (ms0_mem_img_some (8 * ARGC + 8 * ENVC + 24 + off) ltac:(lia)) as [b Hb].
    replace (bv_unsigned sp + 8 * ARGC + 8 * ENVC + 24 + off) with (bv_unsigned sp + (8 * ARGC + 8 * ENVC + 24 + off)) by lia.
    exists b. apply rd_of_mem. exact Hb.
  - exact I.
Qed.

Lemma O_str0_holds : obj_holds segs rho0 ms0 O_str0.
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR.
  nums. pose proof LEN_bound.
  assert (LSB : Z.of_nat (tab argv) + 1 <= Z.of_nat (launch_string_bytes argv envp (in_execfn inp)))
    by (unfold launch_string_bytes; rewrite !length_flatten_strings; lia).
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
    replace (bv_unsigned sp + STR + off) with (bv_unsigned sp + (Z.of_nat (str_off inp sp draw + tab (firstn 0 (in_argv inp))) + Z.of_nat (Z.to_nat off)))
      by (cbn [firstn tab]; rewrite Nat.add_0_r; subst STR; lia).
    unfold argv0 in *. rewrite (ms0_mem_region _ (nth 0 (in_argv inp) [] ++ [Z_to_bv 8 0]) (Z.to_nat off)
      (region_argv_str inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw Hsp_hi0 0 ltac:(unfold argc, ARGC, argv in *; lia))).
    + reflexivity.
    + rewrite length_app. cbn [length]. unfold argv in *. lia.
  - cbn [dflt_inv rl rho0]. change (2 =? 1)%positive with false. rewrite Pos.eqb_refl. cbn [negb].
    rewrite length_app. cbn [length]. lia.
Qed.

Lemma O_rand_holds : obj_holds segs rho0 ms0 O_rand.
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR.
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
    apply (cells_from_hold (SVar 6) (bv_unsigned sp + RND) (rand_off inp) [rnd0; rnd1] _ 0);
      cbn [length]; try lia.
    + apply U_v6.
    + pose proof (region_rand inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw Hsp_hi0) as Hr.
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
Proof using ARGC ENVC Hdata Hdata_hi Hinp Hlaunch Hsp LEN pc0 ph RND STR.
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
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR.
  nums. unfold obj_hi_of. cbn [ob_hi O_env]. apply soff_small; [|lia].
  erewrite U_add; [reflexivity | apply (U_sll3 3 ENVC U_v3); lia | apply U_lit; lia | | |]; lia.
Qed.

Lemma hi_str0 : ltac2:(tb__ "0|0|
S0S4S3bS28S7cA2S7S9S18S24Q8A1Vargv0;A2A1Z1A2A3").
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR.
  nums. unfold obj_hi_of. cbn [ob_hi O_str0]. apply soff_small; [|lia].
  erewrite U_add; [reflexivity | apply U_v5 | apply U_lit; lia | | |]; lia.
Qed.

Lemma data_lo_hi : 0 <= data_lo <= data_hi.
Proof using ARGC ENVC Hdata LEN RND STR draw sp.
  pose proof Hdata as Hd. unfold data_ok_b in Hd. apply andb_prop in Hd as [Hd _]. apply andb_prop in Hd as [Hd1 Hd2].
  apply Z.leb_le in Hd1. apply Z.leb_le in Hd2. lia.
Qed.

Lemma ranges0 :
  obj_range rho0 O_stk = (bv_unsigned sp + - STK_FREE, bv_unsigned sp + 0)
  /\ obj_range rho0 O_hdr = (bv_unsigned sp + 0, bv_unsigned sp + 16)
  /\ obj_range rho0 O_env = (bv_unsigned sp + 8 * ARGC + 16 + 0, bv_unsigned sp + 8 * ARGC + 16 + (8 * ENVC + 8))
  /\ obj_range rho0 (O_aux (Z.of_N pc0) ph (kb_rseq (in_kernel inp)))
     = (bv_unsigned sp + 8 * ARGC + 8 * ENVC + 24 + 0, bv_unsigned sp + 8 * ARGC + 8 * ENVC + 24 + Z.of_nat (auxv_size (kb_rseq (in_kernel inp))))
  /\ obj_range rho0 O_str0 = (bv_unsigned sp + STR + 0, bv_unsigned sp + STR + (Z.of_nat (length argv0) + 1))
  /\ obj_range rho0 O_rand = (bv_unsigned sp + RND + 0, bv_unsigned sp + RND + 16)
  /\ obj_range rho0 (O_data data_lo data_hi) = (0 + data_lo, 0 + data_hi).
Proof using ARGC ENVC Hdata Hdata_hi Hinp Hlaunch Hsp LEN pc0 ph RND STR.
  nums. pose proof data_lo_hi.
  assert (HA : Z.of_nat (auxv_size (kb_rseq (in_kernel inp))) <= 464) by (unfold auxv_size, auxv_count; destruct (kb_rseq (in_kernel inp)); cbn; lia).
  split. { apply obj_range_of; [apply U_v1 | apply soff_lit'; unfold STK_FREE; lia | apply soff_lit'; lia]. }
  split. { apply obj_range_of; [apply U_v1 | apply soff_lit'; lia | apply soff_lit'; lia]. }
  split. { apply obj_range_of; [apply U_env_base | apply soff_lit'; lia | apply hi_env]. }
  split. { apply obj_range_of; [apply U_aux_base | apply soff_lit'; lia | apply soff_lit'; lia]. }
  split. { apply obj_range_of; [apply U_v4 | apply soff_lit'; lia | apply hi_str0]. }
  split. { apply obj_range_of; [apply U_v6 | apply soff_lit'; lia | apply soff_lit'; lia]. }
  apply obj_range_of; [apply U_lit; lia | apply soff_lit'; lia | apply soff_lit'; lia].
Qed.

Lemma pairwise0 : pairwise_disjoint rho0 (objs0 (Z.of_N pc0) ph data_lo data_hi (kb_rseq (in_kernel inp))).
Proof using ARGC ENVC Hdata Hdata_hi Hinp Hlaunch Hsp LEN pc0 ph RND STR.
  nums. pose proof stack_max_size_val. pose proof ranges0 as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  pose proof data_lo_hi.
  assert (LSB : Z.of_nat (tab argv) + 1 <= Z.of_nat (launch_string_bytes argv envp (in_execfn inp)))
    by (unfold launch_string_bytes; rewrite !length_flatten_strings; lia).
  unfold objs0, pairwise_disjoint.
  repeat split; repeat (apply Forall_cons || apply Forall_nil);
    rewrite ?R1, ?R2, ?R3, ?R4, ?R5, ?R6, ?R7; unfold ranges_disjoint, STK_FREE; cbn [fst snd]; lia.
Qed.

Lemma mem_match0 : mem_match segs rho0 (objs0 (Z.of_N pc0) ph data_lo data_hi (kb_rseq (in_kernel inp))) ms0.
Proof using ARGC ENVC Hdata Hdata_hi Hinp Hlaunch Hsp LEN pc0 ph RND STR.
  split; [|split].
  - repeat apply Forall_cons; [ | | | | | | | apply Forall_nil].
    + apply O_stk_holds. + apply O_hdr_holds. + apply O_env_holds. + apply O_aux_holds.
    + apply O_str0_holds. + apply O_rand_holds. + apply O_data_holds.
  - apply pairwise0.
  - intros a _. reflexivity.
Qed.

Lemma regs_match0 : regs_match rho0 (S0 (Z.of_N pc0) ph data_lo data_hi (kb_rseq (in_kernel inp))) ms0.
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

Lemma fregs_match0 : fregs_match rho0 (S0 (Z.of_N pc0) ph data_lo data_hi (kb_rseq (in_kernel inp))) ms0.
Proof using .
  intros r. unfold freg_sv. cbn [ss_fregs S0]. rewrite nth_fregs0.
  unfold ms0, init_machine_state. cbn [ms_fregs]. unfold reg_get. rewrite bvmap_get_empty. reflexivity.
Qed.

Lemma mod8_of16 : ltac2:(tb__ "0|2|
S4S4S0S4SeR2Z10A2Z0M0A3S0S4SeR2Z8M1A2G0A3S0S4SeS7R4R3A2G1A2G0A3F_;F_;Fb;Fa;").
Proof using ARGC ENVC LEN RND STR draw sp.
  intros a b Ha Hb.
  apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia].
  destruct Ha as [k Hk]. destruct Hb as [m Hm]. subst.
  replace (k * 16 + m * 8) with ((2 * k + m) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma facts0 : Forall (holds rho0) F0.
Proof using ARGC ENVC Hinp Hlaunch Hsp LEN pc0 ph RND STR.
  nums. pose proof (auxv_size_ge (kb_rseq (in_kernel inp))). pose proof LEN_fit as LF. rewrite sp_hi_val in LF.
  assert (LSB : Z.of_nat (tab argv) + 1 <= Z.of_nat (launch_string_bytes argv envp (in_execfn inp)))
    by (unfold launch_string_bytes; rewrite !length_flatten_strings; lia).
  unfold F0, SP_HI, STR0_END_HI, RAND_HI, V_SP, V_ARGC, V_ENVC, V_ARGV0, V_LEN0, V_RAND. rewrite sp_lo_val, sp_hi_val.
  repeat apply Forall_cons; try apply Forall_nil; cbn [holds];
    rewrite ?rw1, ?rw4, ?rw6, ?U_v1, ?U_v2, ?U_v3, ?U_v4, ?U_v5, ?U_v6; rewrite ?U_lit by lia; try lia.
  all: first [ erewrite U_add; [ | apply U_v4 | apply U_v5 | lia | lia | lia]; lia
             | rewrite U_addr by lia; split; [lia|];
               first [apply mod8_of16; lia | rewrite Z.pow_0_r; apply Z.mod_1_r | reflexivity]
             | split; [lia|]; change (2 ^ 4) with 16; lia ].
Qed.

Lemma swf0 : swf (S0 (Z.of_N pc0) ph data_lo data_hi (kb_rseq (in_kernel inp))) = true.
Proof using . destruct (kb_rseq (in_kernel inp)); reflexivity. Qed.

Theorem init_smatch0 : smatch segs rho0 (S0 (Z.of_N pc0) ph data_lo data_hi (kb_rseq (in_kernel inp))) (w0 c0).
Proof using ARGC ENVC Hdata Hdata_hi Hinp Hlaunch Hsp Htop LEN pc0 ph RND STR.
  nums. pose proof stack_max_size_val.
  unfold smatch, w0. cbn [fst snd cfg_ms cfg_model c0 init_config].
  change (init_machine_state segs pc0 ph sp mb draw inp) with ms0.
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
