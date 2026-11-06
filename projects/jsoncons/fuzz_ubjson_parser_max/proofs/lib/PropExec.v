(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PlacementSearch.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PropExec () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.WithFP1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.WithFP3."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1S"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"]; ["1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3add"; "3mul"; "4le"; "4lt"; "5firstn"; "5nth"; "5skipn"; "6N"; "6Z"; "7Z_to_le_bytes"]; ["7bytes_le_to_Z"; "7le2"; "7le4"; "7le8"; "7le_bytes_to_word"; "7len_word"; "7nat_to_word"; "7word_le8"; "8PhdrInfo"; "8Segment"; "9Build_machine_state"; "9MachineOk"; "9fetch_word"; "9is_ecall"; "9machine_result"; "9machine_state"]; ["9ov_read_bytes"; "9step"; "9word_to_le_bytes"; ":entry_block_top"; ":entry_page_top"; ":entry_stack_fits"; ":entry_stack_image"; ":entry_stack_span"; ":init_machine_state"; ":total_arg_bytes"; ";EntryDraw"; ";build_stack_bytes"; ";flatten_strings"; ";stack_to_mem"; ";string_addrs"; "<errno_ret"]; ["<sp_window_hi"; "=decode_any"; ">ALU_ADD"; ">ALU_AND"; ">ALU_OR"; ">ALU_SLL"; ">ALU_SLT"; ">ALU_SLTU"; ">ALU_SRA"; ">ALU_SRL"; ">ALU_SUB"; ">ALU_XOR"; ">BC_EQ"; ">BC_GE"; ">BC_GEU"; ">BC_LT"]; [">BC_LTU"; ">BC_NE"; ">Branch"; ">Jal"; ">M_DIV"; ">M_DIVU"; ">M_MUL"; ">M_MULH"; ">M_MULHSU"; ">M_MULHU"; ">M_REM"; ">M_REMU"; ">branch_cond"; ">instr"; "?bv_eqb"; "?bv_ltu"]; ["?bvmap"; "?bvmap_empty"; "?sext"; "?zext"; "@alu32"; "@alu64"; "@branch_taken"; "@is_x0"; "@low32"; "@mul_div"; "@reg_get"; "Bjalr_tgt"; "Brdn"; "Bv_add"; "Bv_addi"; "Bv_addiw"]; ["Bv_addw"; "Bv_and"; "Bv_auipc"; "Bv_div"; "Bv_divuw"; "Bv_divw"; "Bv_lb"; "Bv_lh"; "Bv_lui"; "Bv_lw"; "Bv_mul"; "Bv_mulh"; "Bv_mulhsu"; "Bv_mulhu"; "Bv_mulw"; "Bv_or"]; ["Bv_rem"; "Bv_remuw"; "Bv_remw"; "Bv_sll"; "Bv_slli"; "Bv_slliw"; "Bv_sllw"; "Bv_slt"; "Bv_slti"; "Bv_sltu"; "Bv_sra"; "Bv_srai"; "Bv_sraiw"; "Bv_sraw"; "Bv_srl"; "Bv_srli"]; ["Bv_srliw"; "Bv_srlw"; "Bv_sub"; "Bv_subw"; "Bv_xor"; "Ctotal_arg_bytes_nat"; "Cwrap_mem"; "Abtgt"; "Ac_eq"; "Ac_lts"; "Ac_ltu"; "Afp_csr"; "Afp_regs"; "Afx0"; "Agetr"; "Amkst"]; ["Ardn"; "Aregupd"; "Aseg_rom"; "Av_add"; "Av_addi"; "Av_slli"; "Av_sub"; "Dflat_map"; "Eadd"; "Eeqb"; "Eland"; "Ele"; "Elor"; "Elt"; "Elxor"; "Emodulo"]; ["Emul"; "Eof_N"; "Eof_nat"; "Eopp"; "Epow"; "Eshiftl"; "Eshiftr"; "Esub"; "Etestbit"; "Eto_nat"; "0a"; "0a1"; "0addr"; "0argv"; "0b"; "0b0"]; ["0b1"; "0b2"; "0b3"; "0b4"; "0b5"; "0b6"; "0b7"; "0base"; "0bs"; "0bytes"; "0c"; "0draw"; "0e"; "0envp"; "0fx"; "0hw"]; ["0hwcap"; "0imm"; "0j"; "0k"; "0l"; "0m"; "0m1"; "0m2"; "0mem"; "0mid"; "0n"; "0p"; "0p1"; "0p2"; "0pc"; "0ph"]; ["0post"; "0pre"; "0r"; "0r'"; "0r1"; "0r2"; "0regs"; "0rnd"; "0ro"; "0rom"; "0rs1"; "0rs2"; "0s"; "0segs"; "0sp"; "FBV"]; ["FZ_to_bv"; "Fbv"; "Fbv_add"; "Fbv_and"; "Fbv_concat"; "Fbv_extract"; "Fbv_half_modulus"; "Fbv_modulus"; "Fbv_not"; "Fbv_signed"; "Fbv_swrap"; "Fbv_unsigned"; "Fbv_wrap"; "0strs"; "0tl"; "0uid"]; ["0v"; "0w"; "0x"; "0xs"; "0y"; "0ys"; "0z"]]).
Class FPState := mkFP { fp_regs : bvmap 5 word; fp_csr : bv 32 }.
Definition fx0 : FPState := mkFP bvmap_empty (Z_to_bv 32 0).
Definition mkst `{fx : FPState} (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) : machine_state :=
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := None; ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}.
Section WithFP1.
Context {fx : FPState}.
Definition getr (regs : bvmap 5 word) (r : reg) : word :=
if bv_eqb r 0 then Z_to_bv 64 0 else reg_get regs r.
Definition regupd (regs : bvmap 5 word) (r : reg) (v : word) : bvmap 5 word :=
bvmap_set r v regs.
Lemma bv_eqb0_is_x0 : ltac2:(TCodec.tc2 tcn__PropExec "@'WAy5%211'C'5&RNr1(W?z(A%33921%63:51&S7%117%;3:31p^6=1").
Proof. reflexivity. Qed.
Lemma is_x0_0 : ltac2:(TCodec.tc2 tcn__PropExec ";'C'5&S7(W?y5z(A%43321%611(@%:3921").
Proof. reflexivity. Qed.
Lemma bv_wrap64_mod : ltac2:(TCodec.tc2 tcn__PropExec ">'N'C&WLyR0r1%3221&U?&UD+2+R0%3221%5271%;3<71p`>=1").
Proof. reflexivity. Qed.
Lemma bv_wrap32_mod : ltac2:(TCodec.tc2 tcn__PropExec ">'N'C&WLyQ0r1%3221&U?&UD+2+Q0%3221%5271%;3<71p`>=1").
Proof. reflexivity. Qed.
Lemma bv_eqb_refl : forall {n} (a : bv n), bv_eqb a a = true.
Proof. intros n a. unfold bv_eqb. apply Z.eqb_refl. Qed.
Lemma bv_eqb_neq : forall {n} (a b : bv n), a <> b -> bv_eqb a b = false.
Proof.
intros n a b Hne. unfold bv_eqb. apply Z.eqb_neq.
intro Hu. apply Hne. apply bv_eq. exact Hu.
Qed.
Lemma arg_reg_0 : ltac2:(TCodec.tc2 tcn__PropExec "A'C'WAy5%211&W@&U8+:&UB(1%211%5241%7291(W?(A%23<81/01<%@3=51").
Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_1 : ltac2:(TCodec.tc2 tcn__PropExec "B'C'WAy5%211&W@&U8+:&UBu1%211%5241%7291(W?+;(A%33=21/01=%A3>61").
Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_2 : ltac2:(TCodec.tc2 tcn__PropExec "B'C'WAy5%211&W@&U8+:&UBu2%211%5241%7291(W?+<(A%33=21/01=%A3>61").
Proof. apply bv_eq. reflexivity. Qed.
Lemma Z_testbit_high : ltac2:(TCodec.tc2 tcn__PropExec "K'N&U;zr3%3221'B&U=&UD+2r4%3221%5281%7281r5%=21;'C'5&UH%1259(7%53421p071p0:1p0C1p]8H1p[FI1p]FJ1").
Proof.
intros n a k Hn [Ha1 Ha2] Hk.
exact (proj1 (Z.bounded_iff_bits_nonneg n a Hn Ha1) Ha2 k Hk).
Qed.
Lemma Z_bounded_by_bits : ltac2:(TCodec.tc2 tcn__PropExec "K'N&U;zr2%3221r5r1%6221'C'5&UH%1268(7%53421p071p]8?1&U=r4&UD+2%221?%5241p071p0C1p0D1p[FI1p]FJ1").
Proof.
intros n a Hn Ha Hb. exact (proj2 (Z.bounded_iff_bits_nonneg n a Hn Ha) Hb).
Qed.
Lemma Z_land_range : ltac2:(TCodec.tc2 tcn__PropExec "H'N'B&U;zr2%3221&U=&UD+2+R0%3221%5271%;271&U:r4r3%3221%?2>1%<228%B221p0?1p091p[NF1p[FG1").
Proof.
intros a b Ha Hb. split; [apply Z.land_nonneg; lia|].
apply Z_bounded_by_bits; [lia| apply Z.land_nonneg; lia |].
intros k Hk. rewrite Z.land_spec.
rewrite (Z_testbit_high 64 a k) by lia. reflexivity.
Qed.
Lemma Z_lor_range : ltac2:(TCodec.tc2 tcn__PropExec "H'N'B&U;zr2%3221&U=&UD+2+R0%3221%5271%;271&U<r4r3%3221%?2>1%<228%B221p081p091p[NF1p[FG1").
Proof.
intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
apply Z_bounded_by_bits; [lia| apply Z.lor_nonneg; lia |].
intros k Hk. rewrite Z.lor_spec.
rewrite (Z_testbit_high 64 a k) by lia.
rewrite (Z_testbit_high 64 b k) by lia.
reflexivity.
Qed.
Lemma Z_lxor_range : ltac2:(TCodec.tc2 tcn__PropExec "H'N'B&U;zr2%3221&U=&UD+2+R0%3221%5271%;271&U>r4r3%3221%?2>1%<228%B221p081p091p[NF1p[FG1").
Proof.
intros a b Ha Hb. split; [apply Z.lxor_nonneg; lia|].
apply Z_bounded_by_bits; [lia| apply Z.lxor_nonneg; lia |].
intros k Hk. rewrite Z.lxor_spec.
rewrite (Z_testbit_high 64 a k) by lia.
rewrite (Z_testbit_high 64 b k) by lia.
reflexivity.
Qed.
Lemma Z_shiftr_range : ltac2:(TCodec.tc2 tcn__PropExec "H'N'B&U;zr2%3221&U=&UD+2+R0%3221%5271%;271&UFr4r3%3221%?2>1%<228%B221p0?1p091p]8F1p[FG1").
Proof.
intros a k Ha Hk. rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
split; [apply Z.div_pos; lia|].
apply Z.le_lt_trans with a; [|lia].
apply Z.div_le_upper_bound; nia.
Qed.
Lemma bv_swrap_add_idemp_l : ltac2:(TCodec.tc2 tcn__PropExec "B'M'N'C&WJr3&U8&WLr2%2241r1%5221%8271%7253%:291%<3=31p`:>1p`6?1p]FA1").
Proof.
intros n x y. unfold bv_swrap. f_equal.
replace (bv_wrap n x + y + bv_half_modulus n)%Z
with (bv_wrap n x + (y + bv_half_modulus n))%Z by lia.
rewrite bv_wrap_add_idemp_l. f_equal. lia.
Qed.
Lemma bv_swrap_add_idemp_r : ltac2:(TCodec.tc2 tcn__PropExec "B'M'N'C&WJr3&U8r2&WLr1%2251%5241%8271%7264%:291%<3=31p`:>1p`6?1p]FA1").
Proof.
intros n x y. rewrite Z.add_comm, bv_swrap_add_idemp_l, Z.add_comm. reflexivity.
Qed.
Lemma bv_swrap_wrap' : ltac2:(TCodec.tc2 tcn__PropExec "='M'N'C&WJr2&WLr1%2231%5241%6253%83921p`>:1p]F<1").
Proof. intros. apply bv_swrap_wrap. Qed.
Definition zsig (x : word) : Z := bv_signed x.
Definition v_addi (x : word) (imm : Z) : word := Z_to_bv 64 (bv_unsigned x + imm).
Definition v_add (x y : word) : word := Z_to_bv 64 (bv_unsigned x + bv_unsigned y).
Definition v_sub (x y : word) : word := Z_to_bv 64 (bv_unsigned x - bv_unsigned y).
Definition v_mul (x y : word) : word := Z_to_bv 64 (bv_unsigned x * bv_unsigned y).
Definition v_andi (x : word) (imm : Z) : word := Z_to_bv 64 (Z.land (bv_unsigned x) (bv_wrap 64 imm)).
Definition v_ori (x : word) (imm : Z) : word := Z_to_bv 64 (Z.lor (bv_unsigned x) (bv_wrap 64 imm)).
Definition v_xori (x : word) (imm : Z) : word := Z_to_bv 64 (Z.lxor (bv_unsigned x) (bv_wrap 64 imm)).
Definition v_and (x y : word) : word := Z_to_bv 64 (Z.land (bv_unsigned x) (bv_unsigned y)).
Definition v_or (x y : word) : word := Z_to_bv 64 (Z.lor (bv_unsigned x) (bv_unsigned y)).
Definition v_xor (x y : word) : word := Z_to_bv 64 (Z.lxor (bv_unsigned x) (bv_unsigned y)).
Definition c_eq (x y : word) : bool := bv_eqb x y.
Definition c_lts (x y : word) : bool := bv_lts x y.
Definition c_ltu (x y : word) : bool := bv_ltu x y.
Definition btgt (pc : word) (imm : Z) : word := v_addi pc imm.
Definition v_slti (x : word) (imm : Z) : word :=
if (zsig x <? imm)%Z then Z_to_bv 64 1 else Z_to_bv 64 0.
Definition v_sltiu (x : word) (imm : Z) : word :=
if (bv_unsigned x <? bv_wrap 64 imm)%Z then Z_to_bv 64 1 else Z_to_bv 64 0.
Definition v_slt (x y : word) : word := if c_lts x y then Z_to_bv 64 1 else Z_to_bv 64 0.
Definition v_sltu (x y : word) : word := if c_ltu x y then Z_to_bv 64 1 else Z_to_bv 64 0.
Definition v_slli (x : word) (sh : Z) : word := Z_to_bv 64 (Z.shiftl (bv_unsigned x) sh).
Definition v_srli (x : word) (sh : Z) : word := Z_to_bv 64 (Z.shiftr (bv_unsigned x) sh).
Definition v_srai (x : word) (sh : Z) : word := Z_to_bv 64 (Z.shiftr (bv_signed x) sh).
Definition v_sll (x y : word) : word :=
Z_to_bv 64 (Z.shiftl (bv_unsigned x) (bv_unsigned y mod 64)).
Definition v_srl (x y : word) : word :=
Z_to_bv 64 (Z.shiftr (bv_unsigned x) (bv_unsigned y mod 64)).
Definition v_sra (x y : word) : word :=
Z_to_bv 64 (Z.shiftr (bv_signed x) (bv_unsigned y mod 64)).
Definition v_lui (imm : Z) : word := Z_to_bv 64 imm.
Definition v_auipc (pc : word) (imm : Z) : word := Z_to_bv 64 (imm + bv_unsigned pc).
Definition v_addiw (x : word) (imm : Z) : word :=
Z_to_bv 64 (bv_swrap 32 (bv_unsigned x + imm)).
Definition v_slliw (x : word) (sh : Z) : word :=
Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned x) sh)).
Definition v_srliw (x : word) (sh : Z) : word :=
Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned x)) sh)).
Definition v_sraiw (x : word) (sh : Z) : word :=
Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned x)) sh)).
Definition v_addw (x y : word) : word :=
Z_to_bv 64 (bv_swrap 32 (bv_unsigned x + bv_unsigned y)).
Definition v_subw (x y : word) : word :=
Z_to_bv 64 (bv_swrap 32 (bv_unsigned x - bv_unsigned y)).
Definition v_sllw (x y : word) : word :=
Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned x) (bv_unsigned y mod 32))).
Definition v_srlw (x y : word) : word :=
Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned x)) (bv_unsigned y mod 32))).
Definition v_sraw (x y : word) : word :=
Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned x)) (bv_unsigned y mod 32))).
Definition v_mulh (x y : word) : word :=
Z_to_bv 64 (Z.shiftr (bv_signed x * bv_signed y) 64).
Definition v_mulhsu (x y : word) : word :=
Z_to_bv 64 (Z.shiftr (bv_signed x * bv_unsigned y) 64).
Definition v_mulhu (x y : word) : word :=
Z_to_bv 64 (Z.shiftr (bv_unsigned x * bv_unsigned y) 64).
Definition v_mulw (x y : word) : word :=
Z_to_bv 64 (bv_swrap 32 (bv_unsigned x * bv_unsigned y)).
Definition v_div (x y : word) : word :=
if (bv_unsigned y =? 0)%Z then Z_to_bv 64 (-1)
else Z_to_bv 64 (Z.quot (zsig x) (zsig y)).
Definition v_rem (x y : word) : word :=
if (bv_unsigned y =? 0)%Z then x
else Z_to_bv 64 (Z.rem (zsig x) (zsig y)).
Definition v_divw (x y : word) : word :=
if (bv_wrap 32 (bv_unsigned y) =? 0)%Z then Z_to_bv 64 (-1)
else Z_to_bv 64 (bv_swrap 32 (Z.quot (bv_swrap 32 (bv_unsigned x)) (bv_swrap 32 (bv_unsigned y)))).
Definition v_remw (x y : word) : word :=
if (bv_wrap 32 (bv_unsigned y) =? 0)%Z then Z_to_bv 64 (bv_swrap 32 (bv_unsigned x))
else Z_to_bv 64 (bv_swrap 32 (Z.rem (bv_swrap 32 (bv_unsigned x)) (bv_swrap 32 (bv_unsigned y)))).
Definition v_divuw (x y : word) : word :=
if (bv_wrap 32 (bv_unsigned y) =? 0)%Z then Z_to_bv 64 (-1)
else Z_to_bv 64 (bv_swrap 32 (bv_wrap 32 (bv_unsigned x) / bv_wrap 32 (bv_unsigned y))).
Definition v_remuw (x y : word) : word :=
if (bv_wrap 32 (bv_unsigned y) =? 0)%Z then Z_to_bv 64 (bv_swrap 32 (bv_unsigned x))
else Z_to_bv 64 (bv_swrap 32 (bv_wrap 32 (bv_unsigned x) mod bv_wrap 32 (bv_unsigned y))).
Definition v_lb (b : byte) : word := Z_to_bv 64 (bv_signed b).
Definition v_lh (v : word) : word := Z_to_bv 64 (bv_swrap 16 (bv_unsigned v)).
Definition v_lw (v : word) : word := Z_to_bv 64 (bv_swrap 32 (bv_unsigned v)).
Definition jalr_tgtZ (x : word) (imm : Z) : Z := Z.land (bv_unsigned x + imm) (-2).
Definition jalr_tgt (x : word) (imm : Z) : word := Z_to_bv 64 (jalr_tgtZ x imm).
Definition seg_rom (segs : list Segment) : word -> option byte :=
fun addr => match memory_read segs addr 1 with Some (b :: _) => Some b | _ => None end.
Fixpoint rdn (segs : list Segment) (mem : word -> option byte) (a : word) (n : nat) : option (list byte) :=
match n with
| O => Some []
| S n' =>
match (match mem a with Some b => Some b | None => seg_rom segs a end) with
| Some b => match rdn segs mem (a+1) n' with Some rest => Some (b :: rest) | None => None end
| None => None
end
end.
Lemma ov_rdn : ltac2:(TCodec.tc2 tcn__PropExec "L':'Q9%211'WAyR0%211'=y8%511%311p051';'C%=15%811&Q@r4r3r1r2%544321&S<%146543%;3931p[FC1p]F>1p]B@1p^LI1").
Proof.
intros segs mem n. induction n as [|n' IH]; intro a; [reflexivity|].
simpl. unfold seg_rom.
destruct (mem a) as [b|].
- rewrite IH. reflexivity.
- destruct (memory_read segs a 1) as [[|b rest]|]; [reflexivity| rewrite IH; reflexivity | reflexivity].
Qed.
Lemma le_word_1 : ltac2:(TCodec.tc2 tcn__PropExec "C'WAy8%211'CyR0%511&Q4(6r1(<%118%43931%611&W@&WK%12>7%32<1%>3<51p[N@1").
Proof.
intro b. unfold le_bytes_to_word. cbn [bytes_le_to_Z].
rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
Qed.
Lemma le_word_v : ltac2:(TCodec.tc2 tcn__PropExec "G':'WAy8%211%411yR0%511'C'N&Q0r2%211&WKr1%2291%83741&Q4r3%211%<3=19p051p`2?1p\BB1").
Proof.
intros bs v Hv. unfold le_bytes_to_word. rewrite Hv.
apply Z_to_bv_bv_unsigned.
Qed.
Lemma b_extract8_id : ltac2:(TCodec.tc2 tcn__PropExec "?'WAy8%211'C&WEyR0w&W@&WKr1%2291%4261%8476;1%:3;14p[N<1").
Proof.
intro b. apply bv_eq.
rewrite bv_extract_unsigned, Z_to_bv_unsigned, Z.shiftr_0_r.
pose proof (bv_unsigned_in_range _ b) as Hb.
change (bv_modulus 8) with 256%Z in Hb.
rewrite (bv_wrap_small 64) by (change (bv_modulus 64) with (2^64)%Z; lia).
apply bv_wrap_small. change (bv_modulus 8) with 256%Z. lia.
Qed.
Lemma b_lb_val : ltac2:(TCodec.tc2 tcn__PropExec "F'WAy8%211'CyR0%511&S2&WEw&Q4(6r1(<%11;%43<31%611%94<8?1%;3@=1&SF%118%A3?31p[NC1").
Proof.
intro b. rewrite le_word_1, b_extract8_id. apply bv_eq.
unfold sext, v_lb. rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned.
reflexivity.
Qed.
Lemma b_lh_val : ltac2:(TCodec.tc2 tcn__PropExec "?'WAyR0%211'C&S2y@&WEwr1%348241%63591&SG%114%:3;31p`2<1").
Proof.
intro v. apply bv_eq. unfold sext, v_lh.
rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned.
f_equal. unfold bv_signed.
rewrite bv_extract_unsigned, Z.shiftr_0_r.
apply bv_swrap_wrap.
Qed.
Lemma b_lw_val : ltac2:(TCodec.tc2 tcn__PropExec "?'WAyR0%211'C&S2yQ0&WEwr1%348241%63591&SI%114%:3;31p`2<1").
Proof.
intro v. apply bv_eq. unfold sext, v_lw.
rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned.
f_equal. unfold bv_signed.
rewrite bv_extract_unsigned, Z.shiftr_0_r.
apply bv_swrap_wrap.
Qed.
Lemma rdn_length : ltac2:(TCodec.tc2 tcn__PropExec "Q2':'Q9%211'WAyR0%211'=y8%511%311p051';%<14'C%812&S<r5r4r2r3%544321(3r1%22;1%;3:41&9%12B8%>3@1:p041p\BA1p[FI1p]FD1p]BF1p^LO1").
Proof.
intros segs mem n. induction n as [|n IH]; intros a bs H; cbn in H.
- inversion H; reflexivity.
- destruct (match mem a with Some b => Some b | None => seg_rom segs a end); [|discriminate].
destruct (rdn segs mem (a+1) n) eqn:E; [|discriminate].
inversion H; subst; cbn. f_equal. eauto.
Qed.
Lemma bytes_le_to_Z_nonneg : ltac2:(TCodec.tc2 tcn__PropExec "<':'WAy8%211%411&U;z&Q0r1%211%5241p\B71").
Proof.
induction bs as [|b bs IH]; cbn; [lia|].
apply Z.lor_nonneg. split.
- pose proof (bv_unsigned_in_range _ b). lia.
- apply Z.shiftl_nonneg. exact IH.
Qed.
Lemma bytes_le_to_Z_bound : ltac2:(TCodec.tc2 tcn__PropExec "E':'WAy8%211%411&U=&Q0r1%211&UD+2&U@+8&UB&9%12<8%311%6251%9281%>2;1p\B@1").
Proof.
induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
pose proof (bytes_le_to_Z_nonneg bs).
pose proof (bv_unsigned_in_range _ b) as Hb.
change (bv_modulus 8) with 256%Z in Hb.
apply Z_bounded_by_bits; [lia| |].
{ apply Z.lor_nonneg. split; [lia|]. apply Z.shiftl_nonneg. lia. }
intros k Hk. rewrite Z.lor_spec.
rewrite (Z_testbit_high 8 (bv_unsigned b) k) by lia.
rewrite Z.shiftl_spec by lia.
rewrite (Z_testbit_high (8 * Z.of_nat (length bs)) (bytes_le_to_Z bs) (k - 8)) by lia.
reflexivity.
Qed.
Lemma bytes_le_app : ltac2:(TCodec.tc2 tcn__PropExec "M':'WAy8%211%411'C'N&Q0&4r2r1%33821%511&U<%715&UE%916&U@+8&UB&9%12B<%311%6251%9281%<2;1%E3D>1p`<G1p`8H1").
Proof.
induction xs as [|x xs IH]; intro ys; cbn [bytes_le_to_Z app length].
- rewrite Z.mul_0_r, Z.shiftl_0_r, Z.lor_0_l. reflexivity.
- rewrite IH.
rewrite Z.shiftl_lor, Z.shiftl_shiftl by lia.
rewrite Z.lor_assoc. f_equal. f_equal. lia.
Qed.
Lemma le2_spec : ltac2:(TCodec.tc2 tcn__PropExec "F'WAy8%211'C'N&WKy@&Q1r2r1%3221%6251&Q0(6(<%11=%33>81%43?81%611%@3?81p\0B1p\2C1").
Proof.
intros b1 b0. unfold le2.
rewrite bv_concat_unsigned by reflexivity.
cbn [bytes_le_to_Z].
rewrite Z.shiftl_0_l, Z.lor_0_r. apply Z.lor_comm.
Qed.
Lemma le4_spec : ltac2:(TCodec.tc2 tcn__PropExec "L'WAy8%211'C'N&WKyQ0&Q2r4r3r2r1%544321%8271&Q0(6(<%11?%33@:1%43A:1%53B:1%63C:1%811%D3C:1p\0F1p\2G1p\4H1p\6I1").
Proof.
intros b3 b2 b1 b0. unfold le4.
rewrite bv_concat_unsigned by reflexivity.
rewrite !le2_spec.
change [b0; b1; b2; b3] with ([b0; b1] ++ [b2; b3]).
rewrite bytes_le_app. cbn [length]. apply Z.lor_comm.
Qed.
Lemma le8_spec : ltac2:(TCodec.tc2 tcn__PropExec "Q8'WAy8%211'C'N&WKyR0&Q3r8r7r6r5r4r3r2r1%9887654321%<2;1&Q0(6(<%11C%33D>1%43E>1%53F>1%63G>1%73H>1%83I>1%93J>1%:3K>1%<11%L3K>1p\0N1p\2O1p\4Q01p\6Q11p\8Q21p\:Q31p\<Q41p\>Q51").
Proof.
intros. unfold le8.
rewrite bv_concat_unsigned by reflexivity.
rewrite !le4_spec.
change [b0; b1; b2; b3; b4; b5; b6; b7] with ([b0; b1; b2; b3] ++ [b4; b5; b6; b7]).
rewrite bytes_le_app. cbn [length]. apply Z.lor_comm.
Qed.
Lemma ok_mkst_eq : ltac2:(TCodec.tc2 tcn__PropExec "Q?&S0y5'WAyR0%211%5241'=y8%611%311p061'Cr7r6%33921r5%53<31r1%511%412%93;21p[FA1'Q>'Q?%211(Q;&TOvV>r:r8r4%55432B1%7291r9%8571FC4%:2<1%I3<41p0@1p0F1p0I1p^BN1p]@O1p]>Q01p]LQ71p]JQ81p^<Q81p^:Q91").
Proof.
intros r1 r2 p1 p2 m1 m2 ro Hr Hp Hm.
assert (Em : m1 = m2) by (apply functional_extensionality; exact Hm).
subst. reflexivity.
Qed.
Lemma u64_range : ltac2:(TCodec.tc2 tcn__PropExec "B'WAyR0%211'B&U;z&WKr1%2271%5241&U=&UD+2+R0%3221%5271%=271p`6?1").
Proof. intro x. exact (bv_unsigned_in_range _ x). Qed.
Lemma u8_range : ltac2:(TCodec.tc2 tcn__PropExec "?'WAy8%211'B&U;z&WKr1%2271%5241&U=+X0%2241%:241p[N<1").
Proof. intro b. exact (bv_unsigned_in_range _ b). Qed.
Lemma u6_range : ltac2:(TCodec.tc2 tcn__PropExec "?'WAy6%211'B&U;z&WKr1%2271%5241&U=+R0%2241%:241p^J<1").
Proof. intro s. exact (bv_unsigned_in_range _ s). Qed.
Lemma u5_range : ltac2:(TCodec.tc2 tcn__PropExec "?'WAy5%211'B&U;z&WKr1%2271%5241&U=+Q0%2241%:241p^J<1").
Proof. intro s. exact (bv_unsigned_in_range _ s). Qed.
Lemma wrap64_range : ltac2:(TCodec.tc2 tcn__PropExec "A'N'B&U;z&WLyR0r1%3221%6251&U=&UD+2+R0%3221%5271%>271p`>@1").
Proof. intro z. exact (bv_wrap_in_range 64 z). Qed.
Lemma bv_swrap_congr : ltac2:(TCodec.tc2 tcn__PropExec "C'M'N'C&WLr3r2%3221r1%5241%73831&WJr4%2218%3228%<3=21p061p`:?1p`6@1p]FB1").
Proof.
intros n x y H. unfold bv_swrap. f_equal.
rewrite <- (bv_wrap_add_idemp_l n x), H, bv_wrap_add_idemp_l. reflexivity.
Qed.
Lemma bv_swrap_add_swrap_l : ltac2:(TCodec.tc2 tcn__PropExec "A'M'N'C&WJr3&U8r2%4231r1%4221%7261%6253%9281%;3<31p`:=1p`6>1p]F@1").
Proof.
intros n x y. apply bv_swrap_congr.
unfold bv_swrap.
replace (bv_wrap n (x + bv_half_modulus n) - bv_half_modulus n + y)%Z
with (bv_wrap n (x + bv_half_modulus n) + (y - bv_half_modulus n))%Z by lia.
rewrite bv_wrap_add_idemp_l.
f_equal. lia.
Qed.
Lemma bv_swrap_add_swrap_r : ltac2:(TCodec.tc2 tcn__PropExec "A'M'N'C&WJr3&U8r2r1%5241%4231%7261%6254%9281%;3<31p`:=1p`6>1p]F@1").
Proof.
intros n x y. rewrite Z.add_comm, bv_swrap_add_swrap_l, Z.add_comm. reflexivity.
Qed.
Lemma b_addsext : forall (a : word) {n} (imm : bv n),
a + sext 64 imm = v_addi a (bv_signed imm).
Proof.
intros. apply bv_eq. unfold v_addi, sext.
rewrite bv_add_unsigned, bv_sign_extend_unsigned, Z_to_bv_unsigned.
apply bv_wrap_add_idemp_r.
Qed.
Lemma b_npc4 : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C&WBr1&W@+4%2271%53841&S>%1264%93:31p]H;1").
Proof.
intros. apply bv_eq. unfold v_addi.
rewrite bv_add_unsigned, !Z_to_bv_unsigned.
apply bv_wrap_add_idemp_r.
Qed.
Lemma alu_addi : forall (a : word) {n} (imm : bv n),
alu64 ALU_ADD a (sext 64 imm) = v_addi a (bv_signed imm).
Proof. intros. apply b_addsext. Qed.
Lemma alu_andi : forall (a : word) {n} (imm : bv n),
alu64 ALU_AND a (sext 64 imm) = v_andi a (bv_signed imm).
Proof.
intros. apply bv_eq. unfold v_andi.
change (alu64 ALU_AND a (sext 64 imm)) with (bv_and a (sext 64 imm)).
rewrite bv_and_unsigned. unfold sext. rewrite bv_sign_extend_unsigned.
rewrite Z_to_bv_unsigned.
symmetry; apply bv_wrap_small.
apply Z_land_range; [apply u64_range | apply wrap64_range].
Qed.
Lemma alu_ori : forall (a : word) {n} (imm : bv n),
alu64 ALU_OR a (sext 64 imm) = v_ori a (bv_signed imm).
Proof.
intros. apply bv_eq. unfold v_ori.
change (alu64 ALU_OR a (sext 64 imm)) with (bv_or a (sext 64 imm)).
rewrite bv_or_unsigned. unfold sext. rewrite bv_sign_extend_unsigned.
rewrite Z_to_bv_unsigned.
symmetry; apply bv_wrap_small.
apply Z_lor_range; [apply u64_range | apply wrap64_range].
Qed.
Lemma alu_xori : forall (a : word) {n} (imm : bv n),
alu64 ALU_XOR a (sext 64 imm) = v_xori a (bv_signed imm).
Proof.
intros. apply bv_eq. unfold v_xori.
change (alu64 ALU_XOR a (sext 64 imm)) with (bv_xor a (sext 64 imm)).
rewrite bv_xor_unsigned. unfold sext. rewrite bv_sign_extend_unsigned.
rewrite Z_to_bv_unsigned.
symmetry; apply bv_wrap_small.
apply Z_lxor_range; [apply u64_range | apply wrap64_range].
Qed.
Lemma alu_slti : ltac2:(TCodec.tc2 tcn__PropExec "D'WAyR0%211y<%411'C&S5(R6r2&S2r1%238:1%63541&T8&WI%12<5%3281%<3?51p]4>1p[FA1").
Proof.
intros. unfold v_slti, zsig.
change (alu64 ALU_SLT a (sext 64 imm))
with (if bv_lts a (sext 64 imm) then Z_to_bv 64 1 else Z_to_bv 64 0).
unfold bv_lts, sext.
rewrite bv_sign_extend_signed by lia.
reflexivity.
Qed.
Lemma alu_sltiu : forall (a : word) {n} (imm : bv n),
alu64 ALU_SLTU a (sext 64 imm) = v_sltiu a (bv_signed imm).
Proof.
intros. unfold v_sltiu.
change (alu64 ALU_SLTU a (sext 64 imm))
with (if bv_ltu a (sext 64 imm) then Z_to_bv 64 1 else Z_to_bv 64 0).
unfold bv_ltu, sext.
rewrite bv_sign_extend_unsigned.
reflexivity.
Qed.
Lemma alu_add : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C&S5(R2r2r1%43321&S=%1243%83931p[N:1p[F;1").
Proof. reflexivity. Qed.
Lemma alu_sub : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C&S5(R:r2r1%43321&TB%1243%83931p[N:1p[F;1").
Proof. reflexivity. Qed.
Lemma alu_slt : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C&S5(R6r2r1%43321&T7%1243%83931p[N:1p[F;1").
Proof. reflexivity. Qed.
Lemma alu_sltu : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C&S5(R7r2r1%43321&T9%1243%83931p[N:1p[F;1").
Proof. reflexivity. Qed.
Lemma alu_and : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C&S5(R3r2r1%43321&SA%1243%83931p[N:1p[F;1").
Proof.
intros. apply bv_eq. unfold v_and.
change (alu64 ALU_AND a b) with (bv_and a b).
rewrite bv_and_unsigned, Z_to_bv_unsigned.
symmetry; apply bv_wrap_small.
apply Z_land_range; [apply u64_range | apply u64_range].
Qed.
Lemma alu_or : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C&S5(R4r2r1%43321&SO%1243%83931p[N:1p[F;1").
Proof.
intros. apply bv_eq. unfold v_or.
change (alu64 ALU_OR a b) with (bv_or a b).
rewrite bv_or_unsigned, Z_to_bv_unsigned.
symmetry; apply bv_wrap_small.
apply Z_lor_range; apply u64_range.
Qed.
Lemma alu_xor : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C&S5(R;r2r1%43321&TD%1243%83931p[N:1p[F;1").
Proof.
intros. apply bv_eq. unfold v_xor.
change (alu64 ALU_XOR a b) with (bv_xor a b).
rewrite bv_xor_unsigned, Z_to_bv_unsigned.
symmetry; apply bv_wrap_small.
apply Z_lxor_range; apply u64_range.
Qed.
Lemma shamt6_mask : ltac2:(TCodec.tc2 tcn__PropExec "C'WAy6%211'C'N&WKyR0&WC&S3r1%23941&W@+QO%2271%73841%:291%;2?7%>3=21p^J@1").
Proof.
intro s. rewrite bv_and_unsigned. unfold zext.
rewrite bv_zero_extend_unsigned by lia.
rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64)%Z; lia).
change 63%Z with (Z.ones 6).
rewrite Z.land_ones by lia.
apply Z.mod_small. change (2^6)%Z with 64%Z. apply u6_range.
Qed.
Lemma regamt64_mask : ltac2:(TCodec.tc2 tcn__PropExec "C'WAyR0%211'C'N&WK&WCr1&W@+QO%2291%53:41%72;1&U?%92=7+R0%3221%>3=51p[N@1").
Proof.
intro b. rewrite bv_and_unsigned.
rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64)%Z; lia).
change 63%Z with (Z.ones 6).
rewrite Z.land_ones by lia.
reflexivity.
Qed.
Lemma alu_slli : ltac2:(TCodec.tc2 tcn__PropExec "D'WAyR0%211y6%411'C&S5(R5r2&S3r1%238:1%63541&T4&WK%12<5%3281%<3?51p^J>1p[FA1").
Proof.
intros. apply bv_eq. unfold v_slli.
change (alu64 ALU_SLL a (zext 64 s)) with (a ≪ bv_and (zext 64 s) (Z_to_bv 64 63)).
rewrite bv_shiftl_unsigned, Z_to_bv_unsigned, shamt6_mask.
reflexivity.
Qed.
Lemma alu_srli : ltac2:(TCodec.tc2 tcn__PropExec "D'WAyR0%211y6%411'C&S5(R9r2&S3r1%238:1%63541&T?&WK%12<5%3281%<3?51p^J>1p[FA1").
Proof.
intros. apply bv_eq. unfold v_srli.
change (alu64 ALU_SRL a (zext 64 s)) with (a ≫ bv_and (zext 64 s) (Z_to_bv 64 63)).
rewrite bv_shiftr_unsigned, Z_to_bv_unsigned, shamt6_mask.
symmetry; apply bv_wrap_small.
apply Z_shiftr_range; [apply u64_range | apply u6_range].
Qed.
Lemma alu_srai : ltac2:(TCodec.tc2 tcn__PropExec "D'WAyR0%211y6%411'C&S5(R8r2&S3r1%238:1%63541&T;&WK%12<5%3281%<3?51p^J>1p[FA1").
Proof.
intros. apply bv_eq. unfold v_srai.
change (alu64 ALU_SRA a (zext 64 s))
with (bv_ashiftr a (bv_and (zext 64 s) (Z_to_bv 64 63))).
rewrite bv_ashiftr_unsigned, Z_to_bv_unsigned, shamt6_mask.
reflexivity.
Qed.
Lemma alu_sll : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C&S5(R5r2r1%43321&T3%1243%83931p[N:1p[F;1").
Proof.
intros. apply bv_eq. unfold v_sll.
change (alu64 ALU_SLL a b) with (a ≪ bv_and b (Z_to_bv 64 63)).
rewrite bv_shiftl_unsigned, Z_to_bv_unsigned, regamt64_mask.
reflexivity.
Qed.
Lemma alu_srl : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C&S5(R9r2r1%43321&T>%1243%83931p[N:1p[F;1").
Proof.
intros. apply bv_eq. unfold v_srl.
change (alu64 ALU_SRL a b) with (a ≫ bv_and b (Z_to_bv 64 63)).
rewrite bv_shiftr_unsigned, Z_to_bv_unsigned, regamt64_mask.
symmetry; apply bv_wrap_small.
apply Z_shiftr_range; [apply u64_range |].
pose proof (Z.mod_pos_bound (bv_unsigned b) 64 ltac:(lia)). lia.
Qed.
Lemma alu_sra : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C&S5(R8r2r1%43321&T:%1243%83931p[N:1p[F;1").
Proof.
intros. apply bv_eq. unfold v_sra.
change (alu64 ALU_SRA a b) with (bv_ashiftr a (bv_and b (Z_to_bv 64 63))).
rewrite bv_ashiftr_unsigned, Z_to_bv_unsigned, regamt64_mask.
reflexivity.
Qed.
Lemma low32_unsigned : ltac2:(TCodec.tc2 tcn__PropExec "@'WAyR0%211'C'N&WKyQ0&S8r1%211%5241&WL%72;4%2271%;3:41p[F=1").
Proof.
intro a. unfold low32. rewrite bv_extract_unsigned.
change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r. reflexivity.
Qed.
Lemma low32_signed : ltac2:(TCodec.tc2 tcn__PropExec "A'WAyR0%211'C'N&WIyQ0&S8r1%211%5241&WJ&WK%12<5%3281%<3;51p[F>1").
Proof.
intro a. unfold low32. rewrite bv_extract_signed.
change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r. reflexivity.
Qed.
Lemma shamt5_mask : ltac2:(TCodec.tc2 tcn__PropExec "C'WAy5%211'C'N&WKyQ0&WC&S3r1%23941&W@+O%2271%73841%:291%;2?7%>3=21p^J@1").
Proof.
intro s. rewrite bv_and_unsigned. unfold zext.
rewrite bv_zero_extend_unsigned by lia.
rewrite Z_to_bv_small by (change (bv_modulus 32) with (2^32)%Z; lia).
change 31%Z with (Z.ones 5).
rewrite Z.land_ones by lia.
apply Z.mod_small. change (2^5)%Z with 32%Z. apply u5_range.
Qed.
Lemma regamt32_mask : ltac2:(TCodec.tc2 tcn__PropExec "F'WAyR0%211'C'N&WKyQ0&WC&S8r1%211&W@+O%2271%73841%:291&U?%<2@8+Q0%3221%A3@51p[NC1").
Proof.
intro b. rewrite bv_and_unsigned, low32_unsigned.
rewrite Z_to_bv_small by (change (bv_modulus 32) with (2^32)%Z; lia).
change 31%Z with (Z.ones 5).
rewrite Z.land_ones by lia.
rewrite bv_wrap32_mod.
symmetry. apply Znumtheory.Zmod_div_mod; [lia|lia|].
exists (2^27)%Z. reflexivity.
Qed.
Lemma sext32_unsigned : ltac2:(TCodec.tc2 tcn__PropExec "B'WAyQ0%211'C'N&WKyR0&S2r1%23831%5241&WL&WJ%82<5%22=1%4291%=3<61p`2?1").
Proof.
intro v. unfold sext. rewrite bv_sign_extend_unsigned. reflexivity.
Qed.
Lemma w_addiw : ltac2:(TCodec.tc2 tcn__PropExec "H'WAyR0%211y<%411'C&S2yQ0&S4(R2&S8r2%211r1%83;71%73631%:39?1&S?&WI%12@6%3291%@3C51p]4B1p[FE1").
Proof.
intros. apply bv_eq. unfold v_addiw.
rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
change (alu32 ALU_ADD (low32 a) (sext 32 imm)) with (low32 a + sext 32 imm).
rewrite bv_add_unsigned, low32_unsigned.
unfold sext. rewrite bv_sign_extend_unsigned.
rewrite bv_swrap_wrap', bv_swrap_add_idemp_l, bv_swrap_add_idemp_r.
reflexivity.
Qed.
Lemma w_slliw : ltac2:(TCodec.tc2 tcn__PropExec "I'WAyR0%211y5%411'C&S2yQ0&S4(R5&S8r2%211&S3r1%23<81%83741%;3:@1&T5&WK%12A6%32:1%A3D51p^JC1p[FF1").
Proof.
intros. apply bv_eq. unfold v_slliw.
rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
change (alu32 ALU_SLL (low32 a) (zext 32 s))
with (low32 a ≪ bv_and (zext 32 s) (Z_to_bv 32 31)).
rewrite bv_shiftl_unsigned, shamt5_mask, low32_unsigned.
rewrite bv_swrap_wrap'.
apply bv_swrap_congr.
rewrite !Z.shiftl_mul_pow2 by apply u5_range.
rewrite !bv_wrap32_mod.
apply Z.mul_mod_idemp_l. lia.
Qed.
Lemma w_srliw : ltac2:(TCodec.tc2 tcn__PropExec "I'WAyR0%211y5%411'C&S2yQ0&S4(R9&S8r2%211&S3r1%23<81%83741%;3:@1&T@&WK%12A6%32:1%A3D51p^JC1p[FF1").
Proof.
intros. apply bv_eq. unfold v_srliw.
rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
change (alu32 ALU_SRL (low32 a) (zext 32 s))
with (low32 a ≫ bv_and (zext 32 s) (Z_to_bv 32 31)).
rewrite bv_shiftr_unsigned, shamt5_mask, low32_unsigned.
reflexivity.
Qed.
Lemma w_sraiw : ltac2:(TCodec.tc2 tcn__PropExec "I'WAyR0%211y5%411'C&S2yQ0&S4(R8&S8r2%211&S3r1%23<81%83741%;3:@1&T<&WK%12A6%32:1%A3D51p^JC1p[FF1").
Proof.
intros. apply bv_eq. unfold v_sraiw.
rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
change (alu32 ALU_SRA (low32 a) (zext 32 s))
with (bv_ashiftr (low32 a) (bv_and (zext 32 s) (Z_to_bv 32 31))).
rewrite bv_ashiftr_unsigned, shamt5_mask, low32_signed.
rewrite bv_swrap_wrap'. reflexivity.
Qed.
Lemma w_addw : ltac2:(TCodec.tc2 tcn__PropExec "D'WAyR0%211'C&S2yQ0&S4(R2&S8r2%211r1%411%73631%:39=1&S@%1275%>3?31p[N@1p[FA1").
Proof.
intros. apply bv_eq. unfold v_addw.
rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
change (alu32 ALU_ADD (low32 a) (low32 b)) with (low32 a + low32 b).
rewrite bv_add_unsigned, !low32_unsigned.
rewrite bv_swrap_wrap', bv_swrap_add_idemp_l, bv_swrap_add_idemp_r.
reflexivity.
Qed.
Lemma w_subw : ltac2:(TCodec.tc2 tcn__PropExec "D'WAyR0%211'C&S2yQ0&S4(R:&S8r2%211r1%411%73631%:39=1&TC%1275%>3?31p[N@1p[FA1").
Proof.
intros. apply bv_eq. unfold v_subw.
rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
change (alu32 ALU_SUB (low32 a) (low32 b)) with (low32 a - low32 b).
rewrite bv_sub_unsigned, !low32_unsigned.
rewrite bv_swrap_wrap'.
apply bv_swrap_congr.
rewrite !bv_wrap32_mod.
rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r.
reflexivity.
Qed.
Lemma w_sllw : ltac2:(TCodec.tc2 tcn__PropExec "D'WAyR0%211'C&S2yQ0&S4(R5&S8r2%211r1%411%73631%:39=1&T6%1275%>3?31p[N@1p[FA1").
Proof.
intros. apply bv_eq. unfold v_sllw.
rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
change (alu32 ALU_SLL (low32 a) (low32 b))
with (low32 a ≪ bv_and (low32 b) (Z_to_bv 32 31)).
rewrite bv_shiftl_unsigned, regamt32_mask, low32_unsigned.
rewrite bv_swrap_wrap'.
apply bv_swrap_congr.
pose proof (Z.mod_pos_bound (bv_unsigned b) 32 ltac:(lia)).
rewrite !Z.shiftl_mul_pow2 by lia.
rewrite !bv_wrap32_mod.
apply Z.mul_mod_idemp_l. lia.
Qed.
Lemma w_srlw : ltac2:(TCodec.tc2 tcn__PropExec "D'WAyR0%211'C&S2yQ0&S4(R9&S8r2%211r1%411%73631%:39=1&TA%1275%>3?31p[N@1p[FA1").
Proof.
intros. apply bv_eq. unfold v_srlw.
rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
change (alu32 ALU_SRL (low32 a) (low32 b))
with (low32 a ≫ bv_and (low32 b) (Z_to_bv 32 31)).
rewrite bv_shiftr_unsigned, regamt32_mask, low32_unsigned.
reflexivity.
Qed.
Lemma w_sraw : ltac2:(TCodec.tc2 tcn__PropExec "D'WAyR0%211'C&S2yQ0&S4(R8&S8r2%211r1%411%73631%:39=1&T=%1275%>3?31p[N@1p[FA1").
Proof.
intros. apply bv_eq. unfold v_sraw.
rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
change (alu32 ALU_SRA (low32 a) (low32 b))
with (bv_ashiftr (low32 a) (bv_and (low32 b) (Z_to_bv 32 31))).
rewrite bv_ashiftr_unsigned, regamt32_mask, low32_signed.
rewrite bv_swrap_wrap'. reflexivity.
Qed.
Lemma m_mul : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C&S9(RFr2r1%447321&SJ%1243%83931p[N:1p[F;1").
Proof. reflexivity. Qed.
Lemma m_mulh : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C&S9(RGr2r1%447321&SK%1243%83931p[N:1p[F;1").
Proof. reflexivity. Qed.
Lemma m_mulhsu : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C&S9(RHr2r1%447321&SL%1243%83931p[N:1p[F;1").
Proof. reflexivity. Qed.
Lemma m_mulhu : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C&S9(RIr2r1%447321&SM%1243%83931p[N:1p[F;1").
Proof. reflexivity. Qed.
Lemma m_div : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C&S9(RDr2r1%447321&SC%1243%83931p[N:1p[F;1").
Proof. reflexivity. Qed.
Lemma m_rem : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C&S9(RJr2r1%447321&T0%1243%83931p[N:1p[F;1").
Proof. reflexivity. Qed.
Lemma w_mulw : ltac2:(TCodec.tc2 tcn__PropExec "D'WAyR0%211'C&S2yQ0&S9(RF&S8r2%211r1%411%748631%:39=1&SN%1275%>3?31p[N@1p[FA1").
Proof.
intros. apply bv_eq. unfold v_mulw.
rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
change (mul_div M_MUL (low32 a) (low32 b)) with (low32 a * low32 b).
rewrite bv_mul_unsigned, !low32_unsigned.
rewrite bv_swrap_wrap'.
apply bv_swrap_congr.
rewrite !bv_wrap32_mod.
rewrite Z.mul_mod_idemp_l, Z.mul_mod_idemp_r by lia.
reflexivity.
Qed.
Lemma div0_32 : ltac2:(TCodec.tc2 tcn__PropExec "D'WAyR0%211'C'5&U9&WKyQ0&S8r1%211%5241z%8221&WL%92>6%2291%<215%?3>51p[NA1").
Proof. intro b. rewrite low32_unsigned. reflexivity. Qed.
Lemma w_divw : ltac2:(TCodec.tc2 tcn__PropExec "D'WAyR0%211'C&S2yQ0&S9(RD&S8r2%211r1%411%748631%:39=1&SE%1275%>3?31p[N@1p[FA1").
Proof.
intros. unfold mul_div, v_divw.
rewrite div0_32.
destruct (bv_wrap 32 (bv_unsigned b) =? 0)%Z.
- apply bv_eq. reflexivity.
- apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
rewrite bv_quots_unsigned, bv_swrap_wrap', !low32_signed.
reflexivity.
Qed.
Lemma w_remw : ltac2:(TCodec.tc2 tcn__PropExec "D'WAyR0%211'C&S2yQ0&S9(RJ&S8r2%211r1%411%748631%:39=1&T2%1275%>3?31p[N@1p[FA1").
Proof.
intros. unfold mul_div, v_remw.
rewrite div0_32.
destruct (bv_wrap 32 (bv_unsigned b) =? 0)%Z.
- apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned, low32_unsigned.
rewrite bv_swrap_wrap'. reflexivity.
- apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
rewrite bv_rems_unsigned, bv_swrap_wrap', !low32_signed.
reflexivity.
Qed.
Lemma w_divuw : ltac2:(TCodec.tc2 tcn__PropExec "D'WAyR0%211'C&S2yQ0&S9(RE&S8r2%211r1%411%748631%:39=1&SD%1275%>3?31p[N@1p[FA1").
Proof.
intros. unfold mul_div, v_divuw.
rewrite div0_32.
destruct (bv_wrap 32 (bv_unsigned b) =? 0)%Z.
- apply bv_eq. reflexivity.
- apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned.
f_equal; rewrite ?bv_divu_unsigned, ?low32_unsigned; reflexivity.
Qed.
Lemma w_remuw : ltac2:(TCodec.tc2 tcn__PropExec "D'WAyR0%211'C&S2yQ0&S9(RK&S8r2%211r1%411%748631%:39=1&T1%1275%>3?31p[N@1p[FA1").
Proof.
intros. unfold mul_div, v_remuw.
rewrite div0_32.
destruct (bv_wrap 32 (bv_unsigned b) =? 0)%Z.
- apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned, low32_unsigned.
rewrite bv_swrap_wrap'. reflexivity.
- apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned.
f_equal; rewrite ?bv_modu_unsigned, ?low32_unsigned; reflexivity.
Qed.
Lemma bv_swrap_hi : ltac2:(TCodec.tc2 tcn__PropExec "N'M'N&E'Cr2w%33621%511&U;&WFr3%211%4218&U=&WGr4%211%4271&WJr5%2215&UG%813%2281%E3G41p081p0>1p0D1p`>K1p]FM1").
Proof.
intros n z Hn Hlo Hhi. unfold bv_swrap, bv_wrap.
pose proof (bv_half_modulus_twice n Hn) as Htw.
pose proof (bv_modulus_pos n) as Hpos.
replace (z + bv_half_modulus n)%Z
with ((z + bv_half_modulus n - bv_modulus n) + 1 * bv_modulus n)%Z by lia.
rewrite Z_mod_plus_full.
rewrite Z.mod_small by lia.
lia.
Qed.
Lemma b_lui : ltac2:(TCodec.tc2 tcn__PropExec "I'WAyD%211'CyR0%511&S2yQ0&WDy<r1&W@z%2241%657=541%938;1&SH&UE&WI%12B9+<%4221%611%D3B81p]4F1").
Proof.
intros imm. apply bv_eq. unfold v_lui.
rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
rewrite bv_concat_unsigned by reflexivity.
rewrite (Z_to_bv_small 12 0) by (change (bv_modulus 12) with (2^12)%Z; lia).
rewrite Z.lor_0_r.
unfold bv_signed.
pose proof (bv_unsigned_in_range _ imm) as Hr.
change (bv_modulus 20) with (2^20)%Z in Hr.
rewrite !Z.shiftl_mul_pow2 by lia.
change (Z.of_N 12) with 12%Z.
destruct (Z.lt_ge_cases (bv_unsigned imm) (2^19)) as [Hlt|Hge].
- rewrite (bv_swrap_small 32)
by (change (bv_half_modulus 32) with (2^31)%Z; lia).
rewrite (bv_swrap_small 20)
by (change (bv_half_modulus 20) with (2^19)%Z; lia).
reflexivity.
- rewrite (bv_swrap_hi 32)
by first [discriminate
|change (bv_half_modulus 32) with (2^31)%Z;
change (bv_modulus 32) with (2^32)%Z; lia].
rewrite (bv_swrap_hi 20)
by first [discriminate
|change (bv_half_modulus 20) with (2^19)%Z;
change (bv_modulus 20) with (2^20)%Z; lia].
change (bv_modulus 32) with (2^32)%Z.
change (bv_modulus 20) with (2^20)%Z.
lia.
Qed.
Lemma b_auipc : ltac2:(TCodec.tc2 tcn__PropExec "M'WAyR0%211yD%411'C&WBr2&S2yQ0&WDy<r1&W@z%2241%657=541%938@1%<3A;1&SB&UE&WI%12C:+<%4221%62B1%E3H81p]4G1p]HJ1").
Proof.
intros. rewrite b_lui. apply bv_eq. unfold v_lui, v_auipc.
rewrite bv_add_unsigned, !Z_to_bv_unsigned.
rewrite bv_wrap_add_idemp_r. f_equal. lia.
Qed.
Lemma Z_land_m2_wrap : ltac2:(TCodec.tc2 tcn__PropExec ">'N'C&U:&WLyR0r1%3221-2%5241%7231%8253%8271%;3<31p`>=1").
Proof.
intro z. rewrite !bv_wrap64_mod.
apply Z.bits_inj'. intros k Hk.
rewrite Z.land_spec.
destruct (Z.lt_ge_cases k 64) as [Hlt|Hge].
- rewrite !Z.mod_pow2_bits_low by lia.
rewrite Z.land_spec. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia.
apply andb_false_r.
Qed.
Lemma b_jalr : ltac2:(TCodec.tc2 tcn__PropExec "J'WAyR0%211y<%411'C&WC&WBr2&S2r1%238:1%53;41&WH&W@+1%22?1%42@1%<3A61&S;&WI%12B;%32>1%B3E51p]4D1p[FG1").
Proof.
intros. rewrite b_addsext. apply bv_eq.
unfold jalr_tgt, jalr_tgtZ, v_addi.
rewrite bv_and_unsigned, bv_not_unsigned, !Z_to_bv_unsigned.
change (bv_wrap 64 1) with 1%Z.
change (Z.lnot 1) with (-2)%Z.
apply Z_land_m2_wrap.
Qed.
End WithFP1.
Ltac step_pipeline Hfetch Hecall Hdecode :=
unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
cbn [ms_pc ms_pc_val mkst];
rewrite Hfetch;
cbv beta iota;
unfold RiscvSemantics.drop_access_report,
RiscvSemantics.decode_exec_accesses;
rewrite Hecall;
cbv beta iota;
rewrite Hdecode;
cbv beta iota zeta delta
[RiscvSemantics.interp_eff_accesses
RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
Sem.exec Sem.load_val Sem.store_val
Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
Sem.inval_resv Sem.w0 Sem.w1
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst];
rewrite ?bv_eqb0_is_x0.
Section WithFP2.
Context {fx : FPState}.
Lemma step_opimm_gen : forall segs regs pc mem rom w op rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs
else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
(v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w op rd rs imm Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma step_shiftimm_gen : forall segs regs pc mem rom w op rd rs (sh : bv 6),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm op rd rs sh, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs
else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
(v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w op rd rs sh Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma step_op_gen : forall segs regs pc mem rom w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs
else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
(v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma step_opimm32_gen : forall segs regs pc mem rom w rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (alu32 ALU_ADD (low32 (getr regs rs)) (sext 32 imm))))
(v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma step_shiftimm32_gen : forall segs regs pc mem rom w op rd rs (sh : bv 5),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm32 op rd rs sh, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
(v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w op rd rs sh Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma step_op32_gen : forall segs regs pc mem rom w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op32 op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
(v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma step_mul_gen : forall segs regs pc mem rom w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs
else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
(v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma step_mul32_gen : forall segs regs pc mem rom w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul32 op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
(v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma step_branch_tk_gen : ltac2:(TCodec.tc2 tcn__PropExec "RN':'Q9%211&S0y5'WAyR0%211%5241'=y8%611%311p061yQ0%:11'RL%<1=y=%>11'C%<16&Q<r:r8%3221(3r5%22=1%93841'5&Q=r6%211(7%?3521'?'RM'N%3221%O11&R1r7%211(>(RBr4r3%34@E21+4%64=<21%I2<1%Q03<91&S6&TNr<%221H%322N%53@21(@%Q83N21'Q>'Q?%211&QAr>&TOvV>r=r;%4532?1Q?%7261(Q;&TG&WI%12QIQ@%32E1%;5:918QF%62@1%QK3@81p0D1p0M1p0Q?1p0QF1p]4R11p^HR41p^FR51p\FR71p`4R91p^DR<1p]BR=1p]NRD1p^>RD1p^LRK1").
Proof.
intros segs regs pc mem rom w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
step_pipeline Hfetch Hecall Hdecode.
unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
destruct (is_x0 rs1); destruct (is_x0 rs2);
cbv beta iota; rewrite Hc; cbv beta iota;
rewrite b_addsext; reflexivity.
Qed.
Lemma step_branch_ft_gen : ltac2:(TCodec.tc2 tcn__PropExec "RK':'Q9%211&S0y5'WAyR0%211%5241'=y8%611%311p061yQ0%:11'RL%<1=y=%>11'C%<16&Q<r:r8%3221(3r5%22=1%93841'5&Q=r6%211(7%?3521'?'RM'N%3221%O11&R1r7%211(>(RBr4r3%34@E21+4%64=<21%I2<1%Q03<91&S6&TNr<%221H%322N%53@21%Q73M1I'Q>'Q?%211&QAr>&TOvV>r=r;%4532>1Q>%7261(Q;&U4%12BH%958716QC%42>1%QH3>61p0B1p0J1p0Q<1p0QC1p]4QN1p^HR11p^FR21p\FR41p`4R61p^DR91p]BR:1p]NRA1p^>RA1p^LRH1").
Proof.
intros segs regs pc mem rom w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
step_pipeline Hfetch Hecall Hdecode.
unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
destruct (is_x0 rs1); destruct (is_x0 rs2);
cbv beta iota; rewrite Hc; cbv beta iota;
rewrite b_npc4; reflexivity.
Qed.
Lemma step_addi : forall segs regs pc mem rom w rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_opimm_gen by eassumption.
rewrite alu_addi. reflexivity.
Qed.
Lemma step_andi : forall segs regs pc mem rom w rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm ALU_AND rd rs imm, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_andi (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_opimm_gen by eassumption.
rewrite alu_andi. reflexivity.
Qed.
Lemma step_ori : forall segs regs pc mem rom w rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm ALU_OR rd rs imm, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_ori (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_opimm_gen by eassumption.
rewrite alu_ori. reflexivity.
Qed.
Lemma step_xori : forall segs regs pc mem rom w rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm ALU_XOR rd rs imm, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_xori (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_opimm_gen by eassumption.
rewrite alu_xori. reflexivity.
Qed.
Lemma step_sltiu : forall segs regs pc mem rom w rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm ALU_SLTU rd rs imm, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sltiu (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_opimm_gen by eassumption.
rewrite alu_sltiu. reflexivity.
Qed.
Lemma step_slti : forall segs regs pc mem rom w rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm ALU_SLT rd rs imm, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_slti (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_opimm_gen by eassumption.
rewrite alu_slti. reflexivity.
Qed.
Lemma step_slli : forall segs regs pc mem rom w rd rs (sh : bv 6),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm ALU_SLL rd rs sh, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_slli (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_shiftimm_gen by eassumption.
rewrite alu_slli. reflexivity.
Qed.
Lemma step_srli : forall segs regs pc mem rom w rd rs (sh : bv 6),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm ALU_SRL rd rs sh, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srli (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_shiftimm_gen by eassumption.
rewrite alu_srli. reflexivity.
Qed.
Lemma step_srai : forall segs regs pc mem rom w rd rs (sh : bv 6),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm ALU_SRA rd rs sh, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srai (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_shiftimm_gen by eassumption.
rewrite alu_srai. reflexivity.
Qed.
Lemma step_add : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op ALU_ADD rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_add (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_add. reflexivity.
Qed.
Lemma step_sub : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op ALU_SUB rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sub (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_sub. reflexivity.
Qed.
Lemma step_slt : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op ALU_SLT rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_slt (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_slt. reflexivity.
Qed.
Lemma step_sltu : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op ALU_SLTU rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sltu (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_sltu. reflexivity.
Qed.
Lemma step_and : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op ALU_AND rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_and (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_and. reflexivity.
Qed.
Lemma step_or : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_or (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_or. reflexivity.
Qed.
Lemma step_xor : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op ALU_XOR rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_xor (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_xor. reflexivity.
Qed.
Lemma step_sll : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op ALU_SLL rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sll (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_sll. reflexivity.
Qed.
Lemma step_srl : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op ALU_SRL rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srl (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_srl. reflexivity.
Qed.
Lemma step_sra : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op ALU_SRA rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sra (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op_gen by eassumption.
rewrite alu_sra. reflexivity.
Qed.
Lemma step_addiw : forall segs regs pc mem rom w rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addiw (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_opimm32_gen by eassumption.
rewrite w_addiw. reflexivity.
Qed.
Lemma step_slliw : forall segs regs pc mem rom w rd rs (sh : bv 5),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm32 ALU_SLL rd rs sh, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_slliw (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_shiftimm32_gen by eassumption.
rewrite w_slliw. reflexivity.
Qed.
Lemma step_srliw : forall segs regs pc mem rom w rd rs (sh : bv 5),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm32 ALU_SRL rd rs sh, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srliw (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_shiftimm32_gen by eassumption.
rewrite w_srliw. reflexivity.
Qed.
Lemma step_sraiw : forall segs regs pc mem rom w rd rs (sh : bv 5),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm32 ALU_SRA rd rs sh, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sraiw (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_shiftimm32_gen by eassumption.
rewrite w_sraiw. reflexivity.
Qed.
Lemma step_addw : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op32 ALU_ADD rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op32_gen by eassumption.
rewrite w_addw. reflexivity.
Qed.
Lemma step_subw : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op32 ALU_SUB rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_subw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op32_gen by eassumption.
rewrite w_subw. reflexivity.
Qed.
Lemma step_sllw : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op32 ALU_SLL rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sllw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op32_gen by eassumption.
rewrite w_sllw. reflexivity.
Qed.
Lemma step_srlw : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op32 ALU_SRL rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srlw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op32_gen by eassumption.
rewrite w_srlw. reflexivity.
Qed.
Lemma step_sraw : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op32 ALU_SRA rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sraw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_op32_gen by eassumption.
rewrite w_sraw. reflexivity.
Qed.
Lemma step_mul : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul M_MUL rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mul (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul_gen by eassumption.
rewrite m_mul. reflexivity.
Qed.
Lemma step_mulh : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul M_MULH rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mulh (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul_gen by eassumption.
rewrite m_mulh. reflexivity.
Qed.
Lemma step_mulhsu : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul M_MULHSU rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mulhsu (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul_gen by eassumption.
rewrite m_mulhsu. reflexivity.
Qed.
Lemma step_mulhu : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul M_MULHU rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mulhu (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul_gen by eassumption.
rewrite m_mulhu. reflexivity.
Qed.
Lemma step_div : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul M_DIV rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_div (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul_gen by eassumption.
rewrite m_div. reflexivity.
Qed.
Lemma step_rem : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul M_REM rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_rem (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul_gen by eassumption.
rewrite m_rem. reflexivity.
Qed.
Lemma step_mulw : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul32 M_MUL rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mulw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul32_gen by eassumption.
rewrite w_mulw. reflexivity.
Qed.
Lemma step_divw : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul32 M_DIV rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_divw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul32_gen by eassumption.
rewrite w_divw. reflexivity.
Qed.
Lemma step_divuw : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul32 M_DIVU rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_divuw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul32_gen by eassumption.
rewrite w_divuw. reflexivity.
Qed.
Lemma step_remw : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul32 M_REM rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_remw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul32_gen by eassumption.
rewrite w_remw. reflexivity.
Qed.
Lemma step_remuw : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul32 M_REMU rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_remuw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
intros. erewrite step_mul32_gen by eassumption.
rewrite w_remuw. reflexivity.
Qed.
Lemma step_beq_tk : ltac2:(TCodec.tc2 tcn__PropExec "RL':'Q9%211&S0y5'WAyR0%211%5241'=y8%611%311p061yQ0%:11%;1<y=%=11'C%;15&Q<r9r7%3221(3r4%22<1%93841'5&Q=r5%211(7%?3521'?'RM'N%3221%N11&R1r6%211(>(RB(R<r3%342@E1+4%64=<21%I2<1%Q03<91&TH&TNr;%221>%322I%5221(@%Q83N21'Q>'Q?%211&QAr=&TOvV>r<r:%4532?1Q?%7261(Q;&TG&WI%12QIQ;%32E1%;5:918QF%62@1%QK3@81p0D1p0M1p0Q?1p0QF1p]4R11p^HR41p^FR51p`4R71p^DR:1p]BR;1p]NRB1p^>RB1p^LRI1").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_tk_gen segs regs pc mem rom w BC_EQ rs1 rs2 imm Hf He Hd).
exact Hc.
Qed.
Lemma step_beq_ft : ltac2:(TCodec.tc2 tcn__PropExec "RI':'Q9%211&S0y5'WAyR0%211%5241'=y8%611%311p061yQ0%:11%;1<y=%=11'C%;15&Q<r9r7%3221(3r4%22<1%93841'5&Q=r5%211(7%?3521'?'RM'N%3221%N11&R1r6%211(>(RB(R<r3%342@E1+4%64=<21%I2<1%Q03<91&TH&TNr;%221>%322I%5221%Q73M1I'Q>'Q?%211&QAr=&TOvV>r<r:%4532>1Q>%7261(Q;&U4%12BH%958716QC%42>1%QH3>61p0B1p0J1p0Q<1p0QC1p]4QN1p^HR11p^FR21p`4R41p^DR71p]BR81p]NR?1p^>R?1p^LRF1").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_ft_gen segs regs pc mem rom w BC_EQ rs1 rs2 imm Hf He Hd).
exact Hc.
Qed.
Lemma step_bne_tk : ltac2:(TCodec.tc2 tcn__PropExec "RK':'Q9%211&S0y5'WAyR0%211%5241'=y8%611%311p061yQ0%:11%;1<y=%=11'C%;15&Q<r9r7%3221(3r4%22<1%93841'5&Q=r5%211(7%?3521'?'RM'N%3221%N11&R1r6%211(>(RB(RAr3%342@E1+4%64=<21%I2<1%Q03<91&TH&TNr;%221>%322I%5221%Q73M1I'Q>'Q?%211&QAr=&TOvV>r<r:%4532>1Q>%7261(Q;&TG&WI%12QHQ:%32D1%;5:918QE%62@1%QJ3@81p0D1p0L1p0Q>1p0QE1p]4R01p^HR31p^FR41p`4R61p^DR91p]BR:1p]NRA1p^>RA1p^LRH1").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_tk_gen segs regs pc mem rom w BC_NE rs1 rs2 imm Hf He Hd).
cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.
Lemma step_bne_ft : ltac2:(TCodec.tc2 tcn__PropExec "RJ':'Q9%211&S0y5'WAyR0%211%5241'=y8%611%311p061yQ0%:11%;1<y=%=11'C%;15&Q<r9r7%3221(3r4%22<1%93841'5&Q=r5%211(7%?3521'?'RM'N%3221%N11&R1r6%211(>(RB(RAr3%342@E1+4%64=<21%I2<1%Q03<91&TH&TNr;%221>%322I%5221(@%Q83N21'Q>'Q?%211&QAr=&TOvV>r<r:%4532?1Q?%7261(Q;&U4%12CI%958716QD%42>1%QI3>61p0B1p0K1p0Q=1p0QD1p]4QO1p^HR21p^FR31p`4R51p^DR81p]BR91p]NR@1p^>R@1p^LRG1").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_ft_gen segs regs pc mem rom w BC_NE rs1 rs2 imm Hf He Hd).
cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.
Lemma step_blt_tk : ltac2:(TCodec.tc2 tcn__PropExec "RL':'Q9%211&S0y5'WAyR0%211%5241'=y8%611%311p061yQ0%:11%;1<y=%=11'C%;15&Q<r9r7%3221(3r4%22<1%93841'5&Q=r5%211(7%?3521'?'RM'N%3221%N11&R1r6%211(>(RB(R?r3%342@E1+4%64=<21%I2<1%Q03<91&TI&TNr;%221>%322I%5221(@%Q83N21'Q>'Q?%211&QAr=&TOvV>r<r:%4532?1Q?%7261(Q;&TG&WI%12QIQ;%32E1%;5:918QF%62@1%QK3@81p0D1p0M1p0Q?1p0QF1p]4R11p^HR41p^FR51p`4R71p^DR:1p]BR;1p]NRB1p^>RB1p^LRI1").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_tk_gen segs regs pc mem rom w BC_LT rs1 rs2 imm Hf He Hd).
exact Hc.
Qed.
Lemma step_blt_ft : ltac2:(TCodec.tc2 tcn__PropExec "RI':'Q9%211&S0y5'WAyR0%211%5241'=y8%611%311p061yQ0%:11%;1<y=%=11'C%;15&Q<r9r7%3221(3r4%22<1%93841'5&Q=r5%211(7%?3521'?'RM'N%3221%N11&R1r6%211(>(RB(R?r3%342@E1+4%64=<21%I2<1%Q03<91&TI&TNr;%221>%322I%5221%Q73M1I'Q>'Q?%211&QAr=&TOvV>r<r:%4532>1Q>%7261(Q;&U4%12BH%958716QC%42>1%QH3>61p0B1p0J1p0Q<1p0QC1p]4QN1p^HR11p^FR21p`4R41p^DR71p]BR81p]NR?1p^>R?1p^LRF1").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_ft_gen segs regs pc mem rom w BC_LT rs1 rs2 imm Hf He Hd).
exact Hc.
Qed.
Lemma step_bge_tk : ltac2:(TCodec.tc2 tcn__PropExec "RK':'Q9%211&S0y5'WAyR0%211%5241'=y8%611%311p061yQ0%:11%;1<y=%=11'C%;15&Q<r9r7%3221(3r4%22<1%93841'5&Q=r5%211(7%?3521'?'RM'N%3221%N11&R1r6%211(>(RB(R=r3%342@E1+4%64=<21%I2<1%Q03<91&TI&TNr;%221>%322I%5221%Q73M1I'Q>'Q?%211&QAr=&TOvV>r<r:%4532>1Q>%7261(Q;&TG&WI%12QHQ:%32D1%;5:918QE%62@1%QJ3@81p0D1p0L1p0Q>1p0QE1p]4R01p^HR31p^FR41p`4R61p^DR91p]BR:1p]NRA1p^>RA1p^LRH1").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_tk_gen segs regs pc mem rom w BC_GE rs1 rs2 imm Hf He Hd).
cbn [branch_taken]. unfold c_lts in Hc. rewrite Hc. reflexivity.
Qed.
Lemma step_bge_ft : ltac2:(TCodec.tc2 tcn__PropExec "RJ':'Q9%211&S0y5'WAyR0%211%5241'=y8%611%311p061yQ0%:11%;1<y=%=11'C%;15&Q<r9r7%3221(3r4%22<1%93841'5&Q=r5%211(7%?3521'?'RM'N%3221%N11&R1r6%211(>(RB(R=r3%342@E1+4%64=<21%I2<1%Q03<91&TI&TNr;%221>%322I%5221(@%Q83N21'Q>'Q?%211&QAr=&TOvV>r<r:%4532?1Q?%7261(Q;&U4%12CI%958716QD%42>1%QI3>61p0B1p0K1p0Q=1p0QD1p]4QO1p^HR21p^FR31p`4R51p^DR81p]BR91p]NR@1p^>R@1p^LRG1").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_ft_gen segs regs pc mem rom w BC_GE rs1 rs2 imm Hf He Hd).
cbn [branch_taken]. unfold c_lts in Hc. rewrite Hc. reflexivity.
Qed.
Lemma step_bltu_tk : ltac2:(TCodec.tc2 tcn__PropExec "RL':'Q9%211&S0y5'WAyR0%211%5241'=y8%611%311p061yQ0%:11%;1<y=%=11'C%;15&Q<r9r7%3221(3r4%22<1%93841'5&Q=r5%211(7%?3521'?'RM'N%3221%N11&R1r6%211(>(RB(R@r3%342@E1+4%64=<21%I2<1%Q03<91&TJ&TNr;%221>%322I%5221(@%Q83N21'Q>'Q?%211&QAr=&TOvV>r<r:%4532?1Q?%7261(Q;&TG&WI%12QIQ;%32E1%;5:918QF%62@1%QK3@81p0D1p0M1p0Q?1p0QF1p]4R11p^HR41p^FR51p`4R71p^DR:1p]BR;1p]NRB1p^>RB1p^LRI1").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_tk_gen segs regs pc mem rom w BC_LTU rs1 rs2 imm Hf He Hd).
exact Hc.
Qed.
Lemma step_bltu_ft : ltac2:(TCodec.tc2 tcn__PropExec "RI':'Q9%211&S0y5'WAyR0%211%5241'=y8%611%311p061yQ0%:11%;1<y=%=11'C%;15&Q<r9r7%3221(3r4%22<1%93841'5&Q=r5%211(7%?3521'?'RM'N%3221%N11&R1r6%211(>(RB(R@r3%342@E1+4%64=<21%I2<1%Q03<91&TJ&TNr;%221>%322I%5221%Q73M1I'Q>'Q?%211&QAr=&TOvV>r<r:%4532>1Q>%7261(Q;&U4%12BH%958716QC%42>1%QH3>61p0B1p0J1p0Q<1p0QC1p]4QN1p^HR11p^FR21p`4R41p^DR71p]BR81p]NR?1p^>R?1p^LRF1").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_ft_gen segs regs pc mem rom w BC_LTU rs1 rs2 imm Hf He Hd).
exact Hc.
Qed.
Lemma step_bgeu_tk : ltac2:(TCodec.tc2 tcn__PropExec "RK':'Q9%211&S0y5'WAyR0%211%5241'=y8%611%311p061yQ0%:11%;1<y=%=11'C%;15&Q<r9r7%3221(3r4%22<1%93841'5&Q=r5%211(7%?3521'?'RM'N%3221%N11&R1r6%211(>(RB(R>r3%342@E1+4%64=<21%I2<1%Q03<91&TJ&TNr;%221>%322I%5221%Q73M1I'Q>'Q?%211&QAr=&TOvV>r<r:%4532>1Q>%7261(Q;&TG&WI%12QHQ:%32D1%;5:918QE%62@1%QJ3@81p0D1p0L1p0Q>1p0QE1p]4R01p^HR31p^FR41p`4R61p^DR91p]BR:1p]NRA1p^>RA1p^LRH1").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_tk_gen segs regs pc mem rom w BC_GEU rs1 rs2 imm Hf He Hd).
cbn [branch_taken]. unfold c_ltu in Hc. rewrite Hc. reflexivity.
Qed.
Lemma step_bgeu_ft : ltac2:(TCodec.tc2 tcn__PropExec "RJ':'Q9%211&S0y5'WAyR0%211%5241'=y8%611%311p061yQ0%:11%;1<y=%=11'C%;15&Q<r9r7%3221(3r4%22<1%93841'5&Q=r5%211(7%?3521'?'RM'N%3221%N11&R1r6%211(>(RB(R>r3%342@E1+4%64=<21%I2<1%Q03<91&TJ&TNr;%221>%322I%5221(@%Q83N21'Q>'Q?%211&QAr=&TOvV>r<r:%4532?1Q?%7261(Q;&U4%12CI%958716QD%42>1%QI3>61p0B1p0K1p0Q=1p0QD1p]4QO1p^HR21p^FR31p`4R51p^DR81p]BR91p]NR@1p^>R@1p^LRG1").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_ft_gen segs regs pc mem rom w BC_GEU rs1 rs2 imm Hf He Hd).
cbn [branch_taken]. unfold c_ltu in Hc. rewrite Hc. reflexivity.
Qed.
Lemma step_lui : forall segs regs pc mem rom w rd (imm : bv 20),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Lui rd imm, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12))) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4, ?b_lui; reflexivity.
Qed.
Lemma step_auipc : forall segs regs pc mem rom w rd (imm : bv 20),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Auipc rd imm, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_auipc pc (Z.shiftl (bv_signed imm) 12))) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4, ?b_auipc; reflexivity.
Qed.
Lemma step_jal_x0 : ltac2:(TCodec.tc2 tcn__PropExec "RC':'Q9%211&S0y5'WAyR0%211%5241'=y8%611%311p061yQ0%:11yE%<11'C%:14&Q<r7r5%3221(3r2%22;1%93841'5&Q=r3%211(7%?3521'?'RM'N%3221%M11&R1r4%211(>(RC(W?z(A%33Q;21%521B+4%84?>21%K2>1%Q23>;1'Q>'Q?%211&QAr:&TOvV>r9r8r6%55432Q:1%8271(Q;&TG&WI%12QDL%3281%<5;:1QA8%62A1%QF3A81p0E1p0Q91p0Q@1p]4QK1p`4QN1p^DR11p]BR21p]NR91p^>R91p^LR@1").
Proof.
intros segs regs pc mem rom w imm Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
rewrite is_x0_0; cbv beta iota.
rewrite b_addsext. reflexivity.
Qed.
Lemma step_jalr_gen : forall segs regs pc mem rom w rd rs1 (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
(jalr_tgt (getr regs rs1) (bv_signed imm)) mem rom).
Proof.
intros segs regs pc mem rom w rd rs1 imm Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_jalr, ?b_npc4; reflexivity.
Qed.
Lemma step_ecall : ltac2:(TCodec.tc2 tcn__PropExec "R5':'Q9%211&S0y5'WAyR0%211%5241'=y8%611%311p061yQ0%:11'C%812&Q<r6r4%3221(3r1%2291%93841'5&Q=r2%211(@%?3521'Q>'Q?%211&QAr8&TOvV>r7r5%4532F1E%7261(Q;(Q:&TL%118&TN(W?+A(A%33Q?21%52=1%O2Q>1(0%11Q@&TK%11C%>8C<Q7531BQ6%@2J1%Q<3JB1p0N1p0Q51p`4Q@1p^DQC1p]BQD1p]NQK1p^>QK1p^LR21").
Proof.
intros segs regs pc mem rom w Hfetch Hecall.
unfold RiscvSemantics.step, RiscvSemantics.step_accesses.
cbn [ms_pc ms_pc_val mkst].
rewrite Hfetch. cbv beta iota.
unfold RiscvSemantics.drop_access_report,
RiscvSemantics.decode_exec_accesses.
rewrite Hecall. cbv beta iota.
reflexivity.
Qed.
Lemma step_lbu : forall segs regs pc mem rom w rd rs (imm : bv 12) b,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (bv_unsigned b))) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm b Hfetch Hecall Hdecode Hread.
assert (Hz : zext 64 (bv_extract 0 8 (le_bytes_to_word [b])) = Z_to_bv 64 (bv_unsigned b)).
{ rewrite le_word_1, b_extract8_id. apply bv_eq.
unfold zext. rewrite bv_zero_extend_unsigned by lia.
rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
pose proof (u8_range b). change (bv_modulus 64) with (2^64)%Z. lia. }
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite Hz, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
Lemma step_lb : forall segs regs pc mem rom w rd rs (imm : bv 12) b,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ1 true rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lb b)) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm b Hfetch Hecall Hdecode Hread.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite b_lb_val, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
Lemma step_lh : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ2 true rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lh v)) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), b_lh_val, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
Lemma step_lhu : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ2 false rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
assert (Hz : zext 64 (bv_extract 0 16 v) = v).
{ pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
pose proof (bytes_le_to_Z_bound bs) as Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
rewrite Hlen in Hb. rewrite Hv in Hb, Hnn.
apply bv_eq. unfold zext.
rewrite bv_zero_extend_unsigned by lia.
rewrite bv_extract_unsigned, Z.shiftr_0_r.
apply bv_wrap_small.
change (bv_modulus 16) with 65536%Z.
change (2 ^ (8 * Z.of_nat 2))%Z with 65536%Z in Hb. lia. }
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), Hz, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
Lemma step_lw : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v)) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
Lemma step_lwu : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ4 false rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
assert (Hz : zext 64 (bv_extract 0 32 v) = v).
{ pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
pose proof (bytes_le_to_Z_bound bs) as Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
rewrite Hlen in Hb. rewrite Hv in Hb, Hnn.
apply bv_eq. unfold zext.
rewrite bv_zero_extend_unsigned by lia.
rewrite bv_extract_unsigned, Z.shiftr_0_r.
apply bv_wrap_small.
change (bv_modulus 32) with 4294967296%Z.
change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z in Hb. lia. }
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), Hz, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
Lemma step_ld : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
assert (Hz : bv_extract 0 64 v = v).
{ apply bv_eq.
rewrite bv_extract_unsigned, Z.shiftr_0_r.
apply bv_wrap_bv_unsigned. }
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), Hz, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
Lemma two64_pos : ltac2:(TCodec.tc2 tcn__PropExec "7&U=z&UD+2+R0%3221%6251").
Proof. lia. Qed.
Lemma v_addi_nneg : ltac2:(TCodec.tc2 tcn__PropExec "Q0'WAyR0%211'N&U;zr1%3221&U=&U8&WKr3%22;1r2%5221&UD+2+R0%3221%;251'C&U4r4%221<%>2G1%?2H3%A21?%73H31p091p0F1p]4K1p`6M1").
Proof.
intros x imm Hi Hs. unfold v_addi.
rewrite Z_to_bv_unsigned, bv_wrap64_mod.
apply Z.mod_small. pose proof (u64_range x). lia.
Qed.
Lemma v_addi_0 : ltac2:(TCodec.tc2 tcn__PropExec ":'WAyR0%211'C&U4r1z%3221%53613p`671").
Proof.
intro x. apply bv_eq. unfold v_addi.
rewrite Z_to_bv_unsigned, Z.add_0_r. apply bv_wrap_bv_unsigned.
Qed.
Lemma v_add_small : ltac2:(TCodec.tc2 tcn__PropExec "L'WAyR0%211&U=&U8&WKr2%2261r1%4281%6231&UD+2+R0%3221%<251'C'N&U3r3%221>%@2D1%A2E3%C21@%83731p0:1p`:H1p`6I1").
Proof.
intros x y H. unfold v_add.
rewrite Z_to_bv_unsigned, bv_wrap64_mod.
apply Z.mod_small. pose proof (u64_range x). pose proof (u64_range y). lia.
Qed.
Lemma v_sub_small : ltac2:(TCodec.tc2 tcn__PropExec "G'WAyR0%211&U;&WKr1%2251r2%4271%6231'C'N&U6r3%2217%;2>1&UG%=2@4%221:%93841p0;1p`:C1p`6D1").
Proof.
intros x y H. unfold v_sub.
rewrite Z_to_bv_unsigned, bv_wrap64_mod.
apply Z.mod_small. pose proof (u64_range x). pose proof (u64_range y). lia.
Qed.
Lemma v_slli_3 : ltac2:(TCodec.tc2 tcn__PropExec "K'WAyR0%211&U=&U@+8&WKr1%2271%5241&UD+2+R0%3221%;251'C'N&U5r2+3%3221%?2D1%@2E4%C2B1%93831p0;1p`6H1").
Proof.
intros x H8. unfold v_slli.
rewrite Z_to_bv_unsigned, bv_wrap64_mod.
rewrite Z.shiftl_mul_pow2 by lia.
change (2^3)%Z with 8%Z.
pose proof (u64_range x).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma v_addi_0_1 : ltac2:(TCodec.tc2 tcn__PropExec "<'C'WAyR0%211&U4&W@z%2251+1%5221%5282%;3821").
Proof. apply bv_eq. reflexivity. Qed.
Lemma v_addi_0_64 : ltac2:(TCodec.tc2 tcn__PropExec "<'C'WAyR0%211&U4&W@z%2251+R0%5221%5282%;3821").
Proof. apply bv_eq. reflexivity. Qed.
Lemma v_addi_Sj : ltac2:(TCodec.tc2 tcn__PropExec "L';&U=&U8&UBr1%211+1%5221&UD+2+R0%3221%;251'C'WAyR0%211&U4&Q6r2%211%421?(2%114%611%<3941p0>1p]6K1").
Proof.
intros j _. apply bv_eq. unfold v_addi, nat_to_word.
rewrite !Z_to_bv_unsigned.
rewrite bv_wrap_add_idemp_l. f_equal. lia.
Qed.
Lemma bv_signed_small : ltac2:(TCodec.tc2 tcn__PropExec "E'WAyR0%211&U=&WKr1%2251&UD+2+QO%3221%8251'C'N&WIr2%22?1%=2@2%63521p081p`6B1").
Proof.
intros x Hx. unfold bv_signed. apply bv_swrap_small.
change (bv_half_modulus 64) with (2^63)%Z.
pose proof (u64_range x). lia.
Qed.
Lemma bv_signed_hi : ltac2:(TCodec.tc2 tcn__PropExec "I'WAyR0%211&U;&UD+2+QO%3221&WKr1%2291%8241'C'N&WIr2%22?1&UG%:2A3+R0%@2?1%4231%:3961p0<1p`6F1").
Proof.
intros x Hx. unfold bv_signed.
rewrite (bv_swrap_hi 64);
[ change (bv_modulus 64) with (2^64)%Z; reflexivity
| discriminate
| change (bv_half_modulus 64) with (2^63)%Z; lia
| change (bv_modulus 64) with (2^64)%Z; apply u64_range ].
Qed.
Lemma c_lts_small : ltac2:(TCodec.tc2 tcn__PropExec "I'WAyR0%211&U=&WKr2%2251&UD+2+QO%3221%8251'C'5&TIr4r3%3221&RO%13B43%83731p0:1p0;1p`:E1p`6F1").
Proof.
intros x y Hx Hy. unfold c_lts, bv_lts, bv_ltu.
rewrite !bv_signed_small by assumption. reflexivity.
Qed.
Lemma c_lts_neg_0 : ltac2:(TCodec.tc2 tcn__PropExec "H'WAyR0%211&U;&UD+2+QO%3221&WKr1%2291%8241'C'5&TIr2&W@z%22A1%5241(@%93821p0;1p`6E1").
Proof.
intros x Hx. unfold c_lts, bv_lts.
change (bv_signed (Z_to_bv 64 0)) with 0%Z.
rewrite bv_signed_hi by exact Hx.
apply Z.ltb_lt. pose proof (u64_range x). lia.
Qed.
Lemma c_lts_pos_0 : ltac2:(TCodec.tc2 tcn__PropExec "H'WAyR0%211&U=&WKr1%2251&UD+2+QO%3221%8251'C'5&TIr2&W@z%22A1%5241(7%93821p0;1p`6E1").
Proof.
intros x Hx. unfold c_lts, bv_lts.
change (bv_signed (Z_to_bv 64 0)) with 0%Z.
rewrite bv_signed_small by exact Hx.
apply Z.ltb_ge. pose proof (u64_range x). lia.
Qed.
Lemma c_lts_0_pos : ltac2:(TCodec.tc2 tcn__PropExec "N'WAyR0%211&U;+1&WKr1%2261%5241&U=r2%62:1&UD+2+QO%3221%7251'C'5&TI&W@z%22E1r3%5221(@%93821p0;1p0D1p]FK1").
Proof.
intros n H1 H2.
rewrite c_lts_small;
[ unfold bv_ltu; apply Z.ltb_lt;
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia
| change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia
| lia ].
Qed.
Lemma errno_ret_range : ltac2:(TCodec.tc2 tcn__PropExec "L'N&U;+1r1%3221r2+SoO%6221'B&UD+2+QO%3221&WKyR0&QOr3%211%5241%B271&U=+R0%=2<1%3251%@251p0B1p0F1p\JK1").
Proof.
intros e H1 H2. unfold errno_ret.
rewrite Z_to_bv_unsigned, bv_wrap64_mod.
replace (- e)%Z with ((2^64 - e) + (-1) * 2^64)%Z by lia.
rewrite Z_mod_plus_full.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma errno_ret_signed : ltac2:(TCodec.tc2 tcn__PropExec "E'N&U;+1r1%3221r2+SoO%6221'C&WIyR0&QOr3%211%5241&UC%114%93A31p0;1p0?1p\JD1").
Proof.
intros e H1 H2.
destruct (errno_ret_range e H1 H2) as [Hlo Hhi].
rewrite bv_signed_hi by exact Hlo.
unfold errno_ret in *.
rewrite Z_to_bv_unsigned, bv_wrap64_mod in *.
replace (- e)%Z with ((2^64 - e) + (-1) * 2^64)%Z by lia.
rewrite Z_mod_plus_full.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma c_lts_errno : ltac2:(TCodec.tc2 tcn__PropExec "H'N&U;+1r1%3221r2+SoO%6221'C'5&TI&QOr3%211&W@yR0z%3221%8251(@%<3;21p0>1p0B1p\JG1").
Proof.
intros e H1 H2. destruct (errno_ret_range e H1 H2) as [Hlo _].
apply c_lts_neg_0; assumption.
Qed.
Lemma c_eq_small : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C'5&THr2r1%3221&RN%13943%83731p`::1p`6;1").
Proof. reflexivity. Qed.
Lemma c_ltu_small : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C'5&TJr2r1%3221&RO%13943%83731p`::1p`6;1").
Proof. reflexivity. Qed.
Lemma c_eq_0_false : ltac2:(TCodec.tc2 tcn__PropExec "F'WAyR0%211&E'C'N&WKr1%2271z%63521%811'5&THr2&W@%12?7%4231(7%?3721p091p`6C1").
Proof.
intros x Hnz. unfold c_eq, bv_eqb. apply Z.eqb_neq.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. exact Hnz.
Qed.
Lemma c_eq_0_of_u : ltac2:(TCodec.tc2 tcn__PropExec "D'WAyR0%211'C'N&WKr1%2261z%63521'5&THr2&W@%12=6%4231(@%>3721p091p`6A1").
Proof.
intros x Hx. unfold c_eq, bv_eqb. rewrite Hx. reflexivity.
Qed.
Lemma c_eq_0_true : ltac2:(TCodec.tc2 tcn__PropExec ":'C'5&TH&W@yR0z%3221%5211(@%93821").
Proof. reflexivity. Qed.
Lemma c_eq_neq : ltac2:(TCodec.tc2 tcn__PropExec "F'WAyR0%211&E'C'N&WKr2%2271r1%4291%73631%911'5&THr3%2219(7%>3521p071p`:B1p`6C1").
Proof. intros x y Hne. unfold c_eq, bv_eqb. apply Z.eqb_neq. exact Hne. Qed.
Lemma c_eq_refl : ltac2:(TCodec.tc2 tcn__PropExec ";'WAyR0%211'C'5&THr1%2211(@%63521p`681").
Proof. intro x. apply bv_eqb_refl. Qed.
Lemma getr_same : ltac2:(TCodec.tc2 tcn__PropExec "K&S0y5'WAyR0%211%5241%415&E'Cr2(W?z(A%33<21%63851%811&TN&U1r4r3%3321;%5212%>3B1=p081p`2D1p^6C1p^>E1").
Proof.
intros regs r v H. unfold getr, regupd, reg_get.
rewrite (bv_eqb_neq r 0 H), bvmap_get_set_same. reflexivity.
Qed.
Lemma getr_other : ltac2:(TCodec.tc2 tcn__PropExec "K&S0y5'WAyR0%211%5241%415&E'Cr1r3%33521%511&TN&U1r5r4%33217r2%6221%7252%=3A21p0:1p^8A1p`2D1p^6C1p^>E1").
Proof.
intros regs r v r' H. unfold getr, regupd, reg_get.
destruct (bv_eqb r' 0); [reflexivity|].
rewrite bvmap_get_set_other by congruence. reflexivity.
Qed.
Lemma getr_nz : ltac2:(TCodec.tc2 tcn__PropExec "J&S0y5'WAyR0%211%5241%415&E'Cr1(W?z(A%33<21%63851%811&TNr3r2%3221&S:%1243%>3B31p081p^6B1p^>D1").
Proof.
intros regs r H. unfold getr. rewrite (bv_eqb_neq r 0 H). reflexivity.
Qed.
Lemma regupd_other : ltac2:(TCodec.tc2 tcn__PropExec "K&S0y5'WAyR0%211%5241%415&E'Cr1r3%33521%511&S:&U1r5r4%33217r2%6221%7252%=3A21p0:1p^8A1p`2D1p^6C1p^>E1").
Proof.
intros regs r v r' H. unfold regupd, reg_get.
rewrite bvmap_get_set_other by congruence. reflexivity.
Qed.
Lemma regupd_same : ltac2:(TCodec.tc2 tcn__PropExec "C&S0y5'WAyR0%211%5241%415'C&S:&U1r3r2r1%43321%6213%83;13p`2<1p^6;1p^>=1").
Proof.
intros. unfold regupd, reg_get. rewrite bvmap_get_set_same. reflexivity.
Qed.
End WithFP2.
Ltac split_value_ifs :=
repeat match goal with
| |- context [if ?b then _ else _] =>
lazymatch type of b with
| bool =>
lazymatch b with
| true => fail
| false => fail
| _ => destruct b
end
end
end.
Section WithFP3.
Context {fx : FPState}.
Lemma bytes_le_single : ltac2:(TCodec.tc2 tcn__PropExec "@'WAy8%211'C'N&Q0(6r1(<%117%43831%611&WK%12<6%;3:31p[N=1").
Proof. intro b. cbn. apply Z.lor_0_r. Qed.
Lemma bv_wrap8_mod : ltac2:(TCodec.tc2 tcn__PropExec ">'N'C&WLy8r1%3221&U?&UD+2+8%3221%5271%;3<71p`>=1").
Proof. reflexivity. Qed.
Lemma bytes_le_Z_to_le : ltac2:(TCodec.tc2 tcn__PropExec "K';'N&U;zr1%3221'C&Q0&Or3r2%3221%511&U?&UD+2&U@+8&UB%11:%4231%7261%92<1%A3F;1p0C1p`>H1p]8J1").
Proof.
induction k as [|k IH]; intros z Hz.
- cbn. change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.mod_1_r. reflexivity.
- cbn [Z_to_le_bytes bytes_le_to_Z].
rewrite IH by (apply Z.shiftr_nonneg; lia).
rewrite Z_to_bv_unsigned, bv_wrap8_mod.
replace (8 * Z.of_nat (S k))%Z with (8 * Z.of_nat k + 8)%Z by lia.
pose proof (Nat2Z.is_nonneg k).
apply Z.bits_inj'. intros i Hi.
rewrite Z.lor_spec, Z.shiftl_spec by lia.
destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
+ rewrite (Z.mod_pow2_bits_low z 8 i) by lia.
rewrite (Z.mod_pow2_bits_low z (8 * Z.of_nat k + 8) i) by lia.
rewrite (Z.testbit_neg_r _ (i - 8)) by lia.
apply orb_false_r.
+ rewrite (Z.mod_pow2_bits_high z 8 i) by lia.
rewrite orb_false_l.
destruct (Z.lt_ge_cases i (8 * Z.of_nat k + 8)) as [Hik|Hik].
* rewrite (Z.mod_pow2_bits_low _ (8 * Z.of_nat k) (i - 8)) by lia.
rewrite Z.shiftr_spec by lia.
rewrite (Z.mod_pow2_bits_low z (8 * Z.of_nat k + 8) i) by lia.
f_equal. lia.
* rewrite (Z.mod_pow2_bits_high _ (8 * Z.of_nat k) (i - 8)) by lia.
rewrite (Z.mod_pow2_bits_high z (8 * Z.of_nat k + 8) i) by lia.
reflexivity.
Qed.
Lemma bytes_le_N : ltac2:(TCodec.tc2 tcn__PropExec "K';'WAyR0%211'C'N&Q0&QBr2r1%3221%511&U?&WK%12<5&UD+2&U@+8&UB%11<%4231%7261%;291%D3C=1p`2F1p]8J1").
Proof.
intros k v. unfold word_to_le_bytes.
apply bytes_le_Z_to_le. apply u64_range.
Qed.
Lemma n_to_le_8_spec : ltac2:(TCodec.tc2 tcn__PropExec "@'WAyR0%211'C':y8%611%311&Q7r1%211&QBu8%2214%;3741p`2=1").
Proof. reflexivity. Qed.
Lemma bytes_le_n_to_le_8 : ltac2:(TCodec.tc2 tcn__PropExec ">'WAyR0%211'C'N&Q0&Q7r1%211%411&WK%12:4%93831p`2;1").
Proof.
intro v. rewrite n_to_le_8_spec, bytes_le_N.
change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z.
apply Z.mod_small. apply u64_range.
Qed.
Lemma nth_error_skipn_cons : forall {A} (bs : list A) d, (d < length bs)%nat ->
exists b, nth_error bs d = Some b /\ skipn d bs = b :: skipn (S d) bs.
Proof.
intros A bs. induction bs as [|x bs IH]; intros d Hd; [cbn in Hd; lia|].
destruct d as [|d'].
- exists x. split; reflexivity.
- cbn [length] in Hd. destruct (IH d' ltac:(lia)) as [b [H1 H2]].
exists b. split; [exact H1|]. cbn [skipn]. exact H2.
Qed.
Lemma u_add1 : ltac2:(TCodec.tc2 tcn__PropExec "M'WAyR0%211&U=&U8&WKr1%2261+1%5221&UD+2+R0%3221%;251'C'N&WBr2(W?(A%23D=1%53E41%B2F1%C2G6%E21A%;3:31p0=1p[FJ1").
Proof.
intros a Ha. rewrite bv_add_unsigned.
change (bv_unsigned (1 : word)) with 1%Z.
rewrite bv_wrap64_mod. apply Z.mod_small.
pose proof (u64_range a). lia.
Qed.
Lemma rdn_stack : ltac2:(TCodec.tc2 tcn__PropExec "R8':'Q9%211'WAyR0%211y8%411%811';&U;&WKr4%2291r1%42;1%6231'H&F&UI&UGr2%;2B1r5%=2D1%5231%711r3%:221&9%12GB%>231&U=&U8r6%H2O1&UB%82N>%211%6241&UD+2+R0%3221%<251'C'=%11Q7&U0r8&QMr7%221B%5441Q9N(3&J&L%Q>2QE6%Q62Q=1%Q811%43QE1J%63QFQ61%82QF1%B3@:1p0D1p0Q21p0QB1p[JQN1p]8QK1p\DQM1p^NR11p^LR51").
Proof.
intros segs sp bytes k. induction k as [|k IH]; intros addr Hsp Hlen Hnw.
- cbn. reflexivity.
- cbn [rdn].
destruct (nth_error_skipn_cons bytes (Z.to_nat (bv_unsigned addr - bv_unsigned sp)) ltac:(lia)) as [b [Hnth Hskip]].
unfold stack_to_mem.
assert (Hle : Z.leb (bv_unsigned sp) (bv_unsigned addr) = true) by (apply Z.leb_le; lia).
rewrite Hle.
assert (Hlt : Z.ltb (bv_unsigned addr - bv_unsigned sp) (Z.of_nat (length bytes)) = true)
by (apply Z.ltb_lt; lia).
rewrite Hlt. rewrite Hnth.
assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z) by (apply u_add1; lia).
rewrite IH by lia.
rewrite Hskip.
replace (Z.to_nat (bv_unsigned (addr + 1) - bv_unsigned sp))
with (S (Z.to_nat (bv_unsigned addr - bv_unsigned sp))) by lia.
reflexivity.
Qed.
Lemma rdn_ext : ltac2:(TCodec.tc2 tcn__PropExec "QJ':'Q9%211';'WAyR0%211'=y8%511%311p`651&U;&U8&WKr1%22;1&UBr4%211%7241&UD+2+R0%3221%=251'Br3%>2G1%A21=&U=r6%?11%D251%42B1%9261'Cr2%711r5%113%53O31p071p`6Q51%Q<1Q3%Q611&U0r7%2419EA%342OFB%>3521p081p0K1p[FQ?1p]@Q;1p]>Q<1p]8QE1p^LQG1").
Proof.
intros segs k. induction k as [|k IH]; intros m1 m2 a Hnw Hext; [reflexivity|].
cbn [rdn].
rewrite (Hext a ltac:(pose proof (u64_range a); lia)).
destruct k as [|k'].
- reflexivity.
- assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
rewrite (IH m1 m2 (a+1) ltac:(lia)
ltac:(intros x Hx; apply Hext; lia)).
reflexivity.
Qed.
Lemma length_n_to_le_8 : ltac2:(TCodec.tc2 tcn__PropExec "?'WAyR0%211'C';&9y8%711&Q7r1%211%6241u8%:3921p`2<1").
Proof. reflexivity. Qed.
Lemma length_flat_map_le8 : ltac2:(TCodec.tc2 tcn__PropExec "E':'WAyR0%211%411'C';&9y8%811&U7&Q7r1%34:421%7251&Gu8%:2>5%3221%>3=51p]:@1").
Proof.
induction l as [|x l IH]; [reflexivity|].
cbn [flat_map length]. rewrite length_app, IH, length_n_to_le_8. lia.
Qed.
Definition total_arg_bytes_nat (args : list (list byte)) : nat :=
fold_right (fun a acc => length a + 1 + acc)%nat 0%nat args.
Lemma total_arg_bytes_Z : ltac2:(TCodec.tc2 tcn__PropExec "A':'WAy8%211%411%511'C'N&QIr1%211&UB&TE%114%311%93851p]:;1").
Proof.
induction l as [|x l IH]; [reflexivity|].
cbv [total_arg_bytes total_arg_bytes_nat] in *. cbn [fold_right].
rewrite IH. lia.
Qed.
Lemma length_flatten_strings : ltac2:(TCodec.tc2 tcn__PropExec "A':'WAy8%211%411%511'C';&9&QLr1%211%4291&TE%114%93831p]:;1").
Proof.
induction l as [|x l IH]; [reflexivity|].
cbv [flatten_strings total_arg_bytes_nat] in *. cbn [flat_map fold_right].
rewrite length_app, IH. rewrite length_app. cbn [length]. lia.
Qed.
Lemma len_word_nat : forall {A} (l : list A), len_word l = nat_to_word (length l).
Proof. reflexivity. Qed.
Lemma word1_nat : ltac2:(TCodec.tc2 tcn__PropExec "='C'WAyR0%211(W?+1(A%33521/015&Q6u1%211%<3941").
Proof. apply bv_eq. reflexivity. Qed.
Lemma word_add_0 : ltac2:(TCodec.tc2 tcn__PropExec "<'WAyR0%211'C&WBr1&Q6(1%211%53841%73815p[F91").
Proof.
intro a. apply bv_eq. unfold nat_to_word.
rewrite bv_add_unsigned, Z_to_bv_unsigned.
change (bv_wrap 64 (Z.of_nat 0)) with 0%Z.
rewrite Z.add_0_r. apply bv_wrap_bv_unsigned.
Qed.
Lemma nat_to_word_merge : ltac2:(TCodec.tc2 tcn__PropExec "B';'C'WAyR0%211&WB&Q6r2%211r1%411%63831&F%1264%811%>3;41p]8@1p]<A1").
Proof.
intros m k. apply bv_eq. unfold nat_to_word.
rewrite bv_add_unsigned, !Z_to_bv_unsigned.
rewrite bv_wrap_add_idemp_l, bv_wrap_add_idemp_r.
f_equal. lia.
Qed.
Lemma nat_to_word_add_merge : ltac2:(TCodec.tc2 tcn__PropExec "F'WAyR0%211';'C&WBr3&Q6r2%211%53941r1%511%83<31&F%1274%911%<3@;1%>3@51p]8@1p]<A1p[FC1").
Proof.
intros a m k.
rewrite <- (assoc_L bv_add).
rewrite nat_to_word_merge. reflexivity.
Qed.
Lemma string_addrs_fst_structure : forall strs (base : word),
fst (string_addrs base strs) =
match strs with
| [] => []
| s :: rest => base :: fst (string_addrs (base + len_word s + 1) rest)
end.
Proof.
intros strs base. destruct strs as [|s rest]; [reflexivity|].
cbn [string_addrs].
destruct (string_addrs (base + len_word s + 1) rest) as [ptrs fin] eqn:E.
reflexivity.
Qed.
Lemma string_addrs_pair : ltac2:(TCodec.tc2 tcn__PropExec "M':'WAy8%211%411%511yR0%611'C'?%:13%2214&QNr1r2%3221(>&8%138;3&WB&Q6&TE%118%311%53B;1%94?B71%B3?;1p\@D1p_LG1").
Proof.
induction strs as [|s rest IH]; intro base.
- cbn. rewrite word_add_0. reflexivity.
- cbn [string_addrs].
rewrite (IH (base + len_word s + 1)).
cbn [fst]. f_equal.
rewrite len_word_nat, word1_nat, !nat_to_word_add_merge.
cbv [total_arg_bytes_nat]. cbn [fold_right]. f_equal. f_equal. lia.
Qed.
Lemma length_string_addrs_fst : ltac2:(TCodec.tc2 tcn__PropExec "G':'WAy8%211%411%511yR0%611'C';&9&8%<15&QNr1r2%3221%635:1%82;1%92?4%<3;21p\@>1p_LA1").
Proof.
induction strs as [|s rest IH]; intro base; [reflexivity|].
rewrite string_addrs_fst_structure. cbn [length]. rewrite IH. reflexivity.
Qed.
Lemma build_stack_bytes_within_span : ltac2:(TCodec.tc2 tcn__PropExec "Q2'Q8'WAyR0%211':y8%511%311%411'QJ&U;&UB&9&QKr7r6r5r4r3r2r1%877654321%:2@1%<11&QG%1298%@231p^@B1p]0I1p`0J1p\JF1p[FG1p^NM1p^0Q11").
Proof.
intros ph sp a e uid hw rnd.
unfold entry_stack_span, build_stack_bytes. cbv zeta.
rewrite (string_addrs_pair a). cbv beta iota.
rewrite (string_addrs_pair e). cbv beta iota.
rewrite !length_app, repeat_length, !length_flat_map_le8,
!length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes,
!length_flatten_strings, length_at_random_bytes.
rewrite !total_arg_bytes_Z.
match goal with
| |- context [Z.to_nat ?pd] =>
assert (Hpd : (0 <= pd < 8)%Z) by (apply Z.mod_pos_bound; lia)
end.
unfold auxv_size. lia.
Qed.
Lemma bsb_argc_prefix : ltac2:(TCodec.tc2 tcn__PropExec "Q6'Q8'WAyR0%211':y8%511%311%411'QJ'D'C&QKr8r7r6r5r4r3r2%877654321&4&Q7&Q5%12A9%311r1%63E21%A3E81q_NF1%D2G1p^@F1p]0M1p`0N1p\LJ1p[LK1p^NQ11p^0Q51").
Proof.
intros ph sp argv envp uid hw rnd. unfold build_stack_bytes.
rewrite (string_addrs_pair argv). cbv beta iota.
rewrite (string_addrs_pair envp). cbv beta iota.
eexists. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma read_at_offset : ltac2:(TCodec.tc2 tcn__PropExec "QO':'Q9%211'WAyR0%211y8%411%811';'Cr5&4r4r3r2%43921%53:41%83:71&9%12=7%;3<16&U=&U8&WKr8%22F1&UBr7%:2F1%311%8251&UD+2+R0%3221%>251'=%11N&U0r:&QMr9%221B&WB&Q6%11A%33Q;51%94851Q3(3r6%22Q;1%Q:3>41p0A1p0Q11p0Q51p]8Q?1p^2QA1p]DQB1p^4QC1p\DQD1p^NQH1p^LQL1").
Proof.
intros segs sp bytes pre mid post k Hb Hk Hnw.
pose proof (u64_range sp) as Hsp64.
assert (Hlenpre : (length pre <= length bytes)%nat)
by (rewrite Hb, !length_app; lia).
assert (Hu : bv_unsigned (sp + nat_to_word (length pre)) = (bv_unsigned sp + Z.of_nat (length pre))%Z).
{ unfold nat_to_word. rewrite bv_add_unsigned, Z_to_bv_unsigned.
rewrite bv_wrap_add_idemp_r, bv_wrap64_mod.
apply Z.mod_small. lia. }
assert (Hsp : (bv_unsigned sp <= bv_unsigned (sp + nat_to_word (length pre)))%Z) by lia.
assert (Hlen : (Z.to_nat (bv_unsigned (sp + nat_to_word (length pre)) - bv_unsigned sp) + k <= length bytes)%nat)
by (rewrite Hu, Hb, !length_app; lia).
rewrite (rdn_stack segs sp bytes k _ Hsp Hlen Hnw).
rewrite Hu.
replace (Z.to_nat (bv_unsigned sp + Z.of_nat (length pre) - bv_unsigned sp)) with (length pre) by lia.
rewrite Hb, skipn_app, skipn_all, Nat.sub_diag.
cbn [app]. rewrite skipn_O.
rewrite firstn_app, <- Hk, firstn_all, Nat.sub_diag.
cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.
Lemma rdn_image_in_block : ltac2:(TCodec.tc2 tcn__PropExec "R6':'Q9%211'Q8'WAyR0%211y8%411%911%:11'QJ';&U;&U8&WKr2%22<1&UBr1%211%7241&QCr8&QKr9r7r6r5r4r3%776854321%:291%D2<1%C2M4%A1C%F221&UD+2+R0%3221%L251'C'=%11Q3&U0r<&QMr:&QFr;%2713JLIHG%5241%8471HG%N746MOLKJ%8271%;4:1KJ%?3=41p0A1p0J1p]FQ@1p[FQG1p\HQC1p]2QI1p`0QJ1p\LQG1p[LQH1p^NQM1p^0R11p^LR31").
Proof.
intros segs ph sp argv envp uid hwcap draw a n Hin Hnw.
apply rdn_ext; [exact Hnw|].
intros x Hx. apply stack_to_mem_image_in_block. lia.
Qed.
Lemma read_at_offset_image : ltac2:(TCodec.tc2 tcn__PropExec "RB':'Q9%211'Q8'WAyR0%211y8%411%911%:11'QJ';'C&QKr;r:r9r8r7r6r5%877654321&4r4r3r2%43C21%53D41%@3D71&9%12G7%C3D16&U=&U8&WKr<%22Q01&UBr=%J714IHGFE%;2Q11%411%9261&UD+2+R0%3221%?251'=%11Q9&U0r?&QM&QFr>%271ADQ9Q8Q7Q6%42B1&WB&Q6%N2QDQ9%211%43QIG1%<4;61Q7(3%12QHQ=%QE3@31p0C1p0Q41p0Q81p]8QJ1p^2QN1p]DQO1p^4R01p\HQO1p]2R51p`0R61p\LR31p[LR41p^NR91p^0R=1p^LR?1").
Proof.
intros segs ph sp argv envp uid hwcap draw pre mid post k Hb Hk Hnw.
pose proof (u64_range sp) as Hsp64.
assert (Hlen : (length pre + length mid <= length (build_stack_bytes ph sp argv envp uid hwcap draw))%nat)
by (rewrite Hb, !length_app; lia).
assert (Hu : bv_unsigned (sp + nat_to_word (length pre))
= (bv_unsigned sp + Z.of_nat (length pre))%Z).
{ unfold nat_to_word. rewrite bv_add_unsigned, Z_to_bv_unsigned.
rewrite bv_wrap_add_idemp_r, bv_wrap64_mod. apply Z.mod_small. lia. }
rewrite rdn_image_in_block
by (unfold entry_block_top; rewrite Hu; lia).
exact (read_at_offset segs sp _ pre mid post k Hb Hk Hnw).
Qed.
Lemma read_argc : ltac2:(TCodec.tc2 tcn__PropExec "QO'Q8':'Q9%211'WAyR0%211y8%411%811%911'QJ&U=&U8&WKr6%22;1&UB&9&QKr8r5r4r3r2r1%776;54321%92C1%;11%@2=1&UD+2+R0%3221%F251'C'=%11L&U0&QMr7&QFr9%2713LFEDC%5241u8%84J261(3&Q7&Q5%12Q9Q3%311%52Q;1%B3@71p0D1p^@Q<1p]0QB1p`0QC1p\LQ@1p[LQA1p^NQF1p^LQJ1p^0QN1").
Proof.
intros ph segs sp argv envp uid hw rnd Hnw.
destruct (bsb_argc_prefix ph sp argv envp uid hw rnd) as [tl E].
pose proof (read_at_offset_image segs ph sp argv envp uid hw rnd [] (word_le8 (len_word argv)) tl 8%nat) as H.
cbn [length] in H.
rewrite word_add_0 in H.
apply H; [rewrite E; reflexivity|reflexivity|exact Hnw].
Qed.
Lemma read_byte_at : ltac2:(TCodec.tc2 tcn__PropExec "R<':'Q9%211'WAyR0%211y8%411%811';'Cr5&4r4r3r2%43921%53:41%83:71&I&9%12>8%3271&U=&U8&WKr8%22G1&UBr7%:2G1%311%8251&UD+2+R0%3221%>251'=%11O&U0r:&QMr9%221B&WB&Q6&F%12BQ3%311%53Q>71u1%<4;821(3(6&Kr6&W@z%22QE1%54QEQ?41(<%11QG%93QH31%;2QH1%QG3J=1p0M1p0Q=1p0QB1p]6QL1p^2QN1p^JQO1p^4R01p\DR11p^NR51p^LR91").
Proof.
intros segs sp bytes pre s post j Hb Hj Hnw.
destruct (nth_error_skipn_cons s j Hj) as [b [Hnth Hskip]].
assert (Hsj : s = firstn j s ++ b :: skipn (S j) s)
by (rewrite <- Hskip; symmetry; apply firstn_skipn).
pose proof (read_at_offset segs sp bytes (pre ++ firstn j s) [b] (skipn (S j) s ++ post) 1%nat) as H.
rewrite length_app in H.
rewrite firstn_length_le in H by lia.
replace (nth j s (Z_to_bv 8 0)) with b by (symmetry; apply (nth_error_nth _ _ _ Hnth)).
apply H; [|reflexivity|exact Hnw].
rewrite Hb. rewrite Hsj at 1. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma read_byte_at_image : ltac2:(TCodec.tc2 tcn__PropExec "RO':'Q9%211'Q8'WAyR0%211y8%411%911%:11'QJ';'C&QKr;r:r9r8r7r6r5%877654321&4r4r3r2%43C21%53D41%@3D71&I&9%12H8%3271&U=&U8&WKr<%22Q11&UBr=%K714JIHGF%;2Q21%411%9261&UD+2+R0%3221%?251'=%11Q:&U0r?&QM&QFr>%271ADQ:Q9Q8Q7%42B1&WB&Q6&F%O2QFQ;%221Q7%411%63QLI1u1%?4>921(3(6&K&W@z%22R21%44R2QBQF1(<%11R4%83R531%:2R51%R23L<1p0O1p0Q@1p0QE1p]6R71p^2R;1p^JR<1p^4R=1p\HR<1p]2RB1p`0RC1p\LR@1p[LRA1p^NRF1p^0RJ1p^LRL1").
Proof.
intros segs ph sp argv envp uid hwcap draw pre s post j Hb Hj Hnw.
destruct (nth_error_skipn_cons s j Hj) as [b [Hnth Hskip]].
assert (Hsj : s = firstn j s ++ b :: skipn (S j) s)
by (rewrite <- Hskip; symmetry; apply firstn_skipn).
pose proof (read_at_offset_image segs ph sp argv envp uid hwcap draw
(pre ++ firstn j s) [b] (skipn (S j) s ++ post) 1%nat) as H.
rewrite length_app in H.
rewrite firstn_length_le in H by lia.
replace (nth j s (Z_to_bv 8 0)) with b by (symmetry; apply (nth_error_nth _ _ _ Hnth)).
apply H; [|reflexivity|exact Hnw].
rewrite Hb. rewrite Hsj at 1. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma nth_app0_bound : ltac2:(TCodec.tc2 tcn__PropExec "J':'WAy8%211%411';&U=&WK&Kr1&4r2(6&W@z%22=1(<%11>%63?31%93@81%<4A;15%>2C1+X0%A221p]6C1p[HE1").
Proof.
intros a1 j. apply u8_range.
Qed.
Lemma entry_page_top_within_window : ltac2:(TCodec.tc2 tcn__PropExec "Q2'Q8'WAyR0%211':y8%511%311%411'QJ&QEr6r5r4%43321&U;&QDr7&QKr8r3r2%4735;:921%7261&R0%:221p0<1p\HB1p]2I1p`0J1p\LF1p[LG1p^NM1p^0Q11").
Proof.
intros ph sp argv envp uid hwcap draw Hfit.
pose proof (build_stack_bytes_within_span ph sp argv envp uid hwcap draw) as Hlen.
unfold entry_stack_fits in Hfit. unfold entry_page_top.
apply page_round_up_Z_le; [ unfold entry_block_top; lia | reflexivity ].
Qed.
Definition wrap_mem (ph : PhdrInfo) (sp : word) (argv envp : list (list byte))
(uid : word) (hw : word) (rnd : EntryDraw) : word -> option byte :=
fun addr =>
match stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) addr with
| Some b => Some b
| None =>
if andb (Z.leb (bv_unsigned sp - stack_max_size) (bv_unsigned addr))
(Z.ltb (bv_unsigned addr) (bv_unsigned sp))
then Some (Z_to_bv 8 0) else None
end.
Lemma init_mkst : ltac2:(TCodec.tc2 tcn__PropExec "QM':'Q9%211'M'Q8'WAyR0%211y8%411%:11%;11'QJ'C'Q?&QHr9r8r7r6r1r5r4r3r2%:9987654321&TO&TM&U1&S1y5%221H(W?+:(A%33521&W@z%22Q01%;3841+2%93;17%>331G&UA%11K%92Q71&TF%17MLJIHGK&U2%11Q1%H5G8531%Q63Q5J1p^@Q81p]0Q>1p`0Q?1p\LQ<1p[LQ=1p^NQB1p^0QF1p]NQH1p^LQJ1").
Proof. intros. reflexivity. Qed.
Lemma wrap_above_sp : ltac2:(TCodec.tc2 tcn__PropExec "Q:'Q8'WAyR0%211':y8%511%311%411'QJ&U;&WKr7%22;1r4%42=1%6231'C'=%11=&TFr9r8r6r3r2r5%7865?4=321&QM&QF%1798B7@65%33915%?3=51p0A1p^@I1p]0Q01p`0Q11p`6Q21p\LN1p[LO1p^NQ51p^0Q91").
Proof.
intros ph sp argv envp x uid hw rnd Hx. unfold wrap_mem.
destruct (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) x) as [b|] eqn:E; [reflexivity|].
assert (Hltf : Z.ltb (bv_unsigned x) (bv_unsigned sp) = false) by (apply Z.ltb_ge; lia).
rewrite Hltf, andb_false_r. reflexivity.
Qed.
Lemma rdn_wrap_stack_above : ltac2:(TCodec.tc2 tcn__PropExec "QO':'Q9%211'Q8'WAyR0%211y8%411%911%:11';'QJ&U;&WKr8%22;1r5%42=1%6231&U8r6%82A1&UB%117%5231&UD+2+R0%3221%A251'C'=%11H&U0r<&TFr;r:r9r4r3%67543KI21r7%:4921G&QM&QF%17:98Q0N76%32:1%?4>16L%C3A61p0E1p0Q11p^@Q91p]0Q@1p`0QA1p]FQ=1p[FQC1p\LQ@1p[LQA1p^NQF1p^0QJ1p^LQL1").
Proof.
intros segs ph sp argv envp a n uid hw rnd Hsp Hnw.
apply rdn_ext; [exact Hnw|].
intros x Hx. apply wrap_above_sp. lia.
Qed.
End WithFP3.
