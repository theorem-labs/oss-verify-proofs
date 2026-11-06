(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import MuslStrlen.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv
SymExec SymExec2 SymExec2Sound SymRun SymDrive
MemSplit RefLayout StartupTac Ju0StartupDefs Ju0Startup Ju0StartupFacts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0MainEntry () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Hexadecimal."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Number."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0MainEntry.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0StartupDefs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0StartupFacts."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2D0"; "2D1"; "2D4"]; ["2Nil"; "3I"; "3and"; "3eq"; "4add"; "4of_num_uint"; "5UIntHexadecimal"; "6le"; "6lt"; "7firstn"; "7nth"; "7skipn"; "8Z"; "0E"; "9Segment"; "9ph_addr"]; ["9ph_ent"; "9ph_num"; ":word_to_le_bytes"; ";entry_stack_fits"; ";entry_stack_image"; ";valid_argv"; "<at_random_bytes"; "<ed_random"; "<stack_to_mem"; "=bvmap"; "0R"; ">cat_argv_ptr"; "?all_regs"; "?auxvp"; "?kn_auxv"; "?kn_image"]; ["?kn_main"; "?kn_stack"; "?p0"; "?p1"; "?rnd"; "?spx"; "?sr_main"; "@D_main"; "AD_main_missb"; "Arange_disjoint_b"; "Bgetr"; "Brdn"; "Bseg_rom"; "Cauxv_off"; "Cauxv_words"; "Dwseg_ok"]; ["Ejunk_vals"; "FELit"; "FKImg"; "Fedenot"; "Fenv"; "Fev"; "Fexpr"; "Gkentry_ok"; "Gknow_ok"; "Gregs_ok"; "Hloaded_segments"; "Hphdrs"; "Iadd"; "Ile"; "Ilt"; "Imodulo"]; ["Imul"; "Iof_N"; "Iof_nat"; "Ipow"; "Isub"; "Ito_nat"; "0a"; "0a0s"; "0av"; "0bs"; "0c"; "0envv"; "0ev"; "0hi"; "0hw"; "0i"]; ["0j"; "0k"; "0lo"; "0m"; "0mem"; "0n"; "0path"; "0rdraw"; "0regs"; "0rnd"; "0segs"; "0sp0"; "0sr"; "JBV"; "JZ_to_bv"; "Jbv"]; ["Jbv_unsigned"; "0tid"; "0uid"]]).
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_D_main_none := (ltac2:(TCodec.tc2 tcn__Ju0MainEntry "QH'S?yR0%211'7y8%511%311%411yT0%911'L&Q5r6%211&R=+SoonPPPPP0&S@r8%22A1%5241r9%52D1+TPPPPPPPP0%9221'C'4&QHr4u1%3221(<%73621':%11L&QGr;r:r7&S>r5%22Q71%7765EH4M1(0%11Q6%D3;31p0>1p0G1p0L1p0Q31pV0Q71pW4Q@1pVDQ:1pUNQB1pUJQ>1pUBQ?1pVHQE1")) (only parsing).
Variable sp0 : ltac:(sec_ty2 constr:(SEC_T_D_main_none) 0%nat 0%nat).
Variable av : ltac:(sec_ty2 constr:(SEC_T_D_main_none) 1%nat 0%nat).
Variable ev : ltac:(sec_ty2 constr:(SEC_T_D_main_none) 2%nat 0%nat).
Variable hw : ltac:(sec_ty2 constr:(SEC_T_D_main_none) 3%nat 0%nat).
Variable rnd : ltac:(sec_ty2 constr:(SEC_T_D_main_none) 4%nat 0%nat).
Variable tid : ltac:(sec_ty2 constr:(SEC_T_D_main_none) 5%nat 0%nat).
Variable i : ltac:(sec_ty2 constr:(SEC_T_D_main_none) 6%nat 0%nat).
Lemma D_main_none : ltac:(sec_stmt2 constr:(SEC_T_D_main_none) 7%nat 0%nat).
Proof.
intros Hva Hlo Hhi Hb.
pose proof (u64_range tid) as Ht. pose proof (u64_range hw) as Hhw.
unfold D_main_missb, D_main_cells in Hb. cbn [forallb] in Hb.
repeat match goal with
| H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H as [? ?]
end.
repeat match goal with
| H : range_disjoint_b _ _ _ = true |- _ =>
apply range_disjoint_djw in H; cbn [fst snd] in H
| H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
| H : true = true |- _ => clear H
end.
assert (Hui : bv_unsigned (Z_to_bv 64 i) = i) by (apply u_small; lia).
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
Time repeat (rewrite MemSplit.wbytes_outside;
[ | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by (cbn; lia); cbn; lia
| rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Hui; rewrite u_small by (cbn; lia);
match goal with H : djw _ |- _ => unfold djw in H; clear -H; lia end ]).
reflexivity.
Qed.
End SE.
Lemma seg_rom_high : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "G'S?yR0%211&R=+mXP0&S@r1%2261%5241'C':y8%<11%311&QL&R:r2%3221(0%117%;3731p0=1pU>D1").
Proof.
intros a Ha. unfold seg_rom. unfold memory_read.
cbn -[bv_unsigned Z.leb Z.ltb Z.add Z.sub N.leb N.ltb N.add bv_extract Z.of_N Z.to_N].
cbn [Z.of_N].
repeat (lazymatch goal with
| |- context [((?lo <=? bv_unsigned a)%Z && ?c)%bool] =>
replace c with false by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r
end).
reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_rdn_pointwise_inv := (ltac2:(TCodec.tc2 tcn__Ju0MainEntry "R;'7'N%211'S?yR0%211':y8%511%311p051'8%<14&Hr1r4%3221'C&QLr7&S>&R<&S@%12C8&RBr2%211%6241%82H1%;2:1(0%11G%?3G31p0A1pV2G1&R=r3%?2Q11%>1G%B221&RC+2+R0%3221%9251%Q71Q1&QKr6r5%34N2Q21(2%12Q7?%Q33731%Q82Q7Q2r9%Q12QCQ4%Q321N%Q52QE1%411&Jz%Q92QF1%34QFQ5?1%=2QG1%Q?3QG61p0<1pV2QG1p0?1p0H1p0Q31pUDQJ1pU>R21pV<QM1pV8QO1pVFR81")) (only parsing).
Variable segs : ltac:(sec_ty2 constr:(SEC_T_rdn_pointwise_inv) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rdn_pointwise_inv) 1%nat 0%nat).
Lemma rdn_pointwise_inv : ltac:(sec_stmt2 constr:(SEC_T_rdn_pointwise_inv) 2%nat 0%nat).
Proof.
intros n.
induction n as [|n IH]; intros a bs Hseg Hnw Hr j Hj; [lia|].
cbn [rdn] in Hr. pose proof (u64_range a) as Ha.
pose proof (Hseg 0%nat ltac:(lia)) as H0. rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H0.
destruct (m a) as [b|] eqn:Hm.
- destruct (rdn segs m (a + 1) n) as [rest|] eqn:Hr'; [|discriminate]. injection Hr as <-.
destruct j as [|j].
+ rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned. exact Hm.
+ cbn [nth]. assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
replace (bv_unsigned a + Z.of_nat (S j))%Z with (bv_unsigned (a + 1) + Z.of_nat j)%Z by lia.
apply (IH (a + 1) rest); [ | lia | exact Hr' | lia].
intros k Hk. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat k)%Z with (bv_unsigned a + Z.of_nat (S k))%Z by lia.
apply Hseg. lia.
- rewrite H0 in Hr. discriminate.
Qed.
End SE.
Section MainEntry.
Context {RE : RunEnv}.
Variable sp0 : word.
Variables a0s path : list byte.
Variable ev : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rdraw : EntryDraw.
Variable tid : word.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Let av := [a0s; path].
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 av ev uid hw rdraw tid regs mem.
Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
Definition p0 : word := cat_argv_ptr sp0 av ev 0.
Definition p1 : word := cat_argv_ptr sp0 av ev 1.
Definition auxvp : word := auxv_w sp0 av ev.
Definition rnd : word := at_random_ptr sp0 av ev.
Definition vals0 : list word := [sp0; p0; p1; auxvp; rnd; tid] ++ junk_vals regs.
Definition blobs0 : list (list byte) :=
[a0s ++ [Z_to_bv 8 0]; path ++ [Z_to_bv 8 0]; word_to_le_bytes 8 (canary_w (ed_random rdraw)); word_to_le_bytes 8 hw].
Definition E0 : env := Env (vals_ev vals0) (blobs_ev blobs0).
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
Definition sr_main : list expr :=
[ELit 0; ELit 0x994d8; spx (-48); ELit 0x10800; ELit 0xc8cb0; EVar 11; EVar 12; EVar 13;
spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 19; EVar 20; EVar 21;
EVar 22; EVar 23; ELit 0x33e1c; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].
Definition kn_stack : list kentry :=
[KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
KWr (SA (EVar 0) (-8388608)) 8388608;
KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1);
KWord (SA (EVar 0) 16) 8 (EVar 2); KWord (SA (EVar 0) 24) 8 (ELit 0)].
Definition kn_auxv : list kentry :=
[KRange (EVar 3) 0x7fff80000000 0x800000400000; KRange (EVar 4) 0x7fff80000000 0x800000400000;
KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 3) 0) 160;
KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 4) 0) 16;
KAlign (EVar 3) 8; KAlign (EVar 4) 8;
KWord (SA (EVar 3) 0) 8 (ELit 3); KWord (SA (EVar 3) 8) 8 (ELit 0x10040);
KWord (SA (EVar 3) 16) 8 (ELit 4); KWord (SA (EVar 3) 24) 8 (ELit 56);
KWord (SA (EVar 3) 32) 8 (ELit 5); KWord (SA (EVar 3) 40) 8 (ELit 10);
KWord (SA (EVar 3) 48) 8 (ELit 16); KBlob (SA (EVar 3) 56) (ELit 8) 3;
KWord (SA (EVar 3) 64) 8 (ELit 6); KWord (SA (EVar 3) 72) 8 (ELit 4096);
KWord (SA (EVar 3) 80) 8 (ELit 11);
KWord (SA (EVar 3) 96) 8 (ELit 12);
KWord (SA (EVar 3) 112) 8 (ELit 23); KWord (SA (EVar 3) 120) 8 (ELit 0);
KWord (SA (EVar 3) 128) 8 (ELit 25); KWord (SA (EVar 3) 136) 8 (EVar 4);
KWord (SA (EVar 3) 144) 8 (ELit 0); KWord (SA (EVar 3) 152) 8 (ELit 0)
].
Definition kn_image : list kentry :=
[KWr (SA (ELit 0) 0xb6000) 0x34000;
KImg 0x10000 0xb7230;
KImg 0xb7231 0xc8be0; KImg 0xe8cb8 0xe8cd8;
KWord (SA (ELit 0) 0xc8be8) 8 (ELit 0xc8be8);
KWord (SA (ELit 0) 0xc8c08) 4 (EVar 5);
KImg 0xc8c14 0xc8c60; KImg 0xc8c68 0xc8c80; KWord (SA (ELit 0) 0xc8c80) 8 (ELit 0xe8f78); KImg 0xc8c88 0xc8ca0;
KBlob (SA (ELit 0) 0xc8ca0) (ELit 8) 2;
KImg 0xc8cb0 0xc8cc0; KImg 0xc8cc8 0xe8cb8; KImg 0xe8cf0 0xe8cf8; KImg 0xe8cf8 0xe8f18; KImg 0xe8f18 0xe8f20;
KBlob (SA (ELit 0) 0xe8f20) (ELit 8) 2;
KImg 0xe8f28 0xe8f30;
KImg 0xe8f41 0xe8f48; KWord (SA (ELit 0) 0xe8f48) 8 (EVar 3);
KImg 0xe8f50 0xe8f58; KImg 0xe8f68 0xe8f70; KWord (SA (ELit 0) 0xe8f70) 8 (ELit 4096);
KImg 0xe8f78 0xe8fa8; KBlob (SA (ELit 0) 0xe8fa8) (ELit 8) 3 ; KImg 0xe8fb0 0xe90b8; KImg 0xe90b8 0xea000;
KRange (EVar 5) 1 4194303;
KImg 0 0x1000 ].
Definition kn_main : list kentry := kn_stack ++ kn_auxv ++ kn_image.
End MainEntry.
Definition all_regs : list reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma nth_all_regs : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "H'8&Hr1uQ0%3221'C'S?y5%211&Jr2&Q<(S=z(A%33821%748651&S>&RB%119%32=1%@3=51p0B1pV<G1").
Proof.
intros n Hn.
destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.
Lemma regs_ok_by_index : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "Q<'R4'7'R6%211&Q9y5'S?yR0%211%5241'8&Hr1uQ0%3221'C&QJr3&J%=1>r2&Q<(S=z(A%33D21%847651%;2:1&R3r5r4(R1%119%?4O=31%6251%D3K81p0F1pV0K1&R9%139FCp031pRFQ01pVJQ71pQLQ;1").
Proof.
intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot].
reflexivity.
- pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_all_regs in Hx by apply ridx_range.
rewrite ridx_roundtrip in Hx. exact Hx.
Qed.
Section MainEntryProofs.
Context {RE : RunEnv}.
Variable sp0 : word.
Variables a0s path : list byte.
Variable envv : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rdraw : EntryDraw.
Variable tid : word.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Let av := [a0s; path].
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 av envv uid hw rdraw tid regs mem.
Let E := E0 sp0 a0s path envv hw rdraw tid regs.
Lemma sp_lo : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "7&R=+SoonPPPPP0&S@yR0vS;%3221%6251"). Proof. exact (proj1 Hvsp). Qed.
Lemma sp_hi : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "7&R=&S@yR0vS;%3221+TPPPPPPPP0%6221"). Proof. exact (proj1 (proj2 Hvsp)). Qed.
Lemma sp_al : ltac2:(TCodec.tc2 tcn__Ju0MainEntry ";'C'L&R?&S@yR0vS;%3221+@%6221z%:3921"). Proof. exact (proj2 (proj2 Hvsp)). Qed.
Lemma ev_vals : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "Q;'8'C'S?yR0%211&R5vMr1%3221&J&3(5vS;&QBvRGvS6vRK%445321&QC%147543&Q=%149765&QD%14;987vSA(9%11F%@3G31%A3H51%B3I81%C3J;1%D3K>1%E3LD1&R0vS8%211%J3Q041&S>z%22Q41%O4Q4Q141%Q83Q5Q11pV<Q:1").
Proof. intros n. reflexivity. Qed.
Lemma ev_junk : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "K'8&Hr1uQ0%3221'C'S?yR0%211&R5vM&Du6r2%3221%6251&QJvS8&S>y5&RB%118%4231%7261%C3@91p0E1pV0J1").
Proof.
intros i Hi. rewrite ev_vals. change (6 + i)%nat with (length [sp0; p0 sp0 a0s path envv; p1 sp0 a0s path envv; auxvp sp0 a0s path envv; rnd sp0 a0s path envv; tid] + i)%nat.
rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
Qed.
Lemma spx_val : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "D'L'C'S?yR0%211&R3vM&QEr1%211%5241&S>&R<&S@vS;%22<1%4218%62>1%A3>81pV4C1").
Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.
End MainEntryProofs.
Section MainRegs.
Context {RE : RunEnv}.
Variable sp0 : word.
Variables a0s path : list byte.
Variable envv : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rdraw : EntryDraw.
Variable tid : word.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Let av := [a0s; path].
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 av envv uid hw rdraw tid regs mem.
Let E := E0 sp0 a0s path envv hw rdraw tid regs.
Ltac reg_case :=
cbn [nth sr_main all_regs];
first [ rewrite (spx_val sp0 a0s path envv hw rdraw tid regs)
| lazymatch goal with |- _ = edenot _ (EVar ?n) =>
change (edenot E (EVar n)) with (ev E n);
first [ rewrite (ev_junk sp0 a0s path envv hw rdraw tid regs (n - 6)) by lia; reflexivity | idtac ]
| |- _ => cbn [edenot] end ];
first [ reflexivity
| exact (me_ra _ _ _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ _ _ ME)
| exact (me_s2 _ _ _ _ _ _ _ _ _ ME)
| rewrite (me_sp _ _ _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
| rewrite (me_s0 _ _ _ _ _ _ _ _ _ ME); reflexivity
| rewrite (me_a1 _ _ _ _ _ _ _ _ _ ME); reflexivity
| rewrite (me_a2 _ _ _ _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
| rewrite (me_s3 _ _ _ _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
| rewrite (me_s1 _ _ _ _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
| rewrite (me_a0 _ _ _ _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
| apply (me_szero _ _ _ _ _ _ _ _ _ ME); cbn; tauto
| idtac ].
Theorem main_regs_ok : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "5&R9vM&QFvS8%43321").
Proof.
pose proof (proj1 Hvsp) as Hlo. pose proof (proj1 (proj2 Hvsp)) as Hhi. unfold sp_window_lo, sp_window_hi in *.
apply regs_ok_by_index.
intros i Hi.
destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_case.
Qed.
End MainRegs.
Section KnowProofs.
Context {RE : RunEnv}.
Variable sp0 : word.
Variables a0s path : list byte.
Variable envv : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rdraw : EntryDraw.
Variable tid : word.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Let av := [a0s; path].
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 av envv uid hw rdraw tid regs mem.
Let E := E0 sp0 a0s path envv hw rdraw tid regs.
Lemma kp_lo : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "7&R=+SoonPPPPP0&S@yR0vS;%3221%6251"). Proof. exact (proj1 Hvsp). Qed.
Lemma kp_hi : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "7&R=&S@yR0vS;%3221+TPPPPPPPP0%6221"). Proof. exact (proj1 (proj2 Hvsp)). Qed.
Lemma kp_al : ltac2:(TCodec.tc2 tcn__Ju0MainEntry ";'C'L&R?&S@yR0vS;%3221+@%6221z%:3921"). Proof. exact (proj2 (proj2 Hvsp)). Qed.
Lemma ke0 : ltac2:(TCodec.tc2 tcn__Ju0MainEntry ":'C'S?yR0%211&R5vM(1%3221vS;%93621"). Proof. reflexivity. Qed.
Lemma ke1 : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "?'C'S?yR0%211&R5vMu1%3221&QBvS;vRGvS6vRK%544321%>3;71"). Proof. reflexivity. Qed.
Lemma ke2 : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "?'C'S?yR0%211&R5vMu2%3221&QCvS;vRGvS6vRK%544321%>3;71"). Proof. reflexivity. Qed.
Lemma ke3 : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "?'C'S?yR0%211&R5vMu3%3221&Q=vS;vRGvS6vRK%544321%>3;71"). Proof. reflexivity. Qed.
Lemma ke4 : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "?'C'S?yR0%211&R5vMu4%3221&QDvS;vRGvS6vRK%544321%>3;71"). Proof. reflexivity. Qed.
Lemma ke5 : ltac2:(TCodec.tc2 tcn__Ju0MainEntry ":'C'S?yR0%211&R5vMu5%3221vSA%93621"). Proof. reflexivity. Qed.
Lemma know_stack : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "6&R8&R:vMvS4&QA%544321").
Proof.
pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
unfold kn_stack, know_ok.
repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?ke0, ?ke1, ?ke2;
unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?ke0.
- split; [lia | exact Hal].
- lia.
- split; [lia|]. intros d m Hd Hm.
apply (main_entry_store_ok_win sp0 av envv uid hw rdraw tid regs mem ME); rewrite u_small by lia; unfold stack_max_size; lia.
- split; [lia|]. split; [lia|].
unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by lia.
pose proof (read_argc_w RSEGS RPH sp0 av envv uid hw rdraw Hva) as Hr. unfold wmem in Hr.
rewrite (Hr Hve) by (unfold sp_window_hi; lia).
rewrite n_to_le_8_spec. reflexivity.
- split; [lia|]. split; [lia|].
unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv uid hw rdraw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat ltac:(subst av; cbn; lia)) as Hr.
unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
- split; [lia|]. split; [lia|].
unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv uid hw rdraw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 1%nat ltac:(subst av; cbn; lia)) as Hr.
unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
- split; [lia|]. split; [lia|].
unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
pose proof (read_argv_null RSEGS RPH sp0 rdraw av envv uid hw Hva Hve ltac:(unfold sp_window_hi; lia)) as Hr.
rewrite w_add_nat in Hr. subst av. change (Z.of_nat (8 + 8 * length [a0s; path])) with 24%Z in Hr.
rewrite <- (rdn_wmem_stack RSEGS RPH sp0 [a0s; path] envv uid hw rdraw) in Hr by (try rewrite u_small by lia; lia).
unfold wmem in Hr. rewrite n_to_le_8_spec in Hr. exact Hr.
Qed.
Lemma auxvp_eq : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "F'C'S?yR0%211&Q=vS;vRGvS6vRK%544321&S>&R<&S@%12;8&RB&QMvRH%2219%411%8261%:2B1%E3B<1").
Proof. unfold auxvp, auxv_w, auxv_off. subst av. cbn [length]. f_equal. lia. Qed.
Lemma auxvp_u : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "K'B'C'L&S@yR0&Q=vS;vRGvS6vRK%544321%8271&R<%:297&RB&QMvRH%2218%411%7261%C3B91&R=+U0%;251+RT[`0%4221%J261").
Proof.
pose proof kp_lo. pose proof kp_hi.
pose proof (auxv_off_bound RPH sp0 rdraw av envv uid hw) as Hb.
pose proof (lay_bsb_len RPH sp0 rdraw av envv uid hw Hva Hve) as Hl.
rewrite auxvp_eq. rewrite u_small by lia. lia.
Qed.
Lemma rnd_u : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "R<'B&R=&S@yR0vS;%3221&QDvRGvS6vRK%446321%9281%;271&R<+@%2241+RT[`0%42<1%A231'C'L&R?+8%22<1z%63521'8'G&Dr2r1%3221u@%6221':'7'S?y8%211%411%611&QK&R:&Q8&Q4&R;vRHvSBvRNvS7%675Q>4Q9321%82Q?1&S>&RBr3%211%Q;2Q=1%52QF1%A4@71M(2&I&K&Q6&Q7%11?%311%53L<1%73MQ61%92M1%QB3M;1p0Q51pV<Q=1pV2Q>1%R92Q@1%R:2QH1%R;2QO1").
Proof.
pose proof kp_lo as HLO. pose proof kp_hi as HHI.
pose proof (lay_bsb_len RPH sp0 rdraw av envv uid hw Hva Hve) as Hl.
destruct (rnd_facts RSEGS RPH sp0 rdraw av envv uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) kp_al)
as (A & B & C & D & F).
unfold rnd. subst av. repeat split; try assumption; try lia.
Qed.
Lemma auxv_word_at : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "QH'8&Hr1uD%3221'C':'7'S?y8%211%411%611&QK&R:vS4&S>yR0&R<&S@&Q=vS;vRGvS6vRK%544321%7291&R@+8&RBr2%211%5241%?271%B2A1u8%G4FE21(2&Q2&J%Q01G&QN&R;&QD%14GFEDvSBvRN%645321z%Q12Q01%;4:D31%=2@1%?2Q91%Q@3Q9A1p0QB1pV2QG1").
Proof.
intros j Hj. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
destruct auxvp_u as [Hu Hb].
rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv uid hw rdraw) as Hw. unfold wmem in Hw.
rewrite Hw by (rewrite u_small by lia; lia).
replace (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j))
with (sp0 + nat_to_word (auxv_off av envv + 8 * j)) by (rewrite w_add_nat; f_equal; lia).
rewrite (read_auxv_word RSEGS RPH sp0 rdraw av envv uid hw Hva Hve ltac:(unfold sp_window_hi; lia) j Hj).
rewrite n_to_le_8_spec. unfold rnd. reflexivity.
Qed.
Ltac kw_auxv j :=
split; [lia|]; split; [lia|];
unfold adenot; cbn [a_base a_off edenot]; rewrite ke3; unfold v_addi;
lazymatch goal with |- rdn _ _ (Z_to_bv 64 (?u + ?k)) 8 = _ =>
replace k with (8 * Z.of_nat j)%Z by reflexivity end;
rewrite (auxv_word_at j) by lia; unfold auxv_words; cbn [nth]; try reflexivity.
Lemma know_auxv : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "6&R8&R:vMvS4&Q>%544321").
Proof.
pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
destruct auxvp_u as [Hau Hab]. destruct rnd_u as (Hr1 & Hr2 & Hr3 & Hr4).
unfold kn_auxv, know_ok.
repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
rewrite ?ke0, ?ke3, ?ke4; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?ke0, ?ke3, ?ke4;
try rewrite Hau; try lia.
- split; [lia|].
destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z with ((2 * q + 5 + Z.of_nat (length envv)) * 8)%Z
by (unfold auxv_off; subst av; cbn [length]; lia).
apply Z_mod_mult.
- kw_auxv 0%nat. - kw_auxv 1%nat. - kw_auxv 2%nat. - kw_auxv 3%nat. - kw_auxv 4%nat. - kw_auxv 5%nat.
- kw_auxv 6%nat.
-
rewrite u_small by lia. split; [lia|].
split; [subst E; unfold E0; cbn [eb blobs_ev blobs0 nth]; rewrite length_N_to_le_bytes; reflexivity|].
intros i Hi. subst E; unfold E0; cbn [eb blobs_ev blobs0 nth].
pose proof (auxv_word_at 7 ltac:(lia)) as Hr.
unfold auxv_words, auxv_entries in Hr. cbn [flat_map fst snd app nth] in Hr. rewrite Hau in Hr.
pose proof (rdn_pointwise_inv RSEGS mem 8 (Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off av envv) + 8 * Z.of_nat 7)) _
ltac:(intros j Hj; rewrite u_small by lia; apply seg_rom_high; rewrite u_small by lia; lia)
ltac:(rewrite u_small by lia; lia) Hr (Z.to_nat i) ltac:(lia)) as Hp.
rewrite u_small, Z2Nat.id in Hp by lia.
replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv) + 56 + i)%Z
with (bv_unsigned sp0 + Z.of_nat (auxv_off av envv) + 8 * Z.of_nat 7 + i)%Z by lia.
exact Hp.
- kw_auxv 8%nat. - kw_auxv 9%nat. - kw_auxv 10%nat. - kw_auxv 12%nat.
- kw_auxv 14%nat. - kw_auxv 15%nat. - kw_auxv 16%nat. - kw_auxv 17%nat. - kw_auxv 18%nat. - kw_auxv 19%nat.
Qed.
Section SE.
Local Abbreviation SEC_T_D_main_auxvp := (ltac2:(TCodec.tc2 tcn__Ju0MainEntry "Q6'7'N%211'C':'S?y8%211%811%511&QKr1&QGvS;vRHvRKvRN&Q7vS7%211vSA%96876521&S>yR0+mSj8%3221u8%A4@621(2&Q2&Q=vRGvS6%34D21B%5281%72K1%Q13K91pVFQ31")) (only parsing).
Variable segs : ltac:(sec_ty2 constr:(SEC_T_D_main_auxvp) 0%nat 0%nat).
Lemma D_main_auxvp : ltac:(sec_stmt2 constr:(SEC_T_D_main_auxvp) 1%nat 0%nat).
Proof.
pose proof (u64_range tid). pose proof (u64_range hw). pose proof kp_lo. pose proof kp_hi.
unfold auxvp, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.
End SE.
Lemma wseg_data : OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim.wseg_ok Ubsan.M.loaded_segments (Z_to_bv 64 0xb6000) 0x34000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma range_disjoint_sub : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "Q2'L'8';%1232'C'4&QIr4r3r2%43321(<%83721&R=r5%2216&R<+1%22:1r6&RB%117%6231%:251u1%C3B1;%F3E1?p041p0=1p0A1pV0N1pUFL1pV<O1pV6Q11").
Proof.
intros lo n [c w] i H Hlo Hhi. unfold range_disjoint_b in *. cbn [fst snd] in *.
apply orb_true_iff in H. apply orb_true_iff. rewrite !Z.leb_le in *. cbn [Z.of_nat Pos.of_succ_nat]. lia.
Qed.
Lemma missb_sub : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "N'L'8'C'4&QHr3r2%3221(<%73621&R=r4%2216&R<+1%22:1r5&RB%117%6231%:251u1%B2;1%E3D1?p041p0=1p0A1pV0K1pV<K1pV6M1").
Proof.
intros lo n i H Hlo Hhi. unfold D_main_missb in *.
apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
apply Z.leb_le in H2. apply Z.leb_le in H3.
apply andb_true_iff; split; [apply andb_true_iff; split|]; [| apply Z.leb_le; lia | apply Z.leb_le; cbn [Z.of_nat Pos.of_succ_nat]; lia].
apply forallb_forall. intros c Hc. apply (range_disjoint_sub lo n); [|lia|lia].
apply (proj1 (forallb_forall _ _) H1). exact Hc.
Qed.
Lemma kimg_ok : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "Q0'L'C'4&QHr2&RE&RDr1%2214%411%7261(<%;3:21&R=r3%221;+mXP0%4231&R7&R:vMvS4(R2r5r4%3221%847651p0:1p0=1p0A1pULN1pV6O1").
Proof.
intros lo hi Hb Hle Hhi. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
assert (Hlo0 : (0 <= lo)%Z).
{ unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
apply Z.leb_le in Hb. exact Hb. }
cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
rewrite (main_entry_mem_data sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
apply (D_main_none sp0 av envv hw (ed_random rdraw) tid i Hva); [lia | lia |].
apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
Qed.
Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].
Ltac kw_pre :=
split; [lia|]; split; [lia|];
unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
Ltac kw_data L :=
kw_pre;
rewrite (main_entry_rdn_data sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
rewrite (L RSEGS); try reflexivity.
Ltac kw_mem L := kw_pre; rewrite (L RSEGS); try reflexivity.
Ltac kblob8 L :=
unorm; rewrite ?Z.add_0_l; repeat split; try lia;
try (subst E; unfold E0; cbn [eb blobs_ev blobs0 nth]; rewrite length_N_to_le_bytes; reflexivity);
intros i Hi; subst E; unfold E0; cbn [eb blobs_ev blobs0 nth];
rewrite (main_entry_mem_data sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
apply L; lia.
Lemma know_image : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "6&R8&R:vMvS4&Q?%544321").
Proof.
pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof (u64_range tid) as Ht.
unfold kn_image, know_ok.
repeat apply Forall_cons; try apply Forall_nil;
try kimg;
cbn [kentry_ok a_base a_off edenot]; rewrite ?ke3, ?ke5; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
rewrite ?(u_small 0) by lia; cbn [Z.add].
- split; [lia|]. intros d m Hd Hm.
eapply (store_ok_window RSEGS mem (Z_to_bv 64 0xb6000) (Z_to_bv 64 (0xb6000 + d)) 0x34000 m 0xb6000 0xea000);
[reflexivity | reflexivity | cbn; lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
- kw_data (D_main_self sp0 av envv hw rdraw tid).
- kw_mem (main_entry_tid sp0 av envv uid hw rdraw tid Hlo regs mem ME).
- kw_data (D_main_locale sp0 av envv hw rdraw tid).
- kblob8 (D_canary_pt sp0 av envv hw rdraw tid Hva).
- kblob8 (D_guard_pt sp0 av envv hw rdraw tid Hva).
- kw_data D_main_auxvp.
- kw_data (D_main_pagesize sp0 av envv hw rdraw tid Hva).
- kblob8 (D_hwcap_pt sp0 av envv hw rdraw tid Hva).
- lia.
Qed.
Theorem main_know_ok : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "6&R8&R:vMvS4&Q@%544321").
Proof.
unfold kn_main, know_ok.
apply Forall_app; split; [apply know_stack|].
apply Forall_app; split; [apply know_auxv | apply know_image].
Qed.
Lemma main_str : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "QN'8&Hr1u2%3221'B'C':'7'S?y8%211%411%611&QK&R:vS4&Q;vS;vRHvRKr2%544321&D&6&J(9%11@%34@791%52B1u1%8221%B4A@:1(2&3(5&S>z%22L1%43L1<%63M<1%82M1%Q43M:1&R=&S@yR0%221L%322I%5221&R<+RPZUH%2251%9251&RB%11I+SooO%=221%QD251%QE2:1%QF2A1p0QH1pV4QM1").
Proof.
intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
pose proof (lay_bsb_nw RPH sp0 rdraw av envv uid hw Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
assert (Hk' : (k < length av)%nat) by (subst av; cbn; lia).
destruct (argv_ptr_bounds_at sp0 av envv Hva Hve ltac:(unfold sp_window_hi; lia) k Hk') as [B1 B2].
pose proof (u_cat_argv_ptr RPH sp0 rdraw av envv uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
pose proof (struct_av_bound RPH sp0 rdraw av envv uid hw Hva Hve) as Hsb.
pose proof (total_arg_bytes_firstn_le k av) as Hf.
pose proof (argv_str_len av Hva k Hk') as Hlen.
repeat split.
- rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by lia.
pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv uid hw rdraw) as Hw. unfold wmem in Hw. rewrite Hw by lia.
apply read_argv_cstr_k; [exact Hk' | exact Hnw].
- exact B1.
- lia.
- exact Hlen.
Qed.
Lemma main_str_fits : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "Q7&Q3vS;vRHvRK%43321'8&Hr1u2%3221&R=&R<&S@yR0&Q;r2%24?>=1%5241&RB&6'S?y8%211&J'7%113(9%115%543=J1%:271%<11%D2>1+A%F221+TPPPPPPPP0%I221p0K1pV4Q01p0Q21").
Proof.
intros Hfit k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
assert (Hk' : (k < length av)%nat) by (subst av; cbn; lia).
pose proof (u_cat_argv_ptr RPH sp0 rdraw av envv uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
pose proof (bsb_len_lower RPH sp0 av envv uid hw rdraw) as Hlow.
pose proof (total_arg_bytes_firstn_le (S k) av) as Hmono.
pose proof (total_arg_bytes_firstn_S av k Hk') as Hstep.
pose proof (build_stack_bytes_within_span RPH sp0 av envv uid hw rdraw) as Hspan.
unfold entry_stack_fits, sp_window_hi in Hfit. lia.
Qed.
Lemma main_auxv : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "S4'8&Hr1uD%3221'C':'7'S?y8%211%411%611&QK&R:vS4&S>yR0&R<&S@&Q=vS;vRGvS6vRK%544321%7291&R@+8&RBr2%211%5241%?271%B2A1u8%G4FE21(2&Q2&J'L(5+3&RA&O&R;%211%411+4&Q0%115%811+5&Q1%119%<11+@vRN%Q72Q91+6+TP0+;vSB%Q<2Q>1+<+Gz+I&QD%14Q@Q?Q>Q=%QC2QE1(9%11Q0%Q03Q171%Q13Q281%Q23Q351%Q33Q491%Q43Q5;1%Q53Q6=1%Q63Q7@1%Q73Q8@1%Q83Q9B1%Q93Q:E1%Q:3Q;G1%Q;3Q<I1%Q<3Q=K1%Q=3Q>N1%Q>3Q?Q01%Q?3Q@Q41%Q@3QAQ61%QA3QBQ:1%QB3QCQ<1%QC3QDQB1%QF4QEQO1K%R>2R=1%QI2QL1%QK2RE1%RL3REQM1p0RN1pV2S31").
Proof.
intros j Hj. rewrite (auxv_word_at j Hj). unfold auxv_words, auxv_entries. cbn [flat_map fst snd app].
do 20 (destruct j as [|j]; [cbn [nth]; rewrite ?Z_to_bv_bv_unsigned; reflexivity|]). lia.
Qed.
Lemma main_auxv_rng : ltac2:(TCodec.tc2 tcn__Ju0MainEntry "QF'B&R=z&S@yR0vS;%3221%6251&R<+Q8%2241&Q=vRGvS6vRK%44:321%=2<1%@271+U0%;231+RT[`0%=2?1%E231'C'L&R?+8%22;1%5341J&R>&RC+2+R0%3221%52=1vSB%Q12Q01%Q42Q31%9225%Q7221&QD%14Q4MLK%Q72Q61%Q:2Q51+@%Q5231%Q=21I%Q?241%Q@291%QA2?1%QB2F1%QC2M1%QD2Q31%QE2Q>1").
Proof.
pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal. pose proof (u64_range uid) as Hu.
destruct auxvp_u as [Hau Hab]. destruct rnd_u as (Hr1 & Hr2 & Hr3 & Hr4).
assert (Hoff : (40 <= Z.of_nat (auxv_off av envv))%Z) by (unfold auxv_off; subst av; cbn [length]; lia).
repeat split; try lia.
rewrite Hau. destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z with ((2 * q + 5 + Z.of_nat (length envv)) * 8)%Z
by (unfold auxv_off; subst av; cbn [length]; lia).
apply Z_mod_mult.
Qed.
End KnowProofs.
End FPX_1.
