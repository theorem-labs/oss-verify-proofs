(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import ExitSim PropExec CatSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CatExec () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Decimal."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Number."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec.WithFP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ExitSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.Lists.List."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1S"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"]; ["1true"; "2D0"; "2D1"; "2D2"; "2D3"; "2D5"; "2D7"; "2D9"; "2Nil"; "3I"; "3and"; "3eq"; "3ex"; "3not"; "3or"; "4add"]; ["4mul"; "4of_num_uint"; "5UIntDecimal"; "6le"; "6lt"; "7Forall"; "7firstn"; "7nth"; "7skipn"; "8Z"; "9Z_to_le_bytes"; "9len_word"; "9nat_to_word"; "9word_le8"; "9word_to_nat"; ":path_eqb"]; [";PhdrInfo"; ";Segment"; "<Build_machine_state"; "<MachineOk"; "<fetch_word"; "<is_ecall"; "<machine_result"; "<machine_state"; "<ms_gpr"; "<ms_mem"; "<ms_read_bytes"; "<ms_read_bytes_aux"; "<ms_rom"; "<ms_svc_pending"; "<set_gpr0"; "<step"]; ["<store_ok"; "<word_to_le_bytes"; "<write_to_mem"; "=advance_past_svc"; "=entry_stack_image"; "=valid_argv"; ">EntryDraw"; ">build_stack_bytes"; ">flatten_strings"; ">stack_to_mem"; ">string_addrs"; "?stack_max_size"; "@openat_plain_name"; "Adot_path"; "Bdecode_any"; "CSZ8"]; ["CStore"; "Cinstr"; "Dbvmap"; "Ereg_get"; "Fbyte_at"; "Fcat_argv_ptr"; "Fcat_string_base"; "Fcat_struct_prefix"; "Fcat_struct_size"; "Fpend"; "Fwbytes"; "Gto_wexit"; "His_exit_no"; "Ifp_csr"; "Ifp_regs"; "Igetr"]; ["Imkst"; "Irdn"; "Iregupd"; "Iseg_rom"; "Itotal_arg_bytes_nat"; "Iv_addi"; "Iwrap_mem"; "JIn"; "Jflat_map"; "Kle"; "Kof_nat"; "Ladd"; "Lle"; "Llt"; "Lof_nat"; "Lpow"]; ["Lsub"; "0a"; "0addr"; "0argv"; "0av"; "0b"; "0base"; "0bs"; "0buf"; "0bufs"; "0code"; "0envp"; "0ev"; "0fx"; "0hw"; "0imm"]; ["0j"; "0k"; "0l"; "0len"; "0m"; "0mem"; "0ms"; "0n"; "0pc"; "0ph"; "0post"; "0pre"; "0regs"; "0rnd"; "0rom"; "0rs1"]; ["0rs2"; "0s"; "0segs"; "0sp"; "MBV"; "MZ_to_bv"; "Mbv"; "Mbv_add"; "Mbv_signed"; "Mbv_unsigned"; "0strs"; "0sv"; "0tail"; "0uid"; "0v"; "0w"]; ["0x"; "0x8"; "0z"]]).
Section WithFP.
Context {fx : FPState}.
Lemma ms_read_bytes_aux_rdn : ltac2:(TCodec.tc2 tcn__CatExec "Q5':'QA%211'QG';'TFyR0%211'K'=y8%611%311p061&QLr3%211&S3r4%211%<3741%E1:%=11&QKr2%2371:&S1r5&QI%11;%44316?%G3961p0<1pW6J1pX@N1pX>Q01pY6Q21").
Proof.
intros segs ms n. induction n as [|n IH]; intros addr Hrom; [reflexivity|].
cbn [ms_read_bytes_aux rdn]. unfold ms_read_byte. rewrite Hrom.
destruct (ms_mem ms addr) as [b|].
- rewrite IH by exact Hrom. reflexivity.
- unfold seg_rom. destruct (memory_read segs addr 1) as [[|b r]|];
try reflexivity; rewrite IH by exact Hrom; reflexivity.
Qed.
Lemma ms_read_bytes_rdn : ltac2:(TCodec.tc2 tcn__CatExec "Q6':'QA%211'QG'TFyR0%211'K'=y8%611%311p061&QLr3%211&S3r4%211%<3741%D1:%=11&QJr2%237:1&S1r5&QI%11;&Q>%117%6453A1%I3;81p0>1pX8L1pW6M1pX>Q11pY6Q31").
Proof. intros. unfold ms_read_bytes. apply ms_read_bytes_aux_rdn; assumption. Qed.
Fixpoint wbytes (m : word -> option byte) (addr : word) (bs : list byte)
: word -> option byte :=
match bs with
| [] => m
| b :: rest => wbytes (fun a => if bv_eqb a addr then Some b else m a) (addr+1) rest
end.
Lemma wbytes_above : ltac2:(TCodec.tc2 tcn__CatExec "Q4':'TFy8%211%411yR0%511'=%115p031&S<&S;&TIr2%2291&S>&9r4%22?1%411%9261r1%:2A1%=231'K&RJr3r5%34;21?%<1@%63F21p081pZ2J1pW6K1pX:I1pW@O1").
Proof.
induction bs as [|b rest IH]; intros m addr x Hle; [reflexivity|].
cbn [wbytes length] in *.
pose proof (u64_range x) as Hx.
assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z)
by (apply u_add1; lia).
rewrite IH by lia.
cbv beta.
assert (Hne : bv_eqb x addr = false)
by (unfold bv_eqb; apply Z.eqb_neq; lia).
rewrite Hne. reflexivity.
Qed.
Lemma rdn_wbytes_disjoint : ltac2:(TCodec.tc2 tcn__CatExec "QF':'QA%211'TFy8%211%611yR0%511'=%115p031';&S<&S;&TIr3%22:1&S>&9r5%22@1%411%9261r2%:2B1%=231%913%>2;1&S?+2+R0%3221%D251'K%J1M&S1r8&RJr6r7%332E1r4%74621K%84752L%;3:21p0=1p0E1pX@Q41pW4Q91pW6Q:1pX:Q81pW@Q>1pY6QC1").
Proof.
intros segs bs m addr a n Hle Hnw. apply rdn_ext; [exact Hnw|].
intros x Hx. apply wbytes_above. lia.
Qed.
Lemma wbytes_below : ltac2:(TCodec.tc2 tcn__CatExec "Q;':'TFy8%211%411yR0%511'=%115p031&S<&S;&TIr2%2291&S>&9r4%22?1%411%9261&S?+2+R0%3221%?251&S=r3%@2G1%32?1'K&RJr5r6%342A17%318%63L21p081p0=1pZ2Q11pW6Q21pX:Q01pW@Q61").
Proof.
induction bs as [|b rest IH]; intros m addr x Hnw Hlt; [reflexivity|].
cbn [wbytes length] in *.
assert (Hne : bv_eqb x addr = false)
by (unfold bv_eqb; apply Z.eqb_neq; lia).
destruct rest as [|b' rest'].
- cbn [wbytes]. rewrite Hne. reflexivity.
- assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z)
by (apply u_add1; cbn [length] in Hnw; lia).
rewrite IH by lia.
cbv beta. rewrite Hne. reflexivity.
Qed.
Lemma rdn_wbytes_below : ltac2:(TCodec.tc2 tcn__CatExec "QH':'QA%211'TFy8%211%611yR0%511'=%115p031';&S<&S;&TIr2%22:1&S>r1%211%7241r3%82@1%;231r4%;2C1&9r6%22H1%<11%A251&S?+2+R0%3221%G251'K%M1Q0&S1r8&RJr5r7%33@21%6451DG%746BEH%:3921p0<1p0I1pX@Q61pW4Q;1pW6Q<1pX:Q:1pW@Q@1pY6QE1").
Proof.
intros segs bs m addr a n Hle Hnw.
pose proof (u64_range addr) as Ha.
apply rdn_ext; [lia|].
intros x Hx. apply wbytes_below; [exact Hnw|lia].
Qed.
Lemma rdn_wbytes_out : ltac2:(TCodec.tc2 tcn__CatExec "R3':'QA%211'TFy8%211%611yR0%511'=%115p031';'N&S<&S;&TIr2%22;1&S>r1%211%7241r3%82A1%;231&9r5%22G1%:11%?261%A21=%C271%>1@%C2:1&S?+2+R0%3221%I251%H2Q1=r7%@2Q51%H11%M241%O217'K%Q61Q9&S1r9&RJr6r8%33<21r4%7462L1%847?M2%;3:21p0=1p0D1p0L1pX@QA1pW4QF1pW6QG1pX:QE1pW@QK1pY6R01").
Proof.
intros segs bs m addr a n [Hb|Hd] Hnw Hnw'.
- apply rdn_wbytes_below; [exact Hb | exact Hnw'].
- apply rdn_wbytes_disjoint; [exact Hd | exact Hnw].
Qed.
Lemma length_Z_to_le_bytes : ltac2:(TCodec.tc2 tcn__CatExec "?';'Q9'K&9'TFy8%211&Q:r2r1%3221%8251%:3<14pZ6<1pX@>1").
Proof.
induction n as [|n IH]; intro z; [reflexivity|].
cbn [Z_to_le_bytes length]. rewrite IH. reflexivity.
Qed.
Lemma length_N_to_le_bytes : ltac2:(TCodec.tc2 tcn__CatExec "@';'TFyR0%211'K&9y8%611&R1r2r1%3221%7251%93=14pYN;1pX@?1").
Proof. intros. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.
Lemma write_to_mem_wbytes : ltac2:(TCodec.tc2 tcn__CatExec "F':'TFy8%211%411yR0%511'=%115p031'K&R2r2r1r3%43321&RJ%13543%83931pW6=1pX:;1pW@A1").
Proof.
induction bs as [|b rest IH]; intros m addr; [reflexivity|].
cbn [write_to_mem wbytes]. apply IH.
Qed.
Lemma step_sd : ltac2:(TCodec.tc2 tcn__CatExec "S?':'QA%211&RBy5'TFyR0%211%5241'=y8%611%311p061yQ0%:11%;1<y<%=11'K%;15&QDr9r7%3221(3r4%22<1%93841'5&QEr5%211(7%?3521'?'RA'Q9%3221%N11&R>r6%211(>(R@(R?r3%342@E1+4%64=<21%I2<1%Q03<91&R0r<&S5&ROr;%221@&TH%12Q:Q1%6231u8%:49Q821(@%Q=3Q321'L%R21QG'J';&9r1%22QL1%QE341;'QF'QG%211&QOr>&S0vSMr=r:%4532MJ1%7261(QC%O2Q0Q5&RJr8%Q1281%O2R8Q@%Q4221%53Q31E%>5=<71;%92C1%R;3C;1%L2G1qW@N1%Q02O1p0Q21p0Q@1p0R21p0R91pX0RD1pY2RG1pY0RH1pZ0RJ1pXNRM1pX<RN1pXBS51pXJS51pY6S<1").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
exists (word_to_le_bytes 8 (getr regs rs2)). split; [reflexivity|].
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
rewrite b_addsext.
rewrite Hok; cbv beta iota.
rewrite write_to_mem_wbytes, b_npc4. reflexivity.
Qed.
Lemma stack_max_size_val : ltac2:(TCodec.tc2 tcn__CatExec "5'K'Q9&R;+XPPP0%43321").
Proof. vm_compute. reflexivity. Qed.
Lemma wrap_mem_below : ltac2:(TCodec.tc2 tcn__CatExec "Q;'Q@'TFyR0%211':y8%511%311%411'R6&S=&TIr4%22;1&S@r7%52>1&R;%4221%9261'K'=%11@&S6r9r8r6r3r2r5%7865?4B321(0%11J%=3;31p0?1pXLJ1pWNQ11pYLQ21pW6Q31pWHO1pW8Q01pY8Q61pXDQ:1").
Proof.
intros ph sp argv envp addr uid hw rnd Hlt.
pose proof stack_max_size_val as Hsms.
unfold wrap_mem, stack_to_mem.
assert (Hsp : Z.leb (bv_unsigned sp) (bv_unsigned addr) = false)
by (apply Z.leb_gt; lia).
rewrite Hsp.
assert (Hgate : Z.leb (bv_unsigned sp - stack_max_size) (bv_unsigned addr) = false)
by (apply Z.leb_gt; lia).
rewrite Hgate. reflexivity.
Qed.
Lemma flat_map_app' : forall {A B : Type} (f : A -> list B) l1 l2,
flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
intros A B f l1 l2. induction l1 as [|x xs IH]; cbn; [reflexivity|].
rewrite IH, app_assoc. reflexivity.
Qed.
Lemma skipn_nth : forall {A : Type} (l : list A) k d, (k < length l)%nat ->
skipn k l = nth k l d :: skipn (S k) l.
Proof.
induction l as [|x xs IH]; intros k d Hk; [cbn in Hk; lia|].
destruct k as [|k']; [reflexivity|].
cbn [skipn nth]. apply IH. cbn in Hk; lia.
Qed.
Lemma flat_map_split : forall {A B : Type} (f : A -> list B) l k d, (k < length l)%nat ->
flat_map f l = flat_map f (firstn k l) ++ f (nth k l d) ++ flat_map f (skipn (S k) l).
Proof.
intros A B f l k d Hk.
rewrite <- (firstn_skipn k l) at 1.
rewrite flat_map_app'.
rewrite (skipn_nth l k d Hk). reflexivity.
Qed.
Lemma flat_map_le8_decomp : ltac2:(TCodec.tc2 tcn__CatExec "Q9':'TFyR0%211%411';&Q4r1&9r2%2271%5241'Ky8%=11%?11&S8&Q=r3%34@521&4&Q6%13C=4%74D961&Q7&TEz%22I1%44IC:1%<11&Q8(2%11G%33N1?%B4ODA1%?3E61%@3F=1%I3FB1p0K1pX4Q21pX6Q41").
Proof. intros l k Hk. apply (flat_map_split word_le8 l k (Z_to_bv 64 0) Hk). Qed.
Lemma flatten_strings_decomp : ltac2:(TCodec.tc2 tcn__CatExec "Q:':'TFy8%211%411%511';&Q4r1&9r2%2271%5241'K&R8r3%211&4&Q6%13?94%611&Q7(<%11D%34D>91(6&TEz%22J1%43J16%=3K61&Q8(2%11G%33N1C%E11%C3Q161%D3Q2A1%I3Q2F1p0K1pX4Q21pYFQ41").
Proof.
intros strs k Hk.
apply (flat_map_split (fun s => s ++ [Z_to_bv 8 0]) strs k [] Hk).
Qed.
Lemma total_arg_bytes_cons : ltac2:(TCodec.tc2 tcn__CatExec "H':'TFy8%211%411%511'K';&S4(6r2r1%33821%511&O&9%12=6u1%4221%;18%6221%?3>81pX6A1pY4C1").
Proof. reflexivity. Qed.
Lemma total_arg_bytes_firstn_le : ltac2:(TCodec.tc2 tcn__CatExec "B';':'TFy8%211%411%511'Q3&S4&Q6r2r1%33721%511%613%8221pX6:1pX4A1").
Proof.
induction k as [|k IH]; intros l.
- change (total_arg_bytes_nat (firstn 0 l)) with 0%nat. lia.
- destruct l as [|s rest]; [cbn; lia|].
cbn [firstn]. rewrite !total_arg_bytes_cons. specialize (IH rest). lia.
Qed.
Lemma natN_le : ltac2:(TCodec.tc2 tcn__CatExec ">';'Q3r2r1%3221&S9&S:r3%211%317%5221p071pX:<1pX@=1").
Proof. intros n m H. lia. Qed.
Lemma of_nat_131071 : ltac2:(TCodec.tc2 tcn__CatExec "E'K'Q9&S>&Q1(Q2(B(D(A(F(H%511%311%511%811%811%:11%<11%>11%@11+SooO%D3C21").
Proof. vm_compute. reflexivity. Qed.
Lemma of_nat_2097152 : ltac2:(TCodec.tc2 tcn__CatExec "H'K'Q9&S>&Q1(Q2(C(A(G(F(B(E(H%711%311%511%711%911%;11%=11%?11%A11%C11+RPPP0%G3F21").
Proof. vm_compute. reflexivity. Qed.
Definition cat_struct_size (av ev : list (list byte)) : nat :=
(8 + (length av + 1) * 8 + (length ev + 1) * 8 + auxv_size)%nat.
Definition cat_string_base (sp : word) (av ev : list (list byte)) : word :=
sp + nat_to_word (cat_struct_size av ev).
Definition cat_env_base (sp : word) (av ev : list (list byte)) : word :=
cat_string_base sp av ev + nat_to_word (total_arg_bytes_nat av).
Definition cat_argv_ptr (sp : word) (av ev : list (list byte)) (k : nat) : word :=
nth k (fst (string_addrs (cat_string_base sp av ev) av)) (Z_to_bv 64 0).
Lemma nth_string_addrs : ltac2:(TCodec.tc2 tcn__CatExec "Q9':'TFy8%211%411%511yR0%611';&Q4r1&9r3%2291%5241'K&Q7r2&8%C1<&R:r4%22:1%534@1&TEz%22D1%;4D:41&TG&Q<&S4&Q6%13L?;%311%511%73MG1%E3M91p0G1pX4N1pW>Q01pYFQ31").
Proof.
induction strs as [|s rest IH]; intros base k Hk; [cbn in Hk; lia|].
rewrite string_addrs_fst_structure.
destruct k as [|k'].
- cbn [nth firstn]. change (total_arg_bytes_nat []) with 0%nat.
rewrite word_add_0. reflexivity.
- cbn [nth]. rewrite (IH (base + len_word s + 1) k' ltac:(cbn in Hk; lia)).
cbn [firstn]. rewrite total_arg_bytes_cons.
rewrite len_word_nat, word1_nat, !nat_to_word_add_merge.
f_equal. f_equal. lia.
Qed.
Lemma cat_argv_ptr_offset : ltac2:(TCodec.tc2 tcn__CatExec "Q5'TFyR0%211':y8%511%311%411';&Q4r1&9r3%2271%5241'K&REr5r4r2%443281&TG&RF%1365;&Q<&S4&Q6%13E89%311%511%93M71%@3M;1p0B1pX4I1pWJK1pW:L1pY8Q21").
Proof. intros. unfold cat_argv_ptr. apply nth_string_addrs. assumption. Qed.
Definition cat_struct_prefix (ph : PhdrInfo) (sp : word) (av ev : list (list byte))
(uid : word) (hw : word) : list byte :=
word_le8 (len_word av)
++ flat_map word_le8 (fst (string_addrs (cat_string_base sp av ev) av))
++ word_le8 (Z_to_bv 64 0)
++ flat_map word_le8 (fst (string_addrs (cat_env_base sp av ev) ev))
++ word_le8 (Z_to_bv 64 0) ++ auxv_bytes ph (at_random_ptr sp av ev) uid hw.
Lemma length_cat_struct_prefix : ltac2:(TCodec.tc2 tcn__CatExec "N'Q@'TFyR0%211':y8%511%311%411'K';&9&RGr6r5r4r3r2r1%76654321%92>1&RH%1276%>3=31pWNE1pYLF1pWJB1pW:C1pY8I1pXDM1").
Proof.
intros ph sp av ev uid hw. unfold cat_struct_prefix, cat_struct_size.
rewrite !length_app, !length_flat_map_le8, !length_string_addrs_fst,
!length_n_to_le_8, length_auxv_bytes.
lia.
Qed.
Lemma bsb_argv_prefix : ltac2:(TCodec.tc2 tcn__CatExec "Q@'Q@'TFyR0%211':y8%511%311%411'R6'L'K&R7r8r7r6r5r4r3r2%877654321&4&Q=&Q;%12A9%311&S8&8%H1I&R:&RF%13A@?%321A%635N1%84OL<1r1%?3N21%@3O<1%K3OB1qYJQ01%N2Q11pXLQ01pWNQ71pYLQ81pWJQ41pW:Q51pY8Q;1pXDQ?1").
Proof.
intros ph sp av ev uid hw rnd. unfold build_stack_bytes.
rewrite (string_addrs_pair av). cbv beta iota.
rewrite (string_addrs_pair ev). cbv beta iota.
eexists. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma bsb_ptr_k : ltac2:(TCodec.tc2 tcn__CatExec "R1'Q@'TFyR0%211':y8%511%311%411';'R6&Q4r4&9r6%2281%5241'L'K&R7r:r9r8r7r5r3%7765432>1&4&Q=&Q;%12G8%311&S8&Q6&8%O1Q0&R:&RF%13A@?%321A%635Q51%83Q6K1%:4Q7Q4>1%@3Q5<1&Q7&TEz%22Q=1%44Q=Q281%E11r1%H3Q=21%I3Q>91%Q33Q>K1qXFQ?1%Q62Q@1p0Q81pXLQ?1pWNQG1pYLQH1pX4QC1pWJQE1pW:QF1pY8QL1pXDR01").
Proof.
intros ph sp av ev k uid hw rnd Hk.
destruct (bsb_argv_prefix ph sp av ev uid hw rnd) as [tail E].
assert (Hk' : (k < length (fst (string_addrs (cat_string_base sp av ev) av)))%nat)
by (rewrite length_string_addrs_fst; exact Hk).
rewrite (flat_map_le8_decomp _ k Hk') in E.
eexists. rewrite E. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma read_argv_ptr_k : ltac2:(TCodec.tc2 tcn__CatExec "R>'Q@':'QA%211'TFyR0%211y8%411%811%911';'R6&Q4r4&9r6%2281%5241&S=&S;&TIr8%22B1&S>&R7r:r7r3r2%57483>@21%@2G1%811%=2:1&S?+2+R0%3221%C251'K'=%11Q0&S1&R9r9&R4r;r5%3724JE1Q2D%6251&TG&Q<&Ou8&Q0%122Q7%4231%611%83QE>1%A4Q1:16(3&Q=&RE%14CQ9Q4Q?%311%52QH1%K3I71p0M1p0QB1pXLQI1pWNR01pYLR11pX4QM1pWJQO1pW:R01pY8R51pY6R91pXDR=1").
Proof.
intros ph segs sp av ev k uid hw rnd Hk Hnw.
destruct (bsb_ptr_k ph sp av ev k uid hw rnd Hk) as [post E].
pose proof (read_at_offset_image segs ph sp av ev uid hw rnd
(word_le8 (len_word av)
++ flat_map word_le8 (firstn k (fst (string_addrs (cat_string_base sp av ev) av))))
(word_le8 (nth k (fst (string_addrs (cat_string_base sp av ev) av)) (Z_to_bv 64 0)))
post 8%nat E (length_n_to_le_8 _) Hnw) as H'.
assert (Hlen : length (word_le8 (len_word av)
++ flat_map word_le8 (firstn k (fst (string_addrs (cat_string_base sp av ev) av))))
= (8 + 8 * k)%nat).
{ rewrite length_app, length_n_to_le_8, length_flat_map_le8, firstn_length_le;
[reflexivity | rewrite length_string_addrs_fst; lia]. }
rewrite Hlen in H'.
rewrite H'. unfold cat_argv_ptr. reflexivity.
Qed.
Lemma bsb_strings_split : ltac2:(TCodec.tc2 tcn__CatExec "Q7'Q@'TFyR0%211':y8%511%311%411'R6'L'K&R7r8r7r6r5r4r3r2%877654321&4&RG%16:98765&R8%11:r1%63E21%73F51%B3F91qYJG1%E2H1pXLG1pWNN1pYLO1pWJK1pW:L1pY8Q21pXDQ61").
Proof.
intros ph sp av ev uid hw rnd. unfold build_stack_bytes, cat_struct_prefix, cat_env_base, cat_string_base.
rewrite (string_addrs_pair av). cbv beta iota.
rewrite (string_addrs_pair ev). cbv beta iota.
eexists. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma bsb_byte_k : ltac2:(TCodec.tc2 tcn__CatExec "R4'Q@'TFyR0%211':y8%511%311%411';'R6&Q4r4&9r6%2281%5241'L'J'K&R7r;r:r9r8r5%675432<1>&4r2&Q7r7(<%11J%44J3:1(6&TEz%22Q01%43Q016%<3Q161r1%>3Q321%?3Q4>1%H3Q4A1%O2Q6@&O&RH%12HG&S4&Q6%13Q;DK%311%7251%Q23Q<91%Q42;1qXFQ@1%Q72QA1qXHQB1%Q92QC1p0Q;1pXLQB1pWNQJ1pYLQK1pX4QF1pWJQH1pW:QI1pY8QO1pXDR31").
Proof.
intros ph sp av ev k uid hw rnd Hk.
destruct (bsb_strings_split ph sp av ev uid hw rnd) as [tail E].
rewrite (flatten_strings_decomp av k Hk) in E.
exists (cat_struct_prefix ph sp av ev uid hw ++ flatten_strings (firstn k av)).
eexists.
split.
- rewrite E. rewrite <- !app_assoc. reflexivity.
- rewrite length_app, length_cat_struct_prefix, length_flatten_strings. reflexivity.
Qed.
Lemma read_argv_byte_k : ltac2:(TCodec.tc2 tcn__CatExec "RL'Q@':'QA%211'TFyR0%211y8%411%811%911';'R6&Q4r5&9r7%2281%5241'Q3&Q7r6r8(<%11@%54@431%;2B1%82=1&S=&S;&TIr:%22K1&S>&R7r<r9r4r3%57483AI21%I2Q01%811%=2:1&S?+2+R0%3221%C251'K'=%11Q9&S1&R9r;&R4r=%2713IDQ3Q:C%5241&TG&RE%147MHQ6&Q<%11Q>%53QJ31u1%>4N821(3(6&4%QA4QLQ?Q6Q=&TEz%22R11%63R11QA%63R251%QG4R3QK13%93R41QD%;2R41%N3L=1p0Q01p0QE1p0QO1pXLR61pWNR=1pYLR>1pX2R:1pX4R;1pWJR=1pW:R>1pY8RC1pY6RG1pXDRK1").
Proof.
intros ph segs sp av ev k j uid hw rnd Hk Hj Hnw.
destruct (bsb_byte_k ph sp av ev k uid hw rnd Hk) as [pre [post [E Hlen]]].
pose proof (read_byte_at_image segs ph sp av ev uid hw rnd
pre (nth k av [] ++ [Z_to_bv 8 0]) post j E) as H'.
rewrite Hlen in H'.
replace (cat_argv_ptr sp av ev k + nat_to_word j)
with (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av) + j)).
2:{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
rewrite !nat_to_word_add_merge. f_equal. f_equal. lia. }
apply H'; [rewrite length_app; cbn [length]; lia | exact Hnw].
Qed.
Lemma read_argv_str_k : ltac2:(TCodec.tc2 tcn__CatExec "R8'Q@':'QA%211'TFyR0%211y8%411%811%911';'R6&Q4r4&9r6%2281%5241&S=&S;&TIr8%22B1&S>&R7r:r7r3r2%57483>@21%@2G1%811%=2:1&S?+2+R0%3221%C251'K'=%11Q0&S1&R9r9&R4r;r5%3724JE1Q2D%6251&RE%147MHQ3&Q7(<%11Q>%34Q>Q7Q11%Q92Q@1%?4O861(3%12QB4%E3C31p0G1p0Q<1pXLQC1pWNQJ1pYLQK1pX4QG1pWJQI1pW:QJ1pY8QO1pY6R31pXDR71").
Proof.
intros ph segs sp av ev k uid hw rnd Hk Hnw.
destruct (bsb_byte_k ph sp av ev k uid hw rnd Hk) as [pre [post [E Hlen]]].
pose proof (read_at_offset_image segs ph sp av ev uid hw rnd
pre (nth k av []) ([Z_to_bv 8 0] ++ post) (length (nth k av []))) as H.
rewrite Hlen in H.
replace (cat_argv_ptr sp av ev k)
with (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
2:{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
rewrite nat_to_word_add_merge. reflexivity. }
apply H; [ | reflexivity | exact Hnw].
rewrite E. rewrite <- !app_assoc. reflexivity.
Qed.
Definition byte_at (s : list byte) (k : nat) : byte :=
nth k (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0).
Lemma nth_lt_byte_at : ltac2:(TCodec.tc2 tcn__CatExec "I':'TFy8%211%411';&Q4r1&9r2%2271%5241'K&RDr3%2216&Q7&TEz%22A1%44A;61%93B61p0;1pX2B1pY4D1").
Proof. intros s j Hj. unfold byte_at. apply app_nth1. exact Hj. Qed.
Lemma byte_at_len : ltac2:(TCodec.tc2 tcn__CatExec "@':'TFy8%211%411'K&RDr1&9%1262%4231&TEz%22;1%93;41pY4;1").
Proof.
intros s. unfold byte_at. rewrite app_nth2 by lia.
rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma byte_at_nz : ltac2:(TCodec.tc2 tcn__CatExec "M':'TFy8%211%411';&M&S7&TEz%2281r2%53921%711&Q4&9r3%22>1%4271'K&RDr4%2216%43D1=%B11p071p0=1pX2F1pY4H1").
Proof.
intros s j Hnz Hj Hc.
apply Hnz. rewrite <- Hc. rewrite nth_lt_byte_at by exact Hj.
apply nth_In. exact Hj.
Qed.
Lemma byte_at_bound : ltac2:(TCodec.tc2 tcn__CatExec "A':'TFy8%211%411';&S=&TI&RDr2r1%3221%52:1+X0%8221pX2:1pY4<1").
Proof. intros s j. unfold byte_at. apply nth_app0_bound. Qed.
Lemma valid_argv_len : ltac2:(TCodec.tc2 tcn__CatExec "C':'TFy8%211%411%511&R5r1%211&S<&S>&9r2%2291%411+QP0%7221p091pW:=1").
Proof. intros av [Hlen _]. lia. Qed.
Lemma valid_argv_nonempty : ltac2:(TCodec.tc2 tcn__CatExec "A':'TFy8%211%411%511&R5r1%211'Q3u1&9r2%2291%5241p071pW:;1").
Proof. intros av [Hlen _]. lia. Qed.
Lemma valid_argv_str_len : ltac2:(TCodec.tc2 tcn__CatExec "N':'TFy8%211%411%511';&R5r2%211&Q4&9r3%2291%4261&S<&S>&Q7r4(<%11A%44A931%;2C1%711+SooO%:221p0<1p0B1pX4F1pW:H1").
Proof.
intros av k [_ [_ [Hstr _]]] Hk.
rewrite Forall_forall in Hstr.
specialize (Hstr _ (nth_In av [] Hk)). exact Hstr.
Qed.
Lemma valid_argv_str_nz : ltac2:(TCodec.tc2 tcn__CatExec "O':'TFy8%211%411%511';&R5r2%211&Q4&9r3%2291%4261&M&S7&TEz%22A1&Q7r4(<%11D%44D<31%93F61%;11p0=1p0C1pX4G1pW:I1").
Proof.
intros av k [_ [_ [_ [Hnz _]]]] Hk.
rewrite Forall_forall in Hnz. apply Hnz. apply nth_In. exact Hk.
Qed.
Lemma valid_argv_str_plain : ltac2:(TCodec.tc2 tcn__CatExec "Q:':'TFy8%211%411%511';&R5r2%211&Q4(2%114&9r3%22;1%6241'K'5&Q?&Q7%:17r4(<%11E%54E431&R=%8221(7%<3;21&R<%D19r5%=4M219%411(@%C3B21p081p0F1p0N1pX4Q21pW:Q41").
Proof.
intros av k [_ [_ [_ [_ Hpl]]]] Hk Hdot.
assert (Hnth : nth (S k) av [] = nth k (tl av) []).
{ destruct av as [|a av']; [cbn in Hk; lia | reflexivity]. }
assert (Hk' : (k < length (tl av))%nat).
{ destruct av as [|a av']; cbn in *; lia. }
rewrite Forall_forall in Hpl.
destruct (Hpl _ (nth_In (tl av) [] Hk')) as [Hsl Hdd].
rewrite Hnth in Hdot |- *.
unfold openat_plain_name, path_is_dirref.
rewrite Hdot, Hsl, Hdd. reflexivity.
Qed.
Lemma valid_argv_str_bytes : ltac2:(TCodec.tc2 tcn__CatExec "Q1':'TFy8%211%411%511';&R5r2%211&Q4&9r3%2291%4261'Q5&S=&TIr1%22A1+X0%5221qW<C1&Q7r4(<%11G%44G?31%=3I61p0?1p0E1pX4I1pW:K1").
Proof.
intros av k _ _. apply Forall_forall. intros b _. apply u8_range.
Qed.
Lemma v_addi_pred : ltac2:(TCodec.tc2 tcn__CatExec "@'TFyR0%211'K&S5&TGr1(TD+1(I%33921%63:51-1%9221%;3<18pZ2=1").
Proof.
intro x. apply bv_eq. unfold v_addi.
rewrite Z_to_bv_unsigned, bv_add_unsigned.
change (bv_unsigned (1 : word)) with 1%Z.
rewrite bv_wrap_add_idemp_l.
replace (bv_unsigned x + 1 + -1)%Z with (bv_unsigned x) by lia.
apply bv_wrap_bv_unsigned.
Qed.
Definition pend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
: machine_state :=
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some (Z_to_bv 64 64);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}.
Lemma adv_set : ltac2:(TCodec.tc2 tcn__CatExec "QC&RBy5'TFyR0%211%5241'=%113y8%711%411p071'K'QG&R3&QN(QBr6&RNvSM%211r5r4(0%11D&RM%117r3r2%=8<9875321r1%@221%B11&S0&S2(TD+:(I%33Q521%53F19&S5+4%22E1%:5H41@?%Q03O<1pYNQ91pXNQ31pX<Q41pYHQ91pXBQ=1pXJQ=1").
Proof.
intros regs pc sv mem rom v.
unfold advance_past_svc, set_gpr0, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom].
unfold mkst, regupd.
rewrite b_npc4. reflexivity.
Qed.
Lemma tw_write_gen : ltac2:(TCodec.tc2 tcn__CatExec "S0':'QA%211&RBy5'TFyR0%211%5241'=y8%611%311p061%>13%?11'K&QH&RIr7r6r5r4%544321(1%8221&TE+1%22F1%=3F41%E1@&QJr8%?41>=<u1%B221u2%D241%73531(3%12JB%I3;31'Q3&9%12Q1G%32;1';r1%62>1r2%72Q7B%9221'RKr>&S0vSM&S2r=(TD+:(I%33QI21&Q;&Q6r3r9%33QG21%52QH1%<3;71&S5r<+4%3221r;r:%E5D7321%H4G1Q<QIp0J1p0N1pX@Q11%QN476?Q@(6%13R4QOQN%O4=31QNp051p0Q81p0Q=1p0QJ1pWFRA1pWDR:1pWBR<1pXNR>1pX<R?1pXBRF1pXJRF1pY6RM1").
Proof.
intros segs regs pc mem rom buf bufs code Hg0 Hr Hnb Hcont.
eapply tw_write;
[reflexivity | reflexivity | exact Hg0 | exact Hr | exact Hnb | ].
intros n Hn1 Hn2. unfold pend. rewrite adv_set. apply Hcont; assumption.
Qed.
Lemma tw_exit0 : ltac2:(TCodec.tc2 tcn__CatExec "Q:':'QA%211'QG'TFyR0%211'K'=%113&QMr2%211(3r1%2291%93741&RL%117&QHr4(1%3221&TEz%22D1%C3D41'RKr6r5(<y8%L11%Q111%411%84761:p0:1p0C1p0F1pZ4Q11pX>Q51pY6Q71").
Proof.
intros segs ms x8 Hsvc Hex Hg0.
assert (Hc : bv_and (ms_gpr ms 0) (Z_to_bv 64 255) = Z_to_bv 64 0).
{ rewrite Hg0. apply bv_eq.
rewrite bv_and_unsigned, !Z_to_bv_unsigned. reflexivity. }
rewrite <- Hc. eapply tw_exit; eassumption.
Qed.
Lemma tw_write_rec : ltac2:(TCodec.tc2 tcn__CatExec "SE':'QA%211&RBy5'TFyR0%211%5241'=y8%611%311p061%>13%?11'K'Q9&TI&ROr7(TD+A(I%33D21%6251%82D1+R0%<3;21&RCr8+:%;3L19%4231&TE+1%22N1%E3N41%M1H&QJ(QBr9&RNvSM%211(3%K25F%22Q81(0%11Q:&RM%118r6%=8<9G642Q11+;%Q23QC1Q0%K2?1+<%Q53QF1Q3%N2B1%E3741r5%A2Q@1%Q?3I31'Q3u1&9%12QH?%4231';r1%7261r2%72QNQ0%:221'RKr?&S0&S2r>&Q;&Q6r3r:%33R921%52R:1%837QF1&S5r=+4%3221r<r;%@5QB7321%C4B1QER0p0E1p0I1pX@L1%R?27R:%QF2RL1%QL89QH81QCQAAQK(6%13RHR8RB%L4?31QCp071p0Q51p0Q;1p0R61p0R@1pWFS61pWDRO1pWBS11pXNS31pX<S41pXBS;1pXJS;1pY6SB1").
Proof.
intros segs regs pc mem rom buf bufs code H17 H10 Hr Hnb Hcont.
eapply tw_write.
- cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_0. exact H10.
- unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_1, arg_reg_2. exact Hr.
- exact Hnb.
- intros n Hn1 Hn2. rewrite adv_set. apply Hcont; assumption.
Qed.
Lemma tw_exit_rec : ltac2:(TCodec.tc2 tcn__CatExec "QO':'QA%211&RBy5'TFyR0%211%5241'=y8%611%311p061'K'Q9&TI&ROr4(TD+A(I%33B21%6251%82B1+RM%<3;21&RCr5+:%;3J19%4231&TEz%22L1%E3L41'RKr7(QBr6&RNvSM%211(3%K25F%22Q61(0%11Q8&RM%118r3%=8<9G642Q11(<%QE1Q:%211%C4B41Ep0E1p0O1pXNQ=1pX<Q>1pXBQE1pXJQE1pY6QL1").
Proof.
intros segs regs pc mem rom H17 H10.
eapply tw_exit0.
- cbn [ms_svc_pending]. reflexivity.
- left. exact H17.
- unfold ms_gpr. cbn [ms_regs].
rewrite arg_reg_0. exact H10.
Qed.
End WithFP.
