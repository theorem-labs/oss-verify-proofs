(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Mem Cells Step Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RMalloc_iface RF_aligned RF_aligned_spec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge Require Import HeapInst0 HeapClosed.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec CatExec SeqExec StoreOk MemSplit AgentLib StartupTac RefLayout ArgvEnv LibTail ZStores
SymExec2 SymExec2Sound SymDriveX DrvKit
SymDrive Js0StartupDefs Js0Startup Js0StartupFacts Js0MainEntry HeapIface LibIface Js0DrvLib Js0DrvLibL Js0DrvG Js0DrvMain Js0Exit_run1.
Import ListNotations.
Import SX2. Import SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0HeapBridge () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.HeapInst0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvMain."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StartupDefs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StartupFacts."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"]; ["3map"; "4Z"; "5Segment"; "6store_ok"; "7segments_reserved"; "7valid_brk"; "7valid_mmap_base"; "7valid_sp"; "8mkVmMapsFull"; "0RND"; "9B0"; "9HI0"; "9K0"; "9L0"; "9init_statics0"; ":cell"]; [":cells_bytes"; ":cells_size"; ":cells_wf"; ";bytes_at"; ";wr_at"; "<rw_cells"; "=rsegs"; ">hi_heap"; "?drv_layout"; "@src_realizes_stmt2"; "AD_main"; "BD_main_missb"; "Crdn"; "Dloaded_segments"; "Eadd"; "Ele"]; ["Elt"; "Eof_nat"; "Epow"; "Esub"; "Eto_nat"; "0a"; "0a0s"; "0brk"; "0bs"; "0bs1"; "0bs2"; "0cs"; "0envv"; "0hi"; "0hw"; "0l1"]; ["0l2"; "0lim"; "0lo"; "0m"; "0mbase"; "0mem0"; "0n"; "0path"; "0scfg"; "0segs"; "0sp"; "0sp0"; "FZ_to_bv"; "Fbv"; "Fbv_unsigned"; "0tid"]; ["0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hfs : sc_fs scfg = true.
#[local] Existing Instance PropExec.fx0.
Lemma drv_layout_L0 : ltac2:(TCodec.tc2 tcn__Js0HeapBridge "?'R=yR0%211&Gr1%211'Q8&M&R>r2%2291%411%6213p081pTF<1").
Proof.
intros sp Hsp. constructor; try reflexivity.
- intros a Ha. cbn [hl_alloc_static L0] in Ha. unfold RMLOCK, RCTX in Ha. lia.
- intros a Ha. cbn [hl_alloc_ro L0] in Ha. unfold IMG_LO, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD in Ha. lia.
- cbn [hl_stack L0]. unfold RALIGNED_STACK, RMALLOC_STACK. lia.
- cbn [hl_k_per_malloc L0]. unfold KPM. lia.
- cbn [hl_b_overhead L0]. vm_compute. discriminate.
Qed.
Lemma bytes_at_of_rdn : ltac2:(TCodec.tc2 tcn__Js0HeapBridge "QE'7'B%211'R=yR0%211':y8%511%311p051'A%<14'?%812&Q<r4r3&R<r2%22@1&6r1%22?1%948741(2%12>4%>3=31&Q?z%221=&Q>&QA%<2I@%211%42C1&QB+2+R0%3221%<251&Q3r7r6r5%44321Mp061p0A1p0E1pSBQ51pS<Q71pT8Q91pTDQB1").
Proof.
intros segs m a bs Hr Ha Hb. split; [exact Ha|]. split; [exact Hb|].
revert a Hr Ha Hb. induction bs as [|b bs IH]; intros a Hr Ha Hb i Hi; [cbn in Hi; lia|].
cbn [length] in Hr. rewrite rdn_unfold in Hr. fold (wa a) in Hr.
destruct (mrd segs m (wa a)) as [b0|] eqn:E0; [|discriminate].
destruct (rdn segs m (wa a + 1)%bv (length bs)) as [r|] eqn:E1; [|discriminate].
injection Hr as <- <-.
destruct i as [|i].
- cbn. rewrite Z.add_0_r. exact E0.
- cbn [nth_error]. replace (a + Z.of_nat (S i)) with ((a + 1) + Z.of_nat i) by lia.
cbn [length] in Hb.
apply (IH (a + 1)); [| lia | lia | cbn in Hi; lia].
rewrite wa_succ in E1. exact E1.
Qed.
Lemma wr_at_of_store_ok : ltac2:(TCodec.tc2 tcn__Js0HeapBridge "QB'7'B%211'R=yR0%211':y8%511%311p051'A'8'?'4&Cr4r3&R<r2%22@1r1%746521(=%;3:21&Q?z%221:&Q>&QA%11=%32?1&QB+2+R0%3221%;251&Q4r7r6r5%<1I%544321p071p0A1p0E1pT>Q21pS<Q41pT8Q61pTDQ?1").
Proof.
intros segs m a n Hs Ha Hb. split; [exact Ha|]. split; [exact Hb|]. intros i Hi.
pose proof (store_ok_wview segs m (Z_to_bv 64 a) n (Z.to_nat i) Hs ltac:(lia)) as W.
rewrite u_small in W by lia. rewrite Z2Nat.id in W by lia. exact W.
Qed.
Lemma bytes_at_app2 : ltac2:(TCodec.tc2 tcn__Js0HeapBridge "Q6'7'B%211'R=yR0%211':y8%511%311p051'A%<14&Q3r5r4r3r2%544321r6&Q>&QA&6%12?7%311%52:1%=47<19r7&3%13E>=%A43;@1p051p0>1pSFE1pSDF1pS<H1pT8J1pTDQ31").
Proof. intros. apply bytes_at_app. split; assumption. Qed.
Section MainEntry.
Context {RE : RunEnv}.
Variable sp0 : word.
Variables a0s path : list byte.
Variable envv : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rdraw : EntryDraw.
Variable tid : word.
Variable regs0 : bvmap 5 word.
Variable mem0 : word -> option byte.
Hypothesis Hva : valid_argv [a0s; path].
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
Let RND : bv 128 := ed_random rdraw.
Let Hlo : 0x7fff80000000 <= bv_unsigned sp0 := proj1 Hvsp.
Let Hhi : bv_unsigned sp0 <= 0x800000000000 := proj1 (proj2 Hvsp).
Lemma rdn_main_data : ltac2:(TCodec.tc2 tcn__Js0HeapBridge "QA'A'8&Q?zr2%3221&Q>r3&QA%115%4231+mTP0%:221'?':'7'R=y8%211%411%611&Q<&Q=vR5&R<yR0r4%3221%74651E&Q:vR;(5vQFvR7(9%11@%53A31%63B51vQLvQNvIvR?%=6<54321%F4E1@Q4%O3H@1p0Q11p0Q91pT>Q>1pS<Q@1").
Proof.
intros a n Ha Hn. apply (main_entry_rdn_data sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME).
rewrite u_small by lia. unfold stack_max_size. lia.
Qed.
Lemma rdn_main_img : ltac2:(TCodec.tc2 tcn__Js0HeapBridge "Q;'A'8'?'4&Q;r2r1%3221(=%73621&Q?&Q>r3&QA%119%4231+mTP0%7221':'7'R=y8%211%411%611&Q<&Q=vR5&R<yR0r4%3221%74651D%=14(1%11=q031%<4;16I%Q43>61p0F1p0O1pT>Q81pS<Q:1").
Proof.
intros a n Hb Hn.
assert (Ha : 0 <= a).
{ unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb]. apply Z.leb_le in Hb. exact Hb. }
rewrite rdn_main_data by lia. apply (D_main_miss sp0 [a0s; path] envv hw rdraw tid). exact Hb.
Qed.
Lemma mem_main_none : ltac2:(TCodec.tc2 tcn__Js0HeapBridge "Q='A'R=yR0%211'?'4&Q;r3&QD&QCr2%2214%411%7261(=%;3:21'>&Q?r4%221<+mTP0%42>1%6231r5&R>%12GB%9231&Q@%123:%=231':y8%O11%311vR5%11A(1%115%Q23531p0:1p0B1p0J1pU2Q71pSLQ;1pT6Q<1").
Proof.
intros lo hi x Hb Hhi' Hx.
assert (Hlo0 : 0 <= lo).
{ unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb]. apply Z.leb_le in Hb. exact Hb. }
rewrite <- (Z_to_bv_bv_unsigned 64 x).
rewrite (main_entry_mem_data sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
apply (D_main_none sp0 [a0s; path] envv hw RND tid (bv_unsigned x) Hva Hlo Hhi).
apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
Qed.
Lemma store_ok_data : ltac2:(TCodec.tc2 tcn__Js0HeapBridge "M'A'8&Q?+fdP0r2%3221&Q>r3&QA%115%4231+mTP0%:221'?'4&C&Q=vR5&R<yR0r4%3221%74651?(=%;3:21p0=1p0E1pT>J1pS<L1").
Proof.
intros a n Ha Hn.
eapply (store_ok_window RSEGS mem0 (Z_to_bv 64 0xb5000) (Z_to_bv 64 a) 0x34000 n 0xb5000 0xe9000);
[reflexivity | reflexivity | lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
Qed.
Lemma store_ok_relro : ltac2:(TCodec.tc2 tcn__Js0HeapBridge "M'A'8&Q?+elP0r2%3221&Q>r3&QA%115%4231+fdP0%:221'?'4&C&Q=vR5&R<yR0r4%3221%74651?(=%;3:21p0=1p0E1pT>J1pS<L1").
Proof.
intros a n Ha Hn.
eapply (store_ok_window RSEGS mem0 (Z_to_bv 64 0xaf000) (Z_to_bv 64 a) 24576 n 0xaf000 0xb5000);
[reflexivity | reflexivity | lia | vm_compute; reflexivity | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
Qed.
Lemma rw_cells_of_rdn : ltac2:(TCodec.tc2 tcn__Js0HeapBridge "R1'A'7'O%211&Q2r1%211'?':'R=y8%211%;11%511&Q<&Q=vR5&R<yR0r3%3221&6&Q0r2%211%42>1%<4;:61(2%12@4%F3@31'4&Cr4%@2?1&Q1%11@%54ED31(=%O3821&Q?zr5%3221&Q>r6&QA%<15%211%5241&QB+2+R0%3221%>251&Q5&Q6r7%342Q91=p051p0A1p0F1p0Q01p0QH1pSHQL1p2R01").
Proof.
intros A cs Hwf Hr Hs HA HB. pose proof (cells_bytes_length cs Hwf) as HL.
split; [split; [exact Hwf|]|].
- apply bytes_at_of_rdn; [exact Hr | exact HA | rewrite HL; exact HB].
- apply wr_at_of_store_ok; [exact Hs | exact HA | exact HB].
Qed.
Lemma bytes_eq_of_unsigned : ltac2:(TCodec.tc2 tcn__Js0HeapBridge "E'7'R=y8%211%411'?'A%711&@&R>%118r2%449621r1%64;841%:3831r3%<3=16p031pT2?1pT0@1").
Proof.
intros l1. induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
Ltac img_read a n :=
rewrite (rdn_main_img a n) by (first [vm_compute; reflexivity | lia]);
lazymatch goal with |- ?l = Some _ => let v := eval vm_compute in l in change l with v end;
f_equal; apply bytes_eq_of_unsigned; vm_compute; reflexivity.
Lemma main_init_statics0 : ltac2:(TCodec.tc2 tcn__Js0HeapBridge "7&N&R>yR0vR;%3221vR5%6221").
Proof.
pose proof (u64_range tid) as Ht.
destruct (auxvp_u sp0 a0s path envv uid hw rdraw Hva Hve Hvsp) as [AV1 AV2].
destruct (rnd_u sp0 a0s path envv uid hw rdraw Hva Hve Hvsp) as (RN1 & RN2 & RN3 & RN4).
pose proof (u64_range (auxvp sp0 a0s path envv)) as AVR. pose proof (u64_range (rnd sp0 a0s path envv)) as RNR.
pose proof (u64_range uid) as UR. pose proof (u64_range hw) as HWR. pose proof (u64_range (canary_w RND)) as CR.
unfold init_statics0.
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
-
intros a Ha. apply (mem_main_none 0xe8068 0xe8418 a); [vm_compute; reflexivity | lia | exact Ha].
-
intros a Ha. apply (mem_main_none RVMLOCKC (RVMLOCKC + 4) a); [vm_compute; reflexivity | lia | exact Ha].
-
apply rw_cells_of_rdn; [cbn; tauto | | apply store_ok_data; cbn; lia | lia | cbn; lia].
cbn [length cells_bytes cbytes app]. img_read 0xe7ef3 1%nat.
-
apply rw_cells_of_rdn; [cbn; tauto | | apply store_ok_data; cbn; lia | lia | cbn; lia].
cbn [length cells_bytes cbytes le8 word_to_le_bytes Z_to_le_bytes app].
rewrite rdn_main_data by (cbn; lia). apply (D_main_pagesize sp0 [a0s; path] envv hw rdraw tid Hva).
-
apply rw_cells_of_rdn; [cbn; tauto | | apply store_ok_relro; cbn; lia | lia | cbn; lia].
cbn [length cells_bytes cbytes le8 word_to_le_bytes Z_to_le_bytes app]. img_read 0xb4ec8 8%nat.
-
exists (bv_unsigned (canary_w RND)). split; [lia|].
apply rw_cells_of_rdn; [cbn; tauto | | apply store_ok_data; cbn; lia | lia | cbn; lia].
cbn [length cells_bytes cbytes le8 word_to_le_bytes Z_to_le_bytes app]. rewrite Z_to_bv_bv_unsigned.
exact (main_entry_guard sp0 [a0s; path] envv uid hw rdraw tid (proj1 Hvsp) regs0 mem0 ME RSEGS).
-
set (sec := firstn 8 (skipn 8 (at_random_bytes RND))).
assert (Lsec : length sec = 8%nat) by (subst sec; rewrite length_firstn, length_skipn, length_at_random_bytes; reflexivity).
exists (bv_unsigned (auxvp sp0 a0s path envv)), (Z.of_N (ph_addr RPH)), (Z.of_N (ph_ent RPH)), (Z.of_N (ph_num RPH)), (bv_unsigned hw),
4096, (bv_unsigned uid), (bv_unsigned uid), 0, (bv_unsigned (rnd sp0 a0s path envv)), (bytes_le_to_Z sec).
pose proof (bytes_le_to_Z_bound sec) as SB. rewrite Lsec in SB.
split; [|split; [|split]].
+ apply rw_cells_of_rdn; [cbn; tauto | | unfold RAUXV_CELL; apply store_ok_data; cbn; lia | unfold RAUXV_CELL; lia | unfold RAUXV_CELL; cbn; lia].
unfold RAUXV_CELL. cbn [length cells_bytes cbytes le8 word_to_le_bytes Z_to_le_bytes app].
rewrite rdn_main_data by (cbn; lia). unfold wz. rewrite Z_to_bv_bv_unsigned. apply (D_main_auxvp sp0 a0s path envv hw rdraw tid Hvsp).
+
cbn [map u64s app].
repeat (apply bytes_at_app2; [|cbn [length le8 word_to_le_bytes Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add]]);
[.. | apply bytes_at_nil; lia];
(apply bytes_at_of_rdn; [| lia | cbn [length le8 word_to_le_bytes Z_to_le_bytes]; lia]);
cbn [length le8 word_to_le_bytes Z_to_le_bytes]; unfold wz;
lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) 8 = _ =>
first [ replace a with (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat 0) by lia;
rewrite (main_auxv sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp ME 0%nat) by lia
| let rec go j := (replace a with (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j) by lia;
rewrite (main_auxv sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp ME j) by lia)
|| go (S j) in go 1%nat ]
end;
cbn [nth]; rewrite ?Z_to_bv_bv_unsigned; try reflexivity.
all: vm_compute; reflexivity.
+
apply bytes_at_of_rdn; [| lia | unfold le8; rewrite length_word_to_le_bytes; lia]. unfold le8. rewrite length_word_to_le_bytes.
rewrite (main_entry_rdn_above sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME); [ | rewrite u_small by lia; lia | rewrite u_small by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
pose proof (rdn_wmem_stack RSEGS RPH sp0 [a0s; path] envv uid hw rdraw) as Hw. unfold wmem in Hw.
rewrite Hw; [ | rewrite u_small by lia; lia | rewrite u_small by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
replace (bv_unsigned (rnd sp0 a0s path envv) + 8) with (bv_unsigned (rnd sp0 a0s path envv) + Z.of_nat 8) by lia.
rewrite (RN4 8%nat 8%nat ltac:(lia)). fold sec. rewrite (word_to_le_bytes_of_lez 8 sec Lsec ltac:(lia)). reflexivity.
+ pose proof (proj1 Hvsp).
change (Z.of_N (ph_addr RPH)) with 0x10040%Z. change (Z.of_N (ph_ent RPH)) with 56%Z. change (Z.of_N (ph_num RPH)) with 10%Z. lia.
-
intros a b Hab. destruct (ro_addr rsegs a) eqn:E; [|reflexivity]. exfalso.
apply ref_ro_addr_true in E. unfold IMG_LO in E.
rewrite (mem_main_none 0x10000 0xaf000 a) in Hab; [discriminate | vm_compute; reflexivity | lia | lia].
Qed.
Theorem main_hi_heap0 : ltac2:(TCodec.tc2 tcn__Js0HeapBridge "Q?'R=yR0%211'A&E&Q=r3%3221&F%113&Q?&QB+2+Q2%3221%5219&Q7&K&R>vR;%22C1%411(9'<%12EE%311(;&L&J%34JJ21vR5(H&D%11L%;2Q0Q0%=11r6r4r5%886443321D%H5C?;:1p0J1p0Q11p0Q41pT4Q91pT:Q;1pS@Q<1").
Proof.
intros brk mbase lim Hbrk Hmb Hlim.
apply (HI0_init (bv_unsigned sp0) mem0 lim); [apply main_init_statics0|].
exists brk, mbase, sp0. split; [reflexivity|]. split; [exact Hbrk|]. split; [exact Hmb|]. split; [exact Hvsp|]. split; [reflexivity | exact Hlim].
Qed.
End MainEntry.
Section WithLib.
Variable LayF : word -> lib_layout.
Variable LStF : word -> lib_statics.
Hypothesis DLLF : forall sp, valid_sp sp -> drv_lib_layout (LayF sp) (L0 (bv_unsigned sp)).
Hypothesis LIokF : forall sp, valid_sp sp -> lib_iface_ok (LayF sp) scfg (HI0 (bv_unsigned sp)) (LStF sp).
Hypothesis LSXF : forall sp, valid_sp sp -> forall g M, ls_ok (LStF sp) g M -> exists reg : bool, ax_block M reg.
Hypothesis Hbudget : forall sp n, valid_sp sp -> 0 <= n < 67108864 ->
cred (L0 (bv_unsigned sp)) (KPM + 4 * fst (ll_credit (LayF sp) n)) (n + BOV + 4 * snd (ll_credit (LayF sp) n)) 0
(debit (L0 (bv_unsigned sp)) (K0, B0) 65536).
Theorem src0_realizes_spec_heap : ltac2:(TCodec.tc2 tcn__Js0HeapBridge "3&Q9vR8%211").
Proof.
apply (src0_realizes_spec scfg (fun sp => L0 (bv_unsigned sp)) (fun sp => HI0 (bv_unsigned sp)) LayF LStF (K0, B0)).
- intros sp Hsp. apply HI0_ok_closed. exact Halloc.
- exact drv_layout_L0.
- exact DLLF.
- exact LIokF.
- exact LSXF.
- intros sp a0s path envp uid hw rdraw tid regs mem brk mbase Hsp Hbrk Hmb Hva Hve Htid ME.
apply (main_hi_heap0 sp a0s path envp uid hw rdraw tid regs mem Hva Hve Hsp Htid ME brk mbase source_alloc_limit Hbrk Hmb).
unfold source_alloc_limit. lia.
- exact Hfs.
- exact Hbudget.
Qed.
End WithLib.
End FPX_1.
