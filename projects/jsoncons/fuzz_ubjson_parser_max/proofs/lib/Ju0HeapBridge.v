(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: adds zpair and auxv_pairs_* lemmas for the variable-length auxiliary vector, threads ProcInput and launch parameters through main_entry uses, reworks main_init_statics1 via read_auxv_all, and takes main_hi_heap1's mapping base from the section, as in fuzz_bigint's copy; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/Ub0HeapBridge.v, 107 lines within its lines 28-347. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Mem Cells Step Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMalloc_iface RF_aligned RF_aligned_spec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge Require Import HeapInst1 HeapClosed.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec CatExec SeqExec StoreOk MemSplit AgentLib StartupTac RefLayout ArgvEnv LibTail ZStores
SymExec2 SymExec2Sound SymDriveX DrvKit
SymDrive Ju0StartupDefs Ju0Startup Ju0StartupFacts Ju0MainEntry HeapIface LibIface Ju0DrvLib Ju0DrvLibL Ju0DrvG Ju0DrvMain Ju0Exit_run1.
Import ListNotations.
Import SX2. Import SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0HeapBridge () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.HeapInst1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvMain."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0StartupDefs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0StartupFacts."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"]; ["3map"; "4Z"; "5Segment"; "6store_ok"; "7segments_reserved"; "7valid_brk"; "7valid_mmap_base"; "7valid_sp"; "8mkVmMapsFull"; "0RND"; "9B0"; "9HI1"; "9K0"; "9L1"; "9init_statics1"; ":cell"]; [":cells_bytes"; ":cells_size"; ":cells_wf"; ";bytes_at"; ";wr_at"; "<rw_cells"; "=rsegs"; ">hi_heap"; "?drv_layout"; "@tgt_realizes_stmt2"; "AD_main"; "BD_main_missb"; "Crdn"; "Dloaded_segments"; "Eadd"; "Ele"]; ["Elt"; "Eof_nat"; "Epow"; "Esub"; "Eto_nat"; "0a"; "0a0s"; "0brk"; "0bs"; "0bs1"; "0bs2"; "0cs"; "0envv"; "0hi"; "0hw"; "0l1"]; ["0l2"; "0lim"; "0lo"; "0m"; "0mbase"; "0mem0"; "0n"; "0path"; "0scfg"; "0segs"; "0sp"; "0sp0"; "FZ_to_bv"; "Fbv"; "Fbv_unsigned"; "0tid"]; ["0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition zpair (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (snd e)).
Lemma map_wz_flat_pairs_zpair : forall es : list (word * word),
map (Z_to_bv 64) (flat_pairs (map zpair es)) = flat_map (fun e : word * word => [fst e; snd e]) es.
Proof.
induction es as [|[a b] es IH]; [reflexivity|]. cbn [map flat_pairs zpair flat_map fst snd app].
rewrite IH. rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma auxv_pairs_words : forall la ph entry uid gid hw r x,
map (Z_to_bv 64) (flat_pairs (map zpair (removelast (auxv_entries la ph entry uid gid hw r x))) ++ [0; 0])
= flat_map (fun e : word * word => [fst e; snd e]) (auxv_entries la ph entry uid gid hw r x).
Proof.
intros. remember (auxv_entries la ph entry uid gid hw r x) as es eqn:Ees.
assert (E : es = removelast es ++ [(AT_NULL, Z_to_bv 64 0)])
by (subst es; unfold auxv_entries; destruct (la_rseq la); reflexivity).
rewrite E at 2. rewrite flat_map_app, map_app, map_wz_flat_pairs_zpair. reflexivity.
Qed.
Lemma auxv_pairs_length : forall la ph entry uid gid hw r x,
(length (map zpair (removelast (auxv_entries la ph entry uid gid hw r x))) + 1 = auxv_count (la_rseq la))%nat.
Proof. intros. rewrite length_map. unfold auxv_entries, auxv_count. destruct (la_rseq la); reflexivity. Qed.
Lemma auxv_pairs_facts : forall la ph entry uid gid hw r x,
let L := map zpair (removelast (auxv_entries la ph entry uid gid hw r x)) in
Forall (fun p => fst p <> 0) L /\ last_assoc 25 L = Some (bv_unsigned r)
/\ Forall (fun p => fst p = 25 -> snd p = bv_unsigned r) L
/\ Forall (fun p => 0 <= fst p < 2^64 /\ 0 <= snd p < 2^64) L.
Proof.
intros. subst L.
assert (RG : forall w : word, 0 <= bv_unsigned w < 2^64)
by (intros w; pose proof (bv_unsigned_in_range 64 w) as R; unfold bv_modulus in R; cbn in R; lia).
unfold auxv_entries; destruct (la_rseq la); cbn [removelast map app]; unfold zpair; cbn [fst snd];
unfold AT_SYSINFO_EHDR, AT_L1I_CACHESIZE, AT_L1I_CACHEGEOMETRY, AT_L1D_CACHESIZE, AT_L1D_CACHEGEOMETRY,
AT_L2_CACHESIZE, AT_L2_CACHEGEOMETRY, AT_L3_CACHESIZE, AT_L3_CACHEGEOMETRY, AT_MINSIGSTKSZ, AT_HWCAP,
AT_PAGESZ, AT_CLKTCK, AT_PHDR, AT_PHENT, AT_PHNUM, AT_BASE, AT_FLAGS, AT_ENTRY, AT_UID, AT_EUID, AT_GID,
AT_EGID, AT_SECURE, AT_RANDOM, AT_EXECFN, AT_RSEQ_FEATURE_SIZE, AT_RSEQ_ALIGN;
(split; [repeat (apply Forall_cons; [cbn [fst snd]; rewrite u_small by lia; lia|]); apply Forall_nil|]);
(split; [reflexivity|]);
(split; [repeat (apply Forall_cons; [cbn [fst snd]; intros HK; first [reflexivity | rewrite u_small in HK by lia; lia]|]);
apply Forall_nil|]);
repeat (apply Forall_cons; [cbn [fst snd]; split; [rewrite u_small by lia; lia| apply RG]|]); apply Forall_nil.
Qed.
Lemma u64s_flat_map_le8 : forall ws, u64s ws = flat_map word_le8 ws.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [u64s flat_map]. rewrite IH. reflexivity. Qed.
Section FPX_1.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hfs : sc_fs scfg = true.
#[local] Existing Instance PropExec.fx0.
Lemma drv_layout_L1 : forall sp, valid_sp sp -> drv_layout (L1 (bv_unsigned sp)) sp.
Proof.
intros sp Hsp. constructor; try reflexivity.
- intros a Ha. cbn [hl_alloc_static L1] in Ha. unfold RMLOCK, RCTX in Ha. lia.
- intros a Ha. cbn [hl_alloc_ro L1] in Ha. unfold IMG_LO, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD in Ha. lia.
- cbn [hl_stack L1]. unfold RALIGNED_STACK, RMALLOC_STACK. lia.
- cbn [hl_k_per_malloc L1]. unfold KPM. lia.
- cbn [hl_b_overhead L1]. vm_compute. discriminate.
Qed.
Lemma bytes_at_of_rdn : forall segs m (a : Z) (bs : list byte),
rdn segs m (Z_to_bv 64 a) (length bs) = Some bs -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
bytes_at segs m a bs.
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
Lemma wr_at_of_store_ok : forall segs m (a : Z) (n : nat),
store_ok segs m (Z_to_bv 64 a) n = true -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> wr_at segs m a (Z.of_nat n).
Proof.
intros segs m a n Hs Ha Hb. split; [exact Ha|]. split; [exact Hb|]. intros i Hi.
pose proof (store_ok_wview segs m (Z_to_bv 64 a) n (Z.to_nat i) Hs ltac:(lia)) as W.
rewrite u_small in W by lia. rewrite Z2Nat.id in W by lia. exact W.
Qed.
Lemma bytes_at_app2 : forall segs m a bs1 bs2,
bytes_at segs m a bs1 -> bytes_at segs m (a + Z.of_nat (length bs1)) bs2 -> bytes_at segs m a (bs1 ++ bs2).
Proof. intros. apply bytes_at_app. split; assumption. Qed.
Section MainEntry.
Context {RE : RunEnv}. Context {RO : ReaderOn}.
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
Variable inp : ProcInput.
Variable mbase entry : word.
Hypothesis ME : main_entry inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
Let RND : bv 128 := ed_random rdraw.
Let Hlo : 0x7fff80000000 <= bv_unsigned sp0 := proj1 Hvsp.
Let Hhi : bv_unsigned sp0 <= 0x800000000000 := proj1 (proj2 Hvsp).
Lemma rdn_main_data : forall (a : Z) (n : nat), 0 <= a -> a + Z.of_nat n <= 0xea000 ->
rdn RSEGS mem0 (Z_to_bv 64 a) n = rdn RSEGS (D_main inp sp0 rdraw RND tid) (Z_to_bv 64 a) n.
Proof.
intros a n Ha Hn. apply (main_entry_rdn_data inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME).
rewrite u_small by lia. unfold stack_max_size. lia.
Qed.
Lemma rdn_main_img : ltac2:(TCodec.tc2 tcn__Ju0HeapBridge "Q;'A'8'?'4&Q;r2r1%3221(=%73621&Q?&Q>r3&QA%119%4231+mXP0%7221':'7'R=y8%211%411%611&Q<&Q=vR5&R<yR0r4%3221%74651D%=14(1%11=q031%<4;16I%Q43>61p0F1p0O1pT>Q81pS<Q:1").
Proof.
intros a n Hb Hn.
assert (Ha : 0 <= a).
{ unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb]. apply Z.leb_le in Hb. exact Hb. }
rewrite rdn_main_data by lia. apply (D_main_miss inp sp0 rdraw tid). exact Hb.
Qed.
Lemma mem_main_none : ltac2:(TCodec.tc2 tcn__Ju0HeapBridge "Q='A'R=yR0%211'?'4&Q;r3&QD&QCr2%2214%411%7261(=%;3:21'>&Q?r4%221<+mXP0%42>1%6231r5&R>%12GB%9231&Q@%123:%=231':y8%O11%311vR5%11A(1%115%Q23531p0:1p0B1p0J1pU2Q71pSLQ;1pT6Q<1").
Proof.
intros lo hi x Hb Hhi' Hx.
assert (Hlo0 : 0 <= lo).
{ unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb]. apply Z.leb_le in Hb. exact Hb. }
rewrite <- (Z_to_bv_bv_unsigned 64 x).
rewrite (main_entry_mem_data inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
destruct (main_entry_inp inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME) as (Eav & _).
apply (D_main_none inp sp0 rdraw RND tid (bv_unsigned x) ltac:(rewrite Eav; exact Hva) Hlo Hhi).
apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
Qed.
Lemma store_ok_data : ltac2:(TCodec.tc2 tcn__Ju0HeapBridge "M'A'8&Q?+fhP0r2%3221&Q>r3&QA%115%4231+mXP0%:221'?'4&C&Q=vR5&R<yR0r4%3221%74651?(=%;3:21p0=1p0E1pT>J1pS<L1").
Proof.
intros a n Ha Hn.
eapply (store_ok_window RSEGS mem0 (Z_to_bv 64 0xb6000) (Z_to_bv 64 a) 0x34000 n 0xb6000 0xea000);
[reflexivity | reflexivity | lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
Qed.
Lemma store_ok_relro : ltac2:(TCodec.tc2 tcn__Ju0HeapBridge "M'A'8&Q?+fPP0r2%3221&Q>r3&QA%115%4231+fhP0%:221'?'4&C&Q=vR5&R<yR0r4%3221%74651?(=%;3:21p0=1p0E1pT>J1pS<L1").
Proof.
intros a n Ha Hn.
eapply (store_ok_window RSEGS mem0 (Z_to_bv 64 0xb0000) (Z_to_bv 64 a) 24576 n 0xb0000 0xb6000);
[reflexivity | reflexivity | lia | vm_compute; reflexivity | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
Qed.
Lemma rw_cells_of_rdn : forall (A : Z) cs,
cells_wf cs ->
rdn RSEGS mem0 (Z_to_bv 64 A) (length (cells_bytes cs)) = Some (cells_bytes cs) ->
store_ok RSEGS mem0 (Z_to_bv 64 A) (cells_size cs) = true ->
0 <= A -> A + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
rw_cells rsegs mem0 A cs.
Proof.
intros A cs Hwf Hr Hs HA HB. pose proof (cells_bytes_length cs Hwf) as HL.
split; [split; [exact Hwf|]|].
- apply bytes_at_of_rdn; [exact Hr | exact HA | rewrite HL; exact HB].
- apply wr_at_of_store_ok; [exact Hs | exact HA | exact HB].
Qed.
Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
intros l1. induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
Ltac img_read a n :=
rewrite (rdn_main_img a n) by (first [vm_compute; reflexivity | lia]);
lazymatch goal with |- ?l = Some _ => let v := eval vm_compute in l in change l with v end;
f_equal; apply bytes_eq_of_unsigned; vm_compute; reflexivity.
Lemma main_init_statics1 : init_statics1 (bv_unsigned sp0) mem0.
Proof.
pose proof (u64_range tid) as Ht.
destruct (auxvp_u sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME) as [AV1 AV2].
destruct (rnd_u sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME) as (RN1 & RN2 & RN3 & RN4).
pose proof (u64_range (auxvp sp0 a0s path envv)) as AVR. pose proof (u64_range (rnd sp0 a0s path envv inp)) as RNR.
pose proof (u64_range uid) as UR. pose proof (u64_range hw) as HWR. pose proof (u64_range (canary_w RND)) as CR.
unfold init_statics1.
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
-
intros a Ha. apply (mem_main_none 0xe90b8 0xe9468 a); [vm_compute; reflexivity | lia | exact Ha].
-
intros a Ha. apply (mem_main_none RVMLOCKC (RVMLOCKC + 4) a); [vm_compute; reflexivity | lia | exact Ha].
-
apply rw_cells_of_rdn; [cbn; tauto | | apply store_ok_data; cbn; lia | lia | cbn; lia].
cbn [length cells_bytes cbytes app]. img_read 0xe8f43 1%nat.
-
apply rw_cells_of_rdn; [cbn; tauto | | apply store_ok_data; cbn; lia | lia | cbn; lia].
cbn [length cells_bytes cbytes le8 word_to_le_bytes Z_to_le_bytes app].
rewrite rdn_main_data by (cbn; lia).
destruct (main_entry_inp inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME) as (Eav & _).
apply (D_main_pagesize inp sp0 rdraw tid ltac:(rewrite Eav; exact Hva)).
-
apply rw_cells_of_rdn; [cbn; tauto | | apply store_ok_relro; cbn; lia | lia | cbn; lia].
cbn [length cells_bytes cbytes le8 word_to_le_bytes Z_to_le_bytes app]. img_read 0xb5f18 8%nat.
-
exists (bv_unsigned (canary_w RND)). split; [lia|].
apply rw_cells_of_rdn; [cbn; tauto | | apply store_ok_data; cbn; lia | lia | cbn; lia].
cbn [length cells_bytes cbytes le8 word_to_le_bytes Z_to_le_bytes app]. rewrite Z_to_bv_bv_unsigned.
first [ exact (main_entry_guard sp0 [a0s; path] envv uid hw rdraw tid Hva Hlo regs0 mem0 inp mbase entry ME RSEGS)
| exact (main_entry_guard sp0 [a0s; path] envv uid hw rdraw tid Hva Hlo Hhi regs0 mem0 inp mbase entry ME RSEGS)
| exact (main_entry_guard sp0 [a0s; path] envv uid hw rdraw tid Hva regs0 mem0 inp mbase entry ME RSEGS)
| exact (main_entry_guard sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 inp mbase entry ME RSEGS) ].
-
set (sec := firstn 8 (skipn 8 (at_random_bytes RND))).
assert (Lsec : length sec = 8%nat) by (subst sec; rewrite length_firstn, length_skipn, length_at_random_bytes; reflexivity).
pose proof (bytes_le_to_Z_bound sec) as SB. rewrite Lsec in SB.
destruct (main_entry_inp inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME) as (Eav & Eev & _ & _ & Hvl & brk & Hlau).
assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva).
assert (Hve' : valid_envp (in_envp inp)) by (rewrite Eev; exact Hve).
pose proof (proj1 Hvsp) as SPLO. pose proof (proj1 (proj2 Hvsp)) as SPHI.
set (rw := at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)).
set (xw := at_execfn_ptr (ed_top rdraw) (in_execfn inp)).
assert (Erw : rnd sp0 a0s path envv inp = rw) by (unfold rnd, rw; rewrite Eav, Eev; reflexivity).
rewrite Erw in RN1, RN2, RN3, RN4, RNR.
set (ES := auxv_entries (launch_auxv inp sp0 mbase) RPH entry (in_uid inp) (in_gid inp) (in_hwcap inp) rw xw).
pose proof (auxv_pairs_length (launch_auxv inp sp0 mbase) RPH entry (in_uid inp) (in_gid inp) (in_hwcap inp) rw xw) as PL.
destruct (auxv_pairs_facts (launch_auxv inp sp0 mbase) RPH entry (in_uid inp) (in_gid inp) (in_hwcap inp) rw xw)
as (NZ & LA & R25 & RNG).
fold ES in PL, NZ, LA, R25, RNG.
assert (AOB : (auxv_off (in_argv inp) (in_envp inp) + auxv_size (kb_rseq (in_kernel inp)) + 16
<= length (entry_stack_image inp mbase RPH entry sp0 rdraw))%nat)
by (eapply auxv_off_bound; first [exact Hva' | exact Hve' | exact Hvl | exact Hlau | exact RSEGS | exact Sv48 | eassumption | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)]).
pose proof (entry_stack_image_no_wrap Sv48 inp mbase RPH entry sp0 brk rdraw Hlau) as NW.
assert (AVU : bv_unsigned (auxvp sp0 a0s path envv) = bv_unsigned sp0 + Z.of_nat (auxv_off (in_argv inp) (in_envp inp)))
by (rewrite AV1, Eav, Eev; reflexivity).
assert (ASZ : auxv_size (kb_rseq (in_kernel inp)) = (16 * auxv_count (kb_rseq (in_kernel inp)))%nat) by reflexivity.
change (la_rseq (launch_auxv inp sp0 mbase)) with (kb_rseq (in_kernel inp)) in PL.
exists (bv_unsigned (auxvp sp0 a0s path envv)), (map zpair (removelast ES)), (bv_unsigned rw), (bytes_le_to_Z sec).
split; [|split; [|split; [|split; [|exact (conj NZ (conj LA (conj R25 RNG)))]]]].
+ apply rw_cells_of_rdn; [cbn; tauto | | unfold RAUXV_CELL; apply store_ok_data; cbn; lia | unfold RAUXV_CELL; lia | unfold RAUXV_CELL; cbn; lia].
unfold RAUXV_CELL. cbn [length cells_bytes cbytes le8 word_to_le_bytes Z_to_le_bytes app].
rewrite rdn_main_data by (cbn; lia). rewrite Z_to_bv_bv_unsigned. eapply (D_main_auxvp sp0 a0s path envv uid hw rdraw tid regs0 mem0); eassumption.
+ subst ES. rewrite auxv_pairs_words, u64s_flat_map_le8.
change (flat_map (fun e : word * word => [fst e; snd e])
(auxv_entries (launch_auxv inp sp0 mbase) RPH entry (in_uid inp) (in_gid inp) (in_hwcap inp) rw xw))
with (auxv_words (launch_auxv inp sp0 mbase) RPH entry (in_uid inp) (in_gid inp) (in_hwcap inp) rw xw).
rewrite <- auxv_bytes_words.
rewrite AVU.
apply bytes_at_of_rdn;
[| lia | rewrite length_auxv_bytes; change (la_rseq (launch_auxv inp sp0 mbase)) with (kb_rseq (in_kernel inp)); lia].
rewrite length_auxv_bytes. change (la_rseq (launch_auxv inp sp0 mbase)) with (kb_rseq (in_kernel inp)).
rewrite <- word_add_nat_Z2bv.
rewrite (main_entry_rdn_above inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME);
[ | rewrite word_add_nat_Z2bv, u_small by lia; lia | rewrite word_add_nat_Z2bv, u_small by lia; lia ].
pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw. unfold wmem in Hw.
rewrite Hw; [ | rewrite word_add_nat_Z2bv, u_small by lia; lia | rewrite word_add_nat_Z2bv, u_small by lia; lia ].
eapply read_auxv_all; first [exact Hva' | exact Hve' | exact Hvl | exact Hlau | exact RSEGS | exact Sv48 | eassumption | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)].
+ apply bytes_at_of_rdn; [| lia | unfold le8; rewrite length_word_to_le_bytes; lia]. unfold le8. rewrite length_word_to_le_bytes.
rewrite (main_entry_rdn_above inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME); [ | rewrite u_small by lia; lia | rewrite u_small by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw. unfold wmem in Hw.
rewrite Hw; [ | rewrite u_small by lia; lia | rewrite u_small by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
replace (bv_unsigned rw + 8) with (bv_unsigned rw + Z.of_nat 8) by lia.
rewrite (RN4 8%nat 8%nat ltac:(lia)). fold sec. rewrite (word_to_le_bytes_of_lez 8 sec Lsec ltac:(lia)). reflexivity.
+ rewrite length_map. pose proof (Nat2Z.inj_add (length (removelast ES)) 1) as LN.
rewrite length_map in PL.
assert (Hc : (Z.of_nat (length (removelast ES)) + 1 = Z.of_nat (auxv_count (kb_rseq (in_kernel inp))))%Z) by lia.
rewrite AVU. repeat split; try lia.
-
intros a b Hab. destruct (ro_addr rsegs a) eqn:E; [|reflexivity]. exfalso.
apply ref_ro_addr_true in E. unfold IMG_LO in E.
rewrite (mem_main_none 0x10000 0xb0000 a) in Hab; [discriminate | vm_compute; reflexivity | lia | lia].
Qed.
Theorem main_hi_heap1 : forall brk (lim : Z),
valid_brk RSEGS brk -> valid_mmap_base mbase -> 2 ^ 34 <= lim ->
hi_heap (HI1 (bv_unsigned sp0)) [] (K0, B0) mem0 (mkVmMapsFull (init_reserved (segments_reserved RSEGS) mbase sp0 (in_kernel inp)) [] [] brk brk lim mbase sp0).
Proof.
intros brk lim Hbrk Hmb Hlim.
apply (HI1_init (bv_unsigned sp0) mem0 lim); [apply main_init_statics1|].
exists brk, mbase, sp0, (in_kernel inp). split; [reflexivity|]. split; [exact Hbrk|]. split; [exact Hmb|]. split; [exact Hvsp|]. split; [reflexivity | exact Hlim].
Qed.
End MainEntry.
Section WithLib.
Variable LayF : word -> lib_layout.
Variable LStF : word -> lib_statics.
Hypothesis DLLF : forall sp, valid_sp sp -> drv_lib_layout (LayF sp) (L1 (bv_unsigned sp)).
Hypothesis LIokF : forall sp, valid_sp sp -> lib_iface_ok (LayF sp) scfg (HI1 (bv_unsigned sp)) (LStF sp).
Hypothesis LSXF : forall sp, valid_sp sp -> forall g M, ls_ok (LStF sp) g M -> exists reg : bool, ax_block M reg.
Hypothesis Hbudget : forall sp n, valid_sp sp -> 0 <= n < 67108864 ->
cred (L1 (bv_unsigned sp)) (KPM + 4 * fst (ll_credit (LayF sp) n)) (n + BOV + 4 * snd (ll_credit (LayF sp) n)) 0
(debit (L1 (bv_unsigned sp)) (K0, B0) 65536).
Theorem ub0_realizes_spec_heap : tgt_realizes_stmt2 scfg.
Proof.
apply (ub0_realizes_spec scfg (fun sp => L1 (bv_unsigned sp)) (fun sp => HI1 (bv_unsigned sp)) LayF LStF (K0, B0)).
- intros sp Hsp. apply HI1_ok_closed. exact Halloc.
- exact drv_layout_L1.
- exact DLLF.
- exact LIokF.
- exact LSXF.
- intros sp a0s path envp uid hw rdraw tid regs mem brk mbase inp Hsp Hbrk Hmb Hva Hve Htid ME.
eapply (main_hi_heap1 sp a0s path envp uid hw rdraw tid regs mem); try eassumption; unfold target_alloc_limit; lia.
Unshelve. all: try exact (run_env_at inp (Vdso.vdso_run_init (ed_vdso rdraw))).
- exact Hfs.
- exact Hbudget.
Qed.
End WithLib.
End FPX_1.
