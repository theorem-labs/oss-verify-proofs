(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
MmapSim AllocSim FileSim AgentLib SpecConsts DivergeSim SpinAlg SpinAlgX
SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame
Spec LibWritev RefNodes RefMemcpyLib RefReadLib RefPrintfLib Ju0StartupDefs Ju0Startup Ju0MainEntry Hoare MemSplit Frame
Ju0MemcpyBase Ju0Memcpy Ju0ExitBase Ju0StdioDefs Ju0Exit Ju0LibStdioCall Ju0LibMainRet Ju0PrintfBufBase Ju0PrintfBuf
HeapIface LibIface DrvKit Ju0Drv_defs Ju0DrvLib Ju0DrvA Ju0DrvB Ju0DrvC_defs Ju0DrvC Ju0DrvD_defs Ju0DrvLibL Ju0DrvD.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0DrvE () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0AtexitCells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvD_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvE.FPX_1.DrvE."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0Drv_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0MainEntry."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0StartupDefs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0StdioDefs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Spec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A1"; "0CAP"; "1O"; "1S"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1negb"; "1nil"; "1option"; "1pair"; "1prod"]; ["1true"; "2I"; "2and"; "2eq"; "2not"; "2or"; "3add"; "3mul"; "4le"; "4lt"; "5nth"; "6Z"; "0ENVb"; "0HI"; "0K"; "0L"]; ["0LB"; "0LSt"; "7word_to_le_bytes"; "8mkCfg"; "9ed_random"; ":Model"; ":VmMaps"; ":event"; ":m_vmmaps"; ";BC_NE"; "<bvmap"; "0M"; "0M'"; "0PL"; "0R"; "=regions_ok"]; [">frame_mod"; ">outside"; "?block_range"; "?credit"; "?hi_heap"; "?model_but_vm"; "@atexit_cells"; "Alay_ext"; "BIMG_PF"; "Bdec_x"; "Bkeep_pf"; "BknX0"; "BsrLH"; "BsrX0"; "CCANZ"; "CCPpf"]; ["CE"; "CLH2P"; "CSCpf"; "CSSP"; "CWP"; "Cpf_rs"; "Crelay2"; "Crelay2_ok_b"; "Dhas_window"; "Dhz"; "EIMG_RW"; "Fauxvp"; "Fblobs0"; "Frnd"; "Gcanary_w"; "Hssp_cells"]; ["Ils_ok"; "Ils_state"; "JFPState"; "Jgetr"; "Jmkst"; "Jrdn"; "Jseg_rom"; "KTSet"; "Lzero_lines"; "Msrealizes"; "Nblobs_ev"; "Nkblob_find"; "Nkread"; "OELit"; "OEnv"; "OSA"]; ["OSCBr"; "OSE"; "Oedenot"; "Oexpr"; "Okentry"; "Osentry"; "Pknow_ok"; "Pmem_denot"; "Pregs_ok"; "Psc_denot"; "Qenv_agree"; "Qvals_ev"; "Rloaded_segments"; "SIn"; "Stl"; "Tadd"]; ["Teqb"; "Tle"; "Tlt"; "Tof_nat"; "Tpow"; "Tsub"; "0VM"; "0W"; "0a"; "0a0s"; "0above"; "0ax"; "0bs"; "0cr"; "0data"; "0envv"]; ["0fdata"; "0fx'"; "0g"; "0hw"; "0i"; "0j"; "0k"; "0kn"; "0m'"; "0model2"; "0n"; "0path"; "0rdraw"; "0scfg"; "0sp0"; "0sr"]; ["UBV"; "UZ_to_bv"; "Ubv"; "Ubv_unsigned"; "0t"; "0tid"; "0v"; "0vals"; "0w"; "0x"]]).
Local Ltac tauto := L5FastTauto.ptauto0.
Open Scope bv_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac lia := first [ solve [ try (match goal with H : (length _ <= S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _)))))))))))))))))))))))))))))))))%nat |- _ => clear dependent H end); Lia.lia ] | Lia.lia ].
Tactic Notation "run_blockT" constr(scr) constr(NX) := run_block_gen FUEL STOPS_T scr NX false.
Tactic Notation "run_blockT_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_T scr NX true.
Tactic Notation "run_blockP_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_P scr NX true.
Tactic Notation "run_blockR_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_R scr NX true.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
#[using="Type"] Lemma length_zero_lines : ltac2:(TCodec.tc2 tcn__Ju0DrvE "?':'C&8'TBy8%211&RHr1%211%7241&Gu2%2215%<3=41pX<>1").
Proof. induction j as [|j IH]; [reflexivity|]. cbn [zero_lines length]. rewrite IH. lia. Qed.
#[using="Type"] Lemma zero_lines_snoc : ltac2:(TCodec.tc2 tcn__Ju0DrvE "K':'C'9'TBy8%211%411&RH(3r1%211%411&5%614(7&TA+Q@%22=1+:%42?1(<%11@%83A31%93B61%<3C;1%H3C>1pX<J1").
Proof. induction j as [|j IH]; [reflexivity|]. cbn [zero_lines]. rewrite IH at 1. reflexivity. Qed.
Section DrvE.
Context {RE : RunEnv}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L scfg HI.
Variable sp0 : word.
Variables a0s path : list byte.
Variable envv : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rdraw : EntryDraw.
Variable tid : word.
Variable regs0 : bvmap 5 word.
Variable mem0 : word -> option byte.
Variable VM0 : VmMaps.
Variable fs0 : Fs.
Variable stdin0 : InputStream.
Variable fdata : list byte.
Variable cr0 : credit.
Hypothesis Hva : valid_argv [a0s; path].
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
Hypothesis Hplen : (length path <= 4095)%nat.
Hypothesis DL : drv_layout L sp0.
Variable CAP : Z.
Hypothesis HCAP : (65536 <= CAP <= 67108864)%Z.
Variable crC : credit.
Hypothesis HLEN : (Z.of_nat (length fdata) < CAP)%Z.
Variable Lay : lib_layout.
Variable LSt : lib_statics.
Hypothesis DLL : drv_lib_layout Lay L.
Hypothesis LIok : lib_iface_ok Lay scfg HI LSt.
Hypothesis LSX : forall g M, ls_ok LSt g M -> exists reg : bool, ax_block M reg.
Let Hsp : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z := conj (proj1 Hvsp) (proj1 (proj2 Hvsp)).
Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
Let LEN : Z := Z.of_nat (length fdata).
Let ENVb (vals : list word) : env := ENV a0s path hw rdraw fdata vals.
Let above (M : word -> option byte) : Prop := above_sp0 sp0 mem0 M.
Let model2 (VM : VmMaps) : Model := model2 tid fs0 stdin0 VM.
Let CFG : Z := CFG fdata.
Let PL : Z := PL fdata.
Let B2 : Z := B2 fdata.
Let CALLS : Z := CALLS fdata.
Let payload : list byte := payload fdata.
Let lh_vals := lh_vals sp0 a0s path envv tid fdata.
Let blk_facts := blk_facts L fdata CAP.
Let lh1_k := lh1_k scfg L HI sp0 a0s path envv hw rdraw tid mem0 fs0 stdin0 fdata CAP crC.
Let relay_regs := relay_regs sp0 a0s path hw rdraw tid mem0 VM0 fs0 stdin0 fdata Hvsp Htid Hplen CAP HCAP.
Let relay_agree := relay_agree sp0 a0s path hw rdraw fdata Hplen.
Let relay_len := relay_len sp0 path fdata Hplen.
Let relay_lo := relay_lo sp0 path fdata Hplen.
Let relay_81 := relay_81 sp0 path fdata Hplen.
Let relay_101 := relay_101 sp0 path fdata Hplen.
Let hiv_facts' := hiv_facts' sp0 a0s path envv uid hw rdraw Hva Hve Hvsp Hplen.
Let content_block' := content_block' sp0 a0s path hw rdraw fdata Hvsp.
Hypothesis Hok : (6 + CFG <= LEN)%Z.
Definition E (n : nat) : TSet := t_emit (W 1 (zero_lines n)) (t_exit (exit_code 0) fs0).
Definition WP (j : nat) : Z := (0xe94a0 + 2 * Z.of_nat j)%Z.
Definition SSP (k : Z) (j : nat) (K : TSet) : Prop :=
forall (fx' : PropExec.FPState) vals R M VM (A1 PTR OWN : Z) LB cr g,
lh_vals vals A1 PTR OWN k -> vals_ev vals 84 = Z_to_bv 64 0 -> vals_ev vals 101 = Z_to_bv 64 (WP j) ->
(Z.of_nat j + k <= 4)%Z -> (1 <= k)%Z ->
regs_ok (ENVb vals) srLH R -> know_ok RSEGS (ENVb vals) M knLH2 ->
above M -> blk_facts A1 PTR OWN LB ->
rdn RSEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
rdn RSEGS M (Z_to_bv 64 PTR) (length payload) = Some payload ->
rdn RSEGS M (Z_to_bv 64 0xe94a0) (length (zero_lines j)) = Some (zero_lines j) ->
hi_heap HI LB cr M VM -> credit_le (credit_scale (k - 1) (ll_credit Lay PL)) cr ->
ls_ok LSt g M ->
srealizes RSEGS scfg (mkCfg (@mkst fx' R (Z_to_bv 64 0x341c8) M (seg_rom RSEGS)) (model2 VM)) K.
Definition LH2P (k : Z) (j : nat) (K : TSet) : Prop :=
forall (fx' : PropExec.FPState) vals R M VM (A1 PTR OWN : Z) LB cr g,
lh_vals vals A1 PTR OWN k -> vals_ev vals 101 = Z_to_bv 64 (WP j) ->
(Z.of_nat j + k <= 3)%Z -> (1 <= k)%Z ->
regs_ok (ENVb vals) srLH R -> know_ok RSEGS (ENVb vals) M knLH2 ->
above M -> blk_facts A1 PTR OWN LB ->
rdn RSEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
rdn RSEGS M (Z_to_bv 64 PTR) (length payload) = Some payload ->
rdn RSEGS M (Z_to_bv 64 0xe94a0) (length (zero_lines j)) = Some (zero_lines j) ->
hi_heap HI LB cr M VM -> credit_le (credit_scale k (ll_credit Lay PL)) cr ->
ls_ok LSt g M ->
srealizes RSEGS scfg (mkCfg (@mkst fx' R (Z_to_bv 64 0x341a4) M (seg_rom RSEGS)) (model2 VM)) K.
#[using="Type"] Lemma m2_but' : ltac2:(TCodec.tc2 tcn__Ju0DrvE "@'Q6'Q5&QEvT9r2%211r1%5221'C&Q8%116%811%43;81p061pXB=1pW>?1").
Proof. intros VM m' H. exact H. Qed.
#[using="sp0 path Hvsp Hplen CAP HCAP HLEN Hsp LEN CFG B2 CALLS Hok"] Lemma PL_range' : ltac2:(TCodec.tc2 tcn__Ju0DrvE "8'B&SAzvQ=%3221+QooooI%5231%7231").
Proof. subst PL CFG LEN. unfold Ju0DrvC.PL. pose proof (CFG_range fdata). lia. Qed.
#[using="sp0 Hplen LEN CFG PL B2 CALLS"] Lemma dec_val : ltac2:(TCodec.tc2 tcn__Ju0DrvE "Q5'9'TByR0%211%411'K'C&S;r2uRA%3221&TAr1%22;1%83;41'B&SA+1%221:+4%42<1%6231&S2vLr4%211&QI%5221&SEr3%221=%D2M1%J3M51p0<1p0D1pX>N1pY@Q01").
Proof.
intros vals k P81 Hk. unfold dec_x. cbn [edenot ev ENVb ENV]. rewrite P81.
assert (k = 1 \/ k = 2 \/ k = 3 \/ k = 4)%Z as [-> |[-> |[-> | ->]]] by lia; vm_compute; reflexivity.
Qed.
#[using="sp0 Hplen LEN CFG PL B2 CALLS"] Lemma dec_sc : ltac2:(TCodec.tc2 tcn__Ju0DrvE "QI'9'TByR0%211%411'=y8%611%311p061'K'6'C&S;r4uRA%3221&TAr2%22A1%83A41'B&SA+1r3%3221+4%5231%7231&;&S@&SE%12B9z%4221%611%H3I1<&S9&S<r6vLr7%211(S0(Q9&QI(RM%11>%54Q2431%<4;:71p0>1p0G1p0Q01pY:Q:1pX>Q<1pRHQ>1pY@QD1").
Proof.
intros vals M k t P81 Hk Ht. cbn [sc_denot branch_taken]. rewrite (dec_val vals k P81 Hk). cbn [edenot].
unfold bv_eqb. rewrite !u_small by lia. exact Ht.
Qed.
Definition CANZ : Z := bv_unsigned (canary_w (ed_random rdraw)).
#[using="Type"] Lemma can_of_know : ltac2:(TCodec.tc2 tcn__Ju0DrvE "QK'9'TByR0%211%411'=y8%611%311p061'S4%;11&S6&S<vLr3%211r2r1%746321'C'?'S3':%3221%D11&RK(RMz%211+mSi0%53>21(4(>+8%811u2%44?>21%62>1%C3>81%Q81Q1%Q411&REr4&TA%12Q;?u8%54Q2421&Q2&QN%62Q@1%3251%D2<1%Q13<61p0?1p0Q41pX@Q=1pRHQ@1pY@QF1").
Proof.
intros vals M kn HK Hc. unfold CANZ. rewrite Z_to_bv_bv_unsigned.
pose proof (kblob_rdn RSEGS (ENVb vals) M kn (ELit 0) 0xe8f20 (ELit 8) 2%nat HK Hc) as R.
replace (adenot (ENVb vals) (SA (ELit 0) 0xe8f20)) with (Z_to_bv 64 0xe8f20) in R by (apply bv_eq; vm_compute; reflexivity).
cbn [eb ENVb ENV blobs_ev nth app blobs0] in R. rewrite length_word_to_le_bytes in R. exact R.
Qed.
#[using="Type"] Lemma CANZ_range : ltac2:(TCodec.tc2 tcn__Ju0DrvE "<'B&SAz&QN%3221&SB&SD+2+R0%3221%5271%;271").
Proof. unfold CANZ. apply u64_range. Qed.
#[using="sp0 Hplen LEN CFG PL B2 CALLS"] Lemma ssp_of_know : ltac2:(TCodec.tc2 tcn__Ju0DrvE "QN'9'TByR0%211%411'=y8%611%311p061'S4%;11&S6&S<vLr3%211r2r1%746321'C'S3%A11&RL(RMz%211+fghHu8%65@<321(4+mSi0%811%32<1%>3<51'?':%22@1%Q111&RK%13I>9(>+8%C11u2%44H921%@291%K3971&R?r5&R>&Q4vT<%211%411%7261p091p0G1p0Q71pX@Q@1pRHQC1pY@QI1").
Proof.
intros vals M kn HK Hg Hc. split.
- pose proof (kread_rdn RSEGS (ENVb vals) M kn (ELit 0) 0xb5f18 8 (ELit 0xe8f20) HK Hg ltac:(lia) ltac:(lia) ltac:(apply flat_abs0; lia)) as R.
replace (adenot (ENVb vals) (SA (ELit 0) 0xb5f18)) with (Z_to_bv 64 0xb5f18) in R by (apply bv_eq; vm_compute; reflexivity). exact R.
- pose proof (kblob_rdn RSEGS (ENVb vals) M kn (ELit 0) 0xe8f20 (ELit 8) 2%nat HK Hc) as R.
replace (adenot (ENVb vals) (SA (ELit 0) 0xe8f20)) with (Z_to_bv 64 0xe8f20) in R by (apply bv_eq; vm_compute; reflexivity).
cbn [eb ENVb ENV blobs_ev nth app blobs0] in R. rewrite length_word_to_le_bytes in R. exact R.
Qed.
#[using="HIok uid Hva Hve Hvsp Htid Hplen DL HCAP Hsp Hal LEN CFG PL B2 CALLS hiv_facts'"] Lemma tail_X : ltac2:(TCodec.tc2 tcn__Ju0DrvE "U3'RB':'9'TByR0%211%411&Q:y5%2214'=y8%911%311p091'Q6'K&QC'C&8r6%22@1uT6%53F21&S;r7(2%3221vT>%;3H21r8uQ@%8221&TAr4%22O1%B3O41r9u3%?221&R;vSIvT;vSO%44@321%K3Q861r:u4%H221&R=%14F987%Q13Q>31r;u5%N221vTE%Q63QC21r<uRD%Q3221z%L2QI1%Q<3QI31r=uS5%Q9221&R4r?%211%Q42R11%QD3R151&SA&SCr@%211+3%5221&S8vL%11<&QMr>%53321&S6&S<%71<&QK%443261&QBvOv1%332L1%RJ1R@%RC11&RE+mUU0%QO2RL1&RHrD%211%RA2RH1%74AL51(4%12;4%RF3;31&QDvM(7'?%12RMRM(>%14ROROQ<E(<%114%73531rA%;5:2Q31Q;&QFrBrE%3221'RIvT=(Q3&RDrH+V`_4%RN2SK1rC&RF%11Q>%756Q1431vT9%11?%;231&R0rG%211%A4QF@41p0C1p0H1p0Q51p0QC1p0QH1p0QN1p0R51p0R<1p0RE1p0RL1p0S21p0S91p0SC1p0SK1p0T21pWLT91p2T;1pW>T=1pRHT?1pRNTE1pY@TI1pWHTO1pX<U01pX4U21").
Proof.
intros fx' j ax vals R M VM A1 cr HL P0 P48 P3 P4 P5 P84 P101 Hj HR HK HBR HBUF HH HAX.
pose proof Hsp as Hsp'. pose proof Hal as Hal'.
pose proof (hz_of_block_range L sp0 DL _ _ HBR) as HZ. pose proof HZ as (Q1 & Q2 & Q4).
pose proof (hiv_facts' vals P3 P4) as HIV.
run_blockT_keep scr0 134%nat.
cbn [mem_denot] in EQM. subst M0.
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
destruct (main_ret_0 Rc M (seg_rom RSEGS) ltac:(regv HR (10 : reg); cbn [edenot ev ENVb ENV]; rewrite ?P84; reflexivity))
as (R2 & MS & G8 & G10 & Gother) end.
replace (Z_to_bv 64 212880) with (0x33f90%bv : word) by (apply bv_eq; reflexivity).
eapply srz_msteps; [reflexivity | reflexivity | exact MS |]. clear MS.
replace (0x34010%bv : word) with (Z_to_bv 64 0x34010) by (apply bv_eq; reflexivity).
set (vals2 := vals ++ [getr R2 1; getr R2 11]).
assert (HL2 : length vals2 = 136%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
assert (HR2 : regs_ok (ENVb vals2) srY0 R2).
{ apply regs_ok_by_nth. intros i Hi.
assert (AG : forall e, expr_vars_lt 134 e = true -> edenot (ENVb vals2) e = edenot (ENVb vals) e).
{ intros e He. symmetry. apply (edenot_agree 134); [| exact He]. subst vals2. rewrite <- HL. apply vals_app_agree. }
destruct (Nat.eq_dec i 1) as [->|N1].
{ change (nth 1 srY0 (ELit 0)) with (EVar 134). cbn [edenot ev ENVb ENV]. subst vals2.
rewrite <- HL, <- (Nat.add_0_r (length vals)), vals_ev_app_r. reflexivity. }
destruct (Nat.eq_dec i 11) as [->|N11].
{ change (nth 11 srY0 (ELit 0)) with (EVar 135). cbn [edenot ev ENVb ENV]. subst vals2.
replace 135%nat with (length vals + 1)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
destruct (Nat.eq_dec i 8) as [->|N8]. { change (nth 8 srY0 (ELit 0)) with (ELit 0). exact G8. }
destruct (Nat.eq_dec i 10) as [->|N10]. { change (nth 10 srY0 (ELit 0)) with (ELit 0). exact G10. }
rewrite Gother by (intros E1; apply (f_equal ridx) in E1; rewrite ridx_lit in E1 by lia;
lazymatch type of E1 with i = ridx ?c => let v := eval vm_compute in (ridx c) in change (ridx c) with v in E1 end; lia).
rewrite (HR (Z_to_bv 5 (Z.of_nat i))), sr_get_nat by lia.
assert (EQi : nth i srY0 (ELit 0) = nth i srX (ELit 0) /\ expr_vars_lt 134 (nth i srX (ELit 0)) = true).
{ clear -Hi N1 N11 N8 N10. do 32 (destruct i as [|i]; [first [lia | (split; reflexivity)] |]). lia. }
destruct EQi as [-> Ev]. symmetry. apply AG. exact Ev. }
pose proof (env_app_know RSEGS vals [getr R2 1; getr R2 11] _ M knX0 ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2.
fold vals2 in HK2. change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals2) in HK2.
assert (Y0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (Y3 : vals_ev vals2 3 = auxvp sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P3).
assert (Y4 : vals_ev vals2 4 = rnd sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P4).
assert (Y5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
assert (Y48 : vals_ev vals2 48 = Z_to_bv 64 A1) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
assert (Y101 : vals_ev vals2 101 = Z_to_bv 64 (WP j)) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P101).
pose proof (hiv_facts' vals2 Y3 Y4) as HIV2.
clear HR HK. rename HR2 into HR. rename HK2 into HK. clearbody vals2. clear Gother G8 G10 HL P0 P3 P4 P5 P48 P84 P101 HIV vals.
run_blockT_keep scr0 136%nat.
cbn [mem_denot] in EQM. subst M0.
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
lazymatch type of HK with know_ok _ _ _ ?knc =>
eapply (free_site scfg L HI HIok sp0 Hsp' Hal' DL vals2 _ srY knc Rc Mc (model2 VM) [(A1, CAP)] cr A1 CAP (-128) [] [] 0x34018 (E j)) end;
[ exact HR | exact HK
| rewrite HL2; vm_compute; reflexivity | rewrite HL2; vm_compute; reflexivity | rewrite HL2; lia
| exact Y0 | exact HIV2 | vm_compute; reflexivity
| regv HR (2 : reg); cbn [edenot ev ENVb ENV]; rewrite Y0; apply alu_add_w_lit
| lia | reflexivity
| left; reflexivity
| regv HR (10 : reg); cbn [edenot ev ENVb ENV]; exact Y48
| regv HR (4 : reg); reflexivity
| regv HR (1 : reg); reflexivity
| lia | reflexivity
| exact HH | reflexivity | reflexivity | reflexivity
| intros i nb Hf; discriminate
| intros v b Hf; discriminate
| unfold E; apply t_emit_has_nil | ]
end.
clear HR HK.
intros R' M' model' vals' E' HL' HR HK HH' HBUT HAB HBLK HIMG. subst vals' E'.
rewrite (m2_but' _ _ HBUT).
set (vals3 := vals2 ++ junk_vals R') in *.
change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals3) in HR, HK.
assert (Z0 : vals_ev vals3 0 = sp0) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact Y0).
assert (Z5 : vals_ev vals3 5 = tid) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact Y5).
assert (Z101 : vals_ev vals3 101 = Z_to_bv 64 (WP j)) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact Y101).
assert (HBUF' : rdn RSEGS M' (Z_to_bv 64 0xe94a0) (length (zero_lines j)) = Some (zero_lines j)).
{ rewrite <- HBUF. apply rdn_agree. intros q Hq. rewrite length_zero_lines in Hq. rewrite u_small by lia. apply HIMG; lia. }
assert (HAX' : atexit_cells M' ax) by (apply (atexit_cells_frame M M' ax); [intros q Hq; apply HIMG; lia | exact HAX]).
clear HBUF HIMG HBLK HAB.
rewrite HL2 in HR. try rewrite HL2 in HK.
run_blockT_keep scr0 168%nat.
cbn [mem_denot] in EQM. subst M0.
unfold E.
lazymatch goal with |- srealizes _ _ (mkCfg _ ?model) _ =>
apply (srz_conseq RSEGS scfg _ (t_emit (W 1 (zero_lines j)) (t_exit (bv_and (Z_to_bv 64 0) (Z_to_bv 64 255)) (m_fs model))));
[ | replace (bv_and (Z_to_bv 64 0) (Z_to_bv 64 255)) with (exit_code 0) by (apply bv_eq; reflexivity); apply t_eq_refl ]
end.
apply ref_exit_Z.
lazymatch type of HK with know_ok ?segs ?Ex ?Mx ?kn =>
pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl) as Ktid;
cbn [kentry_ok edenot ev ENVb ENV] in Ktid; rewrite Z5 in Ktid;
exists (Z_to_bv 64 (bv_unsigned sp0 - 48)), (Z_to_bv 64 0xc8cb0), (bv_unsigned tid), (Z_to_bv 64 0), (Z_to_bv 64 0);
split; [|split; [reflexivity|split; [reflexivity|]]];
[ constructor;
[ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVb ENV];
rewrite Z0; f_equal; lia
| regv HR (4 : reg); reflexivity
| regv HR (10 : reg); reflexivity
| rewrite u_small by lia; lia
| rewrite u_small by lia; lia
| rewrite u_small by lia;
pose proof (kwr_store_ok segs Ex _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-192) 144) in exact i)
_ _ _ (-192) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENVb ENV] in Hst; rewrite Z0 in Hst;
replace (bv_unsigned sp0 - 48 - 144)%Z with (bv_unsigned sp0 + -192)%Z by lia; exact Hst
| lit_u; lia
| lit_u; lia
| lia
| lit_u; change (822448 - 168)%Z with 0xc8c08%Z;
krd HK 0xc8c08%Z 4%nat Htc; rewrite Htc; cbn [ev ENVb ENV]; rewrite Z5;
rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
rewrite Z_to_bv_bv_unsigned; reflexivity
| krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | (exists ax; exact HAX') | krd_solve HK
| repeat split; krd_solve HK
| repeat split; krd_solve HK ]
| ]
end.
destruct j as [|j'].
- left. split; [reflexivity|]. exists (Z_to_bv 64 (WP 0)), (Z_to_bv 64 0).
repeat split; try krd_solve HK; cbn [ev ENVb ENV]; rewrite ?Z101; reflexivity.
- right. eexists 955552%Z, (WP (S j')), _, _, (Z_to_bv 64 0), (canary_w (ed_random rdraw)). split; [|reflexivity].
pose proof rw_bytes_max_ge17 as RW. pose proof (length_zero_lines (S j')) as LZ.
constructor; try exact HBUF'; try (rewrite ?LZ; unfold WP; lia); try krd_solve HK; try (cbn [ev ENVb ENV]; rewrite ?Z101; reflexivity).
eapply ssp_of_know; [exact HK | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.
Section SE.
Local Abbreviation SEC_T_last_S := (ltac2:(TCodec.tc2 tcn__Ju0DrvE "8':&R3+1r1&R0%112%53431pX<71")) (only parsing).
Variable j : ltac:(sec_ty2 constr:(SEC_T_last_S) 0%nat 0%nat).
Lemma last_S : ltac:(sec_stmt2 constr:(SEC_T_last_S) 1%nat 0%nat).
Proof using HIok uid Hva Hve Hvsp Htid Hplen DL HCAP Hsp Hal LEN CFG B2 CALLS hiv_facts' LSX j.
unfold SSP.
intros fx' vals R M VM A1 PTR OWN LB cr g (HL & P0 & P1 & P2 & P3 & P4 & P5 & P48 & P70 & P73 & P79 & P81 & P82 & P83)
P84 P101 Hjk Hk HR HK HA HBLK HC HPAY HBUF HH Hcr Hls.
destruct (LSX g M Hls) as [rg HAXb].
assert (HAX : atexit_cells M (if rg then 2%nat else 1%nat)) by (apply atexit_cells_of_block; [krd_solve HK | exact HAXb]).
set (ax := if rg then 2%nat else 1%nat) in HAX. clearbody ax. clear HAXb rg.
pose proof Hsp as Hsp'. pose proof Hal as Hal'.
pose proof (hiv_facts' vals P3 P4) as HIV.
pose proof (regs_ok_upd_same (ENVb vals) srLH R (19%bv : reg) (ELit 0) HR ltac:(discriminate)
ltac:(symmetry; regv HR (19 : reg); cbn [edenot ev ENVb ENV]; rewrite P84; reflexivity)) as HRS.
change (sr_upd srLH (ridx 19) (ELit 0)) with srS in HRS. clear HR. rename HRS into HR.
run_blockT_keep (SCR [false] [] []) 102%nat.
{ apply (dec_sc vals M 1 false P81); [lia | reflexivity]. }
cbn [mem_denot] in EQM. subst M0.
destruct HBLK as [HBR REST].
pose proof (hz_of_block_range L sp0 DL _ _ HBR) as HZ. pose proof HZ as (Q1 & Q2 & Q4).
destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)]; subst LB.
-
pose proof (hio_free_null L scfg HI HIok) as FN. unfold free_null_spec in FN.
rewrite (dl_segs L sp0 DL), (dl_free L sp0 DL) in FN.
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
apply (FN fx' Rc M (model2 VM) (E j));
[ reflexivity | reflexivity
| regv HR (10 : reg); cbn [edenot ev ENVb ENV]; rewrite P83, HOWN; reflexivity
| regv HR (1 : reg); apply ret_ok_even; reflexivity
| unfold E; apply t_emit_has_nil
| ];
intros R' HPres; rewrite (reg_val _ _ _ (1 : reg) HR); change (edenot (ENVb vals) (sr_get srS_ft 1)) with (Z_to_bv 64 0x341e4)
end.
pose proof (regs_after_keeps vals _ srS_ft _ R' c_kept ltac:(rewrite HL; vm_compute; reflexivity) HR
(regs_preserved_kept sp0 Hsp' _ R' HPres) c_kept_no0) as HR'.
rewrite HL in HR'. change (sr_after_call_j srS_ft (map ridx c_kept) 102) with srX0 in HR'.
pose proof (env_app_know RSEGS vals (junk_vals R') _ M knLH2 ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK'.
apply (tail_X fx' j ax (vals ++ junk_vals R') R' M VM A1 cr);
try (rewrite vals_ev_app_l by (rewrite HL; lia); assumption).
+ rewrite length_app, junk_vals_length, HL. reflexivity.
+ lia.
+ exact HR'.
+ eapply ksubl_sound; [exact HK' | vm_compute; reflexivity].
+ exact HBR.
+ exact HBUF.
+ exact HH.
+ exact HAX.
-
subst PTR.
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
eapply (free_site scfg L HI HIok sp0 Hsp' Hal' DL vals _ srS_ft knLH2 Rc M (model2 VM) [(OWN, PL); (A1, CAP)] cr OWN PL (-208)
[(48%nat, 65536%Z)] [] 0x341e4 (E j));
[ exact HR | exact HK
| rewrite HL; vm_compute; reflexivity | rewrite HL; vm_compute; reflexivity | rewrite HL; lia
| exact P0 | exact HIV | vm_compute; reflexivity
| regv HR (2 : reg); cbn [edenot ev ENVb ENV]; rewrite P0; apply alu_add_w_lit
| lia | reflexivity
| left; reflexivity
| regv HR (10 : reg); cbn [edenot ev ENVb ENV]; exact P83
| regv HR (4 : reg); reflexivity
| regv HR (1 : reg); reflexivity
| lia | reflexivity
| exact HH | reflexivity | reflexivity | reflexivity
| intros i nb Hf; cbn in Hf;
destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL; lia|];
rewrite P48, u_small by lia; exists CAP; split; [lia|]; split; [| exact HBR];
cbn [lb_remove fst]; rewrite Z.eqb_refl; left; reflexivity
| discriminate]
| intros v b Hf; discriminate
| unfold E; apply t_emit_has_nil | ]
end.
clear HR HK.
intros R' M' model' vals' E' HL' HR HK HH' HBUT HAB HBLK' HIMG. subst vals' E'.
rewrite (m2_but' _ _ HBUT).
cbn [lb_remove fst] in HH'. rewrite Z.eqb_refl in HH'.
rewrite HL in HR. try rewrite HL in HK. change (sr_after_call_j srS_ft (map ridx c_kept) 102) with srX0 in HR.
change (keep_alloc (-208) [(48%nat, 65536%Z)] [] knLH2) with knX0 in HK.
apply (tail_X fx' j ax (vals ++ junk_vals R') R' M' (m_vmmaps model') A1 cr);
try (rewrite vals_ev_app_l by (rewrite HL; lia); assumption).
+ rewrite length_app, junk_vals_length, HL. reflexivity.
+ lia.
+ exact HR.
+ exact HK.
+ exact HBR.
+ rewrite <- HBUF. apply rdn_agree. intros q Hq. rewrite length_zero_lines in Hq. rewrite u_small by lia. apply HIMG; lia.
+ exact HH'.
+ apply (atexit_cells_frame M M' ax); [intros q Hq; apply HIMG; lia | exact HAX].
Qed.
End SE.
Definition relay2 (vals : list word) (R : bvmap 5 word) (W : word) : list word :=
firstn 81 vals ++ (getr R 21 :: tl (lay_ext vals R W)).
Definition shared_pos2 : list nat := [2; 3; 4; 8; 20; 22; 23; 24; 25; 26; 27]%nat.
Definition relay2_ok_b (sr : list expr) : bool :=
forallb (fun i => expr_eqb (nth i sr (ELit 0)) (nth i srLH (ELit 0)) && expr_vars_lt 81 (nth i sr (ELit 0))) shared_pos2.
#[using="sp0 path fdata Hplen LEN CFG PL B2 CALLS"] Lemma relay2_len : ltac2:(TCodec.tc2 tcn__Ju0DrvE "K'9'TByR0%211%411&Q:y5%2214'HuRA&8r3%2291%5241'C':&R6r4r2%33281%:2A1uS6%83721p0:1pW@E1pRNB1pY@F1").
Proof. intros. unfold relay2. rewrite len_lay by lia. reflexivity. Qed.
#[using="sp0 path fdata Hplen LEN CFG PL B2 CALLS"] Lemma relay2_lo : ltac2:(TCodec.tc2 tcn__Ju0DrvE "Q2'9'TByR0%211%411&Q:y5%2214':'HuRA&8r4%22:1%5241&Ir2%2217'C&S;&R6r6r5%3321;r3%6221%7252%93H21p0;1p0?1pX<F1pW@L1pRNI1pY@M1").
Proof. intros. unfold relay2. apply vals_lo; lia. Qed.
#[using="sp0 path fdata Hplen LEN CFG PL B2 CALLS"] Lemma relay2_hi : ltac2:(TCodec.tc2 tcn__Ju0DrvE "Q@'9'TByR0%211%411&Q:y5%2214':'HuRA&8r4%22:1%5241'C&S;&R6r5r3%33281&Fr2%22=1%8241&J(7&RC(T@+E(A%33I21%52D1&S>&QG%13AG@%32Q11%;3Q251&TAz%22Q61%@4Q6C41%K3Q7B1p0M1pX:Q41pW@Q:1pRNQ71pY@Q;1").
Proof. intros. unfold relay2. apply vals_hi. lia. Qed.
#[using="sp0 Hplen LEN CFG PL B2 CALLS"] Lemma relay2_agree : ltac2:(TCodec.tc2 tcn__Ju0DrvE "Q@'9'TByR0%211%411&Q:y5%2214'HuRA&8r3%2291%5241&S:(RN&S;r4%211&RJ&5y8%E11%G11&R<vSIvT;vT3vT<%544321(7vT0(<%11:%43;31%?3<61%A11%F2C1vL&R6r2%23HN1%411%M3Q261p0O1pW@Q:1pRNQ71pY@Q;1").
Proof.
intros vals R W HL. split; [|reflexivity]. intros n Hn. cbn [ev ENVb ENV]. symmetry. apply relay2_lo; lia.
Qed.
#[using="RE L sp0 envv tid mem0 VM0 fs0 stdin0 Hvsp Hplen CAP Hsp LEN above model2 CFG PL B2 CALLS lh_vals blk_facts"] Lemma relay2_regs : ltac2:(TCodec.tc2 tcn__Ju0DrvE "QN'9'TByR0%211%411'S3%611&Q:y5%2216'HuRA&8r4%22;1%5241'C'6&R7%116(@%53421&S8(RN&S;r6%211&RJ&5y8%M11%O11&R<vSIvT;vT3vT<%544321(7vT0(<%11:%43;31%?3<61%A11%F2C1r5%I321Q2vL&R6r7%2315Q6%411&QL%Q03218p081p0Q31p0Q:1pW@QG1pRNQB1pY0QF1pY@QI1").
Proof.
intros vals sr R W HL Hokb HR.
unfold relay2_ok_b in Hokb. rewrite forallb_forall in Hokb.
assert (SH : forall i, In i shared_pos2 -> getr R (Z_to_bv 5 (Z.of_nat i)) = edenot (ENVb (relay2 vals R W)) (nth i srLH (ELit 0))).
{ intros i Hi. pose proof (Hokb i Hi) as H. apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1.
rewrite <- H1. rewrite <- (edenot_agree 81 _ _ _ (relay2_agree vals R W HL) H2).
assert (Hi32 : (0 < i < 32)%nat) by (unfold shared_pos2 in Hi; cbn in Hi; lia).
rewrite (HR (Z_to_bv 5 (Z.of_nat i))), sr_get_nat by exact Hi32. reflexivity. }
apply regs_ok_by_nth. intros i Hi.
assert (JK : forall r k, nth r srLH (ELit 0) = EVar (81 + k) ->
nth k (getr R 21 :: tl (lay_ext vals R W)) (Z_to_bv 64 0) = getr R (Z_to_bv 5 (Z.of_nat r)) ->
getr R (Z_to_bv 5 (Z.of_nat r)) = edenot (ENVb (relay2 vals R W)) (nth r srLH (ELit 0))).
{ intros r k Hr Hk2. rewrite Hr. cbn [edenot ev ENVb ENV]. rewrite relay2_hi by lia. symmetry. exact Hk2. }
do 32 (destruct i as [|i]; [first [lia | apply SH; cbn; tauto | eapply JK; reflexivity] |]). lia.
Qed.
Section SE.
Local Abbreviation SEC_T_step_S := (ltac2:(TCodec.tc2 tcn__Ju0DrvE "F'K':&RG&SA+2r3%3221&R1&SEr4+1%3221r2%63281&R3r5%2317;p041p0<1pQNA1pX<C1pX>E1")) (only parsing).
Variable k : ltac:(sec_ty2 constr:(SEC_T_step_S) 0%nat 0%nat).
Variable j : ltac:(sec_ty2 constr:(SEC_T_step_S) 1%nat 0%nat).
Variable K : ltac:(sec_ty2 constr:(SEC_T_step_S) 2%nat 0%nat).
Lemma step_S : ltac:(sec_stmt2 constr:(SEC_T_step_S) 3%nat 0%nat).
Proof using VM0 Hvsp Hplen Hsp LEN CFG B2 CALLS k j K.
intros Hk2 HLH.
unfold SSP.
intros fx' vals R M VM A1 PTR OWN LB cr g (HL & P0 & P1 & P2 & P3 & P4 & P5 & P48 & P70 & P73 & P79 & P81 & P82 & P83)
P84 P101 Hjk Hk HR HK HA HBLK HC HPAY HBUF HH Hcr Hls.
pose proof (regs_ok_upd_same (ENVb vals) srLH R (19%bv : reg) (ELit 0) HR ltac:(discriminate)
ltac:(symmetry; regv HR (19 : reg); cbn [edenot ev ENVb ENV]; rewrite P84; reflexivity)) as HRS.
change (sr_upd srLH (ridx 19) (ELit 0)) with srS in HRS. clear HR. rename HRS into HR.
run_blockT_keep (SCR [true] [] []) 102%nat.
{ apply (dec_sc vals M k true P81); [lia | apply Bool.negb_true_iff; apply Z.eqb_neq; lia]. }
cbn [mem_denot] in EQM. subst M0.
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ => rename Rc into RS end.
assert (V81 : getr RS 21 = Z_to_bv 64 (k - 1)).
{ regv HR (21 : reg). change (sr_get srS_tk 21) with dec_x. apply (dec_val vals k P81). lia. }
set (valsL := relay2 vals RS (Z_to_bv 64 (WP j))).
apply (HLH fx' valsL RS M VM A1 PTR OWN LB cr g).
- unfold lh_vals, Ju0DrvD.lh_vals. subst valsL. rewrite (relay2_len vals RS _ ltac:(lia)).
rewrite !(relay2_lo vals RS _) by lia.
repeat split; try assumption.
+ change 81%nat with (81 + 0)%nat. rewrite relay2_hi by lia. exact V81.
+ change 82%nat with (81 + 1)%nat. rewrite relay2_hi by lia. cbn [nth tl lay_ext]. regv HR (9 : reg). cbn [edenot ev ENVb ENV]. exact P82.
+ change 83%nat with (81 + 2)%nat. rewrite relay2_hi by lia. cbn [nth tl lay_ext]. regv HR (18 : reg). cbn [edenot ev ENVb ENV]. exact P83.
- subst valsL. change 101%nat with (81 + 20)%nat. rewrite relay2_hi by lia. reflexivity.
- lia.
- lia.
- subst valsL. eapply (relay2_regs vals srS_tk RS _ ltac:(lia)); [vm_compute; reflexivity | exact HR].
-
subst valsL. unfold knLH2 in HK |- *.
pose proof (Forall_inv HK) as K1. pose proof (Forall_inv (Forall_inv_tail HK)) as K2.
pose proof (Forall_inv_tail (Forall_inv_tail HK)) as K3.
constructor; [|constructor].
+ cbn [kentry_ok] in K1 |- *. destruct K1 as (K1a & K1b & K1c). split; [exact K1a|]. split; [exact K1b|].
rewrite SymDriveX.adenot_lit0 in K1c |- *. cbn [edenot ev ENVb ENV] in K1c |- *.
change 101%nat with (81 + 20)%nat. rewrite relay2_hi by lia. cbn [nth tl lay_ext]. rewrite P101 in K1c. exact K1c.
+ cbn [kentry_ok edenot ev ENVb ENV] in K2 |- *. change 101%nat with (81 + 20)%nat. rewrite relay2_hi by lia. cbn [nth tl lay_ext].
rewrite P101 in K2. exact K2.
+ eapply (know_ok_agree RSEGS 81); [apply relay2_agree; lia | vm_compute; reflexivity | exact K3].
- exact HA.
- exact HBLK.
- exact HC.
- exact HPAY.
- exact HBUF.
- exact HH.
- exact Hcr.
- exact Hls.
Qed.
End SE.
Definition pf_rs (w : Z) : list (word * Z) :=
[(Z_to_bv 64 (bv_unsigned sp0 - 208 - 1056), 1056%Z); (Z_to_bv 64 0xb7120, 4%Z); (Z_to_bv 64 0xb7148, 8%Z); (Z_to_bv 64 w, 2%Z)].
Definition CPpf (w : Z) (a : Z) : Prop :=
(~ (bv_unsigned sp0 - 208 - 1056 <= a < bv_unsigned sp0 - 208) /\ ~ (0xb7120 <= a < 0xb7124) /\ ~ (0xb7148 <= a < 0xb7150) /\ ~ (w <= a < w + 2))%Z.
Definition SCpf (a : Z) : Prop := (bv_unsigned sp0 - 208 - 1056 <= a < bv_unsigned sp0 - 208)%Z.
#[using="path fdata Hvsp Hplen Hsp LEN CFG PL B2 CALLS"] Lemma CPpf_outside : ltac2:(TCodec.tc2 tcn__Ju0DrvE "Q3'K'B&SAzr1%3221&SB&SD+2+R0%3221%5271%;271+mUU0r3%=221+mVTN%?231%A231&QOr4%2217&QA&TAyR0%2215&R5r5%211%7241p091p0=1p0D1pWBQ11pYBQ21").
Proof.
intros w a Ha Hw (C1 & C2 & C3 & C4). pose proof Hsp as Hsp'.
cbn [outside pf_rs]. unfold in_rng. rewrite !u_small by lia. repeat split; lia.
Qed.
#[using="Hvsp Hplen Hsp LEN CFG PL B2 CALLS"] Lemma regions_pf : ltac2:(TCodec.tc2 tcn__Ju0DrvE "RH'9'TByR0%211%411'K'C&S;r3(2%3221vT>%63921r4uQ@%8221&TAr2%22@1%=3@41&R9+RPP0%23;>1'B&SA+mUU0r5%3221+mVTN%5231%7231':&S=r1(7u3u4(<%117%53831%63951%93:81&TC%12Q9Q0r9%Q621L%42Q<1%G241&S?&SD+2+D%3221%5271+R0%6251%Q0231%Q22:1p0A1pX:L1'Q?&S<-V@+QQ0'?%12Q2QL(>%14Q4QNQEQ>%O13%Q33421&QH&R:vLr8%211&QOr7%211&R2%C<BR6A@:;Q798521p0E1p0QC1p0QL1p0R01p0R81p2R@1pYBRA1pY@RC1").
Proof.
intros vals w A1 P0 P48 (HA1 & HA2 & HA3) Hw Hhi. pose proof Hsp as Hsp'.
constructor; cbn [ev ENVb ENV]; rewrite ?P0.
- lia.
- lia.
- intros z Hz Hnot. unfold CPpf. lia.
- intros z Hz. right. unfold SCpf. lia.
- intros i nb Hf. cbn in Hf. destruct (Nat.eqb i 48) eqn:Ei; [|discriminate]. apply Nat.eqb_eq in Ei. subst i. injection Hf as <-.
rewrite P48, u_small by lia. split; [lia|]. intros z Hz. unfold CPpf. lia.
- intros v b Hf. discriminate.
- intros i Hi. destruct (Hhi i Hi) as [H1 H2]. split; [exact H1|]. split; [exact H2|]. intros z Hz. unfold CPpf. lia.
- intros lo hi Hin. unfold IMG_PF in Hin.
destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; unfold CPpf; lia.
- intros lo hi Hin. unfold IMG_RW in Hin.
destruct Hin as [E1|[E1|[]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros Mx d m Hd Hm.
+ eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xb0000) _ 24576%nat m 0xb0000 0xb6000);
[reflexivity | reflexivity | lia | apply wseg_ac5b0 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
+ eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xb6000) _ 212992%nat m 0xb6000 0xea000);
[reflexivity | reflexivity | lia | apply wseg_5f000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
Qed.
#[using="Hvsp Hplen Hsp LEN CFG PL B2 CALLS"] Lemma know_pf : ltac2:(TCodec.tc2 tcn__Ju0DrvE "S9'9'TByR0%211%411'=y8%611%311p061'S4%;11'K'C&S;r6(2%3221vT>%63@21r7uQ@%8221&TAr2%22G1%=3G41&R9r3+RPP0%33<21'B&SA+mUU0r5%3221+mVTN%5231%7231':&S=r1(7u3u4(<%117%53831%63951%93:81&TC%12QAQ1r<%Q721M%42QD1%G241&S?&SD+2+D%3221%5271+R0%6251%Q0231%Q22:1p0A1pX:L1&S6&S<vLr;%211r:r8%746321'6&R8r9%211(@%R43521&Q@&R5%116%33Q1>1r>%A11&QJ%11B%F4E3Q61p061p0;1p0B1p0K1p0QI1p0R21p0R71p0R?1p2RG1pYBRH1pX@RJ1pRJRM1pRHRN1pY@S41").
Proof.
intros vals M M' kn w A1 P0 P48 HZ Hw Hhi HK Hwin [HFe HFg]. pose proof Hsp as Hsp'.
unfold keep_pf.
eapply (know_keep_sound RSEGS 0 (-208) 1056 [(48%nat, 65536%Z)] [] [3%nat; 4%nat] IMG_PF IMG_RW (ENVb vals) (CPpf w) SCpf).
- eapply regions_pf; eassumption.
- intros a Ha HC. apply HFe. apply CPpf_outside; assumption.
- intros a Ha. apply HFg. destruct (has_window_nth kn Hwin) as [i Hn].
pose proof (kwr_store_ok RSEGS (ENVb vals) M kn i (EVar 0) (-8388608) 8388608 (a - bv_unsigned sp0) 1%nat HK Hn
ltac:(unfold SCpf in Ha; lia) ltac:(unfold SCpf in Ha; cbn; lia)) as W.
unfold adenot in W. cbn [a_base a_off edenot ev ENVb ENV] in W. rewrite P0 in W. unfold v_addi in W.
replace (bv_unsigned sp0 + (a - bv_unsigned sp0))%Z with a in W by lia.
apply (window_defined M a); [unfold SCpf in Ha; lia | unfold SCpf in Ha; lia | exact W].
- exact HK.
Qed.
#[using="scfg L HIok path fdata Hvsp Hplen DL Hsp LEN CFG PL B2 CALLS"] Lemma heap_pf : ltac2:(TCodec.tc2 tcn__Ju0DrvE "Q>'9'?'K%2211%411&QC'TByR0%211'=y8%511%311p051'Q6&QDvMr6r5r4r2%6554321&Q@&R5%114%33761'B&SA+mUU0r3%3221+mVTN%5231%7231r9r8%E5D21CBp041p0=1p0B1pYBQ61pW>K1pRJM1pRHN1pWLQ71pR2Q91").
Proof.
intros LB cr M M' VM w HH [HFe HFg] Hw. pose proof Hsp as Hsp'.
pose proof (dl_ro L sp0 DL) as RO. pose proof (dl_static L sp0 DL) as STA.
pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
apply (hio_frame L scfg HI HIok LB cr M M' VM HH).
- intros a Ha Hpriv. apply HFe. apply CPpf_outside; [exact Ha | exact Hw |]. unfold CPpf.
destruct Hpriv as [[A [_ B]]|A].
+ rewrite (dl_sptop L sp0 DL) in A. rewrite IL, IH in B.
assert (~ (0xb6000 <= a < 0xea000) \/ hl_alloc_static L a)%Z as [C|C] by (destruct (Z_lt_ge_dec a 0xb6000); [left; lia|]; destruct (Z_lt_ge_dec a 0xea000); [|left; lia]; right; apply Classical_Prop.NNPP; intros Hn; apply B; split; [lia| exact Hn]).
* lia.
* apply STA in C. lia.
+ apply RO in A. lia.
- exact HFg.
Qed.
#[using="scfg L HI path fdata Hvsp Hplen DL Lay DLL LIok Hsp LEN CFG PL B2 CALLS"] Lemma ls_pf : ltac2:(TCodec.tc2 tcn__Ju0DrvE "Q6&RAvQ1%211'TByR0%211'=y8%511%311p051'K&R@r4r3%33>21&Q@&R5r2%211%43761'B&SA+mUU0%221:+mVTN%42<1%6231r7r5%B3M21p041p0<1p0B1pYBG1pRJI1pRHJ1pX6Q31").
Proof.
intros g M M' w Hls [HFe HFg] Hw. pose proof Hsp as Hsp'.
apply (lio_frame Lay scfg HI LSt LIok g M M' Hls).
- intros a Ha Hf. apply HFe. apply CPpf_outside; [exact Ha | exact Hw |].
destruct Hf as (iv & Hin & Hr). apply (dll_foot Lay L DLL) in Hin. unfold CPpf. lia.
- intros a Ha Hn. rewrite <- (Z_to_bv_bv_unsigned 64 a). rewrite HFe; [rewrite Z_to_bv_bv_unsigned; exact Hn|].
pose proof (dll_rw_lo Lay L DLL). pose proof (u64_range a).
apply CPpf_outside; [lia | exact Hw |]. unfold CPpf. lia.
- intros a Ha Hi. apply HFe. apply CPpf_outside; [exact Ha | exact Hw |].
destruct Hi as [(iv & Hin & Hr) | Hi].
+ apply (dll_initc Lay L DLL) in Hin. unfold CPpf. lia.
+ rewrite (dll_heap Lay L DLL), (dl_sptop L sp0 DL) in Hi. unfold CPpf. lia.
Qed.
#[using="path fdata Hvsp Hplen Hsp LEN CFG PL B2 CALLS"] Lemma above_pf : ltac2:(TCodec.tc2 tcn__Ju0DrvE "Q1'TByR0%211'=y8%511%311p051'KvSJr3%211&Q@r4&R5r2%211%53471'B&SA+mUU0%221;+mVTN%42=1%6231r5%A11p031p0;1p0B1pYBF1pRJH1pRHI1").
Proof.
intros M M' w HA [HFe HFg] Hw a Ha. pose proof Hsp as Hsp'. pose proof (u64_range a).
rewrite <- (Z_to_bv_bv_unsigned 64 a). rewrite HFe; [rewrite Z_to_bv_bv_unsigned; apply HA; exact Ha|].
apply CPpf_outside; [lia | exact Hw |]. unfold CPpf. lia.
Qed.
#[using="path fdata Hvsp Hplen Hsp LEN CFG PL B2 CALLS"] Lemma rdn_pf : ltac2:(TCodec.tc2 tcn__Ju0DrvE "RA'TByR0%211'=y8%511%311p051'K':'9%116&Q@r6r5&R5r4%211%63541'B&SA+mUU0%2218+mVTN%42:1%6231r1%72>1&SB&S?&SC%11A%32C1%5271%?271&QOr8r2%3221p051pX:Q01z%F21M&SD+2+R0%3221%C2Q21%M261r7%D1Q5%F221%Q0216'C%QC1Q;&RE&S<r;&TA%12QJG%54431;(4%12QCQA%:3931r9%72R01%;4:91N%62QHB%?3>21p061p0B1p0G1p0Q01p0Q@1p0QH1pWNR01pXFR31pWBR51pYBR61pRJR81pRHR91").
Proof.
intros M M' w a n data HF Hw HC Ha Han HR. rewrite <- HR. apply (frame_mod_rdn RSEGS M M' (pf_rs w) n); [exact HF | | rewrite u_small by lia; lia].
intros i Hi. rewrite u_small by lia. apply CPpf_outside; [lia | exact Hw | apply HC; lia].
Qed.
#[using="scfg L HIok Hvsp Hplen DL Lay DLL LIok Hsp LEN CFG PL B2 CALLS"] Lemma cb_pw : ltac2:(TCodec.tc2 tcn__Ju0DrvE "TI'9'TByR0%211%411'=y8%611%311p061'S3'?'K%2211%>11&QC'Q6&RAvQ1%211'C&S;r7(2%3221vT>%63G21&S7vLr8%211(7'S5(S1(RO(RMz%211+hld4%5221u1r6%93321(<%11<%>3=31%C3@H1'B&SAr1%22>1&SB&SD+2+R0%3221%5271%:271&Dr2%Q83Q@1F%311r4&TAr3%22QO1%411r;%113%QA3QM31p091p0>1pWBQL1&QDvMr5%352Q31Q?>%453QGQ4B2p021vSJ%11QC%21Fp021&R@%13R2DQG%23R3GJp021':%RH1RA&R9&SC%11Q0%33R3L1%RH15&RE&S<r<%Q22ROQ3%44321Q2(4%12<Q9%RA3831%Q72S4K%948QN1Q9%52@Q8%RE3<21p051p0?1pWJD1pXFF1pWBS21%QO2R;Q?'E&S?%H1QB%22QE1%R421R>+hld5%R621QH%7231%N1QJ%82Q>1%R:21R3r>%QM2SJRC%O4N21QB%K2Q6R0%S;3Q221%R12SNS:%Q34Q2S41RH%O2Q:QG%S?3Q621p051p0;1p0?1p0H1pWJQ@1pXFQB1pWBSN1%RL2M1%RM2QF1%RN2QK1%RO2R01%S02R71tRJT7S21p0SG1pX6SO1pW>T31pWLT51pR2T71pY>T<1pRHT>1pY@TD1").
Proof.
intros vals M v LB cr VM g P0. cbv zeta. pose proof Hsp as Hsp'.
pose proof (dl_ro L sp0 DL) as RO. pose proof (dl_static L sp0 DL) as STA.
pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
assert (FR : forall a : Z, (0 <= a < 2 ^ 64)%Z -> a <> 0xc7284%Z -> mem_denot (ENVb vals) M [SE (SA (ELit 0) 0xc7284) 1 v] (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha Hne. cbn [mem_denot]. rewrite SymDriveX.adenot_lit0. apply wbytes_out; rewrite length_word_to_le_bytes; rewrite ?u_small by lia; cbn; lia. }
assert (AB : forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> mem_denot (ENVb vals) M [SE (SA (ELit 0) 0xc7284) 1 v] a = M a).
{ intros a Ha. pose proof (u64_range a). rewrite <- (Z_to_bv_bv_unsigned 64 a). apply FR; lia. }
split; [exact FR|]. split; [|split; [|split; [|split]]].
- intros HH. apply (hio_frame L scfg HI HIok LB cr M _ VM HH).
+ intros a Ha Hpriv. apply FR; [lia|].
destruct Hpriv as [[A [_ B]]|A].
* rewrite (dl_sptop L sp0 DL) in A. rewrite IL, IH in B.
assert (~ (0xb6000 <= a < 0xea000) \/ hl_alloc_static L a)%Z as [C|C]
by (destruct (Z_lt_ge_dec a 0xb6000); [left; lia|]; destruct (Z_lt_ge_dec a 0xea000); [|left; lia];
right; apply Classical_Prop.NNPP; intros Hn; apply B; split; [lia| exact Hn]).
-- lia.
-- apply STA in C. lia.
* apply RO in A. lia.
+ intros x Hx. exact (mem_denot_grows (ENVb vals) M _ x Hx).
- intros HA a Ha. rewrite AB by exact Ha. apply HA. exact Ha.
- intros Hls. apply (lio_frame Lay scfg HI LSt LIok g M _ Hls).
+ intros a Ha Hf. apply FR; [lia|]. destruct Hf as (iv & Hin & Hr). apply (dll_foot Lay L DLL) in Hin. lia.
+ intros a Ha Hn. pose proof (dll_rw_lo Lay L DLL). pose proof (u64_range a).
rewrite <- (Z_to_bv_bv_unsigned 64 a), FR; [rewrite Z_to_bv_bv_unsigned; exact Hn | lia | lia].
+ intros a Ha Hi. destruct Hi as [(iv & Hin & Hr) | Hi].
* apply FR; [lia|]. apply (dll_initc Lay L DLL) in Hin. lia.
* rewrite (dll_heap Lay L DLL), (dl_sptop L sp0 DL) in Hi. apply FR; lia.
- intros a n bs (Ha1 & Ha2 & Ha3) HR. rewrite <- HR. apply rdn_agree. intros q Hq. rewrite u_small by lia. apply FR; lia.
- intros a n bs Ha0 Hout Hhi HR. rewrite <- HR. apply rdn_agree. intros q Hq. rewrite u_small by lia. apply FR; lia.
Qed.
Section SE.
Local Abbreviation SEC_T_iter2 := (ltac2:(TCodec.tc2 tcn__Ju0DrvE "N'K':'9'Q7%211!pYD21&SA+1r3%3221r2(<%11:%311&R3r5(3r4%211%5341;&R1r6%23175p041p0;1p0@1pQNE1pX<K1pX>M1")) (only parsing).
Variable k : ltac:(sec_ty2 constr:(SEC_T_iter2) 0%nat 0%nat).
Variable j : ltac:(sec_ty2 constr:(SEC_T_iter2) 1%nat 0%nat).
Variable K : ltac:(sec_ty2 constr:(SEC_T_iter2) 2%nat 0%nat).
Lemma iter2 : ltac:(sec_stmt2 constr:(SEC_T_iter2) 3%nat 0%nat).
Proof using HIok uid VM0 Hva Hve Hvsp Htid Hplen DL HCAP crC HLEN DLL LIok Hsp Hal LEN CFG B2 CALLS lh1_k relay_regs relay_agree relay_len relay_lo relay_81 relay_101 hiv_facts' Hok k j K.
intros Hk1 HK0 HSS.
unfold LH2P.
intros fx' vals R M VM A1 PTR OWN LB cr g (HL & P0 & P1 & P2 & P3 & P4 & P5 & P48 & P70 & P73 & P79 & P81 & P82 & P83)
P101 Hjk Hk HR HK HA HBLK HC HPAY HBUF HH Hcr Hls.
pose proof Hsp as Hsp'. pose proof Hal as Hal'.
pose proof (hiv_facts' vals P3 P4) as HIV.
destruct HBLK as [HBR REST].
pose proof (hz_of_block_range L sp0 DL _ _ HBR) as HZ. pose proof HZ as (Q1 & Q2 & Q4).
pose proof PL_range' as HPr. pose proof (payload_len fdata) as PLN. fold PL in PLN. fold payload in PLN.
pose proof (dll_credit_pos Lay L DLL PL ltac:(lia)) as [CP1 CP2].
run_blockT_keep scr0 102%nat.
destruct (cb_pw vals M (ELit 1) LB cr VM g P0) as (_ & CH & CA & CL & CR & CI). rewrite <- EQM in CH, CA, CL, CR, CI.
apply CH in HH. apply CA in HA. apply CL in Hls.
apply (CR A1 (length fdata) fdata ltac:(eapply (hz_sub sp0); [exact HZ | lia | lia | unfold LEN in HLEN; lia])) in HC.
assert (HPAY0 : rdn RSEGS M0 (Z_to_bv 64 PTR) (length payload) = Some payload).
{ destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
- rewrite PLN. replace (Z.to_nat PL) with 0%nat by lia. rewrite PLN in HPAY. replace (Z.to_nat PL) with 0%nat in HPAY by lia. exact HPAY.
- pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as HZ2. subst PTR.
apply (CR OWN (length payload) payload ltac:(eapply (hz_sub sp0); [exact HZ2 | lia | lia | rewrite PLN; lia]) HPAY). }
apply (CI 0xe94a0%Z (length (zero_lines j)) (zero_lines j) ltac:(lia) ltac:(lia) ltac:(rewrite length_zero_lines; lia)) in HBUF.
clear HPAY CH CA CL CR CI EQM. rename HPAY0 into HPAY. clear M. rename M0 into M.
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
eapply (lib_site scfg L HI HIok sp0 Hsp' Hal' DL Lay LSt DLL LIok vals _ srLB knLB2 Rc M (model2 VM) LB cr g (-208)
[(48%nat, 65536%Z)] [] PTR 0x341b8 payload K);
[ exact HR | exact HK
| rewrite HL; vm_compute; reflexivity | rewrite HL; vm_compute; reflexivity | rewrite HL; lia
| exact P0 | exact HIV | vm_compute; reflexivity
| regv HR (2 : reg); cbn [edenot ev ENVb ENV]; rewrite P0; apply alu_add_w_lit
| lia | reflexivity
| regv HR (1 : reg); reflexivity | lia | reflexivity
| regv HR (3 : reg); reflexivity | regv HR (4 : reg); reflexivity
| regv HR (10 : reg); cbn [edenot ev ENVb ENV]; exact P82
| regv HR (11 : reg); cbn [edenot ev ENVb ENV]; rewrite P79, PLN; f_equal; lia
| rewrite PLN; lia
| destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)];
[ left; split; [rewrite PLN; lia | exact HPTR] | right; split; [rewrite PLN; lia|]; subst LB PTR; left; rewrite PLN; f_equal; lia ]
| exact HPAY
| rewrite PLN; replace (Z.of_nat (Z.to_nat PL)) with PL by lia; exact (credit_le_head sp0 Hsp' k (ll_credit Lay PL) cr Hk1 CP1 CP2 Hcr)
| exact Hls
| exact HH | reflexivity | reflexivity | reflexivity
| intros i nb Hf; cbn in Hf;
destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL; lia|];
rewrite P48, u_small by lia; exists CAP; split; [lia|]; split; [| exact HBR];
destruct REST as [(_ & _ & _ & ->) | (_ & _ & _ & _ & ->)]; [left | right; left]; reflexivity
| discriminate]
| intros v b Hf; discriminate
| exact HK0 | ]
end.
clear HR HK.
intros fx2 R' M' model' g' cr' vals' E' HL' HR HK HH' HBUT Hls' Hcr' HAB HBLK' HIMG. subst vals' E'.
rewrite (m2_but' _ _ HBUT). rewrite (m2_but' _ _ HBUT) in HH'. cbn [m_vmmaps Ju0DrvB.model2 mkModelE with_net with_creds mkModel m_vm vmst_maps] in HH'.
set (VM2 := m_vmmaps model') in *. clearbody VM2.
rewrite HL in HR, HL'. change (keep_lib (-208) [(48%nat, 65536%Z)] [] knLB2) with knLr2 in HK.
set (vals2 := vals ++ junk_vals R') in *.
change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals2) in HR, HK.
assert (XL : forall q x, (q < 102)%nat -> vals_ev vals q = x -> vals_ev vals2 q = x).
{ intros q x Hq Hx. subst vals2. rewrite vals_ev_app_l by (rewrite HL; exact Hq). exact Hx. }
pose proof (XL 0%nat _ ltac:(lia) P0) as X0. pose proof (XL 3%nat _ ltac:(lia) P3) as X3. pose proof (XL 4%nat _ ltac:(lia) P4) as X4.
pose proof (XL 48%nat _ ltac:(lia) P48) as X48. pose proof (XL 101%nat _ ltac:(lia) P101) as X101.
pose proof (hiv_facts' vals2 X3 X4) as HIV2.
assert (HA2 : above M') by (intros a Ha; rewrite HAB by exact Ha; apply HA; exact Ha).
assert (HC2 : rdn RSEGS M' (Z_to_bv 64 A1) (length fdata) = Some fdata).
{ rewrite <- HC. apply rdn_agree. intros q Hq. rewrite u_small by lia. apply HBLK'; [lia|].
exists (A1, CAP). split; [destruct REST as [(_ & _ & _ & ->)|(_ & _ & _ & _ & ->)]; [left|right; left]; reflexivity|]. cbn [fst snd]. lia. }
assert (HPAY2 : rdn RSEGS M' (Z_to_bv 64 PTR) (length payload) = Some payload).
{ destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
- rewrite PLN. replace (Z.to_nat PL) with 0%nat by lia. rewrite PLN in HPAY. replace (Z.to_nat PL) with 0%nat in HPAY by lia. exact HPAY.
- pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as (U1 & U2 & U4).
rewrite <- HPAY. apply rdn_agree. intros q Hq. rewrite PLN in Hq. rewrite u_small by lia. apply HBLK'; [lia|].
exists (OWN, PL). subst LB PTR. split; [left; reflexivity|]. cbn [fst snd]. lia. }
assert (HBUF2 : rdn RSEGS M' (Z_to_bv 64 0xe94a0) (length (zero_lines j)) = Some (zero_lines j)).
{ rewrite <- HBUF. apply rdn_agree. intros q Hq. rewrite length_zero_lines in Hq. rewrite u_small by lia. apply HIMG; lia. }
clear HA HC HPAY HBUF HAB HBLK' HIMG Hls HH.
run_blockT_keep scr0 134%nat.
destruct (cb_pw vals2 M' (ELit 0) LB cr' VM2 g' X0) as (_ & CH & CA & CL & CR & CI). rewrite <- EQM in CH, CA, CL, CR, CI.
apply CH in HH'. apply CA in HA2. apply CL in Hls'.
apply (CR A1 (length fdata) fdata ltac:(eapply (hz_sub sp0); [exact HZ | lia | lia | unfold LEN in HLEN; lia])) in HC2.
assert (HPAY3 : rdn RSEGS M0 (Z_to_bv 64 PTR) (length payload) = Some payload).
{ destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
- rewrite PLN. replace (Z.to_nat PL) with 0%nat by lia. rewrite PLN in HPAY2. replace (Z.to_nat PL) with 0%nat in HPAY2 by lia. exact HPAY2.
- pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as HZ2. subst PTR.
apply (CR OWN (length payload) payload ltac:(eapply (hz_sub sp0); [exact HZ2 | lia | lia | rewrite PLN; lia]) HPAY2). }
apply (CI 0xe94a0%Z (length (zero_lines j)) (zero_lines j) ltac:(lia) ltac:(lia) ltac:(rewrite length_zero_lines; lia)) in HBUF2.
clear HPAY2 CH CA CL CR CI EQM. rename HPAY3 into HPAY2. clear M'. rename M0 into M'.
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ => rename Rc into RP end.
assert (PH : pfH M' (Z_to_bv 64 (bv_unsigned sp0 - 208)) (WP j) CANZ).
{ destruct (has_window_nth knLc2 ltac:(vm_compute; reflexivity)) as [iw Hnw].
constructor; rewrite ?u_small by lia.
- rewrite <- Zminus_mod_idemp_l, Hal'. reflexivity.
- lia.
- lia.
- intros a n H1 H2. rewrite u_small in H1, H2 by lia.
pose proof (kwr_store_ok RSEGS (ENVb vals2) M' knLc2 iw (EVar 0) (-8388608) 8388608 (bv_unsigned a - bv_unsigned sp0) n HK Hnw
ltac:(unfold PF_FR in H1; lia) ltac:(lia)) as W.
unfold adenot in W. cbn [a_base a_off edenot ev ENVb ENV] in W. rewrite X0 in W. unfold v_addi in W.
replace (bv_unsigned sp0 + (bv_unsigned a - bv_unsigned sp0))%Z with (bv_unsigned a) in W by lia. rewrite Z_to_bv_bv_unsigned in W. exact W.
- intros i Hi.
pose proof (know_nth RSEGS _ _ knLc2 ltac:(let q := kidx knLc2 (is_kimg_cov 0x10000 0xa0524) in exact q) _ HK eq_refl) as KI.
cbn [kentry_ok] in KI. destruct KI as (_ & _ & KI). apply KI. lia.
- krd_solve HK.
- krd_solve HK.
- krd HK 0xb7148%Z 8%nat Hw. rewrite Hw. cbn [ev ENVb ENV]. rewrite X101. reflexivity.
- unfold WP. lia.
- krd_solve HK.
- krd_solve HK.
- krd_solve HK.
- eapply can_of_know; [exact HK | vm_compute; reflexivity].
- apply CANZ_range. }
destruct (printf0_buffered RP M' (seg_rom RSEGS) (Z_to_bv 64 (bv_unsigned sp0 - 208)) (WP j) CANZ PH
ltac:(regv HR (1 : reg); reflexivity)
ltac:(regv HR (2 : reg); cbn [edenot ev ENVb ENV]; rewrite X0; apply alu_add_w_lit)
ltac:(regv HR (11 : reg); reflexivity)) as (R2 & M2 & MS & KCS & FM & Rw & Rwpos & Rflags).
rewrite u_small in FM by lia.
eapply srz_msteps; [reflexivity | reflexivity | exact MS |]. clear MS.
change (frame_mod M' M2 (pf_rs (WP j))) in FM.
assert (HwB : (0xe94a0 <= WP j <= 0xe989e)%Z) by (unfold WP; lia).
pose proof (regs_after_keeps vals2 _ srP0 RP R2 callee_saved ltac:(rewrite HL'; vm_compute; reflexivity) HR KCS ltac:(cbn; intuition discriminate)) as HR3.
rewrite HL' in HR3.
set (vals3 := vals2 ++ junk_vals R2) in *.
assert (HL3 : length vals3 = 166%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL'; reflexivity).
assert (YL : forall q x, (q < 102)%nat -> vals_ev vals q = x -> vals_ev vals3 q = x).
{ intros q x Hq Hx. subst vals3. rewrite vals_ev_app_l by (rewrite HL'; lia). apply XL; assumption. }
pose proof (know_pf vals2 M' M2 knLc2 (WP j) A1 X0 X48 ltac:(eapply (hz_sub sp0); [exact HZ | lia | lia | lia]) HwB HIV2 ltac:(exact HK) ltac:(vm_compute; reflexivity) FM) as HK3.
lazymatch type of HK3 with know_ok _ _ _ ?k => let k' := eval vm_compute in k in change k with k' in HK3 end.
lazymatch type of HK3 with know_ok _ _ _ ?k3 =>
pose proof (env_app_know RSEGS vals2 (junk_vals R2) _ M2 k3 ltac:(rewrite HL'; vm_compute; reflexivity) HK3) as HK4 end.
fold vals3 in HK4. change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals3) in HR3, HK4.
set (valsS := relay vals3 R2 (Z_to_bv 64 (WP (S j)))).
apply (HSS fx2 valsS R2 M2 VM2 A1 PTR OWN LB cr' g').
- unfold lh_vals, Ju0DrvD.lh_vals. subst valsS. rewrite (relay_len vals3 R2 _ ltac:(lia)), relay_81 by lia.
rewrite !(relay_lo vals3 R2 _) by lia.
repeat split; try (apply YL; [lia | assumption]).
+ unfold relay. change 82%nat with (81 + 1)%nat. rewrite vals_hi by lia. cbn [nth lay_ext].
rewrite (KCS (9%bv : reg)) by (cbn; tauto). regv HR (9 : reg). cbn [edenot ev ENVb ENV]. apply XL; [lia | exact P82].
+ unfold relay. change 83%nat with (81 + 2)%nat. rewrite vals_hi by lia. cbn [nth lay_ext].
rewrite (KCS (18%bv : reg)) by (cbn; tauto). regv HR (18 : reg). cbn [edenot ev ENVb ENV]. apply XL; [lia | exact P83].
- subst valsS. unfold relay. change 84%nat with (81 + 3)%nat. rewrite vals_hi by lia. cbn [nth lay_ext].
rewrite (KCS (19%bv : reg)) by (cbn; tauto). regv HR (19 : reg). reflexivity.
- subst valsS. apply relay_101. lia.
- lia.
- lia.
- subst valsS. eapply (relay_regs vals3 _ R2 _ ltac:(lia)); [| exact HR3]. vm_compute. reflexivity.
-
subst valsS. unfold knLH2.
constructor; [|constructor; [|constructor]].
+ cbn [kentry_ok]. split; [lia|]. split; [apply flat_abs0; lia|]. rewrite SymDriveX.adenot_lit0. cbn [edenot ev ENVb ENV].
rewrite relay_101 by lia. replace (WP (S j)) with (WP j + 2)%Z by (unfold WP; lia). exact Rwpos.
+ cbn [kentry_ok edenot ev ENVb ENV]. rewrite relay_101 by lia. unfold WP. rewrite u_small by lia. lia.
+ cbn [kentry_ok]. split; [lia|]. split; [apply flat_abs0; lia|]. rewrite SymDriveX.adenot_lit0. cbn [edenot]. exact Rflags.
+ eapply (know_ok_agree RSEGS 82); [apply relay_agree; lia | vm_compute; reflexivity |].
eapply ksubl_sound; [exact HK4 | vm_compute; reflexivity].
- eapply above_pf; [exact HA2 | exact FM | exact HwB].
- split; [exact HBR | exact REST].
- eapply (rdn_pf M' M2 (WP j)); [exact FM | exact HwB | intros i Hi; unfold CPpf, WP; lia | lia | lia | exact HC2].
- destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
+ assert (Hp0 : payload = []) by (apply length_zero_iff_nil; rewrite PLN; lia).
rewrite Hp0. reflexivity.
+ pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as (U1 & U2 & U4). subst PTR.
eapply (rdn_pf M' M2 (WP j)); [exact FM | exact HwB | intros i Hi; rewrite PLN in Hi; unfold CPpf, WP; lia | lia | rewrite PLN; lia | exact HPAY2].
- rewrite zero_lines_snoc, length_app. cbn [length]. apply rdn_app.
+ eapply (rdn_pf M' M2 (WP j)); [exact FM | exact HwB | intros i Hi; rewrite length_zero_lines in Hi; unfold CPpf, WP; lia | lia
| rewrite length_zero_lines; lia | exact HBUF2].
+ rewrite length_zero_lines. replace (Z_to_bv 64 0xe94a0 + nat_to_word (2 * j)) with (Z_to_bv 64 (WP j)); [exact Rw|].
apply bv_eq. rewrite w_add_nat. rewrite (u_small 0xe94a0) by lia. rewrite !u_small by (unfold WP; lia). unfold WP. lia.
- eapply heap_pf; [exact HH' | exact FM | exact HwB].
- rewrite PLN in Hcr'. replace (Z.of_nat (Z.to_nat PL)) with PL in Hcr' by lia.
exact (credit_le_step sp0 Hsp' k (ll_credit Lay PL) cr cr' Hk1 CP1 CP2 Hcr Hcr').
- eapply ls_pf; [exact Hls' | exact FM | exact HwB].
Qed.
End SE.
End DrvE.
End FPX_1.
