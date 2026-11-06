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
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
MmapSim AllocSim FileSim AgentLib SpecConsts DivergeSim SpinAlg SpinAlgX
SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame
Spec LibWritev RefNodes RefMemcpyLib RefReadLib RefPrintfLib Js0Startup Js0MainEntry Hoare MemSplit
Js0MemcpyBase Js0Memcpy Js0ExitBase Js0StdioDefs Js0Exit Js0LibStdioCall
HeapIface LibIface DrvKit Js0Drv_defs Js0DrvLib Js0DrvA Js0DrvB Js0DrvG_defs Js0DrvC_defs Js0DrvC Js0DrvD_defs Js0DrvLibL.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0DrvD () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvC_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvD.FPX_1.DrvD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvD_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0MainEntry."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A1"; "0CAP"; "0CFG"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"]; ["2I"; "2and"; "2eq"; "3le"; "3lt"; "4nth"; "5Z"; "0ENVb"; "0HI"; "0K"; "0L"; "0LEN"; "6mkCfg"; "7Model"; "7VmMaps"; "7event"]; ["7m_vmmaps"; "8bvmap"; "0M"; "0M'"; "0PL"; "0R"; "0R'"; "9block_range"; "9hi_heap"; "9model_but_vm"; ":knT0"; ":zseq"; ";CALLS"; ";callsF"; ";lh1_k"; ";payload"]; [";relay"; "<calls_x"; "<knTc"; "<knTe"; "<relay_ok_b"; "<srLH"; "=auxvp"; "=blobs0"; "=p0"; "=p1"; "=rnd"; ">FPState"; ">mkst"; ">rdn"; ">seg_rom"; "?TSet"]; ["@srealizes"; "Ablobs_ev"; "BELit"; "BEVar"; "BEnv"; "Bedenot"; "Bexpr"; "Bridx"; "Bsr_upd"; "Cknow_ok"; "Cregs_ok"; "Denv_agree"; "Dvals_ev"; "Eloaded_segments"; "FIn"; "Fforallb"]; ["Gadd"; "Geqb"; "Gle"; "Glt"; "Gmodulo"; "Gpow"; "Gto_nat"; "0VM"; "0W"; "0a0s"; "0above"; "0b"; "0bl"; "0chi"; "0clo"; "0crC"]; ["0envv"; "0fdata"; "0fx'"; "0hw"; "0i"; "0j"; "0m'"; "0model2"; "0path"; "0phi"; "0plo"; "0rdraw"; "0scfg"; "0sp0"; "0sr"; "0srX"]; ["HBV"; "HZ_to_bv"; "Hbv"; "Hbv_unsigned"; "0target_k"; "0tid"; "0vals"; "0vals1"]]).
Local Ltac tauto := L5FastTauto.ptauto0.
Open Scope bv_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac lia := first [ solve [ try (match goal with H : (length _ <= S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _)))))))))))))))))))))))))))))))))%nat |- _ => clear dependent H end); Lia.lia ] | Lia.lia ].
Tactic Notation "run_blockT" constr(scr) constr(NX) := run_block_gen FUEL STOPS_T scr NX false.
Tactic Notation "run_blockT_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_T scr NX true.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvD.
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
Let Hsp : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z := conj (proj1 Hvsp) (proj1 (proj2 Hvsp)).
Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
Let LEN : Z := Z.of_nat (length fdata).
Let ENVb (vals : list word) : env := ENV a0s path hw rdraw fdata vals.
Let above (M : word -> option byte) : Prop := above_sp0 sp0 mem0 M.
Let model2 (VM : VmMaps) : Model := model2 tid fs0 stdin0 VM.
Let CFG : Z := CFG fdata.
Let PL : Z := PL fdata.
Let B2 : Z := B2 fdata.
Let target_k := target_k scfg L HI sp0 a0s path envv hw rdraw tid mem0 fs0 stdin0 fdata CAP crC.
Hypothesis Hok : (6 + CFG <= LEN)%Z.
Hypothesis Hcr1 : (0 < PL)%Z -> credit_ok L crC PL.
Definition CALLS : Z := if (CFG =? 0)%Z then 1 else (B2 mod 4 + 1)%Z.
Definition payload : list byte := skipn (Z.to_nat (6 + CFG)) fdata.
Definition cr1 : credit := if (PL =? 0)%Z then crC else debit L crC PL.
#[using="LEN PL"] Lemma CALLS_range : ltac2:(TCodec.tc2 tcn__Js0DrvD "8'A&RB+1&Q<%3221+4%5231%7231").
Proof. clear Htid Hplen HLEN Hsp Hal Hok Hcr1. unfold CALLS. destruct (CFG =? 0)%Z; [lia|]. pose proof (Z.mod_pos_bound B2 4 ltac:(lia)). lia. Qed.
#[using="CAP HCAP HLEN LEN CFG B2 Hok"] Lemma PL_range : ltac2:(TCodec.tc2 tcn__Js0DrvD "8'A&RBzvQ4%3221+QooooI%5231%7231").
Proof. clear Htid Hplen Hsp Hal Hcr1. subst PL CFG LEN. unfold Js0DrvC.PL. pose proof (CFG_range fdata). lia. Qed.
#[using="B2"] Lemma payload_len : ltac2:(TCodec.tc2 tcn__Js0DrvD "<'B':&8'SBy8%211&Q?%5221&RFvQ4%211%;3:41").
Proof. clear Htid Hplen Hsp Hal Hcr1. unfold payload. rewrite length_skipn. subst PL LEN CFG. unfold Js0DrvC.PL. pose proof (CFG_range fdata). lia. Qed.
Definition lh_vals (vals : list word) (A1 PTR OWN k : Z) : Prop :=
length vals = 102%nat /\ vals_ev vals 0 = sp0
/\ vals_ev vals 1 = p0 sp0 a0s path envv /\ vals_ev vals 2 = p1 sp0 a0s path envv
/\ vals_ev vals 3 = auxvp sp0 a0s path envv /\ vals_ev vals 4 = rnd sp0 a0s path envv /\ vals_ev vals 5 = tid
/\ vals_ev vals 48 = Z_to_bv 64 A1 /\ vals_ev vals 70 = Z_to_bv 64 LEN
/\ vals_ev vals 73 = Z_to_bv 64 CFG /\ vals_ev vals 79 = Z_to_bv 64 PL
/\ vals_ev vals 81 = Z_to_bv 64 k /\ vals_ev vals 82 = Z_to_bv 64 PTR /\ vals_ev vals 83 = Z_to_bv 64 OWN.
Definition blk_facts (A1 PTR OWN : Z) (LB : list (Z * Z)) : Prop :=
block_range L A1 CAP /\
((PL = 0%Z /\ PTR = 0xc6240%Z /\ OWN = 0%Z /\ LB = [(A1, CAP)])
\/ ((0 < PL)%Z /\ PTR = OWN /\ block_range L OWN PL /\ blocks_apart OWN PL [(A1, CAP)] /\ LB = [(OWN, PL); (A1, CAP)])).
Definition lh1_k (K : TSet) : Prop :=
forall (fx' : PropExec.FPState) vals R M VM (A1 PTR OWN : Z) LB,
lh_vals vals A1 PTR OWN CALLS ->
regs_ok (ENVb vals) srLH R -> know_ok RSEGS (ENVb vals) M knLH1 ->
above M -> blk_facts A1 PTR OWN LB ->
rdn RSEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
rdn RSEGS M (Z_to_bv 64 PTR) (length payload) = Some payload ->
hi_heap HI LB cr1 M VM ->
srealizes RSEGS scfg (mkCfg (@mkst fx' R (Z_to_bv 64 0x33f34) M (seg_rom RSEGS)) (model2 VM)) K.
#[using="uid hw rdraw Hva Hve Hvsp Hplen"] Lemma hiv_facts' : ltac2:(TCodec.tc2 tcn__Js0DrvD "QF'9'SByR0%211%411'B&R<r1u3%3221&QFvS=vRIvS8vS0%544321%;3=71r2u4%=221&QJ%14:987%A3C31':&R>(7(;%114%335:1%436E1%637G1'A&RB&SC%12Q0Gr5%N21C%42Q31%6241&R@&RE+2+D%3221%5271+R0%6251%?231%A2:1p0C1pV:K1p0M1p0Q41pW>QA1").
Proof. intros vals P3 P4 i Hi. exact (hiv_facts sp0 a0s path envv uid hw rdraw Hva Hve Hvsp Hplen vals P3 P4 i Hi). Qed.
#[using="Type"] Lemma m2_but : ltac2:(TCodec.tc2 tcn__Js0DrvD "@'N'M&Q9vS7r2%211r1%5221'B&Q0%116%811%43;81p061pV>=1pU@?1").
Proof. intros VM m' H. exact H. Qed.
#[using="Type"] Lemma m2_vm : ltac2:(TCodec.tc2 tcn__Js0DrvD "9'N'B&Q0vS7r1%211%411%63713pU@81").
Proof. intros. reflexivity. Qed.
Definition callsF (v80 : word) : word :=
edenot (Env (fun n => match n with 80%nat => v80 | _ => Z_to_bv 64 0 end) (blobs_ev [])) calls_x.
#[using="Type"] Lemma calls_x_callsF : ltac2:(TCodec.tc2 tcn__Js0DrvD "L'9'SByR0%211%411y8%511%711%811'B&R5(R4&R<r2%211&R1r1%211%7241&QA%:221&Q=uR@%;2:1%311%@3F51pUJB1pW>G1").
Proof. intros. reflexivity. Qed.
#[using="Type"] Lemma callsF_tab : ltac2:(TCodec.tc2 tcn__Js0DrvD "K'B'6&R?'F&RA&SCyR0&Q=&SAr1%2241%411%7261&R@&RD+4%2271+1%5221%?271qUHA1&Q;uX0%211%F3E41(?%J3I21").
Proof. vm_compute. reflexivity. Qed.
#[using="sp0 path fdata Hplen LEN CFG PL B2"] Lemma callsF_val : ltac2:(TCodec.tc2 tcn__Js0DrvD "M'F'A&RBzr1%3221&RC+X0%2241%8241'B'SByR0%211&Q=&SAr2%2251%411&R@&RD+4%2261+1%5221%:2=1%@3=81p0B1pUHL1").
Proof.
intros b Hb. pose proof callsF_tab as T. rewrite forallb_forall in T.
specialize (T b (proj2 (in_zseq 256 b) ltac:(cbn; lia))). apply Z.eqb_eq in T.
apply bv_eq. rewrite T. symmetry. apply u_small. pose proof (Z.mod_pos_bound b 4 ltac:(lia)). lia.
Qed.
Definition lay_ext (vals : list word) (R : bvmap 5 word) (W : word) : list word :=
[vals_ev vals 81; getr R 9; getr R 18; getr R 19; getr R 1; getr R 5; getr R 6; getr R 7;
getr R 10; getr R 11; getr R 12; getr R 13; getr R 14; getr R 15; getr R 16; getr R 17;
getr R 28; getr R 29; getr R 30; getr R 31; W].
Definition relay (vals : list word) (R : bvmap 5 word) (W : word) : list word := firstn 81 vals ++ lay_ext vals R W.
#[using="sp0 path fdata Hplen LEN CFG PL B2"] Lemma relay_len : ltac2:(TCodec.tc2 tcn__Js0DrvD "K'9'SByR0%211%411&Q1y5%2214'CuRA&8r3%2291%5241'B':&Q@r4r2%33281%:2A1uS6%83721p0:1pUBE1pR<B1pW>F1").
Proof. intros. unfold relay. rewrite len_lay by lia. reflexivity. Qed.
#[using="sp0 path fdata Hplen LEN CFG PL B2"] Lemma relay_lo : ltac2:(TCodec.tc2 tcn__Js0DrvD "Q2'9'SByR0%211%411&Q1y5%2214':'CuRA&8r4%22:1%5241&Dr2%2217'B&R<&Q@r6r5%3321;r3%6221%7252%93H21p0;1p0?1pV<F1pUBL1pR<I1pW>M1").
Proof. intros. unfold relay. apply vals_lo; lia. Qed.
#[using="sp0 path fdata Hplen LEN CFG PL B2"] Lemma relay_81 : ltac2:(TCodec.tc2 tcn__Js0DrvD "K'9'SByR0%211%411&Q1y5%2214'CuRA&8r3%2291%5241'B&R<&Q@r4r2%33281%521;%624<%83C21p0:1pUBE1pR<B1pW>F1").
Proof.
intros vals R W H. unfold relay.
change (vals_ev (firstn 81 vals ++ lay_ext vals R W) 81) with (vals_ev (firstn 81 vals ++ lay_ext vals R W) (81 + 0)).
rewrite vals_hi by lia. reflexivity.
Qed.
#[using="sp0 path fdata Hplen LEN CFG PL B2"] Lemma relay_101 : ltac2:(TCodec.tc2 tcn__Js0DrvD "K'9'SByR0%211%411&Q1y5%2214'CuRA&8r3%2291%5241'B&R<&Q@r4r2%33281uS5%6221%83C14p0:1pUBE1pR<B1pW>F1").
Proof.
intros vals R W H. unfold relay.
change (vals_ev (firstn 81 vals ++ lay_ext vals R W) 101) with (vals_ev (firstn 81 vals ++ lay_ext vals R W) (81 + 20)).
rewrite vals_hi by lia. reflexivity.
Qed.
#[using="sp0 Hplen LEN CFG PL B2"] Lemma relay_agree : ltac2:(TCodec.tc2 tcn__Js0DrvD "Q@'9'SByR0%211%411&Q1y5%2214'CuRB&8r3%2291%5241&R;(R4&R<r4%211&R1&5y8%E11%G11&QGvRIvS8vS3vS;%544321(7vS1(;%11:%43;31%?3<61%A11%F2C1vG&Q@r2%23HN1%411%M3Q261p0O1pUBQ:1pR<Q71pW>Q;1").
Proof.
intros vals R W HL. split; [|reflexivity]. intros n Hn. cbn [ev ENVb ENV].
destruct (Nat.eq_dec n 81) as [->|Hne]; [symmetry; apply relay_81; lia | symmetry; apply relay_lo; lia].
Qed.
Definition junk_pos : list (nat * nat) :=
[(1,4); (5,5); (6,6); (7,7); (9,1); (10,8); (11,9); (12,10); (13,11); (14,12); (15,13); (16,14); (17,15);
(18,2); (19,3); (28,16); (29,17); (30,18); (31,19)]%nat.
#[using="RE sp0 tid mem0 VM0 fs0 stdin0 Hvsp Htid Hplen CAP HCAP Hsp LEN above model2 CFG PL B2"] Lemma relay_regs : ltac2:(TCodec.tc2 tcn__Js0DrvD "QN'9'SByR0%211%411'R6%611&Q1y5%2216'CuRB&8r4%22;1%5241'B'6&QD%116(?%53421&R:(R4&R<r6%211&R1&5y8%M11%O11&QGvRIvS8vS3vS;%544321(7vS1(;%11:%43;31%?3<61%A11%F2C1r5%I321Q2vG&Q@r7%2315Q6%411&QE%Q03218p081p0Q31p0Q:1pUBQG1pR<QB1pVNQF1pW>QI1").
Proof.
intros vals sr R W HL Hokb HR.
unfold relay_ok_b in Hokb. rewrite forallb_forall in Hokb.
assert (SH : forall i, In i shared_pos -> getr R (Z_to_bv 5 (Z.of_nat i)) = edenot (ENVb (relay vals R W)) (nth i srLH (ELit 0))).
{ intros i Hi. pose proof (Hokb i Hi) as H. apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1.
rewrite <- H1. rewrite <- (edenot_agree 82 _ _ _ (relay_agree vals R W HL) H2).
assert (Hi32 : (0 < i < 32)%nat) by (unfold shared_pos in Hi; cbn in Hi; lia).
rewrite (HR (Z_to_bv 5 (Z.of_nat i))), sr_get_nat by exact Hi32. reflexivity. }
apply regs_ok_by_nth. intros i Hi.
assert (JK : forall r k, nth r srLH (ELit 0) = EVar (81 + k) -> nth k (lay_ext vals R W) (Z_to_bv 64 0) = getr R (Z_to_bv 5 (Z.of_nat r)) ->
getr R (Z_to_bv 5 (Z.of_nat r)) = edenot (ENVb (relay vals R W)) (nth r srLH (ELit 0))).
{ intros r k Hr Hk. rewrite Hr. cbn [edenot ev ENVb ENV]. unfold relay. rewrite vals_hi by lia. symmetry. exact Hk. }
do 32 (destruct i as [|i]; [first [lia | apply SH; cbn; tauto | eapply JK; reflexivity] |]). lia.
Qed.
#[using="sp0 Hplen CAP HCAP HLEN LEN B2 Hok"] Lemma know_Tc : ltac2:(TCodec.tc2 tcn__Js0DrvD "QM'9'SByR0%211%411'<y8%611%311p061'F'B&R<r6uR9%3221&SAv2%22@1%83@41r7uR?%:221vQ4%82F1%>3F31'A&RB%12?;r5%32=1%5231%5239r4%72;1%9231&R9&R=vGr:%211r9&Q:%746321r;%711&QBr8%2471LQ3%=4<4:1p071p0@1p0E1p0L1p0Q31pVDQ=1pVFQ>1pULQ?1pUNQ@1pR6QB1pW>QH1").
Proof.
intros vals M clo chi plo phi P73 P79 HC HP HK. pose proof (CFG_range fdata) as RC. pose proof PL_range as RP.
unfold knTc. constructor; [|constructor; [|exact HK]]; cbn [kentry_ok edenot ev ENVb ENV].
- rewrite P73, u_small by (subst CFG; lia). lia.
- rewrite P79, u_small by lia. lia.
Qed.
#[using="VM0 Hvsp Htid Hplen HCAP Hsp"] Lemma pl0_to_lh : ltac2:(TCodec.tc2 tcn__Js0DrvD "W0&QO'QK'9'SByR0%211%411'R6%611&Q1y5%2216'<y8%;11%311p0;1'N'F&Q>r8%211'B':&8r7%22E1uRB%63521&R<(3%22;1vS=%;3L21r9u1%7221&QHvRIvS8vS0%449321%D3Q561r:u2%@221&QI%14?987%J3Q;31r;u3%F221&QF%14E?>=%Q03QA31r<u4%L221&QJ%14KEDC%Q63QG31r=u5%Q2221vSE%Q;3QL21r>uQ@%Q7221&SA%12R2Q4%QA3R231r?uR6%Q=221vK%72R81%QG3R831r@uR9%QC221v2%=2R>1%QM3R>31rAuR?%QI221vQ4%C2RD1%R33RD31rBuRA%QO221&Q<%I2RJ1%R93RJ31&R:vGrC%211%431:@'6&QD&R8&R7(S@+E(@%33S221%511(R3%11D%93>31%;11(?%RM3>21&Eu9rD(R2z%211%64SC541+hhb0%511%S73SF31uBrE%<4SI217%S;3SJ18&R5rG%Q311uErF%C4T021>%6241%SC3T41Q;&R9&R=rH%Q<11&QC%5442@1vRJ%11;&Q7vJv1%332F1%TD1T8%T;11&QM%RD2TECvS1%T32T=1%44A@31(4%1284%T93831%T:3T>R9Q8&Q8vH(7'>%12TCTC(=%14TETEKC(;%114%73531vROrJrI%=5<4321'R0vS<(L&QLrOrL+V_iD%SA2UB1rK&QN%11Q>%8576431vS7%11@%<231rQ0%@4QD?21p0B1p0Q11p0Q31p0Q>1p0QC1p0QF1p0QM1p0R61p0R;1p0RF1p0S61p0S<1p0SC1p0SJ1p0T11p0T81p0T?1p0TE1p0TL1p0U31p0U:1p0UD1p0UJ1p0V21p2V61pU@V81pR8V:1pR>V@1pW0VD1pW@VG1pV6VM1pQDVO1").
Proof.
intros K fx' vals1 srX R' M' VM A1 HLH HL1 W0 W1 W2 W3 W4 W5 W48 W70 W73 W79 V81 HR' Hrel H9 H18 H20 HK' HA1 HBR HC1 HPL0 HH1.
pose proof Hsp as Hsp'.
assert (Hpay : payload = []).
{ pose proof payload_len as X. rewrite HPL0 in X. destruct payload; [reflexivity | discriminate]. }
assert (HR2 : regs_ok (ENVb vals1) (sr_upd srX (ridx 21) (EVar 81)) R').
{ apply regs_ok_upd_same; [exact HR' | discriminate |].
rewrite (HR' (21%bv : reg)). change (sr_get srX (21%bv : reg)) with (nth 21 srX (ELit 0)). rewrite H20.
cbn [edenot ev ENVb ENV]. exact V81. }
set (valsL := relay vals1 R' (Z_to_bv 64 0)).
apply (HLH fx' valsL R' M' VM A1 0xc6240%Z 0%Z [(A1, CAP)]).
-
unfold lh_vals. subst valsL. rewrite (relay_len vals1 R' _ ltac:(lia)), relay_81 by lia.
rewrite !(relay_lo vals1 R' _) by lia.
repeat split; try assumption.
+ unfold relay. change 82%nat with (81 + 1)%nat. rewrite vals_hi by lia. cbn [nth lay_ext].
rewrite (HR' (9%bv : reg)). change (sr_get srX (9%bv : reg)) with (nth 9 srX (ELit 0)). rewrite H9. reflexivity.
+ unfold relay. change 83%nat with (81 + 2)%nat. rewrite vals_hi by lia. cbn [nth lay_ext].
rewrite (HR' (18%bv : reg)). change (sr_get srX (18%bv : reg)) with (nth 18 srX (ELit 0)). rewrite H18. reflexivity.
-
subst valsL. eapply (relay_regs vals1 _ R' _ ltac:(lia)); [exact Hrel | exact HR2].
-
subst valsL. eapply (know_ok_agree RSEGS 82); [apply relay_agree; lia | vm_compute; reflexivity |].
eapply ksubl_sound; [exact HK' | vm_compute; reflexivity].
- exact HA1.
- split; [exact HBR|]. left. repeat split; lia.
- exact HC1.
- rewrite Hpay. reflexivity.
- unfold cr1. fold PL. rewrite (proj2 (Z.eqb_eq PL 0) HPL0). exact HH1.
Qed.
Section SE.
Local Abbreviation SEC_T_drv_target := (ltac2:(TCodec.tc2 tcn__Js0DrvD "?&QO&Q>r1%211r2(;'O%211%411vSDr3%211p041p0:1pQD>1")) (only parsing).
Variable K : ltac:(sec_ty2 constr:(SEC_T_drv_target) 0%nat 0%nat).
Theorem drv_target : ltac:(sec_stmt2 constr:(SEC_T_drv_target) 1%nat 0%nat).
Proof using HIok uid VM0 Hva Hve Hvsp Htid Hplen DL HCAP HLEN Hsp Hal Hok Hcr1 K.
intros HLH HK0.
unfold target_k, Js0DrvC.target_k.
intros vals R M VM A1 HL P0 P48 P70 P1 P2 P3 P4 P5 P71 P72 P73 P79 P80 HR HK HA HBR HC HH.
pose proof Hsp as Hsp'. pose proof Hal as Hal'.
pose proof (hz_of_block_range L sp0 DL _ _ HBR) as HZ. pose proof HZ as (Q1 & Q2 & Q4).
pose proof (CFG_range fdata) as HCr. pose proof PL_range as HPr. pose proof (B2_range fdata) as HB2r. pose proof CALLS_range as HKr.
assert (ELEN : LEN = Z.of_nat (length fdata)) by reflexivity.
assert (EPL : PL = (LEN - 6 - CFG)%Z) by reflexivity.
fold CFG in P73, Hok. fold PL in P79. fold B2 in P80.
change (Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals) in HR, HK |- *.
pose proof (hiv_facts' vals P3 P4) as HIV.
assert (HPAY0 : rdn RSEGS M (Z_to_bv 64 (A1 + 6 + CFG)) (length payload) = Some payload).
{ unfold payload. rewrite length_skipn.
pose proof (rdn_skipn RSEGS M (length fdata) (Z_to_bv 64 A1) fdata (Z.to_nat (6 + CFG)) HC ltac:(lia)) as X.
rewrite w_add_nat, u_small in X by lia.
replace (A1 + Z.of_nat (Z.to_nat (6 + CFG)))%Z with (A1 + 6 + CFG)%Z in X by lia. exact X. }
set (vals1 := vals ++ [Z_to_bv 64 CALLS]).
assert (HL1 : length vals1 = 82%nat) by (subst vals1; rewrite length_app, HL; reflexivity).
assert (V81 : vals_ev vals1 81 = Z_to_bv 64 CALLS).
{ subst vals1. rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
assert (VL : forall j x, (j < 81)%nat -> vals_ev vals j = x -> vals_ev vals1 j = x).
{ intros j x Hj Hx. subst vals1. rewrite vals_ev_app_l by (rewrite HL; exact Hj). exact Hx. }
pose proof (VL 0%nat _ ltac:(lia) P0) as W0. pose proof (VL 1%nat _ ltac:(lia) P1) as W1. pose proof (VL 2%nat _ ltac:(lia) P2) as W2.
pose proof (VL 3%nat _ ltac:(lia) P3) as W3. pose proof (VL 4%nat _ ltac:(lia) P4) as W4. pose proof (VL 5%nat _ ltac:(lia) P5) as W5.
pose proof (VL 48%nat _ ltac:(lia) P48) as W48. pose proof (VL 70%nat _ ltac:(lia) P70) as W70.
pose proof (VL 73%nat _ ltac:(lia) P73) as W73. pose proof (VL 79%nat _ ltac:(lia) P79) as W79. pose proof (VL 80%nat _ ltac:(lia) P80) as W80.
pose proof (env_app_regs vals [Z_to_bv 64 CALLS] _ srT0 R ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR1.
pose proof (env_app_know RSEGS vals [Z_to_bv 64 CALLS] _ M knT0 ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK1.
fold vals1 in HR1, HK1. change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals1) in HR1, HK1.
clear HR HK. rename HR1 into HR.
pose proof (hiv_facts' vals1 W3 W4) as HIV1.
clearbody vals1. clear VL HL P0 P1 P2 P3 P4 P5 P48 P70 P71 P72 P73 P79 P80 HIV vals.
assert (HCALLS : CALLS = (if (CFG =? 0)%Z then 1 else B2 mod 4 + 1)%Z) by reflexivity.
assert (Ecx : (CFG =? 0)%Z = false -> edenot (ENVb vals1) calls_x = Z_to_bv 64 CALLS).
{ intros E. unfold ENVb, ENV. rewrite calls_x_callsF, W80, callsF_val by lia. rewrite HCALLS, E. reflexivity. }
destruct (Z.eq_dec PL 0) as [HPL0 | HPLp].
-
assert (TAIL : forall srX R' M',
regs_ok (ENVb vals1) srX R' -> relay_ok_b (sr_upd srX (ridx 21) (EVar 81)) = true ->
nth 9 srX (ELit 0) = ELit 811584 -> nth 18 srX (ELit 0) = ELit 0 ->
edenot (ENVb vals1) (nth 21 srX (ELit 0)) = Z_to_bv 64 CALLS ->
know_ok RSEGS (ENVb vals1) M' knTe ->
M' = mem_denot (ENVb vals1) M (s_log (fst (fst rT00))) ->
srealizes RSEGS scfg (mkCfg (mkst R' (Z_to_bv 64 0x33f34) M' (seg_rom RSEGS)) (model2 VM)) K).
{ intros srX R' M' HR' Hrel H9 H18 H20 HK' EQM.
eapply (pl0_to_lh K fx vals1 srX R' M' VM A1); try eassumption.
- rewrite EQM. unfold above. apply (above_sp0_block sp0 a0s path hw rdraw mem0 fdata Hvsp Hplen vals1); [exact W0 | vm_compute; reflexivity | exact HA].
- rewrite EQM. apply (content_block' sp0 a0s path hw rdraw fdata Hvsp vals1); [exact W0 | vm_compute; reflexivity | eapply (hz_sub sp0); [exact HZ | lia | lia | unfold LEN in HLEN; lia] | exact HC].
- rewrite EQM. eapply (heap_block scfg L HI HIok sp0 Hsp' DL vals1 _ []); [exact W0 | intros i nb Hf; discriminate | vm_compute; reflexivity | exact HH]. }
destruct (CFG =? 0)%Z eqn:ECFG.
+
pose proof (know_Tc vals1 M 0 0 0 0 W73 W79 ltac:(apply Z.eqb_eq in ECFG; lia) ltac:(lia) HK1) as HK. clear HK1.
run_blockT_keep scr0 82%nat.
apply (TAIL sr00 _ _ HR); [vm_compute; reflexivity | reflexivity | reflexivity | | eapply ksubl_sound; [exact HK | vm_compute; reflexivity] | exact EQM].
cbn [nth sr00 edenot]. rewrite HCALLS. reflexivity.
+
pose proof (know_Tc vals1 M 1 32767 0 0 W73 W79 ltac:(apply Z.eqb_neq in ECFG; lia) ltac:(lia) HK1) as HK. clear HK1.
run_blockT_keep scr0 82%nat.
apply (TAIL sr10 _ _ HR); [vm_compute; reflexivity | reflexivity | reflexivity | | eapply ksubl_sound; [exact HK | vm_compute; reflexivity] | exact EQM].
change (nth 21 sr10 (ELit 0)) with calls_x. apply Ecx. reflexivity.
-
assert (TAILm : forall srX R' M',
regs_ok (ENVb vals1) srX R' -> sr_upd srX (ridx 21) (EVar 81) = srTm0 ->
edenot (ENVb vals1) (nth 21 srX (ELit 0)) = Z_to_bv 64 CALLS ->
know_ok RSEGS (ENVb vals1) M' knTe ->
M' = mem_denot (ENVb vals1) M (s_log (fst (fst rT00))) ->
srealizes RSEGS scfg (mkCfg (mkst R' (Z_to_bv 64 0x9aab4) M' (seg_rom RSEGS)) (model2 VM)) K).
2:{ destruct (CFG =? 0)%Z eqn:ECFG.
- pose proof (know_Tc vals1 M 0 0 1 67108857 W73 W79 ltac:(apply Z.eqb_eq in ECFG; lia) ltac:(lia) HK1) as HK. clear HK1.
run_blockT_keep scr0 82%nat.
apply (TAILm sr01 _ _ HR); [vm_compute; reflexivity | | eapply ksubl_sound; [exact HK | vm_compute; reflexivity] | exact EQM].
cbn [nth sr01 edenot]. rewrite HCALLS. reflexivity.
- pose proof (know_Tc vals1 M 1 32767 1 67108857 W73 W79 ltac:(apply Z.eqb_neq in ECFG; lia) ltac:(lia) HK1) as HK. clear HK1.
run_blockT_keep scr0 82%nat.
apply (TAILm sr11 _ _ HR); [vm_compute; reflexivity | | eapply ksubl_sound; [exact HK | vm_compute; reflexivity] | exact EQM].
change (nth 21 sr11 (ELit 0)) with calls_x. apply Ecx. reflexivity. }
intros srX R1 M1 HR1 HsrX H20 HK1' EQM.
assert (HH1 : hi_heap HI [(A1, CAP)] (crC) M1 VM).
{ rewrite EQM. eapply (heap_block scfg L HI HIok sp0 Hsp' DL vals1 _ []); [exact W0 | intros i nb Hf; discriminate | vm_compute; reflexivity | exact HH]. }
assert (HA1 : above M1).
{ rewrite EQM. unfold above. apply (above_sp0_block sp0 a0s path hw rdraw mem0 fdata Hvsp Hplen vals1); [exact W0 | vm_compute; reflexivity | exact HA]. }
assert (HC1 : rdn RSEGS M1 (Z_to_bv 64 A1) (length fdata) = Some fdata).
{ rewrite EQM. apply (content_block' sp0 a0s path hw rdraw fdata Hvsp vals1); [exact W0 | vm_compute; reflexivity | eapply (hz_sub sp0); [exact HZ | lia | lia | unfold LEN in HLEN; lia] | exact HC]. }
assert (HPAY1 : rdn RSEGS M1 (Z_to_bv 64 (A1 + 6 + CFG)) (length payload) = Some payload).
{ rewrite EQM. apply (content_block' sp0 a0s path hw rdraw fdata Hvsp vals1); [exact W0 | vm_compute; reflexivity | eapply (hz_sub sp0); [exact HZ | lia | rewrite payload_len; lia | rewrite payload_len; unfold LEN in HLEN; lia] | exact HPAY0]. }
clear EQM HH HA HC HPAY0 HK1.
assert (HR2 : regs_ok (ENVb vals1) srTm0 R1).
{ rewrite <- HsrX. apply regs_ok_upd_same; [exact HR1 | discriminate |].
rewrite (HR1 (21%bv : reg)). change (sr_get srX (21%bv : reg)) with (nth 21 srX (ELit 0)). rewrite H20.
cbn [edenot ev ENVb ENV]. exact V81. }
clear HR1 HsrX H20. rename HK1' into HK.
eapply (malloc_site scfg L HI HIok sp0 Hsp' Hal' DL vals1 _ srTm0 knTe R1 M1 (model2 VM) [(A1, CAP)] (crC) PL (-208)
[(48%nat, 65536%Z)] [] 0x33ee0 K);
[ exact HR2 | exact HK
| rewrite HL1; vm_compute; reflexivity | rewrite HL1; vm_compute; reflexivity | rewrite HL1; lia
| exact W0 | exact HIV1 | vm_compute; reflexivity
| regv HR2 (2 : reg); cbn [edenot ev ENVb ENV]; rewrite W0; apply alu_add_w_lit
| lia | reflexivity
| regv HR2 (10 : reg); cbn [edenot ev ENVb ENV]; exact W79
| pose proof PL_range; lia
| apply Hcr1; lia
| regv HR2 (4 : reg); reflexivity
| regv HR2 (1 : reg); reflexivity
| lia | reflexivity
| exact HH1 | reflexivity | reflexivity | reflexivity
| intros i nb Hf; cbn in Hf;
destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL1; lia|];
rewrite W48, u_small by lia; exists CAP; split; [lia|]; split; [left; reflexivity | exact HBR] | discriminate]
| intros v b Hf; discriminate
| exact HK0 | ].
intros R' M' model' A2 vals' E' HL' HA2 HR' HK' HH' HBUT HBR2 HAP HAB HBLK HIMG. subst vals' E'.
rewrite (m2_but _ _ HBUT). rewrite (m2_but _ _ HBUT), m2_vm in HH'.
set (VM2 := m_vmmaps model') in *. clearbody VM2.
set (vals2 := vals1 ++ junk_vals R') in *.
change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals2) in HR', HK'.
rewrite HL1 in HL', HA2, HR', HK'. change (82 + 10)%nat with 92%nat in HA2.
pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U4). pose proof HBR2 as (_ & _ & U3 & _ & _).
assert (X0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact W0).
assert (X3 : vals_ev vals2 3 = auxvp sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact W3).
assert (X4 : vals_ev vals2 4 = rnd sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact W4).
assert (X48 : vals_ev vals2 48 = Z_to_bv 64 A1) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact W48).
assert (X73 : vals_ev vals2 73 = Z_to_bv 64 CFG) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact W73).
assert (X79 : vals_ev vals2 79 = Z_to_bv 64 PL) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact W79).
pose proof (hiv_facts' vals2 X3 X4) as HIV2.
apply Forall_app in HK' as [HKB HK'].
assert (WST : store_ok RSEGS M' (Z_to_bv 64 A2) (length payload) = true).
{ pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HKB))) as X. cbn [kentry_ok] in X. destruct X as [_ X].
specialize (X 0%Z (length payload) ltac:(lia) ltac:(rewrite payload_len; lia)).
unfold estart in X. cbn [a_base a_off edenot ev ENVb ENV] in X. change (82 + 10)%nat with 92%nat in X.
rewrite HA2, u_small, Z.add_0_r, Z.add_0_r in X by lia. exact X. }
assert (HKU : know_ok RSEGS (ENVb vals2) M' knU0).
{ change knU0 with (kn_blk2 92 ++ knTk). apply Forall_app. split.
- unfold kn_blk2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [kentry_ok edenot ev ENVb ENV]; rewrite HA2, u_small by lia; lia.
- exact HK'. }
clear HK' HKB HK HR2 HR. rename HKU into HK. rename HR' into HR.
assert (HC2 : rdn RSEGS M' (Z_to_bv 64 A1) (length fdata) = Some fdata).
{ rewrite <- HC1. apply rdn_agree. intros k Hk. rewrite u_small by lia. apply HBLK; [lia|].
exists (A1, CAP). split; [left; reflexivity|]. cbn [fst snd]. lia. }
assert (HPAY2 : rdn RSEGS M' (Z_to_bv 64 (A1 + 6 + CFG)) (length payload) = Some payload).
{ rewrite <- HPAY1. apply rdn_agree. intros k Hk. rewrite payload_len in Hk. rewrite u_small by lia. apply HBLK; [lia|].
exists (A1, CAP). split; [left; reflexivity|]. cbn [fst snd]. lia. }
clear HC1 HPAY1.
run_blockT_keep scr0 114%nat.
cbn [mem_denot] in EQM. subst M0.
assert (MCH : mcH M' (Z_to_bv 64 A2) (Z_to_bv 64 (A1 + 6 + CFG)) PL payload).
{ pose proof PL_range as HPr2. pose proof payload_len as PLN.
constructor; rewrite ?PLN, ?u_small by lia; try lia.
- rewrite <- PLN. exact HPAY2.
- rewrite <- PLN. exact WST.
- specialize (HAP (A1, CAP) ltac:(left; reflexivity)). cbn [fst snd] in HAP. lia. }
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
destruct (ref_memcpy M' (Z_to_bv 64 A2) (Z_to_bv 64 (A1 + 6 + CFG)) PL payload (seg_rom RSEGS) MCH Rc (Z_to_bv 64 0x33ef4)
ltac:(apply ret_ok_even; reflexivity)
ltac:(regv HR (1 : reg); reflexivity)
ltac:(regv HR (10 : reg); cbn [edenot ev ENVb ENV]; exact HA2)
ltac:(regv HR (11 : reg); cbn [edenot ev ENVb ENV]; rewrite X48, X73, !alu_add_Z; f_equal; lia)
ltac:(regv HR (12 : reg); cbn [edenot ev ENVb ENV]; exact X79)) as (R2 & MS & KP)
end.
replace (Z_to_bv 64 692576) with (0xa9160%bv : word) by (apply bv_eq; reflexivity).
eapply srz_msteps; [reflexivity | reflexivity | exact MS |]. clear MS.
pose proof (regs_after_keeps vals2 _ srU _ R2 callee_kept ltac:(rewrite HL'; vm_compute; reflexivity) HR KP ltac:(cbn; intuition discriminate)) as HR3.
rewrite HL' in HR3. change (sr_after_call_j srU (map ridx callee_kept) 114) with srV0 in HR3.
set (vals3 := vals2 ++ junk_vals R2) in *.
assert (HL3 : length vals3 = 146%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL'; reflexivity).
pose proof (know_blockwrite sp0 Hsp' vals2 _ M' A2 PL A2 payload knU0 X0 HZ2 ltac:(lia)
ltac:(rewrite payload_len; lia) HIV2 HK) as HK3.
change (kn_keep_g 0 0 0 [] [] [3%nat; 4%nat] IMG_CLIENT IMG_RW knU0) with knV0 in HK3.
pose proof (env_app_know RSEGS vals2 (junk_vals R2) _ _ knV0 ltac:(rewrite HL'; vm_compute; reflexivity) HK3) as HK4.
fold vals3 in HK4. change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals3) in HR3, HK4.
clear HK HK3 HR. rename HR3 into HR. rename HK4 into HK.
set (M3 := wbytes M' (Z_to_bv 64 A2) payload) in *.
assert (HH3 : hi_heap HI [(A2, PL); (A1, CAP)] (debit L (crC) PL) M3 VM2).
{ subst M3. eapply (heap_wbytes scfg L HI HIok sp0 Hsp' DL); [exact HH' | left; reflexivity | lia | rewrite payload_len; lia | lia]. }
assert (HA3 : above M3).
{ subst M3. intros a Ha. rewrite wbytes_out; [rewrite HAB by exact Ha; apply HA1; exact Ha | rewrite u_small, payload_len by lia; lia | rewrite u_small, payload_len by lia; lia]. }
assert (HC3 : rdn RSEGS M3 (Z_to_bv 64 A1) (length fdata) = Some fdata).
{ subst M3. specialize (HAP (A1, CAP) ltac:(left; reflexivity)). cbn [fst snd] in HAP.
rewrite rdn_wbytes_out; [exact HC2 | rewrite !u_small, payload_len by lia; lia | rewrite u_small by lia; lia | rewrite u_small, payload_len by lia; lia]. }
assert (HPAY3 : rdn RSEGS M3 (Z_to_bv 64 A2) (length payload) = Some payload).
{ subst M3. apply rdn_wbytes_hit. rewrite u_small, payload_len by lia. lia. }
assert (Y0 : vals_ev vals3 0 = sp0) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X0).
assert (Y82 : vals_ev vals3 92 = Z_to_bv 64 A2) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact HA2).
assert (YL : forall j, (j < 82)%nat -> vals_ev vals3 j = vals_ev vals1 j).
{ intros j Hj. subst vals3 vals2. rewrite !vals_ev_app_l by (rewrite ?length_app, ?junk_vals_length, HL1; lia). reflexivity. }
clearbody M3 vals3. clear HC2 HPAY2.
run_blockT_keep scr0 146%nat.
cbn [mem_denot] in EQM. subst M0.
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rv _ _ _) _) _ => rename Rv into RV end.
set (valsL := relay vals3 RV (Z_to_bv 64 0)).
apply (HLH fx valsL RV M3 VM2 A1 A2 A2 [(A2, PL); (A1, CAP)]).
+ unfold lh_vals. subst valsL. rewrite (relay_len vals3 RV _ ltac:(lia)), relay_81 by lia.
rewrite !(relay_lo vals3 RV _) by lia. rewrite !YL by lia.
repeat split; try assumption.
* unfold relay. change 82%nat with (81 + 1)%nat. rewrite vals_hi by lia. cbn [nth lay_ext].
regv HR (9 : reg). cbn [edenot ev ENVb ENV]. exact Y82.
* unfold relay. change 83%nat with (81 + 2)%nat. rewrite vals_hi by lia. cbn [nth lay_ext].
regv HR (18 : reg). cbn [edenot ev ENVb ENV]. exact Y82.
+ subst valsL. eapply (relay_regs vals3 srV RV _ ltac:(lia)); [vm_compute; reflexivity | exact HR].
+ subst valsL. eapply (know_ok_agree RSEGS 82); [apply relay_agree; lia | vm_compute; reflexivity |].
eapply ksubl_sound; [exact HK | vm_compute; reflexivity].
+ exact HA3.
+ split; [exact HBR|]. right. split; [lia|]. split; [reflexivity|]. split; [exact HBR2|]. split; [exact HAP | reflexivity].
+ exact HC3.
+ exact HPAY3.
+ unfold cr1. fold PL. replace (PL =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). exact HH3.
Qed.
End SE.
End DrvD.
End FPX_1.
