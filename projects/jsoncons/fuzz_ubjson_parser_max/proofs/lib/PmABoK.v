(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA LibIface
AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR
PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa
PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmAParKit PmAReset1 PmAUarK PmAUar PmAUarKS.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmABoK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABoK.PMABOK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABoK.PMABOK.WithHeap.Call."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABoK.PMABOK.WithHeap.Call.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStepA.PMKA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreA.L5CA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5StepAR.L5SAR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "0Aw'"; "0BX"; "1bool"; "1fst"; "1list"; "1option"; "1prod"; "1snd"; "2and"; "2eq"; "3Z"; "0F"; "0FF"; "0HI"; "0K"]; ["0L"; "0LBX"; "0LK'"; "0LKc"; "4Model"; "5bvmap"; "0M'"; "0M0"; "0M1"; "0M1'"; "0Mc"; "0R"; "0R'"; "0R0"; "6mrestrict"; "7credit"]; ["7regs_preserved"; "8ahid"; "8fframe"; ":ra_ok"; ":range"; "9SCFG"; ";SCR"; "=FF'"; "=binv'"; "=bst"; "=bste"; "=fsh"; "=hdr"; "=vfacts"; "<WR"; "<ocell"]; ["<oec"; "<own"; ">AADDR_A"; ">ADDR_A"; "?p_src"; "?parser_own"; "?pst"; "?sr_qc"; "?srcst"; "?strm"; "@cfg"; "@ec_at"; "@entryA"; "@o_ec"; "@o_is"; "@o_p"]; ["@o_src"; "@o_v"; "@run_pre"; "@src_spec"; "@src_step"; "@with_src"; "Awapp"; "BFPState"; "Bgetr"; "Csrealizes"; "Dastk"; "Eek"; "Floaded_segments"; "0S"; "0SCFG_P"; "0SPEC"]; ["GIn"; "Hadd"; "Hle"; "Hof_nat"; "Hpow"; "Hsub"; "0Wextra"; "0Wx"; "0X"; "0a"; "0ar"; "0args"; "0c"; "0crc"; "0e"; "0fb"]; ["0fx"; "0fx'"; "0h"; "0model'"; "0modelc"; "0pc"; "0res"; "0rr"; "0s"; "0sm"; "0sm'"; "0src'"; "IZ_to_bv"; "Ibv"; "0str"; "0typed"]; ["0v"; "0x"]]).
Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMABOK.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Definition SCR : Z := 26624.
Definition BARR : Z := 0xb0ec4.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (S r fb cat : Z) (s0 : PM.pst) (str : PM.vstr) (sm0 : PM.strm) (e0 : bool).
Hypothesis HH0 : ri_inv HI (PM.parser_own s0 ++ LBX) FF LK0 cr0 Aw0 M0 (vml_of model0).
Hypothesis AM0 : L5CA.amodel_ok Aw0 model0.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R0 M0 S r 7.
Hypothesis FRM : PMSPA.ffroomA 7 FF LK0.
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis FOK : PMSPA.frame_okA FF fb.
Hypothesis SP32 : S mod 32 = 0.
Hypothesis ARGS : PMSPA.args3 AD R0 fb s0.
Hypothesis RPRE : PMSPA.run_pre RSEGS AD PMA.AAD M0 fb s0 str sm0 e0.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis INV : PM.inv s0.
Hypothesis EC0 : PMSPA.ec_at RSEGS M0 (PMSPA.o_ec AD fb) 0 cat.
Hypothesis UNR : PM.unread (PM.p_src s0) sm0 < 2 ^ 26.
Hypothesis CRED : PMSPA.credit_le (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s0)) cr0.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (e' : bool) (cr' : credit),
regs_preserved R0 R' ->
PMSPA.run_post RSEGS AD PMA.AAD (fun _ => PMSPA.prog_value) R' M' fb s0 s' str sm0 sm' e0 e' cat ->
L5CA.ahpres L ar LBX FF S (PMSPA.pm_scr 7) (PMSPA.W_run AD fb) M0 M' ->
PMSPA.credit_keep cr0 cr' (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s0)) (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s')) ->
model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K.
Hypothesis PEEK : PMA.peek_spec L ar HI.
Hypothesis IGN : PMA.ignore_spec L ar HI.
Hypothesis SRD : PMA.src_read_spec L ar HI.
Hypothesis GLS : PMA.get_length_spec L ar HI.
Hypothesis MKE : PMA.make_ec_spec L ar HI.
Hypothesis PMI : PMA.push_mi_spec L ar HI.
Hypothesis PMS : PMA.push_ms_spec L ar HI.
Hypothesis PMSU : PMA.push_msu_spec L ar HI.
Definition op : Z := PMSPA.o_p AD fb.
Definition ois : Z := PMSPA.o_is AD fb.
Definition ov : Z := PMSPA.o_v AD fb.
Definition oec : Z := PMSPA.o_ec AD fb.
Definition WR : list L5.range := PMSPA.W_run AD fb.
Definition U (x : nat) : Z := bv_unsigned (getr R0 (reg x)).
Definition ocell (a : Z) : Prop := S - 104 <= a < S.
Definition own (M : word -> option byte) : Prop :=
L5.u64_at RSEGS M (S - 8) (U 1) /\ L5.u64_at RSEGS M (S - 16) (U 8) /\ L5.u64_at RSEGS M (S - 24) (U 9) /\ L5.u64_at RSEGS M (S - 32) (U 18)
/\ L5.u64_at RSEGS M (S - 40) (U 19) /\ L5.u64_at RSEGS M (S - 48) (U 20) /\ L5.u64_at RSEGS M (S - 56) (U 21) /\ L5.u64_at RSEGS M (S - 64) (U 22)
/\ L5.u64_at RSEGS M (S - 72) (U 23) /\ L5.u64_at RSEGS M (S - 80) (U 24) /\ L5.u64_at RSEGS M (S - 88) (U 25) /\ L5.u64_at RSEGS M (S - 96) (U 26)
/\ L5.u64_at RSEGS M (S - 104) (U 27).
Lemma own_agree : ltac2:(TCodec.tc2 tcn__PmABoK "Q?'S=yR0%211'6y8%511%311p051pW462&RBz&REvR=+S8%3221%6251&RD+2+R0%3221%;281&QAr4%211';&Q?r1%211':r6&S<r2%22O1%411r7%113%83N31p0:1pUD>1r5%C11p031p0C1p0G1p0M1pQDQ51pQBQ71").
Proof. intros M1 M1'.
unfold own, ocell. intros H1 H2 (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13) AG.
assert (KEEP : forall k v, 8 <= k <= 104 -> L5.u64_at RSEGS M1 (S - k) v -> L5.u64_at RSEGS M1' (S - k) v).
{ intros k v Hk X. apply (L5C.u64_at_agree RSEGS M1 M1'); [intros i Hi; apply AG; lia| lia| lia| exact X]. }
repeat split; (apply KEEP; [lia| assumption]).
Qed.
Definition sd (src : PM.srcst) : PM.pst :=
PM.PST (PM.p_more s0) (PM.p_done s0) (PM.p_depth s0 + 1) src (PM.p_tb s0) (PM.p_tg s0) (PM.p_b s0) (PM.p_k s0) (PM.p_stk s0).
Definition sdl (s : PM.pst) : Prop := PM.p_more s = PM.p_more s0 /\ PM.p_done s = PM.p_done s0 /\ PM.p_depth s = PM.p_depth s0 + 1 /\ PM.p_stk s = PM.p_stk s0.
Definition spush (src : PM.srcst) (b k : Z) (c : PM.pstate) : PM.pst :=
PM.PST (PM.p_more s0) (PM.p_done s0) (PM.p_depth s0 + 1) src (PM.p_tb s0) (PM.p_tg s0) b k (PM.p_stk s0 ++ [c]).
Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model).
Hypothesis G : PMAUK.gctx L ar HI LBX FF LK0 Aw0 S SCR (S - 128) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0).
Definition FF' : list fframe := (F, 0, S - 128 + 32) :: FF.
Definition binv' (BX : list (Z * Z)) (Mc : word -> option byte) (modelc : Model) (LKc : list fframe) (crc : credit) (Ac : list (Z * Z)) : Prop :=
PMAUK.binv L ar HI M0 model0 LBX FF LK0 Aw0 S SCR (S - 128) own F 0 WR BX Mc modelc LKc crc Ac.
Definition hdr (Mc : word -> option byte) : Prop :=
L5.u64_at RSEGS Mc F 1102416563 /\ L5.u64_at RSEGS Mc (F + 8) 78501 /\ L5.u64_at RSEGS Mc (F + 16) 724676 /\ L5.u64_at RSEGS Mc (S - 128) F.
Definition fsh (typed : bool) (Mc : word -> option byte) : Prop :=
L5.u8_at RSEGS Mc (F / 8 + 2147450880) 241 /\ L5.u8_at RSEGS Mc (F / 8 + 2147450881) 241 /\ L5.u8_at RSEGS Mc (F / 8 + 2147450882) 241
/\ L5.u8_at RSEGS Mc (F / 8 + 2147450883) 241 /\ L5.u8_at RSEGS Mc (F / 8 + 2147450884) (if typed then 1 else 248)
/\ L5.u8_at RSEGS Mc (F / 8 + 2147450885) 243 /\ L5.u8_at RSEGS Mc (F / 8 + 2147450886) 243 /\ L5.u8_at RSEGS Mc (F / 8 + 2147450887) 243.
Abbreviation pot := (fun (s : PM.pst) => PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s)).
Definition bst (typed : bool) (s : PM.pst) (sm : PM.strm) (e : bool) (Mc : word -> option byte) (modelc : Model) (LKc : list fframe) (crc : credit) (Ac : list (Z * Z)) : Prop :=
binv' (PM.parser_own s) Mc modelc LKc crc Ac
/\ PMSPA.run_pre RSEGS AD PMA.AAD Mc fb s str sm e /\ PMSPA.ec_at RSEGS Mc oec 0 cat
/\ hdr Mc /\ fsh typed Mc
/\ PMSPA.src_step (PM.p_src s0) (PM.p_src s) sm0 sm /\ (e0 = true -> e = true) /\ sdl s
/\ PMSPA.credit_le (pot s) crc /\ PMSPA.credit_keep cr0 crc (pot s0) (pot s).
Lemma frame_geo : ltac2:(TCodec.tc2 tcn__PmABoK "Q3'9':';&QO&QCvRO%3221&RA+^@%2241%93841&QN%1287+S0%7291%>3=31&R1%12=<+]@%<2>1%C3B31&QM%12BA+o0%A2C1%H3G31&R0%12GF+_8%F2H1%M3L31%O261%Q02<1%Q12B1%Q22H1").
Proof. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. unfold PMSPA.o_src. change (PMSPA.o_p AD fb) with (fb + 464). lia. Qed.
Lemma wappR : ltac2:(TCodec.tc2 tcn__PmABoK "3&R6&Q>%211").
Proof using HH0 FOK HIok.
pose proof FOK as ((rs & Hfb) & Fal).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH0) as (WB & WF & FSAPP & FSCEIL & _).
pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 4) with 1024 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
unfold WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_vec, PMSPA.o_ec, PMSPA.o_p.
cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A].
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia.
Qed.
Definition vfacts (typed : bool) (v : Z) (MV : word -> option byte) : Prop :=
(0 <= S < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= ov < 2 ^ 64 /\ 0 <= oec < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64)
/\ L5.img_clear MV 65536 1261568 /\ L5.u64_at RSEGS MV 1289464 2147450880 /\ L5.u32_at RSEGS MV 1289472 1
/\ 140735332487328 <= S <= 140737488355328 /\ S mod 32 = 0 /\ L5.writable RSEGS MV (S - 160) 160
/\ 6885376 <= op <= 140737488354944 /\ op mod 8 = 0 /\ (2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784)
/\ L5KA.zeros_at MV ((op / 8) + 2147450880) 3 /\ L5KA.zeros_at MV (((op + 32) / 8) + 2147450880) 44 /\ L5KA.zeros_at MV (((op + 20) / 8) + 2147450880) 1
/\ L5.writable RSEGS MV op 384 /\ ((S - 160) + 160 <= op \/ op + 384 <= (S - 160))
/\ 6885376 <= oec <= 140737488355312 /\ oec mod 8 = 0 /\ (2147446784 + 17592186048512 <= oec \/ oec + 16 <= 2147446784)
/\ L5KA.zeros_at MV ((oec / 8) + 2147450880) 2 /\ L5.writable RSEGS MV oec 16 /\ ((S - 160) + 160 <= oec \/ oec + 16 <= (S - 160))
/\ 6885376 <= ov <= 140737488355320 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 8 <= 2147446784)
/\ L5KA.zeros_at MV ((ov / 8) + 2147450880) 1 /\ L5.writable RSEGS MV ov 8 /\ ((S - 160) + 160 <= ov \/ ov + 8 <= (S - 160))
/\ (op + 384 <= oec \/ oec + 16 <= op) /\ (op + 384 <= ov \/ ov + 8 <= op) /\ (oec + 16 <= ov \/ ov + 8 <= oec)
/\ 6885376 <= F <= 140737488355264 /\ F mod 32 = 0 /\ L5.defined MV F 64 /\ L5.writable RSEGS MV F 64
/\ (2147446784 + 17592186048512 <= F \/ F + 64 <= 2147446784) /\ L5.writable RSEGS MV ((F / 8) + 2147450880) 8 /\ L5.u64_at RSEGS MV (F + 56) fl
/\ 4096 <= fl <= 140737488355327 /\ L5.writable RSEGS MV fl 1 /\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) /\ (F + 64 <= fl \/ fl + 1 <= F)
/\ ((S - 160) + 160 <= F \/ F + 64 <= (S - 160)) /\ ((S - 160) + 160 <= fl \/ fl + 1 <= (S - 160))
/\ (op + 384 <= F \/ F + 64 <= op) /\ (op + 384 <= fl \/ fl + 1 <= op)
/\ (((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((op / 8) + 2147450880))
/\ (oec + 16 <= F \/ F + 64 <= oec) /\ (oec + 16 <= fl \/ fl + 1 <= oec)
/\ (((oec / 8) + 2147450880) + 2 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((oec / 8) + 2147450880))
/\ (ov + 8 <= F \/ F + 64 <= ov) /\ (ov + 8 <= fl \/ fl + 1 <= ov)
/\ (((ov / 8) + 2147450880) + 1 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((ov / 8) + 2147450880))
/\ (F + 64 <= 65536 \/ 65536 + 1196032 <= F)
/\ hdr MV /\ own MV /\ fsh typed MV
/\ L5.u32_at RSEGS MV oec v /\ L5.u64_at RSEGS MV ov 1231168 /\ L5.u8_at RSEGS MV (op + 16) 0
/\ L5KA.zeros_at MV 2147604784 1 /\ L5KA.zeros_at MV 2147604785 1.
Lemma vpack : ltac2:(TCodec.tc2 tcn__PmABoK "R9'3'5'7';%2211%411'QF'QI'S=yR0%211'6y8%511%311p051'D&Q2%A11&O&Q8r;r5r4r3r2r1%76654321&R2&R<&QC&QBr6vROvS>r:r9%9987654@321&QKr7&Q@r8%45=3261&Q<%113&Q;r@%221;&Q=rAr<&N&Q1%12EA%321C%73651p091p0=1p0@1p0F1p0Q11p2QH1pULQ;1pQ8Q=1pV:Q@1pQFQB1pUJQO1pW2R01pUNR41pVDQN1pVBR01p6R21pW0R81").
Proof using All. intros typed BX s sm e v c Mc modelc LKc crc Ac.
intros BI RP EC HD FSH.
pose proof BI as BI'. destruct BI' as (HHc & AMc & MRTc & IAc & ILKc & ASTKc & EKc & DKc & OWNc & SHDc).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof G as G'. destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
pose proof frame_geo as (Eop & Eois & Eov & Eoec & Eos).
pose proof FOK as ((rs & Hfb) & Fal).
assert (FOK' : PMSPA.frame_okA FF' fb) by (split; [exists rs; right; exact Hfb| exact Fal]).
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc fb _ s HHc FOK' PA) as ((O1 & O8 & ONSH) & Zop & Z32 & Z20 & OWR & OCE & OAV & AOP & _).
pose proof (PMAPAR.ov_vis L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc fb HHc FOK' VIS) as ((V1 & V8 & VNSH) & Zv & VWR & VCE & VU & AOV & _).
pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc fb v c HHc FOK' EC) as ((E1 & E8 & ENSH) & Ze & EWR & ECE & EU & AOE & _).
pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc HHc BASE) as (VM0 & VM1 & VM2).
unfold SCR in ASTKc.
pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc S 26624 160 HHc ASTKc ltac:(lia)) as (SL160 & SH160 & SWR).
pose proof (PMAUK.vis_facts L ar C HI LYa HIok M0 model0 LBX FF LK0 Aw0 S SCR (S - 128) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G WR BX Mc modelc LKc crc Ac BI)
as ((WSv & IMGC & CSB & CUAR & RMS) & OWNv & (FDEF & FW & FSHW & FLU & FLW) & (FLC8 & FLV8 & FV8 & SV8 & SHV8)).
pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ FF' LKc crc Ac Mc modelc 1231240 1 HHc ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as ZV88.
pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ FF' LKc crc Ac Mc modelc 1231232 1 HHc ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as ZV16.
change (1231240 / 8 + 2147450880) with 2147604785 in ZV88. change (1231232 / 8 + 2147450880) with 2147604784 in ZV16.
change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. replace (F + 64 - 8) with (F + 56) in FLU by lia.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & _ & NDF & _).
assert (HfbF : In (fb, 4, rs) FF') by (right; exact Hfb).
assert (FAP : F + 64 <= fb \/ fb + 1024 <= F).
{ destruct (WF (F, 0, S - 128 + 32) (or_introl eq_refl)) as (_ & _ & _ & _ & _ & APF). cbn [ff_addr ff_class fst snd] in APF. change (ff_bytes 0) with 64 in APF.
assert (Iin : In (fb, 4, rs) (ff_remove F FF' ++ LKc)).
{ apply in_or_app. left. unfold FF'. cbn [ff_remove ff_addr]. rewrite Z.eqb_refl. exact Hfb. }
destruct (APF _ Iin) as [X0|X0]; cbn [ff_addr ff_class fst snd] in X0; change (ff_bytes 4) with 1024 in X0; [left| right]; lia. }
assert (FLo : forall o n, fb + 32 <= o -> o + n <= fb + 1016 -> o + n <= fl \/ fl + 1 <= o).
{ intros o n X1 X2. destruct (Z_lt_le_dec fl o) as [Y|Y]; [right; lia|]. destruct (Z_lt_le_dec fl (o + n)) as [Y'|Y']; [|left; lia]. exfalso. apply FLNC.
apply (L5SAR.fframe_client L ar LBX FF' 0 0 fb 4 rs); [exact HfbF| change (ff_bytes 4) with 1024; lia]. }
unfold SB in *. fold op ov oec in *.
assert (Fd : F = 8 * (F / 8)) by lia.
assert (Od : op = 8 * (op / 8)) by (pose proof (Z.div_mod op 8 ltac:(lia)); lia).
assert (Ed : oec = 8 * (oec / 8)) by (pose proof (Z.div_mod oec 8 ltac:(lia)); lia).
assert (Vd : ov = 8 * (ov / 8)) by (pose proof (Z.div_mod ov 8 ltac:(lia)); lia).
unfold vfacts.
split; [lia|]. split; [exact VM0|]. split; [exact VM1|]. split; [exact VM2|].
split; [lia|]. split; [exact SP32|]. split; [exact SWR|].
split; [lia|]. split; [exact O8|]. split; [exact ONSH|]. split; [exact Zop|]. split; [exact Z32|]. split; [exact Z20|]. split; [exact OWR|]. split; [lia|].
split; [lia|]. split; [exact E8|]. split; [exact ENSH|]. split; [exact Ze|]. split; [exact EWR|]. split; [lia|].
split; [lia|]. split; [exact V8|]. split; [exact VNSH|]. split; [exact Zv|]. split; [exact VWR|]. split; [lia|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [exact F32|]. split; [exact FDEF|]. split; [exact FW|]. split; [exact FBIG|]. split; [exact FSHW|]. split; [exact FLU|].
split; [lia|]. split; [exact FLW|]. split; [exact FLBIG|]. split; [exact FLA|].
split; [lia|]. split; [lia|].
split; [lia|]. split; [apply (FLo op 384); lia|].
split; [lia|].
split; [lia|]. split; [apply (FLo oec 16); lia|].
split; [lia|].
split; [lia|]. split; [apply (FLo ov 8); lia|].
split; [lia|].
split; [lia|].
split.
{ pose proof HD as (H0 & H8 & H16 & H128).
split; [apply (proj2 (L5A.u64_at_vis _ Mc F _ (L5A.avis_sub _ F 64 F 8 FV8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact H0|].
split; [apply (proj2 (L5A.u64_at_vis _ Mc (F + 8) _ (L5A.avis_sub _ F 64 (F + 8) 8 FV8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact H8|].
split; [apply (proj2 (L5A.u64_at_vis _ Mc (F + 16) _ (L5A.avis_sub _ F 64 (F + 16) 8 FV8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact H16|].
apply (proj2 (L5A.u64_at_vis _ Mc (S - 128) _ (L5A.avis_sub _ (S - 128) (S - (S - 128)) (S - 128) 8 SV8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact H128. }
split; [exact OWNv|].
split.
{ pose proof FSH as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7).
assert (SHB : forall a w, F / 8 + 2147450880 <= a < F / 8 + 2147450888 -> L5.u8_at RSEGS Mc a w -> L5.u8_at RSEGS (mrestrict (ahid Ac modelc) Mc) a w).
{ intros a w Ha X. apply (proj2 (L5A.u8_at_vis _ Mc a w (L5A.avis_sub _ (F / 8 + 2147450880) 8 a 1 SHV8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
repeat split; (apply SHB; [lia| assumption]). }
split; [exact EU|]. split; [exact VU|].
split; [pose proof PA as (_ & _ & _ & _ & _ & _ & P16 & _); apply (proj2 (L5A.u8_at_vis _ Mc (op + 16) 0 (OAV (op + 16) 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact P16|].
split; [exact ZV16| exact ZV88].
Qed.
Lemma centry : ltac2:(TCodec.tc2 tcn__PmABoK "RI&Ey5'S=yR0%211%5241'6y8%611%311p061';&R:vRJr3vR=&Q6%544321&R;v@vAv=&Q>vGr4%796<54:9321':&R8r6&S<&RCu1%211%42Q01%7261%62Q0;%:3Q021&Q3r5%211r8u2%<11%>2Q:1%A241&RE+T0%22Q01%C2Q=1%G3Q=51r9u3%F11%H2QD1%K241vM%M213%O3QE31r:u4%N11%Q02QL1%Q3241%Q4282%Q63QL21'9&RBz%221L+6%42N1%6231&QL&QCr<r;%483QIQO21MBJp061p0>1p0F1p0O1p0Q:1p0Q>1p0QJ1p0R31pV6R:1pUBR;1pQFR=1pQHRC1").
Proof using All. intros R Mc X h.
intros ASTKc EKc A1 RAX A2 A3 A4 Hh.
pose proof ENT as (Rra0 & RAok0 & Rsp0 & Rgp0 & Rtp0 & ASTK0 & STKSH0). change (PMSPA.pm_scr 7) with 26624 in *. change (26624 / 8) with 3328 in STKSH0.
pose proof ASTK0 as (A16 & SLO & SHI & SPT & SDEF & SUP). unfold SCR in *.
unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
split; [rewrite A3; rewrite <- L5K.rl3; exact Rgp0|]. split; [rewrite A4; rewrite <- L5K.rl4; exact Rtp0|].
split.
- apply (L5SAR.astk_sub ar Mc Mc S 26624 128 (PMSPA.pm_scr h) ASTKc (fun _ Y => Y)); unfold PMSPA.pm_scr; [lia| lia| lia|].
replace (S - 128) with (S + (-8) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
- assert (M8a : (S - 26624) mod 8 = 0) by (apply PMKA.mod16_8'; replace (S - 26624) with (S + (-1664) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
assert (M8b : (S - 128 - PMSPA.pm_scr h) mod 8 = 0).
{ apply PMKA.mod16_8'. unfold PMSPA.pm_scr. replace (S - 128 - (12288 + 2048 * h)) with (S + (-(776 + 128 * h)) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
assert (G8 : PMSPA.pm_scr h / 8 = 1536 + 256 * h).
{ unfold PMSPA.pm_scr. replace (12288 + 2048 * h) with ((1536 + 256 * h) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
rewrite G8. unfold PMSPA.pm_scr in M8b |- *.
apply (PMKA.shadow_zero_sub Mc (S - 26624) 3328); [exact M8a| exact M8b| lia| lia| lia|].
apply (PMKA.stksh_keepA L ar LBX FF S 26624 WR M0 Mc EKc wappR (S - 26624) 3328); [lia|lia|lia| exact M8a| lia| exact STKSH0].
Qed.
Lemma own_with_src : ltac2:(TCodec.tc2 tcn__PmABoK "J'QF'QH':';&QGr1%211&QDr2%211%611%93851'5'7%12;;%311&QE&R5r3%221;%411%513%D3721p0<1pVHG1pVBI1").
Proof. intros s src'. intros E. unfold PM.parser_own, PMSPA.with_src, PM.src_own. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]. rewrite E. reflexivity. Qed.
Lemma call_src : ltac2:(TCodec.tc2 tcn__PmABoK "VJ';'5&Q2%211&Ey5'S=yR0%211%5241'6y8%611%311p061'QF!p021p0B1p0C1p061p0<1p0C1&Q4%G11p019p0A1'QH'QIp01=p021p041p051p0C1p0I1p0J1&R3vR>&R<&QCv@vRJv>r5r4r3r2r1%<;;:987654321'3'R7'D&O'7%12QFQF%QF11&Q9r=r<r;r:r7r6%79654321DCB':&R8r9&S<&RCu1%211%42R21%7261%62R2L%:3R221&Q3%11Q0u2%:11%<2R:1%?2E1&REvR=+T0%3221%B2R>1%F3R>61u3%D11%F2RD1%I2Q01vM%K213%M3RE31u4%K11%M2RK1%Q02Q81%Q1272%Q33RK21r>u:%Q211%Q42S21%Q7241&R0vRO%22R41%Q92S51%Q=3S551'9&RB+1rI%3221+4%5231%7231&Q7r@r?rD%96432Q6@1rA%;21R0&R@%13S7R?R4&RAv<+H%3221&4%13T4T4RF%F231&8%13T7T7RI%9241+QH%;2:1%L231%N271p0?1pV@SG1&Q0rK%221RDrQ3rLr8&QDrQ0%211rO%7765RL2S<1S;&R4rQ1%711%341SA7S@&R5rQ2%221SErJ%S:9@2SF<S0>S51S4'R9&Q5%11T0&QJ%16T1S=S<QFS;S5v?%64T3421p081p0>1p0C1p0L1pVFTB1pVHTD1p4SI1pQ6U>1pV8SO1pQ>U51pQJU;1pV4T31rErCrB%C6TC3R0Q121%G4TDE1Bp061p0Q>1p0R11p0R41p0R:1p0RC1p0RN1p0S51p0S=1p0SH1p0SK1p0T71pU>U?1pUBV81p2TB1pULTF1pQ8V81pV:TI1pQFUO1pQHV51pV2TM1pUNTO1pVDUE1pVBV31pW0U21pU0U41pV>UB1pU@UL1pUHV11pV6VH1pV<VI1").
Proof using All. intros pc h args Wx res SPEC typed s sm e fx R Mc modelc LKc crc Ac X Wextra.
intros BS A1 RAX A2 A3 A4 A10 Hh ARG WXA WEX NEXT.
pose proof BS as (BI & RP & EC & HD & FSH & STEP0 & E0 & SD & CRL & CRK).
pose proof BI as (HHc & AMc & MRTc & IAc & ILKc & ASTKc & EKc & DKc & OWNc & SHDc).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & _ & NDF & _).
pose proof G as G'. destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
pose proof frame_geo as (Eop & Eois & Eov & Eoec & Eos).
pose proof FOK as ((rs & Hfb) & Fal).
pose proof ENT as (_ & _ & _ & _ & _ & ASTK0 & _). pose proof ASTK0 as (A16 & SLO & SHI & SPT & SDEF & SUP).
unfold SCR in *. change (PMSPA.pm_scr 7) with 26624 in *.
assert (HfbF : In (fb, 4, rs) FF') by (right; exact Hfb).
destruct (WF _ HfbF) as (Ff1 & Ff2 & _). cbn [ff_addr ff_class fst snd] in Ff1, Ff2. change (ff_bytes 4) with 1024 in Ff2.
unfold app_mem, FS_BYTES in FSAPP, FSCEIL, Ff1, Ff2. change (ff_bytes 0) with 64 in *.
assert (FAP : F + 64 <= fb \/ fb + 1024 <= F).
{ destruct (WF (F, 0, S - 128 + 32) (or_introl eq_refl)) as (_ & _ & _ & _ & _ & APF). cbn [ff_addr ff_class fst snd] in APF. change (ff_bytes 0) with 64 in APF.
assert (Iin : In (fb, 4, rs) (ff_remove F FF' ++ LKc)).
{ apply in_or_app. left. unfold FF'. cbn [ff_remove ff_addr]. rewrite Z.eqb_refl. exact Hfb. }
destruct (APF _ Iin) as [X0|X0]; cbn [ff_addr ff_class fst snd] in X0; change (ff_bytes 4) with 1024 in X0; [left| right]; lia. }
apply (SPEC fx R Mc modelc K LBX FF' LKc Ac crc (S - 128) X fb s str sm Wextra HHc AMc K0).
- exact (centry R Mc X h ASTKc EKc A1 RAX A2 A3 A4 ltac:(lia)).
- apply (PMAUAR.ffroomA_push 7 h FF LK0 LKc _ FRM ILKc); [exact NDF| lia].
- apply (PMAUAR.ffrsA_push FF S (S - 128) F 0 (S - 128 + 32) FRS); lia.
- exact (PMAUAR.frame_okA_push FF fb F 0 (S - 128 + 32) FOK).
- rewrite L5K.rl10. exact A10.
- exact ARG.
- exact WXA.
- exact PA.
- exact IA.
- exact BASE.
- exact INCS.
- intros fx' R' M' model' LK' Aw' src' sm' RP' PA' IA' STEP' RES' HP' MRT' ILK' IAW' AM' HH'.
set (Wc := PMSPA.W_src AD fb (PM.p_src s) ++ Wextra) in HP'.
set (qc := PM.sr_qc (PM.p_src s)) in *.
assert (QC : PM.sr_qc src' = qc) by (destruct STEP' as (X0 & _); exact X0).
assert (Iq : In (qc, PM.CHUNK) (PM.parser_own s)) by (unfold PM.parser_own, PM.src_own; left; reflexivity).
assert (IqL : In (qc, PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; exact Iq).
pose proof (WB _ IqL) as ((Bq0 & _ & _ & _ & Bq4 & Bq5) & _ & _ & _ & _ & BqF & _). cbn [fst snd] in Bq0, Bq4, Bq5, BqF.
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI, PM.CHUNK in Bq5, Bq4. destruct Bq5 as (_ & Bq5 & _).
destruct (BqF (F, 0, S - 128 + 32) ltac:(apply in_or_app; left; left; reflexivity)) as [QF|QF]; cbn [ff_addr ff_class fst snd] in QF; change (ff_bytes 0) with 64 in QF;
unfold PM.CHUNK in QF.
all: assert (WcR : forall rr a, In rr Wc -> L5.in_rng rr a ->
(fb + 488 + 256 <= a < fb + 488 + 296) \/ (fb + 96 + 40 <= a < fb + 96 + 48) \/ (fb + 96 + 152 <= a < fb + 96 + 156) \/ (qc <= a < qc + 16384)
\/ (F + 24 <= a < F + 56));
[ intros rr a Hin Hr; unfold Wc, PMSPA.W_src, PMSPA.W_srcf in Hin; rewrite Eos, Eois in Hin; cbn [app] in Hin;
destruct Hin as [<-|[<-|[<-|[<-|Hin]]]]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia| unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia
| unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia| unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold PM.CHUNK in Hr; lia| right; right; right; right; destruct (WEX rr Hin) as (X1 & X2); unfold L5.in_rng in Hr; lia] |].
all: assert (WAPPc : PMKA.wapp Wc);
[ intros rr Hin; unfold Wc, PMSPA.W_src, PMSPA.W_srcf in Hin; rewrite Eos, Eois in Hin; cbn [app] in Hin; unfold BIGSHADOW_LO, BIGSHADOW_HI;
pose proof FSAPP as (FA0 & FA1 & FA2); unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1;
destruct Hin as [<-|[<-|[<-|[<-|Hin]]]]; cbn [fst snd]; unfold PM.CHUNK;
[destruct FA1; lia| destruct FA1; lia| destruct FA1; lia| destruct Bq5; lia| ];
destruct (WEX rr Hin) as (X1 & X2); destruct FA1; lia |].
all: pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHc) as FRB'; pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHc) as BRB.
all: assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by (intros f Hf; apply FRB'; right; exact Hf).
all: pose proof (L5SAR.ek_callee L ar (PM.parser_own s ++ LBX) [] FF [(F, 0, S - 128 + 32)] S 26624 (S - 128) (PMSPA.pm_scr h) Wc Wc Mc M' HP'
ltac:(unfold PMSPA.pm_scr; lia) ltac:(lia) (fun a _ X => X)) as EKcc.
all: assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n)
by (intros a n X1 X2; exists (fb, 4, rs); split; [exact Hfb|]; cbn [ff_addr ff_class fst snd]; change (ff_bytes 4) with 1024; lia).
all: assert (OUTf : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> (a + n <= fb + 488 + 256 \/ fb + 488 + 296 <= a) -> (a + n <= fb + 96 + 40 \/ fb + 96 + 48 <= a) ->
(a + n <= fb + 96 + 152 \/ fb + 96 + 156 <= a) -> forall i, a <= i < a + n -> L5.outside Wc i);
[ intros a n X1 X2 X3 X4 X5 i Hi rr Hin Hr; destruct (WcR rr i Hin Hr) as [Y|[Y|[Y|[Y|Y]]]]; [lia| lia| lia| |];
[ destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ qc 16384 a n HHc IqL (PMAUAR.aobjA_push FF a n _ (AOF a n X1 X2))) as [Z|Z]; lia
| destruct FAP; lia ] |].
all: assert (OUTB : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> q <> qc -> forall i, q <= i < q + m -> L5.outside Wc i);
[ intros q m Hq Hne i Hi rr Hin Hr; destruct (WcR rr i Hin Hr) as [Y|[Y|[Y|[Y|Y]]]];
[ destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m (fb + 488 + 256) 40 HHc Hq (PMAUAR.aobjA_push FF (fb + 488 + 256) 40 _ (AOF (fb + 488 + 256) 40 ltac:(lia) ltac:(lia)))) as [Z|Z]; lia
| destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m (fb + 96 + 40) 8 HHc Hq (PMAUAR.aobjA_push FF (fb + 96 + 40) 8 _ (AOF (fb + 96 + 40) 8 ltac:(lia) ltac:(lia)))) as [Z|Z]; lia
| destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m (fb + 96 + 152) 4 HHc Hq (PMAUAR.aobjA_push FF (fb + 96 + 152) 4 _ (AOF (fb + 96 + 152) 4 ltac:(lia) ltac:(lia)))) as [Z|Z]; lia
| destruct (PMASK.blk_apart L ar C HI HIok _ _ _ _ _ _ _ q m qc 16384 HHc Hq IqL Hne) as [Z|Z]; lia
| destruct (WB _ Hq) as (_ & _ & _ & _ & _ & QFF & _); cbn [fst snd] in QFF;
destruct (QFF (F, 0, S - 128 + 32) ltac:(apply in_or_app; left; left; reflexivity)) as [Z|Z]; cbn [ff_addr ff_class fst snd] in Z; change (ff_bytes 0) with 64 in Z; lia ] |].
all: pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HHc) as FSI.
all: pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ _ _ HHc IqL) as Bqi; unfold PM.CHUNK in Bqi.
all: assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; lia).
all: assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; lia).
all: pose proof FSAPP as (FA0 & FA1 & FA2); unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
all: unfold FS_BYTES in FS2.
all: assert (BI' : binv' (PM.parser_own (PMSPA.with_src s src')) M' model' LK' crc Aw');
[ unfold binv'; rewrite (own_with_src s src' QC);
apply (PMAUK.binv_callee L ar C HI HIok M0 model0 LBX FF LK0 Aw0 S 26624 (S - 128) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G
WR WR (PM.parser_own s) (PM.parser_own s) (PM.parser_own s) Mc modelc LKc crc Ac M' model' LK' crc Aw' (PMSPA.pm_scr h) Wc BI HP' HH' AM' MRT' IAW' ILK');
[ unfold PMSPA.pm_scr; lia | unfold PMSPA.pm_scr; lia | | | intros a X0; exact X0 ];
[ intros rr a Hin Hr; unfold ocell; change (ff_bytes 0 / 8) with 8; unfold SB;
destruct (WcR rr a Hin Hr) as [X0|[X0|[X0|[X0|X0]]]]; (split; [lia|]); first [destruct FA1; lia | destruct Bq5; lia]
| intros a Hc Ho rr Hin Hr; destruct (WcR rr a Hin Hr) as [X0|[X0|[X0|[X0|X0]]]];
[ apply (Ho (PMSPA.o_src AD fb + 256, 40)); [unfold WR, PMSPA.W_run, PMSPA.W_srcf; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]
| apply (Ho (PMSPA.o_is AD fb + 40, 8)); [unfold WR, PMSPA.W_run, PMSPA.W_srcf; right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]
| apply (Ho (PMSPA.o_is AD fb + 152, 4)); [unfold WR, PMSPA.W_run, PMSPA.W_srcf; right; right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]
| exact (PMARS1.own_not_aclient L ar C HI HIok (PM.parser_own s) LBX FF' LKc crc Ac Mc _ qc 16384 a S 26624 HHc Iq X0 (L5SAR.aclient_cons L ar LBX FF _ S 26624 a Hc))
| apply (NCF a); [left; lia| exact Hc] ] ] |].
all: assert (OUTimg : forall a, 65536 <= a < 6885376 -> L5.outside Wc a)
by (intros a Ha rr Hin Hr; destruct (WcR rr a Hin Hr) as [X0|[X0|[X0|[X0|X0]]]]; [lia| lia| lia| destruct Bqi; lia| lia]).
all: assert (RUN' : PMSPA.run_pre RSEGS AD PMA.AAD M' fb (PMSPA.with_src s src') str sm' e);
[ split; [exact PA'|]; split; [exact IA'|];
split; [apply (PMKA.visitor_keepA RSEGS AD L ar _ FF S 26624 Wc Mc M' EKcc WAPPc FRB (PMSPA.o_v AD fb) (AOF (PMSPA.o_v AD fb) 8 ltac:(lia) ltac:(lia))); [apply OUTf; lia| exact VIS]|];
split; [apply (PMKA.u64_keepA RSEGS L ar _ FF S 26624 Wc Mc M' EKcc WAPPc FRB (PMSPA.o_p AD fb + 384) (PMSPA.o_v AD fb) (AOF (PMSPA.o_p AD fb + 384) 8 ltac:(lia) ltac:(lia))); [apply OUTf; lia| exact VREF]|];
split; [apply (PMASK.base_keep L ar C LY _ FF S 26624 Wc Mc M' EKcc OUTimg BASE)|];
split; [ apply (PMKA.err_okA_keep RSEGS AD PMA.AAD L ar _ FF S 26624 Wc Mc M' EKcc e PMA.addrs_wf_A); [| exact ERR];
intros a D; pose proof (PMASK.dep_img a D) as DI; rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa); split; [lia|];
split; [exact (PMA.ly_static L C LY a D)| apply OUTimg; lia] |];
exact TBOK |].
all: assert (EC' : PMSPA.ec_at RSEGS M' oec 0 cat)
by (apply (PMKA.ec_keepA RSEGS L ar _ FF S 26624 Wc Mc M' EKcc WAPPc FRB oec 0 cat (AOF oec 16 ltac:(unfold oec; lia) ltac:(unfold oec; lia))); [apply OUTf; unfold oec; lia| exact EC]).
all: assert (KPa : forall a, 0 <= a < 2 ^ 64 -> aclient L ar (PM.parser_own s ++ LBX) FF' (S - 128) (PMSPA.pm_scr h) a -> L5.outside Wc a -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a))
by (intros a X1 X2 X3; apply (proj1 HP'); split; [exact X1| split; assumption]).
all: assert (KPF : forall a, F <= a < F + 24 -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a));
[ intros a Ha; apply KPa; [lia| apply (L5SAR.fframe_client L ar _ FF' _ _ F 0 (S - 128 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; lia]|];
intros rr Hin Hr; destruct (WcR rr a Hin Hr) as [X0|[X0|[X0|[X0|X0]]]]; [destruct FAP; lia| destruct FAP; lia| destruct FAP; lia| lia| lia] |].
all: assert (KPS : forall a, S - 128 <= a < S - 120 -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a));
[ intros a Ha; apply KPa; [lia| apply (L5SAR.stack_client L ar _ FF' _ _ a); lia|];
intros rr Hin Hr; destruct (WcR rr a Hin Hr) as [X0|[X0|[X0|[X0|X0]]]]; lia |].
all: assert (KPSH : forall x, F / 8 + SB <= x < F / 8 + SB + 8 -> M' (Z_to_bv 64 x) = Mc (Z_to_bv 64 x));
[ intros x Hx; apply KPa; [unfold SB in Hx; lia| apply (L5SAR.fframe_shadow_client L ar _ FF' _ _ F 0 (S - 128 + 32)); [left; reflexivity|]|];
[ change (ff_bytes 0) with 64; unfold in_shadow_of, HeapIfaceA.S; rewrite (proj1 (proj2 F8)); change (ff_bytes 0) with 64 in F8; unfold SB in *; lia
| apply (PMKA.wapp_outside_shadow Wc x WAPPc); unfold BIGSHADOW_LO, BIGSHADOW_HI, SB in *; lia ] |].
all: apply (NEXT fx' R' M' model' LK' Aw' src' sm' RP' RES' STEP').
all: split; [exact BI'|]; split; [exact RUN'|]; split; [exact EC'|].
all: split;
[ pose proof HD as (H0 & H8 & H16 & H128); split; [apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPF; lia| lia| lia| exact H0]|];
split; [apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPF; lia| lia| lia| exact H8]|];
split; [apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPF; lia| lia| lia| exact H16]|];
apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPS; lia| lia| lia| exact H128] |].
all: split;
[ pose proof FSH as (Z0 & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7); unfold SB in KPSH;
repeat split; (apply (L5C.u8_at_agree RSEGS Mc M'); [intros i Hi; apply KPSH; lia| lia| lia| assumption]) |].
all: split; [exact (PMAPAR.src_step_transA _ _ _ _ _ _ STEP0 STEP')|].
all: split; [exact E0|].
all: split; [exact SD|].
all: split; [exact CRL| exact CRK].
Qed.
Definition bste (typed : bool) (s : PM.pst) (sm : PM.strm) (v : Z) (Mc : word -> option byte) (modelc : Model) (LKc : list fframe) (crc : credit) (Ac : list (Z * Z)) : Prop :=
binv' (PM.parser_own s) Mc modelc LKc crc Ac
/\ PMSPA.run_pre RSEGS AD PMA.AAD Mc fb s str sm true /\ PMSPA.ec_at RSEGS Mc oec v (pa_errcat_obj AD) /\ 1 <= v <= 64
/\ hdr Mc /\ fsh typed Mc
/\ PMSPA.src_step (PM.p_src s0) (PM.p_src s) sm0 sm /\ sdl s
/\ PMSPA.credit_le (pot s) crc /\ PMSPA.credit_keep cr0 crc (pot s0) (pot s).
Lemma call_mkec : ltac2:(TCodec.tc2 tcn__PmABoK "TG'3'QF'QI'R7&Ey5'S=yR0%211%5241'6y8%611%311p061'D'5&Q2%211&O'7';%2211%711&Q9r=r<r;r:r7r6r5r4r3%:9987654321':&R8r9&S<&RCu1%211%42Q51%7261%62Q5;%:3Q521&Q3%11?u2%:11%<2Q=1%?2H1&REvR=+T0%3221%B2QA1%F3QA61u3%D11%F2QG1%I2Q31vM%K213%M3QH31u4%K11%M2QN1%Q02Q;1%Q1272%Q33QN21r>u:%Q211%Q42R51%Q7241&Q@%Q72R61%Q;3R631r?u;%Q:11%Q<2R=1%Q?241r8%Q?2R>1%QC3R>31'9&RB+1%221QE+R0%42QG1%6231&Q0rG%221R1&Q:rMrLrKrArDr2%796543R9R8R721'R9&R<&Q5vR>%211&QJrC%266LRC1RBRAv?%948521p0;1p0D1p4RN1pQ6S41pV8S81pQ>S:1pQJS@1pV4SG1rB+ej[Dr@%@6D?32I1%F4EB1>p061p0Q41p0Q<1p0QE1p0QN1p0R51p0R=1p0RH1p0RK1p0S71pW2SE1pUBSF1p2SE1pULSJ1pQ8SL1pV:T01pQFT21pQHT81pV2T?1pUNTC1pVDTB1pVBTD1pW0TF1").
Proof using All. intros typed s sm e fx R Mc modelc LKc crc Ac X v.
intros BS A1 RAX A2 A3 A4 A10 A11 Hv NEXT.
pose proof BS as (BI & RP & EC & HD & FSH & STEP0 & E0 & SD & CRL & CRK).
pose proof BI as (HHc & AMc & MRTc & IAc & ILKc & ASTKc & EKc & DKc & OWNc & SHDc).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & _ & NDF & _).
pose proof G as G'. destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
pose proof frame_geo as (Eop & Eois & Eov & Eoec & Eos).
pose proof FOK as ((rs & Hfb) & Fal).
pose proof ENT as (_ & _ & _ & _ & _ & ASTK0 & _). pose proof ASTK0 as (A16 & SLO & SHI & SPT & SDEF & SUP).
unfold SCR in *. change (PMSPA.pm_scr 7) with 26624 in *.
assert (HfbF : In (fb, 4, rs) FF') by (right; exact Hfb).
destruct (WF _ HfbF) as (Ff1 & Ff2 & _). cbn [ff_addr ff_class fst snd] in Ff1, Ff2. change (ff_bytes 4) with 1024 in Ff2.
unfold app_mem, FS_BYTES in FSAPP, FSCEIL, Ff1, Ff2, FS2. change (ff_bytes 0) with 64 in *.
assert (FAP : F + 64 <= fb \/ fb + 1024 <= F).
{ destruct (WF (F, 0, S - 128 + 32) (or_introl eq_refl)) as (_ & _ & _ & _ & _ & APF). cbn [ff_addr ff_class fst snd] in APF. change (ff_bytes 0) with 64 in APF.
assert (Iin : In (fb, 4, rs) (ff_remove F FF' ++ LKc)).
{ apply in_or_app. left. unfold FF'. cbn [ff_remove ff_addr]. rewrite Z.eqb_refl. exact Hfb. }
destruct (APF _ Iin) as [X0|X0]; cbn [ff_addr ff_class fst snd] in X0; change (ff_bytes 4) with 1024 in X0; [left| right]; lia. }
assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n)
by (intros a n X1 X2; exists (fb, 4, rs); split; [exact Hfb|]; cbn [ff_addr ff_class fst snd]; change (ff_bytes 4) with 1024; lia).
pose proof EC as (_ & _ & ECD & ECA).
unfold PMA.make_ec_spec, PMSPA.make_ec_spec in MKE. cbn [pa_make_ec PMA.AD ADDR_A] in MKE.
apply (MKE fx R Mc modelc K (PM.parser_own s ++ LBX) FF' LKc Ac crc oec v (S - 128) X e HHc AMc K0).
{ exact (centry R Mc X 1 ASTKc EKc A1 RAX A2 A3 A4 ltac:(lia)). }
{ apply (PMAUAR.ffroomA_push 7 1 FF LK0 LKc _ FRM ILKc); [exact NDF| lia]. }
{ apply (PMAUAR.ffrsA_push FF S (S - 128) F 0 (S - 128 + 32) FRS); lia. }
{ rewrite L5K.rl10. exact A10. }
{ rewrite L5SAR.r11. exact A11. }
{ exact Hv. }
{ apply PMAUAR.aobjA_push. apply AOF; unfold oec; lia. }
{ unfold oec. rewrite Eoec. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 992) with ((128 * (fb / 1024) + 124) * 8) by lia. apply Z_mod_mult. }
{ exact ECD. }
{ exact ECA. }
{ exact BASE. }
{ exact ERR. }
intros fx' R' M' model' LK' Aw' RP' EC' ERR' HP' MRT' ILK' IAW' AM' HH'.
change (PMSPA.pm_scr 1) with 14336 in HP'.
set (Wc := (oec, 16) :: (if e then [] else PMSPA.err_W AD)) in HP'.
assert (WcR : forall rr a, In rr Wc -> L5.in_rng rr a -> (fb + 992 <= a < fb + 1008) \/ (0x66d380 <= a < 0x68eff0)).
{ intros rr a Hin Hr. unfold Wc in Hin. destruct Hin as [<-|Hin]; [left; unfold L5.in_rng, oec in Hr; cbn [fst snd] in Hr; lia|]. right. destruct e; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
assert (WcR2 : forall rr a, In rr Wc -> L5.in_rng rr a -> (fb + 992 <= a < fb + 1008) \/ (0x66d380 <= a < 0x66d382) \/ (0x68edd0 <= a < 0x68eff0)).
{ intros rr a Hin Hr. unfold Wc in Hin. destruct Hin as [<-|Hin]; [left; unfold L5.in_rng, oec in Hr; cbn [fst snd] in Hr; lia|]. right. destruct e; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; [left| right]; lia. }
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHc) as FRB'. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHc) as BRB.
assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by (intros f Hf; apply FRB'; right; exact Hf).
pose proof (L5SAR.ek_callee L ar (PM.parser_own s ++ LBX) [] FF [(F, 0, S - 128 + 32)] S 26624 (S - 128) 14336 Wc Wc Mc M' HP' ltac:(lia) ltac:(lia) (fun a _ X => X)) as EKcc.
pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HHc) as FSI.
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
assert (WAPPc : PMKA.wapp Wc).
{ intros rr Hin. unfold Wc in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|Hin]; cbn [fst snd].
- unfold oec. destruct FA1; lia.
- destruct e; [destruct Hin|]. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; lia. }
assert (OUTf : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> (a + n <= fb + 992 \/ fb + 1008 <= a) -> forall i, a <= i < a + n -> L5.outside Wc i).
{ intros a n X1 X2 X3 i Hi rr Hin Hr. destruct (WcR rr i Hin Hr) as [Y|Y]; lia. }
assert (OUTB : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> forall i, q <= i < q + m -> L5.outside Wc i).
{ intros q m Hq i Hi rr Hin Hr. destruct (WcR rr i Hin Hr) as [Y|Y].
- destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m oec 16 HHc Hq (PMAUAR.aobjA_push FF oec 16 _ (AOF oec 16 ltac:(unfold oec; lia) ltac:(unfold oec; lia)))) as [Z|Z];
unfold oec in Z; lia.
- destruct (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HHc Hq) as [Z|Z]; lia. }
apply (NEXT fx' R' M' model' LK' Aw' RP').
split.
{ unfold binv'.
apply (PMAUK.binv_callee L ar C HI HIok M0 model0 LBX FF LK0 Aw0 S 26624 (S - 128) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G
WR WR (PM.parser_own s) (PM.parser_own s) (PM.parser_own s) Mc modelc LKc crc Ac M' model' LK' crc Aw' 14336 Wc BI HP' HH' AM' MRT' IAW' ILK');
[lia| lia| | | intros a X0; exact X0].
- intros rr a Hin Hr. unfold ocell. change (ff_bytes 0 / 8) with 8. unfold SB.
assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; lia). assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; lia).
destruct (WcR rr a Hin Hr) as [X0|X0]; (split; [lia|]); [destruct FA1; lia| lia].
- intros a Hc Ho rr Hin Hr. destruct (WcR rr a Hin Hr) as [X0|X0].
+ apply (Ho (PMSPA.o_ec AD fb, 16)); [unfold WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W; cbn [app]; do 6 right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
+ unfold Wc in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng, oec in Hr; cbn [fst snd] in Hr; lia|]. destruct e; [destruct Hin|].
unfold PMSPA.err_W in Hin. destruct Hin as [<-|[<-|[]]].
* apply (Ho _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))); exact Hr.
* apply (Ho _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))); exact Hr. }
assert (KPa : forall a, 0 <= a < 2 ^ 64 -> aclient L ar (PM.parser_own s ++ LBX) FF' (S - 128) 14336 a -> L5.outside Wc a -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a))
by (intros a X1 X2 X3; apply (proj1 HP'); split; [exact X1| split; assumption]).
assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; lia). assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; lia).
split.
{ split; [apply (PMKA.parser_keepA RSEGS AD L ar _ FF S 26624 Wc Mc M' EKcc WAPPc FRB BRB _ _ _ (AOF (PMSPA.o_p AD fb) 384 ltac:(lia) ltac:(lia)));
[apply incl_appl, incl_refl| apply OUTf; lia| intros i Hi; apply (OUTB (PM.sr_qc (PM.p_src s)) PM.CHUNK); [apply in_or_app; left; left; reflexivity| exact Hi]
| intros i Hi; apply (OUTB (PM.p_b s) (32 * 2 ^ PM.p_k s)); [apply in_or_app; left; right; left; reflexivity| exact Hi]
| intros c0 n0 p0 Etb i Hi; apply (OUTB p0 c0); [apply in_or_app; left; unfold PM.parser_own; rewrite Etb; right; right; left; reflexivity| exact Hi]
| exact PA]|].
split; [apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 26624 Wc Mc M' EKcc WAPPc FRB BRB _ str sm (AOF (PMSPA.o_is AD fb) 272 ltac:(lia) ltac:(lia)));
[intros x Hx; apply in_or_app; right; apply INCS; exact Hx| apply OUTf; lia
| intros c0 n0 p0 Etb i Hi; apply (OUTB p0 c0); [apply in_or_app; right; apply INCS; rewrite Etb; left; reflexivity| exact Hi]
| exact IA]|].
split; [apply (PMKA.visitor_keepA RSEGS AD L ar _ FF S 26624 Wc Mc M' EKcc WAPPc FRB (PMSPA.o_v AD fb) (AOF (PMSPA.o_v AD fb) 8 ltac:(lia) ltac:(lia))); [apply OUTf; lia| exact VIS]|].
split; [apply (PMKA.u64_keepA RSEGS L ar _ FF S 26624 Wc Mc M' EKcc WAPPc FRB (PMSPA.o_p AD fb + 384) (PMSPA.o_v AD fb) (AOF (PMSPA.o_p AD fb + 384) 8 ltac:(lia) ltac:(lia)));
[apply OUTf; lia| exact VREF]|].
split; [apply (PMAPAR.base_keepW L ar C LY _ FF S 26624 Wc Mc M' EKcc); [| | | | exact BASE];
first [ intros a Ha rr Hin Hr; destruct (WcR2 rr a Hin Hr) as [X0|[X0|X0]]; lia | intros rr Hin Hr; destruct (WcR2 rr _ Hin Hr) as [X0|[X0|X0]]; lia ]|].
split; [exact ERR'| exact TBOK]. }
split; [exact EC'|]. split; [exact Hv|].
split.
{ pose proof HD as (H0 & H8 & H16 & H128).
assert (KPF : forall a, F <= a < F + 24 -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
{ intros a Ha. apply KPa; [lia| apply (L5SAR.fframe_client L ar _ FF' _ _ F 0 (S - 128 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; lia]|].
intros rr Hin Hr. destruct (WcR rr a Hin Hr) as [X0|X0]; [destruct FAP; lia| lia]. }
assert (KPS : forall a, S - 128 <= a < S - 120 -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
{ intros a Ha. apply KPa; [lia| apply (L5SAR.stack_client L ar _ FF' _ _ a); lia|]. intros rr Hin Hr. destruct (WcR rr a Hin Hr) as [X0|X0]; lia. }
split; [apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPF; lia| lia| lia| exact H0]|].
split; [apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPF; lia| lia| lia| exact H8]|].
split; [apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPF; lia| lia| lia| exact H16]|].
apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPS; lia| lia| lia| exact H128]. }
split.
{ assert (KPSH : forall x, F / 8 + 2147450880 <= x < F / 8 + 2147450880 + 8 -> M' (Z_to_bv 64 x) = Mc (Z_to_bv 64 x)).
{ intros x Hx. apply KPa; [lia| apply (L5SAR.fframe_shadow_client L ar _ FF' _ _ F 0 (S - 128 + 32)); [left; reflexivity|]|].
- change (ff_bytes 0) with 64. unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). change (ff_bytes 0) with 64 in F8. unfold SB in *. lia.
- apply (PMKA.wapp_outside_shadow Wc x WAPPc). unfold BIGSHADOW_LO, BIGSHADOW_HI. lia. }
pose proof FSH as (Z0 & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7).
repeat split; (apply (L5C.u8_at_agree RSEGS Mc M'); [intros i Hi; apply KPSH; lia| lia| lia| assumption]). }
split; [exact STEP0|]. split; [exact SD|]. split; [exact CRL| exact CRK].
Qed.
End Frame.
End Call.
End WithHeap.
End PMABOK.
