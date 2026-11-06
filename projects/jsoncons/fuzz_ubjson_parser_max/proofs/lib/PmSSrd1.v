(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmKeep PmKitS PmFrame PmParSpecs PmParSpecsS PmParKit PmSReset PmTxtSpecs PmTxtKit2 PmSSrdP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSSrd1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParSpecs.PMPS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSSrd1.PMSSR1.WithHeap.Call."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmTxtKit2.PMTK2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.Sorting.Permutation."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."], [["0B"; "0B'"; "1app"; "1bool"; "1fst"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "2or"; "3map"]; ["4Z"; "0HI"; "0K"; "0KS"; "0L"; "0LB"; "0LBX"; "5Model"; "5VmMaps"; "6bvmap"; "0M"; "0M'"; "0OWN"; "0R"; "0R'"; "0R0"]; ["7credit"; "7hi_heap"; "7hl_img_hi"; "7hl_img_lo"; "7hl_sptop"; "7regs_preserved"; "8hpres"; "8stk"; ":outside"; ":ra_ok"; ":range"; "9SCFG"; ";ADDR_S"; "<CHUNK"; "<p_b"; "<p_k"]; ["<p_src"; "<p_tb"; "<p_tg"; "<parser_own"; "<pst"; "<sm_eg"; "<sm_g"; "<sm_st"; "<sr_qc"; "<sr_rem"; "<src_own"; "<srcst"; "<strm"; "<unread"; "<vec_own"; "<vs_cap"]; ["<vs_own"; "<vs_size"; "<vstr"; "=with_src"; ">W0"; ">acct"; ">kept7"; ">memrel"; ">saves8"; ">state_ok"; ">tbdst"; "?W_src"; "?cfg"; "?consumed"; "?src_step"; "@base_ok"]; ["Aek"; "AinW"; "Bwith_tb"; "CFPState"; "Cgetr"; "Dsrealizes"; "Eloaded_segments"; "0S"; "0SCFG_P"; "Feqb"; "GIn"; "Gexistsb"; "Gforallb"; "HPermutation"; "Iadd"; "Ile"]; ["Ilt"; "Iof_nat"; "Ipow"; "Isub"; "0VM"; "0W"; "0W'"; "0X"; "0a"; "0cr"; "0cr'"; "0d"; "0fb"; "0fx"; "0fx'"; "0k"]; ["0l"; "0l'"; "0len"; "0m"; "0m'"; "0model"; "0model'"; "0nn"; "0p"; "0s"; "0scr'"; "0sm"; "0sm'"; "0src"; "0src'"; "JNoDup"]; ["KZ_to_bv"; "Kbv"; "Kbv_unsigned"; "0tb"; "0tb'"; "0tg"; "0tg'"; "0w"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMSSR1.
Import PMS.
Local Ltac lia := PMK.alia.
Local Ltac cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
Lemma sub_in : ltac2:(TCodec.tc2 tcn__PmSSrd1 "J'5'6%211'<'3&RL&RK&RIr1%211r3%53:21qW0;1%83<15(:%<3;21&RJ%13@97r2r5%43C21p041pW0E1p081pW2F1pQ8G1").
Proof. intros KS l. exact (PMSRS.sub_in KS l). Qed.
Lemma nodup_perm : ltac2:(TCodec.tc2 tcn__PmSSrd1 "D'5'9'@%2211%411'RMr2r1%33521'SO&?&4%12::r3%44;<21%62=1p011p091pW4>1pW2?1").
Proof. intros l l'.
intros P ND. apply NoDup_ListNoDup. apply NoDup_ListNoDup in ND.
eapply Permutation.Permutation_NoDup; [|exact ND]. apply Permutation.Permutation_map. exact P.
Qed.
Lemma perm_tb : ltac2:(TCodec.tc2 tcn__PmSSrd1 "QE'QD'5'9'@%2211%411&Q0'T1yR0%211'7y8%511%311p051'H&Q1vA&2&QCr5%211r4%53C21r3r2r1%;5:4321&R0&QAr6%211%411&QJ&Q@%115%311&QN&Q>%119&Q?%11;%5231%I3Q71G%J3Q881%K3Q9=1%N5M1HFEp0D1pV:Q11pQFQ31pVDQ<1pQ<Q>1pWDQD1").
Proof. intros s LB cr M VM.
intros HH. apply (hio_perm L SCFG HI HIok _ _ cr M VM HH).
- intros b. unfold PM.parser_own. rewrite !in_app_iff. tauto.
- apply (nodup_perm (PM.parser_own s ++ LB)); [|exact (PMPK.heap_nodup L HI HIok _ _ _ _ HH)].
unfold PM.parser_own. set (X := PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s)).
replace ((PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ PM.vs_own (PM.p_tb s)) ++ LB) with (X ++ PM.vs_own (PM.p_tb s) ++ LB)
by (unfold X; rewrite <- !app_assoc; reflexivity).
replace (PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ LB) with (X ++ LB) by (unfold X; rewrite <- !app_assoc; reflexivity).
apply Permutation.Permutation_app_swap_app.
Qed.
Lemma perm_tb_back : ltac2:(TCodec.tc2 tcn__PmSSrd1 "QJ'QD'R2'@'5'9%1233%311&Q0'T1yR0%211'7y8%511%311p051'H&Q1vA&2&R0r6%211&QJ&Q@r7%211%411&QN&Q>%115&Q?%117%5231r4%@3N21%A3O91%B3Q0?1r3r2r1%H5G4321&QC&RBr8%231DH%411r5%M3Q;21%Q05O1?;:p091pV:Q31pQFQ51pVDQ>1pQ<Q@1pX<QE1pX8QG1pWDQI1").
Proof. intros s tb tg LB cr M VM.
intros HH. apply (hio_perm L SCFG HI HIok _ _ cr M VM HH).
- intros b. unfold PM.parser_own, PMTK2.with_tb. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]. rewrite !in_app_iff. tauto.
- apply (nodup_perm (PM.vs_own tb ++ (PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ LB)));
[|exact (PMPK.heap_nodup L HI HIok _ _ _ _ HH)].
unfold PM.parser_own, PMTK2.with_tb. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb].
set (X := PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s)).
replace ((PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ PM.vs_own tb) ++ LB) with (X ++ PM.vs_own tb ++ LB)
by (unfold X; rewrite <- !app_assoc; reflexivity).
replace (PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ LB) with (X ++ LB) by (unfold X; rewrite <- !app_assoc; reflexivity).
apply Permutation.Permutation_app_swap_app.
Qed.
Lemma own_apart : ltac2:(TCodec.tc2 tcn__PmSSrd1 "R:'QD'5'9'@%2211%411&Q0'T1yR0%211'7y8%511%311p051'H&Q1vA&2&QCr5%211r4%53C21r3r2r1%;5:4321&RJ(8%14KK54r8%=11%53M31';&RO&RN%12=<&S3&Q4vD%211+XPPP0%5221%9271'>&Q3%117%=2;1&Q2%11:%@21K%7241r:%J3QBH1r6%D21Q4%F21Q1%G2E3%>221p061pW:QJ1p4QK1%M2;1%N2D1p0Q01pW8QO1p2R01p0Q91pV:QF1pQFQH1pVDR11pQ<R31pWDR91").
Proof. intros s LB cr M VM.
intros HH B m Hin. assert (BR : PMFR.brange L (PM.parser_own s ++ LB)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
destruct (BR B m (in_or_app _ _ _ (or_introl Hin))) as (Z0 & Z1 & Z4). split; [exact Z4|]. split; [exact Z1|]. intros B' m' Hin'.
assert (NE : B <> B') by (apply (PMPK.fst_neq_app (PM.parser_own s) LB B m B' m' (PMPK.heap_nodup L HI HIok _ _ _ _ HH) Hin Hin')).
exact (PMPK.blocks_apart_heap L HI HIok _ cr M _ B m B' m' HH (in_or_app _ _ _ (or_introl Hin)) (in_or_app _ _ _ (or_intror Hin')) NE).
Qed.
Lemma outside_own : ltac2:(TCodec.tc2 tcn__PmSSrd1 "Q7'5'9'@%2211%411&Q8r3r1%3221'>&2r4%23916r2%9221'=';&RJ(8%14AA6<r5%43B21&RO%12:<&S0&RN%12=C%32@1%<251%=281qW8L1%@2M1q2N1%B2O1%I2D1p0K1pVBQ21pQJQ11pV<Q21").
Proof. intros W OWN a.
intros O. induction OWN as [|(B, m) OWN IH]; [left; rewrite app_nil_r; exact O|].
destruct (PMK.rng_dec a B (B + m)) as [I|NI]; [right; exists B, m; split; [left; reflexivity| exact I]|].
destruct IH as [O'|(B' & m' & Hin & Ha)]; [left| right; exists B', m'; split; [right; exact Hin| exact Ha]].
intros r Hr. apply in_app_or in Hr. destruct Hr as [Hr|[<-|Hr]]; [apply O; exact Hr| unfold L5.in_rng; cbn [fst snd]; exact NI| apply O'; apply in_or_app; right; exact Hr].
Qed.
Lemma own_with_src : ltac2:(TCodec.tc2 tcn__PmSSrd1 "J'QD'QK'<'@&QHr1%211&Q@r2%211%611%93851'5'9%12;;%311&QC&R3r3%221;%411%513%D3721p0<1pWNG1pWDI1").
Proof. intros s src'. intros E. unfold PM.parser_own, PMPS.with_src, PM.src_own. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]. rewrite E. reflexivity. Qed.
Lemma with_src_id : ltac2:(TCodec.tc2 tcn__PmSSrd1 "9'QD'<&R3r1&Q@%112%4231%63714pWD81").
Proof. intros s. destruct s; reflexivity. Qed.
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (cr0 : credit).
Variables (S r fb len : Z) (s0 : PM.pst) (str : PM.vstr) (sm0 : PM.strm).
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis K0 : K [].
Hypothesis FR1 : S <= fb.
Hypothesis FR2 : fb + 752 <= hl_sptop L.
Hypothesis FR3 : fb mod 16 = 0.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UNS0 : PM.vs_size (PM.p_tb s0) + PM.unread (PM.p_src s0) sm0 < 2 ^ 26.
Hypothesis RSZ : PMS.str_resize_spec L HI.
Hypothesis SRD : PMPSS.src_read_spec L HI.
Hypothesis FBT : PMTXS.fill_buffer_tb_spec RSEGS AD L HI.
Definition W0 : list L5.range := PMSP.W_srcf AD fb ++ [(PMSP.o_tb AD fb, 24)].
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (d : Z),
regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
PMSP.consumed (PM.p_src s0) (PM.p_src s') sm0 sm' = d -> PM.vs_size (PM.p_tb s') = PM.vs_size (PM.p_tb s0) + d ->
PM.parser_at RSEGS AD T3 T4 M' (PMSP.o_p AD fb) (PMSP.o_is AD fb) s' -> PM.iss_at RSEGS AD T3 M' (PMSP.o_is AD fb) str sm' ->
PM.tb_ok (PM.p_tb s') (PM.p_tg s') ->
PM.p_more s' = PM.p_more s0 -> PM.p_done s' = PM.p_done s0 -> PM.p_depth s' = PM.p_depth s0 ->
PM.p_b s' = PM.p_b s0 -> PM.p_k s' = PM.p_k s0 -> PM.p_stk s' = PM.p_stk s0 ->
PMSP.src_step (PM.p_src s0) (PM.p_src s') sm0 sm' ->
L5C.hpres L LBX S (PMSP.pm_scr 5) W0 M0 M' ->
PMSP.credit_keep cr0 cr' (PM.pot_text L (PM.p_tb s0) (PM.p_tg s0)) (PM.pot_text L (PM.p_tb s') (PM.p_tg s')) ->
model_but_vm model0 model' -> hi_heap HI (PM.parser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.
Definition saves8 (M : word -> option byte) : Prop :=
L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
/\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
/\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
/\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22))).
Definition kept7 (R : bvmap 5 word) : Prop := forall x, In x [3; 4; 23; 24; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).
Definition memrel (M : word -> option byte) : Prop :=
PMK.ek L LBX S 22528 W0 M0 M /\ PMK.dk L LBX S 22528 M0 M /\ L5C.stk (hl_sptop L) M S 22528.
Definition fields_eq (s : PM.pst) : Prop :=
PM.p_more s = PM.p_more s0 /\ PM.p_done s = PM.p_done s0 /\ PM.p_depth s = PM.p_depth s0 /\
PM.p_b s = PM.p_b s0 /\ PM.p_k s = PM.p_k s0 /\ PM.p_stk s = PM.p_stk s0.
Definition acct (s : PM.pst) (sm : PM.strm) (w : Z) : Prop :=
PMSP.consumed (PM.p_src s0) (PM.p_src s) sm0 sm = len - w /\ PM.vs_size (PM.p_tb s) = PM.vs_size (PM.p_tb s0) + (len - w)
/\ PMSP.src_step (PM.p_src s0) (PM.p_src s) sm0 sm /\ fields_eq s.
Definition state_ok (M : word -> option byte) (model : Model) (s : PM.pst) (sm : PM.strm) (cr : credit) : Prop :=
memrel M /\ saves8 M /\ PM.parser_at RSEGS AD T3 T4 M (fb + 40) (fb + 440) s /\ PM.iss_at RSEGS AD T3 M (fb + 440) str sm
/\ PMST.base_ok RSEGS AD M /\ PM.tb_ok (PM.p_tb s) (PM.p_tg s)
/\ hi_heap HI (PM.parser_own s ++ LBX) cr M (m_vmmaps model) /\ PMSP.model_ok model /\ model_but_vm model0 model
/\ PMSP.credit_le (PM.pot_text L (PM.p_tb s) (PM.p_tg s)) cr
/\ PMSP.credit_keep cr0 cr (PM.pot_text L (PM.p_tb s0) (PM.p_tg s0)) (PM.pot_text L (PM.p_tb s) (PM.p_tg s)).
Definition lregs (R : bvmap 5 word) (w : Z) : Prop :=
getr R (reg 2) = Z_to_bv 64 (S - 64) /\ getr R (reg 8) = Z_to_bv 64 len /\ getr R (reg 9) = Z_to_bv 64 (fb + 376)
/\ getr R (reg 18) = Z_to_bv 64 (fb + 64) /\ getr R (reg 20) = Z_to_bv 64 w /\ getr R (reg 21) = Z_to_bv 64 (fb + 376 + 1) /\ kept7 R.
Lemma finish : ltac2:(TCodec.tc2 tcn__PmSSrd1 "U3'RC&Iy5'T1yR0%211%5241'7y8%611%311p061'G'QD'QL&Q0'@'<&RDr7&T0&S1u1%211%42F1%7261&T2vO%:214%32I1%:2J1%>3J61r8u2%=11%?2Q11%B241vRG%B2Q21%F3Q231r9u8%E11%G2Q91%J241%K2B2%D2Q:1%K2Q;1%O3Q;41r:u9%N11%Q02QB1%Q3241%Q42K2%M2QC1%Q42QD1%Q83QD41r;uB%Q711%Q92QK1%Q<241%Q=2Q42%Q62QL1%Q=2QM1%QA3QM41r<uC%Q@11%QB2R41%QE241%QF2Q=2%Q?2R51%QF2R61%QJ3R641r=uD%QI11%QK2R=1%QN241%QO2QF2%QH2R>1%QO2R?1%R33R?41r>uE%R211%R42RF1%R7241%R82QO2%R12RG1%R82RH1%R<3RH41r?uF%R;11%R=2RO1%R@241%RA2R82%R:2S01%RA2S11%RE3S141&R6r@%211rAu:%RG11%RI2S;1%RL241&S3vSB%221QG%RN2S>1%S23S>51';&ROz%221QD%32QE8%5221&R9rB%251BDNQ7&R5%13DFQ9'RE&RF&Q;vRH%211&R<rFrE+Vnb0rDrC%66:54321vB%=4<921p0?1p0B1p0F1p0M1p0Q81p0Q<1p0QF1p0R01p0R:1p0RD1p0RN1p0S81p0SB1p0SK1pX@T;1pVDT=1pWHT?1pWDTA1pW<TC1pQFTE1pQLTK1pVLU21").
Proof using All. intros fx R M model s sm cr w.
intros E1 E2 E8 E9 E18 E19 E20 E21 E22 KP E10 Hw
((EK & DK & STK) & _ & PA & IA & BASE & TBOK & HH & MOK & MB & _ & CK) (CONS & SZ & STEP & (F1 & F2 & F3 & F4 & F5 & F6)).
pose proof MOK as (Mh & Ml & Mm). pose proof RAok as (Hr1 & Hr2).
assert (RA : getr R (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact Rra0).
unfold PMSP.cfg.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx R M 0x37a40 (ltac:(oW' 0x37a40%Z)) r (ltac:(oF' 0x37a40%Z)) ltac:(reflexivity) (ltac:(oD' 0x37a40%Z)) RA Hr1 Hr2)|].
apply (KONT fx R M model s sm cr (len - w)); try assumption; try lia.
- apply PMK.preserved_by_index. intros x Hx. unfold PMK.cs_all in Hx. cbn in Hx.
destruct Hx as [<-|Hx]; [rewrite E2, Rsp0; reflexivity|].
destruct Hx as [<-|Hx]; [apply KP; cbn; auto|]. destruct Hx as [<-|Hx]; [apply KP; cbn; auto|].
destruct Hx as [<-|Hx]; [rewrite E8; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E9; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite E18; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E19; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite E20; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E21; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite E22; apply Z_to_bv_bv_unsigned|].
apply KP. destruct Hx as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; auto 10.
- apply (PMK.hpres_of L LBX S 22528 W0 M0 M EK); [destruct STK as (_ & _ & _ & _ & D); exact D| exact DK].
Qed.
Lemma call_resize : ltac2:(TCodec.tc2 tcn__PmSSrd1 "U8'RC&Iy5'T1yR0%211%5241'7y8%611%311p061'G'QD'QL&Q0'@'<&RDr8&T0&S1u1%211%42F1%7261r1%72G1%;3G31&Q9r2%211r:u2%=11%?2Q11%B241&S3vRG+R0%3221%E2Q51%I3Q561&R6r;%211r<u:%K11%M2Q?1%Q0241&RNvS<+[H%3221%Q32QC1%Q73QC61r=u;%Q611%Q82QJ1%Q;241r7%Q;2QK1%Q?3QK31';&ROz%221QA&R1&QA%11K%311&Q=%G221%92QH1%;281&S0r9&S2+2+J%3221%Q021:%7261&R9r?r>%3521OQ:Q<'R2&Q5rHr6%3221r4%J11rC%R@3RA21rD&QOrG%O11%311%Q5251'5'9%12RJRJ%311&R0%11A%Q81C%311%RO3531r5&QB%11H%S33S431%QD251p0?1&RB%13ML7%Q45S6QK1EK'RE&RF&Q;vRH%211&R<rE%266RES11QCS>vB%948521p0;1p0?1p0Q51p0Q:1pVFSI1pX>SI1pX:QA1pW>SO1pQHT11pQNT71pVNT>1rB+ZkW0rAr@%D6HQC4321%J4IF1Bp071p0QN1p0R31p0R<1p0RI1p0S21p0S>1p0SB1p0SN1p0T21pV@T?1pW@T@1pVDTB1pWHTD1pWDTF1pW<TH1pQFTJ1pQLU01pVLU71").
Proof using All. intros fx R M model s sm cr nn X.
intros A1 RAX A2 KP A10 A11 Hn1 Hn2 ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK) NEXT.
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
set (LB' := PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ LBX).
pose proof (perm_tb s LBX cr M _ HH) as HH'. fold LB' in HH'.
pose proof PA as (_ & PD & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _).
assert (STKr : L5C.stk (hl_sptop L) M (S - 64) (PMSP.pm_scr 1)).
{ apply (PMK.stk_call L M S 22528 (S - 64) (PMSP.pm_scr 1) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|].
replace (S - 64) with (S + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMS.str_resize_spec, PMSP.str_resize_spec in RSZ. cbn [pa_str_resize AD] in RSZ.
apply (RSZ fx R M model K LB' cr (fb + 376) nn (S - 64) X (PM.p_tg s) (PM.p_tb s) HH' MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0| exact STKr]. }
{ rewrite L5K.rl10. exact A10. }
{ rewrite L5K.rl11. exact A11. }
{ lia. }
{ lia. }
{ lia. }
{ replace (fb + 376) with (fb + 40 + 336) by lia. exact VS. }
{ exact TBOK. }
{ exact Hn1. }
{ exact Hn2. }
{ exact CRL. }
intros fx' R' M' model' tb' tg' cr' RP VS' SZ TB' OWN HP CK MB' HH2.
apply (NEXT fx' R' M' model' tb' tg' cr' RP SZ OWN).
assert (BR' : PMFR.brange L LB') by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M' _ HH2); intros x Hx; apply in_or_app; right; exact Hx).
assert (EKr : PMK.ek L LB' (S - 64) (PMSP.pm_scr 1) [(fb + 376, 24)] M M') by (apply (PMK.ek_of_hpres L); exact HP).
assert (SC1 : 0 <= PMSP.pm_scr 1) by (unfold PMSP.pm_scr; lia).
assert (WHI : forall a, PMK.inW [(fb + 376, 24)] a -> S - 64 <= a \/ hl_img_lo L <= a < hl_img_hi L).
{ intros a I. left. apply PMFR.inW_inv1 in I. lia. }
assert (NOTW : forall a n, a + n <= fb + 376 \/ fb + 400 <= a -> forall i, a <= i < a + n -> ~ PMK.inW [(fb + 376, 24)] i).
{ intros a n XO i Hi I. apply PMFR.inW_inv1 in I. lia. }
assert (INL : incl LBX LB') by (intros x Hx; unfold LB'; rewrite !in_app_iff; right; right; exact Hx).
split; [split; [|split]|].
- apply (PMK.ek_trans L LBX S 22528 W0 M0 M M' EK).
apply (PMK.ek_callee_in' RSEGS L KL LBX LB' S 22528 (S - 64) (PMSP.pm_scr 1) W0 [(fb + 376, 24)] M M' HP INL);
[unfold PMSP.pm_scr; lia| lia| lia| destruct STOP; lia| exact (PMFR.brange_hi L LBX (PMFR.brange_incl L LBX LB' BR' INL))|].
intros a I. right. apply PMFR.inW_inv1 in I. exists (PMSP.o_tb AD fb, 24). split; [unfold W0, PMSP.W_srcf; apply in_or_app; right; left; reflexivity|].
unfold L5.in_rng, PMSP.o_tb, PMSP.o_p. cbn [fst snd pa_off_p AD PmLayoutS.ADDR_S]. lia.
- apply (PMK.dk_trans L LBX S 22528 M0 M M' DK).
apply (PMK.dk_callee L LBX LB' S 22528 (S - 64) (PMSP.pm_scr 1) [(fb + 376, 24)] M M' HP INL); [unfold PMSP.pm_scr; lia| lia].
- apply (PMK.stk_after RSEGS L KL LB' M M' S 22528 (S - 64) (PMSP.pm_scr 1) [(fb + 376, 24)] STK HP); unfold PMSP.pm_scr; lia.
- split.
{ destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
unfold saves8. repeat split; (apply (PMFR.u64_keep RSEGS L KL LB' (S - 64) (PMSP.pm_scr 1) [(fb + 376, 24)] M M' EKr STKr SC1);
[lia|lia| apply NOTW; lia| eassumption]). }
split.
{ apply (PMTK2.parser_tb_set RSEGS AD M M' (fb + 40) (fb + 440) s tb' tg' PA); [lia|lia| | | | | | | |].
- apply (PMFR.ag_hi RSEGS L KL LB' (S - 64) (PMSP.pm_scr 1) [(fb + 376, 24)] M M' EKr STKr SC1); [lia|lia| apply NOTW; lia].
- apply (PMFR.ag_hi RSEGS L KL LB' (S - 64) (PMSP.pm_scr 1) [(fb + 376, 24)] M M' EKr STKr SC1); [lia|lia| apply NOTW; lia].
- apply PMPK.dkr_agree. apply (PMFR.ag_block RSEGS L KL LB' (S - 64) (PMSP.pm_scr 1) [(fb + 376, 24)] M M' EKr STKr SC1 BR' WHI).
unfold LB', PM.src_own. left. reflexivity.
- pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & Hk & _) & _). pose proof (PM.pow2_pos (PM.p_k s) (proj1 Hk)).
destruct (BR' (PM.p_b s) (32 * 2 ^ PM.p_k s) ltac:(unfold LB', PM.vec_own; right; left; reflexivity)) as (Q0 & _ & _). lia.
- destruct (BR' (PM.p_b s) (32 * 2 ^ PM.p_k s) ltac:(unfold LB', PM.vec_own; right; left; reflexivity)) as (_ & _ & Q4). destruct STOP. lia.
- apply (PMFR.ag_block RSEGS L KL LB' (S - 64) (PMSP.pm_scr 1) [(fb + 376, 24)] M M' EKr STKr SC1 BR' WHI).
unfold LB', PM.vec_own. right. left. reflexivity.
- replace (fb + 40 + 336) with (fb + 376) by lia. exact VS'.
- apply (PMPK.defined_dkr M M' _ _ (PMPK.dkr_hpres_hi RSEGS L KL LB' (S - 64) (PMSP.pm_scr 1) [(fb + 376, 24)] M M' (fb + 40) 384 HP STKr SC1 ltac:(lia) ltac:(lia)) PD). }
split.
{ apply (PMF.iss_at_agree RSEGS AD M M' (fb + 440) str sm); [lia|lia| | |exact IA].
- apply (PMFR.ag_hi RSEGS L KL LB' (S - 64) (PMSP.pm_scr 1) [(fb + 376, 24)] M M' EKr STKr SC1); [lia|lia| apply NOTW; lia].
- intros c n p E. apply (PMFR.ag_block RSEGS L KL LB' (S - 64) (PMSP.pm_scr 1) [(fb + 376, 24)] M M' EKr STKr SC1 BR' WHI).
apply INL. apply INCS. rewrite E. left. reflexivity. }
split.
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB' (S - 64) (PMSP.pm_scr 1) [(fb + 376, 24)] M M' EKr);
first [exact BASE | intros a Ha r0 [<-|[]]; unfold L5.in_rng; cbn [fst snd]; cbn in Ha; lia]. }
split; [exact TB'|].
split; [apply perm_tb_back; exact HH2|].
split; [exact (PMFR.model_ok_but_vm model model' MOK MB')|].
split; [exact (L5C.model_but_vm_trans _ _ _ MB MB')|].
split; [apply (PMPK.credit_le_keep cr cr' _ _ CRL CK)|].
unfold PMSP.credit_keep in *. cbn [PMTK2.with_tb PM.p_tb PM.p_tg]. destruct CRK, CK. split; lia.
Qed.
Definition tbdst (s : PM.pst) (p k : Z) : Prop :=
((exists n, PM.p_tb s = PM.VShort n) /\ fb + 376 + 1 <= p /\ p + k <= fb + 376 + 24)
\/ (exists c n q, PM.p_tb s = PM.VLong c n q /\ q <= p /\ p + k <= q + c).
Lemma inW_W0 : ltac2:(TCodec.tc2 tcn__PmSSrd1 "B'@&RA&R4r1%3221';&ROvS<r2%3221&S0&RN+g@%2261%4261%:261p0<1pVBA1").
Proof using All. intros a.
intros (r0 & Hin & Hr). unfold W0, PMSP.W_srcf, PMSP.o_src, PMSP.o_tb, PMSP.o_is, PMSP.o_p in Hin.
cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S app] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia.
Qed.
Lemma outside_W0 : ltac2:(TCodec.tc2 tcn__PmSSrd1 ";'@&S0r1vRG%3221&Q8&R4r2%3221p051pVB:1").
Proof using All. intros a. intros Ha r0 Hr0 Hin. assert (I : PMK.inW W0 a) by (exists r0; split; assumption). apply inW_W0 in I. lia. Qed.
Lemma W_src_in : ltac2:(TCodec.tc2 tcn__PmSSrd1 "M'QK'@&RA&R;&Q<vS<r2%43321r1%7221'>&R4%:216';&RO&QHr3%211%421<&S0&RN&Q=%2251%42A1%;261%?2=1p0A1pVBJ1pWLL1").
Proof using All. intros src a.
intros (r0 & Hin & Hr). unfold PMSP.W_src in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]].
- left. exists r0. split; [unfold W0; apply in_or_app; left; exact Hin| exact Hr].
- right. exact Hr.
Qed.
Lemma src_callee_mem : ltac2:(TCodec.tc2 tcn__PmSSrd1 "S7'T1yR0%211'7y8%511%311p051'QD&Q0'H'@'5&Q:%211&R7r7%211&R8r8%211&Q1vA&2'9%12>>&QC%11;vF%63421r6r9r5%<5;4321';&ROz%2215&S3+fP0+R0%3221%72:1%9261&Q6vD%D1?%H3F1CvRG%;219r;r:%87753FD21&RAr1%22Q71'>&R4r2%6221'=&RJ(8%14QDQD59r>%Q711%53Q931r4%Q12:1&S0&RN%12=A%3251%Q7251%Q8281qW8R01%@2R11q2R21%B2R31%G2D1p0I1pVBR61r<%R411%R212&R@r=%27Q:QKQ7Q@N15%QF241%QG261p091p0Q71p0QA1p0QL1p0R:1p0R>1pV>RB1pWFRF1pV:RH1pVDRJ1pWDRL1pQHRN1pQFRO1").
Proof using All. intros M M' s cr VM scr' W'.
intros (EK & DK & STK) SV HH Hs HP FP.
pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
set (LBc := PM.parser_own s ++ LBX).
assert (BR : PMFR.brange L LBc) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
pose proof (own_apart s LBX cr M VM HH) as OWNF.
assert (OWNLO : forall a B m, In (B, m) (PM.parser_own s) -> B <= a < B + m -> a < S - 22528).
{ intros a B m Hin Ha. destruct (OWNF B m Hin) as (Q & _). lia. }
assert (EKr : PMK.ek L LBc (S - 64) scr' W' M M') by (apply (PMK.ek_of_hpres L); exact HP).
assert (STKr : L5C.stk (hl_sptop L) M (S - 64) scr').
{ apply (PMK.stk_call L M S 22528 (S - 64) scr' STK); [lia|lia|lia|]. replace (S - 64) with (S + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
assert (SC0 : 0 <= scr') by lia.
assert (EKn : PMK.ek L LBX S 22528 W0 M M').
{ apply (PMPK.ek_drop_own L (PM.parser_own s) LBX S 22528 W0 (W0 ++ PM.parser_own s) M M').
- apply (PMK.ek_callee_in' RSEGS L KL LBc LBc S 22528 (S - 64) scr' (W0 ++ PM.parser_own s) W' M M' HP (incl_refl _));
[lia|lia|lia| destruct STOP; lia| exact (PMFR.brange_hi L LBc BR)|].
intros a I. right. destruct (FP a I) as [(r0 & Hr0 & Hin)|(B & m & Hin & Ha)].
+ exists r0. split; [apply in_or_app; left; exact Hr0| exact Hin].
+ exists (B, m). split; [apply in_or_app; right; exact Hin| unfold L5.in_rng; cbn [fst snd]; lia].
- exact OWNF.
- intros a O. apply outside_own. exact O. }
assert (NOTW : forall a n, S - 64 <= a -> a + n <= S -> forall i, a <= i < a + n -> ~ PMK.inW W' i).
{ intros a n H1 H2 i Hi I. destruct (FP i I) as [I'|(B & m & Hin & Ha)]; [apply inW_W0 in I'; lia| apply (OWNLO i B m Hin) in Ha; lia]. }
split; [split; [|split]|].
- exact (PMK.ek_trans L LBX S 22528 W0 M0 M M' EK EKn).
- apply (PMK.dk_trans L LBX S 22528 M0 M M' DK).
apply (PMK.dk_callee L LBX LBc S 22528 (S - 64) scr' W' M M' HP); [intros x Hx; apply in_or_app; right; exact Hx| lia| lia].
- apply (PMK.stk_after RSEGS L KL LBc M M' S 22528 (S - 64) scr' W' STK HP); lia.
- split; [|exact EKn].
destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
unfold saves8. repeat split; (apply (PMFR.u64_keep RSEGS L KL LBc (S - 64) scr' W' M M' EKr STKr SC0); [lia|lia| apply NOTW; lia| eassumption]).
Qed.
Lemma base_keep : ltac2:(TCodec.tc2 tcn__PmSSrd1 "Q0'T1yR0%211'7y8%511%311p051&R@vDvFvRG+fP0&R4r2r1%877654321&Q7&Q4%11:r3%4421:9&R?&RF&Q<r4%43321p011p071p0=1pQHG1pQFH1").
Proof using All. intros M M'.
intros E (_ & SLO & _ & STOP & _) B. apply (PMKP.base_ok_keep RSEGS AD L KL SF LBX S 22528 W0 M M' E); [| | | |exact B].
all: intros a Ha; apply outside_W0; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S] in Ha; destruct STOP; lia.
Qed.
Lemma call_srcread : ltac2:(TCodec.tc2 tcn__PmSSrd1 "UG'RC&Iy5'T1yR0%211%5241'7y8%611%311p061'G'QD'QL&Q0'@'<&RDr9&T0&S1u1%211%42F1%7261r1%72G1%;3G31&Q9r2%211r;u2%=11%?2Q11%B241&S3vRG+R0%3221%E2Q51%I3Q561&R6r<%211r=u:%K11%M2Q?1%Q0241&RNvS<%221>%Q22QB1%Q63QB51r>u;%Q511%Q72QI1%Q:241r8%Q:2QJ1%Q>3QJ31r?u<%Q=11%Q?2R11%QB241%QD3R017';&RO+1%221QF&Q=%42QH1%6231&R:r:%23GQ?1&R9rAr@%3521CKQ5'QK&Q5rIr5%3221r6%R821Q9%R72RGQM%R;3RG21zr3%H221rD%J231%L231&R=&Q@%11?rH%442>1@r4%RH3RI21&QIrJ%811%311%Q72Q61%Q82Q7Fp021%S03S1HD%81RO%S23S31F&QG%11QH+2%S63S721%QB251p081&R>rL%H11rK%442S;1R1rN&R3rM%221QD%QC5S341S@6'RE&RF&Q;vRH%211&R<rO%266RCRMQERO1vB%948521p0;1p0A1p0G1p0Q11p0Q91p0QA1p0QH1p0QM1pVHT61pWJT91pWNR41pQHT>1pQNTD1pVNTK1rE+VjQ@rCrB%G6K4R0321%M4LI1Ep071p0R@1p0RE1p0RI1p0S11p0S81p0SA1p0SL1p0T01p0T<1p0T@1pV@TM1pW0TN1pWBTO1pVDU11pWHU31pWDU51pW<U71pQFU91pQLU?1pVLUF1").
Proof using All. intros fx R M model s sm cr p k X.
intros A1 RAX A2 KP A10 A11 A12 Hk DST SO NEXT.
pose proof SO as (MR & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
assert (BR : PMFR.brange L (PM.parser_own s ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
assert (DSTB : 0 <= p /\ p + k <= 2 ^ 64 /\ forall a, p <= a < p + k -> PMK.inW W0 a \/ exists B m, In (B, m) (PM.parser_own s) /\ B <= a < B + m).
{ destruct DST as [(_ & D1 & D2)|(c & n & q & E & D1 & D2)].
- split; [lia|]. split; [destruct STOP; lia|]. intros a Ha. left. exists (PMSP.o_tb AD fb, 24).
split; [unfold W0; apply in_or_app; right; left; reflexivity|]. unfold L5.in_rng, PMSP.o_tb, PMSP.o_p; cbn [fst snd pa_off_p AD PmLayoutS.ADDR_S]. lia.
- assert (IN : In (q, c) (PM.parser_own s)) by (unfold PM.parser_own; rewrite E; cbn; right; right; left; reflexivity).
destruct (BR q c ltac:(apply in_or_app; left; exact IN)) as (Q0 & _ & Q4).
split; [lia|]. split; [destruct STOP; lia|]. intros a Ha. right. exists q, c. split; [exact IN| lia]. }
destruct DSTB as (Dp0 & Dp1 & DIN).
assert (STKr : L5C.stk (hl_sptop L) M (S - 64) (PMSP.pm_scr 4)).
{ apply (PMK.stk_call L M S 22528 (S - 64) (PMSP.pm_scr 4) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|].
replace (S - 64) with (S + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
pose proof SRD as SR. unfold PMPSS.src_read_spec, PMPS.src_read_spec, PMPS.src_spec in SR. cbn [pa_src_read AD PmLayoutS.ADDR_S] in SR.
apply (SR fx R M model K LBX cr (S - 64) X fb s str sm [(p, k)] HH MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0| exact STKr]. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutS.ADDR_S]. split; [lia|]. split; [lia| exact FR3]. }
{ rewrite L5K.rl10. unfold PMSP.o_src, PMSP.o_p. cbn [pa_off_p AD PmLayoutS.ADDR_S]. replace (fb + 40 + 24) with (fb + 64) by lia. exact A10. }
{ unfold PMPS.read_args. exists p, k. rewrite L5K.rl11, L5K.rl12. split; [exact A11|]. split; [exact A12|]. split; [exact Hk|].
unfold PMPS.read_dst. right. unfold PMSP.o_tb, PMSP.o_p. cbn [pa_off_p AD PmLayoutS.ADDR_S].
destruct DST as [(E & D1 & D2)|D]; [left; split; [exact E|]; lia| right; exact D]. }
{ unfold PMPS.read_W. exists p, k. rewrite L5K.rl11, L5K.rl12. split; [exact A11|]. split; [exact A12|]. split; [lia|]. split; [unfold PM.CHUNK in Hk; lia| reflexivity]. }
{ unfold PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S]. exact PA. }
{ unfold PMSP.o_is. cbn [pa_off_is AD PmLayoutS.ADDR_S]. exact IA. }
{ exact BASE. }
{ exact INCS. }
intros fx' R' M' src' sm' RP PA' IA' STEP RES HP HH'.
unfold PMSP.o_p, PMSP.o_is in PA', IA'. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S] in PA', IA'.
change (PMSP.pm_scr 4) with 20480 in HP.
unfold PMPS.read_res in RES. destruct RES as (p' & k' & d & Y11 & Y12 & Hp' & Hk' & Y10 & Hd & CONS & _ & POS & ZERO).
assert (pk : p' = p /\ k' = k).
{ change (getr R (reg 11) = Z_to_bv 64 p') in Y11. change (getr R (reg 12) = Z_to_bv 64 k') in Y12.
rewrite A11 in Y11. rewrite A12 in Y12. apply (f_equal bv_unsigned) in Y11, Y12.
unfold PM.CHUNK in Hk, Hk'. rewrite !L5.unsigned_lit in Y11, Y12 by lia. split; congruence. }
destruct pk as (-> & ->).
assert (QC : PM.sr_qc src' = PM.sr_qc (PM.p_src s)) by (destruct STEP as (E & _); exact E).
apply (NEXT fx' R' M' src' sm' d RP Y10 Hd CONS POS ZERO STEP).
destruct (src_callee_mem M M' s cr _ 20480 (PMSP.W_src AD fb (PM.p_src s) ++ [(p, k)]) MR SV HH ltac:(lia) HP) as (MR' & SV' & EKn).
{ intros a (r0 & Hin & Hr). apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]].
- destruct (W_src_in (PM.p_src s) a (ex_intro _ r0 (conj Hin Hr))) as [I|I]; [left; exact I| right].
exists (PM.sr_qc (PM.p_src s)), PM.CHUNK. split; [unfold PM.parser_own, PM.src_own; left; reflexivity| exact I].
- apply DIN. exact Hr. }
split; [exact MR'|]. split; [exact SV'|]. split; [exact PA'|]. split; [exact IA'|].
split; [exact (base_keep M M' EKn STK BASE)|]. split; [exact TBOK|].
split; [rewrite (own_with_src s src' QC); exact HH'|].
split; [exact MOK|]. split; [exact MB|]. split; [exact CRL| exact CRK].
Qed.
Lemma call_filltb (fx : FPState) R M model s sm cr (p X c0 n0 q0 : Z) :
getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 64) -> kept7 R ->
getr R (reg 10) = Z_to_bv 64 (fb + 64) -> getr R (reg 11) = Z_to_bv 64 p -> getr R (reg 12) = Z_to_bv 64 PM.CHUNK ->
PM.p_tb s = PM.VLong c0 n0 q0 -> q0 <= p -> p + PM.CHUNK <= q0 + c0 -> state_ok M model s sm cr ->
(forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (sm' : PM.strm) (c : Z),
regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 c -> 0 <= c <= PM.CHUNK -> PM.sm_g sm' = PM.sm_g sm + c ->
(PM.sm_st sm = 0 -> c = Z.min PM.CHUNK (PM.sm_eg sm - PM.sm_g sm) /\ PM.sm_st sm' = (if Z.ltb c PM.CHUNK then 2 else 0)) ->
PMSP.src_step (PM.p_src s) (PM.p_src s) sm sm' ->
state_ok M' model s sm' cr ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' X M' model) K) ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x36a08 M model) K.
Proof using All.
intros A1 RAX A2 KP A10 A11 A12 ETB D1 D2 SO NEXT.
pose proof SO as (MR & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
assert (BR : PMFR.brange L (PM.parser_own s ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
assert (IN : In (q0, c0) (PM.parser_own s)) by (unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity).
destruct (BR q0 c0 ltac:(apply in_or_app; left; exact IN)) as (Q0 & _ & Q4).
assert (STKr : L5C.stk (hl_sptop L) M (S - 64) (PMSP.pm_scr 3)).
{ apply (PMK.stk_call L M S 22528 (S - 64) (PMSP.pm_scr 3) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|].
replace (S - 64) with (S + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
pose proof FBT as SR. unfold PMTXS.fill_buffer_tb_spec, PMPS.src_spec in SR. cbn [pa_fill_buffer AD PmLayoutS.ADDR_S] in SR.
apply (SR fx R M model K LBX cr (S - 64) X fb s str sm [(p, PM.CHUNK)] HH MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0| exact STKr]. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutS.ADDR_S]. split; [lia|]. split; [lia| exact FR3]. }
{ rewrite L5K.rl10. unfold PMSP.o_src, PMSP.o_p. cbn [pa_off_p AD PmLayoutS.ADDR_S]. replace (fb + 40 + 24) with (fb + 64) by lia. exact A10. }
{ unfold PMTXS.tbfill_args. exists p. rewrite L5K.rl11, L5K.rl12. split; [exact A11|]. split; [exact A12|]. exists c0, n0, q0. split; [exact ETB|]. lia. }
{ unfold PMTXS.tbfill_W. exists p. rewrite L5K.rl11. split; [exact A11|]. split; [destruct STOP; unfold PM.CHUNK in *; lia| reflexivity]. }
{ unfold PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S]. exact PA. }
{ unfold PMSP.o_is. cbn [pa_off_is AD PmLayoutS.ADDR_S]. exact IA. }
{ exact BASE. }
{ exact INCS. }
intros fx' R' M' src' sm' RP PA' IA' STEP RES HP HH'.
unfold PMSP.o_p, PMSP.o_is in PA', IA'. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S] in PA', IA'.
change (PMSP.pm_scr 3) with 18432 in HP.
destruct RES as ((-> & c & Y10 & Hc & G & ST0 & ST2) & _).
rewrite with_src_id in PA'.
apply (NEXT fx' R' M' sm' c RP Y10 Hc G ST0 STEP).
destruct (src_callee_mem M M' s cr _ 18432 (PMSP.W_src AD fb (PM.p_src s) ++ [(p, PM.CHUNK)]) MR SV HH ltac:(lia) HP) as (MR' & SV' & EKn).
{ intros a (r0 & Hin & Hr). apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]].
- destruct (W_src_in (PM.p_src s) a (ex_intro _ r0 (conj Hin Hr))) as [I|I]; [left; exact I| right].
exists (PM.sr_qc (PM.p_src s)), PM.CHUNK. split; [unfold PM.parser_own, PM.src_own; left; reflexivity| exact I].
- right. exists q0, c0. split; [exact IN|]. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
split; [exact MR'|]. split; [exact SV'|]. split; [exact PA'|]. split; [exact IA'|].
split; [exact (base_keep M M' EKn STK BASE)|]. split; [exact TBOK|].
split; [exact HH'|].
split; [exact MOK|]. split; [exact MB|]. split; [exact CRL| exact CRK].
Qed.
Lemma unread_nn : ltac2:(TCodec.tc2 tcn__PmSSrd1 "QH'T1yR0%211'7y8%511%311p051'G'QD'QL&Q0&R9r5r4r3r2r1%6554321';&ROz&QM&Q@%11:%321:%6251'>'<'@&QG%11@%4331;+2%63531%8231&QI%11=%B2A1&Q=%D231%F231&QF%11L&QE%11N%J231%L261%M2=1%N2G1p0Q01pVDQ81pWHQ:1pWDQ<1pW<Q>1pQFQ@1").
Proof using All. intros M model s sm cr.
intros (_ & _ & PA & IA & _).
destruct PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & Q8 & Q9 & Q10 & _) & _).
destruct IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & ST) & _ & G1 & G2).
unfold PM.unread. split; [lia|]. split; [exact ST|]. split; [unfold PM.CHUNK in *; lia| exact G2].
Qed.
Definition lstate (R : bvmap 5 word) (M : word -> option byte) (model : Model) (s : PM.pst) (sm : PM.strm) (cr : credit) (w : Z) : Prop :=
lregs R w /\ state_ok M model s sm cr /\ acct s sm w /\ 1 <= w <= len.
Definition IHt (mu0 : Z) : Prop :=
forall (fx : FPState) R M model s sm cr w, PM.mu_src (PM.p_src s) sm < mu0 -> lstate R M model s sm cr w ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x37900 M model) K.
End Call.
End WithHeap.
End PMSSR1.
