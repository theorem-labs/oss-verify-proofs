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
PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmAParKit PmAReset1 PmAUarK PmAUar.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmARvK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmARvK.PMARVK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmARvK.PMARVK.SCFG_1.WithHeap."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0Ac"; "1bool"; "1list"; "1nat"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "3Z"; "0E"; "0KS"; "0LKc"; "4Model"; "5bvmap"]; ["0M1"; "0M1'"; "0Mc"; "0R"; "0R1"; "0Rc"; "6mrestrict"; "7credit"; "8ahid"; "8fframe"; "9u8_at"; ";FF'"; ";MIDREGS"; ";mid"; ";oec"; ";op"]; [";ov"; ";rvar"; ";rvc"; ";rvmem"; ";rvst"; ";rvvis"; ":ocell"; ":own"; ":rve"; ":vF"; ":vFF"; ":vfb"; ":vfl"; ":vsp"; "<p_more"; "<pst"]; ["<strm"; "=frame_okA"; ">getr"; "?loaded_segments"; "@eqb"; "AIn"; "Aexistsb"; "Aforallb"; "Badd"; "Bdiv"; "Ble"; "Blt"; "Bof_nat"; "Bpow"; "Bsub"; "0X"]; ["0a"; "0c"; "0crc"; "0e"; "0k"; "0modelc"; "0s"; "0sm"; "CZ_to_bv"; "Cbv"; "0v"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Module PMARVK.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition SCR : Z := 28672.
Definition ocell (E : Z) (a : Z) : Prop := E - 104 <= a < E.
Definition own (E : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
L5.u64_at RSEGS M (E - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M (E - 16) (bv_unsigned (getr R (reg 8)))
/\ L5.u64_at RSEGS M (E - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M (E - 32) (bv_unsigned (getr R (reg 18)))
/\ L5.u64_at RSEGS M (E - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M (E - 48) (bv_unsigned (getr R (reg 20)))
/\ L5.u64_at RSEGS M (E - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M (E - 64) (bv_unsigned (getr R (reg 22)))
/\ L5.u64_at RSEGS M (E - 72) (bv_unsigned (getr R (reg 23))) /\ L5.u64_at RSEGS M (E - 80) (bv_unsigned (getr R (reg 24)))
/\ L5.u64_at RSEGS M (E - 88) (bv_unsigned (getr R (reg 25))) /\ L5.u64_at RSEGS M (E - 96) (bv_unsigned (getr R (reg 26)))
/\ L5.u64_at RSEGS M (E - 104) (bv_unsigned (getr R (reg 27))).
Lemma own_agree : ltac2:(TCodec.tc2 tcn__PmARvK "QD':&?y5'R9yR0%211%5241'5y8%611%311p061pTH72&QJz&QNr4+S8%3221%6251r5&QM+2+R0%3221%<251&Q7r6%2318<&Q6r8r1%3221'9&R8r2%22Q01%:11r7%113%73N31p091pT2Q:1%A3=5Gp021p0A1p0E1p0L1pQ4Q41pQ2Q61pQ8Q<1pHQC1").
Proof. intros E R M1 M1'.
intros H1 H2 OW AG. unfold own, ocell in *.
destruct OW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
repeat split; (eapply L5C.u64_at_agree; [| | | eassumption]); first [ (intros i Hi; apply AG; lia) | lia ].
Qed.
Record rve : Type := RVE {
vR : bvmap 5 word; vr : Z; vsp : Z; vfb : Z; vcat : Z; vs0 : PM.pst; vstr : PM.vstr; vsm0 : PM.strm; ve0 : bool;
vLBX : list (Z * Z); vFF : list fframe; vLK : list fframe; vAw : list (Z * Z); vcr : credit; vmodel : Model; vM : word -> option byte; vK : TSet;
vF : Z; vfl : Z; vLK2 : list fframe; vM2 : word -> option byte; vmodel2 : Model }.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Definition op (E : rve) : Z := PMSPA.o_p PMA.AD (vfb E).
Definition ov (E : rve) : Z := PMSPA.o_v PMA.AD (vfb E).
Definition oec (E : rve) : Z := PMSPA.o_ec PMA.AD (vfb E).
Definition ois (E : rve) : Z := PMSPA.o_is PMA.AD (vfb E).
Definition WR (E : rve) : list L5.range := PMSPA.W_run PMA.AD (vfb E).
Definition FF' (E : rve) : list fframe := (vF E, 3, vsp E - 128 + 32) :: vFF E.
Definition kont (E : rve) : Prop :=
forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (e' : bool) (cr' : credit),
regs_preserved (vR E) R' ->
PMSPA.run_post RSEGS PMA.AD PMA.AAD (fun _ => PMSPA.prog_value) R' M' (vfb E) (vs0 E) s' (vstr E) (vsm0 E) sm' (ve0 E) e' (vcat E) ->
L5CA.ahpres L ar (vLBX E) (vFF E) (vsp E) SCR (WR E) (vM E) M' ->
PMSPA.credit_keep (vcr E) cr' (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) (vs0 E))) (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s')) ->
model_rt (vmodel E) model' -> incl LK' (vLK E) -> incl (vAw E) Aw' -> L5CA.amodel_ok Aw' model' ->
ri_inv HI (PM.parser_own s' ++ vLBX E) (vFF E) LK' cr' Aw' M' (vml_of model') ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' (vr E) M' model') (vK E).
Definition rvar (E : rve) : Prop :=
let sp := vsp E in let op := op E in let oec := oec E in let ov := ov E in let F := vF E in let fl := vfl E in
(140735332487296 <= sp <= 140737488355328 /\ sp mod 32 = 0)
/\ (6885376 <= op <= 140737488354944 /\ op mod 8 = 0 /\ (2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784) /\ ((sp - 128) + 128 <= op \/ op + 384 <= (sp - 128)))
/\ (6885376 <= oec <= 140737488355312 /\ oec mod 8 = 0 /\ (2147446784 + 17592186048512 <= oec \/ oec + 16 <= 2147446784) /\ ((sp - 128) + 128 <= oec \/ oec + 16 <= (sp - 128))
/\ (op + 384 <= oec \/ oec + 16 <= op))
/\ (6885376 <= F <= 140737488354816 /\ F mod 32 = 0 /\ (2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784) /\ 4096 <= fl <= 140737488355327
/\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) /\ (F + 512 <= fl \/ fl + 1 <= F) /\ ((sp - 128) + 128 <= F \/ F + 512 <= (sp - 128))
/\ ((sp - 128) + 128 <= fl \/ fl + 1 <= (sp - 128)) /\ (op + 384 <= F \/ F + 512 <= op) /\ (op + 384 <= fl \/ fl + 1 <= op)
/\ (((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 64 <= ((op / 8) + 2147450880))
/\ (oec + 16 <= F \/ F + 512 <= oec) /\ (oec + 16 <= fl \/ fl + 1 <= oec)
/\ (((oec / 8) + 2147450880) + 2 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 64 <= ((oec / 8) + 2147450880))
/\ (F + 512 <= 65536 \/ 65536 + 1196032 <= F) /\ (((F / 8) + 2147450880) + 64 <= 1263176 \/ 1263176 + 8 <= ((F / 8) + 2147450880)))
/\ (6885376 <= ov <= 140737488355320 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 8 <= 2147446784) /\ ((sp - 128) + 128 <= ov \/ ov + 8 <= (sp - 128))
/\ (op + 384 <= ov \/ ov + 8 <= op) /\ (oec + 16 <= ov \/ ov + 8 <= oec) /\ (F + 512 <= ov \/ ov + 8 <= F) /\ (fl + 1 <= ov \/ ov + 8 <= fl)
/\ (((F / 8) + 2147450880) + 64 <= 2147604776 \/ 2147604776 + 16 <= ((F / 8) + 2147450880))
/\ (((F / 8) + 2147450880) + 64 <= ((ov / 8) + 2147450880) \/ ((ov / 8) + 2147450880) + 1 <= ((F / 8) + 2147450880))).
Record rvc (E : rve) : Prop := RVC {
c_AR : rvar E;
c_G : PMAUK.gctx L ar HI (vLBX E) (vFF E) (vLK E) (vAw E) (vsp E) SCR (vsp E - 128) (vsp E - 104) (vsp E) (ocell (vsp E))
(own (vsp E) (vR E)) (vF E) (vfl E) 3 (vLK2 E) (vM2 E) (vmodel2 E) (vcr E) (PM.parser_own (vs0 E));
c_HH : ri_inv HI (PM.parser_own (vs0 E) ++ vLBX E) (vFF E) (vLK E) (vcr E) (vAw E) (vM E) (vml_of (vmodel E));
c_K0 : vK E [];
c_Rra : getr (vR E) (reg 1) = Z_to_bv 64 (vr E);
c_RA : L5.ra_ok (vr E);
c_Rsp : getr (vR E) (reg 2) = Z_to_bv 64 (vsp E);
c_Rgp : getr (vR E) (reg 3) = Z_to_bv 64 (pa_gp PMA.AD);
c_Rtp : getr (vR E) (reg 4) = Z_to_bv 64 (hl_tp L);
c_ASTK : L5CA.astk ar (vM E) (vsp E) SCR;
c_STKSH : shadow_zero (vM E) (vsp E - SCR) (SCR / 8);
c_FRM : PMSPA.ffroomA 8 (vFF E) (vLK E);
c_FRS : PMSPA.ffrsA (vFF E) (vsp E);
c_FOK : PMSPA.frame_okA (vFF E) (vfb E);
c_SP32 : vsp E mod 32 = 0;
c_INCS : incl (PM.vs_own (vstr E)) (vLBX E);
c_UNR : PM.unread (PM.p_src (vs0 E)) (vsm0 E) < 2 ^ 26;
c_CRED : PMSPA.credit_le (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) (vs0 E))) (vcr E);
c_INV : PM.inv (vs0 E);
c_KONT : kont E
}.
Definition mid (E : rve) (Rc : bvmap 5 word) : Prop :=
getr Rc (reg 2) = Z_to_bv 64 (vsp E - 128) /\ getr Rc (reg 8) = Z_to_bv 64 (vsp E) /\ getr Rc (reg 9) = Z_to_bv 64 (vsp E - 128)
/\ getr Rc (reg 18) = Z_to_bv 64 (vF E / 8 + 2147450880) /\ getr Rc (reg 19) = Z_to_bv 64 (vF E) /\ getr Rc (reg 20) = Z_to_bv 64 (op E)
/\ getr Rc (reg 21) = Z_to_bv 64 (oec E) /\ getr Rc (reg 22) = Z_to_bv 64 (ov E) /\ getr Rc (reg 26) = Z_to_bv 64 2147450880
/\ getr Rc (reg 27) = Z_to_bv 64 (vF E) /\ getr Rc (reg 3) = getr (vR E) (reg 3) /\ getr Rc (reg 4) = getr (vR E) (reg 4).
Definition rvst (E : rve) (Rc : bvmap 5 word) (Mc : word -> option byte) (modelc : Model) (LKc : list fframe) (crc : credit) (Ac : list (Z * Z))
(s : PM.pst) (sm : PM.strm) (e : bool) (v c : Z) : Prop :=
PMAUK.binv L ar HI (vM E) (vmodel E) (vLBX E) (vFF E) (vLK E) (vAw E) (vsp E) SCR (vsp E - 128) (own (vsp E) (vR E)) (vF E) 3
(WR E) (PM.parser_own s) Mc modelc LKc crc Ac
/\ mid E Rc
/\ PMSPA.run_pre RSEGS PMA.AD PMA.AAD Mc (vfb E) s (vstr E) sm e
/\ PMSPA.src_step (PM.p_src (vs0 E)) (PM.p_src s) (vsm0 E) sm /\ (ve0 E = true -> e = true)
/\ PMSPA.credit_keep (vcr E) crc (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) (vs0 E))) (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s))
/\ PMSPA.ec_at RSEGS Mc (oec E) v c.
Definition rvmem (E : rve) (MV : word -> option byte) (v : Z) : Prop :=
let sp := vsp E in let op := op E in let oec := oec E in let F := vF E in let fl := vfl E in
L5.img_clear MV 65536 1261568 /\ L5.u64_at RSEGS MV 1289464 2147450880 /\ L5.u32_at RSEGS MV 1289472 1 /\ L5.u64_at RSEGS MV 1263176 1199536
/\ L5.writable RSEGS MV (sp - 128) 128
/\ L5KA.zeros_at MV ((op / 8) + 2147450880) 3 /\ L5KA.zeros_at MV (((op + 32) / 8) + 2147450880) 44 /\ L5KA.zeros_at MV (((op + 20) / 8) + 2147450880) 1
/\ L5.writable RSEGS MV op 384
/\ L5KA.zeros_at MV ((oec / 8) + 2147450880) 2 /\ L5.writable RSEGS MV oec 16 /\ L5.u32_at RSEGS MV oec v
/\ L5.defined MV F 512 /\ L5.writable RSEGS MV F 512 /\ L5.writable RSEGS MV ((F / 8) + 2147450880) 64 /\ L5.u64_at RSEGS MV (F + 504) fl
/\ L5.writable RSEGS MV fl 1
/\ own sp (vR E) MV.
Definition rvvis (E : rve) (MV : word -> option byte) : Prop :=
let op := op E in let ov := ov E in
L5KA.zeros_at MV ((ov / 8) + 2147450880) 1 /\ L5.writable RSEGS MV ov 8 /\ L5.u64_at RSEGS MV ov 1231168 /\ L5KA.zeros_at MV 2147604776 16
/\ L5.u8_at RSEGS MV (op + 16) 0.
Lemma frame_okA' : ltac2:(TCodec.tc2 tcn__PmARvK "?'Q8&QA&Q:r1%211&Q;%113%6231&Kr2%211%612%;221p061pH>1").
Proof. intros E. intros X. exact (PMAUAR.frame_okA_push (vFF E) (vfb E) (vF E) 3 (vsp E - 128 + 32) X). Qed.
Lemma rvmem_of : ltac2:(TCodec.tc2 tcn__PmARvK "QM'Q8'Q2r1%211&?y5'R9yR0%211%5241'5y8%611%311p061'>'3&I%211&G'6':%2211%711'Q?'Q@'2&Q4r=r;r:r9r8r7r6r5r4r3r2%<<;:987654321Q5&Q3r>&F&H%12;>%321@%63519p081pT4K1pTFL1pT8H1pT@J1pT>L1p4N1pT6Q31pLQ51pT<Q91pQ6Q;1pQ<QA1pT0QH1pHQL1").
Proof. intros E X Rc Mc modelc LKc crc Ac s sm e v c.
intros (BI & MID & RPRE & STEP & EE & CK & EC).
destruct (PMAUK.vis_facts L ar C HI LYa HIok (vM E) (vmodel E) (vLBX E) (vFF E) (vLK E) (vAw E) (vsp E) SCR (vsp E - 128) (vsp E - 104) (vsp E) (ocell (vsp E))
(own (vsp E) (vR E)) (vF E) (vfl E) 3 (vLK2 E) (vM2 E) (vmodel2 E) (vcr E) (PM.parser_own (vs0 E)) (c_G E X)
(WR E) (PM.parser_own s) Mc modelc LKc crc Ac BI) as ((WS & _ & _ & _ & RMS) & OWNv & (FD & FW & FSW & FLC & FLW) & _).
change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. replace (vsp E - (vsp E - 128)) with 128 in WS by lia.
replace (vF E + 512 - 8) with (vF E + 504) in FLC by lia.
pose proof BI as (HHc & _). pose proof RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof (frame_okA' E (c_FOK E X)) as FOK'.
pose proof (PMASK.mach_vis L ar C HI LY HIok _ _ LKc crc Ac Mc modelc HHc BASE) as (VM0 & VM1 & VM2).
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LKc crc Ac Mc modelc (vfb E) _ s HHc FOK' PA) as (_ & Zop & Z32 & Z20 & OWR & _).
pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LKc crc Ac Mc modelc (vfb E) v c HHc FOK' EC) as (_ & Zoec & QWR & _ & QU & _).
unfold rvmem. unfold op, oec. repeat (split; [assumption|]). exact OWNv.
Qed.
Lemma rvvis_of : ltac2:(TCodec.tc2 tcn__PmARvK "QM'Q8'Q2r1%211&?y5'R9yR0%211%5241'5y8%611%311p061'>'3&I%211&G'6':%2211%711'Q?'Q@'2&Q4r=r;r:r9r8r7r6r5r4r3r2%<<;:987654321Q5&Q5r>&F&H%12;>%321@%6251p081pT4K1pTFL1pT8H1pT@J1pT>L1p4N1pT6Q31pLQ51pT<Q91pQ6Q;1pQ<QA1pT0QH1pHQL1").
Proof. intros E X Rc Mc modelc LKc crc Ac s sm e v c.
intros (BI & MID & RPRE & STEP & EE & CK & EC).
pose proof BI as (HHc & _). pose proof RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof (frame_okA' E (c_FOK E X)) as FOK'.
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LKc crc Ac Mc modelc (vfb E) _ s HHc FOK' PA) as ((O1 & _) & _ & _ & _ & _ & _ & OVIS & _).
pose proof (PMAPAR.ov_vis L ar C HI LY HIok _ _ LKc crc Ac Mc modelc (vfb E) HHc FOK' VIS) as (_ & Zov & OVW & _ & OVP & _).
pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ _ LKc crc Ac Mc modelc 0x12c940 16 HHc ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as ZVT.
pose proof PA as (_ & _ & _ & _ & _ & _ & P16 & _).
unfold rvvis, op, ov. split; [exact Zov|]. split; [exact OVW|]. split; [exact OVP|]. split; [exact ZVT|].
apply (proj2 (L5A.u8_at_vis _ Mc _ 0 (OVIS (PMSPA.o_p PMA.AD (vfb E) + 16) 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact P16.
Qed.
Lemma rvmore_of : ltac2:(TCodec.tc2 tcn__PmARvK "R5'Q8'Q2r1%211&?y5'R9yR0%211%5241'5y8%611%311p061'>'3&I%211&G'6':%2211%711'Q?'Q@'2&Q4r=r;r:r9r8r7r6r5r4r3r2%<<;:987654321Q5&J&QC&F&H%12;>%321@&QH&Or>%211+8%5221&Q>%11C%>4=931p0@1pT4Q31pTFQ41pT8Q01pT@Q21pT>Q41p4Q61pT6Q;1pLQ=1pT<QA1pQ6QC1pQ<QI1pT0R01pHR41").
Proof. intros E X Rc Mc modelc LKc crc Ac s sm e v c.
intros (BI & MID & RPRE & STEP & EE & CK & EC).
pose proof BI as (HHc & _). pose proof RPRE as (PA & _).
pose proof (frame_okA' E (c_FOK E X)) as FOK'.
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LKc crc Ac Mc modelc (vfb E) _ s HHc FOK' PA) as ((O1 & _) & _ & _ & _ & _ & _ & OVIS & _).
pose proof PA as (_ & _ & _ & P8 & _).
unfold op. apply (proj2 (L5A.u8_at_vis _ Mc _ _ (OVIS (PMSPA.o_p PMA.AD (vfb E) + 8) 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact P8.
Qed.
Lemma sub_in : ltac2:(TCodec.tc2 tcn__PmARvK "I'3'4%211'9'2&QG&QF&QDr1%211r2%53:21qT:;1%83<13(7%<3;21&QEr4%23A:1%33B92p021pT:D1p071pJE1p2F1").
Proof. intros A KS.
intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & Ex). apply Nat.eqb_eq in Ex. subst x. exact Hx.
Qed.
Definition MIDREGS : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27]%nat.
Lemma mid_keep : ltac2:(TCodec.tc2 tcn__PmARvK "Q3'Q8&?y5'R9yR0%211%5241&Mr3r2%3221'4&QEr1&L%33421'9&QBr4&R8&QL%11<%32D1%6251r5%8213%:3E31p0<1pT:A1%F25Ep021p0E1pQ:J1pQ<K1pHQ21").
Proof. intros E Rc R1.
intros (X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X26 & X27 & X3 & X4) KS. unfold mid.
rewrite !KS by (cbn; tauto). repeat split; assumption.
Qed.
Lemma rvar_rng : ltac2:(TCodec.tc2 tcn__PmARvK "R3'Q8&Q1r1%211'8&QJz&Q=r2%211%5241&QK&QM+2+R0%3221%5271%=271&O%11;%?2>1%:226%B221&Q0%11@%D2C1%?22;%G221&N%11E%I2H1%D22@%L221&Q9%11J%N2M1%I22E%Q1221&Q<%11O%Q32Q21%N22J%Q6221&QN+T0%22Q41%Q92Q81%Q422Q0%Q<221&QH&QI+8%22B1+QoooPP0%5221%QB2QA1%Q=22Q9%QE221%QF2:1%QG2A1%QH2G1%QI2M1%QJ2Q31%QK2Q91%QL2Q?1p0QN1pHR21").
Proof. intros E.
intros AR. unfold rvar in AR. cbn zeta in AR.
destruct AR as ((A1 & _) & (B1 & _) & (Q1 & _) & (F1 & _ & _ & F4 & _) & (V1 & _)).
assert (0 <= vF E / 8) by (apply Z.div_pos; lia). assert (vF E / 8 <= 2 ^ 47) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
End WithHeap.
End SCFG_1.
Ltac rvfacts L ar C HI LY HIok E X ST :=
let MEM := fresh "MEM" in let AR := fresh "AR" in let RNG := fresh "RNG" in let MD := fresh "MD" in
pose proof (rvmem_of L ar C HI LY HIok E X _ _ _ _ _ _ _ _ _ _ _ ST) as MEM;
pose proof (c_AR L ar HI E X) as AR; pose proof (rvar_rng E AR) as RNG;
unfold rvmem in MEM; unfold rvar in AR; cbn zeta in MEM, AR;
destruct MEM as (?MI1 & ?MI2 & ?MI3 & ?MI4 & ?MW & ?MZ1 & ?MZ2 & ?MZ3 & ?MOW & ?MZQ & ?MQW & ?MQU & ?MFD & ?MFW & ?MFSW & ?MFLC & ?MFLW & ?MOWN);
destruct AR as ((?AS1 & ?AS2) & (?AO1 & ?AO2 & ?AO3 & ?AO4) & (?AQ1 & ?AQ2 & ?AQ3 & ?AQ4 & ?AQ5)
& (?AF1 & ?AF2 & ?AF3 & ?AF4 & ?AF5 & ?AF6 & ?AF7 & ?AF8 & ?AF9 & ?AF10 & ?AF11 & ?AF12 & ?AF13 & ?AF14 & ?AF15 & ?AF16)
& (?AV1 & ?AV2 & ?AV3 & ?AV4 & ?AV5 & ?AV6 & ?AV7 & ?AV8 & ?AV9 & ?AV10));
destruct RNG as (?RG1 & ?RG2 & ?RG3 & ?RG4 & ?RG5 & ?RG6 & ?RG7 & ?RG8);
pose proof ST as (_ & MD & _); unfold mid in MD;
destruct MD as (?MR2 & ?MR8 & ?MR9 & ?MR18 & ?MR19 & ?MR20 & ?MR21 & ?MR22 & ?MR26 & ?MR27 & ?MR3 & ?MR4);
pose proof MOWN as (?MS8 & ?MS16 & ?MS24 & ?MS32 & ?MS40 & ?MS48 & ?MS56 & ?MS64 & ?MS72 & ?MS80 & ?MS88 & ?MS96 & ?MS104).
Ltac rvfactsv L ar C HI LY HIok IL ICok ILY E X ST :=
let VV := fresh "VV" in
pose proof (rvvis_of L ar C HI LY HIok IL ICok ILY E X _ _ _ _ _ _ _ _ _ _ _ ST) as VV; unfold rvvis in VV; cbn zeta in VV;
destruct VV as (?VZ & ?VW & ?VU & ?VZT & ?VD16).
Ltac rvsc := first [ assumption | (hnf; assumption) ].
Ltac kin := apply sub_in; vm_compute; reflexivity.
Ltac kks KS := let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk; apply KS; revert k Hk; kin.
End PMARVK.
