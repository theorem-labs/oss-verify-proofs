(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmKeep PmKitS PmFrame PmParSpecs PmParSpecsS PmParKit PmParStep PmSRdKeyP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSRdKey () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmFrame.PMFR."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1list"; "1nil"; "1option"; "1prod"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0HI"; "0K"; "0L"; "0LB"; "4Model"; "4m_halted"]; ["4m_vm_lazy"; "4m_vmmaps"; "5bvmap"; "0M"; "0M'"; "0M1"; "0R"; "0R1"; "6msteps"; "7credit"; "7hi_heap"; "7hl_sptop"; "8agree_on"; "8stk"; ":range"; "9SCFG"]; [";brange"; "<cfg"; "<ec_at"; "=get_length_spec"; "=make_ec_spec"; "=read_key_spec"; "=read_span_spec"; "=validate_spec"; ">ek"; ">inW"; "?FPState"; "?mkst"; "?seg_rom"; "@TSet"; "Asrealizes"; "Bmem_grows"]; ["Cloaded_segments"; "0SCFG_P"; "Dadd"; "Dle"; "Dlt"; "Dpow"; "Dsub"; "0W"; "0a"; "0c"; "0cr"; "0fx"; "0fx1"; "0i"; "0model"; "0n"]; ["0o"; "0pc"; "0pc1"; "0sp"; "EZ_to_bv"; "Ebv"; "0v"; "0x"; "0x0"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMSRK.
Import PMS.
Local Ltac gl_disp := lazymatch goal with
| |- getr _ _ = _ => PMK.rk
| |- (_ <= _ <= _)%Z => lia
| |- (_ <= _ < _)%Z => lia
| |- (_ <= _)%Z => lia
| |- (_ < _)%Z => lia
| |- forall x, In x _ -> _ => let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [PMK.rk|]); destruct Hx
| |- L5.ra_ok _ => split; [lia| reflexivity]
| _ => assumption
end.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
Lemma ec_agree : ltac2:(TCodec.tc2 tcn__PmSRdKey "Q9'R5yR0%211'3y8%511%311p051'9&Lr5r4r3+@%544321&QCz%2216&QB%1296&QE+2+R0%3221%9251&Q2&Q@r8r6%45321CBr7%655413Ep031p091p0A1p0E1pSDL1pT>M1pT2N1pQ:Q01pQ8Q11").
Proof. intros M M' o v c.
intros AG H1 H2 (E0 & E8 & ED). split; [|split].
- apply (PMF.u32_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E0].
- apply (L5C.u64_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E8].
- apply (L5C.defined_agree M M' o 16 AG ED).
Qed.
Lemma gl_step : ltac2:(TCodec.tc2 tcn__PmSRdKey "U1'1'4'9%2211%411&I'Q:&By5'R5yR0%211%5241'3y8%611%311p061'>&Q=&Jv:r?r>r7&Ar5%211%8576541'6%A1C&?r6%211(0%11H%73631%Q42JJ%Q611&@%11@(2%115%>3531&QC+SoonPPPPP0&Kv<%211%5241&QF+XPPP0%2241+R0%42N1%;231r8%=219'8z%O3QJQ41'5%B2:6&QB%128Q8%E21A%5241%9271'H&Q@&Q;rDrB&R4r@%22R11&Q<%118%85763QG1rCrA%82R7QKr=%=543216%@3?61&Q?%12R0QOr1%Q<2M1&QD&QE+2%221Q7%4261%Q1261&7%Q>2R9Q;r2%QF221%Q423Q>%;231%Q8231%711r3%QL2RA1%Q:2RBG%A231%Q>231%=11r4%Q52S41%Q011%Q912%RD3S121p061p0=1p0F1pSLSC1rIrH%RO1S2%S55S432Q?1'Q>&OvQA%211&Q1rGrE%36QL21QBQAQG%84QM51S<p0:1rF%76R0>1QNQMQK%<4R191S@p041p0C1p0QC1p0QF1p0R81p0RC1p0RF1p0RM1p0S41p0S<1p0SE1pT0T@1pT@TA1pT8TB1pHT21pSNT41pQ<T61pQ8T71pT6TG1pT4TH1pQ@T?1pQ>T@1pSJTG1pSHTH1pSFTJ1pLTL1").
Proof. intros LB cr fx fx1 R R1 pc pc1 M M1 model K sp x n.
intros HH Mh Ml TOP H1 H2 H3 MS MG FRZ KONT.
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R pc R1 pc1 M1
(fun a => (sp - 64 <= a < sp - 64 + 64) \/ (x <= a < x + n)) K HH Mh Ml TOP MS MG).
- intros a Ha N. apply FRZ; [exact Ha| |]; intros X; apply N; [left|right]; exact X.
- intros a Pa. unfold PMK.cwr. left. destruct Pa as [Pa|Pa]; [lia|]. destruct H3 as [H3|H3]; lia.
- intros a. apply PMK.or_dec; apply PMK.rng_dec.
- exact KONT.
Qed.
Lemma gl_ek : ltac2:(TCodec.tc2 tcn__PmSRdKey "RJ'1'4'9%2211%411&N%611'R5yR0%211'3y8%511%311pTB51'5&QCzr1%3221&QD&QE+2+R0%3221%5271%;271&7&QFr8%2217r2%@221&QB%124;%?241%E241%:11r3%G2:1r7%82<1%F241%L241%A11'6r5&R4r4%22Q91%411r6%113%83Q831p0:1p0B1p0N1pSLQG1&M&Kv<%211+jP0%542IG1&Q0r9%2261%QC22QA%Q323Q7%QA2QC1%QG231&Q9%12Q;Q9p031pSBR81&Q8r;r:%37B21@Q6KQ0p051p0>1p0B1p0I1pQ<R51pQ8R61pS@R?1pT0RD1pT@RE1pT8RF1pLRE1").
Proof. intros LB sp x n W M M1.
intros FRZ STK BR INF.
apply (PMK.ek_piece_in RSEGS L KL LB sp 26624 W M M1 (fun a => (sp - 64 <= a < sp - 64 + 64) \/ (x <= a < x + n))
ltac:(intros a Ha N; apply FRZ; [exact Ha| |]; intros X; apply N; [left|right]; exact X) STK (PMFR.brange_hi L LB BR)).
intros a [Pa|Pa]; [left; lia| right; apply INF; lia].
Qed.
Lemma mem_eq_of_frz : ltac2:(TCodec.tc2 tcn__PmSRdKey "Q4'R5yR0%211'3y8%511%311p051'9'5&QCzr1%3221&QD&QE+2+R0%3221%5271%;271'6r3&R4r2%22H1%411r4%113%83G31p0:1pSLG1%;3I8:p021pQ<K1pQ8L1").
Proof. intros M M1.
intros F. apply functional_extensionality_dep. intros w. rewrite <- (PMPK.word_id w). apply F.
pose proof (bv_unsigned_in_range 64 w) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B.
Qed.
Theorem read_key_ok : ltac2:(TCodec.tc2 tcn__PmSRdKey "A&Q3vQAv<v:%43321&Q6%13543&Q7%1276&Q4%13987&Q5%13;:9p031p061p091p0<1").
Proof.
intros GL RS VAL MKE. unfold PMS.read_key_spec, PMSP.read_key_spec, PMSP.run_spec, PMSP.run_spec_r.
intros fx R M model K LBX cr sp r fb cat s str sm e HH MOK K0 ENT FOK ARGS RPRE INCS INV EC0 UNR CRED KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). destruct FOK as (F1 & F2 & F3). cbn [pa_frame AD PmLayoutS.ADDR_S] in F2.
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
destruct ARGS as (A10 & A11 & A12). destruct RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
unfold PMSP.o_src, PMSP.o_p, PMSP.o_is, PMSP.o_ec, PMSP.o_v in *. cbn [pa_off_p pa_off_is pa_off_ec pa_off_v AD PmLayoutS.ADDR_S] in *.
change (PMSP.pm_scr 7) with 26624 in *.
assert (SC0 : 0 <= 26624) by lia.
set (LB := PM.parser_own s ++ LBX) in *.
assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH); apply incl_refl).
assert (NDL : NoDup (map fst LB)) by exact (PMPK.heap_nodup L HI HIok LB cr M _ HH).
pose proof (L5C.stk_writable RSEGS _ M sp 26624 STK) as WR.
destruct s as [mo dn dp src tb tg vb vk stk]. destruct src as [qc de rem]. destruct sm as [g eg st].
cbn [PM.p_src PM.p_tb PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st] in *.
assert (QIN : In (qc, 16384) LB) by (unfold LB, PM.parser_own, PM.src_own; cbn; left; reflexivity).
assert (VIN : In (vb, 32 * 2 ^ vk) LB) by (unfold LB, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
assert (SINC : incl (PM.vs_own str) LB) by (unfold LB; apply incl_appr; exact INCS).
destruct (BR qc 16384 QIN) as (Q0 & Q1 & Q4). unfold hl_ceil in Q4.
destruct (BR _ _ VIN) as (V0 & V1 & V4). unfold hl_ceil in V4.
assert (QI : forall a, qc <= a < qc + 16384 -> ~ (65536 <= a < 954368)).
{ rewrite (ly_img_lo L LY), (ly_img_hi L LY) in Q1. intros a Ha. clear - Ha Q1. lia. }
assert (VI : forall a, vb <= a < vb + 32 * 2 ^ vk -> ~ (65536 <= a < 954368)).
{ rewrite (ly_img_lo L LY), (ly_img_hi L LY) in V1. intros a Ha. clear - Ha V1. lia. }
clear Q1 V1.
pose proof PA as (_ & PDEF & _).
set (s0 := PM.PST mo dn dp (PM.SRC qc de rem) tb tg vb vk stk) in *.
assert (PINC : incl (PM.parser_own s0) LB) by (unfold LB; apply incl_appl; apply incl_refl).
assert (AL36 : (fb + 40 + 24) mod 8 = 0) by (replace (fb + 40 + 24) with (fb + 8 * 8) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL1 : (fb + 8) mod 8 = 0) by (replace (fb + 8) with (fb + 8 * 1) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL55 : (fb + 440) mod 8 = 0) by (replace (fb + 440) with (fb + 8 * 55) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
set (WS := PMSP.W_srcf AD fb ++ [(qc, 16384)]).
assert (WCs : forall a, PMK.inW WS a -> (fb + 320 <= a < fb + 360) \/ (fb + 480 <= a < fb + 488) \/ (fb + 592 <= a < fb + 596) \/ (qc <= a < qc + 16384)).
{ intros a (r0 & Hin & Hr). unfold WS, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is in Hin. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S app] in Hin.
unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia. }
assert (WRH : forall i, PMK.inW (PMSP.W_run AD fb) i -> (fb + 8 <= i < fb + 24) \/ (fb + 48 <= i < fb + 56) \/ (fb + 320 <= i < fb + 360) \/ (fb + 376 <= i < fb + 424) \/ (fb + 480 <= i < fb + 488) \/ (fb + 592 <= i < fb + 596) \/ (0xc6260 <= i < 0xe7ec8)).
{ intros i (r0 & Hin & Hr). unfold PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_is, PMSP.o_p in Hin.
cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit AD PmLayoutS.ADDR_S app] in Hin. unfold L5.in_rng in Hr.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin. }
assert (NWS : forall a n, sp - 26624 <= a -> a + n <= fb + 320 -> forall i, a <= i < a + n -> ~ PMK.inW WS i).
{ intros a n H1 H2 i Hi I. apply WCs in I. clear - Hi H1 H2 I Q4 SLO. unfold hl_ceil in *. lia. }
assert (NWS2 : forall a n, fb + 360 <= a -> a + n <= fb + 480 -> forall i, a <= i < a + n -> ~ PMK.inW WS i).
{ intros a n H1 H2 i Hi I. apply WCs in I. clear - Hi H1 H2 I Q4 SLO F1. unfold hl_ceil in *. lia. }
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as B8.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as B18. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 20))) as B20.
change (bv_modulus 64) with (2 ^ 64) in *.
assert (REMB : 0 <= rem <= 16384).
{ pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _) & _). cbn [s0 PM.p_src PM.sr_qc PM.sr_de PM.sr_rem] in G1, G2, G3.
unfold PM.CHUNK in G3. lia. }
unfold PMSP.cfg. cbn [pa_read_key AD PmLayoutS.ADDR_S].
assert (OWNF : forall B m, In (B, m) (PM.parser_own s0) -> B + m <= hl_ceil L /\ (B + m <= hl_img_lo L \/ hl_img_hi L <= B) /\
forall B' m', In (B', m') LBX -> B + m <= B' \/ B' + m' <= B).
{ intros B m Hin. assert (HB : In (B, m) LB) by (apply PINC; exact Hin). destruct (BR B m HB) as (Z0 & Z1 & Z4).
split; [exact Z4|]. split; [exact Z1|]. intros B' m' Hin'.
assert (HB' : In (B', m') LB) by (unfold LB; apply in_or_app; right; exact Hin').
assert (NE : B <> B') by (apply (PMPK.fst_neq_app (PM.parser_own s0) LBX B m B' m' NDL Hin Hin')).
exact (PMPK.blocks_apart_heap L HI HIok LB cr M _ B m B' m' HH HB HB' NE). }
assert (FINW : forall M3 W3, PMK.ek L LB sp 26624 W3 M M3 -> PMK.dk L LB sp 26624 M M3 -> L5C.stk (hl_sptop L) M3 sp 26624 ->
(forall a, PMK.inW W3 a -> PMK.inW (PMSP.W_run AD fb) a \/ (qc <= a < qc + 16384)) ->
L5C.hpres L LBX sp 26624 (PMSP.W_run AD fb) M M3).
{ intros M3 W3 EK3 DK3 STK3 HW. apply (PMK.hpres_of L LBX sp 26624 _ M M3).
- apply (PMPK.ek_drop_own L (PM.parser_own s0) LBX sp 26624 (PMSP.W_run AD fb) W3 M M3 EK3 OWNF).
intros a O. destruct (PMK.rng_dec a qc (qc + 16384)) as [IQ|NQ].
+ right. exists qc, 16384. split; [unfold s0, PM.parser_own, PM.src_own; cbn; left; reflexivity| exact IQ].
+ left. intros r0 Hr0 Hin. destruct (HW a (ex_intro _ r0 (conj Hr0 Hin))) as [I'|I']; [exact (PMK.inW_not_outside _ a I' O)| exact (NQ I')].
- destruct STK3 as (_ & _ & _ & _ & D3). exact D3.
- apply (PMPK.dk_incl L LBX LB sp 26624 M M3 DK3). unfold LB. apply incl_appr. apply incl_refl. }
assert (WSR : forall a, PMK.inW WS a -> PMK.inW (PMSP.W_run AD fb) a \/ (qc <= a < qc + 16384)).
{ intros a I. apply WCs in I. destruct I as [I|[I|[I|I]]]; [left|left|left|right; exact I].
all: unfold PMSP.W_run, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is; cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S app].
- apply PMK.inW_next. apply PMK.inW_here. lia.
- do 2 apply PMK.inW_next. apply PMK.inW_here. lia.
- do 3 apply PMK.inW_next. apply PMK.inW_here. lia. }
assert (ERRP : forall (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (v : Z) (s1 : PM.pst) (sm1 : PM.strm) (e1 : bool) (cr1 : credit),
getr R1 (PMK.reg 1) = Z_to_bv 64 222824 -> getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 64) -> getr R1 (PMK.reg 8) = Z_to_bv 64 (fb + 40) ->
getr R1 (PMK.reg 9) = Z_to_bv 64 (fb + 8) -> getr R1 (PMK.reg 10) = Z_to_bv 64 (fb + 8) -> getr R1 (PMK.reg 11) = Z_to_bv 64 v ->
getr R1 (PMK.reg 18) = Z_to_bv 64 (fb + 432) ->
(forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (PMK.reg x) = getr R (PMK.reg x)) -> 1 <= v <= 64 ->
L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) -> L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) ->
L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) -> L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) ->
L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) -> L5.u64_at RSEGS M1 (sp - 48) (bv_unsigned (getr R (PMK.reg 20))) ->
PMSP.run_pre RSEGS AD M1 fb s1 str sm1 e1 -> PMSP.src_step (PM.p_src s0) (PM.p_src s1) (PM.STRM g eg st) sm1 -> (e = true -> e1 = true) ->
L5.defined M1 (fb + 8) 16 ->
L5C.hpres L LBX sp 26624 (PMSP.W_run AD fb) M M1 -> PMSP.credit_keep cr cr1 (PM.pot_parser L s0) (PM.pot_parser L s1) ->
model_but_vm model model1 -> hi_heap HI (PM.parser_own s1 ++ LBX) cr1 M1 (m_vmmaps model1) ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x36490 M1 model1) K).
{ intros fx1 R1 M1 model1 v s1 sm1 e1 cr1 X1 X2 X8 X9 X10 X11 X18 KS1 Hv C8 C16 C24 C32 C40 C48 RPRE1 STEP1 EE1 ED1 HP1 CK1 MB1 HH1.
pose proof (PMFR.model_ok_but_vm model model1 MOK MB1) as MOK1. pose proof MOK1 as (Mh1 & Ml1 & _).
destruct RPRE1 as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & TB1).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA1, IA1, VIS1, VREF1. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S] in PA1, IA1, VIS1, VREF1.
set (LB1 := PM.parser_own s1 ++ LBX) in *.
assert (BR1 : PMFR.brange L LB1) by (apply (PMFR.brange_of_heap L HI HIok LB1 LB1 cr1 M1 _ HH1); apply incl_refl).
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 26624) by (apply (PMK.stk_after RSEGS L KL LBX M M1 sp 26624 sp 26624 _ STK HP1); lia).
assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 64) 14336).
{ apply (PMK.stk_call L M1 sp 26624 (sp - 64) 14336 STK1); [lia|lia|lia|]. replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMS.make_ec_spec, PMSP.make_ec_spec in MKE. cbn [pa_make_ec AD PmLayoutS.ADDR_S] in MKE.
apply (MKE fx1 R1 M1 model1 K LB1 cr1 (fb + 8) v (sp - 64) 222824 e1 HH1 MOK1 K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [split; [lia| reflexivity]|]. split; [exact X2|].
split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKc. }
{ rewrite L5K.rl10. exact X10. } { rewrite L5K.rl11. exact X11. } { exact Hv. } { lia. } { lia. } { exact AL1. }
{ exact ED1. } { exact BASE1. } { exact ERR1. }
intros fx2 R2 M2 RP2 EC2 ERR2 HP2 HH2.
change (PMSP.pm_scr 1) with 14336 in HP2.
set (WE := (fb + 8, 16) :: (if e1 then [] else PMSP.err_W AD)) in HP2.
assert (WCE : forall a, PMK.inW WE a -> (fb + 8 <= a < fb + 24) \/ (0xc6260 <= a < 0xc6262) \/ (0xe7ca8 <= a < 0xe7ec8)).
{ intros a (r0 & Hin & Hr). unfold WE in Hin. destruct Hin as [<-|Hin]; [left; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia|]. destruct e1; [destruct Hin|].
unfold PMSP.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PmLayoutS.ADDR_S] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; right; [left|right]; lia. }
assert (WHIE : forall a, PMK.inW WE a -> (sp - 64) <= a \/ hl_img_lo L <= a < hl_img_hi L).
{ intros a I. apply WCE in I. rewrite (ly_img_lo L LY), (ly_img_hi L LY). destruct I as [I|[I|I]]; [left; lia| right; lia| right; lia]. }
assert (EKc : PMK.ek L LB1 (sp - 64) 14336 WE M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
assert (SCc : 0 <= 14336) by lia.
assert (HI2 : forall a n, sp - 64 <= a -> a + n <= fb + 8 -> L5C.agree_on M1 M2 a n).
{ intros a n H1 H2. apply (PMPK.ag_hi RSEGS L KL LB1 (sp - 64) 14336 WE M1 M2 EKc STKc SCc a n H1); [lia|]. intros i Hi I. apply WCE in I.
clear - Hi H1 H2 I SLO STOP. lia. }
assert (HI2' : forall a n, fb + 24 <= a -> a + n <= fb + 752 -> L5C.agree_on M1 M2 a n).
{ intros a n H1 H2. apply (PMPK.ag_hi RSEGS L KL LB1 (sp - 64) 14336 WE M1 M2 EKc STKc SCc a n); [lia|lia|]. intros i Hi I. apply WCE in I.
clear - Hi H1 H2 I F1 F2 SLO STOP. lia. }
assert (STK2 : L5C.stk (hl_sptop L) M2 sp 26624) by (apply (PMK.stk_after RSEGS L KL LB1 M1 M2 sp 26624 (sp - 64) 14336 WE STK1 HP2); lia).
pose proof (L5C.stk_writable RSEGS _ M2 sp 26624 STK2) as WR2.
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
assert (QIN1 : In (PM.sr_qc src1, 16384) LB1) by (unfold LB1, PM.parser_own, PM.src_own; cbn; left; reflexivity).
assert (VIN1 : In (vb1, 32 * 2 ^ vk1) LB1) by (unfold LB1, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (BR1 _ _ VIN1) as (W0 & W1' & W4). unfold hl_ceil in W4.
assert (VI1 : forall a, vb1 <= a < vb1 + 32 * 2 ^ vk1 -> ~ (65536 <= a < 954368)).
{ rewrite (ly_img_lo L LY), (ly_img_hi L LY) in W1'. intros a Ha. clear - Ha W1'. lia. }
assert (PA2 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M2 (fb + 40) (fb + 440) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1)).
{ apply (PMPK.parser_at_keep RSEGS AD M1 M2 (fb + 40) (fb + 440) _ PA1); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
- lia.
- lia.
- apply HI2'; lia.
- apply (PMPK.dkr_hpres_blk RSEGS L KL LB1 (sp - 64) 14336 WE M1 M2 (PM.sr_qc src1) 16384 HP2 QIN1 BR1). lia.
- lia.
- clear - W4 STOP. unfold hl_ceil in *. lia.
- apply (PMPK.ag_blk RSEGS L KL LB1 (sp - 64) 14336 WE M1 M2 EKc STKc BR1 vb1 (32 * 2 ^ vk1) VIN1).
intros i Hi I. apply WCE in I. destruct I as [I|I]; [clear - Hi I W4 SLO F1; unfold hl_ceil in *; lia| apply (VI1 i Hi); clear - I; lia].
- intros c0 n0 q0 E0. apply (PMPK.dkr_hpres_blk RSEGS L KL LB1 (sp - 64) 14336 WE M1 M2 q0 c0 HP2); [|exact BR1|lia].
unfold LB1, PM.parser_own, PM.vs_own. cbn [PM.p_tb]. rewrite E0. cbn. right. right. left. reflexivity. }
assert (SINC1 : incl (PM.vs_own str) LB1) by (unfold LB1; apply incl_appr; exact INCS).
assert (IA2 : PM.iss_at RSEGS AD PMSP.T3 M2 (fb + 440) str sm1).
{ apply (PMFR.iss_keep RSEGS AD L KL LB1 (sp - 64) 14336 WE M1 M2 EKc STKc SCc BR1 WHIE); [lia|lia| |exact SINC1| exact IA1].
intros i Hi I. apply WCE in I. clear - Hi I F1 F2 SLO STOP. lia. }
assert (BASE2 : PMST.base_ok RSEGS AD M2).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB1 (sp - 64) 14336 WE M1 M2 EKc); [| | | | exact BASE1].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WCE in I; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S] in Ha.
all: clear - I Ha SLO STOP F1; lia. }
assert (RP2_ : forall k, In k PMK.cs_all -> getr R2 (PMK.reg k) = getr R1 (PMK.reg k)) by (intros k Hk; apply (PMK.cs_of_preserved R1 R2 k RP2 Hk)).
cfeed P (PMSRKP.rkZ_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
| 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => bv_unsigned (getr R (PMK.reg 20)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRKP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54]
| (apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia|assumption])
| (apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M2 (fb + 40) 384); [destruct PA2 as (_ & PD2 & _); exact PD2|lia|lia]|lia|lia]) ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T2 & T8 & T9 & T18 & T19 & T20 & Z8)); PMK.pvz_clrT.
rewrite PMPK.word_id in T1, T8, T9, T18, T19, T20.
apply (gl_step LB1 cr1 fx2 fx3 R2 R3 0x36668 0x36688 M2 M3 model1 K sp (fb + 40 + 8) 1 HH2 Mh1 Ml1 ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(right; unfold hl_ceil; lia) MS3 MG3 (fun i Hi _ N2 => FRZ3 i Hi N2)).
intros HH3.
unfold PMSP.cfg.
eapply (L5.cps_of_msteps RSEGS); [exact Mh1| exact Ml1| |].
{ apply (PMK.ret_to RSEGS fx3 R3 M3 0x36688 (ltac:(oW' 0x36688%Z)) r (ltac:(oF' 0x36688%Z)) eq_refl (ltac:(oD' 0x36688%Z))); [rewrite T1; exact Rra| lia| exact Hr2]. }
assert (AG3 : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 48 \/ fb + 49 <= a) -> L5C.agree_on M2 M3 a n).
{ intros a n H1 H2 H4 i Hi. apply FRZ3; [clear - H1 H2 Hi; lia| clear - H4 Hi; lia]. }
assert (EK3 : PMK.ek L LB1 sp 26624 [(fb + 48, 1)] M2 M3).
{ apply (gl_ek LB1 sp (fb + 40 + 8) 1 [(fb + 48, 1)] M2 M3 (fun i Hi _ N2 => FRZ3 i Hi N2) STK2 BR1). intros a Ha. apply PMK.inW_here. lia. }
assert (STK3 : L5C.stk (hl_sptop L) M3 sp 26624) by (apply (PMK.stk_grows L M2 M3 sp 26624 MG3 STK2)).
assert (AGH : forall a n, sp <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ PMK.inW (PMSP.W_run AD fb) i) -> L5C.agree_on M1 M3 a n).
{ intros a n H1 H2 N. apply (L5C.agree_on_trans M1 M2 M3).
- apply (PMPK.ag_hi RSEGS L KL LB1 (sp - 64) 14336 WE M1 M2 EKc STKc SCc a n); [lia|lia|]. intros i Hi I. apply (N i Hi).
apply WCE in I. unfold PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_is, PMSP.o_p.
cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit AD PmLayoutS.ADDR_S app].
destruct I as [I|[I|I]]; [do 6 apply PMK.inW_next; apply PMK.inW_here; lia| do 7 apply PMK.inW_next; apply PMK.inW_here; lia| do 8 apply PMK.inW_next; apply PMK.inW_here; lia].
- intros i Hi. apply FRZ3; [lia|]. intros X. apply (N i Hi). unfold PMSP.W_run, PMSP.o_p. cbn [pa_off_p AD PmLayoutS.ADDR_S app]. apply PMK.inW_here. lia. }
apply (KONT fx3 R3 M3 model1 (PMPK.set_more (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) 0) sm1 true cr1).
- apply PMK.preserved_by_index. intros k Hk. cbn in Hk.
repeat (destruct Hk as [<-|Hk]; [first [ rewrite T2; symmetry; exact Rsp | assumption | (rewrite (KS3 _) by PMK.inl; rewrite RP2_ by PMK.inl; apply KS1; PMK.inl) ] |]).
destruct Hk.
- unfold PMSP.run_post, PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_is pa_off_v pa_off_ec AD PmLayoutS.ADDR_S].
split; [|split; [exact STEP1|split; [intros _; reflexivity| left]]].
+ split.
{ apply (PMPK.parser_more_upd RSEGS AD M2 M3 (fb + 40) (fb + 440) _ 0 PA2); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
- lia.
- lia.
- apply AG3; lia.
- apply AG3; lia.
- apply PMPK.dkr_grows. exact MG3.
- exact Z8.
- left. reflexivity.
- apply PMPK.dkr_grows. exact MG3.
- lia.
- clear - W4 STOP. unfold hl_ceil in *. lia.
- apply AG3; [lia|clear - W4 STOP; unfold hl_ceil in *; lia| clear - W4 SLO F1; unfold hl_ceil in *; lia].
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG3. }
split.
{ apply (PMFR.iss_keep RSEGS AD L KL LB1 sp 26624 [(fb + 48, 1)] M2 M3 EK3 STK2 SC0 BR1); [intros a I; apply PMFR.inW_inv1 in I; left; lia|lia|lia| |exact SINC1| exact IA2].
intros i Hi I. apply PMFR.inW_inv1 in I. lia. }
split.
{ unfold PMSP.visitor_at in *. apply (L5C.u64_at_agree RSEGS M1 M3); [apply AGH; [lia|lia|]|lia|lia| exact VIS1].
intros i Hi I. apply WRH in I. clear - Hi I F1 SLO STOP. lia. }
split.
{ apply (L5C.u64_at_agree RSEGS M1 M3); [apply AGH; [lia|lia|]|lia|lia| exact VREF1].
intros i Hi I. apply WRH in I. clear - Hi I F1 SLO STOP. lia. }
split.
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB1 sp 26624 [(fb + 48, 1)] M2 M3 EK3); [| | | | exact BASE2].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply PMFR.inW_inv1 in I;
cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S] in Ha; clear - I Ha SLO STOP F1; lia. }
split; [|exact TB1].
{ apply (PMKP.err_ok_keep RSEGS AD L KL SF LB1 sp 26624 [(fb + 48, 1)] M2 M3 EK3); [| | exact ERR2].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply PMFR.inW_inv1 in I;
cbn [pa_errcat_guard pa_atexit AD PmLayoutS.ADDR_S] in Ha; clear - I Ha SLO STOP F1; lia. }
+ exists v. split; [exact Hv|]. split; [|split; reflexivity].
apply (ec_agree M2 M3); [apply AG3; lia|lia|lia| exact EC2].
- apply (PMK.hpres_of L LBX sp 26624 _ M M3).
+ apply (PMK.ek_trans L LBX sp 26624 _ M M1 M3 (PMK.ek_of_hpres L LBX sp 26624 _ M M1 HP1)).
apply (PMK.ek_trans L LBX sp 26624 _ M1 M2 M3).
{ apply (PMK.ek_callee_in' RSEGS L KL LBX LB1 sp 26624 (sp - 64) 14336 _ WE M1 M2 HP2); [unfold LB1; apply incl_appr; apply incl_refl|lia|lia|unfold hl_ceil; lia|lia|
exact (PMFR.brange_hi L LBX (PMFR.brange_incl L LBX LB1 BR1 ltac:(unfold LB1; apply incl_appr; apply incl_refl)))|].
intros a I. right. apply WCE in I. unfold PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_is, PMSP.o_p.
cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit AD PmLayoutS.ADDR_S app].
destruct I as [I|[I|I]]; [do 6 apply PMK.inW_next; apply PMK.inW_here; lia| do 7 apply PMK.inW_next; apply PMK.inW_here; lia| do 8 apply PMK.inW_next; apply PMK.inW_here; lia]. }
apply (PMK.ek_weaken L LBX LB1 sp 26624 sp 26624 _ [(fb + 48, 1)] M2 M3 EK3); [unfold LB1; apply incl_appr; apply incl_refl| intros x Hx; exact Hx|].
intros a O r0 Hr0 Hin. destruct Hr0 as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
unfold PMSP.W_run, PMSP.o_p in O. cbn [pa_off_p AD PmLayoutS.ADDR_S app] in O. apply (O (fb + 40 + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
+ destruct STK3 as (_ & _ & _ & _ & D3). exact D3.
+ apply (PMK.dk_trans L LBX sp 26624 M M1 M3 (PMK.dk_of_hpres L LBX sp 26624 _ M M1 HP1)). apply (PMK.dk_trans L LBX sp 26624 M1 M2 M3).
{ apply (PMK.dk_callee L LBX LB1 sp 26624 (sp - 64) 14336 WE M1 M2 HP2); [unfold LB1; apply incl_appr; apply incl_refl|lia|lia]. }
apply (PMK.dk_grows L LBX sp 26624 M2 M3 MG3).
- exact CK1.
- exact MB1.
- exact HH3. }
assert (BRX : PMFR.brange L LBX) by (apply (PMFR.brange_incl L LBX LB BR); unfold LB; apply incl_appr; apply incl_refl).
assert (KPM0 : 0 <= hl_k_per_malloc L) by (pose proof (ly_kpm L LY); lia).
assert (BOV0 : 0 <= hl_b_overhead L) by (pose proof (ly_bov L LY); lia).
assert (KEEPX : forall sp' scr' M1 M2, L5C.hpres L LBX sp' scr' (PMSP.W_run AD fb) M1 M2 -> L5C.stk (hl_sptop L) M1 sp' scr' -> 0 <= scr' ->
sp - 64 <= sp' -> forall a n, sp' <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 8 \/ (fb + 424 <= a /\ a + n <= fb + 440)) -> L5C.agree_on M1 M2 a n).
{ intros sp' scr' M1 M2 HP ST S0 H0 a n H1 H2 H3. apply (PMPK.ag_hi RSEGS L KL LBX sp' scr' (PMSP.W_run AD fb) M1 M2 (PMK.ek_of_hpres L LBX sp' scr' _ M1 M2 HP) ST S0 a n H1 H2).
intros i Hi I. apply WRH in I. clear - Hi I H3 F1 SLO STOP H0 H1. lia. }
cfeed P (PMSRKP.rkA_conc fx R M (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRKP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54]]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X11 & X18 & C48 & C40 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
apply (gl_step LB cr fx fx1 R R1 0x365f0 0x36cf8 M M1 model K sp 0 0 HH Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(left; reflexivity) MS1 MG1 (fun i Hi N1 _ => FRZ1 i Hi N1)).
intros HH1.
assert (EK1f : PMK.ek L LB sp 26624 [] M M1).
{ apply (PMFR.ek_of_piece RSEGS L KL LB sp 26624 M M1 (fun a => sp - 64 <= a < sp - 64 + 64) ltac:(intros a Ha N; apply FRZ1; [exact Ha| exact N]) STK (PMFR.brange_hi L LB BR)). intros a Pa. lia. }
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 26624) by (apply (PMK.stk_grows L M M1 sp 26624 MG1 STK)).
assert (WHI0 : forall a, PMK.inW [] a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
assert (AG01 : forall a n, sp <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M M1 a n) by (intros a n H1 H2 i Hi; apply FRZ1; lia).
assert (HP01 : L5C.hpres L LBX sp 26624 (PMSP.W_run AD fb) M M1).
{ apply (PMK.hpres_of L LBX sp 26624 _ M M1).
- apply (PMK.ek_weaken L LBX LB sp 26624 sp 26624 _ [] M M1 EK1f); [unfold LB; apply incl_appr; apply incl_refl| intros x Hx; exact Hx|]. intros a _. apply L5C.outside_nil.
- destruct STK1 as (_ & _ & _ & _ & D1). exact D1.
- apply (PMK.dk_grows L LBX sp 26624 M M1 MG1). }
assert (STKg : L5C.stk (hl_sptop L) M1 (sp - 64) 22528).
{ apply (PMK.stk_call L M1 sp 26624 (sp - 64) 22528 STK1); [lia|lia|lia|]. replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMS.get_length_spec, PMSP.get_length_spec, PMSP.run_spec_r in GL. cbn [pa_get_length AD PmLayoutS.ADDR_S] in GL.
apply (GL 0 ltac:(lia) fx1 R1 M1 model K LBX cr (sp - 64) 222752 fb cat s0 str (PM.STRM g eg st) e HH1 MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [split; [lia| reflexivity]|]. split; [exact X2|].
split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKg. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutS.ADDR_S]. split; [lia|]. split; [lia| exact F3]. }
{ unfold PMSP.args_gl, PMSP.o_p, PMSP.o_ec. cbn [pa_off_p pa_off_ec AD PmLayoutS.ADDR_S]. rewrite L5K.rl10, L5K.rl11. split; [rewrite (KS1 10%nat) by PMK.inl; exact A10| exact X11]. }
{ unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S].
split; [apply (PMFR.parser_keep RSEGS AD L KL LB sp 26624 [] M M1 EK1f STK SC0 BR WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| exact PINC| exact PA]|].
split; [apply (PMFR.iss_keep RSEGS AD L KL LB sp 26624 [] M M1 EK1f STK SC0 BR WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| exact SINC| exact IA]|].
split; [unfold PMSP.visitor_at in *; apply (L5C.u64_at_agree RSEGS M M1); [apply AG01; lia|lia|lia| exact VIS]|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG01; lia|lia|lia| exact VREF]|].
split; [apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 26624 [] M M1 EK1f); first [exact BASE | intros a _; apply L5C.outside_nil]|].
split; [apply (PMKP.err_ok_keep RSEGS AD L KL SF LB sp 26624 [] M M1 EK1f); first [exact ERR | intros a _; apply L5C.outside_nil]| exact TBOK]. }
{ exact INCS. } { exact (proj1 (PM.inv_d0 _) INV). }
{ unfold PMSP.o_ec. cbn [pa_off_ec AD PmLayoutS.ADDR_S]. apply (ec_agree M M1); [apply AG01; lia|lia|lia| exact EC0]. }
{ exact UNR. } { exact CRED. }
intros fx2 R2 M2 model2 s2 sm2 e2 cr2 RP2 RPOST2 HP2 CK2 MB2 HH2. unfold PMSP.cfg.
change (PMSP.pm_scr 5) with 22528 in HP2.
pose proof (PMFR.model_ok_but_vm model model2 MOK MB2) as MOK2. pose proof MOK2 as (Mh2 & Ml2 & _).
assert (STK2 : L5C.stk (hl_sptop L) M2 sp 26624) by (apply (PMK.stk_after RSEGS L KL LBX M1 M2 sp 26624 (sp - 64) 22528 _ STK1 HP2); lia).
pose proof STK2 as (_ & _ & _ & _ & SD2). pose proof (L5C.stk_writable RSEGS _ M2 sp 26624 STK2) as WR2.
assert (HP02 : L5C.hpres L LBX sp 26624 (PMSP.W_run AD fb) M M2).
{ apply (PMK.hpres_of L LBX sp 26624 _ M M2).
- apply (PMK.ek_trans L LBX sp 26624 _ M M1 M2 (PMK.ek_of_hpres L LBX sp 26624 _ M M1 HP01)).
apply (PMK.ek_callee_in' RSEGS L KL LBX LBX sp 26624 (sp - 64) 22528 _ _ M1 M2 HP2 (incl_refl _)); [lia|lia|unfold hl_ceil; lia|lia| exact (PMFR.brange_hi L LBX BRX)|].
intros a I. right. exact I.
- exact SD2.
- apply (PMK.dk_trans L LBX sp 26624 M M1 M2 (PMK.dk_of_hpres L LBX sp 26624 _ M M1 HP01)).
apply (PMK.dk_callee L LBX LBX sp 26624 (sp - 64) 22528 _ M1 M2 HP2 (incl_refl _)); lia. }
assert (AG12 : forall a n, sp - 64 <= a -> a + n <= fb + 8 -> L5C.agree_on M1 M2 a n).
{ intros a n H1 H2. apply (KEEPX (sp - 64) 22528 M1 M2 HP2 STKg ltac:(lia) ltac:(lia) a n H1); lia. }
assert (D8 : L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG12; lia|lia|lia| exact C8]).
assert (D16 : L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG12; lia|lia|lia| exact C16]).
assert (D24 : L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG12; lia|lia|lia| exact C24]).
assert (D32 : L5.u64_at RSEGS M2 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG12; lia|lia|lia| exact C32]).
assert (D40 : L5.u64_at RSEGS M2 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG12; lia|lia|lia| exact C40]).
assert (D48 : L5.u64_at RSEGS M2 (sp - 48) (bv_unsigned (getr R (PMK.reg 20)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG12; lia|lia|lia| exact C48]).
assert (R1x : forall x, In x [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (PMK.reg x) = getr R (PMK.reg x)).
{ intros x Hx. apply KS1. revert x Hx. apply (PMPK.sub_in PMSRKP.KS_rkA). vm_compute. reflexivity. }
assert (R2x : forall x, In x [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (PMK.reg x) = getr R (PMK.reg x)).
{ intros x Hx. rewrite (PMK.cs_of_preserved R1 R2 x RP2) by (revert x Hx; apply (PMPK.sub_in PMK.cs_all); vm_compute; reflexivity). apply R1x. exact Hx. }
assert (R2_2 : getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 64)) by (rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl; exact X2).
assert (R2_8 : getr R2 (PMK.reg 8) = Z_to_bv 64 (fb + 40)) by (rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl; exact X8).
assert (R2_9 : getr R2 (PMK.reg 9) = Z_to_bv 64 (fb + 8)) by (rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl; exact X9).
assert (R2_18 : getr R2 (PMK.reg 18) = Z_to_bv 64 (fb + 432)) by (rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl; exact X18).
clear X1 X2 X8 X9 X11 X18 KS1 R1x RP2 C8 C16 C24 C32 C40 C48.
destruct RPOST2 as (RPRE2 & STEP2 & EE2 & POST2).
pose proof (bv_unsigned_in_range 64 (getr R2 (PMK.reg 10))) as BL. change (bv_modulus 64) with (2 ^ 64) in BL.
destruct POST2 as [(v & Hv & ECv & MO2 & E2t)|(EC2 & INV2 & PLEN)].
all: try (apply (proj2 (PM.inv_d0 _)) in INV2).
-
destruct ECv as (ECv0 & _ & ECvD). unfold PMSP.o_ec in ECv0, ECvD. cbn [pa_off_ec AD PmLayoutS.ADDR_S] in ECv0, ECvD.
cfeed P (PMSRKP.rkE_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => bv_unsigned (getr R2 (PMK.reg 10)) | 36%nat => fb + 40 | 37%nat => fb + 432
| 38%nat => fb + 8 | 39%nat => v | _ => 0 end)) ltac:(first [PMK.sc | (symmetry; apply PMPK.word_id) | unfold PMSRKP.aligned; first [exact A16 | exact AL5 | exact AL1]]).
destruct P as (fx3 & R3 & M3 & MG3 & FR3 & _ & MS3 & KS3 & T1 & T10 & T11).
assert (M3 = M2) as -> by (apply functional_extensionality; exact FR3).
apply (PMK.spiece_ro RSEGS model2 fx2 fx3 R2 0x36620 R3 0x36490 M2 K Mh2 Ml2 MS3).
apply (ERRP fx3 R3 M2 model2 12 s2 sm2 e2 cr2 T1); try gl_disp.
-
destruct EC2 as (EC20 & EC28 & EC2D). unfold PMSP.o_ec in EC20, EC28, EC2D. cbn [pa_off_ec AD PmLayoutS.ADDR_S] in EC20, EC28, EC2D.
set (len := bv_unsigned (getr R2 (PMK.reg 10))) in *.
cfeed P (PMSRKP.rkB_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => len | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) ltac:(first [PMK.sc | (unfold len; symmetry; apply PMPK.word_id) | unfold PMSRKP.aligned; first [exact A16 | exact AL5 | exact AL1]]).
destruct P as (fx3 & R3 & M3 & MG3 & FR3 & _ & MS3 & KS3 & T1 & T10 & T11 & T12 & T19).
assert (M3 = M2) as -> by (apply functional_extensionality; exact FR3).
apply (PMK.spiece_ro RSEGS model2 fx2 fx3 R2 0x36620 R3 0x36f04 M2 K Mh2 Ml2 MS3).
destruct RPRE2 as (PA2 & IA2 & VIS2 & VREF2 & BASE2 & ERR2 & TB2).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA2, IA2, VIS2, VREF2. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S] in PA2, IA2, VIS2, VREF2.
assert (STKr : L5C.stk (hl_sptop L) M2 (sp - 64) 24576).
{ apply (PMK.stk_call L M2 sp 26624 (sp - 64) 24576 STK2); [lia|lia|lia|]. replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
assert (CR2 : PMSP.credit_le (PM.pot_parser L s2) cr2) by (apply (PMPK.credit_le_keep cr cr2 _ _ CRED CK2)).
assert (HK2 : 0 <= PM.p_k s2 <= 11) by (destruct PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & Hk2 & _) & _); exact Hk2).
unfold PMS.read_span_spec, PMSP.read_span_spec in RS. cbn [pa_read_span AD PmLayoutS.ADDR_S] in RS.
apply (RS fx3 R3 M2 model2 K LBX cr2 (sp - 64) 222780 fb len s2 str sm2 HH2 MOK2 K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact T1|]. split; [split; [lia| reflexivity]|].
split; [rewrite (KS3 2%nat) by PMK.inl; exact R2_2|]. split; [rewrite (KS3 3%nat) by PMK.inl; rewrite R2x by PMK.inl; exact Rgp|].
split; [rewrite (KS3 4%nat) by PMK.inl; rewrite R2x by PMK.inl; exact Rtp|]. exact STKr. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutS.ADDR_S]. split; [lia|]. split; [lia| exact F3]. }
{ rewrite L5K.rl10. unfold PMSP.o_src, PMSP.o_p. cbn [pa_off_p AD PmLayoutS.ADDR_S]. exact T10. }
{ rewrite L5K.rl11. exact T11. }
{ rewrite L5K.rl12. unfold PMSP.o_tb, PMSP.o_p. cbn [pa_off_p AD PmLayoutS.ADDR_S]. replace (fb + 40 + 336) with (fb + 40 + 336) by lia. exact T12. }
{ unfold len. lia. }
{ unfold PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S]. exact PA2. }
{ unfold PMSP.o_is. cbn [pa_off_is AD PmLayoutS.ADDR_S]. exact IA2. }
{ exact BASE2. } { exact TB2. } { exact INCS. }
{ destruct PLEN as (_ & UL & _). unfold PM.unread in UL, UNR |- *. cbn [s0 PM.p_src PM.sr_rem PM.sm_eg PM.sm_g] in UL, UNR |- *. lia. }
{ apply (PMPK.pot_text_le_parser L s2 cr2 KPM0 BOV0 HK2 CR2). }
intros fx4 R4 M4 model4 s4 sm4 cr4 ptr n RP4 Y10 Y11 Hn Hn26 LOC DEF4 PA4 IA4 TB4 EM4 ED4 EDP4 EB4 EPK4 ESTK4 STEP4 HP4 CK4 MB4 HH4.
unfold PMSP.cfg.
change (PMSP.pm_scr 6) with 24576 in HP4.
rewrite L5K.rl10 in Y10. rewrite L5K.rl11 in Y11.
unfold PMSP.o_p, PMSP.o_is, PMSP.o_tb in PA4, IA4, LOC, HP4. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S] in PA4, IA4, LOC, HP4.
pose proof (PMFR.model_ok_but_vm model2 model4 MOK2 MB4) as MOK4. pose proof MOK4 as (Mh4 & Ml4 & _).
assert (MB04 : model_but_vm model model4) by (apply (L5C.model_but_vm_trans model model2 model4 MB2 MB4)).
set (Wr := PMSP.W_srcf AD fb ++ [(fb + 40 + 336, 24)]) in HP4.
assert (WCr : forall a, PMK.inW Wr a -> (fb + 320 <= a < fb + 360) \/ (fb + 480 <= a < fb + 488) \/ (fb + 592 <= a < fb + 596) \/ (fb + 376 <= a < fb + 400)).
{ intros a (r0 & Hin & Hr). unfold Wr, PMSP.W_srcf, PMSP.o_src, PMSP.o_is, PMSP.o_p in Hin. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S app] in Hin.
unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia. }
assert (EK4 : PMK.ek L LBX (sp - 64) 24576 Wr M2 M4) by (apply (PMK.ek_of_hpres L); exact HP4).
assert (HP4w : L5C.hpres L LBX (sp - 64) 24576 (PMSP.W_run AD fb) M2 M4).
{ apply (PMK.hpres_of L LBX (sp - 64) 24576 _ M2 M4).
- apply (PMK.ek_weaken L LBX LBX (sp - 64) 24576 (sp - 64) 24576 _ Wr M2 M4 EK4); [apply incl_refl| intros x Hx; exact Hx|].
intros a O r0 Hr0 Hin. apply (PMK.inW_not_outside (PMSP.W_run AD fb) a); [|exact O].
assert (X : PMK.inW Wr a) by (exists r0; split; assumption). apply WCr in X.
unfold PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_is, PMSP.o_p.
cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit AD PmLayoutS.ADDR_S app].
destruct X as [X|[X|[X|X]]]; [do 1 apply PMK.inW_next; apply PMK.inW_here; lia| do 2 apply PMK.inW_next; apply PMK.inW_here; lia
| do 3 apply PMK.inW_next; apply PMK.inW_here; lia| do 4 apply PMK.inW_next; apply PMK.inW_here; lia].
- exact (L5C.hpres_defined L LBX (sp - 64) 24576 Wr M2 M4 HP4).
- exact (PMK.dk_of_hpres L LBX (sp - 64) 24576 Wr M2 M4 HP4). }
assert (STK4 : L5C.stk (hl_sptop L) M4 sp 26624) by (apply (PMK.stk_after RSEGS L KL LBX M2 M4 sp 26624 (sp - 64) 24576 _ STK2 HP4w); lia).
pose proof STK4 as (_ & _ & _ & _ & SD4). pose proof (L5C.stk_writable RSEGS _ M4 sp 26624 STK4) as WR4.
assert (HP04 : L5C.hpres L LBX sp 26624 (PMSP.W_run AD fb) M M4).
{ apply (PMK.hpres_of L LBX sp 26624 _ M M4).
- apply (PMK.ek_trans L LBX sp 26624 _ M M2 M4 (PMK.ek_of_hpres L LBX sp 26624 _ M M2 HP02)).
apply (PMK.ek_callee_in' RSEGS L KL LBX LBX sp 26624 (sp - 64) 24576 _ _ M2 M4 HP4w (incl_refl _)); [lia|lia|unfold hl_ceil; lia|lia| exact (PMFR.brange_hi L LBX BRX)|].
intros a I. right. exact I.
- exact SD4.
- apply (PMK.dk_trans L LBX sp 26624 M M2 M4 (PMK.dk_of_hpres L LBX sp 26624 _ M M2 HP02)).
apply (PMK.dk_callee L LBX LBX sp 26624 (sp - 64) 24576 _ M2 M4 HP4w (incl_refl _)); lia. }
assert (STKr2 : L5C.stk (hl_sptop L) M2 (sp - 64) 24576) by exact STKr.
assert (AG24 : forall a nn, sp - 64 <= a -> a + nn <= 2 ^ 64 -> (forall i, a <= i < a + nn -> ~ PMK.inW Wr i) -> L5C.agree_on M2 M4 a nn).
{ intros a nn H1 H2 N. apply (PMPK.ag_hi RSEGS L KL LBX (sp - 64) 24576 Wr M2 M4 EK4 STKr2 ltac:(lia) a nn H1 H2 N). }
assert (NWr : forall a nn, (sp - 64 <= a /\ a + nn <= fb + 320) \/ (fb + 424 <= a /\ a + nn <= fb + 480) -> forall i, a <= i < a + nn -> ~ PMK.inW Wr i).
{ intros a nn H i Hi I. apply WCr in I. clear - H Hi I. lia. }
assert (E8 : L5.u64_at RSEGS M4 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by (apply (L5C.u64_at_agree RSEGS M2 M4); [apply AG24; [lia|lia| apply NWr; lia]|lia|lia| exact D8]).
assert (E16 : L5.u64_at RSEGS M4 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))) by (apply (L5C.u64_at_agree RSEGS M2 M4); [apply AG24; [lia|lia| apply NWr; lia]|lia|lia| exact D16]).
assert (E24 : L5.u64_at RSEGS M4 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))) by (apply (L5C.u64_at_agree RSEGS M2 M4); [apply AG24; [lia|lia| apply NWr; lia]|lia|lia| exact D24]).
assert (E32 : L5.u64_at RSEGS M4 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))) by (apply (L5C.u64_at_agree RSEGS M2 M4); [apply AG24; [lia|lia| apply NWr; lia]|lia|lia| exact D32]).
assert (E40 : L5.u64_at RSEGS M4 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))) by (apply (L5C.u64_at_agree RSEGS M2 M4); [apply AG24; [lia|lia| apply NWr; lia]|lia|lia| exact D40]).
assert (E48 : L5.u64_at RSEGS M4 (sp - 48) (bv_unsigned (getr R (PMK.reg 20)))) by (apply (L5C.u64_at_agree RSEGS M2 M4); [apply AG24; [lia|lia| apply NWr; lia]|lia|lia| exact D48]).
assert (VIS4 : L5.u64_at RSEGS M4 (fb + 432) (pa_vp_visitor AD)) by (unfold PMSP.visitor_at in VIS2; apply (L5C.u64_at_agree RSEGS M2 M4); [apply AG24; [lia|lia| apply NWr; lia]|lia|lia| exact VIS2]).
assert (VREF4 : L5.u64_at RSEGS M4 (fb + 40 + 384) (fb + 432)) by (apply (L5C.u64_at_agree RSEGS M2 M4); [apply AG24; [lia|lia| apply NWr; lia]|lia|lia| exact VREF2]).
assert (EC4 : PMSP.ec_at RSEGS M4 (fb + 8) 0 cat) by (apply (ec_agree M2 M4); [apply AG24; [lia|lia| apply NWr; lia]|lia|lia| split; [exact EC20| split; [exact EC28| exact EC2D]]]).
assert (BASE4 : PMST.base_ok RSEGS AD M4).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LBX (sp - 64) 24576 Wr M2 M4 EK4); [| | | | exact BASE2].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WCr in I; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S] in Ha.
all: clear - I Ha SLO STOP F1; lia. }
assert (ERR4 : PMST.err_ok RSEGS AD M4 e2).
{ apply (PMKP.err_ok_keep RSEGS AD L KL SF LBX (sp - 64) 24576 Wr M2 M4 EK4); [| | exact ERR2].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WCr in I; cbn [pa_errcat_guard pa_atexit AD PmLayoutS.ADDR_S] in Ha.
all: clear - I Ha SLO STOP F1; lia. }
assert (RPRE4 : PMSP.run_pre RSEGS AD M4 fb s4 str sm4 e2).
{ unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S].
split; [exact PA4|]. split; [exact IA4|]. split; [exact VIS4|]. split; [exact VREF4|]. split; [exact BASE4|]. split; [exact ERR4| exact TB4]. }
pose proof (proj2 (proj2 EC4)) as ED4e.
assert (STEP04 : PMSP.src_step (PM.p_src s0) (PM.p_src s4) (PM.STRM g eg st) sm4) by (apply (PMPK.src_step_trans _ _ _ _ _ _ STEP2 STEP4)).
assert (CK04 : PMSP.credit_keep cr cr4 (PM.pot_parser L s0) (PM.pot_parser L s4)) by (apply (PMPK.credit_keep_text L cr cr2 cr4 s0 s2 s4 CK2 CK4 EPK4)).
assert (R3_19 : getr R3 (PMK.reg 19) = Z_to_bv 64 len) by exact T19.
assert (RP4_ : forall k, In k PMK.cs_all -> getr R4 (PMK.reg k) = getr R3 (PMK.reg k)) by (intros k Hk; apply (PMK.cs_of_preserved R3 R4 k RP4 Hk)).
pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 n)) as BN. change (bv_modulus 64) with (2 ^ 64) in BN. rewrite L5.unsigned_lit in BN by lia.
pose proof (PMSRKP.rkF_conc fx4 R4 M4 (fun j => match j with 2%nat => sp | 33%nat => len | 34%nat => bv_unsigned (getr R4 (PMK.reg 10)) | 35%nat => n
| 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) as P. cbn beta iota in P.
pose proof (bv_unsigned_in_range 64 (getr R4 (PMK.reg 10))) as BP. change (bv_modulus 64) with (2 ^ 64) in BP.
PMK.feed P ltac:(first [PMK.sc | (symmetry; apply PMPK.word_id) | unfold PMSRKP.aligned; first [exact A16 | exact AL5 | exact AL1]]).
destruct P as (fx5 & R5 & M5 & MG5 & FR5 & _ & EX5).
assert (M5 = M4) as -> by (apply functional_extensionality; exact FR5).
destruct EX5 as [(MS5 & KS5 & W1 & W11 & W20 & BF)|(MS5 & KS5 & W1 & W10 & W11 & BF)].
2:{
apply (PMK.spiece_ro RSEGS model4 fx4 fx5 R4 0x3663c R5 0x36490 M4 K Mh4 Ml4 MS5).
apply (ERRP fx5 R5 M4 model4 1 s4 sm4 e2 cr4 W1); try gl_disp. }
assert (NL : n = len).
{ clear - BF BN BL Hn. unfold len in *. destruct (Z.eq_dec n (bv_unsigned (getr R2 (PMK.reg 10)))) as [E|E]; [exact E|]. exfalso.
assert (X : (n - bv_unsigned (getr R2 (PMK.reg 10))) mod 2 ^ 64 = n - bv_unsigned (getr R2 (PMK.reg 10)) + 2 ^ 64).
{ rewrite <- (Z.mod_add (n - bv_unsigned (getr R2 (PMK.reg 10))) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
lia. }
subst n.
apply (PMK.spiece_ro RSEGS model4 fx4 fx5 R4 0x3663c R5 0x36aec M4 K Mh4 Ml4 MS5).
assert (STKv : L5C.stk (hl_sptop L) M4 (sp - 64) 12288).
{ apply (PMK.stk_call L M4 sp 26624 (sp - 64) 12288 STK4); [lia|lia|lia|]. replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
set (ptr' := bv_unsigned (getr R4 (PMK.reg 10))) in *.
assert (PTR : ptr' = ptr mod 2 ^ 64) by (unfold ptr'; rewrite Y10, Z_to_bv_unsigned; reflexivity).
assert (LOC' : (ptr = 0 /\ len = 0) \/ (exists B m, In (B, m) (PM.parser_own s4) /\ B <= ptr /\ ptr + len <= B + m) \/ (fb + 40 + 336 + 1 <= ptr /\ ptr + len <= fb + 40 + 336 + 24)) by exact LOC.
assert (PLOC : 0 <= ptr /\ ptr + len <= 2 ^ 47 /\ (len = 0 \/ 0 < ptr) /\ (len = 0 \/ ptr + len <= sp - 64 - 12288 \/ sp - 64 <= ptr)).
{ destruct LOC' as [(L1 & L2)|[(B & m & HB & L1 & L2)|(L1 & L2)]].
- clear - L1 L2. lia.
- assert (HB' : In (B, m) (PM.parser_own s4 ++ LBX)) by (apply in_or_app; left; exact HB).
destruct (PMFR.brange_of_heap L HI HIok _ _ cr4 M4 _ HH4 (incl_refl _) B m HB') as (Z0 & _ & Z4). unfold hl_ceil in Z4.
clear - Z0 Z4 L1 L2 SLO STOP. lia.
- clear - L1 L2 F1 F2 SLO STOP. lia. }
assert (PE : ptr' = ptr) by (rewrite PTR; apply Z.mod_small; lia). rewrite PE in W20.
unfold PMS.validate_spec, PMSP.validate_spec, PMSP.scan_spec in VAL. cbn [pa_validate AD PmLayoutS.ADDR_S] in VAL.
apply (VAL fx5 R5 M4 model4 K ptr len (sp - 64) 222796 Mh4 Ml4 K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact W1|]. split; [split; [lia| reflexivity]|].
split; [rewrite (KS5 2%nat) by PMK.inl; rewrite RP4_ by PMK.inl; rewrite (KS3 2%nat) by PMK.inl; exact R2_2|].
split; [rewrite (KS5 3%nat) by PMK.inl; rewrite RP4_ by PMK.inl; rewrite (KS3 3%nat) by PMK.inl; rewrite R2x by PMK.inl; exact Rgp|].
split; [rewrite (KS5 4%nat) by PMK.inl; rewrite RP4_ by PMK.inl; rewrite (KS3 4%nat) by PMK.inl; rewrite R2x by PMK.inl; exact Rtp|]. exact STKv. }
{ rewrite L5K.rl10. rewrite (KS5 10%nat) by PMK.inl. exact Y10. }
{ rewrite L5K.rl11. exact W11. }
{ unfold len in *. lia. } { lia. } { destruct PLOC as (_ & _ & X & _); exact X. } { lia. } { exact DEF4. }
{ destruct PLOC as (_ & _ & _ & [X|[X|X]]); [left; exact X| right; right; exact X| right; left; exact X]. }
{ exact BASE4. }
intros fx6 R6 M6 RP6 FB6 MG6.
assert (FB6' : forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 64 - 12288 <= i < sp - 64) -> M6 (Z_to_bv 64 i) = M4 (Z_to_bv 64 i)).
{ intros i Hi N. apply FB6. rewrite L5.unsigned_lit by exact Hi. intros r0 [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. apply N. unfold PMSP.pm_scr in Hr. lia. }
assert (HH6 : hi_heap HI (PM.parser_own s4 ++ LBX) cr4 M6 (m_vmmaps model4)).
{ apply (PMK.hi_heap_stretch RSEGS L HI KL HIok _ cr4 M4 M6 _ HH4 ltac:(lia)); [|exact MG6].
intros a Ha. destruct (PMK.rng_dec a (sp - 64 - 12288) (sp - 64)) as [X|X]; [right; apply (PMK.cwr_stack L _ M sp 26624 a STK); lia| left; apply FB6'; assumption]. }
assert (AG46 : forall a nn, 0 <= a -> a + nn <= 2 ^ 64 -> (a + nn <= sp - 64 - 12288 \/ sp - 64 <= a) -> L5C.agree_on M4 M6 a nn).
{ intros a nn H1 H2 H3 i Hi. apply FB6'; [lia|]. clear - Hi H3. lia. }
assert (STK6 : L5C.stk (hl_sptop L) M6 sp 26624) by (apply (PMK.stk_grows L M4 M6 sp 26624 MG6 STK4)).
pose proof (L5C.stk_writable RSEGS _ M6 sp 26624 STK6) as WR6.
assert (EK6 : PMK.ek L LBX sp 26624 (PMSP.W_run AD fb) M4 M6).
{ apply (PMK.ek_piece_in RSEGS L KL LBX sp 26624 _ M4 M6 (fun a => sp - 64 - 12288 <= a < sp - 64) ltac:(intros a Ha N; apply FB6'; assumption) STK4 (PMFR.brange_hi L LBX BRX)).
intros a Pa. left. lia. }
assert (EK6f : PMK.ek L LBX sp 26624 [] M4 M6).
{ apply (PMFR.ek_of_piece RSEGS L KL LBX sp 26624 M4 M6 (fun a => sp - 64 - 12288 <= a < sp - 64) ltac:(intros a Ha N; apply FB6'; assumption) STK4 (PMFR.brange_hi L LBX BRX)).
intros a Pa. lia. }
assert (HP06 : L5C.hpres L LBX sp 26624 (PMSP.W_run AD fb) M M6).
{ apply (PMK.hpres_of L LBX sp 26624 _ M M6).
- apply (PMK.ek_trans L LBX sp 26624 _ M M4 M6 (PMK.ek_of_hpres L LBX sp 26624 _ M M4 HP04) EK6).
- destruct STK6 as (_ & _ & _ & _ & D6). exact D6.
- apply (PMK.dk_trans L LBX sp 26624 M M4 M6 (PMK.dk_of_hpres L LBX sp 26624 _ M M4 HP04) (PMK.dk_grows L LBX sp 26624 M4 M6 MG6)). }
assert (F8 : L5.u64_at RSEGS M6 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by (apply (L5C.u64_at_agree RSEGS M4 M6); [apply AG46; lia|lia|lia| exact E8]).
assert (F16 : L5.u64_at RSEGS M6 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))) by (apply (L5C.u64_at_agree RSEGS M4 M6); [apply AG46; lia|lia|lia| exact E16]).
assert (F24 : L5.u64_at RSEGS M6 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))) by (apply (L5C.u64_at_agree RSEGS M4 M6); [apply AG46; lia|lia|lia| exact E24]).
assert (F32 : L5.u64_at RSEGS M6 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))) by (apply (L5C.u64_at_agree RSEGS M4 M6); [apply AG46; lia|lia|lia| exact E32]).
assert (F40 : L5.u64_at RSEGS M6 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))) by (apply (L5C.u64_at_agree RSEGS M4 M6); [apply AG46; lia|lia|lia| exact E40]).
assert (F48 : L5.u64_at RSEGS M6 (sp - 48) (bv_unsigned (getr R (PMK.reg 20)))) by (apply (L5C.u64_at_agree RSEGS M4 M6); [apply AG46; lia|lia|lia| exact E48]).
assert (PA6 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M6 (fb + 40) (fb + 440) s4).
{ destruct s4 as [mo4 dn4 dp4 src4 tb4 tg4 vb4 vk4 stk4].
assert (VIN4 : In (vb4, 32 * 2 ^ vk4) (PM.parser_own (PM.PST mo4 dn4 dp4 src4 tb4 tg4 vb4 vk4 stk4) ++ LBX)) by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (PMFR.brange_of_heap L HI HIok _ _ cr4 M4 _ HH4 (incl_refl _) _ _ VIN4) as (Z0 & _ & Z4). unfold hl_ceil in Z4.
apply (PMPK.parser_at_keep RSEGS AD M4 M6 (fb + 40) (fb + 440) _ PA4); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb].
- lia.
- lia.
- apply AG46; lia.
- apply PMPK.dkr_grows. exact MG6.
- lia.
- clear - Z4 STOP. lia.
- apply AG46; [lia| clear - Z4 STOP; lia| left; clear - Z4 SLO; lia].
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG6. }
assert (IA6 : PM.iss_at RSEGS AD PMSP.T3 M6 (fb + 440) str sm4).
{ apply (PMPK.iss_upd RSEGS AD M4 M6 (fb + 440) str sm4 (PM.sm_g sm4) (PM.sm_st sm4) IA4).
- lia.
- lia.
- apply AG46; lia.
- apply AG46; lia.
- apply AG46; lia.
- apply PMPK.dkr_grows. exact MG6.
- apply PMPK.dkr_grows. exact MG6.
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG6.
- destruct IA4 as (_ & _ & _ & _ & _ & _ & K40 & _). apply (L5C.u64_at_agree RSEGS M4 M6); [apply AG46; lia|lia|lia| exact K40].
- destruct IA4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & K32 & _) & _). replace (fb + 440 + 152) with (fb + 440 + 120 + 32) by lia.
apply (PMF.u32_at_agree RSEGS M4 M6); [apply AG46; lia|lia|lia| exact K32].
- destruct IA4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KE). exact KE.
- destruct IA4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & KS) & _). exact KS. }
assert (RPRE6 : PMSP.run_pre RSEGS AD M6 fb s4 str sm4 e2).
{ unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S].
split; [exact PA6|]. split; [exact IA6|].
split; [unfold PMSP.visitor_at; apply (L5C.u64_at_agree RSEGS M4 M6); [apply AG46; lia|lia|lia| exact VIS4]|].
split; [apply (L5C.u64_at_agree RSEGS M4 M6); [apply AG46; lia|lia|lia| exact VREF4]|].
split; [apply (PMKP.base_ok_keep RSEGS AD L KL SF LBX sp 26624 [] M4 M6 EK6f); first [exact BASE4 | intros a _; apply L5C.outside_nil]|].
split; [apply (PMKP.err_ok_keep RSEGS AD L KL SF LBX sp 26624 [] M4 M6 EK6f); first [exact ERR4 | intros a _; apply L5C.outside_nil]| exact TB4]. }
assert (EC6 : PMSP.ec_at RSEGS M6 (fb + 8) 0 cat) by (apply (ec_agree M4 M6); [apply AG46; lia|lia|lia| exact EC4]).
pose proof (proj2 (proj2 EC6)) as ED6e.
assert (RP6_ : forall k, In k PMK.cs_all -> getr R6 (PMK.reg k) = getr R5 (PMK.reg k)) by (intros k Hk; apply (PMK.cs_of_preserved R5 R6 k RP6 Hk)).
pose proof (bv_unsigned_in_range 64 (getr R6 (PMK.reg 11))) as B6. change (bv_modulus 64) with (2 ^ 64) in B6.
cfeed P (PMSRKP.rkW_conc fx6 R6 M6 (fun j => match j with 2%nat => sp | 33%nat => len | 34%nat => ptr | 35%nat => bv_unsigned (getr R6 (PMK.reg 11))
| 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) ltac:(first [PMK.sc | (symmetry; apply PMPK.word_id) | unfold PMSRKP.aligned; first [exact A16 | exact AL5 | exact AL1]]).
destruct P as (fx7 & R7 & M7 & MG7 & FR7 & _ & EX7).
assert (M7 = M6) as -> by (apply functional_extensionality; exact FR7).
destruct EX7 as [(MS7 & KS7)|(MS7 & KS7 & V1 & V10 & V11)].
2:{
apply (PMK.spiece_ro RSEGS model4 fx6 fx7 R6 0x3664c R7 0x36490 M6 K Mh4 Ml4 MS7).
apply (ERRP fx7 R7 M6 model4 7 s4 sm4 e2 cr4 V1); try gl_disp. }
apply (PMK.spiece_ro RSEGS model4 fx6 fx7 R6 0x3664c R7 0x3668c M6 K Mh4 Ml4 MS7).
pose proof PA6 as (_ & PD6 & _ & _ & _ & _ & P16 & _).
pose proof (PMSRKP.rkK_conc fx7 R7 M6 (fun j => match j with 2%nat => sp | 33%nat => len | 34%nat => ptr | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
| 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => bv_unsigned (getr R (PMK.reg 20)) | _ => 0 end)) as P.
cbn beta iota in P.
pose proof RPRE6 as (_ & _ & _ & _ & BASE6 & ERR6 & _).
pose proof BASE6 as (IMG6 & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in IMG6.
assert (VIS6 : L5.u64_at RSEGS M6 (fb + 432) 717288) by (apply (L5C.u64_at_agree RSEGS M4 M6); [apply AG46; lia|lia|lia| exact VIS4]).
assert (WOP6 : L5.writable RSEGS M6 (fb + 40 + 8) 1) by (apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M6 (fb + 40) 384); [exact PD6|lia|lia]|lia|lia]).
PMK.feed P ltac:(first [PMK.sc | unfold PMSRKP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54]]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx8 & R8 & M8 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG8 & _ & FRZ8 & MS8 & KS8 & U1 & U2 & U8 & U9 & U10 & U11 & U12 & U13 & U14 & U18 & U19 & U20 & Z8 & S56 & S64)); PMK.pvz_clrT.
rewrite PMPK.word_id in U1, U8, U9, U18, U19, U20.
apply (gl_step _ cr4 fx7 fx8 R7 R8 0x3668c 0x36688 M6 M8 model4 K sp (fb + 40 + 8) 1 HH6 Mh4 Ml4 ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(right; unfold hl_ceil; lia) MS8 MG8
(fun i Hi N1 N2 => FRZ8 i Hi (fun X => N1 ltac:(lia)) N2)).
intros HH8.
unfold PMSP.cfg.
eapply (L5.cps_of_msteps RSEGS); [exact Mh4| exact Ml4| |].
{ apply (PMK.ret_to RSEGS fx8 R8 M8 0x36688 (ltac:(oW' 0x36688%Z)) r (ltac:(oF' 0x36688%Z)) eq_refl (ltac:(oD' 0x36688%Z))); [rewrite U1; exact Rra| lia| exact Hr2]. }
set (W8 := [(fb + 48, 1)] : list L5.range).
assert (WC8 : forall a, PMK.inW W8 a -> (fb + 48 <= a < fb + 49)) by (intros a I; apply PMFR.inW_inv1 in I; lia).
assert (WHI8 : forall a, PMK.inW W8 a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply WC8 in I; left; lia).
assert (EK8 : PMK.ek L LBX sp 26624 W8 M6 M8).
{ apply (PMK.ek_piece_in RSEGS L KL LBX sp 26624 W8 M6 M8 (fun a => (sp - 64 <= a < sp - 64 + 16) \/ (fb + 40 + 8 <= a < fb + 40 + 8 + 1))
ltac:(intros a Ha N; apply FRZ8; [exact Ha| |]; intros X; apply N; [left|right]; exact X) STK6 (PMFR.brange_hi L LBX BRX)).
intros a [Pa|Pa]; [left; lia| right; apply PMK.inW_here; lia]. }
assert (AG68 : forall a nn, 0 <= a -> a + nn <= 2 ^ 64 -> (a + nn <= sp - 64 \/ sp - 48 <= a) -> (a + nn <= fb + 48 \/ fb + 49 <= a) -> L5C.agree_on M6 M8 a nn).
{ intros a nn H1 H2 H3 H4 i Hi. apply FRZ8; [clear - H1 H2 Hi; lia| clear - H3 Hi; lia| clear - H4 Hi; lia]. }
apply (KONT fx8 R8 M8 model4 s4 sm4 e2 cr4).
* apply PMK.preserved_by_index. intros k Hk. cbn in Hk.
repeat (destruct Hk as [<-|Hk]; [first [ rewrite U2; symmetry; exact Rsp | assumption
| (rewrite (KS8 _) by PMK.inl; rewrite (KS7 _) by PMK.inl; rewrite RP6_ by PMK.inl; rewrite (KS5 _) by PMK.inl; rewrite RP4_ by PMK.inl;
rewrite (KS3 _) by PMK.inl; apply R2x; PMK.inl) ] |]).
destruct Hk.
* unfold PMSP.run_post, PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_is pa_off_v pa_off_ec AD PmLayoutS.ADDR_S].
assert (MO4 : PM.p_more s4 = 1) by (rewrite EM4; destruct INV2 as (X & _); exact X).
split; [|split; [exact STEP04|split; [exact EE2| right]]].
++ split.
{ destruct s4 as [mo4 dn4 dp4 src4 tb4 tg4 vb4 vk4 stk4]. cbn [PM.p_more] in MO4. subst mo4.
assert (VIN4 : In (vb4, 32 * 2 ^ vk4) (PM.parser_own (PM.PST 1 dn4 dp4 src4 tb4 tg4 vb4 vk4 stk4) ++ LBX)) by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (PMFR.brange_of_heap L HI HIok _ _ cr4 M6 _ HH6 (incl_refl _) _ _ VIN4) as (Z0 & _ & Z4). unfold hl_ceil in Z4.
change (PM.PST 1 dn4 dp4 src4 tb4 tg4 vb4 vk4 stk4) with (PMPK.set_more (PM.PST 1 dn4 dp4 src4 tb4 tg4 vb4 vk4 stk4) 1).
apply (PMPK.parser_more_upd RSEGS AD M6 M8 (fb + 40) (fb + 440) _ 1 PA6); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
- lia.
- lia.
- apply AG68; lia.
- apply AG68; lia.
- apply PMPK.dkr_grows. exact MG8.
- exact Z8.
- right. reflexivity.
- apply PMPK.dkr_grows. exact MG8.
- lia.
- clear - Z4 STOP. lia.
- apply AG68; [lia|clear - Z4 STOP; lia| left; clear - Z4 SLO; lia| left; clear - Z4 SLO F1; lia].
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG8. }
split.
{ apply (PMFR.iss_keep RSEGS AD L KL LBX sp 26624 W8 M6 M8 EK8 STK6 SC0 BRX WHI8); [lia|lia| |exact INCS| exact IA6].
intros i Hi I. apply WC8 in I. lia. }
split; [unfold PMSP.visitor_at; apply (L5C.u64_at_agree RSEGS M6 M8); [apply AG68; lia|lia|lia| exact VIS6]|].
split; [apply (L5C.u64_at_agree RSEGS M6 M8); [apply AG68; lia|lia|lia| apply (L5C.u64_at_agree RSEGS M4 M6); [apply AG46; lia|lia|lia| exact VREF4]]|].
split; [apply (PMKP.base_ok_keep RSEGS AD L KL SF LBX sp 26624 W8 M6 M8 EK8); [| | | | exact BASE6];
intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WC8 in I; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S] in Ha;
clear - I Ha SLO STOP F1; lia|].
split; [apply (PMKP.err_ok_keep RSEGS AD L KL SF LBX sp 26624 W8 M6 M8 EK8); [| | exact ERR6];
intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WC8 in I; cbn [pa_errcat_guard pa_atexit AD PmLayoutS.ADDR_S] in Ha;
clear - I Ha SLO STOP F1; lia| exact TB4].
++ split; [apply (ec_agree M6 M8); [apply AG68; lia|lia|lia| exact EC6]|].
split.
{ unfold PM.inv. rewrite MO4, ED4, EDP4, ESTK4. destruct INV2 as (_ & I2 & I3 & I4 & _). split; [reflexivity|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4| exact TB4]. }
unfold PMSP.prog_key. destruct PLEN as (PS & UL & _). split; [rewrite ESTK4; exact PS|].
unfold PMSP.src_step in STEP4. destruct STEP4 as (_ & _ & _ & _ & U4). lia.
* apply (PMK.hpres_of L LBX sp 26624 _ M M8).
++ apply (PMK.ek_trans L LBX sp 26624 _ M M6 M8 (PMK.ek_of_hpres L LBX sp 26624 _ M M6 HP06)).
apply (PMK.ek_weaken L LBX LBX sp 26624 sp 26624 _ W8 M6 M8 EK8); [apply incl_refl| intros x Hx; exact Hx|].
intros a O r0 Hr0 Hin. unfold W8 in Hr0. destruct Hr0 as [<-|[]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
unfold PMSP.W_run, PMSP.o_p in O. cbn [pa_off_p AD PmLayoutS.ADDR_S app] in O. apply (O (fb + 40 + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
++ destruct STK6 as (_ & _ & _ & _ & D6). apply (L5.defined_grows M6 M8 _ _ MG8). exact D6.
++ apply (PMK.dk_trans L LBX sp 26624 M M6 M8 (PMK.dk_of_hpres L LBX sp 26624 _ M M6 HP06) (PMK.dk_grows L LBX sp 26624 M6 M8 MG8)).
* exact CK04.
* exact MB04.
* exact HH8.
Qed.
End WithHeap.
End PMSRK.
