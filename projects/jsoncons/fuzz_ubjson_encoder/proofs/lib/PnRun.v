(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core
     PmLayout PmModel PmStatics PmSpecs PmParSpecs PmTxtSpecs PgSrc PgV8 PnLayout PnModel PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PnRun () := "C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3appC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L55rangeC13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PnModel3PNM;bparser_ownC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface7hi_heapC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmSpecs4PMSP8model_okC13~~~K47Corelib4Init9Datatypes4list01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmSpecs4PMSP5entryC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmSpecs4PMSP8frame_okC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5PnRun3PNR8brun_preC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM6vs_ownC13~~~C46Stdlib5Lists4List4inclc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5PnRun3PNR4binvC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5PnRun3PNR4o_ecC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmSpecs4PMSP5ec_atC13~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic3and00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PnModel3PNM5b_srcC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM6unreadC13~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5PnRun3PNR;pot_bparserC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmSpecs4PMSP9credit_leC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface>regs_preservedC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5PnRun3PNR9brun_postC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmSpecs4PMSP6pm_scrC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5PnRun3PNR6W_brunC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5C5hpresC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmSpecs4PMSP;credit_keepC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface<model_but_vmC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs4SCFGC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmSpecs4PMSP3cfgC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~K47Corelib4Init5Logic3and01c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5PnRun3PNR9brun_specC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5PnRun3PNR<brun_spec_fbC13~~~C47Corelib4Init5Logic3iffI47Corelib4Init9Datatypes4bool00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PnModel3PNM4bpst00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM4strm00C13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5PnRun3PNR5bprogC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7FPState00C13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface6creditC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM4vstr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PnStatics4PNST3bax00C13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K47Corelib7Numbers7BinNums1Z01".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNR.
Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AN : PNL.pn_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.

Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation iss_at := (PM.iss_at segs A T3).
Abbreviation vstr_at := (PM.vstr_at segs T3).
Abbreviation bparser_at := (PNM.bparser_at segs A T3 T4 (pa_vp_parser A)).
Abbreviation berr_ok := (PNST.berr_ok segs A AN).
Abbreviation entry := (PMSP.entry A L).
Abbreviation frame_ok := (PMSP.frame_ok A L).
Abbreviation pm_scr := PMSP.pm_scr.
Abbreviation cfg := (@PMSP.cfg segs).

(* [comment removed for export] *)
Definition o_p (fb : Z) : Z := PMSP.o_p A fb.
Definition o_is (fb : Z) : Z := PMSP.o_is A fb.
Definition o_v (fb : Z) : Z := PMSP.o_v A fb.
Definition o_ec (fb : Z) : Z := PMSP.o_ec A fb.
Definition o_src (fb : Z) : Z := o_p fb + PNM.OFF_SRC.
Definition o_bb (fb : Z) : Z := o_p fb + PNM.OFF_BB.
Definition o_nb (fb : Z) : Z := o_p fb + PNM.OFF_NB.
Definition o_tb (fb : Z) : Z := o_p fb + PNM.OFF_TB.
Definition o_stk (fb : Z) : Z := o_p fb + PNM.OFF_STK.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bmode_bottom (m : Z) : Prop := m = 0 \/ m = 1.
Definition bmode_cont (m : Z) : Prop := m = 2 \/ m = 3 \/ m = 4.
Definition bstack_shape (stk : list PNM.bstate) : Prop :=
  (1 <= length stk)%nat /\ Z.of_nat (length stk) <= PNM.MAX_DEPTH + 1
  /\ bmode_bottom (PNM.bs_mode (nth 0 stk PNM.bs_root))
  /\ (forall i, (1 <= i < length stk)%nat -> bmode_cont (PNM.bs_mode (nth i stk PNM.bs_root)))
  /\ (forall i, (i < length stk)%nat -> PNM.bstate_ok (nth i stk PNM.bs_root)).
Definition binv (s : PNM.bpst) : Prop :=      (* [comment removed for export] *)
  PNM.b_done s = 0 /\ bstack_shape (PNM.b_stk s).
Definition bflag (stk : list PNM.bstate) : Z :=
  let m := PNM.bs_mode (last stk PNM.bs_root) in if (Z.eqb m 0 || Z.eqb m 4)%bool then 1 else 0.
Definition bmu (s : PNM.bpst) (sm : PM.strm) : Z := 2 * PM.unread (PNM.b_src s) sm + bflag (PNM.b_stk s).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pot_bstack (k : Z) : credit :=
  (hl_k_per_malloc L * (11 - k), PNM.BSZ * (2 ^ 12 - 2 ^ (k + 1)) + (11 - k) * hl_b_overhead L).
Definition pot_bparser (s : PNM.bpst) : credit :=
  PM.credit_add (pot_bstack (PNM.b_sk s))
    (PM.credit_add (PM.pot_text L (PNM.b_tb s) (PNM.b_tg s))
       (PM.credit_add (PM.pot_text L (PNM.b_nb s) (PNM.b_ng s)) (PGV8.pot_v8 L (PNM.b_bb s) (PNM.b_bg s)))).

(* [comment removed for export] *)
Definition pot_callB (n : Z) : credit :=
  PM.credit_add (PM.credit_add (PM.cost1 L (n + 16)) (PM.cost1 L (n + 32)))
    (PM.credit_add (PM.credit_add (PM.cost1 L PM.CHUNK) (PM.cost1 L PNM.BSZ))
       (PM.credit_add (pot_bstack 0)
          (PM.credit_add (PM.pot_text L (PM.VShort 0) 0) (PM.credit_add (PM.pot_text L (PM.VShort 0) 0) (PGV8.pot_v8 L PGV8.V8Null 0))))).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition brun_pre (M : word -> option byte) (fb : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax) : Prop :=
  bparser_at M (o_p fb) (o_is fb) s /\ iss_at M (o_is fb) str sm /\ PMSP.visitor_at segs A M (o_v fb)
  /\ L5.u64_at segs M (o_p fb + PNM.PSIZE) (o_v fb) /\ PMST.base_ok segs A M /\ berr_ok M ax /\ PNM.bgrow_ok s.
Definition W_brun (fb : Z) : list L5.range :=
  [(o_p fb + 8, 8)] ++ PGS.W_srcfG (o_src fb) (o_is fb) ++ [(o_bb fb, 24); (o_nb fb, 24); (o_tb fb, 24); (o_stk fb, 24); (o_ec fb, 16)]
  ++ PNST.berr_W A AN.
(* [comment removed for export] *)
Definition btop_pos (s s' : PNM.bpst) : Prop :=
  exists l c c', PNM.b_stk s = l ++ [c] /\ PNM.b_stk s' = l ++ [c'] /\ PNM.bstate_ok c'
                 /\ PNM.bs_mode c' = PNM.bs_mode c /\ PNM.bs_len c' = PNM.bs_len c /\ PNM.bs_type c' = PNM.bs_type c /\ PNM.bs_idx c' = PNM.bs_idx c.
(* [comment removed for export] *)
Definition bpush_rel (s s' : PNM.bpst) (sm sm' : PM.strm) : Prop :=
  btop_pos s s'
  \/ exists c, PNM.b_stk s' = PNM.b_stk s ++ [c] /\ PNM.bstate_ok c /\ bmode_cont (PNM.bs_mode c) /\ PNM.bs_idx c = 0
               /\ PM.unread (PNM.b_src s') sm' + 4 <= PM.unread (PNM.b_src s) sm.
Definition bprog := bvmap 5 word -> (word -> option byte) -> PNM.bpst -> PNM.bpst -> PM.strm -> PM.strm -> Prop.
(* [comment removed for export] *)
Definition bb_room (s : PNM.bpst) (sm : PM.strm) : Prop := PGV8.v8_room (PNM.b_bb s) (PM.unread (PNM.b_src s) sm).
Definition bb_post (bb : bool) (s s' : PNM.bpst) (sm sm' : PM.strm) : Prop :=
  if bb then (bb_room s sm -> PNM.b_more s' = 1 -> bb_room s' sm') else PNM.b_bb s' = PNM.b_bb s.
Definition brun_post (bb : bool) (prog : bprog) (R' : bvmap 5 word)
           (M' : word -> option byte) (fb : Z) (s s' : PNM.bpst) (str : PM.vstr) (sm sm' : PM.strm) (ax ax' : PNST.bax) (cat e : Z) : Prop :=
  brun_pre M' fb s' str sm' ax' /\ PMSP.src_step (PNM.b_src s) (PNM.b_src s') sm sm' /\ PNST.bax_le ax ax'
  /\ (   (exists v, 1 <= v <= 64 /\ PMSP.ec_at segs M' (o_ec fb) v (pa_errcat_obj A) /\ PNM.b_more s' = 0 /\ PNST.bax_cat ax' = true
                     /\ (length (PNM.b_stk s) <= length (PNM.b_stk s'))%nat /\ binv s')   (* [comment removed for export] *)
      \/ (PMSP.ec_at segs M' (o_ec fb) e cat /\ binv s' /\ prog R' M' s s' sm sm'))      (* [comment removed for export] *)
  /\ bb_post bb s s' sm sm'.

Definition brun_spec (bb : bool) (pc h : Z) (args : bvmap 5 word -> Z -> PNM.bpst -> PM.strm -> Prop) (prog : bprog) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb cat e : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax),
    hi_heap HI (PNM.bparser_own s ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r h -> frame_ok sp fb ->
    args R fb s sm ->
    brun_pre M fb s str sm ax -> incl (PM.vs_own str) LBX -> binv s -> PMSP.ec_at segs M (o_ec fb) e cat -> 0 <= e <= 64 ->
    PM.unread (PNM.b_src s) sm < 2 ^ 26 ->
    PMSP.credit_le (pot_bparser s) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PNM.bpst) (sm' : PM.strm) (ax' : PNST.bax) (cr' : credit),
        regs_preserved R R' ->
        brun_post bb prog R' M' fb s s' str sm sm' ax ax' cat e ->
        L5C.hpres L LBX sp (pm_scr h) (W_brun fb) M M' ->
        PMSP.credit_keep cr cr' (pot_bparser s) (pot_bparser s') ->
        model_but_vm model model' -> hi_heap HI (PNM.bparser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
(* [comment removed for export] *)
Definition brun_spec_fb (bb : bool) (fb pc h : Z) (args : bvmap 5 word -> Z -> PNM.bpst -> PM.strm -> Prop) (prog : bprog) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r cat e : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax),
    hi_heap HI (PNM.bparser_own s ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r h -> frame_ok sp fb ->
    args R fb s sm ->
    brun_pre M fb s str sm ax -> incl (PM.vs_own str) LBX -> binv s -> PMSP.ec_at segs M (o_ec fb) e cat -> 0 <= e <= 64 ->
    PM.unread (PNM.b_src s) sm < 2 ^ 26 ->
    PMSP.credit_le (pot_bparser s) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PNM.bpst) (sm' : PM.strm) (ax' : PNST.bax) (cr' : credit),
        regs_preserved R R' ->
        brun_post bb prog R' M' fb s s' str sm sm' ax ax' cat e ->
        L5C.hpres L LBX sp (pm_scr h) (W_brun fb) M M' ->
        PMSP.credit_keep cr cr' (pot_bparser s) (pot_bparser s') ->
        model_but_vm model model' -> hi_heap HI (PNM.bparser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
Lemma brun_spec_iff bb pc h args prog : brun_spec bb pc h args prog <-> forall fb, brun_spec_fb bb fb pc h args prog.
Proof.
ltac2:(KReplay.run1 (kr_t_PnRun ()) ["Specs"] "h02fbh11Kh23LBXh31Mh41Rh53cath62crh71eh82fxh95modelh:1rh;2sph<2M'h=2R'h>2axh?3ax'h@3cr'hA3fx'hB6model'hC1shD2s'hE2smhF3sm'hG3strhH1HhI4argshJ2bbhK1hhL2pchM4progp%0p;1p;2p;3p;5p;7p;4p;6p;>p-1R0p10000p4p710p8P0g000GR0p4p710R1p8p1000dp4p70P1p8g001nj10Tg002Sj1<Tg0038j1:Tg003Vj1=Tg0049j2\Tg004ej1VTg005Gj2TTg005gj1RTg006Gj1ATP0j37Tg007Yj1;Tg008Pj56Tg009\j1FTg00:lj1[Tg00;Lj75Tg00<Yj4KTg00=ij6ITg00?6j1UTg00@Bj3HTg00@[j1STg00Adj1DTg00Bmj5CTg00D:j2BTg00DVj19Tg00E4j2QTg00EOj1PTg00F[j2OTg00Ggj2NTg00HDj2MTg00H`j18Tg00J0j2@Tg00KAj2?Tg00LTl>3Tg00Mbj1GTg00O0j1>Tg00P;j74Tg00QFj4JTg00RYj2ETg00Sjj1LTg00U0j62Tg00V;j51Tg00WGj4ZTg00Wbj5YTg00Y0j6WTg00ZAj2XTg00ZZS00g00[:R0g00[XR1#0R2#<#:%02#0R3#0#0#0R4#:#=R5'\R6g00\=R7g00]JR8p-0[[\0[R9g00^VR:Q00g00_`R;%:3#=#V\5R5g00`mR3g00acR<1T00R=#RR>g00bkR?g00d6R@g00eBRAp,2HIRBf3RC#ARDf:RE57=f9RFf=RGf<RH#;D6RI%FGRJPGg00fQ#[RKO1RLp,1ARMp,1LRNfAROf@RPf;RQPEfERRF5PMPNPHPECKRSfFRTfCRUPQf8RVf6RWO4PUPHPFPVf7RXPWEIRY%UFRZ=H=OR[%SQR\p,4segsR]PTf?R^#DPGf>R_DCR`g00gG/B_%94,B_'QR4%P_/OH%92%<1#0#<#0#9'N'MR1%8^R2/@RRafSRb/?WRcfZRdfVRePXPWfLRffIRgf4RhfHRifGRjPCPTf2RkfKRlfJRmM>3PNfQRnfOS01fY#GS02fMRo#>S03fTRpPXF4PnPC%8lS04%8WS05CJfURq/EVPB%AVRr=7=pf5RsPE%;FS06D6p,3bmKRtP]p,6SCFG_P#LRuP]PGPHfRRvPQPEE2PeD1[[[S07[[[^@?^?A^F8^D7^B3^<5^=6^A;PtP]PuP]PoPfPnPlPmE2PgD1[[[[[[[[[[[[[[]>^E8]G^C7^70^50^00^:0^;0]6]2]1]9]3^46]8RwPBA7=DFPVPH%;QD6RD%FHRxPHPKO1RKPMPNPPP^PEPFPTF5PMPNPQPUCKRyPjfBRzfDR{PVPWO4PzPRPFPVPXPWEIR|AH=ZPRZP]PR%DiPGP_DCR_1@2{R21?vWR}f[S08fWS09PXPWPqPgPhPiPjPCPTPkPlPmM>3PNfPR~fNS0:%GdS0;%>eS0<PbPXF4P~PCQ04Q05CJ1EpVPBA7=rbPsPEQ06D6PtP]PuP]PGPHPnPQPEE2PqD1[[[RG[[[^@?^?A^F8^D7^B3^<5^=6^A;PtP]PuP]PfPlPvPmPgE2PiD1[[\1\4[\\[[[[[[[[^>A^E8^G@^C7^70^50^:0^;0^6?^2>^1<^93^35^46^8;^00[PMPNPPP^PEPFPRF5PTPzP{PVPWO4PdPePXPWPqPgPhPiPjPCPTPkPlPmM>3PNP~Q0:Q02Q0<PbPXF4PG[[\}^@?^?A^F8^D7^B3^<5^=6^A;PtP]PuP]PfPlPnPmPgE2PiD1[\2\1\4\_\\\Z\|[\y[\K\x\D^>A^E8^G@^C7^70^50^:0^;0^6?^2>^1<^93^35^46^8;^00RDPMPNPOPPPQPEPTF5PjPUPQPVPWO4Q08Q09PXPWPfPgPhPiPjPCPTPkPlPmM>3PNPnQ01Q0;Q03PpPXF4Q07[[\c^@?^?A^F8^D7^B3^<5^=6^A;PtP]PuP]PoPfPvPlPmE2PgD1[\a\1\4\`\\\[\Y[\S[\L\J\I^>A^E8^G@^C7^70^50^00^:0^;0^6?^2>^1<^93^35^46^8;[PHPEPFPVPXPWPsPhPCPkPQf1R7f0R@O<X70X50X:0X;0X6?X2>X1<X93X35X46X8;X00XHwPHPkPQPEPFPVPXPWPsPhPCP7P@O<X70X50X00X:0X;0X6?X2>X1<X93X35X46X8;XHDCZPhPCPkP7P@DYPsP@PhPCPkP7EW^00'XeXM:XI9XK0XL0WJPhPCPkP7P@O5WMWIXK0WLWJo"). Qed.

(* [comment removed for export] *)
Definition bargs3 (R : bvmap 5 word) (fb : Z) (_ : PNM.bpst) (_ : PM.strm) : Prop :=      (* [comment removed for export] *)
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_v fb) /\ getr R 12%bv = Z_to_bv 64 (o_ec fb).
Definition bargs_rv (R : bvmap 5 word) (fb : Z) (s : PNM.bpst) (sm : PM.strm) : Prop :=    (* [comment removed for export] *)
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_v fb) /\ getr R 13%bv = Z_to_bv 64 (o_ec fb)
  /\ (exists t, 0 <= t < 256 /\ getr R 12%bv = Z_to_bv 64 t) /\ bb_room s sm.
Definition bargs_en (R : bvmap 5 word) (fb : Z) (_ : PNM.bpst) (_ : PM.strm) : Prop :=    (* [comment removed for export] *)
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_v fb) /\ getr R 13%bv = Z_to_bv 64 (o_ec fb)
  /\ (getr R 12%bv = Z_to_bv 64 0 \/ getr R 12%bv = Z_to_bv 64 1).
Definition bargs_end (R : bvmap 5 word) (fb : Z) (s : PNM.bpst) (sm : PM.strm) : Prop := bargs3 R fb s sm /\ (2 <= length (PNM.b_stk s))%nat.
(* [comment removed for export] *)
Definition bcs_str (w : Z) (s : PNM.bpst) : PM.vstr := if Z.eqb w 0 then PNM.b_nb s else PNM.b_tb s.
Definition bcs_off (w : Z) : Z := if Z.eqb w 0 then PNM.OFF_NB else PNM.OFF_TB.
Definition bargs_cs (w : Z) (R : bvmap 5 word) (fb : Z) (s : PNM.bpst) (sm : PM.strm) : Prop :=
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_p fb + bcs_off w) /\ getr R 12%bv = Z_to_bv 64 (o_ec fb)
  /\ PM.vs_size (bcs_str w s) + PM.unread (PNM.b_src s) sm <= 2 ^ 26.
Definition bargs_rs (R : bvmap 5 word) (fb : Z) (_ : PNM.bpst) (_ : PM.strm) : Prop :=    (* [comment removed for export] *)
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_ec fb).

(* [comment removed for export] *)
Definition bprog_value : bprog := fun R' M' s s' sm sm' => bpush_rel s s' sm sm'.
Definition bprog_name : bprog := fun R' M' s s' sm sm' =>
  btop_pos s s' /\ PM.unread (PNM.b_src s') sm' < PM.unread (PNM.b_src s) sm.
Definition bprog_pop : bprog := fun R' M' s s' sm sm' =>      (* [comment removed for export] *)
  (exists l c top c', PNM.b_stk s = l ++ [c; top] /\ PNM.b_stk s' = l ++ [c'] /\ PNM.bstate_ok c'
                      /\ PNM.bs_mode c' = PNM.bs_mode c /\ PNM.bs_len c' = PNM.bs_len c
                      /\ PNM.bs_type c' = PNM.bs_type c /\ PNM.bs_idx c' = PNM.bs_idx c)
  /\ PM.unread (PNM.b_src s') sm' = PM.unread (PNM.b_src s) sm.
(* [comment removed for export] *)
Definition bprog_cs (w : Z) : bprog := fun R' M' s s' sm sm' =>
  btop_pos s s' /\ PM.unread (PNM.b_src s') sm' < PM.unread (PNM.b_src s) sm
  /\ PM.vs_size (bcs_str w s') + PM.unread (PNM.b_src s') sm' + 1 <= PM.vs_size (bcs_str w s) + PM.unread (PNM.b_src s) sm.
(* [comment removed for export] *)
Definition bprog_rs (fb : Z) : bprog := fun R' M' s s' sm sm' =>
  btop_pos s s' /\ PM.unread (PNM.b_src s') sm' + 5 <= PM.unread (PNM.b_src s) sm
  /\ exists ptr n, getr R' 10%bv = Z_to_bv 64 ptr /\ getr R' 11%bv = Z_to_bv 64 n /\ 0 <= n < 2 ^ 26 /\ L5.defined M' ptr n
       /\ ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PNM.bparser_own s') ptr n \/ (o_tb fb + 1 <= ptr /\ ptr + n <= o_tb fb + 24)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition begin_document_spec : Prop := brun_spec false (PNL.pn_begin_document AN) 7 bargs3 bprog_value.
Definition begin_array_spec : Prop := brun_spec false (PNL.pn_begin_array AN) 7 bargs3 bprog_value.
(* [comment removed for export] *)
Definition end_document_spec : Prop := brun_spec false (PNL.pn_end_document AN) 3 bargs_end bprog_pop.
Definition end_array_spec : Prop := brun_spec false (PNL.pn_end_array AN) 3 bargs_end bprog_pop.
Definition read_e_name_spec : Prop := brun_spec false (PNL.pn_read_e_name AN) 6 bargs_en bprog_name.
Definition read_value_spec : Prop := brun_spec true (PNL.pn_read_value AN) 8 bargs_rv bprog_value.
Definition read_cstring_spec : Prop := forall w, (w = 0 \/ w = 1) -> brun_spec false (PNL.pn_read_cstring AN) 5 (bargs_cs w) (bprog_cs w).
Definition read_string_spec : Prop := forall fb, brun_spec_fb false fb (PNL.pn_read_string AN) 7 bargs_rs (bprog_rs fb).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition parse_post (M' : word -> option byte) (fb : Z) (s s' : PNM.bpst) (str : PM.vstr) (sm sm' : PM.strm) (ax ax' : PNST.bax) : Prop :=
  brun_pre M' fb s' str sm' ax' /\ PMSP.src_step (PNM.b_src s) (PNM.b_src s') sm sm' /\ PNST.bax_le ax ax' /\ L5.defined M' (o_ec fb) 16.
Definition parse_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb cat e : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax),
    hi_heap HI (PNM.bparser_own s ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 10 -> frame_ok sp fb ->
    bargs3 R fb s sm ->
    brun_pre M fb s str sm ax -> incl (PM.vs_own str) LBX -> binv s -> PMSP.ec_at segs M (o_ec fb) e cat -> 0 <= e <= 64 ->
    PM.unread (PNM.b_src s) sm < 2 ^ 26 -> bb_room s sm ->
    PMSP.credit_le (pot_bparser s) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PNM.bpst) (sm' : PM.strm) (ax' : PNST.bax) (cr' : credit),
        regs_preserved R R' ->
        parse_post M' fb s s' str sm sm' ax ax' ->
        L5C.hpres L LBX sp (pm_scr 10) (W_brun fb) M M' ->
        PMSP.credit_keep cr cr' (pot_bparser s) PMSP.cr0 ->
        model_but_vm model model' -> hi_heap HI (PNM.bparser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_parse AN) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bparser_init (qc b : Z) : PNM.bpst :=
  PNM.BPST 1 0 (PM.SRC qc qc 0) PGV8.V8Null (PM.VShort 0) (PM.VShort 0) 0 0 0 b 0 [PNM.bs_root].
Definition reader_ctor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (sp r fb oo oa : Z) (str : PM.vstr) (sm : PM.strm),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 6 -> frame_ok sp fb ->
    getr R 10%bv = Z_to_bv 64 (o_p fb) -> getr R 11%bv = Z_to_bv 64 (o_is fb) -> getr R 12%bv = Z_to_bv 64 oo -> getr R 13%bv = Z_to_bv 64 oa ->
    fb <= oo -> oo + 24 <= o_p fb -> oo mod 8 = 0 -> L5.defined M (o_p fb) PNM.PSIZE ->
    L5.u64_at segs M oo (pa_vp_opts A) -> L5.u32_at segs M (oo + 16) PNM.MAX_DEPTH ->
    iss_at M (o_is fb) str sm -> PMST.base_ok segs A M -> PMST.loc_ok segs A M true ->
    PMSP.credit_le (PM.credit_add (PM.cost1 L PM.CHUNK) (PM.cost1 L PNM.BSZ)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (qc b : Z) (cr' : credit),
        regs_preserved R R' -> bparser_at M' (o_p fb) (o_is fb) (bparser_init qc b) ->
        L5C.hpres L LB sp (pm_scr 6) [(o_p fb, PNM.PSIZE)] M M' ->
        PMSP.credit_keep cr cr' (PM.credit_add (PM.cost1 L PM.CHUNK) (PM.cost1 L PNM.BSZ)) PMSP.cr0 ->
        model_but_vm model model' -> hi_heap HI (PNM.bparser_own (bparser_init qc b) ++ LB) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_reader_ctor AN) M model) K.

(* [comment removed for export] *)
Definition vs_clear (x : PM.vstr) : PM.vstr := match x with PM.VShort _ => PM.VShort 0 | PM.VLong c _ p => PM.VLong c 0 p end.
Definition bpst_reset (s : PNM.bpst) : PNM.bpst :=
  PNM.BPST 1 0 (PNM.b_src s) (PGV8.v8_clear (PNM.b_bb s)) (vs_clear (PNM.b_nb s)) (vs_clear (PNM.b_tb s))
           (PNM.b_ng s) (PNM.b_tg s) (PNM.b_bg s) (PNM.b_sb s) (PNM.b_sk s) [PNM.bs_root].
Definition reset_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb : Z) (s : PNM.bpst),
    hi_heap HI (PNM.bparser_own s ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 1 -> frame_ok sp fb ->
    getr R 10%bv = Z_to_bv 64 (o_p fb) -> bparser_at M (o_p fb) (o_is fb) s ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
        regs_preserved R R' -> bparser_at M' (o_p fb) (o_is fb) (bpst_reset s) ->
        (* [comment removed for export] *)
        L5C.hpres L LBX sp (pm_scr 1) [(o_p fb + 8, 8); (o_bb fb, 24); (o_nb fb, 24); (o_tb fb, 24); (o_stk fb, 24)] M M' ->
        hi_heap HI (PNM.bparser_own s ++ LBX) cr M' (m_vmmaps model) ->
        srealizes segs SCFG (@cfg fx' R' r M' model) K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_reset AN) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition make_ec_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o v sp r : Z) (ax : PNST.bax),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 1 ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 v -> 1 <= v <= 64 ->
    sp <= o -> o + 16 <= hl_sptop L -> o mod 8 = 0 -> L5.defined M o 16 ->
    PMST.base_ok segs A M -> berr_ok M ax ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
        regs_preserved R R' -> PMSP.ec_at segs M' o v (pa_errcat_obj A) -> berr_ok M' (PNST.bax_add_cat ax) ->
        L5C.hpres L LB sp (pm_scr 1) ((o, 16) :: (if PNST.bax_cat ax then [] else PNST.cat_W A)) M M' ->
        hi_heap HI LB cr M' (m_vmmaps model) ->
        srealizes segs SCFG (@cfg fx' R' r M' model) K) ->
    srealizes segs SCFG (@cfg fx R (pa_make_ec A) M model) K.

(* [comment removed for export] *)
Definition str_push_back_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o c sp r tg : Z) (x : PM.vstr),
    hi_heap HI (PM.vs_own x ++ LB) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 1 ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 c -> 0 <= c < 256 -> sp <= o -> o + 24 <= hl_sptop L -> o mod 8 = 0 ->
    vstr_at M o x -> PM.tb_ok x tg -> PM.vs_size x < 2 ^ 26 ->
    PMSP.credit_le (PM.pot_text L x tg) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : PM.vstr) (tg' : Z) (cr' : credit),
        regs_preserved R R' -> vstr_at M' o x' -> PM.vs_size x' = PM.vs_size x + 1 -> PM.tb_ok x' tg' ->
        (PM.vs_size x < PM.vs_cap x -> PM.vs_own x' = PM.vs_own x /\ tg' = tg) ->
        L5C.hpres L LB sp (pm_scr 1) [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (PM.pot_text L x tg) (PM.pot_text L x' tg') ->
        model_but_vm model model' -> hi_heap HI (PM.vs_own x' ++ LB) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_str_push_back AN) M model) K.

(* [comment removed for export] *)
Definition str_push_back_short_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o sp r n : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 1 ->
    getr R 10%bv = Z_to_bv 64 o -> sp <= o -> o + 24 <= hl_sptop L -> o mod 8 = 0 ->      (* [comment removed for export] *)
    vstr_at M o (PM.VShort n) -> n <= 21 ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
        regs_preserved R R' -> vstr_at M' o (PM.VShort (n + 1)) ->
        L5C.hpres L LB sp (pm_scr 1) [(o, 24)] M M' ->
        hi_heap HI LB cr M' (m_vmmaps model) ->
        srealizes segs SCFG (@cfg fx' R' r M' model) K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_str_push_back AN) M model) K.

(* [comment removed for export] *)
Definition from_int_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o v sp r n : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 2 ->
    getr R 10%bv = Z_to_bv 64 v -> - 2 ^ 31 <= v < 2 ^ 31 -> getr R 11%bv = Z_to_bv 64 o -> sp <= o -> o + 24 <= hl_sptop L -> o mod 8 = 0 ->
    vstr_at M o (PM.VShort n) -> 0 <= n <= 11 ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (n' : Z),
        regs_preserved R R' -> vstr_at M' o (PM.VShort n') -> n + 1 <= n' <= n + 11 ->
        L5C.hpres L LB sp (pm_scr 2) [(o, 24)] M M' ->
        hi_heap HI LB cr M' (m_vmmaps model) ->
        srealizes segs SCFG (@cfg fx' R' r M' model) K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_from_int AN) M model) K.

(* [comment removed for export] *)
Definition dec128_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (first vp sp r : Z) (ax : PNST.bax),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 3 ->
    getr R 10%bv = Z_to_bv 64 first -> getr R 11%bv = Z_to_bv 64 (first + 42) -> getr R 12%bv = Z_to_bv 64 vp ->
    (exists B m, In (B, m) LB /\ B <= first /\ first + 42 <= B + m) -> L5.defined M first 42 ->
    sp <= vp -> vp + 16 <= hl_sptop L -> L5.defined M vp 16 -> vp mod 8 = 0 ->
    PMST.base_ok segs A M -> berr_ok M ax ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (ptr : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 ptr -> first <= ptr <= first + 42 ->
        L5.defined M' first 42 -> berr_ok M' (PNST.bax_add_dec ax) ->
        L5C.hpres L LB sp (pm_scr 3) ((first, 42) :: (if PNST.bax_dec ax then [] else PNST.dec_W A AN)) M M' ->
        hi_heap HI LB cr M' (m_vmmaps model) ->
        srealizes segs SCFG (@cfg fx' R' r M' model) K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_dec128 AN) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition src_read_spec : Prop := PGS.src_read_specG segs A L HI.
Definition fill_buffer_spec : Prop := PGS.fill_buffer_specG segs A L HI.
Definition fill_buffer_tb_spec : Prop := PGS.fill_buffer_tb_specG segs A L HI.
Definition read_span_spec : Prop := PGS.read_span_specG segs A L HI (pa_read_span A).
Definition srd_read_spec : Prop := PGS.srd_read_specG segs A L HI (pa_srd_read A).
Definition read_span_v_spec : Prop := PGV8.read_span_v_specG segs A L HI (PNL.pn_read_span_v AN).
Definition srd_read_v_spec : Prop := PGV8.srd_read_v_specG segs A L HI (PNL.pn_srd_read_v AN).
Definition vu8_resize_spec : Prop := PGV8.vu8_resize_spec segs A L HI (PNL.pn_vu8_resize AN).
Definition vu8_append_spec : Prop := PGV8.vu8_append_spec segs A L HI (PNL.pn_vu8_append AN).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition reader_read_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax),
    hi_heap HI (PNM.bparser_own s ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 11 -> frame_ok sp fb ->
    getr R 10%bv = Z_to_bv 64 (o_p fb) -> getr R 11%bv = Z_to_bv 64 (o_ec fb) ->
    brun_pre M fb s str sm ax -> incl (PM.vs_own str) LBX -> PMSP.ec_at segs M (o_ec fb) 0 cat ->
    PM.unread (PNM.b_src s) sm < 2 ^ 26 -> bb_room s sm ->
    PMSP.credit_le (pot_bparser (bpst_reset s)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PNM.bpst) (sm' : PM.strm) (ax' : PNST.bax) (cr' : credit),
        regs_preserved R R' ->
        parse_post M' fb (bpst_reset s) s' str sm sm' ax ax' ->
        L5C.hpres L LBX sp (pm_scr 11) (W_brun fb) M M' ->
        PMSP.credit_keep cr cr' (pot_bparser (bpst_reset s)) PMSP.cr0 ->
        model_but_vm model model' -> hi_heap HI (PNM.bparser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_reader_read AN) M model) K.

(* [comment removed for export] *)
Definition vec_dtor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (t v b k sp r : Z) (stk : list PNM.bstate),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 0 ->
    getr R 10%bv = Z_to_bv 64 t -> sp <= t -> t + 8 <= hl_sptop L -> t mod 8 = 0 -> L5.u64_at segs M t v ->
    sp <= v -> v + 24 <= hl_sptop L -> v mod 8 = 0 -> L5.defined M v 24 ->
    PNM.bvec_at segs T3 T4 M v b k stk -> In (b, PNM.BSZ * 2 ^ k) LB ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        L5C.hpres L (lb_remove b LB) sp (pm_scr 0) [(v, 24)] M M' ->
        model_but_vm model model' -> hi_heap HI (lb_remove b LB) cr M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_vec_dtor AN) M model) K.

(* [comment removed for export] *)
Definition lb_remove_v8 (x : PGV8.v8) (LB : list (Z * Z)) : list (Z * Z) :=
  match x with PGV8.V8Null => LB | PGV8.V8Blk b _ _ => lb_remove b LB end.
Definition vu8_dtor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (t v sp r : Z) (x : PGV8.v8),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 0 ->
    getr R 10%bv = Z_to_bv 64 t -> sp <= t -> t + 8 <= hl_sptop L -> t mod 8 = 0 -> L5.u64_at segs M t v ->
    sp <= v -> v + 24 <= hl_sptop L -> v mod 8 = 0 -> L5.defined M v 24 ->
    PGV8.v8_at segs T3 T4 M v x -> incl (PGV8.v8_own x) LB ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        L5C.hpres L (lb_remove_v8 x LB) sp (pm_scr 0) [(v, 24)] M M' ->
        model_but_vm model model' -> hi_heap HI (lb_remove_v8 x LB) cr M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_vu8_dtor AN) M model) K.

End Specs.
End PNR.
