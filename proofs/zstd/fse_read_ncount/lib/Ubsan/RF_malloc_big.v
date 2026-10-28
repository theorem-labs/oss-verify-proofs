(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocBlocks MallocHINV.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import Malloc_fp F_malloc_enf F_malloc_join F_malloc_small F_malloc_entry F_malloc_bigw F_malloc_big MallocFacts_AM.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A RMalloc_fp RF_enframe RF_malloc_enf RAllocSlot_iface RF_malloc_entry RF_malloc_join RF_malloc_small RF_malloc_core RMallocKit_A2 RF_malloc_bigw.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require MallocFacts_inv4.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma rmrep_ext : forall st st' m,
rmrep st m ->
s_regions st' = s_regions st -> ctx st' = ctx st -> (forall q, get_meta_rec st' q = get_meta_rec st q) ->
s_areas st' = s_areas st -> s_groups st' = s_groups st -> (forall rid, get_shadow st' rid = get_shadow st rid) ->
s_statics st' = s_statics st ->
rmrep st' m.
Proof.
intros st st' m (WF & CX & GL & AR & GR & SH) ER EC EM EA EG ES ERs.
assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
split; [|split; [|split; [exact GL|split; [|split]]]].
- exact (rregions_wf_restatics _ _ ER EA EG ERs WF).
- eapply rmrep_ctx_ext; [exact EC| exact Hconc| exact CX].
- intros a ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply EM| exact (AR a ar Ha)].
- intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc| exact (GR b gh Hb)].
- intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.
Section FINAL.
Variables (st3 : mstate) (g : aptr) (rid : N) (xa n c : Z).
Hypothesis G0 : get_meta_rec st3 g = meta0.
Hypothesis GN : (s_groups st3) !! (rid, 0) = None.
Hypothesis HC : c_mmap_counter (ctx st3) = c.
Hypothesis NR : 0 <= n < 2^32.
Hypothesis RR : (s_regions st3) !! rid = Some (mkRegion RKGroup xa (n + IB + UNIT)).
Let stF := big_final st3 g rid n.
Let stM := big_st st3 g rid n (u32 (c + 1)).
#[using="G0"] Lemma rbf_meta : get_meta_rec stF g = big_meta rid n.
Proof.
unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. cbn [default from_option id].
rewrite G0. reflexivity.
Qed.
#[using="Type"] Lemma rbf_meta_other q : q <> g -> get_meta_rec stF q = get_meta_rec st3 q.
Proof.
intros NE. unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
#[using="Type"] Lemma rbm_meta : get_meta_rec stM g = big_meta rid n.
Proof. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. reflexivity. Qed.
#[using="Type"] Lemma rbm_meta_other q : q <> g -> get_meta_rec stM q = get_meta_rec st3 q.
Proof.
intros NE. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land].
rewrite lookup_insert_ne by congruence. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
#[using="GN"] Lemma rbf_groups : s_groups stF = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof.
unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land]. unfold group_active_idx, get_group. cbn -[Z.add Z.mul Z.div Z.land].
rewrite GN. reflexivity.
Qed.
#[using="Type"] Lemma rbm_groups : s_groups stM = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof. reflexivity. Qed.
#[using="Type"] Lemma rbf_shadow_other q : q <> rid -> get_shadow stF q = get_shadow st3 q.
Proof.
intros NE. unfold stF, big_final, get_shadow. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
#[using="HC"] Lemma rbf_ctx : ctx stF = ctx stM.
Proof. unfold stF, stM, big_final, big_st, ctx. cbn -[Z.add Z.mul Z.div Z.land u32]. unfold ctx in HC. rewrite HC. reflexivity. Qed.
#[using="HC stM"] Lemma rbf_counter : c_mmap_counter (ctx stF) = u32 (c + 1).
Proof. rewrite rbf_ctx. reflexivity. Qed.
#[using="G0 GN HC"] Lemma rmrep_big_final m : rmrep stM m -> rmrep stF m.
Proof.
intros MR. eapply (rmrep_ext stM stF m MR); try reflexivity.
- exact rbf_ctx.
- intros q. destruct (decide (q = g)) as [->|NE]; [rewrite rbf_meta, rbm_meta; reflexivity| rewrite rbf_meta_other, rbm_meta_other by exact NE; reflexivity].
- rewrite rbf_groups, rbm_groups. reflexivity.
Qed.
#[using="NR"] Lemma rbf_stride : get_stride (big_meta rid n) = big_ml n * 4096 - 16.
Proof.
unfold get_stride, big_meta. cbn [m_last_idx m_maplen]. Local Ltac2 Set LiaHints.tbl := fun () => "0020>18855444922.2136641733805.1400000900=S2NR1H2H0S2NR".
rewrite big_ml_eq by lia.
replace ((n + 4115) / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; Z.div_mod_to_equations; lia).
cbn. rewrite <- big_ml_eq by lia. unfold UNIT. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rbf_slots : s_slots stF = <[(rid, 16) := (g, 0)]> (s_slots st3).
Proof.
unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land get_stride get_meta_rec Z.sub].
unfold aadd. cbn [fst snd]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.
End FINAL.
#[using="Type"] Lemma rrepfoot_where2 st m a : rmrep st m -> rrepfoot st a ->
a < ATOP /\ (RCTX <= a < RCTX + 928 \/ RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x38 \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8 \/ a < 0x10000 \/ 0x50000 <= a).
Proof.
intros MR RF. pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]];
unfold RCTX, RMLOCK, RLIBC, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *. atop_facts.
- Local Ltac2 Set LiaHints.tbl := fun () => "0040>20219916242.2320219916242.2420228154184.1820228154184.9 00000K00k01:01SS2Rb2Cb3Sb03Sb13RBC1D5ATOPRS3Rak2Ca3Sa03Sa13RB03RBC1D5ATOPRS2Rq2RC1D5ATOPRS2R15ATOPR2R22R32R42R82R9".
lia. - lia. - lia. - lia.
- destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa) as D. atop_facts.
pose proof (round_up_pg_ge (r_len ra)). lia.
- destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _ & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). pose proof (rreserved_disjoint1 _ _ RFb) as D. atop_facts.
pose proof (round_up_pg_ge (r_len rb)). lia.
- destruct (WR _ _ Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint1 _ _ RFq) as D. atop_facts. lia.
- lia. - lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rwrapper_munch_keeps st m m' (spv lo : Z) :
rmrep st m -> munch [(spv - 80, spv); (0x2ee8c, 0x2ee8c + 4)] m m' -> wmono usegs m m' -> ATOP <= spv - 80 ->
rmrep st m'.
Proof.
intros MR MU WM HS. eapply (rmrep_transport_unowned st m m' _ MR MU WM).
Local Ltac2 Set LiaHints.tbl := fun () => "0010>59323410545.1700000;S2HS2Ha1A1B".
intros lo' hi' a [E|[E|[]]] Ha RF; inversion E; subst; destruct (rrepfoot_where2 st m a MR RF) as [A B]; unfold RCTX, RMLOCK, RLIBC, RGOT_SSP, RSSP_GUARD in *; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rpres_except_of_munch_nw C W m m' :
munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof.
intros MU HW a Ha Hc. Local Ltac2 Set LiaHints.tbl := fun () => "0010>56765666539.10000004S2Ha".
assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
split; [exact E|]. unfold wview. rewrite E. auto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rfp_below_ceiling K st3 stx m lo spv a :
rmrep st3 m -> spv <= a -> ATOP <= a -> ~ (ralloc_fp K st3 lo spv a \/ fresh_addr stx a).
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>59323410545.1359323410545.1659323410545.198841017104.13 00000?00@00J00KS2H11X2H25ATOPRFS2H22Xa2RCS".
intros MR H1 H2 [[X|[X|[X|(q & rq & Hq & _ & Xa)]]]|[X _]]; try lia.
- rewrite unsigned_lit in X by lia. atop_facts. lia.
- unfold RCTX in *. atop_facts. lia.
- pose proof MR as (WF & _). pose proof WF as (_ & WR & _). destruct (WR q rq Hq) as (_ & _ & _ & RC & _). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rbig_stride n rid : 0 <= n < 2^32 -> get_stride (big_meta rid n) = round_up_pg (n + IB + UNIT) - 16.
Proof. intros Hn. rewrite rbf_stride, big_ml_eq, round_up_pg_4115 by lia. reflexivity. Qed.
#[using="Type"] Lemma rregion_facts_hi : forall st m rid r,
rmrep st m -> (s_regions st) !! rid = Some r ->
r_base r + round_up_pg (r_len r) <= 0x1e000 \/ 0x50000 <= r_base r.
Proof.
intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
destruct (rreserved_disjoint _ _ RFr) as (_ & _ & _ & D). exact D.
Qed.
Definition rAMP_BIG (ram_pre : mstate -> Prop) : Prop :=
forall st LB t xa n, RAREACH st LB -> MMAP_THRESHOLD <= n < 2^32 ->
mmap_answer_ok ATOP (live_ranges (set_tick t st)) (n + IB + UNIT) xa = true -> is_err xa = false ->
ram_pre (step_seq (fst (new_region RKGroup xa (n + IB + UNIT) (set_tick t st)))).
#[using="Type"] Lemma ramp_big : rAMP_BIG (am_pre_g ref_reserved).
Proof.
intros st LB t xa n AR NR VOK ISE. unfold am_pre_g. apply AMpre_big_call; [exact (MallocFacts_inv4.areach_ampre_proof _ _ AR)|].
unfold IB, UNIT, MMAP_THRESHOLD in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010>31172843022.11000004S2NR".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section BIG.
Variable ram_pre : mstate -> Prop.
Hypothesis AM : ralloc_meta_stmt ram_pre.
Hypothesis AMP : rAMP_BIG ram_pre.
#[using="ram_pre AM AMP"] Lemma rbig_spec : rbig_stmt.
Proof.
pose proof AMP as AMP_BIG. unfold rAMP_BIG in AMP_BIG.
intros o m0 st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo t m1 errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r t3 t4 t5 t6 ra' st1.
intros AR MF MR0 TP CLO LO NR BL MR1 TK1 UA1 MI1 ST1 FR1 ERR1 AUX1 PE1.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold RAM_STACK in LO. unfold MMAP_THRESHOLD in NR.
Local Ltac2 Set LiaHints.tbl := fun () => "02h0?10068780064.23610534872771.125133980655.110  13743415799.21013768873754.78 14010212115.19514786946964.69 14788761266.19514790999216.21714791009665.10015047292336.23615211002786.20215211002786.23515529344774.19516187854478.77 16807445354.77 1682179005.146 17991071757.21517991104526.13517991414417.71 17997677457.15317997742848.23217997742862.22318460325067.82 19245567059.20319652550953.18620534863267.12820534863267.15020534865073.12120534922610.2332067834974.231 21122673213.19521137365920.71 21908340778.24721966953530.23622037355069.23522043379654.20222043379654.22622043379654.23522043643862.2312253775594.71  23018907393.12123018908187.14723018909203.12123019172713.1252423491514.224 2426971491.234 2426988754.236 24929764898.23624983202619.24924996521177.18625071898026.84 25071956112.77 25075859045.14926358950539.15326494861100.22926879286852.23226879286858.22328573734967.22528573882423.24828573888615.21929524288756.13529524291444.21829524452599.21529524502512.99 3022852449.226 30235536431.2393024687457.81  31185573393.95 31187606295.12031292287353.21831292563965.99 32051918277.22432051918277.23332419579590.14332921336925.19532927698140.14436027624326.195362166535.253  36473240265.23836642204960.23636642221988.22736654802212.23337792503789.12137792504567.14737792505599.12137792760709.12537794366648.13538715948274.81 38717783282.20238717783282.22338717783282.22638717783282.23238829501949.12139042514146.24740328959280.99 40328959352.12940655993129.12540760572015.1474081038656.236 4111386568.236 44017328668.2364511410525.237 45393275060.21746836598598.23646856919211.23647098239585.19547102046774.12147102049060.12147102050092.14747102305886.12547104223968.14447478388169.23649227435899.21549237472487.15349239901532.71 51902538964.23652300761199.12552507718435.23552509552344.20252509552344.22652509552344.2355251256473.195 53091630391.18454179732855.19556765530045.22556765667309.12156765667309.12856765667309.15056765667309.21956765669119.12156899489284.15357394141695.23557477059391.23657622606836.24559227879194.10159308579027.25159308587409.11059314873579.24659314938599.24559315137787.24461007160479.2276195737636.77  62315620027.71 6273691775.147 64146291918.19564148360531.71 6426363069.248 6428573309.243 6432603914.245 6432667910.143 64618458169.23666151427842.2506644529898.236 66519621351.23667442659576.1276755913069.235 6757748886.202 6757748886.226 6757748886.235 67793881970.13568367801238.23368367867290.2347131003197.235 7137551558.202 7137551558.226 7137551558.235 7390272437.236 8754299652.71  8826221466.81  8828204471.100 8828204971.71  8828302597.100 8828316724.217 8828484023.184 8832250778.226 8832250778.244 8838596267.153 8838661684.223 8838661686.195 8838854330.230 8841002501.94  8841017104.69  9266691294.147 00000100800900H00I00Q00c01501G01Y01Z01]01`01d01l02:02N02S02X02]02b02g02l03903:03>03L03S03W03^03f03g03h04404904@04F04L04X04_04m05@05S05f06906N06R06V06W07407?07S07a07b07j08B08C08D08^09N09b09f09j09n0:20:50:90:=0:A0:E0:S0:a0:h0:o0;70;;0;?0;C0;Z0;`0;d0;h0;l0<?0<R0<e0=80=K0=R0=X0=[0=a0=d0=h0>E0>F0>G0>H0>V0>W0>[0>\0>`0>a0>b0>l0?60?@0?J0?T0?^0?h0?i0?m0@10@50@60@70@;0@>0@A0@D0@H0@I0@W0@[0@k0A@0AD0AY0A]0Aa0Al0Am0B30BE0BQ0BU0B]0Be0C20C80CF0CJ0CX0CY0CZ0Cj0D:0DJ0DZ0D[0E80E=0EB0EU0EV0EW0EX0EY0Ei0El0Eo0F30F60F90FB0FC0FG0FH0FI0FJ0FK0FL0FM0FN0FO0FP0FQ0FR0FS0FT0FU0FVSS2NR2LGSS5ATOPR4Gpos2GCSS3CLO2XCS3CLO2LO3SPR5ATOPRS3CLO2LO3SPR5ATOPRS3CLO2LO3SPR5ATOPRS3CLO2LO3SPR5ATOPRSS1XS1XS2NRS3CLO2LOS3CLO2LO5ATOPRS3CLO2LO5ATOPR2XC2XIS3CLOS3CLOS3CLOS3CLOS3CLOS3CLOS5ATOPR2R12R2SS2HaS3CLO2LO2XC2HaS2XI2HaS2HoS2Xa2D2S2Xa1D1HSSS3GI13GI22H0S3ML1S2XC2HaS2XC1XS2XC1XS2NR2XC2LG1XS2Xa2RCS3CLO2LO5ATOPRS2NR5ATOPR2X02XC2LGS2NR5ATOPR2X02XC2LGS2NR5ATOPR2X02XC2LGS2NR5ATOPR2X02XC2LGS5ATOPR2XI1X2NR2X02LGS2NRS2NRSS2NR2X02XA3GI13GI22RU1H2H02H4S3CLO2LO2HaS3CLO2LO5ATOPR2R22R3S3CLO2LO5ATOPRSS3CLO2LOS2NR2X02XA2LG2XI3GI13GI2SSS3CLO2LO2NR5ATOPR2XC2LG2A1S2NR2X02XA2LG2XI4Gpos3GI13GI22NE2Ho2B01D1H2H02H1S3CLO2LO5ATOPR2XC2HaS2LOS2LOS2LOS2LOS1XS2HfS2HXS2NRS2NRS3CLO2LO5ATOPRS3CLO2LO5ATOPRS2NX2E2S2NX2E2S2Ho1D1HS2X0S2X0S2XIS3GI13GI23LUB4Hfit1H2H0S2Ho1TS2NRS2NRS2NRS2NR5ATOPR2X02XC2LGS2NR5ATOPR2X02XC2LGS2NR5ATOPR2X02XC2LGS2NR5ATOPR2X02XC2LGS2NR5ATOPR2X02XC2LGS2LO2HXS2LO1XS1XS2LO1XS1XS2HaS2NR2X02XA2LG3GI13GI21H2H02H4SSFS3CLO2LO5ATOPRSS2LGSS2HoSSS2NR2LG2RUS5ATOPR2XCS5ATOPR2XCS5ATOPR2XCS5ATOPR2XCS5ATOPR2XCS5ATOPR2XCSS2NRS2NRS2NRSFS2HaS1XS1XS1XS2LOSS3CLO2LO5ATOPRS2HaS5ATOPR2X02XC2HaS3CLO2LO3SPR5ATOPR2HaS2HaS3CLO2LO3SPR5ATOPR2HaS2HaS2LOS3GLg3GHg1XSS2Ho1DS3CLO2LO5ATOPR3SP'S2Ho2Xa1H2H0S2HrS2Ho1Y1HS2Ho1X1DS3CLO2Ho2BC1XS4HoutS3CLO2LO5ATOPRS2NRS3CLO2LO5ATOPRSSS5ATOPR2Ho2B02BCS5ATOPR2Ho2B02BCS5ATOPR2Ho2B02BCS5ATOPR2Ho2B02BCSS2NR2X02XA2LG3GI13GI21H2H02H4S3ML1S3LUBS2NR2X02XA2LG2XI2HwSSSSS2NR5ATOPR2XC2LGS1DS1DS2HaS1XS1XS2NR2LG1XSS2LOSSSSSSSSSSSSSSF".
rewrite (malloc_core_big_eq st1 n) by (unfold MMAP_THRESHOLD; lia).
riprefixT. atop_facts. subst tp. unfold RATP in ERR1. rewrite unsigned_lit in ERR1 by lia.
unfold RMLOCK.
step. step. step. step. step. step. step. step. step.
apply evt_done.
set (sp' := Z_to_bv 64 (bv_unsigned sp + -48)).
assert (SP' : bv_unsigned sp' = bv_unsigned sp + -48) by (subst sp'; apply unsigned_lit; lia).
eapply rimplT_mmap_rw.
{ eapply (rmmap_anon_spec false) with (lo := lo) (avoid := []);
[ rewrite SP'; exact ST1 | unfold RATP; rewrite unsigned_lit by lia; exact ERR1 | exact MI1 | reflexivity | unfold IB, UNIT; f_equal; lia
| reflexivity | reflexivity | reflexivity | reflexivity | unfold IB, UNIT; lia | rewrite SP'; lia | atop_facts; lia
| rewrite SP'; unfold RATP; rewrite unsigned_lit by lia; lia | unfold RATP; rewrite unsigned_lit by lia; lia ]. }
intros ans ms' PO.
assert (FRAME : forall m2, munch [(bv_unsigned sp' - 80, bv_unsigned sp'); (192304 + -164, 192304 + -164 + 4)] m1 m2 -> wmono usegs m1 m2 ->
rw_cells usegs m2 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] /\ rmrep st1 m2 /\ rauxv_ok m2 (bv_unsigned sp)
/\ rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m2 /\ unk_agree st1 o m2).
{ intros m2 MU WM. rewrite SP' in MU. split; [|split; [|split; [|split]]].
- eapply rw_cells_transport; [exact FR1| exact MU| exact WM| cbn; lia].
- eapply (rwrapper_munch_keeps st1 m1 m2 (bv_unsigned sp + -48) lo MR1); [| exact WM| atop_facts; lia].
eapply munch_weaken; [|exact MU]. intros y; cbn; lia.
- eapply rauxv_ok_frame; [exact AUX1| exact MU| exact WM|]. unfold RAUXV_CELL.
constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
- eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch; [exact MU| exact WM|].
intros a Ha NC. cbn. split; [|split; [|exact I]]; intros HX; apply NC; left; [left; lia| right; left]. rewrite unsigned_lit by lia. lia.
- eapply unk_agree_munch; [exact UA1| exact MU| |].
+ intros rid r Hr Hk. pose proof (rregion_facts st1 m1 rid r MR1 Hr) as (R1 & _ & R2 & _). pose proof (rregion_facts_hi st1 m1 rid r MR1 Hr) as R3. atop_facts. cbn. lia.
+ intros rid r Hr. pose proof (rregion_facts st1 m1 rid r MR1 Hr) as (R1 & _ & R2 & _). atop_facts. lia. }
destruct ans as [e|xa].
-
cbn [rmmap_anon_post] in PO.
destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & He).
cbn [mmap_val]. rewrite (rregions_wf_atop st1 (proj1 MR1)). destruct (mmap_answer_ok_err (live_ranges st1) (n + IB + UNIT) e He) as [-> ->]. cbn [negb].
apply rimplT_ret.
unfold RATP in MU2, ERR2. rewrite unsigned_lit in MU2 by lia. rewrite SP' in ST2. rewrite unsigned_lit in ERR2 by lia.
destruct (FRAME m2 MU2 WM2) as (FR2 & MR2 & AUX2 & PE2 & UA2).
replace (ret_pc (Z_to_bv 64 0x15d1c)) with (Z_to_bv 64 0x15d1c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
eapply evt_cut. { eapply rbig_fail1_walk; [exact FR2| exact ST2| lia| lia]. }
intros ms'' [-> ST3]. apply evt_done. cbn [rcoreQ].
exists m2, (Z_to_bv 64 (MM_syscalls.mmap_fix_errno e)). do 14 eexists. split; [reflexivity|].
split; [exact MR2|]. split; [exact TK1|]. split; [exact MI2|]. split; [exact ST3|].
split; [unfold RATP; rewrite unsigned_lit by lia; exact ERR2|]. split; [exact AUX2|]. split; [exact PE2|].
split; [apply mrel_same; reflexivity|]. split; [exact BL|]. repeat split; reflexivity.
-
cbn [rmmap_anon_post] in PO.
destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & AOK).
cbn [mmap_val]. rewrite (rregions_wf_atop st1 (proj1 MR1)).
destruct (mmap_answer_ok ATOP (live_ranges st1) (n + IB + UNIT) xa) eqn:VOK.
2:{ cbn [negb]. apply rimplT_undef. }
cbn [negb].
destruct (mmap_answer_ok_addr (live_ranges st1) (n + IB + UNIT) xa ltac:(unfold IB, UNIT; lia) AOK VOK) as (X0 & XA & XC & XRF & ISE). rewrite ISE.
unfold RATP in MU2, ERR2. rewrite unsigned_lit in MU2 by lia. rewrite SP' in ST2. rewrite unsigned_lit in ERR2 by lia.
destruct (FRAME m2 ltac:(eapply munch_weaken; [|exact MU2]; intros y; cbn; lia) WM2) as (FR2 & MR2 & AUX2 & PE2 & UA2).
unfold new_region.
set (rid := s_next_rid st1). set (st2 := set_next_rid (N.succ rid) (set_regions (<[rid:={| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}]> (s_regions st1)) st1)).
assert (Est2 : st2 = fst (new_region RKGroup xa (n + IB + UNIT) st1)) by reflexivity.
pose proof (mf_ptrs _ _ MF) as [PT0 FRESH0].
assert (PT1 : ptrs_in (fun r => r <> rid) st1).
{ eapply ptrs_in_mono; [|exact PT0]. intros r Hr. cbn in Hr. subst rid. unfold st1. cbn. intros ->. lia. }
destruct (FRESH0 rid ltac:(subst rid; unfold st1; cbn; lia)) as [FRr FRs].
set (L := mmap_len (n + IB + UNIT)).
assert (EL : L = round_up_pg (n + IB + UNIT)) by apply mmap_len_round_up.
pose proof (round_up_pg_ge (n + IB + UNIT)) as LG. rewrite <- EL in LG, XC, XRF.
unfold MM_syscalls.mmap_raw in ST2 |- *. cbn [negb] in ST2 |- *. fold L. fold L in ST2.
assert (ELm : mmap_len (n + IB + UNIT) = L) by reflexivity. clearbody L. atop_facts. unfold IB, UNIT in LG.
set (mz := apply_zeros m2 [(wa xa, Z_to_bv 64 L)]).
assert (ZO : forall a, 0 <= a < 2^64 -> (a < xa \/ xa + L <= a) -> mz (wa a) = m2 (wa a)).
{ intros a Ha Ho. unfold mz. apply (zeros_outside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
assert (ZI : forall a, xa <= a < xa + L -> mz (wa a) = Some (b8 0)).
{ intros a Ha. unfold mz. apply (zeros_inside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
assert (MRz : rmrep st2 mz).
{ rewrite Est2. eapply (rmrep_new_region st1 m2 mz xa (n + IB + UNIT) RKGroup MR2 PT1 FRs X0 XA ltac:(unfold IB, UNIT; lia));
rewrite <- ?EL; [atop_facts; exact XC| exact XRF| exact ZO| intros _; exact ZI]. }
fold mz in ST2 |- *.
pose proof MR1 as (WF1 & _). pose proof WF1 as (RS1 & WR1 & _).
assert (XI : xa + L <= 0x10000 \/ 0x50000 <= xa).
{ assert (RFimg : ranges_free ref_reserved xa L = true).
{ apply ranges_free_intro. intros b k HI. apply (ranges_free_In _ _ _ _ _ XRF). unfold live_ranges. apply in_or_app. left. rewrite (rstatics_reserved _ RS1). exact HI. }
apply (rreserved_disjoint1 _ _ RFimg). lia. }
assert (MIz : mem_inv usegs mz).
{ unfold mz. apply (mem_inv_zeros usegs m2 xa L); try lia; [exact MI2|]. intros w Hw. apply ref_ro_addr_false. lia. }
assert (FRz : rw_cells usegs mz (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]).
{ eapply rrw_cells_agree; [exact FR2|]. intros a Ha. cbn in Ha. apply ZO; lia. }
assert (TKz : ticks_ok st2) by (rewrite Est2; exact TK1).
assert (UAz : unk_agree st2 o mz).
{ eapply (unk_agree_transfer st1 st2 o m2 mz UA2). intros q r Hq Hk.
rewrite Est2 in Hq. destruct (rnr_lookup_inv st1 xa (n + IB + UNIT) RKGroup q r Hq) as [[-> ->]|[NE Hq1]].
- right. intros off h Ho Hc. exfalso. rewrite Est2 in Hc. rewrite (rnr_shadow st1 xa (n + IB + UNIT) RKGroup) in Hc.
unfold get_shadow in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc. rewrite cell_read_shadow0 in Hc. discriminate.
- left. split; [exact Hq1|]. split; [rewrite Est2; apply rnr_shadow|]. split; [intros off X; exact X|].
intros off h Ho Hc NG. destruct (WR1 q r Hq1) as (B0 & _ & _ & BC & _). atop_facts.
pose proof (rnr_old_disjoint st1 xa (n + IB + UNIT) ltac:(rewrite <- EL; exact XRF) q r Hq1) as D.
pose proof (lr_lo_group r Hk). rewrite <- EL in D. apply ZO; lia. }
riprefixT.
replace (ret_pc (Z_to_bv 64 0x15d1c)) with (Z_to_bv 64 0x15d1c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
pose proof (mf_ctx _ _ MF) as FC. destruct FC as (FC1 & FC2 & FC3 & FC4 & FC5 & FC6).
change (ctx (strip st)) with (ctx st) in FC1, FC2, FC3, FC4.
eapply evt_cut.
{ eapply (rbig_seq_walk sp gp (Z_to_bv 64 192304)) with (st := st2) (lo := lo);
[exact MRz| rewrite Est2; exact FC4| rewrite unsigned_lit by lia; lia| exact FRz| exact ST2| lia| atop_facts; lia| exact MIz]. }
intros ms1 (wa0 & wa1 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & MR3).
apply evt_done.
assert (MUz : munch [(xa, xa + L)] m2 mz) by (apply munch_of_pointwise; [lia| lia| exact ZO]).
assert (WMz : wmono usegs m2 mz) by (intros w Hw; unfold mz; apply (wview_zeros_mono usegs m2 xa L); try lia; exact Hw).
assert (AUXz : rauxv_ok mz (bv_unsigned sp)).
{ eapply rauxv_ok_frame; [exact AUX2| exact MUz| exact WMz|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)).
{ eapply rauxv_ok_frame; [exact AUXz| exact MU3| exact WM3|]. unfold RAUXV_CELL, RCTX.
constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor. }
assert (ERRz : rw_cells usegs mz (192304 + -164) [C4 errv]).
{ eapply rrw_cells_agree; [exact ERR2|]. intros a Ha. cbn in Ha. apply ZO; lia. }
assert (ERR3 : rw_cells usegs m3 (192304 + -164) [C4 errv]).
{ eapply rw_cells_transport; [exact ERRz| exact MU3| exact WM3|]. unfold RCTX. cbn. lia. }
assert (Hconc2 : forall q, fst q <> rid -> conc st2 q = conc st1 q) by (intros q Hq; rewrite Est2; apply rnr_conc; exact Hq).
assert (BL2 : brk_link_ps (step_seq st2) s).
{ eapply (brk_link_ps_ext st1); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| | exact BL].
intros rb ob Hb. transitivity (conc st2 (rb, ob)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
apply Hconc2. cbn. destruct PT1 as (_ & _ & _ & _ & _ & _ & P7 & _). rewrite Hb in P7. exact P7. }
assert (TK2' : ticks_ok (step_seq st2)) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); exact TKz).
eapply AM.
{ apply (AMP_BIG st LB t xa n AR); [unfold MMAP_THRESHOLD; lia| exact VOK| exact ISE]. }
{ exact MR3. }
{ exact TK2'. }
{ exact BL2. }
{ rewrite SP'. eapply rauxv_ok_weaken; [exact AUX3| atop_facts; lia]. }
{ rewrite SP'. exact ST3. }
{ atop_facts; lia. }
{ rewrite SP'. unfold RAM_STACK. lia. }
{ unfold RATP. rewrite unsigned_lit by lia. exact ERR3. }
{ exact MI3. }
{ reflexivity. }
intros st3 mo s' ms' PO3 BL3.
destruct PO3 as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m4 & errv4 & -> & MI4 & ST4 & ERR4 & AUX4 & PE4 & MR4 & TK4 & PSM & PSF & PSO & REL).
rewrite SP' in ST4, AUX4, PE4. unfold RATP in ERR4. rewrite unsigned_lit in ERR4 by lia.
replace (ret_pc (Z_to_bv 64 0x15e10)) with (Z_to_bv 64 0x15e10) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
lazymatch type of FR3 with rw_cells _ _ _ ?cs => assert (FR4 : rw_cells usegs m4 (bv_unsigned sp + -48) cs) end.
{ eapply rpres_except_rw_cells; [exact PE4| exact FR3|]. intros a Ha. cbn in Ha. eapply (rfp_below_ceiling _ st3 _ m4); [exact MR4| lia| atop_facts; lia]. }
assert (RR2 : s_regions (step_seq st2) !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
{ rewrite step_seq_eq. destruct (c_seq (ctx st2) =? 255); (rewrite Est2; apply rnr_lookup_new). }
assert (RR3 : s_regions st3 !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
{ destruct (amr_regions _ _ _ REL rid _ RR2) as (r' & Hr' & K' & B' & L' & G'). rewrite Hr'. f_equal. apply G'. reflexivity. }
assert (PT2 : ptrs_in (fun q => q <> rid) (step_seq st2)) by (apply ptrs_in_step_seq; rewrite Est2; apply ptrs_in_new_region; exact PT1).
assert (PT3 : ptrs_in (fun q => q <> rid) st3).
{ apply (amr_ptrs _ _ _ REL); [|exact PT2]. intros q rq Hq Hk ->. rewrite RR3 in Hq. inversion Hq; subst. apply Hk. reflexivity. }
pose proof MR4 as (WF4 & _ & (ML4 & _) & _). pose proof WF4 as (RS4 & WR4 & DJ4 & _).
assert (RS3 : s_reserved st3 = ref_reserved) by exact (rstatics_reserved _ RS4).
assert (PE14 : forall stF, s_reserved stF = s_reserved st ->
(forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a) ->
rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m4).
{ intros stF RSF HFP.
eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU2| exact WM2|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC; left; left; lia. }
eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MUz| exact WMz|]. intros a Ha NC. cbn. split; [|exact I]. intros X. apply NC.
do 4 right. split; [atop_facts; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU3| exact WM3|]. intros a Ha NC. cbn. unfold RCTX in *. atop_facts.
split; [|split; [|exact I]]; intros X; apply NC; left; [right; right; left; unfold RCTX; lia| right; right; left; unfold RCTX; lia]. }
eapply rpres_except_mono; [exact PE4|]. intros a [X|X]; [apply (HFP a X)|].
do 4 right. eapply (fresh_addr_anti st (step_seq st2)); [| |exact X].
{ transitivity (s_reserved st2); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| rewrite Est2; reflexivity]. }
intros q rq Hq. exists rq. split; [|repeat split; auto; lia].
transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2, rnr_lookup_old; [exact Hq|]. intros ->. unfold st1 in Hq. cbn in Hq. fold rid in FRr. unfold st1 in FRr. cbn in FRr. rewrite FRr in Hq. discriminate. }
destruct mo as [g|].
+
apply rimplT_ret.
destruct (amr_result _ _ _ REL g eq_refl) as [G0 MSL].
pose proof (rmeta_chunk_facts st3 m4 g MR4 MSL) as (_ & Gpos & GC & GI1 & GI2 & GRG & (ridg & rg & Hrg & Krg & GLg & GHg)).
set (G := conc st3 g) in *.
assert (HG : bv_unsigned (pw st3 (Some g)) = G) by (unfold pw, oconc; fold G; apply wz_unsigned; atop_facts; lia).
assert (GN3 : forall off, (s_groups st3) !! (rid, off) = None).
{ intros off. destruct ((s_groups st3) !! (rid, off)) as [gh|] eqn:E; [|reflexivity].
destruct PT3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
assert (AN3 : forall off, (s_areas st3) !! (rid, off) = None).
{ intros off. destruct ((s_areas st3) !! (rid, off)) as [ar|] eqn:E; [|reflexivity].
destruct PT3 as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
assert (SHN3 : (s_shadow st3) !! rid = None).
{ rewrite (amr_shadow _ _ _ REL). transitivity (s_shadow st2 !! rid); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2. exact FRs. }
assert (HC3 : c_mmap_counter (ctx st3) = c_mmap_counter (ctx st)).
{ rewrite (amr_counter _ _ _ REL). transitivity (c_mmap_counter (ctx st2)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2. reflexivity. }
eapply evt_cut.
{ eapply (rbig_succ_walk st3 m4 g rid xa n (c_mmap_counter (ctx st)) lo MR4 TK4 G0 MSL RR3 GN3 AN3 SHN3 HC3 FC1 ltac:(unfold MMAP_THRESHOLD; lia) ltac:(atop_facts; lia) sp gp (Z_to_bv 64 192304));
[exact HG| exact FR4| exact ST4| lia| exact MI4]. }
intros ms5 (a0' & a1' & m7 & -> & MU7 & WM7 & MI7 & ST7 & FR7 & MR7 & TK7).
apply evt_done. cbn [rcoreQ].
set (stF := big_final st3 g rid n).
rewrite (rbf_counter st3 g rid n (c_mmap_counter (ctx st)) HC3).
change (pw st3 (Some g)) with (pw stF (Some g)).
exists (rid, 0), {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}, m7, errv4. do 17 eexists.
split; [reflexivity|].
assert (MRF : rmrep stF m7) by (apply (rmrep_big_final st3 g rid n _ G0 (GN3 0) HC3); exact MR7).
split; [exact MRF|].
split; [exact TK7|].
assert (STRIDE : get_stride (big_meta rid n) = L - 16) by (rewrite rbig_stride by lia; rewrite <- EL; reflexivity).
assert (NL : forall q rq, (s_regions st3) !! q = Some rq -> q <> rid -> xa + L <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= xa).
{ intros q rq Hq NE. destruct (DJ4 q rq rid _ Hq RR3 NE) as [D|D]; cbn [r_base r_len lr_lo r_kind] in D; rewrite <- ?EL in D; [|lia]. pose proof (lr_lo_ge rq). lia. }
split.
{
assert (UA3 : unk_agree (step_seq st2) o m3).
{ eapply (unk_agree_transfer st2 (step_seq st2) o mz m3 UAz). intros q r Hq Hk. left.
assert (Hq2 : s_regions st2 !! q = Some r) by (revert Hq; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); intros Hq; exact Hq).
split; [exact Hq2|]. split; [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
split; [intros off X; eapply grp_hdr_cov_same; [|exact X]; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
intros off h Ho Hc NG. pose proof MRz as (WFz & _). pose proof WFz as (_ & WRz & _).
destruct (WRz q r Hq2) as (B0 & _ & _ & BC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). atop_facts.
apply MU3. rewrite wa_unsigned by lia. cbn. unfold RCTX. lia. }
assert (UA4 : unk_agree st3 o m4).
{ eapply (unk_agree_transfer (step_seq st2) st3 o m3 m4 UA3). intros q r Hq Hk. left.
assert (Hq2 : s_regions (step_seq st2) !! q = Some r).
{ destruct ((s_regions (step_seq st2)) !! q) as [r2|] eqn:E.
- destruct (amr_regions _ _ _ REL q r2 E) as (r' & Hr' & K' & _ & _ & G'). rewrite Hq in Hr'. inversion Hr'; subst r'. f_equal. symmetry. apply G'. rewrite <- K'. exact Hk.
- exfalso. exact (amr_new _ _ _ REL q r Hq E Hk). }
split; [exact Hq2|]. split; [unfold get_shadow; rewrite (amr_shadow _ _ _ REL); reflexivity|].
split; [intros off X; eapply grp_hdr_cov_same; [|exact X]; exact (amr_groups _ _ _ REL)|].
intros off h Ho Hc NG. destruct (WR4 q r Hq) as (B0 & _ & _ & BC & RFq). atop_facts.
refine (proj1 (PE4 (r_base r + off) ltac:(lia) _)).
intros [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
- lia.
- rewrite unsigned_lit in X by lia. pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). lia.
- unfold RCTX in X. pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). lia.
- assert (NE : q2 <> q) by (intros ->; rewrite Hq in Hq'; inversion Hq'; subst; apply Kq2; exact Hk).
pose proof (lr_lo_group r Hk). destruct (DJ4 q2 rq2 q r Hq' Hq NE); lia.
- pose proof (fresh_live_region (step_seq st2) (r_base r + off) q r X Hq2) as Y. pose proof (lr_lo_group r Hk). lia. }
eapply (unk_agree_transfer st3 stF o m4 m7 UA4). intros q r Hq Hk. change (s_regions stF) with (s_regions st3) in Hq.
destruct (N.eq_dec q rid) as [->|NE].
- right. rewrite RR3 in Hq. inversion Hq; subst r. cbn [r_len]. intros off h Ho Hc.
change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid) in Hc.
rewrite cell_read_hh0 in Hc by (exact SHN3 || lia). destruct (off <? 12) eqn:T; [|discriminate]. apply Z.ltb_lt in T.
exists (rid, 0), (mkGhdr (Some g) 0). split; [|cbn; lia]. unfold stF. rewrite (rbf_groups st3 g rid n (GN3 0)). apply lookup_insert_eq.
- left. split; [exact Hq|]. split; [apply rbf_shadow_other; exact NE|].
split. { intros off (b & gh & Hb & Hf & Ho). exists b, gh. split; [|auto]. unfold stF. rewrite (rbf_groups st3 g rid n (GN3 0)).
rewrite lookup_insert_ne; [exact Hb|]. intros <-. cbn in Hf. congruence. }
intros off h Ho Hc NG. destruct (WR4 q r Hq) as (B0 & _ & _ & BC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). atop_facts.
pose proof (NL q r Hq NE). pose proof (lr_lo_group r Hk). pose proof (GRG q r Hq Hk).
apply MU7; rewrite wa_unsigned by lia; cbn; unfold RCTX; lia. }
split; [exact MI7|]. split; [exact ST7|]. split; [exact FR7|].
assert (ERR8 : rw_cells usegs m7 (192304 + -164) [C4 errv4]).
{ eapply rw_cells_transport; [exact ERR4| exact MU7| exact WM7|]. cbn. unfold RCTX. lia. }
split; [unfold RATP; rewrite unsigned_lit by lia; exact ERR8|].
assert (HFPF : forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a).
{ intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; exact X| right; right; left; exact X|].
right; right; right. exists q, rq. split; [exact Hq| split; [exact Kq| exact Xa]]. }
assert (PE18 : rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m7).
{ eapply rpres_except_trans. { apply (PE14 stF); [change (s_reserved stF) with (s_reserved st3); rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| exact HFPF]. }
eapply rpres_except_trans.
{ eapply rpres_except_of_munch; [exact MU7| exact WM7|]. intros a Ha NC. cbn. split; [|split; [|split; [|exact I]]]; intros X; apply NC.
- left. right; right; right. exists ridg, rg. split; [exact Hrg|]. split; [exact Krg|]. lia.
- do 4 right. split; [atop_facts; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia].
- left. right; right; left. unfold RCTX in *. atop_facts. lia. }
apply rpres_except_refl. }
split. { eapply (rauxv_ok_malloc_fp st stF lo (bv_unsigned sp) m0 m7 m1 m7); [exact MR0| exact MRF| exact AUX1| exact PE18| atop_facts; lia| lia]. }
assert (MRELF : mrel st stF).
{ split.
- intros q rq Hq.
assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
{ transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2, rnr_lookup_old by exact NE. exact Hq. }
destruct (amr_regions _ _ _ REL q rq Hq2) as (r' & Hr' & K' & B' & L' & _).
exists r'. split; [|repeat split; auto]. exact Hr'.
- change (s_next_rid stF) with (s_next_rid st3). pose proof (amr_next_rid _ _ _ REL) as NX.
assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
- change (s_reserved stF) with (s_reserved st3). rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
split. { eapply rpres_except_trans; [| exact PE18]. eapply rpres_except_mono; [exact PE1|]. intros a Ha.
eapply rmalloc_fp_mono; [apply (mrel_regions _ _ MRELF)| exact Ha]. }
rewrite (rbf_meta st3 g rid n G0). rewrite STRIDE. cbn [fst snd r_base r_len].
split. { intros a Ha. do 4 right. split; [atop_facts; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
split. { unfold u32. Z.div_mod_to_equations. lia. }
assert (ML1 : 32 <= big_ml n < 2^40) by (rewrite big_ml_eq by lia; Z.div_mod_to_equations; lia).
pose proof (round_up_pg_4115 n ltac:(lia)) as RU. rewrite <- EL in RU.
assert (LUB : L <= n + 4115) by (rewrite RU; Z.div_mod_to_equations; lia).
rewrite <- big_ml_eq in RU by lia.
split.
{ constructor; rewrite ?(rbf_meta st3 g rid n G0), ?STRIDE; cbn [m_mem m_last_idx m_avail m_freed m_freeable m_maplen m_sizeclass big_meta fst snd r_kind r_len].
- reflexivity.
- exact RR3.
- reflexivity.
- lia.
- reflexivity.
- lia.
- lia.
- rewrite <- EL. lia.
- lia.
- rewrite RU. Z.div_mod_to_equations. lia.
- lia.
- lia.
- lia.
- intros b' gh Hb' Hf. unfold stF in Hb'. rewrite (rbf_groups st3 g rid n (GN3 0)) in Hb'.
destruct (decide (b' = (rid, 0))) as [->|NEb]; [cbn; lia|].
rewrite lookup_insert_ne in Hb' by congruence. destruct b' as [b1 b2]. cbn in Hf. subst b1. rewrite GN3 in Hb'. discriminate.
- change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
rewrite cell_read_hh0; [| exact SHN3| lia]. replace (0 + 16 + (L - 16) * 0 - 4 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
- intros off Ho Hfit. Z.div_mod_to_equations. lia.
- unfold stF. rewrite rbf_slots. replace (0 + 16 + (L - 16) * 0) with 16 by lia. apply lookup_insert_eq.
- exact MSL.
- lia.
- lia.
- lia.
- lia.
- right. repeat split; lia. }
split. { intros _. unfold F_malloc_enframe.rdv. change (get_shadow stF (fst (rid, 0))) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
cbn [fst snd]. rewrite cell_read_hh0; [| exact SHN3| lia]. replace (0 + (16 + (L - 16) * 0) + -3 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
split; [exact MRELF|].
split. { eapply (brk_link_ps_ext st3); [reflexivity| intros; reflexivity| exact BL3]. }
repeat split; assumption.
+
cbn [pw oconc].
riprefixT.
eapply evt_cut.
{ apply rbig_fail2a_walk. exact ML4. }
intros ms2 ->. apply evt_done.
eapply rimplT_munmap.
{ eapply (rmunmap_spec) with (A := xa) (L := n + IB + UNIT) (lo := lo);
[ rewrite unsigned_lit by lia; exact ST4 | rewrite unsigned_lit by lia; exact ERR4 | exact MI4 | reflexivity | unfold IB, UNIT; f_equal; lia
| lia | rewrite ELm; lia | unfold IB, UNIT; lia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; rewrite unsigned_lit by lia; lia | rewrite ELm; left; atop_facts; lia
| rewrite ELm, unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia ]. }
intros ans2 ms3 PM. unfold rmunmap_post in PM.
destruct PM as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & ERR6 & He6).
rewrite (munmap_answer_ok_range ans2 He6). apply rimplT_ret.
rewrite ELm in MU6. rewrite !unsigned_lit in MU6 by lia. rewrite unsigned_lit in ST6 by lia. rewrite unsigned_lit in ERR6 by lia.
replace (ret_pc (Z_to_bv 64 0x15ee8)) with (Z_to_bv 64 0x15ee8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
lazymatch type of FR4 with rw_cells _ _ _ ?cs => assert (FR6 : rw_cells usegs m6 (bv_unsigned sp + -48) cs) end.
{ eapply rrw_cells_agree; [exact FR4|]. intros a Ha. cbn in Ha. apply MU6. rewrite wa_unsigned by lia. cbn. atop_facts. lia. }
eapply evt_cut. { eapply rbig_fail2b_walk; [exact FR6| exact ST6| lia| lia]. }
intros ms4 [-> ST7]. apply evt_done. cbn [rcoreQ].
set (stF := drop_region rid st3).
assert (MRF : rmrep stF m6).
{ eapply (rmrep_drop_region st3 m4 m6 rid _ MR4 RR3 PT3). intros a Ha Hout Hin. cbn [r_base r_len lr_lo r_kind] in Hout.
rewrite <- EL in Hout.
assert (A1 : a < ATOP /\ (a + 1 <= 192304 + -164 \/ 192304 + -164 + 4 <= a) /\ (a < xa \/ xa + L <= a)).
{ destruct Hin as [X|[X|[X|[X|(q & rq & Hq & Xa)]]]];
[unfold RMLOCK in *; lia| unfold RLIBC in *; lia| unfold RGOT_SSP in *; lia| unfold RSSP_GUARD in *; lia|].
destruct (WR4 q rq Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). pose proof (lr_lo_ge rq).
split; [lia|]. split; [lia|].
destruct (N.eq_dec q rid) as [->|NE]; [rewrite RR3 in Hq; inversion Hq; subst; cbn [lr_lo r_kind r_base r_len] in Xa; lia|].
destruct (DJ4 q rq rid _ Hq RR3 NE) as [D2|D2]; cbn [r_base r_len lr_lo r_kind] in D2; rewrite <- ?EL in D2; lia. }
atop_facts.
apply MU6; rewrite wa_unsigned by lia; cbn; lia. }
assert (HFPF : forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a).
{ intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; exact X| right; right; left; exact X|].
right; right; right. exists q, rq. split; [|split; [exact Kq|exact Xa]].
unfold stF. rewrite rdr_lookup_old; [exact Hq|]. intros ->. rewrite RR3 in Hq. inversion Hq; subst. apply Kq. reflexivity. }
assert (PE16 : rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m6).
{ eapply rpres_except_trans. { apply (PE14 stF); [unfold stF, drop_region; cbn [s_reserved set_shadow set_regions]; rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| exact HFPF]. }
eapply rpres_except_of_munch_nw; [exact MU6|]. intros a Ha NC. cbn.
split; [|split; [|split; [|exact I]]]; intros X; apply NC; [left; left; lia| left; right; left; rewrite unsigned_lit by lia; lia|].
do 4 right. split; [atop_facts; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
exists m6, (MM_syscalls.rg_errno ans2 errv4). do 14 eexists. split; [reflexivity|].
split; [exact MRF|]. split; [apply rticks_ok_drop_region; exact TK4|]. split; [exact MI6|]. split; [exact ST7|].
split; [unfold RATP; rewrite unsigned_lit by lia; exact ERR6|].
split. { eapply (rauxv_ok_malloc_fp st stF lo (bv_unsigned sp) m0 m6 m1 m6); [exact MR0| exact MRF| exact AUX1| exact PE16| atop_facts; lia| lia]. }
assert (MRELF : mrel st stF).
{ split.
- intros q rq Hq.
assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
{ transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2, rnr_lookup_old by exact NE. exact Hq. }
destruct (amr_regions _ _ _ REL q rq Hq2) as (r' & Hr' & K' & B' & L' & _).
exists r'. split; [|repeat split; auto]. unfold stF. rewrite rdr_lookup_old by exact NE. exact Hr'.
- unfold stF, drop_region. cbn [s_next_rid set_shadow set_regions]. pose proof (amr_next_rid _ _ _ REL) as NX.
change (s_next_rid (step_seq st2)) with (s_next_rid (step_seq st2)) in NX.
assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
- unfold stF, drop_region. cbn [s_reserved set_shadow set_regions]. rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
split. { eapply rpres_except_trans; [| exact PE16]. eapply rpres_except_mono; [exact PE1|]. intros a Ha.
eapply rmalloc_fp_mono; [apply (mrel_regions _ _ MRELF)| exact Ha]. }
split; [exact MRELF|].
split.
{ eapply (brk_link_ps_ext st3); [reflexivity| | exact BL3]. intros rb ob Hb. unfold stF. apply rdr_conc. cbn.
destruct PT3 as (_ & _ & _ & _ & _ & _ & P7 & _). rewrite Hb in P7. exact P7. }
repeat split; assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End BIG.
End CANSEC1.
