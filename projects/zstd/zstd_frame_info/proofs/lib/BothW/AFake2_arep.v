(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac InitMem ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg RtCells AProto ABase ABytes AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepExt
     FsKit AFake_iface F_tlsga F_m2s_b AFake_arep AFake_sm2 AFake2_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma c8s_of_dc : forall k m A, dc_at m A (8 * Z.of_nat k) -> exists shs : list word, length shs = k /\ rw_cells bsegs m A (map C8 shs).
Proof.
  induction k as [|k IH]; intros m A D.
  - exists []. split; [reflexivity|]. destruct D as [bs [[[WF _] [B0 [B1 _]]] [W0 [W1 _]]]].
    cbn [cells_size csize Nat.add cells_bytes cbytes] in *.
    Local Ltac2 Set LiaHints.tbl := fun () => "0090>10307011241.1324931651130.9 40669963262.9 41283725690.1141977111588.6 60460143174.1363374425370.6 65924634178.118848319345.6  00000300:00>00E00F00I00J00Q00RS1LS2B02W1S2W1S2W12HiSS1LSS2W12HiS".
split; [split; [exact I|] | split; [lia| split; [cbn; lia| intros i Hi; cbn in Hi; lia]]].
    split; [lia| split; [cbn; lia| intros i Hi; cbn in Hi; lia]].
  - rewrite Nat2Z.inj_succ in D. replace (8 * Z.succ (Z.of_nat k)) with (8 + 8 * Z.of_nat k) in D by lia.
    destruct (dc_split m A 8 (8 * Z.of_nat k) D ltac:(lia) ltac:(lia)) as [D8 Dk].
    destruct (c8_of_dc m A D8) as [w H8]. destruct (IH m (A + 8) Dk) as (shs & L & Hk).
    exists (w :: shs). split; [cbn; lia|].
    change (map C8 (w :: shs)) with ([C8 w] ++ map C8 shs). apply (proj2 (rw_cells_app bsegs m A [C8 w] (map C8 shs))).
    split; [exact H8|]. cbn [cells_size csize Nat.add]. replace (A + Z.of_nat 8) with (A + 8) by lia. exact Hk.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition afake_untouched_sh (L : alayout) (W : list (Z * Z)) : Prop :=
  Forall (fun iv => (snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
                 /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
                 /\ (snd iv <= 0x9add0 \/ 0x9add0 + 8 <= fst iv)
                 /\ (snd iv <= 0x5d3fc8 \/ 0x5d3fc8 + 16 <= fst iv)
                 /\ (snd iv <= 0x5d3fd8 \/ 0x5d3fd8 + 8 <= fst iv)
                 /\ (snd iv <= 0x5d3ff8 \/ 0x5d3ff8 + 8 <= fst iv)
                 /\ (snd iv <= 0x132bf1 \/ 0x132bf1 + 1 <= fst iv)
                 /\ (snd iv <= 0x130ad8 \/ 0x130ad8 + 4 <= fst iv)) W.

#[using="Type"] Lemma afake_frame_sh : forall L LB m m' W,
  AFAKE L LB m -> munch W m m' -> wmono bsegs m m' -> afake_untouched_sh L W -> AFAKE L LB m'.
Proof.
  intros L LB m m' W (G & CE & (h0 & h1 & h2 & hs & HS) & LOG & NGC & DC1 & DC2 & FL & LV) MU WM UT.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11). unfold FAKESZ in *.
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold AIMG_HI in GL1. destruct G5 as (G5s & G5i & G5). destruct G7 as (G7s & G7i & G7). unfold iclr, sclr, AIMG_LO, AIMG_HI, KLS in G5s, G5i, G7s, G7i.
  assert (DF : disjoint_from W (al_fake L) 11571200) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X1).
  assert (DD : disjoint_from W (al_dtls L) 4096) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X3).
  assert (D1 : disjoint_from W 0x9add0 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X4).
  assert (D2 : disjoint_from W 0x5d3fc8 16) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X5).
  assert (D3 : disjoint_from W 0x5d3fd8 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X6).
  assert (D4 : disjoint_from W 0x5d3ff8 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X7).
  assert (D5 : disjoint_from W 0x132bf1 1) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X8).
  assert (D6 : disjoint_from W 0x130ad8 4) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X9).
  split; [exact G|].
  split.
  { destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8). unfold afake_cells.
    Local Ltac2 Set LiaHints.tbl := fun () => "00C0>10317641044.5015502292006.5716593502911.5019346787540.4924540717768.5824540717768.6124922218561.5729782367974.5033667104152.5033667104152.5736041970854.504255436838.50 45485620289.504835283270.2  50203890247.5050861283456.5850861283456.6163541249473.5068061171235.5000000100200700R00`00n00o01001101201301401501:01;01>01A01B01CSSS3GL1S2G13G5s3G7s2G93G103G113GL1S3GL13GL31H2H0S3GL13GL31H2H0SSSSSSSS3G7iSS1HS1HSS".
repeat lazymatch goal with |- _ /\ _ => split end;
      try (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [cells_size csize Nat.add]; first [assumption | eapply disjoint_from_sub; [exact DD| lia| lia| lia]]]).
    eapply dc_at_any2; [exact C8| exact WM| clear -G7i; lia]. }
  split.
  { exists h0, h1, h2, hs. eapply rw_cells_transport; [exact HS| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]. }
  split; [eapply rw_cells_transport; [exact LOG| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
  split; [eapply rw_cells_transport; [exact NGC| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
  split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
  split.
  { eapply dc_at_any; [exact DC2| exact WM|]. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  split.
  - intros c pos b Hc Hp Hb NZ. pose proof (fk_flag_range L c pos Hc Hp).
    rewrite (munch_outside_range W m m' (al_fake L) 11571200) in Hb by (assumption || lia). eauto.
  - intros c F n Hin. destruct (LV c F n Hin) as (Hc & Hn & pos & Hp & HF & Hb). split; [exact Hc|]. split; [exact Hn|].
    exists pos. split; [exact Hp|]. split; [exact HF|]. pose proof (fk_flag_range L c pos Hc Hp).
    rewrite (munch_outside_range W m m' (al_fake L) 11571200) by (assumption || lia). exact Hb.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AHQ := (AH DI AQ ASEC).
Hypothesis HL : ahole_laws AHQ.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.

Notation FB2 F := (mkABlock (ABFake 2) F 256).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sm2_postP (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AHQ L RNG st (FB2 F :: LB) m'
    /\ F mod 256 = 0 /\ ablk F (F + 256) /\ F + 256 <= ATOP
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 224 junk; C8 (Z_to_bv 64 (fflag L 2 F))]
    /\ rw_cells bsegs m' (shad F) (repeat (C8 (Z_to_bv 64 0)) 4)
    /\ rng RNG F 256 /\ rng RNG (shad F) 32.

(* [comment removed for export] *)
#[using="HL"] Lemma arep_ext_sm2 : forall L st X m m' sp fs flag F,
  alayout_ok L -> AREP AHQ L st X m ->
  munch [(sp - 208, sp); (fs + 16, fs + 24); (flag, flag + 1); (F + 24, F + 32); (F + 248, F + 256); (2147450880 + F / 8, 2147450880 + F / 8 + 32)] m m' ->
  wmono bsegs m m' ->
  fs = al_fake L -> ATOP <= sp - 208 -> fs + 4096 <= flag < fs + 36864 -> fs + 36864 <= F -> F + 256 <= fs + 11571200 ->
  shad fs <= 2147450880 + F / 8 -> 2147450880 + F / 8 + 32 <= shad fs + 1446400 ->
  AREP AHQ L st X m'.
Proof.
  intros L st X m m' sp fs flag F ALO AR MU WM E S1 S2 S3 S4 S5 S6.
  assert (SHL : shlen 11571200 = 1446400) by reflexivity.
  eapply (AREP_frame_ext' DI AQ ASEC HL L st X m m' _ ALO AR MU WM). rewrite <- E, SHL. atop_facts.
  repeat (constructor; [cbn [fst snd]; intros _ |]); [right; right; lia| left; lia| left; lia| left; lia| left; lia| right; left; lia| constructor].
Qed.

#[using="HL CI_OK"] Theorem stack_malloc_2_P : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AHQ L RNG st LB m ->
  (forall F n, ~ In (mkABlock (ABFake 2) F n) LB) ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM2_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF bsegs RNG (sm2_postP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC2) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros AHP NOFK MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).
  (* [comment removed for export] *)
  destruct (AREP_cells DI AQ ASEC L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).
  (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "01j0?10092530843.1861043627856.181 1126798092.181 11482393301.20712983820844.8  13859192917.20715298870626.15515536006710.10 1633805619.205 16601926841.2071713438335.10  1715765315.12  17210499164.13817991072190.18118426717457.26 18426717457.29 18641914340.14018928859804.13818933043916.4  20178006101.20720861619413.20721838057999.28 2187326456.225 2189216216.217 2189423342.215 2189423596.154 2191522405.207 22323378911.13222369263914.15323700201109.18124125044652.21 24666123050.15424748059780.1812497545384.131 25156262947.21126087858018.20526265587414.20526265695972.5  2701854589.131 27038025706.20729147256744.21129299450114.15329784497005.18029786479080.14329786644200.14431113308501.15033085935132.24 33086189277.19 33092481056.21 33490756850.17833977372108.5  34304069349.21 34304097934.26 34304097934.28 34304097934.29 34977465718.13335097887758.26 35097887758.29 35236121829.15435440871153.18135696023445.18135890470211.9  41170069461.20741418135916.14241889427502.15241907258637.9  41996978269.18143603868184.18744017226280.16044797435322.16047348482913.1534835283238.2   49927382112.20551064760517.20752101696360.19 52101737131.21152101950377.24 52107990421.21 52469690798.15452564951269.18 52564951269.23 52853427574.15053884004779.28 54965598324.18155355428199.18755448986806.21455448989219.21555448989473.15455449179413.21755451086645.22555463667368.20755873094590.17755878677456.10 55878874588.16 56170253997.18156280132106.13256759370246.21 56765398074.24 56765644088.21156765668603.19 56953681963.20557980378352.18758037925428.16058229716486.13359754268945.20761161636889.15261161650461.20563238912958.15263370230317.15563370230318.15363623655639.13364262607882.21 65645947670.17666754262900.13967013716777.15567069419815.6  67150245700.18167316470978.4  67419257744.1876753474698.150 7106240049.4   9058454530.133 00000^00k00l01n02903;03S03a04T04a05805I05N05[05l06=06B06G06H07J08L08f08o09809A09F09O09T09l09m0:10:60:?0:D0:o0;a0<L0<T0<Y0<n0=:0=R0=[0=`0=e0>B0>Y0?00?C0?L0?T0@60@e0AT0BC0BH0Bb0C<0CT0CU0C^0Cf0Dh0Dm0E20E:0E;0EG0EL0EU0Em0F20Fe0Gg0H@0HX0IA0I]0J50J]0KS0Kk0L<0LI0LU0La0Lm0M50MA0MM0MY0ND0NN0Ne0O20O70O;0O?0OK0OO0P:0PF0Pb0Pg0QR0Qj0RU0Rm0S20S70S<0S\0TG0TL0Td0U00U<0U=0UI0UN0UO0UTS3GL13GL23G5l3G7l2PB3EFF3LSH4HPOS5HFLAG3HFF2WFS3GL23CL23LSHFS3BOT2LO3GL13GL23G5l3G7l3ATR2PB3EFF3SHF3SHS3SB13LSH4HPOS5HFLAG3HFFS2G32PB3HFFS3BOT2LO3GL13GL23G5l3G7l3ATR2PB3EFF3SHF3SHS3SB13LSH4HPOS5HFLAG3HFFS3GL13GL23G5l3G7l2PB3EFFS2G12G33ATR2PBS3GL13GL23G5l3G7l2PB3EFF3SHF3SB13LSH4HPOS5HFLAG3HFFS3GL13GL23LSHS2G32PB3HFF2X11H3GL12HrS3ATR2Hr2Y12Y22Y4S3GL2S3BOT3GL23LSHS3GL13GL33ATR3FRGS3GL13GL33ATR3FRGS3GL2S3GL2SS3BOT2LO3GL13GL23G5l3G7l3ATR2PB3EFF3SHF3SHS3SB13LSH4HPOS5HFLAG3HFFS3BOT2LO3GL13GL23G5l3G7l3ATR2PB3EFF3SHF3SHS3SB13LSH4HPOS5HFLAG3HFFS2G13GL13GL22PB3SHF3HFF2NES3GL23LSHS3GL23LSHS3GL23LSHS3GL2S3GL23LSHS3GL2S3GL13GL23G5l3G7l2PB3EFFFS2HaS3GL2S3GL23LSHS3GL2S3GL13GL23G5l3G7l2PB3EFF3LSH4HPOS5HFLAG3HFFS3BOT2LO3GL13GL23G5l3G7l2PB3EFF3LSH4HPOS5HFLAG3HFFS3GL13GL23G5l3G7l2PB3EFF3LSH4HPOS5HFLAG3HFFS2PB3HFFS3GL2S3GL23G5l3G7l3SHS3LSHS3GL23LSH2N3S3GL13GL23G5l3G7l2PB3EFFS3GL23LSHS3GL2S3GL2S3GL13GL23G5l3G7l3EFF3SB13SB2S2PB5HFLAG3HFF2Hr2Y32Y4S3BOT2LO2G32PB5HFLAG2HsS3GL12PB5HFLAG2Hr1HS3GL23LSHS2PB3HFFS3BOT2LO3ATR3A'R2PB3HFF3G2b2NA3F64S3BOT2LO3GL33FRG2PB3HFF2G13GL23SHF3SHD5HFLAG2NES3BOT2LO3GL33FRG2PB3HFF2G13GL23SHF3SHD5HFLAG2NES3BOT2LO3GL33FRG2PB3HFF2G13GL23SHF3SHD5HFLAG2NES3GL2S2G13GL13GL22PB3SHF3HFF2NES2G13GL13GL22PB3SHF3HFF2NES3GL13GL23G5l3G7l2PB3EFFFS3GL23LSHS2PB3HFFS3BOT2LO3GL13GL23G5l3G7l3ATR2PB3EFF3SHF3SHS3SB13LSH4HPOS5HFLAG3HFFS3GL2S3GL2S2PB3G2cFS3GL23LSH2LJS3GL2S3GL23SB2S3GL13GL23G5l3G7l2PB3EFFS3G7IS3GL13GL23G5l3G7l2PB3EFF3SHF3SB13LSH4HPOS5HFLAG3HFFS3BOT2LO3GL13GL23G5l3G7l3ATR2PB3EFF3SHF3SHS3SB13LSH4HPOS5HFLAG3HFFS2Hs3BOT2LO2G32PB3HFF3ATRS3GL23LSH2N12N22N42N52N6S3BOT2LO2Hr2Y22PB3HFF2Y32Y42G33GL13ATR2Y1S3BOT2LO3ATR2Hr1H3GL12PB3HFFS3GL13GL23G5l3G7l2PB3EFFS3BOT2LO2G33GL13ATR2PB3SHF3SHD5HFLAG3HFFS3BOT2LO2G32G62G93GL13G5s3ATR2PB3SHF3SB33SHD5HFLAG3HFFS3GL13GL23G5l3G7l2PB3EFFS3GL13GL33ATR3FRGS3GL23G7l3LSHS3GL23LSH2LJS3GL22PB3LSHS3GL22PB3LSHS3GL22PBS3GL22PB3LSHS3GL22PB3LSHS3GL22PB3LSHS3GL13GL23G5l3G7l2PB3EFF3LSH4HPOS5HFLAG3HFFS2X12X42DJS2G13GL12PB3HFF2Q32Q41DS3SPT3GL23LSHS3GL2S2HaS2HaS3GL23LSH2HaS2HaS3GL13GL23G5l3G7l2PB3EFF3LSH4HPOS5HFLAG3HFFS3GL23LSH2LJS3GL13GL23G5l3G7l2PB3EFF3SB1S3GL2S3GL13GL23G5l3G7l2PB3EFF3LSH4HPOS5HFLAG3HFFS3GL13GL23G5l3G7l2PB3EFFS3GL13GL23G5l3G7l2PB3EFF3LSH4HPOS5HFLAG3HFFS3GL13GL23G5l3G7l2PB3EFFS3GL2S3GL2S3GL2S2PB5HFLAG3HFF3F642Ha3A'R2NA3G2bS3GL13GL23G5l3G7l2PB3EFF3LSH4HPOS5HFLAG3HFFS3GL2S3GL13GL23G5l3G7l2PB3EFFS2PB3SB13SB2S2LO3GL23LSHSS3GL23LSH2LJS3GL2SS3GL2".
pose proof (relro_word m 0x99060 0x130ad8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0x99d28 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells bsegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app bsegs m 0x99d18 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM2_STACK in *.
  (* [comment removed for export] *)
  set (h := bv_unsigned h2). set (pos := Z.land h 4095). set (flag := (al_fake L) + 28672 + pos). set (F := (al_fake L) + 2134016 + pos * 256).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (PB : 0 <= pos < 4096).
  { subst pos. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL : flag = fk_flag L 2 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 2 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 2 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 266752 + 32 * pos = shad F /\ shad F + 32 <= shad (al_fake L) + 1446400 /\ shad F + 32 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 32 <= al_fake L \/ al_fake L + 11571200 <= shad F).   (* [comment removed for export] *)
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
  destruct (c1_of_dc m flag D3) as [fb FL0].
  assert (fb = Z_to_bv 8 0) as ->.
  { destruct (decide (fb = Z_to_bv 8 0)) as [E|NE]; [exact E| exfalso].
    apply (NOFK (fk_frame L 2 pos) (fk_fsize 2)). apply (FL 2 pos fb); [unfold FK_NCLS; lia| unfold fk_nframes; cbn; lia| | exact NE].
    rewrite <- EFL. apply (rw_C1_high m flag fb FL0). subst flag. lia. }
  (* [comment removed for export] *)
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 216 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 248) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].
  (* [comment removed for export] *)
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 32 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  destruct (c8s_of_dc 4 m (shad F) ltac:(exact DS2)) as (shs & LSH & SH0).
  (* [comment removed for export] *)
  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').
  (* [comment removed for export] *)
  assert (HNT' : rw_cells bsegs m (al_fake L) [C8 h0; C8 h1; C8 (Z_to_bv 64 h); CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).
  (* [comment removed for export] *)
  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (HPOS : pos = Z.land h 4095) by reflexivity. assert (HFLAG : flag = (al_fake L) + 28672 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 2134016 + pos * 256) by reflexivity.
  clearbody h pos flag F.
  eapply evtF_mono.
  { eapply (stack_malloc2_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x5d3fd0 (al_fake L) h pos flag F j24 j56 h0 h1 hs shs);
      try exact MI; try exact ST; try exact TP; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FL1 & F24' & F56' & SH').
  unfold sm2_W in MU. rewrite SHF in MU.
  (* [comment removed for export] *)
  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) + 16 <= a < (al_fake L) + 24) -> a <> flag ->
            ~ (F + 24 <= a < F + 32) -> ~ (F + 248 <= a < F + 256) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 32) ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
  assert (F64 : F mod 256 = 0).
  { rewrite HFF. clear - G1. apply Z.mod_divide in G1; [|lia]. destruct G1 as [k Hk]. rewrite Hk. apply Z.mod_divide; [lia|]. exists (16 * k + 8336 + pos). lia. }
  (* [comment removed for export] *)
  Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
  Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].
  assert (AR' : AREP AHQ L st X m').
  { eapply (arep_ext_sm2 L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
  assert (NOTIN : ~ In (FB2 F) LB) by (apply NOFK).
  assert (HFK' : AFAKE L (FB2 F :: LB) m').
  { split; [exact G|]. split.
    { unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
      split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
    split; [exists h0, h1, (Z_to_bv 64 (h + 1)), hs; exact HNT2|].
    split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGC MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
    split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
    split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
    split.
    - intros c pos' b Hc Hp Hb NZ.
      destruct (Z.eq_dec c 2) as [->|NC]; [destruct (Z.eq_dec pos' pos) as [->|NP]|].
      + left. rewrite <- EFR. unfold fk_fsize. reflexivity.
      + right. pose proof (fk_flags_disjoint L 2 pos' 2 pos Hc Hp Hc ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L 2 pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
      + right. pose proof (fk_flags_disjoint L c pos' 2 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L c pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
    - intros c F' n' [E|Hin].
      + injection E as <- <- <-. split; [unfold FK_NCLS; lia|]. split; [reflexivity|].
        exists pos. split; [unfold fk_nframes; cbn; lia|]. split; [exact EFR|].
        rewrite <- EFL. apply (rw_C1_high m' flag _ FL1). lia.
      + destruct (LV c F' n' Hin) as (Hc & Hn & pos' & Hp & HF' & B1).
        split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp|]. split; [exact HF'|].
        assert (NE : fk_flag L c pos' <> flag).
        { rewrite EFL. apply (fk_flags_disjoint L c pos' 2 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia)).
          intros E. injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn in Hin. replace (fk_fsize 2) with 256 in Hin by reflexivity. exact Hin. }
        pose proof (fk_flag_range L c pos' Hc Hp) as FRG. rewrite OUT by (first [clear -FRG NE G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). exact B1. }
  (* [comment removed for export] *)
  assert (BL' : ablocks L st X (FB2 F :: LB)).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
    - intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - cbn. exact B3.
    - constructor; [exact NOTIN| exact B4]. }
  assert (AHP' : AHEAP_P AHQ L RNG st (FB2 F :: LB) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AH ah_fake]. exact HFK'. }
  (* [comment removed for export] *)
  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 256 <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE DI AQ ASEC L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (2, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in Hb.
        replace (fk_fsize 2) with 256 in Hb by reflexivity. exact Hb. }
      pose proof (fk_frames_disjoint L c' pos' 2 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 2) with 256 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 256)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0
        D3 D24 D56 DS2 RR A10.
  assert (HPR : aheap_pres CI LB (bv_unsigned sp) m m').
  { intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
    destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; clear - Ha Hs SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - pose proof (CI_OK iv Hiv). apply OUT; clear - Ha H Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1. apply OUT; clear - Ha Y1 Y2 Y3 Y4 Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SHA in Ha |- *.
      pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.
      apply OUT; clear - Ha A'R NA F64 G2b G3 HFF HFLAG PB LO SK3 BOT ATR; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  (* [comment removed for export] *)
  pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
  pose proof (dc_at_any m m' (F + 32) 216 DJ1 WM ltac:(lia)) as DJ1'.
  destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
  destruct DJ1' as [junk1 J1]. change (Z.to_nat 216) with 216%nat in J1.
  assert (LJ : length junk1 = 216%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 224 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 2 F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app bsegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 224 (le8 sp ++ junk1)] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
      eapply rw_cells_recast; [apply (proj2 (rw_cells_app bsegs m' (F + 24) [C8 sp] [CB 216 junk1])); split; [exact F24'|];
        cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
      + reflexivity.
    - cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 224) with (F + 248) by lia. exact F56'. }
  (* [comment removed for export] *)
  unfold sm2_postP. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Inst.
  Variable DI : ADepotIface.
  Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
  Hypothesis HL : ahole_laws (AH DI AQ ASEC).
  Variable CI : list (Z * Z).
  Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
  Variable AI : AMallocIface.
  Hypothesis E : AHEAP AI = AHEAP_P (AH DI AQ ASEC).
  Hypothesis EC : aci AI = CI.

  #[using="DI AQ ASEC HL CI CI_OK E EC"] Lemma stack_malloc_2_AI : stack_malloc_2_stmt AI fflag afake_rng.
  Proof.
    unfold stack_malloc_2_stmt. intros until lo. intros AHx NOFK MI ST BOT LO SPT TP RSTK RI RFS.
    rewrite E in AHx. unfold ASM2_ENTRY. change 0x3c8b8 with ASTKMALLOC2.
    eapply evtF_mono; [eapply (stack_malloc_2_P DI AQ ASEC HL CI CI_OK); eassumption|].
    cbv beta. intros ms' PO. unfold sm2_postP in PO. unfold sm2_post.
    destruct PO as (F & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & j0 & j1 & j2 & junk & EQ & MI' & ST' & HPR & AH' & REST).
    exists F, x0, x1, x2, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, m', j0, j1, j2, junk.
    rewrite E, EC. repeat (split; [assumption|]). exact REST.
  Qed.

End Inst.
End CANSEC1.
