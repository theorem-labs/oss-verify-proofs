(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac InitMem ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg RtCells AProto ABase ABytes AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepExt
FsKit AFake_iface F_tlsga F_m2s_b AFake_arep AFake_sm5 AFake_sf5 AFake5_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
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
#[using="Type"] Lemma hint5_split : forall m A (h0 h1 h2 : word) hs,
rw_cells bsegs m A [C8 h0; C8 h1; C8 h2; CB 64 hs] ->
exists hsa (hw : word) hsb, length hsa = 16%nat /\ length hsb = 40%nat
/\ rw_cells bsegs m A [C8 h0; C8 h1; C8 h2; CB 16 hsa; C8 hw; CB 40 hsb].
Proof.
intros m A h0 h1 h2 hs H.
pose proof (rw_cells_split_CB bsegs m A [C8 h0; C8 h1; C8 h2] 64 hs [] [16; 8; 40]%nat H ltac:(reflexivity)) as H2.
cbn [app mk_CB_cells] in H2. try rewrite app_nil_r in H2.
set (hsa := firstn 16 hs) in H2. set (hb := firstn 8 (skipn 16 hs)) in H2. set (hsb := firstn 40 (skipn 8 (skipn 16 hs))) in H2.
assert (LH : length hs = 64%nat) by (destruct H as [[WF _] _]; cbn in WF; tauto).
apply (proj1 (rw_cells_app bsegs m A [C8 h0; C8 h1; C8 h2; CB 16 hsa] [CB 8 hb; CB 40 hsb])) in H2. destruct H2 as [P1 P2].
cbn [cells_size csize Nat.add] in P2.
apply (proj1 (rw_cells_app bsegs m (A + Z.of_nat 40) [CB 8 hb] [CB 40 hsb])) in P2. destruct P2 as [P2 P3].
destruct (c8_of_CB m _ hb P2) as (hw & HW & _).
exists hsa, hw, hsb. Local Ltac2 Set LiaHints.tbl := fun () => "0020>30991657758.16512739997.16  000004008S2LHS2LH".
split; [subst hsa; rewrite firstn_length; lia|]. split; [subst hsb; rewrite firstn_length, !skipn_length; lia|].
change [C8 h0; C8 h1; C8 h2; CB 16 hsa; C8 hw; CB 40 hsb] with ([C8 h0; C8 h1; C8 h2; CB 16 hsa] ++ [C8 hw; CB 40 hsb]).
apply (proj2 (rw_cells_app bsegs m A _ _)). split; [exact P1|]. cbn [cells_size csize Nat.add].
change [C8 hw; CB 40 hsb] with ([C8 hw] ++ [CB 40 hsb]). apply (proj2 (rw_cells_app bsegs m _ _ _)). split; [exact HW|].
cbn [cells_size csize Nat.add] in P3 |- *. exact P3.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma hint5_merge : forall m A (h0 h1 h2 hw : word) hsa hsb,
rw_cells bsegs m A [C8 h0; C8 h1; C8 h2; CB 16 hsa; C8 hw; CB 40 hsb] ->
exists hs, rw_cells bsegs m A [C8 h0; C8 h1; C8 h2; CB 64 hs].
Proof.
intros m A h0 h1 h2 hw hsa hsb H.
pose proof (rw_cells_merge bsegs m A [C8 h0; C8 h1; C8 h2] [CB 16 hsa; C8 hw; CB 40 hsb] [] ltac:(rewrite app_nil_r; exact H)) as M.
cbn [cells_size csize Nat.add] in M. try rewrite app_nil_r in M. eexists. exact M.
Qed.
Definition afake_untouched_sh (L : alayout) (W : list (Z * Z)) : Prop :=
Forall (fun iv => (snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
/\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
/\ (snd iv <= 0x9b6b0 \/ 0x9b6b0 + 8 <= fst iv)
/\ (snd iv <= 0x5d54c8 \/ 0x5d54c8 + 16 <= fst iv)
/\ (snd iv <= 0x5d54d8 \/ 0x5d54d8 + 8 <= fst iv)
/\ (snd iv <= 0x5d54f8 \/ 0x5d54f8 + 8 <= fst iv)
/\ (snd iv <= 0x1340f1 \/ 0x1340f1 + 1 <= fst iv)
/\ (snd iv <= 0x131fd8 \/ 0x131fd8 + 4 <= fst iv)) W.
#[using="Type"] Lemma afake_frame_sh : forall L LB m m' W,
AFAKE L LB m -> munch W m m' -> wmono bsegs m m' -> afake_untouched_sh L W -> AFAKE L LB m'.
Proof.
intros L LB m m' W (G & CE & (h0 & h1 & h2 & hs & HS) & LOG & NGC & DC1 & DC2 & FL & LV) MU WM UT.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11). unfold FAKESZ in *.
pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold AIMG_HI in GL1. destruct G5 as (G5s & G5i & G5). destruct G7 as (G7s & G7i & G7). unfold iclr, sclr, AIMG_LO, AIMG_HI, KLS in G5s, G5i, G7s, G7i.
assert (DF : disjoint_from W (al_fake L) 11571200) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X1).
assert (DD : disjoint_from W (al_dtls L) 4096) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X3).
assert (D1 : disjoint_from W 0x9b6b0 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X4).
assert (D2 : disjoint_from W 0x5d54c8 16) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X5).
assert (D3 : disjoint_from W 0x5d54d8 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X6).
assert (D4 : disjoint_from W 0x5d54f8 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X7).
assert (D5 : disjoint_from W 0x1340f1 1) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X8).
assert (D6 : disjoint_from W 0x131fd8 4) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X9).
split; [exact G|].
split.
{ destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8). unfold afake_cells.
Local Ltac2 Set LiaHints.tbl := fun () => "00C0>10317641044.5015502292006.5716593502911.5022301225132.7124540717768.5824540717768.6124922218561.5729782367974.5033667104152.5033667104152.5736041970854.504255436838.50 45485620289.504835283270.2  50203890247.5050861283456.5850861283456.6163541249473.5068061171235.5000000100200700Z00h01601701801901:01;01<01=01B01C01F01I01J01KSSS3GL1S2G13G5s3G7s2G93G103G113GL11H2H02H9S3GL13GL31H2H0S3GL13GL31H2H0SSSSSSSS3G7iSS1HS1HSS".
repeat lazymatch goal with |- _ /\ _ => split end;
try (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [cells_size csize Nat.add]; first [assumption | eapply disjoint_from_sub; [exact DD| lia| lia| lia]]]).
eapply dc_at_any2; [exact C8| exact WM| clear -G7i; lia]. }
split.
{ exists h0, h1, h2, hs. eapply rw_cells_transport; [exact HS| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]. }
split; [eapply rw_cells_transport; [exact LOG| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
split; [eapply rw_cells_transport; [exact NGC| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
split.
{ eapply dc_at_any; [exact DC2| exact WM|]. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations; lia. }
split.
- intros c pos b Hc Hp Hb NZ. pose proof (fk_flag_range L c pos Hc Hp).
rewrite (munch_outside_range W m m' (al_fake L) 11571200) in Hb by (assumption || lia). eauto.
- intros c F n Hin. destruct (LV c F n Hin) as (Hc & Hn & pos & Hp & HF & Hb). split; [exact Hc|]. split; [exact Hn|].
exists pos. split; [exact Hp|]. split; [exact HF|]. pose proof (fk_flag_range L c pos Hc Hp).
rewrite (munch_outside_range W m m' (al_fake L) 11571200) by (assumption || lia). exact Hb.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AHQ := (AH DI AQ ASEC).
Hypothesis HL : ahole_laws AHQ.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Notation FB5 F := (mkABlock (ABFake 5) F 2048).
Definition sm5_postP (L : alayout) (RNG : footprint)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
(st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (ret_pc ra) fc None m' (seg_rom bsegs)
/\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
/\ aheap_pres CI LB (bv_unsigned sp) m m'
/\ AHEAP_P AHQ L RNG st (FB5 F :: LB) m'
/\ F mod 2048 = 0 /\ ablk F (F + 2048) /\ F + 2048 <= ATOP
/\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 2016 junk; C8 (Z_to_bv 64 (fflag L 5 F))]
/\ rw_cells bsegs m' (shad F) (repeat (C8 (Z_to_bv 64 0)) 32)
/\ rng RNG F 2048 /\ rng RNG (shad F) 256.
#[using="HL"] Lemma arep_ext_sm5 : forall L st X m m' sp fs flag F,
alayout_ok L -> AREP AHQ L st X m ->
munch [(sp - 208, sp); (fs + 40, fs + 48); (flag, flag + 1); (F + 24, F + 32); (F + 2040, F + 2048); (2147450880 + F / 8, 2147450880 + F / 8 + 256)] m m' ->
wmono bsegs m m' ->
fs = al_fake L -> ATOP <= sp - 208 -> fs + 4096 <= flag < fs + 36864 -> fs + 36864 <= F -> F + 2048 <= fs + 11571200 ->
shad fs <= 2147450880 + F / 8 -> 2147450880 + F / 8 + 256 <= shad fs + 1446400 ->
AREP AHQ L st X m'.
Proof.
intros L st X m m' sp fs flag F ALO AR MU WM E S1 S2 S3 S4 S5 S6.
assert (SHL : shlen 11571200 = 1446400) by reflexivity.
eapply (AREP_frame_ext' DI AQ ASEC HL L st X m m' _ ALO AR MU WM). rewrite <- E, SHL. atop_facts.
repeat (constructor; [cbn [fst snd]; intros _ |]); [right; right; lia| left; lia| left; lia| left; lia| left; lia| right; left; lia| constructor].
Qed.
#[using="HL CI_OK"] Theorem stack_malloc_5_P : forall (L : alayout) (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
AHEAP_P AHQ L RNG st LB m ->
(forall F n, ~ In (mkABlock (ABFake 5) F n) LB) ->
mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM5_STACK ->
bv_unsigned sp <= al_top L ->
tp = Z_to_bv 64 ATP ->
rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
evtF bsegs RNG (sm5_postP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (Z_to_bv 64 ASTKMALLOC5) fc None m (seg_rom bsegs)).
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
destruct (AREP_cells DI AQ ASEC L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).
Local Ltac2 Set LiaHints.tbl := fun () => "01k0?10092530843.1911043627856.187 1126798092.187 11956183549.13113553991877.21314712686997.35 16601926841.21317099880932.1461713438335.10  1715765315.12  17935620764.14417991072190.18718426717457.26 18426717457.29 18430963752.16618927930929.4  18933043916.4  22210832021.18722369263914.15924864398468.18725161562922.16026087858018.21127038025706.21328317142370.16129147256744.21729171688231.6  29299450114.15929315431900.14829784497005.18529786479080.14929786644200.15031113308501.15631786379743.28 33085935132.24 33086189277.19 33092481056.21 33473948707.21733490756850.18333977372108.5  34301889471.35 34303987250.42 34304097934.26 34304097934.28 34304097934.29 35097887758.26 35097887758.29 35136785731.9  35440871153.18735696023445.18736302732517.1603642531797.213 3769089931.31  38476996742.13341889427502.15841996978269.18742707878613.21345067941973.21345950707031.1334732340760.192 47348482913.15947817153293.9  4835283238.2   49927382112.21151860349196.14452087137493.21352101696360.19 52101737131.21752101950377.24 52107990421.21 52225734869.21352469690798.16052564951269.18 52564951269.23 52853427574.15653098899172.5  53099060950.21154965598324.18754969975723.28 55355428199.19255448986806.22055448989219.22155448989473.16055449179413.22355451086645.23155463667368.21355873094590.18255878677456.10 55878874588.16 56170253997.18756759370246.21 56765398074.24 56765644088.21756765668603.19 56953681963.21157437516332.8  57980378352.19258037925428.16659008193730.4  59308293368.23159310390508.16059310390766.22159310573272.22359320874341.21359754268945.21361161636889.15861161650461.21162853943946.13263238912958.15863370230317.16163370230318.15963788827578.16665645947670.18165907062579.21166006924073.16166754262900.14567113812098.13367150245700.18767419257744.1926753474698.156 67760285770.35 679825759.132  9380125992.131 9740828406.133 00000f01;01<01A02K03303H03U03l04=04J04_05005A05N05O05P05Q06106B06O07I07f08F08Z08f09F09S09d0:10:>0:c0;=0;T0;k0<>0=10=B0=J0=m0>C0?20?a0@P0@j0AD0AL0AM0A^0B>0CH0Cd0Ci0D60D70EA0FK0FP0Fd0GD0GL0GQ0HL0HY0Ic0J<0J\0KE0Ka0Lk0MK0N30Ni0OI0OQ0PD0PY0Pj0Q>0QR0Qf0R60RJ0R^0S20Se0So0TF0T[0T_0Tc0U70U;0Un0V90VM0W10W20WC0WP0Wa0X20XC0Y60YV0ZI0ZN0Zn0[;0[H0[Y0\L0]G0]g0^40^90^M0^a0^n0_20_70_<0_AS3GL13GL23G5l3G7l3LHA3LHB2PB3EFF3LSH4HPOS5HFLAG3HFF2WFS3GL23CL23LHA3LHB3LSHFS3GL2S3BOT2LO3GL13GL23G5l3G7l3ATR3LHA3LHB2PB3EFF3SHF3SHS3SB13LSH4HPOS5HFLAG3HFFS2PB5HFLAG3HFF3F642Ha3A'R2NA3G2b1H2H02H4S3GL13GL23LHA3LHB3LSHS3GL23LHA3LHBS2G32PB3HFF2X11H3GL12HrS3ATR2Hr2Y12Y22Y4S3GL23LHA3LHBS3BOT3GL23LHA3LHB3LSHS3GL13GL33ATR3FRGS3GL13GL33ATR3FRGS3GL23LHA3LHBSSFS3GL13GL23G5l3G7l3LHA3LHB2PB3EFFS3GL23LHA3LHB3LSHS3GL23LHA3LHBS3BOT2LO3GL13GL23G5l3G7l3LHA3LHB2PB3EFF3LSH4HPOS5HFLAG3HFFS3GL23G5l3G7l3LHA3LHB3SHS3LSHS3GL13GL23G5l3G7l3LHA3LHB2PB3EFFS3GL23LHA3LHB3LSH2N3S2PB3SB13SB2S3GL13GL23G5l3G7l3LHA3LHB2PB3EFFS3GL23LHA3LHBS3GL23LHA3LHB3LSHS3GL23LHA3LHBS3GL23LHA3LHBS3GL13GL23G5l3G7l3LHA3LHB3EFF3SB13SB2S2G13GL13GL22PB3SHF3HFF2NES2PB5HFLAG3HFF2Hr2Y32Y4S3BOT2LO2G32PB5HFLAG2HsS3GL12PB5HFLAG2Hr1HS3GL13GL23G5l3G7l3LHA3LHB2PB3EFF3LSH4HPOS5HFLAG3HFFS3GL23LHA3LHB3LSHS2PB3HFFS3BOT2LO3ATR3A'R1H2H02PB3HFF3G2b2NAS3F642NA1H2H02H42H52H9S3BOT2LO3GL33FRG2PB3HFF2G13GL23SHF3SHD5HFLAG2NES3BOT2LO3GL33FRG2PB3HFF2G13GL23SHF3SHD5HFLAG2NES3BOT2LO3GL33FRG2PB3HFF2G13GL23SHF3SHD5HFLAG2NES2G13GL13GL22PB3SHF3HFF2NES2G13GL13GL22PB3SHF3HFF2NES2PB3HFFFS3GL23LHA3LHB3LSHS3GL13GL23G5l3G7l3LHA3LHB2PB3EFFS3BOT2LO3GL13GL23G5l3G7l3ATR3LHA3LHB2PB3EFF3SHF3SHS3SB13LSH4HPOS5HFLAG3HFFS2G12G33ATR2PB1H2H02H42H52H9S3GL2S3GL23LHA3LHBFS3BOT2LO3GL13GL23G5l3G7l3ATR3LHA3LHB2PB3EFF3SHF3SHS3SB13LSH4HPOS5HFLAG3HFFS3BOT2LO3GL13GL23G5l3G7l3ATR3LHA3LHB2PB3EFF3SHF3SHS3SB13LSH4HPOS5HFLAG3HFFS3GL2S3GL23LHA3LHB3LSH2LJS3GL13GL23G5l3G7l3LHA3LHB2PB3EFFS2PB3G2cS3G7IS3GL13GL23G5l3G7l3LHA3LHB2PB3EFF3SHF3SB13LSH4HPOS5HFLAG3HFFS3GL23LHA3LHBS3BOT2LO3GL13GL23G5l3G7l3ATR3LHA3LHB2PB3EFF3SHF3SHS3SB13LSH4HPOS5HFLAG3HFFS2Hs3BOT2LO2G32PB3HFF3ATRS3GL23LHA3LHB3LSH2N12N22N42N52N6S3BOT2LO2Hr2Y22PB3HFF2Y32Y42G33GL13ATR2Y1S3BOT2LO3ATR2Hr1H3GL12PB3HFFS3BOT2LO3GL13GL23G5l3G7l3ATR3LHA3LHB2PB3EFF3SHF3SHS3SB13LSH4HPOS5HFLAG3HFFS3GL13GL23G5l3G7l3LHA3LHB2PB3EFFS3BOT2LO2G33GL13ATR2PB3SHF3SHD5HFLAG3HFFS3BOT2LO2G32G62G93GL13G5s3ATR2PB3SHF3SB33SHD5HFLAG3HFFS3GL13GL23G5l3G7l3LHA3LHB2PB3EFFS2PB3HFFS3GL13GL23G5l3G7l3LHA3LHB2PB3EFF3LSH4HPOS5HFLAG3HFFS3GL23G7l3LHA3LHB3LSHS3GL13GL33ATR3FRGS3GL23LHA3LHB3LSH2LJS3GL23LHA3LHB2PB3LSHS3GL23LHA3LHB2PB3LSHS3GL23LHA3LHB2PBS3GL23LHA3LHB2PB3LSHS3GL23LHA3LHB2PB3LSHS3GL23LHA3LHB2PB3LSHS3GL13GL23G5l3G7l3LHA3LHB2PB3EFF3LSH4HPOS5HFLAG3HFFS2X12X42DJS2G13GL12PB3HFF2Q32Q41DS3SPT3GL23LHA3LHB3LSHS2HaS2HaS3GL23LHA3LHB3LSH2HaS2HaS3GL13GL23G5l3G7l3LHA3LHB2PB3EFF3LSH4HPOS5HFLAG3HFFS2G32PB3HFFS3GL23LHA3LHB3LSH2LJS3GL13GL23G5l3G7l3LHA3LHB2PB3EFF3SB1SS3GL23LHA3LHB3LSHS3GL23LHA3LHBS3GL23LHA3LHB3LSHS3GL23LHA3LHB3LSHS3GL23LHA3LHB3LSHS3GL13GL23G5l3G7l3LHA3LHB2PB3EFF3LSH4HPOS5HFLAG3HFFS3GL13GL23G5l3G7l3LHA3LHB2PB3EFFS3GL13GL23G5l3G7l3LHA3LHB2PB3EFF3LSH4HPOS5HFLAG3HFFS3GL2S3GL13GL23G5l3G7l3LHA3LHB2PB3EFFS3GL23LHA3LHBS3GL23LHA3LHBS3GL23LHA3LHB3SB2S3GL13GL23G5l3G7l3LHA3LHB2PB3EFF3LSH4HPOS5HFLAG3HFFS3GL13GL23G5l3G7l3LHA3LHB2PB3EFF3SHF3SB13LSH4HPOS5HFLAG3HFFS3GL13GL23G5l3G7l3LHA3LHB2PB3EFFS3GL23LHA3LHBS3GL2S2LO3GL23LHA3LHB3LSHS3GL23LHA3LHB3LSH2LJS3GL23LHA3LHBS2HaS3GL2S3GL2S3GL2".
pose proof (relro_word m 0x99960 0x131fd8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
pose proof (relro_word m 0x9a608 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
assert (DESC : rw_cells bsegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
{ unfold AFSDESC. apply (proj2 (rw_cells_app bsegs m 0x9a5f8 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
unfold FAKESZ, KHIGH, AIMG_HI, SM5_STACK in *.
destruct (hint5_split m (al_fake L) h0 h1 h2 hs HNT) as (hsa & hw & hsb & LHA & LHB & HNT5).
set (h := bv_unsigned hw). set (pos := Z.land h 511). set (flag := (al_fake L) + 35840 + pos). set (F := (al_fake L) + 5279744 + pos * 2048).
assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
assert (PB : 0 <= pos < 512).
{ subst pos. change 511 with (Z.ones 9). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
assert (EFL : flag = fk_flag L 5 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
assert (EFR : F = fk_frame L 5 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
assert (EFF : fflag L 5 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
{ unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
destruct SHS as [SHS SHL]. rewrite SHL in *.
assert (SHB : shad (al_fake L) + 659968 + 256 * pos = shad F /\ shad F + 256 <= shad (al_fake L) + 1446400 /\ shad F + 256 <= 0x10007fff8000).
{ rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
destruct SHB as (SB1 & SB2 & SB3).
assert (SHD : shad F + 256 <= al_fake L \/ al_fake L + 11571200 <= shad F).
{ pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }
pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
destruct (c1_of_dc m flag D3) as [fb FL0].
assert (fb = Z_to_bv 8 0) as ->.
{ destruct (decide (fb = Z_to_bv 8 0)) as [E|NE]; [exact E| exfalso].
apply (NOFK (fk_frame L 5 pos) (fk_fsize 5)). apply (FL 5 pos fb); [unfold FK_NCLS; lia| unfold fk_nframes; cbn; lia| | exact NE].
rewrite <- EFL. apply (rw_C1_high m flag fb FL0). subst flag. lia. }
pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 2008 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 2040) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].
pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 256 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
destruct (c8s_of_dc 32 m (shad F) ltac:(exact DS2)) as (shs & LSH & SH0).
destruct (c8c8_of_dc m _ T48) as (tb & te & T48').
assert (HNT' : rw_cells bsegs m (al_fake L) [C8 h0; C8 h1; C8 h2; CB 16 hsa; C8 (Z_to_bv 64 h); CB 40 hsb]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT5).
pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
assert (HPOS : pos = Z.land h 511) by reflexivity. assert (HFLAG : flag = (al_fake L) + 35840 + pos) by reflexivity.
assert (HFF : F = (al_fake L) + 5279744 + pos * 2048) by reflexivity.
clearbody h pos flag F.
eapply evtF_mono.
{ eapply (stack_malloc5_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x5d54d0 (al_fake L) h pos flag F j24 j56 h0 h1 h2 hsa hsb shs);
try exact MI; try exact ST; try exact TP; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
all: try (eapply rng_sub'; [exact RSTK| lia]).
all: try (eapply rng_sub'; [exact A3| lia]). }
cbv beta. intros ms' PO.
destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FL1 & F24' & F56' & SH').
unfold sm5_W in MU. rewrite SHF in MU.
assert (OUT : forall a, 0 <= a < 2^64 ->
~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) + 40 <= a < (al_fake L) + 48) -> a <> flag ->
~ (F + 24 <= a < F + 32) -> ~ (F + 2040 <= a < F + 2048) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 256) ->
m' (wa a) = m (wa a)).
{ intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
assert (F64 : F mod 2048 = 0).
{ rewrite HFF. clear - G1. apply Z.mod_divide in G1; [|lia]. destruct G1 as [k Hk]. rewrite Hk. apply Z.mod_divide; [lia|]. exists (2 * k + 2578 + pos). lia. }
Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].
assert (AR' : AREP AHQ L st X m').
{ eapply (arep_ext_sm5 L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
assert (NOTIN : ~ In (FB5 F) LB) by (apply NOFK).
assert (HFK' : AFAKE L (FB5 F :: LB) m').
{ split; [exact G|]. split.
{ unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
split; [destruct (hint5_merge m' (al_fake L) h0 h1 h2 _ hsa hsb HNT2) as [hs' HS']; exists h0, h1, h2, hs'; exact HS'|].
split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGC MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
split.
- intros c pos' b Hc Hp Hb NZ.
destruct (Z.eq_dec c 5) as [->|NC]; [destruct (Z.eq_dec pos' pos) as [->|NP]|].
+ left. rewrite <- EFR. unfold fk_fsize. reflexivity.
+ right. pose proof (fk_flags_disjoint L 5 pos' 5 pos Hc Hp Hc ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
rewrite <- EFL in NE. pose proof (fk_flag_range L 5 pos' Hc Hp) as FRG.
rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
+ right. pose proof (fk_flags_disjoint L c pos' 5 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
rewrite <- EFL in NE. pose proof (fk_flag_range L c pos' Hc Hp) as FRG.
rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
- intros c F' n' [E|Hin].
+ injection E as <- <- <-. split; [unfold FK_NCLS; lia|]. split; [reflexivity|].
exists pos. split; [unfold fk_nframes; cbn; lia|]. split; [exact EFR|].
rewrite <- EFL. apply (rw_C1_high m' flag _ FL1). lia.
+ destruct (LV c F' n' Hin) as (Hc & Hn & pos' & Hp & HF' & B1).
split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp|]. split; [exact HF'|].
assert (NE : fk_flag L c pos' <> flag).
{ rewrite EFL. apply (fk_flags_disjoint L c pos' 5 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia)).
intros E. injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn in Hin. replace (fk_fsize 5) with 2048 in Hin by reflexivity. exact Hin. }
pose proof (fk_flag_range L c pos' Hc Hp) as FRG. rewrite OUT by (first [clear -FRG NE G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). exact B1. }
assert (BL' : ablocks L st X (FB5 F :: LB)).
{ destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
- intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
- intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
- cbn. exact B3.
- constructor; [exact NOTIN| exact B4]. }
assert (AHP' : AHEAP_P AHQ L RNG st (FB5 F :: LB) m').
{ split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AH ah_fake]. exact HFK'. }
assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
/\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
/\ (ab_addr b + ab_size b <= F \/ F + 2048 <= ab_addr b)).
{ intros b Hb. destruct b as [[p|c'] A' n']; cbn.
- pose proof (HB_FAKE DI AQ ASEC L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
- pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
assert (NEQ : (c', pos') <> (5, pos)).
{ intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in Hb.
replace (fk_fsize 5) with 2048 in Hb by reflexivity. exact Hb. }
pose proof (fk_frames_disjoint L c' pos' 5 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 5) with 2048 in DJ by reflexivity.
split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->
0 <= a' < 2^47 /\ ~ (F <= a' < F + 2048)).
{ intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
[ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' HNT5 LOG NGC DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0
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
apply OUT; clear - Ha A'R NA F64 G2b G3 HFF HFLAG PB LO SK3 BOT ATR; Z.div_mod_to_equations; lia. }
pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
pose proof (dc_at_any m m' (F + 32) 2008 DJ1 WM ltac:(lia)) as DJ1'.
destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
destruct DJ1' as [junk1 J1]. change (Z.to_nat 2008) with 2008%nat in J1.
assert (LJ : length junk1 = 2008%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
assert (FRM : rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 2016 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 5 F))]).
{ rewrite EFF.
apply (proj2 (rw_cells_app bsegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 2016 (le8 sp ++ junk1)] _)). split.
- replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
eapply rw_cells_recast; [apply (proj2 (rw_cells_app bsegs m' (F + 24) [C8 sp] [CB 2008 junk1])); split; [exact F24'|];
cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
+ cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
+ cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
+ reflexivity.
- cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 2016) with (F + 2040) by lia. exact F56'. }
unfold sm5_postP. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
split; [exact FRM|]. split; [exact SH'|].
split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition sf5_postP (L : alayout) (RNG : footprint)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
(st : astate) (LB : list ablock) (lo F : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (ret_pc ra) fc None m' (seg_rom bsegs)
/\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
/\ aheap_pres CI LB (bv_unsigned sp) m m'
/\ AHEAP_P AHQ L RNG st LB m'
/\ rw_cells bsegs m' (shad F) (repeat (C8 (Z_to_bv 64 0xf5f5f5f5f5f5f5f5)) 32).
#[using="HL CI_OK"] Theorem stack_free_5_P : forall (L : alayout) (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo F : Z) (sh : list byte),
AHEAP_P AHQ L RNG st (FB5 F :: LB) m ->
rw_cells bsegs m (F + 2040) [C8 (Z_to_bv 64 (fflag L 5 F))] ->
rw_cells bsegs m (shad F) [CB 256 sh] ->
F mod 2048 = 0 -> ablk F (F + 2048) -> F + 2048 <= ATOP ->
mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SF5_STACK ->
bv_unsigned sp <= al_top L ->
a0 = Z_to_bv 64 F ->
rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG -> rng RNG F 2048 -> rng RNG (shad F) 256 ->
evtF bsegs RNG (sf5_postP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo F m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (Z_to_bv 64 ASTKFREE5) fc None m (seg_rom bsegs)).
Proof.
intros until sh. intros AHP FP SH0 F64 FB FT MI ST BOT LO SPT A0 RSTK RIMG (RF & RSH & RD) RFR RFS.
pose proof atop_range as ATR. unfold SF5_STACK in LO.
destruct (fake_flag_P DI AQ ASEC CI CI_OK L RNG st (FB5 F :: LB) m 5 F 2048 AHP ltac:(left; reflexivity))
as (FLG & RFL & FLB & FLT & FLAP & FLCI).
set (flag := fflag L 5 F) in *.
pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
pose proof (afake_lb L _ m 5 F 2048 HFK ltac:(left; reflexivity)) as (Hc & Hn & Npos & F64' & FLO & FHI & FK & FC & pos & Hp & HF & EF & FR0).
pose proof HFK as (G & _). pose proof G as (G1 & G2 & G3 & _). pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold FAKESZ, AIMG_HI in *.
pose proof (FLAP (FB5 F) ltac:(left; reflexivity)) as FSEP. cbn [ab_addr ab_size] in FSEP.
Local Ltac2 Set LiaHints.tbl := fun () => "0130?10782553007.16011405914737.16112123010364.11712438227414.15012808249969.16112970872969.27 13409363337.11714712688537.16 14853550687.16015758436758.14817034297127.1171713438335.162 1715765442.166 1717764882.159 17991417505.11718802003475.14718969330854.11724124836557.16124629995946.14824700024599.14927615749535.16029147256363.15429531062692.11729784497005.16029786461159.14029788559742.10330093722840.10 31297135217.16132957640218.11733085935132.16533088130381.15933108746591.14033847131963.16034301889842.18 34303987250.25 34518666763.14835831773163.14042689731675.14846106731935.16047817153293.16148192795039.16049279820513.16150158469617.16152101737256.15452101950377.16552103800869.18752103800869.19352103800870.19052103948536.15952107990421.1625451248731.117 54606265521.16156170432946.11756759370246.16256763400043.15956765398074.16556765643963.15457441792573.11759308243815.14059308243821.10459308489062.15159323005400.14360283080991.16062986586310.11763988256203.14366006289884.7  7436363858.117 00000H00]00^01001E01_01`02102I02b02k03A04@04X04e04n04o05;05P05c06;06G06H06Q06Z06_07007E07F08>08a09909`0:40:J0:_0:l0;80;P0<J0<b0=70=L0=[0>90>T0?W0@N0@Z0A30A?0AT0Aa0Am0B90BE0BQ0B]0Bf0Bk0C40C=0CU0Ck0D>0DI0DVS3BOT2LO3ATR3GL23LSH3G5lS3FLO3GL13GL23LSH3G5lFS3GL23LSH2NE2E12E2S3FLO3GL13GL23LSH3G5lS3FLO3FHI2G11H2H02H42H52H9FS3FLR3G2c2NA1H2H0S3BOT2LO3ATR3GL23LSH3G5lS3FLO3FR03GL13GL23GL43LSHS3GL23LSHS3FLO3GL13GL23LSH2Hr1HS3ATR4F64'3FLO3FHI2FC3GL24FSEP3SHF4SSEP3LSH3FLR2Hr3G2c2Y12Y22Y3S3ATR3FHI3GL23GL33LSH2X1S3BOT3GL23LSHS3GL23LSHFS3GL23LSH2HaS3FLO3FR03GL23GL43LSHS3GL23LSH2E12E23NE1S3BOT2LO3ATR3GL23LSH3G5lS3GL23LSH2N2FS3GL23LSHS3GL23LSHS3GL2S3FLO3FHI3FRG3G2cS3FLO3GL13GL23LSH3G5lFS4F64'3FLO3FHI3GL24FSEP3SHF4SSEP3LSH3FLR2Hr3G2c2Y12Y32Y4S3BOT2LO3ATR3FLO3GL23GL33LSH3FLR2HsS3BOT2LO3FLO3GL13GL23LSHS3BOT2LO3ATR3FLO3GL23GL33LSH3G5l3GL12G6S3BOT2LO3ATR2NA1H2H0S3F642NA1H2H02H42H52H9S3FLO3FR03GL13GL23LSHS3FR03GL23LSHS3GL23LSH2NES3BOT2LO3ATR3GL23LSH3G5lS4F64'3FLO3FHI3FR03GL24FSEP3SHF4SSEP3LSH2G53G2c3ATR2FC3G5sS3BOT2LO3ATR3GL23LSH3G5lS3FLO3GL13GL23LSH3G5lS3FLO3GL13GL23LSH3G5lS3GL23LSH2N12N3S3BOT2LO3FLO3GL13GL23LSH2Hr2Y2S3BOT2LO3ATR2FC3LSH2Hs1H2H0S3ATR4F64'3FLO3FHI2FC4FSEP3SHF4SSEP3LSH3FLR2Hr3G2c2Y12Y32Y41H2H02H9S4F64'3FLO3FHI4FSEP3SHF4SSEP3LSH3FLR2Hr3G2c1H2H02H13H10S3GL23LSH2HsS3BOT2LO3ATR3GL23LSH2Hr1HS2LO3GL23LSHS3FLO3GL13GL23LSH3G5lS3SPT3GL23LSHS3GL23LSH2HaS3GL23LSH2HaS3GL23LSH2HaS3GL23LSH2HaS2FT3GL23LSHS3GL23LSHS3GL2S3GL23LSHS3GL23LSHS3BOT2LO3ATR3GL23LSH3G5lS4F64'3FLO3GL13GL23LSHS3FLO3GL13GL23LSH1HS3FLO3FHI1DS3FLT3GL23LSH".
assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
assert (SSEP : flag + 1 <= shad F \/ shad F + 256 <= flag).
{ pose proof (fk_flag_range L 5 pos ltac:(unfold FK_NCLS; lia) Hp) as FRG. subst flag. rewrite EF.
rewrite SHF. pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. clear - FRG G2c FLO FHI ATR G3. unfold FAKESZ in *. lia. }
destruct (AREP_cells DI AQ ASEC L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).
destruct (c8s_of_dc 32 m (shad F) (dc_of_cells m (shad F) [CB 256 sh] SH0)) as (shs & LSH & SHW).
clear SH0.
eapply evtF_mono.
{ eapply (stack_free5_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
FR fc m lo flag F (Z_to_bv 8 1) shs);
first [ exact MI | exact ST | exact A0 | exact FP | exact FLG | exact SHW | exact LSH | exact RIMG | exact R2 | exact R11 | exact R16
| eapply rng_sub'; [exact RSTK| lia] | eapply rng_sub'; [exact RFR| lia] | exact RFL | exact RFS | exact FB | exact FLB
| exact FSEP | exact SSEP | lia ]. }
cbv beta. intros ms' PO.
destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & -> & MU & WM & MI' & ST' & FL0' & SH').
unfold sf5_W in MU.
assert (AR' : AREP AHQ L st X m').
{ eapply (AREP_frame_ext' DI AQ ASEC HL L st X m m' _ ALO AR MU WM).
assert (SHL : shlen 11571200 = 1446400) by reflexivity. rewrite SHL. atop_facts.
pose proof (fk_flag_range L 5 pos ltac:(unfold FK_NCLS; lia) Hp) as FRG. subst flag. rewrite EF in *.
repeat (constructor; [cbn [fst snd]; intros _ |]); [right; right; lia | left; lia | right; left | constructor].
rewrite SHF. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear - FLO FHI G1 GL1. unfold FAKESZ in *. Z.div_mod_to_equations. lia. }
assert (NI : ~ In (FB5 F) LB) by (destruct BL as (_ & _ & _ & ND); inversion ND; assumption).
pose proof (afake_release L LB m 5 F 2048 HFK NI) as HFK1. fold flag in HFK1.
set (m1 := write_to_mem m (wa flag) [Z_to_bv 8 0]) in *.
assert (FLGV : m' (wa flag) = Some (Z_to_bv 8 0)) by (apply (rw_C1_high m' flag _ FL0'); pose proof (fk_flag_range L 5 pos ltac:(unfold FK_NCLS; lia) Hp); subst flag; rewrite EF; lia).
assert (MU1 : munch [(bv_unsigned sp - 16, bv_unsigned sp); (shad F, shad F + 256)] m1 m').
{ intros x Hx. cbn [outside] in Hx. destruct Hx as (N1 & N2 & _).
destruct (Z.eq_dec (bv_unsigned x) flag) as [E|NE].
- rewrite <- (Z_to_bv_bv_unsigned x). fold (wa (bv_unsigned x)). rewrite E, FLGV. subst m1.
rewrite write_to_mem_spec by (cbn; pose proof (bv_unsigned_in_range 64 x); lia). rewrite wa_unsigned by (pose proof (bv_unsigned_in_range 64 x); lia).
replace (flag <=? flag) with true by (symmetry; apply Z.leb_refl). cbn [length andb]. rewrite Z.sub_diag.
replace (flag <? flag + Z.of_nat 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
- rewrite (MU x) by (cbn [outside]; repeat split; try assumption; try lia; exact I).
subst m1. rewrite write_to_mem_spec by (cbn; pose proof (bv_unsigned_in_range 64 x); lia).
pose proof (bv_unsigned_in_range 64 x).
destruct (flag <=? bv_unsigned x) eqn:E1; destruct (bv_unsigned x <? flag + Z.of_nat (length [Z_to_bv 8 0])) eqn:E2; cbn [andb]; try reflexivity.
apply Z.leb_le in E1. apply Z.ltb_lt in E2. cbn [length] in E2. lia. }
assert (WM1 : wmono bsegs m1 m').
{ intros x Hx. destruct (Z.eq_dec (bv_unsigned x) flag) as [E|NE1].
- rewrite <- (Z_to_bv_bv_unsigned x). fold (wa (bv_unsigned x)). rewrite E. unfold wview. rewrite FLGV. discriminate.
- apply WM. subst m1. unfold wview in Hx |- *.
rewrite write_to_mem_spec in Hx by (cbn; pose proof (bv_unsigned_in_range 64 x); lia).
destruct (flag <=? bv_unsigned x) eqn:E1; destruct (bv_unsigned x <? flag + Z.of_nat (length [Z_to_bv 8 0])) eqn:E2;
cbn [andb] in Hx; try exact Hx.
apply Z.leb_le in E1. apply Z.ltb_lt in E2. cbn [length] in E2. lia. }
assert (HFK' : AFAKE L LB m').
{ eapply (afake_frame_sh L LB m1 m' _ HFK1 MU1 WM1). unfold afake_untouched_sh.
pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3). atop_facts. pose proof G as (_ & _ & _ & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
pose proof G5 as (G5s & G5i & G5l). unfold sclr, iclr, KLS, AIMG_LO in G5s, G5i.
constructor; [cbn [fst snd]; repeat split; lia |].
constructor; [| constructor]. cbn [fst snd].
rewrite SHF. pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. repeat split; lia. }
assert (BL' : ablocks L st X LB) by (eapply ablocks_tail; exact BL).
assert (AHP' : AHEAP_P AHQ L RNG st LB m').
{ split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AH ah_fake]. exact HFK'. }
assert (OUT : forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 16 <= a < bv_unsigned sp) -> a <> flag -> ~ (shad F <= a < shad F + 256) ->
m' (wa a) = m (wa a)).
{ intros a Ha N1 N2 N3. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
/\ (ab_addr b + ab_size b <= F \/ F + 2048 <= ab_addr b)).
{ intros b Hb. destruct b as [[p|c'] A' n']; cbn [ab_addr ab_size].
- pose proof (HB_FAKE DI AQ ASEC L RNG st (FB5 F :: LB) m p A' n' AHP ltac:(right; exact Hb)) as [(Q1 & Q2 & Q3 & Q4) D].
split; [exact Q1|]. split; [exact Q3|]. clear - D FLO FHI. unfold FAKESZ in *. lia.
- pose proof (afake_lb L _ m c' A' n' HFK ltac:(right; exact Hb)) as (_ & _ & _ & _ & _ & _ & X3 & X4 & _).
split; [exact X3|]. split; [exact X4|].
eapply (afake_lb_disjoint L _ m c' A' n' 5 F 2048 HFK); [right; exact Hb| left; reflexivity|].
intros EQ. apply NI. rewrite <- EQ. exact Hb. }
assert (FLR : al_fake L + 4096 <= flag < al_fake L + 36864).
{ pose proof (fk_flag_range L 5 pos ltac:(unfold FK_NCLS; lia) Hp) as FRG. subst flag. rewrite EF. exact FRG. }
assert (HPR : aheap_pres CI LB (bv_unsigned sp) m m').
{ intros a Ha HcA. split; [| intros W0; apply WM; exact W0].
pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3). atop_facts.
pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c.
destruct HcA as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
-
apply OUT; [lia| lia| lia| rewrite SHF; Z.div_mod_to_equations; lia].
-
pose proof (CI_OK iv Hiv). apply OUT; [lia| lia| intros ->; apply FLCI; exists iv; split; [exact Hiv| exact Hr] |].
rewrite SHF. Z.div_mod_to_equations. lia.
-
destruct (BLK b Hb) as (Y1 & Y2 & Y3). pose proof (FLAP b ltac:(right; exact Hb)) as Y4. unfold ablk, AIMG_HI, KLS in Y1.
apply OUT; [lia| lia| lia| rewrite SHF; Z.div_mod_to_equations; lia].
-
assert (NA : 0 <= a' < 2^47 /\ ~ (F <= a' < F + 2048)).
{ destruct Ha' as [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]].
- lia.
- pose proof (CI_OK iv Hiv). lia.
- destruct (BLK _ Hb) as (Y1 & Y2 & Y3). cbn [ab_addr ab_size] in Y1, Y2, Y3. unfold ablk, AIMG_HI, KLS in Y1. lia. }
assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
rewrite SHA in Ha |- *.
apply OUT; [lia| clear - NA SK3 BOT LO ATR; Z.div_mod_to_equations; lia| clear - NA FLR G2c; Z.div_mod_to_equations; lia|].
rewrite SHF. clear - NA F64. Z.div_mod_to_equations. lia. }
unfold sf5_postP. do 15 eexists. exists m'.
split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
unfold F5MAGIC in SH'. exact SH'.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
Section Inst.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC).
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Variable AI : AMallocIface.
Hypothesis E : AHEAP AI = AHEAP_P (AH DI AQ ASEC).
Hypothesis EC : aci AI = CI.
#[using="DI AQ ASEC HL CI CI_OK E EC"] Lemma stack_malloc_5_AI : stack_malloc_5_stmt AI fflag afake_rng.
Proof.
unfold stack_malloc_5_stmt. intros until lo. intros AHx NOFK MI ST BOT LO SPT TP RSTK RI RFS.
rewrite E in AHx. unfold ASM5_ENTRY. change 0x3d880 with ASTKMALLOC5.
eapply evtF_mono; [eapply (stack_malloc_5_P DI AQ ASEC HL CI CI_OK); eassumption|].
cbv beta. intros ms' PO. unfold sm5_postP in PO. unfold sm5_post.
destruct PO as (F & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & j0 & j1 & j2 & junk & EQ & MI' & ST' & HPR & AH' & REST).
exists F, x0, x1, x2, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, m', j0, j1, j2, junk.
rewrite E, EC. repeat (split; [assumption|]). exact REST.
Qed.
#[using="DI AQ ASEC HL CI CI_OK E EC"] Lemma stack_free_5_AI : stack_free_5_stmt AI fflag afake_rng.
Proof.
unfold stack_free_5_stmt. intros until sh. intros AHx FP SH0 F64 FB FT MI ST BOT LO SPT A0 RSTK RI RFS RFR RSF.
rewrite E in AHx. unfold ASF5_ENTRY. change 0x3da8c with ASTKFREE5.
eapply evtF_mono; [eapply (stack_free_5_P DI AQ ASEC HL CI CI_OK); eassumption|].
cbv beta. intros ms' PO. unfold sf5_postP in PO. unfold sf5_post.
destruct PO as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & EQ & MI' & ST' & HPR & AH' & REST).
exists x0, x1, x2, y0, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, m'.
rewrite E, EC. repeat (split; [assumption|]). exact REST.
Qed.
End Inst.
End CANSEC1.
