(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac InitMem ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg RtCells AProto ABase ABytes AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepExt
     FsKit AFake_iface F_tlsga F_m2s_b AFake_sm0.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Definition AH : aholes := mkAHoles AQ ASEC (ADEPOT DI) AFAKE.
Hypothesis HL : ahole_laws AH.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.

#[using="Type"] Lemma HB_FAKE : forall L RNG st LB m p A n,
  AHEAP_P AH L RNG st LB m -> In (HB p A n) LB ->
  ablock_range A n /\ (A + n <= al_fake L \/ al_fake L + 11571200 <= A).
Proof. intros. split; [eapply AHEAP_P_hb_range; eauto| eapply AHEAP_P_hb_fake; eauto]. Qed.

#[using="HL"] Lemma AREP_frame_ext' : forall L st X m m' W,
  alayout_ok L -> AREP AH L st X m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => fst iv < snd iv ->
            (al_fake L <= fst iv /\ snd iv <= al_fake L + 11571200)
         \/ (shad (al_fake L) <= fst iv /\ snd iv <= shad (al_fake L) + shlen 11571200)
         \/ ATOP <= fst iv) W ->
  AREP AH L st X m'.
Proof.
  (* [comment removed for export] *)
  intros L st X m m' W AL AR MU WM HW. eapply (AREP_frame_ext AH HL); [exact AL| exact AR| exact MU| exact WM|].
  eapply List.Forall_impl; [| exact HW]. cbv beta. intros iv H Hlt.
  destruct (H Hlt) as [A|[A|A]]; [left; exact A| right; left; exact A| right; right; left; exact A].
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma AREP_cells : forall L st X m, AREP AH L st X m ->
  rt_got m /\ rt_shbase m
  /\ rw_cells bsegs m 0xa08a0 [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m 0xa08a4 [C4 (Z_to_bv 64 0)]
  /\ rt_inited m /\ rt_layout m
  /\ rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells bsegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))]
  /\ rw_cells bsegs m (al_ctx L + 152) [C8 (Z_to_bv 64 (al_t L))]
  /\ (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None).
Proof.
  intros L st X m H. pose proof (AREP_relro AH L st X m H) as RR. unfold AREP, arep_rt in H. decompose [and] H.
  repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="CI_OK"] Theorem fake_flag_P : forall L RNG st LB m cls F N,
  AHEAP_P AH L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP          (* [comment removed for export] *)
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Proof.
  intros L RNG st LB m cls F N AHP Hin. pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof (afake_lb L LB m cls F N HFK Hin) as (Hc & Hn & Npos & F64 & FLO & FHI & FK & FC & pos & Hp & HF & EF & FR).
  pose proof (afake_flag L LB m cls F N HFK Hin) as FL.
  destruct HFK as (G & _). destruct G as (G1 & G2 & G3 & _). pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold FAKESZ, KHIGH, AIMG_HI in *.   (* [comment removed for export] *)
  destruct ARNG as (_ & _ & _ & _ & _ & _ & RF & _).
  split; [exact FL|]. Local Ltac2 Set LiaHints.tbl := fun () => "0070>1622940839.48 1624975249.49 22039512369.434912423071.43 57105366482.4358173650989.4359314873579.4700000F00Y00a01101901A01US3F643FLO2FR3GL13GL21DS3FLO2FR3GL13GL22X1S2FR3GL2S3FLO2FR3GL23GL3S2FR3GL2S2FR3GL2S3FLO2FR3GL13GL21R1H".
split; [eapply rng_sub'; [exact RF| lia]|]. split; [eapply ablk_sub; [exact G2| lia| lia]|]. split; [lia|]. split.
  - intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    + pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [_ D]. lia.
    + pose proof (afake_lb L LB m c' A' n' (proj2 (proj2 (proj2 AHP))) Hb) as (_ & _ & _ & _ & X1 & X2 & _). lia.
  - intros (iv & Hiv & R). pose proof (CI_OK iv Hiv). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ablocks_tail : forall L st X b LB, ablocks L st X (b :: LB) -> ablocks L st X LB.
Proof.
  intros L st X b LB (H1 & H2 & H3 & H4). split; [|split; [|split]].
  - intros p A n Hin. apply (H1 p A n). right; exact Hin.
  - intros c A n Hin. apply (H2 c A n). right; exact Hin.
  - destruct b as [[p|c] A n]; cbn in H3; [inversion H3; assumption| exact H3].
  - inversion H4; assumption.
Qed.

#[using="HL"] Theorem fake_release_P : forall L RNG st LB m cls F N,
  AHEAP_P AH L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP_P AH L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
Proof.
  intros L RNG st LB m cls F N AHP. pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof (afake_lb L _ m cls F N HFK ltac:(left; reflexivity)) as (Hc & Hn & Npos & F64 & FLO & FHI & FK & FC & pos & Hp & HF & EF & FR).
  assert (NI : ~ In (mkABlock (ABFake cls) F N) LB) by (destruct BL as (_ & _ & _ & ND); inversion ND; assumption).
  destruct HFK as (G & HFK'). pose proof G as (G1 & G2 & G3 & _). pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold FAKESZ, AIMG_HI in *.   (* [comment removed for export] *)
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [| eapply ablocks_tail; exact BL].
    eapply (AREP_frame_ext' _ _ _ _ _ [(fflag L cls F, fflag L cls F + 1)]); [exact ALO| exact AR| | |].
    + Local Ltac2 Set LiaHints.tbl := fun () => "0040>34526563510.4457105366482.4466072110537.4466110803663.4400000@00H00M00]S3FLO2FR3GL23GL3S2FR3GL2S3GL2S3FLO2FR3GL13GL2".
apply munch_write; [apply munch_refl| lia| cbn; lia|]. cbn. left. lia.
    + apply wmono_write, wmono_refl.
    + constructor; [|constructor]. cbn. intros _. left. lia.
  - cbn [AH ah_fake]. apply (afake_release L LB m cls F N); [exact (conj G HFK')| exact NI].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation FB0 F := (mkABlock (ABFake 0) F 64).
Definition SM_STACK : Z := 4096.   (* [comment removed for export] *)

Definition sm0_postP (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st (FB0 F :: LB) m'
    /\ F mod 64 = 0 /\ ablk F (F + 64) /\ F + 64 <= ATOP                 (* [comment removed for export] *)
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 (fflag L 0 F))]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0)]
    /\ rng RNG F 64 /\ rng RNG (shad F) 8.

(* [comment removed for export] *)
#[using="Type"] Lemma relro_word : forall m A v,
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  ARELRO_LO <= A -> A + 8 <= ARELRO_HI -> rw_bytes_b bsegs A (le8 (Z_to_bv 64 v)) = true ->
  rw_cells bsegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A v R LO HI RB. unfold ARELRO_LO, ARELRO_HI in *.
  eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m A (le8 (Z_to_bv 64 v)));
    [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
    | exact RB | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
#[using="HL"] Lemma arep_ext_sm0 : forall L st X m m' sp fs flag F,
  alayout_ok L -> AREP AH L st X m ->
  munch [(sp - 208, sp); (fs, fs + 8); (flag, flag + 1); (F + 24, F + 32); (F + 56, F + 64); (2147450880 + F / 8, 2147450880 + F / 8 + 8)] m m' ->
  wmono bsegs m m' ->
  fs = al_fake L -> ATOP <= sp - 208 -> fs + 4096 <= flag < fs + 36864 -> fs + 36864 <= F -> F + 64 <= fs + 11571200 ->
  shad fs <= 2147450880 + F / 8 -> 2147450880 + F / 8 + 8 <= shad fs + 1446400 ->
  AREP AH L st X m'.
Proof.
  intros L st X m m' sp fs flag F ALO AR MU WM E S1 S2 S3 S4 S5 S6.
  assert (SHL : shlen 11571200 = 1446400) by reflexivity.
  eapply (AREP_frame_ext' L st X m m' _ ALO AR MU WM). rewrite <- E, SHL. atop_facts.
  Local Ltac2 Set LiaHints.tbl := fun () => "0060>24439063673.2924893020817.2946365163094.2960125051567.2968358898262.298819272170.29 00000400500<00C00J00NS2S2SS2S32S4S2S52S6S2S32S4S2S1".
repeat (constructor; [cbn [fst snd]; intros _ |]); [right; right; lia| left; lia| left; lia| left; lia| left; lia| right; left; lia| constructor].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="HL CI_OK"] Theorem stack_malloc_0_P : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  (forall F n, ~ In (mkABlock (ABFake 0) F n) LB) ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF bsegs RNG (sm0_postP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros AHP NOFK MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.   (* [comment removed for export] *)
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).
  (* [comment removed for export] *)
  destruct (AREP_cells L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).
  (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "01i0?10092530843.1851043627856.180 1126798092.180 11482393301.20613859192917.20615047146784.14215047308710.20315536006710.10 1566707379.204 16601926841.2061713438335.10  1715765315.12  1715782596.9   17991072190.18018426717457.26 18426717457.29 18928859804.13820178006101.20620211304835.28 20735943053.9  20861619413.20622323378911.13222369263914.15323300114087.6  23700201109.18024125044652.21 24748059780.1802497545384.131 26087858018.20426889197080.1862701854589.131 27038025706.20629147256744.21029299450114.15329784497005.17929786479080.14329786644200.14431113308501.15033085935132.24 33086189277.19 33092481056.21 33490756850.17733977372108.5  34122686754.7  34304069349.21 34304097934.26 34304097934.28 34304097934.29 34494347618.15534977465718.13335097887758.26 35097887758.29 35440871153.18035696023445.18037656117931.28 40356282428.13841170069461.20641889386282.15441889427502.15241996978269.18046442045225.15546896980997.20646901177752.22446903072696.21646903274638.21446903274892.15447348482913.1534835283238.2   49927382112.20451064760517.20652101696360.19 52101737131.21052101950377.24 52107990421.21 52469690798.15452564951269.18 52564951269.23 52853427574.15053891125283.21054965598324.18055355428199.18655448986806.21355448989219.21455448989473.15455449179413.21655451086645.22455463667368.20655873094590.17655878874588.16 55880970962.9  56170253997.18056280132106.13256759370246.21 56765398074.24 56765644088.21056765668603.19 56953681963.20457161643492.14057980378352.18658037925428.16058229716486.13358351784165.15459424320314.16059754268945.20660524391140.5  60524548822.20461161636889.15261161650461.20463238912958.15263370183848.16063370230317.15563370230318.15363623655639.13364262607882.21 65645947670.17566754262900.13967150245700.18067419257744.1866753474698.150 8316659277.8   9058454530.133 00000Z00c00d01b02`02e02j03803g04004A04R04`04i05:05K05P06N06_06g07e07j08B08N08O08S08X08]09K09S09X09i0:10:I0:N0:S0:X0;50;L0;c0<60<;0<C0<N0=00=_0>N0?=0?U0?Z0@40@N0@O0@T0@n0A30B10B60B;0B<0BT0BY0B^0Bc0Bh0Bm0CE0CJ0D90E70EP0Ed0FM0Fi0GA0Gi0H_0I70I^0Ig0Io0J70J?0JG0JO0JW0J_0KF0K]0Kg0L00L50L90L=0LE0LI0M00M50M=0MY0M^0N60N?0Nf0Nn0OU0Om0PT0Pl0Q10Q60Q;0Q@0Q`0RG0RL0RT0R\0Ra0Ri0RnS3GL13GL23G5l3G7l2PB3EFF4HPOS5HFLAG3HFF2WFS3GL23CL2FS3BOT2LO3GL13GL23G5l3G7l3ATR2PB3EFF3SHF3SHS3SB14HPOS5HFLAG3HFFS3BOT2LO3GL13GL23G5l3G7l3ATR2PB3EFF3SHF3SHS3SB14HPOS5HFLAG3HFFS3GL2S3GL2S2G12G33ATR2PBS3GL13GL23G5l3G7l2PB3EFF3SHF3SB14HPOS5HFLAG3HFFS3GL13GL2S3GL12PB3HFF2Hr1HS3ATR2Hr2Y12Y22Y4S2G32PB3HFF2X1S3BOT3GL2S3GL13GL33ATR3FRGS3GL13GL33ATR3FRGS3GL2S3BOT2LO3GL13GL23G5l3G7l3ATR2PB3EFF3SHF3SHS3SB14HPOS5HFLAG3HFFS3GL13GL33ATR3FRGS2PB3G2cS3BOT2LO3GL13GL23G5l3G7l3ATR2PB3EFF3SHF3SHS3SB14HPOS5HFLAG3HFFS3GL2S3GL13GL23G5l3G7l2PB3EFFS2PB3SB13SB2FS2HaS3GL2S3GL2S3BOT2LO3GL13GL23G5l3G7l2PB3EFF4HPOS5HFLAG3HFFS3GL22LJS3GL2S3GL23G5l3G7l3SHSS3GL22N3S3GL13GL23G5l3G7l2PB3EFFS3GL2S3GL2S3GL2S3GL13GL23G5l3G7l3EFF3SB13SB2S2PB5HFLAG3HFF2Hr2Y32Y4S3BOT2LO2G32PB5HFLAG2HsS3GL12PB5HFLAG2Hr1HS3GL2S2PB3HFFS2G32PB3HFFS3BOT2LO3ATR3A'R2PB3HFF2NA3G2b3F64S3BOT2LO3GL33FRG2PB3HFF2G13GL23SHF3SHD5HFLAG2NES3BOT2LO3GL33FRG2PB3HFF2G13GL23SHF3SHD5HFLAG2NES3BOT2LO3GL33FRG2PB3HFF2G13GL23SHF3SHD5HFLAG2NES3GL13GL23G5l3G7l2PB3EFFS3GL2S2G13GL13GL22PB3SHF3HFF2NES2G13GL13GL22PB3SHF3HFF2NEFS3GL2S2G13GL13GL22PB3SHF3HFF2NES3GL2S3BOT2LO3GL13GL23G5l3G7l3ATR2PB3EFF3SHF3SHS3SB14HPOS5HFLAG3HFFS3GL2S3GL2FS3GL13GL23G5l3G7l2PB3EFFS3GL2S3GL2S3GL2S3GL2S3GL2S3GL13GL23G5l3G7l2PB3EFFS3G7IS3GL13GL23G5l3G7l2PB3EFF3SHF3SB14HPOS5HFLAG3HFFS3BOT2LO3GL13GL23G5l3G7l3ATR2PB3EFF3SHF3SHS3SB14HPOS5HFLAG3HFFS2Hs3BOT2LO2G32PB3HFF3ATRS3GL22N12N22N42N52N6S3BOT2LO2Hr2Y22PB3HFF2Y32Y42G33GL13ATR2Y1S3BOT2LO3ATR2Hr1H3GL12PB3HFFS3GL13GL23G5l3G7l2PB3EFFS3BOT2LO2G33GL13ATR2PB3SHF3SHD5HFLAG3HFFS3BOT2LO2G32G62G93GL13G5s3ATR2PB3SHF3SB33SHD5HFLAG3HFFS3GL13GL23G5l3G7l2PB3EFFS3GL13GL23G5l3G7l2PB3EFF4HPOS5HFLAG3HFFS3GL23G7lS3GL22LJS3GL22PBS3GL22PBS3GL22PBS3GL22PBS3GL22PBS3GL22PBS3GL13GL23G5l3G7l2PB3EFF4HPOS5HFLAG3HFFS2G13GL12PB3HFF2Q32Q41DS2X12X42DJS3SPT3GL2S3GL2S2HaS2HaS3GL22HaS2HaS3GL13GL23G5l3G7l2PB3EFF4HPOS5HFLAG3HFFS3GL2S3GL22LJS3GL13GL23G5l3G7l2PB3EFF3SB1S3GL2S3GL13GL23G5l3G7l2PB3EFFS3GL23SB2S3GL13GL23G5l3G7l2PB3EFF4HPOS5HFLAG3HFFS2PB3HFFS3GL13GL23G5l3G7l2PB3EFF4HPOS5HFLAG3HFFS3GL13GL23G5l3G7l2PB3EFFS3GL13GL23G5l3G7l2PB3EFF4HPOS5HFLAG3HFFS3GL13GL23G5l3G7l2PB3EFFS3GL2S3GL2S3GL2S3GL2S2PB5HFLAG3HFF3F642Ha3A'R2NA3G2bS3GL13GL23G5l3G7l2PB3EFF4HPOS5HFLAG3HFFS3GL2S2LO3GL2S3GL22LJS3GL2S2PB3HFFS3GL2".
pose proof (relro_word m 0x99060 0x130ad8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0x99d28 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells bsegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app bsegs m 0x99d18 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.
  set (h := bv_unsigned h0). set (pos := Z.land h 16383). set (flag := (al_fake L) + 4096 + pos). set (F := (al_fake L) + 36864 + pos * 64).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (PB : 0 <= pos < 16384).
  { subst pos. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL : flag = fk_flag L 0 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 0 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 0 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 4608 + 8 * pos = shad F /\ shad F + 8 <= shad (al_fake L) + 1446400 /\ shad F + 8 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }   (* [comment removed for export] *)
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 8 <= al_fake L \/ al_fake L + 11571200 <= shad F).   (* [comment removed for export] *)
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
  destruct (c1_of_dc m flag D3) as [fb FL0].
  assert (fb = Z_to_bv 8 0) as ->.
  { destruct (decide (fb = Z_to_bv 8 0)) as [E|NE]; [exact E| exfalso].
    apply (NOFK (fk_frame L 0 pos) (fk_fsize 0)). apply (FL 0 pos fb); [unfold FK_NCLS; lia| unfold fk_nframes; cbn; lia| | exact NE].
    rewrite <- EFL. apply (rw_C1_high m flag fb FL0). subst flag. lia. }
  (* [comment removed for export] *)
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 56) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].
  (* [comment removed for export] *)
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 8 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  destruct (c8_of_dc m _ DS2) as [sh0 SH0].
  (* [comment removed for export] *)
  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').
  (* [comment removed for export] *)
  assert (HNT' : rw_cells bsegs m (al_fake L) [C8 (Z_to_bv 64 h); C8 h1; C8 h2; CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).
  (* [comment removed for export] *)
  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (HPOS : pos = Z.land h 16383) by reflexivity. assert (HFLAG : flag = (al_fake L) + 4096 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 36864 + pos * 64) by reflexivity.
  clearbody h pos flag F.
  eapply evtF_mono.
  { eapply (stack_malloc0_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x5d3fd0 (al_fake L) h pos flag F j24 j56 sh0 h1 h2 hs);
      try exact MI; try exact ST; try exact TP; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FL1 & F24' & F56' & SH').
  unfold sm0_W in MU. rewrite SHF in MU.
  (* [comment removed for export] *)
  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) <= a < (al_fake L) + 8) -> a <> flag ->
            ~ (F + 24 <= a < F + 32) -> ~ (F + 56 <= a < F + 64) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 8) ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
  assert (F64 : F mod 64 = 0) by (rewrite EFR; apply fk_frame_al64; [exact G1| lia]).
  (* [comment removed for export] *)
  Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
  Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].   (* [comment removed for export] *)
  assert (AR' : AREP AH L st X m').
  { eapply (arep_ext_sm0 L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
  assert (NOTIN : ~ In (FB0 F) LB) by (apply NOFK).
  assert (HFK' : AFAKE L (FB0 F :: LB) m').
  { split; [exact G|]. split.
    { unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
      split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }   (* [comment removed for export] *)
    split; [exists (Z_to_bv 64 (h + 1)), h1, h2, hs; exact HNT2|].
    split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGC MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
    split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
    split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
    split.
    - intros c pos' b Hc Hp Hb NZ.
      destruct (Z.eq_dec c 0) as [->|NC]; [destruct (Z.eq_dec pos' pos) as [->|NP]|].
      + left. rewrite <- EFR. unfold fk_fsize. reflexivity.
      + right. pose proof (fk_flags_disjoint L 0 pos' 0 pos Hc Hp Hc ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L 0 pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
      + right. pose proof (fk_flags_disjoint L c pos' 0 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L c pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
    - intros c F' n' [E|Hin].
      + injection E as <- <- <-. split; [unfold FK_NCLS; lia|]. split; [reflexivity|].
        exists pos. split; [unfold fk_nframes; cbn; lia|]. split; [exact EFR|].
        rewrite <- EFL. apply (rw_C1_high m' flag _ FL1). lia.
      + destruct (LV c F' n' Hin) as (Hc & Hn & pos' & Hp & HF' & B1).
        split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp|]. split; [exact HF'|].
        assert (NE : fk_flag L c pos' <> flag).
        { rewrite EFL. apply (fk_flags_disjoint L c pos' 0 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia)).
          intros E. injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn in Hin. unfold fk_fsize in Hin.
          cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add] in Hin. exact Hin. }
        pose proof (fk_flag_range L c pos' Hc Hp) as FRG. rewrite OUT by (first [clear -FRG NE G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). exact B1. }
  (* [comment removed for export] *)
  assert (BL' : ablocks L st X (FB0 F :: LB)).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
    - intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - cbn. exact B3.
    - constructor; [exact NOTIN| exact B4]. }
  assert (AHP' : AHEAP_P AH L RNG st (FB0 F :: LB) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AH ah_fake]. exact HFK'. }
  (* [comment removed for export] *)
  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP   (* [comment removed for export] *)
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 64 <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (0, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in Hb.
        replace (fk_fsize 0) with 64 in Hb by reflexivity. exact Hb. }
      pose proof (fk_frames_disjoint L c' pos' 0 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 0) with 64 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->   (* [comment removed for export] *)
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 64)).
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
      pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.   (* [comment removed for export] *)
      apply OUT; clear - Ha A'R NA F64 G2b G3 HFF HFLAG PB LO SK3 BOT ATR; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  (* [comment removed for export] *)
  pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
  pose proof (dc_at_any m m' (F + 32) 24 DJ1 WM ltac:(lia)) as DJ1'.
  destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
  destruct DJ1' as [junk1 J1]. change (Z.to_nat 24) with 24%nat in J1.
  assert (LJ : length junk1 = 24%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 32 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 0 F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app bsegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 32 (le8 sp ++ junk1)] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
      eapply rw_cells_recast; [apply (proj2 (rw_cells_app bsegs m' (F + 24) [C8 sp] [CB 24 junk1])); split; [exact F24'|];
        cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
      + reflexivity.
    - cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 32) with (F + 56) by lia. exact F56'. }
  (* [comment removed for export] *)
  unfold sm0_postP. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].   (* [comment removed for export] *)
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
(* [comment removed for export] *)
End S.
End CANSEC1.
(* [comment removed for export] *)
