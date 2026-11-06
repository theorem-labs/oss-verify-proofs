(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem Mem Frame.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface AHarness_iface AH_fi_iface AF_fi_kit AF_fi_gfha_iface AF_fi_ffsi_iface AF_fi_cbs AF_fi_ffsi AF_fi_ffsi2.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
#[using="Type"] Lemma bytes_at_nil_any : forall (m m' : amem) S, bytes_at asegs m S [] -> bytes_at asegs m' S [].
Proof. intros m m' S (A & B & _). split; [exact A|]. split; [exact B|]. intros i Hi. cbn in Hi. Local Ltac2 Set LiaHints.tbl := fun () => "0010=20742173918.8000004S2Hi".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma unpoisoned_mgA : forall (P : Z -> Prop) m m' lo hi,
  magree asegs P m m' -> unpoisoned m lo hi -> (forall s, shad lo <= s <= shad (hi - 1) -> 0 <= s < 2^64 /\ P s) -> unpoisoned m' lo hi.
Proof.
  intros P m m' lo hi MG U HP. eapply unpoisoned_agree; [exact U|]. intros s Hs. destruct (HP s Hs) as [R Ps]. exact (proj1 (MG s R Ps)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cells24_split : forall m R rj, rw_cells asegs m R rj -> cells_size rj = 24%nat ->
  exists r0 r1 r2, rw_cells asegs m R [CB 8 r0; CB 8 r1; CB 8 r2].
Proof.
  intros m R rj RR RC. destruct (rw_cells_forget asegs _ R rj RR) as [rjb RR']. rewrite RC in RR'.
  apply (rw_cells_split_CB asegs _ _ [] 24 rjb [] [8; 8; 8]%nat) in RR'; [| reflexivity]. cbn [app mk_CB_cells] in RR'.
  do 3 eexists. exact RR'.
Qed.

Section Asm.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFLAG : fake_flag_law AI fflag.
Hypothesis FREL : fake_release_law AI fflag.
Hypothesis SM2 : stack_malloc_2_stmtk AI fflag rng_fs 0.
Hypothesis GFHA : gfhaA_stmt AI rng_fs.
Hypothesis GIMG : In (0x20d40, 0x20dc0)%Z CI.      (* [comment removed for export] *)
Notation FB2 F := (mkABlock (ABFake 2) F 256).

#[using="fflag FFLAG FREL SM2 GFHA GIMG"] Theorem ffsiA : ffsiA_stmt AI rng_fs.
Proof.
  unfold ffsiA_stmt.
  intros L RNG ra SPV gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB S bl R lo rj
         AH LE2 LE0 LBH BUF NB HC RR RC RU R8 RLO RHI GSH ST BOT LO SPT SP16 MI TP RSTK RI RIS RFS RGR RGRS -> -> -> ->.
  pose proof atop_range as ATR.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  unfold AFI_FFSI_STACK, AFI_STACK in LO.
  pose proof (proj1 (spa160_propsA SPV SP16)) as SPAB.
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  pose proof (proj1 BUF) as PL. pose proof (proj2 BUF) as PLR.
  pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
  Local Ltac2 Set LiaHints.tbl := fun () => "03C0?10262368252.16 10267022884.10410671207325.21810671207325.21910671207325.22010671207696.21610671209228.15910671209228.16910671209228.17510671209228.27810671209228.27911806881280.19 12221711412.16412221726393.19812221726393.28512223805064.15112223903412.17012223903414.2711387335774.97  16218619487.17716788340406.22 17283174832.17717293679287.10617990991374.27517991086127.97 17991089884.18817991466122.14117997708175.22917997708813.15618433022589.15718614817987.15218614817987.22619613511714.14120133607273.2  20667538767.15621158549593.22 21307645287.14121307920834.97 21307924273.18821308088291.27521322275426.22921322276832.15621445010926.13721455462619.10622968732719.15523482321.148   23950491086.17124526329910.22 25189311172.10625391299896.19 25400221292.11526492779925.15726987940018.6  27016578387.20227016578387.28927858218882.17727860296837.10628571277759.15728573892092.16528573892092.16628573892092.17628573892092.17728573892092.17829492660456.92 29716468022.20 29782628086.17729784460045.21729786378328.27129786378330.17029786463883.6  29786476646.15129788544730.17229788544731.16029788559447.19829788559447.28529788562138.16429928407609.20629928407609.29329928409768.15629928409768.15730190085610.27931122784804.17731349211992.27131797050725.2  32243272321.11032243272321.15332243272321.16232243272321.16332243272321.17432243272321.22632243272321.22732293822159.15632690013010.20032690013010.28733130444578.20133130444578.28834891932807.15935056585985.16 37424196509.5  3781352017.19  39139380329.14739473606516.2  40575443709.17741676285799.1474221554311.177 42243602205.1594239620236.206 4239620236.293 4293178008.19  43709756574.16643709756574.17243709773854.17043709840670.16943716129054.16743716129054.17343716129182.16843716129182.17443857808572.20043857808572.28744967481793.19 45454628868.13745608879113.15445608879113.16345608879113.17545608879113.22747780784477.15947780784477.16947780784477.17547780784477.20647780784477.27947780784477.29347872599800.10249061310573.27549061474495.18849061477964.97 49061786345.14149068093550.15649068094956.2294982651661.177 5032045212.16  50509325115.27150539538257.19 52037536707.2  52101693566.21652101693566.21752101693566.21852101693566.21952101693566.22052101693566.22552101693566.23352711878607.15653200825392.10653226618553.20 53508799735.15754173630041.17756170235708.97 56170236367.18856170334493.27556170384281.14156185113756.2295634532874.177 57345046017.16 57716256011.15957716256011.23358583933551.14559005644836.16459020395172.17059020395174.27159148144883.14659308586893.88 59308873939.1105971648561.105 59766740182.22959768886227.14159769164165.18859769167734.97 59769327959.27559828028393.2  60595102003.15961116395122.14761139289836.1776149777529.20  62012710248.20062012710248.28763183223768.15563868847056.15064303179846.16364303179846.22764586178545.19 65919039353.16 67046409304.86 67136807939.15867389891845.15168652184072.22668695936106.1067890714315.164 7896976503.151 7897074761.271 7897074763.170 8119806256.152 8119806256.226 8233992770.279 8378946369.216 8378946369.221 8378946369.222 8378946369.223 8378946369.224 9508784316.16  9608221186.277 9608221839.151 9692427101.2   00000D00L00W00b00m01801C01N01Y01h02702;02D02M02e02n03703D03T03`04304W05705G05O05[05g06306?06G06h07I07J07P07X07g07h07i07j07k07l07m08M08m09509^0:R0:^0:f0;60;[0<G0<T0=70=^0>F0>j0?50?_0@N0A=0Al0B[0Be0C10C90CD0CP0CX0CY0Ca0Ci0D10D90DE0DM0Dl0EO0En0FM0G80GD0GP0GQ0Go0H:0HE0HP0H[0Hf0I10I90IE0IU0J80J_0KC0K\0Ke0Kn0L90L?0LG0LO0LW0MP0M[0Mj0N;0Nb0OI0PA0Q90Qe0RQ0SI0TA0TM0T]0Ta0Te0U00U;0UF0UQ0U\0Ug0V20V=0VL0V[0W>0WM0WX0W_0Wj0X50X@0XL0X`0YQ0YZ0Y`0ZK0[A0[L0[W0[b0\U0][0]c0^>0^M0^X0^`0^h0_40_D0_P0_\0_d0`=0`e0aM0ag0bK0bo0cW0d10d;0d\0e:0e;0e<0e=0e>0e?0eE0el0fA0fM0fa0fm0g=0gE0gM0h20hW0hh0i80iS0j?0jk0kU0l00l80l@0lL0lT0m60mX0n@0nK0o:0oV10E10\11211C11P11WS3RLO3BOT2LO3ATR3FHuS2RC3RLOS2RC3FHb2HaS2RC3FHb2HaS2RC3FHb2HaS2RC3FHb2HaS2RC3FHb2HrS2RC3FHb2HrS2RC3FHb2HrS2RC3FHb3CL62HrS2RC3FHb3CL62HrS2GFS2RC4F256S2RC4F256S2RC4F2563FHu2GF3CL63GHuS2RC4F256S2RC4F256S2RC4F2563CL6S2RC3RLO3RHI3LY3S2RC3FHa3FHbS3RLO3BOT2LO2SN3DHcS2RC3RLO3BOT2LO3ATR3LY13LY44SPAB3FHbS2RC3RLO3BOT2LO3ATR3LY13LY44SPABS2RC3BOT3FHb3CL6S2RC3BOTS2RC3BOT3FHbS2RC3BOT3FHbS2RC3BOT3FHbS2RC3BOT3FHbS2RC3FHbS2RC2R83RLO3RHI3BOT2LO3ATR3LY32HsS2RC2R83RLO3RHI3BOT2LO3ATR3LY32HsFS4F256S2RC3FHbS3BSF2DS2SN3DHuFFFFFFS2RC3RLO3RHI3BOT2LO3ATR3LY34SPABS2RC3RLO3RHI3BOT2LO3ATR3LY34SPABS2RC3FHbS2RC3RLO3BOT2LO3ATR3LY13LY44SPAB4RHI'3FHbS2RC2R83RLO3BOT2LO4SP163ATR3LY13LY23LY44F2563FHb3BSFS2DS2SN4SEPFS2RC3BOTS3RLO3BOT2LO3GHcS2RC3RLO3BOT2LO3ATR3LY13LY42Ha2D23BBKS2RC3RLO3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc3BSFS3ATR3FHa3FHcS2RC3RLO3BOT2LO3ATR3LY13LY43FHb3GHcS2RC3RLO3BOT2LO3ATR3LY13LY43FHb3GHc3CL6S2RC3RLO3RHI3BOT2LO3ATR3LY13LY44SPAB3FHbS2RC3RLO3RHI3BOT2LO3ATR3LY13LY44SPABS2RC3FHb2FDS2RC3RLO3BOT2LO3ATR3LY13LY43FHb3FHc3BSF2HxS2RC3RLO3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc3BSF2HxS2RC3RLO3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc3BSF2HxS2RC3RLO3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc3BSF2HxS2RC3RLO3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc3BSF2HxS2D12D22RCS2DS2SN4SEPFS2RC3FHbS2RC3FHb2HaS2RC3FHb3CL6S2RC3FHbSS2RC3FHbS2RC3FHbS2RC3FHbS2RC3FHbS2RC3FHb3CL6S2RC3FHbS2RC3RLO3BOT2LO3ATR3LY13LY43FHbS2RC3RLO3BOT2LO3ATR3LY13LY43FHb3CL6S2RC3RLO3BOT2LO3ATR3LY13LY43FHbS2RC3RLO3BOT2LO3ATR3LY13LY43FHbS2RC3RLO3BOT2LO3ATR3LY13LY44SPAB3FHb3CL62HrS2RC3FHb3FHdS2RC3FHb3CL6SS2RC3RLO3BOT2LO3ATR3LY13LY42HaS2RC3FHb2NZS2RC3FHb2NZS2RC3FHb2NZS2RC3FHb2NZS2RC3FHb2NZS2RC3FHb2NZS2RC3FHbS2RC3FHb3GHdS2RC3FHb3GHd3CL6S2RC3RLO3BOT2LO3ATR3LY13LY43FHb3BSFS2RC3RLO3BOT2LO3ATR3LY13LY43FHb3BSF3CL6S2RC3RLO3BOT2LO3ATR3LY13LY44SPAB3FHbS3RLO3BOT2LO3ATR4RHI'3FHuS4F2562HaS3BSF3GHuS2RC3FHb2DJS4F256S2RC3FHbS2RC3FHbS2RC3FHbS2RC2R83RLO3BOT2LO4SP163ATR3LY13LY23LY44SPAB4F2563FHb3BSFS2RC3FHb2HrS2RC3FHb3CL62HrS3BOT2LO4SPAB3GHcS2RC3RLO3BOT2LO3ATR3LY13LY43FHb3FHc3BSFS2RC3RLO3BOT2LO3ATR3LY13LY43FHb3FHc3BSFS2RC2R83RLO3BOT2LO4SP163ATR3LY13LY23LY44F2563FHb3FHu3BSFS2RC2R83RLO3BOT2LO4SP163ATR3LY13LY23LY44F2563FHb3FHu3BSFS2RC3RLO3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc3BSFS2RC3RLO3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc3BSFS2RC2R83RLO3BOT2LO4SP163ATR3LY13LY23LY44F2563FHb3FHu3BSFS2RC2R83RLO3BOT2LO4SP163ATR3LY13LY23LY44F2563FHb3FHu3BSFS2RC3FHb3GHaS2RC3FHb3GHa3CL6S2GFS2RCS2RC3FHb2Z0S2RC3FHb2Z0S2RC3FHb2Z0S2RC3FHb2Z0S2RC3FHb2HrS2RC3FHb2HrS2RC3FHb2HrS2RC3FHb2HrS2RC3FHb3CL62HrS2RC3FHb3CL62HrS2RC3RLO3RHI3BOT2LO3ATR3LY13LY33LY4S2RC2LO3FHb3CL6S2RC2LO3FHbS2RC2LOS2RC2LO3FHbS2RC2LO3FHbS2RC2LO3FHbS2RC3FHb3FHdS3RLO3BOT2LO3ATR3FHuS2RC3RLO3RHI3BOT2LO3ATR3LY13LY44SPAB4RHI'3FHb3CL6S3BSF3GHuS4F256S2RC3RLO3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc2HaS2RC2R83RLO3BOT2LO4SP163ATR3LY13LY23LY43FHb3FHu3BSF2HaS2RC3FHb2HaS2RC3FHb2HaS2RC3FHb2HaS2RC2R83RLO3BOT2LO4SP163ATR3LY13LY23LY44F2563FHb2HaS2RC2R83RLO3BOT2LO4SP163ATR3LY13LY23LY43FHb3FHu3PAY3GHa2NZ2D12D22FD2HaS2RC3FHbS2RC3RLO3BOT2LO3ATR3LY13LY4S3BSF2DS2SN3DHuS2RC3FHb2HNS2RC3FHbS2RC3SPTS2RC3SPT3FHbS2RC3SPT3FHb3CL6S2RC3SPT3FHbS2RC3SPT3FHbS2RC3FHbS3RLO3BOT2LO3ATR4RHI'3FHuS2RC3RLO3BOT2LO3ATR3LY13LY43FHb2D12D22HaS2RC3RLO3BOT2LO3ATR3LY13LY43FHb2D12D22HaS2RC3RLO3RHI4SPAB4RHI'3FHbS2RC3RLO3BOT2LO3ATR3LY13LY44RHI'3FHbS2RC3RLO3BOT2LO3ATR3LY13LY44RHI'3FHbS2RC3RLO3BOT2LO3ATR3LY13LY44RHI'3FHb3CL6S2RC3RLO3RHI4SPAB4RHI'3FHbS2Z02RC2HnS2RC3RLO3BOT2LO3ATR3LY13LY42Ha2Z0S2RC2R83RHI3BOT2LO3ATR3LY13LY4FFFFFS4F256S2RC3RLO3BOT2LO3ATR3LY13LY44SPAB3FHb2HrS2RC3RLO3RHI4RHI'3FHbS2RC3FHa3FHbS3BOT2LO4SPAB2SN3DHcS2RC3FHb3GHaS2RC3FHb3GHa3CL6S2RC3FHbS2RC3FHbS2RC3RLO3BOT2LO3ATR3LY13LY42BB3FHb2Z0S2RC3RLO3BOT2LO3ATR3LY13LY42BB3FHb2Z0S3BOT2LO4SPAB3GHcS3RLO3BOT2LO3ATRS2RC3RHI3BOT2LO3LY13LY33LY4S2RC3RLO3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc3BSFS2RC3RLO3RHI3BOT2LO3ATR3LY13LY33LY44SPAB3FHbS2RC2R83RLO3RHI3BOT2LO3ATR3LY34RHI'3FHu2HsS2RC3RLO3BOT2LO3ATR3LY13LY4S2RC3FHbS2RC3FHbS2RC3FHb3CL6S2RC3FHbS2RC2R83RLO3RHI3BOT2LO3LY34RHI'2HsS2RC2R83RLO3RHI3BOT2LO3LY34RHI'2HsS2RC3RLO3BOT2LO3ATR3LY13LY44SPAB3FHb3CL6S2RC3FHb2HaS2RC3RLO3RHI3BOT2LO3ATR3LY13LY33LY44SPAB3FHb2HaS2RC3RLO3RHI3LY34SPAB3FHb2HaS2RC3RLO3RHI3BOT2LO3ATR3LY13LY33LY44SPAB3FHb2HaS2RC3RLO3RHI3LY33FHb2HaS3BOT2LO3ATR4SPAB4RHI'S2RC4SPAB3FHb3CL6S2RC4SPAB3FHbS5SPA32".
assert (RHI' : R + 24 <= 2^47) by lia.
  (* [comment removed for export] *)
  assert (PAYX : exists D N, 0 < zlen bl -> exists p, In (HB p D N) LB /\ D <= S /\ S + zlen bl <= D + N).
  { destruct HC as [Z0|(p & D & N & Hin & D1 & D2)].
    - exists 0, 0. intros Hn. exfalso. lia.
    - exists D, N. intros _. exists p. split; [exact Hin| lia]. }
  destruct PAYX as (D & N & PAYB).
  (* [comment removed for export] *)
  destruct (cells24_split m R rj RR RC) as (r0 & r1 & r2 & RR0). clear RR.
  (* [comment removed for export] *)
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
  destruct RTC as (_ & GOT & _ & _ & SHB & SUA & _).
  pose proof (ffsi_got_cells m (AI_relro AI _ _ _ _ _ AH)) as GSU.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply ffsi_pro with (lo := lo); try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
    all: try (unfold KEND; lia). all: try (eapply rng_sub'; [exact RSTK| lia]). all: try (unfold AFI_STACK; lia). }
  cbv beta. intros ms' (m1 & jA & -> & MU1 & WM1 & MI1 & FRB1 & FRA1 & STL1 & STG1).
  clear GOT SHB SUA GSU.
  assert (AH1 : AHEAP AI L RNG st LB m1).
  { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. lia. }
  assert (MG1 : magree asegs (fun a => aclient_addr CI LB SPV a /\ ~ (R <= a < R + 24)) m m1).
  { eapply magree_mono; [eapply magree_of_munch; [exact MU1| exact WM1]|]. intros a [Ha _]. cbn. split; [| exact I].
    intros Hr. exact (stack_not_client CI LB SPV (SPV - 192) a HCI HCI0 LBH ltac:(lia) Hr Ha). }
  pose proof (rw_cells_transport _ _ _ _ _ _ RR0 MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I])) as RR1.
  assert (RU1 : unpoisoned m1 R (R + 24)).
  { eapply unpoisoned_munch; [exact RU| exact MU1|]. rewrite !shad_div. unfold ASHOFF. cbn [disjoint_from]. split; [| exact I].
    OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (GSH1 : gshA m1).
  { unfold harness_invA, GSH_ADDR in *. eapply rw_cells_transport; [exact GSH| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add]. split; [lia| exact I]. }
  assert (PL1 : bytes_at asegs m1 S (map (Z_to_bv 8) bl)).
  { eapply bytes_at_magree; [| exact PL|].
    - eapply magree_mono; [eapply magree_of_munch; [exact MU1| exact WM1]|]. intros a Ha. exact Ha.
    - rewrite length_map. intros a Ha. cbn. split; [| exact I].
      destruct (Z.eq_dec (zlen bl) 0) as [Z0|NZ]; [exfalso; lia|].
      destruct (PAYB ltac:(lia)) as (p & Hin & D1 & D2). pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hin) as BBK. cbn in BBK. lia. }
  clear MU1 WM1.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { pose proof SM2 as SMC. unfold stack_malloc_2_stmtk, sm_stmtk in SMC. eapply SMC with (lo := lo); clear SMC;
      rewrite ?(unsigned_lit (SPAz SPV)) by lia;
      first [exact AH1| exact LE2| exact MI1| exact STL1| exact TP| reflexivity| exact RSTK| exact RI| exact RFS| lia]. }
  cbv beta. intros ms' PO.
  destruct PO as (FF & z5 & z6 & z7 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & z28 & z29 & z30 & z31 & m2 & j0 & j1 & j2 & junk
                  & -> & MI2 & ST2 & HPR2 & AH2 & F256 & FH & FC & FFC2 & SHF2 & RFF & RSFF).
  rewrite ?(unsigned_lit (SPAz SPV)) in ST2, HPR2 by lia.
  retlitA.
  change (Z.to_nat (256 - 32)) with 224%nat in FFC2. change (256 / 8) with 32 in RSFF.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
  pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
  assert (NFB : ~ In (FB2 FF) LB).
  { pose proof (AI_blocks_nodup AI _ _ _ _ _ AH2) as NDx. inversion NDx as [|x l NI0 N3]. exact NI0. }
  assert (FFD : forall b, In b LB -> FF + 256 <= ab_addr b \/ ab_addr b + ab_size b <= FF).
  { intros b Hb. assert (NE : FB2 FF <> b) by (intros E; apply NFB; rewrite E; exact Hb).
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 ltac:(left; reflexivity) ltac:(right; exact Hb) NE) as DJ. cbn in DJ. lia. }
  (* [comment removed for export] *)
  assert (PAY : 0 < zlen bl -> D <= S /\ S + zlen bl <= D + N /\ N <= 2^40 /\ ablk D (D + N) /\ D mod 16 = 0 /\ rng RNG D N /\ rng RNG (shad D) (shlen (N + 7))
                /\ (D + N <= FF \/ FF + 256 <= D)).
  { intros Hn. destruct (PAYB Hn) as (p & Hin & D1 & D2).
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hin) as (HN & (R1 & R2 & R3 & R4) & RGA & RGS & _).
    pose proof (FFD _ Hin) as FD. cbn in FD. unfold AREQMAX in HN.
    repeat match goal with |- _ /\ _ => split end; try assumption; lia. }
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRB1 ltac:(left; left; cbn; lia)) as FRB2.
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA1 ltac:(left; left; cbn; lia)) as FRA2.
  pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG1 ltac:(lia) ltac:(lia)) as STG2.
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 RR1 ltac:(left; left; cbn; lia)) as RR2.
  assert (MG2 : magree asegs (fun a => aclient_addr CI LB SPV a /\ ~ (R <= a < R + 24)) m m2).
  { eapply magree_trans; [exact MG1|]. eapply magree_mono; [exact HPR2|]. intros a [Ha _]. eapply aca_monoA; [exact Ha| intros b Hb; exact Hb| lia]. }
  assert (RU2 : unpoisoned m2 R (R + 24)).
  { eapply (unpoisoned_mgA _ m1 m2); [exact HPR2| exact RU1|]. intros s Hs. rewrite !shad_div in Hs. unfold ASHOFF in Hs.
    split; [OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia|]. right; right; right. exists (8 * (s - ASHOFF)). split; [| symmetry; apply shad_unshad].
    left. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (GSH2 : gshA m2) by (eapply gshA_mg; [exact HPR2| intros a Ha; exact (gsh_client CI LB (SPAz SPV) a GIMG Ha)| exact GSH1]).
  assert (PL2 : bytes_at asegs m2 S (map (Z_to_bv 8) bl)).
  { destruct (Z.eq_dec (zlen bl) 0) as [Z0|NZ].
    - assert (E : bl = []) by (destruct bl; [reflexivity| cbn in Z0; lia]). rewrite E in PL1 |- *. exact (bytes_at_nil_any m1 m2 S PL1).
    - destruct (PAYB ltac:(lia)) as (p & Hin & D1 & D2).
      eapply bytes_at_magree; [exact HPR2| exact PL1|]. rewrite length_map. intros a Ha. apply (cl_block CI LB (SPAz SPV) (HB p D N) a Hin). cbn. lia. }
  clear MG1 HPR2 FRB1 FRA1 STG1 STL1 MI1 AH1 RR1 RU1 GSH1 PL1.
  (* [comment removed for export] *)
  eapply evtF_cut; [| intros ms' Hms; exact Hms].
  eapply ffsi_hdr with (lo := lo); try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
  all: try (unfold KEND; lia). all: try (eapply rng_sub'; [exact RSTK| lia]). all: try (unfold AFI_STACK; lia).
  intros m3 j48 MU3 WM3 MI3 FRA3 FFC3 SHF3. cbv beta.
  assert (BSF : 2148232192 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 32 <= 17594333495296)
    by (clear - FHa FHb FHc ATR; rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  assert (ESH : shad FF = Z.shiftr FF 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (AH3 : AHEAP AI L RNG st (FB2 FF :: LB) m3).
  { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
    constructor; [cbn; left; left; lia|].
    constructor; [cbn; right; left; exists (FB2 FF); split; [left; reflexivity| cbn; lia]|].
    constructor; [cbn; right; right; right; right; exists 2, FF, 256; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                  change (2 ^ 3) with 8; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]| constructor]. }
  assert (LBH3 : forall b, In b (FB2 FF :: LB) -> ablk (ab_addr b) (ab_addr b + ab_size b)).
  { intros b [<-|Hb]; [exact FH| exact (LBH b Hb)]. }
  (* [comment removed for export] *)
  assert (NCS : forall a X, ATOP <= X -> X <= a < SPV -> ~ aclient_addr CI LB SPV a).
  { intros a X HX Ha. exact (stack_not_client CI LB SPV X a HCI HCI0 LBH HX Ha). }
  assert (NCF : forall a, FF <= a < FF + 256 -> ~ aclient_addr CI LB SPV a).
  { intros a Ha. exact (app_not_client CI LB SPV FF 256 a HCI HCI0 FH ltac:(lia) LBH FFD Ha). }
  assert (NCH : forall a, Z.shiftr FF 3 + 2147450880 <= a < Z.shiftr FF 3 + 2147450880 + 32 -> ~ aclient_addr CI LB SPV a).
  { intros a Ha. refine (shadow_not_clientN CI LB SPV FF 256 a HCI HCI0 FH ltac:(clear - F256; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia) ltac:(reflexivity) ltac:(lia) ltac:(lia) LBH FFD _).
    rewrite ESH. change (256 / 8) with 32. exact Ha. }
  assert (MG3 : magree asegs (fun a => aclient_addr CI LB SPV a /\ ~ (R <= a < R + 24)) m m3).
  { eapply magree_munch_step; [exact MG2| exact MU3| exact WM3|]. intros a [Ha _]. cbn.
    split; [intros Hr; exact (NCS a (SPAz SPV) ltac:(lia) ltac:(lia) Ha)|].
    split; [intros Hr; exact (NCF a ltac:(lia) Ha)|].
    split; [intros Hr; exact (NCH a ltac:(lia) Ha)| exact I]. }
  pose proof (rw_cells_transport _ _ _ _ _ _ FRB2 MU3 WM3 ltac:(cbn; lia)) as FRB3.
  pose proof (rw_cells_transport _ _ _ _ _ _ RR2 MU3 WM3 ltac:(cbn; lia)) as RR3.
  assert (GSH3 : gshA m3).
  { unfold harness_invA, GSH_ADDR in *. eapply rw_cells_transport; [exact GSH2| exact MU3| exact WM3|]. cbn. lia. }
  assert (RU3 : unpoisoned m3 R (R + 24)).
  { eapply unpoisoned_munch; [exact RU2| exact MU3|]. rewrite !shad_div, ?Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2^3) with 8. cbn [disjoint_from].
    clear - ATR SPAB LO BOT RLO RHI' LY3 FHb FHc FHu. repeat split; try exact I; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (PL3 : bytes_at asegs m3 S (map (Z_to_bv 8) bl)).
  { destruct (Z.eq_dec (zlen bl) 0) as [Z0|NZ].
    - assert (E : bl = []) by (destruct bl; [reflexivity| cbn in Z0; lia]). rewrite E in PL2 |- *. exact (bytes_at_nil_any m2 m3 S PL2).
    - destruct (PAY ltac:(lia)) as (DS & SN & NN & DH & D16 & RGA & RGS & SEPF). pose proof (ablk_lin _ _ DH) as (DHa & DHb & DHc & DHd).
      pose proof DH as DHu. unfold ablk, AIMG_HI, KLS in DHu.
      eapply bytes_at_transport; [exact PL2| exact MU3|]. rewrite length_map. cbn [disjoint_from]. clear - DS SN DHu DHb DHc BSF SPAB LO BOT ATR SEPF FHb. repeat split; try exact I; lia. }
  assert (UNP3 : unpoisoned m3 S (S + zlen bl)).
  { destruct (Z.eq_dec (zlen bl) 0) as [Z0|NZ]; [rewrite Z0, Z.add_0_r; apply unpoisoned_nil; lia|].
    eapply (hcoverA_unpoisoned AI L RNG st (FB2 FF :: LB) m3 S (zlen bl) AH3); [apply hcoverA_cons_fake; exact HC| lia]. }
  assert (STL3 : stk asegs m3 lo (SPAz SPV))
    by (eapply stk_transport; [exact ST2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
  assert (STG3 : stk asegs m3 (SPAz SPV + 56) (SPV + -104))
    by (eapply stk_transport; [exact STG2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
  clear MG2 FRB2 FRA2 STG2 ST2 MI2 FFC2 SHF2 RR2 RU2 GSH2 PL2.
  (* [comment removed for export] *)
  unfold FFHDR in FFC3.
  lazymatch type of FFC3 with rw_cells _ _ _ ([?h0; ?h1; ?h2] ++ [CB 224 junk; ?fl]) =>
    change ([h0; h1; h2] ++ [CB 224 junk; fl]) with ([h0; h1; h2] ++ [CB 224 junk] ++ [fl]) in FFC3 end.
  apply (proj1 (rw_cells_appA _ _ _ _ _)) in FFC3. destruct FFC3 as [FF03 FFC3]. cbn [cells_size csize Nat.add] in FFC3.
  apply (proj1 (rw_cells_appA _ _ _ _ _)) in FFC3. destruct FFC3 as [FJ3 FF2483]. cbn [cells_size csize Nat.add] in FF2483.
  replace (FF + Z.of_nat 24 + Z.of_nat 224) with (FF + 248) in FF2483 by lia. replace (FF + Z.of_nat 24) with (FF + 24) in FJ3 by lia.
  apply (rw_cells_split_CB asegs m3 _ [] 224 junk [] [8; 48; 32; 4; 4; 4; 4; 120]%nat) in FJ3; [| reflexivity]. cbn [app mk_CB_cells] in FJ3.
  lazymatch type of FJ3 with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7] =>
    apply (proj1 (rw_cells_appA _ m3 _ [c0] [c1; c2; c3; c4; c5; c6; c7])) in FJ3; destruct FJ3 as [_ FZ3]; cbn [cells_size csize Nat.add] in FZ3;
    apply (proj1 (rw_cells_appA _ m3 _ [c1] [c2; c3; c4; c5; c6; c7])) in FZ3; destruct FZ3 as [FZ3 FJb]; cbn [cells_size csize Nat.add] in FJb;
    apply (proj1 (rw_cells_appA _ m3 _ [c2] [c3; c4; c5; c6; c7])) in FJb; destruct FJb as [_ BP3]; cbn [cells_size csize Nat.add] in BP3;
    apply (proj1 (rw_cells_appA _ m3 _ [c3; c4; c5] [c6; c7])) in BP3; destruct BP3 as [BP3 _] end.
  replace (FF + 24 + Z.of_nat 8) with (FF + 32) in FZ3, BP3 by lia.
  replace (FF + 32 + Z.of_nat 48) with (FF + 80) in BP3 by lia. replace (FF + 80 + Z.of_nat 32) with (FF + 112) in BP3 by lia.
  unfold FFHDR in FF03 |- *.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply ffsi_disp with (lo := lo) (D := D) (N := N) (r0 := r0) (r1 := r1) (r2 := r2).
    all: try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
    all: try (unfold KEND; lia).
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (unfold AFI_STACK; lia).
    all: try (rewrite <- ESH; exact RSFF). }
  cbv beta. intros ms' [GF|SK].
  - (* [comment removed for export] *)
    destruct GF as (y14 & m4 & -> & MU4 & WM4 & MI4 & SHF4 & RR4 & FF04). unfold WD in MU4.
    assert (AH4 : AHEAP AI L RNG st (FB2 FF :: LB) m4).
    { eapply (AI_frame AI); [exact AH3| exact MU4| exact WM4|].
      constructor; [cbn; left; left; lia|].
      constructor; [cbn; right; left; exists (FB2 FF); split; [left; reflexivity| cbn; lia]|].
      constructor; [cbn; right; right; right; right; exists 2, FF, 256; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                    change (2 ^ 3) with 8; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]| constructor]. }
    assert (MG4 : magree asegs (fun a => aclient_addr CI LB SPV a /\ ~ (R <= a < R + 24)) m m4).
    { eapply magree_munch_step; [exact MG3| exact MU4| exact WM4|]. intros a [Ha Hn]. cbn.
      split; [intros Hr; exact (Hn Hr)|]. split; [intros Hr; exact (NCF a ltac:(lia) Ha)|]. split; [intros Hr; exact (NCH a ltac:(lia) Ha)| exact I]. }
    pose proof (rw_cells_transport _ _ _ _ _ _ FRB3 MU4 WM4 ltac:(cbn; lia)) as FRB4.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRA3 MU4 WM4 ltac:(cbn; lia)) as FRA4.
    pose proof (rw_cells_transport _ _ _ _ _ _ FZ3 MU4 WM4 ltac:(cbn; lia)) as FZ4.
    pose proof (rw_cells_transport _ _ _ _ _ _ BP3 MU4 WM4 ltac:(cbn; lia)) as BP4.
    pose proof (rw_cells_transport _ _ _ _ _ _ FF2483 MU4 WM4 ltac:(cbn; lia)) as FF2484.
    assert (GSH4 : gshA m4).
    { unfold harness_invA, GSH_ADDR in *. eapply rw_cells_transport; [exact GSH3| exact MU4| exact WM4|]. cbn. lia. }
    assert (RU4 : unpoisoned m4 R (R + 24)).
    { eapply unpoisoned_munch; [exact RU3| exact MU4|]. rewrite !shad_div, ?Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2^3) with 8. cbn [disjoint_from].
      clear - ATR SPAB LO BOT RLO RHI' LY3 FHb FHc FHu. repeat split; try exact I; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    assert (PL4 : bytes_at asegs m4 S (map (Z_to_bv 8) bl)).
    { destruct (Z.eq_dec (zlen bl) 0) as [Z0|NZ].
      - assert (E : bl = []) by (destruct bl; [reflexivity| cbn in Z0; lia]). rewrite E in PL3 |- *. exact (bytes_at_nil_any m3 m4 S PL3).
      - destruct (PAY ltac:(lia)) as (DS & SN & NN & DH & D16 & RGA & RGS & SEPF). pose proof (ablk_lin _ _ DH) as (DHa & DHb & DHc & DHd).
        pose proof DH as DHu. unfold ablk, AIMG_HI, KLS in DHu.
        eapply bytes_at_transport; [exact PL3| exact MU4|]. rewrite length_map. cbn [disjoint_from]. clear - DS SN DHu DHb DHc BSF SPAB LO BOT ATR SEPF FHb RLO. repeat split; try exact I; lia. }
    assert (STL4 : stk asegs m4 lo (SPAz SPV))
      by (eapply stk_transport; [exact STL3| exact MU4| exact WM4| intros x Hx; left; cbn; lia]).
    assert (STG4 : stk asegs m4 (SPAz SPV + 56) (SPV + -104))
      by (eapply stk_transport; [exact STG3| exact MU4| exact WM4| intros x Hx; left; cbn; lia]).
    (* [comment removed for export] *)
    assert (SHZ4 : rw_cells asegs m4 (Z.shiftr (FF + 32) 3 + 2147450880) (repeat (C1 (Z_to_bv 8 0)) 6)).
    { unfold FSH2, FSHZ in SHF4. cbn [app] in SHF4.
      lazymatch type of SHF4 with rw_cells _ _ _ (?a :: ?b :: ?c :: ?d :: ?e0 :: ?e1 :: ?e2 :: ?e3 :: ?e4 :: ?e5 :: ?rest) =>
        change (a :: b :: c :: d :: e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: rest) with ([a; b; c; d] ++ [e0; e1; e2; e3; e4; e5] ++ rest) in SHF4 end.
      pose proof (proj1 (rw_cells_appA _ _ _ _ _) SHF4) as [_ X]. apply (proj1 (rw_cells_appA _ _ _ _ _)) in X. destruct X as [X _].
      cbn [cells_size csize Nat.add] in X.
      replace (Z.shiftr (FF + 32) 3 + 2147450880) with (Z.shiftr FF 3 + 2147450880 + Z.of_nat 4); [exact X|].
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear - F256. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    (* [comment removed for export] *)
    eapply evtF_cut.
    { pose proof GFHA as G. unfold gfhaA_stmt, gfhaA_stmt_at in G.
      eapply (G L RNG (Z_to_bv 64 0x8178c) (SPAz SPV)) with (lo := lo) (S := S) (bl := bl) (ZF := FF + 32); clear G.
      - exact AH4.
      - apply fake_lek_push; [intros F' n' E; discriminate E| exact LE0].
      - exact LBH3.
      - split; [exact PL4| exact PLR].
      - exact NB.
      - apply hcoverA_cons_fake. exact HC.
      - exact FZ4.
      - split.
        + exists 2, FF, 256. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [exact FH| clear - F256; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
        + replace (FF + 32 + 48) with ((FF + 32) + 8 * Z.of_nat 6) by lia. apply (c1z_cells_unpoisoned 6 m4 (FF + 32) SHZ4); [clear - F256; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| lia|].
          unfold KEND in *. lia.
      - clear - F256. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      - exists 2, FF, 256. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [clear - F256; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia|]. split; [reflexivity|].
        split; [lia|]. split; [unfold KEND in *; lia|]. change (256 / 8) with 32. split; [rewrite ESH; exact (proj2 SHF4)| exact RSFF].
      - exact GSH4.
      - exact STL4.
      - exact BOT.
      - unfold AFI_STACK. lia.
      - lia.
      - pose proof (spa160_propsA SPV SP16) as (_ & SPA32 & _). clear - SPA32. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      - exact MI4.
      - exact TP.
      - exact RSTK.
      - exact RI.
      - exact RIS.
      - exact RFS.
      - eapply rng_sub'; [exact RFF| lia].
      - eapply rng_sub'; [exact RSFF|]. rewrite !shad_div. clear - FHb. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity. }
    cbv beta. intros ms' PO. unfold gfhaA_post in PO.
    destruct PO as (r & y5 & y6 & y7 & y11 & y12 & y13 & y14' & y15 & y16 & y17 & y28 & y29 & y30 & y31 & zj1 & hb & zj2 & m5
                    & -> & MI5 & ST5 & MG5 & AH5 & ZFH5 & RF5).
    (* [comment removed for export] *)
    destruct (FFLAG _ _ _ _ _ _ _ _ AH5 ltac:(left; reflexivity)) as (FLC5 & RG & GH & GC & GBL & GCI).
    pose proof (GBL _ ltac:(left; reflexivity)) as GF. cbn [ab_addr ab_size] in GF.
    pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in GHa.
    assert (CLF : forall a, FF <= a < FF + 256 -> ~ (FF + 32 <= a < FF + 32 + 48) -> aclient_addr CI (FB2 FF :: LB) (SPAz SPV) a /\ ~ (FF + 32 <= a < FF + 32 + 48)).
    { intros a Ha Hn. split; [| exact Hn]. apply (cl_block CI (FB2 FF :: LB) (SPAz SPV) (FB2 FF) a ltac:(left; reflexivity)). cbn. lia. }
    assert (CLS : forall a, SPAz SPV <= a < 2^47 -> aclient_addr CI (FB2 FF :: LB) (SPAz SPV) a /\ ~ (FF + 32 <= a < FF + 32 + 48)).
    { intros a Ha. split; [apply cl_stack; lia| lia]. }
    assert (SHF5 : rw_cells asegs m5 (Z.shiftr FF 3 + 2147450880) FSH2).
    { eapply rw_cells_magree; [exact MG5| exact SHF4|]. unfold FSH2, FSHZ. cbn [cells_size csize Nat.add length app]. intros a Ha. split; [| lia].
      right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
      right; right. exists 2, FF, 256. split; [left; reflexivity|]. rewrite Z.shiftr_div_pow2 in Ha by lia. change (2^3) with 8 in Ha.
      unfold ASHOFF. clear - Ha FHb F256. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    assert (FF05 : rw_cells asegs m5 FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1a436); C8 (Z_to_bv 64 0x814a0)]).
    { eapply rw_cells_magree; [exact MG5| exact FF04|]. cbn [cells_size csize Nat.add]. intros a Ha. apply CLF; lia. }
    lazymatch type of BP4 with rw_cells _ _ _ ?bpc =>
      assert (BP5 : rw_cells asegs m5 (FF + 112) bpc)
        by (eapply rw_cells_magree; [exact MG5| exact BP4|]; cbn [cells_size csize Nat.add]; intros a Ha; apply CLF; lia) end.
    assert (FF2485 : rw_cells asegs m5 (FF + 248) [C8 (Z_to_bv 64 (fflag L 2 FF))]).
    { eapply rw_cells_magree; [exact MG5| exact FF2484|]. cbn [cells_size csize Nat.add]. intros a Ha. apply CLF; lia. }
    assert (FRB5 : rw_cells asegs m5 (SPV + -104) (FFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { eapply rw_cells_magree; [exact MG5| exact FRB4|]. unfold FFRB. cbn [cells_size csize Nat.add length]. intros a Ha. apply CLS. lia. }
    assert (FRA5 : rw_cells asegs m5 (SPAz SPV) [CB 48 j48; C8 (Z_to_bv 64 FF)]).
    { eapply rw_cells_magree; [exact MG5| exact FRA4|]. cbn [cells_size csize Nat.add]. intros a Ha. apply CLS. lia. }
    assert (RR5 : rw_cells asegs m5 R [CB 8 r0; CB 8 r1; CB 8 r2]).
    { eapply rw_cells_magree; [exact MG5| exact RR4|]. cbn [cells_size csize Nat.add]. intros a Ha. apply CLS. lia. }
    assert (STG5 : stk asegs m5 (SPAz SPV + 56) (SPV + -104)).
    { eapply stk_magree; [exact MG5| exact STG4|]. intros a Ha. apply CLS. lia. }
    assert (GSH5 : gshA m5) by (eapply gshA_mg; [exact MG5| intros a Ha; split; [exact (gsh_client CI _ (SPAz SPV) a GIMG Ha)| lia]| exact GSH4]).
    assert (RU5 : unpoisoned m5 R (R + 24)).
    { eapply (unpoisoned_mgA _ m4 m5); [exact MG5| exact RU4|]. intros s Hs. rewrite !shad_div in Hs. unfold ASHOFF in Hs.
      split; [OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia|]. split; [| OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
      right; right; right. exists (8 * (s - ASHOFF)). split; [| symmetry; apply shad_unshad]. left. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    assert (PL5 : bytes_at asegs m5 S (map (Z_to_bv 8) bl)).
    { destruct (Z.eq_dec (zlen bl) 0) as [Z0|NZ].
      - assert (E : bl = []) by (destruct bl; [reflexivity| cbn in Z0; lia]). rewrite E in PL4 |- *. exact (bytes_at_nil_any m4 m5 S PL4).
      - destruct (PAYB ltac:(lia)) as (p & Hin & D1 & D2). pose proof (FFD _ Hin) as FD. cbn in FD.
        eapply bytes_at_magree; [exact MG5| exact PL4|]. rewrite length_map. intros a Ha.
        split; [apply (cl_block CI (FB2 FF :: LB) (SPAz SPV) (HB p D N) a ltac:(right; exact Hin)); cbn; lia| lia]. }
    assert (UNP5 : unpoisoned m5 S (S + zlen bl)).
    { destruct (Z.eq_dec (zlen bl) 0) as [Z0|NZ]; [rewrite Z0, Z.add_0_r; apply unpoisoned_nil; lia|].
      eapply (hcoverA_unpoisoned AI L RNG st (FB2 FF :: LB) m5 S (zlen bl) AH5); [apply hcoverA_cons_fake; exact HC| lia]. }
    pose proof (AI_rtcells AI _ _ _ _ _ AH5) as RTC. unfold artcells in RTC. destruct RTC as (_ & GOT5 & _ & _ & SHB5 & _).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply ffsi_gret with (lo := lo) (D := D) (N := N) (FLG := fflag L 2 FF) (r0 := r0) (r1 := r1) (r2 := r2);
        try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
      all: try (unfold core, W5; repeat match goal with |- _ /\ _ => split end; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; first [apply munch_refl | apply wmono_refl]).
      all: try (unfold KEND; lia).
      all: try (eapply rng_sub'; [exact RSTK| lia]).
      all: try (unfold AFI_STACK; lia).
      all: try (rewrite <- ESH; exact RSFF). }
    cbv beta. intros ms' PJ. unfold POST_J in PJ.
    destruct PJ as (w1 & w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w19 & w20 & w21 & w22 & w23 & w24 & w28 & w29 & w30 & w31
                    & cl & nb & cs & db & m6 & -> & C6 & STL6 & FRA6 & CL6 & SHF6 & FF06 & RR6 & CS6).
    destruct C6 as (FRB6 & FF2486 & GOT6 & SHB6 & STG6 & MU6 & WM6 & MI6). unfold W5 in MU6.
    assert (AH6 : AHEAP AI L RNG st (FB2 FF :: LB) m6).
    { eapply (AI_frame AI); [exact AH5| exact MU6| exact WM6|].
      constructor; [cbn; left; left; lia|].
      constructor; [cbn; left; left; lia|].
      constructor; [cbn; right; left; exists (FB2 FF); split; [left; reflexivity| cbn; lia]|].
      constructor; [cbn; right; right; right; right; exists 2, FF, 256; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                    change (2 ^ 3) with 8; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]|].
      constructor; [cbn; right; right; right; right; exists 2, FF, 256; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                    change (2 ^ 3) with 8; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]|].
      constructor; [cbn; left; left; lia|].
      constructor; [cbn; right; left; exists (FB2 FF); split; [left; reflexivity| cbn; lia]| constructor]. }
    pose proof GH as GHu. unfold ablk, AIMG_HI, KLS in GHu.
    pose proof (rw_cells_transport _ _ _ _ _ _ FLC5 MU6 WM6 ltac:(cbn; clear - GF GHb GHc GHu BSF SPAB LO BOT ATR RLO FHb FHc; repeat split; try exact I; lia)) as FLC6.
    assert (MG6 : magree asegs (fun a => aclient_addr CI LB SPV a /\ ~ (R <= a < R + 24)) m m6).
    { assert (MG5' : magree asegs (fun a => aclient_addr CI LB SPV a /\ ~ (R <= a < R + 24)) m m5).
      { eapply magree_trans; [exact MG4|]. eapply magree_mono; [exact MG5|]. intros a [Ha Hn]. split.
        - eapply aca_monoA; [exact Ha| intros b Hb; right; exact Hb| lia].
        - intros Hr. exact (NCF a ltac:(lia) Ha). }
      eapply magree_munch_step; [exact MG5'| exact MU6| exact WM6|]. intros a [Ha Hn]. cbn.
      split; [intros Hr; exact (NCS a (SPAz SPV - 16) ltac:(lia) ltac:(lia) Ha)|].
      split; [intros Hr; exact (NCS a (SPAz SPV + 16) ltac:(lia) ltac:(lia) Ha)|].
      split; [intros Hr; exact (NCF a ltac:(lia) Ha)|].
      split; [intros Hr; exact (NCH a ltac:(lia) Ha)|].
      split; [intros Hr; exact (NCH a ltac:(lia) Ha)|].
      split; [intros Hr; exact (Hn Hr)|].
      split; [intros Hr; exact (NCF a ltac:(lia) Ha)| exact I]. }
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply ffsi_release with (lo := lo) (FLG := fflag L 2 FF); try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
      all: try (unfold KEND; lia).
      all: try (eapply rng_sub'; [exact RSTK| lia]).
      all: try (unfold AFI_STACK; lia).
      all: try (rewrite <- ESH; exact RSFF). }
    cbv beta. intros ms' (mp & m7 & -> & MU7 & WM7 & MIp & MU8 & WM8 & MI7 & ST7 & FLC7).
    assert (AHp : AHEAP AI L RNG st (FB2 FF :: LB) mp).
    { eapply (AI_frame AI); [exact AH6| exact MU7| exact WM7|].
      constructor; [| constructor]. cbn. right; right. right; right. exists 2, FF, 256. split; [left; reflexivity|].
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    pose proof (FREL _ _ _ _ _ _ _ _ AHp) as AHr.
    assert (AH7 : AHEAP AI L RNG st LB m7).
    { eapply aheap_eqA; [exact AHr|].
      apply (mem_eq_singleA mp m7 (fflag L 2 FF) (Z_to_bv 8 0)); [lia| lia| exact MU8| apply byte_of_c1A; [exact FLC7| lia]]. }
    pose proof (rw_cells_transport _ _ _ _ _ _ RR6 MU7 WM7 ltac:(cbn; lia)) as RRp.
    pose proof (rw_cells_transport _ _ _ _ _ _ RRp MU8 WM8 ltac:(cbn; lia)) as RR7.
    apply evtF_done. unfold ffsiA_post. do 15 eexists. exists nb, cs, db, m7. split; [reflexivity|].
    split; [exact MI7|]. split; [exact ST7|].
    split.
    { eapply magree_munch_step; [| exact MU8| exact WM8|].
      - eapply magree_munch_step; [exact MG6| exact MU7| exact WM7|]. intros a [Ha _]. cbn. split; [intros Hr; exact (NCH a ltac:(lia) Ha)| exact I].
      - intros a [Ha _]. cbn. split; [| exact I].
        intros Hr. refine (app_not_client CI LB SPV (fflag L 2 FF) 1 a HCI HCI0 GH ltac:(lia) LBH _ ltac:(lia) Ha).
        intros b Hb. exact (GBL b (or_intror Hb)). }
    split; [exact AH7|]. split; [exact RR7| exact CS6].
  - (* [comment removed for export] *)
    destruct SK as (y10 & y11 & y12 & y13 & y14 & cs & m4 & -> & MU4 & WM4 & MI4 & SHF4 & RR4 & FF04 & CS4). unfold WD in MU4.
    assert (AH4 : AHEAP AI L RNG st (FB2 FF :: LB) m4).
    { eapply (AI_frame AI); [exact AH3| exact MU4| exact WM4|].
      constructor; [cbn; left; left; lia|].
      constructor; [cbn; right; left; exists (FB2 FF); split; [left; reflexivity| cbn; lia]|].
      constructor; [cbn; right; right; right; right; exists 2, FF, 256; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                    change (2 ^ 3) with 8; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]| constructor]. }
    assert (MG4 : magree asegs (fun a => aclient_addr CI LB SPV a /\ ~ (R <= a < R + 24)) m m4).
    { eapply magree_munch_step; [exact MG3| exact MU4| exact WM4|]. intros a [Ha Hn]. cbn.
      split; [intros Hr; exact (Hn Hr)|]. split; [intros Hr; exact (NCF a ltac:(lia) Ha)|]. split; [intros Hr; exact (NCH a ltac:(lia) Ha)| exact I]. }
    pose proof (rw_cells_transport _ _ _ _ _ _ FRB3 MU4 WM4 ltac:(cbn; lia)) as FRB4.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRA3 MU4 WM4 ltac:(cbn; lia)) as FRA4.
    pose proof (rw_cells_transport _ _ _ _ _ _ FF2483 MU4 WM4 ltac:(cbn; lia)) as FF2484.
    assert (STL4 : stk asegs m4 lo (SPAz SPV))
      by (eapply stk_transport; [exact STL3| exact MU4| exact WM4| intros x Hx; left; cbn; lia]).
    assert (STG4 : stk asegs m4 (SPAz SPV + 56) (SPV + -104))
      by (eapply stk_transport; [exact STG3| exact MU4| exact WM4| intros x Hx; left; cbn; lia]).
    destruct (FFLAG _ _ _ _ _ _ _ _ AH4 ltac:(left; reflexivity)) as (FLC4 & RG & GH & GC & GBL & GCI).
    pose proof (GBL _ ltac:(left; reflexivity)) as GF. cbn [ab_addr ab_size] in GF.
    pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in GHa.
    eapply evtF_cut.
    { eapply ffsi_release with (lo := lo) (FLG := fflag L 2 FF) (cl := [CB 48 j48; C8 (Z_to_bv 64 FF)]);
        try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
      all: try reflexivity.
      all: try (unfold KEND; lia).
      all: try (eapply rng_sub'; [exact RSTK| lia]).
      all: try (unfold AFI_STACK; lia).
      all: try (rewrite <- ESH; exact RSFF). }
    cbv beta. intros ms' (mp & m7 & -> & MU7 & WM7 & MIp & MU8 & WM8 & MI7 & ST7 & FLC7).
    assert (AHp : AHEAP AI L RNG st (FB2 FF :: LB) mp).
    { eapply (AI_frame AI); [exact AH4| exact MU7| exact WM7|].
      constructor; [| constructor]. cbn. right; right. right; right. exists 2, FF, 256. split; [left; reflexivity|].
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    pose proof (FREL _ _ _ _ _ _ _ _ AHp) as AHr.
    assert (AH7 : AHEAP AI L RNG st LB m7).
    { eapply aheap_eqA; [exact AHr|].
      apply (mem_eq_singleA mp m7 (fflag L 2 FF) (Z_to_bv 8 0)); [lia| lia| exact MU8| apply byte_of_c1A; [exact FLC7| lia]]. }
    pose proof (rw_cells_transport _ _ _ _ _ _ RR4 MU7 WM7 ltac:(cbn; lia)) as RRp.
    pose proof (rw_cells_transport _ _ _ _ _ _ RRp MU8 WM8 ltac:(cbn; lia)) as RR7.
    apply evtF_done. unfold ffsiA_post. do 15 eexists. exists (le8 (Z_to_bv 64 0)), cs, (Z_to_bv 64 0), m7. split; [reflexivity|].
    split; [exact MI7|]. split; [exact ST7|].
    split.
    { eapply magree_munch_step; [| exact MU8| exact WM8|].
      - eapply magree_munch_step; [exact MG4| exact MU7| exact WM7|]. intros a [Ha _]. cbn. split; [intros Hr; exact (NCH a ltac:(lia) Ha)| exact I].
      - intros a [Ha _]. cbn. split; [| exact I].
        intros Hr. refine (app_not_client CI LB SPV (fflag L 2 FF) 1 a HCI HCI0 GH ltac:(lia) LBH _ ltac:(lia) Ha).
        intros b Hb. exact (GBL b (or_intror Hb)). }
    split; [exact AH7|]. split; [| exact CS4].
    eapply rw_cells_recast; [exact RR7| cbn; repeat split; reflexivity| cbn [cells_bytes cbytes app]; reflexivity| reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Asm.
End CANSEC1.
