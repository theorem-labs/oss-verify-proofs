(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun Stdio_pure.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg RtCells ShadowTac F_rip F_tryinit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

Ltac iprem :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- mem_inv _ _ => first [assumption | eassumption]
  | |- context [bv_unsigned (Z_to_bv 64 _)] => rewrite !unsigned_lit by lia; iprem
  | |- stk _ _ _ _ => first [assumption | eassumption]
  | |- rw_cells _ _ _ _ => rewrite ?Z_to_bv_bv_unsigned; first [assumption | eassumption]
  | |- shadow_bytes _ _ _ _ => first [assumption | eassumption]
  | |- bytes_at _ _ _ _ => first [assumption | eassumption]
  | |- unpoisoned _ _ _ => first [assumption | eassumption]
  | |- wr_at _ _ _ _ => first [assumption | eassumption]
  | |- app_blk _ _ => first [assumption | eassumption]
  | |- Forall _ _ => first [assumption | eassumption]
  | |- _ = Z_to_bv 64 _ => first [reflexivity | assumption | symmetry; assumption]
  | |- rng _ _ _ => first [ assumption | match goal with H : rng _ _ _ |- _ => eapply rng_sub'; [exact H | unfold KHIGH, sf_hide in *; lia] end ]
  | |- _ => unfold KHIGH, sf_hide in *; first [assumption | lia]
  end.

(* [comment removed for export] *)
Notation rt_real_fwrite m := (rw_cells asegs m 0x9ab98 [C8 (Z_to_bv 64 0x8e71c)]).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition fwrite_i_mid (ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x14 x15 x16 x17 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x436a0) (Z_to_bv 64 (bv_unsigned sp - 2128)) gp tp t0 t1 t2
                  sp a1 a0 a1 a2 a3 x14 x15 x16 x17
                  a0 a3 a2 (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x8e71c) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 2128) /\ stk asegs m' (bv_unsigned sp - 2128) (bv_unsigned sp - 56)
    /\ rw_cells asegs m' (bv_unsigned sp - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rt_inited m'.

Section FWRITE_PRE.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2144)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis INI : rt_inited m.
  Hypothesis RFW : rt_real_fwrite m.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).

  #[using="MI ST LO KLO INI RFW RI RSTK"] Lemma fwrite_i_pre :
    evtF asegs RNG (fwrite_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x43644) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    Local Ltac2 Set LiaHints.tbl := fun () => "0180>10943906301.8011799361125.6711799361125.6811799361125.6911799361125.7011801586693.8013078519495.6613105819609.8513169897334.8315104381976.6815549531456.66162492479.58  16522670308.6517288173208.6917305236855.661889508528.66 19042827563.671978529996.67 19943966000.6421568524992.6822284289799.8023077509607.6827147338155.6827571003456.6727800433132.6928072922155.6829777070360.6830232449436.6630748752228.6531142837991.6431161366443.6632149979666.5833320343373.5633588399552.6533762705944.6834237182816.733496372800.66 36986663037.8037062796780.6938540920586.4939298714725.6639480921372.6541297676312.6941914676071.634203475740.66 43055122908.5444484923210.8046235924760.6846568687280.6546970229916.6747651094424.6747700500248.6949921929014.6251188481948.6451896122520.6752230632470.7654549504864.7354553403622.5655890146712.7056172315833.5856185171996.6558604970416.6558672299160.7061323238887.6463984287584.7364623284016.6665212743211.6765317030500.6567715076504.697941138992.67 8603416747.69 9515366336.67 00000<00=00>00?00@00E00F00G00H00P00T00X00Y00a00b00c00h00l00m01101201701<01@01H01M01U01V01W01X01]01^01b01f01n01o02302?02G02K02L02M02U02V02W02[02\02d02e02f02n03603@03A03I03J03K03L03T03U03V03W03_03`03a03b03g03h04004104604:S2LO3KLO3HspSSSSS3HspSSSS2LO3KLOS2HBS2LOSS2LO3KLOSSS3SPRS2HBSS2HBFS3SPRS3SPRS2HBS2LO3KLOS3SPRS2LO3KLOSSSS3SPRFS2LOS2HBS2LO3KLOSS2HBS2LO3KLO3HspS2LO3KLOS2LOSSS2LO3KLOSSS2LOFS2LO3KLOSSS2LO3KLOS2LO3KLOS3SPR1H2H0SS2LO3KLOSSSS2LO3KLOSSSS2LO3KLOSSSS3SPRSS2LO3KLOSS3SPRS2HB".
assert (RSTK' : rng RNG (bv_unsigned sp + -2144) 2144) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0. pose proof INI as INIc. pose proof RFW as RFWc.
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in RFW.
    carve_frame 56%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2128) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    do 14 zstep. zstep.
    call_sp tryinit_spec. all: iprem.
    do 7 zstep. zstep.
    apply evtF_done. unfold fwrite_i_mid.
    replace (bv_unsigned sp - 2128)%Z with (bv_unsigned sp + -2128)%Z by lia.
    replace (bv_unsigned sp - 56)%Z with (bv_unsigned sp + -56)%Z by lia.
    replace (bv_unsigned sp - 2144)%Z with (bv_unsigned sp + -2144)%Z by lia.
    do 12 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End FWRITE_PRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fwrite_i_post_post (sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rav s0v s1v s2v s3v s4v s5v : word) (res lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp - 2128)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Section FWRITE_POST.
  Variables (RNG : footprint)
            (x1 sp gp tp t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7 p x19 x20 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (rav s0v s1v s2v s3v s4v s5v : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo res size N : Z) (RLO RHI : Z).
  Notation P := (bv_unsigned p).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp - 2128).
  Hypothesis STM : stk asegs m (bv_unsigned sp - 2128) (bv_unsigned sp - 56).
  Hypothesis FR : rw_cells asegs m (bv_unsigned sp - 56) [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].
  Hypothesis LO : (lo <= bv_unsigned sp - 2208)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis LAY : rt_layout m.
  Hypothesis X9 : x9 = Z_to_bv 64 size.
  Hypothesis HN : (res * size)%Z = N.
  Hypothesis RES : (0 <= res < 2^64 /\ 1 <= size /\ 0 <= N <= 2^40)%Z.
  Hypothesis APP : app_blk P (P + N).
  Hypothesis UNP : unpoisoned m P (P + N).
  Hypothesis R1 : (RLO <= P /\ P + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at asegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).

  Notation POST := (fwrite_i_post_post sp gp tp s6 s7 s8 s9 s10 s11 F fc rav s0v s1v s2v s3v s4v s5v res lo m).

  Definition INV (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -56) [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
    /\ stk asegs mc lo (bv_unsigned sp + -2128) /\ stk asegs mc (bv_unsigned sp + -2128) (bv_unsigned sp + -56)
    /\ munch [(bv_unsigned sp + -2208, bv_unsigned sp + -2128)]%Z m mc /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc P (P + N) /\ wr_at asegs mc (shad RLO) (shad RHI - shad RLO).

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64 /\ 0 <= N /\ N <= 2^40 /\ 0 <= res < 2^64
     /\ 0 <= P /\ P + N + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad P /\ shad (P + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr P 3 < 2^44 /\ -1 <= Z.shiftr (P + N + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= P /\ P + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
  #[using="m size ST LO KLO HN RES APP R1"] Lemma BND_ok : BND.
  Proof.
    unfold BND. destruct ST as (L0 & _). destruct APP as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range 64 p) as PR. unfold bv_modulus in PR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in PR.
    Local Ltac2 Set LiaHints.tbl := fun () => "0020>29784593404.7062898324748.7000000100JSS2LO3KLO2HN3RES2R12AS3SPR".
rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64 /\ 0 <= N /\ N <= 2^40 /\ 0 <= res < 2^64
     /\ 0 <= P /\ P + N + 8 <= 2^47
     /\ 0 <= Z.shiftr P 3 < 2^44 /\ -1 <= Z.shiftr (P + N + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad P /\ shad (P + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
  #[using="m size ST LO KLO HN RES APP R1"] Lemma BL_ok : BL. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BL. Local Ltac2 Set LiaHints.tbl := fun () => "0010>62904913180.6600000:S2LO3RES1B".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Ltac inv_open H := destruct H as (FR1 & ST1 & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNP1 & WR11).
  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let B := fresh "BL" in pose proof BL_ok as B; unfold BL in B;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]);
    change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in STM;
    change (?P) with (sf_hide P) in FR; change (?P) with (sf_hide P) in GOT; change (?P) with (sf_hide P) in SHB;
    change (?P) with (sf_hide P) in LAY; change (?P) with (sf_hide P) in UNP; change (?P) with (sf_hide P) in WR1.

  #[using="res size ST LO KLO HN RES APP UNP R1 WR1"] Lemma inv_of : forall mc,
    rw_cells asegs mc (bv_unsigned sp + -56) [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
    stk asegs mc lo (bv_unsigned sp + -2128) -> stk asegs mc (bv_unsigned sp + -2128) (bv_unsigned sp + -56) ->
    munch [(bv_unsigned sp + -2208, bv_unsigned sp + -2128)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_shbase mc -> rt_layout mc -> INV mc.
  Proof.
    intros mc FR1 ST1 STM1 MU1 WM1 MI1 G1 G2 G3. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
    repeat (split; [assumption|]).
    Local Ltac2 Set LiaHints.tbl := fun () => "0020>11805731844.7733476969212.76000006009S2R11BS1B".
assert (SS : (shad (P + N - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    split. { eapply unpoisoned_munch; [exact UNP | exact MU1 |]. cbn [disjoint_from]. lia. }
    eapply wr_at_transport; eassumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Notation FWR pc x10 x11 x12 x13 x14 x15 mc :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp (Z_to_bv 64 N) x10 x11 x12 x13 x14 x15 a6 a7
             p x19 (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mc (seg_rom asegs)) (only parsing).

  (* [comment removed for export] *)
  #[using="size ST LO KLO HN RES APP R1 RSTK"] Lemma LX : forall mc x1' x5 x6 x7 x9' x11 x12 x13 x14 x15 x16 x17 x20' x21' x28 x29 x30 x31, INV mc ->
    evtF asegs RNG POST
      (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9' (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17
               p x19 x20' x21' s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x43704) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "00D0?17305236855.10617676671814.1001807322596.105 21879957789.99 22437836862.10030232449436.10633334826102.98 34230845254.1003602932068.105 39480921372.1054203475740.106 46703417572.10546970229916.10750221378407.10451188481948.10552415237221.10656185171996.10663123389028.1056922740008.97  7944451815.104 00000100200300800900:00?00@00A00B00C00D00E00F00G00H00I00J00N00OSSSS3BL0SSS3BL0SSSSSSSSSSSS2LOS".
prep IV.
    do 10 zstep.
    pose proof (stk_merge _ _ _ _ _ ST1 STM1 ltac:(lia)) as SK.
    pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
    replace (bv_unsigned sp + -56 + Z.of_nat 56)%Z with (bv_unsigned sp) in SK2 by lia.
    apply evtF_done. unfold fwrite_i_post_post.
    replace (bv_unsigned sp - 2208)%Z with (bv_unsigned sp + -2208)%Z by lia.
    replace (bv_unsigned sp - 2128)%Z with (bv_unsigned sp + -2128)%Z by lia.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="size ST LO KLO HN RES APP R1 RSTK RSH1"] Lemma LL : forall mc (k : nat) (c : Z) x14 x15,
    INV mc -> (1 <= N <= 64)%Z -> Z.to_nat (shad (P + N - 1) - c) = k -> (shad P <= c < shad (P + N - 1))%Z ->
    evtF asegs RNG POST (FWR 0x437c8 (Z_to_bv 64 res) (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (P + N + -1) 3)) (Z_to_bv 64 0) x14 x15 mc).
  Proof.
    intros mc k c x14 x15 IV N1 Hk Hc. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>13714642969.9113739240004.9118196179457.8924122881917.9128793935657.8944092989942.9859308585478.8659308627018.1 60890567713.9164507443218.986922740008.86 00000700D00K00S00Z00[00b00f01401?01FS2Hk2HcS2Hk2Hc2SL2K1S2Hk2HcS3BL02HkS2Hk2HcFS2Hk2HcS2K'S3BL02Hk2Hc2SLS3BL02Hk2HcS2LO2Hk".
prep IV.
    revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (P + N - 1) = 2147450880 + Z.shiftr (P + N + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc P (P + N) c UNP1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; eassumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="size ST LO KLO HN RES APP R1 RSTK RSH1"] Lemma LE : forall mc x14 x15, INV mc -> (1 <= N <= 64)%Z ->
    evtF asegs RNG POST (FWR 0x437ac (Z_to_bv 64 res) (Z_to_bv 64 (2147450880 + Z.shiftr P 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (P + N + -1) 3))
                             (Z_to_bv 64 (P + N + -1)) x14 x15 mc).
  Proof.
    intros mc x14 x15 IV N1. Local Ltac2 Set LiaHints.tbl := fun () => "00B0>19482125347.9824122881528.8824991237561.9829782203372.9629784416728.8830507626521.8331904842358.833421727977.88 37100885899.9643614754995.8352076332689.9452274034272.8352523015483.9653510313881.9856209684249.8759308629082.1 67298533313.876922740008.82 00000500:00;00<00=00>00B00F00L00M00U00V00W00X00Y00]00b00fS3CK2S3BL0SSSSS2N1S2K6S2N11BSS2N13BL0SSSSS2K7S3CK2S2LO".
prep IV.
    destruct (unpoisoned_check_rd asegs mc P (P + N) (P + N + -1) 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((P + N + -1) mod 8) (sval b2)) by (OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; eassumption.
    - eapply (LL mc); [exact IV0 | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="size N RLO RHI MI ST STM FR LO KLO GOT SHB LAY X9 HN RES APP UNP R1 WR1 RI RSTK RSH1"] Lemma fwrite_i_post :
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp x9 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7
               p x19 x20 (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x436a0) fc None m (seg_rom asegs)).
  Proof.
    assert (IV : INV m).
    { pose proof ST as ST'. pose proof STM as STM'. pose proof FR as FR'.
      Local Ltac2 Set LiaHints.tbl := fun () => "00j0?10242359340.81 10930976917.79 11351744022.10111447730086.13711801586693.10513478728930.84 16232768748.86 16917719815.10518185049160.84 18185344072.82 21665481682.93 24115025141.93 24122799997.82 26552522358.83 26552522358.85 29763632530.86 29765672407.83 29765672657.80 29782203372.94 29782203372.95 30010325480.82 31824352466.93 3210808038.95  34231054557.68 35497698988.81 35895327997.10537911931108.82 38959952907.84 38960247819.82 40886601363.94 40886601363.95 4111193892.78  4118807565.90  42148837058.83 44484923210.10545029014839.84 45029506359.82 47892428837.10 48324714392.83 49610168957.10549921929014.87 51845486909.80 52074235542.94 53142432559.84 54551306461.68 56172410654.83 57880736640.95 58685118222.10 59308628179.1  59308628304.9  59308628566.10 59308628695.1  62348280136.86 62472604513.84 62473096033.82 65098632093.90 6922740008.78  9405451517.105 00000100;00<00=00B00M00R00S00W00[00\00a00f00k01001501:01?01@01A01B01C01D01E01F01O01Z01^01b01o02<02A02F02K02L02P02T02a02e02n03803B03J03O03P03Q03R03[03_03g03n04204304704;04J04N04WFS3BL04NPOSSFS3HspS2R13BL02N1S3BL0FS2R1S2R1SS3BL0S3BL0S3BL0S3BL0S3RESS3RESS3RESSSSSFSSS3BL03HspS2R13BL02N1S2R1S2R1S2HN3RES2KR1BS2HN3RES2KR1BS3RESS3RESS3BL0FS2R1S2R1S3BL04NPOS2K2S2LOS3BL03HspS3BL01H2H0S3BL04NPOSS3BL02N1S3RESSSFS4NPOS2K2S2K0S3BL02K1S2N12K3S2K4FS2R1S2R1S2HN3RES3BL02KRS2LOS3BL03Hsp".
replace (bv_unsigned sp - 2128)%Z with (bv_unsigned sp + -2128)%Z in ST', STM' by lia.
      replace (bv_unsigned sp - 56)%Z with (bv_unsigned sp + -56)%Z in STM', FR' by lia.
      repeat (split; [assumption|]); try assumption. all: try apply munch_refl; try apply wmono_refl.
      split; [apply munch_refl|]. split; [apply wmono_refl|]. repeat (split; [assumption|]). assumption. }
    prep IV. subst x9.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0. cbv in K0. lia. } clear K0.
    zstep. if_cases KR; zify_cond KR.
    { (* [comment removed for export] *) eapply LX; eassumption. }
    assert (NPOS : (1 <= N)%Z) by (clear -KR RES HN BL0; nia).
    zstep. rewrite HN.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1 BL0. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      assert (N1 : (64 < N)%Z).
      { change 18446744073709551615%Z with (Z.ones 64) in K2. rewrite ?Z.land_ones in K2 by lia. change (2 ^ 64)%Z with 18446744073709551616%Z in K2.
        clear - K2 BL0 NPOS. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0 N1. lia. }
      zstep. zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APP | zsimp; exact UNP1
        | zsimp; pose proof BND_ok as B9; unfold BND in B9; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      zstep. zstep.
      eapply LX. eapply inv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= N <= 64)%Z).
      { change 18446744073709551615%Z with (Z.ones 64) in K2. rewrite ?Z.land_ones in K2 by lia. change (2 ^ 64)%Z with 18446744073709551616%Z in K2.
        clear - K2 BL0 NPOS. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1.
      destruct (shadow_probe8 asegs m RLO RHI P WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs m RLO RHI (P + N + -1) WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LE; eassumption.
      + eapply LX; eassumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End FWRITE_POST.
End CANSEC1.
