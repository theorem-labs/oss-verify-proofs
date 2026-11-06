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
     FsKit AFake_iface F_tlsga F_m2s_b AFake_sm0 AFake_arep AFake_sm1k AH_fi_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC).
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Notation AH := (AFake_arep.AH DI AQ ASEC).
Notation FB1 F := (mkABlock (ABFake 1) F 128).

(* [comment removed for export] *)
Definition sm1_postP (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st (FB1 F :: LB) m'
    /\ F mod 128 = 0 /\ ablk F (F + 128) /\ F + 128 <= ATOP
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 96 junk; C8 (Z_to_bv 64 (fflag L 1 F))]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rng RNG F 128 /\ rng RNG (shad F) 16.

(* [comment removed for export] *)
#[using="HL"] Lemma arep_ext_sm1 : forall L st X m m' sp fs flag F,
  alayout_ok L -> AREP AH L st X m ->
  munch [(sp - 208, sp); (fs + 8, fs + 16); (flag, flag + 1); (F + 24, F + 32); (F + 120, F + 128); (2147450880 + F / 8, 2147450880 + F / 8 + 16)] m m' ->
  wmono bsegs m m' ->
  fs = al_fake L -> ATOP <= sp - 208 -> fs + 4096 <= flag < fs + 36864 -> fs + 36864 <= F -> F + 128 <= fs + 11571200 ->
  shad fs <= 2147450880 + F / 8 -> 2147450880 + F / 8 + 16 <= shad fs + 1446400 ->
  AREP AH L st X m'.
Proof.
  intros L st X m m' sp fs flag F ALO AR MU WM E S1 S2 S3 S4 S5 S6.
  assert (SHL : shlen 11571200 = 1446400) by reflexivity.
  eapply (AREP_frame_ext' DI AQ ASEC HL L st X m m' _ ALO AR MU WM). rewrite <- E, SHL. atop_facts.
  repeat (constructor; [cbn [fst snd]; intros _ |]); [right; right; lia| left; lia| left; lia| left; lia| left; lia| right; left; lia| constructor].
Qed.

#[using="HL CI_OK"] Theorem stack_malloc_1k_P : forall (k : nat) (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  Z.of_nat k < 8192 ->
  AHEAP_P AH L RNG st LB m ->
  fake_lek 1 k LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF bsegs RNG (sm1_postP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC1) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros KB AHP LEK MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AFake_arep.AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.   (* [comment removed for export] *)
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).
  (* [comment removed for export] *)
  destruct (AREP_cells _ _ _ L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).
  (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "0250?10092530843.1931043511398.173 1057495591.6   1127175226.173 11486407154.21311829522008.22311829711980.16211829712238.22111831664322.21311831809144.23113871694706.21315536006710.8  16597815198.2131688777962.173 1713438335.10  1715765315.12  17991417480.17318426717457.26 18426717457.29 18933043916.4  19845522309.16420173566834.21320865667058.21322323378911.13422369263914.17423700085155.17324125044652.21 24748469170.1732497545384.133 25886901033.17626087858018.2122701854589.133 27033617613.21328680184205.16329147256744.21829297457836.16629299450114.16229784464364.13829784497005.18729786479080.16832455914008.19432920336925.15633085935132.24 33086189277.19 33092481056.21 33490756850.18533977372108.5  34304069349.21 34304097934.26 34304097934.28 34304097934.29 34626367539.21234977465718.13535097887758.26 35097887758.29 35441213895.17335563505201.4  35695677603.17336693256564.17037192976940.8  40012727619.9  40129711135.28 41157567730.21341889083930.17341996636011.17343123787478.21243123965668.5  47348482913.17448235394228.1584835283238.2   48379341377.1684919416002.4   49927382112.21251060517858.21351781686626.17652101696360.19 52101737131.21852101950377.24 52107990421.21 52469690798.17552564951269.18 52564951269.23 52679724388.15853367570669.16854965485378.17355355428199.19455448986806.22055448989219.22155448989473.16255449179413.22355451086645.23155451297167.21355873094590.18455878677456.10 55878874588.16 56170432923.17356280132106.13456759370246.21 56765398074.24 56765644088.21856765668603.19 56953681963.21257444068485.16657980378352.19458037925428.18158159817957.17558229716486.13559110548266.17559491091130.18159749980982.19159750091318.21361161457197.17361161650461.21263214877442.17063238601098.17363370230317.17663370230318.17463623655639.13564262607882.21 64839109133.7  65018425489.16765018425489.19265500088616.18165645947670.18366755833475.15567149867122.17367238118435.21767419257744.1946753640348.167 6755523980.158 8353057128.170 9058454530.135 9551534635.28  00000K00W00c00d01Y01^01c01h01m02202g03503>03Q03h04904E04V04g04h04m05b06W06\07007107507=07B07V08508:08[08c08k09@09T09Y09^09c09k0:00:G0:^0;10;60;>0;`0<O0=>0=m0>M0>R0>l0?F0?G0?H0?P0@?0@J0@R0@l0Aa0Af0Ag0B?0BG0B[0Bc0Bh0C30C40CT0DI0D]0E60EJ0F30FO0Fc0GK0HA0HI0H_0Hk0I30I;0IC0IK0IS0I[0Ic0J;0JE0J\0Jh0Jm0K10K50K=0KA0K_0Kg0Ko0LG0L[0L`0Le0Ln0MM0Mk0N?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'R2NA3G2bS2PB3G2cS3GL23G5l3G7l3HF'S3GL13GL23G5l3G7l3HFF3Hp'3HF'S3GL2S3GL13GL23G5l3G7l2PB3HFFS3GL2S2LO3GL22HnS3GL13GL23G5l3G7l2PB3HFFS3GL22LJS3GL2S3GL2S2KB3GL23G5l3G7l2Hi2HjS3GL2S3GL13GL33ATR3FRG".
pose proof (relro_word m 0x99060 0x130ad8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0x99d28 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells bsegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app bsegs m 0x99d18 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.
  set (h := bv_unsigned h1).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  (* [comment removed for export] *)
  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').
  (* [comment removed for export] *)
  assert (HNT' : rw_cells bsegs m (al_fake L) [C8 h0; C8 (Z_to_bv 64 h); C8 h2; CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).
  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  clearbody h.
  (* [comment removed for export] *)
  assert (EFLg : forall pos, (al_fake L) + 20480 + pos = fk_flag L 1 pos)
    by (intros pos; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFRg : forall pos, (al_fake L) + 1085440 + pos * 128 = fk_frame L 1 pos)
    by (intros pos; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (FLB : forall pos, 0 <= pos < 8192 -> exists fb, rw_cells bsegs m ((al_fake L) + 20480 + pos) [C1 fb]).
  { intros pos PB. pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) ((al_fake L) + 20480 + pos) 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
    exact (c1_of_dc m _ D3). }
  assert (FLV : forall pos fb, 0 <= pos < 8192 -> rw_cells bsegs m ((al_fake L) + 20480 + pos) [C1 fb] -> fb <> Z_to_bv 8 0 ->
             In (FB1 (fk_frame L 1 pos)) LB /\ fb = Z_to_bv 8 1).
  { intros pos fb PB FLx NE.
    assert (IN : In (FB1 (fk_frame L 1 pos)) LB).
    { change 128 with (fk_fsize 1). apply (FL 1 pos fb); [unfold FK_NCLS; lia| unfold fk_nframes; cbn; lia| | exact NE].
      rewrite <- EFLg. apply (rw_C1_high m _ fb FLx). lia. }
    split; [exact IN|].
    destruct (LV 1 _ _ IN) as (_ & _ & pos' & Hp' & HF' & B1).
    assert (pos' = pos) as ->.
    { unfold fk_frame, fk_frames, fk_fsize in HF'. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add] in HF'. unfold fk_nframes in Hp'. cbn in Hp'. lia. }
    rewrite <- EFLg in B1. pose proof (rw_C1_high m _ fb FLx ltac:(lia)) as B2. congruence. }
  (* [comment removed for export] *)
  assert (CHOICE : exists pos hn, 0 <= pos < 8192 /\ rw_cells bsegs m ((al_fake L) + 20480 + pos) [C1 (Z_to_bv 8 0)] /\
            forall (j24 j56 sh0 sh1 : word),
              rw_cells bsegs m ((al_fake L) + 1085440 + pos * 128 + 24) [C8 j24] -> rw_cells bsegs m ((al_fake L) + 1085440 + pos * 128 + 120) [C8 j56] ->
              rw_cells bsegs m (shad ((al_fake L) + 1085440 + pos * 128)) [C8 sh0; C8 sh1] ->
              evtF bsegs RNG (sm1_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo (al_fake L) hn
                                ((al_fake L) + 20480 + pos) ((al_fake L) + 1085440 + pos * 128) h0 h2 hs m)
                (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    FR (Z_to_bv 64 ASTKMALLOC1) fc None m (seg_rom bsegs))).
  { set (fpos := fun i : nat => Z.land (h + Z.of_nat i) 8191).
    assert (FPB : forall i, 0 <= fpos i < 8192) by (intros i; apply land8191_bound).
    (* [comment removed for export] *)
    assert (RND : forall i, rw_cells bsegs m ((al_fake L) + 20480 + fpos i) [C1 (Z_to_bv 8 0)]
                         \/ (rw_cells bsegs m ((al_fake L) + 20480 + fpos i) [C1 (Z_to_bv 8 1)] /\ In (FB1 (fk_frame L 1 (fpos i))) LB)).
    { intros i. destruct (FLB (fpos i) (FPB i)) as [fb FLi].
      destruct (decide (fb = Z_to_bv 8 0)) as [E0|NE]; [left; subst fb; exact FLi|].
      destruct (FLV (fpos i) fb (FPB i) FLi NE) as [IN ->]. right. split; [exact FLi| exact IN]. }
    (* [comment removed for export] *)
    assert (SEARCH : forall N : nat,
              (exists n, (n < N)%nat /\ rw_cells bsegs m ((al_fake L) + 20480 + fpos n) [C1 (Z_to_bv 8 0)]
                         /\ forall j, (j < n)%nat -> rw_cells bsegs m ((al_fake L) + 20480 + fpos j) [C1 (Z_to_bv 8 1)])
              \/ (forall j, (j < N)%nat -> In (FB1 (fk_frame L 1 (fpos j))) LB
                                          /\ rw_cells bsegs m ((al_fake L) + 20480 + fpos j) [C1 (Z_to_bv 8 1)])).
    { induction N as [|N IH].
      - right. intros j Hj. lia.
      - destruct IH as [(n & Hn & Fn & Bn)|ALL].
        + left. exists n. split; [lia|]. split; [exact Fn| exact Bn].
        + destruct (RND N) as [FN|(BN & IN)].
          * left. exists N. split; [lia|]. split; [exact FN|]. intros j Hj. exact (proj2 (ALL j Hj)).
          * right. intros j Hj. destruct (Nat.eq_dec j N) as [->|NE]; [split; assumption|]. apply ALL. lia. }
    destruct (SEARCH (S k)) as [(n & Hn & FLn & BSn)|ALL].
    2:{ exfalso. apply (fake_lek_pigeon 1 k LB (fun j => fk_frame L 1 (fpos j)) LEK).
        - intros i j Hi Hj E0. unfold fk_frame, fk_frames, fk_fsize in E0. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add] in E0.
          assert (E1 : fpos i = fpos j) by lia.
          destruct (Nat.eq_dec i j) as [EQ|NE]; [exact EQ| exfalso].
          apply (land8191_inj h (Z.of_nat i) (Z.of_nat j)); [lia| lia| lia| exact E1].
        - intros i Hi. exists 128. exact (proj1 (ALL i Hi)). }
    (* [comment removed for export] *)
    exists (fpos n), (h + Z.of_nat n). split; [apply FPB|]. split; [exact FLn|].
    intros j24 j56 sh0 sh1 F24 F56 SH0.
    eapply (stack_malloc1_cspecK RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x5d3fd0 (al_fake L) h n (fpos n) ((al_fake L) + 20480 + fpos n)
               ((al_fake L) + 1085440 + fpos n * 128) j24 j56 sh0 sh1 h0 h2 hs);
      try exact MI; try exact ST; try exact TP; try exact BSn; try exact FLn; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  destruct CHOICE as (pos & hn & PB & FL0 & WALK).
  set (flag := (al_fake L) + 20480 + pos) in *. set (F := (al_fake L) + 1085440 + pos * 128) in *.
  assert (EFL : flag = fk_flag L 1 pos) by (subst flag; apply EFLg).
  assert (EFR : F = fk_frame L 1 pos) by (subst F; apply EFRg).
  assert (EFF : fflag L 1 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHB : shad (al_fake L) + 135680 + 16 * pos = shad F /\ shad F + 16 <= shad (al_fake L) + 1446400 /\ shad F + 16 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 16 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }
  (* [comment removed for export] *)
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 88 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 120) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  destruct (c8c8_of_dc m _ DS2) as (sh0 & sh1 & SH0).
  assert (HFLAG : flag = (al_fake L) + 20480 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 1085440 + pos * 128) by reflexivity.
  clearbody flag F.
  (* [comment removed for export] *)
  assert (NOTIN : ~ In (FB1 F) LB).
  { intros IN. destruct (LV 1 F 128 IN) as (_ & _ & pos' & Hp' & HF' & B1).
    assert (pos' = pos) as ->.
    { rewrite EFR in HF'. unfold fk_frame, fk_frames, fk_fsize in HF'. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add] in HF'.
      unfold fk_nframes in Hp'. cbn in Hp'. lia. }
    rewrite <- EFL in B1. pose proof (rw_C1_high m flag _ FL0 ltac:(lia)) as B0. rewrite B0 in B1. injection B1 as B1.
    vm_compute in B1. discriminate B1. }
  eapply evtF_mono; [exact (WALK j24 j56 sh0 sh1 F24 F56 SH0)|].

  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FL1 & F24' & F56' & SH').
  unfold sm1_W in MU. rewrite SHF in MU.
  (* [comment removed for export] *)
  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) + 8 <= a < (al_fake L) + 16) -> a <> flag ->
            ~ (F + 24 <= a < F + 32) -> ~ (F + 120 <= a < F + 128) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 16) ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
  assert (F64 : F mod 128 = 0).
  { rewrite HFF. clear - G1. apply Z.mod_divide in G1; [|lia]. destruct G1 as [kk Hk]. rewrite Hk. apply Z.mod_divide; [lia|]. exists (32 * kk + 8480 + pos). lia. }
  (* [comment removed for export] *)
  Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
  Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].   (* [comment removed for export] *)
  assert (AR' : AREP AH L st X m').
  { eapply (arep_ext_sm1 L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
  assert (HFK' : AFAKE L (FB1 F :: LB) m').
  { split; [exact G|]. split.
    { unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
      split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }   (* [comment removed for export] *)
    split; [exists h0, (Z_to_bv 64 (hn + 1)), h2, hs; exact HNT2|].
    split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGC MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
    split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
    split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
    split.
    - intros c pos' b Hc Hp Hb NZ.
      destruct (Z.eq_dec c 1) as [->|NC]; [destruct (Z.eq_dec pos' pos) as [->|NP]|].
      + left. rewrite <- EFR. unfold fk_fsize. reflexivity.
      + right. pose proof (fk_flags_disjoint L 1 pos' 1 pos Hc Hp Hc ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L 1 pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
      + right. pose proof (fk_flags_disjoint L c pos' 1 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L c pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
    - intros c F' n' [E|Hin].
      + injection E as <- <- <-. split; [unfold FK_NCLS; lia|]. split; [reflexivity|].
        exists pos. split; [unfold fk_nframes; cbn; lia|]. split; [exact EFR|].
        rewrite <- EFL. apply (rw_C1_high m' flag _ FL1). lia.
      + destruct (LV c F' n' Hin) as (Hc & Hn & pos' & Hp & HF' & B1).
        split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp|]. split; [exact HF'|].
        assert (NE : fk_flag L c pos' <> flag).
        { rewrite EFL. apply (fk_flags_disjoint L c pos' 1 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia)).
          intros E. injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn in Hin. unfold fk_fsize in Hin.
          cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add] in Hin. exact Hin. }
        pose proof (fk_flag_range L c pos' Hc Hp) as FRG. rewrite OUT by (first [clear -FRG NE G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). exact B1. }
  (* [comment removed for export] *)
  assert (BL' : ablocks L st X (FB1 F :: LB)).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
    - intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - cbn. exact B3.
    - constructor; [exact NOTIN| exact B4]. }
  assert (AHP' : AHEAP_P AH L RNG st (FB1 F :: LB) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AFake_arep.AH ah_fake]. exact HFK'. }
  (* [comment removed for export] *)
  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP   (* [comment removed for export] *)
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 128 <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE _ _ _ L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (1, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in Hb.
        replace (fk_fsize 1) with 128 in Hb by reflexivity. exact Hb. }
      pose proof (fk_frames_disjoint L c' pos' 1 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 1) with 128 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->   (* [comment removed for export] *)
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 128)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0
        D24 D56 DS2 RR A10.
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
  pose proof (dc_at_any m m' (F + 32) 88 DJ1 WM ltac:(lia)) as DJ1'.
  destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
  destruct DJ1' as [junk1 J1]. change (Z.to_nat 88) with 88%nat in J1.
  assert (LJ : length junk1 = 88%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 96 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 1 F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app bsegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 96 (le8 sp ++ junk1)] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
      eapply rw_cells_recast; [apply (proj2 (rw_cells_app bsegs m' (F + 24) [C8 sp] [CB 88 junk1])); split; [exact F24'|];
        cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
      + reflexivity.
    - cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 96) with (F + 120) by lia. exact F56'. }
  (* [comment removed for export] *)
  unfold sm1_postP. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].   (* [comment removed for export] *)
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Section Inst.
  Variable AI : AMallocIface.
  Hypothesis E : AHEAP AI = AHEAP_P AH.
  Hypothesis EC : aci AI = CI.

  #[using="DI AQ ASEC HL CI CI_OK E EC"] Lemma stack_malloc_1k_AI : forall k, Z.of_nat k < 8192 -> stack_malloc_1_stmtk AI fflag afake_rng k.
  Proof.
    intros k KB. unfold stack_malloc_1_stmtk, sm_stmtk. intros until lo. intros AHx LE MI ST BOT LO SPT TP RSTK RI RFS.
    rewrite E in AHx. unfold AFI_SM1. change 0x3c728 with ASTKMALLOC1.
    eapply evtF_mono; [eapply (stack_malloc_1k_P k); eassumption|].
    cbv beta. intros ms' PO. unfold sm1_postP in PO. unfold sm_post.
    destruct PO as (F & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & j0 & j1 & j2 & junk & EQ & MI' & ST' & HPR & AH' & REST).
    exists F, x0, x1, x2, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, m', j0, j1, j2, junk.
    rewrite E, EC. repeat (split; [assumption|]). exact REST.
  Qed.

  (* [comment removed for export] *)
  #[using="DI AQ ASEC CI CI_OK E EC"] Lemma fake_flag_AI : fake_flag_law AI fflag.
  Proof.
    unfold fake_flag_law. intros L RNG st LB m cls F N AHx Hin. rewrite E in AHx. rewrite EC.
    eapply fake_flag_P; eassumption.
  Qed.

  #[using="DI AQ ASEC HL E"] Lemma fake_release_AI : fake_release_law AI fflag.
  Proof. unfold fake_release_law. intros L RNG st LB m cls F N AHx. rewrite E in AHx |- *. eapply fake_release_P; eassumption. Qed.
End Inst.
End S.
End CANSEC1.
