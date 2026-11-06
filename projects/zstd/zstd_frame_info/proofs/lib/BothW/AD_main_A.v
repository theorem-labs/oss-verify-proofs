(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts Printf_pieces.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit Stdio_iface F_printf_iface MonadF Strnlen_iface I_printf_formats ADriver_iface AD_kit AD_ctx AD_diag.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac fix_ret := match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  lazymatch n with Zpos _ => idtac end; replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; rpc) end.
Notation wz := (Z_to_bv 64).
Notation gpv := (Z_to_bv 64 0x10800).
Notation tpv := (Z_to_bv 64 ATP).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section A.
  (* [comment removed for export] *)
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Variables (usp TID : Z) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word) (RSTK : region) (canary : word) (L : alayout).
  Hypothesis RSTK_lo : r_lo RSTK <= ALO usp.
  Hypothesis RSTK_hi : usp + -128 <= r_hi RSTK.
  Hypothesis RSTK_rlo : ATOP <= r_rlo RSTK.
  Hypothesis USP16 : usp mod 16 = 0.
  Hypothesis USPLO : ATOP + 8388608 <= usp.
  Hypothesis USPHI : usp + 24 <= 2^47.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv CI.
  Hypothesis CLI_CI : forall iv, In iv cli_img_ranges -> In iv CI.
  Hypothesis CI_WF : forall iv, In iv CI -> 0 <= fst iv.
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis SPG : usp = al_sp0 L.
  Hypothesis BOT : ATOP + 4096 <= ALO usp.
  (* [comment removed for export] *)
  Hypothesis DMALLOC : dmalloc_stmt AI.
  Hypothesis DFREE : dfree_stmt AI.
  Hypothesis DFREEN : dfree_null_stmt AI.
  Hypothesis ASHENV : ashenv_law AI.
  Hypothesis FUZZ : fuzz_oneA_stmt AI rng_fs.
  Hypothesis HSTRN : strnlen_a_stmt.
  (* [comment removed for export] *)
  Variables (argv : list (list byte)) (P0 P1 : Z) (slack0 slack1 : list byte) (RA0 RA1 : region).
  Hypothesis VARGV : valid_argv argv.
  Notation argc := (Z.of_nat (length argv)).
  Notation arg0 := (map bv_unsigned (nth 0 argv [])).
  Notation arg1 := (map bv_unsigned (nth 1 argv [])).

  #[using="Type"] Lemma nth_argv_Z : forall i, nth i (argv_Z argv) [] = map bv_unsigned (nth i argv []).
  Proof. intros i. unfold argv_Z. change (@nil Z) with (map bv_unsigned (@nil byte)) at 1. apply map_nth. Qed.
  (* [comment removed for export] *)
  Notation ABASE' j8 := (ABASE usp TID S0 S1 S2 S3 S4 S5 S6 S7 j8 RSTK canary).
  Notation AMFRAME' j8 := (AMFRAME usp S0 S1 S2 S3 S4 S5 S6 S7 j8).
  Notation LO := (ALO usp).
  Let WOKo := WOK_outside usp USP16 USPLO USPHI.

  (* [comment removed for export] *)
  Definition RNGS (RNG : footprint) : Prop :=
    rng RNG LO (usp + 24 - LO) /\ rng RNG LO (al_top L - LO) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_fs L RNG
    /\ rrng RNG RSTK /\ rrng RNG RFMT /\ rrng RNG RBstdout /\ rng0 RNG
    /\ rng RNG P0 (zlength arg0 + 1 + zlength slack0) /\ rrng RNG RA0
    /\ (2 <= argc -> rng RNG P1 (zlength arg1 + 1 + zlength slack1) /\ rrng RNG RA1).

  #[using="rng_fs_mono"] Lemma RNGS_mono : forall R R', fp_le R R' -> RNGS R -> RNGS R'.
  Proof.
    intros R R' LE (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11). unfold RNGS, rrng, rng0 in *.
    repeat match goal with |- _ /\ _ => split end; try (eapply rng_fp_le; [exact LE|]; assumption).
    - eapply rng_fs_mono; eauto.
    - intros b Hb. eapply rng_fp_le; [exact LE|]. apply G8. exact Hb.
    - intros H. destruct (G11 H) as [X Y]. split; (eapply rng_fp_le; [exact LE|]); assumption.
  Qed.

  (* [comment removed for export] *)
  Definition AARGV (mm : amem) : Prop :=
    bytes_at bsegs mm (usp + 8) (u64s [wz P0]) /\ astring usp mm P0 arg0 slack0 RA0
    /\ (2 <= argc -> bytes_at bsegs mm (usp + 16) (u64s [wz P1]) /\ astring usp mm P1 arg1 slack1 RA1).

  #[using="USP16 USPLO USPHI"] Lemma geoA : ATOP <= LO /\ LO + 8388608 - 4096 = usp /\ KHIGH <= LO /\ usp + 24 <= 2^47 /\ usp mod 16 = 0.
  Proof. clear BOT. unfold ALO, KHIGH in *. repeat split; lia. Qed.   (* [comment removed for export] *)

  #[using="VARGV"] Lemma argc_facts : 1 <= argc <= 1024.
  Proof. destruct VARGV as (A & _). exact A. Qed.

  #[using="rc usp VARGV"] Lemma arg_facts : forall i, Forall (fun c => 0 < c < 256) (map bv_unsigned (nth i argv [])) /\ zlength (map bv_unsigned (nth i argv [])) <= 131071.
  Proof.
    intros i. destruct VARGV as (_ & _ & LEN & NONUL & _).
    destruct (Nat.lt_ge_cases i (length argv)) as [LT|GE].
    - pose proof (proj1 (Forall_forall _ _) LEN _ (nth_In argv [] LT)) as L1. pose proof (proj1 (Forall_forall _ _) NONUL _ (nth_In argv [] LT)) as N1.
      cbv beta in L1, N1. split.
      + apply Forall_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as (b & <- & Hb).
        pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
        Local Ltac2 Set LiaHints.tbl := fun () => "0040>21374823365.5928797312544.5543645609252.5363297471843.5300000800?00C00GS2LT1R1HS2LT2L1S2GES2GE".
assert (bv_unsigned b <> 0); [| lia]. intros E. apply N1. replace (Z_to_bv 8 0) with b; [exact Hb|].
        apply bv_eq. rewrite E. vm_compute. reflexivity.
      + unfold zlength in *. rewrite length_map. lia.
    - rewrite nth_overflow by lia. cbn. split; [constructor| unfold zlength; cbn; lia].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="USP16 USPLO USPHI"] Lemma AARGV_after_dpost : forall LB m m', aheap_pres CI LB (usp + -128) m m' -> astk_shadow_pres (usp + -128) m m' -> AARGV m -> AARGV m'.
  Proof.
    clear BOT. intros LB m m' HP HS (B0 & A0 & A1). pose proof geoA as (G1 & G2 & G3 & G4 & G5).
    pose proof (magree_of_dpost _ _ _ _ _ HP HS) as AG.
    split; [| split].
    - eapply bytes_at_magree; [exact AG| exact B0|]. intros a Ha. cbn [u64s app] in Ha. rewrite app_nil_r, length_le8 in Ha. left. left. Local Ltac2 Set LiaHints.tbl := fun () => "0020>55187454681.6455187454681.6700000700>S2G42HaS2G42Ha".
lia.
    - eapply astring_after_dpost; eauto.
    - intros H2. destruct (A1 H2) as [B1 A1']. split; [| eapply astring_after_dpost; eauto].
      eapply bytes_at_magree; [exact AG| exact B1|]. intros a Ha. cbn [u64s app] in Ha. rewrite app_nil_r, length_le8 in Ha. left. left. lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="USP16 USPLO USPHI"] Lemma AARGV_munch : forall hi W m m', ALO usp <= hi <= usp + 8 -> Forall (WOKb usp hi) W -> munch W m m' -> wmono bsegs m m' -> AARGV m -> AARGV m'.
  Proof.
    clear BOT. intros hi W m m' Hhi HW MU WM (B0 & A0 & A1). pose proof geoA as (G1 & G2 & G3 & G4 & G5).
    pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG.
    split; [| split].
    - eapply bytes_at_magree; [exact AG| exact B0|]. intros a Ha. cbn [u64s app] in Ha. rewrite app_nil_r, length_le8 in Ha. cbv beta.
      Local Ltac2 Set LiaHints.tbl := fun () => "0080>35527003848.6535527003848.6849436243191.6549436243191.6749436243191.6849436243191.7053006806368.6753006806368.7000000500:00?00G00L00T00d014S3HhiS3HhiS3HhiS3Hhi2HaS3HhiS3Hhi2HaS5USPLO3Hhi2Ha1HS5USPLO3Hhi2Ha1H".
eapply (WOKb_outside usp USP16 USPLO USPHI); [| exact HW| left; lia]; lia.
    - eapply (astring_munch usp USP16 USPLO USPHI hi); [split; lia| exact HW| exact MU| exact WM| exact A0].
    - intros H2. destruct (A1 H2) as [B1 A1']. split; [| eapply (astring_munch usp USP16 USPLO USPHI hi); [split; lia| exact HW| exact MU| exact WM| exact A1']].
      eapply bytes_at_magree; [exact AG| exact B1|]. intros a Ha. cbn [u64s app] in Ha. rewrite app_nil_r, length_le8 in Ha. cbv beta.
      eapply (WOKb_outside usp USP16 USPLO USPHI); [| exact HW| left; lia]; lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition AENTRY (RNG : footprint) (st : APS) (ms : machine_state) : Prop :=
    exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : amem),
      ms = MS (mkR (wz ASTAGE2_RET) (wz (usp + -48)) gpv tpv t0 t1 t2 S0 S1 (wz argc) (wz (usp + 8)) a2 a3 a4 a5 a6 a7
                   S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
              bvmap_empty (wz AMAIN_PC) (Z_to_bv 32 0) None mm (seg_rom bsegs)
      /\ stk bsegs mm LO usp /\ mem_inv bsegs mm
      /\ ASTAT TID mm /\ stderr_wfile0 mm /\ rw_cells bsegs mm ssp_guard [C8 canary]
      /\ atrun_cells0 mm /\ harness_invA mm /\ rodata_sh0 mm /\ rclean mm RSTK /\ rclean mm RBstdout
      /\ rclean mm RSTG                                                      (* [comment removed for export] *)
      /\ (exists errv, rw_cells bsegs mm (errno_addr (Z_to_bv 64 ATP)) [C4 errv])
      /\ stdout_file mm stdout_init /\ aps_so st = stdout_init /\ aps_ok L st
      /\ AHEAP AI L RNG (aps_m st) [] mm
      /\ AARGV mm /\ RNGS RNG
      (* [comment removed for export] *)
      /\ bytes_at bsegs mm (usp + -8) (le8 (wz 0))
      /\ ASTG mm.                                                             (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="rc USP16 USPLO USPHI"] Lemma amain_prologue : forall RNG (Q : machine_state -> Prop) (ra s0 s1 a0 a1 a2 s2 s3 t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : amem),
    stk bsegs m LO (usp + -48) -> mem_inv bsegs m -> rng RNG LO (usp + 24 - LO) ->
    (forall (j8 : list byte) m', rw_cells bsegs m' (usp + -128) [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        stk bsegs m' LO (usp + -128) ->
        munch [(usp - 128, usp - 48)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
        evtF bsegs RNG Q (MS (mkR ra (wz (usp + -128)) gpv tpv t0 t1 t2 (wz 2) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (wz 0x7f7c0) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR ra (wz (usp + -48)) gpv tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (wz AMAIN_PC) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST MI RG K. pose proof geoA as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof (munch_refl [(usp - 128, usp - 48)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    unfold AMAIN_PC. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00c0?10551812848.10411799361125.10311799361125.10411799361125.10511799361125.10614430441667.99 19042827563.10419270706391.10321065908055.94 22850700503.10025095686512.1042546095281.103 27147338155.10328072922155.10531114942192.10131161366443.10335205502145.10235942357571.10037045569201.10137115585648.10237153363415.10138005200817.10038479837655.10140415512002.10141151449922.10141340014551.10343121191467.10243134579184.10445591866049.10246327806019.10047179659185.10349170849648.10350664164139.10550800958401.10251234361003.10551508455745.10254065164209.10354599870385.10355129410182.92 55196396784.10461215390320.10262229306583.10362418886577.10262905521367.10364845835479.10265212743211.10566092484567.10267216001008.10367692047537.1028482228913.101 8603416747.104 00000400500600700800<00C00D00E00F00J00K00R00Y00]00d00h00l00m01101201301401801<01=01D01H01L01P01Q01U01\01`01g01k01l01m02102502902:02;02<02=02D02E02I02J02K02RS2HBSSSSS2G2S5USPHISSSS2HBSS5USPHIS5USPHIS2HBS5USPHIS2G2S2G2SS2HBSSSS2G2S2G2SS5USPHIS2HBS2G2S2G2SS2HBS5USPHIS2G2S5USPHIS2G2SSS2G2S2HBS2HBSSSSS5USPHISS2HBSSS5USPHI".
carve_frame 80%nat ST.
    do 10 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => eapply (K _ mx) end; [exact FR| exact ST| exact MU| exact WM| assumption].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  Definition AP1 (RNG : footprint) (st : APS) (ms : machine_state) : Prop :=
    exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (mm : amem) (j8 : list byte),
      ms = MS (mkR (wz ASTAGE2_RET) (wz (usp + -128)) gpv tpv t0 t1 t2 (wz 2) S1 (wz 2) (wz (usp + 8)) a2 a3 a4 a5 a6 a7
                   S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
              bvmap_empty (wz 0x7f7c4) fc None mm (seg_rom bsegs)
      /\ ABASE' j8 stdout_init mm /\ aps_so st = stdout_init /\ aps_ok L st /\ AHEAP AI L RNG (aps_m st) [] mm
      /\ AARGV mm /\ RNGS RNG /\ bytes_at bsegs mm (usp + -8) (le8 (wz 0)) /\ frm0 fc /\ ASTG mm.

  (* [comment removed for export] *)
  #[using="USP16 USPLO USPHI BOT"] Lemma amain_to_test : forall RNG st (ms : machine_state) (Q : machine_state -> Prop),
    AENTRY RNG st ms ->
    (forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : amem) (j8 : list byte),
        ABASE' j8 stdout_init mm -> aps_so st = stdout_init -> aps_ok L st -> AHEAP AI L RNG (aps_m st) [] mm -> AARGV mm -> RNGS RNG ->
        bytes_at bsegs mm (usp + -8) (le8 (wz 0)) -> ASTG mm ->
        evtF bsegs RNG Q (MS (mkR (wz ASTAGE2_RET) (wz (usp + -128)) gpv tpv t0 t1 t2 (wz 2) S1 (wz argc) (wz (usp + 8)) a2 a3 a4 a5 a6 a7
                               S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                          bvmap_empty (wz 0x7f7c0) (Z_to_bv 32 0) None mm (seg_rom bsegs))) ->
    evtF bsegs RNG Q ms.
  Proof.
    intros RNG st ms Q AM K.
    destruct AM as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m
                    & -> & ST & MI & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & ERR & SOF & SOI & RK & AH & ARG & RG & U8 & SJ).
    pose proof geoA as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *. pose proof RG as (RGstk & _).
    Local Ltac2 Set LiaHints.tbl := fun () => "00:0?10953024094.10322197535550.10222700267513.10522700267513.10722700267513.11242856628793.10342856628793.10452728941397.93 64014555701.10767636088670.10400000100500900K00X00\00`00d011012SS2G2S2HaS3BOT2G22Ha1H4STGZS3BOT2G22Ha1HS2G2S2G2S2G2S5USPLO5USPHIS".
destruct (stk_split _ _ LO (usp + -48) usp ST ltac:(lia)) as [ST1 ST2].
    eapply amain_prologue; [exact ST1| exact MI| exact RGstk|].
    intros j8 m1 FR ST3 MU WM MI1.
    assert (HW : Forall (WOKb usp (usp + -48)) [(usp - 128, usp - 48)]) by (constructor; [left; cbn; lia| constructor]).
    apply (K t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 j8).
    - pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG.
      eapply (ABASE_of_parts usp TID S0 S1 S2 S3 S4 S5 S6 S7 j8 RSTK USP16 USPLO USPHI canary (usp + -48) _ m m1);
        first [exact HW| exact MU| exact WM| eassumption| idtac].
      all: lazymatch goal with
           | |- _ /\ _ => split; lia
           | |- AMFRAME _ _ _ _ _ _ _ _ _ _ _ => unfold AMFRAME; exact FR
           | |- stderr_wfile0 _ =>
               destruct SE as (flags & mode & e & wend & tail & Hc & HR); exists flags, mode, e, wend, tail; split; [| exact HR];
               eapply rw_cells_magree; [exact AG| exact Hc|]; intros a Ha; cbn in Ha |- *; lia
           | |- exists errv, _ =>
               destruct ERR as [errv ERR]; exists errv; eapply rw_cells_magree; [exact AG| exact ERR|]; intros a Ha;
               rewrite ?errno_addr_ATP in Ha; cbn in Ha |- *; lia
           end.
    - exact SOI.
    - exact RK.
    - eapply (AI_frame AI); [exact AH| exact MU| exact WM|]. constructor; [| constructor]. left. left. cbn [fst snd].
      pose proof (AI_layout AI _ _ _ _ _ AH) as (Y1 & Y2 & Y3 & Y4 & _). unfold ALO in *. lia.
    - eapply (AARGV_munch (usp + -48)); [split; lia| exact HW| exact MU| exact WM| exact ARG].
    - exact RG.
    - eapply bytes_at_magree; [eapply magree_of_munch; [exact MU| exact WM]| exact U8|]. intros a Ha. rewrite length_le8 in Ha. cbn. lia.
    - destruct SJ as [sj SJ]. exists sj. eapply rw_cells_magree; [eapply magree_of_munch; [exact MU| exact WM]| exact SJ|].
      intros a Ha. pose proof ASTAGE_LEN_Z as STGZ. cbn in Ha |- *. unfold ASTAGE in Ha. lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="USP16 USPLO USPHI BOT"] Lemma amain_to_P1 : forall RNG st (ms : machine_state) (Q : machine_state -> Prop),
    argc = 2 -> AENTRY RNG st ms ->
    (forall ms', AP1 RNG st ms' -> evtF bsegs RNG Q ms') ->
    evtF bsegs RNG Q ms.
  Proof.
    intros RNG st ms Q E2 AM K.
    eapply amain_to_test; [exact AM|]. intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm j8 BA SOI RK AH ARG RG U8 SJ.
    rewrite E2. pose proof BA as (ST & MI & _).
    zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0010>59314873579.82000004S2K0".
if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.
    apply K. unfold AP1. do 13 eexists. exists (Z_to_bv 32 0), mm, j8. split; [reflexivity|].
    split; [exact BA|]. split; [exact SOI|]. split; [exact RK|]. split; [exact AH|]. split; [exact ARG|]. split; [exact RG|]. split; [exact U8|].
    split; [vm_compute; reflexivity| exact SJ].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="USP16 USPLO USPHI WOKo"] Lemma after_diag : forall j8 so m m' W,
    ABASE' j8 so m -> Forall (WOK usp) W -> munch W m m' -> wmono bsegs m m' ->
    AMFRAME' j8 m' /\ ASTAT TID m' /\ stdout_file m' so.
  Proof.
    intros j8 so m m' W (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & ERR & SOF) HW MU WM.
    pose proof geoA as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG.
    split. { unfold AMFRAME in *. eapply rw_cells_magree; [exact AG| exact FR|]. intros a Ha. apply WOKo; [exact HW|]. cbn in Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0030>13076082658.7919422392943.799302149080.79 00000400800<S2HaS2HaS2Ha".
lia. }
    split. { eapply ASTAT_agree; [exact AG| | exact AS]. intros a Ha. apply WOKo; [exact HW|]. right.
             unfold astat_addr, astat_app, astat_sh in Ha. rewrite ?shad_div in Ha. unfold ASHOFF in Ha. lia. }
    eapply stdout_file_magree; [exact AG| | exact SOF]. intros a Ha. apply WOKo; [exact HW|]. right; left. cbn in Ha. lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="RSTK_lo RSTK_hi USP16 USPLO USPHI DRV_CI HT BOT ASHENV HSTRN VARGV WOKo"] Lemma amain_usage : forall RNG st ms, AENTRY RNG st ms -> argc <> 2 ->
    implMA RNG (main_model (ioA AAllocAsan) amalloc_M afree_M ASTAGE (alloc_initA AAllocAsan) (runA AAllocAsan)
                           (alloc_countA AAllocAsan) (argv_Z argv)) st
           (fun code s' RNG' ms' => aat_exit code s' RNG' ms') ms.
  Proof.
    intros RNG st ms AM HARGC.
    unfold main_model. unfold argv_Z at 1. rewrite length_map.
    replace (argc =? 2) with false by (symmetry; apply Z.eqb_neq; exact HARGC). cbn [negb].
    apply implMA_from_evtF.
    eapply amain_to_test; [exact AM|]. intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm j8 BA SOI RK AH ARG RG U8 _.
    pose proof geoA as (G1 & G2 & G3 & G4 & G5). pose proof argc_facts as AC. unfold KHIGH in *.
    pose proof BA as (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & ERR & SOF).
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & RG0 & RGa0 & RRa0 & _).
    destruct ARG as (B0 & A0 & _). pose proof (astring_facts usp _ _ _ _ _ A0) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
    destruct (arg_facts 0) as [HF0 LEN0].
    destruct (drv_got_of_aheap AI _ _ _ _ _ AH) as (GSE & PSE & _ & GSSP).
    zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00J0?11083647278.12215043033658.12215344696443.12215344696443.15216075584458.12217794525788.12219024661562.12223390433792.12231417094143.12932576489530.12934700506614.12235656107625.12943797664203.1224463339780.122 45264780135.12245338953658.13646781193162.1294842679434.148 4969679328.129 56322672148.15656840016110.12256840016110.14859314873579.12367711061858.1227281365951.148 8134347231.156 00000100200300400800A00E00F00J00W00^01401501601?01C01_01`01d01o02?02O02e02i02j02kFSSSS2ACS7RSTK_hiS2G2SS2Y5S3BOT2G22F11HS5USPHIS3BOT2G22F22F62F72F81HFFS7RSTK_loS2G2S3BOT2G22F12F22F62F72F82F91HSS2Y4S5USPHI3BOTS5USPHI3BOT2G21HS5USPHI3BOT2G21HS3BOT5HARGC2G22G52K01HS2G3SS".
if_cases K0; zify_cond K0. 2: { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
    (* [comment removed for export] *)
    unfold AGOT_STDERRP, ASTDERRP in GSE, PSE.
    zstep. zstep. zstep.
    pose proof (u64ro_read bsegs mm (usp + 8) [wz P0] 0 (wz P0) (wz (usp + 8)) B0 eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD. zstep. zstep. zstep.
    (* [comment removed for export] *)
    apply evtF_done.
    eapply implMA_bind.
    { unfold ioA, io_S, io_diag. rewrite (nth_argv_Z 0). apply implMA_of_implAM.
      eapply (afprintf_diag_proof HSTRN RNG RSTK (DUsage arg0)) with (lo := LO); rewrite ?unsigned_lit by lia;
        first [ apply stderr_wfile0_wfile; exact SE | reflexivity | exact ST | exact MI | exact RCS | exact ROD | exact RGimg | exact RG0 | exact RRS | exact RRF
              | split; [exact GSSP| exact GU] | exact (ASHENV _ _ _ _ _ AH) | idtac ].
      all: try (unfold AFPRINTF_DEPTH; lia).
      - cbn [adiag_args]. split; [reflexivity|]. exists slack0, RA0. destruct A0 as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
        rewrite ?unsigned_lit by lia. unfold GLOBALS_TOP, FmtFp.INT_MAX.
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
      - unfold KHIGH. lia.
      - eapply rng_sub'; [exact RGstk| lia]. }
    cbv beta. intros [] st' RNG' ms' [-> PO].
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m2 & -> & MU2 & WM2 & MI2 & FRM2 & FEQ & ST2 & SEW & SSP2 & ->).
    rewrite ?unsigned_lit in MU2, ST2 by lia. fix_ret.
    apply implMA_ret.
    assert (HW2 : Forall (WOK usp) [(LO, usp + -128); (RSTDERR, RSTDERR + 232)]) by (constructor; [left; cbn; lia| constructor; [right; right; left; cbn; split; reflexivity| constructor]]).
    destruct (after_diag _ _ _ _ _ BA HW2 MU2 WM2) as (FR2 & AS2 & SOF2).
    (* [comment removed for export] *)
    zstep.
    eapply (amain_return AI usp TID S0 S1 S2 S3 S4 S5 S6 S7 j8 USP16 USPLO USPHI canary);
      first [exact FR2 | exact ST2 | exact AS2 | exact MI2 | exact HT | exact RGimg | exact RGimsh | exact RG0 | idtac].
    - eapply (AI_frame AI); [exact AH| exact MU2| exact WM2|].
      pose proof (AI_layout AI _ _ _ _ _ AH) as (Y1 & Y2 & Y3 & Y4 & _).
      constructor; [| constructor; [| constructor]]; cbn [fst snd].
      + left. left. lia.
      + left. right; left. exists (RSTDERR, RSTDERR + 232)%Z. split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; lia].
    - rewrite SOI. exact SOF2.
    - apply stderr_wfile_file. exact SEW.
    - exact (proj2 SSP2).
    - eapply rng_sub'; [exact RGstk| lia].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End A.
End CANSEC1.
