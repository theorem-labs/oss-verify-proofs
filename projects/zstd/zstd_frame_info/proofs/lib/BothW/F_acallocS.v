(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import SysStepF StepF ExecF ITreeA.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase ABytes AKit AKit2 AModelFacts APrimFacts ASecFacts ARep ARepKit ARepFrame
     F_ammap F_ammapz F_alarge.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Notation CALLOCS_STACK := 512 (only parsing).   (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma calloc_sec_spec : forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R))
    (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n ctx t PA nres nsec lo : Z) (sj : list word) (sorted : Z) (jstats jbsl jglob jslot : list byte),
  let size := needed_size n in let ms := sec_map_size n in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CALLOCS_STACK ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->      (* [comment removed for export] *)
  ra = Z_to_bv 64 0x314d0 ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  large_cells ctx t PA m ->
  (* [comment removed for export] *)
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> t + 4096 <= ATOP -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0x9da48 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells bsegs m 0x9da58 [C1 (Z_to_bv 8 sorted)] ->
  rw_cells bsegs m 0x9da60 [CB 32 jstats] ->
  rw_cells bsegs m 0x9da80 [CB 512 jbsl] ->
  rw_cells bsegs m 0x9dc80 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0x9dc98 [CB 16 jglob] ->
  (* [comment removed for export] *)
  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> PA mod 4096 = 0 ->
  0 <= nsec <= nres -> nres mod 16384 = 0 -> nres <= 1048576 ->
  (nsec < nres -> rw_cells bsegs m (PA + 8 * nsec) [CB 8 jslot]) ->
  (PA + 8388608 <= t \/ t + 4096 <= PA) -> (PA + 8388608 <= ctx \/ ctx + 4096 <= PA) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  AIMG_HI <= ctx -> iclr t 4096 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall a, FRESH a = true ->
        ablk a (a + ms) /\ a + ms <= ATOP
     /\ (a + ms <= t \/ t + 4096 <= a) /\ (a + ms <= ctx \/ ctx + 4096 <= a) /\ (a + ms <= PA \/ PA + 8388608 <= a)
     /\ fill_at m (shad a) (ms / 8) 0) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ms <= ATOP -> fp_le RNG RNG' ->
      implS bsegs RNG' (K a) (epostF Q) ms') ->
  (* [comment removed for export] *)
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec <> nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono bsegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec nres lo m1 RNG' m') ->
      stk bsegs m' lo (bv_unsigned sp) ->
      implS bsegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x314d0) fc None m' (seg_rom bsegs))) ->
  (* [comment removed for export] *)
  (forall a, FRESH a = true -> nsec = nres -> nres + 16384 <= 1048576 ->
      K a = ebind (enode (NMmap (PA + 8 * nres) 131072 3 50) (adec_mmap ATOP 131072 3)) (K2 a)) ->
  (forall a RNG' ms', FRESH a = true -> nsec = nres -> 1048576 < nres + 16384 -> implS bsegs RNG' (K a) (epostF Q) ms') ->
  (forall a r RNG' ms', r <> PA + 8 * nres -> 0 < r -> r + 131072 <= ATOP -> implS bsegs RNG' (K2 a r) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec = nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono bsegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec (nres + 16384) lo m1 RNG' m') ->
      stk bsegs m' lo (bv_unsigned sp) ->
      implS bsegs RNG' (K2 a (PA + 8 * nres)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x314d0) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMmap 0 ms 3 34) (adec_mmap ATOP ms 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x356c4) fc None m (seg_rom bsegs)).
Proof.
  intros until jslot. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> N PRIM LC CX0 CX1 T0 T1 CT2 STATS LSJ INS SRT JST JBS MTX JGL
         PA0 PA1 PAL NSR NRM NRB0 JSL DPT DPC RIMG RSTK RCTX RT RPA CXI TIC FROK UNR KONT1 SHAPE2 UNR3 UNR2 KONT2. band_lin.   (* [comment removed for export] *)
  pose proof (sec_facts n N PRIM) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
  unfold AIMG_HI, AREQMAX, AINSTANCE in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  box JSL.
  iprefix.
  Local Ltac2 Set LiaHints.tbl := fun () => "01a0?10509430936.12110612086405.12110869356312.11911799361125.11911799361125.12111799361125.12211799361125.12311807744665.15 14795189006.7  16546012056.12117776320431.11717776320431.1541800609155.118 1800609155.155 19042827563.12219365407768.12319621107352.12119733947160.12319761415192.12219885335399.10 20009109144.12120979536691.11821189826028.12122120432152.11922387597248.11722434211608.11922658091809.0  23077509607.12023283716588.12124330518296.11924638473347.11924638473347.15727147338155.12027904923666.14727975202284.12128072922155.11828406852928.1192858126872.119 30364789016.12231378091396.1  31378308326.10932442164504.12232729252332.12134440526528.1213547949305.11  36115622433.15636115622446.1183646371945.123 38068926427.4  38446806799.11838446806799.15438623137641.12239929978554.6  39932046731.11239940869632.12040460011584.11942534833304.12143059266230.10743987951393.11943987951393.15643988483203.11643988483203.15444027328302.9  4442613144.121 45848756903.11646462227904.1204718661144.119 49649769127.12049840447350.15349884968741.24 50336279704.12151014394648.12351709126144.14651845486782.11152105090727.11852569147371.28 53767577775.11753767577775.15454243526019.11854243526019.15555735422744.12356174447011.7  56987328332.11958196829417.12158230945176.12158557316120.12358597736809.11958867974552.12159308628179.7  59308628304.5  60445238764.12160453614616.12360720382360.12160858483367.11961917199020.15361917199023.11763235321900.11563235321900.15363305555623.11863748439415.6  64723157409.0  64997134979.12064997134979.15765212743211.12165447523820.12165525892073.12165576616984.12266765384856.12167536920.122   7935591832.121 8603416747.120 884472088.122  8937270826.120 00000900I00R00S00T00U00V00l01;01D01H01L01M01N01S01\01e01n02702F02O02P02Y02b02f02o03003503>03G03H03I03N03R03[03`03d03m04604704804A04J04N04[04_04c05305>05?05@05P05c06606H06L06U06Y06]06a06b06c06l07507607:07C07D07E07I07R07[07\07n07o08R08V08Z08[08\08e08f08j09:09C09L09\09e0:30:B0:K0:T0:]0:^0:b0:f0:j0:n0:o0;B0;C0;D0;E0;J0;S0;c0;l0<50<>0<G0<L0<U0<VS4CEIL2LOS4CEIL2LO2T13LSJS4CEIL2LOSSSSS4CEIL2LO3PA14NRB03HltS4CEIL2LO3SPR1HS4CEIL2LOS2LOS2LOSSS3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO3CX11HS4CEIL2LOSS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOSS3SPRS4CEIL2LOS4CEIL2LOSSS3SPRS2LOS4CEIL2LOS3SPRS2HBS4CEIL2LOS4CEIL2LOSSS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LO3Y1'S2LOS2LOS4CEIL2LO2T13LSJS1N3RSR3NSESSS4CEIL2LO2T13LSJS1N3RSR3NSE3MSR3MSBS2NB3RSE3RSR3NSE2K0S1N2NB3RSE3RSR3NSES2HBS4CEIL2LOS2LOS2LOS2LOSSS3AL13AL3S4CEIL2LOSS2HBS4CEIL2LOSSS2LOS4CEIL2LOS4CEIL2LOSS1N2NB3RSE3RSR3NSESS4CEIL2LO2T13PA13NSR4NRB'3AL33SHB1HS2LOS2LOSSS4CEIL2LOSS2HBS4CEIL2LO2T13LSJS4CEIL2LOS4CEIL2LOS4CEIL2LO2T13LSJS4CEIL2LOS1N3RSR3NSE2K0S2NB3RSR3NSE2K1S4CEIL2LOS4CEIL2LOS4CEIL2LOSS2LOS2LOS2LOS2LOSS1N3RSR3NSE3MSR3MSBSSSS3SPRS4CEIL2LOS4CEIL2LO2T13LSJS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOF".
carve_frame 48%nat ST.
  do 7 step.                                                     (* [comment removed for export] *)
  do 3 zstep.                                                   (* [comment removed for export] *)
  replace (needed_size n <? 1) with false by (symmetry; apply Z.ltb_ge; clear -NSE RSR N; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small (needed_size n)) by (clear -NSE RSR N MSR MSB; lia). rewrite zb_lxor_ones by (clear -NSE RSR N MSR MSB; lia).
  step. if_cases K0; zify_cond K0. 2: { exfalso. clear -K0 NSE RSR MSR MSB N. lia. }   (* [comment removed for export] *)
  step. step. step. if_lit.                                      (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 NSE RSR NB. lia. }     (* [comment removed for export] *)
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  apply evtF_done.
  (* [comment removed for export] *)
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LC' : large_cells ctx t PA mm) by
      (eapply (large_cells_frame ctx t PA m mm); [exact LC | exact MU | exact WM | exact CXI |];
       apply Forall_cons; [cbn [fst snd]; left; unfold AIMG_HI, AIMG_LO; clear -SPR CEIL LO CX1 CXI; lia | apply Forall_nil]);   (* [comment removed for export] *)
    assert (FROK' : forall a, FRESH a = true ->
        ablk a (a + sec_map_size n) /\ (a + sec_map_size n <= t \/ t + 4096 <= a) /\ (a + sec_map_size n <= ctx \/ ctx + 4096 <= a)
        /\ (a + sec_map_size n <= PA \/ PA + 8388608 <= a) /\ fill_at mm (shad a) (sec_map_size n / 8) 0) by
      (intros a' Ha'; destruct (FROK a' Ha') as (Y1 & Y1' & Y2 & Y3 & Y4 & Y5); split; [exact Y1|]; split; [exact Y2|]; split; [exact Y3|]; split; [exact Y4|];
       eapply fill_frame; [exact Y5 | exact MU | exact WM |]; intros _; cbn [disjoint_from]; split; [| exact I];
       rewrite shad_div; unfold ASHOFF; clear -SPR CEIL LO Y1 Y1' MSB; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)
  end.
  clear LC FROK.
  unbox JSL.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JSL' : nsec < nres -> rw_cells bsegs mm (PA + 8 * nsec) [CB 8 jslot]) by
      (intros Hlt; specialize (JSL Hlt); box JSL; carry JSL MU WM ltac:(clear -SPR CEIL LO PA0 PA1 NSR NRB0 Hlt; lia); exact JSL) end.
  clear JSL.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (large_spec RNG K K2 Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm n ctx t PA nres nsec lo sj sorted jstats jbsl jglob jslot) end.
  all: try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- forall x, _ => first [exact SHAPE2 | exact UNR3 | exact UNR | exact UNR2 | exact FROK' | exact JSL' | idtac]
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
       | |- mem_inv _ _ => assumption
       | |- large_cells _ _ _ _ => exact LC'
       | |- u64arr _ _ _ _ => exact STATS
       | |- rw_cells _ _ _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- @eq bool _ _ => exact PRIM
       | |- @eq nat _ _ => exact LSJ
       | |- _ \/ _ => assumption
       | |- rng _ _ _ => first [assumption | rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia]
       | |- _ => first [assumption | rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); unfold AREQMAX; clear -SPR CEIL LO N PA0 PA1 PAL NSR NRM NRB0 CX0 CX1 T0 T1; lia]
       end.
  all: match goal with |- implS _ _ _ _ _ => idtac | |- forall x, _ => idtac | |- ?G => idtac "REM-LARGE" G end.
  (* [comment removed for export] *)
  all: intros a' RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR HNS LP.
  all: pose proof LP as LP0; destruct LP0 as (FPLE & BW & A0 & A1 & A2 & MUL & WML & MIL & STL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NRB' & _); unfold AINSTANCE in A2, MUL.
  all: pose proof (ablk_lin _ _ A1) as (AL1 & AL2 & AL3 & AL4); unfold AIMG_HI in AL1.   (* [comment removed for export] *)
  all: rewrite ?unsigned_lit in MUL by (clear -SPR CEIL LO; lia).
  all: rewrite ?unsigned_lit in STL by (clear -SPR CEIL LO; lia).
  all: assert (SHB : 0 <= shad a' /\ shad a' + sec_map_size n / 8 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; clear -A1 A2 MSB AL1 AL2 AL3; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  all: xport FR MUL WML ltac:(unfold AINSTANCE; clear -SPR CEIL LO A0 A1 A2 T0 T1 PA0 PA1 NSR NRB0 NRB' MSB SHB AL1 AL2 AL3; lia).
  all: apply (rng_fp_le _ _ _ _ FPLE) in RSTK; apply (rng_fp_le _ _ _ _ FPLE) in RIMG.
  all: iprefix.
  all: replace (ret_pc (Z_to_bv 64 0x3576c)) with (Z_to_bv 64 0x3576c : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  all: step; step; step; if_lit.                                 (* [comment removed for export] *)
  all: step.                                                     (* [comment removed for export] *)
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.                                                (* [comment removed for export] *)
  all: release_frame FR STL (bv_unsigned sp).
  all: replace (ret_pc (Z_to_bv 64 0x314d0)) with (Z_to_bv 64 0x314d0 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  all: apply evtF_done.
  1: eapply (KONT1 a' RNG' m'); [exact HFR | exact HNS | | exact STL].
  2: eapply (KONT2 a' RNG' m'); [exact HFR | exact HNS | | exact STL].
  all: lazymatch type of MU with munch _ _ ?mm => exists mm end.
  all: replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by (clear; lia).
  all: split; [exact MU|]; split; [exact WM| exact LP].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
