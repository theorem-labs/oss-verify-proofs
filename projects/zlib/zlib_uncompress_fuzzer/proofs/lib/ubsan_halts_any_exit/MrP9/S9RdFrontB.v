(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import Vdso.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require MmapBase.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require PropExec CatExec StoreOk Frame ShapeAlg ModelAmb DrawDefs S9ReadBase S9ReadStage S9World
  S9StartupDefs S9Startup S9StartupFacts S9PilotOOM.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Walk Arr SysStep ITree Nodes InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PState. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM12. Import MM12. Import MM12.Malloc_iface. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM02. Import MM02. Import MM02.Malloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.PlainS9 Require Import PImg RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require RunHit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Mr Require Import MrFeasNull MrRoom MrRulesS9.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.MrP9 Require Import S9HeapPre S9HBase S9HConv S9TrTail S9MainPreH S9RdLib S9RdInv S9RdRules.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Module SS := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.S9Startup.
Module SF := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.S9StartupFacts.
Module W0 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.S9World.

Lemma cells_outside_iv : forall lo hi : Z,
  forallb (fun c : Z * nat => (hi <=? fst c) || (fst c + Z.of_nat (snd c) <=? lo)) SF.D_main_cells = true ->
  forall a : Z, lo <= a < hi -> Forall (fun c : Z * nat => a < fst c \/ fst c + Z.of_nat (snd c) <= a) SF.D_main_cells.
Proof.
  intros lo hi H a Ha. apply Forall_forall. intros c Hc.
  pose proof (proj1 (forallb_forall _ _) H c Hc) as Hb. cbv beta in Hb.
  apply orb_true_iff in Hb. destruct Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.

Section FRONTB.
Context {rc : runConstT}.
(* over the launch input (av / ev are notations of it) and its mmap base, as MainPreH;
   brk / Hvl / Hlau are the launch facts MainPreH's me_rauxv reads (RefLayout's 727 layout). *)
Variables (sp0 : word) (inp : ProcInput) (mbase : word) (rdraw : EntryDraw) (tid : word).
#[local] Instance RC_a1_1 : RunCtx := mkRunCtx inp sp0 mbase.
Local Notation av := (in_argv inp) (only parsing).
Local Notation ev := (in_envp inp) (only parsing).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte).
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis ME : SS.main_entry sp0 inp mbase rdraw tid regs0 mem0.
Hypothesis HCAN : CAN = DrawDefs.canary_w rdraw.
Hypothesis HSEC : SECRET = bv_unsigned (DrawDefs.secret_w rdraw).
Hypothesis HATOP : ATOP = bv_unsigned sp0 - 8388608.
Variable brk : word.
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.

Let SP := bv_unsigned sp0.

(* the stack below the call is the ruled window [SP - 6144513, SP) (MainPreH me_stk,
   S8Startup main_entry_store_ok_win); rd_base's stack field starts there (RdInv). *)
Lemma rd_base_at_call : forall M : word -> option byte,
  OF.frame_mod mem0 M [(Z_to_bv 64 (SP - 8388608), 8388608)] -> W0.main_frame SP M ->
  rd_base SP tid M.
Proof.
  intros M FM MF. destruct Hvsp as (SPlo & SPhi & SPal). unfold sp_window_lo, sp_window_hi in *. fold SP in SPlo, SPhi, SPal.
  destruct FM as [FE FG].
  assert (AG : forall a : word, bv_unsigned a < 0x94000 -> M a = mem0 a).
  { intros a Ha. apply FE. cbn [OF.outside]. split; [|exact I]. unfold OF.in_rng. rewrite unsigned_lit by lia. lia. }
  assert (AGhi : forall a : word, SP <= bv_unsigned a -> M a = mem0 a).
  { intros a Ha. apply FE. cbn [OF.outside]. split; [|exact I]. unfold OF.in_rng. rewrite unsigned_lit by lia. lia. }
  assert (AGv : forall a : word, bv_unsigned a < SP - 8388608 -> M a = mem0 a).
  { intros a Ha. apply FE. cbn [OF.outside]. split; [|exact I]. unfold OF.in_rng. rewrite unsigned_lit by lia. lia. }
  pose proof (me_stk sp0 inp mbase rdraw tid regs0 mem0 SPlo ME HATOP M FG (SP - 120) ltac:(unfold SP; lia)) as ST0.
  fold SP in ST0.
  destruct (stk_carve (run_segments psegs rc_inp rc_sp rc_mb) M (SP - 6144513) (SP - 120) 8 ST0 ltac:(cbn; lia)) as [ST [junk FR]].
  change (Z.of_nat 8) with 8 in ST, FR. replace (SP - 120 - 8) with (SP - 128) in ST, FR by lia.
  assert (SOK : forall a (n : nat), SP - 6144513 <= a -> a + Z.of_nat n <= SP -> store_ok (run_segments psegs rc_inp rc_sp rc_mb) M (wa a) n = true).
  { intros a n H1 H2. eapply OS.store_ok_mono; [exact FG|].
    apply (SS.main_entry_store_ok_win sp0 inp mbase rdraw tid regs0 mem0 ME (run_segments psegs rc_inp rc_sp rc_mb) (wa a) n);
      unfold wa; rewrite unsigned_lit by (unfold SP in *; lia); unfold SP in *; lia. }
  constructor.
  - exact ST.
  - apply (wr_at_of_store_ok M (SP - 48) 48); [lia | cbn; lia | apply SOK; cbn; lia].
  - exists junk. destruct MF as [Cra C0 C1 C2 C3 C4 C5 C6 C7]. unfold main_cells.
    apply rw_cells_cons; [exact FR|]. cbn [csize]. change (Z.of_nat 8) with 8.
    replace (SP - 128 + 8) with (SP - 120) by lia.
    apply rw_cells_cons; [apply rw_cell8_of_cell; [exact C7 | apply SOK; cbn; lia | lia | lia]|]. cbn [csize]. change (Z.of_nat 8) with 8.
    replace (SP - 120 + 8) with (SP - 112) by lia.
    apply rw_cells_cons; [apply rw_cell8_of_cell; [exact C6 | apply SOK; cbn; lia | lia | lia]|]. cbn [csize]. change (Z.of_nat 8) with 8.
    replace (SP - 112 + 8) with (SP - 104) by lia.
    apply rw_cells_cons; [apply rw_cell8_of_cell; [exact C5 | apply SOK; cbn; lia | lia | lia]|]. cbn [csize]. change (Z.of_nat 8) with 8.
    replace (SP - 104 + 8) with (SP - 96) by lia.
    apply rw_cells_cons; [apply rw_cell8_of_cell; [exact C4 | apply SOK; cbn; lia | lia | lia]|]. cbn [csize]. change (Z.of_nat 8) with 8.
    replace (SP - 96 + 8) with (SP - 88) by lia.
    apply rw_cells_cons; [apply rw_cell8_of_cell; [exact C3 | apply SOK; cbn; lia | lia | lia]|]. cbn [csize]. change (Z.of_nat 8) with 8.
    replace (SP - 88 + 8) with (SP - 80) by lia.
    apply rw_cells_cons; [apply rw_cell8_of_cell; [exact C2 | apply SOK; cbn; lia | lia | lia]|]. cbn [csize]. change (Z.of_nat 8) with 8.
    replace (SP - 80 + 8) with (SP - 72) by lia.
    apply rw_cells_cons; [apply rw_cell8_of_cell; [exact C1 | apply SOK; cbn; lia | lia | lia]|]. cbn [csize]. change (Z.of_nat 8) with 8.
    replace (SP - 72 + 8) with (SP - 64) by lia.
    apply rw_cells_cons; [apply rw_cell8_of_cell; [exact C0 | apply SOK; cbn; lia | lia | lia]|]. cbn [csize]. change (Z.of_nat 8) with 8.
    replace (SP - 64 + 8) with (SP - 56) by lia.
    apply rw_cell8_of_cell; [exact Cra | apply SOK; cbn; lia | lia | lia].
  - exists (Z_to_bv 64 0). exact (me_errno sp0 inp mbase rdraw tid regs0 mem0 SPlo ME HATOP M AG).
  - eapply me_mem_inv; eassumption.  (* + AGv *)
  - exact (me_rauxv sp0 inp mbase rdraw tid regs0 mem0 Hva SPlo SPhi ME HCAN HSEC HATOP Hve SPal brk Hvl Hlau M AG AGv AGhi).
  - intros lo hi a IN Ha. apply (me_none_gen sp0 inp mbase rdraw tid regs0 mem0 SPlo ME HATOP M AG a).
    + unfold rd_ivs in IN. cbn [In] in IN. repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]). destruct IN.
    + unfold rd_ivs in IN. cbn [In] in IN.
      repeat (destruct IN as [IN|IN]; [injection IN as <- <-; refine (cells_outside_iv _ _ _ a Ha); reflexivity|]). destruct IN.
  - exact (me_tid sp0 inp mbase rdraw tid regs0 mem0 SPlo ME HATOP M AG).
Qed.

(* the model after the openat is PilotOOM model1g over the launch (model0 =
   Run.init_config's with_vdso over init_model, tid set, fd 3 inserted); brk / mbase moved up. The launch's channel
   reader (Hcr) is minv's last conjunct, which KLink's KL_init reads. *)
Variables (content : list byte).
Hypothesis Htid : 0 < bv_unsigned tid < 2 ^ 22.
Hypothesis Hbrk : valid_brk psegs brk.
Hypothesis Hcr : in_channel_reader inp = true.
Variables (AI AIm : nat -> list bptr -> PState -> Model -> Prop) (j0 : nat).
Hypothesis RMF : rule_malloc_first AI j0.
Variables (fde : FdEntry) (G : PState -> Model -> Prop).

Abbreviation MODEL1g := (S9PilotOOM.model1g sp0 inp rdraw tid brk mbase fde).
Hypothesis GOK : frame_ok G.
Hypothesis GM1 : forall s, G s MODEL1g.
Hypothesis MINV1 : minv MODEL1g.

Lemma first_malloc_gen : forall (A K : ShapeAlg.TSet) (R : bvmap 5 word) (M : word -> option byte) (pp : word),
  OP.getr R 1 = Z_to_bv 64 0x14920 -> OP.getr R 2 = Z_to_bv 64 (SP - 128) ->
  OP.getr R 3 = Z_to_bv 64 0x10800 -> OP.getr R 4 = Z_to_bv 64 0x72f60 ->
  OP.getr R 8 = Z_to_bv 64 2 ->
  OP.getr R 10 = Z_to_bv 64 65536 -> OP.getr R 18 = pp ->
  OP.getr R 20 = Z_to_bv 64 3 -> OP.getr R 21 = Z_to_bv 64 65536 ->
  OF.frame_mod mem0 M [(Z_to_bv 64 (SP - 8388608), 8388608)] -> W0.main_frame SP M ->
  A [] -> K [] ->
  (forall (M' : word -> option byte) (s' : PState) (mo' : Model)
          (y1 y5 y6 y7 x8 x9 y11 y12 y13 y14 y15 y16 y17 x18 x19 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31 : word),
     rd_base SP tid M' -> RHEAP s' [] M' -> OWN [] G s' mo' ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 (SP - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) y5 y6 y7 x8 x9
                                    (Z_to_bv 64 0) y11 y12 y13 y14 y15 y16 y17 x18 x19 (Z_to_bv 64 3) (Z_to_bv 64 65536)
                                    x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                               bvmap_empty (Z_to_bv 64 0x14b74) fc0 None M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo') A) ->
  (forall (pb : bptr) (buf : Z) (M' : word -> option byte) (s' : PState) (mo' : Model)
          (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x24 x25 x26 x27 y28 y29 y30 y31 : word),
     rd_inv SP tid content G pb buf 65536 0 M' s' mo' -> AI j0 [pb] s' mo' ->
     (forall a : word, SP <= bv_unsigned a -> M' a = mem0 a) ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 (SP - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 2) (Z_to_bv 64 buf)
                                    y10 y11 y12 y13 y14 y15 y16 y17 pp (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 65536)
                                    (Z_to_bv 64 0x22e59) (Z_to_bv 64 buf) x24 x25 x26 x27 y28 y29 y30 y31)
                               bvmap_empty (Z_to_bv 64 0x14998) fc0 None M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo') K) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) R (Z_to_bv 64 0x19400) M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) MODEL1g) (ShapeAlg.t_alt2 A K).
Proof.
  intros A K R M pp G1 G2 G3 G4 G8 G10 G18 G20 G21 FM MF HA0 HK0 KNULL KSOME.
  destruct Hvsp as (SPlo & SPhi & SPal). unfold sp_window_lo, sp_window_hi in *. fold SP in SPlo, SPhi, SPal.
  pose proof (rd_base_at_call M FM MF) as BASE.
  assert (AG : forall a : word, bv_unsigned a < 0x94000 -> M a = mem0 a).
  { intros a Ha. destruct FM as [FE _]. apply FE. cbn [OF.outside]. split; [|exact I]. unfold OF.in_rng. rewrite unsigned_lit by lia. lia. }
  assert (AGhi : forall a : word, SP <= bv_unsigned a -> M a = mem0 a).
  { intros a Ha. destruct FM as [FE _]. apply FE. cbn [OF.outside]. split; [|exact I]. unfold OF.in_rng. rewrite unsigned_lit by lia. lia. }
  assert (AGv : forall a : word, bv_unsigned a < SP - 8388608 -> M a = mem0 a).
  { intros a Ha. destruct FM as [FE _]. apply FE. cbn [OF.outside]. split; [|exact I]. unfold OF.in_rng. rewrite unsigned_lit by lia. lia. }
  pose proof (main_entry_RHEAP sp0 inp mbase rdraw tid regs0 mem0 Hva SPlo ME HCAN HATOP M AG AGv) as [HH _].  (* + AGv *)
  apply rz_mkR. unfold mkR_of.
  rewrite (G1 : reg_get R (Z_to_bv 5 1) = _), (G2 : reg_get R (Z_to_bv 5 2) = _), (G3 : reg_get R (Z_to_bv 5 3) = _),
          (G4 : reg_get R (Z_to_bv 5 4) = _), (G8 : reg_get R (Z_to_bv 5 8) = _), (G10 : reg_get R (Z_to_bv 5 10) = _),
          (G18 : reg_get R (Z_to_bv 5 18) = _), (G20 : reg_get R (Z_to_bv 5 20) = _), (G21 : reg_get R (Z_to_bv 5 21) = _).
  forget_regs R. clear G1 G2 G3 G4 G8 G10 G18 G20 G21.
  pose proof BASE as [ST UP FRM (errv & ERR) MI AUX IMG TIDC].
  (* the launch's mmap base is in Linux's band (S0PilotOOM mbase_lo). *)
  assert (Hmb : mmap_base_min <= bv_unsigned mbase).
  { destruct Hlau as (_ & _ & Hb). exact (proj1 (MmapBase.valid_launch_base_sv48_in_band _ _ Hb)). }
  assert (HOWN : OWN [] G (ps_init (reservedZ psegs ++ RunHit.vdso_resvZ rc_inp rc_sp rc_mb) ATOP) MODEL1g).
  { apply (OWN_init_vm G MODEL1g brk mbase sp0 S9PilotOOM.LIM inp);
      [reflexivity | reflexivity | exact MINV1 | reflexivity | exact Hbrk | | | exact Hmb | exact Hcr | apply GM1].
    - unfold sp_window_lo, sp_window_hi. fold SP. lia.
    - rewrite HATOP. reflexivity. }
  (* the malloc call's stack bound is the ruled window's low end SP - 6144513 (>= ATOP). *)
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    eapply (RMF RR M MODEL1g G (SP - 6144513) SP errv brk S9PilotOOM.LIM A K) end.  (* mbase sp0 inp = the RunCtx's *)
  1:{ apply call_pre_intro.
      - exact HH.
      - exact HOWN.
      - exact GOK.
      - exact AUX.
      - simp_regs; rewrite unsigned_lit by lia; lia.
      - simp_regs; rewrite unsigned_lit by lia; exact ST.
      - rewrite HATOP. fold SP. lia.
      - simp_regs; rewrite unsigned_lit by lia; unfold RMALLOC_STACK; lia.
      - simp_regs; rewrite rerrno_lit'; exact ERR.
      - exact MI.
      - simp_regs; reflexivity. }
  1: simp_regs; reflexivity. 1: reflexivity. 1: reflexivity.
  1: unfold S9PilotOOM.LIM; rewrite MmapSim.source_alloc_limit_val; lia.
  1: exact HA0. 1: exact HK0.
  intros R' M' mo' s' r MR OR HAI.
  destruct MR as (KEPT & MI' & ST' & [errv' ERR'] & AUX' & HP & _ & _ & HR).
  revert HP ST' ERR'. simp_regs. rewrite !unsigned_lit by lia. rewrite rerrno_lit'. intros HP ST' ERR'.
  assert (BASE' : rd_base SP tid M')
    by (eapply rd_base_heap; [exact BASE | exact HP | lia | exact MI' | exact ST' | exact ERR' | exact AUX']).
  destruct r as [q|]; cbn [own_ret] in OR.
  2:{
    destruct HR as [Ha0 HH'].
    pose proof OR as [(L' & _ & HKL' & _) _].
    pose proof (kl_halt _ _ _ HKL') as Hh'.
    pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo' (kl_minv _ _ _ HKL')) as Hl'.
    use_kept KEPT. rewrite Ha0. forget_regs R'.
    rewrite ret_pc_even by (first [lia | reflexivity]).
    apply rz_evt; [exact Hh' | exact Hl' |].
    step. if_true. apply evt_done.
    eapply KNULL; [exact BASE' | exact HH' | exact OR]. }
  destruct HR as (nb & junk2 & Ha0 & _ & HH' & NBLK & _).
  pose proof OR as [(L' & _ & HKL' & _) _].
  pose proof (kl_halt _ _ _ HKL') as Hh'.
  pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo' (kl_minv _ _ _ HKL')) as Hl'.
  pose proof (RHEAP_block_range_proof _ _ _ (q, nb, 65536) HH' ltac:(left; reflexivity)) as (N1 & N2 & N3 & N4 & N5).
  cbn [blk_addr blk_size fst snd] in N1, N2, N3, N4, N5.
  assert (ABOVE : forall a : word, SP <= bv_unsigned a -> M' a = mem0 a).
  { intros a Ha. rewrite <- (AGhi a Ha). pose proof (bv_unsigned_in_range _ a) as UA. change (bv_modulus 64) with (2 ^ 64) in UA.
    destruct (HP (bv_unsigned a) UA ltac:(left; lia)) as [E _]. unfold wa in E. rewrite Z_to_bv_bv_unsigned in E. exact E. }
  use_kept KEPT. rewrite Ha0. forget_regs R'.
  rewrite ret_pc_even by (first [lia | reflexivity]).
  apply rz_evt; [exact Hh' | exact Hl' |].
  step.
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let C := fresh "C" in assert (C : c = false);
    [ unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia | rewrite C; cbv iota; clear C ] end.
  do 5 step.
  if_true. do 2 step. apply evt_done.
  eapply KSOME; [|exact HAI | exact ABOVE].
  constructor.
  - exact HH'.
  - exact OR.
  - exists junk2. split; [exact NBLK | reflexivity].
  - lia.
  - exact BASE'.
Qed.
End FRONTB.

Section FRONTF.
Context {rc : runConstT}.
(* as FRONTB, over the launch input. The read loop's AmbIn and file system are the
   launch's: stdin0 = ModelAmb.amb_of inp (the run's vDSO run inside, ModelAmb edition), fs0 = in_fs inp;
   MODEL1 (model1g over the launch) is then RS.modelG's model by conversion (ModelAmb init_model_amb). *)
Variables (sp0 : word) (inp : ProcInput) (mbase : word) (rdraw : EntryDraw) (tid : word).
#[local] Instance RC_a1_2 : RunCtx := mkRunCtx inp sp0 mbase.
Local Notation av := (in_argv inp) (only parsing).
Local Notation ev := (in_envp inp) (only parsing).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte).
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis ME : SS.main_entry sp0 inp mbase rdraw tid regs0 mem0.
Hypothesis HCAN : CAN = DrawDefs.canary_w rdraw.
Hypothesis HSEC : SECRET = bv_unsigned (DrawDefs.secret_w rdraw).
Hypothesis HATOP : ATOP = bv_unsigned sp0 - 8388608.
Variable brk : word.
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
Local Notation stdin0 := (ModelAmb.amb_of inp (vdso_run_init (ed_vdso rdraw))) (only parsing).
Local Notation fs0 := (in_fs inp) (only parsing).
Variables (path : list byte) (content : list byte).
Hypothesis Hfile : fs_lookup fs0 path = Some content.
Hypothesis Htid : 0 < bv_unsigned tid < 2 ^ 22.
Hypothesis Hbrk : valid_brk psegs brk.
Hypothesis Hcr : in_channel_reader inp = true.
Variables (AI AIm : nat -> list bptr -> PState -> Model -> Prop) (j0 : nat).
Hypothesis RMF : rule_malloc_first AI j0.

Let SP := bv_unsigned sp0.
Abbreviation MODEL1 := (S9PilotOOM.model1g sp0 inp rdraw tid brk mbase (FdFile path (Z_to_bv 64 0))).
Abbreviation GRD := (G_rd path stdin0 fs0 tid).

Lemma model1_G_rd : forall s, GRD 0 s MODEL1.
Proof. intros s. unfold G_rd. reflexivity. Qed.

Lemma first_malloc_rz : forall (A K : ShapeAlg.TSet) (R : bvmap 5 word) (M : word -> option byte),
  OP.getr R 1 = Z_to_bv 64 0x14920 -> OP.getr R 2 = Z_to_bv 64 (SP - 128) ->
  OP.getr R 3 = Z_to_bv 64 0x10800 -> OP.getr R 4 = Z_to_bv 64 0x72f60 ->
  OP.getr R 8 = Z_to_bv 64 2 ->
  OP.getr R 10 = Z_to_bv 64 65536 ->
  OP.getr R 20 = Z_to_bv 64 3 -> OP.getr R 21 = Z_to_bv 64 65536 ->
  OF.frame_mod mem0 M [(Z_to_bv 64 (SP - 8388608), 8388608)] -> W0.main_frame SP M ->
  A [] -> K [] ->
  (forall (M' : word -> option byte) (s' : PState) (mo' : Model)
          (y1 y5 y6 y7 x8 x9 y11 y12 y13 y14 y15 y16 y17 x18 x19 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31 : word),
     rd_base SP tid M' -> RHEAP s' [] M' -> OWN [] (GRD 0) s' mo' ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 (SP - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) y5 y6 y7 x8 x9
                                    (Z_to_bv 64 0) y11 y12 y13 y14 y15 y16 y17 x18 x19 (Z_to_bv 64 3) (Z_to_bv 64 65536)
                                    x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                               bvmap_empty (Z_to_bv 64 0x14b74) fc0 None M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo') A) ->
  (forall (pb : bptr) (buf : Z) (M' : word -> option byte) (s' : PState) (mo' : Model)
          (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x18 x24 x25 x26 x27 y28 y29 y30 y31 : word),
     rd_inv SP tid content (GRD 0) pb buf 65536 0 M' s' mo' -> AI j0 [pb] s' mo' ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 (SP - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 2) (Z_to_bv 64 buf)
                                    y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 65536)
                                    (Z_to_bv 64 0x22e59) (Z_to_bv 64 buf) x24 x25 x26 x27 y28 y29 y30 y31)
                               bvmap_empty (Z_to_bv 64 0x14998) fc0 None M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo') K) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) R (Z_to_bv 64 0x19400) M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) MODEL1) (ShapeAlg.t_alt2 A K).
Proof.
  intros A K R M G1 G2 G3 G4 G8 G10 G20 G21 FM MF HA0 HK0 KNULL KSOME.
  (* minv's channel-reader conjunct is the launch's (ia_channel_reader of amb_of inp). *)
  assert (MINV : minv MODEL1).
  { apply (minv_modelG path stdin0 fs0 tid ltac:(rewrite Hfile; discriminate) Htid Hcr 0).
    destruct Hvsp as (SPlo & SPhi & _). cbn [vm_init_sp]. exact (conj SPlo SPhi). }
  eapply (first_malloc_gen sp0 inp mbase rdraw tid regs0 mem0 Hva Hve Hvsp ME HCAN HSEC HATOP brk Hvl Hlau content
            Hbrk Hcr AI j0 RMF (FdFile path (Z_to_bv 64 0)) (GRD 0) (frame_ok_G_rd path stdin0 fs0 tid 0) model1_G_rd MINV
            A K R M (OP.getr R 18));
    try eassumption; try reflexivity.
  intros pb buf M' s' mo' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x24 x25 x26 x27 y28 y29 y30 y31 RI HAI _.
  eapply KSOME; eassumption.
Qed.
End FRONTF.
