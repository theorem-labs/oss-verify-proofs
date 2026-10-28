(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_loc_defs Pj_os_defs Pj_os_top Pj_loc_get.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memset Pj_defs Pj_stmts Pj_lftoi.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_iface.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition os_ctor_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo OS : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 672, q); (OS, OS + 288); (PJ_LOC_LO, PJ_LOC_HI)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q /\ OSFRESH m' OS /\ LOCB m'.

Lemma os_ctor_callZ : forall ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (q lo OS : Z) (canary : word) (junk : list byte),
  stk usegs m lo q -> lo <= q - 672 -> 0x110000 <= lo -> q < 2^62 ->
  pj_locale m -> rw_cells usegs m OS [CB 288 junk] -> q <= OS -> OS + 288 < 2^62 ->
  pj_consts m -> ssp_cells m canary -> rw_cells usegs m 0x10ec7b [C1 (Z_to_bv 8 0)] -> mem_inv usegs m ->
  evt usegs (os_ctor_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS m)
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OS) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_OS_CTOR) fc None m (seg_rom usegs)).
Proof.
  intros until junk. intros ST LO GLO Q62 LOC OSC QOS OS62 (_ & _ & GOTV & _ & LCK & _) (SSP1 & SSP2) NL MI.
  assert (Q0 : 0 <= q) by (destruct ST as [L0 _]; lia).
  assert (U : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  eapply evt_mono.
  - eapply (os_ctor_closed ra (Z_to_bv 64 q)) with (lo := lo) (OS := OS) (canary := canary) (junk := junk); rewrite ?U; try assumption.
  - intros ms' P. unfold os_ctor_post in P. rewrite U in P. exact P.
Qed.

Definition os_put_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo OS : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 256, q); (OS, OS + 288)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q /\ OSUSED m' OS /\ LOCB m'.

Lemma os_put_callZ : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (q lo OS BUF N CAP : Z) (bs : list byte),
  stk usegs m lo q -> lo <= q - 256 -> 0x110000 <= lo ->
  OSFRESH m OS -> LOCB m -> q <= OS -> OS + 288 < 2^62 -> OS mod 8 = 0 ->
  rw_cells usegs m BUF [CB (Z.to_nat CAP) bs] -> 0 <= N <= CAP -> 0 < BUF -> BUF + CAP < 2^62 ->
  (BUF + CAP <= lo \/ OS + 288 <= BUF) ->
  pj_consts m -> mem_inv usegs m ->
  evt usegs (os_put_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS m)
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 128)) (Z_to_bv 64 BUF) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_OS_PUT) fc None m (seg_rom usegs)).
Proof.
  intros until bs. intros ST LO GLO FR LB QOS OS62 OSAL BUFC HN HB HBC DISJ (NVT & WID & _ & CID & _ & _) MI.
  assert (Q0 : 0 <= q) by (destruct ST as [L0 _]; lia).
  assert (U : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  eapply evt_mono.
  - eapply (os_put_closed ra (Z_to_bv 64 q)) with (lo := lo) (OS := OS) (CAP := CAP) (bs := bs); rewrite ?U; try assumption.
  - intros ms' P. unfold os_put_post in P. rewrite U in P. exact P.
Qed.

Definition ios_dtor_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo OS fill : Z) (j148 j284 : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 48, q); (OS + 136, OS + 144)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q
    /\ rw_cells usegs m' (OS + 136) (ios_cells OS 0xd93a8 fill j148 j284).

Lemma ios_dtor_callZ : forall ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (q lo OS fill : Z) (j148 j284 : list byte),
  stk usegs m lo q -> lo <= q - 48 -> 0x110000 <= lo ->
  rw_cells usegs m (OS + 136) (ios_cells OS 0xd5fb8 fill j148 j284) -> q <= OS -> OS + 288 < 2^62 ->
  mem_inv usegs m ->
  evt usegs (ios_dtor_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS fill j148 j284 m)
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 136)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_IOS_DTOR) fc None m (seg_rom usegs)).
Proof.
  intros until j284. intros ST LO GLO IOC QOS OS62 MI.
  assert (Q0 : 0 <= q) by (destruct ST as [L0 _]; lia).
  assert (U : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  eapply evt_mono.
  - eapply (ios_dtor_closed ra (Z_to_bv 64 q)) with (lo := lo) (OS := OS) (fill := fill) (j148 := j148) (j284 := j284); rewrite ?U; try assumption.
  - intros ms' P. unfold ios_dtor_post in P. rewrite U in P. exact P.
Qed.

Lemma lb_below : forall s LB m a, RHEAP s LB m -> in_block LB a -> 0 < a < alloc_ceiling /\ (a < 0x10000 \/ 0x110000 <= a).
Proof.
  intros s LB m a H (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ H Hb) as (R1 & R2 & R3 & R4 & R5).
  unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in R4. lia.
Qed.

Definition okarm_setup_post (q0 : Z) (gp s0 s1 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo len : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x3ce08) (Z_to_bv 64 (q0 + -496)) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1
                  (Z_to_bv 64 (q0 + -128)) s0 s1 a3 a4 a5 a6 a7 (Z_to_bv 64 (q0 + -128)) (Z_to_bv 64 64) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 PJ_APPEND_ELEM) fc None m' (seg_rom usegs)
    /\ munch [(q0 - 496 - 672, q0 - 208); (q0 - 128, q0 - 40); (PJ_LOC_LO, PJ_LOC_HI)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (q0 + -496)
    /\ OSFRESH m' (q0 + -496) /\ LOCB m' /\ SBINV m' (q0 + -128) len (sb0 (q0 + -128)).

Lemma okarm_setup : forall x1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (q0 lo len : Z) (canary w0 w1 : word) (bsA jsb : list byte),
  stk usegs m lo (q0 + -496) -> lo <= q0 - 496 - 672 -> 0x110000 <= lo -> q0 < 2^62 ->
  pj_locale m -> pj_consts m -> ssp_cells m canary -> rw_cells usegs m 0x10ec7b [C1 (Z_to_bv 8 0)] -> mem_inv usegs m ->
  rw_cells usegs m (q0 + -496) [C8 w0; C8 w1; CB 272 bsA] ->
  rw_cells usegs m (q0 + -128) [CB 88 jsb] ->
  0 <= len <= SJ_PADMAX ->
  evt usegs (okarm_setup_post q0 gp w0 w1 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo len m)
    (MS (mkR x1 (Z_to_bv 64 (q0 + -496)) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PJ_OKARM) fc None m (seg_rom usegs)).
Proof.
  intros until jsb. intros ST LO GLO Q62 LOC PJC SSP NLK MI OSA SBA LEN.
  unfold PJ_OKARM, SJ_PADMAX in *.
  pose proof (munch_refl [(q0 - 496 - 672, q0 - 208); (q0 - 128, q0 - 40); (PJ_LOC_LO, PJ_LOC_HI)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.

  step. step. step. step.
  apply rw_cells_forget in OSA. destruct OSA as [bsA' OSA]. cbn [cells_size csize Nat.add] in OSA.
  call os_ctor_callZ; [exact ST| lia| lia| lia| exact LOC| exact OSA| lia| lia| exact PJC| exact SSP| exact NLK| exact MI|].
  destruct PC0 as (dum & j148 & j284 & OSC). destruct POST as (lj1 & lj2 & lj3 & lj4 & lj5 & lj6 & LBC). rename PC into ST.
  unfold os_cells, sb_cells, ios_cells in OSC. cbn [app] in OSC. unfold locb_cells in LBC.

  step. step. step. step. step. step.
  apply (rw_cells_split_CB usegs _ _ [] 88 jsb [] [64;8;8;8]%nat) in SBA; [|reflexivity]. cbn [mk_CB_cells app] in SBA.
  destruct (rw_cells_split_at _ _ _ 1%nat SBA) as [INL SBW]. cbn [firstn skipn cells_size csize Nat.add] in INL, SBW. clear SBA.
  replace (q0 + -128 + 64) with (q0 + -64) in SBW by lia.
  call memset_callZ; [exact INL| exact MI0| lia| lia| lia| lia|].

  step. step. fix_lit_store. step. fix_lit_store.
  lazymatch goal with H : rw_cells _ _ (q0 + -128) _ |- _ => rename H into SBUF0 end.
  lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.

  step. step. step. step.
  apply evt_done. unfold okarm_setup_post. do 13 eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST|].
  split. { exists dum, j148, j284. unfold os_cells, sb_cells, ios_cells. cbn [app]. exact OSC. }
  split. { exists lj1, lj2, lj3, lj4, lj5, lj6. exact LBC. }
  unfold SBINV, sb0. cbn [sb_buf sb_size sb_cap sb_blk sb_fuel].
  replace (q0 + -128 + 64) with (q0 + -64) by lia.
  split; [exact SBW|]. split; [lia|]. split; [eexists; exact SBUF0|]. split; [eexists; exact SBUF0|]. split; [apply le_n|].
  split; [| repeat split; reflexivity].
  replace (64 * 2 ^ sb_k _) with 64 by reflexivity. unfold PJ_CAPMAX, PJ_OUTMAX. lia.
Qed.

Lemma okarm_tail : forall {A} (k : M PState A) (Q : A -> PState -> machine_state -> Prop)
    (x1 gp t0 t1 t2 u0 u1 a0 a1 a2 a3 a4 a5 a6 a7 u2 u3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m00 m : mem) (s00 s : PState) (LBall : list block) (q0 lo B : Z) (errv : word) (bs88 : list byte),
  (forall s' ms', pj_okarm_post q0 gp s4 s5 s6 s7 s8 s9 s10 s11 s00 LBall lo B m00 s' ms' -> implM usegs k s' Q ms') ->
  frm0 fc -> mem_inv usegs m -> stk usegs m lo (q0 + -496) -> rw_cells usegs m LX_ERRNO [C4 errv] -> rauxv_ok m B ->
  ps_fa s = ps_fa s00 -> ps_so s = ps_so s00 -> RHEAP s LBall m -> lx_pres LBall (q0 + -496) (pj_okarm_X q0) m00 m ->
  rw_cells usegs m SJ_STATICS_LO (sj_cells true) -> LOCB m -> OSUSED m (q0 + -496) -> pj_consts m ->
  rw_cells usegs m (q0 + -128) [CB 88 bs88] ->
  alloc_ceiling <= lo -> 0x110000 <= lo -> lo <= q0 - 496 - 48 -> q0 <= B -> q0 < 2^62 ->
  implM usegs k s Q (MS (mkR x1 (Z_to_bv 64 (q0 + -496)) gp (Z_to_bv 64 RATP) t0 t1 t2 u0 u1 a0 a1 a2 a3 a4 a5 a6 a7 u2 u3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x3ce30) fc None m (seg_rom usegs)).
Proof.
  intros until bs88. intros KPOST FRM MI ST ERR AUX FA SO HEAP PRES IMPC LB OSU PJC SB88 CEIL GLO LO QB Q62.
  assert (ELX : LX_ERRNO = 977220) by reflexivity. rewrite ELX in ERR.
  unfold SJ_STATICS_LO in IMPC. cbn [sj_cells] in IMPC.
  destruct LB as (lj1 & lj2 & lj3 & lj4 & lj5 & lj6 & LBC). unfold locb_cells in LBC.
  destruct OSU as (pb & pp & ep & dum & j148 & j284 & OSC). unfold os_cells, sb_cells, ios_cells in OSC. cbn [app] in OSC.
  pose proof PJC as (_ & _ & GOTV & _).
  pose proof (munch_refl [(q0 - 496 - 48, q0 - 496 + 144)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold implM. iprefix.

  step. step. step. step. step. step.

  step. step. step. step. fix_lit_store.

  step. step. step. step. step. step. if_true. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with H : rw_cells _ mx (q0 + -496) _ |- _ => rename H into OSC1 end end.
  destruct (rw_cells_split_at _ _ _ 10%nat OSC1) as [OSL IOS]. cbn [firstn skipn cells_size csize Nat.add] in OSL, IOS. clear OSC1.

  step. step. replace (Z_to_bv 64 (q0 + -360)) with (Z_to_bv 64 (q0 + -496 + 136)) by (f_equal; lia).
  call ios_dtor_callZ; [exact ST| lia| lia| exact IOS| lia| lia| assumption|].
  rename PC into ST5. lazymatch goal with H : rw_cells _ _ (q0 + -496 + 136) _ |- _ => rename H into IOSC end.
  unfold ios_cells in IOSC.
  pose proof (rw_cells_join _ _ _ _ _ OSL IOSC ltac:(cbn [cells_size csize Nat.add]; lia)) as OSJ.
  apply rw_cells_forget in OSJ. destruct OSJ as [bsO OSJ]. cbn [app cells_size csize Nat.add] in OSJ. clear OSL IOSC.
  apply evt_done. to_implM. eapply KPOST. unfold pj_okarm_post. do 24 eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact FRM|]. split; [exact MI0|]. split; [exact ST5|]. split; [eassumption|].
  split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
  split; [exact FA|]. split; [exact SO|].
  split. { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
  split. { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
           intros a Ha [NX HC]. unfold pj_okarm_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI in NX. cbn [rin_ivs fst snd] in NX. cbn [outside].
           split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| pose proof (lb_below _ _ _ _ HEAP HC); lia| lia]. }
  split. { split; [exact IMPC| right]. exists lj1, lj2, lj3, lj4, lj5, lj6. exact LBC. }
  split; [exists bsO; exact OSJ| exists bs88; exact SB88].
Qed.

Lemma DOCREP_agree : forall (P : Z -> Prop) m m' LB0 DOC TAPE SBUF len tws sbs,
  agree_on P m m' -> (forall a, DOC <= a < DOC + 16 -> P a) -> (forall a, in_block LB0 a -> P a) ->
  DOCREP m LB0 DOC TAPE SBUF len tws sbs -> DOCREP m' LB0 DOC TAPE SBUF len tws sbs.
Proof.
  intros P m m' LB0 DOC TAPE SBUF len tws sbs AG HD HB (D1 & D2 & D3 & D4 & D5 & D6 & D7 & (bt & Bt1 & Bt2 & Bt3) & (bq & Bq1 & Bq2 & Bq3)).
  split. { eapply rw_cells_agree; [exact AG| exact D1|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply HD. lia. }
  split. { eapply bytes_at_agree; [exact AG| exact D2|]. intros a Ha. rewrite u64s_length, length_map in Ha. apply HB. exists bt. split; [exact Bt1| cbn in *; lia]. }
  split. { eapply bytes_at_agree; [exact AG| exact D3|]. intros a Ha. rewrite length_map in Ha. apply HB. exists bq. split; [exact Bq1| cbn in *; lia]. }
  split; [exact D4|]. split; [exact D5|]. split; [exact D6|]. split; [exact D7|].
  split; [exists bt; auto| exists bq; auto].
Qed.

Lemma implM_nulls_none : forall {A} (k : M PState A) s Q ms,
  implM usegs k s Q ms -> implM usegs (mbind (mbind (del_opt lops None) (fun _ => pj_free_nulls lops)) (fun _ => k)) s Q ms.
Proof. intros A k s Q ms H. exact H. Qed.
Lemma implM_nulls_k : forall {A} (k : M PState A) s Q ms,
  implM usegs k s Q ms -> implM usegs (mbind (pj_free_nulls lops) (fun _ => k)) s Q ms.
Proof. intros A k s Q ms H. exact H. Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis SER : ser_stmt TAPE_MAX_DEPTH.

  Theorem pj_okarm_proof : pj_okarm_stmt.
  Proof.
    unfold pj_okarm_stmt. intros until jsb.
    intros HEAP INT INS AUX QB B62 ST CEIL GLO LO ERR MI FRM AL16 Q496 LXS SJS SSP LEN CAP SRET GAP SBA DOCC OKR KPOST.
    unfold PJ_OKARM_STACK, GLOBALS_TOP in *.
    assert (Q62 : q0 < 2^62) by (clear - QB B62; lia).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in CEIL'.
    pose proof (lx_statics_pj _ LXS) as PJC.
    pose proof (LH_block_range _ _ _ _ HEAP INT) as TR. cbn [blk_addr blk_size fst snd] in TR. destruct TR as (_ & TAL16 & _).
    pose proof (RHEAP_need_locks _ _ _ HEAP) as NLK. unfold RMallocRep.RNEED_LOCKS in NLK.
    pose proof (sj_statics_locale _ _ SJS) as LOC. pose proof (sj_statics_impl _ _ SJS) as IMPC. unfold SJ_STATICS_LO in IMPC. cbn [sj_cells] in IMPC.
    assert (ELX : LX_ERRNO = 977220) by reflexivity. rewrite ELX in ERR.

    destruct OKR as [KO|(_ & tws & sbs & TB & SBB & WF & FAB & TL & SL)]; [exfalso; rewrite unsigned_lit in KO by lia; lia|].
    destruct (rw_cells_split_at _ _ _ 2%nat DOCC) as [DOC2 _]. cbn [firstn skipn cells_size csize Nat.add] in DOC2.
    assert (DR : DOCREP m LBall (q0 + -184) TAPE SBUF len tws sbs).
    { split; [exact DOC2|]. split; [exact TB|]. split; [exact SBB|]. split; [exact WF|]. split; [exact FAB|].
      unfold SJ_TAPE, SJ_SBUF, sj_cap. rewrite <- CAP. split; [lia|]. split; [lia|].
      split; [exists (ptp, TAPE, 8 * roundup64 (cap + 3)); split; [exact INT| cbn; lia]|].
      exists (psb, SBUF, roundup64 (5 * (cap / 3) + 64)); split; [exact INS| cbn; lia]. }
    pose proof WF as (WN & WSN & _ & _ & EL).

    destruct (rw_cells_split_at _ _ _ 2%nat SRET) as [SR2 SRT]. cbn [firstn skipn cells_size csize Nat.add] in SR2, SRT.
    pose proof (rw_cells_join _ _ _ _ _ SRT GAP ltac:(cbn [cells_size csize Nat.add]; lia)) as SRT'. apply rw_cells_forget in SRT'. destruct SRT' as [bsA SRT']. cbn [app cells_size csize Nat.add] in SRT'.
    pose proof (rw_cells_join _ _ _ _ _ SR2 SRT' ltac:(cbn [cells_size csize Nat.add]; lia)) as OSA. cbn [app] in OSA. clear SR2 SRT SRT' GAP SRET.

    eapply (PjImpl.implM_pj_chain_part usegs raw_malloc raw_free ps_so set_so_ps).
    unfold implM. iprefix.
    eapply evt_cut; [eapply okarm_setup with (len := len); [exact ST| lia| lia| exact Q62| exact LOC| exact PJC| exact SSP| exact NLK| exact MI| exact OSA| exact SBA| unfold SJ_PADMAX; clear - LEN; lia]|].
    intros ms1 P1. unfold okarm_setup_post in P1.
    destruct P1 as (r5 & r6 & r7 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m1 & -> & MU & WM & MI1 & ST1 & OSF1 & LB1 & INV1).
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    assert (HEAP1 : RHEAP s LBall m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|].
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor].
      right; left. cbn [fst snd]. unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. repeat constructor; cbn; lia. }
    apply (rw_cells_agree _ _ _ _ _ AG) in ERR; [| intros a Ha; cbn in Ha; cbn [outside]; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in IMPC; [| intros a Ha; cbn in Ha; cbn [outside]; lia].
    apply (DOCREP_agree _ _ _ _ _ _ _ _ _ _ AG) in DR; [| intros a Ha; cbn [outside]; lia| intros a Ha; pose proof (lb_below _ _ _ _ HEAP Ha); cbn [outside]; lia].
    apply (pj_consts_agree _ _ _ AG) in PJC; [| intros a Ha; cbn [outside]; lia].
    clear AG LOC SSP NLK OSA SBA MI ST.
    ihere. to_implM.
    eapply implM_bind.
    { eapply SER with (q := q0 + -496) (lo := lo) (B := B) (SB := q0 + -128) (st := sb0 (q0 + -128)) (DOC := q0 + -184) (LB0 := LBall) (errv := errv)
                      (j := Z.of_nat (length tws) - 1) (c' := Z.of_nat (length sbs));
        [cbn [sbblocks sb_blk sb0 app]; exact HEAP1| exact AUX1| lia| lia| exact ST1| exact CEIL| unfold GLOBALS_TOP; lia
        | unfold TAPE_MAX_DEPTH; rewrite ser_need_root; unfold PJ_SER_STACK, PJ_GROW_STACK, RMALLOC_STACK; lia
        | rewrite ELX; exact ERR| exact MI1| exact FRM| lia| lia| lia| lia| lia| unfold SJ_PADMAX; clear - LEN; lia| exact INV1| exact DR| clear - AL16; Z.div_mod_to_equations; lia| clear - TAL16; Z.div_mod_to_equations; lia| exact EL
        | lia| lia| lia| lia| unfold sb_acc1; cbn [sb_size sb0]; lia]. }
    cbv beta. intros c sM2 ms2 PO2. unfold ser_post in PO2.
    destruct PO2 as (v5 & v6 & v7 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & F2 & fc2 & m2 & errv2 & st2
                     & -> & MI2 & ST2 & ERR2 & AUX2 & FRM2 & FA2 & SO2 & -> & HEAP2 & INV2 & ACC2 & PRES12).
    replace (ret_pc (Z_to_bv 64 249352)) with (Z_to_bv 64 249352) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ELX in ERR2.
    clear TB SBB DOCC DOC2 EL WSN DR ERR AUX1 INV1 ACC2.

    assert (PRES02 : lx_pres LBall (q0 + -496) (pj_okarm_X q0) m m2).
    { eapply lx_pres_trans.
      - eapply lx_pres_of_munch; [exact MU| exact WM|].
        intros a Ha [NX HC]. unfold pj_okarm_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI in NX. cbn [rin_ivs fst snd] in NX. cbn [outside].
        destruct HC as [HC|[HC|HC]]; [lia| pose proof (lb_below _ _ _ _ HEAP HC); lia| lia].
      - eapply lx_pres_weaken; [exact PRES12| lia| intros b0 Hb0; exact Hb0|].
        intros a Ha. unfold pj_okarm_X. cbn [rin_ivs fst snd] in *. lia. }
    pose proof (agree_of_lx_pres _ _ _ _ _ PRES12) as AG.
    assert (STC : forall a, q0 + -496 <= a < q0 + -128 \/ 970568 <= a < 975064 -> lx_client LBall (q0 + -496) [(q0 + -128, q0 + -128 + 88)] a).
    { intros a Ha. split; [cbn [rin_ivs fst snd]; lia|]. destruct Ha as [Ha|Ha]; [left; lia| right; right].
      unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    destruct OSF1 as (dum & j148 & j284 & OSC). apply (rw_cells_agree _ _ _ _ _ AG) in OSC; [| intros a Ha; rewrite os_cells_size in Ha; apply STC; lia].
    destruct LB1 as (lj1 & lj2 & lj3 & lj4 & lj5 & lj6 & LBC). apply (rw_cells_agree _ _ _ _ _ AG) in LBC; [| intros a Ha; rewrite locb_cells_size in Ha; apply STC; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in IMPC; [| intros a Ha; cbn in Ha; apply STC; lia].
    apply (pj_consts_agree _ _ _ AG) in PJC; [| intros a Ha; apply lxs_addr_client; [unfold lxs_addr; do 5 right; exact Ha| cbn [rin_ivs fst snd]; lia]].
    clear AG STC MU WM HEAP1 MI1 ST1 PRES12.

    unfold sb_ch. cbn [ch_fuel ch_cap ch_blk fst snd].
    eapply (PjImpl.implM_pj_chain_stop usegs raw_malloc raw_free ps_so set_so_ps); [pose proof (SBINV_cap_pos _ _ _ _ INV2); lia|]. cbv beta.
    unfold SBINV in INV2. destruct st2 as [buf2 size2 cap2 blk2 fuel2]. cbn [sb_buf sb_size sb_cap sb_blk sb_fuel sbblocks] in *.
    destruct INV2 as (SBW & SZ2 & (bsb & BUF2) & (ji2 & INL) & FU2 & CAPB & BLK2). replace (q0 + -128 + 64) with (q0 + -64) in SBW by lia.
    assert (BF : 0 < buf2 /\ buf2 + cap2 < 2^62 /\ (buf2 + cap2 <= lo \/ q0 + -496 + 288 <= buf2)).
    { destruct blk2; [destruct BLK2 as (R1 & R2 & R3 & R4 & R5); unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in R4; lia| destruct BLK2 as (-> & -> & _); lia]. }
    pose proof (munch_refl [(q0 - 496 - 256, q0 - 496 + 288)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    unfold implM. iprefix.

    step. step. step. step. step.
    replace (Z_to_bv 64 (q0 + -368)) with (Z_to_bv 64 (q0 + -496 + 128)) by (f_equal; lia).
    call os_put_callZ; [exact ST2| lia| lia| exists dum, j148, j284; exact OSC| exists lj1, lj2, lj3, lj4, lj5, lj6; exact LBC| lia| lia| clear - AL16; Z.div_mod_to_equations; lia| exact BUF2| lia| lia| lia| lia
                      | exact PJC| exact MI2|].
    rename PC into ST3. rename PC0 into OSU3. rename POST into LB3. clear BUF2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HEAP3 : RHEAP sM2 (sbblocks (mkSb buf2 size2 cap2 blk2 fuel2) ++ LBall) m3).
    { eapply LH_frame; [exact HEAP2| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX3 : rauxv_ok m3 B).
    { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|]. unfold RAUXV_CELL. repeat constructor; cbn; lia. }
    apply (pj_consts_agree _ _ _ (agree_on_of_munch _ _ _ MU WM)) in PJC; [| intros a Ha; cbn [outside]; lia].
    assert (PRES03 : lx_pres LBall (q0 + -496) (pj_okarm_X q0) m m3).
    { eapply lx_pres_trans; [exact PRES02|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a Ha [NX HC]. unfold pj_okarm_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI in NX. cbn [rin_ivs fst snd] in NX. cbn [outside].
      destruct HC as [HC|[HC|HC]]; [lia| pose proof (lb_below _ _ _ _ HEAP HC); lia| lia]. }
    clear MU WM HEAP2 AUX2 PRES02.

    step. step. step.
    pose proof (rw_cells_join _ _ _ _ _ INL SBW ltac:(cbn [cells_size csize Nat.add]; lia)) as SB88.
    apply rw_cells_forget in SB88. destruct SB88 as [bs88 SB88]. cbn [app cells_size csize Nat.add] in SB88. clear INL SBW.
    destruct blk2 as [b|].
    -
      destruct BLK2 as (R1 & R2 & R3 & R4 & R5). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in R4.
      if_cases KG1. { exfalso. unfold bv_eqb in KG1. rewrite !unsigned_lit in KG1 by lia. apply Z.eqb_eq in KG1. lia. }
      step. if_cases KG2. { exfalso. unfold bv_eqb in KG2. rewrite !unsigned_lit in KG2 by lia. apply Z.eqb_eq in KG2. lia. }
      clear KG1 KG2. step. ihere. to_implM.
      cbn [sbblocks sb_blk sb_buf sb_cap app] in HEAP3.
      apply implM_bind_assoc. eapply implM_bind.
      { eapply (opdel_arr_proof HF) with (B := B) (lo := lo) (A := buf2) (n := cap2);
          [exact HEAP3| left; reflexivity| exact AUX3| lia| exact ST3| exact CEIL| unfold RFREE_STACK; lia| rewrite ELX; exact ERR2| exact MI| lia]. }
      cbv beta. intros [] sM4 ms4 PO4. unfold free_postZ in PO4.
      destruct PO4 as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m4
                       & -> & MI4 & ST4 & ERR4 & AUX4 & PRES34 & FA4 & SO4 & HEAP4).
      rewrite (lb_remove_hd _ _ _ _ (LH_nodup _ _ _ HEAP3)) in PRES34, HEAP4.
      replace (ret_pc (Z_to_bv 64 249392)) with (Z_to_bv 64 249392) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_of_heap_pres _ _ _ _ PRES34) as AG.
      assert (STC : forall a, q0 + -496 <= a \/ 970568 <= a < 975064 \/ lxs_addr a -> rclient_addr LBall (q0 + -496) a).
      { intros a [Ha|[Ha|Ha]]; [left; lia| right; left| ].
        - unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia.
        - destruct (lxs_addr_client LBall (q0 + -496) [] a Ha ltac:(cbn; tauto)) as [_ [H|[H|H]]]; [left; exact H| right; right; exact H| right; left; exact H]. }
      destruct OSU3 as (pb & pp & ep & dum3 & i148 & i284 & OSC). apply (rw_cells_agree _ _ _ _ _ AG) in OSC; [| intros a Ha; rewrite os_cells_size in Ha; apply STC; lia].
      destruct LB3 as (kj1 & kj2 & kj3 & kj4 & kj5 & kj6 & LBC). apply (rw_cells_agree _ _ _ _ _ AG) in LBC; [| intros a Ha; rewrite locb_cells_size in Ha; apply STC; lia].
      apply (rw_cells_agree _ _ _ _ _ AG) in IMPC; [| intros a Ha; cbn in Ha; apply STC; lia].
      apply (rw_cells_agree _ _ _ _ _ AG) in SB88; [| intros a Ha; cbn in Ha; apply STC; lia].
      apply (pj_consts_agree _ _ _ AG) in PJC; [| intros a Ha; apply STC; right; right; unfold lxs_addr; do 5 right; exact Ha].
      apply implM_nulls_k.
      eapply okarm_tail with (m00 := m) (s00 := s);
        [exact KPOST| exact FRM2| exact MI4| exact ST4| exact ERR4| exact AUX4| congruence| congruence| exact HEAP4
        | eapply lx_pres_trans; [exact PRES03| apply lx_pres_of_heap_pres; exact PRES34]
        | exact IMPC| exists kj1, kj2, kj3, kj4, kj5, kj6; exact LBC| exists pb, pp, ep, dum3, i148, i284; exact OSC| exact PJC| exact SB88
        | exact CEIL| lia| lia| exact QB| exact Q62].
    -
      destruct BLK2 as (-> & -> & ->).
      if_true. ihere. to_implM. apply implM_nulls_none.
      cbn [sbblocks sb_blk app] in HEAP3.
      eapply okarm_tail with (m00 := m) (s00 := s);
        [exact KPOST| exact FRM2| exact MI| exact ST3| rewrite ELX; exact ERR2| exact AUX3| exact FA2| exact SO2| exact HEAP3| exact PRES03
        | exact IMPC| exact LB3| exact OSU3| exact PJC| exact SB88| exact CEIL| lia| lia| exact QB| exact Q62].
  Qed.
End Proofs.

End WithCeiling0.
