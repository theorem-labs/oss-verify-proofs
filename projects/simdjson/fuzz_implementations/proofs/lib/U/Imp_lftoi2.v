(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel ImpModel Target Prog ImpImpl.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_h_arith.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Layout Exit Printf_wfile Pj_loc_defs Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Sj_h_create Sj_h_pdtor Imp_defs Imp_kit Imp_iface.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition pdtor0_post (ra : word) (q lo : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (P : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 32, q); (P + 8, P + 16); (P + 24, P + 40); (P + 64, P + 72)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q
    /\ rw_cells usegs m' (P + 8) [C8 (Z_to_bv 64 0)] /\ rw_cells usegs m' (P + 24) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] /\ rw_cells usegs m' (P + 64) [C8 (Z_to_bv 64 0)].

Lemma pdtor0_spec : forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo P : Z),
  stk usegs m lo q -> GLOBALS_TOP <= lo -> lo <= q - 32 -> 0 <= q < 2^63 -> mem_inv usegs m -> q <= P -> P + 80 < 2^63 ->
  rw_cells usegs m (P + 8) [C8 (Z_to_bv 64 0)] -> rw_cells usegs m (P + 24) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> rw_cells usegs m (P + 64) [C8 (Z_to_bv 64 0)] ->
  evt usegs (pdtor0_post ra q lo gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SJ_PARSER_DTOR) fc None m (seg_rom usegs)).
Proof.
  intros until P. intros ST GLO LO Hq MI QP PH P8 P24 P64.
  unfold SJ_PARSER_DTOR, GLOBALS_TOP in *.
  pose proof (munch_refl [(q - 32, q); (P + 8, P + 16); (P + 24, P + 40); (P + 64, P + 72)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  step. carve_frame 16%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 16 junk [] [8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

  hstep. hstep. step. step. hstep. step. if_true.

  step. step.
  step. carve_frame 16%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 16 junk0 [] [8;8]%nat) in FR0; [|reflexivity]. cbn [mk_CB_cells app] in FR0.

  hstep. hstep. step. step. hstep. step. if_true. step. hstep. step. if_true.
  step. step. release_frame FR0 ST (q + -16). step. step.

  step. hstep. step. if_true. step. step. release_frame FR ST q. step. step.
  apply evt_done. unfold pdtor0_post. do 15 eexists. eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [|eassumption]; intros x Hx; cbn [outside] in Hx |- *; lia|].
  split; [eassumption|]. split; [eassumption|]. split; [exact ST|].
  split; [eassumption| split; [eassumption| eassumption]].
Qed.

Definition impl0_tail_cells (I : Z) (m : mem) : Prop :=
  exists j1 j17 j57 j100, rw_cells usegs m I (impl0_cells 0 j1 j17 j57 j100).

Definition REST6 (psb ptp pia poc pix pim : bptr) (p : bptr) : M PState (Z * option bptr) :=
  mbind (del lops psb) (fun _ => mbind (del lops ptp) (fun _ => mbind (del lops pia) (fun _ => mbind (del lops poc) (fun _ =>
  mbind (del lops pix) (fun _ => mbind (del lops pim) (fun _ => mret (0, Some p))))))).

Lemma out0_bytes : forall m A, rw_cells usegs m A [C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
  rw_cells usegs m A [C1 (Z_to_bv 8 0); CB 7 (MallocRep.zeros 7); C8 (wz 0); C8 (wz 0)].
Proof.
  intros m A H. eapply rw_cells_recast; [exact H| | |].
  - cbn. repeat split.
  - vm_compute. reflexivity.
  - reflexivity.
Qed.

Lemma out_long_bytes : forall m A S L DATA, rw_cells usegs m A (out_long S L DATA) ->
  rw_cells usegs m A [C1 (Z_to_bv 8 (bv_unsigned (wz (S + 1)))); CB 7 (Z_to_le_bytes 7 (Z.shiftr (bv_unsigned (wz (S + 1))) 8)); C8 (wz L); C8 (wz DATA)].
Proof.
  intros m A S L DATA H. eapply rw_cells_recast; [exact H| | reflexivity| reflexivity].
  cbn. repeat split. all: apply length_Z_to_le_bytes.
Qed.

Lemma land1_byte : forall x, Z.land (bv_unsigned (Z_to_bv 8 x)) 1 = Z.land x 1.
Proof.
  intros x. rewrite Z_to_bv_unsigned, bv_wrap8_mod, <- (Z.land_ones x 8) by lia. rewrite <- Z.land_assoc.
  change (Z.land (Z.ones 8) 1) with 1. reflexivity.
Qed.

Lemma imp_out_agree : forall P m m' q ocp, agree_on P m m' -> imp_out m q ocp -> (forall a, q + 432 <= a < q + 456 -> P a) -> imp_out m' q ocp.
Proof.
  intros P m m' q [b|] AG H HP; cbn [imp_out] in *.
  - destruct H as (L & H1 & H2). exists L. split; [| exact H2]. eapply rw_cells_agree; [exact AG| exact H1|]. intros a Ha. apply HP. unfold out_long in Ha. cbn in Ha. lia.
  - destruct H as (b0 & j23 & H1 & H2). exists b0, j23. split; [| exact H2]. eapply rw_cells_agree; [exact AG| exact H1|]. intros a Ha. apply HP. unfold out_short in Ha. cbn in Ha. lia.
Qed.

Ltac stk_norm ST :=
  cbn [cells_size csize Nat.add] in ST;
  lazymatch type of ST with
  | stk _ _ _ (?b0 + ?c + Z.of_nat ?n) => let v := eval vm_compute in (c + Z.of_nat n)%Z in replace (b0 + c + Z.of_nat n)%Z with (b0 + v)%Z in ST by lia
  | stk _ _ _ (?b0 + Z.of_nat ?n) => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in ST
  | _ => idtac
  end.
Ltac absorb1 ST :=
  lazymatch type of ST with stk _ ?m ?lo ?top =>
    match goal with
    | FR : rw_cells _ m top _ |- _ => eapply stk_release in FR; [| exact ST| lia]; clear ST; rename FR into ST; stk_norm ST
    | IS : stk _ m top ?hi |- _ =>
        tryif constr_eq IS ST then fail else
        (let ST2 := fresh "ST" in pose proof (stk_merge _ _ _ _ _ ST IS ltac:(lia)) as ST2; clear ST IS; rename ST2 into ST)
    end
  end.

Lemma lftoi_tail_end : rfree_stmt -> forall (ocp : option block) (IMPL IDX OC IA TAPE SBUF : Z) (capw lcapv : word) (psb ptp pia poc pix pim : bptr)
    (s2 : PState) (m2 : mem) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (errv2 : word)
    (nsi nxt capv md bufv lenv docv : word) (b48 b49 : byte) (p12 p28 p50 j57 : list byte)
    (ra : word) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word) (s : PState) (LB OW' : list block) (D : Z) (d : list Z) (v : option bptr) (p : bptr)
    (q lo B : Z) (canary : word) (m : mem) (cap : Z) (b328 : byte) (j329 : list byte) (w332 : word),
  frm0 fc' -> mem_inv usegs m2 -> stk usegs m2 lo q -> rw_cells usegs m2 LX_ERRNO [C4 errv2] -> rauxv_ok m2 B ->
  ps_fa s2 = ps_fa s -> ps_so s2 = ps_so s ->
  alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - 65536 -> 0 <= q -> q + IMP_FRAME <= B -> B < 2^62 ->
  RHEAP s LB m -> lx_statics m -> stderr_wfile m -> ssp_cells m canary -> payload_ok m LB D d ->
  RHEAP s2 (ocp_blocks ocp ++ (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 cap + 9)) :: (pim, IMPL, 96)
              :: (ptp, TAPE, 8 * roundup64 (cap + 3)) :: (psb, SBUF, roundup64 (5 * (cap / 3) + 64)) :: OW' ++ LB) m2 ->
  xnew v p OW' -> imp_vec m2 (OW' ++ LB) (Some p) -> sj_statics m2 true -> aex_tbl m2 3 ->
  lx_pres LB (q + IMP_FRAME) [LXW_IMP; LXW_SJ; LXW_AEX] m m2 ->
  rw_cells usegs m2 SJ_DPI_VPTR dpi_vtable_cells ->
  stk usegs m2 q (q + 336) ->
  rw_cells usegs m2 (q + 336) [C8 (Z_to_bv 64 IMPL)] ->
  rw_cells usegs m2 (q + 344) [C1 b328; CB 3 j329; C4 w332] ->
  rw_cells usegs m2 (q + 352) [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 capw] ->
  rw_cells usegs m2 (q + 376) (p48_cells (Z_to_bv 8 0) j57 (Z_to_bv 64 (match ocp with Some b => blk_addr b | None => 0 end)) lcapv) ->
  stk usegs m2 (q + 408) (q + 952) ->
  rw_cells usegs m2 (q + 952) (imp_saves ra S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11) ->
  rw_cells usegs m2 IMPL (impl_cells16 (Z_to_bv 64 SJ_DPI_VPTR) nsi p12 (Z_to_bv 64 IDX) nxt p28 capv md b48 b49 p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv) ->
  implM usegs (match ocp with Some b => mbind (del lops (blk_id b)) (fun _ => REST6 psb ptp pia poc pix pim p) | None => REST6 psb ptp pia poc pix pim p end) s2
    (rfuzz_one_post ra (Z_to_bv 64 (q + IMP_FRAME)) gp (Z_to_bv 64 RATP) S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s LB D d v lo B canary m)
    (MS (mkR x1 (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 (q + 328)) (Z_to_bv 64 (-136)) a0 a1 a2 a3 a4 a5 a6 a7 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 t3 t4 t5 t6)
        F' (Z_to_bv 64 0x3f284) fc' None m2 (seg_rom usegs)).
Proof.
  intros HF. intros until w332.
  intros FRM MI2 ST2 ERR2 AUX2 FA SO CEIL GLO LO Q0 QB B62 HEAP0 LXS0 SEW0 SSP0 PL0 HEAP2 XN VEC2 SJS2 AEX2 PRES2 VTD2 ISA F320 F328 F336 F360 ISC F936 THISC.
  unfold IMP_FRAME, GLOBALS_TOP in *.
  pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
  assert (ELX : LX_ERRNO = 1004708) by reflexivity.
  assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
  { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP0 Hb) as (_ & _ & _ & BC & _). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
  assert (BLB2 : forall a, in_block (OW' ++ LB) a -> a < alloc_ceiling).
  { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP2 ltac:(apply in_or_app; right; do 6 right; exact Hb)) as (_ & _ & _ & BC & _).
    unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
  pose proof (munch_refl [(q - 16, q)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.

  unfold implM. iprefix. step. step. ihere. to_implM. unfold REST6. clear MU WM.
  replace (q + 336) with (q + 328 + 8) in F320 by lia. replace (q + 352) with (q + 328 + 24) in F336 by lia. replace (q + 376) with (q + 328 + 48) in F360 by lia.
  eapply (pdtor_cps HF (mret (0, Some p))) with (B := B) (lo := lo);
    [exact HEAP2| exact AUX2| lia| exact ST2| exact CEIL'| unfold GLOBALS_TOP; lia| unfold RFREE_STACK; lia| rewrite ELX; exact ERR2| exact MI2| lia| lia| lia
    | exact VTD2| exact F320| exact F336| exact F360| exact THISC|].
  intros s3 ms3 PO3. unfold hpost in PO3.
  destruct PO3 as (v5 & v6 & v7 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m3 & -> & MI3 & ST3 & (errv3 & ERR3) & AUX3 & FA3 & SO3 & RR).
  unfold pdtor_R in RR. destruct RR as (HEAP3 & PRES23 & PIMPL3 & DOCC3 & P483).
  apply implM_ret.
  replace (ret_pc (Z_to_bv 64 0x3f28c)) with (Z_to_bv 64 0x3f28c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  pose proof (agree_of_lx_pres _ _ _ _ _ PRES23) as AG3.
  clear F320 F336 F360 THISC VTD2.
  apply (rw_cells_agree _ _ _ _ _ AG3) in F328; [| intros a Ha; cbn in Ha; split; [unfold pdtor_X; cbn [rin_ivs fst snd]; lia| left; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG3) in F936; [| intros a Ha; cbn in Ha; split; [unfold pdtor_X; cbn [rin_ivs fst snd]; lia| left; lia]].
  apply (stk_agree _ _ _ _ _ AG3) in ISA; [| intros a Ha; split; [unfold pdtor_X; cbn [rin_ivs fst snd]; lia| left; lia]].
  apply (stk_agree _ _ _ _ _ AG3) in ISC; [| intros a Ha; split; [unfold pdtor_X; cbn [rin_ivs fst snd]; lia| left; lia]].
  replace (q + 328 + 8) with (q + 336) in PIMPL3 by lia. replace (q + 328 + 24) with (q + 352) in DOCC3 by lia. replace (q + 328 + 48) with (q + 376) in P483 by lia.
  unfold p48_cells in P483. unfold imp_saves in F936.
  pose proof (munch_refl [(q - 16, q)]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.

  zstep. zstep. step. if_false. step.
  do 13 step. step.

  rename ST3 into ST. repeat (absorb1 ST).
  lazymatch type of ST with stk _ _ lo (q + 1056) => idtac | ?T => fail 100 "frame release incomplete:" T end.
  step.

  assert (PRESF : lx_pres LB (q + 1056) [LXW_IMP; LXW_SJ; LXW_AEX] m m3).
  { eapply lx_pres_trans; [exact PRES2|]. eapply (lx_pres_sub LB (q + 1056) _ _ _ _ _ _ PRES23); [lia| intros b0 Hb0; apply in_or_app; right; exact Hb0|].
    intros a Ha NX. unfold pdtor_X in Ha. cbn [rin_ivs fst snd] in Ha. refine (conj _ (conj _ _)); [lia| intros IB; specialize (BLB a IB); lia| lia]. }
  assert (PRESF5 : lx_pres LB (q + 1056) LXW_CLIENT m m3).
  { eapply lx_pres_weaken; [exact PRESF| lia| intros b0 Hb0; exact Hb0| intros a Ha; unfold LXW_CLIENT; cbn [rin_ivs fst snd] in Ha |- *; tauto]. }
  pose proof (agree_of_lx_pres _ _ _ _ _ PRESF) as AGF.
  assert (LXSF : lx_statics m3).
  { eapply lx_statics_agree; [exact AGF| | exact LXS0]. intros a Ha. apply lxs_addr_client; [exact Ha|].
    unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha.
    unfold LXW_IMP, LXW_SJ, LXW_AEX, IMP_VEC_LO, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia. }
  assert (SJSF : sj_statics m3 true).
  { eapply sj_statics_agree; [exact AG3| | exact SJS2]. intros a Ha. pose proof (sjs_addr_lt a Ha) as [Ra Rb]. unfold GLOBALS_TOP in Ra.
    split; [unfold pdtor_X; cbn [rin_ivs fst snd]; lia| right; right; split; [lia| exact Rb]]. }
  assert (AEXF : aex_tbl m3 3).
  { eapply aex_tbl_agree; [exact AG3| | exact AEX2]. intros a Ha. unfold aex_tbl_addr, AEX in Ha.
    split; [unfold pdtor_X; cbn [rin_ivs fst snd]; lia| right; right; split; [lia|]].
    unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
  assert (VECF : imp_vec m3 (OW' ++ LB) (Some p)).
  { eapply imp_vec_agree; [exact AG3| | | exact VEC2].
    - intros a Ha. pose proof (impvec_addr_lt a Ha) as [Ra Rb]. unfold GLOBALS_TOP in Ra. split; [unfold pdtor_X; cbn [rin_ivs fst snd]; lia| right; right; split; [lia| exact Rb]].
    - intros a Ha. split; [specialize (BLB2 a Ha); unfold pdtor_X; cbn [rin_ivs fst snd]; lia| right; left; exact Ha]. }
  assert (SEWF : stderr_wfile m3).
  { eapply stderr_wfile_agree; [exact AGF| | exact SEW0]. intros a Ha. apply stderr_addr_client; [exact Ha|]. unfold stderr_addr in Ha.
    unfold LXW_IMP, LXW_SJ, LXW_AEX, IMP_VEC_LO, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia. }
  assert (PLF : payload_ok m3 LB D d).
  { eapply payload_ok_agree; [exact AGF| exact PL0|]. intros b0 a Hb Ha. split; [| right; left; exists b0; split; assumption].
    pose proof (LH_block_range _ _ _ _ HEAP0 Hb) as (_ & _ & _ & _ & BS). unfold LXW_IMP, LXW_SJ, LXW_AEX, IMP_VEC_LO, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd].
    clear - Ha BS. lia. }
  apply evt_done. unfold rfuzz_one_post. cbn [fst snd].
  do 15 eexists. exists F', fc', m3, p, OW'.
  split; [cbv delta [mkR]; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact XN|].
  split.
  { unfold lx_post_env, lx_env. rewrite !(unsigned_lit (q + 1056)) by lia.
    split; [| split; [exact FRM| split; [exact PRESF5| split; congruence]]].
    exists errv3.
    split; [exact HEAP3|]. split; [exact LXSF|]. split; [exists true; exact SJSF|]. split; [exact SEWF|].
    split; [pose proof (ssp_canary_0 _ _ _ _ HEAP0 SSP0) as EC; rewrite EC; eapply RHEAP_ssp; exact HEAP3|].
    split; [exact AUX3|]. split; [lia|]. split; [lia|]. split; [exact ST|].
    split; [exact CEIL'|]. split; [unfold GLOBALS_TOP; lia|].
    split; [unfold errno_addr, RATP; rewrite unsigned_lit by lia; rewrite ELX in ERR3; exact ERR3|]. split; [reflexivity| exact MI3]. }
  split; [exact SJSF|]. split; [exact VECF|]. split; [exact AEXF| exact PLF].
Qed.

Lemma lftoi_tail : rfree_stmt -> forall (ostr ocp : option block) (IMPL IDX OC IA TAPE SBUF : Z) (capw lcapv : word) (psb ptp pia poc pix pim : bptr)
    (sJ : PState) (mJ : mem) (x1 gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s11 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (errvJ : word)
    (nsi nxt capv md bufv lenv docv : word) (b48 b49 : byte) (p12 p28 p50 j57 : list byte) (ne : Z)
    (ra : word) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word) (s : PState) (LB OW' : list block) (D : Z) (d : list Z) (v : option bptr) (p : bptr)
    (q lo B : Z) (canary : word) (m : mem) (cap : Z) (j16 jgap jel jsb : list byte) (w16 w24 w32 w40 w48 : word) (b312 b328 : byte) (j313 j329 : list byte) (w332 : word),
  frm0 fc' -> mem_inv usegs mJ -> stk usegs mJ lo q -> rw_cells usegs mJ LX_ERRNO [C4 errvJ] -> rauxv_ok mJ B ->
  ps_fa sJ = ps_fa s -> ps_so sJ = ps_so s ->
  alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - 65536 -> 0 <= q -> q + IMP_FRAME <= B -> B < 2^62 ->
  RHEAP s LB m -> lx_statics m -> stderr_wfile m -> ssp_cells m canary -> payload_ok m LB D d ->
  RHEAP sJ (ocp_blocks ostr ++ ocp_blocks ocp ++ (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 cap + 9)) :: (pim, IMPL, 96)
              :: (ptp, TAPE, 8 * roundup64 (cap + 3)) :: (psb, SBUF, roundup64 (5 * (cap / 3) + 64)) :: OW' ++ LB) mJ ->
  xnew v p OW' -> imp_vec mJ (OW' ++ LB) (Some p) -> sj_statics mJ true -> aex_tbl mJ 3 ->
  lx_pres LB (q + IMP_FRAME) [LXW_IMP; LXW_SJ; LXW_AEX] m mJ ->
  (ne = 0 \/ ne = 1) ->

  rw_cells usegs mJ q [CB 8 j16] -> rw_cells usegs mJ (q + 8) [C8 (Z_to_bv 64 1); C8 w16; C8 w24; C8 w32; C8 w40; C8 w48] ->
  rw_cells usegs mJ (q + 56) [CB 264 jgap] ->
  rw_cells usegs mJ (q + 320) [C8 (Z_to_bv 64 SJ_FALLBACK)] ->
  rw_cells usegs mJ (q + 328) [C1 b312; CB 7 j313] ->
  rw_cells usegs mJ (q + 336) [C8 (Z_to_bv 64 IMPL)] ->
  rw_cells usegs mJ (q + 344) [C1 b328; CB 3 j329; C4 w332] ->
  rw_cells usegs mJ (q + 352) [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 capw] ->
  rw_cells usegs mJ (q + 376) (p48_cells (Z_to_bv 8 0) j57 (Z_to_bv 64 (match ocp with Some b => blk_addr b | None => 0 end)) lcapv) ->
  rw_cells usegs mJ (q + 408) [CB 24 jel] ->
  imp_out mJ q ostr ->
  impl0_tail_cells (q + 456) mJ -> impl0_tail_cells (q + 592) mJ -> impl0_tail_cells (q + 728) mJ ->
  rw_cells usegs mJ (q + 864) [CB 88 jsb] ->
  rw_cells usegs mJ (q + 952) (imp_saves ra S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11) ->
  rw_cells usegs mJ IMPL (impl_cells16 (Z_to_bv 64 SJ_DPI_VPTR) nsi p12 (Z_to_bv 64 IDX) nxt p28 capv md b48 b49 p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv) ->
  implM usegs (mbind (del_opt lops (option_map blk_id ostr)) (fun _ =>
               match ocp with Some b => mbind (del lops (blk_id b)) (fun _ => REST6 psb ptp pia poc pix pim p) | None => REST6 psb ptp pia poc pix pim p end)) sJ
    (rfuzz_one_post ra (Z_to_bv 64 (q + IMP_FRAME)) gp (Z_to_bv 64 RATP) S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s LB D d v lo B canary m)
    (MS (mkR x1 (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 0) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 136) (Z_to_bv 64 1) s4 s5 s6 s7 (Z_to_bv 64 ne)
             (Z_to_bv 64 (q + IMP_IMPLS)) (Z_to_bv 64 0) s11 t3 t4 t5 t6)
        F' (Z_to_bv 64 IMP_OKARM_END) fc' None mJ (seg_rom usegs)).
Proof.
  intros HF. intros until w332.
  intros FRM MI ST ERR AUX FA SO CEIL GLO LO Q0 QB B62 HEAP0 LXS0 SEW0 SSP0 PL0 HEAP XN VEC SJS AEXT PRES NE F0 F16 F40 F304 F312 F320 F328 F336 F360 F392 OUT T1 T2 T3 F848 F936 THISC.
  unfold IMP_OKARM_END, IMP_FRAME, IMP_IMPLS, GLOBALS_TOP in *.
  pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
  assert (ELX : LX_ERRNO = 1004708) by reflexivity. rewrite ELX in ERR.
  pose proof (munch_refl [(q - 32, q); (q + 456, q + 864)]%Z mJ) as MU. pose proof (wmono_refl usegs mJ) as WM.
  unfold implM. iprefix.

  zstep. zstep. step. if_false. step.

  lazymatch goal with |- evt _ ?QQ _ =>
    assert (K : forall a0' a2' s7' : word, evt usegs QQ
      (MS (mkR x1 (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 136) s1 a0' a1 a2' a3 a4 a5 a6 a7 (Z_to_bv 64 136) (Z_to_bv 64 1) s4 s5 s6 s7' (Z_to_bv 64 ne)
               (Z_to_bv 64 (q + 320)) (Z_to_bv 64 1) s11 t3 t4 t5 t6) F' (Z_to_bv 64 0x3f260) fc' None mJ (seg_rom usegs))) end.
  2:{ destruct NE as [-> | ->].
      - if_true. step. step. step. if_true. apply K.
      - if_false. step. step. if_true. apply K. }
  intros a0' a2' s7'.

  step. step.

  Ltac open_slot T QQ O :=
    let TC := fresh "TC" in let j1 := fresh "j1" in let j17 := fresh "j17" in let j57 := fresh "j57" in let j100 := fresh "j100" in
    destruct T as (j1 & j17 & j57 & j100 & TC); unfold impl0_cells in TC; cbv delta [MallocRep.wz] in TC;
    let Ta := fresh "Ta" in let Tr := fresh "Tr" in let Tp8 := fresh "Tp8" in let Tr2 := fresh "Tr" in let Tb := fresh "Tb" in let Tr3 := fresh "Tr" in
    let Tp24 := fresh "Tp24" in let Tr4 := fresh "Tr" in let Tc := fresh "Tc" in let Tr5 := fresh "Tr" in let Tp64 := fresh "Tp64" in let Tr6 := fresh "Tr" in
    let Td := fresh "Td" in let Tout := fresh "Tout" in
    split_cells TC 3%nat Ta Tr; split_cells Tr 1%nat Tp8 Tr2; split_cells Tr2 3%nat Tb Tr3; split_cells Tr3 2%nat Tp24 Tr4;
    split_cells Tr4 4%nat Tc Tr5; split_cells Tr5 1%nat Tp64 Tr6; split_cells Tr6 5%nat Td Tout; apply out0_bytes in Tout.

  Ltac walk_slot FF FC QQ LO O :=
    let a8 := eval vm_compute in (O + 8)%Z in let a24 := eval vm_compute in (O + 24)%Z in let a64 := eval vm_compute in (O + 64)%Z in
    match goal with H : rw_cells _ _ (QQ + a8)%Z _ |- _ => replace (QQ + a8)%Z with (QQ + O + 8)%Z in H by lia end;
    match goal with H : rw_cells _ _ (QQ + a24)%Z _ |- _ => replace (QQ + a24)%Z with (QQ + O + 24)%Z in H by lia end;
    match goal with H : rw_cells _ _ (QQ + a64)%Z _ |- _ => replace (QQ + a64)%Z with (QQ + O + 64)%Z in H by lia end;
    step; zstep; step; if_true; step; step;
    call (pdtor0_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FF FC _ QQ LO);
      [ eassumption | unfold GLOBALS_TOP; lia | lia | lia | assumption | lia | lia | eassumption | eassumption | eassumption | ];
    try (replace (QQ + O + 8)%Z with (QQ + a8)%Z in * by lia); try (replace (QQ + O + 24)%Z with (QQ + a24)%Z in * by lia); try (replace (QQ + O + 64)%Z with (QQ + a64)%Z in * by lia);
    zstep; zstep; step; if_true.
  pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; apply in_or_app; right; do 3 right; left; reflexivity)) as BRI.
  cbn [blk_addr blk_size fst snd] in BRI. unfold rblock_range, OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BRI. destruct BRI as (BI0 & _ & _ & BIC & BIS).
  unfold p48_cells in F360. unfold impl_cells16 in THISC.
  open_slot T3 q 736. open_slot T2 q 600. open_slot T1 q 464.
  walk_slot F' fc' q lo 736.
  walk_slot F' fc' q lo 600.
  walk_slot F' fc' q lo 464.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  lazymatch goal with H : stk _ m1 _ _ |- _ => rename H into ST1 end.
  lazymatch goal with H : mem_inv _ m1 |- _ => rename H into MI1 end.
  lazymatch goal with H : rw_cells _ m1 1004708 _ |- _ => rename H into ERR1 end.
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG1.
  assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
  { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP0 Hb) as (_ & _ & _ & BC & _). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
  assert (BLB2 : forall a, in_block (OW' ++ LB) a -> a < alloc_ceiling).
  { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; apply in_or_app; right; do 6 right; exact Hb)) as (_ & _ & _ & BC & _).
    unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
  assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB (q + 1056) [LXW_IMP; LXW_SJ; LXW_AEX] a -> outside [(q - 32, q); (q + 456, q + 864)]%Z a).
  { intros a Ha [HX HC]. cbn [outside]. refine (conj _ (conj _ I)); (destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]). }
  eapply LH_frame in HEAP; [| exact MU| exact WM| constructor; [apply W_ok_stack; cbn; lia| constructor; [apply W_ok_stack; cbn; lia| constructor]]].
  eapply rauxv_ok_frame in AUX; [| exact MU| exact WM| constructor; [cbn; unfold RAUXV_CELL; lia| constructor; [cbn; unfold RAUXV_CELL; lia| constructor]]].
  assert (SJS1 : sj_statics m1 true).
  { eapply sj_statics_agree; [exact AG1| | exact SJS]. intros a Ha. pose proof (sjs_addr_lt a Ha) as [Ra _]. unfold GLOBALS_TOP in Ra. cbn [outside]. refine (conj _ (conj _ I)); lia. }
  assert (AEX1 : aex_tbl m1 3).
  { eapply aex_tbl_agree; [exact AG1| | exact AEXT]. intros a Ha. unfold aex_tbl_addr, AEX in Ha. cbn [outside]. refine (conj _ (conj _ I)); lia. }
  assert (VEC1 : imp_vec m1 (OW' ++ LB) (Some p)).
  { eapply imp_vec_agree; [exact AG1| | | exact VEC].
    - intros a Ha. pose proof (impvec_addr_lt a Ha) as [Ra _]. unfold GLOBALS_TOP in Ra. cbn [outside]. refine (conj _ (conj _ I)); lia.
    - intros a Ha. specialize (BLB2 a Ha). cbn [outside]. refine (conj _ (conj _ I)); lia. }
  assert (OUT1 : imp_out m1 q ostr) by (eapply imp_out_agree; [exact AG1| exact OUT| intros a Ha; cbn [outside]; refine (conj _ (conj _ I)); lia]).
  assert (PRES1 : lx_pres LB (q + 1056) [LXW_IMP; LXW_SJ; LXW_AEX] m m1).
  { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
  clear SJS AEXT VEC OUT AG1 MU WM.
  assert (VTD1 : rw_cells usegs m1 SJ_DPI_VPTR dpi_vtable_cells).
  { pose proof LXS0 as (_ & _ & _ & _ & VTD & _). eapply rw_cells_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES1)| exact VTD|].
    intros a Ha. unfold dpi_vtable_cells, SJ_DPI_VPTR in Ha. cbn in Ha. apply lxs_addr_client; [unfold lxs_addr, SJ_DPI_VPTR; do 4 right; left; lia|].
    unfold LXW_IMP, LXW_SJ, LXW_AEX, IMP_VEC_LO, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia. }

  rename ST1 into STK. hide STK. hide F320. hide F936.
  pose proof (stk_empty usegs m1 q ltac:(lia)) as ISA. repeat (absorb1 ISA).
  lazymatch type of ISA with stk _ _ q (q + 336) => idtac | ?T => fail 100 "island A:" T end.
  pose proof (stk_empty usegs m1 (q + 456) ltac:(lia)) as ISC. repeat (absorb1 ISC).
  lazymatch type of ISC with stk _ _ (q + 456) (q + 952) => idtac | ?T => fail 100 "island C:" T end.
  unhide F320. unhide F936. unhide STK. rename STK into ST1.

  destruct ostr as [[[pob OA] on]|].
  -
    destruct OUT1 as (L & OUTC & ODD & OSZ & OBR). cbn [blk_size blk_addr blk_id fst snd option_map ocp_blocks app del_opt] in OUTC, ODD, OSZ, OBR, HEAP |- *.
    pose proof (out_long_bytes _ _ _ _ _ OUTC) as OUTB. unfold out_long in OUTC. unfold MallocRep.wz in OUTC, OUTB.
    rewrite (unsigned_lit (on + 1)) in OUTB by lia.
    step. zstep. step. if_cases K; zify_cond K; [exfalso; rewrite land1_byte in K; clear - K ODD; lia| clear K].

    step. step. zstep. step. clear OUTB.
    pose proof (stk_of_rw_cells _ _ _ _ F392) as ISB. clear F392. stk_norm ISB. absorb1 ISB. absorb1 ISB. rename ISB into ISC.
    lazymatch type of ISC with stk _ _ (q + 408) (q + 952) => idtac | ?T => fail 100 "island B+C:" T end.
    lazymatch type of HEAP with RHEAP _ ?L _ => assert (ND : List.NoDup (map blk_id L)) by (eapply LH_nodup; exact HEAP) end.
    ihere. to_implM. eapply implM_bind.
    { eapply (opdel_sz_proof HF) with (B := B) (lo := lo) (A := OA) (n := on);
        [exact HEAP| left; reflexivity| exact AUX| lia| exact ST1| assumption| unfold RFREE_STACK; lia| exact ERR1| exact MI1| lia]. }
    cbv beta. intros [] s2 ms2 PO. unfold free_postZ in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & -> & MI2 & ST2 & ERR2 & AUX2 & HP & FA2 & SO2 & HEAP2).
    rewrite (lb_remove_hd _ _ _ _ ND) in HP, HEAP2. clear ND.
    replace (ret_pc (Z_to_bv 64 0x3f284)) with (Z_to_bv 64 0x3f284) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_of_heap_pres _ _ _ _ HP) as AG2.
    apply (rw_cells_agree _ _ _ _ _ AG2) in THISC; [| intros a Ha; right; right; exists (pim, IMPL, 96); split; [apply in_or_app; right; do 3 right; left; reflexivity| cbn in Ha |- *; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG2) in VTD1;
      [| intros a Ha; right; left; unfold dpi_vtable_cells, SJ_DPI_VPTR in Ha; cbn in Ha;
         unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia].
    clear ERR1.
    repeat match goal with H : rw_cells _ m1 _ _ |- _ => first [apply (rw_cells_agree _ _ _ _ _ AG2) in H; [| intros a Ha; left; cbn in Ha; lia] | clear H] end.
    apply (stk_agree _ _ _ _ _ AG2) in ISA; [| intros a Ha; left; lia]. apply (stk_agree _ _ _ _ _ AG2) in ISC; [| intros a Ha; left; lia].
    assert (SJS2 : sj_statics m2 true).
    { eapply sj_statics_agree; [exact AG2| | exact SJS1]. intros a Ha. pose proof (sjs_addr_lt a Ha) as [Ra Rb]. unfold GLOBALS_TOP in Ra. right; left. split; [lia| exact Rb]. }
    assert (AEX2 : aex_tbl m2 3).
    { eapply aex_tbl_agree; [exact AG2| | exact AEX1]. intros a Ha. unfold aex_tbl_addr, AEX in Ha. right; left. split; [lia|].
      unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    assert (VEC2 : imp_vec m2 (OW' ++ LB) (Some p)).
    { eapply imp_vec_agree; [exact AG2| | | exact VEC1].
      - intros a Ha. pose proof (impvec_addr_lt a Ha) as [Ra Rb]. unfold GLOBALS_TOP in Ra. right; left. split; [lia| exact Rb].
      - intros a (b0 & Hb0 & Hr). right; right. exists b0. split; [apply in_or_app; right; do 6 right; exact Hb0| exact Hr]. }
    assert (PRES2 : lx_pres LB (q + 1056) [LXW_IMP; LXW_SJ; LXW_AEX] m m2).
    { eapply lx_pres_trans; [exact PRES1|].
      eapply (lx_pres_sub LB (q + 1056) _ _ _ _ _ _ (lx_pres_of_heap_pres _ _ _ _ _ HP)); [lia| intros b0 Hb0; apply in_or_app; right; do 6 right; apply in_or_app; right; exact Hb0|].
      intros a Ha NX. exfalso. exact (NX Ha). }
    eapply (lftoi_tail_end HF ocp) with (B := B) (lo := lo);
      [exact FRM| exact MI2| exact ST2| exact ERR2| exact AUX2| congruence| congruence| exact CEIL'| unfold GLOBALS_TOP; lia| lia| lia| unfold IMP_FRAME; lia| lia
      | exact HEAP0| exact LXS0| exact SEW0| exact SSP0| exact PL0| exact HEAP2| exact XN| exact VEC2| exact SJS2| exact AEX2| unfold IMP_FRAME; exact PRES2| exact VTD1
      | exact ISA| eassumption| eassumption| eassumption| unfold p48_cells; cbn [blk_addr fst snd]; eassumption| exact ISC| eassumption| exact THISC].
  -
    destruct OUT1 as (b0 & j23 & OUTC & EVEN). unfold out_short in OUTC. cbn [option_map ocp_blocks app del_opt] in HEAP |- *.
    step. zstep. step. if_cases K; zify_cond K; [clear K| exfalso; clear - K EVEN; lia].
    pose proof (stk_of_rw_cells _ _ _ _ F392) as ISB. clear F392. stk_norm ISB. absorb1 ISB. absorb1 ISB. rename ISB into ISC.
    lazymatch type of ISC with stk _ _ (q + 408) (q + 952) => idtac | ?T => fail 100 "island B+C:" T end.
    ihere. to_implM. cbn [bind ret lib_malloc lib_free lops Target.ops]. apply implM_ret_bind. cbv beta.
    eapply (lftoi_tail_end HF ocp) with (B := B) (lo := lo);
      [exact FRM| exact MI1| exact ST1| exact ERR1| exact AUX| exact FA| exact SO| exact CEIL'| unfold GLOBALS_TOP; lia| lia| lia| unfold IMP_FRAME; lia| lia
      | exact HEAP0| exact LXS0| exact SEW0| exact SSP0| exact PL0| exact HEAP| exact XN| exact VEC1| exact SJS1| exact AEX1| unfold IMP_FRAME; exact PRES1| exact VTD1
      | exact ISA| eassumption| eassumption| eassumption| exact F360| exact ISC| eassumption| exact THISC].
Qed.

End WithCeiling0.
