(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto AMalloc_iface AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA.
Import CtrFX.

Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CtrPre CtrPost CtrFree CtrRealloc CtrFrame CtrNoDelta FrameV.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ARealloc_x F_arealloc_iseg. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc1. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aaligned_iseg AInstanceA16 AInstanceU2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CtrNull.
Unset Nia Cache. Unset Nra Cache.

Section Sound.
Context {rc : runConstT}.

Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Hypothesis IMGSH_aci : forall v a, In v SHLIT -> fst v <= a < snd v -> exists a', in_ranges (aci AI) a' /\ a = shad a'.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable COVP : Model -> word -> Prop.
Variable NMAX : nat.
Hypothesis ACCT_led : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).
Hypothesis ACCT_cov : forall aw L RNG st LBa m mo b z, ACCT aw L RNG st LBa mo -> AHEAP AI L RNG st LBa m -> In b LBa ->
  (ab_addr b <= z < ab_addr b + ab_size b \/ shad (ab_addr b) <= z < shad (ab_addr b) + shlen (ab_size b + 7)) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_mat : forall aw L RNG st LBa mo mo', ACCT aw L RNG st LBa mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  ACCT aw L RNG st LBa mo'.
Variable UNIV : list (list Z).
Hypothesis AI_frame_top : forall L RNG st LB m m',
  AHEAP AI L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (ALib.Mem.wa a) = m (ALib.Mem.wa a)) -> wmono asegs m m' -> AHEAP AI L RNG st LB m'.
Hypothesis wmono_of : forall m m' : amem, (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) -> wmono asegs m m'.
Variable Cw : client_world.

Variable OPS : optable.

Hypothesis AI_fake : AI_fake_law AI.

Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis Cw_ghost_grow : forall md ca LB ws m b0 n0 n, cw_holds Cw md ca LB ws m ->
  In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
  (forall a, in_iv (shad b0, n) a -> ~ in_user LB a) -> cw_holds Cw md ca ((shad b0, n) :: LB) (ws ++ [Win (shad b0) n K_TWINz]) m.
Hypothesis Cw_ghost_free : forall md ca LB ws m b n ws', cw_holds Cw md ca LB ws m -> In (Win b n K_TWINz) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n K_TWINz) -> cw_holds Cw md ca (remove iv_eq_dec (b, n) LB) ws' m.

Hypothesis Cw_vec_unowned : forall md ca LB ws m i a, cw_holds Cw md ca LB ws m -> In i (VECS md) -> nth_error ca i = Some a -> bv_unsigned a <> 0 ->
  forall w, In w ws -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned a.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.cov1 HEAP_ID args z.
Hypothesis OPS_minv : forall mo, op_minv OPS mo -> m_halted mo = None.

Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb asegs m a = true -> wb asegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> op_cov0 OPS a.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).

Definition acct_leaf (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock) (n chg : Z)
    (r : astate * option aptr) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo' Aaddr, mrel A' moc' mo' ->
    MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\
    match snd r with
    | Some p => ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst r) (HB p Aaddr n :: LBa) mo'
    | None => ACCT (Z_to_bv 64 (bv_unsigned aw - 1048576)) L RNG' (fst r) LBa mo'
    end

    /\ (64512 < n -> aprist st -> aprist (fst r)).
Definition chg_ok (aw : word) (n chg : Z) : Prop := (chg = 0 /\ n <= 64512) \/ (chg = n /\ n <= bv_unsigned aw).

Definition c6ok (RESV : list (Z * Z)) (RNG : footprint) (st : astate) : Prop :=
  c6m RESV RNG st /\ (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23).

Hypothesis AERRNO_aci : forall LB SP, aclient_range (aci AI) LB SP AERRNO 4.
Hypothesis ACCT_malloc : forall aw L RNG st LBa mo n chg,
  ACCT aw L RNG st LBa mo -> MP mo -> op_minv OPS mo -> 1 <= n <= AREQMAX -> chg_ok aw n chg -> 1048576 <= bv_unsigned aw -> C24.c24count LBa <= 255 ->
  exists RESV A moc, aresv_ok L RESV /\ c6ok RESV RNG st /\ mrel A moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A (aembed ATOP (amalloc ATOP RESV st n)) moc (acct_leaf mo aw L st LBa n chg).

Lemma chg_of_pre : forall E st XN aw n, facts_hold E (s_facts st) -> bv_unsigned (den E (getr st XN)) = n ->
  (prim_decided (s_facts st) (getr st XN) = true \/ n <= bv_unsigned aw) ->
  chg_ok aw n (if prim_decided (s_facts st) (getr st XN) then 0 else n).
Proof.
  intros E st XN aw n HF EN H. destruct (prim_decided (s_facts st) (getr st XN)) eqn:PD.
  - left. split; [reflexivity|]. rewrite <- EN. exact (CallA.prim_decided_sound E _ _ HF PD).
  - right. split; [reflexivity|]. destruct H as [H|H]; [discriminate| exact H].
Qed.

Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).

Notation sp_lo := CtrPre.sp_lo.

Theorem amalloc_sound : forall pc, to_Z pc = AMALLOC_SYM -> contract_sound asegs OPS MP PB (amalloc_c UNIV AMALLOC_PC pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc amalloc_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = AMALLOC_SYM) by (rewrite Hspc; exact Hpc).
  destruct (CtrPre.amalloc_pre_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng st sts E ms mo HS HPC Happ)
    as (L & RNG & sta & LBa & aw & n & Ems & AH & AC & HU & MI & ST & BOT & LO & TP & Ha0 & NR & NC & AUNW & S0NE & RA4 & RANE & SP16 & RSTK & CF & PRISTF).
  destruct AUNW as [utr AUNW].
  destruct NC as [NCX NC]. destruct (CtrPre.acall_facts_c24 AI ACCT UNIV Cw X10 E st ms mo L RNG sta LBa aw n CF) as [C24B NDEN].
  set (chg := if prim_decided (s_facts st) (getr st X10) then 0 else n).
  destruct (ACCT_malloc aw L RNG sta LBa mo n chg AC HMP (so_mf _ _ _ _ _ _ HS) NR (chg_of_pre E st X10 aw n (so_facts _ _ _ _ _ _ HS) NDEN NC) NCX C24B) as (RESV & A & moc & ROK & [C6M CAPB] & MR & MINV & HH & TW).
  set (R := ms_regs ms) in *.
  pose proof (AI_malloc AI L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) sta LBa n (sp_lo E st) utr RESV AH MI ST BOT LO TP Ha0 NR AUNW S0NE RA4 RANE SP16 RSTK ROK
                (so_fcsr _ _ _ _ _ _ HS) C6M CAPB (CtrNull.errno_cells (ms_mem ms))) as IMPL.
  rewrite Ems. apply (GlueA.realizes_to_mkRA asegs).
  eapply (implS_twfS_realizes_silent asegs NMAXt _ RNG A _ _ _ moc mo K IMPL TW HH MINV MR).
  intros r RNG' A' ms' moc' mo' HQ HP ACC' HH' MINV' MR'.
  assert (LEAF : forall Aaddr, MP mo' /\ op_minv OPS mo' /\ OTHER mo mo' /\
            match snd r with
            | Some p => ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst r) (HB p Aaddr n :: LBa) mo'
            | None => ACCT (Z_to_bv 64 (bv_unsigned aw - 1048576)) L RNG' (fst r) LBa mo'
            end /\ (64512 < n -> aprist sta -> aprist (fst r))) by (intros Aaddr; exact (HP mo' Aaddr MR')).
  destruct (LEAF 0) as (HMP' & HMI' & OTH & ACP0 & PKEEP).
  assert (PRSX : CtrPre.prist_in E st -> aprist (fst r)).
  { intros PI. destruct PRISTF as [SEC|NP]; [| exfalso; exact (NP PI)].
    exact (PKEEP SEC (CtrPre.prist_in_aprist AI ACCT UNIV Cw X10 E st ms mo L RNG sta LBa aw n CF PI)). }
  destruct r as [sta' [p|]]; unfold amalloc_post2x in HQ; cbn [fst snd] in HQ, ACP0, PRSX, LEAF.
  -
    destruct (CtrPost.amalloc_post_okA AI IMGX IMGX_aci IMGSH_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 Cw_ghost_grow OPS_frame_other OPS_fp_other
                OTHER OPS_mo_other OPS_cov0_img st sts E ms mo L RNG sta LBa aw n (sta', Some p) RNG' ms' mo' HS Happ CF HQ
                (fun Aaddr => proj1 (proj2 (proj2 (proj2 (LEAF Aaddr))))) PRSX HMI' OTH) as (stB & E' & INB & EXT & HS').

    eapply (HK stB); [destruct sts as [|stN tl0]; [destruct INB| right; exact INB] | exact EXT | exact HMP' | exact HS'].
  -
    destruct (CtrPre.amalloc_apply_inv UNIV st sts Happ) as (r0 & tp0 & hargs0 & cred0 & st10 & CP0 & _ & FO0 & HA0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FS0 & stN & tl0 & ESTS & NPOST).
    destruct (CtrNull.acallN_of_facts AI ACCT UNIV Cw X10 E st ms mo L RNG sta LBa aw n CF) as (r1 & hargs1 & wnl1 & st11 & CP1 & FS1 & CFN).
    rewrite CP0 in CP1. injection CP1 as <-. rewrite FS0 in FS1. injection FS1 as <-.
    assert (EH : hargs1 = hargs0).
    { destruct CFN as (LB1 & ks1 & offs1 & rss1 & ksp1 & nn1 & md1 & A1 & nw1 & rest1 & _ & _ & _ & _ & _ & _ & Hf1 & _). rewrite FO0 in Hf1. injection Hf1 as E1. exact (eq_sym E1). }
    subst hargs1.
    destruct (CtrNull.anull_post_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                AERRNO_aci IMGSH_aci st E ms mo L RNG sta LBa aw r0 hargs0 wnl1 st10 cred0 stN sta' RNG' ms' mo'
                HS CP0 FS0 CFN AH HA0 NPOST BOT HQ ACP0 (fun PI _ => PRSX PI) HMI' OTH) as (E1 & EXT & HS').
    eapply (HK stN); [rewrite ESTS; left; reflexivity | exact EXT | exact HMP' | exact HS'].
Qed.

Definition acct_leaf_free (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock) (p : aptr)
    (r : astate) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\ ACCT aw L RNG' r (lb_remove p LBa) mo'
    /\ (aprist st -> aprist r).
Hypothesis ACCT_free : forall aw L RNG st LBa mo p ch,
  ACCT aw L RNG st LBa mo -> MP mo -> op_minv OPS mo -> (a_live st) !! p = Some ch ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (aembed ATOP (afree st (Some p))) moc (acct_leaf_free mo aw L st LBa p).

Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc4000.
Definition acct_leaf_silent (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\ ACCT aw L RNG' st LBa mo'.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent mo aw L st LBa).

Theorem afree_sound : forall pc, to_Z pc = AFREE_SYM -> contract_sound asegs OPS MP PB (afree_c UNIV AFREE_PC pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc afree_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = AFREE_SYM) by (rewrite Hspc; exact Hpc).
  destruct (CtrFree.afree_apply_shape UNIV AFREE_PC st sts Happ) as (r & hargs & wnl & st1 & kf & sh & h1 & h2 & tlc & PRE & X10E & FT & FOKk & H1 & H2 & ESTS & NV & TCAN).
  destruct (CtrPre.acall_pre_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK AFREE_PC st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & MI & ST & BOT & LO & TP & AUNW & S0NE & RA4 & RANE & SP16 & RSTK & CP & FS & CF).
  destruct AUNW as [utr AUNW].
  destruct (CtrFree.afree_block AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake E st ms mo r hargs wnl L RNG sta LBa aw kf sh tlc HS CF FT FOKk TCAN X10E) as (p & lenf & WLf & HP & Ha0 & FPAT).
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH HP) as (_ & _ & _ & _ & _ & _ & (chp & LIVEp & _) & _).
  destruct (ACCT_free aw L RNG sta LBa mo p chp AC HMP (so_mf _ _ _ _ _ _ HS) LIVEp) as (A0 & moc & MR & MINV & HH & TW).
  set (R := ms_regs ms) in *.
  pose proof (AI_free AI L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) sta LBa p _ _ (sp_lo E st) utr AH HP FPAT MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK) as IMPL.
  rewrite Ems, HPC. apply (GlueA.realizes_to_mkRA asegs).
  eapply (implS_twfS_realizes_silent asegs NMAXt _ RNG A0 _ _ _ moc mo K IMPL TW HH MINV MR).
  intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
  destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP & PKEEP).
  destruct (CtrFree.afree_post_okA AI IMGX IMGX_aci IMGSH_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 Cw_ghost_free Cw_vec_unowned OPS_frame_other OPS_fp_other
              OTHER OPS_mo_other OPS_cov0_img st sts E ms mo r hargs wnl st1 kf sh tlc h1 h2 L RNG sta LBa aw p lenf rr RNG' ms' mo'
              HS CP FS CF FT FOKk NV TCAN H1 H2 ESTS WLf HP HQ ACP PKEEP HMI' OTH) as (stF & E' & -> & EXT & HS').
  eapply (HK stF); [left; reflexivity | exact EXT | exact HMP' | exact HS'].
Qed.

Hypothesis AI_realloc : AInstanceU2F.arealloc_stmt2x (aci AI) (AHEAP AI).
Definition acct_leaf_realloc (mo0 : Model) (aw : word) (L : alayout) (LBa : list ablock) (p : aptr) (n chg : Z)
    (r : astate * option aptr) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo' Aaddr, mrel A' moc' mo' ->
    MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\
    match snd r with
    | Some q => ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst r) (HB q Aaddr n :: lb_remove p LBa) mo'
    | None => ACCT (Z_to_bv 64 (bv_unsigned aw - 1048576)) L RNG' (fst r) LBa mo'
    end.
Hypothesis ACCT_realloc : forall aw L RNG st LBa mo p chp n chg,
  ACCT aw L RNG st LBa mo -> MP mo -> op_minv OPS mo -> (a_live st) !! p = Some chp -> 1 <= n <= AREQMAX -> chg_ok aw n chg -> 1048576 <= bv_unsigned aw ->
  C24.c24count LBa <= 255 ->
  exists RESV A0 moc, aresv_ok L RESV /\ c6ok RESV RNG st /\ mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (aembed ATOP (ARealloc_x.arealloc RESV st p n)) moc (acct_leaf_realloc mo aw L LBa p n chg).

Theorem arealloc_sound : forall pc, to_Z pc = F_arealloc_iseg.AREALLOC_SYM -> contract_sound asegs OPS MP PB (arealloc_c UNIV F_arealloc_iseg.AREALLOC_PC pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc arealloc_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = F_arealloc_iseg.AREALLOC_SYM) by (rewrite Hspc; exact Hpc).
  destruct (CtrRealloc.arealloc_apply_shape UNIV F_arealloc_iseg.AREALLOC_PC st sts Happ)
    as (r & hargs & wnl & st1 & kf & sh & cred & h1 & h2 & h3 & h4 & h5 & stN & PRE & X10E & FT & HA & FOKk & NV & TCAN & N0 & N1 & SS & NC & PRA & H1 & H2 & H3 & H4 & H5 & NPOST & ESTS).
  assert (ROOM : 4096 <= to_Z AREALLOC_ROOM < 2 ^ 32) by (vm_compute; split; congruence).
  destruct (CtrPre.acall_pre_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng AREALLOC_ROOM F_arealloc_iseg.AREALLOC_PC st r hargs wnl st1 E ms mo HS ROOM PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & MI & ST & BOT & LO & TP & AUNW & S0NE & RA4 & RANE & SP16 & RSTK & CP & FS & CF).
  destruct AUNW as [utr AUNW].
  pose proof (CtrPre.acall_pre_room AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng AREALLOC_ROOM _ st r hargs wnl st1 E ms mo HS ROOM PRE) as LOR.
  destruct (CtrRealloc.arealloc_block AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake E st ms mo r hargs wnl L RNG sta LBa aw kf sh cred HS CF FT FOKk TCAN X10E HA N0 N1 NC)
    as (p & lenf & WLf & HP & Ha0 & Ha1 & NR & NCR & CANM).
  set (n := bv_unsigned (den E (getr st X11))) in *.
  destruct NCR as [NCX NCR].
  set (chg := if prim_decided (s_facts st) (getr st X11) then 0 else n).
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH HP) as (_ & _ & _ & _ & _ & _ & (chp & LIVEp & _) & _).
  destruct (ACCT_realloc aw L RNG sta LBa mo p chp n chg AC HMP (so_mf _ _ _ _ _ _ HS) LIVEp NR (chg_of_pre E st X11 aw n (so_facts _ _ _ _ _ _ HS) eq_refl NCR) NCX
              (CtrPre.acallG_c24 AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw CF)) as (RESV & A0 & moc & ROK & [C6M CAPB] & MR & MINV & HH & TW).
  set (R := ms_regs ms) in *.
  pose proof (AI_realloc L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) sta LBa p _ _ n (sp_lo E st) utr RESV AH HP CANM MI ST BOT
                ltac:(unfold ARealloc_x.AREALLOC_STACK; change (to_Z AREALLOC_ROOM) with 12288 in LOR; lia) TP Ha0 Ha1 NR AUNW S0NE RA4 RANE SP16 RSTK ROK
                (so_fcsr _ _ _ _ _ _ HS) C6M CAPB (CtrNull.errno_cells (ms_mem ms))) as IMPL.
  rewrite Ems, HPC. apply (GlueA.realizes_to_mkRA asegs).
  eapply (implS_twfS_realizes_silent asegs NMAXt _ RNG A0 _ _ _ moc mo K IMPL TW HH MINV MR).
  intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
  assert (LEAF : forall Aaddr, MP mo' /\ op_minv OPS mo' /\ OTHER mo mo' /\
            match snd rr with
            | Some q => ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst rr) (HB q Aaddr n :: lb_remove p LBa) mo'
            | None => ACCT (Z_to_bv 64 (bv_unsigned aw - 1048576)) L RNG' (fst rr) LBa mo'
            end) by (intros Aaddr; exact (HP' mo' Aaddr MR')).
  destruct (LEAF 0) as (HMP' & HMI' & OTH & ACP0).
  destruct rr as [sta' [q|]]; unfold AInstanceU2F.arealloc_post2x in HQ; cbn [fst snd] in HQ, ACP0, LEAF.
  -
    destruct (CtrRealloc.arealloc_post_okA AI IMGX IMGX_aci IMGSH_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 Cw_ghost_free Cw_ghost_grow Cw_vec_unowned OPS_frame_other OPS_fp_other
                OTHER OPS_mo_other OPS_cov0_img st sts E ms mo r hargs wnl st1 kf sh cred h1 h2 h3 h4 h5 stN L RNG sta LBa aw p lenf n (sta', Some q) RNG' ms' mo'
                HS CP FS CF FT FOKk NV TCAN HA SS NC PRA H1 H2 H3 H4 H5 ESTS WLf HP eq_refl HQ
                ltac:(intros UB; destruct (LEAF UB) as (_ & _ & _ & X); exact X) HMI' OTH) as (stB & E' & -> & EXT & HS').
    eapply (HK stB); [right; left; reflexivity | exact EXT | exact HMP' | exact HS'].
  -
    pose proof (CtrNull.acallN_of_G AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw CF) as CFN.
    assert (FO : find_op HEAP_ID (s_ops st) = Some hargs).
    { destruct CFN as (LB1 & ks1 & offs1 & rss1 & ksp1 & nn1 & md1 & A1 & nw1 & rest1 & _ & _ & _ & _ & _ & _ & Hf1 & _). exact Hf1. }
    assert (NPI : ~ CtrPre.prist_in E st) by (exact (CtrPre.prist_absent_not_in E st hargs (so_facts _ _ _ _ _ _ HS) FO PRA)).
    destruct (CtrNull.anull_post_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                AERRNO_aci IMGSH_aci st E ms mo L RNG sta LBa aw r hargs wnl st1 cred stN sta' RNG' ms' mo'
                HS CP FS CFN AH HA NPOST BOT HQ ACP0 (fun PI _ => False_ind _ (NPI PI)) HMI' OTH) as (E1 & EXT & HS').
    eapply (HK stN); [rewrite ESTS; left; reflexivity | exact EXT | exact HMP' | exact HS'].
Qed.

Hypothesis AI_aligned16 : AInstanceU2F.aaligned16_stmt2x (aci AI) (AHEAP AI).

Hypothesis ACCT_aligned16 : forall aw L RNG st LBa mo n chg,
  ACCT aw L RNG st LBa mo -> MP mo -> op_minv OPS mo -> 16 <= n <= 4096 -> n mod 16 = 0 -> chg_ok aw n chg -> 1048576 <= bv_unsigned aw ->
  exists RESV A moc, aresv_ok L RESV /\ c6ok RESV RNG st /\ mrel A moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A (aembed ATOP (aaligned16x ATOP RESV st n)) moc (acct_leaf mo aw L st LBa n chg).

Theorem aaligned_sound : forall pc, to_Z pc = F_aaligned_iseg.AALIGNED_SYM ->
  contract_sound asegs OPS MP PB (aaligned_c UNIV F_aaligned_iseg.AALIGNED_PC pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc aaligned_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = F_aaligned_iseg.AALIGNED_SYM) by (rewrite Hspc; exact Hpc).
  destruct (CtrPre.aaligned_pre_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng st sts E ms mo HS HPC Happ)
    as (L & RNG & sta & LBa & aw & n & Ems & AH & AC & HU & MI & ST & BOT & LO & TP & Ha0 & Ha1 & PRIM & N16 & NR16 & NC & AUNW & S0NE & RA4 & RANE & SP16 & RSTK & CF & NOPR).
  destruct AUNW as [utr AUNW].
  assert (NR : 1 <= n <= AREQMAX) by (unfold AREQMAX; lia).
  destruct NC as [NCX NC]. destruct (CtrPre.acall_facts_c24 AI ACCT UNIV Cw X11 E st ms mo L RNG sta LBa aw n CF) as [C24B NDEN].
  set (chg := if prim_decided (s_facts st) (getr st X11) then 0 else n).
  destruct (ACCT_aligned16 aw L RNG sta LBa mo n chg AC HMP (so_mf _ _ _ _ _ _ HS) NR16 N16 (chg_of_pre E st X11 aw n (so_facts _ _ _ _ _ _ HS) NDEN NC) NCX) as (RESV & A & moc & ROK & [C6M CAPB] & MR & MINV & HH & TW).
  set (R := ms_regs ms) in *.
  pose proof (AI_aligned16 L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) sta LBa n (sp_lo E st) utr RESV PRIM N16 AH MI ST BOT LO TP Ha0 Ha1 NR AUNW S0NE RA4 RANE SP16 RSTK ROK
                (so_fcsr _ _ _ _ _ _ HS) C6M CAPB (CtrNull.errno_cells (ms_mem ms))) as IMPL.
  rewrite Ems. apply (GlueA.realizes_to_mkRA asegs).
  eapply (implS_twfS_realizes_silent asegs NMAXt _ RNG A _ _ _ moc mo K IMPL TW HH MINV MR).
  intros r RNG' A' ms' moc' mo' HQ HP ACC' HH' MINV' MR'.
  assert (LEAF : forall Aaddr, MP mo' /\ op_minv OPS mo' /\ OTHER mo mo' /\
            match snd r with
            | Some p => ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst r) (HB p Aaddr n :: LBa) mo'
            | None => ACCT (Z_to_bv 64 (bv_unsigned aw - 1048576)) L RNG' (fst r) LBa mo'
            end /\ (64512 < n -> aprist sta -> aprist (fst r))) by (intros Aaddr; exact (HP mo' Aaddr MR')).
  destruct (LEAF 0) as (HMP' & HMI' & OTH & ACP0 & _).
  destruct r as [sta' [p|]]; unfold amalloc_post2x in HQ; cbn [fst snd] in HQ, ACP0, LEAF.
  -
    destruct (CtrPost.aaligned_post_okA AI IMGX IMGX_aci IMGSH_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 Cw_ghost_grow OPS_frame_other OPS_fp_other
                OTHER OPS_mo_other OPS_cov0_img st sts E ms mo L RNG sta LBa aw n (sta', Some p) RNG' ms' mo' HS Happ CF HQ
                (fun Aaddr => proj1 (proj2 (proj2 (proj2 (LEAF Aaddr))))) NOPR HMI' OTH) as (stN & stB & E' & -> & EXT & HS').
    eapply (HK stB); [right; left; reflexivity | exact EXT | exact HMP' | exact HS'].
  -
    destruct (CtrPre.aaligned_apply_inv UNIV st sts Happ) as (r0 & tp0 & hargs0 & cred0 & st10 & al0 & CP0 & _ & FO0 & HA0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FS0 & stN & stB0 & ESTS & NPOST).
    destruct (CtrNull.acallN_of_facts AI ACCT UNIV Cw X11 E st ms mo L RNG sta LBa aw n CF) as (r1 & hargs1 & wnl1 & st11 & CP1 & FS1 & CFN).
    rewrite CP0 in CP1. injection CP1 as <-. rewrite FS0 in FS1. injection FS1 as <-.
    assert (EH : hargs1 = hargs0).
    { destruct CFN as (LB1 & ks1 & offs1 & rss1 & ksp1 & nn1 & md1 & A1 & nw1 & rest1 & _ & _ & _ & _ & _ & _ & Hf1 & _). rewrite FO0 in Hf1. injection Hf1 as E1. exact (eq_sym E1). }
    subst hargs1.
    destruct (CtrNull.anull_post_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                AERRNO_aci IMGSH_aci st E ms mo L RNG sta LBa aw r0 hargs0 wnl1 st10 cred0 stN sta' RNG' ms' mo'
                HS CP0 FS0 CFN AH HA0 NPOST BOT HQ ACP0 (fun PI _ => False_ind _ (NOPR PI)) HMI' OTH) as (E1 & EXT & HS').
    eapply (HK stN); [rewrite ESTS; left; reflexivity | exact EXT | exact HMP' | exact HS'].
Qed.

Lemma afree0_apply_shape : forall PCz st sts, afree0_apply UNIV PCz st = Some sts ->
  exists r hargs wnl st1,
    acall_pre ASTACK (Some (UNIV, PCz)) st = Some (r, hargs, wnl, st1) /\ getr st X10 = VL wzero
    /\ sts = [setpc (setr (snd (fresh (clobber st1))) X10 (VP (fst (fresh (clobber st1))) wzero)) r].
Proof.
  intros PCz st sts H. unfold afree0_apply in H.
  destruct (acall_pre ASTACK (Some (UNIV, PCz)) st) as [[[[r hargs] wnl] st1]|] eqn:PRE; [|discriminate].
  destruct (getr st X10) as [w| | | | | | | | | |] eqn:X10E; try discriminate.
  destruct (weqb w wzero) eqn:W0; [|discriminate]. apply (proj1 (weqb_ok _ _)) in W0. subst w.
  exists r, hargs, wnl, st1. split; [reflexivity|]. split; [reflexivity|].
  destruct (fresh (clobber st1)) as [v st3] eqn:F. injection H as <-. reflexivity.
Qed.

Theorem afree0_sound : forall pc, to_Z pc = AFREE_SYM -> contract_sound asegs OPS MP PB (afree0_c UNIV AFREE_PC pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc afree0_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = AFREE_SYM) by (rewrite Hspc; exact Hpc).
  destruct (afree0_apply_shape AFREE_PC st sts Happ) as (r & hargs & wnl & st1 & PRE & X10E & ESTS).
  destruct (CtrPre.acall_pre_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK AFREE_PC st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & MI & ST & BOT & LO & TP & AUNW & S0NE & RA4 & RANE & SP16 & RSTK & CP & FS & CF).
  destruct AUNW as [utr AUNW].
  set (R := ms_regs ms) in *. set (sp := bv_unsigned (AP.getr R 2)) in *. set (m := ms_mem ms) in *.
  pose proof atop_range as ATR.
  assert (Ha0 : AP.getr R 10 = Z_to_bv 64 0).
  { unfold R. rewrite <- HeapCtr.reg_of_X10, (GlueA.getr_RA asegs OPS E st ms mo HS X10), X10E. reflexivity. }
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (AI_free_null AI L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) m sta LBa (sp_lo E st) utr AH MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK) as EV.
  rewrite Ems, HPC. apply (GlueA.realizes_to_mkRA asegs).
  eapply (implS_twfS_realizes_silent asegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ afree_null_post2 (aci AI) (AHEAP AI) L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4)
               (AP.getr R 8) (AP.getr R 9) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
               (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) sta LBa (sp_lo E st) m ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MINV'' & STK' & PRES & TWP & AH').
    fold sp in PRES.
    match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
    set (Fv := CtrFree.cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
    destruct (HeapCtr.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
    assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
    { unfold R. rewrite <- HeapCtr.reg_of_X1, (GlueA.getr_RA asegs OPS E st ms mo HS X1), Hra0, ER.
      assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.den_wlit. }
    assert (EMS' : ms' = CtrFrame.ms' ms r R' m').
    { rewrite EMS. unfold CtrFrame.ms'. f_equal. rewrite RAEQ. apply MState.ret_pc_even.
      - pose proof (int_range r) as RRr. rewrite two63_eq in RRr. lia.
      - pose proof (HeapCtr.call_pre_even st r CP) as EV0.
        pose proof (ValP.land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
        change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV0 in LM. change (to_Z 0%uint63) with 0 in LM.
        change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }

    pose proof CF as CF0.
    destruct CF0 as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                    & NW & AN & AJ & TS & WF & HC & AWden & (Wt & WOF & ARW & TI)).
    destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0' & OP & PV & NXc).
    destruct (CtrFrame.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
    assert (XE : s_next (clobber st1) = addn (s_next st) 15).
    { rewrite NXc, NX1. symmetry. destruct (CtrFrame.NX st FOK) as (_ & _ & B). pose proof (int_range (s_next st)) as RRn. rewrite two63_eq in RRn.
      apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia]. }
    assert (SHAPE : sts = [SS r (rf_set (s_rf (clobber st1)) X10 (VP (addn (s_next st) 15) wzero)) (s_ff st) (s_resv st) (s_regs st1) (s_facts st)
                              (s_ops st) (s_priv st) (PrimInt63.add (addn (s_next st) 15) 1%uint63)]).
    { rewrite ESTS. unfold fresh. cbn [fst snd]. rewrite XE. f_equal.
      assert (G : forall (S : sstate) nx1 v, setpc (setr (set_next S nx1) X10 v) r
                  = SS r (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (s_regs S) (s_facts S) (s_ops S) (s_priv S) nx1) by (intros [] ? ?; reflexivity).
      rewrite G, FF, RV, RG, FS0', OP, PV, FF1, RV1, FS1, OP1, PV1. reflexivity. }
    apply (HK _ ltac:(rewrite SHAPE; left; reflexivity) (CtrFrame.E' E st Fv Gv) ms' mo' (CtrFrame.EXT E st Fv Gv) HMP').
    rewrite EMS'.

    assert (RAWV : forall a, m' (ALib.Mem.wa a) = m (ALib.Mem.wa a) -> rb asegs m' a = rb asegs m a /\ (wb asegs m a = true -> wb asegs m' a = true)).
    { intros a EQ. split; [unfold rb; unfold ALib.Mem.wa in EQ; rewrite EQ; reflexivity|].
      intros Wb. apply (GlueA.wb_wviewA asegs). apply (GlueA.wb_wviewA asegs) in Wb. rewrite (wview_ext1 m' m _ EQ). exact Wb. }
    assert (CLX : forall a, 0 <= a < 2 ^ 64 -> aclient_addr (aci AI) LBa sp a ->
              rb asegs m' a = rb asegs m a /\ (wb asegs m a = true -> wb asegs m' a = true)).
    { intros a Ha CA. apply RAWV. exact (proj1 (PRES a Ha CA)). }
    assert (STBx : forall LB0, aw_real AI ACCT UNIV aw LB0 m mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> CtrFrame.stableA AI ms LB0 a ->
              m' (ALib.Mem.wa a) = m (ALib.Mem.wa a)).
    { intros LB0 (W0 & (E1 & E2 & E3 & E4) & ARW0) a Ha ST0. pose proof ARW0 as [HW0 _]. pose proof HW0 as (_ & HT0 & _).
      destruct (LB_classify AI ACCT UNIV AI_fake W0 aw LB0 m mo HW0) as (KU & KT).
      apply (aw_real_stable AI ACCT UNIV AI_fake aw LB0 m mo W0 RNG sta LBa m' LBa LB0 sp LBa TWP ltac:(intros b0 Hb0 _ _; rewrite <- E4; exact Hb0) ARW0).
      - rewrite E1. exact AH'.
      - exact PRES.
      - intros v Hv UB P. destruct (KU v Hv UB P) as (b & Vb & ->). exists b. split; [rewrite <- E4; exact (proj1 Vb)| reflexivity].
      - intros v Hv NUB. destruct (KT v Hv NUB) as [(b & Hb & ->)|(b & Vb & ->)].
        + left. exists b. destruct (HT0 b Hb) as [HbL HH0]. split; [exact HbL|]. split; [rewrite <- E4; exact HbL|]. split; [exact HH0| reflexivity].
        + right. exists b. split; [exact (proj1 (proj1 Vb))|]. split; [rewrite <- E4; exact (proj1 (proj1 Vb))|]. split; [exact (proj2 Vb)| reflexivity].
      - exact Ha.
      - exact ST0. }
    apply (CtrNoDelta.nodelta_st_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other
             OPS_cov0_img E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG sta _ _ HS CP FS CF).
    +
      intros rg Hrg. unfold CtrFrame.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
    + intros x i Hx. exact (CtrFree.cfvF_clob R' x i Hx).
    + rewrite HeapCtr.den_VPz. rewrite (CtrFrame.ev_E'_fresh E st FOK Fv Gv 15 ltac:(lia)). reflexivity.
    + exact MINV''.
    + exact STK'.
    +   intros LB0 AR0 a Ha STB. apply RAWV. exact (STBx LB0 AR0 a Ha STB).
    +   intros LB0 AR0 a Ha IU. apply (STBx LB0 AR0 a Ha). right; right. exact IU.
    +
      intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
      assert (CA : aclient_addr (aci AI) LBa sp a).
      { destruct (OPS_fp_other _ _ a NI FP) as [INA|[(a' & INA & ->)|(a' & STK & ->)]].
        - right; left; exact INA.
        - right; right; right. exists a'. split; [right; left; exact INA| reflexivity].
        - right; right; right. exists a'. split; [left; exact STK| reflexivity]. }
      pose proof (proj1 (PRES a ltac:(unfold two64 in Ha; lia) CA)) as E0. unfold ALib.Mem.wa in E0. exact E0.
    +
      intros a Ha CC Wb. apply (CLX a ltac:(unfold two64 in Ha; lia)); [| exact Wb].
      destruct CC as [CC|[(a' & CC & ->)|(a' & CC & ->)]]; [right; left; exact CC| |]; right; right; right; exists a'; (split; [| reflexivity]); [right; left; exact CC| left; exact CC].
    +
      intros a Ha SC IB. apply (CLX a Ha).
      destruct SC as [(a' & RRa & ->)|(vv & Hv & RRa)].
      * right; right; right. exists a'. split; [left; exact RRa| reflexivity].
      * destruct (IMGSH_aci vv a Hv RRa) as (a' & INA & ->). right; right; right. exists a'. split; [right; left; exact INA| reflexivity].
    + exact AH'.
    + exact ACP.
    +
      intros b x Hb FK Hx. pose proof (Op.blk_band AI AI_fake L RNG sta LBa m b x AH Hb Hx) as BB.
      exact (proj1 (PRES x ltac:(unfold AIMG_HI, KLS in BB; lia) ltac:(right; right; left; exists b; split; [exact Hb| exact Hx]))).
    + exact TWP.
    + exact OTH.
    + exact HMI'.
    + intros P; exact P.
Qed.

End Sound.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB AMalloc_iface.TwinB AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import CtrFX.

Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Unset Nia Cache. Unset Nra Cache.

Section Sound.
Context {rc : runConstT}.

Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Hypothesis IMGSH_aci : forall v a, In v SHLIT -> fst v <= a < snd v -> exists a', in_ranges (aci AI) a' /\ a = shad a'.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable COVP : Model -> word -> Prop.
Variable NMAX : nat.
Hypothesis ACCT_led : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).
Hypothesis ACCT_cov : forall aw L RNG st LBa m mo b z, ACCT aw L RNG st LBa mo -> AHEAP AI L RNG st LBa m -> In b LBa ->
  (ab_addr b <= z < ab_addr b + ab_size b \/ shad (ab_addr b) <= z < shad (ab_addr b) + shlen (ab_size b + 7)) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_mat : forall aw L RNG st LBa mo mo', ACCT aw L RNG st LBa mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  ACCT aw L RNG st LBa mo'.
Variable UNIV : list (list Z).
Hypothesis AI_frame_top : forall L RNG st LB m m',
  AHEAP AI L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (ALib.Mem.wa a) = m (ALib.Mem.wa a)) -> wmono bsegs m m' -> AHEAP AI L RNG st LB m'.
Hypothesis wmono_of : forall m m' : amem, (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) -> wmono bsegs m m'.
Variable Cw : client_world.

Variable OPS : optable.

Hypothesis AI_fake : AI_fake_law AI.

Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis Cw_ghost_grow : forall md ca LB ws m b0 n0 n, cw_holds Cw md ca LB ws m ->
  In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
  (forall a, in_iv (shad b0, n) a -> ~ in_user LB a) -> cw_holds Cw md ca ((shad b0, n) :: LB) (ws ++ [Win (shad b0) n K_TWINz]) m.
Hypothesis Cw_ghost_free : forall md ca LB ws m b n ws', cw_holds Cw md ca LB ws m -> In (Win b n K_TWINz) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n K_TWINz) -> cw_holds Cw md ca (remove iv_eq_dec (b, n) LB) ws' m.

Hypothesis Cw_vec_unowned : forall md ca LB ws m i a, cw_holds Cw md ca LB ws m -> In i (VECS md) -> nth_error ca i = Some a -> bv_unsigned a <> 0 ->
  forall w, In w ws -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned a.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.TwinB.cov1 HEAP_ID args z.
Hypothesis OPS_minv : forall mo, op_minv OPS mo -> m_halted mo = None.

Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb bsegs m a = true -> wb bsegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> op_cov0 OPS a.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).

Definition acct_leaf (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock) (n chg : Z)
    (r : astate * option aptr) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo' Aaddr, mrel A' moc' mo' ->
    MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\
    match snd r with
    | Some p => ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst r) (HB p Aaddr n :: LBa) mo'
    | None => ACCT (Z_to_bv 64 (bv_unsigned aw - 1048576)) L RNG' (fst r) LBa mo'
    end

    /\ (64512 < n -> aprist st -> aprist (fst r)).
Definition chg_ok (aw : word) (n chg : Z) : Prop := (chg = 0 /\ n <= 64512) \/ (chg = n /\ n <= bv_unsigned aw).

Definition c6ok (RESV : list (Z * Z)) (RNG : footprint) (st : astate) : Prop :=
  c6m RESV RNG st /\ (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23).

Hypothesis AERRNO_aci : forall LB SP, aclient_range (aci AI) LB SP AERRNO 4.
Hypothesis ACCT_malloc : forall aw L RNG st LBa mo n chg,
  ACCT aw L RNG st LBa mo -> MP mo -> op_minv OPS mo -> 1 <= n <= AREQMAX -> chg_ok aw n chg -> 1048576 <= bv_unsigned aw -> C24.TwinB.c24count LBa <= 255 ->
  exists RESV A moc, aresv_ok L RESV /\ c6ok RESV RNG st /\ mrel A moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A (aembed ATOP (amalloc ATOP RESV st n)) moc (acct_leaf mo aw L st LBa n chg).

Lemma chg_of_pre : forall E st XN aw n, facts_hold E (s_facts st) -> bv_unsigned (den E (getr st XN)) = n ->
  (prim_decided (s_facts st) (getr st XN) = true \/ n <= bv_unsigned aw) ->
  chg_ok aw n (if prim_decided (s_facts st) (getr st XN) then 0 else n).
Proof.
  intros E st XN aw n HF EN H. destruct (prim_decided (s_facts st) (getr st XN)) eqn:PD.
  - left. split; [reflexivity|]. rewrite <- EN. exact (CallA.TwinB.prim_decided_sound E _ _ HF PD).
  - right. split; [reflexivity|]. destruct H as [H|H]; [discriminate| exact H].
Qed.

Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).

Notation sp_lo := CtrPre.TwinB.sp_lo.

Theorem amalloc_sound : forall pc, to_Z pc = AMALLOC_SYM -> contract_sound bsegs OPS MP PB (amalloc_c UNIV AMALLOC_PC pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc amalloc_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = AMALLOC_SYM) by (rewrite Hspc; exact Hpc).
  destruct (CtrPre.TwinB.amalloc_pre_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng st sts E ms mo HS HPC Happ)
    as (L & RNG & sta & LBa & aw & n & Ems & AH & AC & HU & MI & ST & BOT & LO & TP & Ha0 & NR & NC & AUNW & S0NE & RA4 & RANE & SP16 & RSTK & CF & PRISTF).
  destruct AUNW as [utr AUNW].
  destruct NC as [NCX NC]. destruct (CtrPre.TwinB.acall_facts_c24 AI ACCT UNIV Cw X10 E st ms mo L RNG sta LBa aw n CF) as [C24B NDEN].
  set (chg := if prim_decided (s_facts st) (getr st X10) then 0 else n).
  destruct (ACCT_malloc aw L RNG sta LBa mo n chg AC HMP (so_mf _ _ _ _ _ _ HS) NR (chg_of_pre E st X10 aw n (so_facts _ _ _ _ _ _ HS) NDEN NC) NCX C24B) as (RESV & A & moc & ROK & [C6M CAPB] & MR & MINV & HH & TW).
  set (R := ms_regs ms) in *.
  pose proof (AI_malloc AI L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) sta LBa n (sp_lo E st) utr RESV AH MI ST BOT LO TP Ha0 NR AUNW S0NE RA4 RANE SP16 RSTK ROK
                (so_fcsr _ _ _ _ _ _ HS) C6M CAPB (CtrNull.TwinB.errno_cells (ms_mem ms))) as IMPL.
  rewrite Ems. apply (GlueA.TwinB.realizes_to_mkRA bsegs).
  eapply (implS_twfS_realizes_silent bsegs NMAXt _ RNG A _ _ _ moc mo K IMPL TW HH MINV MR).
  intros r RNG' A' ms' moc' mo' HQ HP ACC' HH' MINV' MR'.
  assert (LEAF : forall Aaddr, MP mo' /\ op_minv OPS mo' /\ OTHER mo mo' /\
            match snd r with
            | Some p => ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst r) (HB p Aaddr n :: LBa) mo'
            | None => ACCT (Z_to_bv 64 (bv_unsigned aw - 1048576)) L RNG' (fst r) LBa mo'
            end /\ (64512 < n -> aprist sta -> aprist (fst r))) by (intros Aaddr; exact (HP mo' Aaddr MR')).
  destruct (LEAF 0) as (HMP' & HMI' & OTH & ACP0 & PKEEP).
  assert (PRSX : CtrPre.TwinB.prist_in E st -> aprist (fst r)).
  { intros PI. destruct PRISTF as [SEC|NP]; [| exfalso; exact (NP PI)].
    exact (PKEEP SEC (CtrPre.TwinB.prist_in_aprist AI ACCT UNIV Cw X10 E st ms mo L RNG sta LBa aw n CF PI)). }
  destruct r as [sta' [p|]]; unfold amalloc_post2x in HQ; cbn [fst snd] in HQ, ACP0, PRSX, LEAF.
  -
    destruct (CtrPost.TwinB.amalloc_post_okA AI IMGX IMGX_aci IMGSH_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 Cw_ghost_grow OPS_frame_other OPS_fp_other
                OTHER OPS_mo_other OPS_cov0_img st sts E ms mo L RNG sta LBa aw n (sta', Some p) RNG' ms' mo' HS Happ CF HQ
                (fun Aaddr => proj1 (proj2 (proj2 (proj2 (LEAF Aaddr))))) PRSX HMI' OTH) as (stB & E' & INB & EXT & HS').

    eapply (HK stB); [destruct sts as [|stN tl0]; [destruct INB| right; exact INB] | exact EXT | exact HMP' | exact HS'].
  -
    destruct (CtrPre.TwinB.amalloc_apply_inv UNIV st sts Happ) as (r0 & tp0 & hargs0 & cred0 & st10 & CP0 & _ & FO0 & HA0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FS0 & stN & tl0 & ESTS & NPOST).
    destruct (CtrNull.TwinB.acallN_of_facts AI ACCT UNIV Cw X10 E st ms mo L RNG sta LBa aw n CF) as (r1 & hargs1 & wnl1 & st11 & CP1 & FS1 & CFN).
    rewrite CP0 in CP1. injection CP1 as <-. rewrite FS0 in FS1. injection FS1 as <-.
    assert (EH : hargs1 = hargs0).
    { destruct CFN as (LB1 & ks1 & offs1 & rss1 & ksp1 & nn1 & md1 & A1 & nw1 & rest1 & _ & _ & _ & _ & _ & _ & Hf1 & _). rewrite FO0 in Hf1. injection Hf1 as E1. exact (eq_sym E1). }
    subst hargs1.
    destruct (CtrNull.TwinB.anull_post_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                AERRNO_aci IMGSH_aci st E ms mo L RNG sta LBa aw r0 hargs0 wnl1 st10 cred0 stN sta' RNG' ms' mo'
                HS CP0 FS0 CFN AH HA0 NPOST BOT HQ ACP0 (fun PI _ => PRSX PI) HMI' OTH) as (E1 & EXT & HS').
    eapply (HK stN); [rewrite ESTS; left; reflexivity | exact EXT | exact HMP' | exact HS'].
Qed.

Definition acct_leaf_free (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock) (p : aptr)
    (r : astate) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\ ACCT aw L RNG' r (lb_remove p LBa) mo'
    /\ (aprist st -> aprist r).
Hypothesis ACCT_free : forall aw L RNG st LBa mo p ch,
  ACCT aw L RNG st LBa mo -> MP mo -> op_minv OPS mo -> (a_live st) !! p = Some ch ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (aembed ATOP (afree st (Some p))) moc (acct_leaf_free mo aw L st LBa p).

Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc5000.
Definition acct_leaf_silent (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\ ACCT aw L RNG' st LBa mo'.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent mo aw L st LBa).

Theorem afree_sound : forall pc, to_Z pc = AFREE_SYM -> contract_sound bsegs OPS MP PB (afree_c UNIV AFREE_PC pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc afree_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = AFREE_SYM) by (rewrite Hspc; exact Hpc).
  destruct (CtrFree.TwinB.afree_apply_shape UNIV AFREE_PC st sts Happ) as (r & hargs & wnl & st1 & kf & sh & h1 & h2 & tlc & PRE & X10E & FT & FOKk & H1 & H2 & ESTS & NV & TCAN).
  destruct (CtrPre.TwinB.acall_pre_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK AFREE_PC st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & MI & ST & BOT & LO & TP & AUNW & S0NE & RA4 & RANE & SP16 & RSTK & CP & FS & CF).
  destruct AUNW as [utr AUNW].
  destruct (CtrFree.TwinB.afree_block AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake E st ms mo r hargs wnl L RNG sta LBa aw kf sh tlc HS CF FT FOKk TCAN X10E) as (p & lenf & WLf & HP & Ha0 & FPAT).
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH HP) as (_ & _ & _ & _ & _ & _ & (chp & LIVEp & _) & _).
  destruct (ACCT_free aw L RNG sta LBa mo p chp AC HMP (so_mf _ _ _ _ _ _ HS) LIVEp) as (A0 & moc & MR & MINV & HH & TW).
  set (R := ms_regs ms) in *.
  pose proof (AI_free AI L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) sta LBa p _ _ (sp_lo E st) utr AH HP FPAT MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK) as IMPL.
  rewrite Ems, HPC. apply (GlueA.TwinB.realizes_to_mkRA bsegs).
  eapply (implS_twfS_realizes_silent bsegs NMAXt _ RNG A0 _ _ _ moc mo K IMPL TW HH MINV MR).
  intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
  destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP & PKEEP).
  destruct (CtrFree.TwinB.afree_post_okA AI IMGX IMGX_aci IMGSH_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 Cw_ghost_free Cw_vec_unowned OPS_frame_other OPS_fp_other
              OTHER OPS_mo_other OPS_cov0_img st sts E ms mo r hargs wnl st1 kf sh tlc h1 h2 L RNG sta LBa aw p lenf rr RNG' ms' mo'
              HS CP FS CF FT FOKk NV TCAN H1 H2 ESTS WLf HP HQ ACP PKEEP HMI' OTH) as (stF & E' & -> & EXT & HS').
  eapply (HK stF); [left; reflexivity | exact EXT | exact HMP' | exact HS'].
Qed.

Hypothesis AI_realloc : AInstanceU2F.TwinB.arealloc_stmt2x (aci AI) (AHEAP AI).
Definition acct_leaf_realloc (mo0 : Model) (aw : word) (L : alayout) (LBa : list ablock) (p : aptr) (n chg : Z)
    (r : astate * option aptr) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo' Aaddr, mrel A' moc' mo' ->
    MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\
    match snd r with
    | Some q => ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst r) (HB q Aaddr n :: lb_remove p LBa) mo'
    | None => ACCT (Z_to_bv 64 (bv_unsigned aw - 1048576)) L RNG' (fst r) LBa mo'
    end.
Hypothesis ACCT_realloc : forall aw L RNG st LBa mo p chp n chg,
  ACCT aw L RNG st LBa mo -> MP mo -> op_minv OPS mo -> (a_live st) !! p = Some chp -> 1 <= n <= AREQMAX -> chg_ok aw n chg -> 1048576 <= bv_unsigned aw ->
  C24.TwinB.c24count LBa <= 255 ->
  exists RESV A0 moc, aresv_ok L RESV /\ c6ok RESV RNG st /\ mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (aembed ATOP (ARealloc_x.TwinB.arealloc RESV st p n)) moc (acct_leaf_realloc mo aw L LBa p n chg).

Theorem arealloc_sound : forall pc, to_Z pc = F_arealloc_iseg.TwinB.AREALLOC_SYM -> contract_sound bsegs OPS MP PB (arealloc_c UNIV F_arealloc_iseg.TwinB.AREALLOC_PC pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc arealloc_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = F_arealloc_iseg.TwinB.AREALLOC_SYM) by (rewrite Hspc; exact Hpc).
  destruct (CtrRealloc.TwinB.arealloc_apply_shape UNIV F_arealloc_iseg.TwinB.AREALLOC_PC st sts Happ)
    as (r & hargs & wnl & st1 & kf & sh & cred & h1 & h2 & h3 & h4 & h5 & stN & PRE & X10E & FT & HA & FOKk & NV & TCAN & N0 & N1 & SS & NC & PRA & H1 & H2 & H3 & H4 & H5 & NPOST & ESTS).
  assert (ROOM : 4096 <= to_Z AREALLOC_ROOM < 2 ^ 32) by (vm_compute; split; congruence).
  destruct (CtrPre.TwinB.acall_pre_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng AREALLOC_ROOM F_arealloc_iseg.TwinB.AREALLOC_PC st r hargs wnl st1 E ms mo HS ROOM PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & MI & ST & BOT & LO & TP & AUNW & S0NE & RA4 & RANE & SP16 & RSTK & CP & FS & CF).
  destruct AUNW as [utr AUNW].
  pose proof (CtrPre.TwinB.acall_pre_room AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng AREALLOC_ROOM _ st r hargs wnl st1 E ms mo HS ROOM PRE) as LOR.
  destruct (CtrRealloc.TwinB.arealloc_block AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake E st ms mo r hargs wnl L RNG sta LBa aw kf sh cred HS CF FT FOKk TCAN X10E HA N0 N1 NC)
    as (p & lenf & WLf & HP & Ha0 & Ha1 & NR & NCR & CANM).
  set (n := bv_unsigned (den E (getr st X11))) in *.
  destruct NCR as [NCX NCR].
  set (chg := if prim_decided (s_facts st) (getr st X11) then 0 else n).
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH HP) as (_ & _ & _ & _ & _ & _ & (chp & LIVEp & _) & _).
  destruct (ACCT_realloc aw L RNG sta LBa mo p chp n chg AC HMP (so_mf _ _ _ _ _ _ HS) LIVEp NR (chg_of_pre E st X11 aw n (so_facts _ _ _ _ _ _ HS) eq_refl NCR) NCX
              (CtrPre.TwinB.acallG_c24 AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw CF)) as (RESV & A0 & moc & ROK & [C6M CAPB] & MR & MINV & HH & TW).
  set (R := ms_regs ms) in *.
  pose proof (AI_realloc L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) sta LBa p _ _ n (sp_lo E st) utr RESV AH HP CANM MI ST BOT
                ltac:(unfold ARealloc_x.TwinB.AREALLOC_STACK; change (to_Z AREALLOC_ROOM) with 12288 in LOR; lia) TP Ha0 Ha1 NR AUNW S0NE RA4 RANE SP16 RSTK ROK
                (so_fcsr _ _ _ _ _ _ HS) C6M CAPB (CtrNull.TwinB.errno_cells (ms_mem ms))) as IMPL.
  rewrite Ems, HPC. apply (GlueA.TwinB.realizes_to_mkRA bsegs).
  eapply (implS_twfS_realizes_silent bsegs NMAXt _ RNG A0 _ _ _ moc mo K IMPL TW HH MINV MR).
  intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
  assert (LEAF : forall Aaddr, MP mo' /\ op_minv OPS mo' /\ OTHER mo mo' /\
            match snd rr with
            | Some q => ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst rr) (HB q Aaddr n :: lb_remove p LBa) mo'
            | None => ACCT (Z_to_bv 64 (bv_unsigned aw - 1048576)) L RNG' (fst rr) LBa mo'
            end) by (intros Aaddr; exact (HP' mo' Aaddr MR')).
  destruct (LEAF 0) as (HMP' & HMI' & OTH & ACP0).
  destruct rr as [sta' [q|]]; unfold AInstanceU2F.TwinB.arealloc_post2x in HQ; cbn [fst snd] in HQ, ACP0, LEAF.
  -
    destruct (CtrRealloc.TwinB.arealloc_post_okA AI IMGX IMGX_aci IMGSH_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 Cw_ghost_free Cw_ghost_grow Cw_vec_unowned OPS_frame_other OPS_fp_other
                OTHER OPS_mo_other OPS_cov0_img st sts E ms mo r hargs wnl st1 kf sh cred h1 h2 h3 h4 h5 stN L RNG sta LBa aw p lenf n (sta', Some q) RNG' ms' mo'
                HS CP FS CF FT FOKk NV TCAN HA SS NC PRA H1 H2 H3 H4 H5 ESTS WLf HP eq_refl HQ
                ltac:(intros UB; destruct (LEAF UB) as (_ & _ & _ & X); exact X) HMI' OTH) as (stB & E' & -> & EXT & HS').
    eapply (HK stB); [right; left; reflexivity | exact EXT | exact HMP' | exact HS'].
  -
    pose proof (CtrNull.TwinB.acallN_of_G AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw CF) as CFN.
    assert (FO : find_op HEAP_ID (s_ops st) = Some hargs).
    { destruct CFN as (LB1 & ks1 & offs1 & rss1 & ksp1 & nn1 & md1 & A1 & nw1 & rest1 & _ & _ & _ & _ & _ & _ & Hf1 & _). exact Hf1. }
    assert (NPI : ~ CtrPre.TwinB.prist_in E st) by (exact (CtrPre.TwinB.prist_absent_not_in E st hargs (so_facts _ _ _ _ _ _ HS) FO PRA)).
    destruct (CtrNull.TwinB.anull_post_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                AERRNO_aci IMGSH_aci st E ms mo L RNG sta LBa aw r hargs wnl st1 cred stN sta' RNG' ms' mo'
                HS CP FS CFN AH HA NPOST BOT HQ ACP0 (fun PI _ => False_ind _ (NPI PI)) HMI' OTH) as (E1 & EXT & HS').
    eapply (HK stN); [rewrite ESTS; left; reflexivity | exact EXT | exact HMP' | exact HS'].
Qed.

Hypothesis AI_aligned16 : AInstanceU2F.TwinB.aaligned16_stmt2x (aci AI) (AHEAP AI).

Hypothesis ACCT_aligned16 : forall aw L RNG st LBa mo n chg,
  ACCT aw L RNG st LBa mo -> MP mo -> op_minv OPS mo -> 16 <= n <= 4096 -> n mod 16 = 0 -> chg_ok aw n chg -> 1048576 <= bv_unsigned aw ->
  exists RESV A moc, aresv_ok L RESV /\ c6ok RESV RNG st /\ mrel A moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A (aembed ATOP (aaligned16x ATOP RESV st n)) moc (acct_leaf mo aw L st LBa n chg).

Theorem aaligned_sound : forall pc, to_Z pc = F_aaligned_iseg.TwinB.AALIGNED_SYM ->
  contract_sound bsegs OPS MP PB (aaligned_c UNIV F_aaligned_iseg.TwinB.AALIGNED_PC pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc aaligned_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = F_aaligned_iseg.TwinB.AALIGNED_SYM) by (rewrite Hspc; exact Hpc).
  destruct (CtrPre.TwinB.aaligned_pre_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng st sts E ms mo HS HPC Happ)
    as (L & RNG & sta & LBa & aw & n & Ems & AH & AC & HU & MI & ST & BOT & LO & TP & Ha0 & Ha1 & PRIM & N16 & NR16 & NC & AUNW & S0NE & RA4 & RANE & SP16 & RSTK & CF & NOPR).
  destruct AUNW as [utr AUNW].
  assert (NR : 1 <= n <= AREQMAX) by (unfold AREQMAX; lia).
  destruct NC as [NCX NC]. destruct (CtrPre.TwinB.acall_facts_c24 AI ACCT UNIV Cw X11 E st ms mo L RNG sta LBa aw n CF) as [C24B NDEN].
  set (chg := if prim_decided (s_facts st) (getr st X11) then 0 else n).
  destruct (ACCT_aligned16 aw L RNG sta LBa mo n chg AC HMP (so_mf _ _ _ _ _ _ HS) NR16 N16 (chg_of_pre E st X11 aw n (so_facts _ _ _ _ _ _ HS) NDEN NC) NCX) as (RESV & A & moc & ROK & [C6M CAPB] & MR & MINV & HH & TW).
  set (R := ms_regs ms) in *.
  pose proof (AI_aligned16 L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) sta LBa n (sp_lo E st) utr RESV PRIM N16 AH MI ST BOT LO TP Ha0 Ha1 NR AUNW S0NE RA4 RANE SP16 RSTK ROK
                (so_fcsr _ _ _ _ _ _ HS) C6M CAPB (CtrNull.TwinB.errno_cells (ms_mem ms))) as IMPL.
  rewrite Ems. apply (GlueA.TwinB.realizes_to_mkRA bsegs).
  eapply (implS_twfS_realizes_silent bsegs NMAXt _ RNG A _ _ _ moc mo K IMPL TW HH MINV MR).
  intros r RNG' A' ms' moc' mo' HQ HP ACC' HH' MINV' MR'.
  assert (LEAF : forall Aaddr, MP mo' /\ op_minv OPS mo' /\ OTHER mo mo' /\
            match snd r with
            | Some p => ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst r) (HB p Aaddr n :: LBa) mo'
            | None => ACCT (Z_to_bv 64 (bv_unsigned aw - 1048576)) L RNG' (fst r) LBa mo'
            end /\ (64512 < n -> aprist sta -> aprist (fst r))) by (intros Aaddr; exact (HP mo' Aaddr MR')).
  destruct (LEAF 0) as (HMP' & HMI' & OTH & ACP0 & _).
  destruct r as [sta' [p|]]; unfold amalloc_post2x in HQ; cbn [fst snd] in HQ, ACP0, LEAF.
  -
    destruct (CtrPost.TwinB.aaligned_post_okA AI IMGX IMGX_aci IMGSH_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 Cw_ghost_grow OPS_frame_other OPS_fp_other
                OTHER OPS_mo_other OPS_cov0_img st sts E ms mo L RNG sta LBa aw n (sta', Some p) RNG' ms' mo' HS Happ CF HQ
                (fun Aaddr => proj1 (proj2 (proj2 (proj2 (LEAF Aaddr))))) NOPR HMI' OTH) as (stN & stB & E' & -> & EXT & HS').
    eapply (HK stB); [right; left; reflexivity | exact EXT | exact HMP' | exact HS'].
  -
    destruct (CtrPre.TwinB.aaligned_apply_inv UNIV st sts Happ) as (r0 & tp0 & hargs0 & cred0 & st10 & al0 & CP0 & _ & FO0 & HA0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FS0 & stN & stB0 & ESTS & NPOST).
    destruct (CtrNull.TwinB.acallN_of_facts AI ACCT UNIV Cw X11 E st ms mo L RNG sta LBa aw n CF) as (r1 & hargs1 & wnl1 & st11 & CP1 & FS1 & CFN).
    rewrite CP0 in CP1. injection CP1 as <-. rewrite FS0 in FS1. injection FS1 as <-.
    assert (EH : hargs1 = hargs0).
    { destruct CFN as (LB1 & ks1 & offs1 & rss1 & ksp1 & nn1 & md1 & A1 & nw1 & rest1 & _ & _ & _ & _ & _ & _ & Hf1 & _). rewrite FO0 in Hf1. injection Hf1 as E1. exact (eq_sym E1). }
    subst hargs1.
    destruct (CtrNull.TwinB.anull_post_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                AERRNO_aci IMGSH_aci st E ms mo L RNG sta LBa aw r0 hargs0 wnl1 st10 cred0 stN sta' RNG' ms' mo'
                HS CP0 FS0 CFN AH HA0 NPOST BOT HQ ACP0 (fun PI _ => False_ind _ (NOPR PI)) HMI' OTH) as (E1 & EXT & HS').
    eapply (HK stN); [rewrite ESTS; left; reflexivity | exact EXT | exact HMP' | exact HS'].
Qed.

Lemma afree0_apply_shape : forall PCz st sts, afree0_apply UNIV PCz st = Some sts ->
  exists r hargs wnl st1,
    acall_pre ASTACK (Some (UNIV, PCz)) st = Some (r, hargs, wnl, st1) /\ getr st X10 = VL wzero
    /\ sts = [setpc (setr (snd (fresh (clobber st1))) X10 (VP (fst (fresh (clobber st1))) wzero)) r].
Proof.
  intros PCz st sts H. unfold afree0_apply in H.
  destruct (acall_pre ASTACK (Some (UNIV, PCz)) st) as [[[[r hargs] wnl] st1]|] eqn:PRE; [|discriminate].
  destruct (getr st X10) as [w| | | | | | | | | |] eqn:X10E; try discriminate.
  destruct (weqb w wzero) eqn:W0; [|discriminate]. apply (proj1 (weqb_ok _ _)) in W0. subst w.
  exists r, hargs, wnl, st1. split; [reflexivity|]. split; [reflexivity|].
  destruct (fresh (clobber st1)) as [v st3] eqn:F. injection H as <-. reflexivity.
Qed.

Theorem afree0_sound : forall pc, to_Z pc = AFREE_SYM -> contract_sound bsegs OPS MP PB (afree0_c UNIV AFREE_PC pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc afree0_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = AFREE_SYM) by (rewrite Hspc; exact Hpc).
  destruct (afree0_apply_shape AFREE_PC st sts Happ) as (r & hargs & wnl & st1 & PRE & X10E & ESTS).
  destruct (CtrPre.TwinB.acall_pre_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK AFREE_PC st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & MI & ST & BOT & LO & TP & AUNW & S0NE & RA4 & RANE & SP16 & RSTK & CP & FS & CF).
  destruct AUNW as [utr AUNW].
  set (R := ms_regs ms) in *. set (sp := bv_unsigned (AP.getr R 2)) in *. set (m := ms_mem ms) in *.
  pose proof atop_range as ATR.
  assert (Ha0 : AP.getr R 10 = Z_to_bv 64 0).
  { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X10, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10), X10E. reflexivity. }
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (AI_free_null AI L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) m sta LBa (sp_lo E st) utr AH MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK) as EV.
  rewrite Ems, HPC. apply (GlueA.TwinB.realizes_to_mkRA bsegs).
  eapply (implS_twfS_realizes_silent bsegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ afree_null_post2 (aci AI) (AHEAP AI) L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4)
               (AP.getr R 8) (AP.getr R 9) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
               (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) sta LBa (sp_lo E st) m ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MINV'' & STK' & PRES & TWP & AH').
    fold sp in PRES.
    match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
    set (Fv := CtrFree.TwinB.cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
    destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
    assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
    { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X1, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X1), Hra0, ER.
      assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.TwinB.den_wlit. }
    assert (EMS' : ms' = CtrFrame.TwinB.ms' ms r R' m').
    { rewrite EMS. unfold CtrFrame.TwinB.ms'. f_equal. rewrite RAEQ. apply MState.ret_pc_even.
      - pose proof (int_range r) as RRr. rewrite two63_eq in RRr. lia.
      - pose proof (HeapCtr.TwinB.call_pre_even st r CP) as EV0.
        pose proof (ValP.land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
        change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV0 in LM. change (to_Z 0%uint63) with 0 in LM.
        change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }

    pose proof CF as CF0.
    destruct CF0 as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                    & NW & AN & AJ & TS & WF & HC & AWden & (Wt & WOF & ARW & TI)).
    destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0' & OP & PV & NXc).
    destruct (CtrFrame.TwinB.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
    assert (XE : s_next (clobber st1) = addn (s_next st) 15).
    { rewrite NXc, NX1. symmetry. destruct (CtrFrame.TwinB.NX st FOK) as (_ & _ & B). pose proof (int_range (s_next st)) as RRn. rewrite two63_eq in RRn.
      apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia]. }
    assert (SHAPE : sts = [SS r (rf_set (s_rf (clobber st1)) X10 (VP (addn (s_next st) 15) wzero)) (s_ff st) (s_resv st) (s_regs st1) (s_facts st)
                              (s_ops st) (s_priv st) (PrimInt63.add (addn (s_next st) 15) 1%uint63)]).
    { rewrite ESTS. unfold fresh. cbn [fst snd]. rewrite XE. f_equal.
      assert (G : forall (S : sstate) nx1 v, setpc (setr (set_next S nx1) X10 v) r
                  = SS r (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (s_regs S) (s_facts S) (s_ops S) (s_priv S) nx1) by (intros [] ? ?; reflexivity).
      rewrite G, FF, RV, RG, FS0', OP, PV, FF1, RV1, FS1, OP1, PV1. reflexivity. }
    apply (HK _ ltac:(rewrite SHAPE; left; reflexivity) (CtrFrame.TwinB.E' E st Fv Gv) ms' mo' (CtrFrame.TwinB.EXT E st Fv Gv) HMP').
    rewrite EMS'.

    assert (RAWV : forall a, m' (ALib.Mem.wa a) = m (ALib.Mem.wa a) -> rb bsegs m' a = rb bsegs m a /\ (wb bsegs m a = true -> wb bsegs m' a = true)).
    { intros a EQ. split; [unfold rb; unfold ALib.Mem.wa in EQ; rewrite EQ; reflexivity|].
      intros Wb. apply (GlueA.TwinB.wb_wviewA bsegs). apply (GlueA.TwinB.wb_wviewA bsegs) in Wb. rewrite (wview_ext1 m' m _ EQ). exact Wb. }
    assert (CLX : forall a, 0 <= a < 2 ^ 64 -> aclient_addr (aci AI) LBa sp a ->
              rb bsegs m' a = rb bsegs m a /\ (wb bsegs m a = true -> wb bsegs m' a = true)).
    { intros a Ha CA. apply RAWV. exact (proj1 (PRES a Ha CA)). }
    assert (STBx : forall LB0, aw_real AI ACCT UNIV aw LB0 m mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> CtrFrame.TwinB.stableA AI ms LB0 a ->
              m' (ALib.Mem.wa a) = m (ALib.Mem.wa a)).
    { intros LB0 (W0 & (E1 & E2 & E3 & E4) & ARW0) a Ha ST0. pose proof ARW0 as [HW0 _]. pose proof HW0 as (_ & HT0 & _).
      destruct (LB_classify AI ACCT UNIV AI_fake W0 aw LB0 m mo HW0) as (KU & KT).
      apply (aw_real_stable AI ACCT UNIV AI_fake aw LB0 m mo W0 RNG sta LBa m' LBa LB0 sp LBa TWP ltac:(intros b0 Hb0 _ _; rewrite <- E4; exact Hb0) ARW0).
      - rewrite E1. exact AH'.
      - exact PRES.
      - intros v Hv UB P. destruct (KU v Hv UB P) as (b & Vb & ->). exists b. split; [rewrite <- E4; exact (proj1 Vb)| reflexivity].
      - intros v Hv NUB. destruct (KT v Hv NUB) as [(b & Hb & ->)|(b & Vb & ->)].
        + left. exists b. destruct (HT0 b Hb) as [HbL HH0]. split; [exact HbL|]. split; [rewrite <- E4; exact HbL|]. split; [exact HH0| reflexivity].
        + right. exists b. split; [exact (proj1 (proj1 Vb))|]. split; [rewrite <- E4; exact (proj1 (proj1 Vb))|]. split; [exact (proj2 Vb)| reflexivity].
      - exact Ha.
      - exact ST0. }
    apply (CtrNoDelta.TwinB.nodelta_st_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other
             OPS_cov0_img E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG sta _ _ HS CP FS CF).
    +
      intros rg Hrg. unfold CtrFrame.TwinB.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
    + intros x i Hx. exact (CtrFree.TwinB.cfvF_clob R' x i Hx).
    + rewrite HeapCtr.TwinB.den_VPz. rewrite (CtrFrame.TwinB.ev_E'_fresh E st FOK Fv Gv 15 ltac:(lia)). reflexivity.
    + exact MINV''.
    + exact STK'.
    +   intros LB0 AR0 a Ha STB. apply RAWV. exact (STBx LB0 AR0 a Ha STB).
    +   intros LB0 AR0 a Ha IU. apply (STBx LB0 AR0 a Ha). right; right. exact IU.
    +
      intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
      assert (CA : aclient_addr (aci AI) LBa sp a).
      { destruct (OPS_fp_other _ _ a NI FP) as [INA|[(a' & INA & ->)|(a' & STK & ->)]].
        - right; left; exact INA.
        - right; right; right. exists a'. split; [right; left; exact INA| reflexivity].
        - right; right; right. exists a'. split; [left; exact STK| reflexivity]. }
      pose proof (proj1 (PRES a ltac:(unfold two64 in Ha; lia) CA)) as E0. unfold ALib.Mem.wa in E0. exact E0.
    +
      intros a Ha CC Wb. apply (CLX a ltac:(unfold two64 in Ha; lia)); [| exact Wb].
      destruct CC as [CC|[(a' & CC & ->)|(a' & CC & ->)]]; [right; left; exact CC| |]; right; right; right; exists a'; (split; [| reflexivity]); [right; left; exact CC| left; exact CC].
    +
      intros a Ha SC IB. apply (CLX a Ha).
      destruct SC as [(a' & RRa & ->)|(vv & Hv & RRa)].
      * right; right; right. exists a'. split; [left; exact RRa| reflexivity].
      * destruct (IMGSH_aci vv a Hv RRa) as (a' & INA & ->). right; right; right. exists a'. split; [right; left; exact INA| reflexivity].
    + exact AH'.
    + exact ACP.
    +
      intros b x Hb FK Hx. pose proof (Op.TwinB.blk_band AI AI_fake L RNG sta LBa m b x AH Hb Hx) as BB.
      exact (proj1 (PRES x ltac:(unfold AIMG_HI, KLS in BB; lia) ltac:(right; right; left; exists b; split; [exact Hb| exact Hx]))).
    + exact TWP.
    + exact OTH.
    + exact HMI'.
    + intros P; exact P.
Qed.

End Sound.
End TwinB.
