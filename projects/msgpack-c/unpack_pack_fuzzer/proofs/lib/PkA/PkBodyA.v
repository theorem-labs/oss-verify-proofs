(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_asan_memcpy.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs DefsA DefsB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB MemFX RstageCtr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CallV GlueA CtrPre CtrFrame CtrNoDelta CtrFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggGeo UnreggPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import UnreggSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import MemOps RangeC SinkC MemsetFX RangePre MemsetPre MemsetPost RegRepl MemcpySound Memcpy0Sound RstageSound RstagePost.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require MemcpyCtr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import RtCells.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadPost.
Import ValP MemP StepB CtrFX ActrA SinkC.
Module IMC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.I_memcpy.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import SinkSound.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CtrPat.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import StackSh RangeC RangeFX MemcpyC RangePre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require ShLaw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv GLib PkOps PkLib PkBody.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA Require Import VecCopy2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA Require Import PkBodyAC PkBodySrc.
Unset Nia Cache. Unset Nra Cache.
Import UG.

Module PkBodyA.
Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.cov1 HEAP_ID args z.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb asegs m a = true -> wb asegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> op_cov0 OPS a.
Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Hypothesis W_PAT : w_pat_ev_stmt AI ACCT UNIV Cw OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).
Hypothesis OPS_holds_ssh : forall m mo, op_holds OPS RangeC.SSH_ID [] m mo -> ssh_holds m.
Hypothesis ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP).
Hypothesis ACCT_frng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> FRNG AI AI_fake L RNG.
Variable SYM : Z.
Hypothesis WALK : memcpy_walk_stmt SYM.
Variable FRM0 : Z.
Hypothesis FR0 : 0 < FRM0 <= 8192.
Hypothesis WALK0 : memcpy0_walk_stmt SYM FRM0.
Variable AWx : alloc_world asegs IMGX.
Hypothesis HOPS : heap_ops asegs IMGX AWx Cw OPS.
Hypothesis CW3 : forall ca LB ws m, cw_holds Cw 3 ca LB ws m -> PK.cw_pk_holds asegs ca LB ws m.

Lemma LB_bound : forall W aw LB m mo v, aw_holds_w AI ACCT UNIV W aw LB m mo -> In v LB -> fst v + snd v <= 2 ^ 64.
Proof.
  intros W aw LB m mo v HW Hv. pose proof atop_range as ATR.
  destruct (LB_cases AI ACCT UNIV W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]].
  - destruct (LB_user_facts AI ACCT UNIV AI_fake W aw LB m mo b HW Vb) as (_ & _ & _ & HI). pose proof (usz_le b). unfold user_iv. cbn [fst snd]. lia.
  - destruct (LB_twin_facts AI ACCT UNIV W aw LB m mo b HW Hb) as (_ & T2 & _). unfold twin_iv. cbn [fst snd]. lia.
  - destruct (LB_fsh_facts AI ACCT UNIV AI_fake W aw LB m mo b HW Vb) as (_ & T2 & _). unfold fsh_iv. cbn [fst snd]. lia.
Qed.

Lemma chunk_block_pat : forall W aw LB m mo ws cs c,
  aw_holds_w AI ACCT UNIV W aw LB m mo -> ties W ws -> Seal.Seal.seal_ok ws cs -> In c cs -> In (Inv.chunk_block c) LB ->
  (forall w, In w ws -> (w_kind w = HeapOp.K_BLOCK \/ K_GHOST <= w_kind w) -> forall a, in_iv (w_iv w) a -> ~ in_iv (Inv.chunk_block c) a) ->
  0 < snd (Inv.chunk_block c) ->
  exists p, In (HB p (fst (Inv.chunk_block c)) (snd (Inv.chunk_block c))) (w_LBa W) /\ ablock_shadow m (fst (Inv.chunk_block c)) (snd (Inv.chunk_block c)).
Proof.
  intros W aw LB m mo ws cs c HW TI [SEAL S8] Hc HLB APART POS.
  pose proof TI as (T1 & T2 & T3 & _). set (v := Inv.chunk_block c) in *. pose proof HW as (AH & HT & _).
  destruct (LB_cases AI ACCT UNIV W aw LB m mo v HW HLB) as [(b & Vb & Ev)|[(b & Hb & Ev)|(b & Vb & Ev)]].
  2:{ exfalso. pose proof (T1 b Hb) as WIN. destruct (LB_twin_facts AI ACCT UNIV W aw LB m mo b HW Hb) as (_ & _ & P1).
      apply (APART _ WIN ltac:(right; unfold K_GHOST, K_TWINz; cbn; lia) (fst v)).
      - unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. rewrite Ev. unfold twin_iv. cbn [fst snd]. lia.
      - unfold in_iv. lia. }
  2:{ exfalso. destruct (T3 b Vb) as [_ WIN]. destruct (LB_fsh_facts AI ACCT UNIV AI_fake W aw LB m mo b HW Vb) as (_ & _ & P1 & _).
      apply (APART _ WIN ltac:(right; unfold K_GHOST, K_FTWINz; cbn; lia) (fst v)).
      - unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. rewrite Ev. unfold fsh_iv. cbn [fst snd]. lia.
      - unfold in_iv. lia. }
  destruct (kind_cases b) as [HH|HF].
  2:{ exfalso. destruct (T3 b (conj Vb HF)) as [WIN _].
      destruct (blk_facts AI AI_fake _ _ _ _ _ b AH (proj1 Vb)) as (NP & _).
      destruct (AI_fake _ _ _ _ _ b AH (proj1 Vb) HF) as (_ & _ & _ & _ & N64 & _).
      apply (APART _ WIN ltac:(right; unfold K_GHOST, K_FRAMEz; cbn; lia) (ab_addr b)).
      - unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. lia.
      - rewrite Ev. unfold in_iv, user_iv. cbn [fst snd]. rewrite (usz_fake b HF). lia. }
  assert (NT : ~ In b (w_T W)).
  { intros HbT. pose proof (T1 b HbT) as WIN. apply (SEAL _ WIN eq_refl c Hc). cbn [w_lo]. rewrite ShLaw.shadZ_shad.
    replace (fst c) with (fst v) by reflexivity. rewrite Ev. reflexivity. }
  destruct HH as [p KP]. exists p.
  assert (EB : HB p (fst v) (snd v) = b).
  { rewrite Ev. unfold user_iv. cbn [fst snd]. rewrite (usz_heap b (ex_intro _ p KP)). destruct b as [kd ad sz]. cbn [ab_kind ab_addr ab_size] in *. subst kd. reflexivity. }
  split; [rewrite EB; exact (proj1 Vb)|].
  pose proof (CtrPat.aw_pat_in AI ACCT UNIV AI_fake W aw LB m mo b HW Vb (ex_intro _ p KP) NT) as PAT.
  rewrite <- EB in PAT. cbn [ab_addr ab_size] in PAT. exact PAT.
Qed.

Theorem pkbody_sound : forall pc, to_Z pc = SYM -> contract_sound asegs OPS MP PB (PkBodyAC.pkbody_c asegs pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc PkBodyAC.pkbody_c] in Happ, Hspc. rewrite PkBodyAC.pkbody_apply_eq in Happ. unfold PkBodyAC.pkbody_apply_spec in Happ.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:PRE; [|discriminate Happ].
  destruct (CtrA.sym_offset (s_regs st) (getr st X10)) as [[kS OFF]|] eqn:DOFF; [|discriminate Happ].
  destruct (IMap.find kS (s_regs st)) as [rS|] eqn:HkS; [|discriminate Happ].
  destruct (CtrA.win_lookup wnl kS) as [[lenS kdS]|] eqn:WLS; [|discriminate Happ].
  cbv zeta in Happ.
  match type of Happ with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate Happ] end.
  injection Happ as <-.
  apply andb_prop in C2 as [C2 SRC]. apply andb_prop in C2 as [C2 PATS]. apply andb_prop in C2 as [C2 LE3]. apply andb_prop in C2 as [C2 LE2]. apply andb_prop in C2 as [C2 LE1].
  apply andb_prop in C2 as [C2 NOC]. apply andb_prop in C2 as [C2 Ws]. apply andb_prop in C2 as [C2 LOs]. apply andb_prop in C2 as [C2 BGs].
  apply andb_prop in C2 as [KS0 KDS]. apply negb_true_iff in KS0. apply Uint63.eqb_correct in LOs. apply ValP.weqb_eq in KDS. subst kdS.
  assert (BG : rg_bg rS = BGNone) by (destruct (rg_bg rS); try discriminate BGs; reflexivity).
  assert (HPC : to_Z (s_pc st) = SYM) by (rewrite Hspc; exact Hpc).
  pose proof (so_facts _ _ _ _ _ _ HS) as Pfacts.
  pose proof atop_range as ATR. pose proof two64_eq as T64.
  set (m := ms_mem ms) in *.
  assert (ENZ : exists nZ, nZ = bv_unsigned (den E (getr st X12))) by (eexists; reflexivity). destruct ENZ as [nZ ENZ].
  destruct (Z.eq_dec nZ 0) as [NZ0|NZ1].
  {
    apply (mc0_core AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
             MP NMAXt ACCT_rng ACCT_rng_aimg ACCT_silent SYM FRM0 FR0 WALK0 st K E ms mo r hargs wnl st1 HS HMP HPC PRE); [| exact HK].
    change (AP.getr (ms_regs ms) 12) with (AP.getr (ms_regs ms) (reg_of_r5 X12)). rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X12).
    apply bv_eq. rewrite Z_to_bv_unsigned, <- ENZ, NZ0. reflexivity. }

  destruct (CtrPre.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L0 & RNG0 & sta0 & LBa0 & aw0 & Ems & AH0 & AC0 & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF0).

  pose proof (so_reg _ _ _ _ _ _ HS kS rS HkS) as ROs.
  set (BS := bv_unsigned (ev E kS)) in *. set (offZ := bv_unsigned (den E OFF)) in *.
  pose proof (bv_unsigned_in_range 64 (den E OFF)) as OR. rewrite bv_modulus_64 in OR. fold offZ in OR.
  pose proof (bv_unsigned_in_range 64 (den E (getr st X12))) as NR. rewrite bv_modulus_64, <- ENZ in NR.
  apply (HeapCtr.known_leu_sound E _ _ _ Pfacts) in LE1. apply (HeapCtr.known_leu_sound E _ _ _ Pfacts) in LE2. apply (HeapCtr.known_leu_sound E _ _ _ Pfacts) in LE3.
  fold offZ in LE1. change (bv_unsigned (den E (rg_hi rS))) with (hiZ E rS) in LE1, LE3.
  rewrite <- ENZ in LE2. rewrite ValP.den_sv_alu in LE2. cbn [alu64 alu] in LE2. rewrite bv_sub_unsigned in LE2. fold offZ in LE2.
  change (bv_unsigned (den E (rg_hi rS))) with (hiZ E rS) in LE2.
  pose proof (ro_range _ _ _ _ _ _ ROs KS0) as [RLs RHs]. fold BS in RLs, RHs.
  assert (LZs : loZ rS = 0) by (unfold loZ; rewrite LOs; reflexivity). rewrite LZs in RLs.
  pose proof (bv_unsigned_in_range 64 (den E (rg_hi rS))) as HSR. rewrite bv_modulus_64 in HSR. change (bv_unsigned (den E (rg_hi rS))) with (hiZ E rS) in HSR.
  assert (SUM : offZ + nZ <= hiZ E rS).
  { unfold bv_wrap in LE2. rewrite bv_modulus_64 in LE2. rewrite Z.mod_small in LE2; unfold two64 in *; lia. }
  assert (DA : bv_unsigned (den E (getr st X10)) = BS + offZ).
  { rewrite (MemcpyCtr.sym_offset_sound E (s_regs st) _ kS OFF DOFF). rewrite bv_add_unsigned. fold BS offZ. apply bv_wrap_small. rewrite bv_modulus_64. unfold two64 in *. lia. }
  set (S := bv_unsigned (den E (getr st X11))) in *.

  assert (SRCX : (S + nZ <= BS + offZ \/ BS + offZ + nZ <= S) /\
                 (forall L RNG sta LBa aw, CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> AHEAP AI L RNG sta LBa m ->
                    ACCT aw L RNG sta LBa mo -> srcF RNG m (bv_unsigned (AP.getr (ms_regs ms) 2)) S nZ)).
  { apply orb_prop in SRC as [SRCR|SRCB].
    -
      unfold PkBodyAC.lit_src_ok in SRCR.
      destruct (getr st X11) as [|ks os| | | | | | | | |] eqn:G11; try discriminate SRCR.
      destruct (getr st X12) as [nw| | | | | | | | | |] eqn:G12; try discriminate SRCR.
      apply andb_prop in SRCR as [SRCR RIN]. apply andb_prop in SRCR as [SRCR KK]. apply andb_prop in SRCR as [SRCR NMX]. apply andb_prop in SRCR as [WTN N1].
      apply negb_true_iff in WTN. apply negb_true_iff in KK. apply Uint63.eqb_false_spec in KK. apply Uint63.leb_spec in N1. apply Uint63.leb_spec in NMX.
      change (to_Z 1%uint63) with 1 in N1. change (to_Z RangeC.NMAX) with 4096 in NMX.
      assert (ENW : nZ = to_Z (wl nw)) by (rewrite ENZ; cbn [den]; rewrite wbv_unsigned; unfold w2Z; rewrite WTN; lia).
      destruct (range_in_inv _ _ _ _ _ _ RIN) as (rs & cs & FSs & IRS & RCS & KS0s & _).
      destruct (in_region_s_sound E _ rs os (wl nw) Pfacts IRS ltac:(lia)) as (S1 & S2).
      destruct (range_class_facts_ev AI ACCT UNIV Cw OPS AI_fake Cw_sub_ghost OPS_holds_ssh ACCT_rng ACCT_rng_stk_sh ACCT_frng W_PAT E st ms mo r hargs wnl
                  L0 RNG0 sta0 LBa0 aw0 ks os (wl nw) false cs HS CF0 AH0 AC0 BOT LO SPT RCS ltac:(lia)) as (DEN1 & _).
      assert (ES : S = bv_unsigned (ev E ks) + w2Zs os) by (unfold S; exact DEN1).
      split.
      + pose proof (so_disj _ _ _ _ _ _ HS kS rS ks rs HkS FSs ltac:(intros Q; apply KK; symmetry; exact Q) KS0 KS0s (or_introl Ws)) as NO.
        destruct (Z_le_gt_dec (S + nZ) (BS + offZ)) as [Q1|Q1]; [left; exact Q1|]. destruct (Z_le_gt_dec (BS + offZ + nZ) S) as [Q2|Q2]; [right; exact Q2|].
        exfalso. apply (NO (Z.max (BS + offZ) S)). rewrite LZs. fold BS. rewrite ES in *. lia.
      + intros L RNG sta LBa aw CF AH AC.
        destruct (range_class_facts_ev AI ACCT UNIV Cw OPS AI_fake Cw_sub_ghost OPS_holds_ssh ACCT_rng ACCT_rng_stk_sh ACCT_frng W_PAT E st ms mo r hargs wnl
                    L RNG sta LBa aw ks os (wl nw) false cs HS CF AH AC BOT LO SPT RCS ltac:(lia)) as (_ & LOW1 & HI1 & POS1 & SRCBY & _ & APB1 & UNP1 & RNG1 & HULL).
        rewrite ES, ENW.
        split; [exact HI1|]. split; [exact POS1|]. split; [exact SRCBY|]. split; [exact APB1|]. split; [exact UNP1|]. split; [exact RNG1| exact HULL].
    -
      pose proof SRCB as SRCB'. unfold PkBody.body_src_ok in SRCB'.
      destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate SRCB'].
      apply andb_prop in SRCB' as [MD _]. apply Uint63.eqb_correct in MD. subst mdi.
      destruct (the_op_full st 3%uint63 aw ws ca TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN').
      split.
      +
        pose proof (ops_hold_in OPS _ _ _ _ o (so_ops _ _ _ _ _ _ HS) (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
        destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
        rewrite (DECf E) in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC. apply CW3 in HC.
        pose proof (aw_ceiling_small asegs IMGX AWx mo) as CEIL. unfold two62Z in CEIL.
        destruct (PkBodySrc.body_src_facts asegs E st aw ws ca LB _ m Pfacts TO SRCB HC
                    ltac:(intros b Hb; destruct (aw_blocks_ok asegs IMGX AWx _ LB _ m mo b HA Hb) as (B1 & B2 & B3 & _); lia))
          as [Z0|(NZ & g & ls & c & P & O & Wk & GH1 & Hc & CLO & CHI)]; [rewrite <- ENZ in Z0; contradiction|].
        rewrite <- ENZ in CHI. fold S in CLO, CHI.
        assert (INLB : In (chunk_block c) LB) by (apply (proj1 O); unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc).
        destruct (aw_blocks_ok asegs IMGX AWx _ LB _ m mo (chunk_block c) HA INLB) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
        unfold chunk_block in Bc1, Bc2, Bc3, Bc5. cbn [fst snd] in Bc1, Bc2, Bc3, Bc5.
        apply (CopyFX.CopyFX.sep_of_pointwise S (BS + offZ) nZ ltac:(lia)). intros j j' Hj Hj' EQ.
        assert (INB : in_iv (fst c, CHUNK_HDR + snd c) (S + j)) by (unfold in_iv, chunk_lo, chunk_hi, CHUNK_HDR in *; cbn [fst snd]; lia).
        assert (FP : Exists (fun q => fst q <= S + j < snd q) (St.op_fp OPS (op_id o) (map (den E) (op_args o)))).
        { rewrite OID, (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ _ _ _ _ (S + j) (DECf E))).
          split; [unfold two64; lia|]. split; [exact (Bc5 _ INB)|].
          intros IW. apply in_ws_map_iff in IW as (w & Hw & INW).
          pose proof (proj1 (Forall_forall _ _) WF (wden E w) (in_map _ _ _ Hw)) as (_ & _ & _ & [[KSk CEk]|OTHERk]).
          - unfold in_iv, w_iv in INW. unfold in_iv in INB. cbn [fst snd] in INW, INB. lia.
          - assert (NK : w_kind (wden E w) <> K_STACK) by (destruct OTHERk as [[-> _]|[KS _]]; [discriminate| unfold K_SUB, K_STACK in *; lia]).
            destruct (proj1 (Forall_forall _ _) Wk (wden E w) (in_map _ _ _ Hw) NK) as [[_ DISJ]|[_ ET]].
            + apply (DISJ (chunk_block c) ltac:(unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc) (S + j) INW). exact INB.
            + exact (PK.safe_zone g ls LB (map (wden E) ws) P O S nZ (S + j) ltac:(lia) (ex_intro _ c (conj Hc (conj CLO CHI))) ltac:(lia) (wden E w) (in_map _ _ _ Hw) ET INW). }
        destruct (proj1 (Forall_forall _ _) (so_apart _ _ _ _ _ _ HS) o (op_in_In st o OPS1) (S + j) FP) as [NB _].
        apply NB. exists kS, rS. split; [exact HkS|]. split; [exact KS0|]. fold BS. rewrite LZs. rewrite EQ. lia.
      +
        intros L RNG sta LBa aw' CF AH AC.
        pose proof CF as (LB & ks & offs & rss & ksp & nn & mdw & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc0 & Eh & Tnw & Nn & Ln & N255
                          & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
        pose proof (ReadPost.count_one_args HEAP_ID (s_ops st) o hargs (op_in_In st o OPS1) OID Hc0 Hf) as EA.
        pose proof (decode_hargs E mdw A nw rest nn Tnw Nn Ln) as D1. rewrite <- Eh, <- EA, (DECf E) in D1. injection D1 as M1 _ W1 C1.
        change (nn + (nn + (nn + 0)))%nat with (3 * nn)%nat in C1.
        rewrite <- M1, <- C1, <- W1 in HC. rewrite <- W1 in TI. change (to_Z 3%uint63) with 3 in HC. apply CW3 in HC.
        destruct ARW as [HW WMS]. destruct WOF as (_ & _ & _ & WLBa).
        destruct (PkBodySrc.body_src_facts asegs E st aw ws ca LB _ m Pfacts TO SRCB HC (fun b Hb => LB_bound W aw' LB m mo b HW Hb))
          as [Z0|(NZ & g & ls & c & P & O & Wk & GH1 & Hc & CLO & CHI)]; [rewrite <- ENZ in Z0; contradiction|].
        rewrite <- ENZ in CHI. fold S in CLO, CHI.
        assert (OWNc : In (chunk_block c) (PK.owned g)) by (unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc).
        destruct (chunk_block_pat W aw' LB m mo (map (wden E) ws) (z_chunks (PK.k_zone g)) c HW TI (proj1 GH1) Hc (proj1 O _ OWNc)) as (p & HIN & PAT).
        { intros w0 Hw0 KD0 a Ha0 Hb0.
          destruct (proj1 (Forall_forall _ _) Wk w0 Hw0 ltac:(unfold HeapOp.K_STACK, HeapOp.K_BLOCK, K_GHOST in *; lia)) as [[_ DJ]|[_ ET]].
          - exact (DJ _ OWNc a Ha0 Hb0).
          - destruct ET as (K6 & _). unfold PK.K_ETOP, HeapOp.K_BLOCK, K_GHOST in *. lia. }
        { exact (PK.owned_pos g ls P _ OWNc). }
        rewrite WLBa in HIN. unfold chunk_block in HIN, PAT. cbn [fst snd] in HIN, PAT.
        destruct (block_range_facts AI L RNG sta LBa m p (fst c) (CHUNK_HDR + snd c) S nZ AH HIN PAT
                    ltac:(unfold chunk_lo, CHUNK_HDR in *; lia) ltac:(unfold chunk_hi, CHUNK_HDR in *; lia) ltac:(lia))
          as ((src & SRCC) & APB1 & UNP1 & LOWs & HIs & RNGS & RLOs & RHIs & HULLs & WRHs & RNGHs).
        split; [lia|]. split; [left; exact HIs|].
        split. { exists src. destruct SRCC as [[WFs BYs] _]. cbn [cells_wf cell_wf] in WFs. cbn [cells_bytes cbytes] in BYs. rewrite app_nil_r in BYs.
                 split; [exact (proj1 WFs)| exact BYs]. }
        split; [exact APB1|]. split; [exact UNP1|]. split; [exact RNGS|]. exists RLOs, RHIs. split; [exact HULLs|]. split; [exact WRHs| exact RNGHs]. }
  destruct SRCX as [SEP SRCF].
  apply (acopy_cps AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           Cw_sub_ghost W_PAT MP NMAXt ACCT_rng ACCT_rng_aimg ACCT_silent SYM WALK
           st K E ms mo r hargs wnl st1 kS rS lenS (wlit 1%uint63) offZ S nZ HS HMP HPC PRE DA ltac:(lia) HkS BG LOs Ws WLS ltac:(vm_compute; reflexivity) PATS
           ltac:(lia) SUM LE3).
  - intros g0 gr c0 i Hf. unfold PkBodyAC.no_cells in NOC. destruct (rg_cells rS); [discriminate Hf| discriminate NOC].
  - reflexivity.
  - symmetry. exact ENZ.
  - exact SEP.
  - exact SRCF.
  - intros E' ms' mo' HX HMP' HS' _. exact (HK _ (or_introl eq_refl) E' ms' mo' HX HMP' HS').
Qed.
End Sound.
End PkBodyA.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB.
Import AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsB.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import UnreggSound.TwinB.
Import MemOps.TwinB RangeC.TwinB SinkC.TwinB MemsetFX.TwinB RangePre.TwinB MemsetPre.TwinB MemsetPost.TwinB RegRepl.TwinB MemcpySound.TwinB Memcpy0Sound.TwinB RstageSound.TwinB RstagePost.TwinB.

Import RtCells.TwinB.

Import ValP MemP StepB CtrFX ActrA SinkC.TwinB.SinkC.
Module IMC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.TwinB.I_memcpy.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Import SinkSound.TwinB.

Import StackSh.TwinB RangeC.TwinB RangeFX.TwinB MemcpyC.TwinB RangePre.TwinB.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Model OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Layout OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Inv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkOps OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkBody.
Import VecCopy2.TwinB.
Import PkBodyAC.TwinB PkBodySrc.TwinB.
Unset Nia Cache. Unset Nra Cache.
Import UG.

Module PkBodyA.
Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Bridge.Op.TwinB.cov1 HEAP_ID args z.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb bsegs m a = true -> wb bsegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> op_cov0 OPS a.
Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Hypothesis W_PAT : w_pat_ev_stmt AI ACCT UNIV Cw OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).
Hypothesis OPS_holds_ssh : forall m mo, op_holds OPS RangeC.TwinB.RangeC.SSH_ID [] m mo -> ssh_holds m.
Hypothesis ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP).
Hypothesis ACCT_frng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> FRNG AI AI_fake L RNG.
Variable SYM : Z.
Hypothesis WALK : memcpy_walk_stmt SYM.
Variable FRM0 : Z.
Hypothesis FR0 : 0 < FRM0 <= 8192.
Hypothesis WALK0 : memcpy0_walk_stmt SYM FRM0.
Variable AWx : alloc_world bsegs IMGX.
Hypothesis HOPS : heap_ops bsegs IMGX AWx Cw OPS.
Hypothesis CW3 : forall ca LB ws m, cw_holds Cw 3 ca LB ws m -> PK.cw_pk_holds bsegs ca LB ws m.

Lemma LB_bound : forall W aw LB m mo v, aw_holds_w AI ACCT UNIV W aw LB m mo -> In v LB -> fst v + snd v <= 2 ^ 64.
Proof.
  intros W aw LB m mo v HW Hv. pose proof atop_range as ATR.
  destruct (LB_cases AI ACCT UNIV W aw LB m mo v HW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]].
  - destruct (LB_user_facts AI ACCT UNIV AI_fake W aw LB m mo b HW Vb) as (_ & _ & _ & HI). pose proof (usz_le b). unfold user_iv. cbn [fst snd]. lia.
  - destruct (LB_twin_facts AI ACCT UNIV W aw LB m mo b HW Hb) as (_ & T2 & _). unfold twin_iv. cbn [fst snd]. lia.
  - destruct (LB_fsh_facts AI ACCT UNIV AI_fake W aw LB m mo b HW Vb) as (_ & T2 & _). unfold fsh_iv. cbn [fst snd]. lia.
Qed.

Lemma chunk_block_pat : forall W aw LB m mo ws cs c,
  aw_holds_w AI ACCT UNIV W aw LB m mo -> ties W ws -> Seal.Seal.seal_ok ws cs -> In c cs -> In (Inv.chunk_block c) LB ->
  (forall w, In w ws -> (w_kind w = HeapOp.K_BLOCK \/ K_GHOST <= w_kind w) -> forall a, in_iv (w_iv w) a -> ~ in_iv (Inv.chunk_block c) a) ->
  0 < snd (Inv.chunk_block c) ->
  exists p, In (HB p (fst (Inv.chunk_block c)) (snd (Inv.chunk_block c))) (w_LBa W) /\ ablock_shadow m (fst (Inv.chunk_block c)) (snd (Inv.chunk_block c)).
Proof.
  intros W aw LB m mo ws cs c HW TI [SEAL S8] Hc HLB APART POS.
  pose proof TI as (T1 & T2 & T3 & _). set (v := Inv.chunk_block c) in *. pose proof HW as (AH & HT & _).
  destruct (LB_cases AI ACCT UNIV W aw LB m mo v HW HLB) as [(b & Vb & Ev)|[(b & Hb & Ev)|(b & Vb & Ev)]].
  2:{ exfalso. pose proof (T1 b Hb) as WIN. destruct (LB_twin_facts AI ACCT UNIV W aw LB m mo b HW Hb) as (_ & _ & P1).
      apply (APART _ WIN ltac:(right; unfold K_GHOST, K_TWINz; cbn; lia) (fst v)).
      - unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. rewrite Ev. unfold twin_iv. cbn [fst snd]. lia.
      - unfold in_iv. lia. }
  2:{ exfalso. destruct (T3 b Vb) as [_ WIN]. destruct (LB_fsh_facts AI ACCT UNIV AI_fake W aw LB m mo b HW Vb) as (_ & _ & P1 & _).
      apply (APART _ WIN ltac:(right; unfold K_GHOST, K_FTWINz; cbn; lia) (fst v)).
      - unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. rewrite Ev. unfold fsh_iv. cbn [fst snd]. lia.
      - unfold in_iv. lia. }
  destruct (kind_cases b) as [HH|HF].
  2:{ exfalso. destruct (T3 b (conj Vb HF)) as [WIN _].
      destruct (blk_facts AI AI_fake _ _ _ _ _ b AH (proj1 Vb)) as (NP & _).
      destruct (AI_fake _ _ _ _ _ b AH (proj1 Vb) HF) as (_ & _ & _ & _ & N64 & _).
      apply (APART _ WIN ltac:(right; unfold K_GHOST, K_FRAMEz; cbn; lia) (ab_addr b)).
      - unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. lia.
      - rewrite Ev. unfold in_iv, user_iv. cbn [fst snd]. rewrite (usz_fake b HF). lia. }
  assert (NT : ~ In b (w_T W)).
  { intros HbT. pose proof (T1 b HbT) as WIN. apply (SEAL _ WIN eq_refl c Hc). cbn [w_lo]. rewrite ShLaw.TwinB.shadZ_shad.
    replace (fst c) with (fst v) by reflexivity. rewrite Ev. reflexivity. }
  destruct HH as [p KP]. exists p.
  assert (EB : HB p (fst v) (snd v) = b).
  { rewrite Ev. unfold user_iv. cbn [fst snd]. rewrite (usz_heap b (ex_intro _ p KP)). destruct b as [kd ad sz]. cbn [ab_kind ab_addr ab_size] in *. subst kd. reflexivity. }
  split; [rewrite EB; exact (proj1 Vb)|].
  pose proof (CtrPat.TwinB.aw_pat_in AI ACCT UNIV AI_fake W aw LB m mo b HW Vb (ex_intro _ p KP) NT) as PAT.
  rewrite <- EB in PAT. cbn [ab_addr ab_size] in PAT. exact PAT.
Qed.

Theorem pkbody_sound : forall pc, to_Z pc = SYM -> contract_sound bsegs OPS MP PB (PkBodyAC.TwinB.PkBodyAC.pkbody_c bsegs pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc PkBodyAC.TwinB.PkBodyAC.pkbody_c] in Happ, Hspc. rewrite PkBodyAC.TwinB.PkBodyAC.pkbody_apply_eq in Happ. unfold PkBodyAC.TwinB.PkBodyAC.pkbody_apply_spec in Happ.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:PRE; [|discriminate Happ].
  destruct (CtrA.sym_offset (s_regs st) (getr st X10)) as [[kS OFF]|] eqn:DOFF; [|discriminate Happ].
  destruct (IMap.find kS (s_regs st)) as [rS|] eqn:HkS; [|discriminate Happ].
  destruct (CtrA.win_lookup wnl kS) as [[lenS kdS]|] eqn:WLS; [|discriminate Happ].
  cbv zeta in Happ.
  match type of Happ with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate Happ] end.
  injection Happ as <-.
  apply andb_prop in C2 as [C2 SRC]. apply andb_prop in C2 as [C2 PATS]. apply andb_prop in C2 as [C2 LE3]. apply andb_prop in C2 as [C2 LE2]. apply andb_prop in C2 as [C2 LE1].
  apply andb_prop in C2 as [C2 NOC]. apply andb_prop in C2 as [C2 Ws]. apply andb_prop in C2 as [C2 LOs]. apply andb_prop in C2 as [C2 BGs].
  apply andb_prop in C2 as [KS0 KDS]. apply negb_true_iff in KS0. apply Uint63.eqb_correct in LOs. apply ValP.weqb_eq in KDS. subst kdS.
  assert (BG : rg_bg rS = BGNone) by (destruct (rg_bg rS); try discriminate BGs; reflexivity).
  assert (HPC : to_Z (s_pc st) = SYM) by (rewrite Hspc; exact Hpc).
  pose proof (so_facts _ _ _ _ _ _ HS) as Pfacts.
  pose proof atop_range as ATR. pose proof two64_eq as T64.
  set (m := ms_mem ms) in *.
  assert (ENZ : exists nZ, nZ = bv_unsigned (den E (getr st X12))) by (eexists; reflexivity). destruct ENZ as [nZ ENZ].
  destruct (Z.eq_dec nZ 0) as [NZ0|NZ1].
  {
    apply (mc0_core AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
             MP NMAXt ACCT_rng ACCT_rng_aimg ACCT_silent SYM FRM0 FR0 WALK0 st K E ms mo r hargs wnl st1 HS HMP HPC PRE); [| exact HK].
    change (AP.getr (ms_regs ms) 12) with (AP.getr (ms_regs ms) (reg_of_r5 X12)). rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X12).
    apply bv_eq. rewrite Z_to_bv_unsigned, <- ENZ, NZ0. reflexivity. }

  destruct (CtrPre.TwinB.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L0 & RNG0 & sta0 & LBa0 & aw0 & Ems & AH0 & AC0 & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF0).

  pose proof (so_reg _ _ _ _ _ _ HS kS rS HkS) as ROs.
  set (BS := bv_unsigned (ev E kS)) in *. set (offZ := bv_unsigned (den E OFF)) in *.
  pose proof (bv_unsigned_in_range 64 (den E OFF)) as OR. rewrite bv_modulus_64 in OR. fold offZ in OR.
  pose proof (bv_unsigned_in_range 64 (den E (getr st X12))) as NR. rewrite bv_modulus_64, <- ENZ in NR.
  apply (HeapCtr.TwinB.known_leu_sound E _ _ _ Pfacts) in LE1. apply (HeapCtr.TwinB.known_leu_sound E _ _ _ Pfacts) in LE2. apply (HeapCtr.TwinB.known_leu_sound E _ _ _ Pfacts) in LE3.
  fold offZ in LE1. change (bv_unsigned (den E (rg_hi rS))) with (hiZ E rS) in LE1, LE3.
  rewrite <- ENZ in LE2. rewrite ValP.den_sv_alu in LE2. cbn [alu64 alu] in LE2. rewrite bv_sub_unsigned in LE2. fold offZ in LE2.
  change (bv_unsigned (den E (rg_hi rS))) with (hiZ E rS) in LE2.
  pose proof (ro_range _ _ _ _ _ _ ROs KS0) as [RLs RHs]. fold BS in RLs, RHs.
  assert (LZs : loZ rS = 0) by (unfold loZ; rewrite LOs; reflexivity). rewrite LZs in RLs.
  pose proof (bv_unsigned_in_range 64 (den E (rg_hi rS))) as HSR. rewrite bv_modulus_64 in HSR. change (bv_unsigned (den E (rg_hi rS))) with (hiZ E rS) in HSR.
  assert (SUM : offZ + nZ <= hiZ E rS).
  { unfold bv_wrap in LE2. rewrite bv_modulus_64 in LE2. rewrite Z.mod_small in LE2; unfold two64 in *; lia. }
  assert (DA : bv_unsigned (den E (getr st X10)) = BS + offZ).
  { rewrite (MemcpyCtr.TwinB.sym_offset_sound E (s_regs st) _ kS OFF DOFF). rewrite bv_add_unsigned. fold BS offZ. apply bv_wrap_small. rewrite bv_modulus_64. unfold two64 in *. lia. }
  set (S := bv_unsigned (den E (getr st X11))) in *.

  assert (SRCX : (S + nZ <= BS + offZ \/ BS + offZ + nZ <= S) /\
                 (forall L RNG sta LBa aw, CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> AHEAP AI L RNG sta LBa m ->
                    ACCT aw L RNG sta LBa mo -> srcF RNG m (bv_unsigned (AP.getr (ms_regs ms) 2)) S nZ)).
  { apply orb_prop in SRC as [SRCR|SRCB].
    -
      unfold PkBodyAC.TwinB.PkBodyAC.lit_src_ok in SRCR.
      destruct (getr st X11) as [|ks os| | | | | | | | |] eqn:G11; try discriminate SRCR.
      destruct (getr st X12) as [nw| | | | | | | | | |] eqn:G12; try discriminate SRCR.
      apply andb_prop in SRCR as [SRCR RIN]. apply andb_prop in SRCR as [SRCR KK]. apply andb_prop in SRCR as [SRCR NMX]. apply andb_prop in SRCR as [WTN N1].
      apply negb_true_iff in WTN. apply negb_true_iff in KK. apply Uint63.eqb_false_spec in KK. apply Uint63.leb_spec in N1. apply Uint63.leb_spec in NMX.
      change (to_Z 1%uint63) with 1 in N1. change (to_Z RangeC.TwinB.RangeC.NMAX) with 4096 in NMX.
      assert (ENW : nZ = to_Z (wl nw)) by (rewrite ENZ; cbn [den]; rewrite wbv_unsigned; unfold w2Z; rewrite WTN; lia).
      destruct (range_in_inv _ _ _ _ _ _ RIN) as (rs & cs & FSs & IRS & RCS & KS0s & _).
      destruct (in_region_s_sound E _ rs os (wl nw) Pfacts IRS ltac:(lia)) as (S1 & S2).
      destruct (range_class_facts_ev AI ACCT UNIV Cw OPS AI_fake Cw_sub_ghost OPS_holds_ssh ACCT_rng ACCT_rng_stk_sh ACCT_frng W_PAT E st ms mo r hargs wnl
                  L0 RNG0 sta0 LBa0 aw0 ks os (wl nw) false cs HS CF0 AH0 AC0 BOT LO SPT RCS ltac:(lia)) as (DEN1 & _).
      assert (ES : S = bv_unsigned (ev E ks) + w2Zs os) by (unfold S; exact DEN1).
      split.
      + pose proof (so_disj _ _ _ _ _ _ HS kS rS ks rs HkS FSs ltac:(intros Q; apply KK; symmetry; exact Q) KS0 KS0s (or_introl Ws)) as NO.
        destruct (Z_le_gt_dec (S + nZ) (BS + offZ)) as [Q1|Q1]; [left; exact Q1|]. destruct (Z_le_gt_dec (BS + offZ + nZ) S) as [Q2|Q2]; [right; exact Q2|].
        exfalso. apply (NO (Z.max (BS + offZ) S)). rewrite LZs. fold BS. rewrite ES in *. lia.
      + intros L RNG sta LBa aw CF AH AC.
        destruct (range_class_facts_ev AI ACCT UNIV Cw OPS AI_fake Cw_sub_ghost OPS_holds_ssh ACCT_rng ACCT_rng_stk_sh ACCT_frng W_PAT E st ms mo r hargs wnl
                    L RNG sta LBa aw ks os (wl nw) false cs HS CF AH AC BOT LO SPT RCS ltac:(lia)) as (_ & LOW1 & HI1 & POS1 & SRCBY & _ & APB1 & UNP1 & RNG1 & HULL).
        rewrite ES, ENW.
        split; [exact HI1|]. split; [exact POS1|]. split; [exact SRCBY|]. split; [exact APB1|]. split; [exact UNP1|]. split; [exact RNG1| exact HULL].
    -
      pose proof SRCB as SRCB'. unfold PkBody.body_src_ok in SRCB'.
      destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate SRCB'].
      apply andb_prop in SRCB' as [MD _]. apply Uint63.eqb_correct in MD. subst mdi.
      destruct (the_op_full st 3%uint63 aw ws ca TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN').
      split.
      +
        pose proof (ops_hold_in OPS _ _ _ _ o (so_ops _ _ _ _ _ _ HS) (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
        destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
        rewrite (DECf E) in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC. apply CW3 in HC.
        pose proof (aw_ceiling_small bsegs IMGX AWx mo) as CEIL. unfold two62Z in CEIL.
        destruct (PkBodySrc.TwinB.PkBodySrc.body_src_facts bsegs E st aw ws ca LB _ m Pfacts TO SRCB HC
                    ltac:(intros b Hb; destruct (aw_blocks_ok bsegs IMGX AWx _ LB _ m mo b HA Hb) as (B1 & B2 & B3 & _); lia))
          as [Z0|(NZ & g & ls & c & P & O & Wk & GH1 & Hc & CLO & CHI)]; [rewrite <- ENZ in Z0; contradiction|].
        rewrite <- ENZ in CHI. fold S in CLO, CHI.
        assert (INLB : In (chunk_block c) LB) by (apply (proj1 O); unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc).
        destruct (aw_blocks_ok bsegs IMGX AWx _ LB _ m mo (chunk_block c) HA INLB) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
        unfold chunk_block in Bc1, Bc2, Bc3, Bc5. cbn [fst snd] in Bc1, Bc2, Bc3, Bc5.
        apply (CopyFX.CopyFX.sep_of_pointwise S (BS + offZ) nZ ltac:(lia)). intros j j' Hj Hj' EQ.
        assert (INB : in_iv (fst c, CHUNK_HDR + snd c) (S + j)) by (unfold in_iv, chunk_lo, chunk_hi, CHUNK_HDR in *; cbn [fst snd]; lia).
        assert (FP : Exists (fun q => fst q <= S + j < snd q) (St.op_fp OPS (op_id o) (map (den E) (op_args o)))).
        { rewrite OID, (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ _ _ _ _ (S + j) (DECf E))).
          split; [unfold two64; lia|]. split; [exact (Bc5 _ INB)|].
          intros IW. apply in_ws_map_iff in IW as (w & Hw & INW).
          pose proof (proj1 (Forall_forall _ _) WF (wden E w) (in_map _ _ _ Hw)) as (_ & _ & _ & [[KSk CEk]|OTHERk]).
          - unfold in_iv, w_iv in INW. unfold in_iv in INB. cbn [fst snd] in INW, INB. lia.
          - assert (NK : w_kind (wden E w) <> K_STACK) by (destruct OTHERk as [[-> _]|[KS _]]; [discriminate| unfold K_SUB, K_STACK in *; lia]).
            destruct (proj1 (Forall_forall _ _) Wk (wden E w) (in_map _ _ _ Hw) NK) as [[_ DISJ]|[_ ET]].
            + apply (DISJ (chunk_block c) ltac:(unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc) (S + j) INW). exact INB.
            + exact (PK.safe_zone g ls LB (map (wden E) ws) P O S nZ (S + j) ltac:(lia) (ex_intro _ c (conj Hc (conj CLO CHI))) ltac:(lia) (wden E w) (in_map _ _ _ Hw) ET INW). }
        destruct (proj1 (Forall_forall _ _) (so_apart _ _ _ _ _ _ HS) o (op_in_In st o OPS1) (S + j) FP) as [NB _].
        apply NB. exists kS, rS. split; [exact HkS|]. split; [exact KS0|]. fold BS. rewrite LZs. rewrite EQ. lia.
      +
        intros L RNG sta LBa aw' CF AH AC.
        pose proof CF as (LB & ks & offs & rss & ksp & nn & mdw & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc0 & Eh & Tnw & Nn & Ln & N255
                          & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
        pose proof (ReadPost.TwinB.count_one_args HEAP_ID (s_ops st) o hargs (op_in_In st o OPS1) OID Hc0 Hf) as EA.
        pose proof (decode_hargs E mdw A nw rest nn Tnw Nn Ln) as D1. rewrite <- Eh, <- EA, (DECf E) in D1. injection D1 as M1 _ W1 C1.
        change (nn + (nn + (nn + 0)))%nat with (3 * nn)%nat in C1.
        rewrite <- M1, <- C1, <- W1 in HC. rewrite <- W1 in TI. change (to_Z 3%uint63) with 3 in HC. apply CW3 in HC.
        destruct ARW as [HW WMS]. destruct WOF as (_ & _ & _ & WLBa).
        destruct (PkBodySrc.TwinB.PkBodySrc.body_src_facts bsegs E st aw ws ca LB _ m Pfacts TO SRCB HC (fun b Hb => LB_bound W aw' LB m mo b HW Hb))
          as [Z0|(NZ & g & ls & c & P & O & Wk & GH1 & Hc & CLO & CHI)]; [rewrite <- ENZ in Z0; contradiction|].
        rewrite <- ENZ in CHI. fold S in CLO, CHI.
        assert (OWNc : In (chunk_block c) (PK.owned g)) by (unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc).
        destruct (chunk_block_pat W aw' LB m mo (map (wden E) ws) (z_chunks (PK.k_zone g)) c HW TI (proj1 GH1) Hc (proj1 O _ OWNc)) as (p & HIN & PAT).
        { intros w0 Hw0 KD0 a Ha0 Hb0.
          destruct (proj1 (Forall_forall _ _) Wk w0 Hw0 ltac:(unfold HeapOp.K_STACK, HeapOp.K_BLOCK, K_GHOST in *; lia)) as [[_ DJ]|[_ ET]].
          - exact (DJ _ OWNc a Ha0 Hb0).
          - destruct ET as (K6 & _). unfold PK.K_ETOP, HeapOp.K_BLOCK, K_GHOST in *. lia. }
        { exact (PK.owned_pos g ls P _ OWNc). }
        rewrite WLBa in HIN. unfold chunk_block in HIN, PAT. cbn [fst snd] in HIN, PAT.
        destruct (block_range_facts AI L RNG sta LBa m p (fst c) (CHUNK_HDR + snd c) S nZ AH HIN PAT
                    ltac:(unfold chunk_lo, CHUNK_HDR in *; lia) ltac:(unfold chunk_hi, CHUNK_HDR in *; lia) ltac:(lia))
          as ((src & SRCC) & APB1 & UNP1 & LOWs & HIs & RNGS & RLOs & RHIs & HULLs & WRHs & RNGHs).
        split; [lia|]. split; [left; exact HIs|].
        split. { exists src. destruct SRCC as [[WFs BYs] _]. cbn [cells_wf cell_wf] in WFs. cbn [cells_bytes cbytes] in BYs. rewrite app_nil_r in BYs.
                 split; [exact (proj1 WFs)| exact BYs]. }
        split; [exact APB1|]. split; [exact UNP1|]. split; [exact RNGS|]. exists RLOs, RHIs. split; [exact HULLs|]. split; [exact WRHs| exact RNGHs]. }
  destruct SRCX as [SEP SRCF].
  apply (acopy_cps AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           Cw_sub_ghost W_PAT MP NMAXt ACCT_rng ACCT_rng_aimg ACCT_silent SYM WALK
           st K E ms mo r hargs wnl st1 kS rS lenS (wlit 1%uint63) offZ S nZ HS HMP HPC PRE DA ltac:(lia) HkS BG LOs Ws WLS ltac:(vm_compute; reflexivity) PATS
           ltac:(lia) SUM LE3).
  - intros g0 gr c0 i Hf. unfold PkBodyAC.TwinB.PkBodyAC.no_cells in NOC. destruct (rg_cells rS); [discriminate Hf| discriminate NOC].
  - reflexivity.
  - symmetry. exact ENZ.
  - exact SEP.
  - exact SRCF.
  - intros E' ms' mo' HX HMP' HS' _. exact (HK _ (or_introl eq_refl) E' ms' mo' HX HMP' HS').
Qed.
End Sound.
End PkBodyA.
End TwinB.
