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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_asan_memcpy.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import RtCells.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA GlueA CtrPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import UnreggSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import StackSh RangeC RangeFX MemcpyC MemsetPre RangePre LowImg StrRegC StrReg GshC GshImg.
Import CtrFX ActrA MemcpyC.
Module IMC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.I_memcpy.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require KnownA.
Unset Nia Cache. Unset Nra Cache.

Definition MEMCPY_SYM : Z := 0x5da90.
Definition ASAN_MEMCPY_SYM : Z := 0x5cc04.

Definition memcpy_walk_stmt {rc : runConstT} (SYM : Z) : Prop :=
  forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (src junk : list byte) (RLO1 RHI1 RLO2 RHI2 : Z),
  ALib.Mem.mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2240)%Z -> (Shadow.KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  ALib.Mem.bytes_at asegs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
  ALib.Step.rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned sp - 2240 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  Shadow.app_blk (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) ->
  Shadow.app_blk (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  Shadow.unpoisoned m (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) ->
  Shadow.unpoisoned m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  (bv_unsigned a2 <= 2^40)%Z ->
  (RLO1 <= bv_unsigned a1 /\ bv_unsigned a1 + bv_unsigned a2 <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= Shadow.KEND)%Z ->
  (RLO2 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= Shadow.KEND)%Z ->
  ALib.Mem.wr_at asegs m (shad RLO1) (shad RHI1 - shad RLO1) -> ALib.Mem.wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (bv_unsigned a1) (bv_unsigned a2) -> rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  rng RNG (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  evtF asegs RNG (IMC.memcpy_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SYM) fc None m (seg_rom asegs)).

Lemma memcpy_walk_i {rc : runConstT} : memcpy_walk_stmt MEMCPY_SYM.
Proof. exact IMC.memcpy_i_spec. Qed.

Definition srcF {rc : runConstT} (RNG : footprint) (m : amem) (sp A1 len : Z) : Prop :=
  A1 + len + 8 <= 2 ^ 47 /\ (A1 + len <= ATOP \/ sp <= A1)
  /\ (exists src, length src = Z.to_nat len /\ ALib.Mem.bytes_at asegs m A1 src)
  /\ Shadow.app_blk A1 (A1 + len) /\ Shadow.unpoisoned m A1 (A1 + len) /\ rng RNG A1 len
  /\ (exists RLO1 RHI1, (RLO1 <= A1 /\ A1 + len <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= Shadow.KEND)
        /\ ALib.Mem.wr_at asegs m (shad RLO1) (shad RHI1 - shad RLO1) /\ rng RNG (shad RLO1) (shad RHI1 - shad RLO1)).

Lemma bytes_at_nil {rc : runConstT} : forall (m : amem) A, 0 <= A <= 2 ^ 64 -> ALib.Mem.bytes_at asegs m A [].
Proof. intros m A H. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi. lia. Qed.

Lemma srcF_zero {rc : runConstT} : forall RNG m sp A n, srcF RNG m sp A n -> 0 <= n -> 0 <= A -> srcF RNG m sp A 0.
Proof.
  intros RNG m sp A n (HI & POS & _ & APB & UNP & RG & (RLO & RHI & HULL & WR & RGH)) Hn HA.
  split; [lia|]. split; [destruct POS as [P|P]; [left; lia| right; exact P]|].
  split; [exists []; split; [reflexivity| apply bytes_at_nil; lia]|].
  split; [apply (Shadow.app_blk_sub _ _ _ _ APB); lia|].
  split; [apply (Shadow.unpoisoned_sub _ _ _ _ _ UNP); lia|].
  split; [apply (rng_sub _ _ _ _ _ RG); lia|].
  exists RLO, RHI. split; [lia| split; assumption].
Qed.

Lemma range_facts_zero {rc : runConstT} : forall RNG m sp A n, range_facts RNG m sp A n true -> 0 <= n -> range_facts RNG m sp A 0 true.
Proof.
  intros RNG m sp A n (LOW & HI & POS & _ & _ & APB & UNP & RG & (RLO & RHI & HULL & WR & RGH)) Hn. unfold AIMG_HI in LOW.
  split; [exact LOW|]. split; [lia|]. split; [destruct POS as [P|P]; [left; lia| right; exact P]|].
  split; [exists []; split; [reflexivity| apply bytes_at_nil; lia]|].
  split. { intros _. apply (UnreggLib.mapped_chunk asegs m 0 A); [lia| cbn; lia| intros i Hi; cbn in Hi; lia]. }
  split; [apply (Shadow.app_blk_sub _ _ _ _ APB); lia|].
  split; [apply (Shadow.unpoisoned_sub _ _ _ _ _ UNP); lia|].
  split; [apply (rng_sub _ _ _ _ _ RG); lia|].
  exists RLO, RHI. split; [lia| split; assumption].
Qed.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Hypothesis OPS_holds_ssh : forall m mo, op_holds OPS RangeC.SSH_ID [] m mo -> ssh_holds m.
Hypothesis OPS_holds_zro : forall m mo, op_holds OPS RangeC.ZRO_ID [] m mo -> zro_holds m.
Hypothesis OPS_holds_gsh : forall m mo, op_holds OPS GshC.GSH_ID [] m mo -> gsh_holds GshC.GSH_TAB_ASAN m.
Hypothesis OPS_holds_shmap : forall m mo, op_holds OPS GshC.SHMAP_ID [] m mo -> UnreggPre.shmap_holds m.
Hypothesis OPS_holds_zarg : forall az m mo, op_holds OPS StrRegC.ZARG_ID [az] m mo -> zarg_holds az m.
Variable OTHER : Model -> Model -> Prop.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Variable SYM : Z.
Hypothesis WALK : memcpy_walk_stmt SYM.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP).
Hypothesis ACCT_frng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> FRNG AI AI_fake L RNG.
Hypothesis W_PAT : w_pat_ev_stmt AI ACCT UNIV Cw OPS.
Hypothesis ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc4000.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).

Lemma amemcpy_apply_shape : forall st sts, amemcpy_apply asegs st = Some sts ->
  exists r hargs wnl st1 kd od srcv sofs n lenc,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ getr st X10 = VP kd od /\ getr st X11 = srcv /\ getr st X12 = VL n
    /\ wt n = false /\ 0 <= to_Z (wl n) <= 4096
    /\ 1 <= to_Z lenc <= 4096 /\ (to_Z (wl n) = 0 \/ lenc = wl n)
    /\ range_in asegs st wnl kd od lenc true = true /\ src_ok asegs st wnl srcv kd od lenc = Some sofs
    /\ copy_post asegs kd od srcv sofs (wl n) (setpc (setr (clobber st1) X10 (VP kd od)) r) = Some sts.
Proof.
  intros st sts H. unfold amemcpy_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (getr st X10) as [|kd od| | | | | | | | |] eqn:G10; try discriminate H.
  destruct (getr st X12) as [n| | | | | | | | | |] eqn:G12; try discriminate H.
  cbv zeta in H.
  set (lenc := if PrimInt63.eqb (wl n) 0%uint63 then 1%uint63 else wl n) in *.
  destruct (src_ok asegs st wnl (getr st X11) kd od lenc) as [sofs|] eqn:SRC; [|discriminate H].
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate H] end.
  repeat match type of CND with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in CND as [CND X] end.
  apply negb_true_iff in CND; apply Uint63.leb_spec in Q0; change (to_Z RangeC.NMAX) with 4096 in Q0.
  pose proof (to_Z_bounded (wl n)) as NB.
  assert (LC : 1 <= to_Z lenc <= 4096 /\ (to_Z (wl n) = 0 \/ lenc = wl n)).
  { unfold lenc. destruct (PrimInt63.eqb (wl n) 0%uint63) eqn:Z0.
    - apply Uint63.eqb_correct in Z0. rewrite Z0. change (to_Z 1%uint63) with 1. change (to_Z 0%uint63) with 0. split; [lia| left; reflexivity].
    - apply Uint63.eqb_false_spec in Z0. split; [| right; reflexivity]. split; [| lia].
      assert (to_Z (wl n) <> 0) by (intros QZ; apply Z0; apply to_Z_inj; exact QZ). lia. }
  destruct LC as [LC1 LC2].
  exists r, hargs, wnl, st1, kd, od, (getr st X11), sofs, n, lenc. repeat split; try reflexivity; try eassumption; lia.
Qed.

Lemma in_region_s_sound : forall E fs r o len, facts_hold E fs -> in_region_s fs r o len = true -> 0 <= to_Z len <= 2 ^ 32 ->
  loZ r <= w2Zs o /\ w2Zs o + to_Z len <= hiZ E r.
Proof.
  intros E fs r o len Hfs H Hl. unfold in_region_s in H. apply orb_prop in H as [H|H].
  - destruct (RangeFX.in_region_sound E r o len H Hl) as (D1 & D2 & _). split; assumption.
  - repeat match type of H with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in H as [H X] end.
    apply Uint63.eqb_correct in H. apply negb_true_iff in Q2, Q1.
    pose proof (KnownA.KnownA.known_leu_sound E _ _ _ Hfs Q) as KL. cbn [den] in KL. rewrite wbv_unsigned, wadd_ok, wlit_ok in KL.
    pose proof (w2Z_range o) as ROD.
    assert (ODS : w2Z o < two63) by (unfold w2Z; rewrite Q2; pose proof (wl_range o); unfold two63 in *; lia).
    rewrite Z.mod_small in KL by (unfold two63, two64 in *; lia).
    assert (ES : w2Zs o = w2Z o) by (rewrite ValP.w2Zs_eq, Q2; lia).
    unfold loZ. rewrite H. change (keyZ 0%uint63) with 0. unfold hiZ. rewrite ES. lia.
Qed.

Lemma range_in_inv : forall st wnl k o len needw, range_in asegs st wnl k o len needw = true ->
  exists r c, IMap.find k (s_regs st) = Some r /\ in_region_s (s_facts st) r o len = true /\ RangeC.range_class asegs st wnl k o len needw = Some c
    /\ PrimInt63.eqb k 0%uint63 = false /\ (needw = true -> rg_w r = true).
Proof.
  intros st wnl k o len needw H. unfold range_in in H. destruct (IMap.find k (s_regs st)) as [r|] eqn:F; [|discriminate H].
  apply andb_prop in H as [IR H]. destruct (RangeC.range_class asegs st wnl k o len needw) as [c|] eqn:RC; [|discriminate H].
  exists r, c. split; [reflexivity|]. split; [exact IR|]. split; [reflexivity|].
  unfold RangeC.range_class in RC. rewrite F in RC.
  destruct (negb (PrimInt63.eqb k 0%uint63) && implb needw (rg_w r))%bool eqn:C0; [|discriminate RC].
  apply andb_prop in C0 as [K0 NW]. apply negb_true_iff in K0. split; [exact K0|]. intros ->. exact NW.
Qed.

Definition amemcpy_leaf : Prop :=
  forall st sts (K : TSet) E ms mo r hargs wnl st1 kd od srcv sofs n (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) (src : list byte),
  st_ok asegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' sts -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok asegs OPS E' st' ms' mo' ->
               realizes asegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) -> getr st X10 = VP kd od -> getr st X11 = srcv -> getr st X12 = VL n ->
  wt n = false -> 0 <= to_Z (wl n) <= 4096 ->
  copy_post asegs kd od srcv sofs (wl n) (setpc (setr (clobber st1) X10 (VP kd od)) r) = Some sts ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ALib.Mem.mem_inv asegs (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  let A0 := bv_unsigned (ev E kd) + w2Zs od in let A1 := bv_unsigned (den E srcv) in
  AIMG_HI <= A0 -> A0 + to_Z (wl n) + 8 <= 2 ^ 47 -> (A0 + to_Z (wl n) <= ATOP \/ bv_unsigned (AP.getr R 2) <= A0) ->
  A1 + to_Z (wl n) + 8 <= 2 ^ 47 -> (A1 + to_Z (wl n) <= ATOP \/ bv_unsigned (AP.getr R 2) <= A1) ->
  (A1 + to_Z (wl n) <= A0 \/ A0 + to_Z (wl n) <= A1) ->
  bv_unsigned (AP.getr R 10) = A0 -> bv_unsigned (AP.getr R 11) = A1 -> bv_unsigned (AP.getr R 12) = to_Z (wl n) ->
  length src = Z.to_nat (to_Z (wl n)) ->
  forall ms' mo',
  IMC.memcpy_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) src (CtrPre.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes asegs (mkCfg ms' mo') K.

Theorem amemcpy_sound_of_leaf : amemcpy_leaf ->
  forall pc, to_Z pc = SYM -> contract_sound asegs OPS MP PB (amemcpy_c asegs pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc amemcpy_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = SYM) by (rewrite Hspc; exact Hpc).
  destruct (amemcpy_apply_shape st sts Happ) as (r & hargs & wnl & st1 & kd & od & srcv & sofs & n & lenc & PRE & G10 & G11 & G12 & WTN & NR & NRc & LCE & RID & SRCOK & CPY).
  destruct (CtrPre.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  set (R := ms_regs ms) in *. set (len := to_Z (wl n)) in *. set (lc := to_Z lenc) in *.
  destruct (range_in_inv _ _ _ _ _ _ RID) as (rd & cd & FD & IRD & RCD & KD0 & WD). specialize (WD eq_refl).

  destruct (range_class_facts_ev AI ACCT UNIV Cw OPS AI_fake Cw_sub_ghost OPS_holds_ssh ACCT_rng ACCT_rng_stk_sh ACCT_frng W_PAT E st ms mo r hargs wnl L RNG sta LBa aw
              kd od lenc true cd HS CF AH AC BOT LO SPT RCD NRc) as (DEN0 & RF0c).
  fold lc in RF0c.
  set (A0 := bv_unsigned (ev E kd) + w2Zs od) in *. set (A1 := bv_unsigned (den E srcv)) in *.
  pose proof atop_range as ATR.
  assert (LOW0c : AIMG_HI <= A0) by exact (proj1 RF0c).

  assert (SRCFc : srcF RNG (ms_mem ms) (bv_unsigned (AP.getr R 2)) A1 lc /\ (A1 + lc <= A0 \/ A0 + lc <= A1)).
  { unfold src_ok in SRCOK. destruct srcv as [a|ks os| | | | | | | | |]; try discriminate SRCOK.
    -
      destruct (RangeC.lit_low st a lenc) eqn:LL.
      2:{
        cbn [orb] in SRCOK. destruct (GshC.lit_gsh GshC.CFG_ASAN st a lenc) eqn:LG; [|discriminate SRCOK].
        destruct (lit_gsh_inv st a lenc LG) as (WTG & LAG & HAG & QUG & FGG & FMG). fold lc in HAG, QUG.
        assert (EAG : A1 = to_Z (wl a)).
        { unfold A1. cbn [den]. rewrite wbv_unsigned. unfold w2Z. rewrite WTG. lia. }
        pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.find_op_In _ _ _ FGG)) as HOG. cbn [op_id op_args map] in HOG.
        pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.find_op_In _ _ _ FMG)) as HOM. cbn [op_id op_args map] in HOM.
        destruct (gsh_range_facts_ok RNG (ms_mem ms) A1 lc (OPS_holds_gsh _ _ HOG) (OPS_holds_shmap _ _ HOM) (ACCT_rng_aimg _ _ _ _ _ _ AC) (ACCT_rng_aimg_sh _ _ _ _ _ _ AC)
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite EAG; exact QUG)) as (SRCB & APB1 & UNP1 & RNG1 & HULL).
        split; [| left; unfold AIMG_HI in LOW0c; lia].
        split; [lia|]. split; [left; lia|]. split; [exact SRCB|]. split; [exact APB1|]. split; [exact UNP1|]. split; [exact RNG1| exact HULL]. }
      cbn [orb] in SRCOK.
      destruct (lit_low_inv st a lenc LL ltac:(lia)) as (WTA & LA & HA & FZ). fold lc in HA.
      assert (EA : A1 = to_Z (wl a)).
      { unfold A1. cbn [den]. rewrite wbv_unsigned. unfold w2Z. rewrite WTA. lia. }
      pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.find_op_In _ _ _ FZ)) as HO. cbn [op_id op_args map] in HO.
      pose proof (OPS_holds_zro _ _ HO) as ZRO.
      destruct (low_range_facts_ok RNG (ms_mem ms) A1 lc ZRO (ACCT_rng_aimg _ _ _ _ _ _ AC) (ACCT_rng_aimg_sh _ _ _ _ _ _ AC) ltac:(lia) ltac:(lia) ltac:(lia))
        as (_ & _ & SRCB & APB1 & UNP1 & RNG1 & HULL).
      split; [| left; unfold AIMG_HI in LOW0c; lia].
      split; [lia|]. split; [left; lia|]. split; [exact SRCB|]. split; [exact APB1|]. split; [exact UNP1|]. split; [exact RNG1| exact HULL].
    -
      match type of SRCOK with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate SRCOK] end. apply andb_prop in CND as [RIS DJ].
      apply orb_prop in RIS. destruct RIS as [RIS|ARG].
      2:{
        unfold StrRegC.arg_range in ARG. destruct (IMap.find ks (s_regs st)) as [rs|] eqn:FSs; [|discriminate ARG].
        repeat match type of ARG with (_ && _)%bool = true => let X := fresh "G" in apply andb_prop in ARG as [ARG X] end.
        apply negb_true_iff in G2, G1.
        assert (SRO : exists j js, StrRegC.str_reg_ok st wnl ks rs j js = true).
        { apply orb_prop in ARG. destruct ARG as [Q|Q]; [exists 1%uint63, 9%uint63| exists 3%uint63, 10%uint63]; exact Q. }
        destruct SRO as (j & js & SRO).
        destruct (str_reg_ok_shape st wnl ks rs j js SRO) as (az & _ & KS0 & _ & LOs & WS & _ & _ & _ & _ & _ & _ & _).
        pose proof (known_leu_sound_r_plain OPS E st ms mo _ _ HS G) as KL.        cbn [den] in KL. rewrite wbv_unsigned, wadd_ok, wlit_ok in KL.
        pose proof (w2Z_range os) as ROS.
        assert (ODS : w2Z os < two63) by (unfold w2Z; rewrite G2; pose proof (wl_range os); unfold two63 in *; lia).
        rewrite Z.mod_small in KL by (unfold two63, two64 in *; fold lc; lia). fold lc in KL.
        change (bv_unsigned (den E (rg_hi rs))) with (hiZ E rs) in KL.
        assert (ES : w2Zs os = w2Z os) by (rewrite ValP.w2Zs_eq, G2; lia).
        destruct (str_reg_facts AI ACCT UNIV Cw OPS OPS_holds_zarg ACCT_rng ACCT_rng_stk_sh E st ms mo r hargs wnl L RNG sta LBa aw ks rs j js (w2Z os) lc HS CF AC BOT LO SPT FSs SRO
                    ltac:(lia) ltac:(lia) KL) as (RLO1 & RHI1 & KE & BYT & SPA & APB1 & SPOS & UNP1 & HULL1 & WRH1 & RNG1 & RNGH1).
        fold R in SPA.
        assert (EA1 : A1 = bv_unsigned (ev E ks) + w2Z os).
        { unfold A1. rewrite ValP.den_VP, ES. apply Z.mod_small. pose proof (bv_unsigned_in_range _ (ev E ks)). unfold two64. lia. }
        rewrite <- EA1 in BYT, SPA, APB1, UNP1, HULL1, RNG1.
        split.
        { split; [lia|]. split; [right; exact SPA|].
          split; [eexists; split; [| exact BYT]; rewrite length_map, length_seq; reflexivity|].
          split; [exact APB1|]. split; [exact UNP1|]. split; [exact RNG1|]. exists RLO1, RHI1. split; [exact HULL1|]. split; [exact WRH1| exact RNGH1]. }
        assert (KK : kd <> ks) by (intros ->; rewrite FD in FSs; injection FSs as ->; rewrite WD in WS; discriminate WS).
        destruct (in_region_s_sound E _ rd od lenc (so_facts _ _ _ _ _ _ HS) IRD ltac:(lia)) as (D1 & D2). fold lc in D2.
        pose proof (so_disj _ _ _ _ _ _ HS kd rd ks rs FD FSs KK KD0 KS0 (or_introl WD)) as NO.
        assert (LZs : loZ rs = 0) by (unfold loZ; rewrite LOs; reflexivity).
        destruct (Z_le_gt_dec (A1 + lc) A0) as [Q1|Q1]; [left; exact Q1|]. destruct (Z_le_gt_dec (A0 + lc) A1) as [Q2|Q2]; [right; exact Q2|].
        exfalso. apply (NO (Z.max A0 A1)). rewrite LZs. unfold A0 in *. rewrite EA1 in *. lia. }
      destruct (range_in_inv _ _ _ _ _ _ RIS) as (rs & cs & FSs & IRS & RCS & KS0 & _).
      destruct (range_class_facts_ev AI ACCT UNIV Cw OPS AI_fake Cw_sub_ghost OPS_holds_ssh ACCT_rng ACCT_rng_stk_sh ACCT_frng W_PAT E st ms mo r hargs wnl L RNG sta LBa aw
                  ks os lenc false cs HS CF AH AC BOT LO SPT RCS NRc) as (DEN1 & LOW1 & HI1 & POS1 & SRCB & _ & APB1 & UNP1 & RNG1 & HULL).
      fold lc in HI1, POS1, SRCB, APB1, UNP1, RNG1, HULL. unfold A1. rewrite DEN1.
      split; [split; [exact HI1|]; split; [exact POS1|]; split; [exact SRCB|]; split; [exact APB1|]; split; [exact UNP1|]; split; [exact RNG1| exact HULL]|].
      unfold disjoint_ok in DJ. destruct (PrimInt63.eqb ks kd) eqn:KK.
      + apply Uint63.eqb_correct in KK. subst ks. apply orb_prop in DJ as [Q|Q]; apply Z.leb_le in Q; fold lc in Q; unfold A0; lia.
      + apply Uint63.eqb_false_spec in KK.
        destruct (in_region_s_sound E _ rd od lenc (so_facts _ _ _ _ _ _ HS) IRD ltac:(lia)) as (D1 & D2).
        destruct (in_region_s_sound E _ rs os lenc (so_facts _ _ _ _ _ _ HS) IRS ltac:(lia)) as (S1 & S2). fold lc in D2, S2.
        pose proof (so_disj _ _ _ _ _ _ HS kd rd ks rs FD FSs ltac:(intros Q; apply KK; symmetry; exact Q) KD0 KS0 (or_introl WD)) as NO.
        set (A1' := bv_unsigned (ev E ks) + w2Zs os) in *.
        destruct (Z_le_gt_dec (A1' + lc) A0) as [Q1|Q1]; [left; exact Q1|]. destruct (Z_le_gt_dec (A0 + lc) A1') as [Q2|Q2]; [right; exact Q2|].
        exfalso. apply (NO (Z.max A0 A1')). unfold A0, A1' in *. lia. }

  assert (A1pos : 0 <= A1) by (unfold A1; pose proof (bv_unsigned_in_range 64 (den E srcv)); lia).
  assert (FACTS : range_facts RNG (ms_mem ms) (bv_unsigned (AP.getr R 2)) A0 len true
                  /\ srcF RNG (ms_mem ms) (bv_unsigned (AP.getr R 2)) A1 len /\ (A1 + len <= A0 \/ A0 + len <= A1)).
  { destruct SRCFc as [SF DJc]. destruct LCE as [Z0| ->].
    - rewrite Z0. split; [exact (range_facts_zero _ _ _ _ _ RF0c ltac:(lia))|]. split; [exact (srcF_zero _ _ _ _ _ SF ltac:(lia) A1pos)| lia].
    - fold len in RF0c, SF, DJc. auto. }
  destruct FACTS as ((LOW0 & HI0 & POS0 & _ & DSTW & APB0 & UNP0 & RNG0 & RLO2 & RHI2 & HULL2 & WRH2 & RNGH2)
                     & (HI1 & POS1 & (src & LSRC & SRCB) & APB1 & UNP1 & RNG1 & (RLO1 & RHI1 & HULL1 & WRH1 & RNGH1)) & DISJ).
  destruct (DSTW eq_refl) as (junk & DST).

  assert (EA0 : bv_unsigned (AP.getr R (reg_of_r5 X10)) = A0).
  { unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X10), G10. exact DEN0. }
  assert (EA1 : bv_unsigned (AP.getr R (reg_of_r5 X11)) = A1).
  { unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X11), G11. reflexivity. }
  assert (EA2 : bv_unsigned (AP.getr R (reg_of_r5 X12)) = len).
  { unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X12), G12. cbn [den]. rewrite wbv_unsigned. unfold w2Z. rewrite WTN. unfold len. lia. }
  idtac "MC-1".
  assert (EA0' : bv_unsigned (AP.getr R 10) = A0) by exact EA0. assert (EA1' : bv_unsigned (AP.getr R 11) = A1) by exact EA1.
  assert (EA2' : bv_unsigned (AP.getr R 12) = len) by exact EA2.
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG.
  assert (EV : evtF asegs RNG
            (IMC.memcpy_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) src (CtrPre.sp_lo E st) (ms_mem ms))
            (MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                (ms_fregs ms) (Z_to_bv 64 SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom asegs))).
  { unfold artcells in RT. decompose [and] RT. clear RT.
    eapply (WALK RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_fregs ms) (ms_fcsr ms) (ms_mem ms)
              (CtrPre.sp_lo E st) src junk RLO1 RHI1 RLO2 RHI2).
    all: rewrite ?EA0', ?EA1', ?EA2'.
    all: try lazymatch goal with
         | |- ALib.Mem.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact ST
         | |- ALib.Mem.bytes_at _ _ _ _ => exact SRCB
         | |- length _ = _ => exact LSRC
         | |- ALib.Step.rw_cells _ _ _ [CB _ _] => exact DST
         | |- ALib.Step.rw_cells _ _ _ _ => assumption
         | |- Shadow.unpoisoned _ _ _ => first [exact UNP1 | exact UNP0]
         | |- Shadow.app_blk _ _ => first [exact APB1 | exact APB0]
         | |- ALib.Mem.wr_at _ _ _ _ => first [exact WRH1 | exact WRH2]
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ _ => first [exact RNGH1 | exact RNGH2 | exact RNG1 | exact RNG0 | exact RSTK]
         | |- _ <= _ /\ _ => first [exact HULL1 | exact HULL2]
         end.
    all: try (unfold Shadow.KHIGH in *; lia).
    all: try (destruct POS0 as [P|P]; [left; lia | right; exact P]).
    all: try (destruct POS1 as [P|P]; [left; lia | right; exact P]).
    all: match goal with |- ?G => idtac "REMW" G end. }
  rewrite Ems, HPC. apply (GlueA.realizes_to_mkRA asegs).
  eapply (implS_twfS_realizes_silent asegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ IMC.memcpy_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) src (CtrPre.sp_lo E st) (ms_mem ms) ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    exact (LEAF st sts K E ms mo r hargs wnl st1 kd od srcv sofs n L RNG sta LBa aw src HS HPB HK PRE G10 G11 G12 WTN NR CPY CP FS CF AH MI BOT LO SPT
             LOW0 HI0 POS0 HI1 POS1 DISJ EA0 EA1 EA2 LSRC ms' mo' HQ HMP' HMI' OTH ACP).
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
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB.
Import AMalloc_iface2.TwinB.
Import RtCells.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import UnreggSound.TwinB.
Import StackSh.TwinB RangeC.TwinB RangeFX.TwinB MemcpyC.TwinB MemsetPre.TwinB RangePre.TwinB LowImg.TwinB StrRegC.TwinB StrReg.TwinB GshC.TwinB GshImg.TwinB.
Import CtrFX ActrA MemcpyC.TwinB.MemcpyC.
Module IMC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.TwinB.I_memcpy.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Unset Nia Cache. Unset Nra Cache.

Definition MEMCPY_SYM : Z := 0x5e420.
Definition ASAN_MEMCPY_SYM : Z := 0x5d594.

Definition memcpy_walk_stmt {rc : runConstT} (SYM : Z) : Prop :=
  forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (src junk : list byte) (RLO1 RHI1 RLO2 RHI2 : Z),
  ALib.Mem.mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2240)%Z -> (Shadow.KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  ALib.Mem.bytes_at bsegs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
  ALib.Step.rw_cells bsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned sp - 2240 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  Shadow.app_blk (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) ->
  Shadow.app_blk (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  Shadow.unpoisoned m (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) ->
  Shadow.unpoisoned m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  (bv_unsigned a2 <= 2^40)%Z ->
  (RLO1 <= bv_unsigned a1 /\ bv_unsigned a1 + bv_unsigned a2 <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= Shadow.KEND)%Z ->
  (RLO2 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= Shadow.KEND)%Z ->
  ALib.Mem.wr_at bsegs m (shad RLO1) (shad RHI1 - shad RLO1) -> ALib.Mem.wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (bv_unsigned a1) (bv_unsigned a2) -> rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  rng RNG (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  evtF bsegs RNG (IMC.memcpy_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SYM) fc None m (seg_rom bsegs)).

Lemma memcpy_walk_i {rc : runConstT} : memcpy_walk_stmt MEMCPY_SYM.
Proof. exact IMC.memcpy_i_spec. Qed.

Definition srcF {rc : runConstT} (RNG : footprint) (m : amem) (sp A1 len : Z) : Prop :=
  A1 + len + 8 <= 2 ^ 47 /\ (A1 + len <= ATOP \/ sp <= A1)
  /\ (exists src, length src = Z.to_nat len /\ ALib.Mem.bytes_at bsegs m A1 src)
  /\ Shadow.app_blk A1 (A1 + len) /\ Shadow.unpoisoned m A1 (A1 + len) /\ rng RNG A1 len
  /\ (exists RLO1 RHI1, (RLO1 <= A1 /\ A1 + len <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= Shadow.KEND)
        /\ ALib.Mem.wr_at bsegs m (shad RLO1) (shad RHI1 - shad RLO1) /\ rng RNG (shad RLO1) (shad RHI1 - shad RLO1)).

Lemma bytes_at_nil {rc : runConstT} : forall (m : amem) A, 0 <= A <= 2 ^ 64 -> ALib.Mem.bytes_at bsegs m A [].
Proof. intros m A H. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi. lia. Qed.

Lemma srcF_zero {rc : runConstT} : forall RNG m sp A n, srcF RNG m sp A n -> 0 <= n -> 0 <= A -> srcF RNG m sp A 0.
Proof.
  intros RNG m sp A n (HI & POS & _ & APB & UNP & RG & (RLO & RHI & HULL & WR & RGH)) Hn HA.
  split; [lia|]. split; [destruct POS as [P|P]; [left; lia| right; exact P]|].
  split; [exists []; split; [reflexivity| apply bytes_at_nil; lia]|].
  split; [apply (Shadow.app_blk_sub _ _ _ _ APB); lia|].
  split; [apply (Shadow.unpoisoned_sub _ _ _ _ _ UNP); lia|].
  split; [apply (rng_sub _ _ _ _ _ RG); lia|].
  exists RLO, RHI. split; [lia| split; assumption].
Qed.

Lemma range_facts_zero {rc : runConstT} : forall RNG m sp A n, range_facts RNG m sp A n true -> 0 <= n -> range_facts RNG m sp A 0 true.
Proof.
  intros RNG m sp A n (LOW & HI & POS & _ & _ & APB & UNP & RG & (RLO & RHI & HULL & WR & RGH)) Hn. unfold AIMG_HI in LOW.
  split; [exact LOW|]. split; [lia|]. split; [destruct POS as [P|P]; [left; lia| right; exact P]|].
  split; [exists []; split; [reflexivity| apply bytes_at_nil; lia]|].
  split. { intros _. apply (UnreggLib.TwinB.mapped_chunk bsegs m 0 A); [lia| cbn; lia| intros i Hi; cbn in Hi; lia]. }
  split; [apply (Shadow.app_blk_sub _ _ _ _ APB); lia|].
  split; [apply (Shadow.unpoisoned_sub _ _ _ _ _ UNP); lia|].
  split; [apply (rng_sub _ _ _ _ _ RG); lia|].
  exists RLO, RHI. split; [lia| split; assumption].
Qed.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Hypothesis OPS_holds_ssh : forall m mo, op_holds OPS RangeC.TwinB.RangeC.SSH_ID [] m mo -> ssh_holds m.
Hypothesis OPS_holds_zro : forall m mo, op_holds OPS RangeC.TwinB.RangeC.ZRO_ID [] m mo -> zro_holds m.
Hypothesis OPS_holds_gsh : forall m mo, op_holds OPS GshC.TwinB.GshC.GSH_ID [] m mo -> gsh_holds GshC.TwinB.GshC.GSH_TAB_ASAN m.
Hypothesis OPS_holds_shmap : forall m mo, op_holds OPS GshC.TwinB.GshC.SHMAP_ID [] m mo -> UnreggPre.TwinB.shmap_holds m.
Hypothesis OPS_holds_zarg : forall az m mo, op_holds OPS StrRegC.TwinB.StrRegC.ZARG_ID [az] m mo -> zarg_holds az m.
Variable OTHER : Model -> Model -> Prop.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Variable SYM : Z.
Hypothesis WALK : memcpy_walk_stmt SYM.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP).
Hypothesis ACCT_frng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> FRNG AI AI_fake L RNG.
Hypothesis W_PAT : w_pat_ev_stmt AI ACCT UNIV Cw OPS.
Hypothesis ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc5000.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).

Lemma amemcpy_apply_shape : forall st sts, amemcpy_apply bsegs st = Some sts ->
  exists r hargs wnl st1 kd od srcv sofs n lenc,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ getr st X10 = VP kd od /\ getr st X11 = srcv /\ getr st X12 = VL n
    /\ wt n = false /\ 0 <= to_Z (wl n) <= 4096
    /\ 1 <= to_Z lenc <= 4096 /\ (to_Z (wl n) = 0 \/ lenc = wl n)
    /\ range_in bsegs st wnl kd od lenc true = true /\ src_ok bsegs st wnl srcv kd od lenc = Some sofs
    /\ copy_post bsegs kd od srcv sofs (wl n) (setpc (setr (clobber st1) X10 (VP kd od)) r) = Some sts.
Proof.
  intros st sts H. unfold amemcpy_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (getr st X10) as [|kd od| | | | | | | | |] eqn:G10; try discriminate H.
  destruct (getr st X12) as [n| | | | | | | | | |] eqn:G12; try discriminate H.
  cbv zeta in H.
  set (lenc := if PrimInt63.eqb (wl n) 0%uint63 then 1%uint63 else wl n) in *.
  destruct (src_ok bsegs st wnl (getr st X11) kd od lenc) as [sofs|] eqn:SRC; [|discriminate H].
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate H] end.
  repeat match type of CND with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in CND as [CND X] end.
  apply negb_true_iff in CND; apply Uint63.leb_spec in Q0; change (to_Z RangeC.TwinB.RangeC.NMAX) with 4096 in Q0.
  pose proof (to_Z_bounded (wl n)) as NB.
  assert (LC : 1 <= to_Z lenc <= 4096 /\ (to_Z (wl n) = 0 \/ lenc = wl n)).
  { unfold lenc. destruct (PrimInt63.eqb (wl n) 0%uint63) eqn:Z0.
    - apply Uint63.eqb_correct in Z0. rewrite Z0. change (to_Z 1%uint63) with 1. change (to_Z 0%uint63) with 0. split; [lia| left; reflexivity].
    - apply Uint63.eqb_false_spec in Z0. split; [| right; reflexivity]. split; [| lia].
      assert (to_Z (wl n) <> 0) by (intros QZ; apply Z0; apply to_Z_inj; exact QZ). lia. }
  destruct LC as [LC1 LC2].
  exists r, hargs, wnl, st1, kd, od, (getr st X11), sofs, n, lenc. repeat split; try reflexivity; try eassumption; lia.
Qed.

Lemma in_region_s_sound : forall E fs r o len, facts_hold E fs -> in_region_s fs r o len = true -> 0 <= to_Z len <= 2 ^ 32 ->
  loZ r <= w2Zs o /\ w2Zs o + to_Z len <= hiZ E r.
Proof.
  intros E fs r o len Hfs H Hl. unfold in_region_s in H. apply orb_prop in H as [H|H].
  - destruct (RangeFX.TwinB.RangeFX.in_region_sound E r o len H Hl) as (D1 & D2 & _). split; assumption.
  - repeat match type of H with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in H as [H X] end.
    apply Uint63.eqb_correct in H. apply negb_true_iff in Q2, Q1.
    pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ Hfs Q) as KL. cbn [den] in KL. rewrite wbv_unsigned, wadd_ok, wlit_ok in KL.
    pose proof (w2Z_range o) as ROD.
    assert (ODS : w2Z o < two63) by (unfold w2Z; rewrite Q2; pose proof (wl_range o); unfold two63 in *; lia).
    rewrite Z.mod_small in KL by (unfold two63, two64 in *; lia).
    assert (ES : w2Zs o = w2Z o) by (rewrite ValP.w2Zs_eq, Q2; lia).
    unfold loZ. rewrite H. change (keyZ 0%uint63) with 0. unfold hiZ. rewrite ES. lia.
Qed.

Lemma range_in_inv : forall st wnl k o len needw, range_in bsegs st wnl k o len needw = true ->
  exists r c, IMap.find k (s_regs st) = Some r /\ in_region_s (s_facts st) r o len = true /\ RangeC.TwinB.RangeC.range_class bsegs st wnl k o len needw = Some c
    /\ PrimInt63.eqb k 0%uint63 = false /\ (needw = true -> rg_w r = true).
Proof.
  intros st wnl k o len needw H. unfold range_in in H. destruct (IMap.find k (s_regs st)) as [r|] eqn:F; [|discriminate H].
  apply andb_prop in H as [IR H]. destruct (RangeC.TwinB.RangeC.range_class bsegs st wnl k o len needw) as [c|] eqn:RC; [|discriminate H].
  exists r, c. split; [reflexivity|]. split; [exact IR|]. split; [reflexivity|].
  unfold RangeC.TwinB.RangeC.range_class in RC. rewrite F in RC.
  destruct (negb (PrimInt63.eqb k 0%uint63) && implb needw (rg_w r))%bool eqn:C0; [|discriminate RC].
  apply andb_prop in C0 as [K0 NW]. apply negb_true_iff in K0. split; [exact K0|]. intros ->. exact NW.
Qed.

Definition amemcpy_leaf : Prop :=
  forall st sts (K : TSet) E ms mo r hargs wnl st1 kd od srcv sofs n (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) (src : list byte),
  st_ok bsegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' sts -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok bsegs OPS E' st' ms' mo' ->
               realizes bsegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) -> getr st X10 = VP kd od -> getr st X11 = srcv -> getr st X12 = VL n ->
  wt n = false -> 0 <= to_Z (wl n) <= 4096 ->
  copy_post bsegs kd od srcv sofs (wl n) (setpc (setr (clobber st1) X10 (VP kd od)) r) = Some sts ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ALib.Mem.mem_inv bsegs (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  let A0 := bv_unsigned (ev E kd) + w2Zs od in let A1 := bv_unsigned (den E srcv) in
  AIMG_HI <= A0 -> A0 + to_Z (wl n) + 8 <= 2 ^ 47 -> (A0 + to_Z (wl n) <= ATOP \/ bv_unsigned (AP.getr R 2) <= A0) ->
  A1 + to_Z (wl n) + 8 <= 2 ^ 47 -> (A1 + to_Z (wl n) <= ATOP \/ bv_unsigned (AP.getr R 2) <= A1) ->
  (A1 + to_Z (wl n) <= A0 \/ A0 + to_Z (wl n) <= A1) ->
  bv_unsigned (AP.getr R 10) = A0 -> bv_unsigned (AP.getr R 11) = A1 -> bv_unsigned (AP.getr R 12) = to_Z (wl n) ->
  length src = Z.to_nat (to_Z (wl n)) ->
  forall ms' mo',
  IMC.memcpy_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) src (CtrPre.TwinB.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes bsegs (mkCfg ms' mo') K.

Theorem amemcpy_sound_of_leaf : amemcpy_leaf ->
  forall pc, to_Z pc = SYM -> contract_sound bsegs OPS MP PB (amemcpy_c bsegs pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc amemcpy_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = SYM) by (rewrite Hspc; exact Hpc).
  destruct (amemcpy_apply_shape st sts Happ) as (r & hargs & wnl & st1 & kd & od & srcv & sofs & n & lenc & PRE & G10 & G11 & G12 & WTN & NR & NRc & LCE & RID & SRCOK & CPY).
  destruct (CtrPre.TwinB.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  set (R := ms_regs ms) in *. set (len := to_Z (wl n)) in *. set (lc := to_Z lenc) in *.
  destruct (range_in_inv _ _ _ _ _ _ RID) as (rd & cd & FD & IRD & RCD & KD0 & WD). specialize (WD eq_refl).

  destruct (range_class_facts_ev AI ACCT UNIV Cw OPS AI_fake Cw_sub_ghost OPS_holds_ssh ACCT_rng ACCT_rng_stk_sh ACCT_frng W_PAT E st ms mo r hargs wnl L RNG sta LBa aw
              kd od lenc true cd HS CF AH AC BOT LO SPT RCD NRc) as (DEN0 & RF0c).
  fold lc in RF0c.
  set (A0 := bv_unsigned (ev E kd) + w2Zs od) in *. set (A1 := bv_unsigned (den E srcv)) in *.
  pose proof atop_range as ATR.
  assert (LOW0c : AIMG_HI <= A0) by exact (proj1 RF0c).

  assert (SRCFc : srcF RNG (ms_mem ms) (bv_unsigned (AP.getr R 2)) A1 lc /\ (A1 + lc <= A0 \/ A0 + lc <= A1)).
  { unfold src_ok in SRCOK. destruct srcv as [a|ks os| | | | | | | | |]; try discriminate SRCOK.
    -
      destruct (RangeC.TwinB.RangeC.lit_low st a lenc) eqn:LL.
      2:{
        cbn [orb] in SRCOK. destruct (GshC.TwinB.GshC.lit_gsh GshC.TwinB.GshC.CFG_ASAN st a lenc) eqn:LG; [|discriminate SRCOK].
        destruct (lit_gsh_inv st a lenc LG) as (WTG & LAG & HAG & QUG & FGG & FMG). fold lc in HAG, QUG.
        assert (EAG : A1 = to_Z (wl a)).
        { unfold A1. cbn [den]. rewrite wbv_unsigned. unfold w2Z. rewrite WTG. lia. }
        pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.TwinB.find_op_In _ _ _ FGG)) as HOG. cbn [op_id op_args map] in HOG.
        pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.TwinB.find_op_In _ _ _ FMG)) as HOM. cbn [op_id op_args map] in HOM.
        destruct (gsh_range_facts_ok RNG (ms_mem ms) A1 lc (OPS_holds_gsh _ _ HOG) (OPS_holds_shmap _ _ HOM) (ACCT_rng_aimg _ _ _ _ _ _ AC) (ACCT_rng_aimg_sh _ _ _ _ _ _ AC)
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite EAG; exact QUG)) as (SRCB & APB1 & UNP1 & RNG1 & HULL).
        split; [| left; unfold AIMG_HI in LOW0c; lia].
        split; [lia|]. split; [left; lia|]. split; [exact SRCB|]. split; [exact APB1|]. split; [exact UNP1|]. split; [exact RNG1| exact HULL]. }
      cbn [orb] in SRCOK.
      destruct (lit_low_inv st a lenc LL ltac:(lia)) as (WTA & LA & HA & FZ). fold lc in HA.
      assert (EA : A1 = to_Z (wl a)).
      { unfold A1. cbn [den]. rewrite wbv_unsigned. unfold w2Z. rewrite WTA. lia. }
      pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.TwinB.find_op_In _ _ _ FZ)) as HO. cbn [op_id op_args map] in HO.
      pose proof (OPS_holds_zro _ _ HO) as ZRO.
      destruct (low_range_facts_ok RNG (ms_mem ms) A1 lc ZRO (ACCT_rng_aimg _ _ _ _ _ _ AC) (ACCT_rng_aimg_sh _ _ _ _ _ _ AC) ltac:(lia) ltac:(lia) ltac:(lia))
        as (_ & _ & SRCB & APB1 & UNP1 & RNG1 & HULL).
      split; [| left; unfold AIMG_HI in LOW0c; lia].
      split; [lia|]. split; [left; lia|]. split; [exact SRCB|]. split; [exact APB1|]. split; [exact UNP1|]. split; [exact RNG1| exact HULL].
    -
      match type of SRCOK with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate SRCOK] end. apply andb_prop in CND as [RIS DJ].
      apply orb_prop in RIS. destruct RIS as [RIS|ARG].
      2:{
        unfold StrRegC.TwinB.StrRegC.arg_range in ARG. destruct (IMap.find ks (s_regs st)) as [rs|] eqn:FSs; [|discriminate ARG].
        repeat match type of ARG with (_ && _)%bool = true => let X := fresh "G" in apply andb_prop in ARG as [ARG X] end.
        apply negb_true_iff in G2, G1.
        assert (SRO : exists j js, StrRegC.TwinB.StrRegC.str_reg_ok st wnl ks rs j js = true).
        { apply orb_prop in ARG. destruct ARG as [Q|Q]; [exists 1%uint63, 9%uint63| exists 3%uint63, 10%uint63]; exact Q. }
        destruct SRO as (j & js & SRO).
        destruct (str_reg_ok_shape st wnl ks rs j js SRO) as (az & _ & KS0 & _ & LOs & WS & _ & _ & _ & _ & _ & _ & _).
        pose proof (known_leu_sound_r_plain OPS E st ms mo _ _ HS G) as KL.        cbn [den] in KL. rewrite wbv_unsigned, wadd_ok, wlit_ok in KL.
        pose proof (w2Z_range os) as ROS.
        assert (ODS : w2Z os < two63) by (unfold w2Z; rewrite G2; pose proof (wl_range os); unfold two63 in *; lia).
        rewrite Z.mod_small in KL by (unfold two63, two64 in *; fold lc; lia). fold lc in KL.
        change (bv_unsigned (den E (rg_hi rs))) with (hiZ E rs) in KL.
        assert (ES : w2Zs os = w2Z os) by (rewrite ValP.w2Zs_eq, G2; lia).
        destruct (str_reg_facts AI ACCT UNIV Cw OPS OPS_holds_zarg ACCT_rng ACCT_rng_stk_sh E st ms mo r hargs wnl L RNG sta LBa aw ks rs j js (w2Z os) lc HS CF AC BOT LO SPT FSs SRO
                    ltac:(lia) ltac:(lia) KL) as (RLO1 & RHI1 & KE & BYT & SPA & APB1 & SPOS & UNP1 & HULL1 & WRH1 & RNG1 & RNGH1).
        fold R in SPA.
        assert (EA1 : A1 = bv_unsigned (ev E ks) + w2Z os).
        { unfold A1. rewrite ValP.den_VP, ES. apply Z.mod_small. pose proof (bv_unsigned_in_range _ (ev E ks)). unfold two64. lia. }
        rewrite <- EA1 in BYT, SPA, APB1, UNP1, HULL1, RNG1.
        split.
        { split; [lia|]. split; [right; exact SPA|].
          split; [eexists; split; [| exact BYT]; rewrite length_map, length_seq; reflexivity|].
          split; [exact APB1|]. split; [exact UNP1|]. split; [exact RNG1|]. exists RLO1, RHI1. split; [exact HULL1|]. split; [exact WRH1| exact RNGH1]. }
        assert (KK : kd <> ks) by (intros ->; rewrite FD in FSs; injection FSs as ->; rewrite WD in WS; discriminate WS).
        destruct (in_region_s_sound E _ rd od lenc (so_facts _ _ _ _ _ _ HS) IRD ltac:(lia)) as (D1 & D2). fold lc in D2.
        pose proof (so_disj _ _ _ _ _ _ HS kd rd ks rs FD FSs KK KD0 KS0 (or_introl WD)) as NO.
        assert (LZs : loZ rs = 0) by (unfold loZ; rewrite LOs; reflexivity).
        destruct (Z_le_gt_dec (A1 + lc) A0) as [Q1|Q1]; [left; exact Q1|]. destruct (Z_le_gt_dec (A0 + lc) A1) as [Q2|Q2]; [right; exact Q2|].
        exfalso. apply (NO (Z.max A0 A1)). rewrite LZs. unfold A0 in *. rewrite EA1 in *. lia. }
      destruct (range_in_inv _ _ _ _ _ _ RIS) as (rs & cs & FSs & IRS & RCS & KS0 & _).
      destruct (range_class_facts_ev AI ACCT UNIV Cw OPS AI_fake Cw_sub_ghost OPS_holds_ssh ACCT_rng ACCT_rng_stk_sh ACCT_frng W_PAT E st ms mo r hargs wnl L RNG sta LBa aw
                  ks os lenc false cs HS CF AH AC BOT LO SPT RCS NRc) as (DEN1 & LOW1 & HI1 & POS1 & SRCB & _ & APB1 & UNP1 & RNG1 & HULL).
      fold lc in HI1, POS1, SRCB, APB1, UNP1, RNG1, HULL. unfold A1. rewrite DEN1.
      split; [split; [exact HI1|]; split; [exact POS1|]; split; [exact SRCB|]; split; [exact APB1|]; split; [exact UNP1|]; split; [exact RNG1| exact HULL]|].
      unfold disjoint_ok in DJ. destruct (PrimInt63.eqb ks kd) eqn:KK.
      + apply Uint63.eqb_correct in KK. subst ks. apply orb_prop in DJ as [Q|Q]; apply Z.leb_le in Q; fold lc in Q; unfold A0; lia.
      + apply Uint63.eqb_false_spec in KK.
        destruct (in_region_s_sound E _ rd od lenc (so_facts _ _ _ _ _ _ HS) IRD ltac:(lia)) as (D1 & D2).
        destruct (in_region_s_sound E _ rs os lenc (so_facts _ _ _ _ _ _ HS) IRS ltac:(lia)) as (S1 & S2). fold lc in D2, S2.
        pose proof (so_disj _ _ _ _ _ _ HS kd rd ks rs FD FSs ltac:(intros Q; apply KK; symmetry; exact Q) KD0 KS0 (or_introl WD)) as NO.
        set (A1' := bv_unsigned (ev E ks) + w2Zs os) in *.
        destruct (Z_le_gt_dec (A1' + lc) A0) as [Q1|Q1]; [left; exact Q1|]. destruct (Z_le_gt_dec (A0 + lc) A1') as [Q2|Q2]; [right; exact Q2|].
        exfalso. apply (NO (Z.max A0 A1')). unfold A0, A1' in *. lia. }

  assert (A1pos : 0 <= A1) by (unfold A1; pose proof (bv_unsigned_in_range 64 (den E srcv)); lia).
  assert (FACTS : range_facts RNG (ms_mem ms) (bv_unsigned (AP.getr R 2)) A0 len true
                  /\ srcF RNG (ms_mem ms) (bv_unsigned (AP.getr R 2)) A1 len /\ (A1 + len <= A0 \/ A0 + len <= A1)).
  { destruct SRCFc as [SF DJc]. destruct LCE as [Z0| ->].
    - rewrite Z0. split; [exact (range_facts_zero _ _ _ _ _ RF0c ltac:(lia))|]. split; [exact (srcF_zero _ _ _ _ _ SF ltac:(lia) A1pos)| lia].
    - fold len in RF0c, SF, DJc. auto. }
  destruct FACTS as ((LOW0 & HI0 & POS0 & _ & DSTW & APB0 & UNP0 & RNG0 & RLO2 & RHI2 & HULL2 & WRH2 & RNGH2)
                     & (HI1 & POS1 & (src & LSRC & SRCB) & APB1 & UNP1 & RNG1 & (RLO1 & RHI1 & HULL1 & WRH1 & RNGH1)) & DISJ).
  destruct (DSTW eq_refl) as (junk & DST).

  assert (EA0 : bv_unsigned (AP.getr R (reg_of_r5 X10)) = A0).
  { unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10), G10. exact DEN0. }
  assert (EA1 : bv_unsigned (AP.getr R (reg_of_r5 X11)) = A1).
  { unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X11), G11. reflexivity. }
  assert (EA2 : bv_unsigned (AP.getr R (reg_of_r5 X12)) = len).
  { unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X12), G12. cbn [den]. rewrite wbv_unsigned. unfold w2Z. rewrite WTN. unfold len. lia. }
  idtac "MC-1".
  assert (EA0' : bv_unsigned (AP.getr R 10) = A0) by exact EA0. assert (EA1' : bv_unsigned (AP.getr R 11) = A1) by exact EA1.
  assert (EA2' : bv_unsigned (AP.getr R 12) = len) by exact EA2.
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG.
  assert (EV : evtF bsegs RNG
            (IMC.memcpy_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) src (CtrPre.TwinB.sp_lo E st) (ms_mem ms))
            (MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                (ms_fregs ms) (Z_to_bv 64 SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom bsegs))).
  { unfold artcells in RT. decompose [and] RT. clear RT.
    eapply (WALK RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_fregs ms) (ms_fcsr ms) (ms_mem ms)
              (CtrPre.TwinB.sp_lo E st) src junk RLO1 RHI1 RLO2 RHI2).
    all: rewrite ?EA0', ?EA1', ?EA2'.
    all: try lazymatch goal with
         | |- ALib.Mem.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact ST
         | |- ALib.Mem.bytes_at _ _ _ _ => exact SRCB
         | |- length _ = _ => exact LSRC
         | |- ALib.Step.rw_cells _ _ _ [CB _ _] => exact DST
         | |- ALib.Step.rw_cells _ _ _ _ => assumption
         | |- Shadow.unpoisoned _ _ _ => first [exact UNP1 | exact UNP0]
         | |- Shadow.app_blk _ _ => first [exact APB1 | exact APB0]
         | |- ALib.Mem.wr_at _ _ _ _ => first [exact WRH1 | exact WRH2]
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ _ => first [exact RNGH1 | exact RNGH2 | exact RNG1 | exact RNG0 | exact RSTK]
         | |- _ <= _ /\ _ => first [exact HULL1 | exact HULL2]
         end.
    all: try (unfold Shadow.KHIGH in *; lia).
    all: try (destruct POS0 as [P|P]; [left; lia | right; exact P]).
    all: try (destruct POS1 as [P|P]; [left; lia | right; exact P]).
    all: match goal with |- ?G => idtac "REMW" G end. }
  rewrite Ems, HPC. apply (GlueA.TwinB.realizes_to_mkRA bsegs).
  eapply (implS_twfS_realizes_silent bsegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ IMC.memcpy_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) src (CtrPre.TwinB.sp_lo E st) (ms_mem ms) ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    exact (LEAF st sts K E ms mo r hargs wnl st1 kd od srcv sofs n L RNG sta LBa aw src HS HPB HK PRE G10 G11 G12 WTN NR CPY CP FS CF AH MI BOT LO SPT
             LOW0 HI0 POS0 HI1 POS1 DISJ EA0 EA1 EA2 LSRC ms' mo' HQ HMP' HMI' OTH ACP).
Qed.
End Sound.
End TwinB.
