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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs DefsA DefsB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB MemcpyCtr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA GlueA CtrPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import UnreggSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import StackSh RangeC ReadC ReadPre ReadPost RstageC MemsetPre RangePre MemcpySound.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX ActrA RstageC.
Module IMC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.I_memcpy.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition rs_post (st st1 : sstate) (r kb : int) (X off : sv) : sstate :=
  let n := getr st X12 in
  let st2 := setr (clobber st1) X10 (getr st X10) in
  let rb' := Region 0%uint63 (CtrB.new_hi (s_facts st) X n) true (BGBlob 4%uint63 0%uint63) IMap.empty in
  setpc (set_ops (setregs st2 (IMap.add kb rb' (s_regs st2))) (set_op ReadC.RSTV_ID [sv_alu ALU_ADD off n; VL wzero] (s_ops st2))) r.

Lemma arstage_apply_shape : forall st sts, arstage_apply ReadC.CFG_ASAN st = Some sts ->
  exists r hargs wnl st1 kb X off n' wlen rb,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ getr st X11 = VL (wlit (ReadC.r_stage ReadC.CFG_ASAN))
    /\ CtrA.sym_offset (s_regs st) (getr st X10) = Some (kb, X)
    /\ find_op ReadC.RSTV_ID (s_ops st) = Some [off; n'] /\ CtrA.count_op ReadC.RSTV_ID (s_ops st) = 1%nat
    /\ find_op (ReadC.r_zsh ReadC.CFG_ASAN) (s_ops st) = Some []
    /\ CtrA.win_lookup wnl kb = Some (wlen, CtrLib.K_BLOCK) /\ others_twins wnl kb = true
    /\ IMap.find kb (s_regs st) = Some rb /\ rg_cells rb = IMap.Leaf /\ prefix_ok (s_facts st) rb X = true
    /\ rg_lo rb = 0%uint63 /\ rg_w rb = true
    /\ known_eq (s_facts st) off X = true /\ known_eq (s_facts st) n' (getr st X12) = true
    /\ known_leu (s_facts st) X wlen = true /\ known_leu (s_facts st) (getr st X12) (sv_alu ALU_SUB wlen X) = true
    /\ known_ltu (s_facts st) (VL wzero) (getr st X12) = true
    /\ RangeC.pat_ok st wnl kb CtrLib.K_BLOCK = true
    /\ sts = [rs_post st st1 r kb X off].
Proof.
  intros st sts H. unfold arstage_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (getr st X11) as [rs| | | | | | | | | |] eqn:G11; try discriminate H.
  destruct (CtrA.sym_offset (s_regs st) (getr st X10)) as [[kb X]|] eqn:SO; [|discriminate H].
  destruct (find_op ReadC.RSTV_ID (s_ops st)) as [[|off [|n' [|? ?]]]|] eqn:F3; try discriminate H.
  destruct (find_op (ReadC.r_zsh ReadC.CFG_ASAN) (s_ops st)) as [[|? ?]|] eqn:FZ; try discriminate H.
  destruct (CtrA.win_lookup wnl kb) as [[wlen kd]|] eqn:WL; [|discriminate H].
  destruct (IMap.find kb (s_regs st)) as [rb|] eqn:FB; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:PKC; [discriminate H|] end. apply negb_false_iff in PKC.
  cbv zeta in H. match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate H] end.
  repeat match type of CND with (_ && _)%bool = true => let Q := fresh "Q" in apply andb_prop in CND as [CND Q] end.
  apply weqb_eq in CND. subst rs. apply Nat.eqb_eq in Q10. apply weqb_eq in Q9. subst kd. apply Uint63.eqb_correct in Q5.
  destruct (rg_cells rb) eqn:CB; [|discriminate Q7].
  injection H as <-.
  exists r, hargs, wnl, st1, kb, X, off, n', wlen, rb. repeat (split; [reflexivity || assumption|]). reflexivity.
Qed.

Lemma bytes_at_of_rb {rc : runConstT} : forall (m : amem) A (bs : list byte),
  0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall j, 0 <= j < Z.of_nat (length bs) -> rb asegs m (A + j) = nth_error bs (Z.to_nat j)) ->
  ALib.Mem.bytes_at asegs m A bs.
Proof.
  intros m A bs HA HB H. split; [exact HA|]. split; [exact HB|]. intros i Hi. rewrite <- (GlueA.rb_mrdA asegs).
  rewrite (H (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id. reflexivity.
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
Hypothesis W_PAT : w_pat_ev_stmt AI ACCT UNIV Cw OPS.
Variable file : list byte.
Hypothesis OPS_holds_zsh : forall m mo, op_holds OPS (ReadC.r_zsh ReadC.CFG_ASAN) [] m mo -> zsh_holds m.
Hypothesis OPS_holds_rstage : forall args m mo, op_holds OPS ReadC.RSTV_ID args m mo -> rstage_holds_v file args m.
Variable OTHER : Model -> Model -> Prop.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Variable SYM : Z.
Hypothesis WALK : memcpy_walk_stmt SYM.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc4000.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).

Definition stage_src (off n : Z) : list byte := map (fun i => nth (Z.to_nat off + i)%nat file (Z_to_bv 8 0)) (seq 0 (Z.to_nat n)).
Lemma stage_src_len : forall off n, length (stage_src off n) = Z.to_nat n.
Proof. intros. unfold stage_src. rewrite length_map, length_seq. reflexivity. Qed.

Definition arstage_leaf : Prop :=
  forall st (K : TSet) E ms mo r hargs wnl st1 kb X off n' wlen rb (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word),
  st_ok asegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' [rs_post st st1 r kb X off] -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok asegs OPS E' st' ms' mo' ->
               realizes asegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) ->
  CtrA.sym_offset (s_regs st) (getr st X10) = Some (kb, X) ->
  find_op ReadC.RSTV_ID (s_ops st) = Some [off; n'] -> CtrA.count_op ReadC.RSTV_ID (s_ops st) = 1%nat ->
  CtrA.win_lookup wnl kb = Some (wlen, CtrLib.K_BLOCK) -> others_twins wnl kb = true ->
  IMap.find kb (s_regs st) = Some rb -> rg_cells rb = IMap.Leaf -> prefix_ok (s_facts st) rb X = true ->
  rg_lo rb = 0%uint63 -> rg_w rb = true ->
  known_eq (s_facts st) off X = true -> known_eq (s_facts st) n' (getr st X12) = true ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ALib.Mem.mem_inv asegs (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  let Db := bv_unsigned (ev E kb) in let Xz := bv_unsigned (den E X) in let nZ := bv_unsigned (den E (getr st X12)) in
  let wlenZ := bv_unsigned (den E wlen) in
  0 < nZ <= 65536 -> Xz + nZ <= wlenZ -> AIMG_HI <= Db + Xz -> Db + Xz + nZ <= ATOP ->
  Xz + nZ <= Z.of_nat (length file) ->
  bv_unsigned (AP.getr R 10) = Db + Xz -> bv_unsigned (AP.getr R 11) = STAGE -> bv_unsigned (AP.getr R 12) = nZ ->
  forall ms' mo',
  IMC.memcpy_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (stage_src Xz nZ) (CtrPre.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes asegs (mkCfg ms' mo') K.

Theorem arstage_sound_of_leaf : arstage_leaf ->
  forall pc, to_Z pc = SYM -> contract_sound asegs OPS MP PB (arstage_c ReadC.CFG_ASAN pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc arstage_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = SYM) by (rewrite Hspc; exact Hpc).
  destruct (arstage_apply_shape st sts Happ)
    as (r & hargs & wnl & st1 & kb & X & off & n' & wlen & rb & PRE & G11 & SO & F3 & CNT & FZ & WL & OT & FB & CB & PFX & LO0 & RW & EQoff & EQn & LEX & LEn & POSn & PKb & ->).
  destruct (CtrPre.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs. pose proof atop_range as ATR.
  set (R := ms_regs ms) in *. set (m := ms_mem ms) in *.
  set (Db := bv_unsigned (ev E kb)) in *. set (Xz := bv_unsigned (den E X)) in *. set (nsv := getr st X12) in *.
  set (nZ := bv_unsigned (den E nsv)) in *. set (wlenZ := bv_unsigned (den E wlen)) in *.
  pose proof (bv_unsigned_in_range 64 (den E X)) as XR. change (bv_modulus 64) with (2 ^ 64) in XR. fold Xz in XR.
  pose proof (bv_unsigned_in_range 64 (den E nsv)) as NR. change (bv_modulus 64) with (2 ^ 64) in NR. fold nZ in NR.
  pose proof (bv_unsigned_in_range 64 (den E wlen)) as WLR. change (bv_modulus 64) with (2 ^ 64) in WLR. fold wlenZ in WLR.

  apply (HeapCtr.known_leu_sound E _ _ _ Hfs) in LEX. fold Xz wlenZ in LEX.
  apply (HeapCtr.known_leu_sound E _ _ _ Hfs) in LEn. rewrite den_sv_alu in LEn. cbn [alu64 alu] in LEn. rewrite bv_sub_unsigned in LEn. fold nZ Xz wlenZ in LEn.
  assert (SUM : Xz + nZ <= wlenZ).
  { unfold bv_wrap in LEn. change (bv_modulus 64) with (2 ^ 64) in LEn. rewrite Z.mod_small in LEn; lia. }
  apply (HeapCtr.known_ltu_sound E _ _ _ Hfs) in POSn. cbn [den] in POSn. rewrite wbv_unsigned, wzero_ok in POSn. fold nZ in POSn.
  pose proof (HeapCtr.known_eq_sound E _ _ _ Hfs EQoff) as Eoff. pose proof (HeapCtr.known_eq_sound E _ _ _ Hfs EQn) as En.

  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.find_op_In _ _ _ F3)) as H3. cbn [op_id op_args map] in H3.
  pose proof (OPS_holds_rstage _ _ _ H3) as RSV. cbn [rstage_holds_v] in RSV. rewrite Eoff, En in RSV. fold Xz nZ in RSV.
  destruct RSV as (FLEN & N64K & BY3).

  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.find_op_In _ _ _ FZ)) as HZ. cbn [op_id op_args map] in HZ.
  pose proof (OPS_holds_zsh _ _ HZ) as ZSH.

  assert (KT : W64.weqb CtrLib.K_BLOCK ActrA.K_TWIN = false) by reflexivity.
  destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw kb wlen CtrLib.K_BLOCK Xz (Xz + nZ) CF WL KT
              ltac:(vm_compute; congruence) ltac:(vm_compute; congruence) ltac:(vm_compute; split; [discriminate| reflexivity]) ltac:(lia) ltac:(lia) ltac:(fold wlenZ; lia)) as (p & Ab & nb & HINB & BA1 & BA2).
  pose proof (W_PAT E st ms mo r hargs wnl L RNG sta LBa aw kb wlen CtrLib.K_BLOCK p Ab nb HS CF AH WL KT ltac:(vm_compute; congruence) ltac:(vm_compute; congruence) PKb Xz (Xz + nZ) ltac:(lia) ltac:(lia) ltac:(fold wlenZ; lia) HINB BA1 BA2) as PAT_p.
  fold Db in BA1, BA2.
  destruct (block_range_facts AI L RNG sta LBa m p Ab nb (Db + Xz) nZ AH HINB PAT_p BA1 ltac:(lia) ltac:(lia))
    as ((junk & DST) & APB0 & UNP0 & LOWA & HIA & RNGD & RLOd & RHId & HULLd & WRHd & RNGHd).

  set (src := stage_src Xz nZ).
  assert (LSRC : length src = Z.to_nat nZ) by apply stage_src_len.
  assert (SRCB : ALib.Mem.bytes_at asegs m STAGE src).
  { apply bytes_at_of_rb; [unfold STAGE; lia| rewrite LSRC, Z2Nat.id by lia; unfold STAGE; lia|]. rewrite LSRC, Z2Nat.id by lia.
    intros j Hj. unfold m. rewrite (BY3 j Hj). unfold src, stage_src. rewrite nth_error_map, nth_error_seq.
    destruct (Nat.ltb_spec (Z.to_nat j) (Z.to_nat nZ)); [| lia]. cbn [option_map]. f_equal. f_equal. lia. }

  assert (EA0 : bv_unsigned (AP.getr R (reg_of_r5 X10)) = Db + Xz).
  { unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X10), (MemcpyCtr.sym_offset_sound E (s_regs st) _ kb X SO).
    rewrite bv_add_unsigned. fold Db Xz. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). unfold AIMG_HI in *. lia. }
  assert (EA1 : bv_unsigned (AP.getr R (reg_of_r5 X11)) = STAGE).
  { unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X11), G11. cbn [den]. rewrite wbv_unsigned, wlit_ok. reflexivity. }
  assert (EA2 : bv_unsigned (AP.getr R (reg_of_r5 X12)) = nZ).
  { unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X12). reflexivity. }
  assert (EA0' : bv_unsigned (AP.getr R 10) = Db + Xz) by exact EA0. assert (EA1' : bv_unsigned (AP.getr R 11) = STAGE) by exact EA1.
  assert (EA2' : bv_unsigned (AP.getr R 12) = nZ) by exact EA2.
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG. pose proof (ACCT_rng_aimg_sh _ _ _ _ _ _ AC) as RISH.
  assert (SH1 : shad RLO2 = ZSH_LO) by (vm_compute; reflexivity). assert (SH2 : shad RHI2 = ZSH_HI) by (vm_compute; reflexivity).
  assert (EV : evtF asegs RNG
            (IMC.memcpy_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) src (CtrPre.sp_lo E st) m)
            (MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                (ms_fregs ms) (Z_to_bv 64 SYM) (ms_fcsr ms) None m (seg_rom asegs))).
  { unfold artcells in RT. decompose [and] RT. clear RT.
    eapply (WALK RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_fregs ms) (ms_fcsr ms) m
              (CtrPre.sp_lo E st) src junk RLO2 RHI2 RLOd RHId).
    all: rewrite ?EA0', ?EA1', ?EA2'.
    all: try lazymatch goal with
         | |- ALib.Mem.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact ST
         | |- ALib.Mem.bytes_at _ _ _ _ => exact SRCB
         | |- length _ = _ => exact LSRC
         | |- ALib.Step.rw_cells _ _ _ [CB _ _] => exact DST
         | |- ALib.Step.rw_cells _ _ _ _ => assumption
         | |- Shadow.unpoisoned _ STAGE _ => apply (zsh_unpoisoned _ _ ZSH); lia
         | |- Shadow.unpoisoned _ _ _ => exact UNP0
         | |- Shadow.app_blk STAGE _ => unfold Shadow.app_blk, Shadow.KLOW, Shadow.KHIGH, Shadow.KEND, STAGE; lia
         | |- Shadow.app_blk _ _ => exact APB0
         | |- ALib.Mem.wr_at _ _ (shad RLO2) _ => exact (zsh_wr _ ZSH)
         | |- ALib.Mem.wr_at _ _ _ _ => exact WRHd
         | |- rng_aimg _ => exact RIMG
         | |- rng _ (shad RLO2) _ => rewrite SH1, SH2; eapply rng_sub'; [exact RISH| unfold ZSH_LO, ZSH_HI; lia]
         | |- rng _ STAGE _ => eapply rng_sub'; [exact RIMG| unfold STAGE; lia]
         | |- rng _ _ _ => first [exact RNGHd | exact RNGD | exact RSTK]
         | |- _ <= _ /\ _ => first [exact HULLd | unfold STAGE, RLO2, RHI2, Shadow.KEND; repeat split; lia]
         end.
    all: try (unfold STAGE, Shadow.KHIGH, AIMG_HI in *; lia).
    all: match goal with |- ?G => idtac "REMW" G end. }
  rewrite Ems, HPC. apply (GlueA.realizes_to_mkRA asegs).
  eapply (implS_twfS_realizes_silent asegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ IMC.memcpy_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) src (CtrPre.sp_lo E st) m ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    assert (NB : 0 < nZ <= 65536) by lia.
    exact (LEAF st K E ms mo r hargs wnl st1 kb X off n' wlen rb L RNG sta LBa aw HS HPB HK PRE SO F3 CNT WL OT FB CB PFX LO0 RW EQoff EQn CP FS CF AH MI BOT LO SPT
             NB SUM LOWA HIA FLEN EA0 EA1 EA2 ms' mo' HQ HMP' HMI' OTH ACP).
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
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsB.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import UnreggSound.TwinB.
Import StackSh.TwinB RangeC.TwinB ReadC.TwinB ReadPre.TwinB ReadPost.TwinB RstageC.TwinB MemsetPre.TwinB RangePre.TwinB MemcpySound.TwinB.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX ActrA RstageC.TwinB.RstageC.
Module IMC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.TwinB.I_memcpy.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition rs_post (st st1 : sstate) (r kb : int) (X off : sv) : sstate :=
  let n := getr st X12 in
  let st2 := setr (clobber st1) X10 (getr st X10) in
  let rb' := Region 0%uint63 (CtrB.new_hi (s_facts st) X n) true (BGBlob 4%uint63 0%uint63) IMap.empty in
  setpc (set_ops (setregs st2 (IMap.add kb rb' (s_regs st2))) (set_op ReadC.TwinB.ReadC.RSTV_ID [sv_alu ALU_ADD off n; VL wzero] (s_ops st2))) r.

Lemma arstage_apply_shape : forall st sts, arstage_apply ReadC.TwinB.ReadC.CFG_ASAN st = Some sts ->
  exists r hargs wnl st1 kb X off n' wlen rb,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ getr st X11 = VL (wlit (ReadC.TwinB.ReadC.r_stage ReadC.TwinB.ReadC.CFG_ASAN))
    /\ CtrA.sym_offset (s_regs st) (getr st X10) = Some (kb, X)
    /\ find_op ReadC.TwinB.ReadC.RSTV_ID (s_ops st) = Some [off; n'] /\ CtrA.count_op ReadC.TwinB.ReadC.RSTV_ID (s_ops st) = 1%nat
    /\ find_op (ReadC.TwinB.ReadC.r_zsh ReadC.TwinB.ReadC.CFG_ASAN) (s_ops st) = Some []
    /\ CtrA.win_lookup wnl kb = Some (wlen, CtrLib.K_BLOCK) /\ others_twins wnl kb = true
    /\ IMap.find kb (s_regs st) = Some rb /\ rg_cells rb = IMap.Leaf /\ prefix_ok (s_facts st) rb X = true
    /\ rg_lo rb = 0%uint63 /\ rg_w rb = true
    /\ known_eq (s_facts st) off X = true /\ known_eq (s_facts st) n' (getr st X12) = true
    /\ known_leu (s_facts st) X wlen = true /\ known_leu (s_facts st) (getr st X12) (sv_alu ALU_SUB wlen X) = true
    /\ known_ltu (s_facts st) (VL wzero) (getr st X12) = true
    /\ RangeC.TwinB.RangeC.pat_ok st wnl kb CtrLib.K_BLOCK = true
    /\ sts = [rs_post st st1 r kb X off].
Proof.
  intros st sts H. unfold arstage_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (getr st X11) as [rs| | | | | | | | | |] eqn:G11; try discriminate H.
  destruct (CtrA.sym_offset (s_regs st) (getr st X10)) as [[kb X]|] eqn:SO; [|discriminate H].
  destruct (find_op ReadC.TwinB.ReadC.RSTV_ID (s_ops st)) as [[|off [|n' [|? ?]]]|] eqn:F3; try discriminate H.
  destruct (find_op (ReadC.TwinB.ReadC.r_zsh ReadC.TwinB.ReadC.CFG_ASAN) (s_ops st)) as [[|? ?]|] eqn:FZ; try discriminate H.
  destruct (CtrA.win_lookup wnl kb) as [[wlen kd]|] eqn:WL; [|discriminate H].
  destruct (IMap.find kb (s_regs st)) as [rb|] eqn:FB; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:PKC; [discriminate H|] end. apply negb_false_iff in PKC.
  cbv zeta in H. match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate H] end.
  repeat match type of CND with (_ && _)%bool = true => let Q := fresh "Q" in apply andb_prop in CND as [CND Q] end.
  apply weqb_eq in CND. subst rs. apply Nat.eqb_eq in Q10. apply weqb_eq in Q9. subst kd. apply Uint63.eqb_correct in Q5.
  destruct (rg_cells rb) eqn:CB; [|discriminate Q7].
  injection H as <-.
  exists r, hargs, wnl, st1, kb, X, off, n', wlen, rb. repeat (split; [reflexivity || assumption|]). reflexivity.
Qed.

Lemma bytes_at_of_rb {rc : runConstT} : forall (m : amem) A (bs : list byte),
  0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall j, 0 <= j < Z.of_nat (length bs) -> rb bsegs m (A + j) = nth_error bs (Z.to_nat j)) ->
  ALib.Mem.bytes_at bsegs m A bs.
Proof.
  intros m A bs HA HB H. split; [exact HA|]. split; [exact HB|]. intros i Hi. rewrite <- (GlueA.TwinB.rb_mrdA bsegs).
  rewrite (H (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id. reflexivity.
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
Hypothesis W_PAT : w_pat_ev_stmt AI ACCT UNIV Cw OPS.
Variable file : list byte.
Hypothesis OPS_holds_zsh : forall m mo, op_holds OPS (ReadC.TwinB.ReadC.r_zsh ReadC.TwinB.ReadC.CFG_ASAN) [] m mo -> zsh_holds m.
Hypothesis OPS_holds_rstage : forall args m mo, op_holds OPS ReadC.TwinB.ReadC.RSTV_ID args m mo -> rstage_holds_v file args m.
Variable OTHER : Model -> Model -> Prop.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Variable SYM : Z.
Hypothesis WALK : memcpy_walk_stmt SYM.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc5000.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).

Definition stage_src (off n : Z) : list byte := map (fun i => nth (Z.to_nat off + i)%nat file (Z_to_bv 8 0)) (seq 0 (Z.to_nat n)).
Lemma stage_src_len : forall off n, length (stage_src off n) = Z.to_nat n.
Proof. intros. unfold stage_src. rewrite length_map, length_seq. reflexivity. Qed.

Definition arstage_leaf : Prop :=
  forall st (K : TSet) E ms mo r hargs wnl st1 kb X off n' wlen rb (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word),
  st_ok bsegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' [rs_post st st1 r kb X off] -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok bsegs OPS E' st' ms' mo' ->
               realizes bsegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) ->
  CtrA.sym_offset (s_regs st) (getr st X10) = Some (kb, X) ->
  find_op ReadC.TwinB.ReadC.RSTV_ID (s_ops st) = Some [off; n'] -> CtrA.count_op ReadC.TwinB.ReadC.RSTV_ID (s_ops st) = 1%nat ->
  CtrA.win_lookup wnl kb = Some (wlen, CtrLib.K_BLOCK) -> others_twins wnl kb = true ->
  IMap.find kb (s_regs st) = Some rb -> rg_cells rb = IMap.Leaf -> prefix_ok (s_facts st) rb X = true ->
  rg_lo rb = 0%uint63 -> rg_w rb = true ->
  known_eq (s_facts st) off X = true -> known_eq (s_facts st) n' (getr st X12) = true ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ALib.Mem.mem_inv bsegs (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  let Db := bv_unsigned (ev E kb) in let Xz := bv_unsigned (den E X) in let nZ := bv_unsigned (den E (getr st X12)) in
  let wlenZ := bv_unsigned (den E wlen) in
  0 < nZ <= 65536 -> Xz + nZ <= wlenZ -> AIMG_HI <= Db + Xz -> Db + Xz + nZ <= ATOP ->
  Xz + nZ <= Z.of_nat (length file) ->
  bv_unsigned (AP.getr R 10) = Db + Xz -> bv_unsigned (AP.getr R 11) = STAGE -> bv_unsigned (AP.getr R 12) = nZ ->
  forall ms' mo',
  IMC.memcpy_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (stage_src Xz nZ) (CtrPre.TwinB.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes bsegs (mkCfg ms' mo') K.

Theorem arstage_sound_of_leaf : arstage_leaf ->
  forall pc, to_Z pc = SYM -> contract_sound bsegs OPS MP PB (arstage_c ReadC.TwinB.ReadC.CFG_ASAN pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc arstage_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = SYM) by (rewrite Hspc; exact Hpc).
  destruct (arstage_apply_shape st sts Happ)
    as (r & hargs & wnl & st1 & kb & X & off & n' & wlen & rb & PRE & G11 & SO & F3 & CNT & FZ & WL & OT & FB & CB & PFX & LO0 & RW & EQoff & EQn & LEX & LEn & POSn & PKb & ->).
  destruct (CtrPre.TwinB.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs. pose proof atop_range as ATR.
  set (R := ms_regs ms) in *. set (m := ms_mem ms) in *.
  set (Db := bv_unsigned (ev E kb)) in *. set (Xz := bv_unsigned (den E X)) in *. set (nsv := getr st X12) in *.
  set (nZ := bv_unsigned (den E nsv)) in *. set (wlenZ := bv_unsigned (den E wlen)) in *.
  pose proof (bv_unsigned_in_range 64 (den E X)) as XR. change (bv_modulus 64) with (2 ^ 64) in XR. fold Xz in XR.
  pose proof (bv_unsigned_in_range 64 (den E nsv)) as NR. change (bv_modulus 64) with (2 ^ 64) in NR. fold nZ in NR.
  pose proof (bv_unsigned_in_range 64 (den E wlen)) as WLR. change (bv_modulus 64) with (2 ^ 64) in WLR. fold wlenZ in WLR.

  apply (HeapCtr.TwinB.known_leu_sound E _ _ _ Hfs) in LEX. fold Xz wlenZ in LEX.
  apply (HeapCtr.TwinB.known_leu_sound E _ _ _ Hfs) in LEn. rewrite den_sv_alu in LEn. cbn [alu64 alu] in LEn. rewrite bv_sub_unsigned in LEn. fold nZ Xz wlenZ in LEn.
  assert (SUM : Xz + nZ <= wlenZ).
  { unfold bv_wrap in LEn. change (bv_modulus 64) with (2 ^ 64) in LEn. rewrite Z.mod_small in LEn; lia. }
  apply (HeapCtr.TwinB.known_ltu_sound E _ _ _ Hfs) in POSn. cbn [den] in POSn. rewrite wbv_unsigned, wzero_ok in POSn. fold nZ in POSn.
  pose proof (HeapCtr.TwinB.known_eq_sound E _ _ _ Hfs EQoff) as Eoff. pose proof (HeapCtr.TwinB.known_eq_sound E _ _ _ Hfs EQn) as En.

  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.TwinB.find_op_In _ _ _ F3)) as H3. cbn [op_id op_args map] in H3.
  pose proof (OPS_holds_rstage _ _ _ H3) as RSV. cbn [rstage_holds_v] in RSV. rewrite Eoff, En in RSV. fold Xz nZ in RSV.
  destruct RSV as (FLEN & N64K & BY3).

  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.TwinB.find_op_In _ _ _ FZ)) as HZ. cbn [op_id op_args map] in HZ.
  pose proof (OPS_holds_zsh _ _ HZ) as ZSH.

  assert (KT : W64.weqb CtrLib.K_BLOCK ActrA.K_TWIN = false) by reflexivity.
  destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw kb wlen CtrLib.K_BLOCK Xz (Xz + nZ) CF WL KT
              ltac:(vm_compute; congruence) ltac:(vm_compute; congruence) ltac:(vm_compute; split; [discriminate| reflexivity]) ltac:(lia) ltac:(lia) ltac:(fold wlenZ; lia)) as (p & Ab & nb & HINB & BA1 & BA2).
  pose proof (W_PAT E st ms mo r hargs wnl L RNG sta LBa aw kb wlen CtrLib.K_BLOCK p Ab nb HS CF AH WL KT ltac:(vm_compute; congruence) ltac:(vm_compute; congruence) PKb Xz (Xz + nZ) ltac:(lia) ltac:(lia) ltac:(fold wlenZ; lia) HINB BA1 BA2) as PAT_p.
  fold Db in BA1, BA2.
  destruct (block_range_facts AI L RNG sta LBa m p Ab nb (Db + Xz) nZ AH HINB PAT_p BA1 ltac:(lia) ltac:(lia))
    as ((junk & DST) & APB0 & UNP0 & LOWA & HIA & RNGD & RLOd & RHId & HULLd & WRHd & RNGHd).

  set (src := stage_src Xz nZ).
  assert (LSRC : length src = Z.to_nat nZ) by apply stage_src_len.
  assert (SRCB : ALib.Mem.bytes_at bsegs m STAGE src).
  { apply bytes_at_of_rb; [unfold STAGE; lia| rewrite LSRC, Z2Nat.id by lia; unfold STAGE; lia|]. rewrite LSRC, Z2Nat.id by lia.
    intros j Hj. unfold m. rewrite (BY3 j Hj). unfold src, stage_src. rewrite nth_error_map, nth_error_seq.
    destruct (Nat.ltb_spec (Z.to_nat j) (Z.to_nat nZ)); [| lia]. cbn [option_map]. f_equal. f_equal. lia. }

  assert (EA0 : bv_unsigned (AP.getr R (reg_of_r5 X10)) = Db + Xz).
  { unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10), (MemcpyCtr.TwinB.sym_offset_sound E (s_regs st) _ kb X SO).
    rewrite bv_add_unsigned. fold Db Xz. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). unfold AIMG_HI in *. lia. }
  assert (EA1 : bv_unsigned (AP.getr R (reg_of_r5 X11)) = STAGE).
  { unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X11), G11. cbn [den]. rewrite wbv_unsigned, wlit_ok. reflexivity. }
  assert (EA2 : bv_unsigned (AP.getr R (reg_of_r5 X12)) = nZ).
  { unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X12). reflexivity. }
  assert (EA0' : bv_unsigned (AP.getr R 10) = Db + Xz) by exact EA0. assert (EA1' : bv_unsigned (AP.getr R 11) = STAGE) by exact EA1.
  assert (EA2' : bv_unsigned (AP.getr R 12) = nZ) by exact EA2.
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG. pose proof (ACCT_rng_aimg_sh _ _ _ _ _ _ AC) as RISH.
  assert (SH1 : shad RLO2 = ZSH_LO) by (vm_compute; reflexivity). assert (SH2 : shad RHI2 = ZSH_HI) by (vm_compute; reflexivity).
  assert (EV : evtF bsegs RNG
            (IMC.memcpy_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) src (CtrPre.TwinB.sp_lo E st) m)
            (MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                (ms_fregs ms) (Z_to_bv 64 SYM) (ms_fcsr ms) None m (seg_rom bsegs))).
  { unfold artcells in RT. decompose [and] RT. clear RT.
    eapply (WALK RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_fregs ms) (ms_fcsr ms) m
              (CtrPre.TwinB.sp_lo E st) src junk RLO2 RHI2 RLOd RHId).
    all: rewrite ?EA0', ?EA1', ?EA2'.
    all: try lazymatch goal with
         | |- ALib.Mem.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact ST
         | |- ALib.Mem.bytes_at _ _ _ _ => exact SRCB
         | |- length _ = _ => exact LSRC
         | |- ALib.Step.rw_cells _ _ _ [CB _ _] => exact DST
         | |- ALib.Step.rw_cells _ _ _ _ => assumption
         | |- Shadow.unpoisoned _ STAGE _ => apply (zsh_unpoisoned _ _ ZSH); lia
         | |- Shadow.unpoisoned _ _ _ => exact UNP0
         | |- Shadow.app_blk STAGE _ => unfold Shadow.app_blk, Shadow.KLOW, Shadow.KHIGH, Shadow.KEND, STAGE; lia
         | |- Shadow.app_blk _ _ => exact APB0
         | |- ALib.Mem.wr_at _ _ (shad RLO2) _ => exact (zsh_wr _ ZSH)
         | |- ALib.Mem.wr_at _ _ _ _ => exact WRHd
         | |- rng_aimg _ => exact RIMG
         | |- rng _ (shad RLO2) _ => rewrite SH1, SH2; eapply rng_sub'; [exact RISH| unfold ZSH_LO, ZSH_HI; lia]
         | |- rng _ STAGE _ => eapply rng_sub'; [exact RIMG| unfold STAGE; lia]
         | |- rng _ _ _ => first [exact RNGHd | exact RNGD | exact RSTK]
         | |- _ <= _ /\ _ => first [exact HULLd | unfold STAGE, RLO2, RHI2, Shadow.KEND; repeat split; lia]
         end.
    all: try (unfold STAGE, Shadow.KHIGH, AIMG_HI in *; lia).
    all: match goal with |- ?G => idtac "REMW" G end. }
  rewrite Ems, HPC. apply (GlueA.TwinB.realizes_to_mkRA bsegs).
  eapply (implS_twfS_realizes_silent bsegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ IMC.memcpy_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) src (CtrPre.TwinB.sp_lo E st) m ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    assert (NB : 0 < nZ <= 65536) by lia.
    exact (LEAF st K E ms mo r hargs wnl st1 kb X off n' wlen rb L RNG sta LBa aw HS HPB HK PRE SO F3 CNT WL OT FB CB PFX LO0 RW EQoff EQn CP FS CF AH MI BOT LO SPT
             NB SUM LOWA HIA FLEN EA0 EA1 EA2 ms' mo' HQ HMP' HMI' OTH ACP).
Qed.
End Sound.
End TwinB.
