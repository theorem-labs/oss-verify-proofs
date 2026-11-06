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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs DefsA DefsB DefsM.
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import StackSh RangeC BlobC PayloadC MemsetPre RangePre MemcpySound RstageSound BlobSound.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX ActrA PayloadC.
Module IMC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.I_memcpy.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition payload_post (st st1 : sstate) (r kp : int) : sstate :=
  let st2 := setr (clobber st1) X10 (getr st X10) in
  setpc (setregs st2 (IMap.add kp (Region 0%uint63 (getr st X12) true (BGBlob 5%uint63 0%uint63) IMap.empty) (s_regs st2))) r.

Lemma apayload_apply_shape : forall st sts, apayload_apply st = Some sts ->
  exists r hargs wnl st1 kp kb OFF rp rb wlenp wlenb,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ getr st X10 = VP kp wzero
    /\ CtrM.dst_offset (s_regs st) (getr st X11) = Some (kb, OFF) /\ kb <> kp
    /\ IMap.find kp (s_regs st) = Some rp /\ IMap.find kb (s_regs st) = Some rb
    /\ CtrA.win_lookup wnl kp = Some (wlenp, CtrLib.K_BLOCK) /\ CtrA.win_lookup wnl kb = Some (wlenb, CtrLib.K_BLOCK)
    /\ others_ok wnl kp kb = true
    /\ rg_cells rp = IMap.Leaf /\ rg_cells rb = IMap.Leaf /\ rg_bg rb = BGBlob 4%uint63 0%uint63
    /\ rg_lo rb = 0%uint63 /\ rg_lo rp = 0%uint63 /\ rg_w rp = true
    /\ fact_lookup (s_facts st) (is_FEq OFF CtrM.B14) = true /\ fact_lookup (s_facts st) (is_FEq (getr st X12) CtrM.B13) = true
    /\ known_ltu (s_facts st) (VL wzero) (getr st X12) = true
    /\ known_leu (s_facts st) (getr st X12) (rg_hi rp) = true
    /\ known_leu (s_facts st) OFF (rg_hi rb) = true /\ known_leu (s_facts st) (getr st X12) (sv_alu ALU_SUB (rg_hi rb) OFF) = true
    /\ known_leu (s_facts st) (getr st X12) wlenp = true /\ known_leu (s_facts st) (rg_hi rb) wlenb = true
    /\ RangeC.pat_ok st wnl kp CtrLib.K_BLOCK = true /\ RangeC.pat_ok st wnl kb CtrLib.K_BLOCK = true
    /\ sts = [payload_post st st1 r kp].
Proof.
  intros st sts H. unfold apayload_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (getr st X10) as [|kp op| | | | | | | | |] eqn:G10; try discriminate H.
  destruct (CtrM.dst_offset (s_regs st) (getr st X11)) as [[kb OFF]|] eqn:DO; [|discriminate H].
  destruct (IMap.find kp (s_regs st)) as [rp|] eqn:FD; [|discriminate H].
  destruct (IMap.find kb (s_regs st)) as [rb|] eqn:FB; [|discriminate H].
  destruct (CtrA.win_lookup wnl kp) as [[wlenp kdp]|] eqn:WLp; [|discriminate H].
  destruct (CtrA.win_lookup wnl kb) as [[wlenb kdb]|] eqn:WLb; [|discriminate H].
  destruct (rg_cells rp) eqn:CBp; [|discriminate H]. destruct (rg_cells rb) eqn:CBb; [|discriminate H].
  destruct (rg_bg rb) as [| | | |j sh] eqn:BGb; try discriminate H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:PKC; [discriminate H|] end. apply negb_false_iff in PKC. apply andb_prop in PKC as [PKp PKb].
  cbv zeta in H. match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate H] end.
  repeat match type of CND with (_ && _)%bool = true => let Q := fresh "Q" in apply andb_prop in CND as [CND Q] end.
  apply weqb_eq in CND. subst op. apply negb_true_iff in Q15. apply Uint63.eqb_false_spec in Q15.
  apply weqb_eq in Q14. subst kdp. apply weqb_eq in Q13. subst kdb.
  apply Uint63.eqb_correct in Q11. subst j. apply Uint63.eqb_correct in Q10. subst sh.
  apply Uint63.eqb_correct in Q9. apply Uint63.eqb_correct in Q8.
  injection H as <-.
  exists r, hargs, wnl, st1, kp, kb, OFF, rp, rb, wlenp, wlenb. repeat (split; [reflexivity || assumption|]).
  unfold payload_post. rewrite G10. reflexivity.
Qed.

Definition pay_src (E : env) (off n : Z) : list byte := map (fun i => nth (Z.to_nat off + i)%nat (eb E 4%uint63) (Z_to_bv 8 0)) (seq 0 (Z.to_nat n)).
Lemma pay_src_len : forall E off n, length (pay_src E off n) = Z.to_nat n.
Proof. intros. unfold pay_src. rewrite length_map, length_seq. reflexivity. Qed.

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
Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Hypothesis W_PAT : w_pat_ev_stmt AI ACCT UNIV Cw OPS.
Variable OTHER : Model -> Model -> Prop.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Hypothesis PB5 : forall E, PB (eb E) -> forall i, 0 <= i < bv_unsigned (den E CtrM.B13) ->
  nth (Z.to_nat (bv_unsigned (den E CtrM.B14) + i)) (eb E 4%uint63) (Z_to_bv 8 0) = nth (Z.to_nat i) (eb E 5%uint63) (Z_to_bv 8 0).
Variable NMAXt : nat.
Variable SYM : Z.
Hypothesis WALK : memcpy_walk_stmt SYM.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).

Definition apayload_leaf : Prop :=
  forall st (K : TSet) E ms mo r hargs wnl st1 kp kb rp wlenp wlenb (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) (offZ : Z),
  st_ok asegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' [payload_post st st1 r kp] -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok asegs OPS E' st' ms' mo' ->
               realizes asegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) -> getr st X10 = VP kp wzero -> kb <> kp ->
  IMap.find kp (s_regs st) = Some rp ->
  CtrA.win_lookup wnl kp = Some (wlenp, CtrLib.K_BLOCK) -> CtrA.win_lookup wnl kb = Some (wlenb, CtrLib.K_BLOCK) -> others_ok wnl kp kb = true ->
  rg_cells rp = IMap.Leaf -> rg_lo rp = 0%uint63 -> rg_w rp = true ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ALib.Mem.mem_inv asegs (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  let Dd := bv_unsigned (ev E kp) in let Db := bv_unsigned (ev E kb) in let nZ := bv_unsigned (den E (getr st X12)) in
  0 < nZ -> nZ <= bv_unsigned (den E wlenp) -> AIMG_HI <= Dd -> Dd + nZ <= ATOP -> Db <> Dd ->
  bv_unsigned (AP.getr R 10) = Dd -> bv_unsigned (AP.getr R 12) = nZ ->
  (forall o, 0 <= o < nZ -> nth (Z.to_nat o) (pay_src E offZ nZ) (Z_to_bv 8 0) = nth (Z.to_nat o) (eb E 5%uint63) (Z_to_bv 8 0)) ->
  forall ms' mo',
  IMC.memcpy_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (pay_src E offZ nZ) (CtrPre.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes asegs (mkCfg ms' mo') K.

Theorem apayload_sound_of_leaf : apayload_leaf ->
  forall pc, to_Z pc = SYM -> contract_sound asegs OPS MP PB (apayload_c pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc apayload_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = SYM) by (rewrite Hspc; exact Hpc).
  destruct (apayload_apply_shape st sts Happ)
    as (r & hargs & wnl & st1 & kp & kb & OFF & rp & rb & wlenp & wlenb & PRE & G10 & DO & NKK & FD & FB & WLp & WLb & OT & CBp & CBb & BGb & LOb & LOp & RWp
        & F14 & F13 & POSn & LEp & LEo & LEs & LEWp & LEWb & PKp & PKb & ->).
  destruct (CtrPre.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs. pose proof atop_range as ATR.
  set (R := ms_regs ms) in *. set (m := ms_mem ms) in *.
  set (Dd := bv_unsigned (ev E kp)) in *. set (Db := bv_unsigned (ev E kb)) in *. set (nsv := getr st X12) in *.
  set (nZ := bv_unsigned (den E nsv)) in *. set (offZ := bv_unsigned (den E OFF)) in *.
  apply (HeapCtr.known_ltu_sound E _ _ _ Hfs) in POSn. cbn [den] in POSn. rewrite wbv_unsigned, wzero_ok in POSn. fold nZ in POSn.
  apply (HeapCtr.known_leu_sound E _ _ _ Hfs) in LEp. fold nZ in LEp.
  apply (HeapCtr.known_leu_sound E _ _ _ Hfs) in LEo. fold offZ in LEo. change (bv_unsigned (den E (rg_hi rb))) with (hiZ E rb) in LEo.
  apply (HeapCtr.known_leu_sound E _ _ _ Hfs) in LEs. fold nZ in LEs. rewrite ValP.den_sv_alu in LEs. cbn [alu64 alu] in LEs. rewrite bv_sub_unsigned in LEs.
  fold offZ in LEs. change (bv_unsigned (den E (rg_hi rb))) with (hiZ E rb) in LEs.
  apply (HeapCtr.known_leu_sound E _ _ _ Hfs) in LEWp. fold nZ in LEWp.
  apply (HeapCtr.known_leu_sound E _ _ _ Hfs) in LEWb. change (bv_unsigned (den E (rg_hi rb))) with (hiZ E rb) in LEWb.
  pose proof (bv_unsigned_in_range 64 (den E (rg_hi rb))) as HBR. change (bv_modulus 64) with (2 ^ 64) in HBR. change (bv_unsigned (den E (rg_hi rb))) with (hiZ E rb) in HBR.
  pose proof (bv_unsigned_in_range 64 (den E OFF)) as ORr. change (bv_modulus 64) with (2 ^ 64) in ORr. fold offZ in ORr.
  assert (SUM : offZ + nZ <= hiZ E rb).
  { rewrite bv_wrap_small in LEs by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia). lia. }

  pose proof (proj2 (ValP.syntactic_eq_sound E _ Hfs OFF CtrM.B14) F14) as E14. pose proof (proj2 (ValP.syntactic_eq_sound E _ Hfs nsv CtrM.B13) F13) as E13.

  assert (KT : W64.weqb CtrLib.K_BLOCK ActrA.K_TWIN = false) by reflexivity.
  destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw kp wlenp CtrLib.K_BLOCK 0 nZ CF WLp KT
              ltac:(vm_compute; congruence) ltac:(vm_compute; congruence) ltac:(vm_compute; split; [discriminate| reflexivity]) ltac:(lia) ltac:(lia) LEWp) as (pd & Abd & nbd & HINd & BAd1 & BAd2).
  pose proof (W_PAT E st ms mo r hargs wnl L RNG sta LBa aw kp wlenp CtrLib.K_BLOCK pd Abd nbd HS CF AH WLp KT ltac:(vm_compute; congruence) ltac:(vm_compute; congruence) PKp 0 nZ ltac:(lia) ltac:(lia) LEWp HINd BAd1 BAd2) as PAT_pd.
  destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw kb wlenb CtrLib.K_BLOCK offZ (offZ + nZ) CF WLb KT
              ltac:(vm_compute; congruence) ltac:(vm_compute; congruence) ltac:(vm_compute; split; [discriminate| reflexivity]) ltac:(lia) ltac:(lia) ltac:(lia)) as (ps & Abs & nbs & HINs & BAs1 & BAs2).
  pose proof (W_PAT E st ms mo r hargs wnl L RNG sta LBa aw kb wlenb CtrLib.K_BLOCK ps Abs nbs HS CF AH WLb KT ltac:(vm_compute; congruence) ltac:(vm_compute; congruence) PKb offZ (offZ + nZ) ltac:(lia) ltac:(lia) ltac:(lia) HINs BAs1 BAs2) as PAT_ps.
  fold Dd in BAd1, BAd2. fold Db in BAs1, BAs2.
  set (S := Db + offZ) in *.
  destruct (block_range_facts AI L RNG sta LBa m pd Abd nbd Dd nZ AH HINd PAT_pd ltac:(lia) ltac:(lia) ltac:(lia))
    as ((junk & DST) & APB0 & UNP0 & LOWd & HId & RNGD & RLOd & RHId & HULLd & WRHd & RNGHd).
  destruct (block_range_facts AI L RNG sta LBa m ps Abs nbs S nZ AH HINs PAT_ps ltac:(unfold S; lia) ltac:(unfold S; lia) ltac:(lia))
    as (_ & APB1 & UNP1 & LOWs & HIs & RNGS & RLOs & RHIs & HULLs & WRHs & RNGHs).
  assert (N40 : nZ <= 2 ^ 40).
  { destruct (heap_block_facts AI _ _ _ _ _ (HB pd Abd nbd) AH HINd ltac:(exists pd; reflexivity)) as (NRb & _). cbn [ab_size] in NRb.
    unfold AREQMAX in NRb. lia. }

  pose proof (so_reg _ _ _ _ _ _ HS kb rb FB) as ROb.
  assert (Kb0 : PrimInt63.eqb kb 0%uint63 = false).
  { destruct CF as (LB0 & ks0 & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255 & NW & _).
    destruct (HeapCtrB.nonstack_windows_In E nn rest wnl kb wlenb CtrLib.K_BLOCK NW (HeapCtrB.win_lookup_In _ _ _ _ WLb)) as (K0 & _). apply Uint63.eqb_false_spec. exact K0. }
  assert (Kp0 : PrimInt63.eqb kp 0%uint63 = false).
  { destruct CF as (LB0 & ks0 & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255 & NW & _).
    destruct (HeapCtrB.nonstack_windows_In E nn rest wnl kp wlenp CtrLib.K_BLOCK NW (HeapCtrB.win_lookup_In _ _ _ _ WLp)) as (K0 & _). apply Uint63.eqb_false_spec. exact K0. }
  assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity.
  set (src := pay_src E offZ nZ).
  assert (LSRC : length src = Z.to_nat nZ) by apply pay_src_len.
  assert (SRCB : ALib.Mem.bytes_at asegs m S src).
  { apply bytes_at_of_rb; [unfold AIMG_HI in LOWs; lia| rewrite LSRC, Z2Nat.id by lia; lia|]. rewrite LSRC, Z2Nat.id by lia.
    intros o Ho.
    pose proof (ro_bg _ _ _ _ _ _ ROb (offZ + o) ltac:(intros _; unfold loZ; rewrite LOb, KZ0; lia)
                  ltac:(intros X1; rewrite Kb0 in X1; discriminate X1) ltac:(intros g gr _ F; rewrite CBb in F; cbn in F; discriminate F)) as G.
    unfold bg_byte in G. rewrite BGb in G. change (to_Z 0%uint63) with 0 in G. rewrite Z.sub_0_r in G. fold Db in G. unfold m, S.
    replace (Db + offZ + o) with (Db + (offZ + o)) by lia. rewrite G.
    unfold src, pay_src. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec (Z.to_nat o) (Z.to_nat nZ)); [| lia]. cbn [option_map]. f_equal. f_equal. lia. }

  assert (SRC5 : forall o, 0 <= o < nZ -> nth (Z.to_nat o) src (Z_to_bv 8 0) = nth (Z.to_nat o) (eb E 5%uint63) (Z_to_bv 8 0)).
  { intros o Ho. unfold src, pay_src. rewrite StrReg.nth_map_seq by lia.
    rewrite <- (PB5 E HPB o) by (rewrite <- E13; fold nZ; lia). f_equal. rewrite <- E14. fold offZ. lia. }

  pose proof (so_reg _ _ _ _ _ _ HS kp rp FD) as ROp.
  assert (NEA : Db <> Dd).
  { intros EQA. apply (so_disj _ _ _ _ _ _ HS kp rp kb rb FD FB ltac:(intros Q; apply NKK; symmetry; exact Q) Kp0 Kb0 (or_introl RWp) Dd).
    unfold loZ. rewrite LOp, LOb, KZ0. fold Dd Db. rewrite EQA. change (bv_unsigned (den E (rg_hi rp))) with (hiZ E rp) in LEp. lia. }
  assert (DISJ : S + nZ <= Dd \/ Dd + nZ <= S).
  { destruct CF as (LB0 & ks0 & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                    & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
    pose proof (aw_real_holds AI ACCT UNIV _ _ _ _ _ ARW) as AWH0.
    assert (INd : In (Dd, bv_unsigned (den E wlenp)) LB0).
    { destruct (HeapCtrB.nonstack_windows_In E nn rest wnl kp wlenp CtrLib.K_BLOCK NW (HeapCtrB.win_lookup_In _ _ _ _ WLp)) as (_ & _ & _ & INW).
      pose proof (proj1 (Forall_forall _ _) WF _ INW) as (_ & _ & _ & [[KS0 _]|[[KB B]|[KS2 _]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *;
        [exfalso; vm_compute in KS0; discriminate KS0| exact B| exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS2; unfold K_SUB in KS2; lia]. }
    assert (INs : In (Db, bv_unsigned (den E wlenb)) LB0).
    { destruct (HeapCtrB.nonstack_windows_In E nn rest wnl kb wlenb CtrLib.K_BLOCK NW (HeapCtrB.win_lookup_In _ _ _ _ WLb)) as (_ & _ & _ & INW).
      pose proof (proj1 (Forall_forall _ _) WF _ INW) as (_ & _ & _ & [[KS0 _]|[[KB B]|[KS2 _]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *;
        [exfalso; vm_compute in KS0; discriminate KS0| exact B| exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS2; unfold K_SUB in KS2; lia]. }
    destruct (Z_le_gt_dec (S + nZ) Dd) as [Q1|Q1]; [left; exact Q1|]. destruct (Z_le_gt_dec (Dd + nZ) S) as [Q2|Q2]; [right; exact Q2|].
    exfalso. apply (aw_blocks_disj_asan AI ACCT UNIV AI_fake _ LB0 _ _ (Dd, bv_unsigned (den E wlenp)) (Db, bv_unsigned (den E wlenb)) (Z.max Dd S) AWH0 INd INs);
      [cbn [fst]; intros Q; apply NEA; symmetry; exact Q| |]; unfold in_iv; cbn [fst snd]; unfold S in *; lia. }

  assert (EA0 : bv_unsigned (AP.getr R (reg_of_r5 X10)) = Dd).
  { unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X10), G10, HeapCtr.den_VPz. reflexivity. }
  assert (EA1 : bv_unsigned (AP.getr R (reg_of_r5 X11)) = S).
  { unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X11), (MemcpyCtr.dst_offset_sound E (s_regs st) _ kb OFF DO).
    rewrite bv_add_unsigned. fold Db offZ. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). unfold S, AIMG_HI in *. lia. }
  assert (EA2 : bv_unsigned (AP.getr R (reg_of_r5 X12)) = nZ).
  { unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X12). reflexivity. }
  assert (EA0' : bv_unsigned (AP.getr R 10) = Dd) by exact EA0. assert (EA1' : bv_unsigned (AP.getr R 11) = S) by exact EA1.
  assert (EA2' : bv_unsigned (AP.getr R 12) = nZ) by exact EA2.
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG.
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
              (CtrPre.sp_lo E st) src junk RLOs RHIs RLOd RHId).
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
         | |- ALib.Mem.wr_at _ _ _ _ => first [exact WRHs | exact WRHd]
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ _ => first [exact RNGHs | exact RNGHd | exact RNGS | exact RNGD | exact RSTK]
         | |- _ <= _ /\ _ => first [exact HULLs | exact HULLd]
         end.
    all: try (unfold Shadow.KHIGH, AIMG_HI in *; lia).
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
    exact (LEAF st K E ms mo r hargs wnl st1 kp kb rp wlenp wlenb L RNG sta LBa aw offZ HS HPB HK PRE G10 NKK FD WLp WLb OT CBp LOp RWp CP FS CF AH MI BOT LO SPT
             POSn LEWp LOWd HId NEA EA0 EA2 SRC5 ms' mo' HQ HMP' HMI' OTH ACP).
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
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsB OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsM.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import UnreggSound.TwinB.
Import StackSh.TwinB RangeC.TwinB BlobC.TwinB PayloadC.TwinB MemsetPre.TwinB RangePre.TwinB MemcpySound.TwinB RstageSound.TwinB BlobSound.TwinB.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX ActrA PayloadC.TwinB.PayloadC.
Module IMC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.TwinB.I_memcpy.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition payload_post (st st1 : sstate) (r kp : int) : sstate :=
  let st2 := setr (clobber st1) X10 (getr st X10) in
  setpc (setregs st2 (IMap.add kp (Region 0%uint63 (getr st X12) true (BGBlob 5%uint63 0%uint63) IMap.empty) (s_regs st2))) r.

Lemma apayload_apply_shape : forall st sts, apayload_apply st = Some sts ->
  exists r hargs wnl st1 kp kb OFF rp rb wlenp wlenb,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ getr st X10 = VP kp wzero
    /\ CtrM.dst_offset (s_regs st) (getr st X11) = Some (kb, OFF) /\ kb <> kp
    /\ IMap.find kp (s_regs st) = Some rp /\ IMap.find kb (s_regs st) = Some rb
    /\ CtrA.win_lookup wnl kp = Some (wlenp, CtrLib.K_BLOCK) /\ CtrA.win_lookup wnl kb = Some (wlenb, CtrLib.K_BLOCK)
    /\ others_ok wnl kp kb = true
    /\ rg_cells rp = IMap.Leaf /\ rg_cells rb = IMap.Leaf /\ rg_bg rb = BGBlob 4%uint63 0%uint63
    /\ rg_lo rb = 0%uint63 /\ rg_lo rp = 0%uint63 /\ rg_w rp = true
    /\ fact_lookup (s_facts st) (is_FEq OFF CtrM.B14) = true /\ fact_lookup (s_facts st) (is_FEq (getr st X12) CtrM.B13) = true
    /\ known_ltu (s_facts st) (VL wzero) (getr st X12) = true
    /\ known_leu (s_facts st) (getr st X12) (rg_hi rp) = true
    /\ known_leu (s_facts st) OFF (rg_hi rb) = true /\ known_leu (s_facts st) (getr st X12) (sv_alu ALU_SUB (rg_hi rb) OFF) = true
    /\ known_leu (s_facts st) (getr st X12) wlenp = true /\ known_leu (s_facts st) (rg_hi rb) wlenb = true
    /\ RangeC.TwinB.RangeC.pat_ok st wnl kp CtrLib.K_BLOCK = true /\ RangeC.TwinB.RangeC.pat_ok st wnl kb CtrLib.K_BLOCK = true
    /\ sts = [payload_post st st1 r kp].
Proof.
  intros st sts H. unfold apayload_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (getr st X10) as [|kp op| | | | | | | | |] eqn:G10; try discriminate H.
  destruct (CtrM.dst_offset (s_regs st) (getr st X11)) as [[kb OFF]|] eqn:DO; [|discriminate H].
  destruct (IMap.find kp (s_regs st)) as [rp|] eqn:FD; [|discriminate H].
  destruct (IMap.find kb (s_regs st)) as [rb|] eqn:FB; [|discriminate H].
  destruct (CtrA.win_lookup wnl kp) as [[wlenp kdp]|] eqn:WLp; [|discriminate H].
  destruct (CtrA.win_lookup wnl kb) as [[wlenb kdb]|] eqn:WLb; [|discriminate H].
  destruct (rg_cells rp) eqn:CBp; [|discriminate H]. destruct (rg_cells rb) eqn:CBb; [|discriminate H].
  destruct (rg_bg rb) as [| | | |j sh] eqn:BGb; try discriminate H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:PKC; [discriminate H|] end. apply negb_false_iff in PKC. apply andb_prop in PKC as [PKp PKb].
  cbv zeta in H. match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate H] end.
  repeat match type of CND with (_ && _)%bool = true => let Q := fresh "Q" in apply andb_prop in CND as [CND Q] end.
  apply weqb_eq in CND. subst op. apply negb_true_iff in Q15. apply Uint63.eqb_false_spec in Q15.
  apply weqb_eq in Q14. subst kdp. apply weqb_eq in Q13. subst kdb.
  apply Uint63.eqb_correct in Q11. subst j. apply Uint63.eqb_correct in Q10. subst sh.
  apply Uint63.eqb_correct in Q9. apply Uint63.eqb_correct in Q8.
  injection H as <-.
  exists r, hargs, wnl, st1, kp, kb, OFF, rp, rb, wlenp, wlenb. repeat (split; [reflexivity || assumption|]).
  unfold payload_post. rewrite G10. reflexivity.
Qed.

Definition pay_src (E : env) (off n : Z) : list byte := map (fun i => nth (Z.to_nat off + i)%nat (eb E 4%uint63) (Z_to_bv 8 0)) (seq 0 (Z.to_nat n)).
Lemma pay_src_len : forall E off n, length (pay_src E off n) = Z.to_nat n.
Proof. intros. unfold pay_src. rewrite length_map, length_seq. reflexivity. Qed.

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
Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Hypothesis W_PAT : w_pat_ev_stmt AI ACCT UNIV Cw OPS.
Variable OTHER : Model -> Model -> Prop.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Hypothesis PB5 : forall E, PB (eb E) -> forall i, 0 <= i < bv_unsigned (den E CtrM.B13) ->
  nth (Z.to_nat (bv_unsigned (den E CtrM.B14) + i)) (eb E 4%uint63) (Z_to_bv 8 0) = nth (Z.to_nat i) (eb E 5%uint63) (Z_to_bv 8 0).
Variable NMAXt : nat.
Variable SYM : Z.
Hypothesis WALK : memcpy_walk_stmt SYM.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).

Definition apayload_leaf : Prop :=
  forall st (K : TSet) E ms mo r hargs wnl st1 kp kb rp wlenp wlenb (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) (offZ : Z),
  st_ok bsegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' [payload_post st st1 r kp] -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok bsegs OPS E' st' ms' mo' ->
               realizes bsegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) -> getr st X10 = VP kp wzero -> kb <> kp ->
  IMap.find kp (s_regs st) = Some rp ->
  CtrA.win_lookup wnl kp = Some (wlenp, CtrLib.K_BLOCK) -> CtrA.win_lookup wnl kb = Some (wlenb, CtrLib.K_BLOCK) -> others_ok wnl kp kb = true ->
  rg_cells rp = IMap.Leaf -> rg_lo rp = 0%uint63 -> rg_w rp = true ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ALib.Mem.mem_inv bsegs (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  let Dd := bv_unsigned (ev E kp) in let Db := bv_unsigned (ev E kb) in let nZ := bv_unsigned (den E (getr st X12)) in
  0 < nZ -> nZ <= bv_unsigned (den E wlenp) -> AIMG_HI <= Dd -> Dd + nZ <= ATOP -> Db <> Dd ->
  bv_unsigned (AP.getr R 10) = Dd -> bv_unsigned (AP.getr R 12) = nZ ->
  (forall o, 0 <= o < nZ -> nth (Z.to_nat o) (pay_src E offZ nZ) (Z_to_bv 8 0) = nth (Z.to_nat o) (eb E 5%uint63) (Z_to_bv 8 0)) ->
  forall ms' mo',
  IMC.memcpy_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (pay_src E offZ nZ) (CtrPre.TwinB.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes bsegs (mkCfg ms' mo') K.

Theorem apayload_sound_of_leaf : apayload_leaf ->
  forall pc, to_Z pc = SYM -> contract_sound bsegs OPS MP PB (apayload_c pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc apayload_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = SYM) by (rewrite Hspc; exact Hpc).
  destruct (apayload_apply_shape st sts Happ)
    as (r & hargs & wnl & st1 & kp & kb & OFF & rp & rb & wlenp & wlenb & PRE & G10 & DO & NKK & FD & FB & WLp & WLb & OT & CBp & CBb & BGb & LOb & LOp & RWp
        & F14 & F13 & POSn & LEp & LEo & LEs & LEWp & LEWb & PKp & PKb & ->).
  destruct (CtrPre.TwinB.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs. pose proof atop_range as ATR.
  set (R := ms_regs ms) in *. set (m := ms_mem ms) in *.
  set (Dd := bv_unsigned (ev E kp)) in *. set (Db := bv_unsigned (ev E kb)) in *. set (nsv := getr st X12) in *.
  set (nZ := bv_unsigned (den E nsv)) in *. set (offZ := bv_unsigned (den E OFF)) in *.
  apply (HeapCtr.TwinB.known_ltu_sound E _ _ _ Hfs) in POSn. cbn [den] in POSn. rewrite wbv_unsigned, wzero_ok in POSn. fold nZ in POSn.
  apply (HeapCtr.TwinB.known_leu_sound E _ _ _ Hfs) in LEp. fold nZ in LEp.
  apply (HeapCtr.TwinB.known_leu_sound E _ _ _ Hfs) in LEo. fold offZ in LEo. change (bv_unsigned (den E (rg_hi rb))) with (hiZ E rb) in LEo.
  apply (HeapCtr.TwinB.known_leu_sound E _ _ _ Hfs) in LEs. fold nZ in LEs. rewrite ValP.den_sv_alu in LEs. cbn [alu64 alu] in LEs. rewrite bv_sub_unsigned in LEs.
  fold offZ in LEs. change (bv_unsigned (den E (rg_hi rb))) with (hiZ E rb) in LEs.
  apply (HeapCtr.TwinB.known_leu_sound E _ _ _ Hfs) in LEWp. fold nZ in LEWp.
  apply (HeapCtr.TwinB.known_leu_sound E _ _ _ Hfs) in LEWb. change (bv_unsigned (den E (rg_hi rb))) with (hiZ E rb) in LEWb.
  pose proof (bv_unsigned_in_range 64 (den E (rg_hi rb))) as HBR. change (bv_modulus 64) with (2 ^ 64) in HBR. change (bv_unsigned (den E (rg_hi rb))) with (hiZ E rb) in HBR.
  pose proof (bv_unsigned_in_range 64 (den E OFF)) as ORr. change (bv_modulus 64) with (2 ^ 64) in ORr. fold offZ in ORr.
  assert (SUM : offZ + nZ <= hiZ E rb).
  { rewrite bv_wrap_small in LEs by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia). lia. }

  pose proof (proj2 (ValP.syntactic_eq_sound E _ Hfs OFF CtrM.B14) F14) as E14. pose proof (proj2 (ValP.syntactic_eq_sound E _ Hfs nsv CtrM.B13) F13) as E13.

  assert (KT : W64.weqb CtrLib.K_BLOCK ActrA.K_TWIN = false) by reflexivity.
  destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw kp wlenp CtrLib.K_BLOCK 0 nZ CF WLp KT
              ltac:(vm_compute; congruence) ltac:(vm_compute; congruence) ltac:(vm_compute; split; [discriminate| reflexivity]) ltac:(lia) ltac:(lia) LEWp) as (pd & Abd & nbd & HINd & BAd1 & BAd2).
  pose proof (W_PAT E st ms mo r hargs wnl L RNG sta LBa aw kp wlenp CtrLib.K_BLOCK pd Abd nbd HS CF AH WLp KT ltac:(vm_compute; congruence) ltac:(vm_compute; congruence) PKp 0 nZ ltac:(lia) ltac:(lia) LEWp HINd BAd1 BAd2) as PAT_pd.
  destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw kb wlenb CtrLib.K_BLOCK offZ (offZ + nZ) CF WLb KT
              ltac:(vm_compute; congruence) ltac:(vm_compute; congruence) ltac:(vm_compute; split; [discriminate| reflexivity]) ltac:(lia) ltac:(lia) ltac:(lia)) as (ps & Abs & nbs & HINs & BAs1 & BAs2).
  pose proof (W_PAT E st ms mo r hargs wnl L RNG sta LBa aw kb wlenb CtrLib.K_BLOCK ps Abs nbs HS CF AH WLb KT ltac:(vm_compute; congruence) ltac:(vm_compute; congruence) PKb offZ (offZ + nZ) ltac:(lia) ltac:(lia) ltac:(lia) HINs BAs1 BAs2) as PAT_ps.
  fold Dd in BAd1, BAd2. fold Db in BAs1, BAs2.
  set (S := Db + offZ) in *.
  destruct (block_range_facts AI L RNG sta LBa m pd Abd nbd Dd nZ AH HINd PAT_pd ltac:(lia) ltac:(lia) ltac:(lia))
    as ((junk & DST) & APB0 & UNP0 & LOWd & HId & RNGD & RLOd & RHId & HULLd & WRHd & RNGHd).
  destruct (block_range_facts AI L RNG sta LBa m ps Abs nbs S nZ AH HINs PAT_ps ltac:(unfold S; lia) ltac:(unfold S; lia) ltac:(lia))
    as (_ & APB1 & UNP1 & LOWs & HIs & RNGS & RLOs & RHIs & HULLs & WRHs & RNGHs).
  assert (N40 : nZ <= 2 ^ 40).
  { destruct (heap_block_facts AI _ _ _ _ _ (HB pd Abd nbd) AH HINd ltac:(exists pd; reflexivity)) as (NRb & _). cbn [ab_size] in NRb.
    unfold AREQMAX in NRb. lia. }

  pose proof (so_reg _ _ _ _ _ _ HS kb rb FB) as ROb.
  assert (Kb0 : PrimInt63.eqb kb 0%uint63 = false).
  { destruct CF as (LB0 & ks0 & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255 & NW & _).
    destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl kb wlenb CtrLib.K_BLOCK NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLb)) as (K0 & _). apply Uint63.eqb_false_spec. exact K0. }
  assert (Kp0 : PrimInt63.eqb kp 0%uint63 = false).
  { destruct CF as (LB0 & ks0 & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255 & NW & _).
    destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl kp wlenp CtrLib.K_BLOCK NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLp)) as (K0 & _). apply Uint63.eqb_false_spec. exact K0. }
  assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity.
  set (src := pay_src E offZ nZ).
  assert (LSRC : length src = Z.to_nat nZ) by apply pay_src_len.
  assert (SRCB : ALib.Mem.bytes_at bsegs m S src).
  { apply bytes_at_of_rb; [unfold AIMG_HI in LOWs; lia| rewrite LSRC, Z2Nat.id by lia; lia|]. rewrite LSRC, Z2Nat.id by lia.
    intros o Ho.
    pose proof (ro_bg _ _ _ _ _ _ ROb (offZ + o) ltac:(intros _; unfold loZ; rewrite LOb, KZ0; lia)
                  ltac:(intros X1; rewrite Kb0 in X1; discriminate X1) ltac:(intros g gr _ F; rewrite CBb in F; cbn in F; discriminate F)) as G.
    unfold bg_byte in G. rewrite BGb in G. change (to_Z 0%uint63) with 0 in G. rewrite Z.sub_0_r in G. fold Db in G. unfold m, S.
    replace (Db + offZ + o) with (Db + (offZ + o)) by lia. rewrite G.
    unfold src, pay_src. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec (Z.to_nat o) (Z.to_nat nZ)); [| lia]. cbn [option_map]. f_equal. f_equal. lia. }

  assert (SRC5 : forall o, 0 <= o < nZ -> nth (Z.to_nat o) src (Z_to_bv 8 0) = nth (Z.to_nat o) (eb E 5%uint63) (Z_to_bv 8 0)).
  { intros o Ho. unfold src, pay_src. rewrite StrReg.TwinB.nth_map_seq by lia.
    rewrite <- (PB5 E HPB o) by (rewrite <- E13; fold nZ; lia). f_equal. rewrite <- E14. fold offZ. lia. }

  pose proof (so_reg _ _ _ _ _ _ HS kp rp FD) as ROp.
  assert (NEA : Db <> Dd).
  { intros EQA. apply (so_disj _ _ _ _ _ _ HS kp rp kb rb FD FB ltac:(intros Q; apply NKK; symmetry; exact Q) Kp0 Kb0 (or_introl RWp) Dd).
    unfold loZ. rewrite LOp, LOb, KZ0. fold Dd Db. rewrite EQA. change (bv_unsigned (den E (rg_hi rp))) with (hiZ E rp) in LEp. lia. }
  assert (DISJ : S + nZ <= Dd \/ Dd + nZ <= S).
  { destruct CF as (LB0 & ks0 & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                    & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
    pose proof (aw_real_holds AI ACCT UNIV _ _ _ _ _ ARW) as AWH0.
    assert (INd : In (Dd, bv_unsigned (den E wlenp)) LB0).
    { destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl kp wlenp CtrLib.K_BLOCK NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLp)) as (_ & _ & _ & INW).
      pose proof (proj1 (Forall_forall _ _) WF _ INW) as (_ & _ & _ & [[KS0 _]|[[KB B]|[KS2 _]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *;
        [exfalso; vm_compute in KS0; discriminate KS0| exact B| exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS2; unfold K_SUB in KS2; lia]. }
    assert (INs : In (Db, bv_unsigned (den E wlenb)) LB0).
    { destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl kb wlenb CtrLib.K_BLOCK NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLb)) as (_ & _ & _ & INW).
      pose proof (proj1 (Forall_forall _ _) WF _ INW) as (_ & _ & _ & [[KS0 _]|[[KB B]|[KS2 _]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *;
        [exfalso; vm_compute in KS0; discriminate KS0| exact B| exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS2; unfold K_SUB in KS2; lia]. }
    destruct (Z_le_gt_dec (S + nZ) Dd) as [Q1|Q1]; [left; exact Q1|]. destruct (Z_le_gt_dec (Dd + nZ) S) as [Q2|Q2]; [right; exact Q2|].
    exfalso. apply (aw_blocks_disj_asan AI ACCT UNIV AI_fake _ LB0 _ _ (Dd, bv_unsigned (den E wlenp)) (Db, bv_unsigned (den E wlenb)) (Z.max Dd S) AWH0 INd INs);
      [cbn [fst]; intros Q; apply NEA; symmetry; exact Q| |]; unfold in_iv; cbn [fst snd]; unfold S in *; lia. }

  assert (EA0 : bv_unsigned (AP.getr R (reg_of_r5 X10)) = Dd).
  { unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10), G10, HeapCtr.TwinB.den_VPz. reflexivity. }
  assert (EA1 : bv_unsigned (AP.getr R (reg_of_r5 X11)) = S).
  { unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X11), (MemcpyCtr.TwinB.dst_offset_sound E (s_regs st) _ kb OFF DO).
    rewrite bv_add_unsigned. fold Db offZ. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). unfold S, AIMG_HI in *. lia. }
  assert (EA2 : bv_unsigned (AP.getr R (reg_of_r5 X12)) = nZ).
  { unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X12). reflexivity. }
  assert (EA0' : bv_unsigned (AP.getr R 10) = Dd) by exact EA0. assert (EA1' : bv_unsigned (AP.getr R 11) = S) by exact EA1.
  assert (EA2' : bv_unsigned (AP.getr R 12) = nZ) by exact EA2.
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG.
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
              (CtrPre.TwinB.sp_lo E st) src junk RLOs RHIs RLOd RHId).
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
         | |- ALib.Mem.wr_at _ _ _ _ => first [exact WRHs | exact WRHd]
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ _ => first [exact RNGHs | exact RNGHd | exact RNGS | exact RNGD | exact RSTK]
         | |- _ <= _ /\ _ => first [exact HULLs | exact HULLd]
         end.
    all: try (unfold Shadow.KHIGH, AIMG_HI in *; lia).
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
    exact (LEAF st K E ms mo r hargs wnl st1 kp kb rp wlenp wlenb L RNG sta LBa aw offZ HS HPB HK PRE G10 NKK FD WLp WLb OT CBp LOp RWp CP FS CF AH MI BOT LO SPT
             POSn LEWp LOWd HId NEA EA0 EA2 SRC5 ms' mo' HQ HMP' HMI' OTH ACP).
Qed.
End Sound.
End TwinB.
