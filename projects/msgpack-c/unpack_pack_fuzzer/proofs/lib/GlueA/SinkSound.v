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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require KnownA.
Unset Nia Cache. Unset Nra Cache.

Definition sink_state (st st1 : sstate) (r : int) : sstate := setpc (setr (clobber st1) X10 (getr st X10)) r.

Lemma client_kind_inv : forall kd, client_kind kd = true ->
  weqb kd ActrA.K_TWIN = false /\ w2Z kd <> K_FRAMEz /\ w2Z kd <> K_FTWINz.
Proof.
  intros kd H. unfold client_kind in H. apply andb_prop in H as [H _]. repeat match type of H with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in H as [H X] end.
  apply negb_true_iff in Q1, Q0, Q. split; [exact Q1|].
  split; intros X; [rewrite weqb_eqb in Q0; apply Z.eqb_neq in Q0; apply Q0; rewrite X; reflexivity
                   | rewrite weqb_eqb in Q; apply Z.eqb_neq in Q; apply Q; rewrite X; reflexivity].
Qed.

Lemma client_kind_range : forall kd, client_kind kd = true -> K_BLOCK <= w2Z kd < K_GHOST.
Proof.
  intros kd H. unfold client_kind in H. apply andb_prop in H as [_ H].
  repeat (apply orb_prop in H as [H|H]); apply weqb_eq in H; subst kd; vm_compute; (split; [discriminate| reflexivity]).
Qed.

Lemma asink_apply_shape : forall st sts, asink_apply st = Some sts ->
  exists r hargs wnl st1 ka kd OFF ra rd wlena kda wlend kdd,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ getr st X10 = VP ka wzero
    /\ CtrA.sym_offset (s_regs st) (getr st X11) = Some (kd, OFF) /\ kd <> ka
    /\ IMap.find ka (s_regs st) = Some ra /\ IMap.find kd (s_regs st) = Some rd
    /\ CtrA.win_lookup wnl ka = Some (wlena, kda) /\ CtrA.win_lookup wnl kd = Some (wlend, kdd)
    /\ client_kind kda = true /\ client_kind kdd = true
    /\ rg_cells ra = IMap.Leaf /\ rg_bg ra = BGNone /\ rg_lo ra = 0%uint63 /\ rg_w ra = true /\ rg_lo rd = 0%uint63
    /\ KnownT.KnownT.known_leu_t (s_facts st) (getr st X12) (rg_hi ra) = true
    /\ KnownT.KnownT.known_leu_t (s_facts st) OFF (rg_hi rd) = true /\ KnownT.KnownT.known_leu_t (s_facts st) (getr st X12) (sv_alu ALU_SUB (rg_hi rd) OFF) = true
    /\ KnownT.KnownT.known_leu_t (s_facts st) (rg_hi ra) wlena = true /\ KnownT.KnownT.known_leu_t (s_facts st) (rg_hi rd) wlend = true
    /\ RangeC.pat_ok st wnl ka kda = true /\ RangeC.pat_ok st wnl kd kdd = true
    /\ sts = [sink_state st st1 r].
Proof.
  intros st sts H. unfold asink_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (getr st X10) as [|ka oa| | | | | | | | |] eqn:G10; try discriminate H.
  destruct (CtrA.sym_offset (s_regs st) (getr st X11)) as [[kd OFF]|] eqn:DO; [|discriminate H].
  destruct (IMap.find ka (s_regs st)) as [ra|] eqn:FA; [|discriminate H].
  destruct (IMap.find kd (s_regs st)) as [rd|] eqn:FD; [|discriminate H].
  destruct (rg_cells ra) eqn:CBa; [|discriminate H].
  destruct (CtrA.win_lookup wnl ka) as [[wlena kda]|] eqn:WLa; [|discriminate H].
  destruct (CtrA.win_lookup wnl kd) as [[wlend kdd]|] eqn:WLd; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:PKC; [discriminate H|] end. apply negb_false_iff in PKC. apply andb_prop in PKC as [PKa PKd].
  cbv zeta in H. match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate H] end.
  repeat match type of CND with (_ && _)%bool = true => let Q := fresh "Q" in apply andb_prop in CND as [CND Q] end.
  apply weqb_eq in CND. subst oa. apply negb_true_iff in Q6. apply Uint63.eqb_false_spec in Q6.
  apply Uint63.eqb_correct in Q9, Q7.
  assert (BGN : rg_bg ra = BGNone) by (unfold is_bgnone in Q10; destruct (rg_bg ra); try discriminate Q10; reflexivity).
  exists r, hargs, wnl, st1, ka, kd, OFF, ra, rd, wlena, kda, wlend, kdd. repeat (split; [reflexivity || assumption|]).
  unfold sink_state. congruence.
Qed.

Lemma st_ok_regs_ext {rc : runConstT} : forall OPS E pc rf ff rv R R' fs ops priv nx ms mo,
  IMap.bst R' -> (forall k, IMap.find k R' = IMap.find k R) ->
  st_ok asegs OPS E (SS pc rf ff rv R fs ops priv nx) ms mo -> st_ok asegs OPS E (SS pc rf ff rv R' fs ops priv nx) ms mo.
Proof.
  intros OPS E pc rf ff rv R R' fs ops priv nx ms mo BST EXT HS.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next] in *.
  assert (IB : forall a, in_based E R' a <-> in_based E R a).
  { intros a. unfold in_based. split; intros (k & r & F & X); exists k, r; (split; [| exact X]); [rewrite <- EXT| rewrite EXT]; exact F. }
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - intros k r F. rewrite EXT in F. exact (Preg k r F).
  - intros k1 r1 k2 r2 F1 F2. rewrite EXT in F1, F2. exact (Pdisj k1 r1 k2 r2 F1 F2).
  - intros r g gr c F. rewrite EXT in F. exact (Ppub r g gr c F).
  - apply Forall_forall. intros o Ho a FP. destruct (proj1 (Forall_forall _ _) Papart o Ho a FP) as [NB X]. split; [| exact X].
    intros B. apply NB. apply IB. exact B.
  - intros a [B|S]; apply Pcov; [left; apply IB; exact B| right; exact S].
Qed.

Lemma region_ok_claimless {rc : runConstT} : forall priv E (m m' : word -> option byte) k r,
  rg_cells r = IMap.Leaf -> rg_bg r = BGNone ->
  region_ok asegs priv E m k r ->
  (forall a, bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r -> rb asegs m' a <> None /\ (wb asegs m a = true -> wb asegs m' a = true)) ->
  region_ok asegs priv E m' k r.
Proof.
  intros priv E m m' k r CB BG [Rbst Rrange Rvalid Rcells Rin Rbg] H.
  constructor.
  - exact Rbst.
  - exact Rrange.
  - intros K a Ha. destruct (Rvalid K a Ha) as (V1 & V2 & V3). destruct (H a Ha) as [H1 H2]. split; [exact H1|]. split; [intros W; exact (H2 (V2 W))| exact V3].
  - intros g gr Hg. rewrite CB in Hg. cbn in Hg. discriminate Hg.
  - intros g gr c i Hg. rewrite CB in Hg. cbn in Hg. discriminate Hg.
  - intros o H1 H2 U. unfold bg_byte. rewrite BG. exact I.
Qed.

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

Lemma zone_ops_k : forall E st ms mo r hargs wnl L RNG sta LBa aw ka wlena kda a,
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  CtrA.win_lookup wnl ka = Some (wlena, kda) ->
  0 <= a < two64 -> bv_unsigned (ev E ka) <= a < bv_unsigned (ev E ka) + bv_unsigned (den E wlena) -> uband a ->
  forall o, In o (s_ops st) -> ~ Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E) (op_args o))).
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw ka wlena kda a CF WL Ha INB UB o Ho FP. pose proof atop_range as ATR.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (PrimInt63.eqb (op_id o) HEAP_ID) eqn:QH.
  - apply Uint63.eqb_correct in QH. pose proof (ReadPost.count_one_args HEAP_ID (s_ops st) o hargs Ho QH Hc Hf) as EA.
    rewrite QH, EA, OPS_fp1, Eh in FP.
    apply (proj1 (fp_spec IMGX _ _ _ _ _ a (decode_hargs E md A nw rest nn Tnw Nn Ln))) in FP as (_ & _ & NWS).
    apply NWS. destruct (HeapCtrB.nonstack_windows_In E nn rest wnl ka wlena kda NW (HeapCtrB.win_lookup_In _ _ _ _ WL)) as (_ & _ & _ & INW).
    unfold in_ws. apply in_ivs_In. eexists. split; [apply in_map; exact INW|]. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. lia.
  - apply Uint63.eqb_false_spec in QH. destruct (OPS_fp_other _ _ a QH FP) as [(iv0 & Hi & RRa)|[(a' & (iv0 & Hi & RRa) & ->)|(a' & STK & ->)]].
    + pose proof (AI_aci_img AI iv0 Hi) as HIa. unfold uband, AIMG_HI, KLS in *. lia.
    + pose proof (AI_aci_img AI iv0 Hi) as HIa. pose proof (AI_aci_lo AI iv0 Hi) as LOa. unfold AIMG_HI in HIa.
      exact (shad_not_uband a' ltac:(lia) UB).
    +
      exact (shad_not_uband a' ltac:(lia) UB).
Qed.

Variable SYM : Z.
Variable FRM0 : Z.
Hypothesis FR0 : 0 < FRM0 <= 8192.
Hypothesis WALK : memcpy_walk_stmt SYM.
Hypothesis WALK0 : memcpy0_walk_stmt SYM FRM0.

Theorem asink_sound_at : forall pc, to_Z pc = SYM -> contract_sound asegs OPS MP PB (asink_c pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc asink_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = SYM) by (rewrite Hspc; exact Hpc).
  destruct (asink_apply_shape st sts Happ)
    as (r & hargs & wnl & st1 & ka & kd & OFF & ra & rd & wlena & kda & wlend & kdd & PRE & G10 & DO & NKK & FA & FD & WLa & WLd & CKa & CKd
        & CBa & BGa & LOa & RWa & LOd & LEn & LEo & LEs & LEWa & LEWd & PKa & PKd & ->).
  set (nsv := getr st X12) in *. set (nZ := bv_unsigned (den E nsv)) in *.
  destruct (Z.eq_dec nZ 0) as [NZ0|NZ1].
  {
    apply (mc0_core AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
             MP NMAXt ACCT_rng ACCT_rng_aimg ACCT_silent SYM FRM0 FR0 WALK0 st K E ms mo r hargs wnl st1 HS HMP HPC PRE); [| exact HK].
    change (AP.getr (ms_regs ms) 12) with (AP.getr (ms_regs ms) (reg_of_r5 X12)). rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X12). fold nsv.
    apply bv_eq. rewrite Z_to_bv_unsigned. fold nZ. rewrite NZ0. reflexivity. }

  destruct (CtrPre.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs. pose proof atop_range as ATR.
  set (R := ms_regs ms) in *. set (m := ms_mem ms) in *.
  set (Dd := bv_unsigned (ev E ka)) in *. set (Db := bv_unsigned (ev E kd)) in *. set (offZ := bv_unsigned (den E OFF)) in *.
  set (wlenZ := bv_unsigned (den E wlena)) in *.
  pose proof (bv_unsigned_in_range 64 (den E nsv)) as NRr. change (bv_modulus 64) with (2 ^ 64) in NRr. fold nZ in NRr.
  assert (POSn : 0 < nZ) by lia.
  apply (KnownA.KnownA.known_leu_sound E _ _ _ Hfs) in LEn. fold nZ in LEn. change (bv_unsigned (den E (rg_hi ra))) with (hiZ E ra) in LEn.
  apply (KnownA.KnownA.known_leu_sound E _ _ _ Hfs) in LEo. fold offZ in LEo. change (bv_unsigned (den E (rg_hi rd))) with (hiZ E rd) in LEo.
  apply (KnownA.KnownA.known_leu_sound E _ _ _ Hfs) in LEs. fold nZ in LEs. rewrite ValP.den_sv_alu in LEs. cbn [alu64 alu] in LEs. rewrite bv_sub_unsigned in LEs.
  fold offZ in LEs. change (bv_unsigned (den E (rg_hi rd))) with (hiZ E rd) in LEs.
  apply (KnownA.KnownA.known_leu_sound E _ _ _ Hfs) in LEWa. change (bv_unsigned (den E (rg_hi ra))) with (hiZ E ra) in LEWa. fold wlenZ in LEWa.
  apply (KnownA.KnownA.known_leu_sound E _ _ _ Hfs) in LEWd. change (bv_unsigned (den E (rg_hi rd))) with (hiZ E rd) in LEWd.
  pose proof (bv_unsigned_in_range 64 (den E (rg_hi rd))) as HBR. change (bv_modulus 64) with (2 ^ 64) in HBR. change (bv_unsigned (den E (rg_hi rd))) with (hiZ E rd) in HBR.
  pose proof (bv_unsigned_in_range 64 (den E OFF)) as ORr. change (bv_modulus 64) with (2 ^ 64) in ORr. fold offZ in ORr.
  assert (SUM : offZ + nZ <= hiZ E rd).
  { rewrite bv_wrap_small in LEs by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia). lia. }

  destruct (client_kind_inv kda CKa) as (KTa & NF7a & NF8a). destruct (client_kind_inv kdd CKd) as (KTd & NF7d & NF8d).
  destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw ka wlena kda 0 nZ CF WLa KTa
              NF7a NF8a (client_kind_range kda CKa) ltac:(lia) ltac:(lia) ltac:(fold wlenZ; lia)) as (pd & Abd & nbd & HINd & BAd1 & BAd2).
  pose proof (W_PAT E st ms mo r hargs wnl L RNG sta LBa aw ka wlena kda pd Abd nbd HS CF AH WLa KTa NF7a NF8a PKa 0 nZ ltac:(lia) ltac:(lia) ltac:(fold wlenZ; lia) HINd BAd1 BAd2) as PAT_pd.
  destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw kd wlend kdd offZ (offZ + nZ) CF WLd KTd
              NF7d NF8d (client_kind_range kdd CKd) ltac:(lia) ltac:(lia) ltac:(lia)) as (ps & Abs & nbs & HINs & BAs1 & BAs2).
  pose proof (W_PAT E st ms mo r hargs wnl L RNG sta LBa aw kd wlend kdd ps Abs nbs HS CF AH WLd KTd NF7d NF8d PKd offZ (offZ + nZ) ltac:(lia) ltac:(lia) ltac:(lia) HINs BAs1 BAs2) as PAT_ps.
  fold Dd in BAd1, BAd2. fold Db in BAs1, BAs2.
  set (S := Db + offZ) in *.
  destruct (block_range_facts AI L RNG sta LBa m pd Abd nbd Dd nZ AH HINd PAT_pd ltac:(lia) ltac:(lia) ltac:(lia))
    as ((junk & DST) & APB0 & UNP0 & LOWd & HId & RNGD & RLOd & RHId & HULLd & WRHd & RNGHd).
  destruct (block_range_facts AI L RNG sta LBa m ps Abs nbs S nZ AH HINs PAT_ps ltac:(unfold S; lia) ltac:(unfold S; lia) ltac:(lia))
    as ((src & SRCC) & APB1 & UNP1 & LOWs & HIs & RNGS & RLOs & RHIs & HULLs & WRHs & RNGHs).
  assert (N40 : nZ <= 2 ^ 40).
  { destruct (heap_block_facts AI _ _ _ _ _ (HB pd Abd nbd) AH HINd ltac:(exists pd; reflexivity)) as (NRb & _). cbn [ab_size] in NRb.
    unfold AREQMAX in NRb. lia. }

  assert (LSRC : length src = Z.to_nat nZ).
  { destruct SRCC as [[WFs _] _]. cbn [cells_wf cell_wf] in WFs. exact (proj1 WFs). }
  assert (SRCB : ALib.Mem.bytes_at asegs m S src).
  { destruct SRCC as [[_ BYs] _]. cbn [cells_bytes cbytes] in BYs. rewrite app_nil_r in BYs. exact BYs. }

  destruct CF as (LB0 & ks0 & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)) eqn:CFE. clear CFE.
  destruct (HeapCtrB.nonstack_windows_In E nn rest wnl ka wlena kda NW (HeapCtrB.win_lookup_In _ _ _ _ WLa)) as (Ka0n & _ & KDa & INWa).
  destruct (HeapCtrB.nonstack_windows_In E nn rest wnl kd wlend kdd NW (HeapCtrB.win_lookup_In _ _ _ _ WLd)) as (Kd0n & _ & _ & _).
  assert (Ka0 : PrimInt63.eqb ka 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Ka0n).
  assert (Kd0 : PrimInt63.eqb kd 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kd0n).
  assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity.
  assert (DISJ : S + nZ <= Dd \/ Dd + nZ <= S).
  { destruct (Z_lt_le_dec Dd (S + nZ)) as [L1|G1]; [| left; lia]. destruct (Z_lt_le_dec S (Dd + nZ)) as [L2|G2]; [| right; lia].
    exfalso. apply (so_disj _ _ _ _ _ _ HS ka ra kd rd FA FD ltac:(intros Q; apply NKK; symmetry; exact Q) Ka0 Kd0 (or_introl RWa) (Z.max Dd S)).
    unfold loZ. rewrite LOa, LOd, KZ0. fold Dd Db. unfold S in *. lia. }
  idtac "SK-1".

  assert (EA0 : bv_unsigned (AP.getr R (reg_of_r5 X10)) = Dd).
  { unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X10), G10, HeapCtr.den_VPz. reflexivity. }
  assert (EA1 : bv_unsigned (AP.getr R (reg_of_r5 X11)) = S).
  { unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X11), (MemcpyCtr.sym_offset_sound E (s_regs st) _ kd OFF DO).
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
  idtac "SK-2".
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
  -
    intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV'' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    destruct HQ as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK' & DSTP & SRCP).
    rewrite EA0', EA2' in MU, DSTP.
    match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
    set (Fv := CtrFree.cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0). set (E' := CtrFrame.E' E st Fv Gv).
    destruct (HeapCtr.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
    assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
    { unfold R. rewrite <- HeapCtr.reg_of_X1, (GlueA.getr_RA asegs OPS E st ms mo HS X1), Hra0, ER.
      assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.den_wlit. }
    assert (EMS' : ms' = CtrFrame.ms' ms r R' m').
    { rewrite EMS. unfold CtrFrame.ms'. f_equal. rewrite RAEQ. apply ret_pc_even.
      - pose proof (int_range r) as RRr. rewrite two63_eq in RRr. lia.
      - pose proof (HeapCtr.call_pre_even st r CP) as EVn.
        pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
        change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EVn in LM. change (to_Z 0%uint63) with 0 in LM.
        change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
    destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & NXc).
    destruct (CtrFrame.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
    destruct (CtrFrame.SVB_parts st FOK) as (RFB & _ & _ & _ & _ & OPB).
    assert (VB10 : sv_vars_below (s_next st) (getr st X10) = true) by exact (PlanS.rf_allb_get _ _ _ RFB X10).
    assert (DVP : den E' (getr st X10) = AP.getr R' 10%bv).
    { unfold E'. rewrite (CtrFrame.den_E' E st Fv Gv _ VB10). symmetry. exact (GlueA.getr_RA asegs OPS E st ms mo HS X10). }
    assert (CF2 : CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw).
    { exists LB0, ks0, offs, rss, ksp, nn, md, A, nw, rest. repeat (split; [assumption|]). exists W. repeat (split; [assumption|]). assumption. }

    pose proof (phaseA_ms AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                  st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' Dd nZ 2240 (getr st X10) (s_next (clobber st1)) HS CP FS CF2 AH BOT LO SPT
                  ltac:(unfold AIMG_HI in *; lia) (or_introl HId) ltac:(lia) MU WM MI MINV' STK'
                  ltac:(intros rg Hrg; unfold CtrFrame.kept_regsA in Hrg; cbn [In] in Hrg; repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]); destruct Hrg)
                  DVP OTH HMI' ACP) as HSA.
    fold Fv Gv E' in HSA. fold m in HSA.
    set (mj := mjoinR Dd (Dd + nZ) m m') in *.
    idtac "SK-A".
    destruct (CallA.sp_region_inv st ks0 offs rss SPR) as (_ & Hrs & _).
    assert (NKS : ka <> ks0).
    { intros Q. rewrite Q, Hrs in FA. injection FA as Q2. rewrite Q2 in FLOOR. unfold loZ in FLOOR. rewrite LOa, KZ0 in FLOOR.
      rewrite <- Q in FLOOR. fold Dd in FLOOR. lia. }
    assert (FA1 : IMap.find ka (s_regs st1) = Some ra).
    { rewrite (CtrFrame.st1_regs st st1 FS ks0 offs rss ksp SPR Hksp).
      rewrite IMap.find_add_other; [exact FA| exact (so_bst _ _ _ _ _ _ HS)| intros Q; apply NKS; symmetry; exact Q]. }

    destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw ka wlena kda 0 wlenZ CF2 WLa KTa
                NF7a NF8a (client_kind_range kda CKa) ltac:(lia) ltac:(lia) ltac:(unfold wlenZ; lia)) as (p & Ab & nb & HINB & BA1 & BA2).
  pose proof (W_PAT E st ms mo r hargs wnl L RNG sta LBa aw ka wlena kda p Ab nb HS CF2 AH WLa KTa NF7a NF8a PKa 0 wlenZ ltac:(lia) ltac:(lia) ltac:(unfold wlenZ; lia) HINB BA1 BA2) as PAT_p.
    fold Dd in BA1, BA2.
    assert (UBW : forall a, Dd <= a < Dd + wlenZ -> uband a).
    { intros a Ha. exact (Op.blk_band AI AI_fake L RNG sta LBa m (HB p Ab nb) a AH HINB ltac:(cbn [ab_addr ab_size]; lia)). }
    assert (A64 : forall a, Dd <= a < Dd + wlenZ -> 0 <= a < 2 ^ 64 /\ 0x62f000 <= a).
    { intros a Ha. pose proof (UBW a Ha) as U. unfold uband, AIMG_HI, KLS in U. lia. }
    destruct (CtrFrame.reg_E' OPS E st ms mo HS FOK Fv Gv ka ra FA) as (EKa & EHa & _). fold E' in EKa, EHa.
    assert (OUTSIDE : forall a, 0 <= a < 2 ^ 64 -> ~ (Dd <= a < Dd + nZ) -> mj (AM.wa a) = m' (AM.wa a)).
    { intros a Ha N. unfold mj, mjoinR. rewrite (ReadPost.wa_u a Ha). unfold in_rng. replace ((Dd <=? a) && (a <? Dd + nZ)) with false by lia. reflexivity. }
    pose proof (so_reg _ _ _ _ _ _ HSA ka ra FA1) as ROj. cbn [s_priv] in ROj. change (ms_mem (CtrFrame.ms' ms r R' mj)) with mj in ROj.
    assert (MAPPED : forall a, Dd <= a < Dd + hiZ E ra -> m' (Z_to_bv 64 a) <> None).
    { intros a Ha. destruct (A64 a ltac:(lia)) as [AR A6].
      destruct (Z_lt_le_dec a (Dd + nZ)) as [IN|OUT].
      - destruct DSTP as [[_ BY] _]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. destruct BY as (_ & _ & BY).
        pose proof (BY (Z.to_nat (a - Dd)) ltac:(rewrite LSRC; lia)) as B1. replace (Dd + Z.of_nat (Z.to_nat (a - Dd))) with a in B1 by lia.
        destruct (nth_error src (Z.to_nat (a - Dd))) as [b|] eqn:NE; [| apply nth_error_None in NE; lia].
        rewrite <- (GlueA.rb_mrdA asegs) in B1. rewrite (raw_of_view m' a b ltac:(lia) B1). discriminate.
      - destruct (ro_valid _ _ _ _ _ _ ROj Ka0 a ltac:(rewrite EKa, EHa; unfold loZ; rewrite LOa, KZ0; fold Dd; lia)) as (V1 & _).
        destruct (rb asegs mj a) as [b|] eqn:RBj; [| exfalso; exact (V1 eq_refl)].
        pose proof (raw_of_view mj a b ltac:(lia) RBj) as RAWj. change (Z_to_bv 64 a) with (AM.wa a) in RAWj |- *.
        rewrite (OUTSIDE a AR ltac:(lia)) in RAWj. rewrite RAWj. discriminate. }
    assert (RO' : region_ok asegs (s_priv st) E' m' ka ra).
    { apply (region_ok_claimless (s_priv st) E' mj m' ka ra CBa BGa ROj). intros a Ha. rewrite EKa, EHa in Ha. unfold loZ in Ha. rewrite LOa, KZ0 in Ha. fold Dd in Ha.
      pose proof (MAPPED a ltac:(lia)) as MP1. destruct (A64 a ltac:(lia)) as [AR A6]. split.
      - unfold rb. destruct (m' (Z_to_bv 64 a)); [discriminate| exfalso; exact (MP1 eq_refl)].
      - intros _. apply (GlueA.wb_wviewA asegs). rewrite (AImg.ref_wview_overlay m' (AM.wa a)); [exact MP1|]. right. rewrite (ReadPost.wa_u a AR). lia. }
    idtac "SK-B0".
    assert (ARGT : forall o, In o (s_ops st) -> map (den E') (op_args o) = map (den E) (op_args o)).
    { intros o Ho. apply (CtrFrame.map_den_E' E st Fv Gv). exact (proj1 (forallb_forall _ _) OPB o Ho). }
    assert (HS1 : st_ok asegs OPS E'
              (SS r (rf_set (s_rf (clobber st1)) X10 (getr st X10)) (s_ff st) (s_resv st) (IMap.add ka ra (s_regs st1)) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1)))
              (MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None m' (seg_rom asegs)) mo').
    { apply (st_ok_based_replace_g asegs OPS E' _ R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None mj m' (seg_rom asegs) mo' ka ra ra HSA FA1 Ka0).
      - intros a Ha NC. unfold two64 in Ha. cbn [s_regs s_ops] in *.
        assert (INR : Dd <= a < Dd + hiZ E ra).
        { destruct NC as [RGa|CH]; [rewrite EHa, EKa in RGa; unfold loZ in RGa; rewrite LOa, KZ0 in RGa; fold Dd in RGa; lia|].
          destruct (Z_lt_le_dec a Dd) as [L1|G1]; [exfalso; apply CH; symmetry; apply (OUTSIDE a ltac:(lia)); lia|].
          destruct (Z_lt_le_dec a (Dd + nZ)) as [L2|G2]; [lia| exfalso; apply CH; symmetry; apply (OUTSIDE a ltac:(lia)); lia]. }
        assert (INB : Dd <= a < Dd + wlenZ) by lia.
        pose proof (UBW a INB) as UB. split; [| split].
        + intros k2 r2 H2 NK2 K20 RG2.
          apply (so_disj _ _ _ _ _ _ HSA ka ra k2 r2 FA1 H2 ltac:(intros Q; apply NK2; symmetry; exact Q) Ka0 K20 (or_introl RWa) a).
          split; [rewrite EKa, EHa; unfold loZ; rewrite LOa, KZ0; fold Dd; lia| exact RG2].
        + exact (UnreggPre.no_seg_above a (proj2 (A64 a INB))).
        + intros o Ho FP. rewrite (ARGT o Ho) in FP.
          exact (zone_ops_k E st ms mo r hargs wnl L RNG sta LBa aw ka wlena kda a CF2 WLa ltac:(unfold two64; lia) INB UB o Ho FP).
      - intros x H. unfold mj, mjoinR in H. destruct (in_rng Dd (Dd + nZ) (bv_unsigned x)) eqn:IS; [| exact H].
        unfold in_rng in IS. rewrite <- (Z_to_bv_bv_unsigned x). apply MAPPED. lia.
      - intros x b Hx seg Hs. pose proof (MINV' x b Hx) as RO. unfold AM.ro_addr in RO. rewrite Hs in RO. apply negb_false_iff in RO. exact RO.
      - exact RO'.
      - intros a RGa. rewrite EHa, EKa in RGa. unfold loZ in RGa. rewrite LOa, KZ0 in RGa. fold Dd in RGa. right. apply Exists_exists. exists (HEAP_ID, map (den E') hargs). split.
        + unfold insts. apply in_map_iff. exists (OpI HEAP_ID hargs). split; [reflexivity|]. cbn [s_ops]. exact (UnreggPre.find_op_In _ _ _ Hf).
        + cbn [fst snd]. apply OPS_cov1. split; [reflexivity|]. eexists _, _, _, _.
          split; [exact (CtrFrame.DEC' E st FOK Fv Gv nn rest hargs md A nw Hf Eh Tnw Nn Ln)| left].
          unfold in_ws, heap_ws. apply in_ivs_In. eexists. split; [apply in_map; apply filter_In; split; [exact INWa|]|].
          * cbn [w_kind]. apply negb_true_iff. apply Z.eqb_neq. exact KDa.
          * unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. fold Dd wlenZ. lia. }
    idtac "SK-B1".

    assert (HS2 : st_ok asegs OPS E'
              (SS r (rf_set (s_rf (clobber st1)) X10 (getr st X10)) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1)))
              (MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None m' (seg_rom asegs)) mo').
    { apply (st_ok_regs_ext OPS E' _ _ _ _ (IMap.add ka ra (s_regs st1)) (s_regs st1) _ _ _ _ _ _ (so_bst _ _ _ _ _ _ HSA)); [| exact HS1].
      intros k. destruct (Uint63.eqb ka k) eqn:Q.
      - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_add_same by exact (so_bst _ _ _ _ _ _ HSA). exact FA1.
      - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other by (exact (so_bst _ _ _ _ _ _ HSA) || exact Q). reflexivity. }
    assert (SH2 : sink_state st st1 r
                = SS r (rf_set (s_rf (clobber st1)) X10 (getr st X10)) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1))).
    { unfold sink_state. rewrite <- FF1, <- RV1, <- FS1, <- OP1, <- PV1, <- FF, <- RV, <- RG, <- FS0, <- OP, <- PV. destruct (clobber st1); reflexivity. }
    apply (HK _ (or_introl eq_refl) E' ms' mo' (CtrFrame.EXT E st Fv Gv) HMP').
    rewrite EMS'. unfold CtrFrame.ms'. rewrite SH2. exact HS2.
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

Unset Nia Cache. Unset Nra Cache.

Definition sink_state (st st1 : sstate) (r : int) : sstate := setpc (setr (clobber st1) X10 (getr st X10)) r.

Lemma client_kind_inv : forall kd, client_kind kd = true ->
  weqb kd ActrA.K_TWIN = false /\ w2Z kd <> K_FRAMEz /\ w2Z kd <> K_FTWINz.
Proof.
  intros kd H. unfold client_kind in H. apply andb_prop in H as [H _]. repeat match type of H with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in H as [H X] end.
  apply negb_true_iff in Q1, Q0, Q. split; [exact Q1|].
  split; intros X; [rewrite weqb_eqb in Q0; apply Z.eqb_neq in Q0; apply Q0; rewrite X; reflexivity
                   | rewrite weqb_eqb in Q; apply Z.eqb_neq in Q; apply Q; rewrite X; reflexivity].
Qed.

Lemma client_kind_range : forall kd, client_kind kd = true -> K_BLOCK <= w2Z kd < K_GHOST.
Proof.
  intros kd H. unfold client_kind in H. apply andb_prop in H as [_ H].
  repeat (apply orb_prop in H as [H|H]); apply weqb_eq in H; subst kd; vm_compute; (split; [discriminate| reflexivity]).
Qed.

Lemma asink_apply_shape : forall st sts, asink_apply st = Some sts ->
  exists r hargs wnl st1 ka kd OFF ra rd wlena kda wlend kdd,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ getr st X10 = VP ka wzero
    /\ CtrA.sym_offset (s_regs st) (getr st X11) = Some (kd, OFF) /\ kd <> ka
    /\ IMap.find ka (s_regs st) = Some ra /\ IMap.find kd (s_regs st) = Some rd
    /\ CtrA.win_lookup wnl ka = Some (wlena, kda) /\ CtrA.win_lookup wnl kd = Some (wlend, kdd)
    /\ client_kind kda = true /\ client_kind kdd = true
    /\ rg_cells ra = IMap.Leaf /\ rg_bg ra = BGNone /\ rg_lo ra = 0%uint63 /\ rg_w ra = true /\ rg_lo rd = 0%uint63
    /\ KnownT.KnownT.known_leu_t (s_facts st) (getr st X12) (rg_hi ra) = true
    /\ KnownT.KnownT.known_leu_t (s_facts st) OFF (rg_hi rd) = true /\ KnownT.KnownT.known_leu_t (s_facts st) (getr st X12) (sv_alu ALU_SUB (rg_hi rd) OFF) = true
    /\ KnownT.KnownT.known_leu_t (s_facts st) (rg_hi ra) wlena = true /\ KnownT.KnownT.known_leu_t (s_facts st) (rg_hi rd) wlend = true
    /\ RangeC.TwinB.RangeC.pat_ok st wnl ka kda = true /\ RangeC.TwinB.RangeC.pat_ok st wnl kd kdd = true
    /\ sts = [sink_state st st1 r].
Proof.
  intros st sts H. unfold asink_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (getr st X10) as [|ka oa| | | | | | | | |] eqn:G10; try discriminate H.
  destruct (CtrA.sym_offset (s_regs st) (getr st X11)) as [[kd OFF]|] eqn:DO; [|discriminate H].
  destruct (IMap.find ka (s_regs st)) as [ra|] eqn:FA; [|discriminate H].
  destruct (IMap.find kd (s_regs st)) as [rd|] eqn:FD; [|discriminate H].
  destruct (rg_cells ra) eqn:CBa; [|discriminate H].
  destruct (CtrA.win_lookup wnl ka) as [[wlena kda]|] eqn:WLa; [|discriminate H].
  destruct (CtrA.win_lookup wnl kd) as [[wlend kdd]|] eqn:WLd; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:PKC; [discriminate H|] end. apply negb_false_iff in PKC. apply andb_prop in PKC as [PKa PKd].
  cbv zeta in H. match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate H] end.
  repeat match type of CND with (_ && _)%bool = true => let Q := fresh "Q" in apply andb_prop in CND as [CND Q] end.
  apply weqb_eq in CND. subst oa. apply negb_true_iff in Q6. apply Uint63.eqb_false_spec in Q6.
  apply Uint63.eqb_correct in Q9, Q7.
  assert (BGN : rg_bg ra = BGNone) by (unfold is_bgnone in Q10; destruct (rg_bg ra); try discriminate Q10; reflexivity).
  exists r, hargs, wnl, st1, ka, kd, OFF, ra, rd, wlena, kda, wlend, kdd. repeat (split; [reflexivity || assumption|]).
  unfold sink_state. congruence.
Qed.

Lemma st_ok_regs_ext {rc : runConstT} : forall OPS E pc rf ff rv R R' fs ops priv nx ms mo,
  IMap.bst R' -> (forall k, IMap.find k R' = IMap.find k R) ->
  st_ok bsegs OPS E (SS pc rf ff rv R fs ops priv nx) ms mo -> st_ok bsegs OPS E (SS pc rf ff rv R' fs ops priv nx) ms mo.
Proof.
  intros OPS E pc rf ff rv R R' fs ops priv nx ms mo BST EXT HS.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next] in *.
  assert (IB : forall a, in_based E R' a <-> in_based E R a).
  { intros a. unfold in_based. split; intros (k & r & F & X); exists k, r; (split; [| exact X]); [rewrite <- EXT| rewrite EXT]; exact F. }
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - intros k r F. rewrite EXT in F. exact (Preg k r F).
  - intros k1 r1 k2 r2 F1 F2. rewrite EXT in F1, F2. exact (Pdisj k1 r1 k2 r2 F1 F2).
  - intros r g gr c F. rewrite EXT in F. exact (Ppub r g gr c F).
  - apply Forall_forall. intros o Ho a FP. destruct (proj1 (Forall_forall _ _) Papart o Ho a FP) as [NB X]. split; [| exact X].
    intros B. apply NB. apply IB. exact B.
  - intros a [B|S]; apply Pcov; [left; apply IB; exact B| right; exact S].
Qed.

Lemma region_ok_claimless {rc : runConstT} : forall priv E (m m' : word -> option byte) k r,
  rg_cells r = IMap.Leaf -> rg_bg r = BGNone ->
  region_ok bsegs priv E m k r ->
  (forall a, bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r -> rb bsegs m' a <> None /\ (wb bsegs m a = true -> wb bsegs m' a = true)) ->
  region_ok bsegs priv E m' k r.
Proof.
  intros priv E m m' k r CB BG [Rbst Rrange Rvalid Rcells Rin Rbg] H.
  constructor.
  - exact Rbst.
  - exact Rrange.
  - intros K a Ha. destruct (Rvalid K a Ha) as (V1 & V2 & V3). destruct (H a Ha) as [H1 H2]. split; [exact H1|]. split; [intros W; exact (H2 (V2 W))| exact V3].
  - intros g gr Hg. rewrite CB in Hg. cbn in Hg. discriminate Hg.
  - intros g gr c i Hg. rewrite CB in Hg. cbn in Hg. discriminate Hg.
  - intros o H1 H2 U. unfold bg_byte. rewrite BG. exact I.
Qed.

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
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.TwinB.cov1 HEAP_ID args z.
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

Lemma zone_ops_k : forall E st ms mo r hargs wnl L RNG sta LBa aw ka wlena kda a,
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  CtrA.win_lookup wnl ka = Some (wlena, kda) ->
  0 <= a < two64 -> bv_unsigned (ev E ka) <= a < bv_unsigned (ev E ka) + bv_unsigned (den E wlena) -> uband a ->
  forall o, In o (s_ops st) -> ~ Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E) (op_args o))).
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw ka wlena kda a CF WL Ha INB UB o Ho FP. pose proof atop_range as ATR.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (PrimInt63.eqb (op_id o) HEAP_ID) eqn:QH.
  - apply Uint63.eqb_correct in QH. pose proof (ReadPost.TwinB.count_one_args HEAP_ID (s_ops st) o hargs Ho QH Hc Hf) as EA.
    rewrite QH, EA, OPS_fp1, Eh in FP.
    apply (proj1 (fp_spec IMGX _ _ _ _ _ a (decode_hargs E md A nw rest nn Tnw Nn Ln))) in FP as (_ & _ & NWS).
    apply NWS. destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl ka wlena kda NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL)) as (_ & _ & _ & INW).
    unfold in_ws. apply in_ivs_In. eexists. split; [apply in_map; exact INW|]. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. lia.
  - apply Uint63.eqb_false_spec in QH. destruct (OPS_fp_other _ _ a QH FP) as [(iv0 & Hi & RRa)|[(a' & (iv0 & Hi & RRa) & ->)|(a' & STK & ->)]].
    + pose proof (AI_aci_img AI iv0 Hi) as HIa. unfold uband, AIMG_HI, KLS in *. lia.
    + pose proof (AI_aci_img AI iv0 Hi) as HIa. pose proof (AI_aci_lo AI iv0 Hi) as LOa. unfold AIMG_HI in HIa.
      exact (shad_not_uband a' ltac:(lia) UB).
    +
      exact (shad_not_uband a' ltac:(lia) UB).
Qed.

Variable SYM : Z.
Variable FRM0 : Z.
Hypothesis FR0 : 0 < FRM0 <= 8192.
Hypothesis WALK : memcpy_walk_stmt SYM.
Hypothesis WALK0 : memcpy0_walk_stmt SYM FRM0.

Theorem asink_sound_at : forall pc, to_Z pc = SYM -> contract_sound bsegs OPS MP PB (asink_c pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc asink_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = SYM) by (rewrite Hspc; exact Hpc).
  destruct (asink_apply_shape st sts Happ)
    as (r & hargs & wnl & st1 & ka & kd & OFF & ra & rd & wlena & kda & wlend & kdd & PRE & G10 & DO & NKK & FA & FD & WLa & WLd & CKa & CKd
        & CBa & BGa & LOa & RWa & LOd & LEn & LEo & LEs & LEWa & LEWd & PKa & PKd & ->).
  set (nsv := getr st X12) in *. set (nZ := bv_unsigned (den E nsv)) in *.
  destruct (Z.eq_dec nZ 0) as [NZ0|NZ1].
  {
    apply (mc0_core AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
             MP NMAXt ACCT_rng ACCT_rng_aimg ACCT_silent SYM FRM0 FR0 WALK0 st K E ms mo r hargs wnl st1 HS HMP HPC PRE); [| exact HK].
    change (AP.getr (ms_regs ms) 12) with (AP.getr (ms_regs ms) (reg_of_r5 X12)). rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X12). fold nsv.
    apply bv_eq. rewrite Z_to_bv_unsigned. fold nZ. rewrite NZ0. reflexivity. }

  destruct (CtrPre.TwinB.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs. pose proof atop_range as ATR.
  set (R := ms_regs ms) in *. set (m := ms_mem ms) in *.
  set (Dd := bv_unsigned (ev E ka)) in *. set (Db := bv_unsigned (ev E kd)) in *. set (offZ := bv_unsigned (den E OFF)) in *.
  set (wlenZ := bv_unsigned (den E wlena)) in *.
  pose proof (bv_unsigned_in_range 64 (den E nsv)) as NRr. change (bv_modulus 64) with (2 ^ 64) in NRr. fold nZ in NRr.
  assert (POSn : 0 < nZ) by lia.
  apply (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ Hfs) in LEn. fold nZ in LEn. change (bv_unsigned (den E (rg_hi ra))) with (hiZ E ra) in LEn.
  apply (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ Hfs) in LEo. fold offZ in LEo. change (bv_unsigned (den E (rg_hi rd))) with (hiZ E rd) in LEo.
  apply (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ Hfs) in LEs. fold nZ in LEs. rewrite ValP.den_sv_alu in LEs. cbn [alu64 alu] in LEs. rewrite bv_sub_unsigned in LEs.
  fold offZ in LEs. change (bv_unsigned (den E (rg_hi rd))) with (hiZ E rd) in LEs.
  apply (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ Hfs) in LEWa. change (bv_unsigned (den E (rg_hi ra))) with (hiZ E ra) in LEWa. fold wlenZ in LEWa.
  apply (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ Hfs) in LEWd. change (bv_unsigned (den E (rg_hi rd))) with (hiZ E rd) in LEWd.
  pose proof (bv_unsigned_in_range 64 (den E (rg_hi rd))) as HBR. change (bv_modulus 64) with (2 ^ 64) in HBR. change (bv_unsigned (den E (rg_hi rd))) with (hiZ E rd) in HBR.
  pose proof (bv_unsigned_in_range 64 (den E OFF)) as ORr. change (bv_modulus 64) with (2 ^ 64) in ORr. fold offZ in ORr.
  assert (SUM : offZ + nZ <= hiZ E rd).
  { rewrite bv_wrap_small in LEs by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia). lia. }

  destruct (client_kind_inv kda CKa) as (KTa & NF7a & NF8a). destruct (client_kind_inv kdd CKd) as (KTd & NF7d & NF8d).
  destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw ka wlena kda 0 nZ CF WLa KTa
              NF7a NF8a (client_kind_range kda CKa) ltac:(lia) ltac:(lia) ltac:(fold wlenZ; lia)) as (pd & Abd & nbd & HINd & BAd1 & BAd2).
  pose proof (W_PAT E st ms mo r hargs wnl L RNG sta LBa aw ka wlena kda pd Abd nbd HS CF AH WLa KTa NF7a NF8a PKa 0 nZ ltac:(lia) ltac:(lia) ltac:(fold wlenZ; lia) HINd BAd1 BAd2) as PAT_pd.
  destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw kd wlend kdd offZ (offZ + nZ) CF WLd KTd
              NF7d NF8d (client_kind_range kdd CKd) ltac:(lia) ltac:(lia) ltac:(lia)) as (ps & Abs & nbs & HINs & BAs1 & BAs2).
  pose proof (W_PAT E st ms mo r hargs wnl L RNG sta LBa aw kd wlend kdd ps Abs nbs HS CF AH WLd KTd NF7d NF8d PKd offZ (offZ + nZ) ltac:(lia) ltac:(lia) ltac:(lia) HINs BAs1 BAs2) as PAT_ps.
  fold Dd in BAd1, BAd2. fold Db in BAs1, BAs2.
  set (S := Db + offZ) in *.
  destruct (block_range_facts AI L RNG sta LBa m pd Abd nbd Dd nZ AH HINd PAT_pd ltac:(lia) ltac:(lia) ltac:(lia))
    as ((junk & DST) & APB0 & UNP0 & LOWd & HId & RNGD & RLOd & RHId & HULLd & WRHd & RNGHd).
  destruct (block_range_facts AI L RNG sta LBa m ps Abs nbs S nZ AH HINs PAT_ps ltac:(unfold S; lia) ltac:(unfold S; lia) ltac:(lia))
    as ((src & SRCC) & APB1 & UNP1 & LOWs & HIs & RNGS & RLOs & RHIs & HULLs & WRHs & RNGHs).
  assert (N40 : nZ <= 2 ^ 40).
  { destruct (heap_block_facts AI _ _ _ _ _ (HB pd Abd nbd) AH HINd ltac:(exists pd; reflexivity)) as (NRb & _). cbn [ab_size] in NRb.
    unfold AREQMAX in NRb. lia. }

  assert (LSRC : length src = Z.to_nat nZ).
  { destruct SRCC as [[WFs _] _]. cbn [cells_wf cell_wf] in WFs. exact (proj1 WFs). }
  assert (SRCB : ALib.Mem.bytes_at bsegs m S src).
  { destruct SRCC as [[_ BYs] _]. cbn [cells_bytes cbytes] in BYs. rewrite app_nil_r in BYs. exact BYs. }

  destruct CF as (LB0 & ks0 & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)) eqn:CFE. clear CFE.
  destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl ka wlena kda NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLa)) as (Ka0n & _ & KDa & INWa).
  destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl kd wlend kdd NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLd)) as (Kd0n & _ & _ & _).
  assert (Ka0 : PrimInt63.eqb ka 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Ka0n).
  assert (Kd0 : PrimInt63.eqb kd 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kd0n).
  assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity.
  assert (DISJ : S + nZ <= Dd \/ Dd + nZ <= S).
  { destruct (Z_lt_le_dec Dd (S + nZ)) as [L1|G1]; [| left; lia]. destruct (Z_lt_le_dec S (Dd + nZ)) as [L2|G2]; [| right; lia].
    exfalso. apply (so_disj _ _ _ _ _ _ HS ka ra kd rd FA FD ltac:(intros Q; apply NKK; symmetry; exact Q) Ka0 Kd0 (or_introl RWa) (Z.max Dd S)).
    unfold loZ. rewrite LOa, LOd, KZ0. fold Dd Db. unfold S in *. lia. }
  idtac "SK-1".

  assert (EA0 : bv_unsigned (AP.getr R (reg_of_r5 X10)) = Dd).
  { unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10), G10, HeapCtr.TwinB.den_VPz. reflexivity. }
  assert (EA1 : bv_unsigned (AP.getr R (reg_of_r5 X11)) = S).
  { unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X11), (MemcpyCtr.TwinB.sym_offset_sound E (s_regs st) _ kd OFF DO).
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
  idtac "SK-2".
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
  -
    intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV'' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    destruct HQ as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK' & DSTP & SRCP).
    rewrite EA0', EA2' in MU, DSTP.
    match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
    set (Fv := CtrFree.TwinB.cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0). set (E' := CtrFrame.TwinB.E' E st Fv Gv).
    destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
    assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
    { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X1, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X1), Hra0, ER.
      assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.TwinB.den_wlit. }
    assert (EMS' : ms' = CtrFrame.TwinB.ms' ms r R' m').
    { rewrite EMS. unfold CtrFrame.TwinB.ms'. f_equal. rewrite RAEQ. apply ret_pc_even.
      - pose proof (int_range r) as RRr. rewrite two63_eq in RRr. lia.
      - pose proof (HeapCtr.TwinB.call_pre_even st r CP) as EVn.
        pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
        change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EVn in LM. change (to_Z 0%uint63) with 0 in LM.
        change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
    destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & NXc).
    destruct (CtrFrame.TwinB.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
    destruct (CtrFrame.TwinB.SVB_parts st FOK) as (RFB & _ & _ & _ & _ & OPB).
    assert (VB10 : sv_vars_below (s_next st) (getr st X10) = true) by exact (PlanS.rf_allb_get _ _ _ RFB X10).
    assert (DVP : den E' (getr st X10) = AP.getr R' 10%bv).
    { unfold E'. rewrite (CtrFrame.TwinB.den_E' E st Fv Gv _ VB10). symmetry. exact (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10). }
    assert (CF2 : CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw).
    { exists LB0, ks0, offs, rss, ksp, nn, md, A, nw, rest. repeat (split; [assumption|]). exists W. repeat (split; [assumption|]). assumption. }

    pose proof (phaseA_ms AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                  st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' Dd nZ 2240 (getr st X10) (s_next (clobber st1)) HS CP FS CF2 AH BOT LO SPT
                  ltac:(unfold AIMG_HI in *; lia) (or_introl HId) ltac:(lia) MU WM MI MINV' STK'
                  ltac:(intros rg Hrg; unfold CtrFrame.TwinB.kept_regsA in Hrg; cbn [In] in Hrg; repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]); destruct Hrg)
                  DVP OTH HMI' ACP) as HSA.
    fold Fv Gv E' in HSA. fold m in HSA.
    set (mj := mjoinR Dd (Dd + nZ) m m') in *.
    idtac "SK-A".
    destruct (CallA.TwinB.sp_region_inv st ks0 offs rss SPR) as (_ & Hrs & _).
    assert (NKS : ka <> ks0).
    { intros Q. rewrite Q, Hrs in FA. injection FA as Q2. rewrite Q2 in FLOOR. unfold loZ in FLOOR. rewrite LOa, KZ0 in FLOOR.
      rewrite <- Q in FLOOR. fold Dd in FLOOR. lia. }
    assert (FA1 : IMap.find ka (s_regs st1) = Some ra).
    { rewrite (CtrFrame.TwinB.st1_regs st st1 FS ks0 offs rss ksp SPR Hksp).
      rewrite IMap.find_add_other; [exact FA| exact (so_bst _ _ _ _ _ _ HS)| intros Q; apply NKS; symmetry; exact Q]. }

    destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw ka wlena kda 0 wlenZ CF2 WLa KTa
                NF7a NF8a (client_kind_range kda CKa) ltac:(lia) ltac:(lia) ltac:(unfold wlenZ; lia)) as (p & Ab & nb & HINB & BA1 & BA2).
  pose proof (W_PAT E st ms mo r hargs wnl L RNG sta LBa aw ka wlena kda p Ab nb HS CF2 AH WLa KTa NF7a NF8a PKa 0 wlenZ ltac:(lia) ltac:(lia) ltac:(unfold wlenZ; lia) HINB BA1 BA2) as PAT_p.
    fold Dd in BA1, BA2.
    assert (UBW : forall a, Dd <= a < Dd + wlenZ -> uband a).
    { intros a Ha. exact (Op.TwinB.blk_band AI AI_fake L RNG sta LBa m (HB p Ab nb) a AH HINB ltac:(cbn [ab_addr ab_size]; lia)). }
    assert (A64 : forall a, Dd <= a < Dd + wlenZ -> 0 <= a < 2 ^ 64 /\ 0x631000 <= a).
    { intros a Ha. pose proof (UBW a Ha) as U. unfold uband, AIMG_HI, KLS in U. lia. }
    destruct (CtrFrame.TwinB.reg_E' OPS E st ms mo HS FOK Fv Gv ka ra FA) as (EKa & EHa & _). fold E' in EKa, EHa.
    assert (OUTSIDE : forall a, 0 <= a < 2 ^ 64 -> ~ (Dd <= a < Dd + nZ) -> mj (AM.wa a) = m' (AM.wa a)).
    { intros a Ha N. unfold mj, mjoinR. rewrite (ReadPost.TwinB.wa_u a Ha). unfold in_rng. replace ((Dd <=? a) && (a <? Dd + nZ)) with false by lia. reflexivity. }
    pose proof (so_reg _ _ _ _ _ _ HSA ka ra FA1) as ROj. cbn [s_priv] in ROj. change (ms_mem (CtrFrame.TwinB.ms' ms r R' mj)) with mj in ROj.
    assert (MAPPED : forall a, Dd <= a < Dd + hiZ E ra -> m' (Z_to_bv 64 a) <> None).
    { intros a Ha. destruct (A64 a ltac:(lia)) as [AR A6].
      destruct (Z_lt_le_dec a (Dd + nZ)) as [IN|OUT].
      - destruct DSTP as [[_ BY] _]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. destruct BY as (_ & _ & BY).
        pose proof (BY (Z.to_nat (a - Dd)) ltac:(rewrite LSRC; lia)) as B1. replace (Dd + Z.of_nat (Z.to_nat (a - Dd))) with a in B1 by lia.
        destruct (nth_error src (Z.to_nat (a - Dd))) as [b|] eqn:NE; [| apply nth_error_None in NE; lia].
        rewrite <- (GlueA.TwinB.rb_mrdA bsegs) in B1. rewrite (raw_of_view m' a b ltac:(lia) B1). discriminate.
      - destruct (ro_valid _ _ _ _ _ _ ROj Ka0 a ltac:(rewrite EKa, EHa; unfold loZ; rewrite LOa, KZ0; fold Dd; lia)) as (V1 & _).
        destruct (rb bsegs mj a) as [b|] eqn:RBj; [| exfalso; exact (V1 eq_refl)].
        pose proof (raw_of_view mj a b ltac:(lia) RBj) as RAWj. change (Z_to_bv 64 a) with (AM.wa a) in RAWj |- *.
        rewrite (OUTSIDE a AR ltac:(lia)) in RAWj. rewrite RAWj. discriminate. }
    assert (RO' : region_ok bsegs (s_priv st) E' m' ka ra).
    { apply (region_ok_claimless (s_priv st) E' mj m' ka ra CBa BGa ROj). intros a Ha. rewrite EKa, EHa in Ha. unfold loZ in Ha. rewrite LOa, KZ0 in Ha. fold Dd in Ha.
      pose proof (MAPPED a ltac:(lia)) as MP1. destruct (A64 a ltac:(lia)) as [AR A6]. split.
      - unfold rb. destruct (m' (Z_to_bv 64 a)); [discriminate| exfalso; exact (MP1 eq_refl)].
      - intros _. apply (GlueA.TwinB.wb_wviewA bsegs). rewrite (BImg.ref_wview_overlay m' (AM.wa a)); [exact MP1|]. right. rewrite (ReadPost.TwinB.wa_u a AR). lia. }
    idtac "SK-B0".
    assert (ARGT : forall o, In o (s_ops st) -> map (den E') (op_args o) = map (den E) (op_args o)).
    { intros o Ho. apply (CtrFrame.TwinB.map_den_E' E st Fv Gv). exact (proj1 (forallb_forall _ _) OPB o Ho). }
    assert (HS1 : st_ok bsegs OPS E'
              (SS r (rf_set (s_rf (clobber st1)) X10 (getr st X10)) (s_ff st) (s_resv st) (IMap.add ka ra (s_regs st1)) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1)))
              (MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None m' (seg_rom bsegs)) mo').
    { apply (st_ok_based_replace_g bsegs OPS E' _ R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None mj m' (seg_rom bsegs) mo' ka ra ra HSA FA1 Ka0).
      - intros a Ha NC. unfold two64 in Ha. cbn [s_regs s_ops] in *.
        assert (INR : Dd <= a < Dd + hiZ E ra).
        { destruct NC as [RGa|CH]; [rewrite EHa, EKa in RGa; unfold loZ in RGa; rewrite LOa, KZ0 in RGa; fold Dd in RGa; lia|].
          destruct (Z_lt_le_dec a Dd) as [L1|G1]; [exfalso; apply CH; symmetry; apply (OUTSIDE a ltac:(lia)); lia|].
          destruct (Z_lt_le_dec a (Dd + nZ)) as [L2|G2]; [lia| exfalso; apply CH; symmetry; apply (OUTSIDE a ltac:(lia)); lia]. }
        assert (INB : Dd <= a < Dd + wlenZ) by lia.
        pose proof (UBW a INB) as UB. split; [| split].
        + intros k2 r2 H2 NK2 K20 RG2.
          apply (so_disj _ _ _ _ _ _ HSA ka ra k2 r2 FA1 H2 ltac:(intros Q; apply NK2; symmetry; exact Q) Ka0 K20 (or_introl RWa) a).
          split; [rewrite EKa, EHa; unfold loZ; rewrite LOa, KZ0; fold Dd; lia| exact RG2].
        + exact (UnreggPre.TwinB.no_seg_above a (proj2 (A64 a INB))).
        + intros o Ho FP. rewrite (ARGT o Ho) in FP.
          exact (zone_ops_k E st ms mo r hargs wnl L RNG sta LBa aw ka wlena kda a CF2 WLa ltac:(unfold two64; lia) INB UB o Ho FP).
      - intros x H. unfold mj, mjoinR in H. destruct (in_rng Dd (Dd + nZ) (bv_unsigned x)) eqn:IS; [| exact H].
        unfold in_rng in IS. rewrite <- (Z_to_bv_bv_unsigned x). apply MAPPED. lia.
      - intros x b Hx seg Hs. pose proof (MINV' x b Hx) as RO. unfold AM.ro_addr in RO. rewrite Hs in RO. apply negb_false_iff in RO. exact RO.
      - exact RO'.
      - intros a RGa. rewrite EHa, EKa in RGa. unfold loZ in RGa. rewrite LOa, KZ0 in RGa. fold Dd in RGa. right. apply Exists_exists. exists (HEAP_ID, map (den E') hargs). split.
        + unfold insts. apply in_map_iff. exists (OpI HEAP_ID hargs). split; [reflexivity|]. cbn [s_ops]. exact (UnreggPre.TwinB.find_op_In _ _ _ Hf).
        + cbn [fst snd]. apply OPS_cov1. split; [reflexivity|]. eexists _, _, _, _.
          split; [exact (CtrFrame.TwinB.DEC' E st FOK Fv Gv nn rest hargs md A nw Hf Eh Tnw Nn Ln)| left].
          unfold in_ws, heap_ws. apply in_ivs_In. eexists. split; [apply in_map; apply filter_In; split; [exact INWa|]|].
          * cbn [w_kind]. apply negb_true_iff. apply Z.eqb_neq. exact KDa.
          * unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. fold Dd wlenZ. lia. }
    idtac "SK-B1".

    assert (HS2 : st_ok bsegs OPS E'
              (SS r (rf_set (s_rf (clobber st1)) X10 (getr st X10)) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1)))
              (MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None m' (seg_rom bsegs)) mo').
    { apply (st_ok_regs_ext OPS E' _ _ _ _ (IMap.add ka ra (s_regs st1)) (s_regs st1) _ _ _ _ _ _ (so_bst _ _ _ _ _ _ HSA)); [| exact HS1].
      intros k. destruct (Uint63.eqb ka k) eqn:Q.
      - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_add_same by exact (so_bst _ _ _ _ _ _ HSA). exact FA1.
      - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other by (exact (so_bst _ _ _ _ _ _ HSA) || exact Q). reflexivity. }
    assert (SH2 : sink_state st st1 r
                = SS r (rf_set (s_rf (clobber st1)) X10 (getr st X10)) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1))).
    { unfold sink_state. rewrite <- FF1, <- RV1, <- FS1, <- OP1, <- PV1, <- FF, <- RV, <- RG, <- FS0, <- OP, <- PV. destruct (clobber st1); reflexivity. }
    apply (HK _ (or_introl eq_refl) E' ms' mo' (CtrFrame.TwinB.EXT E st Fv Gv) HMP').
    rewrite EMS'. unfold CtrFrame.TwinB.ms'. rewrite SH2. exact HS2.
Qed.
End Sound.
End TwinB.
