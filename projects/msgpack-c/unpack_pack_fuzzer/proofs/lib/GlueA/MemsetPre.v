(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require GlueA CtrPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggLib UnreggPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RangeC.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module SH := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.

Section Facts.
Context {rc : runConstT}.
Variable AI : AMallocIface2.

Lemma block_range_facts : forall L RNG sta LBa (m : amem) p A nb A0 n,
  AHEAP AI L RNG sta LBa m -> In (HB p A nb) LBa -> ablock_shadow m A nb -> A <= A0 -> A0 + n <= A + nb -> 1 <= n ->
  (exists junk, AS.rw_cells asegs m A0 [CB (Z.to_nat n) junk])
  /\ SH.app_blk A0 (A0 + n) /\ SH.unpoisoned m A0 (A0 + n)
  /\ AIMG_HI <= A0 /\ A0 + n <= ATOP /\ rng RNG A0 n
  /\ exists RLO2 RHI2, (RLO2 <= A0 /\ A0 + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= SH.KEND)
       /\ AM.wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) /\ rng RNG (shad RLO2) (shad RHI2 - shad RLO2).
Proof.
  intros L RNG sta LBa m p A nb A0 n AH HIN SHB LE1 LE2 N1.
  destruct (AI_block AI L RNG sta LBa m p A nb AH HIN) as (NB & (BK & N0 & HI & AL) & RB & RSH & _ & WR & _ & RLO & RHI & P1 & P2 & Q1 & Q2 & RH & WH).
  pose proof atop_range as ATR.
  assert (LOW : AIMG_HI <= A) by (unfold ablk, AIMG_HI, KLS in *; lia).
  destruct WR as (W0 & W1 & WV).
  split; [| split; [| split; [| split; [lia| split; [lia| split; [eapply rng_sub'; [exact RB| lia]|]]]]]].
  -
    apply (UnreggLib.mapped_chunk asegs); [unfold AIMG_HI in *; lia | rewrite Z2Nat.id by lia; lia |].
    intros i Hi. rewrite Z2Nat.id in Hi by lia.
    assert (WBI : FX.State.St.wb asegs m (A0 + i) = true).
    { apply (GlueA.wb_wviewA asegs). replace (A0 + i) with (A + (A0 - A + i)) by lia. apply WV. lia. }
    split; [exact WBI|]. apply UnreggPre.shmap_rb; [unfold AIMG_HI in *; lia| exact WBI].
  -
    unfold SH.app_blk, SH.KLOW, SH.KHIGH, SH.KEND. split; [lia|]. unfold ablk, AIMG_HI, KLS in BK. destruct BK as [[B1 B2]|[B1 B2]]; [left| right]; lia.
  -
    unfold SH.unpoisoned. split; [unfold AIMG_HI in *; lia|]. split; [lia|]. intros G _ G1 G2.
    assert (A8 : A = 8 * (A / 8)) by (Z.div_mod_to_equations; lia).
    set (g := G - A / 8).
    assert (Gg : 0 <= g /\ 8 * g < nb) by (unfold g; lia).
    pose proof (SHB g (proj1 Gg) (proj2 Gg)) as SB.
    replace (shad A + g) with (ASHOFF + G) in SB by (unfold shad, g; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; lia).
    eexists. split; [exact SB|]. unfold SH.gran_ok, SH.sval.
    destruct (8 * g + 8 <=? nb) eqn:Q.
    + left. reflexivity.
    + right. apply Z.leb_gt in Q.
      assert (SV : bv_signed (Z_to_bv 8 (nb - 8 * g)) = nb - 8 * g).
      { unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
        change (2 ^ Z.of_N 8) with 256. change (256 / 2) with 128. rewrite (Z.mod_small (nb - 8 * g)) by lia. rewrite Z.mod_small by lia. lia. }
      rewrite SV. lia.
  -
    exists (64 * (A0 / 64)), (64 * ((A0 + n + 63) / 64)).
    assert (H1 : 64 * (A0 / 64) <= A0 < 64 * (A0 / 64) + 64) by (Z.div_mod_to_equations; lia).
    assert (H2 : A0 + n <= 64 * ((A0 + n + 63) / 64) < A0 + n + 64) by (Z.div_mod_to_equations; lia).
    assert (R64 : RLO mod 64 = 0 /\ RHI mod 64 = 0) by (split; Z.div_mod_to_equations; lia).
    assert (H3 : RLO <= 64 * (A0 / 64)) by (Z.div_mod_to_equations; lia).
    assert (H4 : 64 * ((A0 + n + 63) / 64) <= RHI) by (Z.div_mod_to_equations; lia).
    split.
    { split; [lia|]. split; [lia|]. split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|]. split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|].
      split; [unfold AIMG_HI in *; lia| unfold SH.KEND; lia]. }
    assert (SHE : forall x, shad x = ASHOFF + x / 8) by (intros x; unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (SL : shlen (RHI - RLO) = (RHI - RLO) / 8) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (B1 : shad RLO <= shad (64 * (A0 / 64))) by (rewrite !SHE; Z.div_mod_to_equations; lia).
    assert (B2 : shad (64 * ((A0 + n + 63) / 64)) <= shad RLO + shlen (RHI - RLO)).
    { rewrite SL, !SHE. Z.div_mod_to_equations; lia. }
    assert (B0 : shad (64 * (A0 / 64)) <= shad (64 * ((A0 + n + 63) / 64))) by (rewrite !SHE; Z.div_mod_to_equations; lia).
    split; [| eapply rng_sub'; [exact RH| lia]].
    destruct WH as (V0 & V1 & VV). split; [lia|]. split; [lia|]. intros i Hi.
    replace (shad (64 * (A0 / 64)) + i) with (shad RLO + (shad (64 * (A0 / 64)) - shad RLO + i)) by lia. apply VV. lia.
Qed.

Lemma block_range_cells : forall L RNG sta LBa (m : amem) p A nb A0 n,
  AHEAP AI L RNG sta LBa m -> In (HB p A nb) LBa -> A <= A0 -> A0 + n <= A + nb -> 1 <= n ->
  exists junk, AS.rw_cells asegs m A0 [CB (Z.to_nat n) junk].
Proof.
  intros L RNG sta LBa m p A nb A0 n AH HIN LE1 LE2 N1.
  destruct (AI_block AI L RNG sta LBa m p A nb AH HIN) as (NB & (BK & N0 & HI & AL) & RB & RSH & _ & WR & _).
  pose proof atop_range as ATR.
  assert (LOW : AIMG_HI <= A) by (unfold ablk, AIMG_HI, KLS in *; lia).
  destruct WR as (W0 & W1 & WV).
  apply (UnreggLib.mapped_chunk asegs); [unfold AIMG_HI in *; lia | rewrite Z2Nat.id by lia; lia |].
  intros i Hi. rewrite Z2Nat.id in Hi by lia.
  assert (WBI : FX.State.St.wb asegs m (A0 + i) = true).
  { apply (GlueA.wb_wviewA asegs). replace (A0 + i) with (A + (A0 - A + i)) by lia. apply WV. lia. }
  split; [exact WBI|]. apply UnreggPre.shmap_rb; [unfold AIMG_HI in *; lia| exact WBI].
Qed.

Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.

Hypothesis AI_fake : AI_fake_law AI.

Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.

Lemma pat_ok_kind_range : forall st wl k kind, RangeC.RangeC.pat_ok st wl k kind = true -> K_BLOCK <= W64.w2Z kind < K_GHOST.
Proof.
  intros st wl k kind H. unfold RangeC.RangeC.pat_ok in H. destruct (W64.weqb kind CtrLib.K_BLOCK) eqn:KB.
  - apply ValProofs.ValP.weqb_eq in KB. subst kind. vm_compute. split; [discriminate| reflexivity].
  - apply orb_prop in H as [H|H]; apply ValProofs.ValP.weqb_eq in H; subst kind; vm_compute; (split; [discriminate| reflexivity]).
Qed.

Lemma win_noframe_k : forall W md ca LB ws m w fw, ties W ws -> cw_holds Cw md ca LB ws m -> In w ws -> In fw ws -> w_kind fw = K_FRAMEz ->
  K_BLOCK <= w_kind w < K_GHOST -> forall a, in_iv (w_iv w) a -> ~ in_iv (w_iv fw) a.
Proof.
  intros W md ca LB ws m w fw TI HC INW INF KF KR a IA IF.
  destruct TI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GA & _).
  destruct (Z.eq_dec (w_kind w) K_BLOCK) as [KB|KB].
  - exact (GA fw w INF INW ltac:(rewrite KF; unfold K_GHOST, K_FRAMEz; lia) KB a IF IA).
  - exact (Cw_sub_ghost md ca LB ws m w fw a HC INW INF ltac:(unfold K_SUB, K_BLOCK in *; lia) ltac:(rewrite KF; unfold K_GHOST, K_FRAMEz; lia) IA IF).
Qed.

Lemma win_user_k : forall W aw LB m mo ws ceil md ca w,
  aw_holds_w AI ACCT UNIV W aw LB m mo -> ties W ws -> windows_wf ws LB ceil -> cw_holds Cw md ca LB ws m ->
  In w ws -> K_BLOCK <= w_kind w < K_GHOST -> 0 < w_len w -> user_band (w_lo w).
Proof.
  intros W aw LB m mo ws ceil md ca w HWW TI WF HC INW KR WP.
  destruct (LB_classify AI ACCT UNIV AI_fake W aw LB m mo HWW) as [CLU CLS].
  destruct TI as (T1 & _ & T3 & _ & _ & _ & _ & _ & _ & GA & _).
  assert (IA : in_iv (w_iv w) (w_lo w)) by (unfold in_iv, w_iv; cbn [fst snd]; lia).

  assert (GH : forall v, In v LB -> ~ user_band (fst v) -> exists g, In g ws /\ K_GHOST <= w_kind g /\ w_iv g = v).
  { intros v Hv NU. destruct (CLS v Hv NU) as [(tb & HtT & ->)|(fb & Vfb & ->)].
    - exists (Win (shad (ab_addr tb)) (shlen (ab_size tb + 7)) K_TWINz). split; [exact (T1 tb HtT)|]. split; [cbn [w_kind]; unfold K_GHOST, K_TWINz; lia| reflexivity].
    - exists (Win (shad (ab_addr fb)) (shlen (ab_size fb)) K_FTWINz). split; [exact (proj2 (T3 fb Vfb))|]. split; [cbn [w_kind]; unfold K_GHOST, K_FTWINz; lia| reflexivity]. }
  assert (DEC : forall A, user_band A \/ ~ user_band A).
  { intros A. unfold user_band. destruct (Z_lt_le_dec A 0x7fff8000); [left; left; assumption|]. destruct (Z_lt_le_dec A 0x10007fff8000); [right; lia| left; right; assumption]. }
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]).
  - exfalso. unfold K_STACK, K_BLOCK in *. lia.
  - destruct (DEC (w_lo w)) as [U|NU]; [exact U| exfalso].
    destruct (GH _ B NU) as (g & INg & Kg & EQg).
    apply (GA g w INg INW Kg KB (w_lo w)); [rewrite EQg; exact IA| exact IA].
  - assert (UBb : user_band (fst b)).
    { destruct (DEC (fst b)) as [U|NU]; [exact U| exfalso].
      destruct (GH _ Hb NU) as (g & INg & Kg & EQg).
      apply (Cw_sub_ghost md ca LB ws m w g (w_lo w) HC INW INg ltac:(lia) Kg IA). rewrite EQg. exact (SUB _ IA). }
    pose proof (SUB _ IA) as INB.
    assert (PB : 0 < snd b) by (unfold in_iv in INB; lia).
    destruct (CLU _ Hb UBb PB) as (hb & Vhb & ->).
    destruct (LB_user_facts AI ACCT UNIV AI_fake W aw LB m mo hb HWW Vhb) as (_ & BAND & _ & _).
    pose proof (usz_le hb) as UZ. unfold in_iv, user_iv in INB. cbn [fst snd] in INB. unfold user_band. lia.
Qed.

Lemma window_block_k : forall E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind lo hi,
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  CtrA.win_lookup wnl kd = Some (wlen, kind) -> W64.weqb kind ActrA.K_TWIN = false ->
  W64.w2Z kind <> K_FRAMEz -> W64.w2Z kind <> K_FTWINz -> K_BLOCK <= W64.w2Z kind < K_GHOST ->
  0 <= lo -> lo < hi -> hi <= bv_unsigned (Val.den E wlen) ->
  exists p A nb, In (HB p A nb) LBa /\ A <= bv_unsigned (Val.ev E kd) + lo /\ bv_unsigned (Val.ev E kd) + hi <= A + nb.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind lo hi CF WL NT NF7 NF8 KR L0 LH HW.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (HeapCtrB.nonstack_windows_In E nn rest wnl kd wlen kind NW (HeapCtrB.win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
  set (w := Win (bv_unsigned (Val.ev E kd)) (bv_unsigned (Val.den E wlen)) (W64.w2Z kind)) in *.
  assert (KT : w_kind w <> K_TWINz).
  { cbn [w_kind w]. intros Q. rewrite weqb_eqb in NT. apply Z.eqb_neq in NT. apply NT. rewrite Q. reflexivity. }
  assert (KS : w_kind w <> K_STACK) by (cbn [w_kind w]; unfold K_STACK; exact KD).
  destruct ARW as [HWW EMW]. destruct WOF as (E1 & E2 & E3 & E4).
  pose proof (win_user_k W aw LB (ms_mem ms) mo _ _ _ _ w HWW TI WF HC INW ltac:(cbn [w_kind w]; exact KR) ltac:(cbn [w_len w]; lia)) as UB. cbn [w_lo w] in UB.
  destruct (LB_classify AI ACCT UNIV AI_fake W aw LB (ms_mem ms) mo HWW) as [CLU CLS].
  pose proof TI as TI0. destruct TI as (_ & _ & T3 & _).

  assert (HEAPB : forall b, vis W b -> (forall a, in_iv (w_iv w) a -> in_iv (user_iv b) a) -> exists p, b = HB p (ab_addr b) (ab_size b) /\ usz b = ab_size b).
  { intros b Vb SUBb. destruct (kind_cases b) as [[p Hp]|HF].
    - exists p. split; [| exact (usz_heap b (ex_intro _ p Hp))]. destruct b as [kk aa nn0]. cbn [ab_kind ab_addr ab_size] in *. subst kk. reflexivity.
    - exfalso. destruct (T3 b (conj Vb HF)) as [INF _].
      set (a0 := bv_unsigned (Val.ev E kd) + lo).
      assert (IA : in_iv (w_iv w) a0) by (unfold in_iv, w_iv, a0; cbn [fst snd w_lo w_len w]; lia).
      apply (win_noframe_k W _ _ _ _ _ w _ TI0 HC INW INF eq_refl ltac:(cbn [w_kind w]; exact KR) a0 IA).
      unfold w_iv. cbn [w_lo w_len]. pose proof (SUBb a0 IA) as SB0. unfold user_iv in SB0. rewrite (usz_fake b HF) in SB0. exact SB0. }
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len w] in *.
  - exfalso. exact (KD KS0).
  - destruct (CLU _ B ltac:(cbn [fst]; exact UB) ltac:(cbn [snd]; lia)) as (hb & Vhb & EQ).
    destruct (HEAPB hb Vhb ltac:(intros a Ha; rewrite <- EQ; exact Ha)) as (p & EHB & USZ).
    unfold user_iv in EQ. rewrite USZ in EQ. injection EQ as EQ1 EQ2.
    exists p, (ab_addr hb), (ab_size hb). split; [rewrite <- EHB, <- E4; exact (proj1 Vhb)| lia].
  - assert (INB : in_iv b (bv_unsigned (Val.ev E kd))) by (apply SUB; unfold in_iv; cbn [fst snd]; lia).
    assert (UBb : user_band (fst b)).
    { destruct (Z_lt_le_dec (fst b) 0x7fff8000) as [Q|Q]; [left; exact Q|].
      destruct (Z_lt_le_dec (fst b) 0x10007fff8000) as [Q'|Q']; [| right; exact Q'].
      exfalso. assert (NU : ~ user_band (fst b)) by (unfold user_band; lia).
      unfold in_iv in INB. unfold user_band in UB.
      destruct (CLS b Hb NU) as [(tb & HtT & ->)|(fb & Vfb & ->)].
      - destruct (LB_twin_facts AI ACCT UNIV W aw LB (ms_mem ms) mo tb HWW HtT) as (T1 & T2 & _).
        unfold twin_iv in INB. cbn [fst snd] in INB. lia.
      - destruct (LB_fsh_facts AI ACCT UNIV AI_fake W aw LB (ms_mem ms) mo fb HWW Vfb) as (T1 & T2 & _).
        unfold fsh_iv in INB. cbn [fst snd] in INB. lia. }
    assert (PB : 0 < snd b) by (unfold in_iv in INB; lia).
    destruct (CLU _ Hb UBb PB) as (hb & Vhb & EQ). subst b.
    destruct (HEAPB hb Vhb SUB) as (p & EHB & USZ).
    exists p, (ab_addr hb), (ab_size hb). split; [rewrite <- EHB, <- E4; exact (proj1 Vhb)|].
    pose proof (SUB (bv_unsigned (Val.ev E kd) + lo) ltac:(unfold in_iv; cbn [fst snd]; lia)) as I1.
    pose proof (SUB (bv_unsigned (Val.ev E kd) + hi - 1) ltac:(unfold in_iv; cbn [fst snd]; lia)) as I2.
    unfold in_iv, user_iv in I1, I2. rewrite USZ in I1, I2. cbn [fst snd] in I1, I2. lia.
Qed.

Variable OPS : FX.State.St.optable.
Definition w_pat_ev_stmt : Prop :=
  forall E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb,
  FX.State.St.st_ok asegs OPS E st ms mo ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) ->
  CtrA.win_lookup wnl kd = Some (wlen, kind) -> W64.weqb kind ActrA.K_TWIN = false ->
  W64.w2Z kind <> K_FRAMEz -> W64.w2Z kind <> K_FTWINz ->
  RangeC.RangeC.pat_ok st wnl kd kind = true ->
  forall lo hi, 0 <= lo -> lo < hi -> hi <= bv_unsigned (Val.den E wlen) ->
  In (HB p A nb) LBa -> A <= bv_unsigned (Val.ev E kd) + lo -> bv_unsigned (Val.ev E kd) + hi <= A + nb ->
  ablock_shadow (ms_mem ms) A nb.

Definition w_pat_sub_stmt : Prop :=
  forall E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb,
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  CtrA.win_lookup wnl kd = Some (wlen, kind) -> W64.weqb kind ActrA.K_TWIN = false -> W64.weqb kind CtrLib.K_BLOCK = false ->
  W64.w2Z kind <> K_FRAMEz -> W64.w2Z kind <> K_FTWINz ->
  (W64.weqb kind RangeC.RangeC.K_SLOT || W64.weqb kind RangeC.RangeC.K_ZONE)%bool = true ->
  forall lo hi, 0 <= lo -> lo < hi -> hi <= bv_unsigned (Val.den E wlen) ->
  In (HB p A nb) LBa -> A <= bv_unsigned (Val.ev E kd) + lo -> bv_unsigned (Val.ev E kd) + hi <= A + nb ->
  ablock_shadow (ms_mem ms) A nb.
End Facts.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB.
Import AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import Ledger.TwinB Op.TwinB.
Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module SH := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.

Section Facts.
Context {rc : runConstT}.
Variable AI : AMallocIface2.

Lemma block_range_facts : forall L RNG sta LBa (m : amem) p A nb A0 n,
  AHEAP AI L RNG sta LBa m -> In (HB p A nb) LBa -> ablock_shadow m A nb -> A <= A0 -> A0 + n <= A + nb -> 1 <= n ->
  (exists junk, AS.rw_cells bsegs m A0 [CB (Z.to_nat n) junk])
  /\ SH.app_blk A0 (A0 + n) /\ SH.unpoisoned m A0 (A0 + n)
  /\ AIMG_HI <= A0 /\ A0 + n <= ATOP /\ rng RNG A0 n
  /\ exists RLO2 RHI2, (RLO2 <= A0 /\ A0 + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= SH.KEND)
       /\ AM.wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2) /\ rng RNG (shad RLO2) (shad RHI2 - shad RLO2).
Proof.
  intros L RNG sta LBa m p A nb A0 n AH HIN SHB LE1 LE2 N1.
  destruct (AI_block AI L RNG sta LBa m p A nb AH HIN) as (NB & (BK & N0 & HI & AL) & RB & RSH & _ & WR & _ & RLO & RHI & P1 & P2 & Q1 & Q2 & RH & WH).
  pose proof atop_range as ATR.
  assert (LOW : AIMG_HI <= A) by (unfold ablk, AIMG_HI, KLS in *; lia).
  destruct WR as (W0 & W1 & WV).
  split; [| split; [| split; [| split; [lia| split; [lia| split; [eapply rng_sub'; [exact RB| lia]|]]]]]].
  -
    apply (UnreggLib.TwinB.mapped_chunk bsegs); [unfold AIMG_HI in *; lia | rewrite Z2Nat.id by lia; lia |].
    intros i Hi. rewrite Z2Nat.id in Hi by lia.
    assert (WBI : FX.State.St.wb bsegs m (A0 + i) = true).
    { apply (GlueA.TwinB.wb_wviewA bsegs). replace (A0 + i) with (A + (A0 - A + i)) by lia. apply WV. lia. }
    split; [exact WBI|]. apply UnreggPre.TwinB.shmap_rb; [unfold AIMG_HI in *; lia| exact WBI].
  -
    unfold SH.app_blk, SH.KLOW, SH.KHIGH, SH.KEND. split; [lia|]. unfold ablk, AIMG_HI, KLS in BK. destruct BK as [[B1 B2]|[B1 B2]]; [left| right]; lia.
  -
    unfold SH.unpoisoned. split; [unfold AIMG_HI in *; lia|]. split; [lia|]. intros G _ G1 G2.
    assert (A8 : A = 8 * (A / 8)) by (Z.div_mod_to_equations; lia).
    set (g := G - A / 8).
    assert (Gg : 0 <= g /\ 8 * g < nb) by (unfold g; lia).
    pose proof (SHB g (proj1 Gg) (proj2 Gg)) as SB.
    replace (shad A + g) with (ASHOFF + G) in SB by (unfold shad, g; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; lia).
    eexists. split; [exact SB|]. unfold SH.gran_ok, SH.sval.
    destruct (8 * g + 8 <=? nb) eqn:Q.
    + left. reflexivity.
    + right. apply Z.leb_gt in Q.
      assert (SV : bv_signed (Z_to_bv 8 (nb - 8 * g)) = nb - 8 * g).
      { unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
        change (2 ^ Z.of_N 8) with 256. change (256 / 2) with 128. rewrite (Z.mod_small (nb - 8 * g)) by lia. rewrite Z.mod_small by lia. lia. }
      rewrite SV. lia.
  -
    exists (64 * (A0 / 64)), (64 * ((A0 + n + 63) / 64)).
    assert (H1 : 64 * (A0 / 64) <= A0 < 64 * (A0 / 64) + 64) by (Z.div_mod_to_equations; lia).
    assert (H2 : A0 + n <= 64 * ((A0 + n + 63) / 64) < A0 + n + 64) by (Z.div_mod_to_equations; lia).
    assert (R64 : RLO mod 64 = 0 /\ RHI mod 64 = 0) by (split; Z.div_mod_to_equations; lia).
    assert (H3 : RLO <= 64 * (A0 / 64)) by (Z.div_mod_to_equations; lia).
    assert (H4 : 64 * ((A0 + n + 63) / 64) <= RHI) by (Z.div_mod_to_equations; lia).
    split.
    { split; [lia|]. split; [lia|]. split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|]. split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|].
      split; [unfold AIMG_HI in *; lia| unfold SH.KEND; lia]. }
    assert (SHE : forall x, shad x = ASHOFF + x / 8) by (intros x; unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (SL : shlen (RHI - RLO) = (RHI - RLO) / 8) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (B1 : shad RLO <= shad (64 * (A0 / 64))) by (rewrite !SHE; Z.div_mod_to_equations; lia).
    assert (B2 : shad (64 * ((A0 + n + 63) / 64)) <= shad RLO + shlen (RHI - RLO)).
    { rewrite SL, !SHE. Z.div_mod_to_equations; lia. }
    assert (B0 : shad (64 * (A0 / 64)) <= shad (64 * ((A0 + n + 63) / 64))) by (rewrite !SHE; Z.div_mod_to_equations; lia).
    split; [| eapply rng_sub'; [exact RH| lia]].
    destruct WH as (V0 & V1 & VV). split; [lia|]. split; [lia|]. intros i Hi.
    replace (shad (64 * (A0 / 64)) + i) with (shad RLO + (shad (64 * (A0 / 64)) - shad RLO + i)) by lia. apply VV. lia.
Qed.

Lemma block_range_cells : forall L RNG sta LBa (m : amem) p A nb A0 n,
  AHEAP AI L RNG sta LBa m -> In (HB p A nb) LBa -> A <= A0 -> A0 + n <= A + nb -> 1 <= n ->
  exists junk, AS.rw_cells bsegs m A0 [CB (Z.to_nat n) junk].
Proof.
  intros L RNG sta LBa m p A nb A0 n AH HIN LE1 LE2 N1.
  destruct (AI_block AI L RNG sta LBa m p A nb AH HIN) as (NB & (BK & N0 & HI & AL) & RB & RSH & _ & WR & _).
  pose proof atop_range as ATR.
  assert (LOW : AIMG_HI <= A) by (unfold ablk, AIMG_HI, KLS in *; lia).
  destruct WR as (W0 & W1 & WV).
  apply (UnreggLib.TwinB.mapped_chunk bsegs); [unfold AIMG_HI in *; lia | rewrite Z2Nat.id by lia; lia |].
  intros i Hi. rewrite Z2Nat.id in Hi by lia.
  assert (WBI : FX.State.St.wb bsegs m (A0 + i) = true).
  { apply (GlueA.TwinB.wb_wviewA bsegs). replace (A0 + i) with (A + (A0 - A + i)) by lia. apply WV. lia. }
  split; [exact WBI|]. apply UnreggPre.TwinB.shmap_rb; [unfold AIMG_HI in *; lia| exact WBI].
Qed.

Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.

Hypothesis AI_fake : AI_fake_law AI.

Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.

Lemma pat_ok_kind_range : forall st wl k kind, RangeC.TwinB.RangeC.pat_ok st wl k kind = true -> K_BLOCK <= W64.w2Z kind < K_GHOST.
Proof.
  intros st wl k kind H. unfold RangeC.TwinB.RangeC.pat_ok in H. destruct (W64.weqb kind CtrLib.K_BLOCK) eqn:KB.
  - apply ValProofs.ValP.weqb_eq in KB. subst kind. vm_compute. split; [discriminate| reflexivity].
  - apply orb_prop in H as [H|H]; apply ValProofs.ValP.weqb_eq in H; subst kind; vm_compute; (split; [discriminate| reflexivity]).
Qed.

Lemma win_noframe_k : forall W md ca LB ws m w fw, ties W ws -> cw_holds Cw md ca LB ws m -> In w ws -> In fw ws -> w_kind fw = K_FRAMEz ->
  K_BLOCK <= w_kind w < K_GHOST -> forall a, in_iv (w_iv w) a -> ~ in_iv (w_iv fw) a.
Proof.
  intros W md ca LB ws m w fw TI HC INW INF KF KR a IA IF.
  destruct TI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GA & _).
  destruct (Z.eq_dec (w_kind w) K_BLOCK) as [KB|KB].
  - exact (GA fw w INF INW ltac:(rewrite KF; unfold K_GHOST, K_FRAMEz; lia) KB a IF IA).
  - exact (Cw_sub_ghost md ca LB ws m w fw a HC INW INF ltac:(unfold K_SUB, K_BLOCK in *; lia) ltac:(rewrite KF; unfold K_GHOST, K_FRAMEz; lia) IA IF).
Qed.

Lemma win_user_k : forall W aw LB m mo ws ceil md ca w,
  aw_holds_w AI ACCT UNIV W aw LB m mo -> ties W ws -> windows_wf ws LB ceil -> cw_holds Cw md ca LB ws m ->
  In w ws -> K_BLOCK <= w_kind w < K_GHOST -> 0 < w_len w -> user_band (w_lo w).
Proof.
  intros W aw LB m mo ws ceil md ca w HWW TI WF HC INW KR WP.
  destruct (LB_classify AI ACCT UNIV AI_fake W aw LB m mo HWW) as [CLU CLS].
  destruct TI as (T1 & _ & T3 & _ & _ & _ & _ & _ & _ & GA & _).
  assert (IA : in_iv (w_iv w) (w_lo w)) by (unfold in_iv, w_iv; cbn [fst snd]; lia).

  assert (GH : forall v, In v LB -> ~ user_band (fst v) -> exists g, In g ws /\ K_GHOST <= w_kind g /\ w_iv g = v).
  { intros v Hv NU. destruct (CLS v Hv NU) as [(tb & HtT & ->)|(fb & Vfb & ->)].
    - exists (Win (shad (ab_addr tb)) (shlen (ab_size tb + 7)) K_TWINz). split; [exact (T1 tb HtT)|]. split; [cbn [w_kind]; unfold K_GHOST, K_TWINz; lia| reflexivity].
    - exists (Win (shad (ab_addr fb)) (shlen (ab_size fb)) K_FTWINz). split; [exact (proj2 (T3 fb Vfb))|]. split; [cbn [w_kind]; unfold K_GHOST, K_FTWINz; lia| reflexivity]. }
  assert (DEC : forall A, user_band A \/ ~ user_band A).
  { intros A. unfold user_band. destruct (Z_lt_le_dec A 0x7fff8000); [left; left; assumption|]. destruct (Z_lt_le_dec A 0x10007fff8000); [right; lia| left; right; assumption]. }
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]).
  - exfalso. unfold K_STACK, K_BLOCK in *. lia.
  - destruct (DEC (w_lo w)) as [U|NU]; [exact U| exfalso].
    destruct (GH _ B NU) as (g & INg & Kg & EQg).
    apply (GA g w INg INW Kg KB (w_lo w)); [rewrite EQg; exact IA| exact IA].
  - assert (UBb : user_band (fst b)).
    { destruct (DEC (fst b)) as [U|NU]; [exact U| exfalso].
      destruct (GH _ Hb NU) as (g & INg & Kg & EQg).
      apply (Cw_sub_ghost md ca LB ws m w g (w_lo w) HC INW INg ltac:(lia) Kg IA). rewrite EQg. exact (SUB _ IA). }
    pose proof (SUB _ IA) as INB.
    assert (PB : 0 < snd b) by (unfold in_iv in INB; lia).
    destruct (CLU _ Hb UBb PB) as (hb & Vhb & ->).
    destruct (LB_user_facts AI ACCT UNIV AI_fake W aw LB m mo hb HWW Vhb) as (_ & BAND & _ & _).
    pose proof (usz_le hb) as UZ. unfold in_iv, user_iv in INB. cbn [fst snd] in INB. unfold user_band. lia.
Qed.

Lemma window_block_k : forall E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind lo hi,
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  CtrA.win_lookup wnl kd = Some (wlen, kind) -> W64.weqb kind ActrA.K_TWIN = false ->
  W64.w2Z kind <> K_FRAMEz -> W64.w2Z kind <> K_FTWINz -> K_BLOCK <= W64.w2Z kind < K_GHOST ->
  0 <= lo -> lo < hi -> hi <= bv_unsigned (Val.den E wlen) ->
  exists p A nb, In (HB p A nb) LBa /\ A <= bv_unsigned (Val.ev E kd) + lo /\ bv_unsigned (Val.ev E kd) + hi <= A + nb.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind lo hi CF WL NT NF7 NF8 KR L0 LH HW.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl kd wlen kind NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
  set (w := Win (bv_unsigned (Val.ev E kd)) (bv_unsigned (Val.den E wlen)) (W64.w2Z kind)) in *.
  assert (KT : w_kind w <> K_TWINz).
  { cbn [w_kind w]. intros Q. rewrite weqb_eqb in NT. apply Z.eqb_neq in NT. apply NT. rewrite Q. reflexivity. }
  assert (KS : w_kind w <> K_STACK) by (cbn [w_kind w]; unfold K_STACK; exact KD).
  destruct ARW as [HWW EMW]. destruct WOF as (E1 & E2 & E3 & E4).
  pose proof (win_user_k W aw LB (ms_mem ms) mo _ _ _ _ w HWW TI WF HC INW ltac:(cbn [w_kind w]; exact KR) ltac:(cbn [w_len w]; lia)) as UB. cbn [w_lo w] in UB.
  destruct (LB_classify AI ACCT UNIV AI_fake W aw LB (ms_mem ms) mo HWW) as [CLU CLS].
  pose proof TI as TI0. destruct TI as (_ & _ & T3 & _).

  assert (HEAPB : forall b, vis W b -> (forall a, in_iv (w_iv w) a -> in_iv (user_iv b) a) -> exists p, b = HB p (ab_addr b) (ab_size b) /\ usz b = ab_size b).
  { intros b Vb SUBb. destruct (kind_cases b) as [[p Hp]|HF].
    - exists p. split; [| exact (usz_heap b (ex_intro _ p Hp))]. destruct b as [kk aa nn0]. cbn [ab_kind ab_addr ab_size] in *. subst kk. reflexivity.
    - exfalso. destruct (T3 b (conj Vb HF)) as [INF _].
      set (a0 := bv_unsigned (Val.ev E kd) + lo).
      assert (IA : in_iv (w_iv w) a0) by (unfold in_iv, w_iv, a0; cbn [fst snd w_lo w_len w]; lia).
      apply (win_noframe_k W _ _ _ _ _ w _ TI0 HC INW INF eq_refl ltac:(cbn [w_kind w]; exact KR) a0 IA).
      unfold w_iv. cbn [w_lo w_len]. pose proof (SUBb a0 IA) as SB0. unfold user_iv in SB0. rewrite (usz_fake b HF) in SB0. exact SB0. }
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len w] in *.
  - exfalso. exact (KD KS0).
  - destruct (CLU _ B ltac:(cbn [fst]; exact UB) ltac:(cbn [snd]; lia)) as (hb & Vhb & EQ).
    destruct (HEAPB hb Vhb ltac:(intros a Ha; rewrite <- EQ; exact Ha)) as (p & EHB & USZ).
    unfold user_iv in EQ. rewrite USZ in EQ. injection EQ as EQ1 EQ2.
    exists p, (ab_addr hb), (ab_size hb). split; [rewrite <- EHB, <- E4; exact (proj1 Vhb)| lia].
  - assert (INB : in_iv b (bv_unsigned (Val.ev E kd))) by (apply SUB; unfold in_iv; cbn [fst snd]; lia).
    assert (UBb : user_band (fst b)).
    { destruct (Z_lt_le_dec (fst b) 0x7fff8000) as [Q|Q]; [left; exact Q|].
      destruct (Z_lt_le_dec (fst b) 0x10007fff8000) as [Q'|Q']; [| right; exact Q'].
      exfalso. assert (NU : ~ user_band (fst b)) by (unfold user_band; lia).
      unfold in_iv in INB. unfold user_band in UB.
      destruct (CLS b Hb NU) as [(tb & HtT & ->)|(fb & Vfb & ->)].
      - destruct (LB_twin_facts AI ACCT UNIV W aw LB (ms_mem ms) mo tb HWW HtT) as (T1 & T2 & _).
        unfold twin_iv in INB. cbn [fst snd] in INB. lia.
      - destruct (LB_fsh_facts AI ACCT UNIV AI_fake W aw LB (ms_mem ms) mo fb HWW Vfb) as (T1 & T2 & _).
        unfold fsh_iv in INB. cbn [fst snd] in INB. lia. }
    assert (PB : 0 < snd b) by (unfold in_iv in INB; lia).
    destruct (CLU _ Hb UBb PB) as (hb & Vhb & EQ). subst b.
    destruct (HEAPB hb Vhb SUB) as (p & EHB & USZ).
    exists p, (ab_addr hb), (ab_size hb). split; [rewrite <- EHB, <- E4; exact (proj1 Vhb)|].
    pose proof (SUB (bv_unsigned (Val.ev E kd) + lo) ltac:(unfold in_iv; cbn [fst snd]; lia)) as I1.
    pose proof (SUB (bv_unsigned (Val.ev E kd) + hi - 1) ltac:(unfold in_iv; cbn [fst snd]; lia)) as I2.
    unfold in_iv, user_iv in I1, I2. rewrite USZ in I1, I2. cbn [fst snd] in I1, I2. lia.
Qed.

Variable OPS : FX.State.St.optable.
Definition w_pat_ev_stmt : Prop :=
  forall E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb,
  FX.State.St.st_ok bsegs OPS E st ms mo ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) ->
  CtrA.win_lookup wnl kd = Some (wlen, kind) -> W64.weqb kind ActrA.K_TWIN = false ->
  W64.w2Z kind <> K_FRAMEz -> W64.w2Z kind <> K_FTWINz ->
  RangeC.TwinB.RangeC.pat_ok st wnl kd kind = true ->
  forall lo hi, 0 <= lo -> lo < hi -> hi <= bv_unsigned (Val.den E wlen) ->
  In (HB p A nb) LBa -> A <= bv_unsigned (Val.ev E kd) + lo -> bv_unsigned (Val.ev E kd) + hi <= A + nb ->
  ablock_shadow (ms_mem ms) A nb.

Definition w_pat_sub_stmt : Prop :=
  forall E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb,
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  CtrA.win_lookup wnl kd = Some (wlen, kind) -> W64.weqb kind ActrA.K_TWIN = false -> W64.weqb kind CtrLib.K_BLOCK = false ->
  W64.w2Z kind <> K_FRAMEz -> W64.w2Z kind <> K_FTWINz ->
  (W64.weqb kind RangeC.TwinB.RangeC.K_SLOT || W64.weqb kind RangeC.TwinB.RangeC.K_ZONE)%bool = true ->
  forall lo hi, 0 <= lo -> lo < hi -> hi <= bv_unsigned (Val.den E wlen) ->
  In (HB p A nb) LBa -> A <= bv_unsigned (Val.ev E kd) + lo -> bv_unsigned (Val.ev E kd) + hi <= A + nb ->
  ablock_shadow (ms_mem ms) A nb.
End Facts.
End TwinB.
