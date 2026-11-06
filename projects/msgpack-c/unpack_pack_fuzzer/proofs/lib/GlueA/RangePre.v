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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require GlueA CtrPre CallA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggLib UnreggPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import StackSh RangeC RangeFX MemsetPre.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require KnownT.
Unset Nia Cache. Unset Nra Cache.

Definition range_facts {rc : runConstT} (RNG : footprint) (m : amem) (sp A len : Z) (needw : bool) : Prop :=
  AIMG_HI <= A /\ A + len + 8 <= 2 ^ 47 /\ (A + len <= ATOP \/ sp <= A)
  /\ (exists bs, length bs = Z.to_nat len /\ AM.bytes_at asegs m A bs)
  /\ (needw = true -> exists junk, AS.rw_cells asegs m A [CB (Z.to_nat len) junk])
  /\ SH.app_blk A (A + len) /\ SH.unpoisoned m A (A + len) /\ rng RNG A len
  /\ exists RLO RHI, (RLO <= A /\ A + len <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= SH.KEND)
       /\ AM.wr_at asegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).

Lemma mapped_bytes {rc : runConstT} : forall (m : amem) n A, 0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> St.rb asegs m (A + i) <> None) ->
  exists bs, length bs = n /\ AM.bytes_at asegs m A bs.
Proof.
  intros m n. induction n as [|n IH]; intros A HA HB H.
  - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (St.rb asegs m A) as [b|] eqn:RB; [| exfalso; apply (H 0 ltac:(lia)); rewrite Z.add_0_r; exact RB].
    destruct (IH (A + 1) ltac:(lia) ltac:(lia)) as (bs & LEN & _ & _ & BY).
    { intros i Hi. replace (A + 1 + i) with (A + (1 + i)) by lia. apply H. lia. }
    exists (b :: bs). split; [cbn; lia|]. split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + cbn [nth_error]. rewrite Z.add_0_r. rewrite <- (GlueA.rb_mrdA asegs). exact RB.
    + cbn [nth_error]. replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply BY. cbn [length] in Hi. lia.
Qed.

Lemma raw_of_view {rc : runConstT} : forall (mm : amem) a b, 0x62f000 <= a < 2 ^ 64 -> St.rb asegs mm a = Some b -> mm (Z_to_bv 64 a) = Some b.
Proof.
  intros mm a b Ha H. unfold St.rb in H. destruct (mm (Z_to_bv 64 a)) as [b0|]; [exact H|]. exfalso. unfold St.rom_of in H.
  destruct (memory_read asegs (Z_to_bv 64 a) 1) as [[|b' l]|] eqn:MR; try discriminate H.
  destruct (MemP.memory_read_find_segment asegs a _ ltac:(unfold W64.two64; lia) MR) as [seg Hs].
  rewrite (UnreggPre.no_seg_above a (proj1 Ha)) in Hs. discriminate Hs.
Qed.

Section Facts.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : St.optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Hypothesis OPS_holds_ssh : forall m mo, St.op_holds OPS RangeC.SSH_ID [] m mo -> ssh_holds m.
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (SH.KHIGH - shad ATOP).
Hypothesis ACCT_frng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> FRNG AI AI_fake L RNG.

Hypothesis W_PAT : w_pat_ev_stmt AI ACCT UNIV Cw OPS.

Lemma known_leu_sound_r : forall E st ms model a b, St.st_ok asegs OPS E st ms model ->
  KnownT.KnownT.known_leu_t (s_facts st) a b = true -> bv_unsigned (Val.den E a) <= bv_unsigned (Val.den E b).
Proof.
  intros E st ms model a b HS H. exact (KnownT.KnownT.known_leu_t_sound E _ (St.so_facts _ _ _ _ _ _ HS) a b H).
Qed.
Lemma known_leu_sound_r_plain : forall E st ms model a b, St.st_ok asegs OPS E st ms model ->
  CtrLib.known_leu (s_facts st) a b = true -> bv_unsigned (Val.den E a) <= bv_unsigned (Val.den E b).
Proof.
  intros E st ms model a b HS H. unfold CtrLib.known_leu, Step.dec_false in H.
  destruct (Step.decide_ltu (s_facts st) b a) as [[|]|] eqn:Hd; try discriminate H.
  pose proof (ValP.decide_ltu_sound E (s_facts st) (St.so_facts _ _ _ _ _ _ HS) b a false Hd) as X.
  apply (proj1 (ValP.ltu_iff _ _ false)) in X. exact X.
Qed.

Lemma sval_small : forall b : byte, 0 <= bv_unsigned b <= 7 -> SH.sval b = bv_unsigned b.
Proof.
  intros b Hb. unfold SH.sval, bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (256 / 2) with 128. rewrite Z.mod_small by lia. lia.
Qed.

Lemma frame_range_facts : forall E st ms mo r hargs wnl L RNG sta LBa aw k o len needw,
  St.st_ok asegs OPS E st ms mo ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ACCT aw L RNG sta LBa mo ->
  RangeC.in_frame st wnl k o len = true -> RangeC.shadow_ok_x asegs st k o len = true -> 1 <= to_Z len <= 4096 ->
  let sp := bv_unsigned (AP.getr (ms_regs ms) 2) in
  let A := bv_unsigned (Val.ev E k) + W64.w2Zs o in
  bv_unsigned (Val.den E (Val.VP k o)) = A /\ range_facts RNG (ms_mem ms) sp A (to_Z len) needw.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw k o len needw HS CF AH AC INF SHX NR sp A.
  pose proof atop_range as ATR. set (m := ms_mem ms) in *.
  unfold RangeC.in_frame in INF. destruct (CtrA.win_lookup wnl k) as [[wlen kind]|] eqn:WL; [|discriminate INF].
  repeat match type of INF with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in INF as [INF X] end.
  apply ValP.weqb_eq in INF. subst kind. apply negb_true_iff in Q3, Q2.
  pose proof (St.so_facts _ _ _ _ _ _ HS) as Hfs.
  pose proof (known_leu_sound_r E st ms mo _ _ HS Q0) as KL. cbn [Val.den] in KL. rewrite W64Proofs.wbv_unsigned, W64Proofs.wadd_ok, W64Proofs.wlit_ok in KL.
  pose proof (W64Proofs.w2Z_range o) as ROD.
  assert (ODS : W64.w2Z o < W64.two63) by (unfold W64.w2Z; rewrite Q3; pose proof (W64Proofs.wl_range o); unfold W64.two63 in *; lia).
  rewrite Z.mod_small in KL by (unfold W64.two63, W64.two64 in *; lia).
  assert (ES : W64.w2Zs o = W64.w2Z o) by (rewrite ValP.w2Zs_eq, Q3; lia).
  pose proof (ValP.aligned_sound E _ Hfs _ _ Q ltac:(change (to_Z 6%uint63) with 6; lia)) as AL64. change (2 ^ to_Z 6%uint63) with 64 in AL64.

  destruct CF as (LB & ks & offs & rss & ksp & nn & md & Asv & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NWI & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct WOF as (E1 & E2 & E3 & E4).
  destruct (HeapCtrB.nonstack_windows_In E nn rest wnl k wlen RangeC.K_FRAME NWI (HeapCtrB.win_lookup_In _ _ _ _ WL)) as (K0' & _ & KD & INW0).
  destruct TI as (_ & _ & _ & T4 & _).
  destruct (T4 _ INW0 eq_refl) as (fb & VF & EIV). unfold w_iv, user_iv in EIV. cbn [w_lo w_len] in EIV. rewrite (usz_fake fb (proj2 VF)) in EIV.
  injection EIV as EAf ENf.
  assert (Hb : In fb LBa) by (rewrite <- E4; exact (proj1 (proj1 VF))).
  destruct (fk_facts AI AI_fake L RNG sta LBa m fb AH Hb (proj2 VF)) as (BK & HIb & A8b & N8b & N64b & WRb & WRs).
  destruct (fk_class AI AI_fake L RNG sta LBa m fb AH Hb (proj2 VF)) as (c & _ & C0 & EN).
  destruct (fk_rng AI AI_fake L RNG sta LBa m fb AH Hb (proj2 VF) (ACCT_frng _ _ _ _ _ _ AC)) as (RNGb & RNGs & _).
  set (F := ab_addr fb) in *. set (n := ab_size fb) in *.
  pose proof (bv_unsigned_in_range _ (Val.ev E k)) as RK. unfold bv_modulus in RK. change (2 ^ Z.of_N 64) with (2 ^ 64) in RK.
  assert (DVK : bv_unsigned (Val.den E (Val.VP k W64.wzero)) = bv_unsigned (Val.ev E k)).
  { rewrite ValP.den_VP. change (W64.w2Zs W64.wzero) with 0. rewrite Z.add_0_r. apply Z.mod_small. unfold W64.two64. lia. }
  rewrite DVK in AL64. rewrite EAf in AL64. fold F in AL64.
  assert (N64 : n mod 64 = 0).
  { rewrite EN, Z.mul_comm. apply Z_mod_mult. }
  assert (INR : F <= A /\ A + to_Z len <= F + n - 8) by (unfold A, F, n; rewrite ES, EAf; lia).
  assert (BND : AIMG_HI <= F /\ F + n <= ATOP) by (unfold ablk, AIMG_HI, KLS in *; lia).
  split.
  { rewrite ValP.den_VP. apply Z.mod_small. fold A. unfold W64.two64, AIMG_HI in *. lia. }
  destruct WRb as (W0 & W1 & WV).
  assert (VAL : forall i, 0 <= i < to_Z len -> St.wb asegs m (A + i) = true /\ St.rb asegs m (A + i) <> None).
  { intros i Hi. assert (WBI : St.wb asegs m (A + i) = true).
    { apply (GlueA.wb_wviewA asegs). replace (A + i) with (F + (A - F + i)) by lia. apply WV. lia. }
    split; [exact WBI|]. apply UnreggPre.shmap_rb; [unfold AIMG_HI in *; lia| exact WBI]. }
  split; [lia|]. split; [lia|]. split; [left; lia|].
  split.
  { destruct (mapped_bytes m (Z.to_nat (to_Z len)) A ltac:(unfold AIMG_HI in *; lia) ltac:(lia)) as (bs & LEN & BY).
    - intros i Hi. apply VAL. lia.
    - exists bs. split; assumption. }
  split.
  { intros _. apply (UnreggLib.mapped_chunk asegs m (Z.to_nat (to_Z len)) A ltac:(unfold AIMG_HI in *; lia) ltac:(lia)).
    intros i Hi. apply VAL. lia. }
  split.
  { unfold SH.app_blk, SH.KLOW, SH.KHIGH, SH.KEND. split; [lia|]. unfold ablk, AIMG_HI, KLS in BK. destruct BK as [[B1 B2]|[B1 B2]]; [left| right]; lia. }
  split.
  { split; [unfold AIMG_HI in *; lia|]. split; [lia|]. intros G _ G1 G2.
    destruct (RangeFX.shadow_ok_x_sound asegs OPS st k o len E ms mo HS SHX ltac:(lia) ltac:(rewrite <- ES; fold A; lia) G
                ltac:(rewrite <- ES; fold A; lia) ltac:(rewrite <- ES; fold A; lia)) as (b & RB & GB).
    exists b. split.
    - unfold AM.wa, ASHOFF. apply raw_of_view; [lia| exact RB].
    - rewrite <- ES in GB. fold A in GB. unfold SH.gran_ok. destruct GB as [G0|GN]; [left| right].
      + rewrite sval_small by lia. exact G0.
      + rewrite sval_small by lia. exact GN. }
  split; [eapply rng_sub'; [exact RNGb| lia]|].
  exists (A / 64 * 64), ((A + to_Z len + 63) / 64 * 64).
  assert (H1 : F <= A / 64 * 64 /\ A / 64 * 64 <= A) by (Z.div_mod_to_equations; lia).
  assert (H2 : A + to_Z len <= (A + to_Z len + 63) / 64 * 64 /\ (A + to_Z len + 63) / 64 * 64 <= F + n) by (Z.div_mod_to_equations; lia).
  split; [repeat split; try lia; try (apply Z_mod_mult); unfold SH.KEND; lia|].
  assert (SHE : forall x, 0 <= x -> shad x = ASHOFF + x / 8) by (intros x Hx; unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (S1 : shad F <= shad (A / 64 * 64) /\ shad (A / 64 * 64) <= shad ((A + to_Z len + 63) / 64 * 64) /\ shad ((A + to_Z len + 63) / 64 * 64) <= shad F + shlen n).
  { unfold shlen. rewrite !SHE, Z.shiftr_div_pow2 by (unfold AIMG_HI in *; lia). change (2 ^ 3) with 8. unfold AIMG_HI in *. Z.div_mod_to_equations. lia. }
  split.
  - destruct WRs as (V0 & V1 & VV). split; [lia|]. split; [lia|]. intros i Hi.
    replace (shad (A / 64 * 64) + i) with (shad F + (shad (A / 64 * 64) - shad F + i)) by lia. apply VV. lia.
  - eapply rng_sub'; [exact RNGs| lia].
Qed.

Lemma block_range_facts_z : forall L RNG sta LBa (m : amem) p A nb A0 n,
  AHEAP AI L RNG sta LBa m -> In (HB p A nb) LBa -> A <= A0 -> A0 + n <= A + nb -> 1 <= n ->
  (exists junk, AS.rw_cells asegs m A0 [CB (Z.to_nat n) junk])
  /\ SH.app_blk A0 (A0 + n)
  /\ AIMG_HI <= A0 /\ A0 + n <= ATOP /\ rng RNG A0 n
  /\ exists RLO2 RHI2, (RLO2 <= A0 /\ A0 + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= SH.KEND)
       /\ AM.wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) /\ rng RNG (shad RLO2) (shad RHI2 - shad RLO2).
Proof.
  intros L RNG sta LBa m p A nb A0 n AH HIN LE1 LE2 N1.
  destruct (AI_block AI L RNG sta LBa m p A nb AH HIN) as (NB & (BK & N0 & HI & AL) & RB & RSH & _ & WR & _ & RLO & RHI & P1 & P2 & Q1 & Q2 & RH & WH).
  pose proof atop_range as ATR.
  assert (LOW : AIMG_HI <= A) by (unfold ablk, AIMG_HI, KLS in *; lia).
  destruct WR as (W0 & W1 & WV).
  split; [| split; [| split; [lia| split; [lia| split; [eapply rng_sub'; [exact RB| lia]|]]]]].
  -
    apply (UnreggLib.mapped_chunk asegs); [unfold AIMG_HI in *; lia | rewrite Z2Nat.id by lia; lia |].
    intros i Hi. rewrite Z2Nat.id in Hi by lia.
    assert (WBI : St.wb asegs m (A0 + i) = true).
    { apply (GlueA.wb_wviewA asegs). replace (A0 + i) with (A + (A0 - A + i)) by lia. apply WV. lia. }
    split; [exact WBI|]. apply UnreggPre.shmap_rb; [unfold AIMG_HI in *; lia| exact WBI].
  -
    unfold SH.app_blk, SH.KLOW, SH.KHIGH, SH.KEND. split; [lia|]. unfold ablk, AIMG_HI, KLS in BK. destruct BK as [[B1 B2]|[B1 B2]]; [left| right]; lia.
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

Lemma top_kind_facts : forall kind, RangeC.top_kind kind = true ->
  W64.weqb kind ActrA.K_TWIN = false /\ W64.w2Z kind <> K_FRAMEz /\ W64.w2Z kind <> K_FTWINz /\ K_BLOCK <= W64.w2Z kind < K_GHOST.
Proof.
  intros kind H. unfold RangeC.top_kind in H.
  apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|]; apply ValP.weqb_eq in H; subst kind; vm_compute;
    (split; [reflexivity|]; split; [discriminate|]; split; [discriminate|]; split; [discriminate| reflexivity]).
Qed.

Theorem range_class_facts_ev : forall E st ms mo r hargs wnl L RNG sta LBa aw k o len needw c,
  St.st_ok asegs OPS E st ms mo ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ACCT aw L RNG sta LBa mo ->
  let sp := bv_unsigned (AP.getr (ms_regs ms) 2) in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 ->
  RangeC.range_class asegs st wnl k o len needw = Some c -> 1 <= to_Z len <= 4096 ->
  let A := bv_unsigned (Val.ev E k) + W64.w2Zs o in
  bv_unsigned (Val.den E (Val.VP k o)) = A /\ range_facts RNG (ms_mem ms) sp A (to_Z len) needw.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw k o len needw c HS CF AH AC sp BOT LO SPT RC NR A.
  pose proof atop_range as ATR. set (m := ms_mem ms) in *.
  unfold RangeC.range_class in RC.
  destruct (IMap.find k (s_regs st)) as [rr|] eqn:Hk; [|discriminate RC].
  destruct (negb (PrimInt63.eqb k 0%uint63) && implb needw (rg_w rr))%bool eqn:C0; [|discriminate RC].
  apply andb_prop in C0 as [K0 NW]. apply negb_true_iff in K0.
  destruct (RangeC.in_window st wnl k o len) eqn:INW.
  -
    clear RC. unfold RangeC.in_window in INW. destruct (CtrA.win_lookup wnl k) as [[wlen kind]|] eqn:WL; [|discriminate INW].
    destruct (RangeC.pat_ok st wnl k kind) eqn:PK; [|discriminate INW].
    repeat match type of INW with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in INW as [INW X] end.
    apply negb_true_iff in INW, Q5, Q4, Q3, Q2, Q1.
    assert (NF7 : W64.w2Z kind <> K_FRAMEz).
    { intros QQ. rewrite W64Proofs.weqb_eqb in INW. apply Z.eqb_neq in INW. apply INW. rewrite QQ. reflexivity. }
    assert (NF8 : W64.w2Z kind <> K_FTWINz).
    { intros QQ. rewrite W64Proofs.weqb_eqb in Q5. apply Z.eqb_neq in Q5. apply Q5. rewrite QQ. reflexivity. }
    pose proof (known_leu_sound_r E st ms mo _ _ HS Q) as KL. cbn [Val.den] in KL. rewrite W64Proofs.wbv_unsigned, W64Proofs.wadd_ok, W64Proofs.wlit_ok in KL.
    pose proof (W64Proofs.w2Z_range o) as ROD.
    assert (ODS : W64.w2Z o < W64.two63) by (unfold W64.w2Z; rewrite Q2; pose proof (W64Proofs.wl_range o); unfold W64.two63 in *; lia).
    rewrite Z.mod_small in KL by (unfold W64.two63, W64.two64 in *; lia).
    assert (ES : W64.w2Zs o = W64.w2Z o) by (rewrite ValP.w2Zs_eq, Q2; lia).
    destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw k wlen kind (W64.w2Z o) (W64.w2Z o + to_Z len) CF WL Q4
                NF7 NF8 (pat_ok_kind_range _ _ _ _ PK) ltac:(lia) ltac:(lia) KL) as (p & Ab & nb & HINB & BA1 & BA2).
    unfold A. rewrite ES.
    pose proof (W_PAT E st ms mo r hargs wnl L RNG sta LBa aw k wlen kind p Ab nb HS CF AH WL Q4 NF7 NF8 PK (W64.w2Z o) (W64.w2Z o + to_Z len)
                  ltac:(lia) ltac:(lia) KL HINB BA1 BA2) as PATW.
    destruct (block_range_facts AI L RNG sta LBa m p Ab nb (bv_unsigned (Val.ev E k) + W64.w2Z o) (to_Z len) AH HINB PATW BA1 ltac:(lia) ltac:(lia))
      as ((junk & DST) & APB & UNP & LOWA & HIA & RNGD & RLO2 & RHI2 & HULL & WRH & RNGH).
    split.
    { rewrite ValP.den_VP, ES. apply Z.mod_small. unfold W64.two64, AIMG_HI in *. lia. }
    split; [exact LOWA|]. split; [lia|]. split; [left; exact HIA|].
    split.
    { destruct DST as [[WF BY] _]. exists junk. cbn [cells_wf cell_wf] in WF. split; [exact (proj1 WF)|].
      cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exact BY. }
    split; [intros _; exists junk; exact DST|].
    split; [exact APB|]. split; [exact UNP|]. split; [exact RNGD|]. exists RLO2, RHI2. auto.
  - destruct (RangeC.in_view asegs st wnl k o len) eqn:INV.
    {
      clear RC. unfold RangeC.in_view in INV. destruct (CtrA.win_lookup wnl k) as [[wlen kind]|] eqn:WL; [|discriminate INV].
      repeat match type of INV with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in INV as [INV X] end.
      apply negb_true_iff in Q4, Q3, Q2.
      destruct (top_kind_facts kind INV) as (NT & NF7 & NF8 & KR).
      pose proof (known_leu_sound_r E st ms mo _ _ HS Q0) as KL. cbn [Val.den] in KL. rewrite W64Proofs.wbv_unsigned, W64Proofs.wadd_ok, W64Proofs.wlit_ok in KL.
      pose proof (W64Proofs.w2Z_range o) as ROD.
      assert (ODS : W64.w2Z o < W64.two63) by (unfold W64.w2Z; rewrite Q3; pose proof (W64Proofs.wl_range o); unfold W64.two63 in *; lia).
      rewrite Z.mod_small in KL by (unfold W64.two63, W64.two64 in *; lia).
      assert (ES : W64.w2Zs o = W64.w2Z o) by (rewrite ValP.w2Zs_eq, Q3; lia).
      destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw k wlen kind (W64.w2Z o) (W64.w2Z o + to_Z len) CF WL NT
                  NF7 NF8 KR ltac:(lia) ltac:(lia) KL) as (p & Ab & nb & HINB & BA1 & BA2).
      unfold A. rewrite ES.
      destruct (block_range_facts_z L RNG sta LBa m p Ab nb (bv_unsigned (Val.ev E k) + W64.w2Z o) (to_Z len) AH HINB BA1 ltac:(lia) ltac:(lia))
        as ((junk & DST) & APB & LOWA & HIA & RNGD & RLO2 & RHI2 & HULL & WRH & RNGH).
      assert (DEN : bv_unsigned (Val.den E (Val.VP k o)) = bv_unsigned (Val.ev E k) + W64.w2Z o).
      { rewrite ValP.den_VP, ES. apply Z.mod_small. unfold W64.two64, AIMG_HI in *. lia. }
      split; [exact DEN|].
      split; [exact LOWA|]. split; [lia|]. split; [left; exact HIA|].
      split.
      { destruct DST as [[WF BY] _]. exists junk. cbn [cells_wf cell_wf] in WF. split; [exact (proj1 WF)|].
        cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exact BY. }
      split; [intros _; exists junk; exact DST|].
      split; [exact APB|].
      split.
      { split; [unfold AIMG_HI in *; lia|]. split; [lia|]. intros G _ G1 G2. exists (Z_to_bv 8 0). split; [| left; reflexivity].
        unfold AM.wa, ASHOFF. apply raw_of_view; [unfold AIMG_HI in *; lia|].
        apply (RangeFX.shadow_zero_sound asegs OPS st k o len E ms mo HS Q ltac:(lia)); rewrite ?DEN; lia. }
      split; [exact RNGD|]. exists RLO2, RHI2. auto. }
    destruct (RangeC.in_frame st wnl k o len && RangeC.shadow_ok_x asegs st k o len)%bool eqn:INF.
    {
      apply andb_prop in INF as [INF SHX].
      exact (frame_range_facts E st ms mo r hargs wnl L RNG sta LBa aw k o len needw HS CF AH AC INF SHX NR). }

    match type of RC with (if ?cnd then _ else _) = _ => destruct cnd eqn:C1; [|discriminate RC] end. clear RC.
    repeat match type of C1 with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in C1 as [C1 X] end.
    destruct (find_op RangeC.SSH_ID (s_ops st)) as [[|? ?]|] eqn:FZ; try discriminate Q.
    assert (L8 : to_Z (PrimInt63.add len 8%uint63) = to_Z len + 8).
    { rewrite Uint63.add_spec. change (to_Z 8%uint63) with 8. apply Z.mod_small. change wB with (2 ^ 63). lia. }
    destruct (RangeFX.in_region_sound E rr o _ Q2 ltac:(rewrite L8; lia)) as (RL & RH & RK). rewrite L8 in RH.
    pose proof (St.so_reg _ _ _ _ _ _ HS k rr Hk) as RO.
    destruct (St.ro_range _ _ _ _ _ _ RO K0) as [RG0 RG1].
    pose proof (St.ro_valid _ _ _ _ _ _ RO K0) as RV.

    assert (SS : sp <= A /\ bv_unsigned (Val.ev E k) + St.hiZ E rr <= 2 ^ 47).
    { destruct CF as (LB & ks & offs & rss & ksp & nn & md & Asv & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                      & NWI & AN & AJ & TS & WF & HC & AWden & AR).
      assert (KN0 : k <> 0%uint63) by (intros ->; discriminate K0).
      pose proof (CallA.aregion_just_sound asegs OPS E st ms mo wnl ks offs rss k rr HS SPR AJ Hk KN0) as JU.
      unfold RangeC.stack_side in Q1. rewrite SPR in Q1.
      destruct (PrimInt63.eqb k ks) eqn:KS.
      - apply Uint63.eqb_correct in KS. subst ks. apply Z.leb_le in Q1. destruct (MemP.okey_sound _ _ Hksp) as [EK _].
        destruct JU as [[_ J]|[NE _]]; [| exfalso; apply NE; reflexivity].
        split; [| exact J]. unfold sp, A. unfold St.keyZ in *. change (AP.getr (ms_regs ms) 2) with (AP.getr (ms_regs ms) 2%bv). rewrite SPE. lia.
      - destruct (CtrA.win_lookup wnl k) as [[? ?]|] eqn:WLK; [discriminate Q1|].
        destruct JU as [[EQ _]|[_ [(len0 & kd0 & WLS & _)|[[J1 J2]|VJ]]]].
        + exfalso. subst ks. rewrite Uint63.eqb_refl in KS. discriminate KS.
        + discriminate WLS.
        + split; [| exact J2]. unfold sp, A.
          assert (E2 : bv_unsigned (AP.getr (ms_regs ms) 2) = bv_unsigned (Val.den E (Step.getr st X2))).
          { f_equal. exact (GlueA.getr_RA asegs OPS E st ms mo HS X2). }
          rewrite E2. lia.
        +
          exfalso. destruct VJ as [VJ|SL].
          * unfold RangeC.not_view in C1. apply andb_prop in C1 as [NZV NPIN].
            unfold ActrA.view_just, ActrA.view_I in VJ.
            destruct (ActrA.zero_view rr); [discriminate NZV|]. destruct (ActrA.find_pin (s_facts st) k); [discriminate NPIN|].

            assert (VT : ActrA.view_tail (s_facts st) wnl k rr = true) by (destruct (ActrA.ro_lit_hi rr); cbn [orb] in VJ; exact VJ).
            unfold ActrA.view_tail in VT.
            destruct (negb (rg_w rr) && PrimInt63.eqb (rg_lo rr) 0%uint63 && sv_eqb (rg_hi rr) (VL wone))%bool eqn:TC; [|discriminate VT].
            apply andb_prop in TC as [TC T3]. apply andb_prop in TC as [_ T2]. apply Uint63.eqb_correct in T2. apply ValP.sv_eqb_eq in T3.
            assert (HZ1 : St.hiZ E rr = 1) by (unfold St.hiZ; rewrite T3; reflexivity).
            assert (LZ0 : St.loZ rr = 0) by (unfold St.loZ; rewrite T2; reflexivity).
            rewrite HZ1 in RH. rewrite LZ0 in RL. pose proof (to_Z_bounded len). lia.
          *
            unfold ActrA.sliver_just in SL. destruct (ActrA.stack_wlo st); [|discriminate SL]. destruct (IMap.find ks (s_regs st)); [|discriminate SL].
            apply andb_prop in SL as [SL _]. apply andb_prop in SL as [_ SL].
            unfold RangeC.in_region in Q2. destruct (okey o); [|discriminate Q2]. destruct (okey (wadd o (wlit (PrimInt63.add len 8%uint63)))); [|discriminate Q2].
            destruct (rg_hi rr); try discriminate Q2. cbn in SL. discriminate SL. }
    destruct SS as [SPA HI47].
    assert (ARNG : ATOP + 8192 <= A /\ A + to_Z len + 8 <= 2 ^ 47) by (unfold A in *; lia).
    split.
    { rewrite ValP.den_VP. apply Z.mod_small. unfold A in *. unfold W64.two64. lia. }
    assert (DEN : bv_unsigned (Val.den E (Val.VP k o)) = A).
    { rewrite ValP.den_VP. apply Z.mod_small. unfold A in *. unfold W64.two64. lia. }

    pose proof (proj1 (Forall_forall _ _) (St.so_ops _ _ _ _ _ _ HS) _ (UnreggPre.find_op_In _ _ _ FZ)) as HO. cbn [op_id op_args map] in HO.
    pose proof (OPS_holds_ssh _ _ HO) as SSH. fold m in SSH.
    assert (VAL : forall i, 0 <= i < to_Z len -> St.rb asegs m (A + i) <> None /\ (rg_w rr = true -> St.wb asegs m (A + i) = true)).
    { intros i Hi. destruct (RV (A + i) ltac:(unfold A; lia)) as (V1 & V2 & _). split; assumption. }
    split; [unfold AIMG_HI; lia|]. split; [lia|]. split; [right; exact SPA|].
    split.
    { destruct (mapped_bytes m (Z.to_nat (to_Z len)) A ltac:(lia) ltac:(lia)) as (bs & LEN & BY).
      - intros i Hi. apply VAL. lia.
      - exists bs. split; assumption. }
    split.
    { intros NWt. subst needw. cbn [implb] in NW.
      apply (UnreggLib.mapped_chunk asegs m (Z.to_nat (to_Z len)) A ltac:(lia) ltac:(lia)).
      intros i Hi. destruct (VAL i ltac:(lia)) as [V1 V2]. split; [exact (V2 NW)| exact V1]. }
    split; [split; [lia|]; right; unfold SH.KHIGH, SH.KEND; lia|].
    split.
    { split; [lia|]. split; [lia|]. intros G _ G1 G2. exists (Z_to_bv 8 0). split; [| left; reflexivity].
      unfold AM.wa, ASHOFF. apply raw_of_view; [lia|].
      apply (RangeFX.shadow_zero_sound asegs OPS st k o len E ms mo HS Q0 ltac:(lia)); rewrite ?DEN; lia. }
    split; [apply (rng_sub _ _ _ _ _ (ACCT_rng _ _ _ _ _ _ AC)); lia|].
    exists (A / 64 * 64), ((A + to_Z len + 63) / 64 * 64).
    assert (H1 : A / 64 * 64 <= A /\ A < A / 64 * 64 + 64) by (Z.div_mod_to_equations; lia).
    assert (H2 : A + to_Z len <= (A + to_Z len + 63) / 64 * 64 /\ (A + to_Z len + 63) / 64 * 64 <= 2 ^ 47) by (Z.div_mod_to_equations; lia).
    split; [repeat split; try lia; try (apply Z_mod_mult); unfold SH.KEND; lia|].
    split; [apply (ssh_wr_at m _ _ SSH); lia|].
    apply (rng_sub _ _ _ _ _ (ACCT_rng_stk_sh _ _ _ _ _ _ AC)).
    + apply shad_mono. lia.
    + pose proof (shad_mono _ _ (proj2 H2)) as S3. rewrite shad_top in S3. lia.
Qed.
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
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import StackSh.TwinB RangeC.TwinB RangeFX.TwinB MemsetPre.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Unset Nia Cache. Unset Nra Cache.

Definition range_facts {rc : runConstT} (RNG : footprint) (m : amem) (sp A len : Z) (needw : bool) : Prop :=
  AIMG_HI <= A /\ A + len + 8 <= 2 ^ 47 /\ (A + len <= ATOP \/ sp <= A)
  /\ (exists bs, length bs = Z.to_nat len /\ AM.bytes_at bsegs m A bs)
  /\ (needw = true -> exists junk, AS.rw_cells bsegs m A [CB (Z.to_nat len) junk])
  /\ SH.app_blk A (A + len) /\ SH.unpoisoned m A (A + len) /\ rng RNG A len
  /\ exists RLO RHI, (RLO <= A /\ A + len <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= SH.KEND)
       /\ AM.wr_at bsegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).

Lemma mapped_bytes {rc : runConstT} : forall (m : amem) n A, 0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> St.rb bsegs m (A + i) <> None) ->
  exists bs, length bs = n /\ AM.bytes_at bsegs m A bs.
Proof.
  intros m n. induction n as [|n IH]; intros A HA HB H.
  - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (St.rb bsegs m A) as [b|] eqn:RB; [| exfalso; apply (H 0 ltac:(lia)); rewrite Z.add_0_r; exact RB].
    destruct (IH (A + 1) ltac:(lia) ltac:(lia)) as (bs & LEN & _ & _ & BY).
    { intros i Hi. replace (A + 1 + i) with (A + (1 + i)) by lia. apply H. lia. }
    exists (b :: bs). split; [cbn; lia|]. split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + cbn [nth_error]. rewrite Z.add_0_r. rewrite <- (GlueA.TwinB.rb_mrdA bsegs). exact RB.
    + cbn [nth_error]. replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply BY. cbn [length] in Hi. lia.
Qed.

Lemma raw_of_view {rc : runConstT} : forall (mm : amem) a b, 0x631000 <= a < 2 ^ 64 -> St.rb bsegs mm a = Some b -> mm (Z_to_bv 64 a) = Some b.
Proof.
  intros mm a b Ha H. unfold St.rb in H. destruct (mm (Z_to_bv 64 a)) as [b0|]; [exact H|]. exfalso. unfold St.rom_of in H.
  destruct (memory_read bsegs (Z_to_bv 64 a) 1) as [[|b' l]|] eqn:MR; try discriminate H.
  destruct (MemP.memory_read_find_segment bsegs a _ ltac:(unfold W64.two64; lia) MR) as [seg Hs].
  rewrite (UnreggPre.TwinB.no_seg_above a (proj1 Ha)) in Hs. discriminate Hs.
Qed.

Section Facts.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : St.optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Hypothesis OPS_holds_ssh : forall m mo, St.op_holds OPS RangeC.TwinB.RangeC.SSH_ID [] m mo -> ssh_holds m.
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (SH.KHIGH - shad ATOP).
Hypothesis ACCT_frng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> FRNG AI AI_fake L RNG.

Hypothesis W_PAT : w_pat_ev_stmt AI ACCT UNIV Cw OPS.

Lemma known_leu_sound_r : forall E st ms model a b, St.st_ok bsegs OPS E st ms model ->
  KnownT.KnownT.known_leu_t (s_facts st) a b = true -> bv_unsigned (Val.den E a) <= bv_unsigned (Val.den E b).
Proof.
  intros E st ms model a b HS H. exact (KnownT.KnownT.known_leu_t_sound E _ (St.so_facts _ _ _ _ _ _ HS) a b H).
Qed.
Lemma known_leu_sound_r_plain : forall E st ms model a b, St.st_ok bsegs OPS E st ms model ->
  CtrLib.known_leu (s_facts st) a b = true -> bv_unsigned (Val.den E a) <= bv_unsigned (Val.den E b).
Proof.
  intros E st ms model a b HS H. unfold CtrLib.known_leu, Step.dec_false in H.
  destruct (Step.decide_ltu (s_facts st) b a) as [[|]|] eqn:Hd; try discriminate H.
  pose proof (ValP.decide_ltu_sound E (s_facts st) (St.so_facts _ _ _ _ _ _ HS) b a false Hd) as X.
  apply (proj1 (ValP.ltu_iff _ _ false)) in X. exact X.
Qed.

Lemma sval_small : forall b : byte, 0 <= bv_unsigned b <= 7 -> SH.sval b = bv_unsigned b.
Proof.
  intros b Hb. unfold SH.sval, bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (256 / 2) with 128. rewrite Z.mod_small by lia. lia.
Qed.

Lemma frame_range_facts : forall E st ms mo r hargs wnl L RNG sta LBa aw k o len needw,
  St.st_ok bsegs OPS E st ms mo ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ACCT aw L RNG sta LBa mo ->
  RangeC.TwinB.RangeC.in_frame st wnl k o len = true -> RangeC.TwinB.RangeC.shadow_ok_x bsegs st k o len = true -> 1 <= to_Z len <= 4096 ->
  let sp := bv_unsigned (AP.getr (ms_regs ms) 2) in
  let A := bv_unsigned (Val.ev E k) + W64.w2Zs o in
  bv_unsigned (Val.den E (Val.VP k o)) = A /\ range_facts RNG (ms_mem ms) sp A (to_Z len) needw.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw k o len needw HS CF AH AC INF SHX NR sp A.
  pose proof atop_range as ATR. set (m := ms_mem ms) in *.
  unfold RangeC.TwinB.RangeC.in_frame in INF. destruct (CtrA.win_lookup wnl k) as [[wlen kind]|] eqn:WL; [|discriminate INF].
  repeat match type of INF with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in INF as [INF X] end.
  apply ValP.weqb_eq in INF. subst kind. apply negb_true_iff in Q3, Q2.
  pose proof (St.so_facts _ _ _ _ _ _ HS) as Hfs.
  pose proof (known_leu_sound_r E st ms mo _ _ HS Q0) as KL. cbn [Val.den] in KL. rewrite W64Proofs.wbv_unsigned, W64Proofs.wadd_ok, W64Proofs.wlit_ok in KL.
  pose proof (W64Proofs.w2Z_range o) as ROD.
  assert (ODS : W64.w2Z o < W64.two63) by (unfold W64.w2Z; rewrite Q3; pose proof (W64Proofs.wl_range o); unfold W64.two63 in *; lia).
  rewrite Z.mod_small in KL by (unfold W64.two63, W64.two64 in *; lia).
  assert (ES : W64.w2Zs o = W64.w2Z o) by (rewrite ValP.w2Zs_eq, Q3; lia).
  pose proof (ValP.aligned_sound E _ Hfs _ _ Q ltac:(change (to_Z 6%uint63) with 6; lia)) as AL64. change (2 ^ to_Z 6%uint63) with 64 in AL64.

  destruct CF as (LB & ks & offs & rss & ksp & nn & md & Asv & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NWI & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct WOF as (E1 & E2 & E3 & E4).
  destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl k wlen RangeC.TwinB.RangeC.K_FRAME NWI (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL)) as (K0' & _ & KD & INW0).
  destruct TI as (_ & _ & _ & T4 & _).
  destruct (T4 _ INW0 eq_refl) as (fb & VF & EIV). unfold w_iv, user_iv in EIV. cbn [w_lo w_len] in EIV. rewrite (usz_fake fb (proj2 VF)) in EIV.
  injection EIV as EAf ENf.
  assert (Hb : In fb LBa) by (rewrite <- E4; exact (proj1 (proj1 VF))).
  destruct (fk_facts AI AI_fake L RNG sta LBa m fb AH Hb (proj2 VF)) as (BK & HIb & A8b & N8b & N64b & WRb & WRs).
  destruct (fk_class AI AI_fake L RNG sta LBa m fb AH Hb (proj2 VF)) as (c & _ & C0 & EN).
  destruct (fk_rng AI AI_fake L RNG sta LBa m fb AH Hb (proj2 VF) (ACCT_frng _ _ _ _ _ _ AC)) as (RNGb & RNGs & _).
  set (F := ab_addr fb) in *. set (n := ab_size fb) in *.
  pose proof (bv_unsigned_in_range _ (Val.ev E k)) as RK. unfold bv_modulus in RK. change (2 ^ Z.of_N 64) with (2 ^ 64) in RK.
  assert (DVK : bv_unsigned (Val.den E (Val.VP k W64.wzero)) = bv_unsigned (Val.ev E k)).
  { rewrite ValP.den_VP. change (W64.w2Zs W64.wzero) with 0. rewrite Z.add_0_r. apply Z.mod_small. unfold W64.two64. lia. }
  rewrite DVK in AL64. rewrite EAf in AL64. fold F in AL64.
  assert (N64 : n mod 64 = 0).
  { rewrite EN, Z.mul_comm. apply Z_mod_mult. }
  assert (INR : F <= A /\ A + to_Z len <= F + n - 8) by (unfold A, F, n; rewrite ES, EAf; lia).
  assert (BND : AIMG_HI <= F /\ F + n <= ATOP) by (unfold ablk, AIMG_HI, KLS in *; lia).
  split.
  { rewrite ValP.den_VP. apply Z.mod_small. fold A. unfold W64.two64, AIMG_HI in *. lia. }
  destruct WRb as (W0 & W1 & WV).
  assert (VAL : forall i, 0 <= i < to_Z len -> St.wb bsegs m (A + i) = true /\ St.rb bsegs m (A + i) <> None).
  { intros i Hi. assert (WBI : St.wb bsegs m (A + i) = true).
    { apply (GlueA.TwinB.wb_wviewA bsegs). replace (A + i) with (F + (A - F + i)) by lia. apply WV. lia. }
    split; [exact WBI|]. apply UnreggPre.TwinB.shmap_rb; [unfold AIMG_HI in *; lia| exact WBI]. }
  split; [lia|]. split; [lia|]. split; [left; lia|].
  split.
  { destruct (mapped_bytes m (Z.to_nat (to_Z len)) A ltac:(unfold AIMG_HI in *; lia) ltac:(lia)) as (bs & LEN & BY).
    - intros i Hi. apply VAL. lia.
    - exists bs. split; assumption. }
  split.
  { intros _. apply (UnreggLib.TwinB.mapped_chunk bsegs m (Z.to_nat (to_Z len)) A ltac:(unfold AIMG_HI in *; lia) ltac:(lia)).
    intros i Hi. apply VAL. lia. }
  split.
  { unfold SH.app_blk, SH.KLOW, SH.KHIGH, SH.KEND. split; [lia|]. unfold ablk, AIMG_HI, KLS in BK. destruct BK as [[B1 B2]|[B1 B2]]; [left| right]; lia. }
  split.
  { split; [unfold AIMG_HI in *; lia|]. split; [lia|]. intros G _ G1 G2.
    destruct (RangeFX.TwinB.RangeFX.shadow_ok_x_sound bsegs OPS st k o len E ms mo HS SHX ltac:(lia) ltac:(rewrite <- ES; fold A; lia) G
                ltac:(rewrite <- ES; fold A; lia) ltac:(rewrite <- ES; fold A; lia)) as (b & RB & GB).
    exists b. split.
    - unfold AM.wa, ASHOFF. apply raw_of_view; [lia| exact RB].
    - rewrite <- ES in GB. fold A in GB. unfold SH.gran_ok. destruct GB as [G0|GN]; [left| right].
      + rewrite sval_small by lia. exact G0.
      + rewrite sval_small by lia. exact GN. }
  split; [eapply rng_sub'; [exact RNGb| lia]|].
  exists (A / 64 * 64), ((A + to_Z len + 63) / 64 * 64).
  assert (H1 : F <= A / 64 * 64 /\ A / 64 * 64 <= A) by (Z.div_mod_to_equations; lia).
  assert (H2 : A + to_Z len <= (A + to_Z len + 63) / 64 * 64 /\ (A + to_Z len + 63) / 64 * 64 <= F + n) by (Z.div_mod_to_equations; lia).
  split; [repeat split; try lia; try (apply Z_mod_mult); unfold SH.KEND; lia|].
  assert (SHE : forall x, 0 <= x -> shad x = ASHOFF + x / 8) by (intros x Hx; unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (S1 : shad F <= shad (A / 64 * 64) /\ shad (A / 64 * 64) <= shad ((A + to_Z len + 63) / 64 * 64) /\ shad ((A + to_Z len + 63) / 64 * 64) <= shad F + shlen n).
  { unfold shlen. rewrite !SHE, Z.shiftr_div_pow2 by (unfold AIMG_HI in *; lia). change (2 ^ 3) with 8. unfold AIMG_HI in *. Z.div_mod_to_equations. lia. }
  split.
  - destruct WRs as (V0 & V1 & VV). split; [lia|]. split; [lia|]. intros i Hi.
    replace (shad (A / 64 * 64) + i) with (shad F + (shad (A / 64 * 64) - shad F + i)) by lia. apply VV. lia.
  - eapply rng_sub'; [exact RNGs| lia].
Qed.

Lemma block_range_facts_z : forall L RNG sta LBa (m : amem) p A nb A0 n,
  AHEAP AI L RNG sta LBa m -> In (HB p A nb) LBa -> A <= A0 -> A0 + n <= A + nb -> 1 <= n ->
  (exists junk, AS.rw_cells bsegs m A0 [CB (Z.to_nat n) junk])
  /\ SH.app_blk A0 (A0 + n)
  /\ AIMG_HI <= A0 /\ A0 + n <= ATOP /\ rng RNG A0 n
  /\ exists RLO2 RHI2, (RLO2 <= A0 /\ A0 + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= SH.KEND)
       /\ AM.wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2) /\ rng RNG (shad RLO2) (shad RHI2 - shad RLO2).
Proof.
  intros L RNG sta LBa m p A nb A0 n AH HIN LE1 LE2 N1.
  destruct (AI_block AI L RNG sta LBa m p A nb AH HIN) as (NB & (BK & N0 & HI & AL) & RB & RSH & _ & WR & _ & RLO & RHI & P1 & P2 & Q1 & Q2 & RH & WH).
  pose proof atop_range as ATR.
  assert (LOW : AIMG_HI <= A) by (unfold ablk, AIMG_HI, KLS in *; lia).
  destruct WR as (W0 & W1 & WV).
  split; [| split; [| split; [lia| split; [lia| split; [eapply rng_sub'; [exact RB| lia]|]]]]].
  -
    apply (UnreggLib.TwinB.mapped_chunk bsegs); [unfold AIMG_HI in *; lia | rewrite Z2Nat.id by lia; lia |].
    intros i Hi. rewrite Z2Nat.id in Hi by lia.
    assert (WBI : St.wb bsegs m (A0 + i) = true).
    { apply (GlueA.TwinB.wb_wviewA bsegs). replace (A0 + i) with (A + (A0 - A + i)) by lia. apply WV. lia. }
    split; [exact WBI|]. apply UnreggPre.TwinB.shmap_rb; [unfold AIMG_HI in *; lia| exact WBI].
  -
    unfold SH.app_blk, SH.KLOW, SH.KHIGH, SH.KEND. split; [lia|]. unfold ablk, AIMG_HI, KLS in BK. destruct BK as [[B1 B2]|[B1 B2]]; [left| right]; lia.
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

Lemma top_kind_facts : forall kind, RangeC.TwinB.RangeC.top_kind kind = true ->
  W64.weqb kind ActrA.K_TWIN = false /\ W64.w2Z kind <> K_FRAMEz /\ W64.w2Z kind <> K_FTWINz /\ K_BLOCK <= W64.w2Z kind < K_GHOST.
Proof.
  intros kind H. unfold RangeC.TwinB.RangeC.top_kind in H.
  apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|]; apply ValP.weqb_eq in H; subst kind; vm_compute;
    (split; [reflexivity|]; split; [discriminate|]; split; [discriminate|]; split; [discriminate| reflexivity]).
Qed.

Theorem range_class_facts_ev : forall E st ms mo r hargs wnl L RNG sta LBa aw k o len needw c,
  St.st_ok bsegs OPS E st ms mo ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ACCT aw L RNG sta LBa mo ->
  let sp := bv_unsigned (AP.getr (ms_regs ms) 2) in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 ->
  RangeC.TwinB.RangeC.range_class bsegs st wnl k o len needw = Some c -> 1 <= to_Z len <= 4096 ->
  let A := bv_unsigned (Val.ev E k) + W64.w2Zs o in
  bv_unsigned (Val.den E (Val.VP k o)) = A /\ range_facts RNG (ms_mem ms) sp A (to_Z len) needw.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw k o len needw c HS CF AH AC sp BOT LO SPT RC NR A.
  pose proof atop_range as ATR. set (m := ms_mem ms) in *.
  unfold RangeC.TwinB.RangeC.range_class in RC.
  destruct (IMap.find k (s_regs st)) as [rr|] eqn:Hk; [|discriminate RC].
  destruct (negb (PrimInt63.eqb k 0%uint63) && implb needw (rg_w rr))%bool eqn:C0; [|discriminate RC].
  apply andb_prop in C0 as [K0 NW]. apply negb_true_iff in K0.
  destruct (RangeC.TwinB.RangeC.in_window st wnl k o len) eqn:INW.
  -
    clear RC. unfold RangeC.TwinB.RangeC.in_window in INW. destruct (CtrA.win_lookup wnl k) as [[wlen kind]|] eqn:WL; [|discriminate INW].
    destruct (RangeC.TwinB.RangeC.pat_ok st wnl k kind) eqn:PK; [|discriminate INW].
    repeat match type of INW with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in INW as [INW X] end.
    apply negb_true_iff in INW, Q5, Q4, Q3, Q2, Q1.
    assert (NF7 : W64.w2Z kind <> K_FRAMEz).
    { intros QQ. rewrite W64Proofs.weqb_eqb in INW. apply Z.eqb_neq in INW. apply INW. rewrite QQ. reflexivity. }
    assert (NF8 : W64.w2Z kind <> K_FTWINz).
    { intros QQ. rewrite W64Proofs.weqb_eqb in Q5. apply Z.eqb_neq in Q5. apply Q5. rewrite QQ. reflexivity. }
    pose proof (known_leu_sound_r E st ms mo _ _ HS Q) as KL. cbn [Val.den] in KL. rewrite W64Proofs.wbv_unsigned, W64Proofs.wadd_ok, W64Proofs.wlit_ok in KL.
    pose proof (W64Proofs.w2Z_range o) as ROD.
    assert (ODS : W64.w2Z o < W64.two63) by (unfold W64.w2Z; rewrite Q2; pose proof (W64Proofs.wl_range o); unfold W64.two63 in *; lia).
    rewrite Z.mod_small in KL by (unfold W64.two63, W64.two64 in *; lia).
    assert (ES : W64.w2Zs o = W64.w2Z o) by (rewrite ValP.w2Zs_eq, Q2; lia).
    destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw k wlen kind (W64.w2Z o) (W64.w2Z o + to_Z len) CF WL Q4
                NF7 NF8 (pat_ok_kind_range _ _ _ _ PK) ltac:(lia) ltac:(lia) KL) as (p & Ab & nb & HINB & BA1 & BA2).
    unfold A. rewrite ES.
    pose proof (W_PAT E st ms mo r hargs wnl L RNG sta LBa aw k wlen kind p Ab nb HS CF AH WL Q4 NF7 NF8 PK (W64.w2Z o) (W64.w2Z o + to_Z len)
                  ltac:(lia) ltac:(lia) KL HINB BA1 BA2) as PATW.
    destruct (block_range_facts AI L RNG sta LBa m p Ab nb (bv_unsigned (Val.ev E k) + W64.w2Z o) (to_Z len) AH HINB PATW BA1 ltac:(lia) ltac:(lia))
      as ((junk & DST) & APB & UNP & LOWA & HIA & RNGD & RLO2 & RHI2 & HULL & WRH & RNGH).
    split.
    { rewrite ValP.den_VP, ES. apply Z.mod_small. unfold W64.two64, AIMG_HI in *. lia. }
    split; [exact LOWA|]. split; [lia|]. split; [left; exact HIA|].
    split.
    { destruct DST as [[WF BY] _]. exists junk. cbn [cells_wf cell_wf] in WF. split; [exact (proj1 WF)|].
      cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exact BY. }
    split; [intros _; exists junk; exact DST|].
    split; [exact APB|]. split; [exact UNP|]. split; [exact RNGD|]. exists RLO2, RHI2. auto.
  - destruct (RangeC.TwinB.RangeC.in_view bsegs st wnl k o len) eqn:INV.
    {
      clear RC. unfold RangeC.TwinB.RangeC.in_view in INV. destruct (CtrA.win_lookup wnl k) as [[wlen kind]|] eqn:WL; [|discriminate INV].
      repeat match type of INV with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in INV as [INV X] end.
      apply negb_true_iff in Q4, Q3, Q2.
      destruct (top_kind_facts kind INV) as (NT & NF7 & NF8 & KR).
      pose proof (known_leu_sound_r E st ms mo _ _ HS Q0) as KL. cbn [Val.den] in KL. rewrite W64Proofs.wbv_unsigned, W64Proofs.wadd_ok, W64Proofs.wlit_ok in KL.
      pose proof (W64Proofs.w2Z_range o) as ROD.
      assert (ODS : W64.w2Z o < W64.two63) by (unfold W64.w2Z; rewrite Q3; pose proof (W64Proofs.wl_range o); unfold W64.two63 in *; lia).
      rewrite Z.mod_small in KL by (unfold W64.two63, W64.two64 in *; lia).
      assert (ES : W64.w2Zs o = W64.w2Z o) by (rewrite ValP.w2Zs_eq, Q3; lia).
      destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw k wlen kind (W64.w2Z o) (W64.w2Z o + to_Z len) CF WL NT
                  NF7 NF8 KR ltac:(lia) ltac:(lia) KL) as (p & Ab & nb & HINB & BA1 & BA2).
      unfold A. rewrite ES.
      destruct (block_range_facts_z L RNG sta LBa m p Ab nb (bv_unsigned (Val.ev E k) + W64.w2Z o) (to_Z len) AH HINB BA1 ltac:(lia) ltac:(lia))
        as ((junk & DST) & APB & LOWA & HIA & RNGD & RLO2 & RHI2 & HULL & WRH & RNGH).
      assert (DEN : bv_unsigned (Val.den E (Val.VP k o)) = bv_unsigned (Val.ev E k) + W64.w2Z o).
      { rewrite ValP.den_VP, ES. apply Z.mod_small. unfold W64.two64, AIMG_HI in *. lia. }
      split; [exact DEN|].
      split; [exact LOWA|]. split; [lia|]. split; [left; exact HIA|].
      split.
      { destruct DST as [[WF BY] _]. exists junk. cbn [cells_wf cell_wf] in WF. split; [exact (proj1 WF)|].
        cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exact BY. }
      split; [intros _; exists junk; exact DST|].
      split; [exact APB|].
      split.
      { split; [unfold AIMG_HI in *; lia|]. split; [lia|]. intros G _ G1 G2. exists (Z_to_bv 8 0). split; [| left; reflexivity].
        unfold AM.wa, ASHOFF. apply raw_of_view; [unfold AIMG_HI in *; lia|].
        apply (RangeFX.TwinB.RangeFX.shadow_zero_sound bsegs OPS st k o len E ms mo HS Q ltac:(lia)); rewrite ?DEN; lia. }
      split; [exact RNGD|]. exists RLO2, RHI2. auto. }
    destruct (RangeC.TwinB.RangeC.in_frame st wnl k o len && RangeC.TwinB.RangeC.shadow_ok_x bsegs st k o len)%bool eqn:INF.
    {
      apply andb_prop in INF as [INF SHX].
      exact (frame_range_facts E st ms mo r hargs wnl L RNG sta LBa aw k o len needw HS CF AH AC INF SHX NR). }

    match type of RC with (if ?cnd then _ else _) = _ => destruct cnd eqn:C1; [|discriminate RC] end. clear RC.
    repeat match type of C1 with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in C1 as [C1 X] end.
    destruct (find_op RangeC.TwinB.RangeC.SSH_ID (s_ops st)) as [[|? ?]|] eqn:FZ; try discriminate Q.
    assert (L8 : to_Z (PrimInt63.add len 8%uint63) = to_Z len + 8).
    { rewrite Uint63.add_spec. change (to_Z 8%uint63) with 8. apply Z.mod_small. change wB with (2 ^ 63). lia. }
    destruct (RangeFX.TwinB.RangeFX.in_region_sound E rr o _ Q2 ltac:(rewrite L8; lia)) as (RL & RH & RK). rewrite L8 in RH.
    pose proof (St.so_reg _ _ _ _ _ _ HS k rr Hk) as RO.
    destruct (St.ro_range _ _ _ _ _ _ RO K0) as [RG0 RG1].
    pose proof (St.ro_valid _ _ _ _ _ _ RO K0) as RV.

    assert (SS : sp <= A /\ bv_unsigned (Val.ev E k) + St.hiZ E rr <= 2 ^ 47).
    { destruct CF as (LB & ks & offs & rss & ksp & nn & md & Asv & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                      & NWI & AN & AJ & TS & WF & HC & AWden & AR).
      assert (KN0 : k <> 0%uint63) by (intros ->; discriminate K0).
      pose proof (CallA.TwinB.aregion_just_sound bsegs OPS E st ms mo wnl ks offs rss k rr HS SPR AJ Hk KN0) as JU.
      unfold RangeC.TwinB.RangeC.stack_side in Q1. rewrite SPR in Q1.
      destruct (PrimInt63.eqb k ks) eqn:KS.
      - apply Uint63.eqb_correct in KS. subst ks. apply Z.leb_le in Q1. destruct (MemP.okey_sound _ _ Hksp) as [EK _].
        destruct JU as [[_ J]|[NE _]]; [| exfalso; apply NE; reflexivity].
        split; [| exact J]. unfold sp, A. unfold St.keyZ in *. change (AP.getr (ms_regs ms) 2) with (AP.getr (ms_regs ms) 2%bv). rewrite SPE. lia.
      - destruct (CtrA.win_lookup wnl k) as [[? ?]|] eqn:WLK; [discriminate Q1|].
        destruct JU as [[EQ _]|[_ [(len0 & kd0 & WLS & _)|[[J1 J2]|VJ]]]].
        + exfalso. subst ks. rewrite Uint63.eqb_refl in KS. discriminate KS.
        + discriminate WLS.
        + split; [| exact J2]. unfold sp, A.
          assert (E2 : bv_unsigned (AP.getr (ms_regs ms) 2) = bv_unsigned (Val.den E (Step.getr st X2))).
          { f_equal. exact (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X2). }
          rewrite E2. lia.
        +
          exfalso. destruct VJ as [VJ|SL].
          * unfold RangeC.TwinB.RangeC.not_view in C1. apply andb_prop in C1 as [NZV NPIN].
            unfold ActrA.view_just, ActrA.view_I in VJ.
            destruct (ActrA.zero_view rr); [discriminate NZV|]. destruct (ActrA.find_pin (s_facts st) k); [discriminate NPIN|].

            assert (VT : ActrA.view_tail (s_facts st) wnl k rr = true) by (destruct (ActrA.ro_lit_hi rr); cbn [orb] in VJ; exact VJ).
            unfold ActrA.view_tail in VT.
            destruct (negb (rg_w rr) && PrimInt63.eqb (rg_lo rr) 0%uint63 && sv_eqb (rg_hi rr) (VL wone))%bool eqn:TC; [|discriminate VT].
            apply andb_prop in TC as [TC T3]. apply andb_prop in TC as [_ T2]. apply Uint63.eqb_correct in T2. apply ValP.sv_eqb_eq in T3.
            assert (HZ1 : St.hiZ E rr = 1) by (unfold St.hiZ; rewrite T3; reflexivity).
            assert (LZ0 : St.loZ rr = 0) by (unfold St.loZ; rewrite T2; reflexivity).
            rewrite HZ1 in RH. rewrite LZ0 in RL. pose proof (to_Z_bounded len). lia.
          *
            unfold ActrA.sliver_just in SL. destruct (ActrA.stack_wlo st); [|discriminate SL]. destruct (IMap.find ks (s_regs st)); [|discriminate SL].
            apply andb_prop in SL as [SL _]. apply andb_prop in SL as [_ SL].
            unfold RangeC.TwinB.RangeC.in_region in Q2. destruct (okey o); [|discriminate Q2]. destruct (okey (wadd o (wlit (PrimInt63.add len 8%uint63)))); [|discriminate Q2].
            destruct (rg_hi rr); try discriminate Q2. cbn in SL. discriminate SL. }
    destruct SS as [SPA HI47].
    assert (ARNG : ATOP + 8192 <= A /\ A + to_Z len + 8 <= 2 ^ 47) by (unfold A in *; lia).
    split.
    { rewrite ValP.den_VP. apply Z.mod_small. unfold A in *. unfold W64.two64. lia. }
    assert (DEN : bv_unsigned (Val.den E (Val.VP k o)) = A).
    { rewrite ValP.den_VP. apply Z.mod_small. unfold A in *. unfold W64.two64. lia. }

    pose proof (proj1 (Forall_forall _ _) (St.so_ops _ _ _ _ _ _ HS) _ (UnreggPre.TwinB.find_op_In _ _ _ FZ)) as HO. cbn [op_id op_args map] in HO.
    pose proof (OPS_holds_ssh _ _ HO) as SSH. fold m in SSH.
    assert (VAL : forall i, 0 <= i < to_Z len -> St.rb bsegs m (A + i) <> None /\ (rg_w rr = true -> St.wb bsegs m (A + i) = true)).
    { intros i Hi. destruct (RV (A + i) ltac:(unfold A; lia)) as (V1 & V2 & _). split; assumption. }
    split; [unfold AIMG_HI; lia|]. split; [lia|]. split; [right; exact SPA|].
    split.
    { destruct (mapped_bytes m (Z.to_nat (to_Z len)) A ltac:(lia) ltac:(lia)) as (bs & LEN & BY).
      - intros i Hi. apply VAL. lia.
      - exists bs. split; assumption. }
    split.
    { intros NWt. subst needw. cbn [implb] in NW.
      apply (UnreggLib.TwinB.mapped_chunk bsegs m (Z.to_nat (to_Z len)) A ltac:(lia) ltac:(lia)).
      intros i Hi. destruct (VAL i ltac:(lia)) as [V1 V2]. split; [exact (V2 NW)| exact V1]. }
    split; [split; [lia|]; right; unfold SH.KHIGH, SH.KEND; lia|].
    split.
    { split; [lia|]. split; [lia|]. intros G _ G1 G2. exists (Z_to_bv 8 0). split; [| left; reflexivity].
      unfold AM.wa, ASHOFF. apply raw_of_view; [lia|].
      apply (RangeFX.TwinB.RangeFX.shadow_zero_sound bsegs OPS st k o len E ms mo HS Q0 ltac:(lia)); rewrite ?DEN; lia. }
    split; [apply (rng_sub _ _ _ _ _ (ACCT_rng _ _ _ _ _ _ AC)); lia|].
    exists (A / 64 * 64), ((A + to_Z len + 63) / 64 * 64).
    assert (H1 : A / 64 * 64 <= A /\ A < A / 64 * 64 + 64) by (Z.div_mod_to_equations; lia).
    assert (H2 : A + to_Z len <= (A + to_Z len + 63) / 64 * 64 /\ (A + to_Z len + 63) / 64 * 64 <= 2 ^ 47) by (Z.div_mod_to_equations; lia).
    split; [repeat split; try lia; try (apply Z_mod_mult); unfold SH.KEND; lia|].
    split; [apply (ssh_wr_at m _ _ SSH); lia|].
    apply (rng_sub _ _ _ _ _ (ACCT_rng_stk_sh _ _ _ _ _ _ AC)).
    + apply shad_mono. lia.
    + pose proof (shad_mono _ _ (proj2 H2)) as S3. rewrite shad_top in S3. lia.
Qed.
End Facts.
End TwinB.
