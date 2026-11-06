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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase StepSoundMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require GlueA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import GshC.
Import ListNotations.
Import W64 Val St Step CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Module SH := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.

Definition gsh_holds (tab : GshC.tab_t) (m : word -> option byte) : Prop :=
  forall a n v, In (a, n, v) tab -> forall i, 0 <= i < n -> m (AM.wa (a + i)) = Some (Z_to_bv 8 v).
Definition gsh_fp (tab : GshC.tab_t) : list (Z * Z) := map (fun e => (fst (fst e), fst (fst e) + snd (fst e))) tab.

Lemma gsh_byte_sound : forall tab m s v, gsh_holds tab m -> GshC.gsh_byte tab s = Some v -> m (AM.wa s) = Some (Z_to_bv 8 v).
Proof.
  induction tab as [|[[a n] v'] t IH]; intros m s v H B; cbn [GshC.gsh_byte] in B; [discriminate B|].
  destruct ((a <=? s) && (s <? a + n))%bool eqn:Q.
  - injection B as <-. apply andb_prop in Q as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.ltb_lt in Q2.
    pose proof (H a n v' (or_introl eq_refl) (s - a) ltac:(lia)) as X. replace (a + (s - a)) with s in X by lia. exact X.
  - apply (IH m s v); [| exact B]. intros a0 n0 v0 I0. exact (H a0 n0 v0 (or_intror I0)).
Qed.

Lemma gsh_grans_sound : forall tab m fuel G hi, gsh_holds tab m -> GshC.gsh_grans tab fuel G hi = true ->
  forall G', G <= G' < G + Z.of_nat fuel ->
  exists v, m (AM.wa (2147450880 + G')) = Some (Z_to_bv 8 v) /\ (v = 0 \/ (Z.min (8 * G' + 8) hi - 8 * G' <= v /\ v <= 7)).
Proof.
  intros tab m fuel. induction fuel as [|f IH]; intros G hi H C G' HG; [lia|].
  cbn [GshC.gsh_grans] in C. destruct (GshC.gsh_byte tab (2147450880 + G)) as [v|] eqn:B; [|discriminate C].
  apply andb_prop in C as [C1 C2].
  destruct (Z.eq_dec G' G) as [->|NE].
  - exists v. split; [exact (gsh_byte_sound tab m _ v H B)|].
    apply orb_prop in C1 as [C1|C1]; [left; apply Z.eqb_eq; exact C1| right]. apply andb_prop in C1 as [D1 D2].
    apply Z.leb_le in D1, D2. lia.
  - apply (IH (G + 1) hi H C2 G'). lia.
Qed.

Lemma sval_small : forall v, 0 <= v <= 7 -> SH.sval (Z_to_bv 8 v) = v.
Proof.
  intros v Hv. assert (C : v = 0 \/ v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5 \/ v = 6 \/ v = 7) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity.
Qed.

Lemma gsh_unpoisoned_sound : forall tab m lo len, gsh_holds tab m -> GshC.gsh_unpoisoned tab lo len = true -> lo + len <= 2 ^ 64 ->
  SH.unpoisoned m lo (lo + len).
Proof.
  intros tab m lo len H C HB. unfold GshC.gsh_unpoisoned in C.
  apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2]. apply Z.ltb_lt in C1. apply Z.leb_le in C2.
  split; [exact C2|]. split; [exact HB|]. intros G _ G1 G2.
  destruct (gsh_grans_sound tab m _ _ _ H C3 G) as (v & Hv & OK).
  { rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia. }
  exists (Z_to_bv 8 v). unfold ASHOFF. split; [exact Hv|]. unfold SH.gran_ok.
  destruct OK as [->|[O1 O2]]; [left; reflexivity| right].
  assert (V0 : 0 <= v) by lia. rewrite (sval_small v ltac:(lia)). lia.
Qed.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RangePre GshFX.
Unset Nia Cache. Unset Nra Cache.

Section Str.
Context {rc : runConstT}.
Variable OPS : optable.

Lemma gstr_ops : forall C st a len, GshC.gstr asegs C st a = Some len ->
  find_op GshC.GSH_ID (s_ops st) = Some [] /\ find_op GshC.SHMAP_ID (s_ops st) = Some [].
Proof.
  intros C st a len H. unfold GshC.gstr in H. cbv zeta in H.
  destruct (negb (wt a) && (GshC.g_lo C <=? to_Z (wl a)) && (to_Z (wl a) <? GshC.g_hi C))%bool; [|discriminate H].
  destruct (GshC.scan_nul asegs 64 st (wl a) 0%uint63) as [l|]; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Q; [|discriminate H] end.
  apply andb_prop in Q as [Q Q2]. apply andb_prop in Q as [Q Q1].
  destruct (find_op GshC.GSH_ID (s_ops st)) as [[|? ?]|]; try discriminate Q1.
  destruct (find_op GshC.SHMAP_ID (s_ops st)) as [[|? ?]|]; try discriminate Q2. split; reflexivity.
Qed.

Lemma gstr_facts : forall E st ms mo a len (RNG : footprint),
  st_ok asegs OPS E st ms mo -> GshC.gstr asegs GshC.CFG_ASAN st a = Some len ->
  gsh_holds GshC.GSH_TAB_ASAN (ms_mem ms) -> UnreggPre.shmap_holds (ms_mem ms) -> rng_aimg RNG -> rng RNG 0x7fffa000 0xc4000 ->
  let m := ms_mem ms in let S := to_Z (wl a) in let L0 := to_Z len in
  wt a = false /\ 0x22c80 <= S /\ L0 <= 63
  /\ exists str slack, Z.of_nat (length str) = L0 /\ AM.bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) str
       /\ (- (S + L0 + 1)) mod 8 <= Z.of_nat (length slack) /\ S + L0 + 1 + Z.of_nat (length slack) <= 0x23360
       /\ SH.app_blk S (S + (L0 + 1)) /\ SH.unpoisoned m S (S + (L0 + 1)) /\ rng RNG S (L0 + 1 + Z.of_nat (length slack))
       /\ exists RLO RHI, (RLO <= S /\ S + (L0 + 1) <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= SH.KEND)
            /\ AM.wr_at asegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).
Proof.
  intros E st ms mo a len RNG HS H GH SM RI RS m S L0. unfold GshC.gstr in H. cbv zeta in H. fold S in H.
  change (GshC.g_lo GshC.CFG_ASAN) with 0x22c80 in H. change (GshC.g_hi GshC.CFG_ASAN) with 0x23360 in H. change (GshC.g_tab GshC.CFG_ASAN) with GshC.GSH_TAB_ASAN in H.
  destruct (negb (wt a) && (0x22c80 <=? S) && (S <? 0x23360))%bool eqn:Q0; [|discriminate H].
  apply andb_prop in Q0 as [Q0 QH]. apply andb_prop in Q0 as [QT QL]. apply negb_true_iff in QT. apply Z.leb_le in QL. apply Z.ltb_lt in QH.
  destruct (GshC.scan_nul asegs 64 st (wl a) 0%uint63) as [l|] eqn:SC; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Q; [|discriminate H] end. injection H as ->.
  apply andb_prop in Q as [Q _]. apply andb_prop in Q as [Q _]. apply andb_prop in Q as [Q QU]. apply andb_prop in Q as [QE QP]. apply Z.leb_le in QE.
  fold L0 in QE, QP, QU.
  destruct (GshFX.GshFX.scan_nul_sound asegs OPS 64 st (wl a) 0%uint63 len E ms mo HS SC ltac:(change (to_Z 0%uint63) with 0; fold S; change (Z.of_nat 64) with 64; lia))
    as (LR & NZ & ZR). change (to_Z 0%uint63) with 0 in LR, NZ. change (Z.of_nat 64) with 64 in LR. fold S L0 m in LR, NZ, ZR.
  set (pad := (- (S + (L0 + 1))) mod 8) in *.
  assert (PR : 0 <= pad < 8) by (unfold pad; apply Z.mod_pos_bound; lia).
  assert (A1 : to_Z (PrimInt63.add (wl a) (PrimInt63.add len 1%uint63)) = S + (L0 + 1)).
  { rewrite (GshFX.GshFX.add_small (wl a) _); rewrite (GshFX.GshFX.add_small len 1%uint63); change (to_Z 1%uint63) with 1; fold S L0; lia. }
  pose proof (GshFX.GshFX.lit_loads_sound asegs OPS _ st _ E ms mo HS QP ltac:(rewrite A1, Z2Nat.id by lia; lia)) as PL.
  rewrite A1, Z2Nat.id in PL by lia. fold m in PL.

  set (NT := L0 + 1 + pad).
  assert (RD : forall j, 0 <= j < NT -> rb asegs m (S + j) <> None).
  { intros j Hj. destruct (Z_lt_le_dec j L0) as [C1|C1]; [destruct (NZ j ltac:(lia)) as (b & RB & _); rewrite RB; discriminate|].
    destruct (Z.eq_dec j L0) as [->|C2]; [rewrite ZR; discriminate|].
    pose proof (PL (j - (L0 + 1)) ltac:(unfold NT in Hj; lia)) as X. replace (S + (L0 + 1) + (j - (L0 + 1))) with (S + j) in X by lia. exact X. }
  destruct (RangePre.mapped_bytes m (Z.to_nat NT) S ltac:(lia) ltac:(rewrite Z2Nat.id by (unfold NT; lia); unfold NT; lia)
              ltac:(intros i Hi; apply RD; rewrite Z2Nat.id in Hi by (unfold NT; lia); exact Hi)) as (bs & LEN & BY).
  assert (NTH : forall j, 0 <= j < NT -> nth_error bs (Z.to_nat j) = rb asegs m (S + j)).
  { intros j Hj. destruct BY as (_ & _ & BY). specialize (BY (Z.to_nat j) ltac:(rewrite LEN; lia)). rewrite Z2Nat.id in BY by lia.
    rewrite (GlueA.rb_mrdA asegs). symmetry. exact BY. }
  set (str := firstn (Z.to_nat L0) bs). set (tl := skipn (Z.to_nat L0) bs).
  assert (EBS : bs = str ++ tl) by (symmetry; apply firstn_skipn).
  assert (LS : length str = Z.to_nat L0) by (unfold str; rewrite length_firstn, LEN; unfold NT; lia).
  assert (LT : length tl = Z.to_nat (1 + pad)) by (unfold tl; rewrite length_skipn, LEN; unfold NT; lia).
  destruct tl as [|z slack] eqn:ETL; [cbn [length] in LT; lia|].
  assert (Z0 : z = Z_to_bv 8 0).
  { pose proof (NTH L0 ltac:(unfold NT; lia)) as X. rewrite ZR, EBS, nth_error_app2 in X by lia. rewrite LS, Nat.sub_diag in X. cbn [nth_error] in X. congruence. }
  subst z.
  assert (LSL : Z.of_nat (length slack) = pad) by (cbn [length] in LT; lia).
  split; [exact QT|]. split; [exact QL|]. split; [lia|].
  exists str, slack.
  split; [lia|]. split; [rewrite <- EBS; exact BY|].
  split.
  { intros IN. apply In_nth_error in IN as (k & Hk).
    assert (KL : (k < length str)%nat) by (apply nth_error_Some; rewrite Hk; discriminate).
    pose proof (NTH (Z.of_nat k) ltac:(unfold NT; lia)) as X. rewrite Nat2Z.id, EBS, nth_error_app1, Hk in X by exact KL.
    destruct (NZ (Z.of_nat k) ltac:(lia)) as (b & RB & NB). rewrite RB in X. injection X as <-. apply NB. reflexivity. }
  split; [rewrite LSL; unfold pad; replace (S + L0 + 1) with (S + (L0 + 1)) by lia; lia|].
  split; [lia|].
  split; [split; [lia|]; left; unfold SH.KLOW; lia|].
  split; [apply (gsh_unpoisoned_sound _ m S (L0 + 1) GH QU); lia|].
  split; [apply (rng_sub _ _ _ _ _ RI); lia|].
  exists (S / 64 * 64), ((S + (L0 + 1) + 63) / 64 * 64).
  assert (H1 : S / 64 * 64 <= S /\ 0x22c80 <= S / 64 * 64) by (Z.div_mod_to_equations; lia).
  assert (H2 : S + (L0 + 1) <= (S + (L0 + 1) + 63) / 64 * 64 /\ (S + (L0 + 1) + 63) / 64 * 64 <= 0x23380) by (Z.div_mod_to_equations; lia).
  assert (SE : forall x, shad x = ASHOFF + x / 8) by (intros x; unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  split; [repeat split; try lia; try (apply Z_mod_mult); unfold SH.KEND; lia|].
  split.
  - split; [rewrite SE; unfold ASHOFF; Z.div_mod_to_equations; lia|]. split; [rewrite !SE; unfold ASHOFF; Z.div_mod_to_equations; lia|].
    intros i Hi. apply (GlueA.wb_wviewA asegs). apply SM. left. unfold UnreggPre.SH_LO, UnreggPre.SH_HI. rewrite !SE in *. unfold ASHOFF in *.
    clear - Hi H1 H2. Z.div_mod_to_equations. lia.
  - apply (rng_sub _ _ _ _ _ RS); rewrite !SE; unfold ASHOFF; Z.div_mod_to_equations; lia.
Qed.
End Str.

Definition GLOB_N : nat := Z.to_nat 1824.
Definition glob_readable_b {rc : runConstT} : bool :=
  forallb (fun i : nat => match memory_read asegs (Z_to_bv 64 (0x22c60 + Z.of_nat i)) 1 with Some (_ :: _) => true | _ => false end) (seq 0 GLOB_N).
Lemma glob_readable_ok {rc : runConstT} : glob_readable_b = true.
Proof. vm_compute. reflexivity. Qed.
Lemma glob_readable {rc : runConstT} : forall (m : word -> option byte) a, 0x22c60 <= a < 0x23360 -> rb asegs m a <> None.
Proof.
  intros m a Ha. pose proof (proj1 (forallb_forall _ _) glob_readable_ok (Z.to_nat (a - 0x22c60))) as X.
  specialize (X ltac:(apply in_seq; unfold GLOB_N; lia)). cbv beta in X. rewrite Z2Nat.id in X by lia.
  replace (0x22c60 + (a - 0x22c60)) with a in X by lia.
  destruct (memory_read asegs (Z_to_bv 64 a) 1) as [[|b rest]|] eqn:MR; try discriminate X.
  exact (MemP.rb_rom asegs m a b rest MR).
Qed.

Lemma lit_gsh_inv : forall st a len, GshC.lit_gsh GshC.CFG_ASAN st a len = true ->
  wt a = false /\ 0x22c80 <= to_Z (wl a) /\ to_Z (wl a) + to_Z len + 8 <= 0x23360
  /\ GshC.gsh_unpoisoned GshC.GSH_TAB_ASAN (to_Z (wl a)) (to_Z len) = true
  /\ find_op GshC.GSH_ID (s_ops st) = Some [] /\ find_op GshC.SHMAP_ID (s_ops st) = Some [].
Proof.
  intros st a len H. unfold GshC.lit_gsh in H. cbv zeta in H.
  change (GshC.g_lo GshC.CFG_ASAN) with 0x22c80 in H. change (GshC.g_hi GshC.CFG_ASAN) with 0x23360 in H. change (GshC.g_tab GshC.CFG_ASAN) with GshC.GSH_TAB_ASAN in H.
  apply andb_prop in H as [H Q5]. apply andb_prop in H as [H Q4]. apply andb_prop in H as [H Q3]. apply andb_prop in H as [H Q2]. apply andb_prop in H as [Q0 Q1].
  apply negb_true_iff in Q0. apply Z.leb_le in Q1, Q2.
  destruct (find_op GshC.GSH_ID (s_ops st)) as [[|? ?]|]; try discriminate Q4.
  destruct (find_op GshC.SHMAP_ID (s_ops st)) as [[|? ?]|]; try discriminate Q5.
  repeat (split; [first [assumption | reflexivity]|]). reflexivity.
Qed.

Lemma gsh_range_facts_ok {rc : runConstT} : forall (RNG : footprint) (m : word -> option byte) A len,
  gsh_holds GshC.GSH_TAB_ASAN m -> UnreggPre.shmap_holds m -> rng_aimg RNG -> rng RNG 0x7fffa000 0xc4000 ->
  0x22c80 <= A -> 0 < len -> A + len + 8 <= 0x23360 -> GshC.gsh_unpoisoned GshC.GSH_TAB_ASAN A len = true ->
  (exists bs, length bs = Z.to_nat len /\ AM.bytes_at asegs m A bs)
  /\ SH.app_blk A (A + len) /\ SH.unpoisoned m A (A + len) /\ rng RNG A len
  /\ exists RLO RHI, (RLO <= A /\ A + len <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= SH.KEND)
       /\ AM.wr_at asegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).
Proof.
  intros RNG m A len GH SM RI RS HA HN HH QU.
  split.
  { destruct (RangePre.mapped_bytes m (Z.to_nat len) A ltac:(lia) ltac:(lia)) as (bs & LEN & BY).
    - intros i Hi. apply glob_readable. lia.
    - exists bs. split; assumption. }
  split; [split; [lia|]; left; unfold SH.KLOW; lia|].
  split; [apply (gsh_unpoisoned_sound _ m A len GH QU); lia|].
  split; [apply (rng_sub _ _ _ _ _ RI); lia|].
  exists (A / 64 * 64), ((A + len + 63) / 64 * 64).
  assert (H1 : A / 64 * 64 <= A /\ 0x22c80 <= A / 64 * 64) by (Z.div_mod_to_equations; lia).
  assert (H2 : A + len <= (A + len + 63) / 64 * 64 /\ (A + len + 63) / 64 * 64 <= 0x23380) by (Z.div_mod_to_equations; lia).
  assert (SE : forall x, shad x = ASHOFF + x / 8) by (intros x; unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  split; [repeat split; try lia; try (apply Z_mod_mult); unfold SH.KEND; lia|].
  split.
  - split; [rewrite SE; unfold ASHOFF; Z.div_mod_to_equations; lia|]. split; [rewrite !SE; unfold ASHOFF; Z.div_mod_to_equations; lia|].
    intros i Hi. apply (GlueA.wb_wviewA asegs). apply SM. left. unfold UnreggPre.SH_LO, UnreggPre.SH_HI. rewrite !SE in *. unfold ASHOFF in *.
    clear - Hi H1 H2. Z.div_mod_to_equations. lia.
  - apply (rng_sub _ _ _ _ _ RS); rewrite !SE; unfold ASHOFF; Z.div_mod_to_equations; lia.
Qed.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import ABase.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib.
Import GshC.TwinB.

Import ListNotations.
Import W64 Val St Step CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Module SH := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.

Definition gsh_holds (tab : GshC.TwinB.GshC.tab_t) (m : word -> option byte) : Prop :=
  forall a n v, In (a, n, v) tab -> forall i, 0 <= i < n -> m (AM.wa (a + i)) = Some (Z_to_bv 8 v).
Definition gsh_fp (tab : GshC.TwinB.GshC.tab_t) : list (Z * Z) := map (fun e => (fst (fst e), fst (fst e) + snd (fst e))) tab.

Lemma gsh_byte_sound : forall tab m s v, gsh_holds tab m -> GshC.TwinB.GshC.gsh_byte tab s = Some v -> m (AM.wa s) = Some (Z_to_bv 8 v).
Proof.
  induction tab as [|[[a n] v'] t IH]; intros m s v H B; cbn [GshC.TwinB.GshC.gsh_byte] in B; [discriminate B|].
  destruct ((a <=? s) && (s <? a + n))%bool eqn:Q.
  - injection B as <-. apply andb_prop in Q as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.ltb_lt in Q2.
    pose proof (H a n v' (or_introl eq_refl) (s - a) ltac:(lia)) as X. replace (a + (s - a)) with s in X by lia. exact X.
  - apply (IH m s v); [| exact B]. intros a0 n0 v0 I0. exact (H a0 n0 v0 (or_intror I0)).
Qed.

Lemma gsh_grans_sound : forall tab m fuel G hi, gsh_holds tab m -> GshC.TwinB.GshC.gsh_grans tab fuel G hi = true ->
  forall G', G <= G' < G + Z.of_nat fuel ->
  exists v, m (AM.wa (2147450880 + G')) = Some (Z_to_bv 8 v) /\ (v = 0 \/ (Z.min (8 * G' + 8) hi - 8 * G' <= v /\ v <= 7)).
Proof.
  intros tab m fuel. induction fuel as [|f IH]; intros G hi H C G' HG; [lia|].
  cbn [GshC.TwinB.GshC.gsh_grans] in C. destruct (GshC.TwinB.GshC.gsh_byte tab (2147450880 + G)) as [v|] eqn:B; [|discriminate C].
  apply andb_prop in C as [C1 C2].
  destruct (Z.eq_dec G' G) as [->|NE].
  - exists v. split; [exact (gsh_byte_sound tab m _ v H B)|].
    apply orb_prop in C1 as [C1|C1]; [left; apply Z.eqb_eq; exact C1| right]. apply andb_prop in C1 as [D1 D2].
    apply Z.leb_le in D1, D2. lia.
  - apply (IH (G + 1) hi H C2 G'). lia.
Qed.

Lemma sval_small : forall v, 0 <= v <= 7 -> SH.sval (Z_to_bv 8 v) = v.
Proof.
  intros v Hv. assert (C : v = 0 \/ v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5 \/ v = 6 \/ v = 7) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity.
Qed.

Lemma gsh_unpoisoned_sound : forall tab m lo len, gsh_holds tab m -> GshC.TwinB.GshC.gsh_unpoisoned tab lo len = true -> lo + len <= 2 ^ 64 ->
  SH.unpoisoned m lo (lo + len).
Proof.
  intros tab m lo len H C HB. unfold GshC.TwinB.GshC.gsh_unpoisoned in C.
  apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2]. apply Z.ltb_lt in C1. apply Z.leb_le in C2.
  split; [exact C2|]. split; [exact HB|]. intros G _ G1 G2.
  destruct (gsh_grans_sound tab m _ _ _ H C3 G) as (v & Hv & OK).
  { rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia. }
  exists (Z_to_bv 8 v). unfold ASHOFF. split; [exact Hv|]. unfold SH.gran_ok.
  destruct OK as [->|[O1 O2]]; [left; reflexivity| right].
  assert (V0 : 0 <= v) by lia. rewrite (sval_small v ltac:(lia)). lia.
Qed.

Unset Nia Cache. Unset Nra Cache.

Section Str.
Context {rc : runConstT}.
Variable OPS : optable.

Lemma gstr_ops : forall C st a len, GshC.TwinB.GshC.gstr bsegs C st a = Some len ->
  find_op GshC.TwinB.GshC.GSH_ID (s_ops st) = Some [] /\ find_op GshC.TwinB.GshC.SHMAP_ID (s_ops st) = Some [].
Proof.
  intros C st a len H. unfold GshC.TwinB.GshC.gstr in H. cbv zeta in H.
  destruct (negb (wt a) && (GshC.TwinB.GshC.g_lo C <=? to_Z (wl a)) && (to_Z (wl a) <? GshC.TwinB.GshC.g_hi C))%bool; [|discriminate H].
  destruct (GshC.TwinB.GshC.scan_nul bsegs 64 st (wl a) 0%uint63) as [l|]; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Q; [|discriminate H] end.
  apply andb_prop in Q as [Q Q2]. apply andb_prop in Q as [Q Q1].
  destruct (find_op GshC.TwinB.GshC.GSH_ID (s_ops st)) as [[|? ?]|]; try discriminate Q1.
  destruct (find_op GshC.TwinB.GshC.SHMAP_ID (s_ops st)) as [[|? ?]|]; try discriminate Q2. split; reflexivity.
Qed.

Lemma gstr_facts : forall E st ms mo a len (RNG : footprint),
  st_ok bsegs OPS E st ms mo -> GshC.TwinB.GshC.gstr bsegs GshC.TwinB.GshC.CFG_ASAN st a = Some len ->
  gsh_holds GshC.TwinB.GshC.GSH_TAB_ASAN (ms_mem ms) -> UnreggPre.TwinB.shmap_holds (ms_mem ms) -> rng_aimg RNG -> rng RNG 0x7fffa000 0xc5000 ->
  let m := ms_mem ms in let S := to_Z (wl a) in let L0 := to_Z len in
  wt a = false /\ 0x22d00 <= S /\ L0 <= 63
  /\ exists str slack, Z.of_nat (length str) = L0 /\ AM.bytes_at bsegs m S (str ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) str
       /\ (- (S + L0 + 1)) mod 8 <= Z.of_nat (length slack) /\ S + L0 + 1 + Z.of_nat (length slack) <= 0x23500
       /\ SH.app_blk S (S + (L0 + 1)) /\ SH.unpoisoned m S (S + (L0 + 1)) /\ rng RNG S (L0 + 1 + Z.of_nat (length slack))
       /\ exists RLO RHI, (RLO <= S /\ S + (L0 + 1) <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= SH.KEND)
            /\ AM.wr_at bsegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).
Proof.
  intros E st ms mo a len RNG HS H GH SM RI RS m S L0. unfold GshC.TwinB.GshC.gstr in H. cbv zeta in H. fold S in H.
  change (GshC.TwinB.GshC.g_lo GshC.TwinB.GshC.CFG_ASAN) with 0x22d00 in H. change (GshC.TwinB.GshC.g_hi GshC.TwinB.GshC.CFG_ASAN) with 0x23500 in H. change (GshC.TwinB.GshC.g_tab GshC.TwinB.GshC.CFG_ASAN) with GshC.TwinB.GshC.GSH_TAB_ASAN in H.
  destruct (negb (wt a) && (0x22d00 <=? S) && (S <? 0x23500))%bool eqn:Q0; [|discriminate H].
  apply andb_prop in Q0 as [Q0 QH]. apply andb_prop in Q0 as [QT QL]. apply negb_true_iff in QT. apply Z.leb_le in QL. apply Z.ltb_lt in QH.
  destruct (GshC.TwinB.GshC.scan_nul bsegs 64 st (wl a) 0%uint63) as [l|] eqn:SC; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Q; [|discriminate H] end. injection H as ->.
  apply andb_prop in Q as [Q _]. apply andb_prop in Q as [Q _]. apply andb_prop in Q as [Q QU]. apply andb_prop in Q as [QE QP]. apply Z.leb_le in QE.
  fold L0 in QE, QP, QU.
  destruct (GshFX.TwinB.GshFX.scan_nul_sound bsegs OPS 64 st (wl a) 0%uint63 len E ms mo HS SC ltac:(change (to_Z 0%uint63) with 0; fold S; change (Z.of_nat 64) with 64; lia))
    as (LR & NZ & ZR). change (to_Z 0%uint63) with 0 in LR, NZ. change (Z.of_nat 64) with 64 in LR. fold S L0 m in LR, NZ, ZR.
  set (pad := (- (S + (L0 + 1))) mod 8) in *.
  assert (PR : 0 <= pad < 8) by (unfold pad; apply Z.mod_pos_bound; lia).
  assert (A1 : to_Z (PrimInt63.add (wl a) (PrimInt63.add len 1%uint63)) = S + (L0 + 1)).
  { rewrite (GshFX.TwinB.GshFX.add_small (wl a) _); rewrite (GshFX.TwinB.GshFX.add_small len 1%uint63); change (to_Z 1%uint63) with 1; fold S L0; lia. }
  pose proof (GshFX.TwinB.GshFX.lit_loads_sound bsegs OPS _ st _ E ms mo HS QP ltac:(rewrite A1, Z2Nat.id by lia; lia)) as PL.
  rewrite A1, Z2Nat.id in PL by lia. fold m in PL.

  set (NT := L0 + 1 + pad).
  assert (RD : forall j, 0 <= j < NT -> rb bsegs m (S + j) <> None).
  { intros j Hj. destruct (Z_lt_le_dec j L0) as [C1|C1]; [destruct (NZ j ltac:(lia)) as (b & RB & _); rewrite RB; discriminate|].
    destruct (Z.eq_dec j L0) as [->|C2]; [rewrite ZR; discriminate|].
    pose proof (PL (j - (L0 + 1)) ltac:(unfold NT in Hj; lia)) as X. replace (S + (L0 + 1) + (j - (L0 + 1))) with (S + j) in X by lia. exact X. }
  destruct (RangePre.TwinB.mapped_bytes m (Z.to_nat NT) S ltac:(lia) ltac:(rewrite Z2Nat.id by (unfold NT; lia); unfold NT; lia)
              ltac:(intros i Hi; apply RD; rewrite Z2Nat.id in Hi by (unfold NT; lia); exact Hi)) as (bs & LEN & BY).
  assert (NTH : forall j, 0 <= j < NT -> nth_error bs (Z.to_nat j) = rb bsegs m (S + j)).
  { intros j Hj. destruct BY as (_ & _ & BY). specialize (BY (Z.to_nat j) ltac:(rewrite LEN; lia)). rewrite Z2Nat.id in BY by lia.
    rewrite (GlueA.TwinB.rb_mrdA bsegs). symmetry. exact BY. }
  set (str := firstn (Z.to_nat L0) bs). set (tl := skipn (Z.to_nat L0) bs).
  assert (EBS : bs = str ++ tl) by (symmetry; apply firstn_skipn).
  assert (LS : length str = Z.to_nat L0) by (unfold str; rewrite length_firstn, LEN; unfold NT; lia).
  assert (LT : length tl = Z.to_nat (1 + pad)) by (unfold tl; rewrite length_skipn, LEN; unfold NT; lia).
  destruct tl as [|z slack] eqn:ETL; [cbn [length] in LT; lia|].
  assert (Z0 : z = Z_to_bv 8 0).
  { pose proof (NTH L0 ltac:(unfold NT; lia)) as X. rewrite ZR, EBS, nth_error_app2 in X by lia. rewrite LS, Nat.sub_diag in X. cbn [nth_error] in X. congruence. }
  subst z.
  assert (LSL : Z.of_nat (length slack) = pad) by (cbn [length] in LT; lia).
  split; [exact QT|]. split; [exact QL|]. split; [lia|].
  exists str, slack.
  split; [lia|]. split; [rewrite <- EBS; exact BY|].
  split.
  { intros IN. apply In_nth_error in IN as (k & Hk).
    assert (KL : (k < length str)%nat) by (apply nth_error_Some; rewrite Hk; discriminate).
    pose proof (NTH (Z.of_nat k) ltac:(unfold NT; lia)) as X. rewrite Nat2Z.id, EBS, nth_error_app1, Hk in X by exact KL.
    destruct (NZ (Z.of_nat k) ltac:(lia)) as (b & RB & NB). rewrite RB in X. injection X as <-. apply NB. reflexivity. }
  split; [rewrite LSL; unfold pad; replace (S + L0 + 1) with (S + (L0 + 1)) by lia; lia|].
  split; [lia|].
  split; [split; [lia|]; left; unfold SH.KLOW; lia|].
  split; [apply (gsh_unpoisoned_sound _ m S (L0 + 1) GH QU); lia|].
  split; [apply (rng_sub _ _ _ _ _ RI); lia|].
  exists (S / 64 * 64), ((S + (L0 + 1) + 63) / 64 * 64).
  assert (H1 : S / 64 * 64 <= S /\ 0x22d00 <= S / 64 * 64) by (Z.div_mod_to_equations; lia).
  assert (H2 : S + (L0 + 1) <= (S + (L0 + 1) + 63) / 64 * 64 /\ (S + (L0 + 1) + 63) / 64 * 64 <= 0x23500) by (Z.div_mod_to_equations; lia).
  assert (SE : forall x, shad x = ASHOFF + x / 8) by (intros x; unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  split; [repeat split; try lia; try (apply Z_mod_mult); unfold SH.KEND; lia|].
  split.
  - split; [rewrite SE; unfold ASHOFF; Z.div_mod_to_equations; lia|]. split; [rewrite !SE; unfold ASHOFF; Z.div_mod_to_equations; lia|].
    intros i Hi. apply (GlueA.TwinB.wb_wviewA bsegs). apply SM. left. unfold UnreggPre.TwinB.SH_LO, UnreggPre.TwinB.SH_HI. rewrite !SE in *. unfold ASHOFF in *.
    clear - Hi H1 H2. Z.div_mod_to_equations. lia.
  - apply (rng_sub _ _ _ _ _ RS); rewrite !SE; unfold ASHOFF; Z.div_mod_to_equations; lia.
Qed.
End Str.

Definition GLOB_N : nat := Z.to_nat 2112.
Definition glob_readable_b {rc : runConstT} : bool :=
  forallb (fun i : nat => match memory_read bsegs (Z_to_bv 64 (0x22d00 + Z.of_nat i)) 1 with Some (_ :: _) => true | _ => false end) (seq 0 GLOB_N).
Lemma glob_readable_ok {rc : runConstT} : glob_readable_b = true.
Proof. vm_compute. reflexivity. Qed.
Lemma glob_readable {rc : runConstT} : forall (m : word -> option byte) a, 0x22d00 <= a < 0x23500 -> rb bsegs m a <> None.
Proof.
  intros m a Ha. pose proof (proj1 (forallb_forall _ _) glob_readable_ok (Z.to_nat (a - 0x22d00))) as X.
  specialize (X ltac:(apply in_seq; unfold GLOB_N; lia)). cbv beta in X. rewrite Z2Nat.id in X by lia.
  replace (0x22d00 + (a - 0x22d00)) with a in X by lia.
  destruct (memory_read bsegs (Z_to_bv 64 a) 1) as [[|b rest]|] eqn:MR; try discriminate X.
  exact (MemP.rb_rom bsegs m a b rest MR).
Qed.

Lemma lit_gsh_inv : forall st a len, GshC.TwinB.GshC.lit_gsh GshC.TwinB.GshC.CFG_ASAN st a len = true ->
  wt a = false /\ 0x22d00 <= to_Z (wl a) /\ to_Z (wl a) + to_Z len + 8 <= 0x23500
  /\ GshC.TwinB.GshC.gsh_unpoisoned GshC.TwinB.GshC.GSH_TAB_ASAN (to_Z (wl a)) (to_Z len) = true
  /\ find_op GshC.TwinB.GshC.GSH_ID (s_ops st) = Some [] /\ find_op GshC.TwinB.GshC.SHMAP_ID (s_ops st) = Some [].
Proof.
  intros st a len H. unfold GshC.TwinB.GshC.lit_gsh in H. cbv zeta in H.
  change (GshC.TwinB.GshC.g_lo GshC.TwinB.GshC.CFG_ASAN) with 0x22d00 in H. change (GshC.TwinB.GshC.g_hi GshC.TwinB.GshC.CFG_ASAN) with 0x23500 in H. change (GshC.TwinB.GshC.g_tab GshC.TwinB.GshC.CFG_ASAN) with GshC.TwinB.GshC.GSH_TAB_ASAN in H.
  apply andb_prop in H as [H Q5]. apply andb_prop in H as [H Q4]. apply andb_prop in H as [H Q3]. apply andb_prop in H as [H Q2]. apply andb_prop in H as [Q0 Q1].
  apply negb_true_iff in Q0. apply Z.leb_le in Q1, Q2.
  destruct (find_op GshC.TwinB.GshC.GSH_ID (s_ops st)) as [[|? ?]|]; try discriminate Q4.
  destruct (find_op GshC.TwinB.GshC.SHMAP_ID (s_ops st)) as [[|? ?]|]; try discriminate Q5.
  repeat (split; [first [assumption | reflexivity]|]). reflexivity.
Qed.

Lemma gsh_range_facts_ok {rc : runConstT} : forall (RNG : footprint) (m : word -> option byte) A len,
  gsh_holds GshC.TwinB.GshC.GSH_TAB_ASAN m -> UnreggPre.TwinB.shmap_holds m -> rng_aimg RNG -> rng RNG 0x7fffa000 0xc5000 ->
  0x22d00 <= A -> 0 < len -> A + len + 8 <= 0x23500 -> GshC.TwinB.GshC.gsh_unpoisoned GshC.TwinB.GshC.GSH_TAB_ASAN A len = true ->
  (exists bs, length bs = Z.to_nat len /\ AM.bytes_at bsegs m A bs)
  /\ SH.app_blk A (A + len) /\ SH.unpoisoned m A (A + len) /\ rng RNG A len
  /\ exists RLO RHI, (RLO <= A /\ A + len <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= SH.KEND)
       /\ AM.wr_at bsegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).
Proof.
  intros RNG m A len GH SM RI RS HA HN HH QU.
  split.
  { destruct (RangePre.TwinB.mapped_bytes m (Z.to_nat len) A ltac:(lia) ltac:(lia)) as (bs & LEN & BY).
    - intros i Hi. apply glob_readable. lia.
    - exists bs. split; assumption. }
  split; [split; [lia|]; left; unfold SH.KLOW; lia|].
  split; [apply (gsh_unpoisoned_sound _ m A len GH QU); lia|].
  split; [apply (rng_sub _ _ _ _ _ RI); lia|].
  exists (A / 64 * 64), ((A + len + 63) / 64 * 64).
  assert (H1 : A / 64 * 64 <= A /\ 0x22d00 <= A / 64 * 64) by (Z.div_mod_to_equations; lia).
  assert (H2 : A + len <= (A + len + 63) / 64 * 64 /\ (A + len + 63) / 64 * 64 <= 0x23500) by (Z.div_mod_to_equations; lia).
  assert (SE : forall x, shad x = ASHOFF + x / 8) by (intros x; unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  split; [repeat split; try lia; try (apply Z_mod_mult); unfold SH.KEND; lia|].
  split.
  - split; [rewrite SE; unfold ASHOFF; Z.div_mod_to_equations; lia|]. split; [rewrite !SE; unfold ASHOFF; Z.div_mod_to_equations; lia|].
    intros i Hi. apply (GlueA.TwinB.wb_wviewA bsegs). apply SM. left. unfold UnreggPre.TwinB.SH_LO, UnreggPre.TwinB.SH_HI. rewrite !SE in *. unfold ASHOFF in *.
    clear - Hi H1 H2. Z.div_mod_to_equations. lia.
  - apply (rng_sub _ _ _ _ _ RS); rewrite !SE; unfold ASHOFF; Z.div_mod_to_equations; lia.
Qed.
End TwinB.
