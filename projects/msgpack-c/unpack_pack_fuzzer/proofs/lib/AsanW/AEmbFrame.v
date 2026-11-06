(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import MM_syscalls WStr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AKit AKit2 ARep ARepKit ARepFrame. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface AEmbRep AFrameD.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC. Context {rc : runConstT} {ov : annOV}.

Lemma disjoint_from_sub' : forall (W : list ivl) A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> disjoint_from W A' n'.
Proof. induction W as [|[lo hi] W IH]; cbn; intros A n A' n' H H1 H2; [exact I|]. destruct H as [H H']. split; [lia| eapply IH; eauto]. Qed.

Lemma emb_cells_frameD : forall st m m' (W : list ivl), emb_cells st m -> munch W m m' ->
  disjoint_from W AEMB 56 -> (let '(d, cap, _) := a_emb st in cap = 0 \/ disjoint_from W d cap) -> emb_cells st m'.
Proof.
  intros st m m' W EC MU DA DB. unfold emb_cells in *. destruct (a_emb st) as [[d cap] sz].
  assert (T : forall A cs, rw_cells asegs m A cs -> AEMB <= A -> A + Z.of_nat (cells_size cs) <= AEMB + 56 -> rw_cells asegs m' A cs).
  { intros A cs H H1 H2. eapply cells_frameD; [exact H| exact MU|]. eapply disjoint_from_sub'; [exact DA| exact H1| exact H2]. }
  destruct EC as [MTX EC]. split; [apply T; [exact MTX| unfold AEMB; lia| unfold AEMB; cbn; lia]|].
  destruct (cap =? 0) eqn:C0.
  - destruct EC as (PTR & SZ & VEC). split; [apply T; [exact PTR| lia| unfold AEMB; cbn; lia]|]. split; [exact SZ|]. apply T; [exact VEC| lia| unfold AEMB; cbn; lia].
  - apply Z.eqb_neq in C0. destruct DB as [DB|DB]; [contradiction|].
    destruct EC as (PTR & VEC & P1 & P2 & P3 & P4 & P5 & P6 & (junk & OLD)).
    split; [apply T; [exact PTR| lia| unfold AEMB; cbn; lia]|]. split; [apply T; [exact VEC| lia| unfold AEMB; cbn; lia]|].
    repeat (split; [assumption|]). exists junk. eapply cells_frameD; [exact OLD| exact MU|].
    cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (unfold EMB_INIT in P2; lia). exact DB.
Qed.

Lemma outside_above : forall (W : list ivl) x, Forall (fun iv => AIMG_HI <= fst iv) W -> x < AIMG_HI -> outside W x.
Proof. induction W as [|[lo hi] W IH]; intros x HW Hx; cbn; [exact I|]. inversion HW as [|? ? H1 H2]; subst. cbn [fst] in H1. split; [lia| apply IH; assumption]. Qed.
Lemma disjoint_above : forall (W : list ivl) A k, Forall (fun iv => AIMG_HI <= fst iv) W -> A + k <= AIMG_HI -> disjoint_from W A k.
Proof. induction W as [|[lo hi] W IH]; intros A k HW HA; cbn; [exact I|]. inversion HW as [|? ? H1 H2]; subst. cbn [fst] in H1. split; [lia| apply IH; assumption]. Qed.

Lemma exh_cells_frameD : forall m m' (W : list ivl), exh_cells m -> munch W m m' -> Forall (fun iv => AIMG_HI <= fst iv) W -> exh_cells m'.
Proof.
  intros m m' W (RC & TN & CF & CB) MU HW.
  assert (T : forall A cs, rw_cells asegs m A cs -> A + Z.of_nat (cells_size cs) <= 0x62f000 -> rw_cells asegs m' A cs).
  { intros A cs H HA. eapply cells_frameD; [exact H| exact MU|]. apply disjoint_above; [exact HW| unfold AIMG_HI; exact HA]. }
  destruct RC as (R1 & R2 & R3 & R4 & R5).
  assert (T1 : forall A cs, rw_cells asegs m A cs -> (A + Z.of_nat (cells_size cs) <=? 0x62f000) = true -> rw_cells asegs m' A cs)
    by (intros A cs H HA; apply T; [exact H| apply Z.leb_le; exact HA]).
  split; [unfold rmap_cells; split; [| split; [| split; [| split]]]| split; [| split]]; (eapply T1; [eassumption| reflexivity]).
Qed.

Lemma arelro_frameD : forall m m' (W : list ivl), arelro m -> munch W m m' -> Forall (fun iv => AIMG_HI <= fst iv) W -> arelro m'.
Proof.
  intros m m' W RO MU HW i Hi. rewrite (MU (wa i)); [exact (RO i Hi)|]. unfold ARELRO_LO, ARELRO_HI in Hi.
  unfold wa. rewrite unsigned_lit by lia. apply outside_above; [exact HW| unfold AIMG_HI; lia].
Qed.

Lemma munch_focus : forall (W : list ivl) (m m' : amem) A n, munch W m m' -> 0 <= A ->
  (forall x, A <= x < A + n -> outside W x) -> munch [(0, A); (A + n, 2 ^ 64)]%Z m m'.
Proof.
  intros W m m' A n MU A0 O x Hx. apply MU. apply O. cbn [outside] in Hx. pose proof (bv_unsigned_in_range _ x) as R.
  change (bv_modulus 64) with (2 ^ 64) in R. lia.
Qed.
Lemma cells_frameO : forall (W : list ivl) (m m' : amem) A cs, rw_cells asegs m A cs -> munch W m m' ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells asegs m' A cs.
Proof.
  intros W m m' A cs RC MU O. pose proof (rw_cells_bound asegs _ _ _ RC) as [B0 B1].
  eapply AFrameD.cells_frameD; [exact RC| exact (munch_focus W m m' A _ MU B0 O)|]. cbn [disjoint_from]. lia.
Qed.

Definition img_clear (W : list ivl) : Prop := forall x, AIMG_LO <= x < AIMG_HI -> outside W x.
Lemma img_clear_above : forall W : list ivl, Forall (fun iv => AIMG_HI <= fst iv) W -> img_clear W.
Proof. intros W HW x Hx. apply outside_above; [exact HW| lia]. Qed.
Lemma img_clear_band : forall W : list ivl, Forall (fun iv => AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) W -> img_clear W.
Proof.
  intros W HW x Hx. induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|]. inversion HW as [|? ? H1 H2]; subst. cbn [fst snd] in H1.
  split; [lia| exact (IH H2)].
Qed.
Lemma init_cache_emb : forall st, a_emb (init_cache st) = a_emb st.
Proof. intros st. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma init_cache_exh : forall c st, exh_mem c (init_cache st) = exh_mem c st.
Proof. intros c st. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma img_clear_app : forall W1 W2 : list ivl, img_clear W1 -> img_clear W2 -> img_clear (W1 ++ W2).
Proof.
  intros W1 W2 H1 H2 x Hx. specialize (H1 x Hx). specialize (H2 x Hx). induction W1 as [|[lo hi] W1 IH]; cbn [app outside] in *; [exact H2|].
  destruct H1 as [A B]. split; [exact A| exact (IH B)].
Qed.
Lemma exh_cells_frameO : forall m m' (W : list ivl), exh_cells m -> munch W m m' -> img_clear W -> exh_cells m'.
Proof.
  intros m m' W (RC & TN & CF & CB) MU IC.
  assert (T1 : forall A cs, rw_cells asegs m A cs -> (AIMG_LO <=? A) && (A + Z.of_nat (cells_size cs) <=? AIMG_HI) = true -> rw_cells asegs m' A cs).
  { intros A cs H HA. apply andb_prop in HA as [H1 H2]. apply Z.leb_le in H1, H2. eapply cells_frameO; [exact H| exact MU|]. intros x Hx. apply IC. lia. }
  destruct RC as (R1 & R2 & R3 & R4 & R5).
  split; [unfold rmap_cells; split; [| split; [| split; [| split]]]| split; [| split]]; (eapply T1; [eassumption| reflexivity]).
Qed.
Lemma arelro_frameO : forall m m' (W : list ivl), arelro m -> munch W m m' -> img_clear W -> arelro m'.
Proof.
  intros m m' W RO MU IC i Hi. rewrite (MU (wa i)); [exact (RO i Hi)|]. unfold ARELRO_LO, ARELRO_HI in Hi.
  unfold wa. rewrite unsigned_lit by lia. apply IC. unfold AIMG_LO, AIMG_HI. lia.
Qed.
Lemma emb_cells_frameO : forall st m m' (W : list ivl), emb_cells st m -> munch W m m' -> img_clear W ->
  (let '(d, cap, _) := a_emb st in forall x, d <= x < d + cap -> outside W x) -> emb_cells st m'.
Proof.
  intros st m m' W EC MU IC DB. unfold emb_cells in *. destruct (a_emb st) as [[d cap] sz].
  assert (T : forall A cs, rw_cells asegs m A cs -> AEMB <= A -> A + Z.of_nat (cells_size cs) <= AEMB + 56 -> rw_cells asegs m' A cs).
  { intros A cs H H1 H2. eapply cells_frameO; [exact H| exact MU|]. intros x Hx. apply IC. unfold AEMB, AIMG_LO, AIMG_HI in *. lia. }
  destruct EC as [MTX EC]. split; [apply T; [exact MTX| unfold AEMB; lia| unfold AEMB; cbn; lia]|].
  destruct (cap =? 0) eqn:C0.
  - destruct EC as (PTR & SZ & VEC). split; [apply T; [exact PTR| lia| unfold AEMB; cbn; lia]|]. split; [exact SZ|]. apply T; [exact VEC| lia| unfold AEMB; cbn; lia].
  - destruct EC as (PTR & VEC & P1 & P2 & P3 & P4 & P5 & P6 & (junk & OLD)).
    split; [apply T; [exact PTR| lia| unfold AEMB; cbn; lia]|]. split; [apply T; [exact VEC| lia| unfold AEMB; cbn; lia]|].
    repeat (split; [assumption|]). exists junk. eapply cells_frameO; [exact OLD| exact MU|].
    cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (unfold EMB_INIT in P2; lia). exact DB.
Qed.

Definition emb_clr (RESV : list (Z * Z)) (st : astate) : Prop :=
  let '(d, cap, _) := a_emb st in cap = 0 \/ avoids_all d cap (RESV ++ flat_map sec_iv (achunks st)) = true.
Lemma emb_clr_pcov : forall RESV st d cap sz lo hi, emb_clr RESV st -> a_emb st = (d, cap, sz) -> pcov RESV lo hi -> lo < hi ->
  cap <= 0 \/ d + cap <= lo \/ hi <= d.
Proof.
  intros RESV st d cap sz lo hi EC EA PC LH. unfold emb_clr in EC. rewrite EA in EC. destruct EC as [Z0|AV]; [left; lia|].
  unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
  destruct (Z_le_gt_dec cap 0) as [LE|GT]; [left; exact LE| right]. exact (pcov_clear _ _ _ _ _ PC AV LH ltac:(lia)).
Qed.

Lemma exh_mem_clear_same : forall c s, exh_mem c (exh_clear c s) = false.
Proof.
  intros c s. unfold exh_mem, exh_clear. destruct s. cbn. induction a_exh as [|x l IH]; [reflexivity|]. cbn.
  destruct (x =? c) eqn:Q; cbn; [exact IH|]. rewrite IH. rewrite Z.eqb_sym, Q. reflexivity.
Qed.
Lemma get_cls_exh_clear : forall c s c', get_cls (exh_clear c s) c' = get_cls s c'.
Proof. intros c s c'. destruct s. reflexivity. Qed.
Lemma a_emb_exh_clear : forall c s, a_emb (exh_clear c s) = a_emb s.
Proof. intros c s. destruct s. reflexivity. Qed.
End CANSEC.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AKit.TwinB AKit2.TwinB ARep.TwinB ARepKit.TwinB ARepFrame.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap. Import AMalloc_iface.TwinB AEmbRep.TwinB AFrameD.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC. Context {rc : runConstT} {ov : annOV}.

Lemma disjoint_from_sub' : forall (W : list ivl) A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> disjoint_from W A' n'.
Proof. induction W as [|[lo hi] W IH]; cbn; intros A n A' n' H H1 H2; [exact I|]. destruct H as [H H']. split; [lia| eapply IH; eauto]. Qed.

Lemma emb_cells_frameD : forall st m m' (W : list ivl), emb_cells st m -> munch W m m' ->
  disjoint_from W AEMB 56 -> (let '(d, cap, _) := a_emb st in cap = 0 \/ disjoint_from W d cap) -> emb_cells st m'.
Proof.
  intros st m m' W EC MU DA DB. unfold emb_cells in *. destruct (a_emb st) as [[d cap] sz].
  assert (T : forall A cs, rw_cells bsegs m A cs -> AEMB <= A -> A + Z.of_nat (cells_size cs) <= AEMB + 56 -> rw_cells bsegs m' A cs).
  { intros A cs H H1 H2. eapply cells_frameD; [exact H| exact MU|]. eapply disjoint_from_sub'; [exact DA| exact H1| exact H2]. }
  destruct EC as [MTX EC]. split; [apply T; [exact MTX| unfold AEMB; lia| unfold AEMB; cbn; lia]|].
  destruct (cap =? 0) eqn:C0.
  - destruct EC as (PTR & SZ & VEC). split; [apply T; [exact PTR| lia| unfold AEMB; cbn; lia]|]. split; [exact SZ|]. apply T; [exact VEC| lia| unfold AEMB; cbn; lia].
  - apply Z.eqb_neq in C0. destruct DB as [DB|DB]; [contradiction|].
    destruct EC as (PTR & VEC & P1 & P2 & P3 & P4 & P5 & P6 & (junk & OLD)).
    split; [apply T; [exact PTR| lia| unfold AEMB; cbn; lia]|]. split; [apply T; [exact VEC| lia| unfold AEMB; cbn; lia]|].
    repeat (split; [assumption|]). exists junk. eapply cells_frameD; [exact OLD| exact MU|].
    cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (unfold EMB_INIT in P2; lia). exact DB.
Qed.

Lemma outside_above : forall (W : list ivl) x, Forall (fun iv => AIMG_HI <= fst iv) W -> x < AIMG_HI -> outside W x.
Proof. induction W as [|[lo hi] W IH]; intros x HW Hx; cbn; [exact I|]. inversion HW as [|? ? H1 H2]; subst. cbn [fst] in H1. split; [lia| apply IH; assumption]. Qed.
Lemma disjoint_above : forall (W : list ivl) A k, Forall (fun iv => AIMG_HI <= fst iv) W -> A + k <= AIMG_HI -> disjoint_from W A k.
Proof. induction W as [|[lo hi] W IH]; intros A k HW HA; cbn; [exact I|]. inversion HW as [|? ? H1 H2]; subst. cbn [fst] in H1. split; [lia| apply IH; assumption]. Qed.

Lemma exh_cells_frameD : forall m m' (W : list ivl), exh_cells m -> munch W m m' -> Forall (fun iv => AIMG_HI <= fst iv) W -> exh_cells m'.
Proof.
  intros m m' W (RC & TN & CF & CB) MU HW.
  assert (T : forall A cs, rw_cells bsegs m A cs -> A + Z.of_nat (cells_size cs) <= 0x631000 -> rw_cells bsegs m' A cs).
  { intros A cs H HA. eapply cells_frameD; [exact H| exact MU|]. apply disjoint_above; [exact HW| unfold AIMG_HI; exact HA]. }
  destruct RC as (R1 & R2 & R3 & R4 & R5).
  assert (T1 : forall A cs, rw_cells bsegs m A cs -> (A + Z.of_nat (cells_size cs) <=? 0x631000) = true -> rw_cells bsegs m' A cs)
    by (intros A cs H HA; apply T; [exact H| apply Z.leb_le; exact HA]).
  split; [unfold rmap_cells; split; [| split; [| split; [| split]]]| split; [| split]]; (eapply T1; [eassumption| reflexivity]).
Qed.

Lemma arelro_frameD : forall m m' (W : list ivl), arelro m -> munch W m m' -> Forall (fun iv => AIMG_HI <= fst iv) W -> arelro m'.
Proof.
  intros m m' W RO MU HW i Hi. rewrite (MU (wa i)); [exact (RO i Hi)|]. unfold ARELRO_LO, ARELRO_HI in Hi.
  unfold wa. rewrite unsigned_lit by lia. apply outside_above; [exact HW| unfold AIMG_HI; lia].
Qed.

Lemma munch_focus : forall (W : list ivl) (m m' : amem) A n, munch W m m' -> 0 <= A ->
  (forall x, A <= x < A + n -> outside W x) -> munch [(0, A); (A + n, 2 ^ 64)]%Z m m'.
Proof.
  intros W m m' A n MU A0 O x Hx. apply MU. apply O. cbn [outside] in Hx. pose proof (bv_unsigned_in_range _ x) as R.
  change (bv_modulus 64) with (2 ^ 64) in R. lia.
Qed.
Lemma cells_frameO : forall (W : list ivl) (m m' : amem) A cs, rw_cells bsegs m A cs -> munch W m m' ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells bsegs m' A cs.
Proof.
  intros W m m' A cs RC MU O. pose proof (rw_cells_bound bsegs _ _ _ RC) as [B0 B1].
  eapply AFrameD.TwinB.cells_frameD; [exact RC| exact (munch_focus W m m' A _ MU B0 O)|]. cbn [disjoint_from]. lia.
Qed.

Definition img_clear (W : list ivl) : Prop := forall x, AIMG_LO <= x < AIMG_HI -> outside W x.
Lemma img_clear_above : forall W : list ivl, Forall (fun iv => AIMG_HI <= fst iv) W -> img_clear W.
Proof. intros W HW x Hx. apply outside_above; [exact HW| lia]. Qed.
Lemma img_clear_band : forall W : list ivl, Forall (fun iv => AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) W -> img_clear W.
Proof.
  intros W HW x Hx. induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|]. inversion HW as [|? ? H1 H2]; subst. cbn [fst snd] in H1.
  split; [lia| exact (IH H2)].
Qed.
Lemma init_cache_emb : forall st, a_emb (init_cache st) = a_emb st.
Proof. intros st. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma init_cache_exh : forall c st, exh_mem c (init_cache st) = exh_mem c st.
Proof. intros c st. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma img_clear_app : forall W1 W2 : list ivl, img_clear W1 -> img_clear W2 -> img_clear (W1 ++ W2).
Proof.
  intros W1 W2 H1 H2 x Hx. specialize (H1 x Hx). specialize (H2 x Hx). induction W1 as [|[lo hi] W1 IH]; cbn [app outside] in *; [exact H2|].
  destruct H1 as [A B]. split; [exact A| exact (IH B)].
Qed.
Lemma exh_cells_frameO : forall m m' (W : list ivl), exh_cells m -> munch W m m' -> img_clear W -> exh_cells m'.
Proof.
  intros m m' W (RC & TN & CF & CB) MU IC.
  assert (T1 : forall A cs, rw_cells bsegs m A cs -> (AIMG_LO <=? A) && (A + Z.of_nat (cells_size cs) <=? AIMG_HI) = true -> rw_cells bsegs m' A cs).
  { intros A cs H HA. apply andb_prop in HA as [H1 H2]. apply Z.leb_le in H1, H2. eapply cells_frameO; [exact H| exact MU|]. intros x Hx. apply IC. lia. }
  destruct RC as (R1 & R2 & R3 & R4 & R5).
  split; [unfold rmap_cells; split; [| split; [| split; [| split]]]| split; [| split]]; (eapply T1; [eassumption| reflexivity]).
Qed.
Lemma arelro_frameO : forall m m' (W : list ivl), arelro m -> munch W m m' -> img_clear W -> arelro m'.
Proof.
  intros m m' W RO MU IC i Hi. rewrite (MU (wa i)); [exact (RO i Hi)|]. unfold ARELRO_LO, ARELRO_HI in Hi.
  unfold wa. rewrite unsigned_lit by lia. apply IC. unfold AIMG_LO, AIMG_HI. lia.
Qed.
Lemma emb_cells_frameO : forall st m m' (W : list ivl), emb_cells st m -> munch W m m' -> img_clear W ->
  (let '(d, cap, _) := a_emb st in forall x, d <= x < d + cap -> outside W x) -> emb_cells st m'.
Proof.
  intros st m m' W EC MU IC DB. unfold emb_cells in *. destruct (a_emb st) as [[d cap] sz].
  assert (T : forall A cs, rw_cells bsegs m A cs -> AEMB <= A -> A + Z.of_nat (cells_size cs) <= AEMB + 56 -> rw_cells bsegs m' A cs).
  { intros A cs H H1 H2. eapply cells_frameO; [exact H| exact MU|]. intros x Hx. apply IC. unfold AEMB, AIMG_LO, AIMG_HI in *. lia. }
  destruct EC as [MTX EC]. split; [apply T; [exact MTX| unfold AEMB; lia| unfold AEMB; cbn; lia]|].
  destruct (cap =? 0) eqn:C0.
  - destruct EC as (PTR & SZ & VEC). split; [apply T; [exact PTR| lia| unfold AEMB; cbn; lia]|]. split; [exact SZ|]. apply T; [exact VEC| lia| unfold AEMB; cbn; lia].
  - destruct EC as (PTR & VEC & P1 & P2 & P3 & P4 & P5 & P6 & (junk & OLD)).
    split; [apply T; [exact PTR| lia| unfold AEMB; cbn; lia]|]. split; [apply T; [exact VEC| lia| unfold AEMB; cbn; lia]|].
    repeat (split; [assumption|]). exists junk. eapply cells_frameO; [exact OLD| exact MU|].
    cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (unfold EMB_INIT in P2; lia). exact DB.
Qed.

Definition emb_clr (RESV : list (Z * Z)) (st : astate) : Prop :=
  let '(d, cap, _) := a_emb st in cap = 0 \/ avoids_all d cap (RESV ++ flat_map sec_iv (achunks st)) = true.
Lemma emb_clr_pcov : forall RESV st d cap sz lo hi, emb_clr RESV st -> a_emb st = (d, cap, sz) -> pcov RESV lo hi -> lo < hi ->
  cap <= 0 \/ d + cap <= lo \/ hi <= d.
Proof.
  intros RESV st d cap sz lo hi EC EA PC LH. unfold emb_clr in EC. rewrite EA in EC. destruct EC as [Z0|AV]; [left; lia|].
  unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
  destruct (Z_le_gt_dec cap 0) as [LE|GT]; [left; exact LE| right]. exact (pcov_clear _ _ _ _ _ PC AV LH ltac:(lia)).
Qed.

Lemma exh_mem_clear_same : forall c s, exh_mem c (exh_clear c s) = false.
Proof.
  intros c s. unfold exh_mem, exh_clear. destruct s. cbn. induction a_exh as [|x l IH]; [reflexivity|]. cbn.
  destruct (x =? c) eqn:Q; cbn; [exact IH|]. rewrite IH. rewrite Z.eqb_sym, Q. reflexivity.
Qed.
Lemma get_cls_exh_clear : forall c s c', get_cls (exh_clear c s) c' = get_cls s c'.
Proof. intros c s c'. destruct s. reflexivity. Qed.
Lemma a_emb_exh_clear : forall c s, a_emb (exh_clear c s) = a_emb s.
Proof. intros c s. destruct s. reflexivity. Qed.
End CANSEC.
End TwinB.
