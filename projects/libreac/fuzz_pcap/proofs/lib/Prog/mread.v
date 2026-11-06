(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel memcpy_c mread_c.
Import ListNotations.
Open Scope Z_scope.

Lemma rw_cells_app_l : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) -> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2 [[Hwf Hb] (H0 & H1 & H2)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  rewrite cells_size_app in H1, H2.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply H2. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H2. lia.
Qed.

Lemma rw_cells_app_r : forall segs m A cs1 cs2,
  rw_cells segs m A cs1 -> rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros segs m A cs1 cs2 [[W1 B1] (H0 & H1 & H2)] [[W2 B2] (G0 & G1 & G2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))).
    + apply H2. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply G2. lia.
Qed.

Lemma rw_cells_CB_split2 : forall segs m A n k junk,
  rw_cells segs m A [CB n junk] -> (k <= n)%nat ->
  rw_cells segs m A [CB k (firstn k junk)] /\ rw_cells segs m (A + Z.of_nat k) [CB (n - k) (skipn k junk)].
Proof.
  intros segs m A n k junk H Hk.
  assert (Hl : length junk = n) by (destruct H as [[[Hl _] _] _]; exact Hl).
  apply (rw_cells_split_CB segs m A [] n junk [] [k; (n - k)%nat]) in H; [|cbn; lia].
  cbn [app mk_CB_cells] in H.
  rewrite (firstn_all2 (n := (n - k)%nat) (skipn k junk)) in H by (rewrite length_skipn; lia).
  change [CB k (firstn k junk); CB (n - k) (skipn k junk)] with ([CB k (firstn k junk)] ++ [CB (n - k) (skipn k junk)]) in H.
  apply rw_cells_app_l in H. cbn [cells_size csize] in H. rewrite Nat.add_0_r in H. exact H.
Qed.

Lemma rw_cells_CB_join : forall segs m A k j bs1 bs2,
  rw_cells segs m A [CB k bs1] -> rw_cells segs m (A + Z.of_nat k) [CB j bs2] ->
  rw_cells segs m A [CB (k + j) (bs1 ++ bs2)].
Proof.
  intros segs m A k j bs1 bs2 H1 H2.
  assert (H : rw_cells segs m A ([] ++ [CB k bs1; CB j bs2] ++ [])).
  { change ([] ++ [CB k bs1; CB j bs2] ++ []) with ([CB k bs1] ++ [CB j bs2]).
    apply rw_cells_app_r; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H2. }
  apply rw_cells_merge in H.
  cbn [cells_size csize cells_bytes cbytes app] in H. rewrite Nat.add_0_r, app_nil_r in H. exact H.
Qed.

Lemma rw_cells_CB_eq : forall segs m A A' k k' bs,
  rw_cells segs m A [CB k bs] -> A = A' -> k = k' -> rw_cells segs m A' [CB k' bs].
Proof. intros; subst; assumption. Qed.

Lemma rw_cells_eq : forall segs m A A' cs cs',
  rw_cells segs m A cs -> A = A' -> cs = cs' -> rw_cells segs m A' cs'.
Proof. intros; subst; assumption. Qed.

Lemma bytes_at_eq : forall segs m a a' bs bs',
  bytes_at segs m a bs -> a = a' -> bs = bs' -> bytes_at segs m a' bs'.
Proof. intros; subst; assumption. Qed.

Lemma bytes_at_sub : forall segs m a bs k j,
  bytes_at segs m a bs -> (k + j <= length bs)%nat ->
  bytes_at segs m (a + Z.of_nat k) (firstn j (skipn k bs)).
Proof.
  intros segs m a bs k j H Hl.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia.
  rewrite <- (firstn_skipn j (skipn k bs)) in H. apply bytes_at_app in H. tauto.
Qed.

Lemma land_ones64_l : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
  apply Z.mod_small. lia.
Qed.

Definition mhead (h b n : Z) (flags pad0 rpos rend prev next mode pad1 pos pad2 : word) (ung : list byte) : list cell :=
  [ C4 flags; C4 pad0; C8 rpos; C8 rend; C8 (wz A_MCLOSE);
    C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
    C8 (wz A_MREAD); C8 (wz A_MWRITE); C8 (wz A_MSEEK); C8 (wz (h + 280)); C8 (wz 1024);
    C8 prev; C8 next;
    C4 (wz 4294967295); C4 (wz 0); C8 (wz 0); C4 mode; C4 (wz 4294967295); C4 (wz 4294967295); C4 pad1;
    C8 (wz (h + 232));
    C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
    C8 pos; C8 (wz n); C8 (wz n); C8 (wz b); C4 (wz 114); C4 pad2;
    CB 8 ung ].

Lemma mfile_cells_eq : forall h b n flags pad0 rpos rend prev next mode pad1 pos pad2 ung buf,
  mfile_cells h b n flags pad0 rpos rend prev next mode pad1 pos pad2 ung buf =
  mhead h b n flags pad0 rpos rend prev next mode pad1 pos pad2 ung ++ [CB 1024 buf].
Proof. reflexivity. Qed.

Lemma mhead_size : forall h b n flags pad0 rpos rend prev next mode pad1 pos pad2 ung,
  cells_size (mhead h b n flags pad0 rpos rend prev next mode pad1 pos pad2 ung) = 280%nat.
Proof. reflexivity. Qed.

Lemma rw_cells_CB_bytes : forall segs m A n bs, rw_cells segs m A [CB n bs] -> bytes_at segs m A bs.
Proof. intros segs m A n bs [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Lemma mfile_rebuild : forall m h b Fc fl md q pv nx pad0 pad1 pad2 ung buf r2 S2 hd,
  rw_cells rsegs m h hd ->
  hd = mhead h b (Z.of_nat (length Fc)) fl pad0 (rpos_of h (Some (0, r2))) (rend_of h (Some (0, r2))) pv nx md pad1 (wz q) pad2 ung ->
  rw_cells rsegs m (h + 280) [CB (Z.to_nat r2) S2] ->
  rw_cells rsegs m (h + 280 + r2) [CB (1024 - Z.to_nat r2) (skipn (Z.to_nat r2) buf)] ->
  length ung = 8%nat -> length buf = 1024%nat -> 0 < h -> h mod 16 = 0 ->
  0 <= r2 <= 1024 -> r2 <= q <= Z.of_nat (length Fc) ->
  S2 = firstn (Z.to_nat r2) (skipn (Z.to_nat (q - r2)) Fc) ->
  bytes_at rsegs m b Fc -> 0 < b -> (h + 1304 <= b \/ b + Z.of_nat (length Fc) <= h) ->
  mfile m h b Fc fl md q (Some (0, r2)) pv nx.
Proof.
  intros m h b Fc fl md q pv nx pad0 pad1 pad2 ung buf r2 S2 hd HH Ehd HM HR LU LB H0 H16 R0 RQ ES BF B0 HBH.
  subst hd.
  assert (LS : length S2 = Z.to_nat r2).
  { rewrite ES, firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. }
  unfold mfile, mfile_raw. exists (S2 ++ skipn (Z.to_nat r2) buf).
  split; [|split; [lia|split; [|split; [exact BF|split; [exact B0|exact HBH]]]]].
  - exists pad0, pad1, pad2, ung.
    split; [|split; [exact LU|split; [|split; [exact H0|exact H16]]]].
    + rewrite mfile_cells_eq. apply rw_cells_app_r; [exact HH|].
      rewrite mhead_size. change (Z.of_nat 280) with 280.
      apply (rw_cells_CB_eq _ _ (h + 280) _ (Z.to_nat r2 + (1024 - Z.to_nat r2)) 1024 _); [| reflexivity | lia].
      apply rw_cells_CB_join; [exact HM|]. rewrite Z2Nat.id by lia. exact HR.
    + rewrite length_app, LS, length_skipn, LB. lia.
  - refine (conj _ (conj _ (conj _ _))); [lia | lia | lia |].
    rewrite Z.sub_0_r. change (skipn (Z.to_nat 0) (S2 ++ skipn (Z.to_nat r2) buf)) with (S2 ++ skipn (Z.to_nat r2) buf).
    rewrite firstn_app, LS, Nat.sub_diag, firstn_O, app_nil_r.
    rewrite ES, firstn_firstn, Nat.min_id. reflexivity.
Qed.

Ltac ulia := rewrite ?unsigned_lit by lia; lia.

Ltac br_cond := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; rewrite ?unsigned_lit by lia; solve_cond_rec.
Ltac br_true := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with true; [cbv iota | symmetry; br_cond] end.
Ltac br_false := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with false; [cbv iota | symmetry; br_cond] end.

Ltac post_call_u segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  repeat match type of PO with context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) in PO by lia end;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Ltac call_memcpy HMC BS RW :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply HMC;
      [ eapply bytes_at_eq; [exact BS | ulia | reflexivity]
      | ulia
      | eapply rw_cells_CB_eq; [exact RW | ulia | ulia]
      | ulia
      | assumption ]
    | post_call_u rsegs mm ] end.

Ltac cells_eq_tac :=
  unfold mhead, rpos_of, rend_of, wz, A_MCLOSE, A_MREAD, A_MWRITE, A_MSEEK;
  repeat (lazymatch goal with
          | |- cons _ _ = cons _ _ => f_equal
          | |- C4 _ = C4 _ => f_equal
          | |- C8 _ = C8 _ => f_equal
          end);
  first [ reflexivity | f_equal; lia ].

Local Ltac OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib.Step.addr_eq_tac ::=
  first [ symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ]
        | apply wa_of_var; lia ].

Theorem mread_holds : memcpy_contract -> mread_contract.
Proof.
  intros HMC. unfold mread_contract, MREAD_FN, MREAD_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo b Fc md q rb pv nx junk
    HMF HRL HD L1 DH DB DS MI ST LO HLO BLO.
  unfold mfile, mfile_raw in HMF.
  destruct HMF as (buf & (pad0 & pad1 & pad2 & ung & HC & LU & LB & H0 & H16) & Q0 & _ & BF & B0 & HBH).
  clear HRL.
  pose proof (bytes_at_bound _ _ _ _ BF) as BFB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  pose proof (zr_word a1) as Ra1. unfold inr64 in Ra1.
  pose proof (zr_word a2) as Ra2. unfold inr64 in Ra2.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (rw_cells_bound _ _ _ _ HD) as HDB. cbn [cells_size csize] in HDB.
  remember (Z.min (bv_unsigned a2) (Z.of_nat (length Fc) - q)) as t eqn:Et.
  remember (Z.min (Z.of_nat (length Fc) - q - t) 1024) as r2 eqn:Er.
  assert (T0 : 0 <= t <= bv_unsigned a2) by lia.
  assert (T1 : t <= Z.of_nat (length Fc) - q) by lia.
  assert (R0 : 0 <= r2 <= 1024) by lia.
  assert (R1 : r2 <= Z.of_nat (length Fc) - q - t) by lia.
  destruct (rw_cells_CB_split2 _ _ _ _ (Z.to_nat t) _ HD ltac:(lia)) as [RW1 _]. clear HD.
  rewrite mfile_cells_eq in HC. apply rw_cells_app_l in HC. destruct HC as [HCa HCb].
  rewrite mhead_size in HCb. change (Z.of_nat 280) with 280 in HCb.
  destruct (rw_cells_CB_split2 _ _ _ _ (Z.to_nat r2) _ HCb ltac:(lia)) as [BUF1 BUF2]. clear HCb.
  rewrite Z2Nat.id in BUF2 by lia.
  unfold mhead, wz, A_MCLOSE, A_MREAD, A_MWRITE, A_MSEEK in HCa.
  assert (BS1 : bytes_at rsegs m (b + q) (firstn (Z.to_nat t) (skipn (Z.to_nat q) Fc))).
  { pose proof (bytes_at_sub _ _ _ _ (Z.to_nat q) (Z.to_nat t) BF ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. exact E. }
  assert (LS1 : length (firstn (Z.to_nat t) (skipn (Z.to_nat q) Fc)) = Z.to_nat t).
  { rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. }
  assert (BS2 : bytes_at rsegs m (b + (q + t)) (firstn (Z.to_nat r2) (skipn (Z.to_nat (q + t)) Fc))).
  { pose proof (bytes_at_sub _ _ _ _ (Z.to_nat (q + t)) (Z.to_nat r2) BF ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. exact E. }
  assert (LS2 : length (firstn (Z.to_nat r2) (skipn (Z.to_nat (q + t)) Fc)) = Z.to_nat r2).
  { rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. }
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + t);
              (bv_unsigned a0, bv_unsigned a0 + 1304)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. zstep.
  zstep.
  replace (Z.of_nat (length Fc) <? Z.of_nat (length Fc) - q) with false by (symmetry; apply Z.ltb_ge; lia).
  change (Z.b2z false) with 0.
  zstep. zstep.
  rewrite (land_ones64_l (Z.of_nat (length Fc) - q)) by lia.
  zstep. zstep.
  destruct (Z.le_gt_cases (bv_unsigned a2) (Z.of_nat (length Fc) - q)) as [CA|CBr].
  1: assert (FLG : (bv_unsigned a2 >? Z.of_nat (length Fc) - q) = false) by (rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  2: assert (FLG : (bv_unsigned a2 >? Z.of_nat (length Fc) - q) = true) by (rewrite Z.gtb_ltb; apply Z.ltb_lt; lia).
  1: br_true.
  2: br_false.
  2: zstep.
  2: unfold sx32.
  2: zstep. 2: zstep. 2: zstep. 2: zstep.
  all: zstep. all: zstep. all: zstep. all: zstep.
  all: call_memcpy HMC BS1 RW1.
  all: zstep. all: zstep. all: zstep. all: zstep. all: zstep. all: zstep.
  1: destruct (Z.lt_ge_cases (Z.of_nat (length Fc) - q - bv_unsigned a2) 1024) as [CA1|CA2].
  1: br_true.
  2: br_false.
  2: zstep.
  3: br_true.
  all: zstep. all: zstep. all: zstep. all: zstep. all: zstep. all: zstep. all: zstep. all: zstep. all: zstep.
  all: call_memcpy HMC BS2 BUF1.
  all: zstep. all: zstep. all: zstep. all: zstep. all: zstep.
  all: zstep. all: zstep. all: zstep. all: zstep. all: zstep.
  all: release_frame FR ST (bv_unsigned sp).
  all: zstep.
  all: apply evt_done.
  all: unfold mread_post, mread_rem2, mread_t.
  all: rewrite <- Et, <- Er, FLG.
  all: do 16 eexists.
  all: split; [reflexivity|].
  all: split; [unfold wz; apply bv_lit_eq; ulia|].
  all: split; [replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; exact MU|].
  all: split; [assumption|].
  all: split; [assumption|].
  all: split; [exact ST|].
  all: split; [match goal with H : rw_cells _ _ ?A [CB _ ?s] |- bytes_at _ _ ?A ?s => exact (rw_cells_CB_bytes _ _ _ _ _ H) end|].
  all: match goal with HM : rw_cells _ _ (_ + 280) [CB _ _] |- _ =>
         eapply mfile_rebuild with (pad0 := pad0) (pad1 := pad1) (pad2 := pad2) (ung := ung) (buf := buf);
         [ exact HCa | cells_eq_tac | eapply rw_cells_CB_eq; [exact HM | reflexivity | ulia] | exact BUF2
         | exact LU | exact LB | exact H0 | exact H16 | lia | lia
         | match goal with |- _ = firstn _ (skipn (Z.to_nat ?e) _) => replace e with (q + t) by lia; reflexivity end
         | exact BF | exact B0 | exact HBH ] end.
Qed.
