(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, addresses and numbers changed; 976 of its 1075 lines of code are new or changed and 647 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_reject_clean_starved.v, with its module names and numbers changed; 714 of its 791 lines of code are new or changed and 998 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_as_written.v, with its module paths, module names, addresses and numbers changed; 1718 of its 1786 lines of code are new or changed and 723 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_no_overread.v, with its module paths, module names and numbers changed; 1318 of its 1476 lines of code are new or changed and 1628 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require YL01 YI04 YO10.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger LedgerFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import HState.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import HStateRoom ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import fuzz_free_c fuzz_malloc_c preset_base64_encode_c preset_base64_decode_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import pj_string_c pj_set_c pj_free_c pj_parse_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterApp WriterAppFacts WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import put_c put_string_c indent_c write_value_c pj_write_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import check_round_trip_c check_round_trip_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require HsKindB check_reject_clean_starved past_nul.
Import ListNotations.
Local Open Scope Z_scope.


Lemma crt_bytes_some : forall m a bs i, Mem.bytes_at rsegs m a bs -> 0 <= i < Z.of_nat (length bs) ->
  mbyte rsegs m (a + i) <> None.
Proof.
  intros m a bs i (_ & _ & H) Hi. pose proof (H (Z.to_nat i) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia.
  change (mbyte rsegs m (a + i)) with (Mem.mrd rsegs m (Mem.wa (a + i))). rewrite E.
  apply nth_error_Some. lia.
Qed.

Definition xblk (ak : Z * Z) : Z * Z := (fst ak - 16, snd ak + 16).

Lemma lsum_perm : forall l l', Permutation l l' -> lsum l = lsum l'.
Proof.
  intros l l' H. induction H as [|[a k] l l' _ IH|[a k] [b j] l|l l' l'' _ IH1 _ IH2]; cbn [lsum]; lia.
Qed.

Lemma crt_nd_app_not : forall {X : Type} (l1 l2 : list X) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  intros X l1. induction l1 as [|a l1 IH]; intros l2 x ND H1 H2; [destruct H1|]. cbn [app] in ND.
  apply NoDup_cons_iff in ND as [Hn ND].
  destruct H1 as [<-|H1]; [apply Hn; apply in_or_app; right; exact H2 | exact (IH l2 x ND H1 H2)].
Qed.

Lemma crt_nd_app : forall {X : Type} (l1 l2 : list X), List.NoDup l1 -> List.NoDup l2 ->
  (forall x, In x l1 -> ~ In x l2) -> List.NoDup (l1 ++ l2).
Proof.
  intros X l1. induction l1 as [|a l1 IH]; intros l2 N1 N2 H; [exact N2|]. cbn [app].
  apply NoDup_cons_iff in N1 as [Hn N1]. constructor.
  - intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Hn Hin) | exact (H a (or_introl eq_refl) Hin)].
  - apply IH; [exact N1 | exact N2 |]. intros x Hx. exact (H x (or_intror Hx)).
Qed.

Lemma ledger_perm : forall B L A mem Lam Lam' peak c f, Permutation Lam Lam' ->
  ledger B L A mem Lam peak c f -> ledger B L A mem Lam' peak c f.
Proof.
  intros B L A mem Lam Lam' peak c f HP (W & HPk & HC & HF & HN & HB).
  rewrite (lsum_perm Lam Lam' HP) in W, HPk.
  split; [exact W|]. split; [exact HPk|]. split; [exact HC|]. split; [exact HF|].
  split; [apply NoDup_ListNoDup; apply NoDup_ListNoDup in HN; exact (Permutation_NoDup (Permutation_map fst HP) HN)|].
  exact (Permutation_Forall HP HB).
Qed.

Lemma calls_le : forall tr, (calls tr <= length tr)%nat.
Proof. induction tr as [|e tr IH]; cbn [calls length]; [lia|]. destruct (is_call e); lia. Qed.

Lemma room_cap : forall tr (b : sbound) N,
  Forall (fun e => Z.of_nat (esize e) + 16 <= CRT_SIZE) tr -> (length tr <= N)%nat -> hs_cap b N CRT_SIZE ->
  room_run sb_form b tr /\ hs_cap (rf_run sb_form b tr) (N - length tr) CRT_SIZE.
Proof.
  unfold rf_run. induction tr as [|e tr IH]; intros b N HF HN HC.
  - split; [exact I|]. cbn [fold_left length]. rewrite Nat.sub_0_r. exact HC.
  - inversion HF as [|? ? He HF']; subst. cbn [length] in HN.
    destruct N as [|N]; [lia|].
    assert (HS : 0 <= CRT_SIZE <= 2 ^ 28 - 2 ^ 13) by (unfold CRT_SIZE; lia).
    assert (HS2 : CRT_SIZE <= 2 ^ 28) by (unfold CRT_SIZE; lia).
    destruct e as [n|m n|n|n]; cbn [room_run fold_left rf_ev esize is_call length rf_malloc rf_free rf_room
      rf_realloc rf_grow sb_form] in *.
    + destruct (IH (sb_malloc b (Z.of_nat n + 16)) N HF' ltac:(lia)
        (hs_cap_malloc b N CRT_SIZE (Z.of_nat n + 16) ltac:(lia) HC)) as [R1 R2].
      split; [split; [intros _; split; [exact (hs_cap_room b N CRT_SIZE (Z.of_nat n + 16) HS ltac:(lia) HC) | lia] | exact R1]|].
      exact R2.
    + assert (HB : hs_cap (if Z.of_nat m =? 0 then sb_malloc b (Z.of_nat n + 16)
                           else sb_realloc b (Z.of_nat m + 16) (Z.of_nat n + 16)) N CRT_SIZE).
      { destruct (Z.of_nat m =? 0); [apply hs_cap_malloc | apply hs_cap_realloc]; (lia || exact HC). }
      destruct (IH _ N HF' ltac:(lia) HB) as [R1 R2].
      split; [split; [intros _; split; [exact (hs_cap_room b N CRT_SIZE (Z.of_nat n + 16) HS ltac:(lia) HC) | lia] | exact R1]|].
      exact R2.
    + destruct (IH b N HF' ltac:(lia) (hs_cap_le b (Datatypes.S N) N CRT_SIZE ltac:(lia) ltac:(lia) HC))
        as [R1 R2].
      split; [split; [intros _; split; [exact (hs_cap_room b N CRT_SIZE (Z.of_nat n + 16) HS ltac:(lia) HC) | lia] | exact R1]|].
      exact R2.
    + destruct (IH (sb_free b (Z.of_nat n + 16)) (Datatypes.S N) HF' ltac:(lia)
        (hs_cap_free b (Datatypes.S N) CRT_SIZE (Z.of_nat n + 16) ltac:(lia) HC)) as [R1 R2].
      split; [split; [intros H; discriminate H | exact R1]|].
      exact (hs_cap_le _ (Datatypes.S N - length tr) (N - length tr) CRT_SIZE ltac:(lia) ltac:(lia) R2).
Qed.

Lemma set_trace_ok : forall n cap klen, 0 <= n <= 2 -> 0 <= klen -> klen + 17 <= CRT_SIZE -> n <= cap ->
  Forall (fun e => Z.of_nat (esize e) + 16 <= CRT_SIZE) (set_trace n cap klen) /\
  (length (set_trace n cap klen) <= 3)%nat.
Proof.
  intros n cap klen Hn Hk Hs Hc. unfold set_trace. unfold CRT_SIZE in *.
  destruct (Z.eqb_spec n cap) as [<-|Hne]; cbn [app length].
  - split; [|lia]. unfold cap2.
    destruct (Z.eqb_spec n 0); repeat constructor; cbn [esize]; rewrite ?Z2Nat.id by lia; lia.
  - split; [repeat constructor; cbn [esize]; rewrite Z2Nat.id by lia; lia | lia].
Qed.

Lemma sum_piece_lens : forall P, fold_right Z.add 0 (piece_lens P) = Z.of_nat (length (concat P)).
Proof.
  induction P as [|b P IH]; [reflexivity|]. rewrite piece_lens_cons. cbn [fold_right concat].
  rewrite IH, length_app. lia.
Qed.

Lemma piece_lens_nonneg : forall P, Forall (fun l => 0 <= l) (piece_lens P).
Proof.
  intros P. unfold piece_lens. apply Forall_forall. intros l Hl. apply in_map_iff in Hl as (b & <- & _). lia.
Qed.

Lemma dbl_pow : forall f i need, 0 <= i <= 10 -> 10 - i <= Z.of_nat f -> need <= 2 ^ 22 ->
  exists j, i <= j <= 10 /\ dbl f (4096 * 2 ^ i) need = 4096 * 2 ^ j /\ need <= 4096 * 2 ^ j.
Proof.
  induction f as [|f IH]; intros i need Hi Hf Hn.
  - assert (i = 10) by lia. subst i. exists 10. cbn [dbl]. split; [lia|]. split; [reflexivity | lia].
  - cbn [dbl]. destruct (Z.leb_spec need (4096 * 2 ^ i)) as [H|H].
    + exists i. split; [lia|]. split; [reflexivity | exact H].
    + assert (Hi10 : i < 10) by (destruct (Z.eq_dec i 10) as [->|Hne]; lia).
      replace (2 * (4096 * 2 ^ i)) with (4096 * 2 ^ (i + 1)) by (rewrite Z.pow_add_r by lia; ring).
      destruct (IH (i + 1) need ltac:(lia) ltac:(lia) Hn) as (j & Hj & E & Hle).
      exists j. split; [lia|]. split; [exact E | exact Hle].
Qed.

Lemma pow_mono_inv : forall i j, 0 <= i -> 0 <= j -> 4096 * 2 ^ i < 4096 * 2 ^ j -> i < j.
Proof.
  intros i j Hi Hj H. destruct (Z_lt_le_dec i j) as [L|L]; [exact L|].
  pose proof (Z.pow_le_mono_r 2 j i ltac:(lia) L). lia.
Qed.

Lemma newcap_pow : forall c need, (c = 0 \/ exists i, 0 <= i <= 10 /\ c = 4096 * 2 ^ i) -> need <= 2 ^ 22 ->
  exists j, 0 <= j <= 10 /\ newcap c need = 4096 * 2 ^ j /\ need <= 4096 * 2 ^ j.
Proof.
  intros c need Hc Hn. unfold newcap.
  destruct Hc as [->|(i & Hi & ->)].
  - cbn [Z.eqb]. destruct (dbl_pow 64 0 need ltac:(lia) ltac:(lia) Hn) as (j & Hj & E & Hle).
    exists j. split; [lia|]. split; [exact E | exact Hle].
  - assert (Hne : (4096 * 2 ^ i =? 0) = false).
    { apply Z.eqb_neq. pose proof (Z.pow_pos_nonneg 2 i ltac:(lia) ltac:(lia)). lia. }
    rewrite Hne. destruct (dbl_pow 64 i need Hi ltac:(lia) Hn) as (j & Hj & E & Hle).
    exists j. split; [lia|]. split; [exact E | exact Hle].
Qed.

Lemma grow_len : forall ls x c (mu : nat), Forall (fun l => 0 <= l) ls -> 0 <= x ->
  x + fold_right Z.add 0 ls + 1 <= 2 ^ 22 ->
  (c = 0 /\ mu = 11%nat \/ exists i, 0 <= i <= 10 /\ c = 4096 * 2 ^ i /\ mu = Z.to_nat (10 - i)) ->
  (length (grow_calls x c ls) <= mu)%nat /\
  (grow_calls x c ls = [] /\ grow_cap x c ls = c \/ exists j, 0 <= j <= 10 /\ grow_cap x c ls = 4096 * 2 ^ j).
Proof.
  induction ls as [|l ls IH]; intros x c mu HF Hx Hs Hc.
  - cbn [grow_calls grow_cap length]. split; [lia | left; split; reflexivity].
  - inversion HF as [|? ? Hl HF']; subst. cbn [fold_right] in Hs.
    assert (Hs' : 0 <= fold_right Z.add 0 ls) by (clear -HF'; induction HF' as [|y ys Hy _ IHy]; cbn [fold_right]; lia).
    rewrite grow_calls_cons, grow_cap_cons.
    destruct (Z.ltb_spec c (x + l + 1)) as [Hg|Hg].
    + assert (Hc' : c = 0 \/ exists i, 0 <= i <= 10 /\ c = 4096 * 2 ^ i).
      { destruct Hc as [(-> & _)|(i & Hi & -> & _)]; [left; reflexivity | right; exists i; split; [lia | reflexivity]]. }
      destruct (newcap_pow c (x + l + 1) Hc' ltac:(lia)) as (j & Hj & E & Hle).
      rewrite E.
      destruct (IH (x + l) (4096 * 2 ^ j) (Z.to_nat (10 - j)) HF' ltac:(lia) ltac:(lia)
        ltac:(right; exists j; split; [lia | split; reflexivity])) as [IH1 IH2].
      split.
      * cbn [length]. destruct Hc as [(_ & ->)|(i & Hi & Ec & ->)]; [lia|].
        pose proof (pow_mono_inv i j ltac:(lia) ltac:(lia) ltac:(lia)). lia.
      * right. destruct IH2 as [(_ & ->)|(j' & Hj' & ->)]; [exists j; split; [lia | reflexivity]|].
        exists j'. split; [lia | reflexivity].
    + exact (IH (x + l) c mu HF' ltac:(lia) ltac:(lia) Hc).
Qed.

Lemma wr_result : forall P cnt, P <> [] -> 0 <= cnt -> cnt < 2 ^ 63 -> Z.of_nat (length (concat P)) + 1 <= 2 ^ 22 ->
  w_failed (putN (w0 cnt (2 ^ 64 - 1)) P) = 0 /\ w_fail (putN (w0 cnt (2 ^ 64 - 1)) P) = 2 ^ 64 - 1 /\
  cnt <= w_cnt (putN (w0 cnt (2 ^ 64 - 1)) P) <= cnt + 11 /\
  Z.of_nat (length (concat P)) < w_cap (putN (w0 cnt (2 ^ 64 - 1)) P) /\
  w_cap (putN (w0 cnt (2 ^ 64 - 1)) P) <= 2 ^ 22 /\ w_cap (putN (w0 cnt (2 ^ 64 - 1)) P) mod 4096 = 0.
Proof.
  intros P cnt HP H0 H63 HL.
  destruct (grow_len (piece_lens P) 0 0 11 (piece_lens_nonneg P) ltac:(lia) ltac:(rewrite sum_piece_lens; lia)
    ltac:(left; split; reflexivity)) as [G1 G2].
  pose proof (putN_cap_pow P (w0 cnt (2 ^ 64 - 1)) ltac:(left; reflexivity) ltac:(constructor)
    ltac:(cbn [w_text w0 length Z.of_nat]; lia)) as [WC _].
  assert (E : putN (w0 cnt (2 ^ 64 - 1)) P =
    mkW 0 ([] ++ concat P) (grow_cap 0 0 (piece_lens P)) (cnt + Z.of_nat (length (grow_calls 0 0 (piece_lens P))))
      (2 ^ 64 - 1) ([] ++ grow_calls 0 0 (piece_lens P))).
  { unfold w0. apply (putN_ok P (mkW 0 [] 0 cnt (2 ^ 64 - 1) [])); cbn [w_failed w_cnt w_text w_cap w_fail];
      [reflexivity | lia | | right]; change (Z.of_nat (length (@nil Z))) with 0; lia. }
  rewrite E in WC |- *. unfold wcap_ok in WC. cbn [w_failed w_text w_fail w_cnt w_cap app] in *.
  destruct G2 as [(Hn & _)|(j & Hj & Ec)]; [exact (False_rect _ (grow_calls_nonempty P HP Hn))|].
  rewrite Ec in *.
  destruct WC as [WC|(_ & WC)]; [pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) ltac:(lia)); lia|].
  split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact WC|].
  split; [pose proof (Z.pow_le_mono_r 2 j 10 ltac:(lia) ltac:(lia)); lia|].
  rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.

Section W.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GF : globals_free B API [(G_FAIL, 8); (G_LIVE, 24)].
Hypothesis AX : lib.U.Reusable.YL01.AllocExtra B MR.
Hypothesis CO : ctx_owned B API.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Hypothesis PRE : call_pre_k B MR CRT_STK L A regs mem md.
Variables (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound).
Hypothesis LG0 : ledger B L A mem Lam peak cnt (2 ^ 64 - 1).

Lemma LG0_blk : forall a k, In (a, k) Lam -> In (a - 16, k + 16) (blocks L A).
Proof.
  intros a k Hin. pose proof LG0 as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
  exact (proj1 (proj2 (LF _ Hin))).
Qed.

Definition bat (X P : list (Z * Z)) : sbound :=
  SB (sb_live bnd + Z.of_nat (length X) + Z.of_nat (length P))
     (sb_bytes bnd + lsum X + 16 * Z.of_nat (length X) + lsum P) (sb_cap bnd).

Definition CR (X P : list (Z * Z)) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
    (Lamc : list (Z * Z)) (peakc cntc : Z) (Nc : nat) : Prop :=
  GI B API L A regs mem md Lc Ac memc mdc /\
  NBok L A Lc Ac (P ++ map xblk X) /\
  ledger B Lc Ac memc Lamc peakc cntc (2 ^ 64 - 1) /\ peak <= peakc /\ cnt <= cntc /\
  Permutation Lamc (X ++ Lam) /\
  res_ok_slots Ac (bat X P) /\ hs_cap (bat X P) Nc CRT_SIZE.

Lemma crt_pre : forall Lc Ac memc mdc regsc K, GI B API L A regs mem md Lc Ac memc mdc ->
  getr regsc 2 = Z_to_bv 64 (spZ regs - 352) -> getr regsc 4 = getr regs 4 -> lib.Reusable.YK0s.ret_ok (getr regsc 1) ->
  0 <= K -> K + 352 <= CRT_STK ->
  spZ regsc = spZ regs - 352 /\ call_pre_k B MR K Lc Ac regsc memc mdc.
Proof.
  intros Lc Ac memc mdc regsc K (MID & _ & _ & INIT & _) R2 R4 R1 HK HK2.
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & _).
  pose proof MID as (HMc & HWFc & HBDc & _ & _ & _ & _ & _ & S).
  pose proof alloc_ceiling_val as Hacv.
  unfold CRT_STK, ALLOC_STACK in *.
  assert (SP : spZ regsc = spZ regs - 352).
  { unfold spZ at 1. rewrite R2, MState.unsigned_lit by lia. reflexivity. }
  split; [exact SP|].
  split; [exact HMc|]. split; [exact HWFc|]. split; [exact HBDc|]. split; [exact R1|].
  split; [rewrite SP; Z.div_mod_to_equations; lia|].
  split; [rewrite SP; lia|]. split; [rewrite SP; lia|].
  split; [intros a Ha; apply S; left; rewrite SP in Ha; lia|].
  split; [rewrite R4; exact HTP|].
  split; [intros a Ha; apply S; right; exact Ha|].
  intros Hf. rewrite INIT in Hf. discriminate.
Qed.

Lemma crt_entry_pos : forall p n, In (p, n) (blocks L A) -> 4096 <= p.
Proof.
  intros p n Hin. pose proof PRE as (HM & _).
  destruct (HsKindB.in_blocks L A p n Hin) as (q & Hq & ->).
  exact (proj1 (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q n HM Hq)).
Qed.

Lemma cr_mk : forall X P Lc Ac memc mdc Lamc peakc cntc Nc X' P' Lc' Ac' memc' mdc' Lamc' peakc' cntc' Nc' K E G,
  CR X P Lc Ac memc mdc Lamc peakc cntc Nc ->
  cs B API (spZ regs - 352) K E G Lc Ac memc mdc Lc' Ac' memc' mdc' ->
  ro_agree rsegs memc' -> guard_kept B memc memc' -> 0 <= K -> K + 352 <= CRT_STK ->
  (forall p n, In (p, n) (blocks L A) -> ~ G p n) ->
  (forall x, E x -> alloc_statics x \/ (spZ regs - 352 <= x < spZ regs - 104 /\ mbyte rsegs memc' x <> None) \/
     (exists y, In y (P ++ map xblk X) /\ fst y <= x < fst y + snd y) \/
     (exists y, In y (blocks Lc' Ac') /\ ~ In y (blocks Lc Ac) /\ fst y <= x < fst y + snd y)) ->
  (forall x, spZ regs - 352 <= x < spZ regs - 104 -> E x \/ ~ E x) ->
  ledger B Lc' Ac' memc' Lamc' peakc' cntc' (2 ^ 64 - 1) -> peakc <= peakc' -> cntc <= cntc' ->
  Permutation Lamc' (X' ++ Lam) -> NBok L A Lc' Ac' (P' ++ map xblk X') ->
  res_ok_slots Ac' (bat X' P') -> hs_cap (bat X' P') Nc' CRT_SIZE ->
  CR X' P' Lc' Ac' memc' mdc' Lamc' peakc' cntc' Nc'.
Proof.
  intros X P Lc Ac memc mdc Lamc peakc cntc Nc X' P' Lc' Ac' memc' mdc' Lamc' peakc' cntc' Nc' K E G
    (GIc & NBc & LGc & PKc & CNc & PMc & RSc & HCc) CS RA' GK' HK HK2 HG HE HDE LG' PK' CN' PM' NB' RS' HC'.
  pose proof crt_sp B API L A regs mem md PRE as (Hsp1 & Hsp2 & _).
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hacl.
  pose proof GIc as ((HMc & _) & _).
  pose proof CS as (HM' & _).
  split; [|split; [exact NB'|split; [exact LG'|split; [lia|split; [lia|split; [exact PM'|split; [exact RS' | exact HC']]]]]]].
  apply (gi_call B API SEG ERR AX CO L A regs mem md PRE Lc Ac memc mdc K E G Lc' Ac' memc' mdc' GIc CS RA' GK' HK HK2 HG).
  - intros p n x Hp Hx Hex. destruct (HE x Hex) as [Hs|[(Hf & _)|[(y & Hy & Hyx)|(y & Hy & Hny & Hyx)]]].
    + pose proof (crt_GS2 B API GF x Hs) as (_ & _ & _ & HGS).
      exact (proj2 (HGS _ _ _ _ HMc) p n (gi_entry_blk B API L A regs mem md PRE Lc Ac memc mdc p n GIc Hp) Hx).
    + pose proof (crt_blk B API GF AX Lc Ac memc mdc p n (x - p) HMc
        (gi_entry_blk B API L A regs mem md PRE Lc Ac memc mdc p n GIc Hp) ltac:(lia)) as (R & _).
      unfold CRT_STK, ALLOC_STACK in *. lia.
    + exact (nb_entry B API L A regs mem md PRE Lc Ac memc mdc _ y p n x GIc NBc Hy Hp Hyx Hx).
    + destruct (cs_blk B API SEG _ _ _ _ _ _ _ _ _ _ _ _ p n CS
        (gi_entry_blk B API L A regs mem md PRE Lc Ac memc mdc p n GIc Hp) (HG p n Hp)) as [Hp' _].
      destruct y as [a k]. cbn [fst snd] in Hyx.
      apply (crt_blk_disj B API Lc' Ac' memc' mdc' a k p n x HM' Hy Hp'); [|exact Hyx|exact Hx].
      intros Eq. apply Hny. rewrite Eq. exact (gi_entry_blk B API L A regs mem md PRE Lc Ac memc mdc p n GIc Hp).
  - intros x Hx Hw Hex. destruct (HE x Hex) as [Hs|[(Hf & _)|[(y & Hy & Hyx)|(y & Hy & Hny & Hyx)]]].
    + exact Hs.
    + exfalso. apply Hw. unfold CRT_STK, ALLOC_STACK. lia.
    + exfalso. destruct NBc as (INC & _).
      destruct y as [a k]. cbn [fst snd] in Hyx.
      destruct (crt_blk B API GF AX Lc Ac memc mdc a k (x - a) HMc (INC _ Hy) ltac:(lia)) as (R & NI & _).
      replace (a + (x - a)) with x in * by lia. destruct Hx as [Hx|Hx]; [lia | exact (NI Hx)].
    + exfalso. destruct y as [a k]. cbn [fst snd] in Hyx.
      destruct (crt_blk B API GF AX Lc' Ac' memc' mdc' a k (x - a) HM' Hy ltac:(lia)) as (R & NI & _).
      replace (a + (x - a)) with x in * by lia. destruct Hx as [Hx|Hx]; [lia | exact (NI Hx)].
  - intros x Hx Hw Hex. destruct (HE x Hex) as [Hs|[(Hf & Hn)|[(y & Hy & Hyx)|(y & Hy & Hny & Hyx)]]].
    + exfalso. destruct (crt_GS2 B API GF x Hs) as (_ & Hr & _). unfold CRT_STK, ALLOC_STACK in Hx. lia.
    + split; [exact Hf | exact Hn].
    + exfalso. destruct NBc as (INC & _).
      destruct y as [a k]. cbn [fst snd] in Hyx.
      destruct (crt_blk B API GF AX Lc Ac memc mdc a k (x - a) HMc (INC _ Hy) ltac:(lia)) as (R & _).
      unfold CRT_STK, ALLOC_STACK in Hx. lia.
    + exfalso. destruct y as [a k]. cbn [fst snd] in Hyx.
      destruct (crt_blk B API GF AX Lc' Ac' memc' mdc' a k (x - a) HM' Hy ltac:(lia)) as (R & _).
      unfold CRT_STK, ALLOC_STACK in Hx. lia.
  - exact HDE.
Qed.

Lemma crt_notin_mid : forall (b1 b2 : list (Z * Z)) y, pairwise ranges_disjoint (b1 ++ y :: b2) -> 0 < snd y ->
  ~ In y (b1 ++ b2).
Proof.
  intros b1 b2 y DJ Hy Hin. destruct (past_nul.pn_pairwise_mid _ b1 y b2 y DJ Hin) as [D|D];
    unfold ranges_disjoint in D; lia.
Qed.

Lemma crt_in_rm : forall (b1 b2 : list (Z * Z)) x y, In y (b1 ++ x :: b2) -> y <> x -> In y (b1 ++ b2).
Proof.
  intros b1 b2 x y H Hne. apply in_app_or in H as [H|[H|H]]; apply in_or_app;
    [left; exact H | exfalso; exact (Hne (eq_sym H)) | right; exact H].
Qed.

Lemma nb_add : forall Lc Ac Lc' Ac' NB y b1 b2,
  NBok L A Lc Ac NB -> (forall z, In z (blocks L A) -> In z (blocks Lc Ac)) ->
  blocks Lc' Ac' = b1 ++ y :: b2 -> blocks Lc Ac = b1 ++ b2 -> pairwise ranges_disjoint (blocks Lc' Ac') ->
  0 < snd y -> NBok L A Lc' Ac' (y :: NB).
Proof.
  intros Lc Ac Lc' Ac' NB y b1 b2 (INC & ND & NE) HE B1 B2 DJ Hy.
  rewrite B1 in DJ. pose proof (crt_notin_mid b1 b2 y DJ Hy) as Hn.
  split; [|split].
  - intros z [<-|Hz]; rewrite B1; [apply in_or_app; right; left; reflexivity|].
    apply past_nul.pn_in_mid. rewrite <- B2. exact (INC z Hz).
  - apply NoDup_ListNoDup. constructor; [|apply NoDup_ListNoDup; exact ND].
    intros Hz. apply Hn. rewrite <- B2. exact (INC y Hz).
  - intros z [<-|Hz]; [intros Hz; apply Hn; rewrite <- B2; exact (HE _ Hz) | exact (NE z Hz)].
Qed.

Lemma nb_rem : forall Lc Ac Lc' Ac' N1 N2 y b1 b2,
  NBok L A Lc Ac (N1 ++ y :: N2) -> blocks Lc Ac = b1 ++ y :: b2 -> blocks Lc' Ac' = b1 ++ b2 ->
  NBok L A Lc' Ac' (N1 ++ N2).
Proof.
  intros Lc Ac Lc' Ac' N1 N2 y b1 b2 (INC & ND & NE) B1 B2.
  apply NoDup_ListNoDup in ND.
  pose proof (NoDup_remove_2 _ _ _ ND) as Hy.
  split; [|split].
  - intros z Hz. rewrite B2. apply (crt_in_rm b1 b2 y z); [rewrite <- B1; apply INC; apply past_nul.pn_in_mid; exact Hz|].
    intros ->. exact (Hy Hz).
  - apply NoDup_ListNoDup. exact (NoDup_remove_1 _ _ _ ND).
  - intros z Hz. apply NE. apply past_nul.pn_in_mid. exact Hz.
Qed.

Lemma nb_perm : forall Lc Ac N N', NBok L A Lc Ac N -> Permutation N N' -> NBok L A Lc Ac N'.
Proof.
  intros Lc Ac N N' (INC & ND & NE) HP.
  split; [intros z Hz; apply INC; exact (Permutation_in _ (Permutation_sym HP) Hz)|].
  split; [apply NoDup_ListNoDup; apply NoDup_ListNoDup in ND; exact (Permutation_NoDup HP ND)|].
  intros z Hz. apply NE. exact (Permutation_in _ (Permutation_sym HP) Hz).
Qed.

Lemma bat_perm : forall X X' P, Permutation X X' -> bat X P = bat X' P.
Proof.
  intros X X' P HP. unfold bat. rewrite (lsum_perm X X' HP), (Permutation_length HP). reflexivity.
Qed.

Lemma bat_pmalloc : forall X P w n, sb_malloc (bat X P) n = bat X ((w, n) :: P).
Proof. intros X P w n. unfold bat, sb_malloc. cbn [sb_live sb_bytes sb_cap lsum length]. f_equal; lia. Qed.

Lemma bat_pfree : forall X P1 P2 w n, sb_free (bat X (P1 ++ (w, n) :: P2)) n = bat X (P1 ++ P2).
Proof.
  intros X P1 P2 w n. unfold bat, sb_free. cbn [sb_live sb_bytes sb_cap].
  rewrite !lsum_app, !length_app. cbn [lsum length]. f_equal; lia.
Qed.

Lemma bat_xmalloc : forall X P a k, sb_malloc (bat X P) (k + 16) = bat ((a, k) :: X) P.
Proof. intros X P a k. unfold bat, sb_malloc. cbn [sb_live sb_bytes sb_cap lsum length]. f_equal; lia. Qed.

Lemma bat_xfree : forall X1 X2 P a k, sb_free (bat (X1 ++ (a, k) :: X2) P) (k + 16) = bat (X1 ++ X2) P.
Proof.
  intros X1 X2 P a k. unfold bat, sb_free. cbn [sb_live sb_bytes sb_cap].
  rewrite !lsum_app, !length_app. cbn [lsum length]. f_equal; lia.
Qed.

Lemma crt_fst_uniq : forall {X Y : Type} (l : list (X * Y)) x a c,
  List.NoDup (map fst l) -> In (x, a) l -> In (x, c) l -> a = c.
Proof.
  intros X Y l. induction l as [|[y e] l IH]; intros x a c ND Ha Hc; [destruct Ha|].
  cbn [map fst] in ND. apply NoDup_cons_iff in ND as [Hn ND].
  destruct Ha as [Ha|Ha]; destruct Hc as [Hc|Hc].
  - injection Ha as E1 E2. injection Hc as E3 E4. congruence.
  - injection Ha as E1 E2. subst. exfalso. apply Hn. apply (in_map fst) in Hc. exact Hc.
  - injection Hc as E1 E2. subst. exfalso. apply Hn. apply (in_map fst) in Ha. exact Ha.
  - exact (IH x a c ND Ha Hc).
Qed.

Lemma crt_ub_free : forall Lc Ac A' p n, WF Ac -> In (p, n) (user_blocks Ac) ->
  (forall q k, In (q, k) (user_blocks Ac) -> q <> p -> In (q, k) (user_blocks A')) ->
  ublocks_kept Lc Ac A' (ptr_addr Lc p, n).
Proof.
  intros Lc Ac A' p n HW Hp H q k Hq Hne. apply (H q k Hq). intros ->. apply Hne.
  pose proof (lib.Reusable.YO10.user_block_ptrs_NoDup Ac HW) as ND.
  rewrite (crt_fst_uniq _ p k n ND Hq Hp). reflexivity.
Qed.

Lemma crt_lam_blk : forall Lc Ac memc Lamc pk c f a k, ledger B Lc Ac memc Lamc pk c f -> In (a, k) Lamc ->
  In (a - 16, k + 16) (blocks Lc Ac) /\ 0 <= k /\ (forall i, 0 <= i < k + 16 -> ~ in_img B (a - 16 + i)).
Proof.
  intros Lc Ac memc Lamc pk c f a k (_ & _ & _ & _ & _ & LF) Hin. rewrite Forall_forall in LF.
  destruct (LF _ Hin) as (Hk & Hb & _ & Hi). split; [exact Hb|]. split; [exact Hk | exact Hi].
Qed.

Lemma cr_entry_sub : forall X P Lc Ac memc mdc Lamc peakc cntc Nc, CR X P Lc Ac memc mdc Lamc peakc cntc Nc ->
  forall z, In z (blocks L A) -> In z (blocks Lc Ac).
Proof.
  intros X P Lc Ac memc mdc Lamc peakc cntc Nc (GIc & _) [p n] Hz.
  exact (gi_entry_blk B API L A regs mem md PRE Lc Ac memc mdc p n GIc Hz).
Qed.

Lemma cr_ledger_G0 : forall Lc Ac memc mdc Lamc pk c f, MR Lc Ac memc mdc -> ledger B Lc Ac memc Lamc pk c f ->
  forall a k, In (a, k) Lamc -> (a - 16, k + 16) <> (0, 0).
Proof.
  intros Lc Ac memc mdc Lamc pk c f HM LG a k Hin E. injection E as E1 _.
  pose proof (ledger_block_range B API Lc Ac memc mdc Lamc pk c f a k HM LG Hin). lia.
Qed.

Lemma w_malloc : malloc_contract B API -> ms_malloc B = 0x16c7c ->
  forall X P Lc Ac regsc memc mdc Lamc peakc cntc Nc n (Q : config -> Prop),
  CR X P Lc Ac memc mdc Lamc peakc cntc (Datatypes.S Nc) ->
  getr regsc 2 = Z_to_bv 64 (spZ regs - 352) -> getr regsc 4 = getr regs 4 -> lib.Reusable.YK0s.ret_ok (getr regsc 1) ->
  getr regsc 10 = Z_to_bv 64 n -> 0 < n <= CRT_SIZE ->
  (forall Lc' Ac' regs' memc' mdc' w,
     regs_preserved regsc regs' -> getr regs' 10 = Z_to_bv 64 w -> 4096 <= w -> w + n <= alloc_ceiling ->
     w mod 16 = 0 -> In (w, n) (blocks Lc' Ac') ->
     CR X ((w, n) :: P) Lc' Ac' memc' mdc' Lamc peakc cntc Nc ->
     cs B API (spZ regs - 352) ALLOC_STACK (fun _ => False) (fun a k => (a, k) = (0, 0))
       Lc Ac memc mdc Lc' Ac' memc' mdc' ->
     SR (ms_segs B) (mkCfg (mkst regs' (getr regsc 1) memc' (seg_rom (ms_segs B))) mdc') Q) ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 0x16c7c) memc (seg_rom (ms_segs B))) mdc) Q.
Proof.
  intros MALLOC MAL X P Lc Ac regsc memc mdc Lamc peakc cntc Nc n Q CRc R2 R4 R1 R10 Hn K.
  pose proof CRc as (GIc & NBc & LGc & PKc & CNc & PMc & RSc & HCc).
  pose proof GIc as ((HMc & _) & _ & _ & _ & RAc & _).
  pose proof crt_sp B API L A regs mem md PRE as (Hsp1 & Hsp2 & _).
  pose proof alloc_ceiling_val as Hacv.
  destruct (crt_pre Lc Ac memc mdc regsc ALLOC_STACK GIc R2 R4 R1 ltac:(unfold ALLOC_STACK; lia)
    ltac:(unfold CRT_STK, ALLOC_STACK; lia)) as [SPc PREc].
  rewrite <- MAL.
  eapply SR_bind.
  { apply (MALLOC Lc Ac regsc memc mdc n (bat X P)).
    - apply (proj2 (call_pre_k_alloc B MR Lc Ac regsc memc mdc)). exact PREc.
    - rewrite SEG. exact RAc.
    - exact R10.
    - exact RSc.
    - apply (hs_cap_room (bat X P) Nc CRT_SIZE n); [unfold CRT_SIZE; lia | lia | exact HCc]. }
  intros c1 (L' & A' & regs' & mem' & md' & w & -> & CP & R10' & Hw0 & Hw16 & FB & (b1 & b2 & BL' & BL) &
    BKP & RA' & GK' & UB' & INIT' & LEN' & RES').
  pose proof FB as (FB1 & FB2 & FB3).
  destruct (cs_of_post B API AX CO ALLOC_STACK Lc Ac regsc memc mdc (fun _ => False) L' A' regs' mem' md' (0, 0)
    HMc CP LEN' (fun _ => INIT') (fun q k Hq _ => UB' q k Hq)) as [CS RP].
  rewrite SPc in CS.
  pose proof CS as (HM' & _).
  assert (HW : In (w, n) (blocks L' A')) by (rewrite BL'; apply in_or_app; right; left; reflexivity).
  apply (K L' A' regs' mem' md' w RP R10' FB1 FB2 Hw16 HW); [|exact CS].
  apply (cr_mk X P Lc Ac memc mdc Lamc peakc cntc (Datatypes.S Nc) X ((w, n) :: P) L' A' mem' md' Lamc peakc cntc Nc
    ALLOC_STACK (fun _ => False) (fun a k => (a, k) = (0, 0)) CRc CS).
  - rewrite <- SEG. exact RA'.
  - exact GK'.
  - unfold ALLOC_STACK. lia.
  - unfold CRT_STK, ALLOC_STACK. lia.
  - intros p k Hp E. injection E as -> _. pose proof (crt_entry_pos 0 k Hp). lia.
  - intros x [].
  - intros x _. right. intros [].
  - apply (cs_ledger B API SEG GF _ _ _ _ _ _ _ _ _ _ _ _ Lamc peakc cntc (2 ^ 64 - 1) CS HMc
      ltac:(unfold ALLOC_STACK; lia) LGc).
    + intros x _ [].
    + intros a k Hin. split; [exact (cr_ledger_G0 Lc Ac memc mdc Lamc peakc cntc _ HMc LGc a k Hin)|].
      intros x _ [].
  - lia.
  - lia.
  - exact PMc.
  - apply (nb_add Lc Ac L' A' (P ++ map xblk X) (w, n) b1 b2 NBc (cr_entry_sub X P Lc Ac memc mdc Lamc peakc cntc _ CRc)
      BL' BL (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM') ltac:(cbn [snd]; lia)).
  - rewrite <- (bat_pmalloc X P w n). exact RES'.
  - rewrite <- (bat_pmalloc X P w n). apply (hs_cap_malloc (bat X P) Nc CRT_SIZE n); [lia | exact HCc].
Qed.

Lemma w_free : free_contract B API -> ms_free B = 0x16b3c ->
  forall X P1 P2 Lc Ac regsc memc mdc Lamc peakc cntc Nc w n (Q : config -> Prop),
  CR X (P1 ++ (w, n) :: P2) Lc Ac memc mdc Lamc peakc cntc Nc ->
  getr regsc 2 = Z_to_bv 64 (spZ regs - 352) -> getr regsc 4 = getr regs 4 -> lib.Reusable.YK0s.ret_ok (getr regsc 1) ->
  getr regsc 10 = Z_to_bv 64 w -> 0 < n ->
  (forall Lc' Ac' regs' memc' mdc',
     regs_preserved regsc regs' ->
     CR X (P1 ++ P2) Lc' Ac' memc' mdc' Lamc peakc cntc Nc ->
     cs B API (spZ regs - 352) ALLOC_STACK (fun a => w <= a < w + n) (fun a k => (a, k) = (w, n))
       Lc Ac memc mdc Lc' Ac' memc' mdc' ->
     SR (ms_segs B) (mkCfg (mkst regs' (getr regsc 1) memc' (seg_rom (ms_segs B))) mdc') Q) ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 0x16b3c) memc (seg_rom (ms_segs B))) mdc) Q.
Proof.
  intros FREE FRE X P1 P2 Lc Ac regsc memc mdc Lamc peakc cntc Nc w n Q CRc R2 R4 R1 R10 Hn K.
  pose proof CRc as (GIc & NBc & LGc & PKc & CNc & PMc & RSc & HCc).
  pose proof GIc as ((HMc & HWFc & _) & _ & _ & _ & RAc & _).
  pose proof crt_sp B API L A regs mem md PRE as (Hsp1 & Hsp2 & _).
  pose proof alloc_ceiling_val as Hacv.
  destruct (crt_pre Lc Ac memc mdc regsc ALLOC_STACK GIc R2 R4 R1 ltac:(unfold ALLOC_STACK; lia)
    ltac:(unfold CRT_STK, ALLOC_STACK; lia)) as [SPc PREc].
  pose proof NBc as (INC & ND & NE).
  assert (Hwb : In (w, n) (blocks Lc Ac)) by (apply INC; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
  destruct (HsKindB.in_blocks Lc Ac w n Hwb) as (p & Hp & Ew).
  rewrite <- FRE.
  eapply SR_bind.
  { apply (FREE Lc Ac regsc memc mdc p n (bat X (P1 ++ (w, n) :: P2))).
    - apply (proj2 (call_pre_k_alloc B MR Lc Ac regsc memc mdc)). exact PREc.
    - rewrite SEG. exact RAc.
    - exact Hp.
    - rewrite R10, Ew. reflexivity.
    - exact RSc. }
  intros c1 (L' & A' & regs' & mem' & md' & -> & CP & (b1 & b2 & BL & BL') & BKP & RA' & GK' & UB' & INIT' & LEN' &
    RES').
  apply call_post_k_alloc in CP.
  rewrite <- Ew in CP, BL.
  pose proof (crt_ub_free Lc Ac A' p n HWFc Hp UB') as UBg. rewrite <- Ew in UBg.
  destruct (cs_of_post B API AX CO ALLOC_STACK Lc Ac regsc memc mdc _ L' A' regs' mem' md' (w, n)
    HMc CP LEN' INIT' UBg) as [CS RP].
  rewrite SPc in CS.
  pose proof CS as (HM' & _).
  apply (K L' A' regs' mem' md' RP); [|exact CS].
  apply (cr_mk X (P1 ++ (w, n) :: P2) Lc Ac memc mdc Lamc peakc cntc Nc X (P1 ++ P2) L' A' mem' md' Lamc peakc cntc Nc
    ALLOC_STACK _ _ CRc CS).
  - rewrite <- SEG. exact RA'.
  - exact GK'.
  - unfold ALLOC_STACK. lia.
  - unfold CRT_STK, ALLOC_STACK. lia.
  - intros q k Hq E. injection E as -> ->. apply (NE (w, n)); [|exact Hq].
    apply in_or_app; left; apply in_or_app; right; left; reflexivity.
  - intros x Hx. right. right. left. exists (w, n). split; [|cbn [fst snd]; lia].
    apply in_or_app; left; apply in_or_app; right; left; reflexivity.
  - intros x Hx. right. intros Hx'.
    destruct (crt_blk B API GF AX Lc Ac memc mdc w n (x - w) HMc Hwb ltac:(lia)) as (R & _).
    unfold CRT_STK, ALLOC_STACK in *. lia.
  - apply (cs_ledger B API SEG GF _ _ _ _ _ _ _ _ _ _ _ _ Lamc peakc cntc (2 ^ 64 - 1) CS HMc
      ltac:(unfold ALLOC_STACK; lia) LGc).
    + intros x Hs Hx. destruct (crt_GS2 B API GF x Hs) as (_ & _ & _ & HGS).
      exact (proj2 (HGS _ _ _ _ HMc) w n Hwb Hx).
    + intros a k Hin. destruct (crt_lam_blk Lc Ac memc Lamc peakc cntc _ a k LGc Hin) as (Hb & Hk & _).
      assert (Hne : (a - 16, k + 16) <> (w, n)).
      { intros E. apply NoDup_ListNoDup in ND.
        pose proof (Permutation_in _ PMc Hin) as HX. apply in_app_or in HX as [HX|HX].
        - assert (H1 : In (a - 16, k + 16) (map xblk X)) by (apply (in_map xblk) in HX; exact HX).
          rewrite E in H1. rewrite <- app_assoc in ND. cbn [app] in ND.
          apply NoDup_remove_2 in ND. apply ND. apply in_or_app. right. apply in_or_app. right. exact H1.
        - apply (NE (w, n)); [apply in_or_app; left; apply in_or_app; right; left; reflexivity|].
          rewrite <- E. exact (LG0_blk a k HX). }
      split; [exact Hne|].
      intros x Hx Hx'. exact (crt_blk_disj B API Lc Ac memc mdc (a - 16) (k + 16) w n x HMc Hb Hwb Hne ltac:(lia) Hx').
  - lia.
  - lia.
  - exact PMc.
  - rewrite <- app_assoc. rewrite <- app_assoc in NBc. cbn [app] in NBc.
    exact (nb_rem Lc Ac L' A' P1 (P2 ++ map xblk X) (w, n) b1 b2 NBc BL BL').
  - rewrite <- (bat_pfree X P1 P2 w n). exact RES'.
  - rewrite <- (bat_pfree X P1 P2 w n). apply hs_cap_free; [lia | exact HCc].
Qed.

Lemma cr_in_lam : forall X P Lc Ac memc mdc Lamc peakc cntc Nc a k,
  CR X P Lc Ac memc mdc Lamc peakc cntc Nc -> In (a, k) X -> In (a, k) Lamc.
Proof.
  intros X P Lc Ac memc mdc Lamc peakc cntc Nc a k (_ & _ & _ & _ & _ & PMc & _) Hin.
  apply (Permutation_in _ (Permutation_sym PMc)). apply in_or_app. left. exact Hin.
Qed.

Lemma w_ffree : fuzz_free_contract B API sb_form ->
  forall X1 X2 P Lc Ac regsc memc mdc Lamc peakc cntc Nc p k (Q : config -> Prop),
  CR (X1 ++ (p, k) :: X2) P Lc Ac memc mdc Lamc peakc cntc Nc ->
  getr regsc 2 = Z_to_bv 64 (spZ regs - 352) -> getr regsc 4 = getr regs 4 -> lib.Reusable.YK0s.ret_ok (getr regsc 1) ->
  getr regsc 10 = Z_to_bv 64 p ->
  (forall Lc' Ac' regs' memc' mdc' Lamc',
     regs_preserved regsc regs' ->
     CR (X1 ++ X2) P Lc' Ac' memc' mdc' Lamc' peakc cntc Nc ->
     cs B API (spZ regs - 352) ALLOC_STACK (free_writes p k) (fun a n => (a, n) = (p - 16, k + 16))
       Lc Ac memc mdc Lc' Ac' memc' mdc' ->
     SR (ms_segs B) (mkCfg (mkst regs' (getr regsc 1) memc' (seg_rom (ms_segs B))) mdc') Q) ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 FUZZ_FREE) memc (seg_rom (ms_segs B))) mdc) Q.
Proof.
  intros FF X1 X2 P Lc Ac regsc memc mdc Lamc peakc cntc Nc p k Q CRc R2 R4 R1 R10 K.
  pose proof CRc as (GIc & NBc & LGc & PKc & CNc & PMc & RSc & HCc).
  pose proof GIc as ((HMc & _) & _ & _ & _ & RAc & _).
  pose proof crt_sp B API L A regs mem md PRE as (Hsp1 & Hsp2 & _).
  pose proof alloc_ceiling_val as Hacv.
  destruct (crt_pre Lc Ac memc mdc regsc ALLOC_STACK GIc R2 R4 R1 ltac:(unfold ALLOC_STACK; lia)
    ltac:(unfold CRT_STK, ALLOC_STACK; lia)) as [SPc PREc].
  assert (Hin : In (p, k) Lamc) by (apply (cr_in_lam _ _ _ _ _ _ _ _ _ _ p k CRc); apply in_or_app; right; left; reflexivity).
  pose proof (ledger_block_range B API Lc Ac memc mdc Lamc peakc cntc _ p k HMc LGc Hin) as (Rp1 & Rp2 & _).
  pose proof NBc as (INC & ND & NE).
  assert (HyN : In (p - 16, k + 16) (P ++ map xblk (X1 ++ (p, k) :: X2))).
  { apply in_or_app. right. rewrite map_app. apply in_or_app. right. left. reflexivity. }
  eapply SR_bind.
  { apply (FF Lc Ac regsc memc mdc p k (bat (X1 ++ (p, k) :: X2) P) Lamc peakc cntc (2 ^ 64 - 1) PREc R10 LGc).
    - rewrite SEG. exact RAc.
    - right. exact Hin.
    - exact RSc. }
  intros c1 (L' & A' & regs' & mem' & md' & -> & RA' & GK' & INIT' & _ & CP & LEN' & KP & UB & BR).
  destruct BR as [(Hp0 & _) | (_ & (b1 & b2 & BL & BL') & (l1 & l2 & EL & LG') & RES')]; [lia|].
  destruct (cs_of_post B API AX CO ALLOC_STACK Lc Ac regsc memc mdc _ L' A' regs' mem' md' (p - 16, k + 16)
    HMc CP LEN' INIT' UB) as [CS RP].
  rewrite SPc in CS.
  apply (K L' A' regs' mem' md' (l1 ++ l2) RP); [|exact CS].
  apply (cr_mk (X1 ++ (p, k) :: X2) P Lc Ac memc mdc Lamc peakc cntc Nc (X1 ++ X2) P L' A' mem' md' (l1 ++ l2)
    peakc cntc Nc ALLOC_STACK _ _ CRc CS).
  - rewrite <- SEG. exact RA'.
  - exact GK'.
  - unfold ALLOC_STACK. lia.
  - unfold CRT_STK, ALLOC_STACK. lia.
  - intros q n Hq E. injection E as -> ->. exact (NE _ HyN Hq).
  - intros x [Hx|(_ & Hx)]; [left; left; exact Hx|]. right. right. left.
    exists (p - 16, k + 16). split; [exact HyN | cbn [fst snd]; lia].
  - intros x Hx. right. unfold free_writes, G_LIVE. intros [Hx'|(_ & Hx')]; unfold CRT_STK, ALLOC_STACK in *; lia.
  - exact LG'.
  - lia.
  - lia.
  - rewrite EL in PMc. rewrite <- app_assoc in PMc. cbn [app] in PMc. rewrite <- app_assoc.
    exact (Permutation_app_inv _ _ _ _ _ PMc).
  - rewrite map_app in NBc |- *. cbn [map] in NBc. rewrite app_assoc in NBc |- *.
    exact (nb_rem Lc Ac L' A' (P ++ map xblk X1) (map xblk X2) (p - 16, k + 16) b1 b2 NBc BL BL').
  - rewrite <- (bat_xfree X1 X2 P p k). exact RES'.
  - pose proof (crt_lam_blk Lc Ac memc Lamc peakc cntc _ p k LGc Hin) as (_ & Hk0 & _).
    rewrite <- (bat_xfree X1 X2 P p k). apply hs_cap_free; [lia | exact HCc].
Qed.

Lemma w_enc : preset_base64_encode_contract B API sb_form ->
  forall X P Lc Ac regsc memc mdc Lamc peakc cntc Nc data len bs (Q : config -> Prop),
  CR X P Lc Ac memc mdc Lamc peakc cntc (Datatypes.S Nc) ->
  getr regsc 2 = Z_to_bv 64 (spZ regs - 352) -> getr regsc 4 = getr regs 4 -> lib.Reusable.YK0s.ret_ok (getr regsc 1) ->
  getr regsc 10 = Z_to_bv 64 data -> getr regsc 11 = Z_to_bv 64 len ->
  0 <= data < 2 ^ 64 -> data + len <= 2 ^ 64 ->
  bytes_ok bs -> Z.of_nat (length bs) = len -> len <= 2 ^ 27 ->
  (forall i, 0 <= i < len -> mbyte (ms_segs B) memc (data + i) = Some (Z_to_bv 8 (nth (Z.to_nat i) bs 0))) ->
  enc_data_where B Lc Ac regsc data len -> cntc < 2 ^ 63 -> enc_size len + 16 <= CRT_SIZE ->
  (forall Lc' Ac' regs' memc' mdc' q,
     regs_preserved regsc regs' -> getr regs' 10 = Z_to_bv 64 q -> q <> 0 -> q mod 16 = 0 ->
     In (q - 16, enc_size len + 16) (blocks Lc' Ac') ->
     CR ((q, enc_size len) :: X) P Lc' Ac' memc' mdc' ((q, enc_size len) :: Lamc)
       (Z.max peakc (lsum Lamc + enc_size len)) (cntc + 1) Nc ->
     cs B API (spZ regs - 352) ENC_STACK (enc_writes q (enc_size len)) (fun a n => (a, n) = (0, 0))
       Lc Ac memc mdc Lc' Ac' memc' mdc' ->
     (forall i, 0 <= i < enc_size len ->
        mbyte (ms_segs B) memc' (q + i) = nth_error (map (Z_to_bv 8) (b64_enc bs ++ [0])) (Z.to_nat i)) ->
     SR (ms_segs B) (mkCfg (mkst regs' (getr regsc 1) memc' (seg_rom (ms_segs B))) mdc') Q) ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PRESET_BASE64_ENCODE) memc (seg_rom (ms_segs B))) mdc) Q.
Proof.
  intros ENC X P Lc Ac regsc memc mdc Lamc peakc cntc Nc data len bs Q CRc R2 R4 R1 R10 R11 Hd Hdl Hbs HL Hl
    HB HW Hc Hsz K.
  pose proof CRc as (GIc & NBc & LGc & PKc & CNc & PMc & RSc & HCc).
  pose proof GIc as ((HMc & _) & _ & _ & _ & RAc & _).
  pose proof crt_sp B API L A regs mem md PRE as (Hsp1 & Hsp2 & _).
  pose proof alloc_ceiling_val as Hacv.
  destruct (crt_pre Lc Ac memc mdc regsc ENC_STACK GIc R2 R4 R1 ltac:(unfold ENC_STACK, ALLOC_STACK; lia)
    ltac:(unfold CRT_STK, ENC_STACK, ALLOC_STACK; lia)) as [SPc PREc].
  assert (Hn : 0 <= enc_size len) by (unfold enc_size; Z.div_mod_to_equations; lia).
  eapply SR_bind.
  { apply (ENC Lc Ac regsc memc mdc data len bs (bat X P) Lamc peakc cntc (2 ^ 64 - 1) SEG ERR
      ltac:(rewrite SEG; exact RAc) PREc R10 R11 Hd Hdl Hbs HL Hl HB HW LGc RSc).
    apply (hs_cap_room (bat X P) Nc CRT_SIZE); [unfold CRT_SIZE; lia | lia | exact HCc]. }
  intros c1 (L' & A' & regs' & mem' & md' & q & -> & RA' & GK' & INIT' & CP & LEN' & R10' & KP & UB & _ & BR).
  destruct BR as [(Hc0 & _) | (_ & Hq0 & Hq16 & RES' & NS & NI & NL & (b1 & b2 & BL' & BL) & LG' & TX)];
    [lia|].
  destruct (cs_of_post B API AX CO ENC_STACK Lc Ac regsc memc mdc _ L' A' regs' mem' md' (0, 0)
    HMc CP LEN' INIT' UB) as [CS RP].
  rewrite SPc in CS.
  pose proof CS as (HM' & _).
  assert (HQ : In (q - 16, enc_size len + 16) (blocks L' A')) by (rewrite BL'; apply in_or_app; right; left; reflexivity).
  assert (HQn : ~ In (q - 16, enc_size len + 16) (blocks Lc Ac)).
  { rewrite BL. pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM') as DJ. rewrite BL' in DJ.
    apply (crt_notin_mid b1 b2 _ DJ). cbn [snd]. lia. }
  pose proof LGc as (_ & _ & Hc00 & _). rewrite (Z.mod_small (cntc + 1) (2 ^ 64)) in LG' by lia.
  apply (K L' A' regs' mem' md' q RP R10' Hq0 Hq16 HQ); [| exact CS | exact TX].
  apply (cr_mk X P Lc Ac memc mdc Lamc peakc cntc (Datatypes.S Nc) ((q, enc_size len) :: X) P L' A' mem' md'
    ((q, enc_size len) :: Lamc) (Z.max peakc (lsum Lamc + enc_size len)) (cntc + 1) Nc ENC_STACK _ _ CRc CS).
  - rewrite <- SEG. exact RA'.
  - exact GK'.
  - unfold ENC_STACK, ALLOC_STACK. lia.
  - unfold CRT_STK, ENC_STACK, ALLOC_STACK. lia.
  - intros p k Hp E. injection E as -> _. pose proof (crt_entry_pos 0 k Hp). lia.
  - intros x Hx. unfold enc_writes, alloc_writes in Hx.
    destruct Hx as [[Hx|(_ & Hx)]|(_ & Hx)]; [left; exact Hx| |]; right; right; right;
      exists (q - 16, enc_size len + 16); (split; [exact HQ|]); (split; [exact HQn | cbn [fst snd]; lia]).
  - intros x Hx. right. intros Hex.
    assert (Hxb : q - 16 <= x < q - 16 + (enc_size len + 16)).
    { unfold enc_writes, alloc_writes in Hex. destruct Hex as [[Hs|(_ & Hs)]|(_ & Hs)]; [|lia|lia].
      exfalso. destruct (crt_GS2 B API GF x Hs) as (_ & Hr & _). unfold CRT_STK, ALLOC_STACK in *. lia. }
    destruct (crt_blk B API GF AX L' A' mem' md' (q - 16) (enc_size len + 16) (x - (q - 16)) HM' HQ ltac:(lia))
      as (R & _).
    unfold CRT_STK, ALLOC_STACK in *. lia.
  - exact LG'.
  - lia.
  - lia.
  - exact (perm_skip _ PMc).
  - apply (nb_perm L' A' ((q - 16, enc_size len + 16) :: P ++ map xblk X)).
    + exact (nb_add Lc Ac L' A' (P ++ map xblk X) _ b1 b2 NBc (cr_entry_sub X P Lc Ac memc mdc Lamc peakc cntc _ CRc)
        BL' BL (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM') ltac:(cbn [snd]; lia)).
    + cbn [map]. exact (Permutation_middle P (map xblk X) _).
  - rewrite <- (bat_xmalloc X P q (enc_size len)). exact RES'.
  - rewrite <- (bat_xmalloc X P q (enc_size len)). apply (hs_cap_malloc (bat X P) Nc CRT_SIZE); [lia | exact HCc].
Qed.

Lemma w_dec : preset_base64_decode_contract B API sb_form ->
  forall X P Lc Ac regsc memc mdc Lamc peakc cntc Nc text lenp tb slack bs (Q : config -> Prop),
  CR X P Lc Ac memc mdc Lamc peakc cntc (Datatypes.S Nc) ->
  getr regsc 2 = Z_to_bv 64 (spZ regs - 352) -> getr regsc 4 = getr regs 4 -> lib.Reusable.YK0s.ret_ok (getr regsc 1) ->
  getr regsc 10 = Z_to_bv 64 text -> getr regsc 11 = Z_to_bv 64 lenp ->
  no_zero tb -> bytes_ok tb -> Z.of_nat (length tb) <= 2 ^ 28 ->
  Mem.bytes_at (ms_segs B) memc text (map (Z_to_bv 8) (tb ++ [0]) ++ slack) ->
  (- (text + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length slack) ->
  dec_text_where B Lc Ac regsc Lamc text (Z.of_nat (length tb) + 1) ->
  spZ regs - 352 <= lenp -> lenp + 8 <= spZ regs - 104 -> lenp mod 8 = 0 ->
  lenp + 8 <= text \/ text + Z.of_nat (length tb) + 1 <= lenp ->
  b64_dec tb = Some bs -> cntc < 2 ^ 63 -> dec_size tb + 16 <= CRT_SIZE ->
  (forall Lc' Ac' regs' memc' mdc' q,
     regs_preserved regsc regs' -> getr regs' 10 = Z_to_bv 64 q -> q <> 0 -> q mod 16 = 0 ->
     In (q - 16, dec_size tb + 16) (blocks Lc' Ac') ->
     CR ((q, dec_size tb) :: X) P Lc' Ac' memc' mdc' ((q, dec_size tb) :: Lamc)
       (Z.max peakc (lsum Lamc + dec_size tb)) (cntc + 1) Nc ->
     cs B API (spZ regs - 352) DEC_STACK (dec_writes q (dec_size tb) lenp) (fun a n => (a, n) = (0, 0))
       Lc Ac memc mdc Lc' Ac' memc' mdc' ->
     Mem.bytes_at (ms_segs B) memc' q (map (Z_to_bv 8) bs) ->
     Mem.bytes_at (ms_segs B) memc' lenp (Mem.le8 (Z_to_bv 64 (Z.of_nat (length bs)))) ->
     SR (ms_segs B) (mkCfg (mkst regs' (getr regsc 1) memc' (seg_rom (ms_segs B))) mdc') Q) ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PRESET_BASE64_DECODE) memc (seg_rom (ms_segs B))) mdc) Q.
Proof.
  intros DEC X P Lc Ac regsc memc mdc Lamc peakc cntc Nc text lenp tb slack bs Q CRc R2 R4 R1 R10 R11 HNZ HBO HTL
    TB SL TW Hl1 Hl2 Hl3 Hl4 HD Hc Hsz K.
  pose proof CRc as (GIc & NBc & LGc & PKc & CNc & PMc & RSc & HCc).
  pose proof GIc as ((HMc & _ & _ & _ & _ & _ & _ & _ & WS) & _ & _ & _ & RAc & _).
  pose proof crt_sp B API L A regs mem md PRE as (Hsp1 & Hsp2 & _).
  pose proof alloc_ceiling_val as Hacv.
  destruct (crt_pre Lc Ac memc mdc regsc DEC_STACK GIc R2 R4 R1 ltac:(unfold DEC_STACK, ALLOC_STACK; lia)
    ltac:(unfold CRT_STK, DEC_STACK, ALLOC_STACK; lia)) as [SPc PREc].
  assert (Hn : 0 <= dec_size tb) by (unfold dec_size; Z.div_mod_to_equations; lia).
  eapply SR_bind.
  { apply (DEC Lc Ac regsc memc mdc text lenp tb slack (bat X P) Lamc peakc cntc (2 ^ 64 - 1) SEG ERR
      ltac:(rewrite SEG; exact RAc) PREc R10 R11 HNZ HBO HTL TB SL TW).
    - rewrite SPc. lia.
    - exact Hl3.
    - intros i Hi. apply WS. left. unfold CRT_STK, ALLOC_STACK. lia.
    - exact Hl4.
    - exact LGc.
    - exact RSc.
    - apply (hs_cap_room (bat X P) Nc CRT_SIZE); [unfold CRT_SIZE; lia | lia | exact HCc]. }
  intros c1 (L' & A' & regs' & mem' & md' & q & -> & RA' & GK' & INIT' & CP & LEN' & KP & _ & BR).
  destruct BR as [(Hc0 & _) | [(_ & HN & _) | (bs' & _ & HD' & Hq0 & R10' & Hq16 & NL & NS & NI &
    (b1 & b2 & BL' & BL) & UB & LG' & BQ & BN & RES')]]; [lia | congruence |].
  rewrite HD in HD'. injection HD' as <-.
  destruct (cs_of_post B API AX CO DEC_STACK Lc Ac regsc memc mdc _ L' A' regs' mem' md' (0, 0)
    HMc CP LEN' INIT' UB) as [CS RP].
  rewrite SPc in CS.
  pose proof CS as (HM' & _).
  assert (HQ : In (q - 16, dec_size tb + 16) (blocks L' A')) by (rewrite BL'; apply in_or_app; right; left; reflexivity).
  assert (HQn : ~ In (q - 16, dec_size tb + 16) (blocks Lc Ac)).
  { rewrite BL. pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM') as DJ. rewrite BL' in DJ.
    apply (crt_notin_mid b1 b2 _ DJ). cbn [snd]. lia. }
  pose proof LGc as (_ & _ & Hc00 & _). rewrite (Z.mod_small (cntc + 1) (2 ^ 64)) in LG' by lia.
  pose proof BN as (_ & BNl & BNb). rewrite length_le8 in BNl.
  apply (K L' A' regs' mem' md' q RP R10' Hq0 Hq16 HQ); [| exact CS | exact BQ | exact BN].
  apply (cr_mk X P Lc Ac memc mdc Lamc peakc cntc (Datatypes.S Nc) ((q, dec_size tb) :: X) P L' A' mem' md'
    ((q, dec_size tb) :: Lamc) (Z.max peakc (lsum Lamc + dec_size tb)) (cntc + 1) Nc DEC_STACK _ _ CRc CS).
  - rewrite <- SEG. exact RA'.
  - exact GK'.
  - unfold DEC_STACK, ALLOC_STACK. lia.
  - unfold CRT_STK, DEC_STACK, ALLOC_STACK. lia.
  - intros p k Hp E. injection E as -> _. pose proof (crt_entry_pos 0 k Hp). lia.
  - intros x Hx. unfold dec_writes in Hx.
    destruct Hx as [Hx|[(_ & Hx)|Hx]]; [left; exact Hx| |].
    + right; right; right. exists (q - 16, dec_size tb + 16). split; [exact HQ|]. split; [exact HQn | cbn [fst snd]; lia].
    + right; left. split; [lia|]. rewrite SEG in BN. replace x with (lenp + (x - lenp)) by lia.
      apply (crt_bytes_some mem' lenp _ (x - lenp) BN). rewrite length_le8. lia.
  - intros x Hx. unfold dec_writes.
    destruct (Z_lt_le_dec x lenp) as [Hx1|Hx1]; [|destruct (Z_lt_le_dec x (lenp + 8)) as [Hx2|Hx2]].
    2: { left. right. right. lia. }
    all: right; intros [Hs|[(_ & Hs)|Hs]]; [| |lia].
    all: try (destruct (crt_GS2 B API GF x Hs) as (_ & Hr & _); unfold CRT_STK, ALLOC_STACK in *; lia).
    all: destruct (crt_blk B API GF AX L' A' mem' md' (q - 16) (dec_size tb + 16) (x - (q - 16)) HM' HQ ltac:(lia))
      as (R & _); unfold CRT_STK, ALLOC_STACK in *; lia.
  - exact LG'.
  - lia.
  - lia.
  - exact (perm_skip _ PMc).
  - apply (nb_perm L' A' ((q - 16, dec_size tb + 16) :: P ++ map xblk X)).
    + exact (nb_add Lc Ac L' A' (P ++ map xblk X) _ b1 b2 NBc (cr_entry_sub X P Lc Ac memc mdc Lamc peakc cntc _ CRc)
        BL' BL (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM') ltac:(cbn [snd]; lia)).
    + cbn [map]. exact (Permutation_middle P (map xblk X) _).
  - rewrite <- (bat_xmalloc X P q (dec_size tb)). exact RES'.
  - rewrite <- (bat_xmalloc X P q (dec_size tb)). apply (hs_cap_malloc (bat X P) Nc CRT_SIZE); [lia | exact HCc].
Qed.

Hypothesis RTP : ms_tp B = U.Prog.strtod_c.STRTOD_TP.
Hypothesis RER : errno_addr B = U.Prog.strtod_c.STRTOD_ERRNO.
Hypothesis RGG : ms_got_guard B = U.Prog.strtod_c.STRTOD_GOT_GUARD.
Hypothesis RGD : ms_guard B = U.Prog.strtod_c.STRTOD_GUARD.
Hypothesis RSP : spZ regs <= 2 ^ 47.
Hypothesis RGT : U.Prog.strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK.

Lemma crt_rdc : forall Lc Ac memc mdc, MR Lc Ac memc mdc -> ro_agree rsegs memc -> rd_cells B memc.
Proof.
  intros Lc Ac memc mdc HM RA. destruct (lib.U.Reusable.YL01.ax_statics AX _ _ _ _ HM) as (W1 & (g & _ & W2) & _).
  split; [rewrite SEG; exact RA|]. split; [exact W1 | exists g; exact W2].
Qed.

Lemma crt_gk : forall m m', rd_cells B m -> rd_cells B m' -> guard_kept B m m'.
Proof.
  intros m m' (_ & W & _) (_ & W' & _) i Hi.
  pose proof (W (Z.to_nat i) ltac:(lia)) as E. pose proof (W' (Z.to_nat i) ltac:(lia)) as E'.
  rewrite Z2Nat.id in E, E' by lia. rewrite E, E'. reflexivity.
Qed.

Lemma crt_raw : forall (m m' : word -> option byte) (x : word), find_segment rsegs (bv_unsigned x) 1 = None ->
  mbyte rsegs m' (bv_unsigned x) = mbyte rsegs m (bv_unsigned x) -> m' x = m x.
Proof.
  intros m m' x F E. pose proof (seg_rom_unmapped rsegs _ F) as R0.
  assert (Hm : forall mm : word -> option byte, mbyte rsegs mm (bv_unsigned x) =
     match mm x with Some b => Some b | None => None end).
  { intros mm. unfold mbyte. rewrite MState.Z_to_bv_bv_unsigned. destruct (mm x); [reflexivity | exact R0]. }
  rewrite !Hm in E. destruct (m' x), (m x); congruence.
Qed.

Lemma crt_fs_none : forall x, (alloc_ceiling <= x < 2 ^ 64 \/ (0 <= x /\ ~ in_img B x)) ->
  find_segment rsegs x 1 = None.
Proof.
  intros x Hx. destruct (find_segment rsegs x 1) as [seg|] eqn:F; [|reflexivity]. exfalso.
  pose proof (past_nul.pn_seg_img B SEG _ _ F) as HI.
  destruct (crt_IL B SEG) as [H1 _]. pose proof (H1 x HI). destruct Hx as [Hx|[_ Hx]]; [lia | exact (Hx HI)].
Qed.

Lemma crt_frame_rw : forall Lc Ac memc mdc v, GI B API L A regs mem md Lc Ac memc mdc ->
  spZ regs - 352 <= v -> v + 56 <= spZ regs -> v mod 8 = 0 -> pj_rw rsegs memc v.
Proof.
  intros Lc Ac memc mdc v ((_ & _ & _ & _ & _ & _ & _ & _ & S) & _) H1 H2 H3.
  pose proof crt_sp B API L A regs mem md PRE as (Hsp1 & Hsp2 & _). pose proof alloc_ceiling_val as Hacv.
  split; [exact H3|]. split; [lia|]. split; [lia|]. intros a Ha.
  assert (W : writable_at (ms_segs B) memc a) by (apply S; left; unfold CRT_STK, ALLOC_STACK; lia).
  rewrite SEG in W. unfold writable_at in W. split; [exact W | exact (past_nul.pn_rd memc _ W)].
Qed.

Lemma crt_rplace_frame : forall Lc Ac memc mdc Lamc regsc v, MR Lc Ac memc mdc -> st_init_done Ac = true ->
  spZ regsc = spZ regs - 352 -> spZ regs - 352 <= v -> v + 56 <= spZ regs -> rplace B Lc Ac Lamc regsc memc v.
Proof.
  intros Lc Ac memc mdc Lamc regsc v HM INI SPc H1 H2.
  pose proof crt_sp B API L A regs mem md PRE as (Hsp1 & Hsp2 & _). pose proof alloc_ceiling_val as Hacv.
  destruct (crt_IL B SEG) as [IL _].
  split; [left; rewrite SPc; lia|]. split; [intros _ Hf; rewrite INI in Hf; discriminate|].
  intros i Hi. split; [intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho); lia|].
  split; [intros Hs; destruct (crt_GS B API GF _ Hs) as [_ Hr]; lia|].
  split; [lia|]. intros Hi'. pose proof (IL _ Hi'). lia.
Qed.

Lemma crt_renv : forall Lc Ac memc mdc regsc K, GI B API L A regs mem md Lc Ac memc mdc ->
  getr regsc 2 = Z_to_bv 64 (spZ regs - 352) -> getr regsc 4 = getr regs 4 -> lib.Reusable.YK0s.ret_ok (getr regsc 1) ->
  0 <= K -> K + 352 <= CRT_STK -> frm_zero fp_csr ->
  spZ regsc = spZ regs - 352 /\ reader_env B API K Lc Ac regsc memc mdc.
Proof.
  intros Lc Ac memc mdc regsc K GIc R2 R4 R1 HK HK2 FRM.
  destruct (crt_pre Lc Ac memc mdc regsc K GIc R2 R4 R1 HK HK2) as [SPc PREc].
  pose proof GIc as ((HMc & _) & _ & _ & _ & RAc & _).
  split; [exact SPc|].
  split; [exact SEG|]. split; [exact RTP|]. split; [exact RER|]. split; [exact RGG|]. split; [exact RGD|].
  split; [exact PREc|]. split; [rewrite SPc; lia|]. split; [rewrite SPc; lia|]. split; [exact FRM|].
  exact (crt_rdc Lc Ac memc mdc HMc RAc).
Qed.

Lemma nb_relist : forall X P X' Lc Ac Lc' Ac' memc' Lamc' pk c f,
  NBok L A Lc Ac (P ++ map xblk X) -> (forall z, In z (blocks L A) -> In z (blocks Lc Ac)) ->
  ledger B Lc' Ac' memc' Lamc' pk c f -> Permutation Lamc' (X' ++ Lam) ->
  (forall y, In y P -> In y (blocks Lc' Ac')) ->
  (forall d, In d X' -> In d X \/ ~ In (xblk d) (blocks Lc Ac)) ->
  NBok L A Lc' Ac' (P ++ map xblk X').
Proof.
  intros X P X' Lc Ac Lc' Ac' memc' Lamc' pk c f (INC & ND & NE) HE LG' PM' HP HX.
  pose proof LG' as (_ & _ & _ & _ & NDf & _). apply NoDup_ListNoDup in NDf.
  assert (NDX : List.NoDup (map fst X')).
  { pose proof (Permutation_NoDup (Permutation_map fst PM') NDf) as H. rewrite map_app in H.
    exact (NoDup_app_remove_r _ _ H). }
  assert (NDx : List.NoDup (map xblk X')).
  { clear -NDX. induction X' as [|[a k] X' IH]; [constructor|]. cbn [map fst] in NDX |- *.
    apply NoDup_cons_iff in NDX as [Hn ND]. constructor; [|exact (IH ND)].
    intros Hin. apply in_map_iff in Hin as ([a' k'] & E & Hin). unfold xblk in E. cbn [fst snd] in E.
    injection E as E1 _. apply Hn. apply in_map_iff. exists (a', k'). split; [cbn; lia | exact Hin]. }
  apply NoDup_ListNoDup in ND.
  split; [|split].
  - intros z Hz. apply in_app_or in Hz as [Hz|Hz]; [exact (HP z Hz)|].
    apply in_map_iff in Hz as ([a k] & <- & Hd).
    exact (proj1 (crt_lam_blk Lc' Ac' memc' Lamc' pk c f a k LG'
      (Permutation_in _ (Permutation_sym PM') (in_or_app _ _ _ (or_introl Hd))))).
  - apply NoDup_ListNoDup. apply crt_nd_app; [exact (NoDup_app_remove_r _ _ ND) | exact NDx |].
    intros z Hz Hz'. apply in_map_iff in Hz' as (d & <- & Hd).
    destruct (HX d Hd) as [Hd'|Hn].
    + apply (crt_nd_app_not _ _ _ ND Hz). apply in_map. exact Hd'.
    + apply Hn. apply INC. apply in_or_app. left. exact Hz.
  - intros z Hz. apply in_app_or in Hz as [Hz|Hz]; [apply NE; apply in_or_app; left; exact Hz|].
    apply in_map_iff in Hz as (d & <- & Hd). destruct (HX d Hd) as [Hd'|Hn].
    + apply NE. apply in_or_app. right. apply in_map. exact Hd'.
    + intros He. apply Hn. exact (HE _ He).
Qed.

Lemma nb_P_kept : forall spc K E G X P Lc Ac memc mdc Lc' Ac' memc' mdc',
  cs B API spc K E G Lc Ac memc mdc Lc' Ac' memc' mdc' -> NBok L A Lc Ac (P ++ map xblk X) ->
  (forall a n, G a n -> In (a, n) (map xblk X)) ->
  forall y, In y P -> In y (blocks Lc' Ac').
Proof.
  intros spc K E G X P Lc Ac memc mdc Lc' Ac' memc' mdc' CS (INC & ND & _) HG [a n] Hy.
  apply NoDup_ListNoDup in ND.
  apply (fun Hg => proj1 (cs_blk B API SEG _ _ _ _ _ _ _ _ _ _ _ _ a n CS (INC _ (in_or_app _ _ _ (or_introl Hy))) Hg)).
  intros Hg. exact (crt_nd_app_not _ _ _ ND Hy (HG a n Hg)).
Qed.

Lemma crt_node_present : forall m lblk p t D x, pj_node rsegs m lblk p t D -> p <= x < p + 56 ->
  mbyte rsegs m x <> None.
Proof.
  intros m lblk p t D x H Hx. destruct t; cbn [pj_node] in H;
    destruct H as (_ & _ & num & str & kids & keys & n & cap & ((_ & _ & _ & HS) & _) & _);
    destruct (HS x Hx) as (_ & b & Hb); intros E;
    assert (E' : Mem.mrd rsegs m (Mem.wa x) = None) by exact E;
    assert (Hb' : Mem.mrd rsegs m (Mem.wa x) = Some b) by exact Hb; congruence.
Qed.

Lemma w_string : pj_string_contract B API sb_form ->
  forall X P Lc Ac regsc memc mdc Lamc peakc cntc Nc v s str slack (Q : config -> Prop),
  frm_zero fp_csr ->
  CR X P Lc Ac memc mdc Lamc peakc cntc (Datatypes.S Nc) ->
  getr regsc 2 = Z_to_bv 64 (spZ regs - 352) -> getr regsc 4 = getr regs 4 -> lib.Reusable.YK0s.ret_ok (getr regsc 1) ->
  getr regsc 10 = Z_to_bv 64 v -> getr regsc 11 = Z_to_bv 64 s ->
  spZ regs - 352 <= v -> v + 56 <= spZ regs - 104 -> v mod 8 = 0 ->
  s <> 0 -> Mem.bytes_at (ms_segs B) memc s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  cstr_ok B Lamc s (Z.of_nat (length str) + 1) ->
  Frame.disjoint_from [(v, v + 56)] s (Z.of_nat (length str) + 1) ->
  Frame.disjoint_from [(s, s + Z.of_nat (length str) + 1)] (spZ regs - 352 - PJ_STRING_K) PJ_STRING_K ->
  Z.of_nat (length str) + 17 <= CRT_SIZE -> cntc < 2 ^ 63 ->
  (forall Lc' Ac' regs' memc' mdc' a,
     regs_preserved regsc regs' -> getr regs' 10 = Z_to_bv 64 0 ->
     CR ((a, Z.of_nat (length str) + 1) :: X) P Lc' Ac' memc' mdc' ((a, Z.of_nat (length str) + 1) :: Lamc)
       (Z.max peakc (lsum ((a, Z.of_nat (length str) + 1) :: Lamc))) (cntc + 1) Nc ->
     cs B API (spZ regs - 352) PJ_STRING_K (pj_string_writes v) (fun _ _ => False) Lc Ac memc mdc Lc' Ac' memc' mdc' ->
     rd_cells B memc' ->
     pj_node rsegs memc' (lin ((a, Z.of_nat (length str) + 1) :: Lamc)) v (JStr (zb str))
       [(a, Z.of_nat (length str) + 1)] ->
     SR (ms_segs B) (mkCfg (mkst regs' (getr regsc 1) memc' (seg_rom (ms_segs B))) mdc') Q) ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PJ_STRING) memc (seg_rom (ms_segs B))) mdc) Q.
Proof.
  intros PJS X P Lc Ac regsc memc mdc Lamc peakc cntc Nc v s cs0 slack Q FRM CRc R2 R4 R1 R10 R11 Hv1 Hv2 Hv3
    Hs0 BS NZ SL CSO DJ1 DJ2 Hsz Hc K.
  pose proof CRc as (GIc & NBc & LGc & PKc & CNc & PMc & RSc & HCc).
  pose proof GIc as ((HMc & _) & _ & _ & INIc & RAc & _).
  pose proof crt_sp B API L A regs mem md PRE as (Hsp1 & Hsp2 & _).
  pose proof alloc_ceiling_val as Hacv. pose proof LGc as (_ & _ & Hc00 & _).
  assert (HKs : PJ_STRING_K = 8288) by reflexivity.
  destruct (crt_renv Lc Ac memc mdc regsc PJ_STRING_K GIc R2 R4 R1 ltac:(lia)
    ltac:(unfold CRT_STK, ALLOC_STACK; lia) FRM) as [SPc ENV].
  eapply SR_bind.
  { apply (PJS Lc Ac regsc memc mdc Lamc peakc cntc (2 ^ 64 - 1) (bat X P) v s cs0 slack ENV LGc RSc R10 R11).
    - lia.
    - rewrite SEG. exact (crt_frame_rw Lc Ac memc mdc v GIc Hv1 ltac:(lia) Hv3).
    - exact (crt_rplace_frame Lc Ac memc mdc Lamc regsc v HMc INIc SPc Hv1 ltac:(lia)).
    - rewrite SPc. cbn [Frame.disjoint_from]. split; [lia | exact I].
    - right. split; [exact Hs0|]. split; [exact BS|]. split; [exact NZ|]. split; [exact SL|]. split; [exact CSO|].
      split; [exact DJ1 | rewrite SPc; exact DJ2].
    - unfold CRT_SIZE in Hsz. lia.
    - apply (hs_cap_room (bat X P) Nc CRT_SIZE); [unfold CRT_SIZE; lia | lia | exact HCc]. }
  intros c1 (L' & A' & regs' & mem' & md' & Lam' & peak' & fail' & res & -> & RP & RDC & R10' & LG' & BR).
  destruct BR as [(_ & -> & -> & RES' & (a & -> & NBk & -> & ND)) | (Hcf & _)]; [|lia]. rewrite SEG in ND.
  destruct (cs_of_rpost B API AX CO PJ_STRING_K Lc Ac regsc memc mdc _ _ L' A' regs' mem' md' HMc RP) as [CS RP'].
  rewrite SPc in CS.
  pose proof CS as (HM' & _).
  rewrite (Z.mod_small (cntc + 1) (2 ^ 64)) in LG' by lia.
  apply (K L' A' regs' mem' md' a RP' R10'); [| exact CS | exact RDC | exact ND].
  apply (cr_mk X P Lc Ac memc mdc Lamc peakc cntc (Datatypes.S Nc) ((a, Z.of_nat (length cs0) + 1) :: X) P L' A' mem' md'
    _ _ (cntc + 1) Nc PJ_STRING_K _ _ CRc CS).
  - pose proof RDC as (RA' & _). rewrite <- SEG. exact RA'.
  - exact (crt_gk memc mem' (crt_rdc Lc Ac memc mdc HMc RAc) RDC).
  - lia.
  - unfold CRT_STK, ALLOC_STACK. lia.
  - intros p n _ [].
  - intros x [Hx|Hx]; [right; left; split; [lia | exact (crt_node_present mem' _ v _ _ x ND Hx)] | left; exact Hx].
  - intros x Hx. unfold pj_string_writes.
    destruct (Z_lt_le_dec x v) as [H1|H1]; [|destruct (Z_lt_le_dec x (v + 56)) as [H2|H2]].
    2: { left. left. lia. }
    all: right; intros [Hx'|Hs]; [lia|]; destruct (crt_GS B API GF _ Hs) as [_ Hr]; unfold CRT_STK, ALLOC_STACK in *; lia.
  - exact LG'.
  - lia.
  - lia.
  - exact (perm_skip _ PMc).
  - apply (nb_relist X P ((a, Z.of_nat (length cs0) + 1) :: X) Lc Ac L' A' mem' _ _ _ _ NBc
      (cr_entry_sub X P Lc Ac memc mdc Lamc peakc cntc _ CRc) LG'
      (perm_skip _ PMc)).
    + exact (nb_P_kept _ _ _ _ X P Lc Ac memc mdc L' A' mem' md' CS NBc (fun a n H => match H with end)).
    + intros d [<-|Hd]; [right; exact (NBk _ _ (or_introl eq_refl)) | left; exact Hd].
  - rewrite <- (bat_xmalloc X P a (Z.of_nat (length cs0) + 1)).
    replace (Z.of_nat (length cs0) + 1 + 16) with (Z.of_nat (length cs0) + 17) by lia. exact RES'.
  - rewrite <- (bat_xmalloc X P a (Z.of_nat (length cs0) + 1)).
    apply (hs_cap_malloc (bat X P) Nc CRT_SIZE); [lia | exact HCc].
Qed.

Lemma bat_run : forall X P X' tr, Z.of_nat (length X') = Z.of_nat (length X) + nlive tr ->
  lsum X' = lsum X + held tr -> rf_run sb_form (bat X P) tr = bat X' P.
Proof. intros X P X' tr H1 H2. rewrite sb_run_eq. unfold bat. cbn [sb_live sb_bytes sb_cap]. f_equal; lia. Qed.

Lemma bat_frees : forall X Y P D, Permutation X (D ++ Y) -> rf_frees sb_form (bat X P) D = bat Y P.
Proof.
  intros X Y P D H. rewrite sb_frees_eq. unfold bat. cbn [sb_live sb_bytes sb_cap].
  rewrite (Permutation_length H), length_app, (lsum_perm _ _ H), lsum_app. f_equal; lia.
Qed.

Lemma bat_cap_down : forall X Y P D N, Permutation X (D ++ Y) -> 0 <= lsum D ->
  hs_cap (bat X P) N CRT_SIZE -> hs_cap (bat Y P) N CRT_SIZE.
Proof.
  intros X Y P D N H HD (H1 & H2). unfold hs_cap, bat in *. cbn [sb_live sb_bytes sb_cap] in *.
  rewrite (Permutation_length H), length_app in H1, H2. rewrite (lsum_perm _ _ H), lsum_app in H2. split; lia.
Qed.

Lemma cr_nodup : forall X P Lc Ac memc mdc Lamc peakc cntc Nc, CR X P Lc Ac memc mdc Lamc peakc cntc Nc ->
  List.NoDup (map fst X).
Proof.
  intros X P Lc Ac memc mdc Lamc peakc cntc Nc (_ & _ & (_ & _ & _ & _ & ND & _) & _ & _ & PM & _).
  apply NoDup_ListNoDup in ND. pose proof (Permutation_NoDup (Permutation_map fst PM) ND) as H.
  rewrite map_app in H. exact (NoDup_app_remove_r _ _ H).
Qed.

Lemma cr_X_lam : forall X P Lc Ac memc mdc Lamc peakc cntc Nc Z0, CR X P Lc Ac memc mdc Lamc peakc cntc Nc ->
  Permutation X Z0 -> forall a k, In (a, k) Z0 ->
  In (a, k) Lamc /\ 4112 <= a /\ a + k <= alloc_ceiling /\ 0 <= k /\ forall i, -16 <= i < k -> ~ in_img B (a + i).
Proof.
  intros X P Lc Ac memc mdc Lamc peakc cntc Nc Z0 CRc PX a k H.
  pose proof CRc as (((HMc & _) & _) & _ & LGc & _).
  assert (H' : In (a, k) Lamc) by (apply (cr_in_lam X P Lc Ac memc mdc Lamc peakc cntc Nc a k CRc);
    exact (Permutation_in _ (Permutation_sym PX) H)).
  destruct (ledger_block_range B API Lc Ac memc mdc Lamc peakc cntc _ a k HMc LGc H') as (R1 & R2 & _).
  destruct (crt_lam_blk Lc Ac memc Lamc peakc cntc _ a k LGc H') as (_ & Hk0 & NI).
  split; [exact H'|]. split; [lia|]. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + i) with (a - 16 + (i + 16)) by lia. apply NI. lia.
Qed.

Lemma crt_rw_present : forall m p x, pj_rw rsegs m p -> p <= x < p + 56 -> mbyte rsegs m x <> None.
Proof.
  intros m p x (_ & _ & _ & HS) Hx. destruct (HS x Hx) as (_ & b & Hb). intros E.
  assert (E' : Mem.mrd rsegs m (Mem.wa x) = None) by exact E.
  assert (Hb' : Mem.mrd rsegs m (Mem.wa x) = Some b) by exact Hb. congruence.
Qed.

Lemma crt_ro_img : forall x, 0 <= x < 2 ^ 64 -> Mem.ro_addr rsegs (Z_to_bv 64 x) = true -> in_img B x.
Proof.
  intros x Hx H. unfold Mem.ro_addr in H. rewrite MState.unsigned_lit in H by lia.
  destruct (find_segment rsegs x 1) as [seg|] eqn:F; [|discriminate].
  exact (past_nul.pn_seg_img B SEG _ _ F).
Qed.

Lemma crt_errno_img : forall i, 0 <= i < 4 -> in_img B (errno_addr B + i).
Proof.
  intros i Hi. rewrite RER.
  assert (F : exists seg, find_segment rsegs (U.Prog.strtod_c.STRTOD_ERRNO + i) 1 = Some seg).
  { assert (H : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct H as [->|[->|[->| ->]]]; unfold U.Prog.strtod_c.STRTOD_ERRNO; vm_compute; eexists; reflexivity. }
  destruct F as (seg & F). exact (past_nul.pn_seg_img B SEG _ _ F).
Qed.

Ltac crt_fk FK :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hr' := fresh "Hr'" in let E := fresh "E" in
  intros r Hr; apply FK;
  assert (Hr' : r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/
    r = 26 \/ r = 27) by lia;
  repeat (destruct Hr' as [E|Hr']; [subst r; vm_compute; lia|]); subst r; vm_compute; lia.

Lemma w_set : pj_set_contract B API sb_form ->
  forall X P Lc Ac regsc memc mdc Lamc peakc cntc Nc o w k ms tv D Dw Y kname slack (Q : config -> Prop),
  frm_zero fp_csr ->
  CR X P Lc Ac memc mdc Lamc peakc cntc (Datatypes.S (Datatypes.S (Datatypes.S Nc))) ->
  getr regsc 2 = Z_to_bv 64 (spZ regs - 352) -> getr regsc 4 = getr regs 4 -> lib.Reusable.YK0s.ret_ok (getr regsc 1) ->
  getr regsc 10 = Z_to_bv 64 o -> getr regsc 11 = Z_to_bv 64 k -> getr regsc 12 = Z_to_bv 64 w ->
  spZ regs - 352 <= o -> o + 56 <= spZ regs - 104 ->
  spZ regs - 352 <= w -> w + 56 <= spZ regs - 104 -> o + 56 <= w \/ w + 56 <= o ->
  pj_node rsegs memc (lin Lamc) o (JObj ms) D -> pj_node rsegs memc (lin Lamc) w tv Dw ->
  Permutation X (D ++ Dw ++ Y) ->
  (depth (JObj ms) <= 2)%nat -> (depth tv <= 1)%nat -> (length ms <= 2)%nat -> ~ In (zb kname) (map fst ms) ->
  Mem.bytes_at (ms_segs B) memc k (kname ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) kname ->
  (- (k + Z.of_nat (length kname) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (forall i, 0 <= i < Z.of_nat (length kname) + 1 + Z.of_nat (length slack) ->
     Mem.ro_addr rsegs (Z_to_bv 64 (k + i)) = true) ->
  Z.of_nat (length kname) + 17 <= CRT_SIZE -> cntc < 2 ^ 63 ->
  (forall Lc' Ac' regs' memc' mdc' Lamc' peakc' cntc' Do,
     regs_preserved regsc regs' -> getr regs' 10 = Z_to_bv 64 0 ->
     CR (Do ++ Y) P Lc' Ac' memc' mdc' Lamc' peakc' cntc' Nc -> cntc' <= cntc + 3 ->
     cs B API (spZ regs - 352) (PJ_SET_K 1) (pj_set_writes o w D Dw) (freed (D ++ Dw))
       Lc Ac memc mdc Lc' Ac' memc' mdc' ->
     rd_cells B memc' ->
     pj_node rsegs memc' (lin Lamc') o (JObj (pj_set_model ms (zb kname) tv)) Do -> pj_zero rsegs memc' w ->
     SR (ms_segs B) (mkCfg (mkst regs' (getr regsc 1) memc' (seg_rom (ms_segs B))) mdc') Q) ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PJ_SET) memc (seg_rom (ms_segs B))) mdc) Q.
Proof.
  intros PJS X P Lc Ac regsc memc mdc Lamc peakc cntc Nc o w k ms tv D Dw Y kname slack Q FRM CRc R2 R4 R1 R10 R11 R12
    Ho1 Ho2 Hw1 Hw2 HOW NO NW PX Hd1 Hd2 Hlen HK KB KZ KS KRO Hksz Hc K.
  pose proof CRc as (GIc & NBc & LGc & PKc & CNc & PMc & RSc & HCc).
  pose proof GIc as ((HMc & _) & _ & _ & INIc & RAc & _).
  pose proof crt_sp B API L A regs mem md PRE as (Hsp1 & Hsp2 & _).
  pose proof alloc_ceiling_val as Hacv. pose proof lib.Reusable.YM05.alloc_ceiling_lt as Hacl. pose proof LGc as (_ & _ & Hc00 & _).
  assert (HKs : PJ_SET_K 1 = 8400) by reflexivity.
  destruct (crt_renv Lc Ac memc mdc regsc (PJ_SET_K 1) GIc R2 R4 R1 ltac:(lia)
    ltac:(unfold CRT_STK, ALLOC_STACK; lia) FRM) as [SPc ENV].
  pose proof NO as NO'. cbn [pj_node] in NO'.
  destruct NO' as (_ & _ & num & str & kids & keys & n & cap & HH & _ & En & Hncap & Hcap & _).
  assert (Hcap54 : cap <= 2 ^ 54).
  { destruct Hcap as [(-> & _)|(Hc0 & Hk & _)]; [lia|].
    pose proof (ledger_block_range B API Lc Ac memc mdc Lamc peakc cntc _ kids (56 * cap) HMc LGc Hk) as (Rk & R & _).
    lia. }
  pose proof (cr_nodup X P Lc Ac memc mdc Lamc peakc cntc _ CRc) as NDX.
  assert (NDl : List.NoDup (D ++ Dw ++ Y)).
  { apply (NoDup_map_inv fst). exact (Permutation_NoDup (Permutation_map fst PX) NDX). }
  assert (LO : forall a kk, In (a, kk) (D ++ Dw ++ Y) ->
     4112 <= a /\ a + kk <= alloc_ceiling /\ 0 <= kk /\ forall i, -16 <= i < kk -> ~ in_img B (a + i)).
  { intros a kk H. destruct (cr_X_lam X P Lc Ac memc mdc Lamc peakc cntc _ _ CRc PX a kk H) as (_ & H1 & H2 & H3 & H4).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact H4]. }
  assert (KI : forall x, k <= x < k + Z.of_nat (length kname) + 1 -> in_img B x /\ x < alloc_ceiling).
  { intros x Hx. destruct KB as (Hk0 & Hkl & _). rewrite length_app in Hkl. cbn [length] in Hkl.
    assert (HI : in_img B x).
    { apply crt_ro_img; [lia|]. replace x with (k + (x - k)) by lia. apply KRO. lia. }
    split; [exact HI|]. destruct (crt_IL B SEG) as [IL _]. pose proof (IL x HI). lia. }
  assert (Hn2 : 0 <= n <= 2) by lia.
  destruct (set_trace_ok n cap (Z.of_nat (length kname)) Hn2 ltac:(lia) Hksz Hncap) as [TF TL].
  destruct (room_cap _ (bat X P) (Datatypes.S (Datatypes.S (Datatypes.S Nc))) TF ltac:(lia) HCc) as [ROOM HCr].
  assert (HGX : forall a0 n0, freed (D ++ Dw) a0 n0 -> In (a0, n0) (map xblk X)).
  { intros a0 n0 Hg. unfold freed in Hg. apply in_map_iff. exists (a0 + 16, n0 - 16).
    split; [unfold xblk; cbn [fst snd]; f_equal; lia|].
    apply (Permutation_in _ (Permutation_sym PX)). rewrite app_assoc. apply in_or_app. left. exact Hg. }
  eapply SR_bind.
  { apply (PJS Lc Ac regsc memc mdc Lamc peakc cntc (2 ^ 64 - 1) (bat X P) o k w ms tv D Dw num str kids keys n cap
      kname slack 1%nat ENV LGc RSc R10 R11 R12).
    - lia.
    - rewrite SEG. exact NO.
    - rewrite SEG. exact HH.
    - exact Hcap54.
    - exact (crt_rplace_frame Lc Ac memc mdc Lamc regsc o HMc INIc SPc Ho1 ltac:(lia)).
    - lia.
    - rewrite SEG. exact NW.
    - exact (crt_rplace_frame Lc Ac memc mdc Lamc regsc w HMc INIc SPc Hw1 ltac:(lia)).
    - intros bk H1 H2. exact (crt_nd_app_not D (Dw ++ Y) bk NDl H2 (in_or_app _ _ _ (or_introl H1))).
    - intros x Hx [Hx'|([a kk] & Hb & Hbx)]; [lia|]. unfold pj_holds in Hbx. cbn [fst snd] in Hbx.
      destruct (LO a kk (in_or_app _ _ _ (or_introl Hb))) as (_ & R & _). lia.
    - intros [a kk] x Hb Hbx Hx. unfold pj_holds in Hbx. cbn [fst snd] in Hbx.
      destruct (LO a kk ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb)) as (_ & R & _). lia.
    - exact Hd1.
    - exact Hd2.
    - exact KB.
    - exact KZ.
    - exact KS.
    - unfold cstr_ok. left. intros i Hi. rewrite SEG. exact (KRO i Hi).
    - intros x Hx. destruct (KI x Hx) as [HI Hxa]. split.
      + intros [Hx'|([a kk] & Hb & Hbx)]; [lia|]. unfold pj_holds in Hbx. cbn [fst snd] in Hbx.
        destruct (LO a kk (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & NI).
        apply (NI (x - a)); [lia|]. replace (a + (x - a)) with x by lia. exact HI.
      + intros [Hx'|([a kk] & Hb & Hbx)]; [lia|]. unfold pj_holds in Hbx. cbn [fst snd] in Hbx.
        destruct (LO a kk ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb)) as (_ & _ & _ & NI).
        apply (NI (x - a)); [lia|]. replace (a + (x - a)) with x by lia. exact HI.
    - rewrite SPc. pose proof (KI (k + Z.of_nat (length kname)) ltac:(lia)) as (_ & Hke).
      cbn [Frame.disjoint_from]. unfold CRT_STK, ALLOC_STACK in *. lia.
    - lia.
    - exact ROOM. }
  intros c1 (L' & A' & regs' & mem' & md' & Lam' & peak' & fail' & res & c & Lr & Do & -> & RP & RDC & R10' & LG' & FA &
    PL & PL' & ZW & _ & BR).
  destruct BR as [(HIn & _) | [(_ & Hrng & Hcl & Hres & Hpk & RES' & HLD & HLS &
    (Dold & Dnew & Dr & a & PD & PDo & FRESH & _) & NODE) | (_ & Hrng & _)]];
    [exact (False_rect _ (HK HIn)) | | lia].
  rewrite (proj2 FA) in LG' by lia.
  destruct (cs_of_rpost B API AX CO (PJ_SET_K 1) Lc Ac regsc memc mdc _ _ L' A' regs' mem' md' HMc RP) as [CS RP'].
  rewrite SPc in CS. pose proof CS as (HM' & _).
  rewrite SEG in NODE, ZW.
  assert (PLr : Permutation Lr (Y ++ Lam)).
  { apply (Permutation_app_inv_l (D ++ Dw)). rewrite <- !app_assoc.
    eapply Permutation_trans; [exact (Permutation_sym PL)|]. eapply Permutation_trans; [exact PMc|].
    rewrite !app_assoc. apply Permutation_app_tail. rewrite <- !app_assoc. exact PX. }
  assert (PX' : Permutation Lam' ((Do ++ Y) ++ Lam)).
  { rewrite <- app_assoc. eapply Permutation_trans; [exact PL'|]. apply Permutation_app_head. exact PLr. }
  assert (HL1 : length X = (length D + length Dw + length Y)%nat) by (rewrite (Permutation_length PX), !length_app; lia).
  assert (HS1 : lsum X = lsum D + lsum Dw + lsum Y) by (rewrite (lsum_perm _ _ PX), !lsum_app; lia).
  rewrite length_app in HLD. rewrite lsum_app in HLS.
  assert (BAT : rf_run sb_form (bat X P) (set_trace n cap (Z.of_nat (length kname))) = bat (Do ++ Y) P).
  { apply bat_run; rewrite ?length_app, ?lsum_app; lia. }
  rewrite Hres in R10'.
  apply (K L' A' regs' mem' md' Lam' peak' (cntc + Z.of_nat c) Do RP' R10'); [| lia | exact CS | exact RDC | exact NODE |
    exact ZW].
  apply (cr_mk X P Lc Ac memc mdc Lamc peakc cntc _ (Do ++ Y) P L' A' mem' md' Lam' peak' (cntc + Z.of_nat c) Nc
    (PJ_SET_K 1) _ _ CRc CS).
  - pose proof RDC as (RA' & _). rewrite <- SEG. exact RA'.
  - exact (crt_gk memc mem' (crt_rdc Lc Ac memc mdc HMc RAc) RDC).
  - lia.
  - unfold CRT_STK, ALLOC_STACK. lia.
  - intros p nn Hp Hg. pose proof NBc as (_ & _ & NE). apply (NE (p, nn)); [|exact Hp].
    apply in_or_app. right. exact (HGX p nn Hg).
  - intros x Hx. unfold pj_set_writes in Hx.
    destruct Hx as [Hx|[Hx|[(aa & kk & Hb & Hbx)|Hx]]].
    + right. left. split; [lia | exact (crt_node_present mem' _ o _ _ x NODE Hx)].
    + right. left. split; [lia | exact (crt_rw_present mem' w x (proj1 ZW) Hx)].
    + right. right. left. exists (xblk (aa, kk)). split; [|unfold xblk; cbn [fst snd]; lia].
      apply in_or_app. right. apply in_map. apply (Permutation_in _ (Permutation_sym PX)). rewrite app_assoc.
      apply in_or_app. left. exact Hb.
    + left. exact Hx.
  - intros x Hx. unfold pj_set_writes.
    assert (NB : ~ blk_set (D ++ Dw) x).
    { intros (aa & kk & Hb & Hbx). destruct (LO aa kk ltac:(rewrite app_assoc; apply in_or_app; left; exact Hb))
        as (_ & R & _). unfold CRT_STK, ALLOC_STACK in *. lia. }
    assert (NS : ~ alloc_statics x).
    { intros Hs. destruct (crt_GS B API GF x Hs) as [_ Hr]. unfold CRT_STK, ALLOC_STACK in *. lia. }
    assert (DEC : (o <= x < o + 56 \/ w <= x < w + 56) \/ ~ (o <= x < o + 56 \/ w <= x < w + 56)) by lia.
    destruct DEC as [DEC|DEC]; [left; destruct DEC as [DEC|DEC]; [left | right; left]; exact DEC|].
    right. intros [H|[H|[H|H]]]; [exact (DEC (or_introl H)) | exact (DEC (or_intror H)) | exact (NB H) | exact (NS H)].
  - exact LG'.
  - rewrite Hpk. lia.
  - lia.
  - exact PX'.
  - apply (nb_relist X P (Do ++ Y) Lc Ac L' A' mem' Lam' peak' (cntc + Z.of_nat c) (2 ^ 64 - 1) NBc
      (cr_entry_sub X P Lc Ac memc mdc Lamc peakc cntc _ CRc) LG' PX').
    + exact (nb_P_kept _ _ _ _ X P Lc Ac memc mdc L' A' mem' md' CS NBc HGX).
    + assert (INX : forall y, In y (D ++ Dw ++ Y) -> In y X) by (intros y Hy; exact (Permutation_in _ (Permutation_sym PX) Hy)).
      assert (IND : forall y, In y D -> In y X) by (intros y Hy; apply INX; apply in_or_app; left; exact Hy).
      assert (INO : forall y, In y Dold -> In y X).
      { intros y Hy. apply IND. apply (Permutation_in _ (Permutation_sym PD)). apply in_or_app. left. exact Hy. }
      intros d Hd. apply in_app_or in Hd as [Hd|Hd].
      * apply (Permutation_in _ PDo) in Hd. apply in_app_or in Hd as [Hd|[Hd|Hd]].
        -- destruct d as [a' k']. destruct (FRESH a' k' (in_or_app _ _ _ (or_introl Hd))) as [Hold|Hnew];
             [left; exact (INO _ Hold) | right; exact Hnew].
        -- subst d. destruct (FRESH a (Z.of_nat (length kname) + 1) ltac:(apply in_or_app; right; left; reflexivity))
             as [Hold|Hnew]; [left; exact (INO _ Hold) | right; exact Hnew].
        -- left. apply in_app_or in Hd as [Hd|Hd].
           ++ apply IND. apply (Permutation_in _ (Permutation_sym PD)). apply in_or_app. right. exact Hd.
           ++ apply INX. apply in_or_app. right. apply in_or_app. left. exact Hd.
      * left. apply INX. apply in_or_app. right. apply in_or_app. right. exact Hd.
  - rewrite <- BAT. exact RES'.
  - rewrite <- BAT. exact (hs_cap_le _ (Datatypes.S (Datatypes.S (Datatypes.S Nc)) -
      length (set_trace n cap (Z.of_nat (length kname)))) Nc CRT_SIZE ltac:(lia) ltac:(unfold CRT_SIZE; lia) HCr).
Qed.

Lemma w_pfree : pj_free_contract B API sb_form ->
  forall X P Lc Ac regsc memc mdc Lamc peakc cntc Nc v t D Y (Q : config -> Prop),
  frm_zero fp_csr -> CR X P Lc Ac memc mdc Lamc peakc cntc Nc ->
  getr regsc 2 = Z_to_bv 64 (spZ regs - 352) -> getr regsc 4 = getr regs 4 -> lib.Reusable.YK0s.ret_ok (getr regsc 1) ->
  getr regsc 10 = Z_to_bv 64 v -> spZ regs - 352 <= v -> v + 56 <= spZ regs - 104 ->
  pj_node rsegs memc (lin Lamc) v t D -> (depth t <= 2)%nat -> Permutation X (D ++ Y) ->
  (forall Lc' Ac' regs' memc' mdc' Lamc',
     regs_preserved regsc regs' -> CR Y P Lc' Ac' memc' mdc' Lamc' peakc cntc Nc ->
     cs B API (spZ regs - 352) (PJ_FREE_K 2) (pj_free_writes v D) (freed D) Lc Ac memc mdc Lc' Ac' memc' mdc' ->
     rd_cells B memc' -> pj_zero rsegs memc' v ->
     SR (ms_segs B) (mkCfg (mkst regs' (getr regsc 1) memc' (seg_rom (ms_segs B))) mdc') Q) ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PJ_FREE) memc (seg_rom (ms_segs B))) mdc) Q.
Proof.
  intros PJF X P Lc Ac regsc memc mdc Lamc peakc cntc Nc v t D Y Q FRM CRc R2 R4 R1 R10 Hv1 Hv2 NV Hd PX K.
  pose proof CRc as (GIc & NBc & LGc & PKc & CNc & PMc & RSc & HCc).
  pose proof GIc as ((HMc & _) & _ & _ & INIc & RAc & _).
  pose proof crt_sp B API L A regs mem md PRE as (Hsp1 & Hsp2 & _).
  pose proof alloc_ceiling_val as Hacv.
  assert (HKf : PJ_FREE_K 2 = 8336) by reflexivity.
  destruct (crt_renv Lc Ac memc mdc regsc (PJ_FREE_K 2) GIc R2 R4 R1 ltac:(lia)
    ltac:(unfold CRT_STK, ALLOC_STACK; lia) FRM) as [SPc ENV].
  assert (LO : forall a kk, In (a, kk) (D ++ Y) -> 4112 <= a /\ a + kk <= alloc_ceiling /\ 0 <= kk).
  { intros a kk H. destruct (cr_X_lam X P Lc Ac memc mdc Lamc peakc cntc _ _ CRc PX a kk H) as (_ & H1 & H2 & H3 & _).
    lia. }
  assert (HGX : forall a0 n0, freed D a0 n0 -> In (a0, n0) (map xblk X)).
  { intros a0 n0 Hg. unfold freed in Hg. apply in_map_iff. exists (a0 + 16, n0 - 16).
    split; [unfold xblk; cbn [fst snd]; f_equal; lia|].
    apply (Permutation_in _ (Permutation_sym PX)). apply in_or_app. left. exact Hg. }
  eapply SR_bind.
  { apply (PJF Lc Ac regsc memc mdc Lamc peakc cntc (2 ^ 64 - 1) (bat X P) v 2%nat D ENV LGc RSc R10).
    right. split; [lia|]. split.
    { rewrite SEG. apply (pj_fd_mono rsegs memc (lin Lamc) (depth t) 2 v D Hd). exact (pj_node_fd rsegs t memc _ v D NV). }
    split; [exact (crt_rplace_frame Lc Ac memc mdc Lamc regsc v HMc INIc SPc Hv1 ltac:(lia))|].
    rewrite SPc. cbn [Frame.disjoint_from]. split; [lia | exact I]. }
  intros c1 (L' & A' & regs' & mem' & md' & Lam' & -> & RP & RDC & PL & LG' & (D' & PD' & RES') & _ & ZV).
  specialize (ZV ltac:(lia)). rewrite SEG in ZV.
  destruct (cs_of_rpost B API AX CO (PJ_FREE_K 2) Lc Ac regsc memc mdc _ _ L' A' regs' mem' md' HMc RP) as [CS RP'].
  rewrite SPc in CS.
  assert (PY : Permutation Lam' (Y ++ Lam)).
  { apply (Permutation_app_inv_l D). eapply Permutation_trans; [exact (Permutation_sym PL)|].
    eapply Permutation_trans; [exact PMc|]. rewrite app_assoc. apply Permutation_app_tail. exact PX. }
  assert (HD0 : 0 <= lsum D).
  { apply lsum_nonneg. apply Forall_forall. intros [a kk] Hin.
    destruct (LO a kk (in_or_app _ _ _ (or_introl Hin))) as (_ & _ & H). exact H. }
  apply (K L' A' regs' mem' md' Lam' RP'); [| exact CS | exact RDC | exact ZV].
  apply (cr_mk X P Lc Ac memc mdc Lamc peakc cntc Nc Y P L' A' mem' md' Lam' peakc cntc Nc (PJ_FREE_K 2) _ _ CRc CS).
  - pose proof RDC as (RA' & _). rewrite <- SEG. exact RA'.
  - exact (crt_gk memc mem' (crt_rdc Lc Ac memc mdc HMc RAc) RDC).
  - lia.
  - unfold CRT_STK, ALLOC_STACK. lia.
  - intros p nn Hp Hg. pose proof NBc as (_ & _ & NE). apply (NE (p, nn)); [|exact Hp].
    apply in_or_app. right. exact (HGX p nn Hg).
  - intros x (_ & [Hx|[(aa & kk & Hb & Hbx)|Hx]]).
    + right. left. split; [lia | exact (crt_rw_present mem' v x (proj1 ZV) Hx)].
    + right. right. left. exists (xblk (aa, kk)). split; [|unfold xblk; cbn [fst snd]; lia].
      apply in_or_app. right. apply in_map. apply (Permutation_in _ (Permutation_sym PX)). apply in_or_app. left. exact Hb.
    + left. exact Hx.
  - intros x Hx. unfold pj_free_writes.
    assert (NB : ~ blk_set D x).
    { intros (aa & kk & Hb & Hbx). destruct (LO aa kk (in_or_app _ _ _ (or_introl Hb))) as (_ & R & _).
      unfold CRT_STK, ALLOC_STACK in *. lia. }
    assert (NS : ~ alloc_statics x).
    { intros Hs. destruct (crt_GS B API GF x Hs) as [_ Hr]. unfold CRT_STK, ALLOC_STACK in *. lia. }
    assert (DEC : v <= x < v + 56 \/ ~ (v <= x < v + 56)) by lia.
    destruct DEC as [DEC|DEC]; [left; split; [lia | left; exact DEC]|].
    right. intros (_ & [H|[H|H]]); [exact (DEC H) | exact (NB H) | exact (NS H)].
  - exact LG'.
  - lia.
  - lia.
  - exact PY.
  - apply (nb_relist X P Y Lc Ac L' A' mem' Lam' peakc cntc (2 ^ 64 - 1) NBc
      (cr_entry_sub X P Lc Ac memc mdc Lamc peakc cntc _ CRc) LG' PY).
    + exact (nb_P_kept _ _ _ _ X P Lc Ac memc mdc L' A' mem' md' CS NBc HGX).
    + intros d Hdd. left. apply (Permutation_in _ (Permutation_sym PX)). apply in_or_app. right. exact Hdd.
  - rewrite <- (sb_frees_perm (bat X P) D D' PD') in RES'. rewrite (bat_frees X Y P D PX) in RES'. exact RES'.
  - exact (bat_cap_down X Y P D Nc PX HD0 HCc).
Qed.

Lemma w_write : pj_write_contract_sb B API ->
  forall X P Lc Ac regsc memc mdc Lamc peakc cntc Nc v t D Y (Q : config -> Prop),
  frm_zero fp_csr -> CR X P Lc Ac memc mdc Lamc peakc cntc (Datatypes.S (Datatypes.S Nc)) ->
  getr regsc 2 = Z_to_bv 64 (spZ regs - 352) -> getr regsc 4 = getr regs 4 -> lib.Reusable.YK0s.ret_ok (getr regsc 1) ->
  getr regsc 10 = Z_to_bv 64 v -> getr regsc 11 = Z_to_bv 64 1 -> spZ regs - 352 <= v -> v + 56 <= spZ regs - 104 ->
  pj_node rsegs memc (lin Lamc) v t D -> Permutation X (D ++ Y) -> (depth t <= 2)%nat ->
  Z.of_nat (length (wdoc t true)) + 1 <= 2 ^ 22 -> cntc < 2 ^ 63 ->
  (forall (fx' : lib.Reusable.YK11.FPState) Lc' Ac' regs' memc' mdc' q c peakc' cntc',
     fregs_kept fx fx' -> frm_zero (@fp_csr fx') -> regs_preserved regsc regs' -> getr regs' 10 = Z_to_bv 64 q ->
     CR ((q, c) :: X) P Lc' Ac' memc' mdc' ((q, c) :: Lamc) peakc' cntc' Nc -> cntc' <= cntc + 11 ->
     Z.of_nat (length (wdoc t true)) + 1 <= c -> c + 16 <= CRT_SIZE -> c mod 4096 = 0 ->
     cs B API (spZ regs - 352) (PJW_K t) alloc_statics (fun _ _ => False) Lc Ac memc mdc Lc' Ac' memc' mdc' ->
     pj_node rsegs memc' (lin ((q, c) :: Lamc)) v t D ->
     zbytes_at B memc' q (wdoc t true ++ [0]) ->
     SR (ms_segs B) (mkCfg (@mkst fx' regs' (getr regsc 1) memc' (seg_rom (ms_segs B))) mdc') Q) ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PJ_WRITE_PC) memc (seg_rom (ms_segs B))) mdc) Q.
Proof.
  intros PJW X P Lc Ac regsc memc mdc Lamc peakc cntc Nc v t D Y Q FRM CRc R2 R4 R1 R10 R11 Hv1 Hv2 NV PX Hd Hwd Hc K.
  pose proof CRc as (GIc & NBc & LGc & PKc & CNc & PMc & RSc & HCc).
  pose proof GIc as ((HMc & _) & _ & _ & INIc & RAc & _).
  pose proof crt_sp B API L A regs mem md PRE as (Hsp1 & Hsp2 & _).
  pose proof alloc_ceiling_val as Hacv. pose proof LGc as (_ & _ & Hc00 & _).
  assert (HKw : PJW_K t <= 8928).
  { unfold PJW_K, PJW_FR, WV_K, WV_FR, WV_KMAX, PS_K, IND_K, PUT_K, REALLOC_STACK, ALLOC_STACK. lia. }
  assert (HKw0 : 0 <= PJW_K t) by (unfold PJW_K, PJW_FR, PUT_K, REALLOC_STACK, ALLOC_STACK; lia).
  destruct (crt_pre Lc Ac memc mdc regsc (PJW_K t) GIc R2 R4 R1 HKw0 ltac:(unfold CRT_STK, ALLOC_STACK; lia))
    as [SPc PREc].
  assert (HDX : forall a kk, In (a, kk) D -> In (a, kk) Lamc).
  { intros a kk H. exact (proj1 (cr_X_lam X P Lc Ac memc mdc Lamc peakc cntc _ _ CRc PX a kk (in_or_app _ _ _ (or_introl H)))). }
  destruct (wr_result (wdpieces t true) cntc ltac:(unfold wdpieces; destruct (wvpieces t true 0); discriminate) ltac:(lia) Hc Hwd)
    as (W1 & W2 & W3 & W4 & W5 & W6).
  pose proof RSc as (_ & _ & _ & _ & _ & _ & _ & _ & (Hbat0 & _) & Hbat1 & _).
  eapply SR_bind.
  { apply (PJW Lc Ac regsc memc mdc (bat X P) v 1 t D Lamc peakc cntc (2 ^ 64 - 1) SEG
      ltac:(rewrite RGG; reflexivity) ltac:(rewrite RGD; reflexivity)).
    - split; [exact PREc | rewrite SPc; change TASK_SIZE with (2 ^ 47); lia].
    - exact INIc.
    - rewrite SEG. exact RAc.
    - exact FRM.
    - exact R10.
    - exact R11.
    - lia.
    - exact LGc.
    - unfold off_errno. right. rewrite SPc. unfold CRT_STK, ALLOC_STACK in *. lia.
    - exact NV.
    - left. rewrite SPc. split; [lia|]. unfold off_errno. right. unfold CRT_STK, ALLOC_STACK in *. lia.
    - exact HDX.
    - lia.
    - change (negb (1 =? 0)) with true. unfold WMAX. lia.
    - exact RSc.
    - pose proof HCc as (HC1 & HC2). unfold wr_room. unfold bat, CRT_SIZE in *. cbn [sb_live sb_bytes sb_cap] in *. lia. }
  intros c1 HW. unfold pj_write_ret_sb in HW. cbv zeta in HW. change (negb (1 =? 0)) with true in HW.
  destruct HW as (fx' & L' & A' & regs' & mem' & md' & Lam' & peak' & b' & -> & FK & FRM' & RP & HM' & HWF' & HBD' &
    RA' & GK' & LG' & RES' & LY & LEN' & INI' & VM & UK & KP & NODE & MEMF & WINF & BR).
  destruct BR as [(_ & q & R10' & Hq0 & Hqn & -> & Hpk & -> & ZB) | (Wf1 & _)]; [|exact (False_rect _ (Wf1 W1))].
  rewrite W2 in LG'.
  set (c := w_cap (putN (w0 cntc (2 ^ 64 - 1)) (wdpieces t true))) in *.
  set (n := w_cnt (putN (w0 cntc (2 ^ 64 - 1)) (wdpieces t true))) in *.
  assert (CS : cs B API (spZ regsc) (PJW_K t) alloc_statics (fun _ _ => False) Lc Ac memc mdc L' A' mem' md').
  { split; [exact HM'|]. split; [exact HWF'|]. split; [exact HBD'|]. split; [exact LY|]. split; [exact LEN'|].
    split; [exact INI'|].
    split; [intros p nn Hp _; exact (proj2 (UK p nn Hp))|].
    split; [intros p nn Hp _; exact (proj1 (UK p nn Hp))|].
    split; [exact VM|].
    split.
    { intros a Ha Ho Hw He Hs. apply MEMF; [exact Ha | exact Ho | | exact Hw | exact He | exact Hs].
      exact (check_reject_clean_starved.crs_own_mid B API AX CO Lc Ac memc mdc L' A' mem' md' a HMc HM' Ha Ho). }
    split.
    { intros p nn i Hp Hp' Hi _. apply (KP (ptr_addr Lc p) nn i); [|  | exact Hi].
      - unfold blocks. apply in_map_iff. exists (p, nn). split; [reflexivity | exact Hp].
      - pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p nn HMc Hp). lia. }
    intros a Ha. apply WINF; [exact Ha|]. pose proof PREc as (_ & _ & _ & _ & _ & _ & _ & HWS & _ & HER & _).
    destruct Ha as [Ha|Ha]; [apply HWS; exact Ha | apply HER; exact Ha]. }
  rewrite SPc in CS.
  assert (NODE' : pj_node rsegs mem' (lin ((q, c) :: Lamc)) v t D).
  { apply (pj_node_frame rsegs t mem' (wv_lblk Lamc) mem' _ v D NODE); [|intros x _; reflexivity].
    intros a kk Hin. right. exact (HDX a kk Hin). }
  assert (FK' : fregs_kept fx fx') by crt_fk FK.
  apply (K fx' L' A' regs' mem' md' q c peak' n FK' FRM' RP R10'); [| lia | unfold wdoc; lia | unfold CRT_SIZE; lia |
    exact W6 | exact CS | exact NODE' | exact ZB].
  apply (cr_mk X P Lc Ac memc mdc Lamc peakc cntc _ ((q, c) :: X) P L' A' mem' md' ((q, c) :: Lamc) peak' n Nc
    (PJW_K t) _ _ CRc CS).
  - rewrite <- SEG. exact RA'.
  - exact GK'.
  - exact HKw0.
  - unfold CRT_STK, ALLOC_STACK. lia.
  - intros p nn _ [].
  - intros x Hx. left. exact Hx.
  - intros x Hx. right. intros Hs. destruct (crt_GS B API GF x Hs) as [_ Hr]. unfold CRT_STK, ALLOC_STACK in *. lia.
  - exact LG'.
  - rewrite Hpk. lia.
  - lia.
  - exact (perm_skip _ PMc).
  - apply (nb_relist X P ((q, c) :: X) Lc Ac L' A' mem' ((q, c) :: Lamc) peak' n (2 ^ 64 - 1) NBc
      (cr_entry_sub X P Lc Ac memc mdc Lamc peakc cntc _ CRc) LG' (perm_skip _ PMc)).
    + exact (nb_P_kept _ _ _ _ X P Lc Ac memc mdc L' A' mem' md' CS NBc (fun a0 n0 H => match H with end)).
    + intros d [<-|Hdd]; [right; exact Hqn | left; exact Hdd].
  - rewrite <- (bat_xmalloc X P q c). exact RES'.
  - rewrite <- (bat_xmalloc X P q c).
    exact (hs_cap_le _ (Datatypes.S Nc) Nc CRT_SIZE ltac:(lia) ltac:(unfold CRT_SIZE; lia)
      (hs_cap_malloc (bat X P) (Datatypes.S Nc) CRT_SIZE (c + 16) ltac:(unfold CRT_SIZE; lia) HCc)).
Qed.

Lemma w_parse : pj_parse_contract B API sb_form ->
  forall X P Lc Ac regsc memc mdc Lamc peakc cntc Nc t0 tb out t (Q : config -> Prop),
  frm_zero fp_csr -> CR X P Lc Ac memc mdc Lamc peakc cntc Nc ->
  getr regsc 2 = Z_to_bv 64 (spZ regs - 352) -> getr regsc 4 = getr regs 4 -> lib.Reusable.YK0s.ret_ok (getr regsc 1) ->
  getr regsc 10 = Z_to_bv 64 t0 -> getr regsc 11 = Z_to_bv 64 (Z.of_nat (length tb)) ->
  getr regsc 12 = Z_to_bv 64 out -> spZ regs - 352 <= out -> out + 56 <= spZ regs - 104 -> out mod 8 = 0 ->
  Mem.bytes_at (ms_segs B) memc t0 tb -> zb tb = wdoc t true -> PjRoundTrip.pj_wf jr_strtod t ->
  (exists a k, In (a, k) Lamc /\ a <= t0 /\ t0 + Z.of_nat (length tb) <= a + k) ->
  Z.of_nat (length tb) < 2 ^ 22 -> cntc < 2 ^ 63 ->
  Forall (fun e => Z.of_nat (esize e) + 16 <= CRT_SIZE) (PjRoundTrip.ttrace t) ->
  (length (PjRoundTrip.ttrace t) <= Nc)%nat ->
  (forall (fx' : lib.Reusable.YK11.FPState) Lc' Ac' regs' memc' mdc' Lamc' peakc' cntc' D,
     fregs_kept fx fx' -> frm_zero (@fp_csr fx') -> regs_preserved regsc regs' -> getr regs' 10 = Z_to_bv 64 0 ->
     CR (D ++ X) P Lc' Ac' memc' mdc' Lamc' peakc' cntc' (Nc - length (PjRoundTrip.ttrace t)) ->
     cntc' <= cntc + Z.of_nat (length (PjRoundTrip.ttrace t)) ->
     cs B API (spZ regs - 352) PJ_PARSE_K (pj_parse_writes out) (fun _ _ => False) Lc Ac memc mdc Lc' Ac' memc' mdc' ->
     rd_cells B memc' ->
     pj_node rsegs memc' (lin Lamc') out t D ->
     SR (ms_segs B) (mkCfg (@mkst fx' regs' (getr regsc 1) memc' (seg_rom (ms_segs B))) mdc') Q) ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PJ_PARSE) memc (seg_rom (ms_segs B))) mdc) Q.
Proof.
  intros PJP X P Lc Ac regsc memc mdc Lamc peakc cntc Nc t0 tb out t Q FRM CRc R2 R4 R1 R10 R11 R12 Hu1 Hu2 Hu3 TB Ezb WF
    TBL Htl Hc TF TL K.
  pose proof CRc as (GIc & NBc & LGc & PKc & CNc & PMc & RSc & HCc).
  pose proof GIc as ((HMc & _) & _ & _ & INIc & RAc & _).
  pose proof crt_sp B API L A regs mem md PRE as (Hsp1 & Hsp2 & _).
  pose proof alloc_ceiling_val as Hacv. pose proof lib.Reusable.YM05.alloc_ceiling_lt as Hacl. pose proof LGc as (_ & _ & Hc00 & _).
  assert (HKp : PJ_PARSE_K = 14160) by reflexivity.
  destruct (crt_renv Lc Ac memc mdc regsc PJ_PARSE_K GIc R2 R4 R1 ltac:(lia)
    ltac:(unfold CRT_STK, ALLOC_STACK; lia) FRM) as [SPc ENV].
  destruct TBL as (a & k & Hak & Ha1 & Ha2).
  pose proof (ledger_block_range B API Lc Ac memc mdc Lamc peakc cntc _ a k HMc LGc Hak) as (Ra1 & Ra2 & _).
  destruct (crt_lam_blk Lc Ac memc Lamc peakc cntc _ a k LGc Hak) as (Hab & Hk0 & _).
  assert (HTR : snd (jr_run jr_strtod (zb tb) []) = PjRoundTrip.ttrace t).
  { rewrite Ezb. exact (PjRoundTrip.G9_trace jr_strtod t WF true). }
  destruct (room_cap _ (bat X P) _ TF TL HCc) as [ROOM HCr].
  assert (HNC : (ncalls jr_strtod (zb tb) <= 2 * length tb + 2)%nat).
  { unfold ncalls. pose proof (G7_4 jr_strtod (zb tb) []) as G. unfold zb in G. rewrite length_map in G. exact G. }
  eapply SR_bind.
  { apply (PJP Lc Ac regsc memc mdc Lamc peakc cntc (2 ^ 64 - 1) (bat X P) t0 (Z.of_nat (length tb)) out tb
      ENV LGc RSc R10 R11 R12).
    - lia.
    - lia.
    - lia.
    - reflexivity.
    - exact TB.
    - pose proof (PjRoundTrip.G12_1 (zb tb)) as G. unfold zb in G at 2. rewrite length_map in G. lia.
    - split; [right; right; right; exists a, k; split; [exact Hak | lia]|].
      intros i Hi.
      destruct (crt_blk B API GF AX Lc Ac memc mdc (a - 16) (k + 16) (t0 + i - (a - 16)) HMc Hab ltac:(lia))
        as (_ & NI & NO & NS).
      replace (a - 16 + (t0 + i - (a - 16))) with (t0 + i) in * by lia.
      split; [exact NO|]. split; [exact NS|]. intros He. apply NI.
      replace (t0 + i) with (errno_addr B + (t0 + i - errno_addr B)) by lia. apply crt_errno_img. lia.
    - lia.
    - rewrite SEG. exact (crt_frame_rw Lc Ac memc mdc out GIc Hu1 ltac:(lia) Hu3).
    - exact (crt_rplace_frame Lc Ac memc mdc Lamc regsc out HMc INIc SPc Hu1 ltac:(lia)).
    - intros a' k' H. pose proof (ledger_block_range B API Lc Ac memc mdc Lamc peakc cntc _ a' k' HMc LGc H) as (_ & R & _).
      unfold CRT_STK, ALLOC_STACK in *. lia.
    - cbn [Frame.disjoint_from]. unfold CRT_STK, ALLOC_STACK in *. split; [lia | exact I].
    - rewrite SPc. cbn [Frame.disjoint_from]. unfold CRT_STK, ALLOC_STACK in *. lia.
    - lia.
    - rewrite HTR. exact ROOM. }
  intros c1 (fx' & L' & A' & regs' & mem' & md' & Lam' & peak' & cnt' & fail' & ok & res & tr & -> & FZ & FK & RP & RDC &
    LG' & JR & OKS & CN & FA & PK & _ & _ & H2 & MT).
  destruct (H2 ltac:(right; lia)) as [Eres Ecalls].
  assert (Ett : tr = PjRoundTrip.ttrace t).
  { assert (HU : forall i, (i < ncalls jr_strtod (zb tb))%nat -> nth i ok true = true).
    { intros i Hi. rewrite (OKS i ltac:(lia)). apply negb_true_iff. apply Z.eqb_neq. lia. }
    pose proof (G7_1 jr_strtod (zb tb) ok HU) as G. rewrite JR in G. injection G as _ G. rewrite G. exact HTR. }
  subst tr.
  rewrite Ezb, (PjRoundTrip.G9 jr_strtod t WF true) in Eres. subst res.
  destruct MT as (R10' & RES' & D & PLD & HSZ & HLN & NBk & NODE).
  pose proof (lsz_counts D _ HSZ HLN) as HLS.
  rewrite (proj2 FA) in LG' by lia. rewrite CN in LG'.
  destruct (cs_of_rpost B API AX CO PJ_PARSE_K Lc Ac regsc memc mdc _ _ L' A' regs' mem' md' HMc RP) as [CS RP'].
  rewrite SPc in CS. rewrite SEG in NODE.
  pose proof (calls_le (PjRoundTrip.ttrace t)) as HCL.
  assert (PD' : Permutation Lam' ((D ++ X) ++ Lam)).
  { rewrite <- app_assoc. eapply Permutation_trans; [exact PLD|]. apply Permutation_app_head. exact PMc. }
  apply (K fx' L' A' regs' mem' md' Lam' peak' (cntc + Z.of_nat (calls (PjRoundTrip.ttrace t))) D FK FZ RP' R10');
    [| lia | exact CS | exact RDC | exact NODE].
  apply (cr_mk X P Lc Ac memc mdc Lamc peakc cntc Nc (D ++ X) P L' A' mem' md' Lam' peak'
    (cntc + Z.of_nat (calls (PjRoundTrip.ttrace t))) _ PJ_PARSE_K _ _ CRc CS).
  - pose proof RDC as (RA' & _). rewrite <- SEG. exact RA'.
  - exact (crt_gk memc mem' (crt_rdc Lc Ac memc mdc HMc RAc) RDC).
  - lia.
  - unfold CRT_STK, ALLOC_STACK. lia.
  - intros p nn _ [].
  - intros x [Hx|Hx]; [right; left; split; [lia | exact (crt_node_present mem' _ out _ _ x NODE Hx)] | left; exact Hx].
  - intros x Hx. unfold pj_parse_writes.
    assert (DEC : out <= x < out + 56 \/ ~ (out <= x < out + 56)) by lia.
    destruct DEC as [DEC|DEC]; [left; left; exact DEC|]. right. intros [H|H]; [exact (DEC H)|].
    destruct (crt_GS B API GF x H) as [_ Hr]. unfold CRT_STK, ALLOC_STACK in *. lia.
  - exact LG'.
  - rewrite PK. lia.
  - lia.
  - exact PD'.
  - apply (nb_relist X P (D ++ X) Lc Ac L' A' mem' Lam' peak' _ (2 ^ 64 - 1) NBc
      (cr_entry_sub X P Lc Ac memc mdc Lamc peakc cntc _ CRc) LG' PD').
    + exact (nb_P_kept _ _ _ _ X P Lc Ac memc mdc L' A' mem' md' CS NBc (fun a0 n0 H => match H with end)).
    + intros [a' k'] Hd. apply in_app_or in Hd as [Hd|Hd]; [right; exact (NBk a' k' Hd) | left; exact Hd].
  - rewrite <- (bat_run X P (D ++ X) (PjRoundTrip.ttrace t) ltac:(rewrite length_app; lia) ltac:(rewrite lsum_app; lia)).
    exact RES'.
  - rewrite <- (bat_run X P (D ++ X) (PjRoundTrip.ttrace t) ltac:(rewrite length_app; lia) ltac:(rewrite lsum_app; lia)).
    exact HCr.
Qed.

End W.
