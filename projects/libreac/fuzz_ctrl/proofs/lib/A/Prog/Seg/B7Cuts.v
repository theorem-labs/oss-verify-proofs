(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 540 of its 622 lines of code are new or changed and 2475 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F20.v, with its module paths, module names and numbers changed; 322 of its 378 lines of code are new or changed and 566 lines of the source are left out. *)
(* Helpers of batch B7 (segments F22-F28) of fuzz_ctrl LLVMFuzzerTestOneInput, asan build of image A, libreac
   v1.9.0: the head-amp record check and the inlined check_ports, 0x82554 .. 0x82750 (v1.8 0x824a8 .. 0x826a4,
   every instruction EQUAL at +0xac). The segments are stated on the official SlotInv.v cuts (B7CUT = the
   frame-loop skeleton with FLSI, B7K and the body; Inv_A82554_at .. Inv_A826d4_at, and Inv_A82750_at for the exit
   of F27 and F28b). This file has no cut of its own; it has:
   - the FLSI transports b7_flsi_regs (memory unchanged), b7_flsi_win (a run that writes app memory only) and
     b7_flsi_keep (a run that may also write shadow bytes, none of FLSI's), with FLC's b7_flc_keep (push 14D / 14E;
     v1.9: PRO's 16th conjunct [A + 32] = fr + 2880 and FLC's 13th / 14th [A + 56] = fr + 2889, [A + 48] = fr + 2890
     are carried like the other spills);
   - the B7K transports b7_B7K_regs (memory unchanged) and b7_B7K_keep (a run that misses the spills, the live
     block, the frame's records and the FIRST body first.sroa.7 at fr + 2880, and the shadow bytes of that body),
     with LT's b7_lt_keep and the record sizes b7_tID_len / b7_tFG_len (a Theorem Labs lane's F36.v f36_tID_len /
     f36_tFG_len, a working branch) and the FIRST body's size b7_fsbody_len;
   - b7_a826a4, the 0x82750 body (LK, FLS, LT) from FLSI, B7K and s9 = fr + 64. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame MState Regs6ss RegisterBridge Exec Cells Step Tac Bytes.
Import ListNotations.
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import AYK.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.

(* In this region the frame is at least 50 bytes (B7K), so the allocated size of the live block is its length. *)
Lemma b7_asize_flen : forall g j phi fr regs m,
  B7K g j phi fr regs m -> AC.a_size (flen g j) = flen g j.
Proof.
  intros g j phi fr regs m HK.
  destruct HK as (_ & _ & _ & _ & _ & Hfl & _).
  unfold AC.a_size. lia.
Qed.

(* A spill read through s1 = A: its base is A (A in range). *)
Lemma b7_spill_at : forall regs m A off v, rg regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= off ->
  off + 8 <= 416 -> spill regs m off v -> q64 m (A + off) v.
Proof.
  intros regs m A off v H9 HA0 HA Ho0 Ho (A' & H9' & Hq).
  assert (E : A' = A).
  { pose proof Hq as (Hq0 & Hq1 & _). rewrite length_le8 in Hq1. cbn in Hq1.
    unfold rg in H9, H9'. rewrite H9 in H9'. apply (f_equal bv_unsigned) in H9'.
    rewrite (unsigned_lit A) in H9' by lia. rewrite Z_to_bv_unsigned in H9'. unfold bv_wrap, bv_modulus in H9'.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in H9'.
    pose proof (Z.div_mod A' (2 ^ 64) ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound A' (2 ^ 64) ltac:(lia)).
    lia. }
  subst A'. exact Hq.
Qed.

(* A spill survives a register change that keeps s1 (memory unchanged). *)
Lemma b7_spill_regs : forall regs regs' m off v, getr regs' 9 = getr regs 9 ->
  spill regs m off v -> spill regs' m off v.
Proof. intros regs regs' m off v E (A & HA & Hq). exists A. unfold rg in *. rewrite E. split; assumption. Qed.

(* A spill survives a run that misses the spill area [A, A + 416) and keeps s1. *)
Lemma b7_spill_keep : forall regs regs' mem mem' W A off v,
  rg regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> getr regs' 9 = getr regs 9 -> munch W mem mem' ->
  (forall x, A <= x < A + 416 -> outside W x) -> 0 <= off -> off + 8 <= 416 ->
  spill regs mem off v -> spill regs' mem' off v.
Proof.
  intros regs regs' mem mem' W A off v H9 HA0 HA E9 MU HWA Ho0 Ho1 Hs.
  pose proof (b7_spill_at regs mem A off v H9 HA0 HA Ho0 Ho1 Hs) as Hq.
  exists A. split; [unfold rg in *; rewrite E9; exact H9|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8. intros x Hx. apply HWA. lia.
Qed.

(* addressable survives a run that leaves the shadow byte of each of its bytes alone. *)
Lemma b7_addr_munch : forall W m m' p n, munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m p n -> addressable m' p n.
Proof.
  intros W m m' p n MU Ho (H1 & H2 & H3 & H).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Happ & b & Hb & Hok).
  pose proof (shadow_of_app (p + i) Happ) as His.
  destruct (in_shadow_range (shadow_addr (p + i)) His) as (R1 & R2).
  assert (Hmb : mbyte rsegs m' (shadow_addr (p + i)) = mbyte rsegs m (shadow_addr (p + i)))
    by exact (mbyte_munch rsegs W m m' (shadow_addr (p + i)) MU ltac:(lia) (Ho i Hi)).
  split; [exact Happ|]. exists b. split; [|exact Hok]. exact (eq_trans Hmb Hb).
Qed.

(* A write set of app memory misses every shadow byte. *)
Lemma b7_app_shadow_out : forall W a, all_app W -> in_shadow a -> outside W a.
Proof.
  intros W a AW Ha. induction W as [|[lo hi] W IH]; cbn [outside all_app] in *; [exact I|].
  destruct AW as (Hlh & AW). split; [|exact (IH AW)]. intros Hx. exact (app_not_shadow a (Hlh a Hx) Ha).
Qed.

(* ---- FLSI transports ---- *)

(* FLC (push 14D / 14E; v1.9: [A + 192 / 80 / 88 / 96 / 72 / 64] and the two FIRST-body pointers [A + 56] /
   [A + 48]) across a run that keeps the spills [A + 48] .. [A + 280) and the two record ranges' addressability
   (the 72 bytes at fragb fr and the 38 bytes at fr + 2688). *)
Lemma b7_flc_keep : forall fr regs regs' (m m' : word -> option byte),
  (forall off v, 48 <= off <= 272 -> spill regs m off v -> spill regs' m' off v) ->
  (addressable m (fragb fr) 72 -> addressable m' (fragb fr) 72) ->
  (addressable m (fr + 2688) 38 -> addressable m' (fr + 2688) 38) ->
  FLC fr regs m -> FLC fr regs' m'.
Proof.
  intros fr regs regs' m m' Hs Ha72 Ha38
    (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & A72 & A38 & C72 & C64 & C56 & C48).
  split; [exact (Hs 256 _ ltac:(lia) C256)|].
  split; [exact (Hs 184 _ ltac:(lia) C184)|].
  split; [exact (Hs 192 _ ltac:(lia) C192)|].
  split; [exact (Hs 80 _ ltac:(lia) C80)|].
  split; [exact (Hs 88 _ ltac:(lia) C88)|].
  split; [exact (Hs 96 _ ltac:(lia) C96)|].
  split; [exact (Hs 272 _ ltac:(lia) C272)|].
  split; [exact (Hs 264 _ ltac:(lia) C264)|].
  split; [exact (Ha72 A72)|].
  split; [exact (Ha38 A38)|].
  split; [exact (Hs 72 _ ltac:(lia) C72)|].
  split; [exact (Hs 64 _ ltac:(lia) C64)|].
  split; [exact (Hs 56 _ ltac:(lia) C56) | exact (Hs 48 _ ltac:(lia) C48)].
Qed.

(* FLSI reads the registers only through s1 (its spills). FLSH = PRO /\ the loop part (push 13B); PRO's input pair
   and our[] addressability read memory only; FLC is spills and addressability (push 14D / 14E). *)
Lemma b7_flsi_regs : forall g j fr regs regs' m,
  FLSI g j fr regs m -> getr regs' 9 = getr regs 9 -> FLSI g j fr regs' m.
Proof.
  intros g j fr regs regs' m
    (((F40 & F120 & F136 & F160 & F168 & F176 & F208 & P248 & Fout6 & Pin & Pin2 & P184 & P256 & P264 & P272 &
       P32) &
      F128 & Fstk & F144 & Fid17) &
     F216 & F224 & F248 & Fin & FC)
    E9.
  pose proof (b7_spill_regs regs regs' m) as K.
  split; [split|].
  { split; [exact (K _ _ E9 F40)|]. split; [exact (K _ _ E9 F120)|]. split; [exact (K _ _ E9 F136)|].
    split; [exact (K _ _ E9 F160)|]. split; [exact (K _ _ E9 F168)|]. split; [exact (K _ _ E9 F176)|].
    split; [exact (K _ _ E9 F208)|]. split; [exact (K _ _ E9 P248)|]. split; [exact Fout6|].
    split; [exact Pin|]. split; [exact Pin2|].
    split; [exact (K _ _ E9 P184)|]. split; [exact (K _ _ E9 P256)|].
    split; [exact (K _ _ E9 P264)|]. split; [exact (K _ _ E9 P272) | exact (K _ _ E9 P32)]. }
  { split; [exact (K _ _ E9 F128)|]. split; [exact Fstk|].
    split; [exact (K _ _ E9 F144) | exact Fid17]. }
  split; [exact (K _ _ E9 F216)|]. split; [exact (K _ _ E9 F224)|]. split; [exact (K _ _ E9 F248)|].
  split; [exact Fin|].
  exact (b7_flc_keep fr regs regs' m m (fun off v _ H => K off v E9 H) (fun H => H) (fun H => H) FC).
Qed.

(* FLSI moves across a run whose writes may include shadow bytes: the spills [A, A + 416) at s1 = A, the input
   block's bytes, its shadow bytes and the shadow bytes of fr + 2624 .. fr + 2629, of fr + 2688 .. fr + 2725 (the
   identity record; FLSH's 17 bytes at fr + 2691 are among them) and of fragb fr .. fragb fr + 71 (FLC) are
   outside the write set, and the frame window [fr, fr + FRAME_BYTES) is still present and writable after the
   run (stk, from the caller). *)
Lemma b7_flsi_keep : forall g j fr regs regs' mem mem' W A,
  FLSI g j fr regs mem -> rg regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> getr regs' 9 = getr regs 9 ->
  munch W mem mem' ->
  (forall x, A <= x < A + 416 -> outside W x) ->
  (forall i, 0 <= i < 6 -> outside W (shadow_addr (fr + 2624 + i))) ->
  (forall i, 0 <= i < 38 -> outside W (shadow_addr (fr + 2688 + i))) ->
  (forall i, 0 <= i < 72 -> outside W (shadow_addr (fragb fr + i))) ->
  (forall x, g_p g <= x < g_p g + g_n g -> outside W x) ->
  (forall i, 0 <= i < g_n g -> outside W (shadow_addr (g_p g + i))) ->
  stk rsegs mem' fr (fr + FRAME_BYTES) ->
  FLSI g j fr regs' mem'.
Proof.
  intros g j fr regs regs' mem mem' W A
    (((F40 & F120 & F136 & F160 & F168 & F176 & F208 & P248 & Fout6 & Pin & Pin2 & P184 & P256 & P264 & P272 &
       P32) &
      F128 & Fstk & F144 & Fid17) &
     F216 & F224 & F248 & (Fin1 & Fin2 & Fin3) & FC)
    H9 HA0 HA E9 MU HWA HWsh HWsh38 HWsh72 HWin HWinsh Hstk'.
  pose proof (b7_spill_keep regs regs' mem mem' W A) as Kq.
  assert (HWsh17 : forall i, 0 <= i < 17 -> outside W (shadow_addr (fr + 2691 + i))).
  { intros i Hi. replace (fr + 2691 + i) with (fr + 2688 + (i + 3)) by lia. apply HWsh38. lia. }
  assert (Kin : bytes_at rsegs mem' (g_p g) (g_in g)).
  { eapply fl_bytes; [exact Fin3 | exact MU |]. intros x Hx. apply HWin. rewrite g_n_len. lia. }
  assert (Kad : addressable mem' (g_p g) (g_n g)) by exact (b7_addr_munch W mem mem' (g_p g) (g_n g) MU HWinsh Fin2).
  split; [split|].
  { split; [apply (Kq 40 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F40]|].
    split; [apply (Kq 120 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F120]|].
    split; [apply (Kq 136 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F136]|].
    split; [apply (Kq 160 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F160]|].
    split; [apply (Kq 168 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F168]|].
    split; [apply (Kq 176 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F176]|].
    split; [apply (Kq 208 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F208]|].
    split; [apply (Kq 248 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact P248]|].
    split; [exact (b7_addr_munch W mem mem' (fr + 2624) 6 MU HWsh Fout6)|].
    split; [exact Kin|].
    split; [intros Hn; split; [exact (proj1 (Pin2 Hn)) | exact Kad]|].
    split; [apply (Kq 184 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact P184]|].
    split; [apply (Kq 256 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact P256]|].
    split; [apply (Kq 264 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact P264]|].
    split; [apply (Kq 272 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact P272]|].
    apply (Kq 32 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact P32]. }
  { split; [apply (Kq 128 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F128]|].
    split; [exact Hstk'|].
    split; [apply (Kq 144 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F144]|].
    exact (b7_addr_munch W mem mem' (fr + 2691) 17 MU HWsh17 Fid17). }
  split; [apply (Kq 216 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F216]|].
  split; [apply (Kq 224 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F224]|].
  split; [apply (Kq 248 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact F248]|].
  split; [split; [exact Fin1|]; split; [exact Kad | exact Kin]|].
  apply (b7_flc_keep fr regs regs' mem mem'); [| | | exact FC].
  - intros off v Ho Hs. apply (Kq off v H9 HA0 HA E9 MU HWA); [lia | lia | exact Hs].
  - exact (b7_addr_munch W mem mem' (fragb fr) 72 MU HWsh72).
  - exact (b7_addr_munch W mem mem' (fr + 2688) 38 MU HWsh38).
Qed.

(* FLSI moves across a run whose write set W is app memory (no shadow byte changes) and misses the spill area
   [A, A + 416), the frame [fr, fr + FRAME_BYTES) and every block of the entry heap (the input block f1_IN names
   is one of them when n > 0). The statement of a Theorem Labs lane's F20.flsi_win (a working branch). *)
Lemma b7_flsi_win : forall g j fr regs regs' mem mem' W A,
  FLSI g j fr regs mem -> rg regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> getr regs' 9 = getr regs 9 ->
  munch W mem mem' -> wmono rsegs mem mem' -> all_app W ->
  (forall x, A <= x < A + 416 -> outside W x) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> outside W x) ->
  (forall q n x, In (q, n) (g_H g) -> q <= x < q + n -> outside W x) ->
  FLSI g j fr regs' mem'.
Proof.
  intros g j fr regs regs' mem mem' W A HF H9 HA0 HA E9 MU WM AW HWA HWfr HWblk.
  pose proof HF as (((_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & Had6) & _) & _ & Fstk & _ & _) &
                    _ & _ & _ & (Fin1 & (_ & _ & _ & Hadin) & _) &
                    (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & Had72) & (_ & _ & _ & Had38) & _)).
  apply (b7_flsi_keep g j fr regs regs' mem mem' W A HF H9 HA0 HA E9 MU HWA).
  - intros i Hi. apply (b7_app_shadow_out W _ AW). apply shadow_of_app. exact (proj1 (Had6 i Hi)).
  - intros i Hi. apply (b7_app_shadow_out W _ AW). apply shadow_of_app. exact (proj1 (Had38 i Hi)).
  - intros i Hi. apply (b7_app_shadow_out W _ AW). apply shadow_of_app. exact (proj1 (Had72 i Hi)).
  - intros x Hx. apply (HWblk (g_p g) (g_n g) x); [apply Fin1; lia | exact Hx].
  - intros i Hi. apply (b7_app_shadow_out W _ AW). apply shadow_of_app. exact (proj1 (Hadin i Hi)).
  - apply (stk_transport rsegs W mem mem' fr (fr + FRAME_BYTES) Fstk MU WM).
    intros x Hx. left. exact (HWfr x Hx).
Qed.

(* ---- The frame records of LT and the B7K transports ---- *)

(* The frame records keep their sizes: the identity record is ID_SIZE = 38 bytes (ING keeps it) and the fragment
   state 72 bytes, so both lie in [fr + 2688, fr + 2840). a Theorem Labs lane's F36.v (f36_tID_len / f36_fg_st_len /
   f36_tFG_len, a working branch). *)
Lemma b7_tID_len : forall inp j, length (t_ID inp j) = ID_SIZE.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH].
  - cbn [fst_at fs0 fs_id]. unfold ID0. apply repeat_length.
  - rewrite fst_at_S. set (s := fst_at inp j) in *.
    assert (E : fs_id (turn s (t_len inp j) (t_g inp j)) =
                fg_id (rp_id (fs_id s) (t_len inp j) (t_g inp j)) (t_len inp j) (fs_fg s) (t_g inp j))
      by (unfold turn; destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity).
    rewrite E.
    assert (E1 : length (rp_id (fs_id s) (t_len inp j) (t_g inp j)) = ID_SIZE).
    { unfold rp_id. match goal with |- context [if ?b then _ else _] => destruct b end;
        [apply ING_length; exact IH | exact IH]. }
    unfold fg_id. match goal with |- context [if ?b then _ else _] => destruct b end;
      [apply ING_length; exact E1 | exact E1].
Qed.

Lemma b7_fg_st_len : forall len st g, length st = 72%nat -> length g = 50%nat ->
  length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg.
  assert (Hlf : 0 <= fg_lf st).
  { unfold fg_lf, bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat 7) st (Z_to_bv 8 0))) as R. lia. }
  assert (Hnn : forall len', fg_fr len' g = true -> 1 <= fg_n g <= 22).
  { intros len' Ef. unfold fg_fr in Ef. apply andb_prop in Ef as [Ef E2]. apply andb_prop in Ef as [Ef E2'].
    apply andb_prop in Ef as [_ E1]. apply Z.leb_le in E1. apply Z.leb_le in E2'. lia. }
  assert (HJ : 1 <= fg_n g <= 22 -> fg_T st g <= 64 -> length (fg_join st g) = 72%nat).
  { intros Hn HT. unfold fg_T in HT. unfold fg_join, fg_body, bsl.
    rewrite !length_app, !length_firstn, !length_skipn. rewrite Hs, Hg. unfold fg_T. lia. }
  assert (HC : forall l, length l = 72%nat -> length (fg_clear l) = 72%nat).
  { intros l Hl. unfold fg_clear. rewrite !length_app, length_firstn, length_skipn. cbn [length]. lia. }
  unfold fg_st. destruct (fcls len st g) eqn:Ec; cbn [fg_next].
  - exact Hs.
  - exact Hs.
  - unfold fcls, fg_class in Ec. cbn [Z.eqb orb] in Ec.
    destruct (fg_fr len g) eqn:Ef; cbn [negb] in Ec; [|discriminate Ec].
    pose proof (Hnn len Ef) as Hn.
    unfold fg_first, fg_body, bsl. rewrite !length_app, !length_firstn, !length_skipn. cbn [length].
    rewrite Hs, Hg. lia.
  - exact (HC st Hs).
  - unfold fcls, fg_class in Ec. cbn [Z.eqb orb] in Ec.
    destruct (fg_fr len g) eqn:Ef; cbn [negb] in Ec; [|discriminate Ec].
    destruct (bat g 19 =? 1); [discriminate Ec|].
    destruct (fg_keep st g) eqn:Ek; cbn [negb] in Ec; [|discriminate Ec].
    unfold fg_keep in Ek. apply andb_prop in Ek as [_ E3]. apply Z.leb_le in E3.
    exact (HC _ (HJ (Hnn len Ef) E3)).
  - unfold fcls, fg_class in Ec. cbn [Z.eqb orb] in Ec.
    destruct (fg_fr len g) eqn:Ef; cbn [negb] in Ec; [|discriminate Ec].
    destruct (bat g 19 =? 1); [discriminate Ec|].
    destruct (fg_keep st g) eqn:Ek; cbn [negb] in Ec; [|discriminate Ec].
    unfold fg_keep in Ek. apply andb_prop in Ek as [_ E3]. apply Z.leb_le in E3.
    exact (HC _ (HJ (Hnn len Ef) E3)).
Qed.

Lemma b7_tFG_len : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. unfold t_FG. induction j as [|j IH].
  - cbn [fst_at fs0 fs_fg]. exact z72_length.
  - rewrite fst_at_S. set (s := fst_at inp j) in *.
    assert (E : fs_fg (turn s (t_len inp j) (t_g inp j)) = fg_st (t_len inp j) (fs_fg s) (t_g inp j))
      by (unfold turn; destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity).
    rewrite E. apply b7_fg_st_len; [exact IH | unfold t_g; apply fr50_length].
Qed.

Lemma b7_tg_len : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. unfold t_g. apply fr50_length. Qed.

Lemma b7_tblk_len : forall inp j, length (t_blk inp j) = 32%nat.
Proof.
  intros inp j. unfold t_blk, bsl. rewrite length_firstn, length_skipn, b7_tg_len.
  change (Z.to_nat 32) with 32%nat. change (Z.to_nat 18) with 18%nat. reflexivity.
Qed.

(* v1.9: the FIRST body fs_body (SlotModel.turn: `firstn (bat g 26) (skipn 27 g)` of a 50-byte frame, else kept;
   [] at turn 0) has at most 23 bytes, so it lies in first.sroa.7 = [fr + 2880, fr + 2915). *)
Lemma b7_fsbody_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fst_at]. unfold fs0. cbn [fs_body length]. lia.
  - rewrite fst_at_S. set (s := fst_at inp j) in *.
    assert (E : fs_body (turn s (t_len inp j) (t_g inp j)) =
                if f_opens (t_len inp j) (t_g inp j)
                then firstn (Z.to_nat (bat (t_g inp j) 26)) (skipn 27 (t_g inp j)) else fs_body s)
      by (unfold turn; destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity).
    rewrite E. destruct (f_opens (t_len inp j) (t_g inp j)); [|exact IH].
    rewrite length_firstn, length_skipn, b7_tg_len. lia.
Qed.

(* LT (IFS g fr (S j): the frame records of turn j + 1 at fr + 2688 / fr + 2768, the spills [A + 104] / [A + 112]
   and, v1.9, the FIRST body at fr + 2880 with its 35 bytes addressable) reads the registers only through s1. *)
Lemma b7_lt_regs : forall g fr j regs regs' m,
  LT g fr j regs m -> getr regs' 9 = getr regs 9 -> LT g fr j regs' m.
Proof.
  intros g fr j regs regs' m (HID & HFG & (S104 & S112 & Hbody & Hab & HFI)) E9.
  pose proof (b7_spill_regs regs regs' m) as K.
  split; [exact HID|]. split; [exact HFG|].
  split; [exact (K _ _ E9 S104)|]. split; [exact (K _ _ E9 S112)|].
  split; [exact Hbody|]. split; [exact Hab | exact HFI].
Qed.

(* LT across a run whose writes miss the spill area [A, A + 416), the frame records [fr + 2688, fr + 2840)
   (a Theorem Labs lane's F36.v f36_lt_keep) and, v1.9, the FIRST body first.sroa.7 [fr + 2880, fr + 2915) and its shadow
   bytes (FSb's `addressable m (fr + 2880) 35`). *)
Lemma b7_lt_keep : forall g fr j regs regs' mem mem' W A,
  LT g fr j regs mem -> munch W mem mem' -> getr regs' 9 = getr regs 9 ->
  rg regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  (forall x, A <= x < A + 416 -> outside W x) ->
  (forall x, fr + 2688 <= x < fr + 2840 -> outside W x) ->
  (forall x, fr + 2880 <= x < fr + 2915 -> outside W x) ->
  (forall i, 0 <= i < 35 -> outside W (shadow_addr (fr + 2880 + i))) ->
  LT g fr j regs' mem'.
Proof.
  intros g fr j regs regs' mem mem' W A (HID & HFG & HFS) MU E9 Hr9 HA0 HA1 HWA HWF HWB HWBsh.
  pose proof (b7_spill_keep regs regs' mem mem' W A) as SP.
  split; [|split].
  - destruct HID as (HIDB & Hok). split; [|exact Hok]. unfold IDBe in *.
    apply (fl_bytes _ mem mem' _ _ HIDB MU). rewrite b7_tID_len. unfold ID_SIZE.
    intros x Hx. apply HWF. lia.
  - destruct HFG as (HFGB & Hok). split; [|exact Hok]. unfold FGBe in *.
    apply (fl_bytes _ mem mem' _ _ HFGB MU). rewrite b7_tFG_len.
    intros x Hx. apply HWF. lia.
  - destruct HFS as (H104 & H112 & Hbody & Hab & HFI).
    split; [apply (SP 104 _ Hr9 HA0 HA1 E9 MU HWA); [lia | lia | exact H104]|].
    split; [apply (SP 112 _ Hr9 HA0 HA1 E9 MU HWA); [lia | lia | exact H112]|].
    split.
    { apply (fl_bytes _ mem mem' _ _ Hbody MU).
      pose proof (b7_fsbody_len (g_in g) (S j)) as Hbl.
      intros x Hx. apply HWB. lia. }
    split; [exact (b7_addr_munch W mem mem' (fr + 2880) 35 MU HWBsh Hab) | exact HFI].
Qed.

(* B7K reads the registers 9 (spills), 18, 21, 22, 23, 24 and memory. *)
Lemma b7_B7K_regs : forall g j phi fr regs regs' m,
  B7K g j phi fr regs m ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 21 = getr regs 21 ->
  getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 ->
  B7K g j phi fr regs' m.
Proof.
  intros g j phi fr regs regs' m
    ((Hj & H21 & HOUR) & H23 & H22 & Hp0 & Hp50 & Hfl & Hblk & H280 & H24 & H18 & H152 & Hg & Hph & Hlen & HLT &
     (S136 & S120 & S176))
    E9 E18 E21 E22 E23 E24.
  pose proof (b7_spill_regs regs regs' m) as K.
  unfold rg in H18, H21, H22, H23, H24.
  split; [split; [exact Hj | split; [unfold rg; rewrite E21; exact H21 | exact HOUR]]|].
  split; [unfold rg; rewrite E23; exact H23|]. split; [unfold rg; rewrite E22; exact H22|].
  split; [exact Hp0|]. split; [exact Hp50|]. split; [exact Hfl|]. split; [exact Hblk|].
  split; [exact (K _ _ E9 H280)|]. split; [unfold rg; rewrite E24; exact H24|].
  split; [unfold rg; rewrite E18; exact H18|]. split; [exact (K _ _ E9 H152)|].
  split; [exact Hg|]. split; [exact Hph|]. split; [exact Hlen|].
  split; [exact (b7_lt_regs g fr j regs regs' m HLT E9)|].
  split; [exact (K _ _ E9 S136)|]. split; [exact (K _ _ E9 S120) | exact (K _ _ E9 S176)].
Qed.

(* B7K across a run whose writes miss the spill area [A, A + 416), the live block [phi, phi + len_j) (the record
   at phi and its 32 block bytes at phi + 18 lie in it: 50 <= len_j and the length bound), the frame's
   [fr + 2624, fr + 2840) (OUR at fr + 2624, LT's records at fr + 2688 / fr + 2768) and, v1.9, LT's FIRST body
   [fr + 2880, fr + 2915) and its shadow bytes, and that keeps the registers 9, 18, 21-24. *)
Lemma b7_B7K_keep : forall g j phi fr regs regs' mem mem' W A,
  B7K g j phi fr regs mem -> munch W mem mem' ->
  rg regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 21 = getr regs 21 ->
  getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 ->
  (forall x, A <= x < A + 416 -> outside W x) ->
  (forall x, phi <= x < phi + flen g j -> outside W x) ->
  (forall x, fr + 2624 <= x < fr + 2840 -> outside W x) ->
  (forall x, fr + 2880 <= x < fr + 2915 -> outside W x) ->
  (forall i, 0 <= i < 35 -> outside W (shadow_addr (fr + 2880 + i))) ->
  B7K g j phi fr regs' mem'.
Proof.
  intros g j phi fr regs regs' mem mem' W A
    ((Hj & H21 & HOUR) & H23 & H22 & Hp0 & Hp50 & Hfl & Hblk & H280 & H24 & H18 & H152 & Hg & Hph & Hlen & HLT &
     (S136 & S120 & S176))
    MU H9 HA0 HA E9 E18 E21 E22 E23 E24 HWA HWphi HWfr HWB HWBsh.
  pose proof (b7_spill_keep regs regs' mem mem' W A) as K.
  unfold rg in H18, H21, H22, H23, H24.
  split.
  { split; [exact Hj|]. split; [unfold rg; rewrite E21; exact H21|].
    unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
    intros x Hx. apply HWfr. lia. }
  split; [unfold rg; rewrite E23; exact H23|]. split; [unfold rg; rewrite E22; exact H22|].
  split; [exact Hp0|]. split; [exact Hp50|]. split; [exact Hfl|].
  split.
  { eapply fl_bytes; [exact Hblk | exact MU |]. rewrite b7_tblk_len. intros x Hx. apply HWphi. lia. }
  split; [apply (K 280 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact H280]|].
  split; [unfold rg; rewrite E24; exact H24|].
  split; [unfold rg; rewrite E18; exact H18|].
  split; [apply (K 152 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact H152]|].
  split.
  { eapply fl_bytes; [exact Hg | exact MU |]. rewrite b7_tg_len. intros x Hx. apply HWphi. lia. }
  split.
  { eapply fl_bytes; [exact Hph | exact MU |]. intros x Hx. apply HWphi. lia. }
  split; [exact Hlen|].
  split; [exact (b7_lt_keep g fr j regs regs' mem mem' W A HLT MU E9 H9 HA0 HA HWA
                   (fun x Hx => HWfr x ltac:(lia)) HWB HWBsh)|].
  split; [apply (K 136 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact S136]|].
  split; [apply (K 120 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact S120]|].
  apply (K 176 _ H9 HA0 HA E9 MU HWA); [lia | lia | exact S176].
Qed.

(* ---- 0x82750 (F27's and F28b's exit) ---- *)

(* The 0x82750 body from FLSI, B7K and s9 = fr + 64: B7K's s6 = phi + 18 is FLS's
   `if t_big then phi + 18 else 0`, since B7K has 50 <= len_j (t_big = true, Z.leb_le); B7K carries FLS's
   turn-dependent facts (s2, the record at phi, the [A+152] / [A+280] spills) and LT. *)
Lemma b7_a826a4 : forall g j phi fr regs m,
  FLSI g j fr regs m -> B7K g j phi fr regs m -> rg regs 25 (fr + 64) ->
  LK g fr j regs m /\ FLS g j phi fr regs m /\ LT g fr j regs m.
Proof.
  intros g j phi fr regs m HI HK H25.
  destruct HK as (HLK & H23 & H22 & Hphi0 & Hphi50 & Hfl & Hblk & H280 & H24 & H18 & H152 & Hg & Hp & Hl & HLT &
                  HSPL).
  assert (Ebig : t_big (g_in g) j = true) by (unfold t_big; apply Z.leb_le; exact Hfl).
  split; [exact HLK|]. split; [|exact HLT].
  split; [exact HI|]. split; [exact H18|]. split; [rewrite Ebig; exact H22|].
  split; [exact H23|]. split; [exact H24|]. split; [exact H25|].
  split; [intros _; tauto|]. split; [exact H152 | exact H280].
Qed.
