(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec StoreOk AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec FP Image RunConst SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import AsanEmbed AsanCtrl.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegLin SegTmpl SegGhost SegCall SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AGLUE AGLX AHMB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import ST.
Open Scope Z_scope.

Module AGLRB.
Section RT.
Context {rc : runConstT}.
Variable AI : AMallocIface.
Notation CI := (aci AI).

(* [comment removed for export] *)
Lemma classic_fake : forall LB y, (exists cls A n, In (mkABlock (ABFake cls) A n) LB /\ A <= y < A + n) \/
  (forall cls A n, In (mkABlock (ABFake cls) A n) LB -> ~ (A <= y < A + n)).
Proof.
  intros LB y. induction LB as [|[k A n] LB IH].
  - right. intros cls A n [].
  - destruct IH as [(cls & A' & n' & Hin & Hy)|Hn].
    + left. exists cls, A', n'. split; [right; exact Hin | exact Hy].
    + destruct k as [p|cls].
      * right. intros cls A' n' [Heq|Hin]; [discriminate Heq | exact (Hn cls A' n' Hin)].
      * destruct (Z_le_gt_dec A y) as [H1|H1]; [destruct (Z_lt_ge_dec y (A + n)) as [H2|H2]|].
        -- left. exists cls, A, n. split; [left; reflexivity | lia].
        -- right. intros cls' A' n' [Heq|Hin]; [injection Heq as <- <- <-; lia | exact (Hn cls' A' n' Hin)].
        -- right. intros cls' A' n' [Heq|Hin]; [injection Heq as <- <- <-; lia | exact (Hn cls' A' n' Hin)].
Qed.

(* [comment removed for export] *)
Lemma in_stack_win : forall E spc x, bv_unsigned (edenot E spc) <= 2^47 ->
  SC.in_win E (SP.stack_win spc) x -> bv_unsigned (edenot E spc) <= x < 2^47.
Proof.
  intros E spc x Hs Hin. unfold SC.in_win, SP.stack_win, SG.win_den in Hin. cbn [edenot] in Hin.
  rewrite u_sub64, u_lit64a in Hin. rewrite (Z.mod_small (2^47) (2^64)) in Hin by lia.
  pose proof (bv_unsigned_in_range 64 (edenot E spc)) as R.
  rewrite (Z.mod_small (2^47 - bv_unsigned (edenot E spc)) (2^64)) in Hin by lia. lia.
Qed.

(* [comment removed for export] *)
Definition rt_pres (LB : list ablock) (sp : Z) (m m' : amem) : Prop :=
  aheap_pres CI LB sp m m' /\ (forall a, in_block LB a -> m' (wa (shad a)) = m (wa (shad a))).

(* [comment removed for export] *)
Definition pres_obj (LB : list ablock) (sp : Z) (E : env) (w : SC.wn) : Prop :=
  forall x, SC.in_win E w x -> 0 <= x < 2^64 -> aclient_addr CI LB sp x.
Definition pres_sh (LB : list ablock) (sp : Z) (E : env) (w : SC.wn) : Prop :=
  forall x, SC.in_win E w x -> 0 <= x < 2^64 -> aclient_addr CI LB sp x \/ (exists y, in_block LB y /\ x = shad y).

Lemma rt_keep_of_pres : forall LB sp m m' E PR PRW,
  rt_pres LB sp m m' ->
  Forall (pres_obj LB sp E) PRW -> Forall (pres_sh LB sp E) PR ->
  AGL.rt_keep bsegs E PR PRW m m'.
Proof.
  intros LB sp m m' E PR PRW (HP & HB) HW HR. split.
  - intros x (w & Hw & Hin). pose proof (bv_unsigned_in_range 64 x) as Rx; change (bv_modulus 64) with (2^64) in Rx.
    destruct (proj1 (Forall_forall _ _) HR w Hw (bv_unsigned x) Hin ltac:(lia)) as [Ha|(y & Hy & Ex)].
    + destruct (HP (bv_unsigned x) ltac:(lia) Ha) as [E1 _]. unfold wa in E1. rewrite Z_to_bv_bv_unsigned in E1. exact E1.
    + specialize (HB y Hy). rewrite <- Ex in HB. unfold wa in HB. rewrite Z_to_bv_bv_unsigned in HB. exact HB.
  - intros x (w & Hw & Hin). pose proof (bv_unsigned_in_range 64 x) as Rx; change (bv_modulus 64) with (2^64) in Rx.
    pose proof (proj1 (Forall_forall _ _) HW w Hw (bv_unsigned x) Hin ltac:(lia)) as Ha.
    destruct (HP (bv_unsigned x) ltac:(lia) Ha) as [_ W1]. unfold wa in W1. rewrite Z_to_bv_bv_unsigned in W1. exact W1.
Qed.

(* [comment removed for export] *)
Definition pres_cls (LB : list ablock) (sp bot x : Z) : Prop :=
  (sp <= x < 2^47) \/ (exists a, bot <= a < 2^47 /\ x = shad a) \/ AHMB.hmA AI LB x
  \/ in_ranges CI x \/ (exists a, in_ranges CI a /\ x = shad a).
Definition pres_win (LB : list ablock) (sp bot : Z) (E : env) (w : SC.wn) : Prop :=
  forall x, SC.in_win E w x -> 0 <= x < 2^64 -> pres_cls LB sp bot x.

(* [comment removed for export] *)
Definition shw (LB : list ablock) (m' : amem) : Prop :=
  forall y, in_block LB y -> (forall cls A n, In (mkABlock (ABFake cls) A n) LB -> ~ (A <= y < A + n)) ->
    wview bsegs m' (wa (shad y)) <> None.

Lemma rt_keep_cls : forall LB sp bot m m' E PR,
  rt_pres LB sp m m' -> shw LB m' -> ATOP <= bot -> sp <= 2^47 ->
  Forall (pres_win LB sp bot E) PR ->
  AGL.rt_keep bsegs E PR PR m m'.
Proof.
  intros LB sp bot m m' E PR (HP & HB) HW Hbot Hsp HR.
  assert (CL : forall x : word, SC.in_PR E (Some PR) (bv_unsigned x) ->
            aclient_addr CI LB sp (bv_unsigned x) \/ (exists y, in_block LB y /\ (forall cls A n, In (mkABlock (ABFake cls) A n) LB -> ~ (A <= y < A + n))
                                                              /\ bv_unsigned x = shad y)).
  { intros x (w & Hw & Hin). pose proof (bv_unsigned_in_range 64 x) as Rx; change (bv_modulus 64) with (2^64) in Rx.
    destruct (proj1 (Forall_forall _ _) HR w Hw (bv_unsigned x) Hin ltac:(lia)) as [H|[(a & Ha & ->)|[[H|(y & Hy & ->)]|[H|(a & Ha & ->)]]]].
    - left. left. exact H.
    - left. right. right. right. exists a. split; [left; lia | reflexivity].
    - left. destruct H as [H|[H|[H|H]]]; [lia | right; left; exact H | right; right; left; exact H | right; right; right; exact H].
    - destruct (classic_fake LB y) as [(cls & A & n & Hin' & Hy')|Hn].
      + left. right. right. right. exists y. split; [right; right; exists cls, A, n; split; [exact Hin'|lia] | reflexivity].
      + right. exists y. split; [exact Hy|]. split; [exact Hn | reflexivity].
    - left. right. left. exact H.
    - left. right. right. right. exists a. split; [right; left; exact Ha | reflexivity]. }
  split.
  - intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx; change (bv_modulus 64) with (2^64) in Rx.
    destruct (CL x Hx) as [Ha|(y & Hy & _ & Ex)].
    + destruct (HP (bv_unsigned x) ltac:(lia) Ha) as [E1 _]. unfold wa in E1. rewrite Z_to_bv_bv_unsigned in E1. exact E1.
    + specialize (HB y Hy). rewrite <- Ex in HB. unfold wa in HB. rewrite Z_to_bv_bv_unsigned in HB. exact HB.
  - intros x Hx Hv. pose proof (bv_unsigned_in_range 64 x) as Rx; change (bv_modulus 64) with (2^64) in Rx.
    destruct (CL x Hx) as [Ha|(y & Hy & Hn & Ex)].
    + destruct (HP (bv_unsigned x) ltac:(lia) Ha) as [_ W1]. unfold wa in W1. rewrite Z_to_bv_bv_unsigned in W1. exact (W1 Hv).
    + pose proof (HW y Hy Hn) as W2. rewrite <- Ex in W2. unfold wa in W2. rewrite Z_to_bv_bv_unsigned in W2. exact W2.
Qed.

(* [comment removed for export] *)
Lemma shw_of_aheap : forall L R st LB LB' m,
  AHEAP AI L R st LB' m -> (forall b, In b LB -> In b LB') -> shw LB m.
Proof.
  intros L R st LB LB' m AH HS y (b & Hb & Hy) Hn. destruct b as [[p|cls] A n]; cbn [ab_addr ab_size] in Hy.
  - destruct (AI_block AI L R st LB' m p A n AH (HS _ Hb)) as (_ & _ & _ & _ & _ & _ & _ & (RLO & RHI & H1 & H2 & H3 & H4 & _ & (W0 & W1 & W2))).
    assert (Hi : 0 <= shad y - shad RLO < shlen (RHI - RLO)).
    { unfold shad, shlen. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear - H1 H3 H4 Hy. Z.div_mod_to_equations. lia. }
    specialize (W2 (shad y - shad RLO) Hi). replace (shad RLO + (shad y - shad RLO)) with (shad y) in W2 by lia. exact W2.
  - exfalso. exact (Hn cls A n Hb Hy).
Qed.

(* [comment removed for export] *)
Lemma fresh_apart : forall L R st LB m cls F SZ A n,
  AHEAP AI L R st (mkABlock (ABFake cls) F SZ :: LB) m ->
  (forall z, A <= z < A + n -> AHMB.hmA AI LB z) ->
  AIMG_HI <= A -> (A + n <= 0x7fff7000 \/ 0x7fff7000 + 0x100000001000 <= A) -> 0 < SZ ->
  A + n <= F \/ F + SZ <= A \/ n <= 0.
Proof.
  intros L R st LB m cls F SZ A n AH HA Himg Hband HSZ.
  destruct (Z_le_gt_dec n 0) as [Hn|Hn]; [right; right; exact Hn|].
  destruct (Z_le_gt_dec (A + n) F) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (F + SZ) A) as [H2|H2]; [right; left; exact H2|].
  exfalso. set (z := Z.max A F).
  pose proof atop_range as AT.
  assert (Hz : A <= z < A + n) by (unfold z; lia).
  assert (HzF : F <= z < F + SZ) by (unfold z; lia).
  (* [comment removed for export] *)
  assert (SHB : forall a', 0 <= a' < 2^47 -> z <> shad a').
  { intros a' Ha' E. unfold shad, ASHOFF in E. rewrite Z.shiftr_div_pow2 in E by lia. change (2^3) with 8 in E.
    assert (0 <= a' / 8 < 2^44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia. }
  destruct (HA z Hz) as [Hc | (y & Hy & Ez)].
  - destruct Hc as [H|[H|[H|(a' & Ha' & Ez)]]].
    + lia.
    + destruct H as (iv & Hiv & Hin). pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. lia.
    + destruct H as (b & Hb & Hin).
      assert (ND : ~ In (mkABlock (ABFake cls) F SZ) LB).
      { pose proof (AI_blocks_nodup AI L R st _ m AH) as N. inversion N; assumption. }
      assert (NE : mkABlock (ABFake cls) F SZ <> b) by (intros <-; exact (ND Hb)).
      destruct (AI_blocks_disjoint AI L R st _ m _ _ AH (or_introl eq_refl) (or_intror Hb) NE) as [D|D]; cbn [ab_addr ab_size] in D; lia.
    + apply (SHB a'); [| exact Ez].
      destruct Ha' as [H|[(iv & Hiv & Hin)|(c & A' & n' & Hin & H)]].
      * lia.
      * pose proof (AI_aci_img AI iv Hiv). pose proof (AI_aci_lo AI iv Hiv). unfold AIMG_HI in *. lia.
      * pose proof (AI_block_bounds AI L R st _ m _ AH (or_intror Hin)) as (B0 & B1 & B2). cbn [ab_addr ab_size] in B0, B1, B2.
        unfold AIMG_HI in B0. lia.
  - destruct Hy as (b & Hb & Hin). pose proof (AI_block_bounds AI L R st _ m _ AH (or_intror Hb)) as (B0 & B1 & B2).
    unfold AIMG_HI in B0. apply (SHB y); [lia | exact Ez].
Qed.

(* [comment removed for export] *)
Lemma acr_mono : forall LB LB' SP A n, aclient_range CI LB SP A n -> (forall b, In b LB -> In b LB') -> aclient_range CI LB' SP A n.
Proof.
  intros LB LB' SP A n H HL.
  destruct H as [[H|[H|(c & FA & fn & Hin & H)]]|[(b & Hb & H)|[H|[H|(c & FA & fn & Hin & H)]]]].
  - left. left. exact H.
  - left. right. left. exact H.
  - left. right. right. exists c, FA, fn. split; [apply HL; exact Hin | exact H].
  - right. left. exists b. split; [apply HL; exact Hb | exact H].
  - right. right. left. exact H.
  - right. right. right. left. exact H.
  - right. right. right. right. exists c, FA, fn. split; [apply HL; exact Hin | exact H].
Qed.
Lemma acr_stack : forall LB SP A n, SP <= A -> A + n <= 2^47 -> aclient_range CI LB SP A n.
Proof. intros. left. left. lia. Qed.
Lemma acr_fake : forall LB SP cls FA fn A n, In (mkABlock (ABFake cls) FA fn) LB -> FA <= A -> A + n <= FA + fn ->
  aclient_range CI LB SP A n.
Proof. intros. left. right. right. exists cls, FA, fn. split; [assumption | lia]. Qed.
Lemma acr_fake_shadow : forall LB SP cls FA fn A n, In (mkABlock (ABFake cls) FA fn) LB -> FA <= 8 * (A - ASHOFF) ->
  8 * (A - ASHOFF) + 8 * n <= FA + fn -> aclient_range CI LB SP A n.
Proof. intros. right. right. right. right. exists cls, FA, fn. split; [assumption | lia]. Qed.

End RT.

(* [comment removed for export] *)
Lemma unk_of_wr : forall E (M : amem) a n, flat E a (elenZ E n) -> 0x671000 <= estart E a ->
  wr_at bsegs M (estart E a) (elenZ E n) -> kentry_ok bsegs E M (KUnk a n).
Proof.
  intros E M a n Hfl H0 (W0 & W1 & W2). apply AGX.kx_unk; [exact Hfl|]. intros i Hi. specialize (W2 i Hi).
  destruct Hfl as (F1 & F2 & F3 & F4).
  rewrite ref_wview_overlay in W2 by (unfold wa; rewrite u_small by lia; lia). exact W2.
Qed.
(* [comment removed for export] *)
Lemma zero_cellsN : forall m A k, rw_cells bsegs m A (repeat (C8 (Z_to_bv 64 0)) k) -> 0x671000 <= A -> A + 8 * Z.of_nat k < 2^64 ->
  forall i, 0 <= i < 8 * Z.of_nat k -> m (Z_to_bv 64 (A + i)) = Some (Z_to_bv 8 0).
Proof.
  intros m A k HC H1 H2 i Hi. pose proof (rw_cells_bytes_at _ _ _ _ HC) as (_ & _ & HB).
  assert (EQ : forall k', cells_bytes (repeat (C8 (Z_to_bv 64 0)) k') = repeat (Z_to_bv 8 0) (8 * k')).
  { induction k' as [|k' IH]; [reflexivity|]. cbn [repeat cells_bytes cbytes]. rewrite IH.
    replace (8 * S k')%nat with (8 + 8 * k')%nat by lia. rewrite repeat_app. f_equal. }
  rewrite EQ in HB. rewrite repeat_length in HB. specialize (HB (Z.to_nat i) ltac:(lia)).
  rewrite nth_error_repeat in HB by lia. rewrite Z2Nat.id in HB by lia.
  rewrite ref_mrd_overlay in HB by (unfold wa; rewrite u_small by lia; lia). exact HB.
Qed.
End AGLRB.
