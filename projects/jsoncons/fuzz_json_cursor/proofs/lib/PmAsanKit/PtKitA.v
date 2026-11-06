(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3B AxSymExec3Sound HeapIface HeapIfaceA FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibDefs PmLibDefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeapA CutL5A.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PTA.
Definition mem := (word -> option byte).

Section Agree.
Variable segs : list Segment.
Variable IC : PMLA.consts.
Variables (M M' : mem) (S : Z -> Prop).
Hypothesis AG : forall a, S a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Definition out (a n : Z) : Prop := 0 <= a /\ a + n <= 2 ^ 64 /\ forall i, a <= i < a + n -> S i.
Lemma out_sub : forall a n a' n', out a n -> a <= a' -> a' + n' <= a + n -> out a' n'.
Proof. intros a n a' n' (H0 & H1 & H2) Ha Hn. split; [lia|]. split; [lia|]. intros i Hi. apply H2. lia. Qed.
Lemma rdn_ag : forall a (n : nat), out a (Z.of_nat n) -> rdn segs M' (Z_to_bv 64 a) n = rdn segs M (Z_to_bv 64 a) n.
Proof. intros a n (H0 & H1 & H2). apply (CL5A.rdn_same segs); [exact H0 | exact H1 | intros i Hi; apply AG; apply H2; exact Hi]. Qed.
Lemma u64_ag : forall a v, out a 8 -> L5.u64_at segs M a v -> L5.u64_at segs M' a v.
Proof. intros a v Ho H. unfold L5.u64_at in *. rewrite (rdn_ag a 8 Ho). exact H. Qed.
Lemma u32_ag : forall a v, out a 4 -> L5.u32_at segs M a v -> L5.u32_at segs M' a v.
Proof. intros a v Ho H. unfold L5.u32_at in *. rewrite (rdn_ag a 4 Ho). exact H. Qed.
Lemma u8_ag : forall a v, out a 1 -> L5.u8_at segs M a v -> L5.u8_at segs M' a v.
Proof. intros a v Ho H. unfold L5.u8_at in *. rewrite (rdn_ag a 1 Ho). exact H. Qed.
Lemma cell_ag : forall a (n : nat) v, out a (Z.of_nat n) -> cell_is segs M a n v -> cell_is segs M' a n v.
Proof. intros a n v Ho H. unfold cell_is in *. rewrite (rdn_ag a n Ho). exact H. Qed.
Lemma bytes_ag : forall p bs, out p (Z.of_nat (length bs)) -> L5.bytes_at segs M p bs -> L5.bytes_at segs M' p bs.
Proof. intros p bs Ho H i Hi. apply u8_ag; [apply (out_sub _ _ _ _ Ho); lia | exact (H i Hi)]. Qed.
Lemma def_ag : forall a n, out a n -> L5.defined M a n -> L5.defined M' a n.
Proof. intros a n (H0 & H1 & H2) H i Hi. rewrite AG; [exact (H i Hi) | apply H2; lia]. Qed.
Lemma byte_ag : forall a v, S a -> byte_at M a v -> byte_at M' a v.
Proof. intros a v Ha H. unfold byte_at in *. rewrite (AG a Ha). exact H. Qed.
Lemma clear_ag : forall lo hi, (forall i, lo <= i < hi -> S i) -> L5.img_clear M lo hi -> L5.img_clear M' lo hi.
Proof. intros lo hi Ho H i Hi. rewrite (AG i (Ho i Hi)). exact (H i Hi). Qed.
Lemma lstr_short_nil_ag : forall o, out o 24 -> L5.lstr_short segs M o [] -> L5.lstr_short segs M' o [].
Proof.
  intros o Ho (H1 & H2 & H3 & H4). cbn [length] in *. split; [exact H1|]. split; [apply u8_ag; [apply (out_sub _ _ _ _ Ho); lia | exact H2]|].
  split; [intros i Hi; cbn in Hi; lia|]. apply u8_ag; [apply (out_sub _ _ _ _ Ho); cbn; lia | exact H4].
Qed.
Lemma str_long_ag : forall o cap p s, out o 24 -> out p cap -> PMLA.str_at segs M o (PML.SLong cap p s) -> PMLA.str_at segs M' o (PML.SLong cap p s).
Proof.
  intros o cap p s Ho Hp ((B & W0 & W8 & W16 & BS & NUL) & C8 & LT). split; [|split; assumption].
  split; [exact B|]. split; [apply u64_ag; [apply (out_sub _ _ _ _ Ho); lia | exact W0]|]. split; [apply u64_ag; [apply (out_sub _ _ _ _ Ho); lia | exact W8]|].
  split; [apply u64_ag; [apply (out_sub _ _ _ _ Ho); lia | exact W16]|].
  split; [apply bytes_ag; [apply (out_sub _ _ _ _ Hp); lia | exact BS] | apply u8_ag; [apply (out_sub _ _ _ _ Hp); lia | exact NUL]].
Qed.

Lemma parser_at_st : forall P ps st',
  (forall k n, 0 <= k -> k + n <= 272 -> (k + n <= 208 \/ 209 <= k) -> out (P + k) n) -> out (PML.ps_bptr ps) (PML.ps_bcap ps) -> out (PML.ps_sb ps) (PML.ps_scap ps) ->
  PMLA.parser_at segs IC M P ps -> L5.u8_at segs M' (P + 208) st' -> M' (Z_to_bv 64 (P + 208)) <> None ->
  PMLA.parser_at segs IC M' P (PML.PS st' (PML.ps_sst ps) (PML.ps_nst ps) (PML.ps_more ps) (PML.ps_done ps) (PML.ps_level ps) (PML.ps_stack ps) (PML.ps_sb ps) (PML.ps_scap ps)
                                      (PML.ps_bcap ps) (PML.ps_bptr ps) (PML.ps_buf ps) (PML.ps_win ps)).
Proof.
  intros P ps st' HP HB HS H HST HDEF. unfold PMLA.parser_at, PMLA.u64, PMLA.u32, PMLA.u8 in *. cbn [PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_done PML.ps_level PML.ps_stack PML.ps_sb PML.ps_scap PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_win].
  destruct H as (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30).
  assert (O : forall k n, 0 <= k -> k + n <= 272 -> (k + n <= 208 \/ 209 <= k) -> out (P + k) n) by exact HP.
  split; [apply u64_ag; [replace P with (P + 0) by lia; apply O; lia | exact A0]|].
  split; [apply u32_ag; [apply O; lia | exact A1]|].
  split; [apply u8_ag; [apply O; lia | exact A2]|]. split; [apply u8_ag; [apply O; lia | exact A3]|]. split; [apply u8_ag; [apply O; lia | exact A4]|].
  split; [apply u8_ag; [apply O; lia | exact A5]|]. split; [apply u8_ag; [apply O; lia | exact A6]|]. split; [apply u8_ag; [apply O; lia | exact A7]|].
  split; [apply u8_ag; [apply O; lia | exact A8]|].
  split; [apply lstr_short_nil_ag; [apply O; lia | exact A9]|]. split; [apply lstr_short_nil_ag; [apply O; lia | exact A10]|]. split; [apply lstr_short_nil_ag; [apply O; lia | exact A11]|].
  split; [apply u64_ag; [apply O; lia | exact A12]|]. split; [apply u64_ag; [apply O; lia | exact A13]|].
  split; [apply u32_ag; [apply O; lia | exact A14]|].
  split; [destruct (PML.ps_win ps) as [[p e]|]; [destruct A15 as (X & Y & Z); split; [apply u64_ag; [apply O; lia | exact X] | split; [apply u64_ag; [apply O; lia | exact Y] | exact Z]]
                                                 | destruct A15 as (X & Y); split; apply u64_ag; try (apply O; lia); assumption]|].
  split; [exact HST|]. split; [apply u8_ag; [apply O; lia | exact A17]|]. split; [apply u8_ag; [apply O; lia | exact A18]|].
  split; [apply u8_ag; [apply O; lia | exact A19]|]. split; [apply u8_ag; [apply O; lia | exact A20]|]. split; [apply u8_ag; [apply O; lia | exact A21]|].
  split; [apply u32_ag; [apply O; lia | exact A22]|].
  split; [apply str_long_ag; [apply O; lia | exact HB | exact A23]|]. split; [exact A24|].
  split; [apply u64_ag; [apply O; lia | exact A25]|]. split; [apply u64_ag; [apply O; lia | exact A26]|]. split; [apply u64_ag; [apply O; lia | exact A27]|].
  split; [apply bytes_ag; [apply (out_sub _ _ _ _ HS); lia | exact A28]|]. split; [exact A29|].
  intros i Hi. destruct (Z.eq_dec i 208) as [->|Hne]; [exact HDEF|]. destruct (O i 1 ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & G). rewrite AG; [exact (A30 i Hi) | apply G; lia].
Qed.

Lemma ec_at_ag : forall E code, out E 16 -> PMLA.ec_at segs IC M E code -> PMLA.ec_at segs IC M' E code.
Proof.
  intros E code HE (A & B & C). unfold PMLA.u32, PMLA.u64 in *. split; [apply u32_ag; [apply (out_sub _ _ _ _ HE); lia | exact A]|]. split; [apply def_ag; [exact HE | exact B]|].
  destruct C as [C|[C1 C2]]; [left; exact C | right; split; [exact C1 | apply u64_ag; [apply (out_sub _ _ _ _ HE); lia | exact C2]]].
Qed.

Lemma vis_at_ag : forall V, out V 8 -> (forall i, 0 <= i < 48 -> M (Z_to_bv 64 (V + i)) <> None -> M' (Z_to_bv 64 (V + i)) <> None) ->
  PMLA.vis_at segs IC M V -> PMLA.vis_at segs IC M' V.
Proof. intros V HV HG (H1 & H2). unfold PMLA.vis_at, PMLA.u64 in *. split; [exact (u64_ag _ _ HV H1) | intros i Hi; exact (HG i Hi (H2 i Hi))]. Qed.
Lemma shadow_zero_ag : forall p g, (forall j, 0 <= j < g -> S (HeapIfaceA.S p + j)) -> shadow_zero M p g -> shadow_zero M' p g.
Proof. intros p g Ho H j Hj. exact (byte_ag _ _ (Ho j Hj) (H j Hj)). Qed.

Lemma shadow_blk_ag : forall u n, 0 <= n -> (forall a, in_shadow_of u n a -> S a) -> u mod 8 = 0 -> shadow_blk M u n -> shadow_blk M' u n.
Proof.
  intros u n Hn Ho U8 (Z0 & P0). pose proof (Z.mul_div_le n 8 ltac:(lia)) as ND. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as NM. pose proof (Z_div_mod_eq_full n 8) as NE.
  assert (IN : forall j, 0 <= j -> 8 * j < n -> in_shadow_of u n (HeapIfaceA.S u + j)).
  { intros j J0 J1. apply (CL5A.blk_shadow_in u n); [exact U8 | lia |]. assert (j + 1 <= (n + 7) / 8) by (apply Z.div_le_lower_bound; lia). lia. }
  split.
  - intros j Hj. apply byte_ag; [apply Ho, IN; lia | exact (Z0 j Hj)].
  - intros NZ. apply byte_ag; [apply Ho, IN; [apply Z.div_pos; lia | lia] | exact (P0 NZ)].
Qed.
Lemma shadow_cont_ag : forall u n mid, 0 <= mid <= n -> u mod 8 = 0 -> (forall a, in_shadow_of u n a -> S a) -> shadow_cont M u n mid -> shadow_cont M' u n mid.
Proof.
  intros u n mid Hm U8 Ho H. apply (CL5A.shadow_cont_same M M' u n mid Hm U8); [|exact H]. intros a Ha. apply AG. apply Ho. exact Ha.
Qed.
Lemma parser_sh_ag : forall ps, 0 <= PML.ps_bcap ps -> 0 <= Z.of_nat (length (PML.ps_stack ps)) <= PML.ps_scap ps -> PML.ps_bptr ps mod 8 = 0 -> PML.ps_sb ps mod 8 = 0 ->
  (forall a, in_shadow_of (PML.ps_bptr ps) (PML.ps_bcap ps) a -> S a) -> (forall a, in_shadow_of (PML.ps_sb ps) (PML.ps_scap ps) a -> S a) ->
  PMLA.parser_sh M ps -> PMLA.parser_sh M' ps.
Proof. intros ps H0 H1 B8 S8 HB HS (X & Y). split; [exact (shadow_blk_ag _ _ H0 HB B8 X) | exact (shadow_cont_ag _ _ _ H1 S8 HS Y)]. Qed.
Lemma win_okA_ag : forall LBo ps, (forall ch a, In (ch, 16384) LBo -> ch <= a < ch + 16384 \/ in_shadow_of ch 16384 a -> S a) -> (forall ch, In (ch, 16384) LBo -> 0 <= ch /\ ch + 16384 <= 2 ^ 64 /\ ch mod 8 = 0) ->
  PMLA.win_okA M LBo ps -> PMLA.win_okA M' LBo ps.
Proof.
  intros LBo ps Ho Hr H. unfold PMLA.win_okA in *. destruct (PML.ps_win ps) as [[p e]|]; [|exact I]. destruct H as (ch & A & B & C & D & F). exists ch.
  destruct (Hr ch A) as (R0 & R1 & R8). split; [exact A|]. split; [exact B|]. split; [exact C|]. split.
  - apply def_ag; [|exact D]. split; [lia|]. split; [lia|]. intros i Hi. apply (Ho ch i A). left. lia.
  - apply (shadow_blk_ag ch 16384 ltac:(lia)); [intros a Ha; apply (Ho ch a A); right; exact Ha | exact R8 | exact F].
Qed.

Lemma ls_ok_ag : forall g, g <> PML.LS0 -> (forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a -> 0 <= a < 2 ^ 63 /\ S a) ->
  (forall a, PMLA.GLOC_GUARD IC <= a < PMLA.GLOC_GUARD IC + 1 \/ PMLA.GLOC_PTR IC <= a < PMLA.GLOC_PTR IC + 8 \/ PMLA.SYSCAT_GUARD IC <= a < PMLA.SYSCAT_GUARD IC + 1
             \/ PMLA.ERRCAT_GUARD IC <= a < PMLA.ERRCAT_GUARD IC + 2 \/ PMLA.ATEXIT_TAB IC <= a < PMLA.ATEXIT_TAB IC + 544 \/ a = PMLA.NEED_LOCKS IC
             \/ PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 \/ PMLA.CONVCAT_GUARD IC <= a < PMLA.CONVCAT_GUARD IC + 2 -> PMLA.in_foot IC a) ->
  PMLA.ls_ok segs IC g M -> PMLA.ls_ok segs IC g M'.
Proof.
  intros g Hg HS HF (IR & ((T1 & T2 & T3) & (Q1 & Q2)) & H).
  assert (OF : forall a n, 0 < n -> (forall i, a <= i < a + n -> PMLA.in_foot IC i) -> out a n).
  { intros a n Hn Hi. destruct (HS a (or_intror (Hi a ltac:(lia)))) as ((X0 & _) & _). destruct (HS (a + n - 1) (or_intror (Hi (a + n - 1) ltac:(lia)))) as ((_ & X1) & _).
    split; [lia|]. split; [lia|]. intros i Hii. exact (proj2 (HS i (or_intror (Hi i Hii)))). }
  assert (U8 : forall a v, (forall i, a <= i < a + 1 -> PMLA.in_foot IC i) -> L5.u8_at segs M a v -> L5.u8_at segs M' a v) by (intros a v Hf; apply u8_ag; apply OF; [lia | exact Hf]).
  assert (U64 : forall a v, (forall i, a <= i < a + 8 -> PMLA.in_foot IC i) -> L5.u64_at segs M a v -> L5.u64_at segs M' a v) by (intros a v Hf; apply u64_ag; apply OF; [lia | exact Hf]).
  assert (CE : forall a (n : nat) v, (0 < n)%nat -> (forall i, a <= i < a + Z.of_nat n -> PMLA.in_foot IC i) -> cell_is segs M a n v -> cell_is segs M' a n v)
    by (intros a n v Hn Hf; apply cell_ag; apply OF; [lia | exact Hf]).
  assert (TAB : forall i, PMLA.ATEXIT_TAB IC <= i < PMLA.ATEXIT_TAB IC + 544 -> PMLA.in_foot IC i) by (intros i Hi; apply HF; do 4 right; left; lia).
  split; [apply clear_ag; [intros i Hi; exact (proj2 (HS i (or_introl Hi))) | exact IR]|]. split.
  - split.
    + split; [apply CE; [lia | intros ii Hii; apply TAB; lia | exact T1]|]. split; [apply CE; [lia | intros ii Hii; apply TAB; lia | exact T2]|].
      destruct (PMLA.HS0 IC ++ PMLA.ls_atexit IC g) as [|h0 hs] eqn:EH.
      * destruct T3 as (X & Y). split; [apply CE; [lia | intros ii Hii; apply TAB; lia | exact X]|].
        destruct Y as [Y|[Y1 Y2]]; [left; apply CE; [lia | intros ii Hii; apply TAB; lia | exact Y] | right; split; [apply CE; [lia | intros ii Hii; apply TAB; lia | exact Y1] | apply CE; [lia | intros ii Hii; apply TAB; lia | exact Y2]]].
      * destruct T3 as (X0 & X1 & X2 & X3 & X4). split; [exact X0|]. split; [apply CE; [lia | intros ii Hii; apply TAB; lia | exact X1]|]. split; [apply CE; [lia | intros ii Hii; apply TAB; lia | exact X2]|].
        split; [apply CE; [lia | intros ii Hii; apply TAB; lia | exact X3]|]. intros i f a Hn. destruct (X4 i f a Hn) as (Y1 & Y2).
        assert (Hi : Z.of_nat i < 32) by (pose proof (nth_error_Some (h0 :: hs) i) as G; rewrite Hn in G; assert ((i < length (h0 :: hs))%nat) by (apply G; discriminate); lia).
        split; [apply CE; [lia | intros ii Hii; apply TAB; lia | exact Y1] | apply CE; [lia | intros ii Hii; apply TAB; lia | exact Y2]].
    + split; [apply CE; [lia | intros i Hi; apply HF; do 5 right; left; lia | exact Q1] | apply CE; [lia | intros i Hi; apply HF; do 6 right; left; lia | exact Q2]].
  - assert (LD : PMLA.loc_done segs IC M -> PMLA.loc_done segs IC M').
    { intros (X & Y & Z). unfold PMLA.u8, PMLA.u64 in *. split; [apply U8; [intros i Hi; apply HF; left; lia | exact X]|].
      split; [apply U64; [intros i Hi; apply HF; right; left; lia | exact Y] | apply U8; [intros i Hi; apply HF; right; right; left; lia | exact Z]]. }
    assert (EG : forall b, PMLA.errcat_guard segs IC M b -> PMLA.errcat_guard segs IC M' b).
    { intros b (X & Y). unfold PMLA.u8 in *. split; apply U8; try assumption; intros i Hi; apply HF; do 3 right; left; lia. }
    assert (CG : forall b, PMLA.convcat_guard segs IC M b -> PMLA.convcat_guard segs IC M' b).
    { intros b (X & Y). unfold PMLA.u8 in *. split; apply U8; try assumption; intros i Hi; apply HF; do 7 right; lia. }
    destruct g; [exfalso; apply Hg; reflexivity | ..]; destruct H as (X & Y & Z); (split; [apply LD; exact X | split; [apply EG; exact Y | apply CG; exact Z]]).
Qed.
End Agree.

Lemma sltu_sub_ne : forall Ex x c, CL5A.uv Ex (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB x (ELit c)) (ELit 1)) = 0 -> 0 <= c < 2 ^ 64 -> CL5A.uv Ex x <> c.
Proof.
  intros Ex x c H Hc Heq. unfold CL5A.uv in H. cbn [edenot] in H. rewrite u_sltu64, u_sub64 in H. cbn [edenot] in H. rewrite u_lit64 in H. unfold two64 in H.
  rewrite (Z.mod_small c) in H by lia. unfold CL5A.uv in Heq. rewrite Heq, Z.sub_diag in H. change (bv_unsigned (Z_to_bv 64 1)) with 1 in H. rewrite Z.mod_0_l in H by lia. cbn in H. discriminate H.
Qed.

Lemma stksh_mono : forall ar (M : mem) sp scr sp' scr', PMLA.stksh ar M sp scr -> (sp - scr) mod 8 = 0 -> (sp' - scr') mod 8 = 0 -> sp - scr <= sp' - scr' ->
  PMLA.stksh ar M sp' scr'.
Proof.
  intros ar M sp scr sp' scr' H A1 A2 LE. unfold PMLA.stksh in *. remember (sp - scr) as a eqn:Ea. remember (sp' - scr') as a' eqn:Ea'.
  remember (Z.max (ar_sptop ar) (ar_stack_top ar)) as mx eqn:Emx. clear Ea Ea' Emx.
  apply Z.mod_divide in A1; [|lia]. destruct A1 as [q Hq]. assert (D : exists k, a' = a + k * 8) by (apply Z.mod_divide in A2; [|lia]; destruct A2 as [q' Hq']; exists (q' - q); lia).
  destruct D as [k Hk]. assert (K0 : 0 <= k) by lia. subst a'. intros j Hj.
  rewrite (CL5A.S_add_al a (k * 8) ltac:(rewrite Hq; apply Z_mod_mult)). rewrite Z_div_mult by lia. rewrite <- Z.add_assoc. apply H.
  split; [lia|]. replace (mx - a) with (k * 8 + (mx - (a + k * 8))) by lia. rewrite Z.div_add_l by lia. lia.
Qed.
Lemma stksh_ag : forall ar (M M' : mem) sp scr, (forall a, HeapIfaceA.S (sp - scr) <= a < HeapIfaceA.S (sp - scr) + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - scr)) / 8 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  PMLA.stksh ar M sp scr -> PMLA.stksh ar M' sp scr.
Proof.
  intros ar M M' sp scr AG H. unfold PMLA.stksh in *. apply (CL5A.shadow_zero_same M M'); [|exact H]. intros j Hj. apply AG. lia.
Qed.

Lemma stksh_rng : forall ar sp scr a, ahl_ceil ar <= sp - scr -> (sp - scr) mod 8 = 0 -> ahl_ceil ar mod 8 = 0 -> ar_sptop ar <= 2 ^ 47 -> ar_stack_top ar <= 2 ^ 47 -> 0 <= ahl_ceil ar ->
  HeapIfaceA.S (sp - scr) <= a < HeapIfaceA.S (sp - scr) + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - scr)) / 8 ->
  0 <= a < 2 ^ 64 /\ in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a.
Proof.
  intros ar sp scr a H1 A1 A2 T1 T2 C0 Ha. unfold in_shadow_of. replace (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) with (2 ^ 47 - 1) by lia. unfold HeapIfaceA.S in *.
  change ((2 ^ 47 - 1) / 8) with 17592186044415.
  pose proof (CL5A.div8_le (ahl_ceil ar) (sp - scr) H1) as G1.
  apply Z.mod_divide in A1; [|lia]. destruct A1 as [q Hq].
  assert (G2 : (sp - scr) / 8 + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - scr)) / 8 <= 2 ^ 44).
  { rewrite Hq. rewrite Z_div_mult by lia.
    assert (X : (Z.max (ar_sptop ar) (ar_stack_top ar) - q * 8) / 8 <= (2 ^ 47 - q * 8) / 8) by (apply Z.div_le_mono; lia).
    replace (2 ^ 47 - q * 8) with ((2 ^ 44 - q) * 8) in X by lia. rewrite Z_div_mult in X by lia. lia. }
  assert (G0 : 0 <= ahl_ceil ar / 8) by (apply Z.div_pos; lia). unfold SB in *. lia.
Qed.

Section Lit.
Variable segs : list Segment.
Variable IC : PMLA.consts.

Lemma defined_bytes : forall (M : mem) p (n : nat), L5.defined M p (Z.of_nat n) ->
  exists bs, length bs = n /\ L5.bytes_at segs M p bs.
Proof.
  intros M p n HD.
  set (f := fun i : nat => match M (Z_to_bv 64 (p + Z.of_nat i)) with Some b => bv_unsigned b | None => 0 end).
  exists (map f (seq 0 n)). split; [rewrite length_map, length_seq; reflexivity|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  rewrite (nth_indep (map f (seq 0 n)) (n:=i) 0 (f 0%nat) ltac:(rewrite length_map, length_seq; exact Hi)). rewrite map_nth. rewrite (seq_nth 0%nat 0%nat Hi). cbn [Nat.add].
  unfold f. destruct (M (Z_to_bv 64 (p + Z.of_nat i))) as [b|] eqn:Hb; [|exfalso; exact (HD (Z.of_nat i) ltac:(lia) Hb)].
  unfold L5.u8_at. cbn [rdn]. rewrite Hb. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Variables (M M' : mem) (S : Z -> Prop).
Hypothesis AG : forall a, S a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).

Lemma parser_at_lit : forall P ps st' (more' : bool) p' p e,
  PML.ps_win ps = Some (p, e) -> p' <= e ->
  out S P 168 -> out S (P + 176) 8 -> out S (P + 192) 8 -> out S (P + 209) 2 -> out S (P + 212) 60 ->
  out S (PML.ps_bptr ps) (PML.ps_bcap ps) -> out S (PML.ps_sb ps) (PML.ps_scap ps) ->
  PMLA.parser_at segs IC M P ps ->
  L5.u64_at segs M' (P + 200) p' -> L5.u8_at segs M' (P + 208) st' -> L5.u8_at segs M' (P + 211) (PML.b2z more') ->
  (forall i, 0 <= i < 272 -> M' (Z_to_bv 64 (P + i)) <> None) ->
  PMLA.parser_at segs IC M' P (PML.PS st' (PML.ps_sst ps) (PML.ps_nst ps) more' (PML.ps_done ps) (PML.ps_level ps) (PML.ps_stack ps) (PML.ps_sb ps) (PML.ps_scap ps)
                               (PML.ps_bcap ps) (PML.ps_bptr ps) (PML.ps_buf ps) (Some (p', e))).
Proof.
  intros P ps st' more' p' p e HW HPE O0 O1 O2 O3 O4 HB HS H H200 H208 H211 HDEF. unfold PMLA.parser_at, PMLA.u64, PMLA.u32, PMLA.u8 in *.
  cbn [PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_done PML.ps_level PML.ps_stack PML.ps_sb PML.ps_scap PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_win].
  destruct H as (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30).
  rewrite HW in A15. destruct A15 as (_ & A15 & _).
  split; [apply (u64_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O0); lia | exact A0]|].
  split; [apply (u32_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O0); lia | exact A1]|].
  split; [apply (u8_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O0); lia | exact A2]|]. split; [apply (u8_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O0); lia | exact A3]|].
  split; [apply (u8_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O0); lia | exact A4]|]. split; [apply (u8_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O0); lia | exact A5]|].
  split; [apply (u8_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O0); lia | exact A6]|]. split; [apply (u8_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O0); lia | exact A7]|].
  split; [apply (u8_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O0); lia | exact A8]|].
  split; [apply (lstr_short_nil_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O0); lia | exact A9]|]. split; [apply (lstr_short_nil_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O0); lia | exact A10]|].
  split; [apply (lstr_short_nil_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O0); lia | exact A11]|].
  split; [apply (u64_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O0); lia | exact A12]|]. split; [apply (u64_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O0); lia | exact A13]|].
  split; [apply (u32_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O0); lia | exact A14]|].
  split; [split; [exact H200 | split; [apply (u64_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O2); lia | exact A15] | exact HPE]]|].
  split; [exact H208|]. split; [apply (u8_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O3); lia | exact A17]|]. split; [apply (u8_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O3); lia | exact A18]|].
  split; [exact H211|]. split; [apply (u8_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O4); lia | exact A20]|]. split; [apply (u8_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O4); lia | exact A21]|].
  split; [apply (u32_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O4); lia | exact A22]|].
  split; [apply (str_long_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O4); lia | exact HB | exact A23]|]. split; [exact A24|].
  split; [apply (u64_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O4); lia | exact A25]|]. split; [apply (u64_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O4); lia | exact A26]|].
  split; [apply (u64_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ O4); lia | exact A27]|].
  split; [apply (bytes_ag segs M M' S AG); [apply (out_sub _ _ _ _ _ HS); lia | exact A28]|]. split; [exact A29|].
  intros i Hi. exact (HDEF i Hi).
Qed.

Lemma win_okA_adv : forall LBo ps ps' p e p', PML.ps_win ps = Some (p, e) -> PML.ps_win ps' = Some (p', e) -> p <= p' <= e ->
  (forall ch a, In (ch, 16384) LBo -> ch <= a < ch + 16384 \/ in_shadow_of ch 16384 a -> S a) -> (forall ch, In (ch, 16384) LBo -> 0 <= ch /\ ch + 16384 <= 2 ^ 64 /\ ch mod 8 = 0) ->
  PMLA.win_okA M LBo ps -> PMLA.win_okA M' LBo ps'.
Proof.
  intros LBo ps ps' p e p' HW HW' HPE Ho Hr H. unfold PMLA.win_okA in *. rewrite HW in H. rewrite HW'. destruct H as (ch & A & B & C & D & F). exists ch.
  destruct (Hr ch A) as (R0 & R1 & R8). split; [exact A|]. split; [lia|]. split; [exact C|]. split.
  - apply (def_ag M M' S AG); [split; [lia|]; split; [lia|]; intros i Hi; apply (Ho ch i A); left; lia|]. apply (L5.defined_sub M p (e - p)); [exact D | lia | lia].
  - apply (shadow_blk_ag M M' S AG ch 16384 ltac:(lia)); [intros a Ha; apply (Ho ch a A); right; exact Ha | exact R8 | exact F].
Qed.
End Lit.
End PTA.
