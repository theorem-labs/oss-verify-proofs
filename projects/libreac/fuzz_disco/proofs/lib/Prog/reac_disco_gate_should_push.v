From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import CtrlParsed disco_classify_c GateModel bcmp_c
  reac_disco_gate_should_push_c.
Import ListNotations.
Open Scope Z_scope.

Section Plain.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (lo g s now : Z) (G S : list byte).
Hypothesis Hnow : 0 <= now < 2 ^ 64.
Hypothesis Hg0 : 0 < g.
Hypothesis Hg264 : g + 264 <= 2 ^ 64.
Hypothesis HGok : gate_ok G.
Hypothesis Hs0 : 0 < s.
Hypothesis Hs24 : s + 24 <= 2 ^ 64.
Hypothesis HSl : length S = 24%nat.
Hypothesis Dgs : g + 264 <= s \/ s + 24 <= g.
Hypothesis Dgk : g + 264 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= g.
Hypothesis Dsk : s + 24 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= s.
Hypothesis Hlo : 0 <= lo.
Hypothesis Hsp : lo + 64 <= bv_unsigned sp.
Hypothesis Hsp1 : bv_unsigned sp <= 2 ^ 64.

Definition MF (m : word -> option byte) (B : list byte) : Prop :=
  rw_cells rsegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  stk rsegs m lo (bv_unsigned sp + -64) /\
  munch [(bv_unsigned sp - 64, bv_unsigned sp); (g, g + 264)] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\
  rw_cells rsegs m g [CB 264 B] /\ bytes_at rsegs m s S.

Lemma epi : forall m B r rx x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
  MF m B -> gate_model G S now = (B, r) ->
  evt rsegs (gsp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo g s now G S)
    (MS (mkR rx (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x15548) fc None m (seg_rom rsegs)).
Proof.
  intros m B r rx x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31
    (FR & ST & MU & WM & MI & HG & HS) EM.
  step. step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold gsp_post, REAC_DISCO_GATE_SHOULD_PUSH_K. rewrite EM. cbn [fst snd].
  pose proof (gate_model_ok G S now HGok HSl) as OK. rewrite EM in OK. cbn [fst] in OK.
  do 14 eexists; eexists; split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact HG|]. split; [exact OK|exact HS].
Qed.

Ltac mk_mf := unfold MF; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); eassumption.

Lemma st_last : forall m B i e rx x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31,
  (i < 8)%nat -> e = g + 32 * Z.of_nat i -> MF m B ->
  gate_model G S now = (upd_bytes B (32 * i + 24) (le8 (Z_to_bv 64 now)), 1) ->
  evt rsegs (gsp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo g s now G S)
    (MS (mkR rx (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 now) x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 e) x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x15540) fc None m (seg_rom rsegs)).
Proof.
  intros m B i e rx x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31
    Hi He (FR & ST & MU & WM & MI & HG & HS) EM.
  gstep_st HG (32 * i + 24)%nat 8%nat.
  step.
  eapply epi; [ | exact EM ]. mk_mf.
Qed.

Lemma ret0 : forall m rx x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
  MF m G -> gate_model G S now = (G, 0) ->
  evt rsegs (gsp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo g s now G S)
    (MS (mkR rx (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1551c) fc None m (seg_rom rsegs)).
Proof.
  intros m rx x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 HM EM.
  step. step. eapply epi; [exact HM | exact EM].
Qed.

Local Notation QP := (gsp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo g s now G S).
Local Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -64)).
Local Notation GF i := (gfind G (fld S 0 6) 0 (Z.to_nat (gn G)) = Some i).

Ltac ffacts Hf i :=
  pose proof HGok as (HL & Hn & _); destruct (gfind_Some _ _ _ _ _ Hf) as [Ri _];
  assert (Hi : (i < 8)%nat) by lia.

Lemma edge_tail : forall m B1 i e rx x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x28 x29 x30 x31,
  GF i -> gedge G S i = true -> e = g + 32 * Z.of_nat i ->
  B1 = (if fu S 8 4 =? 0 then G else upd_bytes G (32 * i + 8) (fld S 8 4)) -> MF m B1 ->
  evt rsegs QP
    (MS (mkR rx SPF gp tp x5 x6 x7 (Z_to_bv 64 now) (Z_to_bv 64 s) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 e) x19 (Z_to_bv 64 (gdk S)) x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1552c) fc None m (seg_rom rsegs)).
Proof.
  intros m B1 i e rx x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x28 x29 x30 x31 Hf Hed He EB
    (FR & ST & MU & WM & MI & HG & HS).
  subst B1. ffacts Hf i.
  pose proof (gm_edge G S now i Hf Hed) as EM.
  pose proof (fb_rng S 16) as R16. pose proof (gdk_rng S) as Rdk.
  sld HS 16%nat 1%nat.
  change (zxb (nth 16 S (zb 0))) with (Z_to_bv 64 (fb S 16)).
  step. rewrite (eqb_lit (fb S 16) 0) by lia. brc E16.
  - step. rewrite (lts_lit (gdk S) 0) by lia. brc Edk.
    + eapply st_last; [exact Hi | exact He | mk_mf | rewrite EM; rewrite ?E16, ?Edk; reflexivity].
    + gstep_st HG (32 * i + 12)%nat 4%nat.
      eapply st_last; [exact Hi | exact He | mk_mf | rewrite EM; rewrite ?E16, ?Edk; reflexivity].
  - gstep_st HG (32 * i + 16)%nat 1%nat. rewrite le1_fb in HG.
    step. rewrite (lts_lit (gdk S) 0) by lia. brc Edk.
    + eapply st_last; [exact Hi | exact He | mk_mf | rewrite EM; rewrite ?E16, ?Edk; reflexivity].
    + gstep_st HG (32 * i + 12)%nat 4%nat.
      eapply st_last; [exact Hi | exact He | mk_mf | rewrite EM; rewrite ?E16, ?Edk; reflexivity].
Qed.

Lemma edge_w : forall m i e rx x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x28 x29 x30 x31,
  GF i -> gedge G S i = true -> e = g + 32 * Z.of_nat i -> (fu S 8 4 =? 0) = false -> MF m G ->
  evt rsegs QP
    (MS (mkR rx SPF gp tp x5 x6 x7 (Z_to_bv 64 now) (Z_to_bv 64 s) (Z_to_bv 64 (s32 (fu S 8 4)))
             x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 e) x19 (Z_to_bv 64 (gdk S)) x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x15528) fc None m (seg_rom rsegs)).
Proof.
  intros m i e rx x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x28 x29 x30 x31 Hf Hed He E0
    (FR & ST & MU & WM & MI & HG & HS).
  ffacts Hf i.
  gstep_st HG (32 * i + 8)%nat 4%nat.
  rewrite (le4_s32_fu S 8) in HG by lia.
  eapply edge_tail; [exact Hf | exact Hed | exact He | | mk_mf]. rewrite E0. reflexivity.
Qed.

Lemma edge_head : forall m i e rx x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x28 x29 x30 x31,
  GF i -> gedge G S i = true -> e = g + 32 * Z.of_nat i -> MF m G ->
  evt rsegs QP
    (MS (mkR rx SPF gp tp x5 x6 x7 (Z_to_bv 64 now) (Z_to_bv 64 s) (Z_to_bv 64 (s32 (fu S 8 4)))
             x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 e) x19 (Z_to_bv 64 (gdk S)) x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x15524) fc None m (seg_rom rsegs)).
Proof.
  intros m i e rx x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x28 x29 x30 x31 Hf Hed He HM.
  pose proof (fu_rng4 S 8 ltac:(lia)) as R8. pose proof (s32_range _ R8) as R8'.
  step. rewrite (eqb_lit (s32 (fu S 8 4)) 0) by lia. rewrite (s32_eq0 _ R8). brc E0.
  - eapply edge_tail; [exact Hf | exact Hed | exact He | | exact HM]. rewrite E0. reflexivity.
  - eapply edge_w; [exact Hf | exact Hed | exact He | exact E0 | exact HM].
Qed.

Lemma refresh : forall m i e rx x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x28 x29 x30 x31,
  GF i -> gedge G S i = false -> e = g + 32 * Z.of_nat i -> MF m G ->
  evt rsegs QP
    (MS (mkR rx SPF gp tp x5 x6 x7 (Z_to_bv 64 now) (Z_to_bv 64 s) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 e) x19 (Z_to_bv 64 (gdk S)) x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x15504) fc None m (seg_rom rsegs)).
Proof.
  intros m i e rx x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x28 x29 x30 x31 Hf Hed He
    (FR & ST & MU & WM & MI & HG & HS).
  ffacts Hf i.
  pose proof (fu_rng8 G (32 * i + 24) ltac:(lia)) as RL.
  gld HG (32 * i + 24)%nat 8%nat.
  rewrite (ld_val (fld G (32 * i + 24) 8)) by (apply length_fld; lia).
  change (bytes_le_to_Z (fld G (32 * i + 24) 8)) with (fu G (32 * i + 24) 8).
  step. rewrite (ltu_lit now (fu G (32 * i + 24) 8)) by lia. brc El.
  - eapply st_last; [exact Hi | exact He | mk_mf | apply (gm_refresh G S now i Hf Hed); rewrite El; reflexivity].
  - apply Z.ltb_ge in El.
    step. rewrite (unsigned_lit now) by lia. rewrite (unsigned_lit (fu G (32 * i + 24) 8)) by lia.
    step. step.
    step. rewrite (ltu_lit (now - fu G (32 * i + 24) 8) 1000000000) by lia. brc Ed.
    + eapply ret0; [mk_mf | apply (gm_keep G S now i Hf Hed)].
      unfold RF. rewrite Z.leb_antisym, Ed. destruct (Z.ltb_spec now (fu G (32 * i + 24) 8)); [lia | reflexivity].
    + eapply st_last; [exact Hi | exact He | mk_mf | apply (gm_refresh G S now i Hf Hed)].
      unfold RF. rewrite Z.leb_antisym, Ed. destruct (now <? fu G (32 * i + 24) 8); reflexivity.
Qed.

Lemma ss_part : forall m i e rx x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x28 x29 x30 x31,
  GF i -> e = g + 32 * Z.of_nat i ->
  (negb (fu S 8 4 =? 0) && negb (fu S 8 4 =? fu G (32 * i + 8) 4)) = false ->
  ((0 <=? gdk S) && negb (gdk S =? s32 (fu G (32 * i + 12) 4))) = false -> MF m G ->
  evt rsegs QP
    (MS (mkR rx SPF gp tp x5 x6 x7 (Z_to_bv 64 now) (Z_to_bv 64 s) (Z_to_bv 64 (s32 (fu S 8 4)))
             x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 e) x19 (Z_to_bv 64 (gdk S)) x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x154f4) fc None m (seg_rom rsegs)).
Proof.
  intros m i e rx x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x28 x29 x30 x31 Hf He C1 C2
    (FR & ST & MU & WM & MI & HG & HS).
  ffacts Hf i.
  pose proof (fb_rng S 16) as R16. pose proof (fb_rng G (32 * i + 16)) as R16'.
  sld HS 16%nat 1%nat. change (zxb (nth 16 S (zb 0))) with (Z_to_bv 64 (fb S 16)).
  step. rewrite (eqb_lit (fb S 16) 0) by lia. brc E16.
  - eapply refresh; [exact Hf | | exact He | mk_mf]. unfold gedge. rewrite C1, C2, E16. reflexivity.
  - gld HG (32 * i + 16)%nat 1%nat.
    change (zxb (nth (32 * i + 16) G (zb 0))) with (Z_to_bv 64 (fb G (32 * i + 16))).
    step. rewrite (eqb_lit (fb S 16) (fb G (32 * i + 16))) by lia. brc Es.
    + eapply refresh; [exact Hf | | exact He | mk_mf]. unfold gedge. rewrite C1, C2, E16, Es. reflexivity.
    + eapply edge_head; [exact Hf | | exact He | mk_mf]. unfold gedge. rewrite C1, C2, E16, Es. reflexivity.
Qed.

Lemma dk_part : forall m i e rx x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x28 x29 x30 x31,
  GF i -> e = g + 32 * Z.of_nat i ->
  (negb (fu S 8 4 =? 0) && negb (fu S 8 4 =? fu G (32 * i + 8) 4)) = false -> MF m G ->
  evt rsegs QP
    (MS (mkR rx SPF gp tp x5 x6 x7 (Z_to_bv 64 now) (Z_to_bv 64 s) (Z_to_bv 64 (s32 (fu S 8 4)))
             x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 e) x19 (Z_to_bv 64 (gdk S)) x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x154e8) fc None m (seg_rom rsegs)).
Proof.
  intros m i e rx x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x28 x29 x30 x31 Hf He C1
    (FR & ST & MU & WM & MI & HG & HS).
  ffacts Hf i.
  pose proof (gdk_rng S) as Rdk. pose proof (fu_rng4 G (32 * i + 12) ltac:(lia)) as R12.
  pose proof (s32_range _ R12) as R12'.
  step. rewrite (lts_lit (gdk S) 0) by lia. brc Edk.
  - eapply ss_part; [exact Hf | exact He | exact C1 | | mk_mf]. rewrite Z.leb_antisym, Edk. reflexivity.
  - gld HG (32 * i + 12)%nat 4%nat.
    rewrite (lw_val (fld G (32 * i + 12) 4)) by (apply length_fld; lia).
    change (bytes_le_to_Z (fld G (32 * i + 12) 4)) with (fu G (32 * i + 12) 4).
    step. rewrite (eqb_lit (gdk S) (s32 (fu G (32 * i + 12) 4))) by lia. brc Ek.
    + eapply ss_part; [exact Hf | exact He | exact C1 | | mk_mf]. rewrite Ek. destruct (0 <=? gdk S); reflexivity.
    + eapply edge_head; [exact Hf | | exact He | mk_mf]. unfold gedge. rewrite C1, Z.leb_antisym, Edk, Ek. reflexivity.
Qed.

Lemma arm_found : forall m i e rx x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x28 x29 x30 x31,
  GF i -> e = g + 32 * Z.of_nat i -> MF m G ->
  evt rsegs QP
    (MS (mkR rx SPF gp tp x5 x6 x7 (Z_to_bv 64 now) (Z_to_bv 64 s) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 e) x19 (Z_to_bv 64 (gdk S)) x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x154d8) fc None m (seg_rom rsegs)).
Proof.
  intros m i e rx x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x28 x29 x30 x31 Hf He
    (FR & ST & MU & WM & MI & HG & HS).
  ffacts Hf i.
  pose proof (fu_rng4 S 8 ltac:(lia)) as R8. pose proof (s32_range _ R8) as R8'.
  pose proof (fu_rng4 G (32 * i + 8) ltac:(lia)) as RG8. pose proof (s32_range _ RG8) as RG8'.
  sld HS 8%nat 4%nat.
  rewrite (lw_val (fld S 8 4)) by (apply length_fld; lia).
  change (bytes_le_to_Z (fld S 8 4)) with (fu S 8 4).
  step. rewrite (eqb_lit (s32 (fu S 8 4)) 0) by lia. rewrite (s32_eq0 _ R8). brc E0.
  - eapply dk_part; [exact Hf | exact He | | mk_mf]. rewrite E0. reflexivity.
  - gld HG (32 * i + 8)%nat 4%nat.
    rewrite (lw_val (fld G (32 * i + 8) 4)) by (apply length_fld; lia).
    change (bytes_le_to_Z (fld G (32 * i + 8) 4)) with (fu G (32 * i + 8) 4).
    step. rewrite (eqb_lit (s32 (fu S 8 4)) (s32 (fu G (32 * i + 8) 4))) by lia.
    rewrite (s32_inj _ _ R8 RG8). brc E1.
    + eapply dk_part; [exact Hf | exact He | | mk_mf]. rewrite E0, E1. reflexivity.
    + eapply edge_w; [exact Hf | | exact He | exact E0 | mk_mf]. unfold gedge. rewrite E0, E1. reflexivity.
Qed.

Lemma arm_app : forall m n rx x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x28 x29 x30 x31,
  gfind G (fld S 0 6) 0 (Z.to_nat (gn G)) = None -> n = gn G -> n < 8 -> MF m G ->
  evt rsegs QP
    (MS (mkR rx SPF gp tp x5 x6 x7 (Z_to_bv 64 now) (Z_to_bv 64 s) x10 x11 x12 x13 x14 x15 x16 x17
             x18 (Z_to_bv 64 g) (Z_to_bv 64 (gdk S)) (Z_to_bv 64 n) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1549c) fc None m (seg_rom rsegs)).
Proof.
  intros m n rx x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x28 x29 x30 x31 Hf Hn Hn8
    (FR & ST & MU & WM & MI & HG & HS).
  pose proof HGok as (HL & HnG & _).
  set (N := Z.to_nat n).
  assert (HnN : n = Z.of_nat N) by (unfold N; lia).
  assert (HN8 : (N < 8)%nat) by lia.
  clearbody N.
  step.
  gstep_st HG 256%nat 4%nat.
  sld HS 4%nat 2%nat.
  step. step.
  rewrite (unsigned_lit n) by lia. rewrite (Z.shiftl_mul_pow2 n 5) by lia. change (2 ^ 5) with 32.
  gstep_st HG (32 * N + 4)%nat 2%nat.
  rewrite (le2_lh_g (fld S 4 2)) in HG by (apply length_fld; lia).
  sld HS 0%nat 4%nat.
  gstep_st HG (32 * N)%nat 4%nat.
  rewrite (le4_lw_g (fld S 0 4)) in HG by (apply length_fld; lia).
  sld HS 8%nat 4%nat.
  sld HS 16%nat 1%nat.
  change (zxb (nth 16 S (zb 0))) with (Z_to_bv 64 (fb S 16)).
  gstep_st HG (32 * N + 12)%nat 4%nat.
  gstep_st HG (32 * N + 24)%nat 8%nat.
  gstep_st HG (32 * N + 8)%nat 4%nat.
  rewrite (le4_lw_g (fld S 8 4)) in HG by (apply length_fld; lia).
  gstep_st HG (32 * N + 16)%nat 1%nat.
  rewrite le1_fb in HG.
  step. step.
  rewrite (app_eq _ (fld S 0 4) (fld S 4 2) (fld S 8 4)) in HG
    by first [ rewrite upd_bytes_length; [lia | rewrite length_le4; lia] | lia | apply length_fld; lia
             | apply length_le4 | apply length_le8 | reflexivity ].
  rewrite (fld_app_06 S) in HG by lia.
  eapply epi; [mk_mf|].
  rewrite (gm_app G S now N Hf ltac:(lia) HN8). rewrite <- HnN. reflexivity.
Qed.

Lemma gmemcmp : forall n (l r : list byte) v, length l = n -> length r = n -> memcmp_model l r n = Some v ->
  -256 < v < 256 /\ (v = 0 <-> map bv_unsigned l = map bv_unsigned r).
Proof.
  induction n as [|n IH]; intros [|a l] [|b r] v Hl Hr H; cbn [length memcmp_model map] in *; try discriminate.
  - injection H as <-. split; [lia| tauto].
  - injection Hl as Hl. injection Hr as Hr.
    pose proof (byte_rng a) as Ra. pose proof (byte_rng b) as Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|NE].
    + destruct (IH l r v Hl Hr H) as [Hv Hi]. split; [exact Hv|]. rewrite Hi, E.
      split; [intros ->; reflexivity | intros Hc; injection Hc as Hc; exact Hc].
    + injection H as <-. split; [lia|]. split; [lia | intros Hc; injection Hc as Hc _; contradiction].
Qed.

Hypothesis BC : bcmp_contract.

Lemma loop : forall k i e c n m rx x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  (i + k = Z.to_nat (gn G))%nat -> (0 < k)%nat -> e = g + 32 * Z.of_nat i -> c = Z.of_nat k -> n = gn G ->
  (forall j, (j < i)%nat -> bytes_eqb (gmac G j) (fld S 0 6) = false) -> MF m G ->
  evt rsegs QP
    (MS (mkR rx SPF gp tp x5 x6 x7 (Z_to_bv 64 now) (Z_to_bv 64 s) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 e) (Z_to_bv 64 g) (Z_to_bv 64 (gdk S)) (Z_to_bv 64 n) (Z_to_bv 64 c)
             s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x15474) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros i e c n m rx x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
    Hk Hk0 He Hc Hn Hb (FR & ST & MU & WM & MI & HG & HS); [lia|].
  pose proof HGok as (HL & HnG & _).
  assert (Hi : (i < 8)%nat) by lia.
  pose proof (proj1 (rw_CB_bytes _ _ _ _ _ HG)) as HGb.
  pose proof (bytes_at_fld _ _ _ _ (32 * i) 6 HGb ltac:(lia)) as HA.
  pose proof (bytes_at_fld _ _ _ _ 0 6 HS ltac:(lia)) as HB.
  clear HGb.
  assert (LA : length (gmac G i) = 6%nat) by (apply length_fld; lia).
  assert (LB : length (fld S 0 6) = 6%nat) by (apply length_fld; lia).
  destruct (memcmp_model_total (gmac G i) (fld S 0 6) 6 ltac:(lia) ltac:(lia)) as [v Hv].
  destruct (gmemcmp 6 (gmac G i) (fld S 0 6) v LA LB Hv) as [Rv Iv].
  step. step. step. step.
  eapply evt_cut.
  { eapply BC; [ eapply bat_word; [exact HA | lia | lia] | eapply bat_word; [exact HB | lia | lia] | exact Hv | exact MI ]. }
  post_call rsegs m.
  step. rewrite (eqb_lit v 0) by lia. brc Ev.
  - apply Z.eqb_eq in Ev.
    assert (Hf : gfind G (fld S 0 6) 0 (Z.to_nat (gn G)) = Some i).
    { apply gfind_Some_intro; [lia | intros j' Hj'; apply Hb; lia | apply beq_iff, Iv, Ev]. }
    eapply arm_found; [exact Hf | exact He | mk_mf].
  - apply Z.eqb_neq in Ev.
    assert (Hbi : bytes_eqb (gmac G i) (fld S 0 6) = false).
    { destruct (bytes_eqb (gmac G i) (fld S 0 6)) eqn:E; [|reflexivity]. apply beq_iff, Iv in E. contradiction. }
    assert (Hb' : forall j, (j < Datatypes.S i)%nat -> bytes_eqb (gmac G j) (fld S 0 6) = false).
    { intros j Hj. destruct (Nat.eq_dec j i) as [->|NE]; [exact Hbi | apply Hb; lia]. }
    step. step. step. rewrite (eqb_lit (c + -1) 0) by lia. brc Ec.
    + apply Z.eqb_eq in Ec.
      assert (Hnf : gfind G (fld S 0 6) 0 (Z.to_nat (gn G)) = None).
      { apply gfind_None_intro. intros j Hj. apply Hb'. lia. }
      step. step. rewrite (lts_lit 7 n) by lia. brc E7.
      * eapply ret0; [mk_mf | apply gm_full; [exact Hnf | lia]].
      * eapply arm_app; [exact Hnf | exact Hn | lia | mk_mf].
    + apply Z.eqb_neq in Ec.
      eapply (IH (Datatypes.S i) (e + 32) (c + -1) n); [lia | lia | lia | lia | exact Hn | exact Hb' | mk_mf].
Qed.

Lemma at_lw : forall m rx x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x28 x29 x30 x31,
  MF m G ->
  evt rsegs QP
    (MS (mkR rx SPF gp tp x5 x6 x7 (Z_to_bv 64 now) (Z_to_bv 64 s) x10 x11 x12 x13 x14 x15 x16 x17
             x18 (Z_to_bv 64 g) (Z_to_bv 64 (gdk S)) x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x15464) fc None m (seg_rom rsegs)).
Proof.
  intros m rx x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x28 x29 x30 x31
    (FR & ST & MU & WM & MI & HG & HS).
  pose proof HGok as (HL & HnG & _).
  gld HG 256%nat 4%nat.
  rewrite (lw_val (fld G 256 4)) by (apply length_fld; lia).
  change (s32 (bytes_le_to_Z (fld G 256 4))) with (gn G).
  step. rewrite (lts_lit 0 (gn G)) by lia. brc En.
  - apply Z.ltb_lt in En.
    step. step.
    eapply (loop (Z.to_nat (gn G)) 0 g (gn G) (gn G)); [lia | lia | lia | lia | reflexivity | intros; lia | mk_mf].
  - apply Z.ltb_ge in En.
    eapply arm_app; [ | reflexivity | lia | mk_mf].
    replace (Z.to_nat (gn G)) with 0%nat by lia. reflexivity.
Qed.

Lemma dk_val : (fb S 12 =? 0) = false ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (fb S 13))) 8)))
    (bv_unsigned (Z_to_bv 64 (fb S 14)))) = Z_to_bv 64 (gdk S).
Proof.
  intros E12. pose proof (fb_rng S 13) as R13. pose proof (fb_rng S 14) as R14.
  rewrite (unsigned_lit (fb S 13)) by lia. rewrite (unsigned_lit (fb S 14)) by lia.
  rewrite (Z.shiftl_mul_pow2 (fb S 13) 8) by lia. change (2 ^ 8) with 256.
  rewrite (unsigned_lit (fb S 13 * 256)) by lia.
  rewrite (lor_add (fb S 13 * 256) (fb S 14) 8) by (try change (2 ^ 8) with 256; first [lia | apply Z.mod_mul; lia]).
  unfold gdk. rewrite E12. f_equal. lia.
Qed.

Lemma entry : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  rw_cells rsegs m0 g [CB 264 G] -> bytes_at rsegs m0 s S -> stk rsegs m0 lo (bv_unsigned sp) -> mem_inv rsegs m0 ->
  evt rsegs QP
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 g) (Z_to_bv 64 s) (Z_to_bv 64 now) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15414) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HG HS ST MI.
  pose proof HGok as (HL & HnG & _).
  carve_frame 64%nat ST.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (g, g + 264)] m0) as MU.
  pose proof (wmono_refl rsegs m0) as WM.
  step. step. step. step. step. step. step. step. step.
  step. step.
  sld HS 12%nat 1%nat.
  change (zxb (nth 12 S (zb 0))) with (Z_to_bv 64 (fb S 12)).
  pose proof (fb_rng S 12) as R12. pose proof (fb_rng S 13) as R13. pose proof (fb_rng S 14) as R14.
  step. step. rewrite (eqb_lit (fb S 12) 0) by lia.
  brc E12.
  - step.
    replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (gdk S)) by (unfold gdk; rewrite E12; reflexivity).
    eapply at_lw. mk_mf.
  - sld HS 13%nat 1%nat. sld HS 14%nat 1%nat.
    change (zxb (nth 13 S (zb 0))) with (Z_to_bv 64 (fb S 13)).
    change (zxb (nth 14 S (zb 0))) with (Z_to_bv 64 (fb S 14)).
    step. step. step.
    rewrite (dk_val E12).
    eapply at_lw. mk_mf.
Qed.

End Plain.

Theorem reac_disco_gate_should_push_holds : bcmp_contract -> reac_disco_gate_should_push_contract.
Proof.
  intros BC. unfold reac_disco_gate_should_push_contract, REAC_DISCO_GATE_SHOULD_PUSH_K, REAC_DISCO_GATE_SHOULD_PUSH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo g s now
    G S -> -> -> Hnow Hg0 Hg8 HG HGok Hs0 Hs4 HSl HS Dgs Dgk Dsk ST Hsp MI.
  pose proof (rw_CB_bytes _ _ _ _ _ HG) as [HGb LG].
  pose proof (bytes_at_bound _ _ _ _ HGb) as Bg. rewrite LG in Bg.
  pose proof (bytes_at_bound _ _ _ _ HS) as Bs. rewrite HSl in Bs.
  pose proof ST as (Hlo & Hsp1 & _).
  eapply entry; try eassumption; lia.
Qed.
