(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import AShadow ASaves.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require Import BCode BRt BrCode BRtIc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition TP : Z := 0xbdae10.             (* [comment removed for export] *)
Definition DTV : Z := 0xbdae40.            (* [comment removed for export] *)
Definition TSD : Z := 0xbfc1b8.            (* [comment removed for export] *)
Definition R_TLSGA : Z := 0x5e4068.        (* [comment removed for export] *)
Definition TLS_DESC : Z := 0x5e2f20.       (* [comment removed for export] *)
Definition C_TSDINIT : Z := 0x6a32e0.      (* [comment removed for export] *)
Definition G_VERB : Z := 0x5e0fa8.         (* [comment removed for export] *)
Definition C_VERB : Z := 0x733518.
Definition G_DTLSOFF : Z := 0x5e2f50.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fsrt_ok (M : mem) (fs T ctx thr : Z) : Prop :=
  cell BSEGS M C_INITED 1 (W 1)
  /\ cell BSEGS M R_TLSGA 8 (W 0x5643f0)
  /\ cell BSEGS M TLS_DESC 8 (W 1) /\ cell BSEGS M (TLS_DESC + 8) 8 (W (-2048))
  /\ cell BSEGS M (TP - 8) 8 (W DTV) /\ cell BSEGS M (DTV + 8) 8 (W (TP + 2048))
  /\ cell BSEGS M TP 8 (W fs)
  /\ cell BSEGS M C_TSDINIT 1 (W 1) /\ cell BSEGS M (C_TSDINIT + 4) 4 (W 0)
  /\ cell BSEGS M (TP - 88) 8 (W TSD) /\ cell BSEGS M TSD 8 (W ctx)
  /\ cell BSEGS M G_CF 8 (W C_CF) /\ cell BSEGS M (C_CF + 137) 1 (W 1)
  /\ cell BSEGS M G_VERB 8 (W C_VERB) /\ cell BSEGS M C_VERB 4 (W 0)
  /\ cell BSEGS M G_DTLSOFF 8 (W 24) /\ cell BSEGS M (TP + 24) 8 (W T)
  /\ cell BSEGS M (ctx + 152) 8 (W thr)
  /\ (exists tb te, cell BSEGS M (thr + 48) 8 tb /\ cell BSEGS M (thr + 56) 8 te)
  /\ (exists beg, cell BSEGS M (T + 24) 8 (W beg) /\ 0 < beg < 2 ^ 64)
  /\ cell BSEGS M (fs + 88) 8 (W 20) /\ cell BSEGS M (fs + 96) 1 (W 0).

(* [comment removed for export] *)
Definition fsrt_dom (fs T ctx thr : Z) (x : word) : Prop :=
  inr x (T + 24) 8 \/ inr x (ctx + 152) 8 \/ inr x (thr + 48) 16 \/ inr x (fs + 88) 9.

Definition fsrt_wf (fs T ctx thr : Z) : Prop :=
  0 < T < 2 ^ 63 /\ 0 < ctx < 2 ^ 63 /\ 0 < thr < 2 ^ 63 /\ 0 < fs < 2 ^ 63.

(* [comment removed for export] *)
Definition fsrt_sep (lo n fs T ctx thr : Z) : Prop :=
  (T + 32 <= lo \/ lo + n <= T + 24) /\ (ctx + 160 <= lo \/ lo + n <= ctx + 152)
  /\ (thr + 64 <= lo \/ lo + n <= thr + 48) /\ (fs + 97 <= lo \/ lo + n <= fs + 88).

Lemma fsrt_sep_dom : forall lo n fs T ctx thr x, fsrt_sep lo n fs T ctx thr -> inr x lo n -> ~ fsrt_dom fs T ctx thr x.
Proof. intros lo n fs T ctx thr x (H1 & H2 & H3 & H4) Hx Hd. unfold fsrt_dom, inr in *. lia. Qed.

Lemma fsrt_sep_sub : forall lo n lo' n' fs T ctx thr, fsrt_sep lo n fs T ctx thr -> lo <= lo' -> lo' + n' <= lo + n ->
  fsrt_sep lo' n' fs T ctx thr.
Proof. intros lo n lo' n' fs T ctx thr (H1 & H2 & H3 & H4) Hlo Hhi. unfold fsrt_sep. lia. Qed.

Lemma fsrt_ok_unch : forall M0 M (P : word -> Prop) fs T ctx thr,
  fsrt_wf fs T ctx thr -> unch M0 M P ->
  (forall y, P y -> B_IMG_END <= bv_unsigned y /\ ~ fsrt_dom fs T ctx thr y) ->
  fsrt_ok M0 fs T ctx thr -> fsrt_ok M fs T ctx thr.
Proof.
  intros M0 M P fs T ctx thr (HT & Hctx & Hthr & Hfs) HU HP
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18
     & (tb & te & H19 & H20) & (beg & H21 & Hbeg) & H22 & H23).
  assert (TI : forall a (k : nat) v, 0 <= a -> a + Z.of_nat k <= B_IMG_END -> cell BSEGS M0 a k v -> cell BSEGS M a k v).
  { intros a k v Ha Hk Hc. eapply cell_unch; [exact HU | lia | unfold B_IMG_END in *; lia | | exact Hc].
    intros x Hx HPx. apply HP in HPx. unfold inr in Hx. lia. }
  assert (TO : forall a (k : nat) v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
               (forall x, inr x a (Z.of_nat k) -> fsrt_dom fs T ctx thr x) -> cell BSEGS M0 a k v -> cell BSEGS M a k v).
  { intros a k v Ha Hk Hd Hc. eapply cell_unch; [exact HU | lia | lia | | exact Hc].
    intros x Hx HPx. apply HP in HPx. apply (proj2 HPx). apply Hd. exact Hx. }
  unfold fsrt_ok, C_INITED, R_TLSGA, TLS_DESC, TP, DTV, TSD, C_TSDINIT, G_CF, C_CF, G_VERB, C_VERB, G_DTLSOFF, B_IMG_END in *.
  repeat split; try (apply TI; [lia | cbn; lia | assumption]).
  - apply TO; [lia | cbn; lia | | assumption]. intros x Hx. cbn in Hx. unfold fsrt_dom, inr in *. lia.
  - exists tb, te. split; (apply TO; [lia | cbn; lia | | assumption]); intros x Hx; cbn in Hx; unfold fsrt_dom, inr in *; lia.
  - exists beg. split; [|exact Hbeg]. apply TO; [lia | cbn; lia | | assumption]. intros x Hx. cbn in Hx. unfold fsrt_dom, inr in *. lia.
  - apply TO; [lia | cbn; lia | | assumption]. intros x Hx. cbn in Hx. unfold fsrt_dom, inr in *. lia.
  - apply TO; [lia | cbn; lia | | assumption]. intros x Hx. cbn in Hx. unfold fsrt_dom, inr in *. lia.
Qed.

(* [comment removed for export] *)
Ltac wp_tga stops := wp_go 0x5643f0 9%nat C_tlsga_eq C_tlsga stops.

Lemma tlsga_cps : forall rom Post M fs T ctx thr l,
  fsrt_ok M fs T ctx thr -> length l = 32%nat -> rget l 4 = W TP -> rget l 10 = W TLS_DESC ->
  (forall l', length l' = 32%nat -> same_except [10%nat; 11%nat; 12%nat] l l' -> rget l' 10 = W TP ->
              reach BSEGS rom (v_jalr (rget l 1) 0) l' M Post) ->
  reach BSEGS rom (Z_to_bv 64 0x5643f0) l M Post.
Proof.
  intros rom Post M fs T ctx thr l (_ & _ & Hd0 & Hd8 & Hdtv & Hdtv1 & _) Hl H4 H10 K.
  unfold TLS_DESC, TP, DTV in *. regs_open l Hl. subst tp a0.
  wp_tga (@nil Z). mem_auto.
  change (v_slli (Z_to_bv 64 1) 3) with (W 8). rewrite ?add_W. mem_auto. rewrite ?add_W.
  apply K; [reflexivity | same_ex | cbn [lget]; f_equal; lia].
Qed.

(* [comment removed for export] *)
Ltac wp_gsp stops := wp_go 0x56625c 7%nat C_getspecific_eq C_getspecific stops.
Ltac wp_tsd stops := wp_go 0x1c0628 17%nat C_tsdget_eq C_tsdget stops.
Ltac wp_cth stops := wp_go 0x1c8030 8%nat C_curthread_eq C_curthread stops.

Lemma getspecific_cps : forall rom Post M fs T ctx thr l,
  fsrt_ok M fs T ctx thr -> length l = 32%nat -> rget l 4 = W TP -> rget l 10 = W 0 ->
  (forall l', length l' = 32%nat -> same_except [10%nat; 11%nat] l l' -> rget l' 10 = W ctx ->
              reach BSEGS rom (v_jalr (rget l 1) 0) l' M Post) ->
  reach BSEGS rom (Z_to_bv 64 0x56625c) l M Post.
Proof.
  intros rom Post M fs T ctx thr l (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htsd & Hctx & _) Hl H4 H10 K.
  unfold TP, TSD in *. regs_open l Hl. subst tp a0.
  wp_gsp (@nil Z). mem_auto.
  change (v_srli (v_slli (Z_to_bv 64 0) 32) 29) with (W 0). rewrite ?add_W. mem_auto.
  apply K; [reflexivity | same_ex | reflexivity].
Qed.

Lemma tsdget_cps : forall rom Post M fs T ctx thr l,
  fsrt_ok M fs T ctx thr -> length l = 32%nat -> rget l 4 = W TP ->
  (forall l', length l' = 32%nat -> same_except [6%nat; 10%nat; 11%nat] l l' -> rget l' 10 = W ctx ->
              reach BSEGS rom (v_jalr (rget l 1) 0) l' M Post) ->
  reach BSEGS rom (Z_to_bv 64 0x1c0628) l M Post.
Proof.
  intros rom Post M fs T ctx thr l Hok Hl H4 K.
  pose proof Hok as (_ & _ & _ & _ & _ & _ & _ & Hki & Hkey & _).
  unfold C_TSDINIT in *. regs_open l Hl. subst tp.
  wp_tsd [0x1c0644]. mem_auto.
  change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) mod 2 ^ (8 * Z.of_nat 1)))) with 1.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  eexists. split; [apply load_cell; [exact Hkey | lia]|].
  replace (v_jalr (Z_to_bv 64 5662572) (-1296)) with (Z_to_bv 64 0x56625c) by reflexivity.
  change (v_lw (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) mod 2 ^ (8 * Z.of_nat 4)))) with (W 0).
  eapply (getspecific_cps rom Post M fs T ctx thr); [exact Hok | reflexivity | reflexivity | reflexivity |].
  intros l' Hl' Hse' H10'. cbn [rget lget].
  apply K; [exact Hl' | | exact H10'].
  eapply same_except_trans; [|eapply same_except_weaken; [exact Hse'|]].
  - same_ex.
  - intros j Hj. cbn [In] in *. intuition lia.
Qed.

(* [comment removed for export] *)
Lemma curthread_cps : forall rom Post M fs T ctx thr S l,
  fsrt_ok M fs T ctx thr -> fsrt_wf fs T ctx thr ->
  B_IMG_END <= S - 16 /\ S < 2 ^ 63 -> wr_ok BSEGS M (S - 16) 16 ->
  fsrt_sep (S - 16) 16 fs T ctx thr ->
  length l = 32%nat -> rget l 2 = W S -> rget l 4 = W TP ->
  (forall l' M', length l' = 32%nat -> same_except [6%nat; 10%nat; 11%nat] l l' -> rget l' 10 = W thr ->
                 unch M M' (fun x => inr x (S - 16) 16) -> mem_grows M M' ->
                 reach BSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach BSEGS rom (Z_to_bv 64 0x1c8030) l M Post.
Proof.
  intros rom Post M fs T ctx thr S l Hok Hwf HS Hw Hdj Hl H2 H4 K.
  pose proof Hwf as (HT & Hctx & Hthr & Hfs). unfold B_IMG_END in *.
  regs_open l Hl. subst sp tp.
  wp_cth (@nil Z). mem_auto.
  match goal with |- reach _ _ _ _ ?Mx _ => set (M1 := Mx) end.
  assert (HU1 : unch M M1 (fun x => inr x (S - 16) 16)).
  { unfold M1. solve_unch ltac:(unfold inr in *; lia). }
  assert (HG1 : mem_grows M M1) by (unfold M1; solve_grows).
  assert (Cra : cell BSEGS M1 (S + -16 + 8) 8 ra) by (unfold M1; solve_cell).
  assert (Hok1 : fsrt_ok M1 fs T ctx thr).
  { eapply fsrt_ok_unch; [exact Hwf | exact HU1 | | exact Hok].
    intros y Hy. split; [unfold inr, B_IMG_END in *; lia | eapply fsrt_sep_dom; [exact Hdj | exact Hy]]. }
  clearbody M1.
  replace (Z_to_bv 64 1836584) with (Z_to_bv 64 0x1c0628) by reflexivity.
  eapply (tsdget_cps rom Post M1 fs T ctx thr); [exact Hok1 | reflexivity | reflexivity |].
  intros l' Hl' Hse' H10'. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1867836) 0) with (Z_to_bv 64 0x1c803c) by reflexivity.
  regs_open l' Hl'. se_subst Hse'. clear Hse'. cbn [rget lget] in H10'. match type of H10' with ?x = _ => subst x end.
  pose proof Hok1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hthrc & _).
  wp_cth (@nil Z). rewrite (Wu ctx) by lia.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  mem_auto. replace (S + -16 + 16) with S by lia.
  apply K; [reflexivity | same_ex | reflexivity | exact HU1 | exact HG1].
Qed.

(* [comment removed for export] *)
Ltac wp_dtl stops := wp_go 0x1d5a88 212%nat C_dtls_eq C_dtls stops.

Section Dtls.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (fs T ctx thr S : Z).
Hypothesis Hok : fsrt_ok M fs T ctx thr.
Hypothesis Hwf : fsrt_wf fs T ctx thr.
Hypothesis HS : B_IMG_END <= S - 144 /\ S < 2 ^ 63.
Hypothesis Hw : wr_ok BSEGS M (S - 144) 144.
Hypothesis Hsep : fsrt_sep (S - 144) 144 fs T ctx thr.

Definition KS_dtl : list nat := [10; 11]%nat.
Definition KSI_dtl : list nat :=
  [1; 2; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition FP_dtl (x : word) : Prop := inr x (S - 144) 144.

Variable l0 : regfile.
Hypothesis Hl0 : length l0 = 32%nat.
Hypothesis H0sp : rget l0 2 = W S.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KS_dtl l0 l' -> rget l' 10 = W 0 ->
  unch M M' FP_dtl -> mem_grows M M' ->
  reach BSEGS rom (v_jalr (rget l0 1) 0) l' M' Post.

Definition SL_dtl : list (Z * word) :=
  [(136, rget l0 1); (128, rget l0 8); (120, rget l0 9); (112, rget l0 18); (104, rget l0 19); (96, rget l0 20);
   (88, rget l0 21); (80, rget l0 22); (72, rget l0 23); (64, rget l0 24); (56, rget l0 25); (48, rget l0 26);
   (40, rget l0 27)].

(* [comment removed for export] *)
Definition DMI (M' : mem) : Prop :=
  (forall off v, In (off, v) SL_dtl -> cell BSEGS M' (S + -144 + off) 8 v) /\ unch M M' FP_dtl /\ mem_grows M M'.

(* [comment removed for export] *)
Lemma dtls_epi : forall l M', DMI M' -> length l = 32%nat -> same_except KSI_dtl l0 l -> rget l 2 = W (S + -144) ->
  reach BSEGS rom (Z_to_bv 64 0x1d5c64) l M' Post.
Proof.
  intros l M' (Hsv & HU & HG) Hl Hse H2. unfold B_IMG_END in *.
  pose proof (Hsv 136 _ ltac:(unfold SL_dtl; in_list)) as Csv1. pose proof (Hsv 128 _ ltac:(unfold SL_dtl; in_list)) as Csv8.
  pose proof (Hsv 120 _ ltac:(unfold SL_dtl; in_list)) as Csv9. pose proof (Hsv 112 _ ltac:(unfold SL_dtl; in_list)) as Csv18.
  pose proof (Hsv 104 _ ltac:(unfold SL_dtl; in_list)) as Csv19. pose proof (Hsv 96 _ ltac:(unfold SL_dtl; in_list)) as Csv20.
  pose proof (Hsv 88 _ ltac:(unfold SL_dtl; in_list)) as Csv21. pose proof (Hsv 80 _ ltac:(unfold SL_dtl; in_list)) as Csv22.
  pose proof (Hsv 72 _ ltac:(unfold SL_dtl; in_list)) as Csv23. pose proof (Hsv 64 _ ltac:(unfold SL_dtl; in_list)) as Csv24.
  pose proof (Hsv 56 _ ltac:(unfold SL_dtl; in_list)) as Csv25. pose proof (Hsv 48 _ ltac:(unfold SL_dtl; in_list)) as Csv26.
  pose proof (Hsv 40 _ ltac:(unfold SL_dtl; in_list)) as Csv27. clear Hsv.
  regs_open l Hl. subst sp.
  wp_dtl (@nil Z). mem_auto.
  apply K; [reflexivity | | reflexivity | exact HU | exact HG].
  same_fix Hse. rewrite H0sp. f_equal. lia.
Qed.

Lemma DMI_store : forall M' a v, DMI M' -> (a = S + -144 + 16 \/ a = S + -144 + 24) ->
  DMI (wbytes M' (W a) (word_to_le_bytes 8 v)).
Proof.
  intros M' a v (Hsv & HU & HG) Ha. unfold B_IMG_END in *. split; [|split].
  - intros off w Hin. pose proof (slots_ok_in 144 SL_dtl off w eq_refl Hin) as Ho.
    assert (40 <= off).
    { unfold SL_dtl in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; lia|]). contradiction. }
    apply cell_store_other; [lia | (cbn; lia) | lia | rewrite length_N_to_le_bytes; lia
                            | rewrite length_N_to_le_bytes; cbn; lia | apply Hsv; exact Hin].
  - apply unch_store; [exact HU | lia | rewrite length_N_to_le_bytes; lia|].
    intros x Hx. rewrite length_N_to_le_bytes in Hx. unfold FP_dtl, inr in *. lia.
  - eapply mem_grows_trans; [exact HG | apply wbytes_grows].
Qed.

Lemma dtls_body : forall l, l = l0 -> rget l 4 = W TP -> rget l 10 = W TLS_DESC ->
  reach BSEGS rom (Z_to_bv 64 0x1d5a88) l M Post.
Proof.
  intros l El H4 H10. pose proof Hl0 as Hl. rewrite <- El in Hl.
  assert (Hse : same_except KSI_dtl l0 l) by (rewrite El; apply same_except_refl).
  pose proof H0sp as H2. rewrite <- El in H2.
  assert (HSLe : SL_dtl = SL_dtl) by reflexivity. unfold SL_dtl at 1 in HSLe. rewrite <- El in HSLe. clear El.
  pose proof Hwf as (HT & Hctx & Hthr & Hfs). pose proof Hsep as (Hs1 & Hs2 & Hs3 & Hs4).
  unfold B_IMG_END in *.
  regs_open l Hl. subst sp tp a0. cbn [rget lget] in HSLe.
  (* [comment removed for export] *)
  wp_dtl [0x1d5ac0]. mem_auto.
  assert (HSL : slots_ok 144 SL_dtl = true) by reflexivity.
  match goal with |- reach _ _ _ _ ?Mx _ => replace Mx with (saves M (S + -144) SL_dtl) by (rewrite <- HSLe; reflexivity) end.
  assert (HD1 : DMI (saves M (S + -144) SL_dtl)).
  { split; [|split].
    - intros off v Hin. apply (saves_cell BSEGS SL_dtl M (S + -144) 144); [lia | lia | exact HSL | exact Hin].
    - apply (saves_unch SL_dtl M M (S + -144) 144); [lia | lia | exact HSL | | apply unch_refl].
      intros x Hx. unfold FP_dtl, inr in *. lia.
    - apply saves_grows. }
  set (M1 := saves M (S + -144) SL_dtl) in *. clear HSLe.
  assert (Hok1 : fsrt_ok M1 fs T ctx thr).
  { destruct HD1 as (_ & HU1 & _). eapply fsrt_ok_unch; [exact Hwf | exact HU1 | | exact Hok].
    intros y Hy. split; [unfold FP_dtl, inr, B_IMG_END in *; lia | eapply fsrt_sep_dom; [exact Hsep | exact Hy]]. }
  assert (Hw1 : wr_ok BSEGS M1 (S - 144) 144) by (destruct HD1 as (_ & _ & HG1); eapply wr_ok_grows; [exact HG1 | exact Hw]).
  clearbody M1. clear HSL.
  pose proof Hok1 as (_ & _ & Hd0 & _ & _ & _ & _ & _ & _ & _ & _ & Hgcf & Hf137 & Hgv & Hverb & Hgoff & HcT & _ & _ & (beg & Hbeg & Hbeg0) & _).
  unfold TP, TLS_DESC, G_CF, C_CF, G_VERB, C_VERB, G_DTLSOFF in *.
  assert (Hepi : forall l' , length l' = 32%nat -> same_except KSI_dtl l0 l' -> rget l' 2 = W (S + -144) ->
            reach BSEGS rom (Z_to_bv 64 0x1d5c64) l' M1 Post).
  { intros l' Hl' Hse' H2'. apply dtls_epi; assumption. }
  wp_dtl [0x1d5c64; 0x1d5cec; 0x1d5b10; 0x1d5ba4; 0x1d5ca4]. mem_auto.
  split; intros Hb0; [apply Hepi; [reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity]|]. clear Hb0.
  mem_auto. eexists. split; [apply load_cell; [exact Hverb | lia]|]. mem_auto.
  change (v_lw (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) mod 2 ^ (8 * Z.of_nat 4)))) with (W 0).
  change (bv_unsigned (Z_to_bv 64 3)) with 3. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  split; intros Hb1; [exfalso; lia|]. clear Hb1.
  rewrite add_W.
  eexists. split; [apply load_cell8; exact HcT|].
  rewrite (Wu T) by lia. change (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1).
  split; intros Hb2; [exfalso; lia|]. clear Hb2.
  split; intros Hb3; [|exfalso; lia].
  split; intros Hb4; [exfalso; lia|]. clear Hb4.
  mem_auto.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 255)) with 255.
  split; intros Hb5; [|exfalso; lia]. clear Hb5.
  change (v_slli (Z_to_bv 64 1) 4) with (W 16). rewrite add_W, addi_W. replace (T + 16 + 8) with (T + 24) by lia.
  eexists. split; [apply load_cell8; solve_cell|].
  rewrite (Wu beg) by lia.
  split; intros Hb6; [exfalso; lia|]. clear Hb6.
  apply dtls_epi; [ | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity].
  apply DMI_store; [apply DMI_store; [exact HD1 | left; reflexivity] | right; reflexivity].
Qed.
End Dtls.

Theorem dtls_cps : forall rom Post M fs T ctx thr S l,
  fsrt_ok M fs T ctx thr -> fsrt_wf fs T ctx thr ->
  B_IMG_END <= S - 144 /\ S < 2 ^ 63 -> wr_ok BSEGS M (S - 144) 144 -> fsrt_sep (S - 144) 144 fs T ctx thr ->
  length l = 32%nat -> rget l 2 = W S -> rget l 4 = W TP -> rget l 10 = W TLS_DESC ->
  (forall l' M', length l' = 32%nat -> same_except KS_dtl l l' -> rget l' 10 = W 0 ->
                 unch M M' (FP_dtl S) -> mem_grows M M' ->
                 reach BSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach BSEGS rom (Z_to_bv 64 0x1d5a88) l M Post.
Proof.
  intros rom Post M fs T ctx thr S l; intros.
  eapply (dtls_body rom Post M fs T ctx thr S) with (l0 := l); eauto.
Qed.

(* [comment removed for export] *)
Ltac wp_itg stops := wp_go 0x1aeca0 31%nat C_ic_tlsga_eq C_ic_tlsga stops.

Section IcTlsga.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (fs T ctx thr S : Z).
Hypothesis Hok : fsrt_ok M fs T ctx thr.
Hypothesis Hwf : fsrt_wf fs T ctx thr.
Hypothesis HS : B_IMG_END <= S - 176 /\ S < 2 ^ 63.
Hypothesis Hw : wr_ok BSEGS M (S - 176) 176.
Hypothesis Hsep : fsrt_sep (S - 176) 176 fs T ctx thr.

Definition KS_itg : list nat := [6; 10; 11; 12; 13]%nat.
Definition KSI_itg : list nat := [1; 2; 6; 8; 9; 10; 11; 12; 13; 18]%nat.
Definition FP_itg (x : word) : Prop := inr x (S - 176) 176.

Variable l0 : regfile.
Hypothesis Hl0 : length l0 = 32%nat.
Hypothesis H0sp : rget l0 2 = W S.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KS_itg l0 l' -> rget l' 10 = W TP ->
  unch M M' FP_itg -> mem_grows M M' ->
  reach BSEGS rom (v_jalr (rget l0 1) 0) l' M' Post.

Definition SL_itg : list (Z * word) := [(24, rget l0 1); (16, rget l0 8); (8, rget l0 9); (0, rget l0 18)].

(* [comment removed for export] *)
Definition IMI (M' : mem) : Prop :=
  (forall off v, In (off, v) SL_itg -> cell BSEGS M' (S + -32 + off) 8 v)
  /\ unch M M' FP_itg /\ mem_grows M M' /\ fsrt_ok M' fs T ctx thr.

Lemma IMI_step : forall M' M'' lo n, IMI M' -> unch M' M'' (fun x => inr x lo n) -> mem_grows M' M'' ->
  S - 176 <= lo -> lo + n <= S - 32 -> IMI M''.
Proof.
  intros M' M'' lo n (Hsv & HU & HG & Hok') HU' HG' Hlo Hhi. unfold B_IMG_END in *. split; [|split; [|split]].
  - intros off v Hin. pose proof (slots_ok_in 32 SL_itg off v eq_refl Hin) as Ho.
    eapply cell_unch; [exact HU' | lia | (cbn; lia) | | apply Hsv; exact Hin].
    intros x Hx Hx2. cbn in Hx. unfold inr in *. lia.
  - eapply unch_trans; [exact HU|]. eapply unch_weaken; [exact HU'|]. intros x Hx. unfold FP_itg, inr in *. lia.
  - eapply mem_grows_trans; eassumption.
  - eapply fsrt_ok_unch; [exact Hwf | exact HU' | | exact Hok'].
    intros y Hy. split; [unfold inr, B_IMG_END in *; lia|].
    eapply fsrt_sep_dom; [eapply (fsrt_sep_sub _ _ lo n); [exact Hsep | lia | lia] | exact Hy].
Qed.

Definition istable (l : regfile) : Prop :=
  length l = 32%nat /\ same_except KSI_itg l0 l /\ rget l 2 = W (S + -32) /\ rget l 4 = W TP /\ rget l 8 = W TLS_DESC.

Ltac open_istable H l :=
  let Hl := fresh "Hl" in let Hse := fresh "Hse" in
  destruct H as (Hl & Hse & ?H2 & ?H4 & ?H8); regs_open l Hl.
Ltac prove_istable Hse :=
  split; [reflexivity|]; split; [eapply same_except_trans; [exact Hse | same_ex]|]; cbn [rget lget]; repeat split; reflexivity.

(* [comment removed for export] *)
Lemma itg_epi : forall l M', IMI M' -> istable l -> rget l 9 = W TP -> reach BSEGS rom (Z_to_bv 64 0x1aed00) l M' Post.
Proof.
  intros l M' (Hsv & HU & HG & _) Hst H9. unfold B_IMG_END in *.
  pose proof (Hsv 24 _ ltac:(unfold SL_itg; in_list)) as Csv1. pose proof (Hsv 16 _ ltac:(unfold SL_itg; in_list)) as Csv8.
  pose proof (Hsv 8 _ ltac:(unfold SL_itg; in_list)) as Csv9. pose proof (Hsv 0 _ ltac:(unfold SL_itg; in_list)) as Csv18.
  clear Hsv. replace (S + -32 + 0) with (S + -32) in Csv18 by lia. open_istable Hst l. subst sp tp s0 s1.
  wp_itg (@nil Z). mem_auto.
  apply K; [reflexivity | | reflexivity | exact HU | exact HG].
  same_fix Hse. rewrite H0sp. f_equal. lia.
Qed.

Lemma itg_body : forall l, l = l0 -> rget l 4 = W TP -> rget l 10 = W TLS_DESC ->
  reach BSEGS rom (Z_to_bv 64 0x1aeca0) l M Post.
Proof.
  intros l El H4 H10. pose proof Hl0 as Hl. rewrite <- El in Hl.
  assert (Hse : same_except KSI_itg l0 l) by (rewrite El; apply same_except_refl).
  pose proof H0sp as H2. rewrite <- El in H2.
  assert (HSLe : SL_itg = SL_itg) by reflexivity. unfold SL_itg at 1 in HSLe. rewrite <- El in HSLe. clear El.
  pose proof Hwf as (HT & Hctx & Hthr & Hfs).
  unfold B_IMG_END in *.
  regs_open l Hl. subst sp tp a0. cbn [rget lget] in HSLe.
  wp_itg (@nil Z). mem_auto.
  assert (HSL : slots_ok 32 SL_itg = true) by reflexivity.
  match goal with |- reach _ _ _ _ ?Mx _ => replace Mx with (saves M (S + -32) SL_itg)
    by (rewrite <- HSLe; cbn [saves]; replace (S + -32 + 0) with (S + -32) by lia; reflexivity) end.
  assert (HI1 : IMI (saves M (S + -32) SL_itg)).
  { assert (HU1 : unch M (saves M (S + -32) SL_itg) FP_itg).
    { apply (saves_unch SL_itg M M (S + -32) 32); [lia | lia | exact HSL | | apply unch_refl].
      intros x Hx. unfold FP_itg, inr in *. lia. }
    split; [|split; [|split]].
    - intros off v Hin. apply (saves_cell BSEGS SL_itg M (S + -32) 32); [lia | lia | exact HSL | exact Hin].
    - exact HU1.
    - apply saves_grows.
    - eapply fsrt_ok_unch; [exact Hwf | exact HU1 | | exact Hok].
      intros y Hy. split; [unfold FP_itg, inr, B_IMG_END in *; lia | eapply fsrt_sep_dom; [exact Hsep | exact Hy]]. }
  set (M1 := saves M (S + -32) SL_itg) in *. clearbody M1. clear HSLe HSL.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 1857412) with (Z_to_bv 64 0x1c5784) by reflexivity.
  pose proof HI1 as (_ & _ & HG1 & Hok1). pose proof Hok1 as (Hini & _).
  eapply (tryinit_cps rom Post M1 (S + -32)); [exact Hini | unfold B_IMG_END; lia
    | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG1 | exact Hw] | lia | lia] | reflexivity | reflexivity |].
  intros l2 M2 Hl2 Hse2 H10' HU2 HG2. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1764540) 0) with (Z_to_bv 64 0x1aecbc) by reflexivity.
  regs_open l2 Hl2. se_subst Hse2. clear Hse2. cbn [rget lget] in H10'. match type of H10' with ?x = _ => subst x end.
  assert (HI2 : IMI M2) by (eapply (IMI_step M1 M2 (S + -32 - 16) 16); [exact HI1 | exact HU2 | exact HG2 | lia | lia]).
  clear HI1 HG1 Hok1 Hini HU2 HG2.
  (* [comment removed for export] *)
  pose proof HI2 as (_ & _ & HG2 & Hok2). pose proof Hok2 as (_ & Hreal & _). unfold R_TLSGA in *.
  wp_itg (@nil Z). mem_auto.
  replace (v_jalr (Z_to_bv 64 5653488) 0) with (Z_to_bv 64 0x5643f0) by reflexivity.
  eapply (tlsga_cps rom Post M2 fs T ctx thr); [exact Hok2 | reflexivity | reflexivity | reflexivity |].
  intros l3 Hl3 Hse3 H10''. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1764560) 0) with (Z_to_bv 64 0x1aecd0) by reflexivity.
  regs_open l3 Hl3. se_subst Hse3. clear Hse3. cbn [rget lget] in H10''. match type of H10'' with ?x = _ => subst x end.
  wp_itg [0x1aed00; 0x1aecd8]. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  (* [comment removed for export] *)
  wp_itg (@nil Z).
  replace (Z_to_bv 64 1867824) with (Z_to_bv 64 0x1c8030) by reflexivity.
  eapply (curthread_cps rom Post M2 fs T ctx thr (S + -32)); [exact Hok2 | exact Hwf | unfold B_IMG_END; lia
    | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG2 | exact Hw] | lia | lia]
    | eapply (fsrt_sep_sub _ _ (S + -32 - 16) 16); [exact Hsep | lia | lia] | reflexivity | reflexivity | reflexivity |].
  intros l4 M4 Hl4 Hse4 H10''' HU4 HG4. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1764572) 0) with (Z_to_bv 64 0x1aecdc) by reflexivity.
  regs_open l4 Hl4. se_subst Hse4. clear Hse4. cbn [rget lget] in H10'''. match type of H10''' with ?x = _ => subst x end.
  assert (HI4 : IMI M4) by (eapply (IMI_step M2 M4 (S + -32 - 16) 16); [exact HI2 | exact HU4 | exact HG4 | lia | lia]).
  clear HI2 HG2 Hok2 Hreal HU4 HG4.
  pose proof HI4 as (_ & _ & HG4 & Hok4).
  pose proof Hok4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (tb & te & Htb & Hte) & _).
  wp_itg (@nil Z). rewrite (Wu thr) by lia.
  split; intros Hb; [exfalso; lia|]. clear Hb. mem_auto.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 1923720) with (Z_to_bv 64 0x1d5a88) by reflexivity.
  eapply (dtls_cps rom Post M4 fs T ctx thr (S + -32)); [exact Hok4 | exact Hwf | unfold B_IMG_END; lia
    | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG4 | exact Hw] | lia | lia]
    | eapply (fsrt_sep_sub _ _ (S + -32 - 144) 144); [exact Hsep | lia | lia] | reflexivity | reflexivity | reflexivity | reflexivity |].
  intros l5 M5 Hl5 Hse5 H10'''' HU5 HG5. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1764608) 0) with (Z_to_bv 64 0x1aed00) by reflexivity.
  regs_open l5 Hl5. se_subst Hse5. clear Hse5.
  assert (HI5 : IMI M5) by (eapply (IMI_step M4 M5 (S + -32 - 144) 144); [exact HI4 | exact HU5 | exact HG5 | lia | lia]).
  apply itg_epi; [exact HI5 | prove_istable Hse | reflexivity].
Qed.
End IcTlsga.

Theorem ic_tlsga_cps : forall rom Post M fs T ctx thr S l,
  fsrt_ok M fs T ctx thr -> fsrt_wf fs T ctx thr ->
  B_IMG_END <= S - 176 /\ S < 2 ^ 63 -> wr_ok BSEGS M (S - 176) 176 -> fsrt_sep (S - 176) 176 fs T ctx thr ->
  length l = 32%nat -> rget l 2 = W S -> rget l 4 = W TP -> rget l 10 = W TLS_DESC ->
  (forall l' M', length l' = 32%nat -> same_except KS_itg l l' -> rget l' 10 = W TP ->
                 unch M M' (FP_itg S) -> mem_grows M M' ->
                 reach BSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach BSEGS rom (Z_to_bv 64 0x1aeca0) l M Post.
Proof.
  intros rom Post M fs T ctx thr S l; intros.
  eapply (itg_body rom Post M fs T ctx thr S) with (l0 := l); eauto.
Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require Import BMemToShadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wp_m2 stops := wp_go 0x1a2504 79%nat C_m2s_eq C_m2s stops.

Theorem m2s_cps : forall rom (Post : word -> regfile -> mem -> Prop) M x l,
  rt_ok M -> inmem x ->
  length l = 32%nat -> rget l 10 = W x ->
  (forall l', length l' = 32%nat -> same_except KS_M2S l l' -> rget l' 10 = W (sha x) ->
              reach BSEGS rom (v_jalr (rget l 1) 0) l' M Post) ->
  reach BSEGS rom (Z_to_bv 64 0x1a2504) l M Post.
Proof.
  intros rom Post M x l (H1 & H2 & H3 & H4 & H5 & (v6 & H6) & H7 & H8 & _) Hx Hl H10 K.
  unfold G_SB, C_SB, G_MIDBEG, C_MIDBEG, G_MIDEND, C_MIDEND, G_HIEND, C_HIEND in *.
  regs_open l Hl. subst a0. cbn [rget lget] in K.
  assert (Hxr : 0 <= x < 2 ^ 64) by (unfold inmem, LOMEM_END, HIMEM_BEG, HIMEM_END in Hx; lia).
  assert (Esh : v_add (W SB) (v_srli (W x) 3) = W (sha x)).
  { rewrite srli3_W by lia. rewrite add_W. f_equal. unfold sha. lia. }
  wp_m2 [0x1a2570]. mem_auto. rewrite lowmem_end_val. rewrite Esh.
  split; intros Hb1.
  - apply K; [reflexivity | same_ex | reflexivity].
  - mem_auto. rewrite midbeg_m1_val.
    split; intros Hb2.
    + mem_auto. rewrite hishadow_end_val. rewrite !Wu in * by (unfold SB, HIMEM_BEG, HIMEM_END in *; lia).
      split; intros Hb3; [exfalso; unfold inmem, LOMEM_END, HIMEM_BEG, HIMEM_END, SB in *; lia|].
      split; intros Hb4; [exfalso; unfold inmem, LOMEM_END, HIMEM_BEG, HIMEM_END, SB in *; lia|].
      apply K; [reflexivity | same_ex | reflexivity].
    + exfalso. rewrite !Wu in Hb2 by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma wbytes_nth' : forall bs m (a : word) j,
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z -> (j < length bs)%nat ->
  wbytes m a bs (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
Proof.
  induction bs as [|b rest IH]; intros m a j Hnw Hj; [cbn in Hj; lia|].
  cbn [length] in Hnw, Hj. cbn [wbytes].
  destruct j as [|j'].
  - cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    destruct rest as [|b' rest'].
    + cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
    + cbn [length] in Hnw.
      rewrite wbytes_below; [rewrite bv_eqb_refl; reflexivity | | ];
        rewrite (u_add1 a) by lia; cbn [length]; lia.
  - cbn [nth]. assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
    replace (bv_unsigned a + Z.of_nat (S j'))%Z with (bv_unsigned (a + 1) + Z.of_nat j')%Z by lia.
    apply IH; lia.
Qed.

Lemma zeros_store8 : forall M a, 0 <= a -> a + 8 < 2 ^ 64 -> zeros (wbytes M (W a) (word_to_le_bytes 8 (W 0))) a 8.
Proof.
  intros M a Ha Hn i Hi.
  pose proof (wbytes_nth' (word_to_le_bytes 8 (W 0)) M (W a) (Z.to_nat i)) as H.
  rewrite length_N_to_le_bytes, Wu, Z2Nat.id in H by lia. rewrite H by lia.
  f_equal. assert (Hj : (Z.to_nat i < 8)%nat) by lia. revert Hj. generalize (Z.to_nat i). intros j Hj.
  do 8 (destruct j as [|j]; [reflexivity|]). lia.
Qed.

(* [comment removed for export] *)
Lemma ring0_release : forall M0 M' (P : word -> Prop) F kk,
  zeros M0 F 16384 -> 0 <= F -> F + 16384 < 2 ^ 64 -> 0 <= kk < 16384 ->
  unch M0 M' P -> (forall x, P x -> inr x F 16384 -> bv_unsigned x = F + kk) ->
  M' (W (F + kk)) = Some (Z_to_bv 8 0) -> zeros M' F 16384.
Proof.
  intros M0 M' P F kk Hz HF HF2 Hk HU HP Hk0 i Hi.
  destruct (Z.eq_dec i kk) as [->|Hne]; [exact Hk0|].
  rewrite HU; [apply Hz; exact Hi|]. intros HPx.
  pose proof (HP _ HPx) as Hx. unfold inr in Hx. rewrite Wu in Hx by lia. lia.
Qed.

(* [comment removed for export] *)
Ltac wp_m0 stops := wp_go 0x1a1328 93%nat C_malloc0_eq C_malloc0 stops.

Lemma and_ones14 : forall h, 0 <= h < 2 ^ 64 -> v_and (W h) (W 16383) = W (h mod 16384).
Proof.
  intros h Hh. rewrite and_W by lia. f_equal. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. reflexivity.
Qed.

Section Malloc0.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (fs T ctx thr h S : Z).
Hypothesis Hrt : rt_ok M.
Hypothesis Hok : fsrt_ok M fs T ctx thr.
Hypothesis Hwf : fsrt_wf fs T ctx thr.
Hypothesis Hhint : cell BSEGS M fs 8 (W h).
Hypothesis Hh : 0 <= h < 2 ^ 64.
Hypothesis Hidle : zeros M (fs + 4096) 16384.
(* [comment removed for export] *)
Hypothesis Hfsm : B_IMG_END <= fs /\ fs + 11571200 <= HIMEM_END /\ (fs + 11571200 <= SB \/ HIMEM_BEG <= fs).
Hypothesis Hwh : wr_ok BSEGS M fs 8.
Hypothesis Hwfl : wr_ok BSEGS M (fs + 4096) 16384.
Hypothesis Hwfr : wr_ok BSEGS M (fs + 36864) 1048576.
Hypothesis Hwsh : wr_ok BSEGS M (sha (fs + 36864)) 131072.
Hypothesis HS : B_IMG_END <= S - 208 /\ S < 2 ^ 63.
Hypothesis HSz : S <= SB \/ HIMEM_BEG <= S - 208.
Hypothesis Hw : wr_ok BSEGS M (S - 208) 208.
Hypothesis Hsep : fsrt_sep (S - 208) 208 fs T ctx thr.
Hypothesis Hdjfs : fs + 11571200 <= S - 208 \/ S <= fs.

Let pos := h mod 16384.
Let FB := fs + 36864 + 64 * pos.

Definition KSI_m0 : list nat := [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 28; 29; 30; 31]%nat.
Definition FP_m0 (x : word) : Prop :=
  inr x (S - 208) 208 \/ inr x fs 8 \/ inr x (fs + 4096 + h mod 16384) 1
  \/ inr x (fs + 36864 + 64 * (h mod 16384) + 24) 8 \/ inr x (fs + 36864 + 64 * (h mod 16384) + 56) 8
  \/ inr x (sha (fs + 36864 + 64 * (h mod 16384))) 8.

Variable l0 : regfile.
Hypothesis Hl0 : length l0 = 32%nat.
Hypothesis H0sp : rget l0 2 = W S.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KSC l0 l' -> rget l' 10 = W FB ->
  cell BSEGS M' fs 8 (W (h + 1)) -> cell BSEGS M' (fs + 4096 + pos) 1 (W 1) ->
  cell BSEGS M' (FB + 24) 8 (W S) -> cell BSEGS M' (FB + 56) 8 (W (fs + 4096 + pos)) -> zeros M' (sha FB) 8 ->
  unch M M' FP_m0 -> mem_grows M M' ->
  reach BSEGS rom (v_jalr (rget l0 1) 0) l' M' Post.

Definition SL_m0 : list (Z * word) := [(24, rget l0 1); (16, rget l0 8); (8, rget l0 9); (0, rget l0 18)].
Definition FPw (x : word) : Prop := inr x (S - 208) 208.

(* [comment removed for export] *)
Definition SMI (M' : mem) : Prop :=
  (forall off v, In (off, v) SL_m0 -> cell BSEGS M' (S + -32 + off) 8 v) /\ unch M M' FPw /\ mem_grows M M'.

Lemma pos_range : 0 <= pos < 16384.
Proof. subst pos. apply Z.mod_pos_bound. lia. Qed.

Lemma FPw_facts : forall y, FPw y -> B_IMG_END <= bv_unsigned y /\ ~ fsrt_dom fs T ctx thr y
  /\ ~ inr y fs 11571200 /\ ~ (SB <= bv_unsigned y < HIMEM_BEG).
Proof.
  intros y Hy. split; [unfold FPw, inr in *; lia|]. split; [eapply fsrt_sep_dom; [exact Hsep | exact Hy]|].
  unfold FPw, inr in *. lia.
Qed.

Lemma SMI_ok : forall M', SMI M' -> fsrt_ok M' fs T ctx thr /\ rt_ok M' /\ cell BSEGS M' fs 8 (W h)
  /\ zeros M' (fs + 4096) 16384.
Proof.
  intros M' (_ & HU & HG). unfold B_IMG_END, SB, HIMEM_BEG, HIMEM_END in *. split; [|split; [|split]].
  - eapply fsrt_ok_unch; [exact Hwf | exact HU | | exact Hok]. intros y Hy. destruct (FPw_facts y Hy) as (H1 & H2 & _). auto.
  - eapply rt_ok_unch; [exact HU | | exact Hrt]. intros y Hy. apply (FPw_facts y Hy).
  - eapply cell_unch; [exact HU | lia | (cbn; lia) | | exact Hhint].
    intros x Hx Hx2. destruct (FPw_facts x Hx2) as (_ & _ & H3 & _). apply H3. cbn in Hx. unfold inr in *. lia.
  - eapply zeros_grows_unch; [exact HU | lia | lia | | exact Hidle].
    intros x Hx Hx2. destruct (FPw_facts x Hx2) as (_ & _ & H3 & _). apply H3. unfold inr in *. lia.
Qed.

Lemma malloc0_body : forall l, l = l0 -> rget l 4 = W TP -> reach BSEGS rom (Z_to_bv 64 0x1a1328) l M Post.
Proof.
  intros l El H4. pose proof Hl0 as Hl. rewrite <- El in Hl.
  assert (Hse : same_except KSI_m0 l0 l) by (rewrite El; apply same_except_refl).
  pose proof H0sp as H2. rewrite <- El in H2.
  assert (HSLe : SL_m0 = SL_m0) by reflexivity. unfold SL_m0 at 1 in HSLe. rewrite <- El in HSLe. clear El.
  pose proof Hwf as (HT & Hctx & Hthr & Hfs). pose proof pos_range as Hpos.
  unfold B_IMG_END in *.
  regs_open l Hl. subst sp tp. cbn [rget lget] in HSLe.
  (* [comment removed for export] *)
  wp_m0 (@nil Z). mem_auto. replace (S + -32 + 32) with S by lia.
  assert (HSL : slots_ok 32 SL_m0 = true) by reflexivity.
  match goal with |- reach _ _ _ _ ?Mx _ => replace Mx with (saves M (S + -32) SL_m0)
    by (rewrite <- HSLe; cbn [saves]; replace (S + -32 + 0) with (S + -32) by lia; reflexivity) end.
  assert (HI1 : SMI (saves M (S + -32) SL_m0)).
  { split; [|split].
    - intros off v Hin. apply (saves_cell BSEGS SL_m0 M (S + -32) 32); [lia | lia | exact HSL | exact Hin].
    - apply (saves_unch SL_m0 M M (S + -32) 32); [lia | lia | exact HSL | | apply unch_refl].
      intros x Hx. unfold FPw, inr in *. lia.
    - apply saves_grows. }
  set (M1 := saves M (S + -32) SL_m0) in *. clearbody M1. clear HSLe HSL.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 1733984) with (Z_to_bv 64 0x1a7560) by reflexivity.
  wp_go 0x1a74d4 36%nat C_stubs_eq C_stubs (@nil Z).
  replace (Z_to_bv 64 1764512) with (Z_to_bv 64 0x1aeca0) by reflexivity.
  destruct (SMI_ok _ HI1) as (Hok1 & _). pose proof HI1 as (_ & _ & HG1).
  eapply (ic_tlsga_cps rom Post M1 fs T ctx thr (S + -32)); [exact Hok1 | exact Hwf | unfold B_IMG_END; lia
    | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HG1 | exact Hw] | lia | lia]
    | eapply (fsrt_sep_sub _ _ (S + -32 - 176) 176); [exact Hsep | lia | lia]
    | reflexivity | reflexivity | reflexivity | reflexivity |].
  intros l2 M2 Hl2 Hse2 H10' HU2 HG2. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1708876) 0) with (Z_to_bv 64 0x1a134c) by reflexivity.
  regs_open l2 Hl2. se_subst Hse2. clear Hse2. cbn [rget lget] in H10'. match type of H10' with ?x = _ => subst x end.
  assert (HI2 : SMI M2).
  { destruct HI1 as (Hsv1 & HU1 & _). split; [|split].
    - intros off v Hin. pose proof (slots_ok_in 32 SL_m0 off v eq_refl Hin) as Ho.
      eapply cell_unch; [exact HU2 | lia | (cbn; lia) | | apply Hsv1; exact Hin].
      intros x Hx Hx2. cbn in Hx. unfold FP_itg, inr in *. lia.
    - eapply unch_trans; [exact HU1|]. eapply unch_weaken; [exact HU2|]. intros x Hx. unfold FP_itg, FPw, inr in *. lia.
    - eapply mem_grows_trans; eassumption. }
  clear HI1 Hok1 HG1 HU2 HG2.
  (* [comment removed for export] *)
  destruct (SMI_ok _ HI2) as (Hok2 & Hrt2 & Hhint2 & Hidle2). pose proof HI2 as (Hsv2 & HUw2 & HGw2).
  pose proof Hok2 as (_ & _ & _ & _ & _ & _ & Hfsc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hssl & Hgc).
  assert (Hwh2 : wr_ok BSEGS M2 fs 8) by (eapply wr_ok_grows; [exact HGw2 | exact Hwh]).
  assert (Hwfl2 : wr_ok BSEGS M2 (fs + 4096) 16384) by (eapply wr_ok_grows; [exact HGw2 | exact Hwfl]).
  assert (Hwfr2 : wr_ok BSEGS M2 (fs + 36864) 1048576) by (eapply wr_ok_grows; [exact HGw2 | exact Hwfr]).
  unfold TP in *.
  wp_m0 [0x1a13d0; 0x1a1360; 0x1a13f0; 0x1a13bc]. mem_auto.
  rewrite (Wu fs) by lia.
  split; intros Hb0; [exfalso; lia|]. clear Hb0.
  eexists. split; [apply load_cell; [exact Hgc | lia]|].
  eexists. split; [apply load_cell8; exact Hssl|].
  assert (E1 : v_sll (Z_to_bv 64 1) (v_addi (Z_to_bv 64 20) (-6)) = W 16384) by (apply bv_eq; reflexivity).
  assert (E2 : v_xori (v_sll (Z_to_bv 64 (-1)) (v_addi (Z_to_bv 64 20) (-6))) (-1) = W 16383) by (apply bv_eq; reflexivity).
  assert (E3 : v_sll (Z_to_bv 64 1) (v_addi (Z_to_bv 64 20) (-5)) = W 32768) by (apply bv_eq; reflexivity).
  assert (E4 : v_addiw (W 16384) 0 = W 16384) by (apply bv_eq; reflexivity).
  rewrite ?E1, ?E2, ?E3, ?E4. clear E1 E2 E3 E4.
  change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) mod 2 ^ (8 * Z.of_nat 1)))) with 0.
  split; [intros _ | intros Hb; exfalso; lia].
  change (bv_signed (W 16384)) with 16384. change (bv_signed (Z_to_bv 64 0)) with 0.
  split; intros Hb1; [exfalso; lia|]. clear Hb1.
  (* [comment removed for export] *)
  eexists. split; [apply load_cell8; exact Hhint2|].
  rewrite (and_ones14 h Hh). fold pos. rewrite !add_W.
  eexists. split; [apply (load1_zeros BSEGS M2 (fs + 4096) 16384); [exact Hidle2 | lia]|].
  change (bv_unsigned (W 0)) with 0.
  split; [intros _ | intros Hb; exfalso; lia].
  rewrite slli_W by lia. change (2 ^ 6) with 64. rewrite !add_W, !addi_W.
  replace (fs + 4096 + 32768 + pos * 64) with FB by (unfold FB; lia).
  assert (HFB : FB = fs + 36864 + 64 * pos) by reflexivity.
  unfold B_IMG_END, SB, HIMEM_BEG, HIMEM_END in Hfsm.
  (* [comment removed for export] *)
  mem_auto.
  match goal with |- reach _ _ _ _ ?Mx _ => set (M3 := Mx) end.
  assert (HU3 : unch M2 M3 (fun x => inr x fs 8 \/ inr x (fs + 4096 + pos) 1 \/ inr x (FB + 24) 8 \/ inr x (FB + 56) 8)).
  { unfold M3. solve_unch ltac:(unfold inr in *; lia). }
  assert (HG3 : mem_grows M2 M3) by (unfold M3; solve_grows).
  assert (Chint3 : cell BSEGS M3 fs 8 (W (h + 1))) by (unfold M3; solve_cell).
  assert (Cflag3 : cell BSEGS M3 (fs + 4096 + pos) 1 (W 1)) by (unfold M3; solve_cell).
  assert (Crs3 : cell BSEGS M3 (FB + 24) 8 (W S)) by (unfold M3; solve_cell).
  assert (Cfp3 : cell BSEGS M3 (FB + 56) 8 (W (fs + 4096 + pos))) by (unfold M3; solve_cell).
  clearbody M3.
  (* [comment removed for export] *)
  assert (Hrt3 : rt_ok M3).
  { eapply rt_ok_unch; [exact HU3 | | exact Hrt2]. intros y Hy. unfold B_IMG_END, inr in *. lia. }
  assert (HFBm : inmem FB) by (unfold inmem, LOMEM_END, HIMEM_BEG, HIMEM_END; lia).
  eapply (m2s_cps rom Post M3 FB); [exact Hrt3 | exact HFBm | reflexivity | reflexivity |].
  intros l4 Hl4 Hse4 H10'. cbn [rget lget].
  replace (v_jalr (Z_to_bv 64 1709144) 0) with (Z_to_bv 64 0x1a1458) by reflexivity.
  regs_open l4 Hl4. se_subst Hse4. clear Hse4. cbn [rget lget] in H10'. match type of H10' with ?x = _ => subst x end.
  (* [comment removed for export] *)
  assert (Hsha : sha FB = sha (fs + 36864) + 8 * pos).
  { rewrite HFB. replace (fs + 36864 + 64 * pos) with (fs + 36864 + 8 * (8 * pos)) by lia. apply sha_add8. }
  assert (Hshr : SB <= sha FB /\ sha FB + 8 <= HIMEM_BEG).
  { assert (Hq : (fs + 36864) / 8 <= 17592185913344) by (apply Z.div_le_upper_bound; lia).
    assert (Hq0 : 0 <= (fs + 36864) / 8) by (apply Z.div_pos; lia).
    rewrite Hsha. unfold sha, SB, HIMEM_BEG. lia. }
  assert (Hwsh3 : wr_ok BSEGS M3 (sha (fs + 36864)) 131072).
  { eapply wr_ok_grows; [exact HG3|]. eapply wr_ok_grows; [exact HGw2 | exact Hwsh]. }
  assert (TS : forall off v, In (off, v) SL_m0 -> cell BSEGS M3 (S + -32 + off) 8 v).
  { intros off v Hin. pose proof (slots_ok_in 32 SL_m0 off v eq_refl Hin) as Ho.
    eapply cell_unch; [exact HU3 | lia | (cbn; lia) | | apply Hsv2; exact Hin].
    intros x Hx Hx2. cbn in Hx. unfold inr in *. lia. }
  pose proof (TS 24 _ ltac:(unfold SL_m0; in_list)) as Csv1. pose proof (TS 16 _ ltac:(unfold SL_m0; in_list)) as Csv8.
  pose proof (TS 8 _ ltac:(unfold SL_m0; in_list)) as Csv9. pose proof (TS 0 _ ltac:(unfold SL_m0; in_list)) as Csv18.
  replace (S + -32 + 0) with (S + -32) in Csv18 by lia. clear TS.
  unfold SB, HIMEM_BEG in Hshr, HSz.
  wp_m0 (@nil Z). mem_auto.
  replace (S + -32 + 32) with S by lia.
  assert (Hz4 : zeros (wbytes M3 (W (sha FB)) (word_to_le_bytes 8 (W 0))) (sha FB) 8) by (apply zeros_store8; lia).
  assert (HU4 : unch M3 (wbytes M3 (W (sha FB)) (word_to_le_bytes 8 (W 0))) (fun x => inr x (sha FB) 8)).
  { solve_unch ltac:(unfold inr in *; lia). }
  assert (TC : forall a (k : nat) v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= SB \/ HIMEM_BEG <= a) ->
            cell BSEGS M3 a k v -> cell BSEGS (wbytes M3 (W (sha FB)) (word_to_le_bytes 8 (W 0))) a k v).
  { intros a k v Ha Hk Hhi Hc. eapply cell_unch; [exact HU4 | lia | lia | | exact Hc].
    intros x Hx Hx2. unfold inr, SB, HIMEM_BEG in *. lia. }
  set (M4 := wbytes M3 (W (sha FB)) (word_to_le_bytes 8 (W 0))) in *.
  assert (HG4 : mem_grows M3 M4) by (unfold M4; solve_grows).
  clearbody M4.
  apply K; [reflexivity | | reflexivity | | | | | exact Hz4 | | ].
  - same_fix Hse. rewrite H0sp. reflexivity.
  - apply TC; [lia | cbn; lia | unfold SB, HIMEM_BEG; cbn; lia | exact Chint3].
  - apply TC; [lia | cbn; lia | unfold SB, HIMEM_BEG; cbn; lia | exact Cflag3].
  - apply TC; [lia | cbn; lia | unfold SB, HIMEM_BEG; cbn; lia | exact Crs3].
  - apply TC; [lia | cbn; lia | unfold SB, HIMEM_BEG; cbn; lia | exact Cfp3].
  - eapply unch_trans; [eapply unch_weaken; [exact HUw2|]
                       | eapply unch_trans; [eapply unch_weaken; [exact HU3|] | eapply unch_weaken; [exact HU4|]]].
    + intros x Hx. left. exact Hx.
    + intros x Hx. right. fold pos. rewrite <- HFB. cbv beta in Hx. tauto.
    + intros x Hx. do 5 right. fold pos. rewrite <- HFB. exact Hx.
  - eapply mem_grows_trans; [exact HGw2|]. eapply mem_grows_trans; [exact HG3 | exact HG4].
Qed.
End Malloc0.

(* [comment removed for export] *)
Theorem malloc0_cps : forall rom Post M fs T ctx thr h S l,
  rt_ok M -> fsrt_ok M fs T ctx thr -> fsrt_wf fs T ctx thr ->
  cell BSEGS M fs 8 (W h) -> 0 <= h < 2 ^ 64 -> zeros M (fs + 4096) 16384 ->
  B_IMG_END <= fs /\ fs + 11571200 <= HIMEM_END /\ (fs + 11571200 <= SB \/ HIMEM_BEG <= fs) ->
  wr_ok BSEGS M fs 8 -> wr_ok BSEGS M (fs + 4096) 16384 -> wr_ok BSEGS M (fs + 36864) 1048576 ->
  wr_ok BSEGS M (sha (fs + 36864)) 131072 ->
  B_IMG_END <= S - 208 /\ S < 2 ^ 63 -> (S <= SB \/ HIMEM_BEG <= S - 208) -> wr_ok BSEGS M (S - 208) 208 ->
  fsrt_sep (S - 208) 208 fs T ctx thr -> (fs + 11571200 <= S - 208 \/ S <= fs) ->
  length l = 32%nat -> rget l 2 = W S -> rget l 4 = W TP ->
  (forall l' M', let k := h mod 16384 in let FB := fs + 36864 + 64 * k in
     length l' = 32%nat -> same_except KSC l l' -> rget l' 10 = W FB ->
     cell BSEGS M' fs 8 (W (h + 1)) -> cell BSEGS M' (fs + 4096 + k) 1 (W 1) ->
     cell BSEGS M' (FB + 24) 8 (W S) -> cell BSEGS M' (FB + 56) 8 (W (fs + 4096 + k)) -> zeros M' (sha FB) 8 ->
     unch M M' (FP_m0 fs h S) -> mem_grows M M' ->
     reach BSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach BSEGS rom (Z_to_bv 64 0x1a1328) l M Post.
Proof.
  intros rom Post M fs T ctx thr h S l Hrt Hok Hwf Hhint Hh Hidle Hfsm Hwh Hwfl Hwfr Hwsh HS HSz Hw Hsep Hdj Hl H2 H4 K.
  eapply (malloc0_body rom Post M fs T ctx thr h S) with (l0 := l); eauto.
Qed.

Print Assumptions malloc0_cps.
