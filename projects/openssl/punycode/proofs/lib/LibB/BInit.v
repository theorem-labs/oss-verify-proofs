(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit StrKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import AShadow ASaves.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require Import BCode BCode2 BRt BImg BIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_wi stops := wp_go 0x272638 188%nat C_wp_init_eq C_wp_init stops.

Ltac fix_jalr target :=
  match goal with |- reach _ _ (v_jalr (Z_to_bv 64 ?x) ?i) _ _ _ =>
    replace (v_jalr (Z_to_bv 64 x) i) with (W target) by reflexivity end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KS_r1 : list nat :=
  [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 23; 24; 25; 26; 28; 29; 30; 31]%nat.
Definition FP_r1 (fs spv pkt : Z) (x : word) : Prop := inr x (spv - 336) 336 \/ inr x (pkt + 16) 16 \/ ring_FP fs x.

(* [comment removed for export] *)
Definition WI_SLOTS : list (Z * nat) :=
  [(120, 1%nat); (112, 8%nat); (104, 9%nat); (96, 18%nat); (88, 19%nat); (80, 20%nat); (72, 21%nat); (64, 22%nat);
   (56, 23%nat); (48, 24%nat); (40, 25%nat); (32, 26%nat)].

Section R1.
Variables (RTX : mem -> Prop) (RTXD : word -> Prop) (RSEP : Z -> Z -> Prop) (fs : Z).
Hypothesis IF : rt_iface RTX RTXD RSEP fs.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (pkt lb spv h : Z).
Hypothesis Hrt : rt_ok M.
Hypothesis Hrtx : RTX M.
Hypothesis Huar : uar_on M.
Hypothesis Hfs : fs_wf fs.
Hypothesis Hh : 0 <= h < 2 ^ 64.
Hypothesis Hhint : cell BSEGS M fs 8 (W h).
Hypothesis Hflags : zeros M (fs + 4096) 16384.
Hypothesis Hrwr : ring_wr M fs.
Hypothesis Hsp : B_IMG_END <= spv - 336 /\ spv < 2 ^ 63 /\ spv mod 32 = 0.
Hypothesis Hfr : wr_ok BSEGS M (spv - 336) 336.
Hypothesis Hs_fs : spv <= fs \/ fs + FS_SIZE <= spv - 336.
Hypothesis Hs_sh : spv <= SB \/ HIMEM_BEG <= spv - 336.
Hypothesis Hrsep : RSEP (spv - 336) 336.
(* [comment removed for export] *)
Hypothesis Hpkt : B_IMG_END <= pkt /\ memrange pkt 56 /\ pkt mod 8 = 0.
Hypothesis Hshp : zeros M (sha (pkt + 16)) 2.
Hypothesis Hwp : wr_ok BSEGS M (pkt + 16) 16.
Hypothesis Hs_pk : (spv <= pkt \/ pkt + 56 <= spv - 336) /\ (pkt + 56 <= fs \/ fs + 1085440 <= pkt).

Let k := h mod 16384.
Let FB := fs + 36864 + 64 * k.

Variable l0 : regfile.
Hypothesis Hl0 : length l0 = 32%nat.
Hypothesis H0sp : rget l0 2 = W spv.
Hypothesis H0tp : rget l0 4 = W TP.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KS_r1 l0 l' ->
  rget l' 2 = W (spv - 128) -> rget l' 8 = W spv -> rget l' 9 = W (spv - 128) ->
  rget l' 10 = W 40 -> rget l' 11 = W 0x2d61f -> rget l' 12 = W 110 ->
  rget l' 18 = W FB -> rget l' 19 = W lb -> rget l' 20 = W pkt -> rget l' 23 = W (sha FB) ->
  rget l' 24 = W FB -> rget l' 25 = W SB ->
  (forall off r, In (off, r) WI_SLOTS -> cell BSEGS M' (spv - 128 + off) 8 (rget l0 r)) ->
  cell BSEGS M' fs 8 (W (h + 1)) -> cell BSEGS M' (fs + 4096 + k) 1 (W 1) ->
  zeros M' (fs + 4096) k -> zeros M' (fs + 4096 + k + 1) (16383 - k) ->
  cell BSEGS M' (FB + 56) 8 (W (fs + 4096 + k)) ->
  cell BSEGS M' (pkt + 16) 8 (W 0) -> cell BSEGS M' (pkt + 24) 8 (W 0) ->
  unch M M' (FP_r1 fs spv pkt) -> mem_grows M M' ->
  reach BSEGS rom (W 0x272778) l' M' Post.

Lemma kb : 0 <= k < 16384.
Proof. unfold k. apply Z.mod_pos_bound. lia. Qed.

Lemma nums : fs + 36864 <= FB /\ FB + 64 <= fs + 1085440 /\ (B_IMG_END <= fs /\ (fs + FS_SIZE <= SB \/ HIMEM_BEG <= fs)) /\ fs + FS_SIZE <= HIMEM_END
  /\ SB <= sha FB /\ sha FB + 8 <= HIMEM_BEG /\ sha FB = sha (fs + 36864) + 8 * k.
Proof.
  destruct Hfs as (F1 & F2 & F3). pose proof kb as Hkb.
  assert (Es : sha FB = sha (fs + 36864) + 8 * k) by (unfold FB; apply sha_frame).
  assert (Hq : (fs + 36864) / 8 <= 17592185913344) by (unfold HIMEM_END, FS_SIZE in *; apply Z.div_le_upper_bound; lia).
  assert (Hq0 : 0 <= (fs + 36864) / 8) by (unfold HIMEM_BEG, B_IMG_END, SB, FS_SIZE in *; apply Z.div_pos; lia).
  clear - F1 F2 Hkb Es Hq Hq0. unfold FB, HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END, SB in *. repeat split; try lia.
  - rewrite Es. unfold sha, SB. lia.
  - rewrite Es. unfold sha, SB. lia.
Qed.

Definition SL_wi : list (Z * word) :=
  [(0, W 0); (120, rget l0 1); (112, rget l0 8); (104, rget l0 9); (96, rget l0 18); (88, rget l0 19); (80, rget l0 20);
   (72, rget l0 21); (64, rget l0 22); (56, rget l0 23); (48, rget l0 24); (40, rget l0 25); (32, rget l0 26)].

Lemma win_nums : (fs + FS_SIZE <= spv + -128 - 208 \/ spv + -128 <= fs)
  /\ (spv + -128 <= SB \/ HIMEM_BEG <= spv + -128 - 208)
  /\ (forall x, inr x (spv - 336) 336 -> ~ inr x fs FS_SIZE /\ B_IMG_END <= bv_unsigned x
                                       /\ ~ (SB <= bv_unsigned x < HIMEM_BEG)).
Proof.
  destruct Hsp as (Sp1 & Sp2 & Sp3). clear - Sp1 Sp2 Hs_fs Hs_sh.
  unfold inr, B_IMG_END, SB, HIMEM_BEG, FS_SIZE in *. split; [lia|]. split; [lia|]. intros x Hx. lia.
Qed.

(* [comment removed for export] *)
Lemma sh_pkt_apart : forall y, pkt <= y < pkt + 56 -> ~ (sha FB <= sha y < sha FB + 8).
Proof.
  intros y Hy. pose proof nums as (NF1 & NF2 & NF5 & NF4 & NS1 & NS2 & NS3). destruct Hs_pk as (_ & S2).
  destruct Hfs as (F1 & F2 & F3). pose proof kb as Hkb.
  assert (Hq : FB = 8 * (FB / 8)).
  { unfold FB. pose proof (Z.div_mod (fs + 36864 + 64 * k) 8 ltac:(lia)) as Hd.
    replace ((fs + 36864 + 64 * k) mod 8) with 0 in Hd; [lia|].
    symmetry. replace (fs + 36864 + 64 * k) with (fs + (4608 + 8 * k) * 8) by lia. rewrite Z.mod_add by lia. exact F3. }
  unfold sha. set (q := FB / 8) in *. clearbody q.
  destruct S2 as [Hlt|Hge].
  - assert (y / 8 < q) by (apply Z.div_lt_upper_bound; lia). lia.
  - assert (q + 8 <= y / 8) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma r1_body : forall l, l = l0 -> rget l 10 = W pkt -> rget l 11 = W lb ->
  reach BSEGS rom (W 0x272638) l M Post.
Proof.
  intros l El H10 H11. pose proof Hl0 as Hl. rewrite <- El in Hl.
  assert (Hse : same_except KS_r1 l0 l) by (rewrite El; apply same_except_refl).
  pose proof H0sp as H2. rewrite <- El in H2. pose proof H0tp as H4. rewrite <- El in H4.
  assert (HSLe : SL_wi = SL_wi) by reflexivity. unfold SL_wi at 1 in HSLe. rewrite <- El in HSLe. clear El.
  destruct Hsp as (Sp1 & Sp2 & Sp3). destruct win_nums as (Q1 & Q2 & Q3).
  unfold B_IMG_END in Sp1.
  regs_open l Hl. subst sp tp a0 a1. cbn [rget lget] in HSLe.
  wp_wi [0x272670]. mem_auto.
  assert (HSL : slots_ok 128 SL_wi = true) by reflexivity.
  match goal with |- reach _ _ _ _ ?Mx _ => replace Mx with (saves M (spv + -128) SL_wi)
    by (rewrite <- HSLe; cbn [saves]; replace (spv + -128 + 0) with (spv + -128) by lia; reflexivity) end.
  set (M0s := saves M (spv + -128) SL_wi) in *.
  assert (HUs : unch M M0s (fun x => inr x (spv - 336) 336)).
  { apply (saves_unch SL_wi M M (spv + -128) 128); [lia | lia | exact HSL | | apply unch_refl]. intros x Hx. unfold inr in *. lia. }
  assert (HGs : mem_grows M M0s) by apply saves_grows.
  assert (Hsvs : forall off v, In (off, v) SL_wi -> cell BSEGS M0s (spv + -128 + off) 8 v).
  { intros off v Hin. apply (saves_cell BSEGS SL_wi M (spv + -128) 128); [lia | lia | exact HSL | exact Hin]. }
  clearbody M0s. clear HSLe HSL.
  assert (Hrt0 : rt_ok M0s). { eapply rt_ok_unch; [exact HUs | | exact Hrt]. intros y Hy. apply (Q3 y Hy). }
  assert (Hrtx0 : RTX M0s).
  { eapply (if_unch _ _ _ _ IF); [exact Hrtx | exact HUs |]. intros x Hx. split; [apply (Q3 x Hx) | eapply (if_sep_dom _ _ _ _ IF); [exact Hrsep | exact Hx]]. }
  assert (Huar0 : uar_on M0s). { eapply uar_on_unch; [exact HUs | | exact Huar]. intros y Hy. apply (Q3 y Hy). }
  pose proof nums as (NF1 & NF2 & NF5 & NF4 & NS1 & NS2 & NS3).
  assert (Hhint0 : cell BSEGS M0s fs 8 (W h)).
  { eapply cell_unch; [exact HUs | unfold HIMEM_BEG, B_IMG_END, SB, FS_SIZE in *; lia | (cbn; unfold HIMEM_END, FS_SIZE in *; lia) | | exact Hhint].
    intros x Hx Hx2. destruct (Q3 x Hx2) as [Hq _]. apply Hq. cbn in Hx. unfold inr, FS_SIZE in *. lia. }
  assert (Hflags0 : zeros M0s (fs + 4096) 16384).
  { eapply zeros_grows_unch; [exact HUs | unfold HIMEM_BEG, B_IMG_END, SB, FS_SIZE in *; lia | unfold HIMEM_END, FS_SIZE in *; lia | | exact Hflags].
    intros x Hx Hx2. destruct (Q3 x Hx2) as [Hq _]. apply Hq. unfold inr, FS_SIZE in *. lia. }
  pose proof (ring_wr_grows _ _ _ HGs Hrwr) as (Rw1 & Rw2 & Rw3 & Rw4).
  pose proof Hrt0 as (G1 & G2 & _). pose proof Huar0 as (U1 & U2).
  unfold G_SB, C_SB, G_UAR, C_UAR in *.
  wp_wi [0x2726b0]. rewrite ?addi_W. mem_auto.
  eexists. split; [apply load_cell; [exact U2 | lia]|]. mem_auto.
  change (v_lw (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) mod 2 ^ (8 * Z.of_nat 4)))) with (W 1).
  change (bv_unsigned (W 1)) with 1.
  assert (Hal : (spv + -128) mod 32 = 0).
  { replace (spv + -128) with (spv + (-4) * 32) by lia. rewrite Z.mod_add by lia. exact Sp3. }
  rewrite (andi_m32_aligned (spv + -128)) by (lia || exact Hal).
  replace (spv + -128 + 128) with spv by lia.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  replace (Z_to_bv 64 1708840) with (W 0x1a1328) by reflexivity.
  destruct Hfs as (Fs1 & Fs2 & Fs3).
  eapply (if_malloc0 _ _ _ _ IF rom Post M0s h (spv + -128));
    [ exact Hrt0 | exact Hrtx0 | exact Hhint0 | exact Hh | exact Hflags0 | split; [exact Fs1 | exact Fs2]
    | exact Rw1 | exact Rw2 | exact Rw3 | exact Rw4 | unfold B_IMG_END; lia | exact Q2
    | eapply wr_ok_sub; [eapply wr_ok_grows; [exact HGs | exact Hfr] | lia | lia]
    | eapply (if_sep_sub _ _ _ _ IF); [exact Hrsep | lia | lia] | exact Q1
    | reflexivity | reflexivity | reflexivity | ].
  intros l' M' k0 FB0 Hl' Hse' H10' Ch' Cf' C24' C56' Hz' HU' HG'. subst k0 FB0. fold k in H10', Ch', Cf', C24', C56', Hz', HU' |- *. fold FB in H10', Ch', Cf', C24', C56', Hz', HU' |- *. cbn [rget lget].
  fix_jalr 0x2726a8.
  pose proof kb as Hkb.
  assert (W1' : wr_ok BSEGS M' (spv - 336) 336) by (eapply wr_ok_grows; [exact HG'|]; eapply wr_ok_grows; [exact HGs | exact Hfr]).
  assert (W3' : wr_ok BSEGS M' (fs + 36864) 1048576) by (eapply wr_ok_grows; [exact HG' | exact Rw3]).
  assert (W4' : wr_ok BSEGS M' (sha (fs + 36864)) 131072) by (eapply wr_ok_grows; [exact HG' | exact Rw4]).
  regs_open l' Hl'. se_subst Hse'. cbn [rget lget] in H10'. match type of H10' with ?x = _ => subst x end.
  unfold SB, HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END in NF1, NF2, NF5, NF4, NS1, NS2, Fs1, Fs2.
  wp_wi [0x2726bc; 0x27272c]. rewrite (Wu FB) by lia.
  split; intros Hb; [|exfalso; lia]. clear Hb.
  rewrite ?addi_W. rewrite (sha_addr_r FB) by lia.
  assert (E1 : v_addiw (Z_to_bv 64 1102417920) (-1357) = W 0x41b58ab3) by (apply bv_eq; reflexivity). rewrite E1. clear E1.
  mem_auto.
  match goal with |- reach _ _ _ _ ?Mx _ =>
    assert (HU2 : unch M' Mx (fun x => inr x FB 24 \/ inr x (sha FB) 8))
      by (solve_unch ltac:(unfold inr in *; lia));
    assert (HG2 : mem_grows M' Mx) by solve_grows;
    set (M2 := Mx) in * end.
  clearbody M2.
  destruct Hpkt as (P1 & [_ P2] & P3). destruct Hs_pk as (Sk1 & Sk2).
  unfold B_IMG_END, LOMEM_END, HIMEM_BEG, HIMEM_END, SB, FS_SIZE in P1, P2.
  pose proof (sha_range (pkt + 16) ltac:(unfold HIMEM_END; lia)) as Hrp. unfold SB, HIMEM_BEG, B_IMG_END, FS_SIZE in Hrp.
  assert (Esh24 : sha (pkt + 24) = sha (pkt + 16) + 1).
  { replace (pkt + 24) with (pkt + 16 + 8 * 1) by lia. apply sha_add8. }
  pose proof (sha_range (pkt + 24) ltac:(unfold HIMEM_END; lia)) as Hrp2. rewrite Esh24 in Hrp2. unfold SB, HIMEM_BEG, B_IMG_END, FS_SIZE in Hrp2.
  assert (Hap : forall i, 0 <= i < 2 -> ~ (sha FB <= sha (pkt + 16) + i < sha FB + 8)).
  { intros i Hi. assert (i = 0 \/ i = 1) as [->| ->] by lia.
    - rewrite Z.add_0_r. apply sh_pkt_apart. lia.
    - rewrite <- Esh24. apply sh_pkt_apart. lia. }
  assert (Zs2 : zeros M2 (sha (pkt + 16)) 2).
  { eapply zeros_grows_unch; [exact HU2 | lia | lia | |].
    { intros x Hx HF. unfold inr in *. destruct HF as [HF|HF]; [lia|].
      apply (Hap (bv_unsigned x - sha (pkt + 16))); lia. }
    eapply zeros_grows_unch; [exact HU' | lia | lia | |].
    { pose proof Q2 as Q2'. unfold SB, HIMEM_BEG, B_IMG_END, FS_SIZE in Q2'.
      intros x Hx HF. unfold inr in *. destruct HF as [HF|[HF|[HF|[HF|[HF|HF]]]]];
        first [lia | apply (Hap (bv_unsigned x - sha (pkt + 16))); lia]. }
    eapply zeros_grows_unch; [exact HUs | lia | lia | | exact Hshp].
    intros x Hx HF. destruct (Q3 x HF) as (_ & _ & Q33). apply Q33. unfold inr, SB, HIMEM_BEG, B_IMG_END, FS_SIZE in *. lia. }
  assert (Wp2 : wr_ok BSEGS M2 (pkt + 16) 16).
  { eapply wr_ok_grows; [exact HG2|]. eapply wr_ok_grows; [exact HG'|]. eapply wr_ok_grows; [exact HGs | exact Hwp]. }
  assert (W12 : wr_ok BSEGS M2 (spv - 336) 336) by (eapply wr_ok_grows; [exact HG2 | exact W1']).
  assert (Ean : v_andi (W pkt) 7 = W 0) by (rewrite andi7_W by lia; rewrite P3; reflexivity).
  wp_wi [0x272778; 0x2728f4; 0x2728f8; 0x2728fc]. rewrite ?addi_W. rewrite Ean.
  assert (Zst : forall Mx a bs, zeros Mx (sha (pkt + 16)) 2 -> 0 <= a -> a + Z.of_nat (length bs) < 2 ^ 64 ->
                 (a + Z.of_nat (length bs) <= sha (pkt + 16) \/ sha (pkt + 16) + 2 <= a) ->
                 zeros (wbytes Mx (W a) bs) (sha (pkt + 16)) 2).
  { intros Mx a bs Hz Ha Hn Hd. eapply zeros_grows_unch; [ | lia | lia | | exact Hz].
    - apply unch_store; [apply unch_refl | exact Ha | exact Hn | intros x Hx; exact Hx].
    - intros x Hx HF. unfold inr in *. lia. }
  pose proof Hs_sh as Hs_sh'. unfold SB, HIMEM_BEG, B_IMG_END, FS_SIZE in Hs_sh'.
  split; [eapply wr_ok_store; [exact W12 | lia | cbn; lia]|].
  change (bv_unsigned (Z_to_bv 64 0)) with 0.
  split; [intros Hb; exfalso; apply Hb; reflexivity | intros _].
  rewrite (sha_addr_r (pkt + 16)) by lia. rewrite (sha_addr_r (pkt + 24)) by lia.
  exists (W 0). split; [apply (load1_zeros BSEGS _ (sha (pkt + 16)) 2); [apply Zst; [exact Zs2 | lia | cbn; lia | cbn; lia] | lia]|].
  change (bv_unsigned (W 0)) with 0.
  split; [intros Hb; exfalso; apply Hb; reflexivity | intros _].
  split; [eapply wr_ok_store; [eapply wr_ok_grows; [|exact Wp2]; solve_grows | lia | cbn; lia]|].
  exists (W 0). split; [apply (load1_zeros BSEGS _ (sha (pkt + 16)) 2);
    [apply Zst; [apply Zst; [exact Zs2 | lia | cbn; lia | cbn; lia] | lia | cbn; lia | cbn; lia] | lia]|].
  change (bv_unsigned (W 0)) with 0.
  split; [intros Hb; exfalso; apply Hb; reflexivity | intros _].
  split; [eapply wr_ok_store; [eapply wr_ok_grows; [|exact Wp2]; solve_grows | lia | cbn; lia]|].
  match goal with |- reach _ _ _ _ ?Mx _ =>
    assert (HU3 : unch M2 Mx (fun x => inr x (spv - 128 + 24) 8 \/ inr x (pkt + 16) 16))
      by (solve_unch ltac:(unfold inr in *; lia));
    assert (HG3 : mem_grows M2 Mx) by solve_grows;
    assert (Cp16 : cell BSEGS Mx (pkt + 16) 8 (W 0))
      by (apply cell_store_other; [lia | (cbn; lia) | lia | cbn; lia | cbn; lia | apply cell_store_same; cbn; lia]);
    assert (Cp24 : cell BSEGS Mx (pkt + 24) 8 (W 0)) by (apply cell_store_same; cbn; lia);
    set (M3 := Mx) in * end.
  clearbody M3.
  assert (HU23 : unch M' M3 (fun x => inr x (spv - 128 + 24) 8 \/ inr x (pkt + 16) 16 \/ inr x FB 24 \/ inr x (sha FB) 8)).
  { eapply unch_trans; [eapply unch_weaken; [exact HU2|] | eapply unch_weaken; [exact HU3|]].
    - intros x [H|H]; [right; right; left; exact H | right; right; right; exact H].
    - intros x [H|H]; [left; exact H | right; left; exact H]. }
  assert (HG23 : mem_grows M' M3) by (eapply mem_grows_trans; eassumption).
  clear HU2 HG2 HU3 HG3 Zs2 Wp2 W12 Zst.
  match goal with |- reach _ _ _ ?lx _ _ => assert (Hse2 : same_except KS_r1 l0 lx) end.
  { eapply same_except_trans;
      [eapply same_except_call; [ | exact Hse' | ]; [eapply same_except_trans; [exact Hse | same_ex] | unfold KSC, KS_r1; subset_tac]
      | same_ex]. }
  assert (PA : forall x, (inr x (spv - 128 + 24) 8 \/ inr x (pkt + 16) 16 \/ inr x FB 24 \/ inr x (sha FB) 8) ->
             ~ inr x (spv - 128 + 32) 96 /\ ~ inr x fs 8 /\ ~ inr x (fs + 4096) 16384 /\ ~ inr x (FB + 56) 8).
  { clear - NF1 NF2 NF5 NF4 NS1 NS2 Hs_fs Hs_sh Sp1 Sp2 Sk1 Sk2 P1 P2. intros x Hx. unfold inr, SB, HIMEM_BEG, FS_SIZE, B_IMG_END in *. lia. }
  assert (PB : forall x, (inr x (spv + -128 - 208) 208 \/ inr x fs 8 \/ inr x (fs + 4096 + k) 1 \/ inr x (FB + 24) 8
                           \/ inr x (FB + 56) 8 \/ inr x (sha FB) 8) ->
             ~ inr x (spv - 128 + 32) 96 /\ ~ inr x (fs + 4096) k /\ ~ inr x (fs + 4096 + k + 1) (16383 - k)).
  { clear - NF1 NF2 NF5 NF4 NS1 NS2 Hs_fs Hs_sh Sp1 Sp2 Hkb. intros x Hx. unfold inr, SB, HIMEM_BEG, FS_SIZE, B_IMG_END in *. lia. }
  apply K; [reflexivity | exact Hse2 | cbn [rget lget]; f_equal; lia | reflexivity | cbn [rget lget]; f_equal; lia
           | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
           | reflexivity | | | | | | | exact Cp16 | exact Cp24 | | ].
  - intros off r Hin.
    assert (Hin2 : In (off, rget l0 r) SL_wi /\ 32 <= off <= 120).
    { unfold WI_SLOTS in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; split; [unfold SL_wi; in_list | lia]|]). contradiction. }
    destruct Hin2 as (Hin2 & Ho). replace (spv - 128 + off) with (spv + -128 + off) by lia.
    eapply cell_unch; [exact HU23 | lia | (cbn; lia) | | eapply cell_unch; [exact HU' | lia | (cbn; lia) | | apply Hsvs; exact Hin2]].
    + intros x Hx HP. destruct (PA x HP) as (P1' & _). apply P1'. cbn in Hx. unfold inr in *. lia.
    + intros x Hx HP. destruct (PB x HP) as (P1' & _). apply P1'. cbn in Hx. unfold inr in *. lia.
  - eapply cell_unch; [exact HU23 | lia | (cbn; lia) | | exact Ch'].
    intros x Hx HP. destruct (PA x HP) as (_ & P2' & _). apply P2'. exact Hx.
  - eapply cell_unch; [exact HU23 | lia | (cbn; lia) | | exact Cf'].
    intros x Hx HP. destruct (PA x HP) as (_ & _ & P3' & _). apply P3'. cbn in Hx. unfold inr in *. lia.
  - eapply zeros_grows_unch; [exact HU23 | lia | lia | | eapply zeros_grows_unch; [exact HU' | lia | lia | | eapply zeros_sub; [exact Hflags0 | lia | lia]]].
    + intros x Hx HP. destruct (PA x HP) as (_ & _ & P3' & _). apply P3'. unfold inr in *. lia.
    + intros x Hx HP. destruct (PB x HP) as (_ & P2' & _). apply P2'. exact Hx.
  - eapply zeros_grows_unch; [exact HU23 | lia | lia | | eapply zeros_grows_unch; [exact HU' | lia | lia | | eapply zeros_sub; [exact Hflags0 | lia | lia]]].
    + intros x Hx HP. destruct (PA x HP) as (_ & _ & P3' & _). apply P3'. unfold inr in *. lia.
    + intros x Hx HP. destruct (PB x HP) as (_ & _ & P3'). apply P3'. exact Hx.
  - eapply cell_unch; [exact HU23 | lia | (cbn; lia) | | exact C56'].
    intros x Hx HP. destruct (PA x HP) as (_ & _ & _ & P4'). apply P4'. exact Hx.
  - eapply unch_trans; [eapply unch_weaken; [exact HUs|] | eapply unch_trans; [eapply unch_weaken; [exact HU'|] | eapply unch_weaken; [exact HU23|]]].
    + intros x Hx. left. exact Hx.
    + clear - NF1 NF2 Hkb NS3. intros x Hx. unfold FP_r1, ring_FP, inr in *. lia.
    + clear - NF1 NF2 Hkb NS3. intros x Hx. unfold FP_r1, ring_FP, inr in *. lia.
  - eapply mem_grows_trans; [exact HGs|]. eapply mem_grows_trans; [exact HG' | exact HG23].
Qed.

End R1.

Theorem wpinit_r1_cps : forall RTX RTXD RSEP fs, rt_iface RTX RTXD RSEP fs ->
  forall rom Post M pkt lb spv h l,
  rt_ok M -> RTX M -> uar_on M -> fs_wf fs -> 0 <= h < 2 ^ 64 -> cell BSEGS M fs 8 (W h) ->
  zeros M (fs + 4096) 16384 -> ring_wr M fs ->
  B_IMG_END <= spv - 336 /\ spv < 2 ^ 63 /\ spv mod 32 = 0 -> wr_ok BSEGS M (spv - 336) 336 ->
  (spv <= fs \/ fs + FS_SIZE <= spv - 336) -> (spv <= SB \/ HIMEM_BEG <= spv - 336) -> RSEP (spv - 336) 336 ->
  B_IMG_END <= pkt /\ memrange pkt 56 /\ pkt mod 8 = 0 -> zeros M (sha (pkt + 16)) 2 -> wr_ok BSEGS M (pkt + 16) 16 ->
  (spv <= pkt \/ pkt + 56 <= spv - 336) /\ (pkt + 56 <= fs \/ fs + 1085440 <= pkt) ->
  length l = 32%nat -> rget l 2 = W spv -> rget l 4 = W TP -> rget l 10 = W pkt -> rget l 11 = W lb ->
  (forall l' M', let k := h mod 16384 in let FB := fs + 36864 + 64 * k in
     length l' = 32%nat -> same_except KS_r1 l l' ->
     rget l' 2 = W (spv - 128) -> rget l' 8 = W spv -> rget l' 9 = W (spv - 128) ->
     rget l' 10 = W 40 -> rget l' 11 = W 0x2d61f -> rget l' 12 = W 110 ->
     rget l' 18 = W FB -> rget l' 19 = W lb -> rget l' 20 = W pkt -> rget l' 23 = W (sha FB) ->
     rget l' 24 = W FB -> rget l' 25 = W SB ->
     (forall off r, In (off, r) WI_SLOTS -> cell BSEGS M' (spv - 128 + off) 8 (rget l r)) ->
     cell BSEGS M' fs 8 (W (h + 1)) -> cell BSEGS M' (fs + 4096 + k) 1 (W 1) ->
     zeros M' (fs + 4096) k -> zeros M' (fs + 4096 + k + 1) (16383 - k) ->
     cell BSEGS M' (FB + 56) 8 (W (fs + 4096 + k)) ->
     cell BSEGS M' (pkt + 16) 8 (W 0) -> cell BSEGS M' (pkt + 24) 8 (W 0) ->
     unch M M' (FP_r1 fs spv pkt) -> mem_grows M M' ->
     reach BSEGS rom (W 0x272778) l' M' Post) ->
  reach BSEGS rom (W 0x272638) l M Post.
Proof.
  intros RTX RTXD RSEP fs IF rom Post M pkt lb spv h l; intros.
  eapply (r1_body RTX RTXD RSEP fs IF rom Post M pkt lb spv h) with (l0 := l); eauto.
Qed.

(* [comment removed for export] *)
Definition KS_r2 : list nat := [1; 2; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26]%nat.
(* [comment removed for export] *)
Definition FP_r2 (fs pkt k : Z) (x : word) : Prop :=
  inr x (pkt + 40) 8 \/ inr x (fs + 36864 + 64 * k) 8 \/ inr x (sha (fs + 36864 + 64 * k)) 8 \/ inr x (fs + 4096 + k) 1.

Section R2.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (fs pkt spv k : Z) (res : word) (sv : nat -> word).
Hypothesis Hfs : fs_wf fs.
Hypothesis Hk : 0 <= k < 16384.
Let FB := fs + 36864 + 64 * k.
Hypothesis Hsaved : forall off r, In (off, r) WI_SLOTS -> cell BSEGS M (spv - 128 + off) 8 (sv r).
Hypothesis C56 : cell BSEGS M (FB + 56) 8 (W (fs + 4096 + k)).
Hypothesis Hz1 : zeros M (fs + 4096) k.
Hypothesis Hz2 : zeros M (fs + 4096 + k + 1) (16383 - k).
Hypothesis Hshp : zeros M (sha (pkt + 40)) 1.
Hypothesis Hpkt : B_IMG_END <= pkt /\ memrange pkt 56 /\ pkt mod 8 = 0.
Hypothesis Hwr : wr_ok BSEGS M (pkt + 40) 8 /\ wr_ok BSEGS M FB 8 /\ wr_ok BSEGS M (sha FB) 8
                 /\ wr_ok BSEGS M (fs + 4096 + k) 1.
Hypothesis Hsp : B_IMG_END <= spv - 128 /\ spv < 2 ^ 63.
Hypothesis Hsep : (spv <= fs \/ fs + FS_SIZE <= spv - 128) /\ (spv <= SB \/ HIMEM_BEG <= spv - 128)
                  /\ (spv <= pkt \/ pkt + 56 <= spv - 128) /\ (pkt + 56 <= fs \/ fs + 1085440 <= pkt).

Variable l0 : regfile.
Hypothesis Hl0 : length l0 = 32%nat.
Hypothesis K : forall l' M' (a0v : Z), length l' = 32%nat -> same_except KS_r2 l0 l' ->
  rget l' 2 = W spv -> rget l' 10 = W a0v -> (bv_unsigned res = 0 -> a0v = 0) -> (bv_unsigned res <> 0 -> a0v = 1) ->
  (forall off r, In (off, r) WI_SLOTS -> rget l' r = sv r) ->
  cell BSEGS M' (pkt + 40) 8 res -> zeros M' (fs + 4096) 16384 ->
  unch M M' (FP_r2 fs pkt k) -> mem_grows M M' ->
  reach BSEGS rom (v_jalr (sv 1) 0) l' M' Post.

Lemma nums2 : fs + 36864 <= FB /\ FB + 64 <= fs + 1085440 /\ (B_IMG_END <= fs /\ (fs + FS_SIZE <= SB \/ HIMEM_BEG <= fs)) /\ fs + FS_SIZE <= HIMEM_END
  /\ SB <= sha FB /\ sha FB + 8 <= HIMEM_BEG /\ sha FB = sha (fs + 36864) + 8 * k.
Proof.
  destruct Hfs as (F1 & F2 & F3).
  assert (Es : sha FB = sha (fs + 36864) + 8 * k) by (unfold FB; apply sha_frame).
  assert (Hq : (fs + 36864) / 8 <= 17592185913344) by (unfold HIMEM_END, FS_SIZE in *; apply Z.div_le_upper_bound; lia).
  assert (Hq0 : 0 <= (fs + 36864) / 8) by (unfold HIMEM_BEG, B_IMG_END, SB, FS_SIZE in *; apply Z.div_pos; lia).
  clear - F1 F2 Hk Es Hq Hq0. unfold FB, HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END, SB in *. repeat split; try lia.
  - rewrite Es. unfold sha, SB. lia.
  - rewrite Es. unfold sha, SB. lia.
Qed.

(* [comment removed for export] *)
Definition FPQ (x : word) : Prop := inr x (pkt + 40) 8 \/ inr x FB 8 \/ inr x (sha FB) 8.
Definition QI (M2 : mem) : Prop := unch M M2 FPQ /\ mem_grows M M2.

Lemma QI_store : forall M2 a bs, QI M2 -> 0 <= a -> a + Z.of_nat (length bs) < 2 ^ 64 ->
  (forall x, inr x a (Z.of_nat (length bs)) -> FPQ x) -> QI (wbytes M2 (W a) bs).
Proof.
  intros M2 a bs [HU HG] Ha Hn HF. split; [|eapply mem_grows_trans; [exact HG | apply wbytes_grows]].
  eapply unch_trans; [exact HU|]. eapply unch_weaken; [|exact HF].
  apply unch_store; [apply unch_refl | exact Ha | exact Hn | intros x Hx; exact Hx].
Qed.

Ltac solve_QI HQI :=
  repeat (apply QI_store; [ | lia | rewrite ?length_N_to_le_bytes; lia
                          | let x := fresh "x" in let Hx := fresh "Hx" in
                            intros x Hx; rewrite ?length_N_to_le_bytes in Hx; unfold FPQ, inr in *; lia ]);
  exact HQI.

Lemma FPQ_apart : forall x, FPQ x -> ~ inr x (spv - 128) 128 /\ ~ inr x (FB + 56) 8 /\ ~ inr x (fs + 4096) 16384.
Proof.
  pose proof nums2 as (N1 & N2 & N3 & N4 & N5 & N6 & _). destruct Hsep as (S1 & S2 & S3 & S4).
  destruct Hpkt as (_ & [_ P2] & _).
  clear - N1 N2 N3 N4 N5 N6 S1 S2 S3 S4 P2.
  intros x Hx. unfold FPQ, inr, SB, LOMEM_END, HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END in *. lia.
Qed.

Lemma QI_facts : forall M2, QI M2 ->
  (forall off r, In (off, r) WI_SLOTS -> cell BSEGS M2 (spv - 128 + off) 8 (sv r))
  /\ cell BSEGS M2 (FB + 56) 8 (W (fs + 4096 + k)) /\ zeros M2 (fs + 4096) k /\ zeros M2 (fs + 4096 + k + 1) (16383 - k)
  /\ wr_ok BSEGS M2 (pkt + 40) 8 /\ wr_ok BSEGS M2 FB 8 /\ wr_ok BSEGS M2 (sha FB) 8 /\ wr_ok BSEGS M2 (fs + 4096 + k) 1.
Proof.
  intros M2 [HU HG]. pose proof nums2 as (N1 & N2 & N3 & N4 & N5 & N6 & _). destruct Hsp as (Sp1 & Sp2).
  destruct Hwr as (W1 & W2 & W3 & W4). unfold B_IMG_END, HIMEM_BEG, HIMEM_END, FS_SIZE, SB in *.
  split; [|split; [|split; [|split]]].
  - intros off r Hin.
    assert (Ho : 32 <= off <= 120).
    { unfold WI_SLOTS in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). contradiction. }
    eapply cell_unch; [exact HU | lia | (cbn; lia) | | apply Hsaved; exact Hin].
    intros x Hx HF. destruct (FPQ_apart x HF) as (A1 & _). apply A1. cbn in Hx. unfold inr in *. lia.
  - eapply cell_unch; [exact HU | lia | (cbn; lia) | | exact C56].
    intros x Hx HF. destruct (FPQ_apart x HF) as (_ & A2 & _). apply A2. exact Hx.
  - eapply zeros_grows_unch; [exact HU | lia | lia | | exact Hz1].
    intros x Hx HF. destruct (FPQ_apart x HF) as (_ & _ & A3). apply A3. unfold inr in *. lia.
  - eapply zeros_grows_unch; [exact HU | lia | lia | | exact Hz2].
    intros x Hx HF. destruct (FPQ_apart x HF) as (_ & _ & A3). apply A3. unfold inr in *. lia.
  - repeat split; eapply wr_ok_grows; eassumption.
Qed.

Lemma ring_merge : forall (Mx : mem), zeros Mx (fs + 4096) k -> zeros Mx (fs + 4096 + k + 1) (16383 - k) ->
  zeros (wbytes Mx (W (fs + 4096 + k)) (word_to_le_bytes 1 (Z_to_bv 64 0))) (fs + 4096) 16384.
Proof.
  intros Mx Z1 Z2 i Hi. pose proof nums2 as (_ & _ & N3 & N4 & _). unfold HIMEM_BEG, HIMEM_END, FS_SIZE, B_IMG_END, SB in *.
  destruct (Z.eq_dec i k) as [->|Hne].
  - change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]. cbn [wbytes]. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity.
  - rewrite wbytes_out; [ | lia | cbn; lia | unfold inr; rewrite Wu by lia; cbn; lia].
    destruct (Z_lt_le_dec i k) as [Hlt|Hge]; [apply Z1; lia|].
    replace (fs + 4096 + i) with (fs + 4096 + k + 1 + (i - k - 1)) by lia. apply Z2. lia.
Qed.

(* [comment removed for export] *)
Lemma r2_epi : forall l M2 a0v, QI M2 -> length l = 32%nat -> same_except KS_r2 l0 l ->
  rget l 8 = W spv -> rget l 18 = W FB -> rget l 23 = W (sha FB) -> rget l 24 = W FB -> rget l 21 = W a0v ->
  (bv_unsigned res = 0 -> a0v = 0) -> (bv_unsigned res <> 0 -> a0v = 1) -> cell BSEGS M2 (pkt + 40) 8 res ->
  reach BSEGS rom (W 0x27284c) l M2 Post.
Proof.
  intros l M2 a0v HQI Hl Hse H8 H18 H23 H24 H21 Ha0 Ha1 Cres.
  pose proof nums2 as (N1 & N2 & N3 & N4 & N5 & N6 & _). destruct Hsp as (Sp1 & Sp2).
  destruct (QI_facts _ HQI) as (_ & _ & _ & _ & W1 & W2 & W3 & W4).
  unfold B_IMG_END, SB, HIMEM_BEG, HIMEM_END, FS_SIZE in N1, N2, N3, N4, N5, N6, Sp1.
  regs_open l Hl. subst s0 s2 s7 s8 s5.
  wp_wi [0x272894; 0x272888]. rewrite ?addi_W.
  assert (E1 : v_addiw (Z_to_bv 64 1172320256) 1550 = W 0x45e0360e) by (apply bv_eq; reflexivity). rewrite E1. clear E1.
  split; [eapply wr_ok_store; [exact W3 | lia | cbn; lia]|].
  split; [eapply wr_ok_store; [eapply wr_ok_grows; [apply wbytes_grows | exact W2] | lia | cbn; lia]|].
  rewrite (Wu FB) by lia. split; intros Hb; [exfalso; lia|]. clear Hb.
  repeat (split; [eapply wr_ok_store; [eapply wr_ok_grows; [|exact W3]; solve_grows | lia | cbn; lia]|]).
  match goal with |- reach _ _ _ _ ?Mx _ =>
    assert (HQI3 : QI Mx) by solve_QI HQI;
    assert (Cres3 : cell BSEGS Mx (pkt + 40) 8 res) end.
  { destruct Hpkt as (P1 & [_ P2] & _). destruct Hsep as (_ & _ & _ & S4).
    unfold B_IMG_END, SB, LOMEM_END, HIMEM_BEG, HIMEM_END, FS_SIZE in P1, P2.
    repeat (apply cell_store_other; [lia | (cbn; lia) | lia | cbn; lia | cbn; lia |]). exact Cres. }
  match goal with |- reach _ _ _ _ ?Mx _ => set (M3 := Mx) in * end. clearbody M3.
  destruct (QI_facts _ HQI3) as (Hsv3 & C563 & Z13 & Z23 & _ & _ & _ & W43).
  pose proof (Hsv3 120 1%nat ltac:(unfold WI_SLOTS; in_list)) as Csv1. pose proof (Hsv3 112 8%nat ltac:(unfold WI_SLOTS; in_list)) as Csv8.
  pose proof (Hsv3 104 9%nat ltac:(unfold WI_SLOTS; in_list)) as Csv9. pose proof (Hsv3 96 18%nat ltac:(unfold WI_SLOTS; in_list)) as Csv18.
  pose proof (Hsv3 88 19%nat ltac:(unfold WI_SLOTS; in_list)) as Csv19. pose proof (Hsv3 80 20%nat ltac:(unfold WI_SLOTS; in_list)) as Csv20.
  pose proof (Hsv3 72 21%nat ltac:(unfold WI_SLOTS; in_list)) as Csv21. pose proof (Hsv3 64 22%nat ltac:(unfold WI_SLOTS; in_list)) as Csv22.
  pose proof (Hsv3 56 23%nat ltac:(unfold WI_SLOTS; in_list)) as Csv23. pose proof (Hsv3 48 24%nat ltac:(unfold WI_SLOTS; in_list)) as Csv24.
  pose proof (Hsv3 40 25%nat ltac:(unfold WI_SLOTS; in_list)) as Csv25. pose proof (Hsv3 32 26%nat ltac:(unfold WI_SLOTS; in_list)) as Csv26.
  clear Hsv3.
  destruct Hsep as (S1 & _). unfold FS_SIZE in S1.
  wp_wi (@nil Z). rewrite ?addi_W.
  eexists. split; [apply load_cell8; exact C563|].
  split; [eapply wr_ok_store; [exact W43 | lia | cbn; lia]|].
  replace (spv + -128 + 120) with (spv - 128 + 120) by lia. replace (spv + -128 + 112) with (spv - 128 + 112) by lia.
  replace (spv + -128 + 104) with (spv - 128 + 104) by lia. replace (spv + -128 + 96) with (spv - 128 + 96) by lia.
  replace (spv + -128 + 88) with (spv - 128 + 88) by lia. replace (spv + -128 + 80) with (spv - 128 + 80) by lia.
  replace (spv + -128 + 72) with (spv - 128 + 72) by lia. replace (spv + -128 + 64) with (spv - 128 + 64) by lia.
  replace (spv + -128 + 56) with (spv - 128 + 56) by lia. replace (spv + -128 + 48) with (spv - 128 + 48) by lia.
  replace (spv + -128 + 40) with (spv - 128 + 40) by lia. replace (spv + -128 + 32) with (spv - 128 + 32) by lia.
  mem_auto.
  replace (spv + -128 + 128) with spv by lia.
  destruct HQI3 as (HU3 & HG3). destruct Hpkt as (P1 & [_ P2] & _). destruct Hsep as (_ & _ & _ & S4).
  unfold B_IMG_END, SB, LOMEM_END, HIMEM_BEG, HIMEM_END, FS_SIZE in P1, P2.
  apply (K _ _ a0v); [reflexivity | | reflexivity | reflexivity | exact Ha0 | exact Ha1 | | | | | ].
  - eapply same_except_trans; [exact Hse | same_ex].
  - intros off r Hin. unfold WI_SLOTS in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; reflexivity|]). contradiction.
  - apply cell_store_other; [lia | (cbn; lia) | lia | cbn; lia | cbn; lia | exact Cres3].
  - apply ring_merge; assumption.
  - eapply unch_trans; [eapply unch_weaken; [exact HU3|]|].
    + intros x Hx. unfold FPQ, FP_r2 in *. fold FB. destruct Hx as [H|[H|H]]; [left | right; left | right; right; left]; exact H.
    + apply unch_store; [apply unch_refl | lia | cbn; lia |]. intros x Hx. cbn in Hx.
      unfold FP_r2. right. right. right. exact Hx.
  - eapply mem_grows_trans; [exact HG3 | apply wbytes_grows].
Qed.

Lemma r2_body : forall l, l = l0 -> rget l 8 = W spv -> rget l 10 = res -> rget l 18 = W FB -> rget l 19 = W 0 ->
  rget l 20 = W pkt -> rget l 23 = W (sha FB) -> rget l 24 = W FB -> rget l 25 = W SB ->
  reach BSEGS rom (W 0x27277c) l M Post.
Proof.
  intros l El H8 H10 H18 H19 H20 H23 H24 H25. pose proof Hl0 as Hl. rewrite <- El in Hl.
  assert (Hse : same_except KS_r2 l0 l) by (rewrite El; apply same_except_refl). clear El.
  destruct Hpkt as (P1 & [_ P2] & P3). destruct Hwr as (W1 & _).
  unfold B_IMG_END, SB, LOMEM_END, HIMEM_BEG, HIMEM_END, FS_SIZE in P1, P2.
  assert (HQ0 : QI M) by (split; [apply unch_refl | apply mem_grows_refl]).
  regs_open l Hl. subst s0 a0 s2 s3 s4 s7 s8 s9.
  wp_wi [0x272900; 0x2727a0; 0x27284c]. rewrite ?addi_W. rewrite sha_addr_r by lia.
  exists (W 0). split; [apply (load1_zeros BSEGS M (sha (pkt + 40)) 1); [exact Hshp | lia]|].
  change (bv_unsigned (W 0)) with 0.
  split; [intros Hb; exfalso; apply Hb; reflexivity | intros _].
  split; [eapply wr_ok_store; [exact W1 | lia | cbn; lia]|].
  match goal with |- (_ -> reach _ _ _ _ ?Mx _) /\ _ =>
    assert (HQ1 : QI Mx) by solve_QI HQ0;
    assert (Cres : cell BSEGS Mx (pkt + 40) 8 res) by (apply cell_store_same; cbn; lia);
    set (M1 := Mx) in * end.
  clearbody M1.
  split; intros Hb.
  - eapply (r2_epi _ M1 0); [exact HQ1 | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity | reflexivity
      | reflexivity | reflexivity | reflexivity | intros _; reflexivity | intros Hn; exfalso; apply Hn; exact Hb | exact Cres].
  - change (bv_unsigned (Z_to_bv 64 0)) with 0. split; intros Hb2; [|exfalso; apply Hb2; reflexivity].
    eapply (r2_epi _ M1 1); [exact HQ1 | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity | reflexivity
      | reflexivity | reflexivity | reflexivity | intros Hz; exfalso; apply Hb; exact Hz | intros _; reflexivity | exact Cres].
Qed.

End R2.

Theorem wpinit_r2_cps : forall rom Post M fs pkt spv k (res : word) (sv : nat -> word) l,
  fs_wf fs -> 0 <= k < 16384 ->
  (forall off r, In (off, r) WI_SLOTS -> cell BSEGS M (spv - 128 + off) 8 (sv r)) ->
  cell BSEGS M (fs + 36864 + 64 * k + 56) 8 (W (fs + 4096 + k)) ->
  zeros M (fs + 4096) k -> zeros M (fs + 4096 + k + 1) (16383 - k) -> zeros M (sha (pkt + 40)) 1 ->
  B_IMG_END <= pkt /\ memrange pkt 56 /\ pkt mod 8 = 0 ->
  wr_ok BSEGS M (pkt + 40) 8 /\ wr_ok BSEGS M (fs + 36864 + 64 * k) 8 /\ wr_ok BSEGS M (sha (fs + 36864 + 64 * k)) 8
    /\ wr_ok BSEGS M (fs + 4096 + k) 1 ->
  B_IMG_END <= spv - 128 /\ spv < 2 ^ 63 ->
  (spv <= fs \/ fs + FS_SIZE <= spv - 128) /\ (spv <= SB \/ HIMEM_BEG <= spv - 128)
    /\ (spv <= pkt \/ pkt + 56 <= spv - 128) /\ (pkt + 56 <= fs \/ fs + 1085440 <= pkt) ->
  length l = 32%nat -> rget l 8 = W spv -> rget l 10 = res -> rget l 18 = W (fs + 36864 + 64 * k) -> rget l 19 = W 0 ->
  rget l 20 = W pkt -> rget l 23 = W (sha (fs + 36864 + 64 * k)) -> rget l 24 = W (fs + 36864 + 64 * k) -> rget l 25 = W SB ->
  (forall l' M' (a0v : Z), length l' = 32%nat -> same_except KS_r2 l l' ->
     rget l' 2 = W spv -> rget l' 10 = W a0v -> (bv_unsigned res = 0 -> a0v = 0) -> (bv_unsigned res <> 0 -> a0v = 1) ->
     (forall off r, In (off, r) WI_SLOTS -> rget l' r = sv r) ->
     cell BSEGS M' (pkt + 40) 8 res -> zeros M' (fs + 4096) 16384 ->
     unch M M' (FP_r2 fs pkt k) -> mem_grows M M' ->
     reach BSEGS rom (v_jalr (sv 1%nat) 0) l' M' Post) ->
  reach BSEGS rom (W 0x27277c) l M Post.
Proof.
  intros rom Post M fs pkt spv k res sv l; intros.
  eapply (r2_body rom Post M fs pkt spv k res sv) with (l0 := l); eauto.
Qed.

Print Assumptions wpinit_r1_cps.
Print Assumptions wpinit_r2_cps.
