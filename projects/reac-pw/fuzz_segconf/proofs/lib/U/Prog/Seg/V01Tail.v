(** Segment V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan, ELF afc060e3cc9c / pinned 1696d6c34ffd),
    stretch TAIL 0x141ac .. 0x141e8 (UBSan binary): proof of
    [V01D.V01_TAIL] from the two callee contracts of [MainB.K_V01] it uses, reac_segconf_declared_contract
    (0x16210, U/Prog/reac_segconf_declared_c.v) and check_declared_contract (0x14e0c, U/Prog/check_declared_c.v).

    Code (no branch, no trap):
      0x141ac a3 = sp + 0x5c (&n); s0 = c (ld 0x48(sp)); a0 = s0; s2 = tab (ld 0(sp)); a1 = s2; s1 = cap
              (ld 0x10(sp)); a2 = s1; 0x141c8 jal reac_segconf_declared
      0x141cc a3 = n (lw 0x5c(sp)); a1 = want (ld 0x20(sp)); a2 = s2; s4 = mt (ld 0x18(sp)); a4 = s4;
              a5 = mn (ld 0x28(sp)); a6 = s1; 0x141e8 jal check_declared
      0x141ec s0 = c, s1 = cap, s2 = tab, s3 = m, s4 = mt: [V01D.V01_post].
    reac_segconf_declared's premise comes from [V01_geo] and [V01_mem] (the reader's table, its free entries and
    the int n at sp + 0x5c, the errno cell, the stack-protector cells, the stack region [S - 65536, sp)); its post,
    with declared_guard_kept, gives check_declared's table and guard; check_declared's vlans_are premise is the last
    check of SegModel.harness_ok (MainBPure.mb_checks). Both callees keep F and fcsr (ret_post / ret_void), and their
    write sets lie inside [V01_W].
    Part of the proof of LLVMFuzzerTestOneInput (segment V01, stretch TAIL); no released proof of fuzz_segconf's
    LLVMFuzzerTestOneInput exists. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import MainBPure.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env reac_declared_vlan_split_c
  reac_declared_vlan_add_c reac_segconf_declared_c check_declared_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require MainB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import V01D.
Import ListNotations.
Open Scope Z_scope.

(** ** Build-independent facts (SegModel only) *)
Module V01TailPure.

(** The reader's initial table has at most cap entries: SegModel.vlan_init holds one entry only when 0 < cap. *)
Lemma vlan_init_len : forall p : payload, 0 <= p_cap p -> Z.of_nat (length (vlan_init p)) <= p_cap p.
Proof.
  intros p H. unfold vlan_init.
  match goal with |- context [if ?b then _ else _] => destruct b eqn:E end; cbn [length]; [|lia].
  apply andb_prop in E as [_ E]. apply Z.ltb_lt in E. lia.
Qed.

(** vlans_are fixes got's answer to want's and bounds got's table by cap. *)
Lemma vlans_are_fst : forall got w wt cap, vlans_are got (w, wt) cap = true ->
  fst got = w /\ Z.of_nat (length (snd got)) <= cap.
Proof.
  intros got w wt cap H. unfold vlans_are in H. cbn [fst snd] in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H _]. apply andb_prop in H as [H1 _].
  apply Z.eqb_eq in H1. apply Z.leb_le in H4. split; assumption.
Qed.

End V01TailPure.

(** ** Words and cells *)
(** A fact lia must not see (the alignment facts: lia case-splits every mod it is given). *)
Definition v01t_hide (P : Prop) : Prop := P.

(** `lw` sign-extends bit 31; a value below 2^31 comes back as itself. *)
Lemma v01t_sx32 : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite unsigned_lit by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia). reflexivity.
Qed.

(** The cells after the first one. *)
Lemma v01t_rw_tl : forall m A c cs A', rw_cells rsegs m A (c :: cs) -> A' = A + Z.of_nat (csize c) ->
  rw_cells rsegs m A' cs.
Proof.
  unfold rw_cells, cells_at, wr_at. intros m A c cs A' [[[Hc Hwf] Hb] (Ha & Hl & Hw)] ->.
  cbn [cells_bytes] in Hb. apply bytes_at_app in Hb as [_ Hb]. rewrite cbytes_length in Hb by exact Hc.
  cbn [cells_size] in Hl, Hw.
  split; [split; [exact Hwf | exact Hb]|].
  split; [lia|]. split; [lia|].
  intros i Hi. replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia.
  apply Hw. lia.
Qed.

(** ** The write sets *)
(** reac_segconf_declared's write set lies apart from [A, A + k). *)
Lemma v01t_dW_disj : forall sp tp tab n tb tb' A k,
  A + k <= sp - DECLARED_STACK \/ sp <= A ->
  A + k <= tab + RVLAN_SIZE * Z.of_nat (length tb) \/ tab + RVLAN_SIZE * Z.of_nat (length tb') <= A ->
  A + k <= n \/ n + 4 <= A ->
  A + k <= tp - 164 \/ tp - 164 + 4 <= A ->
  disjoint_from (declared_W sp tp tab n tb tb') A k.
Proof.
  intros sp tp tab n tb tb' A k H1 H2 H3 H4. unfold declared_W, vtab_W.
  destruct (length tb <? length tb')%nat; cbn [app disjoint_from]; tauto.
Qed.

(** reac_segconf_declared's write set at this call site (sp = S - 240, n = sp + 0x5c, tp - 164 the errno cell) is
    inside V01_W: its frames [sp - 544, sp) and n in the stack interval, the appended entries in the table block. *)
Lemma v01t_dW_sub : forall X gt, Z.of_nat (length gt) <= v_cap X ->
  sub_fp (declared_W (v_sp X) 0x335b0 (v_tab X) (v_sp X + 92) (v_tab0 X) gt) (V01_W X).
Proof.
  intros X gt L x Hx. unfold V01_W in Hx. cbn [outside] in Hx. destruct Hx as (O1 & O2 & _ & O4 & _).
  unfold declared_W, vtab_W.
  destruct (length (v_tab0 X) <? length gt)%nat; cbn [app outside];
    unfold v_lo, v_sp, v_ntab, V01_FRAME, V01_ERRNO, DECLARED_STACK, SPLIT_STACK, RVLAN_SIZE in *;
    repeat split; lia.
Qed.

(** check_declared's write set [sp - 96, sp) is inside V01_W's stack interval. *)
Lemma v01t_cd_sub : forall X, sub_fp [(v_sp X - CHECK_DECLARED_STACK, v_sp X)] (V01_W X).
Proof.
  intros X x Hx. unfold V01_W in Hx. cbn [outside] in Hx |- *. destruct Hx as (O1 & _).
  unfold v_lo, v_sp, V01_FRAME, CHECK_DECLARED_STACK in *. split; [lia | exact I].
Qed.

(** ** The stretch *)
Lemma v01_tail : forall X : vctx, V01_geo X -> MainB.K_V01 -> V01_TAIL X.
Proof.
  intros X G K. destruct K as (_ & _ & _ & _ & HDC & HCD).
  unfold V01_TAIL, V01_PC_TAIL.
  intros want wt m w8 w30 w38 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 Hmd Hwant Hmem.
  destruct G as (S16 & Hlo & HS & Htp & Hcap & Hc1 & Hc16 & Hcl & _ & _ & _ & Ht1 & Ht16 & Htl & Hmt0 & Hmt16 & Hmtl
    & _ & Act & _ & _ & _ & Atmt & AEc & _ & AEt & AEmt & _ & _ & _ & _ & _ & _ & NIt & _).
  destruct Hmem as (Henv & Hcells & (jn & Hn0) & _ & Hrt & Hg & (ft & Hft) & Hmt & _ & Hwl & HMU & HWM).
  destruct Henv as (MI & ST & ROM & Hgg & (gw & Hgw) & (ev & Hev) & _ & Hrc & _).
  unfold V01_cells in Hcells.
  (* the numbers of the frame *)
  assert (Esp : v_sp X = v_S X - 240) by reflexivity.
  assert (Elo : v_lo X = v_S X - 65536) by reflexivity.
  assert (Ent : v_ntab X = 18 * (v_cap X + 1)) by reflexivity.
  assert (Enm : v_nmt X = 20 * (v_cap X + 1)) by reflexivity.
  assert (HC : 0 < SEG_C_SIZE) by (unfold SEG_C_SIZE; lia).
  pose proof (V01TailPure.vlan_init_len (seg_pay (v_inp X)) (proj1 Hcap)) as L0.
  change (Z.of_nat (length (v_tab0 X)) <= v_cap X) in L0.
  assert (AL : v01t_hide (v_c X mod 16 = 0 /\ v_tab X mod 16 = 0 /\ v_mt X mod 16 = 0 /\ v_sp X mod 16 = 0 /\
                          (v_sp X + 92) mod 4 = 0)).
  { clear - S16 Hc16 Ht16 Hmt16 Esp. unfold v01t_hide. rewrite Esp.
    split; [exact Hc16|]. split; [exact Ht16|]. split; [exact Hmt16|]. split; Z.div_mod_to_equations; lia. }
  clear S16 Hc16 Ht16 Hmt16.
  assert (Usp : bv_unsigned (Z_to_bv 64 (v_sp X)) = v_sp X) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 (v_sp X + 92)) = v_sp X + 92) by (apply unsigned_lit; lia).
  assert (Uc : bv_unsigned (Z_to_bv 64 (v_c X)) = v_c X) by (apply unsigned_lit; lia).
  assert (Ut : bv_unsigned (Z_to_bv 64 (v_tab X)) = v_tab X) by (apply unsigned_lit; lia).
  assert (Umt : bv_unsigned (Z_to_bv 64 (v_mt X)) = v_mt X) by (apply unsigned_lit; lia).
  assert (Ucap : bv_unsigned (Z_to_bv 64 (v_cap X)) = v_cap X) by (apply unsigned_lit; lia).
  assert (Umn : bv_unsigned (Z_to_bv 64 (Z.of_nat (length wt))) = Z.of_nat (length wt))
    by (apply unsigned_lit; lia).
  (* the int n at sp + 0x5c *)
  pose proof (v01t_rw_tl m (v_sp X + 0x58) (CB 4 jn) _ (v_sp X + 92) Hn0 ltac:(cbn [csize]; lia)) as Hn.
  clear Hn0.
  (* the last check of harness_ok: the reader's answer is the model's *)
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (mb_checks (v_inp X)))))))) as HV.
  change (vlans_are (r_declared (v_rc X) (v_tab0 X) (v_cap X)) (m_declared (v_mc X) (v_tab0 X) (v_cap X))
            (v_cap X) = true) in HV.
  rewrite Hmd in HV.
  (* reac_segconf_declared's premise *)
  assert (PRE1 : declared_pre m (v_sp X) (v_lo X) 0x335b0 (v_c X) (v_tab X) (v_cap X) (v_sp X + 92) (v_rc X)
                   (v_tab0 X) ev).
  { unfold declared_pre.
    split; [lia|]. split; [exact (proj1 AL)|]. split; [exact Hrc|]. split; [unfold apart; left; exact Hcl|].
    split.
    { unfold vtab_pre.
      split; [lia|]. split; [exact (proj1 (proj2 AL))|]. split; [exact Hrt|]. split; [lia|].
      split; [exists ft; exact Hft|]. split; [unfold apart, RVLAN_SIZE; lia|].
      split; [lia|]. split; [exact (proj2 (proj2 (proj2 (proj2 AL))))|]. split; [exact Hn|].
      split; [unfold apart; lia|]. unfold apart, RVLAN_SIZE; lia. }
    split; [exact Act|]. split; [unfold apart; lia|].
    split.
    { unfold errno_ok. split; [exact Hev|]. split; [unfold apart; lia|].
      unfold apart; left; apply Z.leb_le; reflexivity. }
    split; [exact AEc|]. split; [exact AEt|]. split; [unfold apart; lia|].
    split; [unfold ssp_ok; split; [exact Hgg | exists gw; exact Hgw]|].
    split; [apply (Z.le_trans _ 0x60000); [apply Z.leb_le; reflexivity | lia]|].
    split; [exact NIt|].
    split; [apply (Z.le_trans _ 0x60000); [apply Z.leb_le; reflexivity | lia]|].
    split; [|exact MI].
    unfold stack_ok. split; [exact ST|]. split; [unfold DECLARED_STACK, SPLIT_STACK; lia|].
    split; [exact (proj1 (proj2 (proj2 (proj2 AL))))|]. intros a Ha. apply ROM. lia. }
  (* 0x141ac .. 0x141c8: the arguments, then reac_segconf_declared(c, tab, cap, &n) *)
  do 8 step.
  rewrite ?Z.add_0_r.
  eapply evt_cut.
  { eapply HDC with (lo := v_lo X) (rc := v_rc X) (tb := v_tab0 X) (ev := ev).
    rewrite ?Usp, ?Htp, ?Uc, ?Ut, ?Ucap, ?Un. exact PRE1. }
  intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & -> &
    MU1 & WM1 & MI1 & ST1 & RT1 & N1 & _).
  clear PRE1.
  rewrite ?Usp, ?Htp, ?Ut, ?Ucap, ?Un in *.
  rewrite ret_pc_even by (try lia; reflexivity).
  set (r := r_declared (v_rc X) (v_tab0 X) (v_cap X)) in *.
  destruct (V01TailPure.vlans_are_fst _ _ _ _ HV) as [Egw L1].
  (* main's frame, mt's table and the guard entry across the call *)
  apply (rw_cells_transport rsegs (declared_W (v_sp X) 0x335b0 (v_tab X) (v_sp X + 92) (v_tab0 X) (snd r)) m m1)
    in Hcells;
    [| exact MU1 | exact WM1 |
     apply v01t_dW_disj; cbn [cells_size csize]; unfold DECLARED_STACK, SPLIT_STACK, RVLAN_SIZE; lia].
  assert (Hmt1 : mtab_at rsegs m1 (v_mt X) wt).
  { destruct Hmt as (bm & BM & EM). exists bm. split; [|exact EM].
    apply (bytes_at_transport rsegs (declared_W (v_sp X) 0x335b0 (v_tab X) (v_sp X + 92) (v_tab0 X) (snd r))
             m m1 _ _ BM MU1).
    destruct EM as [LB _]. rewrite LB. unfold apart in Atmt, AEmt. unfold V01_ERRNO in AEmt.
    apply v01t_dW_disj; unfold DECLARED_STACK, SPLIT_STACK, RVLAN_SIZE; lia. }
  pose proof (declared_guard_kept (v_sp X) (v_lo X) 0x335b0 (v_tab X) (v_sp X + 92) (v_cap X) (v_rc X) (v_tab0 X)
                m m1 L0 ltac:(unfold DECLARED_STACK, SPLIT_STACK; lia) ltac:(unfold apart, RVLAN_SIZE; lia)
                ltac:(unfold apart, RVLAN_SIZE; lia) AEt MU1 Hg) as Hg1.
  clear Hn Hft Hev Hgg Hgw Hrc Hg Hrt Hmt ST MI.
  assert (Ulen : bv_unsigned (Z_to_bv 64 (Z.of_nat (length (snd r)))) = Z.of_nat (length (snd r)))
    by (apply unsigned_lit; lia).
  (* 0x141cc .. 0x141e8: the arguments, then check_declared(got, want, tab, n, mt, mn, cap) *)
  do 8 step.
  rewrite ?Z.add_0_r.
  rewrite (v01t_sx32 (Z.of_nat (length (snd r)))) by lia.
  eapply evt_cut.
  { eapply HCD with (lo := v_lo X) (gv := fst r) (wv := want) (gt := snd r) (wt := wt).
    rewrite ?Usp, ?Ut, ?Umt, ?Ucap, ?Ulen, ?Umn, ?unsigned_lit_wrap.
    unfold check_declared_pre.
    split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hcap|].
    split; [lia|]. split; [exact (proj1 (proj2 AL))|]. split; [exact RT1|]. split; [exact Hg1|].
    split; [unfold apart, RVLAN_SIZE; lia|]. split; [reflexivity|].
    split; [lia|]. split; [exact (proj1 (proj2 (proj2 AL)))|]. split; [exact Hmt1|].
    split; [unfold apart, MVLAN_SIZE; lia|]. split; [exact Hwl|]. split; [reflexivity|].
    split; [rewrite <- surjective_pairing; exact HV|].
    split; [|exact MI1].
    unfold stack_ok. split; [exact ST1|]. split; [unfold CHECK_DECLARED_STACK; lia|].
    split; [exact (proj1 (proj2 (proj2 (proj2 AL))))|]. intros a Ha. apply ROM. lia. }
  intros ms' (z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m2 & -> &
    MU2 & WM2 & MI2 & _ & _).
  rewrite Usp in MU2.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x141ec: V01_post *)
  apply evt_done. unfold V01_post. cbv beta.
  do 25 eexists. split; [reflexivity|].
  split; [|split; [eapply wmono_trans; [eapply wmono_trans; [exact HWM | exact WM1] | exact WM2] | exact MI2]].
  apply (munch_trans _ (v_m0 X) m1 m2).
  - apply (munch_trans _ (v_m0 X) m m1); [exact HMU|].
    eapply munch_weaken; [apply (v01t_dW_sub X (snd r) L1) | exact MU1].
  - eapply munch_weaken; [apply v01t_cd_sub | exact MU2].
Qed.
