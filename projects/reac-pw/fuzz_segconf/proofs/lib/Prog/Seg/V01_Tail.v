(* Segment V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f = pinned 3776ca44d75c): TAIL,
   0x13f04 .. 0x13f3c (plain binary), from TAIL to END (0x13f40),
   V01_Inv.v's [v01_tail_stmt].
   - 0x13f04 .. 0x13f1c: a3 = sp + 0x3c (&n), s1 = 0x30(sp) = c, a0 = c, a1 = s3 = tab, s2 = 0x10(sp) = cap, a2 = cap,
     `jal reac_segconf_declared` (reac_segconf_declared_contract, lo = S - 65536, rc = v_rc inp, tb = v_tab0 inp; the
     premise is [v01t_dpre]: c, the table, *n and the errno cell from v01_base / v01_tail_mem, carried from m0 over
     v01_W; the errno cell and the stack-protector cells lie in reserved segments of the image (vm_compute over
     segments_reserved rsegs), so apart from every block, which no reserved segment covers (blk_noimg)).
   - 0x13f20 .. 0x13f3c: a3 = `lw` n (= length tb', below cap), a1 = 0x18(sp) = fst V01_RES, a2 = tab, s4 = 0x20(sp) =
     mt, a4 = mt, a5 = s6 = mn, a6 = s2 = cap, `jal check_declared` (check_declared_contract; the premise is
     [v01t_cpre]: vlans_are is MainBPure.mb_checks' last conjunct, fst V01_RES lies in [-1, 32] (V01TailPure.
     m_decl_go_fst and mconf_enc's 32 segments), the guard entry kept by declared_guard_kept, mt's table carried over
     declared_W).
   - END: munch over v01_We (declared_W, the frames below sp and the errno cell all lie inside it), wmono, mem_inv.
   [V01TailPure] holds the build-independent lemmas.
   Part of the proof of LLVMFuzzerTestOneInput: this file is part of segment V01 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec seg_env seg_cuts
  reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c check_declared_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import MainBPure V01_Inv.
Import ListNotations.
Open Scope Z_scope.

Module V01TailPure.

(* m_declared's count: -1 (the table is full) or between added and added + the number of segments. *)
Lemma m_decl_go_fst : forall segs tab cap added,
  fst (m_decl_go segs tab cap added) = -1 \/
  added <= fst (m_decl_go segs tab cap added) <= added + Z.of_nat (length segs).
Proof.
  induction segs as [|g r IH]; intros tab cap added.
  - right. cbn [m_decl_go fst length Z.of_nat]. lia.
  - assert (EL : Z.of_nat (length (g :: r)) = Z.of_nat (length r) + 1)
      by (cbn [length]; rewrite Nat2Z.inj_succ; reflexivity).
    rewrite EL. cbn [m_decl_go].
    destruct (ms_ignore g); cbv beta iota; [destruct (IH tab cap added); [left | right]; lia|].
    destruct (m_split (ms_name g)) as [[p v]|]; cbv beta iota;
      [|destruct (IH tab cap added); [left | right]; lia].
    match goal with |- context [if existsb ?f ?l then _ else _] => destruct (existsb f l) end; cbv beta iota;
      [destruct (IH tab cap added); [left | right]; lia|].
    destruct (cap <=? Z.of_nat (length tab)); cbv beta iota; [left; reflexivity|].
    destruct (IH (tab ++ [(p, v)]) cap (added + 1)); [left | right]; lia.
Qed.

(* `lw` of a small non-negative int. *)
Lemma v01t_sx32 : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite unsigned_lit by lia.
  rewrite bv_swrap_small; [reflexivity|]. change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

(* [x, x + k) lies inside one reserved segment of the image. *)
Definition inresv (segs : list Segment) (x k : Z) : bool :=
  existsb (fun s : word * word => (bv_unsigned (fst s) <=? x) && (x + k <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
    (segments_reserved segs).

(* A block with no byte in a reserved segment lies wholly on one side of such a range. *)
Lemma resv_apart : forall segs x k a n, inresv segs x k = true -> 0 < k -> 0 < n -> blk_noimg segs a n ->
  apart x k a (a + n).
Proof.
  intros segs x k a n E Hk Hn B. unfold inresv in E. apply existsb_exists in E as (s & Hs & E).
  cbv beta in E. apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  unfold apart.
  pose proof (B 0 ltac:(lia) s Hs) as B0.
  destruct (Z_lt_le_dec a (bv_unsigned (fst s))) as [H1|H1].
  - destruct (Z_lt_le_dec (a + n - 1) (bv_unsigned (fst s))) as [H2|H2]; [right; lia|].
    exfalso. apply (B (bv_unsigned (fst s) - a) ltac:(lia) s Hs). lia.
  - left. destruct (Z_lt_le_dec a (bv_unsigned (fst s) + bv_unsigned (snd s))) as [H3|H3];
      [exfalso; apply B0; lia | lia].
Qed.

(* A cell list splits at a cell boundary. *)
Lemma rwc_app : forall segs m A cs1 cs2 k, Z.of_nat (cells_size cs1) = k ->
  rw_cells segs m A (cs1 ++ cs2) -> rw_cells segs m A cs1 /\ rw_cells segs m (A + k) cs2.
Proof.
  intros segs m A cs1 cs2 k Hk [[Hwf Hb] (Ha & Hn & Hw)]. subst k.
  apply cells_wf_app in Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  rewrite cells_size_app, Nat2Z.inj_add in Hn, Hw.
  split; split.
  - split; [exact W1 | exact B1].
  - split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [exact W2 | exact B2].
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hw. lia.
Qed.

End V01TailPure.

Import V01TailPure.

(* ---- The image: the errno cell and the two stack-protector cells lie in reserved segments ---- *)
Lemma v01t_resv_errno : inresv rsegs V01_ERRNO 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma v01t_resv_got : inresv rsegs 0x21818 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma v01t_resv_guard : inresv rsegs 0x52e80 8 = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- Write sets ---- *)
(* main's frame cells [sp, sp + 60) lie outside reac_segconf_declared's write set. *)
Lemma v01t_dj_frame : forall inp S tab SP tb tb',
  SP = S - 208 -> 0x60000 <= S - 65536 -> tab + TAB_N inp <= S - 65536 -> Z.of_nat (length tb') <= v_cap inp ->
  disjoint_from (declared_W SP 0x32c10 tab (SP + 60) tb tb') SP 60.
Proof.
  intros inp S tab SP tb tb' ESP SLO TB L. pose proof (Nat2Z.is_nonneg (length tb)).
  unfold TAB_N, RVLAN_SIZE, v_cap in *.
  unfold declared_W, vtab_W, DECLARED_STACK, SPLIT_STACK, RVLAN_SIZE.
  match goal with |- context [if ?b then _ else _] => destruct b end; cbn [app disjoint_from]; repeat split; lia.
Qed.

(* So does the table mt (its first n bytes). *)
Lemma v01t_dj_mt : forall inp S tab mt SP tb tb' n,
  SP = S - 208 -> 0x60000 <= S - 65536 -> mt + MT_N inp <= S - 65536 ->
  apart tab (TAB_N inp) mt (mt + MT_N inp) -> apart V01_ERRNO 4 mt (mt + MT_N inp) ->
  0 <= n <= MT_N inp -> Z.of_nat (length tb') <= v_cap inp -> 0 <= v_cap inp ->
  disjoint_from (declared_W SP 0x32c10 tab (SP + 60) tb tb') mt n.
Proof.
  intros inp S tab mt SP tb tb' n ESP SLO MTB AT AE Hn L C. pose proof (Nat2Z.is_nonneg (length tb)).
  unfold apart, TAB_N, MT_N, RVLAN_SIZE, MVLAN_SIZE, V01_ERRNO, v_cap in *.
  unfold declared_W, vtab_W, DECLARED_STACK, SPLIT_STACK, RVLAN_SIZE.
  match goal with |- context [if ?b then _ else _] => destruct b end; cbn [app disjoint_from]; repeat split; lia.
Qed.

Lemma v01t_sub_W : forall inp S tab mt, sub_fp (v01_W inp S tab mt) (v01_We inp S tab mt).
Proof. intros inp S tab mt x Hx. unfold v01_We in Hx. cbn [outside] in Hx. exact (proj2 Hx). Qed.

(* reac_segconf_declared's write set lies inside v01_We. *)
Lemma v01t_sub_decl : forall inp S tab mt SP tb tb',
  SP = S - 208 -> Z.of_nat (length tb') <= v_cap inp ->
  sub_fp (declared_W SP 0x32c10 tab (SP + 60) tb tb') (v01_We inp S tab mt).
Proof.
  intros inp S tab mt SP tb tb' ESP L x Hx. pose proof (Nat2Z.is_nonneg (length tb)).
  unfold v01_We, v01_W, V01_ERRNO, TAB_N, MT_N, RVLAN_SIZE, MVLAN_SIZE, v_cap in *.
  cbn [outside] in Hx. destruct Hx as (O1 & O2 & O3 & O4 & _).
  unfold declared_W, vtab_W, DECLARED_STACK, SPLIT_STACK, RVLAN_SIZE.
  match goal with |- context [if ?b then _ else _] => destruct b end; cbn [app outside]; repeat split;
    intros ?; lia.
Qed.

(* check_declared's frame lies inside v01_We. *)
Lemma v01t_sub_chk : forall inp S tab mt SP, SP = S - 208 -> sub_fp [(SP - 48, SP)] (v01_We inp S tab mt).
Proof.
  intros inp S tab mt SP ESP x Hx. unfold v01_We, v01_W in Hx. cbn [outside] in Hx |- *.
  destruct Hx as (_ & O2 & _). split; [intros ?; lia | exact I].
Qed.

(* ---- reac_segconf_declared's premise at 0x13f1c ---- *)
Lemma v01t_dpre : forall inp S c mm tab mt m0 m,
  v01_geo inp S c mm tab mt -> v01_base inp c mm m0 -> v01_tail_mem inp S c tab mt m0 m ->
  exists ev, declared_pre m (S - 208) (S - 65536) 0x32c10 c tab (v_cap inp) (S - 208 + 60) (v_rc inp) (v_tab0 inp) ev.
Proof.
  intros inp S c mm tab mt m0 m GEO BASE TM.
  destruct GEO as (S16 & SLO & SHI & SROM & C4k & CB & C16 & CNI & _ & _ & _ & _ & T4k & TB & T16 & TNI &
    MT4k & MTB & MT16 & MTNI & _ & ACT & ACMT & _ & _ & _).
  destruct BASE as ((bsc & BC & EC) & _ & (ev & EV0) & (SG & g & SQ)).
  destruct TM as ((MU & WM & MI & STK & RT & (fr & FREE) & _) & _ & (w00 & w08 & w28 & w38 & FR)).
  unfold v01_frame in FR.
  pose proof (rwc_app rsegs m (S - 208)
    [C8 w00; C8 w08; C8 (Z_to_bv 64 (v_cap inp)); C8 (Z_to_bv 64 (fst (V01_RES inp))); C8 (Z_to_bv 64 mt);
     C8 w28; C8 (Z_to_bv 64 c); C4 w38] [C4 (Z_to_bv 64 (v_n0 inp))] 60 eq_refl FR) as [_ FN].
  clear FR.
  pose proof (mb_cap inp) as CAP.
  assert (Bcap : 0 <= v_cap inp < 40) by exact CAP.
  assert (L0 : Z.of_nat (length (v_tab0 inp)) <= v_cap inp) by exact (vlan_init_len (seg_pay inp) (proj1 CAP)).
  assert (TN : 0 < TAB_N inp) by (unfold TAB_N, RVLAN_SIZE; lia).
  assert (MN : 0 < MT_N inp) by (unfold MT_N, MVLAN_SIZE; lia).
  assert (CN : 0 < SEG_C_SIZE) by (unfold SEG_C_SIZE; lia).
  pose proof (resv_apart rsegs V01_ERRNO 4 tab (TAB_N inp) v01t_resv_errno ltac:(lia) TN TNI) as ET.
  pose proof (resv_apart rsegs V01_ERRNO 4 mt (MT_N inp) v01t_resv_errno ltac:(lia) MN MTNI) as EMT.
  pose proof (resv_apart rsegs V01_ERRNO 4 c SEG_C_SIZE v01t_resv_errno ltac:(lia) CN CNI) as EC'.
  pose proof (resv_apart rsegs 0x21818 8 tab (TAB_N inp) v01t_resv_got ltac:(lia) TN TNI) as GT.
  pose proof (resv_apart rsegs 0x21818 8 mt (MT_N inp) v01t_resv_got ltac:(lia) MN MTNI) as GMT.
  pose proof (resv_apart rsegs 0x52e80 8 tab (TAB_N inp) v01t_resv_guard ltac:(lia) TN TNI) as QT.
  pose proof (resv_apart rsegs 0x52e80 8 mt (MT_N inp) v01t_resv_guard ltac:(lia) MN MTNI) as QMT.
  (* What lies below the stack window and apart from the two tables keeps its bytes from m0. *)
  assert (DW : forall a n, a + n <= S - 65536 -> apart a n mt (mt + MT_N inp) -> apart a n tab (tab + TAB_N inp) ->
                 disjoint_from (v01_W inp S tab mt) a n).
  { intros a n H1 H2 H3. unfold v01_W. cbn [disjoint_from].
    split; [left; exact H1|]. split; [exact H2|]. split; [exact H3 | exact I]. }
  assert (RC : rconf_at rsegs m c (v_rc inp)).
  { exists bsc. split; [|exact EC]. eapply bytes_at_transport; [exact BC | exact MU |].
    rewrite (proj1 EC). apply DW; [exact CB | exact ACMT | exact ACT]. }
  assert (EV : rw_cells rsegs m V01_ERRNO [C4 ev]).
  { eapply rw_cells_transport; [exact EV0 | exact MU | exact WM |].
    change (Z.of_nat (cells_size [C4 ev])) with 4. apply DW; [unfold V01_ERRNO; lia | exact EMT | exact ET]. }
  assert (SSP : ssp_ok m).
  { split.
    - eapply bytes_at_transport; [exact SG | exact MU |]. rewrite length_le8.
      match goal with |- disjoint_from _ ?a _ => change a with 0x21818 end. change (Z.of_nat 8) with 8.
      apply DW; [lia | exact GMT | exact GT].
    - exists g. eapply bytes_at_transport; [exact SQ | exact MU |]. rewrite length_le8.
      match goal with |- disjoint_from _ ?a _ => change a with 0x52e80 end. change (Z.of_nat 8) with 8.
      apply DW; [lia | exact QMT | exact QT]. }
  assert (TB' : tab + 18 * (v_cap inp + 1) <= S - 65536) by exact TB.
  assert (CB' : c + 16616 <= S - 65536) by exact CB.
  exists ev. unfold declared_pre.
  split; [lia|].
  split; [exact C16|].
  split; [exact RC|].
  split; [left; exact CB|].
  split.
  { unfold vtab_pre.
    split; [lia|]. split; [exact T16|]. split; [exact RT|]. split; [split; [exact L0 | lia]|].
    split; [exists fr; exact FREE|]. split; [left; exact TB|].
    split; [lia|]. split; [clear - S16; Z.div_mod_to_equations; lia|].
    split; [exact FN|]. split; [right; lia|].
    right. unfold RVLAN_SIZE. lia. }
  split; [exact ACT|].
  split; [right; lia|].
  split.
  { split; [exact EV|]. split; [left; lia|].
    left. match goal with |- _ <= sa_guard ?x => change (sa_guard x) with 0x52e80 end. lia. }
  split; [exact EC'|].
  split; [exact ET|].
  split; [left; lia|].
  split; [exact SSP|].
  split; [match goal with |- sa_img_end ?x <= _ => change (sa_img_end x) with 0x536e8 end; lia|].
  split; [exact TNI|].
  split; [match goal with |- sa_img_end ?x <= _ => change (sa_img_end x) with 0x536e8 end; lia|].
  split.
  { split; [exact STK|]. split; [unfold DECLARED_STACK, SPLIT_STACK; lia|].
    split; [clear - S16; Z.div_mod_to_equations; lia|]. intros a Ha. apply SROM. lia. }
  exact MI.
Qed.

(* ---- check_declared's premise at 0x13f3c ---- *)
Lemma v01t_cpre : forall inp S c mm tab mt m0 m m1 SP,
  SP = S - 208 ->
  v01_geo inp S c mm tab mt -> v01_base inp c mm m0 -> v01_tail_mem inp S c tab mt m0 m ->
  munch (declared_W SP 0x32c10 tab (SP + 60) (v_tab0 inp) (snd (r_declared (v_rc inp) (v_tab0 inp) (v_cap inp))))
    m m1 ->
  mem_inv rsegs m1 -> stk rsegs m1 (S - 65536) SP ->
  rtab_at rsegs m1 tab (snd (r_declared (v_rc inp) (v_tab0 inp) (v_cap inp))) ->
  check_declared_pre m1 SP (S - 65536)
    (fst (r_declared (v_rc inp) (v_tab0 inp) (v_cap inp)) mod 2 ^ 64) (fst (V01_RES inp) mod 2 ^ 64)
    tab (Z.of_nat (length (snd (r_declared (v_rc inp) (v_tab0 inp) (v_cap inp)))))
    mt (Z.of_nat (length (snd (V01_RES inp)))) (v_cap inp)
    (fst (r_declared (v_rc inp) (v_tab0 inp) (v_cap inp))) (fst (V01_RES inp))
    (snd (r_declared (v_rc inp) (v_tab0 inp) (v_cap inp))) (snd (V01_RES inp)).
Proof.
  intros inp S c mm tab mt m0 m m1 SP ESP GEO BASE TM MU1 MI1 ST1 RT1.
  destruct GEO as (S16 & SLO & SHI & SROM & _ & _ & _ & _ & _ & _ & _ & _ & T4k & TB & T16 & TNI &
    MT4k & MTB & MT16 & MTNI & _ & _ & _ & _ & _ & ATMT).
  destruct BASE as (_ & (bsm & _ & (_ & L32 & _)) & _ & _).
  destruct TM as ((_ & _ & _ & _ & _ & _ & GU) & (LWT & (bst & BT & TENC) & _) & _).
  pose proof (mb_cap inp) as CAP.
  assert (Bcap : 0 <= v_cap inp < 40) by exact CAP.
  assert (L0 : Z.of_nat (length (v_tab0 inp)) <= v_cap inp) by exact (vlan_init_len (seg_pay inp) (proj1 CAP)).
  assert (TN : 0 < TAB_N inp) by (unfold TAB_N, RVLAN_SIZE; lia).
  assert (MN : 0 < MT_N inp) by (unfold MT_N, MVLAN_SIZE; lia).
  pose proof (resv_apart rsegs V01_ERRNO 4 tab (TAB_N inp) v01t_resv_errno ltac:(lia) TN TNI) as ET.
  pose proof (resv_apart rsegs V01_ERRNO 4 mt (MT_N inp) v01t_resv_errno ltac:(lia) MN MTNI) as EMT.
  destruct (r_decl_go_len (rc_seg (v_rc inp)) (v_tab0 inp) (v_cap inp) 0 L0) as [_ LR].
  change (r_decl_go (rc_seg (v_rc inp)) (v_tab0 inp) (v_cap inp) 0)
    with (r_declared (v_rc inp) (v_tab0 inp) (v_cap inp)) in LR.
  pose proof (mb_checks inp) as (_ & _ & _ & _ & _ & _ & VL).
  change (vlans_are (r_declared (v_rc inp) (v_tab0 inp) (v_cap inp)) (V01_RES inp) (v_cap inp) = true) in VL.
  assert (GW : fst (r_declared (v_rc inp) (v_tab0 inp) (v_cap inp)) = fst (V01_RES inp)).
  { pose proof VL as V. unfold vlans_are in V.
    apply andb_true_iff in V as [V _]. apply andb_true_iff in V as [V _]. apply andb_true_iff in V as [V _].
    apply Z.eqb_eq in V. exact V. }
  assert (L32Z : Z.of_nat (length (mc_seg (v_mc inp))) <= 32) by (apply (Nat2Z.inj_le _ 32); exact L32).
  assert (WB : -1 <= fst (V01_RES inp) <= 32).
  { destruct (m_decl_go_fst (mc_seg (v_mc inp)) (v_tab0 inp) (v_cap inp) 0) as [W|W];
      change (m_decl_go (mc_seg (v_mc inp)) (v_tab0 inp) (v_cap inp) 0) with (V01_RES inp) in W; lia. }
  pose proof (proj1 TENC) as LB.
  assert (LBZ : Z.of_nat (length bst) = 20 * Z.of_nat (length (snd (V01_RES inp))))
    by (rewrite LB, Nat2Z.inj_mul; reflexivity).
  subst SP.
  unfold check_declared_pre.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [rewrite GW; lia|].
  split; [lia|].
  split; [exact Bcap|].
  split; [lia|].
  split; [exact T16|].
  split; [exact RT1|].
  split.
  { apply (declared_guard_kept (S - 208) (S - 65536) 0x32c10 tab (S - 208 + 60) (v_cap inp) (v_rc inp) (v_tab0 inp)
             m m1).
    - exact L0.
    - unfold DECLARED_STACK, SPLIT_STACK. lia.
    - left. exact TB.
    - right. assert (TB' : tab + 18 * (v_cap inp + 1) <= S - 65536) by exact TB. unfold RVLAN_SIZE. lia.
    - exact ET.
    - exact MU1.
    - exact GU. }
  split; [left; exact TB|].
  split; [reflexivity|].
  split; [lia|].
  split; [exact MT16|].
  split.
  { exists bst. split; [|exact TENC]. eapply bytes_at_transport; [exact BT | exact MU1 |].
    apply (v01t_dj_mt inp S tab mt (S - 208)); [reflexivity | exact SLO | exact MTB | exact ATMT | exact EMT | | exact LR
      | exact (proj1 Bcap)].
    rewrite LBZ. split; [lia|]. unfold MT_N, MVLAN_SIZE. unfold v_cap in LWT. lia. }
  split; [left; exact MTB|].
  split; [exact LWT|].
  split; [reflexivity|].
  split; [rewrite <- !surjective_pairing; exact VL|].
  split.
  { split; [exact ST1|]. split; [unfold CHECK_DECLARED_STACK; lia|].
    split; [clear - S16; Z.div_mod_to_equations; lia|]. intros a Ha. apply SROM. lia. }
  exact MI1.
Qed.

(* bv_unsigned of a register the run computed. *)
Ltac v01t_uz :=
  first [ rewrite unsigned_lit by lia; lia
        | rewrite v01t_sx32 by lia; rewrite unsigned_lit by lia; lia ].

(* ---- TAIL ---- *)
Lemma v01_tail : reac_segconf_declared_contract -> check_declared_contract -> v01_tail_stmt.
Proof.
  intros DECL CHK. unfold v01_tail_stmt.
  intros inp S c mm tab mt m0 gp tp F fc Q GEO BASE TP KEND.
  unfold K_tail.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 m TM.
  destruct (v01t_dpre inp S c mm tab mt m0 m GEO BASE TM) as (ev & DP).
  pose proof GEO as (_ & SLO & SHI & _ & C4k & CB & _ & _ & _ & _ & _ & _ & T4k & TB & _ & _ & MT4k & MTB & _).
  pose proof TM as ((MU0 & WM0 & _ & _ & _ & _ & _) & (LWT & _ & _) & (w00 & w08 & w28 & w38 & FR)).
  unfold v01_frame in FR.
  pose proof (rwc_app rsegs m (S - 208)
    [C8 w00; C8 w08; C8 (Z_to_bv 64 (v_cap inp)); C8 (Z_to_bv 64 (fst (V01_RES inp))); C8 (Z_to_bv 64 mt);
     C8 w28; C8 (Z_to_bv 64 c); C4 w38] [C4 (Z_to_bv 64 (v_n0 inp))] 60 eq_refl FR) as [F1 _].
  clear FR.
  pose proof (mb_cap inp) as CAP.
  assert (Bcap : 0 <= v_cap inp < 40) by exact CAP.
  assert (L0 : Z.of_nat (length (v_tab0 inp)) <= v_cap inp) by exact (vlan_init_len (seg_pay inp) (proj1 CAP)).
  destruct (r_decl_go_len (rc_seg (v_rc inp)) (v_tab0 inp) (v_cap inp) 0 L0) as [_ LR].
  change (r_decl_go (rc_seg (v_rc inp)) (v_tab0 inp) (v_cap inp) 0)
    with (r_declared (v_rc inp) (v_tab0 inp) (v_cap inp)) in LR.
  assert (Bc : 0 <= c < 2 ^ 64) by (clear - C4k CB SHI; unfold SEG_C_SIZE in CB; lia).
  assert (Bt : 0 <= tab < 2 ^ 64) by (clear - T4k TB SHI CAP; unfold TAB_N, RVLAN_SIZE in TB; lia).
  assert (Bm : 0 <= mt < 2 ^ 64) by (clear - MT4k MTB SHI CAP; unfold MT_N, MVLAN_SIZE in MTB; lia).
  assert (HSP : exists SP, SP = S - 208) by (eexists; reflexivity).
  destruct HSP as (SP & ESP).
  rewrite <- ESP in F1, DP.
  unfold v01_tail_st, vst. rewrite <- ESP.
  assert (Bsp : 0 <= SP /\ SP + 64 < 2 ^ 64) by lia.
  (* 0x13f04 addi a3,sp,0x3c; 0x13f08 ld s1,0x30(sp); 0x13f0c mv a0,s1; 0x13f10 mv a1,s3; 0x13f14 ld s2,0x10(sp);
     0x13f18 mv a2,s2; 0x13f1c jal reac_segconf_declared *)
  do 6 step. step.
  assert (E2 : bv_unsigned (Z_to_bv 64 SP) = SP) by v01t_uz.
  assert (E10 : bv_unsigned (Z_to_bv 64 c) = c) by v01t_uz.
  assert (E11 : bv_unsigned (Z_to_bv 64 tab) = tab) by v01t_uz.
  assert (E12 : bv_unsigned (Z_to_bv 64 (v_cap inp)) = v_cap inp) by v01t_uz.
  assert (E13 : bv_unsigned (Z_to_bv 64 (SP + 60)) = SP + 60) by v01t_uz.
  eapply evt_cut.
  { eapply DECL with (lo := S - 65536) (rc := v_rc inp) (tb := v_tab0 inp) (ev := ev).
    rewrite E2, TP, E10, E11, E12, E13. exact DP. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
              MU1 & WM1 & MI1 & ST1 & RT1 & RN1 & _).
  rewrite E2, TP, E11, E13, E12 in MU1. rewrite E2 in ST1. rewrite E11, E12 in RT1. rewrite E13, E12 in RN1.
  rewrite ?E12.
  rewrite ret_pc_even by (try lia; reflexivity).
  pose proof (rw_cells_transport rsegs _ m m1 SP _ F1 MU1 WM1
                (v01t_dj_frame inp S tab SP (v_tab0 inp) (snd (r_declared (v_rc inp) (v_tab0 inp) (v_cap inp)))
                   ESP SLO TB LR)) as F1'.
  clear F1 DP.
  (* 0x13f20 lw a3,0x3c(sp); 0x13f24 ld a1,0x18(sp); 0x13f28 mv a2,s3; 0x13f2c ld s4,0x20(sp); 0x13f30 mv a4,s4;
     0x13f34 mv a5,s6; 0x13f38 mv a6,s2; 0x13f3c jal check_declared *)
  step.
  try (rewrite v01t_sx32 by lia).
  do 6 step. step.
  assert (F10 : bv_unsigned (Z_to_bv 64 (fst (r_declared (v_rc inp) (v_tab0 inp) (v_cap inp)))) =
                fst (r_declared (v_rc inp) (v_tab0 inp) (v_cap inp)) mod 2 ^ 64) by (apply unsigned_lit_wrap).
  assert (F11 : bv_unsigned (Z_to_bv 64 (fst (V01_RES inp))) = fst (V01_RES inp) mod 2 ^ 64)
    by (apply unsigned_lit_wrap).
  assert (F13 : bv_unsigned (Z_to_bv 64 (Z.of_nat (length (snd (r_declared (v_rc inp) (v_tab0 inp) (v_cap inp))))))
                = Z.of_nat (length (snd (r_declared (v_rc inp) (v_tab0 inp) (v_cap inp))))) by v01t_uz.
  assert (F14 : bv_unsigned (Z_to_bv 64 mt) = mt) by v01t_uz.
  assert (F15 : bv_unsigned (Z_to_bv 64 (Z.of_nat (length (snd (V01_RES inp))))) = Z.of_nat (length (snd (V01_RES inp))))
    by v01t_uz.
  eapply evt_cut.
  { eapply CHK with (lo := S - 65536) (gv := fst (r_declared (v_rc inp) (v_tab0 inp) (v_cap inp)))
      (wv := fst (V01_RES inp)) (gt := snd (r_declared (v_rc inp) (v_tab0 inp) (v_cap inp)))
      (wt := snd (V01_RES inp)).
    rewrite E2, F10, F11, E11, F13, F14, F15, E12.
    exact (v01t_cpre inp S c mm tab mt m0 m m1 SP ESP GEO BASE TM MU1 MI1 ST1 RT1). }
  intros ms'' (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' &
               t6'' & m2 & -> & MU2 & WM2 & MI2 & _ & _).
  rewrite E2 in MU2.
  rewrite ret_pc_even by (try lia; reflexivity).
  apply evt_done.
  assert (MUF : munch (v01_We inp S tab mt) m0 m2).
  { apply (munch_trans _ m0 m1 m2).
    - apply (munch_trans _ m0 m m1).
      + exact (munch_weaken _ _ _ _ (v01t_sub_W inp S tab mt) MU0).
      + exact (munch_weaken _ _ _ _ (v01t_sub_decl inp S tab mt SP (v_tab0 inp) _ ESP LR) MU1).
    - exact (munch_weaken _ _ _ _ (v01t_sub_chk inp S tab mt SP ESP) MU2). }
  pose proof (wmono_trans rsegs _ _ _ (wmono_trans rsegs _ _ _ WM0 WM1) WM2) as WMF.
  subst SP.
  unfold K_end, v01_end_st, vst in KEND.
  eapply KEND; [exact MUF | exact WMF | exact MI2].
Qed.
