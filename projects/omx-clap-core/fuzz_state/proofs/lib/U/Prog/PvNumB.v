From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require YI06.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame Exec Cells Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct PjIn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import PvDefs PvModel PvGlue PvMain0 PvPaths PvV.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import fuzz_malloc_c memcpy_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require ReaderKB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require PvItems PvLit PvStr PvNum PvNumH MallocRuns strtod_c.
Import ListNotations.
Local Open Scope Z_scope.
Module Frame := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Frame.
Module MState := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.MState.
Module Mem := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.
Module Exec := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Exec.
Module Cells := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Cells.
Module Step := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Step.

(* Proof speed (internal path, Proof speed (2)): the five lia sites of pv_num_ok that use rs_hide_all need
   none of the context's disjunctions or mod facts, so they are cleared before lia sees them (a tactic only: no new
   Theorem, Lemma or Definition). *)
Local Ltac rs_hide_all := repeat match goal with
  | H : _ \/ _ |- _ => clear H
  | H : _ mod _ = _ |- _ => clear H end.

Lemma MS_inj : forall R1 F1 p1 c1 m1 ro1 R2 F2 p2 c2 m2 ro2,
  MState.MS R1 F1 p1 c1 None m1 ro1 = MState.MS R2 F2 p2 c2 None m2 ro2 ->
  R1 = R2 /\ F1 = F2 /\ p1 = p2 /\ c1 = c2 /\ m1 = m2.
Proof.
  intros R1 F1 p1 c1 m1 ro1 R2 F2 p2 c2 m2 ro2 H.
  pose proof (f_equal ms_regs H) as E1. pose proof (f_equal ms_fregs H) as E2. pose proof (f_equal ms_pc_val H) as E3.
  pose proof (f_equal ms_fcsr H) as E4. pose proof (f_equal ms_mem H) as E5. cbn in E1, E2, E3, E4, E5. auto.
Qed.

Lemma ret_ok_15600 : YK0s.ret_ok (Z_to_bv 64 0x146f4).
Proof. vm_compute. reflexivity. Qed.

Lemma pj_in_ok_keep : forall m m' q text len p d tb, pj_in_ok rsegs m q text len p d tb ->
  (forall x, q <= x < q + 24 -> mbyte rsegs m' x = mbyte rsegs m x /\ (writable_at rsegs m x -> writable_at rsegs m' x)) ->
  (forall i, 0 <= i < len -> mbyte rsegs m' (text + i) = mbyte rsegs m (text + i)) ->
  pj_in_ok rsegs m' q text len p d tb.
Proof.
  intros m m' q text len p d tb (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) HQ HT.
  split; [apply (PvStr.bytes_keep m m' q _ H1); intros i Hi; rewrite Mem.length_le8 in Hi; exact (proj1 (HQ (q + i) ltac:(lia)))|].
  split; [apply (PvStr.bytes_keep m m' (q + 8) _ H2); intros i Hi; rewrite Mem.length_le8 in Hi;
          replace (q + 8 + i) with (q + (8 + i)) by lia; exact (proj1 (HQ (q + (8 + i)) ltac:(lia)))|].
  split; [apply (PvStr.bytes_keep m m' (q + 16) _ H3); intros i Hi; rewrite Mem.length_le4 in Hi;
          replace (q + 16 + i) with (q + (16 + i)) by lia; exact (proj1 (HQ (q + (16 + i)) ltac:(lia)))|].
  split.
  { destruct H4 as (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|]. intros i Hi.
    exact (proj2 (HQ (q + i) ltac:(lia)) (W3 i Hi)). }
  split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
  split; [apply (PvStr.bytes_keep m m' text _ H10); intros i Hi; apply HT; lia|].
  split; [exact H11 | exact H12].
Qed.

Lemma fd_str : forall m lblk dd v ty num s k cap, pj_hdr rsegs m v ty num s 0 0 0 cap -> lblk s k ->
  pj_apart [(s, k)] v -> pj_fd rsegs m lblk dd v [(s, k)].
Proof.
  intros m lblk dd v ty num s k cap H Hl Ha.
  destruct dd as [|dd]; cbn [pj_fd]; unfold pj_fshape;
    (split; [constructor; [intros Hn; inversion Hn | constructor]|]); (split; [exact Ha|]);
    exists ty, num, s, 0, 0, 0, cap, false, [(s, k)], [], [], [];
    (split; [exact H|]); (split; [right; exists k; split; [exact Hl | reflexivity]|]);
    (split; [left; split; [reflexivity | split; reflexivity]|]);
    (split; [left; split; [reflexivity | split; reflexivity]|]); (split; [apply Permutation_refl|]).
  - split; reflexivity.
  - reflexivity.
Qed.

Section N.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Local Abbreviation segs := (ms_segs B).
Local Abbreviation MR := (aa_MR API).

Theorem pv_num_ok : forall d, AllocExtra B (aa_MR API) -> ctx_owned B API -> errno_unowned B API ->
  fuzz_malloc_contract B API RF -> memcpy_contract -> strtod_c.strtod_contract -> pv_num_stmt B API RF d.
Proof.
  intros d AX CO ERR FM MC SC L A regs mem md Lam peak cnt fail b q text len p tb v PRE0 P m' regs' b0 y txt r
    HP HR PJ WM HO OB NT MU ST FR PZ R1 R2 R8 R9 R10 R18 R19 R20 RK.
  pose proof PRE0 as (ENV & LED & RES & Q10 & V11 & PJ0 & Hq & QA & MX & TX & V0 & VZ & VP & D1 & D2 & CN & RR).
  pose proof ENV as (SEG & TP & EA & GG & GD & PRE & H47 & GT & FRM & RC).
  pose proof (pj_in_ok_bounds segs _ _ _ _ _ _ _ PJ0) as (Bq0 & Bq1 & Bt0 & Bp & Bt1 & Bqt & BL & Bq8 & Bd).
  assert (Hd : (d <= MAXD)%nat) by (unfold MAXD; lia).
  pose proof PRE as (HM & HWF & HB & HRA & Hal16 & Hlo & Hhi & HWs & Htp & Her & Haux).
  pose proof (pvk_bounds d Hd) as (K1 & K2 & K3).
  pose proof ceil_big as Cb. pose proof LED as (_ & _ & CNT0 & _).
  pose proof pv_consts as (CPS & CMA & CLI & CST & CAS).
  assert (Hsp' : spZ regs' = spZ regs - 64) by (unfold spZ at 1; rewrite R2; apply MState.unsigned_lit; lia).
  pose proof D1 as D1'. cbn [Frame.disjoint_from] in D1'. pose proof D2 as D2'. cbn [Frame.disjoint_from] in D2'.
  destruct VP as (VPl & VPa & VPo).
  assert (Hvn : forall i, 0 <= i < 56 -> ~ owned B L A (v + i) /\ ~ alloc_statics (v + i) /\ ~ in_img B (v + i)).
  { intros i Hi. destruct (VPo i Hi) as (H1 & H2 & _ & H4). split; [exact H1|]. split; [exact H2 | exact H4]. }
  pose proof (v_heads B API L A mem md Lam peak cnt fail (spZ regs) v HM LED ltac:(lia) VPl) as Hheads.
  pose proof (PvStr.vloc B L A mem Lam peak cnt fail (spZ regs) v LED VPl) as VL.
  assert (Hvb : v + 56 <= alloc_ceiling \/ spZ regs <= v).
  { destruct VL as [H|(ra & rk & Hb & H1 & H2)]; [right; exact H|left].
    destruct (PvStr.blk_facts B API L A mem md ra rk 0 HM Hb ltac:(lia)) as (_ & _ & _ & H3). lia. }
  assert (ERRL : forall x, errno_addr B <= x < errno_addr B + 4 -> 0x33b84 <= x < 0x33b88)
    by (intros x Hx; rewrite EA in Hx; unfold strtod_c.STRTOD_ERRNO in Hx; lia).
  pose proof PZ as ((Hv8 & Hvs) & Hvz).
  pose proof Hvs as (Hv0 & Hv56 & _).
  destruct (num_tok_some (b0 :: y) txt r NT) as (Etr & NC & L1 & _).
  assert (RAT : rest_at tb text P = txt ++ r) by (rewrite HO; exact Etr).
  pose proof (PvItems.ra_len_le tb text p P HR) as LL. rewrite RAT, length_app in LL.
  pose proof (rest_at_len tb text len P BL HP) as RL. rewrite RAT, length_app in RL.
  assert (JV : forall ok, jr_value jr_strtod d (rest_at tb text p) ok = jr_number jr_strtod (b0 :: y) ok).
  { intros ok. rewrite jr_value_unfold, <- HR, HO. destruct OB as (O1 & O2 & O3 & O4 & O5 & O6).
    rewrite (proj2 (Z.eqb_neq b0 123) O1), (proj2 (Z.eqb_neq b0 91) O2), (proj2 (Z.eqb_neq b0 34) O3),
      (proj2 (Z.eqb_neq b0 116) O4), (proj2 (Z.eqb_neq b0 102) O5), (proj2 (Z.eqb_neq b0 110) O6). reflexivity. }
  assert (ROOM : rf_room RF b (Z.of_nat (S (length txt)) + 16) /\ Z.of_nat (S (length txt)) + 16 <= 2 ^ 28).
  { pose proof RR as RR'. rewrite (JV []), jr_number_tok, NT in RR'. cbn [take] in RR'.
    destruct (whole jr_strtod txt); cbn [snd fst room_run is_call esize] in RR'; destruct RR' as (Hc & _);
      exact (Hc eq_refl). }
  set (n := Z.of_nat (length txt) + 1). assert (En : n = Z.of_nat (length txt) + 1) by reflexivity.
  set (W1 := [(spZ regs - 64, spZ regs); (q, q + 8)]).
  assert (HW1 : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W1 x ->
                  spZ regs - 64 <= x < spZ regs \/ (q <= x /\ q <= x < q + 8)).
  { intros x Hx Ho. destruct (outside2 _ _ _ _ _ Ho) as [H|H]; [left; exact H | right; split; [lia | exact H]]. }
  assert (HW1' : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W1 x -> spZ regs - 64 <= x)
    by (intros x Hx Ho; destruct (outside2 _ _ _ _ _ Ho) as [H|H]; lia).
  assert (MID1 : pv_mid B API (PARSE_VALUE_K d) (spZ regs) L A mem md (fun x => q <= x < q + 8) L A m' md)
    by (apply (pv_mid_A0 B API d L A regs mem md q m' _ W1 SEG PRE Hd Hq MU); [rewrite SEG; exact WM | exact HW1]).
  pose proof (pv_ledger_A0 B API d L A regs mem md Lam peak cnt fail q m' W1 PRE Hd LED Hq MU HW1') as LED1.
  pose proof (pv_cells_A0 B d regs mem m' W1 SEG GG GD GT Hd RC MU HW1') as RC1.
  pose proof MID1 as (HM1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWS1).
  assert (Hown : forall x, 0 <= x < alloc_ceiling -> owned B L A x -> Frame.outside W1 x)
    by (intros x Hx Ho; unfold W1; cbn [Frame.outside]; split; [lia|]; split; [lia | exact I]).
  assert (AXm : st_init_done A = false -> auxv_pre B (ly_sec L) (q + 24) m').
  { intros Hf. apply (kb_auxv B API _ _ mem m' W1 L A md HM (QA Hf) MU); [|exact Hown].
    intros x Hx Hlx. unfold W1. cbn [Frame.outside]. split; [lia|]. split; [lia | exact I]. }
  assert (CP : call_pre_k B MR (ALLOC_STACK + 32) L A regs' m' md).
  { apply (pre_callee B API (PARSE_VALUE_K d) 64 (ALLOC_STACK + 32) L A regs mem md regs' m' (q + 24) PRE);
      [lia | rewrite CAS; lia | rewrite CAS; lia | exact Hsp' | rewrite Hsp'; lia | exact (RK 4 ltac:(lia)) |
       rewrite R1; exact ret_ok_15600 | exact HM1 | rewrite SEG; exact WM | exact AXm | lia]. }
  pose proof RC1 as (RO1 & _).
  eapply SR_bind.
  { apply (FM L A regs' m' md n b Lam peak cnt fail CP R10 ltac:(lia) LED1 RO1 RES);
      [replace (n + 16) with (Z.of_nat (S (length txt)) + 16) by lia; exact (proj1 ROOM) | lia]. }
  intros c1 (L' & A' & regs2 & mem2 & md2 & res & -> & ROA2 & GK & HI2 & HAV2 & CPK & HLn2 & G10 & KP & UK & ARM).
  rewrite R1.
  pose proof CPK as (HM2 & HWF2 & HB2 & HL2 & HPA2 & HRP2 & HMD2 & HHI2 & HU2 & HSW2).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM2) as (Hh2 & Hl2 & _).
  assert (UKA : forall pp k, In (pp, k) (user_blocks A) -> In (pp, k) (user_blocks A')).
  { intros pp k Hpp. apply UK; [exact Hpp|]. intros Eq. injection Eq as E1 _.
    pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ pp k HM1 Hpp). lia. }
  assert (NEWB : res <> 0 -> In (res - 16, n + 16) (blocks L' A') /\ ~ In (res - 16, n + 16) (blocks L A) /\
    (forall ra rk, In (ra, rk) (blocks L A) -> 0 < rk -> ra + rk <= res - 16 \/ res + n <= ra) /\
    4096 <= res - 16 /\ res + n <= alloc_ceiling /\
    (forall i, 0 <= i < n + 16 -> ~ in_img B (res - 16 + i) /\ ~ alloc_statics (res - 16 + i))).
  { intros Hr0. destruct ARM as [(_ & Er & _)|(Hcf & _ & _ & _ & HS & HIm & _ & (b1 & b2 & Eb1 & Eb2) & _)];
      [contradiction|].
    pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM2) as PW. rewrite Eb1 in PW.
    destruct (MallocRuns.pairwise_mid ranges_disjoint b1 (res - 16, n + 16) b2 PW) as (PD & _).
    assert (Hin : In (res - 16, n + 16) (blocks L' A')) by (rewrite Eb1; apply in_or_app; right; left; reflexivity).
    destruct (PvStr.blk_facts B API L' A' mem2 md2 _ _ 0 HM2 Hin ltac:(lia)) as (_ & _ & R1' & R2').
    split; [exact Hin|].
    split.
    { intros Hin'. rs_hide_all. rewrite Eb2 in Hin'. destruct (PD _ Hin') as [Hd0|Hd0]; unfold ranges_disjoint in Hd0; cbn in Hd0; lia. }
    split.
    { intros ra rk Hb Hrk. rewrite Eb2 in Hb. destruct (PD _ Hb) as [Hd0|Hd0]; unfold ranges_disjoint in Hd0; cbn in Hd0; lia. }
    split; [lia|]. split; [lia|].
    intros i Hi. split; [exact (HIm i Hi) | exact (HS i Hi)]. }
  assert (Hres : 0 <= res < 2 ^ 64).
  { destruct (Z.eq_dec res 0) as [->|Hr0]; [lia|]. destruct (NEWB Hr0) as (_ & _ & _ & H1 & H2 & _). lia. }
  assert (NSC : forall x, spZ regs - 48 <= x -> ~ scratch_k B (ALLOC_STACK + 32) regs' x).
  { intros x Hx Hs. unfold scratch_k in Hs. rewrite Hsp' in Hs. destruct Hs as [Hs|Hs]; [lia | pose proof (ERRL x Hs); lia]. }
  assert (HIGHK : forall x, spZ regs - 48 <= x < 2 ^ 64 ->
    mbyte segs mem2 x = mbyte segs m' x /\ (writable_at segs m' x <-> writable_at segs mem2 x)).
  { intros x Hx. apply HHI2; [left; lia | | | apply NSC; lia |].
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM1 Ho). lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM2 Ho). lia.
    - rs_hide_all. intros [Hw|(Hr0 & Hw)]; [unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hw; lia|].
      destruct (NEWB Hr0) as (_ & _ & _ & _ & H2 & _). lia. }
  assert (BLKK : forall ra rk x, In (ra, rk) (blocks L A) -> ra <= x < ra + rk ->
    mbyte segs mem2 x = mbyte segs m' x /\ (writable_at segs m' x <-> writable_at segs mem2 x)).
  { intros ra rk x Hb Hx. unfold blocks in Hb. apply in_map_iff in Hb as ([pp kk] & Eq & Hpp). cbn [fst snd] in Eq.
    injection Eq as Era Erk. subst kk.
    pose proof (UKA pp rk Hpp) as Hpp'.
    split.
    - pose proof (HU2 pp rk (x - ra) Hpp Hpp' ltac:(lia)) as Hk. rewrite Era in Hk.
      replace (ra + (x - ra)) with x in Hk by lia. exact Hk.
    - destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ pp rk (x - ra) HM1 Hpp ltac:(lia)) as (Pr1 & _).
      destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ pp rk (x - ra) HM2 Hpp' ltac:(lia)) as (Pr2 & _).
      rewrite (HPA2 pp rk Hpp Hpp'), Era in Pr2. rewrite Era in Pr1.
      replace (ra + (x - ra)) with x in Pr1, Pr2 by lia.
      split; intros _; apply (present_writable B); assumption. }
  assert (IMGK : forall x, in_img B x -> ~ owned B L A x -> ~ alloc_statics x -> ~ (errno_addr B <= x < errno_addr B + 4) ->
    mbyte segs mem2 x = mbyte segs m' x).
  { intros x Hi Ho Hs He. apply HHI2; [right; exact Hi | exact Ho | | |].
    - intros [Ha|Hso].
      + pose proof (ax_img AX L' A' mem2 md2 x HM2 Hi Ha) as Hc. exact (Ho (CO L A m' md x HM1 Hc)).
      + apply Ho. right. exact Hso.
    - intros [Hs'|Hs']; [rewrite Hsp' in Hs'; apply (img_iff B SEG) in Hi; lia | exact (He Hs')].
    - intros [Hw|(Hr0 & Hw)]; [exact (Hs Hw)|].
      destruct (NEWB Hr0) as (_ & _ & _ & _ & _ & HN). destruct (HN (x - (res - 16)) ltac:(lia)) as (HN1 & _).
      apply HN1. replace (res - 16 + (x - (res - 16))) with x by lia. exact Hi. }
  destruct TX as (TXl & TXo).
  assert (TEXTK : forall i, 0 <= i < len -> mbyte segs mem2 (text + i) = mbyte segs m' (text + i)).
  { intros i Hi. destruct (TXo i Hi) as (To & Ts & Te).
    destruct TXl as [Ht|[Ht|[(ra & rk & Hb & _ & H1 & H2)|(a0 & k0 & Hl & H1 & H2)]]].
    - exact (proj1 (HIGHK (text + i) ltac:(lia))).
    - exact (IMGK (text + i) (Ht i Hi) To Ts Te).
    - exact (proj1 (BLKK ra rk (text + i) Hb ltac:(lia))).
    - destruct (vb_lblock B _ _ _ _ _ _ _ _ _ LED Hl) as (Hk0 & Hraw).
      exact (proj1 (BLKK (a0 - 16) (k0 + 16) (text + i) Hraw ltac:(lia))). }
  assert (VK : forall x, v <= x < v + 56 ->
    mbyte segs mem2 x = mbyte segs m' x /\ (writable_at segs m' x <-> writable_at segs mem2 x)).
  { intros x Hx. destruct VL as [Hsv|(ra & rk & Hb & H1 & H2)]; [apply HIGHK; lia | apply (BLKK ra rk x Hb); lia]. }
  rewrite SEG in HIGHK, BLKK, IMGK, TEXTK, VK.
  assert (PJ2 : pj_in_ok rsegs mem2 q text len P (Z.of_nat d) tb).
  { apply (pj_in_ok_keep m' mem2 q text len P (Z.of_nat d) tb PJ); [|exact TEXTK].
    intros x Hx. destruct (HIGHK x ltac:(lia)) as (E1 & E2). split; [exact E1 | exact (proj1 E2)]. }
  assert (PZ2 : pj_zero rsegs mem2 v).
  { split; [split; [exact Hv8 | exact (PvStr.stk_keep m' mem2 v (v + 56) Hvs VK)]|].
    apply (PvStr.bytes_keep m' mem2 v _ Hvz). intros i Hi. rewrite repeat_length in Hi. exact (proj1 (VK (v + i) ltac:(lia))). }
  assert (FR2 : Step.rw_cells rsegs mem2 (spZ regs - 48)
    [Cells.C8 (getr regs 20); Cells.C8 (getr regs 19); Cells.C8 (getr regs 18); Cells.C8 (getr regs 9);
     Cells.C8 (getr regs 8); Cells.C8 (getr regs 1)]).
  { apply (ReaderKB.rk_rw_cells_keep m' mem2 _ _ FR). intros i Hi. cbn [Cells.cells_size Cells.csize] in Hi.
    destruct (HIGHK (spZ regs - 48 + i) ltac:(lia)) as (E1 & E2). split; [exact E1 | exact (proj1 E2)]. }
  set (E2 := fun x => alloc_statics x \/ (res <> 0 /\ res - 16 <= x < res + n)).
  assert (MB : pv_mid B API (PARSE_VALUE_K d) (spZ regs) L A m' md E2 L' A' mem2 md2).
  { apply (mid_of_call B API (PARSE_VALUE_K d) (spZ regs) (ALLOC_STACK + 32) L A regs' m' md _ E2 L' A' regs2 mem2 md2 CPK HM1
      HI2 HAV2 HLn2 UKA); [rewrite Hsp', CAS; lia | lia | | | lia | lia | exact HWS1].
    - intros x [Hw|(Hr0 & Hw)]; [left; exact Hw | right; split; [exact Hr0 | lia]].
    - rs_hide_all. intros x Hx _ [Hw|(Hr0 & Hw)]; [unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hw; lia|].
      destruct (NEWB Hr0) as (_ & _ & _ & _ & H2 & _). lia. }
  pose proof MB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWSB).
  pose proof (mid_seq B API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MID1 MB) as M12.
  assert (RP2 : regs_preserved regs' regs2) by exact HRP2.
  assert (GR : forall k, k = 3 \/ k = 4 \/ k = 8 \/ k = 9 \/ k = 18 \/ k = 19 \/ k = 20 \/ 21 <= k <= 27 ->
                 getr regs2 (Z_to_bv 5 k) = getr regs' (Z_to_bv 5 k))
    by (intros k Hk; apply RP2; unfold callee_saved; lia).
  assert (G2 : getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs - 64))
    by (rewrite (RP2 2 ltac:(unfold callee_saved; lia)); exact R2).
  assert (SPU : bv_unsigned (getr regs2 2) = spZ regs - 64).
  { change (bv_unsigned (getr regs2 2)) with (bv_unsigned (getr regs2 (Z_to_bv 5 2))). rewrite G2.
    apply MState.unsigned_lit. lia. }
  pose proof (ax_statics AX L' A' mem2 md2 HM2) as (GW1 & (g & Hg & GW2) & _).
  assert (RC2 : rd_cells B mem2) by (split; [exact ROA2 | split; [exact GW1 | exists g; exact GW2]]).
  rewrite GG, GD in GW1. rewrite GD in GW2.
  assert (GGc : Step.rw_cells rsegs mem2 strtod_c.STRTOD_GOT_GUARD [Cells.C8 (Z_to_bv 64 strtod_c.STRTOD_GUARD)]).
  { split; [split; [cbn; tauto|] | split; [unfold strtod_c.STRTOD_GOT_GUARD; lia | split; [cbn; unfold strtod_c.STRTOD_GOT_GUARD; lia|]]].
    - cbn [Cells.cells_bytes Cells.cbytes]. rewrite app_nil_r. rewrite <- SEG.
      apply (word_mem_le8 (ms_segs B) mem2 _ _ GW1); unfold strtod_c.STRTOD_GUARD, strtod_c.STRTOD_GOT_GUARD; lia.
    - intros i Hi. cbn [Cells.cells_size Cells.csize] in Hi. exact (proj1 (PvNumH.guard_wr mem2 i Hi)). }
  assert (GDc : Step.rw_cells rsegs mem2 strtod_c.STRTOD_GUARD [Cells.C8 (Z_to_bv 64 g)]).
  { split; [split; [cbn; tauto|] | split; [unfold strtod_c.STRTOD_GUARD; lia | split; [cbn; unfold strtod_c.STRTOD_GUARD; lia|]]].
    - cbn [Cells.cells_bytes Cells.cbytes]. rewrite app_nil_r. rewrite <- SEG.
      apply (word_mem_le8 (ms_segs B) mem2 _ _ GW2); unfold strtod_c.STRTOD_GUARD; lia.
    - intros i Hi. cbn [Cells.cells_size Cells.csize] in Hi. exact (proj2 (PvNumH.guard_wr mem2 i Hi)). }
  destruct (PvNumH.errno_C4 mem2) as (ew & ERc).
  { intros i Hi. rewrite <- SEG. apply HSW2. right. rewrite EA. unfold strtod_c.STRTOD_ERRNO. lia. }
  assert (Hlen : 1 <= len) by lia.
  assert (IMGOUT : res <> 0 -> res + n <= 0x10000 \/ 0x55000 <= res - 16).
  { intros Hr0. destruct (NEWB Hr0) as (_ & _ & _ & R1' & R2' & HN).
    destruct (Z_le_gt_dec (res + n) 0x10000) as [H|H]; [left; exact H|right].
    destruct (Z_le_gt_dec 0x55000 (res - 16)) as [H'|H']; [exact H'|exfalso].
    destruct (HN (Z.max (res - 16) 0x10000 - (res - 16)) ltac:(lia)) as (HN1 & _). apply HN1.
    replace (res - 16 + (Z.max (res - 16) 0x10000 - (res - 16))) with (Z.max (res - 16) 0x10000) by lia.
    apply (img_iff B SEG). lia. }
  assert (TXI : forall x, 0x10000 <= x < 0x55000 -> in_img B x) by (intros x Hx; apply (img_iff B SEG); exact Hx).
  assert (TLOC : spZ regs <= text \/ (0x10000 <= text /\ text + len <= 0x55000) \/
                 exists ra rk, In (ra, rk) (blocks L A) /\ ra <= text /\ text + len <= ra + rk).
  { destruct TXl as [Ht|[Ht|[(ra & rk & Hb & _ & H1 & H2)|(a0 & k0 & Hl & H1 & H2)]]].
    - left. exact Ht.
    - right. left. pose proof (proj1 (img_iff B SEG _) (Ht 0 ltac:(lia))) as I0.
      pose proof (proj1 (img_iff B SEG _) (Ht (len - 1) ltac:(lia))) as I1. lia.
    - right. right. exists ra, rk. auto.
    - right. right. destruct (vb_lblock B _ _ _ _ _ _ _ _ _ LED Hl) as (Hk0 & Hraw).
      exists (a0 - 16), (k0 + 16). split; [exact Hraw | lia]. }
  assert (TXE : text + len <= 0x33b84 \/ 0x33b88 <= text).
  { destruct (Z_le_gt_dec (text + len) 0x33b84) as [H|H]; [left; exact H|].
    destruct (Z_le_gt_dec 0x33b88 text) as [H'|H']; [right; exact H'|exfalso].
    destruct (TXo (Z.max text 0x33b84 - text) ltac:(lia)) as (_ & _ & Te). apply Te.
    rewrite EA. unfold strtod_c.STRTOD_ERRNO. lia. }
  assert (VE : v + 56 <= 0x33b84 \/ 0x33b88 <= v).
  { destruct (Z_le_gt_dec (v + 56) 0x33b84) as [H|H]; [left; exact H|].
    destruct (Z_le_gt_dec 0x33b88 v) as [H'|H']; [right; exact H'|exfalso].
    destruct (VPo (Z.max v 0x33b84 - v) ltac:(lia)) as (_ & _ & Ve & _). apply Ve.
    rewrite EA. unfold strtod_c.STRTOD_ERRNO. lia. }
  eapply (pv_run B regs2 (Z_to_bv 64 0x146f4) mem2 md2 _ _ Hh2 Hl2).
  { rewrite SEG. unfold rmk.
    eapply (PvNum.pv_num_tail MC SC) with (q := q) (text := text) (len := len) (P := P) (d := Z.of_nat d)
      (tb := tb) (v := v) (res := res) (txt := txt) (r := r) (lo := spZ regs - PARSE_VALUE_K d)
      (canary := Z_to_bv 64 g) (ev := ew) (rao := getr regs 1) (s0o := getr regs 8) (s1o := getr regs 9)
      (s2o := getr regs 18) (s3o := getr regs 19) (s4o := getr regs 20).
    - transitivity (getr regs' (Z_to_bv 5 8)); [exact (GR 8 ltac:(lia)) | exact R8].
    - transitivity (getr regs' (Z_to_bv 5 9)); [exact (GR 9 ltac:(lia)) | exact R9].
    - exact G10.
    - transitivity (getr regs' (Z_to_bv 5 18)); [exact (GR 18 ltac:(lia)) | exact R18].
    - transitivity (getr regs' (Z_to_bv 5 19)); [exact (GR 19 ltac:(lia)) | exact R19].
    - transitivity (getr regs' (Z_to_bv 5 20)); [exact (GR 20 ltac:(lia)) | exact R20].
    - transitivity (getr regs' (Z_to_bv 5 4)); [exact (GR 4 ltac:(lia))|].
      transitivity (getr regs (Z_to_bv 5 4)); [exact (RK 4 ltac:(lia))|]. etransitivity; [exact Htp|]. rewrite TP. reflexivity.
    - exact PJ2.
    - exact RAT.
    - exact NC.
    - exact L1.
    - pose proof (proj2 ROOM). lia.
    - exact PZ2.
    - exact V0.
    - exact D1.
    - intros i Hi. rewrite <- SEG. apply (not_img_ro B SEG); [lia | exact (proj2 (proj2 (Hvn i Hi)))].
    - exact Hres.
    - intros Hr0. destruct (NEWB Hr0) as (Hin & _ & _ & R1' & R2' & _).
      assert (STK : Frame.stk rsegs mem2 res (res + Z.of_nat (S (length txt)))).
      { split; [lia|]. split; [lia|]. intros a Ha.
        destruct (PvStr.blk_facts B API L' A' mem2 md2 _ _ (a - (res - 16)) HM2 Hin ltac:(lia)) as (Pr & _).
        replace (res - 16 + (a - (res - 16))) with a in Pr by lia.
        pose proof (present_writable B mem2 a Pr) as Hw. rewrite SEG in Hw.
        split; [exact Hw|]. destruct Pr as (bb & Hbb). exists bb. unfold Mem.mrd, Mem.wa. rewrite Hbb. reflexivity. }
      destruct (Frame.stk_carve rsegs mem2 res (res + Z.of_nat (S (length txt))) (S (length txt)) STK ltac:(lia))
        as (_ & junk & Hj).
      replace (res + Z.of_nat (S (length txt)) - Z.of_nat (S (length txt))) with res in Hj by lia.
      exists junk. exact Hj.
    - intros Hr0. destruct (NEWB Hr0) as (_ & _ & _ & R1' & R2' & _). pose proof (IMGOUT Hr0) as IO.
      unfold strtod_c.STRTOD_IMG_LO, strtod_c.STRTOD_GLOBALS_TOP, strtod_c.STRTOD_K. rewrite SPU. lia.
    - intros Hr0. destruct (NEWB Hr0) as (_ & _ & HD & R1' & R2' & _). pose proof (IMGOUT Hr0) as IO.
      unfold strtod_c.STRTOD_ERRNO, strtod_c.STRTOD_GOT_GUARD, strtod_c.STRTOD_GUARD.
      cbn [Frame.disjoint_from].
      split.
      { destruct TLOC as [Ht|[Ht|(ra & rk & Hb & H1 & H2)]]; [lia | lia |].
        destruct (HD ra rk Hb ltac:(lia)); lia. }
      split; [lia|].
      split.
      { destruct VL as [Hsv|(ra & rk & Hb & H1 & H2)]; [lia|]. destruct (HD ra rk Hb ltac:(lia)); lia. }
      split; [lia|]. split; [lia|]. split; [lia | exact I].
    - pose proof (@YM05.alloc_ceiling_val rc) as CV.
      eapply ReaderKB.rk_stk_of_wr; [lia | rewrite SPU; lia |]. intros a Ha. rewrite SPU in Ha.
      rewrite <- SEG. apply HWSB. left. lia.
    - rewrite SPU. unfold strtod_c.STRTOD_K. lia.
    - rewrite SPU. unfold strtod_c.STRTOD_K, strtod_c.STRTOD_GLOBALS_TOP in *. lia.
    - rewrite SPU. lia.
    - rewrite SPU. lia.
    - rewrite SPU. replace (spZ regs - 64 + 16) with (spZ regs - 48) by lia. exact FR2.
    - rewrite SPU. unfold strtod_c.STRTOD_K. cbn [Frame.disjoint_from]. split; [lia|]. split; [lia|]. split; [lia | exact I].
    - unfold strtod_c.STRTOD_ERRNO. cbn [Frame.disjoint_from]. split; [lia|]. split; [lia|]. split; [lia | exact I].
    - exact GGc.
    - exact GDc.
    - exact ERc.
    - rewrite <- SEG. exact ROA2.
    - exact FRM. }
  { intros ms HQ. unfold PvDefs.pv_num_post in HQ.
    destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
      F'' & fc'' & m'' & -> & _).
    do 5 eexists. rewrite SEG. reflexivity. }
  intros R F' pc' fc' m3 regs3 HQ Hg3.
  destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
    F'' & fc'' & m'' & EQ & WM3 & RO3 & ARM3).
  destruct (MS_inj _ _ _ _ _ _ _ _ _ _ _ _ EQ) as (ER & EF & EP & EC & EM). subst F' pc' fc' m3. rewrite ER in Hg3.
  assert (Hcfg : MState.ret_pc (getr regs 1) = getr regs 1) by exact (ret_pc_of regs HRA).
  assert (RP3 : regs_preserved regs regs3).
  { intros k Hk. rewrite (Hg3 (Z_to_bv 5 k)). unfold callee_saved in Hk.
    assert (Hk' : k = 2 \/ k = 3 \/ k = 4 \/ k = 8 \/ k = 9 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/
      k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by lia.
    destruct Hk' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
      try reflexivity;
      try (transitivity (Z_to_bv 64 (bv_unsigned (getr regs2 2) + 64)); [reflexivity|]; rewrite SPU;
           replace (spZ regs - 64 + 64) with (spZ regs) by lia; unfold spZ; apply MState.Z_to_bv_bv_unsigned);
      lazymatch goal with |- getr _ (Z_to_bv 5 ?kk) = _ =>
        transitivity (getr regs2 (Z_to_bv 5 kk)); [reflexivity|]; rewrite (GR kk ltac:(lia)); exact (RK kk ltac:(lia)) end. }
  assert (VOUT : v + 56 <= 0x10000 \/ 0x55000 <= v).
  { destruct (Z_le_gt_dec (v + 56) 0x10000) as [H|H]; [left; exact H|].
    destruct (Z_le_gt_dec 0x55000 v) as [H'|H']; [right; exact H'|exfalso].
    destruct (Hvn (Z.max v 0x10000 - v) ltac:(lia)) as (_ & _ & Hi). apply Hi.
    apply (img_iff B SEG). lia. }
  assert (G10f : forall w, a0' = w -> getr regs3 10 = w)
    by (intros w Hw; rewrite <- Hw; exact (Hg3 (Z_to_bv 5 10))).
  destruct ARM3 as [(Hr0 & Ea0 & EF'' & Efc & MU3 & PZ3 & PJ3)|(Hrn & c & bits & SM & Hc & FO & FRM' & MU3 & _ & CB3 & ARM4)].
  - destruct ARM as [(Hcf & _ & EL & EA' & Emd & RFb & _ & _ & LEDf)|(_ & Hrn & _)]; [|contradiction].
    subst L' A'.
    set (W3 := [(v + 16, v + 24)]).
    assert (WM3' : Frame.wmono segs mem2 m'') by (rewrite SEG; exact WM3).
    assert (PA3 : pv_mid B API (PARSE_VALUE_K d) (spZ regs) L A mem2 md2 (fun x => v <= x < v + 56) L A m'' md2 /\
                  ledger B L A m'' Lam peak ((cnt + 1) mod 2 ^ 64) (2 ^ 64 - 1) /\ rd_cells B m'').
    { apply (pv_A B API (PARSE_VALUE_K d) (spZ regs) L A mem2 md2 Lam peak ((cnt + 1) mod 2 ^ 64) (2 ^ 64 - 1) m'' W3 _ v
        SEG HM2 HWF2 HB2 LEDf RC2); [lia | lia | | exact HWSB | exact MU3 | exact WM3' | | exact Hvn | exact Hheads |].
      - intros k Hk. rewrite GG, GD. split; apply (img_iff B SEG); unfold strtod_c.STRTOD_GOT_GUARD, strtod_c.STRTOD_GUARD; lia.
      - intros x Hx Ho. right. unfold W3 in Ho. cbn [Frame.outside] in Ho. split; lia.
      - intros i Hi Ho. apply (PvLit.pres_of_wr B m'' (v + i) SEG); [lia | exact (proj2 (proj2 (Hvn i Hi))) |].
        unfold writable_at. apply WM3. pose proof PZ2 as ((_ & (_ & _ & S2)) & _). exact (proj1 (S2 (v + i) ltac:(lia))). }
    destruct PA3 as (MIDC & LED3 & RC3).
    pose proof (mid_seq B API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M12 MIDC) as M123.
    apply SR_ret. unfold pv_post.
    exists (mkFP F'' fc''), L, A, regs3, m'', md2, Lam, peak, ((cnt + 1) mod 2 ^ 64), (2 ^ 64 - 1),
      [negb (cnt =? fail)], (@None (jv * list Z)), [EFail (S (length txt))], (@nil bool), (@nil (Z * Z)).
    split; [rewrite Hcfg; reflexivity|].
    split; [rewrite Efc; exact FRM|].
    split; [intros k Hk; rewrite EF''; reflexivity|].
    split.
    { eapply mid_rpost; [eapply mid_E; [exact M123|] | exact RP3].
      intros x [[Hx|[Hx|(Hr' & _)]]|Hx]; [right; left; left; exact Hx | right; right; right; exact Hx | contradiction |
        left; exact Hx]. }
    split; [exact RC3|]. split; [exact LED3|].
    split; [rewrite JV, jr_number_tok, NT; cbn [take]; rewrite Hcf, Z.eqb_refl; reflexivity|].
    split; [apply oks_one|]. split; [cbn [calls is_call]; rewrite Z.mod_small by lia; lia|].
    split; [rewrite Hcf; apply fail_after_one_hit|].
    split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|].
    split; [intros a0 k0 []|].
    split; [rewrite hpeak_fail; pose proof LED as (_ & (LP & _) & _); lia|]. split; [rewrite hpeak_fail; lia|].
    split; [unfold rf_run; cbn [fold_left rf_ev]; exact RFb|].
    split; [apply G10f; exact Ea0|].
    split; [apply (pv_after_ok B m'' q text len P d tb); rewrite SEG; exact PJ3|].
    apply (pv_fd_zero B m'' Lam d v). rewrite SEG. exact PZ3.
  - destruct ARM as [(_ & Er & _)|(Hcf & _ & _ & RFm & HS & HIm & _ & (b1 & b2 & Eb1 & Eb2) & LEDs)]; [contradiction|].
    destruct (NEWB Hrn) as (Hnew & Hnnew & HD & R1' & R2' & HN).
    pose proof (IMGOUT Hrn) as IO.
    assert (BKE : forall ra rk, In (ra, rk) (blocks L A) -> In (ra, rk) (blocks L' A'))
      by (intros ra rk Hb; rewrite Eb1; rewrite Eb2 in Hb; apply in_app_or in Hb as [Hb|Hb];
          apply in_or_app; [left; exact Hb | right; right; exact Hb]).
    assert (VNB : forall x, v <= x < v + 56 -> ~ (res - 16 <= x < res + n)).
    { intros x Hx Hr'. destruct VL as [Hsv|(ra & rk & Hb & H1 & H2)]; [lia|]. destruct (HD ra rk Hb ltac:(lia)); lia. }
    rewrite SPU, MState.unsigned_lit in MU3 by lia.
    unfold strtod_c.STRTOD_K, strtod_c.STRTOD_ERRNO in MU3.
    set (W3 := [(spZ regs - 64 + 64 - 64 - 8928, spZ regs - 64 + 64); (res, res + Z.of_nat (length txt) + 1);
                (v, v + 24); (q, q + 8); (0x33b84, 0x33b84 + 4)]) in MU3.
    assert (HX5 : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W3 x ->
      (spZ regs - 8992 <= x < spZ regs) \/ (res <= x < res + n) \/ (v <= x < v + 24) \/ (q <= x < q + 8) \/
      (0x33b84 <= x < 0x33b88)).
    { intros x Hx Ho. unfold W3 in Ho. cbn [Frame.outside] in Ho. rs_hide_all. lia. }
    assert (WM3' : Frame.wmono segs mem2 m'') by (rewrite SEG; exact WM3).
    set (E3 := fun x => v <= x < v + 56 \/ q <= x < q + 8 \/ res <= x < res + n).
    assert (MIDC : pv_mid B API (PARSE_VALUE_K d) (spZ regs) L' A' mem2 md2 E3 L' A' m'' md2).
    { apply (mid_A B API (pv_img_low B SEG) (PARSE_VALUE_K d) (spZ regs) L' A' mem2 md2 m'' W3 E3 HM2 HWF2 HB2 HWSB MU3 WM3').
      - intros x Hx Ho. destruct (HX5 x Hx Ho) as [H|[H|[H|[H|H]]]].
        + left. left. lia.
        + right. right. right. exact H.
        + right. left. lia.
        + right. right. left. exact H.
        + left. right. rewrite EA. unfold strtod_c.STRTOD_ERRNO. lia.
      - intros x Hx Ho Hwn. destruct (HX5 x Hx Ho) as [H|[H|[H|[H|H]]]].
        + pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM2 Hwn). lia.
        + destruct (PvStr.blk_facts B API L' A' mem2 md2 _ _ (x - (res - 16)) HM2 Hnew ltac:(lia)) as (_ & Hno & _).
          apply Hno. replace (res - 16 + (x - (res - 16))) with x by lia. exact Hwn.
        + destruct VL as [Hsv|(ra & rk & Hb & H1 & H2)].
          * pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM2 Hwn). lia.
          * destruct (PvStr.blk_facts B API L' A' mem2 md2 ra rk (x - ra) HM2 (BKE ra rk Hb) ltac:(lia)) as (_ & Hno & _).
            apply Hno. replace (ra + (x - ra)) with x by lia. exact Hwn.
        + pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM2 Hwn). lia.
        + apply (ERR L' A' mem2 md2 x HM2); [rewrite EA; unfold strtod_c.STRTOD_ERRNO; lia | exact Hwn].
      - intros pp n0 i Hpp Hi Ho.
        destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ pp n0 i HM2 Hpp Hi) as (Pr & H1 & H2 & _).
        pose proof (ax_blocks_img AX L' A' mem2 md2 pp n0 i HM2 Hpp Hi) as NI.
        assert (Hxr : 0 <= ptr_addr L' pp + i < 2 ^ 64) by lia.
        split.
        + destruct (HX5 _ Hxr Ho) as [H|[H|[H|[H|H]]]]; [exfalso; lia | right; right; exact H | left; lia | exfalso; lia |].
          exfalso. apply NI. apply (img_iff B SEG). lia.
        + apply (PvLit.pres_of_wr B m'' _ SEG); [lia | exact NI |].
          unfold writable_at. apply WM3. pose proof (present_writable B mem2 _ Pr) as Hw. rewrite SEG in Hw. exact Hw. }
    assert (LED3 : ledger B L' A' m'' ((res, n) :: Lam) (Z.max peak (lsum Lam + n)) ((cnt + 1) mod 2 ^ 64) fail).
    { apply (ledger_A B API L' A' mem2 md2 m'' W3 _ _ _ _ HM2 LEDs MU3).
      intros x Hx Ho. destruct (HX5 x Hx Ho) as [H|[H|[H|[H|H]]]].
      - split; [unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia|].
        intros a0 k0 Hin Hr'. pose proof (ledger_block_range B API L' A' mem2 md2 _ _ _ _ a0 k0 HM2 LEDs Hin).
        destruct (vb_lblock B _ _ _ _ _ _ _ _ _ LEDs Hin) as (Hk0 & _). lia.
      - split; [destruct (HN (x - (res - 16)) ltac:(lia)) as (_ & Hs); replace (res - 16 + (x - (res - 16))) with x in Hs by lia; exact Hs|].
        intros a0 k0 [Eq|Hin] Hr'; [injection Eq as <- <-; lia|].
        destruct (vb_lblock B _ _ _ _ _ _ _ _ _ LED Hin) as (Hk0 & Hraw).
        destruct (HD _ _ Hraw ltac:(lia)); lia.
      - split; [destruct (Hvn (x - v) ltac:(lia)) as (_ & Hs & _); replace (v + (x - v)) with x in Hs by lia; exact Hs|].
        intros a0 k0 [Eq|Hin] Hr'; [injection Eq as <- <-; exact (VNB x ltac:(lia) ltac:(lia)) | exact (Hheads a0 k0 x Hin ltac:(lia) ltac:(lia))].
      - split; [unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia|].
        intros a0 k0 Hin Hr'. pose proof (ledger_block_range B API L' A' mem2 md2 _ _ _ _ a0 k0 HM2 LEDs Hin).
        destruct (vb_lblock B _ _ _ _ _ _ _ _ _ LEDs Hin) as (Hk0 & _). lia.
      - split; [unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia|].
        intros a0 k0 Hin Hr'. destruct (vb_lblock B _ _ _ _ _ _ _ _ _ LEDs Hin) as (Hk0 & _).
        apply (ledger_block_not_img B L' A' mem2 _ _ _ _ a0 k0 (x - a0) LEDs Hin ltac:(lia)).
        replace (a0 + (x - a0)) with x by lia. apply (img_iff B SEG). lia. }
    assert (RC3 : rd_cells B m'').
    { apply (rd_cells_A B mem2 m'' W3 RC2 MU3); rewrite ?GG, ?GD; unfold strtod_c.STRTOD_GOT_GUARD, strtod_c.STRTOD_GUARD;
        try (rs_hide_all; lia).
      - intros x Hro. pose proof (ro_low B SEG x Hro) as Hx. pose proof (bv_unsigned_in_range 64 x) as BR.
        unfold bv_modulus in BR. cbn in BR. unfold W3. cbn [Frame.outside]. repeat split; lia.
      - intros k Hk. unfold W3. cbn [Frame.outside]. repeat split; lia. }
    pose proof (mid_seq B API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M12 MIDC) as M123.
    assert (SUB : forall x, ((q <= x < q + 8) \/ E2 x) \/ E3 x -> rd_writes q v [(res, n)] x).
    { intros x [[Hx|[Hx|(_ & Hx)]]|[Hx|[Hx|Hx]]].
      - right. left. left. exact Hx.
      - right. right. right. exact Hx.
      - right. right. left. exists res, n. split; [left; reflexivity | lia].
      - left. exact Hx.
      - right. left. left. exact Hx.
      - right. right. left. exists res, n. split; [left; reflexivity | lia]. }
    assert (FRG : fregs_kept fx (mkFP F'' fc'')).
    { intros k Hk.
      assert (Hk' : k = 8 \/ k = 9 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/
        k = 26 \/ k = 27) by lia.
      destruct Hk' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]];
        apply FO; vm_compute; discriminate. }
    assert (APV : pj_apart [(res, n)] v).
    { intros bb x [<-|[]] Hx Hv. unfold pj_holds in Hx. cbn [fst snd] in Hx. exact (VNB x Hv ltac:(lia)). }
    destruct (jr_strtod_some txt bits c SM) as (JS & JW).
    apply SR_ret. unfold pv_post.
    destruct ARM4 as [(Hcl & Hfin & Ea0 & HDR & PJ3)|(Hbad & Ea0 & HDR & PJ3)].
    + exists (mkFP F'' fc''), L', A', regs3, m'', md2, ((res, n) :: Lam), (Z.max peak (lsum Lam + n)),
        ((cnt + 1) mod 2 ^ 64), fail, [negb (cnt =? fail)], (Some (JNum txt bits, r)), [EAlloc (S (length txt))],
        (@nil bool), [(res, n)].
      split; [rewrite Hcfg; reflexivity|]. split; [exact FRM'|]. split; [exact FRG|].
      split; [eapply mid_rpost; [eapply mid_E; [exact M123 | exact SUB] | exact RP3]|].
      split; [exact RC3|]. split; [exact LED3|].
      split; [rewrite JV, jr_number_tok, NT; cbn [take]; rewrite (proj2 (Z.eqb_neq cnt fail) Hcf); cbn [negb];
              rewrite JW, Hcl, Z.eqb_refl, Hfin; cbn [andb]; rewrite JS; reflexivity|].
      split; [apply oks_one|]. split; [cbn [calls is_call]; rewrite Z.mod_small by lia; lia|].
      split; [apply fail_after_one_miss; exact Hcf|].
      split; [apply Permutation_refl|]. split; [apply lsz_one_alloc; lia|].
      split; [cbn [length nlive nlive_ev]; lia|].
      split; [intros a0 k0 [Eq|[]]; injection Eq as <- <-; exact Hnnew|].
      split; [rewrite hpeak_alloc; f_equal; lia|]. split; [rewrite hpeak_alloc; lia|].
      split; [unfold rf_run; cbn [fold_left rf_ev]; replace (Z.of_nat (S (length txt)) + 16) with (n + 16) by lia; exact RFm|].
      split; [apply G10f; exact Ea0|].
      split; [rewrite SEG; replace (text + len - Z.of_nat (length r)) with (P + Z.of_nat (length txt)) by lia; exact PJ3|].
      split; [|cbn [lsum]; lia].
      rewrite SEG. cbn [pj_node].
      split; [constructor; [intros Hn'; inversion Hn' | constructor]|].
      split; [exact APV|].
      exists bits, res, 0, 0, 0, 0. split; [exact HDR|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists n. split; [|reflexivity].
      split; [unfold lin; left; reflexivity|]. split; [lia | exact CB3].
    + exists (mkFP F'' fc''), L', A', regs3, m'', md2, ((res, n) :: Lam), (Z.max peak (lsum Lam + n)),
        ((cnt + 1) mod 2 ^ 64), fail, [negb (cnt =? fail)], (@None (jv * list Z)), [EAlloc (S (length txt))],
        (@nil bool), [(res, n)].
      split; [rewrite Hcfg; reflexivity|]. split; [exact FRM'|]. split; [exact FRG|].
      split; [eapply mid_rpost; [eapply mid_E; [exact M123 | exact SUB] | exact RP3]|].
      split; [exact RC3|]. split; [exact LED3|].
      assert (HW0 : whole jr_strtod txt = false).
      { rewrite JW. destruct Hbad as [Hb'|Hb']; [rewrite (proj2 (Z.eqb_neq c _) Hb'); reflexivity | rewrite Hb'; apply andb_false_r]. }
      split; [rewrite JV, jr_number_tok, NT; cbn [take]; rewrite (proj2 (Z.eqb_neq cnt fail) Hcf); cbn [negb];
              rewrite HW0; reflexivity|].
      split; [apply oks_one|]. split; [cbn [calls is_call]; rewrite Z.mod_small by lia; lia|].
      split; [apply fail_after_one_miss; exact Hcf|].
      split; [apply Permutation_refl|]. split; [apply lsz_one_alloc; lia|].
      split; [cbn [length nlive nlive_ev]; lia|].
      split; [intros a0 k0 [Eq|[]]; injection Eq as <- <-; exact Hnnew|].
      split; [rewrite hpeak_alloc; f_equal; lia|]. split; [rewrite hpeak_alloc; lia|].
      split; [unfold rf_run; cbn [fold_left rf_ev]; replace (Z.of_nat (S (length txt)) + 16) with (n + 16) by lia; exact RFm|].
      split; [apply G10f; exact Ea0|].
      split; [apply (pv_after_ok B m'' q text len P d tb); rewrite SEG; exact PJ3|].
      rewrite SEG. apply (fd_str m'' (lin ((res, n) :: Lam)) (MAXD - d) v 0 bits res n 0 HDR); [unfold lin; left; reflexivity | exact APV].
Qed.

End N.
