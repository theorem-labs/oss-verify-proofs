From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame Exec Cells Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct PjIn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import PvDefs PvModel PvGlue PvMain0 PvPaths PvV.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import parse_string_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require ReaderKB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require PvItems PvLit PvStrA strtod_c.
Import ListNotations.
Local Open Scope Z_scope.
Module Frame := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Frame.
Module MState := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.MState.
Module Mem := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.
Module Exec := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Exec.
Module Cells := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Cells.
Module Step := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Step.

Lemma zz_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Qed.

Lemma bytes_keep : forall m m' a bs, Mem.bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  Mem.bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H3) HA. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite <- (H3 i Hi). exact (HA (Z.of_nat i) ltac:(lia)).
Qed.

Lemma stk_keep : forall m m' lo hi, Frame.stk rsegs m lo hi ->
  (forall x, lo <= x < hi -> mbyte rsegs m' x = mbyte rsegs m x /\ (writable_at rsegs m x <-> writable_at rsegs m' x)) ->
  Frame.stk rsegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H3) HA. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H3 a Ha) as [Hw (b & Hb)]. destruct (HA a Ha) as [Hm Hwr]. split.
  - apply Hwr. exact Hw.
  - exists b. rewrite <- Hb. exact Hm.
Qed.

Lemma munch_keep : forall W m m' x, Frame.munch W m m' -> 0 <= x < 2 ^ 64 -> Frame.outside W x ->
  mbyte rsegs m' x = mbyte rsegs m x.
Proof.
  intros W m m' x H Hx Ho. unfold mbyte. rewrite (H (Z_to_bv 64 x)); [reflexivity|].
  rewrite MState.unsigned_lit by lia. exact Ho.
Qed.

Lemma hdr4 : forall m v st, pj_rw rsegs m v -> Mem.bytes_at rsegs m v (Mem.le4 (Z_to_bv 64 4)) ->
  Mem.bytes_at rsegs m (v + 4) (repeat (Z_to_bv 8 0) 12) -> 0 <= st < 2 ^ 64 ->
  Mem.bytes_at rsegs m (v + 16) (Mem.le8 (Z_to_bv 64 st)) ->
  Mem.bytes_at rsegs m (v + 24) (repeat (Z_to_bv 8 0) 32) -> pj_hdr rsegs m v 4 0 st 0 0 0 0.
Proof.
  intros m v st Hrw H4 Z12 Hst H16 Z32.
  assert (U : forall a N off, Mem.bytes_at rsegs m a (repeat (Z_to_bv 8 0) N) -> 0 <= off ->
                off + 8 <= Z.of_nat N -> pj_u64 rsegs m (a + off) 0).
  { intros a N off H Ho Hl. split; [lia|]. rewrite pj_le8_0. exact (zeros_sub m a N off 8 H Ho Hl). }
  split; [exact Hrw|]. split; [split; [lia | exact H4]|].
  split; [replace (v + 8) with (v + 4 + 4) by lia; apply (U _ 12%nat); [exact Z12 | lia | cbn; lia]|].
  split; [split; [exact Hst | exact H16]|].
  split; [replace (v + 24) with (v + 24 + 0) by lia; apply (U _ 32%nat); [exact Z32 | lia | cbn; lia]|].
  split; [replace (v + 32) with (v + 24 + 8) by lia; apply (U _ 32%nat); [exact Z32 | lia | cbn; lia]|].
  split; [replace (v + 40) with (v + 24 + 16) by lia; apply (U _ 32%nat); [exact Z32 | lia | cbn; lia]|].
  replace (v + 48) with (v + 24 + 24) by lia; apply (U _ 32%nat); [exact Z32 | lia | cbn; lia].
Qed.

Lemma fd_empty : forall m lblk dd v ty num cap, pj_hdr rsegs m v ty num 0 0 0 0 cap -> pj_fd rsegs m lblk dd v [].
Proof.
  intros m lblk dd v ty num cap H.
  destruct dd as [|dd]; cbn [pj_fd]; unfold pj_fshape;
    (split; [constructor|]); (split; [intros bb x Hb; destruct Hb|]);
    exists ty, num, 0, 0, 0, 0, cap, false, [], [], [], [];
    (split; [exact H|]); (split; [left; split; reflexivity|]);
    (split; [left; split; [reflexivity | split; reflexivity]|]);
    (split; [left; split; [reflexivity | split; reflexivity]|]); (split; [apply Permutation_refl|]).
  - split; reflexivity.
  - reflexivity.
Qed.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Local Abbreviation segs := (ms_segs B).
Local Abbreviation MR := (aa_MR API).

Lemma mid_of_rpost2 : forall K S Kc L A regs1 mem md (Ec E : Z -> Prop) L' A' regs2 mem' md',
  rpost B API Kc L A regs1 mem md Ec (fun _ _ => False) L' A' regs2 mem' md' ->
  S - K <= spZ regs1 - Kc -> spZ regs1 <= S ->
  (forall a, Ec a -> E a \/ (a < alloc_ceiling /\ ~ in_img B a /\
     forall p n, In (p, n) (user_blocks A) -> ~ (ptr_addr L p <= a < ptr_addr L p + n))) ->
  (forall a, S - K <= a < S -> ~ (spZ regs1 - Kc <= a < spZ regs1) -> ~ Ec a) ->
  alloc_ceiling <= S - K -> S <= 2 ^ 64 ->
  (forall a, (S - K <= a < S \/ errno_addr B <= a < errno_addr B + 4) -> writable_at segs mem a) ->
  pv_mid B API K S L A mem md E L' A' mem' md'.
Proof.
  intros K S Kc L A regs1 mem md Ec E L' A' regs2 mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) W1 W2 HE HN Hc Hs HS.
  unfold scratch_k in *.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [intros p n Hp; exact (H8 p n Hp (fun h => h))|].
  split; [exact H9|]. split; [exact H11|].
  split.
  { intros a Ha Hn He. apply H12; [exact Ha | |].
    - intros [Hx|Hx]; apply Hn; [left; lia | right; exact Hx].
    - intros h. destruct (HE a h) as [h'|(h' & _)]; [exact (He h') | lia]. }
  split.
  { intros a Hi Hno Hn He. apply H13; [exact Hi | exact Hno | |].
    - intros [Hx|Hx]; apply Hn; [left; lia | right; exact Hx].
    - intros h. destruct (HE a h) as [h'|(_ & h' & _)]; [exact (He h') | exact (h' Hi)]. }
  split.
  { intros p n i Hp Hp' Hi He. apply (H14 p n i); [exact Hp | exact Hp' | exact Hi |].
    intros h. destruct (HE _ h) as [h'|(_ & _ & h')]; [exact (He h') | exact (h' p n Hp ltac:(lia))]. }
  intros a Ha.
  assert (D : (spZ regs1 - Kc <= a < spZ regs1 \/ errno_addr B <= a < errno_addr B + 4) \/
              ~ (spZ regs1 - Kc <= a < spZ regs1 \/ errno_addr B <= a < errno_addr B + 4)) by lia.
  destruct D as [D|D]; [exact (H15 a D)|].
  destruct Ha as [Ha|Ha]; [|exfalso; apply D; right; exact Ha].
  apply (proj2 (H12 a ltac:(lia) D (HN a Ha ltac:(lia)))). exact (HS a (or_introl Ha)).
Qed.

Lemma blocks_keep : forall K L A regs mem md E L' A' regs' mem' md',
  rpost B API K L A regs mem md E (fun _ _ => False) L' A' regs' mem' md' ->
  forall ra rk, In (ra, rk) (blocks L A) -> In (ra, rk) (blocks L' A').
Proof.
  intros K L A regs mem md E L' A' regs' mem' md' (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & _) ra rk Hin.
  unfold blocks in Hin |- *. apply in_map_iff in Hin as ([p k'] & Eq & Hp). cbn [fst snd] in Eq.
  injection Eq as <- <-. pose proof (H8 p k' Hp (fun h => h)) as Hp'.
  apply in_map_iff. exists (p, k'). cbn [fst snd]. rewrite (H9 p k' Hp Hp'). split; [reflexivity | exact Hp'].
Qed.

Lemma blk_facts : forall L A mem md ra rk i, MR L A mem md -> In (ra, rk) (blocks L A) -> 0 <= i < rk ->
  present mem (ra + i) /\ ~ owned B L A (ra + i) /\ 4096 <= ra /\ ra + rk <= alloc_ceiling.
Proof.
  intros L A mem md ra rk i HM Hin Hi. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & Eq & Hp).
  cbn [fst snd] in Eq. injection Eq as <- <-.
  destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p k' i HM Hp Hi) as (H1 & H2 & H3 & H4). auto.
Qed.

Lemma vloc : forall L A mem Lam peak cnt fail S v, ledger B L A mem Lam peak cnt fail ->
  pj_place (lin Lam) (fun a k => In (a, k) (blocks L A)) S (2 ^ 64) v ->
  S <= v \/ exists ra rk, In (ra, rk) (blocks L A) /\ ra <= v /\ v + 56 <= ra + rk.
Proof.
  intros L A mem Lam peak cnt fail S v HL [(H1 & _)|[(ra & rk & Hb & _ & H1 & H2)|(a & k & Hl & H1 & H2)]].
  - left. exact H1.
  - right. exists ra, rk. split; [exact Hb | lia].
  - right. destruct (vb_lblock B _ _ _ _ _ _ _ _ _ HL Hl) as (Hk & Hraw). exists (a - 16), (k + 16).
    split; [exact Hraw | lia].
Qed.

Lemma fresh_succ : forall K L A regs mem md E L' A' regs' mem' md' Lam2 peak cnt fail a n x,
  rpost B API K L A regs mem md E (fun _ _ => False) L' A' regs' mem' md' ->
  ledger B L' A' mem' Lam2 peak cnt fail -> In (a, n) Lam2 -> new_blks L A [(a, n)] ->
  a - 16 <= x < a + n ->
  x < alloc_ceiling /\ ~ in_img B x /\ forall ra rk, In (ra, rk) (blocks L A) -> ~ (ra <= x < ra + rk).
Proof.
  intros K L A regs mem md E L' A' regs' mem' md' Lam2 peak cnt fail a n x RP HL Hin NB Hx.
  pose proof RP as (HM' & _).
  destruct (vb_lblock B _ _ _ _ _ _ _ _ _ HL Hin) as (Hn & Hraw).
  pose proof (ledger_block_range B API L' A' mem' md' Lam2 peak cnt fail a n HM' HL Hin) as (R1 & R2 & _).
  split; [lia|]. split.
  { pose proof (ledger_block_not_img B L' A' mem' Lam2 peak cnt fail a n (x - a) HL Hin ltac:(lia)) as H.
    replace (a + (x - a)) with x in H by lia. exact H. }
  intros ra rk Hb Hr.
  pose proof (blocks_keep K L A regs mem md E L' A' regs' mem' md' RP ra rk Hb) as Hb'.
  assert (Hne : (ra, rk) <> (a - 16, n + 16)).
  { intros Eq. rewrite Eq in Hb. exact (NB a n (or_introl eq_refl) Hb). }
  destruct (vb_disj B API _ _ _ _ _ _ _ _ HM' Hb' Hraw Hne ltac:(lia) ltac:(lia)); lia.
Qed.

Lemma ret_ok_15544 : YK0s.ret_ok (Z_to_bv 64 0x1459c).
Proof. vm_compute. reflexivity. Qed.

Local Ltac pkc PK RP2 RK regs2 n :=
  etransitivity; [exact (PK n ltac:(lia))|]; transitivity (getr regs2 (Z_to_bv 5 n)); [reflexivity|];
  rewrite (RP2 n ltac:(unfold callee_saved; lia)); exact (RK n ltac:(lia)).

Theorem pv_str_ok : forall d, parse_string_contract B API RF -> pv_str_stmt B API RF d.
Proof.
  intros d PS L A regs mem md Lam peak cnt fail b q text len p tb v PRE0 P m' regs' y
    HP HR PJ WM HO MU ST FR PRW B4 BZ R1 R2 R8 R9 R10 RK.
  pose proof PRE0 as (ENV & LED & RES & Q10 & V11 & PJ0 & Hq & QA & MX & TX & V0 & VZ & VP & D1 & D2 & CN & RR).
  pose proof ENV as (SEG & TP & EA & GG & GD & PRE & H47 & GT & FRM & RC).
  pose proof (pj_in_ok_bounds segs _ _ _ _ _ _ _ PJ0) as (Bq0 & Bq1 & Bt0 & Bp & Bt1 & Bqt & BL & Bq8 & Bd).
  assert (Hd : (d <= MAXD)%nat) by (unfold MAXD; lia).
  pose proof PRE as (HM & HWF & HB & HRA & Hal16 & Hlo & Hhi & HWs & Htp & Her & Haux).
  pose proof (pvk_bounds d Hd) as (K1 & K2 & K3).
  pose proof ceil_big as Cb.
  pose proof pv_consts as (CPS & CMA & CLI & CST & CAS).
  assert (Hsp' : spZ regs' = spZ regs - 64) by (unfold spZ at 1; rewrite R2; apply MState.unsigned_lit; lia).
  pose proof D1 as D1'. cbn [Frame.disjoint_from] in D1'. pose proof D2 as D2'. cbn [Frame.disjoint_from] in D2'.
  destruct VP as (VPl & VPa & VPo).
  assert (Hvn : forall i, 0 <= i < 56 -> ~ owned B L A (v + i) /\ ~ alloc_statics (v + i) /\ ~ in_img B (v + i)).
  { intros i Hi. destruct (VPo i Hi) as (H1 & H2 & _ & H4). split; [exact H1|]. split; [exact H2 | exact H4]. }
  pose proof (v_heads B API L A mem md Lam peak cnt fail (spZ regs) v HM LED ltac:(lia) VPl) as Hheads.
  pose proof (vloc L A mem Lam peak cnt fail (spZ regs) v LED VPl) as VL.
  assert (Hvb : v + 56 <= alloc_ceiling \/ spZ regs <= v).
  { destruct VL as [H|(ra & rk & Hb & H1 & H2)]; [right; exact H|left].
    destruct (blk_facts L A mem md ra rk 0 HM Hb ltac:(lia)) as (_ & _ & _ & H3). lia. }
  destruct PRW as (Hv8 & Hvs).
  pose proof Hvs as (Hv0 & Hv56 & _).
  assert (Hvw : forall i, 0 <= i < 56 -> writable_at rsegs m' (v + i))
    by (intros i Hi; exact (proj1 (proj2 (proj2 Hvs) (v + i) ltac:(lia)))).
  assert (ERRL : forall x, errno_addr B <= x < errno_addr B + 4 -> x < 0x55000)
    by (intros x Hx; rewrite EA in Hx; unfold strtod_c.STRTOD_ERRNO in Hx; lia).
  set (W1 := [(spZ regs - 64, spZ regs); (q, q + 8); (v, v + 4)]).
  assert (Hown : forall x, 0 <= x < alloc_ceiling -> owned B L A x -> Frame.outside W1 x).
  { intros x Hx Ho. unfold W1. cbn [Frame.outside]. split; [lia|]. split; [lia|]. split; [|exact I].
    assert (Hx' : x < v \/ v + 4 <= x).
    { destruct (Z_lt_le_dec x v); [left; lia|]. destruct (Z_lt_le_dec x (v + 4)); [|right; lia].
      exfalso. destruct (Hvn (x - v) ltac:(lia)) as (Hno & _). apply Hno. replace (v + (x - v)) with x by lia. exact Ho. }
    lia. }
  assert (PA1 : pv_mid B API (PARSE_VALUE_K d) (spZ regs) L A mem md (fun x => q <= x < q + 8 \/ v <= x < v + 56)
                  L A m' md /\ ledger B L A m' Lam peak cnt fail /\ rd_cells B m').
  { apply (pv_A B API (PARSE_VALUE_K d) (spZ regs) L A mem md Lam peak cnt fail m' W1 _ v SEG HM HWF HB LED RC);
      [lia | lia | | | exact MU | rewrite SEG; exact WM | | exact Hvn | exact Hheads |].
    - intros k Hk. rewrite GG, GD. split; apply (img_iff B SEG); unfold strtod_c.STRTOD_GOT_GUARD, strtod_c.STRTOD_GUARD; lia.
    - intros a [Ha|Ha]; [exact (HWs a Ha) | exact (Her a Ha)].
    - intros x Hx Ho. unfold W1 in Ho. destruct (outside3 _ _ _ _ _ _ _ Ho) as [H|[H|H]].
      + left. split; [lia | left; lia].
      + left. split; [lia | right; left; exact H].
      + right. split; [lia | right; lia].
    - intros i Hi _. apply (PvLit.pres_of_wr B m' (v + i) SEG); [lia | exact (proj2 (proj2 (Hvn i Hi))) | exact (Hvw i Hi)]. }
  destruct PA1 as (MID1 & LED1 & RC1).
  pose proof MID1 as (HM1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWS1).
  assert (AXm : st_init_done A = false -> auxv_pre B (ly_sec L) (q + 24) m').
  { intros Hf. destruct (Z_le_gt_dec (spZ regs) v) as [Hsv|Hsv].
    - apply (auxv_pre_mono B _ (Z.max (v + 56) (q + 24))); [lia|].
      apply (kb_auxv B API _ _ mem m' W1 L A md HM); [eapply auxv_join; [exact (VPa Hsv Hf) | exact (QA Hf)] | exact MU | | exact Hown].
      intros x Hx Hlx. unfold W1. cbn [Frame.outside]. split; [lia|]. split; [lia|]. split; [lia | exact I].
    - apply (kb_auxv B API _ _ mem m' W1 L A md HM (QA Hf) MU); [|exact Hown].
      intros x Hx Hlx. unfold W1. cbn [Frame.outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (CP : call_pre_k B MR PARSE_STRING_K L A regs' m' md).
  { apply (pre_callee B API (PARSE_VALUE_K d) 64 PARSE_STRING_K L A regs mem md regs' m' (q + 24) PRE);
      [lia | rewrite CPS; lia | rewrite CPS; lia | exact Hsp' | rewrite Hsp'; lia | exact (RK 4 ltac:(lia)) |
       rewrite R1; exact ret_ok_15544 | exact HM1 | rewrite SEG; exact WM | exact AXm | lia]. }
  assert (TX' : text_ok B L A Lam regs' text len).
  { destruct TX as ([H|H] & H2); split; [left; lia | exact H2 | right; exact H | exact H2]. }
  assert (Y1 : rest_at tb text (P + 1) = y) by exact (rest_at_cons tb text P 34 y ltac:(lia) HO).
  pose proof (PvItems.ra_len_le tb text p P HR) as LL.
  pose proof (rest_at_len tb text len P BL HP) as RL. rewrite HO in RL. cbn [length] in RL.
  assert (JV : forall ok, jr_value jr_strtod d (rest_at tb text p) ok =
                 jbind (jr_string y) (fun '(s, r) => jret (JStr s, r)) ok).
  { intros ok. rewrite jr_value_unfold, <- HR, HO. reflexivity. }
  assert (ROOM : forall Q, scan (rest_at tb text (P + 1)) = Some Q ->
                   rf_room RF b (Z.of_nat Q + 17) /\ Z.of_nat Q + 17 <= 2 ^ 28).
  { intros Q HQ. rewrite Y1 in HQ. pose proof RR as RR'. rewrite (JV []), jr_string_unfold, HQ in RR'.
    cbn [take] in RR'.
    destruct (decode y) as [[s r]|]; cbn [snd fst room_run is_call esize] in RR'; destruct RR' as (Hc & _);
      specialize (Hc eq_refl); replace (Z.of_nat Q + 17) with (Z.of_nat (S Q) + 16) by lia; exact Hc. }
  eapply SR_bind.
  { apply (PS L A regs' m' md Lam peak cnt fail b q text len P (Z.of_nat d) tb).
    - split; [exact SEG|]. split; [exact TP|]. split; [exact EA|]. split; [exact GG|]. split; [exact GD|].
      split; [exact CP|]. split; [lia|]. split; [rewrite Hsp', CPS; lia|]. split; [exact FRM | exact RC1].
    - exact LED1.
    - exact RES.
    - exact R10.
    - rewrite SEG. exact PJ.
    - lia.
    - exact (PvItems.ra_nth tb text P 34 y HO).
    - lia.
    - exact AXm.
    - exact TX'.
    - rewrite Hsp', CPS. cbn [Frame.disjoint_from]. split; [lia|]. split; [lia | exact I].
    - lia.
    - exact ROOM. }
  intros c1 (L' & A' & regs2 & mem2 & md2 & Lam' & peak' & cnt' & fail' & b' & res & a & n & -> &
    RPS & RC2 & G10 & LED2 & RF2 & ARM).
  rewrite R1, Y1 in *.
  pose proof RPS as (HM2 & HWF2 & HB2 & HL2 & HI2 & HAV2 & HLn2 & HUB2 & HPA2 & HRP2 & HMD2 & HH2 & HG2 & HU2 & HSW2).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM2) as (Hh2 & Hl2 & _).
  assert (COM : (forall x, a <> 0 -> a - 16 <= x < a + n ->
                  x < alloc_ceiling /\ ~ in_img B x /\ forall ra rk, In (ra, rk) (blocks L A) -> ~ (ra <= x < ra + rk)) /\
                (forall bb, In bb Lam' -> In bb Lam \/ (bb = (a, n) /\ a <> 0)) /\
                (res = 0 \/ res = a /\ a <> 0) /\
                exists P2, (res = 0 -> P2 = P) /\ (res <> 0 -> P2 = P + n + 1) /\
                  text <= P2 <= text + len /\ pj_in_ok segs mem2 q text len P2 (Z.of_nat d) tb).
  { destruct (scan y) as [Q|] eqn:HQ.
    - destruct ARM as (En & Ec & [(Hcf & Er & Ea & EL & Ep & Ef & Eb & PJ2)|
        [(Hcf & Hdc & Er & Ha & EL & Ep & Ef & HFr & HLo & Eb & PJ2)|(Hcf & Er & Ha & s & r & Hdc & EL & NB & Ep & Ef & Eb & CB & PJ2)]]).
      + split; [intros x Hx; contradiction|]. split; [intros bb Hb; left; rewrite <- EL; exact Hb|].
        split; [left; exact Er|]. exists P. split; [intros _; reflexivity|].
        split; [intros H; exfalso; exact (H Er)|]. split; [lia | exact PJ2].
      + split; [intros x _ Hx; destruct (HFr x Hx) as (F1 & F2); split; [lia|]; split; [exact F1|];
                intros ra rk Hb; exact (F2 ra rk Hb)|].
        split; [intros bb Hb; left; rewrite <- EL; exact Hb|].
        split; [left; exact Er|]. exists P. split; [intros _; reflexivity|].
        split; [intros H; exfalso; exact (H Er)|]. split; [lia | exact PJ2].
      + split; [intros x _ Hx; apply (fresh_succ PARSE_STRING_K L A regs' m' md _ L' A' regs2 mem2 md2 Lam' peak' cnt' fail' a n x RPS LED2);
                  [rewrite EL; left; reflexivity | exact NB | exact Hx]|].
        split; [intros bb Hb; rewrite EL in Hb; destruct Hb as [<-|Hb]; [right; split; [reflexivity | exact Ha] | left; exact Hb]|].
        split; [right; split; [exact Er | exact Ha]|].
        destruct (G1_4 y s r Hdc) as (Q' & HQ' & Er' & Hls & _). rewrite HQ in HQ'. injection HQ' as <-.
        pose proof (scan_quote y Q HQ) as (HQl & _).
        assert (Hlr : length r = (length y - S Q)%nat) by (rewrite Er'; apply length_skipn).
        exists (P + n + 1). split; [intros H; exfalso; rewrite Er in H; exact (Ha H)|].
        split; [intros _; reflexivity|]. split; [lia | exact PJ2].
    - destruct ARM as (Er & Ea & En & EL' & EA' & EL & Ep & Ec & Ef & Eb & PJ2).
      split; [intros x Hx; contradiction|]. split; [intros bb Hb; left; rewrite <- EL; exact Hb|].
      split; [left; exact Er|]. exists P. split; [intros _; reflexivity|].
      split; [intros H; exfalso; exact (H Er)|]. split; [lia | exact PJ2]. }
  destruct COM as (FRESH & LAMS & RESV & P2 & EP0 & EP1 & HP2 & PJ2).
  assert (Hres : 0 <= res < 2 ^ 64).
  { destruct RESV as [->|(-> & Ha)]; [lia|].
    destruct (scan y) as [Q|] eqn:HQ; [|destruct ARM as (_ & Ea & _); contradiction].
    destruct ARM as (_ & _ & [(_ & _ & Ea & _)|[(_ & _ & Er & _)|(_ & _ & _ & s & r & _ & EL & _)]]);
      [contradiction | lia |].
    assert (Hin : In (a, n) Lam') by (rewrite EL; left; reflexivity).
    pose proof (ledger_block_range B API L' A' mem2 md2 Lam' peak' cnt' fail' a n HM2 LED2 Hin).
    pose proof (vb_lblock B _ _ _ _ _ _ _ _ _ LED2 Hin). lia. }
  assert (NE : forall x, (v <= x < v + 56 \/ spZ regs - 48 <= x < spZ regs) -> ~ parse_string_writes q a n x).
  { intros x Hx (Hn0 & [Hw|[Hw|(Ha & Hw)]]).
    - destruct Hx as [Hx|Hx]; lia.
    - destruct Hx as [Hx|Hx].
      + destruct (Hvn (x - v) ltac:(lia)) as (_ & Hs & _). apply Hs. replace (v + (x - v)) with x by lia. exact Hw.
      + unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hw. lia.
    - destruct (FRESH x Ha Hw) as (F1 & _ & F3). destruct Hx as [Hx|Hx]; [|lia].
      destruct VL as [Hsv|(ra & rk & Hb & H1 & H2)]; [lia | exact (F3 ra rk Hb ltac:(lia))]. }
  assert (NSC : forall x, spZ regs - 48 <= x -> ~ scratch_k B PARSE_STRING_K regs' x).
  { intros x Hx Hs. unfold scratch_k in Hs. rewrite Hsp' in Hs. destruct Hs as [Hs|Hs]; [lia | pose proof (ERRL x Hs); lia]. }
  assert (VK : forall x, v <= x < v + 56 ->
                 mbyte segs mem2 x = mbyte segs m' x /\ (writable_at segs m' x <-> writable_at segs mem2 x)).
  { intros x Hx. destruct VL as [Hsv|(ra & rk & Hb & H1 & H2)].
    - apply HH2; [lia | apply NSC; lia | apply NE; left; exact Hx].
    - unfold blocks in Hb. apply in_map_iff in Hb as ([pp kk] & Eq & Hpp). cbn [fst snd] in Eq.
      injection Eq as Era Erk. subst kk.
      pose proof (HUB2 pp rk Hpp (fun h => h)) as Hpp'.
      split.
      + pose proof (HU2 pp rk (x - ra) Hpp Hpp' ltac:(lia)) as Hk. rewrite Era in Hk.
        replace (ra + (x - ra)) with x in Hk by lia. apply Hk. apply NE. left. exact Hx.
      + destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ pp rk (x - ra) HM1 Hpp ltac:(lia)) as (Pr1 & _).
        destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ pp rk (x - ra) HM2 Hpp' ltac:(lia)) as (Pr2 & _).
        rewrite (HPA2 pp rk Hpp Hpp'), Era in Pr2. rewrite Era in Pr1.
        replace (ra + (x - ra)) with x in Pr1, Pr2 by lia.
        split; intros _; apply (present_writable B); assumption. }
  assert (FK : forall x, spZ regs - 48 <= x < spZ regs ->
                 mbyte segs mem2 x = mbyte segs m' x /\ (writable_at segs m' x <-> writable_at segs mem2 x)).
  { intros x Hx. apply HH2; [lia | apply NSC; lia | apply NE; right; exact Hx]. }
  rewrite SEG in VK, FK, PJ2.
  assert (VS2 : Frame.stk rsegs mem2 v (v + 56)) by exact (stk_keep m' mem2 v (v + 56) Hvs VK).
  assert (FR2 : Step.rw_cells rsegs mem2 (spZ regs - 48)
    [Cells.C8 (getr regs 20); Cells.C8 (getr regs 19); Cells.C8 (getr regs 18); Cells.C8 (getr regs 9);
     Cells.C8 (getr regs 8); Cells.C8 (getr regs 1)]).
  { apply (ReaderKB.rk_rw_cells_keep m' mem2 _ _ FR). intros i Hi. cbn [Cells.cells_size Cells.csize] in Hi.
    destruct (FK (spZ regs - 48 + i) ltac:(lia)) as (E1 & E2). split; [exact E1 | exact (proj1 E2)]. }
  assert (B4' : Mem.bytes_at rsegs mem2 v (Mem.le4 (Z_to_bv 64 4))).
  { apply (bytes_keep m' mem2 v _ B4). intros i Hi. rewrite Mem.length_le4 in Hi. exact (proj1 (VK (v + i) ltac:(lia))). }
  assert (Z12 : Mem.bytes_at rsegs mem2 (v + 4) (repeat (Z_to_bv 8 0) 12)).
  { replace (v + 4) with (v + 4 + 0) by lia.
    apply (bytes_keep m' mem2 (v + 4 + 0) _ (zeros_sub m' (v + 4) 52 0 12 BZ ltac:(lia) ltac:(cbn; lia))).
    intros i Hi. rewrite repeat_length in Hi. exact (proj1 (VK (v + 4 + 0 + i) ltac:(cbn in Hi; lia))). }
  assert (Z32 : Mem.bytes_at rsegs mem2 (v + 24) (repeat (Z_to_bv 8 0) 32)).
  { replace (v + 24) with (v + 4 + 20) by lia.
    apply (bytes_keep m' mem2 (v + 4 + 20) _ (zeros_sub m' (v + 4) 52 20 32 BZ ltac:(lia) ltac:(cbn; lia))).
    intros i Hi. rewrite repeat_length in Hi. exact (proj1 (VK (v + 4 + 20 + i) ltac:(cbn in Hi; lia))). }
  destruct (Frame.stk_split rsegs mem2 v (v + 24) (v + 56) VS2 ltac:(lia)) as (VS24 & _).
  destruct (Frame.stk_carve rsegs mem2 v (v + 24) 8 VS24 ltac:(lia)) as (_ & jk & VC).
  replace (v + 24 - Z.of_nat 8) with (v + 16) in VC by lia.
  assert (RP2 : regs_preserved regs' regs2) by exact HRP2.
  assert (G2 : getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs - 64))
    by (rewrite (RP2 2 ltac:(unfold callee_saved; lia)); exact R2).
  assert (G8 : getr regs2 (Z_to_bv 5 8) = Z_to_bv 64 v)
    by (rewrite (RP2 8 ltac:(unfold callee_saved; lia)); exact R8).
  apply (kb_run B regs2 (Z_to_bv 64 0x1459c) mem2 md2
    (fun R pc' mm => pc' = MState.ret_pc (getr regs 1) /\
       (forall r, callee_saved r -> getr R (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
       getr R (Z_to_bv 5 10) = Z_to_bv 64 (if res =? 0 then -1 else 0) /\
       Frame.munch [(v + 16, v + 24)] mem2 mm /\ Frame.wmono rsegs mem2 mm /\
       Step.rw_cells rsegs mm (v + 16) [Cells.C8 (Z_to_bv 64 res)]) _ Hh2 Hl2).
  { rewrite SEG. unfold rmk. eapply Exec.evt_mono.
    { eapply PvStrA.ka_ps_ret with (v := v) (res := res) (jv := jk).
      - lia.
      - lia.
      - exact G8.
      - exact G10.
      - exact Hres.
      - change (bv_unsigned (getr regs2 2)) with (bv_unsigned (getr regs2 (Z_to_bv 5 2))). rewrite G2.
        rewrite MState.unsigned_lit by lia. lia.
      - change (bv_unsigned (getr regs2 2)) with (bv_unsigned (getr regs2 (Z_to_bv 5 2))). rewrite G2.
        rewrite MState.unsigned_lit by lia. lia.
      - exact VC.
      - change (bv_unsigned (getr regs2 2)) with (bv_unsigned (getr regs2 (Z_to_bv 5 2))). rewrite G2.
        rewrite MState.unsigned_lit by lia. replace (spZ regs - 64 + 16) with (spZ regs - 48) by lia. exact FR2. }
    intros ms (R & mm & -> & E1 & E2 & E8 & E9 & E18 & E19 & E20 & E10 & PK & MU3 & WM3 & VC3).
    exists R, (MState.ret_pc (getr regs 1)), mm. split; [reflexivity|]. split; [reflexivity|].
    split.
    { intros r Hr. unfold callee_saved in Hr.
      assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
        r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
      - etransitivity; [exact E2|].
        change (bv_unsigned (getr regs2 2)) with (bv_unsigned (getr regs2 (Z_to_bv 5 2))). rewrite G2.
        rewrite MState.unsigned_lit by lia. replace (spZ regs - 64 + 64) with (spZ regs) by lia.
        unfold spZ. apply MState.Z_to_bv_bv_unsigned.
      - pkc PK RP2 RK regs2 3.
      - pkc PK RP2 RK regs2 4.
      - exact E8.
      - exact E9.
      - exact E18.
      - exact E19.
      - exact E20.
      - pkc PK RP2 RK regs2 21.
      - pkc PK RP2 RK regs2 22.
      - pkc PK RP2 RK regs2 23.
      - pkc PK RP2 RK regs2 24.
      - pkc PK RP2 RK regs2 25.
      - pkc PK RP2 RK regs2 26.
      - pkc PK RP2 RK regs2 27. }
    split; [exact E10|]. split; [exact MU3|]. split; [exact WM3 | exact VC3]. }
  intros R pc' mm regs3 (-> & HCS & G10' & MU3 & WM3 & VC3) Hg3.
  assert (RP3 : regs_preserved regs regs3) by (intros r Hr; rewrite Hg3; exact (HCS r Hr)).
  pose proof VC3 as ((_ & V16b) & _). cbn [Cells.cells_bytes Cells.cbytes] in V16b. rewrite app_nil_r in V16b.
  set (W3 := [(v + 16, v + 24)]).
  assert (OUT3 : forall x, ~ (v + 16 <= x < v + 24) -> Frame.outside W3 x)
    by (intros x Hx; unfold W3; cbn [Frame.outside]; split; [lia | exact I]).
  assert (KM : forall x, 0 <= x < 2 ^ 64 -> ~ (v + 16 <= x < v + 24) -> mbyte rsegs mm x = mbyte rsegs mem2 x)
    by (intros x Hx Hn; exact (munch_keep W3 mem2 mm x MU3 Hx (OUT3 x Hn))).
  assert (VSm : Frame.stk rsegs mm v (v + 56)).
  { apply (PvLit.stk_patch W3 mem2 mm v (v + 56) VS2 MU3 WM3). intros x Hx.
    destruct (Z_lt_le_dec x (v + 16)) as [H|H]; [left; apply OUT3; lia|].
    destruct (Z_lt_le_dec x (v + 24)) as [H'|H']; [right | left; apply OUT3; lia].
    pose proof V16b as (_ & _ & Hb). pose proof (Hb (Z.to_nat (x - (v + 16))) ltac:(rewrite Mem.length_le8; lia)) as Hn.
    replace (v + 16 + Z.of_nat (Z.to_nat (x - (v + 16)))) with x in Hn by lia. rewrite Hn.
    destruct (nth_error (Mem.le8 (Z_to_bv 64 res)) (Z.to_nat (x - (v + 16)))) as [bb|] eqn:Eb; [exists bb; reflexivity|].
    apply nth_error_None in Eb. rewrite Mem.length_le8 in Eb. lia. }
  assert (HDR : pj_hdr rsegs mm v 4 0 res 0 0 0 0).
  { apply hdr4; [split; [exact Hv8 | exact VSm] | | | exact Hres | exact V16b |].
    - apply (bytes_keep mem2 mm v _ B4'). intros i Hi. rewrite Mem.length_le4 in Hi. apply KM; lia.
    - apply (bytes_keep mem2 mm (v + 4) _ Z12). intros i Hi. rewrite repeat_length in Hi. cbn in Hi. apply KM; lia.
    - apply (bytes_keep mem2 mm (v + 24) _ Z32). intros i Hi. rewrite repeat_length in Hi. cbn in Hi. apply KM; lia. }
  assert (PJ3 : pj_in_ok rsegs mm q text len P2 (Z.of_nat d) tb).
  { apply (pj_in_ok_transport rsegs W3 mem2 mm q text len P2 (Z.of_nat d) tb PJ2 MU3 WM3);
      unfold W3; cbn [Frame.disjoint_from]; split; [lia | exact I | lia | exact I]. }
  assert (HH3 : forall a0 k x, In (a0, k) Lam' -> a0 - 16 <= x < a0 -> ~ (v <= x < v + 56)).
  { intros a0 k x Hin Hx. destruct (LAMS _ Hin) as [Hin0|(Eq & Ha)]; [exact (Hheads a0 k x Hin0 Hx)|].
    injection Eq as -> ->. destruct (vb_lblock B _ _ _ _ _ _ _ _ _ LED2 Hin) as (Hk & _).
    destruct (FRESH x Ha ltac:(lia)) as (F1 & _ & F3). intros Hv.
    destruct VL as [Hsv|(ra & rk & Hb & H1 & H2)]; [lia | exact (F3 ra rk Hb ltac:(lia))]. }
  assert (HVN3 : forall i, 0 <= i < 56 -> ~ owned B L' A' (v + i) /\ ~ alloc_statics (v + i) /\ ~ in_img B (v + i)).
  { intros i Hi. destruct (Hvn i Hi) as (_ & H2 & H3). split; [|split; [exact H2 | exact H3]].
    destruct VL as [Hsv|(ra & rk & Hb & H1 & H4)].
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM2 Ho). lia.
    - pose proof (blocks_keep _ _ _ _ _ _ _ _ _ _ _ _ RPS ra rk Hb) as Hb'.
      destruct (blk_facts L' A' mem2 md2 ra rk (v + i - ra) HM2 Hb' ltac:(lia)) as (_ & Hno & _).
      replace (ra + (v + i - ra)) with (v + i) in Hno by lia. exact Hno. }
  assert (WM3' : Frame.wmono segs mem2 mm) by (rewrite SEG; exact WM3).
  set (E2 := fun x => q <= x < q + 8 \/ alloc_statics x \/ (a <> 0 /\ a - 16 <= x < a + n /\ In (a, n) Lam')).
  assert (MB : pv_mid B API (PARSE_VALUE_K d) (spZ regs) L A m' md E2 L' A' mem2 md2).
  { apply (mid_of_rpost2 (PARSE_VALUE_K d) (spZ regs) PARSE_STRING_K L A regs' m' md _ E2 L' A' regs2 mem2 md2 RPS);
      [rewrite Hsp', CPS; lia | lia | | | lia | lia | exact HWS1].
    - intros x (Hn0 & [Hw|[Hw|(Ha & Hw)]]); [left; left; exact Hw | left; right; left; exact Hw |].
      destruct (in_dec zz_dec (a, n) Lam') as [Hin|Hnin]; [left; right; right; split; [exact Ha | split; assumption] | right].
      destruct (FRESH x Ha Hw) as (F1 & F2 & F3). split; [exact F1|]. split; [exact F2|].
      intros pp n0 Hpp Hx. apply (F3 (ptr_addr L pp) n0); [|exact Hx].
      unfold blocks. apply in_map_iff. exists (pp, n0). split; [reflexivity | exact Hpp].
    - intros x Hx _ (Hn0 & [Hw|[Hw|(Ha & Hw)]]).
      + lia.
      + unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hw. lia.
      + destruct (FRESH x Ha Hw) as (F1 & _). lia. }
  pose proof MB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWSB).
  assert (PA3 : pv_mid B API (PARSE_VALUE_K d) (spZ regs) L' A' mem2 md2 (fun x => v <= x < v + 56) L' A' mm md2 /\
                ledger B L' A' mm Lam' peak' cnt' fail' /\ rd_cells B mm).
  { apply (pv_A B API (PARSE_VALUE_K d) (spZ regs) L' A' mem2 md2 Lam' peak' cnt' fail' mm W3 _ v SEG HM2 HWF2 HB2 LED2 RC2);
      [lia | lia | | exact HWSB | exact MU3 | exact WM3' | | exact HVN3 | exact HH3 |].
    - intros k Hk. rewrite GG, GD. split; apply (img_iff B SEG); unfold strtod_c.STRTOD_GOT_GUARD, strtod_c.STRTOD_GUARD; lia.
    - intros x Hx Ho. right. unfold W3 in Ho. cbn [Frame.outside] in Ho. split; lia.
    - intros i Hi Ho. apply (PvLit.pres_of_wr B mm (v + i) SEG); [lia | exact (proj2 (proj2 (Hvn i Hi))) |].
      exact (proj1 (proj2 (proj2 VSm) (v + i) ltac:(lia))). }
  destruct PA3 as (MIDC & LED3 & RC3).
  pose proof (mid_seq B API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MID1 MB) as M12.
  pose proof (mid_seq B API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M12 MIDC) as M123.
  assert (Hcfg : MState.ret_pc (getr regs 1) = getr regs 1) by exact (ret_pc_of regs HRA).
  assert (G10r : getr regs3 10 = Z_to_bv 64 (if res =? 0 then -1 else 0))
    by (transitivity (getr R (Z_to_bv 5 10)); [exact (Hg3 (Z_to_bv 5 10)) | exact G10']).
  pose proof LED as (_ & (LP & _) & _).
  rewrite HO in LL. cbn [length] in LL.
  assert (SUBE : forall D, (forall x, a <> 0 -> a - 16 <= x < a + n -> In (a, n) Lam' -> blk_set D x) ->
    forall x, ((q <= x < q + 8 \/ v <= x < v + 56) \/ E2 x) \/ v <= x < v + 56 -> rd_writes q v D x).
  { intros D HD x [[[H|H]|[H|[H|(Ha & H & Hin)]]]|H].
    - right. left. left. exact H.
    - left. exact H.
    - right. left. left. exact H.
    - right. right. right. exact H.
    - right. right. left. exact (HD x Ha H Hin).
    - left. exact H. }
  apply SR_ret. unfold pv_post.
  destruct (scan y) as [Q|] eqn:HQ.
  - pose proof (scan_quote y Q HQ) as (HQl & _).
    destruct ARM as (En & Ec & [(Hcf & Er & Ea & EL & Ep & Ef & Eb & _)|
      [(Hcf & Hdc & Er & Ha & EL & Ep & Ef & HFr & HLo & Eb & _)|(Hcf & Er & Ha & s & r & Hdc & EL & NB & Ep & Ef & Eb & CB & _)]]).
    + exists fx, L', A', regs3, mm, md2, Lam', peak', cnt', fail', [negb (cnt =? fail)], (@None (jv * list Z)),
        [EFail (S Q)], (@nil bool), (@nil (Z * Z)).
      split; [rewrite Hcfg; reflexivity|]. split; [exact FRM|]. split; [intros r Hr; reflexivity|].
      split.
      { eapply mid_rpost; [eapply mid_E; [exact M123|] | exact RP3].
        apply SUBE. intros x Ha. contradiction. }
      split; [exact RC3|]. split; [exact LED3|].
      split; [rewrite JV, jr_string_unfold, HQ; cbn [take]; rewrite Hcf, Z.eqb_refl; reflexivity|].
      split; [apply oks_one|]. split; [rewrite Ec; cbn [calls is_call]; lia|].
      split; [rewrite Ef, Hcf; apply fail_after_one_hit|].
      split; [rewrite EL; apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|].
      split; [intros a0 k0 []|].
      split; [rewrite Ep, hpeak_fail; lia|]. split; [rewrite hpeak_fail; lia|].
      split; [unfold rf_run; cbn [fold_left rf_ev]; rewrite <- Eb; exact RF2|].
      rewrite Er in G10r, HDR, EP0. specialize (EP0 eq_refl). subst P2.
      split; [exact G10r|]. rewrite SEG.
      split; [apply (pv_after_ok B mm q text len P d tb); rewrite SEG; exact PJ3|].
      exact (fd_empty mm (lin Lam') (MAXD - d) v 4 0 0 HDR).
    + exists fx, L', A', regs3, mm, md2, Lam', peak', cnt', fail', [negb (cnt =? fail)], (@None (jv * list Z)),
        [EAlloc (S Q); EFree (S Q)], (@nil bool), (@nil (Z * Z)).
      split; [rewrite Hcfg; reflexivity|]. split; [exact FRM|]. split; [intros r Hr; reflexivity|].
      split.
      { eapply mid_rpost; [eapply mid_E; [exact M123|] | exact RP3].
        apply SUBE. intros x Hx Hr Hin. exfalso. rewrite EL in Hin.
        destruct (vb_lblock B _ _ _ _ _ _ _ _ _ LED Hin) as (Hk & Hraw).
        destruct (FRESH (a - 16) Ha ltac:(lia)) as (_ & _ & F3). exact (F3 _ _ Hraw ltac:(lia)). }
      split; [exact RC3|]. split; [exact LED3|].
      split; [rewrite JV, jr_string_unfold, HQ; cbn [take]; rewrite (proj2 (Z.eqb_neq cnt fail) Hcf); cbn [negb];
              rewrite Hdc; reflexivity|].
      split; [apply oks_one|]. split; [rewrite Ec; cbn [calls is_call]; lia|].
      split; [rewrite Ef; apply fail_after_one_miss; exact Hcf|].
      split; [rewrite EL; apply Permutation_refl|]. split; [rewrite lsz_alloc_free; apply Permutation_refl|].
      split; [cbn [length nlive nlive_ev]; lia|].
      split; [intros a0 k0 []|].
      split; [rewrite Ep, hpeak_alloc_free, En; f_equal; lia|]. split; [rewrite hpeak_alloc_free; lia|].
      split; [unfold rf_run; cbn [fold_left rf_ev]; replace (Z.of_nat (S Q) + 16) with (n + 16) by lia;
              rewrite <- Eb; exact RF2|].
      rewrite Er in G10r, HDR, EP0. specialize (EP0 eq_refl). subst P2.
      split; [exact G10r|]. rewrite SEG.
      split; [apply (pv_after_ok B mm q text len P d tb); rewrite SEG; exact PJ3|].
      exact (fd_empty mm (lin Lam') (MAXD - d) v 4 0 0 HDR).
    + destruct (G1_4 y s r Hdc) as (Q' & HQ' & Er' & Hls & _). rewrite HQ in HQ'. injection HQ' as <-.
      assert (Hlr : length r = (length y - S Q)%nat) by (rewrite Er'; apply length_skipn).
      exists fx, L', A', regs3, mm, md2, Lam', peak', cnt', fail', [negb (cnt =? fail)], (Some (JStr s, r)),
        [EAlloc (S Q)], (@nil bool), [(a, n)].
      split; [rewrite Hcfg; reflexivity|]. split; [exact FRM|]. split; [intros r0 Hr0; reflexivity|].
      split.
      { eapply mid_rpost; [eapply mid_E; [exact M123|] | exact RP3].
        apply SUBE. intros x _ Hx _. exists a, n. split; [left; reflexivity | lia]. }
      split; [exact RC3|]. split; [exact LED3|].
      split; [rewrite JV, jr_string_unfold, HQ; cbn [take]; rewrite (proj2 (Z.eqb_neq cnt fail) Hcf); cbn [negb];
              rewrite Hdc; reflexivity|].
      split; [apply oks_one|]. split; [rewrite Ec; cbn [calls is_call]; lia|].
      split; [rewrite Ef; apply fail_after_one_miss; exact Hcf|].
      split; [rewrite EL; apply Permutation_refl|]. split; [apply lsz_one_alloc; lia|].
      split; [cbn [length nlive nlive_ev]; lia|].
      split; [exact NB|].
      split; [rewrite Ep, hpeak_alloc, En; f_equal; lia|]. split; [rewrite hpeak_alloc; lia|].
      split; [unfold rf_run; cbn [fold_left rf_ev]; replace (Z.of_nat (S Q) + 16) with (n + 16) by lia;
              rewrite <- Eb; exact RF2|].
      assert (Hrn : res <> 0) by lia.
      rewrite (EP1 Hrn) in PJ3. rewrite Er in G10r, HDR. rewrite (proj2 (Z.eqb_neq a 0) Ha) in G10r.
      split; [exact G10r|].
      split; [rewrite SEG; replace (text + len - Z.of_nat (length r)) with (P + n + 1) by lia; exact PJ3|].
      split; [|cbn [lsum]; lia].
      rewrite SEG. cbn [pj_node].
      split; [constructor; [intros Hn; inversion Hn | constructor]|].
      split.
      { intros bb x [<-|[]] Hx Hv. unfold pj_holds in Hx. cbn [fst snd] in Hx.
        destruct (FRESH x Ha ltac:(lia)) as (F1 & _ & F3).
        destruct VL as [Hsv|(ra & rk & Hb & H1 & H2)]; [lia | exact (F3 ra rk Hb ltac:(lia))]. }
      exists 0, a, 0, 0, 0, 0. split; [exact HDR|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists n. split; [|reflexivity].
      split; [unfold lin; rewrite EL; left; reflexivity|].
      split; [lia|].
      destruct CB as (CF & CBb). split; [exact CF|].
      rewrite SEG in CBb. apply (bytes_keep mem2 mm a _ CBb). intros i Hi.
      rewrite length_map, length_app in Hi. cbn [length] in Hi.
      destruct (FRESH (a + i) Ha ltac:(lia)) as (F1 & _ & F3).
      apply KM; [lia|]. intros Hv.
      destruct VL as [Hsv|(ra & rk & Hb & H1 & H2)]; [lia | exact (F3 ra rk Hb ltac:(lia))].
  - destruct ARM as (Er & Ea & En & EL' & EA' & EL & Ep & Ec & Ef & Eb & _).
    exists fx, L', A', regs3, mm, md2, Lam', peak', cnt', fail', (@nil bool), (@None (jv * list Z)),
      (@nil ev), (@nil bool), (@nil (Z * Z)).
    split; [rewrite Hcfg; reflexivity|]. split; [exact FRM|]. split; [intros r Hr; reflexivity|].
    split.
    { eapply mid_rpost; [eapply mid_E; [exact M123|] | exact RP3].
      apply SUBE. intros x Ha. contradiction. }
    split; [exact RC3|]. split; [exact LED3|].
    split; [rewrite JV, jr_string_unfold, HQ; reflexivity|].
    split; [apply oks_zero|]. split; [rewrite Ec; cbn; lia|].
    split; [rewrite Ef; apply fail_after_zero|].
    split; [rewrite EL; apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|].
    split; [intros a0 k0 []|].
    split; [rewrite Ep, hpeak_nil; lia|]. split; [rewrite hpeak_nil; lia|].
    split; [unfold rf_run; cbn [fold_left]; rewrite <- Eb; exact RF2|].
    rewrite Er in G10r, HDR, EP0. specialize (EP0 eq_refl). subst P2.
    split; [exact G10r|]. rewrite SEG.
    split; [apply (pv_after_ok B mm q text len P d tb); rewrite SEG; exact PJ3|].
    exact (fd_empty mm (lin Lam') (MAXD - d) v 4 0 0 HDR).
Qed.

End S.
