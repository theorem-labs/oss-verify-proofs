From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame Exec Cells Step Image.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger PjStruct PjIn ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PvDefs PvModel PvGlue PvMain0 PvPaths PvV.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require ReaderKB PvNum PvDisp PvItems literal_c strtod_c.
Import ListNotations.
Local Open Scope Z_scope.
Module Frame := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Frame.
Module MState := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.MState.
Module Mem := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.
Module Exec := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Exec.

Lemma stk_norm : forall m lo hi, MemNorm.ro_agree rsegs m ->
  (forall a, lo <= a < hi -> Mem.ro_addr rsegs (Z_to_bv 64 a) = false) ->
  Frame.stk rsegs m lo hi -> Frame.stk rsegs (MemNorm.normalize rsegs m) lo hi.
Proof.
  intros m lo hi HRO Hn (H1 & H2 & H). pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as HR.
  split; [exact H1|]. split; [exact H2|]. intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split.
  - pose proof (MemNorm.wview_rel_rw rsegs m _ (Mem.wa a) HR (Hn a Ha)) as E. rewrite E. exact Hw.
  - exists b. pose proof (MemNorm.mrd_rel rsegs m _ (Mem.wa a) HR) as E. rewrite <- E. exact Hb.
Qed.

Lemma stk_patch : forall W m m' lo hi, Frame.stk rsegs m lo hi -> Frame.munch W m m' -> Frame.wmono rsegs m m' ->
  (forall a, lo <= a < hi -> Frame.outside W a \/ exists b, Mem.mrd rsegs m' (Mem.wa a) = Some b) ->
  Frame.stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM HO. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (HO a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold Mem.mrd in *. rewrite (MU (Mem.wa a)); [exact Hb|]. unfold Mem.wa. rewrite MState.unsigned_lit by lia. exact Ho.
Qed.

Lemma lit_node : forall m lblk v t ty, tag t = ty -> (t = JTrue \/ t = JFalse \/ t = JNull) -> 0 <= ty <= 2 ->
  pj_rw rsegs m v -> Mem.bytes_at rsegs m v (Mem.le4 (Z_to_bv 64 ty)) ->
  Mem.bytes_at rsegs m (v + 4) (repeat (Z_to_bv 8 0) 52) -> pj_node rsegs m lblk v t [].
Proof.
  intros m lblk v t ty Ht Hc Hty Hrw H4 Hz.
  assert (U : forall off, 8 <= off <= 48 -> pj_u64 rsegs m (v + off) 0).
  { intros off Ho. split; [lia|]. rewrite pj_le8_0. replace (v + off) with (v + 4 + (off - 4)) by lia.
    apply (zeros_sub m (v + 4) 52); [exact Hz | lia | cbn; lia]. }
  destruct Hc as [-> | [-> | ->]]; cbn [pj_node]; (split; [constructor|]); (split; [intros bb x Hb; destruct Hb|]);
    exists 0, 0, 0, 0, 0, 0; (split; [|repeat split]);
    (split; [exact Hrw|]); (split; [split; [rewrite Ht; lia | rewrite Ht; exact H4]|]);
    repeat (split; [apply U; lia|]); apply U; lia.
Qed.

Lemma pres_of_wr : forall B m x, ms_segs B = rsegs -> 0 <= x < 2 ^ 64 -> ~ in_img B x ->
  writable_at rsegs m x -> present m x.
Proof.
  intros B m x SEG Hx Hn Hw. unfold writable_at in Hw.
  assert (Hf : find_segment rsegs (bv_unsigned (Z_to_bv 64 x)) 1 = None).
  { rewrite MState.unsigned_lit by lia. rewrite <- SEG. exact (not_img_seg B SEG x Hn). }
  rewrite (ReaderKB.rk_wview_nofs m _ Hf) in Hw.
  destruct (m (Z_to_bv 64 x)) as [b|] eqn:E; [exists b; exact E | contradiction].
Qed.

Ltac nz_tac :=
  let H := fresh "H" in let c := fresh "c" in let Hc := fresh "Hc" in let Hin := fresh "Hin" in
  intros H; apply in_map_iff in H as (c & Hc & Hin); apply (f_equal bv_unsigned) in Hc;
  cbv [In w_true w_false w_null] in Hin;
  repeat (destruct Hin as [Hin|Hin]; [subst c; vm_compute in Hc; discriminate Hc|]); destruct Hin.

Ltac cs_tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hr' := fresh "Hr" in
  intros r Hr; unfold callee_saved in Hr;
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]; reflexivity.

Section Lit.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Local Abbreviation segs := (ms_segs B).
Local Abbreviation MR := (aa_MR API).

Lemma pv_lit_case : literal_c.literal_contract -> forall d L A regs mem md Lam peak cnt fail b q text len p tb v,
  pv_pre B API RF d L A regs mem md Lam peak cnt fail b q text len p tb v ->
  forall P m' regs' wa ty (w : list Z) (t : jv) (slack : list byte),
  text <= P <= text + len ->
  pj_in_ok rsegs m' q text len P (Z.of_nat d) tb -> Frame.wmono rsegs mem m' ->
  Frame.munch [(spZ regs - 64, spZ regs); (q, q + 8)] mem m' ->
  Frame.stk rsegs m' (spZ regs - PARSE_VALUE_K d) (spZ regs) ->
  pj_zero rsegs m' v ->
  getr regs' 1 = getr regs 1 -> regs_preserved regs regs' ->
  getr regs' 10 = Z_to_bv 64 q -> getr regs' 11 = Z_to_bv 64 wa -> getr regs' 12 = Z_to_bv 64 ty ->
  getr regs' 13 = Z_to_bv 64 v ->
  Forall (fun c => 0 < c < 256) w ->
  Mem.ro_bytes rsegs wa (map (Z_to_bv 8) w ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) w) ->
  (- (wa + Z.of_nat (length (map (Z_to_bv 8) w)) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0 <= wa -> wa + Z.of_nat (length (map (Z_to_bv 8) w)) + 1 + Z.of_nat (length slack) <= 2 ^ 64 ->
  0 <= ty <= 2 -> tag t = ty -> (t = JTrue \/ t = JFalse \/ t = JNull) ->
  (forall ok, jr_value jr_strtod d (rest_at tb text p) ok = lit w t (rest_at tb text P) ok) ->
  (length (rest_at tb text P) <= length (rest_at tb text p))%nat ->
  SR segs (mkCfg (mkst regs' (Z_to_bv 64 0x155e8) m' (seg_rom segs)) md)
    (pv_post B API RF d L A regs mem md Lam peak cnt fail b q text len p tb v).
Proof.
  intros LIT d L A regs mem md Lam peak cnt fail b q text len p tb v PRE0 P m' regs' wa ty w t slack
    HP PJ WM MU ST PZ R1 RP R10 R11 R12 R13 Hw Hro Hnz Hal Hwa Hwa2 Hty Htag Ht JV LL.
  pose proof PRE0 as (ENV & LED & RES & Q10 & V11 & PJ0 & Hq & QA & MX & TX & V0 & VZ & VP & D1 & D2 & CN & RR).
  pose proof ENV as (SEG & TP & EA & GG & GD & PRE & H47 & GT & FRM & RC).
  pose proof (pj_in_ok_bounds segs _ _ _ _ _ _ _ PJ0) as (Bq0 & Bq1 & Bt0 & Bp & Bt1 & Bqt & BL & Bq8 & Bd).
  assert (Hd : (d <= MAXD)%nat) by (unfold MAXD; lia).
  pose proof PRE as (HM & HWF & HB & HRA & Hal16 & Hlo & Hhi & HWs & Htp & Her & Haux).
  pose proof (pvk_bounds d Hd) as (K1 & K2 & K3).
  pose proof ceil_big as Cb.
  assert (Hsp : spZ regs' = spZ regs) by (unfold spZ; f_equal; exact (RP 2 ltac:(unfold callee_saved; lia))).
  pose proof D1 as D1'. cbn [Frame.disjoint_from] in D1'. pose proof D2 as D2'. cbn [Frame.disjoint_from] in D2'.
  destruct VP as (VPl & VPa & VPo).
  assert (Hvn : forall i, 0 <= i < 56 -> ~ owned B L A (v + i) /\ ~ alloc_statics (v + i) /\ ~ in_img B (v + i)).
  { intros i Hi. destruct (VPo i Hi) as (H1 & H2 & _ & H4). split; [exact H1|]. split; [exact H2 | exact H4]. }
  pose proof (v_heads B API L A mem md Lam peak cnt fail (spZ regs) v HM LED ltac:(lia) VPl) as Hheads.
  pose proof PZ as ((Hv8 & Hvs) & Hvz).
  pose proof (Hvs) as (Hv0 & Hv56 & _).
  assert (NRO : forall a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> Mem.ro_addr rsegs (Z_to_bv 64 a) = false).
  { intros a Ha Hn. rewrite <- SEG. exact (not_img_ro B SEG a Ha Hn). }
  assert (NIH : forall a, 0x55000 <= a -> ~ in_img B a) by (intros a Ha Hi; apply (img_iff B SEG) in Hi; lia).
  assert (ROS : MemNorm.ro_same rsegs mem m').
  { intros a Ha. apply MU. pose proof (ro_low B SEG a ltac:(rewrite SEG; exact Ha)) as Hx.
    cbn [Frame.outside]. split; [lia|]. split; [lia | exact I]. }
  destruct RC as (RO0 & RCg).
  assert (RO' : MemNorm.ro_agree rsegs m') by (rewrite SEG in RO0; exact (MemNorm.ro_agree_same rsegs mem m' RO0 ROS)).
  assert (MID0 : pv_mid B API (PARSE_VALUE_K d) (spZ regs) L A mem md (fun _ => True) L A m' md).
  { apply (pv_mid_A0 B API d L A regs mem md q m' (fun _ => True) _ SEG PRE Hd Hq MU); [rewrite SEG; exact WM|].
    intros x Hx Ho. destruct (outside2 _ _ _ _ _ Ho) as [H|H]; [left; exact H | right; split; [lia | exact I]]. }
  pose proof MID0 as (HM1 & _).
  pose proof VZ as ((_ & Hvs0) & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM1) as (Hh1 & Hl1 & _).
  set (W2 := [(spZ regs - 64, spZ regs); (q, q + 8); (v, v + 4)]).
  apply (kb_run B regs' (Z_to_bv 64 0x155e8) m' md
    (fun R pc' mm => pc' = MState.ret_pc (getr regs' 1) /\
       (forall r, callee_saved r -> getr R (Z_to_bv 5 r) = getr regs' (Z_to_bv 5 r)) /\
       Frame.munch W2 m' mm /\ Frame.wmono rsegs m' mm /\
       ((literal_c.lit_hit tb (P - text) (map (Z_to_bv 8) w) /\ getr R (Z_to_bv 5 10) = Z_to_bv 64 0 /\
         pj_in_ok rsegs mm q text len (P + Z.of_nat (length w)) (Z.of_nat d) tb /\
         Mem.bytes_at rsegs mm v (Mem.le4 (Z_to_bv 64 ty))) \/
        (~ literal_c.lit_hit tb (P - text) (map (Z_to_bv 8) w) /\ getr R (Z_to_bv 5 10) = Z_to_bv 64 (-1) /\
         Frame.munch [(spZ regs - 64, spZ regs)] m' mm /\ pj_in_ok rsegs mm q text len P (Z.of_nat d) tb)))
    _ Hh1 Hl1).
  { rewrite SEG. unfold rmk. unfold literal_c.literal_contract in LIT.
    eapply Exec.evt_mono.
    { apply (MemNorm.evt_normalize rsegs); [exact ReaderKB.rk_wx | exact RO' |].
      eapply LIT with (q := q) (text := text) (len := len) (p := P) (d := Z.of_nat d) (txt := tb) (w := wa)
        (cw := map (Z_to_bv 8) w) (slack := slack) (ty := ty) (v := v) (lo := spZ regs - PARSE_VALUE_K d).
      - exact R10.
      - exact R11.
      - exact R12.
      - exact R13.
      - apply pj_in_ok_norm; [exact RO' | | exact PJ]. intros i Hi. apply NRO; [lia | apply NIH; lia].
      - exact Hwa.
      - exact Hwa2.
      - exact Hro.
      - exact Hnz.
      - exact Hal.
      - exact Hty.
      - exact V0.
      - exact Hv8.
      - apply (MemNorm.wr_at_norm rsegs m' _ v 4 (MemNorm.mem_rel_normalize rsegs m' RO')).
        + split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (proj2 (proj2 Hvs) (v + i) ltac:(lia))).
        + intros i Hi. apply NRO; [lia|]. exact (proj2 (proj2 (Hvn i ltac:(lia)))).
      - cbn [Frame.disjoint_from]. split; [lia|]. split; [lia | exact I].
      - change (bv_unsigned (getr regs' 2)) with (spZ regs'). rewrite Hsp.
        apply stk_norm; [exact RO' | | exact ST]. intros a Ha. apply NRO; [lia | apply NIH; lia].
      - change (bv_unsigned (getr regs' 2)) with (spZ regs'). rewrite Hsp. lia.
      - change (bv_unsigned (getr regs' 2)) with (spZ regs'). rewrite Hsp. cbn [Frame.disjoint_from].
        split; [lia|]. split; [lia|]. split; [lia | exact I].
      - exact (MemNorm.mem_inv_normalize rsegs m'). }
    intros ms (s0 & HQ & Hrel & Hros).
    destruct HQ as (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
      -> & MU2 & WM2 & MI2 & ST2 & Hout).
    destruct (PvNum.pvn_ms_rel _ _ _ _ _ _ _ _ Hrel) as (mm & -> & HR2).
    change (MemNorm.ro_same rsegs m' mm) in Hros.
    pose proof (MemNorm.mem_rel_normalize rsegs m' RO') as HR1.
    change (bv_unsigned (getr regs' 2)) with (spZ regs') in MU2, Hout. rewrite Hsp in MU2, Hout.
    do 2 eexists. exists mm. split; [reflexivity|]. split; [reflexivity|]. split; [cs_tac|].
    split; [exact (MemNorm.munch_rel rsegs _ m' _ mm m0' HR1 HR2 Hros MU2)|].
    split; [exact (MemNorm.wmono_rel rsegs m' _ mm m0' HR1 HR2 Hros WM2)|].
    destruct Hout as [(Hit & -> & PJ2 & B2)|(Hmiss & -> & MU3 & PJ2)].
    - left. split; [exact Hit|]. split; [reflexivity|]. rewrite length_map in PJ2.
      split; [exact (pj_in_ok_back mm m0' _ _ _ _ _ _ HR2 PJ2)|].
      exact (proj2 (MemNorm.bytes_at_rel rsegs mm m0' _ _ HR2) B2).
    - right. split; [exact Hmiss|]. split; [reflexivity|].
      split; [exact (MemNorm.munch_rel rsegs _ m' _ mm m0' HR1 HR2 Hros MU3)|].
      exact (pj_in_ok_back mm m0' _ _ _ _ _ _ HR2 PJ2). }
  intros R pc' mm regs2 (-> & HCS & MU2 & WM2 & Hout) Hg.
  assert (RP2 : regs_preserved regs regs2).
  { intros r Hr. rewrite Hg, (HCS r Hr). exact (RP r Hr). }
  assert (MUa : Frame.munch W2 mem mm).
  { apply (Frame.munch_trans W2 mem m' mm); [|exact MU2].
    apply (Frame.munch_weaken [(spZ regs - 64, spZ regs); (q, q + 8)] W2 mem m'); [|exact MU].
    intros x (O1 & O2 & _). split; [exact O1 | split; [exact O2 | exact I]]. }
  assert (WMa : Frame.wmono segs mem mm) by (rewrite SEG; exact (Frame.wmono_trans rsegs mem m' mm WM WM2)).
  assert (Hvw : forall i, 0 <= i < 56 -> writable_at rsegs mm (v + i)).
  { intros i Hi. rewrite <- SEG. unfold writable_at. apply WMa. exact (proj1 (proj2 (proj2 Hvs0) (v + i) ltac:(lia))). }
  assert (Hvout : forall a, v + 4 <= a < v + 56 -> Frame.outside W2 a).
  { intros a Ha. unfold W2. cbn [Frame.outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (PA : pv_mid B API (PARSE_VALUE_K d) (spZ regs) L A mem md (rd_writes q v []) L A mm md /\
               ledger B L A mm Lam peak cnt fail /\ rd_cells B mm).
  { apply (pv_A B API (PARSE_VALUE_K d) (spZ regs) L A mem md Lam peak cnt fail mm W2 (rd_writes q v []) v
      SEG HM HWF HB LED (conj RO0 RCg)); [lia | lia | | | exact MUa | exact WMa | | exact Hvn | exact Hheads |].
    - intros k Hk. rewrite GG, GD. split; apply (img_iff B SEG); unfold strtod_c.STRTOD_GOT_GUARD, strtod_c.STRTOD_GUARD; lia.
    - intros a [Ha|Ha]; [exact (HWs a Ha) | exact (Her a Ha)].
    - intros x Hx Ho. unfold W2 in Ho. destruct (outside3 _ _ _ _ _ _ _ Ho) as [H|[H|H]].
      + left. split; [lia | left; lia].
      + left. split; [lia | right; right; left; left; exact H].
      + right. split; [lia | left; lia].
    - intros i Hi _. apply (pres_of_wr B mm (v + i) SEG); [lia | exact (proj2 (proj2 (Hvn i Hi))) | exact (Hvw i Hi)]. }
  destruct PA as (MID & LED2 & RC2).
  apply SR_ret. unfold pv_post.
  assert (Hcfg : MState.ret_pc (getr regs' 1) = getr regs 1) by (rewrite R1; exact (ret_pc_of regs HRA)).
  assert (Hw' : Forall (fun c => 0 <= c < 256) w).
  { pose proof Hw as Hw0. rewrite Forall_forall in Hw0 |- *. intros c Hc. specialize (Hw0 c Hc). cbv beta in *. lia. }
  pose proof (rest_at_len tb text len P BL HP) as RL.
  destruct Hout as [(Hit & G10 & PJ2 & B2)|(Hmiss & G10 & MU3 & PJ2)].
  - pose proof (proj1 (lit_hit_prefixb tb text len P w BL HP Hw') Hit) as Hpf.
    pose proof Hit as (Hlen & _). rewrite length_map in Hlen.
    exists fx, L, A, regs2, mm, md, Lam, peak, cnt, fail, [], (Some (t, skipn (length w) (rest_at tb text P))), [], [], [].
    split; [rewrite Hcfg; reflexivity|]. split; [exact FRM|]. split; [intros r Hr; reflexivity|].
    split; [exact (mid_rpost B API _ L A regs mem md _ L A regs2 mm md MID RP2)|].
    split; [exact RC2|]. split; [exact LED2|].
    split; [rewrite JV, lit_unfold, Hpf; reflexivity|].
    split; [apply oks_zero|]. split; [cbn; lia|]. split; [apply fail_after_zero|].
    split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|]. split; [intros a k []|].
    split; [destruct LED as (_ & (LP & _) & _); cbn [hpeak]; lia|].
    split; [cbn [hpeak]; lia|].
    split; [exact RES|].
    rewrite length_skipn.
    split; [rewrite Hg; exact G10|].
    split; [replace (text + len - Z.of_nat (length (rest_at tb text P) - length w)) with (P + Z.of_nat (length w)) by lia;
            rewrite SEG; exact PJ2|].
    split; [|cbn [lsum]; lia].
    rewrite SEG. apply lit_node with (ty := ty); [exact Htag | exact Ht | exact Hty | | exact B2 |].
    + split; [exact Hv8|]. apply (stk_patch W2 m' mm v (v + 56) Hvs MU2 WM2).
      intros a Ha. right.
      assert (Hpa : present mm a).
      { replace a with (v + (a - v)) by lia. apply (pres_of_wr B mm (v + (a - v)) SEG);
          [lia | exact (proj2 (proj2 (Hvn (a - v) ltac:(lia)))) | exact (Hvw (a - v) ltac:(lia))]. }
      destruct Hpa as (bb & Hbb). exists bb. unfold Mem.mrd, Mem.wa. rewrite Hbb. reflexivity.
    + apply (pj_bytes_eq rsegs m' mm (v + 4) _ (zeros_sub m' v 56 4 52 Hvz ltac:(lia) ltac:(cbn; lia))).
      intros x Hx. rewrite repeat_length in Hx. apply MU2. apply Hvout. lia.
  - assert (Hpf : prefixb w (rest_at tb text P) = false).
    { destruct (prefixb w (rest_at tb text P)) eqn:Ep; [|reflexivity].
      exfalso. apply Hmiss. exact (proj2 (lit_hit_prefixb tb text len P w BL HP Hw') Ep). }
    exists fx, L, A, regs2, mm, md, Lam, peak, cnt, fail, [], (@None (jv * list Z)), [], [], [].
    split; [rewrite Hcfg; reflexivity|]. split; [exact FRM|]. split; [intros r Hr; reflexivity|].
    split; [exact (mid_rpost B API _ L A regs mem md _ L A regs2 mm md MID RP2)|].
    split; [exact RC2|]. split; [exact LED2|].
    split; [rewrite JV, lit_unfold, Hpf; reflexivity|].
    split; [apply oks_zero|]. split; [cbn; lia|]. split; [apply fail_after_zero|].
    split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|]. split; [intros a k []|].
    split; [destruct LED as (_ & (LP & _) & _); cbn [hpeak]; lia|].
    split; [cbn [hpeak]; lia|].
    split; [exact RES|].
    split; [rewrite Hg; exact G10|].
    split; [apply (pv_after_ok B mm q text len P d tb); rewrite SEG; exact PJ2|].
    apply (pv_fd_zero B). rewrite SEG. apply (PvDisp.pj_zero_transport [(spZ regs - 64, spZ regs)] m' mm v PZ MU3 WM2).
    cbn [Frame.disjoint_from]. split; [lia | exact I].
Qed.

Theorem pv_lit_ok : forall d, literal_c.literal_contract -> pv_lit_stmt B API RF d.
Proof.
  intros d LIT L A regs mem md Lam peak cnt fail b q text len p tb v PRE0 P m' regs' b0 y wa ty
    HP HR PJ WM HO LS MU ST PZ R1 RP R10 R11 R12 R13.
  pose proof (PvItems.ra_len_le tb text p P HR) as LL.
  destruct LS as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]].
  - apply (pv_lit_case LIT d L A regs mem md Lam peak cnt fail b q text len p tb v PRE0 P m' regs' 0x1033c 2 w_true JTrue
      [Z_to_bv 8 58; Z_to_bv 8 0; Z_to_bv 8 73; Z_to_bv 8 78; Z_to_bv 8 70; Z_to_bv 8 0; Z_to_bv 8 99]); try assumption;
      [ unfold w_true; repeat (apply Forall_cons; [lia|]); apply Forall_nil
      | apply (Image.ro_bytes_b_sound rsegs); vm_compute; reflexivity
      | nz_tac
      | cbn; lia
      | lia
      | cbn; lia
      | lia
      | reflexivity
      | left; reflexivity
      | intros ok; rewrite jr_value_unfold, <- HR, HO; reflexivity ].
  - apply (pv_lit_case LIT d L A regs mem md Lam peak cnt fail b q text len p tb v PRE0 P m' regs' 0x10298 1 w_false JFalse
      [Z_to_bv 8 45; Z_to_bv 8 43]); try assumption;
      [ unfold w_false; repeat (apply Forall_cons; [lia|]); apply Forall_nil
      | apply (Image.ro_bytes_b_sound rsegs); vm_compute; reflexivity
      | nz_tac
      | cbn; lia
      | lia
      | cbn; lia
      | lia
      | reflexivity
      | right; left; reflexivity
      | intros ok; rewrite jr_value_unfold, <- HR, HO; reflexivity ].
  - apply (pv_lit_case LIT d L A regs mem md Lam peak cnt fail b q text len p tb v PRE0 P m' regs' 0x102fe 0 w_null JNull
      [Z_to_bv 8 117; Z_to_bv 8 115; Z_to_bv 8 97; Z_to_bv 8 103; Z_to_bv 8 101]); try assumption;
      [ unfold w_null; repeat (apply Forall_cons; [lia|]); apply Forall_nil
      | apply (Image.ro_bytes_b_sound rsegs); vm_compute; reflexivity
      | nz_tac
      | cbn; lia
      | lia
      | cbn; lia
      | lia
      | reflexivity
      | right; right; reflexivity
      | intros ok; rewrite jr_value_unfold, <- HR, HO; reflexivity ].
Qed.

End Lit.
