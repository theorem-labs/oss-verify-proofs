From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame Exec Cells Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct PjIn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import PvDefs PvModel PvGlue PvMain0 PvPaths.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import parse_items_c.
Import ListNotations.
Local Open Scope Z_scope.
Module Frame := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Frame.
Module MState := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.MState.
Module Mem := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.

Lemma skipn_nth : forall (T : Type) n (l : list T) c r, skipn n l = c :: r -> nth_error l n = Some c.
Proof.
  intros T n. induction n as [|n IH]; intros [|x l] c r H; cbn in *; try discriminate.
  - injection H as -> _. reflexivity.
  - exact (IH l c r H).
Qed.

Lemma byte_rt : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma ra_nth : forall (tb : list byte) text P b y, rest_at tb text P = b :: y ->
  nth_error tb (Z.to_nat (P - text)) = Some (Z_to_bv 8 b).
Proof.
  intros tb text P b y H. unfold rest_at, zb in H.
  destruct (skipn (Z.to_nat (P - text)) tb) as [|c r] eqn:E; [discriminate|].
  cbn [map] in H. injection H as Hb _. rewrite (skipn_nth _ _ _ c r E). rewrite <- Hb, byte_rt. reflexivity.
Qed.

Lemma ra_len_le : forall (tb : list byte) text p P, rest_at tb text P = skip (rest_at tb text p) ->
  (length (rest_at tb text P) <= length (rest_at tb text p))%nat.
Proof. intros tb text p P H. rewrite H. apply skip_len. Qed.

Section Items.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Local Abbreviation segs := (ms_segs B).
Local Abbreviation MR := (aa_MR API).

Theorem pv_items_ok : forall d, parse_items_contract B API RF d -> pv_items_stmt B API RF d.
Proof.
  intros d PI L A regs mem md Lam peak cnt fail b q text len p tb v PRE0 P m' regs' o y HP HR PJ WM HO MU ST PZ
    R1 RP R10 R11 R12.
  pose proof PRE0 as (ENV & LED & RES & Q10 & V11 & PJ0 & Hq & QA & MX & TX & V0 & VZ & VP & D1 & D2 & CN & RR).
  pose proof ENV as (SEG & TP & EA & GG & GD & PRE & H47 & GT & FRM & RC).
  pose proof (pj_in_ok_bounds segs _ _ _ _ _ _ _ PJ0) as (_ & _ & _ & Bp & _ & _ & BL & _ & Bd).
  assert (Hd : (d <= MAXD)%nat) by (unfold MAXD; lia).
  pose proof PRE as (HM & HWF & HB & HRA & Hal & Hlo & Hhi & HWs & Htp & Her & Haux).
  pose proof (pvk_bounds d Hd) as (K1 & K2 & K3).
  pose proof ceil_big as Cb.
  assert (Hsp : spZ regs' = spZ regs).
  { unfold spZ. f_equal. exact (RP 2 ltac:(unfold callee_saved; lia)). }
  rewrite <- SEG in PJ, WM, PZ, ST.
  assert (HW' : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside [(spZ regs - 64, spZ regs); (q, q + 8)] x ->
                  spZ regs - 64 <= x).
  { intros x Hx Ho. destruct (outside2 _ _ _ _ _ Ho) as [H|H]; lia. }
  assert (MID0 : forall E : Z -> Prop, (forall x, q <= x < q + 8 -> E x) ->
                   pv_mid B API (PARSE_VALUE_K d) (spZ regs) L A mem md E L A m' md).
  { intros E HE. apply (pv_mid_A0 B API d L A regs mem md q m' E _ SEG PRE Hd Hq MU WM).
    intros x Hx Ho. destruct (outside2 _ _ _ _ _ Ho) as [H|H]; [left; exact H|].
    right. split; [lia | apply HE; exact H]. }
  pose proof (MID0 (fun _ => True) (fun _ _ => I)) as (HM1 & _).
  pose proof (pv_ledger_A0 B API d L A regs mem md Lam peak cnt fail q m' _ PRE Hd LED Hq MU HW') as LED1.
  pose proof (pv_cells_A0 B d regs mem m' _ SEG GG GD GT Hd RC MU HW') as RC1.
  assert (Hhigh : forall lo x, q + 24 <= lo -> 0 <= x < 2 ^ 64 -> lo <= x ->
                    Frame.outside [(spZ regs - 64, spZ regs); (q, q + 8)] x).
  { intros lo x Hl Hx Hlx. cbn [Frame.outside]. split; [lia|]. split; [lia | exact I]. }
  assert (Hown : forall x, 0 <= x < alloc_ceiling -> owned B L A x ->
                   Frame.outside [(spZ regs - 64, spZ regs); (q, q + 8)] x).
  { intros x Hx Ho. cbn [Frame.outside]. split; [lia|]. split; [lia | exact I]. }
  assert (AXq : st_init_done A = false -> auxv_pre B (ly_sec L) (q + 24) m').
  { intros Hf. apply (kb_auxv B API _ _ mem m' _ L A md HM (QA Hf) MU); [|exact Hown].
    intros x Hx Hlx. exact (Hhigh (q + 24) x ltac:(lia) Hx Hlx). }
  assert (AXv : spZ regs <= v -> st_init_done A = false -> auxv_pre B (ly_sec L) (v + 56) m').
  { intros Hsv Hf. destruct VP as (_ & VPa & _).
    apply (auxv_pre_mono B _ (Z.max (v + 56) (q + 24))); [lia|].
    apply (kb_auxv B API _ _ mem m' [(spZ regs - 64, spZ regs); (q, q + 8)] L A md HM);
      [eapply auxv_join; [exact (VPa Hsv Hf) | exact (QA Hf)] | exact MU | | exact Hown].
    intros x Hx Hlx. exact (Hhigh (Z.max (v + 56) (q + 24)) x ltac:(lia) Hx Hlx). }
  assert (JV : forall ok, jr_value jr_strtod d (rest_at tb text p) ok = jr_items jr_strtod d o (rest_at tb text P) ok).
  { intros ok. rewrite jr_value_unfold, <- HR, HO. destruct o; reflexivity. }
  pose proof (ra_len_le tb text p P HR) as LL.
  eapply SR_mono.
  { apply (PI L A regs' m' md Lam peak cnt fail b q text len P tb v o).
    - split; [exact SEG|]. split; [exact TP|]. split; [exact EA|]. split; [exact GG|]. split; [exact GD|].
      split.
      { apply (pre_callee B API (PARSE_VALUE_K d) 0 (PARSE_ITEMS_K d) L A regs mem md regs' m' (q + 24) PRE);
          [lia | lia | lia | lia | rewrite Hsp; exact Hal | exact (RP 4 ltac:(unfold callee_saved; lia)) |
           rewrite R1; exact HRA | exact HM1 | exact WM | exact AXq | lia]. }
      split; [rewrite Hsp; exact H47|]. split; [rewrite Hsp; lia|]. split; [exact FRM | exact RC1].
    - exact LED1.
    - exact RES.
    - exact R10.
    - exact R11.
    - exact R12.
    - exact PJ.
    - pose proof (rest_at_len tb text len P BL HP) as RL. rewrite HO in RL. cbn [length] in RL. lia.
    - exact (ra_nth tb text P _ y HO).
    - lia.
    - exact AXq.
    - exact MX.
    - unfold text_ok in *. rewrite Hsp. exact TX.
    - exact V0.
    - exact PZ.
    - destruct VP as (VP1 & _ & VP3). split; [rewrite Hsp; exact VP1|]. split; [rewrite Hsp; exact AXv | exact VP3].
    - exact D1.
    - rewrite Hsp. apply (disjoint_from_sub _ _ _ _ _ D2); lia.
    - lia.
    - rewrite <- (JV []). exact RR. }
  intros c' (fx' & L' & A' & regs'' & mem'' & md'' & Lam' & peak' & cnt' & fail' & ok & res & tr & okr & D & -> &
    FZ & FK & RPo & RC2 & LED2 & JI & OK & CNT & FA & PL & LS & NL & NB & PK & HPK & RO2 & Hres).
  unfold pv_post. exists fx', L', A', regs'', mem'', md'', Lam', peak', cnt', fail', ok, res, tr, okr, D.
  split; [rewrite R1; reflexivity|].
  split; [exact FZ|]. split; [exact FK|].
  split.
  { pose proof RPo as (HM2 & _ & _ & _ & _ & _ & _ & _ & _ & RP2 & _).
    assert (HDl : forall a k, In (a, k) D -> a + k <= alloc_ceiling).
    { intros a k Hin.
      assert (Hin' : In (a, k) Lam') by (apply (Permutation_in _ (Permutation_sym PL)); apply in_or_app; left; exact Hin).
      pose proof (ledger_block_range B API L' A' mem'' md'' Lam' peak' cnt' fail' a k HM2 LED2 Hin'). lia. }
    pose proof (MID0 (rd_writes q v D) (fun x Hx => or_intror (or_introl (or_introl Hx)))) as MA.
    assert (MB : pv_mid B API (PARSE_VALUE_K d) (spZ regs) L A m' md (rd_writes q v D) L' A' mem'' md'').
    { apply (mid_of_rpost B API (PARSE_VALUE_K d) (spZ regs) (PARSE_ITEMS_K d) L A regs' m' md (rd_writes q v D)
        (rd_writes q v D) L' A' regs'' mem'' md'' RPo); [rewrite Hsp; lia | rewrite Hsp; lia | intros a Ha; exact Ha | | lia | lia |].
      - intros a Ha Hn Hw. pose proof D2 as D2'. cbn [Frame.disjoint_from] in D2'.
        destruct Hw as [Hw|[Hw|[(a0 & k0 & Hin & Hw)|Hw]]].
        + lia.
        + unfold pj_in_set in Hw. lia.
        + pose proof (HDl a0 k0 Hin). lia.
        + unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hw. lia.
      - intros a [Ha|Ha]; unfold writable_at; apply WM; [exact (HWs a Ha) | exact (Her a Ha)]. }
    eapply mid_rpost; [|exact (kb_preserved_trans _ _ _ RP RP2)].
    eapply mid_E; [eapply mid_seq; [exact MA | exact MB]|]. intros a [Ha|Ha]; exact Ha. }
  split; [exact RC2|]. split; [exact LED2|]. split; [rewrite JV; exact JI|].
  split; [exact OK|]. split; [exact CNT|]. split; [exact FA|]. split; [exact PL|]. split; [exact LS|].
  split; [exact NL|]. split; [exact NB|]. split; [exact PK|].
  split; [lia|]. split; [exact RO2|].
  destruct res as [[t r]|].
  - destruct Hres as (H10 & H2 & H3 & H4). split; [exact H10|]. split; [exact H2|]. split; [exact H3 | lia].
  - destruct Hres as (H10 & (p' & d' & Hp' & Hd' & Hr) & H3). split; [exact H10|]. split; [|exact H3].
    exists p', d'. split; [exact Hp'|]. split; [lia | exact Hr].
Qed.

End Items.
