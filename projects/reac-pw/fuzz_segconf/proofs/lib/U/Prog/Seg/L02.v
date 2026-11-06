(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 294 of its 323 lines of code are new or changed and 545 lines of the source are left out. *)
(* Segment L02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan, ELF afc060e3cc9c): K13aac f -> K13c34 f, the
   file-loop body (0x13aac .. 0x13c30), as U/Prog/SegEvt.evt_L02 at the cut record CPseg (U), and the
   segment statement U/Prog/SegEnd.seg_L02_stmt CPseg K_L02. The twin of lib/Prog/Seg/L02.v: from FR and P_K13aac
   the memory the inner walk needs (U/Prog/Seg/L02D.L02_mem) on the CJ-normalized memory WmcEnv.M1, the turn's data
   (L02M.l02m_model), the registers; the inner walk (U/Prog/Seg/L02W.L02_inner_holds) runs; its post gives P_K13c34
   on the inner end memory (the frame cells [sp, sp + 0x60) untouched), and WmcEnv.seg_lift_cj moves it to seg_evt's
   post over normalize mem.
   Segment lemma of LLVMFuzzerTestOneInput's walk. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require KindBGlue RoAdapt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require seg_cuts m_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c SegEnd SegEvt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b8 Tac_seg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import SegWalkMainA WmcEnv L02D.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import L02M.
Import ListNotations.
Open Scope Z_scope.

(** ** The image facts of longl (vm_compute on the image's segment list) *)
Lemma l02_longl_rom : forallb (fun k => match seg_rom rsegs (Z_to_bv 64 (0x33460 + Z.of_nat k)) with
  Some _ => true | None => false end) (seq 0 128) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma l02_longl_seg : forallb (fun k => match find_segment rsegs (0x33460 + Z.of_nat k) 1 with
  Some _ => true | None => false end) (seq 0 128) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma l02_forallb_seq : forall (P : nat -> bool) n k, forallb P (seq 0 n) = true -> (k < n)%nat -> P k = true.
Proof.
  intros P n k H Hk. rewrite forallb_forall in H. apply H. apply in_seq. lia.
Qed.

Lemma l02_nat_of : forall a, 0x33460 <= a < 0x33460 + 128 -> a = 0x33460 + Z.of_nat (Z.to_nat (a - 0x33460)).
Proof. intros a Ha. rewrite Z2Nat.id by lia. lia. Qed.

Lemma l02_longl_some : forall m a, 0x33460 <= a < 0x33460 + 128 -> exists b, mrd rsegs m (wa a) = Some b.
Proof.
  intros m a Ha. unfold mrd. destruct (m (wa a)) as [b|]; [exists b; reflexivity|].
  pose proof (l02_forallb_seq _ 128 (Z.to_nat (a - 0x33460)) l02_longl_rom ltac:(lia)) as H.
  cbv beta in H. rewrite <- (l02_nat_of a Ha) in H. unfold wa.
  destruct (seg_rom rsegs (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | discriminate H].
Qed.

Lemma l02_getr_eqv_pe : forall R R' r, Regs6ss.xregs_eqv R R' -> PropExec.getr R' r = PropExec.getr R r.
Proof.
  intros R R' r H. unfold PropExec.getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  symmetry. apply H. exact E.
Qed.

(** ** The cut predicate P_K13c34 moves along the slot's relations (the CJ move, then mem_rel, xregs_eqv) *)
Lemma l02_P_back : forall inp p S f c mm t nt R' m1' m' m regs',
  seg_cuts.P_K13c34 inp p S f c mm t nt R' m1' -> mem_rel_cj rsegs m' m1' -> mem_rel rsegs m m' ->
  Regs6ss.xregs_eqv R' regs' -> seg_cuts.P_K13c34 inp p S f c mm t nt regs' m.
Proof.
  intros inp p S f c mm t nt R' m1' m' m regs'
    (Hf & Hnt & ((H18 & H27 & C8 & C10 & C20 & C48 & C50 & Hc16 & Hm16 & Hcn & Hmn) & H21 & C28 & C30 & C38 & C40) &
     H10 & H23 & H8 & H19 & H9 & H20 & H26 & (bc & Bc & Ec) & (bm & Bm & Em)) Hr1 Hr2 Hx.
  unfold seg_cuts.P_K13c34, seg_cuts.P_lcore, seg_cuts.P_mcore, seg_cuts.rgz, seg_cuts.celz in *.
  try rewrite !(sl_getr_eqv _ _ _ Hx). try rewrite !(l02_getr_eqv_pe _ _ _ Hx).
  refine (conj Hf (conj Hnt (conj
            (conj (conj H18 (conj H27 (conj _ (conj _ (conj _ (conj _ (conj _
                     (conj Hc16 (conj Hm16 (conj Hcn Hmn))))))))))
                  (conj H21 (conj _ (conj _ (conj _ _)))))
            (conj H10 (conj H23 (conj H8 (conj H19 (conj H9 (conj H20 (conj H26 (conj _ _)))))))))));
    try (eapply bytes_back; eassumption).
  - exists bc. split; [eapply bytes_back; eassumption | exact Ec].
  - exists bm. split; [eapply bytes_back; eassumption | exact Em].
Qed.

Lemma l02_st_eta : forall st : rconf * mconf * bool, (seg_rc st, seg_mc st, seg_ret st) = st.
Proof. intros [[a b] c]. reflexivity. Qed.

(** ** The slot side *)
Section L02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_ubsan B APIf LS SH SK ra empty.
Hypothesis INNER : L02_inner.

Lemma evt_L02_of_inner : evt_L02 B APIf ra empty CPseg.
Proof using fx rc B APIf LS SH SK ra empty FF INNER.
  unfold evt_L02, seg_evt. intros g f bc bm t nt L A regs mem md HFR HP HPre Hfrm.
  unfold CPseg in HPre |- *. cbn [cp_K13aac cp_K13c34] in HPre |- *.
  destruct HPre as (Hf & Htn &
                    ((H18 & H27 & C8 & C10 & C20 & C48 & C50 & Hc16 & Hm16 & Hcn & Hmn) & H21 & C28 & C30 & C38 & C40) &
                    H10 & Ht16 & Ent & (junk & Hrw) & H26 & H22 & H25 & H19 & H9 & H24 & H8 & H20 & Hrc & Hmc).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & Hsp16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & HMI0 & HRL & HM & _ & _ & _ & _ & _ & HIMG & _).
  pose proof HGV as (Hn26 & Hpl & Hdat & HS16 & HSKc & HS47c & _ & _ & _ & HGI).
  pose proof alloc_ceiling_value as HAC.
  pose proof (l02m_nfiles (g_in g)) as HNF.
  pose proof (l02m_np (g_in g) f) as HNP.
  pose proof (l02m_tail_len (g_in g) f) as HTL.
  pose proof (l02m_model (g_in g) f Hf) as HMOD.
  assert (Hnt : nt = Z.of_nat (length (seg_txt (g_in g) f)) + 1) by (rewrite Htn; reflexivity).
  unfold SLOT_K, SLOT_STACK, fsp, SLOT_FRAME, g_n in *.
  assert (HAC1 : 0x7fff7f800000 <= YM05.alloc_ceiling) by exact (proj1 (proj1 HAC)).
  assert (ELL : sa_longl SA = 0x33460) by reflexivity.
  assert (ECAT : sa_catalogue SA = 0x21468) by reflexivity.
  assert (EGG : sa_got_guard SA = 0x221b0) by reflexivity.
  assert (EGD : sa_guard SA = 0x53820) by reflexivity.
  assert (TS : TASK_SIZE = 2 ^ 47) by reflexivity.
  assert (HMI' : ro_agree rsegs mem) by (unfold MI in HMI0; rewrite SEGS in HMI0; exact HMI0).
  (* the three live blocks *)
  assert (It : In (t, nt) (hb_tcm bc bm t nt)) by (left; reflexivity).
  assert (Im : In (bm, M_SIZE) (hb_tcm bc bm t nt)) by (right; left; reflexivity).
  assert (Ic : In (bc, C_SIZE) (hb_tcm bc bm t nt)) by (right; right; left; reflexivity).
  destruct (b1_hb B APIf ra empty FF g _ t nt L A regs mem md HFR HP It) as (STt & Ht4 & Htc).
  destruct (b1_hb B APIf ra empty FF g _ bm M_SIZE L A regs mem md HFR HP Im) as (STm & Hm4 & Hmc').
  destruct (b1_hb B APIf ra empty FF g _ bc C_SIZE L A regs mem md HFR HP Ic) as (STc & Hc4 & Hcc).
  destruct (b1_slack_ok B APIf ra empty FF g _ t nt L A regs mem md HFR HP It ltac:(lia)) as (slt & Bslt & Lslt & Cslt).
  destruct (b1_slack_ok B APIf ra empty FF g _ bm M_SIZE L A regs mem md HFR HP Im ltac:(unfold M_SIZE; lia))
    as (slm & Bslm & Lslm & Cslm).
  assert (Dtm : t + nt <= bm \/ bm + M_SIZE <= t).
  { first [ exact (b1_sep B APIf ra empty g [] (t, nt) [(bm, M_SIZE); (bc, C_SIZE)] L A regs mem md (bm, M_SIZE)
                   HFR HP ltac:(left; reflexivity))
          | exact (b1_sep B APIf ra empty FF g [] (t, nt) [(bm, M_SIZE); (bc, C_SIZE)] L A regs mem md (bm, M_SIZE)
                   HFR HP ltac:(left; reflexivity)) ]. }
  assert (Dtc : t + nt <= bc \/ bc + C_SIZE <= t).
  { first [ exact (b1_sep B APIf ra empty g [] (t, nt) [(bm, M_SIZE); (bc, C_SIZE)] L A regs mem md (bc, C_SIZE)
                   HFR HP ltac:(right; left; reflexivity))
          | exact (b1_sep B APIf ra empty FF g [] (t, nt) [(bm, M_SIZE); (bc, C_SIZE)] L A regs mem md (bc, C_SIZE)
                   HFR HP ltac:(right; left; reflexivity)) ]. }
  assert (Dmc : bm + M_SIZE <= bc \/ bc + C_SIZE <= bm).
  { first [ exact (b1_sep B APIf ra empty g [(t, nt)] (bm, M_SIZE) [(bc, C_SIZE)] L A regs mem md (bc, C_SIZE)
                   HFR HP ltac:(right; left; reflexivity))
          | exact (b1_sep B APIf ra empty FF g [(t, nt)] (bm, M_SIZE) [(bc, C_SIZE)] L A regs mem md (bc, C_SIZE)
                   HFR HP ltac:(right; left; reflexivity)) ]. }
  (* longl's 128 bytes lie in the image; a block lies apart from them *)
  assert (LIMG : forall a, 0x33460 <= a < 0x33460 + 128 -> exists s, In s (segments_reserved rsegs) /\
                   bv_unsigned (fst s) <= a < bv_unsigned (fst s) + bv_unsigned (snd s)).
  { intros a Ha. pose proof (l02_forallb_seq _ 128 (Z.to_nat (a - 0x33460)) l02_longl_seg ltac:(lia)) as H.
    cbv beta in H. rewrite <- (l02_nat_of a Ha) in H.
    destruct (find_segment rsegs a 1) as [sg|] eqn:E; [|discriminate H].
    destruct (b1_find_img B a sg SEGS E) as (_ & s & Hs & Hs2). rewrite SEGS in Hs. exists s. split; assumption. }
  (* the text's source bytes in the input block *)
  unfold seg_txt_n in HNP.
  assert (HSRC : bytes_at rsegs mem (seg_turn_at (g_in g) (g_p g) f) (zb (seg_txt (g_in g) f)) /\
                 apart (seg_turn_at (g_in g) (g_p g) f) (Z.of_nat (length (seg_txt (g_in g) f))) t (t + nt) /\
                 seg_turn_at (g_in g) (g_p g) f + Z.of_nat (length (seg_txt (g_in g) f)) <= YM05.alloc_ceiling).
  { destruct Hpl as [(Hn0 & Hpe) | (Hn0 & Hinb)].
    - assert (L0 : length (g_in g) = 0%nat) by lia.
      assert (Ls : length (seg_txt (g_in g) f) = 0%nat) by lia.
      assert (Esrc : seg_turn_at (g_in g) (g_p g) f = empty) by (unfold seg_turn_at; lia).
      rewrite Esrc, Ls. destruct (seg_txt (g_in g) f) as [|x s'] eqn:Es; [|discriminate Ls]. cbn [zb map Z.of_nat].
      pose proof (ff_empty B APIf ra empty FF) as Hemp. pose proof (ff_empty_val B APIf ra empty FF) as Hempv.
      split; [apply sl_bytes_nil; lia|]. split; [|rewrite Hempv; lia].
      unfold apart. destruct (Z_le_gt_dec empty t) as [L1|L1]; [left; lia|].
      destruct (Z_le_gt_dec (t + nt) empty) as [L2|L2]; [right; lia|]. exfalso.
      assert (HQ : find_segment rsegs empty 1 <> None) by (rewrite Hempv; vm_compute; discriminate).
      destruct (find_segment rsegs empty 1) as [sg|] eqn:E; [|exact (HQ eq_refl)].
      destruct (b1_find_img B empty sg SEGS E) as (_ & sr & Hs & Hs2). rewrite SEGS in Hs.
      apply (Ent (empty - t) ltac:(lia) sr Hs). replace (t + (empty - t)) with empty by lia. exact Hs2.
    - destruct (b1_in_all B APIf ra empty FF g _ L A regs mem md HFR HP Hn0) as (Hinb' & Hp4 & Hpac & HBYT).
      unfold g_n in Hinb', Hpac.
      assert (Hk : ((length (g_in g) - length (seg_turn_tail (g_in g) f)) + length (seg_txt (g_in g) f)
                    <= length (g_in g))%nat) by lia.
      pose proof (b8_ba_sub rsegs mem (g_p g) (g_in g) _ _ HBYT Hk) as HB.
      rewrite <- (l02m_text_bytes (g_in g) f Hf) in HB.
      assert (Esrc : seg_turn_at (g_in g) (g_p g) f =
                     g_p g + Z.of_nat (length (g_in g) - length (seg_turn_tail (g_in g) f))).
      { unfold seg_turn_at. rewrite Nat2Z.inj_sub by exact HTL. lia. }
      rewrite Esrc. split; [exact HB|].
      assert (Dtp : t + nt <= g_p g \/ g_p g + Z.of_nat (length (g_in g)) <= t).
      { first [ exact (b1_sep B APIf ra empty g [] (t, nt) [(bm, M_SIZE); (bc, C_SIZE)] L A regs mem md
                         (g_p g, Z.of_nat (length (g_in g))) HFR HP ltac:(right; right; exact Hinb'))
              | exact (b1_sep B APIf ra empty FF g [] (t, nt) [(bm, M_SIZE); (bc, C_SIZE)] L A regs mem md
                         (g_p g, Z.of_nat (length (g_in g))) HFR HP ltac:(right; right; exact Hinb')) ]. }
      rewrite Nat2Z.inj_sub by exact HTL.
      split; [unfold apart; lia | lia]. }
  destruct HSRC as (HSRC & HSA & HSC).
  (* the memory the inner walk runs on *)
  assert (HMEM : L02_mem (g_S g) bc bm t nt (seg_turn_at (g_in g) (g_p g) f) (seg_nfiles (g_in g))
                   (seg_txt (g_in g) f) (seg_rc (seg_run (g_in g) f)) (seg_mc (seg_run (g_in g) f)) (M1 mem)).
  { unfold L02_mem.
    split; [apply m1_mem_inv|]. split; [apply m1_task_mem|].
    split.
    { (* ssp_ok *)
      destruct (ax_statics (b8_ax B APIf ra empty FF) L A mem md HM) as (Hgg & (gv & Hgv & Hgw) & _).
      rewrite (ff_got_guard B APIf ra empty FF), (ff_guard B APIf ra empty FF) in Hgg.
      rewrite (ff_guard B APIf ra empty FF) in Hgw. rewrite SEGS in Hgg, Hgw.
      unfold ssp_ok. rewrite EGG, EGD.
      split.
      - apply bytes_m1; [exact HMI' | rewrite length_le8, TS; lia |].
        apply (KindBGlue.word_mem_le8 rsegs); [exact Hgg | lia | lia | lia].
      - exists (Z_to_bv 64 gv). apply bytes_m1; [exact HMI' | rewrite length_le8, TS; lia |].
        apply (KindBGlue.word_mem_le8 rsegs); [exact Hgw | lia | lia | lia]. }
    split.
    { (* cat_img *)
      intros a Ha. rewrite ECAT in Ha. unfold CAT_BYTES in Ha.
      rewrite mrd_m1_n by (apply wa_low; rewrite TS; lia).
      apply (b8_relro_norm B APIf ra empty FF mem a HRL HMI0). lia. }
    split.
    { (* words_img *)
      intros a Ha. unfold m_file_c.M_KEY_WORDS in Ha.
      rewrite mrd_m1_n by (apply wa_low; rewrite TS; lia).
      apply (b8_relro_norm B APIf ra empty FF mem a HRL HMI0). lia. }
    split; [exact HS16|]. split; [lia|]. split; [exact HS47c|].
    split; [apply stk_m1; [exact ST | rewrite TS; lia]|].
    split; [intros a Ha; apply (b8_seg_rom_hi B APIf ra empty FF); lia|].
    split; [apply bytes_m1; [exact HMI' | rewrite length_le8, TS; unfold L02_FRAME; lia | exact C28]|].
    split; [apply bytes_m1; [exact HMI' | rewrite length_le8, TS; unfold L02_FRAME; lia | exact C30]|].
    split; [apply bytes_m1; [exact HMI' | rewrite length_le8, TS; unfold L02_FRAME; lia | exact C38]|].
    split; [apply bytes_m1; [exact HMI' | rewrite length_le8, TS; unfold L02_FRAME; lia | exact C40]|].
    split; [apply bytes_m1; [exact HMI' | rewrite length_le8, TS; unfold L02_FRAME; lia | exact C48]|].
    split; [apply bytes_m1; [exact HMI' | rewrite length_le8, TS; unfold L02_FRAME; lia | exact C50]|].
    split; [lia|]. split; [exact Hc16|]. split; [exact Hcn|]. split; [unfold C_SIZE in Hcc; unfold SEG_C_SIZE; lia|].
    split; [lia|]. split; [exact Hm16|]. split; [exact Hmn|]. split; [unfold M_SIZE in Hmc'; unfold SEG_M_SIZE; lia|].
    split; [lia|]. split; [exact Ht16|]. split; [exact Ent|]. split; [lia|].
    split; [exact Hnt|].
    split; [unfold apart, SEG_M_SIZE; unfold M_SIZE in Dtm; lia|].
    split; [unfold apart, SEG_C_SIZE; unfold C_SIZE in Dtc; lia|].
    split; [unfold apart, SEG_M_SIZE, SEG_C_SIZE; unfold M_SIZE, C_SIZE in Dmc; lia|].
    split; [apply apart_noimg; [exact Ent | lia | lia | rewrite ELL; exact LIMG]|].
    split; [apply apart_noimg; [exact Hmn | unfold SEG_M_SIZE; lia | lia | rewrite ELL; exact LIMG]|].
    split; [apply apart_noimg; [exact Hcn | unfold SEG_C_SIZE; lia | lia | rewrite ELL; exact LIMG]|].
    split.
    { destruct Hrc as (bs & Hb & He). exists bs. split; [|exact He].
      apply bytes_m1; [exact HMI' | | exact Hb]. destruct He as (Hl & _). rewrite Hl, TS. unfold SEG_C_SIZE, C_SIZE in *. lia. }
    split.
    { replace SEG_C_SIZE with (bc + C_SIZE - bc) by (unfold SEG_C_SIZE, C_SIZE; lia).
      apply wr_m1; [exact (wr_of_stk _ _ _ STc) | rewrite TS; lia]. }
    split.
    { destruct Hmc as (bs & Hb & He). exists bs. split; [|exact He].
      apply bytes_m1; [exact HMI' | | exact Hb]. destruct He as (Hl & _). rewrite Hl, TS. unfold SEG_M_SIZE, M_SIZE in *. lia. }
    split.
    { replace SEG_M_SIZE with (bm + M_SIZE - bm) by (unfold SEG_M_SIZE, M_SIZE; lia).
      apply wr_m1; [exact (wr_of_stk _ _ _ STm) | rewrite TS; lia]. }
    split.
    { exists slm. split; [|unfold SEG_M_SIZE, M_SIZE in *; exact Lslm].
      apply bytes_m1_n; [rewrite TS; unfold SEG_M_SIZE, M_SIZE in *; lia | exact Bslm]. }
    split.
    { exists junk. apply rw_cells_m1; [exact HMI' | | | exact Hrw].
      - cbn [cells_size csize]. rewrite TS. lia.
      - intros i Hi. cbn [cells_size csize] in Hi. unfold ro_addr.
        rewrite wa_unsigned by lia.
        rewrite (b1_blk_noseg B APIf ra empty FF L A mem md t nt (t + i) HM (b1_in_hb _ _ _ _ HP It) ltac:(lia)).
        reflexivity. }
    split.
    { exists slt. split; [|exact Lslt]. apply bytes_m1_n; [rewrite TS; lia | exact Bslt]. }
    split.
    { apply bytes_m1; [exact HMI' | | exact HSRC]. unfold zb. rewrite length_map, TS. lia. }
    split; [exact HSA|].
    split.
    { destruct (bytes_exist (M1 mem) (sa_longl SA) 120) as (lj & Hlj & Hbl).
      - lia.
      - lia.
      - intros k Hk. apply l02_longl_some. lia.
      - exists lj. split; [split|].
        + cbn [cells_wf cell_wf]. split; [exact Hlj | exact I].
        + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hbl.
        + cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi.
          refine (sl_longl_writable (M1 mem) (sa_longl SA + i) _). exists 0x33460, 121.
          split; [left; reflexivity | lia]. }
    { destruct (bytes_exist (M1 mem) (sa_longl SA + 121) 7) as (sl & Hsl & Hbs).
      - lia.
      - lia.
      - intros k Hk. apply l02_longl_some. lia.
      - exists sl. split; [|exact Hsl].
        assert (H120 : mrd rsegs (M1 mem) (wa (sa_longl SA + 120)) = Some ZERO).
        { rewrite mrd_m1 by (exact HMI' || (apply wa_low; rewrite TS; lia)).
          destruct (ff_G B APIf ra empty FF (LONGL + LONGL_W) sl_longl_nul_in) as (Gi & Gs & Gc & Ge).
          destruct (HIMG (LONGL + LONGL_W) Gi Gs Gc Ge ltac:(unfold LONGL_W; lia)) as (Eb & _).
          unfold GIb in HGI. rewrite SEGS in Eb, HGI. rewrite HGI in Eb.
          rewrite ELL. exact Eb. }
        destruct Hbs as (Hb0 & Hb1 & Hb2).
        split; [lia|]. cbn [length]. rewrite Hsl.
        split; [lia|]. intros i Hi.
        destruct i as [|i]; [rewrite Z.add_0_r; exact H120|].
        cbn [nth_error]. rewrite <- (Hb2 i ltac:(lia)). f_equal. unfold wa. f_equal. lia. } }
  (* the inner walk *)
  apply (seg_lift_cj mem (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x13aac) fp_csr 0x13c34
           (seg_W g (hb_tcm bc bm t nt)) (L02_W (g_S g) bc bm t nt)
           (YK11.getr regs 2) (YK11.getr regs 3) (YK11.getr regs 4)
           (seg_cuts.P_K13c34 (g_in g) (g_p g) (g_S g) f bc bm t nt)).
  - (* L02_W inside seg_W *)
    intros x Hx. unfold seg_W, L02_W in *. cbn [Frame.outside map fst snd hb_tcm hb_cm] in *.
    unfold SLOT_K, SLOT_STACK, LONGL, LONGL_W, L02_FRAME, C_SIZE, M_SIZE, SEG_C_SIZE, SEG_M_SIZE in *.
    destruct Hx as (X1 & X2 & X3 & X4 & X5 & _).
    repeat split; lia.
  - intros R' m1' m' m regs' HP' H1 H2 Hx. exact (l02_P_back _ _ _ _ _ _ _ _ R' m1' m' m regs' HP' H1 H2 Hx).
  - rewrite sl_mkR_of.
    eapply evt_mono.
    + apply (INNER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fp_regs fp_csr (M1 mem)
               (g_S g) bc bm t nt (seg_turn_at (g_in g) (g_p g) f)
               (Z.of_nat (length (seg_turn_tail (g_in g) f)))
               (seg_turn_np (g_in g) f) (Z.of_nat f) (seg_nfiles (g_in g)) (seg_lb (g_in g) f) (seg_txt (g_in g) f)
               (seg_rc (seg_run (g_in g) f)) (seg_mc (seg_run (g_in g) f)) (seg_ret (seg_run (g_in g) f)));
        first [ exact Hsp | exact H10 | exact H27 | exact H18 | exact H21 | exact H8 | exact H20 | exact H26
              | exact H25 | exact H9 | exact H22 | exact H24 | exact Hfrm | exact HMOD | exact HMEM | lia ].
    + intros ms (ra' & t0' & t1' & t2' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s4' & s7' &
                 s8' & s9' & s10' & t3' & t4' & t5' & t6' & F' & fc' & m' & -> & Hz & MU & WM & MI' & TM' &
                 Ea0 & Es7 & Es0 & Es1 & Es10 & Es4 & Hrc2 & Hmc2).
      rewrite l02_st_eta in Es4, Hrc2, Hmc2.
      rewrite <- (l02m_after (g_in g) f) in Es4, Hrc2, Hmc2.
      do 4 eexists. split; [reflexivity|]. split; [exact Hz|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      assert (OUT : forall a, g_S g - 240 <= a < g_S g - 240 + 0x60 -> Frame.outside (L02_W (g_S g) bc bm t nt) a).
      { intros a Ha. unfold L02_W. cbn [Frame.outside].
        unfold L02_FRAME, SEG_M_SIZE, SEG_C_SIZE in *. unfold C_SIZE, M_SIZE in *.
        repeat split; try exact I; lia. }
      assert (KEEP : forall off v, 0 <= off -> off + 8 <= 0x60 ->
                bytes_at rsegs mem (g_S g - seg_cuts.SEG_FRAME + off) (le8 (Z_to_bv 64 v)) ->
                bytes_at rsegs m' (g_S g - seg_cuts.SEG_FRAME + off) (le8 (Z_to_bv 64 v))).
      { intros off v H0 H1 Hb.
        assert (HbM : bytes_at rsegs (M1 mem) (g_S g - seg_cuts.SEG_FRAME + off) (le8 (Z_to_bv 64 v))).
        { apply bytes_m1; [exact HMI' | rewrite length_le8, TS; unfold seg_cuts.SEG_FRAME; lia | exact Hb]. }
        apply (b8_ba_keepW _ (M1 mem) m' _ _ HbM MU).
        intros x Hx. rewrite length_le8 in Hx. apply OUT. unfold seg_cuts.SEG_FRAME in Hx. lia. }
      unfold seg_cuts.P_K13c34, seg_cuts.P_lcore, seg_cuts.P_mcore, seg_cuts.rgz, seg_cuts.celz.
      split; [exact Hf|]. split; [exact Htn|].
      split.
      { split.
        { split; [exact H18|]. split; [exact H27|].
          split; [apply KEEP; [lia | lia | exact C8]|]. split; [apply KEEP; [lia | lia | exact C10]|].
          split; [apply KEEP; [lia | lia | exact C20]|]. split; [apply KEEP; [lia | lia | exact C48]|].
          split; [apply KEEP; [lia | lia | exact C50]|].
          split; [exact Hc16|]. split; [exact Hm16|]. split; [exact Hcn | exact Hmn]. }
        split; [exact H21|].
        split; [apply KEEP; [lia | lia | exact C28]|]. split; [apply KEEP; [lia | lia | exact C30]|].
        split; [apply KEEP; [lia | lia | exact C38]|]. apply KEEP; [lia | lia | exact C40]. }
      split; [exact Ea0|]. split; [exact Es7|].
      split; [rewrite Nat2Z.inj_succ; exact Es0|].
      split; [rewrite <- (proj1 (l02m_cur_next (g_in g) (g_p g) f)) in H19; exact H19|].
      split; [rewrite <- (proj2 (l02m_cur_next (g_in g) (g_p g) f)) in Es1; exact Es1|].
      split; [exact Es4|].
      split; [exact Es10|].
      split; [exact Hrc2 | exact Hmc2].
Qed.

End L02.
