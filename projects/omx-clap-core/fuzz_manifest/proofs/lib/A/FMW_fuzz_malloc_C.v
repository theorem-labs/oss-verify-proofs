(* fuzz_malloc, segment C: from the return of __asan_poison_memory_region (0x81a10) to the `ret` (0x81a50):
   g_live += n, g_peak = max (g_peak, g_live), a0 = b + 16, the epilogue; closed by fmm_post_close. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0s YG0d YG0p YG0q YCbq YC5d YCbp YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0m AF0x AE2y ACej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import ACeg.
From OSSVerify.omx_clap_core.fuzz_manifest.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMpoisonS FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_fuzz_alloc_base FMW_fuzz_malloc_lem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_fuzz_malloc_Cpost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis TL : TfibLib B.
#[local] Notation LAWS := (AR_laws_ok tfibsegs B).

(* entry atoms past the registers: 32 g_live, 33 g_peak, 34..37 the entry ra, s0, s1, s2 saved in the frame *)
Definition fmmC_extra (regs : bvmap 5 word) (live peak : Z) : list word :=
  [w64 live; w64 peak; getr regs 1; getr regs 8; getr regs 9; getr regs 18].
(* the 32-byte frame at sp = sp0 - 32 (atom 2), read only: s2, s1, s0, ra at sp + 0, 8, 16, 24 *)
Definition fmmC_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 32 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 37 0)); YP09.mkChunk 8 (CVal 8 (SOff 36 0));
    YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 8 (SOff 34 0))].
Definition ss_fmmC : sstate :=
  mkSS 530960 sr_atoms [fmmC_frame; fm_wcell G_LIVE 32; fm_wcell G_PEAK 33] None (mkFacts [] [] []).

(* the bytes the segment may write: g_live and g_peak (the frame is only read) *)
Definition fmmC_win (a : Z) : Prop := G_LIVE <= a < G_LIVE + 8 \/ G_PEAK <= a < G_PEAK + 8.
Lemma fmmC_win_inFP : forall a, fmmC_win a -> inFP FM_PSTAT_FP a.
Proof. intros a Ha. apply fmm_cell_inFP. unfold fmmC_win, fmm_cell in *. tauto. Qed.

(* the callee-saved registers at the ret: sp, s0, s1, s2 restored, the rest as at 0x81a10, which kept the entry's *)
Lemma fmmC_regs : forall (regs regs5 regs6 : bvmap 5 word),
  getr regs6 (Z_to_bv 5 2) = getr regs (Z_to_bv 5 2) -> getr regs6 (Z_to_bv 5 8) = getr regs (Z_to_bv 5 8) ->
  getr regs6 (Z_to_bv 5 9) = getr regs (Z_to_bv 5 9) -> getr regs6 (Z_to_bv 5 18) = getr regs (Z_to_bv 5 18) ->
  (forall r : bv 5, In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs6 r = getr regs5 r) ->
  (forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 ->
     getr regs5 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  aregs_preserved regs regs6.
Proof.
intros regs regs5 regs6 P2 P8 P9 P18 K Rcs r Hr.
destruct (Z.eq_dec r 2) as [->|N2]; [exact P2|].
destruct (Z.eq_dec r 8) as [->|N8]; [exact P8|].
destruct (Z.eq_dec r 9) as [->|N9]; [exact P9|].
destruct (Z.eq_dec r 18) as [->|N18]; [exact P18|].
rewrite <- (Rcs r Hr N2 N8 N9 N18). apply K.
assert (R : r = 3 \/ r = 4 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
  by (unfold acallee_saved in Hr; lia).
clear - R. repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; subst r; cbn [In];
  repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]).
Qed.

(* the state at 0x81a10: regs at entry (regs, sp0 = spZ regs), the block b = res, the head user-poisoned; the frame
   holds the entry ra, s0, s1, s2 at sp0 - 8, -16, -24, -32; s0 = n, s1 = b, sp = sp0 - 32 *)
Lemma fmm_seg_C : forall ly S (W : world tfibsegs) regs mem md ch n live peak cnt fail
  ly2 S2 (W2 : world tfibsegs) regs5 mem5 md5 res,
  afn_pre tfibsegs B STK_fuzz_malloc ly S W regs mem md ch ->
  cnt <> fail -> 1 <= n -> n + 16 < 2 ^ 28 -> live + n < 2 ^ 33 -> cnt + 1 < 2 ^ 33 ->
  0 <= live <= peak -> peak < 2 ^ 33 -> 0 <= cnt -> 0 <= fail < 2 ^ 64 ->
  ajournal tfibsegs B STK_fuzz_malloc (spZ regs) FM_PSTAT_FP ly S W mem md [] ly2 S2 W2 (unpoison [(res, 16)] mem5) md5 1 ->
  upoison_ok B ly2 S2 [(res, 16)] -> upoisoned tfibsegs W2 mem5 [(res, 16)] ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, n + 16)] ->
  val_mem tfibsegs (mrestrict (w_H W2) mem5) res 8 n ->
  getr regs5 2 = w64 (spZ regs - 32) -> getr regs5 8 = w64 n -> getr regs5 9 = w64 res ->
  (forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 ->
     getr regs5 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  val_mem tfibsegs (mrestrict (w_H W2) mem5) (spZ regs - 8) 8 (raZ regs) ->
  val_mem tfibsegs (mrestrict (w_H W2) mem5) (spZ regs - 16) 8 (s0Z regs) ->
  val_mem tfibsegs (mrestrict (w_H W2) mem5) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
  val_mem tfibsegs (mrestrict (w_H W2) mem5) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
  val_mem tfibsegs (mrestrict (w_H W2) mem5) G_LIVE 8 live ->
  val_mem tfibsegs (mrestrict (w_H W2) mem5) G_PEAK 8 peak ->
  val_mem tfibsegs (mrestrict (w_H W2) mem5) G_COUNT 8 (cnt + 1) ->
  val_mem tfibsegs (mrestrict (w_H W2) mem5) G_FAIL 8 fail ->
  SRr tfibsegs W2 (mkCfg (mkst regs5 (Z_to_bv 64 0x81a10) mem5 (seg_rom tfibsegs)) md5)
    (fmm_post2 B regs ly S W mem md n live peak cnt fail).
Proof using HB TL.
intros ly S W regs mem md ch n live peak cnt fail ly2 S2 W2 regs5 mem5 md5 res
  HPRE Hcf Hn1 HnM HLn Hc33 Hlp Hp33 Hc0 Hf64 J5 UOK UPS Eab Vh G2 G8 G9 Rcs Vra Vs0 Vs1 Vs2 GL GP GC GF.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof fma_wx as Hwx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : STK_fuzz_malloc = 16416) by reflexivity.
rewrite FFS in Hslo.
unfold YK0s.ret_ok in Hra.
set (E := Ereg regs5 (fmmC_extra regs live peak)).
assert (E2 : ew E 2 = w64 (spZ regs - 32)) by exact (eq_trans (ew_Ereg_nat regs5 (fmmC_extra regs live peak) 2 2%bv eq_refl) G2).
assert (E8 : ew E 8 = w64 n) by exact (eq_trans (ew_Ereg_nat regs5 (fmmC_extra regs live peak) 8 8%bv eq_refl) G8).
assert (E9 : ew E 9 = w64 res) by exact (eq_trans (ew_Ereg_nat regs5 (fmmC_extra regs live peak) 9 9%bv eq_refl) G9).
assert (E32 : ew E 32 = w64 live) by exact (ew_Ereg_extra regs5 (fmmC_extra regs live peak) 0).
assert (E33 : ew E 33 = w64 peak) by exact (ew_Ereg_extra regs5 (fmmC_extra regs live peak) 1).
assert (E34 : ew E 34 = getr regs 1) by exact (ew_Ereg_extra regs5 (fmmC_extra regs live peak) 2).
assert (E35 : ew E 35 = getr regs 8) by exact (ew_Ereg_extra regs5 (fmmC_extra regs live peak) 3).
assert (E36 : ew E 36 = getr regs 9) by exact (ew_Ereg_extra regs5 (fmmC_extra regs live peak) 4).
assert (E37 : ew E 37 = getr regs 18) by exact (ew_Ereg_extra regs5 (fmmC_extra regs live peak) 5).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 32).
{ rewrite E2. unfold YG0d.w64. apply unsigned_lit_small. lia. }
assert (HS : st_ok tfibsegs E ss_fmmC (restrict (w_H W2) (mkst regs5 (Z_to_bv 64 530960) mem5 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok; fold E.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold region_ok, fmmC_frame.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      * apply (chunk_ok_val tfibsegs E _ (spZ regs - 32) 0 8 (SOff 37 0) (bv_unsigned (getr regs 18)));
          [cbn [sv_denot]; rewrite E37, Z.add_0_r; reflexivity | exact (u64_range _) | cbn; lia |].
        replace (spZ regs - 32 + 0) with (spZ regs - 32) by lia. exact Vs2.
      * apply (chunk_ok_val tfibsegs E _ (spZ regs - 32) 8 8 (SOff 36 0) (bv_unsigned (getr regs 9)));
          [cbn [sv_denot]; rewrite E36, Z.add_0_r; reflexivity | exact (u64_range _) | cbn; lia |].
        replace (spZ regs - 32 + 8) with (spZ regs - 24) by lia. exact Vs1.
      * apply (chunk_ok_val tfibsegs E _ (spZ regs - 32) 16 8 (SOff 35 0) (s0Z regs));
          [cbn [sv_denot]; rewrite E35, Z.add_0_r; reflexivity | exact (u64_range _) | cbn; lia |].
        replace (spZ regs - 32 + 16) with (spZ regs - 16) by lia. exact Vs0.
      * apply (chunk_ok_val tfibsegs E _ (spZ regs - 32) 24 8 (SOff 34 0) (raZ regs));
          [cbn [sv_denot]; rewrite E34, Z.add_0_r; reflexivity | exact (u64_range _) | cbn; lia |].
        replace (spZ regs - 32 + 24) with (spZ regs - 8) by lia. exact Vra.
    + apply (region_ok_fm_wcell _ _ G_LIVE 32 live); [exact GL | exact E32 | lia | unfold G_LIVE; lia | unfold G_LIVE; lia].
    + apply (region_ok_fm_wcell _ _ G_PEAK 33 peak); [exact GP | exact E33 | lia | unfold G_PEAK; lia | unfold G_PEAK; lia].
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, fmmC_frame, fm_wcell, G_LIVE, G_PEAK.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp. repeat split; try exact I; lia.
  - exact I. }
assert (HEE : E = Ereg regs5 (fmmC_extra regs live peak)) by reflexivity.
clearbody E.
(* g_live + n, the value the run stores *)
assert (DS : sv_denot E (SAlu Instr.ALU_ADD (SOff 8 0) (SOff 32 0)) = Z_to_bv 64 (live + n)).
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 8 n E8 ltac:(lia)), (U_atom E 32 live E32 ltac:(lia)).
  rewrite zcanon_id by (unfold M64; lia). lia. }
assert (US : U E (SAlu Instr.ALU_ADD (SOff 8 0) (SOff 32 0)) = live + n).
{ unfold U. rewrite DS. apply unsigned_lit_small. lia. }
(* the block b = res: its bounds, outside the image *)
pose proof (proj1 J5) as HAR5.
assert (Hin5 : In (res, n + 16) (ablocks B ly2 S2)) by (rewrite Eab; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 _ md5 res (n + 16) HAR5 Hin5) as (Hr16 & Hr4096 & Hrceil & _).
assert (Hrq : req_size (n + 16) = n + 16) by (unfold req_size; destruct (Z.eqb_spec (n + 16) 0); lia).
rewrite Hrq in Hrceil.
assert (HARU5 : ARU tfibsegs B ly2 S2 [(res, 16)] W2 mem5 md5) by exact (conj HAR5 (conj UOK UPS)).
(* 0x81a10 .. the bgeu at 0x81a28: g_live += n *)
assert (WIN1 : forall a, in_wrange E (ss_mem ss_fmmC) a -> fmmC_win a) by (unfold fmmC_win; win_solve Usp).
srr_runG_with tbl_fmm_ok HS.
rename ms into ms1, HF into HF1, HFr into HFr1, HG into HG1, HH into HH1.
srr_branch_with tbl_fmm_ok HS.
all: rewrite branch_geu_U, (U_atom E 33 peak E33 ltac:(lia)), US in Hc.
all: lazymatch goal with HS0 : st_ok _ _ ?ss _ |- _ =>
  assert (WIN2 : forall a, in_wrange E (ss_mem ss) a -> fmmC_win a) by (unfold fmmC_win; win_solve Usp) end.
(* .. the ret at 0x81a50: the g_peak store when g_peak < g_live, a0 = b + 16, the epilogue *)
all: srr_runG_with tbl_fmm_ok HS.
all: rename ms into ms2, HF into HF2, HFr into HFr2, HG into HG2, HH into HH2.
all: assert (GP6 : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms2)) G_PEAK 8 (Z.max peak (live + n))).
1: { (* bgeu taken: g_peak >= g_live, the store skipped *)
  apply Bool.negb_true_iff, Z.ltb_ge in Hc. rewrite Z.max_l by lia.
  eapply (val_mem_of_chunk8 E _ (ss_mem _) 2%nat G_PEAK (SOff 33 0) peak);
    [exact (st_ok_mem_ok E _ (w_H W2) ms2 HS) | vm_compute; reflexivity | | lia].
  rewrite denot_lit_U, (U_atom E 33 peak E33 ltac:(lia)). reflexivity. }
2: { (* fall through: g_peak = g_live *)
  apply Bool.negb_false_iff, Z.ltb_lt in Hc. rewrite Z.max_r by lia.
  eapply (val_mem_of_chunk8 E _ (ss_mem _) 2%nat G_PEAK (SAlu Instr.ALU_ADD (SOff 8 0) (SOff 32 0)) (live + n));
    [exact (st_ok_mem_ok E _ (w_H W2) ms2 HS) | vm_compute; reflexivity | exact DS | lia]. }
all: clear Hc.
all: eapply (SRr_ret_at tfibsegs tbl_fmm tbl_fmm_ok Hwx W2 E); [exact HS | reflexivity | vm_compute; reflexivity |].
all: intros mat2; rewrite wvb_collapse.
all: rreg HS (1%bv : bv 5) Q1.
all: rewrite Q1, E34, Hra.
all: assert (RAW : forall x : word, ~ fmmC_win (bv_unsigned x) -> ms_mem ms2 x = mem5 x)
  by (intros x Hx; rewrite (HF2 x (fun H => Hx (WIN2 _ H))), (HF1 x (fun H => Hx (WIN1 _ H))); reflexivity).
all: assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ fmmC_win a ->
    aview tfibsegs (w_H W2) (ms_mem ms2) a = aview tfibsegs (w_H W2) mem5 a)
  by (intros a Ha Hw; apply aview_eq_of; unfold mrestrict;
      rewrite RAW; [reflexivity | rewrite unsigned_lit_small by lia; exact Hw]).
(* the journal: the run wrote only g_live and g_peak (in FM_PSTAT_FP); the user-poisoned head reads as before *)
all: assert (J6 : ajournal tfibsegs B STK_fuzz_malloc (spZ regs) FM_PSTAT_FP ly S W mem md [] ly2 S2 W2
    (unpoison [(res, 16)] (ms_mem ms2)) (with_vm_backing (m_vm_lazy md5) mat2 md5) 1)
  by (eapply (ajournal_stk_pstat B HB);
      [ exact J5
      | intros a Ha; exact Ha
      | intros x Hs Hp; unfold mrestrict, unpoison; destruct (w_H W2 x); [reflexivity|];
        destruct (in_ush [(res, 16)] (bv_unsigned x)); [reflexivity|];
        exact (RAW x (fun Hw => Hp (fmmC_win_inFP _ Hw)))
      | intros x; unfold mrestrict, unpoison; destruct (w_H W2 x) eqn:Ew; [exact (fun h => h)|];
        destruct (in_ush [(res, 16)] (bv_unsigned x)); [exact (fun h => h)|];
        intros Hx; pose proof (HG1 x) as G1'; pose proof (HG2 x) as G2'; unfold mrestrict in G1', G2';
        rewrite Ew in G1', G2'; exact (G2' (G1' Hx))
      | intros x Hx; unfold unpoison; destruct (in_ush [(res, 16)] (bv_unsigned x)); [reflexivity|];
        exact (eq_trans (HH2 x Hx) (HH1 x Hx))
      | apply same_but_materialized_wvb_any ]).
all: assert (UPS6 : upoisoned tfibsegs W2 (ms_mem ms2) [(res, 16)])
  by (intros s Hs; transitivity (aview tfibsegs (w_H W2) mem5 s); [|exact (UPS s Hs)];
      apply AV; [exact (ush_range tfibsegs B ly2 S2 _ W2 mem5 md5 s HARU5 Hs)|];
      intros Hw; exact (fmm_pstat_not_owned B HB ly2 S2 W2 _ md5 s HAR5 (fmmC_win_inFP _ Hw)
        (proj1 (ush_facts tfibsegs B ly2 S2 _ W2 mem5 md5 s HARU5 Hs)))).
all: assert (AP : aregs_preserved regs (ms_regs ms2))
  by (rreg HS (2%bv : bv 5) Q2; rreg HS (8%bv : bv 5) Q8; rreg HS (9%bv : bv 5) Q9; rreg HS (18%bv : bv 5) Q18;
      apply (fmmC_regs regs regs5 (ms_regs ms2));
      [ replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite Q2, Usp;
        replace (spZ regs - 32 + 32) with (spZ regs) by lia; unfold spZ at 1; apply Z_to_bv_bv_unsigned
      | replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity); rewrite Q8; exact E35
      | replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity); rewrite Q9; exact E36
      | replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity); rewrite Q18; exact E37
      | intros r Hr; exact (regs_kept_of_st_ok tfibsegs E _ (restrict (w_H W2) ms2) regs5 (fmmC_extra regs live peak)
          [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS ltac:(rewrite HEE; apply env_agree_refl)
          ltac:(vm_compute; reflexivity) r Hr)
      | exact Rcs ]).
all: assert (A0 : getr (ms_regs ms2) 10 = w64 (res + 16))
  by (rreg HS (10%bv : bv 5) Q10; rewrite Q10, E9; unfold YG0d.w64; rewrite unsigned_lit_small by lia; reflexivity).
all: assert (Vh6 : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms2)) res 8 n)
  by (eapply val_mem_kept; [exact Vh|]; intros i Hi; cbn in Hi; apply AV; [lia|]; intros Hw;
      apply (blk_img tfibsegs B LAWS ly2 S2 W2 _ md5 res (n + 16) (res + i) HAR5 Hin5 ltac:(rewrite Hrq; lia));
      apply fma_in_img; exact (fmm_pstat_range _ (fmmC_win_inFP _ Hw))).
all: assert (GL6 : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms2)) G_LIVE 8 (live + n))
  by (eapply (val_mem_of_chunk8 E _ (ss_mem _) 1%nat G_LIVE (SAlu Instr.ALU_ADD (SOff 8 0) (SOff 32 0)) (live + n));
      [exact (st_ok_mem_ok E _ (w_H W2) ms2 HS) | vm_compute; reflexivity | exact DS | lia]).
all: assert (GC6 : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms2)) G_COUNT 8 (cnt + 1))
  by (eapply val_mem_kept; [exact GC|]; intros i Hi; cbn in Hi; apply AV; unfold fmmC_win, G_LIVE, G_PEAK, G_COUNT; lia).
all: assert (GF6 : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms2)) G_FAIL 8 fail)
  by (eapply val_mem_kept; [exact GF|]; intros i Hi; cbn in Hi; apply AV; unfold fmmC_win, G_LIVE, G_PEAK, G_FAIL; lia).
all: pose proof (fmm_post_close B) as FPC.
all: try specialize (FPC HB).
all: try specialize (FPC TL).
all: exact (FPC ly S W regs mem md n live peak cnt fail ly2 S2 W2 (ms_regs ms2) (ms_mem ms2) _ res
  Hcf Hn1 HnM HLn Hc33 Hlp Hp33 Hc0 Hf64 J6 UOK UPS6 Eab AP A0 Vh6 GL6 GP6 GC6 GF6).
Qed.

End c.
