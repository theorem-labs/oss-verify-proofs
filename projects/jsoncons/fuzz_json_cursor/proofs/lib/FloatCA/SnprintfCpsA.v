(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape HeapIface HeapIfaceA
  IcptIfaceA LibIface FPSteps L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibDefsA PmCurDefs PmLibSpecsA PmFloatCSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeapA CutL5A.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import MState Mem Exec Frame Cells Step Image SysStep.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import Prelim Monad SoftFloat FmtFp FmtFpDig Stdio.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import ITree.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F8 Require Import F_memset F_pad F_fmt_fp_lib FmtFpNF F_fmt_fp_nf Printf_model F_printf_iface Printf_sn F_printf_core F_vsnprintf FmtFpFactsC.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJM Require Import ShZero QcF IcptCells IcptCellsA FfpTac.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJI Require Import IcptPcomS IcptSnprintfS IcptSnprintfZ.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.FloatCA Require Import CjCpsA CjMemA NumFinalCA.
Import ListNotations.
Import ITree.Exc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition FMT_ADDR : Z := 0x26120.

Definition SN_LO_OFF : Z := PMFCA.SNPRINTF_SCR_A - 64.

Definition SNA_CELLS : list (Z * Z * Z) :=
  [ (0x153138, 8, 0x15c9b8); (0x15c9b8, 8, 0x7fff8000); (0x153140, 8, 0x15d6a8); (0x15d6a8, 8, 0); (0x153148, 8, 0x15d6b0); (0x15d6b0, 8, 0);
    (0x153150, 8, 0x15d6a0); (0x15d6a0, 8, 0x7fffffffffff);
    (0x153ca0, 8, 0x15d699); (0x15d699, 1, 1); (0x155158, 8, 0x144f04); (0x155160, 8, 0x145308); (0x15d698, 1, 1); (0x154fa0, 8, 0x137a68);
    (0x153128, 8, 0x1ee4e8); (0x154fe0, 8, 0x13c71c); (0x154fe8, 8, 0x142a1c) ].

Lemma pass1_ok_g : pass1_ok FMT_G = true. Proof. reflexivity. Qed.
Lemma fp_calls_g2 : forall prec d, (prec = 15 \/ prec = 17) ->
  fp_calls (length FMT_G) FMT_G [PA_i prec; PA_g d] = [(f128_of_d d, 1, prec, 0, CHR_g)].
Proof. intros prec d [-> | ->]; reflexivity. Qed.

Lemma printf_sn_g2 : forall d prec o l, (prec = 15 \/ prec = 17) ->
  fmt_fp' [] (f128_of_d d) 1 prec 0 CHR_g = Some (o, l) -> 0 <= l <= INT_MAX -> zlength o <= SN_CAP ->
  printf_model OUT_sn OUTFP_sn FMT_G [PA_i prec; PA_g d] [] = ITree.Ret (Ok (l, o)).
Proof.
  intros d prec o l Hp F Hl Ho.
  destruct Hp as [-> | ->];
    unfold printf_model; lhs_cbvg1;
    (pose proof (OUT_sn_eq [] [] ltac:(rewrite zlength_nil; unfold SN_CAP; lia)) as E0; msn E0; clear E0);
    unfold conv; lhs_cbvg2.
  - replace (15 <? 0) with false by reflexivity. replace ((1 <? 1) || (1048576 <=? 15))%bool with false by reflexivity.
    change CHR_g with 103 in F.
    pose proof (OUTFP_sn_eq _ _ _ _ _ _ _ _ F Ho) as E1. msn E1.
    replace ((l <? 0) || (2147483647 - 0 <? l))%bool with false by (symmetry; apply Bool.orb_false_intro; apply Z.ltb_ge; unfold INT_MAX in Hl; lia).
    rewrite mbind_mret. cbv -[Z.add]. rewrite Z.add_0_l. reflexivity.
  - replace (17 <? 0) with false by reflexivity. replace ((1 <? 1) || (1048576 <=? 17))%bool with false by reflexivity.
    change CHR_g with 103 in F.
    pose proof (OUTFP_sn_eq _ _ _ _ _ _ _ _ F Ho) as E1. msn E1.
    replace ((l <? 0) || (2147483647 - 0 <? l))%bool with false by (symmetry; apply Bool.orb_false_intro; apply Z.ltb_ge; unfold INT_MAX in Hl; lia).
    rewrite mbind_mret. cbv -[Z.add]. rewrite Z.add_0_l. reflexivity.
Qed.

Lemma fmt_g_bytes : forall m, mem_inv ASEGS m -> bytes_at ASEGS m FMT_ADDR (zb FMT_G).
Proof.
  intros m MI. unfold zb. apply fmt_bytes_at_a; [exact MI | vm_compute; reflexivity | unfold FMT_ADDR; lia | vm_compute; discriminate].
Qed.

Lemma rdn_some_of_def : forall segs (m : word -> option byte) n (a : Z), (forall i : nat, (i < n)%nat -> m (wa (a + Z.of_nat i)) <> None) ->
  exists bs, rdn segs m (wa a) n = Some bs.
Proof.
  intros segs m n. induction n as [|n IH]; intros a Hd; [exists []; reflexivity|].
  cbn [rdn]. destruct (m (wa a)) as [b|] eqn:E.
  - rewrite wa_succ. destruct (IH (a + 1)) as (bs & Hbs).
    { intros i Hi. specialize (Hd (Datatypes.S i) ltac:(lia)). replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (Datatypes.S i)) by lia. exact Hd. }
    rewrite Hbs. eexists; reflexivity.
  - exfalso. apply (Hd 0%nat ltac:(lia)). rewrite Z.add_0_r. exact E.
Qed.

Lemma same_page8 : forall x i, 0 <= x -> 0 <= i < 8 -> (x - x mod 8 + i) / 4096 = x / 4096.
Proof.
  intros x i Hx Hi.
  pose proof (Z.div_mod x 4096 ltac:(lia)) as E. pose proof (Z.mod_pos_bound x 4096 ltac:(lia)) as Hr.
  set (q := x / 4096) in *. set (r := x mod 4096) in *.
  assert (Xm : x mod 8 = r mod 8).
  { rewrite E. replace (4096 * q + r) with (r + (512 * q) * 8) by ring. apply Z_mod_plus_full. }
  pose proof (Z.div_mod r 8 ltac:(lia)) as E8. pose proof (Z.mod_pos_bound r 8 ltac:(lia)) as H8.
  set (k := r / 8) in *. set (t := r mod 8) in *.
  assert (Hk : 8 * k <= 4088) by lia.
  rewrite Xm. replace (x - t + i) with ((8 * k + i) + q * 4096) by (rewrite E, E8; ring).
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Section SnA.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (IC : PMLA.consts) (IL : icpt_layout).
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Hypothesis LY_below : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Hypothesis LY_nowrap : wx_segs_nowrap (hl_segs L).
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x6b3000.
Hypothesis ICRO : PMLA.IMG_RO_LO IC = 0x10000 /\ PMLA.IMG_RO_HI IC = 0x154000.
Hypothesis CELLS : incl SNA_CELLS (asc_cells C).
Hypothesis RTG : rt_globals IL HI.
Hypothesis ILG : In (FMT_ADDR, 6) (icl_globals IL).
Hypothesis ISH : rt_img_shadow L IL HI.
Hypothesis POI : Forall (fun r : Z * Z => 0x24080 <= fst r \/ snd r <= 0x13fc0) (icl_poison IL).
Hypothesis RSD : rt_shadow_defined HI.

Section Inst.
Variables (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : mem) (model : Model).
Hypothesis RI : ri_inv HI LB FF LK cr A M (vml_of model).
Local Notation H := (ahid A model).

Lemma wfA : CHA.wf_facts L ar LB FF LK cr A M.
Proof. exact (CHA.wf_of L ar C HI HIok LB FF LK cr A M _ RI). Qed.
Lemma rfA : CHA.rng_facts L ar LB FF.
Proof. exact (CHA.rng_of_wf _ _ _ _ _ _ _ _ wfA). Qed.

Lemma fs_above : 0x6b3000 <= ar_fs ar /\ ar_fs ar + FS_BYTES <= ahl_ceil ar /\ app_mem (ar_fs ar) FS_BYTES.
Proof.
  destruct (CHA.rf_fs _ _ _ _ rfA) as ((F0 & F1 & F2) & F3 & F4). rewrite HLlo, HLhi in F4. unfold FS_BYTES in *.
  split; [destruct F4 as [F4|F4]; lia|]. split; [exact F3|]. split; [exact F0| split; assumption].
Qed.

Lemma vis_img : forall a, 0 <= a < 0x6b3000 -> H (Z_to_bv 64 a) = false.
Proof. intros a Ha. eapply (CHA.img_vis L ar C HI HIok LY_img 32 0 ltac:(lia) LB FF LK cr A M model a RI). rewrite HLhi. exact Ha. Qed.

Lemma vis_fs : forall a, ar_fs ar <= a < ar_fs ar + FS_BYTES -> H (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. pose proof fs_above as (F0 & F1 & _). pose proof (CHA.rf_sptop _ _ _ _ rfA) as (S1 & S2). pose proof (CHA.rf_ceil _ _ _ _ rfA) as (CL & C8).
  eapply (CHA.fs_vis L ar C HI HIok 32 0 ltac:(lia) LB FF LK cr A M model a RI); [unfold FS_BYTES in *; lia | exact Ha].
Qed.

Lemma vis_stk : forall a, ahl_ceil ar <= a < 2 ^ 47 -> H (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. pose proof (CHA.rf_sptop _ _ _ _ rfA) as (S1 & S2). pose proof (CHA.rf_ceil _ _ _ _ rfA) as (CL & C8).
  eapply (CHA.client_vis L ar C HI HIok LB FF LK cr A M model 0 0 a RI); [lia | |].
  - unfold aclient, aclient_g. right; left. split; [exact Ha | lia].
  - intros (X1 & X2). exfalso. replace (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) with (2 ^ 47 - 1) in X2 by lia.
    unfold S, SB in X2. change ((2 ^ 47 - 1) / 8) with 17592186044415 in X2. lia.
Qed.

Lemma vis_stksh : forall y, S (ahl_ceil ar) <= y < S (ar_sptop ar) -> H (Z_to_bv 64 y) = false.
Proof.
  intros y Hy. pose proof (CHA.rf_sptop _ _ _ _ rfA) as (S1 & S2). pose proof (CHA.rf_ceil _ _ _ _ rfA) as (CL & C8).
  assert (T1 : ar_sptop ar / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with 17592186044416 in T1.
  assert (T0 : 0 <= ahl_ceil ar / 8) by (apply Z.div_pos; lia).
  unfold S, SB in Hy.
  eapply (CHA.client_vis L ar C HI HIok LB FF LK cr A M model 0 0 y RI); [lia | |].
  - unfold aclient, aclient_g. right; right; right; right; left. unfold in_shadow_of, S, SB. split; [lia|].
    replace (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) with (2 ^ 47 - 1) by lia. change ((2 ^ 47 - 1) / 8) with 17592186044415. lia.
  - intros _. unfold S, SB. lia.
Qed.

Lemma H_page : forall y y', 0 <= y < 2 ^ 64 -> 0 <= y' < 2 ^ 64 -> y / 4096 = y' / 4096 -> H (Z_to_bv 64 y) = H (Z_to_bv 64 y').
Proof.
  intros y y' Hy Hy' E. unfold ahid, mkH. unfold page_base, page_base_of, page_size.
  rewrite !L5.unsigned_lit by lia. rewrite E. reflexivity.
Qed.

Lemma vis_sh_allowed : forall a n y, shadow_allowed A a n -> in_shadow_of a n y -> H (Z_to_bv 64 y) = false.
Proof. intros a n y SA Hy. apply CHA.vis_allowed. exact (SA y Hy). Qed.
Lemma vis_word : forall y i, 0 <= y -> y + 8 <= 2 ^ 64 -> 0 <= i < 8 -> H (Z_to_bv 64 y) = false -> H (Z_to_bv 64 (y - y mod 8 + i)) = false.
Proof.
  intros y i Hy0 Hy1 Hi V. pose proof (Z.mod_pos_bound y 8 ltac:(lia)). pose proof (Z.div_mod y 8 ltac:(lia)).
  rewrite (H_page (y - y mod 8 + i) y); [exact V | lia | lia | apply same_page8; lia].
Qed.

Local Notation m0 := (mrestrict H M).

Lemma img_clear_m0 : PMLA.img_ro IC M -> L5.img_clear m0 0x10000 0x154000.
Proof.
  intros IMG i Hi. unfold mrestrict. destruct (H (Z_to_bv 64 i)); [reflexivity|].
  unfold PMLA.img_ro, L5.img_clear in IMG. destruct ICRO as [E1 E2]. rewrite E1, E2 in IMG. apply IMG. lia.
Qed.
Lemma mem_inv_m0 : PMLA.img_ro IC M -> mem_inv ASEGS m0.
Proof. intros IMG. apply mem_inv_of_clear_a. intros i Hi. apply (img_clear_m0 IMG). lia. Qed.

Lemma SNA_rng : forall a n v, In (a, n, v) SNA_CELLS -> 0x153040 <= a /\ a + n <= 0x160040 /\ 0 <= n /\ 0 <= v < 2 ^ 64.
Proof. intros a n v Hin. unfold SNA_CELLS in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; lia|]). destruct Hin. Qed.

Lemma cell_m0_a : forall a (n : nat) v w, In (a, Z.of_nat n, v) SNA_CELLS -> w = Z_to_bv 64 a ->
  rdn ASEGS m0 w n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Proof.
  intros a n v w Hin ->.
  pose proof (PmHeapIfaceA.aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ RI) as (_ & ST).
  rewrite Forall_forall in ST. specialize (ST _ (CELLS _ Hin)). cbn [fst snd] in ST. unfold cell_is in ST. rewrite HLsegs, Nat2Z.id in ST.
  destruct (SNA_rng _ _ _ Hin) as (R1 & R2 & R3 & R4).
  rewrite (CL5A.rdn_vis ASEGS H M a n); [exact ST | lia | lia | intros i Hi; apply vis_img; lia].
Qed.

Lemma cell_m0 : forall (n : nat) v w, In (bv_unsigned w, Z.of_nat n, v) SNA_CELLS -> rdn ASEGS m0 w n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Proof. intros n v w Hin. apply (cell_m0_a (bv_unsigned w) n v w Hin). symmetry. apply Z_to_bv_bv_unsigned. Qed.

Ltac sna_in := unfold SNA_CELLS; cbn [In Z.of_nat Pos.of_succ_nat Pos.succ];
  repeat (first [ left; unfold Pm8RegionPoisoned.SB, Pm8RegionPoisoned.HIGHEND; reflexivity | right ]).
Ltac cell_solve := apply cell_m0; sna_in.

Lemma aenv_m0 : IcptCells.aenv m0.
Proof.
  unfold IcptCells.aenv, Pm8RegionPoisoned.rt_layout_globs, Pm8AsanMemcpy.mc_icpt_globs, Pm8AsanMemset.ms_icpt_globs, IcptCells.ai_byte, IcptCells.fx_got.
  change Asan.M.loaded_segments with ASEGS.
  assert (B1 : word_to_le_bytes 1 (Z_to_bv 64 1) = [Z_to_bv 8 1]) by (apply CL5A.bytes1; lia).
  repeat split; first [ cell_solve | rewrite <- B1; cell_solve ].
Qed.

Lemma icpt_cells_m0 : icpt_cells m0.
Proof. unfold icpt_cells. change F_memset.rsegs with ASEGS. repeat split; cell_solve. Qed.

Lemma stk_m0 : forall sp scr lo, CHA.astk ar M sp scr -> sp - scr <= lo <= sp -> stk ASEGS m0 lo sp.
Proof.
  intros sp scr lo (S16 & S1 & S2 & S3 & SD & _) Hlo. pose proof (CHA.rf_ceil _ _ _ _ rfA) as (CL & C8).
  apply stk_of_defined_g; [| lia | lia].
  apply CL5A.defined_vis.
  - intros i Hi. apply vis_stk. lia.
  - intros i Hi. replace (lo + i) with (sp - scr + (lo - (sp - scr) + i)) by ring. apply SD. lia.
Qed.

Lemma buf_vis : forall buf n, CL5A.ainfr FF buf n -> 0 < n -> CL5A.visr H buf n.
Proof.
  intros buf n HF Hn i Hi. destruct (CL5A.infr_rng L ar LB FF buf n rfA HF Hn) as (R1 & R2 & _). apply vis_fs. unfold FS_BYTES in *; lia.
Qed.
Lemma buf_cells : forall buf, CL5A.ainfr FF buf 100 -> L5.defined M buf 100 -> rw_cells ASEGS m0 buf [CB 100 (ovl_bytes m0 buf 100)].
Proof.
  intros buf HF D. destruct (CL5A.infr_rng L ar LB FF buf 100 rfA HF ltac:(lia)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  apply defined_rw_cells_g; [| lia | lia]. apply CL5A.defined_vis; [apply buf_vis; [exact HF | lia] | exact D].
Qed.

Lemma ssp_m0 : PMLA.img_ro IC M -> ssp_cells m0 (le_bytes_to_word (guard_bytes_a m0)).
Proof. intros IMG. unfold ssp_cells, got_ssp, ssp_guard. exact (ssp_cells_a m0 (img_clear_m0 IMG)). Qed.

Lemma zsh_stk : forall sp, CHA.astk ar M sp PMFCA.SNPRINTF_SCR_A -> PMSA.stksh ar M sp PMFCA.SNPRINTF_SCR_A ->
  ShZero.zsh m0 (sp - SN_LO_OFF) (sp - 2256).
Proof.
  intros sp (S16 & S1 & S2 & S3 & SD & _) SH. unfold PMSA.stksh, PMLA.stksh, shadow_zero in SH.
  pose proof (CHA.rf_ceil _ _ _ _ rfA) as (CL & C8). pose proof (CHA.rf_sptop _ _ _ _ rfA) as (T1 & T2).
  unfold ShZero.zsh, ShZero.shw_lo, ShZero.shw_hi, ShZero.SBZ, SN_LO_OFF, PMFCA.SNPRINTF_SCR_A in *. intros y Hy.
  pose proof (Z.div_mod sp 16 ltac:(lia)) as Dk. rewrite S16, Z.add_0_r in Dk.
  pose proof (Z.div_mod (ar_sptop ar) 16 ltac:(lia)) as Dj. rewrite T2, Z.add_0_r in Dj.
  assert (E1 : (sp - 12288) / 8 = 2 * (sp / 16) - 1536).
  { symmetry. apply (Z.div_unique _ 8 _ 0); [lia|]. rewrite Dk at 1. ring. }
  assert (E0 : (sp - (12288 - 64)) / 8 = 2 * (sp / 16) - 1528).
  { symmetry. apply (Z.div_unique _ 8 _ 0); [lia|]. rewrite Dk at 1. ring. }
  assert (E2 : (sp - 2256) / 8 = 2 * (sp / 16) - 282).
  { symmetry. apply (Z.div_unique _ 8 _ 0); [lia|]. rewrite Dk at 1. ring. }
  assert (E4 : ar_sptop ar / 8 = 2 * (ar_sptop ar / 16)).
  { symmetry. apply (Z.div_unique _ 8 _ 0); [lia|]. rewrite Dj at 1. ring. }
  assert (E3 : 1536 <= (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 12288)) / 8).
  { change 1536 with (12288 / 8). apply Z.div_le_mono; lia. }
  assert (Ec : ahl_ceil ar / 8 <= (sp - 12288) / 8) by (apply Z.div_le_mono; lia).
  change (wa y) with (Z_to_bv 64 y).
  rewrite L5LZ.mrestrict_visible' by (apply vis_stksh; unfold S, SB; lia).
  specialize (SH (y - S (sp - 12288)) ltac:(unfold S, SB; lia)). unfold byte_at in SH.
  replace (S (sp - 12288) + (y - S (sp - 12288))) with y in SH by ring. exact SH.
Qed.

Lemma zsh_ro : ShZero.zsh m0 FfpTac.RODATA_LO FfpTac.RODATA_HI.
Proof.
  destruct (ISH _ _ _ _ _ _ _ RI 0x13fc0 0x100c0) as (Z0 & SA); [rewrite HLlo; lia | rewrite HLhi; lia | lia | |].
  - eapply Forall_impl; [|exact POI]. intros r Hr. cbn in Hr |- *. lia.
  - unfold ShZero.zsh, ShZero.shw_lo, ShZero.shw_hi, ShZero.SBZ, FfpTac.RODATA_LO, FfpTac.RODATA_HI. intros y Hy.
    change (0x14000 / 8) with 0x2800 in Hy. change (0x24000 / 8) with 0x4800 in Hy.
    assert (IS : in_shadow_of 0x13fc0 0x100c0 y).
    { unfold in_shadow_of, S, SB. change (0x13fc0 / 8) with 0x27f8. change ((0x13fc0 + 0x100c0 - 1) / 8) with 0x480f. lia. }
    change (wa y) with (Z_to_bv 64 y). rewrite L5LZ.mrestrict_visible' by exact (vis_sh_allowed _ _ _ SA IS). exact (Z0 y IS).
Qed.

Lemma shword_m0 : forall y, ((LOWSH_LO <= y - y mod 8 /\ y - y mod 8 + 8 <= LOWSH_HI) \/ (HIGHSH_LO <= y - y mod 8 /\ y - y mod 8 + 8 <= HIGHSH_HI)) ->
  H (Z_to_bv 64 y) = false -> exists w, rdn ASEGS m0 (Z_to_bv 64 (y - y mod 8)) 8 = Some w.
Proof.
  intros y Hy V. pose proof (Z.mod_pos_bound y 8 ltac:(lia)) as My.
  assert (Y0 : 0 <= y) by (unfold LOWSH_LO, LOWSH_HI, HIGHSH_LO, HIGHSH_HI in Hy; lia).
  assert (Y1 : y + 8 <= 2 ^ 64) by (unfold LOWSH_LO, LOWSH_HI, HIGHSH_LO, HIGHSH_HI in Hy; lia).
  change (Z_to_bv 64 (y - y mod 8)) with (wa (y - y mod 8)). apply rdn_some_of_def. intros i Hi. unfold wa.
  rewrite L5LZ.mrestrict_visible' by (apply vis_word; [lia | lia | lia | exact V]).
  apply (RSD _ _ _ _ _ _ _ RI). unfold LOWSH_LO, LOWSH_HI, HIGHSH_LO, HIGHSH_HI in *. lia.
Qed.

Lemma fmtq_m0 : fmtq m0 FMT_ADDR FMT_G.
Proof.
  pose proof (RTG _ _ _ _ _ _ _ RI) as G. rewrite Forall_forall in G. destruct (G _ ILG) as ((_ & BY) & SA). cbn [fst snd] in BY, SA.
  specialize (BY ltac:(discriminate)). change (6 / 8) with 0 in BY. change (6 mod 8) with 6 in BY.
  unfold byte_at, S, SB, FMT_ADDR in BY. change (0x26120 / 8 + 0x7fff8000 + 0) with 0x7fffcc24 in BY.
  assert (IS : in_shadow_of FMT_ADDR 6 0x7fffcc24) by (unfold in_shadow_of, FMT_ADDR, S, SB; change (0x26120 / 8) with 0x4c24; change ((0x26120 + 6 - 1) / 8) with 0x4c24; lia).
  assert (V : H (Z_to_bv 64 0x7fffcc24) = false) by exact (vis_sh_allowed _ _ _ SA IS).
  unfold fmtq. intros i n Hi Hn Hin. change (zlength FMT_G) with 6 in Hin.
  unfold QcF.shk. intros _. unfold Pm8RegionPoisoned.SB, FMT_ADDR.
  assert (E1 : (0x26120 + i) / 8 = 0x4c24) by (symmetry; apply (Z.div_unique _ 8 _ i); lia).
  assert (E2 : (0x26120 + i + n - 1) / 8 = 0x4c24) by (symmetry; apply (Z.div_unique _ 8 _ (i + n - 1)); lia).
  rewrite E1, E2. change (0x7fff8000 + 0x4c24) with 0x7fffcc24.
  split; [|split].
  - intros x Hx. lia.
  - exists 6. split; [rewrite L5LZ.mrestrict_visible' by exact V; exact BY |].
    pose proof (Z.div_mod (0x26120 + i + n - 1) 8 ltac:(lia)) as D. rewrite E2 in D. right. lia.
  - intros _. destruct (shword_m0 0x7fffcc24) as (w & Hw); [unfold LOWSH_LO, LOWSH_HI; change (0x7fffcc24 mod 8) with 4; lia | exact V |].
    exists w, w. split; exact Hw.
Qed.

Lemma shz_buf : forall buf N, CL5A.ainfr FF buf 100 -> aacc M buf 100 -> 1 <= N <= 26 -> ShZero.shz ASEGS m0 buf N.
Proof.
  intros buf N HF AC HN. destruct (CL5A.infr_rng L ar LB FF buf 100 rfA HF ltac:(lia)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  pose proof fs_above as (F0 & F1 & F2). pose proof (CHA.wf_fs_sh _ _ _ _ _ _ _ _ wfA) as FSH.
  pose proof (CHA.rf_sptop _ _ _ _ rfA) as (T1 & T2).
  pose proof (Z.div_mod buf 8 ltac:(lia)) as Db. pose proof (Z.mod_pos_bound buf 8 ltac:(lia)) as Mb.
  pose proof (Z.div_mod (buf + N - 1) 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound (buf + N - 1) 8 ltac:(lia)) as Mn.
  assert (G : forall x, 0x7fff8000 + buf / 8 <= x <= 0x7fff8000 + (buf + N - 1) / 8 ->
                mrestrict H M (Z_to_bv 64 x) = Some (Z_to_bv 8 0) /\ H (Z_to_bv 64 x) = false).
  { intros x Hx. set (a := 8 * (x - 0x7fff8000) + 7).
    assert (Ha : buf <= a < buf + 100) by (unfold a; lia).
    assert (Sa : S a = x).
    { unfold S, SB, a. replace (8 * (x - 0x7fff8000) + 7) with (7 + (x - 0x7fff8000) * 8) by ring. rewrite Z.div_add by lia. change (7 / 8) with 0. ring. }
    assert (IS : in_shadow_of (ar_fs ar) FS_BYTES x).
    { unfold in_shadow_of. rewrite <- Sa. unfold S. unfold FS_BYTES in *.
      split; apply Z.add_le_mono_r; apply Z.div_le_mono; lia. }
    assert (V : H (Z_to_bv 64 x) = false) by exact (vis_sh_allowed _ _ _ FSH IS).
    split; [|exact V]. rewrite L5LZ.mrestrict_visible' by exact V.
    destruct (AC a Ha) as [Z0 | (v & Bv & Hv & Hm)]; [unfold byte_at in Z0; rewrite <- Sa; exact Z0|].
    exfalso. assert (A7 : a mod 8 = 7).
    { unfold a. replace (8 * (x - 0x7fff8000) + 7) with (7 + (x - 0x7fff8000) * 8) by ring. rewrite Z_mod_plus_full. reflexivity. }
    lia. }
  unfold ShZero.shz. intros _. unfold Pm8RegionPoisoned.SB. split; [|split].
  - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x). apply G. lia.
  - apply G. lia.
  - intros _.
    assert (W : forall y, 0x7fff8000 + buf / 8 <= y <= 0x7fff8000 + (buf + N - 1) / 8 -> exists w, rdn ASEGS m0 (Z_to_bv 64 (y - y mod 8)) 8 = Some w).
    assert (B1 : buf / 8 <= 0x7fff7000 / 8 \/ 0x10007fff8000 / 8 <= buf / 8).
    { destruct R5 as [R5|R5]; [left | right]; apply Z.div_le_mono; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia. }
    assert (B2 : (buf + N - 1) / 8 <= 0x7fff7000 / 8 \/ 0x10007fff8000 / 8 <= (buf + N - 1) / 8).
    { destruct R5 as [R5|R5]; [left | right]; apply Z.div_le_mono; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia. }
    assert (B3 : (buf + N - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
    assert (B4 : 0 <= buf / 8) by (apply Z.div_pos; lia).
    assert (B5 : buf / 8 <= (buf + N - 1) / 8) by (apply Z.div_le_mono; lia).
    change (0x7fff7000 / 8) with 0xfffee00 in B1, B2. change (0x10007fff8000 / 8) with 0x2000ffff000 in B1, B2. change ((2 ^ 47 - 1) / 8) with 0xfffffffffff in B3.
    { intros y Hy. apply shword_m0; [| exact (proj2 (G y Hy))].
      pose proof (Z.mod_pos_bound y 8 ltac:(lia)). pose proof (Z.div_mod y 8 ltac:(lia)).
      unfold BIGSHADOW_LO, BIGSHADOW_HI, LOWSH_LO, LOWSH_HI, HIGHSH_LO, HIGHSH_HI in *.
      destruct R5 as [R5|R5]; [left | right]; lia. }
    destruct (W (0x7fff8000 + buf / 8)) as (w0 & H0); [lia|]. destruct (W (0x7fff8000 + (buf + N - 1) / 8)) as (w1 & H1); [lia|].
    exists w0, w1. split; assumption.
Qed.

Lemma app_buf : forall buf, CL5A.ainfr FF buf 100 -> 0x160040 <= buf /\ ShZero.app buf (Z.of_nat 100).
Proof.
  intros buf HF. destruct (CL5A.infr_rng L ar LB FF buf 100 rfA HF ltac:(lia)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  pose proof fs_above as (F0 & F1 & (A0 & A1 & A2)). pose proof (CHA.rf_sptop _ _ _ _ rfA) as (T1 & T2).
  unfold ShZero.app, BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *. cbn [Z.of_nat Pos.of_succ_nat].
  split; [lia|]. destruct R5 as [R5|R5]; [left | right]; lia.
Qed.

Section Post.
Variables (sp scr lo buf : Z) (m' : mem).
Hypothesis ASTK : CHA.astk ar M sp scr.
Hypothesis LOr : sp - scr <= lo <= sp.
Hypothesis HIF : CL5A.ainfr FF buf 100.
Hypothesis MU : munch [(lo, sp); (buf, buf + 100)] m0 m'.
Hypothesis WM : wmono ASEGS m0 m'.
Local Notation M' := (munrestrict H M m').

Lemma post_rng : 0x6b3000 <= buf /\ buf + 100 <= ahl_ceil ar /\ ahl_ceil ar + 4096 <= sp - scr /\ sp <= 2 ^ 47 /\ 0 <= scr.
Proof.
  destruct (CL5A.infr_rng L ar LB FF buf 100 rfA HIF ltac:(lia)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  pose proof fs_above as (F0 & F1 & F2). destruct ASTK as (S16 & S1 & S2 & S3 & _). pose proof (CHA.rf_sptop _ _ _ _ rfA) as (T1 & T2).
  unfold FS_BYTES in *. repeat split; lia.
Qed.

Lemma post_keep : forall x : word, outside [(lo, sp); (buf, buf + 100)] (bv_unsigned x) -> M' x = M x.
Proof.
  intros x Hx. unfold munrestrict. destruct (H x) eqn:E; [reflexivity|]. rewrite (MU x Hx). unfold mrestrict. rewrite E. reflexivity.
Qed.

Lemma post_vis_written : forall a, lo <= a < sp \/ buf <= a < buf + 100 -> H (Z_to_bv 64 a) = false.
Proof.
  pose proof post_rng as (P1 & P2 & P3 & P4 & P5). pose proof fs_above as (F0 & F1 & F2).
  destruct (CL5A.infr_rng L ar LB FF buf 100 rfA HIF ltac:(lia)) as (R1 & R2 & _).
  intros a [Ha|Ha]; [apply vis_stk; lia | apply vis_fs; unfold FS_BYTES in *; lia].
Qed.

Lemma post_def : forall x : word, M x <> None -> M' x <> None.
Proof.
  intros x Hx. pose proof post_rng as (P1 & P2 & P3 & P4 & P5). pose proof (bv_unsigned_in_range _ x) as Rx. unfold bv_modulus in Rx.
  unfold munrestrict. destruct (H x) eqn:E; [exact Hx|].
  assert (M0x : m0 x = M x) by (unfold mrestrict; rewrite E; reflexivity).
  destruct (Z_le_gt_dec lo (bv_unsigned x)) as [X1|X1]; [destruct (Z_lt_ge_dec (bv_unsigned x) sp) as [X2|X2]|].
  -
    assert (W0 : wview ASEGS m0 x <> None) by (rewrite wview_off_image_a by lia; rewrite M0x; exact Hx).
    pose proof (WM x W0) as W1. rewrite wview_off_image_a in W1 by lia. exact W1.
  - destruct (Z_le_gt_dec buf (bv_unsigned x)) as [Y1|Y1]; [destruct (Z_lt_ge_dec (bv_unsigned x) (buf + 100)) as [Y2|Y2]|].
    + assert (W0 : wview ASEGS m0 x <> None) by (rewrite wview_off_image_a by lia; rewrite M0x; exact Hx).
      pose proof (WM x W0) as W1. rewrite wview_off_image_a in W1 by lia. exact W1.
    + rewrite (MU x) by (cbn [outside]; repeat split; lia). rewrite M0x. exact Hx.
    + rewrite (MU x) by (cbn [outside]; repeat split; lia). rewrite M0x. exact Hx.
  - destruct (Z_le_gt_dec buf (bv_unsigned x)) as [Y1|Y1]; [destruct (Z_lt_ge_dec (bv_unsigned x) (buf + 100)) as [Y2|Y2]|].
    + assert (W0 : wview ASEGS m0 x <> None) by (rewrite wview_off_image_a by lia; rewrite M0x; exact Hx).
      pose proof (WM x W0) as W1. rewrite wview_off_image_a in W1 by lia. exact W1.
    + rewrite (MU x) by (cbn [outside]; repeat split; lia). rewrite M0x. exact Hx.
    + rewrite (MU x) by (cbn [outside]; repeat split; lia). rewrite M0x. exact Hx.
Qed.

Lemma post_written_clientw : forall a, lo <= a < sp \/ buf <= a < buf + 100 -> aclientw L ar LB FF 0 0 a.
Proof.
  pose proof post_rng as (P1 & P2 & P3 & P4 & P5).
  intros a [Ha|Ha].
  - unfold aclientw, aclient_g. right; left. split; lia.
  - exact (CL5A.infr_clientw L ar LB FF 0 0 buf 100 a HIF Ha).
Qed.

Lemma post_private : forall a, 0 <= a < 2 ^ 64 -> art_private L ar LB FF a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros a Ha P. apply post_keep. rewrite L5.unsigned_lit by lia. cbn [outside].
  split; [|split; [|exact I]]; intros X;
    [ exact (CHA.aclientw_not_private L ar LY_img LY_ro LB FF LK cr A M 0 0 a wfA (post_written_clientw a (or_introl X)) P)
    | exact (CHA.aclientw_not_private L ar LY_img LY_ro LB FF LK cr A M 0 0 a wfA (post_written_clientw a (or_intror X)) P) ].
Qed.

Lemma post_ri : ri_inv HI LB FF LK cr A M' (vml_of model).
Proof. exact (PmHeapIfaceA.aio_frame _ _ _ _ _ HIok _ _ _ _ _ M _ _ RI post_private post_def). Qed.

Lemma post_scratch_not_client : forall a, sp - scr <= a < sp -> ~ aclient L ar LB FF sp scr a.
Proof.
  pose proof post_rng as (P1 & P2 & P3 & P4 & P5). pose proof (CHA.rf_sptop _ _ _ _ rfA) as (T1 & T2).
  intros a Ha Hc. destruct LY_img as (I0 & I1). rewrite HLhi in I1.
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - destruct Hc as (b & Hb & X). destruct (CHA.rf_blk _ _ _ _ rfA b Hb) as (B0 & B1 & B2 & B3 & B4 & _). lia.
  - lia.
  - rewrite HLhi in Hc. unfold BIGSHADOW_LO in *. lia.
  - destruct Hc as (f & Hf & X). destruct (CHA.rf_frm _ _ _ _ rfA f Hf) as (F1 & F2 & _). pose proof fs_above as (G0 & G1 & _).
    unfold FS_BYTES in *. lia.
  - pose proof (CHA.shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(lia) ltac:(lia) ltac:(lia) Hc). unfold BIGSHADOW_HI in *. lia.
  - destruct Hc as (f & Hf & X). destruct (CHA.rf_frm _ _ _ _ rfA f Hf) as (F1 & F2 & G1 & G2 & G3). pose proof fs_above as (G0 & G4 & _).
    unfold FS_BYTES in *. pose proof (CHA.shadow_range (ff_addr f) (ff_bytes (ff_class f)) a ltac:(lia) ltac:(lia) ltac:(lia) X). unfold BIGSHADOW_HI in *. lia.
  - destruct Hc as (b & Hb & X). destruct (CHA.rf_blk _ _ _ _ rfA b Hb) as (B0 & B1 & B2 & B3 & B4 & B5).
    pose proof (CHA.shadow_range (fst b) (snd b) a ltac:(lia) B3 ltac:(destruct B5 as (_ & _ & B6); lia) X). unfold BIGSHADOW_HI in *. lia.
Qed.

Lemma post_ahpres : stk ASEGS m' lo sp -> CHA.ahpres L ar LB FF sp scr [(buf, 100)] M M'.
Proof.
  intros STK'. pose proof post_rng as (P1 & P2 & P3 & P4 & P5). split; [|split].
  - intros a (Ha & Hc & Ho). apply post_keep. rewrite L5.unsigned_lit by lia. cbn [outside]. split; [|split; [|exact I]].
    + intros X. exact (post_scratch_not_client a ltac:(lia) Hc).
    + intros X. apply (Ho (buf, 100)); [left; reflexivity | unfold L5.in_rng; cbn; lia].
  - intros i Hi. destruct ASTK as (S16 & S1 & S2 & S3 & SD & _).
    destruct (Z_lt_ge_dec (sp - scr + i) lo) as [X|X].
    + rewrite post_keep by (rewrite L5.unsigned_lit by lia; cbn [outside]; split; [lia | split; [lia | exact I]]). apply SD. lia.
    + unfold munrestrict. rewrite (post_vis_written (sp - scr + i) ltac:(left; lia)).
      destruct STK' as (_ & _ & SK). destruct (SK (sp - scr + i) ltac:(lia)) as (W0 & _).
      change (wa (sp - scr + i)) with (Z_to_bv 64 (sp - scr + i)) in W0. rewrite wview_off_image_a in W0 by (rewrite L5.unsigned_lit by lia; lia). exact W0.
  - intros a Ha Hc Hd. apply post_def. exact Hd.
Qed.

Lemma post_out : forall (o : list Z) (junk : list byte), rw_cells ASEGS m' buf [CB 100 (zb o ++ Z_to_bv 8 0 :: skipn (Datatypes.S (length o)) junk)] ->
  (length o < 100)%nat ->
  L5.bytes_at ASEGS M' buf o /\ L5.u8_at ASEGS M' (buf + Z.of_nat (length o)) 0 /\ L5.defined M' buf 100.
Proof.
  intros o junk ((_ & BA) & WR) Lo. pose proof post_rng as (P1 & P2 & P3 & P4 & P5). cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
  assert (EQ : forall i, buf <= i < buf + 100 -> M' (Z_to_bv 64 i) = m' (Z_to_bv 64 i)).
  { intros i Hi. unfold munrestrict. rewrite (post_vis_written i ltac:(right; lia)). reflexivity. }
  split; [|split].
  - apply (CL5A.bytes_same ASEGS m' M' buf o); [lia | lia | intros i Hi; apply EQ; lia |].
    eapply bytes_at_L5_g. unfold zb in BA. exact BA.
  - apply (CL5A.u8_same ASEGS m' M'); [lia | lia | apply EQ; lia |].
    unfold L5.u8_at. destruct BA as (_ & _ & HB).
    assert (Hi : (length o < length (zb o ++ Z_to_bv 8 0 :: skipn (Datatypes.S (length o)) junk))%nat)
      by (unfold zb; rewrite length_app, length_map; cbn [length]; lia).
    pose proof (HB (length o) Hi) as E. rewrite nth_error_app2 in E by (unfold zb; rewrite length_map; lia).
    unfold zb in E. rewrite length_map, Nat.sub_diag in E. cbn [nth_error] in E.
    rewrite rdn_unfold. change (Z_to_bv 64 (buf + Z.of_nat (length o))) with (wa (buf + Z.of_nat (length o))).
    rewrite E. rewrite rdn_unfold. reflexivity.
  - destruct WR as (_ & _ & HW). intros i Hi. rewrite EQ by lia. specialize (HW i ltac:(cbn; lia)).
    change (wa (buf + i)) with (Z_to_bv 64 (buf + i)) in HW. rewrite wview_off_image_a in HW by (rewrite L5.unsigned_lit by lia; lia). exact HW.
Qed.
End Post.
End Inst.

Theorem snprintf_g_okA : PMFCA.snprintf_g_specA L ar HI IC PMFCA.PC_SNPRINTF_casan FMT_ADDR.
Proof.
  unfold PMFCA.snprintf_g_specA, PMSA.cps_asan, PMSA.cfg.
  intros LB FF LK cr A buf p v sp r fx R M model K RI AMOK HK FPOK RA RAOK SPr TPr ASTK FFR FFRS PRE CONT.
  destruct PRE as (A0 & A1 & A2 & A3 & Hp & A4 & Hv & IMG & STKSH & DEF & INFR & ACC).
  destruct AMOK as (Hh & HMI).
  destruct (fmt_fp'_g_total v p Hp) as (o & l & FM & El & Lo & FACTS & FINE & NFE).
  rewrite El in FM.
  assert (LOr : sp - PMFCA.SNPRINTF_SCR_A <= sp - SN_LO_OFF <= sp) by (unfold SN_LO_OFF, PMFCA.SNPRINTF_SCR_A; lia).
  pose proof (post_rng LB FF LK cr A M model RI sp PMFCA.SNPRINTF_SCR_A (sp - SN_LO_OFF) buf ASTK LOr INFR) as (P1 & P2 & P3 & P4 & P5).
  pose proof ASTK as (S16 & S1 & S2 & S3 & SD & _).
  pose proof (CHA.rf_ceil _ _ _ _ (rfA LB FF LK cr A M model RI)) as (CL & C8).
  assert (Esp : bv_unsigned (getr R 2) = sp) by (rewrite SPr; apply L5.unsigned_lit; lia).
  unfold PMFCA.SNPRINTF_SCR_A in P3.
  pose proof (app_buf LB FF LK cr A M model RI buf INFR) as APP.
  rewrite HLsegs in CONT |- *.
  assert (HOFF : H_off_segments ASEGS (ahid A model)) by (rewrite <- HLsegs; exact (CHA.vis_off_segments L ar C HI HIok LY_below LB FF LK cr A M model RI)).
  assert (HWX : wx_segs_nowrap ASEGS) by (rewrite <- HLsegs; exact LY_nowrap).
  eapply (cj_evt_srzA ASEGS SCFG (ahid A model) HOFF HWX R (Z_to_bv 64 PMFCA.PC_SNPRINTF_casan) M (seg_rom ASEGS) A model K).
  - exact (L5LZ.lazy_cover_ahid A model).
  - exact (proj1 (PmHeapIfaceA.aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ RI)).
  - exact HMI.
  - exact Hh.
  -
    unfold canon_regs, PMFCA.PC_SNPRINTF_casan.
    eapply (snprintf_icpt_ok (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9)
             (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16) (getr R 17) (getr R 18) (getr R 19)
             (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29)
             (getr R 30) (getr R 31) fp_regs fp_csr (mrestrict (ahid A model) M)
             buf 100 FMT_ADDR 100%nat (ovl_bytes (mrestrict (ahid A model) M) buf 100) [PA_i p; PA_g v]
             (sp - SN_LO_OFF) (le_bytes_to_word (guard_bytes_a (mrestrict (ahid A model) M))) (zlength o) o); rewrite ?Esp.
    + exact A0.
    + exact A1.
    + exact A2.
    + exact (buf_cells LB FF LK cr A M model RI buf INFR DEF).
    + exact (fmt_g_bytes _ (mem_inv_m0 A M model IMG)).
    + constructor; [exact I | constructor; [exact I | constructor]].
    + cbn [args_ok arg_ok]. split; [split; [destruct Hp as [-> | ->]; lia | rewrite A3, L5.unsigned_lit by (destruct Hp as [-> | ->]; lia); reflexivity]|].
      split; [rewrite A4, L5.unsigned_lit by lia; reflexivity | exact I].
    + apply printf_sn_g2; [exact Hp | exact FM | unfold INT_MAX, zlength in *; lia | unfold SN_CAP, zlength in *; lia].
    + rewrite fp_calls_g2 by exact Hp. constructor; [exact FACTS | constructor].
    + reflexivity.
    + unfold zlength in *; lia.
    + unfold zlength in *; lia.
    + unfold zlength in *; lia.
    + lia.
    + exact (stk_m0 LB FF LK cr A M model RI sp PMFCA.SNPRINTF_SCR_A (sp - SN_LO_OFF) ASTK ltac:(unfold SN_LO_OFF, PMFCA.SNPRINTF_SCR_A; lia)).
    + unfold SN_LO_OFF, PMFCA.SNPRINTF_SCR_A, SNI_DEPTH. lia.
    + unfold SN_LO_OFF, PMFCA.SNPRINTF_SCR_A, GLOBALS_TOP. lia.
    + lia.
    + exact (ssp_m0 A M model IMG).
    + exact (mem_inv_m0 A M model IMG).
    + exact FPOK.
    + unfold FMT_ADDR. lia.
    + unfold FMT_ADDR, STATIC_SPLIT. lia.
    + left. unfold SN_LO_OFF, PMFCA.SNPRINTF_SCR_A. cbn [Z.of_nat Pos.of_succ_nat]. lia.
    + right. unfold GLOBALS_TOP. lia.
    + exact (aenv_m0 LB FF LK cr A M model RI).
    + exact (zsh_stk LB FF LK cr A M model RI sp ASTK STKSH).
    + exact (zsh_ro LB FF LK cr A M model RI).
    + unfold SN_LO_OFF, PMFCA.SNPRINTF_SCR_A. lia.
    + lia.
    + exact (fmtq_m0 LB FF LK cr A M model RI).
    + apply (shz_buf LB FF LK cr A M model RI buf (zlength o) INFR ACC). unfold zlength in *; lia.
    + apply QcF.shk_of_shz. apply (shz_buf LB FF LK cr A M model RI buf (zlength o + 1) INFR ACC). unfold zlength in *; lia.
    + exact APP.
    + exact (icpt_cells_m0 LB FF LK cr A M model RI).
  -
    intros ms1 ms1' POST EQV model' HMI' SBM HC.
    unfold vsnprintf_post in POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' & E1 & MU & WM & MI' & FRM' & FPR & ST' & SSP' & DST').
    subst ms1.
    destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems REQ].
    rewrite Ems. set (R' := ms_regs ms1') in *.
    rewrite Esp in MU, ST'. change (buf + Z.of_nat 100) with (buf + 100) in MU.
    replace (ret_pc (getr R 1)) with (Z_to_bv 64 r) by (rewrite RA; symmetry; apply ret_pc_even; unfold L5.ra_ok in RAOK; lia).
    change (unrestrict (ahid A model) M (MS R' Ft (Z_to_bv 64 r) fc' None m' (seg_rom rsegs)))
      with (@mkst (mkFP Ft fc') R' (Z_to_bv 64 r) (munrestrict (ahid A model) M m') (seg_rom ASEGS)).
    destruct (post_out LB FF LK cr A M model RI sp PMFCA.SNPRINTF_SCR_A (sp - SN_LO_OFF) buf m' ASTK LOr INFR o
                (ovl_bytes (mrestrict (ahid A model) M) buf 100) DST' ltac:(unfold zlength in *; lia)) as (BO & U8 & DF).
    apply (CONT (mkFP Ft fc') R' (munrestrict (ahid A model) M m') model' LB cr LB [(buf, 100)] LK A).
    + exact FRM'.
    + split; [|repeat split].
      exists o. split.
      { unfold PMFCA.gtext. destruct (dfin_dec v) as [Hfin|Hnf]; [left; exact (numf_proof v p o l Hp Hfin (FINE Hfin)) | right; exact (NFE Hnf)]. }
      split; [unfold zlength in Lo; lia|].
      split. { unfold PMSA.a0. rewrite <- (getr_eqv _ _ _ REQ). unfold getr; cbn. reflexivity. }
      split; [exact BO|]. split; [unfold PMSA.u8; rewrite HLsegs; exact U8 | exact DF].
    + intros rr Hrr. rewrite <- (getr_eqv _ _ rr REQ).
      assert (Er : exists k, In k callee_saved_idx /\ rr = Z_to_bv 5 k).
      { exists (bv_unsigned rr). split; [exact Hrr| symmetry; apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range]. }
      destruct Er as (k & Hk & ->). unfold callee_saved_idx in Hk. cbn [In] in Hk.
      repeat (destruct Hk as [<-|Hk]; [unfold getr; cbn; reflexivity|]). destruct Hk.
    + exact (post_ahpres LB FF LK cr A M model RI sp PMFCA.SNPRINTF_SCR_A (sp - SN_LO_OFF) buf m' ASTK LOr INFR MU WM ST').
    + exact (L5LZ.sbm_model_rt _ _ SBM).
    + apply incl_refl.
    + split; [rewrite (L5LZ.sbm_halted _ _ SBM); exact Hh | exact HMI'].
    + apply incl_refl.
    + replace (vml_of model') with (vml_of model) by (unfold vml_of; rewrite (L5LZ.sbm_vmmaps _ _ SBM), (L5LZ.sbm_lazy _ _ SBM); reflexivity).
      exact (post_ri LB FF LK cr A M model RI sp PMFCA.SNPRINTF_SCR_A (sp - SN_LO_OFF) buf m' ASTK LOr INFR MU WM).
Qed.
End SnA.
