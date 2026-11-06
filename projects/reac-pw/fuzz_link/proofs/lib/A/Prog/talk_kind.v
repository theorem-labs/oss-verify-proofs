(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 1428 of its 1523 lines of code are new or changed and 2594 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/talk_take.v; 415 of its 588 lines of code are new or changed and 1350 lines of the source are left out. *)
(* talk on image A: the inner loop over the IFLA_INFO_* attributes of an IFLA_LINKINFO (+0x3f8 .. +0x518), the piece
   TK_KIND of lib/A/Prog/talk_defs.v, from TK_TAKE_KD (lib/A/Prog/talk_take.v proves it) (listing
   (internal path) (internal record, sha256 5526460cb5be)). One turn at (i, il), b the chunk base:
   - kk_step, +0x3f8: `add a0, s4, s8` (a0 = b + i), to +0x3fc;
   - kk_kf, +0x3fc: one fresh state whose region holds the four header bytes at b + i (an SH entry from the chunk
     queue's addressable range covers the instrumented checks), s10 := l' (the length); l' < 4 or il < l' goes to
     the attribute step +0x598 (kind_scan stops); type 1 with the spilled kind flag clear goes to take_text +0x47c
     (TK_TAKE_KD); type 1 with the flag set (no kind buffer) and any other type go to the inner step +0x504;
   - kd_ks, +0x504: s10 := align4 l', s9 -= it, s8 += it; `blt 3, s9` goes back to +0x3f8 (the next turn, by the
     induction hypothesis) or to +0x598 (kind_scan has nothing left).
   tk_kind_ok: induction on the fuel of kind_scan (kk_all).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk fuzz_recv_kit talk_c talk_defs talk_kit talk_spec talk_take.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the registers every run of the loop keeps (the others it changes, or holds as constants) *)
Definition kk_KL : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 20%bv; 21%bv; 22%bv; 23%bv; 27%bv].
Definition kk_same (r1 r2 : bvmap 5 word) : Prop := forall r, In r kk_KL -> getr r2 r = getr r1 r.
Ltac kk_in := unfold kk_KL; cbn [In]; repeat (first [left; reflexivity | right]).

(* a fact on a symbolic term at an environment the run extended by fresh atoms, moved back to E *)
Ltac kk_back E H :=
  lazymatch type of H with
  | context [sv_denot ?E1 _] =>
      lazymatch E1 with
      | E => idtac
      | _ =>
          let HA := fresh "HA" in
          assert (HA : YP06.env_agree 512 E E1)
            by (split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]);
          rewrite !(YP06.sv_denot_agree 512 E E1 _ HA) in H by (vm_compute; reflexivity); clear HA
      end
  | _ => idtac
  end.

(* `blt 3, x` (signed) for x the 64-bit value of z *)
Lemma kk_blt3 : forall E v z, U E v = zcanon z -> - 2 ^ 63 <= z < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SLit 3)) (sv_denot E v) = (3 <? z).
Proof.
  intros E v z Hv Hz. cbn [branch_taken]. unfold bv_lts. rewrite !signed_is_swrap_unsigned.
  fold (U E (SLit 3)). fold (U E v). rewrite Hv, U_SLit, !zcanon_wrap, !bv_swrap_wrap.
  rewrite !swrap64_id by (unfold half64; lia). reflexivity.
Qed.

(* lbu x, lbu y, slli x 8, or *)
Lemma kk_U_join : forall E x y v0 v1, ew E y = w64 v0 -> ew E x = w64 v1 -> 0 <= v0 < 256 -> 0 <= v1 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SLL (SOff x 0) (SLit 8)) (SOff y 0)) = v0 + 256 * v1.
Proof.
  intros E x y v0 v1 Hy Hx R0 R1.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E x v1 Hx ltac:(lia)), (U_atom E y v0 Hy ltac:(lia)), (tt_U_lit E 8 ltac:(lia)).
  change (Z.land 8 63) with 8.
  assert (Hs : zcanon (Z.shiftl v1 8) = Z.shiftl v1 8).
  { unfold zcanon, M64. apply Z.mod_small. rewrite Z.shiftl_mul_pow2 by lia. lia. }
  rewrite Hs, (tw_join2 v1 v0 R1 R0). unfold zcanon, M64. apply Z.mod_small. lia.
Qed.

Lemma kk_flag : forall p n,
  (tk_flag p n = 0 -> p <> 0 /\ n <> 0) /\ (tk_flag p n <> 0 -> p = 0 \/ n = 0) /\ 0 <= tk_flag p n <= 1.
Proof. intros p n. unfold tk_flag. destruct (Z.eqb_spec p 0), (Z.eqb_spec n 0); cbn [orb]; lia. Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ link_listing PI).
#[local] Abbreviation VAL := (@pa_val _ link_listing PI).
#[local] Abbreviation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation cfg_of regs pc mem md := (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom SEGS)) md).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals.
Variable c : tkc.
Hypothesis HC : tk_call SK B c.
#[local] Abbreviation W := (tc_W c).
#[local] Abbreviation memc := (tc_memc c).
#[local] Abbreviation regs0 := (tc_regs0 c).
#[local] Abbreviation kbs := (tc_kbs c).

(* TK_KIND at one fuel *)
Definition kk_P (fk : nat) : Prop := forall ci a al l aa i il k,
  TK_A598 SK B c ci a al l (Attrs (kind_scan fk (tk_ck c ci) i il k) aa) ->
  forall regs mem md,
  tk_inv SK B c regs mem md -> tk_rs0 c regs -> tk_rat regs (tk_b ci) a al -> getr regs 21 = w64 l ->
  getr regs 24 = w64 i -> getr regs 25 = w64 il ->
  tk_amem c mem (tk_b ci) (Attrs k aa) ->
  0 <= ci < tk_nch c -> 0 <= i -> i + il <= Z.of_nat (length (tk_ck c ci)) -> 4 <= il < Z.of_nat fk ->
  tk_goal SK B c (cfg_of regs (BASE + TP_KH) mem md).

Lemma kk_rs0 : forall r1 r2, kk_same r1 r2 -> tk_rs0 c r1 -> tk_rs0 c r2.
Proof.
  intros r1 r2 Hs (H8 & H9 & H23). unfold tk_rs0.
  rewrite (Hs 8%bv ltac:(kk_in)), (Hs 9%bv ltac:(kk_in)), (Hs 23%bv ltac:(kk_in)). auto.
Qed.

Lemma kk_rat : forall r1 r2 b a al, kk_same r1 r2 -> tk_rat r1 b a al ->
  getr r2 19 = w64 0x1fffc -> getr r2 15 = w64 4 -> getr r2 16 = w64 1 -> getr r2 17 = w64 3 -> tk_rat r2 b a al.
Proof.
  intros r1 r2 b a al Hs (H20 & H27 & H22 & _) H19 H15 H16 H17. unfold tk_rat.
  rewrite (Hs 20%bv ltac:(kk_in)), (Hs 27%bv ltac:(kk_in)), (Hs 22%bv ltac:(kk_in)). auto 10.
Qed.

(* with no kind buffer, the buffers say nothing of the kind *)
Lemma kk_amem_dead : forall mem b k k' aa, (tk_kd c = 0 \/ tk_kn c = 0) ->
  tk_amem c mem b (Attrs k aa) -> tk_amem c mem b (Attrs k' aa).
Proof.
  intros mem b k k' aa Hd (HM & (B1 & B2 & B3 & B4 & B5 & B6) & HSP).
  split; [exact HM|]. split; [|exact HSP].
  refine (conj B1 (conj B2 (conj _ (conj B4 (conj _ B6))))).
  - intros p _ H0 H1. exfalso. destruct Hd; lia.
  - intros _ H0 H1. exfalso. destruct Hd; lia.
Qed.

(* byte o of chunk ci at the current memory *)
Lemma kk_byte : forall regs mem md ci o, tk_inv SK B c regs mem md -> 0 <= ci < tk_nch c ->
  0 <= o < Z.of_nat (length (tk_ck c ci)) ->
  mbyte SEGS (rdW W mem) (tk_b ci + o) = nth_error (tk_ck c ci) (Z.to_nat o).
Proof.
  intros regs mem md ci o HI Hci Ho.
  destruct (tt_chunk SK B c HC ci Hci) as (Hcl & Hcl2 & Hnc).
  pose proof HC as (_ & _ & _ & _ & HNW & _).
  unfold tk_nch, tk_ck, tk_b in *.
  replace (LA_G_NL + NL_CHUNK_MAX * ci + o) with (LA_G_NL + 4096 * ci + o) by (unfold NL_CHUNK_MAX; ring).
  apply (anlk_chunk_byte SEGS (rdW W mem) LA_G_NL kbs ci o (tk_nlk_kept SK B c HC regs mem md HI) HNW Hci). lia.
Qed.

(* +0x504: s10 := align4 l', s9 -= it, s8 += it; `blt 3, s9` *)
Lemma kd_ks : forall (fk : nat) ci a al l aa, kk_P fk ->
  forall i il l' k',
  TK_A598 SK B c ci a al l (Attrs (kind_scan fk (tk_ck c ci) (i + nl_align l') (il - nl_align l') k') aa) ->
  0 <= ci < tk_nch c -> 0 <= i -> 4 <= l' <= il -> l' < 2 ^ 16 -> i + il <= Z.of_nat (length (tk_ck c ci)) ->
  il < Z.of_nat fk + 4 ->
  TK_K504 SK B c ci a al l aa i il l' k'.
Proof.
  intros fk ci a al l aa IH i il l' k' K598 Hci Hi Hl Hl16 Hil Hfk regs mem md HI Hrs0 Hrat H21 H24 H25 H26 Ham.
  unfold tk_goal in *.
  destruct (tt_chunk SK B c HC ci Hci) as (Hcl & Hcl2 & Hnc). unfold NL_CHUNK_MAX, NL_CHUNKS in Hcl2, Hnc.
  pose proof HC as ((_ & HGX & _) & _). pose proof HI as (HJ & _).
  pose proof Hrs0 as (H8 & H9 & H23).
  pose proof (tw_align_range l' ltac:(lia)) as (Al1 & Al2).
  set (xs := @nil word).
  pose proof (tk_st_ok SK B LV c HC regs mem md xs TP_KS tk_ov_at [] [] HI H23 (tk_ov_at_ok c regs xs _ _ _ Hrat)
    eq_refl (Forall_nil _) I I) as HS.
  assert (SHOK : sh_ok SEGS tk_Bx [] (tk_E c regs xs) (rdW W mem)) by constructor.
  pose proof (tk_E_env c regs xs) as HEI.
  pose proof (paj_run_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUN.
  pose proof (paj_run_to_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUNTO.
  pose proof (paj_branch (PI := PI)) as BR.
  assert (E24 : ew (tk_E c regs xs) 24 = w64 i)
    by (rewrite (tk_E_reg c regs xs 24 24%bv) by (lia || reflexivity); exact H24).
  assert (E25 : ew (tk_E c regs xs) 25 = w64 il)
    by (rewrite (tk_E_reg c regs xs 25 25%bv) by (lia || reflexivity); exact H25).
  assert (E26 : ew (tk_E c regs xs) 26 = w64 l')
    by (rewrite (tk_E_reg c regs xs 26 26%bv) by (lia || reflexivity); exact H26).
  assert (Ual : U (tk_E c regs xs) (SAlu ALU_AND (SOff 26 3) (SLit 131068)) = nl_align l').
  { rewrite U_and_lit by lia. rewrite (U_atom_off _ 26 l' 3 E26) by lia. apply tw_land_align. lia. }
  assert (Usub : U (tk_E c regs xs) (SAlu ALU_SUB (SOff 25 0) (SAlu ALU_AND (SOff 26 3) (SLit 131068))) =
                 zcanon (il - nl_align l')).
  { rewrite U_SAlu. cbn [zalu_raw]. rewrite Ual, (U_atom _ 25 il E25) by lia. reflexivity. }
  assert (Uadd : U (tk_E c regs xs) (SAlu ALU_ADD (SAlu ALU_AND (SOff 26 3) (SLit 131068)) (SOff 24 0)) =
                 nl_align l' + i).
  { rewrite U_SAlu. cbn [zalu_raw]. rewrite Ual, (U_atom _ 24 i E24) by lia. unfold zcanon, M64.
    apply Z.mod_small. lia. }
  (* +0x504..+0x514 *)
  paj_run_tok RUN HS HJ SHOK tk_span; [tt_awr0 |].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
  tt_ro HF Em1. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK tk_span; kk_back (tk_E c regs xs) Hc;
    rewrite (kk_blt3 _ _ (il - nl_align l') Usub ltac:(lia)) in Hc.
  - (* il - align4 l' > 3: the next turn at (i + align4 l', il - align4 l') *)
    apply Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_KH; [tt_awr0 |].
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
    tt_ro HF Em2. pmkst HS. rewrite Em2, Em1 in HJ |- *.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in * end.
    lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
      pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) kk_KL HS
        ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                     | reflexivity])
        ltac:(vm_compute; reflexivity)) as RK end.
    cbn [ms_regs restrict] in RK.
    tt_reg HS (24%bv : bv 5) R24. tt_reg HS (25%bv : bv 5) R25.
    tt_reg HS (15%bv : bv 5) R15. tt_reg HS (16%bv : bv 5) R16. tt_reg HS (17%bv : bv 5) R17.
    tt_reg HS (19%bv : bv 5) R19.
    kk_back (tk_E c regs xs) R24. kk_back (tk_E c regs xs) R25.
    rewrite denot_lit_U, Uadd in R24. rewrite denot_lit_U, Usub in R25.
    assert (HI2 : tk_inv SK B c (ms_regs ms2) mem md2).
    { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms2) mem md2 (fun _ => False) HI HJ).
      - unfold md2. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
      - unfold md2. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
      - intros x _ _. reflexivity.
      - intros x [].
      - intros x Hp. exact Hp.
      - exact (RK 2%bv ltac:(kk_in)).
      - exact (RK 3%bv ltac:(kk_in)).
      - exact (RK 4%bv ltac:(kk_in)). }
    apply (IH ci a al l aa (i + nl_align l') (il - nl_align l') k' K598 (ms_regs ms2) mem md2 HI2
      (kk_rs0 _ _ RK Hrs0)
      (kk_rat _ _ _ _ _ RK Hrat ltac:(rewrite R19; reflexivity) ltac:(rewrite R15; reflexivity)
         ltac:(rewrite R16; reflexivity) ltac:(rewrite R17; reflexivity))
      ltac:(rewrite (RK 21%bv ltac:(kk_in)); exact H21)).
    + rewrite R24. unfold w64. f_equal. lia.
    + rewrite R25. unfold w64, zcanon, M64. rewrite Z.mod_small by lia. reflexivity.
    + exact Ham.
    + exact Hci.
    + lia.
    + lia.
    + lia.
  - (* il - align4 l' <= 3: the attribute step *)
    apply Z.ltb_ge in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_AS; [tt_awr0 |].
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
    tt_ro HF Em2. pmkst HS. rewrite Em2, Em1 in HJ |- *.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in * end.
    lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
      pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) kk_KL HS
        ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                     | reflexivity])
        ltac:(vm_compute; reflexivity)) as RK end.
    cbn [ms_regs restrict] in RK.
    tt_reg HS (15%bv : bv 5) R15. tt_reg HS (16%bv : bv 5) R16. tt_reg HS (17%bv : bv 5) R17.
    tt_reg HS (19%bv : bv 5) R19.
    assert (HI2 : tk_inv SK B c (ms_regs ms2) mem md2).
    { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms2) mem md2 (fun _ => False) HI HJ).
      - unfold md2. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
      - unfold md2. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
      - intros x _ _. reflexivity.
      - intros x [].
      - intros x Hp. exact Hp.
      - exact (RK 2%bv ltac:(kk_in)).
      - exact (RK 3%bv ltac:(kk_in)).
      - exact (RK 4%bv ltac:(kk_in)). }
    rewrite (ks_short fk (tk_ck c ci) (i + nl_align l') (il - nl_align l') k' ltac:(lia)) in K598.
    apply (K598 (ms_regs ms2) mem md2 HI2 (kk_rs0 _ _ RK Hrs0)
      (kk_rat _ _ _ _ _ RK Hrat ltac:(rewrite R19; reflexivity) ltac:(rewrite R15; reflexivity)
         ltac:(rewrite R16; reflexivity) ltac:(rewrite R17; reflexivity))
      ltac:(rewrite (RK 21%bv ltac:(kk_in)); exact H21) Ham).
Qed.

(* +0x3fc: the attribute's header at b + i, its two tests, its type and the kind flag *)
Lemma kk_kf : TK_TAKE_KD SK B c -> forall fk, kk_P fk ->
  forall ci a al l aa i il k, TK_A598 SK B c ci a al l (Attrs (kind_scan (S fk) (tk_ck c ci) i il k) aa) ->
  forall regs mem md, tk_inv SK B c regs mem md -> tk_rs0 c regs -> tk_rat regs (tk_b ci) a al ->
  getr regs 21 = w64 l -> getr regs 24 = w64 i -> getr regs 25 = w64 il -> getr regs 10 = w64 (tk_b ci + i) ->
  tk_amem c mem (tk_b ci) (Attrs k aa) ->
  0 <= ci < tk_nch c -> 0 <= i -> i + il <= Z.of_nat (length (tk_ck c ci)) -> 4 <= il < Z.of_nat (S fk) ->
  tk_goal SK B c (cfg_of regs (BASE + TP_KF) mem md).
Proof.
  intros TKD fk IH ci a al l aa i il k K598 regs mem md HI Hrs0 Hrat H21 H24 H25 H10 Ham Hci Hi Hil Hfk.
  unfold tk_goal in *.
  destruct (tt_chunk SK B c HC ci Hci) as (Hcl & Hcl2 & Hnc). unfold NL_CHUNK_MAX, NL_CHUNKS in Hcl2, Hnc.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (tk_sp_rng SK B c HC) as (S0 & S1 & S2 & S3).
  pose proof HC as ((_ & HGX & _) & _). pose proof HI as (HJ & _).
  pose proof Hrs0 as (H8 & H9 & H23). pose proof Hrat as (H20 & H27 & H22 & H19 & H15 & H16 & H17).
  pose proof Ham as (_ & _ & HSP).
  rewrite Nat2Z.inj_succ in Hfk.
  assert (HbR : 0x5dcac0 <= tk_b ci /\ tk_b ci + 4096 <= 0x5dcac0 + 262144)
    by (unfold tk_b, NL_CHUNK_MAX, LA_G_NL; lia).
  (* the four header bytes *)
  destruct (nth_error (tk_ck c ci) (Z.to_nat i)) as [b0|] eqn:E0; [|apply nth_error_None in E0; lia].
  destruct (nth_error (tk_ck c ci) (Z.to_nat (i + 1))) as [b1|] eqn:E1; [|apply nth_error_None in E1; lia].
  destruct (nth_error (tk_ck c ci) (Z.to_nat (i + 2))) as [b2|] eqn:E2; [|apply nth_error_None in E2; lia].
  destruct (nth_error (tk_ck c ci) (Z.to_nat (i + 2 + 1))) as [b3|] eqn:E3; [|apply nth_error_None in E3; lia].
  pose proof (tw_byte_range b0) as R0. pose proof (tw_byte_range b1) as R1.
  pose proof (tw_byte_range b2) as R2. pose proof (tw_byte_range b3) as R3.
  assert (M0 : mbyte SEGS (rdW W mem) (tk_b ci + i + 0) = Some b0)
    by (rewrite Z.add_0_r, (kk_byte regs mem md ci i HI Hci ltac:(lia)); exact E0).
  assert (M1 : mbyte SEGS (rdW W mem) (tk_b ci + i + 1) = Some b1)
    by (rewrite <- Z.add_assoc, (kk_byte regs mem md ci (i + 1) HI Hci ltac:(lia)); exact E1).
  assert (M2 : mbyte SEGS (rdW W mem) (tk_b ci + i + 2) = Some b2)
    by (rewrite <- Z.add_assoc, (kk_byte regs mem md ci (i + 2) HI Hci ltac:(lia)); exact E2).
  assert (M3 : mbyte SEGS (rdW W mem) (tk_b ci + i + 3) = Some b3)
    by (replace (tk_b ci + i + 3) with (tk_b ci + (i + 2 + 1)) by ring;
        rewrite (kk_byte regs mem md ci (i + 2 + 1) HI Hci ltac:(lia)); exact E3).
  set (xs := [w64 (bz b0); w64 (bz b1); w64 (bz b2); w64 (bz b3)]).
  assert (U10 : bv_unsigned (ew (tk_E c regs xs) 10) = tk_b ci + i).
  { rewrite (tk_E_reg c regs xs 10 10%bv) by (lia || reflexivity). rewrite H10. apply unsigned_lit_small. lia. }
  assert (E49 : ew (tk_E c regs xs) 49 = w64 (bz b0)) by exact (tk_E_xs c regs xs 0 ltac:(lia)).
  assert (E50 : ew (tk_E c regs xs) 50 = w64 (bz b1)) by exact (tk_E_xs c regs xs 1 ltac:(lia)).
  assert (E51 : ew (tk_E c regs xs) 51 = w64 (bz b2)) by exact (tk_E_xs c regs xs 2 ltac:(lia)).
  assert (E52 : ew (tk_E c regs xs) 52 = w64 (bz b3)) by exact (tk_E_xs c regs xs 3 ltac:(lia)).
  assert (U49 : bv_unsigned (ew (tk_E c regs xs) 49) = bz b0) by (rewrite E49; apply unsigned_lit_small; lia).
  assert (U50 : bv_unsigned (ew (tk_E c regs xs) 50) = bz b1) by (rewrite E50; apply unsigned_lit_small; lia).
  assert (U51 : bv_unsigned (ew (tk_E c regs xs) 51) = bz b2) by (rewrite E51; apply unsigned_lit_small; lia).
  assert (U52 : bv_unsigned (ew (tk_E c regs xs) 52) = bz b3) by (rewrite E52; apply unsigned_lit_small; lia).
  assert (HR4 : region_ok SEGS (tk_E c regs xs) (rdW W mem) (tk_R4 10)).
  { unfold region_ok, tk_R4, tk_ch.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    - apply (chunk_ok_val SEGS _ _ (tk_b ci + i) 0 1 (SOff 49 0) (bz b0));
        [cbn [sv_denot]; rewrite U49, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia
        | exact (tt_val1 _ _ _ M0)].
    - apply (chunk_ok_val SEGS _ _ (tk_b ci + i) 1 1 (SOff 50 0) (bz b1));
        [cbn [sv_denot]; rewrite U50, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia
        | exact (tt_val1 _ _ _ M1)].
    - apply (chunk_ok_val SEGS _ _ (tk_b ci + i) 2 1 (SOff 51 0) (bz b2));
        [cbn [sv_denot]; rewrite U51, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia
        | exact (tt_val1 _ _ _ M2)].
    - apply (chunk_ok_val SEGS _ _ (tk_b ci + i) 3 1 (SOff 52 0) (bz b3));
        [cbn [sv_denot]; rewrite U52, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia
        | exact (tt_val1 _ _ _ M3)]. }
  pose proof (tk_base_sp SK B c HC regs mem md xs HI) as Usp.
  assert (HPD : pairwise_disjoint (tk_E c regs xs) [tk_frs; tk_R4 10]).
  { refine (conj (conj _ I) (conj I I)). unfold extent_disjoint, tk_frs, tk_R4.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite Usp. cbn [base_val]. rewrite U10. right. lia. }
  assert (HAT : atoms_ok (tk_E c regs xs) ((10%nat, mkAF LA_G_NL (LA_G_NL + NK_CHUNK_LEN - 4) 0) :: tk_bfacts)).
  { unfold tk_bfacts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U10, U49, U50, U51, U52, !Z.pow_0_r, !Z.mod_1_r. unfold LA_G_NL, NK_CHUNK_LEN. repeat split; lia. }
  assert (SHOK : sh_ok SEGS tk_Bx tk_SH_kf (tk_E c regs xs) (rdW W mem)).
  { apply Forall_cons; [|apply Forall_nil].
    apply (tk_shent_ok _ _ 10 0 8 (tk_b ci + i)).
    - unfold tk_Bx. apply (tk_U_reg c regs xs 23 23%bv); [lia | reflexivity | exact H23 | unfold SHADOW_OFF; lia].
    - apply (tk_U_reg c regs xs 10 10%bv); [lia | reflexivity | exact H10 | lia].
    - lia.
    - left. lia.
    - apply (tt_ra_gnl SK B c HC regs mem md HI); unfold LA_G_NL, NK_N_CHUNKS; lia. }
  pose proof (tk_st_ok SK B LV c HC regs mem md xs TP_KF tk_ov_at [tk_frs; tk_R4 10]
    ((10%nat, mkAF LA_G_NL (LA_G_NL + NK_CHUNK_LEN - 4) 0) :: tk_bfacts) HI H23 (tk_ov_at_ok c regs xs _ _ _ Hrat)
    ltac:(vm_compute; reflexivity)
    ltac:(apply Forall_cons; [exact (tk_frs_ok SK B c HC regs mem md xs (tk_b ci) HI HSP H20 ltac:(lia) ltac:(lia))
                             | apply Forall_cons; [exact HR4 | apply Forall_nil]]) HPD HAT) as HS.
  (* the values the branches test *)
  assert (Ul : U (tk_E c regs xs) (SAlu ALU_OR (SAlu ALU_SLL (SOff 50 0) (SLit 8)) (SOff 49 0)) = rd16 (tk_ck c ci) i).
  { rewrite (kk_U_join _ 50 49 (bz b0) (bz b1) E49 E50) by lia. symmetry. exact (tw_rd16_bytes _ i b0 b1 Hi E0 E1). }
  assert (Ut : U (tk_E c regs xs) (SAlu ALU_OR (SAlu ALU_SLL (SOff 52 0) (SLit 8)) (SOff 51 0)) =
               rd16 (tk_ck c ci) (i + 2)).
  { rewrite (kk_U_join _ 52 51 (bz b2) (bz b3) E51 E52) by lia. symmetry.
    exact (tw_rd16_bytes _ (i + 2) b2 b3 ltac:(lia) E2 E3). }
  assert (Rl : 0 <= rd16 (tk_ck c ci) i < 2 ^ 16) by (rewrite (tw_rd16_bytes _ i b0 b1 Hi E0 E1); lia).
  assert (E25 : ew (tk_E c regs xs) 25 = w64 il)
    by (rewrite (tk_E_reg c regs xs 25 25%bv) by (lia || reflexivity); exact H25).
  assert (E48 : ew (tk_E c regs xs) 48 = w64 (tk_flag (tk_kd c) (tk_kn c))) by exact (tk_E_ext c regs xs 16 ltac:(lia)).
  pose proof (kk_flag (tk_kd c) (tk_kn c)) as (Fl0 & Fl1 & Fl2).
  pose proof (tk_E_env c regs xs) as HEI.
  pose proof (paj_run_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUN.
  pose proof (paj_run_to_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUNTO.
  pose proof (paj_branch (PI := PI)) as BR.
  (* the checks of bytes 0 and 1, the length; `bltu s10, a5` *)
  paj_run_tok RUN HS HJ SHOK tk_span; [tt_awr0 |].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
  tt_ro HF Em1. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK tk_span; kk_back (tk_E c regs xs) Hc;
    rewrite branch_ltu_U, Ul, (tt_U_lit _ 4 ltac:(lia)) in Hc.
  - (* l' < 4: the attribute step, kind_scan stops *)
    apply Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_AS; [tt_awr0 |].
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
    tt_ro HF Em2. pmkst HS. rewrite Em2, Em1 in HJ |- *.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in * end.
    lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
      pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) kk_KL HS
        ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                     | reflexivity])
        ltac:(vm_compute; reflexivity)) as RK end.
    cbn [ms_regs restrict] in RK.
    tt_reg HS (15%bv : bv 5) R15. tt_reg HS (16%bv : bv 5) R16. tt_reg HS (17%bv : bv 5) R17.
    tt_reg HS (19%bv : bv 5) R19.
    assert (HI2 : tk_inv SK B c (ms_regs ms2) mem md2).
    { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms2) mem md2 (fun _ => False) HI HJ).
      - unfold md2. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
      - unfold md2. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
      - intros x _ _. reflexivity.
      - intros x [].
      - intros x Hp. exact Hp.
      - exact (RK 2%bv ltac:(kk_in)).
      - exact (RK 3%bv ltac:(kk_in)).
      - exact (RK 4%bv ltac:(kk_in)). }
    rewrite (ks_stop fk (tk_ck c ci) i il k ltac:(lia) ltac:(lia)) in K598.
    apply (K598 (ms_regs ms2) mem md2 HI2 (kk_rs0 _ _ RK Hrs0)
      (kk_rat _ _ _ _ _ RK Hrat ltac:(rewrite R19; reflexivity) ltac:(rewrite R15; reflexivity)
         ltac:(rewrite R16; reflexivity) ltac:(rewrite R17; reflexivity))
      ltac:(rewrite (RK 21%bv ltac:(kk_in)); exact H21) Ham).
  - apply Z.ltb_ge in Hc. rename Hc into Hl4.
    (* `bltu s9, s10` *)
    paj_run_tok RUN HS HJ SHOK tk_span; [tt_awr0 |].
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
    tt_ro HF Em2. clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK tk_span; kk_back (tk_E c regs xs) Hc;
      rewrite branch_ltu_U, (U_atom _ 25 il E25 ltac:(lia)), Ul in Hc.
    + (* il < l': the attribute step, kind_scan stops *)
      apply Z.ltb_lt in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_AS; [tt_awr0 |].
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms3 end.
      tt_ro HF Em3. pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
      lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md3 := m) in * end.
      lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
        pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) kk_KL HS
          ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                       | reflexivity])
          ltac:(vm_compute; reflexivity)) as RK end.
      cbn [ms_regs restrict] in RK.
      tt_reg HS (15%bv : bv 5) R15. tt_reg HS (16%bv : bv 5) R16. tt_reg HS (17%bv : bv 5) R17.
      tt_reg HS (19%bv : bv 5) R19.
      assert (HI3 : tk_inv SK B c (ms_regs ms3) mem md3).
      { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms3) mem md3 (fun _ => False) HI HJ).
        - unfold md3. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
        - unfold md3. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
        - intros x _ _. reflexivity.
        - intros x [].
        - intros x Hp. exact Hp.
        - exact (RK 2%bv ltac:(kk_in)).
        - exact (RK 3%bv ltac:(kk_in)).
        - exact (RK 4%bv ltac:(kk_in)). }
      rewrite (ks_stop fk (tk_ck c ci) i il k ltac:(lia) ltac:(lia)) in K598.
      apply (K598 (ms_regs ms3) mem md3 HI3 (kk_rs0 _ _ RK Hrs0)
        (kk_rat _ _ _ _ _ RK Hrat ltac:(rewrite R19; reflexivity) ltac:(rewrite R15; reflexivity)
           ltac:(rewrite R16; reflexivity) ltac:(rewrite R17; reflexivity))
        ltac:(rewrite (RK 21%bv ltac:(kk_in)); exact H21) Ham).
    + apply Z.ltb_ge in Hc. rename Hc into Hll.
      (* the checks of bytes 2 and 3, the type; `bne type, 1` *)
      paj_run_tok RUN HS HJ SHOK tk_span; [tt_awr0 |].
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms3 end.
      tt_ro HF Em3. clear HF HFr HG.
      psrr_branch_tok RUN BR HS SHOK tk_span; kk_back (tk_E c regs xs) Hc;
        rewrite branch_ne_U, Ut, (tt_U_lit _ 1 ltac:(lia)) in Hc.
      * (* another type: the inner step with the kind kept *)
        apply negb_true_iff, Z.eqb_neq in Hc.
        paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_KS; [tt_awr0 |].
        lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms4 end.
        tt_ro HF Em4. pmkst HS. rewrite Em4, Em3, Em2, Em1 in HJ |- *.
        lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md4 := m) in * end.
        lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
          pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) kk_KL HS
            ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                         | reflexivity])
            ltac:(vm_compute; reflexivity)) as RK end.
        cbn [ms_regs restrict] in RK.
        tt_reg HS (15%bv : bv 5) R15. tt_reg HS (16%bv : bv 5) R16. tt_reg HS (17%bv : bv 5) R17.
        tt_reg HS (19%bv : bv 5) R19. tt_reg HS (24%bv : bv 5) R24. tt_reg HS (25%bv : bv 5) R25.
        tt_reg HS (26%bv : bv 5) R26.
        kk_back (tk_E c regs xs) R24. kk_back (tk_E c regs xs) R25. kk_back (tk_E c regs xs) R26.
        rewrite (tt_den c regs xs 24 24%bv) in R24 by (lia || reflexivity).
        rewrite (tt_den c regs xs 25 25%bv) in R25 by (lia || reflexivity).
        rewrite denot_lit_U, Ul in R26.
        assert (HI4 : tk_inv SK B c (ms_regs ms4) mem md4).
        { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms4) mem md4 (fun _ => False) HI HJ).
          - unfold md4. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
          - unfold md4. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
          - intros x _ _. reflexivity.
          - intros x [].
          - intros x Hp. exact Hp.
          - exact (RK 2%bv ltac:(kk_in)).
          - exact (RK 3%bv ltac:(kk_in)).
          - exact (RK 4%bv ltac:(kk_in)). }
        rewrite (ks_other fk (tk_ck c ci) i il k ltac:(lia) ltac:(lia) Hc) in K598.
        apply (kd_ks fk ci a al l aa IH i il (rd16 (tk_ck c ci) i) k K598 Hci Hi ltac:(lia) ltac:(lia) Hil
          ltac:(lia) (ms_regs ms4) mem md4 HI4 (kk_rs0 _ _ RK Hrs0)
          (kk_rat _ _ _ _ _ RK Hrat ltac:(rewrite R19; reflexivity) ltac:(rewrite R15; reflexivity)
             ltac:(rewrite R16; reflexivity) ltac:(rewrite R17; reflexivity))
          ltac:(rewrite (RK 21%bv ltac:(kk_in)); exact H21) ltac:(rewrite R24; exact H24)
          ltac:(rewrite R25; exact H25) R26 Ham).
      * (* IFLA_INFO_KIND: the spilled kind flag; `bnez` *)
        apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hty.
        paj_run_tok RUN HS HJ SHOK tk_span; [tt_awr0 |].
        lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms4 end.
        tt_ro HF Em4. clear HF HFr HG.
        psrr_branch_tok RUN BR HS SHOK tk_span; kk_back (tk_E c regs xs) Hc;
          rewrite branch_ne_U, (U_atom _ 48 _ E48 ltac:(lia)), (tt_U_lit _ 0 ltac:(lia)) in Hc.
        -- (* the flag set (no kind buffer): the inner step; the kind the scan takes needs no buffer *)
           apply negb_true_iff, Z.eqb_neq in Hc.
           paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_KS; [tt_awr0 |].
           lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms5 end.
           tt_ro HF Em5. pmkst HS. rewrite Em5, Em4, Em3, Em2, Em1 in HJ |- *.
           lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md5 := m) in * end.
           lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
             pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) kk_KL HS
               ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT;
                             lia | reflexivity])
               ltac:(vm_compute; reflexivity)) as RK end.
           cbn [ms_regs restrict] in RK.
           tt_reg HS (15%bv : bv 5) R15. tt_reg HS (16%bv : bv 5) R16. tt_reg HS (17%bv : bv 5) R17.
           tt_reg HS (19%bv : bv 5) R19. tt_reg HS (24%bv : bv 5) R24. tt_reg HS (25%bv : bv 5) R25.
           tt_reg HS (26%bv : bv 5) R26.
           kk_back (tk_E c regs xs) R24. kk_back (tk_E c regs xs) R25. kk_back (tk_E c regs xs) R26.
           rewrite (tt_den c regs xs 24 24%bv) in R24 by (lia || reflexivity).
           rewrite (tt_den c regs xs 25 25%bv) in R25 by (lia || reflexivity).
           rewrite denot_lit_U, Ul in R26.
           assert (HI5 : tk_inv SK B c (ms_regs ms5) mem md5).
           { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms5) mem md5 (fun _ => False) HI HJ).
             - unfold md5. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
             - unfold md5. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
             - intros x _ _. reflexivity.
             - intros x [].
             - intros x Hp. exact Hp.
             - exact (RK 2%bv ltac:(kk_in)).
             - exact (RK 3%bv ltac:(kk_in)).
             - exact (RK 4%bv ltac:(kk_in)). }
           rewrite (ks_kind fk (tk_ck c ci) i il k ltac:(lia) ltac:(lia) Hty) in K598.
           apply (kd_ks fk ci a al l aa IH i il (rd16 (tk_ck c ci) i)
             (Some (slice (tk_ck c ci) (i + RTA_HDR) (rd16 (tk_ck c ci) i - RTA_HDR))) K598 Hci Hi ltac:(lia)
             ltac:(lia) Hil ltac:(lia) (ms_regs ms5) mem md5 HI5 (kk_rs0 _ _ RK Hrs0)
             (kk_rat _ _ _ _ _ RK Hrat ltac:(rewrite R19; reflexivity) ltac:(rewrite R15; reflexivity)
                ltac:(rewrite R16; reflexivity) ltac:(rewrite R17; reflexivity))
             ltac:(rewrite (RK 21%bv ltac:(kk_in)); exact H21) ltac:(rewrite R24; exact H24)
             ltac:(rewrite R25; exact H25) R26 (kk_amem_dead _ _ _ _ _ (Fl1 Hc) Ham)).
        -- (* the flag clear: take_text into the kind buffer *)
           apply negb_false_iff, Z.eqb_eq in Hc.
           destruct (Fl0 Hc) as (Hkd & Hkn).
           paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_TK; [tt_awr0 |].
           lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms5 end.
           tt_ro HF Em5. pmkst HS. rewrite Em5, Em4, Em3, Em2, Em1 in HJ |- *.
           lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md5 := m) in * end.
           lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
             pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) kk_KL HS
               ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT;
                             lia | reflexivity])
               ltac:(vm_compute; reflexivity)) as RK end.
           cbn [ms_regs restrict] in RK.
           tt_reg HS (15%bv : bv 5) R15. tt_reg HS (16%bv : bv 5) R16. tt_reg HS (17%bv : bv 5) R17.
           tt_reg HS (19%bv : bv 5) R19. tt_reg HS (24%bv : bv 5) R24. tt_reg HS (25%bv : bv 5) R25.
           tt_reg HS (26%bv : bv 5) R26.
           kk_back (tk_E c regs xs) R24. kk_back (tk_E c regs xs) R25. kk_back (tk_E c regs xs) R26.
           rewrite (tt_den c regs xs 24 24%bv) in R24 by (lia || reflexivity).
           rewrite (tt_den c regs xs 25 25%bv) in R25 by (lia || reflexivity).
           rewrite denot_lit_U, Ul in R26.
           assert (HI5 : tk_inv SK B c (ms_regs ms5) mem md5).
           { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms5) mem md5 (fun _ => False) HI HJ).
             - unfold md5. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
             - unfold md5. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
             - intros x _ _. reflexivity.
             - intros x [].
             - intros x Hp. exact Hp.
             - exact (RK 2%bv ltac:(kk_in)).
             - exact (RK 3%bv ltac:(kk_in)).
             - exact (RK 4%bv ltac:(kk_in)). }
           rewrite (ks_kind fk (tk_ck c ci) i il k ltac:(lia) ltac:(lia) Hty) in K598.
           apply (TKD ci a al l aa i il (rd16 (tk_ck c ci) i) k
             (kd_ks fk ci a al l aa IH i il (rd16 (tk_ck c ci) i)
                (Some (slice (tk_ck c ci) (i + RTA_HDR) (rd16 (tk_ck c ci) i - RTA_HDR))) K598 Hci Hi ltac:(lia)
                ltac:(lia) Hil ltac:(lia))
             (ms_regs ms5) mem md5 HI5 (kk_rs0 _ _ RK Hrs0)
             (kk_rat _ _ _ _ _ RK Hrat ltac:(rewrite R19; reflexivity) ltac:(rewrite R15; reflexivity)
                ltac:(rewrite R16; reflexivity) ltac:(rewrite R17; reflexivity))
             ltac:(rewrite (RK 21%bv ltac:(kk_in)); exact H21) ltac:(rewrite R24; exact H24)
             ltac:(rewrite R25; exact H25) R26 Ham Hkd Hkn Hci Hi ltac:(lia) Hil).
Qed.

(* one turn: +0x3f8 `add a0, s4, s8`, then +0x3fc *)
Lemma kk_step : TK_TAKE_KD SK B c -> forall fk, kk_P fk -> kk_P (S fk).
Proof.
  intros TKD fk IH ci a al l aa i il k K598 regs mem md HI Hrs0 Hrat H21 H24 H25 Ham Hci Hi Hil Hfk.
  unfold tk_goal in *.
  destruct (tt_chunk SK B c HC ci Hci) as (Hcl & Hcl2 & Hnc). unfold NL_CHUNK_MAX, NL_CHUNKS in Hcl2, Hnc.
  pose proof HC as ((_ & HGX & _) & _). pose proof HI as (HJ & _).
  pose proof Hrs0 as (H8 & H9 & H23). pose proof Hrat as (H20 & H27 & H22 & H19 & H15 & H16 & H17).
  assert (HbR : 0x5dcac0 <= tk_b ci /\ tk_b ci + 4096 <= 0x5dcac0 + 262144)
    by (unfold tk_b, NL_CHUNK_MAX, LA_G_NL; lia).
  set (xs := @nil word).
  pose proof (tk_st_ok SK B LV c HC regs mem md xs TP_KH tk_ov_at [] [] HI H23 (tk_ov_at_ok c regs xs _ _ _ Hrat)
    eq_refl (Forall_nil _) I I) as HS.
  assert (SHOK : sh_ok SEGS tk_Bx [] (tk_E c regs xs) (rdW W mem)) by constructor.
  pose proof (tk_E_env c regs xs) as HEI.
  pose proof (paj_run_to_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUNTO.
  assert (E20 : ew (tk_E c regs xs) 20 = w64 (tk_b ci))
    by (rewrite (tk_E_reg c regs xs 20 20%bv) by (lia || reflexivity); exact H20).
  assert (E24 : ew (tk_E c regs xs) 24 = w64 i)
    by (rewrite (tk_E_reg c regs xs 24 24%bv) by (lia || reflexivity); exact H24).
  paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_KF; [tt_awr0 |].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
  tt_ro HF Em1. pmkst HS. rewrite Em1 in HJ |- *.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md1 := m) in * end.
  lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
    pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) kk_KL HS
      ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                   | reflexivity])
      ltac:(vm_compute; reflexivity)) as RK end.
  cbn [ms_regs restrict] in RK.
  tt_reg HS (10%bv : bv 5) R10. tt_reg HS (24%bv : bv 5) R24. tt_reg HS (25%bv : bv 5) R25.
  tt_reg HS (15%bv : bv 5) R15. tt_reg HS (16%bv : bv 5) R16. tt_reg HS (17%bv : bv 5) R17.
  tt_reg HS (19%bv : bv 5) R19.
  kk_back (tk_E c regs xs) R10. kk_back (tk_E c regs xs) R24. kk_back (tk_E c regs xs) R25.
  rewrite denot_lit_U, (tt_U_add _ 20 0 24 (tk_b ci) i E20 E24) in R10 by lia.
  rewrite (tt_den c regs xs 24 24%bv) in R24 by (lia || reflexivity).
  rewrite (tt_den c regs xs 25 25%bv) in R25 by (lia || reflexivity).
  assert (HI1 : tk_inv SK B c (ms_regs ms1) mem md1).
  { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms1) mem md1 (fun _ => False) HI HJ).
    - unfold md1. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
    - unfold md1. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
    - intros x _ _. reflexivity.
    - intros x [].
    - intros x Hp. exact Hp.
    - exact (RK 2%bv ltac:(kk_in)).
    - exact (RK 3%bv ltac:(kk_in)).
    - exact (RK 4%bv ltac:(kk_in)). }
  apply (kk_kf TKD fk IH ci a al l aa i il k K598 (ms_regs ms1) mem md1 HI1 (kk_rs0 _ _ RK Hrs0)
    (kk_rat _ _ _ _ _ RK Hrat ltac:(rewrite R19; reflexivity) ltac:(rewrite R15; reflexivity)
       ltac:(rewrite R16; reflexivity) ltac:(rewrite R17; reflexivity))
    ltac:(rewrite (RK 21%bv ltac:(kk_in)); exact H21) ltac:(rewrite R24; exact H24) ltac:(rewrite R25; exact H25)
    ltac:(rewrite R10; unfold w64; f_equal; lia) Ham Hci Hi Hil Hfk).
Qed.

Lemma kk_all : TK_TAKE_KD SK B c -> forall fk, kk_P fk.
Proof.
  intros TKD fk. induction fk as [|fk IH].
  - intros ci a al l aa i il k _ regs mem md _ _ _ _ _ _ _ _ _ _ Hfk. cbn in Hfk. lia.
  - exact (kk_step TKD fk IH).
Qed.

(* THE PIECE: the inner loop, by induction on the fuel of kind_scan *)
Lemma tk_kind_ok : TK_TAKE_KD SK B c -> TK_KIND SK B c.
Proof.
  intros TKD ci a al l aa i il k fk K598 regs mem md HI Hrs0 Hrat H21 H24 H25 Ham Hci Hi Hil Hfk.
  exact (kk_all TKD fk ci a al l aa i il k K598 regs mem md HI Hrs0 Hrat H21 H24 H25 Ham Hci Hi Hil Hfk).
Qed.
End w.
