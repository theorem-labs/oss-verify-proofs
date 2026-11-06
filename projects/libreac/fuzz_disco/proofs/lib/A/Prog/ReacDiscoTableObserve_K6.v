(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 238 of its 275 lines of code are new or changed and 32 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI0m.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3u.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow DiscoSyms DiscoList DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve ReacDiscoTableObserve_C.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacDiscoTableObserve_M.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve_X.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_observe_c reac_disco_table_observe.
Module DTC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.disco_table_c.
Module RDOC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe_c.
Module RDO := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe.
Module TM := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog.ReacDiscoTableObserve_M.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma t456_ltu : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  (zcanon (bv_swrap 32 x) <? zcanon (bv_swrap 32 y)) = (x <? y).
Proof.
intros x y Hx Hy. apply Bool.eq_iff_eq_true. rewrite !Z.ltb_lt.
unfold zcanon, M64, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
split; intros H; Z.div_mod_to_equations; lia.
Qed.
Lemma t456_eq0 : forall x, 0 <= x < 2 ^ 32 -> (zcanon (bv_swrap 32 x) =? zcanon 0) = (bv_swrap 32 x =? 0).
Proof.
intros x Hx. apply Bool.eq_iff_eq_true. rewrite !Z.eqb_eq.
unfold zcanon, M64, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
split; intros H; Z.div_mod_to_equations; lia.
Qed.
Lemma t456_zc0 : forall x, -2 ^ 31 <= x < 2 ^ 31 -> (zcanon x =? zcanon 0) = (x =? 0).
Proof.
intros x Hx. apply Bool.eq_iff_eq_true. rewrite !Z.eqb_eq. unfold zcanon, M64.
split; intros H; [Z.div_mod_to_equations; lia | subst; reflexivity].
Qed.
Lemma t456_U_atom : forall E n x, ew E n = Z_to_bv 64 x -> U E (SOff n 0) = zcanon x.
Proof.
intros E n x H. rewrite U_SOff, H, Z.add_0_r, Z_to_bv_unsigned. unfold zcanon, bv_wrap, M64.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma t456_U_sx : forall E d s, U E (SExt true 32 (SData d s 4)) = zcanon (bv_swrap 32 (data_word E d s 4)).
Proof.
intros E d s. rewrite U_SExt. cbv iota. f_equal. f_equal.
pose proof (data_word_range E d s 4 ltac:(cbn; lia)) as R. change (8 * Z.of_N 4) with 32 in R.
change (Z.of_N 32) with 32. unfold U. cbn [sv_denot]. rewrite unsigned_lit_small by lia. apply Z.mod_small. lia.
Qed.
Lemma t456_dw_ent : forall E d s X r, ed E d = DTC.sub X (48 * r) 48 -> length X = 400%nat -> 0 <= r < 8 ->
  0 <= s -> s + 4 <= 48 -> data_word E d s 4 = DTC.u_at X (48 * r + s) 4.
Proof.
intros E d s X r Hd HX Hr Hs Hs4. unfold data_word. rewrite Hd.
rewrite <- (TM.u_at_ent X r s 4 HX Hr Hs ltac:(lia)). reflexivity.
Qed.
Lemma t456_dw : forall E d s X, ed E d = X -> data_word E d s 4 = DTC.u_at X s 4.
Proof. intros E d s X Hd. unfold data_word. rewrite Hd. reflexivity. Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Lemma t456_cbyte_sx : forall E a d s i X, ed E d = X -> 0 <= s -> (Z.to_nat s + 4 <= length X)%nat -> 0 <= i < 4 ->
  YP09.cbyte SEGS E a (CVal 4 (SExt true 32 (SData d s 4))) i = nth_error X (Z.to_nat (s + i)).
Proof.
intros E a d s i X Hd Hs Hl Hi. cbn [YP09.cbyte].
transitivity (Some (byte_of_word (Z_to_bv 64 (data_word E d s 4)) i)).
- f_equal. exact (byte_of_word_low32 true (Z_to_bv 64 (data_word E d s 4)) i Hi).
- rewrite <- (Z2Nat.id i) at 1 by lia. rewrite <- Hd in Hl |- *.
  rewrite (byte_of_data_word E d s 4 (Z.to_nat i) Hs Hl ltac:(cbn; lia) ltac:(cbn; lia)). f_equal. lia.
Qed.
Lemma t456_cbyte_one : forall E a i, 0 <= i < 4 ->
  YP09.cbyte SEGS E a (CVal 4 (SLit 1)) i = nth_error (Z_to_le_bytes 4 1) (Z.to_nat i).
Proof. intros E a i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as [-> | [-> | [-> | ->]]] by lia; reflexivity. Qed.
Lemma t456_cd_out : forall E b lo X koff v off d s len, ed E d = X -> 0 <= s -> 0 <= koff ->
  koff + Z.of_nat (length v) <= Z.of_nat (length X) ->
  (forall k, 0 <= k < len -> s + k = off + k - lo /\ 0 <= off + k - lo /\ ~ (koff <= off + k - lo < koff + Z.of_nat (length v))) ->
  cagree E b lo (DTC.upd X koff v) (YP09.mkChunk off (CData d s len)).
Proof.
intros E b lo X koff v off d s len Hd Hs Hk Hkv H. apply cagree_cdata; [exact Hs|].
intros k Hk'. destruct (H k Hk') as (H1 & H2 & H3). rewrite Hd, (TM.upd_nth_out X v koff (off + k - lo)) by lia.
rewrite H1. reflexivity.
Qed.
Lemma t456_cv_in : forall E b lo X koff v off w sv,
  0 <= koff -> koff + Z.of_nat (length v) <= Z.of_nat (length X) -> koff <= off - lo ->
  off - lo + Z.of_N w <= koff + Z.of_nat (length v) ->
  (forall i, 0 <= i < Z.of_N w -> YP09.cbyte SEGS E (b + off) (CVal w sv) i = nth_error v (Z.to_nat (off + i - lo - koff))) ->
  cagree E b lo (DTC.upd X koff v) (YP09.mkChunk off (CVal w sv)).
Proof.
intros E b lo X koff v off w sv Hk Hkv H1 H2 H i Hi. cbn [YP09.c_len YP09.c_val YP09.c_off YP09.cv_len] in Hi |- *.
rewrite (TM.upd_nth_in X v koff (off + i - lo)) by lia. apply H. exact Hi.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma t456_exit : forall c regs1 m1 md1 Tc E E2 so r regs2 m2 md2 Tc',
  tpre B c -> tobs_m B c regs1 m1 md1 Tc ->
  base_val E (Some 8%nat) = tt c -> base_val E (Some 19%nat) = tt c + 48 * r -> 0 <= r < 8 ->
  frame_of E (tobs_regions true so) (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) m2) ->
  mem_grows (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) m2) ->
  ajournal SEGS B (tSTK c) (tsp0 c) (tFP c) (tly c) (tS c) (tW0 c) (tmem0 c) (tmd0 c) (town c)
    (tlyc c) (tSc c) (tW c) m2 md2 (tk c) ->
  YP09.region_ok SEGS E2 (mrestrict (w_H (tW c)) m2) R_hdr -> base_val E2 (Some 8%nat) = tt c -> ed E2 0 = Tc ->
  length Tc' = 400%nat ->
  (forall i, 0 <= i < 400 -> ~ (48 * r <= i < 48 * r + 48) -> nth_error Tc' (Z.to_nat i) = nth_error Tc (Z.to_nat i)) ->
  (forall i, 0 <= i < 48 -> mbyte SEGS (mrestrict (w_H (tW c)) m2) (tt c + 48 * r + i) =
     nth_error (DTC.sub Tc' (48 * r) 48) (Z.to_nat (i - 0))) ->
  (forall q : Z, In q [2; 3; 4; 8; 9; 20; 21; 22; 24; 27] -> YK11.getr regs2 (Z_to_bv 5 q) = YK11.getr regs1 (Z_to_bv 5 q)) ->
  tobs_m B c regs2 m2 md2 Tc'.
Proof.
intros c regs1 m1 md1 Tc E E2 so r regs2 m2 md2 Tc' HP HM B8 B19 Hr HF HG HJ2 Rh B8' Ed0 HL' Hout Hent Hregs.
pose proof (tm_Tl _ _ _ _ _ _ HM) as HTl.
apply (tobs_exit_run B LAWS c regs1 m1 md1 Tc E true so r regs2 m2 md2 Tc' HP HM B8 (fun _ => conj B19 Hr) HF HG HJ2 HL').
- intros i Hi _ Hr'. apply Hout; [exact Hi | exact (Hr' eq_refl)].
- intros i Hi. rewrite Hout by lia.
  rewrite (region_bytes E2 _ 8 384 400 384 400 _ (tt c) (DTC.sub Tc 384 16) Rh B8' ltac:(vm_compute; reflexivity)) by
    (first [ lia
           | apply Forall_cons; [|apply Forall_nil]; apply cagree_cdata; [lia|]; intros k Hk; rewrite Ed0;
             rewrite nth_error_sub by lia; f_equal; lia ]).
  rewrite nth_error_sub by lia. f_equal. lia.
- intros _ i Hi. replace (tt c + i) with (tt c + 48 * r + (i - 48 * r)) by lia.
  rewrite (Hent (i - 48 * r)) by lia. rewrite nth_error_sub by lia. f_equal. lia.
- exact Hregs.
Qed.
Lemma t456_exit_same : forall c regs1 m1 md1 Tc E E2 so r regs2 m2 md2,
  tpre B c -> tobs_m B c regs1 m1 md1 Tc ->
  base_val E (Some 8%nat) = tt c -> base_val E (Some 19%nat) = tt c + 48 * r -> 0 <= r < 8 ->
  frame_of E (tobs_regions true so) (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) m2) ->
  mem_grows (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) m2) ->
  ajournal SEGS B (tSTK c) (tsp0 c) (tFP c) (tly c) (tS c) (tW0 c) (tmem0 c) (tmd0 c) (town c)
    (tlyc c) (tSc c) (tW c) m2 md2 (tk c) ->
  YP09.region_ok SEGS E2 (mrestrict (w_H (tW c)) m2) R_hdr -> YP09.region_ok SEGS E2 (mrestrict (w_H (tW c)) m2) R_ent ->
  base_val E2 (Some 8%nat) = tt c -> base_val E2 (Some 19%nat) = tt c + 48 * r ->
  ed E2 0 = Tc -> ed E2 2 = DTC.sub Tc (48 * r) 48 ->
  (forall q : Z, In q [2; 3; 4; 8; 9; 20; 21; 22; 24; 27] -> YK11.getr regs2 (Z_to_bv 5 q) = YK11.getr regs1 (Z_to_bv 5 q)) ->
  tobs_m B c regs2 m2 md2 Tc.
Proof.
intros c regs1 m1 md1 Tc E E2 so r regs2 m2 md2 HP HM B8 B19 Hr HF HG HJ2 Rh Re B8' B19' Ed0 Ed2 Hregs.
apply (t456_exit c regs1 m1 md1 Tc E E2 so r regs2 m2 md2 Tc HP HM B8 B19 Hr HF HG HJ2 Rh B8' Ed0 (tm_Tl _ _ _ _ _ _ HM));
  [intros; reflexivity | | exact Hregs].
apply (region_bytes E2 _ 19 0 48 0 48 _ (tt c + 48 * r) _ Re B19' ltac:(vm_compute; reflexivity)).
apply Forall_cons; [|apply Forall_nil]. apply cagree_cdata; [lia|]. intros k Hk. rewrite Ed2. f_equal. lia.
Qed.
End h.
End f.
End d.
Ltac t456_bv H := cbn [base_val ew ewset extK Nat.eqb]; exact H.
Ltac t456_awr B c HP B8 B19 Hr8 so r :=
  eapply (tobs_awr B c _ true so r HP); [t456_bv B8 | intros _; split; [t456_bv B19 | exact Hr8]].
Ltac t456_regs HS HS0 :=
  let q := fresh "q" in let Hq := fresh "Hq" in
  intros q Hq; cbn [In] in Hq;
  repeat (destruct Hq as [Hq | Hq];
    [ subst q;
      lazymatch goal with |- YK11.getr _ (Z_to_bv 5 ?k) = _ =>
        let R := fresh "R" in let R0 := fresh "R0" in
        prreg HS (Z_to_bv 5 k) R; prreg HS0 (Z_to_bv 5 k) R0; rewrite R, R0; reflexivity end
    | ]);
  destruct Hq.
Ltac t456_same B LAWS c regs1 Tc r HP HM B8 B19 Hr8 HS HS0 HFr HG HJ rg mm md :=
  let Rh := fresh "Rh" in let Re := fresh "Re" in
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as Rh; cbn [ms_mem restrict] in Rh;
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as Re; cbn [ms_mem restrict] in Re;
  lazymatch type of HFr with frame_of ?E1 _ _ _ =>
  lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
    exact (t456_exit_same B LAWS c regs1 _ _ Tc E1 E2 _ r rg mm md HP HM ltac:(t456_bv B8) ltac:(t456_bv B19) Hr8
      HFr HG HJ Rh Re ltac:(t456_bv B8) ltac:(t456_bv B19) eq_refl eq_refl ltac:(t456_regs HS HS0))
  end end.
Ltac t456_mid B LAWS c regs1 Tc r HP HM B8 B19 Hr8 HS HFr HG HJ mm md :=
  let Rh := fresh "Rh" in let Re := fresh "Re" in
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as Rh; cbn [ms_mem restrict] in Rh;
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as Re; cbn [ms_mem restrict] in Re;
  lazymatch type of HFr with frame_of ?E1 _ _ _ =>
  lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
    exact (t456_exit_same B LAWS c regs1 _ _ Tc E1 E2 _ r regs1 mm md HP HM ltac:(t456_bv B8) ltac:(t456_bv B19) Hr8
      HFr HG HJ Rh Re ltac:(t456_bv B8) ltac:(t456_bv B19) eq_refl eq_refl (fun _ _ => eq_refl))
  end end.
Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h2.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Lemma seg_K6 : forall c, SegSeq B c -> SegRet B c -> SegK6 B c.
Proof.
intros c HSEQ HRET regs1 m1 md1 r HP HM H18 H19 H12 Hfd HcO.
remember (RDO.kF (tT c) (tG c) (tnow c) r) as Tc eqn:HTc.
pose proof (tm_J _ _ _ _ _ _ HM) as HJ.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63.
pose proof (tp_s0 _ _ HP) as Hs0. pose proof (tp_s63 _ _ HP) as Hs63.
pose proof (tp_Tl _ _ HP) as HTl. pose proof (tp_Gl _ _ HP) as HGl.
pose proof (tp_T1 _ _ HP) as HT1. unfold DTC.tbl_T1 in HT1.
destruct Hfd as (Hrn & Hm & Hb).
assert (Hr8 : 0 <= r < 8) by lia.
assert (B8 : base_val (tobs_env c regs1 Tc r) (Some 8%nat) = tt c).
{ cbn [base_val]. rewrite (tobs_env_reg c regs1 Tc r 8 8%bv eq_refl), (tm_s0 _ _ _ _ _ _ HM). apply unsigned_lit_small. lia. }
assert (B19 : base_val (tobs_env c regs1 Tc r) (Some 19%nat) = tt c + 48 * r).
{ cbn [base_val]. rewrite (tobs_env_reg c regs1 Tc r 19 19%bv eq_refl), H19. apply unsigned_lit_small. lia. }
pose proof (tobs_env_img c regs1 Tc r) as HEI.
assert (H18' : YK11.getr regs1 18 = w64 (ts c - -20)) by (rewrite H18; f_equal; lia).
destruct (tobs_enter B c regs1 m1 md1 Tc 0x53bc true r (-20) HP HM (or_intror eq_refl) H18' (fun _ => conj Hr8 H19))
  as [HS SHOK].
pose proof HS as HS0.
unfold cfgB.
psrr_branch_tok RUN BR HS SHOK TBspan.
- rewrite branch_eq_U, (t456_U_atom _ 12 (Z.b2z (tf5 c r))), U_SLit in Hc
    by (rewrite (tobs_env_reg c regs1 Tc r 12 12%bv eq_refl); exact H12).
  destruct (tf5 c r) eqn:Htf; vm_compute in Hc; [discriminate Hc|]. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x55f0; [t456_awr B c HP B8 B19 Hr8 (-20) r |].
  rewrite ?wvb_collapse in HJ.
  prreg HS (18%bv : bv 5) G18r. prreg HS (10%bv : bv 5) G10r.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (?mk ?rg _ ?mm _) ?md) _ =>
    assert (HM2 : tobs_m B c rg mm md Tc) by t456_same B LAWS c regs1 Tc r HP HM B8 B19 Hr8 HS HS0 HFr HG HJ rg mm md;
    assert (Hmod : RDOC.observe_model (tT c) (tG c) (tow c) (tnow c) Tc 0);
    [ pose proof (TM.model_known (tT c) (tG c) (tow c) (tnow c) r HTl HGl Hrn Hm Hb) as X;
      rewrite RDO.known_eq in X; unfold tf5, tf4, tf3, tf2, tf1 in Htf; rewrite Htf, HcO in X; cbn [orb fst snd] in X;
      unfold RDO.kG in X; rewrite HcO, <- HTc in X; exact X
    | ];
    apply (HRET rg mm md Tc (-20) 0 HP HM2 (or_intror eq_refl));
    [ rewrite G18r, (tobs_env_reg c regs1 Tc r 18 18%bv eq_refl); exact H18'
    | exact G10r
    | exact Hmod ]
  end.
- rewrite branch_eq_U, (t456_U_atom _ 12 (Z.b2z (tf5 c r))), U_SLit in Hc
    by (rewrite (tobs_env_reg c regs1 Tc r 12 12%bv eq_refl); exact H12).
  destruct (tf5 c r) eqn:Htf; vm_compute in Hc; [|discriminate Hc]. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x55d0; [t456_awr B c HP B8 B19 Hr8 (-20) r |].
  rewrite ?wvb_collapse in HJ.
  prreg HS (18%bv : bv 5) G18r. prreg HS (10%bv : bv 5) G10r.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (?mk ?rg _ ?mm _) ?md) _ =>
    assert (HM2 : tobs_m B c rg mm md Tc) by t456_same B LAWS c regs1 Tc r HP HM B8 B19 Hr8 HS HS0 HFr HG HJ rg mm md;
    assert (Hmod : RDOC.observe_model (tT c) (tG c) (tow c) (tnow c)
      (DTC.upd Tc 392 (Z_to_le_bytes 4 (DTC.seq_of Tc + 1))) 1);
    [ destruct (TM.stage_reads (tT c) (tG c) (tow c) (tnow c) r HTl HGl Hr8) as (_ & _ & _ & _ & _ & _ & _ & _ & S9);
      pose proof (TM.model_known (tT c) (tG c) (tow c) (tnow c) r HTl HGl Hrn Hm Hb) as X;
      rewrite RDO.known_eq in X; unfold tf5, tf4, tf3, tf2, tf1 in Htf; rewrite Htf in X; cbn [orb fst snd] in X;
      unfold RDO.kG in X, S9; rewrite HcO, <- HTc in X, S9;
      replace (DTC.seq_of Tc) with (DTC.seq_of (tT c)) by (unfold DTC.seq_of; exact (eq_sym S9)); exact X
    | ];
    apply (HSEQ rg mm md Tc (-20) 1 HP HM2 (or_intror eq_refl));
    [ rewrite G18r, (tobs_env_reg c regs1 Tc r 18 18%bv eq_refl); exact H18'
    | exact G10r
    | exact Hmod ]
  end.
Qed.
End h2.
End f2.
End d2.
