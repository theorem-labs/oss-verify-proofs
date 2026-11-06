(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 167 of its 204 lines of code are new or changed and 32 lines of the source are left out. *)
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
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Lemma cagree_cdata : forall E b lo L off d s len, 0 <= s ->
  (forall i, 0 <= i < len -> nth_error (ed E d) (Z.to_nat (s + i)) = nth_error L (Z.to_nat (off + i - lo))) ->
  cagree E b lo L (YP09.mkChunk off (CData d s len)).
Proof. intros E b lo L off d s len Hs H i Hi. exact (H i Hi). Qed.
Lemma aview_eq_nth : forall H m p (L : list byte) q (G : list byte) k i,
  garr8 SEGS (mrestrict H m) p (map (fun b : byte => bv_unsigned b) L) ->
  garr8 SEGS (mrestrict H m) q (map (fun b : byte => bv_unsigned b) G) ->
  (k < length L)%nat -> (i < length G)%nat ->
  (aview SEGS H m (p + Z.of_nat k) = aview SEGS H m (q + Z.of_nat i) <-> nth_error L k = nth_error G i).
Proof.
intros H m p L q G k i HL HG Hk Hi.
rewrite (aview_of_garr8 H m p L k HL Hk), (aview_of_garr8 H m q G i HG Hi).
rewrite (nth_error_nth' L (Z_to_bv 8 0) Hk), (nth_error_nth' G (Z_to_bv 8 0) Hi).
split; intros E; injection E as E; [f_equal; apply bv_eq; exact E | rewrite E; reflexivity].
Qed.
Lemma hull_sub : forall (rd : Z -> option Z) x n y k, shadow_hull_vis rd x n -> x <= y -> y + k <= x + n -> 0 < k -> 0 <= x ->
  shadow_hull_vis rd y k.
Proof.
intros rd x n y k H Hxy Hyk Hk Hx s Hs. apply H. unfold shadow_addr in *.
assert (A1 : x / 8 <= y / 8) by (apply Z.div_le_mono; lia).
assert (A2 : (SHADOW_OFF + x / 8) / 8 <= (SHADOW_OFF + y / 8) / 8) by (apply Z.div_le_mono; lia).
assert (A3 : (y + k - 1) / 8 <= (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
assert (A4 : (SHADOW_OFF + (y + k - 1) / 8) / 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.
Lemma tobs_reg_same : forall c regs1 Tc r E' ss ms H (q : bv 5),
  st_ok SEGS E' ss (restrict H ms) -> regs_ok (tobs_env c regs1 Tc r) tobs_sr regs1 ->
  sr_get (ss_regs ss) q = sr_get tobs_sr q -> sv_atoms_lt 32 (sr_get tobs_sr q) = true ->
  env_agree 32 (tobs_env c regs1 Tc r) E' ->
  YK11.getr (ms_regs ms) q = YK11.getr regs1 q.
Proof.
intros c regs1 Tc r E' ss ms H q HS HR Hq Hat HA.
rewrite (st_ok_restrict_reg SEGS H E' ss ms q HS), Hq, (sv_denot_agree 32 _ _ _ HA Hat).
symmetry. exact (HR q).
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Lemma tobs_post_intro : forall c regs2 m2 md2 T' ret,
  tpre B c ->
  ajournal SEGS B (tSTK c) (tsp0 c) (tFP c) (tly c) (tS c) (tW0 c) (tmem0 c) (tmd0 c) (town c)
    (tlyc c) (tSc c) (tW c) m2 md2 (tk c) ->
  aregs_preserved (tregs c) regs2 -> YK11.getr regs2 10 = w64 ret ->
  tobs_kept B c m2 ->
  garr8 SEGS (mrestrict (w_H (tW c)) m2) (tt c) (map (fun b : byte => bv_unsigned b) T') -> length T' = 400%nat ->
  garr8 SEGS (mrestrict (w_H (tW c)) m2) (ts c) (map (fun b : byte => bv_unsigned b) (tG c)) ->
  RDOC.observe_model (tT c) (tG c) (tow c) (tnow c) T' ret ->
  tpost B c (tW c) (mkCfg (YK11.mkst regs2 (YK11.getr (tregs c) 1) m2 (YK11.seg_rom SEGS)) md2).
Proof.
intros c regs2 m2 md2 T' ret HP HJ HPr H10 HK HT HL HG HM.
destruct (RDO.observe_model_tbl (tT c) (tG c) (tow c) (tnow c) T' ret (tp_Tl _ _ HP) (tp_Gl _ _ HP)
  (tp_T1 _ _ HP) (tp_T2 _ _ HP) (tp_T3 _ _ HP) (tp_S1 _ _ HP) (tp_S2 _ _ HP) HM) as (T1 & T2 & T3 & T4).
unfold tpost, treac_disco_table_observe_post.
exists (tlyc c), (tSc c), regs2, m2, md2, T', ret.
split; [reflexivity|]. split; [exact HJ|]. split; [exact HPr|]. split; [exact H10|].
split; [reflexivity|]. split; [apply Permutation_refl|]. split; [exact HK|].
split; [exact HT|]. split; [exact HL|]. split; [exact HG|]. split; [exact HM|].
split; [exact T1|]. split; [exact T2|]. split; [exact T3 | exact T4].
Qed.
Lemma tobs_exit_nostore : forall c regs1 m1 md1 Tc so E' m2 md2 regs2,
  tpre B c -> tobs_m B c regs1 m1 md1 Tc -> (so = 0 \/ so = -20) ->
  frame_of (tobs_env c regs1 Tc 0) (tobs_regions false so) (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) m2) ->
  mem_grows (mrestrict (w_H (tW c)) m1) (mrestrict (w_H (tW c)) m2) ->
  ajournal SEGS B (tSTK c) (tsp0 c) (tFP c) (tly c) (tS c) (tW0 c) (tmem0 c) (tmd0 c) (town c)
    (tlyc c) (tSc c) (tW c) m2 md2 (tk c) ->
  YP09.region_ok SEGS E' (mrestrict (w_H (tW c)) m2) R_hdr -> base_val E' (Some 8%nat) = tt c -> ed E' 0 = Tc ->
  (forall q : Z, In q [2; 3; 4; 8; 9; 20; 21; 22; 24; 27] -> YK11.getr regs2 (Z_to_bv 5 q) = YK11.getr regs1 (Z_to_bv 5 q)) ->
  tobs_m B c regs2 m2 md2 Tc.
Proof.
intros c regs1 m1 md1 Tc so E' m2 md2 regs2 HP HM Hso HF HG HJ2 Hreg B8' Hed Hregs.
assert (B8 : base_val (tobs_env c regs1 Tc 0) (Some 8%nat) = tt c).
{ cbn [base_val]. rewrite (tobs_env_reg c regs1 Tc 0 8 8%bv eq_refl), (tm_s0 _ _ _ _ _ _ HM).
  pose proof (tp_t0 _ _ HP). pose proof (tp_t63 _ _ HP). apply unsigned_lit_small. lia. }
apply (tobs_exit_run B LAWS c regs1 m1 md1 Tc (tobs_env c regs1 Tc 0) false so 0 regs2 m2 md2 Tc HP HM B8
  ltac:(discriminate) HF HG HJ2 (tm_Tl _ _ _ _ _ _ HM)).
- intros; reflexivity.
- intros i Hi. unfold R_hdr in Hreg.
  rewrite (region_bytes E' _ 8 384 400 384 400 _ (tt c) (DTC.sub Tc 384 16) Hreg B8' ltac:(vm_compute; reflexivity)) by
    (first [ lia
           | apply Forall_cons; [|apply Forall_nil]; apply cagree_cdata; [lia|]; intros k Hk; rewrite Hed;
             rewrite nth_error_sub by lia; f_equal; lia ]).
  rewrite nth_error_sub by lia. f_equal. lia.
- discriminate.
- exact Hregs.
Qed.
Lemma tobs_bcmp : forall c regsT memT mdT Tc j ret Q,
  tpre B c -> tobs_m B c regsT memT mdT Tc -> 0 <= j < 8 ->
  YK11.getr regsT 10 = w64 (tt c + 48 * j) -> YK11.getr regsT 11 = w64 (ts c) -> YK11.getr regsT 12 = w64 6 ->
  YK11.getr regsT 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  (forall regs2 mem2 md2 (v : word), tobs_m B c regs2 mem2 md2 Tc -> aregs_preserved regsT regs2 -> YK11.getr regs2 10 = v ->
     (v = w64 0 <-> forall i, 0 <= i < 6 -> nth_error Tc (Z.to_nat (48 * j + i)) = nth_error (tG c) (Z.to_nat i)) ->
     SRr SEGS (tW c) (mkCfg (YK11.mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (YK11.seg_rom SEGS)) md2) Q) ->
  SRr SEGS (tW c) (mkCfg (YK11.mkst regsT (Z_to_bv 64 (SIGMA DS___interceptor_trampoline_bcmp)) memT (YK11.seg_rom SEGS)) mdT) Q.
Proof.
intros c regsT memT mdT Tc j ret Q HP HM Hj H10 H11 H12 H1 Hret0 Hret2 HK.
pose proof (tm_J _ _ _ _ _ _ HM) as HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (tp_wlo _ _ HP) as Hwlo. pose proof (tp_whi _ _ HP) as Hwhi. pose proof (tp_al _ _ HP) as Hal.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63. pose proof (tp_tam _ _ HP) as Htam. pose proof (tp_twin _ _ HP) as Htwin.
pose proof (tp_s0 _ _ HP) as Hs0. pose proof (tp_s63 _ _ HP) as Hs63. pose proof (tp_sam _ _ HP) as Hsam. pose proof (tp_swin _ _ HP) as Hswin.
pose proof (tp_Gl _ _ HP) as HGl.
pose proof (tm_sp _ _ _ _ _ _ HM) as Hsp. pose proof (tm_Tl _ _ _ _ _ _ HM) as HTl.
pose proof (tm_T _ _ _ _ _ _ HM) as HT. pose proof (tm_G _ _ _ _ _ _ HM) as HG.
pose proof (tm_tra _ _ _ _ _ _ HM) as Htra. pose proof (tm_sra _ _ _ _ _ _ HM) as Hsra.
pose proof (tm_thull _ _ _ _ _ _ HM) as Hthull. pose proof (tm_shull _ _ _ _ _ _ HM) as Hshull.
pose proof (tm_tpres _ _ _ _ _ _ HM) as Htpres. pose proof (tm_spres _ _ _ _ _ _ HM) as Hspres.
assert (STK : REAC_DISCO_TABLE_OBSERVE_STK = 8288) by reflexivity. rewrite STK in Hwlo, Htwin, Hswin.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam, Hsam.
pose proof (Z.div_mod (tsp0 c) 16 ltac:(lia)) as D0. rewrite Hsp0al, Z.add_0_r in D0.
pose proof (Z.div_mod (spZ (tregs c)) 16 ltac:(lia)) as D1. rewrite Hal, Z.add_0_r in D1.
assert (Hes : ESTACK = 4096) by reflexivity.
eapply SRr_bind.
{ eapply (aj_bcmp_at SEGS B LAWS pa_segs_low _ (ABCMP fx) (tW c) regsT memT (tSTK c) (tsp0 c) (tFP c) (tly c) (tS c)
    (tW0 c) (tmem0 c) (tmd0 c) (town c) (tlyc c) (tSc c) mdT (tk c) (tt c + 48 * j) (ts c) 6 (spZ regsT - tsp0 c)
    (Z_to_bv 64 (BASE + ret)) HJ H10 H11 H12).
  - lia. - lia. - lia. - lia. - lia. - lia.
  - replace (spZ regsT - tsp0 c) with ((spZ (tregs c) / 16 - 6 - tsp0 c / 16) * 16) by lia. apply Z_mod_mult.
  - lia. - rewrite Hes. lia.
  - rewrite (tm_gp _ _ _ _ _ _ HM). exact (tp_gp _ _ HP).
  - rewrite (tm_tp _ _ _ _ _ _ HM). exact (tp_tp _ _ HP).
  - exact H1.
  - apply ret_ok_codeptr_v; lia.
  - intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply Htpres; lia | rewrite Hes; lia].
  - intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply Hspres; lia | rewrite Hes; lia].
  - intros a Ha. rewrite Hes. lia.
  - intros a Ha. rewrite Hes. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - eapply range_addressable_sub; [exact Htra | lia | lia].
  - intros _. eapply hull_sub; [exact Hthull | lia | lia | lia | lia].
  - eapply range_addressable_sub; [exact Hsra | lia | lia].
  - intros _. eapply hull_sub; [exact Hshull | lia | lia | lia | lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpr2).
assert (Hkt : forall a, tt c <= a < tt c + 400 -> aview SEGS (w_H (tW c)) mem2 a = aview SEGS (w_H (tW c)) memT a).
{ intros a Ha. apply Hfr; [lia | rewrite Hes; lia]. }
assert (Hks : forall a, ts c <= a < ts c + 24 -> aview SEGS (w_H (tW c)) mem2 a = aview SEGS (w_H (tW c)) memT a).
{ intros a Ha. apply Hfr; [lia | rewrite Hes; lia]. }
apply (HK regs2 mem2 md2 v).
- apply (tobs_m_step B LAWS c regsT memT mdT Tc regs2 mem2 md2 Tc HP HM HJ2).
  + intros a Ha Ht Hw. apply Hfr; [exact Ha | rewrite Hes; lia].
  + exact Hpr2.
  + eapply garr8_aview_kept; [|exact HT]. intros a Ha. rewrite length_map, HTl in Ha. apply Hkt. lia.
  + exact HTl.
  + intros q Hq. apply HP2. unfold acallee_saved. cbn in Hq. lia.
- exact HP2.
- exact Hv.
- rewrite Hcmp. split; intros X i Hi; specialize (X i Hi).
  + pose proof (aview_eq_nth (w_H (tW c)) memT (tt c) Tc (ts c) (tG c) (Z.to_nat (48 * j + i)) (Z.to_nat i) HT HG
      ltac:(lia) ltac:(lia)) as Q'.
    rewrite !Z2Nat.id in Q' by lia. apply Q'. replace (tt c + (48 * j + i)) with (tt c + 48 * j + i) by lia. exact X.
  + pose proof (aview_eq_nth (w_H (tW c)) memT (tt c) Tc (ts c) (tG c) (Z.to_nat (48 * j + i)) (Z.to_nat i) HT HG
      ltac:(lia) ltac:(lia)) as Q'.
    rewrite !Z2Nat.id in Q' by lia. replace (tt c + 48 * j + i) with (tt c + (48 * j + i)) by lia. apply Q'. exact X.
Qed.
End h.
End f.
End d.
