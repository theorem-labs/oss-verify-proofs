(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC1f.v, with its module paths and module names changed; 1310 of its 1364 lines of code are new or changed and 437 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacMasterOnlyCadenceNs.v, with its module paths and module names changed; 222 of its 290 lines of code are new or changed and 1296 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0s YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_rate_snap_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_rate_snap.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma rs_rg_other : forall (m : bvmap 5 word) (k k' : bv 5) (v : word),
  bv_unsigned k <> bv_unsigned k' -> Sem.reg_get (bvmap_set k v m) k' = Sem.reg_get m k'.
Proof.
intros m k k' v H. unfold Sem.reg_get. rewrite bvmap_get_set_other; [reflexivity|].
intros X. apply H. rewrite X. reflexivity.
Qed.
Lemma rs_rg_same : forall (m : bvmap 5 word) (k : bv 5) (v : word), Sem.reg_get (bvmap_set k v m) k = v.
Proof. intros m k v. unfold Sem.reg_get. rewrite bvmap_get_set_same. reflexivity. Qed.
Lemma rs_getr_s0 : forall (regs : bvmap 5 word) (v : word) (r : bv 5),
  bv_unsigned r <> 8 -> getr (regupd regs 8 v) r = getr regs r.
Proof.
intros regs v r Hr. unfold getr, regupd. destruct (bv_eqb r 0); [reflexivity|].
apply rs_rg_other. intros X. apply Hr. rewrite <- X. reflexivity.
Qed.
Lemma rs_spZ_s0 : forall (regs : bvmap 5 word) (v : word), spZ (regupd regs 8 v) = spZ regs.
Proof.
intros regs v. unfold spZ. rewrite rs_getr_s0; [reflexivity|].
intros X. vm_compute in X. discriminate.
Qed.
Lemma rs_step_flt : forall (F : bvmap 5 word) (fc : bv 32) segs regs pc mem rom w (rd rs1 rs2 : bv 5) (x y : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcmp F_LT FMT_D rd rs1 rs2, 4%Z) ->
  Sem.reg_get F rs1 = x -> Sem.reg_get F rs2 = y ->
  RiscvSemantics.step segs (@mkst (mkFP F fc) regs pc mem rom) =
  MachineOk (@mkst (mkFP F (Z_to_bv 32 (Z.lor (bv_unsigned fc)
      (fflags_bits (FP.fcmp_fl F_LT fmt_double (bv_unsigned x) (bv_unsigned y))))))
    (if bv_eqb rd 0 then regs else regupd regs rd (if FP.flt_d x y then Z_to_bv 64 1 else Z_to_bv 64 0))
    (v_addi pc 4) mem rom).
Proof.
intros F fc segs regs pc mem rom w rd rs1 rs2 x y Hf He Hd Hx Hy.
assert (E1 : FP.fcmp_fl F_LT fmt_double (bv_unsigned x) (bv_unsigned y) = snd (fp_lt fmt_double (bv_unsigned x) (bv_unsigned y))) by reflexivity.
assert (E2 : FP.flt_d x y = fst (fp_lt fmt_double (bv_unsigned x) (bv_unsigned y))) by reflexivity.
rewrite E1, E2.
fp_pipeline Hf He Hd.
cbv beta iota. change (fp_format FMT_D) with fmt_double. rewrite Hx, Hy.
destruct (fp_lt fmt_double (bv_unsigned x) (bv_unsigned y)) as [v fl]. cbn [fst snd].
rewrite b_npc4. unfold regupd. destruct (is_x0 rd); reflexivity.
Qed.
Lemma rs_fcsr : forall (x : word) (fc : bv 32),
  Z_to_bv 32 (Z.lor (bv_unsigned (Z_to_bv 32 (Z.lor (bv_unsigned fc)
      (fflags_bits (FP.fcmp_fl F_LT fmt_double (bv_unsigned x) (bv_unsigned (Z_to_bv 64 D6000)))))))
    (fflags_bits (FP.fcmp_fl F_LT fmt_double (bv_unsigned x) (bv_unsigned (Z_to_bv 64 D3837)))))
  = reac_rate_snap_fcsr x fc.
Proof.
intros x fc.
change (bv_unsigned (Z_to_bv 64 D6000)) with 4663319084467748864.
change (bv_unsigned (Z_to_bv 64 D3837)) with 4660657166816903168.
exact (reac_rate_snap.fcsr_nan x fc).
Qed.
Lemma rs_slit : forall (E : env) (b : bool),
  sv_denot E (SLit (if b then 1 else 0)) = (if b then Z_to_bv 64 1 else Z_to_bv 64 0).
Proof. intros E b. destruct b; reflexivity. Qed.
Definition rs_bytes (v : Z) : list byte := map (fun k => Z_to_bv 8 (le_byte v 8 k)) (seq 0 8).
Lemma rs_val6000 : bv_extract 0 64 (le_bytes_to_word (rs_bytes D6000)) = Z_to_bv 64 D6000.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma rs_val3837 : bv_extract 0 64 (le_bytes_to_word (rs_bytes D3837)) = Z_to_bv 64 D3837.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Definition RS_SB : Z := 0x7fff8000.
Definition rs_Bx : sv := SLit RS_SB.
Definition rs_Bspan : Z * Z := (RS_SB, RS_SB + 2 ^ 44 - 1).
Definition rs_ss0 : sstate := mkSS AF_reac_rate_snap sr_atoms [] None (mkFacts [] [] []).
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Lemma rs_fetch : forall k w, plookup (@pl_tpi disco_listing PL_disco) k = Some (PW w) ->
  fetch_word SEGS (Z_to_bv 64 (BASE + k)) = Some (Z_to_bv 32 w).
Proof.
intros k w Hpl. rewrite <- pl_tpi_eq in Hpl.
pose proof (cert_slot dsym (clookup pa_tbl) VAL SIGMA disco_listing pa_cert _ _ Hpl) as (Hck & _ & _).
unfold pi_slot_check in Hck. cbv zeta in Hck.
destruct (clookup pa_tbl (BASE + k)) as [wz|] eqn:Hl; [|discriminate Hck].
apply Z.eqb_eq in Hck. subst wz. apply pa_fetch_ok. exact Hl.
Qed.
Lemma rs_pc4 : forall k k', k' = k + 4 -> 0 <= k < 2 ^ 40 ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = Z_to_bv 64 (BASE + k').
Proof.
intros k k' Hk' Hk. pose proof pa_B_ok as HB. unfold v_addi.
rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.
Lemma rs_rdn8 : forall m a v, val_mem SEGS m a 8 v -> rdn SEGS m (Z_to_bv 64 a) 8 = Some (rs_bytes v).
Proof.
intros m a v H. apply (mbytes_at_rdn SEGS m a (rs_bytes v)).
intros j Hj. cbn [length rs_bytes map seq] in Hj.
destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; try lia; cbn [nth_error rs_bytes map seq]; apply H; lia.
Qed.
Definition rs_E (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Lemma rs_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) mem,
  @st_ok_pi SEGS VAL fq (rs_E regs) rs_ss0
    (restrict (w_H W) (@mkst fq regs (Z_to_bv 64 (BASE + AF_reac_rate_snap)) mem (seg_rom SEGS)))
  /\ YCbn.sh_ok SEGS rs_Bx [] (rs_E regs) (mrestrict (w_H W) mem).
Proof.
intros fq W regs mem. rewrite restrict_mkst_fx. split.
- unfold rs_ss0. apply pa_entry_st_ok_full.
  + unfold rs_E. apply (regs_ok_agree 32 (Ereg regs [])).
    * split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
    * vm_compute. reflexivity.
    * apply regs_ok_Ereg.
  + reflexivity.
  + constructor.
  + exact I.
  + split; [exact I | split; exact I].
- constructor.
Qed.
Lemma rs_regs_ok : forall (fq : YK11.FPState) E ss ms (H : word -> bool),
  @st_ok_pi SEGS VAL fq E ss (restrict H ms) -> regs_ok E (ss_regs ss) (ms_regs ms).
Proof. intros fq E ss ms H HS r. exact (st_ok_pi_restrict_reg H E ss ms r HS). Qed.
Lemma rs_switch : forall (fq fq' : YK11.FPState) E ss ms (H : word -> bool) sr' R' pc',
  @st_ok_pi SEGS VAL fq E ss (restrict H ms) -> regs_ok E sr' R' ->
  @st_ok_pi SEGS VAL fq' E (mkSS pc' sr' (ss_mem ss) None (ss_facts ss))
    (restrict H (@mkst fq' R' (Z_to_bv 64 (BASE + pc')) (ms_mem ms) (seg_rom SEGS))).
Proof.
intros fq fq' E ss ms H sr' R' pc' HS HR.
destruct HS as (_ & _ & _ & _ & _ & _ & _ & Hm & Hf).
exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj HR (conj Hm Hf)))))))).
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Definition REAC_RATE_SNAP_STK : Z := ESTACK.
Definition treac_rate_snap_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  : world SEGS -> config -> Prop :=
  fun W' c' => exists fq' : YK11.FPState,
    @YK11.fp_regs fq' = bvmap_set (Z_to_bv 5 14) (Z_to_bv 64 D3837)
                          (bvmap_set (Z_to_bv 5 15) (Z_to_bv 64 D6000) (@YK11.fp_regs fq)) /\
    @YK11.fp_csr fq' = reac_rate_snap_fcsr (Sem.reg_get (@YK11.fp_regs fq) (Z_to_bv 5 10)) (@YK11.fp_csr fq) /\
    apost_base (fx := fq') SEGS B REAC_RATE_SNAP_STK [] regs ly S W mem md 0
      (fun ly' S' W' regs' mem' md' =>
         getr regs' 10 = w64 (reac_rate_snap_model (Sem.reg_get (@YK11.fp_regs fq) (Z_to_bv 5 10))) /\
         Permutation (ablocks B ly' S') (ablocks B ly S) /\
         W' = W /\ (forall x, mem' x = mem x)) W' c'.
Definition treac_rate_snap_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch,
  afn_pre SEGS B REAC_RATE_SNAP_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 97) + -1832) 8 D6000 ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 96) + -1628) 8 D3837 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_rate_snap) regs mem md)
    (treac_rate_snap_post fq regs ly S W mem md).
Lemma rs_step_keep : forall (W : world SEGS) (f f' : YK11.FPState) R R' pc pc' mem md Q STK sp0 FPl ly S W0 mem0 md0 own lyc Sc k,
  RiscvSemantics.step SEGS (@mkst f R pc (mrestrict (w_H W) mem) (seg_rom SEGS)) =
    MachineOk (@mkst f' R' pc' (mrestrict (w_H W) mem) (seg_rom SEGS)) ->
  ajournal SEGS B STK sp0 FPl ly S W0 mem0 md0 own lyc Sc W mem md k ->
  (forall md', ajournal SEGS B STK sp0 FPl ly S W0 mem0 md0 own lyc Sc W mem md' k ->
     SRr SEGS W (mkCfg (@mkst f' R' pc' mem (seg_rom SEGS)) md') Q) ->
  SRr SEGS W (mkCfg (@mkst f R pc mem (seg_rom SEGS)) md) Q.
Proof.
intros W f f' R R' pc pc' mem md Q STK sp0 FPl ly S W0 mem0 md0 own lyc Sc k Hst HJ Hk.
eapply (SRr_step SEGS pa_wx W); [reflexivity | rewrite restrict_mkst_fx; exact Hst |].
intros md' Hs. rewrite (same_but_materialized_wvb md md' Hs).
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
apply Hk. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.
Theorem pb_reac_rate_snap : treac_rate_snap_spec.
Proof.
unfold treac_rate_snap_spec.
intros fq ly S W regs mem md ch HPRE HRO H6000 H3837.
destruct fq as [F fc].
pose proof (ajournal_init SEGS B REAC_RATE_SNAP_STK [] ly S W _ mem md ch HPRE) as HJ.
rewrite rs_spZ_s0 in HJ.
pose proof HPRE as (_ & Hra & _).
rewrite rs_getr_s0 in Hra by (intros X; vm_compute in X; discriminate).
unfold YK0s.ret_ok in Hra.
destruct (rs_entry (mkFP F fc) W regs mem) as [HS SHOK].
remember (rs_E regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E1 : ew E 1 = getr regs 1)
  by (subst E; unfold rs_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_reac_rate_snap)) with (Z_to_bv 64 (BASE + AF_reac_rate_snap)).
pose proof (paj_run (fx := mkFP F fc) B LAWS) as RUN0.
paj_run_tok RUN0 HS HJ SHOK rs_Bspan; [apply awr_ok_nil |].
lazymatch goal with HF : frame_of _ ?rs mem (ms_mem ?m1) |- _ =>
  pose proof (frame_of_read_only _ rs _ _ eq_refl HF) as HM; clear HF end.
rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl); cbn [ss_pc].
rewrite HM in HJ, SHOK |- *.
pose proof (rs_regs_ok _ _ _ _ _ HS) as HRG.
prreg HS (Z_to_bv 5 11) R11. prreg HS (Z_to_bv 5 10) R10.
eapply (rs_step_keep W); [ | exact HJ | clear HJ; intros md1 HJ].
{ rewrite (fp_step_fld (mkFP F fc) SEGS (ms_regs ms) (Z_to_bv 64 (BASE + 31480)) (mrestrict (w_H W) mem) (seg_rom SEGS)
    (Z_to_bv 32 2374350727) (Z_to_bv 5 15) (Z_to_bv 5 11) (Z_to_bv 12 2264)
    (Z_to_bv 64 (VAL (A_HI 97) + -1832)) (rs_bytes D6000)).
  - cbn [YK11.fp_regs YK11.fp_csr]. rewrite rs_val6000, (rs_pc4 31480 31484) by lia. reflexivity.
  - apply rs_fetch. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_refl_bv.
  - unfold v_addi. rewrite R11, (HEI 417%nat) by (unfold A_TEXT, A_LIM; lia).
    replace (bv_signed (Z_to_bv 12 2264)) with (-1832) by (vm_compute; reflexivity). reflexivity.
  - apply rs_rdn8. exact H6000. }
eapply (rs_step_keep W); [ | exact HJ | clear HJ; intros md2 HJ].
{ rewrite (fp_step_fld _ SEGS (ms_regs ms) (Z_to_bv 64 (BASE + 31484)) (mrestrict (w_H W) mem) (seg_rom SEGS)
    (Z_to_bv 32 2588227335) (Z_to_bv 5 14) (Z_to_bv 5 10) (Z_to_bv 12 2468)
    (Z_to_bv 64 (VAL (A_HI 96) + -1628)) (rs_bytes D3837)).
  - cbn [YK11.fp_regs YK11.fp_csr]. rewrite rs_val3837, (rs_pc4 31484 31488) by lia. reflexivity.
  - apply rs_fetch. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_refl_bv.
  - unfold v_addi. rewrite R10, (HEI 416%nat) by (unfold A_TEXT, A_LIM; lia).
    replace (bv_signed (Z_to_bv 12 2468)) with (-1628) by (vm_compute; reflexivity). reflexivity.
  - apply rs_rdn8. exact H3837. }
eapply (rs_step_keep W); [ | exact HJ | clear HJ; intros md3 HJ].
{ rewrite (rs_step_flt _ fc SEGS (ms_regs ms) (Z_to_bv 64 (BASE + 31488)) (mrestrict (w_H W) mem) (seg_rom SEGS)
    (Z_to_bv 32 2733970771) (Z_to_bv 5 10) (Z_to_bv 5 10) (Z_to_bv 5 15)
    (Sem.reg_get F (Z_to_bv 5 10)) (Z_to_bv 64 D6000)).
  - rewrite (rs_pc4 31488 31492) by lia. reflexivity.
  - apply rs_fetch. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_refl_bv.
  - rewrite !rs_rg_other by (intros X; vm_compute in X; discriminate). reflexivity.
  - rewrite rs_rg_other by (intros X; vm_compute in X; discriminate). apply rs_rg_same. }
eapply (rs_step_keep W); [ | exact HJ | clear HJ; intros md4 HJ].
{ rewrite (rs_step_flt _ _ SEGS _ (Z_to_bv 64 (BASE + 31492)) (mrestrict (w_H W) mem) (seg_rom SEGS)
    (Z_to_bv 32 2732922323) (Z_to_bv 5 11) (Z_to_bv 5 10) (Z_to_bv 5 14)
    (Sem.reg_get F (Z_to_bv 5 10)) (Z_to_bv 64 D3837)).
  - rewrite (rs_pc4 31492 31496) by lia. reflexivity.
  - apply rs_fetch. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_refl_bv.
  - rewrite !rs_rg_other by (intros X; vm_compute in X; discriminate). reflexivity.
  - apply rs_rg_same. }
lazymatch goal with |- SRr _ _ {| cfg_ms := @mkst ?f ?R4 _ _ _ |} _ =>
  pose proof (rs_switch (mkFP F fc) f E _ _ (w_H W) _ R4 31496 HS
    (regs_ok_set E _ _ (Z_to_bv 5 11) _ _ (regs_ok_set E _ _ (Z_to_bv 5 10) _ _ HRG (rs_slit E _)) (rs_slit E _))) as HS2
end.
rewrite HM in HS2.
clear HS HRG R10 R11 RUN0.
revert HS2.
destruct (FP.flt_d (Sem.reg_get F (Z_to_bv 5 10)) (Z_to_bv 64 D6000)) eqn:C0;
destruct (FP.flt_d (Sem.reg_get F (Z_to_bv 5 10)) (Z_to_bv 64 D3837)) eqn:C1; intros HS2;
lazymatch type of HS2 with @st_ok_pi _ _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS2 end;
lazymatch type of HS2 with @st_ok_pi _ _ ?f _ _ _ => pose proof (paj_run (fx := f) B LAWS) as RUN4 end;
(paj_run_tok RUN4 HS2 HJ SHOK rs_Bspan; [apply awr_ok_nil |]);
lazymatch goal with HF : frame_of _ ?rs mem (ms_mem ?m3) |- _ =>
  pose proof (frame_of_read_only _ rs _ _ eq_refl HF) as HM4; clear HF end;
lazymatch type of HS2 with @st_ok_pi _ _ ?f5 _ _ (restrict _ ?m3) =>
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?md5 |} _ =>
  prreg HS2 (10%bv : bv 5) Q10; prreg HS2 (1%bv : bv 5) Q1;
  eapply (paj_ret_at (PL := PL_disco) W E _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity));
  intros mat5;
  unfold treac_rate_snap_post;
  exists f5;
  cbn [YK11.fp_regs YK11.fp_csr];
  split; [reflexivity|];
  split; [apply rs_fcsr|];
  apply apost_base_same_fx;
  exists ly, S, (ms_regs m3), (ms_mem m3), (with_vm_backing (m_vm_lazy md5) mat5 md5);
  split; [rewrite Q1, E1, Hra; reflexivity|];
  split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs [] HS2); [exact HAE | vm_compute; reflexivity]|];
  split; [rewrite Q10; unfold reac_rate_snap_model; rewrite ?C0, ?C1; reflexivity|];
  split; [apply Permutation_refl|];
  split; [reflexivity | intros x; rewrite HM4; reflexivity]
  end end.
Qed.
End h.
End f.
End d.
