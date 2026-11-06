(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 759 of its 797 lines of code are new or changed and 507 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntExit.v, with its module names changed; 576 of its 632 lines of code are new or changed and 741 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0p YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC1i YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoArm3TailK DiscoYEntBodyStmt DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut
DiscoArm3JsonMs DiscoArm3JsonADefs DiscoArm3JsonK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_jscalar_model disco_json_reader_model slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_age_c slot_ser_defs.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition NB : nat := 555%nat.
Definition NL : nat := 556%nat.
Definition NR : nat := 557%nat.
Definition N32 : nat := 551%nat.
Definition NB1 : nat := 563%nat.
Definition NSB : nat := 564%nat.
Definition NOO : nat := 565%nat.

Definition ja2_acs : list YP09.chunk := [YP09.mkChunk 232 (CVal 8 (SOff NOO 0))].

Definition ja2_extra : smem :=
  [YP09.mkRegion (Some NB) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 91)); YP09.mkChunk 1 (CVal 1 (SOff NB1 0))];
   YP09.mkRegion (Some NSB) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))]].

Definition ja2_fa : list (nat * afact) :=
  [(NR, mkAF 2 969 0); (NB, mkAF 4096 (2 ^ 47) 4); (NL, mkAF (2 ^ 64 - 1 - 2 ^ 47) (2 ^ 64 - 1) 0);
   (N32, mkAF 32 32 0); (NB1, mkAF 33 255 0); (NSB, mkAF SB (SB + 2 ^ 44) 0); (NOO, mkAF 0 (2 ^ 64 - 1) 0)].

Definition ja2_al_l : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff NB 0) (SLit 3)) (SOff 32 0).
Definition ja2_al_r : sv := SOff NSB 0.

Definition ja2_rs : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 360 368 (dslot_chunks ++ ja2_acs);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 dfhdr_chunks;
   fshadow_region AT_SH DFRAME_CLASS 4 22 (dsh_chunks dsh_ser);
   got_regionP; bcell_regionP 32] ++ ja2_extra.

Definition ja2_cnt : sv :=
  SAlu ALU_ADD (SAlu ALU_SLTU (SAlu ALU_XOR (SLit 2) (SOff NR 0)) (SLit 1)) (SLit (-1)).

Definition jwok (w : option nat * Z * Z) : bool :=
  let '(b, wlo, whi) := w in
  (whi <=? wlo) || (obase_eqb b (Some AT_SH) && (4 <=? wlo) && (whi <=? 22))
  || (obase_eqb b (Some AT_A) && (360 <=? wlo) && (whi <=? 368)).

Lemma sv_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma ja2_cnt0 : forall E, ew E NR = Z_to_bv 64 2 -> sv_denot E ja2_cnt = Z_to_bv 64 0.
Proof. intros E HE. apply bv_eq. unfold ja2_cnt. cbn [sv_denot]. rewrite HE. vm_compute. reflexivity. Qed.

Lemma ja2_cap : forall op, 2 < slot_ser_defs.ser_cap op -> 43 <= slot_ser_defs.ser_cap op.
Proof.
  intros op H. unfold slot_ser_defs.ser_cap in *.
  assert (Hk : 0 <= slot_ser_defs.ser_k op) by (unfold slot_ser_defs.ser_k; apply Z.land_nonneg; right; lia).
  destruct (slot_ser_defs.ser_k op =? 0) eqn:Ez; lia.
Qed.

Lemma ja2_objs_nil : forall buf vpad, slot_ser_defs.objs_bytes buf vpad [] = [].
Proof. intros buf vpad. reflexivity. Qed.

Lemma ja2_submem : submem ja2_rs (d_kregions dsh_ser ja2_acs [] ++ ja2_extra).
Proof.
  unfold ja2_rs, ja2_extra, d_kregions, fshadow_region, DFRAME_SH, DFRAME_SIZE. cbn [app].
  repeat (apply submem_keep;
    [split; [reflexivity|];
     cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
     split; [lia|]; split; [lia|]; split; [lia|];
     intros cc Hcc; rewrite ?app_nil_r; exact Hcc |]).
  apply submem_nil.
Qed.

Ltac jregq HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict] in Hr
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict] in Hr
  end.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma ja2_pcall : forall (fq : YK11.FPState) E ss ms s,
  st_ok (fx := fq) SEGS E (setpc ss (SIGMA s)) ms ->
  st_ok_pi (fx := fq) SEGS VAL E (setpc ss (SIGMA s - BASE)) ms.
Proof.
  intros fq E ss ms s H. unfold st_ok_pi, abs_ss, setpc in *. destruct ss. simpl.
  replace (BASE + (SIGMA s - BASE)) with (SIGMA s) by lia. exact H.
Qed.

Definition jZs (cx : dcx) (a : Z) : Prop :=
  (shadow_addr (d_FB cx) + 4 <= a < shadow_addr (d_FB cx) + 22) \/ (d_A cx + 360 <= a < d_A cx + 368).

Lemma jwin_ok : forall (cx : dcx) E rs, forallb jwok (windows rs) = true ->
  bv_unsigned (ew E AT_SH) = shadow_addr (d_FB cx) -> bv_unsigned (ew E AT_A) = d_A cx ->
  forall b wlo whi a, In (b, wlo, whi) (windows rs) ->
  base_val E b + wlo <= a < base_val E b + whi -> jZs cx a.
Proof.
  intros cx E rs Hw H529 H60 b wlo whi a Hin Ha.
  pose proof (proj1 (forallb_forall _ _) Hw _ Hin) as Hb. unfold jwok in Hb.
  apply orb_true_iff in Hb as [Hb | Hb].
  - apply orb_true_iff in Hb as [Hb | Hb]; [apply Z.leb_le in Hb; lia|].
    apply andb_true_iff in Hb as [Hb Hhi]. apply andb_true_iff in Hb as [Hb Hlo].
    apply Z.leb_le in Hhi. apply Z.leb_le in Hlo.
    destruct b as [nb|]; [|discriminate Hb]. cbn [obase_eqb] in Hb. apply Nat.eqb_eq in Hb. subst nb.
    cbn [base_val] in Ha. rewrite H529 in Ha. unfold jZs. lia.
  - apply andb_true_iff in Hb as [Hb Hhi]. apply andb_true_iff in Hb as [Hb Hlo].
    apply Z.leb_le in Hhi. apply Z.leb_le in Hlo.
    destruct b as [nb|]; [|discriminate Hb]. cbn [obase_eqb] in Hb. apply Nat.eqb_eq in Hb. subst nb.
    cbn [base_val] in Ha. rewrite H60 in Ha. unfold jZs. lia.
Qed.

Lemma ja2_awr : forall (cx : dcx) E rs FP bl0 blc ly, forallb jwok (windows rs) = true ->
  bv_unsigned (ew E AT_SH) = shadow_addr (d_FB cx) -> bv_unsigned (ew E AT_A) = d_A cx ->
  frame_addr ly DFRAME_CLASS (c_fpos cx) = d_FB cx ->
  d_S cx - LLVMF_STK <= d_A cx -> d_A cx + 472 <= d_S cx ->
  awr_ok E rs LLVMF_STK (d_S cx) FP bl0 blc ly [(DFRAME_CLASS, c_fpos cx)].
Proof.
  intros cx E rs FP bl0 blc ly Hw H529 H60 Hfa Hs1 Hs2 a (r & Hr & Ha).
  assert (Hin : In (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r) (windows rs)).
  { unfold windows. exact (in_map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) rs r Hr). }
  pose proof (jwin_ok cx E rs Hw H529 H60 _ _ _ a Hin Ha) as HZ. unfold jZs in HZ.
  destruct HZ as [HZ | HZ].
  - right. right. right. exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite Hfa. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
  - left. lia.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBRT : d_body_rt_stmt B.

Lemma ja2_fsh_rdset : forall cx h n xb shf ly3 S3 W mem3 md3 k a,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k -> d_body B cx h n xb shf ly3 S3 W mem3 ->
  d_fsh cx a -> ~ d_rdset B cx h a.
Proof.
  intros cx h n xb shf ly3 S3 W mem3 md3 k a HC HBODY Ha.
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
    as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & _ & _ & _ & HAR3 & _ & _ & _).
  pose proof asan_consts as (Hac & _).
  pose proof alloc_ceiling_lt as Hcl.
  destruct HBODY as (T & G & Lk & HL & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
  destruct HBLK as (HPerm & _ & _ & _).
  unfold d_fsh in Ha. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha.
  assert (HF8 : 512 <= d_FB cx / 8 /\ d_FB cx / 8 + 512 <= 2 ^ 44).
  { split; [apply Z.div_le_lower_bound; lia|].
    assert (d_FB cx / 8 + 512 = (d_FB cx + 4096) / 8) as ->.
    { replace (d_FB cx + 4096) with (d_FB cx + 512 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    apply Z.div_le_upper_bound; lia. }
  unfold shadow_addr, SHADOW_OFF in Ha.
  assert (HA0 : 0x7fff8000 <= a < 0x7fff8000 + 2 ^ 44) by lia.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in GFapp.
  assert (HhA : in_app h (req_size HUNT_SIZE)).
  { assert (Hin : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
    exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin))))). }
  assert (HpA : 0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))).
  { intros Hc. destruct HC as ((HPRE & _) & _ & _). pose proof HPRE as (HAFN & _ & _ & _ & Hpn & _).
    pose proof HAFN as (HAR0 & _).
    destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia|].
    exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin))))). }
  assert (Hro : forall x, in_roP SEGS pa_relro_lo pa_relro_hi x -> 0 <= x < kLowMemEnd).
  { intros x [(s & Hs & _ & Hsa) | Hr]; apply pa_segs_low;
      [exists s; split; [exact Hs | exact Hsa] | exact (pa_relro_img x Hr)]. }
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HhA, HpA.
  change (req_size HUNT_SIZE) with 480 in HhA.
  unfold d_rdset, d_objr, d_obj, dobj_off, dobj_size, HUNT_SIZE.
  intros [H1 | [H1 | [H1 | [H1 | [H1 | [(Hc & H1) | [H1 | H1]]]]]]].
  - zlia.
  - zlia.
  - zlia.
  - zlia.
  - zlia.
  - specialize (HpA Hc). unfold req_size in HpA.
    destruct (Z.eqb_spec (c_n cx) 0); [lia|]. zlia.
  - pose proof (Hro a (proj1 H1)). unfold kLowMemEnd in *. zlia.
  - unfold FF_canary in H1. zlia.
Qed.

Lemma ja2_land : forall (fq : YK11.FPState) (cx : dcx) h i n now xb shf shf' pc ly3 S3 (W : world SEGS) mem3 k acc
    (R : bvmap 5 word -> Prop) (X : world SEGS -> (word -> option byte) -> Prop) E ss ms md' (Zs : Z -> Prop),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) -> d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD i + 1 -> st_nev S3 <= st_nev (c_S cx) + (EV_HEAD i + 1) ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX ->
  0 <= i < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 ->
  d_body B cx h n xb shf ly3 S3 W mem3 -> d_sp0 cx i now W mem3 ->
  d_E cx E -> ew E AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  d_land_chk shf' (ss_mem ss) = true ->
  (forall a, Zs a -> (d_S cx - LLVMF_STK <= a < d_S cx) \/ d_fsh cx a) ->
  (forall a, d_fsh cx a -> ~ d_rdset B cx h a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a) ->
  (forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms) a) ->
  (forall a, d_A cx + 120 <= a < d_A cx + 360 -> ~ Zs a) ->
  (forall a, d_A cx + 368 <= a < d_A cx + 384 -> ~ Zs a) ->
  d_rL B cx (ms_regs ms) -> R (ms_regs ms) -> X W (ms_mem ms) ->
  d_arm_at_pf B MT XM_LIB RLO RHI tfib_K cx pc h i n now xb shf' R X W (mkCfg ms md').
Proof.
  intros fq cx h i n now xb shf shf' pc ly3 S3 W mem3 k acc R X E ss ms md' Zs
    Hfrm0 HBASE HJ HFR Hk Hnev HMO Hacc Hi Hn Hnow HBODY HSP0 HE HFL HS Hrv Hpc Hchk HZs HRD HKEEP HPRES HZA HZB HRL HR
    HX.
  pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hms.
  pose proof HBODY as (T & G & Lk & HL & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
  assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md' k) by exact (conj HBASE (conj HJ HFR)).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md' k HCTX)
    as (GS16 & GSlo & GShi & _).
  pose proof alloc_ceiling_lt as Hcl. pose proof asan_consts as (Hac & _).
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & _).
  unfold MFRAME, LLVMF_STK in *.
  assert (KV : forall off len v, 120 <= off -> off + Z.of_nat len <= 360 ->
    val_mem SEGS (rd W mem3) (d_A cx + off) len v -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + off) len v).
  { intros off len v H1 H2 Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 (ms_mem ms)); [|exact Hv].
    intros kk Hkk. apply HKEEP; [lia|]. apply HZA. lia. }
  assert (KW : forall off len v, 368 <= off -> off + Z.of_nat len <= 384 ->
    val_mem SEGS (rd W mem3) (d_A cx + off) len v -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + off) len v).
  { intros off len v H1 H2 Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 (ms_mem ms)); [|exact Hv].
    intros kk Hkk. apply HKEEP; [lia|]. apply HZB. lia. }
  pose proof (d_hslots_of_frame cx h shf W mem3 HFRM) as HSL.
  destruct HSL as (V184 & V120 & V136 & V376 & V280 & V232 & V264).
  assert (HSL' : d_hslots cx h W (ms_mem ms)).
  { split; [exact (KV 184 8%nat h ltac:(lia) ltac:(cbn; lia) V184)|].
    split; [exact (KV 120 8%nat (h + 440) ltac:(lia) ltac:(cbn; lia) V120)|].
    split; [exact (KV 136 8%nat 0 ltac:(lia) ltac:(cbn; lia) V136)|].
    split; [exact (KW 376 8%nat (dnot (d_obj cx OG)) ltac:(lia) ltac:(cbn; lia) V376)|].
    split; [exact (KV 280 8%nat (dnot (d_obj cx OT)) ltac:(lia) ltac:(cbn; lia) V280)|].
    split; [exact (KV 232 8%nat (dnot (d_obj cx OO)) ltac:(lia) ltac:(cbn; lia) V232)|].
    exact (KV 264 8%nat (dnot (d_obj cx OUSED)) ltac:(lia) ltac:(cbn; lia) V264). }
  pose proof (d_land_hs B MT XM_LIB RLO RHI tfib_K DLAND LAWS FFL fq cx h shf' ly3 S3 W md' k E ss ms
    HCTX HE HFL HS Hchk HSL') as (HFRM' & HSHD').
  pose proof (DBRT cx h n n xb shf shf' ly3 S3 W mem3 (ms_mem ms) (d_S cx - 32768) (d_S cx) Zs HBODY
    ltac:(unfold LLVMF_STK; lia) ltac:(lia)
    ltac:(intros a Ha; destruct (HZs a Ha) as [Hs | Hs]; [left; exact Hs | right; exact (HRD a Hs)])
    HKEEP ltac:(intros a _ Ha; exact (HPRES a Ha)) HFRM' HSHD' ltac:(lia)) as HBODY'.
  unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
  split.
  { transitivity (mkCfg (YK11.mkst (fx := fq) (ms_regs ms) (Z_to_bv 64 (BASE + ss_pc ss)) (ms_mem ms)
      (YK11.seg_rom SEGS)) md'); [f_equal; exact Hms | unfold cfg_at, w64; rewrite Hpc; reflexivity]. }
  split; [exact Hfrm0|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|].
  split; [exact Hnev|].
  split; [exact HMO|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|]. split; [exact HRL|]. split; [exact HR|].
  split; [exact HX|]. split; [|exact HBODY'].
  destruct HSP0 as (H208 & H320). split.
  - exact (KV 208 8%nat i ltac:(lia) ltac:(cbn; lia) H208).
  - exact (KV 320 8%nat now ltac:(lia) ltac:(cbn; lia) H320).
Qed.

Theorem jA_S2 : jA_S2_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros cx h i n now op W0 c0 T0 T1 buf W c [HFROM HAT].
  unfold d_arm_at_pf, d_at in HAT.
  destruct HAT as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & HBASE & HJ & HFR & Hk & Hnev & HMO &
    Hacc &
    Hi & Hn & Hnow & HRL & (R26 & R24 & R25 & _) & (HSP1 & HTAB & HBUF & _) & HSP0 & HBODY).
  pose proof HTAB as ((removed & HAGE & HPOST) & HGT).
  destruct (jk_fin T0 T1 now removed HPOST Hnow) as (fin & HFIN).
  pose proof HFIN as (HJR & Hfn & HWS & HLEN & HINB).
  pose proof HBUF as (Hr & HGB).
  pose proof HRL as (L2 & L3 & L4 & L8 & L9 & L19 & L18 & L20 & L27).
  assert (HrB : a3_r T1 now = jlen (a3_text T1 now)) by reflexivity.
  assert (HW0 : json_ws (a3_text T1 now) 0 = 0) by (apply json_ws_id; [exact HWS | lia]).
  assert (HW1 : json_ws (a3_text T1 now) 1 = 1) by (apply json_ws_id; [exact HWS | lia]).
  assert (HW2 : json_ws (a3_text T1 now) 2 = 2) by (apply json_ws_id; [exact HWS | lia]).
  pose proof (json_read_step (a3_text T1 now) fin HJR) as (H0 & HCASE).
  rewrite HW0 in H0, HCASE. change (0 + 1) with 1 in HCASE. rewrite HW1 in HCASE.
  change (1 + 1) with 2 in HCASE. rewrite HW2 in HCASE.
  apply at_byte_true in H0 as (_ & Hb0).
  assert (Hb1r : 33 <= jbyte (a3_text T1 now) 1 <= 255) by (apply jno_ws_byte; [exact HWS | lia]).
  set (b1 := jbyte (a3_text T1 now) 1) in *.
  pose proof HBODY as (T & G & Lk & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
  pose proof HFRM as (E & HE & HREG & HFLAG & V184 & V120 & V136 & V376 & V280 & V232 & V264).
  pose proof HBLK as (HPerm & _ & _ & HOFFb).
  assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
    as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
  pose proof asan_consts as (Hac & _).
  pose proof alloc_ceiling_lt as Hcl.
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
  unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
  assert (Hcap : 43 <= slot_ser_defs.ser_cap op) by (apply ja2_cap; lia).
  assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). unfold a3_xb. cbn [app]. left. reflexivity. }
  assert (Hrq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = slot_ser_defs.ser_cap op).
  { rewrite Z.max_l by lia. unfold req_size.
    destruct (Z.eqb_spec (slot_ser_defs.ser_cap op) 0); [lia | reflexivity]. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _).
  destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (HbSh & _).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hinb HFin3) as Hsep.
  rewrite EFA3 in Hsep. rewrite Hrq in Hbceil, Hbapp, HbSh, Hsep.
  unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hsep.
  unfold a3_xb in HOFFb. pose proof (Forall_inv (Forall_inv_tail HOFFb)) as HoffB. cbn [fst snd] in HoffB.
  rewrite Hrq in HoffB.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp, GFapp.
  assert (MB0 : val_mem SEGS (rd W mem3) buf 1 91).
  { destruct (HGB 0%nat) as (Hv & _); [rewrite length_app; cbn [length]; unfold jlen in HrB; lia|].
    rewrite app_nth1 in Hv by (unfold jlen in HrB; lia).
    unfold jbyte in Hb0. change (Z.to_nat 0) with 0%nat in Hb0. rewrite Hb0 in Hv.
    change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv. exact Hv. }
  assert (MB1 : val_mem SEGS (rd W mem3) (buf + 1) 1 b1).
  { destruct (HGB 1%nat) as (Hv & _); [rewrite length_app; cbn [length]; unfold jlen in HrB; lia|].
    rewrite app_nth1 in Hv by (unfold jlen in HrB; lia). exact Hv. }
  assert (MSB : val_mem SEGS (rd W mem3) (shadow_addr buf) 1 0).
  { destruct HbSh as (_ & _ & Hsh). specialize (Hsh 0 ltac:(lia)).
    replace (0 <? slot_ser_defs.ser_cap op / 8) with true in Hsh by (symmetry; apply Z.ltb_lt; lia).
    unfold shadow_of_addr in Hsh. rewrite Z.add_0_r in Hsh. unfold aview in Hsh.
    intros kk Hkk. assert (kk = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
    unfold shadow_addr. destruct (mbyte SEGS (rd W mem3) (SHADOW_OFF + buf / 8)) as [bb|] eqn:Eb; [|discriminate Hsh].
    cbn [option_map] in Hsh. injection Hsh as Hbb. f_equal. apply bv_eq. rewrite Hbb. reflexivity. }
  set (ex := [Z_to_bv 64 b1; Z_to_bv 64 (shadow_addr buf); Z_to_bv 64 (dnot (d_obj cx OO))]).
  set (E' := d_env cx E (jk_vals regs ex)).
  pose proof HE as (EE & E32 & HEI0 & E60 & EF & ESH). unfold AT_A, AT_F, AT_SH in E60, EF, ESH.
  assert (AX : forall j, (j < 32)%nat -> ew E' (AT_X + j) = getr regs (Z_to_bv 5 (Z.of_nat j)))
    by (intros j Hj; exact (jk_x cx E regs ex j Hj)).
  assert (AO : forall nn, (nn < AT_FL)%nat -> ew E' nn = ew E nn) by (intros nn Hnn; apply d_env_old; exact Hnn).
  assert (A534 : ew E' 534 = getr regs 3)
    by (change 534%nat with (AT_X + 3)%nat; exact (AX 3%nat ltac:(lia))).
  assert (A535 : ew E' 535 = getr regs 4)
    by (change 535%nat with (AT_X + 4)%nat; exact (AX 4%nat ltac:(lia))).
  assert (A549 : ew E' 549 = getr regs 18)
    by (change 549%nat with (AT_X + 18)%nat; exact (AX 18%nat ltac:(lia))).
  assert (A551 : ew E' 551 = getr regs 20)
    by (change 551%nat with (AT_X + 20)%nat; exact (AX 20%nat ltac:(lia))).
  assert (A555 : ew E' 555 = getr regs 24)
    by (change 555%nat with (AT_X + 24)%nat; exact (AX 24%nat ltac:(lia))).
  assert (A556 : ew E' 556 = getr regs 25)
    by (change 556%nat with (AT_X + 25)%nat; exact (AX 25%nat ltac:(lia))).
  assert (A557 : ew E' 557 = getr regs 26)
    by (change 557%nat with (AT_X + 26)%nat; exact (AX 26%nat ltac:(lia))).
  assert (A516 : ew E' 516 = Z_to_bv 64 (d_FB cx))
    by (rewrite AO by (unfold AT_FL; lia); exact EF).
  assert (EB : ew E' NB = Z_to_bv 64 buf).
  { unfold NB. change 555%nat with (AT_X + 24)%nat. rewrite (AX 24%nat ltac:(lia)). exact R24. }
  assert (ER : ew E' NR = Z_to_bv 64 (a3_r T1 now)).
  { unfold NR. change 557%nat with (AT_X + 26)%nat. rewrite (AX 26%nat ltac:(lia)). exact R26. }
  assert (EL : ew E' NL = Z_to_bv 64 (2 ^ 64 - 1 - buf)).
  { unfold NL. change 556%nat with (AT_X + 25)%nat. rewrite (AX 25%nat ltac:(lia)).
    rewrite (jk_lnot buf ltac:(lia)) in R25. exact R25. }
  assert (E20 : ew E' N32 = Z_to_bv 64 32).
  { unfold N32. change 551%nat with (AT_X + 20)%nat. rewrite (AX 20%nat ltac:(lia)). exact L20. }
  assert (EB1 : ew E' NB1 = Z_to_bv 64 b1).
  { unfold NB1. change 563%nat with (AT_X + (32 + 0))%nat.
    exact (jk_xe cx E regs ex 0%nat ltac:(cbn; lia)). }
  assert (ESB : ew E' NSB = Z_to_bv 64 (shadow_addr buf)).
  { unfold NSB. change 564%nat with (AT_X + (32 + 1))%nat.
    exact (jk_xe cx E regs ex 1%nat ltac:(cbn; lia)). }
  assert (ENOO : ew E' NOO = Z_to_bv 64 (dnot (d_obj cx OO))).
  { unfold NOO. change 565%nat with (AT_X + (32 + 2))%nat.
    exact (jk_xe cx E regs ex 2%nat ltac:(cbn; lia)). }
  assert (E32' : ew E' 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite AO by (unfold AT_FL; lia); exact E32).
  assert (U2 : bv_unsigned (ew E' 2) = d_S cx)
    by (rewrite AO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
  assert (U60 : bv_unsigned (ew E' 60) = d_A cx)
    by (rewrite AO by (unfold AT_FL; lia); rewrite E60; apply unsigned_lit_small; lia).
  assert (U516 : bv_unsigned (ew E' 516) = d_FB cx)
    by (rewrite AO by (unfold AT_FL; lia); rewrite EF; apply unsigned_lit_small; lia).
  assert (U529 : bv_unsigned (ew E' 529) = shadow_addr (d_FB cx))
    by (rewrite AO by (unfold AT_FL; lia); rewrite ESH; apply unsigned_lit_small;
        unfold shadow_addr, SHADOW_OFF; lia).
  assert (HEI : img_env VAL A_LIM E') by exact (proj1 (proj2 (proj2 (d_E_env cx E (jk_vals regs ex) HE)))).
  assert (UG0 : base_val E' (Some (A_OBJ 0)) = VAL (A_OBJ 0)).
  { cbn [base_val]. rewrite (img_env_atomP E' (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
    apply unsigned_lit_small. apply pa_val_range. }
  assert (UG12 : base_val E' (Some (A_OBJ 12)) = VAL (A_OBJ 12)).
  { cbn [base_val]. rewrite (img_env_atomP E' (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
    apply unsigned_lit_small. apply pa_val_range. }
  pose proof (pa_obj_img 0 ltac:(vm_compute; lia)) as HO0.
  pose proof (pa_obj_img 12 ltac:(vm_compute; lia)) as HO12.
  unfold IMG_LO, IMG_TOP in HO0, HO12. unfold off_img, IMG_LO, IMG_TOP in HoffB.
  assert (Hr969 : a3_r T1 now <= 969) by (unfold a3_r; lia).
  assert (HFA : atoms_ok E' ja2_fa).
  { unfold ja2_fa. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite ER, EB, EL, E20, EB1, ESB, ENOO.
    rewrite (unsigned_lit_small (a3_r T1 now)) by lia.
    rewrite (unsigned_lit_small buf) by lia.
    rewrite (unsigned_lit_small (2 ^ 64 - 1 - buf)) by lia.
    rewrite (unsigned_lit_small 32) by lia.
    rewrite (unsigned_lit_small b1) by lia.
    rewrite (unsigned_lit_small (shadow_addr buf)) by (unfold shadow_addr, SHADOW_OFF; lia).
    rewrite (unsigned_lit_small (dnot (d_obj cx OO))) by (unfold dnot, d_obj, dobj_off; lia).
    unfold SB, shadow_addr, SHADOW_OFF, dnot, d_obj, dobj_off.
    change (2 ^ 0) with 1. change (2 ^ 4) with 16.
    repeat split; first [ exact Hb16 | rewrite Z.mod_1_r; reflexivity | lia ]. }
  assert (HXR : Forall (region_ok SEGS E' (rd W mem3)) ja2_extra).
  { unfold ja2_extra. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    - rewrite EB, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (chunk_ok_val SEGS E' _ buf 0 1 (SLit 91) 91);
          [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia | rewrite Z.add_0_r; exact MB0].
      + apply (chunk_ok_val SEGS E' _ buf 1 1 (SOff NB1 0) b1);
          [rewrite sv_off0; exact EB1 | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia | exact MB1].
    - rewrite ESB, unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
      split; [unfold shadow_addr, SHADOW_OFF; lia|].
      split; [unfold shadow_addr, SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E' _ (shadow_addr buf) 0 1 (SLit 0) 0);
        [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia | rewrite Z.add_0_r; exact MSB]. }
  assert (HPDX : pairwise_disjoint E' ja2_extra).
  { apply pairwise_disjoint_of_extents. unfold ja2_extra, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite EB, ESB.
    rewrite !unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold shadow_addr, SHADOW_OFF.
    repeat split; lia. }
  assert (HDX : Forall (fun r => all_disjoint E' r (d_kregions dsh_ser ja2_acs [])) ja2_extra).
  { unfold ja2_extra. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      apply all_disjoint_of_extents;
      unfold d_kregions, fshadow_region, got_regionP, bcell_regionP, extent_of_region;
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi]; rewrite UG0, UG12;
      unfold AT_STK, AT_A, AT_F, AT_SH; cbn [base_val];
      rewrite ?EB, ?ESB, U2, U60, U516, U529;
      rewrite !unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia);
      change (fs_frame_bytes DFRAME_CLASS) with 4096; change (4096 / 8) with 512;
      cbn [zall_disjoint]; unfold zdisj; cbn [fst snd]; unfold shadow_addr, SHADOW_OFF; repeat split; lia. }
  assert (HAC : Forall (YP09.chunk_ok SEGS E' (rd W mem3) (d_A cx)) ja2_acs).
  { unfold ja2_acs. apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E' _ (d_A cx) 232 8 (SOff NOO 0) (dnot (d_obj cx OO)));
      [rewrite sv_off0; exact ENOO
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold dnot, d_obj, dobj_off; lia
      | lia | exact V232]. }
  pose proof (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (jk_vals regs ex) ja2_fa [] HCTX HE HFA I) as HFACTS.
  pose proof (DSEAT LAWS PAL fq cx dsh_ser ly3 S3 W regs mem3 md3 k E JA_RET1 jk_sr (jk_vals regs ex)
    ja2_acs [] ja2_extra (d_facts ja2_fa []) HCTX HE HREG HFLAG
    ltac:(apply (jk_regs_ok B); [exact HE | exact HRL]) HFACTS HAC (Forall_nil _)
    HXR HPDX HDX ltac:(vm_compute; reflexivity)) as HS0.
  fold E' in HS0.
  pose proof (st_ok_pi_add_alias E' _ _ ja2_al_l ja2_al_r HS0
    (shadow_decl_ok E' NB 32 NSB buf SHADOW_OFF EB ltac:(lia) E32' ESB)) as HS1.
  clear HS0.
  pose proof (st_ok_pi_submem E' _ _ ja2_rs HS1
    ltac:(cbn [set_facts ss_mem ss_d]; exact ja2_submem) ltac:(vm_compute; reflexivity)) as HS.
  clear HS1. norm_ss HS.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E' (rd W mem3)) by (unfold sh_ok; apply Forall_nil).
  pose proof (paj_run (fx := fq) B LAWS) as RUN.
  pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
  pose proof (paj_branch (fx := fq)) as BR.
  assert (XK : forall mF, (forall a, 0 <= a < 2 ^ 64 -> ~ jZs cx a ->
      aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem3 a) ->
    d_sp1 cx i n now W mF /\ a3_tab cx now T0 T1 W mF /\ a3_buf op T1 now buf W mF).
  { intros mF HK. split; [|split].
    - destruct HSP1 as ((H208 & H320) & H192 & H200).
      split; [split|split]; (eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mF); [|eassumption]);
        intros kk Hkk; (apply HK; [lia | unfold jZs, shadow_addr, SHADOW_OFF; lia]).
    - split; [exact (proj1 HTAB)|].
      apply (garr8_frame SEGS (rd W mem3) (rd W mF) (d_obj cx OT) _ HGT).
      intros x Hx. rewrite length_map in Hx. pose proof (proj1 HPOST) as LT1. rewrite LT1 in Hx.
      apply (mbyte_of_aview SEGS). apply HK;
        [unfold d_obj, dobj_off in Hx; lia | unfold jZs, d_obj, dobj_off, shadow_addr, SHADOW_OFF in *; lia].
    - split; [exact Hr|].
      apply (garr8_frame SEGS (rd W mem3) (rd W mF) buf _ HGB).
      intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. unfold a3_r in Hr.
      apply (mbyte_of_aview SEGS). apply HK; [lia | unfold jZs, shadow_addr, SHADOW_OFF in *; lia]. }
  assert (HZs : forall a, jZs cx a -> (d_S cx - LLVMF_STK <= a < d_S cx) \/ d_fsh cx a).
  { intros a [Ha | Ha].
    - right. unfold d_fsh. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
    - left. unfold LLVMF_STK. lia. }
  assert (HRD : forall a, d_fsh cx a -> ~ d_rdset B cx h a)
    by (intros a Ha; exact (ja2_fsh_rdset cx h n (a3_xb buf op) dsh_ser ly3 S3 W mem3 md3 k a HCTX HBODY Ha)).
  assert (HZA : forall a, d_A cx + 120 <= a < d_A cx + 360 -> ~ jZs cx a)
    by (intros a Ha [Hb | Hb]; unfold shadow_addr, SHADOW_OFF in *; lia).
  assert (HZB : forall a, d_A cx + 368 <= a < d_A cx + 384 -> ~ jZs cx a)
    by (intros a Ha [Hb | Hb]; unfold shadow_addr, SHADOW_OFF in *; lia).
  pose proof (d_E_env cx E (jk_vals regs ex) HE) as HE'. fold E' in HE'.
  pose proof (d_env_fl cx E (jk_vals regs ex)) as HFL'. fold E' in HFL'.
  unfold cfg_at. change (w64 (BASE + JA_RET1)) with (Z_to_bv 64 (BASE + JA_RET1)).
  paj_run_tok RUN HS HJ SHOK (0, 0).
  { eapply ja2_awr; [vm_compute; reflexivity | exact U529 | exact U60 | exact EFA3 | unfold LLVMF_STK; lia | lia]. }
  lazymatch goal with HFr0 : frame_of _ ?rs0 (mrestrict _ mem3) (mrestrict _ (ms_mem ?m1)), HG0 : mem_grows _ _ |- _ =>
    assert (HWW0 : forallb jwok (windows rs0) = true) by (vm_compute; reflexivity);
    pose proof (kept_of_frame (segs := SEGS) E' rs0 (w_H W) mem3 (ms_mem m1) (jZs cx) HFr0
      (jwin_ok cx E' rs0 HWW0 U529 U60)) as KEEP1;
    pose proof (fun a => jk_apres_grow (w_H W) mem3 (ms_mem m1) a HG0) as PRES1 end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  - rewrite branch_ne_U, (U_atom E' 563%nat b1 EB1 ltac:(lia)), U_lit in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc.
    destruct HCASE as [(Hat & _ & _) | (_ & HOBJS)].
    { exfalso. apply at_byte_true in Hat as (_ & Hat). exact (Hc Hat). }
    paj_run_tok RUN HS HJ SHOK (0, 0).
    { eapply ja2_awr; [vm_compute; reflexivity | exact U529 | exact U60 | exact EFA3 | unfold LLVMF_STK; lia | lia]. }
    lazymatch goal with
      HFr0 : frame_of _ ?rs0 (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)), HG0 : mem_grows _ _ |- _ =>
      assert (HWW1 : forallb jwok (windows rs0) = true) by (vm_compute; reflexivity);
      pose proof (kept_of_frame (segs := SEGS) E' rs0 (w_H W) (ms_mem m1) (ms_mem m2) (jZs cx) HFr0
        (jwin_ok cx E' rs0 HWW1 U529 U60)) as KEEP2;
      pose proof (fun a => jk_apres_grow (w_H W) (ms_mem m1) (ms_mem m2) a HG0) as PRES2;
      assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ jZs cx a ->
        aview SEGS (w_H W) (ms_mem m2) a = aview SEGS (w_H W) mem3 a)
        by (intros a Ha Hnz; rewrite (KEEP2 a Ha Hnz); exact (KEEP1 a Ha Hnz));
      assert (PRESF : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem m2) a)
        by (intros a Ha; exact (PRES2 a (PRES1 a Ha))) end.
    lazymatch goal with
    | HSc : st_ok _ _ (setpc ?ssF _) (restrict _ ?mF) |- _ =>
      pose proof (ja2_pcall fq E' ssF (restrict (w_H W) mF) AS___asan_memset HSc) as HSp;
      jregq HSc (1%bv : bv 5) Q1; jregq HSc (2%bv : bv 5) Q2; jregq HSc (3%bv : bv 5) Q3;
      jregq HSc (4%bv : bv 5) Q4; jregq HSc (8%bv : bv 5) Q8; jregq HSc (9%bv : bv 5) Q9;
      jregq HSc (10%bv : bv 5) Q10; jregq HSc (11%bv : bv 5) Q11; jregq HSc (12%bv : bv 5) Q12;
      jregq HSc (18%bv : bv 5) Q18; jregq HSc (19%bv : bv 5) Q19; jregq HSc (20%bv : bv 5) Q20;
      jregq HSc (21%bv : bv 5) Q21; jregq HSc (22%bv : bv 5) Q22; jregq HSc (23%bv : bv 5) Q23;
      jregq HSc (24%bv : bv 5) Q24; jregq HSc (25%bv : bv 5) Q25; jregq HSc (26%bv : bv 5) Q26;
      jregq HSc (27%bv : bv 5) Q27 end.
    apply SRr_ret. right. exists fin. unfold ms_in, jcut. split; [exact HFROM|].
    eapply (ja2_land fq cx h i n now (a3_xb buf op) dsh_ser dsh_scr (SIGMA AS___asan_memset - BASE)
      ly3 S3 W mem3 k acc _ _ E' _ _ _ (jZs cx) Hfrm0 HBASE HJ HFR Hk Hnev HMO Hacc Hi Hn Hnow
      HBODY HSP0 HE' HFL' HSp ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
      HZs HRD KEEPF PRESF HZA HZB).
    + rewrite sv_off0 in Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q20, Q27.
      split; [unfold spZ; rewrite Q2, U60; reflexivity|].
      split; [rewrite Q3, A534; exact L3|].
      split; [rewrite Q4, A535; exact L4|].
      split; [rewrite Q8; rewrite AO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
              unfold w64, d_S, spZ; symmetry; apply Z_to_bv_bv_unsigned|].
      split; [rewrite Q9; rewrite AO by (unfold AT_FL; lia); exact E60|].
      split; [rewrite Q19; rewrite AO by (unfold AT_FL; lia); exact E32|].
      split; [rewrite Q18, A549; exact L18|].
      split; [rewrite Q20, A551; exact L20|].
      rewrite Q27; rewrite AO by (unfold AT_FL; lia); exact ESH.
    + cbv beta. rewrite sv_off0 in Q24, Q25, Q26.
      cbn [sv_denot] in Q11, Q12, Q21, Q22.
      split; [rewrite Q26, A557; exact R26|].
      split; [rewrite Q24, A555; exact R24|].
      split; [rewrite Q25, A556; exact R25|].
      split; [rewrite Q1; exact (codeptr_val E' JA_RET2 HEI)|].
      split; [rewrite Q10, (jk_den E' 516%nat (d_FB cx) 240 A516 ltac:(lia));
              unfold jcur, d_obj, dobj_off, w64; f_equal; lia|].
      split; [exact Q11|]. split; [exact Q12|].
      split; [exact Q21|]. split; [exact Q22|].
      rewrite Q23, (jk_den E' 516%nat (d_FB cx) 240 A516 ltac:(lia)).
      unfold jcur, d_obj, dobj_off, w64. f_equal. lia.
    + cbv beta. destruct (XK _ KEEPF) as (X1 & X2 & X3).
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact HFIN | exact HOBJS].
  - rewrite branch_ne_U, (U_atom E' 563%nat b1 EB1 ltac:(lia)), U_lit in Hc by lia.
    apply negb_false_iff, Z.eqb_eq in Hc.
    destruct HCASE as [(_ & Hend & Hfin) | (Hat & _)].
    2: { exfalso. rewrite (at_byte_spec (a3_text T1 now) 1 93 ltac:(rewrite <- HrB; lia)) in Hat.
         assert (Hc' : jbyte (a3_text T1 now) 1 = 93) by exact Hc.
         rewrite Hc' in Hat. cbn in Hat. discriminate Hat. }
    assert (Hr2 : a3_r T1 now = 2) by (rewrite HrB; rewrite <- Hend; lia).
    paj_run_tok RUN HS HJ SHOK (0, 0).
    { eapply ja2_awr; [vm_compute; reflexivity | exact U529 | exact U60 | exact EFA3 | unfold LLVMF_STK; lia | lia]. }
    lazymatch goal with
      HFr0 : frame_of _ ?rs0 (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)), HG0 : mem_grows _ _ |- _ =>
      assert (HWW1 : forallb jwok (windows rs0) = true) by (vm_compute; reflexivity);
      pose proof (kept_of_frame (segs := SEGS) E' rs0 (w_H W) (ms_mem m1) (ms_mem m2) (jZs cx) HFr0
        (jwin_ok cx E' rs0 HWW1 U529 U60)) as KEEP2;
      pose proof (fun a => jk_apres_grow (w_H W) (ms_mem m1) (ms_mem m2) a HG0) as PRES2;
      assert (KEEPA : forall a, 0 <= a < 2 ^ 64 -> ~ jZs cx a ->
        aview SEGS (w_H W) (ms_mem m2) a = aview SEGS (w_H W) mem3 a)
        by (intros a Ha Hnz; rewrite (KEEP2 a Ha Hnz); exact (KEEP1 a Ha Hnz));
      assert (PRESA : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem m2) a)
        by (intros a Ha; exact (PRES2 a (PRES1 a Ha))) end.
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
    clear KEEP1 KEEP2 PRES1 PRES2.
    psrr_branch_tok RUN BR HS SHOK (0, 0).
    { exfalso. rewrite branch_ltu_U, (U_atom E' 557%nat (a3_r T1 now) ER ltac:(lia)), U_lit in Hc0 by lia.
      apply Z.ltb_lt in Hc0. lia. }
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) R12_OFF.
    { eapply ja2_awr; [vm_compute; reflexivity | exact U529 | exact U60 | exact EFA3 | unfold LLVMF_STK; lia | lia]. }
    lazymatch goal with
      HFr0 : frame_of _ ?rs0 (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)), HG0 : mem_grows _ _ |- _ =>
      assert (HWW2 : forallb jwok (windows rs0) = true) by (vm_compute; reflexivity);
      pose proof (kept_of_frame (segs := SEGS) E' rs0 (w_H W) (ms_mem m1) (ms_mem m2) (jZs cx) HFr0
        (jwin_ok cx E' rs0 HWW2 U529 U60)) as KEEP3;
      pose proof (fun a => jk_apres_grow (w_H W) (ms_mem m1) (ms_mem m2) a HG0) as PRES3;
      assert (KEEPG : forall a, 0 <= a < 2 ^ 64 -> ~ jZs cx a ->
        aview SEGS (w_H W) (ms_mem m2) a = aview SEGS (w_H W) mem3 a)
        by (intros a Ha Hnz; rewrite (KEEP3 a Ha Hnz); exact (KEEPA a Ha Hnz));
      assert (PRESG : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem m2) a)
        by (intros a Ha; exact (PRES3 a (PRESA a Ha))) end.
    jregq HS (24%bv : bv 5) Q24. jregq HS (27%bv : bv 5) Q27.
    jregq HS (2%bv : bv 5) Q2. jregq HS (3%bv : bv 5) Q3. jregq HS (4%bv : bv 5) Q4.
    jregq HS (8%bv : bv 5) Q8. jregq HS (9%bv : bv 5) Q9. jregq HS (18%bv : bv 5) Q18.
    jregq HS (19%bv : bv 5) Q19. jregq HS (20%bv : bv 5) Q20.
    apply SRr_ret. left. exists 0, (@nil jobj), (repeat (Z_to_bv 8 0) 4).
    unfold r12_in. split; [exact HFROM|].
    eapply (ja2_land fq cx h i n now (a3_xb buf op) dsh_ser dsh_ser R12_OFF ly3 S3 W mem3 k acc
      _ _ E' _ _ _ (jZs cx) Hfrm0 HBASE HJ HFR Hk Hnev HMO Hacc Hi Hn Hnow
      HBODY HSP0 HE' HFL' HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
      HZs HRD KEEPG PRESG HZA HZB).
    + rewrite sv_off0 in Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q20, Q27.
      split; [unfold spZ; rewrite Q2, U60; reflexivity|].
      split; [rewrite Q3, A534; exact L3|].
      split; [rewrite Q4, A535; exact L4|].
      split; [rewrite Q8; rewrite AO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
              unfold w64, d_S, spZ; symmetry; apply Z_to_bv_bv_unsigned|].
      split; [rewrite Q9; rewrite AO by (unfold AT_FL; lia); exact E60|].
      split; [rewrite Q19; rewrite AO by (unfold AT_FL; lia); exact E32|].
      split; [rewrite Q18, A549; exact L18|].
      split; [rewrite Q20, A551; exact L20|].
      rewrite Q27; rewrite AO by (unfold AT_FL; lia); exact ESH.
    + cbv beta. rewrite sv_off0 in Q24, Q27.
      split; [rewrite Q24, A555; exact R24|].
      rewrite Q27; rewrite AO by (unfold AT_FL; lia); exact ESH.
    + cbv beta. destruct (XK _ KEEPG) as (X1 & X2 & X3).
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
      split; [rewrite <- Hfin; exact HJR|].
      split.
      { pose proof (st_ok_pi_region_nth E' _ _ 1%nat _ HS eq_refl) as RA.
        cbn [ms_mem restrict] in RA.
        exact (field_of_region E' _ AT_A (d_A cx) _ 0 472 360 368 360 8 ja2_cnt 0 RA U60
                 ltac:(apply jk_in; vm_compute; reflexivity)
                 ltac:(apply ja2_cnt0; rewrite <- Hr2; exact ER)
                 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)). }
      split; [reflexivity|].
      rewrite ja2_objs_nil. cbn [map]. apply garr8_nil.
Qed.

End h.
End f.
End d.
