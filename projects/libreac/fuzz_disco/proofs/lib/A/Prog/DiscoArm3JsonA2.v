(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 501 of its 566 lines of code are new or changed and 1213 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3AgeLeft.v, with its module names changed; 516 of its 585 lines of code are new or changed and 497 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC1i YC81 YC4b DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut DiscoArm3JsonMs
DiscoArm3JsonADefs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_age_c slot_ser_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition jsrx (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0 | 18%nat => SOff 32 0
  | 20%nat => SLit WS_MASK | 25%nat => SLit 32
  | _ => SOff (AT_X + r) 0
  end.
Definition jsr : list sv := map jsrx (seq 0 32).
Definition jvals (regs : bvmap 5 word) (ex : list word) : list word :=
  map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32) ++ ex.
Definition NB : nat := 557.
Definition NR : nat := 553.
Definition NB1 : nat := 563.
Definition NSB : nat := 564.
Definition jextra : smem :=
  [YP09.mkRegion (Some NB) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 91)); YP09.mkChunk 1 (CVal 1 (SOff NB1 0))];
   YP09.mkRegion (Some NSB) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))]].
Definition jfa : list (nat * afact) :=
  [(NR, mkAF 2 969 0); (NB, mkAF 4096 (2 ^ 47) 4); (NB1, mkAF 33 255 0); (NSB, mkAF SB (SB + 2 ^ 44) 0)].
Definition jbal_l : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff NB 0) (SLit 3)) (SOff 32 0).
Definition jbal_r : sv := SOff NSB 0.
Definition jmem2 : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 0 0 dslot_chunks;
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 dfhdr_chunks;
   fshadow_region AT_SH DFRAME_CLASS 0 DFRAME_SH (dsh_chunks dsh_ser);
   got_regionP; bcell_regionP 32] ++ jextra.

Lemma sv_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma sp_w64 : forall (regs : bvmap 5 word) v, spZ regs = v -> getr regs 2 = w64 v.
Proof. intros regs v H. unfold spZ in H. unfold w64. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma ser_cap_ge : forall op, 2 < slot_ser_defs.ser_cap op -> 43 <= slot_ser_defs.ser_cap op.
Proof.
  intros op H. unfold slot_ser_defs.ser_cap in *.
  assert (Hk : 0 <= slot_ser_defs.ser_k op) by (unfold slot_ser_defs.ser_k; apply Z.land_nonneg; right; lia).
  destruct (slot_ser_defs.ser_k op =? 0) eqn:E; lia.
Qed.

Lemma apresent_grows : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
  intros H m m' a G (Hh & b & Hb). split; [exact Hh|].
  specialize (G (Z_to_bv 64 a)). unfold mrestrict in G. rewrite Hh, Hb in G. cbn in G.
  destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|].
  exfalso. exact (G ltac:(discriminate) eq_refl).
Qed.

Definition jwok (w : option nat * Z * Z) : bool :=
  let '(b, wlo, whi) := w in (whi <=? wlo) || (obase_eqb b (Some AT_SH) && (0 <=? wlo) && (whi <=? 384)).

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

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma jnth_map_seq : forall (f : nat -> word) j d, (j < 32)%nat -> nth j (map f (seq 0 32)) d = f j.
Proof.
  intros f j d Hj. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma jenv_x : forall (cx : dcx) E regs ex n, (AT_X <= n < AT_X + 32)%nat ->
  ew (d_env cx E (jvals regs ex)) n = getr regs (Z_to_bv 5 (Z.of_nat (n - AT_X))).
Proof.
  intros cx E regs ex n Hn.
  replace n with (AT_X + (n - AT_X))%nat at 1 by lia.
  rewrite d_env_x by (unfold jvals; rewrite length_app, length_map, length_seq; lia).
  unfold jvals. rewrite app_nth1 by (rewrite length_map, length_seq; lia).
  rewrite jnth_map_seq by lia. reflexivity.
Qed.

Lemma jgarr8_kept : forall (H : word -> bool) (m m' : word -> option byte) a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS H m' x = aview SEGS H m x) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H m') a l.
Proof.
  intros H m m' a l HK G j Hj. destruct (G j Hj) as (Hv & Hr). split; [|exact Hr].
  eapply (val_mem_kept SEGS H H m m'); [|exact Hv]. intros kk Hkk. apply HK. lia.
Qed.

Lemma jenv_ex : forall (cx : dcx) E regs ex n, (AT_X + 32 <= n)%nat -> (n - (AT_X + 32) < length ex)%nat ->
  ew (d_env cx E (jvals regs ex)) n = nth (n - (AT_X + 32)) ex (Z_to_bv 64 0).
Proof.
  intros cx E regs ex n Hn Hl.
  replace n with (AT_X + (32 + (n - (AT_X + 32))))%nat at 1 by lia.
  rewrite d_env_x by (unfold jvals; rewrite length_app, length_map, length_seq; lia).
  unfold jvals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
  rewrite length_map, length_seq. f_equal. lia.
Qed.

Lemma jobjs_nil : forall buf vpad, slot_ser_defs.objs_bytes buf vpad [] = [].
Proof. intros buf vpad. reflexivity. Qed.

Lemma jsltu0 : forall E v, ew E v = Z_to_bv 64 2 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SLTU (SAlu ALU_XOR (SLit 2) (SOff v 0)) (SLit 1)) (SLit (-1))) = Z_to_bv 64 0.
Proof.
  intros E v Hv. apply bv_eq. cbn [sv_denot]. rewrite Hv. vm_compute. reflexivity.
Qed.

Lemma jpcall_pi : forall (fq : YK11.FPState) E ss ms (s : dsym),
  st_ok (fx := fq) SEGS E (setpc ss (SIGMA s)) ms ->
  st_ok_pi (fx := fq) SEGS VAL E (setpc ss (SIGMA s - BASE)) ms.
Proof.
  intros fq E ss ms s H. unfold st_ok_pi, abs_ss, setpc in *. destruct ss. simpl.
  replace (BASE + (SIGMA s - BASE)) with (SIGMA s) by lia. exact H.
Qed.

Definition jZs (cx : dcx) (a : Z) : Prop := shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384.

Lemma jwin_ok : forall (cx : dcx) E rs, forallb jwok (windows rs) = true ->
  bv_unsigned (ew E AT_SH) = shadow_addr (d_FB cx) ->
  forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> jZs cx a.
Proof.
  intros cx E rs Hw H529 b wlo whi a Hin Ha.
  pose proof (proj1 (forallb_forall _ _) Hw _ Hin) as Hb. unfold jwok in Hb.
  apply orb_true_iff in Hb as [Hb | Hb]; [apply Z.leb_le in Hb; lia|].
  apply andb_true_iff in Hb as [Hb Hhi]. apply andb_true_iff in Hb as [Hb Hlo].
  apply Z.leb_le in Hhi. apply Z.leb_le in Hlo.
  destruct b as [nb|]; [|discriminate Hb]. cbn [obase_eqb] in Hb. apply Nat.eqb_eq in Hb. subst nb.
  cbn [base_val] in Ha. rewrite H529 in Ha. unfold jZs. lia.
Qed.

Lemma jawr_ok : forall (cx : dcx) E rs bl0 blc ly, forallb jwok (windows rs) = true ->
  bv_unsigned (ew E AT_SH) = shadow_addr (d_FB cx) -> frame_addr ly DFRAME_CLASS (c_fpos cx) = d_FB cx ->
  awr_ok E rs LLVMF_STK (d_S cx) [] bl0 blc ly [(DFRAME_CLASS, c_fpos cx)].
Proof.
  intros cx E rs bl0 blc ly Hw H529 Hfa a (r & Hr & Ha).
  assert (Hin : In (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r) (windows rs)).
  { unfold windows. exact (in_map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) rs r Hr). }
  pose proof (jwin_ok cx E rs Hw H529 _ _ _ a Hin Ha) as HZ. unfold jZs in HZ.
  right. right. right. exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. right.
  unfold in_zr. cbn [fst snd]. rewrite Hfa. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
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
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.

Lemma jsr_regs_ok : forall (cx : dcx) E regs ex, d_E cx E -> d_rL B cx regs ->
  regs_ok (d_env cx E (jvals regs ex)) jsr regs.
Proof.
  intros cx E regs ex HE HRL.
  pose proof HE as (EE & E32 & _ & E60 & _ & _).
  pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs4 & Rs9).
  assert (A60 : ew (d_env cx E (jvals regs ex)) 60 = w64 (d_A cx)) by (rewrite d_env_old by (unfold AT_FL; lia); exact E60).
  assert (A2 : ew (d_env cx E (jvals regs ex)) 2 = w64 (d_S cx)).
  { rewrite d_env_old by (unfold AT_FL; lia). rewrite (EE 2%nat 2%bv eq_refl). unfold d_S, spZ, w64.
    symmetry. apply Z_to_bv_bv_unsigned. }
  assert (A32 : ew (d_env cx E (jvals regs ex)) 32 = w64 SHADOW_OFF) by (rewrite d_env_old by (unfold AT_FL; lia); exact E32).
  apply regs_ok_by_cases. intros z Hz. cbv [all_regs In] in Hz.
  repeat (destruct Hz as [<-|Hz]; [
    lazymatch goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
      let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
    first [ rewrite getr_zero; reflexivity
          | rewrite sv_off0, A60; first [exact Rs1 | exact (sp_w64 _ _ Rsp)]
          | rewrite sv_off0, A2; exact Rs0
          | rewrite sv_off0, A32; exact Rs2
          | cbn [sv_denot]; first [exact Rs4 | exact Rs9]
          | rewrite sv_off0, jenv_x by (unfold AT_X; lia); reflexivity ] | ]).
  destruct Hz.
Qed.

Lemma jfsh_rdset : forall cx h n xb shf ly3 S3 W mem3 md3 k a,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k -> d_body B cx h n xb shf ly3 S3 W mem3 ->
  d_fsh cx a -> ~ d_rdset B cx h a.
Proof.
  intros cx h n xb shf ly3 S3 W mem3 md3 k a HC HBODY Ha.
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
    as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & _ & _ & _ & HAR3 & _ & _ & _).
  pose proof asan_consts as (Hac & _).
  pose proof alloc_ceiling_lt as Hcl.
  destruct HBODY as (T & G & Lk & HL & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HDCAN & HSTKF & HAWRF).
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
  unfold d_rdset, d_objr, d_obj, dobj_off, dobj_size. intros [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | H1]]]]]]].
  - lia.
  - lia.
  - lia.
  - lia.
  - assert (Hin : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & _ & _ & Happ & _).
    change (req_size HUNT_SIZE) with 480 in Happ. unfold HUNT_SIZE in H1.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia.
  - destruct H1 as (Hn0 & H1).
    destruct HC as ((HPRE & _) & _ & _).
    destruct HPRE as (_ & _ & _ & _ & Hpn & _).
    destruct Hpn as [(Hn' & _) | (_ & Hin)]; [lia|].
    assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. right. exact Hin. }
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & _ & _ & Happ & _).
    assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (c_n cx =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | reflexivity]).
    rewrite Hrq in Happ. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia.
  - assert (Himg : in_img SEGS a).
    { destruct H1 as ([(s & Hs & _ & Hr) | Hr] & _); [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hr)]. }
    pose proof (pa_segs_low a Himg) as Hlow. unfold kLowMemEnd in Hlow. lia.
  - unfold AE2k.FF_canary in H1. lia.
Qed.

Lemma jland : forall (fq : YK11.FPState) (cx : dcx) h i n now xb shf shf' pc ly3 S3 (W : world SEGS) mem3 k acc
    (R : bvmap 5 word -> Prop) (X : world SEGS -> (word -> option byte) -> Prop) E ss ms md' (Zs : Z -> Prop),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
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
  (forall a, d_A cx + 152 <= a < d_A cx + 352 -> ~ Zs a) ->
  d_rL B cx (ms_regs ms) -> R (ms_regs ms) -> X W (ms_mem ms) ->
  d_arm_at_pf B MT XM_LIB RLO RHI tfib_K cx pc h i n now xb shf' R X W (mkCfg ms md').
Proof.
  intros fq cx h i n now xb shf shf' pc ly3 S3 W mem3 k acc R X E ss ms md' Zs
    HCSR HBASE HJ HFR Hk Hnev HMO Hacc Hi Hn Hnow HBODY HSP0 HE HFL HS Hrv Hpc Hchk HZs HRD HKEEP HPRES HZA HRL HR HX.
  pose proof (d_body_rt B) as DBRT.
  pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hms.
  pose proof HBODY as (T & G & Lk & HL & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HDCAN & HSTKF & HAWRF).
  pose proof HFRM as (E0 & HE0 & HREG0 & HFLAG0 & H216 & H152).
  assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md' k) by exact (conj HBASE (conj HJ HFR)).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md' k HCTX)
    as (GS16 & GSlo & GShi & _).
  pose proof alloc_ceiling_lt as Hcl. pose proof asan_consts as (Hac & _).
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & _).
  unfold MFRAME, LLVMF_STK in *.
  assert (KV : forall off len v, 152 <= off -> off + Z.of_nat len <= 352 ->
    val_mem SEGS (rd W mem3) (d_A cx + off) len v -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + off) len v).
  { intros off len v H1 H2 Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 (ms_mem ms)); [|exact Hv].
    intros kk Hkk. apply HKEEP; [lia|]. apply HZA. lia. }
  pose proof (DLAND LAWS FFL fq cx h shf' ly3 S3 W md' k E ss ms HCTX HE HFL HS Hchk
    (KV 216 8%nat h ltac:(lia) ltac:(cbn; lia) H216) (KV 152 8%nat (h + 440) ltac:(lia) ltac:(cbn; lia) H152)) as (HFRM' & HSHD').
  pose proof (DBRT cx h n n xb shf shf' ly3 S3 W mem3 (ms_mem ms) (d_S cx - LLVMF_STK) (d_S cx) Zs HBODY
    ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; destruct (HZs a Ha) as [Hs | Hs]; [left; exact Hs | right; exact (HRD a Hs)])
    HKEEP ltac:(intros a _ Ha; exact (HPRES a Ha)) HFRM' HSHD' ltac:(lia)) as HBODY'.
  unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
  split.
  { transitivity (mkCfg (YK11.mkst (fx := fq) (ms_regs ms) (Z_to_bv 64 (BASE + ss_pc ss)) (ms_mem ms) (YK11.seg_rom SEGS)) md');
      [f_equal; exact Hms | unfold cfg_at, w64; rewrite Hpc; reflexivity]. }
  split; [exact HCSR|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hnev|].
  split; [exact HMO|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|]. split; [exact HRL|]. split; [exact HR|].
  split; [exact HX|]. split; [|exact HBODY'].
  destruct HSP0 as (H232 & H344). split.
  - exact (KV 232 8%nat i ltac:(lia) ltac:(cbn; lia) H232).
  - exact (KV 344 8%nat now ltac:(lia) ltac:(cbn; lia) H344).
Qed.

Theorem jA_S2 : jA_S2_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros cx h i n now op W0 c0 T0 T1 buf W c [HFROM HAT].
  unfold d_arm_at_pf, d_at in HAT.
  destruct HAT as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HCSR & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc &
    Hi & Hn & Hnow & HRL & (R22 & R26 & _) & (HSP1 & HTAB & HBUF & _) & HSP0 & HBODY).
  pose proof HTAB as ((removed & HAGE & HPOST) & HGT).
  destruct (jA_fin T0 T1 now removed HPOST Hnow) as (fin & HFIN).
  pose proof HFIN as (HJR & Hfn & HWS & HLEN & HINB).
  pose proof HBUF as (Hr & HGB).
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
  assert (MB0 : val_mem SEGS (rd W mem3) buf 1 91).
  { destruct (HGB 0%nat) as (Hv & _); [rewrite length_app; cbn [length]; unfold jlen in HrB; lia|].
    rewrite app_nth1 in Hv by (unfold jlen in HrB; lia).
    unfold jbyte in Hb0. change (Z.to_nat 0) with 0%nat in Hb0. rewrite Hb0 in Hv.
    change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv. exact Hv. }
  assert (MB1 : val_mem SEGS (rd W mem3) (buf + 1) 1 b1).
  { destruct (HGB 1%nat) as (Hv & _); [rewrite length_app; cbn [length]; unfold jlen in HrB; lia|].
    rewrite app_nth1 in Hv by (unfold jlen in HrB; lia). exact Hv. }
  pose proof HBODY as (T & G & Lk & HL & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HDCAN & HSTKF & HAWRF).
  pose proof HFRM as (E & HE & HREG & HFLAG & H216 & H152).
  pose proof HBLK as (HPerm & _ & _ & HOFFb).
  assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
    as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
  pose proof alloc_ceiling_lt as Hcl. pose proof asan_consts as (Hac & _).
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
  unfold MFRAME, LLVMF_STK in *.
  assert (Hcap : 43 <= slot_ser_defs.ser_cap op) by (apply ser_cap_ge; lia).
  assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). unfold a3_xb. left. reflexivity. }
  assert (Hcap' : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = slot_ser_defs.ser_cap op).
  { rewrite Z.max_l by lia. unfold req_size. destruct (slot_ser_defs.ser_cap op =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | reflexivity]. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _).
  destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (HbSh & _).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hinb HFin3) as Hsep.
  rewrite EFA3 in Hsep. rewrite Hcap' in Hbceil, Hbapp, HbSh, Hsep.
  unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hsep.
  unfold a3_xb in HOFFb. pose proof (Forall_inv (Forall_inv_tail HOFFb)) as HoffB. cbn [fst snd] in HoffB.
  rewrite Hcap' in HoffB.
  assert (MSB : val_mem SEGS (rd W mem3) (shadow_addr buf) 1 0).
  { destruct HbSh as (_ & _ & Hsh). specialize (Hsh 0 ltac:(lia)).
    replace (0 <? slot_ser_defs.ser_cap op / 8) with true in Hsh by (symmetry; apply Z.ltb_lt; lia).
    unfold shadow_of_addr in Hsh. rewrite Z.add_0_r in Hsh. unfold aview in Hsh.
    intros kk Hkk. assert (kk = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
    unfold shadow_addr. destruct (mbyte SEGS (rd W mem3) (SHADOW_OFF + buf / 8)) as [bb|] eqn:Eb; [|discriminate Hsh].
    cbn [option_map] in Hsh. injection Hsh as Hbb. f_equal. apply bv_eq. rewrite Hbb. reflexivity. }
  set (ex := [Z_to_bv 64 b1; Z_to_bv 64 (shadow_addr buf)]).
  set (E' := d_env cx E (jvals regs ex)).
  pose proof HE as (EE & E32 & HEI & E60 & EF & ESH). unfold AT_A, AT_F, AT_SH in E60, EF, ESH.
  assert (AX : forall nn, (AT_X <= nn < AT_X + 32)%nat -> ew E' nn = getr regs (Z_to_bv 5 (Z.of_nat (nn - AT_X))))
    by (intros nn Hnn; apply jenv_x; exact Hnn).
  assert (AO : forall nn, (nn < AT_FL)%nat -> ew E' nn = ew E nn) by (intros nn Hnn; apply d_env_old; exact Hnn).
  assert (EB : ew E' NB = Z_to_bv 64 buf) by (rewrite AX by (unfold NB, AT_X; lia); exact R26).
  assert (ER : ew E' NR = Z_to_bv 64 (a3_r T1 now)) by (rewrite AX by (unfold NR, AT_X; lia); exact R22).
  assert (EB1 : ew E' NB1 = Z_to_bv 64 b1) by (unfold E'; rewrite jenv_ex by (unfold NB1, AT_X; cbn; lia); reflexivity).
  assert (ESB : ew E' NSB = Z_to_bv 64 (shadow_addr buf)) by (unfold E'; rewrite jenv_ex by (unfold NSB, AT_X; cbn; lia); reflexivity).
  assert (E32' : ew E' 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite AO by (unfold AT_FL; lia); exact E32).
  assert (HFB8 : 0 <= d_FB cx / 8 < 2 ^ 44) by lia.
  assert (Hbuf8 : 0 <= buf / 8 < 2 ^ 44) by lia.
  assert (U2 : bv_unsigned (ew E' 2) = d_S cx) by (rewrite AO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
  assert (U60 : bv_unsigned (ew E' 60) = d_A cx) by (rewrite AO, E60 by (unfold AT_FL; lia); apply unsigned_lit_small; lia).
  assert (U516 : bv_unsigned (ew E' 516) = d_FB cx) by (rewrite AO, EF by (unfold AT_FL; lia); apply unsigned_lit_small; lia).
  assert (U529 : bv_unsigned (ew E' 529) = shadow_addr (d_FB cx))
    by (rewrite AO, ESH by (unfold AT_FL; lia); apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
  assert (HEI' : img_env VAL A_LIM E') by exact (proj1 (proj2 (proj2 (d_E_env cx E (jvals regs ex) HE)))).
  assert (UG1 : base_val E' (Some (A_OBJ 1)) = VAL (A_OBJ 1)).
  { cbn [base_val]. rewrite (img_env_atomP E' (A_OBJ 1) HEI' ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
    apply unsigned_lit_small. apply pa_val_range. }
  assert (UG66 : base_val E' (Some (A_OBJ 66)) = VAL (A_OBJ 66)).
  { cbn [base_val]. rewrite (img_env_atomP E' (A_OBJ 66) HEI' ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
    apply unsigned_lit_small. apply pa_val_range. }
  pose proof (pa_obj_img 1 ltac:(vm_compute; lia)) as HO1. pose proof (pa_obj_img 66 ltac:(vm_compute; lia)) as HO66.
  unfold IMG_LO, IMG_TOP in HO1, HO66. unfold off_img, IMG_LO, IMG_TOP in HoffB.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp, GFapp.
  assert (Hr969 : a3_r T1 now <= 969) by (unfold a3_r; lia).
  assert (HFA : atoms_ok E' jfa).
  { unfold jfa. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite ER, EB, EB1, ESB. unfold shadow_addr, SB, SHADOW_OFF in *.
    rewrite !unsigned_lit_small by lia. repeat split; try lia; try exact I. }
  assert (HXR : Forall (region_ok SEGS E' (rd W mem3)) jextra).
  { unfold jextra. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    - rewrite EB, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (chunk_ok_val SEGS E' _ buf 0 1 (SLit 91) 91); [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia | rewrite Z.add_0_r; exact MB0].
      + apply (chunk_ok_val SEGS E' _ buf 1 1 (SOff NB1 0) b1); [rewrite sv_off0; exact EB1 | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia | exact MB1].
    - rewrite ESB, unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
      split; [unfold shadow_addr, SHADOW_OFF; lia|]. split; [unfold shadow_addr, SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E' _ (shadow_addr buf) 0 1 (SLit 0) 0); [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia | rewrite Z.add_0_r; exact MSB]. }
  assert (HPDX : pairwise_disjoint E' jextra).
  { apply pairwise_disjoint_of_extents. unfold jextra, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite EB, ESB.
    rewrite !unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold shadow_addr, SHADOW_OFF.
    repeat split; lia. }
  assert (HDX : Forall (fun r => all_disjoint E' r (d_kregions dsh_ser [] [])) jextra).
  { unfold jextra. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      apply all_disjoint_of_extents; unfold d_kregions, fshadow_region, got_regionP, bcell_regionP, extent_of_region;
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi]; rewrite UG1, UG66; unfold AT_STK, AT_A, AT_F, AT_SH; cbn [base_val];
      rewrite ?EB, ?ESB, U2, U60, U516, U529; rewrite !unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia);
      change (fs_frame_bytes DFRAME_CLASS) with 4096; change (4096 / 8) with 512;
      cbn [zall_disjoint]; unfold zdisj; cbn [fst snd]; unfold shadow_addr, SHADOW_OFF; repeat split; lia. }
  assert (HFACTS := DFACTS LAWS cx ly3 S3 W mem3 md3 k E (jvals regs ex) jfa [] HCTX HE HFA I).
  pose proof (DSEAT LAWS PAL fq cx dsh_ser ly3 S3 W regs mem3 md3 k E JA_RET1 jsr (jvals regs ex) [] [] jextra
    (d_facts jfa []) HCTX HE HREG HFLAG (jsr_regs_ok cx E regs ex HE HRL) HFACTS (Forall_nil _) (Forall_nil _)
    HXR HPDX HDX ltac:(vm_compute; reflexivity)) as HS0.
  fold E' in HS0.
  pose proof (st_ok_pi_add_alias E' _ _ jbal_l jbal_r HS0
    (shadow_decl_ok E' NB 32 NSB buf SHADOW_OFF EB ltac:(lia) E32' ESB)) as HS1.
  clear HS0.
  assert (HSUB : submem jmem2 (ss_mem (set_facts (ss_d JA_RET1 jsr dsh_ser [] [] jextra (d_facts jfa []))
    (mkFacts (f_atoms (ss_facts (ss_d JA_RET1 jsr dsh_ser [] [] jextra (d_facts jfa []))))
             (f_conds (ss_facts (ss_d JA_RET1 jsr dsh_ser [] [] jextra (d_facts jfa []))))
             ((jbal_l, jbal_r) :: f_alias (ss_facts (ss_d JA_RET1 jsr dsh_ser [] [] jextra (d_facts jfa [])))))))).
  { unfold jmem2. cbn [set_facts ss_mem ss_d d_kregions app].
    repeat (apply submem_keep;
      [split; [reflexivity|]; cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
       split; [lia|]; split; [lia|]; split; [lia|]; intros cc Hcc; rewrite ?app_nil_r; exact Hcc |]).
    apply submem_nil. }
  pose proof (st_ok_pi_submem E' _ _ jmem2 HS1 HSUB ltac:(vm_compute; reflexivity)) as HS.
  clear HS1 HSUB. norm_ss HS.
  pose proof (Forall_nil (shent_ok SEGS (SOff 32 0) E' (mrestrict (w_H W) mem3))
    : sh_ok SEGS (SOff 32 0) [] E' (mrestrict (w_H W) mem3)) as SHOK.
  pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
  pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
  pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
  assert (XK : forall mF, (forall a, 0 <= a < 2 ^ 64 -> ~ jZs cx a -> aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem3 a) ->
    d_sp1 cx i n now W mF /\ a3_tab cx now T0 T1 W mF /\ a3_buf op T1 now buf W mF).
  { intros mF HK. split; [|split].
    - destruct HSP1 as ((H232 & H344) & H224 & H248).
      split; [split|split]; (eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mF); [|eassumption]);
        intros kk Hkk; (apply HK; [lia | unfold jZs, shadow_addr, SHADOW_OFF; lia]).
    - destruct HTAB as (HX1 & HGT1). split; [exact HX1|].
      apply (jgarr8_kept (w_H W) mem3 mF); [|exact HGT1].
      rewrite length_map. destruct HPOST as (LT1 & _). rewrite LT1.
      intros x Hx. apply HK; [unfold d_obj, dobj_off in Hx; lia|].
      unfold jZs, d_obj, dobj_off, shadow_addr, SHADOW_OFF in *. lia.
    - split; [exact Hr|]. apply (jgarr8_kept (w_H W) mem3 mF); [|exact HGB].
      rewrite length_app. cbn [length]. unfold a3_r in Hr.
      intros x Hx. apply HK; [lia|]. unfold jZs, shadow_addr, SHADOW_OFF in *. lia. }
  assert (HZs : forall a, jZs cx a -> (d_S cx - LLVMF_STK <= a < d_S cx) \/ d_fsh cx a).
  { intros a Ha. right. unfold d_fsh. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. unfold jZs in Ha. lia. }
  assert (HRD : forall a, d_fsh cx a -> ~ d_rdset B cx h a)
    by (intros a Ha; exact (jfsh_rdset cx h n (a3_xb buf op) dsh_ser ly3 S3 W mem3 md3 k a HCTX HBODY Ha)).
  assert (HZA : forall a, d_A cx + 152 <= a < d_A cx + 352 -> ~ jZs cx a)
    by (intros a Ha; unfold jZs, shadow_addr, SHADOW_OFF; lia).
  pose proof (d_E_env cx E (jvals regs ex) HE) as HE'. fold E' in HE'.
  pose proof (d_env_fl cx E (jvals regs ex)) as HFL'. fold E' in HFL'.
  pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs4 & Rs9).
  assert (A2 : ew E' 2 = w64 (d_S cx)).
  { rewrite AO by (unfold AT_FL; lia). rewrite (EE 2%nat 2%bv eq_refl). unfold d_S, spZ, w64.
    symmetry. apply Z_to_bv_bv_unsigned. }
  assert (A60 : ew E' 60 = w64 (d_A cx)) by (rewrite AO by (unfold AT_FL; lia); exact E60).
  assert (A516 : ew E' 516 = w64 (d_FB cx)) by (rewrite AO by (unfold AT_FL; lia); exact EF).
  paj_run_tok RUN HS HJ SHOK (0, 0).
  { eapply jawr_ok; [vm_compute; reflexivity | exact U529 | exact EFA3]. }
  lazymatch goal with HFr0 : frame_of _ ?rs0 (mrestrict _ mem3) (mrestrict _ (ms_mem ?m1)), HG0 : mem_grows _ _ |- _ =>
    assert (HWW0 : forallb jwok (windows rs0) = true) by (vm_compute; reflexivity);
    pose proof (kept_of_frame (segs := SEGS) E' rs0 (w_H W) mem3 (ms_mem m1) (jZs cx) HFr0
      (jwin_ok cx E' rs0 HWW0 U529)) as KEEP1;
    pose proof (fun a => apresent_grows (w_H W) mem3 (ms_mem m1) a HG0) as PRES1 end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  - rewrite branch_ne_U, (U_atom E' 563%nat b1 EB1 ltac:(lia)), U_lit in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc.
    destruct HCASE as [(Hat & _ & _) | (_ & HOBJS)].
    { exfalso. apply at_byte_true in Hat as (_ & Hat). exact (Hc Hat). }
    paj_run_tok RUN HS HJ SHOK (0, 0).
    { eapply jawr_ok; [vm_compute; reflexivity | exact U529 | exact EFA3]. }
    lazymatch goal with HFr0 : frame_of _ ?rs0 (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)), HG0 : mem_grows _ _ |- _ =>
      assert (HWW1 : forallb jwok (windows rs0) = true) by (vm_compute; reflexivity);
      pose proof (kept_of_frame (segs := SEGS) E' rs0 (w_H W) (ms_mem m1) (ms_mem m2) (jZs cx) HFr0
        (jwin_ok cx E' rs0 HWW1 U529)) as KEEP2;
      pose proof (fun a => apresent_grows (w_H W) (ms_mem m1) (ms_mem m2) a HG0) as PRES2;
      assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ jZs cx a -> aview SEGS (w_H W) (ms_mem m2) a = aview SEGS (w_H W) mem3 a)
        by (intros a Ha Hnz; rewrite (KEEP2 a Ha Hnz); exact (KEEP1 a Ha Hnz));
      assert (PRESF : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem m2) a)
        by (intros a Ha; exact (PRES2 a (PRES1 a Ha))) end.
    lazymatch goal with
    | HS0 : st_ok _ _ (setpc ?ssF _) (restrict _ ?mF), HJF : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdF _ |- _ =>
      pose proof (jpcall_pi fq E' ssF (restrict (w_H W) mF) DS___asan_memset HS0) as HSp;
      jregq HS0 (1%bv : bv 5) Q1; jregq HS0 (2%bv : bv 5) Q2; jregq HS0 (3%bv : bv 5) Q3; jregq HS0 (4%bv : bv 5) Q4;
      jregq HS0 (8%bv : bv 5) Q8; jregq HS0 (9%bv : bv 5) Q9; jregq HS0 (10%bv : bv 5) Q10; jregq HS0 (11%bv : bv 5) Q11;
      jregq HS0 (12%bv : bv 5) Q12; jregq HS0 (18%bv : bv 5) Q18; jregq HS0 (20%bv : bv 5) Q20;
      jregq HS0 (22%bv : bv 5) Q22; jregq HS0 (23%bv : bv 5) Q23; jregq HS0 (24%bv : bv 5) Q24;
      jregq HS0 (25%bv : bv 5) Q25; jregq HS0 (26%bv : bv 5) Q26;
      apply SRr_ret; right; exists fin; unfold ms_in, jcut; split; [exact HFROM|];
      apply (jland fq cx h i n now (a3_xb buf op) dsh_ser dsh_scr (SIGMA DS___asan_memset - BASE) ly3 S3 W mem3 k acc _ _ E'
               (setpc ssF (SIGMA DS___asan_memset - BASE)) mF mdF (jZs cx) HCSR HBASE HJF HFR Hk Hnev HMO Hacc Hi Hn Hnow
               HBODY HSP0 HE' HFL' HSp ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
               HZs HRD KEEPF PRESF HZA)
    end.
    + rewrite sv_off0, A60 in Q2. rewrite sv_off0, AX in Q3 by (unfold AT_X; lia).
      rewrite sv_off0, AX in Q4 by (unfold AT_X; lia). rewrite sv_off0, A2 in Q8. rewrite sv_off0, A60 in Q9.
      rewrite sv_off0, E32' in Q18. cbn [sv_denot] in Q20, Q25.
      split; [unfold spZ; rewrite Q2; apply unsigned_lit_small; lia|].
      split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [exact Q8|]. split; [exact Q9|].
      split; [exact Q18|]. split; [exact Q20 | exact Q25].
    + cbv beta. rewrite sv_off0, AX in Q22 by (unfold AT_X; lia). rewrite sv_off0, AX in Q26 by (unfold AT_X; lia).
      cbn [sv_denot] in Q10, Q11, Q12, Q23, Q24. rewrite A516 in Q10, Q23.
      rewrite unsigned_lit_small in Q10, Q23 by lia.
      split; [rewrite Q22; exact R22|]. split; [rewrite Q26; exact R26|].
      split; [rewrite Q1; exact (codeptr_val E' 4168 HEI')|].
      split; [rewrite Q10; unfold jcur, d_obj, dobj_off, w64; f_equal; lia|].
      split; [exact Q11|]. split; [exact Q12|].
      split; [rewrite Q23; unfold jcur, d_obj, dobj_off, w64; f_equal; lia | exact Q24].
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
    { eapply jawr_ok; [vm_compute; reflexivity | exact U529 | exact EFA3]. }
    lazymatch goal with HFr0 : frame_of _ ?rs0 (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)), HG0 : mem_grows _ _ |- _ =>
      assert (HWW1 : forallb jwok (windows rs0) = true) by (vm_compute; reflexivity);
      pose proof (kept_of_frame (segs := SEGS) E' rs0 (w_H W) (ms_mem m1) (ms_mem m2) (jZs cx) HFr0
        (jwin_ok cx E' rs0 HWW1 U529)) as KEEP2;
      pose proof (fun a => apresent_grows (w_H W) (ms_mem m1) (ms_mem m2) a HG0) as PRES2;
      assert (KEEPA : forall a, 0 <= a < 2 ^ 64 -> ~ jZs cx a -> aview SEGS (w_H W) (ms_mem m2) a = aview SEGS (w_H W) mem3 a)
        by (intros a Ha Hnz; rewrite (KEEP2 a Ha Hnz); exact (KEEP1 a Ha Hnz));
      assert (PRESA : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem m2) a)
        by (intros a Ha; exact (PRES2 a (PRES1 a Ha))) end.
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
    clear KEEP1 KEEP2 PRES1 PRES2.
    psrr_branch_tok RUN BR HS SHOK (0, 0).
    2: { exfalso. rewrite branch_geu_U, (U_atom E' 553%nat (a3_r T1 now) ER ltac:(lia)), U_lit in Hc0 by lia.
         apply negb_false_iff, Z.ltb_lt in Hc0. lia. }
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) R12_OFF.
    { eapply jawr_ok; [vm_compute; reflexivity | exact U529 | exact EFA3]. }
    lazymatch goal with HFr0 : frame_of _ ?rs0 (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)), HG0 : mem_grows _ _ |- _ =>
      assert (HWW2 : forallb jwok (windows rs0) = true) by (vm_compute; reflexivity);
      pose proof (kept_of_frame (segs := SEGS) E' rs0 (w_H W) (ms_mem m1) (ms_mem m2) (jZs cx) HFr0
        (jwin_ok cx E' rs0 HWW2 U529)) as KEEP3;
      pose proof (fun a => apresent_grows (w_H W) (ms_mem m1) (ms_mem m2) a HG0) as PRES3;
      assert (KEEPG : forall a, 0 <= a < 2 ^ 64 -> ~ jZs cx a -> aview SEGS (w_H W) (ms_mem m2) a = aview SEGS (w_H W) mem3 a)
        by (intros a Ha Hnz; rewrite (KEEP3 a Ha Hnz); exact (KEEPA a Ha Hnz));
      assert (PRESG : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem m2) a)
        by (intros a Ha; exact (PRES3 a (PRESA a Ha))) end.
    lazymatch goal with
    | HS0 : st_ok_pi _ _ _ ?ssF (restrict _ ?mF), HJF : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdF _ |- _ =>
      jregq HS0 (1%bv : bv 5) Q1; jregq HS0 (2%bv : bv 5) Q2; jregq HS0 (3%bv : bv 5) Q3; jregq HS0 (4%bv : bv 5) Q4;
      jregq HS0 (8%bv : bv 5) Q8; jregq HS0 (9%bv : bv 5) Q9; jregq HS0 (18%bv : bv 5) Q18; jregq HS0 (20%bv : bv 5) Q20;
      jregq HS0 (21%bv : bv 5) Q21; jregq HS0 (25%bv : bv 5) Q25; jregq HS0 (26%bv : bv 5) Q26;
      apply SRr_ret; left; exists 0, (@nil jobj), (repeat (Z_to_bv 8 0) 4);
      unfold r12_in; split; [exact HFROM|];
      apply (jland fq cx h i n now (a3_xb buf op) dsh_ser dsh_ser R12_OFF ly3 S3 W mem3 k acc
               (fun regs => bv_unsigned (getr regs 21) mod 2 ^ 32 = 0 /\ getr regs 26 = w64 buf)
               (fun W1 m1 => d_sp1 cx i n now W1 m1 /\ a3_tab cx now T0 T1 W1 m1 /\ a3_buf op T1 now buf W1 m1 /\
                  json_read (a3_text T1 now) 9 = Some (0, @nil jobj) /\ length (repeat (Z_to_bv 8 0) 4) = 4%nat /\
                  garr8 SEGS (mrestrict (w_H W1) m1) (d_obj cx OO)
                    (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf (repeat (Z_to_bv 8 0) 4) (@nil jobj))))
               E' ssF mF mdF (jZs cx) HCSR HBASE HJF HFR Hk Hnev HMO Hacc Hi Hn Hnow
               HBODY HSP0 HE' HFL' HS0 ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
               HZs HRD KEEPG PRESG HZA)
    end.
    + rewrite sv_off0, A60 in Q2. rewrite sv_off0, AX in Q3 by (unfold AT_X; lia).
      rewrite sv_off0, AX in Q4 by (unfold AT_X; lia). rewrite sv_off0, A2 in Q8. rewrite sv_off0, A60 in Q9.
      rewrite sv_off0, E32' in Q18. cbn [sv_denot] in Q20, Q25.
      split; [unfold spZ; rewrite Q2; apply unsigned_lit_small; lia|].
      split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [exact Q8|]. split; [exact Q9|].
      split; [exact Q18|]. split; [exact Q20 | exact Q25].
    + cbv beta. rewrite sv_off0, AX in Q26 by (unfold AT_X; lia).
      rewrite (jsltu0 E' 553%nat ltac:(rewrite <- Hr2; exact ER)) in Q21.
      split; [rewrite Q21; vm_compute; reflexivity | rewrite Q26; exact R26].
    + cbv beta. destruct (XK _ KEEPG) as (X1 & X2 & X3).
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
      split; [rewrite <- Hfin; exact HJR|]. split; [reflexivity|].
      rewrite jobjs_nil. cbn [map]. apply garr8_nil.
Qed.

End h.
End f.
End d.
