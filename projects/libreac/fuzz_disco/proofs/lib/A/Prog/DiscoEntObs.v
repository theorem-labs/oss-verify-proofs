(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 959 of its 988 lines of code are new or changed and 40 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YC88 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody FindEntry CheckTable ReacDiscoTableObserve DiscoEntObsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_observe_c slot_observe slot_known slot_newent CtrlParsed.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Let DSEAT := d_seat B MT XM_LIB RLO RHI tfib_K.
Let DFACTS := d_facts_ok B MT XM_LIB RLO RHI tfib_K.
Let DLAND := d_land B MT XM_LIB RLO RHI tfib_K.
Let DBRT := d_body_rt B.
Let DBCK := d_body_call_keep B MT XM_LIB RLO RHI tfib_K.
Let DBTOBS := d_body_tobs B MT XM_LIB RLO RHI tfib_K.
Let DBREAD := d_body_read B.
Hypothesis TFIND : tfind_entry_spec B.
Hypothesis TCHK : tcheck_table_spec B.
Hypothesis TTOBS : treac_disco_table_observe_spec B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Hypothesis DCAN : asink_img_laws SEGS B tfib_K /\ ak_canary tfib_K = AE2k.FF_canary.
#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).
#[local] Notation oc := (oc B).
#[local] Notation ob_c0 := (ob_c0 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation ob_c1 := (ob_c1 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation ob_c2 := (ob_c2 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation ob_c3 := (ob_c3 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation ob_c4 := (ob_c4 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation ob_c5 := (ob_c5 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation ob_c6 := (ob_c6 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation ob_c7 := (ob_c7 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation ob_c8 := (ob_c8 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation ob_c9 := (ob_c9 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation ob_c10 := (ob_c10 B MT XM_LIB RLO RHI tfib_K).

Lemma ob_s01 : forall cx h i n now op nb fr len Sg kmax accmax W c,
  ob_c0 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c1 cx h i n now op nb fr len Sg kmax accmax).
Proof.
intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfz & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & T & HOC & HrO).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcanb & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
destruct (ob_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
pose proof (DSEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E OBS_OFF obs_sr (obs_vals regs) [] [] [] (d_facts [] [])
  HctxD HdE Hregs Hflag (regs_ok_obs B cx E regs HdE HrL HAr2)
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (obs_vals regs) [] [] HctxD HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
ro_base HS 516%nat. ro_base HS 529%nat. ro_base HS 60%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E (obs_vals regs))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (obs_vals regs)) (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + OBS_OFF)) with (Z_to_bv 64 (BASE + OBS_OFF)).
paj_run_tok RUN HS HJ SHOK OBspan.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Hpt := frame_of_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
assert (Hptr := frame_of_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
assert (Hsig := pa_sigma_find_entry (PI := PI)).
rewrite Hsig in HS.
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 22; 25; 26]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS). rewrite (regs_ok_obs B cx E regs HdE HrL HAr2 r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms HS eq_refl) as Hms.
cbn [ss_pc setpc] in Hms.
lazymatch type of HS with st_ok _ ?Ex (setpc ?ssx _) ?msx =>
  assert (HSpi : st_ok_pi SEGS VAL Ex (setpc ssx AF_find_entry) msx) by exact HS end.
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (Hctx4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md4 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
assert (H216' := val_mem_pt _ _ _ _ _ Hptr Hh216).
assert (H152' := val_mem_pt _ _ _ _ _ Hptr Hh152).
destruct (DLAND LAWS FFL fq cx h dsh_rec ly3 S3 W md4 k (d_env cx E (obs_vals regs)) _ ms Hctx4 (d_E_env cx E _ HdE)
  (d_env_fl cx E _) HSpi ltac:(vm_compute; reflexivity) H216' H152') as [Hframe4 Hshadow4].
assert (Hbody4 : d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms)).
{ apply (DBRT cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 (ms_mem ms) (d_A cx) (d_A cx) (fun _ => False) Hbody).
  - unfold LLVMF_STK; lia.
  - lia.
  - intros a [].
  - intros a Ha _. apply aview_eq_of. apply Hptr.
  - intros a _ [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite Hpt. exact Hb.
  - exact Hframe4.
  - exact Hshadow4.
  - lia. }
assert (R2 := RG 2%bv ltac:(cbv; tauto)). assert (R3 := RG 3%bv ltac:(cbv; tauto)). assert (R4 := RG 4%bv ltac:(cbv; tauto)).
assert (R8 := RG 8%bv ltac:(cbv; tauto)). assert (R9 := RG 9%bv ltac:(cbv; tauto)). assert (R18 := RG 18%bv ltac:(cbv; tauto)).
assert (R20 := RG 20%bv ltac:(cbv; tauto)). assert (R22 := RG 22%bv ltac:(cbv; tauto)). assert (R25 := RG 25%bv ltac:(cbv; tauto)).
assert (R26 := RG 26%bv ltac:(cbv; tauto)).
assert (EFB : ew (d_env cx E (obs_vals regs)) 516 = Z_to_bv 64 (d_FB cx)).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia). destruct HdE as (_ & _ & _ & _ & HF & _). exact HF. }
assert (RA : forall r : bv 5, getr (ms_regs ms) r = sv_denot (d_env cx E (obs_vals regs)) (sr_get (ss_regs (setpc (mkSS 0 [] [] None (mkFacts [] [] [])) 0)) r) -> True) by (intros; exact I).
clear RA.
apply SRr_ret. unfold ob_c1, d_at.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md4, k, acc.
split; [unfold cfg_at, w64; rewrite <- Hms; reflexivity|].
split; [exact Hfz|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
exists T. split; [|split].
- unfold oc.
  refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj _ (conj _ (conj _ (conj HSgl (conj _ (conj HSf
    (conj _ (conj _ (conj _ (conj _ (conj Hlen (conj Hnb (conj HTl (conj _ (conj HTok Hbody4)))))))))))))))))))).
  + destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25). unfold d_rL, spZ in *.
    rewrite R2, R3, R4, R8, R9, R18, R20, R25. repeat split; assumption.
  + destruct Hsp0 as (Hs1 & Hs2). split; eapply val_mem_pt; [exact Hptr | exact Hs1 | exact Hptr | exact Hs2].
  + destruct Hfrm as (F1 & F2 & Fn & F3). split; [exact F1|]. split; [exact F2|]. split; [exact Fn|]. exact (garr8_pt _ _ _ _ Hptr F3).
  + exact (garr8_pt _ _ _ _ Hptr HSg).
  + exact (val_mem_pt _ _ _ _ _ Hptr H248).
  + exact (val_mem_pt _ _ _ _ _ Hptr H336).
  + exact (val_mem_pt _ _ _ _ _ Hptr H368).
  + exact (val_mem_pt _ _ _ _ _ Hptr H280).
  + exact (garr8_pt _ _ _ _ Hptr HT).
- destruct HrO as (H22 & H26). unfold dR_obs. rewrite R22, R26. split; assumption.
- split; [|split; [|split]].
  + rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    unfold w64. replace (OBS_OFF + 16) with 3620 by reflexivity. exact (codeptr_val _ 3620 HEI).
  + rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    cbn [sv_denot]. rewrite EFB, w64_add_w. reflexivity.
  + rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 11%bv HS).
    transitivity (getr regs 22); [|destruct HrO as (H22 & _); exact H22].
    rewrite (regs_ok_obs B cx E regs HdE HrL HAr2 22%bv). f_equal; try (vm_compute; reflexivity).
  + rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 27%bv HS).
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    cbn [sv_denot]. rewrite EFB, w64_add_w. reflexivity.
Qed.

Lemma val_mem_keep : forall (W W' : world SEGS) (m m' : word -> option byte) a n v,
  (forall j, (j < n)%nat -> aview SEGS (w_H W') m' (a + Z.of_nat j) = aview SEGS (w_H W) m (a + Z.of_nat j)) ->
  val_mem SEGS (rd W m) a n v -> val_mem SEGS (rd W' m') a n v.
Proof. intros W W' m m' a n v Hk H j Hj. rewrite (mbyte_of_aview SEGS _ _ _ _ _ (Hk j Hj)). exact (H j Hj). Qed.
Lemma garr8_keep : forall (W W' : world SEGS) (m m' : word -> option byte) a l,
  (forall j, (j < length l)%nat -> aview SEGS (w_H W') m' (a + Z.of_nat j) = aview SEGS (w_H W) m (a + Z.of_nat j)) ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W' m') a l.
Proof.
intros W W' m m' a l Hk H j Hj. destruct (H j Hj) as [H1 H2]. split; [|exact H2].
apply (val_mem_keep W W' m m' _ 1 _); [|exact H1].
intros k Hk'. replace (a + Z.of_nat j + Z.of_nat k) with (a + Z.of_nat j) by lia. exact (Hk j Hj).
Qed.
Lemma region_ok_keep : forall E (W W' : world SEGS) (m m' : word -> option byte) r,
  region_ok SEGS E (rd W m) r ->
  (forall c i, In c (YP09.r_chunks r) -> 0 <= i < YP09.c_len c ->
     aview SEGS (w_H W') m' (base_val E (YP09.r_base r) + YP09.c_off c + i) =
     aview SEGS (w_H W) m (base_val E (YP09.r_base r) + YP09.c_off c + i)) ->
  (forall o, YP09.r_wlo r <= o < YP09.r_whi r -> apresent (w_H W') m' (base_val E (YP09.r_base r) + o)) ->
  region_ok SEGS E (rd W' m') r.
Proof.
intros E W W' m m' r (H1 & H2 & H3 & H4) Hc Hp. unfold region_ok.
split; [exact H1|]. split; [exact H2|]. split.
- intros o Ho. apply (apresent_writable SEGS). apply Hp. exact Ho.
- rewrite Forall_forall in *. intros c Hin i Hi. destruct (H4 c Hin i Hi) as (b & Hb & Hm).
  exists b. split; [exact Hb|]. rewrite (mbyte_of_aview SEGS _ _ _ _ _ (Hc c i Hin Hi)). exact Hm.
Qed.
Lemma rdword_keep : forall (rd rd' : reader) a, (forall j, 0 <= j < 8 -> rd' (a + j) = rd (a + j)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. unfold rdword.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma aview_present : forall H (m : word -> option byte) a, apresent H m a -> exists b : byte, aview SEGS H m a = Some (bv_unsigned b).
Proof. intros H m a [Hh [b Hb]]. exists b. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. reflexivity. Qed.
Lemma ex_val_mem8 : forall H (m : word -> option byte) a, (forall j, 0 <= j < 8 -> apresent H m (a + j)) ->
  exists v, val_mem SEGS (mrestrict H m) a 8 v /\ 0 <= v < 2 ^ 64.
Proof.
intros H m a Hp.
destruct (aview_present H m _ (Hp 0 ltac:(lia))) as [b0 E0]. rewrite Z.add_0_r in E0.
destruct (aview_present H m _ (Hp 1 ltac:(lia))) as [b1 E1]. destruct (aview_present H m _ (Hp 2 ltac:(lia))) as [b2 E2].
destruct (aview_present H m _ (Hp 3 ltac:(lia))) as [b3 E3]. destruct (aview_present H m _ (Hp 4 ltac:(lia))) as [b4 E4].
destruct (aview_present H m _ (Hp 5 ltac:(lia))) as [b5 E5]. destruct (aview_present H m _ (Hp 6 ltac:(lia))) as [b6 E6].
destruct (aview_present H m _ (Hp 7 ltac:(lia))) as [b7 E7].
lazymatch goal with |- exists v, _ => idtac end.
assert (Hr : exists v, rdword (aview SEGS H m) a = Some v) by (unfold rdword; rewrite E0, E1, E2, E3, E4, E5, E6, E7; eexists; reflexivity).
destruct Hr as [v Hr]. exists v. split; [exact (val_mem_of_rdword SEGS H m a v Hr) | exact (rdword_aview_range SEGS H m a v Hr)].
Qed.
Lemma d_shadow_keep : forall cx shf (W W' : world SEGS) (m m' : word -> option byte),
  d_shadow cx shf W m ->
  (forall k, 0 <= k < DFRAME_SH -> aview SEGS (w_H W') m' (shadow_addr (d_FB cx) + k) = aview SEGS (w_H W) m (shadow_addr (d_FB cx) + k)) ->
  d_shadow cx shf W' m'.
Proof. intros cx shf W W' m m' H Hk k Hkk. rewrite (Hk k Hkk). exact (H k Hkk). Qed.

Lemma d_frame_keep : forall cx h shf (W W' : world SEGS) (m m' : word -> option byte) ly3 S3 md3 k,
  d_frame cx h shf W m -> d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W' m' md3 k ->
  (forall a, (d_A cx <= a < d_S cx \/ d_FB cx <= a < d_FB cx + 24 \/ d_FB cx + 4088 <= a < d_FB cx + 4096 \/
              shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  d_frame cx h shf W' m'.
Proof.
intros cx h shf W W' m m' ly3 S3 md3 k (E & HE & Hregs & Hflag & H216 & H152) Hctx Hkeep.
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W' m' md3 k Hctx)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
pose proof HE as (HER & H32 & HI & HA & HF & HSH).
assert (B2 : bv_unsigned (ew E AT_STK) = d_S cx) by (change AT_STK with 2%nat; rewrite (HER 2%nat 2%bv eq_refl); reflexivity).
assert (BA : bv_unsigned (ew E AT_A) = d_A cx) by (rewrite HA; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
assert (BF : bv_unsigned (ew E AT_F) = d_FB cx) by (rewrite HF; apply unsigned_lit_small; lia).
assert (BSH : bv_unsigned (ew E AT_SH) = shadow_addr (d_FB cx)).
{ rewrite HSH; apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. split; [|apply Z.lt_le_trans with (2147450880 + 2 ^ 47 / 8 + 1); [|lia]]; 
  pose proof (Z.div_pos (d_FB cx) 8 ltac:(lia) ltac:(lia)); [lia|]. assert (d_FB cx / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). lia. }
change (fs_frame_bytes DFRAME_CLASS) with 4096 in *.
exists E. split; [exact HE|]. split; [|split; [|split]].
- unfold d_regions in *. rewrite !Forall_cons_iff in Hregs. destruct Hregs as (R1 & R2 & R3 & R4 & _).
  repeat (apply Forall_cons); [| | | | apply Forall_nil].
  + apply (region_ok_keep E W W' m m' _ R1).
    * intros c i Hin Hi. cbn [YP09.r_chunks YP09.r_base base_val] in *. rewrite B2.
      unfold dsave_chunks in Hin. apply in_map_iff in Hin as (j & <- & Hj). apply in_seq in Hj.
      cbn [length dsave_regs] in Hj. cbn [YP09.c_off YP09.c_len YP09.c_val cv_len Z.of_N] in *.
      apply Hkeep. left. lia.
    * cbn. intros o Ho. lia.
  + apply (region_ok_keep E W W' m m' _ R2).
    * intros c i Hin Hi. cbn [YP09.r_chunks YP09.r_base base_val] in *. rewrite BA.
      unfold dslot_chunks in Hin. apply in_map_iff in Hin as (kv & <- & Hkv).
      assert (Hkv' : 0 <= fst kv <= 416) by (cbn [In] in Hkv; repeat destruct Hkv as [<-|Hkv]; cbn; lia).
      cbn [YP09.c_off YP09.c_len YP09.c_val cv_len Z.of_N] in *. apply Hkeep. left. lia.
    * cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val]. rewrite BA. intros o Ho. apply HStk. unfold LLVMF_STK. lia.
  + apply (region_ok_keep E W W' m m' _ R3).
    * intros c i Hin Hi. cbn [YP09.r_chunks YP09.r_base base_val] in *. rewrite BF.
      cbn [In] in Hin. repeat destruct Hin as [<-|Hin]; [..|destruct Hin]; cbn [YP09.c_off YP09.c_len YP09.c_val cv_len Z.of_N] in *;
      apply Hkeep; right; left; lia.
    * cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val]. rewrite BF. intros o Ho. apply HFp. unfold DFRAME_SIZE in Ho. lia.
  + apply (region_ok_keep E W W' m m' _ R4).
    * intros c i Hin Hi. cbn [YP09.r_chunks YP09.r_base base_val fshadow_region] in *. rewrite BSH.
      unfold dsh_chunks in Hin. apply in_map_iff in Hin as (j & <- & Hj). apply in_seq in Hj.
      cbn [YP09.c_off YP09.c_len YP09.c_val cv_len Z.of_N] in *. unfold DFRAME_SH in Hj.
      apply Hkeep. right; right; right. lia.
    * cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val fshadow_region]. rewrite BSH. intros o Ho. apply HSp. unfold DFRAME_SH in Ho. lia.
- rewrite (rdword_keep (aview SEGS (w_H W) m) (aview SEGS (w_H W') m')); [exact Hflag|].
  intros j Hj. apply Hkeep. right; right; left. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
- apply (val_mem_keep W W' m m' _ 8 _); [|exact H216]. intros j Hj. apply Hkeep. left. lia.
- apply (val_mem_keep W W' m m' _ 8 _); [|exact H152]. intros j Hj. apply Hkeep. left. lia.
Qed.

Lemma dsh_rec_t : forall k, 270 <= k < 320 -> dsh_rec k = 0.
Proof.
intros k Hk. assert (Hj : exists j, (j < 50)%nat /\ k = 270 + Z.of_nat j) by (exists (Z.to_nat (k - 270)); lia).
destruct Hj as (j & Hj & ->). do 50 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma dsh_rec_s : forall k, 374 <= k < 377 -> dsh_rec k = 0.
Proof.
intros k Hk. assert (Hj : exists j, (j < 3)%nat /\ k = 374 + Z.of_nat j) by (exists (Z.to_nat (k - 374)); lia).
destruct Hj as (j & Hj & ->). do 3 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma shadow_addr_off : forall F o, F mod 8 = 0 -> shadow_addr (F + o) = shadow_addr F + o / 8.
Proof.
intros F o HF. unfold shadow_addr. pose proof (Z.div_mod F 8 ltac:(lia)) as D.
replace (F + o) with (o + F / 8 * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.
Lemma ra_frame : forall cx shf (W : world SEGS) (m : word -> option byte) lo len,
  d_shadow cx shf W m -> d_FB cx mod 8 = 0 -> 0 <= lo -> 0 <= len -> lo + len <= 3072 ->
  (forall k, lo / 8 <= k < (lo + len + 7) / 8 -> shf k = 0) ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (d_FB cx + lo) len.
Proof.
intros cx shf W m lo len Hsh HF8 Hlo Hlen Hhi Hz x Hx. exists 0. split; [|left; reflexivity].
assert (Hq : shadow_of_addr SHADOW_OFF x = shadow_addr (d_FB cx) + (x - d_FB cx) / 8).
{ rewrite <- shadow_addr_off by exact HF8. replace (d_FB cx + (x - d_FB cx)) with x by lia. reflexivity. }
rewrite Hq. rewrite (Hsh ((x - d_FB cx) / 8)).
- rewrite Hz; [reflexivity|]. split; [apply Z.div_le_mono; lia|].
  apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.mod_pos_bound (lo + len + 7) 8 ltac:(lia)).
  pose proof (Z.div_mod (lo + len + 7) 8 ltac:(lia)). lia.
- unfold DFRAME_SH. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.
Lemma hull_frame : forall cx shf (W : world SEGS) (m : word -> option byte) lo len,
  d_shadow cx shf W m -> d_FB cx mod 8 = 0 -> 64 <= lo -> 0 < len -> lo + len <= 3016 ->
  shadow_hull_vis (aview SEGS (w_H W) m) (d_FB cx + lo) len.
Proof.
intros cx shf W m lo len Hsh HF8 Hlo Hlen Hhi s Hs.
assert (E1 : shadow_addr (d_FB cx + lo) = shadow_addr (d_FB cx) + lo / 8) by (apply shadow_addr_off; exact HF8).
assert (E2 : shadow_addr (d_FB cx + lo + len - 1) = shadow_addr (d_FB cx) + (lo + len - 1) / 8).
{ replace (d_FB cx + lo + len - 1) with (d_FB cx + (lo + len - 1)) by lia. apply shadow_addr_off; exact HF8. }
rewrite E1, E2 in Hs.
pose proof (Z.div_mod (shadow_addr (d_FB cx) + lo / 8) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (shadow_addr (d_FB cx) + lo / 8) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (shadow_addr (d_FB cx) + (lo + len - 1) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (shadow_addr (d_FB cx) + (lo + len - 1) / 8) 8 ltac:(lia)) as M2.
assert (Lb : 8 <= lo / 8) by (apply Z.div_le_lower_bound; lia).
assert (Ub : (lo + len - 1) / 8 < 377) by (apply Z.div_lt_upper_bound; lia).
replace s with (shadow_addr (d_FB cx) + (s - shadow_addr (d_FB cx))) by lia.
rewrite (Hsh (s - shadow_addr (d_FB cx))); [discriminate|]. unfold DFRAME_SH. lia.
Qed.

Lemma oc_val_keep : forall (W W' : world SEGS) (m m' : word -> option byte) lo hi a n v,
  d_kept (fun x => lo <= x < hi) W m W' m' -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= lo \/ hi <= a) ->
  val_mem SEGS (rd W m) a n v -> val_mem SEGS (rd W' m') a n v.
Proof. intros W W' m m' lo hi a n v HK H0 H1 H2. apply val_mem_keep. intros j Hj. apply HK; lia. Qed.
Lemma oc_garr8_keep : forall (W W' : world SEGS) (m m' : word -> option byte) lo hi a l,
  d_kept (fun x => lo <= x < hi) W m W' m' -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  (a + Z.of_nat (length l) <= lo \/ hi <= a) ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W' m') a l.
Proof. intros W W' m m' lo hi a l HK H0 H1 H2. apply garr8_keep. intros j Hj. apply HK; lia. Qed.
Lemma d_rL_pres : forall cx regs regs', aregs_preserved regs regs' -> d_rL B cx regs -> d_rL B cx regs'.
Proof.
intros cx regs regs' HP (H2 & H3 & H4 & H8 & H9 & H18 & H20 & H25). unfold d_rL.
split; [unfold spZ in *; rewrite <- H2; f_equal; exact (HP 2 ltac:(unfold acallee_saved; lia))|].
split; [transitivity (getr regs 3%bv); [exact (HP 3 ltac:(unfold acallee_saved; lia)) | exact H3]|].
split; [transitivity (getr regs 4%bv); [exact (HP 4 ltac:(unfold acallee_saved; lia)) | exact H4]|].
split; [transitivity (getr regs 8%bv); [exact (HP 8 ltac:(unfold acallee_saved; lia)) | exact H8]|].
split; [transitivity (getr regs 9%bv); [exact (HP 9 ltac:(unfold acallee_saved; lia)) | exact H9]|].
split; [transitivity (getr regs 18%bv); [exact (HP 18 ltac:(unfold acallee_saved; lia)) | exact H18]|].
split; [transitivity (getr regs 20%bv); [exact (HP 20 ltac:(unfold acallee_saved; lia)) | exact H20]|].
transitivity (getr regs 25%bv); [exact (HP 25 ltac:(unfold acallee_saved; lia)) | exact H25].
Qed.

Lemma oc_call_keep : forall cx h i n now op nb fr len Sg T regs ly3 S3 W3 m3 md3 k3 regs' ly4 S4 W4 m4 md4 k4 STK,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 m3 md3 k3 ->
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W4 m4 md4 k4 ->
  oc cx h i n now op nb fr len Sg T regs ly3 S3 W3 m3 ->
  0 <= STK -> STK + 640 <= LLVMF_STK ->
  d_kept (fun a => d_A cx - STK <= a < d_A cx) W3 m3 W4 m4 ->
  Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
  aregs_preserved regs regs' ->
  oc cx h i n now op nb fr len Sg T regs' ly4 S4 W4 m4.
Proof.
intros cx h i n now op nb fr len Sg T regs ly3 S3 W3 m3 md3 k3 regs' ly4 S4 W4 m4 md4 k4 STK Hc3 Hc4 HOC HS0 HS1 HK HPm HP.
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcanb & Hstk & Hawr).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W3 m3 md3 k3 Hc3)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
pose proof alloc_ceiling_val as Hac.
assert (Hlo : d_S cx - LLVMF_STK <= d_A cx - STK) by lia.
assert (HKA : forall a nn v, d_A cx <= a -> a + Z.of_nat nn <= d_S cx ->
  val_mem SEGS (rd W3 m3) a nn v -> val_mem SEGS (rd W4 m4) a nn v).
{ intros a nn v H1 H2. apply (oc_val_keep W3 W4 m3 m4 (d_A cx - STK) (d_A cx) a nn v HK); lia. }
assert (HKF : forall a l, d_FB cx <= a -> a + Z.of_nat (length l) <= d_FB cx + 4096 ->
  garr8 SEGS (rd W3 m3) a l -> garr8 SEGS (rd W4 m4) a l).
{ intros a l H1 H2. apply (oc_garr8_keep W3 W4 m3 m4 (d_A cx - STK) (d_A cx) a l HK); lia. }
unfold oc.
refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj _ (conj _ (conj _ (conj HSgl (conj _ (conj HSf
  (conj _ (conj _ (conj _ (conj _ (conj Hlen (conj Hnb (conj HTl (conj _ (conj HTok _)))))))))))))))))))).
- exact (d_rL_pres cx regs regs' HP HrL).
- destruct Hsp0 as (S1 & S2). split; apply HKA; try exact S1; try exact S2; cbn; lia.
- destruct Hfrm as (F1 & F2 & Fn & F3). split; [exact F1|]. split; [exact F2|]. split; [exact Fn|].
  destruct (Z.eq_dec fr 0) as [E0|E0].
  + rewrite (F2 E0). exact (garr8_nil SEGS _ _).
  + assert (Hin : In (fr, len) (ablocks B ly3 S3)).
    { destruct Hblocks as (Hperm & _). apply (Permutation_in _ (Permutation_sym Hperm)). unfold dxb.
      rewrite (proj2 (Z.eqb_neq fr 0) E0). left. reflexivity. }
    destruct (al_blocks _ _ LAWS ly3 S3 W3 m3 md3 fr len HAR Hin) as (_ & Hfr4 & Hfrc & _).
    assert (Hrq : len <= req_size len) by (unfold req_size; destruct (Z.eqb_spec len 0); lia).
    assert (HL : Z.of_nat (length (map (fun b : byte => bv_unsigned b) (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)))) <= len)
      by (rewrite length_map, length_firstn; lia).
    apply (oc_garr8_keep W3 W4 m3 m4 (d_A cx - STK) (d_A cx) fr _ HK); [lia | lia | left; lia | exact F3].
- apply HKF; [unfold d_obj, dobj_off; lia | rewrite length_map, HSgl; unfold d_obj, dobj_off; cbn; lia | exact HSg].
- apply HKA; [lia | cbn; lia | exact H248].
- apply HKA; [lia | cbn; lia | exact H336].
- apply HKA; [lia | cbn; lia | exact H368].
- apply HKA; [lia | cbn; lia | exact H280].
- apply HKF; [unfold d_obj, dobj_off; lia | rewrite length_map, HTl; unfold d_obj, dobj_off; cbn; lia | exact HT].
- assert (Hjr : d_jr B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W4 m4 md4 k4) by exact (conj (proj1 Hc4) (proj1 (proj2 Hc4))).
  assert (HKX : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx - STK <= a < d_A cx) -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a)
    by exact HK.
  apply (DBCK LAWS cx h n (dxb fr len) dsh_rec dsh_rec ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 (d_A cx - STK) (d_A cx) Hbody Hjr Hlo
    ltac:(lia) HK HPm).
  + apply (d_frame_keep cx h dsh_rec W3 W4 m3 m4 ly4 S4 md4 k4 Hframe Hc4). intros a Ha. apply HKX.
    * unfold shadow_addr, SHADOW_OFF in Ha. lia.
    * unfold shadow_addr, SHADOW_OFF in Ha. lia.
  + apply (d_shadow_keep cx dsh_rec W3 W4 m3 m4 Hshadow). intros kk Hkk. apply HKX; unfold shadow_addr, SHADOW_OFF, DFRAME_SH in *; lia.
Qed.

Ltac ne8 := let X := fresh in intros X; apply (f_equal bv_unsigned) in X; discriminate X.

Lemma ob_s12 : forall cx h i n now op nb fr len Sg kmax accmax W c,
  ob_c1 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c2 cx h i n now op nb fr len Sg kmax accmax).
Proof.
intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfz & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & T & HOC & HrO &
  Hra & Ha0 & Ha1 & Ha27).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcanb & Hstk & Hawr).
assert (Hc3 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hc3)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
pose proof alloc_ceiling_val as Hac. pose proof pa_base_lo as HBlo. pose proof pa_B_ok as HB.
pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
assert (FB8 : d_FB cx mod 8 = 0) by lia.
set (regs8 := regupd regs 8 (Z_to_bv 64 0)).
assert (G8 : forall r : bv 5, r <> 8%bv -> getr regs8 r = getr regs r).
{ intros r Hr. unfold regs8, getr. destruct (bv_eqb r 0); [reflexivity|]. exact (regupd_other regs 8 _ r Hr). }
assert (G88 : getr regs8 8%bv = Z_to_bv 64 0) by (unfold regs8, getr; rewrite regupd_same; destruct (bv_eqb _ _); reflexivity).
assert (Hsp8 : spZ regs8 = d_A cx) by (unfold spZ; rewrite G8 by ne8; exact Hsp).
assert (HPRE : afn_pre SEGS B TFIND_ENTRY_STK ly3 S3 W regs8 mem3 md3 []).
{ apply (afn_pre_at SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)]
    ly3 S3 W mem3 md3 k regs8 TFIND_ENTRY_STK (d_A cx - d_S cx) [] HJ).
  - rewrite Hsp8. lia.
  - lia.
  - lia.
  - unfold TFIND_ENTRY_STK, ESTACK. lia.
  - unfold TFIND_ENTRY_STK, ESTACK, LLVMF_STK. lia.
  - rewrite G8 by ne8. rewrite Hra. unfold w64. apply ret_ok_codeptr_v; [unfold OBS_OFF; lia | reflexivity].
  - unfold raZ. rewrite G8 by ne8. rewrite Hra. unfold w64. rewrite unsigned_lit_small by (unfold OBS_OFF; lia).
    unfold IMG_LO in HBlo. unfold OBS_OFF. lia.
  - rewrite G8 by ne8. exact Hgp.
  - rewrite G8 by ne8. exact Htp.
  - unfold s0Z. rewrite G88, unsigned_lit_small by lia. apply achain_low. lia. }
eapply SRr_mono.
{ apply (TFIND fq ly3 S3 W regs mem3 md3 [] (d_obj cx OT) (d_obj cx OS) T (s_mac Sg) HPRE Himg Ha0 Ha1).
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - exact HTl.
  - exact HT.
  - change (length (firstn 6 Sg) = 6%nat). rewrite length_firstn, HSgl. reflexivity.
  - change (garr8 SEGS (mrestrict (w_H W) mem3) (d_obj cx OS) (map bv_unsigned (firstn 6 Sg))). rewrite <- firstn_map.
    replace (d_obj cx OS) with (d_obj cx OS + Z.of_nat 0) by lia.
    exact (garr8_sub_x SEGS _ _ _ 0 6 HSg ltac:(rewrite length_map; lia)).
  - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg in HFia; unfold d_obj, dobj_off; lia |
      unfold d_obj, dobj_off; lia].
  - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg in HFia; unfold d_obj, dobj_off; lia |
      unfold d_obj, dobj_off; lia].
  - exact (ra_frame cx dsh_rec W mem3 2160 400 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia) (fun kk Hkk => dsh_rec_t kk ltac:(lia))).
  - exact (hull_frame cx dsh_rec W mem3 2160 400 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (ra_frame cx dsh_rec W mem3 2992 6 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia) (fun kk Hkk => dsh_rec_s kk ltac:(lia))).
  - exact (hull_frame cx dsh_rec W mem3 2992 6 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)).
  - left. rewrite Hsp. unfold d_obj, dobj_off, TFIND_ENTRY_STK, ESTACK, LLVMF_STK in *. lia.
  - unfold off_img in *. unfold d_obj, dobj_off. lia.
  - left. rewrite Hsp. unfold d_obj, dobj_off, TFIND_ENTRY_STK, ESTACK, LLVMF_STK in *. lia.
  - exact (proj1 HTok). }
cbv beta. intros W2 c2 _ HQ. unfold tfind_entry_post, apost_base in HQ.
destruct HQ as (fx' & ly4 & S4 & regs4 & mem4 & md4 & -> & _ & HCsr & HJ1 & HP & HPm & (r & Hr10 & Hfind) & Hkept).
assert (Hfz' : lib.Lib.FP.frm0 (@YK11.fp_csr fx')) by (destruct HCsr as [E|E]; [rewrite E; exact Hfz | exact E]).
rewrite Hsp in HJ1, Hkept.
assert (HJ2 : ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  [(DFRAME_CLASS, c_fpos cx)] ly4 S4 W2 mem4 md4 (k + 0)).
{ change [(DFRAME_CLASS, c_fpos cx)] with ([] ++ [(DFRAME_CLASS, c_fpos cx)]).
  eapply (ajournal_sub_tok SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | unfold TFIND_ENTRY_STK, ESTACK, LLVMF_STK; lia | lia |
    intros a (rg & [] & _)]. }
assert (Hc4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 mem4 md4 (k + 0)).
{ split; [exact Hbase|]. split; [exact HJ2|]. pose proof HJ1 as (_ & _ & _ & _ & _ & Hf1 & _). rewrite Hf1, Hfrs. reflexivity. }
assert (HOC4 : oc cx h i n now op nb fr len Sg T regs4 ly4 S4 W2 mem4)
  by exact (oc_call_keep cx h i n now op nb fr len Sg T regs ly3 S3 W mem3 md3 k regs4 ly4 S4 W2 mem4 md4 (k + 0) TFIND_ENTRY_STK
    Hc3 Hc4 HOC ltac:(unfold TFIND_ENTRY_STK, ESTACK; lia) ltac:(unfold TFIND_ENTRY_STK, ESTACK, LLVMF_STK; lia) Hkept HPm HP).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly4 S4 W2 mem4 md4 (k + 0) Hc4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HStk4 & _).
assert (HP408 : forall j, 0 <= j < 8 -> apresent (w_H W2) mem4 (d_A cx + 408 + j)) by (intros j Hj; apply HStk4; unfold LLVMF_STK; lia).
destruct (ex_val_mem8 (w_H W2) mem4 (d_A cx + 408) HP408) as (w & Hw & _).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
unfold DiscoEntObsCuts.ob_c2, d_at.
exists fx', ly4, S4, regs4, mem4, md4, (k + 0), acc.
split; [rewrite Hra; reflexivity|].
split; [exact Hfz'|]. split; [exact Hbase|]. split; [exact HJ2|]. split; [exact (proj2 (proj2 Hc4))|]. split; [lia|]. split; [lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
exists T, r, w. split; [exact HOC4|].
destruct HrO as (H22 & H26).
split; [transitivity (getr regs 26%bv); [exact (HP 26 ltac:(unfold acallee_saved; lia)) | exact H26]|].
split; [transitivity (getr regs 27%bv); [exact (HP 27 ltac:(unfold acallee_saved; lia)) | exact Ha27]|].
split; [exact Hr10|]. split; [exact Hfind|]. exact Hw.
Qed.

Lemma ob_pre8 : forall cx regs ly3 S3 (W : world SEGS) mem3 md3 k STK ret,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k -> d_rL B cx regs -> getr regs 1 = w64 (BASE + ret) ->
  0 <= ret < 2 ^ 40 -> ret mod 2 = 0 -> 0 <= STK -> STK + 640 <= LLVMF_STK ->
  afn_pre SEGS B STK ly3 S3 W (regupd regs 8 (Z_to_bv 64 0)) mem3 md3 [].
Proof.
intros cx regs ly3 S3 W mem3 md3 k STK ret Hc HrL Hra Hr0 Hr2 HS0 HS1.
pose proof Hc as (_ & HJ & _).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hc) as (HS16 & HSlo & HShi & _).
pose proof alloc_ceiling_val as Hac0.
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
pose proof pa_base_lo as HBlo. pose proof pa_B_ok as HB. pose proof alloc_ceiling_val as Hac.
pose proof HrL as (Hsp & Hgp & Htp & _).
set (regs8 := regupd regs 8 (Z_to_bv 64 0)).
assert (G8 : forall r : bv 5, r <> 8%bv -> getr regs8 r = getr regs r).
{ intros r Hr. unfold regs8, getr. destruct (bv_eqb r 0); [reflexivity|]. exact (regupd_other regs 8 _ r Hr). }
assert (G88 : getr regs8 8%bv = Z_to_bv 64 0) by (unfold regs8, getr; rewrite regupd_same; destruct (bv_eqb _ _); reflexivity).
assert (Hsp8 : spZ regs8 = d_A cx) by (unfold spZ; rewrite G8 by ne8; exact Hsp).
apply (afn_pre_at SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)]
  ly3 S3 W mem3 md3 k regs8 STK (d_A cx - d_S cx) [] HJ).
- rewrite Hsp8. lia.
- lia.
- lia.
- exact HS0.
- unfold LLVMF_STK in *. lia.
- rewrite G8 by ne8. rewrite Hra. unfold w64. apply ret_ok_codeptr_v; assumption.
- unfold raZ. rewrite G8 by ne8. rewrite Hra. unfold w64. rewrite unsigned_lit_small by lia. unfold IMG_LO in HBlo. lia.
- rewrite G8 by ne8. exact Hgp.
- rewrite G8 by ne8. exact Htp.
- unfold s0Z. rewrite G88, unsigned_lit_small by lia. apply achain_low. lia.
Qed.

Lemma ob_post : forall cx ly3 S3 (W : world SEGS) mem3 md3 k STK ly4 S4 W2 mem4 md4,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k -> 0 <= STK -> STK + 640 <= LLVMF_STK ->
  ajournal SEGS B STK (d_A cx) [] ly3 S3 W mem3 md3 [] ly4 S4 W2 mem4 md4 0 ->
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 mem4 md4 (k + 0).
Proof.
intros cx ly3 S3 W mem3 md3 k STK ly4 S4 W2 mem4 md4 Hc HS0 HS1 HJ1.
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hc) as (HS16 & HSlo & HShi & _).
pose proof alloc_ceiling_val as Hac0.
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
destruct Hc as (Hbase & HJ & Hfrs).
split; [exact Hbase|]. split.
- change [(DFRAME_CLASS, c_fpos cx)] with ([] ++ [(DFRAME_CLASS, c_fpos cx)]).
  eapply (ajournal_sub_tok SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | unfold LLVMF_STK in *; lia | lia |
    intros a (rg & [] & _)].
- pose proof HJ1 as (_ & _ & _ & _ & _ & Hf1 & _). rewrite Hf1, Hfrs. reflexivity.
Qed.

Lemma ob_dat : forall cx pc kmax accmax
  (P : bvmap 5 word -> alayout -> astate -> world SEGS -> (word -> option byte) -> Model -> Prop)
  (fq : YK11.FPState) ly4 S4 regs4 mem4 md4 k acc (W2 : world SEGS),
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 mem4 md4 k -> 0 <= k <= kmax -> acc <= accmax ->
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) -> P regs4 ly4 S4 W2 mem4 md4 ->
  DAT cx pc kmax accmax P W2 (cfg_at (fx := fq) SEGS (BASE + pc) regs4 mem4 md4).
Proof.
intros cx pc kmax accmax P fq ly4 S4 regs4 mem4 md4 k acc W2 (Hbase & HJ & Hfrs) Hk Hacc Hfz HP.
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
unfold d_at. exists fq, ly4, S4, regs4, mem4, md4, k, acc.
split; [reflexivity|]. split; [exact Hfz|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [lia|]. split; [lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|]. exact HP.
Qed.

Lemma obT_keep : forall cx now Sg T T' ai ow ret (W3 W4 : world SEGS) m3 m4 STK,
  d_kept (fun a => d_A cx - STK <= a < d_A cx) W3 m3 W4 m4 -> 640 <= d_S cx -> d_S cx <= 2 ^ 47 ->
  obT cx now Sg T T' ai ow ret W3 m3 -> obT cx now Sg T T' ai ow ret W4 m4.
Proof.
intros cx now Sg T T' ai ow ret W3 W4 m3 m4 STK HK H0 H1
  (L & Ok & F & Ow & (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11) & V12 & M).
destruct (d_A_range cx ltac:(unfold MFRAME; lia)) as (HAr & _). unfold MFRAME in HAr.
assert (KA : forall a nn v, 0 <= a -> a + Z.of_nat nn <= 448 ->
  val_mem SEGS (rd W3 m3) (d_A cx + a) nn v -> val_mem SEGS (rd W4 m4) (d_A cx + a) nn v).
{ intros a nn v Ha Hb Hv. apply (oc_val_keep W3 W4 m3 m4 (d_A cx - STK) (d_A cx) _ nn v HK); [lia | lia | lia | exact Hv]. }
unfold obT, ob_sp22.
refine (conj L (conj Ok (conj F (conj Ow (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
  (conj _ _)))))))))) (conj _ M)))))); apply KA; try assumption; cbn; lia.
Qed.

Lemma ob_tfind : forall cx (fq : YK11.FPState) ly3 S3 (W : world SEGS) regs mem3 md3 k h n xb ret (T Sg : list byte),
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k -> d_rL B cx regs -> getr regs 1 = w64 (BASE + ret) ->
  0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  getr regs 10 = w64 (d_obj cx OT) -> getr regs 11 = w64 (d_obj cx OS) ->
  length T = 400%nat -> garr8 SEGS (rd W mem3) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T) -> table_ok T ->
  length Sg = 24%nat -> garr8 SEGS (rd W mem3) (d_obj cx OS) (map (fun b : byte => bv_unsigned b) Sg) ->
  d_body B cx h n xb dsh_rec ly3 S3 W mem3 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_find_entry) regs mem3 md3)
    (tfind_entry_post B fq regs ly3 S3 W mem3 md3 T (s_mac Sg)).
Proof.
intros cx fq ly3 S3 W regs mem3 md3 k h n xb ret T Sg Hc3 HrL Hra Hr0 Hr2 Ha0 Ha1 HTl HT HTok HSgl HSg Hbody.
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcanb & Hstk & Hawr).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hc3)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
pose proof alloc_ceiling_val as Hac0.
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
pose proof alloc_ceiling_val as Hac. pose proof HrL as (Hsp & _).
assert (FB8 : d_FB cx mod 8 = 0) by lia.
apply (TFIND fq ly3 S3 W regs mem3 md3 [] (d_obj cx OT) (d_obj cx OS) T (s_mac Sg)
  (ob_pre8 cx regs ly3 S3 W mem3 md3 k TFIND_ENTRY_STK ret Hc3 HrL Hra Hr0 Hr2 ltac:(unfold TFIND_ENTRY_STK, ESTACK; lia)
    ltac:(unfold TFIND_ENTRY_STK, ESTACK, LLVMF_STK; lia)) Himg Ha0 Ha1).
- unfold d_obj, dobj_off. lia.
- unfold d_obj, dobj_off. lia.
- unfold d_obj, dobj_off. lia.
- unfold d_obj, dobj_off. lia.
- unfold d_obj, dobj_off. lia.
- exact HTl.
- exact HT.
- change (length (firstn 6 Sg) = 6%nat). rewrite length_firstn, HSgl. reflexivity.
- change (garr8 SEGS (mrestrict (w_H W) mem3) (d_obj cx OS) (map bv_unsigned (firstn 6 Sg))). rewrite <- firstn_map.
  replace (d_obj cx OS) with (d_obj cx OS + Z.of_nat 0) by lia.
  exact (garr8_sub_x SEGS _ _ _ 0 6 HSg ltac:(rewrite length_map; lia)).
- apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg in HFia; unfold d_obj, dobj_off; lia |
    unfold d_obj, dobj_off; lia].
- apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg in HFia; unfold d_obj, dobj_off; lia |
    unfold d_obj, dobj_off; lia].
- exact (ra_frame cx dsh_rec W mem3 2160 400 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia) (fun kk Hkk => dsh_rec_t kk ltac:(lia))).
- exact (hull_frame cx dsh_rec W mem3 2160 400 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)).
- exact (ra_frame cx dsh_rec W mem3 2992 6 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia) (fun kk Hkk => dsh_rec_s kk ltac:(lia))).
- exact (hull_frame cx dsh_rec W mem3 2992 6 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)).
- left. rewrite Hsp. unfold d_obj, dobj_off, TFIND_ENTRY_STK, ESTACK, LLVMF_STK in *. lia.
- unfold off_img in *. unfold d_obj, dobj_off. lia.
- left. rewrite Hsp. unfold d_obj, dobj_off, TFIND_ENTRY_STK, ESTACK, LLVMF_STK in *. lia.
- exact (proj1 HTok).
Qed.

Lemma ob_s56 : forall cx h i n now op nb fr len Sg kmax accmax W c,
  ob_c5 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c6 cx h i n now op nb fr len Sg kmax accmax).
Proof.
intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfz & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & T' & ai & ow & ret & HOC & H26 & HoT & HrT & Hra & Ha0 & H21 & H24 & H23 & H27).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcanb & Hstk & Hawr).
assert (Hc3 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hc3)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
pose proof alloc_ceiling_val as Hac0.
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
pose proof alloc_ceiling_val as Hac. pose proof HrL as (Hsp & _).
assert (FB8 : d_FB cx mod 8 = 0) by lia.
eapply SRr_mono.
{ apply (TCHK fq ly3 S3 W regs mem3 md3 [] (d_obj cx OT) T'
    (ob_pre8 cx regs ly3 S3 W mem3 md3 k TCHECK_TABLE_STK 0x181c Hc3 HrL Hra ltac:(lia) ltac:(reflexivity)
      ltac:(unfold TCHECK_TABLE_STK, ESTACK; lia) ltac:(unfold TCHECK_TABLE_STK, ESTACK, LLVMF_STK; lia)) Himg Ha0).
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - exact HTl.
  - exact HT.
  - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg in HFia; unfold d_obj, dobj_off; lia |
      unfold d_obj, dobj_off; lia].
  - exact (ra_frame cx dsh_rec W mem3 2160 400 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia) (fun kk Hkk => dsh_rec_t kk ltac:(lia))).
  - exact (hull_frame cx dsh_rec W mem3 2160 400 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)).
  - left. rewrite Hsp. unfold d_obj, dobj_off, TCHECK_TABLE_STK, ESTACK, LLVMF_STK in *. lia.
  - unfold off_img in *. unfold d_obj, dobj_off. lia.
  - exact (proj1 HTok).
  - exact (proj1 (proj2 HTok)).
  - exact (proj1 (proj2 (proj2 HTok))). }
cbv beta. intros W2 c2 _ HQ. unfold tcheck_table_post, apost_base in HQ.
destruct HQ as (fx' & ly4 & S4 & regs4 & mem4 & md4 & -> & _ & HCsr & HJ1 & HP & HPm & Hkept).
assert (Hfz' : lib.Lib.FP.frm0 (@YK11.fp_csr fx')) by (destruct HCsr as [E|E]; [rewrite E; exact Hfz | exact E]).
rewrite Hsp in HJ1, Hkept.
pose proof (ob_post cx ly3 S3 W mem3 md3 k TCHECK_TABLE_STK ly4 S4 W2 mem4 md4 Hc3
  ltac:(unfold TCHECK_TABLE_STK, ESTACK; lia) ltac:(unfold TCHECK_TABLE_STK, ESTACK, LLVMF_STK; lia) HJ1) as Hc4.
pose proof (oc_call_keep cx h i n now op nb fr len Sg T' regs ly3 S3 W mem3 md3 k regs4 ly4 S4 W2 mem4 md4 (k + 0)
  TCHECK_TABLE_STK Hc3 Hc4 HOC ltac:(unfold TCHECK_TABLE_STK, ESTACK; lia)
  ltac:(unfold TCHECK_TABLE_STK, ESTACK, LLVMF_STK; lia) Hkept HPm HP) as HOC4.
rewrite Hra.
apply (ob_dat cx 0x181c kmax accmax _ fx' ly4 S4 regs4 mem4 md4 (k + 0) acc W2 Hc4 ltac:(lia) Hacc Hfz').
exists T, T', ai, ow, ret. split; [exact HOC4|].
split; [transitivity (getr regs 26%bv); [exact (HP 26 ltac:(unfold acallee_saved; lia)) | exact H26]|].
split; [exact (obT_keep cx now Sg T T' ai ow ret W W2 mem3 mem4 TCHECK_TABLE_STK Hkept ltac:(unfold LLVMF_STK in *; lia)
  ltac:(lia) HoT)|].
split; [destruct HrT as (R19 & R22); split;
  [transitivity (getr regs 19%bv); [exact (HP 19 ltac:(unfold acallee_saved; lia)) | exact R19]
  |transitivity (getr regs 22%bv); [exact (HP 22 ltac:(unfold acallee_saved; lia)) | exact R22]]|].
split; [transitivity (getr regs 21%bv); [exact (HP 21 ltac:(unfold acallee_saved; lia)) | exact H21]|].
split; [transitivity (getr regs 24%bv); [exact (HP 24 ltac:(unfold acallee_saved; lia)) | exact H24]|].
split; [transitivity (getr regs 23%bv); [exact (HP 23 ltac:(unfold acallee_saved; lia)) | exact H23]|].
transitivity (getr regs 27%bv); [exact (HP 27 ltac:(unfold acallee_saved; lia)) | exact H27].
Qed.

Lemma ob_s78 : forall cx h i n now op nb fr len Sg kmax accmax W c,
  ob_c7 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c8 cx h i n now op nb fr len Sg kmax accmax).
Proof.
intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfz & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & T' & ai & ow & ret & HOC & H26 & HoT & HrT & HrX & Hai & Hrole & Hra & Ha0 & Ha1).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
assert (Hc3 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hc3) as (HS16 & HSlo & HShi & _).
pose proof alloc_ceiling_val as Hac0.
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
pose proof HrL as (Hsp & _).
eapply SRr_mono.
{ exact (ob_tfind cx fq ly3 S3 W regs mem3 md3 k h n (dxb fr len) 0x1874 T' Sg Hc3 HrL Hra ltac:(lia) ltac:(reflexivity)
    Ha0 Ha1 HTl HT HTok HSgl HSg Hbody). }
cbv beta. intros W2 c2 _ HQ. unfold tfind_entry_post, apost_base in HQ.
destruct HQ as (fx' & ly4 & S4 & regs4 & mem4 & md4 & -> & _ & HCsr & HJ1 & HP & HPm & (r & Hr10 & Hfind) & Hkept).
assert (Hfz' : lib.Lib.FP.frm0 (@YK11.fp_csr fx')) by (destruct HCsr as [E|E]; [rewrite E; exact Hfz | exact E]).
rewrite Hsp in HJ1, Hkept.
pose proof (ob_post cx ly3 S3 W mem3 md3 k TFIND_ENTRY_STK ly4 S4 W2 mem4 md4 Hc3
  ltac:(unfold TFIND_ENTRY_STK, ESTACK; lia) ltac:(unfold TFIND_ENTRY_STK, ESTACK, LLVMF_STK; lia) HJ1) as Hc4.
pose proof (oc_call_keep cx h i n now op nb fr len Sg T' regs ly3 S3 W mem3 md3 k regs4 ly4 S4 W2 mem4 md4 (k + 0)
  TFIND_ENTRY_STK Hc3 Hc4 HOC ltac:(unfold TFIND_ENTRY_STK, ESTACK; lia)
  ltac:(unfold TFIND_ENTRY_STK, ESTACK, LLVMF_STK; lia) Hkept HPm HP) as HOC4.
rewrite Hra.
apply (ob_dat cx 0x1874 kmax accmax _ fx' ly4 S4 regs4 mem4 md4 (k + 0) acc W2 Hc4 ltac:(lia) Hacc Hfz').
exists T, T', ai, ow, ret, r. split; [exact HOC4|].
split; [transitivity (getr regs 26%bv); [exact (HP 26 ltac:(unfold acallee_saved; lia)) | exact H26]|].
split; [exact (obT_keep cx now Sg T T' ai ow ret W W2 mem3 mem4 TFIND_ENTRY_STK Hkept ltac:(unfold LLVMF_STK in *; lia)
  ltac:(lia) HoT)|].
split; [destruct HrT as (R19 & R22); split;
  [transitivity (getr regs 19%bv); [exact (HP 19 ltac:(unfold acallee_saved; lia)) | exact R19]
  |transitivity (getr regs 22%bv); [exact (HP 22 ltac:(unfold acallee_saved; lia)) | exact R22]]|].
split; [destruct HrX as (X21 & X23 & X24 & X27); split;
  [transitivity (getr regs 21%bv); [exact (HP 21 ltac:(unfold acallee_saved; lia)) | exact X21]|]; split;
  [transitivity (getr regs 23%bv); [exact (HP 23 ltac:(unfold acallee_saved; lia)) | exact X23]|]; split;
  [transitivity (getr regs 24%bv); [exact (HP 24 ltac:(unfold acallee_saved; lia)) | exact X24]
  |transitivity (getr regs 27%bv); [exact (HP 27 ltac:(unfold acallee_saved; lia)) | exact X27]]|].
split; [exact Hai|]. split; [exact Hrole|]. split; [exact Hr10|]. exact Hfind.
Qed.

Lemma optZ_dec : forall x y : option Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Qed.
Lemma u_at_fb : forall (S : list byte) (k : nat), (k < length S)%nat -> u_at S (Z.of_nat k) 1 = CtrlParsed.fb S k.
Proof.
intros S k. unfold u_at, sub, CtrlParsed.fb. rewrite Nat2Z.id. revert S. induction k as [|k IH]; intros [|b S] Hk; cbn [length] in Hk; try lia.
- cbn [skipn firstn nth bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
- cbn [skipn nth]. apply IH. lia.
Qed.
Lemma sight_S12 : forall S : list byte, disco_classify_c.sighting_ok S -> sighting_S1 S /\ sighting_S2 S.
Proof.
intros S (HL & HR & HD).
assert (Hb : 0 <= CtrlParsed.fu S 8 4 < 2 ^ 32).
{ unfold CtrlParsed.fu, CtrlParsed.fld. pose proof (bytes_le_to_Z_nonneg (firstn 4 (skipn 8 S))).
  pose proof (bytes_le_to_Z_bound (firstn 4 (skipn 8 S))) as Hu. rewrite length_firstn, length_skipn, HL in Hu. cbn in Hu. lia. }
assert (SW : bv_swrap 32 (CtrlParsed.fu S 8 4) = CtrlParsed.s32 (CtrlParsed.fu S 8 4)).
{ unfold CtrlParsed.s32. change (bv_swrap 32 (CtrlParsed.fu S 8 4)) with ((CtrlParsed.fu S 8 4 + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31).
  destruct (Z.ltb_spec (CtrlParsed.fu S 8 4) (2 ^ 31)); lia. }
split.
- unfold sighting_S1, s_role, s32_at. change (u_at S 8 4) with (CtrlParsed.fu S 8 4). rewrite SW. lia.
- unfold sighting_S2, s_hd, s_din, s_dout.
  change 12 with (Z.of_nat 12). change 13 with (Z.of_nat 13). change 14 with (Z.of_nat 14).
  rewrite !u_at_fb by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *. lia.
Qed.

Lemma tobs_frame : forall cx ly3 S3 W3 m3 md3 k3 W4 m4,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 m3 md3 k3 ->
  treac_disco_table_observe_kept B ly3 S3 W3 m3 W4 m4 (d_A cx) (d_obj cx OT) ->
  (forall a, d_A cx <= a < d_S cx -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) /\
  (forall a, d_FB cx <= a < d_FB cx + 4096 -> ~ (d_obj cx OT <= a < d_obj cx OT + 400) ->
     aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) /\
  (forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) /\
  (forall b m j, In (b, m) (ablocks B ly3 S3) -> 0 <= j < req_size m ->
     aview SEGS (w_H W4) m4 (b + j) = aview SEGS (w_H W3) m3 (b + j)).
Proof.
intros cx ly3 S3 W3 m3 md3 k3 W4 m4 Hc3 (K1 & K2 & K3 & K4 & K5 & K6).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W3 m3 md3 k3 Hc3)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
pose proof alloc_ceiling_val as Hac.
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
split; [|split; [|split]].
- intros a Ha. apply K1; unfold d_obj, dobj_off, REAC_DISCO_TABLE_OBSERVE_STK, ESTACK, LLVMF_STK in *; lia.
- intros a Ha Ht. apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin); [|exact Ht].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
- intros a Ha. apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin).
  + right. unfold in_zr. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
  + unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFia. unfold d_obj, dobj_off, shadow_addr, SHADOW_OFF in *. lia.
- intros b m j Hin Hj. apply (K2 b m j Hin Hj).
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 m3 md3 b m DFRAME_CLASS (c_fpos cx) HAR Hin Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efa in Hd. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hd.
  unfold d_obj, dobj_off. lia.
Qed.

Lemma oc_tobs_keep : forall cx h i n now op nb fr len Sg T T' regs ly3 S3 W3 m3 md3 k3 regs' ly4 S4 W4 m4 md4 k4,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 m3 md3 k3 ->
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W4 m4 md4 k4 ->
  oc cx h i n now op nb fr len Sg T regs ly3 S3 W3 m3 ->
  treac_disco_table_observe_kept B ly3 S3 W3 m3 W4 m4 (d_A cx) (d_obj cx OT) ->
  Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) -> aregs_preserved regs regs' ->
  length T' = 400%nat -> garr8 SEGS (rd W4 m4) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T') -> table_ok T' ->
  garr8 SEGS (rd W4 m4) (d_obj cx OS) (map (fun b : byte => bv_unsigned b) Sg) ->
  oc cx h i n now op nb fr len Sg T' regs' ly4 S4 W4 m4.
Proof.
intros cx h i n now op nb fr len Sg T T' regs ly3 S3 W3 m3 md3 k3 regs' ly4 S4 W4 m4 md4 k4 Hc3 Hc4 HOC HKT HPm HP HTl' HT' HTok' HSg'.
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcanb & Hstk & Hawr).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W3 m3 md3 k3 Hc3)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
pose proof alloc_ceiling_val as Hac.
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
destruct (tobs_frame cx ly3 S3 W3 m3 md3 k3 W4 m4 Hc3 HKT) as (KA & KFr & KSh & KB).
destruct HKT as (K1 & K2 & K3 & K4 & K5 & K6).
assert (VA : forall a nn v, d_A cx <= a -> a + Z.of_nat nn <= d_S cx ->
  val_mem SEGS (rd W3 m3) a nn v -> val_mem SEGS (rd W4 m4) a nn v).
{ intros a nn v H1 H2 Hv. apply (val_mem_keep W3 W4 m3 m4 a nn v); [|exact Hv]. intros j Hj. apply KA. lia. }
unfold oc.
refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj _ (conj _ (conj _ (conj HSgl (conj HSg' (conj HSf
  (conj _ (conj _ (conj _ (conj _ (conj Hlen (conj Hnb (conj HTl' (conj HT' (conj HTok' _)))))))))))))))))))).
- exact (d_rL_pres cx regs regs' HP HrL).
- destruct Hsp0 as (S1 & S2). split; apply VA; try exact S1; try exact S2; cbn; lia.
- destruct Hfrm as (F1 & F2 & Fn & F3). split; [exact F1|]. split; [exact F2|]. split; [exact Fn|].
  destruct (Z.eq_dec fr 0) as [E0|E0].
  + rewrite (F2 E0). exact (garr8_nil SEGS _ _).
  + assert (Hin : In (fr, len) (ablocks B ly3 S3)).
    { destruct Hblocks as (Hperm & _). apply (Permutation_in _ (Permutation_sym Hperm)). unfold dxb.
      rewrite (proj2 (Z.eqb_neq fr 0) E0). left. reflexivity. }
    assert (Hrq : len <= req_size len) by (unfold req_size; destruct (Z.eqb_spec len 0); lia).
    apply (garr8_keep W3 W4 m3 m4 fr _); [|exact F3]. intros j Hj.
    rewrite length_map, length_firstn in Hj. apply (KB fr len (Z.of_nat j) Hin). lia.
- apply VA; [lia | cbn; lia | exact H248].
- apply VA; [lia | cbn; lia | exact H336].
- apply VA; [lia | cbn; lia | exact H368].
- apply VA; [lia | cbn; lia | exact H280].
- assert (Hjr : d_jr B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W4 m4 md4 k4) by exact (conj (proj1 Hc4) (proj1 (proj2 Hc4))).
  assert (Hfr4 : d_frame cx h dsh_rec W4 m4).
  { apply (d_frame_keep cx h dsh_rec W3 W4 m3 m4 ly4 S4 md4 k4 Hframe Hc4).
    intros a [Ha|[Ha|[Ha|Ha]]]; [apply KA; exact Ha | apply KFr | apply KFr | apply KSh; exact Ha];
    unfold d_obj, dobj_off; lia. }
  assert (Hsh4 : d_shadow cx dsh_rec W4 m4).
  { apply (d_shadow_keep cx dsh_rec W3 W4 m3 m4 Hshadow). intros kk Hkk. apply KSh. unfold DFRAME_SH in Hkk. lia. }
  apply (DBTOBS LAWS cx h n (dxb fr len) dsh_rec dsh_rec ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4
    (d_A cx - REAC_DISCO_TABLE_OBSERVE_STK) (d_A cx) [OT] (fun a => aview SEGS (w_H W4) m4 a <> aview SEGS (w_H W3) m3 a)
    Hbody Hjr ltac:(unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK, LLVMF_STK; lia) ltac:(lia)).
  + intros a HR.
    assert (Hw : (d_A cx - REAC_DISCO_TABLE_OBSERVE_STK <= a < d_A cx) \/ ~ (d_A cx - REAC_DISCO_TABLE_OBSERVE_STK <= a < d_A cx))
      by lia.
    destruct Hw as [Hw|Hw]; [left; exact Hw|].
    assert (Ht : (d_obj cx OT <= a < d_obj cx OT + 400) \/ ~ (d_obj cx OT <= a < d_obj cx OT + 400)) by lia.
    destruct Ht as [Ht|Ht]; [right; left; apply Exists_cons_hd; unfold d_objr, dobj_size; exact Ht|].
    right; right. intros Hrd. apply HR.
    destruct Hrd as [Ho|[Ho|[Ho|[Ho|[Hh|[Hin|[Hro|Hcan]]]]]]].
    8: { destruct DCAN as (AIL & Ecan). rewrite <- Ecan in Hcan.
      assert (Ho : Exists (YG0n.in_zr a) (ak_owned tfib_K)).
      { apply (ail_owned_core _ _ _ AIL). unfold aenv_core. right; right; right. exact Hcan. }
      assert (Hsp : fp_spares [] a) by (apply fp_spares_off; exact (ail_env_static _ _ _ AIL a Ho)).
      assert (Hae : aenv_addr tfib_K a) by (unfold aenv_addr; left; exact Ho).
      pose proof (aenv_kept SEGS B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a (proj1 (proj2 Hc4)) Hae Hsp) as E4.
      pose proof (aenv_kept SEGS B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a (proj1 (proj2 Hc3)) Hae Hsp) as E3.
      unfold aview. rewrite E4, E3. reflexivity. }
    * exfalso. apply Ht. unfold d_objr, dobj_size in Ho. exact Ho.
    * apply KFr; unfold d_objr, d_obj, dobj_off, dobj_size in *; lia.
    * apply KFr; unfold d_objr, d_obj, dobj_off, dobj_size in *; lia.
    * apply KFr; unfold d_objr, d_obj, dobj_off, dobj_size in *; lia.
    * assert (HinH : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
      { destruct Hblocks as (Hperm & _). apply (Permutation_in _ (Permutation_sym Hperm)).
        apply in_or_app. right. left. reflexivity. }
      replace a with (h + (a - h)) by lia. apply (KB h HUNT_SIZE (a - h) HinH). unfold req_size, HUNT_SIZE in *. cbn. lia.
    * destruct Hin as (Hn0 & Hin).
      pose proof (proj1 Hc3) as ((_ & _ & _ & _ & Hpn & _) & _).
      destruct Hpn as [(E & _)|(_ & HinP)]; [lia|].
      assert (HinP3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)).
      { destruct Hblocks as (Hperm & _). apply (Permutation_in _ (Permutation_sym Hperm)).
        apply in_or_app. right. right. exact HinP. }
      replace a with (c_p cx + (a - c_p cx)) by lia. apply (KB (c_p cx) (c_n cx) (a - c_p cx) HinP3).
      unfold req_size. destruct (Z.eqb_spec (c_n cx) 0); lia.
    * destruct Hro as (Hrop & Hno & Hne). exact (K3 a (in_roP_img a Hrop) Hno Hne).
  + intros a _ HnR. destruct (optZ_dec (aview SEGS (w_H W4) m4 a) (aview SEGS (w_H W3) m3 a)) as [E|E];
      [exact E | exfalso; exact (HnR E)].
  + constructor; [|constructor]. exists T'. split; [exact HTl'|]. split; [exact HT' | exact HTok'].
  + exact HPm.
  + exact Hfr4.
  + exact Hsh4.
Qed.

Lemma ob_s34 : forall cx h i n now op nb fr len Sg kmax accmax W c,
  ob_c3 cx h i n now op nb fr len Sg kmax accmax W c -> SRr SEGS W c (ob_c4 cx h i n now op nb fr len Sg kmax accmax).
Proof.
intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfz & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & ai & ow & HOC & H26 & Hfind & How & Hsp22 & H408 & Hra & Ha0 & Ha1 & Ha2 & Ha3 & H19 & H24 & H23 & H22 & H27).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcanb & Hstk & Hawr).
assert (Hc3 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hc3)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
pose proof alloc_ceiling_val as Hac. pose proof pa_base_lo as HBlo. pose proof pa_B_ok as HB.
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
pose proof HrL as (Hsp & Hgp & Htp & _).
assert (FB8 : d_FB cx mod 8 = 0) by lia.
destruct HSf as (Hs50 & Hs1 & Hs2 & Hs3 & Hs4 & HSok & Hs5).
destruct (sight_S12 Sg HSok) as (HS1 & HS2).
eapply SRr_mono.
{ apply (TTOBS fq LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)]
    ly3 S3 W mem3 md3 k regs (d_obj cx OT) (d_obj cx OS) ow now T Sg HJ Himg).
  - rewrite Hra. unfold w64. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Hra. unfold w64. rewrite unsigned_lit_small by lia. unfold IMG_LO in HBlo. lia.
  - exact Hgp.
  - exact Htp.
  - exact Ha0.
  - exact Ha1.
  - exact Ha2.
  - exact Ha3.
  - lia.
  - exact Hnow.
  - rewrite Hsp. lia.
  - rewrite Hsp. unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK, LLVMF_STK. lia.
  - rewrite Hsp. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg in HFia; unfold d_obj, dobj_off; lia |
      unfold d_obj, dobj_off; lia].
  - right. rewrite Hsp. unfold d_obj, dobj_off, REAC_DISCO_TABLE_OBSERVE_STK, ESTACK, LLVMF_STK in *. lia.
  - intros a Ha. apply Hawr. unfold d_obj, dobj_off in Ha. unfold DFRAME_SIZE. lia.
  - exact (ra_frame cx dsh_rec W mem3 2160 400 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia) (fun kk Hkk => dsh_rec_t kk ltac:(lia))).
  - exact (hull_frame cx dsh_rec W mem3 2160 400 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact HT.
  - exact HTl.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg in HFia; unfold d_obj, dobj_off; lia |
      unfold d_obj, dobj_off; lia].
  - unfold d_obj, dobj_off. lia.
  - intros a Ha. apply (proj2 (Hawr a ltac:(unfold d_obj, dobj_off in Ha; unfold DFRAME_SIZE; lia))).
  - exact (ra_frame cx dsh_rec W mem3 2992 24 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia) (fun kk Hkk => dsh_rec_s kk ltac:(lia))).
  - right. rewrite Hsp. unfold d_obj, dobj_off, REAC_DISCO_TABLE_OBSERVE_STK, ESTACK, LLVMF_STK in *. lia.
  - exact (hull_frame cx dsh_rec W mem3 2992 24 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact HSg.
  - exact HSgl.
  - left. exists DFRAME_CLASS, (c_fpos cx). split; [exact Hfin|]. rewrite Efa.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. unfold d_obj, dobj_off. lia.
  - right. unfold d_obj, dobj_off. lia.
  - exact (proj1 HTok).
  - exact (proj1 (proj2 HTok)).
  - exact (proj1 (proj2 (proj2 HTok))).
  - exact HS1.
  - exact HS2. }
cbv beta. intros W2 c2 _ HQ. unfold treac_disco_table_observe_post in HQ.
destruct HQ as (ly4 & S4 & regs4 & mem4 & md4 & T' & ret & -> & HJ2 & HP & Hret & Hfr4 & HPm & HKT & HT' & HTl' & HSg' &
  Hmodel & T1' & T2' & T3' & T4').
rewrite Hsp in HKT.
assert (Hc4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 mem4 md4 k).
{ split; [exact Hbase|]. split; [exact HJ2|]. rewrite Hfr4. exact Hfrs. }
assert (HTok' : table_ok T') by exact (conj T1' (conj T2' (conj T3' (T4' (proj2 (proj2 (proj2 HTok))))))).
pose proof (oc_tobs_keep cx h i n now op nb fr len Sg T T' regs ly3 S3 W mem3 md3 k regs4 ly4 S4 W2 mem4 md4 k
  Hc3 Hc4 HOC HKT HPm HP HTl' HT' HTok' HSg') as HOC4.
destruct (tobs_frame cx ly3 S3 W mem3 md3 k W2 mem4 Hc3 HKT) as (KA & _ & _ & _).
assert (VA : forall a nn v, d_A cx <= a -> a + Z.of_nat nn <= d_S cx ->
  val_mem SEGS (rd W mem3) a nn v -> val_mem SEGS (rd W2 mem4) a nn v).
{ intros a nn v H1 H2 Hv. apply (val_mem_keep W W2 mem3 mem4 a nn v); [|exact Hv]. intros j Hj. apply KA. lia. }
assert (HoT : obT cx now Sg T T' ai ow ret W2 mem4).
{ destruct Hsp22 as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11).
  unfold obT, ob_sp22.
  refine (conj HTl (conj HTok (conj Hfind (conj How (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ _)))))))))) (conj _ Hmodel)))))); apply VA; try assumption; cbn; lia. }
rewrite Hra.
apply (ob_dat cx 0x1804 kmax accmax _ fq ly4 S4 regs4 mem4 md4 k acc W2 Hc4 ltac:(lia) Hacc Hfz).
exists T, T', ai, ow, ret. split; [exact HOC4|].
split; [transitivity (getr regs 26%bv); [exact (HP 26 ltac:(unfold acallee_saved; lia)) | exact H26]|].
split; [exact HoT|].
split; [split;
  [transitivity (getr regs 19%bv); [exact (HP 19 ltac:(unfold acallee_saved; lia)) | exact H19]
  |transitivity (getr regs 22%bv); [exact (HP 22 ltac:(unfold acallee_saved; lia)) | exact H22]]|].
split; [exact Hret|].
split; [transitivity (getr regs 24%bv); [exact (HP 24 ltac:(unfold acallee_saved; lia)) | exact H24]|].
split; [transitivity (getr regs 23%bv); [exact (HP 23 ltac:(unfold acallee_saved; lia)) | exact H23]|].
transitivity (getr regs 27%bv); [exact (HP 27 ltac:(unfold acallee_saved; lia)) | exact H27].
Qed.

Lemma ob_in0 : forall cx h i n now op nb fr len Sg W c,
  obs_in B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len Sg W c ->
  ob_c0 cx h i n now op nb fr len Sg (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) W c.
Proof.
intros cx h i n now op nb fr len Sg W c H.
unfold obs_in, d_arm_at_pf, d_at in H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & Hfz & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & HrL & HrO & HX & Hsp0 & Hbody).
destruct HX as (Hop & Hop2 & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 & Hlen & Hnb).
pose proof Hbody as (T & G & Lk & H & _ & _ & Hobjs & _).
destruct Hobjs as (HTl & HT & HTok & _).
unfold DiscoEntObsCuts.ob_c0, d_at.
exists fq, ly3, S3, regs, mem3, md3, k, acc.
split; [exact Hc|]. split; [exact Hfz|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
exists T. split; [|exact HrO].
exact (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj HrL (conj Hsp0 (conj Hfrm (conj HSgl (conj HSg (conj HSf
  (conj H248 (conj H336 (conj H368 (conj H280 (conj Hlen (conj Hnb (conj HTl (conj HT (conj HTok Hbody)))))))))))))))))))).
Qed.

Theorem obs_of_parts : ob_seg23 B MT XM_LIB RLO RHI tfib_K -> ob_seg45 B MT XM_LIB RLO RHI tfib_K ->
  ob_seg67 B MT XM_LIB RLO RHI tfib_K -> ob_seg89 B MT XM_LIB RLO RHI tfib_K ->
  ob_seg9r B MT XM_LIB RLO RHI tfib_K -> ob_seg10r B MT XM_LIB RLO RHI tfib_K ->
  obs_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros S23 S45 S67 S89 S9r S10r cx h i n now op nb fr len Sg W c H.
set (km := EV_HEAD i + 1). set (am := ACC_HEAD MT i + mo_malloc MT REC_MAX).
eapply SRr_bind; [exact (ob_s01 cx h i n now op nb fr len Sg km am W c (ob_in0 cx h i n now op nb fr len Sg W c H))|].
intros W1 c1 _ H1.
eapply SRr_bind; [exact (ob_s12 cx h i n now op nb fr len Sg km am W1 c1 H1)|]. intros W2 c2 _ H2.
eapply SRr_bind; [exact (S23 cx h i n now op nb fr len Sg km am W2 c2 H2)|]. intros W3 c3 _ H3.
eapply SRr_bind; [exact (ob_s34 cx h i n now op nb fr len Sg km am W3 c3 H3)|]. intros W4 c4 _ H4.
eapply SRr_bind; [exact (S45 cx h i n now op nb fr len Sg km am W4 c4 H4)|]. intros W5 c5 _ H5.
eapply SRr_bind; [exact (ob_s56 cx h i n now op nb fr len Sg km am W5 c5 H5)|]. intros W6 c6 _ H6.
eapply SRr_bind; [exact (S67 cx h i n now op nb fr len Sg km am W6 c6 H6)|]. intros W7 c7 _ [H7|[H9|H10]].
- eapply SRr_bind; [exact (ob_s78 cx h i n now op nb fr len Sg km am W7 c7 H7)|]. intros W8 c8 _ H8.
  eapply SRr_bind; [exact (S89 cx h i n now op nb fr len Sg km am W8 c8 H8)|]. intros W9 c9 _ H9.
  exact (S9r cx h i n now op nb fr len Sg W9 c9 H9).
- exact (S9r cx h i n now op nb fr len Sg W7 c7 H9).
- exact (S10r cx h i n now op nb fr len Sg W7 c7 H10).
Qed.

Theorem ob_seg9r_of : ob_seg9a B MT XM_LIB RLO RHI tfib_K -> ob_seg9b B MT XM_LIB RLO RHI tfib_K ->
  ob_seg9r B MT XM_LIB RLO RHI tfib_K.
Proof.
intros S9a S9b cx h i n now op nb fr len Sg W c H.
eapply SRr_bind; [exact (S9a cx h i n now op nb fr len Sg (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) W c H)|].
intros W1 c1 _ H1. exact (S9b cx h i n now op nb fr len Sg W1 c1 H1).
Qed.

End h.
End f.
End d.
