(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 249 of its 280 lines of code are new or changed and 38 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop YI0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import SbDec SbDecLib SbDecCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
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
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM0 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 0.
Hypothesis TLF : PALibF B.
Hypothesis SMP : stack_malloc_progressP B.
Lemma sbd1_frame_of_region : forall E m spe cs (regs : bvmap 5 word),
  region_ok SEGS E m (YP09.mkRegion (Some 2%nat) (-112) 0 (-112) 0 cs) -> bv_unsigned (ew E 2) = spe ->
  (forall j r, nth_error sbd_saved_regs j = Some r ->
     In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
  (forall r, 0 <= r < 32 -> ew E (Z.to_nat r) = getr regs (Z_to_bv 5 r)) ->
  forall j r, nth_error sbd_saved_regs j = Some r ->
    val_mem SEGS m (spe - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
Proof.
intros E m spe cs regs HR Hsp Hin Hew j r Hj.
assert (Hr : 0 <= r < 32).
{ apply nth_error_In in Hj. unfold sbd_saved_regs in Hj. cbn [In] in Hj. lia. }
replace (spe - 8 - 8 * Z.of_nat j) with (spe + (-8 - 8 * Z.of_nat j)) by lia.
apply (slot_of_region E m spe cs (-112) 0 (-112) 0 (-8 - 8 * Z.of_nat j) (SOff (Z.to_nat r) 0)
  (bv_unsigned (getr regs (Z_to_bv 5 r))) HR Hsp (Hin j r Hj)).
- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite (Hew r Hr). symmetry. apply Z_to_bv_bv_unsigned.
- apply bv_unsigned_in_range.
Qed.
Lemma sbd1_rec_of_region : forall E m wlo whi A p cap n over,
  region_ok SEGS E m (YP09.mkRegion (Some 10%nat) 0 28 wlo whi
    [YP09.mkChunk 0 (CVal 8 (SOff 34 0)); YP09.mkChunk 8 (CVal 8 (SOff 35 0));
     YP09.mkChunk 16 (CVal 8 (SOff 36 0)); YP09.mkChunk 24 (CVal 4 (SOff 37 0))]) ->
  bv_unsigned (ew E 10) = A ->
  ew E 34 = Z_to_bv 64 p -> ew E 35 = Z_to_bv 64 cap -> ew E 36 = Z_to_bv 64 n -> ew E 37 = Z_to_bv 64 over ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= over < 2 ^ 32 ->
  sbd_rec m A p cap n over.
Proof.
intros E m wlo whi A p cap n over (_ & _ & _ & HC) HA E34 E35 E36 E37 Rp Rc Rn Ro.
cbn [YP09.r_base YP09.r_chunks base_val] in HC. rewrite HA in HC.
pose proof (Forall_inv HC) as C1. apply Forall_inv_tail in HC.
pose proof (Forall_inv HC) as C2. apply Forall_inv_tail in HC.
pose proof (Forall_inv HC) as C3. apply Forall_inv_tail in HC.
pose proof (Forall_inv HC) as C4. clear HC.
split; [|split; [|split]].
- rewrite <- (Z.add_0_r A). apply (val_of_chunk_ok SEGS E m A 0 8 (SOff 34 0) p C1);
  [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia].
- apply (val_of_chunk_ok SEGS E m A 8 8 (SOff 35 0) cap C2);
  [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia].
- apply (val_of_chunk_ok SEGS E m A 16 8 (SOff 36 0) n C3);
  [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia].
- apply (val_of_chunk_ok SEGS E m A 24 4 (SOff 37 0) over C4);
  [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia].
Qed.
Lemma sbd1_val_mem_mbyte : forall (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte SEGS m' x = mbyte SEGS m x) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v H Hv kk Hk. rewrite H by lia. exact (Hv kk Hk). Qed.
Theorem sbd_seg1 : sbd_seg1_stmt B.
Proof.
intros [fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch A v md p cap n over] HX.
unfold sbd_cx, sbm_room, sbm_acc in HX. cbn [si_fq si_STK si_sp0 si_FP si_ly si_S si_W0 si_mem0 si_md0
  si_own si_lyc si_Sc si_W si_memc si_mdc si_k si_regs si_ch si_A si_v si_md si_p si_cap si_n si_over] in HX |- *.
destruct HX as (HJ & HROD & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hch & Hal16 & Hbud & Hsp & Hlen9 & Hv & Hmd &
  HA8 & HAapp & HA63 & HAimg & HAsp & Rp & Rcap & Rn0 & Rn1 & Rover & (Mp & Mcap & Mn & Mover) & HRA & HApres & HAwr & HPN).
assert (Rn : 0 <= n < 2 ^ 64) by lia.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
destruct (sbd_entry B LAWS TL TLF fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n over
  HJ H10 HA8 HAapp HA63 HAimg HAsp Rp Rcap Rn Rover Mp Mcap Mn Mover HApres HRA Hal16 Hbud Hsp) as [HS SHOK].
pose proof HJ as (HAR & Hlyc & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk0' & _).
pose proof Hstk0' as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4208) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HAr : 4096 <= A /\ A + 28 <= 2 ^ 47 /\ (A + 28 <= 2147446784 \/ 17594333495296 <= A)).
{ destruct HAapp as [HAapp | HAapp]; [unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HAapp; lia | lia]. }
assert (Hspr : 2 ^ 46 <= spZ regs - 4208 /\ spZ regs <= 2 ^ 47)
  by (clear - Hbud WS Hslo Hceil C1 Hstk0 Hsp Hshi H47; lia).
box HAsp. box HAimg. box Hmd. box HPN. box HAapp.
set (E := ESB B regs p cap n over) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ESB; apply Eimg_env).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r)
  by (intros m r Hm; subst E; unfold ESB; apply ew_Eimg_Ereg_nat; exact Hm).
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (sbd_extra B p cap n over) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold ESB; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
cbn [Nat.add nth sbd_extra map] in E32, E33, E34, E35, E36, E37. clear EX.
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite (EE 2%nat 2%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned).
assert (E10 : ew E 10 = Z_to_bv 64 A) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U10 : bv_unsigned (ew E 10) = A) by (rewrite E10; apply unsigned_lit_small; lia).
clearbody E.
unfold cfg_at. change (w64 (BASE + AF_sb_dec)) with (Z_to_bv 64 (BASE + AF_sb_dec)).
paj_run_tok RUN HS HJ SHOK SBspan.
{ lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?s0 ?fp ?b0 ?bc ?lyv ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk s0 fp b0 bc lyv ow) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
    [reflexivity | cbn [ew]; rewrite Usp; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]).
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat A);
    [reflexivity | exact U10 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HAwr; lia |].
  apply awr_ok_nil. }
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) =>
assert (HKP : sbd_kept B lyc Sc W memc m2 (spZ regs - SB_DEC_STK) (spZ regs) (sbd_Er A v md p cap n));
[ eapply (sbd_kept_run B LAWS lyc Sc W memc memc m2 mdc _ _ _ (in_wrange Ef rs));
  [ exact HAR | apply sbd_kept_refl; intros a Ha; apply Hpres; lia | exact HFr | exact HG |];
  intros a Ha (rg & Hin & Hrg);
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end;
  cbn [In] in Hin;
  destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; try (exfalso; clear - Hrg; lia);
  [ rewrite Usp in Hrg; split; [intros Himg; pose proof (pa_segs_low a Himg); unfold kLowMemEnd in *; lia | left; split; lia]
  | rewrite U10 in Hrg; split; [intros Himg; pose proof (pa_img_range a Himg); unfold boxed, IMG_LO, IMG_TOP in *; lia
                                | right; left; unfold sbd_Er; left; lia] ]
| ] end.
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as HR0.
pose proof (st_ok_region_nth _ _ _ 5 _ HS eq_refl) as HR5.
cbn [ms_mem restrict] in HR0, HR5.
lazymatch type of HR0 with region_ok _ _ _ ?r => let r' := eval vm_compute in r in change r with r' in HR0 end.
lazymatch type of HR5 with region_ok _ _ _ ?r => let r' := eval vm_compute in r in change r with r' in HR5 end.
set (sp1 := 32 * ((spZ regs + -96) / 32)).
destruct (sp1_facts (spZ regs + -96) ltac:(clear - Hspr; lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 112 <= sp1 <= spZ regs - 96) by (clear - Hsp1r; lia). clear Hsp1r.
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
  (denot_and_m32 E 2 (spZ regs) (-96) E2 ltac:(clear - Hspr; lia) ltac:(clear - Hspr; lia) ltac:(clear - Hspr; lia)) R2.
assert (D9 : sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-96)) (SLit (-32))) (SLit 0)) = Z_to_bv 64 sp1).
{ rewrite denot_lit_U, U_add0, <- denot_lit_U.
  exact (denot_and_m32 E 2 (spZ regs) (-96) E2 ltac:(clear - Hspr; lia) ltac:(clear - Hspr; lia) ltac:(clear - Hspr; lia)). }
rreg_by HS (9%bv : bv 5) (Z_to_bv 64 sp1) D9 R9. clear D9.
assert (Esp1 : sp1 = 32 * ((spZ regs + -96) / 32)) by reflexivity. clearbody sp1.
prreg HS (1%bv : bv 5) R1. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (8%bv : bv 5) R8.
prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21.
prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch goal with |- SRr _ _ (mkCfg ?msX _) _ =>
  pose proof (sbd1_frame_of_region E (mrestrict (w_H W) (ms_mem msX)) (spZ regs) _ regs HR0 Usp) as HFR end.
lazymatch goal with |- SRr _ _ (mkCfg ?msX _) _ =>
  pose proof (sbd1_rec_of_region E (mrestrict (w_H W) (ms_mem msX)) _ _ A p cap n over HR5 U10 E34 E35 E36 E37
    Rp Rcap Rn Rover) as HREC end.
pmkst HS.
rewrite (palf_sm0 B TLF).
pose proof (count_cid_le_length 0 (frames Sc)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_stack_malloc_atS (fx := fq) SEGS B LAWS Hsegs (pal_env B TL) ML SMP 0 (ASM0 fq) ltac:(lia)
    W (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (sp1 - sp0) _ HJ) end.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by (clear - Hsp1 Hspr; lia). lia.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hsp0al. reflexivity.
  - clear - Hsp1 Hsp. lia.
  - rewrite Hes. clear - Hsp1 Hbud WS. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - let vv := eval vm_compute in (fs_frames 0) in change (fs_frames 0) with vv. clear - Hcnt Hlen9. lia. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz &
  Hflag & HK & _ & (fS2 & ES2)).
lazymatch type of HK with acall_kept _ _ _ _ _ ?mT _ _ _ _ _ =>
assert (HKP2 : sbd_kept B lyc Sc W memc mem2 (spZ regs - SB_DEC_STK) (spZ regs) (sbd_Er A v md p cap n))
  by (eapply (sbd_kept_call B lyc Sc W memc mT mem2 _ _ _ _ _ _ _ _ _ HKP HK); clear - Hspr Hsp1 Hceil Hslo Hbud Hstk0 C1 WS Hes Hsp; lia) end.
clear HKP. rename HKP2 into HKP.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (Hsub2 : forall c, In c (frames Sc) -> In c (frames S2)) by (intros c Hc; rewrite Hfrs2; right; exact Hc).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2pres & _).
lazymatch type of HK with acall_kept _ _ _ _ _ ?mT _ _ ?slo ?shi _ =>
assert (KA : forall x, A <= x < A + 28 -> mbyte SEGS (mrestrict (w_H W) mem2) x = mbyte SEGS (mrestrict (w_H W) mT) x);
[ intros x Hx;
  pose proof (region_kept_awr_aj B E lyc Sc W mT W mem2 slo shi (fun _ => False) 10%nat 0 28 0 0 [] A STK sp0 FP ly S own
    HK Hfrs0 ltac:(lia) ltac:(lia) U10 ltac:(intros a Ha; apply HAwr; lia)
    ltac:(intros a Ha; unfold boxed in HAsp; rewrite ?Hes, ?WS in *; lia) ltac:(intros a Ha Hf; exact Hf)
    ltac:(intros a Ha; lia)) as (KK & _);
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in KK; rewrite U10 in KK; apply KK; lia
| ];
assert (KS : forall x, spZ regs - 72 <= x < spZ regs ->
  mbyte SEGS (mrestrict (w_H W) mem2) x = mbyte SEGS (mrestrict (w_H W) mT) x);
[ intros x Hx; apply (mbyte_of_aview SEGS); apply (proj1 HK); [lia | rewrite ?Hes; lia] | ] end.
apply SRr_ret.
unfold sbd_at2. cbn [si_W]. split; [reflexivity|].
exists fpos, regs2, lyc, S2, mem2, md2.
split.
{ unfold sbd_cfg, cfg_at, w64. cbn [si_fq].
  replace (BASE + AF_sb_dec + SBD_P2) with (BASE + 16812) by (unfold AF_sb_dec, SBD_P2; lia).
  first [reflexivity | rewrite R1; reflexivity]. }
pose proof HP2 as GR. unfold aregs_preserved in GR.
unfold sbd_st2, sbd_mid, sbd_base, sbd_kept_at, sbd_frame, sbd_shadow_at, sbd_rec, sbd_F, sbd_FL, sbd_SH, sbd_SP1, sbd_SP.
cbn [si_fq si_STK si_sp0 si_FP si_ly si_S si_W0 si_mem0 si_md0 si_own si_lyc si_Sc si_W si_memc si_mdc si_k
  si_regs si_ch si_A si_v si_md si_p si_cap si_n si_over].
rewrite <- ?Esp1.
split.
{ split; [exact HJ2|]. split; [exact Hfrs2|]. split; [exact Eab|].
  split; [intros; reflexivity|]. split; [intros; reflexivity|].
  split; [exact HKP|].
  split.
  { intros j r Hj.
    assert (Hjl : (j < length sbd_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    unfold sbd_saved_regs in Hjl. cbn [length] in Hjl.
    apply (sbd1_val_mem_mbyte (mrestrict (w_H W) (ms_mem ms))).
    - intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KS. lia.
    - refine (HFR _ _ j r Hj).
      + intros j0 r0 Hj0. unfold sbd_saved_regs in Hj0.
        do 9 (destruct j0 as [|j0]; [cbn in Hj0; injection Hj0 as <-; cbn [In]; repeat (first [left; reflexivity | right])|]).
        cbn in Hj0. destruct j0; discriminate.
      + intros r0 Hr0. apply EE. rewrite Z_to_bv_unsigned. unfold bv_wrap.
        change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
  split.
  { change (fs_frame_bytes 0) with 64 in Hflag. replace (frame_addr lyc 0 fpos + 56) with (frame_addr lyc 0 fpos + 64 - 8) by lia.
    exact (val_mem_of_rdword SEGS _ _ _ _ Hflag). }
  intros j Hj. cbn in Hj.
  unfold zero_shadow, shadow_of_addr in Hz. change (fs_frame_bytes 0 / 8) with 8 in Hz.
  rewrite nth_repeat. unfold shadow_addr. apply Hz. lia. }
split.
{ split; [etransitivity; [exact (GR 2 ltac:(unfold acallee_saved; lia)) | exact R2]|].
  split; [etransitivity; [exact (GR 3 ltac:(unfold acallee_saved; lia))|];
          etransitivity; [exact R3|]; etransitivity; [exact (EE 3%nat 3%bv eq_refl) | exact Hgp]|].
  split; [etransitivity; [exact (GR 4 ltac:(unfold acallee_saved; lia))|];
          etransitivity; [exact R4|]; etransitivity; [exact (EE 4%nat 4%bv eq_refl) | exact Htp]|].
  split; [etransitivity; [exact (GR 8 ltac:(unfold acallee_saved; lia))|];
          etransitivity; [exact R8|]; etransitivity; [exact (EE 2%nat 2%bv eq_refl)|];
          unfold w64, spZ; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [etransitivity; [exact (GR 9 ltac:(unfold acallee_saved; lia)) | exact R9]|].
  split; [etransitivity; [exact (GR 18 ltac:(unfold acallee_saved; lia))|]; etransitivity; [exact R18 | exact E10]|].
  split; [etransitivity; [exact (GR 21 ltac:(unfold acallee_saved; lia))|]; etransitivity; [exact R21 | exact E32]|].
  split; [exact Ha0|].
  intros r Hr. etransitivity; [exact (GR r ltac:(unfold acallee_saved; lia))|].
  assert (Hr4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr4 as [-> | [-> | [-> | ->]]].
  - etransitivity; [exact R24 | exact (EE 24%nat 24%bv eq_refl)].
  - etransitivity; [exact R25 | exact (EE 25%nat 25%bv eq_refl)].
  - etransitivity; [exact R26 | exact (EE 26%nat 26%bv eq_refl)].
  - etransitivity; [exact R27 | exact (EE 27%nat 27%bv eq_refl)]. }
split; [etransitivity; [exact (GR 19 ltac:(unfold acallee_saved; lia))|];
        etransitivity; [exact R19|]; etransitivity; [exact (EE 12%nat 12%bv eq_refl) | exact H12]|].
split; [etransitivity; [exact (GR 20 ltac:(unfold acallee_saved; lia))|];
        etransitivity; [exact R20|]; etransitivity; [exact (EE 11%nat 11%bv eq_refl) | exact H11]|].
destruct HREC as (Q1 & Q2 & Q3 & Q4).
split; [|split; [|split]]; (eapply sbd1_val_mem_mbyte; [|eassumption]); intros x Hx; apply KA; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia.
Unshelve.
all: clear - Hspr Hsp1 Hceil Hslo Hbud Hstk0 C1 WS Hes Hsp; lia.
Qed.
End h.
End f.
End d.
