(* pcap_source_next (fuzz_pcap.asan 0x8181c) on libreac v1.9.0's ASan build: the phase from NP_fit
   (0x81b40, listing offset 0x1408) to NP_ts (0x81ce4) or NP_exit (0x81d24), the record that fits.

   The code (0x81b40..0x81ce4, rows NP_fit, NP_fit_ra, NP_mm_ra of PcapSourceNextDefs.v):
   - 0x81b40..0x81bb8: the two timestamp words from the eight header bytes the header phase left in
     a2 t1 a7 t0 (bytes 0..3) and a1 a6 a4 a5 (bytes 4..7): s10 := the seconds, s7 := the
     microseconds, byte-swapped when a0 (ps->sw) is not 0;
   - 0x81bbc: the shadow check of ps (`lbu a0,0(s8)`), `ld a3,0(s5)` = ps->f;
   - 0x81bd4: fread(buf, 1, incl, f) (the fread wrapper's 4-byte jump 0x41580);
   - 0x81bd8: `bne a0,s11` -> NP_exit with s6 = -1 (the record is cut: KCutFit);
   - 0x81bdc..0x81c14: ps->vtag := 0 (0x81bf4), s5 := &ts from the spill slot (0x81c08),
     ps->vid := 0 (0x81c14), each store behind its shadow check;
   - 0x81c18: `bltu s9,18` -> NP_ts; buf[12] = 0x81 (0x81c3c) and buf[13] = 0 (0x81c5c) or -> NP_ts;
   - the tag: ps->vtag := 1 (0x81c6c), ps->vid := ((buf[14] << 8) & 0xf00) | buf[15] (0x81ccc),
     __asan_memmove(buf + 12, buf + 16, incl - 16) (0x81cdc; the two ranges OVERLAP);
   - 0x81ce0: `addi s9,s9,-4`, then NP_ts.

   Every number is read from the pin fuzz_pcap.asan (sha256 b7a91d9b1fb0017d...),
   capstone 5 disassembly next.dis (sha256 06286410ee55; internal record).

   THE PROOF. fa_fit_phase (the end of this file) is `nx_from POST nx_ts_inv -> nx_from POST
   nx_exit_inv -> nx_from POST nx_fit_inv`, composed of
   - fa_pre: NP_fit -> the record's fread (fa_call, afread_spec) -> the cut nx_fitra_inv at NP_fit_ra;
   - fb_post: from nx_fitra_inv, a short read (kk < incl) runs the `bne` to NP_exit (nx_exit_inv,
     the model's KCutFit outcome); a full one runs the two stores and the tag test to NP_ts
     (fb_land_u over a Theorem Labs lane's fa_land_ts), or, for a tagged record, up to the call of
     __asan_memmove, which fa_mm_call (PcapSourceNextFitACall.v) carries on to NP_ts.
   Each straight run is a symbolic run of the image's shadow-token engine (PaShadow) from a local
   seat (fa_seat1 at NP_fit, fb_seat2 at NP_fit_ra; the buffer's bytes 12..15 are added as a region
   after the `bltu s9,18`, when incl >= 18 guarantees them).
   Section hypotheses: LAWS (AR_laws), AFREAD (afread_spec at the fread trampoline), ASIL
   (asource_img_laws) and AMM (lib/A/Rt/MemmoveDef.v amemmove_realizes at __asan_memmove: the copy
   with the source allowed to overlap the destination, which fa_mm_call takes). *)
(* Modified by Theorem Labs, 2026-10: the uses of PcapSourceNextFitAHelp.v's fa_ra_kept (deleted) name
   lib/A/Prog/PcapSourceCloseSpec.v's ra_frame. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PFreadM PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Rt Require Import MemmoveDef.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextFitAModel PcapSourceNextFitAHelp.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import YC4b YC81 YC1g YC1h YC85 YC88 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSourceMeta.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextFitADefs PcapSourceNextKit.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextFitBDefs PcapSourceNextFitALand PcapSourceNextFitACall.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceNextFitABits.
(* The image-free frame lemma ra_frame, Required without Import and used qualified. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceCloseSpec.
From Stdlib Require Import FunctionalExtensionality.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.



(* ---------------------------------------------------------------------------------------------- *)
(* The walk: a local seat at NP_fit, the run to the record's fread, the call, and the cut after it  *)
(* ---------------------------------------------------------------------------------------------- *)

Definition fa_SB : sv := SOff 32 0.
Definition fa_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition fa_sh8 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 21 0) (SLit 3)) fa_SB.
Definition fa_sr : list sv := sr_set sr_atoms (24%bv : bv 5) fa_sh8.
Definition fa_spill_r : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 120 0 0 [YP09.mkChunk 32 (CVal 8 (SOff 33 0)); YP09.mkChunk 40 (CVal 8 fa_SB)].
Definition fa_ps_r (wlo whi : Z) : YP09.region :=
  YP09.mkRegion (Some 21%nat) 0 24 wlo whi [YP09.mkChunk 0 (CVal 8 (SOff 34 0))].
Definition fa_byte_af : afact := mkAF 0 255 0.
Definition fa_G1 : facts := mkFacts
  [(12%nat, fa_byte_af); (6%nat, fa_byte_af); (17%nat, fa_byte_af); (5%nat, fa_byte_af);
   (11%nat, fa_byte_af); (16%nat, fa_byte_af); (14%nat, fa_byte_af); (15%nat, fa_byte_af);
   (21%nat, mkAF 4096 (2 ^ 47 - 24) 3); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition fa_ss1 : sstate := mkSS NP_fit fa_sr [fa_spill_r; fa_ps_r 0 0] None fa_G1.
Definition fa_SH : list shent := [mkSHE 21 0 24].
Definition fa_extra (ts h : Z) : list word := map (Z_to_bv 64) [SHADOW_OFF; ts; h].

Lemma fa_regs_ok_set : forall E sr regs (r : bv 5) e,
  regs_ok E sr regs -> bv_eqb r 0 = false -> getr regs r = sv_denot E e -> regs_ok E (sr_set sr r e) regs.
Proof.
  intros E sr regs r e Hr Hr0 He r'. unfold sr_set. rewrite Hr0. unfold sr_get.
  destruct (bv_eqb r' 0) eqn:Hr'0; [specialize (Hr r'); unfold sr_get in Hr; rewrite Hr'0 in Hr; exact Hr |].
  rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi.
  - apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. exact He.
  - specialize (Hr r'). unfold sr_get in Hr. rewrite Hr'0 in Hr. exact Hr.
Qed.

Ltac fbox := repeat match goal with
  | H : _ \/ _ |- _ => box H
  | H : ?A -> ?Bq |- _ => lazymatch Bq with False => fail | _ => box H end
  end.


Ltac fa_base HB :=
  destruct HB as (HJ0 & HROD & Hraok & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & Hal16 & Hwlo & Hwhi & Hch
    & Hcnt & Hpsf & Hh64 & Hps8 & Hps4096 & Hps47 & Hpsamr & Hcown & Hcfa1 & Hcfa2 & HRA0 & HPS0 & Hsw & Hrng
    & HWRps & HBUF0 & HTS0 & HSTR & HMETA & HE0 & HE2).

Ltac fa_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v end; lia.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Notation VAL := (@pa_val _ pcap_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Notation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.

Lemma fa_ms_eq : forall cx fp pc W3 ms3 sh, nx_body0 cx fp pc W3 ms3 sh ->
  restrict (w_H W3) ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (rdW W3 (ms_mem ms3)) (seg_rom SEGS).
Proof.
  intros cx fp pc W3 ms3 sh (Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & _).
  destruct ms3. cbn in *. subst. reflexivity.
Qed.

Lemma fa_seat1 : forall cx fp k2 ly3 S3 W3 ms3 md3,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  nx_fit_inv B MT KS cx fp k2 ly3 S3 W3 ms3 md3 ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) (fa_extra (n_ts cx) (n_h cx)))) fa_ss1 (restrict (w_H W3) ms3) /\
  sh_ok SEGS fa_SB fa_SH (Eimg (Ereg (ms_regs ms3) (fa_extra (n_ts cx) (n_h cx)))) (rdW W3 (ms_mem ms3)).
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 HB HJ GI.
  destruct GI as (q & HM & Hq & Hlh & Hpq & Hincl & R10 & R12 & R6 & R17 & R5 & R11 & R16 & R14 & R15
    & R20 & R21 & R22 & R23 & R25 & R27).
  destruct HM as (HBD & R24 & HJB & HKEPT & HEsub & Hh & HPS & HRAps & HSRC & Hqr & HBUF & HTS).
  pose proof HBD as (HB0 & HSL).
  pose proof HB0 as (Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & HREGS & HSAV & HHDR & HFLW & HSHW & Hlen & R18 & R19 & HF0).
  pose proof HREGS as (R2 & R8 & R9 & R3 & R4).
  pose proof HSL as (S_F0 & S_FK & S_TS & S_SB & _).
  fa_base HB.
  unfold PS_LEN in Hps47, Hcfa2.
  pose proof HJ0 as (HAR0 & Hly0 & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hcin : In (n_cid cx, n_pos cx) (frames (n_Sc cx))) by (rewrite Hfrs0; apply in_or_app; left; exact Hcown).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR0 Hcin) as (Hf4096 & Hfceil & Hfapp).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
  assert (HSP1 : n_sp1 cx = 32 * ((spZ (n_regs cx) - NX_MFRAME) / 32)) by reflexivity.
  assert (Hsp1lo : spZ (n_regs cx) - 256 <= n_sp1 cx <= spZ (n_regs cx) - 224).
  { rewrite HSP1. unfold NX_MFRAME. pose proof (Z.mod_pos_bound (spZ (n_regs cx) - 224) 32 ltac:(lia)).
    pose proof (Z_div_mod_eq_full (spZ (n_regs cx) - 224) 32). lia. }
  assert (HNX : NX_STK = 8496) by reflexivity.
  set (E := Eimg (Ereg (ms_regs ms3) (fa_extra (n_ts cx) (n_h cx)))).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) (fa_extra (n_ts cx) (n_h cx))) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (ER : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
    by (intros n r Hr; rewrite EL by (pose proof (u5_range r); unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ n r Hr)).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (n_ts cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (n_h cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
  assert (E21 : ew E 21 = Z_to_bv 64 (n_ps cx)) by (rewrite (ER 21%nat (21%bv : bv 5) eq_refl); exact R21).
  assert (E9 : ew E 9 = Z_to_bv 64 (n_sp1 cx)) by (rewrite (ER 9%nat (9%bv : bv 5) eq_refl); exact R9).
  assert (Hsp1r : 0 <= n_sp1 cx /\ n_sp1 cx + 120 <= 2 ^ 47) by lia.
  assert (Hts64 : 0 <= n_ts cx < 2 ^ 64).
  { destruct (Z.eq_dec (n_ts cx) 0) as [->|Hts0]; [lia|].
    destruct (HTS0 Hh Hts0) as (_ & _ & Hts4096 & Hts47 & _). lia. }
  assert (Ups : U E (SOff 21 0) = n_ps cx) by (apply U_atom; [exact E21 | lia]).
  assert (USB : U E fa_SB = SHADOW_OFF) by (apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
  split.
  - rewrite (fa_ms_eq _ _ _ _ _ _ HB0). unfold fa_ss1. apply pa_entry_st_ok_full.
    + apply fa_regs_ok_set; [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity |].
      rewrite R24, (denot_lit_U E fa_sh8). f_equal. unfold fa_sh8.
      rewrite U_SAlu, U_SAlu, Ups, USB, U_lit by lia. cbn [zalu_raw]. change (Z.land 3 63) with 3.
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      unfold zcanon, M64, shadow_of_addr, SHADOW_OFF.
      assert (0 <= n_ps cx / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      rewrite (Z.mod_small (n_ps cx / 8)) by lia. rewrite Z.mod_small by lia. lia.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * unfold region_ok, fa_spill_r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E9, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 33 0) (n_ts cx));
             [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
           exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S_TS).
        -- apply (chunk_ok_val SEGS E _ _ 40 8 fa_SB SHADOW_OFF);
             [unfold fa_SB; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | unfold SHADOW_OFF; zside | zside |].
           exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S_SB).
      * unfold region_ok, fa_ps_r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E21, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 34 0) (n_h cx));
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        destruct HPS as (Hpf & _). rewrite Z.add_0_r. unfold PS_F_OFF in Hpf. rewrite Z.add_0_r in Hpf. exact Hpf.
    + unfold fa_spill_r, fa_ps_r. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E21, !unsigned_lit_small by lia.
      split; [split; [right; lia | exact I] | split; exact I].
    + split; [|split; exact I]. unfold fa_G1, fa_byte_af. cbn [f_atoms atoms_ok]. unfold afact_ok.
      cbn [af_lo af_hi af_al2].
      assert (FB : forall i, 0 <= PSN.fb (nxF (n_C cx)) i < 256).
      { intros i. unfold PSN.fb. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) (nxF (n_C cx)) (Z_to_bv 8 0))) as Hr.
        unfold bv_modulus in Hr. change (2 ^ Z.of_N 8) with 256 in Hr. exact Hr. }
      assert (UBy : forall (n : nat) (r : bv 5) i, Z.of_nat n = bv_unsigned r ->
        getr (ms_regs ms3) r = w64 (PSN.fb (nxF (n_C cx)) i) -> bv_unsigned (ew E n) = PSN.fb (nxF (n_C cx)) i).
      { intros n r i Hn Hr. rewrite (ER n r Hn), Hr. apply unsigned_lit_small. pose proof (FB i). lia. }
      rewrite (UBy 12%nat (12%bv : bv 5) q eq_refl R12), (UBy 6%nat (6%bv : bv 5) (q + 1) eq_refl R6),
        (UBy 17%nat (17%bv : bv 5) (q + 2) eq_refl R17), (UBy 5%nat (5%bv : bv 5) (q + 3) eq_refl R5),
        (UBy 11%nat (11%bv : bv 5) (q + 4) eq_refl R11), (UBy 16%nat (16%bv : bv 5) (q + 5) eq_refl R16),
        (UBy 14%nat (14%bv : bv 5) (q + 6) eq_refl R14), (UBy 15%nat (15%bv : bv 5) (q + 7) eq_refl R15).
      rewrite E21, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      pose proof (FB q). pose proof (FB (q + 1)). pose proof (FB (q + 2)). pose proof (FB (q + 3)).
      pose proof (FB (q + 4)). pose proof (FB (q + 5)). pose proof (FB (q + 6)). pose proof (FB (q + 7)).
      change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; first [exact I | unfold SHADOW_OFF; lia].
  - unfold sh_ok, fa_SH. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart.
    cbn [she_m she_lo she_hi]. rewrite USB, Ups. split.
    + rewrite Z.add_0_r, <- (aview_rd_of SEGS). exact HRAps.
    + intros a Ha. unfold SHADOW_OFF, PS_LEN in *. cbn in Ha. lia.
Qed.

Definition fa_barea (cx : ncx) (fp a : Z) : Prop :=
  (n_sp1 cx <= a < spZ (n_regs cx)) \/ (nF cx fp <= a < nF cx fp + 64) \/ (nSH cx fp <= a < nSH cx fp + 8).

Lemma fa_body_keep : forall cx fp pc pc' W3 ms3 W4 ms4 sh,
  nx_body cx fp pc W3 ms3 sh ->
  ms_pc_val ms4 = w64 (BASE + pc') -> ms_resv ms4 = None -> ms_svc_pending ms4 = None ->
  ms_rom ms4 = seg_rom SEGS -> ms_fregs ms4 = fp_regs -> ms_fcsr ms4 = fp_csr ->
  getr (ms_regs ms4) 2 = getr (ms_regs ms3) 2 -> getr (ms_regs ms4) 8 = getr (ms_regs ms3) 8 ->
  getr (ms_regs ms4) 9 = getr (ms_regs ms3) 9 -> getr (ms_regs ms4) 3 = getr (ms_regs ms3) 3 ->
  getr (ms_regs ms4) 4 = getr (ms_regs ms3) 4 -> getr (ms_regs ms4) 18 = getr (ms_regs ms3) 18 ->
  getr (ms_regs ms4) 19 = getr (ms_regs ms3) 19 ->
  (forall a, fa_barea cx fp a -> aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  nx_body cx fp pc' W4 ms4 sh.
Proof.
  intros cx fp pc pc' W3 ms3 W4 ms4 sh ((_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4) & HSAV & (Hh0 & Hh8 & Hh16)
    & HFL & HSH & Hlen & G18 & G19 & HF0) & HSL)
    Hpc Hrv Hsv Hrom Hfr Hfc E2 E8 E9 E3 E4 E18 E19 HK.
  assert (Hsp1 : n_sp1 cx <= spZ (n_regs cx) - 224).
  { unfold n_sp1, nx_sp1, NX_MFRAME. pose proof (Z.mod_pos_bound (spZ (n_regs cx) - 224) 32 ltac:(lia)).
    pose proof (Z_div_mod_eq_full (spZ (n_regs cx) - 224) 32). lia. }
  assert (RW : forall a v, (forall k, 0 <= k < 8 -> fa_barea cx fp (a + k)) ->
    rdword (aview SEGS (w_H W3) (ms_mem ms3)) a = Some v -> rdword (aview SEGS (w_H W4) (ms_mem ms4)) a = Some v).
  { intros a v Ha Hv. rewrite <- Hv. apply rdword_ext. intros k Hk. apply HK. apply Ha. exact Hk. }
  unfold NX_FLAGPTR in *.
  Ltac rwk RW H := lazymatch type of H with rdword _ ?a = Some ?v =>
    apply (RW a v); [intros ?k ?Hk; unfold fa_barea; first [left; lia | right; left; lia | right; right; lia] | exact H] end.
  assert (RS : forall off v, 0 <= off <= 112 -> nslot cx W3 ms3 off v -> nslot cx W4 ms4 off v).
  { intros off v Ho Hv. unfold nslot in *. apply (RW _ v); [intros k Hk; left; lia | exact Hv]. }
  split.
  - split; [exact Hpc|]. split; [exact Hrv|]. split; [exact Hsv|]. split; [exact Hrom|].
    split; [exact Hfr|]. split; [exact Hfc|].
    split; [unfold nregs; rewrite E2, E8, E9, E3, E4; tauto|].
    split.
    { destruct HSAV as (Hra & Hsj). split.
      - rwk RW Hra.
      - intros j Hj. pose proof (Hsj j Hj) as Hsjj. rwk RW Hsjj. }
    split.
    { unfold nheader. split; [|split].
      - rwk RW Hh0.
      - rwk RW Hh8.
      - rwk RW Hh16. }
    split; [unfold nflagw, NX_FLAGPTR in *; rwk RW HFL|].
    split.
    { unfold nshadow in *. intros i Hi. rewrite HK; [exact (HSH i Hi)|]. right; right.
      rewrite Hlen in Hi. unfold NX_NSH in Hi. lia. }
    split; [exact Hlen|]. split; [rewrite E18; exact G18|]. split; [rewrite E19; exact G19|].
    apply RS; [unfold NS_F0; lia | exact HF0].
  - destruct HSL as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11).
    unfold NS_F0, NS_FK, NS_TS, NS_SB, NS_PS8, NS_PS12, NS_SH8, NS_SH12, NS_OFF8, NS_OFF12, NS_MASK in *.
    refine (conj (RS _ _ _ S1) (conj (RS _ _ _ S2) (conj (RS _ _ _ S3) (conj (RS _ _ _ S4) (conj (RS _ _ _ S5)
      (conj (RS _ _ _ S6) (conj (RS _ _ _ S7) (conj (RS _ _ _ S8) (conj (RS _ _ _ S9) (conj (RS _ _ _ S10)
      (RS _ _ _ S11)))))))))));
    lia.
Qed.



Lemma fa_sp1 : forall cx, n_sp1 cx <= spZ (n_regs cx) - 224 /\ spZ (n_regs cx) - 256 <= n_sp1 cx /\ n_sp1 cx mod 32 = 0.
Proof.
  intros cx. unfold n_sp1, nx_sp1, NX_MFRAME.
  pose proof (Z.mod_pos_bound (spZ (n_regs cx) - 224) 32 ltac:(lia)).
  pose proof (Z_div_mod_eq_full (spZ (n_regs cx) - 224) 32).
  split; [lia|]. split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

(* The bytes the call may write all lie under the allocator's ceiling (the struct and the timestamp
   cell in the caller's frames, the buffer and the FILE in blocks). *)
Lemma fa_E_low : forall cx a, nx_base SK B KS cx -> n_h cx <> 0 -> nx_E cx a -> 4096 <= a < alloc_ceiling.
Proof.
  intros cx a HB Hh HE. fa_base HB. unfold PS_LEN in *.
  pose proof HJ0 as (HAR0 & _ & _ & _ & _ & Hfrs0 & _).
  assert (Hcin : In (n_cid cx, n_pos cx) (frames (n_Sc cx))) by (rewrite Hfrs0; apply in_or_app; left; exact Hcown).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR0 Hcin) as (Hf4096 & Hfceil & _).
  pose proof (fs_frame_bytes_nonneg (n_cid cx)).
  destruct (HBUF0 Hh) as (Hbin & Hb4096 & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hbin) as (_ & _ & Hbceil & _).
  destruct (HSTR Hh) as (Hhin & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hhin) as (_ & Hh4096 & Hhceil & _).
  pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as [_ Hrq].
  change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
  unfold nx_E, nx_wrset in HE. unfold SRC_FILE_BLOCK, PS_LEN in *.
  destruct HE as [Ha | [Ha | [(Hts & Ha) | (_ & Ha)]]]; [lia | lia | | lia].
  destruct (HTS0 Hh Hts) as (_ & _ & Ht4096 & _ & _ & (tc & tp & Htin & Htf1 & Htf2) & _).
  assert (Htc : In (tc, tp) (frames (n_Sc cx))) by (rewrite Hfrs0; apply in_or_app; left; exact Htin).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR0 Htc) as (_ & Htceil & _). lia.
Qed.

Lemma fa_achain : forall cx ly3 W3 ms3,
  nx_base SK B KS cx -> n_h cx <> 0 ->
  layout_le (length (st_secs (n_S cx))) (n_ly cx) ly3 ->
  nsaved cx W3 ms3 ->
  nx_kept SEGS NX_STK B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 (ms_mem ms3) (spZ (n_regs cx)) (nx_E cx) ->
  achain ly3 (aview SEGS (w_H W3) (ms_mem ms3)) (n_sp1 cx) (spZ (n_regs cx)) (nx_ch cx).
Proof.
  intros cx ly3 W3 ms3 HB Hh Hly3 (Hra & Hsj) (K1 & _).
  pose proof (fun a => fa_E_low cx a HB Hh) as Elow.
  pose proof (fa_sp1 cx) as (Hs1 & Hs2 & Hs3).
  fa_base HB. fbox.
  pose proof HJ0 as (HAR0 & Hly0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HNX : NX_STK = 8496) by reflexivity.
  assert (T3 : ly_top ly3 = ly_top (n_ly cx)) by (destruct Hly3 as (_&_&_&_&_&_&_&_&T&_); exact T).
  assert (T0 : ly_top (n_lyc cx) = ly_top (n_ly cx)) by (destruct Hly0 as (_&_&_&_&_&_&_&_&T&_); exact T).
  apply (achain_ly_top (n_lyc cx)); [congruence|].
  unfold nx_ch. destruct (Z.ltb_spec (spZ (n_regs cx) + 16) (ly_top (n_lyc cx))) as [Hlt|Hge].
  - apply (achain_push (n_lyc cx) (aview SEGS (w_H (n_W cx)) (n_memc cx)) _ (spZ (n_regs cx))
      (s0Z (n_regs cx)) (raZ (n_regs cx)) (n_ch cx) (n_sp1 cx) Hch).
    + lia.
    + intros a Ha. apply K1; [lia | lia |]. intros HE. pose proof (Elow a HE). lia.
    + exact Hra.
    + replace (spZ (n_regs cx) - 16) with (spZ (n_regs cx) - 16 - 8 * 0) by lia. rewrite (Hsj 0 ltac:(lia)).
      reflexivity.
    + exact Hra4.
    + lia.
    + apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [z Hz].
      exists (2 * z). lia.
    + lia.
    + lia.
  - left. split; [right; left; lia | reflexivity].
Qed.

Lemma fa_kept_call : forall cx ly3 S3 W3 mem3 W2 mem2 (Ef : Z -> Prop),
  nx_base SK B KS cx -> n_h cx <> 0 ->
  layout_le (length (st_secs (n_S cx))) (n_ly cx) ly3 ->
  ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx) ->
  (forall x, In x (frames (n_Sc cx)) -> In x (frames S3)) ->
  nx_kept SEGS NX_STK B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 mem3 (spZ (n_regs cx)) (nx_E cx) ->
  rread_kept SEGS B AFREAD_STK ly3 S3 W3 mem3 W2 mem2 (n_sp1 cx) Ef ->
  (forall a, Ef a -> nx_E cx a) ->
  nx_kept SEGS NX_STK B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W2 mem2 (spZ (n_regs cx)) (nx_E cx).
Proof.
  intros cx ly3 S3 W3 mem3 W2 mem2 Ef HB Hh Hly3 Hbl Hfr (K1 & K2 & K3 & K4 & K5 & K6) (A1 & A2 & A3 & A4 & A5 & A6) HEf.
  pose proof (fa_sp1 cx) as (Hs1 & Hs2 & Hs3).
  pose proof (fun a => fa_E_low cx a HB Hh) as Elow.
  fa_base HB. fbox.
  pose proof HJ0 as (HAR0 & Hly0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HNX : NX_STK = 8496) by reflexivity. assert (HAF : AFREAD_STK = 8192) by reflexivity.
  assert (EF : forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p).
  { intros c p. rewrite (frame_addr_layout_le _ _ _ Hly3), (frame_addr_layout_le _ _ _ Hly0). reflexivity. }
  split.
  { intros a Ha Hw He. rewrite (A1 a Ha ltac:(lia) ltac:(intros X; exact (He (HEf a X)))). exact (K1 a Ha Hw He). }
  split.
  { intros b m i Hb Hi He. rewrite <- Hbl in Hb.
    rewrite (A2 b m i Hb Hi ltac:(intros X; exact (He (HEf _ X)))). rewrite Hbl in Hb. exact (K2 b m i Hb Hi He). }
  split.
  { intros a Hi Hs He. rewrite (A3 a Hi Hs He). exact (K3 a Hi Hs He). }
  split.
  { intros cid pos a Hin Hr He. rewrite (A4 cid pos a (Hfr _ Hin)); [exact (K4 cid pos a Hin Hr He)| |].
    - unfold frame_rng, in_zr in *. cbn [fst snd] in *. rewrite !EF. exact Hr.
    - intros X. exact (He (HEf a X)). }
  split.
  { intros a Ha Hw Hp. apply A5; [exact Ha | lia | exact (K5 a Ha Hw Hp)]. }
  intros a Ha. destruct (Z_lt_le_dec a (n_sp1 cx - AFREAD_STK)) as [Hl|Hl];
    [| destruct (Z_lt_le_dec a (n_sp1 cx)) as [Hl2|Hl2]; [apply A6; lia|]];
    apply A5; [lia | lia | exact (K6 a Ha) | lia | lia | exact (K6 a Ha)].
Qed.






(* The cut after the record's fread (NP_fit_ra, 0x81bd8). *)
Definition nx_fitra_inv (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  let sw := (n_sw cx =? 1) in
  let F := nxF (n_C cx) in
  let R := ms_regs ms3 in
  exists q kk : Z,
  nx_mid B MT KS cx fp NP_fit_ra NSH_ph (nx_E cx) (q + 16 + kk) (PSN.orig sw F q) (n_lvt cx) (n_lvid cx)
    (n_tsv cx) k2 ly3 S3 W3 ms3 md3 /\
  nx_q sw (n_C cx) (n_cap cx) (n_p cx) = q /\
  nx_lh sw (n_C cx) (n_cap cx) (n_p cx) = Some q /\
  n_p cx <= q /\ q + 16 <= Z.of_nat (length (n_C cx)) /\
  0 < PSN.incl sw F q <= n_cap cx /\
  kk = Z.min (PSN.incl sw F q) (Z.of_nat (length (n_C cx)) - (q + 16)) /\
  (exists bj', garr8 SEGS (rdW W3 (ms_mem ms3)) (n_buf cx) bj' /\ length bj' = length (n_bj cx) /\
     firstn (Z.to_nat kk) bj' = firstn (Z.to_nat kk) (skipn (Z.to_nat (q + 16)) (n_C cx))) /\
  getr R 10 = w64 kk /\
  getr R 20 = w64 (n_buf cx) /\ getr R 21 = w64 (n_ps cx) /\ getr R 22 = w64 (-1) /\
  getr R 25 = w64 (PSN.incl sw F q) /\ getr R 27 = w64 (PSN.incl sw F q) /\
  bv_unsigned (getr R 26) mod 2 ^ 32 = PSN.hw sw F q 0 /\
  bv_unsigned (getr R 23) mod 2 ^ 32 = PSN.hw sw F q 4.


Hypothesis AFREAD : afread_spec SK SEGS B KS (SIGMA PS___interceptor_trampoline_fread).
Let RUN := paj_run (PL := PL_pcap) B LAWS.
Let BR := paj_branch (PI := PI).

Lemma fa_call : forall cx fp k2 ly3 S3 W3 ms3 md3 (rg : bvmap 5 word) mdq q,
  nx_from SK B KS (nx_post SK B MT KS) nx_fitra_inv ->
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) mdq k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  nx_mid B MT KS cx fp NP_fit NSH_ph (nx_E cx) (q + 16) (PSN.orig (n_sw cx =? 1) (nxF (n_C cx)) q)
    (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W3 ms3 md3 ->
  nx_q (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) = q ->
  nx_lh (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) = Some q ->
  n_p cx <= q ->
  0 < PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q <= n_cap cx ->
  m_fds mdq = m_fds md3 -> m_fs mdq = m_fs md3 ->
  getr rg 1 = Z_to_bv 64 (BASE + NP_fit_ra) ->
  getr rg 10 = w64 (n_buf cx) -> getr rg 11 = w64 1 ->
  getr rg 12 = w64 (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q) -> getr rg 13 = w64 (n_h cx) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 27]%bv -> getr rg r = getr (ms_regs ms3) r) ->
  bv_unsigned (getr rg 26) mod 2 ^ 32 = PSN.hw (n_sw cx =? 1) (nxF (n_C cx)) q 0 ->
  bv_unsigned (getr rg 23) mod 2 ^ 32 = PSN.hw (n_sw cx =? 1) (nxF (n_C cx)) q 4 ->
  getr (ms_regs ms3) 20 = w64 (n_buf cx) -> getr (ms_regs ms3) 21 = w64 (n_ps cx) ->
  getr (ms_regs ms3) 22 = w64 (-1) ->
  getr (ms_regs ms3) 25 = w64 (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q) ->
  getr (ms_regs ms3) 27 = w64 (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q) ->
  SRr SEGS W3 (mkCfg (mkst rg (Z_to_bv 64 (SIGMA PS___interceptor_trampoline_fread)) (ms_mem ms3) (seg_rom SEGS)) mdq)
    (nx_post SK B MT KS cx).
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 rg mdq q NEXT HB HJ HFRS HM Hq Hlh Hpq Hincl Hfdq Hfsq
    R1 R10 R11 R12 R13 RK R26 R23 R20s R21s R22s R25s R27s.
  set (sw := n_sw cx =? 1) in *. set (F := nxF (n_C cx)) in *. set (incl := PSN.incl sw F q) in *.
  pose proof HM as (HBD & R24 & HJB & HKEPT & HEsub & Hh & HPS & HRAps & HSRC & Hqr & HBUF & HTS).
  pose proof HJB as (Hk2 & Hbl3 & Hmo & Hfd3 & Hfs3).
  pose proof HBD as (HB0 & HSL).
  pose proof HB0 as (Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & HREGS & HSAV & HHDR & HFLW & HSHW & Hlen & R18 & R19 & HF0).
  pose proof HREGS as (G2 & G8 & G9 & G3 & G4).
  pose proof (fa_sp1 cx) as (Hs1 & Hs2 & Hs3).
  pose proof (fun a => fa_E_low cx a HB Hh) as Elow.
  pose proof HB as HB'. box HB. box HTS.
  fa_base HB'. unfold PS_LEN in *. fbox.
  pose proof HJ0 as (HAR0 & Hly0 & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HNX : NX_STK = 8496) by reflexivity. assert (HAF : AFREAD_STK = 8192) by reflexivity.
  destruct (HBUF0 Hh) as (Hbin & Hb4096 & Hbn63 & Hbg & Hblen & Hcap & HWRbuf & Hbps). unfold NX_CAP_MAX in Hcap.
  destruct (HSTR Hh) as (Hhin & Hbin2 & HSRC0 & HClen & Hp & Hbh & Hbb & Hpsh & Hpsb & Htsh & HFPh).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hbin) as (_ & _ & Hbceil & Hbapp & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hhin) as (_ & Hh4096 & Hhceil & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hbin2) as (_ & Hbb4096 & Hbbceil & _).
  fbox.
  pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as [_ Hrqb].
  pose proof (req_size_pos (Z.of_nat (length (n_C cx))) ltac:(lia)) as [_ Hrqc].
  clear HMETA HROD Hch Hsw Hrng HPS0 HWRps Hpsf HE0 HE2 HRA0 HBUF0 HSTR.
  assert (Hbh' : n_buf cx + incl <= n_h cx \/ n_h cx + SRC_FILE_BLOCK <= n_buf cx)
    by (clear - Hbh Hincl Hcap; unfold boxed, nx_bufn in *; lia).
  assert (Hbb' : n_buf cx + incl <= n_b cx \/ n_b cx + Z.of_nat (length (n_C cx)) <= n_buf cx)
    by (clear - Hbb Hincl Hcap; unfold boxed, nx_bufn in *; lia).
  fbox.
  change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
  assert (Hbufn : incl <= nx_bufn (n_cap cx)) by (unfold nx_bufn; lia).
  assert (EF : forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p).
  { intros c p. rewrite (frame_addr_layout_le _ _ _ Hly3), (frame_addr_layout_le _ _ _ Hly0). reflexivity. }
  assert (Hown3 : forall x, In x (n_own cx) -> In x ((NX_CID, fp) :: n_own cx)) by (intros x Hx; right; exact Hx).
  assert (Hblc : forall x, In x (ablocks B (n_lyc cx) (n_Sc cx)) -> In x (ablocks B ly3 S3)) by (intros x Hx; rewrite Hbl3; exact Hx).
  assert (Hspc : spZ rg = n_sp1 cx).
  { unfold spZ. rewrite (RK 2%bv ltac:(cbn; tauto)), G2. apply unsigned_lit_small. lia. }
  eapply SRr_bind.
  { apply (AFREAD (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
      ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) mdq k2 rg (nx_ch cx)
      (n_buf cx) incl (n_h cx) (n_b cx) (q + 16) (n_C cx)).
    unfold afread_pre, rread_call, rread_dest, rread_at.
    assert (HBS := pa_B_ok). assert (HBL := pa_base_lo (PL := PL_pcap) (PI := PI)).
    split.
    { split; [exact HJ|].
      split; [rewrite R1; apply ret_ok_codeptr_v; [unfold NP_fit_ra; lia | reflexivity]|].
      split; [unfold raZ; rewrite R1, unsigned_lit_small by (unfold NP_fit_ra; lia); unfold NP_fit_ra; lia|].
      split; [rewrite (RK 3%bv ltac:(cbn; tauto)), G3; exact Hgp|].
      split; [rewrite (RK 4%bv ltac:(cbn; tauto)), G4; exact Htp|].
      rewrite Hspc.
      split; [rewrite Z.mod_divide in Hs3 |- * by lia; destruct Hs3 as [z Hz]; exists (2 * z); lia|].
      split; [lia|]. split; [lia|].
      assert (Hs0 : s0Z rg = spZ (n_regs cx)).
      { unfold s0Z. rewrite (RK 8%bv ltac:(cbn; tauto)), G8. apply unsigned_lit_small. lia. }
      rewrite Hs0. unfold boxed in HB. exact (fa_achain cx ly3 W3 ms3 HB Hh Hly3 HSAV HKEPT). }
    split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact R13|].
    split; [exact (Hblc _ Hhin)|]. split; [exact (Hblc _ Hbin2)|].
    split; [left; rewrite Hspc; lia|].
    split; [exact HSRC|].
    split.
    { intros a Ha. split; [|rewrite Hspc; unfold SRC_FILE_BLOCK in Ha; lia].
      assert (Hfa : inFP (asource_fp (n_h cx)) a)
        by (exists (n_h cx, n_h cx + SRC_FILE_BLOCK); split; [left; reflexivity | cbn [fst snd]; lia]).
      destruct (HFPh a Hfa) as [Hfp | Htmp].
      - right. left. split; [exact Hfp|]. exists (n_h cx), SRC_FILE_BLOCK. split; [exact (Hblc _ Hhin)|].
        change (req_size SRC_FILE_BLOCK) with 1304. unfold SRC_FILE_BLOCK in Ha. lia.
      - right. right. left. exact (in_tmp_block_mono _ _ _ a Hblc Htmp). }
    split; [lia|].
    split; [unfold boxed in Hbh'; exact Hbh'|]. split; [unfold boxed in Hbb'; exact Hbb'|]. split; [lia|].
    split; [apply (amem_range_sub_app (n_buf cx) (req_size (nx_bufn (n_cap cx)))); [unfold boxed in Hbapp; exact Hbapp | lia | lia | lia | lia]|].
    split; [right; right; exists (n_buf cx), (nx_bufn (n_cap cx)); split; [exact (Hblc _ Hbin) | lia]|].
    split.
    { intros a Ha. split; [|rewrite Hspc; lia].
      apply (awr_byte_weaken _ _ _ _ _ _ _ _ _ _ a Hblc Hown3 EF). apply (proj1 (HWRbuf a ltac:(lia))). }
    split.
    { apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) mdq (n_buf cx) (nx_bufn (n_cap cx)));
        [exact HAR3 | exact (Hblc _ Hbin) | lia | lia]. }
    intros Hn0. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) mdq (n_buf cx) (nx_bufn (n_cap cx)));
      [exact HAR3 | exact (Hblc _ Hbin) | lia | lia | exact Hn0].
  }
  cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HK2 & HQ2).
  destruct HQ2 as (-> & -> & Ha0 & HG2 & HSRC2 & _ & _ & Hfd2 & Hfs2 & Hshb).
  unfold boxed in HB. eapply NEXT; [exact HB | exact HJ2 | exact HFRS |].
  unfold nx_fitra_inv. fold sw F incl.
  set (j := rread_k incl (Z.of_nat (length (n_C cx))) (q + 16)) in *.
  assert (Hj : j = Z.min incl (Z.of_nat (length (n_C cx)) - (q + 16))) by reflexivity.
  pose proof HK2 as (A1 & A2 & A3 & A4 & A5 & A6).
  pose proof HJ2 as (HAR2 & _).
  assert (P : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr rg r) by (apply fa_pres; exact HP2).
  assert (HFin : In (NX_CID, fp) (frames S3)) by (rewrite HFRS; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR3 HFin) as (HF4096 & HFceil & HFapp).
  assert (HFB : fs_frame_bytes NX_CID = 64) by reflexivity.
  assert (EnF : frame_addr ly3 NX_CID fp = nF cx fp) by (unfold nF; apply EF).
  rewrite EnF in HF4096, HFceil, HFapp. rewrite HFB in HFceil, HFapp.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 (Hblc _ Hbin) HFin) as DbF.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 (Hblc _ Hhin) HFin) as DhF.
  unfold zdisjoint in DbF, DhF. cbn [fst snd] in DbF, DhF. rewrite EnF, HFB in DbF, DhF.
  change (req_size SRC_FILE_BLOCK) with 1304 in DhF.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hhin) as (_ & _ & _ & Hhapp & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hhapp, HFapp. unfold boxed in Hbapp. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  change (req_size SRC_FILE_BLOCK) with 1304 in Hhapp.
  box DbF. box DhF. box Hhapp. box HFapp. box Hbapp.
  assert (Hnsh : nSH cx fp = shadow_addr (nF cx fp)) by reflexivity.
  (* the bytes of the body are kept *)
  assert (KB : forall a, fa_barea cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. unfold fa_barea in Ha. unfold rread_wrset.
    destruct Ha as [Ha | [Ha | Ha]].
    - apply A1; [lia | rewrite Hspc; lia | unfold rread_wrset, SRC_FILE_BLOCK; lia].
    - apply (A4 NX_CID fp a HFin); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EnF, HFB; lia|].
      unfold boxed in DbF, DhF. unfold rread_wrset, SRC_FILE_BLOCK. lia.
    - apply (A4 NX_CID fp a HFin); [right; unfold in_zr; cbn [fst snd]; rewrite EnF, HFB, <- Hnsh; change (64 / 8) with 8; lia|].
      unfold boxed in Hhapp, Hbapp. rewrite Hnsh in Ha. unfold rread_wrset, shadow_addr, SHADOW_OFF, SRC_FILE_BLOCK in *.
      assert (nF cx fp / 8 * 8 <= nF cx fp) by (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
      assert (0 <= nF cx fp / 8) by (apply Z.div_pos; lia). lia. }
  fbox.
  assert (Q : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 27]%bv ->
    getr regs2 r = getr (ms_regs ms3) r) by (intros r Hr Hin; rewrite (P r Hr); exact (RK r Hin)).
  assert (HFin0 : forall x, In x (frames (n_Sc cx)) -> In x (frames S3)) by (intros x Hx; rewrite HFRS; right; exact Hx).
  assert (Hcin : In (n_cid cx, n_pos cx) (frames S3)) by (apply HFin0; rewrite Hfrs0; apply in_or_app; left; exact Hcown).
  assert (KPS : forall x, n_ps cx <= x < n_ps cx + 24 -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W3) (ms_mem ms3) x).
  { intros x Hx. apply (A4 (n_cid cx) (n_pos cx) x Hcin).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. lia.
    - unfold rread_wrset. unfold boxed in Hpsh, Hbps. unfold SRC_FILE_BLOCK in *. unfold nx_bufn in *. lia. }
  assert (HSB : forall x, 4096 <= x < 2 ^ 47 -> aview SEGS (w_H W2) mem2 (shadow_of_addr SHADOW_OFF x) =
    aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF x)).
  { intros x Hx. apply Hshb. unfold shadow_of_addr, SHADOW_OFF. rewrite C5, C2.
    assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). assert (0 <= x / 8) by (apply Z.div_pos; lia). lia. }
  (* the buffer *)
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 (Hblc _ Hbin)) as (_ & _ & _ & _ & Hbpres & _).
  destruct (fa_garr8_present (w_H W2) mem2 (n_buf cx) (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)
    ltac:(intros i Hi; apply (proj1 (Hbpres (n_buf cx + i) ltac:(lia))))) as (bj2 & Hbj2 & Hbj2l & _).
  assert (Hjr : 0 <= j <= incl) by (rewrite Hj; lia).
  assert (Hpre : firstn (Z.to_nat j) bj2 = firstn (Z.to_nat j) (skipn (Z.to_nat (q + 16)) (n_C cx))).
  { assert (Hl' : length (firstn (Z.to_nat j) (skipn (Z.to_nat (q + 16)) (n_C cx))) = Z.to_nat j)
      by (rewrite length_firstn, length_skipn; lia).
    rewrite <- Hl' at 1. apply (fa_garr8_prefix (rdW W2 mem2) (n_buf cx)); [exact Hbj2 | exact HG2 | rewrite Hl'; lia]. }
  assert (Hbj2l' : length bj2 = length (n_bj cx)) by lia.
  exists q, j.
  split.
  { split.
    { apply (fa_body_keep cx fp NP_fit NP_fit_ra W3 ms3 W2 (mkst regs2 (getr rg 1) mem2 (seg_rom SEGS)) NSH_ph HBD);
        cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst];
        first [ rewrite R1; reflexivity | reflexivity
              | apply Q; [fa_cs | cbn; tauto] | exact KB ]. }
    cbn [ms_regs ms_mem mkst].
    split; [rewrite Q by (try fa_cs; cbn; tauto); exact R24|].
    split; [split; [exact Hk2|]; split; [exact Hbl3|]; split; [exact Hmo|];
            split; [rewrite Hfd2, Hfdq; exact Hfd3 | rewrite Hfs2, Hfsq; exact Hfs3]|].
    split.
    { unfold boxed in HB. apply (fa_kept_call cx ly3 S3 W3 (ms_mem ms3) W2 mem2 (rread_wrset (n_h cx) (n_buf cx) incl)
        HB Hh Hly3 Hbl3 HFin0 HKEPT ltac:(rewrite <- Hspc; exact HK2)).
      intros a Ha. unfold rread_wrset, nx_E, nx_wrset in *. unfold nx_bufn in *. lia. }
    split; [intros a Ha; exact Ha|].
    split; [exact Hh|].
    split.
    { unfold nx_ps_at. destruct HPS as (P1 & P2 & P3 & P4 & P5 & P6 & P7). unfold PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF in *.
      split; [apply (fa_vm_kept W3 W2 (ms_mem ms3) mem2 _ 8 _); [intros x Hx; apply KPS; lia | exact P1]|].
      split; [apply (fa_vm_kept W3 W2 (ms_mem ms3) mem2 _ 4 _); [intros x Hx; apply KPS; lia | exact P2]|].
      split; [apply (fa_vm_kept W3 W2 (ms_mem ms3) mem2 _ 4 _); [intros x Hx; apply KPS; lia | exact P3]|].
      split; [apply (fa_vm_kept W3 W2 (ms_mem ms3) mem2 _ 4 _); [intros x Hx; apply KPS; lia | exact P4]|].
      split; [apply (fa_vm_kept W3 W2 (ms_mem ms3) mem2 _ 2 _); [intros x Hx; apply KPS; lia | exact P5]|].
      split; [apply (fa_garr8_kept W3 W2 (ms_mem ms3) mem2 _ _); [intros x Hx; apply KPS; rewrite P7 in Hx; lia | exact P6]|].
      exact P7. }
    split.
    { apply (PcapSourceCloseSpec.ra_frame (aview SEGS (w_H W3) (ms_mem ms3))); [exact HRAps|]. intros x Hx. apply HSB. unfold PS_LEN in Hx. lia. }
    split; [replace (q + 16 + j) with (q + 16 + rread_k incl (Z.of_nat (length (n_C cx))) (q + 16)) by reflexivity; exact HSRC2|].
    split; [rewrite Hj; lia|].
    split; [exists bj2; split; [exact Hbj2 | exact Hbj2l']|].
    intros Hts. unfold boxed in HTS, HTS0. destruct (HTS Hts) as (Tv & Tra).
    destruct (HTS0 Hh Hts) as (_ & _ & Ht4096 & Ht47 & _ & (tc & tp & Htin & Htf1 & Htf2) & _ & _ & Htps & Htb).
    assert (Htc : In (tc, tp) (frames S3)) by (apply HFin0; rewrite Hfrs0; apply in_or_app; left; exact Htin).
    split.
    - apply (fa_vm_kept W3 W2 (ms_mem ms3) mem2 _ 8 _); [|exact Tv]. intros x Hx.
      apply (A4 tc tp x Htc).
      + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. lia.
      + unfold rread_wrset, SRC_FILE_BLOCK in *. unfold boxed in Htsh. destruct (Htsh Hts) as [Th Tb].
        unfold nx_bufn in *. lia.
    - apply (PcapSourceCloseSpec.ra_frame (aview SEGS (w_H W3) (ms_mem ms3))); [exact Tra|]. intros x Hx. apply HSB. lia. }
  split; [exact Hq|]. split; [exact Hlh|]. split; [exact Hpq|]. split; [lia|]. split; [exact Hincl|].
  split; [exact Hj|].
  split; [exists bj2; split; [exact Hbj2 | split; [exact Hbj2l' | exact Hpre]]|].
  cbn [ms_regs mkst].
  split; [exact Ha0|].
  split; [rewrite Q by (try fa_cs; cbn; tauto); exact R20s|].
  split; [rewrite Q by (try fa_cs; cbn; tauto); exact R21s|].
  split; [rewrite Q by (try fa_cs; cbn; tauto); exact R22s|].
  split; [rewrite Q by (try fa_cs; cbn; tauto); exact R25s|].
  split; [rewrite Q by (try fa_cs; cbn; tauto); exact R27s|].
  split; [rewrite (P 26%bv) by fa_cs; exact R26 | rewrite (P 23%bv) by fa_cs; exact R23].
Qed.


Lemma fa_mem_eq_ro : forall (E : env) (rs : YP09.smem) (m m' : word -> option byte),
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> frame_of E rs m m' -> m' = m.
Proof.
  intros E rs m m' Hro HF. apply functional_extensionality. intros x. apply HF.
  intros (r & Hin & Hr). rewrite Forall_forall in Hro. pose proof (Hro r Hin). lia.
Qed.

Ltac fa_ro := unfold fa_ss1; cbn [ss_mem add_cond setpc YP09.r_wlo YP09.r_whi]; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil.

Lemma fa_pre : nx_from SK B KS (nx_post SK B MT KS) nx_fitra_inv ->
  nx_from SK B KS (nx_post SK B MT KS) (nx_fit_inv B MT KS).
Proof.
  intros NEXT cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFRS GI.
  pose proof GI as GI'.
  destruct GI' as (q & HM & Hq & Hlh & Hpq & Hincl & R10 & R12 & R6 & R17 & R5 & R11 & R16 & R14 & R15
    & R20 & R21 & R22 & R23 & R25 & R27).
  destruct (fa_seat1 cx fp k2 ly3 S3 W3 ms3 md3 HB HJ GI) as [HS SHOK].
  remember (Eimg (Ereg (ms_regs ms3) (fa_extra (n_ts cx) (n_h cx)))) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (R0 : forall r, getr (ms_regs ms3) r = sv_denot E (sr_get fa_sr r))
    by (intros r; exact (st_ok_pi_restrict_reg (w_H W3) E fa_ss1 ms3 r HS)).
  assert (ER : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hr. subst E. rewrite Eimg_low by (pose proof (u5_range r); unfold A_TEXT; lia).
    exact (ew_Ereg_nat _ _ n r Hr). }
  set (sw := n_sw cx =? 1) in *. set (F := nxF (n_C cx)) in *.
  assert (FB : forall i, 0 <= PSN.fb F i < 256).
  { intros i. unfold PSN.fb. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) F (Z_to_bv 8 0))) as Hr.
    unfold bv_modulus in Hr. change (2 ^ Z.of_N 8) with 256 in Hr. exact Hr. }
  assert (UB : forall (n : nat) (r : bv 5) i, Z.of_nat n = bv_unsigned r ->
    getr (ms_regs ms3) r = w64 (PSN.fb F i) -> U E (SOff n 0) = PSN.fb F i).
  { intros n r i Hn Hr. apply U_atom; [rewrite (ER n r Hn), Hr; reflexivity | pose proof (FB i); lia]. }
  pose proof (UB 12%nat (12%bv : bv 5) q eq_refl R12) as U12.
  pose proof (UB 6%nat (6%bv : bv 5) (q + 1) eq_refl R6) as U6.
  pose proof (UB 17%nat (17%bv : bv 5) (q + 2) eq_refl R17) as U17.
  pose proof (UB 5%nat (5%bv : bv 5) (q + 3) eq_refl R5) as U5.
  pose proof (UB 11%nat (11%bv : bv 5) (q + 4) eq_refl R11) as U11.
  pose proof (UB 16%nat (16%bv : bv 5) (q + 5) eq_refl R16) as U16.
  pose proof (UB 14%nat (14%bv : bv 5) (q + 6) eq_refl R14) as U14.
  pose proof (UB 15%nat (15%bv : bv 5) (q + 7) eq_refl R15) as U15.
  pose proof (FB q) as B0. pose proof (FB (q + 1)) as B1. pose proof (FB (q + 2)) as B2. pose proof (FB (q + 3)) as B3.
  pose proof (FB (q + 4)) as B4. pose proof (FB (q + 5)) as B5. pose proof (FB (q + 6)) as B6. pose proof (FB (q + 7)) as B7.
  assert (HW0 : forall b, PSN.hw b F q 0 =
    if b then PSN.w32le (PSN.fb F (q + 3)) (PSN.fb F (q + 2)) (PSN.fb F (q + 1)) (PSN.fb F q)
    else PSN.w32le (PSN.fb F q) (PSN.fb F (q + 1)) (PSN.fb F (q + 2)) (PSN.fb F (q + 3))).
  { intros b. unfold PSN.hw. rewrite !Z.add_0_r. reflexivity. }
  assert (HW4 : forall b, PSN.hw b F q 4 =
    if b then PSN.w32le (PSN.fb F (q + 7)) (PSN.fb F (q + 6)) (PSN.fb F (q + 5)) (PSN.fb F (q + 4))
    else PSN.w32le (PSN.fb F (q + 4)) (PSN.fb F (q + 5)) (PSN.fb F (q + 6)) (PSN.fb F (q + 7))).
  { intros b. unfold PSN.hw. replace (q + 4 + 1) with (q + 5) by lia. replace (q + 4 + 2) with (q + 6) by lia.
    replace (q + 4 + 3) with (q + 7) by lia. reflexivity. }
  assert (W32 : forall x0 x1 x2 x3, 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
    PSN.w32le x0 x1 x2 x3 mod 2 ^ 32 = PSN.w32le x0 x1 x2 x3).
  { intros x0 x1 x2 x3 Hx0 Hx1 Hx2 Hx3. apply Z.mod_small. unfold PSN.w32le. lia. }
  assert (Hsw01 : n_sw cx = 0 \/ n_sw cx = 1).
  { destruct HM as (_ & _ & _ & _ & _ & Hh & _). pose proof HB as HB'. fa_base HB'. exact (Hsw Hh). }
  assert (Usw : U E (SOff 10 0) = n_sw cx).
  { apply U_atom; [rewrite (ER 10%nat (10%bv : bv 5) eq_refl), R10; reflexivity | lia]. }

  assert (E34 : ew E 34 = Z_to_bv 64 (n_h cx)).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra _ _ 2). }
  paj_run_tok RUN HS HJ SHOK fa_span;
    [ repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil |].
  pose proof HF as Em1. apply fa_mem_eq_ro in Em1; [|fa_ro].
  psrr_branch_tok RUN BR HS SHOK fa_span.
  - rewrite branch_eq_U, Usw, U_lit in Hc by lia. apply Z.eqb_eq in Hc.
    assert (Esw : sw = false) by (unfold sw; rewrite Hc; reflexivity).
    paj_run_tok RUN HS HJ SHOK fa_span;
      [ repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil |].
    pose proof HF0 as Em2. apply fa_mem_eq_ro in Em2; [|fa_ro].
    rewrite Em1 in Em2. pmkst HS. rewrite Em2 in HJ |- *.
    assert (RK : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 27]%bv ->
      getr (ms_regs ms0) r = getr (ms_regs ms3) r).
    { intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W3) E _ ms0 r HS), R0. f_equal.
      repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
    assert (Q26 : bv_unsigned (getr (ms_regs ms0) 26) =
      U E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 6 0) (SLit 8)) (SOff 12 0))
            (SAlu ALU_OR (SAlu ALU_SLL (SOff 17 0) (SLit 16)) (SAlu ALU_SLL (SOff 5 0) (SLit 24))))).
    { unfold U. rewrite (st_ok_restrict_reg SEGS (w_H W3) E _ ms0 26%bv HS). do 2 f_equal; try (vm_compute; reflexivity). }
    assert (Q23 : bv_unsigned (getr (ms_regs ms0) 23) =
      U E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 16 0) (SLit 8)) (SOff 11 0))
            (SAlu ALU_OR (SAlu ALU_SLL (SOff 14 0) (SLit 16)) (SAlu ALU_SLL (SOff 15 0) (SLit 24))))).
    { unfold U. rewrite (st_ok_restrict_reg SEGS (w_H W3) E _ ms0 23%bv HS). do 2 f_equal; try (vm_compute; reflexivity). }
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
    prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
    apply (fa_call cx fp k2 ly3 S3 W3 ms3 md3 (ms_regs ms0) _ q NEXT HB HJ HFRS HM Hq Hlh Hpq Hincl).
    + reflexivity.
    + reflexivity.
    + exact Q1.
    + rewrite Q10, (ER 20%nat (20%bv : bv 5) eq_refl). exact R20.
    + exact Q11.
    + rewrite Q12, (ER 27%nat (27%bv : bv 5) eq_refl). exact R27.
    + rewrite Q13. exact E34.
    + exact RK.
    + rewrite Q26, (PcapSourceNextFitABits.fa_ts_noswap E (SOff 12 0) (SOff 6 0) (SOff 17 0) (SOff 5 0) _ _ _ _ U12 U6 U17 U5 B0 B1 B2 B3).
      rewrite W32 by assumption. rewrite HW0. fold sw. rewrite Esw. reflexivity.
    + rewrite Q23, (PcapSourceNextFitABits.fa_ts_noswap E (SOff 11 0) (SOff 16 0) (SOff 14 0) (SOff 15 0) _ _ _ _ U11 U16 U14 U15 B4 B5 B6 B7).
      rewrite W32 by assumption. rewrite HW4. fold sw. rewrite Esw. reflexivity.
    + exact R20.
    + exact R21.
    + exact R22.
    + exact R25.
    + exact R27.
  - rewrite branch_eq_U, Usw, U_lit in Hc by lia. apply Z.eqb_neq in Hc.
    assert (Esw : sw = true) by (unfold sw; destruct Hsw01 as [H0'|H1']; [lia | rewrite H1'; reflexivity]).
    paj_run_tok RUN HS HJ SHOK fa_span;
      [ repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil |].
    pose proof HF0 as Em2. apply fa_mem_eq_ro in Em2; [|fa_ro].
    rewrite Em1 in Em2. pmkst HS. rewrite Em2 in HJ |- *.
    assert (RK : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 27]%bv ->
      getr (ms_regs ms0) r = getr (ms_regs ms3) r).
    { intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W3) E _ ms0 r HS), R0. f_equal.
      repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
    assert (Q26 : bv_unsigned (getr (ms_regs ms0) 26) = U E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 12 0) (SLit 24)) (SAlu ALU_SLL (SAlu ALU_AND (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 6 0) (SLit 8)) (SOff 12 0)) (SAlu ALU_OR (SAlu ALU_SLL (SOff 17 0) (SLit 16)) (SAlu ALU_SLL (SOff 5 0) (SLit 24)))) (SLit 65280)) (SLit 8))) (SAlu ALU_OR (SAlu ALU_SLL (SOff 17 0) (SLit 8)) (SAluw ALU_SRL (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 6 0) (SLit 8)) (SOff 12 0)) (SAlu ALU_OR (SAlu ALU_SLL (SOff 17 0) (SLit 16)) (SAlu ALU_SLL (SOff 5 0) (SLit 24)))) (SLit 24))))).
    { unfold U. rewrite (st_ok_restrict_reg SEGS (w_H W3) E _ ms0 26%bv HS). do 2 f_equal; try (vm_compute; reflexivity). }
    assert (Q23 : bv_unsigned (getr (ms_regs ms0) 23) = U E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 11 0) (SLit 24)) (SAlu ALU_SLL (SAlu ALU_AND (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 16 0) (SLit 8)) (SOff 11 0)) (SAlu ALU_OR (SAlu ALU_SLL (SOff 14 0) (SLit 16)) (SAlu ALU_SLL (SOff 15 0) (SLit 24)))) (SLit 65280)) (SLit 8))) (SAlu ALU_OR (SAlu ALU_SLL (SOff 14 0) (SLit 8)) (SAluw ALU_SRL (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 16 0) (SLit 8)) (SOff 11 0)) (SAlu ALU_OR (SAlu ALU_SLL (SOff 14 0) (SLit 16)) (SAlu ALU_SLL (SOff 15 0) (SLit 24)))) (SLit 24))))).
    { unfold U. rewrite (st_ok_restrict_reg SEGS (w_H W3) E _ ms0 23%bv HS). do 2 f_equal; try (vm_compute; reflexivity). }
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
    prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
    apply (fa_call cx fp k2 ly3 S3 W3 ms3 md3 (ms_regs ms0) _ q NEXT HB HJ HFRS HM Hq Hlh Hpq Hincl).
    + reflexivity.
    + reflexivity.
    + exact Q1.
    + rewrite Q10, (ER 20%nat (20%bv : bv 5) eq_refl). exact R20.
    + exact Q11.
    + rewrite Q12, (ER 27%nat (27%bv : bv 5) eq_refl). exact R27.
    + rewrite Q13. exact E34.
    + exact RK.
    + rewrite Q26, (PcapSourceNextFitABits.fa_ts_swap E (SOff 12 0) (SOff 6 0) (SOff 17 0) (SOff 5 0) _ _ _ _ U12 U6 U17 U5 B0 B1 B2 B3).
      rewrite HW0. fold sw. rewrite Esw. reflexivity.
    + rewrite Q23, (PcapSourceNextFitABits.fa_ts_swap E (SOff 11 0) (SOff 16 0) (SOff 14 0) (SOff 15 0) _ _ _ _ U11 U16 U14 U15 B4 B5 B6 B7).
      rewrite HW4. fold sw. rewrite Esw. reflexivity.
    + exact R20.
    + exact R21.
    + exact R22.
    + exact R25.
    + exact R27.
Qed.
End w.

(* ---------------------------------------------------------------------------------------------- *)
(* From NP_fit_ra: the short record to NP_exit, the full one through ps->vtag / ps->vid, the        *)
(* `bltu s9,18` and the 0x81 / 0x00 tag test to NP_ts, or through __asan_memmove (fa_mm_call)       *)
(* ---------------------------------------------------------------------------------------------- *)

Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Notation VAL := (@pa_val _ pcap_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Notation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.

Definition fb_ps_r (wlo whi : Z) : YP09.region :=
  YP09.mkRegion (Some 21%nat) 0 24 wlo whi [YP09.mkChunk 0 (CVal 8 (SOff 34 0))].
Definition fb_G2 : facts := mkFacts
  [(10%nat, mkAF 0 2040 0); (25%nat, mkAF 1 2040 0); (27%nat, mkAF 1 2040 0);
   (35%nat, fa_byte_af); (36%nat, fa_byte_af); (37%nat, fa_byte_af); (38%nat, fa_byte_af);
   (21%nat, mkAF 4096 (2 ^ 47 - 24) 3); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition fb_ss2 (wlo whi : Z) : sstate := mkSS NP_fit_ra fa_sr [fa_spill_r; fb_ps_r wlo whi] None fb_G2.
Definition fb_buf_r : YP09.region :=
  YP09.mkRegion (Some 20%nat) 0 16 0 0 [YP09.mkChunk 12 (CVal 1 (SOff 35 0)); YP09.mkChunk 13 (CVal 1 (SOff 36 0));
    YP09.mkChunk 14 (CVal 1 (SOff 37 0)); YP09.mkChunk 15 (CVal 1 (SOff 38 0))].
Definition fb_SH2 : list shent := [mkSHE 21 0 24; mkSHE 20 12 16].
Definition fb_extra (ts h b12 b13 b14 b15 : Z) : list word := map (Z_to_bv 64) [SHADOW_OFF; ts; h; b12; b13; b14; b15].

Lemma fb_ps_wf : forall wlo whi, (forall o, wlo <= o < whi -> 16 <= o < 22) -> region_wf (fb_ps_r wlo whi) = true.
Proof.
  intros wlo whi Hw. unfold region_wf, fb_ps_r. cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  destruct (Z.leb_spec whi wlo) as [H|H].
  - reflexivity.
  - pose proof (Hw wlo ltac:(lia)). pose proof (Hw (whi - 1) ltac:(lia)).
    rewrite (proj2 (Z.leb_le 0 wlo)) by lia. rewrite (proj2 (Z.leb_le whi 24)) by lia. reflexivity.
Qed.

Lemma fb_seat2 : forall cx fp k2 ly3 S3 W3 ms3 md3 Eq ol vt vid tv kk incl b12 b13 b14 b15 wlo whi,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  nx_mid B MT KS cx fp NP_fit_ra NSH_ph (nx_E cx) Eq ol vt vid tv k2 ly3 S3 W3 ms3 md3 ->
  getr (ms_regs ms3) 10 = w64 kk -> 0 <= kk <= 2040 ->
  getr (ms_regs ms3) 25 = w64 incl -> getr (ms_regs ms3) 27 = w64 incl -> 1 <= incl <= 2040 ->
  getr (ms_regs ms3) 21 = w64 (n_ps cx) ->
  0 <= b12 < 256 -> 0 <= b13 < 256 -> 0 <= b14 < 256 -> 0 <= b15 < 256 ->
  (forall o, wlo <= o < whi -> 16 <= o < 22) ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) (fb_extra (n_ts cx) (n_h cx) b12 b13 b14 b15)))
    (fb_ss2 wlo whi) (restrict (w_H W3) ms3) /\
  sh_ok SEGS fa_SB fa_SH (Eimg (Ereg (ms_regs ms3) (fb_extra (n_ts cx) (n_h cx) b12 b13 b14 b15))) (rdW W3 (ms_mem ms3)).
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 Eq ol vt vid tv kk incl b12 b13 b14 b15 wlo whi HB HJ HM
    R10 Hkk R25 R27 Hincl R21 Hb12 Hb13 Hb14 Hb15 Hwin.
  destruct HM as (HBD & R24 & HJB & HKEPT & HEsub & Hh & HPS & HRAps & HSRC & Hqr & HBUF & HTS).
  pose proof HBD as (HB0 & HSL).
  pose proof HB0 as (Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & HREGS & HSAV & HHDR & HFLW & HSHW & Hlen & R18 & R19 & HF0).
  pose proof HREGS as (R2 & R8 & R9 & R3 & R4).
  pose proof HSL as (S_F0 & S_FK & S_TS & S_SB & _).
  fa_base HB.
  unfold PS_LEN in Hps47, Hcfa2.
  pose proof (HWRps Hh) as HWRp.
  assert (Hts64 : 0 <= n_ts cx < 2 ^ 64).
  { destruct (Z.eq_dec (n_ts cx) 0) as [->|Hts0]; [lia|]. destruct (HTS0 Hh Hts0) as (_ & _ & Hts4096 & Hts47 & _). lia. }
  fbox.
  pose proof HJ0 as (HAR0 & Hly0 & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hcin : In (n_cid cx, n_pos cx) (frames (n_Sc cx))) by (rewrite Hfrs0; apply in_or_app; left; exact Hcown).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR0 Hcin) as (Hf4096 & Hfceil & Hfapp).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
  assert (HSP1 : n_sp1 cx = 32 * ((spZ (n_regs cx) - NX_MFRAME) / 32)) by reflexivity.
  assert (Hsp1lo : spZ (n_regs cx) - 256 <= n_sp1 cx <= spZ (n_regs cx) - 224).
  { rewrite HSP1. unfold NX_MFRAME. pose proof (Z.mod_pos_bound (spZ (n_regs cx) - 224) 32 ltac:(lia)).
    pose proof (Z_div_mod_eq_full (spZ (n_regs cx) - 224) 32). lia. }
  assert (HNX : NX_STK = 8496) by reflexivity.
  set (E := Eimg (Ereg (ms_regs ms3) (fb_extra (n_ts cx) (n_h cx) b12 b13 b14 b15))).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) (fb_extra (n_ts cx) (n_h cx) b12 b13 b14 b15)) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (ER : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
    by (intros n r Hr; rewrite EL by (pose proof (u5_range r); unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ n r Hr)).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (n_ts cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (n_h cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 b12) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 3)).
  assert (E36 : ew E 36 = Z_to_bv 64 b13) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 4)).
  assert (E37 : ew E 37 = Z_to_bv 64 b14) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 5)).
  assert (E38 : ew E 38 = Z_to_bv 64 b15) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 6)).
  assert (E21 : ew E 21 = Z_to_bv 64 (n_ps cx)) by (rewrite (ER 21%nat (21%bv : bv 5) eq_refl); exact R21).
  assert (E9 : ew E 9 = Z_to_bv 64 (n_sp1 cx)) by (rewrite (ER 9%nat (9%bv : bv 5) eq_refl); exact R9).
  assert (E10 : ew E 10 = Z_to_bv 64 kk) by (rewrite (ER 10%nat (10%bv : bv 5) eq_refl); exact R10).
  assert (E25 : ew E 25 = Z_to_bv 64 incl) by (rewrite (ER 25%nat (25%bv : bv 5) eq_refl); exact R25).
  assert (E27 : ew E 27 = Z_to_bv 64 incl) by (rewrite (ER 27%nat (27%bv : bv 5) eq_refl); exact R27).
  assert (Hsp1r : 0 <= n_sp1 cx /\ n_sp1 cx + 120 <= 2 ^ 47) by lia.
  assert (Ups : U E (SOff 21 0) = n_ps cx) by (apply U_atom; [exact E21 | lia]).
  assert (USB : U E fa_SB = SHADOW_OFF) by (apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
  split.
  - rewrite (fa_ms_eq _ _ _ _ _ _ HB0). unfold fb_ss2. apply pa_entry_st_ok_full.
    + apply fa_regs_ok_set; [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity |].
      rewrite R24, (denot_lit_U E fa_sh8). f_equal. unfold fa_sh8.
      rewrite U_SAlu, U_SAlu, Ups, USB, U_lit by lia. cbn [zalu_raw]. change (Z.land 3 63) with 3.
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      unfold zcanon, M64, shadow_of_addr, SHADOW_OFF.
      assert (0 <= n_ps cx / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      rewrite (Z.mod_small (n_ps cx / 8)) by lia. rewrite Z.mod_small by lia. lia.
    + cbn [regions_wf]. rewrite (fb_ps_wf wlo whi Hwin). reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * unfold region_ok, fa_spill_r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E9, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 33 0) (n_ts cx));
             [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
           exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S_TS).
        -- apply (chunk_ok_val SEGS E _ _ 40 8 fa_SB SHADOW_OFF);
             [unfold fa_SB; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | unfold SHADOW_OFF; zside | zside |].
           exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S_SB).
      * unfold region_ok, fb_ps_r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E21, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|].
        split.
        { intros o Ho. pose proof (Hwin o Ho) as Ho'. cbn [ms_mem restrict]. apply apresent_writable.
          destruct (HWRp (n_ps cx + o) ltac:(unfold PS_LEN; lia)) as [Hw _].
          apply (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
          assert (Hblc : forall x, In x (ablocks B (n_lyc cx) (n_Sc cx)) -> In x (ablocks B ly3 S3))
            by (intros x Hx; pose proof HJB as (_ & Hbl3 & _); rewrite Hbl3; exact Hx).
          assert (Hown3 : forall x, In x (n_own cx) -> In x ((NX_CID, fp) :: n_own cx)) by (intros x Hx; right; exact Hx).
          assert (EF : forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p).
          { intros c p. pose proof HJ as (_ & Hly3 & _).
            rewrite (frame_addr_layout_le _ _ _ Hly3), (frame_addr_layout_le _ _ _ Hly0). reflexivity. }
          exact (awr_byte_weaken _ _ _ _ _ _ _ _ _ _ _ Hblc Hown3 EF Hw). }
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 34 0) (n_h cx));
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        destruct HPS as (Hpf & _). rewrite Z.add_0_r. unfold PS_F_OFF in Hpf. rewrite Z.add_0_r in Hpf. exact Hpf.
    + unfold fa_spill_r, fb_ps_r. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E21, !unsigned_lit_small by lia.
      split; [split; [right; lia | exact I] | split; exact I].
    + split; [|split; exact I]. unfold fb_G2, fa_byte_af. cbn [f_atoms atoms_ok]. unfold afact_ok.
      cbn [af_lo af_hi af_al2].
      rewrite E10, E25, E27, E35, E36, E37, E38, E21, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; first [exact I | unfold SHADOW_OFF; lia].
  - unfold sh_ok, fa_SH. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart.
    cbn [she_m she_lo she_hi]. rewrite USB, Ups. split.
    + rewrite Z.add_0_r, <- (aview_rd_of SEGS). exact HRAps.
    + intros a Ha. unfold SHADOW_OFF, PS_LEN in *. cbn in Ha. lia.
Qed.

Lemma fb_src_bytes : forall m f b C p, asource_at SEGS KS m f b C p -> bytes_ok C.
Proof. intros m f b C p (W & cpos & fl & md & _ & _ & _ & _ & _ & _ & _ & HC & _). exact HC. Qed.

Lemma fb_wb_md : forall l mat (md : Model), m_fds (with_vm_backing l mat md) = m_fds md /\
  m_fs (with_vm_backing l mat md) = m_fs md.
Proof. intros l mat md. destruct md as [f [mp lz mt] io fs pr li ti sg sc]. split; reflexivity. Qed.

Lemma fb_jbk : forall cx k2 ly3 S3 md3 md4, nx_jbk B MT cx k2 ly3 S3 md3 ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 -> nx_jbk B MT cx k2 ly3 S3 md4.
Proof. intros cx k2 ly3 S3 md3 md4 (H1 & H2 & H3 & H4 & H5) E1 E2. repeat split; congruence. Qed.

Lemma fb_body_at : forall cx fp pc pc' W3 ms3 ms sh E ss extra,
  nx_body cx fp pc W3 ms3 sh ->
  E = Eimg (Ereg (ms_regs ms3) extra) ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms) -> ss_resv ss = None -> ss_pc ss = pc' ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19]%bv -> sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0) ->
  (forall a, fa_barea cx fp a -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  nx_body cx fp pc' W3 ms sh.
Proof.
  intros cx fp pc pc' W3 ms3 ms sh E ss extra HBD HE HS Hrv Hpc Hsr HK.
  assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19]%bv -> getr (ms_regs ms) r = getr (ms_regs ms3) r).
  { intros r Hr. rewrite (st_ok_pi_restrict_reg (w_H W3) E ss ms r HS), (Hsr r Hr). cbn [sv_denot]. subst E.
    rewrite (ew_Eimg_Ereg_nat _ _ _ r) by (pose proof (u5_range r); lia).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  rewrite (st_ok_pi_restrict_mkst (w_H W3) E ss ms HS Hrv).
  apply (fa_body_keep cx fp pc pc' W3 ms3 W3 _ sh HBD);
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst];
    try reflexivity.
  - rewrite Hpc. reflexivity.
  - apply RG. cbn; tauto.
  - apply RG. cbn; tauto.
  - apply RG. cbn; tauto.
  - apply RG. cbn; tauto.
  - apply RG. cbn; tauto.
  - apply RG. cbn; tauto.
  - apply RG. cbn; tauto.
  - exact HK.
Qed.

Lemma fb_nth_byte : forall (m : word -> option byte) a l j, garr8 SEGS m a l -> 0 <= nth j l 0 < 256.
Proof.
  intros m a l j Hg. destruct (Nat.lt_ge_cases j (length l)) as [Hj|Hj].
  - exact (proj2 (Hg j Hj)).
  - rewrite nth_overflow by exact Hj. lia.
Qed.

Hypothesis AFREAD : afread_spec SK SEGS B KS (SIGMA PS___interceptor_trampoline_fread).
Let RUN := paj_run (PL := PL_pcap) B LAWS.
Let RUNTO := paj_run_to (PL := PL_pcap) B LAWS.
Let BR := paj_branch (PI := PI).

Hypothesis ASIL : asource_img_laws SK SEGS B KS.
Let LAND := fa_land_ts B MT KS LAWS ASIL.

Hypothesis AMM : amemmove_realizes SEGS B (SIGMA PS___asan_memmove).
(* a Theorem Labs lane's call transport across __asan_memmove (PcapSourceNextFitACall.v). *)
Let MMC := fa_mm_call B MT KS LAWS ASIL AMM.

Lemma fb_aview_frame : forall E rs H (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' a HF Ha Hn. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.

Lemma fb_nwr : forall E rs ps a,
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r \/
    (YP09.r_base r = Some 21%nat /\ YP09.r_wlo r = 16 /\ YP09.r_whi r = 22)) rs ->
  bv_unsigned (ew E 21) = ps -> ~ (ps + 16 <= a < ps + 22) -> ~ in_wrange E rs a.
Proof.
  intros E rs ps a HF Hps Ha (r & Hin & Hr). rewrite Forall_forall in HF.
  destruct (HF r Hin) as [Hw | (Hb & Hlo & Hhi)]; [lia|].
  rewrite Hb, Hlo, Hhi in Hr. cbn [base_val] in Hr. rewrite Hps in Hr. lia.
Qed.
Ltac fb_rs := repeat (apply Forall_cons; [first [left; cbn; lia | right; split; [reflexivity | split; reflexivity]] |]);
  apply Forall_nil.

Lemma fb_reg_eq : forall E E' ss ss0 ms ms3 H (r : bv 5),
  st_ok_pi SEGS VAL E' ss (restrict H ms) -> st_ok_pi SEGS VAL E ss0 (restrict H ms3) ->
  env_agree 512 E E' -> sv_atoms_lt 512 (sr_get (ss_regs ss0) r) = true ->
  sr_get (ss_regs ss) r = sr_get (ss_regs ss0) r -> getr (ms_regs ms) r = getr (ms_regs ms3) r.
Proof.
  intros E E' ss ss0 ms ms3 H r HS HS0 HA Hat Heq.
  rewrite (st_ok_pi_restrict_reg H E' ss ms r HS), (st_ok_pi_restrict_reg H E ss0 ms3 r HS0), Heq.
  exact (sv_denot_agree 512 E E' _ HA Hat).
Qed.
Ltac fb_agree := split; [intros ? ?; rewrite ?ew_ewset_other by lia;
  try (match goal with EE : forall n, (n < 512)%nat -> ew _ n = ew _ n |- _ => rewrite EE by lia end); reflexivity | reflexivity].


Lemma fb_land_u : forall cx fp k2 ly3 S3 W3 ms3 md3 ms4 md4 q bj',
  let sw := n_sw cx =? 1 in let F := nxF (n_C cx) in let incl := PSN.incl sw F q in
  nx_from SK B KS (nx_post SK B MT KS) (nx_ts_inv B MT KS) ->
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms4) md4 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  nx_mid B MT KS cx fp NP_fit_ra NSH_ph (nx_E cx) (q + 16 + incl) (PSN.orig sw F q) (n_lvt cx) (n_lvid cx)
    (n_tsv cx) k2 ly3 S3 W3 ms3 md3 ->
  nx_q sw (n_C cx) (n_cap cx) (n_p cx) = q -> nx_lh sw (n_C cx) (n_cap cx) (n_p cx) = Some q -> n_p cx <= q ->
  0 < incl <= n_cap cx -> q + 16 + incl <= Z.of_nat (length (n_C cx)) -> 0 <= q ->
  garr8 SEGS (rdW W3 (ms_mem ms3)) (n_buf cx) bj' -> length bj' = length (n_bj cx) ->
  firstn (Z.to_nat incl) bj' = firstn (Z.to_nat incl) (skipn (Z.to_nat (q + 16)) (n_C cx)) ->
  PSN.tagged sw F q = false ->
  ms4 = mkst (ms_regs ms4) (Z_to_bv 64 (BASE + NP_ts)) (ms_mem ms4) (seg_rom SEGS) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26; 23]%bv -> getr (ms_regs ms4) r = getr (ms_regs ms3) r) ->
  getr (ms_regs ms3) 25 = w64 incl ->
  bv_unsigned (getr (ms_regs ms3) 26) mod 2 ^ 32 = PSN.hw sw F q 0 ->
  bv_unsigned (getr (ms_regs ms3) 23) mod 2 ^ 32 = PSN.hw sw F q 4 ->
  getr (ms_regs ms4) 21 = w64 (n_ts cx) ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (n_ps cx + 16 <= a < n_ps cx + 22) ->
     aview SEGS (w_H W3) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms4) a) ->
  val_mem SEGS (rdW W3 (ms_mem ms4)) (n_ps cx + 16) 4 0 ->
  val_mem SEGS (rdW W3 (ms_mem ms4)) (n_ps cx + 20) 2 0 ->
  SRr SEGS W3 (mkCfg ms4 md4) (nx_post SK B MT KS cx).
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 ms4 md4 q bj' sw F incl NTS HB HJ HFRS HM Hq Hlh Hpq Hincl Hfit Hq0
    Hbj Hbjl Hbjp Htag Hms RG R25 R26 R23 R21 Hfd Hfs KM HGR Vt Vid.
  pose proof HM as (HBD & R24 & HJB & HKEPT & HEsub & Hh & HPS & HRAps & HSRC & Hqr & HBUF & HTS).
  pose proof (fb_src_bytes _ _ _ _ _ HSRC) as HCb.
  pose proof HB as HB'. fa_base HB'. destruct (HBUF0 Hh) as (Hbin & Hb4096 & Hbn63 & _ & _ & Hcap & _ & Hbps).
  unfold PS_LEN in *. fbox.
  eapply NTS; [exact HB | exact HJ | exact HFRS |].
  apply (LAND cx fp k2 ly3 S3 W3 ms3 md3 ms4 md4 q bj' HB HJ HFRS HM Hq Hlh Hpq Hincl Hfit);
    try (rewrite Hms; reflexivity).
  all: try change (n_sw cx =? 1) with sw. all: try change (nxF (n_C cx)) with F.
  all: try change (PSN.incl sw F q) with incl.
  - intros r Hr. apply RG. cbn in Hr |- *. tauto.
  - exact R21.
  - rewrite (RG 25%bv) by (cbn; tauto). rewrite R25. unfold PSN.rec_len. rewrite Htag.
    try change (PSN.incl sw F q) with incl. unfold w64. unfold NX_CAP_MAX in Hcap.
    rewrite unsigned_lit_small by lia. apply Z.mod_small. lia.
  - rewrite (RG 26%bv) by (cbn; tauto). exact R26.
  - rewrite (RG 23%bv) by (cbn; tauto). exact R23.
  - exact Hfd.
  - exact Hfs.
  - intros a Ha Hn _ _. exact (KM a Ha Hn).
  - exact HGR.
  - rewrite Htag. exact Vt.
  - rewrite Htag. exact Vid.
  - apply (fa_garr8_kept W3 W3 (ms_mem ms3) (ms_mem ms4) _ _); [| exact Hbj].
    intros x Hx. rewrite Hbjl in Hx. unfold boxed in HBUF0. destruct (HBUF0 Hh) as (_ & _ & _ & _ & Hbl & _). apply KM; [lia|].
    unfold boxed in Hbps. unfold nx_bufn in *. lia.
  - exact Hbjl.
  - rewrite (fa_rec_untagged sw (n_C cx) (n_cap cx) (n_p cx) q HCb Hq Htag).
    unfold fa_raw. rewrite length_firstn, length_skipn. change (PSN.incl sw (nxF (n_C cx)) q) with incl.
    rewrite Nat.min_l by lia. exact Hbjp.
Qed.


Lemma fb_tag_byte : forall (C bj : list Z) q incl j, bytes_ok C -> 0 <= q -> 0 <= j < incl ->
  firstn (Z.to_nat incl) bj = firstn (Z.to_nat incl) (skipn (Z.to_nat (q + 16)) C) ->
  nth (Z.to_nat j) bj 0 = PSN.fb (nxF C) (q + 16 + j).
Proof.
  intros C bj q incl j HC Hq Hj Hp. rewrite (fa_fb C _ HC).
  transitivity (nth (Z.to_nat j) (firstn (Z.to_nat incl) bj) 0).
  - rewrite nth_firstn. destruct (Nat.ltb_spec (Z.to_nat j) (Z.to_nat incl)); [reflexivity | lia].
  - rewrite Hp, nth_firstn. destruct (Nat.ltb_spec (Z.to_nat j) (Z.to_nat incl)); [| lia].
    rewrite nth_skipn. f_equal. lia.
Qed.

Lemma fb_atom_reg : forall Ex E ss ms H (r : bv 5) (n : nat) v,
  st_ok_pi SEGS VAL Ex ss (restrict H ms) -> env_agree 512 E Ex -> (n < 512)%nat ->
  sr_get (ss_regs ss) r = SOff n 0 -> ew E n = Z_to_bv 64 v -> getr (ms_regs ms) r = w64 v.
Proof.
  intros Ex E ss ms H r n v HS HA Hn Hsr Hv. rewrite (st_ok_pi_restrict_reg H Ex ss ms r HS), Hsr. cbn [sv_denot].
  rewrite (proj1 HA n Hn), Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.


Lemma fb_a2 : forall E v, U E (SOff 25 0) = v -> 18 <= v <= 2040 ->
  U E (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 25 0) (SLit 32)) (SLit (-68719476736))) (SLit 32)) = v - 16.
Proof.
  intros E v Hv Hr. rewrite !U_SAlu, !U_SLit, Hv. cbn [zalu_raw].
  rewrite (zcanon_id 32) by (unfold M64; lia). change (Z.land 32 63) with 32.
  unfold zcanon, M64. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (v * 2 ^ 32)) by lia.
  change ((-68719476736) mod 2 ^ 64) with 18446744004990074880.
  rewrite <- (Z.mod_unique (v * 2 ^ 32 + 18446744004990074880) (2 ^ 64) 1 ((v - 16) * 2 ^ 32)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. apply Z.mod_small. lia.
Qed.

Lemma fb_vid : forall E b14 b15, U E (SOff 37 0) = b14 -> U E (SOff 38 0) = b15 -> 0 <= b14 < 256 -> 0 <= b15 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_AND (SAlu ALU_SLL (SOff 37 0) (SLit 8)) (SLit 3840)) (SOff 38 0)) = (256 * b14 + b15) mod 4096.
Proof.
  intros E b14 b15 H14 H15 R14 R15. rewrite !U_SAlu, !U_SLit, H14, H15. cbn [zalu_raw].
  rewrite (zcanon_id 8) by (unfold M64; lia). rewrite (zcanon_id 3840) by (unfold M64; lia).
  change (Z.land 8 63) with 8.
  rewrite Z.shiftl_mul_pow2 by lia. unfold zcanon, M64. rewrite (Z.mod_small (b14 * 2 ^ 8)) by lia.
  assert (HA : Z.land (b14 * 2 ^ 8) 3840 = (b14 mod 16) * 256).
  { change 3840 with (Z.shiftl 15 8). rewrite <- Z.shiftl_mul_pow2 by lia. rewrite <- Z.shiftl_land.
    change 15 with (Z.ones 4). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
  rewrite HA. pose proof (Z.mod_pos_bound b14 16 ltac:(lia)).
  rewrite (Z.mod_small (b14 mod 16 * 256)) by lia.
  rewrite Z.lor_comm, (PcapSourceNextWords.nx_lor_add b15 (b14 mod 16 * 256) 8) by (try lia; rewrite Z_mod_mult; reflexivity).
  rewrite (Z.mod_small (b15 + b14 mod 16 * 256)) by lia.
  apply (Z.mod_unique (256 * b14 + b15) 4096 (b14 / 16)); [lia|].
  pose proof (Z_div_mod_eq_full b14 16). lia.
Qed.


Lemma fb_reg_eq_ok : forall E E' ss ss0 ms ms3 H (r : bv 5),
  st_ok SEGS E' ss (restrict H ms) -> st_ok_pi SEGS VAL E ss0 (restrict H ms3) ->
  env_agree 512 E E' -> sv_atoms_lt 512 (sr_get (ss_regs ss0) r) = true ->
  sr_get (ss_regs ss) r = sr_get (ss_regs ss0) r -> getr (ms_regs ms) r = getr (ms_regs ms3) r.
Proof.
  intros E E' ss ss0 ms ms3 H r HS HS0 HA Hat Heq.
  rewrite (st_ok_restrict_reg SEGS H E' ss ms r HS), (st_ok_pi_restrict_reg H E ss0 ms3 r HS0), Heq.
  exact (sv_denot_agree 512 E E' _ HA Hat).
Qed.
Lemma fb_atom_off_ok : forall Ex E ss ms H (r : bv 5) (n : nat) k v,
  st_ok SEGS Ex ss (restrict H ms) -> env_agree 512 E Ex -> (n < 512)%nat ->
  sr_get (ss_regs ss) r = SOff n k -> ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> getr (ms_regs ms) r = w64 (v + k).
Proof.
  intros Ex E ss ms H r n k v HS HA Hn Hsr Hv Hr. rewrite (st_ok_restrict_reg SEGS H Ex ss ms r HS), Hsr. cbn [sv_denot].
  rewrite (proj1 HA n Hn), Hv, unsigned_lit_small by exact Hr. reflexivity.
Qed.

Lemma fb_post : nx_from SK B KS (nx_post SK B MT KS) (nx_ts_inv B MT KS) ->
  nx_from SK B KS (nx_post SK B MT KS) (nx_exit_inv B MT KS) ->
  nx_from SK B KS (nx_post SK B MT KS) (nx_fitra_inv B MT KS).
Proof.
  intros NTS NEX cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFRS GI.
  destruct GI as (q & kk & HM & Hq & Hlh & Hpq & Hroom & Hincl & Hkk & HBJ & R10 & R20 & R21 & R22 & R25 & R27 & R26 & R23).
  set (sw := n_sw cx =? 1) in *. set (F := nxF (n_C cx)) in *. set (incl := PSN.incl sw F q) in *.
  destruct HBJ as (bj' & Hbj & Hbjl & Hbjp).
  pose proof (fb_nth_byte _ _ _ 12 Hbj) as Hb12. pose proof (fb_nth_byte _ _ _ 13 Hbj) as Hb13.
  pose proof (fb_nth_byte _ _ _ 14 Hbj) as Hb14. pose proof (fb_nth_byte _ _ _ 15 Hbj) as Hb15.
  assert (HkkR : 0 <= kk <= incl) by lia.
  assert (HiR : 1 <= incl <= 2040).
  { pose proof HB as HB'. fa_base HB'. destruct (HBUF0 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HM))))))) as (_ & _ & _ & _ & _ & Hcap & _).
    unfold NX_CAP_MAX in Hcap. lia. }
  assert (Hq0 : 0 <= q).
  { pose proof HB as HB'. fa_base HB'. destruct (HSTR (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HM))))))) as (_ & _ & _ & _ & Hp0 & _). lia. }
  destruct (Z.eq_dec kk incl) as [Ekk | Nkk].
  - (* the record was read in full: kk = incl *)
    subst kk. rewrite Ekk in HM, R10, Hbjp.
    assert (Hfit : q + 16 + incl <= Z.of_nat (length (n_C cx))) by lia.
    destruct (fb_seat2 cx fp k2 ly3 S3 W3 ms3 md3 _ _ _ _ _ incl incl _ _ _ _ 16 22 HB HJ HM R10 ltac:(lia) R25 R27 HiR R21
      Hb12 Hb13 Hb14 Hb15 ltac:(intros; lia)) as [HS SHOK].
    remember (Eimg (Ereg (ms_regs ms3) (fb_extra (n_ts cx) (n_h cx) (nth 12 bj' 0) (nth 13 bj' 0) (nth 14 bj' 0)
      (nth 15 bj' 0)))) as E eqn:HEdef.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (UE : forall (n : nat) (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr (ms_regs ms3) r = w64 v ->
      0 <= v < 2 ^ 64 -> U E (SOff n 0) = v).
    { intros n r v Hn Hr Hv. apply U_atom; [rewrite HEdef, (ew_Eimg_Ereg_nat _ _ n r Hn), Hr; reflexivity | exact Hv]. }
    pose proof HS as HS0.
    pose proof HM as (HBD & R24 & HJB & HKEPT & HEsub & Hh & HPS & HRAps & HSRC & Hqr & HBUF & HTS).
    assert (U21 : bv_unsigned (ew E 21) = n_ps cx).
    { rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 21 (21%bv : bv 5) eq_refl), R21. apply unsigned_lit_small.
      pose proof HB as HB'. fa_base HB'. fbox. unfold PS_LEN in *. lia. }
    assert (HWR : forall a, n_ps cx + 16 <= a < n_ps cx + 22 ->
      awr_byte (n_STK cx) (n_sp0 cx) (n_FP cx) (ablocks B (n_ly cx) (n_S cx)) (ablocks B ly3 S3) ly3
        ((NX_CID, fp) :: n_own cx) a).
    { intros a Ha. pose proof HB as HB'. fa_base HB'. pose proof (HWRps Hh) as HWRp. fbox.
      destruct (HWRp a ltac:(unfold PS_LEN; lia)) as [Hw _].
      assert (Hblc : forall x, In x (ablocks B (n_lyc cx) (n_Sc cx)) -> In x (ablocks B ly3 S3))
        by (intros x Hx; pose proof HJB as (_ & Hbl3 & _); rewrite Hbl3; exact Hx).
      assert (Hown3 : forall x, In x (n_own cx) -> In x ((NX_CID, fp) :: n_own cx)) by (intros x Hx; right; exact Hx).
      assert (EF : forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p).
      { intros c p. pose proof HJ0 as (_ & Hly0 & _). pose proof HJ as (_ & Hly3 & _).
        rewrite (frame_addr_layout_le _ _ _ Hly3), (frame_addr_layout_le _ _ _ Hly0). reflexivity. }
      exact (awr_byte_weaken _ _ _ _ _ _ _ _ _ _ _ Hblc Hown3 EF Hw). }
    pose proof HB as HBb. fa_base HBb. destruct (HBUF0 Hh) as (Hbin & Hb4096 & Hbn63 & _ & Hblen & Hcap & _ & Hbps).
    pose proof HJ0 as (HAR0 & Hly0 & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
    pose proof Hstk0 as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hbin) as (_ & _ & Hbceil & Hbapp & _).
    pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
    assert (HNX : NX_STK = 8496) by reflexivity.
    pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as [_ Hrqb].
    assert (Hblc : forall x, In x (ablocks B (n_lyc cx) (n_Sc cx)) -> In x (ablocks B ly3 S3))
      by (intros x Hx; pose proof HJB as (_ & Hbl3 & _); rewrite Hbl3; exact Hx).
    assert (Hts64 : 0 <= n_ts cx < 2 ^ 64).
    { destruct (Z.eq_dec (n_ts cx) 0) as [->|Hts0]; [lia|]. destruct (HTS0 Hh Hts0) as (_ & _ & Hts4096 & Hts47 & _). lia. }
    unfold PS_LEN, NX_CAP_MAX in *. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. fbox.
    psrr_branch_tok RUN BR HS SHOK fa_span.
    + exfalso. rewrite branch_ne_U, (UE 10%nat (10%bv : bv 5) incl eq_refl R10 ltac:(lia)),
        (UE 27%nat (27%bv : bv 5) incl eq_refl R27 ltac:(lia)), Z.eqb_refl in Hc. discriminate.
    + paj_run_tok RUN HS HJ SHOK fa_span;
        [ apply awr_ok_cons_ro; [cbn; lia|];
          eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 21%nat (n_ps cx)); [reflexivity | exact U21 | exact HWR | apply awr_ok_nil] |].
      psrr_branch_tok RUN BR HS SHOK fa_span.
      * paj_run_to_tok RUNTO HS HJ SHOK fa_span NP_ts;
          [ apply awr_ok_cons_ro; [cbn; lia|];
            eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 21%nat (n_ps cx)); [reflexivity | exact U21 | exact HWR | apply awr_ok_nil] |].
        (* NP_ts, incl < 18: untagged *)
        assert (Hlt : incl < 18).
        { rewrite branch_ltu_U, U_lit in Hc0 by lia.
          assert (U25 : U (ewset (ewset E 512 w) 513 w0) (SOff 25 0) = incl).
          { apply U_atom; [rewrite !ew_ewset_other by lia; rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 25 (25%bv : bv 5) eq_refl), R25; reflexivity | lia]. }
          rewrite U25 in Hc0. apply Z.ltb_lt in Hc0. exact Hc0. }
        assert (Htag : PSN.tagged sw F q = false).
        { unfold PSN.tagged. fold incl. rewrite (proj2 (Z.leb_gt 18 incl) Hlt). reflexivity. }
        pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as HR1. cbn [ms_mem restrict] in HR1.
        match type of HS with st_ok_pi _ _ ?Ex _ _ => assert (U21x : bv_unsigned (ew Ex 21) = n_ps cx) by (rewrite ?ew_ewset_other by lia; first [exact U21 | exact E21]) end.
        refine (fb_land_u cx fp k2 ly3 S3 W3 ms3 md3 _ _ q bj' NTS HB HJ HFRS HM Hq Hlh Hpq Hincl Hfit Hq0
           Hbj Hbjl Hbjp Htag (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) _ R25 R26 R23 _ _ _ _ _ _ _).
        -- intros r Hr. repeat (destruct Hr as [<- | Hr];
             [apply (fb_reg_eq _ _ _ _ _ _ _ _ HS HS0); [fb_agree | vm_compute; reflexivity | reflexivity] |]). destruct Hr.
        -- apply (fb_atom_reg _ E _ _ _ (21%bv : bv 5) 33 _ HS); [fb_agree | lia | reflexivity |].
           rewrite HEdef, Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra _ _ 1).
        -- rewrite !(proj1 (fb_wb_md _ _ _)). reflexivity.
        -- rewrite !(proj2 (fb_wb_md _ _ _)). reflexivity.
        -- intros a Ha Hn.
           repeat match goal with
           | HFq : frame_of ?Ex ?rs (mrestrict ?H ?m) (mrestrict ?H ?m') |- aview _ ?H ?m' _ = _ =>
               rewrite (fb_aview_frame Ex rs H m m' _ HFq Ha);
               [| apply (fb_nwr Ex rs (n_ps cx)); [cbn; fb_rs | rewrite ?ew_ewset_other by lia; first [exact U21 | exact E21] | exact Hn]]
           end; reflexivity.
        -- intros a Hp.
           repeat match goal with
           | HGq : mem_grows (mrestrict ?H ?m) (mrestrict ?H ?m') |- apresent ?H ?m' _ => apply (apresent_grows H m m' _ HGq)
           end; exact Hp.
        -- change 4%nat with (N.to_nat 4).
           apply (field_of_region _ _ 21 (n_ps cx) _ 0 24 16 22 16 4%N (SLit 0) 0 HR1 U21x); [cbn; tauto | reflexivity | lia | lia].
        -- change 2%nat with (N.to_nat 2).
           apply (field_of_region _ _ 21 (n_ps cx) _ 0 24 16 22 20 2%N (SLit 0) 0 HR1 U21x); [cbn; tauto | reflexivity | lia | lia].
      * (* incl >= 18: the buffer's bytes 12 .. 15 are read *)
        assert (U25 : U (ewset (ewset E 512 w) 513 w0) (SOff 25 0) = incl).
        { apply U_atom; [rewrite !ew_ewset_other by lia; rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 25 (25%bv : bv 5) eq_refl), R25; reflexivity | lia]. }
        assert (Hge : 18 <= incl).
        { rewrite branch_ltu_U, U_lit, U25 in Hc0 by lia. apply Z.ltb_ge in Hc0. exact Hc0. }
        set (E1 := ewset (ewset E 512 w) 513 w0) in *.
        assert (EE : forall n, (n < 512)%nat -> ew E1 n = ew E n) by (intros n Hn; subst E1; rewrite !ew_ewset_other by lia; reflexivity).
        assert (EX : forall i, (i < 7)%nat -> ew E1 (32 + i) = nth i (fb_extra (n_ts cx) (n_h cx) (nth 12 bj' 0) (nth 13 bj' 0) (nth 14 bj' 0) (nth 15 bj' 0)) (Z_to_bv 64 0)).
        { intros i Hi. rewrite EE by lia. rewrite HEdef, Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra _ _ i). }
        assert (E20 : ew E1 20 = Z_to_bv 64 (n_buf cx)).
        { rewrite EE by lia. rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 20 (20%bv : bv 5) eq_refl), R20. reflexivity. }
        assert (E9 : ew E1 9 = Z_to_bv 64 (n_sp1 cx)).
        { rewrite EE by lia. rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 9 (9%bv : bv 5) eq_refl).
          pose proof HBD as ((_ & _ & _ & _ & _ & _ & (_ & _ & R9 & _) & _) & _). exact R9. }
        assert (E21 : bv_unsigned (ew E1 21) = n_ps cx) by (rewrite EE by lia; exact U21).
        assert (Hsp1 : spZ (n_regs cx) - 256 <= n_sp1 cx <= spZ (n_regs cx) - 224).
        { unfold n_sp1, nx_sp1, NX_MFRAME. pose proof (Z.mod_pos_bound (spZ (n_regs cx) - 224) 32 ltac:(lia)).
          pose proof (Z_div_mod_eq_full (spZ (n_regs cx) - 224) 32). lia. }
        pose proof (st_ok_pi_add_fact _ _ _ 20%nat (mkAF 4096 (2 ^ 47 - 32) 0) HS) as HSa.
        assert (Hbj0 : garr8 SEGS (rdW W3 (ms_mem ms)) (n_buf cx) bj').
        { apply (fa_garr8_kept W3 W3 (ms_mem ms3) (ms_mem ms) _ _); [| exact Hbj].
          intros a Hx. assert (Ha : 0 <= a < 2 ^ 64) by (rewrite Hbjl in Hx; unfold nx_bufn in *; lia).
          assert (Hn : ~ (n_ps cx + 16 <= a < n_ps cx + 22)).
          { rewrite Hbjl in Hx. unfold boxed in Hbps. unfold nx_bufn in *. lia. }
          repeat match goal with
          | HFq : frame_of ?Ex ?rs (mrestrict ?H ?m) (mrestrict ?H ?m') |- aview _ ?H ?m' _ = _ =>
              rewrite (fb_aview_frame Ex rs H m m' _ HFq Ha);
              [| apply (fb_nwr Ex rs (n_ps cx)); [cbn; fb_rs | rewrite ?ew_ewset_other by lia; first [exact U21 | exact E21] | exact Hn]]
          end; reflexivity. }
        assert (Hb16 : (16 <= length bj')%nat) by (rewrite Hbjl; unfold nx_bufn in *; lia).
        pose proof (st_ok_pi_add_region _ _ _ fb_buf_r (HSa ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2];
          rewrite E20, unsigned_lit_small by lia; split; [lia|]; split; [apply Z.mod_1_r | lia])) eq_refl) as HSb.
        assert (E32 : ew E1 32 = Z_to_bv 64 SHADOW_OFF) by exact (EX 0%nat ltac:(lia)).
        assert (E35 : ew E1 35 = Z_to_bv 64 (nth 12 bj' 0)) by exact (EX 3%nat ltac:(lia)).
        assert (E36 : ew E1 36 = Z_to_bv 64 (nth 13 bj' 0)) by exact (EX 4%nat ltac:(lia)).
        assert (E37 : ew E1 37 = Z_to_bv 64 (nth 14 bj' 0)) by exact (EX 5%nat ltac:(lia)).
        assert (E38 : ew E1 38 = Z_to_bv 64 (nth 15 bj' 0)) by exact (EX 6%nat ltac:(lia)).
        assert (BV : forall j, (12 <= j < 16)%nat -> val_mem SEGS (rdW W3 (ms_mem ms)) (n_buf cx + Z.of_nat j) 1 (nth j bj' 0))
          by (intros j Hj; exact (proj1 (Hbj0 j ltac:(lia)))).
        assert (HRb : region_ok SEGS E1 (ms_mem (restrict (w_H W3) ms)) fb_buf_r).
        { cbn [ms_mem restrict]. unfold region_ok, fb_buf_r.
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
          rewrite E20, unsigned_lit_small by lia.
          split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
          - apply (chunk_ok_val SEGS E1 _ _ 12 1 (SOff 35 0) (nth 12 bj' 0));
              [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact (BV 12%nat ltac:(lia))].
          - apply (chunk_ok_val SEGS E1 _ _ 13 1 (SOff 36 0) (nth 13 bj' 0));
              [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact (BV 13%nat ltac:(lia))].
          - apply (chunk_ok_val SEGS E1 _ _ 14 1 (SOff 37 0) (nth 14 bj' 0));
              [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact (BV 14%nat ltac:(lia))].
          - apply (chunk_ok_val SEGS E1 _ _ 15 1 (SOff 38 0) (nth 15 bj' 0));
              [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact (BV 15%nat ltac:(lia))]. }
        specialize (HSb HRb). cbn [ss_mem add_atom add_cond] in HSb.
        assert (HS2 := HSb ltac:(cbn [all_disjoint]; unfold extent_disjoint;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val fb_buf_r fa_spill_r];
          rewrite E20, E9, E21, !unsigned_lit_small by lia; unfold boxed in Hbps; unfold nx_bufn in *;
          split; [left; lia | split; [lia | exact I]])).
        clear HSb HSa.
        assert (SHOK2 : sh_ok SEGS fa_SB fb_SH2 E1 (rdW W3 (ms_mem ms))).
        { unfold sh_ok in SHOK |- *. unfold fb_SH2. apply Forall_cons; [exact (Forall_inv SHOK)|].
          apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
          assert (USB1 : U E1 fa_SB = SHADOW_OFF) by (apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
          assert (U20 : U E1 (SOff 20 0) = n_buf cx) by (apply U_atom; [exact E20 | lia]).
          rewrite USB1, U20. split.
          - rewrite <- (aview_rd_of SEGS). pose proof HJ as (HARc & _).
            intros x Hx. apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ (n_buf cx) (nx_bufn (n_cap cx))
              (n_buf cx + 12) 4 HARc (Hblc _ Hbin)); [lia | unfold nx_bufn in *; lia | lia].
          - intros a Ha. unfold boxed in Hbapp. unfold SHADOW_OFF in *. unfold nx_bufn in *. lia. }
        clear HS SHOK. rename HS2 into HS. rename SHOK2 into SHOK.
        paj_run_tok RUN HS HJ SHOK fa_span;
          [ apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
            eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 21%nat (n_ps cx)); [reflexivity | exact E21 | exact HWR | apply awr_ok_nil] |].
        assert (U35 : forall Ex, (forall n, (n < 512)%nat -> ew Ex n = ew E1 n) -> U Ex (SOff 35 0) = nth 12 bj' 0).
        { intros Ex HEx. apply U_atom; [rewrite HEx by lia; exact E35 | lia]. }
        assert (U36 : forall Ex, (forall n, (n < 512)%nat -> ew Ex n = ew E1 n) -> U Ex (SOff 36 0) = nth 13 bj' 0).
        { intros Ex HEx. apply U_atom; [rewrite HEx by lia; exact E36 | lia]. }
        psrr_branch_tok RUN BR HS SHOK fa_span.
        -- (* NP_ts: buf[12] <> 129, untagged *)
           lazymatch type of Hc1 with context [sv_denot ?Ex (SOff 35 0)] => rewrite branch_ne_U, U_lit, (U35 Ex ltac:(intros ? ?; rewrite ?ew_ewset_other by lia; reflexivity)) in Hc1 by lia end.
           assert (Hb : nth 12 bj' 0 <> 129) by (intros Heq; rewrite Heq in Hc1; discriminate).
           assert (Htag : PSN.tagged sw F q = false).
           { pose proof (fb_src_bytes _ _ _ _ _ HSRC) as HCb.
              pose proof (fb_tag_byte (n_C cx) bj' q incl 12 HCb Hq0 ltac:(lia) Hbjp) as Hfb. change (Z.to_nat 12) with 12%nat in Hfb.
              unfold PSN.tagged. fold incl. change (nxF (n_C cx)) with F in Hfb.
              replace (q + 16 + 12) with (q + 28) in Hfb by lia. rewrite <- Hfb.
              destruct (Z.eqb_spec (nth 12 bj' 0) 129); [contradiction|]. rewrite andb_false_r. reflexivity. }
           paj_run_to_tok RUNTO HS HJ SHOK fa_span NP_ts;
              [ apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
                eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 21%nat (n_ps cx)); [reflexivity | rewrite ?ew_ewset_other by lia; exact E21 | exact HWR | apply awr_ok_nil] |].
           pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as HR1. cbn [ms_mem restrict] in HR1.
           match type of HS with st_ok_pi _ _ ?Ex _ _ => assert (U21x : bv_unsigned (ew Ex 21) = n_ps cx) by (rewrite ?ew_ewset_other by lia; first [exact U21 | exact E21]) end.
           refine (fb_land_u cx fp k2 ly3 S3 W3 ms3 md3 _ _ q bj' NTS HB HJ HFRS HM Hq Hlh Hpq Hincl Hfit Hq0
              Hbj Hbjl Hbjp Htag (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) _ R25 R26 R23 _ _ _ _ _ _ _).
           ++ intros r Hr. repeat (destruct Hr as [<- | Hr];
                [apply (fb_reg_eq _ _ _ _ _ _ _ _ HS HS0); [fb_agree | vm_compute; reflexivity | reflexivity] |]). destruct Hr.
           ++ apply (fb_atom_reg _ E _ _ _ (21%bv : bv 5) 33 _ HS); [fb_agree | lia | reflexivity |].
              rewrite HEdef, Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra _ _ 1).
           ++ rewrite !(proj1 (fb_wb_md _ _ _)). reflexivity.
           ++ rewrite !(proj2 (fb_wb_md _ _ _)). reflexivity.
           ++ intros a Ha Hn.
              repeat match goal with
              | HFq : frame_of ?Ex ?rs (mrestrict ?H ?m) (mrestrict ?H ?m') |- aview _ ?H ?m' _ = _ =>
                  rewrite (fb_aview_frame Ex rs H m m' _ HFq Ha);
                  [| apply (fb_nwr Ex rs (n_ps cx)); [cbn; fb_rs | rewrite ?ew_ewset_other by lia; first [exact U21 | exact E21] | exact Hn]]
              end; reflexivity.
           ++ intros a Hp.
              repeat match goal with
              | HGq : mem_grows (mrestrict ?H ?m) (mrestrict ?H ?m') |- apresent ?H ?m' _ => apply (apresent_grows H m m' _ HGq)
              end; exact Hp.
           ++ change 4%nat with (N.to_nat 4).
              apply (field_of_region _ _ 21 (n_ps cx) _ 0 24 16 22 16 4%N (SLit 0) 0 HR1 U21x); [cbn; tauto | reflexivity | lia | lia].
           ++ change 2%nat with (N.to_nat 2).
              apply (field_of_region _ _ 21 (n_ps cx) _ 0 24 16 22 20 2%N (SLit 0) 0 HR1 U21x); [cbn; tauto | reflexivity | lia | lia].
        -- lazymatch type of Hc1 with context [sv_denot ?Ex (SOff 35 0)] => rewrite branch_ne_U, U_lit, (U35 Ex ltac:(intros ? ?; rewrite ?ew_ewset_other by lia; reflexivity)) in Hc1 by lia end.
           assert (Hb12' : nth 12 bj' 0 = 129) by (destruct (Z.eqb_spec (nth 12 bj' 0) 129); [assumption | discriminate]).
           paj_run_tok RUN HS HJ SHOK fa_span;
             [ apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
               eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 21%nat (n_ps cx)); [reflexivity | rewrite ?ew_ewset_other by lia; exact E21 | exact HWR | apply awr_ok_nil] |].
           psrr_branch_tok RUN BR HS SHOK fa_span.
           ++ (* NP_ts: buf[13] <> 0, untagged *)
              lazymatch type of Hc2 with context [sv_denot ?Ex (SOff 36 0)] => rewrite branch_ne_U, U_lit, (U36 Ex ltac:(intros ? ?; rewrite ?ew_ewset_other by lia; reflexivity)) in Hc2 by lia end.
              assert (Hb : nth 13 bj' 0 <> 0) by (intros Heq; rewrite Heq in Hc2; discriminate).
              assert (Htag : PSN.tagged sw F q = false).
              { pose proof (fb_src_bytes _ _ _ _ _ HSRC) as HCb.
                 pose proof (fb_tag_byte (n_C cx) bj' q incl 13 HCb Hq0 ltac:(lia) Hbjp) as Hfb. change (Z.to_nat 13) with 13%nat in Hfb.
                 unfold PSN.tagged. fold incl. change (nxF (n_C cx)) with F in Hfb.
                 replace (q + 16 + 13) with (q + 29) in Hfb by lia. rewrite <- Hfb.
                 destruct (Z.eqb_spec (nth 13 bj' 0) 0); [contradiction|]. rewrite andb_false_r. reflexivity. }
              paj_run_to_tok RUNTO HS HJ SHOK fa_span NP_ts;
                 [ apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
                   eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 21%nat (n_ps cx)); [reflexivity | rewrite ?ew_ewset_other by lia; exact E21 | exact HWR | apply awr_ok_nil] |].
              pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as HR1. cbn [ms_mem restrict] in HR1.
              match type of HS with st_ok_pi _ _ ?Ex _ _ => assert (U21x : bv_unsigned (ew Ex 21) = n_ps cx) by (rewrite ?ew_ewset_other by lia; first [exact U21 | exact E21]) end.
              refine (fb_land_u cx fp k2 ly3 S3 W3 ms3 md3 _ _ q bj' NTS HB HJ HFRS HM Hq Hlh Hpq Hincl Hfit Hq0
                 Hbj Hbjl Hbjp Htag (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) _ R25 R26 R23 _ _ _ _ _ _ _).
              ** intros r Hr. repeat (destruct Hr as [<- | Hr];
                   [apply (fb_reg_eq _ _ _ _ _ _ _ _ HS HS0); [fb_agree | vm_compute; reflexivity | reflexivity] |]). destruct Hr.
              ** apply (fb_atom_reg _ E _ _ _ (21%bv : bv 5) 33 _ HS); [fb_agree | lia | reflexivity |].
                 rewrite HEdef, Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra _ _ 1).
              ** rewrite !(proj1 (fb_wb_md _ _ _)). reflexivity.
              ** rewrite !(proj2 (fb_wb_md _ _ _)). reflexivity.
              ** intros a Ha Hn.
                 repeat match goal with
                 | HFq : frame_of ?Ex ?rs (mrestrict ?H ?m) (mrestrict ?H ?m') |- aview _ ?H ?m' _ = _ =>
                     rewrite (fb_aview_frame Ex rs H m m' _ HFq Ha);
                     [| apply (fb_nwr Ex rs (n_ps cx)); [cbn; fb_rs | rewrite ?ew_ewset_other by lia; first [exact U21 | exact E21] | exact Hn]]
                 end; reflexivity.
              ** intros a Hp.
                 repeat match goal with
                 | HGq : mem_grows (mrestrict ?H ?m) (mrestrict ?H ?m') |- apresent ?H ?m' _ => apply (apresent_grows H m m' _ HGq)
                 end; exact Hp.
              ** change 4%nat with (N.to_nat 4).
                 apply (field_of_region _ _ 21 (n_ps cx) _ 0 24 16 22 16 4%N (SLit 0) 0 HR1 U21x); [cbn; tauto | reflexivity | lia | lia].
              ** change 2%nat with (N.to_nat 2).
                 apply (field_of_region _ _ 21 (n_ps cx) _ 0 24 16 22 20 2%N (SLit 0) 0 HR1 U21x); [cbn; tauto | reflexivity | lia | lia].
           ++ (* buf[12] = 0x81, buf[13] = 0: the VLAN tag, then __asan_memmove *)
              lazymatch type of Hc2 with context [sv_denot ?Ex (SOff 36 0)] => rewrite branch_ne_U, U_lit, (U36 Ex ltac:(intros ? ?; rewrite ?ew_ewset_other by lia; reflexivity)) in Hc2 by lia end.
              assert (Hb13' : nth 13 bj' 0 = 0) by (destruct (Z.eqb_spec (nth 13 bj' 0) 0); [assumption | discriminate]).
              pose proof (fb_src_bytes _ _ _ _ _ HSRC) as HCb.
              assert (FB : forall j, 0 <= j < incl -> nth (Z.to_nat j) bj' 0 = PSN.fb F (q + 16 + j))
                by (intros j Hj; exact (fb_tag_byte (n_C cx) bj' q incl j HCb Hq0 Hj Hbjp)).
              assert (Htag : PSN.tagged sw F q = true).
              { unfold PSN.tagged. fold incl. pose proof (FB 12 ltac:(lia)) as F12. pose proof (FB 13 ltac:(lia)) as F13.
                change (Z.to_nat 12) with 12%nat in F12. change (Z.to_nat 13) with 13%nat in F13.
                replace (q + 16 + 12) with (q + 28) in F12 by lia.
                replace (q + 16 + 13) with (q + 29) in F13 by lia. rewrite <- F12, <- F13, Hb12', Hb13'.
                rewrite (proj2 (Z.leb_le 18 incl) Hge). reflexivity. }
              assert (Hvid : PSN.rec_vid F q = (256 * nth 14 bj' 0 + nth 15 bj' 0) mod 4096).
              { pose proof (FB 14 ltac:(lia)) as F14. pose proof (FB 15 ltac:(lia)) as F15.
                change (Z.to_nat 14) with 14%nat in F14. change (Z.to_nat 15) with 15%nat in F15.
                replace (q + 16 + 14) with (q + 30) in F14 by lia. replace (q + 16 + 15) with (q + 31) in F15 by lia.
                unfold PSN.rec_vid. rewrite <- F14, <- F15. reflexivity. }
              paj_run_tok RUN HS HJ SHOK fa_span;
                [ apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
                  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 21%nat (n_ps cx)); [reflexivity | rewrite ?ew_ewset_other by lia; exact E21 | exact HWR | apply awr_ok_nil] |].
              pose proof (st_ok_region_nth _ _ _ 2 _ HS eq_refl) as HR1. cbn [ms_mem restrict] in HR1.
              match type of HS with st_ok _ ?Ex _ _ =>
                assert (U21x : bv_unsigned (ew Ex 21) = n_ps cx) by (rewrite ?ew_ewset_other by lia; exact E21);
                assert (U25x : U Ex (SOff 25 0) = incl) by (apply U_atom; [rewrite ?ew_ewset_other by lia; rewrite EE by lia; rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 25 (25%bv : bv 5) eq_refl), R25; reflexivity | lia]);
                assert (U37x : U Ex (SOff 37 0) = nth 14 bj' 0) by (apply U_atom; [rewrite ?ew_ewset_other by lia; exact E37 | lia]);
                assert (U38x : U Ex (SOff 38 0) = nth 15 bj' 0) by (apply U_atom; [rewrite ?ew_ewset_other by lia; exact E38 | lia]);
                assert (RGc : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 24; 26; 23]%bv -> getr (ms_regs ms2) r = getr (ms_regs ms3) r)
                  by (intros r Hr; repeat (destruct Hr as [<- | Hr];
                    [apply (fb_reg_eq_ok _ _ _ _ _ _ _ _ HS HS0); [fb_agree | vm_compute; reflexivity | vm_compute; reflexivity] |]); destruct Hr);
                assert (R12c : getr (ms_regs ms2) 12 = w64 (incl - 16))
                  by (rewrite (st_ok_restrict_reg SEGS _ Ex _ ms2 (12%bv : bv 5) HS); cbn [setpc ss_regs sr_get bv_eqb];
                      rewrite denot_lit_U; unfold w64; f_equal; apply fb_a2; [exact U25x | lia]);
                assert (Vvid : val_mem SEGS (rdW W3 (ms_mem ms2)) (n_ps cx + 20) 2 (PSN.rec_vid F q))
                  by (change 2%nat with (N.to_nat 2); apply (field_of_region Ex _ 21 (n_ps cx) _ 0 24 16 22 20 2%N (SAlu ALU_OR (SAlu ALU_AND (SAlu ALU_SLL (SOff 37 0) (SLit 8)) (SLit 3840)) (SOff 38 0)) (PSN.rec_vid F q) HR1 U21x);
                      [cbn; tauto | rewrite denot_lit_U, (fb_vid Ex _ _ U37x U38x Hb14 Hb15), Hvid; reflexivity
                      | rewrite Hvid; pose proof (Z.mod_pos_bound (256 * nth 14 bj' 0 + nth 15 bj' 0) 4096 ltac:(lia)); cbn; lia | lia]);
                assert (Vtag : val_mem SEGS (rdW W3 (ms_mem ms2)) (n_ps cx + 16) 4 1)
                  by (change 4%nat with (N.to_nat 4); apply (field_of_region Ex _ 21 (n_ps cx) _ 0 24 16 22 16 4%N (SLit 1) 1 HR1 U21x);
                      [cbn; tauto | reflexivity | lia | lia]);
                assert (R10c : getr (ms_regs ms2) 10 = w64 (n_buf cx + 12))
                  by (apply (fb_atom_off_ok _ E _ _ _ (10%bv : bv 5) 20 12 _ HS); [fb_agree | lia | vm_compute; reflexivity
                      | rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 20 (20%bv : bv 5) eq_refl), R20; reflexivity | lia]);
                assert (R11c : getr (ms_regs ms2) 11 = w64 (n_buf cx + 16))
                  by (apply (fb_atom_off_ok _ E _ _ _ (11%bv : bv 5) 20 16 _ HS); [fb_agree | lia | vm_compute; reflexivity
                      | rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 20 (20%bv : bv 5) eq_refl), R20; reflexivity | lia]);
                assert (R21c : getr (ms_regs ms2) 21 = w64 (n_ts cx))
                  by (rewrite <- (Z.add_0_r (n_ts cx)); apply (fb_atom_off_ok _ E _ _ _ (21%bv : bv 5) 33 0 _ HS); [fb_agree | lia | vm_compute; reflexivity
                      | rewrite HEdef, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1) | lia]);
                assert (R25c : getr (ms_regs ms2) 25 = w64 incl)
                  by (rewrite <- (Z.add_0_r incl); apply (fb_atom_off_ok _ E _ _ _ (25%bv : bv 5) 25 0 _ HS); [fb_agree | lia | vm_compute; reflexivity
                      | rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 25 (25%bv : bv 5) eq_refl), R25; reflexivity | lia])
              end.
              prreg HS (1%bv : bv 5) Q1.
              pmkst HS.
              refine (MMC cx fp k2 ly3 S3 W3 ms3 md3 q bj' _ _ _ NTS HB HJ HFRS HM Hq Hlh Hpq Hincl Hfit Htag Hbj Hbjl Hbjp
                Q1 R10c R11c R12c _ R21c R25c _ _ _ _ _ _ Vtag Vvid).
              ** intros r Hr. apply RGc. cbn in Hr |- *. tauto.
              ** rewrite (RGc 26%bv) by (cbn; tauto). exact R26.
              ** rewrite (RGc 23%bv) by (cbn; tauto). exact R23.
              ** rewrite !(proj1 (fb_wb_md _ _ _)). reflexivity.
              ** rewrite !(proj2 (fb_wb_md _ _ _)). reflexivity.
              ** intros a Ha Hn.
                 repeat match goal with
                 | HFq : frame_of ?Ex ?rs (mrestrict ?H ?m) (mrestrict ?H ?m') |- aview _ ?H ?m' _ = _ =>
                     rewrite (fb_aview_frame Ex rs H m m' _ HFq Ha);
                     [| apply (fb_nwr Ex rs (n_ps cx)); [cbn; fb_rs | rewrite ?ew_ewset_other by lia; first [exact U21 | exact E21] | exact Hn]]
                 end; reflexivity.
              ** intros a Hp.
                 repeat match goal with
                 | HGq : mem_grows (mrestrict ?H ?m) (mrestrict ?H ?m') |- apresent ?H ?m' _ => apply (apresent_grows H m m' _ HGq)
                 end; exact Hp.
  - destruct (fb_seat2 cx fp k2 ly3 S3 W3 ms3 md3 _ _ _ _ _ kk incl _ _ _ _ 0 0 HB HJ HM R10 ltac:(lia) R25 R27 HiR R21
      Hb12 Hb13 Hb14 Hb15 ltac:(intros; lia)) as [HS SHOK].
    remember (Eimg (Ereg (ms_regs ms3) (fb_extra (n_ts cx) (n_h cx) (nth 12 bj' 0) (nth 13 bj' 0) (nth 14 bj' 0)
      (nth 15 bj' 0)))) as E eqn:HEdef.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    psrr_branch_tok RUN BR HS SHOK fa_span.
    + paj_run_to_tok RUNTO HS HJ SHOK fa_span NP_exit;
        [ repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil |].
      pose proof HF as Em. apply fa_mem_eq_ro in Em;
        [| unfold fb_ss2, fb_ps_r, fa_spill_r; cbn; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil].
      assert (Hcut : Z.of_nat (length (n_C cx)) < q + 16 + incl) by lia.
      assert (Hpos : q + 16 + kk = Z.of_nat (length (n_C cx))) by lia.
      prreg HS (22%bv : bv 5) Q22. rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 22 (22%bv : bv 5) eq_refl) in Q22.
      pose proof HM as (HBD & R24 & HJB & HKEPT & HEsub & Hh & HPS & HRAps & HSRC & Hqr & HBUF & HTS).
      pose proof (fb_src_bytes _ _ _ _ _ HSRC) as HCb.
      eapply NEX; [exact HB | exact HJ | exact HFRS |].
      split; [|split].
      * apply (fb_body_at cx fp NP_fit_ra NP_exit W3 ms3 ms NSH_ph E _ _ HBD HEdef HS eq_refl eq_refl);
          [intros r Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr |].
        intros a _. rewrite Em. reflexivity.
      * apply (fb_jbk _ _ _ _ md3); [exact HJB | apply fb_wb_md | apply fb_wb_md].
      * unfold nx_fin_at, nx_fin. right. rewrite Em, Q22, R22.
        split; [exact Hh|].
        split; [fold sw; rewrite (fa_cut_res sw (n_C cx) (n_cap cx) (n_p cx) q Hq Hroom Hincl Hcut); reflexivity|].
        split; [exact HKEPT|].
        split; [fold sw; rewrite (fa_cut_pos sw (n_C cx) (n_cap cx) (n_p cx) q Hq Hroom Hincl Hcut), <- Hpos; exact HSRC|].
        split.
        { fold sw. rewrite (fa_cut_vtag sw (n_C cx) (n_cap cx) (n_p cx) q Hq Hroom Hincl Hcut),
            (fa_cut_vid sw (n_C cx) (n_cap cx) (n_p cx) q Hq Hroom Hincl Hcut).
          unfold nx_orig. rewrite Hlh. exact HPS. }
        split.
        { destruct HBUF as (bj2 & Hb2 & Hb2l). exists bj2. split; [exact Hb2|]. split; [exact Hb2l|].
          fold sw. rewrite (fa_cut_fit sw (n_C cx) (n_cap cx) (n_p cx) q Hq Hroom Hincl Hcut). discriminate. }
        intros Hts. fold sw. rewrite (fa_cut_tsv sw (n_C cx) (n_cap cx) (n_p cx) q Hq Hroom Hincl Hcut).
        exact (proj1 (HTS Hts)).
    + exfalso. apply Nkk.
      assert (UE : forall (n : nat) (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr (ms_regs ms3) r = w64 v ->
        0 <= v < 2 ^ 64 -> U E (SOff n 0) = v).
      { intros n r v Hn Hr Hv. apply U_atom; [rewrite HEdef, (ew_Eimg_Ereg_nat _ _ n r Hn), Hr; reflexivity | exact Hv]. }
      rewrite branch_ne_U, (UE 10%nat (10%bv : bv 5) kk eq_refl R10 ltac:(lia)),
        (UE 27%nat (27%bv : bv 5) incl eq_refl R27 ltac:(lia)) in Hc.
      destruct (Z.eqb_spec kk incl); [assumption | discriminate].
Qed.

(* THE PHASE: from NP_fit (nx_fit_inv) to NP_ts (nx_ts_inv) or NP_exit (nx_exit_inv, the record is cut). *)
Lemma fa_fit_phase : nx_from SK B KS (nx_post SK B MT KS) (nx_ts_inv B MT KS) ->
  nx_from SK B KS (nx_post SK B MT KS) (nx_exit_inv B MT KS) ->
  nx_from SK B KS (nx_post SK B MT KS) (nx_fit_inv B MT KS).
Proof. intros NTS NEX. exact (fa_pre B MT KS LAWS AFREAD (fb_post NTS NEX)). Qed.
End v.
