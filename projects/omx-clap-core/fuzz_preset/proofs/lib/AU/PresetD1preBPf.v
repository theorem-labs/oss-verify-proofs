(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: GENERATED from lib/A/PresetD1preAPf.v (lane CwPreA, a working branch a9e03801db9b) by port/a2b.py (sha256 e4f47803449f38c2) with its measured literal map (a table literal in code is written as its image-B cell name from lib/Reusable/YImgCellsB.v) and --map 0x10000=0x10000 0x20e00=0x20e00 0x20f40=0x20f40 (image B's first zero-shadow range is also (YImgTop.IMG_LO, 0x20f40 - YImgTop.IMG_LO), lib/Reusable/YF0m.v Tfib_zero_shadow). No hand edit. PENDING YF0m, as PresetD1preB.v. *)
(* Modified by Theorem Labs, 2026-10: the proofs of the results stated in lib/AU/PresetD1preB.v (fuzz_preset, asan-ubsan
   image), ported from proofs/cgif/cgif_file_fuzzer/lib (here as relocated by the core in lib/Reusable) with cgif's AR
   replaced by ARcf at Hp = [], cgif's AR_laws by a8's AR_laws_ok_cf (YG0lawscf.v), cgif's model law ml_malloc_ns
   by a8's malloc_ok_cf (YG07cf.v:390), and cgif's event bounds dropped:
     ecall_pre_cf_of_drv                    from YD1i.v:95-104 ecall_pre_of_drv;
     tfib_malloc_site_cf_B_holds            from YD1n.v:24-44;
     tfib_memcpy_site_cf_B_holds            from YD1i.v:105-110;
     tfib_read_check_cf_B_holds             from YD1i.v:111-115;
     se_not_owned_cf / site_keep_free_cf    from YD27.v:137-167;
     exit2_tail_cf / fpr_leaf_cf            from YD27.v:310-404;
     tfib_rderr_leaf_cf_B_holds / tfib_refused_leaf_cf_B_holds / tfib_cannot_open_cf_B_holds /
     tfib_usage_cf_B_holds                  from YD27.v:405-444, :465-547, :568-671;
     fw_leaf_cf / tfib_short_leaf_cf_B_holds / tfib_overrun_leaf_cf_B_holds   from YD27.v:714-877.
   Cited from other lanes: CwSites' lib/AU/PresetD1sitesBPf.v (acall_pre_cf_of_drv, call_trace_drv,
   layout_of_ARcf, est_frame_run_cf, so_state_run_cf, run_to_exit_cf), CwLoopB's lib/AU/PresetD1rBx.v
   (AR_after_run_cf, drv_after_call_cf) and lib/AU/PresetD1rBso.v (so_not_owned_cf), and the interface's
   PCB.iface_room_np_tail (lib/AU/PresetCfnB.v). The symbolic runs of the driver (YD27.v / YD28.v /
   YD2h.v ...) name no allocator invariant and are used as they are.
   Rule 24: no function is proved here (composition / driver layer of a port). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15
YK0k YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP01 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02
YL04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0k YG0f YG0v YG0n YG0d YCe5.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB12 YF0l YB1h YB13 YF0m YD2j YD2i YD1t
YD20 YD1v YD1y YD2a YD26 YD24.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD21 YD25 YD22 YD23 YD2h YD1w YD2f YD2b YD2g
YD1s YD2c YD2d YD29 YD1x YD28 YD27.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0d2cf YGcfTok YGcfRoomPre YG07cf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomKeep YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD1rBx PresetD1rBso PresetD1sitesB PresetD1sitesBPf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD1preB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetDrvHull.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetDrvAroB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
(* The interface's non-primary room (PROVISIONAL, CwSites' PresetD1sitesB.v): a driver state carries NP S. *)
Variable NP : astate -> Prop.

(* ---------------------------------------------------------------------- *)
(* 1. The intrinsic call form from the driver's pre. Donor: YD1i.v:95-104. *)
Lemma ecall_pre_cf_of_drv : forall ly S W regs mem md,
drv_epre_cf B ly S W regs mem md -> ecall_pre_cf tfibsegs B ly S [] W regs mem md.
Proof.
intros ly S W regs mem md (HAR & [Elo Ehi] & Hret & Hal & [Wlo Whi] & [Tlo Thi] & Hpres & Hgp & Htp).
unfold sp_window_lo, sp_window_hi in *.
split; [exact HAR|]. split; [exact Hret|]. split; [exact Hal|].
pose proof (lo_top _ (layout_of_ARcf B _ _ _ _ _ _ HAR)) as (T1 & T2 & _).
split; [unfold ly_bot, kStackSpan, ESTACK in *; lia|]. split; [rewrite Ehi; unfold kHighMemEnd; lia|].
split; [exact Hpres|]. exact (conj Hgp Htp).
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The malloc site. Donor: YD1n.v:24-44. a8's malloc_ok_cf replaces cgif's ml_malloc_ns; its room premise
      ROOM_cf S comes from drv_pre_cf's NP S by the interface's PCB.iface_room_np_tail NP (a8's RK_room). Every outcome goes
      to the continuation (no PNull refutation: a8's ml_malloc_ns_cf NULL arm is carried to the caller). *)
Lemma tfib_malloc_site_cf_sec : PCB.iface_room_np_tail NP -> drv_hull_link -> drv_aro_link B ->
  YGcfMallocComposeKeep.amalloc_realizes_cf_keep tfibsegs B -> malloc_site_tfa_cf B NP.
Proof.
intros NPT HL AL AMALLOC ly S W regs mem md n KB HPRE Ha0 Hn Hlive Htr2 Htr1 HAI KBLK.
pose proof (acall_pre_cf_of_drv B NP NPT HL AL ly S W regs mem md HPRE) as HAP.
pose proof (proj1 HPRE) as HAR.
assert (HRM : ROOM_cf S) by (apply (YGcfRoomKeep.RK_room S 2); apply NPT; unfold drv_pre_cf in HPRE; tauto).
pose proof (proj1 HAR) as HWF. apply amc_wf in HWF. pose proof (proj1 HAR) as HU. apply amc_universe in HU.
unfold ROOM_cf in HRM. destruct HRM as (R1 & R2 & R3).
set (trc := call_trace ly (pc_malloc_ra0 (as_code B)) regs []).
assert (Htr : In trc (as_universe B)).
{ subst trc. destruct (call_trace_drv ly regs (pc_malloc_ra0 (as_code B))) as [-> | ->]; assumption. }
pose proof (malloc_ok_cf (as_universe B) S n trc HU HWF Hn Hlive (YG01.admits_fix _ _ S HU Htr) R1 R2 R3) as HTOK.
pose proof (AMALLOC ly S [] W regs mem md n [] HAP Ha0 Hn Hlive (YG01.admits_fix _ _ S HU Htr)) as HREAL. fold trc in HREAL.
apply (SRr_srealizes tfibsegs W (cfg_at tfibsegs (pc_wrap_malloc (as_code B)) regs mem md) _ _
(amreal_SRr04 tfibsegs _ W _ _ HREAL (atok_cf_asafe _ _ _ HTOK) (atok_cf_agprog _ _ _ HTOK) (atok_cf_nospin _ _ HTOK)) HAI).
intros W' c' Hwle HAI' (r & tr & Hpath & Hgf & Hleaf).
exact (KBLK r trc tr W' c' Htr Hpath Hgf Hleaf Hwle HAI').
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The memcpy site and the read check. Donor: YD1i.v:105-115. *)
Lemma tfib_memcpy_site_cf_sec : YGcallMxmn.aintrin_realizes_xm tfibsegs B (ARcf tfibsegs B) OCpy (pc_wrap_memcpy (as_code B)) -> memcpy_site_tfa_cf B.
Proof.
intros AICPY ly S W regs mem md d x n HPRE R10 R11 R12 Hn Hd0 Hd1 Hdest Hdm Hra Hhv Hx0 Hx1 Hsrc Hdisj Hxm Hrax Hhvx.
exact (AICPY ly S [] W regs mem md d x n (ecall_pre_cf_of_drv _ _ _ _ _ _ HPRE) R10 R11 R12 Hn Hd0 Hd1 Hdest Hdm Hra Hhv
(conj Hx0 (conj Hx1 (conj Hsrc (conj Hdisj (conj Hxm (conj Hrax Hhvx))))))).
Qed.

Lemma tfib_read_check_cf_sec : aread_check_stmt_cf B -> read_check_tfa_cf B.
Proof.
intros ARD ly S W regs mem md n ptr HPRE R10 R9 Hn Hp0 Hp1 Ham Hra Hhv.
exact (ARD ly S [] W regs mem md n ptr (ecall_pre_cf_of_drv _ _ _ _ _ _ HPRE) R10 R9 Hn Hp0 Hp1 Ham Hra Hhv).
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. The diagnostic leaves. Donor: YD27.v:100-877 (Section f). *)
Section R.
Hypothesis HB : TfibSyms B.
Let ARL : AR_laws_cf tfibsegs B := AR_laws_ok_cf tfibsegs B.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis EXS : exit_site_cf B est xst.

(* YD27.v:137-145. *)
Lemma se_not_owned_cf : forall ly S Hp W mem md a, ARcf tfibsegs B ly S Hp W mem md -> STDERR_MUT a -> ~ aowned B ly S a.
Proof.
intros ly S Hp W mem md a HAR Ha X.
assert (Hi : in_img tfibsegs a) by (apply in_img_rw; unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Ha; lia).
pose proof (proj1 (alc_owned_image _ _ ARL _ _ _ _ _ _ _ HAR Hi) X) as Y. rewrite (ts_owned B HB) in Y.
apply Exists_exists in Y as ([lo l] & Hin & Hz). unfold in_zr in Hz. cbn in Hz.
unfold Tfib_owned_static in Hin. unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Ha. cbn in Hin.
repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.

(* YD27.v:146-167. *)
Lemma site_keep_free_cf : forall ly S W mem md ly' S' W' regs regs' mem' md' (Eb : Z -> Prop) usp k,
acall_post_cf tfibsegs B ASTACK ly S [] W regs mem md Eb ly' S' W' regs' mem' md' -> ARcf tfibsegs B ly S [] W mem md ->
(forall a, Eb a -> a < alloc_ceiling /\ ~ in_img tfibsegs a) -> spZ regs = usp - 128 -> sp_window_lo <= usp ->
est (w_H W) mem -> so_state xst k (w_H W) mem ->
est (w_H W') mem' /\ so_state xst k (w_H W') mem'.
Proof.
intros ly S W mem md ly' S' W' regs regs' mem' md' Eb usp k HPOST HAR HEb Hsp Ulo HE HSO.
pose proof HPOST as (HAR' & _ & _ & _ & _ & Hfr & _).
assert (KEEP : forall a, (STDERR_MUT a \/ STDOUT_MUT a) -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha.
assert (Hr : YImgCellsB.B_STDERR_FILE_CELL <= a < YImgCellsB.B_FUNCS_CELL) by (unfold STDERR_MUT, STDOUT_MUT, F_STDERR_LO, F_STDERR_HI, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha; lia).
apply Hfr.
- lia.
- destruct Ha as [Ha|Ha]; [exact (se_not_owned_cf ly S [] W mem md a HAR Ha) | exact (so_not_owned_cf B HB ARL ly S [] W mem md a HAR Ha)].
- destruct Ha as [Ha|Ha]; [exact (se_not_owned_cf ly' S' [] W' mem' md' a HAR' Ha) | exact (so_not_owned_cf B HB ARL ly' S' [] W' mem' md' a HAR' Ha)].
- unfold ascratch. rewrite Hsp, (ts_errno B HB). unfold TFIB_ERRNO, ASTACK. unfold sp_window_lo in Ulo.
unfold STDERR_MUT, STDOUT_MUT, F_STDERR_LO, F_STDERR_HI, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. lia.
- intros X. apply (proj2 (HEb a X)). apply in_img_rw. lia. }
split.
- apply (ESTF (w_H W) (w_H W') mem mem' HE). intros a Ha. apply KEEP. left. exact Ha.
- apply (so_state_keep xst XFR k (w_H W) (w_H W') mem mem'); [| exact HSO]. intros a Ha. apply KEEP. right. exact Ha.
Qed.

(* the same after a free under the re-hide (YGcfRehidePost.acall_post_cf_rh): the set the call may hide misses the
   image's stderr / stdout bytes (PresetD1rBx.dsn_not_img) *)
Lemma site_keep_free_cf_rh : forall ly S W mem md ly' S' W' regs regs' mem' md' (Eb : Z -> Prop) usp k,
YGcfRehidePost.acall_post_cf_rh tfibsegs B ASTACK ly S [] W regs mem md Eb ly' S' W' regs' mem' md' ->
ARcf tfibsegs B ly S [] W mem md ->
(forall a, Eb a -> a < alloc_ceiling /\ ~ in_img tfibsegs a) -> spZ regs = usp - 128 -> sp_window_lo <= usp ->
est (w_H W) mem -> so_state xst k (w_H W) mem ->
est (w_H W') mem' /\ so_state xst k (w_H W') mem'.
Proof.
intros ly S W mem md ly' S' W' regs regs' mem' md' Eb usp k HPOST HAR HEb Hsp Ulo HE HSO.
pose proof HPOST as (HAR' & _ & _ & _ & _ & Hfr & _).
assert (KEEP : forall a, (STDERR_MUT a \/ STDOUT_MUT a) -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha.
assert (Hr : YImgCellsB.B_STDERR_FILE_CELL <= a < YImgCellsB.B_FUNCS_CELL) by (unfold STDERR_MUT, STDOUT_MUT, F_STDERR_LO, F_STDERR_HI, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha; lia).
apply Hfr.
- lia.
- destruct Ha as [Ha|Ha]; [exact (se_not_owned_cf ly S [] W mem md a HAR Ha) | exact (so_not_owned_cf B HB ARL ly S [] W mem md a HAR Ha)].
- destruct Ha as [Ha|Ha]; [exact (se_not_owned_cf ly' S' [] W' mem' md' a HAR' Ha) | exact (so_not_owned_cf B HB ARL ly' S' [] W' mem' md' a HAR' Ha)].
- unfold ascratch. rewrite Hsp, (ts_errno B HB). unfold TFIB_ERRNO, ASTACK. unfold sp_window_lo in Ulo.
unfold STDERR_MUT, STDOUT_MUT, F_STDERR_LO, F_STDERR_HI, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. lia.
- intros X. apply (proj2 (HEb a X)). apply in_img_rw. lia.
- apply dsn_not_img. lia. }
split.
- apply (ESTF (w_H W) (w_H W') mem mem' HE). intros a Ha. apply KEEP. left. exact Ha.
- apply (so_state_keep xst XFR k (w_H W) (w_H W') mem mem'); [| exact HSO]. intros a Ha. apply KEEP. right. exact Ha.
Qed.

(* YD27.v:310-348. *)
Lemma exit2_tail_cf : forall (b : bool) E (W : world tfibsegs) regs mem md ly S (usp : Z) (fs : Fs),
bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 -> 1 <= bv_unsigned (ew E 8) <= 4194303 ->
spZ regs = usp - 128 -> getr regs 3%bv = w64 TFIB_GP -> getr regs 4%bv = w64 TFIB_TP ->
mem_ok tfibsegs E (mrestrict (w_H W) mem) IMG_X ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S [] W mem md -> top_ok usp ly ->
est (w_H W) mem -> stdout_img (w_H W) mem -> m_fs md = fs ->
srealizes tfibsegs (mkCfg (mkst regs (Z_to_bv 64 (if b then YImgCellsB.B_MAIN_PC_OFF_288 else YImgCellsB.B_MAIN_PC_OFF_264)) mem (seg_rom tfibsegs)) md) (ex 2 fs).
Proof.
intros b E W regs mem md ly S usp fs E0 [Ulo Uhi] U16 Htid Hsp R3 R4 HM Hwin HAI HAR HTOP HEst HSO Hfs.
pose proof (regs_ok_J E regs (-128) usp E0 ltac:(lia) Ulo ltac:(lia) R3 R4) as HR.
pose proof (st_ok_J IMG_X E regs (jregs (-128)) (-128) (if b then YImgCellsB.B_MAIN_PC_OFF_288 else YImgCellsB.B_MAIN_PC_OFF_264) usp false (w_H W) mem (or_introl eq_refl) HR E0 Ulo ltac:(lia) HM Hwin ltac:(discriminate)) as HS.
assert (HS' : st_ok tfibsegs (E_J E regs) (if b then S_J7 else S_J5) (restrict (w_H W) (mkst regs (Z_to_bv 64 (if b then YImgCellsB.B_MAIN_PC_OFF_288 else YImgCellsB.B_MAIN_PC_OFF_264)) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. pose proof S_J_defs as (D7 & D5 & _). destruct b; [rewrite D7 | rewrite D5]; exact HS. }
clear HS. set (E2 := E_J E regs) in *.
assert (E2_0 : bv_unsigned (ew E2 0) = usp) by (subst E2; rewrite E_J_old by (unfold KJ; lia); exact E0).
apply (srz_conseq tfibsegs _ (wr ch_stdout (concat (repeat line0 (0 - 1))) (ex 2 fs))).
2:{ cbn [Nat.sub repeat concat]. unfold wr. cbn [map]. apply t_emit_nil_eq. unfold ex, t_exit. apply t_emit_has_nil. }
apply (run_to_exit_cf B HB xst est XFR ESTF EXS (if b then 0 else 1)%nat (if b then S_J7 else S_J5) E2 W _ md ly S usp fs 2 0%nat IMG_X (-128) false);
[| | | left; reflexivity | | right; reflexivity | ..].
- destruct b; cbn; lia.
- cbn [ms_mem mkst]. pose proof S_JFc_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M7 & M5 & _).
destruct b; cbn [nth XSTS]; [rewrite M7; exact (j7_run E2 W _ md HS') | rewrite M5; exact (j5_run E2 W _ md HS')].
- pose proof S_JFc_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M7 & M5 & _). destruct b; [exact M7 | exact M5].
- left. reflexivity.
- exact E2_0.
- lia.
- exact U16.
- subst E2. rewrite E_J_old by (unfold KJ; lia). exact Htid.
- destruct b; reflexivity.
- right. reflexivity.
- exact HAI.
- exact HAR.
- exact HTOP.
- exact HEst.
- left. split; [reflexivity | exact HSO].
- intros Hk. exfalso. lia.
- exact Hfs.
Qed.

(* YD27.v:353-404. *)
Lemma fpr_leaf_cf : forall (fmt : Z) (lit1 : list byte), fprintf_s_site_tfa_cf B est fmt lit1 nlB ->
forall E (W : world tfibsegs) regs mem md ly S (usp : Z) (p : list byte) (zp : Z) (fs : Fs),
bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 -> 1 <= bv_unsigned (ew E 8) <= 4194303 ->
getr regs 10%bv = w64 YImgCellsB.B_STDERR_FILE_CELL -> getr regs 11%bv = w64 fmt -> getr regs 12%bv = w64 zp ->
getr regs 1%bv = w64 YImgCellsB.B_MAIN_PC_OFF_264 -> spZ regs = usp - 128 -> getr regs 3%bv = w64 TFIB_GP -> getr regs 4%bv = w64 TFIB_TP ->
usp <= zp -> zp + Z.of_nat (length p) + 1 < kHighMemEnd -> ~ In NUL p -> Z.of_nat (length p) <= 131071 ->
YP03.bytes_at (mrestrict (w_H W) mem) zp (p ++ [NUL]) ->
(forall a, zp + Z.of_nat (length p) < a < zp + Z.of_nat (length p) - (zp + Z.of_nat (length p)) mod 8 + 8 -> mrestrict (w_H W) mem (Z_to_bv 64 a) <> None) ->
mem_ok tfibsegs E (mrestrict (w_H W) mem) IMG_REGIONS ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S [] W mem md -> top_ok usp ly ->
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> m_fs md = fs ->
srealizes tfibsegs (mkCfg (mkst regs (w64 YImgCellsB.B_WRAP_FPRINTF_PC) mem (seg_rom tfibsegs)) md) (wr ch_stderr (lit1 ++ p ++ nlB) (ex 2 fs)).
Proof.
intros fmt lit1 FP E W regs mem md ly S usp p zp fs E0 [Ulo Uhi] U16 Htid R10 R11 R12 R1 Hsp R3 R4 Hzp1 Hzp2 Hnn Hlen HBr Htl HM Hwin HAI HAR HTOP Hfd2 Hfs.
pose proof (imgs_of_R E (w_H W) mem HM) as [HSO HSE].
assert (Hra : raZ regs = YImgCellsB.B_MAIN_PC_OFF_264) by (unfold raZ; rewrite R1; apply u64_lit; lia).
change (mkCfg (mkst regs (w64 YImgCellsB.B_WRAP_FPRINTF_PC) mem (seg_rom tfibsegs)) md) with (cfg_at tfibsegs A_icpt_fprintf regs mem md).
apply (FP ly S W regs mem md E zp p (ex 2 fs)).
- split; [exact HAR|]. split; [rewrite R1; exact (proj1 (proj2 (proj2 (proj2 ret_oks))))|]. split; [rewrite Hra; lia|].
split; [rewrite Hsp, <- Zminus_mod_idemp_l, U16; reflexivity|]. split; [rewrite Hsp; unfold sp_window_lo, sp_window_hi in *; lia|].
split; [rewrite Hsp; unfold top_ok in HTOP; lia|]. split; [unfold top_ok in HTOP; tauto|]. split; [unfold top_ok in HTOP; tauto|].
split; [rewrite Hsp; intros a Ha; apply Hwin; unfold DIAG_STK in Ha; lia|].
rewrite (ts_gp B HB), (ts_tp B HB). exact (conj R3 R4).
- exact R10.
- exact R11.
- exact R12.
- exact Hlen.
- exact Hnn.
- rewrite Hsp. lia.
- exact Hzp2.
- exact HBr.
- exact Htl.
- exact HM.
- exact Hfd2.
- exact HAI.
- intros regs' mem' md' HAR' HP Hsbm Ha0 HE' Hfr Hpres HAI'. unfold cfg_at. rewrite Hra. change (w64 YImgCellsB.B_MAIN_PC_OFF_264) with (Z_to_bv 64 (if false then YImgCellsB.B_MAIN_PC_OFF_288 else YImgCellsB.B_MAIN_PC_OFF_264)).
apply (exit2_tail_cf false E W regs' mem' md' ly S usp fs E0 (conj Ulo Uhi) U16 Htid).
+ unfold spZ. replace (getr regs' 2%bv) with (getr regs 2%bv) by (symmetry; exact (HP 2 ltac:(unfold acallee_saved; lia))). exact Hsp.
+ replace (getr regs' 3%bv) with (getr regs 3%bv) by (symmetry; exact (HP 3 ltac:(unfold acallee_saved; lia))). exact R3.
+ replace (getr regs' 4%bv) with (getr regs 4%bv) by (symmetry; exact (HP 4 ltac:(unfold acallee_saved; lia))). exact R4.
+ apply (img_kept_site E (w_H W) mem mem' (spZ regs - DIAG_STK) (spZ regs) (mem_ok_X_of_R E _ HM) Hfr). rewrite Hsp. unfold DIAG_STK, sp_window_lo in *. lia.
+ intros a Ha. pose proof (Hwin a Ha) as Pa. unfold sp_window_lo, sp_window_hi in Ulo, Uhi. apply Hpres; [lia | unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI; lia | exact Pa].
+ exact HAI'.
+ exact HAR'.
+ exact HTOP.
+ exact HE'.
+ intros a Ha. rewrite (Hfr a); [exact (HSO a Ha) | unfold STDOUT_LO, STDOUT_HI in Ha; lia | rewrite Hsp; unfold STDOUT_LO, STDOUT_HI, DIAG_STK, sp_window_lo in *; lia
| unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI, STDOUT_LO, STDOUT_HI in *; lia].
+ rewrite (sbm_fs_eq md md' Hsbm). exact Hfs.
Qed.

(* YD27.v:405-410. *)
Lemma tfib_rderr_leaf_cf_sec : fprintf_s_site_tfa_cf B est YImgCellsB.B_RODATA_0XD577 (strB "cli: read error on "%string) nlB -> rderr_leaf_tfa_cf B.
Proof.
intros FPR E W regs mem md ly S usp p zp fs E0 U U16 Htid R10 R11 R12 R1 Hsp R3 R4 Hzp1 Hzp2 Hnn Hlen HBr Htl HM Hwin HAI HAR HTOP Hfd2 Hfs.
unfold diag, msg_read_error.
exact (fpr_leaf_cf YImgCellsB.B_RODATA_0XD577 _ FPR E W regs mem md ly S usp p zp fs E0 U U16 Htid R10 R11 R12 R1 Hsp R3 R4 Hzp1 Hzp2 Hnn Hlen HBr Htl HM Hwin HAI HAR HTOP Hfd2 Hfs).
Qed.

(* YD27.v:411-444. *)
Lemma tfib_refused_leaf_cf_sec : refused_site_tfa_cf B est -> refused_leaf_tfa_cf B.
Proof.
intros RFS E W regs mem md ly S usp fs E0 [Ulo Uhi] U16 Htid R10 R11 R12 R1 Hsp R3 R4 HM Hwin HAI HAR HTOP Hfd2 Hfs.
pose proof (imgs_of_R E (w_H W) mem HM) as [HSO HSE].
assert (Hra : raZ regs = YImgCellsB.B_MAIN_PC_OFF_264) by (unfold raZ; rewrite R1; apply u64_lit; lia).
unfold diag. change (mkCfg (mkst regs (w64 YImgCellsB.B_WRAP_FPRINTF_PC) mem (seg_rom tfibsegs)) md) with (cfg_at tfibsegs A_icpt_fprintf regs mem md).
apply (RFS ly S W regs mem md E (ex 2 fs)).
- split; [exact HAR|]. split; [rewrite R1; exact (proj1 (proj2 (proj2 (proj2 ret_oks))))|]. split; [rewrite Hra; lia|].
split; [rewrite Hsp, <- Zminus_mod_idemp_l, U16; reflexivity|]. split; [rewrite Hsp; unfold sp_window_lo, sp_window_hi in *; lia|].
split; [rewrite Hsp; unfold top_ok in HTOP; lia|]. split; [unfold top_ok in HTOP; tauto|]. split; [unfold top_ok in HTOP; tauto|].
split; [rewrite Hsp; intros a Ha; apply Hwin; unfold DIAG_STK in Ha; lia|].
rewrite (ts_gp B HB), (ts_tp B HB). exact (conj R3 R4).
- exact R10.
- exact R11.
- exact R12.
- exact HM.
- exact Hfd2.
- exact HAI.
- intros regs' mem' md' HAR' HP Hsbm Ha0 HE' Hfr Hpres HAI'. unfold cfg_at. rewrite Hra. change (w64 YImgCellsB.B_MAIN_PC_OFF_264) with (Z_to_bv 64 (if false then YImgCellsB.B_MAIN_PC_OFF_288 else YImgCellsB.B_MAIN_PC_OFF_264)).
apply (exit2_tail_cf false E W regs' mem' md' ly S usp fs E0 (conj Ulo Uhi) U16 Htid).
+ unfold spZ. replace (getr regs' 2%bv) with (getr regs 2%bv) by (symmetry; exact (HP 2 ltac:(unfold acallee_saved; lia))). exact Hsp.
+ replace (getr regs' 3%bv) with (getr regs 3%bv) by (symmetry; exact (HP 3 ltac:(unfold acallee_saved; lia))). exact R3.
+ replace (getr regs' 4%bv) with (getr regs 4%bv) by (symmetry; exact (HP 4 ltac:(unfold acallee_saved; lia))). exact R4.
+ apply (img_kept_site E (w_H W) mem mem' (spZ regs - DIAG_STK) (spZ regs) (mem_ok_X_of_R E _ HM) Hfr). rewrite Hsp. unfold DIAG_STK, sp_window_lo in *. lia.
+ intros a Ha. pose proof (Hwin a Ha) as Pa. unfold sp_window_lo, sp_window_hi in Ulo, Uhi. apply Hpres; [lia | unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI; lia | exact Pa].
+ exact HAI'.
+ exact HAR'.
+ exact HTOP.
+ exact HE'.
+ intros a Ha. rewrite (Hfr a); [exact (HSO a Ha) | unfold STDOUT_LO, STDOUT_HI in Ha; lia | rewrite Hsp; unfold STDOUT_LO, STDOUT_HI, DIAG_STK, sp_window_lo in *; lia
| unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI, STDOUT_LO, STDOUT_HI in *; lia].
+ rewrite (sbm_fs_eq md md' Hsbm). exact Hfs.
Qed.

(* YD27.v:465-547. *)
Lemma tfib_cannot_open_cf_sec : fprintf_s_site_tfa_cf B est YImgCellsB.B_RODATA_0XD562 (strB "cli: cannot open "%string) nlB -> cannot_open_tfa_cf B.
Proof.
intros FPO sp inp xw xd W regs mem md ly a0 p e Hargv Hsp Hva Hve Hfit Hregs Hmem HG HR HAI HAR HTOP Hfs Hfds He.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
set (EL := YP08.E0 sp [a0; p] (in_envp inp) xw xd) in *. set (usp := bv_unsigned sp) in *.
set (E1 := ewset EL A_NEGE (errno_ret e)).
assert (E1_0 : bv_unsigned (ew E1 0) = usp) by (subst E1; rewrite ew_ewset_other by (unfold A_NEGE; lia); reflexivity).
assert (E1_41 : ew E1 A_NEGE = errno_ret e) by (subst E1; apply ew_ewset_same).
assert (Herr : bv_unsigned (errno_ret e) = 2 ^ 64 - e).
{ unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia. }
pose proof CO_checks as (WB1 & WB2 & GF1 & TIDf & WOK & M1eq & RV0 & RV1).
pose proof (st_ok_resume_atom tfibsegs A_NEGE fact_err EL ss_open regs (mrestrict (w_H W) mem) (errno_ret e) Hregs Hmem HG
(proj1 (proj2 (proj2 (proj2 (proj2 (proj2 S_CO1_facts)))))) ltac:(cbn [af_lo af_hi fact_err]; rewrite Herr; lia) ltac:(cbn; lia)
ltac:(cbn [af_al2 fact_err]; rewrite Z.pow_0_r; apply Z.mod_1_r)) as HS0.
fold E1 in HS0. change (resume ss_open (SOff A_NEGE 0) (ss_mem ss_open) _) with S_COr in HS0.
assert (HS1 : st_ok tfibsegs E1 S_CO (restrict (w_H W) (mkst (regupd regs 10%bv (errno_ret e)) (v_addi (Z_to_bv 64 (ss_pc ss_open)) 4) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx, S_CO_eq. apply (st_ok_app_regions E1 S_COr _ [R_errno] HS0 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 S_CO1_facts))))))).
- constructor; [apply region_ok_errno | constructor].
- cbn. split; [constructor | exact I].
- intros r1 r2 Hr1 Hr2. destruct Hr2 as [<-|[]].
pose proof (proj1 (forallb_forall _ _) (proj1 S_CO_ext) r1 Hr1) as Y. unfold ext_chk2 in Y. cbn [r_base R_errno r_lo r_hi] in Y.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_errno base_val].
assert (A1 : usp <= bv_unsigned (ew E1 1)) by (subst E1; rewrite ew_ewset_other by (unfold A_NEGE; lia); subst EL usp; rewrite (YP08.ew1 sp [a0; p] (in_envp inp) Hsp Hva Hve); unfold z_strs; lia).
assert (A2 : usp <= bv_unsigned (ew E1 2)) by (subst E1; rewrite ew_ewset_other by (unfold A_NEGE; lia); subst EL usp; rewrite (YP08.ew2' sp [a0; p] (in_envp inp) Hsp Hva Hve) by (cbn; lia);
pose proof (YP08.z_argv_bounds sp [a0; p] (in_envp inp) 1 ltac:(cbn; lia)) as [Z1 _]; unfold z_strs in Z1; lia).
assert (A6 : usp <= bv_unsigned (ew E1 6)) by (subst E1; rewrite ew_ewset_other by (unfold A_NEGE; lia); subst EL usp; exact (YD29.EL6 sp inp xw xd a0 p Hsp Hva Hve)).
unfold sp_window_lo in Ulo.
destruct (r_base r1) as [[|[|[|[|[|[|[|n]]]]]]]|]; try discriminate Y; cbn [base_val]; try (apply Z.leb_le in Y).
+ rewrite E1_0. right. lia.
+ right. lia.
+ right. lia.
+ right. lia.
+ apply orb_prop in Y as [Y|Y]; apply Z.leb_le in Y; lia. }
apply (SRr_srealizes tfibsegs W _ _ _ (co_run1 E1 W _ md HS1) HAI).
intros Wa ca _ HAIa (-> & ms1 & mat1 & -> & HSa & HFa & HFra). cbn [cfg_model ms_mem mkst] in HAIa, HFa, HFra |- *.
assert (HSb : st_ok tfibsegs E1 (add_cond S_CO1 cond_CO) (restrict (w_H W) ms1)).
{ apply (st_ok_add_cond tfibsegs E1 S_CO1 _ BC_GEU sv_nege (SLit LIT_M4095) HSa).
rewrite (nege_val E1 e He E1_41). cbn [sv_denot Sem.branch_taken]. unfold LIT_M4095.
unfold bv_ltu. rewrite !u64_lit by lia. destruct (Z.ltb_spec (2 ^ 64 - e) 18446744073709547521); [lia | reflexivity]. }
apply (SRr_srealizes tfibsegs W _ _ _ (co_run2 E1 W ms1 _ HSb) HAIa).
intros Wb cb _ HAIb (-> & ms2 & mat2 & -> & HS2 & HFb & HFrb). cbn [cfg_model] in HAIb.
pose proof S_COf_facts as (Ppc & Pra & Psp & Pa0 & Pa1 & Pa2 & Pgp & Ptp & Prv).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E1 S_COf ms2 HS2 Prv) as Hshape. rewrite Hshape, Ppc. change (Z_to_bv 64 YImgCellsB.B_WRAP_FPRINTF_PC) with (w64 YImgCellsB.B_WRAP_FPRINTF_PC).
pose proof (st_ok_mem_ok tfibsegs E1 S_COf _ HS2) as HM2. cbn [restrict ms_mem] in HM2.
assert (RG : forall r, getr (ms_regs ms2) r = sv_denot E1 (sr_get (ss_regs S_COf) r)) by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W) E1 S_COf ms2 r HS2)).
assert (HR2 : runs_at usp (mrestrict (w_H W) (ms_mem ms2)) (runs_main_tfa true sp [a0; p] (in_envp inp))).
{ eapply (runs_at_frame E1 (ss_facts S_COf) (ss_mem S_CO)); [exact (st_ok_facts_ok tfibsegs E1 S_COf _ HS2) | exact WB2 | exact HFrb | rewrite E1_0; lia |].
eapply (runs_at_frame E1 (ss_facts S_CO1) (ss_mem S_CO)); [exact (st_ok_facts_ok tfibsegs E1 S_CO1 _ HSa) | exact WB1 | exact HFra | rewrite E1_0; lia | exact HR]. }
pose proof (runs_at_nth _ _ _ 2 _ _ HR2 eq_refl) as HBr. cbn [nth] in HBr.
destruct S_COf_mem as (cs0 & Hhd & _).
pose proof (win0_present E1 (w_H W) (ms_mem ms2) (ss_mem S_COf) cs0 usp HM2 Hhd ltac:(destruct S_CO_hd as (_ & _ & _ & X); exact X) E1_0 (conj Ulo Uhi)) as Hwin2.
unfold diag, msg_cannot_open.
apply (fpr_leaf_cf YImgCellsB.B_RODATA_0XD562 _ FPO E1 W (ms_regs ms2) (ms_mem ms2) _ ly init_state usp p (z_argv usp [a0; p] (in_envp inp) 1) (in_fs inp) E1_0 (conj Ulo Uhi) U16).
- exact (tid_of_st_ok E1 S_COf _ HS2 TIDf).
- rewrite (RG 10%bv), Pa0. reflexivity.
- rewrite (RG 11%bv), Pa1. reflexivity.
- rewrite (RG 12%bv), Pa2. cbn [sv_denot]. rewrite Z.add_0_r. subst E1. rewrite ew_ewset_other by (unfold A_NEGE; lia).
subst EL. rewrite (YP08.ew2' sp [a0; p] (in_envp inp) Hsp Hva Hve) by (cbn; lia). reflexivity.
- rewrite (RG 1%bv), Pra. reflexivity.
- unfold spZ. rewrite (RG 2%bv), Psp. cbn [sv_denot]. rewrite E1_0. apply u64_lit. unfold sp_window_lo in Ulo. lia.
- rewrite (RG 3%bv), Pgp. reflexivity.
- rewrite (RG 4%bv), Ptp. reflexivity.
- pose proof (YP08.z_argv_bounds sp [a0; p] (in_envp inp) 1 ltac:(cbn; lia)) as [Z1 _]. unfold z_strs in Z1. subst usp. lia.
- exact (argv_str_fits' sp [a0; p] (in_envp inp) 1 Hfit ltac:(cbn; lia)).
- exact (argv_no_nul [a0; p] Hva 1 ltac:(cbn; lia)).
- exact (argv_str_len [a0; p] Hva 1 ltac:(cbn; lia)).
- exact HBr.
- subst usp. exact (argv_over_read sp (StackLayout.mkDraw (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0)) [a0; p] (in_envp inp) true _ 1 Hsp ltac:(cbn; lia) HR2).
- exact (mem_ok_sub tfibsegs E1 _ _ IMG_REGIONS img_sub_COf img_regions_wf HM2).
- exact Hwin2.
- exact HAIb.
- pose proof (st_ok_mem_ok tfibsegs E1 S_CO1 _ HSa) as HMa. cbn [restrict ms_mem] in HMa. rewrite M1eq in HMa.
destruct S_CO_hd as (cs1 & Hhd1 & Hne1 & _).
pose proof (win0_present E1 (w_H W) (ms_mem ms1) (ss_mem S_CO) cs1 usp HMa Hhd1 Hne1 E1_0 (conj Ulo Uhi)) as Hwin1.
apply (AR_after_run_cf B HB ARL ly init_state [] W E1 (ss_mem S_CO) (ms_mem ms1) (ms_mem ms2) _ mat2); [| exact WOK | rewrite E1_0; exact Ulo | rewrite E1_0; exact (top_ok_ceil _ _ HTOP) | exact HFb | rewrite E1_0; intros a Ha; exact (apresent_some' _ _ _ (Hwin2 a Ha))].
apply (AR_after_run_cf B HB ARL ly init_state [] W E1 (ss_mem S_CO) mem (ms_mem ms1) md mat1 HAR WOK); [rewrite E1_0; exact Ulo | rewrite E1_0; exact (top_ok_ceil _ _ HTOP) | exact HFa |].
rewrite E1_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin1 a Ha)).
- exact HTOP.
- rewrite !wvb_fds', Hfds. reflexivity.
- rewrite !wvb_fs'. exact Hfs.
Qed.

(* YD27.v:568-671. *)
Lemma tfib_usage_cf_sec : fprintf_s_site_tfa_cf B est YImgCellsB.B_RODATA_0X55CA (strB "usage: "%string) (strB " INPUT"%string ++ nlB) -> usage_tfa_cf B.
Proof.
intros FPU sp inp xw xd W ms md ly Hsp Hva Hve Hfit Hlen HS HR HAI HAR HTOP Hfs Hfds.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
set (argv := in_argv inp) in *. set (envp := in_envp inp) in *.
set (EL := YP08.E0 sp argv envp xw xd) in *. set (usp := bv_unsigned sp) in *.
assert (EL0 : bv_unsigned (ew EL 0) = usp) by reflexivity.
assert (Hargc : (1 <= length argv)%nat) by (pose proof (proj1 Hva); lia).
pose proof US_checks as (TIDf & NEus & WF0 & TID0).
pose proof (tid_of_st_ok EL (ss_main false) _ HS TID0) as Htid.
apply (SRr_srealizes tfibsegs W _ _ _ (us_run sp argv envp xw xd W ms md Hsp Hva Hve Hlen HS) HAI).
intros Wb cb _ HAIb (-> & ms2 & mat2 & -> & HS2 & HFb & HFrb). cbn [cfg_model] in HAIb.
pose proof S_US_facts as (Ppc & Pra & Psp & Pa0 & Pa1 & Pa2 & Pgp & Ptp & Ps0 & Prv & _).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) EL S_US ms2 HS2 Prv) as Hshape. rewrite Hshape, Ppc.
change (mkCfg (mkst (ms_regs ms2) (Z_to_bv 64 YImgCellsB.B_WRAP_FPRINTF_PC) (ms_mem ms2) (seg_rom tfibsegs)) _) with (cfg_at tfibsegs A_icpt_fprintf (ms_regs ms2) (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
pose proof (st_ok_mem_ok tfibsegs EL S_US _ HS2) as HM2. cbn [restrict ms_mem] in HM2.
assert (RG : forall r, getr (ms_regs ms2) r = sv_denot EL (sr_get (ss_regs S_US) r)) by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W) EL S_US ms2 r HS2)).
set (regs := ms_regs ms2) in *. set (mem := ms_mem ms2) in *.
assert (HR2 : runs_at usp (mrestrict (w_H W) mem) (runs_main_tfa false sp argv envp)).
{ pose proof S_CO_ext as (_ & _ & _ & _ & WBu & WBp & _).
eapply (runs_at_frame EL (ss_facts S_US) (ss_mem (ss_main false))); [exact (st_ok_facts_ok tfibsegs EL S_US _ HS2) | | exact HFrb | rewrite EL0; lia | exact HR].
vm_compute. reflexivity. }
pose proof (runs_at_nth _ _ _ 1 _ _ HR2 eq_refl) as HBr. cbn [nth] in HBr.
pose proof S_US_mem as (Hhd & _ & _).
pose proof (win0_present EL (w_H W) mem (ss_mem S_US) JFR_chunks usp HM2 Hhd NEus EL0 (conj Ulo Uhi)) as Hwin2.
pose proof (jfr_of_region EL (w_H W) mem (ss_mem S_US) (-65536) 0 (-65536) 0 usp HM2 ltac:(rewrite <- Hhd; destruct (ss_mem S_US); [exact (NEus eq_refl) | left; reflexivity]) EL0) as HJ2.
pose proof (mem_ok_sub tfibsegs EL _ _ IMG_REGIONS img_sub_US img_regions_wf HM2) as HMR. pose proof (imgs_of_R EL (w_H W) mem HMR) as [HSO HSE].
assert (HAR2 : ARcf tfibsegs B ly init_state [] W mem (with_vm_backing (m_vm_lazy md) mat2 md)).
{ apply (AR_after_run_cf B HB ARL ly init_state [] W EL (ss_mem (ss_main false)) (ms_mem ms) mem md mat2 HAR (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 S_CO_ext))))))); [rewrite EL0; exact Ulo | rewrite EL0; exact (top_ok_ceil _ _ HTOP) | exact HFb |].
rewrite EL0. intros a Ha. exact (apresent_some' _ _ _ (Hwin2 a Ha)). }
assert (Hsp2 : spZ regs = usp - 128) by (unfold spZ; rewrite (RG 2%bv), Psp; cbn [sv_denot]; rewrite EL0; apply u64_lit; unfold sp_window_lo in Ulo; lia).
assert (Hra : raZ regs = YImgCellsB.B_MAIN_PC_OFF_1B4) by (unfold raZ; rewrite (RG 1%bv), Pra; reflexivity).
assert (E1z : bv_unsigned (ew EL 1) = z_argv usp argv envp 0).
{ subst EL usp. rewrite (YP08.ew1 sp argv envp Hsp Hva Hve). unfold z_argv. rewrite firstn_O. cbn [total_arg_bytes_nat fold_right]. lia. }
unfold diag, msg_usage.
apply (FPU ly init_state W regs mem _ EL (z_argv usp argv envp 0) (nth 0 argv []) (ex 2 (in_fs inp))).
- split; [exact HAR2|]. split; [rewrite (RG 1%bv), Pra; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 ret_oks))))))|]. split; [rewrite Hra; lia|].
split; [rewrite Hsp2, <- Zminus_mod_idemp_l, U16; reflexivity|]. split; [rewrite Hsp2; unfold sp_window_lo, sp_window_hi in *; lia|].
split; [rewrite Hsp2; unfold top_ok in HTOP; lia|]. split; [unfold top_ok in HTOP; tauto|]. split; [unfold top_ok in HTOP; tauto|].
split; [rewrite Hsp2; intros a Ha; apply Hwin2; unfold DIAG_STK in Ha; lia|].
rewrite (ts_gp B HB), (ts_tp B HB), (RG 3%bv), (RG 4%bv), Pgp, Ptp. split; reflexivity.
- rewrite (RG 10%bv), Pa0. reflexivity.
- rewrite (RG 11%bv), Pa1. reflexivity.
- rewrite (RG 12%bv), Pa2. cbn [sv_denot]. rewrite Z.add_0_r, E1z. reflexivity.
- exact (argv_str_len argv Hva 0 ltac:(lia)).
- exact (argv_no_nul argv Hva 0 ltac:(lia)).
- rewrite Hsp2. pose proof (YP08.z_argv_bounds sp argv envp 0 ltac:(lia)) as [Z1 _]. unfold z_strs in Z1. subst usp. lia.
- exact (argv_str_fits' sp argv envp 0 Hfit ltac:(lia)).
- exact HBr.
- subst usp. exact (argv_over_read sp (StackLayout.mkDraw (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0)) argv envp false _ 0 Hsp ltac:(lia) HR2).
- exact HMR.
- rewrite wvb_fds', Hfds. reflexivity.
- exact HAIb.
-
intros regs' mem' md' HAR' HP Hsbm Ha0 HE' Hfr Hpres HAI'. unfold cfg_at. rewrite Hra.
assert (P2 : getr regs' 2%bv = getr regs 2%bv) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs' 3%bv = getr regs 3%bv) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs' 4%bv = getr regs 4%bv) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs' 8%bv = getr regs 8%bv) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (Hwin' : forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem' a).
{ intros a Ha. pose proof (Hwin2 a Ha) as Pa. unfold sp_window_lo, sp_window_hi in Ulo, Uhi. apply Hpres; [lia | unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI; lia | exact Pa]. }
assert (HMX : mem_ok tfibsegs EL (mrestrict (w_H W) mem') IMG_X).
{ apply (img_kept_site EL (w_H W) mem mem' (spZ regs - DIAG_STK) (spZ regs) (mem_ok_X_of_R EL _ HMR) Hfr). rewrite Hsp2. unfold DIAG_STK, sp_window_lo in *. lia. }
assert (HJ' : Forall (YP09.chunk_ok tfibsegs EL (mrestrict (w_H W) mem') usp) JFR_chunks).
{ apply (jfr_kept_site EL (w_H W) mem mem' usp (spZ regs - DIAG_STK) (spZ regs) HJ2 Hfr); [rewrite Hsp2; lia | exact (conj Ulo Uhi)]. }
pose proof (regs_ok_J EL regs' (-128) usp EL0 ltac:(unfold spZ; rewrite P2; fold (spZ regs); rewrite Hsp2; lia) Ulo ltac:(lia)
ltac:(rewrite P3, (RG 3%bv), Pgp; reflexivity) ltac:(rewrite P4, (RG 4%bv), Ptp; reflexivity)) as HRJ.
pose proof (regs_ok_ovr (E_J EL regs') (jregs (-128)) regs' 8%bv (SLit 2) HRJ eq_refl ltac:(rewrite P8, (RG 8%bv), Ps0; reflexivity)) as HRJ'.
pose proof (st_ok_J IMG_X EL regs' _ (-128) YImgCellsB.B_MAIN_PC_OFF_1B4 usp true (w_H W) mem' (or_introl eq_refl) HRJ' EL0 Ulo ltac:(left; reflexivity) HMX Hwin' ltac:(intros _; exact HJ')) as HSJ.
rewrite <- (proj1 (proj2 (proj2 (proj2 S_J_defs)))), <- restrict_mkst_fx in HSJ.
set (E2 := E_J EL regs') in *.
assert (E2_0 : bv_unsigned (ew E2 0) = usp) by (subst E2; rewrite E_J_old by (unfold KJ; lia); exact EL0).
apply (srz_conseq tfibsegs _ (wr ch_stdout (concat (repeat line0 (0 - 1))) (ex 2 (in_fs inp)))).
2:{ cbn [Nat.sub repeat concat]. unfold wr. cbn [map]. apply t_emit_nil_eq. unfold ex, t_exit. apply t_emit_has_nil. }
pose proof S_JFc_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & _).
apply (run_to_exit_cf B HB xst est XFR ESTF EXS 3%nat S_JU E2 W _ md' ly init_state usp (in_fs inp) 2 0%nat IMG_X (-128) true ltac:(lia));
[| | left; reflexivity | | right; reflexivity | ..].
+ cbn [nth XSTS]. rewrite MU. exact (ju_run E2 W _ md' HSJ).
+ exact MU.
+ left. reflexivity.
+ exact E2_0.
+ exact (conj Ulo Uhi).
+ exact U16.
+ subst E2. rewrite E_J_old by (unfold KJ; lia). exact Htid.
+ reflexivity.
+ right. reflexivity.
+ exact HAI'.
+ exact HAR'.
+ exact HTOP.
+ exact HE'.
+ left. split; [reflexivity|]. cbn [ms_mem mkst]. intros a Ha.
rewrite (Hfr a); [exact (HSO a Ha) | unfold STDOUT_LO, STDOUT_HI in Ha; lia | rewrite Hsp2; unfold STDOUT_LO, STDOUT_HI, DIAG_STK, sp_window_lo in *; lia
| unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI, STDOUT_LO, STDOUT_HI in *; lia].
+ intros Hk. exfalso. lia.
+ rewrite (sbm_fs_eq _ md' Hsbm), wvb_fs'. exact Hfs.
Qed.

(* YD27.v:714-861. The tail: fwrite the diagnostic, free the read buffer (CwSites' free_site_cf B NP: its drv_pre_cf
   takes NP S from the tail and qtight from drv_minv_cf, its live bound from blocks S = [(pb, cap)]), then exit 2.
   cgif's ml_free served only its event bound and is gone; no headroom number occurs. *)
Lemma fw_leaf_cf : fwrite_site_tfa_cf B est -> free_site_nomn_cf B NP ->
forall (b : bool) (E : YP0m.env) sp inp (a0 p data : list byte) (W : world tfibsegs) ms md ly S (pb : sptr) (cap : Z),
valid_sp sp -> bv_unsigned sp <= bv_unsigned (ew E 6) -> bv_unsigned (ew E 0) = bv_unsigned sp ->
tail_at_pinv_B B NP (if b then S_SHORT else S_OVR) E sp inp a0 p data W ms md ly S pb cap ->
srealizes tfibsegs (mkCfg ms md) (diag (if b then msg_short else msg_overrun) (in_fs inp)).
Proof.
intros FWS FREE b E sp inp a0 p data W ms md ly S pb cap Hsp HU6 E0 HT.
destruct HT as (HS & E41 & E42 & HR & HAI & HAR & HNP & HTOP & Hbl & Hcap & Hdl & Hblk & Hfs & Hfds & Hminv & HPI & Hxs & _).
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (proj1 (@YM05.alloc_ceiling_value rc)) as CV.
pose proof (top_ok_ceil _ _ HTOP) as HCT. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
set (usp := bv_unsigned sp) in *. set (ss := if b then S_SHORT else S_OVR) in *.
pose proof (FW_facts b) as F. cbv zeta in F. fold ss in F. destruct F as (Ppc & Pa0 & Pa1 & Pa2 & Pa3 & Pra & Psp & Pgp & Ptp & Ps0 & Ps1 & Prv & TIDf & Hhd2 & Hlen2 & _).
destruct (FW_hd b) as (cs0 & Hhd). fold ss in Hhd.
pose proof msgs_img as (_ & IMs & IMo & _ & LMs & LMo).
set (msg := if b then msg_short else msg_overrun). set (msgp := if b then YImgCellsB.B_RODATA_0XF6CD else YImgCellsB.B_RODATA_0X55DB) in *.
assert (IM : img_msg_chk msgp msg = true /\ length msg = 31%nat) by (subst msg msgp; destruct b; split; assumption). destruct IM as [IM LM].
pose proof (tid_of_st_ok E ss _ HS TIDf) as Htid.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E ss ms HS Prv) as Hshape.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as HM. cbn [restrict ms_mem] in HM.
assert (RG : forall r, getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r)) by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W) E ss ms r HS)).
set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *.
pose proof (win2_present E (w_H W) mem (ss_mem ss) cs0 usp HM Hhd Hhd2 Hlen2 E0 (conj Ulo Uhi)) as Hwin.
pose proof (jfr_of_region E (w_H W) mem (ss_mem ss) (-128) 0 (-128) 0 usp HM
ltac:(rewrite <- Hhd2; destruct (ss_mem ss) as [|r [|r' rs]]; [cbn in Hlen2; lia | cbn in Hlen2; lia | right; left; reflexivity]) E0) as HJ.
pose proof (mem_ok_sub tfibsegs E _ _ IMG_REGIONS (img_sub_FW b) img_regions_wf HM) as HMR. pose proof (imgs_of_R E (w_H W) mem HMR) as [HSO HSE].
assert (Hsp2 : spZ regs = usp - 128) by (unfold spZ; rewrite (RG 2%bv), Psp; cbn [sv_denot]; rewrite E0; apply u64_lit; unfold sp_window_lo in Ulo; lia).
assert (Hra : raZ regs = YImgCellsB.B_MAIN_PC_OFF_1F4) by (unfold raZ; rewrite (RG 1%bv), Pra; reflexivity).
assert (Hin : In (sptr_addr B ly pb, cap) (ablocks B ly S)) by (unfold ablocks; rewrite Hbl; left; reflexivity).
pose proof (alc_blocks _ _ ARL ly S [] W mem md _ _ HAR Hin) as (_ & Hb4096 & Hbce & _).
assert (NIMG : forall a, sptr_addr B ly pb <= a < sptr_addr B ly pb + req_size cap -> ~ in_img tfibsegs a).
{ intros a Ha. exact (proj2 (alc_client_img _ _ ARL ly S [] W mem md a HAR (or_introl (ex_intro _ _ (ex_intro _ cap (conj Hin Ha)))))). }
assert (Hcap' : cap <= req_size cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
rewrite Hshape, Ppc. unfold diag.
change (mkCfg (mkst regs (Z_to_bv 64 A_icpt_fwrite) mem (seg_rom tfibsegs)) md) with (cfg_at tfibsegs A_icpt_fwrite regs mem md).
apply (FWS ly S W regs mem md E msgp 31 msg (ex 2 (in_fs inp))).
- split; [exact HAR|]. split; [rewrite (RG 1%bv), Pra; exact (proj1 (proj2 (proj2 (proj2 (proj2 ret_oks)))))|]. split; [rewrite Hra; lia|].
split; [rewrite Hsp2, <- Zminus_mod_idemp_l, U16; reflexivity|]. split; [rewrite Hsp2; unfold sp_window_lo, sp_window_hi in *; lia|].
split; [rewrite Hsp2; unfold top_ok in HTOP; lia|]. split; [unfold top_ok in HTOP; tauto|]. split; [unfold top_ok in HTOP; tauto|].
split; [rewrite Hsp2; intros a Ha; apply Hwin; unfold DIAG_STK in Ha; lia|].
rewrite (ts_gp B HB), (ts_tp B HB), (RG 3%bv), (RG 4%bv), Pgp, Ptp. split; reflexivity.
- rewrite (RG 10%bv), Pa0. reflexivity.
- rewrite (RG 11%bv), Pa1. reflexivity.
- rewrite (RG 12%bv), Pa2. reflexivity.
- rewrite (RG 13%bv), Pa3. reflexivity.
- rewrite LM. reflexivity.
- lia.
- subst msgp; destruct b; lia.
- subst msgp; destruct b; lia.
- subst msgp; destruct b; [right | left]; lia.
- intros i Hi. apply (img_msg_chk_sound _ _ IM i Hi).
- exact HMR.
- rewrite Hfds. reflexivity.
- exact HAI.
-
intros regs' mem' md' HAR' HP Hsbm Ha0 HE' Hfr Hpres HAI'. unfold cfg_at. rewrite Hra.
assert (P2 : getr regs' 2%bv = getr regs 2%bv) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs' 3%bv = getr regs 3%bv) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs' 4%bv = getr regs 4%bv) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs' 8%bv = getr regs 8%bv) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs' 9%bv = getr regs 9%bv) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
assert (Hwin' : forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem' a).
{ intros a Ha. pose proof (Hwin a Ha) as Pa. unfold sp_window_lo, sp_window_hi in Ulo, Uhi. apply Hpres; [lia | unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI; lia | exact Pa]. }
assert (HMX : mem_ok tfibsegs E (mrestrict (w_H W) mem') IMG_X).
{ apply (img_kept_site E (w_H W) mem mem' (spZ regs - DIAG_STK) (spZ regs) (mem_ok_X_of_R E _ HMR) Hfr). rewrite Hsp2. unfold DIAG_STK, sp_window_lo in *. lia. }
assert (HJ' : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) mem') usp) JFR_chunks).
{ apply (jfr_kept_site E (w_H W) mem mem' usp (spZ regs - DIAG_STK) (spZ regs) HJ Hfr); [rewrite Hsp2; lia | exact (conj Ulo Uhi)]. }
assert (HSO' : stdout_img (w_H W) mem').
{ intros a Ha. rewrite (Hfr a); [exact (HSO a Ha) | unfold STDOUT_LO, STDOUT_HI in Ha; lia | rewrite Hsp2; unfold STDOUT_LO, STDOUT_HI, DIAG_STK, sp_window_lo in *; lia
| unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI, STDOUT_LO, STDOUT_HI in *; lia]. }
pose proof (regs_ok_J E regs' (-128) usp E0 ltac:(unfold spZ; rewrite P2; fold (spZ regs); rewrite Hsp2; lia) Ulo ltac:(lia)
ltac:(rewrite P3, (RG 3%bv), Pgp; reflexivity) ltac:(rewrite P4, (RG 4%bv), Ptp; reflexivity)) as HRJ.
pose proof (regs_ok_ovr (E_J E regs') (jregs (-128)) regs' 8%bv (SLit 2) HRJ eq_refl ltac:(rewrite P8, (RG 8%bv), Ps0; reflexivity)) as HRJ'.
pose proof (regs_ok_ovr (E_J E regs') _ regs' 9%bv (SOff A_BUF 0) HRJ' eq_refl ltac:(rewrite P9, (RG 9%bv), Ps1; cbn [sv_denot]; rewrite E_J_old by (unfold KJ, A_BUF; lia); reflexivity)) as HRJ''.
pose proof (st_ok_J IMG_X E regs' _ (-128) YImgCellsB.B_MAIN_PC_OFF_1F4 usp true (w_H W) mem' (or_introl eq_refl) HRJ'' E0 Ulo ltac:(left; reflexivity) HMX Hwin' ltac:(intros _; exact HJ')) as HSJ.
rewrite <- (proj2 (proj2 (proj2 (proj2 S_J_defs)))), <- restrict_mkst_fx in HSJ.
set (E2 := E_J E regs') in *.
assert (E2old : forall j, (j < KJ)%nat -> ew E2 j = ew E j) by (intros j Hj; subst E2; apply E_J_old; exact Hj).
assert (E2_0 : bv_unsigned (ew E2 0) = usp) by (rewrite E2old by (unfold KJ; lia); exact E0).
assert (E2_6 : usp <= bv_unsigned (ew E2 6)) by (rewrite E2old by (unfold KJ; lia); exact HU6).
pose proof S_JFc_facts as (Qpc & Qa0 & Qra & Qsp & Qs0 & Qgp & Qtp & QM & Qrv & QMr & QMf & _).
apply (SRr_srealizes tfibsegs W _ _ _ (jf_run E2 W _ md' HSJ) HAI').
intros W1 c1 _ HAI1 (-> & msc & matc & -> & HSc & HFc & HFrc). cbn [cfg_model ms_mem mkst] in HAI1, HFc, HFrc.
set (md1 := with_vm_backing (m_vm_lazy md') matc md') in *.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E2 S_JFc msc HSc Qrv) as Hshape1.
pose proof (st_ok_mem_ok tfibsegs E2 S_JFc _ HSc) as HMc. cbn [restrict ms_mem] in HMc. rewrite QM in HMc.
assert (RG1 : forall r, getr (ms_regs msc) r = sv_denot E2 (sr_get (ss_regs S_JFc) r)) by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W) E2 S_JFc msc r HSc)).
pose proof (jmem_present (-128) true E2 (w_H W) (ms_mem msc) usp HMc E2_0 (conj Ulo Uhi) ltac:(left; reflexivity)) as Hwin1.
assert (HAR1 : ARcf tfibsegs B ly S [] W (ms_mem msc) md1).
{ apply (AR_after_run_cf B HB ARL ly S [] W E2 (jmem (-128) true) mem' (ms_mem msc) md' matc HAR' (proj1 (jmem_checks (-128) true ltac:(left; reflexivity)))); [rewrite E2_0; exact Ulo | rewrite E2_0; exact (top_ok_ceil _ _ HTOP) | exact HFc |].
rewrite E2_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin1 a Ha)). }
pose proof (jmem_checks (-128) true ltac:(left; reflexivity)) as (JWOK & JSEK & JSXK & _).
assert (HE1 : est (w_H W) (ms_mem msc)) by exact (est_frame_run_cf est ESTF (w_H W) E2 (jmem (-128) true) _ _ HFrc JSEK ltac:(rewrite E2_0; exact Ulo) HE').
assert (HSO1 : so_state xst 0%nat (w_H W) (ms_mem msc)) by exact (so_state_run_cf xst XFR 0%nat (w_H W) E2 (jmem (-128) true) _ _ HFrc JSXK ltac:(rewrite E2_0; exact Ulo) (or_introl (conj eq_refl HSO'))).
assert (Hsp1 : spZ (ms_regs msc) = usp + -128) by (unfold spZ; rewrite (RG1 2%bv), Qsp; cbn [sv_denot]; rewrite E2_0; apply u64_lit; unfold sp_window_lo in Ulo; lia).
assert (Hra1 : raZ (ms_regs msc) = RA_JF) by (unfold raZ; rewrite (RG1 1%bv), Qra; reflexivity).
rewrite Hshape1, Qpc.
replace (Z_to_bv 64 YImgCellsB.B_WRAP_FREE_PC) with (w64 (pc_wrap_free (as_code B))) by (rewrite (ts_code B HB); reflexivity).
change (mkCfg (mkst (ms_regs msc) (w64 (pc_wrap_free (as_code B))) (ms_mem msc) (seg_rom tfibsegs)) md1) with (cfg_at tfibsegs (pc_wrap_free (as_code B)) (ms_regs msc) (ms_mem msc) md1).
eapply (YA0nH.SRrG_srealizes tfibsegs (YA0nH.wle' tfibsegs YGcfRehidePost.RZ_cf) W
  (cfg_at tfibsegs (pc_wrap_free (as_code B)) (ms_regs msc) (ms_mem msc) md1)); [| exact HAI1 |].
{ eapply (FREE ly S W (ms_regs msc) (ms_mem msc) md1 pb cap).
- split; [exact HAR1|]. split; [unfold top_ok in *; tauto|].
split; [rewrite (RG1 1%bv), Qra; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ret_oks))))))|]. split; [rewrite Hra1; unfold RA_JF; lia|].
split; [rewrite Hsp1; rewrite <- Zplus_mod_idemp_l, U16; reflexivity|].
split; [rewrite Hsp1; unfold sp_window_lo in *; lia|]. split; [rewrite Hsp1; unfold top_ok in HTOP; lia|].
split; [rewrite Hsp1; intros a Ha; apply Hwin1; unfold ASTACK in Ha; lia|].
split; [rewrite (ts_gp B HB), (RG1 3%bv), Qgp; reflexivity|]. split; [rewrite (ts_tp B HB), (RG1 4%bv), Qtp; reflexivity|].
split; [unfold s0Z; rewrite (RG1 8%bv), Qs0; cbn [sv_denot]; rewrite u64_lit by lia; lia|].
split; [unfold drv_minv_cf in Hminv; tauto|]. split; [exact HNP|]. split; [exact Hxs|].
(* the hull from A18's base at the tail (drv_secs_cf in drv_minv_cf, 65536 <= cap <= 2 ^ 26) and the read-only bytes
   off jmem's image cells; memnorm is not carried here (the TEMPORARY free form) *)
split; [exact (proj1 (PresetDrvHull.drv_cf_hull_ok_drv_preset S cap (proj2 (proj2 (proj2 (proj2 (proj2 Hminv))))) Hcap))|].
exact (PresetDrvAroB.drv_arodata_mem B HB (jmem (-128) true) E2 (w_H W) (ms_mem msc) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) HMc).
- rewrite Hbl. cbn. lia.
- rewrite Hbl. left. reflexivity.
- rewrite (RG1 10%bv), Qa0. cbn [sv_denot]. rewrite Z.add_0_r, E2old by (unfold KJ, A_BUF; lia). unfold w64. rewrite <- E41, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (ts_code B HB), Hra1. apply (ts_universe_drv B HB). cbn. tauto.
- rewrite (ts_code B HB). apply (ts_universe_drv B HB). cbn. tauto. }
cbv beta. intros W2 c2 Hwle2 HAI2 (ly6 & S6 & regs6 & mem6 & md6 & trc6 & tr6 & Htrc6 & Hpath6 & -> & HPOST6 & HQT6 & HRM6 & HXS6 & _). cbn [cfg_model] in HAI2.
unfold cfg_at. rewrite Hra1.
pose proof HPOST6 as (HAR6 & Hlyle6 & _ & HP6 & Hio6 & Hfr6 & Hsc6).
destruct (same_io_fs_fds _ _ Hio6) as [Efs6 Efds6].
assert (HEb : forall a, sptr_addr B ly pb <= a < sptr_addr B ly pb + req_size cap -> a < alloc_ceiling /\ ~ in_img tfibsegs a) by (intros a Ha; split; [lia | exact (NIMG a Ha)]).
destruct (site_keep_free_cf_rh ly S W (ms_mem msc) md1 ly6 S6 W2 (ms_regs msc) regs6 mem6 md6 _ usp 0%nat HPOST6 HAR1 HEb ltac:(rewrite Hsp1; lia) Ulo HE1 HSO1) as [HE6 HSO6].
pose proof jf_checks as (FK1 & FK2 & FK3 & FK4 & FK5 & FKsub).
pose proof (drv_after_call_cf_rh B HB ARL K_JF E2 S_JFc msc ly S [] W md1 (fun a => sptr_addr B ly pb <= a < sptr_addr B ly pb + req_size cap)
ly6 S6 W2 regs6 mem6 md6 (JFR :: IMG_X) RA_JF usp (-128) HSc Qrv FK1 FK2 FK3 FK4 FKsub Qra HPOST6 HAR1 HEb
FK5 E2_0 E2_6 Hsp1 ltac:(lia) Ulo HCT ltac:(intros a Ha; apply Hwin1; lia)) as HS7.
rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 S_Jx_eq)))))) in HS7.
set (E6 := havoc E2 K_JF (map (getr regs6) CLOB)) in *.
assert (E6old : forall j, (j < K_JF)%nat -> ew E6 j = ew E2 j) by (intros j Hj; subst E6; apply ew_havoc_old; exact Hj).
assert (E6_0 : bv_unsigned (ew E6 0) = usp) by (rewrite E6old by (unfold K_JF; lia); exact E2_0).
apply (srz_conseq tfibsegs _ (wr ch_stdout (concat (repeat line0 (0 - 1))) (ex 2 (in_fs inp)))).
2:{ cbn [Nat.sub repeat concat]. unfold wr. cbn [map]. apply t_emit_nil_eq. unfold ex, t_exit. apply t_emit_has_nil. }
apply (run_to_exit_cf B HB xst est XFR ESTF EXS 4%nat S_JFr E6 W2 _ md6 ly6 S6 usp (in_fs inp) 2 0%nat IMG_X (-128) true ltac:(lia));
[| | left; reflexivity | | right; reflexivity | ..].
+ cbn [nth XSTS]. rewrite QMr. exact (jfx_run E6 W2 _ md6 HS7).
+ exact QMr.
+ left. reflexivity.
+ exact E6_0.
+ exact (conj Ulo Uhi).
+ exact U16.
+ rewrite E6old by (unfold K_JF; lia). rewrite E2old by (unfold KJ; lia). exact Htid.
+ reflexivity.
+ right. reflexivity.
+ exact HAI2.
+ exact HAR6.
+ exact (top_ok_le _ _ _ _ Hlyle6 HTOP).
+ exact HE6.
+ exact HSO6.
+ intros Hk. exfalso. lia.
+ rewrite Efs6. subst md1. rewrite wvb_fs', (sbm_fs_eq _ md' Hsbm). exact Hfs.
Qed.

(* YD27.v:862-877. *)
Lemma tfib_short_leaf_cf_sec : fwrite_site_tfa_cf B est -> free_site_nomn_cf B NP -> short_leaf_tfa_cf B NP.
Proof.
intros FWS FREE sp inp xw xd ws W ms md ly S a0 p data pb cap Hargv Hsp Hva Hve Hvfs Hlk Hdl HT.
apply (fw_leaf_cf FWS FREE true (havoc (YP08.E0 sp [a0; p] (in_envp inp) xw xd) K_M1 ws) sp inp a0 p data W ms md ly S pb cap Hsp).
- rewrite ew_havoc_old by (unfold K_M1; lia). exact (YD29.EL6 sp inp xw xd a0 p Hsp Hva Hve).
- rewrite ew_havoc_old by (unfold K_M1; lia). reflexivity.
- exact HT.
Qed.

Lemma tfib_overrun_leaf_cf_sec : fwrite_site_tfa_cf B est -> free_site_nomn_cf B NP -> overrun_leaf_tfa_cf B NP.
Proof.
intros FWS FREE sp inp xw xd ws W ms md ly S a0 p data pb cap Hargv Hsp Hva Hve Hvfs Hlk Hdl HT.
apply (fw_leaf_cf FWS FREE false (edset (havoc (YP08.E0 sp [a0; p] (in_envp inp) xw xd) K_M1 ws) 2 data) sp inp a0 p data W ms md ly S pb cap Hsp).
- cbn [ew edset]. rewrite ew_havoc_old by (unfold K_M1; lia). exact (YD29.EL6 sp inp xw xd a0 p Hsp Hva Hve).
- cbn [ew edset]. rewrite ew_havoc_old by (unfold K_M1; lia). reflexivity.
- exact HT.
Qed.
End R.
End P.

(* ---------------------------------------------------------------------- *)
(* 5. The closed results. *)
Theorem tfib_malloc_site_cf_B_holds : tfib_malloc_site_cf_B.
Proof. intros fx rc ci cp B NP NPT HL AL AMALLOC. exact (tfib_malloc_site_cf_sec B NP NPT HL AL AMALLOC). Qed.

Theorem tfib_memcpy_site_cf_B_holds : tfib_memcpy_site_cf_B.
Proof. intros fx rc ci cp B AICPY. exact (tfib_memcpy_site_cf_sec B AICPY). Qed.

Theorem tfib_read_check_cf_B_holds : tfib_read_check_cf_B.
Proof. intros fx rc ci cp B ARD. exact (tfib_read_check_cf_sec B ARD). Qed.

(* fpr_leaf_cf and the three leaves on it abstract the Section's NP as an unused, non-dependent argument (their
   statements do not mention it); any predicate fills it. *)
Theorem tfib_rderr_leaf_cf_B_holds : tfib_rderr_leaf_cf_B.
Proof. intros fx rc ci cp B xst est HB XFR ESTF FPR EXS. eapply tfib_rderr_leaf_cf_sec; try eassumption; exact (fun _ => True). Qed.

Theorem tfib_refused_leaf_cf_B_holds : tfib_refused_leaf_cf_B.
Proof. intros fx rc ci cp B xst est HB XFR ESTF RFS EXS. eapply tfib_refused_leaf_cf_sec; try eassumption; exact (fun _ => True). Qed.

Theorem tfib_cannot_open_cf_B_holds : tfib_cannot_open_cf_B.
Proof. intros fx rc ci cp B xst est HB XFR ESTF FPO EXS. eapply tfib_cannot_open_cf_sec; try eassumption; exact (fun _ => True). Qed.

Theorem tfib_usage_cf_B_holds : tfib_usage_cf_B.
Proof. intros fx rc ci cp B xst est HB XFR ESTF FPU EXS. eapply tfib_usage_cf_sec; eassumption. Qed.

Theorem tfib_short_leaf_cf_B_holds : tfib_short_leaf_cf_B.
Proof. intros fx rc ci cp B NP xst est HB XFR ESTF FWS EXS FREE. eapply tfib_short_leaf_cf_sec; eassumption. Qed.

Theorem tfib_overrun_leaf_cf_B_holds : tfib_overrun_leaf_cf_B.
Proof. intros fx rc ci cp B NP xst est HB XFR ESTF FWS EXS FREE. eapply tfib_overrun_leaf_cf_sec; eassumption. Qed.

Print Assumptions tfib_memcpy_site_cf_B_holds.
Print Assumptions tfib_read_check_cf_B_holds.
Print Assumptions tfib_short_leaf_cf_B_holds.
Print Assumptions tfib_overrun_leaf_cf_B_holds.
