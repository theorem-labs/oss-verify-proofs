(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0q YA0m YA0k YP0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE2y AE3i AE2l AE2h AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2g AE2j AE2d.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Syscall.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05 YK0r YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK18 YI17.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac INL := cbn; repeat (first [left; reflexivity | right]).
Lemma SRr_srz : forall segs (W : world segs) (c : config) (R : world segs -> config -> Prop) (T : TSet),
SRr segs W c R -> AI segs (w_H W) (w_A W) (cfg_model c) ->
(forall W' c', wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') -> R W' c' -> srealizes segs c' T) ->
srealizes segs c T.
Proof. intros segs W c R T HS HAI HK. exact (HS HAI T HK). Qed.
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variable cval : Z.
Let sp0 : Z := spZ regs.
Let H := w_H W.
Let m0 := mrestrict H mem.
Let FOP_WIN : Z := AE2a.FOP_WIN.
Hypothesis HAR : AR tfibsegs B ly S W mem md.
Hypothesis Hra : YK0s.ret_ok (getr regs 1).
Hypothesis Hal16 : sp0 mod 16 = 0.
Hypothesis Hslo : ly_stk_lo ly + FOP_WIN <= sp0.
Hypothesis Hshi : sp0 <= ly_stk_hi ly.
Hypothesis Hpres : forall a, sp0 - FOP_WIN <= a < sp0 -> apresent H mem a.
Hypothesis Hgp : getr regs 3 = w64 (as_gp B).
Hypothesis Htp : getr regs 4 = w64 (as_tp B).
Hypothesis G10 : getr regs 10 = w64 A_PATH.
Hypothesis G11 : getr regs 11 = w64 A_WB.
Hypothesis HIO : cells_hold m0 io_cells.
Hypothesis HSTC : cells_hold m0 st_cells.
Hypothesis HIMG : ro_img m0.
Hypothesis Hcan1 : val_mem tfibsegs m0 A_GOT_canary 8 A_canary.
Hypothesis Hcan2 : val_mem tfibsegs m0 A_canary 8 cval.
Hypothesis Hcv : 0 <= cval < 2 ^ 64.
Hypothesis Henv0 : val_mem tfibsegs m0 A_threaded 1 0.
Hypothesis Henv1 : val_mem tfibsegs m0 A_need_locks 1 0.
Hypothesis Henv2 : val_mem tfibsegs m0 A_ofl_lock 4 0.
Hypothesis Hhead : val_mem tfibsegs m0 A_ofl_head 8 0.
Hypothesis HOFLown : forall a, A_ofl_head <= a < A_ofl_head + 8 -> ~ aowned B ly S a.
Hypothesis HERRown : forall a, TFIB_TP - 164 <= a < TFIB_TP - 160 -> ~ aowned B ly S a.
Let stackW : Z -> Prop := AE2a.stackW regs.
Let errW : Z -> Prop := AE2a.errW.
Let oflW : Z -> Prop := AE2a.oflW.
Variable OPRE : Model -> Prop.
Hypothesis HOPRE : OPRE md.
Hypothesis OPRE_sbm : forall m m', same_but_materialized m m' -> OPRE m -> OPRE m'.
Hypothesis OPENATX : forall regs1 mem1 md1 (fs0 : Fs.Fs) (XA XB : TSet),
AI tfibsegs (w_H W) (w_A W) md1 -> OPRE md1 -> m_fs md1 = fs0 ->
bv_unsigned (getr regs1 17) = 56 -> getr regs1 10 = w64 (2 ^ 64 - 100) -> getr regs1 11 = w64 A_PATH ->
getr regs1 12 = w64 33345 -> getr regs1 13 = w64 438 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ stackW a -> ~ errW a -> ~ oflW a -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) ->
(forall md' e, 1 <= e <= 4095 -> same_but_materialized md1 md' -> AI tfibsegs (w_H W) (w_A W) md' ->
srealizes tfibsegs (mkCfg (mkst (regupd regs1 10 (errno_ret e)) (v_addi (Z_to_bv 64 FO_ECALL) 4) mem1 (seg_rom tfibsegs)) md') XA) ->
(forall md' (fd : word), bv_unsigned fd < 2 ^ 31 -> fd_lookup (m_fds md1) fd = None ->
same_but_materialized (with_fds (fd_insert (m_fds md1) fd (FdFileW sink_path (Z_to_bv 64 0))) (with_fs (fs_set (m_fs md1) sink_path []) md1)) md' ->
AI tfibsegs (w_H W) (w_A W) md' ->
srealizes tfibsegs (mkCfg (mkst (regupd regs1 10 fd) (v_addi (Z_to_bv 64 FO_ECALL) 4) mem1 (seg_rom tfibsegs)) md') XB) ->
srealizes tfibsegs (mkCfg (pend_at regs1 (Z_to_bv 64 FO_ECALL) mem1 (seg_rom tfibsegs)) md1) (openat_shape fs0 XA XB).
Definition LAPOST_A : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\
(exists regs' mem' md' (e : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md' /\ 1 <= e <= 4095 /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
m_vmmaps md' = m_vmmaps md /\ m_vm_lazy md' = m_vm_lazy md /\ same_io md md' /\ os_kept md md' /\ same_but_materialized md md' /\
val_mem tfibsegs (mrestrict H mem') (TFIB_TP - 164) 4 e /\ val_mem tfibsegs (mrestrict H mem') A_ofl_head 8 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ stackW a -> ~ errW a -> ~ oflW a -> aview tfibsegs H mem' a = aview tfibsegs H mem a) /\
(forall a, stackW a -> apresent H mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ errW a -> ~ oflW a -> apresent H mem a -> apresent H mem' a)).
Definition LAPOST_B : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\
(exists regsT memT mdT (fd : word) (v8 v9 v18 v19 : Z),
c' = cfg_at tfibsegs PC_MALLOC regsT memT mdT /\ AR tfibsegs B ly S W memT mdT /\
getr regsT 10 = w64 1264 /\ getr regsT 1 = w64 FO_MALLOC_RA /\ getr regsT 2 = w64 (sp0 - FO_FRAME - 96) /\
getr regsT 8 = w64 A_WB /\ getr regsT 9 = fd /\ getr regsT 18 = w64 A_WB /\ getr regsT 19 = w64 A_canary /\
(forall r, In r AE2g.KEPTF -> getr regsT (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
bv_unsigned fd < 2 ^ 31 /\ fd_lookup (m_fds md) fd = None /\
m_fds mdT = fd_insert (m_fds md) fd (FdFileW sink_path (Z_to_bv 64 0)) /\ m_fs mdT = fs_set (m_fs md) sink_path [] /\
m_vmmaps mdT = m_vmmaps md /\ m_vm_lazy mdT = m_vm_lazy md /\ os_kept md mdT /\
0 <= v8 < 2 ^ 64 /\ 0 <= v9 < 2 ^ 64 /\ 0 <= v18 < 2 ^ 64 /\ 0 <= v19 < 2 ^ 64 /\
val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 8) 8 IO_RET /\ val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 16) 8 v8 /\
val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 24) 8 v9 /\ val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 32) 8 v18 /\
val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 40) 8 FO_FDOPEN_RA /\ val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 48) 8 A_WB /\
val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 56) 8 (bv_unsigned fd) /\ val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 64) 8 FO_S2VAL /\
val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 72) 8 v19 /\
val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 80) 8 cval /\
(forall j rz off, nth_error SAVEDF j = Some (rz, off) -> val_mem tfibsegs (mrestrict H memT) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))) /\
val_mem tfibsegs (mrestrict H memT) A_ofl_head 8 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ stackW a -> ~ errW a -> ~ oflW a -> aview tfibsegs H memT a = aview tfibsegs H mem a) /\
(forall a, stackW a -> apresent H memT a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ errW a -> ~ oflW a -> apresent H mem a -> apresent H memT a)).
Lemma factsMX : 2 ^ 44 <= sp0 /\ sp0 <= 2 ^ 47 /\ FOP_WIN = 6400 /\ FO_WIN = 2304 /\ FO_FRAME = 2144 /\
(ly_stk_hi ly <= 2 ^ 47 /\ 17594333495296 + 6400 <= sp0) /\ A_ofl_head = 0x5f9688 /\ TFIB_TP = 0x5d8f90 /\ TFIB_IMG_END = 0x5fb000 /\
bv_unsigned (getr regs 4) = TFIB_TP.
Proof.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (FS : FOP_WIN = 6400) by reflexivity. rewrite FS in *. clear OPENATX. subst sp0.
repeat split; try lia; try reflexivity. rewrite Htp, (ts_tp B TB). apply unsigned_lit_small. unfold TFIB_TP. lia.
Qed.
Lemma frameOX : forall (memA mem1 : word -> option byte) mdA md1 (Wr : Z -> Prop) (blk : Z -> Prop),
AR tfibsegs B ly S W memA mdA ->
(forall a, Wr a \/ ~ Wr a) ->
(forall a, Wr a -> stackW a \/ errW a \/ oflW a \/ blk a) ->
(forall a, blk a -> ~ aowned B ly S a /\ AF0x.off_img a) ->
(forall z : word, ~ Wr (bv_unsigned z) -> mem1 z = memA z) ->
(forall a, Wr a -> ~ errW a -> ~ oflW a -> apresent H mem1 a) ->
md_frame mdA md1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs H mem1 a = aview tfibsegs H memA a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ errW a -> ~ oflW a -> apresent H memA a -> apresent H mem1 a) /\
AR tfibsegs B ly S W mem1 md1.
Proof.
intros memA mem1 mdA md1 Wr blk HARA Wdec HWin Hblk MEQ PRS MF.
pose proof factsMX as (Hsp & Hsp2 & FS & FW & FF & Lhi & HO & HT & HIE & Etp). rewrite FS in *. unfold stackW, errW, oflW, AE2a.stackW, AE2a.errW, AE2a.oflW in *. rewrite HO, HT in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs H mem1 a = aview tfibsegs H memA a).
{ intros a Hr Hw. apply aview_same. apply MEQ. rewrite unsigned_lit_small by lia. exact Hw. }
assert (PM : forall a, 0 <= a < 2 ^ 64 -> ~ (0x5d8f90 - 164 <= a < 0x5d8f90 - 160) -> ~ (0x5f9688 <= a < 0x5f9688 + 8) -> apresent H memA a -> apresent H mem1 a).
{ intros a Hr He Ho Hp. destruct (Wdec a) as [Hw|Hw]; [apply PRS; assumption|].
apply (apresent_same H memA mem1 a); [apply MEQ; rewrite unsigned_lit_small by lia; exact Hw | exact Hp]. }
split; [exact AV|]. split; [exact PM|].
pose proof (md_frame_eager _ _ MF) as Feu. destruct MF as [Fmaps Flazy].
assert (IMGb : forall a, (0x5d8f90 - 164 <= a < 0x5d8f90 - 160) \/ (0x5f9688 <= a < 0x5f9688 + 8) -> seg_rom tfibsegs (Z_to_bv 64 a) <> None).
{ intros a Ha.
assert (C : forall j, In j [0; 1; 2; 3] -> seg_rom tfibsegs (Z_to_bv 64 (0x5d8f90 - 164 + j)) <> None /\ (j < 4 \/ True))
by (intros j Hj; cbn [In] in Hj; repeat (destruct Hj as [<- | Hj]; [vm_compute; split; [discriminate | lia]|]); destruct Hj).
destruct Ha as [Ha|Ha].
- replace a with (0x5d8f90 - 164 + (a - (0x5d8f90 - 164))) by lia. apply (proj1 (C (a - (0x5d8f90 - 164)) ltac:(cbn [In]; lia))).
- rewrite <- HO in Ha. destruct (ofl_img_facts_fo (a - A_ofl_head) ltac:(lia)) as [_ Hrom]. replace (A_ofl_head + (a - A_ofl_head)) with a in Hrom by lia. exact Hrom. }
apply (al_frame _ _ LAWS ly S W memA mdA mem1 _ HARA).
+ intros a Hr Hown. apply AV; [exact Hr|]. intros Hw. destruct (HWin a Hw) as [Hs | [He | [Ho | Hb]]].
* exact (al_stack _ _ LAWS ly S W memA mdA a HARA ltac:(unfold sp0 in *; lia) Hown).
* exact (HERRown a He Hown).
* exact (HOFLown a Ho Hown).
* exact (proj1 (Hblk a Hb) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ mem1 a). rewrite (AE2y.aview_mod _ memA a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Wdec a') as [Hw|Hw]; [| rewrite AV by assumption; exact Hv].
destruct (HWin a' Hw) as [Hs | [He | [Ho | Hb]]].
* apply AE2y.aview_some_of_apresent. apply PRS; [exact Hw | lia | lia].
* unfold aview, mbyte. destruct (mrestrict (w_H W) mem1 (Z_to_bv 64 a')) as [b|]; [cbn; discriminate|].
pose proof (IMGb a' (or_introl He)) as Hrom. destruct (seg_rom tfibsegs (Z_to_bv 64 a')); [cbn; discriminate | exfalso; exact (Hrom eq_refl)].
* unfold aview, mbyte. destruct (mrestrict (w_H W) mem1 (Z_to_bv 64 a')) as [b|]; [cbn; discriminate|].
pose proof (IMGb a' (or_intror Ho)) as Hrom. destruct (seg_rom tfibsegs (Z_to_bv 64 a')); [cbn; discriminate | exfalso; exact (Hrom eq_refl)].
* pose proof (proj2 (Hblk a' Hb)) as Hoff. apply AE2y.aview_some_of_apresent. apply PRS; [exact Hw | | ]; unfold AF0x.off_img, TFIB_IMG_LO, TFIB_IMG_END in Hoff; lia.
+ exact Fmaps.
+ exact Flazy.
+ exact Feu.
+ intros a Hband Hh. pose proof (AE2y.in_band_rw_u64 a Hband) as Hr. change (w64 a) with (Z_to_bv 64 a) in *.
apply MEQ. rewrite unsigned_lit_small by lia. intros Hw. destruct (HWin a Hw) as [Hs | [He | [Ho | Hb]]].
* exfalso. pose proof (Hpres a Hs) as [Hn0 _]. unfold H in Hn0. rewrite Hh in Hn0. discriminate.
* unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hband. clear - Hband He. lia.
* unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hband. clear - Hband Ho. lia.
* exfalso. pose proof (PRS a Hw ltac:(clear - Hb Hblk; pose proof (proj2 (Hblk a Hb)) as X; unfold AF0x.off_img, TFIB_IMG_LO, TFIB_IMG_END in X; lia)
ltac:(clear - Hb Hblk; pose proof (proj2 (Hblk a Hb)) as X; unfold AF0x.off_img, TFIB_IMG_LO, TFIB_IMG_END in X; lia)) as [Hn0 _].
unfold H in Hn0. rewrite Hh in Hn0. discriminate.
Qed.
Theorem fopen_LAX : forall (XA XB : TSet),
AI tfibsegs (w_H W) (w_A W) md ->
(forall W' c', wle W W' -> AI tfibsegs (w_H W') (w_A W') (cfg_model c') -> LAPOST_A W' c' -> srealizes tfibsegs c' XA) ->
(forall W' c', wle W W' -> AI tfibsegs (w_H W') (w_A W') (cfg_model c') -> LAPOST_B W' c' -> srealizes tfibsegs c' XB) ->
srealizes tfibsegs (cfg_at tfibsegs FF_pc_wrap_fopen regs mem md) (openat_shape (m_fs md) XA XB).
Proof.
intros XA XB HAI0 KA KB.
pose proof factsMX as (Hsp & Hsp2 & FS & FW & FF & Lhi & HO & HT & HIE & Etp). rewrite FS in *.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi' & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi'.
pose proof AF0x.Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (IW : IO_WIN = 2160) by reflexivity. assert (IFR : IO_FRAME = 2144) by reflexivity.
eapply (SRr_srz tfibsegs).
{ apply (iopen_front B LAWS TB ly S W regs mem md HAR Hal16); rewrite ?IW.
- lia.
- exact Hshi.
- intros a Ha. apply Hpres. lia.
- exact G10.
- exact G11.
- exact HIO. }
{ exact HAI0. }
intros W1 c1 _ HAI1 (-> & regs1 & mem1 & md1 & -> & MF1 & HAR1 & Q10 & Q11 & Q1 & Q2 & QK & QS & AV1 & PRS1 & PM1).
rewrite IW in AV1, PRS1. rewrite IFR in Q2. fold H in AV1, PRS1, PM1, QS. fold sp0 in Q2, QS, AV1, PRS1.
set (E1 := AE2y.Env regs1 [cval]).
assert (E1reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E1 i = getr regs1 r) by (intros; apply AE2y.Env_reg; assumption).
assert (E1_2 : bv_unsigned (ew E1 2) = sp0 - 2144) by (rewrite (E1reg 2%nat 2%bv eq_refl), Q2; apply unsigned_lit_small; lia).
assert (E1_4 : bv_unsigned (ew E1 4) = TFIB_TP) by (rewrite (E1reg 4%nat 4%bv eq_refl); rewrite <- Etp; f_equal; exact (QK 4 ltac:(unfold AE2g.KEPTF; INL))).
assert (E1_32 : ew E1 32 = Z_to_bv 64 cval) by (exact (AE2y.Env_x regs1 [cval] 0%nat cval eq_refl)).
assert (MB1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2160 <= a < sp0) -> mbyte tfibsegs (mrestrict H mem1) a = mbyte tfibsegs (mrestrict H mem) a).
{ intros a Hr Hs. apply AE2y.mbyte_of_aview. apply AV1; lia. }
assert (HSTC1 : cells_hold (mrestrict H mem1) st_cells).
{ apply (cells_hold_frame m0); [| | exact HSTC].
- intros a Hx. unfold st_cells, A_WB in Hx. apply Exists_exists in Hx as (r & Hin & Hr). cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hr; apply MB1; lia.
- unfold st_cells. repeat constructor; cbn; lia. }
assert (HIMG1 : ro_img (mrestrict H mem1)).
{ apply (ro_img_mb m0); [| exact HIMG]. intros a Ha. unfold IMG_RO_LO, IMG_RO_HI in Ha. apply MB1; lia. }
assert (WOFL : forall (m : word -> option byte) o, 0 <= o < 8 -> writable_at tfibsegs m (A_ofl_head + o)).
{ intros m o Ho. destruct (ofl_img_facts_fo o Ho) as [Hw _]. unfold img_writable_ok in Hw.
apply (writable_at_grows tfibsegs (fun _ => None)); [intros x Hx; exfalso; exact (Hx eq_refl)|].
unfold writable_at. destruct (wview tfibsegs (fun _ => None) (Z_to_bv 64 (A_ofl_head + o))); [discriminate | discriminate Hw]. }
assert (WERR : forall (m : word -> option byte) o, 0 <= o < 4 -> writable_at tfibsegs m (TFIB_TP - 164 + o)).
{ intros m o Ho.
assert (C : forall j, In j [0; 1; 2; 3] -> img_writable_ok tfibsegs (TFIB_TP - 164 + j) = true)
by (intros j Hj; cbn [In] in Hj; repeat (destruct Hj as [<- | Hj]; [vm_compute; reflexivity|]); destruct Hj).
pose proof (C o ltac:(cbn [In]; lia)) as Hw. unfold img_writable_ok in Hw.
apply (writable_at_grows tfibsegs (fun _ => None)); [intros x Hx; exfalso; exact (Hx eq_refl)|].
unfold writable_at. destruct (wview tfibsegs (fun _ => None) (Z_to_bv 64 (TFIB_TP - 164 + o))); [discriminate | discriminate Hw]. }
assert (HS1 : st_ok tfibsegs E1 ssO1 (restrict H (mkst regs1 (Z_to_bv 64 FF_real_fopen) mem1 (seg_rom tfibsegs)))).
{ unfold ssO1.
apply (st_ok_pin_reg E1 (mkSS FF_real_fopen (sr_set sr_atoms 10%bv (SLit A_PATH)) memO None (mkFacts factsO [] [])) _ 11%bv (SLit A_WB));
[| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite Q11; reflexivity].
apply (st_ok_pin_reg E1 (mkSS FF_real_fopen sr_atoms memO None (mkFacts factsO [] [])) _ 10%bv (SLit A_PATH));
[| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite Q10; reflexivity].
rewrite restrict_mkst_fx. unfold E1, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs1 (map (Z_to_bv 64) [cval])) with E1.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold memO. apply Forall_cons.
{ unfold stkO. rewrite FW. apply (region_ok_stack tfibsegs E1 _ 2 (sp0 - 2144) (- 2304)); [exact E1_2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. destruct (Z_lt_le_dec a (sp0 - 2160)) as [L|L]; [apply PM1, Hpres; lia | apply PRS1; lia]. }
unfold memS. change (skipn 1 ([stkS; img_piece 0x2011e 8; img_piece 0x10330 (0x10398 - 0x10330)] ++ map ro_region (icpt_rodata ++ st_const ++ st_cells)))
with ([img_piece 0x2011e 8; img_piece 0x10330 (0x10398 - 0x10330)] ++ map ro_region (icpt_rodata ++ st_const ++ st_cells)).
rewrite <- !app_assoc. apply Forall_app. split.
{ apply Forall_cons; [apply (img_piece_ok _ E1 0x1cd1e (0x20b7c - 0x1cd1e)); [exact HIMG1 | unfold img_ro_chunks; cbn; tauto | lia | lia | lia]|].
apply Forall_cons; [apply (img_piece_ok _ E1 0x10330 (0x10398 - 0x10330)); [exact HIMG1 | unfold img_ro_chunks; cbn; tauto | lia | lia | lia]|]. apply Forall_nil. }
apply Forall_app. split.
{ rewrite !map_app. apply Forall_app. split; [exact (AE2y.icpt_rodata_ok B TB ly S H mem1 E1 (proj1 HAR1))|].
apply Forall_app. split; [exact (rodata_ok B TB st_const ly S H mem1 E1 (st_const_chk ly) (proj1 HAR1))|].
exact (cells_region_ok _ E1 st_cells HSTC1). }
apply Forall_app. split.
{ unfold canR. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_GOT_canary, A_canary.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E1 _ 0 0x9ec38 8 (SLit 0x5f8fd0) 0x5f8fd0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l].
apply (val_mem_frame tfibsegs m0); [intros x Hx; apply MB1; lia | exact Hcan1]. }
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_canary.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E1 _ 0 0x5f8fd0 8 (SOff 32 0) cval); [cbn [sv_denot]; rewrite E1_32, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l].
apply (val_mem_frame tfibsegs m0); [intros x Hx; apply MB1; lia | exact Hcan2]. } }
apply Forall_cons.
{ unfold errR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E1_4, HT.
split; [lia|]. split; [lia|]. split; [intros o Ho; replace (6131600 + o) with (TFIB_TP - 164 + (o + 164)) by (rewrite HT; lia); apply WERR; lia | apply Forall_nil]. }
unfold envO. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; unfold A_threaded, A_need_locks, A_ofl_lock; rewrite ?HO.
{ split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E1 _ 0 0x5f9221 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l].
apply (val_mem_frame tfibsegs m0); [intros x Hx; apply MB1; lia | exact Henv0]. }
{ split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E1 _ 0 0x5f9223 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l].
apply (val_mem_frame tfibsegs m0); [intros x Hx; apply MB1; lia | exact Henv1]. }
{ split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E1 _ 0 0x5f9680 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l].
apply (val_mem_frame tfibsegs m0); [intros x Hx; apply MB1; lia | exact Henv2]. }
{ split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; replace o with (A_ofl_head + (o - 0x5f9688)) by (rewrite HO; lia); apply WOFL; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E1 _ 0 0x5f9688 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l].
rewrite <- HO. apply (val_mem_frame tfibsegs m0); [intros x Hx; rewrite HO in Hx; apply MB1; lia | exact Hhead]. }
- apply pairwise_disjoint_of_extents. unfold memO, memS, stkO, stkS, img_piece, st_cells, st_const, icpt_rodata, canR, errR, envO, ro_region, extent_of_region.
cbn [skipn map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E1_2, E1_4, HT.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold A_WB, A_GOT_canary, A_canary, A_threaded, A_need_locks, A_ofl_lock, A_ofl_head, FO_WIN in *. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsO]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E1_2, E1_4, HT.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia. replace (sp0 - 2144) with (sp0 + (-134) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
unfold cfg_at. change (w64 FF_real_fopen) with (Z_to_bv 64 FF_real_fopen).
eapply (SRr_srz tfibsegs); [exact (fo_phase W E1 ssO1 eO1 _ (mkst regs1 (Z_to_bv 64 FF_real_fopen) mem1 (seg_rom tfibsegs)) md1 HS1 r_O1) | exact HAI1 |].
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [ms_mem mkst] in HF2. clear HFr2.
set (md2 := with_vm_backing (m_vm_lazy md1) mat2 md1) in *.
assert (MF2 : same_but_materialized md1 md2) by (subst md2; apply with_vm_backing_same).
pose proof shapeO1_ok as Hsh. unfold shapeO1 in Hsh.
apply andb_prop in Hsh as [Hsh Hat]. apply andb_prop in Hsh as [Hsh Hsk]. apply andb_prop in Hsh as [Hsh R13]. apply andb_prop in Hsh as [Hsh R12].
apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hsh R17]. apply andb_prop in Hsh as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
assert (Hresv2 : ss_resv eO1 = None) by (destruct (ss_resv eO1); [discriminate | reflexivity]).
destruct (st_ok_ecall_shape_r tfibsegs H E1 eO1 ms2 HS2 Hresv2) as (regs2 & mem2 & Hms2 & Hregs2 & Hmemok2 & HG2).
assert (Hmm2 : ms_mem ms2 = mem2) by (rewrite Hms2; reflexivity). rewrite Hmm2 in HF2.
assert (WIN : forall E rs a, windows rs = WINS -> bv_unsigned (ew E 2) = sp0 - 2144 -> bv_unsigned (ew E 4) = TFIB_TP -> in_wrange E rs a ->
(sp0 - 2144 - 2304 <= a < sp0 - 2144) \/ errW a \/ oflW a).
{ intros E rs a HWl E2 E4 Hin. destruct (in_wrange_windows E rs a Hin) as (bw & lo & hi & Ht & Hr). rewrite HWl in Ht. unfold WINS in Ht. cbn [In] in Ht.
unfold errW, oflW, AE2a.errW, AE2a.oflW. rewrite HO, HT. rewrite HT in E4.
repeat (destruct Ht as [Et | Ht]; [injection Et as <- <- <-; cbn [base_val] in Hr; rewrite ?E2, ?E4 in Hr; lia|]). destruct Ht. }
pose proof wins_O1 as (WL1 & WL2 & WL2r & WL0).
assert (MEQ2 : forall z : word, ~ ((sp0 - 2144 - 2304 <= bv_unsigned z < sp0 - 2144) \/ errW (bv_unsigned z) \/ oflW (bv_unsigned z)) -> mem2 z = mem1 z).
{ intros z Hz. apply (HF2 z). intros Hin. exact (Hz (WIN E1 _ _ WL0 E1_2 E1_4 Hin)). }
clear HF2.
assert (RD2 : forall (r : bv 5) v, reg_is eO1 (bv_unsigned r) v = true -> getr regs2 r = sv_denot E1 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply Hregs2. }
assert (Q2_17 : bv_unsigned (getr regs2 17) = 56) by (rewrite (RD2 17%bv (SLit 56) R17); reflexivity).
assert (Q2_10 : getr regs2 10 = w64 (2 ^ 64 - 100)) by (rewrite (RD2 10%bv _ R10); reflexivity).
assert (Q2_11 : getr regs2 11 = w64 A_PATH) by (rewrite (RD2 11%bv _ R11); reflexivity).
assert (Q2_12 : getr regs2 12 = w64 33345) by (rewrite (RD2 12%bv _ R12); reflexivity).
assert (Q2_13 : getr regs2 13 = w64 438) by (rewrite (RD2 13%bv _ R13); reflexivity).
unfold skelsO in Hsk. apply andb_prop in Hsk as [Hlen Hsk]. destruct (ss_mem eO1) as [|r0 rest] eqn:Hmem; [discriminate Hsk|].
apply andb_prop in Hsk as [Hsk _]. apply andb_prop in Hsk as [K0 _]. apply skel_is_sound in K0 as (K0a & K0lo & K0hi & K0b & K0c). rewrite FW in K0b, K0lo.
assert (PRS2s : forall a, sp0 - 2144 - 2304 <= a < sp0 - 2144 -> apresent H mem2 a).
{ intros a Ha. apply (mem_ok_window_apresent H E1 mem2 _ 0 r0 a Hmemok2 ltac:(rewrite ?Hmem; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite K0a, K0b, K0c. cbn [base_val]. rewrite E1_2. lia. }
set (Wr2 := fun a => (sp0 - 2144 - 2304 <= a < sp0 - 2144) \/ errW a \/ oflW a).
assert (Wr2d : forall a, Wr2 a \/ ~ Wr2 a) by (intros a; subst Wr2; cbn beta; unfold errW, oflW, AE2a.errW, AE2a.oflW; lia).
assert (Wr2i : forall a, Wr2 a -> stackW a \/ errW a \/ oflW a \/ False) by (intros a Ha; subst Wr2; cbn beta in Ha; unfold stackW, AE2a.stackW; destruct Ha as [Ha|Ha]; [left; lia | tauto]).
assert (Wr2p : forall a, Wr2 a -> ~ errW a -> ~ oflW a -> apresent H mem2 a).
{ intros a Ha He Hof. subst Wr2. cbn beta in Ha. destruct Ha as [Hs | [Hx | Hx]]; [exact (PRS2s a Hs) | exfalso; exact (He Hx) | exfalso; exact (Hof Hx)]. }
destruct (frameOX mem1 mem2 md1 md2 Wr2 (fun _ => False) HAR1 Wr2d Wr2i ltac:(intros a Hf; destruct Hf) MEQ2 Wr2p (md_frame_sbm _ _ MF2)) as (AV2 & PM2 & HAR2).
subst Wr2. cbv beta in AV2. clear Wr2d Wr2i Wr2p.
assert (MB2 : forall a, 0 <= a < 2 ^ 64 -> ~ stackW a -> ~ errW a -> ~ oflW a -> mbyte tfibsegs (mrestrict H mem2) a = mbyte tfibsegs (mrestrict H mem) a).
{ intros a Hr Hs He Hof. unfold stackW, AE2a.stackW in Hs. rewrite <- (MB1 a Hr ltac:(lia)). apply AE2y.mbyte_of_aview. apply AV2; [lia|]. intros [Hx|[Hx|Hx]]; [lia | exact (He Hx) | exact (Hof Hx)]. }
assert (AVF2 : forall a, 0 <= a < 2 ^ 64 -> ~ stackW a -> ~ errW a -> ~ oflW a -> aview tfibsegs H mem2 a = aview tfibsegs H mem a).
{ intros a Hr Hs He Hof. rewrite AV2; [apply AV1; [exact Hr | unfold stackW, AE2a.stackW in Hs; lia] | exact Hr | unfold stackW, AE2a.stackW in Hs; intros [Hx|[Hx|Hx]]; [lia | exact (He Hx) | exact (Hof Hx)]]. }
rewrite Hms2. rewrite Hms2 in HAI2. rename HAI2 into HAI. cbn [cfg_model] in HAI.
pose proof (same_but_materialized_frame md md2 (same_but_materialized_trans _ _ _ MF1 MF2)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FS02 & _).
rewrite Hpc. apply (OPENATX regs2 mem2 md2 (m_fs md) XA XB HAI (OPRE_sbm md md2 (same_but_materialized_trans _ _ _ MF1 MF2) HOPRE) FS02 Q2_17 Q2_10 Q2_11 Q2_12 Q2_13 AVF2).
-
intros md3 e He MF3 HAI3.
enough (ARM : SRr tfibsegs W (mkCfg (mkst (regupd regs2 10 (errno_ret e)) (v_addi (Z_to_bv 64 FO_ECALL) 4) mem2 (seg_rom tfibsegs)) md3) LAPOST_A)
by (apply (ARM HAI3 XA); intros W' c' Hw HA' HP; exact (KA W' c' Hw HA' HP)).
set (RET := errno_ret e).
assert (HRETu : bv_unsigned RET = 2 ^ 64 - e).
{ subst RET. unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
replace (- e) with ((2 ^ 64 - e) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
set (E2 := ewset E1 40 RET).
assert (E2old : forall i, (i < 40)%nat -> ew E2 i = ew E1 i) by (intros i Hi; subst E2; apply ew_ewset_other; lia).
assert (E2_40 : ew E2 40 = RET) by (subst E2; apply ew_ewset_same).
assert (E2_2 : bv_unsigned (ew E2 2) = sp0 - 2144) by (rewrite (E2old 2%nat ltac:(lia)); exact E1_2).
assert (E2_4 : bv_unsigned (ew E2 4) = TFIB_TP) by (rewrite (E2old 4%nat ltac:(lia)); exact E1_4).
assert (HS3 : st_ok tfibsegs E2 (resumeO2r eO1) (restrict H (mkst (regupd regs2 10 RET) (v_addi (Z_to_bv 64 FO_ECALL) 4) mem2 (seg_rom tfibsegs)))).
{ unfold resumeO2r. rewrite restrict_mkst_fx, <- Hpc. subst E2.
apply (st_ok_resume_atom tfibsegs 40 (mkAF (2 ^ 64 - 4095) (2 ^ 64 - 1) 0) E1 eO1 regs2 (mrestrict H mem2) RET Hregs2 ltac:(rewrite Hmem; exact Hmemok2) HG2 Hat); cbn [af_lo af_hi af_al2]; rewrite ?HRETu; [lia | lia |].
change (2 ^ 0) with 1. apply Z.mod_1_r. }
eapply SRr_bind; [exact (fo_phase W E2 (resumeO2r eO1) eO2r _ (mkst (regupd regs2 10 RET) (v_addi (Z_to_bv 64 FO_ECALL) 4) mem2 (seg_rom tfibsegs)) md3 HS3 r_O2r)|].
intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [ms_mem mkst] in HF4. clear HFr4.
set (md4 := with_vm_backing (m_vm_lazy md3) mat4 md3) in *.
assert (MF4 : same_but_materialized md2 md4) by (eapply same_but_materialized_trans; [exact MF3 | subst md4; apply with_vm_backing_same]).
pose proof shapeO2r_ok as Hsr. unfold shapeO2r in Hsr.
apply andb_prop in Hsr as [Hsr Hsk4]. apply andb_prop in Hsr as [Hsr Hofl4]. apply andb_prop in Hsr as [Hsr Herr4]. apply andb_prop in Hsr as [Hsr HK4].
apply andb_prop in Hsr as [Hsr Z10]. apply andb_prop in Hsr as [Hpc4 Hrv4]. apply Z.eqb_eq in Hpc4.
assert (Hresv4 : ss_resv eO2r = None) by (destruct (ss_resv eO2r); [discriminate | reflexivity]).
unfold skelsO in Hsk4. apply andb_prop in Hsk4 as [Hlen4 Hsk4]. destruct (ss_mem eO2r) as [|q0 qrest] eqn:Hmem4; [discriminate Hsk4|].
apply andb_prop in Hsk4 as [Hsk4 _]. apply andb_prop in Hsk4 as [J0 Hsk4].
destruct (nth_error qrest 17) as [qe|] eqn:Hqe; [|discriminate Hsk4]. destruct (nth_error qrest 21) as [qo|] eqn:Hqo; [|discriminate Hsk4].
apply andb_prop in Hsk4 as [Je Jo].
apply skel_is_sound in J0 as (J0a & J0lo & J0hi & J0b & J0c). apply skel_is_sound in Je as (Jea & Jelo & Jehi & Jeb & Jec). apply skel_is_sound in Jo as (Joa & Jolo & Johi & Job & Joc).
rewrite FW in J0b, J0lo.
assert (MEQ4 : forall z : word, ~ ((sp0 - 2144 - 2304 <= bv_unsigned z < sp0 - 2144) \/ errW (bv_unsigned z) \/ oflW (bv_unsigned z)) -> ms_mem ms4 z = mem2 z).
{ intros z Hz. apply (HF4 z). intros Hin. exact (Hz (WIN E2 _ _ WL2r E2_2 E2_4 Hin)). }
clear HF4.
assert (RD4 : forall (r : bv 5) v, reg_is eO2r (bv_unsigned r) v = true -> getr (ms_regs ms4) r = sv_denot E2 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E2 eO2r ms4 r HS4). }
set (regs4 := ms_regs ms4) in *.
assert (PK4 : forall r, In r KEPTR1 -> getr regs4 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ intros r Hin. assert (Hr : 0 <= r < 32) by (unfold KEPTR1 in Hin; cbn in Hin; lia).
rewrite forallb_forall in HK4. specialize (HK4 _ Hin). cbn beta in HK4.
rewrite (RD4 (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
- cbn [sv_denot]. rewrite (E2old (Z.to_nat r) ltac:(lia)), (E1reg (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact HK4. }
assert (P4_1 : getr regs4 1 = w64 IO_RET) by (etransitivity; [exact (PK4 1 ltac:(unfold KEPTR1; INL)) | exact Q1]).
assert (P4_2 : getr regs4 2 = w64 (sp0 - 2144)) by (etransitivity; [exact (PK4 2 ltac:(unfold KEPTR1; INL)) | exact Q2]).
assert (P4_10 : getr regs4 10 = w64 0) by (rewrite (RD4 10%bv (SLit 0) Z10); reflexivity).
assert (PRS4s : forall a, sp0 - 2144 - 2304 <= a < sp0 - 2144 -> apresent H (ms_mem ms4) a).
{ intros a Ha. apply (AF0x.st_ok_window_apresent_off H E2 eO2r ms4 0 q0 a HS4 ltac:(rewrite ?Hmem4; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite J0a, J0b, J0c. cbn [base_val]. rewrite E2_2. lia. }
set (Wr4 := fun a => (sp0 - 2144 - 2304 <= a < sp0 - 2144) \/ errW a \/ oflW a).
assert (Wr4d : forall a, Wr4 a \/ ~ Wr4 a) by (intros a; subst Wr4; cbn beta; unfold errW, oflW, AE2a.errW, AE2a.oflW; lia).
assert (Wr4i : forall a, Wr4 a -> stackW a \/ errW a \/ oflW a \/ False) by (intros a Ha; subst Wr4; cbn beta in Ha; unfold stackW, AE2a.stackW; destruct Ha as [Ha|Ha]; [left; lia | tauto]).
assert (Wr4p : forall a, Wr4 a -> ~ errW a -> ~ oflW a -> apresent H (ms_mem ms4) a).
{ intros a Ha He' Hof. subst Wr4. cbn beta in Ha. destruct Ha as [Hs | [Hx | Hx]]; [exact (PRS4s a Hs) | exfalso; exact (He' Hx) | exfalso; exact (Hof Hx)]. }
destruct (frameOX mem2 (ms_mem ms4) md2 md4 Wr4 (fun _ => False) HAR2 Wr4d Wr4i ltac:(intros a Hf; destruct Hf) MEQ4 Wr4p (md_frame_sbm _ _ MF4)) as (AV4 & PM4 & HAR4).
subst Wr4. cbv beta in AV4. clear Wr4d Wr4i Wr4p.
eapply SRr_bind.
{ eapply (SRr_ret_at tfibsegs tbl_fo tbl_fo_ok Hwx W E2 eO2r ms4 md4
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms4) (v_jalr (getr (ms_regs ms4) 1) 0) (ms_mem ms4) (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md4) mat' md4)));
[exact HS4 | exact Hresv4 | rewrite Hpc4; vm_compute; reflexivity | intros mat'; split; [reflexivity | exists mat'; reflexivity]]. }
intros W5 c5 _ (-> & mat5 & ->).
set (md5 := with_vm_backing (m_vm_lazy md4) mat5 md4). fold regs4.
assert (MF5 : same_but_materialized md4 md5) by (subst md5; apply with_vm_backing_same).
rewrite P4_1, (AE2y.ret_ok_lit IO_RET ltac:(unfold IO_RET; lia) eq_refl).
assert (R4sp : spZ regs4 = sp0 - 2144) by (unfold spZ; rewrite P4_2; apply unsigned_lit_small; lia).
assert (MBtop : forall a, 0 <= a < 2 ^ 64 -> sp0 - 2144 <= a < sp0 -> mbyte tfibsegs (mrestrict H (ms_mem ms4)) a = mbyte tfibsegs (mrestrict H mem1) a).
{ intros a Hr Ha. unfold errW, oflW, AE2a.errW, AE2a.oflW in AV4, AV2. rewrite HO, HT in AV4, AV2. apply AE2y.mbyte_of_aview. rewrite AV4 by lia. apply AV2; lia. }
set (v := map (fun p : Z * Z => bv_unsigned (getr regs (Z_to_bv 5 (fst p)))) SAVEDF).
assert (HCv : forall j, (j < 8)%nat -> val_mem tfibsegs (mrestrict H (ms_mem ms4)) (spZ regs4 + 2136 - 8 * Z.of_nat j) 8 (nth j v 0)).
{ intros j Hj. rewrite R4sp. apply (val_mem_frame tfibsegs (mrestrict H mem1)); [intros x Hx; apply MBtop; lia|].
destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; [| | | | | | | | lia]; subst v; cbn [map fst nth SAVEDF].
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 0) with (sp0 + -8) by lia. exact (QS 0%nat 1 (-8) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 1) with (sp0 + -16) by lia. exact (QS 1%nat 8 (-16) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 2) with (sp0 + -24) by lia. exact (QS 2%nat 9 (-24) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 3) with (sp0 + -32) by lia. exact (QS 3%nat 18 (-32) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 4) with (sp0 + -40) by lia. exact (QS 4%nat 19 (-40) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 5) with (sp0 + -48) by lia. exact (QS 5%nat 20 (-48) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 6) with (sp0 + -56) by lia. exact (QS 6%nat 21 (-56) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 7) with (sp0 + -64) by lia. exact (QS 7%nat 22 (-64) eq_refl). }
assert (Heven : bv_unsigned (getr regs 1) mod 2 = 0).
{ pose proof (u64_range (getr regs 1)) as Hu. pose proof (f_equal bv_unsigned Hra) as E. unfold v_jalr, jalr_tgtZ in E.
rewrite Z.add_0_r, Z_to_bv_unsigned in E.
assert (Hld : Z.land (bv_unsigned (getr regs 1)) (-2) = Z.shiftl (Z.shiftr (bv_unsigned (getr regs 1)) 1) 1).
{ change (-2) with (Z.lnot (Z.ones 1)). rewrite <- Z.ldiff_land. apply Z.ldiff_ones_r. lia. }
rewrite Hld, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 in E by lia. change (2 ^ 1) with 2 in E.
unfold bv_wrap in E. change (bv_modulus 64) with (2 ^ 64) in E.
pose proof (Z.mul_div_le (bv_unsigned (getr regs 1)) 2 ltac:(lia)) as Hm1. assert (Hm2 : 0 <= bv_unsigned (getr regs 1) / 2) by (apply Z.div_pos; lia).
rewrite Z.mod_small in E by lia. rewrite <- E. apply Z_mod_mult. }
change (mkCfg (mkst regs4 (Z_to_bv 64 IO_RET) (ms_mem ms4) (seg_rom tfibsegs)) md5) with (cfg_at tfibsegs IO_RET regs4 (ms_mem ms4) md5).
eapply SRr_bind.
{ apply (iopen_tail W regs4 (ms_mem ms4) md5 v eq_refl); rewrite ?R4sp; unfold IO_FRAME; try lia.
- subst v. cbn [map fst SAVEDF]. repeat (apply Forall_cons; [apply u64_range|]). apply Forall_nil.
- subst v. cbn [map fst nth SAVEDF]. replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity). exact Heven.
- replace (sp0 - 2144) with (sp0 + (-134) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- intros j Hj. fold H. rewrite <- R4sp. exact (HCv j Hj). }
intros W6 c6 _ (-> & regs6 & md6 & -> & MF6 & T10 & T1 & T2 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & TK).
pose proof same_io_sbm as SIO.
assert (MF46 : same_but_materialized md4 md6) by (eapply same_but_materialized_trans; [exact MF5 | exact MF6]).
pose proof (same_but_materialized_frame md md1 MF1) as (_ & V01 & Z01 & _). pose proof (same_but_materialized_frame md1 md2 MF2) as (_ & V12 & Z12 & _).
pose proof (same_but_materialized_frame md2 md4 MF4) as (_ & V24 & Z24 & _). pose proof (same_but_materialized_frame md4 md6 MF46) as (_ & V46 & Z46 & _).
assert (Hv0 : nth 0 v 0 = bv_unsigned (getr regs 1)) by (subst v; cbn [map fst nth SAVEDF]; replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity); reflexivity).
apply SRr_ret. split; [reflexivity|]. exists regs6, (ms_mem ms4), md6, e.
split; [rewrite Hv0; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact He|].
split.
{ apply (al_frame _ _ LAWS ly S W (ms_mem ms4) md4 (ms_mem ms4) md6 HAR4); [intros a Hr Hown; reflexivity | intros a Hv'; exact Hv' | exact V46 | exact Z46 | | intros a _ _; reflexivity].
apply (same_but_materialized_frame md4 _ MF46). }
split.
{ intros rr Hr. unfold acallee_saved in Hr.
assert (KK : forall r, In r [3; 4; 23; 24; 25; 26; 27] -> getr regs6 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hin. cbn [In] in Hin.
rewrite (TK r) by (unfold KEPTT; cbn [In]; lia). rewrite (PK4 r) by (unfold KEPTR1; cbn [In]; lia). apply (QK r). unfold AE2g.KEPTF. cbn [In]. lia. }
assert (VV : forall j (r : Z), nth_error SAVEDF j = nth_error SAVEDF j -> (j < 8)%nat -> fst (nth j SAVEDF (0, 0)) = r -> w64 (nth j v 0) = getr regs (Z_to_bv 5 r)).
{ intros j r _ Hj Hrz. subst v. rewrite <- Hrz.
destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; [| | | | | | | | lia]; cbn [map fst nth SAVEDF]; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity. }
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
* replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T2, R4sp. unfold IO_FRAME. replace (sp0 - 2144 + 2144) with sp0 by lia.
unfold sp0, spZ, w64. apply Z_to_bv_bv_unsigned.
* exact (KK 3 ltac:(INL)).
* exact (KK 4 ltac:(INL)).
* replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T8. exact (VV 1%nat 8 eq_refl ltac:(lia) eq_refl).
* replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T9. exact (VV 2%nat 9 eq_refl ltac:(lia) eq_refl).
* assert (Hc : rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ (rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27)) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | Hc]]]]].
-- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T18. exact (VV 3%nat 18 eq_refl ltac:(lia) eq_refl).
-- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T19. exact (VV 4%nat 19 eq_refl ltac:(lia) eq_refl).
-- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T20. exact (VV 5%nat 20 eq_refl ltac:(lia) eq_refl).
-- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T21. exact (VV 6%nat 21 eq_refl ltac:(lia) eq_refl).
-- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T22. exact (VV 7%nat 22 eq_refl ltac:(lia) eq_refl).
-- apply KK. cbn [In]. lia. }
split; [rewrite T10; exact P4_10|].
split; [rewrite V46, V24, V12; exact V01|].
split; [rewrite Z46, Z24, Z12; exact Z01|].
pose proof same_io_trans3 as SIOT.
split.
{ apply (SIOT md md4 md6); [| exact (SIO _ _ MF46)]. apply (SIOT md md2 md4); [| exact (SIO _ _ MF4)].
apply (SIOT md md1 md2); [exact (SIO _ _ MF1) | exact (SIO _ _ MF2)]. }
split.
{ eapply os_kept_trans; [exact (os_kept_sbm _ _ MF1)|]. eapply os_kept_trans; [exact (os_kept_sbm _ _ MF2)|].
eapply os_kept_trans; [exact (os_kept_sbm _ _ MF4) | exact (os_kept_sbm _ _ MF46)]. }
split.
{ eapply same_but_materialized_trans; [exact MF1|]. eapply same_but_materialized_trans; [exact MF2|]. eapply same_but_materialized_trans; [exact MF4 | exact MF46]. }
split.
{
unfold has_chunk in Herr4. rewrite Hmem4 in Herr4. change (nth_error (q0 :: qrest) 18) with (nth_error qrest 17) in Herr4. rewrite Hqe in Herr4.
apply existsb_exists in Herr4 as (c & Hc & Hcc). apply chunk_is_sound in Hcc. subst c.
pose proof (st_ok_mem_ok tfibsegs E2 eO2r _ HS4) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem4 in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs qe ltac:(right; eapply nth_error_In; exact Hqe)) as (_ & _ & _ & Hcs). rewrite Jea in Hcs. cbn [base_val] in Hcs. rewrite E2_4 in Hcs.
replace (TFIB_TP - 164) with (TFIB_TP + -164) by lia.
apply (val_of_chunk_ok tfibsegs E2 _ _ (-164) 4 _ e (proj1 (Forall_forall _ _) Hcs _ Hc)); [| cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite E2_40. apply bv_eq.
rewrite !low32_lit.
replace (alu32 ALU_SUB (Z_to_bv 32 0) (Z_to_bv 32 (bv_unsigned RET + 0))) with (low32 (Z_to_bv 64 e)).
2:{ rewrite low32_lit. apply bv_eq. rewrite alu32_unsigned, !Z_to_bv_unsigned. cbn [zalu_raw]. unfold bv_wrap.
change (bv_modulus 32) with (2 ^ 32). rewrite HRETu, Z.add_0_r, (Z.mod_small e) by lia. change (0 mod 2 ^ 32) with 0.
replace (2 ^ 64 - e) with ((2 ^ 32 - e) + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z_mod_plus_full, (Z.mod_small (2 ^ 32 - e)) by lia.
replace (0 - (2 ^ 32 - e)) with (e + (-1) * 2 ^ 32) by lia. rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia. }
unfold low32. rewrite sext32_small by lia. reflexivity. }
split.
{
unfold has_chunk in Hofl4. rewrite Hmem4 in Hofl4. change (nth_error (q0 :: qrest) 22) with (nth_error qrest 21) in Hofl4. rewrite Hqo in Hofl4.
apply existsb_exists in Hofl4 as (c & Hc & Hcc). apply chunk_is_sound in Hcc. subst c.
pose proof (st_ok_mem_ok tfibsegs E2 eO2r _ HS4) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem4 in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs qo ltac:(right; eapply nth_error_In; exact Hqo)) as (_ & _ & _ & Hcs). rewrite Joa in Hcs. cbn [base_val] in Hcs.
rewrite <- (Z.add_0_l A_ofl_head).
exact (val_of_chunk_ok tfibsegs E2 _ _ A_ofl_head 8 (SLit 0) 0 (proj1 (Forall_forall _ _) Hcs _ Hc) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
split.
{ intros a Hr Hs Herr Hofl.
rewrite AV4; [| exact Hr | unfold stackW, AE2a.stackW in Hs; intros [X|[X|X]]; [lia | exact (Herr X) | exact (Hofl X)]].
rewrite AV2; [| exact Hr | unfold stackW, AE2a.stackW in Hs; intros [X|[X|X]]; [lia | exact (Herr X) | exact (Hofl X)]]. apply AV1; [exact Hr | unfold stackW, AE2a.stackW in Hs; lia]. }
split.
{ intros a Hs. unfold stackW, AE2a.stackW in Hs. unfold errW, oflW, AE2a.errW, AE2a.oflW in PM4, PM2. rewrite HO, HT in PM4, PM2.
destruct (Z_lt_le_dec a (sp0 - 2144 - 2304)) as [L|L]; [| destruct (Z_lt_le_dec a (sp0 - 2144)) as [L2|L2]; [apply PRS4s; lia|]].
- apply PM4; [lia | lia | lia |]. apply PM2; [lia | lia | lia |]. apply PM1, Hpres. lia.
- apply PM4; [lia | lia | lia |]. apply PM2; [lia | lia | lia |]. apply PRS1. lia. }
intros a Hr Herr Hofl Hp. apply PM4; [exact Hr | exact Herr | exact Hofl |]. apply PM2; [exact Hr | exact Herr | exact Hofl |]. apply PM1. exact Hp.
-
intros md3 fd Hfd Hfdn MF3 HAI3.
enough (ARM : SRr tfibsegs W (mkCfg (mkst (regupd regs2 10 fd) (v_addi (Z_to_bv 64 FO_ECALL) 4) mem2 (seg_rom tfibsegs)) md3) LAPOST_B)
by (apply (ARM HAI3 XB); intros W' c' Hw HA' HP; exact (KB W' c' Hw HA' HP)).
pose proof (u64_range fd) as Hfdu.
set (E2 := ewset E1 40 fd).
assert (E2old : forall i, (i < 40)%nat -> ew E2 i = ew E1 i) by (intros i Hi; subst E2; apply ew_ewset_other; lia).
assert (E2_40 : ew E2 40 = fd) by (subst E2; apply ew_ewset_same).
assert (E2_2 : bv_unsigned (ew E2 2) = sp0 - 2144) by (rewrite (E2old 2%nat ltac:(lia)); exact E1_2).
assert (E2_4 : bv_unsigned (ew E2 4) = TFIB_TP) by (rewrite (E2old 4%nat ltac:(lia)); exact E1_4).
assert (HS3 : st_ok tfibsegs E2 (resumeO2 eO1) (restrict H (mkst (regupd regs2 10 fd) (v_addi (Z_to_bv 64 FO_ECALL) 4) mem2 (seg_rom tfibsegs)))).
{ unfold resumeO2. rewrite restrict_mkst_fx, <- Hpc. subst E2.
apply (st_ok_resume_atom tfibsegs 40 (mkAF 0 (2 ^ 31 - 1) 0) E1 eO1 regs2 (mrestrict H mem2) fd Hregs2 ltac:(rewrite Hmem; exact Hmemok2) HG2 Hat); cbn [af_lo af_hi af_al2]; [lia | lia |].
change (2 ^ 0) with 1. apply Z.mod_1_r. }
eapply SRr_bind; [exact (fo_phase W E2 (resumeO2 eO1) eO2 _ (mkst (regupd regs2 10 fd) (v_addi (Z_to_bv 64 FO_ECALL) 4) mem2 (seg_rom tfibsegs)) md3 HS3 r_O2)|].
intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [ms_mem mkst] in HF4. clear HFr4.
set (md4 := with_vm_backing (m_vm_lazy md3) mat4 md3) in *.
set (md2' := with_fds (fd_insert (m_fds md2) fd (FdFileW sink_path (Z_to_bv 64 0))) (with_fs (fs_set (m_fs md2) sink_path []) md2)) in MF3.
assert (MD24 : md_frame md2 md4).
{ eapply md_frame_trans; [| apply md_frame_sbm; subst md4; apply with_vm_backing_same]. eapply md_frame_trans; [| exact (md_frame_sbm _ _ MF3)].
subst md2'. eapply md_frame_trans; [apply md_frame_with_fs | apply md_frame_with_fds]. }
pose proof shapeO2_ok as Hsr. unfold shapeO2 in Hsr.
apply andb_prop in Hsr as [Hsr Hsk4]. apply andb_prop in Hsr as [Hsr Hofl4]. apply andb_prop in Hsr as [Hsr HC4]. apply andb_prop in Hsr as [Hsr HK4].
apply andb_prop in Hsr as [Hsr Z19]. apply andb_prop in Hsr as [Hsr Z18]. apply andb_prop in Hsr as [Hsr Z9]. apply andb_prop in Hsr as [Hsr Z8].
apply andb_prop in Hsr as [Hsr Z2]. apply andb_prop in Hsr as [Hsr Z1]. apply andb_prop in Hsr as [Hsr Z10].
apply andb_prop in Hsr as [Hpc4 Hrv4]. apply Z.eqb_eq in Hpc4.
unfold skelsO in Hsk4. apply andb_prop in Hsk4 as [Hlen4 Hsk4]. destruct (ss_mem eO2) as [|q0 qrest] eqn:Hmem4; [discriminate Hsk4|].
apply andb_prop in Hsk4 as [Hsk4 _]. apply andb_prop in Hsk4 as [J0 Hsk4].
destruct (nth_error qrest 17) as [qe|] eqn:Hqe; [|discriminate Hsk4]. destruct (nth_error qrest 21) as [qo|] eqn:Hqo; [|discriminate Hsk4].
apply andb_prop in Hsk4 as [Je Jo].
apply skel_is_sound in J0 as (J0a & J0lo & J0hi & J0b & J0c). apply skel_is_sound in Jo as (Joa & Jolo & Johi & Job & Joc). clear Je.
rewrite FW in J0b, J0lo.
assert (MEQ4 : forall z : word, ~ ((sp0 - 2144 - 2304 <= bv_unsigned z < sp0 - 2144) \/ errW (bv_unsigned z) \/ oflW (bv_unsigned z)) -> ms_mem ms4 z = mem2 z).
{ intros z Hz. apply (HF4 z). intros Hin. exact (Hz (WIN E2 _ _ WL2 E2_2 E2_4 Hin)). }
clear HF4.
assert (RD4 : forall (r : bv 5) v, reg_is eO2 (bv_unsigned r) v = true -> getr (ms_regs ms4) r = sv_denot E2 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E2 eO2 ms4 r HS4). }
set (regs4 := ms_regs ms4) in *.
assert (PRS4s : forall a, sp0 - 2144 - 2304 <= a < sp0 - 2144 -> apresent H (ms_mem ms4) a).
{ intros a Ha. apply (AF0x.st_ok_window_apresent_off H E2 eO2 ms4 0 q0 a HS4 ltac:(rewrite ?Hmem4; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite J0a, J0b, J0c. cbn [base_val]. rewrite E2_2. lia. }
set (Wr4 := fun a => (sp0 - 2144 - 2304 <= a < sp0 - 2144) \/ errW a \/ oflW a).
assert (Wr4d : forall a, Wr4 a \/ ~ Wr4 a) by (intros a; subst Wr4; cbn beta; unfold errW, oflW, AE2a.errW, AE2a.oflW; lia).
assert (Wr4i : forall a, Wr4 a -> stackW a \/ errW a \/ oflW a \/ False) by (intros a Ha; subst Wr4; cbn beta in Ha; unfold stackW, AE2a.stackW; destruct Ha as [Ha|Ha]; [left; lia | tauto]).
assert (Wr4p : forall a, Wr4 a -> ~ errW a -> ~ oflW a -> apresent H (ms_mem ms4) a).
{ intros a Ha He' Hof. subst Wr4. cbn beta in Ha. destruct Ha as [Hs | [Hx | Hx]]; [exact (PRS4s a Hs) | exfalso; exact (He' Hx) | exfalso; exact (Hof Hx)]. }
destruct (frameOX mem2 (ms_mem ms4) md2 md4 Wr4 (fun _ => False) HAR2 Wr4d Wr4i ltac:(intros a Hf; destruct Hf) MEQ4 Wr4p MD24) as (AV4 & PM4 & HAR4).
subst Wr4. cbv beta in AV4. clear Wr4d Wr4i Wr4p.
pose proof (st_ok_restrict_mkst tfibsegs H E2 _ _ HS4 eq_refl) as Hshape4. rewrite Hpc4 in Hshape4. fold regs4 in Hshape4.
assert (CELL : forall off v z, has_chunk eO2 0 off 8 v = true -> sv_denot E2 v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
val_mem tfibsegs (mrestrict H (ms_mem ms4)) (sp0 - 2144 + off) 8 z).
{ intros off v z Hh Hd Hz. unfold has_chunk in Hh. rewrite Hmem4 in Hh. cbn [nth_error] in Hh. apply existsb_exists in Hh as (c & Hc & Hcc). apply chunk_is_sound in Hcc. subst c.
pose proof (st_ok_mem_ok tfibsegs E2 eO2 _ HS4) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem4 in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs q0 ltac:(left; reflexivity)) as (_ & _ & _ & Hcs). rewrite J0a in Hcs. cbn [base_val] in Hcs. rewrite E2_2 in Hcs.
exact (val_of_chunk_ok tfibsegs E2 _ _ off 8 v z (proj1 (Forall_forall _ _) Hcs _ Hc) Hd Hz ltac:(cbn; lia)). }
assert (HCo : forall off v, In (off, v) cellsO2 -> has_chunk eO2 0 off 8 v = true) by (intros off v Hin; rewrite forallb_forall in HC4; exact (HC4 _ Hin)).
pose proof (same_but_materialized_frame md md1 MF1) as (_ & V01 & Z01 & _ & _ & _ & _ & _ & FD01 & _ & _ & FS01 & _).
pose proof (same_but_materialized_frame md1 md2 MF2) as (_ & V12 & Z12 & _ & _ & _ & _ & _ & FD12 & _ & _ & FS12 & _).
pose proof (same_but_materialized_frame _ md3 MF3) as (_ & V23 & Z23 & _ & _ & _ & _ & _ & FD23 & _ & _ & FS23 & _).
assert (MF34 : same_but_materialized md3 md4) by (subst md4; apply with_vm_backing_same).
pose proof (same_but_materialized_frame md3 md4 MF34) as (_ & V34 & Z34 & _ & _ & _ & _ & _ & FD34 & _ & _ & FS34 & _).
assert (MBtop : forall a, 0 <= a < 2 ^ 64 -> sp0 - 2144 <= a < sp0 -> mbyte tfibsegs (mrestrict H (ms_mem ms4)) a = mbyte tfibsegs (mrestrict H mem1) a).
{ intros a Hr Ha. unfold errW, oflW, AE2a.errW, AE2a.oflW in AV4, AV2. rewrite HO, HT in AV4, AV2. apply AE2y.mbyte_of_aview. rewrite AV4 by lia. apply AV2; lia. }
set (v8 := bv_unsigned (getr regs1 8%bv)). set (v9 := bv_unsigned (getr regs1 9%bv)). set (v18 := bv_unsigned (getr regs1 18%bv)). set (v19 := bv_unsigned (getr regs1 19%bv)).
assert (EV : forall i (r : bv 5) vv, Z.of_nat i = bv_unsigned r -> (i < 40)%nat -> vv = bv_unsigned (getr regs1 r) -> sv_denot E2 (SOff i 0) = Z_to_bv 64 vv).
{ intros i r vv Hi Hlt ->. cbn [sv_denot]. rewrite (E2old i Hlt), (E1reg i r Hi), Z.add_0_r. reflexivity. }
apply SRr_ret. split; [reflexivity|]. exists regs4, (ms_mem ms4), md4, fd, v8, v9, v18, v19.
split; [unfold cfg_at; rewrite Hshape4 at 1; reflexivity|].
split; [exact HAR4|].
split; [rewrite (RD4 10%bv _ Z10); reflexivity|].
split; [rewrite (RD4 1%bv _ Z1); reflexivity|].
split; [rewrite (RD4 2%bv _ Z2); cbn [sv_denot]; rewrite E2_2, FF; unfold w64; f_equal; lia|].
split; [rewrite (RD4 8%bv _ Z8); reflexivity|].
split; [rewrite (RD4 9%bv _ Z9); cbn [sv_denot]; rewrite E2_40, Z.add_0_r; apply Z_to_bv_bv_unsigned|].
split; [rewrite (RD4 18%bv _ Z18); reflexivity|].
split; [rewrite (RD4 19%bv _ Z19); reflexivity|].
split.
{ intros r Hin. assert (Hr : 0 <= r < 32) by (unfold AE2g.KEPTF in Hin; cbn in Hin; lia).
assert (Hur : bv_unsigned (Z_to_bv 5 r) = r) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; apply Z.mod_small; lia).
rewrite forallb_forall in HK4. pose proof (HK4 r ltac:(unfold KEPTO; unfold AE2g.KEPTF in Hin; cbn [In] in Hin |- *; lia)) as Hk. cbn beta in Hk.
rewrite (RD4 (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)) by (rewrite Hur; exact Hk).
cbn [sv_denot]. rewrite (E2old (Z.to_nat r) ltac:(lia)), (E1reg (Z.to_nat r) (Z_to_bv 5 r)) by (rewrite Hur; lia). rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
exact (QK r Hin). }
split; [exact Hfd|].
split; [rewrite <- FD01, <- FD12; exact Hfdn|].
split; [rewrite FD34, FD23; subst md2'; cbn [m_fds with_fds with_fs]; rewrite FD12, FD01; reflexivity|].
split; [rewrite FS34, FS23; subst md2'; cbn [m_fs with_fds with_fs]; rewrite FS12, FS01; reflexivity|].
split; [exact (eq_trans (proj1 MD24) (eq_trans V12 V01))|].
split; [exact (eq_trans (proj2 MD24) (eq_trans Z12 Z01))|].
split.
{ eapply os_kept_trans; [exact (os_kept_sbm _ _ MF1)|]. eapply os_kept_trans; [exact (os_kept_sbm _ _ MF2)|].
eapply os_kept_trans; [| exact (os_kept_sbm _ _ MF34)]. eapply os_kept_trans; [| exact (os_kept_sbm _ _ MF3)].
subst md2'. eapply os_kept_trans; [apply os_kept_with_fs | apply os_kept_with_fds]. }
split; [subst v8; apply u64_range|]. split; [subst v9; apply u64_range|]. split; [subst v18; apply u64_range|]. split; [subst v19; apply u64_range|].
rewrite FF.
split; [replace (sp0 - 2144 - 8) with (sp0 - 2144 + -8) by lia; apply (CELL (-8) _ _ (HCo _ _ ltac:(unfold cellsO2; INL))); [| unfold IO_RET; lia];
cbn [sv_denot]; rewrite (E2old 1%nat ltac:(lia)), (E1reg 1%nat 1%bv eq_refl), Q1, Z.add_0_r; reflexivity|].
split; [replace (sp0 - 2144 - 16) with (sp0 - 2144 + -16) by lia; apply (CELL (-16) _ _ (HCo (-16) (SOff 8 0) ltac:(unfold cellsO2; INL))); [exact (EV 8%nat 8%bv v8 eq_refl ltac:(lia) eq_refl) | subst v8; apply u64_range]|].
split; [replace (sp0 - 2144 - 24) with (sp0 - 2144 + -24) by lia; apply (CELL (-24) _ _ (HCo (-24) (SOff 9 0) ltac:(unfold cellsO2; INL))); [exact (EV 9%nat 9%bv v9 eq_refl ltac:(lia) eq_refl) | subst v9; apply u64_range]|].
split; [replace (sp0 - 2144 - 32) with (sp0 - 2144 + -32) by lia; apply (CELL (-32) _ _ (HCo (-32) (SOff 18 0) ltac:(unfold cellsO2; INL))); [exact (EV 18%nat 18%bv v18 eq_refl ltac:(lia) eq_refl) | subst v18; apply u64_range]|].
split; [replace (sp0 - 2144 - 40) with (sp0 - 2144 + -40) by lia; apply (CELL (-40) _ _ (HCo (-40) (SLit FO_FDOPEN_RA) ltac:(unfold cellsO2; INL))); [reflexivity | unfold FO_FDOPEN_RA; lia]|].
split; [replace (sp0 - 2144 - 48) with (sp0 - 2144 + -48) by lia; apply (CELL (-48) _ _ (HCo (-48) (SLit A_WB) ltac:(unfold cellsO2; INL))); [reflexivity | unfold A_WB; lia]|].
split; [replace (sp0 - 2144 - 56) with (sp0 - 2144 + -56) by lia; apply (CELL (-56) _ _ (HCo (-56) (SOff 40 0) ltac:(unfold cellsO2; INL))); [cbn [sv_denot]; rewrite E2_40, Z.add_0_r; reflexivity | apply u64_range]|].
split; [replace (sp0 - 2144 - 64) with (sp0 - 2144 + -64) by lia; apply (CELL (-64) _ _ (HCo (-64) (SLit FO_S2VAL) ltac:(unfold cellsO2; INL))); [reflexivity | unfold FO_S2VAL; lia]|].
split; [replace (sp0 - 2144 - 72) with (sp0 - 2144 + -72) by lia; apply (CELL (-72) _ _ (HCo (-72) (SOff 19 0) ltac:(unfold cellsO2; INL))); [exact (EV 19%nat 19%bv v19 eq_refl ltac:(lia) eq_refl) | subst v19; apply u64_range]|].
split; [replace (sp0 - 2144 - 80) with (sp0 - 2144 + -80) by lia; apply (CELL (-80) _ _ (HCo (-80) (SOff 32 0) ltac:(unfold cellsO2; INL))); [| exact Hcv];
cbn [sv_denot]; rewrite (E2old 32%nat ltac:(lia)), E1_32, Z.add_0_r, unsigned_lit_small by lia; reflexivity|].
split.
{ intros j rz off Hj. assert (Hoff : -64 <= off <= -8) by (do 8 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
apply (val_mem_frame tfibsegs (mrestrict H mem1)); [| exact (QS j rz off Hj)]. intros x Hx. apply MBtop; lia. }
split.
{
unfold has_chunk in Hofl4. rewrite Hmem4 in Hofl4. change (nth_error (q0 :: qrest) 22) with (nth_error qrest 21) in Hofl4. rewrite Hqo in Hofl4.
apply existsb_exists in Hofl4 as (c & Hc & Hcc). apply chunk_is_sound in Hcc. subst c.
pose proof (st_ok_mem_ok tfibsegs E2 eO2 _ HS4) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem4 in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs qo ltac:(right; eapply nth_error_In; exact Hqo)) as (_ & _ & _ & Hcs). rewrite Joa in Hcs. cbn [base_val] in Hcs.
rewrite <- (Z.add_0_l A_ofl_head).
exact (val_of_chunk_ok tfibsegs E2 _ _ A_ofl_head 8 (SLit 0) 0 (proj1 (Forall_forall _ _) Hcs _ Hc) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
split.
{ intros a Hr Hs Herr Hofl.
rewrite AV4; [| exact Hr | unfold stackW, AE2a.stackW in Hs; intros [X|[X|X]]; [lia | exact (Herr X) | exact (Hofl X)]].
rewrite AV2; [| exact Hr | unfold stackW, AE2a.stackW in Hs; intros [X|[X|X]]; [lia | exact (Herr X) | exact (Hofl X)]]. apply AV1; [exact Hr | unfold stackW, AE2a.stackW in Hs; lia]. }
split.
{ intros a Hs. unfold stackW, AE2a.stackW in Hs. unfold errW, oflW, AE2a.errW, AE2a.oflW in PM4, PM2. rewrite HO, HT in PM4, PM2.
destruct (Z_lt_le_dec a (sp0 - 2144 - 2304)) as [L|L]; [| destruct (Z_lt_le_dec a (sp0 - 2144)) as [L2|L2]; [apply PRS4s; lia|]].
- apply PM4; [lia | lia | lia |]. apply PM2; [lia | lia | lia |]. apply PM1, Hpres. lia.
- apply PM4; [lia | lia | lia |]. apply PM2; [lia | lia | lia |]. apply PRS1. lia. }
intros a Hr Herr Hofl Hp. apply PM4; [exact Hr | exact Herr | exact Hofl |]. apply PM2; [exact Hr | exact Herr | exact Hofl |]. apply PM1. exact Hp.
Qed.
End f.
End d.
