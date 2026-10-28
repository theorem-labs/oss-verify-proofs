(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI00 YI16 YK0p YP0h YI19.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m YA0l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0p.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE2y AE3i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2h AE2g AE2j AE2d AE2a AE27 AE24.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbq YE01 YK18 YI17 YE02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE6j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ff_cells_law (B : asyms) : Prop :=
forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md ->
arodata_okS tfibsegs B TFIB_RELRO_LO TFIB_RELRO_HI (aview tfibsegs (w_H W) mem) ->
cells_hold (mrestrict (w_H W) mem) io_cells /\ cells_hold (mrestrict (w_H W) mem) st_cells.
Lemma ffo_cstr_len_le : forall mp fuel (a : word) n,
mp (woff a n) = Some (Z_to_bv 8 0) -> (cstr_access_len_aux mp a fuel <= S n)%nat.
Proof.
intros mp fuel. induction fuel as [|fuel IH]; intros a n Hn; cbn [cstr_access_len_aux]; [lia|].
destruct (mp a) as [b|] eqn:Ha; [|lia].
destruct (bv_eqb b (Z_to_bv 8 0)) eqn:Hb; [lia|].
destruct n as [|n].
- exfalso. rewrite woff_0, Ha in Hn. injection Hn as ->. rewrite bv_eqb_refl in Hb. discriminate Hb.
- rewrite <- woff_succ in Hn. specialize (IH _ _ Hn). lia.
Qed.
Lemma same_io_fds_fs : forall md md', same_io md md' -> m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof. intros md md' (Efd & _ & Efsys & _). unfold m_fds, m_fs. rewrite Efd, Efsys. split; reflexivity. Qed.
Lemma ffo_in_img_find : forall a, in_img tfibsegs a -> find_segment tfibsegs a 1 <> None.
Proof.
intros a (sg & Hsg & Hrg) Hn. unfold tfibsegs, M.loaded_segments, Asan.Asan_loaded_segments in Hsg, Hn.
cbn [find_segment seg_base seg_size Z.of_N In
Asan.Asan_segment_000 Asan.Asan_segment_001
Asan.Asan_segment_002 Asan.Asan_segment_003] in Hsg, Hn.
repeat (destruct (_ && _)%bool eqn:?E in Hn; [discriminate Hn|]).
repeat match goal with E : (_ && _)%bool = false |- _ => apply Bool.andb_false_iff in E; destruct E as [E|E]; apply Z.leb_gt in E end.
all: destruct Hsg as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hrg; lia.
Qed.
Lemma ffo_mbyte_unhidden : forall (W : world tfibsegs) (m : word -> option byte) a,
in_img tfibsegs a -> 0 <= a < 2 ^ 64 -> mbyte tfibsegs (mrestrict (w_H W) m) a = mrb tfibsegs m (Z_to_bv 64 a) /\ w_H W (Z_to_bv 64 a) = false.
Proof.
intros W m a Hin Hr.
assert (Hh : w_H W (Z_to_bv 64 a) = false).
{ destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
pose proof (w_Hoff W _ E) as Hn. rewrite unsigned_lit_small in Hn by lia. exact (ffo_in_img_find a Hin Hn). }
split; [|exact Hh]. unfold mbyte, mrestrict, mrb. rewrite Hh. reflexivity.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis AIL : asink_img_laws tfibsegs B tfib_K.
Hypothesis ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AINTR : aintrin_realizes tfibsegs B OSet PC_MEMSET.
Hypothesis FFC : ff_cells_law B.
Lemma ffo_intrin_at_sbm : forall op pc, aintrin_realizes tfibsegs B op pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n (o : Z) raw,
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) memT) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok tfibsegs W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) memT) x n)
| OSet => True end) ->
SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom tfibsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem2 (d + i) =
match op with OCpy => aview tfibsegs (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
same_but_materialized mdc md2).
Proof.
intros op pc AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hsrc.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre tfibsegs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
assert (HDEST : dest_ok tfibsegs B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
destruct (awr_byte_present tfibsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Hno]. rewrite Hsp'.
split; [apply apresent_writable; exact Hp | auto]. }
eapply SRr_mono.
{ exact (AI lyc Sc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull Hsrc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write tfibsegs B LAWS ffc_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => (d <= a < d + n) \/ (sp0 + o - ESTACK <= a < sp0 + o)) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
- exact Hpres2.
- exact Hsame.
- intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; lia].
- exact HAR2.
- reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Heff|]. split; [exact Hfr|]. split; [exact Hpres2 | exact Hsame].
Qed.
Lemma ffo_openat_nodeX : forall ly S (W : world tfibsegs) regs mem md regs1 mem1 md1 (fs0 : Fs.Fs) (XA XB : TSet),
AR tfibsegs B ly S W mem md ->
ly_stk_lo ly + FOP_WIN <= spZ regs ->
garr8 tfibsegs (mrestrict (w_H W) mem) A_PATH (sink_path_Z ++ [0]) ->
AI tfibsegs (w_H W) (w_A W) md1 ->
fd_lookup (m_fds md1) (alloc_fd (m_fds md1)) = None -> m_fs md1 = fs0 ->
bv_unsigned (getr regs1 17) = 56 -> getr regs1 10 = w64 (2 ^ 64 - 100) -> getr regs1 11 = w64 A_PATH ->
getr regs1 12 = w64 33345 -> getr regs1 13 = w64 438 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ stackW regs a -> ~ errW a -> ~ oflW a -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) ->
(forall md' e, 1 <= e <= 4095 -> same_but_materialized md1 md' -> AI tfibsegs (w_H W) (w_A W) md' ->
srealizes tfibsegs (mkCfg (mkst (regupd regs1 10 (errno_ret e)) (v_addi (Z_to_bv 64 FO_ECALL) 4) mem1 (seg_rom tfibsegs)) md') XA) ->
(forall md' (fd : word), bv_unsigned fd < 2 ^ 31 -> fd_lookup (m_fds md1) fd = None ->
same_but_materialized (with_fds (fd_insert (m_fds md1) fd (FdFileW sink_path (Z_to_bv 64 0))) (with_fs (fs_set (m_fs md1) sink_path []) md1)) md' ->
AI tfibsegs (w_H W) (w_A W) md' ->
srealizes tfibsegs (mkCfg (mkst (regupd regs1 10 fd) (v_addi (Z_to_bv 64 FO_ECALL) 4) mem1 (seg_rom tfibsegs)) md') XB) ->
srealizes tfibsegs (mkCfg (pend_at regs1 (Z_to_bv 64 FO_ECALL) mem1 (seg_rom tfibsegs)) md1) (openat_shape fs0 XA XB).
Proof.
intros ly S W regs mem md regs1 mem1 md1 fs0 XA XB HAR Hslo Hpath HAI Hfree Hfs0 H17 H10 H11 H12 H13 HAV Kref Kcre.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (FW : FOP_WIN = 6400) by reflexivity. rewrite FW in Hslo.
destruct sink_path_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8). rewrite <- sink_path_eq in F1, F2, F3, F4, F5, F6, F7.
assert (PIMG : forall j, 0 <= j < 13 -> in_img tfibsegs (A_PATH + j)).
{ intros j Hj. exists Asan.Asan_segment_000. split; [left; reflexivity | unfold A_PATH; cbn; lia]. }
assert (Hpath1 : garr8 tfibsegs (mrestrict (w_H W) mem1) A_PATH (sink_path_Z ++ [0])).
{ eapply garr8_frame; [exact Hpath|]. intros x Hx. unfold sink_path_Z in Hx. cbn [length app] in Hx. unfold A_PATH in Hx.
apply AE2y.mbyte_of_aview. apply HAV; [lia | unfold stackW; lia | unfold errW, TFIB_TP; lia | unfold oflW, A_ofl_head; lia]. }
assert (Hraw : garr8 tfibsegs mem1 A_PATH (sink_path_Z ++ [0])).
{ intros j Hj. destruct (Hpath1 j Hj) as [Hv Hb]. split; [|exact Hb]. intros k Hk. pose proof (Hv k Hk) as X.
unfold sink_path_Z in Hj. cbn [length app] in Hj.
replace (A_PATH + Z.of_nat j + Z.of_nat k) with (A_PATH + (Z.of_nat j + Z.of_nat k)) in X |- * by lia.
destruct (ffo_mbyte_unhidden W mem1 (A_PATH + (Z.of_nat j + Z.of_nat k)) (PIMG (Z.of_nat j + Z.of_nat k) ltac:(lia)) ltac:(unfold A_PATH; lia)) as [E _].
rewrite E in X. unfold mbyte, mrb in *. exact X. }
assert (Hcstr : read_cstr (ms_read_byte (pend_at regs1 (Z_to_bv 64 FO_ECALL) mem1 (seg_rom tfibsegs))) (getr regs1 11) = CstrOk sink_path).
{ rewrite pend_read_byte_mrb, H11. change (w64 A_PATH) with (Z_to_bv 64 A_PATH). rewrite sink_path_eq.
apply (read_cstr_of_garr8 tfibsegs mem1 A_PATH sink_path_Z Hraw); [|cbn; lia]. unfold sink_path_Z. repeat (constructor; [lia|]). constructor. }
assert (Hav : ranges_avoid (w_H W) (open_copyins (pend_at regs1 (Z_to_bv 64 FO_ECALL) mem1 (seg_rom tfibsegs)))).
{ intros a n Hin. unfold open_copyins in Hin. rewrite pend_gpr1, pend_read_byte_mrb, H11 in Hin. change (w64 A_PATH) with (Z_to_bv 64 A_PATH) in Hin.
assert (Hlen : (cstr_access_len_aux (mrb tfibsegs mem1) (Z_to_bv 64 A_PATH) path_max <= 13)%nat).
{ apply ffo_cstr_len_le. destruct (Hraw 12%nat ltac:(unfold sink_path_Z; cbn; lia)) as [Hv _]. pose proof (Hv 0%nat ltac:(lia)) as X.
unfold sink_path_Z in X. cbn [nth app Z.of_nat Nat.add] in X. unfold mbyte in X. unfold woff, mrb. rewrite unsigned_lit_small by (unfold A_PATH; lia).
replace (A_PATH + Z.of_nat 12) with (A_PATH + 12 + 0) by lia. rewrite Z.add_0_r in X |- *. replace (A_PATH + 12 + 0) with (A_PATH + 12) in X by lia.
exact X. }
revert Hin Hlen. generalize (cstr_access_len_aux (mrb tfibsegs mem1) (Z_to_bv 64 A_PATH) path_max). intros L Hin Hlen.
destruct Hin as [Heq|[]]. injection Heq as <- <-.
intros k Hk. unfold woff. rewrite unsigned_lit_small by (unfold A_PATH; lia).
exact (proj2 (ffo_mbyte_unhidden W mem1 (A_PATH + Z.of_nat k) (PIMG (Z.of_nat k) ltac:(lia)) ltac:(unfold A_PATH; lia))). }
assert (Hdir : getr regs1 10 = AT_FDCWD) by (rewrite H10; unfold AT_FDCWD; apply bv_eq; reflexivity).
assert (Hfl : Z.ldiff (bv_unsigned (getr regs1 12)) open_ignored_flags = wr_create_flags) by (rewrite H12; vm_compute; reflexivity).
rewrite <- Hfs0. unfold openat_shape.
destruct (fs_under (m_fs md1) sink_path) eqn:Hun.
{
destruct (node_openat_tmp_isdir_lazy tfibsegs (w_H W) (w_A W) regs1 (Z_to_bv 64 FO_ECALL) mem1 (seg_rom tfibsegs) md1 sink_path sink_name_bytes
HAI H17 Hdir Hfl Hcstr F1 F3 F4 F5 F6 F7 F8 Hun Hav) as (Hnode & HAI' & Hsbm).
apply (srz_silent1 tfibsegs _ _ XA Hnode). apply (Kref _ EISDIR); [unfold EISDIR; lia | exact Hsbm | exact HAI']. }
destruct (node_openat_tmp_create_lazy tfibsegs (w_H W) (w_A W) regs1 (Z_to_bv 64 FO_ECALL) mem1 (seg_rom tfibsegs) md1 sink_path sink_name_bytes
HAI H17 Hdir Hfl Hcstr F1 F3 F4 F5 F6 F7 F8 Hun Hfree Hav) as [Hnode Hall].
apply (srz_alt2 tfibsegs _ {e : Z | In e openat_errnos} unit _ XA XB (exist _ ENOMEM ENOMEM_in_openat_errnos) tt Hnode).
- intros [e He]. cbn [open_ret open_md proj1_sig].
apply (Kref _ e); [exact (openat_errnos_range e He) | exact (proj2 (Hall (inl (exist _ e He)))) | exact (proj1 (Hall (inl (exist _ e He))))].
- intros []. cbn [open_ret open_md]. pose proof (Open.alloc_fd_le (m_fds md1)) as Hle.
apply (Kcre _ (alloc_fd (m_fds md1))); [lia | exact Hfree | exact (proj2 (Hall (inr tt))) | exact (proj1 (Hall (inr tt)))].
Qed.
Theorem tfib_afopen_x : afopen_x tfibsegs B tfib_K FF_pc_wrap_fopen FO_MALLOC_RA TFIB_RELRO_LO TFIB_RELRO_HI.
Proof.
intros W ly S regs mem md ch M XA XB HAI0 HPRE G10 G11 HNONE HMI HRO Hev Hlive Huni Hfree KXA KXB.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HNONE as (Henv & Hhead & Hnames).
pose proof HMI as (HX & HMimg & HMptr & HMmem & HM0 & HM47 & HMal & HMZ).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (FB : FILE_BLOCK = 1264) by reflexivity. assert (FS : AFOPEN_STK = 18624) by reflexivity. assert (FW : FOP_WIN = 6400) by reflexivity.
assert (FF : FO_FRAME = 2144) by reflexivity. assert (HAS : AMETA_SIZE = 3727360) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HO : A_ofl_head = 0x5f9688) by reflexivity. assert (HT : TFIB_TP = 0x5d8f90) by reflexivity.
rewrite FS in Hslo, Hpres, Hstk0, Hbot.
set (sp0 := spZ regs) in *.
pose proof (astdio_env_canary tfibsegs tfib_K _ Henv) as (cval & Hcv & Hcan2).
pose proof (acan_got_of_AR tfibsegs B tfib_K AIL ly S W mem md HAR) as Hcan1.
pose proof Henv as (Ethr & Enl & Elock & Epath & Emode & Erwa & Etrl & _).
destruct (FFC ly S W mem md HAR HRO) as [HIO HSTC].
assert (HIMG : ro_img (mrestrict (w_H W) mem)) by (exact (ffc_ro_img_of_arodata B (w_H W) mem _ _ TB HRO)).
assert (HOFLown : forall a, A_ofl_head <= a < A_ofl_head + 8 -> ~ aowned B ly S a).
{ intros a Ha Hown. rewrite HO in Ha.
destruct (ail_env _ _ _ AIL a ltac:(unfold aenv_addr; cbn [ak_threaded ak_need_locks ak_ofl_lock ak_path ak_mode ak_rwa ak_trailer ak_canary tfib_K]; unfold A_ofl_lock; lia)) as (Hi & Hns & _).
apply Hns. exact (proj1 (al_owned_image _ _ LAWS ly S W mem md a HAR Hi) Hown). }
assert (HERRown : forall a, TFIB_TP - 164 <= a < TFIB_TP - 160 -> ~ aowned B ly S a).
{ intros a Ha Hown. assert (Hi : in_img tfibsegs a) by (apply (ail_errno_img _ _ _ AIL); rewrite (ts_errno B TB); unfold TFIB_ERRNO; rewrite HT in Ha; lia).
pose proof (proj1 (al_owned_image _ _ LAWS ly S W mem md a HAR Hi) Hown) as HX2. rewrite (ts_owned B TB) in HX2.
apply Exists_exists in HX2 as (r & Hr & Hin). unfold Tfib_owned_static in Hr. cbn [In] in Hr. unfold in_zr in Hin. rewrite HT in Ha.
repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Hin; lia|]). destruct Hr. }
unshelve (eapply (fopen_LAX B LAWS TB ly S W regs mem md cval HAR Hra Hal16 ltac:(rewrite FW; lia) Hshi ltac:(rewrite FW; intros a Ha; apply Hpres; lia)
Htp G10 G11 HIO HSTC HIMG Hcan1 Hcan2 Hcv Ethr Enl Elock Hhead HOFLown HERRown
(fun m => fd_lookup (m_fds m) (alloc_fd (m_fds m)) = None) Hfree
ltac:(intros m m' SBM Hm; pose proof (same_but_materialized_frame m m' SBM) as (_ & _ & _ & _ & _ & _ & _ & _ & EFD & _); rewrite EFD; exact Hm)
_ XA XB HAI0)).
{ intros regs1 mem1 md1 fs0 XA' XB' HAI Hfree1 Hfs0 H17 H10 H11 H12 H13 HAV Kref Kcre.
exact (ffo_openat_nodeX ly S W regs mem md regs1 mem1 md1 fs0 XA' XB' HAR ltac:(rewrite FW; lia) Epath HAI Hfree1 Hfs0 H17 H10 H11 H12 H13 HAV Kref Kcre). }
-
intros W1 c1 Hw1 HAI1 HL. unfold LAPOST_A in HL. destruct HL as [-> HREF].
destruct HREF as (regs' & mem' & md' & e & -> & He & HAR' & HPRSV & H10' & V' & L' & SIO' & OK' & SBM' & TERR & TOFL & TAV & TPRS & TPM).
fold sp0 in TAV, TPRS. unfold stackW in TAV, TPRS. rewrite FW in TAV, TPRS. unfold errW, oflW in TAV, TPM. rewrite ?HT, ?HO in TAV. rewrite ?HT, ?HO in TPM. rewrite HO in TOFL. rewrite HT in TERR.
assert (OFLimg : forall a, 0x5f9688 <= a < 0x5f9688 + 8 -> in_img tfibsegs a).
{ intros a Ha. exact (proj1 (ail_env _ _ _ AIL a ltac:(unfold aenv_addr; cbn [ak_threaded ak_need_locks ak_ofl_lock ak_path ak_mode ak_rwa ak_trailer ak_canary tfib_K]; unfold A_ofl_lock; lia))). }
assert (ERRimg : forall a, 0x5d8f90 - 164 <= a < 0x5d8f90 - 160 -> in_img tfibsegs a).
{ intros a Ha. apply (ail_errno_img _ _ _ AIL). rewrite (ts_errno B TB). unfold TFIB_ERRNO. lia. }
pose proof (same_io_fds_fs _ _ SIO') as [EFDS EFS].
assert (J0 : ajournal tfibsegs B AFOPEN_STK sp0 [sink_token] ly S W mem md [] ly S W mem' md' 0).
{ split; [exact HAR'|]. split; [apply layout_le_refl|]. split; [lia|]. split; [apply wle_refl|].
split; [apply aos_step_of_same_io; exact SIO'|].
split; [reflexivity|]. split; [lia|]. split; [lia|].
split.
{   intros a Ha Hs. rewrite FS in Hs. apply TAV; [clear - Ha C1; lia | clear - Ha Hs; lia | clear - Ha C1; lia | clear - Ha C1; lia]. }
split.
{   intros p0 n0 i Hin _ Hi Hnf.
destruct (al_blocks _ _ LAWS ly S W mem md p0 n0 HAR Hin) as (_ & Hq0 & Hq0c & _).
apply TAV; [clear - Hq0 Hq0c Hi C1; lia | clear - Hq0c Hi Hceil Hslo; lia | |].
- intros Hr. exact (blk_img tfibsegs B LAWS ly S W mem md p0 n0 (p0 + i) HAR Hin ltac:(lia) (ERRimg _ Hr)).
- intros Hr. exact (blk_img tfibsegs B LAWS ly S W mem md p0 n0 (p0 + i) HAR Hin ltac:(lia) (OFLimg _ Hr)). }
split.
{   intros a Hi Hns Hne Hsp. pose proof (ffa_img_range a Hi) as Ra.
apply TAV; [lia | clear - Ra Hslo Hceil C1; lia | | ].
- rewrite (ts_errno B TB) in Hne. unfold TFIB_ERRNO in Hne. clear - Hne. lia.
- intros Hr. apply (Hsp (sink_open_token [sink_token] ltac:(left; reflexivity))). unfold AOFL_HEAD. cbn. lia. }
split.
{   intros cid pos a Hin Hr Hnf.
destruct (frames_bounds tfibsegs B LAWS ly S W mem md cid pos HAR Hin) as (Hf0' & Hfc & Hfapp').
pose proof (fs_frame_bytes_nonneg cid) as Hnn. unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
destruct Hr as [Hr | Hr].
- apply TAV; [clear - Hr Hf0' Hfc C1; lia | clear - Hr Hfc Hceil Hslo; lia | |].
+ intros Ho. exact (frm_img tfibsegs B LAWS ly S W mem md cid pos a HAR Hin ltac:(lia) (ERRimg _ Ho)).
+ intros Ho. exact (frm_img tfibsegs B LAWS ly S W mem md cid pos a HAR Hin ltac:(lia) (OFLimg _ Ho)).
- pose proof (AE2y.shadow_addr_bounds (frame_addr ly cid pos) ltac:(clear - Hf0' Hfc C1 C4 Hnn; unfold kHighMemEnd; lia)) as [B1 B2].
pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hnn) as Hse.
pose proof (AE2y.shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(clear - Hf0' Hfc C1 C4 Hnn; unfold kHighMemEnd; lia)) as [U1 U2].
apply TAV; [clear - Hr B1 U2 Hse; unfold kLowMemEnd, kHighShadowEnd in *; lia | clear - Hr B1 U2 Hse Lbeg Hslo; unfold kLowMemEnd, kHighShadowEnd, kHighMemBeg in *; lia | |].
+ clear - Hr B1 U2 Hse. unfold kLowMemEnd, kHighShadowEnd in *. lia.
+ clear - Hr B1 U2 Hse. unfold kLowMemEnd, kHighShadowEnd in *. lia. }
split; [intros p0 n0 i H1 H2; exfalso; exact (H2 H1)|].
split; [intros a Ha; rewrite FS in Ha; destruct (Z_lt_le_dec a (sp0 - 6400)) as [L|L]; [apply TPM; [clear - Ha Hslo Hceil C1 Hshi H47; lia | clear - Ha Hslo Hceil C1; lia | clear - Ha Hslo Hceil C1; lia | apply Hpres; exact Ha] | apply TPRS; lia]|].
split; [exact Hstk|].
split.
{   intros a HXa Hne. destruct (AR_extra_law_ok tfibsegs B ly S W mem md a HAR HXa) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
apply TAV; [clear - Xapp C1; unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; lia | | |].
- intros Hs. apply Xs. clear - Hs Hslo Hshi. lia.
- intros Hr. exact (Xi (ERRimg _ Hr)).
- intros Ho. exact (Xi (OFLimg _ Ho)). }
exact HQT. }
apply (KXA W _ Hw1 HAI1). exists ly, S, regs', mem', md', e.
split; [reflexivity|]. split; [exact J0|]. split; [exact HPRSV|]. split; [exact H10'|]. split; [reflexivity|]. split; [reflexivity|].
split.
{
split; [| split; [unfold ak_ofl_head; cbn [ak_ofl_lock tfib_K]; unfold A_ofl_lock; replace (6264448 + 8) with 6264456 by reflexivity; exact TOFL | rewrite EFDS; exact Hnames]].
apply (astdio_env_frame tfibsegs tfib_K (mrestrict (w_H W) mem)); [|exact Henv].
intros a Ha. unfold aenv_addr in Ha. cbn [ak_threaded ak_need_locks ak_ofl_lock ak_path ak_mode ak_rwa ak_trailer ak_canary tfib_K] in Ha.
unfold A_threaded, A_need_locks, A_ofl_lock, A_PATH, AE2k.A_WB, AE2k.A_RWA, A_TRAILER, FF_canary in Ha.
destruct (Z_lt_le_dec a 0x5f9688) as [L1|L1]; [| destruct (Z_lt_le_dec a (0x5f9688 + 8)) as [L2|L2]].
- apply AE2y.mbyte_of_aview. apply TAV; clear - Ha L1 Hslo Lbeg; lia.
-
unfold ak_ofl_head in Hhead. cbn [ak_ofl_lock tfib_K] in Hhead. unfold A_ofl_lock in Hhead. replace (6264448 + 8) with 6264456 in Hhead by reflexivity.
replace a with (0x5f9688 + Z.of_nat (Z.to_nat (a - 0x5f9688))) by lia.
rewrite (TOFL (Z.to_nat (a - 0x5f9688)) ltac:(lia)), (Hhead (Z.to_nat (a - 0x5f9688)) ltac:(lia)). reflexivity.
- apply AE2y.mbyte_of_aview. apply TAV; clear - Ha L2 Hslo Lbeg; lia. }
split; [exact EFDS|]. split; [exact EFS|].
split; [exact He|]. rewrite (ts_errno B TB). unfold TFIB_ERRNO. replace 6131436 with (0x5d8f90 - 164) by reflexivity. exact TERR.
-
intros W1 c1 Hw1 HAI1 HL. unfold LAPOST_B in HL. destruct HL as [-> HCRE].
destruct HCRE as (regsT & memT & mdT & fd & v8 & v9 & v18 & v19 & -> & HART & T10 & T1 & T2 & T8 & T9 & T18 & T19 & TK & Hfd & Hfdn & TFDS & TFS & TV & TL & TOK &
Hv8 & Hv9 & Hv18 & Hv19 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & CS & TOFL & TAV & TPRS & TPM).
enough (REST : SRr tfibsegs W (cfg_at tfibsegs PC_MALLOC regsT memT mdT) (afopen_postB tfibsegs B tfib_K AFOPEN_STK W ly S regs mem md))
by (exact (SRr_srz tfibsegs _ _ _ _ REST HAI1 (fun W' c' Hw HA HP => KXB W' c' Hw HA HP))).
fold sp0 in T2, C8, C16, C24, C32, C40, C48, C56, C64, C72, C80, CS, TAV, TPRS. rewrite FF in T2, C8, C16, C24, C32, C40, C48, C56, C64, C72, C80.
unfold stackW in TAV, TPRS. rewrite FW in TAV, TPRS. unfold errW, oflW in TAV, TPM. rewrite ?HT, ?HO in TAV. rewrite ?HT, ?HO in TPM. rewrite HO in TOFL.
assert (OFLimg : forall a, 0x5f9688 <= a < 0x5f9688 + 8 -> in_img tfibsegs a).
{ intros a Ha. exact (proj1 (ail_env _ _ _ AIL a ltac:(unfold aenv_addr; cbn [ak_threaded ak_need_locks ak_ofl_lock ak_path ak_mode ak_rwa ak_trailer ak_canary tfib_K]; unfold A_ofl_lock; lia))). }
assert (ERRimg : forall a, 0x5d8f90 - 164 <= a < 0x5d8f90 - 160 -> in_img tfibsegs a).
{ intros a Ha. apply (ail_errno_img _ _ _ AIL). rewrite (ts_errno B TB). unfold TFIB_ERRNO. lia. }
pose proof TOK as (Oio & Opipes & Oproc).
assert (JT : ajournal tfibsegs B AFOPEN_STK sp0 [sink_token] ly S W mem md [] ly S W memT mdT 0).
{ split; [exact HART|]. split; [apply layout_le_refl|]. split; [lia|]. split; [apply wle_refl|].
split.
{
split; [exact Oio|]. split; [exact Opipes|].
split.
{ intros fd0. rewrite TFDS. destruct (bv_eq_dec _ fd0 fd) as [->|Hne].
- right. split; [left; exact Hfdn|]. right. exists (Z_to_bv 64 0). unfold fd_insert. cbn [fd_lookup fst]. rewrite bv_eqb_refl. reflexivity.
- left. unfold fd_insert. cbn [fd_lookup fst]. replace (bv_eqb fd fd0) with false by (symmetry; apply bv_eqb_neq; intros E; exact (Hne (eq_sym E))).
fold (fd_remove (m_fds md) fd). apply fd_lookup_remove_neq. exact Hne. }
split; [intros q Hq; rewrite TFS; apply fs_lookup_set_neq; exact Hq|].
split; [intros Hso; rewrite TFS; apply fs_set_sorted; exact Hso|].
split; [exact Oproc|].
intros Hc. exfalso. apply Hc. apply sink_open_token. left. reflexivity. }
split; [reflexivity|]. split; [lia|]. split; [lia|].
split.
{   intros a Ha Hs. rewrite FS in Hs. apply TAV; [clear - Ha C1; lia | clear - Ha Hs; lia | clear - Ha C1; lia | clear - Ha C1; lia]. }
split.
{   intros p0 n0 i Hin _ Hi Hnf.
destruct (al_blocks _ _ LAWS ly S W mem md p0 n0 HAR Hin) as (_ & Hq0 & Hq0c & _).
apply TAV; [clear - Hq0 Hq0c Hi C1; lia | clear - Hq0c Hi Hceil Hslo; lia | |].
- intros Hr. exact (blk_img tfibsegs B LAWS ly S W mem md p0 n0 (p0 + i) HAR Hin ltac:(lia) (ERRimg _ Hr)).
- intros Hr. exact (blk_img tfibsegs B LAWS ly S W mem md p0 n0 (p0 + i) HAR Hin ltac:(lia) (OFLimg _ Hr)). }
split.
{   intros a Hi Hns Hne Hsp. pose proof (ffa_img_range a Hi) as Ra.
apply TAV; [lia | clear - Ra Hslo Hceil C1; lia | | ].
- rewrite (ts_errno B TB) in Hne. unfold TFIB_ERRNO in Hne. clear - Hne. lia.
- intros Hr. apply (Hsp (sink_open_token [sink_token] ltac:(left; reflexivity))). unfold AOFL_HEAD. cbn. lia. }
split.
{   intros cid pos a Hin Hr Hnf.
destruct (frames_bounds tfibsegs B LAWS ly S W mem md cid pos HAR Hin) as (Hf0' & Hfc & Hfapp').
pose proof (fs_frame_bytes_nonneg cid) as Hnn. unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
destruct Hr as [Hr | Hr].
- apply TAV; [clear - Hr Hf0' Hfc C1; lia | clear - Hr Hfc Hceil Hslo; lia | |].
+ intros Ho. exact (frm_img tfibsegs B LAWS ly S W mem md cid pos a HAR Hin ltac:(lia) (ERRimg _ Ho)).
+ intros Ho. exact (frm_img tfibsegs B LAWS ly S W mem md cid pos a HAR Hin ltac:(lia) (OFLimg _ Ho)).
- pose proof (AE2y.shadow_addr_bounds (frame_addr ly cid pos) ltac:(clear - Hf0' Hfc C1 C4 Hnn; unfold kHighMemEnd; lia)) as [B1 B2].
pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hnn) as Hse.
pose proof (AE2y.shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(clear - Hf0' Hfc C1 C4 Hnn; unfold kHighMemEnd; lia)) as [U1 U2].
apply TAV; [clear - Hr B1 U2 Hse; unfold kLowMemEnd, kHighShadowEnd in *; lia | clear - Hr B1 U2 Hse Lbeg Hslo; unfold kLowMemEnd, kHighShadowEnd, kHighMemBeg in *; lia | |].
+ clear - Hr B1 U2 Hse. unfold kLowMemEnd, kHighShadowEnd in *. lia.
+ clear - Hr B1 U2 Hse. unfold kLowMemEnd, kHighShadowEnd in *. lia. }
split; [intros p0 n0 i H1 H2; exfalso; exact (H2 H1)|].
split; [intros a Ha; rewrite FS in Ha; destruct (Z_lt_le_dec a (sp0 - 6400)) as [L|L]; [apply TPM; [clear - Ha Hslo Hceil C1 Hshi H47; lia | clear - Ha Hslo Hceil C1; lia | clear - Ha Hslo Hceil C1; lia | apply Hpres; exact Ha] | apply TPRS; lia]|].
split; [exact Hstk|].
split.
{   intros a HXa Hne. destruct (AR_extra_law_ok tfibsegs B ly S W mem md a HAR HXa) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
apply TAV; [clear - Xapp C1; unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; lia | | |].
- intros Hs. apply Xs. clear - Hs Hslo Hshi. lia.
- intros Hr. exact (Xi (ERRimg _ Hr)).
- intros Ho. exact (Xi (OFLimg _ Ho)). }
exact HQT. }
assert (RTsp : spZ regsT = sp0 + -2240) by (unfold spZ; rewrite T2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (RTgp : getr regsT 3 = w64 (as_gp B)) by (etransitivity; [exact (TK 3 ltac:(unfold AE2g.KEPTF; cbn; tauto)) | exact Hgp]).
assert (RTtp : getr regsT 4 = w64 (as_tp B)) by (etransitivity; [exact (TK 4 ltac:(unfold AE2g.KEPTF; cbn; tauto)) | exact Htp]).
pose proof (ts_code B TB) as TC.
assert (CHT : chain_pre ly (aview tfibsegs (w_H W) memT) regsT []).
{ unfold chain_pre. split; [unfold raZ; rewrite T1; unfold w64; rewrite unsigned_lit_small; unfold FO_MALLOC_RA; lia|].
destruct (frame0_ok ly regsT); [|reflexivity].
assert (Hbad : bad_next (spZ regsT) (ly_top ly) (s0Z regsT) = true).
{ unfold bad_next, s0Z. rewrite T8, RTsp. unfold w64, A_WB; rewrite unsigned_lit_small by lia.
destruct (Z.leb_spec 0x20e60 (sp0 + -2240)) as [L|L]; [reflexivity | exfalso; clear - L Hslo Lbeg; lia]. }
rewrite Hbad. reflexivity. }
assert (TRT : In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT []) (as_universe B)).
{ unfold call_trace0, unwind_of_chain. unfold raZ. rewrite T1. unfold w64. rewrite unsigned_lit_small by (unfold FO_MALLOC_RA; lia).
rewrite TC in Huni |- *. cbn. exact Huni. }
unfold cfg_at. replace (w64 PC_MALLOC) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite TC; reflexivity).
eapply SRr_bind.
{ apply (aj_malloc_at04_io tfibsegs B LAWS ffc_segs_low ENV ML AMALLOC W regsT memT AFOPEN_STK sp0 [sink_token] ly S W mem md [] ly S mdT 0 1264 (-2240) (w64 FO_MALLOC_RA) [] JT T10);
rewrite ?RTsp, ?FS, ?Has; try lia.
- unfold MALLOC_MAX. lia.
- reflexivity.
- exact RTgp.
- exact RTtp.
- exact T1.
- apply AE2y.ret_ok_lit; [unfold FO_MALLOC_RA; lia | reflexivity].
- exact CHT.
- exact TRT. }
cbv beta. intros W2 c2 HWLE (ly2 & S2 & regs2 & mem2 & md2 & f & -> & J2 & HPR2 & U10 & Hfr2 & SIO2 & Hf0 & Hab2 & HCK).
pose proof J2 as (HAR2 & _).
assert (Hblk2 : In (f, 1264) (ablocks B ly2 S2)) by (rewrite Hab2; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 f 1264 HAR2 Hblk2) as (Hf16 & _ & Hfceil & Hfapp & Hfbytes & Hfdisj & _).
assert (RQ : req_size 1264 = 1264) by reflexivity. rewrite RQ in *.
assert (Hfnew : ~ In (f, 1264) (ablocks B ly S)).
{ intros Hin. rewrite Hab2, map_app in Hfdisj. cbn [map fst snd] in Hfdisj.
pose proof (pairwise_In _ _ (f, req_size 1264) (f, req_size 1264) _ _ eq_refl Hfdisj ltac:(apply in_map_iff; exists (f, 1264); split; [reflexivity | exact Hin]) ltac:(left; reflexivity)) as HD.
unfold zdisjoint in HD. cbn [fst snd] in HD. rewrite RQ in HD. lia. }
assert (HBam : amem_range f 1264).
{ clear - Hfapp Hf0 C1. unfold in_app, amem_range, ASAN_CEIL, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
assert (Hfhi : f + 4096 <= 2 ^ 47) by (clear - Hfceil C1; lia).
pose proof (same_io_fds_fs _ _ SIO2) as [EFDS2 EFS2].
assert (HP2 : forall r (rb : bv 5), acallee_saved r -> Z_to_bv 5 r = rb -> getr regs2 rb = getr regsT rb) by (intros r rb Hr <-; apply HPR2; exact Hr).
assert (R2sp : getr regs2 2 = w64 (sp0 - 2240)) by (rewrite (HP2 2 2%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), T2; unfold w64; f_equal; lia).
assert (R2_8 : getr regs2 8 = w64 A_WB) by (rewrite (HP2 8 8%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact T8).
assert (R2_9 : getr regs2 9 = fd) by (rewrite (HP2 9 9%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact T9).
assert (R2_18 : getr regs2 18 = w64 A_WB) by (rewrite (HP2 18 18%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact T18).
assert (R2_19 : getr regs2 19 = w64 A_canary) by (rewrite (HP2 19 19%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact T19).
assert (R2K : forall r, In r AE2g.KEPTF -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite (HPR2 r) by (unfold AE2g.KEPTF in Hr; cbn in Hr; unfold acallee_saved; lia). exact (TK r Hr). }
change (mkCfg (mkst regs2 (w64 FO_MALLOC_RA) mem2 (seg_rom tfibsegs)) md2) with (cfg_at tfibsegs FO_MALLOC_RA regs2 mem2 md2).
eapply SRr_bind; [exact (fopen_LB W2 regs2 mem2 md2 f U10 Hf0 Hfhi Hf16)|].
cbv beta. intros W3 c3 _ (-> & regs3 & md3 & -> & MF3 & Q10 & Q11 & Q12 & Q1 & Q8 & QK).
assert (J3 : ajournal tfibsegs B AFOPEN_STK sp0 [sink_token] ly S W mem md [] ly2 S2 W2 mem2 md3 1).
{ replace 1 with (0 + 1) by reflexivity.
eapply (ajournal_exec tfibsegs B LAWS ffc_segs_low AFOPEN_STK sp0 [sink_token] ly S W mem md [] ly2 S2 W2 mem2 md2 (0 + 1) mem2 md3 (fun _ => False) J2);
[intros x _; reflexivity | apply mem_grows_refl | intros x _; reflexivity | exact MF3 | intros a Ha; destruct Ha]. }
assert (HQ3 : forall r (rb : bv 5), In r KEPTB -> Z_to_bv 5 r = rb -> getr regs3 rb = getr regs2 rb) by (intros r rb Hr <-; apply QK; exact Hr).
assert (R3sp : spZ regs3 = sp0 + -2240) by (unfold spZ; rewrite (HQ3 2 2%bv ltac:(unfold KEPTB; cbn; tauto) ltac:(apply bv_eq; reflexivity)), R2sp; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (R3gp : getr regs3 3 = w64 (as_gp B)).
{ rewrite (HQ3 3 3%bv ltac:(unfold KEPTB; cbn; tauto) ltac:(apply bv_eq; reflexivity)), (HP2 3 3%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)). exact RTgp. }
assert (R3tp : getr regs3 4 = w64 (as_tp B)).
{ rewrite (HQ3 4 4%bv ltac:(unfold KEPTB; cbn; tauto) ltac:(apply bv_eq; reflexivity)), (HP2 4 4%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)). exact RTtp. }
change (cfg_at tfibsegs PC_MEMSET regs3 mem2 md3) with (mkCfg (mkst regs3 (Z_to_bv 64 PC_MEMSET) mem2 (seg_rom tfibsegs)) md3).
eapply SRr_bind.
{ apply (ffo_intrin_at_sbm OSet PC_MEMSET AINTR W2 regs3 mem2 AFOPEN_STK sp0 [sink_token] ly S W mem md [] ly2 S2 md3 1 f 0 232 (-2240) (w64 FO_MEMSET_RA) J3 Q10 Q11 Q12);
rewrite ?R3sp, ?FS, ?Hes; try lia.
- reflexivity.
- exact R3gp.
- exact R3tp.
- exact Q1.
- apply AE2y.ret_ok_lit; [unfold FO_MEMSET_RA; lia | reflexivity].
- intros a Ha. split; [| clear - Ha Hfceil Hceil Hslo; lia]. right. right. left. exists f, 1264. split; [exact Hblk2|]. split; [exact Hfnew | rewrite RQ; lia].
- clear - HBam. unfold amem_range in *. lia.
- apply (range_addressable_of_block tfibsegs B LAWS ly2 S2 W2 mem2 md2 f 1264 f 232 HAR2 Hblk2); [lia | rewrite RQ; lia].
- intros _. apply (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 mem2 md2 f 1264 f 232 HAR2 Hblk2); [lia | rewrite RQ; lia | lia]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & J4 & HPR4 & V10 & HZ4 & FR4 & PM4 & MF4).
pose proof HCK as (K1 & K2 & K3 & K4 & K5 & K6). rewrite Has in K1, K5, K6. rewrite Hes in FR4.
pose proof J4 as (HAR4 & Hly4 & _).
pose proof Hly4 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem4 md4 f 1264 HAR4 Hblk2) as (_ & _ & _ & _ & Hfbytes4 & _ & _). rewrite RQ in Hfbytes4.
pose proof (ffa_blk_off_img B ly2 S2 W2 mem4 md4 f 1264 HAR4 Hblk2) as HBimg. rewrite RQ in HBimg.
assert (KHI : forall a, sp0 - 2240 <= a < 2 ^ 64 -> aview tfibsegs (w_H W2) mem4 a = aview tfibsegs (w_H W) memT a).
{ intros a Ha. rewrite FR4; [| lia | clear - Ha Hfceil Hceil Hslo; lia | lia]. apply K1; [clear - Ha Hceil Hslo; lia | lia]. }
assert (KIMG : forall a, in_img tfibsegs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview tfibsegs (w_H W2) mem4 a = aview tfibsegs (w_H W) memT a).
{ intros a Hi Hns Hne. pose proof (ffa_img_range a Hi) as Ra. unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg.
rewrite FR4; [| lia | clear - Ra HBimg; lia | clear - Ra Hslo Lbeg; lia]. apply K3; assumption. }
assert (OFLns : forall a, 0x5f9688 <= a < 0x5f9688 + 8 -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha. destruct (ail_env _ _ _ AIL a ltac:(unfold aenv_addr; cbn [ak_threaded ak_need_locks ak_ofl_lock ak_path ak_mode ak_rwa ak_trailer ak_canary tfib_K]; unfold A_ofl_lock; lia)) as (_ & Hns & Hne). exact (conj Hns Hne). }
assert (HP4 : forall r (rb : bv 5), acallee_saved r -> Z_to_bv 5 r = rb -> getr regs4 rb = getr regs3 rb) by (intros r rb Hr <-; apply HPR4; exact Hr).
assert (X2 : getr regs4 2 = w64 (sp0 - 2240)) by (rewrite (HP4 2 2%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), (HQ3 2 2%bv ltac:(unfold KEPTB; cbn; tauto) ltac:(apply bv_eq; reflexivity)); exact R2sp).
assert (X8 : getr regs4 8 = w64 f) by (rewrite (HP4 8 8%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact Q8).
assert (X9 : getr regs4 9 = fd) by (rewrite (HP4 9 9%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), (HQ3 9 9%bv ltac:(unfold KEPTB; cbn; tauto) ltac:(apply bv_eq; reflexivity)); exact R2_9).
assert (X18 : getr regs4 18 = w64 A_WB) by (rewrite (HP4 18 18%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), (HQ3 18 18%bv ltac:(unfold KEPTB; cbn; tauto) ltac:(apply bv_eq; reflexivity)); exact R2_18).
assert (X19 : getr regs4 19 = w64 A_canary) by (rewrite (HP4 19 19%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), (HQ3 19 19%bv ltac:(unfold KEPTB; cbn; tauto) ltac:(apply bv_eq; reflexivity)); exact R2_19).
assert (XK : forall r, In r AE2g.KEPTF -> getr regs4 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. unfold AE2g.KEPTF in Hr. cbn [In] in Hr.
rewrite (HPR4 r) by (unfold acallee_saved; lia). rewrite (QK r) by (unfold KEPTB; cbn [In]; lia). apply R2K. unfold AE2g.KEPTF. cbn [In]. lia. }
assert (Henv4 : astdio_env tfibsegs tfib_K (mrestrict (w_H W2) mem4)) by (exact (astdio_env_kept tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J4 Henv)).
pose proof Henv4 as (Ethr4 & Enl4 & Elock4 & _).
assert (HRO4 : arodata_okS tfibsegs B TFIB_RELRO_LO TFIB_RELRO_HI (aview tfibsegs (w_H W2) mem4)).
{ intros a Ha Hns Hne.
assert (Hi : in_img tfibsegs a).
{ destruct Ha as [(sg & Hsg & Hw & Hrg)|Ha']; [exists sg; split; [exact Hsg | exact Hrg] |].
exists Asan.Asan_segment_002. split; [do 2 right; left; reflexivity | unfold TFIB_RELRO_LO, TFIB_RELRO_HI in Ha'; cbn; lia]. }
rewrite (KIMG a Hi Hns Hne).
pose proof (ffa_img_range a Hi) as Ra. pose proof Hne as Hne'. rewrite (ts_errno B TB) in Hne'. unfold TFIB_ERRNO in Hne'.
rewrite TAV; [exact (HRO a Ha Hns Hne) | lia | clear - Ra Hslo Lbeg; lia | clear - Hne'; lia |].
intros Ho. destruct Ha as [(sg & Hsg & Hw & Hrg)|Ha']; [| unfold TFIB_RELRO_LO, TFIB_RELRO_HI in Ha'; clear - Ho Ha'; lia].
unfold tfibsegs, M.loaded_segments, Asan.Asan_loaded_segments in Hsg. cbn [In] in Hsg.
destruct Hsg as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hw, Hrg; first [discriminate Hw | clear - Ho Hrg; lia]. }
assert (HIMG4 : ro_img (mrestrict (w_H W2) mem4)) by (exact (ffc_ro_img_of_arodata B (w_H W2) mem4 _ _ TB HRO4)).
destruct (FFC ly2 S2 W2 mem4 md4 HAR4 HRO4) as [HIO4 HSTC4].
pose proof (acan_got_of_AR tfibsegs B tfib_K AIL ly2 S2 W2 mem4 md4 HAR4) as Hcan1'.
assert (Hcan2' : val_mem tfibsegs (mrestrict (w_H W2) mem4) FF_canary 8 cval).
{ apply (AE2y.val_mem_kept (w_H W) (w_H W2) mem mem4); [| exact Hcan2]. intros k Hk.
destruct (ail_env _ _ _ AIL (FF_canary + k) ltac:(unfold aenv_addr; cbn [ak_threaded ak_need_locks ak_ofl_lock ak_path ak_mode ak_rwa ak_trailer ak_canary tfib_K]; lia)) as (Hi & Hns & Hne).
rewrite (KIMG _ Hi Hns Hne). unfold FF_canary. rewrite (ts_errno B TB) in Hne. unfold TFIB_ERRNO, FF_canary in Hne. apply TAV; lia. }
assert (Hhead4 : val_mem tfibsegs (mrestrict (w_H W2) mem4) A_ofl_head 8 0).
{ apply (AE2y.val_mem_kept (w_H W) (w_H W2) memT mem4); [| rewrite HO; exact TOFL]. intros k Hk. rewrite HO.
destruct (OFLns (0x5f9688 + k) ltac:(lia)) as [Hns Hne]. exact (KIMG _ (OFLimg (0x5f9688 + k) ltac:(lia)) Hns Hne). }
assert (HOFLown4 : forall a, A_ofl_head <= a < A_ofl_head + 8 -> ~ aowned B ly2 S2 a).
{ intros a Ha Hown. rewrite HO in Ha. destruct (OFLns a Ha) as [Hns _]. apply Hns. exact (proj1 (al_owned_image _ _ LAWS ly2 S2 W2 mem4 md4 a HAR4 (OFLimg _ Ha)) Hown). }
assert (DK : forall a v, sp0 - 2240 <= a -> a + 8 <= 2 ^ 64 -> val_mem tfibsegs (mrestrict (w_H W) memT) a 8 v -> val_mem tfibsegs (mrestrict (w_H W2) mem4) a 8 v).
{ intros a v Ha Ha' Hv. apply (AE2y.val_mem_kept (w_H W) (w_H W2) memT mem4); [| exact Hv]. intros k Hk. apply KHI. lia. }
assert (HFDL4 : fd_lookup (m_fds md4) fd = Some (FdFileW sink_path (Z_to_bv 64 0))).
{ pose proof (same_but_materialized_frame _ _ MF4) as (_ & _ & _ & _ & _ & _ & _ & _ & FD34 & _). pose proof (same_but_materialized_frame _ _ MF3) as (_ & _ & _ & _ & _ & _ & _ & _ & FD23 & _).
rewrite FD34, FD23, EFDS2, TFDS. unfold fd_insert. cbn [fd_lookup fst]. rewrite bv_eqb_refl. reflexivity. }
change (mkCfg (mkst regs4 (w64 FO_MEMSET_RA) mem4 (seg_rom tfibsegs)) md4) with (cfg_at tfibsegs FO_MEMSET_RA regs4 mem4 md4).
eapply SRr_bind.
{ apply (fopen_LC B LAWS TB ly2 S2 W2 regs regs4 mem4 md4 f cval v8 v9 v18 v19 fd (FdFileW sink_path (Z_to_bv 64 0)) HAR4 Hra Hal16);
fold sp0; rewrite ?Eslo, ?Eshi, ?FW, ?FF.
- lia.
- exact Hshi.
- intros a Ha. apply PM4. destruct (Z_lt_le_dec a (sp0 - 2240)) as [L0|L0]; [apply K6; lia|].
apply K5; [clear - Ha Hceil Hslo Hshi H47; lia | clear - L0; lia |]. apply TPRS. lia.
- exact X2.
- exact X8.
- exact X9.
- exact X18.
- exact X19.
- exact XK.
- exact Hfd.
- exact Hf0.
- exact Hfhi.
- exact Hf16.
- intros i Hi. rewrite (HZ4 i Hi). reflexivity.
- intros a Ha. exact (proj1 (Hfbytes4 a Ha)).
- intros a Ha. exact (proj2 (Hfbytes4 a Ha)).
- left. clear - Hfceil Hceil Hslo. lia.
- exact HBimg.
- exact HBam.
- exact HSTC4.
- exact HIMG4.
- exact Hcan1'.
- exact Hcan2'.
- exact Hcv.
- exact Ethr4.
- exact Enl4.
- exact Elock4.
- exact Hhead4.
- exact HOFLown4.
- exact Hv8.
- exact Hv9.
- exact Hv18.
- exact Hv19.
- apply DK; [lia | lia | exact C8].
- apply DK; [lia | lia | exact C16].
- apply DK; [lia | lia | exact C24].
- apply DK; [lia | lia | exact C32].
- apply DK; [lia | lia | exact C40].
- apply DK; [lia | lia | exact C48].
- apply DK; [lia | lia | exact C56].
- apply DK; [lia | lia | exact C64].
- apply DK; [lia | lia | exact C72].
- apply DK; [lia | lia | exact C80].
- intros j rz off Hj. assert (Hoff : -64 <= off <= -8) by (do 8 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
apply DK; [lia | lia | exact (CS j rz off Hj)].
- exact HFDL4.
- intros rd wr. discriminate. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HAR5 & HPR5 & Y10 & V5 & L5 & SIO5 & OK5 & MF5 & FD5 & FS5 & HFILE & HOFL5 & AV5 & PRS5 & PM5).
pose proof J4 as (_ & _ & Hsecs4 & Hwle4 & Hos4 & Hfrs4 & Hnev4 & _ & F1 & F2 & F3 & F4 & Hgone4 & Hpres4 & _ & F5 & HQT4).
pose proof Hly4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
fold sp0 in AV5, PRS5. unfold stackC in AV5, PRS5. rewrite FW in AV5, PRS5. unfold blkW, oflW in AV5. rewrite HO in AV5.
rewrite FS in F1, Hpres4.
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 6400 <= a < sp0) -> ~ (f <= a < f + 1264) -> ~ (0x5f9688 <= a < 0x5f9688 + 8) ->
aview tfibsegs (w_H W2) mem5 a = aview tfibsegs (w_H W2) mem4 a) by (intros a Hr Hs Hb Ho; apply AV5; assumption).
assert (J5 : ajournal tfibsegs B AFOPEN_STK sp0 [sink_token] ly S W mem md [] ly2 S2 W2 mem5 md5 1).
{ split; [exact HAR5|]. split; [exact Hly4|]. split; [exact Hsecs4|]. split; [exact Hwle4|].
split; [eapply aos_step_same_io; [exact Hos4 | exact SIO5]|].
split; [exact Hfrs4|]. split; [exact Hnev4|]. split; [lia|].
split.
{   intros a Ha Hs. rewrite FS in Hs. rewrite KB; [exact (F1 a Ha Hs) | clear - Ha C1; lia | clear - Ha Hs; lia | clear - Ha Hfceil; lia | clear - Ha C1; lia]. }
split.
{   intros p0 n0 i Hin Hin2 Hi Hnf.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem4 md4 p0 n0 HAR4 Hin2) as (_ & Hq0 & Hq0c & _ & _ & Hdj & _).
assert (Hne : (p0, n0) <> (f, 1264)) by (intros E; apply Hfnew; rewrite <- E; exact Hin).
rewrite KB; [exact (F2 p0 n0 i Hin Hin2 Hi Hnf) | clear - Hq0 Hq0c Hi C1; lia | clear - Hq0c Hi Hceil Hslo; lia | |].
- rewrite Hab2 in Hdj. rewrite map_app in Hdj. cbn [map fst snd] in Hdj.
rewrite Hab2 in Hin2. apply in_app_iff in Hin2. destruct Hin2 as [Hold | [E|[]]]; [| exfalso; exact (Hne (eq_sym E))].
pose proof (pairwise_In _ _ (p0, req_size n0) (f, req_size 1264) _ _ eq_refl Hdj ltac:(apply in_map_iff; exists (p0, n0); split; [reflexivity | exact Hold]) ltac:(left; reflexivity)) as HD.
unfold zdisjoint in HD. cbn [fst snd] in HD. rewrite RQ in HD. clear - HD Hi. lia.
- intros Hr. exact (blk_img tfibsegs B LAWS ly2 S2 W2 mem4 md4 p0 n0 (p0 + i) HAR4 Hin2 ltac:(lia) (OFLimg _ Hr)). }
split.
{   intros a Hi Hns Hne Hsp. pose proof (ffa_img_range a Hi) as Ra. unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg.
rewrite KB; [exact (F3 a Hi Hns Hne Hsp) | lia | clear - Ra Hslo Hceil C1; lia | clear - Ra HBimg; lia |].
intros Hr. apply (Hsp (sink_open_token [sink_token] ltac:(left; reflexivity))). unfold AOFL_HEAD. cbn. lia. }
split.
{   intros cid pos a Hin Hr Hnf.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs4; exact Hin).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem4 md4 cid pos HAR4 Hin2) as (Hf0' & Hfc & Hfapp').
pose proof (sep_block_frame tfibsegs B LAWS ly2 S2 W2 mem4 md4 f 1264 cid pos HAR4 Hblk2 Hin2) as Hd. rewrite RQ in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
assert (EFA : forall c q, frame_addr ly2 c q = frame_addr ly c q) by (intros c q; unfold frame_addr; pose proof Hly4 as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
rewrite !EFA in Hf0', Hfc, Hd.
rewrite KB; [exact (F4 cid pos a Hin Hr Hnf) | | | |]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
- destruct Hr as [Hr|Hr]; [clear - Hr Hf0' Hfc C1; lia|].
pose proof (AE2y.shadow_addr_bounds (frame_addr ly cid pos) ltac:(clear - Hf0' Hfc C1 C4 Hnn; unfold kHighMemEnd; lia)) as [B1 B2].
pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hnn) as Hse.
pose proof (AE2y.shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(clear - Hf0' Hfc C1 C4 Hnn; unfold kHighMemEnd; lia)) as [U1 U2].
clear - Hr B1 U2 Hse. unfold kLowMemEnd, kHighShadowEnd in *. lia.
- destruct Hr as [Hr|Hr]; [clear - Hr Hfc Hceil Hslo; lia|].
pose proof (AE2y.shadow_addr_bounds (frame_addr ly cid pos) ltac:(clear - Hf0' Hfc C1 C4 Hnn; unfold kHighMemEnd; lia)) as [B1 B2].
pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hnn) as Hse.
pose proof (AE2y.shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(clear - Hf0' Hfc C1 C4 Hnn; unfold kHighMemEnd; lia)) as [U1 U2].
clear - Hr B1 U2 Hse Lbeg Hslo. unfold kLowMemEnd, kHighShadowEnd, kHighMemBeg in *. lia.
- destruct Hr as [Hr|Hr]; [clear - Hr Hd; lia|].
pose proof (AE2y.shadow_addr_bounds (frame_addr ly cid pos) ltac:(clear - Hf0' Hfc C1 C4 Hnn; unfold kHighMemEnd; lia)) as [B1 B2].
pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hnn) as Hse.
pose proof (AE2y.shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(clear - Hf0' Hfc C1 C4 Hnn; unfold kHighMemEnd; lia)) as [U1 U2].
clear - Hr B1 U2 Hse HBam. unfold amem_range, kLowMemEnd, kHighShadowEnd, kHighMemBeg, kHighMemEnd in *. lia.
- destruct Hr as [Hr|Hr]; [intros Ho; exact (frm_img tfibsegs B LAWS ly S W mem md cid pos a HAR Hin ltac:(lia) (OFLimg _ Ho))|].
pose proof (AE2y.shadow_addr_bounds (frame_addr ly cid pos) ltac:(clear - Hf0' Hfc C1 C4 Hnn; unfold kHighMemEnd; lia)) as [B1 B2].
pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hnn) as Hse.
pose proof (AE2y.shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(clear - Hf0' Hfc C1 C4 Hnn; unfold kHighMemEnd; lia)) as [U1 U2].
clear - Hr B1 U2 Hse. unfold kLowMemEnd, kHighShadowEnd in *. lia. }
split; [exact Hgone4|].
split; [intros a Ha; destruct (Z_lt_le_dec a (sp0 - 6400)) as [L|L]; [apply PM5; apply Hpres4; exact Ha | apply PRS5; lia]|].
split; [exact Hstk|].
split.
{   intros a HXa Hne. assert (HXc : Exists (in_zr a) (ly_extra ly2)) by (rewrite Eextra; exact HXa).
destruct (AR_extra_law_ok tfibsegs B ly2 S2 W2 mem4 md4 a HAR4 HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
rewrite KB; [exact (F5 a HXa Hne) | clear - Xapp C1; unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; lia | | |].
- intros Hs. apply Xs. rewrite Eslo, Eshi. clear - Hs Hslo Hshi. lia.
- intros Hr. exact (Xb f 1264 Hblk2 ltac:(rewrite RQ; lia)).
- intros Ho. exact (Xi (OFLimg _ Ho)). }
exact HQT4. }
assert (Hnr : forall fds (w : word), fd_names_path fds sink_path = false -> fd_names_path (fd_remove fds w) sink_path = false).
{ clear. intros fds w. unfold fd_remove. induction fds as [|[kk x] r IH]; [reflexivity|]. cbn [List.filter fst].
intros HN. destruct (negb (bv_eqb kk w)).
- cbn [fd_names_path]. destruct x; cbn [fd_names_path] in HN |- *;
try (apply Bool.orb_false_iff in HN as [H1 H2]; rewrite H1; cbn [orb]); auto.
- apply IH. destruct x; cbn [fd_names_path] in HN; try (apply Bool.orb_false_iff in HN as [H1 H2]); auto. }
pose proof (same_but_materialized_frame _ _ MF4) as (_ & _ & _ & _ & _ & _ & _ & _ & FD34 & _ & _ & FS34 & _).
pose proof (same_but_materialized_frame _ _ MF3) as (_ & _ & _ & _ & _ & _ & _ & _ & FD23 & _ & _ & FS23 & _).
assert (EFDS5 : m_fds md5 = fd_insert (m_fds md) fd (FdFileW sink_path (Z_to_bv 64 0))) by (rewrite FD5, FD34, FD23, EFDS2; exact TFDS).
assert (EFS5 : m_fs md5 = fs_set (m_fs md) sink_path []) by (rewrite FS5, FS34, FS23, EFS2; exact TFS).
apply SRr_ret. unfold afopen_postB. exists ly2, S2, regs5, mem5, md5, f.
split; [reflexivity|]. split; [exact J5|]. split; [exact HPR5|]. split; [exact Y10|]. split; [exact Hfrs4|].
split; [exact Hf0|]. split; [rewrite FB; exact Hab2|].
split.
{ exists (bv_unsigned fd), [], []. pose proof (u64_range fd) as Hfdu.
split; [reflexivity|]. split; [constructor|]. split; [cbn; unfold SINK_MAX; lia|].
split; [exact (astdio_env_kept tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J5 Henv)|].
split; [exact HFILE|].
split; [unfold ak_ofl_head; cbn [ak_ofl_lock tfib_K]; unfold A_ofl_lock; replace (6264448 + 8) with 6264456 by reflexivity; rewrite <- HO; exact HOFL5|].
split; [lia|].
split; [rewrite EFS5, fs_lookup_set_eq; reflexivity|].
split; [rewrite Z_to_bv_bv_unsigned, EFDS5; unfold fd_insert; cbn [fd_lookup fst length Z.of_nat]; rewrite bv_eqb_refl; reflexivity|].
rewrite Z_to_bv_bv_unsigned, EFDS5, fd_remove_insert. apply Hnr. exact Hnames. }
split; [rewrite EFS5; apply fs_lookup_set_eq | exact EFS5].
Qed.
End h.
End g.
