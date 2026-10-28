(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI00 YI16 YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0p.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE2y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2d AE2c AE26.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbq YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ffa_img_cover : forall ly S md, ALedger tfibsegs ly S md ->
fst (ly_img ly) <= TFIB_IMG_LO /\ TFIB_IMG_END <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S md L. split.
- destruct (al_img _ _ _ _ L Asan.Asan_segment_000 ltac:(left; reflexivity)) as [H _].
cbn in H. unfold TFIB_IMG_LO. lia.
- destruct (al_img _ _ _ _ L Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H].
cbn in H. unfold TFIB_IMG_END. lia.
Qed.
Lemma ffa_blk_off_img : forall B ly S (W : world tfibsegs) mem md p n,
AR tfibsegs B ly S W mem md -> In (p, n) (ablocks B ly S) -> p + req_size n <= TFIB_IMG_LO \/ TFIB_IMG_END <= p.
Proof.
intros B ly S W mem md p n (M & L & _) Hin. pose proof (ffa_img_cover ly S md L) as [C1 C2]. unfold TFIB_IMG_LO, TFIB_IMG_END in *.
apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hn).
pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _). rewrite Hn in G7.
pose proof (req_size_pos n ltac:(lia)) as [Q _].
destruct (Z.le_gt_cases (p + req_size n) 0x10000) as [|H1]; [left; lia|].
destruct (Z.le_gt_cases 0x5fb000 p) as [|H2]; [right; lia|]. exfalso.
apply (client_byte_not_img B ly S _ (Z.max p 0x10000) M).
- left. exists k. rewrite Hu. unfold ck_n. rewrite Hn. refine (conj Hk (conj Hst _)). lia.
- unfold in_zr. lia.
Qed.
Lemma ffa_img_range : forall a, in_img tfibsegs a -> 0x10000 <= a < 0x5fb000.
Proof.
intros a (sg & Hin & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
(map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H.
destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Lemma fd_remove_insert : forall fds (fd : word) e, fd_remove (fd_insert fds fd e) fd = fd_remove fds fd.
Proof.
intros fds fd e. unfold fd_remove, fd_insert. cbn [List.filter fst].
replace (bv_eqb fd fd) with true by (symmetry; apply bv_eqb_eq; reflexivity). cbn [negb].
induction fds as [|[k x] r IH]; [reflexivity|]. cbn [List.filter fst].
destruct (bv_eqb k fd) eqn:Ek; cbn [negb]; [exact IH|]. cbn [List.filter fst]. rewrite Ek. cbn [negb]. rewrite IH. reflexivity.
Qed.
Lemma app_eq_prefix : forall {X} (a b c d : list X), a ++ b = c ++ d -> length a = length c -> a = c /\ b = d.
Proof.
intros X a. induction a as [|x a IH]; intros b c d E L.
- destruct c; [split; [reflexivity | exact E] | discriminate L].
- destruct c as [|y c]; [discriminate L|]. cbn in E. injection E as <- E'. injection L as L'.
destruct (IH b c d E' L') as [<- <-]. split; reflexivity.
Qed.
Ltac INL := cbn; repeat (first [left; reflexivity | right]).
Section S.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis AIL : asink_img_laws tfibsegs B tfib_K.
Theorem tfib_afwrite_spec : afwrite_spec tfibsegs B tfib_K FW_ENTRY.
Proof.
intros W ly S regs mem md ch p n f Sg bs HPRE G10 G11 G12 G13 Hblk HSINK HSRC Hn Hn1 HSmax HSf HSstk Hp0 HSam HSra HShull.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HSINK as (fd & Wb & P & ESg & Hok & Hmax & Henv & Hfile & Hhead & Hfnz & Hfs & Hfd & Huniq).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FB : FILE_BLOCK = 1264) by reflexivity. assert (FS : AFWRITE_STK = 6352) by reflexivity. assert (FS' : AFW_STK = 6352) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md f FILE_BLOCK HAR Hblk) as (Hf16 & Hf0 & Hfceil & Hfapp & Hfbytes & Hfdisj & Hfrange).
assert (RQ : req_size FILE_BLOCK = FILE_BLOCK) by reflexivity. rewrite RQ in *.
pose proof (ffa_blk_off_img B ly S W mem md f FILE_BLOCK HAR Hblk) as HBimg. rewrite RQ in HBimg.
assert (HBam : amem_range f FILE_BLOCK).
{ clear - Hfapp Hf0 C1. unfold in_app, amem_range, ASAN_CEIL, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. rewrite ?RQ in *. lia. }
assert (Hfhi : f + FILE_BLOCK <= 2 ^ 47) by (clear - Hfceil C1; lia).
pose proof Hfile as [HST HWIN]. pose proof HST as (Hfdr & _).
pose proof (astdio_env_canary tfibsegs tfib_K _ Henv) as (cval & Hcv & Hcan2).
pose proof (acan_got_of_AR tfibsegs B tfib_K AIL ly S W mem md HAR) as Hcan1.
assert (HPlen : Z.of_nat (length P) <= 1024).
{ destruct HWIN as [(-> & _) | (_ & _ & _ & _ & _ & HL)]; [cbn; lia | unfold FILE_BUFSIZ in HL; exact HL]. }
assert (HBstk : f + FILE_BLOCK <= spZ regs - AFW_STK \/ spZ regs <= f).
{   left. rewrite FS'. rewrite FS in Hslo. clear - Hfceil Hceil Hslo. lia. }
assert (HSstk' : p + n <= spZ regs - AFW_STK \/ spZ regs <= p) by (rewrite FS'; rewrite FS in HSstk; exact HSstk).
assert (Hlen : Z.of_nat (length Wb) + Z.of_nat (length P) + n <= SINK_MAX) by (rewrite ESg, length_app, Nat2Z.inj_add in HSmax; lia).
assert (HBra : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (f + 240) 1024).
{ apply (range_addressable_of_block tfibsegs B LAWS ly S W mem md f FILE_BLOCK (f + 240) 1024 HAR Hblk); rewrite ?RQ, ?FB; clear - Hf0; lia. }
assert (HBhull : shadow_hull_vis (aview tfibsegs (w_H W) mem) (f + 240) 1024).
{ apply (shadow_hull_vis_of_block tfibsegs B LAWS ly S W mem md f FILE_BLOCK (f + 240) 1024 HAR Hblk); rewrite ?RQ, ?FB; clear - Hf0; lia. }
assert (HSf' : p + n <= f \/ f + FILE_BLOCK <= p) by exact HSf.
eapply SRr_mono.
{ apply (tfib_afwrite B LAWS TB ly S W regs mem md f fd n p cval P bs Wb HAR Hra Hal16);
[ rewrite FS'; rewrite FS in Hslo; exact Hslo | exact Hshi | intros a Ha; apply Hpres; rewrite FS; rewrite FS' in Ha; exact Ha
| exact Hgp | exact Htp | exact G10 | exact G11 | exact G12 | exact G13 | exact Hfile | exact Hf0 | exact Hfhi | exact Hf16 | exact Hfdr
| exact Hfbytes | exact HBstk | exact HBimg | exact HBam | exact HBra | exact HBhull
| exact HSRC | exact Hn | exact Hn1 | exact Hp0 | clear - HSam Hn1 C4; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia
| exact HSf' | exact HSstk' | exact HSam | exact HSra | exact HShull | exact Hcan1 | exact Hcan2 | exact Hcv
| exact Hfd | exact Hfs | exact Hlen ]. }
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Wb' & P' & -> & HAR' & HPRES' & A10' & Evm & Elz & HOK & HCAT & HPL' & HHDR' & HP' & HFS' & HSO' & HFDS' & HFSo & HFR' & HPM').
fold (w_H W) in HFR', HPM', HHDR', HP'.
assert (MB : forall a, 0 <= a < 2 ^ 64 -> ~ (f <= a < f + FILE_BLOCK) -> ~ (spZ regs - AFWRITE_STK <= a < spZ regs) ->
mbyte tfibsegs (mrestrict (w_H W) mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ intros a Hr Hb Hs. apply mbyte_of_aview. apply HFR'; [exact Hr | exact Hb | rewrite FS'; rewrite FS in Hs; exact Hs]. }
assert (IMGK : forall a, in_img tfibsegs a -> mbyte tfibsegs (mrestrict (w_H W) mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ intros a Hi. pose proof (ffa_img_range a Hi) as Ra. apply MB; [lia | intros Hr; exact (blk_img tfibsegs B LAWS ly S W mem md f FILE_BLOCK a HAR Hblk ltac:(rewrite RQ; exact Hr) Hi) |].
rewrite FS. clear - Ra Hslo Hceil C1 FS. rewrite FS in Hslo. lia. }
assert (ENVK : forall a, aenv_addr tfib_K a -> mbyte tfibsegs (mrestrict (w_H W) mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ intros a Ha. apply IMGK. exact (proj1 (ail_env _ _ _ AIL a Ha)). }
exists regs', mem', md'.
split. { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{
split; [exact HAR'|]. split; [apply layout_le_refl|]. split; [lia|]. split; [apply wle_refl|].
split.
{
pose proof HOK as (Oio & Opipes & Oproc).
split; [exact Oio|]. split; [exact Opipes|].
split.
{ intros fd0. destruct (Nat.eqb (length Wb') (length Wb)) eqn:EL; [left; rewrite HFDS'; reflexivity|].
destruct (bv_eq_dec _ fd0 (Z_to_bv 64 fd)) as [->|Hne].
- right. split; [right; eexists; exact Hfd | right; eexists; rewrite HFDS'; apply fd_lookup_insert_eq].
- left. rewrite HFDS'. apply fd_lookup_insert_neq. exact Hne. }
split; [intros q Hq; exact (HFSo q Hq)|]. split; [exact HSO'|]. split; [exact Oproc|].
intros Hc. exfalso. exact (Hc (asink_fp_open f)). }
split; [reflexivity|]. split; [lia|]. split; [lia|].
split.
{   intros a Ha Hs. apply HFR'; [clear - Ha C1; lia | clear - Ha Hfceil; lia | rewrite FS'; rewrite FS in Hs; exact Hs]. }
split.
{   intros p0 n0 i Hin _ Hi Hnf.
destruct (al_blocks _ _ LAWS ly S W mem md p0 n0 HAR Hin) as (_ & Hq0 & Hq0c & _).
apply HFR'; [clear - Hq0 Hq0c Hi C1; lia | | rewrite FS'; clear - Hq0c Hi Hceil Hslo FS; rewrite FS in Hslo; lia].
intros Hr. apply Hnf. apply (proj2 (in_asink_fp f (p0 + i))). left. exact Hr. }
split.
{   intros a Hi Hns He _. unfold aview. rewrite (IMGK a Hi). reflexivity. }
split.
{   intros cid pos a Hin Hr Hnf.
destruct (frames_bounds tfibsegs B LAWS ly S W mem md cid pos HAR Hin) as (Hf0' & Hfc & Hfapp').
pose proof (sep_block_frame tfibsegs B LAWS ly S W mem md f FILE_BLOCK cid pos HAR Hblk Hin) as Hd. rewrite RQ in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
pose proof (fs_frame_bytes_nonneg cid) as Hnn. unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
destruct Hr as [Hr | Hr].
- apply HFR'; [clear - Hr Hf0' Hfc C1; lia | clear - Hr Hd; lia | rewrite FS'; clear - Hr Hfc Hceil Hslo FS; rewrite FS in Hslo; lia].
- pose proof (AE2y.shadow_addr_bounds (frame_addr ly cid pos) ltac:(clear - Hf0' Hfc C1 C4 Hnn; unfold kHighMemEnd; lia)) as [B1 B2].
pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hnn) as Hse.
pose proof (AE2y.shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(clear - Hf0' Hfc C1 C4 Hnn; unfold kHighMemEnd; lia)) as [T1 T2].
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (_ & _ & _ & _ & _ & _ & Lbeg).
apply HFR'; [clear - Hr B1 T2 Hse; unfold kLowMemEnd, kHighShadowEnd in *; lia | | rewrite FS'; clear - Hr B1 T2 Hse Lbeg Hslo FS; unfold kLowMemEnd, kHighShadowEnd, kHighMemBeg in *; rewrite FS in Hslo; lia].
clear - Hr B1 T2 Hse HBam Hfhi FB. unfold amem_range, kLowMemEnd, kHighShadowEnd, kHighMemBeg, kHighMemEnd in *. rewrite FB in *. lia. }
split; [intros p0 n0 i H1 H2; exfalso; exact (H2 H1)|].
split; [intros a Ha; apply HPM'; apply Hpres; exact Ha|].
split; [exact Hstk|].
split.
{   intros a HX He. destruct (AR_extra_law_ok tfibsegs B ly S W mem md a HAR HX) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
apply HFR'; [clear - Xapp C1; unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; lia | exact (fun Hr => Xb f FILE_BLOCK Hblk ltac:(rewrite RQ; exact Hr)) |].
rewrite FS'. intros Hs. apply Xs. clear - Hs Hslo Hshi FS. rewrite FS in Hslo. lia. }
exact HQT. }
split; [exact HPRES'|]. split; [exact A10'|].
exists fd, Wb', P'.
split; [rewrite ESg, <- app_assoc, <- HCAT; reflexivity|].
split. { unfold bytes_ok in *. apply Forall_app. split; [exact Hok | exact (garr8_bytes_ok tfibsegs _ _ _ HSRC)]. }
split; [rewrite length_app; lia|].
split; [exact (astdio_env_frame tfibsegs tfib_K _ _ ENVK Henv)|].
split.
{
assert (HC : forall o nn v, In (o, nn, v) (hdr_cells f (f + 240 + Z.of_nat (length P')) fd) -> val_mem tfibsegs (mrestrict (w_H W) mem') (f + o) (N.to_nat nn) v).
{ intros o nn v Hin. unfold hdr_is in HHDR'. exact (proj1 (Forall_forall _ _) HHDR' (o, nn, v) Hin). }
split.
- unfold file_static. cbn [ak_close ak_read ak_write ak_seek tfib_K]. unfold FILE_BUF_OFF, FILE_BUFSIZ, U32M1.
split; [exact Hfdr|].
repeat split; (first [apply (HC _ 8%N) | apply (HC _ 4%N)]; unfold hdr_cells; INL).
- right. unfold FILE_BUF_OFF, FILE_BUFSIZ, U32M1.
split; [replace (f + 240 + 1024) with (f + 1264) by lia; apply (HC _ 8%N); unfold hdr_cells; INL|].
split; [apply (HC _ 8%N); unfold hdr_cells; INL|]. split; [apply (HC _ 8%N); unfold hdr_cells; INL|]. split; [apply (HC _ 4%N); unfold hdr_cells; INL|].
split; [exact HP' | exact HPL']. }
split.
{ eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply ENVK. unfold aenv_addr, ak_ofl_head in *. cbn [ak_ofl_lock tfib_K] in *. cbn in Hx. lia. }
split; [exact Hfnz|]. split; [exact HFS'|].
destruct (Nat.eqb_spec (length Wb') (length Wb)) as [EL|NL].
- destruct (app_eq_prefix Wb' P' Wb (P ++ bs) HCAT EL) as [-> _]. rewrite HFDS'. split; [exact Hfd | exact Huniq].
- rewrite HFDS'. split; [apply fd_lookup_insert_eq|]. rewrite fd_remove_insert. exact Huniq.
Qed.
End S.
End g.
