(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Stdio/PFmreadMW.v, with its module names changed; 125 of its 196 lines of code are new or changed and 1146 lines of the source are left out. *)
(* pcap_source_next on libreac v1.9.0's ASan build (lib/A, 0x8181c) and ASan+UBSan build (lib/B, 0x815b8): the
   image-free lemmas of the fit-A phase that both builds use: the model's facts at a record that the buffer holds
   (Section model) and the __asan_memmove contract inside the caller's journal (Section mm).

   IMAGE-FREE: the text names no image. It Requires only lib/Reusable, lib/A/Stdio/PSource.v (bytesZ),
   lib/A/Rt/MemmoveDef.v (amemmove_realizes, over a segs variable) and lib/A/Prog/PcapSourceNextSpec.v (the shared
   statement's model lift nxF, nx_q .. nx_rec, and Pau's model PSN). aj_memmove_atS is stated over a `segs` Variable;
   its proof uses only lib/Reusable/YCbq.v (ecall_pre_at, awr_byte_present, ajournal_after_write) and YA0n.v
   (SRr_mono), so it needs neither lib/A/Prog/YC85.v nor YC85G.v. *)
(* Modified by Theorem Labs, 2026-10: MOVED here unchanged (no statement or proof text altered) so that one copy serves
   both images: fa_nth_byte .. fa_rec_tagged from lib/A/Prog/PcapSourceNextFitAModel.v, aj_memmove_atS from
   lib/A/Prog/PcapSourceNextFitAHelp.v. lib/B/Prog/PcapSourceNextFitA.v held a verbatim copy of both, because
   FitAModel and FitAHelp Require lib/A/Prog/PcapSourceNextDefs.v and PcapSyms / PcapList (image A), which a lib/B
   file may not Require (the porter); that copy is deleted and lib/B FitA Requires this file. FitAModel and
   FitAHelp Require Export this file, so their lib/A users keep every name. *)
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Rt Require Import MemmoveDef.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The model at a record that the buffer holds (cap >= incl > 0)                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma fa_nth_byte : forall (C : list Z) n, bytes_ok C -> 0 <= nth n C 0 < 256.
Proof.
  intros C n HC. destruct (Nat.lt_ge_cases n (length C)) as [Hl|Hl].
  - unfold bytes_ok in HC. rewrite Forall_forall in HC. apply HC. apply nth_In. exact Hl.
  - rewrite nth_overflow by exact Hl. lia.
Qed.

Lemma fa_u8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  assert (bv_modulus 8 = 256) as -> by reflexivity. lia.
Qed.

(* The model's byte of the lifted content is the content's byte. *)
Lemma fa_fb : forall (C : list Z) i, bytes_ok C -> PSN.fb (nxF C) i = nth (Z.to_nat i) C 0.
Proof.
  intros C i HC. unfold PSN.fb, nxF, bytesZ.
  change (Z_to_bv 8 0) with ((fun z => Z_to_bv 8 z) 0). rewrite map_nth.
  apply fa_u8. apply fa_nth_byte. exact HC.
Qed.

Lemma fa_map_bytesZ : forall l, bytes_ok l -> map (fun b : byte => bv_unsigned b) (bytesZ l) = l.
Proof.
  intros l Hl. unfold bytesZ. rewrite map_map.
  induction l as [|x l IH]; [reflexivity|]. inversion Hl as [|y t Hx Ht]; subst.
  cbn [map]. rewrite fa_u8 by exact Hx. f_equal. apply IH. exact Ht.
Qed.

Lemma fa_bytes_ok_firstn : forall l n, bytes_ok l -> bytes_ok (firstn n l).
Proof.
  intros l. unfold bytes_ok. induction l as [|x l IH]; intros n Hl; destruct n as [|n]; cbn [firstn];
    [constructor | constructor | constructor | inversion Hl; subst; constructor; [assumption | apply IH; assumption]].
Qed.

Lemma fa_bytes_ok_skipn : forall l n, bytes_ok l -> bytes_ok (skipn n l).
Proof.
  intros l. unfold bytes_ok. induction l as [|x l IH]; intros n Hl; destruct n as [|n]; cbn [skipn];
    [exact Hl | constructor | exact Hl | inversion Hl; subst; apply IH; assumption].
Qed.

Section model.
Variables (sw : bool) (C : list Z) (cap p q : Z).
Hypothesis HC : bytes_ok C.
#[local] Notation F := (nxF C).
#[local] Notation flen := (Z.of_nat (length C)).
#[local] Notation incl := (PSN.incl sw (nxF C) q).

(* The model's raw record, as the list of Z the read-stream predicate states its content with. *)
Lemma fa_rec_raw : map (fun b : byte => bv_unsigned b) (PSN.rec_raw sw F q) =
  firstn (Z.to_nat incl) (skipn (Z.to_nat (q + 16)) C).
Proof.
  unfold PSN.rec_raw. set (n := Z.to_nat incl). set (m := Z.to_nat (q + 16)).
  unfold nxF at 1, bytesZ. rewrite skipn_map, firstn_map.
  apply fa_map_bytesZ. apply fa_bytes_ok_firstn. apply fa_bytes_ok_skipn. exact HC.
Qed.

(* The kind of a record whose header has been read (q + 16 <= flen), non-empty and fitting. *)
Lemma fa_kind : q + 16 <= flen -> 0 < incl <= cap ->
  PSN.kind sw F cap q = if q + 16 + incl <=? flen then PSN.KFit else PSN.KCutFit.
Proof.
  intros Hq Hi. unfold PSN.kind, PSN.flen. rewrite nxF_length.
  destruct (Z.eqb_spec (flen - q) 0) as [E|E]; [lia|].
  destruct (Z.ltb_spec (flen - q) 16) as [E2|E2]; [lia|].
  destruct (Z.eqb_spec incl 0) as [E3|E3]; [lia|].
  destruct (Z.leb_spec incl cap) as [E4|E4]; [reflexivity | lia].
Qed.

Hypothesis Hq : nx_q sw C cap p = q.
Hypothesis Hq0 : 0 <= q.
Hypothesis Hroom : q + 16 <= flen.
Hypothesis Hincl : 0 < incl <= cap.

Lemma fa_kind_q : nx_kind sw C cap p = if q + 16 + incl <=? flen then PSN.KFit else PSN.KCutFit.
Proof. unfold nx_kind. rewrite Hq. exact (fa_kind Hroom Hincl). Qed.

(* A cut record: the call ends with -1, the stream at its end, the struct's tag fields and the
   timestamp untouched. *)
Section cut.
Hypothesis Hcut : flen < q + 16 + incl.
Lemma fa_cut_kq : PSN.kind sw F cap q = PSN.KCutFit.
Proof. rewrite (fa_kind Hroom Hincl). destruct (Z.leb_spec (q + 16 + incl) flen); [lia | reflexivity]. Qed.
Lemma fa_cut_kind : nx_kind sw C cap p = PSN.KCutFit.
Proof. unfold nx_kind. rewrite Hq. exact fa_cut_kq. Qed.
Lemma fa_cut_fit : nx_fit sw C cap p = false.
Proof. unfold nx_fit. rewrite fa_cut_kind. reflexivity. Qed.
Lemma fa_cut_res : nx_res sw C cap p = -1.
Proof. unfold nx_res, PSN.res_of. rewrite Hq, fa_cut_kq. reflexivity. Qed.
Lemma fa_cut_pos : nx_pos sw C cap p = flen.
Proof. unfold nx_pos, PSN.pos_of. rewrite Hq, fa_cut_kq. unfold PSN.flen. rewrite nxF_length. reflexivity. Qed.
Lemma fa_cut_vtag : forall lvt, nx_vtag sw C cap p lvt = lvt.
Proof. intros lvt. unfold nx_vtag. rewrite fa_cut_fit. reflexivity. Qed.
Lemma fa_cut_vid : forall lvid, nx_vid sw C cap p lvid = lvid.
Proof. intros lvid. unfold nx_vid. rewrite fa_cut_fit. reflexivity. Qed.
Lemma fa_cut_tsv : forall tsv, nx_tsv sw C cap p tsv = tsv.
Proof. intros tsv. unfold nx_tsv. rewrite fa_cut_fit. reflexivity. Qed.
End cut.

(* A record that fits: the call hands it back. *)
Section fit.
Hypothesis Hfit : q + 16 + incl <= flen.
Lemma fa_fit_kq : PSN.kind sw F cap q = PSN.KFit.
Proof. rewrite (fa_kind Hroom Hincl). destruct (Z.leb_spec (q + 16 + incl) flen); [reflexivity | lia]. Qed.
Lemma fa_fit_kind : nx_kind sw C cap p = PSN.KFit.
Proof. unfold nx_kind. rewrite Hq. exact fa_fit_kq. Qed.
Lemma fa_fit_fit : nx_fit sw C cap p = true.
Proof. unfold nx_fit. rewrite fa_fit_kind. reflexivity. Qed.
Lemma fa_fit_res : nx_res sw C cap p = PSN.rec_len sw F q.
Proof. unfold nx_res, PSN.res_of. rewrite Hq, fa_fit_kq. reflexivity. Qed.
Lemma fa_fit_pos : nx_pos sw C cap p = q + 16 + incl.
Proof. unfold nx_pos, PSN.pos_of. rewrite Hq, fa_fit_kq. reflexivity. Qed.
Lemma fa_fit_vtag : forall lvt, nx_vtag sw C cap p lvt = if PSN.tagged sw F q then 1 else 0.
Proof. intros lvt. unfold nx_vtag. rewrite fa_fit_fit, Hq. reflexivity. Qed.
Lemma fa_fit_vid : forall lvid, nx_vid sw C cap p lvid = if PSN.tagged sw F q then PSN.rec_vid F q else 0.
Proof. intros lvid. unfold nx_vid. rewrite fa_fit_fit, Hq. reflexivity. Qed.
Lemma fa_fit_tsv : forall tsv, nx_tsv sw C cap p tsv = PSN.rec_ts sw F q.
Proof. intros tsv. unfold nx_tsv. rewrite fa_fit_fit, Hq. reflexivity. Qed.
Lemma fa_fit_reclen : nx_reclen sw C cap p = PSN.rec_len sw F q.
Proof. unfold nx_reclen. rewrite Hq. reflexivity. Qed.

(* The record's bytes as fread leaves them at the head of the buffer. *)
Definition fa_raw : list Z := firstn (Z.to_nat incl) (skipn (Z.to_nat (q + 16)) C).
Lemma fa_raw_length : length fa_raw = Z.to_nat incl.
Proof. unfold fa_raw. rewrite length_firstn, length_skipn. lia. Qed.

(* The bytes the model hands back, as the code leaves them: untagged, the raw record; tagged, the
   raw record with bytes 16 .. incl - 1 moved down by 4 (the memmove), the last 4 bytes kept. *)
Lemma fa_rec_untagged : PSN.tagged sw F q = false -> nx_rec sw C cap p = fa_raw.
Proof.
  intros Ht. unfold nx_rec, PSN.rec_bytes. rewrite Hq, Ht. unfold fa_raw. exact fa_rec_raw.
Qed.
Lemma fa_rec_tagged : PSN.tagged sw F q = true ->
  nx_rec sw C cap p =
  firstn 12 fa_raw ++ firstn (Z.to_nat (incl - 16)) (skipn 16 fa_raw) ++ skipn (Z.to_nat (incl - 4)) fa_raw.
Proof.
  intros Ht. unfold nx_rec, PSN.rec_bytes. rewrite Hq, Ht. cbv zeta.
  rewrite !map_app, <- !firstn_map, <- !skipn_map, fa_rec_raw. reflexivity.
Qed.
End fit.
End model.

(* ---------------------------------------------------------------------------------------------- *)
(* The call of __asan_memmove inside the caller's journal                                           *)
(* ---------------------------------------------------------------------------------------------- *)

(* YC85.aj_intrin_atS for lib/A/Rt/MemmoveDef.v's amemmove_realizes: the same statement and proof,
   but the source may overlap the destination (no `d + n <= x \/ x + n <= d`), as at 0x81cdc, where
   the code moves buf + 16 .. buf + incl down to buf + 12. *)
Section mm. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Lemma aj_memmove_atS : forall pc, amemmove_realizes segs B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) memT) d n) ->
0 <= x -> x + n <= 2 ^ 63 -> src_ok segs W regsT memT x n -> amem_range x n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (d + i) = aview segs (w_H W) memT (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
   aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
same_but_materialized mdc md2).
Proof.
intros pc AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hx0 Hxn Hsrc Hamx Hra_x Hhullx.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
assert (HDEST : dest_ok segs B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
  destruct (awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Hno]. rewrite Hsp'.
  split; [apply apresent_writable; exact Hp | auto]. }
eapply SRr_mono.
{ exact (AI lyc Sc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull Hx0 Hxn Hsrc Hamx Hra_x Hhullx). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => (d <= a < d + n) \/ (sp0 + o - ESTACK <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; lia].
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Heff|]. split; [exact Hfr|]. split; [exact Hpres2 | exact Hsame].
Qed.
End mm.
