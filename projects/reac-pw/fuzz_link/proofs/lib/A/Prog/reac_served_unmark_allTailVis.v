(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 297 of its 339 lines of code are new or changed and 1038 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readDefs.v, with its module paths and module names changed; 162 of its 201 lines of code are new or changed and 300 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_writeCall.v, with its module names changed; 116 of its 157 lines of code are new or changed and 160 lines of the source are left out. *)
(* reac_served_unmark_all (fuzz_link.asan 0x89ed4) on image A: the rest of each passed string's NUL granule is
   visible at a callee's call (the strcmp tail clause of the two alias contracts, model_decide_c.v astr_rt_ok's
   tail conjunct: `forall a, p + |s| < a < p + |s| - (p + |s|) mod 8 + 8 -> ard segs m a <> None`).

   At the contract's call memory the Pre gives it:
   - an interface-table string (amk_table_ok's astr_rt_ok);
   - a name m->name[c] in the marks block: its NUL lies in its 16-byte slot (marks_wf), so the bytes after it up to
     the end of its 8-byte granule are either bytes of the block, which amarks_at reads as bytes, or among the 8
     bytes after the block, which amarks_blk_ok makes visible.
   At any later state that keeps the call's memory by `akept` (from the contract's call state, with the walk's
   window [sp - K, sp)), the NUL byte is a read-set byte (`akb`): a table string's by the read set
   (reac_served_mark_c.v amk_tab_rd), a name's as a byte of the write set (LinkWalkCall.v ajw_akb); then
   lib/A/Prog/LinkWalkMkVis.v `tail_vis_transport` moves the visibility to that state.

   Users: the alias_read call (reac_served_unmark_allReadA.v) and the alias_write call
   (reac_served_unmark_allWrite.v).

   Proves no function (kind: segment lemma of reac_served_unmark_all's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AB13.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro link_aaddr link_amem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_unmark_all_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkCall LinkWalkMkVis.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_served_unmark_allDefs reac_served_unmark_allWriteKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
(* AR's laws (the frame); the segments the listing is certified against (LinkImgInst.v pi_link_segs): the
   image's file backs every image byte (AB13.v tfib_rom_all) *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HSEGS : SEGS = AB1v.tfibsegs.

Lemma utv_segs_rom : forall a, 0x10000 <= a < pcap_img_end -> seg_rom SEGS (Z_to_bv 64 a) <> None.
Proof. intros a Ha. rewrite HSEGS. exact (AB13.tfib_rom_all a Ha). Qed.

Lemma utv_vis_of_mbyte : forall (m : word -> option byte) a x, mbyte SEGS m a = Some x -> ard SEGS m a <> None.
Proof. intros m a x H. unfold ard. rewrite H. discriminate. Qed.

Section c.
Variable cx : umcx.
Hypothesis HPRE : um_pre SK B cx.
(* a later state that keeps the call's memory, at a layout with the call's blocks, frames and frame addresses *)
Variables (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (mem2 : word -> option byte) (md2 : Model)
  (E : Z -> Prop).
Hypothesis HAR2 : AR SEGS B ly2 S2 W2 mem2 md2.
Hypothesis HBL : forall q m, In (q, m) (ablocks B (um_lyc cx) (um_Sc cx)) -> In (q, m) (ablocks B ly2 S2).
Hypothesis HFR : forall c q, In (c, q) (frames (um_Sc cx)) -> In (c, q) (frames S2).
Hypothesis HFA : forall c q, frame_addr ly2 c q = frame_addr (um_lyc cx) c q.
Hypothesis HK : akept SEGS B (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) W2 mem2
  (um_sp cx - REAC_SERVED_UNMARK_ALL_AK) (um_sp cx) E.

(* the rest of the granule of a read-set byte e, visible at the call, is visible at the later state *)
Lemma utv_move : forall e b,
  akb SEGS B (um_lyc cx) (um_Sc cx) (um_sp cx - REAC_SERVED_UNMARK_ALL_AK) (um_sp cx) e ->
  e < b < e - e mod 8 + 8 -> ard SEGS (um_m0 cx) b <> None -> ard SEGS (rdW W2 mem2) b <> None.
Proof.
  intros e b He Hb Hv.
  pose proof HPRE as ((HJ & _ & _ & _ & _ & _ & _ & Hal16 & _) & _).
  assert (HR := HJ). apply ajournal_gx_row in HR. destruct HR as (R1 & R2 & _ & _).
  assert (HKv : REAC_SERVED_UNMARK_ALL_AK = 8768) by reflexivity.
  change (ard SEGS (um_m0 cx) b <> None) with (aview SEGS (w_H (um_W cx)) (um_memc cx) b <> None) in Hv.
  change (ard SEGS (mrestrict (w_H W2) mem2) b <> None) with (aview SEGS (w_H W2) mem2 b <> None).
  eapply tail_vis_transport with (slo := um_sp cx - REAC_SERVED_UNMARK_ALL_AK) (shi := um_sp cx) (E := E) (e := e).
  - exact LAWS.
  - exact pa_img_range.
  - exact utv_segs_rom.
  - exact HAR2.
  - exact R1.
  - exact R2.
  - unfold um_sp in *. rewrite HKv. lia.
  - unfold um_sp in *. lia.
  - exact HBL.
  - exact HFR.
  - exact HFA.
  - exact HK.
  - exact He.
  - exact Hb.
  - exact Hv.
Qed.

(* an interface-table string, by its pointer at the call *)
Lemma utv_tab : forall i n2 ix p, nth_error (um_tab cx) i = Some (n2, ix) ->
  au64_at SEGS (um_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
  forall b, p + Z.of_nat (length n2) < b < p + Z.of_nat (length n2) - (p + Z.of_nat (length n2)) mod 8 + 8 ->
    ard SEGS (rdW W2 mem2) b <> None.
Proof.
  intros i n2 ix p Hi Hp Hpr b Hb.
  pose proof HPRE as (_ & HRD & (NK & _ & _ & _ & _ & IT & _ & _) & _ & HTB & _).
  destruct (HTB i n2 ix p Hi Hp Hpr) as ((_ & _ & _ & _ & _ & HT & _) & _).
  pose proof IT as (_ & _ & IT0). destruct (IT0 i n2 ix Hi) as (_ & p0 & P0 & _ & C0 & _).
  pose proof (uw_acstr_range SEGS _ p0 n2 C0) as R0.
  pose proof (uw_au64_unique SEGS _ _ _ _ Hp P0) as Ep. rewrite !Z.mod_small in Ep by lia. subst p0.
  apply (utv_move (p + Z.of_nat (length n2)) b).
  - apply HRD. right. exists (um_kbs cx), (um_tab cx), i, n2, ix, p.
    split; [exact NK|]. split; [exact IT|]. split; [exact Hi|]. split; [exact Hp|].
    split; [exact C0 | lia].
  - exact Hb.
  - exact (HT b Hb).
Qed.

(* the name m->name[c] of the marks block *)
Lemma utv_name : forall c, um_mk cx <> 0 -> (c < Z.to_nat (um_n cx))%nat ->
  forall b,
    um_mk cx + MK_NAME + MARK_LEN * Z.of_nat c + Z.of_nat (length (nth c (um_names cx) [])) < b <
    um_mk cx + MK_NAME + MARK_LEN * Z.of_nat c + Z.of_nat (length (nth c (um_names cx) []))
      - (um_mk cx + MK_NAME + MARK_LEN * Z.of_nat c + Z.of_nat (length (nth c (um_names cx) []))) mod 8 + 8 ->
    ard SEGS (rdW W2 mem2) b <> None.
Proof.
  intros c Hm Hc b Hb.
  pose proof HPRE as ((HJ & HGX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAJW & _) & _ & _ & _ & _ & HBK & _ & _ & _ & _
    & HGB).
  destruct (HBK Hm) as ((Hp0 & Hamr & _ & _ & HT8 & Hapf) & _ & Herr & _ & _).
  destruct (HGB Hm) as (((HB0 & _) & HL) & (Hn & HTm)).
  fold (um_mk cx) in *. fold (um_m0 cx) in *.
  unfold um_n in Hc.
  assert (Hc32 : Z.of_nat c < 32) by (unfold MARKS_MAX in Hn; lia).
  unfold um_names in Hb. rewrite (uw_mk_names_nth (um_gbs cx) c Hc) in Hb.
  destruct (uw_slot_cstr SEGS (um_m0 cx) (um_mk cx) (um_gbs cx) (Z.of_nat c) HB0 HL
    ltac:(unfold MARKS_MAX; lia) ltac:(apply HTm; lia)) as (_ & Hlen).
  set (s := cstr (slice (um_gbs cx) (MK_NAME + MARK_LEN * Z.of_nat c) MARK_LEN)) in *.
  set (e := um_mk cx + MK_NAME + MARK_LEN * Z.of_nat c + Z.of_nat (length s)) in *.
  pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Hm8.
  assert (He1 : um_mk cx <= e < um_mk cx + MK_SIZE)
    by (unfold e, MK_NAME, MARK_LEN, MK_SIZE in *; lia).
  assert (Hb1 : b < um_mk cx + MK_SIZE + 8) by (unfold e, MK_NAME, MARK_LEN, MK_SIZE in *; lia).
  assert (HKv : REAC_SERVED_UNMARK_ALL_AK = 8768) by reflexivity.
  (* the NUL byte: a byte of the write set, hence of the read set at the call *)
  assert (Hw : inFP (um_wr cx) e).
  { exists (aivl (um_mk cx) MK_SIZE). split; [right; left; reflexivity|].
    unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) Hm). cbn [fst snd]. lia. }
  assert (Happ : e < kLowMemEnd \/ kHighMemBeg <= e).
  { clear - He1 Hamr. unfold amem_range, MK_SIZE in *. lia. }
  assert (Hakb : akb SEGS B (um_lyc cx) (um_Sc cx) (um_sp cx - REAC_SERVED_UNMARK_ALL_AK) (um_sp cx) e).
  { apply (ajw_akb SK SEGS B LAWS (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx)
      (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) (um_own cx) (um_lyc cx) (um_Sc cx) (um_W cx)
      (um_memc cx) (um_mdc cx) (um_k cx) (um_lyc cx) (um_Sc cx) _ _ e HGX HJ (HAJW e Hw)).
    - unfold apart_frame in Hapf. unfold um_sp. rewrite HKv in *. lia.
    - exact Happ.
    - unfold apart in Herr. lia.
    - reflexivity.
    - reflexivity.
    - intros q m Hq; exact Hq.
    - intros q m Hq; exact Hq.
    - intros q m; reflexivity. }
  apply (utv_move e b Hakb Hb).
  (* visible at the call: a byte of the block, or one of the eight bytes after it *)
  destruct (Z_lt_le_dec b (um_mk cx + MK_SIZE)) as [Hin | Hout].
  - destruct HB0 as (_ & _ & HB).
    pose proof (HB (Z.to_nat (b - um_mk cx)) ltac:(lia)) as Hy.
    replace (um_mk cx + Z.of_nat (Z.to_nat (b - um_mk cx))) with b in Hy by lia.
    destruct (nth_error (um_gbs cx) (Z.to_nat (b - um_mk cx))) as [x|] eqn:Hx.
    + exact (utv_vis_of_mbyte _ _ x Hy).
    + exfalso. apply nth_error_None in Hx. lia.
  - apply HT8. lia.
Qed.

End c.
End b.
End a.

(* No global sink_head instance is in scope here. *)
Fail Definition sink_head_probe_um_tv : YI16.sink_head := _.
