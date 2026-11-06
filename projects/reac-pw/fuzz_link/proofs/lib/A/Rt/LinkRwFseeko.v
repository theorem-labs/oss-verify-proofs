(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1y.v (origin/ossv/recipes c8557374ad2e), with its module paths changed, names TfibSyms -> PcapSyms and its addresses moved to libreac/fuzz_pcap's ASan build; the image end is pcap_img_end (Reusable/PcapImgEnd.v). ADAPTED (porter ruling 4): the relocated driver window (0x5d3f10, 0x5d4838) (donor AD1y.v:16 (0x5d8650, 0x5d8f38)) holds fuzz_pcap's two harness globals g_file_len / g_file and their ASan redzones, [0x5d3f40, 0x5d3f80); DRV_IVS splits that window around it into (0x5d3f10, 0x5d3f40) and (0x5d3f80, 0x5d4838), both MEASURED (unstripped twin fuzz_pcap.asan (sha256 36da3052c383): g_file_len 0x5d3f40 size 0x20, g_file 0x5d3f60 size 0x20; AF0m Tfib_owned_static (0x5d3f48, 0x18), (0x5d3f68, 0x18) are the redzones). DRV_IVS_not_G / DRVW_not_G check that the windows and the hull [DRV_G_LO, DRV_G_HI) are disjoint (lib/A/PcapDrvG.v ties the hull to PcapEntry.v's G_HARNESS); DRV_IVS_split_exact checks the two windows are the old window less the hull. DRVW_cases has five cases. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/AD1y.v, with its module paths and module names changed; 1350 of its 1413 lines of code are new or changed and 326 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): the walk of musl __fseeko_unlocked 0x96e78 at
   off = 0, whence = SEEK_SET, on link's memory FILE: LinkRwDefs.v afseeko0_mf_realizes at LA_FSEEKO.

   Listing: (internal path) (internal record, sha256 db254527920b) (54
   instructions, frame 32). The code table is those 54 words; the walk runs the symbolic engine over it in phases and
   stops at each `jalr` into a callee (the table has no word there: SR_fetch) and at the `ret`.
   - entry +0x00..+0x10: push 32, save ra, s0, s1, s2 (the stack window [sp - 32, sp));
     +0x18 bltu a2,3 is taken (a2 = 0, pinned), +0x34 bne a2,1 is taken: the EINVAL arm (+0x1c, ___errno_location)
     and the SEEK_CUR arm (+0x38..+0x48) are not reached;
     +0x4c / +0x50 load wpos (f + 40) and wbase (f + 56) as two atoms; +0x54 beq stops the run.
   - wpos = wbase (k = 0: amf_win gives both 0, or both f + 280): phase A0, +0x84 ld a3,0x50(s0) (f->seek, the
     word amemfile_at fixes to amf_seek link_amf = LA_MSEEK), +0x88..+0x90 wend = wpos = wbase = 0, +0x98 jalr: the
     run stops at mseek's entry; HMS (amseek_set_realizes, off 0) runs it at sp - 32 (window 48).
   - wpos <> wbase (0 < k: wpos = f + 280 + k, wbase = f + 280): phase A1, +0x58 ld a3,0x48(s0) (f->write =
     LA_MWRITE), +0x5c..+0x6c a0 = f, a1 = a2 = 0, s1 = s2 = 0, +0x70 jalr: the run stops at mwrite's entry; HFL
     (amwrite_mf_flush_realizes) runs it at sp - 32 (window AMW_STK = AFS_STK - 32).
     Back at +0x74 (fresh symbolic state over the saved frame): +0x7c ld wpos; +0x80 beqz:
     * n1 < k (the flush hit g_said's end and zeroed the window): wpos = 0, taken, +0xbc a0 = -1, restore, ret
       (phase B0, no store);
     * n1 = k: wpos = wbase = f + 280, not taken: phase B1 continues as A0 from +0x84 to mseek's entry.
   - back at +0x9c (fresh state; a0 = 0 from mseek): +0x9c bltz not taken, +0xa4..+0xac flags &= ~F_EOF (flags
     is 4 or 36, amemfile_flags, so the stored word is the same), +0xb0 / +0xb4 rpos = rend = 0, ret (phase C).
   Each fresh state takes the saved ra / s0 / s1 / s2 as extra atoms 32..35 and the frame slots as their chunks;
   the memory relation from phase to phase is FI (the post's frame clauses) plus the FILE words each phase
   leaves. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_pw.fuzz_link.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y AE7f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFileSink AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkRwDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ==========================================================================
   1. The code table and the symbolic states
   ========================================================================== *)

Definition fs_tbl : ctable := Eval vm_compute in build_table tfibsegs LA_FSEEKO 54 TEmpty.
Lemma fs_tbl_eq : fs_tbl = build_table tfibsegs LA_FSEEKO 54 TEmpty.
Proof. vm_cast_no_check (eq_refl fs_tbl). Qed.
Lemma fs_tbl_ok : table_ok tfibsegs fs_tbl.
Proof. rewrite fs_tbl_eq. apply build_table_ok0. unfold LA_FSEEKO. lia. Qed.

Definition ch8 (o : Z) (v : sv) : YP09.chunk := YP09.mkChunk o (CVal 8 v).
(* the frame push: 32 bytes below sp *)
Definition R_stkA : YP09.region := YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [].
(* k = 0: wpos (atom 32), wbase (atom 33), the static 0 at +48, f->seek; [32, 64) written *)
Definition R_fK0 : YP09.region :=
  YP09.mkRegion (Some 10%nat) 32 88 32 64 [ch8 40 (SOff 32 0); ch8 48 (SLit 0); ch8 56 (SOff 33 0); ch8 80 (SLit LA_MSEEK)].
(* 0 < k: wpos, wbase, f->write; nothing written *)
Definition R_fK1 : YP09.region :=
  YP09.mkRegion (Some 10%nat) 40 80 0 0 [ch8 40 (SOff 32 0); ch8 56 (SOff 33 0); ch8 72 (SLit LA_MWRITE)].
Definition sr_A : list sv := sr_set (sr_set sr_atoms 11%bv (SLit 0)) 12%bv (SLit 0).
Definition ss_A (rf : YP09.region) : sstate := mkSS LA_FSEEKO sr_A [R_stkA; rf] None (mkFacts [] [] []).
Definition c_wp : acond := mkAC BC_EQ (SOff 32 0) (SOff 33 0).
Definition c_wpn : acond := mkAC (neg_bc BC_EQ) (SOff 32 0) (SOff 33 0).

Definition st_A0a : sstate := Eval vm_compute in fst (sym_runN tfibsegs fs_tbl FUEL (ss_A R_fK0)).
Definition st_A0b : sstate := Eval vm_compute in fst (sym_runN tfibsegs fs_tbl FUEL (YP06.add_cond st_A0a c_wp)).
Definition st_A1a : sstate := Eval vm_compute in fst (sym_runN tfibsegs fs_tbl FUEL (ss_A R_fK1)).
Definition st_A1b : sstate := Eval vm_compute in fst (sym_runN tfibsegs fs_tbl FUEL (YP06.add_cond st_A1a c_wpn)).
Lemma run_A0a : sym_runN tfibsegs fs_tbl FUEL (ss_A R_fK0) = (st_A0a, RS_stopped (SR_branch BC_EQ (SOff 32 0) (SOff 33 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_A0b : sym_runN tfibsegs fs_tbl FUEL (YP06.add_cond st_A0a c_wp) = (st_A0b, RS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
Lemma run_A1a : sym_runN tfibsegs fs_tbl FUEL (ss_A R_fK1) = (st_A1a, RS_stopped (SR_branch BC_EQ (SOff 32 0) (SOff 33 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_A1b : sym_runN tfibsegs fs_tbl FUEL (YP06.add_cond st_A1a c_wpn) = (st_A1b, RS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.

(* after a call: the saved frame at the new sp (atoms 35, 34, 33, 32 = the caller's s2, s1, s0, ra) *)
Definition R_frm : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 32 0 0 [ch8 0 (SOff 35 0); ch8 8 (SOff 34 0); ch8 16 (SOff 33 0); ch8 24 (SOff 32 0)].
Definition R_fB0 : YP09.region := YP09.mkRegion (Some 8%nat) 40 48 0 0 [ch8 40 (SLit 0)].
Definition R_fB1 : YP09.region :=
  YP09.mkRegion (Some 8%nat) 32 88 32 64 [ch8 40 (SOff 8 280); ch8 48 (SLit 0); ch8 80 (SLit LA_MSEEK)].
Definition ss_B (rf : YP09.region) : sstate := mkSS 0x96eec sr_atoms [R_frm; rf] None (mkFacts [] [] []).
Definition c_b1 : acond := mkAC (neg_bc BC_EQ) (SOff 8 280) (SLit 0).
Definition st_B0 : sstate := Eval vm_compute in fst (sym_runN tfibsegs fs_tbl FUEL (ss_B R_fB0)).
Definition st_B1a : sstate := Eval vm_compute in fst (sym_runN tfibsegs fs_tbl FUEL (ss_B R_fB1)).
Definition st_B1b : sstate := Eval vm_compute in fst (sym_runN tfibsegs fs_tbl FUEL (YP06.add_cond st_B1a c_b1)).
Lemma run_B0 : sym_runN tfibsegs fs_tbl FUEL (ss_B R_fB0) = (st_B0, RS_stopped (SR_jalr (SOff 32 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_B1a : sym_runN tfibsegs fs_tbl FUEL (ss_B R_fB1) = (st_B1a, RS_stopped (SR_branch BC_EQ (SOff 8 280) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_B1b : sym_runN tfibsegs fs_tbl FUEL (YP06.add_cond st_B1a c_b1) = (st_B1b, RS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.

Definition R_fC (fl : Z) : YP09.region := YP09.mkRegion (Some 8%nat) 0 24 0 24 [YP09.mkChunk 0 (CVal 4 (SLit fl))].
Definition ss_C (fl : Z) : sstate := mkSS 0x96f14 (sr_set sr_atoms 10%bv (SLit 0)) [R_frm; R_fC fl] None (mkFacts [] [] []).
Definition st_C4 : sstate := Eval vm_compute in fst (sym_runN tfibsegs fs_tbl FUEL (ss_C 4)).
Definition st_C36 : sstate := Eval vm_compute in fst (sym_runN tfibsegs fs_tbl FUEL (ss_C 36)).
Lemma run_C4 : sym_runN tfibsegs fs_tbl FUEL (ss_C 4) = (st_C4, RS_stopped (SR_jalr (SOff 32 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_C36 : sym_runN tfibsegs fs_tbl FUEL (ss_C 36) = (st_C36, RS_stopped (SR_jalr (SOff 32 0))).
Proof. vm_compute. reflexivity. Qed.

(* ==========================================================================
   2. Generic helpers
   ========================================================================== *)

Ltac zofn H := cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H.
Ltac kside := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold AMF_ZEROED, AMF_COOKIE, AMF_BUF, AMF_BUFSIZ, AMF_BLOCK in *; lia.

(* donor: lib/A/AD1y.v in_img_hull, copied verbatim *)
Lemma fs_in_img : forall a, 0x10000 <= a < pcap_img_end -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img. unfold pcap_img_end, YImgTop.IMG_TOP in Ha.
assert (E : tfibsegs = [Asan_segment_000; Asan_segment_001;
Asan_segment_002; Asan_segment_003]) by reflexivity.
rewrite E.
destruct (Z.lt_ge_cases a 0x31000); [exists Asan_segment_000; split; [cbn; tauto | cbn; lia]|].
destruct (Z.lt_ge_cases a 0xa1000); [exists Asan_segment_001; split; [cbn; tauto | cbn; lia]|].
destruct (Z.lt_ge_cases a 0xa3000); [exists Asan_segment_002; split; [cbn; tauto | cbn; lia]|].
exists Asan_segment_003. split; [cbn; tauto | cbn; lia].
Qed.

Lemma stk_not_img : forall a, kLowMemEnd <= a -> ~ in_img tfibsegs a.
Proof. intros a Ha Hi. pose proof (tfib_segs_low a Hi). lia. Qed.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma fs_phase : forall (W : world tfibsegs) E ss ss' why ms md,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  sym_runN tfibsegs fs_tbl FUEL ss = (ss', RS_stopped why) ->
  SRr tfibsegs W (mkCfg ms md)
    (fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
       st_ok tfibsegs E ss' (restrict (w_H W) ms1) /\
       frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
       frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
  intros W E ss ss' why ms md HS Hrun.
  eapply (SRr_run_gen tfibsegs fs_tbl fs_tbl_ok AF0x.Hwx_tfa W FUEL E ss ss' (RS_stopped why) ms md _ HS Hrun).
  intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
  split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.

Fixpoint find_cv (cs : list YP09.chunk) (o : Z) : option cval :=
  match cs with
  | [] => None
  | c :: t => if Z.eqb (YP09.c_off c) o then Some (YP09.c_val c) else find_cv t o
  end.

Lemma find_cv_In : forall cs o v, find_cv cs o = Some v -> In (YP09.mkChunk o v) cs.
Proof.
  induction cs as [|c t IH]; intros o v H; cbn in H; [discriminate|].
  destruct (Z.eqb (YP09.c_off c) o) eqn:E.
  - injection H as <-. apply Z.eqb_eq in E. left. destruct c as [co cv]. cbn in *. subst. reflexivity.
  - right. apply IH. exact H.
Qed.

Definition chunk_at (rs : smem) (i : nat) (o : Z) : option (option nat * cval) :=
  match nth_error rs i with
  | Some r => match find_cv (YP09.r_chunks r) o with Some v => Some (YP09.r_base r, v) | None => None end
  | None => None
  end.

Definition win_at (rs : smem) (i : nat) : option (option nat * Z * Z) :=
  match nth_error rs i with Some r => Some (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r) | None => None end.

Lemma st_chunk_val : forall E ss ms i o b n e v,
  st_ok tfibsegs E ss ms -> chunk_at (ss_mem ss) i o = Some (b, CVal n e) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem tfibsegs (ms_mem ms) (base_val E b + o) (N.to_nat n) v.
Proof.
  intros E ss ms i o b n e v HS Hc He Hv Hn. unfold chunk_at in Hc.
  destruct (nth_error (ss_mem ss) i) as [r|] eqn:Hi; [|discriminate].
  destruct (find_cv (YP09.r_chunks r) o) as [cv|] eqn:Hf; [|discriminate].
  injection Hc as <- ->.
  pose proof (st_ok_mem_ok tfibsegs E ss ms HS) as (_ & Hrs & _).
  pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as Hr. unfold region_ok in Hr. cbv zeta in Hr.
  destruct Hr as (_ & _ & _ & Hcs).
  pose proof (proj1 (Forall_forall _ _) Hcs _ (find_cv_In _ _ _ Hf)) as Hck.
  exact (val_of_chunk_ok tfibsegs E (ms_mem ms) _ o n e v Hck He Hv Hn).
Qed.

Lemma st_win_writable : forall E ss ms i b wlo whi o,
  st_ok tfibsegs E ss ms -> win_at (ss_mem ss) i = Some (b, wlo, whi) -> wlo <= o < whi ->
  writable_at tfibsegs (ms_mem ms) (base_val E b + o).
Proof.
  intros E ss ms i b wlo whi o HS Hw Ho. unfold win_at in Hw.
  destruct (nth_error (ss_mem ss) i) as [r|] eqn:Hi; [|discriminate].
  injection Hw as <- <- <-.
  pose proof (st_ok_mem_ok tfibsegs E ss ms HS) as (_ & Hrs & _).
  pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as Hr. unfold region_ok in Hr. cbv zeta in Hr.
  destruct Hr as (_ & _ & Hwr & _). exact (Hwr o Ho).
Qed.

Lemma win_present : forall (W : world tfibsegs) E ss ms i b wlo whi a,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> win_at (ss_mem ss) i = Some (b, wlo, whi) ->
  base_val E b + wlo <= a < base_val E b + whi -> 0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a ->
  apresent (w_H W) (ms_mem ms) a.
Proof.
  intros W E ss ms i b wlo whi a HS Hw Ha Hr Hn.
  apply (apresent_of_writable (w_H W) (ms_mem ms) a Hr Hn).
  replace a with (base_val E b + (a - base_val E b)) by lia.
  exact (st_win_writable E ss (restrict (w_H W) ms) i b wlo whi (a - base_val E b) HS Hw ltac:(lia)).
Qed.

Lemma frame2 : forall E rs (m m' : word -> option byte) b1 l1 h1 b2 l2 h2,
  windows rs = [(b1, l1, h1); (b2, l2, h2)] ->
  frame_of E rs m m' ->
  forall x : word, ~ (base_val E b1 + l1 <= bv_unsigned x < base_val E b1 + h1) ->
                   ~ (base_val E b2 + l2 <= bv_unsigned x < base_val E b2 + h2) -> m' x = m x.
Proof.
  intros E rs m m' b1 l1 h1 b2 l2 h2 Hw HF x N1 N2. apply HF. intros Hin.
  destruct (in_wrange_windows E rs _ Hin) as (b & lo & hi & Ht & Hr). rewrite Hw in Ht.
  destruct Ht as [Hq|[Hq|[]]]; injection Hq as <- <- <-; [exact (N1 Hr) | exact (N2 Hr)].
Qed.

Lemma vm_kept_range : forall (H : word -> bool) (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview tfibsegs H m' x = aview tfibsegs H m x) ->
  val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof.
  intros H m m' a n v Hx Hv k Hk. rewrite (mbyte_of_aview H H m m' (a + Z.of_nat k)) by (apply Hx; lia).
  exact (Hv k Hk).
Qed.

Lemma azbytes_kept : forall (H : word -> bool) (m m' : word -> option byte) a l,
  azbytes tfibsegs (mrestrict H m) a l ->
  (forall i, (i < length l)%nat -> aview tfibsegs H m' (a + Z.of_nat i) = aview tfibsegs H m (a + Z.of_nat i)) ->
  azbytes tfibsegs (mrestrict H m') a l.
Proof.
  intros H m m' a l Hz Hk i Hi. pose proof (Hz i Hi) as X. pose proof (Hk i Hi) as Y.
  unfold amf_rd in *. unfold aview in Y. cbv beta in *. rewrite Y. exact X.
Qed.

Lemma rdword_kept : forall (rd1 rd2 : Z -> option Z) a,
  (forall i, 0 <= i < 8 -> rd2 (a + i) = rd1 (a + i)) -> rdword rd2 a = rdword rd1 a.
Proof.
  intros rd1 rd2 a H. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  unfold rdword. rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Lemma val_mem_det : forall (m : word -> option byte) a n x y,
  val_mem tfibsegs m a n x -> val_mem tfibsegs m a n y ->
  0 <= x < 2 ^ (8 * Z.of_nat n) -> 0 <= y < 2 ^ (8 * Z.of_nat n) -> x = y.
Proof.
  intros m a n x y Hx Hy Rx Ry. apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_le_dec i (8 * Z.of_nat n)) as [Hlt|Hge].
  - set (k := Z.to_nat (i / 8)).
    assert (Hq : 0 <= i / 8) by (apply Z.div_pos; lia).
    assert (Ek : Z.of_nat k = i / 8) by (unfold k; rewrite Z2Nat.id; [reflexivity | exact Hq]).
    assert (Hk : (k < n)%nat).
    { apply Nat2Z.inj_lt. rewrite Ek. apply Z.div_lt_upper_bound; lia. }
    assert (Bq : Z.shiftr x (8 * Z.of_nat k) mod 2 ^ 8 = Z.shiftr y (8 * Z.of_nat k) mod 2 ^ 8).
    { pose proof (Hx k Hk) as X0. rewrite (Hy k Hk) in X0.
      assert (X : Z_to_bv 8 (YO0f.le_byte y n k) = Z_to_bv 8 (YO0f.le_byte x n k)) by congruence.
      rewrite (le_byte_small x n k Rx Hk), (le_byte_small y n k Ry Hk) in X.
      apply (f_equal bv_unsigned) in X. rewrite !Z_to_bv_unsigned in X. unfold bv_wrap, bv_modulus in X.
      change (2 ^ Z.of_N 8) with (2 ^ 8) in X. symmetry. exact X. }
    pose proof (Z.div_mod i 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Hm.
    assert (T : forall z, Z.testbit (Z.shiftr z (8 * Z.of_nat k) mod 2 ^ 8) (i - 8 * Z.of_nat k) = Z.testbit z i).
    { intros z. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftr_spec by lia. f_equal. lia. }
    rewrite <- (T x), <- (T y), Bq. reflexivity.
  - rewrite <- (Z.mod_small x (2 ^ (8 * Z.of_nat n))) by lia.
    rewrite <- (Z.mod_small y (2 ^ (8 * Z.of_nat n))) by lia.
    rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma val_mem_det8 : forall (m : word -> option byte) a x y,
  val_mem tfibsegs m a 8 x -> val_mem tfibsegs m a 8 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x = y.
Proof. intros m a x y Hx Hy Rx Ry. exact (val_mem_det m a 8 x y Hx Hy Rx Ry). Qed.

Lemma val_mem_det4 : forall (m : word -> option byte) a x y,
  val_mem tfibsegs m a 4 x -> val_mem tfibsegs m a 4 y -> 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 -> x = y.
Proof. intros m a x y Hx Hy Rx Ry. exact (val_mem_det m a 4 x y Hx Hy Rx Ry). Qed.

(* the callee-saved registers the walk never writes *)
Definition KEEP : list (bv 5) := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition keep_ok (sr : list sv) : bool :=
  forallb (fun r : bv 5 => sv_eqb (sr_get sr r) (SOff (Z.to_nat (bv_unsigned r)) 0)) KEEP.
Definition keep_regs (r0 r1 : bvmap 5 word) : Prop := forall r, In r KEEP -> getr r1 r = getr r0 r.

Lemma keep_of_st_ok : forall H E ss ms regs0 extra,
  st_ok tfibsegs E ss (restrict H ms) -> E = Ereg regs0 extra -> keep_ok (ss_regs ss) = true ->
  keep_regs regs0 (ms_regs ms).
Proof.
  intros H E ss ms regs0 extra HS -> Hk r Hr.
  pose proof (proj1 (forallb_forall _ _) Hk r Hr) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
  rewrite (st_ok_restrict_reg tfibsegs H _ ss ms r HS), Hq. cbn [sv_denot].
  rewrite Z.add_0_r, ew_Ereg_reg, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma KEEP_cs : forall r, In r KEEP -> acallee_saved (bv_unsigned r).
Proof.
  intros r Hr. unfold acallee_saved.
  assert (Bk : forallb (fun r : bv 5 => ((18 <=? bv_unsigned r) && (bv_unsigned r <=? 27)) || (bv_unsigned r =? 3)
                 || (bv_unsigned r =? 4)) KEEP = true) by reflexivity.
  pose proof (proj1 (forallb_forall _ _) Bk r Hr) as Hb. cbv beta in Hb.
  apply orb_prop in Hb as [Hb|Hb]; [apply orb_prop in Hb as [Hb|Hb]|].
  - apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
  - apply Z.eqb_eq in Hb. lia.
  - apply Z.eqb_eq in Hb. lia.
Qed.

Lemma keep_of_aregs : forall r0 r1, aregs_preserved r0 r1 -> keep_regs r0 r1.
Proof.
  intros r0 r1 H r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply H. exact (KEEP_cs r Hr).
Qed.

Lemma cs_of : forall r : bv 5,
  ((bv_unsigned r =? 2) || (bv_unsigned r =? 8) || (bv_unsigned r =? 9) ||
   ((18 <=? bv_unsigned r) && (bv_unsigned r <=? 27)))%bool = true ->
  acallee_saved (bv_unsigned r).
Proof.
  intros r H. unfold acallee_saved.
  apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|]|].
  - apply Z.eqb_eq in H. lia.
  - apply Z.eqb_eq in H. lia.
  - apply Z.eqb_eq in H. lia.
  - apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma keep_trans : forall r0 r1 r2, keep_regs r0 r1 -> keep_regs r1 r2 -> keep_regs r0 r2.
Proof. intros r0 r1 r2 H1 H2 r Hr. rewrite (H2 r Hr). apply H1, Hr. Qed.

Lemma aregs_reg : forall r0 r1 (r : bv 5), aregs_preserved r0 r1 -> acallee_saved (bv_unsigned r) ->
  getr r1 r = getr r0 r.
Proof. intros r0 r1 r H Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply H. exact Hr. Qed.

Lemma aregs_of_list : forall r0 r1 : bvmap 5 word,
  (forall r, In r CALLEE_SAVED -> getr r1 r = getr r0 r) -> aregs_preserved r0 r1.
Proof.
  intros r0 r1 H r Hr. apply H. unfold acallee_saved in Hr. cbv [CALLEE_SAVED In].
  assert (X : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
              r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct X as [->|X]; [repeat (first [left; apply bv_eq; reflexivity | right])|]).
  subst. repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.

Lemma mod16_sub32 : forall z, z mod 16 = 0 -> (z - 32) mod 16 = 0.
Proof. intros z Hz. replace (z - 32) with (z + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact Hz. Qed.

End g.

Ltac fs_rget HS r H :=
  pose proof (st_ok_restrict_reg tfibsegs _ _ _ _ r HS) as H;
  lazymatch type of H with _ = sv_denot _ ?t => let e := eval vm_compute in t in change t with e in H end;
  cbn [sv_denot] in H.

(* ==========================================================================
   3. The walk
   ========================================================================== *)

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : PcapSyms B.
Hypothesis HFL : amwrite_mf_flush_realizes tfibsegs B link_amf LA_MWRITE.
Hypothesis HMS : amseek_set_realizes tfibsegs B link_amf LA_MSEEK.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).

Lemma fs_laws : AR_laws tfibsegs B.
Proof. exact (YG0q.AR_laws_ok tfibsegs B). Qed.

Lemma fs_errno : as_errno B = 0x631b6c.
Proof. rewrite (ts_errno B TB). reflexivity. Qed.

Lemma fs_consts : amf_buf link_amf = 0x62fee0 /\ amf_size link_amf = 4096 /\ AFS_STK = 4224 /\ AMW_STK = 4192 /\
  AMS_STK = 48 /\ ESTACK = 4096 /\ AMF_ZEROED = 272 /\ AMF_COOKIE = 232 /\ AMF_BUF = 280 /\ AMF_BUFSIZ = 1024 /\
  AMF_BLOCK = 1304 /\ kHighMemBeg = 0x10007fff8000 /\ kLowMemEnd = 0x7fff8000 /\ LA_GOT_GUARD = 0xa2658 /\
  LA_GUARD = 0x651c50 /\ pcap_img_end = 0x654000.
Proof. repeat split; reflexivity. Qed.

Section M.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (f k fl om wend wpos wbase pos len : Z) (pb : list Z).
Hypothesis HPRE : ecall_pre tfibsegs B ly S W regs mem md.
Hypothesis Hslo : ly_stk_lo ly + AFS_STK <= spZ regs.
Hypothesis Hpres : forall a, spZ regs - AFS_STK <= a < spZ regs -> apresent (w_H W) mem a.
Hypothesis H10 : getr regs 10 = w64 f.
Hypothesis H11 : getr regs 11 = w64 0.
Hypothesis H12 : getr regs 12 = w64 0.
Hypothesis Hblk : In (f, AMF_BLOCK) (ablocks B ly S).
Hypothesis Hk : amf_k tfibsegs link_amf (rd W mem) f k.
Hypothesis Hdyn : amf_dyn tfibsegs link_amf (rd W mem) f fl om wend wpos wbase pos len.
Hypothesis Hpend : amf_pend tfibsegs (rd W mem) f pb.
Hypothesis Hlen : Z.of_nat (length pb) = k.
Hypothesis Hbuf : amf_buf_ok tfibsegs B link_amf AFS_STK ly S W regs mem.
Hypothesis Hg1 : rdword (aview tfibsegs (w_H W) mem) LA_GOT_GUARD = Some LA_GUARD.
Hypothesis Hg2 : exists g, rdword (aview tfibsegs (w_H W) mem) LA_GUARD = Some g.
Local Abbreviation sp0 := (spZ regs).

Lemma fs_basics :
  kHighMemBeg + AFS_STK <= sp0 /\ sp0 <= 2 ^ 47 /\ sp0 mod 16 = 0 /\ sp0 <= ly_stk_hi ly /\
  f mod 16 = 0 /\ 4096 <= f /\ f + AMF_BLOCK <= sp0 - AFS_STK.
Proof.
  pose proof HPRE as (HAR & _ & Hal & _ & Htop & _).
  pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
  pose proof (lo_stk_ceil ly HLY) as Lceil. unfold ASAN_CEIL in Lceil.
  pose proof (amf_block_facts tfibsegs B fs_laws ly S W mem md f HAR Hblk) as (F16 & F4 & Fc & _).
  unfold kHighMemEnd in Lhi.
  split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [exact Htop|]. split; [exact F16|]. split; lia.
Qed.

Lemma fs_blk : forall a, f <= a < f + AMF_BLOCK -> ~ in_img tfibsegs a.
Proof.
  intros a Ha. pose proof HPRE as (HAR & _).
  pose proof (amf_block_facts tfibsegs B fs_laws ly S W mem md f HAR Hblk) as (_ & _ & _ & _ & Fby & _).
  exact (proj2 (proj2 (Fby a Ha))).
Qed.

(* the stack band of the post, the FILE head, g_said, errno *)
Definition fband (a : Z) : Prop := sp0 - AFS_STK <= a < sp0.
Definition fhead (a : Z) : Prop := f <= a < f + AMF_ZEROED.
Definition fbuf (a : Z) : Prop := amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf.
Definition ferr (a : Z) : Prop := as_errno B <= a < as_errno B + 4.

(* the post's frame clauses, at an intermediate memory *)
Definition FI (m : word -> option byte) (d : Model) : Prop :=
  AR tfibsegs B ly S W m d /\ same_but_materialized md d /\
  (forall a, fband a -> apresent (w_H W) m a) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ fband a -> ~ fhead a -> ~ fbuf a -> ~ ferr a ->
     aview tfibsegs (w_H W) m a = aview tfibsegs (w_H W) mem a) /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) m a).

Lemma FI_init : FI mem md.
Proof.
  pose proof HPRE as (HAR & _).
  split; [exact HAR|]. split; [apply same_but_materialized_refl|]. split; [exact Hpres|].
  split; [intros; reflexivity | intros a Ha; exact Ha].
Qed.

Lemma FI_run : forall m d m' mat l1 h1 l2 h2,
  FI m d -> sp0 - AFS_STK <= l1 -> h1 <= sp0 -> f <= l2 -> h2 <= f + AMF_ZEROED ->
  (forall x : word, ~ (l1 <= bv_unsigned x < h1) -> ~ (l2 <= bv_unsigned x < h2) -> m' x = m x) ->
  (forall a, l1 <= a < h1 -> apresent (w_H W) m' a) ->
  (forall a, l2 <= a < h2 -> apresent (w_H W) m' a) ->
  FI m' (with_vm_backing (m_vm_lazy d) mat d).
Proof.
  intros m d m' mat l1 h1 l2 h2 (HAR & Hsb & Hbp & Hfr & Hpr) L1 Hh1 L2 Hh2 Heq P1 P2.
  pose proof fs_basics as (Bsp & Bsp47 & _ & Btop & _ & Bf4 & Bfs).
  pose proof fs_consts as (Cb & Cs & Cafs & _ & _ & Ces & Cz & _ & _ & _ & Cbl & Chm & _).
  pose proof HPRE as (_ & _ & _ & Hslo0 & _).
  pose proof (amf_block_facts tfibsegs B fs_laws ly S W m d f HAR Hblk) as (_ & _ & _ & Happ & Fby & _).
  assert (EQ : forall a, 0 <= a < 2 ^ 64 -> ~ (l1 <= a < h1) -> ~ (l2 <= a < h2) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
  { intros a Ha N1 N2. apply Heq; rewrite unsigned_lit_small by lia; assumption. }
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (l1 <= a < h1) -> ~ (l2 <= a < h2) ->
     aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a).
  { intros a Ha N1 N2. apply aview_eq_of. unfold mrestrict. rewrite EQ by assumption. reflexivity. }
  assert (PR0 : forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) m a -> apresent (w_H W) m' a).
  { intros a Ha Hp.
    assert (C : (l1 <= a < h1) \/ (l2 <= a < h2) \/ (~ (l1 <= a < h1) /\ ~ (l2 <= a < h2))) by lia.
    destruct C as [C|[C|[N1 N2]]]; [exact (P1 a C) | exact (P2 a C)|].
    destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite EQ by assumption. exact Hb. }
  assert (PR : forall a, apresent (w_H W) m a -> apresent (w_H W) m' a).
  { intros a Hp. rewrite apresent_mod in *. apply PR0; [apply Z.mod_pos_bound; lia | exact Hp]. }
  pose proof (same_but_materialized_frame d _ (with_vm_backing_same d mat)) as MF.
  split; [|split; [|split; [|split]]].
  - apply (al_frame _ _ fs_laws ly S W m d m' _ HAR).
    + intros a Ha Ho. apply AV; [exact Ha | intros Hw | intros Hw].
      * exact (al_stack _ _ fs_laws ly S W m d a HAR ltac:(lia) Ho).
      * exact (proj1 (proj2 (Fby a ltac:(lia))) Ho).
    + intros a Hv. rewrite (aview_mod _ m' a). rewrite (aview_mod _ m a) in Hv.
      pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Hb.
      assert (C : (l1 <= a mod 2 ^ 64 < h1) \/ (l2 <= a mod 2 ^ 64 < h2) \/
                  (~ (l1 <= a mod 2 ^ 64 < h1) /\ ~ (l2 <= a mod 2 ^ 64 < h2))) by lia.
      destruct C as [C|[C|[N1 N2]]].
      * apply aview_some_of_apresent. exact (P1 _ C).
      * apply aview_some_of_apresent. exact (P2 _ C).
      * rewrite AV by assumption. exact Hv.
    + apply MF. + apply MF. + apply MF.
    + intros a Hb Hh. unfold YG0d.w64. pose proof (in_band_rw_u64 a Hb) as Ha.
      apply EQ; [exact Ha | intros Hw | intros Hw];
        unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb;
        unfold in_app, kLowShadowBeg in Happ; lia.
  - eapply same_but_materialized_trans; [exact Hsb | apply with_vm_backing_same].
  - intros a Ha. apply PR. apply Hbp. exact Ha.
  - intros a Ha Nb Nh Nbu Ne. unfold fband, fhead in Nb, Nh. rewrite AV by (try exact Ha; lia).
    apply Hfr; assumption.
  - intros a Hp. apply PR. apply Hpr. exact Hp.
Qed.

Lemma FI_call : forall m d m' d' lo hi (X : Z -> Prop),
  FI m d -> AR tfibsegs B ly S W m' d' -> same_but_materialized d d' ->
  sp0 - AFS_STK <= lo -> hi <= sp0 ->
  (forall a, X a -> fhead a \/ fbuf a \/ ferr a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ X a -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  FI m' d'.
Proof.
  intros m d m' d' lo hi X (HAR & Hsb & Hbp & Hfr & Hpr) HAR' Hsb' L Hh HX Hkp Hp.
  split; [exact HAR'|]. split; [exact (same_but_materialized_trans _ _ _ Hsb Hsb')|].
  split; [intros a Ha; apply Hp, Hbp, Ha|].
  split; [|intros a Ha; apply Hp, Hpr, Ha].
  intros a Ha Nb Nh Nbu Ne. rewrite Hkp; [apply Hfr; assumption | exact Ha | unfold fband in Nb; lia |].
  intros Hx. destruct (HX a Hx) as [C|[C|C]]; contradiction.
Qed.

(* the frame slots: the caller's s2, s1, s0, ra *)
Definition Frame_ok (m : word -> option byte) : Prop :=
  val_mem tfibsegs (rd W m) (sp0 + -32) 8 (bv_unsigned (getr regs 18)) /\
  val_mem tfibsegs (rd W m) (sp0 + -24) 8 (bv_unsigned (getr regs 9)) /\
  val_mem tfibsegs (rd W m) (sp0 + -16) 8 (bv_unsigned (getr regs 8)) /\
  val_mem tfibsegs (rd W m) (sp0 + -8) 8 (bv_unsigned (getr regs 1)).

Lemma Frame_kept : forall m m', Frame_ok m ->
  (forall a, sp0 - 32 <= a < sp0 -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) -> Frame_ok m'.
Proof.
  intros m m' (F1 & F2 & F3 & F4) Hkp.
  split; [|split; [|split]];
    (eapply vm_kept_range; [intros x Hx; apply Hkp; zofn Hx; lia | eassumption]).
Qed.

(* the FILE predicates across a change that leaves the bytes they read *)
Lemma amf_at_kept : forall m m', amemfile_at tfibsegs link_amf (rd W m) f ->
  (forall x, f <= x < f + AMF_ZEROED -> aview tfibsegs (w_H W) m' x = aview tfibsegs (w_H W) m x) ->
  amemfile_at tfibsegs link_amf (rd W m') f.
Proof.
  intros m m' H Hkp. apply (amemfile_at_frame tfibsegs link_amf (rd W m) (rd W m') f); [|exact H].
  intros x Hx. apply mbyte_of_aview. apply Hkp. exact Hx.
Qed.

Lemma amf_win_kept : forall m m' kk, amf_win tfibsegs (rd W m) f kk ->
  (forall x, f + 32 <= x < f + 64 -> aview tfibsegs (w_H W) m' x = aview tfibsegs (w_H W) m x) ->
  amf_win tfibsegs (rd W m') f kk.
Proof.
  intros m m' kk H Hkp.
  assert (T : forall o v, 32 <= o -> o + 8 <= 64 -> val_mem tfibsegs (rd W m) (f + o) 8 v ->
     val_mem tfibsegs (rd W m') (f + o) 8 v).
  { intros o v A1 A2 Hv. eapply vm_kept_range; [|exact Hv]. intros x Hx. apply Hkp. zofn Hx. lia. }
  destruct H as [(H0 & A & Bq & C) | (H0 & A & Bq & C)].
  - left. split; [exact H0|]. split; [apply T; [lia | lia | exact A]|].
    split; [apply T; [lia | lia | exact Bq] | apply T; [lia | lia | exact C]].
  - right. split; [exact H0|]. split; [apply T; [lia | lia | exact A]|].
    split; [apply T; [lia | lia | exact Bq] | apply T; [lia | lia | exact C]].
Qed.

Lemma amf_dyn_kept : forall m m' a1 a2 a3 a4 a5 a6 a7,
  amf_dyn tfibsegs link_amf (rd W m) f a1 a2 a3 a4 a5 a6 a7 ->
  (forall x, f <= x < f + AMF_ZEROED -> aview tfibsegs (w_H W) m' x = aview tfibsegs (w_H W) m x) ->
  amf_dyn tfibsegs link_amf (rd W m') f a1 a2 a3 a4 a5 a6 a7.
Proof.
  intros m m' a1 a2 a3 a4 a5 a6 a7 (R1 & R2 & R3 & R4 & R5 & R6 & R7 & D1 & D2 & D3 & D4 & D5 & D6 & D7) Hkp.
  assert (T : forall o n v, 0 <= o -> o + Z.of_nat n <= AMF_ZEROED ->
     val_mem tfibsegs (rd W m) (f + o) n v -> val_mem tfibsegs (rd W m') (f + o) n v).
  { intros o n v A1 A2 Hv. eapply vm_kept_range; [|exact Hv]. intros x Hx. apply Hkp. lia. }
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|].
  split; [exact R6|]. split; [exact R7|].
  split; [apply T; [kside | kside | exact D1]|]. split; [apply T; [kside | kside | exact D2]|].
  split; [apply T; [kside | kside | exact D3]|]. split; [apply T; [kside | kside | exact D4]|].
  split; [apply T; [kside | kside | exact D5]|]. split; [apply T; [kside | kside | exact D6]|].
  apply T; [kside | kside | exact D7].
Qed.

(* the FILE after the walk's own stores: rpos, rend, the window words, flags rewritten, the cookie's pos *)
Lemma amf_at_upd : forall m m' fl' pos' lenv,
  amemfile_at tfibsegs link_amf (rd W m) f ->
  (forall x, f <= x < f + AMF_ZEROED -> ~ (f <= x < f + 24) -> ~ (f + 32 <= x < f + 64) ->
     ~ (f + AMF_COOKIE <= x < f + AMF_COOKIE + 8) -> aview tfibsegs (w_H W) m' x = aview tfibsegs (w_H W) m x) ->
  (fl' = AF_NORD \/ fl' = AF_NORD + AF_ERR) -> val_mem tfibsegs (rd W m') (f + 0) 4 fl' ->
  val_mem tfibsegs (rd W m') (f + 8) 8 0 -> val_mem tfibsegs (rd W m') (f + 16) 8 0 ->
  val_mem tfibsegs (rd W m') (f + 32) 8 0 -> val_mem tfibsegs (rd W m') (f + 40) 8 0 ->
  val_mem tfibsegs (rd W m') (f + 48) 8 0 -> val_mem tfibsegs (rd W m') (f + 56) 8 0 ->
  val_mem tfibsegs (rd W m) (f + (AMF_COOKIE + 8)) 8 lenv -> 0 <= pos' <= lenv -> lenv <= amf_size link_amf ->
  val_mem tfibsegs (rd W m') (f + AMF_COOKIE) 8 pos' ->
  amemfile_at tfibsegs link_amf (rd W m') f.
Proof.
  intros m m' fl' pos' lenv (Hf0 & Hfb & Hf16 & Hst & _ & Hom & _ & _) Hkp Hfl V0 V8 V16 V32 V40 V48 V56 Vlen Hpl Hls Vpos.
  assert (T : forall o n v, 0 <= o -> o + Z.of_nat n <= AMF_ZEROED ->
     (o + Z.of_nat n <= 0 \/ 24 <= o) -> (o + Z.of_nat n <= 32 \/ 64 <= o) ->
     (o + Z.of_nat n <= AMF_COOKIE \/ AMF_COOKIE + 8 <= o) ->
     val_mem tfibsegs (rd W m) (f + o) n v -> val_mem tfibsegs (rd W m') (f + o) n v).
  { intros o n v A1 A2 A3 A4 A5 Hv. eapply vm_kept_range; [|exact Hv]. intros x Hx.
    apply Hkp; unfold AMF_ZEROED, AMF_COOKIE in *; lia. }
  split; [exact Hf0|]. split; [exact Hfb|]. split; [exact Hf16|].
  split; [|split; [|split; [|split]]].
  - unfold amemfile_static in *.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat match goal with |- _ /\ _ => split end;
      first [exact V48 | apply T; [kside | kside | kside | kside | kside | assumption]].
  - unfold amemfile_flags. destruct Hfl as [-> | ->]; [left | right]; exact V0.
  - unfold amemfile_omode in *. destruct Hom as [Ho | Ho]; [left | right];
      (apply T; [kside | kside | kside | kside | kside | exact Ho]).
  - unfold amemfile_window. split; [exact V8|]. split; [exact V16|]. left.
    split; [exact V32|]. split; [exact V40 | exact V56].
  - unfold amemfile_cookie. exists pos', lenv. split; [exact Hpl|]. split; [exact Hls|].
    split; [exact Vpos|]. apply T; [kside | kside | kside | kside | kside | exact Vlen].
Qed.

Lemma fs_flags : fl = AF_NORD \/ fl = AF_NORD + AF_ERR.
Proof.
  pose proof Hk as ((_ & _ & _ & _ & Hfl & _) & _).
  pose proof Hdyn as (Rfl & _ & _ & _ & _ & _ & _ & Dfl & _).
  unfold AF_NORD, AF_ERR. destruct Hfl as [Hfl | Hfl]; [left | right];
    (apply (val_mem_det4 _ _ _ _ Dfl Hfl); [exact Rfl | unfold AF_NORD, AF_ERR; lia]).
Qed.

Lemma fs_win : (k = 0 -> wpos = wbase) /\ (0 < k -> wbase = f + 280 /\ wpos = f + 280 + k /\ k <= AMF_BUFSIZ).
Proof.
  pose proof fs_basics as (_ & Bsp47 & _ & _ & _ & Bf4 & Bfs).
  pose proof fs_consts as (_ & _ & Cafs & _ & _ & _ & _ & _ & Cbuf & Cbs & Cbl & _).
  pose proof Hk as (_ & Hwin).
  pose proof Hdyn as (_ & _ & _ & Rwp & Rwb & _ & _ & _ & _ & _ & Dwp & Dwb & _ & _).
  destruct Hwin as [(K0 & W32 & W40 & W56) | (Kr & W32 & W40 & W56)].
  - assert (E1 : wpos = 0) by (apply (val_mem_det8 _ _ _ _ Dwp W40); lia).
    assert (E2 : wbase = 0) by (apply (val_mem_det8 _ _ _ _ Dwb W56); lia).
    split; [intros _; lia | intros Hkp; lia].
  - assert (E1 : wpos = f + AMF_BUF + k) by (apply (val_mem_det8 _ _ _ _ Dwp W40); lia).
    assert (E2 : wbase = f + AMF_BUF) by (apply (val_mem_det8 _ _ _ _ Dwb W56); lia).
    split; [intros Hk0; lia | intros Hkp; lia].
Qed.

(* the state at mseek's entry (QS) after A0 or B1: mref is the memory whose FILE the phase started from *)
Definition QSb (mref : word -> option byte) (regsS : bvmap 5 word) (memS : word -> option byte) (mdS : Model) : Prop :=
  FI memS mdS /\ Frame_ok memS /\
  getr regsS 1 = w64 0x96f14 /\ getr regsS 2 = w64 (sp0 - 32) /\ getr regsS 8 = w64 f /\
  getr regsS 10 = w64 f /\ getr regsS 11 = w64 0 /\ getr regsS 12 = w64 0 /\ keep_regs regs regsS /\
  val_mem tfibsegs (rd W memS) (f + 32) 8 0 /\ val_mem tfibsegs (rd W memS) (f + 40) 8 0 /\
  val_mem tfibsegs (rd W memS) (f + 48) 8 0 /\ val_mem tfibsegs (rd W memS) (f + 56) 8 0 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ fband a -> ~ (f + 32 <= a < f + 64) ->
     aview tfibsegs (w_H W) memS a = aview tfibsegs (w_H W) mref a).

Definition QS (mref : word -> option byte) (W' : world tfibsegs) (c' : config) : Prop :=
  W' = W /\ exists regsS memS mdS, c' = cfg_at tfibsegs LA_MSEEK regsS memS mdS /\ QSb mref regsS memS mdS.

Lemma head_A0 : k = 0 -> SRr tfibsegs W (cfg_at tfibsegs LA_FSEEKO regs mem md) (QS mem).
Proof.
  intros Hk0.
  pose proof fs_basics as (Bsp & Bsp47 & Bal & Btop & Bf16 & Bf4 & Bfs).
  pose proof fs_consts as (Cb & Cs & Cafs & Camw & Cams & Ces & Cz & Cck & Cbuf & Cbs & Cbl & Chm & Clm & _).
  pose proof (proj1 fs_win Hk0) as Hwe.
  pose proof HPRE as (HAR & _).
  pose proof (amf_block_facts tfibsegs B fs_laws ly S W mem md f HAR Hblk) as (_ & _ & _ & _ & Fby & _).
  pose proof Hk as ((_ & _ & _ & (_ & S48 & _ & _ & S80 & _) & _) & _).
  pose proof Hdyn as (_ & _ & _ & Rwp & Rwb & _ & _ & _ & _ & _ & Dwp & Dwb & _ & _).
  set (EA := Ereg regs [Z_to_bv 64 wpos; Z_to_bv 64 wbase]).
  assert (E2 : ew EA 2 = getr regs 2) by exact (ew_Ereg_nat regs _ 2 2%bv eq_refl).
  assert (E10 : ew EA 10 = getr regs 10) by exact (ew_Ereg_nat regs _ 10 10%bv eq_refl).
  assert (Usp : bv_unsigned (ew EA 2) = sp0) by (rewrite E2; reflexivity).
  assert (Uf : bv_unsigned (ew EA 10) = f).
  { rewrite E10, H10. unfold w64. apply unsigned_lit_small. lia. }
  assert (E32 : ew EA 32 = Z_to_bv 64 wpos) by exact (ew_Ereg_extra regs _ 0).
  assert (E33 : ew EA 33 = Z_to_bv 64 wbase) by exact (ew_Ereg_extra regs _ 1).
  assert (E1 : ew EA 1 = getr regs 1) by exact (ew_Ereg_nat regs _ 1 1%bv eq_refl).
  assert (E8 : ew EA 8 = getr regs 8) by exact (ew_Ereg_nat regs _ 8 8%bv eq_refl).
  assert (E9 : ew EA 9 = getr regs 9) by exact (ew_Ereg_nat regs _ 9 9%bv eq_refl).
  assert (E18 : ew EA 18 = getr regs 18) by exact (ew_Ereg_nat regs _ 18 18%bv eq_refl).
  assert (HS : st_ok tfibsegs EA (ss_A R_fK0) (restrict (w_H W) (mkst regs (Z_to_bv 64 LA_FSEEKO) mem (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_A. apply (entry_st_ok_full tfibsegs); fold EA.
    - unfold sr_A. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | exact H11]
        | intros X; discriminate X | exact H12].
    - vm_compute. reflexivity.
    - repeat apply Forall_cons; try apply Forall_nil.
      + apply (region_ok_stack tfibsegs EA _ 2 sp0 (-32) Usp); [lia | lia |].
        intros a Ha. apply AE2y.apresent_writable. apply Hpres. lia.
      + unfold region_ok, R_fK0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Uf. split; [lia|]. split; [lia|]. split.
        { intros o Ho. apply AE2y.apresent_writable. exact (proj1 (Fby (f + o) ltac:(lia))). }
        repeat apply Forall_cons; try apply Forall_nil.
        * apply (chunk_ok_val tfibsegs EA _ f 40 8 (SOff 32 0) wpos);
            [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Dwp].
        * apply (chunk_ok_val tfibsegs EA _ f 48 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact S48].
        * apply (chunk_ok_val tfibsegs EA _ f 56 8 (SOff 33 0) wbase);
            [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Dwb].
        * apply (chunk_ok_val tfibsegs EA _ f 80 8 (SLit LA_MSEEK) LA_MSEEK);
            [reflexivity | unfold LA_MSEEK; cbn; lia | cbn; lia | exact S80].
    - apply pairwise_disjoint_of_extents. unfold R_stkA, R_fK0, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uf.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [exact I | split; exact I]. }
  unfold cfg_at. change (w64 LA_FSEEKO) with (Z_to_bv 64 LA_FSEEKO).
  eapply SRr_bind; [apply (fs_phase W EA _ _ _ _ md HS run_A0a)|].
  cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
  assert (Hbt : branch_taken BC_EQ (sv_denot EA (SOff 32 0)) (sv_denot EA (SOff 33 0)) = true).
  { rewrite branch_eq_U, (U_atom EA 32 wpos E32), (U_atom EA 33 wbase E33) by lia. apply Z.eqb_eq. exact Hwe. }
  assert (HS1c : st_ok tfibsegs EA (YP06.add_cond st_A0a c_wp) (restrict (w_H W) ms1))
    by (apply st_ok_add_cond; [exact HS1 | exact Hbt]).
  eapply SRr_bind; [apply (fs_phase W EA _ _ _ _ _ HS1c run_A0b)|].
  cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2).
  apply SRr_ret. unfold QS. split; [reflexivity|].
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) EA _ _ HS2 eq_refl) as Hshape.
  exists (ms_regs ms2), (ms_mem ms2),
    (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) mat1 md)) mat2 (with_vm_backing (m_vm_lazy md) mat1 md)).
  split; [unfold cfg_at; f_equal; exact Hshape|].
  assert (WA : windows (ss_mem (ss_A R_fK0)) = [(Some 2%nat, -32, 0); (Some 10%nat, 32, 64)]) by reflexivity.
  assert (WAc : windows (ss_mem (YP06.add_cond st_A0a c_wp)) = [(Some 2%nat, -32, 0); (Some 10%nat, 32, 64)])
    by (vm_compute; reflexivity).
  assert (Heq1 : forall x : word, ~ (sp0 - 32 <= bv_unsigned x < sp0) -> ~ (f + 32 <= bv_unsigned x < f + 64) ->
     ms_mem ms1 x = mem x).
  { intros x N1 N2. apply (frame2 EA _ _ _ _ _ _ _ _ _ WA HF1); cbn [base_val]; rewrite ?Usp, ?Uf; lia. }
  assert (Heq2 : forall x : word, ~ (sp0 - 32 <= bv_unsigned x < sp0) -> ~ (f + 32 <= bv_unsigned x < f + 64) ->
     ms_mem ms2 x = ms_mem ms1 x).
  { intros x N1 N2. apply (frame2 EA _ _ _ _ _ _ _ _ _ WAc HF2); cbn [base_val]; rewrite ?Usp, ?Uf; lia. }
  assert (Hr1 : forall x : word, ~ (sp0 - 32 <= bv_unsigned x < sp0) -> ~ (f + 32 <= bv_unsigned x < f + 64) ->
     rd W (ms_mem ms1) x = rd W mem x).
  { intros x N1 N2. apply (frame2 EA _ _ _ _ _ _ _ _ _ WA HFr1); cbn [base_val]; rewrite ?Usp, ?Uf; lia. }
  assert (Hr2 : forall x : word, ~ (sp0 - 32 <= bv_unsigned x < sp0) -> ~ (f + 32 <= bv_unsigned x < f + 64) ->
     rd W (ms_mem ms2) x = rd W (ms_mem ms1) x).
  { intros x N1 N2. apply (frame2 EA _ _ _ _ _ _ _ _ _ WAc HFr2); cbn [base_val]; rewrite ?Usp, ?Uf; lia. }
  assert (FI1 : FI (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
  { apply (FI_run mem md _ mat1 (sp0 - 32) sp0 (f + 32) (f + 64) FI_init); [lia | lia | lia | lia | exact Heq1 | |].
    - intros a Ha. apply (win_present W EA _ ms1 0 (Some 2%nat) (-32) 0 a HS1);
        [vm_compute; reflexivity | cbn [base_val]; rewrite Usp; lia | lia | apply stk_not_img; lia].
    - intros a Ha. apply (win_present W EA _ ms1 1 (Some 10%nat) 32 64 a HS1);
        [vm_compute; reflexivity | cbn [base_val]; rewrite Uf; lia | lia | apply fs_blk; lia]. }
  split.
  { apply (FI_run _ _ _ mat2 (sp0 - 32) sp0 (f + 32) (f + 64) FI1); [lia | lia | lia | lia | exact Heq2 | |].
    - intros a Ha. apply (win_present W EA _ ms2 0 (Some 2%nat) (-32) 0 a HS2);
        [vm_compute; reflexivity | cbn [base_val]; rewrite Usp; lia | lia | apply stk_not_img; lia].
    - intros a Ha. apply (win_present W EA _ ms2 1 (Some 10%nat) 32 64 a HS2);
        [vm_compute; reflexivity | cbn [base_val]; rewrite Uf; lia | lia | apply fs_blk; lia]. }
  split.
  { unfold Frame_ok. rewrite <- Usp. split; [|split; [|split]].
    - exact (st_chunk_val EA _ (restrict (w_H W) ms2) 0 (-32) (Some 2%nat) 8 (SOff 18 0) (bv_unsigned (getr regs 18)) HS2
        ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite E18, Z.add_0_r; reflexivity)
        (u64_range _) ltac:(cbn; lia)).
    - exact (st_chunk_val EA _ (restrict (w_H W) ms2) 0 (-24) (Some 2%nat) 8 (SOff 9 0) (bv_unsigned (getr regs 9)) HS2
        ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite E9, Z.add_0_r; reflexivity)
        (u64_range _) ltac:(cbn; lia)).
    - exact (st_chunk_val EA _ (restrict (w_H W) ms2) 0 (-16) (Some 2%nat) 8 (SOff 8 0) (bv_unsigned (getr regs 8)) HS2
        ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite E8, Z.add_0_r; reflexivity)
        (u64_range _) ltac:(cbn; lia)).
    - exact (st_chunk_val EA _ (restrict (w_H W) ms2) 0 (-8) (Some 2%nat) 8 (SOff 1 0) (bv_unsigned (getr regs 1)) HS2
        ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite E1, Z.add_0_r; reflexivity)
        (u64_range _) ltac:(cbn; lia)). }
  fs_rget HS2 (1%bv : bv 5) R1. fs_rget HS2 (2%bv : bv 5) R2. fs_rget HS2 (8%bv : bv 5) R8.
  fs_rget HS2 (10%bv : bv 5) R10. fs_rget HS2 (11%bv : bv 5) R11. fs_rget HS2 (12%bv : bv 5) R12.
  split; [rewrite R1; reflexivity|].
  split; [rewrite R2, Usp; unfold w64; f_equal; lia|].
  split; [rewrite R8, Uf, Z.add_0_r; reflexivity|].
  split; [rewrite R10, Uf, Z.add_0_r; reflexivity|].
  split; [rewrite R11; reflexivity|].
  split; [rewrite R12; reflexivity|].
  split; [exact (keep_of_st_ok (w_H W) EA _ ms2 regs _ HS2 eq_refl ltac:(vm_compute; reflexivity))|].
  split; [rewrite <- Uf; exact (st_chunk_val EA _ (restrict (w_H W) ms2) 1 32 (Some 10%nat) 8 (SLit 0) 0 HS2
             ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
  split; [rewrite <- Uf; exact (st_chunk_val EA _ (restrict (w_H W) ms2) 1 40 (Some 10%nat) 8 (SLit 0) 0 HS2
             ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
  split; [rewrite <- Uf; exact (st_chunk_val EA _ (restrict (w_H W) ms2) 1 48 (Some 10%nat) 8 (SLit 0) 0 HS2
             ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
  split; [rewrite <- Uf; exact (st_chunk_val EA _ (restrict (w_H W) ms2) 1 56 (Some 10%nat) 8 (SLit 0) 0 HS2
             ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
  intros a Ha Nb Nw. unfold fband in Nb. apply aview_eq_of.
  rewrite Hr2, Hr1 by (rewrite unsigned_lit_small by lia; lia). reflexivity.
Qed.

(* the state at mwrite's entry after A1 *)
Definition Q1 (W' : world tfibsegs) (c' : config) : Prop :=
  W' = W /\ exists regs1 mem1 md1, c' = cfg_at tfibsegs LA_MWRITE regs1 mem1 md1 /\
    FI mem1 md1 /\ Frame_ok mem1 /\
    getr regs1 1 = w64 0x96eec /\ getr regs1 2 = w64 (sp0 - 32) /\ getr regs1 8 = w64 f /\
    getr regs1 9 = w64 0 /\ getr regs1 18 = w64 0 /\
    getr regs1 10 = w64 f /\ getr regs1 11 = w64 0 /\ getr regs1 12 = w64 0 /\ keep_regs regs regs1 /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ fband a -> rd W mem1 (Z_to_bv 64 a) = rd W mem (Z_to_bv 64 a)).

Lemma head_A1 : 0 < k -> SRr tfibsegs W (cfg_at tfibsegs LA_FSEEKO regs mem md) Q1.
Proof.
  intros Hkp.
  pose proof fs_basics as (Bsp & Bsp47 & Bal & Btop & Bf16 & Bf4 & Bfs).
  pose proof fs_consts as (Cb & Cs & Cafs & Camw & Cams & Ces & Cz & Cck & Cbuf & Cbs & Cbl & Chm & Clm & _).
  pose proof (proj2 fs_win Hkp) as (Hwb & Hwp & Hkb).
  pose proof HPRE as (HAR & _).
  pose proof (amf_block_facts tfibsegs B fs_laws ly S W mem md f HAR Hblk) as (_ & _ & _ & _ & Fby & _).
  pose proof Hk as ((_ & _ & _ & (_ & _ & _ & S72 & _) & _) & _).
  pose proof Hdyn as (_ & _ & _ & Rwp & Rwb & _ & _ & _ & _ & _ & Dwp & Dwb & _ & _).
  set (EA := Ereg regs [Z_to_bv 64 wpos; Z_to_bv 64 wbase]).
  assert (E2 : ew EA 2 = getr regs 2) by exact (ew_Ereg_nat regs _ 2 2%bv eq_refl).
  assert (E10 : ew EA 10 = getr regs 10) by exact (ew_Ereg_nat regs _ 10 10%bv eq_refl).
  assert (Usp : bv_unsigned (ew EA 2) = sp0) by (rewrite E2; reflexivity).
  assert (Uf : bv_unsigned (ew EA 10) = f).
  { rewrite E10, H10. unfold w64. apply unsigned_lit_small. lia. }
  assert (E32 : ew EA 32 = Z_to_bv 64 wpos) by exact (ew_Ereg_extra regs _ 0).
  assert (E33 : ew EA 33 = Z_to_bv 64 wbase) by exact (ew_Ereg_extra regs _ 1).
  assert (E1 : ew EA 1 = getr regs 1) by exact (ew_Ereg_nat regs _ 1 1%bv eq_refl).
  assert (E8 : ew EA 8 = getr regs 8) by exact (ew_Ereg_nat regs _ 8 8%bv eq_refl).
  assert (E9 : ew EA 9 = getr regs 9) by exact (ew_Ereg_nat regs _ 9 9%bv eq_refl).
  assert (E18 : ew EA 18 = getr regs 18) by exact (ew_Ereg_nat regs _ 18 18%bv eq_refl).
  assert (HS : st_ok tfibsegs EA (ss_A R_fK1) (restrict (w_H W) (mkst regs (Z_to_bv 64 LA_FSEEKO) mem (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_A. apply (entry_st_ok_full tfibsegs); fold EA.
    - unfold sr_A. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | exact H11]
        | intros X; discriminate X | exact H12].
    - vm_compute. reflexivity.
    - repeat apply Forall_cons; try apply Forall_nil.
      + apply (region_ok_stack tfibsegs EA _ 2 sp0 (-32) Usp); [lia | lia |].
        intros a Ha. apply AE2y.apresent_writable. apply Hpres. lia.
      + unfold region_ok, R_fK1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Uf. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        * apply (chunk_ok_val tfibsegs EA _ f 40 8 (SOff 32 0) wpos);
            [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Dwp].
        * apply (chunk_ok_val tfibsegs EA _ f 56 8 (SOff 33 0) wbase);
            [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Dwb].
        * apply (chunk_ok_val tfibsegs EA _ f 72 8 (SLit LA_MWRITE) LA_MWRITE);
            [reflexivity | unfold LA_MWRITE; cbn; lia | cbn; lia | exact S72].
    - apply pairwise_disjoint_of_extents. unfold R_stkA, R_fK1, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uf.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [exact I | split; exact I]. }
  unfold cfg_at. change (w64 LA_FSEEKO) with (Z_to_bv 64 LA_FSEEKO).
  eapply SRr_bind; [apply (fs_phase W EA _ _ _ _ md HS run_A1a)|].
  cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
  assert (Hbt : branch_taken BC_EQ (sv_denot EA (SOff 32 0)) (sv_denot EA (SOff 33 0)) = false).
  { rewrite branch_eq_U, (U_atom EA 32 wpos E32), (U_atom EA 33 wbase E33) by lia. apply Z.eqb_neq. lia. }
  assert (HS1c : st_ok tfibsegs EA (YP06.add_cond st_A1a c_wpn) (restrict (w_H W) ms1))
    by (apply st_ok_add_cond_neg; [exact HS1 | exact Hbt]).
  eapply SRr_bind; [apply (fs_phase W EA _ _ _ _ _ HS1c run_A1b)|].
  cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2).
  apply SRr_ret. unfold Q1. split; [reflexivity|].
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) EA _ _ HS2 eq_refl) as Hshape.
  exists (ms_regs ms2), (ms_mem ms2),
    (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) mat1 md)) mat2 (with_vm_backing (m_vm_lazy md) mat1 md)).
  split; [unfold cfg_at; f_equal; exact Hshape|].
  assert (WA : windows (ss_mem (ss_A R_fK1)) = [(Some 2%nat, -32, 0); (Some 10%nat, 0, 0)]) by reflexivity.
  assert (WAc : windows (ss_mem (YP06.add_cond st_A1a c_wpn)) = [(Some 2%nat, -32, 0); (Some 10%nat, 0, 0)])
    by (vm_compute; reflexivity).
  assert (Heq1 : forall x : word, ~ (sp0 - 32 <= bv_unsigned x < sp0) -> ~ (f <= bv_unsigned x < f) ->
     ms_mem ms1 x = mem x).
  { intros x N1 N2. apply (frame2 EA _ _ _ _ _ _ _ _ _ WA HF1); cbn [base_val]; rewrite ?Usp, ?Uf; lia. }
  assert (Heq2 : forall x : word, ~ (sp0 - 32 <= bv_unsigned x < sp0) -> ~ (f <= bv_unsigned x < f) ->
     ms_mem ms2 x = ms_mem ms1 x).
  { intros x N1 N2. apply (frame2 EA _ _ _ _ _ _ _ _ _ WAc HF2); cbn [base_val]; rewrite ?Usp, ?Uf; lia. }
  assert (Hr1 : forall x : word, ~ (sp0 - 32 <= bv_unsigned x < sp0) -> rd W (ms_mem ms1) x = rd W mem x).
  { intros x N1. apply (frame2 EA _ _ _ _ _ _ _ _ _ WA HFr1); cbn [base_val]; rewrite ?Usp, ?Uf; lia. }
  assert (Hr2 : forall x : word, ~ (sp0 - 32 <= bv_unsigned x < sp0) -> rd W (ms_mem ms2) x = rd W (ms_mem ms1) x).
  { intros x N1. apply (frame2 EA _ _ _ _ _ _ _ _ _ WAc HFr2); cbn [base_val]; rewrite ?Usp, ?Uf; lia. }
  assert (FI1 : FI (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
  { apply (FI_run mem md _ mat1 (sp0 - 32) sp0 f f FI_init); [lia | lia | lia | lia | exact Heq1 | | intros a Ha; lia].
    intros a Ha. apply (win_present W EA _ ms1 0 (Some 2%nat) (-32) 0 a HS1);
      [vm_compute; reflexivity | cbn [base_val]; rewrite Usp; lia | lia | apply stk_not_img; lia]. }
  split.
  { apply (FI_run _ _ _ mat2 (sp0 - 32) sp0 f f FI1); [lia | lia | lia | lia | exact Heq2 | | intros a Ha; lia].
    intros a Ha. apply (win_present W EA _ ms2 0 (Some 2%nat) (-32) 0 a HS2);
      [vm_compute; reflexivity | cbn [base_val]; rewrite Usp; lia | lia | apply stk_not_img; lia]. }
  split.
  { unfold Frame_ok. rewrite <- Usp. split; [|split; [|split]].
    - exact (st_chunk_val EA _ (restrict (w_H W) ms2) 0 (-32) (Some 2%nat) 8 (SOff 18 0) (bv_unsigned (getr regs 18)) HS2
        ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite E18, Z.add_0_r; reflexivity)
        (u64_range _) ltac:(cbn; lia)).
    - exact (st_chunk_val EA _ (restrict (w_H W) ms2) 0 (-24) (Some 2%nat) 8 (SOff 9 0) (bv_unsigned (getr regs 9)) HS2
        ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite E9, Z.add_0_r; reflexivity)
        (u64_range _) ltac:(cbn; lia)).
    - exact (st_chunk_val EA _ (restrict (w_H W) ms2) 0 (-16) (Some 2%nat) 8 (SOff 8 0) (bv_unsigned (getr regs 8)) HS2
        ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite E8, Z.add_0_r; reflexivity)
        (u64_range _) ltac:(cbn; lia)).
    - exact (st_chunk_val EA _ (restrict (w_H W) ms2) 0 (-8) (Some 2%nat) 8 (SOff 1 0) (bv_unsigned (getr regs 1)) HS2
        ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite E1, Z.add_0_r; reflexivity)
        (u64_range _) ltac:(cbn; lia)). }
  fs_rget HS2 (1%bv : bv 5) R1. fs_rget HS2 (2%bv : bv 5) R2. fs_rget HS2 (8%bv : bv 5) R8.
  fs_rget HS2 (9%bv : bv 5) R9. fs_rget HS2 (18%bv : bv 5) R18.
  fs_rget HS2 (10%bv : bv 5) R10. fs_rget HS2 (11%bv : bv 5) R11. fs_rget HS2 (12%bv : bv 5) R12.
  split; [rewrite R1; reflexivity|].
  split; [rewrite R2, Usp; unfold w64; f_equal; lia|].
  split; [rewrite R8, Uf, Z.add_0_r; reflexivity|].
  split; [rewrite R9; reflexivity|].
  split; [rewrite R18; reflexivity|].
  split; [rewrite R10, Uf, Z.add_0_r; reflexivity|].
  split; [rewrite R11; reflexivity|].
  split; [rewrite R12; reflexivity|].
  split; [exact (keep_of_st_ok (w_H W) EA _ ms2 regs _ HS2 eq_refl ltac:(vm_compute; reflexivity))|].
  intros a Ha Nb. unfold fband in Nb.
  rewrite Hr2, Hr1 by (rewrite unsigned_lit_small by lia; lia). reflexivity.
Qed.

(* phase C: from mseek's return (+0x9c) to the ret *)
Definition QC (flv : Z) (memC : word -> option byte) (W' : world tfibsegs) (c' : config) : Prop :=
  W' = W /\ exists regs' mem' md', c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    FI mem' md' /\ aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
    val_mem tfibsegs (rd W mem') (f + 0) 4 flv /\ val_mem tfibsegs (rd W mem') (f + 8) 8 0 /\
    val_mem tfibsegs (rd W mem') (f + 16) 8 0 /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ fband a -> ~ (f <= a < f + 24) ->
       aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) memC a).

Lemma tail_C_gen : forall flv stC regsC memC mdC,
  sym_runN tfibsegs fs_tbl FUEL (ss_C flv) = (stC, RS_stopped (SR_jalr (SOff 32 0))) ->
  ss_resv stC = None -> clookup fs_tbl (ss_pc stC) = Some RET_WORD_r ->
  sr_get (ss_regs stC) 1%bv = SOff 32 0 -> sr_get (ss_regs stC) 2%bv = SOff 2 32 ->
  sr_get (ss_regs stC) 8%bv = SOff 33 0 -> sr_get (ss_regs stC) 9%bv = SOff 34 0 ->
  sr_get (ss_regs stC) 10%bv = SLit 0 -> sr_get (ss_regs stC) 18%bv = SOff 35 0 ->
  keep_ok (ss_regs stC) = true ->
  chunk_at (ss_mem stC) 1 0 = Some (Some 8%nat, CVal 4 (SLit flv)) ->
  chunk_at (ss_mem stC) 1 8 = Some (Some 8%nat, CVal 8 (SLit 0)) ->
  chunk_at (ss_mem stC) 1 16 = Some (Some 8%nat, CVal 8 (SLit 0)) ->
  win_at (ss_mem stC) 1 = Some (Some 8%nat, 0, 24) ->
  0 <= flv < 2 ^ 32 ->
  FI memC mdC -> Frame_ok memC ->
  getr regsC 2 = w64 (sp0 - 32) -> getr regsC 8 = w64 f -> getr regsC 10 = w64 0 -> keep_regs regs regsC ->
  val_mem tfibsegs (rd W memC) (f + 0) 4 flv ->
  SRr tfibsegs W (cfg_at tfibsegs 0x96f14 regsC memC mdC) (QC flv memC).
Proof.
  intros flv stC regsC memC mdC RUN Hrv Hpc R1 R2 R8 R9 R10 R18 RK C0 C8 C16 WN Rfl HFI HFr S2 S8 S10 SK Vfl.
  pose proof fs_basics as (Bsp & Bsp47 & Bal & Btop & Bf16 & Bf4 & Bfs).
  pose proof fs_consts as (Cb & Cs & Cafs & Camw & Cams & Ces & Cz & Cck & Cbuf & Cbs & Cbl & Chm & Clm & _).
  pose proof HPRE as (_ & Hra & _).
  pose proof HFI as (HARC & _).
  pose proof (amf_block_facts tfibsegs B fs_laws ly S W memC mdC f HARC Hblk) as (_ & _ & _ & _ & Fby & _).
  pose proof HFr as (F1 & F2 & F3 & F4).
  set (EC := Ereg regsC [getr regs 1; getr regs 8; getr regs 9; getr regs 18]).
  assert (E2 : ew EC 2 = getr regsC 2) by exact (ew_Ereg_nat regsC _ 2 2%bv eq_refl).
  assert (E8 : ew EC 8 = getr regsC 8) by exact (ew_Ereg_nat regsC _ 8 8%bv eq_refl).
  assert (Usp : bv_unsigned (ew EC 2) = sp0 - 32).
  { rewrite E2, S2. unfold w64. apply unsigned_lit_small. lia. }
  assert (Uf : bv_unsigned (ew EC 8) = f).
  { rewrite E8, S8. unfold w64. apply unsigned_lit_small. lia. }
  assert (E32 : ew EC 32 = getr regs 1) by exact (ew_Ereg_extra regsC _ 0).
  assert (E33 : ew EC 33 = getr regs 8) by exact (ew_Ereg_extra regsC _ 1).
  assert (E34 : ew EC 34 = getr regs 9) by exact (ew_Ereg_extra regsC _ 2).
  assert (E35 : ew EC 35 = getr regs 18) by exact (ew_Ereg_extra regsC _ 3).
  assert (HS : st_ok tfibsegs EC (ss_C flv) (restrict (w_H W) (mkst regsC (Z_to_bv 64 0x96f14) memC (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_C. apply (entry_st_ok_full tfibsegs); fold EC.
    - apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | exact S10].
    - vm_compute. reflexivity.
    - repeat apply Forall_cons; try apply Forall_nil.
      + unfold region_ok, R_frm. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        * apply (chunk_ok_val tfibsegs EC _ (sp0 - 32) 0 8 (SOff 35 0) (bv_unsigned (getr regs 18)));
            [cbn [sv_denot]; rewrite E35, Z.add_0_r; reflexivity | exact (u64_range _) | cbn; lia |].
          replace (sp0 - 32 + 0) with (sp0 + -32) by lia. exact F1.
        * apply (chunk_ok_val tfibsegs EC _ (sp0 - 32) 8 8 (SOff 34 0) (bv_unsigned (getr regs 9)));
            [cbn [sv_denot]; rewrite E34, Z.add_0_r; reflexivity | exact (u64_range _) | cbn; lia |].
          replace (sp0 - 32 + 8) with (sp0 + -24) by lia. exact F2.
        * apply (chunk_ok_val tfibsegs EC _ (sp0 - 32) 16 8 (SOff 33 0) (bv_unsigned (getr regs 8)));
            [cbn [sv_denot]; rewrite E33, Z.add_0_r; reflexivity | exact (u64_range _) | cbn; lia |].
          replace (sp0 - 32 + 16) with (sp0 + -16) by lia. exact F3.
        * apply (chunk_ok_val tfibsegs EC _ (sp0 - 32) 24 8 (SOff 32 0) (bv_unsigned (getr regs 1)));
            [cbn [sv_denot]; rewrite E32, Z.add_0_r; reflexivity | exact (u64_range _) | cbn; lia |].
          replace (sp0 - 32 + 24) with (sp0 + -8) by lia. exact F4.
      + unfold region_ok, R_fC. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Uf. split; [lia|]. split; [lia|]. split.
        { intros o Ho. apply AE2y.apresent_writable. exact (proj1 (Fby (f + o) ltac:(lia))). }
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs EC _ f 0 4 (SLit flv) flv); [reflexivity | cbn; lia | cbn; lia | exact Vfl].
    - apply pairwise_disjoint_of_extents. unfold R_frm, R_fC, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uf.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [exact I | split; exact I]. }
  unfold cfg_at. change (w64 0x96f14) with (Z_to_bv 64 0x96f14).
  eapply SRr_bind; [apply (fs_phase W EC _ _ _ _ mdC HS RUN)|].
  cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
  eapply (SRr_ret_at tfibsegs fs_tbl fs_tbl_ok AF0x.Hwx_tfa W EC); [exact HS1 | exact Hrv | exact Hpc |].
  intros mat'. rewrite ?wvb_collapse, ?wvb_wvb. unfold QC.
  split; [reflexivity|].
  assert (WC : windows (ss_mem (ss_C flv)) = [(Some 2%nat, 0, 0); (Some 8%nat, 0, 24)]) by reflexivity.
  assert (Heq : forall x : word, ~ (sp0 - 32 <= bv_unsigned x < sp0 - 32) -> ~ (f <= bv_unsigned x < f + 24) ->
     ms_mem ms1 x = memC x).
  { intros x N1 N2. apply (frame2 EC _ _ _ _ _ _ _ _ _ WC HF1); cbn [base_val]; rewrite ?Usp, ?Uf; lia. }
  assert (Hr : forall x : word, ~ (f <= bv_unsigned x < f + 24) -> rd W (ms_mem ms1) x = rd W memC x).
  { intros x N2. apply (frame2 EC _ _ _ _ _ _ _ _ _ WC HFr1); cbn [base_val]; rewrite ?Usp, ?Uf; lia. }
  pose proof (st_ok_restrict_reg tfibsegs _ _ _ _ (1%bv : bv 5) HS1) as Q1. rewrite R1 in Q1. cbn [sv_denot] in Q1.
  rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned in Q1.
  exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy mdC) mat' mdC).
  split.
  { unfold cfg_at. replace (v_jalr (getr (ms_regs ms1) 1) 0) with (w64 (raZ regs)); [reflexivity|].
    rewrite Q1. unfold raZ, w64. rewrite Z_to_bv_bv_unsigned. symmetry. exact Hra. }
  split.
  { apply (FI_run memC mdC _ mat' (sp0 - 32) (sp0 - 32) f (f + 24) HFI);
      [lia | lia | lia | lia | exact Heq | intros a Ha; lia |].
    intros a Ha. apply (win_present W EC _ ms1 1 (Some 8%nat) 0 24 a HS1 WN);
      [cbn [base_val]; rewrite Uf; lia | lia | apply fs_blk; lia]. }
  pose proof (keep_of_st_ok (w_H W) EC _ ms1 regsC _ HS1 eq_refl RK) as KF0.
  pose proof (keep_trans _ _ _ SK KF0) as KF.
  split.
  { apply aregs_of_list. intros r Hr0. cbv [CALLEE_SAVED In] in Hr0.
    destruct Hr0 as [<-|[<-|[<-|[<-|[<-|[<-|Hr0]]]]]].
    - rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ _ HS1), R2. cbn [sv_denot]. rewrite Usp.
      replace (sp0 - 32 + 32) with sp0 by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
    - apply KF. cbv [KEEP In]. left. reflexivity.
    - apply KF. cbv [KEEP In]. right. left. reflexivity.
    - rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ _ HS1), R8. cbn [sv_denot].
      rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ _ HS1), R9. cbn [sv_denot].
      rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ _ HS1), R18. cbn [sv_denot].
      rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - apply KF. cbv [KEEP In] in *. right. right. exact Hr0. }
  split.
  { rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ _ HS1), R10. reflexivity. }
  split.
  { rewrite <- Uf. exact (st_chunk_val EC _ (restrict (w_H W) ms1) 1 0 (Some 8%nat) 4 (SLit flv) flv HS1 C0 eq_refl
      ltac:(cbn; lia) ltac:(cbn; lia)). }
  split.
  { rewrite <- Uf. exact (st_chunk_val EC _ (restrict (w_H W) ms1) 1 8 (Some 8%nat) 8 (SLit 0) 0 HS1 C8 eq_refl
      ltac:(cbn; lia) ltac:(cbn; lia)). }
  split.
  { rewrite <- Uf. exact (st_chunk_val EC _ (restrict (w_H W) ms1) 1 16 (Some 8%nat) 8 (SLit 0) 0 HS1 C16 eq_refl
      ltac:(cbn; lia) ltac:(cbn; lia)). }
  intros a Ha Nb Nw. apply aview_eq_of. rewrite Hr by (rewrite unsigned_lit_small by lia; lia). reflexivity.
Qed.

Lemma tail_C : forall flv regsC memC mdC,
  flv = 4 \/ flv = 36 ->
  FI memC mdC -> Frame_ok memC ->
  getr regsC 2 = w64 (sp0 - 32) -> getr regsC 8 = w64 f -> getr regsC 10 = w64 0 -> keep_regs regs regsC ->
  val_mem tfibsegs (rd W memC) (f + 0) 4 flv ->
  SRr tfibsegs W (cfg_at tfibsegs 0x96f14 regsC memC mdC) (QC flv memC).
Proof.
  intros flv regsC memC mdC Hfl HFI HFr S2 S8 S10 SK Vfl.
  destruct Hfl as [-> | ->].
  - apply (tail_C_gen 4 st_C4 regsC memC mdC run_C4);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | lia | exact HFI | exact HFr | exact S2 | exact S8 | exact S10 | exact SK | exact Vfl].
  - apply (tail_C_gen 36 st_C36 regsC memC mdC run_C36);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | lia | exact HFI | exact HFr | exact S2 | exact S8 | exact S10 | exact SK | exact Vfl].
Qed.

(* mseek, then phase C *)
Definition QF (flv lenR : Z) (mref : word -> option byte) (W' : world tfibsegs) (c' : config) : Prop :=
  W' = W /\ exists regs' mem' md', c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    FI mem' md' /\ aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
    amf_k tfibsegs link_amf (rd W mem') f 0 /\
    amf_dyn tfibsegs link_amf (rd W mem') f flv om 0 0 0 0 lenR /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ fband a -> ~ fhead a ->
       aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mref a).

Lemma seek_tail : forall mref regsS memS mdS flv posR lenR,
  flv = 4 \/ flv = 36 ->
  amemfile_at tfibsegs link_amf (rd W mref) f ->
  val_mem tfibsegs (rd W mref) (f + 0) 4 flv -> val_mem tfibsegs (rd W mref) (f + 136) 4 om ->
  val_mem tfibsegs (rd W mref) (f + AMF_COOKIE) 8 posR ->
  val_mem tfibsegs (rd W mref) (f + (AMF_COOKIE + 8)) 8 lenR ->
  0 <= posR <= lenR -> lenR <= amf_size link_amf ->
  QSb mref regsS memS mdS ->
  SRr tfibsegs W (cfg_at tfibsegs LA_MSEEK regsS memS mdS) (QF flv lenR mref).
Proof.
  intros mref regsS memS mdS flv posR lenR Hflv Hat V0 V136 Vpos Vlen Hpl Hls
    (HFI & HFR & R1 & R2 & R8 & R10 & R11 & R12 & RK & V32 & V40 & V48 & V56 & Hkp).
  pose proof fs_basics as (Bsp & Bsp47 & Bal & Btop & Bf16 & Bf4 & Bfs).
  pose proof fs_consts as (Cb & Cs & Cafs & Camw & Cams & Ces & Cz & Cck & Cbuf & Cbs & Cbl & Chm & Clm & Cgg & Cgu & Cie).
  pose proof fs_errno as Cer.
  pose proof HPRE as (_ & _ & _ & Hslo0 & _ & _ & Hgp & Htp).
  pose proof Hdyn as (_ & Rom & _).
  pose proof HFI as (HARS & _ & HbandS & HfrS & _).
  assert (HspS : spZ regsS = sp0 - 32).
  { change (spZ regsS) with (bv_unsigned (getr regsS 2)). rewrite R2. unfold w64. apply unsigned_lit_small. lia. }
  pose proof Hat as (_ & _ & _ & Hst & _).
  destruct Hst as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S152 & _ & _ & _ & _ & _ & _ & _ & _ & _
    & Ssz & _ & _).
  assert (TK : forall o n v, 0 <= o -> o + Z.of_nat n <= AMF_ZEROED -> (o + Z.of_nat n <= 32 \/ 64 <= o) ->
     val_mem tfibsegs (rd W mref) (f + o) n v -> val_mem tfibsegs (rd W memS) (f + o) n v).
  { intros o n v A1 A2 A3 Hv. eapply vm_kept_range; [|exact Hv]. intros x Hx.
    apply Hkp; [lia | unfold fband; lia | lia]. }
  assert (GK : forall a, LA_GOT_GUARD <= a < LA_GOT_GUARD + 8 \/ LA_GUARD <= a < LA_GUARD + 8 ->
     aview tfibsegs (w_H W) memS a = aview tfibsegs (w_H W) mem a).
  { intros a Ha. assert (Hi : in_img tfibsegs a) by (apply fs_in_img; lia).
    apply HfrS; [lia | unfold fband; lia | | unfold fbuf; lia | unfold ferr; lia].
    intros Hh. unfold fhead in Hh. apply (fs_blk a ltac:(lia)). exact Hi. }
  assert (Hm16 : spZ regsS mod 16 = 0) by (rewrite HspS; apply mod16_sub32; exact Bal).
  eapply SRr_bind.
  { apply (HMS ly S W regsS memS mdS f 0 posR lenR).
    - split; [exact HARS|]. split; [rewrite R1; apply ret_ok_lit; [lia | reflexivity]|]. split; [exact Hm16|].
      rewrite HspS. split; [lia|]. split; [lia|]. split; [intros a Ha; apply HbandS; unfold fband; lia|].
      split; [rewrite (RK 3%bv ltac:(cbv [KEEP In]; left; reflexivity)); exact Hgp|].
      rewrite (RK 4%bv ltac:(cbv [KEEP In]; right; left; reflexivity)); exact Htp.
    - exact R10.
    - exact R11.
    - exact R12.
    - lia.
    - lia.
    - exact Hblk.
    - apply TK; [kside | kside | kside | exact S152].
    - apply TK; [kside | kside | kside | exact Vpos].
    - replace (f + AMF_COOKIE + 8) with (f + (AMF_COOKIE + 8)) by lia. apply TK; [kside | kside | kside | exact Vlen].
    - replace (f + AMF_COOKIE + 16) with (f + (AMF_COOKIE + 16)) by lia. apply TK; [kside | kside | kside | exact Ssz].
    - rewrite (rdword_kept (aview tfibsegs (w_H W) mem)); [exact Hg1|]. intros i Hi. apply GK. lia.
    - pose proof Hg2 as (g & Hg). exists g.
      rewrite (rdword_kept (aview tfibsegs (w_H W) mem)); [exact Hg|]. intros i Hi. apply GK. lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hsb2 & R10b & Hck2 & Hkept2 & Hpr2 & Hwin2).
  rewrite HspS in Hkept2, Hwin2.
  assert (FI2 : FI mem2 md2).
  { apply (FI_call memS mdS mem2 md2 (sp0 - 32 - AMS_STK) (sp0 - 32) (fun a => f + AMF_COOKIE <= a < f + AMF_COOKIE + 8)
      HFI HAR2 Hsb2); [lia | lia | | | exact Hpr2].
    - intros a Ha. cbv beta in Ha. left. unfold fhead. lia.
    - intros a Ha Nw Nx. cbv beta in Nx. apply Hkept2; [exact Ha | lia | exact Nx]. }
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ fband a -> ~ (f + AMF_COOKIE <= a < f + AMF_COOKIE + 8) ->
     aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memS a).
  { intros a Ha Nb Nc. apply Hkept2; [exact Ha | unfold fband in Nb; lia | exact Nc]. }
  assert (FR2 : Frame_ok mem2).
  { apply (Frame_kept memS mem2 HFR). intros a Ha. apply Hkept2; lia. }
  assert (Hra : raZ regsS = 0x96f14) by (unfold raZ; rewrite R1; reflexivity).
  rewrite Hra.
  assert (S2 : getr regs2 2 = w64 (sp0 - 32)) by (rewrite (aregs_reg _ _ 2%bv HP2 (cs_of 2%bv eq_refl)); exact R2).
  assert (S8 : getr regs2 8 = w64 f) by (rewrite (aregs_reg _ _ 8%bv HP2 (cs_of 8%bv eq_refl)); exact R8).
  assert (SK2 : keep_regs regs regs2) by exact (keep_trans _ _ _ RK (keep_of_aregs _ _ HP2)).
  assert (V0S : val_mem tfibsegs (rd W memS) (f + 0) 4 flv) by (apply TK; [kside | kside | kside | exact V0]).
  assert (V0b : val_mem tfibsegs (rd W mem2) (f + 0) 4 flv).
  { eapply vm_kept_range; [|exact V0S]. intros x Hx. zofn Hx. apply K2; [lia | unfold fband; lia | lia]. }
  eapply SRr_mono; [apply (tail_C flv regs2 mem2 md2 Hflv FI2 FR2 S2 S8 R10b SK2 V0b)|].
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & FI3 & HP3 & R10c & V0c & V8c & V16c & K3).
  unfold QF. split; [reflexivity|]. exists regs3, mem3, md3.
  split; [reflexivity|]. split; [exact FI3|]. split; [exact HP3|]. split; [exact R10c|].
  (* mem3 against mref: outside the band, [f, f+24), [f+32, f+64) and the cookie's pos *)
  assert (K3S : forall a, 0 <= a < 2 ^ 64 -> ~ fband a -> ~ (f <= a < f + 24) ->
     ~ (f + AMF_COOKIE <= a < f + AMF_COOKIE + 8) -> aview tfibsegs (w_H W) mem3 a = aview tfibsegs (w_H W) memS a).
  { intros a Ha Nb N1 N2. rewrite K3 by assumption. apply K2; assumption. }
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ fband a -> ~ (f <= a < f + 24) -> ~ (f + 32 <= a < f + 64) ->
     ~ (f + AMF_COOKIE <= a < f + AMF_COOKIE + 8) -> aview tfibsegs (w_H W) mem3 a = aview tfibsegs (w_H W) mref a).
  { intros a Ha Nb N1 N2 N3. rewrite K3S by assumption. apply Hkp; assumption. }
  assert (T3 : forall o n v, 32 <= o -> o + Z.of_nat n <= 64 -> val_mem tfibsegs (rd W memS) (f + o) n v ->
     val_mem tfibsegs (rd W mem3) (f + o) n v).
  { intros o n v A1 A2 Hv. eapply vm_kept_range; [|exact Hv]. intros x Hx.
    apply K3S; [lia | unfold fband; lia | lia | unfold AMF_COOKIE; lia]. }
  assert (TR : forall o n v, 0 <= o -> o + Z.of_nat n <= AMF_ZEROED -> 24 <= o -> (o + Z.of_nat n <= 32 \/ 64 <= o) ->
     (o + Z.of_nat n <= AMF_COOKIE \/ AMF_COOKIE + 8 <= o) ->
     val_mem tfibsegs (rd W mref) (f + o) n v -> val_mem tfibsegs (rd W mem3) (f + o) n v).
  { intros o n v A1 A2 A3 A4 A5 Hv. eapply vm_kept_range; [|exact Hv]. intros x Hx.
    apply KR; unfold fband, AMF_ZEROED, AMF_COOKIE in *; lia. }
  assert (V32c : val_mem tfibsegs (rd W mem3) (f + 32) 8 0) by (apply T3; [lia | kside | exact V32]).
  assert (V40c : val_mem tfibsegs (rd W mem3) (f + 40) 8 0) by (apply T3; [lia | kside | exact V40]).
  assert (V48c : val_mem tfibsegs (rd W mem3) (f + 48) 8 0) by (apply T3; [lia | kside | exact V48]).
  assert (V56c : val_mem tfibsegs (rd W mem3) (f + 56) 8 0) by (apply T3; [lia | kside | exact V56]).
  assert (Vposc : val_mem tfibsegs (rd W mem3) (f + AMF_COOKIE) 8 0).
  { eapply vm_kept_range; [|exact Hck2]. intros x Hx. zofn Hx. apply K3; [lia | unfold fband; lia | unfold AMF_COOKIE in Hx; lia]. }
  assert (Vlenc : val_mem tfibsegs (rd W mem3) (f + (AMF_COOKIE + 8)) 8 lenR)
    by (apply TR; [kside | kside | kside | kside | kside | exact Vlen]).
  assert (V136c : val_mem tfibsegs (rd W mem3) (f + 136) 4 om)
    by (apply TR; [kside | kside | kside | kside | kside | exact V136]).
  split.
  { split.
    - apply (amf_at_upd mref mem3 flv 0 lenR Hat); [| unfold AF_NORD, AF_ERR; lia | exact V0c | exact V8c | exact V16c
        | exact V32c | exact V40c | exact V48c | exact V56c | exact Vlen | lia | exact Hls | exact Vposc].
      intros x Hx N1 N2 N3. apply KR; [lia | unfold fband, AMF_ZEROED in *; lia | exact N1 | exact N2 | exact N3].
    - left. split; [reflexivity|]. split; [exact V32c|]. split; [exact V40c | exact V56c]. }
  split.
  { unfold amf_dyn. destruct Hflv as [-> | ->].
    all: split; [lia|]; split; [exact Rom|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|];
      split; [exact Hls|]; split; [assumption|]; split; [exact V136c|]; split; [exact V32c|];
      split; [exact V40c|]; split; [exact V56c|]; split; [exact Vposc | exact Vlenc]. }
  intros a Ha Nb Nh. unfold fhead in Nh. apply KR; [exact Ha | exact Nb | lia | lia | unfold AMF_COOKIE, AMF_ZEROED in *; lia].
Qed.

(* phase B0: n1 < k, wpos = 0: return -1 with no store *)
Lemma tail_B0 : forall regsB memB mdB,
  FI memB mdB -> Frame_ok memB ->
  getr regsB 2 = w64 (sp0 - 32) -> getr regsB 8 = w64 f -> keep_regs regs regsB ->
  val_mem tfibsegs (rd W memB) (f + 40) 8 0 ->
  SRr tfibsegs W (cfg_at tfibsegs 0x96eec regsB memB mdB)
    (fun W' c' => W' = W /\ exists regs' mem' md', c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
       FI mem' md' /\ aregs_preserved regs regs' /\ getr regs' 10 = w64 (-1) /\ mem' = memB).
Proof.
  intros regsB memB mdB HFI HFr S2 S8 SK V40.
  pose proof fs_basics as (Bsp & Bsp47 & Bal & Btop & Bf16 & Bf4 & Bfs).
  pose proof fs_consts as (Cb & Cs & Cafs & Camw & Cams & Ces & Cz & Cck & Cbuf & Cbs & Cbl & Chm & Clm & _).
  pose proof HPRE as (_ & Hra & _).
  pose proof HFr as (F1 & F2 & F3 & F4).
  set (EB := Ereg regsB [getr regs 1; getr regs 8; getr regs 9; getr regs 18]).
  assert (E2 : ew EB 2 = getr regsB 2) by exact (ew_Ereg_nat regsB _ 2 2%bv eq_refl).
  assert (E8 : ew EB 8 = getr regsB 8) by exact (ew_Ereg_nat regsB _ 8 8%bv eq_refl).
  assert (Usp : bv_unsigned (ew EB 2) = sp0 - 32).
  { rewrite E2, S2. unfold w64. apply unsigned_lit_small. lia. }
  assert (Uf : bv_unsigned (ew EB 8) = f).
  { rewrite E8, S8. unfold w64. apply unsigned_lit_small. lia. }
  assert (E32 : ew EB 32 = getr regs 1) by exact (ew_Ereg_extra regsB _ 0).
  assert (E33 : ew EB 33 = getr regs 8) by exact (ew_Ereg_extra regsB _ 1).
  assert (E34 : ew EB 34 = getr regs 9) by exact (ew_Ereg_extra regsB _ 2).
  assert (E35 : ew EB 35 = getr regs 18) by exact (ew_Ereg_extra regsB _ 3).
  assert (HS : st_ok tfibsegs EB (ss_B R_fB0) (restrict (w_H W) (mkst regsB (Z_to_bv 64 0x96eec) memB (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_B. apply (entry_st_ok_full tfibsegs); fold EB.
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - repeat apply Forall_cons; try apply Forall_nil.
      + unfold region_ok, R_frm. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        * apply (chunk_ok_val tfibsegs EB _ (sp0 - 32) 0 8 (SOff 35 0) (bv_unsigned (getr regs 18)));
            [cbn [sv_denot]; rewrite E35, Z.add_0_r; reflexivity | exact (u64_range _) | cbn; lia |].
          replace (sp0 - 32 + 0) with (sp0 + -32) by lia. exact F1.
        * apply (chunk_ok_val tfibsegs EB _ (sp0 - 32) 8 8 (SOff 34 0) (bv_unsigned (getr regs 9)));
            [cbn [sv_denot]; rewrite E34, Z.add_0_r; reflexivity | exact (u64_range _) | cbn; lia |].
          replace (sp0 - 32 + 8) with (sp0 + -24) by lia. exact F2.
        * apply (chunk_ok_val tfibsegs EB _ (sp0 - 32) 16 8 (SOff 33 0) (bv_unsigned (getr regs 8)));
            [cbn [sv_denot]; rewrite E33, Z.add_0_r; reflexivity | exact (u64_range _) | cbn; lia |].
          replace (sp0 - 32 + 16) with (sp0 + -16) by lia. exact F3.
        * apply (chunk_ok_val tfibsegs EB _ (sp0 - 32) 24 8 (SOff 32 0) (bv_unsigned (getr regs 1)));
            [cbn [sv_denot]; rewrite E32, Z.add_0_r; reflexivity | exact (u64_range _) | cbn; lia |].
          replace (sp0 - 32 + 24) with (sp0 + -8) by lia. exact F4.
      + unfold region_ok, R_fB0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Uf. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs EB _ f 40 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V40].
    - apply pairwise_disjoint_of_extents. unfold R_frm, R_fB0, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uf.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [exact I | split; exact I]. }
  unfold cfg_at. change (w64 0x96eec) with (Z_to_bv 64 0x96eec).
  eapply SRr_bind; [apply (fs_phase W EB _ _ _ _ mdB HS run_B0)|].
  cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
  eapply (SRr_ret_at tfibsegs fs_tbl fs_tbl_ok AF0x.Hwx_tfa W EB); [exact HS1 | reflexivity | vm_compute; reflexivity |].
  intros mat'. rewrite ?wvb_collapse, ?wvb_wvb. cbv beta.
  split; [reflexivity|].
  assert (ME : ms_mem ms1 = memB)
    by exact (frame_of_read_only EB (ss_mem (ss_B R_fB0)) _ _ ltac:(vm_compute; reflexivity) HF1).
  pose proof (st_ok_restrict_reg tfibsegs _ _ _ _ (1%bv : bv 5) HS1) as Q1.
  change (sr_get (ss_regs st_B0) 1%bv) with (SOff 32 0) in Q1. cbn [sv_denot] in Q1.
  rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned in Q1.
  exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy mdB) mat' mdB).
  split.
  { unfold cfg_at. replace (v_jalr (getr (ms_regs ms1) 1) 0) with (w64 (raZ regs)); [reflexivity|].
    rewrite Q1. unfold raZ, w64. rewrite Z_to_bv_bv_unsigned. symmetry. exact Hra. }
  split.
  { apply (FI_run memB mdB _ mat' (sp0 - 32) (sp0 - 32) f f HFI);
      [lia | lia | lia | lia | intros x _ _; rewrite ME; reflexivity | intros a Ha; lia | intros a Ha; lia]. }
  pose proof (keep_of_st_ok (w_H W) EB _ ms1 regsB _ HS1 eq_refl ltac:(vm_compute; reflexivity)) as KF0.
  pose proof (keep_trans _ _ _ SK KF0) as KF.
  split.
  { apply aregs_of_list. intros r Hr0. cbv [CALLEE_SAVED In] in Hr0.
    destruct Hr0 as [<-|[<-|[<-|[<-|[<-|[<-|Hr0]]]]]].
    - fs_rget HS1 (2%bv : bv 5) R2. rewrite R2, Usp.
      replace (sp0 - 32 + 32) with sp0 by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
    - apply KF. cbv [KEEP In]. left. reflexivity.
    - apply KF. cbv [KEEP In]. right. left. reflexivity.
    - fs_rget HS1 (8%bv : bv 5) R8. rewrite R8, E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - fs_rget HS1 (9%bv : bv 5) R9. rewrite R9, E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - fs_rget HS1 (18%bv : bv 5) R18. rewrite R18, E35, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - apply KF. cbv [KEEP In] in *. right. right. exact Hr0. }
  split.
  { fs_rget HS1 (10%bv : bv 5) R10. rewrite R10. apply bv_eq. reflexivity. }
  exact ME.
Qed.

(* phase B1: n1 = k, wpos = wbase = f + 280: as A0 from +0x84 to mseek's entry *)
Lemma mid_B1 : forall regsB memB mdB,
  FI memB mdB -> Frame_ok memB ->
  getr regsB 2 = w64 (sp0 - 32) -> getr regsB 8 = w64 f -> getr regsB 9 = w64 0 -> getr regsB 18 = w64 0 ->
  keep_regs regs regsB ->
  val_mem tfibsegs (rd W memB) (f + 40) 8 (f + 280) -> val_mem tfibsegs (rd W memB) (f + 48) 8 0 ->
  val_mem tfibsegs (rd W memB) (f + 80) 8 LA_MSEEK ->
  SRr tfibsegs W (cfg_at tfibsegs 0x96eec regsB memB mdB) (QS memB).
Proof.
  intros regsB memB mdB HFI HFr S2 S8 S9 S18 SK V40 V48 V80.
  pose proof fs_basics as (Bsp & Bsp47 & Bal & Btop & Bf16 & Bf4 & Bfs).
  pose proof fs_consts as (Cb & Cs & Cafs & Camw & Cams & Ces & Cz & Cck & Cbuf & Cbs & Cbl & Chm & Clm & _).
  pose proof HFI as (HARB & _).
  pose proof (amf_block_facts tfibsegs B fs_laws ly S W memB mdB f HARB Hblk) as (_ & _ & _ & _ & Fby & _).
  pose proof HFr as (F1 & F2 & F3 & F4).
  set (EB := Ereg regsB [getr regs 1; getr regs 8; getr regs 9; getr regs 18]).
  assert (E2r : ew EB 2 = getr regsB 2) by exact (ew_Ereg_nat regsB _ 2 2%bv eq_refl).
  assert (E8r : ew EB 8 = getr regsB 8) by exact (ew_Ereg_nat regsB _ 8 8%bv eq_refl).
  assert (E9r : ew EB 9 = getr regsB 9) by exact (ew_Ereg_nat regsB _ 9 9%bv eq_refl).
  assert (E18r : ew EB 18 = getr regsB 18) by exact (ew_Ereg_nat regsB _ 18 18%bv eq_refl).
  assert (Usp : bv_unsigned (ew EB 2) = sp0 - 32).
  { rewrite E2r, S2. unfold w64. apply unsigned_lit_small. lia. }
  assert (Uf : bv_unsigned (ew EB 8) = f).
  { rewrite E8r, S8. unfold w64. apply unsigned_lit_small. lia. }
  assert (E8 : ew EB 8 = Z_to_bv 64 f) by (rewrite E8r, S8; reflexivity).
  assert (E9 : ew EB 9 = Z_to_bv 64 0) by (rewrite E9r, S9; reflexivity).
  assert (E18 : ew EB 18 = Z_to_bv 64 0) by (rewrite E18r, S18; reflexivity).
  assert (E32 : ew EB 32 = getr regs 1) by exact (ew_Ereg_extra regsB _ 0).
  assert (E33 : ew EB 33 = getr regs 8) by exact (ew_Ereg_extra regsB _ 1).
  assert (E34 : ew EB 34 = getr regs 9) by exact (ew_Ereg_extra regsB _ 2).
  assert (E35 : ew EB 35 = getr regs 18) by exact (ew_Ereg_extra regsB _ 3).
  assert (HS : st_ok tfibsegs EB (ss_B R_fB1) (restrict (w_H W) (mkst regsB (Z_to_bv 64 0x96eec) memB (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_B. apply (entry_st_ok_full tfibsegs); fold EB.
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - repeat apply Forall_cons; try apply Forall_nil.
      + unfold region_ok, R_frm. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        * apply (chunk_ok_val tfibsegs EB _ (sp0 - 32) 0 8 (SOff 35 0) (bv_unsigned (getr regs 18)));
            [cbn [sv_denot]; rewrite E35, Z.add_0_r; reflexivity | exact (u64_range _) | cbn; lia |].
          replace (sp0 - 32 + 0) with (sp0 + -32) by lia. exact F1.
        * apply (chunk_ok_val tfibsegs EB _ (sp0 - 32) 8 8 (SOff 34 0) (bv_unsigned (getr regs 9)));
            [cbn [sv_denot]; rewrite E34, Z.add_0_r; reflexivity | exact (u64_range _) | cbn; lia |].
          replace (sp0 - 32 + 8) with (sp0 + -24) by lia. exact F2.
        * apply (chunk_ok_val tfibsegs EB _ (sp0 - 32) 16 8 (SOff 33 0) (bv_unsigned (getr regs 8)));
            [cbn [sv_denot]; rewrite E33, Z.add_0_r; reflexivity | exact (u64_range _) | cbn; lia |].
          replace (sp0 - 32 + 16) with (sp0 + -16) by lia. exact F3.
        * apply (chunk_ok_val tfibsegs EB _ (sp0 - 32) 24 8 (SOff 32 0) (bv_unsigned (getr regs 1)));
            [cbn [sv_denot]; rewrite E32, Z.add_0_r; reflexivity | exact (u64_range _) | cbn; lia |].
          replace (sp0 - 32 + 24) with (sp0 + -8) by lia. exact F4.
      + unfold region_ok, R_fB1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Uf. split; [lia|]. split; [lia|]. split.
        { intros o Ho. apply AE2y.apresent_writable. exact (proj1 (Fby (f + o) ltac:(lia))). }
        repeat apply Forall_cons; try apply Forall_nil.
        * apply (chunk_ok_val tfibsegs EB _ f 40 8 (SOff 8 280) (f + 280));
            [cbn [sv_denot]; rewrite Uf; reflexivity | cbn; lia | cbn; lia | exact V40].
        * apply (chunk_ok_val tfibsegs EB _ f 48 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V48].
        * apply (chunk_ok_val tfibsegs EB _ f 80 8 (SLit LA_MSEEK) LA_MSEEK);
            [reflexivity | unfold LA_MSEEK; cbn; lia | cbn; lia | exact V80].
    - apply pairwise_disjoint_of_extents. unfold R_frm, R_fB1, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uf.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [exact I | split; exact I]. }
  unfold cfg_at. change (w64 0x96eec) with (Z_to_bv 64 0x96eec).
  eapply SRr_bind; [apply (fs_phase W EB _ _ _ _ mdB HS run_B1a)|].
  cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
  assert (Hbt : branch_taken BC_EQ (sv_denot EB (SOff 8 280)) (sv_denot EB (SLit 0)) = false).
  { rewrite branch_eq_U, (U_atom_off EB 8 f 280 E8) by lia. rewrite U_SLit. change (zcanon 0) with 0. apply Z.eqb_neq. lia. }
  assert (HS1c : st_ok tfibsegs EB (YP06.add_cond st_B1a c_b1) (restrict (w_H W) ms1))
    by (apply st_ok_add_cond_neg; [exact HS1 | exact Hbt]).
  eapply SRr_bind; [apply (fs_phase W EB _ _ _ _ _ HS1c run_B1b)|].
  cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2).
  apply SRr_ret. unfold QS. split; [reflexivity|].
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) EB _ _ HS2 eq_refl) as Hshape.
  exists (ms_regs ms2), (ms_mem ms2),
    (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy mdB) mat1 mdB)) mat2 (with_vm_backing (m_vm_lazy mdB) mat1 mdB)).
  split; [unfold cfg_at; f_equal; exact Hshape|].
  assert (WB : windows (ss_mem (ss_B R_fB1)) = [(Some 2%nat, 0, 0); (Some 8%nat, 32, 64)]) by reflexivity.
  assert (WBc : windows (ss_mem (YP06.add_cond st_B1a c_b1)) = [(Some 2%nat, 0, 0); (Some 8%nat, 32, 64)])
    by (vm_compute; reflexivity).
  assert (Heq1 : forall x : word, ~ (sp0 - 32 <= bv_unsigned x < sp0 - 32) -> ~ (f + 32 <= bv_unsigned x < f + 64) ->
     ms_mem ms1 x = memB x).
  { intros x N1 N2. apply (frame2 EB _ _ _ _ _ _ _ _ _ WB HF1); cbn [base_val]; rewrite ?Usp, ?Uf; lia. }
  assert (Heq2 : forall x : word, ~ (sp0 - 32 <= bv_unsigned x < sp0 - 32) -> ~ (f + 32 <= bv_unsigned x < f + 64) ->
     ms_mem ms2 x = ms_mem ms1 x).
  { intros x N1 N2. apply (frame2 EB _ _ _ _ _ _ _ _ _ WBc HF2); cbn [base_val]; rewrite ?Usp, ?Uf; lia. }
  assert (Hr1 : forall x : word, ~ (f + 32 <= bv_unsigned x < f + 64) -> rd W (ms_mem ms1) x = rd W memB x).
  { intros x N2. apply (frame2 EB _ _ _ _ _ _ _ _ _ WB HFr1); cbn [base_val]; rewrite ?Usp, ?Uf; lia. }
  assert (Hr2 : forall x : word, ~ (f + 32 <= bv_unsigned x < f + 64) -> rd W (ms_mem ms2) x = rd W (ms_mem ms1) x).
  { intros x N2. apply (frame2 EB _ _ _ _ _ _ _ _ _ WBc HFr2); cbn [base_val]; rewrite ?Usp, ?Uf; lia. }
  assert (FI1 : FI (ms_mem ms1) (with_vm_backing (m_vm_lazy mdB) mat1 mdB)).
  { apply (FI_run memB mdB _ mat1 (sp0 - 32) (sp0 - 32) (f + 32) (f + 64) HFI);
      [lia | lia | lia | lia | exact Heq1 | intros a Ha; lia |].
    intros a Ha. apply (win_present W EB _ ms1 1 (Some 8%nat) 32 64 a HS1);
      [vm_compute; reflexivity | cbn [base_val]; rewrite Uf; lia | lia | apply fs_blk; lia]. }
  assert (AVk : forall a, 0 <= a < 2 ^ 64 -> ~ (f + 32 <= a < f + 64) ->
     aview tfibsegs (w_H W) (ms_mem ms2) a = aview tfibsegs (w_H W) memB a).
  { intros a Ha Nw. apply aview_eq_of. rewrite Hr2, Hr1 by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
  split.
  { apply (FI_run _ _ _ mat2 (sp0 - 32) (sp0 - 32) (f + 32) (f + 64) FI1);
      [lia | lia | lia | lia | exact Heq2 | intros a Ha; lia |].
    intros a Ha. apply (win_present W EB _ ms2 1 (Some 8%nat) 32 64 a HS2);
      [vm_compute; reflexivity | cbn [base_val]; rewrite Uf; lia | lia | apply fs_blk; lia]. }
  split.
  { apply (Frame_kept memB _ HFr). intros a Ha. apply AVk; lia. }
  fs_rget HS2 (1%bv : bv 5) R1. fs_rget HS2 (2%bv : bv 5) R2. fs_rget HS2 (8%bv : bv 5) R8.
  fs_rget HS2 (10%bv : bv 5) R10. fs_rget HS2 (11%bv : bv 5) R11. fs_rget HS2 (12%bv : bv 5) R12.
  split; [rewrite R1; reflexivity|].
  split; [rewrite R2, Usp, Z.add_0_r; reflexivity|].
  split; [rewrite R8, Uf, Z.add_0_r; reflexivity|].
  split; [rewrite R10, Uf, Z.add_0_r; reflexivity|].
  split; [rewrite R11, E9, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
  split; [rewrite R12, E18, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
  split; [exact (keep_trans _ _ _ SK (keep_of_st_ok (w_H W) EB _ ms2 regsB _ HS2 eq_refl ltac:(vm_compute; reflexivity)))|].
  split; [rewrite <- Uf; exact (st_chunk_val EB _ (restrict (w_H W) ms2) 1 32 (Some 8%nat) 8 (SLit 0) 0 HS2
             ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
  split; [rewrite <- Uf; exact (st_chunk_val EB _ (restrict (w_H W) ms2) 1 40 (Some 8%nat) 8 (SLit 0) 0 HS2
             ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
  split; [rewrite <- Uf; exact (st_chunk_val EB _ (restrict (w_H W) ms2) 1 48 (Some 8%nat) 8 (SLit 0) 0 HS2
             ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
  split; [rewrite <- Uf; exact (st_chunk_val EB _ (restrict (w_H W) ms2) 1 56 (Some 8%nat) 8 (SLit 0) 0 HS2
             ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
  intros a Ha Nb Nw. apply AVk; assumption.
Qed.

(* the contract's post, at link's FILE *)
Definition fs_post (W' : world tfibsegs) (c' : config) : Prop :=
  W' = W /\ exists regs' mem' md',
    let n1 := amf_n1 link_amf k pos in
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
    amf_k tfibsegs link_amf (rd W mem') f 0 /\ amf_pend tfibsegs (rd W mem') f pb /\
    azbytes tfibsegs (rd W mem') (amf_buf link_amf + pos) (firstn (Z.to_nat n1) pb) /\
    (n1 < k ->
       getr regs' 10 = w64 (-1) /\
       amf_dyn tfibsegs link_amf (rd W mem') f (Z.lor fl AF_ERR) om 0 0 0 (pos + n1) (Z.max len (pos + n1))) /\
    (n1 = k ->
       getr regs' 10 = w64 0 /\
       amf_dyn tfibsegs link_amf (rd W mem') f fl om 0 0 0 0 (Z.max len (pos + k))) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - AFS_STK <= a < spZ regs) -> ~ (f <= a < f + AMF_ZEROED) ->
       ~ (amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf) -> ~ (as_errno B <= a < as_errno B + 4) ->
       aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
    (forall a, spZ regs - AFS_STK <= a < spZ regs -> apresent (w_H W) mem' a).

Lemma fs_post_of : forall regs' mem' md',
  FI mem' md' -> aregs_preserved regs regs' ->
  amf_k tfibsegs link_amf (rd W mem') f 0 -> amf_pend tfibsegs (rd W mem') f pb ->
  azbytes tfibsegs (rd W mem') (amf_buf link_amf + pos) (firstn (Z.to_nat (amf_n1 link_amf k pos)) pb) ->
  (amf_n1 link_amf k pos < k ->
     getr regs' 10 = w64 (-1) /\
     amf_dyn tfibsegs link_amf (rd W mem') f (Z.lor fl AF_ERR) om 0 0 0 (pos + amf_n1 link_amf k pos)
       (Z.max len (pos + amf_n1 link_amf k pos))) ->
  (amf_n1 link_amf k pos = k ->
     getr regs' 10 = w64 0 /\ amf_dyn tfibsegs link_amf (rd W mem') f fl om 0 0 0 0 (Z.max len (pos + k))) ->
  fs_post W (cfg_at tfibsegs (raZ regs) regs' mem' md').
Proof.
  intros regs' mem' md' (HAR' & Hsb & Hbp & Hfr & Hpr) HP Hk' Hpend' Haz Hlt Heq.
  split; [reflexivity|]. exists regs', mem', md'. cbv zeta.
  split; [reflexivity|]. split; [exact HAR'|]. split; [exact HP|]. split; [exact Hsb|].
  split; [exact Hk'|]. split; [exact Hpend'|]. split; [exact Haz|]. split; [exact Hlt|]. split; [exact Heq|].
  split; [exact Hfr|]. split; [exact Hpr | exact Hbp].
Qed.

Lemma fs_main : SRr tfibsegs W (cfg_at tfibsegs LA_FSEEKO regs mem md) fs_post.
Proof.
  pose proof fs_basics as (Bsp & Bsp47 & Bal & Btop & Bf16 & Bf4 & Bfs).
  pose proof fs_consts as (Cb & Cs & Cafs & Camw & Cams & Ces & Cz & Cck & Cbuf & Cbs & Cbl & Chm & Clm & Cgg & Cgu & Cie).
  pose proof fs_errno as Cer.
  pose proof fs_flags as Hflg.
  assert (Hflv : fl = 4 \/ fl = 36) by (unfold AF_NORD, AF_ERR in Hflg; lia).
  pose proof Hk as (Hat & Hwin).
  pose proof Hdyn as (Rfl & Rom & Rwe & Rwp & Rwb & Rpl & Rls & Dfl & Dom & Dwe & Dwp & Dwb & Dpos & Dlen).
  pose proof HPRE as (HAR & _ & _ & Hslo0 & _ & _ & Hgp & Htp).
  assert (Hk0' : 0 <= k) by lia.
  assert (Hn1le : amf_n1 link_amf k pos <= k) by (unfold amf_n1; lia).
  assert (Hn10 : 0 <= amf_n1 link_amf k pos) by (unfold amf_n1; rewrite Cs; lia).
  destruct (Z.eq_dec k 0) as [Hk0 | Hk0].
  - (* k = 0: no flush *)
    assert (Hn1 : amf_n1 link_amf k pos = 0) by (unfold amf_n1; rewrite Cs; lia).
    eapply SRr_bind; [apply (head_A0 Hk0)|].
    cbv beta. intros W1 c1 _ (-> & regsS & memS & mdS & -> & HQS).
    eapply SRr_mono; [apply (seek_tail mem regsS memS mdS fl pos len Hflv Hat Dfl Dom Dpos Dlen Rpl Rls HQS)|].
    cbv beta. intros W2 c2 _ (-> & regs' & mem' & md' & -> & HFI' & HP' & R10' & Hk' & Hdyn' & Hkept').
    apply fs_post_of; try assumption.
    + apply (azbytes_kept (w_H W) mem mem'); [exact Hpend|]. intros i Hi.
      apply Hkept'; [lia | unfold fband; lia | unfold fhead; unfold AMF_BUF in *; lia].
    + rewrite Hn1. intros i Hi. exfalso. rewrite length_firstn in Hi. change (Z.to_nat 0) with 0%nat in Hi. lia.
    + intros Hlt. lia.
    + intros _. split; [exact R10'|]. replace (Z.max len (pos + k)) with len by lia. exact Hdyn'.
  - (* 0 < k: the flush *)
    assert (Hkp : 0 < k) by lia.
    pose proof (proj2 fs_win Hkp) as (Hwbe & Hwpe & Hkb).
    eapply SRr_bind; [apply (head_A1 Hkp)|].
    cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & HFI1 & HFr1 & R1 & R2 & R8 & R9 & R18 & R10 & R11 & R12
      & RK1 & Hkept1).
    pose proof HFI1 as (HAR1 & _ & Hband1 & _ & _).
    assert (Hsp1 : spZ regs1 = sp0 - 32).
    { change (spZ regs1) with (bv_unsigned (getr regs1 2)). rewrite R2. unfold w64. apply unsigned_lit_small. lia. }
    assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ fband a -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a).
    { intros a Ha Nb. apply aview_eq_of. apply Hkept1; assumption. }
    assert (FK1 : forall x, f <= x < f + AMF_BLOCK -> aview tfibsegs (w_H W) mem1 x = aview tfibsegs (w_H W) mem x).
    { intros x Hx. apply AV1; [lia | unfold fband; lia]. }
    assert (Hk1 : amf_k tfibsegs link_amf (rd W mem1) f k).
    { split; [apply (amf_at_kept mem mem1 Hat); intros x Hx; apply FK1; lia|].
      apply (amf_win_kept mem mem1 k Hwin). intros x Hx. apply FK1. lia. }
    assert (Hdyn1 : amf_dyn tfibsegs link_amf (rd W mem1) f fl om wend wpos wbase pos len).
    { apply (amf_dyn_kept mem mem1 _ _ _ _ _ _ _ Hdyn). intros x Hx. apply FK1. lia. }
    assert (Hpend1 : amf_pend tfibsegs (rd W mem1) f pb).
    { apply (azbytes_kept (w_H W) mem mem1 _ pb Hpend). intros i Hi. apply FK1. unfold AMF_BUF, AMF_BUFSIZ in *. lia. }
    assert (Hbuf1 : amf_buf_ok tfibsegs B link_amf AMW_STK ly S W regs1 mem1).
    { pose proof Hbuf as (B0 & B1 & B2 & B3 & B4 & B5 & B6).
      split; [exact B0|]. split; [exact B1|]. split; [exact B2|]. split.
      { intros a Ha. destruct (B3 a Ha) as (W3 & O3 & _). split; [|split; [exact O3|]].
        - apply (writable_at_same (rd W mem) (rd W mem1) a); [|exact W3]. apply Hkept1; [lia | unfold fband; lia].
        - rewrite Hsp1. lia. }
      split; [exact B4|]. split.
      { intros x Hx. destruct (B5 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
        assert (Hq : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
        unfold shadow_of_addr in *. rewrite AV1; [exact Hs | unfold SHADOW_OFF; lia | unfold fband, SHADOW_OFF; lia]. }
      assert (L : (0 <=? shadow_addr (amf_buf link_amf) / 8 * 8) &&
                  (shadow_addr (amf_buf link_amf + amf_size link_amf - 1) / 8 * 8 + 8 <=? 2 ^ 40) = true)
        by reflexivity.
      apply andb_prop in L as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
      intros s Hs. rewrite AV1; [exact (B6 s Hs) | lia | unfold fband; lia]. }
    eapply SRr_bind.
    { apply (HFL ly S W regs1 mem1 md1 f k fl om wend wpos wbase pos len pb).
      - split; [exact HAR1|]. split; [rewrite R1; apply ret_ok_lit; [lia | reflexivity]|].
        split; [rewrite Hsp1; apply mod16_sub32; exact Bal|].
        rewrite Hsp1. split; [lia|]. split; [lia|]. split; [intros a Ha; apply Hband1; unfold fband; lia|].
        split; [rewrite (RK1 3%bv ltac:(cbv [KEEP In]; left; reflexivity)); exact Hgp|].
        rewrite (RK1 4%bv ltac:(cbv [KEEP In]; right; left; reflexivity)); exact Htp.
      - rewrite Hsp1. lia.
      - intros a Ha. apply Hband1. rewrite Hsp1 in Ha. unfold fband. lia.
      - exact R10.
      - exact R11.
      - exact R12.
      - exact Hblk.
      - exact Hk1.
      - exact Hdyn1.
      - exact Hpend1.
      - exact Hlen.
      - exact Hbuf1. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & HQ2). cbv zeta in HQ2.
    destruct HQ2 as (-> & HAR2 & HP2 & Hsb2 & R10b & Hk2 & Hpend2 & Haz2 & Hlt2 & Heq2 & Hkept2 & Hpr2 & Hwp2).
    rewrite Hsp1 in Hkept2.
    assert (FI2 : FI mem2 md2).
    { apply (FI_call mem1 md1 mem2 md2 (sp0 - 32 - AMW_STK) (sp0 - 32) (fun a => fhead a \/ fbuf a \/ ferr a)
        HFI1 HAR2 Hsb2); [lia | lia | | | exact Hpr2].
      - intros a Ha. exact Ha.
      - intros a Ha Nw Nx. cbv beta in Nx. apply Hkept2; [exact Ha | lia | intros C; apply Nx; left; exact C
          | intros C; apply Nx; right; left; exact C | intros C; apply Nx; right; right; exact C]. }
    assert (FR2 : Frame_ok mem2).
    { apply (Frame_kept mem1 mem2 HFr1). intros a Ha. apply Hkept2; [lia | lia | lia | lia | lia]. }
    assert (Hra1 : raZ regs1 = 0x96eec) by (unfold raZ; rewrite R1; reflexivity).
    rewrite Hra1.
    assert (S2 : getr regs2 2 = w64 (sp0 - 32)) by (rewrite (aregs_reg _ _ 2%bv HP2 (cs_of 2%bv eq_refl)); exact R2).
    assert (S8 : getr regs2 8 = w64 f) by (rewrite (aregs_reg _ _ 8%bv HP2 (cs_of 8%bv eq_refl)); exact R8).
    assert (S9 : getr regs2 9 = w64 0) by (rewrite (aregs_reg _ _ 9%bv HP2 (cs_of 9%bv eq_refl)); exact R9).
    assert (S18 : getr regs2 18 = w64 0) by (rewrite (aregs_reg _ _ 18%bv HP2 (cs_of 18%bv eq_refl)); exact R18).
    assert (SK2 : keep_regs regs regs2) by exact (keep_trans _ _ _ RK1 (keep_of_aregs _ _ HP2)).
    destruct (Z_lt_le_dec (amf_n1 link_amf k pos) k) as [Hn1 | Hn1].
    + (* n1 < k: return -1 *)
      pose proof (Hlt2 Hn1) as Hdyn2.
      pose proof Hdyn2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D40 & _).
      eapply SRr_mono; [apply (tail_B0 regs2 mem2 md2 FI2 FR2 S2 S8 SK2 D40)|].
      cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & FI3 & HP3 & R10c & ->).
      apply fs_post_of; try assumption.
      * intros _. split; [exact R10c | exact Hdyn2].
      * intros He. lia.
    + (* n1 = k: wpos = wbase, then mseek *)
      assert (Hn1e : amf_n1 link_amf k pos = k) by lia.
      assert (Hks : k <= 4096 - pos) by (unfold amf_n1 in Hn1e; rewrite Cs in Hn1e; lia).
      pose proof (Heq2 Hn1e) as Hdyn2.
      pose proof Hdyn2 as (Rfl2 & Rom2 & _ & _ & _ & Rpl2 & Rls2 & Dfl2 & Dom2 & _ & D40 & _ & Dpos2 & Dlen2).
      pose proof Hk2 as ((_ & _ & _ & (_ & S48 & _ & _ & S80 & _) & _) & _).
      rewrite Hwbe in D40.
      eapply SRr_bind; [apply (mid_B1 regs2 mem2 md2 FI2 FR2 S2 S8 S9 S18 SK2 D40 S48 S80)|].
      cbv beta. intros W3 c3 _ (-> & regsS & memS & mdS & -> & HQS).
      eapply SRr_mono; [apply (seek_tail mem2 regsS memS mdS fl (pos + k) (Z.max len (pos + k)) Hflv
        (proj1 Hk2) Dfl2 Dom2 Dpos2 Dlen2 Rpl2 Rls2 HQS)|].
      cbv beta. intros W4 c4 _ (-> & regs' & mem' & md' & -> & HFI' & HP' & R10' & Hk' & Hdyn' & Hkept').
      apply fs_post_of; try assumption.
      * apply (azbytes_kept (w_H W) mem2 mem'); [exact Hpend2|]. intros i Hi.
        apply Hkept'; [lia | unfold fband; lia | unfold fhead; unfold AMF_BUF in *; lia].
      * apply (azbytes_kept (w_H W) mem2 mem'); [exact Haz2|]. intros i Hi.
        rewrite length_firstn, Hn1e in Hi.
        apply Hkept'; [lia | unfold fband; lia |].
        unfold fhead. intros Hh. apply (fs_blk (amf_buf link_amf + pos + Z.of_nat i) ltac:(lia)).
        apply fs_in_img. lia.
      * intros Hlt. lia.
      * intros _. split; [exact R10' | exact Hdyn'].
Qed.

End M.

Theorem link_afseeko0 : afseeko0_mf_realizes tfibsegs B link_amf LA_FSEEKO.
Proof.
  intros ly S W regs mem md f k fl om wend wpos wbase pos len pb HPRE Hslo Hpres H10 H11 H12 Hblk Hk Hdyn Hpend Hlen
    Hbuf Hg1 Hg2.
  apply (fs_main ly S W regs mem md f k fl om wend wpos wbase pos len pb); assumption.
Qed.

End W.

About link_afseeko0.
Print Assumptions link_afseeko0.
