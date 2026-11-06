(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S32 FIN (0x8d71c .. 0x8d7b0) of the ASan+UBSan walk of verbs_receive
   on plugin-hostd/fuzz_command (image B), the statement vr_s32_stmt of lib/B/Prog/verbs_receive_iface.v: from the
   interface's vr_af (after the call after the reply) to the statement's post vr_final. The B twin of
   lib/A/Prog/verbs_receive_s32.v (A 0x8db50 .. 0x8dbe8), with its symbolic runs redone on B's instructions. The walk
   runs cgif_file_fuzzer's symbolic executor over the position-abstract listing: a state seeded at 0x8d71c from
   vr_core (vr32_seed: the copy c in the spill slot s1+48, which B reloads with `ld a0,48(s1)` where A kept it in s3;
   the caller's registers the prologue saved at sp0-8 .. sp0-104; the side-stack frame F, seen through s4 for the
   flag pointer at F+1016 and through s6 for the store F[0], and its shadow through s9), the two calls of the free
   wrapper (free(copy), free(line)) through afree04_rule (PaCall.afree04_sub), the store shadow(F)[76] := f8, the two
   shadow fills __asan_set_shadow_f8(shadow(F)+4, 64) and __asan_set_shadow_f5(shadow(F), 128) through
   RtShadow.aset_shadow_realizes and the journal rule written here (vr32_shadow_at: the fill stays inside the shadow
   of the frame the walk owns, composed by the core's ajournal_sub_wide), F[0] := 0x45e0360e (`sd a0,0(s6)`), the
   branch `beqz s4` (decided by the seeded fact F >= 4096; the __asan_set_shadow_00 arm at 0x8d768 is not taken), the
   flag release `*F[1016] := 0` (`ld a0,1016(s4)`; PaLibF.aj_flag_store_pi, own = [] after it), and the epilogue to
   the ret (paj_ret_at). The bytes the post reads (the real frame and the caller's stack, g_rec / record.spill /
   g_quitting, the recorder's blocks) are carried from 0x8d71c by vr32_keep; the message and the data block by the
   journal from the entry. The post's live-bytes bound comes from verbs_receive_live.vr_live_le at the return: the
   walk's own two blocks are freed (no temporary block is left) and the recorder holds at most three calls after one
   message (vr32_calls_le, from the plain proof's functional lemmas CrtVr.sp_step / sp_socket_send_m /
   sp_sup_after_reply_m). S32 calls no printf-reaching callee, so the post holds at the section's own FP state. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_live.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require CrtVr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the symbolic state at 0x8d71c (S32's entry, the interface's vr_af): registers as atoms; atom 32 is the flag
   address of the side-stack frame, atom 33 the copy c (B's spill slot s1+48), atoms 34..46 the caller's registers
   the prologue saved at sp0-8 .. sp0-104. B reaches the frame F through two registers, s4 (atom 20: the flag
   pointer at F+1016, the branch) and s6 (atom 22: the store F[0]), so the frame has one region per base, apart *)
Definition vr32_saves : list YP09.chunk :=
map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (34 + j) 0))) (seq 0 13).
Definition vr32_rs : smem :=
[YP09.mkRegion (Some 9%nat) 48 56 48 48 [YP09.mkChunk 48 (CVal 8 (SOff 33 0))];
 YP09.mkRegion (Some 8%nat) (-104) 0 (-104) (-104) vr32_saves;
 YP09.mkRegion (Some 20%nat) 1016 1024 1016 1016 [YP09.mkChunk 1016 (CVal 8 (SOff 32 0))];
 YP09.mkRegion (Some 22%nat) 0 8 0 8 [];
 YP09.mkRegion (Some 25%nat) 0 128 76 77 []].
Definition vr32_facts : facts := mkFacts [(20%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition ss32 : sstate := mkSS (AF_verbs_receive + 0x8d0) sr_atoms vr32_rs None vr32_facts.
(* the flag byte's region, added before the release *)
Definition vr32_rflag : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
(* the write windows of a state: in the side-stack frame (atoms 20 and 22), its shadow (atom 25) or the flag
   (atom 32) *)
Definition vr32_win_ok (fl : bool) (t : option nat * Z * Z) : bool :=
let '(b, lo, hi) := t in
(hi <=? lo) ||
match b with
| Some m =>
  if Nat.eqb m 20 then (0 <=? lo) && (hi <=? 1024)
  else if Nat.eqb m 22 then (0 <=? lo) && (hi <=? 1024)
  else if Nat.eqb m 25 then (0 <=? lo) && (hi <=? 128)
  else if Nat.eqb m 32 then fl && (lo =? 0) && (hi =? 1)
  else false
| None => false
end.

Lemma vr32_fs4 : fs_frame_bytes 4 = 1024. Proof. reflexivity. Qed.

(* the recorder after one message from an empty call table: the handler records at most two calls, the reply none,
   the call after the reply one *)
Lemma vr32_calls_le : forall R D, r_calls R = [] -> (length (r_calls (vr_R3 R D)) <= 3)%nat.
Proof.
intros R D H0.
assert (H : CrtVr.sp_keep R R 0) by (split; [reflexivity | rewrite H0; cbn [length]; lia]).
assert (H1 : CrtVr.sp_keep R (vr_R1 R D) 2) by (unfold vr_R1, vr_h; exact (CrtVr.sp_step _ R R 0 (vr_st D) H ltac:(lia))).
assert (H2 : CrtVr.sp_keep R (vr_R2 R D) 2)
  by exact (CrtVr.sp_socket_send_m R (vr_R1 R D) 2 (vr_x R D ++ [Z_to_bv 8 0]) H1).
unfold vr_R3. destruct (vr_aft D) as [[i v]|].
- exact (proj2 (CrtVr.sp_sup_after_reply_m R (vr_R2 R D) 2 i (Some v) H2 ltac:(lia))).
- pose proof (proj2 H2) as L. cbv beta in L. lia.
Qed.
(* vr_live_le's bound at no temporary block and at most three recorded calls is within the statement's budget *)
Lemma vr32_live_le : forall bS bS' (x : nat), (x <= 3)%nat ->
bS' <= bS + (6 * Z.of_nat x + 8) * (LMAX + 2) + bsum [] -> bS' <= bS + LIVE_VERBS_RECEIVE.
Proof.
intros bS bS' x Hx H. change (bsum []) with 0 in H. unfold LMAX in H.
unfold LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the shadow of the side-stack frame lies between the low and the high application ranges, apart from the frame *)
Lemma vr32_shF : forall F, 4096 <= F -> F + 1024 <= alloc_ceiling -> in_app F 1024 ->
0x7fff8000 <= shadow_addr F /\ shadow_addr F + 128 <= 0x10007fff8000 /\ (F + 1024 <= shadow_addr F \/ shadow_addr F + 128 <= F).
Proof.
intros F H1 H2 H3. pose proof (proj1 alloc_ceiling_val) as C1.
unfold shadow_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in H3.
pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)). lia.
Qed.
Lemma vr32_app_shF : forall F p n a, 4096 <= F -> F + 1024 <= alloc_ceiling -> in_app F 1024 -> in_app p n -> p <= a < p + n ->
~ (shadow_addr F <= a < shadow_addr F + 128).
Proof.
intros F p n a H1 H2 H3 H4 Ha. pose proof (vr32_shF F H1 H2 H3) as (S1 & S2 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in H4. lia.
Qed.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the n-byte value of a reader that is aview is the value of the restricted memory *)
Lemma vr32_val_mem_of_aval : forall H mem a n v,
aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte SEGS H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.

(* the journal of a shadow-fill entry that writes [q, q + n) inside the shadow of a frame of the state: nothing else
   changes, so it is a journal with footprint [q, q + n), no event and no frame *)
Lemma vr32_shadow_inner : forall stk lyc Sc W regs memc mdc mem2 md2 q n cid pos,
AR SEGS B lyc Sc W memc mdc -> AR SEGS B lyc Sc W mem2 md2 -> same_but_materialized mdc md2 ->
astk_ok stk lyc (spZ regs) -> qtight Sc -> In (cid, pos) (frames Sc) ->
shadow_addr (frame_addr lyc cid pos) <= q -> q + n <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) ->
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W) mem2 a) ->
ajournal SEGS B stk (spZ regs) [(q, q + n)] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0.
Proof.
intros stk lyc Sc W regs memc mdc mem2 md2 q n cid pos HAR HAR2 Hsame Hstk HQT Hin Hq1 Hq2 Hout Hp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & Hfh).
assert (Hnf : forall a, ~ inFP [(q, q + n)] a -> ~ (q <= a < q + n)).
{ intros a Hn Ha. apply Hn. exists (q, q + n). split; [left; reflexivity | cbn; lia]. }
unfold ajournal.
split; [exact HAR2|].
split; [apply layout_le_refl|].
split; [lia|].
split; [apply wle_refl|].
split; [eapply aos_step_same_io; [apply aos_step_refl | apply same_io_materialized; exact Hsame]|].
split; [reflexivity|].
split; [lia|]. split; [lia|].
split; [intros a Ha _ Hn; apply Hout; [lia | exact (Hnf a Hn)]|].
split.
{ intros p m i H1 _ Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc p m HAR H1) as (_ & Hp4 & Hpc & _).
  apply Hout; [lia | exact (Hnf _ Hn)]. }
split; [intros a Hi _ _ Hsp; apply Hout; [pose proof (pa_segs_low a Hi); lia | exact (Hnf a (fp_spares_nf _ _ Hsp))]|].
split.
{ intros cid' pos' a Hin' Hr Hn. apply Hout; [|exact (Hnf a Hn)].
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid' pos' HAR Hin') as (Hg0 & Hgc & Hgh).
  pose proof (fs_frame_bytes_nonneg cid').
  pose proof (shadow_addr_bounds (frame_addr lyc cid' pos') ltac:(lia)).
  pose proof (shadow_addr_bounds (frame_addr lyc cid' pos' + fs_frame_bytes cid') ltac:(lia)).
  pose proof (shadow_range_end (frame_addr lyc cid' pos') (fs_frame_bytes cid') (fs_frame_bytes_nonneg cid')).
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. lia. }
split; [intros p m i H1 H2; exfalso; exact (H2 H1)|].
split; [exact Hp|].
split; [exact Hstk|].
split.
{ intros a HXa _. pose proof (YG0p.AR_extra_law_ok SEGS B lyc Sc W memc mdc a HAR HXa) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
  apply Hout; [unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; pose proof (proj1 (@YG0f.ASAN_CEIL_range _)); lia|].
  intros Hqa. apply (proj2 (Xf cid pos Hin)). lia. }
exact HQT.
Qed.

(* a call of a shadow-fill entry (RtShadow.aset_shadow_realizes) as a step under the walk's journal: the fill lies in
   the shadow of a frame the walk owns *)
Lemma vr32_shadow_at : forall pc v, RtShadow.aset_shadow_realizes SEGS B pc v ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n (o : Z) raw,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
In (cid, pos) own ->
getr regsT 10 = w64 q -> getr regsT 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr lyc cid pos) <= q -> q + n <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros pc v HSR W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n o raw
HJ Hown H10 H11 Hn Hq1 Hq2 Hsp Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds SEGS B LAWS lyc Sc W memT mdc cid pos HAR Hin) as (Hf0 & Hfc & Hfh).
pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hsb.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp, Eslo, Eshi, Etop. repeat split; try lia.
  all: rewrite Z.add_mod, Hal16, Hal by lia; reflexivity. }
eapply SRr_mono; [exact (HSR lyc Sc W regsT memT mdc cid pos q n HPRE Hin H10 H11 Hn Hq1 Hq2)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hfill & Hout & Hp2).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ, w64; rewrite Hra, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ pose proof (vr32_shadow_inner ESTACK lyc Sc W regsT memT mdc mem2 md2 q n cid pos HAR HAR2 Hsame HstkC HQT Hin Hq1 Hq2 Hout Hp2) as HJ1.
  rewrite Hsp in HJ1.
  pose proof (ajournal_sub_wide SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ESTACK (sp0 + o)
    [(q, q + n)] [] lyc Sc W mem2 md2 0 HJ HJ1 ltac:(lia) ltac:(lia)) as HJ2.
  rewrite app_nil_l, Z.add_0_r in HJ2. apply HJ2.
  - intros a (r & [<- | []] & Ha). cbn [fst snd] in Ha. right; right; right; left.
    exists cid, pos. split; [exact Hown | right; unfold in_zr; cbn [fst snd]; lia].
  - intros a (r & [<- | []] & Ha) Hw _. cbn [fst snd] in Ha. exfalso. lia. }
split; [exact HP | exact Hout].
Qed.

(* the write windows of the walk's states are in the frame the walk owns (through s4 or s6), in its shadow, or the
   flag byte *)
Lemma vr32_win_cases : forall fl E rs a, forallb (vr32_win_ok fl) (windows rs) = true -> in_wrange E rs a ->
(bv_unsigned (ew E 20) <= a < bv_unsigned (ew E 20) + 1024) \/ (bv_unsigned (ew E 22) <= a < bv_unsigned (ew E 22) + 1024) \/
(bv_unsigned (ew E 25) <= a < bv_unsigned (ew E 25) + 128) \/ (fl = true /\ a = bv_unsigned (ew E 32)).
Proof.
intros fl E rs a Hw (r & Hin & Ha).
assert (Hr : vr32_win_ok fl (r_base r, r_wlo r, r_whi r) = true).
{ rewrite forallb_forall in Hw. apply Hw. unfold windows. apply in_map_iff. exists r. split; [reflexivity | exact Hin]. }
unfold vr32_win_ok in Hr. apply Bool.orb_true_iff in Hr as [Hr | Hr]; [apply Z.leb_le in Hr; lia|].
destruct (r_base r) as [m|]; [|discriminate Hr]. cbn [base_val] in Ha.
destruct (Nat.eqb_spec m 20) as [->|_].
{ apply andb_true_iff in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. left. lia. }
destruct (Nat.eqb_spec m 22) as [->|_].
{ apply andb_true_iff in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. right; left. lia. }
destruct (Nat.eqb_spec m 25) as [->|_].
{ apply andb_true_iff in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. right; right; left. lia. }
destruct (Nat.eqb_spec m 32) as [->|_]; [|discriminate Hr].
apply andb_true_iff in Hr as [Hr H2]. apply andb_true_iff in Hr as [H0 H1]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
right; right; right. split; [exact H0 | lia].
Qed.
Lemma vr32_in_own : forall STK sp0 FP bl0 blc fr0 lyc pos a,
(frame_addr lyc 4 pos <= a < frame_addr lyc 4 pos + 1024) \/
(shadow_addr (frame_addr lyc 4 pos) <= a < shadow_addr (frame_addr lyc 4 pos) + 128) ->
awr_byte SEGS B STK sp0 FP bl0 blc fr0 lyc [(4, pos)] a.
Proof.
intros STK sp0 FP bl0 blc fr0 lyc pos a Ha. right; right; right; left.
exists 4, pos. split; [left; reflexivity|]. unfold in_zr. cbn [fst snd]. rewrite vr32_fs4. change (1024 / 8) with 128. exact Ha.
Qed.
Lemma vr32_awr : forall E rs STK sp0 FP bl0 blc fr0 lyc pos,
bv_unsigned (ew E 20) = frame_addr lyc 4 pos -> bv_unsigned (ew E 22) = frame_addr lyc 4 pos ->
bv_unsigned (ew E 25) = shadow_addr (frame_addr lyc 4 pos) ->
forallb (vr32_win_ok false) (windows rs) = true ->
awr_ok SEGS B E rs STK sp0 FP bl0 blc fr0 lyc [(4, pos)].
Proof.
intros E rs STK sp0 FP bl0 blc fr0 lyc pos H20 H22 H25 Hw a Ha. apply vr32_in_own.
destruct (vr32_win_cases false E rs a Hw Ha) as [H | [H | [H | [H _]]]]; [left; lia | left; lia | right; lia | discriminate H].
Qed.
Lemma vr32_awr_flag : forall E rs STK sp0 FP bl0 blc fr0 lyc pos,
bv_unsigned (ew E 20) = frame_addr lyc 4 pos -> bv_unsigned (ew E 22) = frame_addr lyc 4 pos ->
bv_unsigned (ew E 25) = shadow_addr (frame_addr lyc 4 pos) ->
bv_unsigned (ew E 32) = flag_addr lyc 4 pos ->
forallb (vr32_win_ok true) (windows rs) = true ->
forall a, in_wrange E rs a -> awr_byte SEGS B STK sp0 FP bl0 blc fr0 lyc [(4, pos)] a \/ a = flag_addr lyc 4 pos.
Proof.
intros E rs STK sp0 FP bl0 blc fr0 lyc pos H20 H22 H25 H32 Hw a Ha.
destruct (vr32_win_cases true E rs a Hw Ha) as [H | [H | [H | [_ H]]]];
  [left; apply vr32_in_own; left; lia | left; apply vr32_in_own; left; lia | left; apply vr32_in_own; right; lia | right; lia].
Qed.

(* the bytes the walk's own stores reach: the side-stack frame, its shadow, the flag byte *)
Definition vr32_zone (F FL a : Z) : Prop := (F <= a < F + 1024) \/ (shadow_addr F <= a < shadow_addr F + 128) \/ a = FL.

Lemma vr32_chunk8 : forall E mem base off e v,
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem SEGS mem (base + off) 8 v ->
YP09.chunk_ok SEGS E mem base (YP09.mkChunk off (CVal 8 e)).
Proof.
intros E mem base off e v He Hv Hm. apply (chunk_ok_val SEGS E mem base off 8 e v He); [exact Hv | cbn; lia | exact Hm].
Qed.

Lemma vr32_seed : forall (W : world SEGS) (regsc : bvmap 5 word) memc (ext : list word) s1 sp0 F FL c,
bv_unsigned (getr regsc 9) = s1 -> bv_unsigned (getr regsc 8) = sp0 -> bv_unsigned (getr regsc 20) = F ->
bv_unsigned (getr regsc 22) = F -> bv_unsigned (getr regsc 25) = shadow_addr F ->
nth 0 ext (Z_to_bv 64 0) = Z_to_bv 64 FL -> 0 <= FL < 2 ^ 64 -> nth 1 ext (Z_to_bv 64 0) = Z_to_bv 64 c -> 0 <= c < 2 ^ 64 ->
alloc_ceiling <= s1 -> s1 + 192 <= sp0 -> sp0 <= 2 ^ 47 ->
4096 <= F -> F mod 32 = 0 -> F + 1024 <= alloc_ceiling -> in_app F 1024 ->
(forall o, 0 <= o < 8 -> apresent (w_H W) memc (F + o)) ->
apresent (w_H W) memc (shadow_addr F + 76) ->
val_mem SEGS (mrestrict (w_H W) memc) (s1 + 48) 8 c ->
val_mem SEGS (mrestrict (w_H W) memc) (F + 1016) 8 FL ->
(forall j, (j < 13)%nat -> val_mem SEGS (mrestrict (w_H W) memc) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (nth (S (S j)) ext (Z_to_bv 64 0)))) ->
st_ok_pi SEGS VAL (Eimg (Ereg regsc ext)) ss32
  (mkst regsc (Z_to_bv 64 (BASE + (AF_verbs_receive + 0x8d0))) (mrestrict (w_H W) memc) (seg_rom SEGS)).
Proof.
intros W regsc memc ext s1 sp0 F FL c H9 H8 H20 H22 H25 Hfl Hfl64 Hc Hc64 Hs1c Hs1 Hsp47 HF4 HF32 HFc HFapp HFp HSp V48 V1016 VS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg regsc ext)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j ext (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by exact Hj; apply ew_Ereg_extra).
assert (B9 : base_val E (Some 9%nat) = s1) by (cbn [base_val]; rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (B8 : base_val E (Some 8%nat) = sp0) by (cbn [base_val]; rewrite (EE 8%nat 8%bv eq_refl); exact H8).
assert (B20 : base_val E (Some 20%nat) = F) by (cbn [base_val]; rewrite (EE 20%nat 20%bv eq_refl); exact H20).
assert (B22 : base_val E (Some 22%nat) = F) by (cbn [base_val]; rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (B25 : base_val E (Some 25%nat) = shadow_addr F) by (cbn [base_val]; rewrite (EE 25%nat 25%bv eq_refl); exact H25).
assert (X0 : ew E 32 = Z_to_bv 64 FL) by (rewrite <- Hfl; exact (EX 0%nat ltac:(cbv; lia))).
assert (B32 : bv_unsigned (ew E 32) = FL) by (rewrite X0; apply unsigned_lit_small; lia).
assert (X1 : ew E 33 = Z_to_bv 64 c) by (rewrite <- Hc; exact (EX 1%nat ltac:(cbv; lia))).
assert (B33 : bv_unsigned (ew E 33) = c) by (rewrite X1; apply unsigned_lit_small; lia).
pose proof (vr32_shF F HF4 HFc HFapp) as (SH1 & SH2 & SH3).
unfold ss32. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold vr32_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (vr32_chunk8 E _ s1 48 (SOff 33 0) c); [cbn [sv_denot]; rewrite B33, Z.add_0_r; reflexivity | lia | exact V48].
  + rewrite B8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    unfold vr32_saves. apply Forall_forall. intros chk Hch. apply in_map_iff in Hch as (j & <- & Hj). apply in_seq in Hj.
    apply (vr32_chunk8 E _ sp0 (-8 - 8 * Z.of_nat j) (SOff (34 + j) 0) (bv_unsigned (nth (S (S j)) ext (Z_to_bv 64 0)))).
    * cbn [sv_denot]. replace (34 + j)%nat with (32 + S (S j))%nat by lia. rewrite (EX (S (S j))) by (cbv [A_TEXT]; lia).
      rewrite Z.add_0_r. reflexivity.
    * pose proof (bv_unsigned_in_range 64 (nth (S (S j)) ext (Z_to_bv 64 0))) as HR. change (bv_modulus 64) with (2 ^ 64) in HR. exact HR.
    * replace (sp0 + (-8 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia. apply VS. lia.
  + rewrite B20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (vr32_chunk8 E _ F 1016 (SOff 32 0) FL); [cbn [sv_denot]; rewrite B32, Z.add_0_r; reflexivity | lia | exact V1016].
  + rewrite B22. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply HFp; lia | apply Forall_nil].
  + rewrite B25. split; [lia|]. split; [lia|].
    split; [intros o Ho; replace o with 76 by lia; apply (apresent_writable SEGS); exact HSp | apply Forall_nil].
- apply pairwise_disjoint_of_extents. unfold vr32_rs, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B9, B8, B20, B22, B25.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; exact I]. cbn [vr32_facts f_atoms atoms_ok]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (EE 20%nat 20%bv eq_refl), H20. change (2 ^ 5) with 32. lia.
Qed.

(* the frame chain at a call of the walk: s0 = sp0 holds the caller's frame record at sp0 - 8 / sp0 - 16 *)
Lemma vr32_chain : forall ly lyc (rd0 rd : reader) sp0 v ra ch0 (regsT : bvmap 5 word) s1,
achain ly rd0 sp0 v ch0 -> ly_top lyc = ly_top ly -> ly_top ly <= 2 ^ 64 ->
(forall a, sp0 <= a < 2 ^ 64 -> rd a = rd0 a) ->
rdword rd (sp0 - 8) = Some ra -> rdword rd (sp0 - 16) = Some v -> 4096 <= ra ->
alloc_ceiling <= sp0 -> sp0 mod 8 = 0 -> spZ regsT = s1 -> alloc_ceiling <= s1 -> s1 + 16 <= sp0 ->
s0Z regsT = sp0 -> 4096 <= raZ regsT ->
exists ch, chain_pre lyc rd regsT ch.
Proof.
intros ly lyc rd0 rd sp0 v ra ch0 regsT s1 Hc Etop Htop Hk H8 H16 Hra Hceil Hal Hsp Hs1 Hs16 Hs0 Hra4.
destruct (Z_lt_le_dec sp0 (ly_top ly - 16)) as [Hlt | Hge].
- exists ((sp0, ra, v) :: ch0). apply (achain_chain_pre lyc rd s1 sp0 _ regsT); [| lia | exact Hs0 | exact Hra4].
  apply (achain_ly_top ly lyc); [exact Etop|].
  apply (achain_push ly rd0 rd sp0 v ra ch0 s1 Hc Htop Hk H8 H16 Hra Hceil Hal Hlt). lia.
- exists []. apply (achain_chain_pre lyc rd s1 sp0 [] regsT); [| lia | exact Hs0 | exact Hra4].
  left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.

(* a run's stores lie in its write windows, all in the zone *)
Lemma vr32_kept_run : forall fl E rs H (m m' : word -> option byte) F FL,
bv_unsigned (ew E 20) = F -> bv_unsigned (ew E 22) = F -> bv_unsigned (ew E 25) = shadow_addr F ->
(fl = true -> bv_unsigned (ew E 32) = FL) ->
forallb (vr32_win_ok fl) (windows rs) = true ->
frame_of E rs (mrestrict H m) (mrestrict H m') ->
forall a, 0 <= a < 2 ^ 64 -> ~ vr32_zone F FL a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros fl E rs H m m' F FL H20 H22 H25 H32 Hw HFr.
apply (kept_of_frame (segs := SEGS) E rs H m m' (vr32_zone F FL) HFr).
intros b wlo whi a Hin Ha. unfold windows in Hin. apply in_map_iff in Hin as (r & Er & Hr).
injection Er as <- <- <-.
assert (Hwr : in_wrange E rs a) by (exists r; split; [exact Hr | exact Ha]).
destruct (vr32_win_cases fl E rs a Hw Hwr)
  as [Hz | [Hz | [Hz | [Hfl Hz]]]]; unfold vr32_zone;
  [left; lia | left; lia | right; left; lia | right; right; rewrite (H32 Hfl) in Hz; exact Hz].
Qed.


Lemma vr32_nodup_app : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
induction l1 as [|y l1 IH]; intros l2 x Hnd H1 H2; [destruct H1|]. inversion Hnd; subst.
destruct H1 as [<- | H1]; [apply H3; apply in_or_app; right; exact H2 | exact (IH l2 x H4 H1 H2)].
Qed.
(* the layout's frame base is fixed along the journal *)
Lemma vr32_frame_addr : forall ly ly' cid pos, ly_F ly' = ly_F ly -> frame_addr ly' cid pos = frame_addr ly cid pos /\ flag_addr ly' cid pos = flag_addr ly cid pos.
Proof. intros ly ly' cid pos E. unfold frame_addr, flag_addr. rewrite E. split; reflexivity. Qed.

(* a region whose bytes and write window survive a step *)
Lemma vr32_rk : forall E (Wa Wb : world SEGS) ma mb (r : YP09.region),
(forall a, base_val E (r_base r) + r_lo r <= a < base_val E (r_base r) + r_hi r ->
  aview SEGS (w_H Wb) mb a = aview SEGS (w_H Wa) ma a) ->
(forall a, base_val E (r_base r) + r_wlo r <= a < base_val E (r_base r) + r_whi r -> apresent (w_H Wb) mb a) ->
region_kept SEGS E (mrestrict (w_H Wa) ma) (mrestrict (w_H Wb) mb) r.
Proof.
intros E Wa Wb ma mb r H1 H2. split.
- intros a Ha. apply (mbyte_of_aview SEGS). apply H1. exact Ha.
- intros a Ha _. apply (apresent_writable SEGS). apply H2. exact Ha.
Qed.

(* the bytes S32 keeps from 0x8db50 to the return: the real frame and the caller's stack, the program's statics,
   and the recorder's blocks *)
Definition vr32_keep (s1 : Z) (O3 : list (Z * Z)) (a : Z) : Prop :=
s1 <= a \/ inFP cmd_PG a \/ exists p m, In (p, m) O3 /\ p <= a < p + req_size m.

Lemma vr32_kp_free : forall lyc Sc (Wa Wb : world SEGS) ma mb mda slo s1 x nx O3,
acall_kept SEGS B lyc Sc Wa ma Wb mb slo s1 (fun a => x <= a < x + req_size nx) ->
AR SEGS B lyc Sc Wa ma mda -> (forall pn, In pn O3 -> In pn (ablocks B lyc Sc)) -> ~ In (x, nx) O3 ->
In (x, nx) (ablocks B lyc Sc) -> vr_prog_unowned B -> alloc_ceiling <= s1 ->
forall a, 0 <= a < 2 ^ 64 -> vr32_keep s1 O3 a -> aview SEGS (w_H Wb) mb a = aview SEGS (w_H Wa) ma a.
Proof.
intros lyc Sc Wa Wb ma mb mda slo s1 x nx O3 (K1 & K2 & K3 & _) HAR HO3 HxO Hx PU Hs1 a Ha [Hk | [Hk | (p & m & Hpm & Hk)]].
- apply K1; lia.
- destruct (PU a Hk) as (Hi & Ho & He). exact (K3 a Hi Ho He).
- replace a with (p + (a - p)) by lia. apply (K2 p m); [exact (HO3 _ Hpm) | lia |].
  assert (Hne : (p, m) <> (x, nx)) by (intros E; rewrite E in Hpm; exact (HxO Hpm)).
  pose proof (sep_blocks SEGS B LAWS lyc Sc Wa ma mda p m x nx HAR (HO3 _ Hpm) Hx Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* the runtime entries S32 calls, fx-generic as verbs_receive_c.v states them, and the per-binary facts: TL (the free
   wrapper's listing address is the record's, CmdRecRest.cmd_palib at the pinned image), the model and meter laws,
   and the record fact vr_prog_unowned *)
Hypothesis AFREE : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis SHF5 : forall fx0 : YK11.FPState, @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIGMA CS___asan_set_shadow_f5) 0xf5.
Hypothesis SHF8 : forall fx0 : YK11.FPState, @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIGMA CS___asan_set_shadow_f8) 0xf8.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis PROGU : vr_prog_unowned B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Let RET := paj_ret_at (L := cmd_listing) (PI := PI).

(* the meter at a call of the free wrapper (no malloc, one free, one event): the call is allowed while the route's
   events cover it (the interface's vri_meter_ok), and vr_meter counts it one event later (vri_meter_step); the meter
   reasoning of S32's two frees lives in these two lemmas only *)
Lemma vr32_meter_free_ok : forall e Sc k nm, vr_ent B MT e -> vr_meter MT e Sc k nm ->
k + 1 <= ev_vr (e_R e) (e_D e) -> mo_ok MT Sc (mo_free MT).
Proof.
intros e Sc k nm He Hm Hk.
exact (vri_meter_ok B MT e Sc k nm (mo_free MT) 0 1 1 MTL He Hm ltac:(lia) ltac:(lia) ltac:(lia) Hk).
Qed.
Lemma vr32_meter_free : forall e Sc S2 k nm, vr_meter MT e Sc k nm -> mo_le MT Sc S2 (mo_free MT) ->
vr_meter MT e S2 (k + 1) nm.
Proof.
intros e Sc S2 k nm Hm H2.
pose proof (vri_meter_step MT e Sc S2 k nm (mo_free MT) 0 1 1 MTL Hm H2 ltac:(lia) ltac:(lia) ltac:(lia)) as H.
rewrite Z.add_0_r in H. exact H.
Qed.

Lemma vr_s32 : vr_s32_stmt B MT.
Proof.
intros e W cf HE HAF. pose proof HE as HENT.
unfold vr_ent in HE. cbv zeta in HE.
destruct HE as (HPRE & HROD & H10 & HMSG & HFD & HDATA & HNV & HnR & HDl & HDin & HDnO & HDb & _ & HRE0 & HRC0 & _ & _ & _ & _ &
  HPE & HQ0 & _ & _ & _ & _ & _ & _ & _ & _ & HNEV & _ & HMOK & _).
destruct HAF as (O3 & pos & F & q & c & lyc & Sc & regsc & memc & mdc & k & nm & -> & HC & Hfq & Hfc).
destruct HC as (HJ & Hk & HMET & Hnm & HFR & HRV & HSAV & HSPL & HENV & HREC & HnO3 & HPERM & HQV).
unfold vr_rv, vr_base, vr_rl_af in HRV. cbn [app] in HRV.
repeat (let H := fresh "RV" in apply Forall_cons_iff in HRV as [H HRV]; cbn [fst snd] in H).
destruct HFR as (EF & HFL1016 & _).
set (sp0 := vr_sp0 e) in *. set (s1 := vr_s1 e) in *. set (FL := flag_addr lyc 4 pos) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk0 & JF1 & JF2 & JF3 & JF4 & Hgone & Hpres & Hstatic & JF5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (HSTK : 16384 + 208 <= VERBS_RECEIVE_STK) by (unfold VERBS_RECEIVE_STK, ASTACK; lia).
assert (Hs1 : s1 = sp0 - 192 \/ s1 = sp0 - 208).
{ subst s1. unfold vr_s1. fold sp0. pose proof (Z.div_mod (sp0 - 192) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (sp0 - 192) 32 ltac:(lia)).
  pose proof (Z.div_mod sp0 16 ltac:(lia)). lia. }
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF4096 & HFceil & _).
destruct (FFL lyc Sc W memc mdc 4 pos HAR Hin4) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
rewrite <- EF in HFal, HFapp, HFpres, HFSpres, HF4096, HFceil. rewrite vr32_fs4 in *. change (1024 / 8) with 128 in HFSpres.
fold FL in HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLc.

(* the registers at 0x8d71c: s2 = q, s4 = s6 = F, s9 = shadow(F), s11 = shadow(F) + 4 (vr_rl_af); c is in s1+48 *)
assert (R2c : getr regsc 2 = w64 s1) by exact RV. assert (R3c : getr regsc 3 = w64 (as_gp B)) by exact RV0.
assert (R4c : getr regsc 4 = w64 (as_tp B)) by exact RV1. assert (R8c : getr regsc 8 = w64 sp0) by exact RV2.
assert (R9c : getr regsc 9 = w64 s1) by exact RV3. assert (R18c : getr regsc 18 = w64 q) by exact RV4.
assert (R20c : getr regsc 20 = w64 F) by exact RV5. assert (R22c : getr regsc 22 = w64 F) by exact RV6.
assert (R25c : getr regsc 25 = w64 (shadow_addr F)) by exact RV7. assert (R27c : getr regsc 27 = w64 (shadow_addr F + 4)) by exact RV8.
clear RV RV0 RV1 RV2 RV3 RV4 RV5 RV6 RV7 RV8 HRV.
pose proof HPRE as (HARe & Hrae & Hra4e & Hgpe & Htpe & Hstke & Hprese & Hche & HQTe).
pose proof Hly as (_ & _ & _ & _ & _ & ElyF & _ & _ & Etop & Eslo & Eshi & _).
assert (Hsp0 : sp0 = spZ (e_regs e)) by reflexivity.
assert (Hs1c : alloc_ceiling <= s1) by lia.
assert (Hs1sp : s1 + 192 <= sp0) by lia.
assert (Hsp47 : sp0 <= 2 ^ 47) by lia.
pose proof (vr32_shF F HF4096 HFceil HFapp) as (SH1 & SH2 & SH3).
assert (U9 : bv_unsigned (getr regsc 9) = s1) by (rewrite R9c; unfold w64; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (getr regsc 8) = sp0) by (rewrite R8c; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (getr regsc 20) = F) by (rewrite R20c; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (getr regsc 22) = F) by (rewrite R22c; unfold w64; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (getr regsc 25) = shadow_addr F) by (rewrite R25c; unfold w64; apply unsigned_lit_small; lia).
(* the copy block: a live block of the state, so 4096 <= c < alloc_ceiling *)
assert (Hcb0 : In (c, Z.of_nat (length (Verbs.line (e_D e))) + 1) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb0) as (_ & Hc4 & Hcc & _ & _ & _ & Hcn).
pose proof (req_size_pos _ (proj1 Hcn)) as [Hcr _].
assert (Hc64 : 0 <= c < 2 ^ 64) by lia.
clear Hcb0 Hc4 Hcc Hcn Hcr.
set (ext := Z_to_bv 64 FL :: Z_to_bv 64 c :: map (fun r => getr (e_regs e) (Z_to_bv 5 r)) vr_saved_regs).
assert (VS : forall j, (j < 13)%nat -> val_mem SEGS (mrestrict (w_H W) memc) (sp0 - 8 - 8 * Z.of_nat j) 8
  (bv_unsigned (nth (S (S j)) ext (Z_to_bv 64 0)))).
{ intros j Hj. apply vr32_val_mem_of_aval.
  assert (Hn : nth_error vr_saved_regs j = Some (nth j vr_saved_regs 0)) by (apply nth_error_nth'; cbn; lia).
  pose proof (HSAV j _ Hn) as Hv. unfold ext. cbn [nth].
  rewrite (nth_indep (map (fun r => getr (e_regs e) (Z_to_bv 5 r)) vr_saved_regs) (Z_to_bv 64 0) (getr (e_regs e) (Z_to_bv 5 0)))
    by (rewrite length_map; cbn; lia).
  rewrite (map_nth (fun r => getr (e_regs e) (Z_to_bv 5 r))). exact Hv. }
assert (V48 : val_mem SEGS (mrestrict (w_H W) memc) (s1 + 48) 8 c).
{ apply vr32_val_mem_of_aval. unfold vr_spill in HSPL. apply Forall_inv in HSPL. exact HSPL. }
pose proof (val_mem_of_rdword SEGS (w_H W) memc (F + 1016) FL HFL1016) as V1016.
assert (HFL64 : 0 <= FL < 2 ^ 64) by lia.
pose proof (vr32_seed W regsc memc ext s1 sp0 F FL c U9 U8 U20 U22 U25 eq_refl HFL64 eq_refl Hc64 Hs1c Hs1sp Hsp47 HF4096 HFal
  HFceil HFapp (fun o Ho => proj1 (HFpres (F + o) ltac:(lia))) (proj1 (HFSpres 76 ltac:(lia))) V48 V1016 VS) as HS.
remember (Eimg (Ereg regsc ext)) as E eqn:HE in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j ext (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by exact Hj; apply ew_Ereg_extra).
clear HE.
assert (UE20 : bv_unsigned (ew E 20) = F) by (rewrite (EE 20%nat 20%bv eq_refl); exact U20).
assert (UE22 : bv_unsigned (ew E 22) = F) by (rewrite (EE 22%nat 22%bv eq_refl); exact U22).
assert (UE25 : bv_unsigned (ew E 25) = shadow_addr F) by (rewrite (EE 25%nat 25%bv eq_refl); exact U25).
assert (UE32 : bv_unsigned (ew E 32) = FL) by (pose proof (EX 0%nat ltac:(cbv; lia)) as X0; cbn [Nat.add] in X0; rewrite X0; cbn [nth ext]; apply unsigned_lit_small; lia).
assert (XE33 : ew E 33 = w64 c) by (pose proof (EX 1%nat ltac:(cbv; lia)) as X1; cbn [Nat.add] in X1; rewrite X1; reflexivity).
rewrite <- restrict_mkst_fx in HS.
unfold cfg_at, vr_pc. change (w64 (BASE + (AF_verbs_receive + (0x8d71c - 0x8ce4c)))) with (Z_to_bv 64 (BASE + (AF_verbs_receive + 0x8d0))).
(* 0x8d71c .. 0x8d720: a0 = the copy, reloaded from s1+48; the call of the free wrapper *)
paj_run_shc RUNP RUNC HS HJ.
{ apply vr32_awr; [rewrite UE20; exact EF | rewrite UE22; exact EF | rewrite UE25, EF; reflexivity | vm_compute; reflexivity]. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md1 := m) in *; clearbody md1 end.
assert (UE9 : bv_unsigned (ew E 9) = s1) by (rewrite (EE 9%nat 9%bv eq_refl); exact U9).
assert (UE8 : bv_unsigned (ew E 8) = sp0) by (rewrite (EE 8%nat 8%bv eq_refl); exact U8).
assert (Ho16 : (s1 - sp0) mod 16 = 0)
  by (destruct Hs1 as [Es | Es]; rewrite Es; [replace (sp0 - 192 - sp0) with (-192) by lia | replace (sp0 - 208 - sp0) with (-208) by lia]; reflexivity).
assert (Hsp8 : sp0 mod 8 = 0).
{ apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [t Ht]. apply Z.mod_divide; [lia|]. exists (2 * t). lia. }
pose proof pa_B_ok as HBASE.
assert (HO3 : forall pn, In pn O3 -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; left; exact Hpn).

set (lb := vr_lb e q) in *. set (cb := vr_cb e c) in *.
pose proof (RecBLemmas.recb_ablocks_nodup_m B lyc Sc W memc mdc HAR) as HND.
pose proof (Permutation_NoDup HPERM HND) as HND2. cbn [app] in HND2.
assert (HcbO3 : ~ In cb O3) by (intros H; exact (vr32_nodup_app O3 (lb :: cb :: e_rest e) cb HND2 H ltac:(right; left; reflexivity))).
assert (HlbO3 : ~ In lb O3) by (intros H; exact (vr32_nodup_app O3 (lb :: cb :: e_rest e) lb HND2 H ltac:(left; reflexivity))).
assert (Hlbcb : lb <> cb).
{ intros H. apply List.NoDup_app_remove_l in HND2. inversion HND2 as [|x0 l0 Hx0 Hl0 Ex0]. apply Hx0. left. symmetry. exact H. }
assert (Hcb : In cb (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; right; left; reflexivity).
assert (Hlb : In lb (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; left; reflexivity).
assert (FPlo : forall a, inFP (vr_fp e) a -> a < alloc_ceiling).
{ intros a (r & Hr & Ha). unfold vr_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  - unfold VERBS_RECEIVE_PG, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE, A_G_QUITTING in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
  - unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p m] & <- & Hpm). cbn [fst snd] in Ha.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HARe (rec_repA_in_blocks B _ _ _ _ _ _ HRE0 Hpm)) as (_ & _ & Hc & _). lia. }
assert (Hkz : forall a, vr32_keep s1 O3 a -> ~ vr32_zone F FL a).
{ intros a [Hka | [Hka | (p & m & Hpm & Hka)]] Hz; unfold vr32_zone in Hz.
  - lia.
  - destruct (PROGU a Hka) as (Hi & _ & _). pose proof (pa_img_range a Hi) as Hir.
    destruct Hz as [Hz | [Hz | Hz]]; [| lia | subst a; exact (HFLimg Hi)].
    apply (frm_img SEGS B LAWS lyc Sc W memc mdc 4 pos a HAR Hin4); [rewrite <- EF, vr32_fs4; exact Hz | exact Hi].
  - pose proof (HO3 _ Hpm) as Hpm'.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hpm') as (_ & Hp4 & Hpc & Happ & Hown & _).
    destruct Hz as [Hz | [Hz | Hz]].
    + pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc p m 4 pos HAR Hpm' Hin4) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. rewrite <- EF, vr32_fs4 in D. lia.
    + exact (vr32_app_shF F p (req_size m) a HF4096 HFceil HFapp Happ Hka Hz).
    + subst a. exact (proj2 (Hown FL Hka) HFLo). }
(* the memory the first run left *)
pose proof (vr32_kept_run false E (ss_mem ss32) (w_H W) memc (ms_mem ms) F FL UE20 UE22 UE25 ltac:(intros Hf; discriminate Hf)
  ltac:(vm_compute; reflexivity) HFr) as KR1.
assert (KP1 : forall a, 0 <= a < 2 ^ 64 -> vr32_keep s1 O3 a -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hka; exact (KR1 a Ha (Hkz a Hka))).
clear HF HFr HG KR1.
(* 0x8d720: free(copy) *)
prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
assert (Q10' : getr (ms_regs ms) 10 = w64 c) by (rewrite Q10; exact XE33).
assert (Qsp : spZ (ms_regs ms) = s1) by (unfold spZ; rewrite Q2, (EE 2%nat 2%bv eq_refl), R2c; unfold w64; apply unsigned_lit_small; lia).
assert (Q3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, (EE 3%nat 3%bv eq_refl); exact R3c).
assert (Q4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, (EE 4%nat 4%bv eq_refl); exact R4c).
assert (Qs0 : s0Z (ms_regs ms) = sp0) by (unfold s0Z; rewrite Q8, (EE 8%nat 8%bv eq_refl); exact U8).
assert (Qra : raZ (ms_regs ms) = BASE + 29172) by (unfold raZ; rewrite Q1; apply unsigned_lit_small; lia).
assert (Habove : forall a, sp0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW (e_W e) (e_mem e) a).
{ intros a Ha. rewrite KP1 by (first [lia | left; lia]). apply JF1; [lia | lia | intros Hf; pose proof (FPlo a Hf); lia]. }
assert (Hsv : forall j r, nth_error vr_saved_regs j = Some r ->
  rdword (rdW W (ms_mem ms)) (sp0 - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr (e_regs e) (Z_to_bv 5 r)))).
{ intros j r Hj. assert (Hj13 : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate). cbn [length vr_saved_regs] in Hj13.
  rewrite (rdword_ext (rdW W memc) (rdW W (ms_mem ms))) by (intros kk Hkk; apply KP1; [lia | left; lia]).
  apply (rdword_of_val_mem SEGS). apply vr32_val_mem_of_aval. exact (HSAV j r Hj).
  pose proof (bv_unsigned_in_range 64 (getr (e_regs e) (Z_to_bv 5 r))) as HR. change (bv_modulus 64) with (2 ^ 64) in HR. exact HR. }
pose proof (Hsv 0%nat 1 eq_refl) as H8a. pose proof (Hsv 1%nat 8 eq_refl) as H16a. change (Z.of_nat 0) with 0 in H8a. change (Z.of_nat 1) with 1 in H16a.
replace (sp0 - 8 - 8 * 0) with (sp0 - 8) in H8a by lia. replace (sp0 - 8 - 8 * 1) with (sp0 - 16) in H16a by lia.
destruct (vr32_chain (e_ly e) lyc (rdW (e_W e) (e_mem e)) (rdW W (ms_mem ms)) sp0 (s0Z (e_regs e)) (raZ (e_regs e)) (e_ch e)
  (ms_regs ms) s1 Hche Etop ltac:(lia) Habove H8a H16a Hra4e ltac:(lia) Hsp8 Qsp Hs1c ltac:(lia) Qs0 ltac:(rewrite Qra; lia))
  as (ch1 & Hch1).
pose proof (ev_vr_eq (e_R e) (e_D e)) as Hev.
assert (HMOK1 : mo_ok MT Sc (mo_free MT)) by exact (vr32_meter_free_ok e Sc k nm HENT HMET ltac:(lia)).
pmkst HS. rewrite (pal_free B TL).
eapply SRr_bind.
{ exact (afree04_sub SEGS B LAWS pa_segs_low MT (AFREE fx) W (ms_regs ms) (ms_mem ms) VERBS_RECEIVE_STK sp0 (vr_fp e) (e_ly e) (e_S e)
    (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc md1 k c (snd cb) (s1 - sp0) (Z_to_bv 64 (BASE + 29172)) ch1 HJ Hcb Q10'
    ltac:(rewrite Qsp; lia) Ho16 ltac:(lia) ltac:(unfold ASTACK; lia) Q3' Q4' Q1 (ret_ok_codeptr_v 29172 ltac:(lia) eq_refl)
    ltac:(rewrite Hev in HNEV; lia) Hch1 (fun Hb => False_ind _ (proj2 Hfc Hb)) HMOK1). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Eb1 & Eb2) & Hfr2 & HK2 & HMLE2 & _).

assert (EFe : forall lyx, ly_F lyx = ly_F (e_ly e) -> frame_addr lyx 4 pos = F /\ flag_addr lyx 4 pos = FL).
{ intros lyx Ex. destruct (vr32_frame_addr (e_ly e) lyx 4 pos Ex) as [A1 A2]. destruct (vr32_frame_addr (e_ly e) lyc 4 pos ElyF) as [A3 A4].
  split; [rewrite A1, <- A3; exact (eq_sym EF) | rewrite A2, <- A4; reflexivity]. }
(* the block freed is apart from the frame and its shadow *)
assert (Hblkz : forall lyx Sx (Wx : world SEGS) mx mdx p m a, AR SEGS B lyx Sx Wx mx mdx -> In (p, m) (ablocks B lyx Sx) ->
  In (4, pos) (frames Sx) -> frame_addr lyx 4 pos = F -> p <= a < p + req_size m ->
  ~ (F <= a < F + 1024 \/ shadow_addr F <= a < shadow_addr F + 128)).
{ intros lyx Sx Wx mx mdx p m a HARx Hpm Hfx EFx Ha [Hz | Hz].
  - pose proof (sep_block_frame SEGS B LAWS lyx Sx Wx mx mdx p m 4 pos HARx Hpm Hfx) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. rewrite EFx, vr32_fs4 in D. lia.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HARx Hpm) as (_ & _ & _ & Happ & _).
    exact (vr32_app_shF F p (req_size m) a HF4096 HFceil HFapp Happ Ha Hz). }
(* back at 0x8d724 *)
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & ElyF2 & _ & _ & Etop2 & _).
destruct (EFe ly2 ElyF2) as [EF2 EFL2].
assert (Hin4_2 : In (4, pos) (frames S2)) by (rewrite Hfr2; exact Hin4).
replace (sp0 + (s1 - sp0)) with s1 in HK2 by lia.
pose proof HK2 as (K1 & K2 & K3 & K4 & K5 & K6).
assert (KS2 : forall a, s1 <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W (ms_mem ms) a) by (intros a Ha; apply K1; lia).
assert (KF2 : forall a, F <= a < F + 1024 \/ shadow_addr F <= a < shadow_addr F + 128 -> rdW W2 mem2 a = rdW W (ms_mem ms) a).
{ intros a Ha. apply (K4 4 pos a Hin4).
  - unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EF, vr32_fs4. change (1024 / 8) with 128. lia.
  - intros Hc. exact (Hblkz lyc Sc W (ms_mem ms) md1 c (snd cb) a (proj1 HJ) Hcb Hin4 (eq_sym EF) Hc Ha). }
assert (PF2 : forall a, F <= a < F + 1024 \/ shadow_addr F <= a < shadow_addr F + 128 -> apresent (w_H W2) mem2 a).
{ destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4_2) as (_ & _ & P1 & P2).
  rewrite EF2, vr32_fs4 in P1, P2. change (1024 / 8) with 128 in P2.
  intros a [Ha | Ha]; [exact (proj1 (P1 a Ha)) |].
  replace a with (shadow_addr F + (a - shadow_addr F)) by lia. exact (proj1 (P2 (a - shadow_addr F) ltac:(lia))). }
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0;1;2;3;4]%nat HS2.
match type of HS2 with ?P -> _ => assert (HRK : P); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil; apply vr32_rk;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?UE9, ?UE8, ?UE20, ?UE22, ?UE25; intros a Ha;
  first [ apply KS2; lia | apply KF2; lia | lia | apply PF2; lia ]. }
rewrite <- restrict_mkst_fx in HS2.
remember (havoc E 1024 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS2.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (EO1 : forall n, (n < 1024)%nat -> ew E1 n = ew E n) by (intros n Hn; rewrite HE1; apply ew_havoc_old; exact Hn).
clear HE1.
assert (KP2 : forall a, 0 <= a < 2 ^ 64 -> vr32_keep s1 O3 a -> rdW W2 mem2 a = rdW W memc a).
{ intros a Ha Hka. rewrite (vr32_kp_free lyc Sc W W2 (ms_mem ms) mem2 md1 (s1 - ASTACK) s1 c (snd cb) O3 HK2 (proj1 HJ) HO3 HcbO3 Hcb PROGU Hs1c a Ha Hka).
  exact (KP1 a Ha Hka). }
assert (HPERM2 : Permutation (ablocks B ly2 S2) (O3 ++ lb :: e_rest e)).
{ rewrite Eb2. replace (O3 ++ lb :: e_rest e) with ((O3 ++ [lb]) ++ e_rest e) by (rewrite <- app_assoc; reflexivity).
  apply (Permutation_app_inv l1 l2 (O3 ++ [lb]) (e_rest e) (c, snd cb)). rewrite <- Eb1, <- app_assoc. exact HPERM. }
clear HS K1 K2 K3 K4 K5 K6 KS2 KF2 PF2 Q10 Q1 Q2 Q3 Q4 Q8 Q10' Qsp Q3' Q4' Qs0 Qra Habove Hsv H8a H16a Hch1 KP1.
(* 0x8d724 .. 0x8d728: a0 = line (s2), the call of the free wrapper *)
paj_run_shc RUNP RUNC HS2 HJ2.
{ apply vr32_awr; [rewrite EO1 by lia; rewrite UE20; exact (eq_sym EF2) | rewrite EO1 by lia; rewrite UE22; exact (eq_sym EF2)
  | rewrite EO1 by lia; rewrite UE25, EF2; reflexivity | vm_compute; reflexivity]. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md3 := m) in *; clearbody md3 end.

lazymatch type of HS2 with st_ok _ _ _ (restrict _ ?m) => rename m into ms2 end.
assert (UE20a : bv_unsigned (ew E1 20) = F) by (rewrite EO1 by lia; exact UE20).
assert (UE22a : bv_unsigned (ew E1 22) = F) by (rewrite EO1 by lia; exact UE22).
assert (UE25a : bv_unsigned (ew E1 25) = shadow_addr F) by (rewrite EO1 by lia; exact UE25).
lazymatch type of HFr with frame_of _ ?rs _ _ =>
  pose proof (vr32_kept_run false E1 rs (w_H W2) mem2 (ms_mem ms2) F FL UE20a UE22a UE25a ltac:(intros Hf; discriminate Hf)
    ltac:(vm_compute; reflexivity) HFr) as KR2 end.
assert (KP3 : forall a, 0 <= a < 2 ^ 64 -> vr32_keep s1 O3 a -> rdW W2 (ms_mem ms2) a = rdW W memc a)
  by (intros a Ha Hka; rewrite (KR2 a Ha (Hkz a Hka)); exact (KP2 a Ha Hka)).
clear HF HFr HG KR2.
(* 0x8d728: free(line) *)
prreg HS2 (10%bv : bv 5) Q10. prreg HS2 (1%bv : bv 5) Q1. prreg HS2 (2%bv : bv 5) Q2. prreg HS2 (3%bv : bv 5) Q3.
prreg HS2 (4%bv : bv 5) Q4. prreg HS2 (8%bv : bv 5) Q8.
assert (Q10' : getr (ms_regs ms2) 10 = w64 q) by (rewrite Q10, EO1, (EE 18%nat 18%bv eq_refl) by lia; exact R18c).
assert (Qsp : spZ (ms_regs ms2) = s1) by (unfold spZ; rewrite Q2, EO1, (EE 2%nat 2%bv eq_refl), R2c by lia; unfold w64; apply unsigned_lit_small; lia).
assert (Q3' : getr (ms_regs ms2) 3 = w64 (as_gp B)) by (rewrite Q3, EO1, (EE 3%nat 3%bv eq_refl) by lia; exact R3c).
assert (Q4' : getr (ms_regs ms2) 4 = w64 (as_tp B)) by (rewrite Q4, EO1, (EE 4%nat 4%bv eq_refl) by lia; exact R4c).
assert (Qs0 : s0Z (ms_regs ms2) = sp0) by (unfold s0Z; rewrite Q8, EO1, (EE 8%nat 8%bv eq_refl) by lia; exact U8).
assert (Qra : raZ (ms_regs ms2) = BASE + 29180) by (unfold raZ; rewrite Q1; apply unsigned_lit_small; lia).
assert (Habove : forall a, sp0 <= a < 2 ^ 64 -> rdW W2 (ms_mem ms2) a = rdW (e_W e) (e_mem e) a).
{ intros a Ha. rewrite KP3 by (first [lia | left; lia]). apply JF1; [lia | lia | intros Hf; pose proof (FPlo a Hf); lia]. }
assert (Hsv : forall j r, nth_error vr_saved_regs j = Some r ->
  rdword (rdW W2 (ms_mem ms2)) (sp0 - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr (e_regs e) (Z_to_bv 5 r)))).
{ intros j r Hj. assert (Hj13 : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate). cbn [length vr_saved_regs] in Hj13.
  rewrite (rdword_ext (rdW W memc) (rdW W2 (ms_mem ms2))) by (intros kk Hkk; apply KP3; [lia | left; lia]).
  apply (rdword_of_val_mem SEGS). apply vr32_val_mem_of_aval. exact (HSAV j r Hj).
  pose proof (bv_unsigned_in_range 64 (getr (e_regs e) (Z_to_bv 5 r))) as HR. change (bv_modulus 64) with (2 ^ 64) in HR. exact HR. }
pose proof (Hsv 0%nat 1 eq_refl) as H8a. pose proof (Hsv 1%nat 8 eq_refl) as H16a. change (Z.of_nat 0) with 0 in H8a. change (Z.of_nat 1) with 1 in H16a.
replace (sp0 - 8 - 8 * 0) with (sp0 - 8) in H8a by lia. replace (sp0 - 8 - 8 * 1) with (sp0 - 16) in H16a by lia.
destruct (vr32_chain (e_ly e) ly2 (rdW (e_W e) (e_mem e)) (rdW W2 (ms_mem ms2)) sp0 (s0Z (e_regs e)) (raZ (e_regs e)) (e_ch e)
  (ms_regs ms2) s1 Hche Etop2 ltac:(lia) Habove H8a H16a Hra4e ltac:(lia) Hsp8 Qsp Hs1c ltac:(lia) Qs0 ltac:(rewrite Qra; lia))
  as (ch2 & Hch2).
pose proof (vr32_meter_free e Sc S2 k nm HMET HMLE2) as HMET2.
assert (HMOK2 : mo_ok MT S2 (mo_free MT)) by exact (vr32_meter_free_ok e S2 (k + 1) nm HENT HMET2 ltac:(lia)).
assert (HO3_2 : forall pn, In pn O3 -> In pn (ablocks B ly2 S2))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPERM2)); apply in_or_app; left; exact Hpn).
assert (Hlb2 : In lb (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym HPERM2)); apply in_or_app; right; left; reflexivity).
pmkst HS2. rewrite (pal_free B TL).
eapply SRr_bind.
{ exact (afree04_sub SEGS B LAWS pa_segs_low MT (AFREE fx) W2 (ms_regs ms2) (ms_mem ms2) VERBS_RECEIVE_STK sp0 (vr_fp e) (e_ly e) (e_S e)
    (e_W e) (e_mem e) (e_md e) [(4, pos)] ly2 S2 md3 (k + 1) q (snd lb) (s1 - sp0) (Z_to_bv 64 (BASE + 29180)) ch2 HJ2 Hlb2 Q10'
    ltac:(rewrite Qsp; lia) Ho16 ltac:(lia) ltac:(unfold ASTACK; lia) Q3' Q4' Q1 (ret_ok_codeptr_v 29180 ltac:(lia) eq_refl)
    ltac:(rewrite Hev in HNEV; lia) Hch2 (fun Hb => False_ind _ (proj2 Hfq Hb)) HMOK2). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md4 & -> & HJ3 & HP3 & (l3 & l4 & Eb3 & Eb4) & Hfr3 & HK3 & HMLE3 & _).
(* back at 0x8d72c *)
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & ElyF3 & _ & _ & Etop3 & _).
destruct (EFe ly3 ElyF3) as [EF3 EFL3].
assert (Hin4_3 : In (4, pos) (frames S3)) by (rewrite Hfr3; exact Hin4_2).
replace (sp0 + (s1 - sp0)) with s1 in HK3 by lia.
pose proof HK3 as (K1 & K2 & K3 & K4 & K5 & K6).
assert (KS3 : forall a, s1 <= a < 2 ^ 64 -> rdW W3 mem3 a = rdW W2 (ms_mem ms2) a) by (intros a Ha; apply K1; lia).
assert (KF3 : forall a, F <= a < F + 1024 \/ shadow_addr F <= a < shadow_addr F + 128 -> rdW W3 mem3 a = rdW W2 (ms_mem ms2) a).
{ intros a Ha. apply (K4 4 pos a Hin4_2).
  - unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF2, vr32_fs4. change (1024 / 8) with 128. lia.
  - intros Hc. exact (Hblkz ly2 S2 W2 (ms_mem ms2) md3 q (snd lb) a (proj1 HJ2) Hlb2 Hin4_2 EF2 Hc Ha). }
assert (PF3 : forall a, F <= a < F + 1024 \/ shadow_addr F <= a < shadow_addr F + 128 -> apresent (w_H W3) mem3 a).
{ destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md4 4 pos HAR3 Hin4_3) as (_ & _ & P1 & P2).
  rewrite EF3, vr32_fs4 in P1, P2. change (1024 / 8) with 128 in P2.
  intros a [Ha | Ha]; [exact (proj1 (P1 a Ha)) |].
  replace a with (shadow_addr F + (a - shadow_addr F)) by lia. exact (proj1 (P2 (a - shadow_addr F) ltac:(lia))). }
assert (UE9a : bv_unsigned (ew E1 9) = s1) by (rewrite EO1 by lia; exact UE9).
assert (UE8a : bv_unsigned (ew E1 8) = sp0) by (rewrite EO1 by lia; exact UE8).
jafter_call_keep_hi HS2 1040%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0;1;2;3;4]%nat HS3.
match type of HS3 with ?P -> _ => assert (HRK : P); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil; apply vr32_rk;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?UE9a, ?UE8a, ?UE20a, ?UE22a, ?UE25a; intros a Ha;
  first [ apply KS3; lia | apply KF3; lia | lia | apply PF3; lia ]. }
rewrite <- restrict_mkst_fx in HS3.
remember (havoc E1 1040 (map (getr regs3) CLOB)) as E2 eqn:HE2 in HS3.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [exact HEI1 | cbv; lia]).
assert (EO2 : forall n, (n < 1024)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2, ew_havoc_old by lia; exact (EO1 n Hn)).
clear HE2.
assert (KP4 : forall a, 0 <= a < 2 ^ 64 -> vr32_keep s1 O3 a -> rdW W3 mem3 a = rdW W memc a).
{ intros a Ha Hka. rewrite (vr32_kp_free ly2 S2 W2 W3 (ms_mem ms2) mem3 md3 (s1 - ASTACK) s1 q (snd lb) O3 HK3 (proj1 HJ2) HO3_2 HlbO3 Hlb2 PROGU Hs1c a Ha Hka).
  exact (KP3 a Ha Hka). }
assert (HPERM3 : Permutation (ablocks B ly3 S3) (O3 ++ e_rest e)).
{ rewrite Eb4. apply (Permutation_app_inv l3 l4 O3 (e_rest e) (q, snd lb)). rewrite <- Eb3. exact HPERM2. }
clear HS2 K1 K2 K3 K4 K5 K6 KS3 KF3 PF3 Q10 Q1 Q2 Q3 Q4 Q8 Q10' Qsp Q3' Q4' Qs0 Qra Habove Hsv H8a H16a Hch2 KP3.
assert (UE20b : bv_unsigned (ew E2 20) = F) by (rewrite EO2 by lia; exact UE20).
assert (UE22b : bv_unsigned (ew E2 22) = F) by (rewrite EO2 by lia; exact UE22).
assert (UE25b : bv_unsigned (ew E2 25) = shadow_addr F) by (rewrite EO2 by lia; exact UE25).
(* 0x8d72c .. 0x8d73c: shadow(F)[76] := f8 (`sb a0,76(s9)`), a1 = 64, a0 = shadow(F) + 4 (s11), the call of
   __asan_set_shadow_f8 *)
paj_run_shc RUNP RUNC HS3 HJ3.
{ apply vr32_awr; [rewrite UE20b; exact (eq_sym EF3) | rewrite UE22b; exact (eq_sym EF3) | rewrite UE25b, EF3; reflexivity
  | vm_compute; reflexivity]. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md5 := m) in *; clearbody md5 end.
lazymatch type of HS3 with st_ok _ _ _ (restrict _ ?m) => rename m into ms3 end.
lazymatch type of HFr with frame_of _ ?rs _ _ =>
  pose proof (vr32_kept_run false E2 rs (w_H W3) mem3 (ms_mem ms3) F FL UE20b UE22b UE25b ltac:(intros Hf; discriminate Hf)
    ltac:(vm_compute; reflexivity) HFr) as KR3 end.
assert (KP5 : forall a, 0 <= a < 2 ^ 64 -> vr32_keep s1 O3 a -> rdW W3 (ms_mem ms3) a = rdW W memc a)
  by (intros a Ha Hka; rewrite (KR3 a Ha (Hkz a Hka)); exact (KP4 a Ha Hka)).
assert (KZ5 : forall a, 0 <= a < 2 ^ 64 -> ~ vr32_zone F FL a -> rdW W3 (ms_mem ms3) a = rdW W3 mem3 a) by exact KR3.
clear HF HFr HG.
prreg HS3 (10%bv : bv 5) Q10. prreg HS3 (11%bv : bv 5) Q11. prreg HS3 (1%bv : bv 5) Q1. prreg HS3 (2%bv : bv 5) Q2.
prreg HS3 (3%bv : bv 5) Q3. prreg HS3 (4%bv : bv 5) Q4.
assert (Q10' : getr (ms_regs ms3) 10 = w64 (shadow_addr F + 4)) by (rewrite Q10, EO2, (EE 27%nat 27%bv eq_refl) by lia; exact R27c).
assert (Qsp : spZ (ms_regs ms3) = sp0 + (s1 - sp0))
  by (unfold spZ; rewrite Q2, EO2, (EE 2%nat 2%bv eq_refl), R2c by lia; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Q3' : getr (ms_regs ms3) 3 = w64 (as_gp B)) by (rewrite Q3, EO2, (EE 3%nat 3%bv eq_refl) by lia; exact R3c).
assert (Q4' : getr (ms_regs ms3) 4 = w64 (as_tp B)) by (rewrite Q4, EO2, (EE 4%nat 4%bv eq_refl) by lia; exact R4c).
pmkst HS3.
eapply SRr_bind.
{ exact (vr32_shadow_at (SIGMA CS___asan_set_shadow_f8) 0xf8 (SHF8 fx) W3 (ms_regs ms3) (ms_mem ms3) VERBS_RECEIVE_STK sp0 (vr_fp e)
    (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] ly3 S3 md5 (k + 1 + 1) 4 pos (shadow_addr F + 4) 64 (s1 - sp0)
    (Z_to_bv 64 (BASE + 29200)) HJ3 (or_introl eq_refl) Q10' Q11 ltac:(lia) ltac:(rewrite EF3; lia)
    ltac:(rewrite EF3, vr32_fs4; change (1024 / 8) with 128; lia) Qsp Ho16 ltac:(lia) ltac:(unfold ESTACK; lia) Q3' Q4' Q1
    (ret_ok_codeptr_v 29200 ltac:(lia) eq_refl)). }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md6 & -> & HJ4 & HP4 & HO4).

(* back at 0x8d740: the fill changed the shadow region, so the state keeps the other four *)
assert (PF4 : forall a, F <= a < F + 1024 -> apresent (w_H W3) mem4 a).
{ destruct (al_frames _ _ LAWS ly3 S3 W3 mem4 md6 4 pos (proj1 HJ4) Hin4_3) as (_ & _ & P1 & _).
  rewrite EF3, vr32_fs4 in P1. intros a Ha. exact (proj1 (P1 a Ha)). }
assert (UE9b : bv_unsigned (ew E2 9) = s1) by (rewrite EO2 by lia; exact UE9).
assert (UE8b : bv_unsigned (ew E2 8) = sp0) by (rewrite EO2 by lia; exact UE8).
jafter_call_keep_hi HS3 1056%nat regs4 (mrestrict (w_H W3) mem4) HP4 [0;1;2;3]%nat HS4.
match type of HS4 with ?P -> _ => assert (HRK : P); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil; apply vr32_rk;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?UE9b, ?UE8b, ?UE20b, ?UE22b; intros a Ha;
  first [ apply HO4; lia | lia | apply PF4; lia ]. }
rewrite <- restrict_mkst_fx in HS4.
remember (havoc E2 1056 (map (getr regs4) CLOB)) as E3 eqn:HE3 in HS4.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc_hi; [exact HEI2 | cbv; lia]).
assert (EO3 : forall n, (n < 1024)%nat -> ew E3 n = ew E n) by (intros n Hn; rewrite HE3, ew_havoc_old by lia; exact (EO2 n Hn)).
clear HE3.
assert (KP6 : forall a, 0 <= a < 2 ^ 64 -> vr32_keep s1 O3 a -> rdW W3 mem4 a = rdW W memc a).
{ intros a Ha Hka. pose proof (Hkz a Hka) as Hz. unfold vr32_zone in Hz.
  rewrite (HO4 a Ha ltac:(lia)). exact (KP5 a Ha Hka). }
clear HS3 Q10 Q11 Q1 Q2 Q3 Q4 Q10' Qsp Q3' Q4' KP5 KZ5 PF4.
assert (UE20c : bv_unsigned (ew E3 20) = F) by (rewrite EO3 by lia; exact UE20).
assert (UE22c : bv_unsigned (ew E3 22) = F) by (rewrite EO3 by lia; exact UE22).
assert (UE25c : bv_unsigned (ew E3 25) = shadow_addr F) by (rewrite EO3 by lia; exact UE25).
(* 0x8d740 .. 0x8d758: F[0] := 0x45e0360e (`sd a0,0(s6)`), `beqz s4` not taken (s4 = F >= 4096: the
   __asan_set_shadow_00 arm at 0x8d768 is dead), a1 = 128, a0 = shadow(F) (s9), the call of __asan_set_shadow_f5 *)
paj_run_shc RUNP RUNC HS4 HJ4.
{ apply vr32_awr; [rewrite UE20c; exact (eq_sym EF3) | rewrite UE22c; exact (eq_sym EF3) | rewrite UE25c, EF3; reflexivity
  | vm_compute; reflexivity]. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md7 := m) in *; clearbody md7 end.
lazymatch type of HS4 with st_ok _ _ _ (restrict _ ?m) => rename m into ms4 end.
lazymatch type of HFr with frame_of _ ?rs _ _ =>
  pose proof (vr32_kept_run false E3 rs (w_H W3) mem4 (ms_mem ms4) F FL UE20c UE22c UE25c ltac:(intros Hf; discriminate Hf)
    ltac:(vm_compute; reflexivity) HFr) as KR4 end.
assert (KP7 : forall a, 0 <= a < 2 ^ 64 -> vr32_keep s1 O3 a -> rdW W3 (ms_mem ms4) a = rdW W memc a)
  by (intros a Ha Hka; rewrite (KR4 a Ha (Hkz a Hka)); exact (KP6 a Ha Hka)).
clear HF HFr HG KR4.
prreg HS4 (10%bv : bv 5) Q10. prreg HS4 (11%bv : bv 5) Q11. prreg HS4 (1%bv : bv 5) Q1. prreg HS4 (2%bv : bv 5) Q2.
prreg HS4 (3%bv : bv 5) Q3. prreg HS4 (4%bv : bv 5) Q4.
assert (Q10' : getr (ms_regs ms4) 10 = w64 (shadow_addr F)) by (rewrite Q10, EO3, (EE 25%nat 25%bv eq_refl) by lia; exact R25c).
assert (Qsp : spZ (ms_regs ms4) = sp0 + (s1 - sp0))
  by (unfold spZ; rewrite Q2, EO3, (EE 2%nat 2%bv eq_refl), R2c by lia; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Q3' : getr (ms_regs ms4) 3 = w64 (as_gp B)) by (rewrite Q3, EO3, (EE 3%nat 3%bv eq_refl) by lia; exact R3c).
assert (Q4' : getr (ms_regs ms4) 4 = w64 (as_tp B)) by (rewrite Q4, EO3, (EE 4%nat 4%bv eq_refl) by lia; exact R4c).
pmkst HS4.
eapply SRr_bind.
{ exact (vr32_shadow_at (SIGMA CS___asan_set_shadow_f5) 0xf5 (SHF5 fx) W3 (ms_regs ms4) (ms_mem ms4) VERBS_RECEIVE_STK sp0 (vr_fp e)
    (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] ly3 S3 md7 (k + 1 + 1) 4 pos (shadow_addr F) 128 (s1 - sp0)
    (Z_to_bv 64 (BASE + 29228)) HJ4 (or_introl eq_refl) Q10' Q11 ltac:(lia) ltac:(rewrite EF3; lia)
    ltac:(rewrite EF3, vr32_fs4; change (1024 / 8) with 128; lia) Qsp Ho16 ltac:(lia) ltac:(unfold ESTACK; lia) Q3' Q4' Q1
    (ret_ok_codeptr_v 29228 ltac:(lia) eq_refl)). }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md8 & -> & HJ5 & HP5 & HO5).
(* back at 0x8d75c *)
pose proof (proj1 HJ5) as HAR5.
destruct (al_frames _ _ LAWS ly3 S3 W3 mem5 md8 4 pos HAR5 Hin4_3) as (_ & _ & PF5 & _).
rewrite EF3, vr32_fs4 in PF5.
assert (UE20c' : bv_unsigned (ew E3 9) = s1 /\ bv_unsigned (ew E3 8) = sp0) by (rewrite !EO3 by lia; split; [exact UE9 | exact UE8]).
destruct UE20c' as [UE9c UE8c].
jafter_call_keep_hi HS4 1072%nat regs5 (mrestrict (w_H W3) mem5) HP5 [0;1;2;3]%nat HS5.
match type of HS5 with ?P -> _ => assert (HRK : P); [|specialize (HS5 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil; apply vr32_rk;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?UE9c, ?UE8c, ?UE20c, ?UE22c; intros a Ha;
  first [ apply HO5; lia | lia | apply (proj1 (PF5 a ltac:(lia))) ]. }
rewrite <- restrict_mkst_fx in HS5.
remember (havoc E3 1072 (map (getr regs5) CLOB)) as E4 eqn:HE4 in HS5.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc_hi; [exact HEI3 | cbv; lia]).
assert (EO4 : forall n, (n < 1024)%nat -> ew E4 n = ew E n) by (intros n Hn; rewrite HE4, ew_havoc_old by lia; exact (EO3 n Hn)).
clear HE4.
assert (KP8 : forall a, 0 <= a < 2 ^ 64 -> vr32_keep s1 O3 a -> rdW W3 mem5 a = rdW W memc a).
{ intros a Ha Hka. pose proof (Hkz a Hka) as Hz. unfold vr32_zone in Hz.
  rewrite (HO5 a Ha ltac:(lia)). exact (KP7 a Ha Hka). }
clear HS4 Q10 Q11 Q1 Q2 Q3 Q4 Q10' Qsp Q3' Q4' KP6 KP7.
(* the flag byte's region *)
assert (UE32d : bv_unsigned (ew E4 32) = FL) by (rewrite EO4 by lia; exact UE32).
destruct (FFL ly3 S3 W3 mem5 md8 4 pos HAR5 Hin4_3) as (HFLp5 & HFLo5 & _ & _). rewrite EFL3 in HFLp5, HFLo5.
assert (HFLnF : ~ (F <= FL < F + 1024)) by (intros Hz; exact (proj2 (PF5 FL Hz) HFLo5)).
lazymatch type of HS5 with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_pi_add_region Ex ssx msx vr32_rflag HS5 eq_refl) as HS6 end.
match type of HS6 with ?P -> _ => assert (HRK : P); [|specialize (HS6 HRK); clear HRK] end.
{ unfold region_ok, vr32_rflag. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
  rewrite UE32d. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. replace o with 0 by lia. rewrite Z.add_0_r. apply (apresent_writable SEGS). exact HFLp5. }
match type of HS6 with ?P -> _ => assert (HRK : P); [|specialize (HS6 HRK); clear HRK] end.
{ apply all_disjoint_of_extents. unfold extent_of_region, vr32_rflag.
  lazymatch goal with |- zall_disjoint _ (map _ ?rs) => let r := eval vm_compute in rs in change rs with r end.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint]. rewrite UE32d, EO4, EO4, EO4, EO4 by lia. rewrite UE9, UE8, UE20, UE22.
  unfold zdisj. cbn [fst snd]. repeat split; lia. }

(* 0x8d75c .. 0x8d7b0: the flag release (`ld a0,1016(s4)`; `sb zero,0(a0)`), `j 0x8d774`, the epilogue (sp = s0 - 192,
   the 13 reloads from sp0-8 .. sp0-104, sp += 192); the run stops at the ret *)
paj_run_flag_sh RUNF HS6 HJ5.
{ lia. }
{ eapply (vr32_awr_flag E4); [rewrite EO4 by lia; rewrite UE20; exact (eq_sym EF3) | rewrite EO4 by lia; rewrite UE22; exact (eq_sym EF3)
  | rewrite EO4 by lia; rewrite UE25, EF3; reflexivity | rewrite UE32d; exact (eq_sym EFL3) | vm_compute; reflexivity]. }
{ intros msr HSm. unfold st_ok_pi in HSm. pose proof (st_ok_mem_ok SEGS E4 _ msr HSm) as (_ & HRs & _).
  lazymatch type of HRs with Forall _ ?l => let l' := eval vm_compute in l in change l with l' in HRs end.
  apply Forall_inv in HRs. destruct HRs as (_ & _ & _ & HC).
  cbn [YP09.r_chunks YP09.r_base base_val] in HC. apply Forall_inv in HC.
  destruct (HC 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2). cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb1, Hb2.
  rewrite UE32d in Hb2. rewrite EFL3. replace FL with (FL + 0 + 0) by lia. rewrite Hb2. rewrite <- Hb1. reflexivity. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md9 := m) in *; clearbody md9 end.
lazymatch type of HS6 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms6 end.
lazymatch type of HFr with frame_of _ ?rs _ _ =>
  pose proof (vr32_kept_run true E4 rs (w_H W3) mem5 (ms_mem ms6) F FL ltac:(rewrite EO4 by lia; exact UE20)
    ltac:(rewrite EO4 by lia; exact UE22) ltac:(rewrite EO4 by lia; exact UE25) ltac:(intros _; exact UE32d)
    ltac:(vm_compute; reflexivity) HFr) as KR6 end.
assert (KP9 : forall a, 0 <= a < 2 ^ 64 -> vr32_keep s1 O3 a -> rdW W3 (ms_mem ms6) a = rdW W memc a)
  by (intros a Ha Hka; rewrite (KR6 a Ha (Hkz a Hka)); exact (KP8 a Ha Hka)).
clear HF HFr HG KR6.
eapply (RET W3 _ _ _ _ _ HS6 eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
(* the return: the statement's post, at the section's own FP state (S32 reaches no printf wrapper: fx' := fx) *)
unfold vr_final, apost_baseF. cbv zeta.
exists fx, ly3, (stack_free_state 4 pos S3), (ms_regs ms6), (ms_mem ms6), (with_vm_backing (m_vm_lazy md9) mat' md9).

assert (EXn : forall n, (32 <= n < 240)%nat -> ew E n = nth (n - 32) ext (Z_to_bv 64 0)).
{ intros n Hn. replace n with (32 + (n - 32))%nat at 1 by lia. apply EX. cbv [A_TEXT]. lia. }
prreg HS6 (1%bv : bv 5) Z1.
split.
{ rewrite Z1, EO4, (EXn 34%nat ltac:(lia)) by lia.
  assert (X1 : nth (34 - 32) ext (Z_to_bv 64 0) = getr (e_regs e) 1) by reflexivity. rewrite X1.
  unfold YK0s.ret_ok in Hrae. rewrite Hrae. reflexivity. }
split; [intros kf _; reflexivity|].
split; [left; reflexivity|].
split.
{ assert (HJf : ajournal SEGS B VERBS_RECEIVE_STK sp0 (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [] ly3
    (stack_free_state 4 pos S3) W3 (ms_mem ms6) md9 (ev_vr (e_R e) (e_D e))) by (eapply ajournal_mono_k; [exact HJ5 | rewrite Hev; lia]).
  apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJf. }
split.
{ apply aregs_preserved_eqs.
  all: lazymatch goal with |- getr (ms_regs _) ?r = _ => let H := fresh "Z" in prreg HS6 r H; rewrite H end.
  all: rewrite EO4 by lia.
  all: first
    [ rewrite (EE 8%nat 8%bv eq_refl), R8c; unfold w64; change sp0 with (bv_unsigned (getr (e_regs e) 2)); apply Z_to_bv_bv_unsigned
    | rewrite (EE 3%nat 3%bv eq_refl), R3c; exact (eq_sym Hgpe)
    | rewrite (EE 4%nat 4%bv eq_refl), R4c; exact (eq_sym Htpe)
    | lazymatch goal with |- ew _ ?n = _ => rewrite (EXn n ltac:(lia)); reflexivity end ]. }
rewrite vr_runA_eq. cbv beta iota.
exists O3.
pose proof HJ5 as (HAR6 & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
assert (Eab6 : ablocks B ly3 (stack_free_state 4 pos S3) = ablocks B ly3 S3) by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
assert (HPERMf : Permutation (ablocks B ly3 (stack_free_state 4 pos S3)) (O3 ++ e_rest e)) by (rewrite Eab6; exact HPERM3).
assert (Hdr : In (e_data e, e_n e `max` 1) (e_rest e)).
{ pose proof (Permutation_in _ HPE HDin) as H. apply in_app_or in H as [H|H]; [exfalso; exact (HDnO H) | exact H]. }
assert (Hdf : In (e_data e, e_n e `max` 1) (ablocks B ly3 (stack_free_state 4 pos S3)))
  by (apply (Permutation_in _ (Permutation_sym HPERMf)); apply in_or_app; right; exact Hdr).
assert (HOe : forall pn, In pn (e_O e) -> In pn (ablocks B (e_ly e) (e_S e))) by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ HRE0 Hpn)).
lazymatch goal with |- ?P /\ _ => assert (HREPf : P) end.
{ apply (rec_repA_agree B lyc Sc _ _ (rdW W memc) _ _ O3 HREC).
  - intros pn Hpn _. apply (Permutation_in _ (Permutation_sym HPERMf)). apply in_or_app. left. exact Hpn.
  - intros kk Hkk. unfold REC_SIZE in Hkk. apply KP9; [unfold A_G_REC; lia|].
    right; left. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; lia].
  - intros kk Hkk. unfold SC_SIZE in Hkk. apply KP9; [unfold A_REC_SPILL; lia|].
    right; left. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; lia].
  - intros [p m] Hpn kk Hkk. cbn [fst snd] in *. destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR (HO3 _ Hpn)) as (_ & Hp4 & Hpc & _ & _ & _ & Hm).
    pose proof (req_size_pos m ltac:(lia)) as [_ Hrm].
    apply KP9; [lia | right; right; exists p, m; split; [exact Hpn | lia]]. }
split; [exact HREPf|].
split.
{ apply (aval_mem_agree (rdW W memc) _ A_G_QUITTING 4 _ HQV). intros kk Hkk. change (Z.of_nat 4) with 4 in Hkk.
  apply KP9; [unfold A_G_QUITTING; lia|]. right; left. exists (A_G_QUITTING, A_G_QUITTING + 4).
  split; [right; right; left; reflexivity | cbn [fst snd]; lia]. }
split; [exact HPERMf|].
split; [exact HnO3|].
split.
{ intros i Hi. pose proof (req_size_pos (e_n e `max` 1) ltac:(lia)) as [_ Hrq].
  rewrite (G2 (e_data e) (e_n e `max` 1) (Z.of_nat i) HDin Hdf ltac:(lia)); [exact (HDb i Hi)|].
  intros (r & Hr & Ha). apply in_app_or in Hr as [Hr | Hr].
  - pose proof (blk_off_imgP B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) _ _ HARe HDin) as Hoff. unfold off_img in Hoff.
    unfold VERBS_RECEIVE_PG, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE, A_G_QUITTING in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
  - unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p m] & <- & Hpm). cbn [fst snd] in Ha.
    assert (Hne : (p, m) <> (e_data e, e_n e `max` 1)) by (intros Eq; rewrite Eq in Hpm; exact (HDnO Hpm)).
    pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ p m _ _ HARe (HOe _ Hpm) HDin Hne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. lia. }
destruct HMSG as ((cm & pm & Hcm & Hcm0 & _ & Hm1 & Hm2) & _ & _).
assert (Hmsg : forall a, e_msg e <= a < e_msg e + 24 -> rdW W3 (ms_mem ms6) a = rdW (e_W e) (e_mem e) a).
{ intros a Ha. apply (G4 cm pm a Hcm); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia|].
  intros (r & Hr & Hra). apply in_app_or in Hr as [Hr | Hr].
  - pose proof (frm_off_imgP B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) cm pm HARe Hcm) as Hoff. unfold off_img in Hoff.
    unfold VERBS_RECEIVE_PG, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE, A_G_QUITTING in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hra; lia.
  - unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p m] & <- & Hpm). cbn [fst snd] in Hra.
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ p m cm pm HARe (HOe _ Hpm) Hcm) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. lia. }
split; [apply (aval_mem_agree _ _ (e_msg e) 4 (e_fd e) HFD); intros kk Hkk; change (Z.of_nat 4) with 4 in Hkk; apply Hmsg; lia|].
split; [apply (aval_mem_agree _ _ (e_msg e + 8) 8 (e_data e) HDATA); intros kk Hkk; change (Z.of_nat 8) with 8 in Hkk; apply Hmsg; lia|].
split; [apply (aval_mem_agree _ _ (e_msg e + 16) 8 (e_n e) HNV); intros kk Hkk; change (Z.of_nat 8) with 8 in Hkk; apply Hmsg; lia|].
split.
{ apply (vr32_live_le (blocks_bytes (e_S e)) _ (length (r_calls (vr_R3 (e_R e) (e_D e)))) (vr32_calls_le _ (e_D e) HRC0)).
  exact (vr_live_le SEGS B LAWS (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) _ _ _ _ _ _ (vr_R3 (e_R e) (e_D e))
    (e_O e) O3 [] (e_rest e) HARe HAR6 HPE HPERMf HREPf). }
unfold stack_free_state. apply (mo_le_set_fs_r MT MTFL).
exact (vri_meter_final MT e S3 (k + 1 + 1) nm MTL (vr32_meter_free e S2 S3 (k + 1) nm HMET2 HMLE3) ltac:(lia)).
Qed.
End e.
End f.
End d.
