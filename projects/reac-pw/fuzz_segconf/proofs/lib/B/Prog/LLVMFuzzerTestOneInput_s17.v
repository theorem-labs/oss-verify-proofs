(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the cut lemma pb_bs_cell of reac_grant_build_sweep's cell loop, adapting the call-and-reseat walk pattern of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v and lib/A/AChf.v and the caller-journal call block of lib/YC20.v; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantBuildSweepCell.v, with its module paths and module names changed; 905 of its 931 lines of code are new or changed and 336 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the walk of the
   test harness's entry function LLVMFuzzerTestOneInput (0x84dc0): segment S07 (0x854d4 .. 0x8552c: reac_segconf_parse
   (c, text) at 0x854dc, check 17 at 0x854e0 (the shadow byte of m + 0x2000, never poisoned), returned := returned &
   (n == m->n), free(text) at 0x8552c) and segment S08 (0x85530 .. 0x85554: the label's five shadow bytes out of scope,
   the latch `bne s9,s2,85110`).

   proves function LLVMFuzzerTestOneInput (reuse search, rule 24: released units, the earlier proof delivery and working
   heads; the result is recorded with the commissioning brief; none: written new)

   S08 follows image A's twin (image A's S07 / S08 commit 6b130104f652, LLVMFuzzerTestOneInput_s17.v lt_seg_S08), with
   image B's registers and slots (PLAN-asanubsan-main section 11: the shadow base SH(FR) is loaded from 184(s1) into a0,
   the byte -8 is `li a1,-8`, the latch compares s9 with s2). S07 is written new (the twin had no S07 yet): the run to
   the parse's jal, the parse by cl_callSF and its contract (its FP state fx1 by srr_after_callF), then s7_tail at fx1:
   the run to the free's jal (check 17's slow path not taken: the shadow byte is 0) and the free by afree04_sub. The
   stack-protector cells after each call come from AR (SegRecCells.seg_rec_cells, hypothesis HBS : SegBSyms B).
   The kit is LLVMFuzzerTestOneInput_s17k.v. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa
  SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s17k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require reac_segconf_parse_c reac_segconf_parse_file_c
  cross_check_c SegRecBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the frame's 36 shadow bytes: S08's five stores turn the label out of scope, nothing else changes *)
Lemma s17s_fsh_same : forall i, (i < 36)%nat -> ~ (12 <= i < 17)%nat -> nth i (lt_fsh LFO0) 0 = nth i (lt_fsh LFO_L) 0.
Proof. intros i Hi Hn. do 36 (destruct i as [|i]; [first [reflexivity | lia] |]). lia. Qed.
Lemma s17s_fsh_f8 : forall i, (12 <= i < 17)%nat -> nth i (lt_fsh LFO0) 0 = 248.
Proof. intros i Hi. do 17 (destruct i as [|i]; [first [reflexivity | lia] |]). lia. Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* awr_ok reads only the regions' bases and windows (image A's S00 kit s10_awr_skel) *)
Lemma s17s_awr_skel : forall segs B Ex rs rs' STK sp0 FP bl0 blc fr0 lyx own,
  skeleton rs' = skeleton rs -> awr_ok segs B Ex rs STK sp0 FP bl0 blc fr0 lyx own ->
  awr_ok segs B Ex rs' STK sp0 FP bl0 blc fr0 lyx own.
Proof. intros segs B Ex rs rs' STK sp0 FP bl0 blc fr0 lyx own Hsk H a Ha. apply H. exact (in_wrange_skeleton Ex rs' rs a Hsk Ha). Qed.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a sub-list of the slots *)
Lemma s17s_slots_sub : forall cx (rd : reader) L L', (forall x, In x L' -> In x L) -> lt_slots cx rd L -> lt_slots cx rd L'.
Proof. intros cx rd L L' HS H o v Hin. exact (H o v (HS _ Hin)). Qed.
Lemma s17s_slots_kept : forall cx (rd rd' : reader) L,
  (forall o v, In (o, v) L -> 0 <= o <= 216) ->
  (forall a, x_s1 cx <= a < x_s1 cx + 224 -> rd' a = rd a) -> lt_slots cx rd L -> lt_slots cx rd' L.
Proof.
intros cx rd rd' L HO K H o v Hin. pose proof (HO o v Hin) as Ho.
apply (s17_word_kept rd); [|exact (H o v Hin)]. intros x Hx. apply K. lia.
Qed.
Lemma s17s_LT_L_off : forall cx c m o v, In (o, v) (LT_L cx c m) -> 0 <= o <= 216.
Proof.
intros cx c m o v Hin. unfold LT_L in Hin. cbn [In] in Hin.
repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.
Lemma s17s_rdword_rng : forall (W : world SEGS) mem a v, rdword (rdW W mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros W mem a v Hw. unfold rdword in Hw.
destruct (rdW W mem a) as [b0|] eqn:E0; [|cbn in Hw; discriminate Hw].
destruct (rdW W mem (a + 1)) as [b1|] eqn:E1; [|cbn in Hw; discriminate Hw].
destruct (rdW W mem (a + 2)) as [b2|] eqn:E2; [|cbn in Hw; discriminate Hw].
destruct (rdW W mem (a + 3)) as [b3|] eqn:E3; [|cbn in Hw; discriminate Hw].
destruct (rdW W mem (a + 4)) as [b4|] eqn:E4; [|cbn in Hw; discriminate Hw].
destruct (rdW W mem (a + 5)) as [b5|] eqn:E5; [|cbn in Hw; discriminate Hw].
destruct (rdW W mem (a + 6)) as [b6|] eqn:E6; [|cbn in Hw; discriminate Hw].
destruct (rdW W mem (a + 7)) as [b7|] eqn:E7; [|cbn in Hw; discriminate Hw].
cbn in Hw. injection Hw as <-.
apply sa_aview_rng in E0, E1, E2, E3, E4, E5, E6, E7. lia.
Qed.
(* an 8-byte chunk of a word the reader shows, as any sv that denotes it *)
Lemma s17s_sv_chunk : forall (W : world SEGS) mem E e base off v,
  rdword (rdW W mem) (base + off) = Some v -> sv_denot E e = Z_to_bv 64 v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 e)).
Proof.
intros W mem E e base off v Hw He. pose proof (s17s_rdword_rng W mem _ v Hw) as Hr.
apply (chunk_ok_val SEGS E _ base off 8 e v); [exact He | cbn; lia | cbn; lia |].
exact (val_mem_of_rdword SEGS _ _ _ _ Hw).
Qed.
Lemma s17s_word_chunk : forall (W : world SEGS) mem E (n : nat) base off v,
  rdword (rdW W mem) (base + off) = Some v -> ew E n = Z_to_bv 64 v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros W mem E n base off v Hw He. apply (s17s_sv_chunk W mem E _ base off v Hw).
cbn [sv_denot]. rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma s17s_lit_chunk : forall (W : world SEGS) mem E base off v,
  rdword (rdW W mem) (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SLit v))).
Proof. intros W mem E base off v Hw. apply (s17s_sv_chunk W mem E _ base off v Hw). reflexivity. Qed.
(* a byte the reader shows, as a 1-byte literal chunk *)
Lemma s17s_byte_chunk : forall (W : world SEGS) mem E base off v,
  rdW W mem (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 1 (SLit v))).
Proof.
intros W mem E base off v Hb. pose proof (sa_aview_rng _ _ _ _ _ Hb) as Hr.
apply (chunk_ok_val SEGS E _ base off 1 (SLit v) v); [reflexivity | cbn; lia | cbn; lia |].
exact (s17_val_mem1 (w_H W) mem _ v Hb).
Qed.
(* a 4-byte value the reader shows, as a 4-byte literal chunk *)
Lemma s17s_rd32_chunk : forall (W : world SEGS) mem E base off v, 0 <= v < 2 ^ 32 ->
  rd32 (rdW W mem) (base + off) v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 4 (SLit v))).
Proof.
intros W mem E base off v Hv Hb.
apply (chunk_ok_val SEGS E _ base off 4 (SLit v) v); [reflexivity | cbn; lia | cbn; lia |].
exact (val_mem_of_rd32 SEGS _ _ _ _ Hb).
Qed.
(* a 1-byte chunk whose value is the word -8 reads 0xf8 *)
Lemma s17s_rd_f8 : forall (W : world SEGS) mem E base off e,
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 1 e)) ->
  sv_denot E e = Z_to_bv 64 (-8) -> rdW W mem (base + off) = Some 248.
Proof.
intros W mem E base off e Hc He. destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb1, Hb2. rewrite He in Hb1. injection Hb1 as <-.
unfold aview. rewrite Z.add_0_r in Hb2. rewrite Hb2. cbn [option_map].
vm_compute. reflexivity.
Qed.
(* the engine's s4 at 0x85524 (`sub s4,a3,a0`): N1 - NP *)
Lemma s7_U_sub : forall E na nb a b, ew E na = Z_to_bv 64 a -> ew E nb = Z_to_bv 64 b -> 0 <= b <= a -> a < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff nb 0) (SLit (-1))) (SOff na 0)) = Z_to_bv 64 (a - b).
Proof.
intros E na nb a b Ha Hb Hab Ha64. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit.
rewrite (U_atom E na a Ha), (U_atom E nb b Hb) by lia.
change (zcanon (-1)) with (2 ^ 64 - 1).
unfold zcanon, M64. rewrite Zplus_mod_idemp_l.
replace (b * (2 ^ 64 - 1) + a) with ((a - b) + b * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
(* the engine's returned' at 0x854fc (`and a1,a0,a1` of `seqz (n xor m->n)` and 176(s1)): returned, as n = m->n *)
Lemma s7_ret_den : forall E (L : nat) (b : bool), ew E 10 = Z_to_bv 64 (Z.of_nat L) ->
  ew E 41 = Z_to_bv 64 (Z.of_nat L) -> ew E 40 = Z_to_bv 64 (seg_spec.b2z b) -> (L <= 32)%nat ->
  sv_denot E (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_XOR (SOff 10 0) (SExt true 32 (SOff 41 0))) (SLit 1)) (SOff 40 0)) =
  Z_to_bv 64 (seg_spec.b2z b).
Proof.
intros E L b H10 H41 H40 HL. cbn [sv_denot]. rewrite H10, H41, H40, !Z.add_0_r, !Z_to_bv_bv_unsigned.
destruct b; do 33 (destruct L as [|L]; [apply bv_eq; vm_compute; reflexivity|]); lia.
Qed.
Lemma s17s_LT_L_off2 : forall cx c m o v, In (o, v) (LT_L cx c m) -> 0 <= o <= 168 \/ 184 <= o <= 216.
Proof.
intros cx c m o v Hin. unfold LT_L in Hin. cbn [In] in Hin.
repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.
(* a register of a st_ok state, its sv not normalised (prreg without prreg_norm) *)
Ltac prreg_raw HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.
Lemma s7_np_le : forall cx f, 0 <= x_np cx f <= x_n1 cx f.
Proof.
intros cx f. destruct (s17_cur_S (x_pl cx) f) as [_ L]. unfold x_np, x_n1.
assert (0 <= seg_spec.seg_turn_np (x_pl cx) f) by (unfold seg_spec.seg_turn_np; lia). lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
(* the image facts lt_img needs at a later reader (image B's record, lib/B/Prog/SegRecBase.v) *)
Hypothesis IMGF : SegRecBase.seg_img_facts SEGS B.
(* the runtime's record of image B (lib/B/YF0m.v): the stack-protector cells at every AR state (SegRecCells) *)
Hypothesis HBS : SegBSyms B.
(* S07's: the meter across set_fs (the callee's sa_noalloc), the free wrapper (the listing's trampoline) and its
   rule, the parse's contract at its listing entry, the listing's program call targets *)
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TL : PALib B.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis HPARSE : forall fx0 : YK11.FPState, @reac_segconf_parse_c.reac_segconf_parse_contract fx0 rc SK SEGS B
  (BASE + AF_reac_segconf_parse) STK_reac_segconf_parse RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Hypothesis SIGP : seg_sig_prog (PI := PI).

(* ---------------- the frame at a cut: where the side-stack frame and its shadow lie ---------------- *)
Lemma s17s_frame : forall cx ly S (W : world SEGS) mem md k,
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  In (LT_FCLS, x_fpos cx) (frames S) /\ frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx /\
  in_app (x_fr cx) 512 /\ 4096 <= x_fr cx /\ x_fr cx + 512 <= 2 ^ 47 /\
  x_sh cx = 2147450880 + x_fr cx / 8 /\
  (forall i, 0 <= i < 64 -> apresent (w_H W) mem (x_sh cx + i)).
Proof.
intros cx ly S W mem md k HB HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx)
  by (unfold x_fr; exact (s17_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _)).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (al_frames _ _ LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR Hin) as (_ & Happ & _ & Hsh).
rewrite EF, F512 in Happ. rewrite EF, F512 in Hsh.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Esh : x_sh cx = 2147450880 + x_fr cx / 8) by (unfold x_sh, shadow_addr, SHADOW_OFF; lia).
pose proof Happ as Happ'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ'.
split; [exact Hin|]. split; [exact EF|]. split; [exact Happ|]. split; [lia|]. split; [lia|].
split; [exact Esh|].
intros i Hi. unfold x_sh. exact (proj1 (Hsh i ltac:(change (512 / 8) with 64; lia))).
Qed.

(* a window inside the frame's shadow is the walk's to write: its own class-3 frame *)
Lemma s17s_awr_sh : forall E cx ly r rs STK sp0 FP bl0 blc fr0 (n : nat),
  YP09.r_base r = Some n -> 0 <= YP09.r_wlo r -> YP09.r_whi r <= 64 -> bv_unsigned (ew E n) = x_sh cx ->
  frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx ->
  awr_ok SEGS B E rs STK sp0 FP bl0 blc fr0 ly [(LT_FCLS, x_fpos cx)] ->
  awr_ok SEGS B E (r :: rs) STK sp0 FP bl0 blc fr0 ly [(LT_FCLS, x_fpos cx)].
Proof.
intros E cx ly r rs STK sp0 FP bl0 blc fr0 n Hb Hlo Hhi U Hfa Hrs.
eapply awr_ok_cons_gen; [exact Hb | exact U | | exact Hrs].
intros a Ha.
right; right; right; left. exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. right.
unfold in_zr. cbn [fst snd]. rewrite Hfa. change (fs_frame_bytes LT_FCLS / 8) with 64. unfold x_sh in Ha. lia.
Qed.

(* S08's cut facts: the label's five shadow bytes SH(FR) + 12 .. 16 are now 0xf8 and every other byte is as at
   K85530, so the frame holds the entry pattern LFO0 and the rest of the cut is carried *)
Lemma s17s_relabel {fx : YK11.FPState} : forall cx ly S (W : world SEGS) regs mem md regs2 mem2 md2 k acc rem c m L st,
  lt_base B MT cx ->
  lt_core B MT cx ly S W regs mem md k acc rem LFO_L [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem2 md2 k ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 12 <= a < x_sh cx + 17) -> rdW W mem2 a = rdW W mem a) ->
  (forall o, 12 <= o < 17 -> rdW W mem2 (x_sh cx + o) = Some 248) ->
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  (forall o v, In (o, v) L -> 0 <= o <= 216) -> lt_slots cx (rdW W mem) L -> lt_cm (rdW W mem) c m st ->
  lt_core B MT cx ly S W regs2 mem2 md2 k acc rem LFO0 [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem2) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem2) m seg_spec.SEG_M_SIZE /\
  lt_slots cx (rdW W mem2) L /\ lt_cm (rdW W mem2) c m st.
Proof.
intros cx ly S W regs mem md regs2 mem2 md2 k acc rem c m L st HB HC HJ2 P2 P3 P4 P8 P9 KK W5 Hc Hm HLo SLOTS HCM.
pose proof HC as ((HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184) & HI & HBL & HBUD).
pose proof (s17_sp B MT cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct (s17s_frame cx ly S W mem md k HB HJ) as (Hin & HFA & Fapp & F4096 & F47 & Esh & SHP).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ2) as HAR2.
assert (NWs : forall a, x_s1 cx <= a -> ~ (x_sh cx + 12 <= a < x_sh cx + 17)) by (intros a Ha; rewrite Esh; lia).
assert (NWa : forall p n a, in_app p n -> p <= a < p + n -> ~ (x_sh cx + 12 <= a < x_sh cx + 17)).
{ intros p n a Hp Ha Hw. rewrite Esh in Hw.
  exact (fshadow_not_app (x_fr cx) 64 p n a ltac:(lia) ltac:(lia) Hp ltac:(lia) Ha). }
assert (Kst : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W mem2 a = rdW W mem a)
  by (intros a Ha; apply KK; [lia | apply NWs; lia]).
assert (Kfr : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W mem2 a = rdW W mem a)
  by (intros a Ha; apply KK; [lia | exact (NWa _ _ a Fapp Ha)]).
assert (Kim : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> rdW W mem2 a = rdW W mem a).
{ intros a Hia _ _. pose proof (pa_img_range a Hia) as Hr. unfold kImgEnd in Hr.
  apply KK; [lia | rewrite Esh; lia]. }
pose proof Hc as (Hinc & _ & _ & _). pose proof Hm as (Hinm & _ & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ c _ (proj1 HJ) Hinc) as (_ & Hc4 & Hcc & Hcapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ m _ (proj1 HJ) Hinm) as (_ & Hm4 & Hmc & Hmapp & _).
change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE in Hcc, Hcapp.
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc, Hmapp.
split; [|split; [|split; [|split]]].
- split; [|split; [exact (s17_img_kept B IMGF cx W mem2 (rdW W mem) Kim (s17_ssp B IMGF HBS ly S W mem2 md2 HAR2) HI)
    | split; [exact HBL | exact HBUD]]].
  split; [exact HJ2|]. rewrite P2, P3, P4, P8, P9.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (s17_word_kept (rdW W mem)); [|exact (HSV i r Hi)]. intros x Hx. apply Kst. lia. }
  split; [apply (s17_word_kept (rdW W mem)); [|exact HH0]; intros x Hx; apply Kfr; lia|].
  split; [apply (s17_word_kept (rdW W mem)); [|exact HH8]; intros x Hx; apply Kfr; lia|].
  split; [apply (s17_word_kept (rdW W mem)); [|exact HH16]; intros x Hx; apply Kfr; lia|].
  split; [apply (s17_word_kept (rdW W mem)); [|exact HFL]; intros x Hx; apply Kfr; unfold LT_FLAGW in *; lia|].
  split; [apply (s17_word_kept (rdW W mem)); [|exact H200]; intros x Hx; apply Kst; lia|].
  split; [|apply (s17_word_kept (rdW W mem)); [|exact H184]; intros x Hx; apply Kst; lia].
  intros i Hi. rewrite lt_fsh_len in Hi.
  destruct (Nat.ltb_spec i 12) as [Hlo|Hlo]; [|destruct (Nat.ltb_spec i 17) as [Hhi|Hhi]].
  + rewrite KK by (rewrite ?Esh; lia). rewrite (s17s_fsh_same i Hi ltac:(lia)). apply HSH. rewrite lt_fsh_len. exact Hi.
  + rewrite (s17s_fsh_f8 i ltac:(lia)). apply W5. lia.
  + rewrite KK by (rewrite ?Esh; lia). rewrite (s17s_fsh_same i Hi ltac:(lia)). apply HSH. rewrite lt_fsh_len. exact Hi.
- exact (s17_hblk B ly S W mem2 md2 c _ HAR2 Hinc).
- exact (s17_hblk B ly S W mem2 md2 m _ HAR2 Hinm).
- apply (s17s_slots_kept cx (rdW W mem)); [exact HLo | | exact SLOTS]. intros a Ha. apply Kst. lia.
- destruct HCM as [HRC HMC]. split.
  + apply (s17_rconf_kept (rdW W mem)); [exact HRC|].
    intros i Hi. apply KK; [unfold seg_spec.SEG_C_SIZE in *; lia | exact (NWa c seg_spec.SEG_C_SIZE (c + i) Hcapp ltac:(lia))].
  + apply (s17_mconf_kept (rdW W mem)); [exact HMC|].
    intros i Hi. apply KK; [unfold seg_spec.SEG_M_SIZE in *; lia | exact (NWa m seg_spec.SEG_M_SIZE (m + i) Hmapp ltac:(lia))].
Qed.

Section s8.
Context {fx : YK11.FPState}.
(* S08's seed at 0x85530: the five label shadow bytes SH(FR) + 12 .. 16 as a write window off the atom 32 = SH(FR),
   and the slot 184(s1) = SH(FR) *)
Definition s8_rsh : YP09.region := YP09.mkRegion (Some 32%nat) 12 17 12 17 [].
Definition s8_rsl : YP09.region := YP09.mkRegion (Some 9%nat) 184 192 0 0 [YP09.mkChunk 184 (CVal 8 (SOff 32 0))].
Definition s8_ss : sstate := mkSS LO_K85530 sr_atoms [s8_rsh; s8_rsl] None (mkFacts [] [] []).

(* what a plain run of S08 keeps: every byte outside the label's shadow window *)
Ltac s8_keep cx HFr U32 U9 K :=
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => x_sh cx + 12 <= a < x_sh cx + 17) HFr
    ltac:(intros b wlo whi a Hin' Hrr; vm_compute in Hin';
          repeat (destruct Hin' as [Hq | Hin'];
                  [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U32, ?U9 in Hrr; cbv beta; lia |]);
          destruct Hin')) as K.
Ltac s8_w5 HS U32 cx W ms W5 :=
  let RG := fresh "RG" in
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG; cbn [ms_mem restrict] in RG;
  assert (W5 : forall o, 12 <= o < 17 -> rdW W (ms_mem ms) (x_sh cx + o) = Some 248);
  [ let RGc := fresh "RGc" in destruct RG as (_ & _ & _ & RGc); cbn [YP09.r_base base_val YP09.r_chunks] in RGc;
    rewrite U32 in RGc;
    let o := fresh "o" in let Ho := fresh "Ho" in
    intros o Ho; assert (Ho' : o = 12 \/ o = 13 \/ o = 14 \/ o = 15 \/ o = 16) by lia;
    destruct Ho' as [-> | [-> | [-> | [-> | ->]]]];
    (eapply s17s_rd_f8; [apply (proj1 (Forall_forall _ _) RGc); cbn [In]; repeat (first [left; reflexivity | right])
                        | first [reflexivity | (apply bv_eq; vm_compute; reflexivity)]])
  | ].

Lemma lt_seg_S08 : lt_seg_S08_stmt (fx := fx) B MT.
Proof.
intros f HN HX. unfold LT_K85530_stmt.
intros cx ly S W regs mem md k acc c m HBASE HFRM Hf HCORE HBc HBm R18 R20 R21 R22 R24 R25 R26 SLOTS HCM HCNT.
pose proof HCORE as ((HJ & R2 & R3 & R4 & R8 & R9 & _ & _ & _ & _ & _ & _ & _ & H184) & _).
pose proof (s17_sp B MT cx HBASE) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct (s17s_frame cx ly S W mem md k HBASE HJ) as (Hin & HFA & Fapp & F4096 & F47 & Esh & SHP).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg regs [Z_to_bv 64 (x_sh cx)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (x_sh cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply YP03.unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = x_sh cx)
  by (rewrite E32; apply YP03.unsigned_lit_small; rewrite Esh; lia).
assert (HS : st_ok_pi SEGS VAL E s8_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K85530)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
      cbn [s8_rsh s8_rsl YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U32. split; [lia|]. split; [rewrite Esh; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply SHP. lia.
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor]. exact (s17s_word_chunk W mem E 32 (x_s1 cx) 184 (x_sh cx) H184 E32).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map s8_rsh s8_rsl YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite Esh. repeat split; lia.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
assert (AWR0 : awr_ok SEGS B E (ss_mem s8_ss) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
  (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly S) (frames (x_S cx)) ly [(LT_FCLS, x_fpos cx)]).
{ unfold s8_ss. cbn [ss_mem].
  apply (s17s_awr_sh E cx ly s8_rsh [s8_rsl] _ _ _ _ _ _ 32%nat); [reflexivity | cbn; lia | cbn; lia | exact U32 | exact HFA |].
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
unfold cfg_at. change (w64 (BASE + LO_K85530)) with (Z_to_bv 64 (BASE + LO_K85530)).
(* 0x85530 .. 0x8554c: a0 := 184(s1) = SH(FR), a1 := -8, the label's five shadow bytes := 0xf8, a4 := 1; it stops at
   the latch bne s9, s2 (0x85550) *)
paj_run_sh (SRr_run_pi_AJ (fx := fx) B LAWS) HS HJ.
{ exact AWR0. }
cbn [ms_mem mkst] in HF, HFr, HG.
s8_keep cx HFr U32 U9 K1.
clear HF HFr HG. rename ms into ms1.
pose proof (s17_nfiles_range (x_pl cx) : 1 <= x_nf cx <= 4) as NF.
psrr_branch_pi (SRr_run_pi_AJ (fx := fx) B LAWS) (paj_branch (fx := fx) (PI := PI)) HS.
- (* taken: f + 1 <> nfiles, the next turn at 0x85110 *)
  assert (Hnl : Z.of_nat (Datatypes.S f) <> x_nf cx).
  { rewrite branch_ne_U in Hc.
    rewrite (U_atom E 25 (Z.of_nat (Datatypes.S f))), (U_atom E 18 (x_nf cx)) in Hc
      by first [rewrite (EE 18%nat 18%bv eq_refl); exact R18 | rewrite (EE 25%nat 25%bv eq_refl); exact R25 | lia].
    destruct (Z.of_nat (Datatypes.S f) =? x_nf cx) eqn:Ee; [discriminate Hc|]. apply Z.eqb_neq in Ee. exact Ee. }
  paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx) B LAWS) HS HJ LO_K85110.
  { apply (s17s_awr_skel SEGS B E (ss_mem s8_ss)); [vm_compute; reflexivity | exact AWR0]. }
  s8_keep cx HFr U32 U9 K2.
  clear HF HFr HG.
  s8_w5 HS U32 cx W ms W5.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (14%bv : bv 5) P14. prreg HS (18%bv : bv 5) P18. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (24%bv : bv 5) P24.
  prreg HS (25%bv : bv 5) P25.
  rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
  rewrite (EE 8%nat 8%bv eq_refl) in P8. rewrite (EE 9%nat 9%bv eq_refl) in P9.
  rewrite (EE 18%nat 18%bv eq_refl) in P18. rewrite (EE 20%nat 20%bv eq_refl) in P20.
  rewrite (EE 21%nat 21%bv eq_refl) in P21. rewrite (EE 22%nat 22%bv eq_refl) in P22.
  rewrite (EE 24%nat 24%bv eq_refl) in P24. rewrite (EE 25%nat 25%bv eq_refl) in P25.
  pmkst HS.
  destruct (s17s_relabel cx ly S W regs mem md (ms_regs ms) (ms_mem ms) _ k acc _ c m
    (LT_L cx c m ++ [(176, seg_spec.b2z (seg_spec.seg_ret (x_af cx f)))]) (x_af cx f) HBASE HCORE HJ
    P2 P3 P4 P8 P9 ltac:(intros a Ha Hn; rewrite (K2 a Ha Hn); exact (K1 a Ha Hn)) W5 HBc HBm
    ltac:(intros o v Hov; apply in_app_or in Hov as [Hov | [Hov | []]];
          [exact (s17s_LT_L_off cx c m o v Hov) | injection Hov as <- _; lia]) SLOTS HCM)
    as (HCORE2 & Hc2 & Hm2 & SLOTS2 & HCM2).
  assert (EAF : x_af cx f = x_st cx (Datatypes.S f))
    by (unfold x_af, x_st; symmetry; apply s17_next; change (seg_spec.seg_nfiles (x_pl cx)) with (x_nf cx); lia).
  rewrite EAF in SLOTS2, HCM2, HCNT.
  exact (HN fx cx ly S W _ _ _ k acc c m HBASE HFRM ltac:(lia) HCORE2 Hc2 Hm2
    ltac:(rewrite P14; reflexivity)
    ltac:(rewrite P18; exact R18) ltac:(rewrite P20; exact R20)
    ltac:(rewrite P21; exact R21) ltac:(rewrite P22; exact R22) ltac:(rewrite P24; exact R24)
    ltac:(rewrite P25; exact R25) SLOTS2 HCM2 HCNT).
- (* not taken: f + 1 = nfiles, out of the loop to 0x855c8 (j at 0x85554) *)
  assert (Hlast : Z.of_nat (Datatypes.S f) = x_nf cx).
  { rewrite branch_ne_U in Hc.
    rewrite (U_atom E 25 (Z.of_nat (Datatypes.S f))), (U_atom E 18 (x_nf cx)) in Hc
      by first [rewrite (EE 18%nat 18%bv eq_refl); exact R18 | rewrite (EE 25%nat 25%bv eq_refl); exact R25 | lia].
    destruct (Z.of_nat (Datatypes.S f) =? x_nf cx) eqn:Ee; [|discriminate Hc]. apply Z.eqb_eq in Ee. exact Ee. }
  paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx) B LAWS) HS HJ LO_K855c8.
  { apply (s17s_awr_skel SEGS B E (ss_mem s8_ss)); [vm_compute; reflexivity | exact AWR0]. }
  s8_keep cx HFr U32 U9 K2.
  clear HF HFr HG.
  s8_w5 HS U32 cx W ms W5.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (26%bv : bv 5) P26.
  rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
  rewrite (EE 8%nat 8%bv eq_refl) in P8. rewrite (EE 9%nat 9%bv eq_refl) in P9.
  rewrite (EE 21%nat 21%bv eq_refl) in P21. rewrite (EE 22%nat 22%bv eq_refl) in P22.
  rewrite (EE 26%nat 26%bv eq_refl) in P26.
  pmkst HS.
  destruct (s17s_relabel cx ly S W regs mem md (ms_regs ms) (ms_mem ms) _ k acc _ c m
    (LT_L cx c m ++ [(176, seg_spec.b2z (seg_spec.seg_ret (x_af cx f)))]) (x_af cx f) HBASE HCORE HJ
    P2 P3 P4 P8 P9 ltac:(intros a Ha Hn; rewrite (K2 a Ha Hn); exact (K1 a Ha Hn)) W5 HBc HBm
    ltac:(intros o v Hov; apply in_app_or in Hov as [Hov | [Hov | []]];
          [exact (s17s_LT_L_off cx c m o v Hov) | injection Hov as <- _; lia]) SLOTS HCM)
    as (HCORE2 & Hc2 & Hm2 & SLOTS2 & HCM2).
  assert (EAF : x_af cx f = x_run cx)
    by (unfold x_af, x_run; symmetry; apply s17_run_end; exact Hlast).
  rewrite EAF in SLOTS2, HCM2.
  assert (E6 : 6 + 2 * (x_nf cx - Z.of_nat (Datatypes.S f)) = 6) by lia. rewrite E6 in HCORE2.
  assert (SL3 : lt_slots cx (rdW W (ms_mem ms)) (LT_LC cx c m ++
    [(112, x_fr cx + FO_R); (120, x_fr cx + FO_PROBE); (176, seg_spec.b2z (seg_spec.seg_ret (x_run cx)))])).
  { apply (s17s_slots_sub cx _ (LT_L cx c m ++ [(176, seg_spec.b2z (seg_spec.seg_ret (x_run cx)))])); [|exact SLOTS2].
    intros x Hx. unfold LT_LC in Hx. cbn [In app] in Hx. apply in_or_app.
    repeat (destruct Hx as [<- | Hx];
      [first [solve [left; unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right])]
             | solve [right; cbn [In]; left; reflexivity]] |]).
    destruct Hx. }
  exact (HX fx cx ly S W _ _ _ k acc c m HBASE HFRM HCORE2 Hc2 Hm2
    ltac:(rewrite P21; exact R21) ltac:(rewrite P22; exact R22) ltac:(rewrite P26; exact R26) SL3 HCM2).
Qed.
End s8.

(* ================================ S07: 0x854e0 .. 0x8552c, after the parse returned ================================ *)
(* the return point of the parse (0x854e0, offset 0x720 from BASE) *)
Definition LO_K854e0 : Z := 0x720.
(* the seed at 0x854e0: s1's slots 96 .. 216 (the window 176 .. 184 for returned'), the shadow byte SH(m + 0x2000)
   (atom 18 = s2), m->n at m + 0x2000 (atom 33); the slot values are the atoms 32 .. 41 of the extra list *)
Definition s7_rs1 : YP09.region := YP09.mkRegion (Some 9%nat) 96 224 176 184
  [YP09.mkChunk 96 (CVal 8 (SLit 0)); YP09.mkChunk 104 (CVal 8 (SOff 34 0)); YP09.mkChunk 128 (CVal 8 (SOff 35 0));
   YP09.mkChunk 136 (CVal 8 (SOff 36 0)); YP09.mkChunk 144 (CVal 8 (SOff 37 0)); YP09.mkChunk 152 (CVal 8 (SOff 38 0));
   YP09.mkChunk 160 (CVal 8 (SOff 39 0)); YP09.mkChunk 176 (CVal 8 (SOff 40 0)); YP09.mkChunk 192 (CVal 8 (SOff 32 0));
   YP09.mkChunk 216 (CVal 8 (SOff 33 0))].
Definition s7_rsh : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition s7_rmn : YP09.region := YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 41 0))].
Definition s7_ss : sstate := mkSS LO_K854e0 sr_atoms [s7_rs1; s7_rsh; s7_rmn] None (mkFacts [] [] []).

(* the C string and its slack carried to a reader that agrees on them *)
Lemma s17s_str_kept : forall (rd rd' : reader) p s,
  (forall a, p <= a < p + Z.of_nat (length s) + 8 -> rd' a = rd a) -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros rd rd' p s K ((Hz & Hn) & Ht). split; [split; [|exact Hn]|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite K by lia. exact (Hz i ltac:(rewrite length_app; cbn [length]; lia)).
- intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)) as M. rewrite K by lia. exact (Ht x Hx).
Qed.
(* reader_pre at the parse's call (0x854dc): every conjunct from the cut's facts at the call's reader *)
Lemma s7_reader_pre {fx : YK11.FPState} : forall cx ly S (W : world SEGS) regs mem md k acc rem o O c t f mc,
  lt_core B MT cx ly S W regs mem md k acc rem o O -> Z.of_nat f + 1 = x_nf cx ->
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk B ly S (rdW W mem) t (x_tn cx f) ->
  (t, x_tn cx f) <> (c, seg_spec.SEG_C_SIZE) ->
  sa_rconf (rdW W mem) c (seg_spec.seg_rc (x_st cx f)) -> sa_str (rdW W mem) t (seg_spec.seg_txt (x_pl cx) f) ->
  lt_cnt (Datatypes.S f) (seg_spec.seg_rc (x_st cx f)) mc -> sa_frm0 ->
  reac_segconf_parse_file_c.reader_pre SEGS B seg_litA_rc catA gotwA guardA ly S (rdW W mem) c t
    (seg_spec.seg_rc (x_st cx f)) (seg_spec.seg_txt (x_pl cx) f).
Proof.
intros cx ly S W regs mem md k acc rem o O c t f mc HC Hf Hc Ht Hne HRC HSTR HCNT HFRM.
pose proof HC as ((HJ & _) & (HRO & HIM & HGI) & _ & _).
pose proof (proj1 HJ) as HAR.
destruct HIM as (_ & _ & _ & HLR & HCAT & _ & _ & _ & HSSP & _).
pose proof Hc as (Hinc & Hc4 & Hc16 & Hcaddr).
pose proof Ht as (Hint & Ht4 & Ht16 & Htaddr).
pose proof (s17_nfiles_range (x_pl cx) : 1 <= x_nf cx <= 4) as NF.
destruct HCNT as (G1 & G2 & G3 & _).
destruct (s17_txt_ok (x_pl cx) f) as (_ & Hlen & _).
set (s := seg_spec.seg_txt (x_pl cx) f) in *.
assert (Etn : x_tn cx f = Z.of_nat (length s) + 1) by (unfold x_tn, seg_spec.seg_txt_n; reflexivity).
pose proof (sep_blocks SEGS B LAWS ly S W mem md t _ c _ HAR Hint Hinc Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE in Hd.
assert (Hreq : req_size (x_tn cx f) = Z.of_nat (length s) + 1)
  by (rewrite Etn; unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length s) + 1) 0); lia).
rewrite Hreq in Hd.
unfold reac_segconf_parse_file_c.reader_pre.
split; [lia|]. split; [exact Hc16|]. split; [exact HRC|].
split; [exists c, seg_spec.SEG_C_SIZE; split; [exact Hinc | lia]|].
split; [exact Hcaddr|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [exact HSTR|].
split; [apply Nat2Z.inj_le; change (Z.of_nat 65535) with 65535%Z; exact Hlen|].
split; [exists t, (x_tn cx f); split; [exact Hint | rewrite Etn; lia]|].
split; [rewrite <- Etn; exact Htaddr|].
split.
{ unfold sa_disj, seg_spec.cstr_span, seg_spec.SEG_C_SIZE in *.
  pose proof (Z.mod_pos_bound (- (t + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as M.
  pose proof (Z.div_mod (- (t + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as D.
  pose proof (Z.div_mod c 16 ltac:(lia)) as Dc. pose proof (Z.div_mod t 16 ltac:(lia)) as Dt.
  rewrite Hc16 in Dc. rewrite Ht16 in Dt. lia. }
split; [exact HFRM|]. split; [exact HSSP|]. split; [exact HCAT|].
intros x Hx. exact (proj1 (HLR x ltac:(unfold LTOI_RC_LITS; apply in_or_app; left; exact Hx))).
Qed.
(* what the parse keeps: every byte at or above S1 (its window is below S1, its footprint in c's block) and every
   byte of a block live on both sides outside c's block *)
Lemma s7_callee_keep : forall cx lyc Sc (W : world SEGS) memc mdc ly2 S2 (W2 : world SEGS) mem2 md2 c k1,
  lt_base B MT cx ->
  ajournal SEGS B STK_reac_segconf_parse (x_s1 cx) (seg_spec.RC_PARSE_W c) lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
  4096 <= c -> c + seg_spec.SEG_C_SIZE <= alloc_ceiling ->
  (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memc a) /\
  (forall p n i, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
     (p + i < c \/ c + seg_spec.SEG_C_SIZE <= p + i) -> rdW W2 mem2 (p + i) = rdW W memc (p + i)).
Proof.
intros cx lyc Sc W memc mdc ly2 S2 W2 mem2 md2 c k1 HB HJc Hc4 Hcc.
pose proof (s17_sp B MT cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _).
assert (NF : forall a, (a < c \/ c + seg_spec.SEG_C_SIZE <= a) -> ~ inFP (seg_spec.RC_PARSE_W c) a).
{ intros a Ha (r & Hr & Hra). unfold seg_spec.RC_PARSE_W in Hr. cbn [In] in Hr.
  unfold seg_spec.RC_N, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.RC_READING, seg_spec.RC_GEN,
    seg_spec.SEG_C_SIZE in *.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hra; lia. }
split.
- intros a Ha. apply F1; [lia | lia | apply NF; right; unfold seg_spec.SEG_C_SIZE in *; lia].
- intros p n i Hp Hp2 Hi Ho. apply (F2 p n i); [exact Hp | exact Hp2 | exact Hi | apply NF; exact Ho].
Qed.

Section s7t.
Context {fx : YK11.FPState}.
Lemma s7_tail : forall f, LTA_K85530 B MT f ->
  forall cx ly S (W : world SEGS) regs mem md k acc (c m t : Z),
  lt_base B MT cx -> sa_frm0 -> Z.of_nat f + 1 = x_nf cx ->
  lt_core B MT cx ly S W regs mem md k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
    [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk B ly S (rdW W mem) t (x_tn cx f) ->
  getr regs 10 = w64 (Z.of_nat (length (SegModel.mc_seg (seg_spec.seg_mc (x_af cx f))))) ->
  getr regs 18 = w64 (shadow_addr (m + seg_spec.MC_N)) -> getr regs 23 = w64 t ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++
    [(128, (m + seg_spec.MC_N) / 8); (136, Z.of_nat f + 1); (144, x_at cx f + x_np cx f); (152, x_np cx f);
     (160, x_n1 cx f); (176, seg_spec.b2z (seg_spec.seg_ret (x_af cx f)))]) ->
  lt_cm (rdW W mem) c m (x_af cx f) ->
  lt_cnt (Datatypes.S f) (seg_spec.seg_rc (x_af cx f)) (seg_spec.seg_mc (x_af cx f)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_K854e0)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros f HX cx ly S W regs mem md k acc c m t HBASE HFRM Hf HCORE HBc HBm HBt R10 R18 R23 SLOTS HCM HCNT.
pose proof HCORE as ((HJ & R2 & R3 & R4 & R8 & R9 & _ & _ & _ & _ & _ & _ & _ & H184) & _).
pose proof (s17_sp B MT cx HBASE) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (s17_nfiles_range (x_pl cx) : 1 <= x_nf cx <= 4) as NF.
set (nmn := Z.of_nat (length (SegModel.mc_seg (seg_spec.seg_mc (x_af cx f))))) in *.
destruct HCM as [HRC HMC].
destruct (s17_mn (rdW W mem) m _ HMC) as [HMN H32]. fold nmn in HMN.
pose proof (s17_mn_shadow B ly S (rdW W mem) m HBm) as HSH0.
pose proof HBm as (Hinm & Hm4 & Hm16 & Hmaddr).
destruct (al_blocks _ _ LAWS _ _ _ _ _ m _ (proj1 HJ) Hinm) as (_ & _ & Hmc & Hmapp & _).
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc, Hmapp.
pose proof HBc as (Hinc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ c _ (proj1 HJ) Hinc) as (_ & Hc4 & Hcc & Hcapp & _).
change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE in Hcc, Hcapp.
destruct (s17s_frame cx ly S W mem md k HBASE HJ) as (HinF & HFA & Fapp & F4096 & F47 & Esh & SHP).
pose proof HCORE as (_ & _ & HBL & HBUD).
pose proof (s7_np_le cx f) as NPLE.
assert (SL : forall o v, In (o, v) (LT_L cx c m ++
    [(128, (m + seg_spec.MC_N) / 8); (136, Z.of_nat f + 1); (144, x_at cx f + x_np cx f); (152, x_np cx f);
     (160, x_n1 cx f); (176, seg_spec.b2z (seg_spec.seg_ret (x_af cx f)))]) ->
  rdword (rdW W mem) (x_s1 cx + o) = Some v) by exact SLOTS.
assert (SLR : forall o v, In (o, v) (LT_L cx c m) -> rdword (rdW W mem) (x_s1 cx + o) = Some v)
  by (intros o v Hin; apply SL; apply in_or_app; left; exact Hin).
pose proof (SLR 96 0 ltac:(unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right]))) as S96.
pose proof (SLR 104 (x_nf cx) ltac:(unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right]))) as S104.
pose proof (SLR 192 m ltac:(unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right]))) as S192.
pose proof (SLR 216 (m + seg_spec.MC_N) ltac:(unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right]))) as S216.
pose proof (SL 128 _ ltac:(apply in_or_app; right; left; reflexivity)) as S128.
pose proof (SL 136 _ ltac:(apply in_or_app; right; right; left; reflexivity)) as S136.
pose proof (SL 144 _ ltac:(apply in_or_app; right; right; right; left; reflexivity)) as S144.
pose proof (SL 152 _ ltac:(apply in_or_app; right; right; right; right; left; reflexivity)) as S152.
pose proof (SL 160 _ ltac:(apply in_or_app; right; right; right; right; right; left; reflexivity)) as S160.
pose proof (SL 176 _ ltac:(apply in_or_app; right; right; right; right; right; right; left; reflexivity)) as S176.
set (vret := seg_spec.b2z (seg_spec.seg_ret (x_af cx f))) in *.
set (E := Eimg (Ereg regs [Z_to_bv 64 m; Z_to_bv 64 (m + seg_spec.MC_N); Z_to_bv 64 (x_nf cx);
  Z_to_bv 64 ((m + seg_spec.MC_N) / 8); Z_to_bv 64 (Z.of_nat f + 1); Z_to_bv 64 (x_at cx f + x_np cx f);
  Z_to_bv 64 (x_np cx f); Z_to_bv 64 (x_n1 cx f); Z_to_bv 64 vret; Z_to_bv 64 nmn])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
Local Ltac s7_ex E j := subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ j).
assert (E32 : ew E 32 = Z_to_bv 64 m) by s7_ex E 0%nat.
assert (E33 : ew E 33 = Z_to_bv 64 (m + seg_spec.MC_N)) by s7_ex E 1%nat.
assert (E34 : ew E 34 = Z_to_bv 64 (x_nf cx)) by s7_ex E 2%nat.
assert (E35 : ew E 35 = Z_to_bv 64 ((m + seg_spec.MC_N) / 8)) by s7_ex E 3%nat.
assert (E36 : ew E 36 = Z_to_bv 64 (Z.of_nat f + 1)) by s7_ex E 4%nat.
assert (E37 : ew E 37 = Z_to_bv 64 (x_at cx f + x_np cx f)) by s7_ex E 5%nat.
assert (E38 : ew E 38 = Z_to_bv 64 (x_np cx f)) by s7_ex E 6%nat.
assert (E39 : ew E 39 = Z_to_bv 64 (x_n1 cx f)) by s7_ex E 7%nat.
assert (E40 : ew E 40 = Z_to_bv 64 vret) by s7_ex E 8%nat.
assert (E41 : ew E 41 = Z_to_bv 64 nmn) by s7_ex E 9%nat.
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply YP03.unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = shadow_addr (m + seg_spec.MC_N))
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply YP03.unsigned_lit_small;
      unfold shadow_addr, SHADOW_OFF, seg_spec.MC_N, seg_spec.SEG_M_SIZE in *; lia).
assert (U33 : bv_unsigned (ew E 33) = m + seg_spec.MC_N)
  by (rewrite E33; apply YP03.unsigned_lit_small; unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE in *; lia).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HS : st_ok_pi SEGS VAL E s7_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K854e0)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold region_ok;
      cbn [s7_rs1 s7_rsh s7_rmn YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; unfold STK_LLVMFuzzerTestOneInput; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * exact (s17s_lit_chunk W mem E (x_s1 cx) 96 0 S96).
      * exact (s17s_word_chunk W mem E 34 (x_s1 cx) 104 _ S104 E34).
      * exact (s17s_word_chunk W mem E 35 (x_s1 cx) 128 _ S128 E35).
      * exact (s17s_word_chunk W mem E 36 (x_s1 cx) 136 _ S136 E36).
      * exact (s17s_word_chunk W mem E 37 (x_s1 cx) 144 _ S144 E37).
      * exact (s17s_word_chunk W mem E 38 (x_s1 cx) 152 _ S152 E38).
      * exact (s17s_word_chunk W mem E 39 (x_s1 cx) 160 _ S160 E39).
      * exact (s17s_word_chunk W mem E 40 (x_s1 cx) 176 _ S176 E40).
      * exact (s17s_word_chunk W mem E 32 (x_s1 cx) 192 _ S192 E32).
      * exact (s17s_word_chunk W mem E 33 (x_s1 cx) 216 _ S216 E33).
    + rewrite U18. split; [unfold shadow_addr, SHADOW_OFF, seg_spec.MC_N in *; lia|].
      split; [unfold shadow_addr, SHADOW_OFF, seg_spec.MC_N, seg_spec.SEG_M_SIZE in *; lia|].
      split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (s17s_byte_chunk W mem E _ 0 0). rewrite Z.add_0_r. exact HSH0.
    + rewrite U33. split; [unfold seg_spec.MC_N in *; lia|]. split; [unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE in *; lia|].
      split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 0 4 (SOff 41 0) nmn);
        [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; unfold nmn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS _ _ _ _ HMN).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map s7_rs1 s7_rsh s7_rmn YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U18, U33.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr, SHADOW_OFF, seg_spec.MC_N,
      seg_spec.SEG_M_SIZE in *.
    repeat split; lia.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
assert (AWR0 : awr_ok SEGS B E (ss_mem s7_ss) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
  (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly S) (frames (x_S cx)) ly [(LT_FCLS, x_fpos cx)]).
{ unfold s7_ss. cbn [ss_mem].
  eapply awr_ok_cons_gen; [reflexivity | exact U9 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi s7_rs1] in Ha. left. unfold STK_LLVMFuzzerTestOneInput. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
(* 0x854e0 .. 0x8552c: check 17 (lb of SH(m + 0x2000), 0, its slow path not taken), returned' := (n == m->n) &
   returned at 176(s1), the loads of the turn's slots, s4 := N1 - NP, a0 := text; it stops at jal wrapper_free *)
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
{ exact AWR0. }
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => x_s1 cx + 176 <= a < x_s1 cx + 184) HFr
  ltac:(intros b wlo whi a Hin' Hrr; vm_compute in Hin';
        repeat (destruct Hin' as [Hq | Hin'];
                [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9, ?U18, ?U33 in Hrr; cbv beta; lia |]);
        destruct Hin')) as K1.
clear HF HFr HG. cbv beta in K1.
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as RG. cbn [ms_mem restrict] in RG.
destruct RG as (_ & _ & _ & RGc). cbn [YP09.r_base base_val YP09.r_chunks] in RGc. rewrite U9 in RGc.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10.
rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
rewrite (EE 8%nat 8%bv eq_refl) in P8. rewrite (EE 9%nat 9%bv eq_refl) in P9.
rewrite (EE 23%nat 23%bv eq_refl), R23 in P10.
prreg HS (18%bv : bv 5) P18. prreg_raw HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
prreg HS (22%bv : bv 5) P22. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
rewrite E34 in P18. rewrite E32 in P22. rewrite E37 in P24. rewrite E36 in P25. rewrite E35 in P26.
pose proof (s17s_rdword_rng W mem _ _ S160) as N1R.
rewrite (s7_U_sub E 39 38 (x_n1 cx f) (x_np cx f) E39 E38 NPLE ltac:(lia)) in P20.
pose proof (s17s_rdword_rng W mem _ _ S176) as VR.
assert (S176' : rdword (rdW W (ms_mem ms)) (x_s1 cx + 176) = Some vret).
{ apply (s17_rd_chunk8 E (w_H W) (ms_mem ms) (x_s1 cx) 176 (x_s1 cx + 176)
    (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_XOR (SOff 10 0) (SExt true 32 (SOff 41 0))) (SLit 1)) (SOff 40 0)) vret _ RGc);
    [cbn [In]; left; reflexivity | reflexivity | | exact VR].
  apply (s7_ret_den E _ _ ltac:(rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity) E41 E40 H32). }
pmkst HS.
(* what the run keeps: every byte outside 176(s1) .. 183(s1) *)
assert (KR : s17_kept B cx W mem W (ms_mem ms)).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp.
  split; [|split; [|split]].
  - intros a Ha. apply K1; lia.
  - intros a Hia _ _. pose proof (pa_img_range a Hia) as Hr. unfold kImgEnd in Hr. apply K1; lia.
  - intros a Ha. apply K1; lia.
  - intros i Hi. rewrite Esh. apply K1; lia. }
pose proof (s17_core_carry B MT IMGF HBS cx ly S W regs mem md k acc _ LFO_L _ ly S W (ms_regs ms) (ms_mem ms) _ k acc _ _
  HBASE HCORE HJ P2 P3 P4 P8 P9 KR HBL HBUD) as HC1.
pose proof pa_B_ok as (HB0 & HB1 & _). pose proof pa_base_lo as HBLO.
(* 0x8552c: free(text), the newest block, to 0x85530 *)
apply (s17_free_at B MT MTL IMGF HBS TL AFREE4 cx ly S W (ms_regs ms) (ms_mem ms) _ k acc _ LFO_L t (x_tn cx f)
  [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] (Z_to_bv 64 (BASE + LO_K85530)) _ HBASE HC1).
{ lia. }
{ exact P10. }
{ exact P1. }
{ apply ret_ok_codeptr_v; [unfold LO_K85530; lia | reflexivity]. }
{ rewrite YP03.unsigned_lit_small; unfold LO_K85530; lia. }
intros ly2 S2 W2 regs2 mem2 md2 HC2 HPr KO KHI.
pose proof HC2 as ((HJ2 & _) & _ & HBL2 & _).
pose proof (proj1 HJ2) as HAR2.
assert (Hin2c : In (c, seg_spec.SEG_C_SIZE) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym HBL2)); right; left; reflexivity).
assert (Hin2m : In (m, seg_spec.SEG_M_SIZE) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym HBL2)); left; reflexivity).
assert (KM : forall b n i, In (b, n) [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] -> 0 <= i < n ->
  rdW W2 mem2 (b + i) = rdW W mem (b + i)).
{ intros b n i Hb Hi. rewrite (KO b n i Hb ltac:(destruct Hb as [Hb | [Hb | []]]; injection Hb as <- <-;
    change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE; change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE;
    exact Hi)).
  apply K1; destruct Hb as [Hb | [Hb | []]]; injection Hb as <- <-; unfold seg_spec.SEG_M_SIZE, seg_spec.SEG_C_SIZE in *;
  lia. }
assert (SL2 : lt_slots cx (rdW W2 mem2) (LT_L cx c m ++ [(176, vret)])).
{ intros o v Hino. apply in_app_or in Hino as [Hino | [Hino | []]].
  - pose proof (s17s_LT_L_off2 cx c m o v Hino) as Ho.
    apply (s17_word_kept (rdW W mem)); [|exact (SLR o v Hino)].
    intros q Hq. rewrite KHI by lia. apply K1; lia.
  - injection Hino as <- <-. apply (s17_word_kept (rdW W (ms_mem ms))); [|exact S176'].
    intros q Hq. apply KHI. lia. }
assert (HCM2 : lt_cm (rdW W2 mem2) c m (x_af cx f)).
{ split.
  - apply (s17_rconf_kept (rdW W mem)); [exact HRC|]. intros i Hi. apply (KM c seg_spec.SEG_C_SIZE i); [right; left; reflexivity | exact Hi].
  - apply (s17_mconf_kept (rdW W mem)); [exact HMC|]. intros i Hi. apply (KM m seg_spec.SEG_M_SIZE i); [left; reflexivity | exact Hi]. }
destruct (s17_x_cur_S cx f) as (XC & XN).
Local Ltac s7_pres HPr rb rz := exact (s17_pres_reg _ _ rb rz HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
assert (Q18 : getr regs2 18 = getr (ms_regs ms) 18) by s7_pres HPr (18%bv : bv 5) 18.
assert (Q20 : getr regs2 20 = getr (ms_regs ms) 20) by s7_pres HPr (20%bv : bv 5) 20.
assert (Q21 : getr regs2 21 = getr (ms_regs ms) 21) by s7_pres HPr (21%bv : bv 5) 21.
assert (Q22 : getr regs2 22 = getr (ms_regs ms) 22) by s7_pres HPr (22%bv : bv 5) 22.
assert (Q24 : getr regs2 24 = getr (ms_regs ms) 24) by s7_pres HPr (24%bv : bv 5) 24.
assert (Q25 : getr regs2 25 = getr (ms_regs ms) 25) by s7_pres HPr (25%bv : bv 5) 25.
assert (Q26 : getr regs2 26 = getr (ms_regs ms) 26) by s7_pres HPr (26%bv : bv 5) 26.
replace (5 + 2 * (x_nf cx - Z.of_nat f) - 1) with (6 + 2 * (x_nf cx - Z.of_nat (Datatypes.S f))) in HC2 by lia.
exact (HX fx cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT) c m HBASE HFRM ltac:(lia) HC2
  (s17_hblk B ly2 S2 W2 mem2 md2 c _ HAR2 Hin2c) (s17_hblk B ly2 S2 W2 mem2 md2 m _ HAR2 Hin2m)
  ltac:(rewrite Q18, P18; reflexivity) ltac:(rewrite Q20, P20, XN; reflexivity) ltac:(rewrite Q21, P21; reflexivity)
  ltac:(rewrite Q22, P22; reflexivity) ltac:(rewrite Q24, P24, XC; reflexivity)
  ltac:(rewrite Q25, P25, Nat2Z.inj_succ, Z.add_1_r; reflexivity) ltac:(rewrite Q26, P26; reflexivity)
  SL2 HCM2 HCNT).
Qed.
End s7t.

(* ================================ S07: 0x854d4 .. 0x854dc, to the parse ================================ *)
Definition s7_rsl : YP09.region := YP09.mkRegion (Some 9%nat) 168 176 0 0 [YP09.mkChunk 168 (CVal 8 (SOff 32 0))].
Definition s7h_ss : sstate := mkSS LO_K854d4 sr_atoms [s7_rsl] None (mkFacts [] [] []).
Section s7.
Context {fx : YK11.FPState}.
Lemma lt_seg_S07 : lt_seg_S07_stmt (fx := fx) B MT.
Proof.
intros f HX. unfold LT_K854d4_stmt.
intros cx ly S W regs mem md k acc c m t HBASE HFRM Hf HCORE HBc HBm HBt R18 R23 SLOTS HRC HMC HSTR HCNT.
pose proof HCORE as ((HJ & R2 & R3 & R4 & R8 & R9 & _) & HIMG & HBL & HBUD).
pose proof (s17_sp B MT cx HBASE) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (s17_nfiles_range (x_pl cx) : 1 <= x_nf cx <= 4) as NF.
pose proof HBASE as (HPRE0 & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HBc as (Hinc & Hc4 & Hc16 & _). pose proof HBt as (Hint & Ht4 & Ht16 & _).
pose proof HBm as (Hinm & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ c _ (proj1 HJ) Hinc) as (_ & _ & Hcc & Hcapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ t _ (proj1 HJ) Hint) as (_ & _ & Htc & Htapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ m _ (proj1 HJ) Hinm) as (_ & Hm4 & Hmc & Hmapp & _).
change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE in Hcc, Hcapp.
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc, Hmapp.
pose proof (req_size_pos (x_tn cx f) ltac:(unfold x_tn, seg_spec.seg_txt_n; lia)) as (Htn1 & Htn2).
(* the blocks c, m, t are three different live blocks *)
pose proof (s17_nodup B ly S W mem md (proj1 HJ)) as HND.
pose proof (Permutation_NoDup HBL HND) as HNDO. pose proof HNDO as HND2. cbn [app] in HND2.
apply NoDup_cons_iff in HND2 as [HNt HND3]. apply NoDup_cons_iff in HND3 as [HNm _].
assert (Hntc : (t, x_tn cx f) <> (c, seg_spec.SEG_C_SIZE)) by (intros E0; apply HNt; rewrite E0; right; left; reflexivity).
assert (Hmc' : (m, seg_spec.SEG_M_SIZE) <> (c, seg_spec.SEG_C_SIZE)) by (intros E0; apply HNm; rewrite E0; left; reflexivity).
pose proof (sep_blocks SEGS B LAWS ly S W mem md m _ c _ (proj1 HJ) Hinm Hinc Hmc') as Hdmc.
unfold zdisjoint in Hdmc. cbn [fst snd] in Hdmc.
change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE in Hdmc.
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hdmc.
(* the model: the last turn's parse against m_cross (s17_last) *)
destruct (s17_last (x_pl cx) f ltac:(change (seg_spec.seg_nfiles (x_pl cx)) with (x_nf cx); lia)) as (EAF & ECNT & CREL).
set (rcs := seg_spec.seg_rc (seg_spec.seg_run (x_pl cx) f)) in *.
set (txt := seg_spec.seg_txt (x_pl cx) f) in *.
set (MC := SegModel.m_cross (SegModel.m_file (seg_spec.seg_mc (seg_spec.seg_run (x_pl cx) f)) txt None)) in *.
assert (EAFc : x_af cx f = (fst (SegModel.r_parse rcs txt), MC, seg_spec.seg_ret (x_st cx f))) by exact EAF.
(* the seed at 0x854d4: the slot 168(s1) = c as the atom 32 *)
pose proof (SLOTS 168 c ltac:(apply in_or_app; left; unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right])))
  as S168.
set (E := Eimg (Ereg regs [Z_to_bv 64 c])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 c)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply YP03.unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E s7h_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K854d4)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]; unfold region_ok;
      cbn [s7_rsl YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. exact (s17s_word_chunk W mem E 32 (x_s1 cx) 168 c S168 E32).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map s7_rsl YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
assert (AWR0 : awr_ok SEGS B E (ss_mem s7h_ss) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
  (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly S) (frames (x_S cx)) ly [(LT_FCLS, x_fpos cx)]).
{ unfold s7h_ss. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
unfold cfg_at. change (w64 (BASE + LO_K854d4)) with (Z_to_bv 64 (BASE + LO_K854d4)).
(* 0x854d4 .. 0x854dc: a0 := 168(s1) = c, a1 := s7 = text; it stops at jal reac_segconf_parse *)
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
{ exact AWR0. }
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr
  ltac:(intros b wlo whi a Hin' Hrr; vm_compute in Hin';
        repeat (destruct Hin' as [Hq | Hin'];
                [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9 in Hrr; lia |]);
        destruct Hin')) as K1.
clear HF HFr HG. cbv beta in K1.
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a) by (intros a Ha; exact (K1 a Ha (fun H => H))).
clear K1.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (18%bv : bv 5) P18. prreg HS (23%bv : bv 5) P23.
rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
rewrite (EE 8%nat 8%bv eq_refl) in P8. rewrite (EE 9%nat 9%bv eq_refl) in P9. rewrite E32 in P10.
rewrite (EE 23%nat 23%bv eq_refl), R23 in P11. rewrite (EE 18%nat 18%bv eq_refl), R18 in P18.
rewrite (EE 23%nat 23%bv eq_refl), R23 in P23.
pmkst HS.
assert (ESIG : pa_sigma SS_reac_segconf_parse = BASE + AF_reac_segconf_parse).
{ rewrite (SIGP SS_reac_segconf_parse); [reflexivity|]. unfold seg_prog_syms. cbn [In].
  repeat (first [left; reflexivity | right]). }
rewrite ESIG.
(* the cut's facts at the call *)
assert (KR : s17_kept B cx W mem W (ms_mem ms)).
{ destruct (s17s_frame cx ly S W _ _ k HBASE HJ) as (_ & _ & Fapp & F4096 & F47 & Esh & _).
  split; [|split; [|split]].
  - intros a Ha. apply K0. lia.
  - intros a Hia _ _. pose proof (pa_img_range a Hia) as Hr. unfold kImgEnd in Hr. apply K0. lia.
  - intros a Ha. apply K0. lia.
  - intros i Hi. rewrite Esh. apply K0. lia. }
pose proof (s17_core_carry B MT IMGF HBS cx ly S W regs mem md k acc _ LFO_L _ ly S W (ms_regs ms) (ms_mem ms) _ k acc _ _
  HBASE HCORE HJ P2 P3 P4 P8 P9 KR HBL HBUD) as HC1.
pose proof (proj1 HJ) as HAR1.
pose proof (s17_hblk B ly S W (ms_mem ms) _ c _ HAR1 Hinc) as Hc1.
pose proof (s17_hblk B ly S W (ms_mem ms) _ t _ HAR1 Hint) as Ht1.
assert (HRC1 : sa_rconf (rdW W (ms_mem ms)) c rcs).
{ apply (s17_rconf_kept (rdW W mem)); [exact HRC|]. intros i Hi. apply K0. unfold seg_spec.SEG_C_SIZE in *. lia. }
assert (HSTR1 : sa_str (rdW W (ms_mem ms)) t txt).
{ apply (s17s_str_kept (rdW W mem)); [|exact HSTR]. intros a Ha. apply K0.
  pose proof (eq_refl : x_tn cx f = Z.of_nat (length txt) + 1) as Etn. lia. }
destruct (s17_achain B MT cx ly S W (ms_regs ms) (ms_mem ms) _ k LFO_L HBASE (proj1 HC1)) as (ch1 & Hch1).
pose proof pa_B_ok as (HB0 & HB1 & _). pose proof pa_base_lo as HBLO.
assert (HSTK1 : 0 <= STK_reac_segconf_parse /\ STK_reac_segconf_parse + 368 <= STK_LLVMFuzzerTestOneInput)
  by (split; vm_compute; intros Hx; discriminate Hx).
assert (Esp1 : spZ (ms_regs ms) = x_sp0 cx + (x_s1 cx - x_sp0 cx))
  by (unfold spZ; rewrite P2, R2; unfold w64; rewrite YP03.unsigned_lit_small by lia; ring).
assert (Es0 : s0Z (ms_regs ms) = x_sp0 cx)
  by (unfold s0Z; rewrite P8, R8; unfold w64; rewrite YP03.unsigned_lit_small by lia; reflexivity).
unfold lt_post.
eapply (srr_after_callF SEGS W _ (getr (ms_regs ms) 1)).
{ apply (cl_callSF B LAWS W (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_reac_segconf_parse)) STK_LLVMFuzzerTestOneInput
    (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S _ k
    STK_reac_segconf_parse (seg_spec.RC_PARSE_W c) reac_segconf_parse_c.EV_reac_segconf_parse (x_s1 cx - x_sp0 cx)
    (getr (ms_regs ms) 1) ch1
    (fun ly' S' (W' : world SEGS) (regs' : bvmap 5 word) mem' md' =>
       getr regs' 10 = w64 (snd (SegModel.r_parse rcs txt)) /\
       sa_rconf (rdW W' mem') c (fst (SegModel.r_parse rcs txt)) /\ sa_noalloc B ly S ly' S')
    HJ Esp1).
  - clear - Hs1al Hal0. lia.
  - lia.
  - lia.
  - lia.
  - rewrite P3, R3. exact Hgp0.
  - rewrite P4, R4. exact Htp0.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [unfold LO_K854e0; lia | reflexivity].
  - rewrite P1, YP03.unsigned_lit_small; unfold LO_K854e0; lia.
  - rewrite Es0. replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by ring. exact Hch1.
  - intros HPRE. eapply SRr_mono.
    + apply (HPARSE fx ly S W (ms_regs ms) (ms_mem ms) _ ch1 c t rcs txt HPRE).
      * exact (proj1 (proj1 (proj2 HC1))).
      * exact P10.
      * unfold seg_spec.SEG_C_SIZE in Hcc. lia.
      * exact P11.
      * lia.
      * apply (s7_reader_pre cx ly S W (ms_regs ms) (ms_mem ms) _ k acc _ LFO_L _ c t f MC HC1 Hf Hc1 Ht1 Hntc HRC1 HSTR1 HCNT
          HFRM).
      * intros x Hx. pose proof (proj2 (proj1 (proj2 HC1))) as ((_ & _ & _ & HLR & _) & _).
        exact (proj1 (HLR x ltac:(unfold LTOI_RC_LITS; apply in_or_app; right; exact Hx))).
      * unfold sa_room_n. pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
        pose proof HBASE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
        rewrite Hfrs, Hfr0. cbn. lia.
      * pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
        pose proof HBASE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
        pose proof HBUD as (B1 & B2 & B3 & _).
        unfold reac_segconf_parse_c.EV_reac_segconf_parse. lia.
    + cbv beta. intros W3 c3 _ H3. exact H3.
  - intros a Ha. right. exists c, seg_spec.SEG_C_SIZE. split; [exact Hinc|]. split.
    + exact (s17_nodup_app_disj _ _ (c, seg_spec.SEG_C_SIZE) HNDO ltac:(right; right; left; reflexivity)).
    + destruct Ha as (r & Hr & Hra). unfold seg_spec.RC_PARSE_W in Hr. cbn [In] in Hr.
      change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE.
      unfold seg_spec.RC_N, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.RC_READING, seg_spec.RC_GEN,
        seg_spec.SEG_C_SIZE in *.
      destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hra; lia. }
cbv beta. intros fx1 ly2 S2 W2 regs2 mem2 md2 Hle H01 (HJo & HJc & HPr & HR10 & HRC2 & HNA).
(* back at 0x854e0 at the FP state fx1 the parse returned: the cut's facts there, then S07's tail *)
rewrite P1.
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HJc by ring.
unfold reac_segconf_parse_c.EV_reac_segconf_parse in HJo, HJc. rewrite Z.add_0_r in HJo.
destruct HNA as (HPm & Ely & f0 & ES2).
destruct (s7_callee_keep cx ly S W (ms_mem ms) _ ly2 S2 W2 mem2 md2 c 0 HBASE HJc Hc4 Hcc) as (KH & KB).
assert (HFPc : forall a, inFP (seg_spec.RC_PARSE_W c) a -> c <= a < c + req_size seg_spec.SEG_C_SIZE).
{ intros a (r & Hr & Hra). unfold seg_spec.RC_PARSE_W in Hr. cbn [In] in Hr.
  change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE.
  unfold seg_spec.RC_N, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.RC_READING, seg_spec.RC_GEN,
    seg_spec.SEG_C_SIZE in *.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hra; lia. }
assert (HNS : ~ YI16.sink_open_fp (seg_spec.RC_PARSE_W c)).
{ intros (r & Hr & Hra). unfold seg_spec.RC_PARSE_W in Hr. cbn [In] in Hr.
  unfold seg_spec.RC_N, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.RC_READING, seg_spec.RC_GEN in *.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hra; lia. }
pose proof (s17_kept_of_sub B MT cx ly S W (ms_mem ms) _ k ly2 S2 W2 mem2 md2 STK_reac_segconf_parse
  (seg_spec.RC_PARSE_W c) 0 c seg_spec.SEG_C_SIZE HBASE HJ HJc Hinc HFPc HNS) as KEPT2.
assert (Q2 : getr regs2 2 = getr (ms_regs ms) 2)
  by exact (s17_pres_reg _ _ (2%bv : bv 5) 2 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
assert (Q3 : getr regs2 3 = getr (ms_regs ms) 3)
  by exact (s17_pres_reg _ _ (3%bv : bv 5) 3 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
assert (Q4 : getr regs2 4 = getr (ms_regs ms) 4)
  by exact (s17_pres_reg _ _ (4%bv : bv 5) 4 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
assert (Q8 : getr regs2 8 = getr (ms_regs ms) 8)
  by exact (s17_pres_reg _ _ (8%bv : bv 5) 8 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
assert (Q9 : getr regs2 9 = getr (ms_regs ms) 9)
  by exact (s17_pres_reg _ _ (9%bv : bv 5) 9 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
assert (Q18 : getr regs2 18 = getr (ms_regs ms) 18)
  by exact (s17_pres_reg _ _ (18%bv : bv 5) 18 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
assert (Q23 : getr regs2 23 = getr (ms_regs ms) 23)
  by exact (s17_pres_reg _ _ (23%bv : bv 5) 23 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
assert (HBL2 : lt_blocks B cx ly2 S2 [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)])
  by exact (Permutation_trans HPm HBL).
assert (HBUD2 : lt_bud MT cx S2 k acc (5 + 2 * (x_nf cx - Z.of_nat f))).
{ pose proof HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
  split; [rewrite ES2; apply (mo_le_set_fs_r MT MTFL); exact B4|]. split; [exact B5 | exact B6]. }
pose proof (s17_core_carry B MT IMGF HBS cx ly S W (ms_regs ms) (ms_mem ms) _ k acc _ LFO_L _ ly2 S2 W2 regs2 mem2 md2
  k acc _ _ HBASE HC1 HJo Q2 Q3 Q4 Q8 Q9 KEPT2 HBL2 HBUD2) as HC2.
pose proof (proj1 HJo) as HAR2.
pose proof (Permutation_in _ (Permutation_sym HPm) Hinc) as Hin2c.
pose proof (Permutation_in _ (Permutation_sym HPm) Hinm) as Hin2m.
pose proof (Permutation_in _ (Permutation_sym HPm) Hint) as Hin2t.
assert (ERET : seg_spec.seg_ret (x_af cx f) = seg_spec.seg_ret (x_st cx f)) by (rewrite EAFc; reflexivity).
assert (EMC : seg_spec.seg_mc (x_af cx f) = MC) by (rewrite EAFc; reflexivity).
assert (ERC : seg_spec.seg_rc (x_af cx f) = fst (SegModel.r_parse rcs txt)) by (rewrite EAFc; reflexivity).
assert (SL2 : lt_slots cx (rdW W2 mem2) (LT_L cx c m ++
    [(128, (m + seg_spec.MC_N) / 8); (136, Z.of_nat f + 1); (144, x_at cx f + x_np cx f); (152, x_np cx f);
     (160, x_n1 cx f); (176, seg_spec.b2z (seg_spec.seg_ret (x_af cx f)))])).
{ rewrite ERET. apply (s17s_slots_kept cx (rdW W mem)); [| | exact SLOTS].
  - intros o v Hov. apply in_app_or in Hov as [Hov | Hov]; [exact (s17s_LT_L_off cx c m o v Hov)|].
    cbn [In] in Hov. repeat (destruct Hov as [Hov | Hov]; [injection Hov as <- _; lia|]). destruct Hov.
  - intros a Ha. rewrite KH by lia. apply K0. lia. }
assert (HCM2 : lt_cm (rdW W2 mem2) c m (x_af cx f)).
{ unfold lt_cm. rewrite ERC, EMC. split; [exact HRC2|].
  apply (s17_mconf_kept (rdW W mem)); [exact HMC|]. intros i Hi.
  rewrite (KB m seg_spec.SEG_M_SIZE i Hinm Hin2m ltac:(change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE; exact Hi)
    ltac:(unfold seg_spec.SEG_M_SIZE, seg_spec.SEG_C_SIZE in *; lia)).
  apply K0. unfold seg_spec.SEG_M_SIZE in *. lia. }
assert (HCNT2 : lt_cnt (Datatypes.S f) (seg_spec.seg_rc (x_af cx f)) (seg_spec.seg_mc (x_af cx f))).
{ rewrite ERC, EMC. exact (s17_cnt_rel (Datatypes.S f) _ _ MC CREL HCNT). }
exact (s7_tail (fx := fx1) f HX cx ly2 S2 W2 regs2 mem2 md2 k acc c m t HBASE (fxrel_frm0 fx fx1 HFRM H01) Hf HC2
  (s17_hblk B ly2 S2 W2 mem2 md2 c _ HAR2 Hin2c) (s17_hblk B ly2 S2 W2 mem2 md2 m _ HAR2 Hin2m)
  (s17_hblk B ly2 S2 W2 mem2 md2 t _ HAR2 Hin2t)
  ltac:(rewrite HR10, ECNT, EMC; reflexivity) ltac:(rewrite Q18, P18; reflexivity) ltac:(rewrite Q23, P23; reflexivity)
  SL2 HCM2 HCNT2).
Qed.
End s7.
End e.
End f.
End d.
