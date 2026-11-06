(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0j.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YN0j.v, with its module paths and module names changed; 546 of its 584 lines of code are new or changed and 260 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC.v, with its module names changed; 1538 of its 1613 lines of code are new or changed and 509 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC2.v, with its module paths changed; 237 of its 289 lines of code are new or changed and 1561 lines of the source are left out. *)
(* check_no_overread B 0x8124c (fs.c), fs.asan-ubsan: the TAIL of the ASan walk - the epilogue, the `ret` and the R2
   arms of that range. a Theorem Labs lane owns the statement (lib/B/FSH_Fn_cno.v check_no_overread_spec); this file proves ONE
   of the call-step interface statements of lib/B/FSW_check_no_overread.v Section I, `cno_tail_ret_T B`
   (= cno_from cno_ss_R INV_R, the CTX-free interface of a working branch decf0bae273), with the name
   cno_tail_ret. The other call steps of the tail are cno_call_bcmp / cno_call_afree (lib/B/FSW_check_no_overread_tail.v)
   and cno_call_ffree (lib/B/FSW_check_no_overread_ffree.v). Rule 24: this file proves PART of check_no_overread only.
   Template (text only; no byte offset is copied, B's bytes differ): lib/A/FSW_check_no_overread_ret.v at
   a working branch 59f0008819f.

   RANGE (MEASURED: neutral_dis listing (internal path)
   check_no_overread.fuzz_state.asan-ubsan.s on the pinned fs.asan-ubsan; every address below is from it, and every
   claim about the run is re-checked by the engine in this file):
   - 0x814f8-0x81510: a0 := -8, the three locals' shadow bytes (s2 + 4 / 8 / 0xc) := 0xf8 (use-after-scope), then
     a0 := 0x45e0360e (`lui` 0x81508 + `addiw` 0x8150c) and `sd a0, 0(s3)` 0x81510: the frame's magic word is retired;
   - 0x81514 `ld a1, 0x10(s1)`: the frame address is reloaded from the slot the walk wrote at 0x813fc;
     0x81518 `beqz a1` is NOT taken (the slot holds the fake frame, atom 19, and the walk's atom fact
     (19, mkAF 4096 (2^47) 5) puts it at or above 4096), so the fake-frame arm 0x8151c-0x81568 runs and the real-stack
     arm 0x8156c-0x815a8 is DEAD (cno_ret_pcs_dead_real_arm);
   - 0x8151c-0x8155c: the sixteen frame-shadow bytes := 0xf5; 0x81560 `ld a0, 120(a1)` reads the frame's flag word
     (frame + 120), 0x81564 `sb zero, 0(a0)` RELEASES the fake frame (lib/B/FSW_frame.v fsw_flag_storeU: own [(1,pos)]
     -> [], the state -> stack_free_state 1 pos), 0x81568 `j 0x815ac`;
   - 0x815ac-0x815e4: sp := s0 - 0xa0, ra and s0..s11 reloaded from the prologue's thirteen words, `addi sp,sp,160`;
   - 0x815e8 `ret` into check_no_overread_spec's post (lib/B/FSW_ret.v fsw_retU): EV_check_no_overread = 12 (the
     journal's k, fixed by INV_R), ablocks unchanged, cnt + 3, FP = FS_PSTAT_FP, U' = U.
   GUARDS of this range: the 44 instructions hold no UBSan check and no inline ASan check (the shadow stores
   0x814fc-0x8155c are the instrumentation's own frame bookkeeping, unchecked) and no edge to the abort block: the one
   branch, 0x81518 `beqz a1`, goes to the real-stack arm 0x8156c, which is dead.
   R2 of this range (the out-of-line blocks after the ret): 0x815f4 before_abort / 0x815f8 abort, 0x815fc `unimp` (the
   UBSan trap of U1 0x813c0 / U2 0x813e0 / U3 0x813f8) and 0x81600-0x81614 (the two ASan slow paths and
   __asan_report_store1 calls) are NOT entered: cno_ret_pcs_no_abort checks every pc of the 44-step run against
   [0x815f4, 0x81618). The in-function block 0x815ec `ld a0, 0(s7)` / 0x815f0 `beq a0, s10` (A's 0x81540 twin),
   reached from 0x81494 `beqz s10` when the first decoded length n1 = 0 (s10 := 0 by 0x81488 `ld s10, 0(s10)`), goes
   BACK to the frees at 0x814c8 and not on into 0x815f4: cno_r2_5ec / cno_r2_5ec_pcs run the two instructions on the
   walk's own state (s7 = s3 + 0x40 from 0x81418, the second length n2 at frame + 0x40) and the engine answers
   0x814c8, because the three decoded lengths agree (n2 = n1 = 0: the three decoders read the same C string). The arm
   is closed by the engine's own step, not by a halted leaf and not at a Report* call.
   FALL-THROUGH NOTE for 0x81614: it is the LAST instruction of the function (cno_r2_tbl_end: the table has an entry at
   0x81614 and NONE at 0x81618) and __asan_report_store1 ends in `ret`, so a no-return treatment of 0x81614 would miss
   the fall-through into 0x81618, which is outside check_no_overread. No arm of this file is closed that way.

   LOOKUP (rule 24): proof-index by NAME check_no_overread and by B ADDRESS 0x8124c, unpiped, a Theorem Labs lane
   2026-10-29 05:4xZ (outputs (internal path), r24-cnoB-addr.txt): released plain /
   UBSan templates only, no released lib/A or lib/B walk; 0x8124c: 0 released hits; (internal path): no
   row; CONFIRM (internal path). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG05 YG0t YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_rres FSW_frame FSH_Fn_cno FSH_Fn_alloc
FSW_check_no_overread_tbl FSW_check_no_overread.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YF0x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= the engine's answers over this range (MEASURED here, by vm_compute) ================= *)
(* the pre-state is the interface's cno_ss_R = cno_ss 0x814f8 19 18 cno_flag_chunk cno_cssl_R: the thirteen saved
   words at s0, the fake frame at atom 19 with its flag word at frame + 120, the frame's sixteen shadow bytes at atom
   18, and the slots at s1 with the frame address at sp1 + 0x10. The epilogue also WRITES the flag byte, which is not
   a byte of the frame (AR_flag_law owns it, AR_frames_law does not own any frame byte), so it is its own one-byte
   region at the flag atom 46. *)
Definition cno_ss_RE : sstate :=
  mkSS (ss_pc cno_ss_R) (ss_regs cno_ss_R) (YP09.mkRegion (Some 46%nat) 0 1 0 1 [] :: ss_mem cno_ss_R)
    (ss_resv cno_ss_R) (ss_facts cno_ss_R).
(* 44 instructions: 0x814f8-0x81568 (29, the fake-frame arm) and 0x815ac-0x815e4 (15), stopping AT the `ret` *)
Definition cno_ss_RF : sstate := Eval vm_compute in fst (sym_runN tfibsegs cno_tbl 44%N cno_ss_RE).
Lemma cno_ret_run_eq : sym_runN tfibsegs cno_tbl 44%N cno_ss_RE = (cno_ss_RF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma cno_ss_RF_shape : ss_pc cno_ss_RF = 0x815e8 /\ ss_resv cno_ss_RF = None /\
  clookup cno_tbl (ss_pc cno_ss_RF) = Some RET_WORD_r /\
  nth_error (ss_mem cno_ss_RF) 0 = Some (YP09.mkRegion (Some 46%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]).
Proof. repeat split; vm_compute; reflexivity. Qed.
(* at the `ret`: sp is the entry sp (the s0 atom), ra and s0..s11 are the thirteen saved atoms 33 .. 45, gp / tp kept *)
Lemma cno_ss_RF_regs :
  map (fun r => sr_get (ss_regs cno_ss_RF) r) [2; 3; 4; 1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv =
  [SOff 8 0; SOff 3 0; SOff 4 0; SOff 33 0; SOff 34 0; SOff 35 0; SOff 36 0; SOff 37 0; SOff 38 0; SOff 39 0;
   SOff 40 0; SOff 41 0; SOff 42 0; SOff 43 0; SOff 44 0; SOff 45 0].
Proof. vm_compute. reflexivity. Qed.
(* the frame's magic is retired and its sixteen shadow bytes are 0xf5: the fake-frame arm ran *)
Lemma cno_ss_RF_frame_magic :
  nth_error (ss_mem cno_ss_RF) 2 = Some (YP09.mkRegion (Some 19%nat) 0 128 0 128
    [YP09.mkChunk 0 (CVal 8 (SLit 0x45e0360e)); YP09.mkChunk 120 (CVal 8 (SOff 46 0))]).
Proof. vm_compute. reflexivity. Qed.

(* ---- R2: every pc the run visits, and the blocks it must not enter ---- *)
Definition cno_ret_pcs : list Z :=
  Eval vm_compute in map (fun n => ss_pc (fst (sym_runN tfibsegs cno_tbl (N.of_nat n) cno_ss_RE))) (seq 0 45).
(* 0x815f4 before_abort, 0x815f8 abort, 0x815fc the UBSan `unimp`, 0x81600-0x81614 the two ASan slow paths and
   report calls: no pc of the run is in them *)
Lemma cno_ret_pcs_no_abort : forallb (fun p => negb ((0x815f4 <=? p) && (p <? 0x81618))) cno_ret_pcs = true.
Proof. vm_compute. reflexivity. Qed.
(* the real-stack arm 0x8156c-0x815a8 is dead: the reloaded frame address is not 0 *)
Lemma cno_ret_pcs_dead_real_arm : forallb (fun p => negb ((0x8156c <=? p) && (p <? 0x815ac))) cno_ret_pcs = true.
Proof. vm_compute. reflexivity. Qed.
(* every pc of the run is in the function's own text *)
Lemma cno_ret_pcs_in_text : forallb (fun p => (0x814f8 <=? p) && (p <=? 0x815e8)) cno_ret_pcs = true.
Proof. vm_compute. reflexivity. Qed.

(* the 0x815ec / 0x815f0 arm: entered from 0x81494 `beqz s10` when the first decoded length n1 = 0 (s10 := 0), with
   s7 = s3 + 0x40 (0x81418) and the second length n2 at frame + 0x40. The three decoders read the same C string, so
   n2 = n1 = 0 and `beq a0, s10` at 0x815f0 jumps BACK to 0x814c8 (the frees), not on into 0x815f4. *)
Definition cno_cssl_R2 : list YP09.chunk := [YP09.mkChunk 24 (CVal 8 (SOff 48 0)); YP09.mkChunk 16 (CVal 8 (SOff 19 0))].
Definition cno_csF_R2 : list YP09.chunk :=
  [YP09.mkChunk 32 (CVal 8 (SLit 0)); YP09.mkChunk 64 (CVal 8 (SLit 0)); YP09.mkChunk 96 (CVal 8 (SLit 0));
   YP09.mkChunk 120 (CVal 8 (SOff 46 0))].
Definition cno_ss_R2 : sstate :=
  let X := cno_ss 0x815ec 19 18 cno_csF_R2 cno_cssl_R2 in
  mkSS (ss_pc X) (sr_set (sr_set (ss_regs X) 23%bv (SOff 19 64)) 26%bv (SLit 0)) (ss_mem X) (ss_resv X) (ss_facts X).
Definition cno_ss_R2f : sstate := Eval vm_compute in fst (sym_runN tfibsegs cno_tbl 2%N cno_ss_R2).
Lemma cno_r2_5ec : sym_runN tfibsegs cno_tbl 2%N cno_ss_R2 = (cno_ss_R2f, RS_running).
Proof. vm_compute. reflexivity. Qed.
(* the two pcs of that arm: 0x815f0 (the branch) and then 0x814c8 (the first fuzz_free's argument), never 0x815f4 *)
Lemma cno_r2_5ec_pcs :
  map (fun n => ss_pc (fst (sym_runN tfibsegs cno_tbl (N.of_nat n) cno_ss_R2))) (seq 0 3) = [0x815ec; 0x815f0; 0x814c8].
Proof. vm_compute. reflexivity. Qed.
(* the fall-through note: 0x81614 is the function's last instruction, 0x81618 is outside its table *)
Lemma cno_r2_tbl_end : clookup cno_tbl 0x81614 <> None /\ clookup cno_tbl 0x81618 = None.
Proof. split; [vm_compute; discriminate | vm_compute; reflexivity]. Qed.

(* ================= pure facts ================= *)
(* fuzz/alloc.c's statics are image bytes (one loaded segment of fs.asan-ubsan holds .data and .bss from g_fail_at
   0xa41c0 to g_count 0x5dab00, FSH_Base.v:101-104); shape of A's cno_glob_img (59f0008819f) at B's addresses *)
Lemma cno_glob_img : forall a, (G_FAIL <= a < G_FAIL + 8 \/ G_LIVE <= a < G_LIVE + 8 \/ G_PEAK <= a < G_PEAK + 8 \/
  G_COUNT <= a < G_COUNT + 8) -> in_img tfibsegs a.
Proof.
intros a Ha.
assert (Hx : existsb (fun s => (Z.of_N (seg_base s) <=? G_FAIL) && (G_COUNT + 8 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
  tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hx as (sg & Hin & Hc). apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hin|]. unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT in *. lia.
Qed.
(* a run whose write window holds no image byte leaves every image byte as the walk saw it *)
Lemma cno_img_frame : forall E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall a, in_img tfibsegs a -> ~ in_wrange E rs a) ->
  forall a, in_img tfibsegs a -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros E rs H m m' Hfr Hn a Ha. pose proof (fs_segs_img a Ha) as Hr. unfold FS_IMG_END in Hr.
apply aview_eq_of. apply Hfr. rewrite (wz a ltac:(lia)). exact (Hn a Ha).
Qed.
(* fs_glob survives any memory change that keeps the image bytes *)
Lemma cno_glob_keep : forall (W : world tfibsegs) (m m' : word -> option byte) live peak cnt fail,
  (forall a, in_img tfibsegs a -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail Hk (G1 & G2 & G3 & G4 & R).
assert (VB : forall g v, (G_FAIL <= g /\ g + 8 <= G_FAIL + 8 \/ G_LIVE <= g /\ g + 8 <= G_LIVE + 8 \/
    G_PEAK <= g /\ g + 8 <= G_PEAK + 8 \/ G_COUNT <= g /\ g + 8 <= G_COUNT + 8) ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W) m') g 8 v).
{ intros g v Hg Hv kk Hkk. assert (Hi : in_img tfibsegs (g + Z.of_nat kk)) by (apply cno_glob_img; lia).
  rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W) m m' _ (Hk _ Hi)). exact (Hv kk Hkk). }
unfold fs_glob, fs_glob_at in *.
split; [apply VB; [lia | exact G1]|]. split; [apply VB; [lia | exact G2]|].
split; [apply VB; [lia | exact G3]|]. split; [apply VB; [lia | exact G4]|]. exact R.
Qed.
(* the frame and its flag do not move along the walk: ajournal's layout_le keeps ly_F (YG0f.layout_le) *)
Lemma cno_F_ly : forall cx n ly3, layout_le n (c_ly cx) ly3 -> frame_addr ly3 1 (c_fpos cx) = cno_F cx.
Proof.
intros cx n ly3 Hle. unfold cno_F, frame_addr.
destruct Hle as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.
Lemma cno_FL_ly : forall cx n ly3, layout_le n (c_ly cx) ly3 -> flag_addr ly3 1 (c_fpos cx) = cno_FL cx.
Proof.
intros cx n ly3 Hle. unfold cno_FL, flag_addr.
destruct Hle as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.

Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the engine's laws, proved for fs (not assumed) *)
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* the two fake-stack laws FSW_frame's release step consumes. Both are PROVED here, not assumed: the free law is
   YG0t.astack_free_law_ok, and the flag law is AR_flag_law plus AR_client_img_law over S0's image cover
   (B's YF0x.img_cover_of_ledger), A's cno_FFL (59f0008819f) at B's image. *)
Lemma cno_ASF : astack_free_law tfibsegs B.
Proof. exact (astack_free_law_ok tfibsegs B). Qed.
Lemma cno_FFL : frame_flag_lawP tfibsegs B.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (YF0x.img_cover_of_ledger ly S md L) as [C1 C2].
unfold YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* ================= the tail: the epilogue, the frame release and the `ret` =================
   the interface's cno_tail_ret_T (lib/B/FSW_check_no_overread.v Section I): from a machine at which cno_ss_R holds
   under an env E whose atoms are cno_E's, with the walk's journal at k = EV_check_no_overread over the entry's U and
   blocks, to check_no_overread_spec's post. *)
Lemma cno_tail_ret : cno_tail_ret_T B.
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HINV HS.
destruct HINV as (-> & Eab & -> & E2 & E8 & E9 & E18 & E19 & E3 & E4 & (peak' & Hpk & HG)).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 YM05.alloc_ceiling_val) as HCV.
pose proof HE as (EX32 & Esv & E46 & E47).
pose proof HB as (HPRE & _).
pose proof HPRE as ((HAP & _) & _). pose proof HAP as (_ & Hret & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (ML : model_laws (as_universe B))
  by (apply model_laws_ok; destruct HAR as (HARm & _); exact (am_universe _ _ _ _ HARm)).
(* B's frame budget (interface note: STK_check_no_overread = 16863): the saved words lie above the stack floor *)
pose proof cno_stk as HSTK.
(* the entry sp, the re-aligned sp, the frame, its shadow and its flag word, as plain integers *)
set (sp0 := cno_sp0 cx) in *. set (sp1 := cno_sp1 cx) in *.
assert (Hsp0r : 0 <= sp0 < 2 ^ 64) by (unfold sp0, cno_sp0, spZ; apply u64_range).
assert (Hsp1d : sp1 = 32 * ((sp0 - 160) / 32)) by reflexivity.
assert (Hsp1lo : sp0 - 191 <= sp1) by (rewrite Hsp1d; pose proof (Z.mul_div_le (sp0 - 160) 32 ltac:(lia)) as X1;
  pose proof (Z.mod_pos_bound (sp0 - 160) 32 ltac:(lia)) as X2; Z.div_mod_to_equations; lia).
assert (Hsp1hi : sp1 <= sp0 - 160) by (rewrite Hsp1d; Z.div_mod_to_equations; lia).
assert (Hin1 : In (1, c_fpos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
pose proof (cno_F_ly cx _ ly3 Hly) as HF. pose proof (cno_FL_ly cx _ ly3 Hly) as HFL.
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 1 (c_fpos cx) HAR Hin1)
  as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 1 (c_fpos cx) HAR Hin1)
  as (HFal & _ & HFp & HFs).
change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp, HFal, HFp.
change (fs_frame_bytes 1 / 8) with 16 in HFs.
rewrite HF in HF4096, HFceil, HFapp, HFal, HFp, HFs.
destruct (cno_FFL ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 1 (c_fpos cx) HAR Hin1)
  as (HLp & HLo & (HLapp & HLimg) & HL4096 & HLz & HLc).
rewrite HFL in HLp, HLo, HLapp, HLimg, HL4096, HLz, HLc.
set (F := cno_F cx) in *. set (FL := cno_FL cx) in *. set (SF := cno_SF cx) in *.
assert (HFr : 0 <= F < 2 ^ 64) by lia.
assert (HFrng : 0 <= F < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds F HFrng) as (HS1b & HS2b).
assert (HSFlo : SHADOW_OFF <= SF) by (unfold SF, cno_SF, shadow_addr, SHADOW_OFF; fold F;
  pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); lia).
assert (HSFhi : SF < kHighMemBeg) by (unfold SF, cno_SF; fold F; rewrite C2 in HS2b; unfold kHighMemBeg; lia).
assert (HSFr : 0 <= SF < 2 ^ 64) by (unfold SHADOW_OFF, kHighMemBeg in *; lia).
assert (HFLr : 0 <= FL < 2 ^ 64) by lia.
(* the atom values of E *)
assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2; apply wz; lia).
assert (U8 : bv_unsigned (ew E 8) = sp0) by (rewrite E8; apply wz; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply wz; lia).
assert (U18 : bv_unsigned (ew E 18) = SF) by (rewrite E18; apply wz; lia).
assert (U19 : bv_unsigned (ew E 19) = F) by (rewrite E19; apply wz; lia).
assert (U46 : bv_unsigned (ew E 46) = FL) by (rewrite E46; apply wz; lia).
(* the flag byte is no user-poisoned byte of U: a byte of U is a live block's shadow byte, the flag is application
   memory (FSupoison ush_facts, as FSW_frame's own argument) *)
assert (HflagU : in_ush (c_U cx) (bv_unsigned (Z_to_bv 64 FL)) = false).
{ destruct (in_ush (c_U cx) (bv_unsigned (Z_to_bv 64 FL))) eqn:Eu; [|reflexivity]. exfalso.
  rewrite (wz FL ltac:(lia)) in Eu.
  pose proof (ush_facts tfibsegs B ly3 S3 (c_U cx) W3 (ms_mem ms3) md3 _ HARU Eu) as (_ & L1 & L2).
  unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia. }
(* the flag cell is apart from the frame and its shadow: it is runtime-owned, no frame or shadow byte is *)
assert (HFLnf : forall o, 0 <= o < 128 -> F + o <> FL)
  by (intros o Ho Heq; destruct (HFp (F + o) ltac:(lia)) as (_ & Hn); rewrite Heq in Hn; exact (Hn HLo)).
assert (HFLns : forall o, 0 <= o < 16 -> SF + o <> FL)
  by (intros o Ho Heq; destruct (HFs o Ho) as (_ & Hn); unfold SF, cno_SF in Heq; fold F in Heq;
      rewrite Heq in Hn; exact (Hn HLo)).
assert (Dff : FL + 1 <= F \/ F + 128 <= FL).
{ destruct (Z_lt_le_dec FL F) as [Hl|Hl]; [left; lia|].
  destruct (Z_lt_le_dec FL (F + 128)) as [Hh|Hh]; [|right; lia].
  exfalso. exact (HFLnf (FL - F) ltac:(lia) ltac:(lia)). }
assert (Dfs : FL + 1 <= SF \/ SF + 16 <= FL).
{ destruct (Z_lt_le_dec FL SF) as [Hl|Hl]; [left; lia|].
  destruct (Z_lt_le_dec FL (SF + 16)) as [Hh|Hh]; [|right; lia].
  exfalso. exact (HFLns (FL - SF) ltac:(lia) ltac:(lia)). }
(* the state with the flag cell as a region: present (AR_flag_law) and writable on the machine's own memory *)
assert (HSE : st_ok tfibsegs E cno_ss_RE (restrict (w_H W3) ms3)).
{ unfold cno_ss_RE. apply (YI0n.st_ok_add_region' tfibsegs E cno_ss_R (restrict (w_H W3) ms3));
  [exact HS | vm_compute; reflexivity | |].
  - unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
    rewrite U46. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. replace (FL + o) with FL by lia. apply (apresent_writable tfibsegs).
    destruct HLp as (Hh & b & Hb). split; [exact Hh|]. exists b.
    rewrite (unpoison_out (c_U cx) (ms_mem ms3) _ HflagU) in Hb. exact Hb.
  - apply all_disjoint_of_extents.
    unfold cno_ss_R, cno_ss, fss_ret_s0_args, fss_ret_s0_regs, cno_fr_region, cno_sh_region, cno_sl_region,
      fs_ret_s0_region, extent_of_region.
    cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U46, U8, U19, U18, U9.
    cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
    split; [left; lia|]. split; [destruct Dff as [X|X]; [left; lia | right; lia]|].
    split; [destruct Dfs as [X|X]; [left; lia | right; lia]|]. split; [left; lia | exact I]. }
(* the write window of the 44 instructions: the saved words, the frame, its shadow, the slots and the flag cell *)
assert (HWR : forall a, in_wrange E (ss_mem cno_ss_RE) a ->
  awr_byte tfibsegs B STK_check_no_overread sp0 FS_PSTAT_FP (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3
    [(1, c_fpos cx)] (frames (c_S cx)) a \/ a = flag_addr ly3 1 (c_fpos cx)).
{ intros a (r & Hr & Ha).
  unfold cno_ss_RE, cno_ss_R, cno_ss, fss_ret_s0_args, fss_ret_s0_regs, cno_fr_region, cno_sh_region,
    cno_sl_region, fs_ret_s0_region in Hr.
  cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - right. rewrite HFL, U46 in *. lia.
  - left. left. left. rewrite U8 in Ha. lia.
  - left. left. right. right. right. exists 1, (c_fpos cx). split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1) with 128. rewrite HF, U19 in *. lia.
  - left. left. right. right. right. exists 1, (c_fpos cx). split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16. rewrite HF.
    fold F. unfold SF, cno_SF in U18. fold F in U18. rewrite U18 in Ha. lia.
  - left. left. left. rewrite U9 in Ha. lia. }
(* no image byte is in that window: the stack and the slots are at or above alloc_ceiling, the frame's shadow is in
   the shadow band, the frame and the flag cell are client memory (AR_client_img_law) *)
assert (NW : forall a, in_img tfibsegs a -> ~ in_wrange E (ss_mem cno_ss_RE) a).
{ intros a Ha (r & Hr & Har). pose proof (fs_segs_img a Ha) as Hai. unfold FS_IMG_END in Hai.
  unfold cno_ss_RE, cno_ss_R, cno_ss, fss_ret_s0_args, fss_ret_s0_regs, cno_fr_region, cno_sh_region,
    cno_sl_region, fs_ret_s0_region in Hr.
  cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Har.
  - rewrite U46 in Har. assert (a = FL) as -> by lia. exact (HLimg Ha).
  - rewrite U8 in Har. unfold ASAN_CEIL in *. lia.
  - rewrite U19 in Har.
    exact (frm_img tfibsegs B LAWS ly3 S3 W3 _ md3 1 (c_fpos cx) a HAR Hin1
      ltac:(change (fs_frame_bytes 1) with 128; rewrite HF; lia) Ha).
  - rewrite U18 in Har. unfold SHADOW_OFF in HSFlo. lia.
  - rewrite U9 in Har. unfold ASAN_CEIL in *. lia. }
(* 0x814f8 .. 0x815e4: the locals' shadow, the retired magic, the frame release and the epilogue *)
eapply (fsw_flag_storeU B ML cno_ASF cno_FFL cno_tbl cno_tbl_ok W3 44%N E cno_ss_RE cno_ss_RF RS_running ms3
  STK_check_no_overread sp0 FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (unpoison (c_U cx) (c_mem cx)) (c_md cx)
  [] ly3 S3 (c_U cx) md3 EV_check_no_overread 1 (c_fpos cx) (cno_post B cx)
  HSE cno_ret_run_eq I HJ HARU ltac:(lia) HWR).
- (* the released flag byte is 0 in every machine the end state describes *)
  intros msr HSr. rewrite HFL. fold FL.
  pose proof (fsw_region_nth E cno_ss_RF msr 0 _ HSr (proj2 (proj2 (proj2 cno_ss_RF_shape)))) as HR.
  pose proof (fsw_field E (ms_mem msr) 46%nat FL [YP09.mkChunk 0 (CVal 1 (SLit 0))] 0 1 0 1 0 1%N (SLit 0) 0
    HR U46 ltac:(left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
  pose proof (HV 0%nat ltac:(cbn; lia)) as Hb. cbn [Z.of_nat] in Hb.
  rewrite Z.add_0_r, Z.add_0_r in Hb. change (YO0f.le_byte 0 (N.to_nat 1) 0) with 0 in Hb. exact Hb.
- (* 0x815e8: the `ret` into check_no_overread_spec's post *)
  intros ms' mat' HS' HJ' HARU' HFm HFr' HGr'.
  pose proof (cno_img_frame E (ss_mem cno_ss_RE) (w_H W3) (ms_mem ms3) (ms_mem ms') HFr' NW) as KEEP.
  unfold cno_post, cno_sp0 in *.
  apply (fsw_retU B cno_tbl cno_tbl_ok W3 E cno_ss_RF ms' _ STK_check_no_overread sp0 FS_PSTAT_FP (c_regs cx)
    (c_ly cx) (c_S cx) (c_U cx) (c_W cx) (c_mem cx) (c_md cx) ly3 (stack_free_state 1 (c_fpos cx) S3) (c_U cx)
    EV_check_no_overread _ HS' (proj1 (proj2 cno_ss_RF_shape)) (proj1 (proj2 (proj2 cno_ss_RF_shape)))).
  + (* ra: the saved entry ra, extra atom 33 *)
    rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E cno_ss_RF ms' 1%bv HS').
    change (sr_get (ss_regs cno_ss_RF) 1%bv) with (SOff 33 0). rewrite fsw_SOff0.
    change 33%nat with (33 + 0)%nat. rewrite (Esv 0%nat ltac:(lia)). cbn [nth cno_saved_regs]. exact Hret.
  + exact HJ'.
  + exact HARU'.
  + (* the callee-saved registers are back at their entry values *)
    apply (fsw_preserved (w_H W3) E cno_ss_RF ms' (c_regs cx) (fun r => sr_get (ss_regs cno_ss_RF) r) HS');
      [vm_compute; reflexivity|].
    intros r Hr. cbv [CALLEE_SAVED In] in Hr.
    repeat (destruct Hr as [<-|Hr];
      [ lazymatch goal with |- sv_denot E ?x = _ => let y := eval vm_compute in x in change x with y end;
        rewrite fsw_SOff0;
        first [ apply bv_eq; rewrite U8; reflexivity | exact E3 | exact E4
              | lazymatch goal with |- ew E ?n = _ =>
                  let m := eval compute in (n - 33)%nat in change n with (33 + m)%nat end;
                first [ rewrite (Esv 1%nat ltac:(lia)); reflexivity | rewrite (Esv 2%nat ltac:(lia)); reflexivity
                      | rewrite (Esv 3%nat ltac:(lia)); reflexivity | rewrite (Esv 4%nat ltac:(lia)); reflexivity
                      | rewrite (Esv 5%nat ltac:(lia)); reflexivity | rewrite (Esv 6%nat ltac:(lia)); reflexivity
                      | rewrite (Esv 7%nat ltac:(lia)); reflexivity | rewrite (Esv 8%nat ltac:(lia)); reflexivity
                      | rewrite (Esv 9%nat ltac:(lia)); reflexivity | rewrite (Esv 10%nat ltac:(lia)); reflexivity
                      | rewrite (Esv 11%nat ltac:(lia)); reflexivity | rewrite (Esv 12%nat ltac:(lia)); reflexivity ] ] |]).
    destruct Hr.
  + (* the post's own facts: the blocks are the entry's (the release touches only the fake-stack state) and the
       allocator's statics are the ones the walk reached the epilogue with *)
    intros mat. split.
    * change (ablocks B ly3 (stack_free_state 1 (c_fpos cx) S3)) with (ablocks B ly3 S3). exact Eab.
    * exists peak'. split; [exact Hpk|].
      exact (cno_glob_keep W3 (ms_mem ms3) (ms_mem ms') _ _ _ _ KEEP HG).
Qed.

End R.
