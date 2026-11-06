(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:383-389, 448-454, 493-498, 501-509 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:625-631 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:208-214, 227-233 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg10.v, with its module paths and module names changed; 2634 of its 2686 lines of code are new or changed and 608 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_parse_value.v, with its module paths, module names, addresses and numbers changed; 1014 of its 1163 lines of code are new or changed and 2537 lines of the source are left out. *)
(* check_no_overread 0x811c8 (fs.c), fs.asan, 230 instructions: the ASan WALK of FSH_Fn_cno.v
   check_no_overread_spec (the FROZEN statement; this file proves it, it does not restate it).
   Each callee's S0 contract is a Section hypothesis, as the lane rule asks, and so is each call site's call-trace row.
   The kit steps are lemmas: FSW_K / FSW_K3 / FSW_rres / FSW_ret (S0 c6f2144975e), FSW_frame (a working branch
   2fe0e09c2c7) and FSW_malloc_free (a working branch 1d5614a3cd0). The spec carries the stack-room
   premise `spZ regs + 32 <= ly_top ly` (S0 8aeb3e036bf), which gives achain_push its fp < ly_top - 16 (cno_chain).

   CONTROL FLOW (MEASURED, capstone on the pinned fs.asan; every address below is from that disassembly):
   - 0x811c8-0x81238 prologue: frame 0xa0, ra + s0..s11 saved at s0-8 .. s0-104, s0 := entry sp, sp re-aligned down
     to 32 (`andi sp,sp,-0x20`), s1 := sp, s6 := a1 (len), s7 := a0 (d), s9 := the shadow base through the GOT,
     the use-after-return flag (1) tested (`beqz a2` 0x81230 not taken), a0 := 0x80, `jal __asan_stack_malloc_1`.
   - 0x8123c-0x812f8: the frame is granted (FSH_Fn_entry.fs_fake_granted), so `bnez s10` 0x8124c skips the
     real-stack fallback 0x81250-0x81268; s3 := the frame, stored at 0x30(s1); the frame header (magic, descriptor,
     pc) at s3 + 0/8/16; s2 := shadow_addr s3; the frame shadow := f1 f1 f1 f1 f8 f2 f2 f2 f8 f2 f2 f2 f8 f3 f3 f3
     (three 8-byte locals at s3 + 0x20 / 0x40 / 0x60, use-after-scope poisoned);
   - 0x812f8 past_nul (d, len, 'A') -> a, kept at 0x18(s1); 0x8130c past_nul (d, len, 'B') -> b in s4;
   - 0x8131c __wrap_malloc (len + 18) -> t in s5 (`beqz a0` 0x81320 goes to the abort block: UNTAKEN, the model's
     malloc cannot answer NULL under blocks_bytes + n <= LIVE_MAX, YCbq.v aj_malloc_at04);
   - 0x81328 `beqz s6`: len = 0 skips the copy; else 0x81338 __asan_memcpy (t, d, len);
   - 0x81354 __asan_memset (t + len, 0, 17); the frame address is kept at 0x10(s1);
   - 0x81358-0x81364 the inline ASan check of the 1-byte store at s6 = t + len + 17 (the block's last byte); its
     slow path 0x81550-0x8155c (__asan_report_store1) is UNTAKEN; 0x81374 t[len + 17] := 0;
   - 0x81378-0x8138c the three locals are unpoisoned and zeroed;
   - 0x81398 / 0x813a8 / 0x813b8 preset_base64_decode (a, &n1), (b, &n2), (t, &n3): all three read the SAME C
     string db (a = db ++ [0; 'A'; 'A'] ++ 0^15, b = db ++ [0; 'B'; 'A'] ++ 0^15, t = db ++ 0^18, and db has no NUL),
     so b64_dec agrees on the three and the four comparison branches 0x813c8 / 0x813d4 / 0x813e4 / 0x81404 and the
     two bcmp results 0x813fc / 0x81418 cannot reach the abort block 0x81548;
   - 0x8141c / 0x81424 / 0x81430 fuzz_free of the three decoded blocks; 0x81438 / 0x81440 / 0x81448 __wrap_free of
     a, b, t; 0x8144c-0x81464 the locals' shadow := f8 and the frame magic := retired;
   - 0x81468 the frame address is reloaded: non-zero, so 0x81470-0x814b0 writes f5 over the frame shadow and
     0x814b8 stores 0 through the flag word (the frame is released); 0x814c0-0x814fc is the real-stack arm (dead);
   - 0x81500-0x8153c epilogue: sp := s0 - 0xa0, ra + s0..s11 reloaded, `ret`.

   NET: 6 malloc + 6 free (EV_check_no_overread = 12), ablocks unchanged, g_count + 3 (the three decoder
   allocations), FP = FS_PSTAT_FP, U' = U.
   LOOKUP (rule 24, final form a Theorem Labs lane 02:12Z; outputs and dates, not absence claims):
   (1) released refs: proof-index v5 built 2026-10-28T23:48:31Z (main d65b67070f2, ossv/recipes 568db058c1d,
       ossv/candidates ee89628c997, release/pau-projects-recipes b6a0088adcb), run unpiped 2026-10-29 00:4xZ, exit 0:
       20 named / 50 by address / 36 related, all lib/Prog, lib/Prog/CF, lib/U/Prog, lib/U/Prog/CF (plain and UBSan,
       fuzz_state + fuzz_preset + fuzz_manifest); a ls-tree of the four refs lists no lib/A or lib/B file for it.
       Templates used: fs's released plain/UBSan check_no_overread{,_blocks,_cmp}.v, fuzz_preset's
       check_no_overread_{seg,calls,end}.v. (2) named heads: (internal path) read 2026-10-29 02:3xZ, no row
       for check_no_overread. (3) cold heads: (an internal command) over the fs lib/A,B paths
       (2026-10-29 00:5xZ) lists only the stopped bespoke A/B route (lib/{A,B}/Prog/check_no_overread_*.v, text
       template) and this walk. (4) blob-set scan: NOT YET RUN (after a Theorem Labs lane's hold lifts). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret
FSW_rres FSW_frame FSW_strkit FSW_rd FSH_Fn_cno FSH_Fn_alloc FSW_check_no_overread_tbl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Fn_writer.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= pure facts ================= *)
(* the fake frame of class 1 is granted: at most FRL_CHECK = 1 frame is live at the call (restated from ENTRY's
   statement file FSH_Fn_entry.v:38-53, count_cid_le_length / fs_fake_granted, which this walk no longer loads: that
   file still passes CTX to check_no_overread_spec until ENTRY's CTX-drop twin) *)
Lemma cno_count_cid_le : forall cid (l : list (Z * Z)), count_cid cid l <= Z.of_nat (length l).
Proof.
  intros cid l. induction l as [|[c p] t IH]; cbn [count_cid length]; [lia|].
  destruct (c =? cid); lia.
Qed.
Lemma cno_grant : forall l : list (Z * Z), Z.of_nat (length l) <= FRL_CHECK -> count_cid 1 l < fs_frames 1.
Proof.
  intros l Hl. pose proof (cno_count_cid_le 1 l) as Hle.
  unfold fs_frames, kStackSizeLog. rewrite Z.shiftl_1_l.
  assert (Hp : 2 ^ 11 <= 2 ^ (20 - 6 - 1)) by (apply Z.pow_le_mono_r; lia).
  unfold FRL_CHECK in Hl. lia.
Qed.
(* the decoder runs with check_no_overread's own frame on top: at most FRL_CRT_CALLEE = 2 frames *)
Lemma cno_frames_callee : forall (f : Z * Z) (l : list (Z * Z)),
  Z.of_nat (length l) <= FRL_CHECK -> Z.of_nat (length (f :: l)) <= FRL_CRT_CALLEE.
Proof. intros f l Hl. cbn [length]. unfold FRL_CHECK, FRL_CRT_CALLEE in *. lia. Qed.
(* fs_heads depends only on ablocks *)
Lemma cno_heads : forall B ly S ly' S' U,
  ablocks B ly' S' = ablocks B ly S -> FSupoisonU.fs_heads B ly S U -> FSupoisonU.fs_heads B ly' S' U.
Proof. intros B ly S ly' S' U E H r Hr. rewrite E. exact (H r Hr). Qed.
(* quiet keeps the allocation counter away from g_fail_at, so no decoder allocation is refused *)
Lemma cno_not_fail : forall cnt fail k, quiet cnt fail k -> 0 <= k -> cnt + k <> fail.
Proof. intros cnt fail k (Hf & H0 & H1) Hk. unfold SIZE_MAXZ in Hf. lia. Qed.
Lemma cno_tick : forall c, 0 <= c -> c + 1 < 2 ^ 64 -> (c + 1) mod 2 ^ 64 = c + 1.
Proof. intros c H0 H1. apply Z.mod_small. lia. Qed.
(* the three texts the decoder reads are the same C string: past_nul's copy and the memcpy + memset tail both put
   db then a NUL, and db has no NUL of its own *)
Lemma cno_pn_prefix : forall (db : list Z) c, firstn (length db) (pn_copy db c) = db.
Proof.
  intros db c. unfold pn_copy. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. apply app_nil_r.
Qed.
Lemma cno_pn_nul : forall (db : list Z) c, nth (length db) (pn_copy db c) 0 = 0.
Proof.
  intros db c. unfold pn_copy. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma cno_pn_length : forall (db : list Z) c, Z.of_nat (length (pn_copy db c)) = Z.of_nat (length db) + 18.
Proof.
  intros db c. unfold pn_copy. rewrite !length_app, repeat_length. cbn [length]. lia.
Qed.

(* ===== entry and segment 0 of this lane (shape adapted from a Theorem Labs lane's crcs entry,
   a working branch c4bfd3bc057) ===== *)

(* the entry state: fss0T (the shadow-base cells) with the use-after-return cells (FSW_K fs_uar_regions) and the
   0xa0-byte frame of the prologue *)
Definition cno_ss0 : sstate := fss0T_args A_check_no_overread 160 fs_uar_regions [].
(* the state at the call of __asan_stack_malloc_1 (0x81238 -> 0x3d5f8): MEASURED (vm_compute) sp and s1 hold the
   re-aligned SAlu AND (SOff 2 (-160)) (SLit (-32)), a0 = 128, a2 = 1 (the flag: `beqz a2` not taken), s9 = the
   shadow base atom 32, s6 / s7 = the entry a1 / a0, ra = 0x8123c *)
Definition cno_ss1 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs cno_tbl FUEL PC_stack_malloc_1 cno_ss0).

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the image cells of B (owner RELOC: fs's TfibLib gives them, cgif A/ACeg.v:25-36 tl_got_shadow / tl_shadow_cell and
   the use-after-return pair; until it builds on S0 they are named premises, as FSW_K fsw_entryT / fsw_uar_regions_ok
   take them). Values MEASURED on the pinned fs.asan: GOT 0x9f6f0 -> 0xa7f38, GOT 0x9f748 -> 0xa7f40. *)
Hypothesis HGOT : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address.
Hypothesis HCELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address.
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.

Lemma cno_stk : STK_check_no_overread = 16847.
Proof. reflexivity. Qed.

Lemma cno_entry : forall ly S U (W : world tfibsegs) regs mem md ch,
  afn_preU tfibsegs B STK_check_no_overread ly S U W regs mem md ch ->
  st_ok tfibsegs (Ereg regs fs_extraT) cno_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_check_no_overread) mem (seg_rom tfibsegs))).
Proof.
intros ly S U W regs mem md ch HPRE.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _). pose proof cno_stk as FS.
assert (E2 : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
apply (fsw_entryT_args B _ 160 ly S U W regs mem md ch _ fs_uar_regions [] HGOT HCELL HPRE).
- lia.
- vm_compute. reflexivity.
- exact (fsw_uar_regions_ok B _ ly S U W regs mem md ch _ HGUAR HUCELL HPRE).
- apply pairwise_disjoint_of_extents.
  unfold fsT_regions_args, fsT_regions, fs_uar_regions, fs_got_uar_region, fs_uar_cell_region, fs_got_region,
    fs_bcell_region, fstk, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, fs_D_GOT_uar,
    fs_D_uar_cell.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
- exact I.
Qed.

(* segment 0: the prologue, the re-align and the flag test, up to the call of __asan_stack_malloc_1 *)
Lemma cno_seg0 : forall ly S U (W : world tfibsegs) regs mem md ch FP (Q : world tfibsegs -> config -> Prop),
  afn_preU tfibsegs B STK_check_no_overread ly S U W regs mem md ch ->
  (forall ms mat,
     st_ok tfibsegs (Ereg regs fs_extraT) cno_ss1 (restrict (w_H W) ms) ->
     ajournal tfibsegs B STK_check_no_overread (spZ regs) FP ly S W (unpoison U mem) md [] ly S W
       (unpoison U (ms_mem ms)) (with_vm_backing (m_vm_lazy md) mat md) 0 ->
     ARU tfibsegs B ly S U W (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) ->
     frame_of (Ereg regs fs_extraT) (ss_mem cno_ss0) mem (ms_mem ms) ->
     frame_of (Ereg regs fs_extraT) (ss_mem cno_ss0) (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) ->
     SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_check_no_overread regs mem md) Q.
Proof.
intros ly S U W regs mem md ch FP Q HPRE K.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _). pose proof cno_stk as FS.
pose proof (cno_entry ly S U W regs mem md ch HPRE) as HS.
pose proof (fsw_ARU B _ ly S U W regs mem md ch HPRE) as HARU.
pose proof (ajournal_init tfibsegs B STK_check_no_overread FP ly S W regs (unpoison U mem) md ch (proj1 HPRE))
  as HJ.
assert (Usp : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 A_check_no_overread) with (Z_to_bv 64 A_check_no_overread).
fsw_aj_run_toU cno_tbl_ok HS HJ HARU PC_stack_malloc_1.
{ awr_ok_tac. exact Usp. }
exact (K _ _ HS HJ HARU HF HFr).
Qed.

(* the registers at the call of __asan_stack_malloc_1 (read off cno_ss1): sp = s1 = the re-aligned sp1 (the frame
   drop 0xa0, then down to 32), a0 = 128 (class 1), ra = 0x8123c, gp / tp kept, s0 = the entry sp, s9 = the shadow
   base, s6 / s7 = the entry a1 / a0 *)
Lemma cno_sm_site : forall ly S U (W : world tfibsegs) regs mem md ch ms,
  afn_preU tfibsegs B STK_check_no_overread ly S U W regs mem md ch ->
  st_ok tfibsegs (Ereg regs fs_extraT) cno_ss1 (restrict (w_H W) ms) ->
  YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) /\
  YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) /\
  spZ regs - 176 <= 32 * ((spZ regs - 160) / 32) <= spZ regs - 160 /\ (32 * ((spZ regs - 160) / 32)) mod 32 = 0 /\
  YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 0x8123c /\ YK11.getr (ms_regs ms) 10%bv = Z_to_bv 64 128 /\
  YK11.getr (ms_regs ms) 3%bv = YK11.getr regs 3%bv /\ YK11.getr (ms_regs ms) 4%bv = YK11.getr regs 4%bv /\
  YK11.getr (ms_regs ms) 8%bv = YK11.getr regs 2%bv /\ YK11.getr (ms_regs ms) 25%bv = Z_to_bv 64 SHADOW_OFF /\
  YK11.getr (ms_regs ms) 22%bv = YK11.getr regs 11%bv /\ YK11.getr (ms_regs ms) 23%bv = YK11.getr regs 10%bv.
Proof.
intros ly S U W regs mem md ch ms HPRE HS.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _). pose proof cno_stk as FS.
set (E := Ereg regs fs_extraT) in *.
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs)) by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl);
  unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (fsw_realign_facts (spZ regs - 160) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (F1 & F2 & F3).
set (sp1 := 32 * ((spZ regs - 160) / 32)) in *.
assert (R2 : YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 sp1).
{ exact (fsw_realign_val E cno_ss1 (restrict (w_H W) ms) 2%bv 2 (-160) (spZ regs) HS
    ltac:(vm_compute; reflexivity) E2 ltac:(unfold spZ; apply u64_range) ltac:(lia)). }
assert (R9 : YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 sp1).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E cno_ss1 ms 9%bv HS).
  lazymatch goal with |- _ = Z_to_bv 64 ?v => change (sr_get (ss_regs cno_ss1) 9%bv) with
    (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32))) (SLit 0)) end.
  rewrite denot_lit_U, U_SAlu. f_equal. cbn [zalu_raw]. rewrite U_SLit.
  assert (UA : YP0e.U E (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32))) = sp1).
  { unfold YP0e.U. rewrite (denot_and_m32 E 2 (spZ regs) (-160) E2 ltac:(lia) ltac:(lia) ltac:(unfold spZ; apply u64_range)).
    apply wz. lia. }
  rewrite UA. change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
split; [exact R2|]. split; [exact R9|]. split; [lia|]. split; [exact F2|].
split; [exact (fsw_reg_lit _ E _ ms 1%bv 0x8123c HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
split; [exact (fsw_reg_lit _ E _ ms 10%bv 128 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 8%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split.
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E cno_ss1 ms 25%bv HS).
  change (sr_get (ss_regs cno_ss1) 25%bv) with (SOff 32 0). rewrite fsw_SOff0.
  subst E. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 22%bv 11%bv 11 HS ltac:(vm_compute; reflexivity) eq_refl)|].
exact (fsw_reg_atom _ regs fs_extraT _ ms 23%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl).
Qed.
End W.

(* ===== two helper lemmas of this lane (cno_chain's premises are crcs_chain's) ===== *)

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* ---- the frame-pointer chain at a callee's entry: check_no_overread keeps s0 = its entry sp with ra / s0 saved at
   sp0 - 8 / sp0 - 16, so a callee entered with s0 = sp0 sees check_no_overread's record on top of its own chain
   (YCbq.achain_push). Its room premise sp0 < ly_top - 16 is the spec's `spZ regs + 32 <= ly_top ly`
   (FSH_Fn_cno.v, a working branch 5946b5cae2b; the donor's form, cgif ACid.v:59). ---- *)
Lemma cno_chain : forall ly (rd rd' : reader) sp0 v ch ra spc,
  achain ly rd sp0 v ch -> sp0 + 32 <= ly_top ly -> ly_top ly <= 2 ^ 64 ->
  (forall a, sp0 <= a < 2 ^ 64 -> rd' a = rd a) ->
  rdword rd' (sp0 - 8) = Some ra -> rdword rd' (sp0 - 16) = Some v -> 4096 <= ra ->
  alloc_ceiling <= sp0 -> sp0 mod 8 = 0 -> spc + 16 <= sp0 ->
  achain ly rd' spc sp0 ((sp0, ra, v) :: ch).
Proof.
intros ly rd rd' sp0 v ch ra spc Hc Hroom Htop Hk H8 H16 Hra Hceil Hal Hsp.
exact (achain_push ly rd rd' sp0 v ra ch spc Hc Htop Hk H8 H16 Hra Hceil Hal ltac:(lia) Hsp).
Qed.

(* ---- the frame's shadow address (0x8127c `srli s2, s3, 3`, 0x812a4 `add s2, s2, s9`): with s3 = the fake frame F
   (atom 10) and s9 = SHADOW_OFF (atom 25), the engine leaves x18 = (F >> 3) + SHADOW_OFF (MEASURED: the probe run of
   the state at 0x8123c reaches 0x812a8 with that sr_get (ss_regs ss) 18%bv); the machine holds shadow_addr F ---- *)
Lemma cno_shadow_val : forall E ss ms (F : Z),
  st_ok tfibsegs E ss ms ->
  sr_get (ss_regs ss) 18%bv = SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 25 0) ->
  ew E 10 = Z_to_bv 64 F -> ew E 25 = Z_to_bv 64 SHADOW_OFF -> 0 <= F < 2 ^ 47 ->
  YK11.getr (ms_regs ms) 18%bv = Z_to_bv 64 (shadow_addr F).
Proof.
intros E ss ms F HS Hsr H10 H25 HF.
rewrite (st_ok_reg tfibsegs E ss ms 18%bv HS), Hsr, denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3.
rewrite (U_atom_off E 10 F 0 H10) by lia.
rewrite (U_atom_off E 25 SHADOW_OFF 0 H25) by (unfold SHADOW_OFF; lia).
rewrite !Z.add_0_r. unfold shadow_addr.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as D0.
assert (D1 : F / 8 <= F) by (apply Z.div_le_upper_bound; lia).
rewrite (Z.add_comm (F / 8) SHADOW_OFF). apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.
End W.

(* ================= the walk ================= *)
(* the prologue's saved words, as chunks of the s0 region: ra at -8, s0 at -16, s1 at -24, s2 .. s11 at -32 .. -104;
   their values are the walk's extra atoms 33 .. 45 (FSW_K.v xatom 0 .. 12) *)
Definition cno_sv_chunks : list YP09.chunk :=
  map (fun k => YP09.mkChunk (- 8 * (Z.of_nat k + 1)) (CVal 8 (SOff (33 + k) 0))) (seq 0 13).
(* the walk's extra atoms under the env Ereg regs' (fs_extraT ++ cno_extra ...): 32 = the shadow base (fs_extraT),
   33 .. 45 = the saved words (the ENTRY values of ra, s0, s1, s2 .. s11), 46 = the frame's flag address,
   47 = the frame's shadow address, 48 / 49 / 50 = the three raw blocks a / b / t *)
Definition cno_extra (regs : bvmap 5 word) (FL SH A Bp T : Z) : list word :=
  [YK11.getr regs 1%bv; YK11.getr regs 8%bv; YK11.getr regs 9%bv;
   YK11.getr regs 18%bv; YK11.getr regs 19%bv; YK11.getr regs 20%bv; YK11.getr regs 21%bv;
   YK11.getr regs 22%bv; YK11.getr regs 23%bv; YK11.getr regs 24%bv; YK11.getr regs 25%bv;
   YK11.getr regs 26%bv; YK11.getr regs 27%bv;
   Z_to_bv 64 FL; Z_to_bv 64 SH; Z_to_bv 64 A; Z_to_bv 64 Bp; Z_to_bv 64 T].
(* the three regions the walk re-adds after every program call: the fake frame at s3 (atom 19), its shadow at s2
   (atom 18) and the three real-stack slots at s1 (atom 9, window [0x10, 0x38): the frame address at 0x10, the
   first past_nul result at 0x18, the frame address again at 0x30) *)
Definition cno_fr_region (nF : nat) (csF : list YP09.chunk) : YP09.region := YP09.mkRegion (Some nF) 0 128 0 128 csF.
Definition cno_sh_region (nS : nat) : YP09.region := YP09.mkRegion (Some nS) 0 16 0 16 [].
Definition cno_sl_region (cssl : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 9%nat) 16 56 16 56 cssl.
(* the atom facts the engine needs past a call: the frame is a non-zero 32-aligned app address (so `beqz` on the
   reloaded frame address at 0x8146c is decided) and its shadow lies in the shadow band *)
Definition cno_gf (nF nS : nat) : list (nat * afact) :=
  [(nF, mkAF 4096 (2 ^ 47) 5); (nS, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0)].
(* the resume state of the walk after a call: FSW_rres's fss_ret_s0_args (the saved words at s0) with the fake
   frame at nF, its shadow at nS and the three real-stack slots at s1 *)
Definition cno_ss (r : Z) (nF nS : nat) (csF cssl : list YP09.chunk) : sstate :=
  fss_ret_s0_args r (-104) 0 cno_sv_chunks [cno_fr_region nF csF; cno_sh_region nS; cno_sl_region cssl]
    (cno_gf nF nS).

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* a fake frame and its own shadow never overlap: the frame is application memory, the shadow is the shadow band *)
Lemma cno_frame_shadow_disj : forall F, 4096 <= F -> in_app F 128 ->
  F + 128 <= shadow_addr F \/ shadow_addr F + 16 <= F.
Proof.
intros F H4096 Happ. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, app_addr, kLowShadowBeg, ASAN_CEIL, kLowMemEnd, kHighMemBeg, shadow_addr, SHADOW_OFF in *.
destruct Happ as (_ & [Hlo | [Hhi1 Hhi2]]); [left | right]; Z.div_mod_to_equations; lia.
Qed.

(* ---- the resume state after a program call (FSW_rres fsw_resume_after_rtU_s0): the saved words are kept because
   the callee may not write the caller's frame, the frame and its shadow are present and not runtime-owned
   (AR_frames_law), and the three real-stack slots lie in the journal's own window ---- *)
Lemma cno_after : forall STK sp0 FP ly S W0 mem md own lyc Sc U2 (W : world tfibsegs) mem2 md2 k
  regs2 memT extra r nF nS pos sp1 F csF cssl,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U2 mem2) md2 k ->
  ARU tfibsegs B lyc Sc U2 W mem2 md2 ->
  In (1, pos) (frames Sc) -> F = frame_addr lyc 1 pos ->
  YK11.getr regs2 8%bv = Z_to_bv 64 sp0 -> 104 <= STK ->
  bv_unsigned (ew (Ereg regs2 extra) 9) = sp1 ->
  bv_unsigned (ew (Ereg regs2 extra) nF) = F ->
  bv_unsigned (ew (Ereg regs2 extra) nS) = shadow_addr F ->
  sp0 - STK <= sp1 + 16 -> sp1 + 56 <= sp0 - 104 -> alloc_ceiling <= sp1 ->
  Forall (fun c => -104 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 0) cno_sv_chunks ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 extra) (mrestrict (w_H W) memT) sp0) cno_sv_chunks ->
  (forall a, sp0 + -104 <= a < sp0 + 0 -> mbyte tfibsegs (mrestrict (w_H W) mem2) a
     = mbyte tfibsegs (mrestrict (w_H W) memT) a) ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 extra) (mrestrict (w_H W) mem2) F) csF ->
  regions_wf (fss_ret_s0_regs (-104) 0 cno_sv_chunks
    [cno_fr_region nF csF; cno_sh_region nS; cno_sl_region cssl]) = true ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 extra) (mrestrict (w_H W) mem2) sp1) cssl ->
  st_ok tfibsegs (Ereg regs2 extra) (cno_ss r nF nS csF cssl)
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs))).
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc U2 W mem2 md2 k regs2 memT extra r nF nS pos sp1 F csF cssl
  HJ HARU Hin EF Hs0 HSTK E9 EnF EnS Hw1 Hw2 Hsp1 Hin104 Hcs Hkeep HcsF Hwf Hcssl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B lyc Sc U2 W mem2 md2 HARU) as HAR.
destruct (frames_bounds tfibsegs B LAWS lyc Sc W (unpoison U2 mem2) md2 1 pos HAR Hin) as (H4096 & Hceil & Happ).
destruct (al_frames _ _ LAWS lyc Sc W (unpoison U2 mem2) md2 1 pos HAR Hin) as (Hal32 & _ & Hfp & Hsp).
change (fs_frame_bytes 1) with 128 in H4096, Hceil, Happ, Hal32, Hfp.
change (fs_frame_bytes 1 / 8) with 16 in Hsp.
rewrite <- EF in H4096, Hceil, Happ, Hal32, Hfp, Hsp.
pose proof (shadow_addr_bounds F ltac:(lia)) as (Hs1 & Hs2).
pose proof (cno_frame_shadow_disj F ltac:(lia) Happ) as HFS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil2 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold cno_ss.
apply (fsw_resume_after_rtU_s0 B STK sp0 FP ly S W0 mem md own lyc Sc U2 W mem2 md2 k regs2 memT extra
  cno_sv_chunks _ (cno_gf nF nS) r (-104) 0 HJ HARU Hs0 ltac:(lia) ltac:(lia) ltac:(lia)).
- exact Hwf.
- exact Hin104.
- exact Hcs.
- exact Hkeep.
- constructor; [|constructor; [|constructor; [|constructor]]].
  + unfold cno_fr_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite EnF.
    split; [lia|]. split; [lia|]. split; [|exact HcsF].
    intros o Ho. apply (apresent_writable tfibsegs). destruct (Hfp (F + o) ltac:(lia)) as (Hp & Hno).
    exact (fsw_apresent_notowned B lyc Sc U2 W mem2 md2 (F + o) HARU ltac:(lia) Hno Hp).
  + unfold cno_sh_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite EnS.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable tfibsegs). destruct (Hsp o ltac:(lia)) as (Hp & Hno).
    exact (fsw_apresent_notowned B lyc Sc U2 W mem2 md2 (shadow_addr F + o) HARU ltac:(lia) Hno Hp).
  + unfold cno_sl_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
    split; [lia|]. split; [lia|]. split; [|exact Hcssl].
    intros o Ho. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B lyc Sc U2 W mem2 md2 _ HARU); [lia|]. apply Hpres. lia.
- apply pairwise_disjoint_of_extents.
  unfold fss_ret_s0_regs, cno_fr_region, cno_sh_region, cno_sl_region, fs_ret_s0_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  assert (E8 : bv_unsigned (ew (Ereg regs2 extra) 8) = sp0)
    by (rewrite (ew_Ereg_nat regs2 extra 8 8%bv eq_refl), Hs0; apply wz; lia).
  rewrite E8, E9, EnF, EnS.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  destruct HFS as [HFS | HFS];
  (repeat match goal with |- _ /\ _ => split end); try exact I; first [left; lia | right; lia].
- unfold cno_gf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite EnF, EnS. change (2 ^ 5) with 32. rewrite Z.pow_0_r.
  split; [split; [lia | split; [exact Hal32 | lia]]|].
  split; [|exact I]. unfold shadow_addr, SHADOW_OFF in *.
  split; [Z.div_mod_to_equations; lia | split; [apply Z.mod_1_r | Z.div_mod_to_equations; lia]].
Qed.

(* the write window of every run of the walk: the saved words and the slots are the walk's own stack window, the
   fake frame and its shadow are its own frame (ajournal's in_frames arm, own = [(1, pos)]; awr_byte0's fourth case) *)
Lemma cno_awr : forall E STK sp0 FP bl0 blc ly fr0 pos nF nS F sp1 cs1 cs2 cs3 cs4,
  bv_unsigned (ew E 8) = sp0 -> bv_unsigned (ew E nF) = F -> bv_unsigned (ew E nS) = shadow_addr F ->
  bv_unsigned (ew E 9) = sp1 -> F = frame_addr ly 1 pos ->
  104 <= STK -> sp0 - STK <= sp1 + 16 -> sp1 + 56 <= sp0 ->
  awr_ok tfibsegs B E [YP09.mkRegion (Some 8%nat) (-104) 0 (-104) 0 cs1; YP09.mkRegion (Some nF) 0 128 0 128 cs2;
            YP09.mkRegion (Some nS) 0 16 0 16 cs3; YP09.mkRegion (Some 9%nat) 16 56 16 56 cs4]
    STK sp0 FP bl0 blc ly [(1, pos)] fr0.
Proof.
intros E STK sp0 FP bl0 blc ly fr0 pos nF nS F sp1 cs1 cs2 cs3 cs4 E8 EF ES E9 HF HSTK Hw1 Hw2.
eapply awr_ok_cons_stack with (n := 8%nat); [reflexivity | exact E8 | cbn; lia | cbn; lia |].
eapply awr_ok_cons_gen with (k := nF) (b := F); [reflexivity | exact EF | |].
- intros a Ha. left. right; right; right. exists 1, pos. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd YP09.r_wlo YP09.r_whi] in *. change (fs_frame_bytes 1) with 128. rewrite <- HF. lia.
- eapply awr_ok_cons_gen with (k := nS) (b := shadow_addr F); [reflexivity | exact ES | |].
  + intros a Ha. left. right; right; right. exists 1, pos. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd YP09.r_wlo YP09.r_whi] in *. change (fs_frame_bytes 1 / 8) with 16. rewrite <- HF. lia.
  + eapply awr_ok_cons_stack_off with (n := 9%nat) (d := sp1 - sp0);
      [reflexivity | rewrite E9; lia | cbn; lia | cbn; lia | apply awr_ok_nil].
Qed.
Ltac cno_awr_tac E8 EF ES E9 :=
  lazymatch goal with |- awr_ok ?sg ?bs ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own ?fr0 =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bs E rs' stk sp0 fp b0 bc ly own fr0) end;
  eapply cno_awr; [exact E8 | exact EF | exact ES | exact E9 | reflexivity | lia | lia | lia].

(* ---- fuzz/alloc.c's statics (FS_PSTAT_FP, the four ledger cells) are image bytes, and no write window of the walk's
   symbolic states reaches them: the stack, the fake frame (no image byte, YCbq.frm_img), its shadow ---- *)
Lemma cno_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & H). apply (seg_covers_img (fst r) (snd r - fst r) a); [|lia].
unfold FS_PSTAT_FP in Hr. destruct Hr as [<- | [<- | [<- | [<- | []]]]]; vm_compute; reflexivity.
Qed.
Lemma cno_ledger_nowr : forall E rs a, inFP FS_PSTAT_FP a ->
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r \/ 0x5fd000 <= base_val E (YP09.r_base r) + YP09.r_wlo r \/
    (forall x, base_val E (YP09.r_base r) + YP09.r_wlo r <= x < base_val E (YP09.r_base r) + YP09.r_whi r ->
       ~ in_img tfibsegs x)) rs ->
  ~ in_wrange E rs a.
Proof.
intros E rs a Ha HF (r & Hr & Hw). pose proof (cno_pstat_img a Ha) as Hi.
assert (Hb : a < 0x5fd000).
{ destruct Ha as (q & Hq & Hq2). unfold FS_PSTAT_FP in Hq.
  destruct Hq as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hq2; lia. }
destruct (proj1 (Forall_forall _ _) HF r Hr) as [H | [H | H]]; [lia | lia | exact (H a Hw Hi)].
Qed.
(* the write windows depend on the regions' bases and windows only *)
Lemma cno_wr_skel : forall E rs rs' a,
  map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) rs =
  map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) rs' ->
  in_wrange E rs a -> in_wrange E rs' a.
Proof.
intros E rs. induction rs as [|r rs IH]; intros rs' a Hm (q & Hq & Hw); [destruct Hq|].
destruct rs' as [|r' rs']; [discriminate Hm|]. cbn [map] in Hm. injection Hm as E1 E2 E3 Hm.
destruct Hq as [<- | Hq].
- exists r'. split; [left; reflexivity|]. rewrite <- E1, <- E2, <- E3. exact Hw.
- destruct (IH rs' a Hm (ex_intro _ q (conj Hq Hw))) as (q' & Hq' & Hw'). exists q'. split; [right; exact Hq' | exact Hw'].
Qed.

(* ---- segment 1: the entry, the fake-frame grant and the frame set-up, to the state at 0x812a8 (the first store
   of the frame shadow, where the walk seats s2 on the shadow atom) ---- *)
(* the resume state at 0x8123c: the frame is in a0 (atom 10), its shadow address is the extra atom 47, nothing of
   the walk is in the three slots yet, and the frame's flag word (at 120) is the extra atom 46 *)
Definition cno_flag_chunk : list YP09.chunk := [YP09.mkChunk 120 (CVal 8 (SOff 46 0))].
Definition cno_ssA : sstate := cno_ss 0x8123c 10 47 cno_flag_chunk [].
Definition cno_ssB : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs cno_tbl FUEL 0x812a8 cno_ssA).
(* s2 is re-seated on the frame's shadow atom (47) before the sixteen shadow stores *)
Definition cno_ssB' : sstate :=
  mkSS (ss_pc cno_ssB) (sr_set (ss_regs cno_ssB) 18%bv (SOff 47 0)) (ss_mem cno_ssB) (ss_resv cno_ssB)
    (ss_facts cno_ssB).
Definition cno_ssC : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs cno_tbl FUEL A_past_nul cno_ssB').

(* ================= the walk's interface =================
   Every callee's S0 contract is a Section hypothesis, as the lane rule asks (the lanes' files restate the ones they
   use). No call-trace row: the CTX drop (owner a Theorem Labs lane 05:05Z) removed `In (raZ regs :: spine ch) CTX` and its
   binder from check_no_overread_spec, past_nul_spec and the allocator specs; the runtime allocators take C5's
   `In (call_trace ..) (as_universe B) \/ st_nev S < EV_MAX`, closed by the room premise; decode_spec_ff (writer) is
   CTX-free as well (a working branch faa7e2570e5). *)
(* the callee contracts (S0 statements, lib/A/FSH_Fn_*.v, CTX-free) *)
Hypothesis PN : past_nul_spec tfibsegs B.
Hypothesis DEC : FSH_Fn_writer.decode_spec_ff B tfibsegs.
Hypothesis FFREE : fuzz_free_spec tfibsegs B.
Hypothesis ABCMP : FSupoisonU.abcmp_realizesU tfibsegs B PC_bcmp.
Hypothesis AMEMCPY : FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
Hypothesis AMEMSET : FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.
Hypothesis AMALLOC : FSupoisonU.amalloc_realizesU tfibsegs B.
Hypothesis AFREE : FSupoisonU.afree_realizesU tfibsegs B.
Hypothesis IMG : fs_img_facts tfibsegs B.

Hypothesis HGOT : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address.
Hypothesis HCELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address.
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.
Hypothesis HSM1 : pc_stack_malloc (as_code B) 1 = PC_stack_malloc_1.
Hypothesis HMAL : pc_wrap_malloc (as_code B) = PC_malloc.
Hypothesis HFRE : pc_wrap_free (as_code B) = PC_free.
Hypothesis ASM1 : astack_malloc_realizesU tfibsegs B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FS_ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).

Ltac cno_cs_side :=
  unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?q] =>
    let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.

(* the thirteen saved words of the prologue, read off the call-site state and re-expressed over the walk's extra
   atoms 33 .. 45, which are exactly those registers' entry values *)
Lemma cno_saved_chunks : forall (W : world tfibsegs) regs (ms : machine_state) regs2 FL SH A Bp T,
  st_ok tfibsegs (Ereg regs fs_extraT) cno_ss1 (restrict (w_H W) ms) ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (fs_extraT ++ cno_extra regs FL SH A Bp T))
            (mrestrict (w_H W) (ms_mem ms)) (spZ regs)) cno_sv_chunks.
Proof.
intros W regs ms regs2 FL SH A Bp T HS.
assert (Usp : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
pose proof (fsw_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
unfold cno_sv_chunks. cbn [seq map Z.of_nat Nat.add].
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val tfibsegs _ _ _ (-8) 8%N (SOff 33 0) (bv_unsigned (YK11.getr regs 1%bv))).
  + rewrite fsw_SOff0. change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra.
    cbn [cno_extra fs_extraT app nth]. symmetry. apply Z_to_bv_bv_unsigned.
  + apply u64_range.
  + cbn; lia.
  + apply (fsw_field _ _ 2 _ _ _ _ _ _ (-8) 8%N (SOff 1 0) (bv_unsigned (YK11.getr regs 1%bv)) HR0 Usp
      ltac:(cbn; tauto)); [| apply u64_range | cbn; lia].
    rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 1 1%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
- apply (chunk_ok_val tfibsegs _ _ _ (-16) 8%N (SOff 34 0) (bv_unsigned (YK11.getr regs 8%bv))).
  + rewrite fsw_SOff0. change 34%nat with (32 + 2)%nat. rewrite ew_Ereg_extra.
    cbn [cno_extra fs_extraT app nth]. symmetry. apply Z_to_bv_bv_unsigned.
  + apply u64_range.
  + cbn; lia.
  + apply (fsw_field _ _ 2 _ _ _ _ _ _ (-16) 8%N (SOff 8 0) (bv_unsigned (YK11.getr regs 8%bv)) HR0 Usp
      ltac:(cbn; tauto)); [| apply u64_range | cbn; lia].
    rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 8 8%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
- apply (chunk_ok_val tfibsegs _ _ _ (-24) 8%N (SOff 35 0) (bv_unsigned (YK11.getr regs 9%bv))).
  + rewrite fsw_SOff0. change 35%nat with (32 + 3)%nat. rewrite ew_Ereg_extra.
    cbn [cno_extra fs_extraT app nth]. symmetry. apply Z_to_bv_bv_unsigned.
  + apply u64_range.
  + cbn; lia.
  + apply (fsw_field _ _ 2 _ _ _ _ _ _ (-24) 8%N (SOff 9 0) (bv_unsigned (YK11.getr regs 9%bv)) HR0 Usp
      ltac:(cbn; tauto)); [| apply u64_range | cbn; lia].
    rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 9 9%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
- apply (chunk_ok_val tfibsegs _ _ _ (-32) 8%N (SOff 36 0) (bv_unsigned (YK11.getr regs 18%bv))).
  + rewrite fsw_SOff0. change 36%nat with (32 + 4)%nat. rewrite ew_Ereg_extra.
    cbn [cno_extra fs_extraT app nth]. symmetry. apply Z_to_bv_bv_unsigned.
  + apply u64_range.
  + cbn; lia.
  + apply (fsw_field _ _ 2 _ _ _ _ _ _ (-32) 8%N (SOff 18 0) (bv_unsigned (YK11.getr regs 18%bv)) HR0 Usp
      ltac:(cbn; tauto)); [| apply u64_range | cbn; lia].
    rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 18 18%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
- apply (chunk_ok_val tfibsegs _ _ _ (-40) 8%N (SOff 37 0) (bv_unsigned (YK11.getr regs 19%bv))).
  + rewrite fsw_SOff0. change 37%nat with (32 + 5)%nat. rewrite ew_Ereg_extra.
    cbn [cno_extra fs_extraT app nth]. symmetry. apply Z_to_bv_bv_unsigned.
  + apply u64_range.
  + cbn; lia.
  + apply (fsw_field _ _ 2 _ _ _ _ _ _ (-40) 8%N (SOff 19 0) (bv_unsigned (YK11.getr regs 19%bv)) HR0 Usp
      ltac:(cbn; tauto)); [| apply u64_range | cbn; lia].
    rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 19 19%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
- apply (chunk_ok_val tfibsegs _ _ _ (-48) 8%N (SOff 38 0) (bv_unsigned (YK11.getr regs 20%bv))).
  + rewrite fsw_SOff0. change 38%nat with (32 + 6)%nat. rewrite ew_Ereg_extra.
    cbn [cno_extra fs_extraT app nth]. symmetry. apply Z_to_bv_bv_unsigned.
  + apply u64_range.
  + cbn; lia.
  + apply (fsw_field _ _ 2 _ _ _ _ _ _ (-48) 8%N (SOff 20 0) (bv_unsigned (YK11.getr regs 20%bv)) HR0 Usp
      ltac:(cbn; tauto)); [| apply u64_range | cbn; lia].
    rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 20 20%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
- apply (chunk_ok_val tfibsegs _ _ _ (-56) 8%N (SOff 39 0) (bv_unsigned (YK11.getr regs 21%bv))).
  + rewrite fsw_SOff0. change 39%nat with (32 + 7)%nat. rewrite ew_Ereg_extra.
    cbn [cno_extra fs_extraT app nth]. symmetry. apply Z_to_bv_bv_unsigned.
  + apply u64_range.
  + cbn; lia.
  + apply (fsw_field _ _ 2 _ _ _ _ _ _ (-56) 8%N (SOff 21 0) (bv_unsigned (YK11.getr regs 21%bv)) HR0 Usp
      ltac:(cbn; tauto)); [| apply u64_range | cbn; lia].
    rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 21 21%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
- apply (chunk_ok_val tfibsegs _ _ _ (-64) 8%N (SOff 40 0) (bv_unsigned (YK11.getr regs 22%bv))).
  + rewrite fsw_SOff0. change 40%nat with (32 + 8)%nat. rewrite ew_Ereg_extra.
    cbn [cno_extra fs_extraT app nth]. symmetry. apply Z_to_bv_bv_unsigned.
  + apply u64_range.
  + cbn; lia.
  + apply (fsw_field _ _ 2 _ _ _ _ _ _ (-64) 8%N (SOff 22 0) (bv_unsigned (YK11.getr regs 22%bv)) HR0 Usp
      ltac:(cbn; tauto)); [| apply u64_range | cbn; lia].
    rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 22 22%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
- apply (chunk_ok_val tfibsegs _ _ _ (-72) 8%N (SOff 41 0) (bv_unsigned (YK11.getr regs 23%bv))).
  + rewrite fsw_SOff0. change 41%nat with (32 + 9)%nat. rewrite ew_Ereg_extra.
    cbn [cno_extra fs_extraT app nth]. symmetry. apply Z_to_bv_bv_unsigned.
  + apply u64_range.
  + cbn; lia.
  + apply (fsw_field _ _ 2 _ _ _ _ _ _ (-72) 8%N (SOff 23 0) (bv_unsigned (YK11.getr regs 23%bv)) HR0 Usp
      ltac:(cbn; tauto)); [| apply u64_range | cbn; lia].
    rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 23 23%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
- apply (chunk_ok_val tfibsegs _ _ _ (-80) 8%N (SOff 42 0) (bv_unsigned (YK11.getr regs 24%bv))).
  + rewrite fsw_SOff0. change 42%nat with (32 + 10)%nat. rewrite ew_Ereg_extra.
    cbn [cno_extra fs_extraT app nth]. symmetry. apply Z_to_bv_bv_unsigned.
  + apply u64_range.
  + cbn; lia.
  + apply (fsw_field _ _ 2 _ _ _ _ _ _ (-80) 8%N (SOff 24 0) (bv_unsigned (YK11.getr regs 24%bv)) HR0 Usp
      ltac:(cbn; tauto)); [| apply u64_range | cbn; lia].
    rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 24 24%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
- apply (chunk_ok_val tfibsegs _ _ _ (-88) 8%N (SOff 43 0) (bv_unsigned (YK11.getr regs 25%bv))).
  + rewrite fsw_SOff0. change 43%nat with (32 + 11)%nat. rewrite ew_Ereg_extra.
    cbn [cno_extra fs_extraT app nth]. symmetry. apply Z_to_bv_bv_unsigned.
  + apply u64_range.
  + cbn; lia.
  + apply (fsw_field _ _ 2 _ _ _ _ _ _ (-88) 8%N (SOff 25 0) (bv_unsigned (YK11.getr regs 25%bv)) HR0 Usp
      ltac:(cbn; tauto)); [| apply u64_range | cbn; lia].
    rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 25 25%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
- apply (chunk_ok_val tfibsegs _ _ _ (-96) 8%N (SOff 44 0) (bv_unsigned (YK11.getr regs 26%bv))).
  + rewrite fsw_SOff0. change 44%nat with (32 + 12)%nat. rewrite ew_Ereg_extra.
    cbn [cno_extra fs_extraT app nth]. symmetry. apply Z_to_bv_bv_unsigned.
  + apply u64_range.
  + cbn; lia.
  + apply (fsw_field _ _ 2 _ _ _ _ _ _ (-96) 8%N (SOff 26 0) (bv_unsigned (YK11.getr regs 26%bv)) HR0 Usp
      ltac:(cbn; tauto)); [| apply u64_range | cbn; lia].
    rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 26 26%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
- apply (chunk_ok_val tfibsegs _ _ _ (-104) 8%N (SOff 45 0) (bv_unsigned (YK11.getr regs 27%bv))).
  + rewrite fsw_SOff0. change 45%nat with (32 + 13)%nat. rewrite ew_Ereg_extra.
    cbn [cno_extra fs_extraT app nth]. symmetry. apply Z_to_bv_bv_unsigned.
  + apply u64_range.
  + cbn; lia.
  + apply (fsw_field _ _ 2 _ _ _ _ _ _ (-104) 8%N (SOff 27 0) (bv_unsigned (YK11.getr regs 27%bv)) HR0 Usp
      ltac:(cbn; tauto)); [| apply u64_range | cbn; lia].
    rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 27 27%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* the register file at the return of __asan_stack_malloc_1 (0x8123c), as the walk's later segments read it through
   the env Ereg regs2 ..: sp = s1 = the re-aligned sp1, s0 = the entry sp, gp / tp the entry's, a0 = the frame F,
   s6 / s7 = the entry len / d, s9 = the shadow base *)
Definition cno_r2 (regs regs2 : bvmap 5 word) (F : Z) : Prop :=
  YK11.getr regs2 2%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) /\
  YK11.getr regs2 9%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) /\
  YK11.getr regs2 8%bv = Z_to_bv 64 (spZ regs) /\
  YK11.getr regs2 3%bv = YK11.getr regs 3%bv /\ YK11.getr regs2 4%bv = YK11.getr regs 4%bv /\
  YK11.getr regs2 10%bv = Z_to_bv 64 F /\
  YK11.getr regs2 22%bv = YK11.getr regs 11%bv /\ YK11.getr regs2 23%bv = YK11.getr regs 10%bv /\
  YK11.getr regs2 25%bv = Z_to_bv 64 SHADOW_OFF.

Lemma cno_seg1 : forall ly S U (W : world tfibsegs) regs mem md ch (Q : world tfibsegs -> config -> Prop),
  afn_preU tfibsegs B STK_check_no_overread ly S U W regs mem md ch ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  Z.of_nat (length (frames S)) <= FRL_CHECK ->
  (forall S2 pos regs2 md2 (ms : machine_state) mat,
     let F := frame_addr ly 1 pos in
     let E := Ereg regs2 (fs_extraT ++ cno_extra regs (flag_addr ly 1 pos) (shadow_addr F) 0 0 0) in
     st_ok tfibsegs E cno_ssC (restrict (w_H W) ms) ->
     ajournal tfibsegs B STK_check_no_overread (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md [(1, pos)]
       ly S2 W (unpoison U (ms_mem ms)) (with_vm_backing (m_vm_lazy md2) mat md2) 0 ->
     ARU tfibsegs B ly S2 U W (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) ->
     In (1, pos) (frames S2) -> frames S2 = (1, pos) :: frames S ->
     ablocks B ly S2 = ablocks B ly S -> st_nev S2 = st_nev S -> blocks_bytes S2 = blocks_bytes S ->
     cno_r2 regs regs2 F ->
     (forall a, inFP FS_PSTAT_FP a -> aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) mem a) ->
     SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md2) mat md2)) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_check_no_overread regs mem md) Q.
Proof.
intros ly S U W regs mem md ch Q HPRE HRO Hfr K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof cno_stk as FS.
set (sp1 := 32 * ((spZ regs - 160) / 32)) in *.
apply (cno_seg0 B HGOT HCELL HGUAR HUCELL ly S U W regs mem md ch FS_PSTAT_FP Q HPRE).
intros ms mat HS HJ HARU HF HFr.
destruct (cno_sm_site B ly S U W regs mem md ch ms HPRE HS)
  as (R2 & R9 & Hsp1r & Hsp1al & R1 & R10 & R3 & R4 & R8 & R25 & R22 & R23).
fold sp1 in R2, R9, Hsp1r, Hsp1al.
pose proof HPRE as (HAP & _ & _).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
assert (Hsp1b : 0 <= sp1 < 2 ^ 64) by lia.
assert (Hspc : spZ (ms_regs ms) = spZ regs + (sp1 - spZ regs))
  by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) (Ereg regs fs_extraT) cno_ss1 ms HS eq_refl).
replace (ss_pc cno_ss1) with (pc_stack_malloc (as_code B) 1) by (rewrite HSM1; vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (fsw_stack_malloc_atU B FS_ENV ML SMP 1 ASM1 ltac:(lia) W (ms_regs ms) (ms_mem ms)
    STK_check_no_overread (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md [] ly S U _ 0
    (sp1 - spZ regs) _ HJ HARU Hspc).
  all: try (rewrite R3; exact Hgp).
  all: try (rewrite R4; exact Htp).
  all: try exact R1.
  all: try (apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity).
  all: try exact (cno_grant (frames S) Hfr).
  all: try (unfold ESTACK in *; lia).
}
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HARU2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin
  & Hnev2 & Hbb2 & Hz & Hflag & HK).
set (F := frame_addr ly 1 pos) in *. set (FL := flag_addr ly 1 pos) in *.
set (E := Ereg regs2 (fs_extraT ++ cno_extra regs FL (shadow_addr F) 0 0 0)) in *.
assert (Hin2 : In (1, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (ARU_AR tfibsegs B ly S2 U W mem2 md2 HARU2) as HAR2.
destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 1 pos HAR2 Hin2) as (HF4096 & HFceil & HFapp).
destruct (al_flag _ _ LAWS ly S2 W (unpoison U mem2) md2 1 pos HAR2 Hin2) as (_ & _ & HFLapp & _).
change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp. fold F in HF4096, HFceil, HFapp. fold FL in HFLapp.
assert (HFL64 : 0 <= FL < 2 ^ 64) by (unfold in_app, kLowShadowBeg, ASAN_CEIL in HFLapp; lia).
assert (E8 : YK11.getr regs2 8%bv = Z_to_bv 64 (spZ regs)).
{ rewrite (fsw_pres _ _ 8%bv HP2 ltac:(cno_cs_side)), R8. unfold spZ.
  symmetry. apply Z_to_bv_bv_unsigned. }
assert (E8' : bv_unsigned (ew E 8) = spZ regs).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), E8. apply wz. lia. }
assert (E9 : bv_unsigned (ew E 9) = sp1).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl),
    (fsw_pres _ _ 9%bv HP2 ltac:(cno_cs_side)), R9. apply wz. lia. }
assert (E10 : bv_unsigned (ew E 10) = F).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl), Ha0. unfold w64. apply wz. lia. }
assert (E47 : bv_unsigned (ew E 47) = shadow_addr F).
{ subst E. change 47%nat with (32 + 15)%nat. rewrite ew_Ereg_extra.
  cbn [fs_extraT cno_extra app nth]. apply wz.
  pose proof (shadow_addr_bounds F ltac:(lia)) as (Hs1 & Hs2). lia. }
assert (E46 : ew E 46 = Z_to_bv 64 FL).
{ subst E. change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra.
  cbn [fs_extraT cno_extra app nth]. reflexivity. }
assert (HS2 : st_ok tfibsegs E cno_ssA
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x8123c) mem2 (seg_rom tfibsegs)))).
{ unfold cno_ssA.
  eapply (cno_after STK_check_no_overread (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md [(1, pos)] ly S2 U
    W mem2 md2 0 regs2 (ms_mem ms) (fs_extraT ++ cno_extra regs FL (shadow_addr F) 0 0 0) 0x8123c 10 47 pos sp1 F
    cno_flag_chunk []).
  - exact HJ2.
  - exact HARU2.
  - exact Hin2.
  - reflexivity.
  - exact E8.
  - lia.
  - exact E9.
  - exact E10.
  - exact E47.
  - lia.
  - lia.
  - lia.
  - unfold cno_sv_chunks; cbn [seq map]; repeat apply Forall_cons; try apply Forall_nil; cbn; lia.
  - exact (cno_saved_chunks W regs ms regs2 FL (shadow_addr F) 0 0 0 HS).
  - intros a Ha. apply (mbyte_of_aview tfibsegs).
    rewrite <- (fsw_aview_unpoison_high B ly S2 U W mem2 md2 _ HARU2) by lia.
    rewrite <- (fsw_aview_unpoison_high B ly S U W (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) _ HARU) by lia.
    destruct HK as (K1 & _). apply K1; lia.
  - constructor; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs _ _ F 120 8%N (SOff 46 0) FL).
    + rewrite fsw_SOff0. exact E46.
    + lia.
    + cbn; lia.
    + replace (F + 120) with (F + 128 - 8) by lia.
      exact (val_mem_of_rdword tfibsegs (w_H W) mem2 _ _ Hflag).
  - vm_compute. reflexivity.
  - apply Forall_nil. }
fsw_aj_run_toU cno_tbl_ok HS2 HJ2 HARU2 0x812a8.
{ cno_awr_tac E8' E10 E47 E9. }
assert (R25b : YK11.getr regs2 25%bv = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (fsw_pres _ _ 25%bv HP2 ltac:(cno_cs_side)); exact R25).
assert (E25 : ew E 25 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 25 25%bv eq_refl); exact R25b).
assert (E10' : ew E 10 = Z_to_bv 64 F)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl), Ha0; reflexivity).
assert (R18 : YK11.getr (ms_regs (restrict (w_H W) ms0)) 18%bv = Z_to_bv 64 (shadow_addr F))
  by (exact (cno_shadow_val E cno_ssB _ F HS2 ltac:(vm_compute; reflexivity) E10' E25 ltac:(lia))).
assert (Hne18 : (18%bv : bv 5) <> 0%bv).
{ intro Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate Hc. }
assert (Hv18 : YK11.getr (ms_regs (restrict (w_H W) ms0)) 18%bv = sv_denot E (SOff 47 0)).
{ rewrite R18, fsw_SOff0, <- E47. apply Z_to_bv_bv_unsigned. }
pose proof (YI08.st_ok_set_reg tfibsegs E cno_ssB (restrict (w_H W) ms0) 18%bv (SOff 47 0) HS2 Hne18 Hv18) as HS3.
fold cno_ssB' in HS3.
fsw_aj_run_toU cno_tbl_ok HS3 HJ2 HARU2 A_past_nul.
{ cno_awr_tac E8' E10 E47 E9. }
apply (K S2 pos regs2 md2 ms1 mat1 HS3 HJ2 HARU2 Hin2 Hfrs2 Eab Hnev2 Hbb2).
- split; [rewrite (fsw_pres _ _ 2%bv HP2 ltac:(cno_cs_side)); exact R2|].
  split; [rewrite (fsw_pres _ _ 9%bv HP2 ltac:(cno_cs_side)); exact R9|].
  split; [exact E8|].
  split; [rewrite (fsw_pres _ _ 3%bv HP2 ltac:(cno_cs_side)); exact R3|].
  split; [rewrite (fsw_pres _ _ 4%bv HP2 ltac:(cno_cs_side)); exact R4|].
  split; [rewrite Ha0; reflexivity|].
  split; [rewrite (fsw_pres _ _ 22%bv HP2 ltac:(cno_cs_side)); exact R22|].
  split; [rewrite (fsw_pres _ _ 23%bv HP2 ltac:(cno_cs_side)); exact R23|].
  exact R25b.
- (* the ledger cells: kept by the prologue run (stack only), by __asan_stack_malloc_1 (acall_kept's image clause,
     the cells are no owned static and not errno: IMG), and by the two frame runs (frame, shadow, stack only) *)
  intros a Ha.
  pose proof (cno_pstat_img a Ha) as Hai. pose proof (fs_segs_low a Hai) as Hlow.
  assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold kLowMemEnd in Hlow; lia).
  assert (Hsh : a < SHADOW_OFF) by (unfold kLowMemEnd, SHADOW_OFF in *; lia).
  pose proof IMG as (HIMG & _). destruct (HIMG a Ha) as (Hno & Hne).
  assert (WA : forall rs E0, map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) rs =
      map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) (ss_mem cno_ssA) ->
      bv_unsigned (ew E0 8) = spZ regs -> bv_unsigned (ew E0 10) = F -> bv_unsigned (ew E0 47) = shadow_addr F ->
      bv_unsigned (ew E0 9) = sp1 -> ~ in_wrange E0 rs a).
  { intros rs E0 Hm X8 X10 X47 X9 Hw. apply (cno_wr_skel E0 rs (ss_mem cno_ssA) a Hm) in Hw. revert Hw.
    apply (cno_ledger_nowr E0 _ a Ha).
    unfold cno_ssA, cno_ss, fss_ret_s0_args, fss_ret_s0_regs, fs_ret_s0_region, cno_fr_region, cno_sh_region,
      cno_sl_region. cbn [ss_mem].
    repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
      rewrite ?X8, ?X10, ?X47, ?X9.
    - right; left. lia.
    - right; right. intros x Hx. exact (frm_img tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 1 pos x HAR2 Hin2
        ltac:(change (fs_frame_bytes 1) with 128; fold F; lia)).
    - right; left. pose proof (shadow_addr_bounds F ltac:(lia)) as (Hs1 & Hs2). unfold kLowMemEnd in Hs1. lia.
    - right; left. lia. }
  assert (E1 : ms_mem ms1 (Z_to_bv 64 a) = ms_mem ms0 (Z_to_bv 64 a)).
  { apply HF1. rewrite (wz a Ha64).
    apply (WA (ss_mem cno_ssB') E ltac:(vm_compute; reflexivity) E8' E10 E47 E9). }
  assert (E2 : ms_mem ms0 (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
  { apply HF0. rewrite (wz a Ha64). apply (WA (ss_mem cno_ssA) E eq_refl E8' E10 E47 E9). }
  assert (E3 : aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) (ms_mem ms) a).
  { destruct HK as (_ & _ & K3 & _).
    assert (Hush : in_ush U (bv_unsigned (Z_to_bv 64 a)) = false).
    { rewrite (wz a Ha64). destruct (in_ush U a) eqn:Eu; [|reflexivity]. exfalso.
      destruct (ush_facts tfibsegs B ly S2 U W _ _ a HARU2 Eu) as (_ & L1 & _). lia. }
    rewrite <- (aview_unpoison_out tfibsegs (w_H W) U mem2 a Hush).
    rewrite <- (aview_unpoison_out tfibsegs (w_H W) U (ms_mem ms) a Hush).
    exact (K3 a Hai Hno Hne). }
  assert (E4 : ms_mem ms (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { apply HF. rewrite (wz a Ha64). apply (cno_ledger_nowr _ _ a Ha).
    unfold cno_ss0, fss0T_args, fsT_regions_args, fsT_regions, fs_uar_regions, fs_got_uar_region,
      fs_uar_cell_region, fs_got_region, fs_bcell_region, fstk. cbn [ss_mem app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
      try (left; lia).
    right; left. rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl). change (bv_unsigned (YK11.getr regs 2%bv)) with (spZ regs).
    lia. }
  rewrite (aview_at tfibsegs (w_H W) (ms_mem ms1) (ms_mem ms0) a E1),
    (aview_at tfibsegs (w_H W) (ms_mem ms0) mem2 a E2), E3.
  exact (aview_at tfibsegs (w_H W) (ms_mem ms) mem a E4).
Qed.
End W.

(* ================= the call-step interface, shared by the lanes that walk this function's call sites:
   this file (past_nul, 0x812f8 / 0x8130c), _mem.v (__wrap_malloc 0x8131c, __asan_memcpy 0x81338, __asan_memset 0x81354),
   _dec.v (preset_base64_decode 0x81398 / 0x813a8 / 0x813b8), _tail.v and _ret.v (bcmp 0x813f8 / 0x81414, fuzz_free
   0x81420 / 0x81428 / 0x81430, __wrap_free 0x81438 / 0x81440 / 0x81448, the epilogue and the ret), chained by _top.v.
   Definitions and statements (Props) only; each lane proves its statement, the top file takes it as a named Section
   hypothesis of exactly that Prop until the lane's file lands. A call step goes from the machine at the callee's
   entry (cno_site: the walk's journal from the entry, ARU, the registers check_no_overread keeps) to the machine at
   the return address (cno_ret: the composed journal, ARU, the callee-saved registers, the bytes cno_zone of the
   walk's own stack and frame kept, and the callee's own facts P). The top file rebuilds the symbolic resume state
   from cno_ret with cno_after. ================= *)
(* the walk context: check_no_overread_spec's entry state and arguments (FSH_Fn_cno.v:35) and the position of the
   class-1 fake frame __asan_stack_malloc_1 grants at 0x81238 *)
Record cnocx := mkCNOCX {
  c_ly : alayout; c_S : astate; c_U : list (Z * Z); c_W : world tfibsegs; c_regs : bvmap 5 word;
  c_mem : word -> option byte; c_md : Model; c_ch : list (Z * Z * Z); c_d : Z; c_db : list Z;
  c_live : Z; c_peak : Z; c_cnt : Z; c_fail : Z; c_fpos : Z }.
(* the entry sp (s0 from 0x81204 on), the re-aligned sp (sp and s1 from 0x8120c on), the fake frame (s3 from 0x81248
   on), its flag word's target, its 16 shadow bytes (s2 from 0x812a4 on), the text's length *)
Definition cno_sp0 (cx : cnocx) : Z := spZ (c_regs cx).
Definition cno_sp1 (cx : cnocx) : Z := 32 * ((cno_sp0 cx - 160) / 32).
Definition cno_F (cx : cnocx) : Z := frame_addr (c_ly cx) 1 (c_fpos cx).
Definition cno_FL (cx : cnocx) : Z := flag_addr (c_ly cx) 1 (c_fpos cx).
Definition cno_SF (cx : cnocx) : Z := shadow_addr (cno_F cx).
Definition cno_n (cx : cnocx) : Z := Z.of_nat (length (c_db cx)).
(* the bytes every call keeps: the saved words [sp0 - 104, sp0), the slots [sp1 + 16, sp1 + 56), the fake frame and
   its shadow *)
Definition cno_zone (cx : cnocx) (a : Z) : Prop :=
  (cno_sp0 cx - 104 <= a < cno_sp0 cx) \/ (cno_sp1 cx + 16 <= a < cno_sp1 cx + 56) \/
  (cno_F cx <= a < cno_F cx + 128) \/ (cno_SF cx <= a < cno_SF cx + 16).
(* the thirteen registers the prologue saves, in the order of cno_sv_chunks / cno_extra (extra atoms 33 .. 45) *)
Definition cno_saved_regs : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* check_no_overread_spec's premises (FSH_Fn_cno.v, CTX-free form of a working branch 1566ec4f042), at the context *)
Definition cno_base (cx : cnocx) : Prop :=
  fpreU tfibsegs B STK_check_no_overread (c_ly cx) (c_S cx) (c_U cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx)
    (c_ch cx) /\
  FSupoisonU.fs_heads B (c_ly cx) (c_S cx) (c_U cx) /\
  Z.of_nat (length (frames (c_S cx))) <= FRL_CHECK /\
  spZ (c_regs cx) + 32 <= ly_top (c_ly cx) /\
  getr (c_regs cx) 10 = w64 (c_d cx) /\ getr (c_regs cx) 11 = w64 (cno_n cx) /\
  src_rd tfibsegs (c_W cx) (c_mem cx) (c_d cx) (c_db cx) /\ Forall (fun c => c <> 0) (c_db cx) /\
  (0 < cno_n cx -> exists b m, In (b, m) (ablocks B (c_ly cx) (c_S cx)) /\ b <= c_d cx /\
     c_d cx + cno_n cx <= b + m) /\
  cno_n cx <= PRESET_FILE_MAX_BYTES /\
  fs_glob tfibsegs (c_W cx) (c_mem cx) (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx) /\
  quiet (c_cnt cx) (c_fail cx) 3 /\
  c_live cx + 3 * FSH_Fn_writer.dec_size (c_db cx) < 2 ^ 64 /\
  st_nev (c_S cx) + EV_check_no_overread <= EV_MAX /\
  blocks_bytes (c_S cx) + LIVE_check_no_overread <= LIVE_MAX.

(* check_no_overread_spec's post, at the context *)
Definition cno_post (cx : cnocx) : world tfibsegs -> config -> Prop :=
  fpostU tfibsegs B STK_check_no_overread (cno_sp0 cx) FS_PSTAT_FP (c_regs cx) (c_ly cx) (c_S cx) (c_U cx)
    (c_W cx) (c_mem cx) (c_md cx) EV_check_no_overread (c_U cx)
    (fun ly' S' W' regs' mem' md' =>
       ablocks B ly' S' = ablocks B (c_ly cx) (c_S cx) /\
       exists peak', c_peak cx <= peak' /\ fs_glob tfibsegs W' mem' (c_live cx) peak' (c_cnt cx + 3) (c_fail cx)).

(* the walk's journal from the entry, over the unpoisoned memories, while it holds its fake frame *)
Definition cno_J (cx : cnocx) (k : Z) (ly : alayout) (S : astate) (W : world tfibsegs)
  (mem : word -> option byte) (md : Model) : Prop :=
  ajournal tfibsegs B STK_check_no_overread (cno_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(1, c_fpos cx)] ly S W mem md k.

(* the machine at the entry of one of the walk's callees (regs, mem: the call's register file and memory): the
   journal, ARU, the heads, sp = s1 = sp1, s0 = sp0, gp / tp the entry's, a return address, and the two words the
   prologue saved at sp0 - 8 / sp0 - 16 (the entry ra and s0: the callee's frame chain, cno_chain) *)
Definition cno_site (cx : cnocx) (k : Z) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  cno_J cx k ly S W (unpoison U mem) md /\ ARU tfibsegs B ly S U W mem md /\ FSupoisonU.fs_heads B ly S U /\
  getr regs 2 = w64 (cno_sp1 cx) /\ getr regs 8 = w64 (cno_sp0 cx) /\
  getr regs 3 = getr (c_regs cx) 3 /\ getr regs 4 = getr (c_regs cx) 4 /\
  YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
  rdword (aview tfibsegs (w_H W) mem) (cno_sp0 cx - 8) = Some (raZ (c_regs cx)) /\
  rdword (aview tfibsegs (w_H W) mem) (cno_sp0 cx - 16) = Some (s0Z (c_regs cx)).

(* the machine back at the call's return address (ly, S, regs, mem, W: the call's): the journal grown by the callee's
   kc events, ARU and the heads at the callee's U', the callee-saved registers, every byte of cno_zone and every byte of
   a block live before and after outside the callee's own writes Kp kept, and the callee's facts P *)
Definition cno_ret (cx : cnocx) (k : Z) (ly : alayout) (S : astate) (regs : bvmap 5 word) (mem : word -> option byte)
  (W : world tfibsegs) (kc : Z) (U' : list (Z * Z)) (Kp : Z -> Prop)
  (P : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world tfibsegs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    cno_J cx (k + kc) ly' S' W' (unpoison U' mem') md' /\ ARU tfibsegs B ly' S' U' W' mem' md' /\
    FSupoisonU.fs_heads B ly' S' U' /\ aregs_preserved regs regs' /\
    (forall a, cno_zone cx a -> ~ Kp a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
    (forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
       ~ Kp (p + i) -> aview tfibsegs (w_H W') mem' (p + i) = aview tfibsegs (w_H W) mem (p + i)) /\
    P ly' S' W' regs' mem' md'.

(* the segment form (the entry walk's fe_from, FSW_entry_defs.v:133): from a machine at which the symbolic state ss
   holds under an env E whose extra atoms 32 .. 47 are cno_E's, with the journal, ARU and the segment's invariant INV,
   the run reaches check_no_overread_spec's post *)
Definition cno_E (cx : cnocx) (E : env) : Prop :=
  ew E 32 = Z_to_bv 64 SHADOW_OFF /\
  (forall j, (j < 13)%nat -> ew E (33 + j) = getr (c_regs cx) (nth j cno_saved_regs 0%bv)) /\
  ew E 46 = Z_to_bv 64 (cno_FL cx) /\ ew E 47 = Z_to_bv 64 (cno_SF cx).
Definition cno_inv : Type :=
  cnocx -> env -> Z -> alayout -> astate -> list (Z * Z) -> world tfibsegs -> machine_state -> Model -> Prop.
Definition cno_from (ss : sstate) (INV : cno_inv) : Prop :=
  forall (cx : cnocx) (E : env) (k : Z) ly3 S3 U3 (W3 : world tfibsegs) (ms3 : machine_state) md3,
  cno_base cx -> cno_E cx E ->
  cno_J cx k ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 -> ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  INV cx E k ly3 S3 U3 W3 ms3 md3 ->
  st_ok tfibsegs E ss (restrict (w_H W3) ms3) ->
  SRr tfibsegs W3 (mkCfg ms3 md3) (cno_post cx).

(* ---- past_nul (d, len, c) at 0x812f8 (c = 'A', ra 0x812fc) and 0x8130c (c = 'B', ra 0x81310): past_nul_spec
   (FSH_Fn_cno.v:69) at the walk's context; proved in this file (cno_call_pn) ---- *)
Definition cno_call_pn_T : Prop :=
  forall cx k ly S U (W : world tfibsegs) regs mem md c live peak cnt fail,
  cno_base cx -> cno_site cx k ly S U W regs mem md ->
  (getr regs 1 = w64 0x812fc \/ getr regs 1 = w64 0x81310) ->
  getr regs 10 = w64 (c_d cx) -> getr regs 11 = w64 (cno_n cx) -> getr regs 12 = w64 c -> 0 <= c < 2 ^ 64 ->
  src_rd tfibsegs W mem (c_d cx) (c_db cx) ->
  (0 < cno_n cx -> exists b m, In (b, m) (ablocks B ly S) /\ b <= c_d cx /\ c_d cx + cno_n cx <= b + m) ->
  fs_glob tfibsegs W mem live peak cnt fail -> quiet cnt fail 1 ->
  k + 1 <= EV_check_no_overread -> blocks_bytes S + (cno_n cx + 18) <= LIVE_MAX ->
  SRr tfibsegs W (cfg_at tfibsegs A_past_nul regs mem md)
    (fun W' c' => exists res,
       cno_ret cx k ly S regs mem W 1 U (fun _ => False)
         (fun ly' S' W' regs' mem' md' =>
            getr regs' 10 = w64 res /\ res <> 0 /\ res mod 16 = 0 /\
            ablocks B ly' S' = ablocks B ly S ++ [(res, cno_n cx + 18)] /\
            zbytes_at tfibsegs W' mem' res (pn_copy (c_db cx) c) /\
            fs_glob tfibsegs W' mem' live peak cnt fail) W' c').

(* ---- the call steps of a Theorem Labs lane (_mem.v cno_call_mal / cno_call_mcpy / cno_call_mset), its text verbatim (a Theorem Labs lane
   04:1xZ). __wrap_malloc (n + 18) at 0x8131c (ra 0x81320; `t <> 0` closes `beqz a0` 0x81320); __asan_memcpy (t, d, n)
   at 0x81338 (ra 0x8133c, only when n > 0); __asan_memset (t + n, 0, 17) at 0x81354 (ra 0x81358; the range_addressable
   over [t, t + n + 18) closes the inline check 0x81358-0x81364 -> 0x81550) ---- *)
Definition cno_call_mal_T : Prop :=
  forall cx k ly S U (W : world tfibsegs) regs mem md live peak cnt fail,
  cno_base cx -> cno_site cx k ly S U W regs mem md ->
  getr regs 1 = w64 0x81320 -> getr regs 10 = w64 (cno_n cx + 18) ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  k + 1 <= EV_check_no_overread -> blocks_bytes S + (cno_n cx + 18) <= LIVE_MAX ->
  SRr tfibsegs W (cfg_at tfibsegs PC_malloc regs mem md)
    (fun W' c' => exists t,
       cno_ret cx k ly S regs mem W 1 U (fun _ => False)
         (fun ly' S' W' regs' mem' md' =>
            getr regs' 10 = w64 t /\ t <> 0 /\
            ablocks B ly' S' = ablocks B ly S ++ [(t, cno_n cx + 18)] /\
            fs_glob tfibsegs W' mem' live peak cnt fail) W' c').

Definition cno_call_mcpy_T : Prop :=
  forall cx k ly S U (W : world tfibsegs) regs mem md t,
  cno_base cx -> cno_site cx k ly S U W regs mem md -> U = c_U cx ->
  getr regs 1 = w64 0x8133c ->
  getr regs 10 = w64 t -> getr regs 11 = w64 (c_d cx) -> getr regs 12 = w64 (cno_n cx) -> 0 < cno_n cx ->
  (exists l, ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ l ++ [(t, cno_n cx + 18)]) ->
  SRr tfibsegs W (cfg_at tfibsegs PC_memcpy regs mem md)
    (cno_ret cx k ly S regs mem W 0 U (fun a => t <= a < t + cno_n cx)
       (fun ly' S' W' regs' mem' md' =>
          ly' = ly /\ S' = S /\ W' = W /\ getr regs' 10 = w64 t /\
          zbytes_at tfibsegs W' mem' t (c_db cx) /\
          (forall a, 0 <= a < 2 ^ 64 -> ~ (t <= a < t + cno_n cx) -> ~ (cno_sp1 cx - ESTACK <= a < cno_sp1 cx) ->
             aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a))).

Definition cno_call_mset_T : Prop :=
  forall cx k ly S U (W : world tfibsegs) regs mem md t,
  cno_base cx -> cno_site cx k ly S U W regs mem md -> U = c_U cx ->
  getr regs 1 = w64 0x81358 ->
  getr regs 10 = w64 (t + cno_n cx) -> getr regs 11 = w64 0 -> getr regs 12 = w64 17 ->
  (exists l, ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ l ++ [(t, cno_n cx + 18)]) ->
  SRr tfibsegs W (cfg_at tfibsegs PC_memset regs mem md)
    (cno_ret cx k ly S regs mem W 0 U (fun a => t + cno_n cx <= a < t + cno_n cx + 17)
       (fun ly' S' W' regs' mem' md' =>
          ly' = ly /\ S' = S /\ W' = W /\ getr regs' 10 = w64 (t + cno_n cx) /\
          zbytes_at tfibsegs W' mem' (t + cno_n cx) (repeat 0 17%nat) /\
          (forall a, 0 <= a < 2 ^ 64 -> ~ (t + cno_n cx <= a < t + cno_n cx + 17) ->
             ~ (cno_sp1 cx - ESTACK <= a < cno_sp1 cx) -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
          range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF t (cno_n cx + 18))).

(* ---- the call step of a Theorem Labs lane (_dec.v cno_call_dec), its text verbatim (a Theorem Labs lane a188ffd7dd9, in this Section's form:
   B is a Section variable here), except the bad-text arm: `ablocks B ly' S' = ablocks B ly S` where decode_spec_ff
   (FSH_Fn_writer.v:614 on faa7e2570e5) still says Permutation; owner decision (a), a Theorem Labs lane 05:5xZ: the writer's arm is
   strengthened to the equality (one malloc that appends, one free of that same block), since check_no_overread_spec's
   post (FSH_Fn_cno.v:63) and INV_R need the exact list. preset_base64_decode (text, lenp) at 0x81398 / 0x813a8 /
   0x813b8 (ra 0x8139c / 0x813ac / 0x813bc, lenp the frame locals at 0x20 / 0x40 / 0x60); the refused arm is closed
   by quiet; cno_dec_strs carries the other texts across the call ---- *)
Definition cno_dec_strs (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs)
    (mem : word -> option byte) (W' : world tfibsegs) (mem' : word -> option byte) (U' : list (Z * Z)) : Prop :=
  forall p (l : list Z) b m, In (b, m) (ablocks B ly S) -> b <= p -> p + Z.of_nat (length l) + 8 <= b + m ->
    (forall r, In r U -> p + Z.of_nat (length l) + 1 <= fst r \/ fst r + snd r <= p) ->
    cstr_ok tfibsegs W mem p l ->
    cstr_ok tfibsegs W' mem' p l /\
    (forall r, In r U' -> p + Z.of_nat (length l) + 1 <= fst r \/ fst r + snd r <= p).

Definition cno_call_dec_T : Prop :=
  forall cx k ly S U (W : world tfibsegs) regs mem md text lenp v live peak cnt fail,
  cno_base cx -> cno_site cx k ly S U W regs mem md ->
  ((getr regs 1 = w64 0x8139c /\ lenp = cno_F cx + 32) \/ (getr regs 1 = w64 0x813ac /\ lenp = cno_F cx + 64) \/
   (getr regs 1 = w64 0x813bc /\ lenp = cno_F cx + 96)) ->
  getr regs 10 = w64 text -> getr regs 11 = w64 lenp ->
  cstr_ok tfibsegs W mem text (c_db cx) ->
  (exists b m, In (b, m) (ablocks B ly S) /\ b <= text /\ text + cno_n cx + 1 <= b + m /\
     forall r, In r U -> text + cno_n cx + 1 <= fst r \/ fst r + snd r <= text) ->
  (* decode_spec_ff's premise of a working branch 3f4c44b0426: *lenp's granule is addressable (its shadow
     byte is 00, written by the lifetime-start stores 0x81378 / 0x81380 / 0x81388 before the first decode) *)
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF lenp 8 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) lenp 8 v -> 0 <= v < 2 ^ 64 ->
  fs_glob tfibsegs W mem live peak cnt fail -> quiet cnt fail 1 ->
  live + FSH_Fn_writer.dec_size (c_db cx) < 2 ^ 64 ->
  k + FSH_Fn_writer.dec_ev (c_db cx) <= EV_check_no_overread ->
  blocks_bytes S + (FSH_Fn_writer.dec_size (c_db cx) + HEAD) <= LIVE_MAX ->
  SRr tfibsegs W (cfg_at tfibsegs A_preset_base64_decode regs mem md)
    (fun W' c' =>
       (WriterSpec.b64_dec (c_db cx) = None /\
        cno_ret cx k ly S regs mem W EV_preset_base64_decode U (fun a => lenp <= a < lenp + 8)
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly S /\
             val_mem tfibsegs (mrestrict (w_H W') mem') lenp 8 v /\
             fs_glob tfibsegs W' mem' live (Z.max peak (live + FSH_Fn_writer.dec_size (c_db cx))) (cnt + 1) fail /\
             cno_dec_strs ly S U W mem W' mem' U) W' c')
       \/
       (exists q out, WriterSpec.b64_dec (c_db cx) = Some out /\ q <> 0 /\
        cno_ret cx k ly S regs mem W 1 (U ++ [(q - HEAD, HEAD)]) (fun a => lenp <= a < lenp + 8)
          (fun ly' S' W' regs' mem' md' =>
             getr regs' 10 = w64 q /\ 4096 + HEAD <= q /\
             ablocks B ly' S' = ablocks B ly S ++ [(q - HEAD, FSH_Fn_writer.dec_size (c_db cx) + HEAD)] /\
             fs_rblock tfibsegs B ly' S' W' mem' q (FSH_Fn_writer.dec_size (c_db cx)) /\
             zbytes_at tfibsegs W' mem' q out /\
             val_mem tfibsegs (mrestrict (w_H W') mem') lenp 8 (Z.of_nat (length out)) /\
             fs_glob tfibsegs W' mem' (live + FSH_Fn_writer.dec_size (c_db cx))
               (Z.max peak (live + FSH_Fn_writer.dec_size (c_db cx))) (cnt + 1) fail /\
             cno_dec_strs ly S U W mem W' mem' (U ++ [(q - HEAD, HEAD)])) W' c')).

(* ---- the call steps of the tail (_tail.v cno_call_bcmp / cno_call_afree, _ffree.v cno_call_ffree, _ret.v
   cno_tail_ret). The freed blocks are the walk's own (not in the entry's ablocks: the kit's free step, FSW_malloc_free
   fsw_aj_freeU, and the journal composition need them in_tmp_block of the entry blocks; a Theorem Labs lane 04:4xZ) ---- *)
(* bcmp (x, y, n) at 0x813f8 (ra 0x813fc) or 0x81414 (ra 0x81418): two reader blocks holding the same n bytes compare
   equal, so a0 = 0 at the return and `bnez a0` (0x813fc / 0x81418) does not reach the abort block 0x81548; nothing
   but the runtime's stack below sp1 changes *)
Definition cno_call_bcmp_T : Prop :=
  forall cx k ly S U (W : world tfibsegs) regs mem md x y n mx my (l : list Z),
  cno_base cx -> cno_site cx k ly S U W regs mem md ->
  (getr regs 1 = w64 0x813fc \/ getr regs 1 = w64 0x81418) ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> n = Z.of_nat (length l) -> 0 < n ->
  fs_rblock tfibsegs B ly S W mem x mx -> fs_rblock tfibsegs B ly S W mem y my -> n <= mx -> n <= my ->
  zbytes_at tfibsegs W mem x l -> zbytes_at tfibsegs W mem y l ->
  SRr tfibsegs W (cfg_at tfibsegs PC_bcmp regs mem md)
    (cno_ret cx k ly S regs mem W 0 U (fun _ => False)
       (fun ly' S' W' regs' mem' md' =>
          ly' = ly /\ S' = S /\ W' = W /\ getr regs' 10 = w64 0 /\
          forall a, 0 <= a < 2 ^ 64 -> ~ (cno_sp1 cx - STK_RT_BCMP <= a < cno_sp1 cx) ->
            aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a)).

(* fuzz_free (p) at 0x81420 / 0x81428 / 0x81430 (ra 0x81424 / 0x8142c / 0x81434): fuzz_free_spec (FSH_Fn_alloc.v:131)
   at the walk's context; both arms (p = 0 after three refused decodes, else a reader block whose head is in U) *)
Definition cno_call_ffree_T : Prop :=
  forall cx k ly S U (W : world tfibsegs) regs mem md p n live peak cnt fail,
  cno_base cx -> cno_site cx k ly S U W regs mem md ->
  (getr regs 1 = w64 0x81424 \/ getr regs 1 = w64 0x8142c \/ getr regs 1 = w64 0x81434) ->
  getr regs 10 = w64 p ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  (p = 0 \/ (p <> 0 /\ (exists U1 U2, U = U1 ++ (p - HEAD, HEAD) :: U2) /\
     fs_rblock tfibsegs B ly S W mem p n /\ n <= live /\
     ~ In (p - HEAD, n + HEAD) (ablocks B (c_ly cx) (c_S cx)))) ->
  k + 1 <= EV_check_no_overread ->
  SRr tfibsegs W (cfg_at tfibsegs A_fuzz_free regs mem md)
    (fun W' c' =>
       (p = 0 /\
        cno_ret cx k ly S regs mem W 0 U (fun _ => False)
          (fun ly' S' W' regs' mem' md' =>
             ablocks B ly' S' = ablocks B ly S /\ fs_glob tfibsegs W' mem' live peak cnt fail) W' c')
       \/
       (p <> 0 /\ exists U1 U2, U = U1 ++ (p - HEAD, HEAD) :: U2 /\
        cno_ret cx k ly S regs mem W 1 (U1 ++ U2) (fun _ => False)
          (fun ly' S' W' regs' mem' md' =>
             (exists l1 l2, ablocks B ly S = l1 ++ (p - HEAD, n + HEAD) :: l2 /\ ablocks B ly' S' = l1 ++ l2) /\
             fs_glob tfibsegs W' mem' (live - n) peak cnt fail) W' c')).

(* __wrap_free (p) at 0x81438 / 0x81440 / 0x81448 (ra 0x8143c / 0x81444 / 0x8144c): afree_realizesU
   (FSupoisonU.v:211) on one of the walk's raw blocks (past_nul's two, the __wrap_malloc one), no range of U on it *)
Definition cno_call_afree_T : Prop :=
  forall cx k ly S U (W : world tfibsegs) regs mem md p m live peak cnt fail,
  cno_base cx -> cno_site cx k ly S U W regs mem md ->
  (getr regs 1 = w64 0x8143c \/ getr regs 1 = w64 0x81444 \/ getr regs 1 = w64 0x8144c) ->
  getr regs 10 = w64 p -> p <> 0 -> In (p, m) (ablocks B ly S) -> ~ In (p, m) (ablocks B (c_ly cx) (c_S cx)) ->
  (forall r, In r U -> fst r + snd r <= p \/ p + req_size m <= fst r) ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  k + 1 <= EV_check_no_overread ->
  SRr tfibsegs W (cfg_at tfibsegs PC_free regs mem md)
    (cno_ret cx k ly S regs mem W 1 U (fun _ => False)
       (fun ly' S' W' regs' mem' md' =>
          (exists l1 l2, ablocks B ly S = l1 ++ (p, m) :: l2 /\ ablocks B ly' S' = l1 ++ l2) /\
          fs_glob tfibsegs W' mem' live peak cnt fail)).

(* the epilogue from the return of the last __wrap_free (0x8144c): the locals' shadow, the frame's magic, the frame
   released through its flag word (0x81468-0x814bc; the real-stack arm 0x814c0-0x814fc is dead, the reloaded frame
   address is not 0), the saved registers reloaded and the ret (0x81500-0x8153c) into check_no_overread_spec's post.
   The state: cno_ss at 0x8144c with the frame's flag word at frame + 120 and the frame address in the slot
   sp1 + 0x10 (0x8133c). *)
Definition cno_cssl_R : list YP09.chunk := [YP09.mkChunk 16 (CVal 8 (SOff 19 0))].
Definition cno_ss_R : sstate := cno_ss 0x8144c 19 18 cno_flag_chunk cno_cssl_R.
Definition INV_R : cno_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  U3 = c_U cx /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\ k = EV_check_no_overread /\
  ew E 2 = w64 (cno_sp1 cx) /\ ew E 8 = w64 (cno_sp0 cx) /\ ew E 9 = w64 (cno_sp1 cx) /\
  ew E 18 = w64 (cno_SF cx) /\ ew E 19 = w64 (cno_F cx) /\
  ew E 3 = getr (c_regs cx) 3 /\ ew E 4 = getr (c_regs cx) 4 /\
  exists peak', c_peak cx <= peak' /\
    fs_glob tfibsegs W3 (ms_mem ms3) (c_live cx) peak' (c_cnt cx + 3) (c_fail cx).
Definition cno_tail_ret_T : Prop := cno_from cno_ss_R INV_R.
End I.

(* ================= the interface's generic facts, and the past_nul call step (cno_call_pn) ================= *)
Section P. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* the numbers of the context: sp0 16-aligned and in the stack, sp1 the re-aligned sp, room above sp0 *)
Lemma cno_nums : forall cx, cno_base B cx ->
  cno_sp0 cx mod 16 = 0 /\ alloc_ceiling + STK_check_no_overread <= cno_sp0 cx /\ cno_sp0 cx <= 2 ^ 47 /\
  cno_sp0 cx - 176 <= cno_sp1 cx <= cno_sp0 cx - 160 /\ cno_sp1 cx mod 32 = 0 /\
  cno_sp0 cx + 32 <= ly_top (c_ly cx) /\ ly_top (c_ly cx) <= 2 ^ 47.
Proof.
intros cx (HPRE & _ & _ & Htop & _).
pose proof HPRE as ((HAP & _ & _) & _).
pose proof HAP as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof asan_consts as (C1 & _). pose proof cno_stk as FS.
pose proof (fsw_realign_facts (cno_sp0 cx - 160) ltac:(unfold cno_sp0; lia)
  ltac:(unfold cno_sp0; rewrite Zminus_mod, Hal16; reflexivity)) as (F1 & F2 & F3).
unfold cno_sp1. unfold cno_sp0 in *. lia.
Qed.

(* an application byte reads the same through the unpoisoned memory (U's bytes are shadow bytes) *)
Lemma cno_aview_unp : forall ly S U (W : world tfibsegs) m md a, ARU tfibsegs B ly S U W m md ->
  0 <= a < 2 ^ 64 -> a < SHADOW_OFF \/ kHighMemBeg <= a ->
  aview tfibsegs (w_H W) (unpoison U m) a = aview tfibsegs (w_H W) m a.
Proof.
intros ly S U W m md a H Ha Happ. apply (aview_unpoison_out tfibsegs). rewrite (wz a Ha).
destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
destruct (ush_facts tfibsegs B ly S U W m md a H E) as (_ & L1 & L2). lia.
Qed.

(* a byte of a live block likewise *)
Lemma cno_blk_unp : forall ly S U (W : world tfibsegs) mem md p n i,
  ARU tfibsegs B ly S U W mem md -> In (p, n) (ablocks B ly S) -> 0 <= i < req_size n ->
  aview tfibsegs (w_H W) (unpoison U mem) (p + i) = aview tfibsegs (w_H W) mem (p + i).
Proof.
intros ly S U W mem md p n i HARU Hin Hi.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
destruct (fsw_ablock_low B ly S W (unpoison U mem) md p n HAR Hin) as (H1 & H2 & H3).
pose proof asan_consts as (C1 & _).
apply aview_at. apply (fsw_unpoison_app B ly S U W mem md (p + i) HARU); [lia|].
exact (fsw_ablock_off_shadow B ly S W (unpoison U mem) md p n HAR Hin (p + i) ltac:(lia)).
Qed.

(* a byte of cno_zone likewise: the stack is above kHighMemBeg, the frame and its shadow are no runtime bytes *)
Lemma cno_zone_unp : forall cx ly S U (W : world tfibsegs) mem md a,
  cno_base B cx -> ARU tfibsegs B ly S U W mem md -> In (1, c_fpos cx) (frames S) ->
  ly_F ly = ly_F (c_ly cx) -> cno_zone cx a ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros cx ly S U W mem md a Hb HARU Hin EF Hz.
pose proof (cno_nums cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cno_stk as FS.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
assert (EFa : frame_addr ly 1 (c_fpos cx) = cno_F cx) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) HAR Hin) as (H4096 & Hceil & Happ).
destruct (al_frames _ _ LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) HAR Hin) as (_ & _ & Hfp & Hsp).
change (fs_frame_bytes 1) with 128 in H4096, Hceil, Happ, Hfp. change (128 / 8) with 16 in Hsp.
rewrite EFa in H4096, Hceil, Happ, Hfp, Hsp.
pose proof (shadow_addr_bounds (cno_F cx) ltac:(lia)) as (Hs1 & Hs2).
unfold cno_zone, cno_SF in Hz. destruct Hz as [Hz | [Hz | [Hz | Hz]]].
- apply (fsw_aview_unpoison_high B ly S U W mem md a HARU). lia.
- apply (fsw_aview_unpoison_high B ly S U W mem md a HARU). lia.
- apply aview_at. apply (fsw_unpoison_notowned B ly S U W mem md a HARU); [lia | exact (proj2 (Hfp a Hz))].
- apply aview_at. apply (fsw_unpoison_notowned B ly S U W mem md a HARU); [lia|].
  assert (Hi : 0 <= a - shadow_addr (cno_F cx) < fs_frame_bytes 1 / 8) by (change (fs_frame_bytes 1 / 8) with 16; lia).
  pose proof (proj2 (Hsp (a - shadow_addr (cno_F cx)) Hi)) as Hno.
  replace (shadow_addr (cno_F cx) + (a - shadow_addr (cno_F cx))) with a in Hno by lia. exact Hno.
Qed.

(* the read-only data view at a call (fpreU's arodata): the entry's, kept by the journal's image clause *)
Lemma cno_pstat_bounds : forall a, inFP FS_PSTAT_FP a -> 0xa1000 <= a < 0x5fd000.
Proof.
intros a (r & Hr & H). unfold FS_PSTAT_FP in Hr.
repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in H; lia|]). destruct Hr.
Qed.
Lemma cno_ro_segs :
  forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0xa1000)) tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cno_relro : seg_covers FS_RLO (FS_RHI - FS_RLO) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cno_pstat_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof. apply sink_closed_pos. unfold FS_PSTAT_FP. repeat constructor; cbn; lia. Qed.
Lemma cno_arodata : forall cx k ly S U (W : world tfibsegs) mem md,
  cno_base B cx -> cno_J B cx k ly S W (unpoison U mem) md -> ARU tfibsegs B ly S U W mem md ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem).
Proof.
intros cx k ly S U W mem md Hb HJ HARU a Ha Ho He.
pose proof Hb as (HPRE & _). pose proof HPRE as (HAPU & Hro).
pose proof (fsw_ARU B _ _ _ _ _ _ _ _ _ HAPU) as HARU0.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hi : in_img tfibsegs a).
{ destruct Ha as [(sg & Hin & Hw & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] |].
  apply (seg_covers_img FS_RLO (FS_RHI - FS_RLO) a cno_relro). lia. }
assert (Hnp : ~ inFP FS_PSTAT_FP a).
{ intros Hp. pose proof (cno_pstat_bounds a Hp) as Hbd.
  destruct Ha as [(sg & Hin & Hw & Hr) | Hr]; [|unfold FS_RLO, FS_RHI in Hr; lia].
  pose proof (proj1 (forallb_forall _ _) cno_ro_segs sg Hin) as Hs. cbv beta in Hs. rewrite Hw in Hs.
  cbn [orb] in Hs. apply Z.leb_le in Hs. lia. }
pose proof (fs_segs_low a Hi) as Hlow.
rewrite <- (cno_aview_unp ly S U W mem md a HARU) by (unfold kLowMemEnd, SHADOW_OFF in *; lia).
rewrite (F3 a Hi Ho He Hnp (fp_spares_closed FS_PSTAT_FP a cno_pstat_closed)).
rewrite (cno_aview_unp _ _ _ _ _ _ a HARU0) by (unfold kLowMemEnd, SHADOW_OFF in *; lia).
exact (Hro a Ha Ho He).
Qed.

(* the callee's frame chain at a call: check_no_overread's record (sp0, entry ra, entry s0) on the entry's chain *)
Lemma cno_achain : forall cx k ly S U (W : world tfibsegs) mem md,
  cno_base B cx -> cno_J B cx k ly S W (unpoison U mem) md -> ARU tfibsegs B ly S U W mem md ->
  rdword (aview tfibsegs (w_H W) mem) (cno_sp0 cx - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview tfibsegs (w_H W) mem) (cno_sp0 cx - 16) = Some (s0Z (c_regs cx)) ->
  achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (cno_sp1 cx) (cno_sp0 cx)
    ((cno_sp0 cx, raZ (c_regs cx), s0Z (c_regs cx)) :: c_ch cx).
Proof.
intros cx k ly S U W mem md Hb HJ HARU H8 H16.
pose proof (cno_nums cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof Hb as (HPRE & _). pose proof HPRE as ((HAP & _ & _) & _).
pose proof HAP as (_ & _ & Hra4 & _ & _ & _ & _ & Hch & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cno_stk as FS.
assert (RW : forall q, rdword (aview tfibsegs (w_H W) mem) (cno_sp0 cx - q) =
  rdword (aview tfibsegs (w_H W) (unpoison U mem)) (cno_sp0 cx - q) \/ ~ (8 <= q <= 16)).
{ intros q. destruct (Z_le_dec 8 q) as [Hq1|Hq1]; [|right; lia]. destruct (Z_le_dec q 16) as [Hq2|Hq2]; [|right; lia].
  left. symmetry. apply rdword_ext. intros j Hj.
  apply (cno_aview_unp ly S U W mem md _ HARU); lia. }
apply (achain_ly_top (c_ly cx) ly _ _ _ _ Etop).
apply (cno_chain (c_ly cx) (aview tfibsegs (w_H (c_W cx)) (unpoison (c_U cx) (c_mem cx)))
  (aview tfibsegs (w_H W) (unpoison U mem)) (cno_sp0 cx) (s0Z (c_regs cx)) (c_ch cx) (raZ (c_regs cx)) (cno_sp1 cx)
  Hch).
- exact N6.
- lia.
- intros a Ha. apply F1; lia.
- destruct (RW 8) as [E | E]; [rewrite <- E; exact H8 | lia].
- destruct (RW 16) as [E | E]; [rewrite <- E; exact H16 | lia].
- exact Hra4.
- lia.
- clear - N1. Z.div_mod_to_equations. lia.
- lia.
Qed.

(* the callee's fpreU at a call of the walk (window top sp1, the callee's own STK1 within check_no_overread's) *)
Lemma cno_fpre : forall cx k ly S U (W : world tfibsegs) regs mem md STK1,
  cno_base B cx -> cno_site B cx k ly S U W regs mem md ->
  0 <= STK1 -> STK1 + (cno_sp0 cx - cno_sp1 cx) <= STK_check_no_overread ->
  fpreU tfibsegs B STK1 ly S U W regs mem md ((cno_sp0 cx, raZ (c_regs cx), s0Z (c_regs cx)) :: c_ch cx).
Proof.
intros cx k ly S U W regs mem md STK1 Hb (HJ & HARU & Hh & R2 & R8 & R3 & R4 & Hra & Hra4 & H8 & H16) HS1 HS2.
pose proof (cno_nums cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof Hb as (HPRE & _). pose proof HPRE as ((HAP & _ & _) & _).
pose proof HAP as (_ & _ & _ & Hgp & Htp & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cno_stk as FS.
assert (Esp : spZ regs = cno_sp1 cx) by (unfold spZ; rewrite R2; unfold w64; apply wz; lia).
assert (Es0 : s0Z regs = cno_sp0 cx) by (unfold s0Z; rewrite R8; unfold w64; apply wz; lia).
split; [split; [|exact (proj2 HARU)] | exact (cno_arodata cx k ly S U W mem md Hb HJ HARU)].
apply (afn_pre_at tfibsegs B STK_check_no_overread (cno_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
  (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(1, c_fpos cx)] ly S W (unpoison U mem) md k regs STK1
  (cno_sp1 cx - cno_sp0 cx) _ HJ).
- rewrite Esp. lia.
- clear - N1 N5. Z.div_mod_to_equations. lia.
- lia.
- exact HS1.
- lia.
- exact Hra.
- exact Hra4.
- rewrite R3. exact Hgp.
- rewrite R4. exact Htp.
- rewrite Esp, Es0. exact (cno_achain cx k ly S U W mem md Hb HJ HARU H8 H16).
Qed.

(* the return of a PROGRAM callee (its post an apost_baseU at window top sp1) as cno_ret: the journals composed
   (FSW_K3.fsw_ajournal_sub5), the zone kept by the callee journal's stack and frames clauses, the blocks by its
   block clause *)
Lemma cno_after_pcall : forall cx k ly S U (W : world tfibsegs) regs mem md STKc FP1 kc U' (Kp : Z -> Prop)
  (Q P : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  cno_base B cx -> cno_site B cx k ly S U W regs mem md ->
  0 <= STKc -> STKc + (cno_sp0 cx - cno_sp1 cx) <= STK_check_no_overread ->
  fsw_fp_sub B (c_ly cx) (c_S cx) ly S [(1, c_fpos cx)] FS_PSTAT_FP FP1 ->
  (forall a, inFP FP1 a -> cno_zone cx a -> Kp a) ->
  (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n -> inFP FP1 (p + i) -> Kp (p + i)) ->
  (forall ly' S' W' regs' mem' md', Q ly' S' W' regs' mem' md' ->
     FSupoisonU.fs_heads B ly' S' U' /\ P ly' S' W' regs' mem' md') ->
  apost_baseU tfibsegs B STKc FP1 regs ly S W mem md kc U U' Q W' c' ->
  cno_ret B cx k ly S regs mem W kc U' Kp P W' c'.
Proof.
intros cx k ly S U W regs mem md STKc FP1 kc U' Kp Q P W' c' Hb Hs HS1 HS2 Hfp HKz HKb HQ
  (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HQ').
pose proof Hs as (HJ & HARU & Hh & R2 & R8 & R3 & R4 & Hra & Hra4 & H8 & H16).
destruct (HQ _ _ _ _ _ _ HQ') as (Hh' & HP').
pose proof (cno_nums cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cno_stk as FS.
assert (Esp : spZ regs = cno_sp1 cx) by (unfold spZ; rewrite R2; unfold w64; apply wz; lia).
assert (HJ2 : cno_J B cx (k + kc) ly' S' W' (unpoison U' mem') md').
{ exact (fsw_ajournal_sub5 B STK_check_no_overread (cno_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(1, c_fpos cx)] ly S W (unpoison U mem) md k STKc (spZ regs) FP1 []
    ly' S' W' (unpoison U' mem') md' kc HJ HJc ltac:(lia) ltac:(lia) Hfp). }
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact (proj1 HJ2) | split; [exact OK' | exact PO']]).
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
pose proof HJ2 as (_ & Hly2 & _ & _ & _ & Hfrs2 & _).
assert (Hin : In (1, c_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (Hin2 : In (1, c_fpos cx) (frames S')) by (rewrite Hfrs2; left; reflexivity).
assert (EF : ly_F ly = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & E & _); exact E).
assert (EF2 : ly_F ly' = ly_F (c_ly cx)) by (destruct Hly2 as (_ & _ & _ & _ & _ & E & _); exact E).
assert (EFa : frame_addr ly 1 (c_fpos cx) = cno_F cx) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
exists ly', S', regs', mem', md'.
split; [rewrite Ec; unfold cfg_at, w64, raZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact HJ2|]. split; [exact HARU'|]. split; [exact Hh'|]. split; [exact HP|].
split; [|split; [|exact HP']].
- intros a Hz HnK.
  rewrite <- (cno_zone_unp cx ly' S' U' W' mem' md' a Hb HARU' Hin2 EF2 Hz).
  rewrite <- (cno_zone_unp cx ly S U W mem md a Hb HARU Hin EF Hz).
  assert (HnF : ~ inFP FP1 a) by (intros Hx; exact (HnK (HKz a Hx Hz))).
  pose proof (shadow_addr_bounds (cno_F cx)) as Hsb.
  unfold cno_zone, cno_SF in Hz. destruct Hz as [Hz | [Hz | [Hz | Hz]]].
  + apply G1; lia.
  + apply G1; lia.
  + apply (G4 1 (c_fpos cx) a Hin); [left | exact HnF].
    unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 1) with 128. lia.
  + apply (G4 1 (c_fpos cx) a Hin); [right | exact HnF].
    unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 1 / 8) with 16. lia.
- intros p n i Hp Hp' Hi HnK.
  rewrite <- (cno_blk_unp ly' S' U' W' mem' md' p n i HARU' Hp' Hi).
  rewrite <- (cno_blk_unp ly S U W mem md p n i HARU Hp Hi).
  apply (G2 p n i Hp Hp' Hi). intros Hx. exact (HnK (HKb p n i Hp Hi Hx)).
Qed.

(* ---- the past_nul call step ---- *)
Hypothesis PN : past_nul_spec tfibsegs B.

Lemma cno_call_pn : cno_call_pn_T B.
Proof.
intros cx k ly S U W regs mem md c live peak cnt fail Hb Hs Hra Ha0 Ha1 Ha2 Hc Hsrc Hblk Hg Hq Hk Hbb.
pose proof (cno_nums cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof cno_stk as FS. pose proof asan_consts as (C1 & _).
pose proof Hb as (HPRE & Hh0 & Hfr & Htop & Hd & Hn & Hsrc0 & Hnz & Hblk0 & Hmax & Hg0 & Hq0 & Hhd & Hnev
  & Hbb0).
pose proof Hs as (HJ & HARU & Hh & R2 & R8 & R3 & R4 & Hrok & Hra4 & H8 & H16).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnevj & _).
assert (HSp0 : 0 <= STK_past_nul) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSp1 : STK_past_nul + 176 <= STK_check_no_overread) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSp : STK_past_nul + (cno_sp0 cx - cno_sp1 cx) <= STK_check_no_overread) by lia.
eapply SRr_mono.
{ apply (PN ly S U W regs mem md ((cno_sp0 cx, raZ (c_regs cx), s0Z (c_regs cx)) :: c_ch cx) (c_d cx) (cno_n cx) c
    (c_db cx) live peak cnt fail).
  - exact (cno_fpre cx k ly S U W regs mem md STK_past_nul Hb Hs HSp0 HSp).
  - exact Hh.
  - exact Ha0.
  - exact Ha1.
  - exact Ha2.
  - exact Hc.
  - unfold cno_n in *. unfold PRESET_FILE_MAX_BYTES in Hmax. lia.
  - reflexivity.
  - exact Hsrc.
  - exact Hblk.
  - exact Hg.
  - exact Hq.
  - unfold EV_past_nul, EV_check_no_overread in *. lia.
  - exact Hbb.
  - unfold cno_n, PRESET_FILE_MAX_BYTES, MALLOC_MAX in *. lia. }
cbv beta. intros W' c' _ (res & HP).
exists res.
refine (cno_after_pcall cx k ly S U W regs mem md STK_past_nul [] 1 U (fun _ => False) _ _ W' c' Hb Hs HSp0 HSp
  _ _ _ _ HP).
- intros a (r & Hr & _). destruct Hr.
- intros a (r & Hr & _). destruct Hr.
- intros p n i _ _ (r & Hr & _). destruct Hr.
- intros ly' S' W'' regs' mem' md' (E10 & Hres & Hal & Hab & Hheads & Hz & Hg').
  split; [exact Hheads|]. split; [exact E10|]. split; [exact Hres|]. split; [exact Hal|]. split; [exact Hab|].
  split; [exact Hz | exact Hg'].
Qed.
End P.
