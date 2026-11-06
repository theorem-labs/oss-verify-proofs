(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YE05.v, with its module paths changed; 2671 of its 2756 lines of code are new or changed and 333 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segA.v; 712 of its 808 lines of code are new or changed and 2660 lines of the source are left out. *)
(* check_round_trip 0x81b9c (fuzz_state.c:278-314 with round_trip_document fs.c:229-264 inlined), fs.asan-ubsan (image
   tfibsegs = lib/B/YB1v.v, the pinned fuzz_state.asan-ubsan sha256
   5ac5ce0954f87e2d050c481b7b0599cfd55ef554eadc008e51491f44c053d204): the B twin of the ASan walk of lib/B/FSH_Fn_crt.v
   check_round_trip_spec, segment group D = segments 30-39 and the tail, from the return of pj_get_str at 0x823bc
   (0x823c0) to the final `ret` at 0x8261c, with the class-3 fake frame live (own = [(3, pos)]) until the epilogue's flag
   store releases it.
   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from ea635b4653a lib/A/FSH_crt_segD.v)
   rule 24: proves no function (kind: segment lemmas of check_round_trip's walk, PORTED from 1ab57ca7ad7) - the comment
   over crt_set_shadow_fixed corrected as on A (a working branch 1ab57ca7ad7); no statement changed.
   Port source: a working branch ea635b4653a proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segD.v (blob
   429b13fa2c3), CTX-free, itself PORTED from a working branch d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/
   Prog/ (the bespoke ASan proof of this function on fs.asan: stage cuts St20..St25, stdefs.v :521 .. :618, step proofs
   sd20.v .. sd25.v, sdglue.v's crt_keep_blk :612 / crt_spared_blk :659; checker a Theorem Labs lane CONFIRM 04:3xZ on
   (internal path)). Same Definition / Lemma names and statement shapes as the
   A file; every pc, return address, register and frame-slot fact RE-MEASURED on B (capstone over the pinned
   fs.asan-ubsan, (internal path)) and mapped from A by instruction meaning. The shared
   interface is lib/B/FSH_crt_base.v (a Theorem Labs lane); the kit steps are lib/B FSW_K.v / FSW_frame.v / FSW_rres.v / FSW_ret.v,
   used and not copied. A new file: no licence lines.

   A name -> A pc -> B pc (names keep their A form, content is B's):
     crt_ss30      0x82268 -> 0x823c0 (return of pj_get_str)     crt_ss31 / crt_ss31x 0x82274 -> 0x823cc (second decode)
     crt_ss31_bc   ra 0x82298 -> ra 0x823f4 (at PC_bcmp)           crt_ss32 0x82298 -> 0x823f4 (bcmp)
     crt_ss33      0x822a4 -> 0x82400 (fuzz_free got)             crt_ss34 0x822ac -> 0x82408 (fuzz_free file)
     crt_ss34_pf   ra 0x822b4 -> ra 0x82410 (at A_pj_free)         crt_ss35 0x822b4 -> 0x82410 (pj_free &back)
     crt_ss35_pf   ra 0x822bc -> ra 0x82418 (at A_pj_free)         crt_ss36 0x822bc -> 0x82418 (pj_free &doc)
     crt_ss36_ff   ra 0x8233c -> ra 0x8249c (at A_fuzz_free)       crt_ss37 0x8233c -> 0x8249c (fuzz_free back)
     crt_ss38      0x82344 -> 0x824a4 (fuzz_free text)            crt_ss39 0x8234c -> 0x824ac (free want)
     crt_ssT       0x82354 -> 0x824b4 (free same)                 crt_ssTx (B only) 0x824b4, s3 re-seated to F
     crt_ssT_sm    call 0x82378 / ra 0x8237c -> call 0x824d4 / ra 0x824d8 (at PC_set_shadow_f5)
     crt_ssF0      0x8237c -> 0x824d8                             crt_ssF1 / crt_ssF1s 0x82478 -> 0x825e0
     crt_ssE       ret 0x824b4 -> ret 0x8261c

   The eleven calls of this group (MEASURED on fs.asan-ubsan; return address in brackets):
     30  0x823c4..0x823c8  preset_base64_decode (bytes, &n)   [0x823cc]  R1 hold (see below); B reads &n from the s1
                            slot 0x28 (`ld a1, 0x28(s1)`), A from s11
     31  0x823cc..0x823f0  bcmp (got, bd, len)                [0x823f4]  guarded by `bne a0, s4` (n = |bs|) at 0x823dc
                            and skipped when |bs| = 0 (`beqz s4` 0x823e0 -> 0x823f8)
     32  0x823f4..0x823fc  fuzz_free (got)                    [0x82400]
     33  0x82400..0x82404  fuzz_free (file)                   [0x82408]
     34  0x82408..0x8240c  pj_free (&back), a0 from slot 0x20 [0x82410]
     35  0x82410..0x82414  pj_free (&doc), a0 from slot 0x38  [0x82418]
     36  0x82418..0x82498  `mv s4, s2` (text), then fuzz_free (back) after 29 shadow stores `sb s2, off(s10)`
                            (s2 = -8 = 0xf8)                   [0x8249c]
     37  0x8249c..0x824a0  fuzz_free (text), a0 = s4          [0x824a4]
     38  0x824a4..0x824a8  free (want) through __wrap_free     [0x824ac]
     39  0x824ac..0x824b0  free (same) through __wrap_free     [0x824b4]
     tail 0x824b4..0x824d4 __asan_set_shadow_f5 (SF, 64)       [0x824d8], then 0x824d8 `ld a0, 0x1f8(s3)` (s3 = F),
                            0x824dc `sb zero, 0(a0)`: the flag store that releases the frame, 0x824e0 `j 0x825e0`,
                            epilogue 0x825e0..0x82618 and `ret` 0x8261c.
   B's register allocation differs from A's in this group: SF lives in s10 (A: s3), F in s3 (A: s2 reloaded from slot
   0x10 at 0x82368), the magic word's frame address comes from slot 0x10 (A: 0x28), &back / &doc / &n from the s1 slots
   0x20 / 0x38 / 0x28 (A: s2 / s10 / s11). s3 = F is crt_INV_T's register conjunct on B (s3 is the encode loop's cursor
   0x81e0c .. 0x81fcc, so crt_E cannot carry it; 0x82098 `ld s3, 0x38(s1)` makes it F again).
   The U (user-poisoned heads) at each free, in order (fuzz_free disowns the block's own head before it frees;
   afree_realizesU asks every range of U to lie OUTSIDE the freed block, which the two `free` thunks need):
     0x823fc fuzz_free got  : U = crt_U30, drops (got - 16, 16)
     0x82404 fuzz_free file : U = crt_U31, drops (file - 16, 16)
     0x8240c pj_free &back  : U = crt_U32, drops the heads of back's tree blocks (rd_hblocks of its document)
     0x82414 pj_free &doc   : U = crt_U33, drops the heads of doc's tree blocks
     0x82498 fuzz_free back : U = crt_U34, drops (back - 16, 16)
     0x824a0 fuzz_free text : U = crt_U35, drops (text - 16, 16)
     0x824a8 free want      : U = crt_U36 = the entry's c_U; want is a plain malloc block (the malloc returning to
                              0x81da4, kept in slot 0x30), so it has no head in U and U is unchanged - the disjointness
                              premise is crt_free_disj below
     0x824b0 free same      : U = crt_U36, likewise (same is the malloc block returning to 0x81db8, kept in s8)
   so the walk reaches the epilogue at U = c_U cx, which is what the statement's U' = U asks.

   The trap arms this group must show unreachable: `__asan_handle_no_return` 0x824e4 and `abort` 0x824e8, reached only
   from the four `beqz a0` / `bne a0, s4` / `bnez a0` guards at 0x823c0, 0x823cc, 0x823dc, 0x823f4 (MEASURED: the
   branch-target scan over 0x81b9c..0x8266c finds no other edge into 0x824e4 from this group's range 0x823c0..0x8261c,
   and NO edge at all from this group into the UBSan trap 0x82620 or the `__asan_report_*` arms 0x82624..0x8266c, which
   are reached only from segments 5 and 7). The tail's `beqz s3, 0x824f0` (0x824c8, the real-stack unpoison arm) is
   decided false by F >= 4096 (crt_ret_facts' atom-47 fact, s3 re-seated to the frame atom in crt_ssTx). Each guard is
   discharged from the callee's success post: decode returns a non-NULL block with length n (crt_dec_nonnull), bcmp
   returns 0 on equal bytes.

   R1 hold: callee spec being restated in S0; this call's premises are re-checked when it lands (the decode call at
   0x823c8; a Theorem Labs lane's r1-keptbuf.md adds `wsrc_kept ly S W mem 0 text (tb ++ [0])` to decode_spec). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP03 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG05 YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
SetShadowDefU FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Base FSH_Rt FSPstat FSW_K FSW_rres FSW_ret FSW_frame FSW_frame3 FSW_crt_tbl
FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt FSH_crt_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YE2k.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= the group's boundary states (MEASURED: each is crt_ss_ret at the call's return address, with the
   global slot and frame chunk lists of FSH_crt_base.v; the tail adds the frame's magic word and the shadow byte the
   run writes) ================= *)
Definition crt_ss30 : sstate := crt_ss_ret 0x823c0 crt_cs1 crt_csF.   (* return of pj_get_str *)
Definition crt_ss31 : sstate := crt_ss_ret 0x823cc crt_cs1 crt_csF.   (* return of the second decode *)
Definition crt_ss32 : sstate := crt_ss_ret 0x823f4 crt_cs1 crt_csF.   (* return of bcmp *)
Definition crt_ss33 : sstate := crt_ss_ret 0x82400 crt_cs1 crt_csF.   (* return of fuzz_free (got) *)
Definition crt_ss34 : sstate := crt_ss_ret 0x82408 crt_cs1 crt_csF.   (* return of fuzz_free (file) *)
Definition crt_ss35 : sstate := crt_ss_ret 0x82410 crt_cs1 crt_csF.   (* return of pj_free (&back) *)
Definition crt_ss36 : sstate := crt_ss_ret 0x82418 crt_cs1 crt_csF.   (* return of pj_free (&doc) *)
Definition crt_ss37 : sstate := crt_ss_ret 0x8249c crt_cs1 crt_csF.   (* return of fuzz_free (back) *)
Definition crt_ss38 : sstate := crt_ss_ret 0x824a4 crt_cs1 crt_csF.   (* return of fuzz_free (text) *)
Definition crt_ss39 : sstate := crt_ss_ret 0x824ac crt_cs1 crt_csF.   (* return of free (want) *)
Definition crt_ssT : sstate := crt_ss_ret 0x824b4 crt_cs1 crt_csF.    (* return of free (same): the tail *)
(* B only: the tail reads s3 = F (`beqz s3` 0x824c8, `ld a0, 0x1f8(s3)` 0x824d8), which crt_INV_T states as
   ew E 19 = F; the run starts from crt_ssT with s3 re-seated to the frame atom 47, so the engine resolves the
   frame load into the frame region and decides the branch by atom 47's fact (A's s2 came from slot 0x10 instead) *)
Definition crt_ssTx : sstate :=
  mkSS (ss_pc crt_ssT) (sr_set (ss_regs crt_ssT) 19%bv (SOff 47 0)) (ss_mem crt_ssT) (ss_resv crt_ssT) (ss_facts crt_ssT).

(* the state at the __asan_set_shadow_f5 call (0x824d4), MEASURED by the engine from crt_ssTx over crt_tbl: eight
   instructions and the jal, the shadow byte at SF + 0x38 (`sb s2, 0x38(s10)`) and the retired magic 0x45e0360e at
   F + 0 (frame address from slot 0x10) written, a0 = SF (s10, atom 26), a1 = 64, ra = 0x824d8, s3 = F (atom 47), and
   the `beqz s3` at 0x824c8 decided false by crt_ret_facts' atom-47 fact (F >= 4096) *)
Definition crt_ssT_sm : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl 40%N PC_set_shadow_f5 crt_ssTx).
Lemma crt_tail_run_eq : sym_run_toN tfibsegs crt_tbl 40%N PC_set_shadow_f5 crt_ssTx = (crt_ssT_sm, RS_running).
Proof. vm_compute. reflexivity. Qed.
(* what that state holds at the call (read off the engine's answer) *)
Lemma crt_ssT_sm_regs :
  sr_get (ss_regs crt_ssT_sm) 10%bv = SOff 26 0 /\ sr_get (ss_regs crt_ssT_sm) 11%bv = SLit 64 /\
  sr_get (ss_regs crt_ssT_sm) 1%bv = SLit 0x824d8 /\ sr_get (ss_regs crt_ssT_sm) 19%bv = SOff 47 0 /\
  ss_pc crt_ssT_sm = PC_set_shadow_f5.
Proof. repeat split; vm_compute; reflexivity. Qed.
(* the run's own writes: the frame's first word (the retired magic) and one shadow byte of the frame *)
Lemma crt_ssT_sm_mem : map YP09.r_base (ss_mem crt_ssT_sm) = [Some 8%nat; Some 9%nat; Some 47%nat; Some 26%nat].
Proof. vm_compute. reflexivity. Qed.
Lemma crt_ssT_sm_pc : ss_pc crt_ssT_sm = PC_set_shadow_f5.
Proof. vm_compute. reflexivity. Qed.
Lemma crt_ssT_sm_resv : ss_resv crt_ssT_sm = None.
Proof. vm_compute. reflexivity. Qed.
(* the saved words (region 0) and the frame (region 2) at the call, read off the engine's answer: the frame region
   holds the retired magic at 0 and, still, the flag word at 504 *)
Lemma crt_ssT_sm_s0 : nth_error (ss_mem crt_ssT_sm) 0 = Some crt_s0_region.
Proof. vm_compute. reflexivity. Qed.
Lemma crt_ssT_sm_flag : nth_error (ss_mem crt_ssT_sm) 2 = Some (YP09.mkRegion (Some 47%nat) 0 (fs_frame_bytes 3) 0
  (fs_frame_bytes 3) [YP09.mkChunk 0 (CVal 8 (SLit 1172321806)); YP09.mkChunk (fs_frame_bytes 3 - 8) (CVal 8 (SOff 46 0))]).
Proof. vm_compute. reflexivity. Qed.

(* ================= pure facts the group's call sites need ================= *)
(* the group's guards: every `bnez a0` / `beqz a0` / `bne a0, s4` into 0x824e4 is decided by the callee's post, so
   __asan_handle_no_return 0x824e4 and abort 0x824e8 are not reached. These are the arithmetic halves. *)
Lemma crt_guard_nonzero : forall v : Z, 0 <= v < 2 ^ 64 -> v <> 0 -> Z_to_bv 64 v <> Z_to_bv 64 0.
Proof.
intros v H0 Hne E. apply Hne. apply (f_equal (@bv_unsigned 64)) in E.
rewrite !Z_to_bv_unsigned, !bv_wrap_small in E by (change (bv_modulus 64) with (2 ^ 64); lia). exact E.
Qed.
Lemma crt_guard_zero : forall v : Z, 0 <= v < 2 ^ 64 -> v = 0 -> Z_to_bv 64 v = Z_to_bv 64 0.
Proof. intros v H0 ->. reflexivity. Qed.
(* the two `free` thunks of segments 38 / 39 run at the entry's U, and `want` / `same` are plain malloc blocks, which
   carry no user-poisoned head: afree_realizesU's disjointness premise is then fs_heads' own separation *)
Lemma crt_free_disj : forall B ly S U p n,
  FSupoisonU.fs_heads B ly S U ->
  (forall r, In r U -> fst r + snd r <= p \/ p + req_size n <= fst r) ->
  forall r, In r U -> fst r + snd r <= p \/ p + req_size n <= fst r.
Proof. intros B ly S U p n _ H. exact H. Qed.
(* fs's allocator statics live in the image, so any step that keeps the image bytes keeps fs_stat (crcs_glob_img's
   range check, restated for this file) *)
Lemma crt_glob_img : forall a, (G_FAIL <= a < G_FAIL + 8 \/ G_LIVE <= a < G_LIVE + 8 \/ G_PEAK <= a < G_PEAK + 8 \/
  G_COUNT <= a < G_COUNT + 8) -> in_img tfibsegs a.
Proof.
intros a Ha.
assert (Hx : existsb (fun s => (Z.of_N (seg_base s) <=? 0xa1000) && (0x5fd000 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
  tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hx as (sg & Hin & Hc). apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hin|]. unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT in Ha. lia.
Qed.
(* the whole image of the pinned fs.asan-ubsan lies below 0x5fd000, the page end of its last RW segment (PT_LOAD
   0xa1920 + 0x55b3f0 = 0x5fcd10, reserved [0xa1000, 0x5fd000), lib/B/YB1h.v tfib_res_eq): below every stack slot
   (alloc_ceiling >= CEIL_MIN) and below the shadow band the frame's shadow lives in *)
Lemma crt_img_range : forall a, in_img tfibsegs a -> 0 <= a < 0x5fd000.
Proof.
intros a (sg & Hin & Hr).
assert (Hx : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x5fd000) tfibsegs = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in Hx. pose proof (Hx sg Hin) as Hs. apply Z.leb_le in Hs. lia.
Qed.
(* the walk's steps state their frames on the visible memory (a run's YP09.frame_of outside its write window, a runtime
   contract's aview clause); fs_stat reads its statics through the same view, so equal visible image bytes keep it *)
Lemma crt_img_frame : forall E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall a, in_img tfibsegs a -> ~ in_wrange E rs a) ->
  forall a, in_img tfibsegs a -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros E rs H m m' Hfr Hn a Ha. pose proof (crt_img_range a Ha) as Hr.
apply aview_eq_of. apply Hfr. rewrite (wz a ltac:(lia)). exact (Hn a Ha).
Qed.
Lemma crt_glob_keep : forall (W : world tfibsegs) (m m' : word -> option byte) live peak cnt fail,
  (forall a, in_img tfibsegs a -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail Hk (G1 & G2 & G3 & G4 & R).
assert (VB : forall g v, (G_FAIL <= g /\ g + 8 <= G_FAIL + 8 \/ G_LIVE <= g /\ g + 8 <= G_LIVE + 8 \/
    G_PEAK <= g /\ g + 8 <= G_PEAK + 8 \/ G_COUNT <= g /\ g + 8 <= G_COUNT + 8) ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W) m') g 8 v).
{ intros g v Hg Hv kk Hkk. assert (Hi : in_img tfibsegs (g + Z.of_nat kk)) by (apply crt_glob_img; lia).
  rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W) m m' _ (Hk _ Hi)). exact (Hv kk Hkk). }
unfold fs_glob, fs_glob_at in *.
split; [apply VB; [lia | exact G1]|]. split; [apply VB; [lia | exact G2]|].
split; [apply VB; [lia | exact G3]|]. split; [apply VB; [lia | exact G4]|]. exact R.
Qed.
Lemma crt_stat_keep : forall (W : world tfibsegs) (m m' : word -> option byte) live cnt,
  (forall a, in_img tfibsegs a -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  fs_stat tfibsegs W m live cnt -> fs_stat tfibsegs W m' live cnt.
Proof. intros W m m' live cnt Hk (peak & H). exists peak. exact (crt_glob_keep W m m' live peak cnt SIZE_MAXZ Hk H). Qed.
(* the flag address does not move along the walk either: ajournal's layout_le keeps ly_F (YG0f.layout_le) *)
Lemma crt_FL_ly : forall cx n ly3, layout_le n (c_ly cx) ly3 -> flag_addr ly3 3 (c_pos cx) = crt_FL cx.
Proof.
intros cx n ly3 Hle. unfold crt_FL, flag_addr.
destruct Hle as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.

(* ================= the walk ================= *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
(* the image facts of B (owner RELOC: TfibLib discharges them in the final instance; the same names and types as
   a Theorem Labs lane's lib/A/FSH_check_reject_clean_starved.v:297-300, with S0's single shadow-cell hypothesis) *)
Hypothesis HSS : FsShadowSyms B.
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.
Hypothesis HENV : api_env tfibsegs B.


(* ---- the tail's first run: the eight instructions 0x824b4..0x824d0 and the jal, i.e. the shadow byte
   `sb s2, 0x38(s10)` of the frame's last granule, the retired magic `sd a0, 0(a1)` into the frame (a1 from slot
   0x10), and the `beqz s3` that the atom-47 fact decides (F >= 4096, s3 re-seated in crt_ssTx), up to the
   __asan_set_shadow_f5 call ---- *)
Lemma crt_tail_run : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 (Q : world tfibsegs -> config -> Prop),
  crt_E cx E -> spZ (c_regs cx) mod 16 = 0 -> 192 <= spZ (c_regs cx) ->
  frame_addr ly3 3 (c_pos cx) = crt_F cx -> 0 <= crt_F cx < 2 ^ 64 ->
  st_ok tfibsegs E crt_ssTx (restrict (w_H W3) ms3) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  (forall ms mat,
     st_ok tfibsegs E crt_ssT_sm (restrict (w_H W3) ms) ->
     ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
       (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms))
       (with_vm_backing (m_vm_lazy md3) mat md3) k ->
     ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) ->
     frame_of E (ss_mem crt_ssT) (ms_mem ms3) (ms_mem ms) ->
     frame_of E (ss_mem crt_ssT) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
     SRr tfibsegs W3 (mkCfg ms (with_vm_backing (m_vm_lazy md3) mat md3)) Q) ->
  SRr tfibsegs W3 (mkCfg ms3 md3) Q.
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 Q HE H16 H0 HF HFr HS HJ HARU K.
fsw_aj_run_toU crt_tbl_ok HS HJ HARU PC_set_shadow_f5.
{ exact (crt_awr_ok B cx E ly3 S3 crt_cs1 crt_csF HE H16 H0 HF HFr). }
exact (K _ _ HS HJ HARU HF0 HFr0).
Qed.

(* ---- what the machine holds at the __asan_set_shadow_f5 call (0x824d4), read off crt_ssT_sm: a0 = SF (s10), a1 = 64,
   ra = 0x824d8, sp = the re-aligned sp, gp / tp the entry's ---- *)
Lemma crt_tail_sm_site : forall cx E (W3 : world tfibsegs) ms,
  crt_E cx E -> 0 <= crt_SF cx < 2 ^ 64 -> 0 <= crt_sp1 cx < 2 ^ 64 ->
  st_ok tfibsegs E crt_ssT_sm (restrict (w_H W3) ms) ->
  YK11.getr (ms_regs ms) 10%bv = w64 (crt_SF cx) /\ YK11.getr (ms_regs ms) 11%bv = w64 64 /\
  YK11.getr (ms_regs ms) 1%bv = w64 0x824d8 /\ spZ (ms_regs ms) = crt_sp1 cx /\
  YK11.getr (ms_regs ms) 3%bv = YK11.getr (c_regs cx) 3%bv /\
  YK11.getr (ms_regs ms) 4%bv = YK11.getr (c_regs cx) 4%bv.
Proof.
intros cx E W3 ms HE HSF Hsp1 HS.
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & Eex).
assert (R10 : bv_unsigned (YK11.getr (ms_regs ms) 10%bv) = crt_SF cx + 0)
  by (exact (fsw_reg_off (w_H W3) E crt_ssT_sm ms 10%bv 26 0 (crt_SF cx) HS
       ltac:(vm_compute; reflexivity) E26 ltac:(lia))).
assert (R2 : bv_unsigned (YK11.getr (ms_regs ms) 2%bv) = crt_sp1 cx + 0)
  by (exact (fsw_reg_off (w_H W3) E crt_ssT_sm ms 2%bv 2 0 (crt_sp1 cx) HS
       ltac:(vm_compute; reflexivity) E2 ltac:(lia))).
split.
{ apply bv_eq. rewrite R10, Z.add_0_r. unfold w64. symmetry. apply wz. lia. }
split.
{ exact (fsw_reg_lit (w_H W3) E crt_ssT_sm ms 11%bv 64 HS ltac:(vm_compute; reflexivity) ltac:(lia)). }
split.
{ exact (fsw_reg_lit (w_H W3) E crt_ssT_sm ms 1%bv 0x824d8 HS ltac:(vm_compute; reflexivity) ltac:(lia)). }
split.
{ unfold spZ. rewrite R2. lia. }
split.
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crt_ssT_sm ms 3%bv HS).
  change (sr_get (ss_regs crt_ssT_sm) 3%bv) with (SOff 3 0). rewrite fsw_SOff0. exact E3. }
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crt_ssT_sm ms 4%bv HS).
  change (sr_get (ss_regs crt_ssT_sm) 4%bv) with (SOff 4 0). rewrite fsw_SOff0. exact E4. }
Qed.

(* ---- the tail's runtime call: __asan_set_shadow_f5 (SF, 64) at 0x824d4. The contract this step consumes is S0's
   aset_shadow_realizesU with the presence clause that FSupoisonU's aintrin_realizesU also states (FSupoisonU.v:263):
   `forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a`. The clause cannot be derived from the aview clause,
   because `aview` reads image bytes through the image and YCbq.apresent_transfer (YCbq.v:693) therefore needs
   `~ in_img a`. S0 states the clause (SetShadowDefU.v:48, S0 5dbb8ce6286 "set_shadow contracts keep presence"), so
   crt_set_shadow_fixed below is S0's contract less one conjunct (the callee's stack window is present after the call,
   SetShadowDefU.v:47). FSH_crt_setsh.v's crt_setsh_of_rt derives SETSH from S0's contract (the chain passes
   RT_SETSH) by dropping that conjunct. ---- *)
Definition crt_set_shadow_fixed (pc v : Z) : Prop :=
  forall ly S U W regs mem md cid pos q n,
  FSupoison.ecall_preU tfibsegs B ly S U W regs mem md -> In (cid, pos) (frames S) ->
  YK11.getr regs 10%bv = w64 q -> YK11.getr regs 11%bv = w64 n -> 0 < n ->
  shadow_addr (frame_addr ly cid pos) <= q -> q + n <= shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
       ARU tfibsegs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       (forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem' (q + i) = Some v) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
          aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* ---- segment 36's run: 0x82418..0x82498, `mv s4, s2` (s4 := text, s2 held it since 0x821a0), `addi s2, zero, -8`
   at 0x8241c, the 29 `sb s2, off(s10)` stores that poison the frame's objects with 0xf8 (A's comment counted 31; the
   listings show 29 on both builds, 0x822c0..0x82330 on A, 0x82420..0x82490 on B), then `mv a0, s9` and the
   `jal fuzz_free` at 0x82498. The run has no branch and every store lands in the frame's shadow region (offsets
   4..0x34 of [SF, SF + 64), base s10 = atom 26), so crt_awr_ok covers its write window. MEASURED by the engine from
   crt_ss36 over crt_tbl. ---- *)
Definition crt_ss36_ff : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl 80%N A_fuzz_free crt_ss36).
Lemma crt_seg36_run_eq : sym_run_toN tfibsegs crt_tbl 80%N A_fuzz_free crt_ss36 = (crt_ss36_ff, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_ss36_ff_pc : ss_pc crt_ss36_ff = A_fuzz_free.
Proof. vm_compute. reflexivity. Qed.
(* at the call: a0 = s9 (the first decode's block, atom 25), ra = 0x8249c, sp unchanged *)
Lemma crt_ss36_ff_regs :
  sr_get (ss_regs crt_ss36_ff) 10%bv = SOff 25 0 /\ sr_get (ss_regs crt_ss36_ff) 1%bv = SLit 0x8249c /\
  sr_get (ss_regs crt_ss36_ff) 2%bv = SOff 2 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma crt_seg36_run : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 (Q : world tfibsegs -> config -> Prop),
  crt_E cx E -> spZ (c_regs cx) mod 16 = 0 -> 192 <= spZ (c_regs cx) ->
  frame_addr ly3 3 (c_pos cx) = crt_F cx -> 0 <= crt_F cx < 2 ^ 64 ->
  st_ok tfibsegs E crt_ss36 (restrict (w_H W3) ms3) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  (forall ms mat,
     st_ok tfibsegs E crt_ss36_ff (restrict (w_H W3) ms) ->
     ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
       (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms))
       (with_vm_backing (m_vm_lazy md3) mat md3) k ->
     ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) ->
     frame_of E (ss_mem crt_ss36) (ms_mem ms3) (ms_mem ms) ->
     frame_of E (ss_mem crt_ss36) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
     SRr tfibsegs W3 (mkCfg ms (with_vm_backing (m_vm_lazy md3) mat md3)) Q) ->
  SRr tfibsegs W3 (mkCfg ms3 md3) Q.
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 Q HE H16 H0 HF HFr HS HJ HARU K.
fsw_aj_run_toU crt_tbl_ok HS HJ HARU A_fuzz_free.
{ exact (crt_awr_ok B cx E ly3 S3 crt_cs1 crt_csF HE H16 H0 HF HFr). }
exact (K _ _ HS HJ HARU HF0 HFr0).
Qed.
End w.

(* ================= the frame release and the return ================= *)
(* the state at the return of __asan_set_shadow_f5 (0x824d8): the SMALLER resume state, not the whole crt_ss_ret. The
   release and the epilogue read only the saved words (atom 8), the frame's last word (the flag address, crt_csF) and
   the flag cell, so the state is the saved words, the frame [F, F + 512) with its flag chunk only, and a one-byte region
   at the flag atom 46, which is where the epilogue's `sb zero, 0(a0)` lands; s3 is re-seated to the frame atom (it holds
   F across the call: crt_ssTx seated it, and s3 is callee-saved). The s1 slots and the frame's shadow (which set_shadow
   has just rewritten) are not rebuilt. The flag cell is outside the frame - it is runtime-owned (AR_flag_law), no frame
   byte is (AR_frames_law) - so it is its own region. MEASURED by the engine (no extra atom fact is needed). *)
Definition crt_flag_region : YP09.region := YP09.mkRegion (Some 46%nat) 0 1 0 1 [].
Definition crt_rel_regions : list YP09.region := [crt_frame_region crt_csF; crt_flag_region].
Definition crt_ssF0 : sstate :=
  let X := fss_ret_s0_args 0x824d8 (-104) 0 crt_sv_chunks crt_rel_regions [] in
  mkSS (ss_pc X) (sr_set (ss_regs X) 19%bv (SOff 47 0)) (ss_mem X) (ss_resv X) (ss_facts X).
(* three instructions: `ld a0, 0x1f8(s3)` (the flag address from the frame's last word), `sb zero, 0(a0)` (the release)
   and `j 0x825e0`; MEASURED, the flag region (the third) ends holding the byte 0 *)
Definition crt_ssF1 : sstate := Eval vm_compute in fst (sym_runN tfibsegs crt_tbl 3%N crt_ssF0).
Lemma crt_flag_run_eq : sym_runN tfibsegs crt_tbl 3%N crt_ssF0 = (crt_ssF1, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_ssF1_pc : ss_pc crt_ssF1 = 0x825e0.
Proof. vm_compute. reflexivity. Qed.
Lemma crt_ssF1_flag : nth_error (ss_mem crt_ssF1) 2 =
  Some (YP09.mkRegion (Some 46%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]).
Proof. vm_compute. reflexivity. Qed.
(* after the release the frame is handed back (own = []), so neither its bytes nor the flag cell is in the walk's write
   window any more: the epilogue runs over the saved words alone (YP06.st_ok_submem drops the other two regions) *)
Definition crt_ssF1s : sstate :=
  mkSS (ss_pc crt_ssF1) (ss_regs crt_ssF1) [crt_s0_region] (ss_resv crt_ssF1) (ss_facts crt_ssF1).
Lemma crt_ssF1_mem : ss_mem crt_ssF1 = crt_s0_region :: tl (ss_mem crt_ssF1).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_ssF1_sub : submem [crt_s0_region] (ss_mem crt_ssF1).
Proof.
rewrite crt_ssF1_mem. apply submem_keep; [|apply submem_nil].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; split; lia|]. intros c Hc. exact Hc.
Qed.
(* the epilogue: `addi sp, s0, -0xc0`, the thirteen restores and `addi sp, sp, 0xc0` (0x825e0..0x82618), up to the
   `ret` at 0x8261c. MEASURED: at the `ret` every callee-saved register is back at its entry atom (ra = 33, s0 = 34,
   s1 = 35, s2..s11 = 36..45) and sp is the s0 atom, i.e. the entry sp *)
Definition crt_ssE : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl 40%N 0x8261c crt_ssF1s).
Lemma crt_epi_run_eq : sym_run_toN tfibsegs crt_tbl 40%N 0x8261c crt_ssF1s = (crt_ssE, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_ssE_shape : ss_pc crt_ssE = 0x8261c /\ ss_resv crt_ssE = None /\
  clookup crt_tbl (ss_pc crt_ssE) = Some RET_WORD_r /\
  map (fun r => sr_get (ss_regs crt_ssE) r) [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv =
  [SOff 33 0; SOff 8 0; SOff 34 0; SOff 35 0; SOff 36 0; SOff 37 0; SOff 38 0; SOff 39 0; SOff 40 0; SOff 41 0;
   SOff 42 0; SOff 43 0; SOff 44 0; SOff 45 0].
Proof. repeat split; vm_compute; reflexivity. Qed.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
(* the two runtime laws of the fake stack the kit's release step consumes (owner RUNTIME, a Theorem Labs lane: the lane's
   `astack_free_law` row; frame_flag_lawP is its flag twin). model_laws is NOT a hypothesis: it is derived from the
   walk's own AR below (YG05.model_laws_ok at AR's am_universe). *)
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.

(* ---- the epilogue's flag store, 0x824d8..0x824e0: the frame's last word gives the flag address, the store of 0
   releases the class-3 frame (own goes from [(3, pos)] to [], the state to stack_free_state), and the walk lands at
   the epilogue 0x825e0. FSW_frame's fsw_flag_storeU, at the walk's own state; the write window is crt_ssF0's three
   regions: the saved words (the stack arm), the frame (the own-frame arm) and the flag cell. The continuation also gets
   the run's frame on the visible memory (the image bytes of the post, crt_tail). ---- *)
Lemma crt_release : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms md (Q : world tfibsegs -> config -> Prop),
  crt_E cx E ->
  frame_addr ly3 3 (c_pos cx) = crt_F cx -> 0 <= crt_F cx < 2 ^ 64 ->
  flag_addr ly3 3 (c_pos cx) = crt_FL cx -> 0 <= crt_FL cx < 2 ^ 64 ->
  st_ok tfibsegs E crt_ssF0 (restrict (w_H W3) ms) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms)) md k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) md ->
  (forall ms' mat',
     st_ok tfibsegs E crt_ssF1 (restrict (w_H W3) ms') ->
     ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
       (unpoison (c_U cx) (c_mem cx)) (c_md cx) [] ly3 (stack_free_state 3 (c_pos cx) S3) W3
       (unpoison U3 (ms_mem ms')) (with_vm_backing (m_vm_lazy md) mat' md) k ->
     ARU tfibsegs B ly3 (stack_free_state 3 (c_pos cx) S3) U3 W3 (ms_mem ms')
       (with_vm_backing (m_vm_lazy md) mat' md) ->
     frame_of E (ss_mem crt_ssF0) (mrestrict (w_H W3) (ms_mem ms)) (mrestrict (w_H W3) (ms_mem ms')) ->
     SRr tfibsegs W3 (mkCfg ms' (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  SRr tfibsegs W3 (mkCfg ms md) Q.
Proof.
intros cx E k ly3 S3 U3 W3 ms md Q HE HF HFr HFL HFLr HS HJ HARU K.
pose proof HJ as (HAR & _).
pose proof (model_laws_ok (as_universe B) (am_universe _ _ _ _ (proj1 HAR))) as ML.
assert (HSTK : 17000 <= STK_check_round_trip) by (vm_compute; discriminate).
assert (E8 : bv_unsigned (ew E 8) = spZ (c_regs cx)) by (destruct HE as (_ & _ & _ & X & _); exact X).
assert (E46 : bv_unsigned (ew E 46) = crt_FL cx).
{ rewrite (crt_E_FL cx E HE), Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
  reflexivity. }
assert (E47 : bv_unsigned (ew E 47) = crt_F cx).
{ rewrite (crt_E_F cx E HE), Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
  reflexivity. }
eapply (fsw_flag_storeU B ML ASF FFL crt_tbl crt_tbl_ok W3 3%N E crt_ssF0 crt_ssF1 RS_running ms
  STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
  (unpoison (c_U cx) (c_mem cx)) (c_md cx) [] ly3 S3 U3 md k 3 (c_pos cx) Q
  HS crt_flag_run_eq I HJ HARU ltac:(lia)).
- (* the write window: the saved words, the frame, the flag cell *)
  intros a Ha. unfold crt_ssF0, fss_ret_s0_args, fss_ret_s0_regs, crt_rel_regions in Ha. cbn [ss_mem] in Ha.
  destruct Ha as (r & Hr & Har). cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]];
    unfold fs_ret_s0_region, crt_frame_region, crt_flag_region in Har;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Har.
  + left. left. left. rewrite E8 in Har. lia.
  + left. left. right. right. right. exists 3, (c_pos cx). split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite HF, crt_frame3. rewrite E47, crt_frame3 in Har. lia.
  + right. rewrite E46 in Har. rewrite HFL. lia.
- (* the released flag byte is 0 in every machine the end state describes *)
  intros msr HSr. rewrite HFL.
  pose proof (fsw_region_nth E crt_ssF1 msr 2 _ HSr crt_ssF1_flag) as HR.
  pose proof (fsw_field E (ms_mem msr) 46%nat (crt_FL cx) [YP09.mkChunk 0 (CVal 1 (SLit 0))] 0 1 0 1 0 1%N (SLit 0) 0
    HR E46 ltac:(left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
  pose proof (HV 0%nat ltac:(cbn; lia)) as Hb. cbn [Z.of_nat] in Hb.
  rewrite Z.add_0_r, Z.add_0_r in Hb. change (YO0f.le_byte 0 (N.to_nat 1) 0) with 0 in Hb. exact Hb.
- intros ms' mat' HS' HJ' HARU' _ HFr' _. exact (K ms' mat' HS' HJ' HARU' HFr').
Qed.
End r.


(* ================= segment 31: the guards after the second decode and the bcmp call ================= *)
(* the state at the return of the second decode (0x823cc), set up for the run: the n cell's chunk (decode wrote |bs|
   there: atom 20 = s4 = len), a0 = got nonzero (decode's success post) and |bs| >= 1 (the bcmp arm; |bs| = 0 skips
   bcmp, 0x823e0 `beqz s4`). B reads &n = F + 0x1a0 from the s1 slot 0x28 (`ld a0, 0x28(s1)` 0x823d4, crt_cs1's
   SOff 47 0x1a0), so - unlike A, which re-seats s11 to F + 0x1a0 - no register is re-seated. *)
Definition crt_csF31 : list YP09.chunk := YP09.mkChunk 0x1a0 (CVal 8 (SOff 20 0)) :: crt_csF.
Definition crt_ss31x : sstate :=
  let X := crt_ss_ret 0x823cc crt_cs1 crt_csF31 in
  mkSS (ss_pc X) (ss_regs X) (ss_mem X) (ss_resv X)
    (mkFacts ((10%nat, mkAF 4096 (2 ^ 47) 0) :: (20%nat, mkAF 1 (2 ^ 32) 0) :: f_atoms (ss_facts X)) [] []).
(* MEASURED: the engine decides `beqz a0` (0x823cc), `bne a0, s4` (0x823dc, n = len) and `beqz s4` (0x823e0) from
   those facts and reaches the bcmp thunk with a0 = got (atom 10), a1 = bd (atom 21), a2 = len (atom 20),
   ra = 0x823f4, s7 = got *)
Definition crt_ss31_bc : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl 40%N PC_bcmp crt_ss31x).
Lemma crt_seg31_run_eq : sym_run_toN tfibsegs crt_tbl 40%N PC_bcmp crt_ss31x = (crt_ss31_bc, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_ss31_bc_regs :
  ss_pc crt_ss31_bc = PC_bcmp /\
  map (fun r => sr_get (ss_regs crt_ss31_bc) r) [1; 10; 11; 12; 23]%bv =
  [SLit 0x823f4; SOff 10 0; SOff 21 0; SOff 20 0; SOff 10 0].
Proof. split; vm_compute; reflexivity. Qed.


Section s31. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
(* segment 31's run as a walk step over the journal and ARU (FSW_K fsw_aj_run_toU); the write window is the boundary
   state's own (crt_awr_ok), since the run writes nothing *)
Lemma crt_seg31_run : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 (Q : world tfibsegs -> config -> Prop),
  crt_E cx E -> spZ (c_regs cx) mod 16 = 0 -> 192 <= spZ (c_regs cx) ->
  frame_addr ly3 3 (c_pos cx) = crt_F cx -> 0 <= crt_F cx < 2 ^ 64 ->
  st_ok tfibsegs E crt_ss31x (restrict (w_H W3) ms3) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  (forall ms mat,
     st_ok tfibsegs E crt_ss31_bc (restrict (w_H W3) ms) ->
     ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
       (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms))
       (with_vm_backing (m_vm_lazy md3) mat md3) k ->
     ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) ->
     frame_of E (ss_mem crt_ss31x) (ms_mem ms3) (ms_mem ms) ->
     frame_of E (ss_mem crt_ss31x) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
     SRr tfibsegs W3 (mkCfg ms (with_vm_backing (m_vm_lazy md3) mat md3)) Q) ->
  SRr tfibsegs W3 (mkCfg ms3 md3) Q.
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 Q HE H16 H0 HF HFr HS HJ HARU K.
fsw_aj_run_toU crt_tbl_ok HS HJ HARU PC_bcmp.
{ exact (crt_awr_ok B cx E ly3 S3 crt_cs1 crt_csF31 HE H16 H0 HF HFr). }
exact (K _ _ HS HJ HARU HF0 HFr0).
Qed.
End s31.

Section s31c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
(* segment 31's bcmp call: the base's crt_bcmp_call at the engine's state crt_ss31_bc (a0 = got at atom 10, return
   to 0x823f4) *)
Definition crt_seg31_bcmp := crt_bcmp_call B crt_ss31_bc 0x823f4 10%nat.
Lemma crt_ss31_bc_call_regs :
  sr_get (ss_regs crt_ss31_bc) 1%bv = SLit 0x823f4 /\ sr_get (ss_regs crt_ss31_bc) 10%bv = SOff 10 0 /\
  sr_get (ss_regs crt_ss31_bc) 11%bv = SOff 21 0 /\ sr_get (ss_regs crt_ss31_bc) 12%bv = SOff 20 0 /\
  sr_get (ss_regs crt_ss31_bc) 2%bv = SOff 2 0 /\ sr_get (ss_regs crt_ss31_bc) 3%bv = SOff 3 0 /\
  sr_get (ss_regs crt_ss31_bc) 4%bv = SOff 4 0 /\ YK0s.ret_ok (Z_to_bv 64 0x823f4).
Proof. repeat split; vm_compute; reflexivity. Qed.
End s31c.


Section ssh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
(* ---- the tail's runtime call __asan_set_shadow_f5 (SF, 64) at 0x824d4, against the FIXED contract SETSH (the one
   premise of this lemma, see crt_set_shadow_fixed): the registers (crt_tail_sm_site), ecall_preU
   (fsw_ecall_preU_at), the contract at the frame's whole shadow range, and the journal put back over the call
   (fsw_intrin_atU; write set = the frame's 64 shadow granules, awr_byte's own-frame arm, and the callee's ESTACK
   window, its stack arm). The continuation also gets the contract's frame clause on the raw memory, from which the
   resume state after the call (crt_resume_F0) and the image bytes of the post (crt_tail) are read. ---- *)
Lemma crt_tail_sm : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) regsT memT mdT (Q : world tfibsegs -> config -> Prop),
  crt_set_shadow_fixed B PC_set_shadow_f5 0xf5 ->
  crt_E cx E -> spZ (c_regs cx) mod 16 = 0 -> 192 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  0 <= crt_SF cx < 2 ^ 64 ->
  YK11.getr (c_regs cx) 3%bv = w64 (as_gp B) -> YK11.getr (c_regs cx) 4%bv = w64 (as_tp B) ->
  In (3, c_pos cx) (frames S3) -> frame_addr ly3 3 (c_pos cx) = crt_F cx ->
  st_ok tfibsegs E crt_ssT_sm (restrict (w_H W3) (mkst regsT (Z_to_bv 64 PC_set_shadow_f5) memT (seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 memT) mdT k ->
  ARU tfibsegs B ly3 S3 U3 W3 memT mdT ->
  (forall regs2 mem2 md2,
     ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
       (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 mem2) md2 k ->
     ARU tfibsegs B ly3 S3 U3 W3 mem2 md2 ->
     aregs_preserved regsT regs2 ->
     (forall i, 0 <= i < 64 -> aview tfibsegs (w_H W3) mem2 (crt_SF cx + i) = Some 0xf5) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (crt_SF cx <= a < crt_SF cx + 64) -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
        aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) memT a) ->
     SRr tfibsegs W3 (mkCfg (mkst regs2 (YK11.getr regsT 1%bv) mem2 (seg_rom tfibsegs)) md2) Q) ->
  SRr tfibsegs W3 (mkCfg (mkst regsT (Z_to_bv 64 PC_set_shadow_f5) memT (seg_rom tfibsegs)) mdT) Q.
Proof.
intros cx E k ly3 S3 U3 W3 regsT memT mdT Q SETSH HE H16 H0 H47 HSF Hgp Htp Hin HF HS HJ HARU K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (crt_sp1_facts cx H16 H0) as (Hsp1b & Hsp1_32 & Hsp1_16).
assert (Hsp1r : 0 <= crt_sp1 cx < 2 ^ 64) by lia.
destruct (crt_tail_sm_site cx E W3 (mkst regsT (Z_to_bv 64 PC_set_shadow_f5) memT (seg_rom tfibsegs)) HE HSF Hsp1r HS)
  as (G10 & G11 & G1 & GSP & G3 & G4).
cbn [ms_regs mkst] in G10, G11, G1, GSP, G3, G4.
assert (HSTK : 17000 <= STK_check_round_trip) by (vm_compute; discriminate).
assert (Hra : YK0s.ret_ok (YK11.getr regsT 1%bv)) by (rewrite G1; vm_compute; reflexivity).
assert (HPRE : FSupoison.ecall_preU tfibsegs B ly3 S3 U3 W3 regsT memT mdT).
{ eapply (fsw_ecall_preU_at B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 W3 memT mdT k regsT
    (crt_sp1 cx - spZ (c_regs cx)) HJ HARU);
  [lia | rewrite Zminus_mod, H16, Hsp1_16; reflexivity | lia | unfold ESTACK; lia | exact Hra
  | rewrite G3; exact Hgp | rewrite G4; exact Htp]. }
pose proof (SETSH ly3 S3 U3 W3 regsT memT mdT 3 (c_pos cx) (crt_SF cx) 64 HPRE Hin G10 G11 ltac:(lia)
  ltac:(rewrite HF; unfold crt_SF; lia) ltac:(rewrite HF, crt_frame3; unfold crt_SF; cbn; lia)) as HC.
change (cfg_at tfibsegs PC_set_shadow_f5 regsT memT mdT) with
  (mkCfg (mkst regsT (Z_to_bv 64 PC_set_shadow_f5) memT (seg_rom tfibsegs)) mdT) in HC.
eapply SRr_bind.
{ eapply (fsw_intrin_atU B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 W3 memT mdT k U3
    (fun a => (crt_SF cx <= a < crt_SF cx + 64) \/ (spZ regsT - ESTACK <= a < spZ regsT)) (YK11.getr regsT 1%bv) _
    (fun regs' mem' md' => aregs_preserved regsT regs' /\
       (forall i, 0 <= i < 64 -> aview tfibsegs (w_H W3) mem' (crt_SF cx + i) = Some 0xf5) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (crt_SF cx <= a < crt_SF cx + 64) -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
          aview tfibsegs (w_H W3) mem' a = aview tfibsegs (w_H W3) memT a)) HJ).
  - eapply SRr_mono; [exact HC|].
    intros W' c' _ (-> & regs' & mem' & md' & Ec & HARU' & HP & Hsame & Hv & Hfr & Hgr).
    split; [reflexivity|]. exists regs', mem', md'.
    split; [rewrite Ec; unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
    split; [exact HARU'|]. split; [exact Hsame|].
    split.
    { apply (crt_unpoison_keep (w_H W3) U3 memT mem'). intros a Ha Hw. apply Hfr; [exact Ha | |]; intros X; apply Hw;
      [left | right]; exact X. }
    split; [exact (crt_unpoison_present (w_H W3) U3 memT mem' Hgr)|].
    split; [exact HP | split; [exact Hv | exact Hfr]].
  - intros a [Ha | Ha].
    + left. right. right. right. exists 3, (c_pos cx). split; [left; reflexivity|]. right.
      unfold in_zr, crt_SF in *. cbn [fst snd]. rewrite HF, crt_frame3. cbn. lia.
    + left. left. rewrite GSP in Ha. unfold ESTACK in Ha. lia. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & Hv2 & Hfr2).
exact (K regs2 mem2 md2 HJ2 HARU2 HP2 Hv2 Hfr2).
Qed.
End ssh.


Section ret. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
(* ---- the final `ret` at 0x8261c (FSW_ret's fsw_retU at crt_ssE): every callee-saved register is back at its entry
   atom (crt_ssE_shape), so aregs_preserved holds against the entry registers (crt_E's saved atoms 33..45, gp / tp,
   and sp = the s0 atom = sp0), ra jumps back to the entry ra (afn_pre's ret_ok), and the journal - own = [] after the
   release, U back at c_U - is the statement's post at its budget EV_check_round_trip. The two facts the composition
   brings are premises: the journal's k is within the budget (it is, once WRITER / READER restate their fixed terms
   by trace - a Theorem Labs lane), and the statement's Q at the final memory (the boundary invariant's blocks / count /
   image facts carried through the tail). ---- *)
Ltac crt_saved_reg HE :=
  first [ rewrite (crt_E_saved _ _ 1 HE ltac:(lia)); reflexivity | rewrite (crt_E_saved _ _ 2 HE ltac:(lia)); reflexivity
        | rewrite (crt_E_saved _ _ 3 HE ltac:(lia)); reflexivity | rewrite (crt_E_saved _ _ 4 HE ltac:(lia)); reflexivity
        | rewrite (crt_E_saved _ _ 5 HE ltac:(lia)); reflexivity | rewrite (crt_E_saved _ _ 6 HE ltac:(lia)); reflexivity
        | rewrite (crt_E_saved _ _ 7 HE ltac:(lia)); reflexivity | rewrite (crt_E_saved _ _ 8 HE ltac:(lia)); reflexivity
        | rewrite (crt_E_saved _ _ 9 HE ltac:(lia)); reflexivity | rewrite (crt_E_saved _ _ 10 HE ltac:(lia)); reflexivity
        | rewrite (crt_E_saved _ _ 11 HE ltac:(lia)); reflexivity | rewrite (crt_E_saved _ _ 12 HE ltac:(lia)); reflexivity ].
Lemma crt_ret : forall cx E k ly3 S3 (W3 : world tfibsegs) msf mdf,
  crt_base B cx -> crt_E cx E ->
  st_ok tfibsegs E crt_ssE (restrict (w_H W3) msf) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [] ly3 S3 W3 (unpoison (c_U cx) (ms_mem msf)) mdf k ->
  ARU tfibsegs B ly3 S3 (c_U cx) W3 (ms_mem msf) mdf ->
  k <= EV_check_round_trip ->
  (forall mat, crt_Q B cx ly3 S3 W3 (ms_regs msf) (ms_mem msf) (with_vm_backing (m_vm_lazy mdf) mat mdf)) ->
  SRr tfibsegs W3 (mkCfg msf mdf) (crt_post SK B cx).
Proof.
intros cx E k ly3 S3 W3 msf mdf HB HE HS HJ HARU Hk HQ.
destruct (crt_ssE_shape) as (Hpc & Hrv & Hlk & _).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & Eex).
(* the entry's afn_pre: ra is a return address *)
destruct HB as (HP0 & _). destruct HP0 as ((HAP & _) & _). destruct HAP as (_ & Hret & _).
assert (Rd : forall (q : bv 5) n, sr_get (ss_regs crt_ssE) q = SOff n 0 -> YK11.getr (ms_regs msf) q = ew E n).
{ intros q n Hq. rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crt_ssE msf q HS), Hq. apply fsw_SOff0. }
unfold crt_post, apost_baseU.
apply (fsw_retU B crt_tbl crt_tbl_ok W3 E crt_ssE msf mdf STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_regs cx)
  (c_ly cx) (c_S cx) (c_U cx) (c_W cx) (c_mem cx) (c_md cx) ly3 S3 (c_U cx) EV_check_round_trip (crt_Q B cx) HS Hrv Hlk).
- (* ra: the saved entry ra (atom 33) *)
  rewrite (Rd 1%bv 33%nat ltac:(vm_compute; reflexivity)).
  change 33%nat with (33 + 0)%nat. rewrite (crt_E_saved cx E 0 HE ltac:(lia)). cbn [nth crt_saved]. exact Hret.
- exact (ajournal_mono_k tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hk).
- exact HARU.
- (* the callee-saved registers *)
  apply (fsw_preserved (w_H W3) E crt_ssE msf (c_regs cx) (fun r => sr_get (ss_regs crt_ssE) r) HS).
  + vm_compute. reflexivity.
  + intros r Hr. cbv [CALLEE_SAVED In] in Hr.
    repeat (destruct Hr as [<-|Hr];
      [ lazymatch goal with |- sv_denot E ?x = _ => let y := eval vm_compute in x in change x with y end;
        rewrite fsw_SOff0;
        first [ apply bv_eq; rewrite E8; reflexivity | exact E3 | exact E4
              | lazymatch goal with |- ew E ?n = _ =>
                  let m := eval compute in (n - 33)%nat in change n with (33 + m)%nat end; crt_saved_reg HE ] |]).
    destruct Hr.
- exact HQ.
Qed.
End ret.


(* ================= segments 34 / 35: the two pj_free calls ================= *)
(* MEASURED by the engine: from the return of fuzz_free (file) at 0x82408, `ld a0, 0x20(s1)` and `jal pj_free` reach
   A_pj_free with a0 = &back = F + 0x140 (crt_cs1's slot 0x20, SOff 47 0x140; A: s2) and ra = 0x82410; from the return
   of the first pj_free at 0x82410, `ld a0, 0x38(s1)` and `jal pj_free` reach it with a0 = &doc = F + 0x20 (slot 0x38,
   SOff 47 0x20; A: s10) and ra = 0x82418 *)
Definition crt_ss34_pf : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl 8%N A_pj_free crt_ss34).
Lemma crt_seg34_run_eq : sym_run_toN tfibsegs crt_tbl 8%N A_pj_free crt_ss34 = (crt_ss34_pf, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_ss34_pf_regs : ss_pc crt_ss34_pf = A_pj_free /\
  sr_get (ss_regs crt_ss34_pf) 10%bv = SOff 47 0x140 /\ sr_get (ss_regs crt_ss34_pf) 1%bv = SLit 0x82410.
Proof. repeat split; vm_compute; reflexivity. Qed.
Definition crt_ss35_pf : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl 8%N A_pj_free crt_ss35).
Lemma crt_seg35_run_eq : sym_run_toN tfibsegs crt_tbl 8%N A_pj_free crt_ss35 = (crt_ss35_pf, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_ss35_pf_regs : ss_pc crt_ss35_pf = A_pj_free /\
  sr_get (ss_regs crt_ss35_pf) 10%bv = SOff 47 0x20 /\ sr_get (ss_regs crt_ss35_pf) 1%bv = SLit 0x82418.
Proof. repeat split; vm_compute; reflexivity. Qed.

Section s3435. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
(* the two runs as walk steps (they write nothing: crt_awr_ok covers the window) *)
Lemma crt_seg34_run : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 (Q : world tfibsegs -> config -> Prop),
  crt_E cx E -> spZ (c_regs cx) mod 16 = 0 -> 192 <= spZ (c_regs cx) ->
  frame_addr ly3 3 (c_pos cx) = crt_F cx -> 0 <= crt_F cx < 2 ^ 64 ->
  st_ok tfibsegs E crt_ss34 (restrict (w_H W3) ms3) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  (forall ms mat,
     st_ok tfibsegs E crt_ss34_pf (restrict (w_H W3) ms) ->
     ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
       (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms))
       (with_vm_backing (m_vm_lazy md3) mat md3) k ->
     ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) ->
     frame_of E (ss_mem crt_ss34) (ms_mem ms3) (ms_mem ms) ->
     frame_of E (ss_mem crt_ss34) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
     SRr tfibsegs W3 (mkCfg ms (with_vm_backing (m_vm_lazy md3) mat md3)) Q) ->
  SRr tfibsegs W3 (mkCfg ms3 md3) Q.
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 Q HE H16 H0 HF HFr HS HJ HARU K.
fsw_aj_run_toU crt_tbl_ok HS HJ HARU A_pj_free.
{ exact (crt_awr_ok B cx E ly3 S3 crt_cs1 crt_csF HE H16 H0 HF HFr). }
exact (K _ _ HS HJ HARU HF0 HFr0).
Qed.
Lemma crt_seg35_run : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 (Q : world tfibsegs -> config -> Prop),
  crt_E cx E -> spZ (c_regs cx) mod 16 = 0 -> 192 <= spZ (c_regs cx) ->
  frame_addr ly3 3 (c_pos cx) = crt_F cx -> 0 <= crt_F cx < 2 ^ 64 ->
  st_ok tfibsegs E crt_ss35 (restrict (w_H W3) ms3) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  (forall ms mat,
     st_ok tfibsegs E crt_ss35_pf (restrict (w_H W3) ms) ->
     ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
       (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms))
       (with_vm_backing (m_vm_lazy md3) mat md3) k ->
     ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) ->
     frame_of E (ss_mem crt_ss35) (ms_mem ms3) (ms_mem ms) ->
     frame_of E (ss_mem crt_ss35) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
     SRr tfibsegs W3 (mkCfg ms (with_vm_backing (m_vm_lazy md3) mat md3)) Q) ->
  SRr tfibsegs W3 (mkCfg ms3 md3) Q.
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 Q HE H16 H0 HF HFr HS HJ HARU K.
fsw_aj_run_toU crt_tbl_ok HS HJ HARU A_pj_free.
{ exact (crt_awr_ok B cx E ly3 S3 crt_cs1 crt_csF HE H16 H0 HF HFr). }
exact (K _ _ HS HJ HARU HF0 HFr0).
Qed.
End s3435.


(* ================= the tail composed: from the return of free (same) (0x824b4) to the final `ret` =================
   crt_tail_run (to the set_shadow call), crt_tail_sm (the call, against SETSH), crt_resume_F0 (the smaller resume
   state), crt_release (the flag store), YP06.st_ok_submem (drop the handed-back frame and the flag cell), the epilogue
   run, crt_ret. The statement's Q rides along from crt_INV_T: the blocks are untouched (the release changes only the
   fake-stack state, stack_free_state), and no step writes an image byte - every step's frame is on the visible memory,
   and the image lies below every stack slot and shadow byte (crt_img_range) and outside every live frame
   (YCbq.frm_img) and the flag cell (frame_flag_lawP) - so fs_stat and rom_view carry over (crt_Q_keep). *)
Section tail. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis SETSH : crt_set_shadow_fixed B PC_set_shadow_f5 0xf5.

(* the statement's Q survives a step that keeps the blocks and the visible image bytes *)
Lemma crt_Q_keep : forall cx ly S S' (W : world tfibsegs) regs regs' (m m' : word -> option byte) md md',
  ablocks B ly S' = ablocks B ly S ->
  (forall a, in_img tfibsegs a -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  crt_Q B cx ly S W regs m md -> crt_Q B cx ly S' W regs' m' md'.
Proof.
intros cx ly S S' W regs regs' m m' md md' Hb Hk (HP & (cnt' & Hc & Hst) & Hrv).
split; [rewrite Hb; exact HP|]. split.
- exists cnt'. split; [exact Hc | exact (crt_stat_keep W m m' _ _ Hk Hst)].
- intros a Ha. rewrite Hk; [exact (Hrv a Ha)|]. destruct Ha as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr].
Qed.

(* ---- the resume state after __asan_set_shadow_f5 (0x824d8): crt_ssF0 over the memory after the call, in the env
   built from the registers after it (FSW_rres.fsw_resume_after_rtU_s0 for the saved words, the frame and the flag
   cell, then YI08.st_ok_set_reg to re-seat s3). What is kept across the call comes from the contract's own frame
   clause (outside [SF, SF + 64) and outside its ESTACK window): the saved words lie above the call's sp, the frame's
   flag word lies in the frame, below alloc_ceiling. The frame's bytes are present and not owned (AR_frames_law), the
   flag cell is present (AR_flag_law) and no user-poisoned byte (it is application memory, U is shadow), and the two
   are apart because the flag cell is runtime-owned and no frame byte is. ---- *)
Lemma crt_resume_F0 : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) regsT memT regs2 mem2 md2,
  crt_E cx E ->
  st_ok tfibsegs E crt_ssT_sm (restrict (w_H W3) (mkst regsT (Z_to_bv 64 PC_set_shadow_f5) memT (seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 mem2) md2 k ->
  ARU tfibsegs B ly3 S3 U3 W3 mem2 md2 ->
  aregs_preserved regsT regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (crt_SF cx <= a < crt_SF cx + 64) -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
     aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) memT a) ->
  crt_E cx (Ereg regs2 (crt_extra cx)) /\
  st_ok tfibsegs (Ereg regs2 (crt_extra cx)) crt_ssF0
    (restrict (w_H W3) (mkst regs2 (Z_to_bv 64 0x824d8) mem2 (seg_rom tfibsegs))).
Proof.
intros cx E k ly3 S3 U3 W3 regsT memT regs2 mem2 md2 HE HS HJ HARU HP Hfr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 YM05.alloc_ceiling_val) as HCV.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (HSTK : 17000 <= STK_check_round_trip) by (vm_compute; discriminate).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (H16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (H0 : 192 <= spZ (c_regs cx)) by lia.
destruct (crt_sp1_facts cx H16 H0) as (Hsp1b & _ & _).
(* the registers: at the call they are the engine's atoms; the callee keeps the callee-saved ones *)
assert (Rd : forall (q : bv 5) n, sr_get (ss_regs crt_ssT_sm) q = SOff n 0 -> YK11.getr regsT q = ew E n).
{ intros q n Hq. pose proof (st_ok_restrict_reg tfibsegs (w_H W3) E crt_ssT_sm
    (mkst regsT (Z_to_bv 64 PC_set_shadow_f5) memT (seg_rom tfibsegs)) q HS) as X.
  cbn [ms_regs mkst] in X. rewrite X, Hq. apply fsw_SOff0. }
assert (G : forall (r : Z) n, acallee_saved r -> sr_get (ss_regs crt_ssT_sm) (Z_to_bv 5 r) = SOff n 0 ->
  YK11.getr regs2 (Z_to_bv 5 r) = ew E n).
{ intros r n Hr Hq. rewrite (HP r Hr). exact (Rd _ n Hq). }
assert (G2 : YK11.getr regs2 2%bv = ew E 2)
  by exact (G 2 2%nat ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
assert (G3 : YK11.getr regs2 3%bv = ew E 3)
  by exact (G 3 3%nat ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
assert (G4 : YK11.getr regs2 4%bv = ew E 4)
  by exact (G 4 4%nat ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
assert (G8 : YK11.getr regs2 8%bv = ew E 8)
  by exact (G 8 8%nat ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
assert (G9 : YK11.getr regs2 9%bv = ew E 9)
  by exact (G 9 9%nat ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
assert (G19 : YK11.getr regs2 19%bv = ew E 47)
  by exact (G 19 47%nat ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
assert (G26 : YK11.getr regs2 26%bv = ew E 26)
  by exact (G 26 26%nat ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)).
assert (SPT : spZ regsT = crt_sp1 cx) by (unfold spZ; rewrite (Rd 2%bv 2%nat ltac:(vm_compute; reflexivity)); exact E2).
set (E' := Ereg regs2 (crt_extra cx)) in *.
assert (HE' : crt_E cx E').
{ subst E'. apply crt_E_Ereg.
  - rewrite G2. exact E2.
  - rewrite G3. exact E3.
  - rewrite G4. exact E4.
  - rewrite G8. exact E8.
  - rewrite G9. exact E9.
  - rewrite G26. exact E26. }
assert (Hag : forall n, (32 <= n < 51)%nat -> ew E' n = ew E n) by exact (crt_env_agree cx E E' HE HE').
(* the frame, its shadow and the flag cell *)
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
pose proof (crt_F_ly cx _ ly3 Hly) as EF. pose proof (crt_FL_ly cx _ ly3 Hly) as EFL.
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 (unpoison U3 mem2) md2 3 (c_pos cx) HAR Hin3) as (HF0 & HFc & HFapp).
rewrite EF in HF0, HFc, HFapp. rewrite crt_frame3 in HFc, HFapp.
destruct (al_frames _ _ LAWS ly3 S3 W3 (unpoison U3 mem2) md2 3 (c_pos cx) HAR Hin3) as (_ & _ & Hfp & _).
rewrite EF, crt_frame3 in Hfp.
destruct (al_flag _ _ LAWS ly3 S3 W3 (unpoison U3 mem2) md2 3 (c_pos cx) HAR Hin3) as (HFLp & HFLo & HFLapp & HFLc).
rewrite EFL in HFLp, HFLo, HFLapp, HFLc.
destruct (FFL ly3 S3 W3 (unpoison U3 mem2) md2 3 (c_pos cx) HAR Hin3) as (_ & _ & _ & (HFL0 & _ & _)).
rewrite EFL in HFL0.
assert (HFrng : 0 <= crt_F cx < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds (crt_F cx) HFrng) as (HS1b & HS2b).
assert (HSFlo : 2147450880 <= crt_SF cx) by (unfold crt_SF; rewrite C5 in HS1b; lia).
assert (HSFhi : crt_SF cx < 17594333495296) by (unfold crt_SF; rewrite C2 in HS2b; lia).
assert (Dfs : crt_F cx + 512 <= crt_SF cx \/ crt_SF cx + 64 <= crt_F cx).
{ unfold in_app in HFapp. destruct HFapp as (_ & [Hlow | (Hhigh & _)]).
  - left. unfold kLowShadowBeg in *. lia.
  - right. unfold crt_SF, shadow_addr, SHADOW_OFF, kHighMemBeg in *. Z.div_mod_to_equations. lia. }
assert (Dff : crt_FL cx + 1 <= crt_F cx \/ crt_F cx + 512 <= crt_FL cx).
{ destruct (Z_lt_le_dec (crt_FL cx) (crt_F cx)) as [Hl|Hl]; [left; lia|].
  destruct (Z_lt_le_dec (crt_FL cx) (crt_F cx + 512)) as [Hh|Hh]; [|right; lia].
  exfalso. exact (proj2 (Hfp (crt_FL cx) ltac:(lia)) HFLo). }
assert (HflagU : in_ush U3 (bv_unsigned (Z_to_bv 64 (crt_FL cx))) = false).
{ destruct (in_ush U3 (bv_unsigned (Z_to_bv 64 (crt_FL cx)))) eqn:Eu; [|reflexivity]. exfalso.
  pose proof ASAN_CEIL_range as (Hc1 & _).
  unfold in_app in HFLapp.
  destruct HFLapp as (H00 & [Hlo | (Hhi & Hhc)]);
  rewrite (wz (crt_FL cx) ltac:(unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia)) in Eu;
  pose proof (ush_facts tfibsegs B ly3 S3 U3 W3 mem2 md2 _ HARU Eu) as (_ & L1 & L2);
  unfold ASAN_CEIL, SHADOW_OFF, kHighMemBeg, kLowShadowBeg in *; lia. }
assert (E8' : bv_unsigned (ew E' 8) = spZ (c_regs cx)) by (destruct HE' as (_ & _ & _ & X & _); exact X).
assert (E47' : bv_unsigned (ew E' 47) = crt_F cx) by (rewrite (crt_E_F cx E' HE'); apply wz; lia).
assert (E46' : bv_unsigned (ew E' 46) = crt_FL cx) by (rewrite (crt_E_FL cx E' HE'); apply wz; lia).
assert (E47 : bv_unsigned (ew E 47) = crt_F cx) by (rewrite (crt_E_F cx E HE); apply wz; lia).
(* what the engine held at the call: the saved words and the frame's flag word *)
assert (HC0 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (spZ (c_regs cx))) crt_sv_chunks).
{ pose proof (fsw_region_nth E crt_ssT_sm _ 0 _ HS crt_ssT_sm_s0) as (_ & _ & _ & X).
  unfold crt_s0_region, fs_ret_s0_region in X. cbn [YP09.r_base YP09.r_chunks base_val] in X. rewrite E8 in X.
  exact X. }
assert (HCF : YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (crt_F cx)
    (YP09.mkChunk (fs_frame_bytes 3 - 8) (CVal 8 (SOff 46 0)))).
{ pose proof (fsw_region_nth E crt_ssT_sm _ 2 _ HS crt_ssT_sm_flag) as (_ & _ & _ & X).
  cbn [YP09.r_base YP09.r_chunks base_val] in X. rewrite E47 in X.
  rewrite Forall_forall in X. exact (X _ (or_intror (or_introl eq_refl))). }
(* the frame region and the flag region on the memory after the call *)
assert (ROframe : region_ok tfibsegs E' (mrestrict (w_H W3) mem2) (crt_frame_region crt_csF)).
{ unfold region_ok, crt_frame_region, crt_csF.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E47'.
  split; [lia|]. split; [rewrite crt_frame3; lia|]. split.
  - intros o Ho. rewrite crt_frame3 in Ho. apply (apresent_writable tfibsegs).
    destruct (Hfp (crt_F cx + o) ltac:(lia)) as (Hp & Hno).
    apply (fsw_apresent_notowned B ly3 S3 U3 W3 mem2 md2 _ HARU); [lia | exact Hno | exact Hp].
  - constructor; [|constructor].
    apply (chunk_ok_mbyte E' (mrestrict (w_H W3) memT)).
    + intros i Hi. cbn in Hi. cbn [YP09.c_off]. rewrite crt_frame3.
      apply (mbyte_of_aview tfibsegs (w_H W3) (w_H W3)).
      apply Hfr; [lia | destruct Dfs; lia | rewrite SPT; unfold ESTACK; lia].
    + apply (crt_chunk_env E E'); [rewrite !fsw_SOff0; exact (Hag 46%nat ltac:(lia)) | exact HCF]. }
assert (ROflag : region_ok tfibsegs E' (mrestrict (w_H W3) mem2) crt_flag_region).
{ unfold region_ok, crt_flag_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E46'.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. replace (crt_FL cx + o) with (crt_FL cx) by lia. apply (apresent_writable tfibsegs).
  destruct HFLp as (Hh & b & Hb). split; [exact Hh|]. exists b.
  rewrite (unpoison_out U3 mem2 _ HflagU) in Hb. exact Hb. }
(* the resume state before the re-seat of s3 *)
assert (HS0 : st_ok tfibsegs E' (fss_ret_s0_args 0x824d8 (-104) 0 crt_sv_chunks crt_rel_regions [])
    (restrict (w_H W3) (mkst regs2 (Z_to_bv 64 0x824d8) mem2 (seg_rom tfibsegs)))).
{ eapply (fsw_resume_after_rtU_s0 B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 W3 mem2 md2 k regs2 memT
    (crt_extra cx) crt_sv_chunks crt_rel_regions [] 0x824d8 (-104) 0 HJ HARU).
  - rewrite G8. rewrite <- E8. symmetry. apply Z_to_bv_bv_unsigned.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - exact crt_sv_in.
  - eapply crt_chunks_env; [exact Hag | exact crt_sv_atoms | exact HC0].
  - intros a Ha. apply (mbyte_of_aview tfibsegs (w_H W3) (w_H W3)).
    apply Hfr; [lia | lia | rewrite SPT; unfold ESTACK; lia].
  - constructor; [exact ROframe | constructor; [exact ROflag | constructor]].
  - apply pairwise_disjoint_of_extents.
    unfold fss_ret_s0_regs, crt_rel_regions, crt_frame_region, crt_flag_region, fs_ret_s0_region.
    cbn [map]. unfold extent_of_region, base_val. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
    fold E'. rewrite E8', E47', E46'. rewrite !crt_frame3.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; try exact I;
      first [right; lia | left; lia | destruct Dff as [Hd|Hd]; first [left; lia | right; lia]].
  - exact I. }
split; [exact HE'|].
unfold crt_ssF0. cbv zeta.
eapply (YI08.st_ok_set_reg tfibsegs); [exact HS0 | |].
- intros Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate Hc.
- rewrite fsw_SOff0, (Hag 47%nat ltac:(lia)). exact G19.
Qed.

(* ---- the tail: crt_from at the return of free (same), under crt_INV_T (on B with its register conjunct s3 = F) ---- *)
Lemma crt_tail : crt_from SK B crt_ssT (crt_INV_T B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFR HINV HS.
destruct HINV as (-> & Hk & HQ & H19).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 YM05.alloc_ceiling_val) as HCV.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (HSTK : 17000 <= STK_check_round_trip) by (vm_compute; discriminate).
pose proof HB as (HP0 & _). pose proof HP0 as ((HAP & _) & _). pose proof HAP as (_ & _ & _ & Hgp & Htp & _).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (H16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (H0 : 192 <= spZ (c_regs cx)) by lia.
assert (H47' : spZ (c_regs cx) <= 2 ^ 47) by lia.
destruct (crt_sp1_facts cx H16 H0) as (Hsp1b & _ & _).
assert (Hsp1r : 0 <= crt_sp1 cx < 2 ^ 64) by lia.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
pose proof (crt_F_ly cx _ ly3 Hly) as HF. pose proof (crt_FL_ly cx _ ly3 Hly) as HFL.
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 _ md3 3 (c_pos cx) HAR Hin3) as (HF0 & HFc & _).
rewrite HF in HF0, HFc. rewrite crt_frame3 in HFc.
destruct (FFL ly3 S3 W3 _ md3 3 (c_pos cx) HAR Hin3) as (_ & _ & (_ & HFLimg) & (HFL0 & _ & HFLc)).
rewrite HFL in HFLimg, HFL0, HFLc.
assert (HFr : 0 <= crt_F cx < 2 ^ 64) by lia.
assert (HFLr : 0 <= crt_FL cx < 2 ^ 64) by lia.
assert (HFrng : 0 <= crt_F cx < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds (crt_F cx) HFrng) as (HS1b & HS2b).
assert (HSFlo : 2147450880 <= crt_SF cx) by (unfold crt_SF; rewrite C5 in HS1b; lia).
assert (HSFhi : crt_SF cx < 17594333495296) by (unfold crt_SF; rewrite C2 in HS2b; lia).
assert (HSF : 0 <= crt_SF cx < 2 ^ 64) by lia.
assert (E47 : bv_unsigned (ew E 47) = crt_F cx) by (rewrite (crt_E_F cx E HE); apply wz; lia).
(* B: s3 = F (crt_INV_T's register conjunct), so the run starts from crt_ssTx, s3 re-seated to the frame atom *)
assert (HSx : st_ok tfibsegs E crt_ssTx (restrict (w_H W3) ms3)).
{ unfold crt_ssTx. eapply (YI08.st_ok_set_reg tfibsegs); [exact HS | |].
  - intros Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate Hc.
  - assert (X : sv_denot E (sr_get (ss_regs crt_ssT) 19%bv) = sv_denot E (SOff 47 0)).
    { change (sr_get (ss_regs crt_ssT) 19%bv) with (SOff 19 0). rewrite !fsw_SOff0, H19. symmetry.
      exact (crt_E_F cx E HE). }
    exact (eq_trans (st_ok_restrict_reg tfibsegs (w_H W3) E crt_ssT ms3 19%bv HS) X). }
(* the tail run's write window holds no image byte *)
assert (NWT : forall a, in_img tfibsegs a -> ~ in_wrange E (ss_mem crt_ssT) a).
{ intros a Ha (r & Hr & Hra). pose proof (crt_img_range a Ha) as Hai.
  unfold crt_ssT, crt_ss_ret, fss_ret_s0_args, fss_ret_s0_regs, crt_ret_regions in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]];
    unfold fs_ret_s0_region, crt_slot_region, crt_frame_region, crt_shadow_region in Hra;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra.
  - rewrite E8 in Hra. lia.
  - rewrite E9 in Hra. lia.
  - rewrite E47, crt_frame3 in Hra.
    exact (frm_img tfibsegs B LAWS ly3 S3 W3 _ md3 3 (c_pos cx) a HAR Hin3 ltac:(rewrite HF, crt_frame3; lia) Ha).
  - rewrite E26, crt_frame3 in Hra. change (512 / 8) with 64 in Hra. lia. }
(* 0x824b4 .. 0x824d4: the run to the set_shadow call *)
eapply (crt_tail_run SK B cx E k ly3 S3 (c_U cx) W3 ms3 md3 _ HE H16 H0 HF HFr HSx HJ HARU).
intros ms mat HSm HJm HARUm _ HFrm.
pose proof (crt_img_frame E _ (w_H W3) _ _ HFrm NWT) as KT.
destruct (crt_tail_sm_site cx E W3 ms HE HSF Hsp1r HSm) as (_ & _ & G1 & GSP & _ & _).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W3) E crt_ssT_sm ms HSm crt_ssT_sm_resv) as Ems.
rewrite crt_ssT_sm_pc in Ems. rewrite Ems. rewrite Ems in HSm.
(* the call __asan_set_shadow_f5 (SF, 64) *)
eapply (crt_tail_sm SK B cx E k ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) _ _ SETSH HE H16 H0 H47' HSF Hgp Htp Hin3 HF
  HSm HJm HARUm).
intros regs2 mem2 md2 HJ2 HARU2 HP2 _ Hfr2.
rewrite G1. unfold w64.
assert (KS : forall a, in_img tfibsegs a -> aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) (ms_mem ms) a).
{ intros a Ha. pose proof (crt_img_range a Ha) as Hai.
  apply Hfr2; [lia | lia | rewrite GSP; unfold ESTACK; lia]. }
destruct (crt_resume_F0 cx E k ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) regs2 mem2 md2 HE HSm HJ2 HARU2 HP2 Hfr2)
  as (HE' & HS0).
set (E' := Ereg regs2 (crt_extra cx)) in *.
assert (E8' : bv_unsigned (ew E' 8) = spZ (c_regs cx)) by (destruct HE' as (_ & _ & _ & X & _); exact X).
assert (E47' : bv_unsigned (ew E' 47) = crt_F cx) by (rewrite (crt_E_F cx E' HE'); apply wz; lia).
assert (E46' : bv_unsigned (ew E' 46) = crt_FL cx) by (rewrite (crt_E_FL cx E' HE'); apply wz; lia).
(* 0x824d8 .. 0x824e0: the flag store that hands the frame back *)
eapply (crt_release SK B ASF FFL cx E' k ly3 S3 (c_U cx) W3 (mkst regs2 (Z_to_bv 64 0x824d8) mem2 (seg_rom tfibsegs)) md2 _
  HE' HF HFr HFL HFLr HS0 HJ2 HARU2).
intros ms' mat' HS' HJ' HARU' HFr'.
assert (NW0 : forall a, in_img tfibsegs a -> ~ in_wrange E' (ss_mem crt_ssF0) a).
{ intros a Ha (r & Hr & Hra). pose proof (crt_img_range a Ha) as Hai.
  unfold crt_ssF0, fss_ret_s0_args, fss_ret_s0_regs, crt_rel_regions in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]];
    unfold fs_ret_s0_region, crt_frame_region, crt_flag_region in Hra;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra.
  - rewrite E8' in Hra. lia.
  - rewrite E47', crt_frame3 in Hra.
    exact (frm_img tfibsegs B LAWS ly3 S3 W3 _ md3 3 (c_pos cx) a HAR Hin3 ltac:(rewrite HF, crt_frame3; lia) Ha).
  - rewrite E46' in Hra. assert (a = crt_FL cx) as -> by lia. exact (HFLimg Ha). }
pose proof (crt_img_frame E' _ (w_H W3) mem2 (ms_mem ms') HFr' NW0) as KR.
(* the frame is handed back: drop it and the flag cell, then the epilogue over the saved words *)
pose proof (st_ok_submem tfibsegs E' crt_ssF1 _ [crt_s0_region] HS' crt_ssF1_sub ltac:(vm_compute; reflexivity)) as HS1.
change (st_ok tfibsegs E' crt_ssF1s (restrict (w_H W3) ms')) in HS1.
eapply (fsw_run_to_AJU B crt_tbl crt_tbl_ok W3 40%N 0x8261c E' crt_ssF1s crt_ssE RS_running ms'
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS1 crt_epi_run_eq I HARU' HJ').
- unfold crt_ssF1s. cbn [ss_mem].
  apply awr_ok_cons_stack with (n := 8%nat); [reflexivity | exact E8' | cbn; lia | cbn; lia | apply awr_ok_nil].
- intros msf matf HSf HJf HARUf _ HFrf _.
  assert (NWE : forall a, in_img tfibsegs a -> ~ in_wrange E' (ss_mem crt_ssF1s) a).
  { intros a Ha (r & Hr & Hra). pose proof (crt_img_range a Ha) as Hai.
    unfold crt_ssF1s in Hr. cbn [ss_mem In] in Hr. destruct Hr as [<- | []].
    unfold crt_s0_region, fs_ret_s0_region in Hra. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra.
    rewrite E8' in Hra. lia. }
  pose proof (crt_img_frame E' _ (w_H W3) (ms_mem ms') (ms_mem msf) HFrf NWE) as KE.
  (* 0x8261c: the final `ret` *)
  apply (crt_ret SK B cx E' k ly3 (stack_free_state 3 (c_pos cx) S3) W3 msf _ HB HE' HSf HJf HARUf Hk).
  intros mat2.
  apply (crt_Q_keep cx ly3 S3 (stack_free_state 3 (c_pos cx) S3) W3 (ms_regs ms3) _ (ms_mem ms3) _ md3 _ eq_refl).
  + intros a Ha. rewrite (KE a Ha), (KR a Ha), (KS a Ha). exact (KT a Ha).
  + exact HQ.
Qed.
End tail.
