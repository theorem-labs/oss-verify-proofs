(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YE05.v, with its module paths changed; 2671 of its 2756 lines of code are new or changed and 333 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segA.v, with its module names and numbers changed; 1374 of its 1597 lines of code are new or changed and 2533 lines of the source are left out. *)
(* check_round_trip 0x81b9c (fuzz_state.c:278-314 with round_trip_document fs.c:229-264 inlined), fs.asan-ubsan (image
   tfibsegs = lib/B/YB1v.v, the pinned fuzz_state.asan-ubsan sha256
   5ac5ce0954f87e2d050c481b7b0599cfd55ef554eadc008e51491f44c053d204): the B twin of the ASan walk of lib/B/FSH_Fn_crt.v
   check_round_trip_spec, SEGMENTS 10-11 (lane B1's first half): from the A -> B boundary crt_INV_82068 (B 0x821c4, the
   return of the second strcmp) across the second preset_base64_decode (call 0x821d0, return 0x821d4) and the bcmp
   thunk (call 0x821f4) to the bcmp-return boundaries crtB_INV_8209c (B 0x821f8) / crtB_INV_820a0 (B 0x821fc), where
   lib/B/FSH_crt_segB.v's segment 12 starts; the class-3 fake frame is live throughout (own = [(3, pos)]).
   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from 737d62e41df)
   rule 24: proves no function (kind: segment lemmas of check_round_trip's walk, PORTED from 1ab57ca7ad7) - RT : CrtRt B
   (not FsRt), fr_bcmp tfibsegs B RT now crt_fr_bcmp B RT (a working branch 1ab57ca7ad7).
   Port source: a working branch 737d62e41df proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segB0.v (1733
   lines, on A base v28 a working branch 19c84cdc567), itself PORTED from a working branch
   d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_stdefs.v St3 :260 / St4 :315 and
   check_round_trip_sd3.v crt_cmp_seg :239, with check_round_trip_calls.v CR :142 and check_round_trip_sdglue.v
   crt_keep_blk :612 (the checker's CONFIRM for the walk is on (internal path),
   a Theorem Labs lane, role check, 2026-10-29 04:3xZ; the hit's Require closure is 334 files with 0 Admitted / Axiom /
   Parameter). Its helper lemmas are lane D1's (crtD1 -> crtB0, length cell F + 0x1a0 -> F + 0x1c0) and a Theorem Labs lane's
   boundary re-entry (a23 -> crtB0); here they carry the same B deltas as lib/B/FSH_crt_segD1*.v. Same Definition /
   Lemma names and statement shapes as the A file, over image B; every pc, return address, register and slot fact
   RE-MEASURED on B (capstone over the pinned fs.asan-ubsan, (internal path)) and mapped
   from A by instruction meaning (crt.A2B.tsv: every pc of 0x82068 .. 0x820a0 is an `equal` row except A 0x82070 / 0x82080
   (`mv a1, s11` / `ld a0, 0(s11)` -> B 0x821cc `mv a1, s6` / 0x821dc `ld a0, 0(s6)`), mapped by meaning). The exit
   invariants are lib/B/FSH_crt_segB.v's; the entry invariant is lib/B/FSH_crt_base.v's (B base v28: crt_INV_82068
   carries the length cell's shadow fact, unpoisoned at B 0x81db8 `sb zero, 0x38(s10)`). A new file: no licence lines.

   A name -> A pc -> B pc (names keep their A form, content is B's):
     crtB0_sb10 / crtB0_br10 / crtB0_sc10 / crtB0_run10 / crtB0_site10 / crtB0_regs10 / crtB0_ssave10
                                  0x82068 -> 0x821c4 (crt_INV_82068), the decode 0x8481c -> 0x84c4c, ra 0x82078 -> 0x821d4
     crtB0_INV_82078 / crtB0_ss11_base / crtB0_ss11 / crtB0_sc11 / crtB0_ss11z / crtB0_sb11z / crtB0_ss11zc / crtB0_sc11z
                                  0x82078 -> 0x821d4 (return of the second decode); bcmp 0x42668 -> 0x426d8, ra 0x8209c
                                  -> 0x821f8; `beqz s4` 0x82088 -> 0x821e4, its target 0x820a0 -> 0x821fc
     crtB0_ssB / crtB0_ssB_ok     the bcmp call site (PC_bcmp) over crt_ss_ret's regions
     crtB0_hcall10 / crtB0_seg10  segment 10, 0x821c4 -> 0x821d4
     crtB0_seg11                  segment 11, 0x821d4 -> 0x821f8 (crtB_INV_8209c) / 0x821fc (crtB_INV_820a0)
     crtB0_seg10_11               segments 10-11, 0x821c4 -> the two bcmp-return boundaries

   The two calls and the guards (MEASURED, capstone over the pinned fs.asan-ubsan; A in brackets):
     10  0x821c4 `bnez a0`  -> 0x824e4 (__asan_handle_no_return, abort) [0x82068 -> 0x824b8]: a0 = strcmp's 0, crt_INV_82068
         0x821c8 `mv a0, s2` (text), 0x821cc `mv a1, s6` (&n = F + 0x1c0; A `mv a1, s11`), 0x821d0 `jal`
         preset_base64_decode 0x84c4c, return 0x821d4 (decode_spec_ff: lenp in crt's class-3 FAKE frame)
     11  0x821d4 `beqz a0`  -> 0x824e4: decode's success post, dec >= 4096 + HEAD (an atom fact of the run state)
         0x821d8 `mv s9, a0`; 0x821dc `ld a0, 0(s6)` (the cell decode wrote: |bs|; A `ld a0, 0(s11)`)
         0x821e0 `bne a0, s4` -> 0x824e4: both sides are atom 20 (s4 = |bs|), decided by the engine
         0x821e4 `beqz s4`  -> 0x821fc: |bs| = 0 skips the bcmp (exit crtB_ss_820a0, crtB_INV_820a0)
         0x821e8-0x821f0 a0 = s9, a1 = s5 (bd), a2 = s4; 0x821f4 `jal` the bcmp thunk 0x426d8 (FsRt.fr_bcmp), return
         0x821f8 (exit crtB_ss_8209c, crtB_INV_8209c: bcmp answers 0 since dec and bd hold the same |bs| bytes)
   The only trap edges in 0x821c4 .. 0x821f8 are the three branches to 0x824e4 above, each decided by a callee post
   (lib/B/FSH_crt_segD.v's branch-target scan: the UBSan trap 0x82620 and the `__asan_report_*` arms 0x82624..0x8266c are
   reached only from segments 5 and 7).

   B's register allocation differs from A's in this stretch, and every difference is carried into the proofs:
   - &n = F + 0x1c0 is s6 = atom 22 (A: s11 = atom 27): crtB0_regs10's a1, crtB0_ss11_base's re-seat (s6 := SOff 47
     0x1c0), crtB0_ss11_ok's premise ew E 22 = F + 0x1c0, and the extra lemmas crtB0_sc11_s6 / crtB0_sc11z_s6 /
     crtB0_s6_val, from which the exits' ew E 22 = F + 0x1c0 is derived (the re-seated s6 survives both runs and the
     bcmp call, a callee-saved register);
   - SF is s10 = atom 26 (A: s3 = atom 19): crtB0_sc11z_shape, crtB0_reseat / crtB0_reenter, crtB0_bcmp_call /
     crtB0_bcmp_resume, crtB0_ssB_ok (as lib/B/FSH_crt_site.v / FSH_crt_segD1_bcmp.v); B's crt_E has nineteen extra
     atoms 32 .. 50, so the env-agreement range is 32 <= n < 51 (A: < 50);
   - the boundary invariants carry B crt_INV_8212c's register heads s2 = text, s4 = len, s5 = bd, s11 = F + 0xe0,
     s7 = F + 0x80, s6 = F + 0x1c0, s3 = F (A: s6 = F + 0xe0, s10 = F + 0x20, s11 = F + 0x1c0), so crtB0_INV_82078 and
     the two exits get s3 = F and s6 = F + 0x1c0 from B crt_INV_82068 (s3 = F is untouched by both segments; s6 by the
     re-seat above); the callee-saved lists of the two runs exclude s9 (dec) and s6 (re-seated) where A's excluded s9
     and s11. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG05 YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret FSW_frame
FSW_rd FSW_strkit FSW_crt_tbl FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt FSH_crt_base FSH_crt_site
FSH_crt_cstr FSH_crt_segB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterSpecFacts HState.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD: a SUCCESS here (the build errors naming this line) means a wrong sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.

(* ================= pure facts ================= *)
(* the decoded body is no longer than its text (port of lib/Prog/check_reject_clean_starved.v crs_six_len / crs_dec_len
   at WriterSpec's names) *)
Lemma crtB0_six_len : forall six, (length (WriterSpec.six_bytes six) <= length six)%nat.
Proof.
fix IH 1. intros [|a [|b [|c [|d r]]]]; cbn [WriterSpec.six_bytes length]; try lia.
specialize (IH r). lia.
Qed.
Lemma crtB0_dec_len : forall tb bs, WriterSpec.b64_dec tb = Some bs -> (length bs <= length tb)%nat.
Proof.
intros tb bs H. unfold WriterSpec.b64_dec in H.
destruct (WriterSpec.b64_scan 0 [] tb) as [[six pad]|] eqn:E; [|discriminate].
destruct ((pad <=? 2) && WriterSpec.six_tail_ok six); [|discriminate]. injection H as <-.
destruct (WriterSpecFacts.scan_inv tb 0 [] six pad E) as [H1 _]. cbn [length] in H1.
pose proof (crtB0_six_len six). lia.
Qed.
Lemma crtB0_len_bound : forall (tb : list byte) bs, WriterSpec.b64_dec (HState.zs tb) = Some bs ->
  (length bs <= length tb)%nat.
Proof.
intros tb bs H. pose proof (crtB0_dec_len _ _ H) as X. unfold HState.zs in X. rewrite length_map in X. exact X.
Qed.
(* the block bytes the walk holds at 0x82288 (A 0x8212c) fit crt's LIVE_check_round_trip = 2 ^ 25: the text is at most 3 MiB and
   the body no longer than it *)
Lemma crtB0_live_room : forall cx,
  (length (c_bs cx) <= length (c_tb cx))%nat -> Z.of_nat (length (c_tb cx)) <= 3 * 2 ^ 20 ->
  LIVE_8212c cx <= LIVE_check_round_trip.
Proof.
intros cx H1 H2.
unfold LIVE_8212c, LIVE_82068, crt_es, crt_len, FSH_Fn_writer.enc_size, FSH_Fn_writer.dec_size, LIVE_check_round_trip,
  HEAD.
rewrite WriterSpecFacts.b64_enc_length, Nat2Z.inj_mul, Nat2Z.inj_div, Nat2Z.inj_add.
change (Z.of_nat 2) with 2. change (Z.of_nat 3) with 3. change (Z.of_nat 4) with 4.
apply Nat2Z.inj_le in H1.
change (2 ^ 25) with 33554432. change (3 * 2 ^ 20) with 3145728 in H2.
Z.div_mod_to_equations. lia.
Qed.
Lemma crtB0_req_size : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); [lia | reflexivity]. Qed.
(* a list of byte values reads back unchanged through bz / zs (D1's crtD1_zs_bz) *)
Lemma crtB0_zs_bz : forall l, Forall (fun b => 0 <= b < 256) l -> HState.zs (HState.bz l) = l.
Proof.
intros l Hl. unfold HState.zs, HState.bz. induction Hl as [|x l Hx Hl IH]; [reflexivity|].
cbn [map]. rewrite IH. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.
(* a byte window's view (D1's crtD1_zb_view) *)
Lemma crtB0_zb_view : forall (W : world tfibsegs) mem p l i, zbytes_at tfibsegs W mem p l ->
  0 <= i < Z.of_nat (length l) ->
  aview tfibsegs (w_H W) mem (p + i) = Some (bv_unsigned (Z_to_bv 8 (nth (Z.to_nat i) l 0))).
Proof.
intros W mem p l i H Hi. unfold aview.
replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia.
rewrite (garr8_mbyte tfibsegs (mrestrict (w_H W) mem) p l (Z.to_nat i) H ltac:(lia)). reflexivity.
Qed.
(* a byte window carried by a view equality on its bytes *)
Lemma crtB0_zb_keep : forall (W W' : world tfibsegs) m m' p l,
  (forall a, p <= a < p + Z.of_nat (length l) -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  zbytes_at tfibsegs W m p l -> zbytes_at tfibsegs W' m' p l.
Proof.
intros W W' m m' p l K H. unfold zbytes_at in *.
apply (crtB_garr8_keep (w_H W) (w_H W') m m' p l); [|exact H].
intros i Hi. apply K. lia.
Qed.
(* the shadow hull of a sub-range lies in the hull of the range (D1's crtD1_hull_sub) *)
Lemma crtB0_hull_sub : forall (rd : reader) P N x len, shadow_hull_vis rd P N -> P <= x -> 0 < len ->
  x + len <= P + N -> shadow_hull_vis rd x len.
Proof.
intros rd P N x len H H1 H2 H3 s Hs. apply H.
pose proof (Z.div_le_mono P x 8 ltac:(lia) H1) as D1.
pose proof (Z.div_le_mono (x + len - 1) (P + N - 1) 8 ltac:(lia) ltac:(lia)) as D2.
assert (A1 : shadow_addr P <= shadow_addr x) by (unfold shadow_addr; lia).
assert (A2 : shadow_addr (x + len - 1) <= shadow_addr (P + N - 1)) by (unfold shadow_addr; lia).
pose proof (Z.div_le_mono _ _ 8 ltac:(lia) A1) as D3.
pose proof (Z.div_le_mono _ _ 8 ltac:(lia) A2) as D4.
lia.
Qed.
(* a byte visible on the unpoisoned memory is visible on the raw one (D1's crtD1_vis_raw) *)
Lemma crtB0_vis_raw : forall U (W : world tfibsegs) mem s, upoisoned tfibsegs W mem U ->
  aview tfibsegs (w_H W) (unpoison U mem) s <> None -> aview tfibsegs (w_H W) mem s <> None.
Proof.
intros U W mem s HP Hv. destruct (in_ush U (bv_unsigned (Z_to_bv 64 s))) eqn:E.
- rewrite (aview_mod tfibsegs (w_H W) mem s).
  assert (Es : s mod 2 ^ 64 = bv_unsigned (Z_to_bv 64 s)).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. reflexivity. }
  rewrite Es, (HP _ E). discriminate.
- rewrite <- (aview_unpoison_out tfibsegs (w_H W) U mem s E). exact Hv.
Qed.
(* the statics of FS_PSTAT_FP lie below the shadow band (D1's crtD1_pstat_low) *)
Lemma crtB0_pstat_low : forall a, inFP FS_PSTAT_FP a -> 0 <= a < SHADOW_OFF.
Proof.
intros a (r & Hr & Hra). unfold FS_PSTAT_FP in Hr. unfold SHADOW_OFF.
cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in Hra; lia|]). destruct Hr.
Qed.
(* eight present bytes hold a 64-bit value (FSW_indent.rdword_present and AFl3.rdword_range, restated) *)
Lemma crtB0_aview_range : forall (H : word -> bool) mem a v, aview tfibsegs H mem a = Some v -> 0 <= v < 256.
Proof.
intros H mem a v Hv. unfold aview in Hv. destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|]; [|discriminate].
cbn in Hv. injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as X. unfold bv_modulus in X. cbn in X. lia.
Qed.
Lemma crtB0_val_ex : forall (H : word -> bool) m a, (forall i, 0 <= i < 8 -> apresent H m (a + i)) ->
  exists v, val_mem tfibsegs (mrestrict H m) a 8 v /\ 0 <= v < 2 ^ 64.
Proof.
intros H m a Hp.
assert (E : forall i, 0 <= i < 8 -> exists b, aview tfibsegs H m (a + i) = Some b).
{ intros i Hi. destruct (Hp i Hi) as (Hh & b & Hb). exists (bv_unsigned b).
  unfold aview, mbyte, mrestrict. rewrite Hh, Hb. reflexivity. }
destruct (E 0 ltac:(lia)) as (b0 & E0). rewrite Z.add_0_r in E0.
destruct (E 1 ltac:(lia)) as (b1 & E1). destruct (E 2 ltac:(lia)) as (b2 & E2).
destruct (E 3 ltac:(lia)) as (b3 & E3). destruct (E 4 ltac:(lia)) as (b4 & E4).
destruct (E 5 ltac:(lia)) as (b5 & E5). destruct (E 6 ltac:(lia)) as (b6 & E6).
destruct (E 7 ltac:(lia)) as (b7 & E7).
assert (Hw : rdword (aview tfibsegs H m) a =
  Some (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * b7)))))))).
{ unfold rdword. rewrite E0, E1, E2, E3, E4, E5, E6, E7. reflexivity. }
eexists. split; [exact (val_mem_of_rdword tfibsegs H m a _ Hw)|].
pose proof (crtB0_aview_range _ _ _ _ E0). pose proof (crtB0_aview_range _ _ _ _ E1).
pose proof (crtB0_aview_range _ _ _ _ E2). pose proof (crtB0_aview_range _ _ _ _ E3).
pose proof (crtB0_aview_range _ _ _ _ E4). pose proof (crtB0_aview_range _ _ _ _ E5).
pose proof (crtB0_aview_range _ _ _ _ E6). pose proof (crtB0_aview_range _ _ _ _ E7).
lia.
Qed.
(* a chunk list inside [lo, hi) of its base is kept by a memory that keeps those bytes (a Theorem Labs lane's a23_chunks_mb) *)
Lemma crtB0_chunks_mb : forall {fx : YK11.FPState} E (m m' : word -> option byte) base cs lo hi,
  Forall (fun c => lo <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= hi) cs ->
  (forall a, base + lo <= a < base + hi -> mbyte tfibsegs m' a = mbyte tfibsegs m a) ->
  Forall (YP09.chunk_ok tfibsegs E m base) cs -> Forall (YP09.chunk_ok tfibsegs E m' base) cs.
Proof.
intros fx E m m' base cs lo hi Hin Hmb Hc. rewrite Forall_forall in Hin, Hc |- *. intros c Hc'.
apply (chunk_ok_mbyte E m); [|exact (Hc c Hc')].
intros i Hi. destruct (Hin c Hc') as (H1 & H2 & H3). apply Hmb. lia.
Qed.
(* a register a run state holds as an atom, read through the env re-seated on the machine's registers *)
Lemma crtB0_ew_run : forall {fx : YK11.FPState} E ss (H : word -> bool) ms extra (q n : nat),
  st_ok tfibsegs E ss (restrict H ms) -> (q < 32)%nat ->
  sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat q)) = SOff n 0 -> ew (Ereg (ms_regs ms) extra) q = ew E n.
Proof.
intros fx E ss H ms extra q n HS Hq Hr.
rewrite (ew_Ereg_lt (ms_regs ms) extra q Hq), (st_ok_restrict_reg tfibsegs H E ss ms _ HS), Hr.
apply fsw_SOff0.
Qed.

(* ================= the engine runs (MEASURED over crt_tbl on the pinned fs.asan; each closed by vm_compute) ========= *)
(* ---- segment 10: from crt_ss2 0x821c4 the engine stops at once at `bnez a0`; with a0 = 0 it reaches the decoder's
   entry 0x84c4c with ra = 0x821d4, a0 = s2 = text (atom 18), a1 = s6 = &n = F + 0x1c0 (atom 22; 0x821cc `mv a1, s6`,
   A: s11 = atom 27) ---- *)
Definition crtB0_sb10 : sstate := Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x821c4)).
Lemma crtB0_br10 :
  sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x821c4) = (crtB0_sb10, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition crtB0_sc10 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL A_preset_base64_decode (add_cond crtB0_sb10 crt_c0)).
Lemma crtB0_run10 :
  sym_run_toN tfibsegs crt_tbl FUEL A_preset_base64_decode (add_cond crtB0_sb10 crt_c0) = (crtB0_sc10, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtB0_site10 : crt_site crtB0_sb10 crtB0_sc10 A_preset_base64_decode 0x821d4.
Proof. unfold crt_site, crt_csite. repeat split; vm_compute; reflexivity. Qed.
Lemma crtB0_regs10 :
  sr_get (ss_regs crtB0_sc10) 1%bv = SLit 0x821d4 /\ sr_get (ss_regs crtB0_sc10) 10%bv = SOff 18 0 /\
  sr_get (ss_regs crtB0_sc10) 11%bv = SOff 22 0.
Proof. repeat split; vm_compute; reflexivity. Qed.
Lemma crtB0_ssave10 : crt_ssave crtB0_sc10.
Proof. apply crt_ssave_dec. vm_compute. reflexivity. Qed.

(* ---- segment 11: the start state is the shared crt_ss2 shape PLUS the frame as a READ-ONLY region carrying the
   length cell (the stretch reads it, `ld a0, 0(s6)` 0x821dc, and writes nothing), s6 re-seated on the frame atom
   (A: `ld a0, 0(s11)` 0x82080, s11 re-seated).
   Atom facts let the engine decide `beqz a0` (dec in [4096, 2 ^ 47)) and, on the body arm, `beqz s4` (|bs| >= 1);
   `bne a0, s4` needs none (both sides read atom 20). ---- *)
Definition crtB0_fptr : afact := mkAF 4096 (2 ^ 47) 0.
Definition crtB0_csF11 : list YP09.chunk := YP09.mkChunk 0x1c0 (CVal 8 (SOff 20 0)) :: crt_csF.
Definition crtB0_fr_ro : YP09.region := YP09.mkRegion (Some 47%nat) 0 (fs_frame_bytes 3) 0 0 crtB0_csF11.
Definition crtB0_ss11_base : sstate :=
  mkSS 0x821d4 (sr_set sr_atoms 22%bv (SOff 47 0x1c0))
    [crt_s0_region; crt_slot_region crt_cs1; crtB0_fr_ro] None
    (mkFacts ((8%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: crt_ret_facts) [] []).
(* body arm (|bs| >= 1): to the bcmp thunk 0x426d8 with ra = 0x821f8, a0 = s9 = dec (atom 10), a1 = bd (atom 21),
   a2 = |bs| (atom 20) *)
Definition crtB0_ss11 : sstate := add_atom (add_atom crtB0_ss11_base 10 crtB0_fptr) 20 (mkAF 1 (2 ^ 32) 0).
Definition crtB0_sc11 : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL PC_bcmp crtB0_ss11).
Lemma crtB0_run11 : sym_run_toN tfibsegs crt_tbl FUEL PC_bcmp crtB0_ss11 = (crtB0_sc11, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtB0_sc11_regs :
  ss_pc crtB0_sc11 = PC_bcmp /\
  map (fun r => sr_get (ss_regs crtB0_sc11) r) [1; 10; 11; 12; 2; 3; 4; 25]%bv =
  [SLit 0x821f8; SOff 10 0; SOff 21 0; SOff 20 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 10 0] /\
  ss_resv crtB0_sc11 = None.
Proof. repeat split; vm_compute; reflexivity. Qed.
(* empty-body arm (|bs| = 0): the engine stops at `beqz s4`; the taken arm is the condition s4 = 0, and the next pc
   is the join 0x821fc (`beqz s4` 0x821e4; A 0x82088 -> 0x820a0), with s9 = dec and a0 = the cell's |bs| *)
Definition crtB0_ss11z : sstate := add_atom crtB0_ss11_base 10 crtB0_fptr.
Definition crtB0_sb11z : sstate := Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL crtB0_ss11z).
Lemma crtB0_br11z : sym_runN tfibsegs crt_tbl FUEL crtB0_ss11z
  = (crtB0_sb11z, RS_stopped (SR_branch BC_EQ (SOff 20 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition crtB0_ss11zc : sstate := add_cond crtB0_sb11z (mkAC BC_EQ (SOff 20 0) (SLit 0)).
Definition crtB0_sc11z : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x821fc crtB0_ss11zc).
Lemma crtB0_run11z : sym_run_toN tfibsegs crt_tbl FUEL 0x821fc crtB0_ss11zc = (crtB0_sc11z, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtB0_sc11z_shape :
  ss_pc crtB0_sc11z = 0x821fc /\ ss_resv crtB0_sc11z = None /\
  nth_error (ss_mem crtB0_sc11z) 0 = Some crt_s0_region /\
  nth_error (ss_mem crtB0_sc11z) 1 = Some (crt_slot_region crt_cs1) /\
  ss_mem crtB0_sc11z = [crt_s0_region; crt_slot_region crt_cs1; crtB0_fr_ro] /\
  sr_get (ss_regs crtB0_sc11z) 2%bv = SOff 2 0 /\ sr_get (ss_regs crtB0_sc11z) 3%bv = SOff 3 0 /\
  sr_get (ss_regs crtB0_sc11z) 4%bv = SOff 4 0 /\ sr_get (ss_regs crtB0_sc11z) 8%bv = SOff 8 0 /\
  sr_get (ss_regs crtB0_sc11z) 9%bv = SOff 9 0 /\ sr_get (ss_regs crtB0_sc11z) 26%bv = SOff 26 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ================= the walk's helpers, from lane D1 (FSH_crt_segD1_keep.v / _bd.v / _bcmp.v / _s31.v /
   FSH_crt_segD1.v at a working branch 82a1d1bf3a6) and a Theorem Labs lane (FSH_crt_segA23.v reseat / reenter),
   renamed ================= *)
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* the shadow of a live frame lies in the shadow band [SHADOW_OFF, kHighMemBeg) *)
Lemma crtB0_frame_shadow_band : forall ly S (W : world tfibsegs) mem md cid pos a,
  AR tfibsegs B ly S W mem md -> In (cid, pos) (frames S) ->
  shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
  SHADOW_OFF <= a < kHighMemBeg.
Proof.
intros ly S W mem md cid pos a HAR Hin Ha.
destruct (frames_bounds tfibsegs B LAWS ly S W mem md cid pos HAR Hin) as (HF4096 & HFc & _).
pose proof (fs_frame_bytes_nonneg cid) as Hnn. pose proof asan_consts as (C1 & _).
unfold shadow_addr in Ha. unfold SHADOW_OFF, kHighMemBeg in *.
Z.div_mod_to_equations. lia.
Qed.

(* the footprint of one preset_base64_decode call (the statics plus the 8-byte length cell inside crt's class-3 frame)
   meets no live block, no OTHER frame byte, no shadow byte *)
Lemma crtB0_dec_fp_clear : forall ly S (W : world tfibsegs) mem md pos lenp,
  AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) ->
  frame_addr ly 3 pos <= lenp -> lenp + 8 <= frame_addr ly 3 pos + fs_frame_bytes 3 ->
  (forall q m a, In (q, m) (ablocks B ly S) -> q <= a < q + req_size m ->
     ~ inFP (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) a) /\
  (forall a, frame_addr ly 3 pos <= a < frame_addr ly 3 pos + fs_frame_bytes 3 -> ~ (lenp <= a < lenp + 8) ->
     ~ inFP (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) a) /\
  (forall a, shadow_addr (frame_addr ly 3 pos) <= a < shadow_addr (frame_addr ly 3 pos) + fs_frame_bytes 3 / 8 ->
     ~ inFP (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) a) /\
  (forall a, inFP (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)).
Proof.
intros ly S W mem md pos lenp HAR Hin Hl1 Hl2.
pose proof asan_consts as (C1 & _).
destruct (frames_bounds tfibsegs B LAWS ly S W mem md 3 pos HAR Hin) as (HF4096 & HFc & HFapp).
assert (Hc : forall a, inFP [(lenp, lenp + 8)] a -> lenp <= a < lenp + 8).
{ intros a Ha. apply inFP_cons in Ha as [Ha|Ha]; [exact Ha | destruct (inFP_nil a Ha)]. }
split; [|split; [|split]].
- intros q m a Hq Ha HF. apply inFP_app in HF as [HF|HF].
  + exact (blk_img tfibsegs B LAWS ly S W mem md q m a HAR Hq Ha (crt_pstat_img a HF)).
  + pose proof (Hc a HF) as Hr.
    pose proof (sep_block_frame tfibsegs B LAWS ly S W mem md q m 3 pos HAR Hq Hin) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. lia.
- intros a Ha Hna HF. apply inFP_app in HF as [HF|HF].
  + exact (frm_img tfibsegs B LAWS ly S W mem md 3 pos a HAR Hin Ha (crt_pstat_img a HF)).
  + exact (Hna (Hc a HF)).
- intros a Ha HF. pose proof (crtB0_frame_shadow_band ly S W mem md 3 pos a HAR Hin Ha) as Hs.
  apply inFP_app in HF as [HF|HF].
  + pose proof (crtB0_pstat_low a HF) as Hl. lia.
  + pose proof (Hc a HF) as Hr.
    pose proof (in_app_addr _ _ a HFapp ltac:(lia)) as Hap.
    unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia.
- intros a HF. apply inFP_app in HF as [HF|HF].
  + pose proof (crtB0_pstat_low a HF) as Hl. lia.
  + pose proof (Hc a HF) as Hr.
    pose proof (in_app_addr _ _ a HFapp ltac:(lia)) as Hap.
    unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia.
Qed.

(* the user bytes [x, x + len) of a block live at a state: bounds, amem_range, no image byte, application bytes, and
   their shadow on the RAW memory (D1's crtD1_blk_user) *)
Lemma crtB0_blk_user : forall ly S U (W : world tfibsegs) mem md P N x len,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U -> In (P, N) (ablocks B ly S) ->
  P + HEAD <= x -> 0 <= len -> x + len <= P + req_size N ->
  4096 <= x /\ x + len <= alloc_ceiling /\ N < MALLOC_MAX /\ amem_range x len /\
  (forall a, x <= a < x + len -> ~ in_img tfibsegs a /\ (a < SHADOW_OFF \/ kHighMemBeg <= a)) /\
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x len /\
  (0 < len -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x len).
Proof.
intros ly S U W mem md P N x len HARU FH Hin Hx Hl Hn.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof HARU as (_ & _ & HP).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md P N HAR Hin)
  as (_ & H4096 & Hceil & Happ & _ & _ & HMx).
destruct (al_shadow _ _ LAWS ly S W (unpoison U mem) md P N HAR Hin) as (_ & Hhull).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_lt rc) as HC47. change (2 ^ 47) with 140737488355328 in HC47.
cbv [HEAD] in Hx.
cbv [in_app kLowShadowBeg] in Happ. rewrite C3 in Happ.
split; [lia|]. split; [lia|]. split; [lia|]. split.
{ unfold amem_range. rewrite C3, C4, C5.
  destruct Happ as (_ & [Hlo | (Hh1 & _)]); [left; lia | right; split; lia]. }
split.
{ intros a Ha. split.
  - exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md P N a HAR Hin ltac:(lia)).
  - cbv [SHADOW_OFF]. destruct Happ as (_ & [Hlo | (Hh1 & _)]); [left; lia | right; rewrite C3; lia]. }
split.
{ exact (fsw_block_body_addressable B ly S U W mem md P N x len HARU FH Hin ltac:(lia) Hl Hn). }
intros Hl0 s Hs. apply (crtB0_vis_raw U W mem s HP).
exact (crtB0_hull_sub _ P (req_size N) x len Hhull ltac:(lia) Hl0 Hn s Hs).
Qed.

(* every premise the bcmp contract asks of the two ranges, at a state of the walk (D1's crtD1_bcmp_data): p = dec, the
   second decode's block; bd, crt_base's body block, carried from the entry memory by ajournal's block clause *)
Lemma crtB0_bcmp_data : forall cx ly3 S3 U3 (W3 : world tfibsegs) regsT memT mdT k p n,
  crt_base B cx ->
  @ajournal rc SK tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 memT) mdT k ->
  ARU tfibsegs B ly3 S3 U3 W3 memT mdT -> FSupoisonU.fs_heads B ly3 S3 U3 ->
  (forall b, In b (ablocks B (c_ly cx) (c_S cx)) -> In b (ablocks B ly3 S3)) ->
  fs_rblock tfibsegs B ly3 S3 W3 memT p n -> zbytes_at tfibsegs W3 memT p (c_bs cx) ->
  Z.of_nat (length (c_bs cx)) <= n ->
  spZ regsT = crt_sp1 cx ->
  let len := Z.of_nat (length (c_bs cx)) in
  0 <= len < 2 ^ 32 /\ 0 <= p /\ p + len <= 2 ^ 63 /\ 0 <= c_bd cx /\ c_bd cx + len <= 2 ^ 63 /\
  src_ok tfibsegs W3 regsT memT p len /\ src_ok tfibsegs W3 regsT memT (c_bd cx) len /\
  (forall a, p <= a < p + len -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) /\
  (forall a, c_bd cx <= a < c_bd cx + len -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) /\
  amem_range p len /\ amem_range (c_bd cx) len /\
  range_addressable (aview tfibsegs (w_H W3) memT) SHADOW_OFF p len /\
  (0 < len -> shadow_hull_vis (aview tfibsegs (w_H W3) memT) p len) /\
  range_addressable (aview tfibsegs (w_H W3) memT) SHADOW_OFF (c_bd cx) len /\
  (0 < len -> shadow_hull_vis (aview tfibsegs (w_H W3) memT) (c_bd cx) len) /\
  (forall i, 0 <= i < len -> aview tfibsegs (w_H W3) memT (c_bd cx + i) = aview tfibsegs (w_H W3) memT (p + i)).
Proof.
intros cx ly3 S3 U3 W3 regsT memT mdT k p n Hb HJ HARU3 FH3 Hkeep Hrb Hzp Hln Hsp. cbv zeta.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_lt rc) as HC47. change (2 ^ 47) with 140737488355328 in HC47.
assert (HSTK : 17000 <= STK_check_round_trip) by (vm_compute; discriminate).
destruct Hb as (Hpre & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hzbd & (k0 & Hrb0 & Hk0) & _).
destruct Hpre as (((HAR0 & _) & Hok0 & Hp0) & _).
assert (HARU0 : ARU tfibsegs B (c_ly cx) (c_S cx) (c_U cx) (c_W cx) (c_mem cx) (c_md cx))
  by (split; [exact HAR0 | split; [exact Hok0 | exact Hp0]]).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K2 & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & _ & Hsl & Hslo & _).
destruct (crt_sp1_facts cx Hal16 ltac:(lia)) as (Hsp1b & _ & _).
destruct Hrb as (Hin3p & _ & Hn0 & _).
destruct Hrb0 as (Hin0 & _ & Hk00 & _).
pose proof (Hkeep _ Hin0) as Hin3b.
assert (Rp : req_size (n + HEAD) = n + HEAD) by (apply crtB0_req_size; cbv [HEAD]; lia).
assert (Rb : req_size (k0 + HEAD) = k0 + HEAD) by (apply crtB0_req_size; cbv [HEAD]; lia).
destruct (crtB0_blk_user ly3 S3 U3 W3 memT mdT (p - HEAD) (n + HEAD) p (Z.of_nat (length (c_bs cx)))
  HARU3 FH3 Hin3p ltac:(lia) ltac:(lia) ltac:(rewrite Rp; lia))
  as (Hp4096 & Hpc & HpMx & Hpm & Hpi & Hpa & Hph).
destruct (crtB0_blk_user ly3 S3 U3 W3 memT mdT (c_bd cx - HEAD) (k0 + HEAD) (c_bd cx) (Z.of_nat (length (c_bs cx)))
  HARU3 FH3 Hin3b ltac:(lia) ltac:(lia) ltac:(rewrite Rb; lia))
  as (Hb4096 & Hbc & _ & Hbm & Hbi & Hba & Hbh).
cbv [MALLOC_MAX HEAD] in HpMx.
assert (HW : forall a, a < alloc_ceiling -> a < spZ regsT - 2 * ESTACK).
{ intros a Ha. rewrite Hsp. unfold ESTACK. lia. }
assert (Hok : Forall (fun b => 0 <= b < 256) (c_bs cx)) by exact (garr8_bytes_ok tfibsegs _ _ _ Hzp).
rewrite (crtB0_zs_bz _ Hok) in Hzbd.
assert (EQ : forall i, 0 <= i < Z.of_nat (length (c_bs cx)) ->
  aview tfibsegs (w_H W3) memT (c_bd cx + i) = aview tfibsegs (w_H W3) memT (p + i)).
{ intros i Hi.
  rewrite (crtB0_zb_view W3 memT p (c_bs cx) i Hzp Hi).
  rewrite <- (crtB0_zb_view (c_W cx) (c_mem cx) (c_bd cx) (c_bs cx) i Hzbd Hi).
  destruct (Hbi (c_bd cx + i) ltac:(lia)) as (Hni & Happ).
  apply (crt_raw_of_unp B (c_ly cx) (c_S cx) (c_U cx) (c_W cx) (c_mem cx) (c_md cx) ly3 S3 U3 W3 memT mdT
    (c_bd cx + i) HARU0 HARU3); [change (2 ^ 64) with 18446744073709551616; lia | exact Happ|].
  pose proof (K2 (c_bd cx - HEAD) (k0 + HEAD) (HEAD + i) Hin0 Hin3b) as K.
  replace (c_bd cx - HEAD + (HEAD + i)) with (c_bd cx + i) in K by lia.
  apply K; [rewrite Rb; cbv [HEAD]; lia|].
  intros Hf. exact (Hni (crt_pstat_img _ Hf)). }
split; [change (2 ^ 32) with 4294967296; lia|].
split; [lia|].
split; [change (2 ^ 63) with 9223372036854775808; lia|].
split; [lia|].
split; [change (2 ^ 63) with 9223372036854775808; lia|].
split.
{ intros a Ha. split; [|pose proof (HW a ltac:(lia)); unfold ESTACK in *; lia].
  replace a with (p + (a - p)) by lia.
  rewrite (crtB0_zb_view W3 memT p (c_bs cx) (a - p) Hzp ltac:(lia)). discriminate. }
split.
{ intros a Ha. split; [|pose proof (HW a ltac:(lia)); unfold ESTACK in *; lia].
  replace a with (c_bd cx + (a - c_bd cx)) by lia.
  rewrite (EQ (a - c_bd cx) ltac:(lia)).
  rewrite (crtB0_zb_view W3 memT p (c_bs cx) (a - c_bd cx) Hzp ltac:(lia)). discriminate. }
split; [intros a Ha; pose proof (HW a ltac:(lia)); lia|].
split; [intros a Ha; pose proof (HW a ltac:(lia)); lia|].
split; [exact Hpm|].
split; [exact Hbm|].
split; [exact Hpa|].
split; [exact Hph|].
split; [exact Hba|].
split; [exact Hbh|].
exact EQ.
Qed.

(* the frame region of a boundary state, with the length cell F + 0x1c0 added (D1's crtD1_add_ncell) *)
Lemma crtB0_add_ncell : forall cx E (W : world tfibsegs) ms r len,
  crt_E cx E -> 0 <= crt_F cx < 2 ^ 64 -> ew E 20 = Z_to_bv 64 len -> 0 <= len < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (crt_F cx + 0x1c0) 8 len ->
  st_ok tfibsegs E (crt_ss_ret r crt_cs1 crt_csF) (restrict (w_H W) ms) ->
  st_ok tfibsegs E (crt_ss_ret r crt_cs1 crtB0_csF11) (restrict (w_H W) ms).
Proof.
intros cx E W ms r len HE HF E20 Hlen Hval HS.
assert (E47 : bv_unsigned (ew E 47) = crt_F cx)
  by (rewrite (crt_E_F cx E HE), Z_to_bv_unsigned, bv_wrap_small
        by (change (bv_modulus 64) with (2 ^ 64); lia); reflexivity).
destruct HS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
split; [exact A6|]. split; [exact A7|]. split; [|exact A9].
unfold crt_ss_ret, fss_ret_s0_args, fss_ret_s0_regs, crt_ret_regions in A8 |- *.
cbn [ss_mem] in A8 |- *.
destruct A8 as (Hwf & Hok & Hpd).
assert (HCH : YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (bv_unsigned (ew E 47))
    (YP09.mkChunk 0x1c0 (CVal 8 (SOff 20 0)))).
{ apply (chunk_ok_val tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (bv_unsigned (ew E 47)) 0x1c0 8 (SOff 20 0) len).
  - rewrite fsw_SOff0. exact E20.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia.
  - cbn [N.to_nat]. rewrite E47. exact Hval. }
split.
- clear - Hwf. vm_compute. reflexivity.
- split.
  + apply Forall_cons_iff in Hok as (Ok0 & Hok). apply Forall_cons_iff in Hok as (Ok1 & Hok).
    apply Forall_cons_iff in Hok as (Ok2 & Hok).
    apply Forall_cons; [exact Ok0|]. apply Forall_cons; [exact Ok1|]. apply Forall_cons; [|exact Hok].
    destruct Ok2 as (O1 & O2 & O3 & O4).
    unfold crt_frame_region in O1, O2, O3, O4 |- *.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in O1, O2, O3, O4 |- *.
    split; [exact O1|]. split; [exact O2|]. split; [exact O3|].
    unfold crtB0_csF11. apply Forall_cons; [exact HCH | exact O4].
  + cbn [pairwise_disjoint all_disjoint] in Hpd |- *.
    destruct Hpd as (D1 & D2 & D3 & D4).
    unfold crt_frame_region, YP09.extent_disjoint in D1, D2, D3 |- *.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi] in D1, D2, D3 |- *.
    split; [exact D1|]. split; [exact D2|]. split; [exact D3 | exact D4].
Qed.

(* the three-region start state of segment 11 (D1's crtD1_ss31_ok): the frame READ-ONLY with the length cell, the
   shadow region dropped, s6 re-seated on the frame atom (A: s11) *)
Lemma crtB0_ss11_ok : forall cx E (W : world tfibsegs) ms len,
  crt_E cx E -> 0 <= crt_F cx < 2 ^ 64 -> ew E 20 = Z_to_bv 64 len -> 0 <= len < 2 ^ 64 ->
  ew E 22 = Z_to_bv 64 (crt_F cx + 0x1c0) -> 0 <= crt_F cx + 0x1c0 < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (crt_F cx + 0x1c0) 8 len ->
  st_ok tfibsegs E (crt_ss_ret 0x821d4 crt_cs1 crt_csF) (restrict (w_H W) ms) ->
  st_ok tfibsegs E crtB0_ss11_base (restrict (w_H W) ms).
Proof.
intros cx E W ms len HE HF E20 Hlen E22 HF1c0 Hval HS.
assert (E47 : bv_unsigned (ew E 47) = crt_F cx)
  by (rewrite (crt_E_F cx E HE), Z_to_bv_unsigned, bv_wrap_small
        by (change (bv_modulus 64) with (2 ^ 64); lia); reflexivity).
pose proof (crtB0_add_ncell cx E W ms 0x821d4 len HE HF E20 Hlen Hval HS) as HS1.
assert (HSUB : submem [crt_s0_region; crt_slot_region crt_cs1; crtB0_fr_ro]
    (ss_mem (crt_ss_ret 0x821d4 crt_cs1 crtB0_csF11))).
{ cbn [ss_mem crt_ss_ret fss_ret_s0_args fss_ret_s0_regs crt_ret_regions].
  apply submem_keep; [apply subregion_refl|]. apply submem_keep; [apply subregion_refl|].
  apply submem_keep; [|apply submem_nil].
  unfold subregion, crtB0_fr_ro, crt_frame_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. intros c Hc. exact Hc. }
pose proof (st_ok_submem tfibsegs E _ _ _ HS1 HSUB ltac:(vm_compute; reflexivity)) as HS2.
assert (Q22 : sr_get (ss_regs (crt_ss_ret 0x821d4 crt_cs1 crt_csF)) 22%bv = SOff 22 0)
  by (vm_compute; reflexivity).
assert (R22a : YK11.getr (ms_regs (restrict (w_H W) ms)) 22%bv = ew E 22).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E (crt_ss_ret 0x821d4 crt_cs1 crt_csF) ms 22%bv HS), Q22.
  apply fsw_SOff0. }
assert (R22 : YK11.getr (ms_regs (restrict (w_H W) ms)) 22%bv = sv_denot E (SOff 47 0x1c0)).
{ rewrite R22a, E22. apply bv_eq. rewrite denot_SOff, E47.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
  symmetry. apply zcanon_id. unfold M64. lia. }
exact (YI08.st_ok_set_reg tfibsegs E _ _ 22%bv (SOff 47 0x1c0) HS2 ltac:(intros Hc; discriminate Hc) R22).
Qed.

(* fs's four allocator statics are image bytes below 0x5fd000, so a step that keeps every byte there keeps fs_glob
   (D1's crtD1_glob_keep) *)
Lemma crtB0_glob_keep : forall (W : world tfibsegs) (m m' : word -> option byte) live peak cnt fail,
  (forall a, 0 <= a < 0x5fd000 -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail Hk (G1 & G2 & G3 & G4 & R).
assert (HB4 : 0 <= G_FAIL /\ G_FAIL + 8 <= 0x5fd000 /\ 0 <= G_LIVE /\ G_LIVE + 8 <= 0x5fd000 /\
  0 <= G_PEAK /\ G_PEAK + 8 <= 0x5fd000 /\ 0 <= G_COUNT /\ G_COUNT + 8 <= 0x5fd000)
  by (unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT; repeat split; vm_compute; discriminate).
assert (VB : forall g v, 0 <= g -> g + 8 <= 0x5fd000 ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W) m') g 8 v).
{ intros g v Hg0 Hg1 Hv kk Hkk.
  assert (HA : 0 <= g + Z.of_nat kk < 0x5fd000) by lia.
  rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W) m m' (g + Z.of_nat kk) (Hk (g + Z.of_nat kk) HA)).
  exact (Hv kk Hkk). }
unfold fs_glob, fs_glob_at in *.
split; [apply VB; [lia | lia | exact G1]|]. split; [apply VB; [lia | lia | exact G2]|].
split; [apply VB; [lia | lia | exact G3]|]. split; [apply VB; [lia | lia | exact G4]|]. exact R.
Qed.

(* the run's read-only frame region has an empty write window (D1's crtD1_frame_ro) *)
Lemma crtB0_frame_ro : forall E (m m' : word -> option byte),
  frame_of E [crt_s0_region; crt_slot_region crt_cs1; crtB0_fr_ro] m m' ->
  frame_of E [crt_s0_region; crt_slot_region crt_cs1] m m'.
Proof.
intros E m m' HF x Hx. apply HF. intros (r & Hin & Hr). apply Hx.
destruct Hin as [<-|[<-|[<-|[]]]].
- exists crt_s0_region. split; [left; reflexivity | exact Hr].
- exists (crt_slot_region crt_cs1). split; [right; left; reflexivity | exact Hr].
- exfalso. unfold crtB0_fr_ro in Hr. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia.
Qed.

(* a region below alloc_ceiling holds on a memory that agrees below alloc_ceiling (D1's crtD1_region_below) *)
Lemma crtB0_region_below : forall E (H : word -> bool) (m m' : word -> option byte) r,
  same_below m m' alloc_ceiling -> YP09.region_wf r = true ->
  base_val E (YP09.r_base r) + YP09.r_hi r <= alloc_ceiling ->
  region_ok tfibsegs E (mrestrict H m) r -> region_ok tfibsegs E (mrestrict H m') r.
Proof.
intros E H m m' r Hs Hwf Hhi (R1 & R2 & R3 & R4).
apply region_wf_facts in Hwf as (W1 & W2 & W3).
split; [exact R1|]. split; [exact R2|]. split.
- intros o Ho. destruct W2 as [W2|W2]; [lia|].
  apply (fsw_writable_below H m m' _ Hs); [lia | exact (R3 o Ho)].
- rewrite Forall_forall in R4 |- *. intros c Hc.
  apply (chunk_ok_mbyte E (mrestrict H m)); [|exact (R4 c Hc)].
  rewrite forallb_forall in W3. pose proof (W3 c Hc) as Hin. unfold YP09.chunk_inside in Hin.
  rewrite !andb_true_iff, !Z.leb_le in Hin. destruct Hin as ((I1 & I2) & I3).
  intros i Hi. apply (mbyte_below H m m' alloc_ceiling); [exact Hs | lia].
Qed.

(* the run's write window over the three regions of segment 11's states (D1's crtD1_awr3) *)
Lemma crtB0_awr3 : forall cx E ly3 S3, crt_base B cx -> crt_E cx E ->
  awr_ok tfibsegs B E [crt_s0_region; crt_slot_region crt_cs1; crtB0_fr_ro] STK_check_round_trip
    (spZ (c_regs cx)) FS_PSTAT_FP (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(3, c_pos cx)]
    (frames (c_S cx)).
Proof.
intros cx E ly3 S3 HB HE a (r & Hin & Hr).
apply (crt_awr2 B cx E ly3 S3 HB HE). exists r. split; [|exact Hr].
destruct Hin as [<-|[<-|[<-|[]]]]; [left; reflexivity | right; left; reflexivity |].
exfalso. unfold crtB0_fr_ro in Hr. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia.
Qed.

(* a callee-saved register of the env resumed after a call is the call site's value (D1's crtD1_keep_sv) *)
Lemma crtB0_keep_sv : forall E ss (H : word -> bool) ms regs2 extra (q : nat) v,
  st_ok tfibsegs E ss (restrict H ms) -> aregs_preserved (ms_regs ms) regs2 ->
  acallee_saved (Z.of_nat q) -> (q < 32)%nat ->
  sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat q)) = v ->
  ew (Ereg regs2 extra) q = sv_denot E v.
Proof.
intros E ss H ms regs2 extra q v HS HP Hq Hq32 Hr.
rewrite (ew_Ereg_lt regs2 extra q Hq32), (HP _ Hq), (st_ok_restrict_reg tfibsegs H E ss ms _ HS), Hr.
reflexivity.
Qed.

(* ---- a Theorem Labs lane's boundary re-entry (a23_reseat / a23_reenter): crt_ss_ret has every register on its own atom, so a
   boundary is re-entered by re-seating the env on the machine's register file and rebuilding the four regions ---- *)
Lemma crtB0_reseat : forall cx E k ly' S' U' (W' : world tfibsegs) regs' mem' md' r cs1 csF,
  crt_E cx E -> spZ (c_regs cx) mod 16 = 0 -> 192 <= spZ (c_regs cx) ->
  alloc_ceiling + STK_check_round_trip <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly' S' W' (unpoison U' mem') md' k ->
  ARU tfibsegs B ly' S' U' W' mem' md' ->
  In (3, c_pos cx) (frames S') ->
  YK11.getr regs' 2%bv = Z_to_bv 64 (crt_sp1 cx) ->
  YK11.getr regs' 3%bv = YK11.getr (c_regs cx) 3%bv ->
  YK11.getr regs' 4%bv = YK11.getr (c_regs cx) 4%bv ->
  YK11.getr regs' 8%bv = Z_to_bv 64 (spZ (c_regs cx)) ->
  YK11.getr regs' 9%bv = Z_to_bv 64 (crt_sp1 cx) ->
  YK11.getr regs' 26%bv = Z_to_bv 64 (crt_SF cx) ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W') mem') (spZ (c_regs cx))) crt_sv_chunks ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W') mem') (crt_sp1 cx)) cs1 ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W') mem') (crt_F cx)) csF ->
  Forall (fun c => 0x10 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= 0x58) cs1 ->
  Forall (fun c => 0 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= fs_frame_bytes 3) csF ->
  crt_atom_chunks cs1 -> crt_atom_chunks csF ->
  YP09.region_wf (crt_slot_region cs1) = true -> YP09.region_wf (crt_frame_region csF) = true ->
  crt_E cx (Ereg regs' (crt_extra cx)) /\
  st_ok tfibsegs (Ereg regs' (crt_extra cx)) (crt_ss_ret r cs1 csF)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros cx E k ly' S' U' W' regs' mem' md' r cs1 csF HE H16 H0 Hsp0 Hsp47 HJ2 HARU' Hin3' R2 R3 R4 R8 R9 R26
  HSV HCS1 HCSF HcsF1in HcsFin HcsF1at HcsFat HWF1 HWFF.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof crt_STK_eq as HSTKv; unfold crt_STK in HSTKv.
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
pose proof (fsw_realign_facts (spZ (c_regs cx) - 192) ltac:(lia)
  ltac:(rewrite Zminus_mod, H16; reflexivity)) as ((Flo & Fhi) & Fm32 & Fm16).
assert (Hsp1lo : spZ (c_regs cx) - 208 <= crt_sp1 cx) by (unfold crt_sp1; lia).
assert (Hsp1hi : crt_sp1 cx <= spZ (c_regs cx) - 192) by (unfold crt_sp1; lia).
pose proof HJ2 as (HAR' & Hly' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & Hstk2 & _).
destruct Hstk2 as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Efr' : frame_addr ly' 3 (c_pos cx) = crt_F cx).
{ unfold crt_F, frame_addr. destruct Hly' as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (frames_bounds tfibsegs B LAWS ly' S' W' (unpoison U' mem') md' 3 (c_pos cx) HAR' Hin3')
  as (HF0 & HFc & HFapp).
rewrite Efr' in HF0, HFc, HFapp. rewrite crt_frame3 in HFc, HFapp.
assert (HFrng : 0 <= crt_F cx < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds (crt_F cx) HFrng) as (HS1b & HS2b).
destruct (al_frames _ _ LAWS ly' S' W' (unpoison U' mem') md' 3 (c_pos cx) HAR' Hin3')
  as (Hal32' & Happ' & Hfp' & Hsp').
rewrite Efr' in Hal32', Hfp', Hsp'. rewrite crt_frame3 in Hfp', Hsp'. change (512 / 8) with 64 in Hsp'.
assert (HSFlo : 2147450880 <= crt_SF cx) by (unfold crt_SF; rewrite C5 in HS1b; lia).
assert (HSFhi : crt_SF cx < 17594333495296) by (unfold crt_SF; rewrite C2 in HS2b; lia).
set (E' := Ereg regs' (crt_extra cx)) in *.
assert (HE' : crt_E cx E').
{ subst E'. apply crt_E_Ereg.
  - rewrite R2. apply wz. lia.
  - exact R3.
  - exact R4.
  - rewrite R8. apply wz. unfold spZ. apply u64_range.
  - rewrite R9. apply wz. lia.
  - rewrite R26. apply wz. lia. }
assert (Hag : forall n, (32 <= n < 51)%nat -> ew E' n = ew E n) by exact (crt_env_agree cx E E' HE HE').
assert (E9v : bv_unsigned (ew E' 9) = crt_sp1 cx) by (destruct HE' as (_ & _ & _ & _ & H & _); exact H).
assert (E8v : bv_unsigned (ew E' 8) = spZ (c_regs cx)) by (destruct HE' as (_ & _ & _ & H & _); exact H).
assert (E26v : bv_unsigned (ew E' 26) = crt_SF cx) by (destruct HE' as (_ & _ & _ & _ & _ & H & _); exact H).
assert (E47v : bv_unsigned (ew E' 47) = crt_F cx) by (rewrite (crt_E_F cx E' HE'); apply wz; lia).
assert (ROslot : region_ok tfibsegs E' (mrestrict (w_H W') mem') (crt_slot_region cs1)).
{ unfold region_ok, crt_slot_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9v.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B ly' S' U' W' mem' md' _ HARU'); [lia|]. apply Hpres2. lia.
  - eapply crt_chunks_env; [exact Hag | exact HcsF1at | exact HCS1]. }
assert (ROshadow : region_ok tfibsegs E' (mrestrict (w_H W') mem') crt_shadow_region).
{ unfold region_ok, crt_shadow_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E26v.
  split; [lia|]. split; [rewrite crt_frame3; cbn [Z.div]; lia|].
  split; [|apply Forall_nil].
  intros o Ho. rewrite crt_frame3 in Ho. change (512 / 8) with 64 in Ho.
  apply (apresent_writable tfibsegs). destruct (Hsp' o ltac:(lia)) as (Hp & Hno).
  apply (fsw_apresent_notowned B ly' S' U' W' mem' md' _ HARU'); [lia | exact Hno | exact Hp]. }
assert (ROframe : region_ok tfibsegs E' (mrestrict (w_H W') mem') (crt_frame_region csF)).
{ unfold region_ok, crt_frame_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E47v.
  split; [lia|]. split; [rewrite crt_frame3; lia|]. split.
  - intros o Ho. rewrite crt_frame3 in Ho.
    apply (apresent_writable tfibsegs). destruct (Hfp' (crt_F cx + o) ltac:(lia)) as (Hp & Hno).
    apply (fsw_apresent_notowned B ly' S' U' W' mem' md' _ HARU'); [lia | exact Hno | exact Hp].
  - eapply crt_chunks_env; [exact Hag | exact HcsFat | exact HCSF]. }
assert (Hceil1 : alloc_ceiling <= crt_sp1 cx) by lia.
assert (Dfs : crt_F cx + 512 <= crt_SF cx \/ crt_SF cx + 64 <= crt_F cx).
{ unfold in_app in HFapp. destruct HFapp as (_ & [Hlow | (Hhigh & _)]).
  - left. unfold kLowShadowBeg in *. lia.
  - right. unfold crt_SF, shadow_addr, SHADOW_OFF, kHighMemBeg in *.
    Z.div_mod_to_equations. lia. }
split; [exact HE'|].
unfold crt_ss_ret.
eapply (fsw_resume_after_rtU_s0 B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
  (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly' S' U' W' mem' md' k regs' mem'
  (crt_extra cx) crt_sv_chunks (crt_ret_regions cs1 csF) crt_ret_facts r (-104) 0).
- exact HJ2.
- exact HARU'.
- exact R8.
- lia.
- lia.
- lia.
- unfold fss_ret_s0_regs, crt_ret_regions, regions_wf. cbn [forallb andb].
  rewrite HWFF, HWF1. cbn [andb]. vm_compute (YP09.region_wf crt_s0_region).
  vm_compute (YP09.region_wf crt_shadow_region). rewrite !andb_true_r. reflexivity.
- exact crt_sv_in.
- eapply crt_chunks_env; [exact Hag | exact crt_sv_atoms | exact HSV].
- intros a Ha. reflexivity.
- unfold crt_ret_regions. constructor; [exact ROslot|]. constructor; [exact ROframe|].
  constructor; [exact ROshadow | apply Forall_nil].
- apply pairwise_disjoint_of_extents.
  unfold fss_ret_s0_regs, crt_ret_regions, crt_slot_region, crt_frame_region, crt_shadow_region, crt_s0_region,
    fs_ret_s0_region.
  cbn [map]. unfold extent_of_region, base_val. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
  fold E'. rewrite E8v, E9v, E47v, E26v. rewrite !crt_frame3. change (512 / 8) with 64.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; try exact I;
    first [right; lia | left; lia | destruct Dfs as [Hd|Hd]; [left; lia | right; lia]].
- unfold crt_ret_facts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E'.
  rewrite E9v, E47v. change (2 ^ 5) with 32.
  split; [split; [lia | split; [exact Fm32 | lia]]|].
  split; [|exact I]. split; [lia | split; [exact Hal32' | lia]].
Qed.

(* the sp facts of the walk, from crt_base alone (a Theorem Labs lane's a23_spf) *)
Lemma crtB0_spf : forall cx, crt_base B cx ->
  spZ (c_regs cx) mod 16 = 0 /\ 192 <= spZ (c_regs cx) /\
  alloc_ceiling + STK_check_round_trip <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47.
Proof.
intros cx HB. pose proof HB as (HPRE & _).
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPRE)) as (Hal16 & Hceil0 & H47 & _).
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
pose proof crt_STK_eq as HSTKv; unfold crt_STK in HSTKv.
split; [exact Hal16|]. split; [lia|]. split; [lia | exact H47].
Qed.

(* the boundary at the stop pc of a run, rebuilt from the engine's state (a Theorem Labs lane's a23_reenter) *)
Lemma crtB0_reenter : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms mdC ssC r1 cs1' csP,
  crt_base B cx -> crt_E cx E ->
  st_ok tfibsegs E ssC (restrict (w_H W3) ms) -> ss_pc ssC = r1 -> ss_resv ssC = None ->
  nth_error (ss_mem ssC) 0 = Some crt_s0_region ->
  nth_error (ss_mem ssC) 1 = Some (crt_slot_region csP) ->
  incl cs1' csP ->
  Forall (fun c => 0x10 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= 0x58) cs1' ->
  crt_atom_chunks cs1' -> YP09.region_wf (crt_slot_region cs1') = true ->
  sr_get (ss_regs ssC) 2%bv = SOff 2 0 -> sr_get (ss_regs ssC) 3%bv = SOff 3 0 ->
  sr_get (ss_regs ssC) 4%bv = SOff 4 0 -> sr_get (ss_regs ssC) 8%bv = SOff 8 0 ->
  sr_get (ss_regs ssC) 9%bv = SOff 9 0 -> sr_get (ss_regs ssC) 26%bv = SOff 26 0 ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (crt_F cx)) crt_csF ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms)) mdC k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) mdC ->
  In (3, c_pos cx) (frames S3) ->
  crt_E cx (Ereg (ms_regs ms) (crt_extra cx)) /\
  st_ok tfibsegs (Ereg (ms_regs ms) (crt_extra cx)) (crt_ss_ret r1 cs1' crt_csF) (restrict (w_H W3) ms).
Proof.
intros cx E k ly3 S3 U3 W3 ms mdC ssC r1 cs1' csP HB HE HS Hpc Hres H0r H1r Hincl Hin1 Hat1 Hwf1
  G2 G3 G4 G8 G9 G26 HCSF HJ HARU Hin3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
pose proof crt_STK_eq as HSTKv; unfold crt_STK in HSTKv.
destruct (crtB0_spf cx HB) as (H16 & H0 & Hceil0 & H47).
destruct (crt_sp1_facts cx H16 H0) as (Hsp1 & _ & _).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
assert (RG : forall q : bv 5, YK11.getr (ms_regs ms) q = sv_denot E (sr_get (ss_regs ssC) q))
  by (intros q; exact (st_ok_restrict_reg tfibsegs (w_H W3) E ssC ms q HS)).
assert (V : forall n z, bv_unsigned (ew E n) = z -> 0 <= z < 2 ^ 64 -> ew E n = Z_to_bv 64 z)
  by (intros n z Hz Hr64; apply bv_eq; rewrite Hz; symmetry; apply wz; exact Hr64).
assert (R2 : YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 (crt_sp1 cx))
  by (rewrite RG, G2, fsw_SOff0; apply V; [exact E2 | lia]).
assert (R3 : YK11.getr (ms_regs ms) 3%bv = YK11.getr (c_regs cx) 3%bv)
  by (rewrite RG, G3, fsw_SOff0; exact E3).
assert (R4 : YK11.getr (ms_regs ms) 4%bv = YK11.getr (c_regs cx) 4%bv)
  by (rewrite RG, G4, fsw_SOff0; exact E4).
assert (R8 : YK11.getr (ms_regs ms) 8%bv = Z_to_bv 64 (spZ (c_regs cx)))
  by (rewrite RG, G8, fsw_SOff0; apply V; [exact E8 | unfold spZ; apply u64_range]).
assert (R9 : YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 (crt_sp1 cx))
  by (rewrite RG, G9, fsw_SOff0; apply V; [exact E9 | lia]).
assert (R26 : YK11.getr (ms_regs ms) 26%bv = Z_to_bv 64 (crt_SF cx))
  by (rewrite RG, G26, fsw_SOff0; apply V; [exact E26 | pose proof (u64_range (ew E 26)); lia]).
assert (HR0 : region_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) crt_s0_region)
  by exact (fsw_region_nth E ssC (restrict (w_H W3) ms) 0 crt_s0_region HS H0r).
assert (HRs : region_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (crt_slot_region csP))
  by exact (fsw_region_nth E ssC (restrict (w_H W3) ms) 1 (crt_slot_region csP) HS H1r).
assert (HSV : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (spZ (c_regs cx))) crt_sv_chunks).
{ destruct HR0 as (_ & _ & _ & Hc). cbn [crt_s0_region fs_ret_s0_region YP09.r_base YP09.r_chunks base_val] in Hc.
  rewrite E8 in Hc. exact Hc. }
assert (HCS1 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (crt_sp1 cx)) cs1').
{ destruct HRs as (_ & _ & _ & Hc). cbn [crt_slot_region YP09.r_base YP09.r_chunks base_val] in Hc.
  rewrite E9 in Hc. rewrite Forall_forall in Hc |- *. intros c Hc'. exact (Hc c (Hincl c Hc')). }
assert (HcsFin : Forall (fun c => 0 <= YP09.c_off c /\ 0 <= YP09.c_len c /\
    YP09.c_off c + YP09.c_len c <= fs_frame_bytes 3) crt_csF)
  by (unfold crt_csF; rewrite crt_frame3; apply Forall_cons; [cbn; lia | apply Forall_nil]).
assert (HcsFat : crt_atom_chunks crt_csF)
  by (unfold crt_atom_chunks, crt_csF; apply Forall_cons; [do 4 eexists; split; [reflexivity | lia] | apply Forall_nil]).
assert (HwfF : YP09.region_wf (crt_frame_region crt_csF) = true) by (vm_compute; reflexivity).
pose proof (crt_mkst (w_H W3) E ssC ms HS Hres) as Ems. rewrite Hpc in Ems.
destruct (crtB0_reseat cx E k ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) mdC r1 cs1' crt_csF
  HE H16 H0 Hceil0 H47 HJ HARU Hin3 R2 R3 R4 R8 R9 R26 HSV HCS1 HCSF Hin1 HcsFin Hat1 HcsFat Hwf1 HwfF)
  as (HE' & HS').
split; [exact HE'|]. rewrite Ems at 2. exact HS'.
Qed.
End h.

(* ---- the bcmp call and the boundary rebuilt after it (D1's FSH_crt_segD1_bcmp.v, renamed): crt_bcmp_call with the
   contract's md relation and raw-memory frame clause handed to the continuation; the walk's boundary state at the
   return r; and the call as a callee journal with an empty footprint ---- *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SKfp : YI16.sink_head}.
Variable B : asyms.

Lemma crtB0_bcmp_call : forall (ss : sstate) (r : Z) (na : nat) cx E k ly3 S3 U3 (W3 : world tfibsegs) regsT memT mdT got
  (Q : world tfibsegs -> config -> Prop),
  sr_get (ss_regs ss) 1%bv = SLit r -> 0 <= r < 2 ^ 64 -> sr_get (ss_regs ss) 10%bv = SOff na 0 ->
  sr_get (ss_regs ss) 11%bv = SOff 21 0 -> sr_get (ss_regs ss) 12%bv = SOff 20 0 ->
  sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
  YK0s.ret_ok (Z_to_bv 64 r) ->
  CrtRt B ->
  crt_E cx E -> spZ (c_regs cx) mod 16 = 0 -> 192 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  YK11.getr (c_regs cx) 3%bv = w64 (as_gp B) -> YK11.getr (c_regs cx) 4%bv = w64 (as_tp B) ->
  st_ok tfibsegs E ss (restrict (w_H W3) (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs))) ->
  let len := Z.of_nat (length (c_bs cx)) in
  bv_unsigned (ew E na) = got -> bv_unsigned (ew E 21) = c_bd cx -> bv_unsigned (ew E 20) = len ->
  0 <= len < 2 ^ 32 -> 0 <= got -> got + len <= 2 ^ 63 -> 0 <= c_bd cx -> c_bd cx + len <= 2 ^ 63 ->
  src_ok tfibsegs W3 regsT memT got len -> src_ok tfibsegs W3 regsT memT (c_bd cx) len ->
  (forall a, got <= a < got + len -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) ->
  (forall a, c_bd cx <= a < c_bd cx + len -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) ->
  amem_range got len -> amem_range (c_bd cx) len ->
  range_addressable (aview tfibsegs (w_H W3) memT) SHADOW_OFF got len ->
  (0 < len -> shadow_hull_vis (aview tfibsegs (w_H W3) memT) got len) ->
  range_addressable (aview tfibsegs (w_H W3) memT) SHADOW_OFF (c_bd cx) len ->
  (0 < len -> shadow_hull_vis (aview tfibsegs (w_H W3) memT) (c_bd cx) len) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 memT) mdT k ->
  ARU tfibsegs B ly3 S3 U3 W3 memT mdT ->
  (forall regs2 mem2 md2 (v : word),
     ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
       (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 mem2) md2 k ->
     ARU tfibsegs B ly3 S3 U3 W3 mem2 md2 ->
     same_but_materialized mdT md2 ->
     aregs_preserved regsT regs2 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
        aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) memT a) ->
     YK11.getr regs2 10%bv = v ->
     (v = w64 0 <-> forall i, 0 <= i < len ->
        aview tfibsegs (w_H W3) memT (got + i) = aview tfibsegs (w_H W3) memT (c_bd cx + i)) ->
     SRr tfibsegs W3 (mkCfg (mkst regs2 (YK11.getr regsT 1%bv) mem2 (seg_rom tfibsegs)) md2) Q) ->
  SRr tfibsegs W3 (mkCfg (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)) mdT) Q.
Proof.
intros ss r na cx E k ly3 S3 U3 W3 regsT memT mdT got Q Sr1 Hr Sr10 Sr11 Sr12 Sr2 Sr3 Sr4 HRet RT HE H16 H0 H47 Hgp Htp HS len Eg Ebd Elen Hl Hg0 Hg1 Hb0 Hb1
  Hsg Hsb Hwg Hwb Hmg Hmb Hag Hhg Hab Hhb HJ HARU K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (crt_sp1_facts cx H16 H0) as (Hsp1b & Hsp1_32 & Hsp1_16).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & Eex).
assert (HSTK : 17000 <= STK_check_round_trip) by (vm_compute; discriminate).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & Hh47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & _).
assert (Rd : forall (q : bv 5) n, sr_get (ss_regs ss) q = SOff n 0 -> YK11.getr regsT q = ew E n).
{ intros q n Hq. pose proof (st_ok_restrict_reg tfibsegs (w_H W3) E ss
    (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)) q HS) as X.
  cbn [ms_regs mkst] in X. rewrite X, Hq. apply fsw_SOff0. }
assert (G10 : YK11.getr regsT 10%bv = w64 got).
{ rewrite (Rd 10%bv na Sr10). unfold w64. rewrite <- Eg. symmetry. apply Z_to_bv_bv_unsigned. }
assert (G11 : YK11.getr regsT 11%bv = w64 (c_bd cx)).
{ rewrite (Rd 11%bv _ Sr11). unfold w64. rewrite <- Ebd. symmetry. apply Z_to_bv_bv_unsigned. }
assert (G12 : YK11.getr regsT 12%bv = w64 len).
{ rewrite (Rd 12%bv _ Sr12). unfold w64. rewrite <- Elen. symmetry. apply Z_to_bv_bv_unsigned. }
assert (G3 : YK11.getr regsT 3%bv = w64 (as_gp B)) by (rewrite (Rd 3%bv _ Sr3), E3; exact Hgp).
assert (G4 : YK11.getr regsT 4%bv = w64 (as_tp B)) by (rewrite (Rd 4%bv _ Sr4), E4; exact Htp).
assert (GSP : spZ regsT = crt_sp1 cx) by (unfold spZ; rewrite (Rd 2%bv _ Sr2); exact E2).
assert (G1 : YK11.getr regsT 1%bv = Z_to_bv 64 r).
{ exact (fsw_reg_lit (w_H W3) E ss (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)) 1%bv r HS Sr1 Hr). }
assert (Hra : YK0s.ret_ok (YK11.getr regsT 1%bv)) by (rewrite G1; exact HRet).
assert (HPRE : FSupoison.ecall_preU tfibsegs B ly3 S3 U3 W3 regsT memT mdT).
{ eapply (fsw_ecall_preU_at B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 W3 memT mdT k regsT
    (crt_sp1 cx - spZ (c_regs cx)) HJ HARU);
  [lia | rewrite Zminus_mod, H16, Hsp1_16; reflexivity | lia | unfold ESTACK; lia | exact Hra | exact G3
  | exact G4]. }
assert (HSK1 : ly_stk_lo ly3 + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, GSP; unfold ESTACK; lia).
assert (HSK2 : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W3) memT a).
{ intros a Ha. rewrite GSP in Ha. unfold ESTACK in Ha.
  apply (fsw_apresent_unpoison B ly3 S3 U3 W3 memT mdT a HARU); [unfold kHighMemBeg in *; lia|].
  apply Hpres. lia. }
pose proof (crt_fr_bcmp B RT ly3 S3 U3 W3 regsT memT mdT got (c_bd cx) len HPRE HSK1 HSK2 G10 G11 G12 Hl Hg0 Hg1 Hb0 Hb1
  Hsg Hsb Hwg Hwb Hmg Hmb Hag Hhg Hab Hhb) as HC.
change (cfg_at tfibsegs PC_bcmp regsT memT mdT) with
  (mkCfg (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)) mdT) in HC.
eapply SRr_bind.
{ eapply (fsw_intrin_atU B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 W3 memT mdT k U3
    (fun a => spZ regsT - 2 * ESTACK <= a < spZ regsT) (YK11.getr regsT 1%bv) _
    (fun regs' mem' md' => same_but_materialized mdT md' /\ aregs_preserved regsT regs' /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
          aview tfibsegs (w_H W3) mem' a = aview tfibsegs (w_H W3) memT a) /\
       exists v : word, YK11.getr regs' 10%bv = v /\
       (v = w64 0 <-> forall i, 0 <= i < len ->
          aview tfibsegs (w_H W3) memT (got + i) = aview tfibsegs (w_H W3) memT (c_bd cx + i))) HJ).
  - eapply SRr_mono; [exact HC|].
    intros W' c' _ (-> & regs' & mem' & md' & v & Ec & HARU' & HP & Hsame & Hv & Hres & Hfr & Hgr).
    split; [reflexivity|]. exists regs', mem', md'.
    split; [rewrite Ec; unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
    split; [exact HARU'|]. split; [exact Hsame|].
    split; [exact (crt_unpoison_keep (w_H W3) U3 memT mem' _ Hfr)|].
    split; [exact (crt_unpoison_present (w_H W3) U3 memT mem' Hgr)|].
    split; [exact Hsame|]. split; [exact HP|]. split; [exact Hfr|]. exists v. split; [exact Hv | exact Hres].
  - intros a Ha. left. left. rewrite GSP in Ha. unfold ESTACK in Ha. lia. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HSM2 & HP2 & HFR2 & v & Hv & Hres).
exact (K regs2 mem2 md2 v HJ2 HARU2 HSM2 HP2 HFR2 Hv Hres).
Qed.

Lemma crtB0_bcmp_resume : forall cx E (ss : sstate) k ly3 S3 U3 (W3 : world tfibsegs) regsT memT regs2 mem2 md2 csF r,
  crt_E cx E ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 mem2) md2 k ->
  ARU tfibsegs B ly3 S3 U3 W3 mem2 md2 ->
  crt_frame_ok cx S3 W3 (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)) ->
  st_ok tfibsegs E ss (restrict (w_H W3) (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs))) ->
  ss_mem ss = ss_mem (crt_ss_ret 0 crt_cs1 csF) ->
  map (fun q => sr_get (ss_regs ss) q) [2; 3; 4; 8; 9; 26]%bv =
    [SOff 2 0; SOff 3 0; SOff 4 0; SOff 8 0; SOff 9 0; SOff 26 0] ->
  aregs_preserved regsT regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
     aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) memT a) ->
  Forall (fun c => 0 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= fs_frame_bytes 3) csF ->
  crt_atom_chunks csF ->
  crt_E cx (Ereg regs2 (crt_extra cx)) /\
  crt_frame_ok cx S3 W3 (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs)) /\
  st_ok tfibsegs (Ereg regs2 (crt_extra cx)) (crt_ss_ret r crt_cs1 csF)
    (restrict (w_H W3) (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs))).
Proof.
intros cx E ss k ly3 S3 U3 W3 regsT memT regs2 mem2 md2 csF r
  HE HJ HARU HFR HS Hmem Hrg HP Hfr HcsFin HcsFat.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (HSTK : 17000 <= STK_check_round_trip) by (vm_compute; discriminate).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (H0 : 192 <= spZ (c_regs cx)) by lia.
destruct (crt_sp1_facts cx Hal16 H0) as (Hsp1b & Fm32 & _).
destruct HFR as (Hfrs & Hnotin & Hflag).
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
cbn [map] in Hrg. injection Hrg as R2 R3 R4 R8 R9 R26.
assert (Rd : forall (q : bv 5) n, sr_get (ss_regs ss) q = SOff n 0 -> YK11.getr regsT q = ew E n).
{ intros q n Hq. pose proof (st_ok_restrict_reg tfibsegs (w_H W3) E ss
    (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)) q HS) as X.
  cbn [ms_regs mkst] in X. rewrite X, Hq. apply fsw_SOff0. }
assert (G : forall (q : Z) n, acallee_saved q -> sr_get (ss_regs ss) (Z_to_bv 5 q) = SOff n 0 ->
  YK11.getr regs2 (Z_to_bv 5 q) = ew E n).
{ intros q n Hq Hs. rewrite (HP q Hq). exact (Rd _ n Hs). }
assert (G2 : YK11.getr regs2 2%bv = ew E 2) by exact (G 2 2%nat ltac:(unfold acallee_saved; lia) R2).
assert (G3 : YK11.getr regs2 3%bv = ew E 3) by exact (G 3 3%nat ltac:(unfold acallee_saved; lia) R3).
assert (G4 : YK11.getr regs2 4%bv = ew E 4) by exact (G 4 4%nat ltac:(unfold acallee_saved; lia) R4).
assert (G8 : YK11.getr regs2 8%bv = ew E 8) by exact (G 8 8%nat ltac:(unfold acallee_saved; lia) R8).
assert (G9 : YK11.getr regs2 9%bv = ew E 9) by exact (G 9 9%nat ltac:(unfold acallee_saved; lia) R9).
assert (G26 : YK11.getr regs2 26%bv = ew E 26) by exact (G 26 26%nat ltac:(unfold acallee_saved; lia) R26).
assert (SPT : spZ regsT = crt_sp1 cx) by (unfold spZ; rewrite (Rd 2%bv 2%nat R2); exact E2).
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
pose proof (crt_F_ly cx _ ly3 Hly) as EF.
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 (unpoison U3 mem2) md2 3 (c_pos cx) HAR Hin3) as (HF0 & HFc & HFapp).
rewrite EF in HF0, HFc, HFapp. rewrite crt_frame3 in HFc, HFapp.
destruct (al_frames _ _ LAWS ly3 S3 W3 (unpoison U3 mem2) md2 3 (c_pos cx) HAR Hin3) as (Hal32 & _ & Hfp & Hsp).
rewrite EF in Hal32, Hfp, Hsp. rewrite crt_frame3 in Hfp, Hsp. change (512 / 8) with 64 in Hsp.
assert (HFrng : 0 <= crt_F cx < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds (crt_F cx) HFrng) as (HS1b & HS2b).
assert (HSFlo : 2147450880 <= crt_SF cx) by (unfold crt_SF; rewrite C5 in HS1b; lia).
assert (HSFhi : crt_SF cx < 17594333495296) by (unfold crt_SF; rewrite C2 in HS2b; lia).
assert (Dfs : crt_F cx + 512 <= crt_SF cx \/ crt_SF cx + 64 <= crt_F cx).
{ unfold in_app in HFapp. destruct HFapp as (_ & [Hlow | (Hhigh & _)]).
  - left. unfold kLowShadowBeg in *. lia.
  - right. unfold crt_SF, shadow_addr, SHADOW_OFF, kHighMemBeg in *.
    Z.div_mod_to_equations. lia. }
assert (Hceil1 : alloc_ceiling + 2 * ESTACK <= crt_sp1 cx) by (unfold ESTACK; lia).
assert (E9v : bv_unsigned (ew E' 9) = crt_sp1 cx) by (destruct HE' as (_ & _ & _ & _ & X & _); exact X).
assert (E8v : bv_unsigned (ew E' 8) = spZ (c_regs cx)) by (destruct HE' as (_ & _ & _ & X & _); exact X).
assert (E26v : bv_unsigned (ew E' 26) = crt_SF cx) by (destruct HE' as (_ & _ & _ & _ & _ & X & _); exact X).
assert (E47v : bv_unsigned (ew E' 47) = crt_F cx) by (rewrite (crt_E_F cx E' HE'); apply wz; lia).
assert (E47 : bv_unsigned (ew E 47) = crt_F cx) by (rewrite (crt_E_F cx E HE); apply wz; lia).
assert (Hk : forall a, 0 <= a < 2 ^ 64 -> ~ (crt_sp1 cx - 2 * ESTACK <= a < crt_sp1 cx) ->
  mbyte tfibsegs (mrestrict (w_H W3) mem2) a = mbyte tfibsegs (mrestrict (w_H W3) memT) a).
{ intros a Ha Hw. apply (mbyte_of_aview tfibsegs (w_H W3) (w_H W3)). apply Hfr; [exact Ha|]. rewrite SPT. exact Hw. }
assert (Hnth : forall i rg, nth_error (ss_mem (crt_ss_ret 0 crt_cs1 csF)) i = Some rg ->
  region_ok tfibsegs E (mrestrict (w_H W3) memT) rg).
{ intros i rg Hi. rewrite <- Hmem in Hi. exact (fsw_region_nth E ss _ i rg HS Hi). }
assert (HSV : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (spZ (c_regs cx))) crt_sv_chunks).
{ pose proof (Hnth 0%nat (fs_ret_s0_region (-104) 0 crt_sv_chunks) eq_refl) as (_ & _ & _ & X).
  unfold fs_ret_s0_region in X. cbn [YP09.r_base YP09.r_chunks base_val] in X. rewrite E8 in X. exact X. }
assert (HCS1 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (crt_sp1 cx)) crt_cs1).
{ pose proof (Hnth 1%nat (crt_slot_region crt_cs1) eq_refl) as (_ & _ & _ & X).
  unfold crt_slot_region in X. cbn [YP09.r_base YP09.r_chunks base_val] in X. rewrite E9 in X. exact X. }
assert (HCSF : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (crt_F cx)) csF).
{ pose proof (Hnth 2%nat (crt_frame_region csF) eq_refl) as (_ & _ & _ & X).
  unfold crt_frame_region in X. cbn [YP09.r_base YP09.r_chunks base_val] in X. rewrite E47 in X. exact X. }
assert (ROslot : region_ok tfibsegs E' (mrestrict (w_H W3) mem2) (crt_slot_region crt_cs1)).
{ unfold region_ok, crt_slot_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9v.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B ly3 S3 U3 W3 mem2 md2 _ HARU); [unfold kHighMemBeg in *; lia|].
    apply Hpres. lia.
  - assert (H1 : Forall (YP09.chunk_ok tfibsegs E' (mrestrict (w_H W3) memT) (crt_sp1 cx)) crt_cs1)
      by (eapply crt_chunks_env; [exact Hag | exact crt_cs1_atoms | exact HCS1]).
    pose proof crt_cs1_in as Hin1. rewrite Forall_forall in H1, Hin1 |- *. intros c Hc.
    apply (chunk_ok_mbyte E' (mrestrict (w_H W3) memT)); [|exact (H1 c Hc)].
    intros i Hi. destruct (Hin1 c Hc) as (Ho1 & Ho2 & Ho3).
    apply Hk; [lia | unfold ESTACK; lia]. }
assert (ROshadow : region_ok tfibsegs E' (mrestrict (w_H W3) mem2) crt_shadow_region).
{ unfold region_ok, crt_shadow_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E26v.
  split; [lia|]. split; [rewrite crt_frame3; cbn [Z.div]; lia|].
  split; [|apply Forall_nil].
  intros o Ho. rewrite crt_frame3 in Ho. change (512 / 8) with 64 in Ho.
  apply (apresent_writable tfibsegs). destruct (Hsp o ltac:(lia)) as (Hp & Hno).
  apply (fsw_apresent_notowned B ly3 S3 U3 W3 mem2 md2 _ HARU); [lia | exact Hno | exact Hp]. }
assert (ROframe : region_ok tfibsegs E' (mrestrict (w_H W3) mem2) (crt_frame_region csF)).
{ unfold region_ok, crt_frame_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E47v.
  split; [lia|]. split; [rewrite crt_frame3; lia|]. split.
  - intros o Ho. rewrite crt_frame3 in Ho.
    apply (apresent_writable tfibsegs). destruct (Hfp (crt_F cx + o) ltac:(lia)) as (Hp & Hno).
    apply (fsw_apresent_notowned B ly3 S3 U3 W3 mem2 md2 _ HARU); [lia | exact Hno | exact Hp].
  - assert (H1 : Forall (YP09.chunk_ok tfibsegs E' (mrestrict (w_H W3) memT) (crt_F cx)) csF)
      by (eapply crt_chunks_env; [exact Hag | exact HcsFat | exact HCSF]).
    pose proof HcsFin as Hin1. rewrite Forall_forall in H1, Hin1 |- *. intros c Hc.
    apply (chunk_ok_mbyte E' (mrestrict (w_H W3) memT)); [|exact (H1 c Hc)].
    intros i Hi. destruct (Hin1 c Hc) as (Ho1 & Ho2 & Ho3). rewrite crt_frame3 in Ho3.
    apply Hk; lia. }
assert (WFframe : YP09.region_wf (crt_frame_region csF) = true).
{ unfold YP09.region_wf, crt_frame_region. cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite !andb_true_iff. split; [split|].
  - apply Z.leb_le. rewrite crt_frame3. lia.
  - apply orb_true_iff. right. rewrite !andb_true_iff. split; apply Z.leb_le; lia.
  - apply forallb_forall. intros c Hc. pose proof HcsFin as Hin1. rewrite Forall_forall in Hin1.
    destruct (Hin1 c Hc) as (Ho1 & Ho2 & Ho3). unfold YP09.chunk_inside.
    cbn [YP09.r_lo YP09.r_hi]. rewrite !andb_true_iff. split; [split|]; apply Z.leb_le; lia. }
assert (HS4 : st_ok tfibsegs E' (crt_ss_ret r crt_cs1 csF)
  (restrict (w_H W3) (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs)))).
{ unfold crt_ss_ret.
  eapply (fsw_resume_after_rtU_s0 B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 W3 mem2 md2 k regs2 memT
    (crt_extra cx) crt_sv_chunks (crt_ret_regions crt_cs1 csF) crt_ret_facts r (-104) 0 HJ HARU).
  - rewrite G8. rewrite <- E8. symmetry. apply Z_to_bv_bv_unsigned.
  - lia.
  - lia.
  - lia.
  - unfold fss_ret_s0_regs, crt_ret_regions, regions_wf. cbn [forallb andb].
    rewrite WFframe. cbn [andb].
    assert (X0 : YP09.region_wf (fs_ret_s0_region (-104) 0 crt_sv_chunks) = true) by (vm_compute; reflexivity).
    assert (X1 : YP09.region_wf (crt_slot_region crt_cs1) = true) by (vm_compute; reflexivity).
    assert (X3 : YP09.region_wf crt_shadow_region = true) by (vm_compute; reflexivity).
    rewrite X0, X1, X3. reflexivity.
  - exact crt_sv_in.
  - eapply crt_chunks_env; [exact Hag | exact crt_sv_atoms | exact HSV].
  - intros a Ha. apply Hk; [lia | unfold ESTACK; lia].
  - unfold crt_ret_regions. constructor; [exact ROslot|]. constructor; [exact ROframe|].
    constructor; [exact ROshadow | apply Forall_nil].
  - apply pairwise_disjoint_of_extents.
    unfold fss_ret_s0_regs, crt_ret_regions, crt_slot_region, crt_frame_region, crt_shadow_region, fs_ret_s0_region.
    cbn [map]. unfold extent_of_region, base_val. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
    fold E'. rewrite E8v, E9v, E47v, E26v. rewrite !crt_frame3. change (512 / 8) with 64.
    unfold ESTACK in Hceil1.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; try exact I;
      first [right; lia | left; lia | destruct Dfs as [Hd|Hd]; [left; lia | right; lia]].
  - unfold crt_ret_facts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E'.
    rewrite E9v, E47v. change (2 ^ 5) with 32.
    split; [split; [lia | split; [exact Fm32 | lia]]|].
    split; [|exact I]. split; [lia | split; [exact Hal32 | lia]]. }
split; [exact HE'|]. split; [|exact HS4].
split; [exact Hfrs|]. split; [exact Hnotin|].
cbn [ms_mem mkst] in Hflag |- *. rewrite <- Hflag. apply rdword_ext. intros kk Hk8.
rewrite crt_frame3. apply Hfr; [lia|]. rewrite SPT. unfold ESTACK in Hceil1 |- *. lia.
Qed.

Hypothesis HENV : api_env tfibsegs B.
Lemma crtB0_bcmp_journal : forall cx ly3 S3 U3 (W3 : world tfibsegs) regsT memT mdT mem2 md2 k,
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 memT) mdT k ->
  ARU tfibsegs B ly3 S3 U3 W3 memT mdT -> ARU tfibsegs B ly3 S3 U3 W3 mem2 md2 ->
  same_but_materialized mdT md2 ->
  spZ regsT = crt_sp1 cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
     aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) memT a) ->
  (forall a, spZ regsT - ASTACK <= a < spZ regsT -> apresent (w_H W3) mem2 a) ->
  ajournal tfibsegs B ASTACK (spZ regsT) [] ly3 S3 W3 (unpoison U3 memT) mdT []
    ly3 S3 W3 (unpoison U3 mem2) md2 0.
Proof.
intros cx ly3 S3 U3 W3 regsT memT mdT mem2 md2 k HJ HARU HARU2 Hsm SPT Hfr Hpr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (HSTK : 17000 <= STK_check_round_trip) by (vm_compute; discriminate).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & HQT).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (H0 : 192 <= spZ (c_regs cx)) by lia.
destruct (crt_sp1_facts cx Hal16 H0) as (Hsp1b & _ & Hsp1_16).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkA : astk_ok ASTACK ly3 (spZ regsT)).
{ unfold astk_ok. unfold ly_bot in Hbot |- *. rewrite SPT, Etop, Eslo, Eshi. unfold ASTACK in Hbot |- *.
  split; [exact Hsp1_16|]. repeat split; lia. }
assert (HpresU : forall a, spZ regsT - ASTACK <= a < spZ regsT -> apresent (w_H W3) (unpoison U3 mem2) a).
{ intros a Ha. apply (fsw_apresent_poison B ly3 S3 U3 W3 mem2 md2 a HARU2); [|exact (Hpr a Ha)].
  rewrite SPT in Ha. unfold ASTACK in Ha. unfold kHighMemBeg in *. lia. }
eapply (call_effect_journal tfibsegs B LAWS fs_segs_low HENV ASTACK ly3 S3 W3 regsT (unpoison U3 memT) mdT ly3 S3 W3
  (unpoison U3 mem2) md2 (fun _ => False) [] [] 0);
  [exact (ARU_AR tfibsegs B ly3 S3 U3 W3 mem2 md2 HARU2) | apply layout_le_refl | apply wle_refl
  | apply same_io_materialized; exact Hsm | | exact HpresU | exact (ARU_AR tfibsegs B ly3 S3 U3 W3 memT mdT HARU)
  | exact HstkA | reflexivity | lia | lia | lia | intros a [] | | exact HQT ].
- intros a Ha _ _ Hs _. apply (crt_unpoison_keep (w_H W3) U3 memT mem2 _ Hfr a Ha).
  intros Hw. cbv beta in Hw. apply Hs. left. unfold ASTACK. unfold ESTACK in Hw. lia.
- intros p n i Hp Hnp. exfalso. exact (Hnp Hp).
Qed.
End b.

(* the bcmp call site with crt_ss_ret's four regions: the engine's registers and facts at PC_bcmp, the memory of the
   boundary state at 0x821d4 (the run reads the frame only, so its frame and shadow regions still hold) *)
Definition crtB0_ssB : sstate :=
  mkSS (ss_pc crtB0_sc11) (ss_regs crtB0_sc11) (ss_mem (crt_ss_ret 0 crt_cs1 crt_csF)) (ss_resv crtB0_sc11)
    (ss_facts crtB0_sc11).
Lemma crtB0_ssB_ok : forall {fx : YK11.FPState} {rc : YM05.RunCeil} E (H : word -> bool) ms0 ms,
  st_ok tfibsegs E (crt_ss_ret 0x821d4 crt_cs1 crt_csF) (restrict H ms0) ->
  st_ok tfibsegs E crtB0_sc11 (restrict H ms) ->
  same_below (ms_mem ms0) (ms_mem ms) alloc_ceiling ->
  bv_unsigned (ew E 47) + 512 <= alloc_ceiling -> bv_unsigned (ew E 26) + 64 <= alloc_ceiling ->
  st_ok tfibsegs E crtB0_ssB (restrict H ms).
Proof.
intros fx rc E H ms0 ms HS0 HSC Hs HF HSF.
pose proof (st_ok_mem_ok tfibsegs E _ _ HS0) as (_ & Hok0 & Hpd0).
destruct HSC as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (_ & Hok & _) & H9).
assert (Msc : ss_mem crtB0_sc11 = [crt_s0_region; crt_slot_region crt_cs1; crtB0_fr_ro]) by (vm_compute; reflexivity).
rewrite Msc in Hok.
apply Forall_cons_iff in Hok as (Ok0 & Hok). apply Forall_cons_iff in Hok as (Ok1 & _).
cbn [ss_mem crt_ss_ret fss_ret_s0_args fss_ret_s0_regs crt_ret_regions] in Hok0.
apply Forall_cons_iff in Hok0 as (_ & Hok0). apply Forall_cons_iff in Hok0 as (_ & Hok0).
apply Forall_cons_iff in Hok0 as (Ok2 & Hok0). apply Forall_cons_iff in Hok0 as (Ok3 & _).
unfold crtB0_ssB, st_ok. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [exact H6|]. split; [exact H7|]. split; [|exact H9].
split; [vm_compute; reflexivity|]. split; [|exact Hpd0].
cbn [ss_mem crt_ss_ret fss_ret_s0_args fss_ret_s0_regs crt_ret_regions].
apply Forall_cons; [exact Ok0|]. apply Forall_cons; [exact Ok1|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (crtB0_region_below E H (ms_mem ms0) (ms_mem ms) _ Hs); [vm_compute; reflexivity | | exact Ok2].
  unfold crt_frame_region. cbn [YP09.r_base YP09.r_hi base_val]. rewrite crt_frame3. exact HF.
- apply (crtB0_region_below E H (ms_mem ms0) (ms_mem ms) _ Hs); [vm_compute; reflexivity | | exact Ok3].
  unfold crt_shadow_region. cbn [YP09.r_base YP09.r_hi base_val]. rewrite crt_frame3.
  change (512 / 8) with 64. exact HSF.
Qed.
Lemma crtB0_sc11_saved : forall q, In q [8; 9; 18; 19; 20; 21; 23; 24; 26; 27]%nat ->
  sr_get (ss_regs crtB0_sc11) (Z_to_bv 5 (Z.of_nat q)) = SOff q 0.
Proof.
intros q Hq. cbn [In] in Hq.
repeat (destruct Hq as [<-|Hq]; [vm_compute; reflexivity|]). destruct Hq.
Qed.
Lemma crtB0_sc11_s9 : sr_get (ss_regs crtB0_sc11) (Z_to_bv 5 (Z.of_nat 25)) = SOff 10 0.
Proof. vm_compute. reflexivity. Qed.
(* B: s6 holds &n re-seated on the frame atom (crtB0_ss11_base), A's s11 *)
Lemma crtB0_sc11_s6 : sr_get (ss_regs crtB0_sc11) (Z_to_bv 5 (Z.of_nat 22)) = SOff 47 0x1c0.
Proof. vm_compute. reflexivity. Qed.
Lemma crtB0_sc11z_saved : forall q, In q [18; 19; 20; 21; 23; 24; 27]%nat ->
  sr_get (ss_regs crtB0_sc11z) (Z_to_bv 5 (Z.of_nat q)) = SOff q 0.
Proof.
intros q Hq. cbn [In] in Hq.
repeat (destruct Hq as [<-|Hq]; [vm_compute; reflexivity|]). destruct Hq.
Qed.
Lemma crtB0_sc11z_s9 : sr_get (ss_regs crtB0_sc11z) (Z_to_bv 5 (Z.of_nat 25)) = SOff 10 0.
Proof. vm_compute. reflexivity. Qed.
Lemma crtB0_sc11z_s6 : sr_get (ss_regs crtB0_sc11z) (Z_to_bv 5 (Z.of_nat 22)) = SOff 47 0x1c0.
Proof. vm_compute. reflexivity. Qed.
(* the re-seated s6 reads F + 0x1c0 *)
Lemma crtB0_s6_val : forall cx E, crt_E cx E -> 0 <= crt_F cx -> crt_F cx + 0x1c0 < 2 ^ 64 ->
  sv_denot E (SOff 47 0x1c0) = Z_to_bv 64 (crt_F cx + 0x1c0).
Proof.
intros cx E HE H0 H1.
assert (E47 : bv_unsigned (ew E 47) = crt_F cx)
  by (rewrite (crt_E_F cx E HE), Z_to_bv_unsigned, bv_wrap_small
        by (change (bv_modulus 64) with (2 ^ 64); lia); reflexivity).
apply bv_eq. rewrite denot_SOff, E47.
rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
apply zcanon_id. unfold M64. lia.
Qed.

(* ================= the boundary at the return of the second decode (B 0x821d4, A 0x82078) =================
   Register heads are B crt_INV_8212c's (s2 = text, s4 = len, s5 = bd, s11 = F + 0xe0, s7 = F + 0x80, s6 = F + 0x1c0,
   s3 = F; A: s6 = F + 0xe0, s10 = F + 0x20, s11 = F + 0x1c0). Since 0x821c4: decode made `dec`, a live reader block
   of dec_size tb2 bytes holding bs, whose head joins U, and wrote
   |bs| into the length cell F + 0x1c0; a0 = dec. The forms of the block list (want's size enc_size len, same's an
   existential nsame) and the budgets (0x82288's) are a Theorem Labs lane's exit forms, so the bcmp step carries them as they are.
   This boundary is lane B0's own; no other lane names it. *)
Section inv. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Definition crtB0_INV_82078 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  ew E 18 = Z_to_bv 64 (c_text cx) /\ ew E 20 = Z_to_bv 64 len /\
  ew E 21 = Z_to_bv 64 (c_bd cx) /\ ew E 27 = Z_to_bv 64 (F + 0xe0) /\ ew E 23 = Z_to_bv 64 (F + 0x80) /\
  ew E 22 = Z_to_bv 64 (F + 0x1c0) /\ ew E 19 = Z_to_bv 64 F /\
  (exists same nsame dec live peak cnt,
     ew E 24 = Z_to_bv 64 same /\ ew E 10 = Z_to_bv 64 dec /\ 4096 + HEAD <= dec /\
     Permutation (ablocks B ly3 S3)
       (ablocks B (c_ly cx) (c_S cx) ++
        [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD); (c_want cx, FSH_Fn_writer.enc_size len);
         (same, nsame); (dec - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD)]) /\
     Permutation U3 (c_U cx ++ [(c_text cx - HEAD, HEAD); (dec - HEAD, HEAD)]) /\
     FSupoisonU.fs_heads B ly3 S3 U3 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
     zbytes_at tfibsegs W3 mem (c_text cx) (tb2 ++ [0]) /\ cstr_ok tfibsegs W3 mem (c_text cx) tb2 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem dec (FSH_Fn_writer.dec_size tb2) /\
     zbytes_at tfibsegs W3 mem dec (c_bs cx) /\
     val_mem tfibsegs (mrestrict (w_H W3) mem) (F + 0x1c0) 8 len /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\
     live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 /\
     blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVE_8212c cx /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_8212c cx /\ k <= K_8212c cx).
End inv.

(* ================= SEGMENT 10: 0x821c4 -> preset_base64_decode -> 0x821d4 (A 0x82068 -> 0x82078) ================= *)
Section s10. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Hypothesis DECODE : @FSH_Fn_writer.decode_spec_ff fx rc SK B tfibsegs.

(* the decode call's own part: decode_spec_ff's premises at the call site (the length cell's shadow from
   crt_INV_82068's v28 conjunct), its success arm (cnt <> fail and b64_dec (b64_enc bs) = Some bs kill the other two),
   and crtB0_INV_82078 from its post *)
Lemma crtB0_hcall10 : crt_hcall SK B crtB0_sc10 A_preset_base64_decode 0x821d4 STK_preset_base64_decode
  (crt_INV_82068 B) (crtB0_INV_82078 B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HSB RG HPREc HFRL HTOPc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_lt rc) as HC47.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htb & _ & _ & Hb64 & _ & _ & _ & _ & Hquiet & Hlive64 & _ & _ &
  Hnev0 & Hbb0 & _).
destruct HINV as (E10 & E18 & E20 & E21 & E27 & E23 & E22 & E19 & same & live & peak & cnt & E24 & E25 &
  HPB & HPU & HHD & HRT & HZT & HCT & HZW & HZS & HRA & HLT & HG & HLV & HBB & HCN & HK).
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) as HAR3.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
pose proof HJC as (_ & Hly3 & _ & _ & _ & _ & Hnev3 & _).
pose proof (crt_F_ly cx _ ly3 Hly3) as EF.
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 memC mdC k HJC HARUC Hfr) as (HF32 & HF4096 & HFceil & _ & _ & _).
destruct crtB0_regs10 as (Gra & Ga0 & Ga1).
assert (R1 : YK11.getr regsC 1%bv = Z_to_bv 64 0x821d4) by (rewrite RG, Gra; reflexivity).
assert (G10 : YK11.getr regsC 10%bv = w64 (c_text cx)) by (rewrite RG, Ga0, fsw_SOff0; exact E18).
assert (G11 : YK11.getr regsC 11%bv = w64 (crt_F cx + 0x1c0)) by (rewrite RG, Ga1, fsw_SOff0; exact E22).
assert (RS : forall n, (18 <= n <= 27)%nat -> YK11.getr regsC (Z_to_bv 5 (Z.of_nat n)) = ew E n).
{ intros n Hn. rewrite RG, (crtB0_ssave10 n Hn). apply fsw_SOff0. }
(* ---- the text: its block, its bytes and its C string at the call site ---- *)
pose proof (crtB_len_text (c_bs cx)) as Ltxt.
assert (Lt : Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1 =
  FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))).
{ rewrite <- Ltxt. rewrite length_app, Nat2Z.inj_add. cbn [length Z.of_nat]. lia. }
pose proof (cstr_ok_below W3 (ms_mem ms3) memC (c_text cx) (WriterSpec.b64_enc (c_bs cx)) HSB HCT) as HCT'.
pose proof HCT' as ((Hgz & _) & Ht4096 & Htceil & _).
assert (Hbok : WriterSpec.bytes_ok (WriterSpec.b64_enc (c_bs cx)))
  by exact (garr8_bytes_ok tfibsegs _ _ _ (proj1 (proj1 (garr8_app tfibsegs _ _ _ _) Hgz))).
pose proof (fs_rblock_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ _ HAR3 HSB HRT) as HRTc.
pose proof HRTc as (Htin & Htal & Htn & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Htin) as (_ & _ & _ & _ & _ & _ & Htmax).
pose proof (req_size_pos (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD) ltac:(unfold HEAD; lia))
  as (_ & Htreq).
destruct (fsw_rblock_low B ly3 S3 W3 _ mdC memC _ _ HAR3 HRTc) as (HtL1 & HtL2).
assert (HZTc : zbytes_at tfibsegs W3 memC (c_text cx) (WriterSpec.b64_enc (c_bs cx) ++ [0])).
{ apply (crtB0_zb_keep W3 W3 (ms_mem ms3) memC); [|exact HZT].
  intros a Ha. rewrite Ltxt in Ha.
  exact (aview_below (w_H W3) (ms_mem ms3) memC alloc_ceiling a HSB ltac:(lia)). }
(* ---- the length cell F + 0x1c0: inside crt's frame, 8-aligned, present, addressable, apart from the text ---- *)
assert (Hlo : frame_addr ly3 3 (c_pos cx) <= crt_F cx + 0x1c0) by (rewrite EF; lia).
assert (Hhi : crt_F cx + 0x1c0 + 8 <= frame_addr ly3 3 (c_pos cx) + fs_frame_bytes 3)
  by (rewrite EF, crt_frame3; lia).
destruct (crtB0_dec_fp_clear B ly3 S3 W3 (unpoison U3 memC) mdC (c_pos cx) (crt_F cx + 0x1c0) HAR3 Hin3 Hlo Hhi)
  as (HB1 & HB2 & _ & HB4).
rewrite EF, crt_frame3 in HB2.
assert (Hmod8 : (crt_F cx + 0x1c0) mod 8 = 0) by exact (crtB_m8_add (crt_F cx) 0x1c0 HF32 eq_refl).
assert (Hframe : exists cid pos, In (cid, pos) (frames S3) /\
  forall a, crt_F cx + 0x1c0 <= a < crt_F cx + 0x1c0 + 8 -> in_zr a (frame_rng ly3 (cid, pos))).
{ exists 3, (c_pos cx). split; [exact Hin3|]. intros a Ha. unfold in_zr, frame_rng. cbn [fst snd].
  rewrite EF, crt_frame3. lia. }
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (c_pos cx) HAR3 Hin3) as (_ & _ & Hfp & _).
rewrite EF, crt_frame3 in Hfp.
assert (Hpres : forall a, crt_F cx + 0x1c0 <= a < crt_F cx + 0x1c0 + 8 -> apresent (w_H W3) memC a).
{ intros a Ha. destruct (Hfp a ltac:(lia)) as (Hp & Hno).
  exact (fsw_apresent_notowned B ly3 S3 U3 W3 memC mdC a HARUC ltac:(lia) Hno Hp). }
destruct (crtB0_val_ex (w_H W3) memC (crt_F cx + 0x1c0)
  (fun i Hi => Hpres (crt_F cx + 0x1c0 + i) ltac:(lia))) as (v & Hv & Hvr).
assert (Hsep : crt_F cx + 0x1c0 + 8 <= c_text cx \/
  c_text cx + Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1 <= crt_F cx + 0x1c0).
{ pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 (unpoison U3 memC) mdC _ _ 3 (c_pos cx)
    HAR3 Htin Hin3) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite EF, crt_frame3 in D. unfold HEAD in *. lia. }
pose proof (fsw_range_addressable_below (w_H W3) (ms_mem ms3) memC (crt_F cx + 0x1c0) 8 HSB ltac:(lia) ltac:(lia)
  HRA) as HRAC.
pose proof (fs_glob_below W3 (ms_mem ms3) memC live peak cnt SIZE_MAXZ HSB HG) as HG'.
(* ---- the budgets: ticks, block bytes, g_live and g_count ---- *)
assert (Hbs : Forall (fun b => 0 <= b < 256) (c_bs cx)) by exact (WriterSpecFacts.b64_dec_ok _ _ Hb64).
assert (Hdec : WriterSpec.b64_dec (WriterSpec.b64_enc (c_bs cx)) = Some (c_bs cx))
  by exact (WriterSpecFacts.b64_dec_enc _ Hbs).
pose proof (crtB0_len_bound (c_tb cx) (c_bs cx) Hb64) as Hlb.
pose proof (crtB0_live_room cx Hlb Htb) as Hroom.
unfold LIVE_8212c, crt_es in Hroom.
assert (Hev : st_nev S3 + dec_ev (WriterSpec.b64_enc (c_bs cx)) <= EV_MAX).
{ unfold dec_ev. rewrite Hdec.
  unfold K_82068, EV_preset_base64_encode, CRT_EV_WRAP, EV_fuzz_malloc, EV_check_round_trip in *. lia. }
assert (Hroom2 : blocks_bytes S3 + (dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD) <= LIVE_MAX) by lia.
assert (Henc : 0 <= FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))).
{ unfold FSH_Fn_writer.enc_size.
  pose proof (Z.div_pos (Z.of_nat (length (c_bs cx)) + 2) 3 ltac:(lia) ltac:(lia)). lia. }
assert (Hdec3 : 3 <= dec_size (WriterSpec.b64_enc (c_bs cx))).
{ unfold dec_size. pose proof (Z.div_pos (Z.of_nat (length (WriterSpec.b64_enc (c_bs cx)))) 4 ltac:(lia) ltac:(lia)).
  lia. }
assert (Hlive2 : live + dec_size (WriterSpec.b64_enc (c_bs cx)) < 2 ^ 64).
{ unfold LIVE_82068, crt_len, HEAD in Hroom. lia. }
destruct Hquiet as (_ & Hc0 & Hc63).
assert (Hcnt63 : cnt < 2 ^ 63) by (unfold CNT_82068, EV_check_round_trip in *; lia).
(* ---- the decode ---- *)
pose proof (DECODE ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) (c_text cx) (crt_F cx + 0x1c0)
  (WriterSpec.b64_enc (c_bs cx)) live peak cnt SIZE_MAXZ v HPREc HHD HFRL G10 G11 HCT') as HDEC.
lazymatch type of HDEC with ?P -> _ => assert (Hws : P) end.
{ (* the text is the user bytes of its own live reader block (wsrc_kept's second arm) *)
  right. left. exists (c_text cx), (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))).
  split; [lia|]. split; [exact HRTc|]. split; [lia|]. rewrite Ltxt. lia. }
specialize (HDEC Hws Hbok ltac:(unfold MALLOC_MAX, HEAD in Htmax; lia) Hmod8 Hframe Hpres HRAC Hv Hvr Hsep HG'
  Hev Hroom2 Hlive2 ltac:(lia)).
exists (FS_PSTAT_FP ++ [(crt_F cx + 0x1c0, crt_F cx + 0x1c0 + 8)]), 1.
lazymatch type of HDEC with SRr _ _ _ (fun W' c' => _ \/ _ \/ @?C W' c') => exists C end.
split.
{ (* the refused arm needs cnt = SIZE_MAX, the bad-text arm b64_dec tb2 = None: only the success arm is left *)
  eapply SRr_mono; [exact HDEC|]. intros W' c' _ [(Hc & _) | [(_ & Hn & _) | Hok]].
  - exfalso. unfold SIZE_MAXZ in Hc. lia.
  - exfalso. rewrite Hdec in Hn. discriminate.
  - exact Hok. }
split.
{ (* the footprint: the statics are image bytes, the length cell a byte of crt's own frame *)
  intros a Ha. apply inFP_app in Ha as [Ha|Ha].
  - right. right. left. split; [exact Ha | exact (crt_pstat_img a Ha)].
  - right. right. right. left. apply inFP_cons in Ha as [Ha|Ha]; [|destruct (inFP_nil a Ha)].
    exists 3, (c_pos cx). split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EF, crt_frame3. lia. }
split.
{ (* the flag word at F + 504 is off the length cell *)
  intros a Ha. rewrite crt_frame3 in Ha. apply HB2; lia. }
intros W' c' (q & out & Hcnt' & Hout & Hq0 & ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HQ).
destruct HQ as (Q10 & Qq & Qab & Qrb & Qzb & Qval & Qcstr & Qglob).
rewrite Hdec in Hout. injection Hout as Eout. subst out.
exists ly', S', (U3 ++ [(q - HEAD, HEAD)]), regs', mem', md'.
split; [exact Ec|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP|].
intros HJ' HARU'.
(* ---- the heads after the call: U3's, and dec's ---- *)
assert (HH' : FSupoisonU.fs_heads B ly' S' (U3 ++ [(q - HEAD, HEAD)])).
{ intros rr Hrr. apply in_app_or in Hrr as [Hrr|[<-|[]]].
  - destruct (HHD rr Hrr) as (E16 & m & Hm & Hm16). split; [exact E16|]. exists m.
    split; [rewrite Qab; apply in_or_app; left; exact Hm | exact Hm16].
  - split; [reflexivity|]. exists (dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD).
    split; [rewrite Qab; apply in_or_app; right; left; reflexivity|].
    pose proof (req_size_pos (dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrq).
    unfold HEAD in *. lia. }
(* ---- the text across the call: its block (FSW_rd.fs_rblock_kept_call) and its bytes (crt_keep_blk), both off the
   decode's footprint (crtB0_dec_fp_clear) ---- *)
assert (HRB : forall p kk x, fs_rblock tfibsegs B ly3 S3 W3 memC p kk -> p - HEAD <= x < p + kk ->
  ~ inFP (FS_PSTAT_FP ++ [(crt_F cx + 0x1c0, crt_F cx + 0x1c0 + 8)]) x).
{ intros p kk x (Hin & _ & Hkk & _) Hx. apply (HB1 (p - HEAD) (kk + HEAD) x Hin).
  pose proof (req_size_pos (kk + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr). unfold HEAD in *. lia. }
assert (KR : forall p kk, fs_rblock tfibsegs B ly3 S3 W3 memC p kk -> fs_rblock tfibsegs B ly' S' W' mem' p kk).
{ intros p kk Hp. eapply (@fs_rblock_kept_call rc SK B);
    [exact HJc | exact HARUC | exact OK' | exact PO' | | exact Hp].
  intros x Hx. exact (HRB p kk x Hp Hx). }
assert (HZT' : zbytes_at tfibsegs W' mem' (c_text cx) (WriterSpec.b64_enc (c_bs cx) ++ [0])).
{ apply (crtB0_zb_keep W3 W' memC mem'); [|exact HZTc].
  intros a Ha. rewrite Ltxt in Ha.
  replace a with (c_text cx - HEAD + (HEAD + (a - c_text cx))) by lia.
  apply (crt_keep_blk SK B ly3 S3 U3 W3 memC mdC ly' S' (U3 ++ [(q - HEAD, HEAD)]) W' mem' md'
    STK_preset_base64_decode (spZ regsC) (FS_PSTAT_FP ++ [(crt_F cx + 0x1c0, crt_F cx + 0x1c0 + 8)]) 1
    (c_text cx - HEAD) (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD) (HEAD + (a - c_text cx))
    HARUC HARU' HJc Htin ltac:(rewrite Qab; apply in_or_app; left; exact Htin)).
  - unfold HEAD in *. lia.
  - apply (HB1 _ _ _ Htin). unfold HEAD in *. lia. }
assert (Hbb' : blocks_bytes S' = blocks_bytes S3 + (dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD)).
{ rewrite (blocks_bytes_bsum B ly' S'), (blocks_bytes_bsum B ly3 S3), Qab, bsum_app, bsum_cons. cbn [snd].
  change (bsum []) with 0. lia. }
(* ---- the callee-saved registers after the call ---- *)
assert (PE : forall n, (18 <= n <= 27)%nat -> ew (Ereg regs' (crt_extra cx)) n = ew E n).
{ intros n Hn.
  assert (Hb5 : Z.of_nat n = bv_unsigned (Z_to_bv 5 (Z.of_nat n)))
    by (rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | change (bv_modulus 5) with 32; lia]).
  rewrite (ew_Ereg_nat regs' (crt_extra cx) n (Z_to_bv 5 (Z.of_nat n)) Hb5).
  rewrite (HP (Z.of_nat n) ltac:(unfold acallee_saved; lia)). exact (RS n Hn). }
(* ---- crtB0_INV_82078 ---- *)
unfold crtB0_INV_82078. cbn [ms_mem mkst].
split; [rewrite (PE 18%nat ltac:(lia)); exact E18|].
split; [rewrite (PE 20%nat ltac:(lia)); exact E20|].
split; [rewrite (PE 21%nat ltac:(lia)); exact E21|].
split; [rewrite (PE 27%nat ltac:(lia)); exact E27|].
split; [rewrite (PE 23%nat ltac:(lia)); exact E23|].
split; [rewrite (PE 22%nat ltac:(lia)); exact E22|].
split; [rewrite (PE 19%nat ltac:(lia)); exact E19|].
exists same, (Z.of_nat (length (c_tb cx)) + 1), q, (live + dec_size (WriterSpec.b64_enc (c_bs cx))),
  (Z.max peak (live + dec_size (WriterSpec.b64_enc (c_bs cx)))), ((cnt + 1) mod 2 ^ 64).
split; [rewrite (PE 24%nat ltac:(lia)); exact E24|].
split; [rewrite (ew_Ereg_nat regs' (crt_extra cx) 10 10%bv eq_refl); exact Q10|].
split; [exact Qq|].
split.
{ rewrite Qab. eapply Permutation_trans; [apply Permutation_app_tail; exact HPB|].
  rewrite <- app_assoc. apply Permutation_app_head. cbn [app]. unfold FSH_Fn_writer.enc_size.
  apply Permutation_refl. }
split.
{ eapply Permutation_trans; [apply Permutation_app_tail; exact HPU|].
  rewrite <- app_assoc. cbn [app]. apply Permutation_refl. }
split; [exact HH'|].
split; [exact (KR _ _ HRTc)|].
split; [exact HZT'|].
split; [exact Qcstr|].
split; [exact Qrb|].
split; [exact Qzb|].
split; [exact Qval|].
split; [exact Qglob|].
split; [lia|].
split; [rewrite Hbb'; unfold LIVE_8212c, crt_es; lia|].
split; [rewrite Z.mod_small by lia; unfold CNT_8212c, CNT_82068 in *; lia|].
unfold K_8212c, crt_es, dec_ev. rewrite Hdec. unfold EV_fuzz_malloc. lia.
Qed.

(* ---- SEGMENT 10, the generic call crossing with the leading `bnez a0` (FSH_crt_site.crt_seg_call_br) ---- *)
Lemma crtB0_seg10 :
  crt_from SK B (crt_ss_ret 0x821d4 crt_cs1 crt_csF) (crtB0_INV_82078 B) ->
  crt_from SK B (crt_ss_ret 0x821c4 crt_cs1 crt_csF) (crt_INV_82068 B).
Proof.
intros NEXT.
assert (HSTK0 : 0 <= STK_preset_base64_decode) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSTK1 : STK_preset_base64_decode + 208 <= STK_check_round_trip) by (apply Z.leb_le; vm_compute; reflexivity).
refine (crt_seg_call_br SK B 0x821c4 A_preset_base64_decode 0x821d4 crtB0_sb10 crtB0_sc10 (crt_INV_82068 B)
  (crtB0_INV_82078 B) STK_preset_base64_decode crtB0_br10 crtB0_run10 crtB0_site10 ltac:(lia) eq_refl HSTK0 HSTK1
  _ crtB0_hcall10 NEXT).
intros cx E k ly3 S3 U3 W3 ms3 md3 HINV. destruct HINV as (H10 & _). exact H10.
Qed.
End s10.

(* ================= SEGMENT 11: 0x821d4 -> (bcmp ->) 0x821f8, or 0x821fc when |bs| = 0 (A 0x82078 -> 0x8209c / 0x820a0)
   ================= *)
Section s11. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis RT : CrtRt B.
Hypothesis HENV : api_env tfibsegs B.

Lemma crtB0_seg11 :
  crt_from SK B crtB_ss_8209c (crtB_INV_8209c B) ->
  crt_from SK B crtB_ss_820a0 (crtB_INV_820a0 B) ->
  crt_from SK B (crt_ss_ret 0x821d4 crt_cs1 crt_csF) (crtB0_INV_82078 B).
Proof.
intros N9c Na0 cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFO HINV HS.
unfold crtB0_INV_82078 in HINV. cbv beta zeta in HINV.
destruct HINV as (E18 & E20 & E21 & E27 & E23 & E22 & E19 & same & nsame & dec & live & peak & cnt &
  E24 & E10 & Hdec0 & HPa & HPu & FH & HRT & HZT & HCT & HRD & HZD & Hval & HG & HL & Hbb & Hcnt & Hk).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_lt rc) as HC47.
pose proof HFO as (Hfr & Hnin & Hflag).
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 (ms_mem ms3) md3 k HJ HARU Hfr) as (FAl & F4096 & Fceil & Fapp & FS1 & FS2).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
assert (E47 : bv_unsigned (ew E 47) = crt_F cx) by (rewrite (crt_E_F cx E HE); apply wz; lia).
assert (S6v : sv_denot E (SOff 47 0x1c0) = Z_to_bv 64 (crt_F cx + 0x1c0))
  by (apply (crtB0_s6_val cx E HE); lia).
pose proof HB as ((HPREU & _) & _).
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ HPREU) as (H16 & Hceil0 & H47 & _).
pose proof HPREU as ((_ & _ & _ & Hgp & Htp & _) & _).
pose proof crt_STK_eq as HSTK. unfold crt_STK in HSTK.
assert (H0 : 192 <= spZ (c_regs cx)) by lia.
destruct (crt_sp1_facts cx H16 H0) as (Hsp1b & _ & _).
(* the body's length and the block dec *)
pose proof (crtB_len_dec (c_bs cx)) as Hdsz.
pose proof HRD as (Hdin & _ & Hdn & _).
assert (Rd : req_size (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD) =
             FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD)
  by (apply crtB0_req_size; cbv [HEAD]; lia).
destruct (crtB0_blk_user B ly3 S3 U3 W3 (ms_mem ms3) md3 (dec - HEAD)
  (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD) dec (Z.of_nat (length (c_bs cx)))
  HARU FH Hdin ltac:(lia) ltac:(lia) ltac:(rewrite Rd; lia)) as (G4096 & Gceil & GMx & _).
cbv [MALLOC_MAX HEAD] in GMx.
assert (Eg : bv_unsigned (ew E 10) = dec) by (rewrite E10; apply wz; lia).
(* the text block's bounds (its bytes are below alloc_ceiling) *)
destruct (fsw_rblock_low B ly3 S3 W3 _ md3 (ms_mem ms3) _ _ HAR HRT) as (HtL1 & HtL2).
unfold HEAD in HtL1.
pose proof (crtB_len_text (c_bs cx)) as Ltxt.
assert (Lt : Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1 =
  FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))).
{ rewrite <- Ltxt. rewrite length_app, Nat2Z.inj_add. cbn [length Z.of_nat]. lia. }
pose proof HRT as (Htin & _ & _ & _).
assert (Hbs : Forall (fun b => 0 <= b < 256) (c_bs cx)).
{ pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb64 & _).
  exact (WriterSpecFacts.b64_dec_ok _ _ Hb64). }
pose proof (crt_enc_nz (c_bs cx) Hbs) as HNZ.
(* the start state of segment 11 (the length cell in the read-only frame, s6 on the frame atom) *)
pose proof (crtB0_ss11_ok cx E W3 ms3 (Z.of_nat (length (c_bs cx))) HE ltac:(lia) E20 ltac:(lia) E22 ltac:(lia)
  Hval HS) as HSb.
pose proof HSb as (_ & _ & _ & _ & _ & _ & _ & _ & HGb).
assert (A10 : afact_ok E 10 crtB0_fptr).
{ unfold afact_ok, crtB0_fptr. cbn [af_lo af_hi af_al2]. rewrite Eg. change (2 ^ 0) with 1.
  rewrite Z.mod_1_r. lia. }
assert (AWR : forall ssx, ss_mem ssx = [crt_s0_region; crt_slot_region crt_cs1; crtB0_fr_ro] ->
  awr_ok tfibsegs B E (ss_mem ssx) STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP
    (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)))
  by (intros ssx Hx; rewrite Hx; exact (crtB0_awr3 B cx E ly3 S3 HB HE)).
(* the frame chunk of the boundary state at 0x821d4 (the flag word), on the boundary memory *)
assert (HCSF0 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms3)) (crt_F cx)) crt_csF).
{ assert (H2r : nth_error (ss_mem (crt_ss_ret 0x821d4 crt_cs1 crt_csF)) 2 = Some (crt_frame_region crt_csF))
    by reflexivity.
  pose proof (fsw_region_nth E _ (restrict (w_H W3) ms3) 2 (crt_frame_region crt_csF) HS H2r) as HRF.
  destruct HRF as (_ & _ & _ & Hc). cbn [crt_frame_region YP09.r_base YP09.r_chunks base_val] in Hc.
  rewrite E47 in Hc. exact Hc. }
destruct (Z.eq_dec (Z.of_nat (length (c_bs cx))) 0) as [Hl0 | Hl1].
- (* ======== EMPTY-BODY ARM: `beqz s4` (0x821e4) taken, the join 0x821fc ======== *)
  pose proof (st_ok_facts tfibsegs E crtB0_ss11_base _ _ HSb (facts_ok_add_atom E _ 10 crtB0_fptr HGb A10))
    as HS11z.
  change (st_ok tfibsegs E crtB0_ss11z (restrict (w_H W3) ms3)) in HS11z.
  eapply (fsw_run_AJU B crt_tbl crt_tbl_ok W3 FUEL E crtB0_ss11z crtB0_sb11z _ ms3
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS11z crtB0_br11z I HARU HJ (AWR crtB0_ss11z eq_refl)).
  intros ms1 mat1 HS1 HJ1 HARU1 HF1 HFr1 HG1.
  assert (HBR : branch_taken BC_EQ (sv_denot E (SOff 20 0)) (sv_denot E (SLit 0)) = true).
  { rewrite branch_eq_U, (U_atom E 20 _ E20 ltac:(lia)), (U_lit E 0 ltac:(lia)). apply Z.eqb_eq. exact Hl0. }
  pose proof (st_ok_add_cond tfibsegs E crtB0_sb11z _ BC_EQ (SOff 20 0) (SLit 0) HS1 HBR) as HS1c.
  change (st_ok tfibsegs E crtB0_ss11zc (restrict (w_H W3) ms1)) in HS1c.
  assert (HMz : ss_mem crtB0_ss11zc = [crt_s0_region; crt_slot_region crt_cs1; crtB0_fr_ro])
    by (vm_compute; reflexivity).
  eapply (fsw_run_to_AJU B crt_tbl crt_tbl_ok W3 FUEL 0x821fc E crtB0_ss11zc crtB0_sc11z RS_running ms1
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS1c crtB0_run11z I HARU1 HJ1 (AWR crtB0_ss11zc HMz)).
  intros ms mat HSC HJC HARUC HF HFr HGr.
  assert (HF1' : frame_of E [crt_s0_region; crt_slot_region crt_cs1; crtB0_fr_ro] (ms_mem ms3) (ms_mem ms1))
    by exact HF1.
  assert (HF' : frame_of E [crt_s0_region; crt_slot_region crt_cs1; crtB0_fr_ro] (ms_mem ms1) (ms_mem ms))
    by (rewrite <- HMz; exact HF).
  assert (HSB : same_below (ms_mem ms3) (ms_mem ms) alloc_ceiling)
    by exact (same_below_trans _ _ _ _ (crt_sb B cx E _ _ HB HE (crtB0_frame_ro E _ _ HF1'))
                (crt_sb B cx E _ _ HB HE (crtB0_frame_ro E _ _ HF'))).
  destruct crtB0_sc11z_shape as (Zpc & Zres & Z0 & Z1 & Zmem & Z2 & Z3 & Z4 & Z8 & Z9 & Z26).
  (* the flag chunk on the run's memory *)
  assert (HCSF : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (crt_F cx)) crt_csF).
  { apply (crtB0_chunks_mb E (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) _ _ 504 512);
      [unfold crt_csF; rewrite crt_frame3; apply Forall_cons; [cbn; lia | apply Forall_nil] | | exact HCSF0].
    intros a Ha. apply (mbyte_below (w_H W3) (ms_mem ms3) (ms_mem ms) alloc_ceiling a HSB). lia. }
  destruct (crtB0_reenter SK B cx E k ly3 S3 U3 W3 ms _ crtB0_sc11z 0x821fc crt_cs1 crt_cs1 HB HE HSC Zpc Zres Z0 Z1
    (incl_refl _) crt_cs1_in crt_cs1_atoms ltac:(vm_compute; reflexivity) Z2 Z3 Z4 Z8 Z9 Z26 HCSF HJC HARUC Hin3)
    as (HE' & HS').
  assert (HFO' : crt_frame_ok cx S3 W3 ms).
  { split; [exact Hfr|]. split; [exact Hnin|]. rewrite <- Hflag. apply rdword_ext. intros i Hi.
    rewrite crt_frame3.
    exact (aview_below (w_H W3) (ms_mem ms3) (ms_mem ms) alloc_ceiling (crt_F cx + 512 - 8 + i) HSB ltac:(lia)). }
  refine (Na0 cx (Ereg (ms_regs ms) (crt_extra cx)) k ly3 S3 U3 W3 ms _ HB HE' HJC HARUC HFO' _ HS').
  (* ---- crtB_INV_820a0: the run stored nothing, so every data fact is the boundary's, below alloc_ceiling ---- *)
  assert (KS : forall q, In q [18; 19; 20; 21; 23; 24; 27]%nat -> ew (Ereg (ms_regs ms) (crt_extra cx)) q = ew E q).
  { intros q Hq. apply (crtB0_ew_run E crtB0_sc11z (w_H W3) ms (crt_extra cx) q q HSC);
      [cbn [In] in Hq; lia | exact (crtB0_sc11z_saved q Hq)]. }
  assert (K25 : ew (Ereg (ms_regs ms) (crt_extra cx)) 25 = ew E 10)
    by exact (crtB0_ew_run E crtB0_sc11z (w_H W3) ms (crt_extra cx) 25 10 HSC ltac:(lia) crtB0_sc11z_s9).
  assert (K22 : ew (Ereg (ms_regs ms) (crt_extra cx)) 22 = Z_to_bv 64 (crt_F cx + 0x1c0)).
  { rewrite (ew_Ereg_lt (ms_regs ms) (crt_extra cx) 22 ltac:(lia)),
      (st_ok_restrict_reg tfibsegs (w_H W3) E crtB0_sc11z ms _ HSC), crtB0_sc11z_s6. exact S6v. }
  assert (AVB : forall a, 0 <= a < alloc_ceiling ->
    aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) (ms_mem ms3) a)
    by (intros a Ha; exact (aview_below (w_H W3) (ms_mem ms3) (ms_mem ms) alloc_ceiling a HSB Ha)).
  unfold crtB_INV_820a0. cbn [ms_mem].
  split; [rewrite (KS 18%nat ltac:(cbn; tauto)); exact E18|].
  split; [rewrite (KS 20%nat ltac:(cbn; tauto)); exact E20|].
  split; [rewrite (KS 21%nat ltac:(cbn; tauto)); exact E21|].
  split; [rewrite (KS 27%nat ltac:(cbn; tauto)); exact E27|].
  split; [rewrite (KS 23%nat ltac:(cbn; tauto)); exact E23|].
  split; [exact K22|].
  split; [rewrite (KS 19%nat ltac:(cbn; tauto)); exact E19|].
  exists same, nsame, dec, live, peak, cnt.
  split; [rewrite (KS 24%nat ltac:(cbn; tauto)); exact E24|].
  split; [rewrite K25; exact E10|].
  split; [exact HPa|]. split; [exact HPu|]. split; [exact FH|].
  split; [exact (fs_rblock_below B ly3 S3 W3 _ _ _ _ _ _ HAR HSB HRT)|].
  split.
  { apply (crtB0_zb_keep W3 W3 (ms_mem ms3) (ms_mem ms)); [|exact HZT].
    intros a Ha. rewrite Ltxt in Ha. apply AVB. lia. }
  split; [exact (cstr_ok_below W3 (ms_mem ms3) (ms_mem ms) _ _ HSB HCT)|].
  split; [exact (fs_rblock_below B ly3 S3 W3 _ _ _ _ _ _ HAR HSB HRD)|].
  split.
  { apply (crtB0_zb_keep W3 W3 (ms_mem ms3) (ms_mem ms)); [|exact HZD].
    intros a Ha. apply AVB. lia. }
  split; [exact (fs_glob_below W3 (ms_mem ms3) (ms_mem ms) live peak cnt SIZE_MAXZ HSB HG)|].
  split; [exact HL|]. split; [exact Hbb|]. split; [exact Hcnt | exact Hk].
- (* ======== BODY ARM: bcmp (dec, bd, len), which answers 0 ======== *)
  assert (A20 : afact_ok E 20 (mkAF 1 (2 ^ 32) 0)).
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E20, wz by lia. change (2 ^ 0) with 1.
    rewrite Z.mod_1_r. change (2 ^ 32) with 4294967296. lia. }
  pose proof (st_ok_facts tfibsegs E crtB0_ss11_base _ _ HSb
    (facts_ok_add_atom E _ 20 _ (facts_ok_add_atom E _ 10 crtB0_fptr HGb A10) A20)) as HS11.
  change (st_ok tfibsegs E crtB0_ss11 (restrict (w_H W3) ms3)) in HS11.
  eapply (fsw_run_to_AJU B crt_tbl crt_tbl_ok W3 FUEL PC_bcmp E crtB0_ss11 crtB0_sc11 RS_running ms3
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS11 crtB0_run11 I HARU HJ (AWR crtB0_ss11 eq_refl)).
  intros ms mat HSC HJC HARUC HF HFr HG0.
  assert (HSB : same_below (ms_mem ms3) (ms_mem ms) alloc_ceiling)
    by exact (crt_sb B cx E _ _ HB HE (crtB0_frame_ro E _ _ HF)).
  destruct crtB0_sc11_regs as (Hpc11 & _ & Hres11).
  assert (R1 : sr_get (ss_regs crtB0_sc11) 1%bv = SLit 0x821f8) by (vm_compute; reflexivity).
  assert (R10 : sr_get (ss_regs crtB0_sc11) 10%bv = SOff 10 0) by (vm_compute; reflexivity).
  assert (R11 : sr_get (ss_regs crtB0_sc11) 11%bv = SOff 21 0) by (vm_compute; reflexivity).
  assert (R12 : sr_get (ss_regs crtB0_sc11) 12%bv = SOff 20 0) by (vm_compute; reflexivity).
  assert (R2 : sr_get (ss_regs crtB0_sc11) 2%bv = SOff 2 0) by (vm_compute; reflexivity).
  assert (R3 : sr_get (ss_regs crtB0_sc11) 3%bv = SOff 3 0) by (vm_compute; reflexivity).
  assert (R4 : sr_get (ss_regs crtB0_sc11) 4%bv = SOff 4 0) by (vm_compute; reflexivity).
  pose proof (crt_mkst (w_H W3) E crtB0_sc11 ms HSC Hres11) as Ems. rewrite Hpc11 in Ems.
  set (mdT := with_vm_backing (m_vm_lazy md3) mat md3) in *.
  set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
  rewrite Ems in HSC. rewrite Ems.
  assert (HspT : spZ regsT = crt_sp1 cx).
  { unfold spZ. rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtB0_sc11 _ 2%bv HSC), R2, fsw_SOff0.
    exact E2. }
  (* the invariant's data at the call site *)
  assert (AVT : forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W3) memT a = aview tfibsegs (w_H W3) (ms_mem ms3) a)
    by (intros a Ha; exact (aview_below (w_H W3) (ms_mem ms3) memT alloc_ceiling a HSB Ha)).
  assert (HdecT : fs_rblock tfibsegs B ly3 S3 W3 memT dec (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx))))
    by exact (fs_rblock_below B ly3 S3 W3 _ _ _ _ _ _ HAR HSB HRD).
  assert (HzbT : zbytes_at tfibsegs W3 memT dec (c_bs cx)).
  { apply (crtB0_zb_keep W3 W3 (ms_mem ms3) memT); [|exact HZD]. intros a Ha. apply AVT. lia. }
  assert (Hkeep : forall b, In b (ablocks B (c_ly cx) (c_S cx)) -> In b (ablocks B ly3 S3)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPa)). apply in_or_app. left. exact Hb. }
  destruct (crtB0_bcmp_data SK B cx ly3 S3 U3 W3 regsT memT mdT k dec
    (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx))) HB HJC HARUC FH Hkeep HdecT HzbT Hdsz HspT)
    as (Dl & Dg0 & Dg1 & Db0 & Db1 & Dsg & Dsb & Dwg & Dwb & Dmg & Dmb & Dag & Dhg & Dab & Dhb & DEQ).
  assert (HRet : YK0s.ret_ok (Z_to_bv 64 0x821f8)) by (apply ret_ok_even; rewrite (wz 0x821f8) by lia; reflexivity).
  assert (Ebd : bv_unsigned (ew E 21) = c_bd cx).
  { rewrite E21. apply wz. pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      (k0 & Hrb0 & _) & _).
    pose proof Hrb0 as (_ & _ & Hk0pos & _).
    destruct (fsw_rblock_low B (c_ly cx) (c_S cx) (c_W cx) _ (c_md cx) (c_mem cx) _ _
      (proj1 (proj1 (proj1 (proj1 HB)))) Hrb0) as (B1 & B2). unfold HEAD in B1. lia. }
  assert (Elen : bv_unsigned (ew E 20) = Z.of_nat (length (c_bs cx))) by (rewrite E20; apply wz; lia).
  (* the frame word at the call site *)
  assert (HFOT : crt_frame_ok cx S3 W3 (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs))).
  { split; [exact Hfr|]. split; [exact Hnin|]. cbn [ms_mem mkst].
    rewrite <- Hflag. apply rdword_ext. intros i Hi. rewrite crt_frame3 in *.
    exact (aview_below (w_H W3) (ms_mem ms3) memT alloc_ceiling (crt_F cx + 512 - 8 + i) HSB ltac:(lia)). }
  (* the call site with crt_ss_ret's four regions *)
  assert (HSBk : st_ok tfibsegs E crtB0_ssB
    (restrict (w_H W3) (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)))).
  { apply (crtB0_ssB_ok E (w_H W3) ms3 _ HS HSC HSB); [rewrite E47; exact Fceil|].
    rewrite E26. unfold kHighShadowEnd in FS2. lia. }
  (* the call *)
  eapply (crtB0_bcmp_call (SKfp := SK) B crtB0_sc11 0x821f8 10 cx E k ly3 S3 U3 W3 regsT memT mdT dec _
    R1 ltac:(lia) R10 R11 R12 R2 R3 R4 HRet RT HE H16 H0 H47 Hgp Htp HSC Eg Ebd Elen
    Dl Dg0 Dg1 Db0 Db1 Dsg Dsb Dwg Dwb Dmg Dmb Dag Dhg Dab Dhb HJC HARUC).
  intros regs2 mem2 md2 v HJ2 HARU2 HSM2 HP2 HFR2 Hv Hres.
  (* bcmp answered 0: the two byte ranges are equal *)
  pose proof (proj2 Hres (fun i Hi => eq_sym (DEQ i Hi))) as Hv0.
  assert (G1 : YK11.getr regsT 1%bv = Z_to_bv 64 0x821f8)
    by exact (fsw_reg_lit (w_H W3) E crtB0_sc11 (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)) 1%bv
                0x821f8 HSC R1 ltac:(lia)).
  rewrite G1.
  (* the walk's boundary state at 0x821f8 *)
  assert (HcsFin : Forall (fun c => 0 <= YP09.c_off c /\ 0 <= YP09.c_len c /\
      YP09.c_off c + YP09.c_len c <= fs_frame_bytes 3) crt_csF)
    by (unfold crt_csF; rewrite crt_frame3; apply Forall_cons; [cbn; lia | apply Forall_nil]).
  assert (HcsFat : crt_atom_chunks crt_csF)
    by (unfold crt_atom_chunks, crt_csF; apply Forall_cons; [do 4 eexists; split; [reflexivity | lia] | apply Forall_nil]).
  destruct (crtB0_bcmp_resume (SKfp := SK) B cx E crtB0_ssB k ly3 S3 U3 W3 regsT memT regs2 mem2 md2 crt_csF
    0x821f8 HE HJ2 HARU2 HFOT HSBk eq_refl ltac:(vm_compute; reflexivity) HP2 HFR2 HcsFin HcsFat)
    as (HE' & HFO' & HS').
  refine (N9c cx (Ereg regs2 (crt_extra cx)) k ly3 S3 U3 W3 (mkst regs2 (Z_to_bv 64 0x821f8) mem2 (seg_rom tfibsegs))
    md2 HB HE' HJ2 HARU2 HFO' _ HS').
  (* ---- crtB_INV_8209c after the call ---- *)
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  assert (Hpr : forall a, spZ regsT - ASTACK <= a < spZ regsT -> apresent (w_H W3) mem2 a).
  { intros a Ha. rewrite HspT in Ha. unfold ASTACK in Ha.
    apply (fsw_apresent_unpoison B ly3 S3 U3 W3 mem2 md2 a HARU2); [unfold kHighMemBeg in *; lia|].
    apply Hpres2. lia. }
  pose proof (crtB0_bcmp_journal (SKfp := SK) B HENV cx ly3 S3 U3 W3 regsT memT mdT mem2 md2 k HJC HARUC HARU2
    HSM2 HspT HFR2 Hpr) as J0.
  pose proof HARU2 as (_ & HO2 & HP2').
  (* the data facts: ms3 -> the call site (same_below) -> after the call (the empty-footprint journal, and the
     contract's frame clause below alloc_ceiling) *)
  assert (KB : forall p n, fs_rblock tfibsegs B ly3 S3 W3 (ms_mem ms3) p n -> fs_rblock tfibsegs B ly3 S3 W3 mem2 p n).
  { intros p n Hp.
    exact (fs_rblock_kept_call B ASTACK (spZ regsT) [] ly3 S3 U3 W3 memT mdT ly3 S3 U3 W3 mem2 md2 0 p n J0 HARUC
      HO2 HP2' (fun x _ => inFP_nil x) (fs_rblock_below B ly3 S3 W3 _ _ _ _ _ _ HAR HSB Hp)). }
  assert (AV2 : forall a, 0 <= a < alloc_ceiling ->
    aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) (ms_mem ms3) a).
  { intros a Ha. rewrite (HFR2 a ltac:(lia) ltac:(rewrite HspT; unfold ESTACK; lia)). exact (AVT a Ha). }
  assert (HZT2 : zbytes_at tfibsegs W3 mem2 (c_text cx) (WriterSpec.b64_enc (c_bs cx) ++ [0])).
  { apply (crtB0_zb_keep W3 W3 (ms_mem ms3) mem2); [|exact HZT]. intros a Ha. rewrite Ltxt in Ha. apply AV2. lia. }
  assert (HG2 : fs_glob tfibsegs W3 mem2 live peak cnt SIZE_MAXZ).
  { apply (crtB0_glob_keep W3 (ms_mem ms3) mem2); [|exact HG].
    intros a Ha. apply AV2. lia. }
  (* the registers of the resumed env *)
  assert (KR : forall (q n : nat), (q < 32)%nat -> acallee_saved (Z.of_nat q) ->
      sr_get (ss_regs crtB0_sc11) (Z_to_bv 5 (Z.of_nat q)) = SOff n 0 -> ew (Ereg regs2 (crt_extra cx)) q = ew E n).
  { intros q n Hq Hc Hs. rewrite (crtB0_keep_sv E crtB0_sc11 (w_H W3) _ regs2 (crt_extra cx) q _ HSC HP2 Hc Hq Hs).
    apply fsw_SOff0. }
  assert (KS : forall q, In q [8; 9; 18; 19; 20; 21; 23; 24; 26; 27]%nat ->
      ew (Ereg regs2 (crt_extra cx)) q = ew E q).
  { intros q Hq. apply (KR q q); [cbn [In] in Hq; lia | unfold acallee_saved; cbn [In] in Hq; lia |
      exact (crtB0_sc11_saved q Hq)]. }
  assert (G25 : ew (Ereg regs2 (crt_extra cx)) 25 = ew E 10)
    by exact (KR 25%nat 10%nat ltac:(lia) ltac:(unfold acallee_saved; lia) crtB0_sc11_s9).
  assert (G22 : ew (Ereg regs2 (crt_extra cx)) 22 = Z_to_bv 64 (crt_F cx + 0x1c0)).
  { rewrite (crtB0_keep_sv E crtB0_sc11 (w_H W3) _ regs2 (crt_extra cx) 22 _ HSC HP2
      ltac:(unfold acallee_saved; lia) ltac:(lia) crtB0_sc11_s6). exact S6v. }
  assert (G10 : ew (Ereg regs2 (crt_extra cx)) 10 = Z_to_bv 64 0)
    by (rewrite (ew_Ereg_lt regs2 _ 10 ltac:(lia)); exact (eq_trans Hv Hv0)).
  unfold crtB_INV_8209c, crtB_INV_820a0. cbn [ms_mem mkst].
  split; [exact G10|].
  split; [rewrite (KS 18%nat ltac:(cbn; tauto)); exact E18|].
  split; [rewrite (KS 20%nat ltac:(cbn; tauto)); exact E20|].
  split; [rewrite (KS 21%nat ltac:(cbn; tauto)); exact E21|].
  split; [rewrite (KS 27%nat ltac:(cbn; tauto)); exact E27|].
  split; [rewrite (KS 23%nat ltac:(cbn; tauto)); exact E23|].
  split; [exact G22|].
  split; [rewrite (KS 19%nat ltac:(cbn; tauto)); exact E19|].
  exists same, nsame, dec, live, peak, cnt.
  split; [rewrite (KS 24%nat ltac:(cbn; tauto)); exact E24|].
  split; [rewrite G25; exact E10|].
  split; [exact HPa|]. split; [exact HPu|]. split; [exact FH|].
  split; [exact (KB _ _ HRT)|].
  split; [exact HZT2|].
  split.
  { apply (crt_cstr_of_block B ly3 S3 U3 W3 mem2 md2 (c_text cx) (WriterSpec.b64_enc (c_bs cx)) _ _ HARU2 FH Htin);
      [unfold HEAD; lia | unfold HEAD; lia
      | exact HZT2 | exact HNZ]. }
  split; [exact (KB _ _ HRD)|].
  split.
  { apply (crtB0_zb_keep W3 W3 (ms_mem ms3) mem2); [|exact HZD]. intros a Ha. apply AV2. lia. }
  split; [exact HG2|]. split; [exact HL|]. split; [exact Hbb|]. split; [exact Hcnt | exact Hk].
Qed.
End s11.

(* ================= SEGMENTS 10-11: the theorem of this lane ================= *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis DECODE : @FSH_Fn_writer.decode_spec_ff fx rc SK B tfibsegs.
Hypothesis RT : CrtRt B.
Hypothesis HENV : api_env tfibsegs B.

Theorem crtB0_seg10_11 :
  crt_from SK B crtB_ss_8209c (crtB_INV_8209c B) ->
  crt_from SK B crtB_ss_820a0 (crtB_INV_820a0 B) ->
  crt_from SK B (crt_ss_ret 0x821c4 crt_cs1 crt_csF) (crt_INV_82068 B).
Proof.
intros N9c Na0. exact (crtB0_seg10 SK B DECODE (crtB0_seg11 SK B RT HENV N9c Na0)).
Qed.
End t.

(* A's note (build of 2026-10-29 08:5xZ on a build machine), the same for B: crtB0_seg10_11's hypotheses are its three arguments DECODE
   (decode_spec_ff), RT (CrtRt, for crt_fr_bcmp) and HENV (api_env, for the bcmp callee journal); Print Assumptions lists
   only the kernel primitives (PrimInt63 / PrimString / PrimArray) and Stdlib's
   FunctionalExtensionality.functional_extensionality_dep, which enters through the run kit FSW_K.fsw_run_AJU /
   fsw_run_to_AJU (lane D1 measured the same for FSH_crt_site.crt_seg_call). No project axiom. *)
About crtB0_seg10_11.
Print Assumptions crtB0_seg10_11.
