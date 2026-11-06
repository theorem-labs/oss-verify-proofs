(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YE05.v, with its module paths changed; 2671 of its 2756 lines of code are new or changed and 333 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segA.v, with its module paths and module names changed; 906 of its 1036 lines of code are new or changed and 2626 lines of the source are left out. *)
(* lib/B (fs.asan-ubsan) twin of lib/A/FSH_crt_site.v: the CALL-SITE block of check_round_trip's ASan walk, shared by
   every segment lane of the B walk - what the boundary state and the caller's journal give a callee at each program
   call (its fpreU with crt's frame record on the chain, FRL_CRT_CALLEE, the room above sp), the read-only-image facts
   it needs (crt_rodata, and crt_rom: the read-only image at any walk state), the generic call crossing (crt_seg_call /
   crt_seg_call_br / crt_seg_call_full), the RUNTIME-call crossing (crt_reg_atom / crt_gptp / crt_rt_frame /
   crt_rt_call for strlen / crt_rt_call2 for strcmp), the trap arms, the keeps and the rd_sum lemmas. Owner: a Theorem Labs lane
   (lane CRT); B twin written by a Theorem Labs lane.
   PORT SOURCE: a working branch c6275044faa (A site with base v27) proofs/omx-clap-core/fuzz_state/lib/A/
   FSH_crt_site.v (= ea635b4653a's blob 2a5eaa1b347, CTX-free, plus v23's Section rom / crt_rom, v24's Sections rtcall /
   rtcalls, and v27's five STK literals read through FSH_crt_base.crt_STK_eq), whose own history is in its section
   comments below. Same Definition / Lemma names, same
   statement shapes, over image B; Requires lib/B/FSH_crt_base.v. Imports: lib.A.X -> lib.B.X where lib/B/X.v exists
   (AB1v -> YB1v, AB1w -> YB1w, AE2k -> YE2k, AF0x -> YF0x, and every FSH_* / FSW_* / FSPstat kit file); SetShadowDefU,
   FSupoison, FSupoisonU, FSH_YC20 and FSH_Gen stay lib/A's, exactly as lib/B/FSW_K.v and lib/B/FSH_Rt.v import them.
   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from c6275044faa lib/A/FSH_crt_site.v)
   rule 24: proves no function (kind: segment lemmas of check_round_trip's walk, PORTED from 1ab57ca7ad7) - crt_rt_call /
   crt_rt_call2 take CrtRt B (crt_fr_strlen / crt_fr_strcmp) (a working branch 1ab57ca7ad7).

   A -> B TABLE (MEASURED on the pinned images, crt.A.s / crt.B.s, mapped by instruction meaning, never by offset). No
   name of this file carries a pc, so every name keeps its A name; these are the facts its statements, proofs and
   comments use:
     fact (where used)                               A (fs.asan)                        B (fs.asan-ubsan)
     check_round_trip entry                           0x81a9c                            0x81b9c
     prologue: 13 saves at s0-8..s0-104, s0 = sp0,   0x81a9c..0x81ae0                   0x81b9c..0x81be0 (same words,
       sp1 = (sp0 - 192) & -32, s1 = sp1                                                  same offsets)
     frame-shadow register SF (crt_csite,             s3 = x19 (0x81b58, 0x81b7c)        s10 = x26 (0x81c54, 0x81c78;
       crt_csite4, crt_call_core, crt_seg_call_full)                                       next write: the epilogue)
     last s1-slot store (crt_cs1 complete)            0x81f9c                            0x820e8
     abort tail every trap arm jumps to                0x824b8 / 0x824bc                  0x824e4 / 0x824e8
       (__asan_handle_no_return / abort)
     own-frame poison stores (crt_seg_call_full's     0x822bc..0x82334, through s3       0x8241c..0x82490 (addi s2, -8
       example segment)                                                                    and 29 sb), through s10
     relro [FS_RLO, FS_RHI) (crt_roP_img,             [0x9f190, 0xa03e8)                 [0x9f6b0, 0xa0908)
       crt_pstat_not_ro)
     tfibsegs segment holding the relro range         [0x9f000, 0xa1000)                 [0x9f000, 0xa1000) (vm_compute of
       (crt_roP_img)                                                                       B's tfibsegs: 4 segments,
                                                                                           relro PT_LOAD 0x9f678 + 0x1988)
     STK_check_round_trip (crt_sb, crt_awr2,          crt_STK (A base v27)               crt_STK (lib/B/FSH_crt_base.v: vm_compute
       crt_call_core, crt_seg_call_full, crt_rt_frame)                                     of STK_check_round_trip; no literal here)
     strlen thunk: call site / PC_strlen              0x81f74 / 0x42654                  0x820c0 / 0x426c4
       (crt_rt_call)
     strcmp thunks: call sites / PC_strcmp            0x82054, 0x82064 / 0x4265c         0x821b0, 0x821c0 / 0x426cc
       (crt_rt_call2) *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import SetShadowDefU FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_K3 FSH_Fn_reader
FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt FSW_frame FSW_frame3 FSW_rres FSW_crt_tbl FSW_strkit FSW_rd FSH_crt_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YE2k YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD: a SUCCESS here (the build errors naming this line) means a wrong sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= the callee-side precondition of a call =================
   What the boundary state and the caller's journal give the callee, with no boundary invariant: its fpreU (the
   donor's afn_pre_at at o = s1 - s0, with crt's own frame record pushed on the chain) and the fake-frame bound FRL_CRT_CALLEE. The data premises of each callee spec (pobj, the trees, the counters)
   are the boundary invariant's and are NOT here. ---- *)

(* every read-only byte arodata_okP speaks of is an image byte: the relro range [FS_RLO, FS_RHI) = [0x9f6b0, 0xa0908)
   lies inside tfibsegs' segment [0x9f000, 0xa1000) (MEASURED on B: vm_compute of tfibsegs gives the four segments
   [0x10000, 0x30000) [0x30000, 0x9f000) [0x9f000, 0xa1000) [0xa1000, 0x5fd000); same argument as
   FSH_crt_base.crt_pstat_img) *)
Lemma crt_roP_img : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> in_img tfibsegs a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr]|].
assert (Hx : existsb (fun s => (Z.of_N (seg_base s) <=? 0x9f000) && (0xa1000 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
  tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hx as (sg & Hin & Hc). apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hin|]. unfold FS_RLO, FS_RHI in Hr. lia.
Qed.
(* the statics' footprint holds no sink token, so the journal's image clause spares nothing of it *)
Lemma crt_sink_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof.
apply sink_closed_pos. unfold FS_PSTAT_FP. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.

(* no read-only byte is a byte of fs's statics: the relro range ends below g_fail_at, and no non-writable segment of
   tfibsegs meets any of the four 8-byte statics (MEASURED by computation over tfibsegs) *)
Lemma crt_pstat_not_ro : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
Proof.
intros a Ha (r & Hr & Hra).
assert (Hseg : forallb (fun sg => seg_writable sg ||
    forallb (fun r => (fst r >=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) || (snd r <=? Z.of_N (seg_base sg)))
      FS_PSTAT_FP) tfibsegs = true) by (vm_compute; reflexivity).
destruct Ha as [(sg & Hin & Hw & Hsg) | Hrel].
- rewrite forallb_forall in Hseg. pose proof (Hseg sg Hin) as Hs. rewrite Hw in Hs. cbn [orb] in Hs.
  rewrite forallb_forall in Hs. pose proof (Hs r Hr) as Hr'. apply orb_true_iff in Hr' as [H1 | H1].
  + apply Z.geb_le in H1. lia.
  + apply Z.leb_le in H1. lia.
- unfold FS_PSTAT_FP, FS_RLO, FS_RHI in *. cbn [In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in Hra; lia|]). destruct Hr.
Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* a byte below the shadow band is no user-poisoned byte of U (FSupoison.ush_facts) *)
Lemma crt_ush_low : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < SHADOW_OFF -> in_ush U (bv_unsigned (Z_to_bv 64 a)) = false.
Proof.
intros ly S U W mem md a H Ha. rewrite (wz a ltac:(unfold SHADOW_OFF in Ha; lia)).
destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
pose proof (ush_facts tfibsegs B ly S U W mem md a H E) as (_ & L & _). lia.
Qed.
(* the read-only image at any state of the walk: the entry's arodata_okP rides through the journal's image clause
   (the relro bytes are image bytes, below the shadow band, not owned statics, not errno, not in FS_PSTAT_FP, and
   FS_PSTAT_FP is sink-closed) *)
Lemma crt_rodata : forall cx k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crt_base B cx ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W3) (ms_mem ms3)).
Proof.
intros cx k ly3 S3 U3 W3 ms3 md3 HB HJ HARU3.
pose proof (proj2 (proj1 HB)) as HRO.
pose proof (fsw_ARU B _ _ _ _ _ _ _ _ _ (proj1 (proj1 HB))) as HARU0.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
intros a Ha Hno Herr.
pose proof (fs_segs_img a (crt_roP_img a Ha)) as Himg.
assert (Hlow : 0 <= a < SHADOW_OFF) by (unfold FS_IMG_END, SHADOW_OFF in *; lia).
rewrite <- (aview_unpoison_out tfibsegs (w_H W3) U3 (ms_mem ms3) a (crt_ush_low _ _ _ _ _ _ a HARU3 Hlow)).
rewrite (F3 a (crt_roP_img a Ha) Hno Herr (crt_pstat_not_ro a Ha)
  (fp_spares_closed FS_PSTAT_FP a crt_sink_closed)).
rewrite (aview_unpoison_out tfibsegs (w_H (c_W cx)) (c_U cx) (c_mem cx) a
  (crt_ush_low _ _ _ _ _ _ a HARU0 Hlow)).
exact (HRO a Ha Hno Herr).
Qed.

(* the two words the prologue saved, read at a boundary: the s0 region's first two chunks *)
Lemma crt_saved_words : forall cx E ss ms (W : world tfibsegs) i,
  crt_E cx E -> st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) i = Some crt_s0_region ->
  rdword (aview tfibsegs (w_H W) (ms_mem ms)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) /\
  rdword (aview tfibsegs (w_H W) (ms_mem ms)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)).
Proof.
intros cx E ss ms W i HE HS Hi.
pose proof (fsw_region_nth E ss (restrict (w_H W) ms) i crt_s0_region HS Hi) as HR.
cbn [ms_mem restrict] in HR.
pose proof HE as (_ & _ & _ & E8v & _).
assert (R1 : ew E 33 = YK11.getr (c_regs cx) 1%bv) by exact (crt_E_saved cx E 0 HE ltac:(lia)).
assert (R8 : ew E 34 = YK11.getr (c_regs cx) 8%bv) by exact (crt_E_saved cx E 1 HE ltac:(lia)).
split.
- apply YF0x.val_mem_rdword; [unfold raZ; apply u64_range|].
  replace (spZ (c_regs cx) - 8) with (spZ (c_regs cx) + (-8)) by lia.
  eapply (fsw_field E (mrestrict (w_H W) (ms_mem ms)) 8%nat (spZ (c_regs cx)) crt_sv_chunks (-104) 0 (-104) 0
    (-8) 8%N (SOff 33 0) (raZ (c_regs cx))).
  + unfold crt_s0_region, fs_ret_s0_region in HR. exact HR.
  + exact E8v.
  + unfold crt_sv_chunks. cbn [seq map]. left. reflexivity.
  + rewrite fsw_SOff0, R1. unfold raZ. symmetry. apply Z_to_bv_bv_unsigned.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold raZ. apply u64_range.
  + cbn. lia.
- apply YF0x.val_mem_rdword; [unfold s0Z; apply u64_range|].
  replace (spZ (c_regs cx) - 16) with (spZ (c_regs cx) + (-16)) by lia.
  eapply (fsw_field E (mrestrict (w_H W) (ms_mem ms)) 8%nat (spZ (c_regs cx)) crt_sv_chunks (-104) 0 (-104) 0
    (-16) 8%N (SOff 34 0) (s0Z (c_regs cx))).
  + unfold crt_s0_region, fs_ret_s0_region in HR. exact HR.
  + exact E8v.
  + unfold crt_sv_chunks. cbn [seq map]. right. left. reflexivity.
  + rewrite fsw_SOff0, R8. unfold s0Z. symmetry. apply Z_to_bv_bv_unsigned.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold s0Z. apply u64_range.
  + cbn. lia.
Qed.

(* ---- the callee-side precondition at a call of the walk ----
   At a call site the machine is at the callee's entry with sp = s1 (crt never moves sp after the re-align), s0 = the
   entry sp, gp / tp the entry's and ra the measured return address. The callee runs with crt's frame record (the saved
   ra at s0 - 8 and the saved s0 at s0 - 16) on top of crt's own chain, so its chain is ch1 below; its spine is crt's
   return address on top of crt's spine. The window: crt's frame drop
   is at most 208 bytes (192 + the re-align's 16), so a callee whose STK + 208 fits STK_check_round_trip gets its whole
   window inside crt's journal window. The room `sp + 32 <= ly_top` the callees are being restated with (owner decision
   00:26Z) follows from crt_base's own. *)
Lemma crt_callee_pre : forall cx k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 STKc,
  crt_base B cx ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  crt_frame_ok cx S3 W3 ms3 ->
  rdword (aview tfibsegs (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview tfibsegs (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  spZ (ms_regs ms3) = crt_sp1 cx -> s0Z (ms_regs ms3) = spZ (c_regs cx) ->
  YK0s.ret_ok (YK11.getr (ms_regs ms3) 1%bv) -> 4096 <= raZ (ms_regs ms3) ->
  YK11.getr (ms_regs ms3) 3%bv = YK11.getr (c_regs cx) 3%bv ->
  YK11.getr (ms_regs ms3) 4%bv = YK11.getr (c_regs cx) 4%bv ->
  0 <= STKc -> STKc + 208 <= STK_check_round_trip ->
  fpreU tfibsegs B STKc ly3 S3 U3 W3 (ms_regs ms3) (ms_mem ms3) md3
    ((spZ (c_regs cx), raZ (c_regs cx), s0Z (c_regs cx)) :: c_ch cx) /\
  spine ((spZ (c_regs cx), raZ (c_regs cx), s0Z (c_regs cx)) :: c_ch cx) = raZ (c_regs cx) :: spine (c_ch cx) /\
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE /\
  spZ (ms_regs ms3) + 32 <= ly_top ly3.
Proof.
intros cx k ly3 S3 U3 W3 ms3 md3 STKc HB HJ HARU3 HFR Hw8 Hw16 Hsp Hs0 Hra Hra4 Hgp Htp HSTKc HSTK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKv : 208 <= STK_check_round_trip) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof HB as ((HPRE0 & HRO0) & Hheads & Hroom & Hfrl & _).
destruct HPRE0 as (HPRE & OK0 & PO0).
destruct HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof HJ as (HARj & Hly3 & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & Hpres3 & Hstk & _).
destruct Hstk as (Hal16 & Hstk0' & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof (fsw_realign_facts (spZ (c_regs cx) - 192) ltac:(lia)
  ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as ((Flo & Fhi) & Fm32 & Fm16).
assert (Hsp1lo : spZ (c_regs cx) - 208 <= crt_sp1 cx) by (unfold crt_sp1; lia).
assert (Hsp1hi : crt_sp1 cx <= spZ (c_regs cx) - 192) by (unfold crt_sp1; lia).
assert (Hsp1m : crt_sp1 cx mod 16 = 0) by (unfold crt_sp1; exact Fm16).
(* crt's frame record on top of crt's chain, read through the journal's memory *)
assert (Hch1 : achain ly3 (aview tfibsegs (w_H W3) (unpoison U3 (ms_mem ms3))) (crt_sp1 cx) (spZ (c_regs cx))
  ((spZ (c_regs cx), raZ (c_regs cx), s0Z (c_regs cx)) :: c_ch cx)).
{ apply (achain_push ly3 (aview tfibsegs (w_H (c_W cx)) (unpoison (c_U cx) (c_mem cx)))).
  - apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ Etop). exact Hch0.
  - lia.
  - intros a Ha. apply F1; lia.
  - rewrite <- Hw8. apply rdword_ext. intros kk Hkk.
    apply (fsw_aview_unpoison_high B ly3 S3 U3 W3 (ms_mem ms3) md3 _ HARU3). lia.
  - rewrite <- Hw16. apply rdword_ext. intros kk Hkk.
    apply (fsw_aview_unpoison_high B ly3 S3 U3 W3 (ms_mem ms3) md3 _ HARU3). lia.
  - exact Hra40.
  - lia.
  - clear - Hal16. Z.div_mod_to_equations. lia.
  - rewrite Etop. lia.
  - lia. }
(* the callee's afn_pre at o = s1 - s0 (YCbq.afn_pre_at) *)
assert (HPRE1 : afn_pre tfibsegs B STKc ly3 S3 W3 (ms_regs ms3) (unpoison U3 (ms_mem ms3)) md3
  ((spZ (c_regs cx), raZ (c_regs cx), s0Z (c_regs cx)) :: c_ch cx)).
{ eapply (afn_pre_at tfibsegs B) with (o := crt_sp1 cx - spZ (c_regs cx)).
  - exact HJ.
  - rewrite Hsp. lia.
  - rewrite Zminus_mod, Hsp1m, Hal16. reflexivity.
  - lia.
  - exact HSTKc.
  - lia.
  - exact Hra.
  - exact Hra4.
  - rewrite Hgp. exact Hgp0.
  - rewrite Htp. exact Htp0.
  - rewrite Hsp, Hs0. exact Hch1. }
pose proof HARU3 as (_ & OK3 & PO3).
split; [split; [split; [exact HPRE1 | split; [exact OK3 | exact PO3]] | exact (crt_rodata cx k ly3 S3 U3 W3 ms3 md3 HB HJ HARU3)]|].
split; [reflexivity|].
split.
- destruct HFR as (Hfrs & _). rewrite Hfrs. cbn [length]. unfold FRL_CHECK, FRL_CRT_CALLEE in *. lia.
- rewrite Hsp, Etop. lia.
Qed.

(* crt's frame record on top of crt's chain: the chain every callee of the walk is entered with *)
Definition crt_ch1 (cx : crt_cx) : list (Z * Z * Z) := (spZ (c_regs cx), raZ (c_regs cx), s0Z (c_regs cx)) :: c_ch cx.
(* the callee-side precondition read off a call-site symbolic state: sp, gp, tp and s0 still the boundary atoms, ra the
   return address literal, the saved words in the s0 region at index 0 *)
Lemma crt_site_pre : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 ss r STKc,
  crt_base B cx -> crt_E cx E ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  crt_frame_ok cx S3 W3 ms3 ->
  st_ok tfibsegs E ss (restrict (w_H W3) ms3) ->
  sr_get (ss_regs ss) 1%bv = SLit r -> sr_get (ss_regs ss) 2%bv = SOff 2 0 ->
  sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
  sr_get (ss_regs ss) 8%bv = SOff 8 0 -> nth_error (ss_mem ss) 0 = Some crt_s0_region ->
  4096 <= r < 2 ^ 64 -> YK0s.ret_ok (Z_to_bv 64 r) ->
  0 <= STKc -> STKc + 208 <= STK_check_round_trip ->
  fpreU tfibsegs B STKc ly3 S3 U3 W3 (ms_regs ms3) (ms_mem ms3) md3 (crt_ch1 cx) /\
  raZ (ms_regs ms3) = r /\
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE /\
  spZ (ms_regs ms3) + 32 <= ly_top ly3.
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 ss r STKc HB HE HJ HARU3 HFR HS G1 G2 G3 G4 G8 G0 Hr Hrok HSTKc HSTK.
pose proof HE as (E2v & E3v & E4v & E8v & _).
assert (R1 : YK11.getr (ms_regs ms3) 1%bv = Z_to_bv 64 r)
  by exact (fsw_reg_lit (w_H W3) E ss ms3 1%bv r HS G1 ltac:(lia)).
assert (R2 : spZ (ms_regs ms3) = crt_sp1 cx)
  by (unfold spZ; rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E ss ms3 2%bv HS), G2, fsw_SOff0; exact E2v).
assert (R3 : YK11.getr (ms_regs ms3) 3%bv = YK11.getr (c_regs cx) 3%bv)
  by (rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E ss ms3 3%bv HS), G3, fsw_SOff0; exact E3v).
assert (R4 : YK11.getr (ms_regs ms3) 4%bv = YK11.getr (c_regs cx) 4%bv)
  by (rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E ss ms3 4%bv HS), G4, fsw_SOff0; exact E4v).
assert (R8 : s0Z (ms_regs ms3) = spZ (c_regs cx))
  by (unfold s0Z; rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E ss ms3 8%bv HS), G8, fsw_SOff0; exact E8v).
assert (Rra : raZ (ms_regs ms3) = r) by (unfold raZ; rewrite R1; apply wz; lia).
destruct (crt_saved_words cx E ss ms3 W3 0 HE HS G0) as (Hw8 & Hw16).
destruct (crt_callee_pre cx k ly3 S3 U3 W3 ms3 md3 STKc HB HJ HARU3 HFR Hw8 Hw16 R2 R8
  ltac:(rewrite R1; exact Hrok) ltac:(rewrite Rra; lia) R3 R4 HSTKc HSTK) as (HP & _ & HF & HR).
split; [exact HP|]. split; [exact Rra|]. split; [exact HF | exact HR].
Qed.
End p.

(* ================= the generic call crossing, its helpers, the trap arms and the keeps =================
   Moved VERBATIM (a Theorem Labs lane, 05:3xZ): a Theorem Labs lane's lib/A/FSH_crt_segC1.v at a working branch 66580485270
   (lines 51-62, 67, 114-123, 142-150, 154-160, 162-431, prefix crtC1 renamed to crt), a Theorem Labs lane's FSH_crt_segC.v there
   (lines 710-726, crtC_no_trap renamed to crt_no_trap), and a Theorem Labs lane's lib/A/FSH_crt_segB.v at
   a working branch e233fcb1d13 (lines 342-432, prefix crtB renamed to crt, in a Section with B).
   crt_seg_call takes ANY callee post P (a fixed-U' post is
   the case P := fpostU ..); crt_seg_call_br first decides the `bnez a0` of a pj_* return. Both fix the slot chunks
   to crt_cs1, so they serve every call after B's last s1-slot store 0x820e8 (A: 0x81f9c). *)
(* ================= the store-free run state =================
   The boundary state crt_ss_ret r crt_cs1 crt_csF without the frame's two regions: a run from it writes only the s0
   words and the s1 slots (both above alloc_ceiling), so its frame_of keeps every byte below alloc_ceiling - the frame,
   its shadow and every heap block (crtB_ss2 / crtB_sub2, FSH_crt_segB.v:126-133). *)
Definition crt_ss2 (r : Z) : sstate :=
  mkSS r sr_atoms [crt_s0_region; crt_slot_region crt_cs1] None
    (mkFacts ((8%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: crt_ret_facts) [] []).
Lemma crt_sub2 : forall r, submem [crt_s0_region; crt_slot_region crt_cs1] (ss_mem (crt_ss_ret r crt_cs1 crt_csF)).
Proof.
intros r. cbn [ss_mem crt_ss_ret fss_ret_s0_args fss_ret_s0_regs crt_ret_regions].
apply submem_keep; [apply subregion_refl|]. apply submem_keep; [apply subregion_refl|]. apply submem_nil.
Qed.

Definition crt_c0 : acond := mkAC BC_EQ (SOff 10 0) (SLit 0).
(* what each call-site state holds (read off the engine's answers): the two regions unchanged (no store), pc the callee,
   ra the return address, sp gp tp s0 s1 and s10 (B's frame-shadow register; A's s3) the boundary atoms, and the
   argument registers *)
Definition crt_csite (ssC : sstate) (A_c r : Z) : Prop :=
  ss_pc ssC = A_c /\ ss_resv ssC = None /\ ss_mem ssC = [crt_s0_region; crt_slot_region crt_cs1] /\
  sr_get (ss_regs ssC) 1%bv = SLit r /\ sr_get (ss_regs ssC) 2%bv = SOff 2 0 /\
  sr_get (ss_regs ssC) 3%bv = SOff 3 0 /\ sr_get (ss_regs ssC) 4%bv = SOff 4 0 /\
  sr_get (ss_regs ssC) 8%bv = SOff 8 0 /\ sr_get (ss_regs ssC) 9%bv = SOff 9 0 /\
  sr_get (ss_regs ssC) 26%bv = SOff 26 0.
Definition crt_site (sb ssC : sstate) (A_c r : Z) : Prop :=
  ss_mem sb = [crt_s0_region; crt_slot_region crt_cs1] /\ crt_csite ssC A_c r.
(* the callee-saved registers s2 .. s11 at each call site are still the boundary atoms (a pj_* call keeps them) *)
Definition crt_ssave (ssC : sstate) : Prop :=
  forall n : nat, (18 <= n <= 27)%nat -> sr_get (ss_regs ssC) (Z_to_bv 5 (Z.of_nat n)) = SOff n 0.
Lemma crt_ssave_dec : forall ssC,
  forallb (fun n => sv_eqb (sr_get (ss_regs ssC) (Z_to_bv 5 (Z.of_nat n))) (SOff n 0)) (seq 18 10) = true ->
  crt_ssave ssC.
Proof.
intros ssC H n Hn. rewrite forallb_forall in H. apply sv_eqb_eq. apply H. apply in_seq. lia.
Qed.
(* the flag address does not move along the walk: ajournal's layout_le keeps ly_F (YG0f.layout_le; segD's crt_FL_ly,
   which is not in the base) *)
Lemma crt_FL_ly : forall cx n ly3, layout_le n (c_ly cx) ly3 -> flag_addr ly3 3 (c_pos cx) = crt_FL cx.
Proof.
intros cx n ly3 Hle. unfold crt_FL, flag_addr.
destruct Hle as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.

(* ================= the trap arms of segment group C are not taken =================
   Each of the group's nine branches tests the callee's answer and jumps to the function's abort tail
   (B: __asan_handle_no_return call 0x824e4, abort call 0x824e8; A: 0x824b8, 0x824bc; MEASURED, e.g. B's `bnez a0` at
   0x82298 after pj_string jumps to 0x824e4). The arm is decided by the boundary invariant's own a0, never by
   an exit: `bnez a0` after a pj_* call that returned 0, `beqz a0` after pj_write / pj_get_str that returned a
   non-null pointer (R2, a Theorem Labs lane 00:37Z: a report site is never a walk exit). *)
Lemma crt_no_trap_ne : forall E, ew E 10 = Z_to_bv 64 0 ->
  branch_taken BC_NE (sv_denot E (SOff 10 0)) (sv_denot E (SLit 0)) = false.
Proof.
intros E H. rewrite branch_ne_U, (U_atom E 10 0 H ltac:(lia)), (U_lit E 0 ltac:(lia)).
cbn. reflexivity.
Qed.
Lemma crt_no_trap_eq : forall E z, ew E 10 = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> z <> 0 ->
  branch_taken BC_EQ (sv_denot E (SOff 10 0)) (sv_denot E (SLit 0)) = false.
Proof.
intros E z H Hz Hnz. rewrite branch_eq_U, (U_atom E 10 z H Hz), (U_lit E 0 ltac:(lia)).
apply Z.eqb_neq. exact Hnz.
Qed.

(* ================= one segment: the `bnez a0`, a store-free run, a PROGRAM call =================
   a Theorem Labs lane's crtB_seg_call (FSH_crt_segB.v:324-451) with the leading branch: the run from crt_ss2 r0 stops at the
   `bnez a0` (SR_branch BC_NE a0 0), the boundary invariant's a0 = 0 decides it (st_ok_add_cond_neg + segC's
   crt_no_trap_ne), a second run reaches the callee A_c, crt_site_pre gives the callee's fpreU, and
   FSH_crt_base.crt_after_call rebuilds the boundary state at the return address r. HCALL is the segment's own part:
   from INV at the boundary memory (kept below alloc_ceiling by both runs) and the call site, the callee's SRr into a
   post P, its FP relation and flag-word safety, and the next boundary's INV' from any P-state. ---- *)
Section walk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* crt's journal from its entry, with its frame (3, pos) as own (crt_from's premise) *)
Definition crt_J (cx : crt_cx) ly3 S3 (W3 : world tfibsegs) mem3 md3 (k : Z) : Prop :=
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 mem3 md3 k.

(* the frame's place: 32-aligned, at or above 4096, below alloc_ceiling, an application range, its shadow inside
   [kLowMemEnd, kHighShadowEnd) (crtB_F_facts) *)
Lemma crt_F_facts : forall cx ly3 S3 U3 (W3 : world tfibsegs) mem3 md3 k,
  crt_J cx ly3 S3 W3 (unpoison U3 mem3) md3 k -> ARU tfibsegs B ly3 S3 U3 W3 mem3 md3 ->
  frames S3 = (3, c_pos cx) :: frames (c_S cx) ->
  crt_F cx mod 32 = 0 /\ 4096 <= crt_F cx /\ crt_F cx + 512 <= alloc_ceiling /\ in_app (crt_F cx) 512 /\
  kLowMemEnd <= crt_SF cx /\ crt_SF cx + 64 <= kHighShadowEnd.
Proof.
intros cx ly3 S3 U3 W3 mem3 md3 k HJ HARU Hfr.
pose proof HJ as (_ & Hly & _).
pose proof (crt_F_ly cx _ ly3 Hly) as EF.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR.
assert (Hin : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (c_pos cx) HAR Hin) as (Hal & Happ & _).
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 3 (c_pos cx) HAR Hin) as (H4096 & Hceil & _).
rewrite EF, crt_frame3 in *. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (shadow_addr_bounds (crt_F cx) ltac:(lia)) as (S1 & _).
pose proof (shadow_addr_bounds (crt_F cx + 511) ltac:(lia)) as (_ & S2).
assert (HS512 : shadow_addr (crt_F cx) + 64 <= shadow_addr (crt_F cx + 511) + 1)
  by (unfold shadow_addr; Z.div_mod_to_equations; lia).
unfold crt_SF. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Happ|]. split; lia.
Qed.

(* the machine state behind a run's st_ok (restrict only replaces the memory) (crtB_mkst) *)
Lemma crt_mkst : forall (H : word -> bool) E ss ms, st_ok tfibsegs E ss (restrict H ms) -> ss_resv ss = None ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom tfibsegs).
Proof.
intros H E ss ms (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & _) Hrv.
destruct ms as [regs fregs pcv pend resv fcsr mem rom]; cbn in *.
rewrite Hrv in Hresv. cbn in Hresv. subst. reflexivity.
Qed.

(* a run whose windows are the s0 words and the s1 slots writes only stack bytes above alloc_ceiling (crtB_sb) *)
Lemma crt_sb : forall cx E (m m' : word -> option byte),
  crt_base B cx -> crt_E cx E -> frame_of E [crt_s0_region; crt_slot_region crt_cs1] m m' ->
  same_below m m' alloc_ceiling.
Proof.
intros cx E m m' HB HE HF x Hx. pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
pose proof HB as (HPRE & _). pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPRE)) as (Hal16 & Hceil0 & H47 & HS0).
pose proof crt_STK_eq as STKv; unfold crt_STK in STKv.
pose proof asan_consts as (C1 & _).
pose proof (fsw_realign_facts (spZ (c_regs cx) - 192) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
  as (F1 & F2 & F3).
assert (Hsp1 : spZ (c_regs cx) - 208 <= crt_sp1 cx <= spZ (c_regs cx) - 192) by (unfold crt_sp1; lia).
apply HF. rewrite (wz x) by lia. intros (r & Hin & Hr). cbn [In] in Hin.
destruct Hin as [<-|[<-|[]]]; cbn [crt_s0_region fs_ret_s0_region crt_slot_region YP09.r_base YP09.r_wlo YP09.r_whi
  base_val] in Hr; [rewrite E8 in Hr | rewrite E9 in Hr]; lia.
Qed.

(* the run's write window [s0 words; s1 slots]: the caller's own stack window *)
Lemma crt_awr2 : forall cx E ly3 S3, crt_base B cx -> crt_E cx E ->
  awr_ok tfibsegs B E [crt_s0_region; crt_slot_region crt_cs1] STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP
    (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)).
Proof.
intros cx E ly3 S3 HB HE. pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
pose proof HB as (HPRE & _). pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPRE)) as (Hal16 & Hceil0 & H47 & HS0).
pose proof crt_STK_eq as STKv; unfold crt_STK in STKv.
pose proof asan_consts as (C1 & _).
pose proof (fsw_realign_facts (spZ (c_regs cx) - 192) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
  as (F1 & F2 & F3).
assert (Hsp1 : spZ (c_regs cx) - 208 <= crt_sp1 cx <= spZ (c_regs cx) - 192) by (unfold crt_sp1; lia).
eapply awr_ok_cons_stack; [reflexivity | exact E8 | cbn; lia | cbn; lia |].
eapply awr_ok_cons_stack_off with (d := crt_sp1 cx - spZ (c_regs cx));
  [reflexivity | rewrite E9; lia | cbn; lia | cbn; lia | apply awr_ok_nil].
Qed.

(* the segment's own part at a PROGRAM call of A_c returning to r, from the call-site state ssC: from INV at the
   boundary memory (kept below alloc_ceiling by the run) and the callee's fpreU, the callee's SRr into ANY post P (a
   spec whose U' is chosen inside its post, as pj_string's `exists a`, instantiates it), its FP relation and
   flag-word safety, and the next boundary's INV' from any P-state *)
Definition crt_hcall (ssC : sstate) (A_c r STKc : Z) (INV INV' : crt_inv) : Prop :=
  forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 regsC memC mdC,
  crt_base B cx -> crt_E cx E -> INV cx E k ly3 S3 U3 W3 ms3 md3 ->
  crt_J cx ly3 S3 W3 (unpoison U3 memC) mdC k -> ARU tfibsegs B ly3 S3 U3 W3 memC mdC ->
  frames S3 = (3, c_pos cx) :: frames (c_S cx) ->
  same_below (ms_mem ms3) memC alloc_ceiling ->
  (forall rr : bv 5, YK11.getr regsC rr = sv_denot E (sr_get (ss_regs ssC) rr)) ->
  fpreU tfibsegs B STKc ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) ->
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE ->
  spZ regsC + 32 <= ly_top ly3 ->
  exists FPc kc (P : world tfibsegs -> config -> Prop),
    SRr tfibsegs W3 (cfg_at tfibsegs A_c regsC memC mdC) P /\
    fsw_fp_sub B (c_ly cx) (c_S cx) ly3 S3 [(3, c_pos cx)] FS_PSTAT_FP FPc /\
    (forall a, crt_F cx + fs_frame_bytes 3 - 8 <= a < crt_F cx + fs_frame_bytes 3 -> ~ inFP FPc a) /\
    (forall W' c', P W' c' -> exists ly' S' U' regs' mem' md',
       c' = mkCfg (mkst regs' (YK11.getr regsC 1%bv) mem' (seg_rom tfibsegs)) md' /\
       ajournal tfibsegs B STKc (spZ regsC) FPc ly3 S3 W3 (unpoison U3 memC) mdC [] ly' S' W'
         (unpoison U' mem') md' kc /\
       upoison_ok B ly' S' U' /\ upoisoned tfibsegs W' mem' U' /\ aregs_preserved regsC regs' /\
       (crt_J cx ly' S' W' (unpoison U' mem') md' (k + kc) -> ARU tfibsegs B ly' S' U' W' mem' md' ->
        INV' cx (Ereg regs' (crt_extra cx)) (k + kc) ly' S' U' W' (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))
          md')).

(* the call and the return: from the call-site machine state ms (reached by store-free runs from the boundary
   state ms3, so every byte below alloc_ceiling is ms3's), crt_site_pre, HCALL, crt_after_call, then the walk from r *)
Lemma crt_call_core : forall ssC A_c r (INV INV' : crt_inv) STKc cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3
  ms mdC,
  crt_csite ssC A_c r -> 4096 <= r < 2 ^ 64 -> r mod 2 = 0 -> 0 <= STKc -> STKc + 208 <= STK_check_round_trip ->
  crt_hcall ssC A_c r STKc INV INV' ->
  crt_from SK B (crt_ss_ret r crt_cs1 crt_csF) INV' ->
  crt_base B cx -> crt_E cx E -> crt_frame_ok cx S3 W3 ms3 -> INV cx E k ly3 S3 U3 W3 ms3 md3 ->
  st_ok tfibsegs E ssC (restrict (w_H W3) ms) ->
  crt_J cx ly3 S3 W3 (unpoison U3 (ms_mem ms)) mdC k -> ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) mdC ->
  same_below (ms_mem ms3) (ms_mem ms) alloc_ceiling ->
  SRr tfibsegs W3 (mkCfg ms mdC) (crt_post SK B cx).
Proof.
intros ssC A_c r INV INV' STKc cx E k ly3 S3 U3 W3 ms3 md3 ms mdC HCS Hr Hr2 HSTKc HSTK HCALL NEXT
  HB HE HFO HINV HSC HJC HARUC HSB.
destruct HCS as (Hpc & Hres & Hmem & G1 & G2 & G3 & G4 & G8 & G9 & G26).
pose proof HFO as (Hfr & Hnin & Hflag).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HPRE & _). pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPRE)) as (Hal16 & Hceil0 & H47 & HS0).
pose proof (fsw_realign_facts (spZ (c_regs cx) - 192) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
  as (F1 & F2 & F3).
assert (Hsp1 : spZ (c_regs cx) - 208 <= crt_sp1 cx <= spZ (c_regs cx) - 192) by (unfold crt_sp1; lia).
pose proof crt_STK_eq as STKv; unfold crt_STK in STKv.
pose proof (crt_mkst (w_H W3) E ssC ms HSC Hres) as Ems. rewrite Hpc in Ems.
set (regsC := ms_regs ms) in *. set (memC := ms_mem ms) in *.
assert (RG : forall rr : bv 5, YK11.getr regsC rr = sv_denot E (sr_get (ss_regs ssC) rr))
  by (intros rr; exact (st_ok_restrict_reg tfibsegs (w_H W3) E ssC ms rr HSC)).
assert (R1 : YK11.getr regsC 1%bv = Z_to_bv 64 r) by (rewrite RG, G1; reflexivity).
assert (R2 : YK11.getr regsC 2%bv = ew E 2) by (rewrite RG, G2; apply fsw_SOff0).
assert (R3 : YK11.getr regsC 3%bv = ew E 3) by (rewrite RG, G3; apply fsw_SOff0).
assert (R4 : YK11.getr regsC 4%bv = ew E 4) by (rewrite RG, G4; apply fsw_SOff0).
assert (R8 : YK11.getr regsC 8%bv = ew E 8) by (rewrite RG, G8; apply fsw_SOff0).
assert (R9 : YK11.getr regsC 9%bv = ew E 9) by (rewrite RG, G9; apply fsw_SOff0).
assert (R26 : YK11.getr regsC 26%bv = ew E 26) by (rewrite RG, G26; apply fsw_SOff0).
assert (HR0 : region_ok tfibsegs E (mrestrict (w_H W3) memC) crt_s0_region)
  by exact (fsw_region_nth E ssC (restrict (w_H W3) ms) 0 crt_s0_region HSC ltac:(rewrite Hmem; reflexivity)).
assert (HRs : region_ok tfibsegs E (mrestrict (w_H W3) memC) (crt_slot_region crt_cs1))
  by exact (fsw_region_nth E ssC (restrict (w_H W3) ms) 1 (crt_slot_region crt_cs1) HSC ltac:(rewrite Hmem; reflexivity)).
destruct (crt_F_facts cx _ _ _ _ _ _ _ HJC HARUC Hfr) as (Hal & H4096 & Hceil & Happ & Hs1 & Hs2).
assert (Hflag' : rdword (aview tfibsegs (w_H W3) memC) (crt_F cx + fs_frame_bytes 3 - 8) = Some (crt_FL cx)).
{ rewrite <- Hflag. apply rdword_ext. intros i Hi. rewrite crt_frame3 in *.
  exact (aview_below (w_H W3) (ms_mem ms3) memC alloc_ceiling (crt_F cx + 512 - 8 + i) HSB ltac:(lia)). }
assert (Hrok : YK0s.ret_ok (Z_to_bv 64 r)) by (apply ret_ok_even; rewrite (wz r) by lia; exact Hr2).
(* the callee's precondition at the call site (FSH_crt_site.crt_site_pre) *)
destruct (crt_site_pre SK B cx E k ly3 S3 U3 W3 ms mdC ssC r STKc HB HE HJC HARUC (conj Hfr (conj Hnin Hflag'))
  HSC G1 G2 G3 G4 G8 ltac:(rewrite Hmem; reflexivity) Hr Hrok HSTKc HSTK) as (HPREc & _ & HFRL & HTOPc).
rewrite Ems. change (mkCfg (mkst regsC (Z_to_bv 64 A_c) memC (seg_rom tfibsegs)) mdC)
  with (cfg_at tfibsegs A_c regsC memC mdC).
destruct (HCALL cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HSB RG HPREc HFRL HTOPc)
  as (FPc & kc & P & HSRr & HFP & HFL & HK).
eapply SRr_bind; [exact HSRr|].
intros W' c' Hle HPc.
destruct (HK W' c' HPc) as (ly' & S' & U' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP & HINV').
rewrite R1.
(* the call-site facts in the form of FSH_crt_base.crt_after_call, the walk's one program-call step *)
assert (V : forall n z, bv_unsigned (ew E n) = z -> 0 <= z < 2 ^ 64 -> ew E n = Z_to_bv 64 z)
  by (intros n z Hz Hr64; apply bv_eq; rewrite Hz; symmetry; apply wz; exact Hr64).
assert (Esp : spZ regsC = crt_sp1 cx) by (unfold spZ; rewrite R2; exact E2).
assert (HSV : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memC) (spZ (c_regs cx))) crt_sv_chunks).
{ destruct HR0 as (_ & _ & _ & Hc). cbn [crt_s0_region fs_ret_s0_region YP09.r_base YP09.r_chunks base_val] in Hc.
  rewrite E8 in Hc. exact Hc. }
assert (HCS1 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memC) (crt_sp1 cx)) crt_cs1).
{ destruct HRs as (_ & _ & _ & Hc). cbn [crt_slot_region YP09.r_base YP09.r_chunks base_val] in Hc.
  rewrite E9 in Hc. exact Hc. }
assert (HCSF : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memC) (crt_F cx)) crt_csF).
{ pose proof (al_flag _ _ LAWS _ _ _ _ _ 3 (c_pos cx) (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC)
    ltac:(rewrite Hfr; left; reflexivity)) as (_ & _ & Hflapp & Hflc).
  pose proof HJC as (_ & HlyC & _).
  rewrite (crt_FL_ly cx _ ly3 HlyC) in Hflapp, Hflc.
  unfold crt_csF. rewrite crt_frame3. constructor; [|constructor].
  apply (chunk_ok_val tfibsegs E _ (crt_F cx) (512 - 8) 8 (SOff 46 0) (crt_FL cx));
    [rewrite fsw_SOff0; exact (crt_E_FL cx E HE) | unfold in_app in Hflapp; change (8 * Z.of_N 8) with 64; lia
    | cbn; lia |].
  replace (crt_F cx + (512 - 8)) with (crt_F cx + fs_frame_bytes 3 - 8) by (rewrite crt_frame3; lia).
  exact (val_mem_of_rdword tfibsegs (w_H W3) memC _ _ Hflag'). }
rewrite Esp in HJc.
assert (Q2 : YK11.getr regsC 2%bv = Z_to_bv 64 (crt_sp1 cx)) by (rewrite R2; apply V; [exact E2 | lia]).
assert (Q3 : YK11.getr regsC 3%bv = YK11.getr (c_regs cx) 3%bv) by (rewrite R3; exact E3).
assert (Q4 : YK11.getr regsC 4%bv = YK11.getr (c_regs cx) 4%bv) by (rewrite R4; exact E4).
assert (Q8 : YK11.getr regsC 8%bv = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite R8; apply V; [exact E8 | lia]).
assert (Q9 : YK11.getr regsC 9%bv = Z_to_bv 64 (crt_sp1 cx)) by (rewrite R9; apply V; [exact E9 | lia]).
assert (Q26 : YK11.getr regsC 26%bv = Z_to_bv 64 (crt_SF cx))
  by (rewrite R26; apply V; [exact E26 | unfold crt_SF, kLowMemEnd, kHighShadowEnd in *; lia]).
assert (HcsFin : Forall (fun c => 0 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= fs_frame_bytes 3)
  crt_csF) by (unfold crt_csF; rewrite crt_frame3; apply Forall_cons; [cbn; lia | apply Forall_nil]).
assert (HcsFat : crt_atom_chunks crt_csF)
  by (unfold crt_atom_chunks, crt_csF; apply Forall_cons; [do 4 eexists; split; [reflexivity | lia] | apply Forall_nil]).
assert (HcsFnf : forall c, In c crt_csF -> forall i, 0 <= i < YP09.c_len c -> ~ inFP FPc (crt_F cx + YP09.c_off c + i)).
{ intros c Hc i Hi. unfold crt_csF in Hc. destruct Hc as [<-|[]]. cbn in Hi. apply HFL. cbn. rewrite crt_frame3. lia. }
assert (HflNF : forall i, 0 <= i < 8 -> ~ inFP FPc (crt_F cx + fs_frame_bytes 3 - 8 + i)) by (intros i Hi; apply HFL; lia).
destruct (crt_after_call (SKfp := SK) B cx E k ly3 S3 U3 W3 (mkst regsC (Z_to_bv 64 A_c) memC (seg_rom tfibsegs)) mdC
  STKc FPc ly' S' U' W' regs' mem' md' kc r crt_csF HE HJC HARUC (conj Hfr (conj Hnin Hflag'))
  Q2 Q3 Q4 Q8 Q9 Q26 HSV HCS1 HCSF HcsFin HcsFat HcsFnf HflNF HJc OK' PO' HFP HP HSTKc ltac:(lia))
  as (HJ' & HARU' & HFO' & HE' & HS').
exact (NEXT cx (Ereg regs' (crt_extra cx)) (k + kc) ly' S' U' W' (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))
  md' HB HE' HJ' HARU' HFO' (HINV' HJ' HARU') HS').
Qed.

(* one segment with no branch: a store-free run from the boundary at r0 to a PROGRAM call (crtB_seg_call's shape,
   with the generic post) *)
Lemma crt_seg_call : forall r0 A_c r ssC (INV INV' : crt_inv) STKc,
  sym_run_toN tfibsegs crt_tbl FUEL A_c (crt_ss2 r0) = (ssC, RS_running) ->
  crt_csite ssC A_c r -> 4096 <= r < 2 ^ 64 -> r mod 2 = 0 ->
  0 <= STKc -> STKc + 208 <= STK_check_round_trip ->
  crt_hcall ssC A_c r STKc INV INV' ->
  crt_from SK B (crt_ss_ret r crt_cs1 crt_csF) INV' ->
  crt_from SK B (crt_ss_ret r0 crt_cs1 crt_csF) INV.
Proof.
intros r0 A_c r ssC INV INV' STKc HRUN HCS Hr Hr2 HSTKc HSTK HCALL NEXT.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFO HINV HS.
pose proof (st_ok_submem tfibsegs E _ _ _ HS (crt_sub2 r0) ltac:(vm_compute; reflexivity)) as HS2.
change (st_ok tfibsegs E (crt_ss2 r0) (restrict (w_H W3) ms3)) in HS2.
eapply (fsw_run_to_AJU B crt_tbl crt_tbl_ok W3 FUEL A_c E (crt_ss2 r0) ssC RS_running ms3
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS2 HRUN I HARU HJ (crt_awr2 cx E ly3 S3 HB HE)).
intros ms mat HSC HJC HARUC HF HFr HG.
exact (crt_call_core ssC A_c r INV INV' STKc cx E k ly3 S3 U3 W3 ms3 md3 ms _ HCS Hr Hr2 HSTKc HSTK HCALL NEXT
  HB HE HFO HINV HSC HJC HARUC (crt_sb cx E _ _ HB HE HF)).
Qed.

(* one segment after a pj_* return: the `bnez a0` (not taken, a0 = 0), then the store-free run to the call *)
Lemma crt_seg_call_br : forall r0 A_c r sb ssC (INV INV' : crt_inv) STKc,
  sym_runN tfibsegs crt_tbl FUEL (crt_ss2 r0) = (sb, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))) ->
  sym_run_toN tfibsegs crt_tbl FUEL A_c (add_cond sb crt_c0) = (ssC, RS_running) ->
  crt_site sb ssC A_c r -> 4096 <= r < 2 ^ 64 -> r mod 2 = 0 ->
  0 <= STKc -> STKc + 208 <= STK_check_round_trip ->
  (forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3, INV cx E k ly3 S3 U3 W3 ms3 md3 -> ew E 10 = Z_to_bv 64 0) ->
  crt_hcall ssC A_c r STKc INV INV' ->
  crt_from SK B (crt_ss_ret r crt_cs1 crt_csF) INV' ->
  crt_from SK B (crt_ss_ret r0 crt_cs1 crt_csF) INV.
Proof.
intros r0 A_c r sb ssC INV INV' STKc HRUN1 HRUN2 (Hmem1 & HCS) Hr Hr2 HSTKc HSTK HZ HCALL NEXT.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFO HINV HS.
assert (AWR : forall ssx, ss_mem ssx = [crt_s0_region; crt_slot_region crt_cs1] ->
  awr_ok tfibsegs B E (ss_mem ssx) STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP
    (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)))
  by (intros ssx Hx; rewrite Hx; exact (crt_awr2 cx E ly3 S3 HB HE)).
pose proof (st_ok_submem tfibsegs E _ _ _ HS (crt_sub2 r0) ltac:(vm_compute; reflexivity)) as HS2.
change (st_ok tfibsegs E (crt_ss2 r0) (restrict (w_H W3) ms3)) in HS2.
(* run 1: to the `bnez a0` *)
eapply (fsw_run_AJU B crt_tbl crt_tbl_ok W3 FUEL E (crt_ss2 r0) sb _ ms3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  HS2 HRUN1 I HARU HJ (AWR (crt_ss2 r0) eq_refl)).
intros ms1 mat1 HS1 HJ1 HARU1 HF1 HFr1 HG1.
(* the not-taken arm: a0 = 0 *)
pose proof (st_ok_add_cond_neg tfibsegs E sb _ BC_NE (SOff 10 0) (SLit 0) HS1
  (crt_no_trap_ne E (HZ _ _ _ _ _ _ _ _ _ HINV))) as HS1c.
change (add_cond sb (mkAC (neg_bc BC_NE) (SOff 10 0) (SLit 0))) with (add_cond sb crt_c0) in HS1c.
(* run 2: to the callee *)
eapply (fsw_run_to_AJU B crt_tbl crt_tbl_ok W3 FUEL A_c E (add_cond sb crt_c0) ssC RS_running ms1
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS1c HRUN2 I HARU1 HJ1 (AWR (add_cond sb crt_c0) Hmem1)).
intros ms mat HSC HJC HARUC HF HFr HG.
assert (HF1' : frame_of E [crt_s0_region; crt_slot_region crt_cs1] (ms_mem ms3) (ms_mem ms1)) by exact HF1.
assert (HF' : frame_of E [crt_s0_region; crt_slot_region crt_cs1] (ms_mem ms1) (ms_mem ms))
  by (rewrite <- Hmem1; exact HF).
exact (crt_call_core ssC A_c r INV INV' STKc cx E k ly3 S3 U3 W3 ms3 md3 ms _ HCS Hr Hr2 HSTKc HSTK HCALL NEXT
  HB HE HFO HINV HSC HJC HARUC
  (same_below_trans _ _ _ _ (crt_sb cx E _ _ HB HE HF1') (crt_sb cx E _ _ HB HE HF'))).
Qed.
End walk.

Section keep. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* ================= what a callee's journal keeps, on the MACHINE's memories =================
   ajournal's clauses speak of `unpoison U mem`; the boundary invariant's data facts (fs_rblock, zbytes_at, cstr_ok,
   rtree, pobj) are read on the machine's memory. For an APPLICATION byte (a live block's byte, a frame byte) the two
   readings agree (FSW_strkit.unpoison_app: no application address is a user-poisoned shadow byte), and for a frame's
   SHADOW byte they agree because a live frame's shadow is not runtime-owned (AR_frames_law) and U holds only owned
   bytes (FSupoison.ush_facts), i.e. FSW_frame.fsw_unpoison_notowned. These three lemmas are the raw-memory forms of
   ajournal's block clause, frame clause and frame-shadow clause. ---- *)
Lemma crt_raw_of_unp : forall ly S U (W : world tfibsegs) mem md ly' S' U' (W' : world tfibsegs) mem' md' a,
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  0 <= a < 2 ^ 64 -> (a < SHADOW_OFF \/ kHighMemBeg <= a) ->
  aview tfibsegs (w_H W') (unpoison U' mem') a = aview tfibsegs (w_H W) (unpoison U mem) a ->
  aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a.
Proof.
intros ly S U W mem md ly' S' U' W' mem' md' a HARU HARU' Ha Happ H.
rewrite <- (aview_at tfibsegs (w_H W') _ _ a (unpoison_app B ly' S' U' W' mem' md' a HARU' Ha Happ)).
rewrite <- (aview_at tfibsegs (w_H W) _ _ a (unpoison_app B ly S U W mem md a HARU Ha Happ)).
exact H.
Qed.
(* a byte of a block live at both ends, outside the callee's footprint *)
Lemma crt_keep_blk : forall lyc Sc Uc (W : world tfibsegs) memC mdC ly' S' U' (W' : world tfibsegs) mem' md'
  STKc sp1 FPc kc p n i,
  ARU tfibsegs B lyc Sc Uc W memC mdC -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  @ajournal rc SK tfibsegs B STKc sp1 FPc lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FPc (p + i) ->
  aview tfibsegs (w_H W') mem' (p + i) = aview tfibsegs (w_H W) memC (p + i).
Proof.
intros lyc Sc Uc W memC mdC ly' S' U' W' mem' md' STKc sp1 FPc kc p n i HARU HARU' HJ Hin Hin' Hi Hnf.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) Hin)
  as (_ & H4096 & Hceil & Happ & _).
cbv [in_app kLowShadowBeg kHighMemBeg] in Happ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K2 & _).
apply (crt_raw_of_unp lyc Sc Uc W memC mdC ly' S' U' W' mem' md' (p + i) HARU HARU').
- pose proof (@alloc_ceiling_lt rc) as HC47.
  change (2 ^ 47) with 140737488355328 in HC47. change (2 ^ 64) with 18446744073709551616. lia.
- cbv [SHADOW_OFF kHighMemBeg]. lia.
- exact (K2 p n i Hin Hin' Hi Hnf).
Qed.
(* a byte of a frame live at the call, outside the callee's footprint *)
Lemma crt_keep_frm : forall lyc Sc Uc (W : world tfibsegs) memC mdC ly' S' U' (W' : world tfibsegs) mem' md'
  STKc sp1 FPc kc cid pos a,
  ARU tfibsegs B lyc Sc Uc W memC mdC -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  @ajournal rc SK tfibsegs B STKc sp1 FPc lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  In (cid, pos) (frames Sc) -> in_zr a (frame_rng lyc (cid, pos)) -> ~ inFP FPc a ->
  aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) memC a.
Proof.
intros lyc Sc Uc W memC mdC ly' S' U' W' mem' md' STKc sp1 FPc kc cid pos a HARU HARU' HJ Hin Ha Hnf.
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ cid pos (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) Hin)
  as (H4096 & Hceil & Happ).
pose proof Ha as Ha'. unfold in_zr, frame_rng in Ha'. cbn [fst snd] in Ha'.
cbv [in_app kLowShadowBeg kHighMemBeg] in Happ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K4 & _).
apply (crt_raw_of_unp lyc Sc Uc W memC mdC ly' S' U' W' mem' md' a HARU HARU').
- pose proof (@alloc_ceiling_lt rc) as HC47.
  change (2 ^ 47) with 140737488355328 in HC47. change (2 ^ 64) with 18446744073709551616. lia.
- cbv [SHADOW_OFF kHighMemBeg]. lia.
- exact (K4 cid pos a Hin (or_introl Ha) Hnf).
Qed.
(* a SHADOW byte of a frame live at the call and after it, outside the callee's footprint (the shadow is no
   application byte: it is bridged by the frame's own not-owned fact at both ends, AR_frames_law) *)
Lemma crt_keep_fsh : forall lyc Sc Uc (W : world tfibsegs) memC mdC ly' S' U' (W' : world tfibsegs) mem' md'
  STKc sp1 FPc kc cid pos o,
  ARU tfibsegs B lyc Sc Uc W memC mdC -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  @ajournal rc SK tfibsegs B STKc sp1 FPc lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  In (cid, pos) (frames Sc) -> 0 <= o < fs_frame_bytes cid / 8 ->
  ~ inFP FPc (shadow_addr (frame_addr lyc cid pos) + o) ->
  aview tfibsegs (w_H W') mem' (shadow_addr (frame_addr lyc cid pos) + o) =
  aview tfibsegs (w_H W) memC (shadow_addr (frame_addr lyc cid pos) + o).
Proof.
intros lyc Sc Uc W memC mdC ly' S' U' W' mem' md' STKc sp1 FPc kc cid pos o HARU HARU' HJ Hin Ho Hnf.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & K4 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) Hin) as (_ & _ & _ & Hsp).
destruct (Hsp o Ho) as (_ & Hno).
assert (Hin' : In (cid, pos) (frames S')) by (rewrite Hfrs; exact Hin).
assert (Efr : frame_addr ly' cid pos = frame_addr lyc cid pos)
  by (unfold frame_addr; destruct Hly as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos (ARU_AR tfibsegs B _ _ _ _ _ _ HARU') Hin') as (_ & _ & _ & Hsp').
rewrite Efr in Hsp'. destruct (Hsp' o Ho) as (_ & Hno').
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ cid pos (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) Hin)
  as (H4096 & Hceil & _).
pose proof (@alloc_ceiling_lt rc) as HC47. change (2 ^ 47) with 140737488355328 in HC47.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(cbv [kHighMemEnd]; lia)) as (S1 & S2).
cbv [kLowMemEnd kHighShadowEnd] in S1, S2.
assert (Hsh : 0 <= shadow_addr (frame_addr lyc cid pos) + o < 2 ^ 64)
  by (change (2 ^ 64) with 18446744073709551616; lia).
rewrite <- (aview_at tfibsegs (w_H W') _ _ _
  (fsw_unpoison_notowned B ly' S' U' W' mem' md' _ HARU' Hsh Hno')).
rewrite <- (aview_at tfibsegs (w_H W) _ _ _
  (fsw_unpoison_notowned B lyc Sc Uc W memC mdC _ HARU Hsh Hno)).
exact (K4 cid pos (shadow_addr (frame_addr lyc cid pos) + o) Hin
  ltac:(right; unfold in_zr; cbn [fst snd]; lia) Hnf).
Qed.
End keep.

(* ================= pj_set's `rd_sum Dold0 <= live` from an exact live equation (a Theorem Labs lane's text, renamed,
   a working branch d00c16dd751) =================
   An object node's block list starts with its own arrays (PjStruct.pj_node, JObj arm), every block of a tree is a
   reader block with a positive request (FSH_Gen.fs_rblock), and g_live's other terms are >= 0. *)
Lemma crt_rd_sum_app : forall l1 l2, rd_sum (l1 ++ l2) = rd_sum l1 + rd_sum l2.
Proof.
intros l1 l2. induction l1 as [|b l1 IH]; [reflexivity|].
cbn [app]. unfold rd_sum in *. cbn [fold_right]. rewrite IH. lia.
Qed.
(* the object's own arrays head its block list: kids / keys / cap read off any header of the same node *)
Lemma crt_dold0_split : forall m lblk o ms D num str kids keys n cap,
  PjStruct.pj_node tfibsegs m lblk o (PjTree.JObj ms) D ->
  PjStruct.pj_hdr tfibsegs m o 6 num str kids keys n cap ->
  exists Di, D = (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap) ++ Di.
Proof.
intros m lblk o ms D num str kids keys n cap H Hh.
cbn [PjStruct.pj_node] in H.
destruct H as (_ & _ & num' & str' & kids' & keys' & n' & cap' & Hh' & _ & _ & _ & _ & Di & ED & _).
pose proof Hh as (_ & _ & _ & _ & K1 & Y1 & _ & C1).
pose proof Hh' as (_ & _ & _ & _ & K2 & Y2 & _ & C2).
rewrite <- (PjStruct.pj_u64_uniq tfibsegs m _ _ _ K1 K2), <- (PjStruct.pj_u64_uniq tfibsegs m _ _ _ Y1 Y2),
  <- (PjStruct.pj_u64_uniq tfibsegs m _ _ _ C1 C2) in ED.
exists Di. rewrite ED. unfold ReaderRes.kids_blk, ReaderRes.keys_blk. destruct (cap =? 0); reflexivity.
Qed.

Section rdsum. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

Lemma crt_rbo_app : forall ly S (W : world tfibsegs) mem l1 l2,
  rd_blocks_ok tfibsegs B ly S W mem (l1 ++ l2) ->
  rd_blocks_ok tfibsegs B ly S W mem l1 /\ rd_blocks_ok tfibsegs B ly S W mem l2.
Proof.
intros ly S W mem l1 l2 H. split; intros a k Ha; apply H; apply in_or_app; [left | right]; exact Ha.
Qed.
Lemma crt_rd_sum_pos : forall ly S (W : world tfibsegs) mem D, rd_blocks_ok tfibsegs B ly S W mem D -> 0 <= rd_sum D.
Proof.
intros ly S W mem D. induction D as [|[p k] D IH]; intros H; [unfold rd_sum; cbn; lia|].
assert (Hk : 0 < k) by (destruct (H p k (or_introl eq_refl)) as (_ & _ & Hk & _); exact Hk).
assert (HD : rd_blocks_ok tfibsegs B ly S W mem D) by (intros a k' Ha; exact (H a k' (or_intror Ha))).
specialize (IH HD). unfold rd_sum in IH |- *. cbn [fold_right snd]. lia.
Qed.
(* g_live at crt's entry is not negative (crt_base's fs_stat, its 17th conjunct) *)
Lemma crt_live0 : forall cx, crt_base B cx -> 0 <= c_live cx.
Proof.
intros cx HB.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (peak & HG) & _).
pose proof HG as (_ & _ & _ & _ & HL & _). lia.
Qed.
(* the generic form: obj's own arrays are blocks of its tree, and its tree's blocks are among those g_live counts *)
Lemma crt_dold0_le : forall ly S (W : world tfibsegs) mem o ms D num str kids keys n cap live L0 Dl Dr,
  rtree tfibsegs B ly S W mem o (PjTree.JObj ms) D ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) mem) o 6 num str kids keys n cap ->
  rd_blocks_ok tfibsegs B ly S W mem (Dl ++ Dr) -> 0 <= L0 ->
  live = L0 + rd_sum (Dl ++ D ++ Dr) ->
  rd_sum (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap) <= live.
Proof.
intros ly S W mem o ms D num str kids keys n cap live L0 Dl Dr HT Hh HB HL0 ->.
destruct HT as (HN & HBk & _).
destruct (crt_dold0_split _ _ _ _ _ _ _ _ _ _ _ HN Hh) as (Di & ED).
destruct (crt_rbo_app _ _ _ _ _ _ HB) as (HBl & HBr).
rewrite ED in HBk. destruct (crt_rbo_app _ _ _ _ _ _ HBk) as (_ & HBi).
pose proof (crt_rd_sum_pos _ _ _ _ _ HBl) as P1. pose proof (crt_rd_sum_pos _ _ _ _ _ HBr) as P2.
pose proof (crt_rd_sum_pos _ _ _ _ _ HBi) as P3.
rewrite ED, !crt_rd_sum_app. lia.
Qed.
End rdsum.

(* moved VERBATIM from a Theorem Labs lane's lib/A/FSH_crt_segD2.v at a working branch aa2bcfdd59d, lines 768-960 *)
(* ================= crt_seg_call_full: the call crossing of a segment whose run WRITES ITS OWN FRAME =================
   Owner decision (a Theorem Labs lane, 05:4xZ): `crt_seg_call` (this file) runs from `crt_ss2 r0`, which carries
   only the saved words and the s1 slots. A segment that stores into its own frame or its frame's SHADOW - lane D2's
   segment 36 (B: `addi s2, zero, -8` and the 29 `sb s2, off(s10)` stores at 0x8241c..0x82490 that poison the frame's
   objects through s10 = atom 26; A: 0x822bc..0x82334 through s3 = atom 19), group B1's segment 12, group A0's
   segment 1 - cannot run there at all: the engine has no region to
   store into. This section is `crt_call_core` / `crt_seg_call` at a call-site state with the FOUR-region memory of
   `crt_ss_ret`, with two changes and no others:
     (1) `crt_csite`'s `ss_mem ssC = [crt_s0_region; crt_slot_region crt_cs1]` becomes three `nth_error` facts, so
         the frame and shadow regions may be there (and the frame's may have been written);
     (2) the run is a HYPOTHESIS in the journal-step shape that FSH_crt_segD.v's `crt_seg36_run` already has, not
         `sym_run_toN .. (crt_ss2 r0)`; and `crt_hcall`'s `same_below .. alloc_ceiling` - which such a run breaks,
         because a frame's shadow lies below alloc_ceiling - becomes the two `frame_of` facts the run does give.
   Everything after the run is unchanged, because `crt_after_call` reads the frame's chunks from `st_ok` at the CALL
   state: the flag word at F + 504 is region 2's chunk there, so it needs no `same_below`.
   This section holds no name of lane D2 (on A it was moved verbatim into lib/A/FSH_crt_site.v). ============ *)
Section full. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* the call-site state, with the frame (and possibly a shadow region) still present *)
Definition crt_csite4 (ssC : sstate) (A_c r : Z) : Prop :=
  ss_pc ssC = A_c /\ ss_resv ssC = None /\
  nth_error (ss_mem ssC) 0 = Some crt_s0_region /\
  nth_error (ss_mem ssC) 1 = Some (crt_slot_region crt_cs1) /\
  nth_error (ss_mem ssC) 2 = Some (crt_frame_region crt_csF) /\
  sr_get (ss_regs ssC) 1%bv = SLit r /\ sr_get (ss_regs ssC) 2%bv = SOff 2 0 /\
  sr_get (ss_regs ssC) 3%bv = SOff 3 0 /\ sr_get (ss_regs ssC) 4%bv = SOff 4 0 /\
  sr_get (ss_regs ssC) 8%bv = SOff 8 0 /\ sr_get (ss_regs ssC) 9%bv = SOff 9 0 /\
  sr_get (ss_regs ssC) 26%bv = SOff 26 0.

(* the segment's own part, as crt_hcall but with the run's two frame_of facts in place of same_below *)
Definition crt_hcall_full (ss0 ssC : sstate) (A_c r STKc : Z) (INV INV' : crt_inv) : Prop :=
  forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 regsC memC mdC,
  crt_base B cx -> crt_E cx E -> INV cx E k ly3 S3 U3 W3 ms3 md3 ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 memC) mdC k -> ARU tfibsegs B ly3 S3 U3 W3 memC mdC ->
  frames S3 = (3, c_pos cx) :: frames (c_S cx) ->
  frame_of E (ss_mem ss0) (ms_mem ms3) memC ->
  frame_of E (ss_mem ss0) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) memC) ->
  (forall rr : bv 5, YK11.getr regsC rr = sv_denot E (sr_get (ss_regs ssC) rr)) ->
  fpreU tfibsegs B STKc ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) ->
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE ->
  spZ regsC + 32 <= ly_top ly3 ->
  exists FPc kc (P : world tfibsegs -> config -> Prop),
    SRr tfibsegs W3 (cfg_at tfibsegs A_c regsC memC mdC) P /\
    fsw_fp_sub B (c_ly cx) (c_S cx) ly3 S3 [(3, c_pos cx)] FS_PSTAT_FP FPc /\
    (forall a, crt_F cx + fs_frame_bytes 3 - 8 <= a < crt_F cx + fs_frame_bytes 3 -> ~ inFP FPc a) /\
    (forall W' c', P W' c' -> exists ly' S' U' regs' mem' md',
       c' = mkCfg (mkst regs' (YK11.getr regsC 1%bv) mem' (seg_rom tfibsegs)) md' /\
       ajournal tfibsegs B STKc (spZ regsC) FPc ly3 S3 W3 (unpoison U3 memC) mdC [] ly' S' W'
         (unpoison U' mem') md' kc /\
       upoison_ok B ly' S' U' /\ upoisoned tfibsegs W' mem' U' /\ aregs_preserved regsC regs' /\
       (ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly' S' W' (unpoison U' mem') md' (k + kc) -> ARU tfibsegs B ly' S' U' W' mem' md' ->
        INV' cx (Ereg regs' (crt_extra cx)) (k + kc) ly' S' U' W' (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))
          md')).

(* the run, in the shape FSH_crt_segD.v's crt_seg36_run already proves: a journal / ARU step from the FULL boundary
   state to the call-site state, with the run's frame_of on both the raw and the restricted memory *)
Definition crt_runs_full (ss0 ssC : sstate) : Prop :=
  forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 (Q : world tfibsegs -> config -> Prop),
  crt_E cx E -> spZ (c_regs cx) mod 16 = 0 -> 192 <= spZ (c_regs cx) ->
  frame_addr ly3 3 (c_pos cx) = crt_F cx -> 0 <= crt_F cx < 2 ^ 64 ->
  st_ok tfibsegs E ss0 (restrict (w_H W3) ms3) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  (forall ms mat,
     st_ok tfibsegs E ssC (restrict (w_H W3) ms) ->
     ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms)) (with_vm_backing (m_vm_lazy md3) mat md3) k ->
     ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) ->
     frame_of E (ss_mem ss0) (ms_mem ms3) (ms_mem ms) ->
     frame_of E (ss_mem ss0) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
     SRr tfibsegs W3 (mkCfg ms (with_vm_backing (m_vm_lazy md3) mat md3)) Q) ->
  SRr tfibsegs W3 (mkCfg ms3 md3) Q.

Lemma crt_seg_call_full : forall r0 A_c r ssC (INV INV' : crt_inv) STKc,
  crt_runs_full (crt_ss_ret r0 crt_cs1 crt_csF) ssC ->
  crt_csite4 ssC A_c r -> 4096 <= r < 2 ^ 64 -> r mod 2 = 0 ->
  0 <= STKc -> STKc + 208 <= STK_check_round_trip ->
  crt_hcall_full (crt_ss_ret r0 crt_cs1 crt_csF) ssC A_c r STKc INV INV' ->
  crt_from SK B (crt_ss_ret r crt_cs1 crt_csF) INV' ->
  crt_from SK B (crt_ss_ret r0 crt_cs1 crt_csF) INV.
Proof.
intros r0 A_c r ssC INV INV' STKc HRUN HCS Hr Hr2 HSTKc HSTK HCALL NEXT.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFO HINV HS.
destruct HCS as (Hpc & Hres & M0 & M1 & M2 & G1 & G2 & G3 & G4 & G8 & G9 & G26).
pose proof HFO as (Hfr & Hnin & Hflag).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HPRE & _). pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPRE)) as (Hal16 & Hceil0 & H47 & HS0).
pose proof (@alloc_ceiling_value rc) as (HCr & _).
pose proof crt_STK_eq as STKv; unfold crt_STK in STKv.
pose proof (fsw_realign_facts (spZ (c_regs cx) - 192) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
  as (F1 & F2 & F3).
assert (Hsp1 : spZ (c_regs cx) - 208 <= crt_sp1 cx <= spZ (c_regs cx) - 192) by (unfold crt_sp1; lia).
pose proof HJ as (_ & Hly0 & _).
pose proof (crt_F_ly cx _ ly3 Hly0) as EF0.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR0.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (c_pos cx) HAR0 Hin3) as (HFal & HFapp & _).
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 3 (c_pos cx) HAR0 Hin3) as (HF4096 & HFceil & _).
rewrite EF0 in HFal, HFapp, HF4096, HFceil. rewrite crt_frame3 in HFapp, HFceil.
pose proof (shadow_addr_bounds (crt_F cx) ltac:(lia)) as (HSF1 & _).
pose proof (shadow_addr_bounds (crt_F cx + 511) ltac:(lia)) as (_ & HSF2b).
assert (HSF2 : shadow_addr (crt_F cx) + 64 <= shadow_addr (crt_F cx + 511) + 1)
  by (unfold shadow_addr; Z.div_mod_to_equations; lia).
(* the run, to the call site *)
eapply (HRUN cx E k ly3 S3 U3 W3 ms3 md3); [exact HE | lia | lia | exact EF0 | lia
  | exact HS | exact HJ | exact HARU |].
intros ms mat HSC HJC HARUC HF HFr.
set (mdC := with_vm_backing (m_vm_lazy md3) mat md3) in *.
pose proof (crt_mkst (w_H W3) E ssC ms HSC Hres) as Ems. rewrite Hpc in Ems.
set (regsC := ms_regs ms) in *. set (memC := ms_mem ms) in *.
assert (RG : forall rr : bv 5, YK11.getr regsC rr = sv_denot E (sr_get (ss_regs ssC) rr))
  by (intros rr; exact (st_ok_restrict_reg tfibsegs (w_H W3) E ssC ms rr HSC)).
assert (R1 : YK11.getr regsC 1%bv = Z_to_bv 64 r) by (rewrite RG, G1; reflexivity).
assert (R2 : YK11.getr regsC 2%bv = ew E 2) by (rewrite RG, G2; apply fsw_SOff0).
assert (R3 : YK11.getr regsC 3%bv = ew E 3) by (rewrite RG, G3; apply fsw_SOff0).
assert (R4 : YK11.getr regsC 4%bv = ew E 4) by (rewrite RG, G4; apply fsw_SOff0).
assert (R8 : YK11.getr regsC 8%bv = ew E 8) by (rewrite RG, G8; apply fsw_SOff0).
assert (R9 : YK11.getr regsC 9%bv = ew E 9) by (rewrite RG, G9; apply fsw_SOff0).
assert (R26 : YK11.getr regsC 26%bv = ew E 26) by (rewrite RG, G26; apply fsw_SOff0).
assert (HR0 : region_ok tfibsegs E (mrestrict (w_H W3) memC) crt_s0_region)
  by exact (fsw_region_nth E ssC (restrict (w_H W3) ms) 0 crt_s0_region HSC M0).
assert (HRs : region_ok tfibsegs E (mrestrict (w_H W3) memC) (crt_slot_region crt_cs1))
  by exact (fsw_region_nth E ssC (restrict (w_H W3) ms) 1 (crt_slot_region crt_cs1) HSC M1).
assert (HRf : region_ok tfibsegs E (mrestrict (w_H W3) memC) (crt_frame_region crt_csF))
  by exact (fsw_region_nth E ssC (restrict (w_H W3) ms) 2 (crt_frame_region crt_csF) HSC M2).
(* the flag word, read off the frame REGION at the call state - this is what replaces same_below *)
pose proof (al_flag _ _ LAWS _ _ _ _ _ 3 (c_pos cx) (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC)
  ltac:(rewrite Hfr; left; reflexivity)) as (_ & _ & Hflapp & Hflc).
pose proof HJC as (_ & HlyC & _).
rewrite (crt_FL_ly cx _ ly3 HlyC) in Hflapp, Hflc.
assert (HFLr : 0 <= crt_FL cx < 2 ^ 64) by (unfold in_app in Hflapp; lia).
assert (HFv : bv_unsigned (ew E 47) = crt_F cx)
  by (rewrite (crt_E_F cx E HE); apply wz; lia).
assert (Hflval : val_mem tfibsegs (mrestrict (w_H W3) memC) (crt_F cx + (fs_frame_bytes 3 - 8)) 8 (crt_FL cx)).
{ exact (fsw_field E (mrestrict (w_H W3) memC) 47 (crt_F cx) crt_csF 0 (fs_frame_bytes 3) 0 (fs_frame_bytes 3)
    (fs_frame_bytes 3 - 8) 8 (SOff 46 0) (crt_FL cx) HRf HFv ltac:(left; reflexivity)
    ltac:(rewrite fsw_SOff0; exact (crt_E_FL cx E HE)) ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(cbn; lia)). }
assert (Hflag' : rdword (aview tfibsegs (w_H W3) memC) (crt_F cx + fs_frame_bytes 3 - 8) = Some (crt_FL cx)).
{ replace (crt_F cx + fs_frame_bytes 3 - 8) with (crt_F cx + (fs_frame_bytes 3 - 8)) by lia.
  exact (YF0x.val_mem_rdword (w_H W3) memC _ (crt_FL cx) HFLr Hflval). }
assert (Hrok : YK0s.ret_ok (Z_to_bv 64 r)) by (apply ret_ok_even; rewrite (wz r) by lia; exact Hr2).
destruct (crt_site_pre SK B cx E k ly3 S3 U3 W3 ms mdC ssC r STKc HB HE HJC HARUC (conj Hfr (conj Hnin Hflag'))
  HSC G1 G2 G3 G4 G8 M0 Hr Hrok HSTKc HSTK) as (HPREc & _ & HFRL & HTOPc).
rewrite Ems. change (mkCfg (mkst regsC (Z_to_bv 64 A_c) memC (seg_rom tfibsegs)) mdC)
  with (cfg_at tfibsegs A_c regsC memC mdC).
destruct (HCALL cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HF HFr RG HPREc HFRL HTOPc)
  as (FPc & kc & P & HSRr & HFP & HFL & HK).
eapply SRr_bind; [exact HSRr|].
intros W' c' Hle HPc.
destruct (HK W' c' HPc) as (ly' & S' & U' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP & HINV').
rewrite R1.
assert (V : forall n z, bv_unsigned (ew E n) = z -> 0 <= z < 2 ^ 64 -> ew E n = Z_to_bv 64 z)
  by (intros n z Hz Hr64; apply bv_eq; rewrite Hz; symmetry; apply wz; exact Hr64).
assert (Esp : spZ regsC = crt_sp1 cx) by (unfold spZ; rewrite R2; exact E2).
assert (HSV : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memC) (spZ (c_regs cx))) crt_sv_chunks).
{ destruct HR0 as (_ & _ & _ & Hc). cbn [crt_s0_region fs_ret_s0_region YP09.r_base YP09.r_chunks base_val] in Hc.
  rewrite E8 in Hc. exact Hc. }
assert (HCS1 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memC) (crt_sp1 cx)) crt_cs1).
{ destruct HRs as (_ & _ & _ & Hc). cbn [crt_slot_region YP09.r_base YP09.r_chunks base_val] in Hc.
  rewrite E9 in Hc. exact Hc. }
assert (HCSF : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memC) (crt_F cx)) crt_csF).
{ destruct HRf as (_ & _ & _ & Hc). cbn [crt_frame_region YP09.r_base YP09.r_chunks base_val] in Hc.
  rewrite HFv in Hc. exact Hc. }
rewrite Esp in HJc.
assert (Q2 : YK11.getr regsC 2%bv = Z_to_bv 64 (crt_sp1 cx)) by (rewrite R2; apply V; [exact E2 | lia]).
assert (Q3 : YK11.getr regsC 3%bv = YK11.getr (c_regs cx) 3%bv) by (rewrite R3; exact E3).
assert (Q4 : YK11.getr regsC 4%bv = YK11.getr (c_regs cx) 4%bv) by (rewrite R4; exact E4).
assert (Q8 : YK11.getr regsC 8%bv = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite R8; apply V; [exact E8 | lia]).
assert (Q9 : YK11.getr regsC 9%bv = Z_to_bv 64 (crt_sp1 cx)) by (rewrite R9; apply V; [exact E9 | lia]).
assert (Q26 : YK11.getr regsC 26%bv = Z_to_bv 64 (crt_SF cx))
  by (rewrite R26; apply V; [exact E26 | unfold crt_SF, kLowMemEnd, kHighShadowEnd in *; lia]).
assert (HcsFin : Forall (fun c => 0 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= fs_frame_bytes 3)
  crt_csF) by (unfold crt_csF; rewrite crt_frame3; apply Forall_cons; [cbn; lia | apply Forall_nil]).
assert (HcsFat : crt_atom_chunks crt_csF)
  by (unfold crt_atom_chunks, crt_csF; apply Forall_cons; [do 4 eexists; split; [reflexivity | lia] | apply Forall_nil]).
assert (HcsFnf : forall c, In c crt_csF -> forall i, 0 <= i < YP09.c_len c -> ~ inFP FPc (crt_F cx + YP09.c_off c + i)).
{ intros c Hc i Hi. unfold crt_csF in Hc. destruct Hc as [<-|[]]. cbn in Hi. apply HFL. cbn. rewrite crt_frame3. lia. }
assert (HflNF : forall i, 0 <= i < 8 -> ~ inFP FPc (crt_F cx + fs_frame_bytes 3 - 8 + i)) by (intros i Hi; apply HFL; lia).
destruct (crt_after_call (SKfp := SK) B cx E k ly3 S3 U3 W3 (mkst regsC (Z_to_bv 64 A_c) memC (seg_rom tfibsegs)) mdC
  STKc FPc ly' S' U' W' regs' mem' md' kc r crt_csF HE HJC HARUC (conj Hfr (conj Hnin Hflag'))
  Q2 Q3 Q4 Q8 Q9 Q26 HSV HCS1 HCSF HcsFin HcsFat HcsFnf HflNF HJc OK' PO' HFP HP HSTKc ltac:(lia))
  as (HJ' & HARU' & HFO' & HE' & HS').
exact (NEXT cx (Ereg regs' (crt_extra cx)) (k + kc) ly' S' U' W' (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))
  md' HB HE' HJ' HARU' HFO' (HINV' HJ' HARU') HS').
Qed.
End full.

(* ================= the read-only image at any state of the walk =================
   A site v23 (a working branch 6a5c129e991) adds this section: a Theorem Labs lane's a23_rom (a working branch
   14885a42e60 FSH_crt_segA23.v:264-292), renamed; lanes D2 (three copies) and A23 used it, so it lives here once.
   Ported to B unchanged: no pc, register or image constant in it (IMG is lib/B/FSH_Rt.v's fs_img_facts, over B's
   FS_RLO / FS_RHI). ---- *)
Section rom. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis IMG : fs_img_facts tfibsegs B.

Lemma crt_rom : forall cx k ly3 S3 U3 (W3 : world tfibsegs) (mem : word -> option byte) md3,
  crt_base B cx ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 mem) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 mem md3 ->
  rom_view tfibsegs W3 mem.
Proof.
intros cx k ly3 S3 U3 W3 mem md3 HB HJ HARU.
pose proof (crt_rodata SK B cx k ly3 S3 U3 W3 (mkst (c_regs cx) (Z_to_bv 64 0) mem (seg_rom tfibsegs)) md3
  HB HJ HARU) as HRO.
cbn [ms_mem mkst] in HRO.
assert (HU : forall a, 0 <= a < SHADOW_OFF -> in_ush U3 (bv_unsigned (Z_to_bv 64 a)) = false).
{ intros a Ha. eapply crt_ush_low; [exact HARU | exact Ha]. }
assert (HROu : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W3) (unpoison U3 mem))).
{ intros a Ha Ho He.
  assert (Hlow : 0 <= a < SHADOW_OFF).
  { pose proof (fs_segs_img a (crt_roP_img a Ha)) as Hl. unfold FS_IMG_END, SHADOW_OFF in *. lia. }
  rewrite (aview_unpoison_out tfibsegs (w_H W3) U3 mem a (HU a Hlow)). exact (HRO a Ha Ho He). }
pose proof (proj1 (proj2 IMG ly3 S3 W3 (unpoison U3 mem) md3
  (ARU_AR tfibsegs B ly3 S3 U3 W3 mem md3 HARU) HROu)) as HRV.
intros a Ha.
assert (Hlow : 0 <= a < SHADOW_OFF).
{ destruct Ha as (sg & Hin & Hw & Hr).
  pose proof (fs_segs_img a (ex_intro _ sg (conj Hin Hr))) as Hl. unfold FS_IMG_END, SHADOW_OFF in *. lia. }
rewrite <- (aview_unpoison_out tfibsegs (w_H W3) U3 mem a (HU a Hlow)). exact (HRV a Ha).
Qed.
End rom.

(* ================= the RUNTIME-call crossing (an interceptor thunk: strlen / strcmp, and any STK_RT_STR thunk) =================
   A site v24 (a working branch e377e99a5c4) adds this section: moved VERBATIM there from a Theorem Labs lane's
   lib/A/FSH_crt_segA23.v at a working branch c2f01f092c5 (lines 60-68, 258-322, 772-904), prefix a23
   renamed to crt: crt_reg_atom, crt_gptp, crt_rt_frame, crt_rt_call (strlen) and crt_rt_call2 (strcmp). Their
   continuation carries the contract's own memory frame (aview kept outside the thunk's stack window) and presence
   growth, which is what lets a segment take its data facts across a runtime call. Ported to B with B's thunk entries
   PC_strlen = 0x426c4 and PC_strcmp = 0x426cc (lib/B/FSH_Base.v; A: 0x42654 / 0x4265c) and B's call sites in the
   comments; STK_RT_STR = 2 * ESTACK = 8192 on both images, STK_check_round_trip is read through crt_STK_eq. *)
(* a register that a symbolic state holds as its own atom reads that atom on the machine *)
Lemma crt_reg_atom : forall {fx : YK11.FPState} E (H : word -> bool) ms ss (q : bv 5) n,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) q = SOff n 0 ->
  YK11.getr (ms_regs ms) q = ew E n.
Proof.
intros fx E H ms ss q n HS Hq.
rewrite (st_ok_restrict_reg tfibsegs H E ss ms q HS), Hq. apply fsw_SOff0.
Qed.

Section rtcall. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis IMG : fs_img_facts tfibsegs B.

(* the entry's gp / tp, from crt_base's own afn_preU *)
Lemma crt_gptp : forall cx, crt_base B cx ->
  YK11.getr (c_regs cx) 3%bv = w64 (as_gp B) /\ YK11.getr (c_regs cx) 4%bv = w64 (as_tp B).
Proof.
intros cx HB. pose proof HB as (HPRE & _).
destruct HPRE as ((HFN & _) & _). destruct HFN as (_ & _ & _ & Hgp & Htp & _).
split; [exact Hgp | exact Htp].
Qed.

(* the shared part of the two calls: the call-site registers read off the state, the callee's ecall_preU_k, and the
   write window the callee may touch (its own 2 * ESTACK, inside crt's stack window) *)
Lemma crt_rt_frame : forall cx E (ss : sstate) (r : Z) k ly3 S3 U3 (W3 : world tfibsegs) regsT memT mdT pc0,
  crt_base B cx -> crt_E cx E ->
  sr_get (ss_regs ss) 1%bv = SLit r -> 0 <= r < 2 ^ 64 -> YK0s.ret_ok (Z_to_bv 64 r) ->
  sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
  st_ok tfibsegs E ss (restrict (w_H W3) (mkst regsT (Z_to_bv 64 pc0) memT (seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 memT) mdT k ->
  ARU tfibsegs B ly3 S3 U3 W3 memT mdT ->
  YK11.getr regsT 1%bv = Z_to_bv 64 r /\ spZ regsT = crt_sp1 cx /\
  YK11.getr regsT 3%bv = w64 (as_gp B) /\ YK11.getr regsT 4%bv = w64 (as_tp B) /\
  ecall_preU_k tfibsegs B STK_RT_STR ly3 S3 U3 W3 regsT memT mdT /\
  (forall a, crt_sp1 cx - STK_RT_STR <= a < crt_sp1 cx ->
     awr_byte tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (ablocks B (c_ly cx) (c_S cx))
       (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)) a).
Proof.
intros cx E ss r k ly3 S3 U3 W3 regsT memT mdT pc0 HB HE Sr1 Hr HRet Sr2 Sr3 Sr4 HS HJ HARU.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@alloc_ceiling_val rc)) as HACV.
pose proof crt_STK_eq as HSTKv; unfold crt_STK in HSTKv.
assert (HSTR : STK_RT_STR = 2 * ESTACK) by reflexivity. unfold ESTACK in HSTR.
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & Eex).
destruct (crt_gptp cx HB) as (Hgp & Htp).
pose proof HB as (HPRE & _).
pose proof (proj1 (proj1 HPRE)) as HFN.
destruct HFN as (_ & _ & _ & _ & _ & Hstk0 & _).
destruct Hstk0 as (Hal16 & _ & Hceil0 & Hlo0 & Hhi0 & Hsthi & _).
assert (H16 : spZ (c_regs cx) mod 16 = 0) by exact Hal16.
assert (H0 : 192 <= spZ (c_regs cx)) by lia.
destruct (crt_sp1_facts cx H16 H0) as (Hsp1b & Hsp1_32 & Hsp1_16).
assert (Rd : forall (q : bv 5) n, sr_get (ss_regs ss) q = SOff n 0 -> YK11.getr regsT q = ew E n).
{ intros q n Hq. pose proof (st_ok_restrict_reg tfibsegs (w_H W3) E ss
    (mkst regsT (Z_to_bv 64 pc0) memT (seg_rom tfibsegs)) q HS) as X.
  cbn [ms_regs mkst] in X. rewrite X, Hq. apply fsw_SOff0. }
assert (G1 : YK11.getr regsT 1%bv = Z_to_bv 64 r).
{ exact (fsw_reg_lit (w_H W3) E ss (mkst regsT (Z_to_bv 64 pc0) memT (seg_rom tfibsegs)) 1%bv r HS Sr1 Hr). }
assert (GSP : spZ regsT = crt_sp1 cx) by (unfold spZ; rewrite (Rd 2%bv _ Sr2); exact E2).
assert (G3 : YK11.getr regsT 3%bv = w64 (as_gp B)) by (rewrite (Rd 3%bv _ Sr3), E3; exact Hgp).
assert (G4 : YK11.getr regsT 4%bv = w64 (as_tp B)) by (rewrite (Rd 4%bv _ Sr4), E4; exact Htp).
assert (Hra : YK0s.ret_ok (YK11.getr regsT 1%bv)) by (rewrite G1; exact HRet).
split; [exact G1|]. split; [exact GSP|]. split; [exact G3|]. split; [exact G4|].
split.
- eapply (fsw_ecall_preU_k_at B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 W3 memT mdT k regsT
    (crt_sp1 cx - spZ (c_regs cx)) STK_RT_STR HJ HARU);
  [lia | rewrite Zminus_mod, H16, Hsp1_16; reflexivity | lia | unfold ESTACK; lia | lia | lia
  | exact Hra | exact G3 | exact G4].
- intros a Ha. left. left. lia.
Qed.
End rtcall.

Section rtcalls. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.

(* ---- the strlen thunk (B: `jal` at 0x820c0 to PC_strlen 0x426c4; A: 0x81f74 to 0x42654), FsRt.fr_strlen through
   astrlen_realizesU, in the shape of FSH_crt_base.crt_bcmp_call: the call-site registers read off the run's state,
   the callee's ecall_preU_k and write window from crt_rt_frame, the contract, and the journal put back over the call
   by FSW_K.fsw_intrin_atU. The post carries the contract's own memory frame (the callee writes only its 2 * ESTACK
   stack window), which the segment needs to take its data facts across. ---- *)
Lemma crt_rt_call : forall (ss : sstate) (r : Z) (na : nat) cx E k ly3 S3 U3 (W3 : world tfibsegs)
  regsT memT mdT (l : list Z) (Q : world tfibsegs -> config -> Prop),
  CrtRt B -> fs_img_facts tfibsegs B ->
  crt_base B cx -> crt_E cx E ->
  sr_get (ss_regs ss) 1%bv = SLit r -> 0 <= r < 2 ^ 64 -> YK0s.ret_ok (Z_to_bv 64 r) ->
  sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
  sr_get (ss_regs ss) 10%bv = SOff na 0 ->
  st_ok tfibsegs E ss (restrict (w_H W3) (mkst regsT (Z_to_bv 64 PC_strlen) memT (seg_rom tfibsegs))) ->
  cstr_ok tfibsegs W3 memT (bv_unsigned (ew E na)) l ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 memT) mdT k ->
  ARU tfibsegs B ly3 S3 U3 W3 memT mdT ->
  (forall regs2 mem2 md2,
     ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
       (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 mem2) md2 k ->
     ARU tfibsegs B ly3 S3 U3 W3 mem2 md2 ->
     aregs_preserved regsT regs2 -> YK11.getr regs2 10%bv = w64 (Z.of_nat (length l)) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (crt_sp1 cx - STK_RT_STR <= a < crt_sp1 cx) ->
        aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) memT a) ->
     (forall a, apresent (w_H W3) memT a -> apresent (w_H W3) mem2 a) ->
     SRr tfibsegs W3 (mkCfg (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs)) md2) Q) ->
  SRr tfibsegs W3 (mkCfg (mkst regsT (Z_to_bv 64 PC_strlen) memT (seg_rom tfibsegs)) mdT) Q.
Proof.
intros ss r na cx E k ly3 S3 U3 W3 regsT memT mdT l Q RT IMG HB HE Sr1 Hr HRet Sr2 Sr3 Sr4 Sr10 HS HC HJ HARU K.
destruct (crt_rt_frame SK B cx E ss r k ly3 S3 U3 W3 regsT memT mdT PC_strlen HB HE Sr1 Hr HRet Sr2 Sr3 Sr4
  HS HJ HARU) as (G1 & GSP & G3 & G4 & HPRE & HWR).
assert (G10 : YK11.getr regsT 10%bv = w64 (bv_unsigned (ew E na))).
{ pose proof (crt_reg_atom E (w_H W3) (mkst regsT (Z_to_bv 64 PC_strlen) memT (seg_rom tfibsegs)) ss 10%bv na
    HS Sr10) as X.
  cbn [ms_regs mkst] in X. rewrite X. unfold w64. symmetry. apply Z_to_bv_bv_unsigned. }
(* the contract *)
pose proof (crt_fr_strlen B RT ly3 S3 U3 W3 regsT memT mdT (bv_unsigned (ew E na)) l HPRE
  (crt_rom SK B IMG cx k ly3 S3 U3 W3 memT mdT HB HJ HARU) G10 HC) as HCT.
change (cfg_at tfibsegs PC_strlen regsT memT mdT) with
  (mkCfg (mkst regsT (Z_to_bv 64 PC_strlen) memT (seg_rom tfibsegs)) mdT) in HCT.
(* the journal back over the call: the write set is the callee's own stack window *)
eapply SRr_bind.
{ eapply (fsw_intrin_atU B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 W3 memT mdT k U3
    (fun a => spZ regsT - STK_RT_STR <= a < spZ regsT) (YK11.getr regsT 1%bv) _
    (fun regs' mem' md' => aregs_preserved regsT regs' /\
       YK11.getr regs' 10%bv = w64 (Z.of_nat (length l)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - STK_RT_STR <= a < spZ regsT) ->
          aview tfibsegs (w_H W3) mem' a = aview tfibsegs (w_H W3) memT a) /\
       (forall a, apresent (w_H W3) memT a -> apresent (w_H W3) mem' a)) HJ).
  - eapply SRr_mono; [exact HCT|].
    intros W' c' _ (-> & regs' & mem' & md' & v & Ec & HAR' & PO' & HP & Hsame & Hv & Hvr & Hres & Hfr & Hgr).
    split; [reflexivity|]. exists regs', mem', md'.
    split; [rewrite Ec; unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
    split; [split; [exact HAR' | split; [exact (proj1 (proj2 HARU)) | exact PO']]|].
    split; [exact Hsame|].
    split; [exact (crt_unpoison_keep (w_H W3) U3 memT mem' _ Hfr)|].
    split; [exact (crt_unpoison_present (w_H W3) U3 memT mem' Hgr)|].
    split; [exact HP|]. split; [rewrite Hv, Hres; reflexivity|]. split; [exact Hfr | exact Hgr].
  - intros a Ha. rewrite GSP in Ha. exact (HWR a Ha). }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & Hv2 & Hfr2 & Hgr2).
rewrite G1 in *.
rewrite GSP in Hfr2.
exact (K regs2 mem2 md2 HJ2 HARU2 HP2 Hv2 Hfr2 Hgr2).
Qed.

(* ---- the strcmp thunks (B: `jal` at 0x821b0 and 0x821c0 to PC_strcmp 0x426cc; A: 0x82054 / 0x82064 to 0x4265c),
   FsRt.fr_strcmp through astrcmp_realizesU: the same crossing with a second string in a1, and the result read as
   `v = 0 <-> str_eq l1 l2`. ---- *)
Lemma crt_rt_call2 : forall (ss : sstate) (r : Z) (na nb : nat) cx E k ly3 S3 U3 (W3 : world tfibsegs)
  regsT memT mdT (l1 l2 : list Z) (Q : world tfibsegs -> config -> Prop),
  CrtRt B -> fs_img_facts tfibsegs B ->
  crt_base B cx -> crt_E cx E ->
  sr_get (ss_regs ss) 1%bv = SLit r -> 0 <= r < 2 ^ 64 -> YK0s.ret_ok (Z_to_bv 64 r) ->
  sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
  sr_get (ss_regs ss) 10%bv = SOff na 0 -> sr_get (ss_regs ss) 11%bv = SOff nb 0 ->
  st_ok tfibsegs E ss (restrict (w_H W3) (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs))) ->
  cstr_ok tfibsegs W3 memT (bv_unsigned (ew E na)) l1 ->
  cstr_ok tfibsegs W3 memT (bv_unsigned (ew E nb)) l2 ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 memT) mdT k ->
  ARU tfibsegs B ly3 S3 U3 W3 memT mdT ->
  (forall regs2 mem2 md2 (v : Z),
     ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
       (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 mem2) md2 k ->
     ARU tfibsegs B ly3 S3 U3 W3 mem2 md2 ->
     aregs_preserved regsT regs2 -> YK11.getr regs2 10%bv = w64 v -> 0 <= v < 2 ^ 64 ->
     (v = 0 <-> str_eq l1 l2) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (crt_sp1 cx - STK_RT_STR <= a < crt_sp1 cx) ->
        aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) memT a) ->
     (forall a, apresent (w_H W3) memT a -> apresent (w_H W3) mem2 a) ->
     SRr tfibsegs W3 (mkCfg (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs)) md2) Q) ->
  SRr tfibsegs W3 (mkCfg (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs)) mdT) Q.
Proof.
intros ss r na nb cx E k ly3 S3 U3 W3 regsT memT mdT l1 l2 Q RT IMG HB HE Sr1 Hr HRet Sr2 Sr3 Sr4 Sr10 Sr11
  HS HC1 HC2 HJ HARU K.
destruct (crt_rt_frame SK B cx E ss r k ly3 S3 U3 W3 regsT memT mdT PC_strcmp HB HE Sr1 Hr HRet Sr2 Sr3 Sr4
  HS HJ HARU) as (G1 & GSP & G3 & G4 & HPRE & HWR).
assert (G10 : YK11.getr regsT 10%bv = w64 (bv_unsigned (ew E na))).
{ pose proof (crt_reg_atom E (w_H W3) (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs)) ss 10%bv na
    HS Sr10) as X.
  cbn [ms_regs mkst] in X. rewrite X. unfold w64. symmetry. apply Z_to_bv_bv_unsigned. }
assert (G11 : YK11.getr regsT 11%bv = w64 (bv_unsigned (ew E nb))).
{ pose proof (crt_reg_atom E (w_H W3) (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs)) ss 11%bv nb
    HS Sr11) as X.
  cbn [ms_regs mkst] in X. rewrite X. unfold w64. symmetry. apply Z_to_bv_bv_unsigned. }
pose proof (crt_fr_strcmp B RT ly3 S3 U3 W3 regsT memT mdT (bv_unsigned (ew E na)) (bv_unsigned (ew E nb))
  l1 l2 HPRE (crt_rom SK B IMG cx k ly3 S3 U3 W3 memT mdT HB HJ HARU) G10 G11 HC1 HC2) as HCT.
change (cfg_at tfibsegs PC_strcmp regsT memT mdT) with
  (mkCfg (mkst regsT (Z_to_bv 64 PC_strcmp) memT (seg_rom tfibsegs)) mdT) in HCT.
eapply SRr_bind.
{ eapply (fsw_intrin_atU B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 W3 memT mdT k U3
    (fun a => spZ regsT - STK_RT_STR <= a < spZ regsT) (YK11.getr regsT 1%bv) _
    (fun regs' mem' md' => aregs_preserved regsT regs' /\
       (exists v : Z, YK11.getr regs' 10%bv = w64 v /\ 0 <= v < 2 ^ 64 /\ (v = 0 <-> str_eq l1 l2)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - STK_RT_STR <= a < spZ regsT) ->
          aview tfibsegs (w_H W3) mem' a = aview tfibsegs (w_H W3) memT a) /\
       (forall a, apresent (w_H W3) memT a -> apresent (w_H W3) mem' a)) HJ).
  - eapply SRr_mono; [exact HCT|].
    intros W' c' _ (-> & regs' & mem' & md' & v & Ec & HAR' & PO' & HP & Hsame & Hv & Hvr & Hres & Hfr & Hgr).
    split; [reflexivity|]. exists regs', mem', md'.
    split; [rewrite Ec; unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
    split; [split; [exact HAR' | split; [exact (proj1 (proj2 HARU)) | exact PO']]|].
    split; [exact Hsame|].
    split; [exact (crt_unpoison_keep (w_H W3) U3 memT mem' _ Hfr)|].
    split; [exact (crt_unpoison_present (w_H W3) U3 memT mem' Hgr)|].
    split; [exact HP|]. split; [exists v; split; [exact Hv | split; [exact Hvr | exact Hres]]|].
    split; [exact Hfr | exact Hgr].
  - intros a Ha. rewrite GSP in Ha. exact (HWR a Ha). }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & (v & Hv2 & Hvr2 & Hres2) & Hfr2 & Hgr2).
rewrite G1 in *. rewrite GSP in Hfr2.
exact (K regs2 mem2 md2 v HJ2 HARU2 HP2 Hv2 Hvr2 Hres2 Hfr2 Hgr2).
Qed.
End rtcalls.
