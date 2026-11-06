(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:383-389, 448-454, 493-498, 501-509 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:625-631 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:208-214, 227-233 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg10.v, with its module paths and module names changed; 2634 of its 2686 lines of code are new or changed and 608 lines of the source are left out. *)
(* parse_value 0x82f9c (pf.c:283-298) on fs.asan, 373 instructions: the walk of FSH_Fn_reader.v parse_value_spec k
   (level-indexed, narrow success form) against S0's statements. STAGE FORM: every machine stage below is proved; the
   composition into parse_value_spec k is FSW_parse_value_holds.parse_value_holds (front: FSW_parse_value_front.v,
   string arm and the frame chains: FSW_parse_value_str.v, object arm: FSW_parse_value_obj.v).
   rule 24 CONFIRM (a Theorem Labs lane 04:0xZ): no released ASan proof of the function, so the walk is new; the released
   plain parse_value_c.v / Pv*.v and bump's parse_value_disp.v / PvJoin.v (a working branch 64ac962a8d2) are
   control-flow templates only (read, not imported: bump states SR over reader_env, a different framework).
   The decode table is FSW_parse_value_tbl.v. Control flow (MEASURED, capstone 5.0.7 on the pinned fs.asan sha256
   64b53ff86172bb07f93f146e67b81a0354bca88e0a580e93fb1da01406fb76e0):
   - 0x82f9c-0x82fe0: frame 0xa0 (0(sp) := 0, ra/s0..s11 saved at sp0 - 8 .. sp0 - 104), s0 := entry sp, sp
     re-aligned down to 32 (`andi sp, sp, -32`), s1 := sp; s3 := a1 (v), s4 := a0 (q);
   - 0x82fe8-0x83004: a2 := *(u32 * )*(0x9f748) (the use-after-return flag, 0xa7f40, reads 1 by AR_const_law), s7 :=
     *(u64 * )*(0x9f6f0) (the shadow base): `beqz a2` not taken;
   - 0x8300c jal __asan_stack_malloc_0 (a0 = 64): granted (pv_grant: FRL_parse_value k <= 4 frames live), so s2 = s10 =
     the fake frame F and `bnez s2` 0x83020 skips the real-stack fallback 0x83024-0x8303c;
   - 0x83040-0x83098: frame header at F + 0/8/16, s8 := F / 8 + shadow base, shadow of F := f1 f1 f1 f1 f8 f3 f3 f3;
   - 0x830a0-0x830bc: inline shadow checks of q + 8 and q (the token run, q's shent), 0x30(s1) := F;
   - 0x830c0-0x8311c: in->p / in->end loaded; the white-space loop (pf.c skip_ws, inlined): head 0x830e0, the text byte's
     shadow check (token run, slow path 0x83120), exit when the byte is above 32 or not in the mask, in->p += 1 at
     0x83110 (q's shadow check 0x83104);
   - 0x8312c-0x831ac: in->p reloaded, in->p < in->end, the byte at in->p dispatched: the quote (34) -> 0x831b0, the brace (123) ->
     0x831a0; '[', 'f', 'n', 't' and numbers are dead under FS_DOC_STRS (i) (hex4 / put_utf8 / literal / parse_number
     are not reached);
   - string arm 0x831b0: v's shadow check, v->type := 4, jal parse_string (a0 = q) 0x831cc, v->str := result (v + 16),
     s5 := 0 when the result is non-zero;
   - object arm 0x831a0: jal parse_items (a0 = q, a1 = v, a2 = 1) 0x832f4, s5 := result;
   - epilogue 0x83318-0x833b8: F's magic := retired, s2 <> 0: shadow of F := f5 x 8, the frame's flag byte := 0 through
     its last word (frames S' = frames S), a0 := s5, registers restored from s0 - 8 .. s0 - 104, ret. 

   STAGES PROVED AT THIS SHA (no admit, no Admitted, no Axiom, no Parameter, no nia):
     pv_entry, pv_seg0      0x82f9c -> the __asan_stack_malloc_0 call 0x8300c
     pv_sm_site, pv_sm      the class-0 grant (FSW_frame.fsw_stack_malloc_atU), resume at 0x83010
     pv_resume_sm           the resume STATE, with the journal top and the s0 value SEPARATED (see the kit gap below)
     pv_hd_ok               the white-space loop-head state 0x830e0 from machine facts
     pv_seg1                0x83010 -> 0x830e0: frame header, F's shadow, both inline q checks, in->p / in->end
     pv_step, pv_loop       the white-space loop 0x830e0 -> 0x830e0 (one iteration; the induction on the run)
     pv_disp                the loop exit 0x830e0 -> 0x8312c -> the two reachable arms: byte 34 -> 0x831b0 (string),
                            byte 123 -> 0x831a0 (object); the end test and the five dispatch tests decided
     ps_ok, pv_str0         the string arm 0x831b0 -> parse_string's entry (v's shadow check, v->type := 4, the jal)
     pv_strcall             the parse_string call: the callee's fpreU (fsw_fpreU_atFP), HPS, the journal composition
                            (FSW_K3.fsw_rt_atU3), to the return 0x831d0
     pq_ok, pv_str1         the string arm after the call 0x831d0 -> 0x83318 (v->str := the block, s5 := 0)
     pv_obj1                the object arm after the call 0x832f8 -> 0x83318 (s5 := the callee's 0); the object arm
                            up to and through the parse_items call is FSW_parse_value_calls.v (pvc_obj0, pvc_objcall,
                            a Theorem Labs lane's, taken by path from a working branch 23c6ed08f60)
     pe_ok, pv_epi          the epilogue 0x83318 -> `ret` 0x833b8 (F's magic, F's shadow := f5 x 8, the flag byte := 0
                            releasing the frame through FSW_frame.fsw_flag_storeU) and the return through FSW_ret.fsw_retU
                            into fpostU, from any journal start / count, with the memory kept outside pe_wr
     pv_val1, pv_ws_wsb, pv_text_of_tb, pv_unp_high, pv_front_keep
                            the front's helpers: one byte as a val_mem, the grammar's white space is the loop's four
                            bytes, the text bytes at in->p, the stack is no user-poisoned byte, the stack bytes the
                            prologue and the grant do not write keep their entry value
   SECTION HYPOTHESES (RUNTIME / image cells, as the reader specs' header names them): HGOT / HCELL / HGUAR / HUCELL /
   SM0 (FsRt's class-0 stack-malloc field only) / errno_low / ML / SMP (Section W: the entry and the grant); ML / ASF
   (astack_free_law, the class-0 stack-free law) / FFL (frame_flag_lawP) (Section EP2: the epilogue's flag store);
   HPS : parse_string_spec (Section SC; S0 proves it as FSW_parse_string.parse_string_proof under fuzz_malloc_spec);
   FSW_parse_value_calls.v's PI : parse_items_spec k (the parse_items lane). FSW_parse_value_holds.v lists the set
   parse_value_holds takes.
   pv_str0's write window is v's type word [v, v + 4) (its keep covers v's other 52 bytes, which the string node needs);
   pv_str1 carries gp / tp to the epilogue.
   JOURNAL k (step 5 of the brief, checked against S0's event-sensitive rd_ev, FSH_Fn_reader.v:135): the string arm
   composes parse_string's EV_fuzz_malloc = 1 with this function's own 0 (the class-0 grant and the release count 0)
   and rd_ev (ttrace (JStr s)) = rd_ev [EAlloc _] = EV_fuzz_malloc = 1; the object arm passes parse_items' rd_ev
   (ttrace (JObj ms)) through unchanged. Both fit; no definition was loosened.
   REPORT SITES (a Theorem Labs lane report-sites-A.tsv, 19 rows), all refuted by a proved stage: pv_seg1 0x8352c / 0x83534 (the
   q + 8 / q checks); pv_step 0x83128 (the byte's check) and 0x83504 (q's check before in->p += 1); pv_disp 0x8353c,
   0x834c0 and, by deciding the dispatch to bytes 34 / 123 only, every parse_number / literal row (0x832e4, 0x834e4,
   0x834f0, 0x834fc, 0x83518, 0x83528, 0x8354c, 0x83554, 0x8355c, 0x83564, 0x8356c); pv_str0 0x834d4 (v's check at
   0x831b8); pv_str1 0x83544 (v + 16's check at 0x831dc). The object arm and the epilogue have none.
   KIT GAP REPORTED TO a Theorem Labs lane (owner a Theorem Labs lane): FSW_frame3.fsw_resume_after_stack_mallocU and
   FSW_rres.fsw_resume_after_rtU_s0 fix sp0 as BOTH the journal's window top AND the s0 register value. parse_value's
   journal top is pj_parse's RAISED ot while its s0 is its own entry sp s, with s < ot, so neither applies; pv_resume_sm
   here is crcs_resume_sm's text with the two separated (`s` bases the s0 region, `sp0` bounds the window:
   sp0 - STK <= sp1 + slo, s <= sp0, s mod 16 = 0).
   BASE: S0 a working branch 4bed8e9c8ff with a working branch 67a8947cd73 (the left arm's s0 = q,
   lib/A/FSH_Fn_reader.v from 81b380a2d74, and the parse_items lane's re-proof). *)

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
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_frame FSW_ret FSH_Fn_reader FSW_rd
FSW_parse_value_tbl FSH_Fn_entry FSH_Fn_alloc FSW_K3 FSW_parse_string.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YN2j.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved.
   YI14 is required (not imported) so that the second probe names a loaded class. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Ltac pv_cs := unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] =>
  let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.

(* ================= pure facts ================= *)
(* the class-0 fake frame is granted: at most FRL_parse_value k = 2 + k <= 4 frames are live at the call *)
Lemma pv_grant : forall (k : nat) (l : list (Z * Z)), (k <= 2)%nat ->
  Z.of_nat (length l) <= FRL_parse_value (Z.of_nat k) -> count_cid 0 l < fs_frames 0.
Proof. intros k l Hk Hl. apply fs_fake_granted; [lia | unfold FRL_parse_value, FRL_MAX in *; lia]. Qed.

Definition pv_ss0 : sstate := fss0T_args A_parse_value 160 fs_uar_regions [].
(* MEASURED (vm_compute): at the call of __asan_stack_malloc_0 (0x8300c -> 0x3d484) sp = s1 = the re-aligned
   SAlu AND (SOff 2 (-160)) (SLit (-32)), a0 = 64, a2 = 1 (the flag: `beqz a2` 0x83004 not taken), s3 = a1 (v),
   s4 = a0 (q), s7 = the shadow base atom 32, ra = 0x83010; the prologue saved ra, s0 .. s11 at sp0 - 8 .. sp0 - 104
   and stored 0 at sp0 - 160 *)
Definition pv_ss1 : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs pv_tbl FUEL PC_stack_malloc_0 pv_ss0).


(* ---- the symbolic state at the return address r of __asan_stack_malloc_<cid> in a re-aligned fake-frame caller whose
   journal top sp0 may lie ABOVE its s0 value s (a raised window, FSH_Fn_FORM.md 3a: parse_value / parse_items write
   pj_parse's struct pj_in above their own sp): the saved words at the s0 atom 8, window [lo, hi) with chunks cs; one
   stack slot region at atom nsl (the register holding the re-aligned sp), window [slo, shi); the granted frame at atom
   nF, [0, fs_frame_bytes cid), its flag word at fs_frame_bytes cid - 8 holding eflag.
   Ported from: a Theorem Labs lane's crcs_resume_sm (a working branch c4bfd3bc057,
   lib/A/FSH_check_reject_clean_starved.v:201-289, marked there as to move into FSW_frame.v as fsw_resume_after_stack_mallocU), with the
   journal top sp0 and the s0 value s separated (crcs has s = sp0): the s0 region is read at s, the window bound is
   sp0 - STK <= sp1 + slo, and s <= sp0. Same proof otherwise. ---- *)
Definition pv_resume_regions (lo hi : Z) (cs : list YP09.chunk) (nsl : nat) (slo shi : Z) (nF : nat) (eflag : sv)
  (cid : Z) : list YP09.region :=
  [YP09.mkRegion (Some 8%nat) lo hi lo hi cs;
   YP09.mkRegion (Some nsl) slo shi slo shi [];
   YP09.mkRegion (Some nF) 0 (fs_frame_bytes cid) 0 (fs_frame_bytes cid) [YP09.mkChunk (fs_frame_bytes cid - 8) (CVal 8 eflag)]].
Definition pv_resume_ss (r lo hi : Z) (cs : list YP09.chunk) (nsl : nat) (slo shi : Z) (nF : nat) (eflag : sv)
  (cid : Z) : sstate :=
  mkSS r sr_atoms (pv_resume_regions lo hi cs nsl slo shi nF eflag cid) None
    (mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (nF, mkAF 4096 (2 ^ 47) 5)] [] []).

Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Lemma pv_resume_sm : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc S2 U (W : world tfibsegs) memT mdc mem2 md2 k
  cid pos s sp1 regs2 extra r lo hi cs nsl slo shi nF eflag,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 ((cid, pos) :: own) lyc S2 W (unpoison U mem2) md2 k ->
  ARU tfibsegs B lyc S2 U W mem2 md2 -> ARU tfibsegs B lyc Sc U W memT mdc ->
  acall_kept tfibsegs B lyc Sc W (unpoison U memT) W (unpoison U mem2) (sp1 - ESTACK) sp1 (fun _ => False) ->
  In (cid, pos) (frames S2) -> 0 <= cid ->
  bv_unsigned (ew (Ereg regs2 extra) 8) = s -> bv_unsigned (ew (Ereg regs2 extra) nsl) = sp1 ->
  bv_unsigned (ew (Ereg regs2 extra) nF) = frame_addr lyc cid pos ->
  sv_denot (Ereg regs2 extra) eflag = Z_to_bv 64 (flag_addr lyc cid pos) ->
  rdword (aview tfibsegs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) ->
  lo <= hi <= 0 -> sp1 <= s + lo -> slo <= shi -> sp1 + shi <= s + lo -> sp0 - STK <= sp1 + slo -> s <= sp0 ->
  s mod 16 = 0 ->
  regions_wf (pv_resume_regions lo hi cs nsl slo shi nF eflag cid) = true ->
  Forall (fun c => lo <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= hi) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 extra) (mrestrict (w_H W) memT) s) cs ->
  st_ok tfibsegs (Ereg regs2 extra) (pv_resume_ss r lo hi cs nsl slo shi nF eflag cid)
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc S2 U W memT mdc mem2 md2 k cid pos s sp1 regs2 extra r lo hi cs nsl slo
  shi nF eflag HJ HARU2 HARUc Hkept Hin Hc0 E8 Esl EF Eflag Hflag Hlohi Hlo Hsl Hsh Hsw Hs0 Hal16s Hwf Hcin Hcs.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (ARU_AR tfibsegs B lyc S2 U W mem2 md2 HARU2) as HAR2.
destruct (al_frames _ _ LAWS lyc S2 W (unpoison U mem2) md2 cid pos HAR2 Hin) as (Hal32 & _ & Hfp & _).
destruct (frames_bounds tfibsegs B LAWS lyc S2 W (unpoison U mem2) md2 cid pos HAR2 Hin) as (H4096 & Hfc & _).
destruct (al_flag _ _ LAWS lyc S2 W (unpoison U mem2) md2 cid pos HAR2 Hin) as (_ & _ & Hflapp & Hflc).
pose proof (fs_frame_bytes_pos cid Hc0) as Hfb.
destruct Hkept as (K1 & _).
set (F := frame_addr lyc cid pos) in *. set (FL := flag_addr lyc cid pos) in *.
assert (FL4096 : 4096 <= FL) by (unfold in_app in Hflapp; lia).
rewrite restrict_mkst_fx. unfold pv_resume_ss. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- unfold pv_resume_regions. constructor; [|constructor; [|constructor; [|constructor]]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E8. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable tfibsegs).
      apply (fsw_apresent_unpoison B lyc S2 U W mem2 md2 _ HARU2); [lia|]. apply Hpres. lia.
    * apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hcin c Hc) as Hci.
      pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
      apply (chunk_ok_mbyte _ (mrestrict (w_H W) memT)); [|exact Hck].
      destruct Hci as [Hc1 Hc2]. intros i Hi. apply (mbyte_of_aview tfibsegs).
      rewrite <- (fsw_aview_unpoison_high B lyc S2 U W mem2 md2 _ HARU2) by lia.
      rewrite <- (fsw_aview_unpoison_high B lyc Sc U W memT mdc _ HARUc) by lia.
      apply K1; lia.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Esl. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B lyc S2 U W mem2 md2 _ HARU2); [lia|]. apply Hpres. lia.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite EF. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable tfibsegs).
      destruct (Hfp (F + o) ltac:(lia)) as (Hp & Hno).
      exact (fsw_apresent_notowned B lyc S2 U W mem2 md2 (F + o) HARU2 ltac:(lia) Hno Hp).
    * constructor; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs _ _ F (fs_frame_bytes cid - 8) 8 eflag FL Eflag); [cbn; lia | cbn; lia|].
      replace (F + (fs_frame_bytes cid - 8)) with (F + fs_frame_bytes cid - 8) by lia.
      exact (val_mem_of_rdword tfibsegs (w_H W) mem2 _ _ Hflag).
- apply pairwise_disjoint_of_extents. unfold pv_resume_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E8, Esl, EF.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E8, EF. change (2 ^ 4) with 16. change (2 ^ 5) with 32.
  split; [split; [lia | split; [exact Hal16s | lia]]|]. split; [|exact I].
  split; [lia | split; [exact Hal32 | lia]].
Qed.
End R.

(* the env of the walk after the grant: atom 32 the shadow base, atoms 33 .. 45 the thirteen words the prologue saved
   (ra, s0, s1, s2 .. s11 of the entry, at s0 - 8 .. s0 - 104), atom 46 the flag address; the walk's own atoms follow
   (pv_xs: atom 47 the frame's shadow address, 48 cur = in->p, 49 end = in->end, 50 the text byte at cur) *)
Definition pv_extra0 (regs : bvmap 5 word) (flag : Z) : list word :=
  [Z_to_bv 64 SHADOW_OFF; YK11.getr regs 1%bv; YK11.getr regs 8%bv; YK11.getr regs 9%bv; YK11.getr regs 18%bv;
   YK11.getr regs 19%bv; YK11.getr regs 20%bv; YK11.getr regs 21%bv; YK11.getr regs 22%bv; YK11.getr regs 23%bv;
   YK11.getr regs 24%bv; YK11.getr regs 25%bv; YK11.getr regs 26%bv; YK11.getr regs 27%bv; Z_to_bv 64 flag].
Definition pv_xs (shF cur endv c : Z) : list word := [Z_to_bv 64 shF; Z_to_bv 64 cur; Z_to_bv 64 endv; Z_to_bv 64 c].
Definition pv_sv_chunks : list YP09.chunk :=
  map (fun k => YP09.mkChunk (- 8 * (Z.of_nat k + 1)) (CVal 8 (SOff (33 + k) 0))) (seq 0 13).
Lemma pv_sv_chunks_eq : pv_sv_chunks =
  [YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0));
   YP09.mkChunk (-104) (CVal 8 (SOff 45 0))].
Proof. reflexivity. Qed.
(* the state at 0x83010: the saved words at s0, the re-aligned slot 0x30(s1) (atom 9), the frame at atom 10 (a0) *)
Definition pv_ss2 : sstate := pv_resume_ss 0x83010 (-104) 0 pv_sv_chunks 9 0x30 0x38 10 (SOff 46 0) 0.

(* ---- the white-space loop head 0x830e0 (pf.c skip_ws, inlined in parse_value): a0 = a1 = cur (atom 48), a2 = end
   (atom 49), a3 = 32, a4 = the white-space mask (bits 9, 10, 13, 32), s11 = the shadow address of q (s4); every
   other register is its own atom. Regions: q's two words (atom 20 = s4; only in->p writable), the text byte at cur
   (atom 48, read-only, value atom 50), the thirteen saved words at s0 (atom 8, read-only), the frame's flag word
   (atom 26 = s10, read-only). The env is Ereg regs (pv_extra0 regs0 FL ++ [shadow (F); cur; end; c]). ---- *)
Definition pv_mask : Z := 4294977024.
Definition pv_hd_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 10%bv (SOff 48 0)) 11%bv (SOff 48 0)) 12%bv (SOff 49 0))
    13%bv (SLit 32)) 14%bv (SLit pv_mask)) 27%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 0) (SLit 3)) (SOff 23 0)).
Definition pv_q_region (c0 : sv) : YP09.region :=
  YP09.mkRegion (Some 20%nat) 0 24 0 8 [YP09.mkChunk 0 (CVal 8 c0); YP09.mkChunk 8 (CVal 8 (SOff 49 0))].
Definition pv_txt_region : YP09.region := YP09.mkRegion (Some 48%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 50 0))].
Definition pv_s0_region : YP09.region := YP09.mkRegion (Some 8%nat) (-104) 0 0 0 pv_sv_chunks.
Definition pv_flag_region : YP09.region := YP09.mkRegion (Some 26%nat) 56 64 0 0 [YP09.mkChunk 56 (CVal 8 (SOff 46 0))].
Definition pv_hd_facts : facts :=
  mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (20%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3);
           (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (26%nat, mkAF 4096 (2 ^ 47) 5);
           (48%nat, mkAF 4096 (2 ^ 47 - 8) 0); (50%nat, mkAF 0 255 0)] [] [].
Definition pv_hd_regions : list YP09.region := [pv_q_region (SOff 48 0); pv_txt_region; pv_s0_region; pv_flag_region].
Definition pv_hd : sstate := mkSS 0x830e0 pv_hd_regs pv_hd_regions None pv_hd_facts.
Definition pv_SH : list shent := [mkSHE 20 0 24; mkSHE 26 64 0; mkSHE 48 0 1].
Definition pv_Bx : sv := SOff 23 0.
(* the thirteen saved words, in chunk order (s0 - 8 .. s0 - 104) *)
Definition pv_saved (regs : bvmap 5 word) : list word := firstn 13 (tl (pv_extra0 regs 0)).
Definition pv_saved_ok (m : word -> option byte) (s : Z) (regs : bvmap 5 word) : Prop :=
  forall j, (j < 13)%nat -> val_mem tfibsegs m (s - 8 * (Z.of_nat j + 1)) 8 (bv_unsigned (nth j (pv_saved regs) (Z_to_bv 64 0))).

Section H. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.


Lemma pv_chunk_xfer : forall E1 E2 (m : word -> option byte) base o (n : N) e1 e2, sv_denot E1 e1 = sv_denot E2 e2 ->
  YP09.chunk_ok tfibsegs E1 m base (YP09.mkChunk o (CVal n e1)) -> YP09.chunk_ok tfibsegs E2 m base (YP09.mkChunk o (CVal n e2)).
Proof.
intros E1 E2 m base o n e1 e2 H Hc i Hi. destruct (Hc i Hi) as (b & Hb & Hm). exists b. split; [|exact Hm].
cbn [cbyte YP09.c_val YP09.c_off] in *. rewrite <- H. exact Hb.
Qed.

Lemma pv_shadow_denot : forall E (p b : nat) pv Bv, ew E p = Z_to_bv 64 pv -> 0 <= pv < 2 ^ 64 ->
  ew E b = Z_to_bv 64 Bv -> 0 <= Bv -> Bv + pv / 8 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff p 0) (SLit 3)) (SOff b 0)) = Z_to_bv 64 (pv / 8 + Bv).
Proof.
intros E p b pv Bv Hp Hpv Hb HB0 HB1. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
pose proof (Z.div_pos pv 8 ltac:(lia) ltac:(lia)) as Hd.
rewrite U_srl3, (U_atom E p pv Hp Hpv), (U_atom E b Bv Hb ltac:(lia)).
apply zcanon_id. unfold M64. lia.
Qed.

Lemma pv_hd_ok : forall (H : word -> bool) regs mem regs0 F FL shF cur endv c s q,
  YK11.getr regs 10%bv = Z_to_bv 64 cur -> YK11.getr regs 11%bv = Z_to_bv 64 cur ->
  YK11.getr regs 12%bv = Z_to_bv 64 endv -> YK11.getr regs 13%bv = Z_to_bv 64 32 ->
  YK11.getr regs 14%bv = Z_to_bv 64 pv_mask -> YK11.getr regs 23%bv = Z_to_bv 64 SHADOW_OFF ->
  YK11.getr regs 8%bv = Z_to_bv 64 s -> YK11.getr regs 20%bv = Z_to_bv 64 q -> YK11.getr regs 26%bv = Z_to_bv 64 F ->
  YK11.getr regs 27%bv = Z_to_bv 64 (q / 8 + SHADOW_OFF) ->
  2 ^ 46 <= s <= 2 ^ 47 -> s mod 16 = 0 -> 2 ^ 46 <= q <= 2 ^ 47 - 24 -> q mod 8 = 0 ->
  4096 <= F <= 2 ^ 47 -> F mod 32 = 0 -> 4096 <= cur <= 2 ^ 47 - 8 -> 0 <= c <= 255 -> 0 <= endv < 2 ^ 64 ->
  0 <= FL < 2 ^ 64 -> 0 <= shF < 2 ^ 64 ->
  s <= q -> F + 64 <= s - 104 -> (cur + 1 <= q \/ q + 24 <= cur) -> (cur + 1 <= s - 104 \/ s <= cur) ->
  (cur + 1 <= F + 56 \/ F + 64 <= cur) ->
  val_mem tfibsegs (mrestrict H mem) q 8 cur -> val_mem tfibsegs (mrestrict H mem) (q + 8) 8 endv ->
  (forall o, 0 <= o < 8 -> writable_at tfibsegs (mrestrict H mem) (q + o)) ->
  val_mem tfibsegs (mrestrict H mem) cur 1 c -> pv_saved_ok (mrestrict H mem) s regs0 ->
  val_mem tfibsegs (mrestrict H mem) (F + 56) 8 FL ->
  st_ok tfibsegs (Ereg regs (pv_extra0 regs0 FL ++ pv_xs shF cur endv c)) pv_hd
    (restrict H (mkst regs (Z_to_bv 64 0x830e0) mem (seg_rom tfibsegs))).
Proof.
intros H regs mem regs0 F FL shF cur endv c s q R10 R11 R12 R13 R14 R23 R8 R20 R26 R27 Hs Hs16 Hq Hq8 HF HF32 Hcur Hc
  Hend HFL HshF Hsq HFs Hcq Hcs HcF Vq0 Vq8 Wq Vc Vsv Vfl.
set (E := Ereg regs (pv_extra0 regs0 FL ++ pv_xs shF cur endv c)).
assert (A : forall (r : bv 5) n z, Z.of_nat n = bv_unsigned r -> getr regs r = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
  bv_unsigned (ew E n) = z) by (intros r n z Hn Hr Hz; subst E; rewrite (ew_Ereg_nat _ _ n r Hn), Hr; apply wz; exact Hz).
assert (X : forall j z, nth j (pv_extra0 regs0 FL ++ pv_xs shF cur endv c) (Z_to_bv 64 0) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
  bv_unsigned (ew E (32 + j)) = z) by (intros j z Hj Hz; subst E; rewrite ew_Ereg_extra, Hj; apply wz; exact Hz).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (E8 : bv_unsigned (ew E 8) = s) by (apply (A 8%bv); [reflexivity | exact R8 | lia]).
assert (E20 : bv_unsigned (ew E 20) = q) by (apply (A 20%bv); [reflexivity | exact R20 | lia]).
assert (E23 : bv_unsigned (ew E 23) = SHADOW_OFF) by (apply (A 23%bv); [reflexivity | exact R23 | unfold SHADOW_OFF; lia]).
assert (E26 : bv_unsigned (ew E 26) = F) by (apply (A 26%bv); [reflexivity | exact R26 | lia]).
assert (E48 : bv_unsigned (ew E 48) = cur) by (apply (X 16%nat); [reflexivity | lia]).
assert (E49 : bv_unsigned (ew E 49) = endv) by (apply (X 17%nat); [reflexivity | lia]).
assert (E50 : bv_unsigned (ew E 50) = c) by (apply (X 18%nat); [reflexivity | lia]).
assert (E46 : bv_unsigned (ew E 46) = FL) by (apply (X 14%nat); [reflexivity | lia]).
assert (D : forall n v, bv_unsigned (ew E n) = v -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
  by (intros n v Hn; rewrite fsw_SOff0, <- Hn; symmetry; apply Z_to_bv_bv_unsigned).
rewrite restrict_mkst_fx. unfold pv_hd. apply (entry_st_ok_full tfibsegs).
- unfold pv_hd_regs.
  repeat (apply regs_ok_pin; [|discriminate|]); [apply regs_ok_Ereg| | | | | |].
  + rewrite R10. symmetry. exact (D 48%nat cur E48).
  + rewrite R11. symmetry. exact (D 48%nat cur E48).
  + rewrite R12. symmetry. exact (D 49%nat endv E49).
  + rewrite R13. reflexivity.
  + rewrite R14. reflexivity.
  + rewrite R27. symmetry.
    apply (pv_shadow_denot E 20 23 q SHADOW_OFF); [subst E; rewrite (ew_Ereg_nat _ _ 20 20%bv eq_refl), R20; reflexivity | lia
    | subst E; rewrite (ew_Ereg_nat _ _ 23 23%bv eq_refl), R23; reflexivity | unfold SHADOW_OFF; lia
    | unfold SHADOW_OFF; pose proof (Z.div_le_mono q (2 ^ 47) 8 ltac:(lia) ltac:(lia)); lia].
- vm_compute. reflexivity.
- unfold pv_hd_regions. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
  + unfold region_ok, pv_q_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E.
    rewrite E20. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wq; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val tfibsegs _ _ q 0 8 (SOff 48 0) cur (D 48%nat cur E48)); [cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vq0].
    * apply (chunk_ok_val tfibsegs _ _ q 8 8 (SOff 49 0) endv (D 49%nat endv E49)); [cbn; lia | cbn; lia | exact Vq8].
  + unfold region_ok, pv_txt_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E.
    rewrite E48. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ cur 0 1 (SOff 50 0) c (D 50%nat c E50)); [cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vc].
  + unfold region_ok, pv_s0_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E.
    rewrite E8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    rewrite pv_sv_chunks_eq.
    assert (SV : forall j, (j < 13)%nat -> YP09.chunk_ok tfibsegs E (mrestrict H mem) s
      (YP09.mkChunk (- 8 * (Z.of_nat j + 1)) (CVal 8 (SOff (33 + j) 0)))).
    { intros j Hj. apply (chunk_ok_val tfibsegs _ _ s _ 8 _ (bv_unsigned (nth j (pv_saved regs0) (Z_to_bv 64 0)))).
      - rewrite Z_to_bv_bv_unsigned. subst E. change (33 + j)%nat with (32 + S j)%nat. rewrite fsw_extra_atom.
        do 13 (destruct j as [|j]; [reflexivity|]). lia.
      - change (8 * Z.of_N 8) with 64. pose proof (u64_range (nth j (pv_saved regs0) (Z_to_bv 64 0))). lia.
      - cbn. lia.
      - replace (s + - 8 * (Z.of_nat j + 1)) with (s - 8 * (Z.of_nat j + 1)) by lia. exact (Vsv j Hj). }
    repeat (apply Forall_cons; [match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff ?a 0))) =>
      let j := eval vm_compute in (a - 33)%nat in exact (SV j ltac:(lia)) end|]). apply Forall_nil.
  + unfold region_ok, pv_flag_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E.
    rewrite E26. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ F 56 8 (SOff 46 0) FL (D 46%nat FL E46)); [cbn; lia | cbn; lia | exact Vfl].
- apply pairwise_disjoint_of_extents. unfold pv_hd_regions, pv_q_region, pv_txt_region, pv_s0_region, pv_flag_region,
    extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite E20, E48, E8, E26.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- unfold pv_hd_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite E8, E20, E23, E26, E48, E50. change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 5) with 32.
  rewrite Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try lia; unfold SHADOW_OFF; lia.
Qed.
End H.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the image cells of B (owner RELOC: fs's TfibLib gives them, cgif A/ACeg.v:25-36; until it builds on S0 they are
   named premises, as FSW_K fsw_entryT / fsw_uar_regions_ok take them; FsShadowSyms will replace the first two).
   Values MEASURED on the pinned fs.asan: GOT 0x9f6f0 -> 0xa7f38, GOT 0x9f748 -> 0xa7f40. *)
Hypothesis HGOT : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address.
Hypothesis HCELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address.
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.
(* the integrator's narrowing rule (a Theorem Labs lane 12:0xZ): NOT FsRt whole - this walk uses exactly its class-0 field,
   S0's FSH_Rt.fr_stack_malloc_0, which is the conjunction below (pc_stack_malloc 0 pinned, and the class-0 contract) *)
Hypothesis SM0 : pc_stack_malloc (as_code B) 0 = PC_stack_malloc_0 /\
  FSupoisonU.astack_malloc_realizesU tfibsegs B 0.
(* the unit laws fsw_stack_malloc_atU takes (FSW_frame.v Section f) *)
Hypothesis errno_low : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.

Lemma pv_stk : forall k, (k <= 2)%nat -> 4351 <= STK_parse_value (2 - k).
Proof. intros k Hk. destruct k as [|[|[|k]]]; [vm_compute; discriminate..| lia]. Qed.

Lemma pv_entry : forall k ly S U (W : world tfibsegs) regs mem md ch, (k <= 2)%nat ->
  afn_preU tfibsegs B (STK_parse_value (2 - k)) ly S U W regs mem md ch ->
  st_ok tfibsegs (Ereg regs fs_extraT) pv_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_parse_value) mem (seg_rom tfibsegs))).
Proof.
intros k ly S U W regs mem md ch Hk HPRE.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _). pose proof (pv_stk k Hk) as FS.
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

(* segment 0: the prologue, the re-align and the flag test, up to the call of __asan_stack_malloc_0 *)
Lemma pv_seg0 : forall k ly S U (W : world tfibsegs) regs mem md ch FP ot (Q : world tfibsegs -> config -> Prop),
  (k <= 2)%nat ->
  afn_preU tfibsegs B (STK_parse_value (2 - k)) ly S U W regs mem md ch ->
  spZ regs <= ot -> ot mod 16 = 0 -> ot <= ly_top ly -> (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  (forall ms mat,
     st_ok tfibsegs (Ereg regs fs_extraT) pv_ss1 (restrict (w_H W) ms) ->
     ajournal tfibsegs B (STK_parse_value (2 - k) + (ot - spZ regs)) ot FP ly S W (unpoison U mem) md [] ly S W
       (unpoison U (ms_mem ms)) (with_vm_backing (m_vm_lazy md) mat md) 0 ->
     ARU tfibsegs B ly S U W (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) ->
     frame_of (Ereg regs fs_extraT) (ss_mem pv_ss0) mem (ms_mem ms) ->
     frame_of (Ereg regs fs_extraT) (ss_mem pv_ss0) (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) ->
     SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_value regs mem md) Q.
Proof.
intros k ly S U W regs mem md ch FP ot Q Hk HPRE Hot Hal Htop Hpot K.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _). pose proof (pv_stk k Hk) as FS.
pose proof (pv_entry k ly S U W regs mem md ch Hk HPRE) as HS.
pose proof (fsw_ARU B _ ly S U W regs mem md ch HPRE) as HARU.
pose proof (fsw_ajournal_init_ot B _ FP ly S U W regs mem md ch ot HPRE Hot Hal Htop Hpot) as HJ.
assert (Usp : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
unfold YG0d.cfg_at. change (w64 A_parse_value) with (Z_to_bv 64 A_parse_value).
fsw_aj_run_toU pv_tbl_ok HS HJ HARU PC_stack_malloc_0.
{ cbv [pv_ss0 fss0T_args ss_mem fsT_regions_args fsT_regions fs_uar_regions app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - ot);
    [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
exact (K _ _ HS HJ HARU HF HFr).
Qed.

(* the registers at the call of __asan_stack_malloc_0 (read off pv_ss1) *)
Lemma pv_sm_site : forall ly S U (W : world tfibsegs) regs mem md ch k ms, (k <= 2)%nat ->
  afn_preU tfibsegs B (STK_parse_value (2 - k)) ly S U W regs mem md ch ->
  st_ok tfibsegs (Ereg regs fs_extraT) pv_ss1 (restrict (w_H W) ms) ->
  YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) /\
  YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 (32 * ((spZ regs - 160) / 32)) /\
  spZ regs - 176 <= 32 * ((spZ regs - 160) / 32) <= spZ regs - 160 /\ (32 * ((spZ regs - 160) / 32)) mod 32 = 0 /\
  YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 0x83010 /\ YK11.getr (ms_regs ms) 10%bv = Z_to_bv 64 64 /\
  YK11.getr (ms_regs ms) 3%bv = YK11.getr regs 3%bv /\ YK11.getr (ms_regs ms) 4%bv = YK11.getr regs 4%bv /\
  YK11.getr (ms_regs ms) 8%bv = YK11.getr regs 2%bv /\ YK11.getr (ms_regs ms) 23%bv = Z_to_bv 64 SHADOW_OFF /\
  YK11.getr (ms_regs ms) 19%bv = YK11.getr regs 11%bv /\ YK11.getr (ms_regs ms) 20%bv = YK11.getr regs 10%bv.
Proof.
intros ly S U W regs mem md ch k ms Hk HPRE HS.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _). pose proof (pv_stk k Hk) as FS.
set (E := Ereg regs fs_extraT) in *.
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs)) by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl);
  unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (fsw_realign_facts (spZ regs - 160) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (F1 & F2 & F3).
set (sp1 := 32 * ((spZ regs - 160) / 32)) in *.
assert (R2 : YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 sp1).
{ exact (fsw_realign_val E pv_ss1 (restrict (w_H W) ms) 2%bv 2 (-160) (spZ regs) HS
    ltac:(vm_compute; reflexivity) E2 ltac:(unfold spZ; apply u64_range) ltac:(lia)). }
assert (R9 : YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 sp1).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E pv_ss1 ms 9%bv HS).
  lazymatch goal with |- _ = Z_to_bv 64 ?v => change (sr_get (ss_regs pv_ss1) 9%bv) with
    (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32))) (SLit 0)) end.
  rewrite denot_lit_U, U_SAlu. f_equal. cbn [zalu_raw]. rewrite U_SLit.
  assert (UA : YP0e.U E (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32))) = sp1).
  { unfold YP0e.U. rewrite (denot_and_m32 E 2 (spZ regs) (-160) E2 ltac:(lia) ltac:(lia) ltac:(unfold spZ; apply u64_range)).
    apply wz. lia. }
  rewrite UA. change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
split; [exact R2|]. split; [exact R9|]. split; [lia|]. split; [exact F2|].
split; [exact (fsw_reg_lit _ E _ ms 1%bv 0x83010 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
split; [exact (fsw_reg_lit _ E _ ms 10%bv 64 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 8%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split.
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E pv_ss1 ms 23%bv HS).
  change (sr_get (ss_regs pv_ss1) 23%bv) with (SOff 32 0). rewrite fsw_SOff0.
  subst E. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 19%bv 11%bv 11 HS ltac:(vm_compute; reflexivity) eq_refl)|].
exact (fsw_reg_atom _ regs fs_extraT _ ms 20%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl).
Qed.
Lemma pv_sm : forall k ly S U (W : world tfibsegs) regs mem md ch FP ot ms mat (Q : world tfibsegs -> config -> Prop),
  (k <= 2)%nat ->
  afn_preU tfibsegs B (STK_parse_value (2 - k)) ly S U W regs mem md ch ->
  Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k) -> spZ regs <= ot -> ot mod 16 = 0 ->
  st_ok tfibsegs (Ereg regs fs_extraT) pv_ss1 (restrict (w_H W) ms) ->
  ajournal tfibsegs B (STK_parse_value (2 - k) + (ot - spZ regs)) ot FP ly S W (unpoison U mem) md [] ly S W
    (unpoison U (ms_mem ms)) (with_vm_backing (m_vm_lazy md) mat md) 0 ->
  ARU tfibsegs B ly S U W (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) ->
  (forall S2 regs2 mem2 md2 pos,
     (forall xs, st_ok tfibsegs (Ereg regs2 (pv_extra0 regs (flag_addr ly 0 pos) ++ xs)) pv_ss2
       (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x83010) mem2 (seg_rom tfibsegs)))) ->
     ajournal tfibsegs B (STK_parse_value (2 - k) + (ot - spZ regs)) ot FP ly S W (unpoison U mem) md [(0, pos)]
       ly S2 W (unpoison U mem2) md2 0 ->
     ARU tfibsegs B ly S2 U W mem2 md2 ->
     aregs_preserved (ms_regs ms) regs2 -> YK11.getr regs2 10%bv = w64 (frame_addr ly 0 pos) ->
     ablocks B ly S2 = ablocks B ly S -> frames S2 = (0, pos) :: frames S -> ~ In (0, pos) (frames S) ->
     st_nev S2 = st_nev S -> blocks_bytes S2 = blocks_bytes S ->
     zero_shadow (aview tfibsegs (w_H W) mem2) SHADOW_OFF (frame_addr ly 0 pos) (fs_frame_bytes 0) ->
     acall_kept tfibsegs B ly S W (unpoison U (ms_mem ms)) W (unpoison U mem2)
       (32 * ((spZ regs - 160) / 32) - ESTACK) (32 * ((spZ regs - 160) / 32)) (fun _ => False) ->
     SRr tfibsegs W (mkCfg (mkst regs2 (Z_to_bv 64 0x83010) mem2 (seg_rom tfibsegs)) md2) Q) ->
  SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) Q.
Proof.
intros k ly S U W regs mem md ch FP ot ms mat Q Hk HPRE Hfrl Hot Hot16' HS HJ HARU K.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _). pose proof (pv_stk k Hk) as FS.
pose proof HPRE as (HAP & _ & _). pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & _).
destruct (pv_sm_site ly S U W regs mem md ch k ms Hk HPRE HS)
  as (R2 & R9 & Fsp1 & Fal & R1 & R10 & R3 & R4 & R8 & R23 & R19 & R20).
set (sp1 := 32 * ((spZ regs - 160) / 32)) in *.
destruct SM0 as [Hpc0 ASM0].
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ pv_ss1 ms HS eq_refl).
change (ss_pc pv_ss1) with PC_stack_malloc_0. rewrite <- Hpc0.
(* the saved words at the call, read off pv_ss1's stack region *)
assert (HCS : Forall (YP09.chunk_ok tfibsegs (Ereg regs fs_extraT) (mrestrict (w_H W) (ms_mem ms)) (spZ regs))
  (YP09.r_chunks (YP09.mkRegion (Some 2%nat) (-160) 0 (-160) 0
    [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
     YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-160) (CVal 8 (SLit 0))]))).
{ pose proof (fsw_region_nth _ _ _ 0 _ HS ltac:(vm_compute; reflexivity)) as (_ & _ & _ & Hc).
  cbn [YP09.r_base base_val ms_mem restrict] in Hc.
  rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl) in Hc. exact Hc. }
cbn [YP09.r_chunks] in HCS.
eapply SRr_bind.
{ eapply (fsw_stack_malloc_atU B errno_low ML SMP 0 ASM0 ltac:(lia) W (ms_regs ms) (ms_mem ms)
    (STK_parse_value (2 - k) + (ot - spZ regs)) ot FP ly S W (unpoison U mem) md [] ly S U _ 0 (sp1 - ot) _ HJ HARU).
  - unfold spZ at 1. rewrite R2. rewrite wz by lia. lia.
  - assert (Hs1 : sp1 mod 16 = 0) by (subst sp1;
      replace (32 * ((spZ regs - 160) / 32)) with (((spZ regs - 160) / 32 * 2) * 16) by lia; apply Z_mod_mult).
    assert (Hot16 : ot mod 16 = 0) by exact Hot16'.
    rewrite Zminus_mod, Hs1, Hot16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - vm_compute. reflexivity.
  - exact (fs_fake_granted 0 (frames S) ltac:(lia) ltac:(unfold FRL_parse_value, FRL_MAX in *; lia)). }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & Ec2 & HJ2 & HARU2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin
  & Hnev2 & Hbb2 & Hz & Hflag & HK).
replace (ot + (sp1 - ot) - ESTACK) with (sp1 - ESTACK) in HK by lia. replace (ot + (sp1 - ot)) with sp1 in HK by lia.
assert (Ec2' : c2 = mkCfg (mkst regs2 (Z_to_bv 64 0x83010) mem2 (seg_rom tfibsegs)) md2) by exact Ec2.
rewrite Ec2'. clear Ec2 Ec2'.
assert (Hin0 : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (Q8 : getr regs2 8%bv = getr regs 2%bv) by (rewrite (fsw_pres _ _ 8%bv HP2 ltac:(pv_cs)); exact R8).
assert (Q9 : getr regs2 9%bv = Z_to_bv 64 sp1) by (rewrite (fsw_pres _ _ 9%bv HP2 ltac:(pv_cs)); exact R9).
apply (K S2 regs2 mem2 md2 pos); try assumption.
intros xs. set (E2 := Ereg regs2 (pv_extra0 regs (flag_addr ly 0 pos) ++ xs)).
eapply (pv_resume_sm B _ ot FP ly S W (unpoison U mem) md [] ly S S2 U W (ms_mem ms) _ mem2 md2 0 0 pos (spZ regs) sp1
  regs2 _ 0x83010 (-104) 0 pv_sv_chunks 9 0x30 0x38 10 (SOff 46 0) HJ2 HARU2 HARU HK Hin0 ltac:(lia)).
- subst E2. rewrite (ew_Ereg_nat _ _ 8 8%bv eq_refl), Q8. reflexivity.
- subst E2. rewrite (ew_Ereg_nat _ _ 9 9%bv eq_refl), Q9. apply wz. lia.
- subst E2. rewrite (ew_Ereg_nat _ _ 10 10%bv eq_refl), Ha0. unfold w64.
  pose proof (ARU_AR tfibsegs B ly S2 U W mem2 md2 HARU2) as HAR2.
  destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin0) as (Fb1 & Fb2 & _).
  pose proof (fs_frame_bytes_pos 0 ltac:(lia)). apply wz. lia.
- subst E2. change (SOff 46 0) with (SOff (32 + 14) 0). rewrite fsw_extra_atom. reflexivity.
- exact Hflag.
- lia.
- lia.
- lia.
- lia.
- lia.
- lia.
- exact Hal16.
- vm_compute. reflexivity.
- unfold pv_sv_chunks. cbn [map seq]. repeat (apply Forall_cons; [cbn [YP09.c_off YP09.c_len YP09.c_val cv_len Z.of_N Z.of_nat]; lia|]). apply Forall_nil.
- rewrite pv_sv_chunks_eq.
  repeat (apply Forall_cons; [eapply pv_chunk_xfer;
    [| eapply (proj1 (Forall_forall _ _) HCS); repeat (first [left; reflexivity | right])]; subst E2; reflexivity|]).
  apply Forall_nil.
Qed.

End W.

Ltac pv_bv := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?v)] =>
  rewrite (unsigned_lit_small v) by (unfold SHADOW_OFF in *; lia) end.
Ltac pv_fact HS n af :=
  lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
    let H := fresh "HS" in
    assert (H : st_ok tfibsegs Ev (add_atom ssx n af) msx);
    [ apply (st_ok_add_fact tfibsegs Ev ssx msx n af HS); unfold afact_ok; cbn [af_lo af_hi af_al2]
    | clear HS; rename H into HS ] end.
Ltac pv_disj :=
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
    let rs2 := eval vm_compute in rsy in let r2 := eval vm_compute in ry in change (all_disjoint Ey r2 rs2) end;
  apply all_disjoint_of_extents; unfold extent_of_region; cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint].

Ltac pv_norm HS := lazymatch type of HS with st_ok ?sg ?Ev ?ssx ?msx =>
  let ss' := eval vm_compute in ssx in change (st_ok sg Ev ss' msx) in HS end.

Ltac pv_addreg HS r ROK :=
  lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
    let H := fresh "HSa" in pose proof (ast_ok_add_region tfibsegs Ev ssx msx r HS eq_refl ROK) as H;
    lazymatch type of H with _ -> ?T =>
      let H2 := fresh "HSb" in assert (H2 : T); [apply H; pv_disj | clear HS H; rename H2 into HS] end end.

Section H2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the stack's shadow reads 0 (AR_zshadow_law at zero_shadow_ranges' head, the stack, page-aligned by lo_top).
   Port-from: fs lib/A/ACex.v:313-337 stack_cells8 / RA_stack (cgif's A/ACex.v); ACex imports A/ACej.v, which does
   not compile on this base, so the two are restated here with the same proofs. *)
Lemma pv_stack_cells8 : forall lo hi x, lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= x -> x + 8 <= hi ->
  lo mod 8 = 0 /\ (hi - lo) mod 8 = 0.
Proof.
intros lo hi x Hlo Hhi H1 H2.
pose proof (Z.div_mod lo 4096 ltac:(lia)) as A. pose proof (Z.div_mod hi 4096 ltac:(lia)) as C.
rewrite Hlo, Z.add_0_r in A. rewrite Hhi, Z.add_0_r in C. split.
- rewrite A. replace (4096 * (lo / 4096)) with ((512 * (lo / 4096)) * 8) by lia. apply Z_mod_mult.
- rewrite A, C. replace (4096 * (hi / 4096) - 4096 * (lo / 4096)) with ((512 * (hi / 4096) - 512 * (lo / 4096)) * 8) by lia.
  apply Z_mod_mult.
Qed.
Lemma pv_stack_ra : forall ly S (W : world tfibsegs) mem md x n,
  AR tfibsegs B ly S W mem md -> ly_stk_lo ly <= x -> x + n <= ly_stk_hi ly -> x mod 8 = 0 -> n mod 8 = 0 -> 8 <= n ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Proof.
intros ly S W mem md x n HAR Hlo Hhi Hx8 Hn8 Hn.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _). unfold page_aligned in Hpal, Hpah.
pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity)) as Hz.
cbn [fst snd] in Hz.
destruct (pv_stack_cells8 _ _ x Hpal Hpah ltac:(lia) ltac:(lia)) as [Hm1 Hm2].
eapply range_addressable_sub; [apply zero_shadow_range; [exact Hm1 | exact Hm2 | exact Hz] | lia | lia].
Qed.
(* a shadow byte of an address at or above alloc_ceiling is no user-poisoned shadow byte (U's ranges lie in live blocks,
   below alloc_ceiling) *)
Lemma pv_unpoison_shadow_high : forall ly S U (W : world tfibsegs) mem md x,
  ARU tfibsegs B ly S U W mem md -> alloc_ceiling <= x < 2 ^ 47 ->
  unpoison U mem (Z_to_bv 64 (SHADOW_OFF + x / 8)) = mem (Z_to_bv 64 (SHADOW_OFF + x / 8)).
Proof.
intros ly S U W mem md x HARU Hx. pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _).
apply unpoison_out.
assert (Hx8 : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite (wz (SHADOW_OFF + x / 8)) by (unfold SHADOW_OFF; lia).
destruct (in_ush U (SHADOW_OFF + x / 8)) eqn:Hs; [|reflexivity]. exfalso.
destruct HARU as (HAR & OK & _).
destruct (ush_granule B ly S U _ OK Hs) as (g & p & n & Hb & G8 & Gs & Gp & Gn).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p n HAR Hb) as (_ & _ & Hc & _).
pose proof (Z.mul_div_le (req_size n) 8 ltac:(lia)).
assert (g / 8 < x / 8).
{ assert (g + 8 <= x) by lia. apply (Z.lt_le_trans _ ((g + 8) / 8)); [|apply Z.div_le_mono; lia].
  replace (g + 8) with (g + 1 * 8) by lia. rewrite Z.div_add by lia. lia. }
unfold shadow_addr in Gs. lia.
Qed.
Lemma pv_ra_unpoison : forall ly S U (W : world tfibsegs) mem md x n,
  ARU tfibsegs B ly S U W mem md -> alloc_ceiling <= x -> x + n <= 2 ^ 47 ->
  range_addressable (aview tfibsegs (w_H W) (unpoison U mem)) SHADOW_OFF x n ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Proof.
intros ly S U W mem md x n HARU Hx Hn HRA y Hy. destruct (HRA y Hy) as (s & Es & Hok). exists s. split; [|exact Hok].
rewrite <- Es. unfold shadow_of_addr. apply (aview_at tfibsegs). symmetry.
exact (pv_unpoison_shadow_high ly S U W mem md y HARU ltac:(lia)).
Qed.
End H2.

Section H3. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* the bytes the walk writes between the grant and the loop: F's frame and shadow, in->p, the saved-word window at s0
   and the slot 0x30(s1) *)
Definition pv_wr (F q s sp1 a : Z) : Prop :=
  (F <= a < F + 64) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8) \/ (q <= a < q + 8) \/
  (s - 104 <= a < s) \/ (sp1 + 48 <= a < sp1 + 56).
Lemma pv_frame_P : forall E rs (m m' : word -> option byte) (P : Z -> Prop), frame_of E rs m m' ->
  (forall a, in_wrange E rs a -> P a) -> forall x : word, ~ P (bv_unsigned x) -> m' x = m x.
Proof. intros E rs m m' P HF HP x Hx. apply HF. intros Hin. exact (Hx (HP _ Hin)). Qed.
Lemma pv_wrange_cases : forall E (r : YP09.region) rs a,
  in_wrange E (r :: rs) a -> (base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r)
    \/ in_wrange E rs a.
Proof. intros E r rs a (r' & [<-|Hin] & Ha); [left; exact Ha | right; exists r'; split; assumption]. Qed.
Lemma pv_wrange_nil : forall E a, ~ in_wrange E [] a.
Proof. intros E a (r & [] & _). Qed.
(* the saved words, read off a region at the s0 atom carrying pv_sv_chunks *)
Lemma pv_saved_of_region : forall regs regs0 FL xs (m : word -> option byte) s lo hi wlo whi,
  region_ok tfibsegs (Ereg regs (pv_extra0 regs0 FL ++ xs)) m (YP09.mkRegion (Some 8%nat) lo hi wlo whi pv_sv_chunks) ->
  bv_unsigned (ew (Ereg regs (pv_extra0 regs0 FL ++ xs)) 8) = s -> pv_saved_ok m s regs0.
Proof.
intros regs regs0 FL xs m s lo hi wlo whi HR Hs j Hj.
assert (Hin : In (YP09.mkChunk (- 8 * (Z.of_nat j + 1)) (CVal 8 (SOff (33 + j) 0))) pv_sv_chunks).
{ unfold pv_sv_chunks. apply (in_map (fun k => YP09.mkChunk (- 8 * (Z.of_nat k + 1)) (CVal 8 (SOff (33 + k) 0)))).
  apply in_seq. lia. }
pose proof (fsw_field _ m 8 s pv_sv_chunks lo hi wlo whi _ 8 _ (bv_unsigned (nth j (pv_saved regs0) (Z_to_bv 64 0))) HR Hs Hin)
  as Hv.
replace (s + - 8 * (Z.of_nat j + 1)) with (s - 8 * (Z.of_nat j + 1)) in Hv by lia. apply Hv.
- rewrite Z_to_bv_bv_unsigned. change (33 + j)%nat with (32 + S j)%nat. rewrite fsw_extra_atom.
  do 13 (destruct j as [|j]; [reflexivity|]). lia.
- change (8 * Z.of_N 8) with 64. apply u64_range.
- cbn. lia.
Qed.
End H3.

Section H4. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* a byte fact survives a memory change that keeps every byte outside a set P *)
Lemma pv_mbyte_keep : forall (m m' : word -> option byte) (P : Z -> Prop) a,
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) -> 0 <= a < 2 ^ 64 -> ~ P a ->
  mbyte tfibsegs m' a = mbyte tfibsegs m a.
Proof.
intros m m' P a HK Ha HP. unfold mbyte. rewrite (HK (Z_to_bv 64 a)); [reflexivity|].
rewrite (wz a Ha). exact HP.
Qed.
Lemma pv_val_keep : forall (m m' : word -> option byte) (P : Z -> Prop) a (n : nat) v,
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall k, 0 <= k < Z.of_nat n -> ~ P (a + k)) ->
  val_mem tfibsegs m a n v -> val_mem tfibsegs m' a n v.
Proof.
intros m m' P a n v HK Ha Hn HP Hv k Hk. rewrite (pv_mbyte_keep m m' P (a + Z.of_nat k) HK ltac:(lia) (HP (Z.of_nat k) ltac:(lia))).
exact (Hv k Hk).
Qed.
End H4.

Ltac pv_reg HS H r name :=
  lazymatch type of HS with st_ok _ ?Ex ?sx (restrict _ ?msx) =>
    pose proof (st_ok_restrict_reg tfibsegs H Ex sx msx r HS) as name;
    lazymatch type of name with _ = sv_denot _ ?t =>
      let t' := eval vm_compute in t in change t with t' in name end end.
Ltac pv_wr_tac rw :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; cbn [ss_mem add_cond] in Ha;
  repeat (apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    rw Ha; unfold pv_wr; lia|]);
  exfalso; exact (pv_wrange_nil _ _ Ha).

Ltac pv_region HS i name :=
  lazymatch type of HS with st_ok _ _ ?sx _ =>
    let r := eval vm_compute in (nth i (ss_mem sx) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (fsw_region_nth _ _ _ i r HS ltac:(vm_compute; reflexivity)) as name end.

Section S1. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Lemma pv_seg1 : forall STK ot FP ly S S2 U (W : world tfibsegs) regs mem md regs2 mem2 md2 pos s sp1 v q p endv c0
  (Q : world tfibsegs -> config -> Prop),
  let F := frame_addr ly 0 pos in let FL := flag_addr ly 0 pos in
  let E := Ereg regs2 (pv_extra0 regs FL ++ pv_xs (SHADOW_OFF + F / 8) p endv c0) in
  st_ok tfibsegs E pv_ss2 (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x83010) mem2 (seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U mem2) md2 0 ->
  ARU tfibsegs B ly S2 U W mem2 md2 -> In (0, pos) (frames S2) ->
  YK11.getr regs2 10%bv = Z_to_bv 64 F -> YK11.getr regs2 23%bv = Z_to_bv 64 SHADOW_OFF ->
  YK11.getr regs2 20%bv = Z_to_bv 64 q -> YK11.getr regs2 8%bv = Z_to_bv 64 s -> YK11.getr regs2 9%bv = Z_to_bv 64 sp1 ->
  YK11.getr regs2 19%bv = Z_to_bv 64 v ->
  (* gp and tp, kept by the grant (its aregs_preserved) and by this segment's run *)
  YK11.getr regs2 3%bv = YK11.getr regs 3%bv -> YK11.getr regs2 4%bv = YK11.getr regs 4%bv ->
  YK11.getr regs2 2%bv = Z_to_bv 64 sp1 ->
  2 ^ 46 <= q <= 2 ^ 47 - 24 -> q mod 8 = 0 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> alloc_ceiling + 4096 <= sp1 ->
  4096 <= p <= 2 ^ 47 - 8 -> 0 <= endv < 2 ^ 64 ->
  sp1 + 176 <= s + 16 -> s <= q -> s mod 16 = 0 -> ot - STK <= sp1 - 4096 -> q + 24 <= ot ->
  val_mem tfibsegs (mrestrict (w_H W) mem2) q 8 p -> val_mem tfibsegs (mrestrict (w_H W) mem2) (q + 8) 8 endv ->
  p < endv -> 0 <= c0 <= 255 -> val_mem tfibsegs (mrestrict (w_H W) mem2) p 1 c0 -> p + 1 <= alloc_ceiling ->
  (p + 1 <= frame_addr ly 0 pos \/ frame_addr ly 0 pos + 64 <= p) -> (p + 1 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= p) ->
  (forall msh math,
     st_ok tfibsegs (Ereg (ms_regs msh) (pv_extra0 regs FL ++ pv_xs (SHADOW_OFF + F / 8) p endv c0)) pv_hd
       (restrict (w_H W) msh) ->
     ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U (ms_mem msh))
       (with_vm_backing (m_vm_lazy md2) math md2) 0 ->
     ARU tfibsegs B ly S2 U W (ms_mem msh) (with_vm_backing (m_vm_lazy md2) math md2) ->
     (forall x : word, ~ pv_wr F q s sp1 (bv_unsigned x) -> mrestrict (w_H W) (ms_mem msh) x = mrestrict (w_H W) mem2 x) ->
     YK11.getr (ms_regs msh) 8%bv = Z_to_bv 64 s -> YK11.getr (ms_regs msh) 9%bv = Z_to_bv 64 sp1 ->
     YK11.getr (ms_regs msh) 18%bv = Z_to_bv 64 F -> YK11.getr (ms_regs msh) 19%bv = Z_to_bv 64 v ->
     YK11.getr (ms_regs msh) 20%bv = Z_to_bv 64 q -> YK11.getr (ms_regs msh) 23%bv = Z_to_bv 64 SHADOW_OFF ->
     YK11.getr (ms_regs msh) 24%bv = Z_to_bv 64 (SHADOW_OFF + F / 8) ->
     YK11.getr (ms_regs msh) 26%bv = Z_to_bv 64 F ->
     YK11.getr (ms_regs msh) 3%bv = YK11.getr regs 3%bv -> YK11.getr (ms_regs msh) 4%bv = YK11.getr regs 4%bv ->
     YK11.getr (ms_regs msh) 2%bv = Z_to_bv 64 sp1 ->
     SRr tfibsegs W (mkCfg msh (with_vm_backing (m_vm_lazy md2) math md2)) Q) ->
  SRr tfibsegs W (mkCfg (mkst regs2 (Z_to_bv 64 0x83010) mem2 (seg_rom tfibsegs)) md2) Q.
Proof.
intros STK ot FP ly S S2 U W regs mem md regs2 mem2 md2 pos s sp1 v q p endv c0 Q F FL E HS HJ HARU Hin0 R10 R23 R20 R8
  R9 R19 R3 R4 R2 Hq Hq8 Hsp1 Hsp32 Hceil1 Hp Hend Hsps Hsq Hs16 Hstk Hqot Vq0 Vq8 Hpe Hc0 Vc0 Hpc Hpf Hpapp K.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B ly S2 U W mem2 md2 HARU) as HAR2.
destruct (al_frames _ _ LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin0) as (HF32 & HFapp & HFp & HFSp).
destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin0) as (HF4096 & HFc & _).
change (fs_frame_bytes 0) with 64 in *. fold F in HF32, HFapp, HFp, HFSp, HF4096, HFc.
assert (EA : forall (r : bv 5) n z, Z.of_nat n = bv_unsigned r -> getr regs2 r = Z_to_bv 64 z -> ew E n = Z_to_bv 64 z)
  by (intros r n z Hn Hr; subst E; rewrite (ew_Ereg_nat _ _ n r Hn), Hr; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 F) by (apply (EA 10%bv); [reflexivity | exact R10]).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (apply (EA 23%bv); [reflexivity | exact R23]).
assert (E20 : ew E 20 = Z_to_bv 64 q) by (apply (EA 20%bv); [reflexivity | exact R20]).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (apply (EA 9%bv); [reflexivity | exact R9]).
assert (E47 : ew E 47 = Z_to_bv 64 (SHADOW_OFF + F / 8))
  by (subst E; change 47%nat with (32 + 15)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E48 : ew E 48 = Z_to_bv 64 p) by (subst E; change 48%nat with (32 + 16)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E49 : ew E 49 = Z_to_bv 64 endv) by (subst E; change 49%nat with (32 + 17)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
(* the facts the walk adds: s7 is the shadow base, s1 and q are stack addresses, atom 47 is F's shadow address *)
pv_fact HS 23%nat (mkAF SHADOW_OFF SHADOW_OFF 0). { rewrite E23. pv_bv. rewrite Z.pow_0_r, Z.mod_1_r. unfold SHADOW_OFF; lia. }
pv_fact HS 9%nat (mkAF (2 ^ 46) (2 ^ 47) 5). { rewrite E9. pv_bv. change (2 ^ 5) with 32. lia. }
pv_fact HS 20%nat (mkAF (2 ^ 46) (2 ^ 47 - 24) 3). { rewrite E20. pv_bv. change (2 ^ 3) with 8. lia. }
pv_fact HS 47%nat (mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 2).
{ rewrite E47. pv_bv. change (2 ^ 2) with 4.
  assert (HF84 : (F / 8) mod 4 = 0).
  { assert (HFq : F = (F / 32 * 4) * 8) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
    rewrite HFq, Z.div_mul by lia. apply Z_mod_mult. }
  unfold SHADOW_OFF. split; [lia|]. split; [rewrite Zplus_mod, HF84; reflexivity | lia]. }
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_add_alias tfibsegs Ev ssx msx _ _ HS (shadow_decl_ok Ev 10 23 47 F SHADOW_OFF E10 ltac:(lia) E23 E47))
    as HS1 end.
clear HS. rename HS1 into HS.
(* q's two words (only in->p writable) and F's shadow, as regions *)
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
pv_norm HS.
assert (Wq : forall o, 0 <= o < 24 -> writable_at tfibsegs (mrestrict (w_H W) mem2) (q + o)).
{ intros o Ho. apply (apresent_writable tfibsegs). apply (fsw_apresent_unpoison B ly S2 U W mem2 md2 _ HARU); [lia|].
  apply HJpres. lia. }
assert (ROKq : region_ok tfibsegs E (mrestrict (w_H W) mem2) (pv_q_region (SOff 48 0))).
{ unfold region_ok, pv_q_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E20. pv_bv. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wq; lia|].
  constructor; [|constructor; [|constructor]].
  - apply (chunk_ok_val tfibsegs _ _ q 0 8 (SOff 48 0) p); [rewrite fsw_SOff0, E48; reflexivity | cbn; lia | cbn; lia
    | rewrite Z.add_0_r; exact Vq0].
  - apply (chunk_ok_val tfibsegs _ _ q 8 8 (SOff 49 0) endv); [rewrite fsw_SOff0, E49; reflexivity | cbn; lia | cbn; lia
    | exact Vq8]. }
assert (B10 : bv_unsigned (ew E 10) = F) by (rewrite E10; pv_bv; reflexivity).
assert (B20 : bv_unsigned (ew E 20) = q) by (rewrite E20; pv_bv; reflexivity).
assert (B9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; pv_bv; reflexivity).
assert (B8 : bv_unsigned (ew E 8) = s) by (rewrite (EA 8%bv 8%nat s eq_refl R8); pv_bv; reflexivity).
assert (B47 : bv_unsigned (ew E 47) = SHADOW_OFF + F / 8) by (rewrite E47; pv_bv; reflexivity).
pv_addreg HS (pv_q_region (SOff 48 0)) ROKq.
{ rewrite B20, B8, B9, B10. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
pv_norm HS.
(* F's shadow, written by the frame setup: present and not runtime-owned (AR_frames_law), hence writable *)
assert (ROKs : region_ok tfibsegs E (mrestrict (w_H W) mem2) (YP09.mkRegion (Some 47%nat) 0 8 0 8 [])).
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite B47. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable tfibsegs). destruct (HFSp o ltac:(change (64 / 8) with 8; lia)) as (Hp1 & Hno).
  unfold shadow_addr in Hp1, Hno.
  exact (fsw_apresent_notowned B ly S2 U W mem2 md2 (SHADOW_OFF + F / 8 + o) HARU ltac:(unfold SHADOW_OFF; lia) Hno Hp1). }
pv_addreg HS (YP09.mkRegion (Some 47%nat) 0 8 0 8 []) ROKs.
{ rewrite B20, B8, B9, B10, B47. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp. unfold SHADOW_OFF.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
pv_norm HS.
(* 0x83010 .. the shadow load 0x830a4 (q + 8's check): the frame header, F's shadow, s8, the slot *)
fsw_aj_run_toU pv_tbl_ok HS HJ HARU 0x830a4.
{ cbn [ss_mem].
  eapply awr_ok_cons_gen with (k := 47%nat) (b := SHADOW_OFF + F / 8); [reflexivity | exact B47 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. unfold awr_byte, awr_byte0. left; right; right; right.
    exists 0, pos. split; [left; reflexivity|].
    right. unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 0 / 8) with 8. fold F. lia. }
  eapply awr_ok_cons_stack_off with (n := 20%nat) (d := q - ot); [reflexivity | rewrite B20; lia | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 8%nat) (d := s - ot); [reflexivity | rewrite B8; lia | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 9%nat) (d := sp1 - ot); [reflexivity | rewrite B9; lia | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_gen with (k := 10%nat) (b := F); [reflexivity | exact B10 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. unfold awr_byte, awr_byte0. left; right; right; right.
    exists 0, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. fold F. lia. }
  apply awr_ok_nil. }
(* drop F's shadow region (written, never read again: a writable shadow window would fail the token run's static
   check) *)
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  let rs' := eval vm_compute in (tl (ss_mem ssx)) in
  pose proof (st_ok_submem tfibsegs Ev ssx msx rs' HS ltac:(apply YN2j.submemb_sound; vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity)) as HS1 end.
clear HS. rename HS1 into HS. pv_norm HS.
(* the token run's shadow entries: q (24 bytes, the stack: shadow 0) and F's window (app memory, apart from the band) *)
pose proof HJ as (HARj & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJstk & _).
pose proof HJstk as (_ & _ & _ & HJslo & _ & _ & _ & HJtop & HJtop2).
assert (UB : YP0e.U E pv_Bx = SHADOW_OFF) by (unfold pv_Bx; apply (U_atom E 23 SHADOW_OFF E23); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok tfibsegs pv_Bx [mkSHE 20 0 24; mkSHE 10 64 0] E (mrestrict (w_H W) (ms_mem ms))).
{ constructor; [|constructor; [|constructor]].
  - split.
    + cbn [she_m she_lo she_hi]. rewrite (U_atom E 20 q E20 ltac:(lia)), Z.add_0_r.
      eapply (obl_of_range tfibsegs (w_H W) (ms_mem ms) E pv_Bx q 24 q 24); [|exact UB | lia | lia].
      apply (pv_ra_unpoison B ly S2 U W (ms_mem ms) _ q 24 HARU); [lia | lia|].
      apply (pv_stack_ra B ly S2 W _ _ q 24 HARj); [lia | lia | exact Hq8 | reflexivity | lia].
    + intros a Ha. cbn [she_m she_lo she_hi] in Ha. rewrite (U_atom E 20 q E20 ltac:(lia)) in Ha. rewrite UB.
      unfold SHADOW_OFF. lia.
  - split.
    + apply range_addressable_nil. cbn [she_lo she_hi]. lia.
    + intros a Ha. cbn [she_m she_lo she_hi] in Ha. rewrite (U_atom E 10 F E10 ltac:(lia)) in Ha. rewrite UB.
      unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp. unfold SHADOW_OFF. lia. }
(* 0x830a4 .. `bgeu a1, a2` 0x830c8 (in->p against in->end): q's shadow checks, 0x30(s1) := F, in->p / in->end loaded *)
fsw_aj_run_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ cbn [ss_mem].
  eapply awr_ok_cons_stack_off with (n := 20%nat) (d := q - ot); [reflexivity | rewrite B20; lia | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 8%nat) (d := s - ot); [reflexivity | rewrite B8; lia | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 9%nat) (d := sp1 - ot); [reflexivity | rewrite B9; lia | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_gen with (k := 10%nat) (b := F); [reflexivity | exact B10 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. unfold awr_byte, awr_byte0. left; right; right; right.
    exists 0, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. fold F. lia. }
  apply awr_ok_nil. }
eapply SRr_sym_branch with (c := BC_GEU) (a := SOff 48 0) (b := SOff 49 0); [exact HS | |].
{ intros Hb _. exfalso. rewrite branch_geu_U, (U_atom E 48 p E48 ltac:(lia)), (U_atom E 49 endv E49 ltac:(lia)) in Hb.
  apply negb_true_iff, Z.ltb_ge in Hb. lia. }
intros _ HS1. clear HS. rename HS1 into HS.
(* 0x830cc .. the loop head 0x830e0: a3 := 32, a4 := the mask, a0 := in->p *)
fsw_aj_run_to_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan 0x830e0.
{ cbn [ss_mem add_cond].
  eapply awr_ok_cons_stack_off with (n := 20%nat) (d := q - ot); [reflexivity | rewrite B20; lia | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 8%nat) (d := s - ot); [reflexivity | rewrite B8; lia | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 9%nat) (d := sp1 - ot); [reflexivity | rewrite B9; lia | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_gen with (k := 10%nat) (b := F); [reflexivity | exact B10 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. unfold awr_byte, awr_byte0. left; right; right; right.
    exists 0, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. fold F. lia. }
  apply awr_ok_nil. }
(* the loop head: pv_hd under the env of the machine registers at 0x830e0 *)
assert (KEEP : forall x : word, ~ pv_wr F q s sp1 (bv_unsigned x) ->
  mrestrict (w_H W) (ms_mem ms1) x = mrestrict (w_H W) mem2 x).
{ intros x Hx.
  rewrite (pv_frame_P _ _ _ _ (pv_wr F q s sp1) HFr1
    ltac:(pv_wr_tac ltac:(fun H => rewrite ?B20, ?B8, ?B9, ?B10 in H)) x Hx).
  rewrite (pv_frame_P _ _ _ _ (pv_wr F q s sp1) HFr0
    ltac:(pv_wr_tac ltac:(fun H => rewrite ?B20, ?B8, ?B9, ?B10 in H)) x Hx).
  rewrite (pv_frame_P _ _ _ _ (pv_wr F q s sp1) HFr
    ltac:(pv_wr_tac ltac:(fun H => rewrite ?B47, ?B20, ?B8, ?B9, ?B10 in H)) x Hx).
  reflexivity. }
pv_reg HS (w_H W) (10%bv : bv 5) H10. pv_reg HS (w_H W) (11%bv : bv 5) H11. pv_reg HS (w_H W) (12%bv : bv 5) H12. pv_reg HS (w_H W) (13%bv : bv 5) H13.
pv_reg HS (w_H W) (14%bv : bv 5) H14. pv_reg HS (w_H W) (23%bv : bv 5) H23. pv_reg HS (w_H W) (8%bv : bv 5) H8. pv_reg HS (w_H W) (20%bv : bv 5) H20.
pv_reg HS (w_H W) (26%bv : bv 5) H26. pv_reg HS (w_H W) (27%bv : bv 5) H27.
pv_reg HS (w_H W) (9%bv : bv 5) H9. pv_reg HS (w_H W) (18%bv : bv 5) H18. pv_reg HS (w_H W) (19%bv : bv 5) H19.
pv_reg HS (w_H W) (24%bv : bv 5) H24.
pv_reg HS (w_H W) (3%bv : bv 5) HGP. pv_reg HS (w_H W) (4%bv : bv 5) HTP. pv_reg HS (w_H W) (2%bv : bv 5) HSP.
rewrite fsw_SOff0, (EA 2%bv 2%nat sp1 eq_refl R2) in HSP.
assert (EG3 : ew E 3 = YK11.getr regs 3%bv)
  by (unfold E; rewrite (ew_Ereg_nat regs2 _ 3 3%bv eq_refl); exact R3).
assert (EG4 : ew E 4 = YK11.getr regs 4%bv)
  by (unfold E; rewrite (ew_Ereg_nat regs2 _ 4 4%bv eq_refl); exact R4).
rewrite fsw_SOff0, EG3 in HGP. rewrite fsw_SOff0, EG4 in HTP.
rewrite fsw_SOff0, E9 in H9. rewrite fsw_SOff0, E10 in H18.
rewrite fsw_SOff0, (EA 19%bv 19%nat v eq_refl R19) in H19. rewrite fsw_SOff0, E47 in H24.
rewrite fsw_SOff0, E48 in H10, H11. rewrite fsw_SOff0, E49 in H12. rewrite fsw_SOff0, E23 in H23.
rewrite fsw_SOff0, (EA 8%bv 8%nat s eq_refl R8) in H8. rewrite fsw_SOff0, E20 in H20. rewrite fsw_SOff0, E10 in H26.
rewrite (pv_shadow_denot E 20 23 q SHADOW_OFF E20 ltac:(lia) E23 ltac:(unfold SHADOW_OFF; lia)
  ltac:(unfold SHADOW_OFF; pose proof (Z.div_le_mono q (2 ^ 47) 8 ltac:(lia) ltac:(lia)); lia)) in H27.
clear H13 H14.
pose proof (fsw_reg_lit _ E _ ms1 13%bv 32 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as H13.
pose proof (fsw_reg_lit _ E _ ms1 14%bv pv_mask HS ltac:(vm_compute; reflexivity) ltac:(unfold pv_mask; lia)) as H14.
(* the memory facts at ms1, read off the state's regions *)
pv_region HS 0%nat RQ.
pv_region HS 1%nat RS0.
pv_region HS 3%nat RFR.
cbn [ms_mem restrict] in RQ, RS0, RFR.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms1 HS eq_refl) as Hshape.
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 ?pc) _ _ =>
  let pc' := eval vm_compute in pc in change pc with pc' in Hshape end.
assert (B46 : bv_unsigned (ew E 46) = FL).
{ subst E. change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra. cbn [nth pv_extra0 app].
  destruct (al_flag _ _ LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin0) as (_ & _ & Hfa & Hfc).
  unfold in_app in Hfa. apply wz. fold FL in Hfa, Hfc. lia. }
destruct (al_flag _ _ LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin0) as (_ & _ & HFLa & HFLc). fold FL in HFLa, HFLc.
assert (HH : st_ok tfibsegs (Ereg (ms_regs ms1) (pv_extra0 regs FL ++ pv_xs (SHADOW_OFF + F / 8) p endv c0)) pv_hd
  (restrict (w_H W) (mkst (ms_regs ms1) (Z_to_bv 64 0x830e0) (ms_mem ms1) (seg_rom tfibsegs)))).
{ apply (pv_hd_ok (w_H W) (ms_regs ms1) (ms_mem ms1) regs F FL (SHADOW_OFF + F / 8) p endv c0 s q H10 H11 H12 H13 H14
    H23 H8 H20 H26 H27); try lia.
  - unfold in_app in HFLa. lia.
  - unfold SHADOW_OFF. lia.
  - pose proof (fsw_field _ _ 20 q _ 0 24 0 8 0 8 (SOff 48 0) p RQ B20 ltac:(left; reflexivity)
      ltac:(rewrite fsw_SOff0, E48; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V. rewrite Z.add_0_r in V. exact V.
  - exact (fsw_field _ _ 20 q _ 0 24 0 8 8 8 (SOff 49 0) endv RQ B20 ltac:(right; left; reflexivity)
      ltac:(rewrite fsw_SOff0, E49; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
  - intros o Ho. destruct RQ as (_ & _ & Hw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
    rewrite B20 in Hw. apply Hw. lia.
  - apply (pv_val_keep (mrestrict (w_H W) mem2) _ (pv_wr F q s sp1) p 1 c0 KEEP); [lia | cbn; lia | | exact Vc0].
    intros k Hk. cbn in Hk. unfold pv_wr. unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp. unfold SHADOW_OFF in *. lia.
  - exact (pv_saved_of_region regs2 regs FL _ _ s _ _ _ _ RS0 B8).
  - exact (fsw_field _ _ 10 F _ 0 64 0 64 56 8 (SOff 46 0) FL RFR B10 ltac:(right; right; right; left; reflexivity)
      ltac:(rewrite fsw_SOff0, <- B46; symmetry; apply Z_to_bv_bv_unsigned) ltac:(cbn; unfold in_app in HFLa; lia) ltac:(cbn; lia)). }
rewrite <- Hshape in HH.
apply (K ms1 mat1); [exact HH | exact HJ | exact HARU | exact KEEP | exact H8 | exact H9 | exact H18 | exact H19
  | exact H20 | exact H23 | exact H24 | exact H26 | exact HGP | exact HTP | exact HSP].
Qed.
End S1.
(* ---- the white-space loop (pf.c skip_ws, inlined at 0x830e0-0x8311c) ---- *)
(* the text bytes the loop reads, at cur and after it *)
Definition pv_text (m : word -> option byte) (cur : Z) (bs : list Z) : Prop :=
  forall j, (j < length bs)%nat -> 0 <= nth j bs 0 <= 255 /\ val_mem tfibsegs m (cur + Z.of_nat j) 1 (nth j bs 0).
(* what the loop keeps: the saved words at s0, the frame's flag word, in->end, the text *)
Definition pv_inv (m : word -> option byte) (regs0 : bvmap 5 word) (s F FL q endv cur : Z) (bs : list Z) : Prop :=
  pv_saved_ok m s regs0 /\ val_mem tfibsegs m (F + 56) 8 FL /\ val_mem tfibsegs m (q + 8) 8 endv /\
  (forall o, 0 <= o < 8 -> writable_at tfibsegs m (q + o)) /\ pv_text m cur bs.

Section L. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* a shadow fact above the stack survives a change that keeps every byte outside [q, q + 8) of the restricted memory
   (q is a stack address, its shadow band is disjoint from it) *)
Lemma pv_ra_keep : forall (H : word -> bool) (m m' : word -> option byte) q lo n,
  (forall x : word, ~ (q <= bv_unsigned x < q + 8) -> mrestrict H m' x = mrestrict H m x) -> alloc_ceiling <= q ->
  0 <= lo -> lo + n <= 2 ^ 47 ->
  range_addressable (aview tfibsegs H m) SHADOW_OFF lo n -> range_addressable (aview tfibsegs H m') SHADOW_OFF lo n.
Proof.
intros H m m' q lo n HK Hq Hlo Hn HRA y Hy. destruct (HRA y Hy) as (sv & Es & Hok). exists sv. split; [|exact Hok].
rewrite <- Es. unfold shadow_of_addr, aview. pose proof asan_consts as (C1 & _).
pose proof (Z.div_le_mono y (2 ^ 47) 8 ltac:(lia) ltac:(lia)). assert (0 <= y / 8) by (apply Z.div_pos; lia).
rewrite (pv_mbyte_keep (mrestrict H m) (mrestrict H m') (fun a => q <= a < q + 8) _ HK); [reflexivity | | ];
  unfold SHADOW_OFF; lia.
Qed.

(* the four white-space bytes of the mask 0x100002600 (pf.c skip_ws: space, tab, LF, CR) *)
Definition pv_wsb (c : Z) : Prop := c = 9 \/ c = 10 \/ c = 13 \/ c = 32.
Lemma pv_wsb_mask : forall c, pv_wsb c -> Z.land (Z.shiftr pv_mask c) 1 <> 0.
Proof. intros c H. destruct H as [H|[H|[H|H]]]; subst c; vm_compute; discriminate. Qed.
Lemma pv_wsb_le : forall c, pv_wsb c -> c <= 32.
Proof. intros c H. destruct H as [H|[H|[H|H]]]; subst c; lia. Qed.
End L.

Section LD. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* the loop-head package: the symbolic state, in->p and the kept data, at cursor cur with the bytes bs from cur on *)
Definition pv_at (W : world tfibsegs) (regs0 : bvmap 5 word) (F FL q s sp1 v endv : Z) (ms : machine_state) (cur : Z)
  (bs : list Z) : Prop :=
  st_ok tfibsegs (Ereg (ms_regs ms) (pv_extra0 regs0 FL ++ pv_xs (SHADOW_OFF + F / 8) cur endv (nth 0 bs 0))) pv_hd
    (restrict (w_H W) ms) /\
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) q 8 cur /\
  pv_inv (mrestrict (w_H W) (ms_mem ms)) regs0 s F FL q endv cur bs /\
  (* the registers pv_hd leaves as their own atoms, whose values the head and the arms after it need: s0 = s,
     s1 = sp1, s2 = s10 = F, s3 = v, s4 = q, s7 = the shadow base, s8 = F's shadow address *)
  YK11.getr (ms_regs ms) 8%bv = Z_to_bv 64 s /\ YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 sp1 /\
  YK11.getr (ms_regs ms) 18%bv = Z_to_bv 64 F /\ YK11.getr (ms_regs ms) 19%bv = Z_to_bv 64 v /\
  YK11.getr (ms_regs ms) 20%bv = Z_to_bv 64 q /\ YK11.getr (ms_regs ms) 23%bv = Z_to_bv 64 SHADOW_OFF /\
  YK11.getr (ms_regs ms) 24%bv = Z_to_bv 64 (SHADOW_OFF + F / 8) /\ YK11.getr (ms_regs ms) 26%bv = Z_to_bv 64 F /\
  (* gp and tp, which the epilogue's fsw_retU needs at their entry values (they are no atom of pv_extra0) *)
  YK11.getr (ms_regs ms) 3%bv = YK11.getr regs0 3%bv /\ YK11.getr (ms_regs ms) 4%bv = YK11.getr regs0 4%bv /\
  (* sp, which the arms' call steps need at the re-aligned sp1 *)
  YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 sp1.

End LD.


(* ---- the white-space loop, proved: pv_step is one iteration (0x830e0 -> 0x830e0), pv_loop the induction on the run ws
   still to skip. MEASURED (vm_compute over pv_tbl from pv_hd, probes p1-p3 of this lane): each iteration stops at three
   branches, each decided semantically, none of them an __asan_report_* exit -
     0x830f4 `bltu a3, a5` (32 < byte)    NOT taken, by pv_wsb_le;
     0x83100 `beqz a5`    ((mask >> byte) & 1 = 0) NOT taken, by pv_wsbit_U;
     0x83118 `bne a1, a2` (in->p + 1 <> in->end)   TAKEN, by cur + |ws| + 1 <= endv;
   the byte's shadow load 0x830e8 is a token covered by pv_SH's shent at the cursor atom 48 (two token atoms 51, 52; no
   obligation), and the only write of the body is in->p, [q, q + 8) (the state after the back edge carries q's chunk at
   SOff 48 1). The head is re-established at cur + 1 from machine facts through pv_hd_ok. ---- *)
Section LH. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma pv_U_off : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 2 ^ 64 -> U E (SOff n x) = v + x.
Proof. intros E n v x Hn Hv Hx. rewrite U_SOff, Hn, (unsigned_lit_small v Hv). apply zcanon_id. unfold M64. lia. Qed.
Lemma pv_denot_off : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 2 ^ 64 ->
  sv_denot E (SOff n x) = Z_to_bv 64 (v + x).
Proof. intros E n v x Hn Hv Hx. rewrite denot_lit_U. f_equal. apply pv_U_off; assumption. Qed.
Lemma pv_denot_lit : forall E z, 0 <= z < 2 ^ 64 -> sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. intros E z Hz. rewrite denot_lit_U, U_lit by lia. reflexivity. Qed.
(* the mask bit of a white-space byte (pv_mask = 4294977024, the literal the engine carries) *)
Lemma pv_wsbit_U : forall E c, ew E 50 = Z_to_bv 64 c -> pv_wsb c ->
  U E (SAlu ALU_AND (SAlu ALU_SRL (SLit 4294977024) (SOff 50 0)) (SLit 1)) = 1.
Proof.
intros E c H50 Hc. pose proof (pv_wsb_le c Hc) as Hle.
assert (H0 : 0 <= c) by (destruct Hc as [Hc|[Hc|[Hc|Hc]]]; subst c; lia).
rewrite !U_SAlu, !U_SLit, (U_atom E 50 c H50 ltac:(lia)).
destruct Hc as [Hc|[Hc|[Hc|Hc]]]; subst c; vm_compute; reflexivity.
Qed.
Lemma pv_saved_keep : forall (m m' : word -> option byte) (P : Z -> Prop) s regs0,
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) -> 104 <= s <= 2 ^ 64 ->
  (forall a, s - 104 <= a < s -> ~ P a) -> pv_saved_ok m s regs0 -> pv_saved_ok m' s regs0.
Proof.
intros m m' P s regs0 HK Hs HP Hv j Hj.
apply (pv_val_keep m m' P (s - 8 * (Z.of_nat j + 1)) 8 _ HK); [lia | cbn; lia | | exact (Hv j Hj)].
intros k Hk. apply HP. cbn in Hk. lia.
Qed.
Lemma pv_text_keep : forall (m m' : word -> option byte) (P : Z -> Prop) cur bs,
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) -> 0 <= cur -> cur + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall a, cur <= a < cur + Z.of_nat (length bs) -> ~ P a) -> pv_text m cur bs -> pv_text m' cur bs.
Proof.
intros m m' P cur bs HK H0 H1 HP Ht j Hj. destruct (Ht j Hj) as [Hr Hv]. split; [exact Hr|].
apply (pv_val_keep m m' P (cur + Z.of_nat j) 1 _ HK); [lia | cbn; lia | | exact Hv].
intros k Hk. apply HP. cbn in Hk. lia.
Qed.
Lemma pv_text_tl : forall (m : word -> option byte) cur b bs, pv_text m cur (b :: bs) -> pv_text m (cur + 1) bs.
Proof.
intros m cur b bs H j Hj. destruct (H (S j) ltac:(cbn; lia)) as [Hr Hv]. cbn [nth] in Hr, Hv.
replace (cur + 1 + Z.of_nat j) with (cur + Z.of_nat (S j)) by lia. split; [exact Hr | exact Hv].
Qed.
End LH.

Ltac pv_ewo := repeat rewrite ew_ewset_other by lia.
Ltac pv_ewo_in H := repeat rewrite ew_ewset_other in H by lia.
(* the write windows of a loop state: q's chunk [0, 8) is the only writable one *)
Ltac pv_awr_hd q ot B20 :=
  cbn [ss_mem add_cond];
  eapply awr_ok_cons_stack_off with (n := 20%nat) (d := q - ot);
    [reflexivity | pv_ewo; rewrite B20; lia | cbn; lia | cbn; lia |];
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac pv_wr_q B20 :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; cbv beta;
  try (unfold pv_hd, pv_hd_regions, pv_q_region, pv_txt_region, pv_s0_region, pv_flag_region in Ha);
  cbn [ss_mem add_cond] in Ha;
  repeat (apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    pv_ewo_in Ha; rewrite ?B20 in Ha; lia|]);
  exfalso; exact (pv_wrange_nil _ _ Ha).

Section ST. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* one iteration: the byte b at cur is white space, the next byte b' exists (cur + 1 < in->end) *)
Lemma pv_step : forall STK ot FP ly S S2 U (W : world tfibsegs) mem md regs0 pos q s sp1 v endv cur b b' bs ms mdx
  (Q : world tfibsegs -> config -> Prop),
  In (0, pos) (frames S2) ->
  2 ^ 46 <= q <= 2 ^ 47 - 24 -> q mod 8 = 0 -> 2 ^ 46 <= s <= 2 ^ 47 -> s mod 16 = 0 ->
  s <= q -> alloc_ceiling + 104 <= s -> ly_stk_lo ly <= q -> q + 24 <= ly_stk_hi ly -> alloc_ceiling <= q ->
  ot - STK <= q -> q + 8 <= ot ->
  4096 <= cur -> cur + Z.of_nat (length (b :: b' :: bs)) <= endv -> endv <= 2 ^ 47 - 8 ->
  (endv <= q \/ q + 24 <= cur) -> (endv <= s - 104 \/ s <= cur) ->
  (endv <= frame_addr ly 0 pos \/ frame_addr ly 0 pos + 64 <= cur) ->
  (endv <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= cur) ->
  pv_wsb b ->
  range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF cur 1 ->
  pv_at W regs0 (frame_addr ly 0 pos) (flag_addr ly 0 pos) q s sp1 v endv ms cur (b :: b' :: bs) ->
  ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U (ms_mem ms)) mdx 0 ->
  ARU tfibsegs B ly S2 U W (ms_mem ms) mdx ->
  (forall ms' mdx',
     pv_at W regs0 (frame_addr ly 0 pos) (flag_addr ly 0 pos) q s sp1 v endv ms' (cur + 1) (b' :: bs) ->
     ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U (ms_mem ms')) mdx' 0 ->
     ARU tfibsegs B ly S2 U W (ms_mem ms') mdx' ->
     (forall x : word, ~ (q <= bv_unsigned x < q + 8) ->
        mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) (ms_mem ms) x) ->
     SRr tfibsegs W (mkCfg ms' mdx') Q) ->
  SRr tfibsegs W (mkCfg ms mdx) Q.
Proof.
intros STK ot FP ly S S2 U W mem md regs0 pos q s sp1 v endv cur b b' bs ms mdx Q Hin0 Hq Hq8 Hs Hs16 Hsq Hsc Hlo Hhi
  Hceil Hwlo Hwhi Hcur Hend Hend47 Hcq Hcs HcF Hcsh Hwsb HRA
  (HS & Vq0 & HINV & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & RG3 & RG4 & RSP) HJ HARU K.
cbn [length] in Hend.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B ly S2 U W (ms_mem ms) mdx HARU) as HAR.
destruct (al_frames _ _ LAWS ly S2 W (unpoison U (ms_mem ms)) mdx 0 pos HAR Hin0) as (HF32 & HFapp & _ & _).
destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U (ms_mem ms)) mdx 0 pos HAR Hin0) as (HF4096 & HFc & _).
destruct (al_flag _ _ LAWS ly S2 W (unpoison U (ms_mem ms)) mdx 0 pos HAR Hin0) as (_ & _ & HFLa & HFLc).
change (fs_frame_bytes 0) with 64 in *.
set (F := frame_addr ly 0 pos) in *. set (FL := flag_addr ly 0 pos) in *.
set (E := Ereg (ms_regs ms) (pv_extra0 regs0 FL ++ pv_xs (SHADOW_OFF + F / 8) cur endv (nth 0 (b :: b' :: bs) 0))) in HS.
cbn [nth] in E.
destruct HINV as (Vsv & Vfl & Vq8 & Wq & Htx).
destruct (Htx 0%nat ltac:(cbn; lia)) as [Hb0 _]. destruct (Htx 1%nat ltac:(cbn; lia)) as [Hb1 Vb1]. cbn [nth] in Hb0, Hb1, Vb1.
assert (EA : forall (r : bv 5) n z, Z.of_nat n = bv_unsigned r -> getr (ms_regs ms) r = Z_to_bv 64 z -> ew E n = Z_to_bv 64 z)
  by (intros r n z Hn Hr; subst E; rewrite (ew_Ereg_nat _ _ n r Hn), Hr; reflexivity).
assert (E8 : ew E 8 = Z_to_bv 64 s) by (apply (EA 8%bv); [reflexivity | exact R8]).
assert (E20 : ew E 20 = Z_to_bv 64 q) by (apply (EA 20%bv); [reflexivity | exact R20]).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (apply (EA 23%bv); [reflexivity | exact R23]).
assert (E26 : ew E 26 = Z_to_bv 64 F) by (apply (EA 26%bv); [reflexivity | exact R26]).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (apply (EA 9%bv); [reflexivity | exact R9]).
assert (E18 : ew E 18 = Z_to_bv 64 F) by (apply (EA 18%bv); [reflexivity | exact R18]).
assert (E19 : ew E 19 = Z_to_bv 64 v) by (apply (EA 19%bv); [reflexivity | exact R19]).
assert (E24 : ew E 24 = Z_to_bv 64 (SHADOW_OFF + F / 8)) by (apply (EA 24%bv); [reflexivity | exact R24]).
assert (E48 : ew E 48 = Z_to_bv 64 cur) by (subst E; change 48%nat with (32 + 16)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E49 : ew E 49 = Z_to_bv 64 endv) by (subst E; change 49%nat with (32 + 17)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E50 : ew E 50 = Z_to_bv 64 b) by (subst E; change 50%nat with (32 + 18)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (B20 : bv_unsigned (ew E 20) = q) by (rewrite E20; apply unsigned_lit_small; lia).
assert (UB : YP0e.U E pv_Bx = SHADOW_OFF) by (unfold pv_Bx; apply (U_atom E 23 SHADOW_OFF E23); unfold SHADOW_OFF; lia).
(* the token run's shadow entries: q (stack, shadow 0), F's window (apart from the band), the byte at cur *)
assert (SHOK : sh_ok tfibsegs pv_Bx pv_SH E (mrestrict (w_H W) (ms_mem ms))).
{ constructor; [|constructor; [|constructor; [|constructor]]].
  - split.
    + cbn [she_m she_lo she_hi]. rewrite (U_atom E 20 q E20 ltac:(lia)), Z.add_0_r.
      eapply (obl_of_range tfibsegs (w_H W) (ms_mem ms) E pv_Bx q 24 q 24); [|exact UB | lia | lia].
      apply (pv_ra_unpoison B ly S2 U W (ms_mem ms) _ q 24 HARU); [lia | lia|].
      apply (pv_stack_ra B ly S2 W _ _ q 24 HAR); [lia | lia | exact Hq8 | reflexivity | lia].
    + intros a Ha. cbn [she_m she_lo she_hi] in Ha. rewrite (U_atom E 20 q E20 ltac:(lia)) in Ha. rewrite UB.
      unfold SHADOW_OFF. lia.
  - split.
    + apply range_addressable_nil. cbn [she_lo she_hi]. lia.
    + intros a Ha. cbn [she_m she_lo she_hi] in Ha. rewrite (U_atom E 26 F E26 ltac:(lia)) in Ha. rewrite UB.
      unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp. unfold SHADOW_OFF. lia.
  - split.
    + cbn [she_m she_lo she_hi]. rewrite (U_atom E 48 cur E48 ltac:(lia)), Z.add_0_r.
      exact (obl_of_range tfibsegs (w_H W) (ms_mem ms) E pv_Bx cur 1 cur 1 HRA UB ltac:(lia) ltac:(lia)).
    + intros a Ha. cbn [she_m she_lo she_hi] in Ha. rewrite (U_atom E 48 cur E48 ltac:(lia)) in Ha. rewrite UB.
      unfold SHADOW_OFF in *. lia. }
(* 0x830e0 .. `bltu a3, a5` 0x830f4: the byte's shadow check (covered), the byte loaded *)
fsw_aj_run_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ unfold pv_hd, pv_hd_regions, pv_q_region, pv_txt_region, pv_s0_region, pv_flag_region. pv_awr_hd q ot B20. }
(* `bltu a3, a5`: 32 < byte is false for a white-space byte *)
eapply SRr_sym_branch with (c := BC_LTU) (a := SLit 32) (b := SOff 50 0); [exact HS | |].
{ intros Hb _. exfalso. rewrite branch_ltu_U, U_lit, (pv_U_off _ 50 b 0) in Hb by first [pv_ewo; exact E50 | lia].
  apply Z.ltb_lt in Hb. pose proof (pv_wsb_le b Hwsb). lia. }
intros _ HS1. clear HS. rename HS1 into HS.
(* .. `beqz a5` 0x83100 (the mask bit) *)
fsw_aj_run_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ pv_awr_hd q ot B20. }
eapply SRr_sym_branch with (c := BC_EQ) (a := SAlu ALU_AND (SAlu ALU_SRL (SLit 4294977024) (SOff 50 0)) (SLit 1))
  (b := SLit 0); [exact HS | |].
{ intros Hb _. exfalso. rewrite branch_eq_U, U_lit, (pv_wsbit_U _ b) in Hb by first [pv_ewo; exact E50 | exact Hwsb | lia].
  discriminate Hb. }
intros _ HS1. clear HS. rename HS1 into HS.
(* .. `bne a1, a2` 0x83118: q's shadow check (covered), in->p := cur + 1 *)
fsw_aj_run_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ pv_awr_hd q ot B20. }
eapply SRr_sym_branch with (c := BC_NE) (a := SOff 48 1) (b := SOff 49 0); [exact HS | |].
2: { intros Hb _. exfalso. rewrite branch_ne_U, (pv_U_off _ 48 cur 1), (pv_U_off _ 49 endv 0) in Hb
       by first [pv_ewo; first [exact E48 | exact E49] | lia].
     apply negb_false_iff, Z.eqb_eq in Hb. lia. }
intros _ HS1. clear HS. rename HS1 into HS.
(* the back edge to 0x830e0 *)
fsw_aj_run_to_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan 0x830e0.
{ pv_awr_hd q ot B20. }
(* the memory: only in->p [q, q + 8) was written by the four runs *)
assert (KEEP : forall x : word, ~ (q <= bv_unsigned x < q + 8) ->
  mrestrict (w_H W) (ms_mem ms3) x = mrestrict (w_H W) (ms_mem ms) x).
{ intros x Hx.
  rewrite (pv_frame_P _ _ _ _ (fun a => q <= a < q + 8) HFr2 ltac:(pv_wr_q B20) x Hx).
  rewrite (pv_frame_P _ _ _ _ (fun a => q <= a < q + 8) HFr1 ltac:(pv_wr_q B20) x Hx).
  rewrite (pv_frame_P _ _ _ _ (fun a => q <= a < q + 8) HFr0 ltac:(pv_wr_q B20) x Hx).
  rewrite (pv_frame_P _ _ _ _ (fun a => q <= a < q + 8) HFr ltac:(pv_wr_q B20) x Hx).
  reflexivity. }
(* the registers at 0x830e0 *)
pv_reg HS (w_H W) (10%bv : bv 5) H10. pv_reg HS (w_H W) (11%bv : bv 5) H11. pv_reg HS (w_H W) (12%bv : bv 5) H12.
pv_reg HS (w_H W) (8%bv : bv 5) H8. pv_reg HS (w_H W) (20%bv : bv 5) H20. pv_reg HS (w_H W) (23%bv : bv 5) H23.
pv_reg HS (w_H W) (26%bv : bv 5) H26. pv_reg HS (w_H W) (27%bv : bv 5) H27.
pv_reg HS (w_H W) (9%bv : bv 5) H9. pv_reg HS (w_H W) (18%bv : bv 5) H18. pv_reg HS (w_H W) (19%bv : bv 5) H19.
pv_reg HS (w_H W) (24%bv : bv 5) H24.
pv_reg HS (w_H W) (3%bv : bv 5) HGP. pv_reg HS (w_H W) (4%bv : bv 5) HTP. pv_reg HS (w_H W) (2%bv : bv 5) HSP.
lazymatch type of HS with st_ok _ ?Ey _ _ => set (E3 := Ey) in * end.
assert (F8 : ew E3 8 = Z_to_bv 64 s) by (subst E3; pv_ewo; exact E8).
assert (F20 : ew E3 20 = Z_to_bv 64 q) by (subst E3; pv_ewo; exact E20).
assert (F23 : ew E3 23 = Z_to_bv 64 SHADOW_OFF) by (subst E3; pv_ewo; exact E23).
assert (F26 : ew E3 26 = Z_to_bv 64 F) by (subst E3; pv_ewo; exact E26).
assert (F9 : ew E3 9 = Z_to_bv 64 sp1) by (subst E3; pv_ewo; exact E9).
assert (F18 : ew E3 18 = Z_to_bv 64 F) by (subst E3; pv_ewo; exact E18).
assert (F19 : ew E3 19 = Z_to_bv 64 v) by (subst E3; pv_ewo; exact E19).
assert (F24 : ew E3 24 = Z_to_bv 64 (SHADOW_OFF + F / 8)) by (subst E3; pv_ewo; exact E24).
rewrite fsw_SOff0, F9 in H9. rewrite fsw_SOff0, F18 in H18. rewrite fsw_SOff0, F19 in H19.
rewrite fsw_SOff0, F24 in H24.
assert (EG3 : ew E 3 = YK11.getr regs0 3%bv)
  by (subst E; rewrite (ew_Ereg_nat (ms_regs ms) _ 3 3%bv eq_refl); exact RG3).
assert (EG4 : ew E 4 = YK11.getr regs0 4%bv)
  by (subst E; rewrite (ew_Ereg_nat (ms_regs ms) _ 4 4%bv eq_refl); exact RG4).
assert (FG3 : ew E3 3 = YK11.getr regs0 3%bv) by (subst E3; pv_ewo; exact EG3).
assert (FG4 : ew E3 4 = YK11.getr regs0 4%bv) by (subst E3; pv_ewo; exact EG4).
rewrite fsw_SOff0, FG3 in HGP. rewrite fsw_SOff0, FG4 in HTP.
assert (EG2 : ew E 2 = Z_to_bv 64 sp1)
  by (subst E; rewrite (ew_Ereg_nat (ms_regs ms) _ 2 2%bv eq_refl); exact RSP).
assert (FG2 : ew E3 2 = Z_to_bv 64 sp1) by (subst E3; pv_ewo; exact EG2).
rewrite fsw_SOff0, FG2 in HSP.
assert (F48 : ew E3 48 = Z_to_bv 64 cur) by (subst E3; pv_ewo; exact E48).
assert (F49 : ew E3 49 = Z_to_bv 64 endv) by (subst E3; pv_ewo; exact E49).
assert (G20 : bv_unsigned (ew E3 20) = q) by (rewrite F20; apply unsigned_lit_small; lia).
rewrite (pv_denot_off E3 48 cur 1 F48 ltac:(lia) ltac:(lia)) in H10, H11.
rewrite (pv_denot_off E3 49 endv 0 F49 ltac:(lia) ltac:(lia)), Z.add_0_r in H12.
rewrite fsw_SOff0, F8 in H8. rewrite fsw_SOff0, F20 in H20. rewrite fsw_SOff0, F23 in H23. rewrite fsw_SOff0, F26 in H26.
rewrite (pv_shadow_denot E3 20 23 q SHADOW_OFF F20 ltac:(lia) F23 ltac:(unfold SHADOW_OFF; lia)
  ltac:(unfold SHADOW_OFF; pose proof (Z.div_le_mono q (2 ^ 47) 8 ltac:(lia) ltac:(lia)); lia)) in H27.
pose proof (fsw_reg_lit _ E3 _ ms3 13%bv 32 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as H13.
pose proof (fsw_reg_lit _ E3 _ ms3 14%bv pv_mask HS ltac:(vm_compute; reflexivity) ltac:(unfold pv_mask; lia)) as H14.
(* the memory at 0x830e0 *)
pv_region HS 0%nat RQ. cbn [ms_mem restrict] in RQ.
assert (Vq0' : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms3)) q 8 (cur + 1)).
{ pose proof (fsw_field _ _ 20 q _ 0 24 0 8 0 8 (SOff 48 1) (cur + 1) RQ G20 ltac:(left; reflexivity)
    (pv_denot_off E3 48 cur 1 F48 ltac:(lia) ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  rewrite Z.add_0_r in V. exact V. }
assert (Wq' : forall o, 0 <= o < 8 -> writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms3)) (q + o)).
{ intros o Ho. destruct RQ as (_ & _ & Hw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
  rewrite G20 in Hw. apply Hw. lia. }
set (P := fun a => q <= a < q + 8).
assert (Vq8' : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms3)) (q + 8) 8 endv).
{ apply (pv_val_keep _ _ P (q + 8) 8 endv KEEP); [lia | cbn; lia | | exact Vq8]. intros k Hk. unfold P. cbn in Hk. lia. }
assert (Vfl' : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms3)) (F + 56) 8 FL).
{ apply (pv_val_keep _ _ P (F + 56) 8 FL KEEP); [lia | cbn; lia | | exact Vfl]. intros k Hk. unfold P. cbn in Hk. lia. }
assert (Vsv' : pv_saved_ok (mrestrict (w_H W) (ms_mem ms3)) s regs0).
{ apply (pv_saved_keep _ _ P s regs0 KEEP); [lia | | exact Vsv]. intros a Ha. unfold P. lia. }
assert (Htx' : pv_text (mrestrict (w_H W) (ms_mem ms3)) (cur + 1) (b' :: bs)).
{ apply (pv_text_tl _ cur b). apply (pv_text_keep _ _ P cur (b :: b' :: bs) KEEP); [lia | cbn [length]; lia | | exact Htx].
  intros a Ha. unfold P. cbn [length] in Ha. lia. }
destruct (Htx' 0%nat ltac:(cbn; lia)) as [_ Vb1']. cbn [nth] in Vb1'. rewrite Z.add_0_r in Vb1'.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms3 HS eq_refl) as Hshape.
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 ?pc) _ _ =>
  let pc' := eval vm_compute in pc in change pc with pc' in Hshape end.
assert (HH : st_ok tfibsegs (Ereg (ms_regs ms3) (pv_extra0 regs0 FL ++ pv_xs (SHADOW_OFF + F / 8) (cur + 1) endv b')) pv_hd
  (restrict (w_H W) (mkst (ms_regs ms3) (Z_to_bv 64 0x830e0) (ms_mem ms3) (seg_rom tfibsegs)))).
{ apply (pv_hd_ok (w_H W) (ms_regs ms3) (ms_mem ms3) regs0 F FL (SHADOW_OFF + F / 8) (cur + 1) endv b' s q H10 H11 H12
    H13 H14 H23 H8 H20 H26 H27); try lia; try assumption.
  - unfold in_app in HFLa. lia.
  - unfold SHADOW_OFF. lia. }
rewrite <- Hshape in HH.
apply (K ms3 _); [| exact HJ | exact HARU | exact KEEP].
split; [exact HH|]. split; [exact Vq0'|]. split; [split; [exact Vsv'|]; split; [exact Vfl'|]; split; [exact Vq8'|];
  split; [exact Wq' | exact Htx']|].
split; [exact H8|]. split; [exact H9|]. split; [exact H18|]. split; [exact H19|]. split; [exact H20|].
split; [exact H23|]. split; [exact H24|]. split; [exact H26|]. split; [exact HGP|]. split; [exact HTP | exact HSP].
Qed.

(* the loop as one induction on the white-space run ws before the byte b0 that ends it *)
Lemma pv_loop : forall ws STK ot FP ly S S2 U (W : world tfibsegs) mem md regs0 pos q s sp1 v endv cur b0 ms mdx
  (Q : world tfibsegs -> config -> Prop),
  In (0, pos) (frames S2) ->
  2 ^ 46 <= q <= 2 ^ 47 - 24 -> q mod 8 = 0 -> 2 ^ 46 <= s <= 2 ^ 47 -> s mod 16 = 0 ->
  s <= q -> alloc_ceiling + 104 <= s -> ly_stk_lo ly <= q -> q + 24 <= ly_stk_hi ly -> alloc_ceiling <= q ->
  ot - STK <= q -> q + 8 <= ot ->
  4096 <= cur -> cur + Z.of_nat (length ws) + 1 <= endv -> endv <= 2 ^ 47 - 8 ->
  (endv <= q \/ q + 24 <= cur) -> (endv <= s - 104 \/ s <= cur) ->
  (endv <= frame_addr ly 0 pos \/ frame_addr ly 0 pos + 64 <= cur) ->
  (endv <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= cur) ->
  Forall pv_wsb ws ->
  range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF cur (Z.of_nat (length ws) + 1) ->
  pv_at W regs0 (frame_addr ly 0 pos) (flag_addr ly 0 pos) q s sp1 v endv ms cur (ws ++ [b0]) ->
  ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U (ms_mem ms)) mdx 0 ->
  ARU tfibsegs B ly S2 U W (ms_mem ms) mdx ->
  (forall ms' mdx',
     pv_at W regs0 (frame_addr ly 0 pos) (flag_addr ly 0 pos) q s sp1 v endv ms' (cur + Z.of_nat (length ws)) [b0] ->
     ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U (ms_mem ms')) mdx' 0 ->
     ARU tfibsegs B ly S2 U W (ms_mem ms') mdx' ->
     range_addressable (aview tfibsegs (w_H W) (ms_mem ms')) SHADOW_OFF (cur + Z.of_nat (length ws)) 1 ->
     (forall x : word, ~ (q <= bv_unsigned x < q + 8) ->
        mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) (ms_mem ms) x) ->
     SRr tfibsegs W (mkCfg ms' mdx') Q) ->
  SRr tfibsegs W (mkCfg ms mdx) Q.
Proof.
induction ws as [|w ws IH];
  intros STK ot FP ly S S2 U W mem md regs0 pos q s sp1 v endv cur b0 ms mdx Q Hin0 Hq Hq8 Hs Hs16 Hsq Hsc Hlo Hhi Hceil
    Hwlo Hwhi Hcur Hend Hend47 Hcq Hcs HcF Hcsh Hws HRA HAT HJ HARU K.
- cbn [length app] in *. rewrite Z.add_0_r in *. apply (K ms mdx HAT HJ HARU HRA). intros x _. reflexivity.
- cbn [length app] in Hend, HRA, HAT |- *. apply Forall_cons_iff in Hws. destruct Hws as [Hw Hws].
  destruct (ws ++ [b0]) as [|b' bs] eqn:Eq; [destruct ws; discriminate Eq|].
  apply (pv_step STK ot FP ly S S2 U W mem md regs0 pos q s sp1 v endv cur w b' bs ms mdx Q Hin0 Hq Hq8 Hs Hs16 Hsq Hsc
    Hlo Hhi Hceil Hwlo Hwhi Hcur); try assumption.
  + rewrite <- Eq. cbn [length]. rewrite length_app. cbn [length]. lia.
  + eapply range_addressable_sub; [exact HRA | lia | lia].
  + intros ms1 mdx1 HAT1 HJ1 HARU1 KEEP1. rewrite <- Eq in HAT1.
    apply (IH STK ot FP ly S S2 U W mem md regs0 pos q s sp1 v endv (cur + 1) b0 ms1 mdx1 Q Hin0 Hq Hq8 Hs Hs16 Hsq Hsc Hlo
      Hhi Hceil Hwlo Hwhi); try assumption; try lia.
    * apply (pv_ra_keep (w_H W) (ms_mem ms) (ms_mem ms1) q _ _ KEEP1 Hceil); [lia | lia |].
      eapply range_addressable_sub; [exact HRA | lia | lia].
    * intros ms2 mdx2 HAT2 HJ2 HARU2 HRA2 KEEP2.
      replace (cur + Z.of_nat (length (w :: ws))) with (cur + 1 + Z.of_nat (length ws)) in K by (cbn [length]; lia).
      apply (K ms2 mdx2 HAT2 HJ2 HARU2 HRA2). intros x Hx. rewrite (KEEP2 x Hx). exact (KEEP1 x Hx).
Qed.
(* the dispatch 0x830e0 -> 0x8312c -> 0x831b0 (byte 34, the string arm) or 0x831a0 (byte 123, the object arm).
   MEASURED: zero obligations, no memory written; the two shadow checks (q at 0x8312c, the byte at 0x83144) are
   covered by pv_SH. *)
Lemma pv_disp : forall STK ot FP ly S S2 U (W : world tfibsegs) mem md regs0 pos q s sp1 v endv cur b0 ms mdx
  (Q : world tfibsegs -> config -> Prop),
  In (0, pos) (frames S2) ->
  2 ^ 46 <= q <= 2 ^ 47 - 24 -> q mod 8 = 0 -> 2 ^ 46 <= s <= 2 ^ 47 -> s mod 16 = 0 ->
  s <= q -> alloc_ceiling + 104 <= s -> ly_stk_lo ly <= q -> q + 24 <= ly_stk_hi ly -> alloc_ceiling <= q ->
  ot - STK <= q -> q + 8 <= ot ->
  4096 <= cur -> cur + 1 <= endv -> endv <= 2 ^ 47 - 8 ->
  (endv <= q \/ q + 24 <= cur) ->
  (endv <= s - 104 \/ s <= cur) -> (endv <= frame_addr ly 0 pos \/ frame_addr ly 0 pos + 64 <= cur) ->
  (endv <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= cur) ->
  b0 = 34 \/ b0 = 123 ->
  range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF cur 1 ->
  pv_at W regs0 (frame_addr ly 0 pos) (flag_addr ly 0 pos) q s sp1 v endv ms cur [b0] ->
  ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U (ms_mem ms)) mdx 0 ->
  ARU tfibsegs B ly S2 U W (ms_mem ms) mdx ->
  (forall ms' mdx' (pc : Z),
     (b0 = 34 /\ pc = 0x831b0 \/ b0 = 123 /\ pc = 0x831a0) ->
     ms' = mkst (ms_regs ms') (Z_to_bv 64 pc) (ms_mem ms') (seg_rom tfibsegs) ->
     YK11.getr (ms_regs ms') 8%bv = Z_to_bv 64 s -> YK11.getr (ms_regs ms') 9%bv = Z_to_bv 64 sp1 ->
     YK11.getr (ms_regs ms') 18%bv = Z_to_bv 64 (frame_addr ly 0 pos) ->
     YK11.getr (ms_regs ms') 19%bv = Z_to_bv 64 v ->
     YK11.getr (ms_regs ms') 20%bv = Z_to_bv 64 q ->
     YK11.getr (ms_regs ms') 23%bv = Z_to_bv 64 SHADOW_OFF ->
     YK11.getr (ms_regs ms') 24%bv = Z_to_bv 64 (SHADOW_OFF + frame_addr ly 0 pos / 8) ->
     YK11.getr (ms_regs ms') 26%bv = Z_to_bv 64 (frame_addr ly 0 pos) ->
     YK11.getr (ms_regs ms') 3%bv = YK11.getr regs0 3%bv ->
     YK11.getr (ms_regs ms') 4%bv = YK11.getr regs0 4%bv ->
     YK11.getr (ms_regs ms') 2%bv = Z_to_bv 64 sp1 ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms')) q 8 cur ->
     pv_inv (mrestrict (w_H W) (ms_mem ms')) regs0 s (frame_addr ly 0 pos) (flag_addr ly 0 pos) q endv cur [b0] ->
     ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U (ms_mem ms')) mdx' 0 ->
     ARU tfibsegs B ly S2 U W (ms_mem ms') mdx' ->
     (forall x : word, ~ (q <= bv_unsigned x < q + 8) ->
        mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) (ms_mem ms) x) ->
     SRr tfibsegs W (mkCfg ms' mdx') Q) ->
  SRr tfibsegs W (mkCfg ms mdx) Q.
Proof.
intros STK ot FP ly S S2 U W mem md regs0 pos q s sp1 v endv cur b0 ms mdx Q Hin0 Hq Hq8 Hs Hs16 Hsq Hsc Hlo Hhi Hceil
  Hwlo Hwhi Hcur Hend Hend47 Hcq Hcs HcF Hcsh Hb0 HRA
  (HS & Vq0 & HINV & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & RG3 & RG4 & RSP) HJ HARU K.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B ly S2 U W (ms_mem ms) mdx HARU) as HAR.
destruct (al_frames _ _ LAWS ly S2 W (unpoison U (ms_mem ms)) mdx 0 pos HAR Hin0) as (HF32 & HFapp & _ & _).
destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U (ms_mem ms)) mdx 0 pos HAR Hin0) as (HF4096 & HFc & _).
change (fs_frame_bytes 0) with 64 in *.
set (F := frame_addr ly 0 pos) in *. set (FL := flag_addr ly 0 pos) in *.
set (E := Ereg (ms_regs ms) (pv_extra0 regs0 FL ++ pv_xs (SHADOW_OFF + F / 8) cur endv (nth 0 [b0] 0))) in HS.
cbn [nth] in E.
destruct HINV as (Vsv & Vfl & Vq8 & Wq & Htx).
destruct (Htx 0%nat ltac:(cbn; lia)) as [Hb0r Vb0]. cbn [nth] in Hb0r, Vb0. rewrite Z.add_0_r in Vb0.
assert (EA : forall (r : bv 5) n z, Z.of_nat n = bv_unsigned r -> getr (ms_regs ms) r = Z_to_bv 64 z -> ew E n = Z_to_bv 64 z)
  by (intros r n z Hn Hr; subst E; rewrite (ew_Ereg_nat _ _ n r Hn), Hr; reflexivity).
assert (E8 : ew E 8 = Z_to_bv 64 s) by (apply (EA 8%bv); [reflexivity | exact R8]).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (apply (EA 9%bv); [reflexivity | exact R9]).
assert (E18 : ew E 18 = Z_to_bv 64 F) by (apply (EA 18%bv); [reflexivity | exact R18]).
assert (E19 : ew E 19 = Z_to_bv 64 v) by (apply (EA 19%bv); [reflexivity | exact R19]).
assert (E20 : ew E 20 = Z_to_bv 64 q) by (apply (EA 20%bv); [reflexivity | exact R20]).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (apply (EA 23%bv); [reflexivity | exact R23]).
assert (E24 : ew E 24 = Z_to_bv 64 (SHADOW_OFF + F / 8)) by (apply (EA 24%bv); [reflexivity | exact R24]).
assert (E26 : ew E 26 = Z_to_bv 64 F) by (apply (EA 26%bv); [reflexivity | exact R26]).
assert (E48 : ew E 48 = Z_to_bv 64 cur) by (subst E; change 48%nat with (32 + 16)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E49 : ew E 49 = Z_to_bv 64 endv) by (subst E; change 49%nat with (32 + 17)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E50 : ew E 50 = Z_to_bv 64 b0) by (subst E; change 50%nat with (32 + 18)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (B20 : bv_unsigned (ew E 20) = q) by (rewrite E20; apply unsigned_lit_small; lia).
assert (UB : YP0e.U E pv_Bx = SHADOW_OFF) by (unfold pv_Bx; apply (U_atom E 23 SHADOW_OFF E23); unfold SHADOW_OFF; lia).
assert (Hb32 : 32 < b0) by (destruct Hb0 as [->| ->]; lia).
assert (SHOK : sh_ok tfibsegs pv_Bx pv_SH E (mrestrict (w_H W) (ms_mem ms))).
{ constructor; [|constructor; [|constructor; [|constructor]]].
  - split.
    + cbn [she_m she_lo she_hi]. rewrite (U_atom E 20 q E20 ltac:(lia)), Z.add_0_r.
      eapply (obl_of_range tfibsegs (w_H W) (ms_mem ms) E pv_Bx q 24 q 24); [|exact UB | lia | lia].
      apply (pv_ra_unpoison B ly S2 U W (ms_mem ms) _ q 24 HARU); [lia | lia|].
      apply (pv_stack_ra B ly S2 W _ _ q 24 HAR); [lia | lia | exact Hq8 | reflexivity | lia].
    + intros a Ha. cbn [she_m she_lo she_hi] in Ha. rewrite (U_atom E 20 q E20 ltac:(lia)) in Ha. rewrite UB.
      unfold SHADOW_OFF. lia.
  - split.
    + apply range_addressable_nil. cbn [she_lo she_hi]. lia.
    + intros a Ha. cbn [she_m she_lo she_hi] in Ha. rewrite (U_atom E 26 F E26 ltac:(lia)) in Ha. rewrite UB.
      unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp. unfold SHADOW_OFF. lia.
  - split.
    + cbn [she_m she_lo she_hi]. rewrite (U_atom E 48 cur E48 ltac:(lia)), Z.add_0_r.
      exact (obl_of_range tfibsegs (w_H W) (ms_mem ms) E pv_Bx cur 1 cur 1 HRA UB ltac:(lia) ltac:(lia)).
    + intros a Ha. cbn [she_m she_lo she_hi] in Ha. rewrite (U_atom E 48 cur E48 ltac:(lia)) in Ha. rewrite UB.
      unfold SHADOW_OFF in *. lia. }
(* 0x830e0 .. `bltu a3, a5` 0x830f4 *)
fsw_aj_run_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ unfold pv_hd, pv_hd_regions, pv_q_region, pv_txt_region, pv_s0_region, pv_flag_region. pv_awr_hd q ot B20. }
eapply SRr_sym_branch with (c := BC_LTU) (a := SLit 32) (b := SOff 50 0); [exact HS | |].
2: { intros Hb _. exfalso. rewrite branch_ltu_U, U_lit, (pv_U_off _ 50 b0 0) in Hb by first [pv_ewo; exact E50 | lia].
     apply Z.ltb_ge in Hb. lia. }
intros _ HS1. clear HS. rename HS1 into HS.
(* .. 0x8312c (q's shadow check, covered) .. the end test 0x83138 *)
fsw_aj_run_to_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan 0x8312c.
{ pv_awr_hd q ot B20. }
fsw_aj_run_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ pv_awr_hd q ot B20. }
eapply SRr_sym_branch with (c := BC_GEU) (a := SOff 48 0) (b := SOff 49 0); [exact HS | |].
{ intros Hb _. exfalso. rewrite branch_geu_U, (pv_U_off _ 48 cur 0), (pv_U_off _ 49 endv 0) in Hb
    by first [pv_ewo; first [exact E48 | exact E49] | lia].
  apply negb_true_iff, Z.ltb_ge in Hb. lia. }
intros _ HS1. clear HS. rename HS1 into HS.
(* .. the byte's shadow check (covered) and the first dispatch test 0x83154 *)
fsw_aj_run_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ pv_awr_hd q ot B20. }
(* the two arms: byte 34 -> 0x831b0 (string), byte 123 -> 0x831a0 (object) *)
assert (DLT : forall Ex, ew Ex 50 = Z_to_bv 64 b0 ->
  branch_taken BC_LT (sv_denot Ex (SLit 109)) (sv_denot Ex (SOff 50 0)) = (109 <? b0)).
{ intros Ex H50. rewrite (pv_denot_lit Ex 109 ltac:(lia)), (pv_denot_off Ex 50 b0 0 H50 ltac:(lia) ltac:(lia)).
  rewrite Z.add_0_r. exact (bv_lts_small 109 b0 ltac:(lia) ltac:(lia)). }
assert (DEQ : forall Ex (zz : Z), ew Ex 50 = Z_to_bv 64 b0 -> 0 <= zz < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot Ex (SOff 50 0)) (sv_denot Ex (SLit zz)) = (b0 =? zz)).
{ intros Ex zz H50 Hzz. rewrite branch_eq_U, (pv_U_off Ex 50 b0 0 H50 ltac:(lia) ltac:(lia)), U_lit by lia.
  rewrite Z.add_0_r. reflexivity. }
destruct Hb0 as [Hb34 | Hb123].
- (* the string arm *)
  lazymatch type of HS with st_ok _ ?Ey _ _ => assert (G50 : ew Ey 50 = Z_to_bv 64 b0) by (pv_ewo; exact E50) end.
  eapply SRr_sym_branch with (c := BC_LT) (a := SLit 109) (b := SOff 50 0); [exact HS | |].
  { intros Hb _. exfalso. rewrite (DLT _ G50) in Hb. rewrite Hb34 in Hb. discriminate Hb. }
  intros _ HS1. clear HS G50. rename HS1 into HS.
  fsw_aj_run_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan.
  { pv_awr_hd q ot B20. }
  lazymatch type of HS with st_ok _ ?Ey _ _ => assert (G50 : ew Ey 50 = Z_to_bv 64 b0) by (pv_ewo; exact E50) end.
  eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 50 0) (b := SLit 34); [exact HS | |].
  2: { intros Hb _. exfalso. rewrite (DEQ _ 34 G50 ltac:(lia)) in Hb. rewrite Hb34 in Hb. discriminate Hb. }
  intros _ HS1. clear HS G50. rename HS1 into HS.
  fsw_aj_run_to_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan 0x831b0.
  { pv_awr_hd q ot B20. }
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
    assert (KEEP : forall x : word, ~ (q <= bv_unsigned x < q + 8) ->
      mrestrict (w_H W) (ms_mem msF) x = mrestrict (w_H W) (ms_mem ms) x) end.
  { intros x Hx.
    repeat lazymatch goal with
    | |- mrestrict ?Hh (ms_mem ?mA) x = mrestrict ?Hh (ms_mem ms) x =>
        lazymatch goal with
        | HFx : frame_of _ _ (mrestrict Hh (ms_mem _)) (mrestrict Hh (ms_mem mA)) |- _ =>
            rewrite (pv_frame_P _ _ _ _ (fun a => q <= a < q + 8) HFx ltac:(pv_wr_q B20) x Hx)
        end
    end; reflexivity. }
  pv_reg HS (w_H W) (8%bv : bv 5) H8. pv_reg HS (w_H W) (9%bv : bv 5) H9. pv_reg HS (w_H W) (18%bv : bv 5) H18.
  pv_reg HS (w_H W) (19%bv : bv 5) H19. pv_reg HS (w_H W) (20%bv : bv 5) H20. pv_reg HS (w_H W) (23%bv : bv 5) H23.
  pv_reg HS (w_H W) (24%bv : bv 5) H24. pv_reg HS (w_H W) (26%bv : bv 5) H26.
  pv_reg HS (w_H W) (3%bv : bv 5) HGP. pv_reg HS (w_H W) (4%bv : bv 5) HTP. pv_reg HS (w_H W) (2%bv : bv 5) HSP.
  assert (EG3 : ew E 3 = YK11.getr regs0 3%bv)
    by (subst E; rewrite (ew_Ereg_nat (ms_regs ms) _ 3 3%bv eq_refl); exact RG3).
  assert (EG4 : ew E 4 = YK11.getr regs0 4%bv)
    by (subst E; rewrite (ew_Ereg_nat (ms_regs ms) _ 4 4%bv eq_refl); exact RG4).
  lazymatch type of HS with st_ok _ ?Ey _ _ => set (E3 := Ey) in * end.
  assert (F8 : ew E3 8 = Z_to_bv 64 s) by (subst E3; pv_ewo; exact E8).
  assert (F9 : ew E3 9 = Z_to_bv 64 sp1) by (subst E3; pv_ewo; exact E9).
  assert (F18 : ew E3 18 = Z_to_bv 64 F) by (subst E3; pv_ewo; exact E18).
  assert (F19 : ew E3 19 = Z_to_bv 64 v) by (subst E3; pv_ewo; exact E19).
  assert (F20 : ew E3 20 = Z_to_bv 64 q) by (subst E3; pv_ewo; exact E20).
  assert (F23 : ew E3 23 = Z_to_bv 64 SHADOW_OFF) by (subst E3; pv_ewo; exact E23).
  assert (F24 : ew E3 24 = Z_to_bv 64 (SHADOW_OFF + F / 8)) by (subst E3; pv_ewo; exact E24).
  assert (F26 : ew E3 26 = Z_to_bv 64 F) by (subst E3; pv_ewo; exact E26).
  assert (F48 : ew E3 48 = Z_to_bv 64 cur) by (subst E3; pv_ewo; exact E48).
  assert (FG3 : ew E3 3 = YK11.getr regs0 3%bv) by (subst E3; pv_ewo; exact EG3).
  assert (FG4 : ew E3 4 = YK11.getr regs0 4%bv) by (subst E3; pv_ewo; exact EG4).
  rewrite fsw_SOff0, FG3 in HGP. rewrite fsw_SOff0, FG4 in HTP.
  assert (EG2 : ew E 2 = Z_to_bv 64 sp1)
    by (subst E; rewrite (ew_Ereg_nat (ms_regs ms) _ 2 2%bv eq_refl); exact RSP).
  assert (FG2 : ew E3 2 = Z_to_bv 64 sp1) by (subst E3; pv_ewo; exact EG2).
  rewrite fsw_SOff0, FG2 in HSP.
  assert (G20 : bv_unsigned (ew E3 20) = q) by (rewrite F20; apply unsigned_lit_small; lia).
  rewrite fsw_SOff0, F8 in H8. rewrite fsw_SOff0, F9 in H9. rewrite fsw_SOff0, F18 in H18.
  rewrite fsw_SOff0, F19 in H19. rewrite fsw_SOff0, F20 in H20. rewrite fsw_SOff0, F23 in H23.
  rewrite fsw_SOff0, F24 in H24. rewrite fsw_SOff0, F26 in H26.
  pv_region HS 0%nat RQ. cbn [ms_mem restrict] in RQ.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
    assert (Vq0' : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) q 8 cur) end.
  { pose proof (fsw_field _ _ 20 q _ 0 24 0 8 0 8 (SOff 48 0) cur RQ G20 ltac:(left; reflexivity)
      ltac:(rewrite fsw_SOff0; exact F48) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
    rewrite Z.add_0_r in V. exact V. }
  set (P := fun a => q <= a < q + 8).
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
    assert (HINV' : pv_inv (mrestrict (w_H W) (ms_mem msF)) regs0 s F FL q endv cur [b0]) end.
  { split; [|split; [|split; [|split]]].
    - apply (pv_saved_keep _ _ P s regs0 KEEP); [lia | | exact Vsv]. intros a Ha. unfold P. lia.
    - apply (pv_val_keep _ _ P (F + 56) 8 FL KEEP); [lia | cbn; lia | | exact Vfl].
      intros k Hk. unfold P. cbn in Hk. lia.
    - apply (pv_val_keep _ _ P (q + 8) 8 endv KEEP); [lia | cbn; lia | | exact Vq8].
      intros k Hk. unfold P. cbn in Hk. lia.
    - intros o Ho. destruct RQ as (_ & _ & Hw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
      rewrite G20 in Hw. apply Hw. lia.
    - apply (pv_text_keep _ _ P cur [b0] KEEP); [lia | cbn [length]; lia | | exact Htx].
      intros a Ha. unfold P. cbn [length] in Ha. lia. }
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS eq_refl) as Hshape.
  lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 ?pc) _ _ =>
    let pc' := eval vm_compute in pc in change pc with pc' in Hshape end.
  apply (K _ _ 0x831b0); [left; split; [exact Hb34 | reflexivity] | exact Hshape | exact H8 | exact H9 | exact H18
    | exact H19 | exact H20 | exact H23 | exact H24 | exact H26 | exact HGP | exact HTP | exact HSP
    | exact Vq0' | exact HINV' | exact HJ | exact HARU | exact KEEP].
- (* the object arm *)
  lazymatch type of HS with st_ok _ ?Ey _ _ => assert (G50 : ew Ey 50 = Z_to_bv 64 b0) by (pv_ewo; exact E50) end.
  eapply SRr_sym_branch with (c := BC_LT) (a := SLit 109) (b := SOff 50 0); [exact HS | |].
  2: { intros Hb _. exfalso. rewrite (DLT _ G50) in Hb. rewrite Hb123 in Hb. discriminate Hb. }
  intros _ HS1. clear HS G50. rename HS1 into HS.
  fsw_aj_run_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan.
  { pv_awr_hd q ot B20. }
  lazymatch type of HS with st_ok _ ?Ey _ _ => assert (G50 : ew Ey 50 = Z_to_bv 64 b0) by (pv_ewo; exact E50) end.
  eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 50 0) (b := SLit 110); [exact HS | |].
  { intros Hb _. exfalso. rewrite (DEQ _ 110 G50 ltac:(lia)) in Hb. rewrite Hb123 in Hb. discriminate Hb. }
  intros _ HS1. clear HS G50. rename HS1 into HS.
  fsw_aj_run_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan.
  { pv_awr_hd q ot B20. }
  lazymatch type of HS with st_ok _ ?Ey _ _ => assert (G50 : ew Ey 50 = Z_to_bv 64 b0) by (pv_ewo; exact E50) end.
  eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 50 0) (b := SLit 116); [exact HS | |].
  { intros Hb _. exfalso. rewrite (DEQ _ 116 G50 ltac:(lia)) in Hb. rewrite Hb123 in Hb. discriminate Hb. }
  intros _ HS1. clear HS G50. rename HS1 into HS.
  fsw_aj_run_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan.
  { pv_awr_hd q ot B20. }
  lazymatch type of HS with st_ok _ ?Ey _ _ => assert (G50 : ew Ey 50 = Z_to_bv 64 b0) by (pv_ewo; exact E50) end.
  eapply SRr_sym_branch with (c := BC_NE) (a := SOff 50 0) (b := SLit 123); [exact HS | |].
  { intros Hb _. exfalso. rewrite branch_ne_U, (pv_U_off _ 50 b0 0 G50 ltac:(lia) ltac:(lia)), U_lit in Hb by lia.
    rewrite Z.add_0_r, Hb123 in Hb. discriminate Hb. }
  intros _ HS1. clear HS G50. rename HS1 into HS.
  fsw_aj_run_to_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan 0x831a0.
  { pv_awr_hd q ot B20. }
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
    assert (KEEP : forall x : word, ~ (q <= bv_unsigned x < q + 8) ->
      mrestrict (w_H W) (ms_mem msF) x = mrestrict (w_H W) (ms_mem ms) x) end.
  { intros x Hx.
    repeat lazymatch goal with
    | |- mrestrict ?Hh (ms_mem ?mA) x = mrestrict ?Hh (ms_mem ms) x =>
        lazymatch goal with
        | HFx : frame_of _ _ (mrestrict Hh (ms_mem _)) (mrestrict Hh (ms_mem mA)) |- _ =>
            rewrite (pv_frame_P _ _ _ _ (fun a => q <= a < q + 8) HFx ltac:(pv_wr_q B20) x Hx)
        end
    end; reflexivity. }
  pv_reg HS (w_H W) (8%bv : bv 5) H8. pv_reg HS (w_H W) (9%bv : bv 5) H9. pv_reg HS (w_H W) (18%bv : bv 5) H18.
  pv_reg HS (w_H W) (19%bv : bv 5) H19. pv_reg HS (w_H W) (20%bv : bv 5) H20. pv_reg HS (w_H W) (23%bv : bv 5) H23.
  pv_reg HS (w_H W) (24%bv : bv 5) H24. pv_reg HS (w_H W) (26%bv : bv 5) H26.
  pv_reg HS (w_H W) (3%bv : bv 5) HGP. pv_reg HS (w_H W) (4%bv : bv 5) HTP. pv_reg HS (w_H W) (2%bv : bv 5) HSP.
  assert (EG3 : ew E 3 = YK11.getr regs0 3%bv)
    by (subst E; rewrite (ew_Ereg_nat (ms_regs ms) _ 3 3%bv eq_refl); exact RG3).
  assert (EG4 : ew E 4 = YK11.getr regs0 4%bv)
    by (subst E; rewrite (ew_Ereg_nat (ms_regs ms) _ 4 4%bv eq_refl); exact RG4).
  lazymatch type of HS with st_ok _ ?Ey _ _ => set (E3 := Ey) in * end.
  assert (F8 : ew E3 8 = Z_to_bv 64 s) by (subst E3; pv_ewo; exact E8).
  assert (F9 : ew E3 9 = Z_to_bv 64 sp1) by (subst E3; pv_ewo; exact E9).
  assert (F18 : ew E3 18 = Z_to_bv 64 F) by (subst E3; pv_ewo; exact E18).
  assert (F19 : ew E3 19 = Z_to_bv 64 v) by (subst E3; pv_ewo; exact E19).
  assert (F20 : ew E3 20 = Z_to_bv 64 q) by (subst E3; pv_ewo; exact E20).
  assert (F23 : ew E3 23 = Z_to_bv 64 SHADOW_OFF) by (subst E3; pv_ewo; exact E23).
  assert (F24 : ew E3 24 = Z_to_bv 64 (SHADOW_OFF + F / 8)) by (subst E3; pv_ewo; exact E24).
  assert (F26 : ew E3 26 = Z_to_bv 64 F) by (subst E3; pv_ewo; exact E26).
  assert (F48 : ew E3 48 = Z_to_bv 64 cur) by (subst E3; pv_ewo; exact E48).
  assert (FG3 : ew E3 3 = YK11.getr regs0 3%bv) by (subst E3; pv_ewo; exact EG3).
  assert (FG4 : ew E3 4 = YK11.getr regs0 4%bv) by (subst E3; pv_ewo; exact EG4).
  rewrite fsw_SOff0, FG3 in HGP. rewrite fsw_SOff0, FG4 in HTP.
  assert (EG2 : ew E 2 = Z_to_bv 64 sp1)
    by (subst E; rewrite (ew_Ereg_nat (ms_regs ms) _ 2 2%bv eq_refl); exact RSP).
  assert (FG2 : ew E3 2 = Z_to_bv 64 sp1) by (subst E3; pv_ewo; exact EG2).
  rewrite fsw_SOff0, FG2 in HSP.
  assert (G20 : bv_unsigned (ew E3 20) = q) by (rewrite F20; apply unsigned_lit_small; lia).
  rewrite fsw_SOff0, F8 in H8. rewrite fsw_SOff0, F9 in H9. rewrite fsw_SOff0, F18 in H18.
  rewrite fsw_SOff0, F19 in H19. rewrite fsw_SOff0, F20 in H20. rewrite fsw_SOff0, F23 in H23.
  rewrite fsw_SOff0, F24 in H24. rewrite fsw_SOff0, F26 in H26.
  pv_region HS 0%nat RQ. cbn [ms_mem restrict] in RQ.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
    assert (Vq0' : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) q 8 cur) end.
  { pose proof (fsw_field _ _ 20 q _ 0 24 0 8 0 8 (SOff 48 0) cur RQ G20 ltac:(left; reflexivity)
      ltac:(rewrite fsw_SOff0; exact F48) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
    rewrite Z.add_0_r in V. exact V. }
  set (P := fun a => q <= a < q + 8).
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
    assert (HINV' : pv_inv (mrestrict (w_H W) (ms_mem msF)) regs0 s F FL q endv cur [b0]) end.
  { split; [|split; [|split; [|split]]].
    - apply (pv_saved_keep _ _ P s regs0 KEEP); [lia | | exact Vsv]. intros a Ha. unfold P. lia.
    - apply (pv_val_keep _ _ P (F + 56) 8 FL KEEP); [lia | cbn; lia | | exact Vfl].
      intros k Hk. unfold P. cbn in Hk. lia.
    - apply (pv_val_keep _ _ P (q + 8) 8 endv KEEP); [lia | cbn; lia | | exact Vq8].
      intros k Hk. unfold P. cbn in Hk. lia.
    - intros o Ho. destruct RQ as (_ & _ & Hw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
      rewrite G20 in Hw. apply Hw. lia.
    - apply (pv_text_keep _ _ P cur [b0] KEEP); [lia | cbn [length]; lia | | exact Htx].
      intros a Ha. unfold P. cbn [length] in Ha. lia. }
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS eq_refl) as Hshape.
  lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 ?pc) _ _ =>
    let pc' := eval vm_compute in pc in change pc with pc' in Hshape end.
  apply (K _ _ 0x831a0); [right; split; [exact Hb123 | reflexivity] | exact Hshape | exact H8 | exact H9 | exact H18
    | exact H19 | exact H20 | exact H23 | exact H24 | exact H26 | exact HGP | exact HTP | exact HSP
    | exact Vq0' | exact HINV' | exact HJ | exact HARU | exact KEEP].
Qed.
End ST.
(* the epilogue state at 0x83318: F (atom 26, also s2 through SOff 26 0), F's shadow (atom 24), the flag byte
   (atom 46, the address the word at F + 56 holds), and the 13 saved words at s0 (atom 8, read-only). *)
Definition pe_regs : list sv := sr_set sr_atoms 18%bv (SOff 26 0).
Definition pe_s0_region : YP09.region := YP09.mkRegion (Some 8%nat) (-104) 0 0 0 pv_sv_chunks.
Definition pe_F_region : YP09.region :=
  YP09.mkRegion (Some 26%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff 46 0))].
Definition pe_sh_region : YP09.region := YP09.mkRegion (Some 24%nat) 0 8 0 8 [].
Definition pe_fl_region : YP09.region := YP09.mkRegion (Some 46%nat) 0 1 0 1 [].
Definition pe_facts : facts :=
  mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (26%nat, mkAF 4096 (2 ^ 47) 5);
           (24%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 2); (46%nat, mkAF 4096 (2 ^ 47) 0)] [] [].
Definition pe_st : sstate :=
  mkSS 0x83318 pe_regs [pe_F_region; pe_sh_region; pe_fl_region; pe_s0_region] None pe_facts.

Section EP. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma pe_ok : forall (H : word -> bool) regs mem regs0 F FL s xs,
  YK11.getr regs 8%bv = Z_to_bv 64 s -> YK11.getr regs 18%bv = Z_to_bv 64 F ->
  YK11.getr regs 24%bv = Z_to_bv 64 (SHADOW_OFF + F / 8) -> YK11.getr regs 26%bv = Z_to_bv 64 F ->
  2 ^ 46 <= s <= 2 ^ 47 -> s mod 16 = 0 -> 4096 <= F -> F + 64 <= 2 ^ 47 -> F mod 32 = 0 ->
  4096 <= FL <= 2 ^ 47 ->
  F + 64 <= s - 104 -> (FL + 1 <= F \/ F + 64 <= FL) -> (FL + 1 <= s - 104 \/ s <= FL) ->
  (F + 64 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= F) -> (FL + 1 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= FL) ->
  pv_saved_ok (mrestrict H mem) s regs0 ->
  val_mem tfibsegs (mrestrict H mem) (F + 56) 8 FL ->
  (forall o, 0 <= o < 64 -> writable_at tfibsegs (mrestrict H mem) (F + o)) ->
  (forall o, 0 <= o < 8 -> writable_at tfibsegs (mrestrict H mem) (SHADOW_OFF + F / 8 + o)) ->
  writable_at tfibsegs (mrestrict H mem) FL ->
  st_ok tfibsegs (Ereg regs (pv_extra0 regs0 FL ++ xs)) pe_st
    (restrict H (mkst regs (Z_to_bv 64 0x83318) mem (seg_rom tfibsegs))).
Proof.
intros H regs mem regs0 F FL s xs R8 R18 R24 R26 Hs Hs16 HF1 HF2 HF32 HFL Hfs Hflf Hfls Hfsh Hflsh Vsv Vfl WF Wsh Wfl.
set (E := Ereg regs (pv_extra0 regs0 FL ++ xs)).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (A : forall (r : bv 5) n z, Z.of_nat n = bv_unsigned r -> getr regs r = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
  bv_unsigned (ew E n) = z) by (intros r n z Hn Hr Hz; subst E; rewrite (ew_Ereg_nat _ _ n r Hn), Hr; apply wz; exact Hz).
assert (HF8 : 512 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
assert (E8 : bv_unsigned (ew E 8) = s) by (apply (A 8%bv); [reflexivity | exact R8 | lia]).
assert (E24 : bv_unsigned (ew E 24) = SHADOW_OFF + F / 8)
  by (apply (A 24%bv); [reflexivity | exact R24 | unfold SHADOW_OFF in *; lia]).
assert (E26 : bv_unsigned (ew E 26) = F) by (apply (A 26%bv); [reflexivity | exact R26 | lia]).
assert (E46 : bv_unsigned (ew E 46) = FL).
{ subst E. change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra.
  rewrite app_nth1 by (cbn [length pv_extra0]; lia). cbn [nth pv_extra0]. apply wz. lia. }
assert (D : forall n v, bv_unsigned (ew E n) = v -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
  by (intros n v Hn; rewrite fsw_SOff0, <- Hn; symmetry; apply Z_to_bv_bv_unsigned).
rewrite restrict_mkst_fx. unfold pe_st. apply (entry_st_ok_full tfibsegs).
- unfold pe_regs. apply regs_ok_pin; [apply regs_ok_Ereg | discriminate |].
  rewrite R18. symmetry. exact (D 26%nat F E26).
- vm_compute. reflexivity.
- unfold pe_F_region, pe_sh_region, pe_fl_region, pe_s0_region.
  constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E.
    rewrite E26. split; [lia|]. split; [lia|]. split; [intros o Ho; apply WF; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ F 56 8 (SOff 46 0) FL (D 46%nat FL E46)); [cbn; lia | cbn; lia | exact Vfl].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E.
    rewrite E24. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|].
    split; [intros o Ho; apply Wsh; lia | apply Forall_nil].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E.
    rewrite E46. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. replace (FL + o) with FL by lia. exact Wfl.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E.
    rewrite E8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    rewrite pv_sv_chunks_eq.
    assert (SV : forall j, (j < 13)%nat -> YP09.chunk_ok tfibsegs E (mrestrict H mem) s
      (YP09.mkChunk (- 8 * (Z.of_nat j + 1)) (CVal 8 (SOff (33 + j) 0)))).
    { intros j Hj. apply (chunk_ok_val tfibsegs _ _ s _ 8 _ (bv_unsigned (nth j (pv_saved regs0) (Z_to_bv 64 0)))).
      - rewrite Z_to_bv_bv_unsigned. subst E. change (33 + j)%nat with (32 + S j)%nat. rewrite fsw_extra_atom.
        rewrite app_nth1 by (cbn [length pv_extra0]; lia).
        do 13 (destruct j as [|j]; [reflexivity|]). lia.
      - change (8 * Z.of_N 8) with 64. pose proof (u64_range (nth j (pv_saved regs0) (Z_to_bv 64 0))). lia.
      - cbn. lia.
      - replace (s + - 8 * (Z.of_nat j + 1)) with (s - 8 * (Z.of_nat j + 1)) by lia. exact (Vsv j Hj). }
    repeat (apply Forall_cons; [match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff ?a 0))) =>
      let j := eval vm_compute in (a - 33)%nat in exact (SV j ltac:(lia)) end|]). apply Forall_nil.
- apply pairwise_disjoint_of_extents. unfold pe_F_region, pe_sh_region, pe_fl_region, pe_s0_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite E26, E24, E46, E8.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
- unfold pe_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite E8, E24, E26, E46. change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 2) with 4.
  rewrite Z.pow_0_r, !Z.mod_1_r.
  assert (HF84 : (F / 8) mod 4 = 0).
  { assert (HFq : F = (F / 32 * 4) * 8) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
    rewrite HFq, Z.div_mul by lia. apply Z_mod_mult. }
  repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF in *; lia).
Qed.
End EP.
(* an extra atom of the walk's env (32 .. 46: the shadow base, the 13 saved words, the flag address) *)
Lemma pe_extra : forall (regs regs0 : bvmap 5 word) FL (xs : list word) (n : nat), (32 <= n < 47)%nat ->
  ew (Ereg regs (pv_extra0 regs0 FL ++ xs)) n = nth (n - 32) (pv_extra0 regs0 FL) (Z_to_bv 64 0).
Proof.
intros regs regs0 FL xs n Hn. replace n with (32 + (n - 32))%nat at 1 by lia. rewrite ew_Ereg_extra.
apply app_nth1. cbn [length pv_extra0]. lia.
Qed.
Section EP2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the fake-frame kit's unit laws fsw_flag_storeU takes (FSW_frame.v Section f; RUNTIME's, as FSH_Fn_reader.v's header
   names the class-0 stack-free law) *)
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
(* the epilogue 0x83318 -> `ret` 0x833b8: F's magic word, F's shadow := f5 x 8, the flag byte := 0 (which releases
   the frame, FSW_frame.fsw_flag_storeU), the 13 saved words reloaded, and the return through FSW_ret.fsw_retU.
   MEASURED: one plain run, no shadow check, no obligation; at the `ret` ra = the entry ra (atom 33), sp = s0 = the
   entry sp, a0 = s5. *)
(* the bytes the epilogue writes: F's 64 bytes, F's shadow, the flag byte *)
Definition pe_wr (F FL a : Z) : Prop :=
  (F <= a < F + 64) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8) \/ a = FL.
(* The journal runs from any start (ly0 S0 W0 U0 mem0 md0) to the end state (ly S2 W U mem2 md2) with any count kk:
   the composition reaches the epilogue after a callee, whose journal has moved the world, U and the count. *)
Lemma pv_epi : forall STK ot FP ly0 S0 U0 (W0 : world tfibsegs) mem0 md0 kk ly S2 U (W : world tfibsegs) regs0 regs
  mem2 md2 pos s res (xs : list word)
  (Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  let F := frame_addr ly 0 pos in let FL := flag_addr ly 0 pos in
  In (0, pos) (frames S2) ->
  (* no premise for the flag's lower bound: AR_flag_law's `in_app (flag_addr ly cid pos) 1` has `4096 <= lo` as its
     first conjunct (YG0f.v:276), so HFLapp gives it (a Theorem Labs lane 07:12Z). *)
  YK11.getr regs 8%bv = Z_to_bv 64 s -> YK11.getr regs 18%bv = Z_to_bv 64 F ->
  YK11.getr regs 24%bv = Z_to_bv 64 (SHADOW_OFF + F / 8) -> YK11.getr regs 26%bv = Z_to_bv 64 F ->
  YK11.getr regs 21%bv = Z_to_bv 64 res ->
  YK11.getr regs 3%bv = YK11.getr regs0 3%bv -> YK11.getr regs 4%bv = YK11.getr regs0 4%bv ->
  spZ regs0 = s -> YK0s.ret_ok (YK11.getr regs0 1%bv) ->
  2 ^ 46 <= s <= 2 ^ 47 -> s mod 16 = 0 -> ly_stk_lo ly <= s - 104 -> s <= ly_stk_hi ly ->
  ly_stk_hi ly <= 2 ^ 47 -> alloc_ceiling <= ly_stk_lo ly ->
  0 <= res < 2 ^ 64 ->
  pv_saved_ok (mrestrict (w_H W) mem2) s regs0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem2) (F + 56) 8 FL ->
  ajournal tfibsegs B STK ot FP ly0 S0 W0 (unpoison U0 mem0) md0 [(0, pos)] ly S2 W (unpoison U mem2) md2 kk ->
  ARU tfibsegs B ly S2 U W mem2 md2 ->
  (forall mat regsf memf,
     YK11.getr regsf 10%bv = Z_to_bv 64 res ->
     (forall x : word, ~ pe_wr F FL (bv_unsigned x) -> mrestrict (w_H W) memf x = mrestrict (w_H W) mem2 x) ->
     Q ly (stack_free_state 0 pos S2) W regsf memf (with_vm_backing (m_vm_lazy md2) mat md2)) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 0x83318) mem2 (seg_rom tfibsegs)) md2)
    (fpostU tfibsegs B STK ot FP regs0 ly0 S0 U0 W0 mem0 md0 kk U Q).
Proof.
intros STK ot FP ly0 S0 U0 W0 mem0 md0 kk ly S2 U W regs0 regs mem2 md2 pos s res xs Q F FL Hin0 R8 R18 R24 R26 R21 R3
  R4 Hsp Hra Hs Hs16 Hlo Hhi H47 Hceil Hres Vsv Vfl HJ HARU HQ.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B ly S2 U W mem2 md2 HARU) as HAR.
destruct (al_frames _ _ LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR Hin0) as (HF32 & HFapp & HFp & HFSp).
destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR Hin0) as (HF4096 & HFc & _).
destruct (al_flag _ _ LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR Hin0) as (HFLp & HFLo & HFLapp & HFLc).
assert (HFLlo : 4096 <= flag_addr ly 0 pos) by (unfold in_app in HFLapp; lia).
change (fs_frame_bytes 0) with 64 in *.
fold F in HF32, HFapp, HFp, HFSp, HF4096, HFc. fold FL in HFLp, HFLo, HFLapp, HFLc, HFLlo.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & HJstk & _).
(* the frame's bytes, its shadow and the flag byte are writable; the flag is no frame byte and no stack byte *)
assert (WF : forall o, 0 <= o < 64 -> writable_at tfibsegs (mrestrict (w_H W) mem2) (F + o)).
{ intros o Ho. apply (apresent_writable tfibsegs). destruct (HFp (F + o) ltac:(lia)) as (Hp & Hno).
  exact (fsw_apresent_notowned B ly S2 U W mem2 md2 (F + o) HARU ltac:(lia) Hno Hp). }
assert (HF8 : 512 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
assert (Wsh : forall o, 0 <= o < 8 -> writable_at tfibsegs (mrestrict (w_H W) mem2) (SHADOW_OFF + F / 8 + o)).
{ intros o Ho. apply (apresent_writable tfibsegs). destruct (HFSp o ltac:(change (64 / 8) with 8; lia)) as (Hp & Hno).
  unfold shadow_addr in Hp, Hno.
  exact (fsw_apresent_notowned B ly S2 U W mem2 md2 (SHADOW_OFF + F / 8 + o) HARU ltac:(unfold SHADOW_OFF; lia) Hno Hp). }
(* the flag byte is no user-poisoned byte of U (those are live blocks' shadow bytes, inside the band; the flag is
   application memory), so the machine's memory holds it where the unpoisoned reading does *)
assert (HflagU : in_ush U FL = false).
{ destruct (in_ush U FL) eqn:Eu; [|reflexivity]. exfalso.
  pose proof (ush_facts tfibsegs B ly S2 U W mem2 md2 _ HARU Eu) as (_ & L1 & L2).
  unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg, SHADOW_OFF in *. lia. }
assert (Wfl : writable_at tfibsegs (mrestrict (w_H W) mem2) FL).
{ apply (apresent_writable tfibsegs). destruct HFLp as (Hh & b & Hb). split; [exact Hh|]. exists b.
  rewrite <- Hb. symmetry. apply unpoison_out. rewrite (wz FL ltac:(unfold in_app in HFLapp; lia)). exact HflagU. }
assert (HflF : FL + 1 <= F \/ F + 64 <= FL).
{ destruct (Z_lt_le_dec FL F) as [Hl|Hl]; [left; lia|]. destruct (Z_le_gt_dec (F + 64) FL) as [Hr|Hr]; [right; lia|].
  exfalso. destruct (HFp FL ltac:(lia)) as (_ & Hno). exact (Hno HFLo). }
assert (HflS : FL + 1 <= s - 104 \/ s <= FL) by lia.
assert (HflSh : FL + 1 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= FL)
  by (unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg in HFLapp; unfold SHADOW_OFF; lia).
assert (HFsh : F + 64 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= F)
  by (unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg in HFapp; unfold SHADOW_OFF; lia).
assert (HFs : F + 64 <= s - 104) by lia.
pose proof (pe_ok (w_H W) regs mem2 regs0 F FL s xs R8 R18 R24 R26 Hs Hs16 ltac:(lia) ltac:(lia) HF32
  ltac:(lia) HFs HflF HflS HFsh HflSh Vsv Vfl WF Wsh Wfl) as HS.
set (E := Ereg regs (pv_extra0 regs0 FL ++ xs)) in HS.
assert (A : forall (r : bv 5) n z, Z.of_nat n = bv_unsigned r -> getr regs r = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
  bv_unsigned (ew E n) = z) by (intros r n z Hn Hr Hz; subst E; rewrite (ew_Ereg_nat _ _ n r Hn), Hr; apply wz; exact Hz).
assert (B24 : bv_unsigned (ew E 24) = SHADOW_OFF + F / 8)
  by (apply (A 24%bv); [reflexivity | exact R24 | unfold SHADOW_OFF in *; lia]).
assert (B26 : bv_unsigned (ew E 26) = F) by (apply (A 26%bv); [reflexivity | exact R26 | lia]).
assert (B46 : bv_unsigned (ew E 46) = FL).
{ subst E. change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra.
  rewrite app_nth1 by (cbn [length pv_extra0]; lia). cbn [nth pv_extra0]. apply wz. lia. }
(* the whole epilogue as one run; its last store is the flag byte, which releases the frame. The run is computed
   first, so no vm_compute below meets an evar *)
lazymatch eval vm_compute in (sym_runN tfibsegs pv_tbl FUEL pe_st) with (?ssF, ?stF) =>
  assert (Hrun : sym_runN tfibsegs pv_tbl FUEL pe_st = (ssF, stF)) by (vm_compute; reflexivity);
  apply (fsw_flag_storeU B ML ASF FFL pv_tbl pv_tbl_ok W FUEL E pe_st ssF stF _ STK ot FP ly0 S0 W0 (unpoison U0 mem0)
    md0 [] ly S2 U md2 kk 0 pos _ HS Hrun I HJ HARU ltac:(lia)) end.
- (* the write windows: F's 64 bytes, F's shadow, and the flag byte *)
  intros a Ha. cbn [ss_mem pe_st] in Ha.
  apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha].
  { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pe_F_region] in Ha. rewrite B26 in Ha.
    left. unfold awr_byte, awr_byte0. left; right; right; right. exists 0, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. lia. }
  apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha].
  { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pe_sh_region] in Ha. rewrite B24 in Ha.
    left. unfold awr_byte, awr_byte0. left; right; right; right. exists 0, pos. split; [left; reflexivity|].
    right. unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 0 / 8) with 8. lia. }
  apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha].
  { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pe_fl_region] in Ha. rewrite B46 in Ha. right. lia. }
  apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha].
  { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pe_s0_region] in Ha. lia. }
  exfalso. exact (pv_wrange_nil _ _ Ha).
- (* the flag byte is 0 at the end (the run's last store) *)
  intros msr HSr. pv_region HSr 2%nat RF.
  pose proof (fsw_field _ _ 46 FL _ 0 1 0 1 0 1 (SLit 0) 0 RF B46 ltac:(left; reflexivity)
    ltac:(apply pv_denot_lit; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  pose proof (V 0%nat ltac:(cbn; lia)) as V0. cbn [Z.of_nat] in V0. rewrite !Z.add_0_r in V0. exact V0.
- (* the return *)
  intros msf matf HSf HJf HARUf HFr HFrr HG.
  lazymatch type of HSf with st_ok _ _ ?ssx _ =>
    apply (fsw_retU B pv_tbl pv_tbl_ok W E ssx msf _ STK ot FP regs0 ly0 S0 U0 W0 mem0 md0 ly
      (stack_free_state 0 pos S2) U kk Q HSf ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) end.
  + pose proof (fsw_reg_extra _ regs (pv_extra0 regs0 FL ++ xs) _ msf 1%bv 1 HSf ltac:(vm_compute; reflexivity)) as R1F.
    rewrite R1F, app_nth1 by (cbn [length pv_extra0]; lia). cbn [nth pv_extra0]. exact Hra.
  + exact HJf.
  + exact HARUf.
  + intros r Hr. unfold acallee_saved in Hr.
    rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ msf (Z_to_bv 5 r) HSf).
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hr' as [->|Hr']); try subst r;
      lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?sx) ?rr) = _ =>
        let t := eval vm_compute in (sr_get (ss_regs sx) rr) in change (sr_get (ss_regs sx) rr) with t end;
      rewrite fsw_SOff0; subst E;
      first
      [ rewrite pe_extra by lia; cbn [Nat.sub nth pv_extra0]; reflexivity
      | rewrite (ew_Ereg_nat regs (pv_extra0 regs0 FL ++ xs) 8 8%bv eq_refl), R8;
        unfold spZ in Hsp; rewrite <- Hsp; apply Z_to_bv_bv_unsigned
      | rewrite (ew_Ereg_nat regs (pv_extra0 regs0 FL ++ xs) 3 3%bv eq_refl); exact R3
      | rewrite (ew_Ereg_nat regs (pv_extra0 regs0 FL ++ xs) 4 4%bv eq_refl); exact R4 ].
  + intros mat. apply HQ.
    * pv_reg HSf (w_H W) (10%bv : bv 5) H10f. rewrite H10f, fsw_SOff0. subst E.
      rewrite (ew_Ereg_nat regs (pv_extra0 regs0 FL ++ xs) 21 21%bv eq_refl). exact R21.
    * intros x Hx. apply (pv_frame_P _ _ _ _ (pe_wr F FL) HFrr); [|exact Hx].
      intros a Ha. cbn [ss_mem pe_st] in Ha. unfold pe_wr.
      apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha].
      { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pe_F_region] in Ha. rewrite B26 in Ha. left. lia. }
      apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha].
      { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pe_sh_region] in Ha. rewrite B24 in Ha. right; left. lia. }
      apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha].
      { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pe_fl_region] in Ha. rewrite B46 in Ha. right; right. lia. }
      apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha].
      { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pe_s0_region] in Ha. lia. }
      exfalso. exact (pv_wrange_nil _ _ Ha).
Qed.
End EP2.
(* the string arm's entry state 0x831b0: v (atom 19, 56 bytes readable, its write window the type word [v, v + 4)) and
   the shadow base (atom 23); the shent for v is what makes its inline shadow check 0x831b8 `covered` (report site
   0x834d4) *)
Definition ps_v_region : YP09.region := YP09.mkRegion (Some 19%nat) 0 56 0 4 [].
Definition ps_facts : facts :=
  mkFacts [(19%nat, mkAF 4096 (2 ^ 47 - 56) 3); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ps_st : sstate := mkSS 0x831b0 sr_atoms [ps_v_region] None ps_facts.
Definition ps_SH : list shent := [mkSHE 19 0 56].
Definition ps_Bx : sv := SOff 23 0.

Section SA. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma ps_ok : forall (H : word -> bool) regs mem extra v,
  YK11.getr regs 19%bv = Z_to_bv 64 v -> YK11.getr regs 23%bv = Z_to_bv 64 SHADOW_OFF ->
  4096 <= v -> v + 56 <= 2 ^ 47 -> v mod 8 = 0 ->
  (forall o, 0 <= o < 56 -> writable_at tfibsegs (mrestrict H mem) (v + o)) ->
  st_ok tfibsegs (Ereg regs extra) ps_st (restrict H (mkst regs (Z_to_bv 64 0x831b0) mem (seg_rom tfibsegs))).
Proof.
intros H regs mem extra v R19 R23 Hv1 Hv2 Hv8 Wv.
set (E := Ereg regs extra).
pose proof asan_consts as (C1 & _).
assert (E19 : bv_unsigned (ew E 19) = v)
  by (subst E; rewrite (ew_Ereg_nat regs extra 19 19%bv eq_refl), R19; apply wz; lia).
assert (E23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs extra 23 23%bv eq_refl), R23; apply wz; unfold SHADOW_OFF; lia).
rewrite restrict_mkst_fx. unfold ps_st. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold ps_v_region. constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E.
  rewrite E19. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wv; lia | apply Forall_nil].
- apply pairwise_disjoint_of_extents. unfold ps_v_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. split; exact I.
- unfold ps_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite E19, E23. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
  split; [split; [lia | split; [exact Hv8 | lia]]|]. split; [|exact I]. unfold SHADOW_OFF. lia.
Qed.
End SA.

Section SA2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* 0x831b0 -> THE CALLEE'S ENTRY A_parse_string (the run steps the `jal` 0x831cc, as the grant's run stepped
   __asan_stack_malloc_0's): v's shadow check (covered by ps_SH), v->type := 4, a0 := q, ra := 0x831d0.
   MEASURED: no obligation, no token; the only write is v's type word [v, v + 4). *)
Lemma pv_str0 : forall STK ot FP ly S S2 U (W : world tfibsegs) mem md regs mem2 md2 pos q v
  (Q : world tfibsegs -> config -> Prop),
  YK11.getr regs 19%bv = Z_to_bv 64 v -> YK11.getr regs 23%bv = Z_to_bv 64 SHADOW_OFF ->
  YK11.getr regs 20%bv = Z_to_bv 64 q ->
  4096 <= v -> v + 56 <= 2 ^ 47 -> v mod 8 = 0 -> 0 <= q < 2 ^ 64 ->
  (v + 56 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= v) ->
  range_addressable (aview tfibsegs (w_H W) mem2) SHADOW_OFF v 56 ->
  (forall o, 0 <= o < 56 -> writable_at tfibsegs (mrestrict (w_H W) mem2) (v + o)) ->
  (forall a, in_zr a (v, 56) -> awr_byte tfibsegs B STK ot FP (ablocks B ly S) (ablocks B ly S2) ly [(0, pos)]
     (frames S) a) ->
  ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U mem2) md2 0 ->
  ARU tfibsegs B ly S2 U W mem2 md2 ->
  (forall ms' mdx',
     ms' = mkst (ms_regs ms') (Z_to_bv 64 A_parse_string) (ms_mem ms') (seg_rom tfibsegs) ->
     YK11.getr (ms_regs ms') 10%bv = Z_to_bv 64 q -> YK11.getr (ms_regs ms') 1%bv = Z_to_bv 64 0x831d0 ->
     aregs_preserved regs (ms_regs ms') ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms')) v 4 4 ->
     ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U (ms_mem ms')) mdx' 0 ->
     ARU tfibsegs B ly S2 U W (ms_mem ms') mdx' ->
     (forall x : word, ~ (v <= bv_unsigned x < v + 4) ->
        mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) mem2 x) ->
     SRr tfibsegs W (mkCfg ms' mdx') Q) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 0x831b0) mem2 (seg_rom tfibsegs)) md2) Q.
Proof.
intros STK ot FP ly S S2 U W mem md regs mem2 md2 pos q v Q R19 R23 R20 Hv1 Hv2 Hv8 Hq Hvb HRA Wv HAWR HJ HARU K.
pose proof asan_consts as (C1 & _).
pose proof (ps_ok (w_H W) regs mem2 fs_extraT v R19 R23 Hv1 Hv2 Hv8 Wv) as HS.
set (E := Ereg regs fs_extraT) in HS.
assert (E19 : bv_unsigned (ew E 19) = v)
  by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 19 19%bv eq_refl), R19; apply wz; lia).
assert (E23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 23 23%bv eq_refl), R23; apply wz; unfold SHADOW_OFF; lia).
assert (UB : YP0e.U E ps_Bx = SHADOW_OFF) by (unfold ps_Bx; rewrite U_SOff, E23; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
assert (SHOK : sh_ok tfibsegs ps_Bx ps_SH E (mrestrict (w_H W) mem2)).
{ constructor; [|constructor]. split.
  - cbn [she_m she_lo she_hi]. rewrite (U_atom E 19 v ltac:(rewrite <- E19; symmetry; apply Z_to_bv_bv_unsigned)
      ltac:(lia)), Z.add_0_r.
    exact (obl_of_range tfibsegs (w_H W) mem2 E ps_Bx v 56 v 56 HRA UB ltac:(lia) ltac:(lia)).
  - intros a Ha. cbn [she_m she_lo she_hi] in Ha.
    rewrite (U_atom E 19 v ltac:(rewrite <- E19; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia)) in Ha.
    rewrite UB. unfold SHADOW_OFF in *. lia. }
fsw_aj_run_to_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan A_parse_string.
{ cbn [ss_mem ps_st]. eapply awr_ok_cons_gen with (k := 19%nat) (b := v); [reflexivity | exact E19 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi ps_v_region] in Ha. apply HAWR. unfold in_zr. cbn [fst snd]. lia. }
(* the state at the call *)
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
  assert (KEEP : forall x : word, ~ (v <= bv_unsigned x < v + 4) ->
    mrestrict (w_H W) (ms_mem msF) x = mrestrict (w_H W) mem2 x) end.
{ intros x Hx.
  rewrite (pv_frame_P _ _ _ _ (fun a => v <= a < v + 4) HFr
    ltac:(intros a Ha; cbn [ss_mem ps_st] in Ha; apply pv_wrange_cases in Ha; destruct Ha as [Ha|Ha];
          [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ps_v_region] in Ha; rewrite E19 in Ha; lia
          | exfalso; exact (pv_wrange_nil _ _ Ha)]) x Hx).
  reflexivity. }
lazymatch type of HS with st_ok _ ?Ey _ _ => set (E1 := Ey) in * end.
assert (F19 : bv_unsigned (ew E1 19) = v) by (subst E1; pv_ewo; exact E19).
assert (F20 : ew E1 20 = Z_to_bv 64 q) by (subst E1; pv_ewo; subst E;
  rewrite (ew_Ereg_nat regs fs_extraT 20 20%bv eq_refl); exact R20).
pv_reg HS (w_H W) (10%bv : bv 5) H10. pv_reg HS (w_H W) (1%bv : bv 5) H1.
rewrite fsw_SOff0, F20 in H10.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS eq_refl) as Hshape.
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 ?pc) _ _ =>
  let pc' := eval vm_compute in pc in change pc with pc' in Hshape end.
pv_region HS 0%nat RV. cbn [ms_mem restrict] in RV.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
  assert (Vty : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) v 4 4) end.
{ pose proof (fsw_field _ _ 19 v _ 0 56 0 4 0 4 (SLit 4) 4 RV F19 ltac:(left; reflexivity)
    ltac:(apply pv_denot_lit; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  rewrite Z.add_0_r in V. exact V. }
apply (K _ _); [exact Hshape | exact H10 | | | exact Vty | exact HJ | exact HARU | exact KEEP].
- rewrite H1. apply pv_denot_lit. lia.
- lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
    apply (aregs_preserved_of_st_ok tfibsegs (w_H W) E1 _ msF regs fs_extraT HS) end;
    [subst E1; subst E; apply env_agree_refl | vm_compute; reflexivity].
Qed.
End SA2.
Section SC. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
(* parse_string's contract as a hypothesis (the top lemma's shape, a Theorem Labs lane 08:21Z): S0 proves it as
   FSW_parse_string.parse_string_proof (under fuzz_malloc_spec); the reader top discharges it there *)
Hypothesis HPS : parse_string_spec tfibsegs B.
(* the parse_string call: from the callee's entry state (pv_str0's hand-over) to its return 0x831d0, through HPS. The
   caller's journal composes with the callee's over the FP-keyed core (FSW_K3.fsw_rt_atU3); the callee's window
   [sp1 - STK_parse_string, sp1) lies inside the caller's [ot - STK, ot). *)
Lemma pv_strcall : forall STK ot FP ly S S2 U (W : world tfibsegs) mem md regsC memC mdC pos q s sp1 text len p d
    (tb : list byte) tcap Q live peak cnt fail (Qp : world tfibsegs -> config -> Prop),
  (* the state at the callee's entry *)
  spZ regsC = sp1 -> YK11.getr regsC 10%bv = Z_to_bv 64 q -> YK11.getr regsC 1%bv = Z_to_bv 64 0x831d0 ->
  YK11.getr regsC 3%bv = w64 (as_gp B) -> YK11.getr regsC 4%bv = w64 (as_tp B) ->
  YK11.getr regsC 8%bv = Z_to_bv 64 s -> 0 <= s < 2 ^ 64 ->
  sp1 mod 16 = 0 -> alloc_ceiling <= ly_stk_lo ly -> ly_stk_lo ly + STK_parse_string <= sp1 ->
  ot - STK <= sp1 - STK_parse_string -> sp1 <= ot -> sp1 + 16 <= q ->
  (* the chain fpreU reads at the callee's entry (its s0 is still parse_value's s0 = s) *)
  (exists ch0, achain ly (aview tfibsegs (w_H W) (unpoison U memC)) sp1 s ch0) ->
  (* the chain parse_string's own C5 premise reads at its fuzz_malloc call (rooted at q) *)
  (exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U memC)) (sp1 - FRAME_parse_string) q chq) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memC) ->
  FSupoisonU.fs_heads B ly S2 U ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) memC) q text len p d tb ->
  rd_win tfibsegs regsC ly W memC q ot ->
  rd_text tfibsegs B ly S2 W memC text len tcap ->
  p < text + len -> nth_error tb (Z.to_nat (p - text)) = Some (Z_to_bv 8 34) ->
  plain_run tb text len p Q ->
  fs_glob tfibsegs W memC live peak cnt fail -> quiet cnt fail 1 ->
  Q + 1 + HEAD < MALLOC_MAX -> live + Q + 1 < 2 ^ 64 ->
  st_nev S2 + EV_fuzz_malloc <= EV_MAX -> blocks_bytes S2 + (Q + 1 + HEAD) <= LIVE_MAX ->
  ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U memC) mdC 0 ->
  ARU tfibsegs B ly S2 U W memC mdC ->
  (forall a, inFP FS_PSTAT_FP a ->
     (inFP FP a /\ exists b n, In (b, n) (ablocks B ly S2) /\ b <= a < b + req_size n) \/
     in_tmp_block (ablocks B ly S) (ablocks B ly S2) a \/ (inFP FP a /\ in_img tfibsegs a)) ->
  (forall ly2 S3 W2 regs2 mem2 md2 a,
     ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly2 S3 W2
       (unpoison (U ++ [(a - HEAD, HEAD)]) mem2) md2 EV_fuzz_malloc ->
     ARU tfibsegs B ly2 S3 (U ++ [(a - HEAD, HEAD)]) W2 mem2 md2 ->
     aregs_preserved regsC regs2 ->
     YK11.getr regs2 10%bv = w64 a -> 4096 + HEAD <= a ->
     ablocks B ly2 S3 = ablocks B ly S2 ++ [(a - HEAD, Q + 1 + HEAD)] ->
     fs_rblock tfibsegs B ly2 S3 W2 mem2 a (Q + 1) ->
     PjStruct.pj_cbytes tfibsegs (mrestrict (w_H W2) mem2) a (run_at tb text p Q) ->
     PjIn.pj_in_ok tfibsegs (mrestrict (w_H W2) mem2) q text len (p + Q + 2) d tb ->
     wkeep tfibsegs W W2 memC mem2 sp1 ot q 24 ->
     rd_text tfibsegs B ly2 S3 W2 mem2 text len tcap ->
     fs_glob tfibsegs W2 mem2 (live + Q + 1) (Z.max peak (live + Q + 1)) (cnt + 1) fail ->
     SRr tfibsegs W2 (YG0d.cfg_at tfibsegs 0x831d0 regs2 mem2 md2) Qp) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_string regsC memC mdC) Qp.
Proof.
intros STK ot FP ly S S2 U W mem md regsC memC mdC pos q s sp1 text len p d tb tcap Q live peak cnt fail Qp
  Csp C10 C1 C3 C4 C8 Hs64 Hal16 Hceil HSTK Hwin Hsp1ot Hq16 HCH0 HCH HRO FH HIN HWIN HTX Hplen Hquote HPR HGL Hquiet
  HQm Hlive Hnev Hbb HJ HARU HFP K.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1a & _).
destruct HCH as [chq HCHq]. destruct HCH0 as [ch0 HCH0q].
(* the callee's fpreU at its entry (its s0 is still parse_value's s0 = s) *)
assert (HPREc : fpreU tfibsegs B STK_parse_string ly S2 U W regsC memC mdC ch0).
{ apply (fsw_fpreU_atFP B STK ot FP ly S U W (unpoison U mem) md [(0, pos)] ly S2 W memC mdC 0 regsC
    STK_parse_string (sp1 - ot) ch0 HJ HARU HRO);
    [rewrite Csp; lia | | lia | | lia | rewrite C1; vm_compute; reflexivity | | rewrite C3; reflexivity
     | rewrite C4; reflexivity |].
  - assert (Hot16 : ot mod 16 = 0) by (pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _);
      exact (proj1 Hstk)).
    rewrite Zminus_mod, Hal16, Hot16. reflexivity.
  - unfold STK_parse_string. vm_compute. discriminate.
  - unfold raZ. rewrite C1. rewrite (unsigned_lit_small 0x831d0) by lia. lia.
  - unfold s0Z. rewrite Csp, C8, (unsigned_lit_small s) by lia. exact HCH0q. }
(* parse_string's contract at the callee's entry *)
eapply SRr_bind.
{ exact (HPS ly S2 U W regsC memC mdC ch0 q ot text len p d tb tcap Q live peak cnt fail
    HPREc FH ltac:(exists chq; rewrite Csp; exact HCHq) ltac:(rewrite Csp; lia) C10 HIN HWIN HTX Hplen Hquote HPR HGL
    Hquiet HQm Hlive Hnev Hbb). }
cbv beta. intros W' c' _ (a & ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HQ').
destruct HQ' as (Q10 & Q4096 & Qab & QRB & Qcb & QIN & QWK & QTX & QGL).
subst c'. rewrite C1.
(* the journals compose: the callee's window [sp1 - STK_parse_string, ot) lies inside the caller's [ot - STK, ot) *)
destruct (fsw_rt_atU3 B STK ot FP ly S W (unpoison U mem) md [(0, pos)] ly S2 U W memC mdC 0
  (STK_parse_string + (ot - spZ regsC)) ot FS_PSTAT_FP [] ly' S' (U ++ [(a - HEAD, HEAD)]) W' mem' md' EV_fuzz_malloc
  HJ HJc OK' PO' ltac:(rewrite Csp; lia) ltac:(lia) HFP) as (HJ2 & HARU2).
apply (K ly' S' W' regs' mem' md' a);
  [exact HJ2 | exact HARU2 | exact HP | exact Q10 | exact Q4096 | exact Qab | exact QRB | exact Qcb | exact QIN
   | rewrite Csp in QWK; exact QWK | exact QTX | exact QGL].
Qed.
End SC.
(* the string arm after the call, 0x831d0 -> the epilogue 0x83318: v->str := a0 at v + 16 (its shadow check at
   0x831dc is report site 0x83544, covered by pq_SH), s5 := 0 because the result is non-zero *)
Definition pq_v_region : YP09.region := YP09.mkRegion (Some 19%nat) 16 24 16 24 [].
Definition pq_facts : facts :=
  mkFacts [(19%nat, mkAF 4096 (2 ^ 47 - 56) 3); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (10%nat, mkAF 4112 (2 ^ 47) 0)] [] [].
Definition pq_st : sstate := mkSS 0x831d0 sr_atoms [pq_v_region] None pq_facts.
Definition pq_SH : list shent := [mkSHE 19 16 24].

Section SB. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma pq_ok : forall (H : word -> bool) regs mem extra v a,
  YK11.getr regs 19%bv = Z_to_bv 64 v -> YK11.getr regs 23%bv = Z_to_bv 64 SHADOW_OFF ->
  YK11.getr regs 10%bv = Z_to_bv 64 a ->
  4096 <= v -> v + 56 <= 2 ^ 47 -> v mod 8 = 0 -> 4112 <= a <= 2 ^ 47 ->
  (forall o, 16 <= o < 24 -> writable_at tfibsegs (mrestrict H mem) (v + o)) ->
  st_ok tfibsegs (Ereg regs extra) pq_st (restrict H (mkst regs (Z_to_bv 64 0x831d0) mem (seg_rom tfibsegs))).
Proof.
intros H regs mem extra v a R19 R23 R10 Hv1 Hv2 Hv8 Ha Wv.
set (E := Ereg regs extra).
pose proof asan_consts as (C1 & _).
assert (E19 : bv_unsigned (ew E 19) = v)
  by (subst E; rewrite (ew_Ereg_nat regs extra 19 19%bv eq_refl), R19; apply wz; lia).
assert (E23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs extra 23 23%bv eq_refl), R23; apply wz; unfold SHADOW_OFF; lia).
assert (E10 : bv_unsigned (ew E 10) = a)
  by (subst E; rewrite (ew_Ereg_nat regs extra 10 10%bv eq_refl), R10; apply wz; lia).
rewrite restrict_mkst_fx. unfold pq_st. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold pq_v_region. constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E.
  rewrite E19. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wv; lia | apply Forall_nil].
- apply pairwise_disjoint_of_extents. unfold pq_v_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. split; exact I.
- unfold pq_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite E19, E23, E10. change (2 ^ 3) with 8. rewrite Z.pow_0_r, !Z.mod_1_r.
  split; [split; [lia | split; [exact Hv8 | lia]]|]. split; [unfold SHADOW_OFF; lia|]. split; [lia | exact I].
Qed.
End SB.

Section SB2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the journal runs from any start (ly0 S0 W0 U0 mem0 md0) with any count kk: the segment follows the parse_string call,
   whose journal has moved the world, U and the count *)
Lemma pv_str1 : forall STK ot FP ly0 S0 U0 (W0 : world tfibsegs) mem0 md0 kk ly S2 U (W : world tfibsegs) regs mem2 md2
  pos v a
  (Q : world tfibsegs -> config -> Prop),
  YK11.getr regs 19%bv = Z_to_bv 64 v -> YK11.getr regs 23%bv = Z_to_bv 64 SHADOW_OFF ->
  YK11.getr regs 10%bv = Z_to_bv 64 a ->
  4096 <= v -> v + 56 <= 2 ^ 47 -> v mod 8 = 0 -> 4112 <= a <= 2 ^ 47 ->
  (v + 56 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= v) ->
  range_addressable (aview tfibsegs (w_H W) mem2) SHADOW_OFF (v + 16) 8 ->
  (forall o, 16 <= o < 24 -> writable_at tfibsegs (mrestrict (w_H W) mem2) (v + o)) ->
  (forall x, in_zr x (v + 16, 8) -> awr_byte tfibsegs B STK ot FP (ablocks B ly0 S0) (ablocks B ly S2) ly [(0, pos)]
     (frames S0) x) ->
  ajournal tfibsegs B STK ot FP ly0 S0 W0 (unpoison U0 mem0) md0 [(0, pos)] ly S2 W (unpoison U mem2) md2 kk ->
  ARU tfibsegs B ly S2 U W mem2 md2 ->
  (forall ms' mdx',
     ms' = mkst (ms_regs ms') (Z_to_bv 64 0x83318) (ms_mem ms') (seg_rom tfibsegs) ->
     YK11.getr (ms_regs ms') 21%bv = Z_to_bv 64 0 ->
     (* every callee-saved register but s5, which this segment sets *)
     YK11.getr (ms_regs ms') 8%bv = YK11.getr regs 8%bv ->
     YK11.getr (ms_regs ms') 9%bv = YK11.getr regs 9%bv ->
     YK11.getr (ms_regs ms') 18%bv = YK11.getr regs 18%bv ->
     (* s3 is NOT kept: 0x831d0 sets it to v + 16 *)
     YK11.getr (ms_regs ms') 20%bv = YK11.getr regs 20%bv ->
     YK11.getr (ms_regs ms') 23%bv = YK11.getr regs 23%bv ->
     YK11.getr (ms_regs ms') 24%bv = YK11.getr regs 24%bv ->
     YK11.getr (ms_regs ms') 26%bv = YK11.getr regs 26%bv ->
     YK11.getr (ms_regs ms') 3%bv = YK11.getr regs 3%bv -> YK11.getr (ms_regs ms') 4%bv = YK11.getr regs 4%bv ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms')) (v + 16) 8 a ->
     ajournal tfibsegs B STK ot FP ly0 S0 W0 (unpoison U0 mem0) md0 [(0, pos)] ly S2 W (unpoison U (ms_mem ms')) mdx' kk ->
     ARU tfibsegs B ly S2 U W (ms_mem ms') mdx' ->
     (forall x : word, ~ (v + 16 <= bv_unsigned x < v + 24) ->
        mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) mem2 x) ->
     SRr tfibsegs W (mkCfg ms' mdx') Q) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 0x831d0) mem2 (seg_rom tfibsegs)) md2) Q.
Proof.
intros STK ot FP ly0 S0 U0 W0 mem0 md0 kk ly S2 U W regs mem2 md2 pos v a Q R19 R23 R10 Hv1 Hv2 Hv8 Ha Hvb HRA Wv HAWR HJ
  HARU K.
pose proof asan_consts as (C1 & _).
pose proof (pq_ok (w_H W) regs mem2 fs_extraT v a R19 R23 R10 Hv1 Hv2 Hv8 Ha Wv) as HS.
set (E := Ereg regs fs_extraT) in HS.
assert (E19 : bv_unsigned (ew E 19) = v)
  by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 19 19%bv eq_refl), R19; apply wz; lia).
assert (E23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 23 23%bv eq_refl), R23; apply wz; unfold SHADOW_OFF; lia).
assert (E10 : bv_unsigned (ew E 10) = a)
  by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 10 10%bv eq_refl), R10; apply wz; lia).
assert (UB : YP0e.U E ps_Bx = SHADOW_OFF) by (unfold ps_Bx; rewrite U_SOff, E23; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
assert (SHOK : sh_ok tfibsegs ps_Bx pq_SH E (mrestrict (w_H W) mem2)).
{ constructor; [|constructor]. split.
  - cbn [she_m she_lo she_hi]. rewrite (U_atom E 19 v ltac:(rewrite <- E19; symmetry; apply Z_to_bv_bv_unsigned)
      ltac:(lia)).
    exact (obl_of_range tfibsegs (w_H W) mem2 E ps_Bx (v + 16) 8 (v + 16) 8 HRA UB ltac:(lia) ltac:(lia)).
  - intros x Hx. cbn [she_m she_lo she_hi] in Hx.
    rewrite (U_atom E 19 v ltac:(rewrite <- E19; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia)) in Hx.
    rewrite UB. unfold SHADOW_OFF in *. lia. }
fsw_aj_run_to_tokU pv_tbl_ok HS HJ HARU SHOK fs_Bspan 0x83318.
{ cbn [ss_mem pq_st]. eapply awr_ok_cons_gen with (k := 19%nat) (b := v); [reflexivity | exact E19 | | apply awr_ok_nil].
  intros x Hx. cbn [YP09.r_wlo YP09.r_whi pq_v_region] in Hx. apply HAWR. unfold in_zr. cbn [fst snd]. lia. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
  assert (KEEP : forall x : word, ~ (v + 16 <= bv_unsigned x < v + 24) ->
    mrestrict (w_H W) (ms_mem msF) x = mrestrict (w_H W) mem2 x) end.
{ intros x Hx.
  rewrite (pv_frame_P _ _ _ _ (fun y => v + 16 <= y < v + 24) HFr
    ltac:(intros y Hy; cbn [ss_mem pq_st] in Hy; apply pv_wrange_cases in Hy; destruct Hy as [Hy|Hy];
          [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pq_v_region] in Hy; rewrite E19 in Hy; lia
           | exfalso; exact (pv_wrange_nil _ _ Hy)]) x Hx).
  reflexivity. }
lazymatch type of HS with st_ok _ ?Ey _ _ => set (E1 := Ey) in * end.
assert (F19 : bv_unsigned (ew E1 19) = v) by (subst E1; pv_ewo; exact E19).
assert (F10 : bv_unsigned (ew E1 10) = a) by (subst E1; pv_ewo; exact E10).
pv_reg HS (w_H W) (21%bv : bv 5) H21.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS eq_refl) as Hshape.
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 ?pc) _ _ =>
  let pc' := eval vm_compute in pc in change pc with pc' in Hshape end.
pv_region HS 0%nat RV. cbn [ms_mem restrict] in RV.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
  assert (Vstr : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (v + 16) 8 a) end.
{ exact (fsw_field _ _ 19 v _ 16 24 16 24 16 8 (SOff 10 0) a RV F19 ltac:(left; reflexivity)
    ltac:(rewrite fsw_SOff0, <- F10; symmetry; apply Z_to_bv_bv_unsigned) ltac:(cbn; lia) ltac:(cbn; lia)). }
pv_reg HS (w_H W) (8%bv : bv 5) K8. pv_reg HS (w_H W) (9%bv : bv 5) K9. pv_reg HS (w_H W) (18%bv : bv 5) K18.
pv_reg HS (w_H W) (20%bv : bv 5) K20. pv_reg HS (w_H W) (23%bv : bv 5) K23.
pv_reg HS (w_H W) (24%bv : bv 5) K24. pv_reg HS (w_H W) (26%bv : bv 5) K26.
pv_reg HS (w_H W) (3%bv : bv 5) K3. pv_reg HS (w_H W) (4%bv : bv 5) K4.
apply (K _ _);
  [exact Hshape | rewrite H21; apply pv_denot_lit; lia
   | rewrite K8 | rewrite K9 | rewrite K18 | rewrite K20 | rewrite K23 | rewrite K24 | rewrite K26
   | rewrite K3 | rewrite K4
   | exact Vstr | exact HJ | exact HARU | exact KEEP];
  rewrite fsw_SOff0; subst E1; pv_ewo; subst E;
  first [ exact (ew_Ereg_nat regs fs_extraT 8 8%bv eq_refl) | exact (ew_Ereg_nat regs fs_extraT 9 9%bv eq_refl)
        | exact (ew_Ereg_nat regs fs_extraT 18 18%bv eq_refl)
        | exact (ew_Ereg_nat regs fs_extraT 20 20%bv eq_refl) | exact (ew_Ereg_nat regs fs_extraT 23 23%bv eq_refl)
        | exact (ew_Ereg_nat regs fs_extraT 24 24%bv eq_refl) | exact (ew_Ereg_nat regs fs_extraT 26 26%bv eq_refl)
        | exact (ew_Ereg_nat regs fs_extraT 3 3%bv eq_refl) | exact (ew_Ereg_nat regs fs_extraT 4 4%bv eq_refl) ].
Qed.
End SB2.
(* the object arm after the call, 0x832f8 -> the epilogue 0x83318: `j 0x1c` to 0x83314, `mv s5, a0` (the callee's 0).
   No memory read or written, no shadow check. *)
Definition po_st : sstate := mkSS 0x832f8 sr_atoms [] None (mkFacts [] [] []).

Section OB. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Lemma pv_obj1 : forall STK ot FP ly0 S0 U0 (W0 : world tfibsegs) mem0 md0 kk ly S2 U (W : world tfibsegs) regs mem2 md2
  pos res (Q : world tfibsegs -> config -> Prop),
  YK11.getr regs 10%bv = Z_to_bv 64 res -> 0 <= res < 2 ^ 64 ->
  ajournal tfibsegs B STK ot FP ly0 S0 W0 (unpoison U0 mem0) md0 [(0, pos)] ly S2 W (unpoison U mem2) md2 kk ->
  ARU tfibsegs B ly S2 U W mem2 md2 ->
  (forall ms' mdx',
     ms' = mkst (ms_regs ms') (Z_to_bv 64 0x83318) (ms_mem ms') (seg_rom tfibsegs) ->
     YK11.getr (ms_regs ms') 21%bv = Z_to_bv 64 res ->
     (* every callee-saved register but s5, which this segment sets *)
     YK11.getr (ms_regs ms') 3%bv = YK11.getr regs 3%bv ->
     YK11.getr (ms_regs ms') 4%bv = YK11.getr regs 4%bv ->
     YK11.getr (ms_regs ms') 8%bv = YK11.getr regs 8%bv ->
     YK11.getr (ms_regs ms') 9%bv = YK11.getr regs 9%bv ->
     YK11.getr (ms_regs ms') 18%bv = YK11.getr regs 18%bv ->
     YK11.getr (ms_regs ms') 19%bv = YK11.getr regs 19%bv ->
     YK11.getr (ms_regs ms') 20%bv = YK11.getr regs 20%bv ->
     YK11.getr (ms_regs ms') 23%bv = YK11.getr regs 23%bv ->
     YK11.getr (ms_regs ms') 24%bv = YK11.getr regs 24%bv ->
     YK11.getr (ms_regs ms') 26%bv = YK11.getr regs 26%bv ->
     ajournal tfibsegs B STK ot FP ly0 S0 W0 (unpoison U0 mem0) md0 [(0, pos)] ly S2 W (unpoison U (ms_mem ms')) mdx' kk ->
     ARU tfibsegs B ly S2 U W (ms_mem ms') mdx' ->
     (forall x : word, mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) mem2 x) ->
     SRr tfibsegs W (mkCfg ms' mdx') Q) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 0x832f8) mem2 (seg_rom tfibsegs)) md2) Q.
Proof.
intros STK ot FP ly0 S0 U0 W0 mem0 md0 kk ly S2 U W regs mem2 md2 pos res Q R10 Hres HJ HARU K.
pose proof asan_consts as (C1 & _).
assert (HS : st_ok tfibsegs (Ereg regs fs_extraT) po_st
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x832f8) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold po_st. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn. exact I.
  - cbn. repeat split. }
set (E := Ereg regs fs_extraT) in HS.
assert (E10 : ew E 10 = Z_to_bv 64 res)
  by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 10 10%bv eq_refl); exact R10).
fsw_aj_run_toU pv_tbl_ok HS HJ HARU 0x83318.
{ cbn [ss_mem po_st]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
  assert (KEEP : forall x : word, mrestrict (w_H W) (ms_mem msF) x = mrestrict (w_H W) mem2 x) end.
{ intros x.
  rewrite (pv_frame_P _ _ _ _ (fun _ => False) HFr
    ltac:(intros a Ha; cbn [ss_mem po_st] in Ha; exact (pv_wrange_nil _ _ Ha)) x ltac:(intros [])).
  reflexivity. }
lazymatch type of HS with st_ok _ ?Ey _ _ => set (E1 := Ey) in * end.
assert (F10 : ew E1 10 = Z_to_bv 64 res) by (subst E1; pv_ewo; exact E10).
pv_reg HS (w_H W) (21%bv : bv 5) H21.
pv_reg HS (w_H W) (3%bv : bv 5) K3. pv_reg HS (w_H W) (4%bv : bv 5) K4.
pv_reg HS (w_H W) (8%bv : bv 5) K8. pv_reg HS (w_H W) (9%bv : bv 5) K9. pv_reg HS (w_H W) (18%bv : bv 5) K18.
pv_reg HS (w_H W) (19%bv : bv 5) K19. pv_reg HS (w_H W) (20%bv : bv 5) K20. pv_reg HS (w_H W) (23%bv : bv 5) K23.
pv_reg HS (w_H W) (24%bv : bv 5) K24. pv_reg HS (w_H W) (26%bv : bv 5) K26.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS eq_refl) as Hshape.
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 ?pc) _ _ =>
  let pc' := eval vm_compute in pc in change pc with pc' in Hshape end.
apply (K _ _);
  [exact Hshape | rewrite H21, fsw_SOff0; exact F10
   | rewrite K3 | rewrite K4 | rewrite K8 | rewrite K9 | rewrite K18 | rewrite K19 | rewrite K20 | rewrite K23
   | rewrite K24 | rewrite K26
   | exact HJ | exact HARU | exact KEEP];
  rewrite fsw_SOff0; subst E1; pv_ewo; subst E;
  first [ exact (ew_Ereg_nat regs fs_extraT 3 3%bv eq_refl) | exact (ew_Ereg_nat regs fs_extraT 4 4%bv eq_refl)
        | exact (ew_Ereg_nat regs fs_extraT 8 8%bv eq_refl) | exact (ew_Ereg_nat regs fs_extraT 9 9%bv eq_refl)
        | exact (ew_Ereg_nat regs fs_extraT 18 18%bv eq_refl) | exact (ew_Ereg_nat regs fs_extraT 19 19%bv eq_refl)
        | exact (ew_Ereg_nat regs fs_extraT 20 20%bv eq_refl) | exact (ew_Ereg_nat regs fs_extraT 23 23%bv eq_refl)
        | exact (ew_Ereg_nat regs fs_extraT 24 24%bv eq_refl) | exact (ew_Ereg_nat regs fs_extraT 26 26%bv eq_refl) ].
Qed.
End OB.
Section FH. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* one byte read off a memory as a val_mem of width 1 *)
Lemma pv_val1 : forall (m : word -> option byte) a (b : byte), mbyte tfibsegs m a = Some b ->
  val_mem tfibsegs m a 1 (bv_unsigned b).
Proof.
intros m a b H k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, H. f_equal.
pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
unfold YO0f.le_byte. cbn -[Z.modulo Z.shiftr Z.pow]. rewrite ?Z.shiftr_0_r, ?Z.mod_small by lia.
symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hr.
Qed.
(* the grammar's white-space test is the loop's four bytes *)
Lemma pv_ws_wsb : forall c, PjGrammar.ws c = true -> pv_wsb c.
Proof.
intros c H. unfold PjGrammar.ws in H. unfold pv_wsb.
repeat (apply orb_true_iff in H; destruct H as [H|H]); apply Z.eqb_eq in H; subst c; auto.
Qed.
(* the bytes of the text at in->p, read off pj_in_ok's `bytes_at text tb` and the split of rest_at *)
Lemma pv_text_of_tb : forall (tb : list byte) text len p d q (m : word -> option byte) bs rest,
  PjIn.pj_in_ok tfibsegs m q text len p d tb ->
  ReaderRes.rest_at tb text p = bs ++ rest ->
  pv_text m p bs.
Proof.
intros tb text len p d q m bs rest HIN Hsplit j Hj.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Hq0 & Hq64 & Ht0 & (Hp1 & Hp2) & Hend & _ & Hlen & _).
destruct HIN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbat & _).
assert (HLB : (length bs <= length (ReaderRes.rest_at tb text p))%nat)
  by (rewrite Hsplit, length_app; lia).
unfold ReaderRes.rest_at, ReaderRes.zb in HLB. rewrite length_map, length_skipn in HLB.
assert (Hjt : (Z.to_nat (p - text) + j < length tb)%nat) by lia.
assert (Hnth : nth j bs 0 = bv_unsigned (nth (Z.to_nat (p - text) + j) tb (Z_to_bv 8 0))).
{ assert (Hb : nth j (bs ++ rest) 0 = nth j bs 0) by (apply app_nth1; lia).
  rewrite <- Hb, <- Hsplit. unfold ReaderRes.rest_at, ReaderRes.zb.
  rewrite (nth_indep (map _ _) 0 (bv_unsigned (Z_to_bv 8 0)))
    by (rewrite length_map, length_skipn; lia).
  rewrite map_nth, nth_skipn. reflexivity. }
split.
- rewrite Hnth. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (p - text) + j) tb (Z_to_bv 8 0))) as Hr.
  change (bv_modulus 8) with 256 in Hr. lia.
- destruct Hbat as (_ & _ & Hb). pose proof (Hb (Nat.add (Z.to_nat (p - text)) j) Hjt) as Hx.
  rewrite (nth_error_nth' tb (Z_to_bv 8 0) Hjt) in Hx.
  replace (text + Z.of_nat (Nat.add (Z.to_nat (p - text)) j)) with (p + Z.of_nat j) in Hx
    by (rewrite Nat2Z.inj_add, Z2Nat.id by lia; lia).
  rewrite Hnth. apply (pv_val1 m (p + Z.of_nat j) (nth (Nat.add (Z.to_nat (p - text)) j) tb (Z_to_bv 8 0))).
  exact Hx.
Qed.
End FH.
Section TR. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* a byte at or above alloc_ceiling (the real stack and the frames above it) is no user-poisoned byte of U: a byte of U
   is a live block's shadow byte, which lies in [SHADOW_OFF, kHighMemBeg), below alloc_ceiling (ush_facts) *)
Lemma pv_unp_high : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> alloc_ceiling <= a < 2 ^ 64 ->
  unpoison U mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros ly S U W mem md a HARU Ha. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (in_ush U a) eqn:Eu.
- exfalso. pose proof (ush_facts tfibsegs B ly S U W mem md _ HARU Eu) as (_ & L1 & L2).
  unfold kHighMemBeg, SHADOW_OFF in *. lia.
- apply unpoison_out. rewrite (wz a ltac:(lia)). exact Eu.
Qed.
(* the stack bytes the walk's front does not write keep their value from the entry memory to the resume memory: the
   prologue's run writes only its own frame [sp - 160, sp) (pv_ss0's one write window) and the grant writes only its
   fake-stack window [sp1 - ESTACK, sp1) (acall_kept) *)
Lemma pv_front_keep : forall ly S ly2 S2 U (W : world tfibsegs) (mem m1 mem2 : word -> option byte) md1 md2 E slo shi lo hi
  a,
  frame_of E (ss_mem pv_ss0) (mrestrict (w_H W) mem) (mrestrict (w_H W) m1) ->
  (forall x, in_wrange E (ss_mem pv_ss0) x -> lo <= x < hi) ->
  acall_kept tfibsegs B ly S W (unpoison U m1) W (unpoison U mem2) slo shi (fun _ => False) ->
  ARU tfibsegs B ly S U W m1 md1 -> ARU tfibsegs B ly2 S2 U W mem2 md2 ->
  alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ (lo <= a < hi) ->
  mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs (mrestrict (w_H W) mem) a.
Proof.
intros ly S ly2 S2 U W mem m1 mem2 md1 md2 E slo shi lo hi a HFr Hwin (HK & _) HARU1 HARU2 Ha Hs Hl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hm1 : mbyte tfibsegs (mrestrict (w_H W) m1) a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ unfold mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite (wz a ltac:(lia)). intros Hin. exact (Hl (Hwin _ Hin)). }
assert (H1 : aview tfibsegs (w_H W) (unpoison U mem2) a = aview tfibsegs (w_H W) (unpoison U m1) a)
  by (apply HK; [lia | exact Hs]).
assert (Hunp : forall ly' S' (m : word -> option byte) md',
  ARU tfibsegs B ly' S' U W m md' ->
  mbyte tfibsegs (mrestrict (w_H W) (unpoison U m)) a = mbyte tfibsegs (mrestrict (w_H W) m) a).
{ intros ly' S' m md' HA. unfold mbyte, mrestrict.
  rewrite (pv_unp_high ly' S' U W m md' a HA ltac:(lia)). reflexivity. }
assert (Hm2 : mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs (mrestrict (w_H W) m1) a).
{ unfold aview in H1. rewrite (Hunp ly2 S2 mem2 md2 HARU2), (Hunp ly S m1 md1 HARU1) in H1.
  destruct (mbyte tfibsegs (mrestrict (w_H W) mem2) a) as [b2|] eqn:E2;
    destruct (mbyte tfibsegs (mrestrict (w_H W) m1) a) as [b1|] eqn:E1;
    cbn [option_map] in H1; try reflexivity; try discriminate.
  injection H1 as H1. f_equal. apply bv_eq. exact H1. }
rewrite Hm2, Hm1. reflexivity.
Qed.
End TR.
Section TR2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the unpoison step, shared by the three transports: a byte outside the shadow band is no user-poisoned byte of U *)
Lemma pv_unp_out : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44) ->
  unpoison U mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros ly S U W mem md a HARU Ha Hb. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (in_ush U a) eqn:Eu.
- exfalso. pose proof (ush_facts tfibsegs B ly S U W mem md _ HARU Eu) as (_ & L1 & L2).
  unfold kHighMemBeg, SHADOW_OFF in *. lia.
- apply unpoison_out. rewrite (wz a ltac:(lia)). exact Eu.
Qed.
(* an aview equality of two unpoisoned memories at a byte outside the band is an mbyte equality of the memories *)
Lemma pv_mb_of_aview : forall ly S ly2 S2 U (W : world tfibsegs) (m1 m2 : word -> option byte) md1 md2 a,
  ARU tfibsegs B ly S U W m1 md1 -> ARU tfibsegs B ly2 S2 U W m2 md2 ->
  0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44) ->
  aview tfibsegs (w_H W) (unpoison U m2) a = aview tfibsegs (w_H W) (unpoison U m1) a ->
  mbyte tfibsegs (mrestrict (w_H W) m2) a = mbyte tfibsegs (mrestrict (w_H W) m1) a.
Proof.
intros ly S ly2 S2 U W m1 m2 md1 md2 a HARU1 HARU2 Ha Hb H1.
assert (Hunp : forall ly' S' (m : word -> option byte) md',
  ARU tfibsegs B ly' S' U W m md' ->
  mbyte tfibsegs (mrestrict (w_H W) (unpoison U m)) a = mbyte tfibsegs (mrestrict (w_H W) m) a).
{ intros ly' S' m md' HA. unfold mbyte, mrestrict.
  rewrite (pv_unp_out ly' S' U W m md' a HA Ha Hb). reflexivity. }
unfold aview in H1. rewrite (Hunp ly2 S2 m2 md2 HARU2), (Hunp ly S m1 md1 HARU1) in H1.
destruct (mbyte tfibsegs (mrestrict (w_H W) m2) a) as [b2|] eqn:E2;
  destruct (mbyte tfibsegs (mrestrict (w_H W) m1) a) as [b1|] eqn:E1;
  cbn [option_map] in H1; try reflexivity; try discriminate.
injection H1 as H1. f_equal. apply bv_eq. exact H1.
Qed.
(* a live block's body byte: acall_kept's block clause, then the prologue's frame (below the stack) *)
Lemma pv_front_keep_blk : forall ly S ly2 S2 U (W : world tfibsegs) (mem m1 mem2 : word -> option byte) md md1 md2 E
    slo shi lo hi b n i,
  AR tfibsegs B ly S W (unpoison U m1) md ->
  frame_of E (ss_mem pv_ss0) (mrestrict (w_H W) mem) (mrestrict (w_H W) m1) ->
  (forall x, in_wrange E (ss_mem pv_ss0) x -> lo <= x < hi) -> alloc_ceiling <= lo ->
  acall_kept tfibsegs B ly S W (unpoison U m1) W (unpoison U mem2) slo shi (fun _ => False) ->
  ARU tfibsegs B ly S U W m1 md1 -> ARU tfibsegs B ly2 S2 U W mem2 md2 ->
  In (b, n) (ablocks B ly S) -> 0 <= i < req_size n ->
  mbyte tfibsegs (mrestrict (w_H W) mem2) (b + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (b + i).
Proof.
intros ly S ly2 S2 U W mem m1 mem2 md md1 md2 E slo shi lo hi b n i HAR HFr Hwin Hlo (_ & HKb & _) HARU1 HARU2 Hin Hi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (fsw_ablock_low B ly S W (unpoison U m1) md b n HAR Hin) as (Hb4096 & Hbceil & Hreq).
pose proof (fsw_ablock_off_shadow B ly S W (unpoison U m1) md b n HAR Hin (b + i) ltac:(lia)) as Hoff.
assert (Hm1 : mbyte tfibsegs (mrestrict (w_H W) m1) (b + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (b + i)).
{ unfold mbyte. rewrite (HFr (Z_to_bv 64 (b + i))); [reflexivity|].
  rewrite (wz (b + i) ltac:(lia)). intros Hw. pose proof (Hwin _ Hw). lia. }
rewrite (pv_mb_of_aview ly S ly2 S2 U W m1 mem2 md1 md2 (b + i) HARU1 HARU2 ltac:(lia) Hoff
  (HKb b n i Hin Hi ltac:(intros []))).
exact Hm1.
Qed.
(* fs.asan's last PT_LOAD, [0xa1000, 0x5fd000), holds fuzz/alloc.c's statics (MEASURED: tfibsegs's fourth segment);
   same statement as FSW_parse_value_calls.pvc_img, restated here because that file imports this one *)
Lemma pv_img : forall a, 659456 <= a < 6279168 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img.
assert (H : option_map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) (nth_error tfibsegs 3)
  = Some (659456, 5619712)) by (vm_compute; reflexivity).
destruct (nth_error tfibsegs 3) as [sg|] eqn:E; [|discriminate H].
exists sg. split; [exact (nth_error_In _ _ E)|].
cbn [option_map] in H. injection H as H1 H2. lia.
Qed.
(* an image byte of the fuzz statics (FS_PSTAT_FP: g_live, g_peak, g_count, g_fail_at): acall_kept's image clause. The
   asan runtime owns none of them and none is errno - fs_img_facts, through FSH_Gen.fs_pstat_not_owned. *)
Lemma pv_front_keep_img : forall ly S ly2 S2 U (W : world tfibsegs) (mem m1 mem2 : word -> option byte) md1 md2 E
    slo shi lo hi a,
  fs_img_facts tfibsegs B ->
  frame_of E (ss_mem pv_ss0) (mrestrict (w_H W) mem) (mrestrict (w_H W) m1) ->
  (forall x, in_wrange E (ss_mem pv_ss0) x -> lo <= x < hi) -> alloc_ceiling <= lo ->
  acall_kept tfibsegs B ly S W (unpoison U m1) W (unpoison U mem2) slo shi (fun _ => False) ->
  ARU tfibsegs B ly S U W m1 md1 -> ARU tfibsegs B ly2 S2 U W mem2 md2 ->
  inFP FS_PSTAT_FP a -> 659456 <= a < 6279168 ->
  mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs (mrestrict (w_H W) mem) a.
Proof.
intros ly S ly2 S2 U W mem m1 mem2 md1 md2 E slo shi lo hi a IMG HFr Hwin Hlo (_ & _ & HKi & _) HARU1 HARU2 Hfp Ha.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof IMG as (Hpst & _).
destruct (Hpst a Hfp) as (Hno & Herr).
assert (Hm1 : mbyte tfibsegs (mrestrict (w_H W) m1) a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ unfold mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite (wz a ltac:(unfold SHADOW_OFF in *; lia)). intros Hw. pose proof (Hwin _ Hw). lia. }
rewrite (pv_mb_of_aview ly S ly2 S2 U W m1 mem2 md1 md2 a HARU1 HARU2
  ltac:(unfold SHADOW_OFF in *; lia) ltac:(unfold SHADOW_OFF; lia)
  (HKi a (pv_img a Ha) Hno Herr)).
exact Hm1.
Qed.

End TR2.
Section ARM. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* an off-image byte: an mbyte equality is a pointwise one *)
Lemma pv_pw_of_mb : forall (m m' : word -> option byte) a, 0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a ->
  mbyte tfibsegs m' a = mbyte tfibsegs m a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
intros m m' a Ha Hn H. unfold mbyte in H. rewrite (seg_rom_none tfibsegs a Ha Hn) in H.
destruct (m' (Z_to_bv 64 a)), (m (Z_to_bv 64 a)); congruence.
Qed.

(* an old frame's shadow byte is no user-poisoned byte: U's ranges are block heads, apart from every frame *)
Lemma pv_unp_frame_shadow : forall ly S U (W : world tfibsegs) mem md cid pos a,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U -> In (cid, pos) (frames S) ->
  in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8) ->
  unpoison U mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros ly S U W mem md cid pos a HARU HH Hin Ha. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
destruct (al_frames _ _ LAWS ly S W (unpoison U mem) md cid pos HAR Hin) as (HF32 & HFapp & _ & _).
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md cid pos HAR Hin) as (HF4096 & HFc & _).
unfold in_zr, shadow_addr in Ha. cbn [fst snd] in Ha.
destruct (in_ush U a) eqn:Eu.
- exfalso. unfold in_ush in Eu. apply existsb_exists in Eu. destruct Eu as (r & Hr & Hrg).
  apply andb_true_iff in Hrg. destruct Hrg as (H1 & H2). apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  destruct (HH r Hr) as (Hn16 & m & Hb & Hreq). destruct r as (b & n). cbn [fst snd] in *. subst n.
  destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U mem) md b m HAR Hb) as (Hb16 & Hb4096 & Hbc & _).
  pose proof (sep_block_frame tfibsegs B LAWS ly S W (unpoison U mem) md b m cid pos HAR Hb Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold shadow_addr in H1, H2.
  pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
  set (F := frame_addr ly cid pos) in *. set (fb := fs_frame_bytes cid) in *.
  assert (EF : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 32 ltac:(lia)); pose proof (Z.div_mod F 8 ltac:(lia)); lia).
  assert (Eb : b = 8 * (b / 8)) by (pose proof (Z.div_mod b 16 ltac:(lia)); pose proof (Z.div_mod b 8 ltac:(lia)); lia).
  assert (Efb : 8 * (fb / 8) <= fb) by (apply Z.mul_div_le; lia).
  change (16 / 8) with 2 in H2. lia.
- apply unpoison_out. rewrite (wz a ltac:(unfold SHADOW_OFF in *; lia)). exact Eu.
Qed.

(* THE FRONT'S POINTWISE KEEP: a byte that is a stack byte above the grant's window and the prologue's frame, a live
   block's byte or an old frame's byte or shadow byte, and is not in->p's word, is the same at the arm memory ma as at
   the entry memory mem. The five steps: the prologue (frame_of, its own frame [s - 160, s)), the grant (acall_kept),
   segment 1 (pv_wr), the loop and the dispatch (in->p's word). *)
Lemma pv_arm_pw : forall ly S S2 U (W : world tfibsegs) (mem m1 mem2 mh mdl ma : word -> option byte) md1 md2 E
    pos s sp1 q a,
  AR tfibsegs B ly S2 W (unpoison U mem2) md2 ->
  frames S2 = (0, pos) :: frames S -> ablocks B ly S2 = ablocks B ly S -> FSupoisonU.fs_heads B ly S U ->
  frame_of E (ss_mem pv_ss0) (mrestrict (w_H W) mem) (mrestrict (w_H W) m1) ->
  (forall x, in_wrange E (ss_mem pv_ss0) x -> s - 160 <= x < s) ->
  acall_kept tfibsegs B ly S W (unpoison U m1) W (unpoison U mem2) (sp1 - ESTACK) sp1 (fun _ => False) ->
  ARU tfibsegs B ly S U W m1 md1 -> ARU tfibsegs B ly S2 U W mem2 md2 ->
  (forall x, ~ pv_wr (frame_addr ly 0 pos) q s sp1 (bv_unsigned x) ->
     mrestrict (w_H W) mh x = mrestrict (w_H W) mem2 x) ->
  (forall x, ~ (q <= bv_unsigned x < q + 8) -> mrestrict (w_H W) mdl x = mrestrict (w_H W) mh x) ->
  (forall x, ~ (q <= bv_unsigned x < q + 8) -> mrestrict (w_H W) ma x = mrestrict (w_H W) mdl x) ->
  alloc_ceiling <= sp1 -> sp1 + 160 <= s -> s <= q -> q + 24 <= 2 ^ 64 ->
  0 <= a < 2 ^ 64 -> ~ (q <= a < q + 8) ->
  (alloc_ceiling <= a /\ ~ (sp1 - ESTACK <= a < s)) \/
  (exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/
  (exists cid pos', In (cid, pos') (frames S) /\
     (in_zr a (frame_rng ly (cid, pos')) \/ in_zr a (shadow_addr (frame_addr ly cid pos'), fs_frame_bytes cid / 8))) ->
  mrestrict (w_H W) ma (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a).
Proof.
intros ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q a HAR2 HFRS HBL HH HFr HWIN0 HK HARU1 HARU2 KEEPh KEEPd
  KEEPa Hsp1 Hs Hsq Hq64 Ha Haq Hcls.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (HES : 0 <= ESTACK) by (unfold ESTACK; lia).
assert (ESH : SHADOW_OFF = 2147450880) by reflexivity.
assert (Hin0 : In (0, pos) (frames S2)) by (rewrite HFRS; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin0) as (HF4096 & HFc & _).
change (fs_frame_bytes 0) with 64 in HF4096, HFc.
pose proof (ARU_AR tfibsegs B ly S U W m1 md1 HARU1) as HAR1.
assert (Wa : bv_unsigned (Z_to_bv 64 a) = a) by (apply wz; lia).
(* the dispatch, the loop, segment 1 *)
rewrite (KEEPa (Z_to_bv 64 a) ltac:(rewrite Wa; exact Haq)), (KEEPd (Z_to_bv 64 a) ltac:(rewrite Wa; exact Haq)).
rewrite (KEEPh (Z_to_bv 64 a)).
2: { rewrite Wa. unfold pv_wr.
     destruct Hcls as [(Hc & Hns) | [(b & n & Hb & Hbn) | (cid & pos' & Hf & Hfr)]].
     - lia.
     - destruct (al_blocks tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 b n HAR2 ltac:(rewrite HBL; exact Hb))
         as (_ & Hb4096 & Hbc & Happ & _).
       pose proof (sep_block_frame tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 b n 0 pos HAR2
         ltac:(rewrite HBL; exact Hb) Hin0) as Hd.
       unfold zdisjoint in Hd. unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg in Happ. cbn [fst snd] in Hd.
       change (fs_frame_bytes 0) with 64 in Hd.
       assert (HF8 : 0 <= frame_addr ly 0 pos / 8 <= 2 ^ 44)
         by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
       lia.
     - assert (Hf2 : In (cid, pos') (frames S2)) by (rewrite HFRS; right; exact Hf).
       destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 cid pos' HAR2 Hf2) as (Hf4096 & Hfc & _).
       destruct (al_frames _ _ LAWS ly S2 W (unpoison U mem2) md2 cid pos' HAR2 Hf2) as (Hf32 & Hfapp & _ & _).
       destruct (al_frames _ _ LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin0) as (H032 & H0app & _ & _).
       destruct (in_split _ _ Hf) as (l2 & l3 & El).
       pose proof (sep_frames_pos tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 (0, pos) (cid, pos') [] l2 l3 HAR2
         ltac:(rewrite HFRS, El; reflexivity)) as Hd.
       unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd.
       pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
       unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg in Hfapp, H0app.
       unfold in_zr, frame_rng, shadow_addr in Hfr. cbn [fst snd] in Hfr.
       set (F := frame_addr ly 0 pos) in *. set (F' := frame_addr ly cid pos') in *.
       set (fb := fs_frame_bytes cid) in *.
       assert (EF : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 32 ltac:(lia)); pose proof (Z.div_mod F 8 ltac:(lia)); lia).
       assert (EF' : F' = 8 * (F' / 8))
         by (pose proof (Z.div_mod F' 32 ltac:(lia)); pose proof (Z.div_mod F' 8 ltac:(lia)); lia).
       assert (Efb : 8 * (fb / 8) <= fb) by (apply Z.mul_div_le; lia).
       assert (HF8 : 0 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
       change (fs_frame_bytes 0) with 64 in H0app. lia. }
(* the grant, then the prologue *)
transitivity (mrestrict (w_H W) m1 (Z_to_bv 64 a)).
- destruct HK as (HKs & HKb & _ & HKf & _).
  destruct Hcls as [(Hc & Hns) | [(b & n & Hb & Hbn) | (cid & pos' & Hf & Hfr)]].
  + (* a stack byte *)
    assert (Hnimg : ~ in_img tfibsegs a) by (intros Hi; pose proof (fs_segs_img a Hi); unfold FS_IMG_END in *; lia).
    apply (pv_pw_of_mb (mrestrict (w_H W) m1) (mrestrict (w_H W) mem2) a Ha Hnimg).
    apply (pv_mb_of_aview B ly S ly S2 U W m1 mem2 md1 md2 a HARU1 HARU2 Ha ltac:(lia)).
    apply HKs; lia.
  + (* a block byte *)
    destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U m1) md1 b n HAR1 Hb) as (_ & Hb4096 & Hbc & Happ & _).
    pose proof (fsw_ablock_off_shadow B ly S W (unpoison U m1) md1 b n HAR1 Hb a Hbn) as Hoff.
    pose proof (blk_img tfibsegs B LAWS ly S W (unpoison U m1) md1 b n a HAR1 Hb Hbn) as Hnimg.
    apply (pv_pw_of_mb (mrestrict (w_H W) m1) (mrestrict (w_H W) mem2) a Ha Hnimg).
    apply (pv_mb_of_aview B ly S ly S2 U W m1 mem2 md1 md2 a HARU1 HARU2 Ha Hoff).
    replace a with (b + (a - b)) by lia. apply (HKb b n (a - b) Hb ltac:(lia)). intros [].
  + (* an old frame's byte or shadow byte *)
    pose proof (HKf cid pos' a Hf Hfr ltac:(intros [])) as Hv.
    assert (Hf2 : In (cid, pos') (frames S2)) by (rewrite HFRS; right; exact Hf).
    destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U m1) md1 cid pos' HAR1 Hf) as (Hf4096 & Hfc & _).
    destruct (al_frames _ _ LAWS ly S W (unpoison U m1) md1 cid pos' HAR1 Hf) as (Hf32 & Hfapp & _ & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
    unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg in Hfapp.
    destruct Hfr as [Hfr | Hfr].
    * assert (Hnimg : ~ in_img tfibsegs a)
        by (apply (frm_img tfibsegs B LAWS ly S W (unpoison U m1) md1 cid pos' a HAR1 Hf);
            unfold in_zr, frame_rng in Hfr; cbn [fst snd] in Hfr; lia).
      apply (pv_pw_of_mb (mrestrict (w_H W) m1) (mrestrict (w_H W) mem2) a Ha Hnimg).
      unfold in_zr, frame_rng in Hfr. cbn [fst snd] in Hfr.
      exact (pv_mb_of_aview B ly S ly S2 U W m1 mem2 md1 md2 a HARU1 HARU2 Ha ltac:(lia) Hv).
    * assert (HH2 : FSupoisonU.fs_heads B ly S2 U).
      { intros r Hr. destruct (HH r Hr) as (H1 & m' & H2 & H3). split; [exact H1|]. exists m'. rewrite HBL. auto. }
      pose proof (pv_unp_frame_shadow ly S2 U W mem2 md2 cid pos' a HARU2 HH2 Hf2 Hfr) as U2.
      pose proof (pv_unp_frame_shadow ly S U W m1 md1 cid pos' a HARU1 HH Hf Hfr) as U1.
      unfold in_zr, shadow_addr in Hfr. cbn [fst snd] in Hfr.
      assert (Hnimg : ~ in_img tfibsegs a).
      { intros Hi. pose proof (fs_segs_img a Hi). unfold FS_IMG_END in *. lia. }
      apply (pv_pw_of_mb (mrestrict (w_H W) m1) (mrestrict (w_H W) mem2) a Ha Hnimg).
      unfold aview in Hv. unfold mbyte, mrestrict in Hv |- *. rewrite U1, U2 in Hv.
      destruct (w_H W (Z_to_bv 64 a)); [reflexivity|].
      destruct (mem2 (Z_to_bv 64 a)) as [b2|] eqn:E2; destruct (m1 (Z_to_bv 64 a)) as [b1|] eqn:E1;
        destruct (seg_rom tfibsegs (Z_to_bv 64 a)) as [br|] eqn:ER; cbn [option_map] in Hv;
        try reflexivity; try discriminate; injection Hv as Hv; f_equal; apply bv_eq; exact Hv.
- apply (HFr (Z_to_bv 64 a)). rewrite Wa. intros Hin. pose proof (HWIN0 _ Hin).
  destruct Hcls as [(Hc & Hns) | [(b & n & Hb & Hbn) | (cid & pos' & Hf & Hfr)]].
  + lia.
  + destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U m1) md1 b n HAR1 Hb) as (_ & Hb4096 & Hbc & _). lia.
  + destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U m1) md1 cid pos' HAR1 Hf) as (Hf4096 & Hfc & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
    unfold in_zr, frame_rng, shadow_addr in Hfr. cbn [fst snd] in Hfr.
    assert (Hf8 : 8 * (frame_addr ly cid pos' / 8) <= frame_addr ly cid pos') by (apply Z.mul_div_le; lia).
    assert (Hfb8 : 8 * (fs_frame_bytes cid / 8) <= fs_frame_bytes cid) by (apply Z.mul_div_le; lia).
    lia.
Qed.

Lemma pv_pstat_rng : forall a, inFP FS_PSTAT_FP a -> 659456 <= a < 6279168.
Proof.
intros a (r & Hin & Hr). unfold FS_PSTAT_FP in Hin. cbn [In] in Hin.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.

(* THE FRONT'S STATICS KEEP: fuzz/alloc.c's four statics read the same at the arm memory as at the entry memory *)
Lemma pv_arm_img : forall ly S S2 U (W : world tfibsegs) (mem m1 mem2 mh mdl ma : word -> option byte) md1 md2 E
    pos s sp1 q a,
  fs_img_facts tfibsegs B ->
  AR tfibsegs B ly S2 W (unpoison U mem2) md2 -> frames S2 = (0, pos) :: frames S ->
  frame_of E (ss_mem pv_ss0) (mrestrict (w_H W) mem) (mrestrict (w_H W) m1) ->
  (forall x, in_wrange E (ss_mem pv_ss0) x -> s - 160 <= x < s) ->
  acall_kept tfibsegs B ly S W (unpoison U m1) W (unpoison U mem2) (sp1 - ESTACK) sp1 (fun _ => False) ->
  ARU tfibsegs B ly S U W m1 md1 -> ARU tfibsegs B ly S2 U W mem2 md2 ->
  (forall x, ~ pv_wr (frame_addr ly 0 pos) q s sp1 (bv_unsigned x) ->
     mrestrict (w_H W) mh x = mrestrict (w_H W) mem2 x) ->
  (forall x, ~ (q <= bv_unsigned x < q + 8) -> mrestrict (w_H W) mdl x = mrestrict (w_H W) mh x) ->
  (forall x, ~ (q <= bv_unsigned x < q + 8) -> mrestrict (w_H W) ma x = mrestrict (w_H W) mdl x) ->
  alloc_ceiling <= sp1 -> sp1 + 160 <= s -> s <= q ->
  inFP FS_PSTAT_FP a ->
  mbyte tfibsegs (mrestrict (w_H W) ma) a = mbyte tfibsegs (mrestrict (w_H W) mem) a.
Proof.
intros ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q a IMG HAR2 HFRS HFr HWIN0 HK HARU1 HARU2 KEEPh KEEPd
  KEEPa Hsp1 Hs Hsq Hfp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (pv_pstat_rng a Hfp) as Ha.
assert (Wa : bv_unsigned (Z_to_bv 64 a) = a) by (apply wz; lia).
assert (Hin0 : In (0, pos) (frames S2)) by (rewrite HFRS; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin0) as (HF4096 & HFc & _).
change (fs_frame_bytes 0) with 64 in HF4096, HFc.
assert (HnF : ~ (frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64)).
{ intros HF. apply (frm_img tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 0 pos a HAR2 Hin0 HF). exact (pv_img a Ha). }
assert (HF8 : 0 <= frame_addr ly 0 pos / 8) by (apply Z.div_pos; lia).
assert (ESH : SHADOW_OFF = 2147450880) by reflexivity.
assert (HES : 0 <= ESTACK) by (unfold ESTACK; lia).
unfold mbyte.
rewrite (KEEPa (Z_to_bv 64 a) ltac:(rewrite Wa; lia)), (KEEPd (Z_to_bv 64 a) ltac:(rewrite Wa; lia)).
rewrite (KEEPh (Z_to_bv 64 a) ltac:(rewrite Wa; unfold pv_wr; lia)).
fold (mbyte tfibsegs (mrestrict (w_H W) mem2) a). fold (mbyte tfibsegs (mrestrict (w_H W) mem) a).
exact (pv_front_keep_img B ly S ly S2 U W mem m1 mem2 md1 md2 E (sp1 - ESTACK) sp1 (s - 160) s a IMG HFr HWIN0
  ltac:(lia) HK HARU1 HARU2 Hfp Ha).
Qed.
End ARM.
Section PW. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* a pointwise memory equality gives the readings the specs use; the bytes_at / stk / u64 / hdr / cstr transports are
   PjStruct's own (pj_bytes_eq, pj_stk_eq, pj_u64_eq, pj_hdr_eq, pj_cstr_eq), in the same `forall x : word` shape *)
Lemma pv_mb_pw : forall (m m' : word -> option byte) a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  mbyte tfibsegs m' a = mbyte tfibsegs m a.
Proof. intros m m' a H. unfold mbyte. rewrite H. reflexivity. Qed.
Lemma pv_wr_pw : forall (m m' : word -> option byte) a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  wview tfibsegs m' (Z_to_bv 64 a) = wview tfibsegs m (Z_to_bv 64 a).
Proof. intros m m' a H. unfold wview. rewrite H. reflexivity. Qed.
Lemma pv_val_eq : forall (m m' : word -> option byte) a (n : nat) v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem tfibsegs m a n v ->
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat n -> m' x = m x) -> val_mem tfibsegs m' a n v.
Proof.
intros m m' a n v Ha Hb Hv E k Hk.
rewrite (pv_mb_pw m m' (a + Z.of_nat k) ltac:(apply E; rewrite wz; lia)). exact (Hv k Hk).
Qed.
Lemma pv_writable_eq : forall (m m' : word -> option byte) a, 0 <= a < 2 ^ 64 ->
  (forall x : word, a <= bv_unsigned x < a + 1 -> m' x = m x) ->
  writable_at tfibsegs m a -> writable_at tfibsegs m' a.
Proof.
intros m m' a Ha E Hw. unfold writable_at in Hw |- *.
rewrite (pv_wr_pw m m' a ltac:(apply E; rewrite wz; lia)). exact Hw.
Qed.
Lemma pv_wrat_eq : forall (m m' : word -> option byte) a n, Mem.wr_at tfibsegs m a n ->
  (forall x : word, a <= bv_unsigned x < a + n -> m' x = m x) -> Mem.wr_at tfibsegs m' a n.
Proof.
intros m m' a n (Ha & Hb & Hv) E. split; [exact Ha|]. split; [exact Hb|].
intros i Hi. unfold Mem.wa. rewrite (pv_wr_pw m m' (a + i) ltac:(apply E; rewrite wz; lia)). exact (Hv i Hi).
Qed.
End PW.
Section AD. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the walk's keeps, bundled: the three stage keeps and the two call-level ones, as pv_arm_pw / pv_arm_img take them *)
Definition pv_keeps (ly : alayout) (S S2 : astate) (U : list (Z * Z)) (W : world tfibsegs)
  (mem m1 mem2 mh mdl ma : word -> option byte) (md1 md2 : Model) (E : env) (pos s sp1 q : Z) : Prop :=
  frame_of E (ss_mem pv_ss0) (mrestrict (w_H W) mem) (mrestrict (w_H W) m1) /\
  (forall x, in_wrange E (ss_mem pv_ss0) x -> s - 160 <= x < s) /\
  acall_kept tfibsegs B ly S W (unpoison U m1) W (unpoison U mem2) (sp1 - ESTACK) sp1 (fun _ => False) /\
  ARU tfibsegs B ly S U W m1 md1 /\ ARU tfibsegs B ly S2 U W mem2 md2 /\
  (forall x, ~ pv_wr (frame_addr ly 0 pos) q s sp1 (bv_unsigned x) ->
     mrestrict (w_H W) mh x = mrestrict (w_H W) mem2 x) /\
  (forall x, ~ (q <= bv_unsigned x < q + 8) -> mrestrict (w_H W) mdl x = mrestrict (w_H W) mh x) /\
  (forall x, ~ (q <= bv_unsigned x < q + 8) -> mrestrict (w_H W) ma x = mrestrict (w_H W) mdl x).

(* a stack byte above the grant's window, off in->p's word *)
Lemma pv_arm_stk : forall ly S S2 U (W : world tfibsegs) mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q a,
  AR tfibsegs B ly S2 W (unpoison U mem2) md2 ->
  frames S2 = (0, pos) :: frames S -> ablocks B ly S2 = ablocks B ly S -> FSupoisonU.fs_heads B ly S U ->
  pv_keeps ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q ->
  alloc_ceiling <= sp1 -> sp1 + 160 <= s -> s <= q -> q + 24 <= 2 ^ 64 ->
  s <= a < 2 ^ 64 -> ~ (q <= a < q + 8) ->
  mrestrict (w_H W) ma (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a).
Proof.
intros ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q a HAR2 HFRS HBL HH
  (HFr & HWIN0 & HK & HARU1 & HARU2 & KEEPh & KEEPd & KEEPa) Hsp1 Hs Hsq Hq64 Ha Haq.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (pv_arm_pw B ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q a HAR2 HFRS HBL HH HFr HWIN0 HK HARU1 HARU2
  KEEPh KEEPd KEEPa Hsp1 Hs Hsq Hq64 ltac:(lia) Haq).
left. split; lia.
Qed.
(* a live block's byte *)
Lemma pv_arm_blk : forall ly S S2 U (W : world tfibsegs) mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q b n a,
  AR tfibsegs B ly S2 W (unpoison U mem2) md2 ->
  frames S2 = (0, pos) :: frames S -> ablocks B ly S2 = ablocks B ly S -> FSupoisonU.fs_heads B ly S U ->
  pv_keeps ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q ->
  alloc_ceiling <= sp1 -> sp1 + 160 <= s -> s <= q -> q + 24 <= 2 ^ 64 ->
  In (b, n) (ablocks B ly S) -> b <= a < b + req_size n -> 0 <= a < 2 ^ 64 -> ~ (q <= a < q + 8) ->
  mrestrict (w_H W) ma (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a).
Proof.
intros ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q b n a HAR2 HFRS HBL HH
  (HFr & HWIN0 & HK & HARU1 & HARU2 & KEEPh & KEEPd & KEEPa) Hsp1 Hs Hsq Hq64 Hb Hbn Ha Haq.
exact (pv_arm_pw B ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q a HAR2 HFRS HBL HH HFr HWIN0 HK HARU1 HARU2
  KEEPh KEEPd KEEPa Hsp1 Hs Hsq Hq64 Ha Haq (or_intror (or_introl (ex_intro _ b (ex_intro _ n (conj Hb Hbn)))))).
Qed.
(* an old frame's byte or shadow byte *)
Lemma pv_arm_frm : forall ly S S2 U (W : world tfibsegs) mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q cid pos' a,
  AR tfibsegs B ly S2 W (unpoison U mem2) md2 ->
  frames S2 = (0, pos) :: frames S -> ablocks B ly S2 = ablocks B ly S -> FSupoisonU.fs_heads B ly S U ->
  pv_keeps ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q ->
  alloc_ceiling <= sp1 -> sp1 + 160 <= s -> s <= q -> q + 24 <= 2 ^ 64 ->
  In (cid, pos') (frames S) ->
  (in_zr a (frame_rng ly (cid, pos')) \/ in_zr a (shadow_addr (frame_addr ly cid pos'), fs_frame_bytes cid / 8)) ->
  0 <= a < 2 ^ 64 -> ~ (q <= a < q + 8) ->
  mrestrict (w_H W) ma (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a).
Proof.
intros ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q cid pos' a HAR2 HFRS HBL HH
  (HFr & HWIN0 & HK & HARU1 & HARU2 & KEEPh & KEEPd & KEEPa) Hsp1 Hs Hsq Hq64 Hf Hfr Ha Haq.
exact (pv_arm_pw B ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q a HAR2 HFRS HBL HH HFr HWIN0 HK HARU1 HARU2
  KEEPh KEEPd KEEPa Hsp1 Hs Hsq Hq64 Ha Haq
  (or_intror (or_intror (ex_intro _ cid (ex_intro _ pos' (conj Hf Hfr)))))).
Qed.
End AD.
Section AD2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* the word-indexed form of pv_wr_pw, for wr_at's clauses *)
Lemma pv_wv_eq : forall (m m' : word -> option byte) (x : word), m' x = m x ->
  wview tfibsegs m' x = wview tfibsegs m x.
Proof. intros m m' x H. unfold wview. rewrite H. reflexivity. Qed.
(* val_mem reads memory only through mbyte, so an mbyte equality is enough to move it (used for the image-resident
   fuzz statics, where pv_arm_img gives mbyte equality and not raw-byte equality) *)
Lemma pv_val_mb : forall (m m' : word -> option byte) a (n : nat) v, val_mem tfibsegs m a n v ->
  (forall k, (k < n)%nat -> mbyte tfibsegs m' (a + Z.of_nat k) = mbyte tfibsegs m (a + Z.of_nat k)) ->
  val_mem tfibsegs m' a n v.
Proof. intros m m' a n v Hv E k Hk. rewrite (E k Hk). exact (Hv k Hk). Qed.
(* the five data facts of parse_value_spec that the arm memory must still carry, from the entry memory through the
   front's keeps (pv_keeps): the window keep, struct pj_in, the text block, the object's zeros and the fuzz statics.
   pobj is pv_arm_pobj (it splits on pobj's two placements). *)
Lemma pv_arm_data : forall ly S S2 U (W : world tfibsegs) mem m1 mem2 mh mdl ma md0 md1 md2 E
    pos s sp1 q ot v text len p cur d (tb : list byte) tcap live peak cnt fail,
  AR tfibsegs B ly S W (unpoison U mem) md0 ->
  fs_img_facts tfibsegs B ->
  AR tfibsegs B ly S2 W (unpoison U mem2) md2 ->
  frames S2 = (0, pos) :: frames S -> ablocks B ly S2 = ablocks B ly S -> FSupoisonU.fs_heads B ly S U ->
  pv_keeps B ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q ->
  alloc_ceiling <= sp1 -> sp1 + 160 <= s -> s <= q -> q + 24 <= ot -> ot <= 2 ^ 47 ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p d tb ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  PjStruct.pj_zero tfibsegs (mrestrict (w_H W) mem) v ->
  pobj tfibsegs B ly S W mem v ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  val_mem tfibsegs (mrestrict (w_H W) ma) q 8 cur ->
  (forall o, 0 <= o < 8 -> writable_at tfibsegs (mrestrict (w_H W) ma) (q + o)) ->
  text <= cur <= text + len ->
  wkeep tfibsegs W W mem ma s ot q 24 /\
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) ma) q text len cur d tb /\
  rd_text tfibsegs B ly S2 W ma text len tcap /\
  PjStruct.pj_zero tfibsegs (mrestrict (w_H W) ma) v /\
  fs_glob tfibsegs W ma live peak cnt fail.
Proof.
intros ly S S2 U W mem m1 mem2 mh mdl ma md0 md1 md2 E pos s sp1 q ot v text len p cur d tb tcap live peak cnt fail
  HAR0 IMG HAR2 HFRS HBL HH HKEEPS Hsp1 Hs Hsq Hqot Hot HIN HTX HZo HPo HGL VQ WQ Hcur.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HKEEPS as (HFr & HWIN0 & HK & HARU1 & HARU2 & KEEPh & KEEPd & KEEPa).
pose proof (ARU_AR tfibsegs B ly S U W m1 md1 HARU1) as HAR1.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Hq0 & Hq64 & Ht0 & (Hp1 & Hp2) & Hend & Hqtx & Hlen & Hq8 & Hd).
pose proof HTX as (Htx4096 & Htxblk & Htxlen). pose proof Htxblk as (HinT & Ht16 & Htcap & Vhd).
destruct (fsw_rblock_low B ly S W (unpoison U mem) md0 mem text tcap HAR0 Htxblk) as (Ht1 & Ht2).
pose proof (fsw_pobj_low B ly S W (unpoison U mem) md0 mem v HAR0 HPo) as (Hv4096 & Hvc).
assert (STK : forall lo hi, s <= lo -> hi <= 2 ^ 64 -> (q + 8 <= lo \/ hi <= q) ->
  forall x : word, lo <= bv_unsigned x < hi -> mrestrict (w_H W) ma x = mrestrict (w_H W) mem x).
{ intros lo hi Hlo Hhi Hoff x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x).
  exact (pv_arm_stk B ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q (bv_unsigned x) HAR2 HFRS HBL HH HKEEPS
    Hsp1 Hs Hsq ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (BLK : forall b n lo hi, In (b, n) (ablocks B ly S) -> b <= lo -> hi <= b + req_size n -> 0 <= lo ->
  hi <= 2 ^ 64 -> (q + 8 <= lo \/ hi <= q) ->
  forall x : word, lo <= bv_unsigned x < hi -> mrestrict (w_H W) ma x = mrestrict (w_H W) mem x).
{ intros b n lo hi Hb Hlo Hhi H0 Hhi64 Hoff x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x).
  exact (pv_arm_blk B ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q b n (bv_unsigned x) HAR2 HFRS HBL HH
    HKEEPS Hsp1 Hs Hsq ltac:(lia) Hb ltac:(lia) ltac:(lia) ltac:(lia)). }
(* the text block's body, for pj_in_ok's text bytes and rd_text's head word *)
assert (TXB : forall x : word, text - HEAD <= bv_unsigned x < text + tcap ->
  mrestrict (w_H W) ma x = mrestrict (w_H W) mem x).
{ intros x Hx.
  assert (Hrq : tcap + HEAD <= req_size (tcap + HEAD))
    by (unfold req_size; destruct (Z.eqb_spec (tcap + HEAD) 0); lia).
  exact (BLK (text - HEAD) (tcap + HEAD) (text - HEAD) (text + tcap) HinT ltac:(lia) ltac:(unfold HEAD in *; lia)
    ltac:(unfold HEAD in *; lia) ltac:(lia) ltac:(right; unfold HEAD in *; lia) x Hx). }
split; [|split; [|split; [|split]]].
- (* the window keep *)
  intros a Ha Hoff. assert (Hpw : mrestrict (w_H W) ma (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
    by (exact (pv_arm_stk B ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q a HAR2 HFRS HBL HH HKEEPS
         Hsp1 Hs Hsq ltac:(lia) ltac:(lia) ltac:(lia))).
  split; [exact (pv_mb_pw _ _ a Hpw)|].
  split; intros Hw.
  + exact (pv_writable_eq (mrestrict (w_H W) mem) (mrestrict (w_H W) ma) a ltac:(lia)
      ltac:(intros x Hx; rewrite <- (Z_to_bv_bv_unsigned 64 x); replace (bv_unsigned x) with a by lia; exact Hpw) Hw).
  + exact (pv_writable_eq (mrestrict (w_H W) ma) (mrestrict (w_H W) mem) a ltac:(lia)
      ltac:(intros x Hx; rewrite <- (Z_to_bv_bv_unsigned 64 x); replace (bv_unsigned x) with a by lia;
            exact (eq_sym Hpw))
      Hw).
- (* struct pj_in: in->p from the arm, in->end and in->depth kept, the text bytes kept *)
  destruct HIN as (Bp & Be & Bd & Hwr & Hq8' & Ht0' & Hend' & Hp' & Hlen' & Btx & Hdisj & Hd').
  split; [exact (KindBGlue.word_mem_le8 tfibsegs (mrestrict (w_H W) ma) q cur
    (proj1 (val_mem_word_mem tfibsegs _ q cur) VQ) ltac:(lia) ltac:(lia) ltac:(lia))|].
  split.
  { apply (PjStruct.pj_bytes_eq tfibsegs (mrestrict (w_H W) mem) (mrestrict (w_H W) ma) (q + 8) _ Be).
    rewrite Mem.length_le8.
    exact (STK (q + 8) (q + 8 + Z.of_nat 8) ltac:(lia) ltac:(lia) ltac:(left; lia)). }
  split.
  { apply (PjStruct.pj_bytes_eq tfibsegs (mrestrict (w_H W) mem) (mrestrict (w_H W) ma) (q + 16) _ Bd).
    rewrite Mem.length_le4.
    exact (STK (q + 16) (q + 16 + Z.of_nat 4) ltac:(lia) ltac:(lia) ltac:(left; lia)). }
  split.
  { split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i 8) as [Hi8 | Hi8].
    - pose proof (WQ i ltac:(lia)) as Hw. unfold writable_at in Hw. exact Hw.
    - pose proof Hwr as (_ & _ & Hw0). pose proof (Hw0 i Hi) as Hw.
      assert (Epw : mrestrict (w_H W) ma (lib.Lib.Mem.wa (q + i)) = mrestrict (w_H W) mem (lib.Lib.Mem.wa (q + i)))
        by (exact (STK (q + 8) (q + 24) ltac:(lia) ltac:(lia) ltac:(left; lia) (lib.Lib.Mem.wa (q + i))
              ltac:(unfold lib.Lib.Mem.wa; rewrite wz; lia))).
      rewrite (pv_wv_eq _ _ (lib.Lib.Mem.wa (q + i)) Epw). exact Hw. }
  split; [exact Hq8'|]. split; [exact Ht0'|]. split; [exact Hend'|]. split; [exact Hcur|]. split; [exact Hlen'|].
  split.
  { apply (PjStruct.pj_bytes_eq tfibsegs (mrestrict (w_H W) mem) (mrestrict (w_H W) ma) text tb Btx).
    intros x Hx. apply TXB. unfold HEAD in *. lia. }
  split; [exact Hdisj | exact Hd'].
- (* the text block *)
  split; [exact Htx4096|]. split; [|exact Htxlen].
  split; [rewrite HBL; exact HinT|]. split; [exact Ht16|]. split; [exact Htcap|].
  exact (pv_val_eq (mrestrict (w_H W) mem) (mrestrict (w_H W) ma) (text - HEAD) 8 tcap ltac:(unfold HEAD in *; lia)
    ltac:(unfold HEAD in *; lia) Vhd ltac:(intros x Hx; apply TXB; cbn [Z.of_nat] in Hx; unfold HEAD in *; lia)).
- (* the object's 56 zero bytes *)
  destruct HZo as (Hrw & Bz).
  assert (VPW : forall x : word, v <= bv_unsigned x < v + 56 ->
    mrestrict (w_H W) ma x = mrestrict (w_H W) mem x).
  { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x).
    destruct HPo as [[((cid & pos' & Hf & Hc0 & Hfa & Hfv1 & Hfv2) & _ & _) |
                      ((b & n & Hb & Hb1 & Hb2) & _ & _)] _].
    - assert (Hcl : in_zr (bv_unsigned x) (frame_rng ly (cid, pos')) \/
        in_zr (bv_unsigned x) (shadow_addr (frame_addr ly cid pos'), fs_frame_bytes cid / 8))
        by (left; unfold in_zr, frame_rng; cbn [fst snd]; lia).
      exact (pv_arm_frm B ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q cid pos' (bv_unsigned x) HAR2 HFRS
        HBL HH HKEEPS Hsp1 Hs Hsq ltac:(lia) Hf Hcl ltac:(lia) ltac:(lia)).
    - exact (pv_arm_blk B ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q b n (bv_unsigned x) HAR2 HFRS HBL HH
        HKEEPS Hsp1 Hs Hsq ltac:(lia) Hb ltac:(unfold HEAD in *; lia) ltac:(lia) ltac:(lia)). }
  split.
  + destruct Hrw as (Hv8 & Hstk). split; [exact Hv8|].
    exact (PjStruct.pj_stk_eq tfibsegs (mrestrict (w_H W) mem) (mrestrict (w_H W) ma) v (v + 56) Hstk
      ltac:(intros x Hx; apply VPW; lia)).
  + exact (PjStruct.pj_bytes_eq tfibsegs (mrestrict (w_H W) mem) (mrestrict (w_H W) ma) v _ Bz
      ltac:(intros x Hx; apply VPW; rewrite repeat_length in Hx; cbn [Z.of_nat] in Hx; lia)).
- (* the four fuzz statics: image-resident, so the transport runs through mbyte *)
  unfold fs_glob, fs_glob_at in HGL |- *.
  destruct HGL as (Vl & Vp & Vc & Vf & R1 & R2 & R3 & R4).
  assert (GMB : forall g, inFP FS_PSTAT_FP g ->
    mbyte tfibsegs (mrestrict (w_H W) ma) g = mbyte tfibsegs (mrestrict (w_H W) mem) g).
  { intros g Hg.
    exact (pv_arm_img B ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q g IMG HAR2 HFRS
      HFr HWIN0 HK HARU1 HARU2 KEEPh KEEPd KEEPa Hsp1 Hs Hsq Hg). }
  split; [exact (pv_val_mb _ _ G_LIVE 8 live Vl ltac:(intros k Hk; apply GMB; exists (0x5da5c0, 0x5da5c8);
    split; [unfold FS_PSTAT_FP; cbn [In]; right; left; reflexivity
           | unfold G_LIVE; cbn [fst snd]; lia]))|].
  split; [exact (pv_val_mb _ _ G_PEAK 8 peak Vp ltac:(intros k Hk; apply GMB; exists (0x5da5e0, 0x5da5e8);
    split; [unfold FS_PSTAT_FP; cbn [In]; right; right; left; reflexivity
           | unfold G_PEAK; cbn [fst snd]; lia]))|].
  split; [exact (pv_val_mb _ _ G_COUNT 8 cnt Vc ltac:(intros k Hk; apply GMB; exists (0x5da600, 0x5da608);
    split; [unfold FS_PSTAT_FP; cbn [In]; right; right; right; left; reflexivity
           | unfold G_COUNT; cbn [fst snd]; lia]))|].
  split; [exact (pv_val_mb _ _ G_FAIL 8 fail Vf ltac:(intros k Hk; apply GMB; exists (0xa3ca0, 0xa3ca8);
    split; [unfold FS_PSTAT_FP; cbn [In]; left; reflexivity
           | unfold G_FAIL; cbn [fst snd]; lia]))|].
  split; [exact R1|]. split; [exact R2|]. split; [exact R3 | exact R4].
Qed.
End AD2.
Section AD3. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* the caller's object v keeps its placement from the entry (S, mem) to the arm (S2, ma): its 56 bytes are kept
   (pv_arm_frm / pv_arm_blk), the shadow bytes of a frame-resident v are kept (pv_arm_frm's shadow clause), and a
   block-resident v is addressable at the arm by its block (fsw_block_body_addressable over the arm's ARU) *)
Lemma pv_arm_pobj : forall ly S S2 U (W : world tfibsegs) mem m1 mem2 mh mdl ma md0 md1 md2 mda E pos s sp1 q v,
  AR tfibsegs B ly S W (unpoison U mem) md0 ->
  AR tfibsegs B ly S2 W (unpoison U mem2) md2 ->
  frames S2 = (0, pos) :: frames S -> ablocks B ly S2 = ablocks B ly S -> FSupoisonU.fs_heads B ly S U ->
  pv_keeps B ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q ->
  alloc_ceiling <= sp1 -> sp1 + 160 <= s -> s <= q -> q + 24 <= 2 ^ 64 ->
  ARU tfibsegs B ly S2 U W ma mda ->
  pobj tfibsegs B ly S W mem v ->
  pobj tfibsegs B ly S2 W ma v.
Proof.
intros ly S S2 U W mem m1 mem2 mh mdl ma md0 md1 md2 mda E pos s sp1 q v
  HAR0 HAR2 HFRS HBL HH HKEEPS Hsp1 Hs Hsq Hq64 HARUa HPo.
pose proof (fsw_pobj_low B ly S W (unpoison U mem) md0 mem v HAR0 HPo) as (Hv4096 & Hvc).
assert (HH2 : FSupoisonU.fs_heads B ly S2 U).
{ intros r Hr. destruct (HH r Hr) as (H1 & m & H2 & H3). split; [exact H1|]. exists m. rewrite HBL. auto. }
destruct HPo as [[((cid & pos' & Hf & Hc0 & Hfa & Hfv1 & Hfv2) & H8 & Hr) | ((b & n & Hb & Hb1 & Hb2) & H8 & Hr)] Hw].
- (* v in a live fake frame of S: its bytes and its shadow bytes are kept *)
  assert (Hfb : fs_frame_bytes cid = 8 * (8 * 2 ^ cid))
    by (unfold fs_frame_bytes; rewrite Z.shiftl_mul_pow2 by lia; lia).
  pose proof (Z.div_mod (frame_addr ly cid pos') 8 ltac:(lia)) as EF. rewrite Hfa, Z.add_0_r in EF.
  assert (VPW : forall x : word, v <= bv_unsigned x < v + 56 ->
    mrestrict (w_H W) ma x = mrestrict (w_H W) mem x).
  { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x).
    assert (Hcl : in_zr (bv_unsigned x) (frame_rng ly (cid, pos')) \/
        in_zr (bv_unsigned x) (shadow_addr (frame_addr ly cid pos'), fs_frame_bytes cid / 8))
      by (left; unfold in_zr, frame_rng; cbn [fst snd]; lia).
    exact (pv_arm_frm B ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q cid pos' (bv_unsigned x) HAR2 HFRS
      HBL HH HKEEPS Hsp1 Hs Hsq Hq64 Hf Hcl ltac:(lia) ltac:(lia)). }
  split.
  + left. split.
    { exists cid, pos'. split; [rewrite HFRS; right; exact Hf|]. split; [exact Hc0|]. split; [exact Hfa|].
      split; [exact Hfv1 | exact Hfv2]. }
    split; [exact H8|].
    intros x Hx. destruct (Hr x Hx) as (sb & Es & Ok). exists sb. split; [|exact Ok].
    assert (Hxc : 0 <= x < alloc_ceiling) by lia.
    pose proof (fsw_shadow_below x Hxc) as (Hsb0 & Hsb1).
    assert (Hsh : in_zr (shadow_of_addr SHADOW_OFF x) (shadow_addr (frame_addr ly cid pos'), fs_frame_bytes cid / 8)).
    { unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd].
      rewrite Hfb. replace (8 * (8 * 2 ^ cid)) with ((8 * 2 ^ cid) * 8) by lia. rewrite Z.div_mul by lia.
      pose proof (Z.div_mod x 8 ltac:(lia)) as EX. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as MX.
      rewrite Hfb in Hfv2. lia. }
    assert (Ebyte : mrestrict (w_H W) ma (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x))
                  = mrestrict (w_H W) mem (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x)))
      by (exact (pv_arm_frm B ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q cid pos'
                   (shadow_of_addr SHADOW_OFF x) HAR2 HFRS HBL HH HKEEPS Hsp1 Hs Hsq Hq64 Hf (or_intror Hsh)
                   ltac:(lia) ltac:(lia))).
    rewrite <- Es. unfold aview. rewrite (pv_mb_pw (mrestrict (w_H W) mem) (mrestrict (w_H W) ma) _ Ebyte).
    reflexivity.
  + intros i Hi. apply (writable_at_eq tfibsegs (mrestrict (w_H W) mem) (mrestrict (w_H W) ma) (v + i));
      [apply VPW; rewrite wz; lia | exact (Hw i Hi)].
- (* v inside a live heap block past its head: its bytes are kept, its block makes it addressable at the arm *)
  assert (VPW : forall x : word, v <= bv_unsigned x < v + 56 ->
    mrestrict (w_H W) ma x = mrestrict (w_H W) mem x).
  { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x).
    exact (pv_arm_blk B ly S S2 U W mem m1 mem2 mh mdl ma md1 md2 E pos s sp1 q b n (bv_unsigned x) HAR2 HFRS HBL HH
      HKEEPS Hsp1 Hs Hsq Hq64 Hb ltac:(unfold HEAD in *; lia) ltac:(lia) ltac:(lia)). }
  split.
  + right. split; [exists b, n; rewrite HBL; split; [exact Hb | split; [exact Hb1 | exact Hb2]]|].
    split; [exact H8|].
    exact (fsw_block_body_addressable B ly S2 U W ma mda b n v 56 HARUa HH2 ltac:(rewrite HBL; exact Hb)
      ltac:(unfold HEAD in *; lia) ltac:(lia) Hb2).
  + intros i Hi. apply (writable_at_eq tfibsegs (mrestrict (w_H W) mem) (mrestrict (w_H W) ma) (v + i));
      [apply VPW; rewrite wz; lia | exact (Hw i Hi)].
Qed.
End AD3.
