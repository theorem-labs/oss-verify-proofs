(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0j.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YN0j.v, with its module paths and module names changed; 546 of its 584 lines of code are new or changed and 260 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC.v, with its module names changed; 1538 of its 1613 lines of code are new or changed and 509 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC2.v; 288 of its 361 lines of code are new or changed and 1540 lines of the source are left out. *)
(* rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from a working branch d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_stdefs.v St17 :521 / St18 :535 and check_round_trip_sd16.v :541, the bespoke ASan proof of THIS function on THESE bytes). CHECKER VERDICT: CONFIRM (a Theorem Labs lane, role check, 2026-10-29 04:3xZ) on (internal path), lines 6-21 (proof index v5, 2026-10-29T01:50:18Z; 31 named hits all plain/ubsan; the exact hit's Require closure 334 files, 0 Admitted/Axiom/Parameter).

   check_round_trip 0x81a9c, fs.asan (image tfibsegs, the pinned fuzz_state.asan sha256 64b53ff86172bb07...), lane D1,
   SEGMENT 30: from the return of pj_get_str (0x82268, crt_INV_82268) across the second preset_base64_decode (z, &n)
   (call 0x82270, entry A_preset_base64_decode, return 0x82274) to crtD1_INV_82274.
   The stretch 0x82268 .. 0x82270 is `beqz a0` (to the trap arm), `mv a1, s11`, the call: it reads no memory. The run
   starts from the shared two-region state FSH_crt_site.crt_ss2 (the saved words and the s1 slots), stops at the
   `beqz a0`, which crt_INV_82268's z <> 0 decides (FSH_crt_site.crt_no_trap_eq), and runs on to the decoder's entry;
   FSH_crt_site.crt_call_core does the call and the return. The decode's own part is crtD1d_hcall30: decode_spec_ff
   at text := z, lenp := F + 0x1a0 (crt's class-3 frame), tb := zs = b64_enc bs, its success arm (cnt <> fail and
   b64_dec zs = Some bs kill the other two), and crtD1_INV_82274 from its post, the invariant's data facts carried
   across the callee's journal with FSW_rd's *_kept_call lemmas.
   R1 hold: decode's kept-buffer premise `wsrc_kept .. 0 z (zs ++ [0])` is paid by its SECOND arm: z with its nz
   bytes is a block of the parsed document's list (crt_INV_82268's `In (z, nz) Dback`, rnode's rd_blocks_ok), and
   z <> 0. The decode's footprint facts (it meets no live block, no frame byte off the length cell, no shadow byte)
   are a Theorem Labs lane's FSH_crt_segD1_keep.crtD1_dec_fp_clear. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG05 YG0s YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret FSW_frame
FSW_rd FSW_strkit FSW_crt_tbl FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt FSH_crt_base
FSH_crt_site FSH_crt_room FSH_crt_segD1 FSH_crt_segD1_inv FSH_crt_segD1_keep.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AE2k.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState PjStruct
  check_round_trip_stages_b.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= the engine runs of segment 30 (MEASURED by the engine over crt_tbl on the pinned fs.asan; every
   lemma closed by vm_compute) =================
   From crt_ss2 0x82268 the engine stops at once at `beqz a0` (0x82268); with the not-taken condition a0 <> 0 added it
   reaches the decoder's entry with ra = 0x82274, a0 = atom 10 (z), a1 = atom 27 (s11 = F + 0x1a0), and the two
   regions and the boundary atoms unchanged. *)
Definition crtD1d_c0 : acond := mkAC BC_NE (SOff 10 0) (SLit 0).
Definition crtD1d_sb30 : sstate := Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x82268)).
Lemma crtD1d_br30 :
  sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x82268) = (crtD1d_sb30, RS_stopped (SR_branch BC_EQ (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition crtD1d_sc30 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL A_preset_base64_decode (add_cond crtD1d_sb30 crtD1d_c0)).
Lemma crtD1d_run30 :
  sym_run_toN tfibsegs crt_tbl FUEL A_preset_base64_decode (add_cond crtD1d_sb30 crtD1d_c0) = (crtD1d_sc30, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtD1d_site30 : crt_site crtD1d_sb30 crtD1d_sc30 A_preset_base64_decode 0x82274.
Proof. unfold crt_site, crt_csite. repeat split; vm_compute; reflexivity. Qed.
Lemma crtD1d_ra30 : sr_get (ss_regs crtD1d_sc30) 1%bv = SLit 0x82274.
Proof. vm_compute. reflexivity. Qed.
Lemma crtD1d_regs30 :
  sr_get (ss_regs crtD1d_sc30) 10%bv = SOff 10 0 /\ sr_get (ss_regs crtD1d_sc30) 11%bv = SOff 27 0.
Proof. split; vm_compute; reflexivity. Qed.
Lemma crtD1d_ssave30 : crt_ssave crtD1d_sc30.
Proof. apply crt_ssave_dec. vm_compute. reflexivity. Qed.

(* ================= arithmetic of the budgets =================
   Every reader event costs at least one tick (FSH_Fn_reader.rd_ev) and every writer request at least one
   (FSH_Fn_writer.wev0), so each g_count prefix bound is at most the journal-tick prefix bound of the same boundary;
   with crt_room_D1's K_822ac <= EV_check_round_trip (FSH_crt_room.crt_room_D1_holds) this bounds g_count far below
   g_fail_at = SIZE_MAX (crt_base's quiet).
   KERNEL TRAP (a Theorem Labs lane, measured): a Qed hangs when lia uses a hypothesis after `unfold K_<pc> in H`, because the
   kernel's default oracle unfolds Z.add before K_<pc> and evaluates the sum; the Strategy below lets it unfold the
   prefix constants first. *)
Local Strategy expand [K_822ac K_82268 CNT_82268 K_82274 CNT_82274 LIVE_82274 LIVE_822ac LIVE_82268].
Lemma crtD1d_trlen_ev : forall tr, crt_trlen tr <= rd_ev tr.
Proof.
intros tr. unfold crt_trlen, rd_ev. induction tr as [|e tr IH]; [cbn; lia|].
cbn [length fold_right]. rewrite Nat2Z.inj_succ.
destruct e; repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  unfold EV_fuzz_malloc, EV_fuzz_realloc, EV_fuzz_free in *; lia.
Qed.
Lemma crtD1d_wcalls_wev0 : forall w, FSH_Fn_writer.wcalls w <= FSH_Fn_writer.wev0 w.
Proof.
intros w. unfold FSH_Fn_writer.wcalls, FSH_Fn_writer.wev0.
destruct (WriterApp.w_calls w) as [|c r]; cbn [length]; [lia|].
rewrite Nat2Z.inj_succ. unfold EV_fuzz_malloc, EV_fuzz_realloc. lia.
Qed.
(* base v33's by-trace K / CNT_82268: CNT_82218 = 17 <= 19 = K_82218 (FSH_crt_room.crtr_K18), pj_write's requests
   wcalls <= wev0, pj_parse's events crt_trlen <= rd_ev *)
Lemma crtD1d_cnt_le_k : forall cx, CNT_82268 cx <= K_82268 cx.
Proof.
intros cx. destruct (crtr_K18 cx) as (EK & EC).
unfold CNT_82268, K_82268. rewrite EK, EC.
pose proof (crtD1d_wcalls_wev0 (crt_wst cx)) as HW. pose proof (crtD1d_trlen_ev (crt_TR cx)) as HT. lia.
Qed.
(* the block bytes of a tree's list: each reader block is its request plus the 16-byte head *)
Lemma crtD1d_bsum_rdh : forall D, bsum (rd_hblocks D) = rd_sum D + HEAD * Z.of_nat (length D).
Proof.
induction D as [|[a kk] D IH]; [reflexivity|].
change (rd_hblocks ((a, kk) :: D)) with ((a - HEAD, kk + HEAD) :: rd_hblocks D).
change (rd_sum ((a, kk) :: D)) with (kk + rd_sum D).
rewrite bsum_cons, IH. cbn [snd length]. rewrite Nat2Z.inj_succ. cbv [HEAD]. lia.
Qed.

Section s30. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* ---- one segment that starts with `beqz a0` NOT taken (a0 <> 0), then runs store-free to a PROGRAM call:
   FSH_crt_site.crt_seg_call_br with the branch flipped (crt_no_trap_eq instead of crt_no_trap_ne) ---- *)
Lemma crtD1d_seg_call_bz : forall r0 A_c r sb ssC (INV INV' : crt_inv) STKc,
  sym_runN tfibsegs crt_tbl FUEL (crt_ss2 r0) = (sb, RS_stopped (SR_branch BC_EQ (SOff 10 0) (SLit 0))) ->
  sym_run_toN tfibsegs crt_tbl FUEL A_c (add_cond sb crtD1d_c0) = (ssC, RS_running) ->
  crt_site sb ssC A_c r -> 4096 <= r < 2 ^ 64 -> r mod 2 = 0 ->
  0 <= STKc -> STKc + 208 <= STK_check_round_trip ->
  (forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3, INV cx E k ly3 S3 U3 W3 ms3 md3 ->
     exists z, ew E 10 = Z_to_bv 64 z /\ 0 <= z < 2 ^ 64 /\ z <> 0) ->
  crt_hcall SK B ssC A_c r STKc INV INV' ->
  crt_from SK B (crt_ss_ret r crt_cs1 crt_csF) INV' ->
  crt_from SK B (crt_ss_ret r0 crt_cs1 crt_csF) INV.
Proof.
intros r0 A_c r sb ssC INV INV' STKc HRUN1 HRUN2 (Hmem1 & HCS) Hr Hr2 HSTKc HSTK HZ HCALL NEXT.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFO HINV HS.
assert (AWR : forall ssx, ss_mem ssx = [crt_s0_region; crt_slot_region crt_cs1] ->
  awr_ok tfibsegs B E (ss_mem ssx) STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP
    (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)))
  by (intros ssx Hx; rewrite Hx; exact (crt_awr2 B cx E ly3 S3 HB HE)).
pose proof (st_ok_submem tfibsegs E _ _ _ HS (crt_sub2 r0) ltac:(vm_compute; reflexivity)) as HS2.
change (st_ok tfibsegs E (crt_ss2 r0) (restrict (w_H W3) ms3)) in HS2.
(* run 1: to the `beqz a0` *)
eapply (@fsw_run_AJU fx rc SK B crt_tbl crt_tbl_ok W3 FUEL E (crt_ss2 r0) sb _ ms3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  HS2 HRUN1 I HARU HJ (AWR (crt_ss2 r0) eq_refl)).
intros ms1 mat1 HS1 HJ1 HARU1 HF1 HFr1 HG1.
(* the not-taken arm: a0 = z <> 0 *)
destruct (HZ _ _ _ _ _ _ _ _ _ HINV) as (z & Ez & Hz & Hnz).
pose proof (st_ok_add_cond_neg tfibsegs E sb _ BC_EQ (SOff 10 0) (SLit 0) HS1 (crt_no_trap_eq E z Ez Hz Hnz)) as HS1c.
change (add_cond sb (mkAC (neg_bc BC_EQ) (SOff 10 0) (SLit 0))) with (add_cond sb crtD1d_c0) in HS1c.
(* run 2: to the callee *)
eapply (@fsw_run_to_AJU fx rc SK B crt_tbl crt_tbl_ok W3 FUEL A_c E (add_cond sb crtD1d_c0) ssC RS_running ms1
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS1c HRUN2 I HARU1 HJ1 (AWR (add_cond sb crtD1d_c0) Hmem1)).
intros ms mat HSC HJC HARUC HF HFr HG.
assert (HF1' : frame_of E [crt_s0_region; crt_slot_region crt_cs1] (ms_mem ms3) (ms_mem ms1)) by exact HF1.
assert (HF' : frame_of E [crt_s0_region; crt_slot_region crt_cs1] (ms_mem ms1) (ms_mem ms))
  by (rewrite <- Hmem1; exact HF).
exact (crt_call_core SK B ssC A_c r INV INV' STKc cx E k ly3 S3 U3 W3 ms3 md3 ms _ HCS Hr Hr2 HSTKc HSTK HCALL NEXT
  HB HE HFO HINV HSC HJC HARUC
  (same_below_trans _ _ _ _ (crt_sb B cx E _ _ HB HE HF1') (crt_sb B cx E _ _ HB HE HF'))).
Qed.

Hypothesis DECODE : @FSH_Fn_writer.decode_spec_ff fx rc SK B tfibsegs.
(* the decode's room (crt_room_D1) is FSH_crt_room.crt_room_D1_holds, over base v33's by-trace budgets *)

(* ---- the decode call's own part: decode_spec_ff's premises at the call site, its success arm, and
   crtD1_INV_82274 at the return ---- *)
Lemma crtD1d_hcall30 : crt_hcall SK B crtD1d_sc30 A_preset_base64_decode 0x82274 STK_preset_base64_decode
  (crt_INV_82268 B) (crtD1_INV_82274 B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HSB RG HPREc HFRL HTOPc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_lt rc) as HC47.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hquiet & Hlive64 & _ & _ &
  Hnev0 & Hbb0).
destruct (crt_room_D1_holds B cx HB) as (HKroom & HLroom).
destruct HINV as (E18 & E20 & E21 & E23 & E26 & E27 & same & nsame & file & nfile & back & z & zs & Dback & Ddoc &
  tback & live & peak & cnt & E22 & E24 & E25 & E10 & Hz0 & HPB & HPU & HHD & HRtext & HRback & HZback & HRfile &
  HTdoc & HNback & HOback & HOdoc & HCz & Hdec & Hzs & (nz & Hinz & Hnzl) & Hdep & Hlive & HV0 & HRA & HG & Hbb &
  Hcnt & Hk & Hrem).
subst zs.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) as HAR3.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
pose proof HJC as (_ & Hly3 & _ & _ & _ & _ & Hnev3 & _).
pose proof (crt_F_ly cx _ ly3 Hly3) as EF.
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 memC mdC k HJC HARUC Hfr) as (HF32 & HF4096 & HFceil & _ & _ & _).
(* ---- the registers at the call: ra = 0x82274, a0 = z, a1 = &n = F + 0x1a0, s2 .. s11 the boundary atoms ---- *)
assert (R1 : YK11.getr regsC 1%bv = Z_to_bv 64 0x82274) by (rewrite RG, crtD1d_ra30; reflexivity).
assert (Hra : raZ regsC = 0x82274) by (unfold raZ; rewrite R1; apply wz; lia).
assert (G10 : YK11.getr regsC 10%bv = w64 z) by (rewrite RG, (proj1 crtD1d_regs30), fsw_SOff0; exact E10).
assert (G11 : YK11.getr regsC 11%bv = w64 (crt_F cx + 0x1a0))
  by (rewrite RG, (proj2 crtD1d_regs30), fsw_SOff0; exact E27).
assert (RS : forall n, (18 <= n <= 27)%nat -> YK11.getr regsC (Z_to_bv 5 (Z.of_nat n)) = ew E n).
{ intros n Hn. rewrite RG, (crtD1d_ssave30 n Hn). apply fsw_SOff0. }
(* ---- the text z: cstr_ok at the call, its bytes, and its block (z, nz) of back's list ---- *)
pose proof (cstr_ok_below W3 (ms_mem ms3) memC z (WriterSpec.b64_enc (c_bs cx)) HSB HCz) as HCz'.
pose proof HCz' as ((Hgz & _) & Hz4096 & Hzceil & _).
assert (Hbok : WriterSpec.bytes_ok (WriterSpec.b64_enc (c_bs cx)))
  by exact (garr8_bytes_ok tfibsegs _ _ _ (proj1 (proj1 (garr8_app tfibsegs _ _ _ _) Hgz))).
pose proof HNback as (_ & HNblk & HNincl).
pose proof (fs_rblock_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC z nz HAR3 HSB (HNblk z nz (HNincl _ Hinz))) as Hrz.
pose proof Hrz as (Hzin & _ & Hnz0 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hzin) as (_ & _ & _ & _ & _ & _ & Hzmax).
pose proof (req_size_pos (nz + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hzreq).
(* ---- the length cell at F + 0x1a0: inside crt's frame, 8-aligned, present, holding 0, apart from the text ---- *)
assert (Hlo : frame_addr ly3 3 (c_pos cx) <= crt_F cx + 0x1a0) by (rewrite EF; lia).
assert (Hhi : crt_F cx + 0x1a0 + 8 <= frame_addr ly3 3 (c_pos cx) + fs_frame_bytes 3)
  by (rewrite EF, crt_frame3; lia).
destruct (crtD1_dec_fp_clear B ly3 S3 W3 (unpoison U3 memC) mdC (c_pos cx) (crt_F cx + 0x1a0) HAR3 Hin3 Hlo Hhi)
  as (HB1 & HB2 & _ & HB4).
rewrite EF, crt_frame3 in HB2.
assert (Hmod8 : (crt_F cx + 0x1a0) mod 8 = 0).
{ apply Z.mod_divide in HF32 as [qq Hqq]; [|lia]. rewrite Hqq.
  replace (qq * 32 + 0x1a0) with ((qq * 4 + 52) * 8) by lia. apply Z_mod_mult. }
assert (Hframe : exists cid pos, In (cid, pos) (frames S3) /\
  forall a, crt_F cx + 0x1a0 <= a < crt_F cx + 0x1a0 + 8 -> in_zr a (frame_rng ly3 (cid, pos))).
{ exists 3, (c_pos cx). split; [exact Hin3|]. intros a Ha. unfold in_zr, frame_rng. cbn [fst snd].
  rewrite EF, crt_frame3. lia. }
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (c_pos cx) HAR3 Hin3) as (_ & _ & Hfp & _).
rewrite EF, crt_frame3 in Hfp.
assert (Hpres : forall a, crt_F cx + 0x1a0 <= a < crt_F cx + 0x1a0 + 8 -> apresent (w_H W3) memC a).
{ intros a Ha. destruct (Hfp a ltac:(lia)) as (Hp & Hno).
  exact (fsw_apresent_notowned B ly3 S3 U3 W3 memC mdC a HARUC ltac:(lia) Hno Hp). }
assert (HV0' : val_mem tfibsegs (mrestrict (w_H W3) memC) (crt_F cx + 0x1a0) 8 0)
  by exact (val_mem_below (w_H W3) (ms_mem ms3) memC alloc_ceiling (crt_F cx + 0x1a0) 8 0 HSB ltac:(lia)
    ltac:(cbn; lia) HV0).
assert (Hsep : crt_F cx + 0x1a0 + 8 <= z \/
  z + Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1 <= crt_F cx + 0x1a0).
{ pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 (unpoison U3 memC) mdC (z - HEAD) (nz + HEAD) 3 (c_pos cx)
    HAR3 Hzin Hin3) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite EF, crt_frame3 in D. unfold HEAD in *. lia. }
pose proof (fs_glob_below W3 (ms_mem ms3) memC live peak cnt SIZE_MAXZ HSB HG) as HG'.
(* ---- the budgets: ticks, block bytes, g_live and g_count ---- *)
assert (HK3 : K_82268 cx + 3 <= 78)
  by (unfold K_822ac, EV_fuzz_malloc, EV_fuzz_free, EV_check_round_trip in HKroom; lia).
assert (Hev : st_nev S3 + dec_ev (WriterSpec.b64_enc (c_bs cx)) <= EV_MAX).
{ unfold dec_ev. rewrite Hdec. unfold EV_fuzz_malloc, EV_check_round_trip in *. lia. }
assert (Hroom2 : blocks_bytes S3 + (dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD) <= LIVE_MAX) by lia.
assert (Hns : 0 <= nsame).
{ assert (Hs : In (same, nsame) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPB)). apply in_or_app. right. apply in_or_app. left.
    right. right. left. reflexivity. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hs) as (_ & _ & _ & _ & _ & _ & Hm). lia. }
assert (Henc : 0 <= FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))).
{ unfold FSH_Fn_writer.enc_size.
  pose proof (Z.div_pos (Z.of_nat (length (c_bs cx)) + 2) 3 ltac:(lia) ltac:(lia)). lia. }
assert (Hdec3 : 3 <= dec_size (WriterSpec.b64_enc (c_bs cx))).
{ unfold dec_size. pose proof (Z.div_pos (Z.of_nat (length (WriterSpec.b64_enc (c_bs cx)))) 4 ltac:(lia) ltac:(lia)).
  lia. }
assert (HBS : FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + dec_size (WriterSpec.b64_enc (c_bs cx)) + nfile +
    rd_sum (Ddoc ++ Dback) <= blocks_bytes S3 - blocks_bytes (c_S cx)).
{ rewrite (blocks_bytes_bsum B ly3 S3), (blocks_bytes_bsum B (c_ly cx) (c_S cx)), (bsum_perm _ _ HPB).
  rewrite (bsum_app (ablocks B (c_ly cx) (c_S cx))), (bsum_app _ (rd_hblocks (Ddoc ++ Dback))), !bsum_cons,
    crtD1d_bsum_rdh.
  cbn [snd]. change (bsum []) with 0. cbv [HEAD]. lia. }
assert (Hlive2 : live + dec_size (WriterSpec.b64_enc (c_bs cx)) < 2 ^ 64) by (unfold HEAD in HLroom; lia).
pose proof (crtD1d_cnt_le_k cx) as HCK.
destruct Hquiet as (_ & Hc0 & Hc63).
assert (Hcnt63 : cnt < 2 ^ 63) by (unfold EV_check_round_trip in Hc63; lia).
(* ---- the decode ---- *)
pose proof (DECODE ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) z (crt_F cx + 0x1a0) (WriterSpec.b64_enc (c_bs cx))
  live peak cnt SIZE_MAXZ 0 HPREc HHD HFRL G10 G11 HCz') as HDEC.
lazymatch type of HDEC with ?P -> _ => assert (Hws : P) end.
{ (* R1: the second arm, z's own block of back's list *)
  right. left. exists z, nz. split; [exact Hz0|]. split; [exact Hrz|]. split; [lia|].
  rewrite length_app. cbn [length]. lia. }
pose proof (fsw_range_addressable_below (w_H W3) (ms_mem ms3) memC (crt_F cx + 0x1a0) 8 HSB ltac:(lia) ltac:(lia)
  HRA) as HRAC.
specialize (HDEC Hws Hbok ltac:(unfold MALLOC_MAX, HEAD in Hzmax; lia) Hmod8 Hframe Hpres HRAC HV0' ltac:(lia) Hsep HG'
  Hev Hroom2 Hlive2 ltac:(lia)).
exists (FS_PSTAT_FP ++ [(crt_F cx + 0x1a0, crt_F cx + 0x1a0 + 8)]), 1.
lazymatch type of HDEC with SRr _ _ _ (fun W' c' => _ \/ _ \/ @?C W' c') => exists C end.
split.
{ (* the refused arm needs cnt = SIZE_MAX, the bad-text arm b64_dec zs = None: only the success arm is left *)
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
(* ---- the heads after the call: U3's, and got's ---- *)
assert (HH' : fs_heads B ly' S' (U3 ++ [(q - HEAD, HEAD)])).
{ intros rr Hrr. apply in_app_or in Hrr as [Hrr|[<-|[]]].
  - destruct (HHD rr Hrr) as (E16 & m & Hm & Hm16). split; [exact E16|]. exists m.
    split; [rewrite Qab; apply in_or_app; left; exact Hm | exact Hm16].
  - split; [reflexivity|]. exists (dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD).
    split; [rewrite Qab; apply in_or_app; right; left; reflexivity|].
    pose proof (req_size_pos (dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrq).
    unfold HEAD in *. lia. }
(* ---- the data facts across the call: at the call site by same_below, then by the callee's journal ---- *)
assert (BLr : forall p kk, fs_rblock tfibsegs B ly3 S3 W3 (ms_mem ms3) p kk -> fs_rblock tfibsegs B ly3 S3 W3 memC p kk)
  by (intros p kk H; exact (fs_rblock_below B ly3 S3 W3 _ mdC _ _ p kk HAR3 HSB H)).
assert (HRB : forall p kk x, fs_rblock tfibsegs B ly3 S3 W3 memC p kk -> p - HEAD <= x < p + kk ->
  ~ inFP (FS_PSTAT_FP ++ [(crt_F cx + 0x1a0, crt_F cx + 0x1a0 + 8)]) x).
{ intros p kk x (Hin & _ & Hkk & _) Hx. apply (HB1 (p - HEAD) (kk + HEAD) x Hin).
  pose proof (req_size_pos (kk + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr). unfold HEAD in *. lia. }
assert (KR : forall p kk, fs_rblock tfibsegs B ly3 S3 W3 memC p kk -> fs_rblock tfibsegs B ly' S' W' mem' p kk).
{ intros p kk Hp. eapply (@fs_rblock_kept_call rc SK B);
    [exact HJc | exact HARUC | exact OK' | exact PO' | | exact Hp].
  intros x Hx. exact (HRB p kk x Hp Hx). }
assert (HFO : forall v, crt_F cx <= v -> v + 56 <= crt_F cx + 0x1a0 ->
  forall x, v <= x < v + 56 -> ~ inFP (FS_PSTAT_FP ++ [(crt_F cx + 0x1a0, crt_F cx + 0x1a0 + 8)]) x).
{ intros v Hv1 Hv2 x Hx. apply HB2; lia. }
assert (HOdocC : pobj tfibsegs B ly3 S3 W3 memC (crt_F cx + 0x20))
  by exact (pobj_below B ly3 S3 W3 _ mdC _ _ _ HAR3 HSB HOdoc).
assert (HObackC : pobj tfibsegs B ly3 S3 W3 memC (crt_F cx + 0x140))
  by exact (pobj_below B ly3 S3 W3 _ mdC _ _ _ HAR3 HSB HOback).
assert (HTdocC : rtree tfibsegs B ly3 S3 W3 memC (crt_F cx + 0x20)
    (PjTree.JObj (check_round_trip_stages_b.crt_doc (WriterSpec.b64_enc (c_bs cx)))) Ddoc)
  by exact (rnode_below B ly3 S3 W3 (unpoison U3 memC) mdC (ms_mem ms3) memC Ddoc (crt_F cx + 0x20) _ Ddoc HAR3 HSB
    ltac:(lia) ltac:(lia) HTdoc).
assert (HNbackC : rnode tfibsegs B ly3 S3 W3 memC (Ddoc ++ Dback) (crt_F cx + 0x140) tback Dback)
  by exact (rnode_below B ly3 S3 W3 (unpoison U3 memC) mdC (ms_mem ms3) memC (Ddoc ++ Dback) (crt_F cx + 0x140) tback
    Dback HAR3 HSB ltac:(lia) ltac:(lia) HNback).
assert (HOdoc' : pobj tfibsegs B ly' S' W' mem' (crt_F cx + 0x20)).
{ eapply (@pobj_kept_call rc SK B);
    [exact HJc | exact HARUC | exact OK' | exact PO' | | exact HB4 | exact HH' | exact HOdocC].
  apply HFO; lia. }
assert (HOback' : pobj tfibsegs B ly' S' W' mem' (crt_F cx + 0x140)).
{ eapply (@pobj_kept_call rc SK B);
    [exact HJc | exact HARUC | exact OK' | exact PO' | | exact HB4 | exact HH' | exact HObackC].
  apply HFO; lia. }
assert (HTdoc' : rtree tfibsegs B ly' S' W' mem' (crt_F cx + 0x20)
    (PjTree.JObj (check_round_trip_stages_b.crt_doc (WriterSpec.b64_enc (c_bs cx)))) Ddoc).
{ eapply (@rtree_kept_call rc SK B);
    [exact HJc | exact HARUC | exact OK' | exact PO' | apply HFO; lia | | exact HOdocC
    | exact HTdocC].
  intros a kk x Hak Hx. destruct HTdocC as (_ & HBd & _). exact (HRB a kk x (HBd a kk Hak) Hx). }
assert (HNback' : rnode tfibsegs B ly' S' W' mem' (Ddoc ++ Dback) (crt_F cx + 0x140) tback Dback).
{ eapply (@rnode_kept_call rc SK B);
    [exact HJc | exact HARUC | exact OK' | exact PO' | apply HFO; lia | | exact HObackC
    | exact HNbackC].
  intros a kk x Hak Hx. destruct HNbackC as (_ & HBd & _). exact (HRB a kk x (HBd a kk Hak) Hx). }
(* the length cell's shadow: a byte of crt's frame's shadow, off the footprint *)
assert (HRA' : range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF (crt_F cx + 0x1a0) 8).
{ intros x Hx. destruct (HRAC x Hx) as (sv & Esv & Hok). exists sv. split; [|exact Hok].
  rewrite <- Esv.
  eapply (@fsw_journal_kept_shadow rc SK B);
    [exact HJc | exact HARUC | exact OK' | exact PO' | exact HB4 | exact HH' | |].
  - right. exists 3, (c_pos cx). split; [exact Hin3|]. rewrite EF, crt_frame3. lia.
  - destruct (in_ush U3 (shadow_of_addr SHADOW_OFF x)) eqn:Eu; [|reflexivity]. exfalso.
    pose proof HARUC as (_ & _ & HPU3). pose proof (HPU3 _ Eu) as E247. rewrite Esv in E247.
    injection E247 as ->. unfold saddr_ok in Hok. lia. }
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
(* ---- crtD1_INV_82274 ---- *)
unfold crtD1_INV_82274. cbn [ms_mem mkst].
split; [rewrite (PE 18%nat ltac:(lia)); exact E18|].
split; [rewrite (PE 20%nat ltac:(lia)); exact E20|].
split; [rewrite (PE 21%nat ltac:(lia)); exact E21|].
split; [rewrite (PE 26%nat ltac:(lia)); exact E26|].
split; [rewrite (PE 27%nat ltac:(lia)); exact E27|].
exists same, nsame, file, nfile, back, q, Dback, Ddoc, tback, (live + dec_size (WriterSpec.b64_enc (c_bs cx))),
  (Z.max peak (live + dec_size (WriterSpec.b64_enc (c_bs cx)))), ((cnt + 1) mod 2 ^ 64).
split; [rewrite (PE 22%nat ltac:(lia)); exact E22|].
split; [rewrite (PE 24%nat ltac:(lia)); exact E24|].
split; [rewrite (PE 25%nat ltac:(lia)); exact E25|].
split; [rewrite (ew_Ereg_nat regs' (crt_extra cx) 10 10%bv eq_refl); exact Q10|].
split; [exact Qq|].
split.
{ rewrite Qab. eapply Permutation_trans; [apply Permutation_app_tail; exact HPB|].
  rewrite <- !app_assoc. apply Permutation_app_head. cbn [app].
  do 5 apply perm_skip. apply Permutation_sym, Permutation_cons_append. }
split.
{ eapply Permutation_trans; [apply Permutation_app_tail; exact HPU|].
  rewrite <- !app_assoc. apply Permutation_app_head. cbn [app].
  do 3 apply perm_skip. apply Permutation_sym, Permutation_cons_append. }
split; [exact HH'|].
split.
{ exact (conj (KR _ _ (BLr _ _ HRtext)) (conj (KR _ _ (BLr _ _ HRback))
    (conj HTdoc' (conj HNback' (conj Hdep (conj HOback' HOdoc')))))). }
split; [exact (KR _ _ (BLr _ _ HRfile))|].
split; [exact Qrb|].
split; [exact Qzb|].
split; [exact Qval|].
split; [exact HRA'|].
split; [exact Qglob|].
split; [lia|].
split; [rewrite Hbb'; unfold LIVE_82274; lia|].
split; [rewrite Z.mod_small by lia; unfold CNT_82274; lia|].
split; [unfold K_82274, EV_fuzz_malloc; lia|].
(* the remaining allowance: the decode's one tick is crt_INV_82268's EV_fuzz_malloc *)
unfold EV_fuzz_malloc in Hrem. lia.
Qed.

(* ---- SEGMENT 30 ---- *)
Lemma crtD1_seg30 :
  crt_from SK B (crt_ss_ret 0x82274 crt_cs1 crt_csF) (crtD1_INV_82274 B) ->
  crt_from SK B (crt_ss_ret 0x82268 crt_cs1 crt_csF) (crt_INV_82268 B).
Proof.
intros NEXT.
assert (HSTK0 : 0 <= STK_preset_base64_decode) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSTK1 : STK_preset_base64_decode + 208 <= STK_check_round_trip) by (apply Z.leb_le; vm_compute; reflexivity).
refine (crtD1d_seg_call_bz 0x82268 A_preset_base64_decode 0x82274 crtD1d_sb30 crtD1d_sc30 (crt_INV_82268 B)
  (crtD1_INV_82274 B) STK_preset_base64_decode crtD1d_br30 crtD1d_run30 crtD1d_site30 ltac:(lia) eq_refl HSTK0 HSTK1
  _ crtD1d_hcall30 NEXT).
intros cx E k ly3 S3 U3 W3 ms3 md3 HINV.
destruct HINV as (_ & _ & _ & _ & _ & _ & same & nsame & file & nfile & back & z & zs & Dback & Ddoc & tback &
  live & peak & cnt & _ & _ & _ & E10 & Hz0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HCz & _).
destruct HCz as (_ & Hz4096 & Hzceil & _).
pose proof (@alloc_ceiling_lt rc) as HC47.
exists z. split; [exact E10|]. split; [lia | exact Hz0].
Qed.
End s30.

Print Assumptions crtD1d_seg_call_bz.
Print Assumptions crtD1d_hcall30.
Print Assumptions crtD1_seg30.
About crtD1_seg30.
