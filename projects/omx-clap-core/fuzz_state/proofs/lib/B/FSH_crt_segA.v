(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: IMAGE B (fs.asan-ubsan) walk of parse_value 0x82fcc, stage lemmas. HEADER: see
   FSW_parse_value_holds.v (the composition into parse_value_spec k, the rule-24 line, the reuse search, the port
   sources, every pc walked and every report site). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_parse_value.v, with its addresses and numbers changed; 2709 of its 2837 lines of code are new or changed and 1228 lines of the source are left out. *)
(* check_round_trip (fs.asan-ubsan 0x81b9c), build B: the B twin of lane A0 of its ASan walk, entry (0x81b9c) ->
   crt_INV_81d0c (B 0x81e18) / crt_INV_81f58 (B 0x820a4) - segment 0, the class-3 fake-frame grant at 0x81c10 and the
   resume at 0x81c14, and segments 1-5 (the frame header and shadow, preset_base64_encode, malloc want, strlen (input),
   malloc same, and the stretch to the head of the expected_text loop or, when |bs| = 0, to its join).
   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from 6ae0548ca1d)
   rule 24: proves no function (kind: segment lemmas of check_round_trip's walk, PORTED from 1ab57ca7ad7) - RT : CrtRt B
   (not FsRt), each fr_X tfibsegs B RT now crt_fr_X B RT (a working branch 1ab57ca7ad7).
   Port source: a working branch 6ae0548ca1d proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segA.v (3122 lines,
   crtA_from_entry, on A base v32 9ffe6bce6eb + crt6_keepA ff3fb23bb7b), itself PORTED from a working branch
   d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_top.v crt_run_pro :953 / crt_run_sm :1017 /
   crt_run_setup :1129 / crt_run_side :1285, check_round_trip_runs.v crt_pro :42 / crt_side_frame :92, and the stage
   steps check_round_trip_sd0.v .. sd2.v over the cuts St0 :215 / St1 :229 / St2 :244 of check_round_trip_stdefs.v (the
   function's rule-24 line, with the full reuse search and the checker's CONFIRM, a Theorem Labs lane 04:3xZ, is lines 6-21 of
   (internal path)). Same Definition / Lemma names and statement shapes as the A
   file, over image B (lib/B/YB1v.v tfibsegs, fs.asan-ubsan sha256 5ac5ce0954f87e2d050c481b7b0599cfd55ef554eadc008e51491f44c053d204;
   S0 a9edd281227's lib/B kit; the B interface lib/B/FSH_crt_base.v v32 / FSH_crt_site.v; lib/B/FSH_crt_keepA0.v's
   crt6_keepA, a Theorem Labs lane's B twin). Every pc, return address, register, slot and image constant RE-MEASURED on B
   (capstone over the pinned fs.asan-ubsan, (internal path)) and mapped from A by
   instruction meaning (crt.A2B.tsv, crt.calls.tsv). A new file: no licence lines.

   A name -> A pc -> B pc (names keep their A form, content is B's):
     crtA_ss0 / crtA_entry / crtA_seg0        entry 0x81a9c -> 0x81b9c
     crtA_ss1 / crtA_sm_site                  the call of __asan_stack_malloc_3: jal 0x81b10 -> 0x81c10 (callee 0x3d7f8),
                                              ra 0x81b14 -> 0x81c14
     crtA_ss2 / crtA_grant                    the resume 0x81b14 -> 0x81c14
     crtA_ss3 / crtA_seg1 / crtA_site3        segment 1 to the encode call: jal 0x81c80 -> 0x81d7c (callee 0x84700)
     crtA_INV_81c84 / crtA_to_81c84           0x81c84 -> 0x81d80 (return of preset_base64_encode)
     crtA_INV_81ca8 / crtA_ssC2 / crtA_seg2   0x81ca8 -> 0x81da4 (return of malloc want; jal 0x81da0, PC_malloc 0x530e4)
     crtA_INV_81cb4 / crtA_ssC3 / crtA_seg3   0x81cb4 -> 0x81db0 (return of strlen; jal 0x81dac, PC_strlen 0x426c4)
     crtA_INV_81cbc / crtA_ssC4 / crtA_seg4   0x81cbc -> 0x81db8 (return of malloc same; jal 0x81db4)
    crtA_ss5 .. crtA_seg5 / crtA_exit5       segment 5, 0x81cbc -> 0x81db8 .. the loop head 0x81d0c -> 0x81e18 (crt_INV_81d0c,
                                             at crt_ss_ret 0x81e18 crt_cs1L crt_csF: B's loop arm spills 0x28 := En and
                                             0x38 := F; A: crt_cs1e) and the l = 0 bypass `beqz s4` 0x81cdc -> 0x81dd8 to
                                             0x81f58 -> 0x820a4 (crt_INV_81f58, crt_ss_ret 0x820a4 crt_cs1e crt_csF); the
                                             loop arm crosses B's UBSan test 0x81e10 `bltu ~bd, 0` (never taken; A has none)
     crtA_kcell                               the mulhu constant 0xaaaaaaaaaaaaaaab at 0x10320 (B 0x81d84 `auipc` + 0x59c;
                                              the same cell as A's)
   The trap arm of the walk's guards is 0x824e4 (A 0x824b8).

   B's prologue allocates registers differently from A's after the grant, and every difference is carried here:
   - the grant's result: B 0x81c14 `mv s3, a0`, 0x81c20 `mv s6, s3`, 0x81c24 `bnez s3`; F lives in s6 = x22 AND s3 = x19
     until segment 5 (A: a4 and s7 = x23);
   - the frame's shadow address SF: B s10 = x26 (0x81c54 `srli s10, s6, 3`, 0x81c78 `add s10, s10, s2`; A: s3 = x19),
     so crtA_site3 / crtA_after_call read x26 (crt_E's SF atom is 26 on B);
   - segment 1 stores ONE s1 slot, 0x50 := F (0x81c44; A: 0x10 and 0x50), so crtA_cs1a = [0x50 := F]; the text spill is
     slot 0x18 (0x81d80; A 0x30), so crtA_cs1b = [0x18 := text; 0x50 := F];
   - En = s11 = x27 (0x81d98 `andi s11, a0, -4`; A: s6 = x22), want = s7 = x23 (0x81da4 `mv s7, a0`; A: s10 = x26);
   - crtA_core carries x22 = F and x19 = F (A: x23 = F), one conjunct more than A's.

   SK is an EXPLICIT variable: B's instance (fsB_sink_head / YE2k.tfib_sink_head) is passed by whoever instantiates these
   lemmas; nothing here infers it. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YG05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_crt_tbl
FSH_crt_base FSH_crt_site.
(* (A: lib/A/FSH_Fn_entry.v is not imported; B has no FSH_Fn_entry.v. The two lines of its fs_fake_granted the grant
   needs are proved here over YG01's count_cid and YG00's fs_frames, as on A.) *)
(* these files are REQUIRED, not IMPORTED: several of their lemma names clash with the imported kits', so their lemmas
   are reached qualified (FSW_frame., FSW_rd., FSW_strkit., FSW_malloc_free., FSH_crt_keepA0.) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSW_frame FSW_frame3 FSH_Fn_writer FSW_malloc_free
  FSW_rd FSW_strkit FSH_crt_keepA0 YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState check_round_trip_loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a sink instance resolved
   in this file's scope; SK is passed explicitly instead *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* membership of a chunk in a literal chunk list *)
Ltac crtA_in := cbn [In]; repeat (first [ left; reflexivity | right ]).

(* ---- pure facts of this walk ---- *)
(* the stack budget crt passes its interceptor callees, checked by computation; STK_check_round_trip itself is read
   through the base's crt_STK_eq at each use (no STK_* numeral in this file, owner 08:1xZ) *)
Lemma crtA_astack : 0 <= ASTACK /\ ASTACK + 208 <= STK_check_round_trip.
Proof.
assert (H : (0 <=? ASTACK) && (ASTACK + 208 <=? STK_check_round_trip) = true) by (vm_compute; reflexivity).
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. split; assumption.
Qed.
(* the class-3 frame is granted: at most FRL_CHECK = 1 frame is live at 0x81c10 (A 0x81b10; A's
   FSH_Fn_entry.fs_fake_granted) *)
Lemma crtA_count_cid_le : forall cid (l : list (Z * Z)), count_cid cid l <= Z.of_nat (length l).
Proof.
intros cid l. induction l as [|[c p] t IH]; cbn [count_cid length]; [lia|]. destruct (c =? cid); lia.
Qed.
Lemma crtA_grant_room : forall l : list (Z * Z), Z.of_nat (length l) <= FRL_CHECK -> count_cid 3 l < fs_frames 3.
Proof.
intros l Hl. pose proof (crtA_count_cid_le 3 l) as Hle. unfold fs_frames, kStackSizeLog. rewrite Z.shiftl_1_l.
assert (Hp : 2 ^ 11 <= 2 ^ (20 - 6 - 3)) by (apply Z.pow_le_mono_r; lia).
unfold FRL_CHECK in Hl. lia.
Qed.
(* crt's callees run with crt's own frame on top: at most FRL_CRT_CALLEE = 2 frames *)
Lemma crtA_frames_callee : forall (f : Z * Z) (l : list (Z * Z)),
  Z.of_nat (length l) <= FRL_CHECK -> Z.of_nat (length (f :: l)) <= FRL_CRT_CALLEE.
Proof. intros f l Hl. cbn [length]. unfold FRL_CHECK, FRL_CRT_CALLEE in *. lia. Qed.
(* fs_heads depends only on ablocks (a Theorem Labs lane's crcs_heads) *)
Lemma crtA_heads : forall B ly S ly' S' U,
  ablocks B ly' S' = ablocks B ly S -> FSupoisonU.fs_heads B ly S U -> FSupoisonU.fs_heads B ly' S' U.
Proof. intros B ly S ly' S' U E H r Hr. rewrite E. exact (H r Hr). Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.

(* ---- B image facts (RELOC discharges them; the cells are S0's lib/B/FSW_K.v fs_D_GOT_uar / fs_D_uar_cell, image
   B's own) ---- *)
Hypothesis HSS : FsShadowSyms B.
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.
Hypothesis HENV : api_env tfibsegs B.
(* ---- the runtime contracts (FSH_crt_base.v CrtRt: crt_fr_stack_malloc_3 for the grant, crt_fr_strlen / crt_fr_strcmp /
   crt_fr_malloc for segments 2-4, 6, 8, 9) ---- *)
Hypothesis RT : CrtRt B.

(* model_laws and stack_malloc_progressP are NOT hypotheses: they are facts of fs's universe, which AR carries
   (YG0n.am_universe) and YG05 proves. *)
Lemma crtA_ML : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md -> model_laws (as_universe B).
Proof. intros ly S W mem md HAR. exact (model_laws_ok (as_universe B) (am_universe _ _ _ _ (proj1 HAR))). Qed.
Lemma crtA_SMP : stack_malloc_progressP B.
Proof. intros s cid Hwf Hc Hcnt. exact (stack_malloc_progress (as_universe B) s cid Hwf Hc Hcnt). Qed.

(* ================= the entry state ================= *)
(* fss0T (the two shadow-base cells) with the use-after-return cells and the 0xc0-byte frame of the prologue *)
Definition crtA_ss0 : sstate := fss0T_args A_check_round_trip 192 fs_uar_regions [].

Lemma crtA_entry : forall ly S U (W : world tfibsegs) regs mem md ch,
  afn_preU tfibsegs B STK_check_round_trip ly S U W regs mem md ch ->
  st_ok tfibsegs (Ereg regs fs_extraT) crtA_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_check_round_trip) mem (seg_rom tfibsegs))).
Proof.
intros ly S U W regs mem md ch HPRE.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _). pose proof crt_STK_eq as FS; unfold crt_STK in FS.
assert (E2 : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
apply (fsw_entryT_args B _ 192 ly S U W regs mem md ch _ fs_uar_regions [] (proj1 HSS) (proj2 HSS) HPRE).
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

(* ================= segment 0: the prologue, the re-align and the two GOT loads ================= *)
(* the state at the call of __asan_stack_malloc_3 (0x81c10 -> PC_stack_malloc_3 0x3d7f8; A 0x81b10): MEASURED
   (vm_compute) sp and s1 hold the re-aligned `SAlu AND (SOff 2 (-192)) (SLit (-32))`, a0 = 0x1e0, a2 = 1 (so `beqz a2`
   at 0x81c08 is not taken), ra = 0x81c14, s2 = the shadow base atom 32, s4 / s5 / s9 = the entry a2 / a1 / a0 *)
Definition crtA_ss1 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL PC_stack_malloc_3 crtA_ss0).

(* the run's write window: the prologue's 0xc0-byte stack region (atom 2 = sp0, window [-192, 0)) and four read-only
   image cells - named awr_ok_cons_* steps, no awr_ok_tac (its azlit_tac starts with an unrestricted cbv) *)
Lemma crtA_awr0 : forall E sp0 FP bl0 blc ly own fr0,
  bv_unsigned (ew E 2) = sp0 ->
  awr_ok tfibsegs B E (ss_mem crtA_ss0) STK_check_round_trip sp0 FP bl0 blc ly own fr0.
Proof.
intros E sp0 FP bl0 blc ly own fr0 E2. pose proof crt_STK_eq as FS; unfold crt_STK in FS.
unfold crtA_ss0, fss0T_args, fsT_regions_args, fsT_regions, fs_uar_regions. cbn [ss_mem app].
eapply (awr_ok_cons_stack tfibsegs B E (fstk 192) _ STK_check_round_trip sp0 FP bl0 blc ly own fr0 2%nat);
  [reflexivity | exact E2 | unfold fstk; cbn [YP09.r_wlo]; lia | unfold fstk; cbn [YP09.r_whi]; lia |].
apply awr_ok_cons_ro; [unfold fs_got_region; cbn [YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [unfold fs_bcell_region; cbn [YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [unfold fs_got_uar_region; cbn [YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [unfold fs_uar_cell_region; cbn [YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_nil.
Qed.

Lemma crtA_seg0 : forall ly S U (W : world tfibsegs) regs mem md ch FP (Q : world tfibsegs -> config -> Prop),
  afn_preU tfibsegs B STK_check_round_trip ly S U W regs mem md ch ->
  (forall ms mat,
     st_ok tfibsegs (Ereg regs fs_extraT) crtA_ss1 (restrict (w_H W) ms) ->
     ajournal tfibsegs B STK_check_round_trip (spZ regs) FP ly S W (unpoison U mem) md [] ly S W
       (unpoison U (ms_mem ms)) (with_vm_backing (m_vm_lazy md) mat md) 0 ->
     ARU tfibsegs B ly S U W (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) ->
     frame_of (Ereg regs fs_extraT) (ss_mem crtA_ss0) mem (ms_mem ms) ->
     frame_of (Ereg regs fs_extraT) (ss_mem crtA_ss0) (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) ->
     SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_check_round_trip regs mem md) Q.
Proof.
intros ly S U W regs mem md ch FP Q HPRE K.
pose proof (crtA_entry ly S U W regs mem md ch HPRE) as HS.
pose proof (fsw_ARU B _ ly S U W regs mem md ch HPRE) as HARU.
pose proof (ajournal_init tfibsegs B STK_check_round_trip FP ly S W regs (unpoison U mem) md ch (proj1 HPRE)) as HJ.
assert (Usp : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
(* the run, as a closed equation proved first; crtA_ss1 is its result by definition *)
assert (Hrun : sym_run_toN tfibsegs crt_tbl FUEL PC_stack_malloc_3 crtA_ss0 = (crtA_ss1, RS_running))
  by (vm_compute; reflexivity).
unfold cfg_at. change (w64 A_check_round_trip) with (Z_to_bv 64 A_check_round_trip).
eapply (fsw_run_to_AJU B crt_tbl crt_tbl_ok W FUEL PC_stack_malloc_3 (Ereg regs fs_extraT) crtA_ss0 crtA_ss1 RS_running
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HARU HJ (crtA_awr0 _ _ _ _ _ _ _ _ Usp)).
intros ms' mat' HS' HJ' HARU' HF HFr _.
exact (K ms' mat' HS' HJ' HARU' HF HFr).
Qed.

(* the registers at the call of __asan_stack_malloc_3, read off crtA_ss1; each register equation of the state is a
   closed equation proved first *)
Lemma crtA_sm_site : forall ly S U (W : world tfibsegs) regs mem md ch ms,
  afn_preU tfibsegs B STK_check_round_trip ly S U W regs mem md ch ->
  st_ok tfibsegs (Ereg regs fs_extraT) crtA_ss1 (restrict (w_H W) ms) ->
  YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 (32 * ((spZ regs - 192) / 32)) /\
  YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 (32 * ((spZ regs - 192) / 32)) /\
  spZ regs - 208 <= 32 * ((spZ regs - 192) / 32) <= spZ regs - 192 /\
  (32 * ((spZ regs - 192) / 32)) mod 32 = 0 /\ (32 * ((spZ regs - 192) / 32)) mod 16 = 0 /\
  YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 0x81c14 /\ YK11.getr (ms_regs ms) 10%bv = Z_to_bv 64 0x1e0 /\
  YK11.getr (ms_regs ms) 3%bv = YK11.getr regs 3%bv /\ YK11.getr (ms_regs ms) 4%bv = YK11.getr regs 4%bv /\
  YK11.getr (ms_regs ms) 8%bv = YK11.getr regs 2%bv /\ YK11.getr (ms_regs ms) 18%bv = Z_to_bv 64 SHADOW_OFF /\
  YK11.getr (ms_regs ms) 20%bv = YK11.getr regs 12%bv /\ YK11.getr (ms_regs ms) 21%bv = YK11.getr regs 11%bv /\
  YK11.getr (ms_regs ms) 25%bv = YK11.getr regs 10%bv.
Proof.
intros ly S U W regs mem md ch ms HPRE HS.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _). pose proof crt_STK_eq as FS; unfold crt_STK in FS.
assert (G2 : sr_get (ss_regs crtA_ss1) 2%bv = SAlu ALU_AND (SOff 2 (-192)) (SLit (-32))) by (vm_compute; reflexivity).
assert (G9 : sr_get (ss_regs crtA_ss1) 9%bv = SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-192)) (SLit (-32))) (SLit 0))
  by (vm_compute; reflexivity).
assert (G1 : sr_get (ss_regs crtA_ss1) 1%bv = SLit 0x81c14) by (vm_compute; reflexivity).
assert (G10 : sr_get (ss_regs crtA_ss1) 10%bv = SLit 0x1e0) by (vm_compute; reflexivity).
assert (G3 : sr_get (ss_regs crtA_ss1) 3%bv = SOff 3 0) by (vm_compute; reflexivity).
assert (G4 : sr_get (ss_regs crtA_ss1) 4%bv = SOff 4 0) by (vm_compute; reflexivity).
assert (G8 : sr_get (ss_regs crtA_ss1) 8%bv = SOff 2 0) by (vm_compute; reflexivity).
assert (G18 : sr_get (ss_regs crtA_ss1) 18%bv = SOff 32 0) by (vm_compute; reflexivity).
assert (G20 : sr_get (ss_regs crtA_ss1) 20%bv = SOff 12 0) by (vm_compute; reflexivity).
assert (G21 : sr_get (ss_regs crtA_ss1) 21%bv = SOff 11 0) by (vm_compute; reflexivity).
assert (G25 : sr_get (ss_regs crtA_ss1) 25%bv = SOff 10 0) by (vm_compute; reflexivity).
set (E := Ereg regs fs_extraT) in *.
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs)) by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl);
  unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (fsw_realign_facts (spZ regs - 192) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
  as (F1 & F2 & F3).
set (sp1 := 32 * ((spZ regs - 192) / 32)) in *.
assert (R2 : YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 sp1).
{ exact (fsw_realign_val E crtA_ss1 (restrict (w_H W) ms) 2%bv 2 (-192) (spZ regs) HS G2 E2
    ltac:(unfold spZ; apply u64_range) ltac:(lia)). }
assert (R9 : YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 sp1).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E crtA_ss1 ms 9%bv HS), G9.
  rewrite denot_lit_U, U_SAlu. f_equal. cbn [zalu_raw]. rewrite U_SLit.
  assert (UA : YP0e.U E (SAlu ALU_AND (SOff 2 (-192)) (SLit (-32))) = sp1).
  { unfold YP0e.U.
    rewrite (denot_and_m32 E 2 (spZ regs) (-192) E2 ltac:(lia) ltac:(lia) ltac:(unfold spZ; apply u64_range)).
    apply wz. lia. }
  rewrite UA. change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
split; [exact R2|]. split; [exact R9|]. split; [lia|]. split; [exact F2|]. split; [exact F3|].
split; [exact (fsw_reg_lit _ E _ ms 1%bv 0x81c14 HS G1 ltac:(lia))|].
split; [exact (fsw_reg_lit _ E _ ms 10%bv 0x1e0 HS G10 ltac:(lia))|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 3%bv 3%bv 3 HS G3 eq_refl)|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 4%bv 4%bv 4 HS G4 eq_refl)|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 8%bv 2%bv 2 HS G8 eq_refl)|].
split.
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E crtA_ss1 ms 18%bv HS), G18, fsw_SOff0.
  subst E. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 20%bv 12%bv 12 HS G20 eq_refl)|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 21%bv 11%bv 11 HS G21 eq_refl)|].
exact (fsw_reg_atom _ regs fs_extraT _ ms 25%bv 10%bv 10 HS G25 eq_refl).
Qed.

(* ================= the grant at 0x81c10 and the resume at 0x81c14 (A 0x81b10 / 0x81b14) ================= *)
(* the env of the walk between the grant and the first call: FSW_K's ATOM CONVENTION with a Theorem Labs lane's crt_extra layout
   (atom 32 the shadow base, 33..45 the thirteen saved registers, 46 the flag address, 47 the frame address) and one
   walk atom, 48, for the frame's shadow address - the value the prologue computes into s10 at 0x81c54 / 0x81c78 (A:
   s3 at 0x81b58 / 0x81b7c). The frame region is based on atom 10 here, not on 47: between the grant and 0x81c70 the
   code addresses the frame through s3 / s6 (0x81c14 `mv s3, a0`, 0x81c20 `mv s6, s3`; A: a0 / a4), which the engine
   reads as atom 10, and a region is found by its base atom. Atoms 10 and 47 hold
   the same value (the grant's a0), so the boundary state a Theorem Labs lane fixes (crt_ss_ret, frame at atom 47) is built from
   this one at the call's return, not here. *)
Definition crtA_extra (regs : bvmap 5 word) (FL F SF : Z) : list word :=
  [Z_to_bv 64 SHADOW_OFF] ++ map (YK11.getr regs) crt_saved ++ [Z_to_bv 64 FL; Z_to_bv 64 F; Z_to_bv 64 SF].
Definition crtA_shadow_region : YP09.region :=
  YP09.mkRegion (Some 48%nat) 0 (fs_frame_bytes 3 / 8) 0 (fs_frame_bytes 3 / 8) [].
(* the three facts the run needs beyond fsw_resume_ss's own two: the re-aligned sp (atom 9), the frame's shadow
   address (atom 48) and the shadow base (atom 18, the s2 the prologue loaded), and the alias that rewrites the
   address the code computes, `(s6 >> 3) + s2` with s6 = a0 (B 0x81c54 / 0x81c78; A `(a4 >> 3) + s2`), to atom 48
   (YP0i.shadow_decl_ok) *)
Definition crtA_facts : facts :=
  mkFacts [(18%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (48%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 2);
           (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47) 5)]
    [] [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 18 0), SOff 48 0)].
Definition crtA_ss2 : sstate :=
  mkSS 0x81c14 sr_atoms
    (crtA_shadow_region :: FSW_frame3.fsw_resume_regions (-104) 0 crt_sv_chunks 9 0x10 0x58 10 (SOff 46 0) 3) None crtA_facts.

(* crtA_ss1's stack region (its first region), as a closed literal *)
Definition crtA_stk1 : YP09.region := Eval vm_compute in nth 0 (ss_mem crtA_ss1) (fstk 0).

(* the thirteen saved words, read on the call-site memory in the resumed env: the same values the prologue stored,
   which crtA_ss1's stack region holds as the chunks at s0 - 8 (k + 1) *)
Lemma crtA_saved_val : forall ly S U (W : world tfibsegs) regs mem md ch ms,
  afn_preU tfibsegs B STK_check_round_trip ly S U W regs mem md ch ->
  st_ok tfibsegs (Ereg regs fs_extraT) crtA_ss1 (restrict (w_H W) ms) ->
  forall k, (k < 13)%nat ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 8 * (Z.of_nat k + 1)) 8
    (bv_unsigned (YK11.getr regs (nth k crt_saved 0%bv))).
Proof.
intros ly S U W regs mem md ch ms HPRE HS k Hk.
assert (N0 : nth_error (ss_mem crtA_ss1) 0 = Some crtA_stk1) by (vm_compute; reflexivity).
pose proof (fsw_region_nth (Ereg regs fs_extraT) crtA_ss1 (restrict (w_H W) ms) 0 crtA_stk1 HS N0) as HR.
cbn [restrict ms_mem] in HR. unfold crtA_stk1 in HR.
assert (E2 : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
assert (DEN : forall (r : bv 5) (n : nat), Z.of_nat n = bv_unsigned r ->
  sv_denot (Ereg regs fs_extraT) (SOff n 0) = Z_to_bv 64 (bv_unsigned (YK11.getr regs r))).
{ intros r n Hn. rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT n r Hn). symmetry. apply Z_to_bv_bv_unsigned. }
assert (RNG : forall r : bv 5, 0 <= bv_unsigned (YK11.getr regs r) < 2 ^ (8 * Z.of_N 8))
  by (intros r; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply u64_range).
(* one instance of fsw_field per saved register, in the prologue's slot order (crt_saved) *)
lazymatch type of HR with
| region_ok _ _ _ (YP09.mkRegion (Some 2%nat) ?rlo ?rhi ?rwlo ?rwhi ?rcs) =>
  assert (AT : forall (n : nat) (r : bv 5) (od : Z), Z.of_nat n = bv_unsigned r ->
    In (YP09.mkChunk od (CVal 8 (SOff n 0))) rcs ->
    val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + od) 8 (bv_unsigned (YK11.getr regs r)))
  by (intros n r od Hn Hin;
      exact (fsw_field (Ereg regs fs_extraT) (mrestrict (w_H W) (ms_mem ms)) 2 (spZ regs) rcs rlo rhi rwlo rwhi od 8
        (SOff n 0) (bv_unsigned (YK11.getr regs r)) HR E2 Hin (DEN r n Hn) (RNG r) ltac:(cbn [Z.of_N]; lia)))
end.
destruct k as [|[|[|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]]]]; cbn [nth crt_saved];
  lazymatch goal with
  | |- val_mem _ _ (spZ regs - 8 * (Z.of_nat ?j + 1)) _ _ =>
      let od := eval cbn in (- 8 * (Z.of_nat j + 1)) in
      replace (spZ regs - 8 * (Z.of_nat j + 1)) with (spZ regs + od) by (cbn [Z.of_nat]; lia)
  | _ => idtac
  end.
- exact (AT 1%nat 1%bv (-8) eq_refl ltac:(crtA_in)).
- exact (AT 8%nat 8%bv (-16) eq_refl ltac:(crtA_in)).
- exact (AT 9%nat 9%bv (-24) eq_refl ltac:(crtA_in)).
- exact (AT 18%nat 18%bv (-32) eq_refl ltac:(crtA_in)).
- exact (AT 19%nat 19%bv (-40) eq_refl ltac:(crtA_in)).
- exact (AT 20%nat 20%bv (-48) eq_refl ltac:(crtA_in)).
- exact (AT 21%nat 21%bv (-56) eq_refl ltac:(crtA_in)).
- exact (AT 22%nat 22%bv (-64) eq_refl ltac:(crtA_in)).
- exact (AT 23%nat 23%bv (-72) eq_refl ltac:(crtA_in)).
- exact (AT 24%nat 24%bv (-80) eq_refl ltac:(crtA_in)).
- exact (AT 25%nat 25%bv (-88) eq_refl ltac:(crtA_in)).
- exact (AT 26%nat 26%bv (-96) eq_refl ltac:(crtA_in)).
- exact (AT 27%nat 27%bv (-104) eq_refl ltac:(crtA_in)).
- cbn [Z.of_nat] in Hk. lia.
Qed.

(* those thirteen words as the chunks of the resumed s0 region, in the resumed env (atom 33 + k holds the k-th saved
   register's entry value: crtA_extra's layout, which is a Theorem Labs lane's crt_extra) *)
Lemma crtA_saved_chunks : forall (W : world tfibsegs) regs0 regs2 extra (m : word -> option byte) sp0,
  (forall k, (k < 13)%nat -> ew (Ereg regs2 extra) (33 + k)%nat = YK11.getr regs0 (nth k crt_saved 0%bv)) ->
  bv_unsigned (ew (Ereg regs2 extra) 8) = sp0 ->
  (forall k, (k < 13)%nat ->
     val_mem tfibsegs m (sp0 - 8 * (Z.of_nat k + 1)) 8 (bv_unsigned (YK11.getr regs0 (nth k crt_saved 0%bv)))) ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 extra) m sp0) crt_sv_chunks.
Proof.
intros W regs0 regs2 extra m sp0 HE E8 HV.
apply Forall_forall. intros c Hc. unfold crt_sv_chunks in Hc.
apply in_map_iff in Hc as (k & <- & Hk). apply in_seq in Hk. cbn [fst snd] in Hk.
apply (chunk_ok_val tfibsegs (Ereg regs2 extra) m sp0 (- 8 * (Z.of_nat k + 1)) 8 (SOff (33 + k) 0)
  (bv_unsigned (YK11.getr regs0 (nth k crt_saved 0%bv)))).
- rewrite fsw_SOff0, (HE k ltac:(lia)). symmetry. apply Z_to_bv_bv_unsigned.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply u64_range.
- cbn [Z.of_N]. lia.
- cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
  replace (sp0 + - 8 * (Z.of_nat k + 1)) with (sp0 - 8 * (Z.of_nat k + 1)) by lia.
  exact (HV k ltac:(lia)).
Qed.

(* the saved-register atoms of crtA_extra: atom 33 + k holds the entry value of the k-th register of crt_saved *)
Lemma crtA_extra_saved : forall regs2 regs FL F SF k, (k < 13)%nat ->
  ew (Ereg regs2 (crtA_extra regs FL F SF)) (33 + k) = YK11.getr regs (nth k crt_saved 0%bv).
Proof.
intros regs2 regs FL F SF k Hk. replace (33 + k)%nat with (32 + S k)%nat by lia.
rewrite ew_Ereg_extra. unfold crtA_extra. cbn [app nth].
rewrite app_nth1 by (rewrite length_map; cbn; lia).
rewrite (nth_indep _ _ (YK11.getr regs 0%bv)) by (rewrite length_map; cbn; lia).
apply map_nth.
Qed.
Lemma crtA_extra_46 : forall regs2 regs FL F SF, ew (Ereg regs2 (crtA_extra regs FL F SF)) 46 = Z_to_bv 64 FL.
Proof. intros. change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra. reflexivity. Qed.
Lemma crtA_extra_47 : forall regs2 regs FL F SF, ew (Ereg regs2 (crtA_extra regs FL F SF)) 47 = Z_to_bv 64 F.
Proof. intros. change 47%nat with (32 + 15)%nat. rewrite ew_Ereg_extra. reflexivity. Qed.
Lemma crtA_extra_48 : forall regs2 regs FL F SF, ew (Ereg regs2 (crtA_extra regs FL F SF)) 48 = Z_to_bv 64 SF.
Proof. intros. change 48%nat with (32 + 16)%nat. rewrite ew_Ereg_extra. reflexivity. Qed.

Ltac crtA_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?q] => let z := eval vm_compute in (bv_unsigned q) in
    change (bv_unsigned q) with z end; lia.

(* ---- the grant (0x81c10 -> PC_stack_malloc_3 -> 0x81c14; A 0x81b10 / 0x81b14): FSW_frame.fsw_stack_malloc_atU at class 3 with
   FsRt.fr_stack_malloc_3, then FSW_frame3.fsw_resume_after_stack_mallocU for the s0 words, the s1 slots and the frame
   (atom 10 = the grant's a0) with its flag word, then the frame's shadow window at atom 48 (present and not runtime-owned
   by AR_frames_law, so writable on the machine's memory), the facts of atoms 9 / 48 / 18 and the shadow alias. Ported
   from d25a984c903 check_round_trip_top.v crt_run_sm :1017 (the call through its contract, the frame arm) and
   check_round_trip_runs.v crt_side_frame :92 (the arm whose `bnez a0` is taken on 0 < fr; here the frame fact
   4096 <= F lets the engine decide it in the next run; B tests s3 = a0 there, 0x81c24 `bnez s3`). ---- *)
Lemma crtA_grant : forall ly S U (W : world tfibsegs) regs mem md ch FP ms mat (Q : world tfibsegs -> config -> Prop),
  afn_preU tfibsegs B STK_check_round_trip ly S U W regs mem md ch ->
  Z.of_nat (length (frames S)) <= FRL_CHECK ->
  st_ok tfibsegs (Ereg regs fs_extraT) crtA_ss1 (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK_check_round_trip (spZ regs) FP ly S W (unpoison U mem) md [] ly S W
    (unpoison U (ms_mem ms)) (with_vm_backing (m_vm_lazy md) mat md) 0 ->
  ARU tfibsegs B ly S U W (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) ->
  (forall pos S2 regs2 mem2 md2,
     ajournal tfibsegs B STK_check_round_trip (spZ regs) FP ly S W (unpoison U mem) md [(3, pos)] ly S2 W
       (unpoison U mem2) md2 0 ->
     ARU tfibsegs B ly S2 U W mem2 md2 ->
     frames S2 = (3, pos) :: frames S -> ~ In (3, pos) (frames S) ->
     ablocks B ly S2 = ablocks B ly S -> st_nev S2 = st_nev S -> blocks_bytes S2 = blocks_bytes S ->
     aregs_preserved (ms_regs ms) regs2 -> YK11.getr regs2 10%bv = Z_to_bv 64 (frame_addr ly 3 pos) ->
     zero_shadow (aview tfibsegs (w_H W) mem2) SHADOW_OFF (frame_addr ly 3 pos) (fs_frame_bytes 3) ->
     rdword (aview tfibsegs (w_H W) mem2) (frame_addr ly 3 pos + fs_frame_bytes 3 - 8) = Some (flag_addr ly 3 pos) ->
     st_ok tfibsegs (Ereg regs2 (crtA_extra regs (flag_addr ly 3 pos) (frame_addr ly 3 pos)
         (shadow_addr (frame_addr ly 3 pos)))) crtA_ss2
       (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x81c14) mem2 (seg_rom tfibsegs))) ->
     (forall a, in_img tfibsegs a -> ~ Exists (in_zr a) (as_owned_static B) ->
        ~ (as_errno B <= a < as_errno B + 4) ->
        aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) (ms_mem ms) a) ->
     SRr tfibsegs W (mkCfg (mkst regs2 (Z_to_bv 64 0x81c14) mem2 (seg_rom tfibsegs)) md2) Q) ->
  SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) Q.
Proof.
intros ly S U W regs mem md ch FP ms mat Q HPRE HFRL HS HJ HARU K.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof crt_STK_eq as FS; unfold crt_STK in FS.
pose proof HPRE as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0) & OK0 & PO0).
destruct (crtA_sm_site ly S U W regs mem md ch ms HPRE HS)
  as (R2 & R9 & Hsp1 & Hsp1a & Hsp1b & R1 & R10 & R3 & R4 & R8 & R18 & R20 & R21 & R25).
set (sp1 := 32 * ((spZ regs - 192) / 32)) in *.
set (mdx := with_vm_backing (m_vm_lazy md) mat md) in *.
assert (Hres : ss_resv crtA_ss1 = None) by (vm_compute; reflexivity).
assert (Hpc : ss_pc crtA_ss1 = PC_stack_malloc_3) by (vm_compute; reflexivity).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ crtA_ss1 ms HS Hres) as Ems. rewrite Hpc in Ems.
rewrite Ems. rewrite <- (proj1 (crt_fr_stack_malloc_3 B RT)).
assert (Hcnt : count_cid 3 (frames S) < fs_frames 3) by exact (crtA_grant_room _ HFRL).
assert (Hsp' : spZ (ms_regs ms) = spZ regs + (sp1 - spZ regs))
  by (unfold spZ at 1; rewrite R2, (wz sp1) by lia; lia).
assert (Hraw : YK0s.ret_ok (Z_to_bv 64 0x81c14)) by (apply ret_ok_even; rewrite (wz 0x81c14) by lia; reflexivity).
eapply SRr_bind.
{ exact (FSW_frame.fsw_stack_malloc_atU B HENV (crtA_ML _ _ _ _ _ (ARU_AR tfibsegs B _ _ _ _ _ _ HARU)) crtA_SMP 3
    (proj2 (crt_fr_stack_malloc_3 B RT)) ltac:(lia) W (ms_regs ms) (ms_mem ms) STK_check_round_trip (spZ regs) FP ly S W
    (unpoison U mem) md [] ly S U mdx 0 (sp1 - spZ regs) (Z_to_bv 64 0x81c14) HJ HARU Hsp'
    ltac:(rewrite Zminus_mod, Hsp1b, Hal16; reflexivity) ltac:(lia) ltac:(unfold ESTACK; lia)
    ltac:(rewrite R3; exact Hgp0) ltac:(rewrite R4; exact Htp0) R1 Hraw Hcnt). }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HARU2 & HP & Hreg10 & Eab & Hfrs2 & Hfresh
  & Hnev2 & Hbb & Hz & Hflag & HK).
replace (spZ regs + (sp1 - spZ regs) - ESTACK) with (sp1 - ESTACK) in HK by lia.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by lia.
apply (K pos S2 regs2 mem2 md2 HJ2 HARU2 Hfrs2 Hfresh Eab Hnev2 Hbb HP Hreg10 Hz Hflag);
  [|destruct HK as (_ & _ & K3 & _);
    intros a Ha Hns He; pose proof (fs_segs_img a Ha) as Himg;
    exact (crt_raw_of_unp B ly S U W (ms_mem ms) mdx ly S2 U W mem2 md2 a HARU HARU2
      ltac:(unfold FS_IMG_END in Himg; lia) ltac:(left; unfold FS_IMG_END, SHADOW_OFF in *; lia)
      (K3 a Ha Hns He))].
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly S2 U W mem2 md2 HARU2) as HAR2.
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS ly S2 W (unpoison U mem2) md2 3 pos HAR2 Hin) as (HFal & _ & HFp & HFs).
destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 3 pos HAR2 Hin) as (HF4096 & HFceil & HFapp).
rewrite crt_frame3 in HFceil, HFapp.
set (F := frame_addr ly 3 pos) in *. set (FL := flag_addr ly 3 pos) in *. set (SF := shadow_addr F).
set (E := Ereg regs2 (crtA_extra regs FL F SF)).
assert (HSF : SF = SHADOW_OFF + F / 8) by reflexivity.
assert (V : forall n z, ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> bv_unsigned (ew E n) = z)
  by (intros n z Hn Hz0; rewrite Hn; apply wz; exact Hz0).
assert (E8 : ew E 8 = YK11.getr regs 2%bv)
  by (subst E; rewrite (ew_Ereg_nat _ _ 8 8%bv eq_refl), (fsw_pres _ _ 8%bv HP ltac:(crtA_cs)); exact R8).
assert (E8u : bv_unsigned (ew E 8) = spZ regs) by (rewrite E8; reflexivity).
assert (E9 : ew E 9 = Z_to_bv 64 sp1)
  by (subst E; rewrite (ew_Ereg_nat _ _ 9 9%bv eq_refl), (fsw_pres _ _ 9%bv HP ltac:(crtA_cs)); exact R9).
assert (E9u : bv_unsigned (ew E 9) = sp1) by (apply V; [exact E9 | lia]).
assert (E10 : ew E 10 = Z_to_bv 64 F) by (subst E; rewrite (ew_Ereg_nat _ _ 10 10%bv eq_refl); exact Hreg10).
assert (E10u : bv_unsigned (ew E 10) = F) by (apply V; [exact E10 | lia]).
assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat _ _ 18 18%bv eq_refl), (fsw_pres _ _ 18%bv HP ltac:(crtA_cs)); exact R18).
assert (E18u : bv_unsigned (ew E 18) = SHADOW_OFF) by (apply V; [exact E18 | unfold SHADOW_OFF; lia]).
assert (E48 : ew E 48 = Z_to_bv 64 SF) by (subst E; apply crtA_extra_48).
assert (HSFb : SHADOW_OFF <= SF /\ SF + 64 <= SHADOW_OFF + 2 ^ 44).
{ rewrite HSF. pose proof (Z.div_pos F 8 ltac:(lia)).
  assert (F / 8 + 64 <= 2 ^ 44) by (apply (Z.le_trans _ ((F + 512) / 8)); [Z.div_mod_to_equations; lia
    | apply Z.div_le_upper_bound; lia]). lia. }
assert (E48u : bv_unsigned (ew E 48) = SF) by (apply V; [exact E48 | unfold SHADOW_OFF in *; lia]).
assert (HSF4 : SF mod 4 = 0).
{ rewrite HSF. assert (HF8 : F / 8 = 4 * (F / 32)) by (Z.div_mod_to_equations; lia).
  rewrite HF8. unfold SHADOW_OFF. rewrite Z.add_mod, Z.mul_comm, Z_mod_mult by lia. reflexivity. }
(* the three regions of the resume state *)
pose proof (FSW_frame3.fsw_resume_after_stack_mallocU B STK_check_round_trip (spZ regs) FP ly S W (unpoison U mem) md []
  ly S S2 U W (ms_mem ms) mdx mem2 md2 0 3 pos sp1 regs2 (crtA_extra regs FL F SF) 0x81c14 (-104) 0 crt_sv_chunks 9
  0x10 0x58 10 (SOff 46 0) HJ2 HARU2 HARU HK Hin ltac:(lia) E8u E9u E10u
  ltac:(rewrite fsw_SOff0; apply crtA_extra_46) Hflag ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(vm_compute; reflexivity) crt_sv_in) as HS2.
specialize (HS2 (crtA_saved_chunks W regs regs2 (crtA_extra regs FL F SF) _ (spZ regs)
  (fun k Hk => crtA_extra_saved regs2 regs FL F SF k Hk) E8u (crtA_saved_val ly S U W regs mem md ch ms HPRE HS))).
(* the frame's shadow window *)
assert (RS : region_ok tfibsegs E (mrestrict (w_H W) mem2) crtA_shadow_region).
{ unfold region_ok, crtA_shadow_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E48u, crt_frame3. change (512 / 8) with 64.
  pose proof HSFb as [HSFb1 HSFb2]. unfold SHADOW_OFF in HSFb1, HSFb2.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable tfibsegs).
  destruct (HFs o ltac:(rewrite crt_frame3; change (512 / 8) with 64; lia)) as (Hp & Hno).
  exact (FSW_frame.fsw_apresent_notowned B ly S2 U W mem2 md2 (SF + o) HARU2 ltac:(unfold SHADOW_OFF in *; lia)
    Hno Hp). }
assert (DS : all_disjoint E crtA_shadow_region
  (FSW_frame3.fsw_resume_regions (-104) 0 crt_sv_chunks 9 0x10 0x58 10 (SOff 46 0) 3)).
{ apply all_disjoint_of_extents. unfold FSW_frame3.fsw_resume_regions, crtA_shadow_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E48u, E8u, E9u, E10u, crt_frame3.
  change (512 / 8) with 64. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, ASAN_CEIL, SHADOW_OFF in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
pose proof (YI0n.st_ok_add_region' tfibsegs E _ _ crtA_shadow_region HS2 ltac:(vm_compute; reflexivity) RS DS) as HS3.
clear HS2.
(* the three facts and the alias *)
pose proof (st_ok_add_fact tfibsegs E _ _ 9 (mkAF (2 ^ 46) (2 ^ 47) 5) HS3
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E9u; change (2 ^ 5) with 32;
        unfold alloc_ceiling in *; lia)) as HS4. clear HS3.
pose proof (st_ok_add_fact tfibsegs E _ _ 48 (mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 2) HS4
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E48u; change (2 ^ 2) with 4; lia)) as HS5. clear HS4.
pose proof (st_ok_add_fact tfibsegs E _ _ 18 (mkAF SHADOW_OFF SHADOW_OFF 0) HS5
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E18u, Z.pow_0_r, Z.mod_1_r; lia)) as HS6. clear HS5.
pose proof (st_ok_add_alias tfibsegs E _ _ _ _ HS6
  (shadow_decl_ok E 10 18 48 F SHADOW_OFF E10 ltac:(lia) E18 ltac:(rewrite E48, HSF; reflexivity))) as HS7.
exact HS7.
Qed.

(* ================= segment 1: the join 0x81c44, the frame header and the frame's shadow, to the encode call ========
   B (MEASURED, crt.B.s): 0x81c14 `mv s3, a0` -> 0x81c18 `j` -> 0x81c20 `mv s6, s3` -> 0x81c24 `bnez s3` (taken: atom
   10 = F >= 4096, the fallback 0x81c28..0x81c40 with its probe loop is dead) -> 0x81c44 the ONE s1 slot 0x50 := F (A
   stores two here, 0x10 and 0x50; B stores 0x10 in segment 5, 0x81dd4) -> 0x81c68..0x81c70 the frame header triple
   through s6 -> 0x81c78 s10 := (F >> 3) + s2, the alias's atom 48 (A: s3) -> 0x81c7c..0x81d70 the 60 poison bytes of
   the frame's shadow -> 0x81d7c `jal preset_base64_encode` with a0 = s5 = bd, a1 = s4 = |bs|, ra = 0x81d80. (A:
   0x81b14 `j` -> 0x81b1c `mv a4, a0` -> 0x81b20 `bnez a0` -> 0x81b40 / 0x81b44 -> 0x81b6c..0x81b74 -> 0x81b7c s3 ->
   0x81b80..0x81c74 -> 0x81c80, ra 0x81c84.)
   Shadow-store method (a Theorem Labs lane 04:14Z): the state the stores run on is crtA_ss2 - the shadow window seated fresh with
   no chunks at the atom 48 the alias names, and only the flag chunk on the frame. Ported from d25a984c903
   check_round_trip_top.v crt_run_setup :1129 (runs.v crt_setup2: A + 16, A + 80, the header at fr, crt_fshadow). *)
Definition crtA_ss3 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL A_preset_base64_encode crtA_ss2).
(* crtA_ss3's regions, as closed literals (the engine keeps crtA_ss2's order: shadow, s0, slot, frame) *)
Definition crtA_s0_8 : YP09.region := Eval vm_compute in nth 1 (ss_mem crtA_ss3) (fstk 0).
Definition crtA_frm_10 : YP09.region := Eval vm_compute in nth 3 (ss_mem crtA_ss3) (fstk 0).

(* the run's write window: the shadow window and the frame (awr_byte's own-frame arm), the s0 words and the s1 slots
   (the stack arm) *)
Lemma crtA_awr2 : forall E ly pos sp0 sp1 FP bl0 blc fr0,
  bv_unsigned (ew E 48) = shadow_addr (frame_addr ly 3 pos) -> bv_unsigned (ew E 8) = sp0 ->
  bv_unsigned (ew E 9) = sp1 -> bv_unsigned (ew E 10) = frame_addr ly 3 pos ->
  sp0 - 208 <= sp1 <= sp0 - 192 ->
  awr_ok tfibsegs B E (ss_mem crtA_ss2) STK_check_round_trip sp0 FP bl0 blc ly [(3, pos)] fr0.
Proof.
intros E ly pos sp0 sp1 FP bl0 blc fr0 E48 E8 E9 E10 Hsp1. pose proof crt_STK_eq as FS; unfold crt_STK in FS.
unfold crtA_ss2, FSW_frame3.fsw_resume_regions. cbn [ss_mem].
eapply (awr_ok_cons_gen tfibsegs B E crtA_shadow_region _ _ _ _ _ _ _ _ _ 48 (shadow_addr (frame_addr ly 3 pos)));
  [reflexivity | exact E48 | |].
{ intros a Ha. unfold crtA_shadow_region in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  left. right. right. right. exists 3, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. lia. }
eapply (awr_ok_cons_stack tfibsegs B E _ _ _ _ _ _ _ _ _ _ 8%nat); [reflexivity | exact E8 | cbn; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off tfibsegs B E _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0));
  [reflexivity | rewrite E9; lia | cbn; lia | cbn; lia |].
eapply (awr_ok_cons_gen tfibsegs B E _ _ _ _ _ _ _ _ _ _ 10 (frame_addr ly 3 pos));
  [reflexivity | exact E10 | | apply awr_ok_nil].
intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
left. right. right. right. exists 3, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. lia.
Qed.

Lemma crtA_seg1 : forall E STK0 sp0 FP ly S W0 mem0 md0 pos S2 U (W : world tfibsegs) ms md2 k sp1
  (Q : world tfibsegs -> config -> Prop),
  STK0 = STK_check_round_trip ->
  st_ok tfibsegs E crtA_ss2 (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK0 sp0 FP ly S W0 mem0 md0 [(3, pos)] ly S2 W (unpoison U (ms_mem ms)) md2 k ->
  ARU tfibsegs B ly S2 U W (ms_mem ms) md2 ->
  bv_unsigned (ew E 48) = shadow_addr (frame_addr ly 3 pos) -> bv_unsigned (ew E 8) = sp0 ->
  bv_unsigned (ew E 9) = sp1 -> bv_unsigned (ew E 10) = frame_addr ly 3 pos ->
  sp0 - 208 <= sp1 <= sp0 - 192 ->
  (forall ms' mat',
     st_ok tfibsegs E crtA_ss3 (restrict (w_H W) ms') ->
     ajournal tfibsegs B STK0 sp0 FP ly S W0 mem0 md0 [(3, pos)] ly S2 W (unpoison U (ms_mem ms'))
       (with_vm_backing (m_vm_lazy md2) mat' md2) k ->
     ARU tfibsegs B ly S2 U W (ms_mem ms') (with_vm_backing (m_vm_lazy md2) mat' md2) ->
     frame_of E (ss_mem crtA_ss2) (ms_mem ms) (ms_mem ms') ->
     frame_of E (ss_mem crtA_ss2) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     SRr tfibsegs W (mkCfg ms' (with_vm_backing (m_vm_lazy md2) mat' md2)) Q) ->
  SRr tfibsegs W (mkCfg ms md2) Q.
Proof.
intros E STK0 sp0 FP ly S W0 mem0 md0 pos S2 U W ms md2 k sp1 Q -> HS HJ HARU E48 E8 E9 E10 Hsp1 K.
assert (Hrun : sym_run_toN tfibsegs crt_tbl FUEL A_preset_base64_encode crtA_ss2 = (crtA_ss3, RS_running))
  by (vm_compute; reflexivity).
exact (fsw_run_to_AJU B crt_tbl crt_tbl_ok W FUEL A_preset_base64_encode E crtA_ss2 crtA_ss3 RS_running ms
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HARU HJ (crtA_awr2 E ly pos sp0 sp1 FP _ _ _ E48 E8 E9 E10 Hsp1) K).
Qed.

(* ================= the after-call boundary state, generic in the slot chunks =================
   FSH_crt_base.crt_after_call fixes the s1 slots to crt_cs1, true only from B 0x820e8 (A 0x81f9c) on; A0's call boundaries
   (B 0x81d80, 0x81da4, 0x81db8) hold fewer slots. crtA_after_call is lib/B/FSH_crt_base.v's crt_after_call's own proof
   with three parameters opened: the slot chunks cs1 (atom chunks below nb, offsets in [0x10, 0x58)), and the call-site
   env E, which need only agree with crt_extra on atoms 32 .. nb - 1 (46 <= nb <= 51; B's crt_extra has nineteen atoms,
   En at 50; A: <= 50). B: the frame-shadow register crt_after_call reads is x26 = s10 (A: x19 = s3). A0's encode call site holds the frame's shadow address
   at atom 48 (nb = 48); after the encode call atom 48 is c_text and the record's c_want is picked only at the first
   malloc's return (nb = 49); from there on the env is a full crt_E (nb = 50). Everything else is crt_after_call's
   text. a Theorem Labs lane moves it into the base as the general form (decision 05:3xZ). *)
Definition crtA_atomlt (nb : nat) (cs : list YP09.chunk) : Prop :=
  Forall (fun c => exists d w n off, c = YP09.mkChunk d (CVal w (SOff n off)) /\ (32 <= n < nb)%nat) cs.
Lemma crtA_chunks_envlt : forall nb E E' m base cs,
  (forall n, (32 <= n < nb)%nat -> ew E' n = ew E n) -> crtA_atomlt nb cs ->
  Forall (YP09.chunk_ok tfibsegs E m base) cs -> Forall (YP09.chunk_ok tfibsegs E' m base) cs.
Proof.
intros nb E E' m base cs Hag Hsh H. unfold crtA_atomlt in Hsh. rewrite Forall_forall in Hsh, H |- *. intros c Hc.
destruct (Hsh c Hc) as (d & w & n & off & -> & Hn).
apply (crt_chunk_env E E' m base d w (SOff n off)); [|exact (H _ Hc)].
cbn [sv_denot]. rewrite (Hag n Hn). reflexivity.
Qed.
Lemma crtA_sv_atomslt : forall nb, (46 <= nb)%nat -> crtA_atomlt nb crt_sv_chunks.
Proof.
intros nb Hnb. unfold crtA_atomlt, crt_sv_chunks. cbn [seq map].
repeat (apply Forall_cons; [do 4 eexists; split; [reflexivity | cbn; lia]|]). apply Forall_nil.
Qed.
Lemma crtA_after_call : forall cx E k ly3 S3 U3 W3 ms3 md3 STKc FPc ly' S' U' W' regs' mem' md' kc r cs1 csF nb,
  (46 <= nb <= 51)%nat ->
  (forall n, (32 <= n < nb)%nat -> ew E n = nth (n - 32) (crt_extra cx) (Z_to_bv 64 0)) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  crt_frame_ok cx S3 W3 ms3 ->
  YK11.getr (ms_regs ms3) 2%bv = Z_to_bv 64 (crt_sp1 cx) ->
  YK11.getr (ms_regs ms3) 3%bv = YK11.getr (c_regs cx) 3%bv ->
  YK11.getr (ms_regs ms3) 4%bv = YK11.getr (c_regs cx) 4%bv ->
  YK11.getr (ms_regs ms3) 8%bv = Z_to_bv 64 (spZ (c_regs cx)) ->
  YK11.getr (ms_regs ms3) 9%bv = Z_to_bv 64 (crt_sp1 cx) ->
  YK11.getr (ms_regs ms3) 26%bv = Z_to_bv 64 (crt_SF cx) ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms3)) (spZ (c_regs cx))) crt_sv_chunks ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms3)) (crt_sp1 cx)) cs1 ->
  crtA_atomlt nb cs1 ->
  Forall (fun c => 0x10 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= 0x58) cs1 ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms3)) (crt_F cx)) csF ->
  Forall (fun c => 0 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= fs_frame_bytes 3) csF ->
  crtA_atomlt nb csF ->
  (forall c, In c csF -> forall i, 0 <= i < YP09.c_len c -> ~ inFP FPc (crt_F cx + YP09.c_off c + i)) ->
  (forall i, 0 <= i < 8 -> ~ inFP FPc (crt_F cx + fs_frame_bytes 3 - 8 + i)) ->
  ajournal tfibsegs B STKc (crt_sp1 cx) FPc ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 []
    ly' S' W' (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  fsw_fp_sub B (c_ly cx) (c_S cx) ly3 S3 [(3, c_pos cx)] FS_PSTAT_FP FPc ->
  aregs_preserved (ms_regs ms3) regs' -> 0 <= STKc -> STKc + 208 <= STK_check_round_trip ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly' S' W' (unpoison U' mem') md' (k + kc) /\
  ARU tfibsegs B ly' S' U' W' mem' md' /\
  crt_frame_ok cx S' W' (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs)) /\
  crt_E cx (Ereg regs' (crt_extra cx)) /\
  st_ok tfibsegs (Ereg regs' (crt_extra cx)) (crt_ss_ret r cs1 csF)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 STKc FPc ly' S' U' W' regs' mem' md' kc r cs1 csF nb Hnb
  HE HJ HARU3 HFR R2 R3 R4 R8 R9 R26 HSV HCS1 Hcs1at Hcs1in HCSF HcsFin HcsFat HcsFnf HflagNF HJc OK' PO' HFP HP HSTKc
  HSTK.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKv : 208 <= STK_check_round_trip) by (apply Z.leb_le; vm_compute; reflexivity).
destruct HFR as (Hfrs & Hnotin & Hflag).
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
pose proof HJ as (HARj & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hsp0 : alloc_ceiling + STK_check_round_trip <= spZ (c_regs cx)) by lia.
pose proof (fsw_realign_facts (spZ (c_regs cx) - 192) ltac:(lia)
  ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as ((Flo & Fhi) & Fm32 & Fm16).
assert (Hsp1lo : spZ (c_regs cx) - 208 <= crt_sp1 cx) by (unfold crt_sp1; lia).
assert (Hsp1hi : crt_sp1 cx <= spZ (c_regs cx) - 192) by (unfold crt_sp1; lia).
(* the frame's address and shadow, with the layout stable under the journals *)
assert (Efr3 : frame_addr ly3 3 (c_pos cx) = crt_F cx).
{ unfold crt_F, frame_addr. destruct Hly3 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
pose proof (ARU_AR tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 HARU3) as HAR3.
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 3 (c_pos cx) HAR3 Hin3)
  as (HF0 & HFc & HFapp).
rewrite Efr3 in HF0, HFc, HFapp.
rewrite crt_frame3 in HFc, HFapp.
assert (HFrng : 0 <= crt_F cx < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds (crt_F cx) HFrng) as (HS1b & HS2b).
(* the resumed env *)
set (E' := Ereg regs' (crt_extra cx)) in *.
assert (P2 : YK11.getr regs' 2%bv = YK11.getr (ms_regs ms3) 2%bv) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : YK11.getr regs' 3%bv = YK11.getr (ms_regs ms3) 3%bv) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : YK11.getr regs' 4%bv = YK11.getr (ms_regs ms3) 4%bv) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : YK11.getr regs' 8%bv = YK11.getr (ms_regs ms3) 8%bv) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : YK11.getr regs' 9%bv = YK11.getr (ms_regs ms3) 9%bv) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
assert (P26 : YK11.getr regs' 26%bv = YK11.getr (ms_regs ms3) 26%bv) by exact (HP 26 ltac:(unfold acallee_saved; lia)).
assert (HE' : crt_E cx E').
{ subst E'. apply crt_E_Ereg.
  - rewrite P2, R2. apply wz. lia.
  - rewrite P3. exact R3.
  - rewrite P4. exact R4.
  - rewrite P8, R8. apply wz. unfold spZ. apply u64_range.
  - rewrite P9, R9. apply wz. lia.
  - rewrite P26, R26. apply wz.
    unfold crt_SF. lia. }
assert (Hag : forall n, (32 <= n < nb)%nat -> ew E' n = ew E n).
{ intros n Hn. rewrite (HE n Hn). replace n with (32 + (n - 32))%nat at 1 by lia.
  exact (crt_E_extra cx E' (n - 32) HE' ltac:(unfold crt_nextra; lia)). }
(* the composed journal: FSW_K3.fsw_ajournal_sub5, whose FP relation is exactly fsw_fp_sub's five arms (the fifth, an
   entry-frame byte, came with S0 b04db294041's kit update), so HFP fits as given *)
assert (HJ2 : ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly' S' W' (unpoison U' mem') md' (k + kc)).
{ eapply (fsw_ajournal_sub5 B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k
    STKc (crt_sp1 cx) FPc [] ly' S' W' (unpoison U' mem') md' kc);
  first [ solve [exact HJ] | solve [exact HJc] | solve [lia] | solve [exact HFP] ]. }
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md')
  by (split; [exact (proj1 HJ2) | split; [exact OK' | exact PO']]).
pose proof HJ2 as (HAR' & Hly' & _ & _ & _ & Hfrs' & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (Efr' : frame_addr ly' 3 (c_pos cx) = crt_F cx).
{ unfold crt_F, frame_addr. destruct Hly' as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (Hin3' : In (3, c_pos cx) (frames S')).
{ pose proof HJc as (_ & _ & _ & _ & _ & HfrsC & _). rewrite HfrsC. cbn [app]. exact Hin3. }
destruct (al_frames _ _ LAWS ly' S' W' (unpoison U' mem') md' 3 (c_pos cx) (proj1 HJ2) Hin3')
  as (Hal32' & Happ' & Hfp' & Hsp').
rewrite Efr' in Hal32', Hfp', Hsp'. rewrite crt_frame3 in Hfp', Hsp'. change (512 / 8) with 64 in Hsp'.
assert (HSFlo : 2147450880 <= crt_SF cx) by (unfold crt_SF; rewrite C5 in HS1b; lia).
assert (HSFhi : crt_SF cx < 17594333495296) by (unfold crt_SF; rewrite C2 in HS2b; lia).
(* the resumed env's atom values *)
assert (E9v : bv_unsigned (ew E' 9) = crt_sp1 cx) by (destruct HE' as (_ & _ & _ & _ & H & _); exact H).
assert (E8v : bv_unsigned (ew E' 8) = spZ (c_regs cx)) by (destruct HE' as (_ & _ & _ & H & _); exact H).
assert (E26v : bv_unsigned (ew E' 26) = crt_SF cx) by (destruct HE' as (_ & _ & _ & _ & _ & H & _); exact H).
assert (E47v : bv_unsigned (ew E' 47) = crt_F cx) by (rewrite (crt_E_F cx E' HE'); apply wz; lia).
(* the three extra regions of the boundary state, on the memory after the call *)
assert (ROslot : region_ok tfibsegs E' (mrestrict (w_H W') mem') (crt_slot_region cs1)).
{ unfold region_ok, crt_slot_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9v.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B ly' S' U' W' mem' md' _ HARU'); [lia|]. apply Hpres2. lia.
  - assert (H1 : Forall (YP09.chunk_ok tfibsegs E' (mrestrict (w_H W3) (ms_mem ms3)) (crt_sp1 cx)) cs1)
      by (eapply crtA_chunks_envlt; [exact Hag | exact Hcs1at | exact HCS1]).
    pose proof Hcs1in as Hin1. rewrite Forall_forall in H1, Hin1 |- *. intros c Hc.
    apply (chunk_ok_mbyte E' (mrestrict (w_H W3) (ms_mem ms3))); [|exact (H1 c Hc)].
    intros i Hi. destruct (Hin1 c Hc) as (Ho1 & Ho2 & Ho3).
    eapply (crt_kept_stack B ly3 S3 U3 W3 (ms_mem ms3) md3 ly' S' U' W' mem' md' STKc (crt_sp1 cx) FPc kc);
      [exact HARU3 | exact HARU' | exact HJc | lia | lia]. }
assert (ROshadow : region_ok tfibsegs E' (mrestrict (w_H W') mem') crt_shadow_region).
{ unfold region_ok, crt_shadow_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E26v.
  split; [lia|]. split; [rewrite crt_frame3; cbn [Z.div]; lia|].
  split; [|apply Forall_nil].
  intros o Ho. rewrite crt_frame3 in Ho. change (512 / 8) with 64 in Ho.
  apply (apresent_writable tfibsegs). destruct (Hsp' o ltac:(lia)) as (Hp & Hno).
  apply (FSW_frame.fsw_apresent_notowned B ly' S' U' W' mem' md' _ HARU'); [lia | exact Hno | exact Hp]. }
assert (ROframe : region_ok tfibsegs E' (mrestrict (w_H W') mem') (crt_frame_region csF)).
{ unfold region_ok, crt_frame_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E47v.
  split; [lia|]. split; [rewrite crt_frame3; lia|]. split.
  - intros o Ho. rewrite crt_frame3 in Ho.
    apply (apresent_writable tfibsegs). destruct (Hfp' (crt_F cx + o) ltac:(lia)) as (Hp & Hno).
    apply (FSW_frame.fsw_apresent_notowned B ly' S' U' W' mem' md' _ HARU'); [lia | exact Hno | exact Hp].
  - assert (H1 : Forall (YP09.chunk_ok tfibsegs E' (mrestrict (w_H W3) (ms_mem ms3)) (crt_F cx)) csF)
      by (eapply crtA_chunks_envlt; [exact Hag | exact HcsFat | exact HCSF]).
    pose proof HcsFin as Hin1. rewrite Forall_forall in H1, Hin1 |- *. intros c Hc.
    apply (chunk_ok_mbyte E' (mrestrict (w_H W3) (ms_mem ms3))); [|exact (H1 c Hc)].
    intros i Hi. destruct (Hin1 c Hc) as (Ho1 & Ho2 & Ho3).
    apply (mbyte_of_aview tfibsegs (w_H W3) (w_H W')).
    eapply (crt_kept_frame B ly3 S3 U3 W3 (ms_mem ms3) md3 ly' S' U' W' mem' md' STKc (crt_sp1 cx) FPc kc 3 (c_pos cx));
      [exact HARU3 | exact HARU' | exact HJc | exact Hin3 | rewrite Efr3; rewrite crt_frame3 in *; lia
       | exact (HcsFnf c Hc i Hi)]. }
(* the slot region is well formed: its chunks lie inside [0x10, 0x58) *)
assert (WFslot : YP09.region_wf (crt_slot_region cs1) = true).
{ unfold YP09.region_wf, crt_slot_region. cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite !andb_true_iff. split; [split|].
  - apply Z.leb_le. lia.
  - apply orb_true_iff. right. rewrite !andb_true_iff. split; apply Z.leb_le; lia.
  - apply forallb_forall. intros c Hc. pose proof Hcs1in as Hin1. rewrite Forall_forall in Hin1.
    destruct (Hin1 c Hc) as (Ho1 & Ho2 & Ho3). unfold YP09.chunk_inside.
    cbn [YP09.r_lo YP09.r_hi]. rewrite !andb_true_iff. split; [split|]; apply Z.leb_le; lia. }
(* the frame's region is well formed: its chunks lie inside [0, 512) *)
assert (WFframe : YP09.region_wf (crt_frame_region csF) = true).
{ unfold YP09.region_wf, crt_frame_region. cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite !andb_true_iff. split; [split|].
  - apply Z.leb_le. rewrite crt_frame3. lia.
  - apply orb_true_iff. right. rewrite !andb_true_iff. split; apply Z.leb_le; lia.
  - apply forallb_forall. intros c Hc. pose proof HcsFin as Hin1. rewrite Forall_forall in Hin1.
    destruct (Hin1 c Hc) as (Ho1 & Ho2 & Ho3). unfold YP09.chunk_inside.
    cbn [YP09.r_lo YP09.r_hi]. rewrite !andb_true_iff. split; [split|]; apply Z.leb_le; lia. }
(* the four regions never meet: the frame is application memory below alloc_ceiling, its shadow is in the shadow band,
   the slots and the saved words are stack, at or above alloc_ceiling *)
assert (Hceil1 : alloc_ceiling <= crt_sp1 cx) by lia.
assert (Dfs : crt_F cx + 512 <= crt_SF cx \/ crt_SF cx + 64 <= crt_F cx).
{ unfold in_app in HFapp. destruct HFapp as (_ & [Hlow | (Hhigh & _)]).
  - left. unfold kLowShadowBeg in *. lia.
  - right. unfold crt_SF, shadow_addr, SHADOW_OFF, kHighMemBeg in *.
    Z.div_mod_to_equations. lia. }
(* the boundary state itself (FSW_rres.fsw_resume_after_rtU_s0 over the composed journal) *)
assert (HS4 : st_ok tfibsegs E' (crt_ss_ret r cs1 csF)
  (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs)))).
{ unfold crt_ss_ret.
  eapply (fsw_resume_after_rtU_s0 B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly' S' U' W' mem' md' (k + kc) regs' mem'
    (crt_extra cx) crt_sv_chunks (crt_ret_regions cs1 csF) crt_ret_facts r (-104) 0).
  - exact HJ2.
  - exact HARU'.
  - rewrite P8, R8. reflexivity.
  - lia.
  - lia.
  - lia.
  - unfold fss_ret_s0_regs, crt_ret_regions, regions_wf. cbn [forallb andb].
    rewrite WFframe. cbn [andb]. vm_compute (YP09.region_wf crt_s0_region).
    rewrite !andb_true_r. rewrite WFslot.
    vm_compute (YP09.region_wf crt_shadow_region). reflexivity.
  - exact crt_sv_in.
  - assert (H1 : Forall (YP09.chunk_ok tfibsegs E' (mrestrict (w_H W3) (ms_mem ms3)) (spZ (c_regs cx))) crt_sv_chunks)
      by (eapply crtA_chunks_envlt; [exact Hag | exact (crtA_sv_atomslt nb ltac:(lia)) | exact HSV]).
    pose proof crt_sv_in as Hin1. rewrite Forall_forall in H1, Hin1 |- *. intros c Hc.
    apply (chunk_ok_mbyte E' (mrestrict (w_H W3) (ms_mem ms3))); [|exact (H1 c Hc)].
    intros i Hi. destruct (Hin1 c Hc) as (Ho1 & Ho2).
    eapply (crt_kept_stack B ly3 S3 U3 W3 (ms_mem ms3) md3 ly' S' U' W' mem' md' STKc (crt_sp1 cx) FPc kc);
      [exact HARU3 | exact HARU' | exact HJc | lia | lia].
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
    split; [|exact I]. split; [lia | split; [exact Hal32' | lia]]. }
split; [exact HJ2|]. split; [exact HARU'|]. split.
- split; [rewrite Hfrs'; cbn [app]; reflexivity|]. split; [exact Hnotin|].
  cbn [ms_mem mkst]. rewrite <- Hflag. apply rdword_ext. intros kk Hk.
  eapply (crt_kept_frame B ly3 S3 U3 W3 (ms_mem ms3) md3 ly' S' U' W' mem' md' STKc (crt_sp1 cx) FPc kc 3 (c_pos cx));
    [exact HARU3 | exact HARU' | exact HJc | exact Hin3 | rewrite Efr3; rewrite crt_frame3 in *; lia
     | exact (HflagNF kk Hk)].
- split; [exact HE' | exact HS4].
Qed.

(* ================= what crt's journal keeps on the way to a call ==================
   FSH_crt_site's crt_keep_blk is stated at own = [], and crt's journal carries own = [(3, pos)]. The block clause it
   reads does not depend on own, so this is its text with own generic (and FP fixed to FS_PSTAT_FP, whose cells are
   image bytes, while no block byte is: YCbq.blk_img, crt_pstat_img). ---- *)
Lemma crtA_blk_keep : forall ly S U (W : world tfibsegs) mem md ly' S' U' (W' : world tfibsegs) mem' md' k STK sp0 own
  p n i,
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  ajournal tfibsegs B STK sp0 FS_PSTAT_FP ly S W (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
  aview tfibsegs (w_H W') mem' (p + i) = aview tfibsegs (w_H W) mem (p + i).
Proof.
intros ly S U W mem md ly' S' U' W' mem' md' k STK sp0 own p n i HARU HARU' HJ Hin Hin' Hi.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & H4096 & Hceil & Happ & _).
cbv [in_app kLowShadowBeg kHighMemBeg] in Happ.
assert (Hnfp : ~ inFP FS_PSTAT_FP (p + i)).
{ intros HFP. exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md p n (p + i) HAR Hin ltac:(lia)
    (crt_pstat_img _ HFP)). }
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K2 & _).
apply (crt_raw_of_unp B ly S U W mem md ly' S' U' W' mem' md' (p + i) HARU HARU').
- pose proof (@alloc_ceiling_lt rc) as HC47.
  change (2 ^ 47) with 140737488355328 in HC47. change (2 ^ 64) with 18446744073709551616. lia.
- cbv [SHADOW_OFF kHighMemBeg]. lia.
- exact (K2 p n i Hin Hin' Hi Hnfp).
Qed.

(* ================= the encode call (B 0x81d7c, A 0x81c80), its premises and its boundary =================
   Ported from d25a984c903 check_round_trip_stdefs.v St0 :215 (the cut at the encode call: the body bd with its block,
   the text t, the frame and the statics) and check_round_trip_sd0.v st0 :136 (St1 -> St0). encode_spec's premises are
   read off crt_base and the call-site state; the ones that speak of memory come in as hypotheses, because the walk
   proves them once, at the entry, from the runs' own keeps. ---- *)
Hypothesis ENCODE : @FSH_Fn_writer.encode_spec fx rc SK B tfibsegs.
Hypothesis IMG : fs_img_facts tfibsegs B.

(* the decoded body's length: at most 3/4 of the text's, so well inside encode's 2 ^ 27 (ported from d25a984c903
   check_round_trip_top.v crt_dec_len :52, which is WriterSpecFacts.b64_dec_bound here) *)
Lemma crtA_len : forall (tb : list byte) (bs : list Z),
  WriterSpec.b64_dec (HState.zs tb) = Some bs -> Z.of_nat (length tb) <= 3 * 2 ^ 20 ->
  WriterSpec.bytes_ok bs /\ 0 <= Z.of_nat (length bs) <= 2359298 /\
  FSH_Fn_writer.enc_size (Z.of_nat (length bs)) + HEAD <= LIVE_check_round_trip.
Proof.
intros tb bs Hdec Htb. split; [exact (WriterSpecFacts.b64_dec_ok _ _ Hdec)|].
pose proof (WriterSpecFacts.b64_dec_bound _ _ Hdec) as Hb.
assert (Hzs : Z.of_nat (length (HState.zs tb)) = Z.of_nat (length tb)) by (unfold HState.zs; rewrite length_map; reflexivity).
rewrite Hzs in Hb. pose proof (Zle_0_nat (length bs)) as Hnn. pose proof (Zle_0_nat (length tb)) as Hnt.
assert (Hn : 0 <= Z.of_nat (length bs) <= 2359298) by (Z.div_mod_to_equations; lia).
split; [exact Hn|]. unfold FSH_Fn_writer.enc_size, LIVE_check_round_trip, HEAD. Z.div_mod_to_equations. lia.
Qed.

(* encode's premises at 0x81d7c (A 0x81c80), from crt_base and the call-site facts. The three memory premises (the body's bytes,
   its block, the statics) are hypotheses: the entry theorem proves them from the runs' keeps. *)
Lemma crtA_pre_encode : forall cx k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 peak,
  crt_base B cx ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  fpreU tfibsegs B STK_preset_base64_encode ly3 S3 U3 W3 (ms_regs ms3) (ms_mem ms3) md3 (crt_ch1 cx) ->
  FSupoisonU.fs_heads B ly3 S3 U3 ->
  raZ (ms_regs ms3) = 0x81d80 ->
  Z.of_nat (length (frames S3)) <= FRL_CRT_CALLEE ->
  YK11.getr (ms_regs ms3) 10%bv = w64 (c_bd cx) ->
  YK11.getr (ms_regs ms3) 11%bv = w64 (Z.of_nat (length (c_bs cx))) ->
  zbytes_at tfibsegs W3 (ms_mem ms3) (c_bd cx) (c_bs cx) ->
  (exists kd, fs_rblock tfibsegs B ly3 S3 W3 (ms_mem ms3) (c_bd cx) kd /\ Z.of_nat (length (c_bs cx)) <= kd) ->
  fs_glob tfibsegs W3 (ms_mem ms3) (c_live cx) peak (c_cnt cx) SIZE_MAXZ ->
  st_nev S3 <= st_nev (c_S cx) + k -> k + EV_preset_base64_encode <= EV_check_round_trip ->
  blocks_bytes S3 <= blocks_bytes (c_S cx) ->
  SRr tfibsegs W3 (cfg_at tfibsegs A_preset_base64_encode (ms_regs ms3) (ms_mem ms3) md3)
    (fun W' c' =>
       (c_cnt cx = SIZE_MAXZ /\
        fpostU tfibsegs B STK_preset_base64_encode (spZ (ms_regs ms3)) FS_PSTAT_FP (ms_regs ms3) ly3 S3 U3 W3
          (ms_mem ms3) md3 0 U3
          (fun ly' S' W' regs' mem' md' =>
             YK11.getr regs' 10%bv = w64 0 /\ ablocks B ly' S' = ablocks B ly3 S3 /\
             fs_glob tfibsegs W' mem' (c_live cx) peak ((c_cnt cx + 1) mod 2 ^ 64) SIZE_MAXZ) W' c')
       \/
       (exists q, c_cnt cx <> SIZE_MAXZ /\ q <> 0 /\
        fpostU tfibsegs B STK_preset_base64_encode (spZ (ms_regs ms3)) FS_PSTAT_FP (ms_regs ms3) ly3 S3 U3 W3
          (ms_mem ms3) md3 EV_preset_base64_encode (U3 ++ [(q - HEAD, HEAD)])
          (fun ly' S' W' regs' mem' md' =>
             YK11.getr regs' 10%bv = w64 q /\ 4096 + HEAD <= q /\
             ablocks B ly' S' = ablocks B ly3 S3 ++ [(q - HEAD, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD)] /\
             fs_rblock tfibsegs B ly' S' W' mem' q (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))) /\
             zbytes_at tfibsegs W' mem' q (WriterSpec.b64_enc (c_bs cx) ++ [0]) /\
             (forall i, 0 <= i < Z.of_nat (length (c_bs cx)) ->
                mbyte tfibsegs (mrestrict (w_H W') mem') (c_bd cx + i) =
                mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) (c_bd cx + i)) /\
             fs_glob tfibsegs W' mem' (c_live cx + FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))))
               (Z.max peak (c_live cx + FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))))
               ((c_cnt cx + 1) mod 2 ^ 64) SIZE_MAXZ) W' c')).
Proof.
intros cx k ly3 S3 U3 W3 ms3 md3 peak HB HJ HARU HPRE Hheads Hra Hfrl R10 R11 Hbytes Hblk Hglob Hnev Hk Hbb.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HB as ((HPRE0 & HROD0) & Hheads0 & Htop0 & Hfrl0 & Hr10 & Hr11 & Hr12 & Htext & Hnonul & Htblen
  & Htwin & Htblk & Hdec & Hbd0 & Hbody & Hrb0 & Hstat & Hquiet & Hrd & Hcells & Hsp47 & Hnev0 & Hlive0 & HTU0).
destruct (crtA_len (c_tb cx) (c_bs cx) Hdec Htblen) as (Hok & Hlen & Henc).
destruct Hblk as (kd & Hrb & Hkd).
pose proof Hrb as (Hin & Hal & Hpos & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) Hin)
  as (_ & H4096 & Hceil & Happ & _).
pose proof (req_size_bounds (kd + HEAD) ltac:(unfold HEAD; lia)) as (_ & _ & Hrq).
apply (ENCODE ly3 S3 U3 W3 (ms_regs ms3) (ms_mem ms3) md3 (crt_ch1 cx) (c_bd cx) (Z.of_nat (length (c_bs cx)))
  (c_bs cx) (c_live cx) peak (c_cnt cx) SIZE_MAXZ HPRE Hheads
  Hfrl R10 R11 Hok eq_refl ltac:(lia) Hbytes
  ltac:(unfold HEAD in *; lia)
  ltac:(intros _; exists kd; split; [exact Hrb | exact Hkd]) Hglob
  ltac:(unfold EV_preset_base64_encode in *; unfold EV_check_round_trip in Hk, Hnev0; lia)
  ltac:(unfold HEAD in *; unfold LIVE_check_round_trip in Henc, Hlive0; lia)
  ltac:(unfold HEAD in *; unfold LIVE_check_round_trip in Henc, Hrd; lia)
  ltac:(pose proof Hquiet as (_ & Hc0 & Hc1); unfold EV_check_round_trip in Hc1; lia)).
Qed.

(* the spec states the body's bytes as `zs (bz bs)`, encode asks for `bs`: the two agree on bytes (YI00.bytes_ok) *)
Lemma crtA_zs_bz : forall l : list Z, WriterSpec.bytes_ok l -> HState.zs (HState.bz l) = l.
Proof.
intros l H. unfold HState.zs, HState.bz. rewrite map_map.
induction l as [|a l IH]; [reflexivity|].
pose proof (proj1 (Forall_cons_iff _ _ _) H) as (Ha & Hl). cbn [map]. rewrite (IH Hl).
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Ha.
Qed.

(* ================= fuzz/alloc.c's statics across the walk's own runs =================
   ajournal's image clause spares exactly FS_PSTAT_FP, which IS the four statics, so fs_glob does not ride the journal:
   it rides each run's own frame_of. Neither run writes an image byte - segment 0 writes only the entry stack window,
   segment 1 writes that, the s1 slots, the class-3 frame (no frame byte is an image byte: YCbq.frm_img) and the
   frame's shadow (at or above SHADOW_OFF) - and the grant keeps image bytes that are neither owned statics nor errno,
   which is what IMG gives for FS_PSTAT_FP. ---- *)
Lemma crtA_pstat_img8 : forall a, (G_FAIL <= a < G_FAIL + 8 \/ G_LIVE <= a < G_LIVE + 8 \/ G_PEAK <= a < G_PEAK + 8 \/
  G_COUNT <= a < G_COUNT + 8) -> in_img tfibsegs a /\ inFP FS_PSTAT_FP a.
Proof.
intros a Ha.
assert (HFP : inFP FS_PSTAT_FP a).
{ unfold FS_PSTAT_FP, G_FAIL, G_LIVE, G_PEAK, G_COUNT in *.
  destruct Ha as [H|[H|[H|H]]].
  (* B's four statics (lib/B/FSPstat.v FS_PSTAT_FP, lib/B/FSH_Base.v G_FAIL .. G_COUNT) *)
  - exists (0xa41c0, 0xa41c8). split; [left; reflexivity | cbn [fst snd]; lia].
  - exists (0x5daac0, 0x5daac8). split; [right; left; reflexivity | cbn [fst snd]; lia].
  - exists (0x5daae0, 0x5daae8). split; [right; right; left; reflexivity | cbn [fst snd]; lia].
  - exists (0x5dab00, 0x5dab08). split; [right; right; right; left; reflexivity | cbn [fst snd]; lia]. }
split; [exact (crt_pstat_img a HFP) | exact HFP].
Qed.

Lemma crtA_glob_keep : forall (W : world tfibsegs) (m m' : word -> option byte) live peak cnt fail,
  (forall a, in_img tfibsegs a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail Hk (G1 & G2 & G3 & G4 & R).
assert (VB : forall g v, (G_FAIL <= g /\ g + 8 <= G_FAIL + 8 \/ G_LIVE <= g /\ g + 8 <= G_LIVE + 8 \/
    G_PEAK <= g /\ g + 8 <= G_PEAK + 8 \/ G_COUNT <= g /\ g + 8 <= G_COUNT + 8) ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W) m') g 8 v).
{ intros g v Hg Hv k Hkk.
  assert (Hk8 : 0 <= Z.of_nat k < 8) by (cbn in Hkk; lia).
  destruct (crtA_pstat_img8 (g + Z.of_nat k) ltac:(unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT in *; lia)) as (Hi & _).
  unfold mbyte, mrestrict in *. rewrite (Hk _ Hi). exact (Hv k Hkk). }
unfold fs_glob, fs_glob_at in *.
split; [apply VB; [lia | exact G1]|]. split; [apply VB; [lia | exact G2]|].
split; [apply VB; [lia | exact G3]|]. split; [apply VB; [lia | exact G4]|]. exact R.
Qed.

(* segment 0's write ranges hold no image byte: the entry stack window is at or above alloc_ceiling, the four cells
   are read-only (whi <= wlo) *)
Lemma crtA_img_keep0 : forall E sp0 (m m' : word -> option byte),
  bv_unsigned (ew E 2) = sp0 -> alloc_ceiling + STK_check_round_trip <= sp0 ->
  frame_of E (ss_mem crtA_ss0) m m' -> forall a, in_img tfibsegs a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
intros E sp0 m m' E2 Hsp HF a Ha. pose proof crt_STK_eq as FS; unfold crt_STK in FS.
pose proof (fs_segs_img a Ha) as Himg.
pose proof asan_consts as (C1 & _).
apply HF. rewrite (wz a ltac:(unfold FS_IMG_END in Himg; lia)).
intros (r & Hin & Hr). unfold crtA_ss0, fss0T_args, fsT_regions_args, fsT_regions, fs_uar_regions in Hin.
cbn [ss_mem app In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val fstk fs_got_region fs_bcell_region fs_got_uar_region
       fs_uar_cell_region] in Hr;
  [rewrite E2 in Hr | | | | ]; unfold FS_IMG_END in Himg; lia.
Qed.
(* the same keep in the form the grant's acall_kept gives (aview, i.e. mbyte on the restricted memory) *)
Lemma crtA_glob_keep_mb : forall (W : world tfibsegs) (m m' : word -> option byte) live peak cnt fail,
  (forall a, in_img tfibsegs a ->
     mbyte tfibsegs (mrestrict (w_H W) m') a = mbyte tfibsegs (mrestrict (w_H W) m) a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail Hk (G1 & G2 & G3 & G4 & R).
assert (VB : forall g v, (G_FAIL <= g /\ g + 8 <= G_FAIL + 8 \/ G_LIVE <= g /\ g + 8 <= G_LIVE + 8 \/
    G_PEAK <= g /\ g + 8 <= G_PEAK + 8 \/ G_COUNT <= g /\ g + 8 <= G_COUNT + 8) ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W) m') g 8 v).
{ intros g v Hg Hv k Hkk. assert (Hk8 : 0 <= Z.of_nat k < 8) by (cbn in Hkk; lia).
  destruct (crtA_pstat_img8 (g + Z.of_nat k) ltac:(unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT in *; lia)) as (Hi & _).
  rewrite (Hk _ Hi). exact (Hv k Hkk). }
unfold fs_glob, fs_glob_at in *.
split; [apply VB; [lia | exact G1]|]. split; [apply VB; [lia | exact G2]|].
split; [apply VB; [lia | exact G3]|]. split; [apply VB; [lia | exact G4]|]. exact R.
Qed.

(* segment 1's write ranges hold no image byte: the two stack windows are at or above alloc_ceiling, the frame's
   shadow at or above SHADOW_OFF, and no byte of a live frame is an image byte (YCbq.frm_img) *)
Lemma crtA_img_keep2 : forall E ly S2 U (W : world tfibsegs) mem md pos sp0 sp1 (m m' : word -> option byte),
  ARU tfibsegs B ly S2 U W mem md -> In (3, pos) (frames S2) ->
  bv_unsigned (ew E 8) = sp0 -> bv_unsigned (ew E 9) = sp1 ->
  bv_unsigned (ew E 10) = frame_addr ly 3 pos ->
  bv_unsigned (ew E 48) = shadow_addr (frame_addr ly 3 pos) ->
  alloc_ceiling + 208 <= sp0 -> sp0 - 208 <= sp1 ->
  frame_of E (ss_mem crtA_ss2) m m' -> forall a, in_img tfibsegs a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
intros E ly S2 U W mem md pos sp0 sp1 m m' HARU Hin E8 E9 E10 E48 Hsp Hsp1 HF a Ha.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof (fs_segs_img a Ha) as Himg.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B ly S2 U W mem md HARU) as HAR.
destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U mem) md 3 pos HAR Hin) as (HF0 & HFc & _).
rewrite crt_frame3 in HFc.
pose proof (shadow_addr_bounds (frame_addr ly 3 pos) ltac:(rewrite C4; lia)) as (HS1 & _).
apply HF. rewrite (wz a ltac:(unfold FS_IMG_END in Himg; lia)).
intros (r & Hin2 & Hr). unfold crtA_ss2, FSW_frame3.fsw_resume_regions in Hin2. cbn [ss_mem In] in Hin2.
destruct Hin2 as [<-|[<-|[<-|[<-|[]]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val crtA_shadow_region] in Hr.
- rewrite E48 in Hr. rewrite crt_frame3 in Hr. change (512 / 8) with 64 in Hr.
  unfold FS_IMG_END, kLowMemEnd in *. lia.
- rewrite E8 in Hr. unfold FS_IMG_END in *. lia.
- rewrite E9 in Hr. unfold FS_IMG_END in *. lia.
- rewrite E10 in Hr. rewrite crt_frame3 in Hr.
  exact (frm_img tfibsegs B LAWS ly S2 W (unpoison U mem) md 3 pos a HAR Hin ltac:(rewrite crt_frame3; lia) Ha).
Qed.
(* ---- the call site of preset_base64_encode (B 0x81d7c, A 0x81c80), read off crtA_ss3. B: s10 = SF (atom 48),
   s6 = s3 = F (atom 10) there (A: s3 = SF, s7 = F); the one slot chunk is 0x50 := F (A: 0x10 and 0x50): the registers crt_callee_pre and
   encode_spec ask for, the two saved words of crt's frame record, and the frame's flag word. The saved words and the
   flag are chunks of crtA_ss3's own regions (the s0 region at atom 8, the frame at atom 10), so they are read with
   FSW_K.fsw_field rather than transported. ---- *)
Definition crtA_cs1a : list YP09.chunk := [YP09.mkChunk 0x50 (CVal 8 (SOff 47 0))].

Lemma crtA_site3 : forall (W : world tfibsegs) regs regs2 ms3 FL F SF sp0 sp1,
  st_ok tfibsegs (Ereg regs2 (crtA_extra regs FL F SF)) crtA_ss3 (restrict (w_H W) ms3) ->
  bv_unsigned (YK11.getr regs2 8%bv) = sp0 -> bv_unsigned (YK11.getr regs2 9%bv) = sp1 ->
  bv_unsigned (YK11.getr regs2 2%bv) = sp1 ->
  bv_unsigned (YK11.getr regs2 10%bv) = F -> 0 <= FL < 2 ^ 64 -> 0 <= F < 2 ^ 64 ->
  YK11.getr (ms_regs ms3) 1%bv = Z_to_bv 64 0x81d80 /\
  spZ (ms_regs ms3) = sp1 /\ s0Z (ms_regs ms3) = sp0 /\
  YK11.getr (ms_regs ms3) 3%bv = YK11.getr regs2 3%bv /\
  YK11.getr (ms_regs ms3) 4%bv = YK11.getr regs2 4%bv /\
  YK11.getr (ms_regs ms3) 10%bv = YK11.getr regs2 21%bv /\
  YK11.getr (ms_regs ms3) 11%bv = YK11.getr regs2 20%bv /\
  YK11.getr (ms_regs ms3) 18%bv = YK11.getr regs2 18%bv /\
  YK11.getr (ms_regs ms3) 26%bv = Z_to_bv 64 SF /\
  YK11.getr (ms_regs ms3) 22%bv = Z_to_bv 64 F /\ YK11.getr (ms_regs ms3) 19%bv = Z_to_bv 64 F /\
  YK11.getr (ms_regs ms3) 25%bv = YK11.getr regs2 25%bv /\
  rdword (aview tfibsegs (w_H W) (ms_mem ms3)) (sp0 - 8) = Some (bv_unsigned (YK11.getr regs 1%bv)) /\
  rdword (aview tfibsegs (w_H W) (ms_mem ms3)) (sp0 - 16) = Some (bv_unsigned (YK11.getr regs 8%bv)) /\
  rdword (aview tfibsegs (w_H W) (ms_mem ms3)) (F + 504) = Some FL.
Proof.
intros W regs regs2 ms3 FL F SF sp0 sp1 HS E8 E9 E2 E10 HFL HF.
set (E := Ereg regs2 (crtA_extra regs FL F SF)) in *.
assert (G : forall (r : bv 5) v, sr_get (ss_regs crtA_ss3) r = v -> YK11.getr (ms_regs ms3) r = sv_denot E v)
  by (intros r v Hv; rewrite (st_ok_restrict_reg tfibsegs (w_H W) E crtA_ss3 ms3 r HS), Hv; reflexivity).
assert (A : forall (r : bv 5) (n : nat), sr_get (ss_regs crtA_ss3) r = SOff n 0 ->
  YK11.getr (ms_regs ms3) r = ew E n) by (intros r n Hv; rewrite (G r _ Hv); apply fsw_SOff0).
assert (N : forall (r r' : bv 5) (n : nat), sr_get (ss_regs crtA_ss3) r = SOff n 0 -> Z.of_nat n = bv_unsigned r' ->
  YK11.getr (ms_regs ms3) r = YK11.getr regs2 r')
  by (intros r r' n Hv Hn; rewrite (A r n Hv); subst E; exact (ew_Ereg_nat regs2 _ n r' Hn)).
split; [rewrite (G 1%bv (SLit 0x81d80) ltac:(vm_compute; reflexivity)); apply bv_eq;
  rewrite denot_lit_U, !Z_to_bv_unsigned; reflexivity|].
split; [unfold spZ; rewrite (N 2%bv 2%bv 2%nat ltac:(vm_compute; reflexivity) eq_refl); exact E2|].
split; [unfold s0Z; rewrite (N 8%bv 8%bv 8%nat ltac:(vm_compute; reflexivity) eq_refl); exact E8|].
split; [exact (N 3%bv 3%bv 3%nat ltac:(vm_compute; reflexivity) eq_refl)|].
split; [exact (N 4%bv 4%bv 4%nat ltac:(vm_compute; reflexivity) eq_refl)|].
split; [exact (N 10%bv 21%bv 21%nat ltac:(vm_compute; reflexivity) eq_refl)|].
split; [exact (N 11%bv 20%bv 20%nat ltac:(vm_compute; reflexivity) eq_refl)|].
split; [exact (N 18%bv 18%bv 18%nat ltac:(vm_compute; reflexivity) eq_refl)|].
split; [rewrite (A 26%bv 48%nat ltac:(vm_compute; reflexivity)); subst E; apply crtA_extra_48|].
split; [rewrite (A 22%bv 10%nat ltac:(vm_compute; reflexivity)); subst E;
  rewrite (ew_Ereg_nat regs2 (crtA_extra regs FL F SF) 10 10%bv eq_refl); apply bv_eq; rewrite E10, Z_to_bv_unsigned;
  symmetry; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia|].
split; [rewrite (A 19%bv 10%nat ltac:(vm_compute; reflexivity)); subst E;
  rewrite (ew_Ereg_nat regs2 (crtA_extra regs FL F SF) 10 10%bv eq_refl); apply bv_eq; rewrite E10, Z_to_bv_unsigned;
  symmetry; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia|].
split; [exact (N 25%bv 25%bv 25%nat ltac:(vm_compute; reflexivity) eq_refl)|].
(* the two saved words and the flag, from the chunks of crtA_ss3's regions *)
assert (RD : forall (i : nat) (r : YP09.region) (n : nat) (b od : Z) (e : sv) v,
  nth_error (ss_mem crtA_ss3) i = Some r -> YP09.r_base r = Some n -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 8 e)) (YP09.r_chunks r) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview tfibsegs (w_H W) (ms_mem ms3)) (b + od) = Some v).
{ intros i r n b od e v Hi Hb Hn Hc He Hv.
  pose proof (fsw_region_nth E crtA_ss3 (restrict (w_H W) ms3) i r HS Hi) as HR.
  cbn [restrict ms_mem] in HR. destruct r as [rb rlo rhi rwlo rwhi rcs]. cbn [YP09.r_base] in Hb. subst rb.
  apply YF0x.val_mem_rdword; [exact Hv|].
  exact (fsw_field E (mrestrict (w_H W) (ms_mem ms3)) n b rcs rlo rhi rwlo rwhi od 8 e v HR Hn Hc He
    ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(cbn; lia)). }
split.
{ replace (sp0 - 8) with (sp0 + (-8)) by lia.
  apply (RD 1%nat crtA_s0_8 8%nat sp0 (-8) (SOff 33 0) (bv_unsigned (YK11.getr regs 1%bv)));
    [vm_compute; reflexivity | reflexivity | exact E8 | vm_compute; tauto
     | rewrite fsw_SOff0; subst E;
       change 33%nat with (33 + 0)%nat; rewrite (crtA_extra_saved regs2 regs FL F SF 0 ltac:(lia));
       cbn [nth crt_saved]; symmetry; apply Z_to_bv_bv_unsigned
     | apply u64_range]. }
split.
{ replace (sp0 - 16) with (sp0 + (-16)) by lia.
  apply (RD 1%nat crtA_s0_8 8%nat sp0 (-16) (SOff 34 0) (bv_unsigned (YK11.getr regs 8%bv)));
    [vm_compute; reflexivity | reflexivity | exact E8 | vm_compute; tauto
     | rewrite fsw_SOff0; subst E;
       change 34%nat with (33 + 1)%nat; rewrite (crtA_extra_saved regs2 regs FL F SF 1 ltac:(lia));
       cbn [nth crt_saved]; symmetry; apply Z_to_bv_bv_unsigned
     | apply u64_range]. }
apply (RD 3%nat crtA_frm_10 10%nat F 504 (SOff 46 0) FL);
  [vm_compute; reflexivity | reflexivity | exact E10 | vm_compute; tauto
   | rewrite fsw_SOff0; subst E; apply crtA_extra_46 | lia].
Qed.
(* ================= A0's walk tools =================
   crtA_and: the conjunction of two boundary invariants (the lanes' `INV /\ R`). crtA_st_set_reg: a register of a
   symbolic state may be re-expressed by any value of the same denotation (the run from 0x81db8 names s6 / s3 and s7 by
   the frame and want atoms 47 / 49, so the engine finds the frame region and the slot word; A: s7 and s10 from
   0x81cbc). crtA_chunk_swap: the same for
   a chunk's value. crtA_mk: two memories read the same at every byte of R (on the restricted view of each world);
   every keep the walk has - a journal's block clause, acall_kept, a runtime call's frame, a run's frame_of - gives one,
   and val_mem / zbytes_at / fs_rblock / fs_glob ride it. ---- *)
Definition crtA_and (I1 I2 : crt_inv) : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 => I1 cx E k ly3 S3 U3 W3 ms3 md3 /\ I2 cx E k ly3 S3 U3 W3 ms3 md3.

Lemma crtA_st_set_reg : forall E ss ms (r0 : bv 5) v,
  st_ok tfibsegs E ss ms -> bv_eqb r0 0%bv = false ->
  sv_denot E v = sv_denot E (sr_get (ss_regs ss) r0) ->
  st_ok tfibsegs E (mkSST (ss_pc ss) (sr_set (ss_regs ss) r0 v) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss))
    ms.
Proof.
intros E ss ms r0 v (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hr0 Hv.
unfold st_ok; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts]. repeat (split; [assumption|]). split; [|split; assumption].
intros r. destruct (decide (r = r0)) as [->|Hne].
- rewrite (sr_get_set_same _ _ _ Hr0), Hv. apply H7.
- rewrite (sr_get_set_other _ _ _ _ Hne). apply H7.
Qed.

Lemma crtA_chunk_swap : forall E m base d w v v',
  sv_denot E v' = sv_denot E v ->
  YP09.chunk_ok tfibsegs E m base (YP09.mkChunk d (CVal w v)) ->
  YP09.chunk_ok tfibsegs E m base (YP09.mkChunk d (CVal w v')).
Proof.
intros E m base d w v v' Hv H i Hi. destruct (H i Hi) as (b & Hb & Hm). exists b. split; [|exact Hm].
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb |- *. rewrite Hv. exact Hb.
Qed.

Definition crtA_mk (W W' : world tfibsegs) (m m' : word -> option byte) (R : Z -> Prop) : Prop :=
  forall a, R a -> mbyte tfibsegs (mrestrict (w_H W') m') a = mbyte tfibsegs (mrestrict (w_H W) m) a.
Lemma crtA_mk_trans : forall W1 W2 W3 m1 m2 m3 (R : Z -> Prop),
  crtA_mk W1 W2 m1 m2 R -> crtA_mk W2 W3 m2 m3 R -> crtA_mk W1 W3 m1 m3 R.
Proof. intros W1 W2 W3 m1 m2 m3 R H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.
Lemma crtA_mk_sub : forall W W' m m' (R R' : Z -> Prop),
  crtA_mk W W' m m' R -> (forall a, R' a -> R a) -> crtA_mk W W' m m' R'.
Proof. intros W W' m m' R R' H HR a Ha. exact (H a (HR a Ha)). Qed.
(* from a byte equality on the raw memories (a run's frame_of), at one world *)
Lemma crtA_mk_raw : forall (W : world tfibsegs) m m' (R : Z -> Prop),
  (forall a, R a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) -> crtA_mk W W m m' R.
Proof. intros W m m' R H a Ha. unfold mbyte, mrestrict. rewrite (H a Ha). reflexivity. Qed.
(* from an aview equality (a journal's clauses, acall_kept, a runtime call's frame) *)
Lemma crtA_mk_av : forall (W W' : world tfibsegs) m m' (R : Z -> Prop),
  (forall a, R a -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) -> crtA_mk W W' m m' R.
Proof. intros W W' m m' R H a Ha. apply mbyte_of_aview. exact (H a Ha). Qed.
Lemma crtA_mk_val : forall W W' m m' (R : Z -> Prop) a n v,
  crtA_mk W W' m m' R -> (forall k, (k < n)%nat -> R (a + Z.of_nat k)) ->
  val_mem tfibsegs (mrestrict (w_H W) m) a n v -> val_mem tfibsegs (mrestrict (w_H W') m') a n v.
Proof. intros W W' m m' R a n v HK HR Hv k Hk. rewrite (HK _ (HR k Hk)). exact (Hv k Hk). Qed.
Lemma crtA_mk_zbytes : forall W W' m m' (R : Z -> Prop) p l,
  crtA_mk W W' m m' R -> (forall i, 0 <= i < Z.of_nat (length l) -> R (p + i)) ->
  zbytes_at tfibsegs W m p l -> zbytes_at tfibsegs W' m' p l.
Proof.
intros W W' m m' R p l HK HR H. unfold zbytes_at, garr8 in *. intros j Hj. destruct (H j Hj) as (Hv & Hb).
split; [|exact Hb].
apply (crtA_mk_val W W' m m' R); [exact HK | | exact Hv].
intros k Hk. replace (p + Z.of_nat j + Z.of_nat k) with (p + (Z.of_nat j + Z.of_nat k)) by lia. apply HR. lia.
Qed.
Lemma crtA_mk_rblock : forall W W' m m' (R : Z -> Prop) ly S ly' S' p n,
  crtA_mk W W' m m' R -> (forall k, 0 <= k < 8 -> R (p - HEAD + k)) ->
  (In (p - HEAD, n + HEAD) (ablocks B ly S) -> In (p - HEAD, n + HEAD) (ablocks B ly' S')) ->
  fs_rblock tfibsegs B ly S W m p n -> fs_rblock tfibsegs B ly' S' W' m' p n.
Proof.
intros W W' m m' R ly S ly' S' p n HK HR Hin (H1 & H2 & H3 & H4).
split; [exact (Hin H1)|]. split; [exact H2|]. split; [exact H3|].
apply (crtA_mk_val W W' m m' R); [exact HK | intros k Hk; apply HR; lia | exact H4].
Qed.
Lemma crtA_mk_glob : forall W W' m m' (R : Z -> Prop) live peak cnt fail,
  crtA_mk W W' m m' R -> (forall a, inFP FS_PSTAT_FP a -> R a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros W W' m m' R live peak cnt fail HK HR (G1 & G2 & G3 & G4 & Rg).
assert (VB : forall g v, (G_FAIL <= g /\ g + 8 <= G_FAIL + 8 \/ G_LIVE <= g /\ g + 8 <= G_LIVE + 8 \/
    G_PEAK <= g /\ g + 8 <= G_PEAK + 8 \/ G_COUNT <= g /\ g + 8 <= G_COUNT + 8) ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W') m') g 8 v).
{ intros g v Hg Hv. apply (crtA_mk_val W W' m m' R); [exact HK | | exact Hv].
  intros k Hkk. assert (Hk8 : 0 <= Z.of_nat k < 8) by (cbn in Hkk; lia).
  destruct (crtA_pstat_img8 (g + Z.of_nat k) ltac:(unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT in *; lia)) as (_ & Hf).
  exact (HR _ Hf). }
unfold fs_glob, fs_glob_at in *.
split; [apply VB; [lia | exact G1]|]. split; [apply VB; [lia | exact G2]|].
split; [apply VB; [lia | exact G3]|]. split; [apply VB; [lia | exact G4]|]. exact Rg.
Qed.

(* a new block's 16-byte head joins U (fs_heads only reads ablocks) *)
Lemma crtA_heads_snoc : forall ly S ly' S' U h m,
  FSupoisonU.fs_heads B ly S U -> ablocks B ly' S' = ablocks B ly S ++ [(h, m)] -> 16 <= req_size m ->
  FSupoisonU.fs_heads B ly' S' (U ++ [(h, 16)]).
Proof.
intros ly S ly' S' U h m H E Hm r Hr. apply in_app_or in Hr as [Hr | [<- | []]].
- destruct (H r Hr) as (H16 & m' & Hin & Hm'). split; [exact H16|]. exists m'.
  split; [rewrite E; apply in_or_app; left; exact Hin | exact Hm'].
- cbn [fst snd]. split; [reflexivity|]. exists m.
  split; [rewrite E; apply in_or_app; right; left; reflexivity | exact Hm].
Qed.
(* a callee whose footprint is crt's own (FS_PSTAT_FP): its FP lies in fsw_fp_sub's image arm *)
Lemma crtA_fp_self : forall ly S lyc Sc own, fsw_fp_sub B ly S lyc Sc own FS_PSTAT_FP FS_PSTAT_FP.
Proof. intros ly S lyc Sc own a Ha. right. right. left. split; [exact Ha | exact (crt_pstat_img a Ha)]. Qed.

(* ================= the boundaries of segments 2-4: B 0x81d80, 0x81da4, 0x81db0, 0x81db8 (A 0x81c84, 0x81ca8, 0x81cb4,
   0x81cbc; the names keep A's pcs) =================
   What every one of them holds (crtA_core): the text's block (encode's post) on top of the entry's blocks, followed by
   the blocks of the calls since (blks); U = the entry's U plus the text's head; the text's block and bytes; the
   statics after encode's one g_count bump; and the callee-saved registers the rest of the walk reads: s2 = the shadow
   base, s4 = |bs|, s5 = bd, s6 = s3 = F, s9 = t (B: segment 5 reads F in s6 at 0x81dbc / 0x81dd4 and in s3 at 0x81de0,
   and crt_INV_81f58 states both; A: s7 = F). The body bd and the input t are entry blocks, so their bytes come from the
   journal's block clause wherever they are read (crtA_blk_keep) and are not carried. Ported from d25a984c903
   check_round_trip_stdefs.v St0 :215 / St1 :229 / St2 :244, whose cuts carry the same facts. ---- *)
Definition crtA_blen (cx : crt_cx) : Z := Z.of_nat (length (c_bs cx)).
Definition crtA_En (cx : crt_cx) : Z := (crtA_blen cx + 2) / 3 * 4.
Definition crtA_core (cx : crt_cx) (blks : list (Z * Z)) ly3 S3 U3 (W3 : world tfibsegs) (ms3 : machine_state) : Prop :=
  let mem := ms_mem ms3 in let r := ms_regs ms3 in
  (exists peak, fs_glob tfibsegs W3 mem (c_live cx + FSH_Fn_writer.enc_size (crtA_blen cx)) peak (c_cnt cx + 1) SIZE_MAXZ) /\
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++
    (c_text cx - HEAD, FSH_Fn_writer.enc_size (crtA_blen cx) + HEAD) :: blks /\
  U3 = c_U cx ++ [(c_text cx - HEAD, HEAD)] /\ FSupoisonU.fs_heads B ly3 S3 U3 /\
  4096 + HEAD <= c_text cx /\
  fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size (crtA_blen cx)) /\
  zbytes_at tfibsegs W3 mem (c_text cx) (WriterSpec.b64_enc (c_bs cx) ++ [0]) /\
  YK11.getr r 18%bv = w64 SHADOW_OFF /\ YK11.getr r 20%bv = w64 (crtA_blen cx) /\
  YK11.getr r 21%bv = w64 (c_bd cx) /\ YK11.getr r 22%bv = w64 (crt_F cx) /\ YK11.getr r 19%bv = w64 (crt_F cx) /\
  YK11.getr r 25%bv = w64 (c_t cx).
(* B 0x81d80 (A 0x81c84), the return of preset_base64_encode: a0 = text *)
Definition crtA_INV_81c84 : crt_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  crtA_core cx [] ly3 S3 U3 W3 ms3 /\ k = EV_preset_base64_encode /\
  YK11.getr (ms_regs ms3) 10%bv = w64 (c_text cx).
(* B 0x81da4 (A 0x81ca8), the return of malloc (want): a0 = want, s11 = En (0x81d98 `andi s11, a0, -4`; A: s6) *)
Definition crtA_INV_81ca8 : crt_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  crtA_core cx [(c_want cx, crtA_En cx + 1)] ly3 S3 U3 W3 ms3 /\ k = EV_preset_base64_encode + CRT_EV_WRAP /\
  YK11.getr (ms_regs ms3) 10%bv = w64 (c_want cx) /\ YK11.getr (ms_regs ms3) 27%bv = w64 (crtA_En cx).
(* B 0x81db0 (A 0x81cb4), the return of strlen (input): a0 = |tb|, s7 = want (0x81da4 `mv s7, a0`; A: s10) *)
Definition crtA_INV_81cb4 : crt_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  crtA_core cx [(c_want cx, crtA_En cx + 1)] ly3 S3 U3 W3 ms3 /\ k = EV_preset_base64_encode + CRT_EV_WRAP /\
  YK11.getr (ms_regs ms3) 10%bv = w64 (Z.of_nat (length (c_tb cx))) /\
  YK11.getr (ms_regs ms3) 27%bv = w64 (crtA_En cx) /\ YK11.getr (ms_regs ms3) 23%bv = w64 (c_want cx).
(* B 0x81db8 (A 0x81cbc), the return of malloc (same): a0 = same *)
Definition crtA_INV_81cbc : crt_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  exists same,
  crtA_core cx [(c_want cx, crtA_En cx + 1); (same, Z.of_nat (length (c_tb cx)) + 1)] ly3 S3 U3 W3 ms3 /\
  k = EV_preset_base64_encode + 2 * CRT_EV_WRAP /\
  YK11.getr (ms_regs ms3) 10%bv = w64 same /\
  YK11.getr (ms_regs ms3) 27%bv = w64 (crtA_En cx) /\ YK11.getr (ms_regs ms3) 23%bv = w64 (c_want cx).

(* ================= from the entry to B 0x81d80 (A 0x81c84): segment 0, the grant, segment 1 and the encode call ====
   crtA_seg0 / crtA_grant / crtA_seg1 bring the machine to preset_base64_encode's entry with the frame granted; the call
   site gives the callee's fpreU (FSH_crt_site.crt_callee_pre, crt's frame record read off crtA_ss3 by crtA_site3) and
   encode's premises (crtA_pre_encode: bd's bytes and block by the journal's block clause, the statics by the three
   runs' image keeps). The refused arm of encode_spec needs g_count = SIZE_MAX, which crt_base's `quiet` excludes; the
   success arm is crossed by crtA_after_call at nb = 48 (the SF premise at x26 = s10 on B), and the walk picks c_text := encode's result there. Ported
   from d25a984c903 check_round_trip_top.v crt_run_pro :953 / crt_run_sm :1017 / crt_run_setup :1129 and
   check_round_trip_sd0.v st0 :136 (St1 -> St0, the encode crossing). ---- *)
Lemma crtA_reg_eq : forall (x : word) z, bv_unsigned x = z -> 0 <= z < 2 ^ 64 -> x = Z_to_bv 64 z.
Proof. intros x z <- _. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* the chunks of a symbolic state's region, read on the machine *)
Lemma crtA_region_chunks : forall E ss (H : word -> bool) ms i r n b,
  st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r -> YP09.r_base r = Some n ->
  bv_unsigned (ew E n) = b -> Forall (YP09.chunk_ok tfibsegs E (mrestrict H (ms_mem ms)) b) (YP09.r_chunks r).
Proof.
intros E ss H ms i r n b HS Hi Hb Hn.
pose proof (fsw_region_nth E ss (restrict H ms) i r HS Hi) as HR. cbn [restrict ms_mem] in HR.
destruct HR as (_ & _ & _ & Hc). rewrite Hb in Hc. cbn [base_val] in Hc. rewrite Hn in Hc. exact Hc.
Qed.
(* an entry block keeps its bytes along the walk (the journal's block clause), as a crtA_mk *)
Lemma crtA_mk_blk : forall ly S U (W : world tfibsegs) mem md ly' S' U' (W' : world tfibsegs) mem' md' k STK sp0 own
  p n,
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  ajournal tfibsegs B STK sp0 FS_PSTAT_FP ly S W (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') ->
  crtA_mk W W' mem mem' (fun a => p <= a < p + req_size n).
Proof.
intros ly S U W mem md ly' S' U' W' mem' md' k STK sp0 own p n HARU HARU' HJ Hin Hin' a Ha.
apply mbyte_of_aview. replace a with (p + (a - p)) by lia.
exact (crtA_blk_keep ly S U W mem md ly' S' U' W' mem' md' k STK sp0 own p n (a - p) HARU HARU' HJ Hin Hin'
  ltac:(lia)).
Qed.

Lemma crtA_to_81c84 :
  crt_from SK B (crt_ss_ret 0x81d80 crtA_cs1a crt_csF) crtA_INV_81c84 ->
  forall cx0, crt_base B cx0 ->
  SRr tfibsegs (c_W cx0) (cfg_at tfibsegs A_check_round_trip (c_regs cx0) (c_mem cx0) (c_md cx0)) (crt_post SK B cx0).
Proof.
intros NEXT cx0 HB.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof crt_STK_eq as FS; unfold crt_STK in FS.
pose proof HB as ((HPRE & HRO) & Hheads & Htop & Hfrl & Hr10 & Hr11 & Hr12 & Htext & Hnonul & Htblen & Htwin & Htblk
  & Hdec & Hbd0 & Hbody & Hrb0 & Hstat & Hquiet & Hlive0 & Hcells & Hsp47 & Hnev0 & Hbb0 & HTU0).
destruct (crtA_len (c_tb cx0) (c_bs cx0) Hdec Htblen) as (Hok & Hlen & Henc).
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof (fsw_ARU B _ _ _ _ _ _ _ _ _ HPRE) as HARU0.
destruct Hstat as (peak0 & Hglob0).
pose proof Hquiet as (_ & Hcnt0 & Hcnt1).
set (ly := c_ly cx0) in *. set (S := c_S cx0) in *. set (U := c_U cx0) in *. set (W := c_W cx0) in *.
set (regs := c_regs cx0) in *. set (mem := c_mem cx0) in *. set (md := c_md cx0) in *.
set (sp1 := 32 * ((spZ regs - 192) / 32)).
(* segment 0 and the grant *)
apply (crtA_seg0 ly S U W regs mem md (c_ch cx0) FS_PSTAT_FP (crt_post SK B cx0) HPRE).
intros ms mat HS1 HJ1 HARU1 HF1 HFr1.
destruct (crtA_sm_site ly S U W regs mem md (c_ch cx0) ms HPRE HS1)
  as (R2 & R9 & Hsp1 & Hsp1a & Hsp1b & R1 & R10 & R3 & R4 & R8 & R18 & R20 & R21 & R25).
fold sp1 in R2, R9, Hsp1, Hsp1a, Hsp1b.
apply (crtA_grant ly S U W regs mem md (c_ch cx0) FS_PSTAT_FP ms mat _ HPRE Hfrl HS1 HJ1 HARU1).
intros pos S2 regs2 mem2 md2 HJ2 HARU2 Hfrs2 Hfresh Eab2 Hnev2 Hbb2 HP2 Hreg10 Hz2 Hflag2 HS2 Himg2.
pose proof (ARU_AR tfibsegs B ly S2 U W mem2 md2 HARU2) as HAR2.
assert (Hin3 : In (3, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 3 pos HAR2 Hin3) as (HF4096 & HFceil & HFapp).
rewrite crt_frame3 in HFceil, HFapp.
pose proof (al_flag _ _ LAWS _ _ _ _ _ 3 pos HAR2 Hin3) as (_ & _ & HFLapp & _).
set (F := frame_addr ly 3 pos) in *. set (FL := flag_addr ly 3 pos) in *. set (SF := shadow_addr F) in *.
pose proof (shadow_addr_bounds F ltac:(rewrite C4; lia)) as (HSF1 & HSF2).
assert (HFLr : 0 <= FL < 2 ^ 64)
  by (unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFLapp; pose proof (proj1 (@alloc_ceiling_val rc)); lia).
assert (G8 : bv_unsigned (YK11.getr regs2 8%bv) = spZ regs)
  by (rewrite (fsw_pres _ _ 8%bv HP2 ltac:(crtA_cs)), R8; reflexivity).
assert (G9 : bv_unsigned (YK11.getr regs2 9%bv) = sp1)
  by (rewrite (fsw_pres _ _ 9%bv HP2 ltac:(crtA_cs)), R9; apply wz; lia).
assert (G2 : bv_unsigned (YK11.getr regs2 2%bv) = sp1)
  by (rewrite (fsw_pres _ _ 2%bv HP2 ltac:(crtA_cs)), R2; apply wz; lia).
assert (G10 : bv_unsigned (YK11.getr regs2 10%bv) = F) by (rewrite Hreg10; apply wz; lia).
assert (E8 : bv_unsigned (ew (Ereg regs2 (crtA_extra regs FL F SF)) 8) = spZ regs)
  by (rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl); exact G8).
assert (E9 : bv_unsigned (ew (Ereg regs2 (crtA_extra regs FL F SF)) 9) = sp1)
  by (rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact G9).
assert (E10 : bv_unsigned (ew (Ereg regs2 (crtA_extra regs FL F SF)) 10) = F)
  by (rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact G10).
assert (E48 : bv_unsigned (ew (Ereg regs2 (crtA_extra regs FL F SF)) 48) = SF)
  by (rewrite crtA_extra_48; apply wz; unfold SF; lia).
(* segment 1 *)
apply (crtA_seg1 (Ereg regs2 (crtA_extra regs FL F SF)) STK_check_round_trip (spZ regs) FS_PSTAT_FP ly S W
  (unpoison U mem) md pos S2 U W (mkst regs2 (Z_to_bv 64 0x81c14) mem2 (seg_rom tfibsegs)) md2 0 sp1 _ eq_refl
  HS2 HJ2 HARU2 E48 E8 E9 E10 ltac:(lia)).
intros ms3 mat3 HS3 HJ3 HARU3 HF3 HFr3 HG3.
set (md3 := with_vm_backing (m_vm_lazy md2) mat3 md2) in *.
destruct (crtA_site3 W regs regs2 ms3 FL F SF (spZ regs) sp1 HS3 G8 G9 G2 G10 HFLr ltac:(lia))
  as (S1 & Ssp & Ss0 & S3' & S4' & S10 & S11 & S18 & S26 & S22 & S19 & S25 & Sw8 & Sw16 & Sflag).
assert (Gr : forall (q : bv 5) (n : nat), sr_get (ss_regs crtA_ss3) q = SOff n 0 -> Z.of_nat n = bv_unsigned q ->
  YK11.getr (ms_regs ms3) q = YK11.getr regs2 q)
  by (intros q n Hq Hn; exact (fsw_reg_atom (w_H W) regs2 _ crtA_ss3 ms3 q q n HS3 Hq Hn)).
assert (S9 : YK11.getr (ms_regs ms3) 9%bv = YK11.getr regs2 9%bv) by exact (Gr 9%bv 9%nat ltac:(vm_compute; reflexivity) eq_refl).
assert (S20 : YK11.getr (ms_regs ms3) 20%bv = YK11.getr regs2 20%bv)
  by exact (Gr 20%bv 20%nat ltac:(vm_compute; reflexivity) eq_refl).
assert (S21 : YK11.getr (ms_regs ms3) 21%bv = YK11.getr regs2 21%bv)
  by exact (Gr 21%bv 21%nat ltac:(vm_compute; reflexivity) eq_refl).
(* the walk's record at the call: c_text and c_want are picked at the returns *)
set (cx := crt_with cx0 pos 0 0).
assert (HFR : crt_frame_ok cx S2 W ms3).
{ split; [exact Hfrs2|]. split; [exact Hfresh|]. change (crt_F cx) with F. change (crt_FL cx) with FL.
  rewrite crt_frame3. replace (F + 512 - 8) with (F + 504) by lia. exact Sflag. }
assert (Hra3 : YK0s.ret_ok (YK11.getr (ms_regs ms3) 1%bv))
  by (rewrite S1; apply ret_ok_even; rewrite (wz 0x81d80) by lia; reflexivity).
assert (Gp3 : YK11.getr (ms_regs ms3) 3%bv = YK11.getr regs 3%bv)
  by (rewrite S3', (fsw_pres _ _ 3%bv HP2 ltac:(crtA_cs)); exact R3).
assert (Gp4 : YK11.getr (ms_regs ms3) 4%bv = YK11.getr regs 4%bv)
  by (rewrite S4', (fsw_pres _ _ 4%bv HP2 ltac:(crtA_cs)); exact R4).
destruct (crt_callee_pre SK B cx 0 ly S2 U W ms3 md3 STK_preset_base64_encode HB HJ3 HARU3 HFR Sw8 Sw16 Ssp Ss0 Hra3
  ltac:(unfold raZ; rewrite S1, wz by lia; lia) Gp3 Gp4 ltac:(apply Z.leb_le; vm_compute; reflexivity)
  ltac:(apply Z.leb_le; vm_compute; reflexivity))
  as (HPREe & _ & HFRLe & _).
(* bd's bytes and block at the call: the journal's block clause from the entry *)
destruct Hrb0 as (kk & Hrbk & Hkk). pose proof Hrbk as (Hinbd & Hal_bd & Hpos_bd & _).
assert (Hinbd2 : In (c_bd cx0 - HEAD, kk + HEAD) (ablocks B ly S2)) by (rewrite Eab2; exact Hinbd).
pose proof (crtA_mk_blk ly S U W mem md ly S2 U W (ms_mem ms3) md3 0 STK_check_round_trip (spZ regs) [(3, pos)]
  (c_bd cx0 - HEAD) (kk + HEAD) HARU0 HARU3 HJ3 Hinbd Hinbd2) as KB.
assert (Hrq : req_size (kk + HEAD) = kk + HEAD) by (unfold req_size, HEAD in *; destruct (kk + 16 =? 0) eqn:Ez; lia).
rewrite Hrq in KB.
rewrite (crtA_zs_bz _ Hok) in Hbody.
assert (Hbytes : zbytes_at tfibsegs W (ms_mem ms3) (c_bd cx0) (c_bs cx0)).
{ apply (crtA_mk_zbytes W W mem (ms_mem ms3) _ (c_bd cx0) (c_bs cx0) KB); [|exact Hbody].
  intros i Hi. unfold HEAD in *. lia. }
assert (Hblk : exists kd, fs_rblock tfibsegs B ly S2 W (ms_mem ms3) (c_bd cx0) kd /\ Z.of_nat (length (c_bs cx0)) <= kd).
{ exists kk. split; [|exact Hkk].
  apply (crtA_mk_rblock W W mem (ms_mem ms3) _ ly S ly S2 (c_bd cx0) kk KB); [unfold HEAD in *; intros; lia | | exact Hrbk].
  intros _. exact Hinbd2. }
(* the statics at the call: the three runs keep every static byte *)
assert (Hglob : fs_glob tfibsegs W (ms_mem ms3) (c_live cx0) peak0 (c_cnt cx0) SIZE_MAXZ).
{ apply (crtA_mk_glob W W mem (ms_mem ms3) (inFP FS_PSTAT_FP)); [| intros a Ha; exact Ha | exact Hglob0].
  apply (crtA_mk_trans W W W mem (ms_mem ms) (ms_mem ms3)).
  - apply crtA_mk_raw. intros a Ha.
    exact (crtA_img_keep0 (Ereg regs fs_extraT) (spZ regs) mem (ms_mem ms)
      ltac:(rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity) ltac:(lia) HF1 a (crt_pstat_img a Ha)).
  - apply (crtA_mk_trans W W W (ms_mem ms) mem2 (ms_mem ms3)).
    + apply crtA_mk_av. intros a Ha. destruct (proj1 IMG a Ha) as (Hno & Her).
      exact (Himg2 a (crt_pstat_img a Ha) Hno Her).
    + apply crtA_mk_raw. intros a Ha.
      exact (crtA_img_keep2 (Ereg regs2 (crtA_extra regs FL F SF)) ly S2 U W mem2 md2 pos (spZ regs) sp1 mem2
        (ms_mem ms3) HARU2 Hin3 E8 E9 E10 E48 ltac:(lia) ltac:(lia) HF3 a (crt_pstat_img a Ha)). }
(* encode's own SRr *)
assert (Ga0 : YK11.getr (ms_regs ms3) 10%bv = w64 (c_bd cx0))
  by (rewrite S10, (fsw_pres _ _ 21%bv HP2 ltac:(crtA_cs)), R21; exact Hr11).
assert (Ga1 : YK11.getr (ms_regs ms3) 11%bv = w64 (Z.of_nat (length (c_bs cx0))))
  by (rewrite S11, (fsw_pres _ _ 20%bv HP2 ltac:(crtA_cs)), R20; exact Hr12).
pose proof (crtA_pre_encode cx 0 ly S2 U W ms3 md3 peak0 HB HJ3 HARU3 HPREe
  (crtA_heads B ly S ly S2 U Eab2 Hheads) ltac:(unfold raZ; rewrite S1; apply wz; lia) HFRLe Ga0 Ga1 Hbytes Hblk Hglob
  ltac:(change (c_S cx) with S; rewrite Hnev2; lia) ltac:(apply Z.leb_le; vm_compute; reflexivity)
  ltac:(change (c_S cx) with S; rewrite Hbb2; lia)) as HENC.
assert (Hres3 : ss_resv crtA_ss3 = None) by (vm_compute; reflexivity).
assert (Hpc3 : ss_pc crtA_ss3 = A_preset_base64_encode) by (vm_compute; reflexivity).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ crtA_ss3 ms3 HS3 Hres3) as Ems. rewrite Hpc3 in Ems.
rewrite Ems.
eapply SRr_bind; [exact HENC|].
cbv beta. intros W' c' _ [(Hmax & _) | (q & _ & _ & HPOST)].
{ exfalso. unfold SIZE_MAXZ, EV_check_round_trip in *. cbn [c_cnt cx crt_with] in Hmax. lia. }
destruct HPOST as (ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP' & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
(* the return: the walk picks c_text := q *)
set (cx' := crt_with cx0 pos q 0).
assert (EX : forall j, (j < 16)%nat ->
  nth j (crtA_extra regs FL F SF) (Z_to_bv 64 0) = nth j (crt_extra cx') (Z_to_bv 64 0)).
{ intros j Hj. do 16 (destruct j as [|j]; [reflexivity|]). lia. }
assert (HEa : forall n, (32 <= n < 48)%nat ->
  ew (Ereg regs2 (crtA_extra regs FL F SF)) n = nth (n - 32) (crt_extra cx') (Z_to_bv 64 0)).
{ intros n Hn. replace n with (32 + (n - 32))%nat at 1 by lia. rewrite ew_Ereg_extra. apply EX. lia. }
assert (V10 : sv_denot (Ereg regs2 (crtA_extra regs FL F SF)) (SOff 47 0) =
  sv_denot (Ereg regs2 (crtA_extra regs FL F SF)) (SOff 10 0)).
{ rewrite !fsw_SOff0, crtA_extra_47, (ew_Ereg_nat regs2 _ 10 10%bv eq_refl), Hreg10. reflexivity. }
assert (HSV : Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (crtA_extra regs FL F SF)) (mrestrict (w_H W) (ms_mem ms3))
  (spZ (c_regs cx'))) crt_sv_chunks).
{ pose proof (crtA_region_chunks _ crtA_ss3 (w_H W) ms3 1 crtA_s0_8 8 (spZ regs) HS3 ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) E8) as Hc.
  replace (YP09.r_chunks crtA_s0_8) with crt_sv_chunks in Hc by (vm_compute; reflexivity). exact Hc. }
(* B: segment 1 stores ONE s1 slot, 0x50 := s6 = F (0x81c44; A stores 0x10 and 0x50) *)
assert (HSL : Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (crtA_extra regs FL F SF)) (mrestrict (w_H W) (ms_mem ms3)) sp1)
  [YP09.mkChunk 80 (CVal 8 (SOff 10 0))]).
{ pose proof (crtA_region_chunks _ crtA_ss3 (w_H W) ms3 2 (nth 2 (ss_mem crtA_ss3) (fstk 0)) 9 sp1 HS3
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) E9) as Hc.
  replace (YP09.r_chunks (nth 2 (ss_mem crtA_ss3) (fstk 0))) with
    [YP09.mkChunk 80 (CVal 8 (SOff 10 0))] in Hc by (vm_compute; reflexivity).
  exact Hc. }
assert (HCS1 : Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (crtA_extra regs FL F SF)) (mrestrict (w_H W) (ms_mem ms3))
  (crt_sp1 cx')) crtA_cs1a).
{ change (crt_sp1 cx') with sp1. inversion HSL as [|? ? H80 _]; subst.
  unfold crtA_cs1a. constructor; [exact (crtA_chunk_swap _ _ _ _ _ _ _ V10 H80) | constructor]. }
assert (HCSF : Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (crtA_extra regs FL F SF)) (mrestrict (w_H W) (ms_mem ms3))
  (crt_F cx')) crt_csF).
{ pose proof (crtA_region_chunks _ crtA_ss3 (w_H W) ms3 3 crtA_frm_10 10 F HS3 ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) E10) as Hc.
  rewrite Forall_forall in Hc. unfold crt_csF. rewrite crt_frame3. constructor; [|constructor].
  apply Hc. vm_compute. tauto. }
assert (HnFP : forall a, F <= a < F + 512 -> ~ inFP FS_PSTAT_FP a).
{ intros a Ha HFP. exact (frm_img tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 3 pos a HAR2 Hin3
    ltac:(rewrite crt_frame3; lia) (crt_pstat_img a HFP)). }
assert (EQ1 : YK11.getr (ms_regs ms3) 1%bv = Z_to_bv 64 0x81d80) by exact S1.
destruct (crtA_after_call cx' (Ereg regs2 (crtA_extra regs FL F SF)) 0 ly S2 U W ms3 md3 STK_preset_base64_encode
  FS_PSTAT_FP ly' S' (U ++ [(q - HEAD, HEAD)]) W' regs' mem' md' EV_preset_base64_encode 0x81d80 crtA_cs1a crt_csF 48
  ltac:(lia) HEa HJ3 HARU3 HFR
  ltac:(apply crtA_reg_eq; [exact Ssp | change (crt_sp1 cx') with sp1; lia])
  ltac:(exact Gp3) ltac:(exact Gp4)
  ltac:(apply crtA_reg_eq; [exact Ss0 | unfold spZ; apply u64_range])
  ltac:(rewrite S9; apply crtA_reg_eq; [exact G9 | change (crt_sp1 cx') with sp1; lia])
  S26 HSV HCS1
  ltac:(unfold crtA_atomlt, crtA_cs1a; repeat (apply Forall_cons; [do 4 eexists; split; [reflexivity | lia]|]);
        apply Forall_nil)
  ltac:(unfold crtA_cs1a; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil)
  HCSF
  ltac:(unfold crt_csF; rewrite crt_frame3; apply Forall_cons; [cbn; lia | apply Forall_nil])
  ltac:(unfold crtA_atomlt, crt_csF; apply Forall_cons; [do 4 eexists; split; [reflexivity | lia] | apply Forall_nil])
  ltac:(intros c Hc i Hi; unfold crt_csF in Hc; destruct Hc as [<-|[]]; cbn in Hi; cbn [YP09.c_off];
        change (crt_F cx') with F; apply HnFP; rewrite crt_frame3; lia)
  ltac:(intros i Hi; apply HnFP; change (crt_F cx') with F; rewrite crt_frame3; lia)
  ltac:(rewrite Ssp in HJc; exact HJc) OK' PO' (crtA_fp_self _ _ _ _ _) HP'
  ltac:(apply Z.leb_le; vm_compute; reflexivity) ltac:(apply Z.leb_le; vm_compute; reflexivity))
  as (HJ' & HARU' & HFO' & HE' & HS').
rewrite EQ1.
assert (HSQ : 0 <= c_cnt cx0 + 1 < 2 ^ 64) by (unfold EV_check_round_trip in Hcnt1; lia).
apply (NEXT cx' (Ereg regs' (crt_extra cx')) (0 + EV_preset_base64_encode) ly' S' (U ++ [(q - HEAD, HEAD)]) W'
  (mkst regs' (Z_to_bv 64 0x81d80) mem' (seg_rom tfibsegs)) md' HB HE' HJ' HARU' HFO'); [|exact HS'].
(* crtA_INV_81c84 at the return *)
assert (Pq : forall r : bv 5, acallee_saved (bv_unsigned r) -> YK11.getr regs' r = YK11.getr regs2 r ->
  YK11.getr regs' r = YK11.getr regs2 r) by (intros r _ H; exact H).
split; [|split; [lia | exact Q1]].
cbn zeta. unfold crtA_core. cbn [ms_mem ms_regs mkst].
split.
{ exists (Z.max peak0 (c_live cx0 + FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx0))))).
  rewrite Z.mod_small in Q7 by exact HSQ. exact Q7. }
split; [rewrite Q3, Eab2; reflexivity|].
split; [reflexivity|].
split.
{ apply (crtA_heads_snoc ly S ly' S' U (q - HEAD) (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx0))) + HEAD)
    Hheads ltac:(rewrite Q3, Eab2; reflexivity)).
  unfold req_size, HEAD, FSH_Fn_writer.enc_size. destruct (_ =? 0) eqn:Ez; [apply Z.eqb_eq in Ez|]; 
  pose proof (Zle_0_nat (length (c_bs cx0))); Z.div_mod_to_equations; lia. }
split; [exact Q2|]. split; [exact Q4|]. split; [exact Q5|].
assert (K3 : forall r : bv 5, acallee_saved (bv_unsigned r) -> YK11.getr regs' r = YK11.getr (ms_regs ms3) r)
  by (intros r Hr; exact (fsw_pres _ _ r HP' Hr)).
split; [rewrite (K3 18%bv ltac:(crtA_cs)), S18, (fsw_pres _ _ 18%bv HP2 ltac:(crtA_cs)); exact R18|].
split; [rewrite (K3 20%bv ltac:(crtA_cs)), S20, (fsw_pres _ _ 20%bv HP2 ltac:(crtA_cs)), R20; exact Hr12|].
split; [rewrite (K3 21%bv ltac:(crtA_cs)), S21, (fsw_pres _ _ 21%bv HP2 ltac:(crtA_cs)), R21; exact Hr11|].
split; [rewrite (K3 22%bv ltac:(crtA_cs)), S22; reflexivity|].
split; [rewrite (K3 19%bv ltac:(crtA_cs)), S19; reflexivity|].
rewrite (K3 25%bv ltac:(crtA_cs)), S25, (fsw_pres _ _ 25%bv HP2 ltac:(crtA_cs)), R25; exact Hr10.
Qed.

(* ================= segments 2-4: shared steps =================
   crtA_core_move carries a boundary's core across any step that appends blocks, keeps U, the five callee-saved
   registers and the bytes crtA_kept names (the text's block and the four statics). crtA_run_slots is a run from a
   boundary whose only writable regions are the s0 words and the s1 slots (plus read-only cells), so every byte below
   alloc_ceiling survives it. crtA_malloc_call is one `jal __wrap_malloc` of the walk: the callee's fpreU at ASTACK
   (crt_callee_pre), the contract through FSW_malloc_free.fsw_aj_malloc04U_sub over the call site's own trivial journal,
   and crtA_after_call for the boundary state at the return; the walk picks c_want := w res there. *)
Lemma crtA_heads_app : forall ly S ly' S' U l,
  FSupoisonU.fs_heads B ly S U -> ablocks B ly' S' = ablocks B ly S ++ l -> FSupoisonU.fs_heads B ly' S' U.
Proof.
intros ly S ly' S' U l H E r Hr. destruct (H r Hr) as (H16 & m & Hin & Hm). split; [exact H16|]. exists m.
split; [rewrite E; apply in_or_app; left; exact Hin | exact Hm].
Qed.
Definition crtA_txt (cx : crt_cx) (a : Z) : Prop :=
  c_text cx - HEAD <= a < c_text cx + FSH_Fn_writer.enc_size (crtA_blen cx).
Definition crtA_kept (cx : crt_cx) (a : Z) : Prop := crtA_txt cx a \/ inFP FS_PSTAT_FP a.
(* B: crtA_core holds s2 s4 s5 s6 s3 s9 = x18 x20 x21 x22 x19 x25 (A: x18 x20 x21 x23 x25; F is s6 = x22 and s3 = x19
   on B, s7 = x23 on A) *)
Lemma crtA_core_move : forall cx blks new ly3 S3 U3 (W3 : world tfibsegs) ms3 ly' S' (W' : world tfibsegs) ms',
  crtA_core cx blks ly3 S3 U3 W3 ms3 ->
  ablocks B ly' S' = ablocks B ly3 S3 ++ new ->
  crtA_mk W3 W' (ms_mem ms3) (ms_mem ms') (crtA_kept cx) ->
  (forall r : bv 5, In r [18; 20; 21; 22; 19; 25]%bv -> YK11.getr (ms_regs ms') r = YK11.getr (ms_regs ms3) r) ->
  crtA_core cx (blks ++ new) ly' S' U3 W' ms'.
Proof.
intros cx blks new ly3 S3 U3 W3 ms3 ly' S' W' ms'
  (Hg & Hab & HU & Hh & H4 & Hrb & Hz & R18 & R20 & R21 & R22 & R19 & R25) Hab' HK HR.
pose proof (check_round_trip_loops.enc_len_Z (c_bs cx)) as HL.
assert (Hl0 : 0 <= crtA_blen cx) by (unfold crtA_blen; lia).
unfold crtA_core. cbv zeta.
split; [destruct Hg as (peak & Hg); exists peak; exact (crtA_mk_glob _ _ _ _ _ _ _ _ _ HK (fun a Ha => or_intror Ha) Hg)|].
split; [rewrite Hab', Hab, <- app_assoc; reflexivity|].
split; [exact HU|].
split; [exact (crtA_heads_app _ _ _ _ _ _ Hh Hab')|].
split; [exact H4|].
split.
{ apply (crtA_mk_rblock W3 W' (ms_mem ms3) (ms_mem ms') (crtA_kept cx) ly3 S3 ly' S' _ _ HK);
    [| intros Hin; rewrite Hab'; apply in_or_app; left; exact Hin | exact Hrb].
  intros j Hj. left. unfold crtA_txt, FSH_Fn_writer.enc_size, HEAD in *. pose proof (Z.div_pos (crtA_blen cx + 2) 3).
  lia. }
split.
{ apply (crtA_mk_zbytes W3 W' (ms_mem ms3) (ms_mem ms') (crtA_kept cx) _ _ HK); [|exact Hz].
  intros i Hi. left. rewrite length_app in Hi. cbn [length] in Hi. rewrite Nat2Z.inj_add, HL in Hi.
  unfold crtA_txt, FSH_Fn_writer.enc_size, HEAD, crtA_blen in *. lia. }
split; [rewrite HR; [exact R18 | cbn; tauto]|]. split; [rewrite HR; [exact R20 | cbn; tauto]|].
split; [rewrite HR; [exact R21 | cbn; tauto]|]. split; [rewrite HR; [exact R22 | cbn; tauto]|].
split; [rewrite HR; [exact R19 | cbn; tauto]|].
rewrite HR; [exact R25 | cbn; tauto].
Qed.

(* the boundary state without the frame's two regions, with read-only cells xs in front (crt_site.crt_ss2's shape,
   generic in the slot chunks) *)
Lemma crtA_sub2 : forall r cs csF, submem [crt_s0_region; crt_slot_region cs] (ss_mem (crt_ss_ret r cs csF)).
Proof.
intros r cs csF. cbn [ss_mem crt_ss_ret fss_ret_s0_args fss_ret_s0_regs crt_ret_regions].
apply submem_keep; [apply subregion_refl|]. apply submem_keep; [apply subregion_refl|]. apply submem_nil.
Qed.
Definition crtA_facts0 : facts := mkFacts ((8%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: crt_ret_facts) [] [].
Definition crtA_ssR (r : Z) (cs : list YP09.chunk) (xs : list YP09.region) : sstate :=
  mkSS r sr_atoms (xs ++ [crt_s0_region; crt_slot_region cs]) None crtA_facts0.
(* the sp facts of the walk, from crt_base alone *)
Lemma crtA_spf : forall cx, crt_base B cx ->
  spZ (c_regs cx) mod 16 = 0 /\ alloc_ceiling + STK_check_round_trip <= spZ (c_regs cx) /\
  spZ (c_regs cx) <= 2 ^ 47 /\ 0 <= STK_check_round_trip /\
  spZ (c_regs cx) - 208 <= crt_sp1 cx <= spZ (c_regs cx) - 192 /\ crt_sp1 cx mod 32 = 0 /\ crt_sp1 cx mod 16 = 0.
Proof.
intros cx HB. pose proof HB as (HPRE & _).
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPRE)) as (Hal16 & Hceil0 & H47 & HS0).
pose proof asan_consts as (C1 & _).
destruct (crt_sp1_facts cx Hal16 ltac:(lia)) as (Hs1 & Hs2 & Hs3).
split; [exact Hal16|]. split; [exact Hceil0|]. split; [exact H47|]. split; [exact HS0|].
split; [exact Hs1|]. split; [exact Hs2 | exact Hs3].
Qed.
Lemma crtA_run_slots : forall r0 stop cs xs ssC cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3
  (Q : world tfibsegs -> config -> Prop),
  sym_run_toN tfibsegs crt_tbl FUEL stop (crtA_ssR r0 cs xs) = (ssC, RS_running) ->
  Forall (fun rg => YP09.r_whi rg <= YP09.r_wlo rg) xs ->
  crt_base B cx -> crt_E cx E ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  st_ok tfibsegs E (crtA_ssR r0 cs xs) (restrict (w_H W3) ms3) ->
  (forall ms mat, st_ok tfibsegs E ssC (restrict (w_H W3) ms) ->
     ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
       (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms))
       (with_vm_backing (m_vm_lazy md3) mat md3) k ->
     ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) ->
     same_below (ms_mem ms3) (ms_mem ms) alloc_ceiling ->
     SRr tfibsegs W3 (mkCfg ms (with_vm_backing (m_vm_lazy md3) mat md3)) Q) ->
  SRr tfibsegs W3 (mkCfg ms3 md3) Q.
Proof.
intros r0 stop cs xs ssC cx E k ly3 S3 U3 W3 ms3 md3 Q HRUN Hro HB HE HJ HARU HS K.
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
destruct (crtA_spf cx HB) as (Hal16 & Hceil0 & H47 & HS0 & Hsp1 & Hm32 & Hm16).
pose proof crt_STK_eq as FS; unfold crt_STK in FS. pose proof asan_consts as (C1 & _).
assert (AW2 : awr_ok tfibsegs B E [crt_s0_region; crt_slot_region cs] STK_check_round_trip (spZ (c_regs cx))
    FS_PSTAT_FP (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx))).
{ eapply awr_ok_cons_stack; [reflexivity | exact E8 | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (d := crt_sp1 cx - spZ (c_regs cx));
    [reflexivity | rewrite E9; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
eapply (fsw_run_to_AJU (SK := SK) B crt_tbl crt_tbl_ok W3 FUEL stop E (crtA_ssR r0 cs xs) ssC RS_running ms3
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS HRUN I HARU HJ).
- unfold crtA_ssR. cbn [ss_mem]. clear HRUN HS. induction Hro as [|x xs Hx Hxs IH]; cbn [app]; [exact AW2|].
  apply awr_ok_cons_ro; [exact Hx | exact IH].
- intros ms mat HSC HJC HARUC HF HFr HG. apply (K ms mat HSC HJC HARUC).
  intros x Hx. apply HF. rewrite (wz x) by (pose proof (@alloc_ceiling_lt rc); lia). intros (rg & Hin & Hr).
  unfold crtA_ssR in Hin. cbn [ss_mem] in Hin. apply in_app_or in Hin as [Hin | Hin].
  + rewrite Forall_forall in Hro. pose proof (Hro rg Hin). lia.
  + cbn [In] in Hin. destruct Hin as [<-|[<-|[]]];
      cbn [crt_s0_region fs_ret_s0_region crt_slot_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      [rewrite E8 in Hr | rewrite E9 in Hr]; lia.
Qed.

(* the constant 0xaaaaaaaaaaaaaaab of segment 2's division by 3 (B 0x81d84 `auipc` / 0x81d88 `ld` at 0x10320, A 0x81c88 /
   0x81c8c at the same address; MEASURED with pyelftools: B's read-only PT_LOAD [0x10000, 0x2fd20) holds
   ab aa aa aa aa aa aa aa there): a read-only cell of the run state, read off rom_view (crt_rom) *)
Definition crtA_kcell : YP09.region :=
  YP09.mkRegion None 0x10320 0x10328 0 0 [YP09.mkChunk 0x10320 (CVal 8 (SLit 0xaaaaaaaaaaaaaaab))].
Lemma crtA_kcell_rom : forall a, 0x10320 <= a < 0x10328 -> in_rom tfibsegs a.
Proof.
intros a Ha.
assert (Hx : existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? 0x10320) &&
  (0x10328 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hx as (sg & Hin & Hc). apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [H0 H1].
apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hin|]. split; [exact H0|]. lia.
Qed.
Lemma crtA_kcell_ok : forall E (W : world tfibsegs) m, rom_view tfibsegs W m ->
  region_ok tfibsegs E (mrestrict (w_H W) m) crtA_kcell.
Proof.
intros E W m HR.
assert (VB : forall k, (k < 8)%nat -> option_map (fun b : byte => bv_unsigned b)
  (seg_rom tfibsegs (Z_to_bv 64 (0x10320 + Z.of_nat k))) = Some (le_byte 0xaaaaaaaaaaaaaaab 8 k)).
{ intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. }
unfold region_ok, crtA_kcell. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val tfibsegs E _ 0 0x10320 8 (SLit 0xaaaaaaaaaaaaaaab) 0xaaaaaaaaaaaaaaab);
  [reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_l.
intros k Hk. pose proof (eq_trans (HR _ (crtA_kcell_rom (0x10320 + Z.of_nat k) ltac:(lia))) (VB k Hk)) as Hv.
unfold aview in Hv. destruct (mbyte tfibsegs (mrestrict (w_H W) m) (0x10320 + Z.of_nat k)) as [b|] eqn:Hb;
  cbn [option_map] in Hv; [|discriminate]. injection Hv as Hv.
f_equal. rewrite <- (Z_to_bv_bv_unsigned _ b) at 1. f_equal. exact Hv.
Qed.
(* B: s11 := ((mulhu (|bs| + 2, 0xaaaaaaaaaaaaaaab) << 1) & -4) at 0x81d8c .. 0x81d98 is (|bs| + 2) / 3 * 4 (A: s6 at
   0x81c90 .. 0x81c9c; MEASURED by the engine on B: x27 is exactly crtA_sv6 at the malloc call) *)
Lemma crtA_land_m4 : forall a, 0 <= a < 2 ^ 64 -> Z.land a (2 ^ 64 - 4) = a - a mod 4.
Proof.
intros a Ha.
replace (2 ^ 64 - 4) with (Z.ldiff (Z.ones 64) (Z.ones 2)).
2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
pose proof (Z.div_mod a 4 ltac:(lia)). lia.
Qed.
Definition crtA_sv6 : sv :=
  SAlu ALU_AND (SAlu ALU_SLL (SMd M_MULHU (SOff 20 2) (SLit 12297829382473034411)) (SLit 1)) (SLit (-4)).
Lemma crtA_En_U : forall E l, bv_unsigned (ew E 20) = l -> 0 <= l <= 2359298 -> YP0e.U E crtA_sv6 = (l + 2) / 3 * 4.
Proof.
intros E l Hl Hr. unfold crtA_sv6.
rewrite !U_SAlu, U_SMd, U_SOff, !U_SLit. rewrite Hl.
cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
rewrite (Z.mod_small (l + 2)) by lia.
change (12297829382473034411 mod 2 ^ 64) with 12297829382473034411.
change (1 mod 2 ^ 64) with 1. replace ((-4) mod 2 ^ 64) with (2 ^ 64 - 4) by reflexivity.
change (Z.of_N 64) with 64. change (Z.land 1 63) with 1.
rewrite Z.shiftr_div_pow2 by lia.
assert (Hq : (l + 2) * 12297829382473034411 / 2 ^ 64 = 2 * (l + 2) / 3).
{ Z.div_mod_to_equations. lia. }
rewrite (Z.mod_small ((l + 2) * 12297829382473034411 / 2 ^ 64)) by (rewrite Hq; Z.div_mod_to_equations; lia).
rewrite Hq, Z.shiftl_mul_pow2 by lia.
rewrite (Z.mod_small (2 * (l + 2) / 3 * 2 ^ 1)) by (Z.div_mod_to_equations; lia).
rewrite crtA_land_m4 by (Z.div_mod_to_equations; lia).
rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
Z.div_mod_to_equations. lia.
Qed.
Lemma crtA_En_denot : forall E l, bv_unsigned (ew E 20) = l -> 0 <= l <= 2359298 ->
  sv_denot E crtA_sv6 = Z_to_bv 64 ((l + 2) / 3 * 4) /\
  sv_denot E (SAlu ALU_ADD crtA_sv6 (SLit 1)) = Z_to_bv 64 ((l + 2) / 3 * 4 + 1).
Proof.
intros E l Hl Hr. pose proof (crtA_En_U E l Hl Hr) as HU.
split; rewrite denot_lit_U; f_equal; [exact HU|].
rewrite U_SAlu, HU, U_SLit. cbn [zalu_raw]. unfold zcanon, M64.
rewrite (Z.mod_small 1) by lia. apply Z.mod_small. Z.div_mod_to_equations. lia.
Qed.

(* B: the frame-shadow register crt_E and crtA_after_call read is s10 = x26 (A: s3 = x19) *)
Lemma crtA_malloc_call : forall (w : Z -> Z) (nb : nat) cx E k ly3 S3 U3 (W3 : world tfibsegs) regsT memT md n r cs1
  (Q : world tfibsegs -> config -> Prop),
  crt_base B cx -> (47 <= nb <= 50)%nat ->
  (forall res n', (32 <= n' < nb)%nat ->
     ew E n' = nth (n' - 32) (crt_extra (crt_with cx (c_pos cx) (c_text cx) (w res))) (Z_to_bv 64 0)) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 memT) md k ->
  ARU tfibsegs B ly3 S3 U3 W3 memT md ->
  frames S3 = (3, c_pos cx) :: frames (c_S cx) -> ~ In (3, c_pos cx) (frames (c_S cx)) ->
  rdword (aview tfibsegs (w_H W3) memT) (crt_F cx + fs_frame_bytes 3 - 8) = Some (crt_FL cx) ->
  YK11.getr regsT 1%bv = Z_to_bv 64 r -> 4096 <= r < 2 ^ 64 -> r mod 2 = 0 ->
  YK11.getr regsT 2%bv = Z_to_bv 64 (crt_sp1 cx) ->
  YK11.getr regsT 3%bv = YK11.getr (c_regs cx) 3%bv -> YK11.getr regsT 4%bv = YK11.getr (c_regs cx) 4%bv ->
  YK11.getr regsT 8%bv = Z_to_bv 64 (spZ (c_regs cx)) -> YK11.getr regsT 9%bv = Z_to_bv 64 (crt_sp1 cx) ->
  YK11.getr regsT 26%bv = Z_to_bv 64 (crt_SF cx) ->
  YK11.getr regsT 10%bv = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes S3 + n <= LIVE_MAX -> st_nev S3 < EV_MAX ->
  rdword (aview tfibsegs (w_H W3) memT) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview tfibsegs (w_H W3) memT) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (spZ (c_regs cx))) crt_sv_chunks ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (crt_sp1 cx)) cs1 -> crtA_atomlt nb cs1 ->
  Forall (fun c => 0x10 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= 0x58) cs1 ->
  (forall res ly' S' (W' : world tfibsegs) regs' mem' md',
     ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
       (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly' S' W' (unpoison U3 mem') md' (k + 1) ->
     ARU tfibsegs B ly' S' U3 W' mem' md' ->
     crt_frame_ok (crt_with cx (c_pos cx) (c_text cx) (w res)) S' W' (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs)) ->
     crt_E (crt_with cx (c_pos cx) (c_text cx) (w res))
       (Ereg regs' (crt_extra (crt_with cx (c_pos cx) (c_text cx) (w res)))) ->
     st_ok tfibsegs (Ereg regs' (crt_extra (crt_with cx (c_pos cx) (c_text cx) (w res)))) (crt_ss_ret r cs1 crt_csF)
       (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))) ->
     aregs_preserved regsT regs' -> YK11.getr regs' 10%bv = w64 res -> 4096 <= res ->
     ablocks B ly' S' = ablocks B ly3 S3 ++ [(res, n)] ->
     ajournal tfibsegs B ASTACK (crt_sp1 cx) [] ly3 S3 W3 (unpoison U3 memT) md [] ly' S' W' (unpoison U3 mem') md' 1 ->
     acall_kept tfibsegs B ly3 S3 W3 (unpoison U3 memT) W' (unpoison U3 mem') (crt_sp1 cx - ASTACK) (crt_sp1 cx)
       (fun a => res <= a < res + req_size n) ->
     SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs)) md') Q) ->
  SRr tfibsegs W3 (mkCfg (mkst regsT (Z_to_bv 64 PC_malloc) memT (seg_rom tfibsegs)) md) Q.
Proof.
intros w nb cx E k ly3 S3 U3 W3 regsT memT md n r cs1 Q HB Hnb HEa HJ HARU Hfrs Hnin Hflag R1 Hr Hr2 R2 R3 R4 R8 R9 R26
  R10 Hn Hlive Hev Hw8 Hw16 HSV HCS1 Hat1 Hin1 K.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof crt_STK_eq as FS; unfold crt_STK in FS.
destruct (crtA_spf cx HB) as (Hal16 & Hceil0 & H47 & HS0 & Hsp1 & Hm32 & Hm16).
destruct crtA_astack as (HA0 & HA1).
assert (Hra : YK0s.ret_ok (YK11.getr regsT 1%bv)) by (rewrite R1; apply ret_ok_even; rewrite (wz r) by lia; exact Hr2).
assert (Esp : spZ regsT = crt_sp1 cx) by (unfold spZ; rewrite R2; apply wz; lia).
destruct (crt_callee_pre SK B cx k ly3 S3 U3 W3 (mkst regsT (Z_to_bv 64 PC_malloc) memT (seg_rom tfibsegs)) md ASTACK
  HB HJ HARU (conj Hfrs (conj Hnin Hflag)) Hw8 Hw16
  ltac:(cbn [ms_regs mkst]; exact Esp)
  ltac:(cbn [ms_regs mkst]; unfold s0Z; rewrite R8; apply wz; unfold spZ; apply u64_range)
  ltac:(cbn [ms_regs mkst]; exact Hra)
  ltac:(cbn [ms_regs mkst]; unfold raZ; rewrite R1, wz by lia; lia)
  ltac:(cbn [ms_regs mkst]; exact R3) ltac:(cbn [ms_regs mkst]; exact R4)
  ltac:(lia) ltac:(lia)) as (HPREc & _ & _ & _).
cbn [ms_regs ms_mem mkst] in HPREc.
pose proof HPREc as (((HAR & Hret & Hra' & Hgp & Htp & Hstk & Hpres & Hach & Hqt) & OK & PO) & _).
pose proof Hstk as (H16 & H0 & Hceil & Hlo & Hhi & H47' & Hbot & Htop & Htop2).
assert (Hch : chain_pre ly3 (aview tfibsegs (w_H W3) (unpoison U3 memT)) regsT
  ((spZ (c_regs cx), raZ (c_regs cx), s0Z (c_regs cx)) :: c_ch cx)).
{ apply (achain_chain_pre ly3 _ (spZ regsT) (s0Z regsT) _ regsT Hach);
    [lia | reflexivity | unfold raZ; rewrite R1, wz by lia; lia]. }
pose proof (ajournal_init tfibsegs B ASTACK FS_PSTAT_FP ly3 S3 W3 regsT (unpoison U3 memT) md
  ((spZ (c_regs cx), raZ (c_regs cx), s0Z (c_regs cx)) :: c_ch cx) (proj1 (proj1 HPREc))) as HJid.
rewrite <- (proj1 (crt_fr_malloc B RT)).
eapply SRr_bind.
{ exact (@FSW_malloc_free.fsw_aj_malloc04U_sub fx rc SK B HENV (crtA_ML _ _ _ _ _ HAR) (proj2 (crt_fr_malloc B RT))
    W3 regsT memT ASTACK (spZ regsT) FS_PSTAT_FP ly3 S3 W3 memT md [] ly3 S3 U3 md 0 n 0 (Z_to_bv 64 r) _
    HJid HARU R10 Hn Hlive ltac:(lia) eq_refl ltac:(lia) ltac:(lia)
    ltac:(rewrite R3; exact (proj1 (crt_gptp B cx HB))) ltac:(rewrite R4; exact (proj2 (crt_gptp B cx HB)))
    R1 ltac:(apply ret_ok_even; rewrite (wz r) by lia; exact Hr2) Hev Hch). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HARU2 & HJc & HP & Hres & Hfr2 & Hr4 & Hab & HK).
rewrite Z.add_0_r, Esp in HJc, HK.
pose proof HARU2 as (_ & OK2 & PO2).
set (cx' := crt_with cx (c_pos cx) (c_text cx) (w res)).
(* the flag chunk at the call *)
assert (HCSF : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (crt_F cx')) crt_csF).
{ pose proof (al_flag _ _ LAWS _ _ _ _ _ 3 (c_pos cx) HAR ltac:(rewrite Hfrs; left; reflexivity)) as (_ & _ & Hflapp & _).
  pose proof HJ as (_ & HlyC & _).
  rewrite (crt_FL_ly cx _ ly3 HlyC) in Hflapp.
  unfold crt_csF. rewrite crt_frame3. constructor; [|constructor].
  apply (chunk_ok_val tfibsegs E _ (crt_F cx') (512 - 8) 8 (SOff 46 0) (crt_FL cx));
    [rewrite fsw_SOff0, (HEa res 46%nat ltac:(lia)); reflexivity
    | unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Hflapp; change (8 * Z.of_N 8) with 64; lia
    | cbn; lia |].
  change (crt_F cx') with (crt_F cx).
  replace (crt_F cx + (512 - 8)) with (crt_F cx + fs_frame_bytes 3 - 8) by (rewrite crt_frame3; lia).
  exact (val_mem_of_rdword tfibsegs (w_H W3) memT _ _ Hflag). }
destruct (crtA_after_call cx' E k ly3 S3 U3 W3 (mkst regsT (Z_to_bv 64 PC_malloc) memT (seg_rom tfibsegs)) md ASTACK []
  ly2 S2 U3 W2 regs2 mem2 md2 1 r cs1 crt_csF nb ltac:(lia) (HEa res) HJ HARU
  (conj Hfrs (conj Hnin Hflag)) R2 R3 R4 R8 R9 R26 HSV HCS1 Hat1 Hin1 HCSF
  ltac:(unfold crt_csF; rewrite crt_frame3; apply Forall_cons; [cbn; lia | apply Forall_nil])
  ltac:(unfold crtA_atomlt, crt_csF; apply Forall_cons; [do 4 eexists; split; [reflexivity | lia] | apply Forall_nil])
  ltac:(intros c _ i _ (rg & [] & _)) ltac:(intros i _ (rg & [] & _))
  HJc OK2 PO2 ltac:(intros a (rg & [] & _)) HP ltac:(lia) ltac:(lia))
  as (HJ' & HARU' & HFO' & HE' & HS').
exact (K res ly2 S2 W2 regs2 mem2 md2 HJ' HARU' HFO' HE' HS' HP Hres Hr4 Hab HJc HK).
Qed.

(* the kept bytes across a run (every byte below alloc_ceiling survives it) and across an interceptor malloc (the
   callee journal's block clause for the text's block, acall_kept's image clause for the statics) *)
Lemma crtA_txt_blk : forall cx blks ly3 S3 U3 (W3 : world tfibsegs) ms3,
  crtA_core cx blks ly3 S3 U3 W3 ms3 ->
  In (c_text cx - HEAD, FSH_Fn_writer.enc_size (crtA_blen cx) + HEAD) (ablocks B ly3 S3).
Proof.
intros cx blks ly3 S3 U3 W3 ms3 (_ & Hab & _). rewrite Hab. apply in_or_app. right. left. reflexivity.
Qed.
Lemma crtA_txt_req : forall cx a, crtA_txt cx a ->
  c_text cx - HEAD <= a < c_text cx - HEAD + req_size (FSH_Fn_writer.enc_size (crtA_blen cx) + HEAD).
Proof.
intros cx a Ha. unfold crtA_txt in Ha. assert (Hl : 0 <= crtA_blen cx) by (unfold crtA_blen; lia).
unfold req_size, FSH_Fn_writer.enc_size, HEAD in *. pose proof (Z.div_pos (crtA_blen cx + 2) 3 ltac:(lia) ltac:(lia)).
destruct (_ =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | lia].
Qed.
Lemma crtA_mk_run : forall cx blks ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 m',
  crtA_core cx blks ly3 S3 U3 W3 ms3 -> ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  same_below (ms_mem ms3) m' alloc_ceiling -> crtA_mk W3 W3 (ms_mem ms3) m' (crtA_kept cx).
Proof.
intros cx blks ly3 S3 U3 W3 ms3 md3 m' Hc HARU HSB. apply crtA_mk_raw. intros a [Ht | Hs]; apply HSB.
- pose proof (crtA_txt_blk _ _ _ _ _ _ _ Hc) as Hin.
  destruct (al_blocks _ _ (AR_laws_ok tfibsegs B) _ _ _ _ _ _ _ (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) Hin)
    as (_ & H4096 & Hceil & _).
  pose proof (crtA_txt_req cx a Ht). lia.
- pose proof (fs_segs_img a (crt_pstat_img a Hs)) as Hi. pose proof asan_consts as (C1 & _). unfold FS_IMG_END in Hi. lia.
Qed.
Lemma crtA_mk_malloc : forall cx blks ly3 S3 U3 (W3 : world tfibsegs) ms3 memC mdC ly' S' (W' : world tfibsegs) mem' md'
  res n sp lo hi,
  crtA_core cx blks ly3 S3 U3 W3 ms3 ->
  ARU tfibsegs B ly3 S3 U3 W3 memC mdC -> ARU tfibsegs B ly' S' U3 W' mem' md' ->
  ajournal tfibsegs B ASTACK sp [] ly3 S3 W3 (unpoison U3 memC) mdC [] ly' S' W' (unpoison U3 mem') md' 1 ->
  ablocks B ly' S' = ablocks B ly3 S3 ++ [(res, n)] ->
  acall_kept tfibsegs B ly3 S3 W3 (unpoison U3 memC) W' (unpoison U3 mem') lo hi (fun a => res <= a < res + req_size n) ->
  crtA_mk W3 W' memC mem' (crtA_kept cx).
Proof.
intros cx blks ly3 S3 U3 W3 ms3 memC mdC ly' S' W' mem' md' res n sp lo hi Hc HARU HARU' HJc Hab HK.
apply crtA_mk_av. intros a [Ht | Hs].
- pose proof (crtA_txt_blk _ _ _ _ _ _ _ Hc) as Hin. pose proof (crtA_txt_req cx a Ht) as Hr.
  replace a with ((c_text cx - HEAD) + (a - (c_text cx - HEAD))) by lia.
  apply (crt_keep_blk SK B ly3 S3 U3 W3 memC mdC ly' S' U3 W' mem' md' ASTACK sp [] 1 _ _ _ HARU HARU' HJc Hin);
    [rewrite Hab; apply in_or_app; left; exact Hin | lia | intros (rg & [] & _)].
- pose proof (crt_pstat_img a Hs) as Hi. destruct (proj1 IMG a Hs) as (Hno & Her).
  pose proof HK as (_ & _ & K3 & _).
  pose proof (fs_segs_img a Hi) as Hl. pose proof asan_consts as (C1 & _).
  apply (crt_raw_of_unp B ly3 S3 U3 W3 memC mdC ly' S' U3 W' mem' md' a HARU HARU');
    [unfold FS_IMG_END in Hl; lia | left; unfold FS_IMG_END, SHADOW_OFF in *; lia | exact (K3 a Hi Hno Her)].
Qed.
(* the record with a new want agrees with the old on the first seventeen extra atoms *)
Lemma crtA_extra_with : forall cx w j, (j < 17)%nat ->
  nth j (crt_extra cx) (Z_to_bv 64 0) = nth j (crt_extra (crt_with cx (c_pos cx) (c_text cx) w)) (Z_to_bv 64 0).
Proof. intros cx w j Hj. do 17 (destruct j as [|j]; [reflexivity|]). lia. Qed.
(* blocks_bytes of a boundary, from its ablocks *)
Lemma crtA_bb : forall ly S ly' S' l,
  ablocks B ly' S' = ablocks B ly S ++ l -> blocks_bytes S' = blocks_bytes S + bsum l.
Proof.
intros ly S ly' S' l E. rewrite (blocks_bytes_bsum B ly' S'), (blocks_bytes_bsum B ly S), E, bsum_app. reflexivity.
Qed.

(* ================= segment 2: B 0x81d80 -> malloc (want) -> 0x81da4 (A 0x81c84 -> 0x81ca8) =================
   B 0x81d80 `sd a0, 0x18(s1)` (the text's slot; A 0x30), 0x81d84 / 0x81d88 the constant 0xaaaaaaaaaaaaaaab
   (crtA_kcell), 0x81d8c .. 0x81d98 s11 := (|bs| + 2) / 3 * 4 (crtA_En_U; A: s6), 0x81d9c a0 := s11 + 1, 0x81da0
   `jal __wrap_malloc` (PC_malloc 0x530e4). The walk picks c_want := malloc's result. Ported from d25a984c903
   check_round_trip_sd1.v (St1 -> St0's malloc step).
   crtA_cs1b: B's s1 slots from 0x81d80 on are [0x18 := text (atom 48); 0x50 := F] (A: [0x10 := F; 0x30 := text;
   0x50 := F]; B stores 0x10 := F only at 0x81dd4, in segment 5) - iface.v's text.
   MEASURED by the engine on B: at the malloc call ra = 0x81da4, a0 = crtA_sv6 + 1, s11 = x27 = crtA_sv6, every other
   register its own atom; the regions are [crtA_kcell; s0 (atom 8); s1 slots (atom 9) [0x18 := a0; 0x50 := F]]. *)
Definition crtA_cs1b : list YP09.chunk :=
  [YP09.mkChunk 0x18 (CVal 8 (SOff 48 0)); YP09.mkChunk 0x50 (CVal 8 (SOff 47 0))].
Definition crtA_ssC2 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL PC_malloc (crtA_ssR 0x81d80 crtA_cs1a [crtA_kcell])).

Lemma crtA_seg2 : crt_from SK B (crt_ss_ret 0x81da4 crtA_cs1b crt_csF) crtA_INV_81ca8 ->
  crt_from SK B (crt_ss_ret 0x81d80 crtA_cs1a crt_csF) crtA_INV_81c84.
Proof.
intros NEXT cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFO HINV HS.
destruct HINV as (Hcore & -> & Ha0).
pose proof Hcore as (Hg & Hab & HU & Hh & H4 & Hrb & Hz & R18 & R20 & R21 & R22 & R19 & R25).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
pose proof HB as ((HPRE & HRO) & Hheads & Htop & Hfrl & Hr10 & Hr11 & Hr12 & Htext & Hnonul & Htblen & Htwin & Htblk
  & Hdec & Hbd0 & Hbody & Hrb0 & Hstat & Hquiet & Hlive0 & Hcells & Hsp47 & Hnev0 & Hbb0 & HTU0).
destruct (crtA_len (c_tb cx) (c_bs cx) Hdec Htblen) as (Hok & Hlen & Henc).
destruct (crtA_spf cx HB) as (Hal16 & Hceil0 & H47 & HS0 & Hsp1 & Hm32 & Hm16).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (B20 : YK11.getr (ms_regs ms3) 20%bv = ew E 20) by exact (crt_reg_atom E _ ms3 _ 20%bv 20 HS eq_refl).
assert (E20 : bv_unsigned (ew E 20) = crtA_blen cx) by (rewrite <- B20, R20; apply wz; unfold crtA_blen in *; lia).
assert (E10 : ew E 10 = w64 (c_text cx)) by (rewrite <- (crt_reg_atom E _ ms3 _ 10%bv 10 HS eq_refl); exact Ha0).
(* the run state: the s0 words, the s1 slots and the constant cell *)
pose proof (st_ok_submem tfibsegs E _ _ _ HS (crtA_sub2 0x81d80 crtA_cs1a crt_csF) ltac:(vm_compute; reflexivity)) as HS2.
change (st_ok tfibsegs E (crtA_ssR 0x81d80 crtA_cs1a []) (restrict (w_H W3) ms3)) in HS2.
assert (DK : all_disjoint E crtA_kcell (ss_mem (crtA_ssR 0x81d80 crtA_cs1a []))).
{ apply all_disjoint_of_extents. unfold crtA_ssR, crtA_kcell, crt_s0_region, fs_ret_s0_region, crt_slot_region,
    extent_of_region.
  cbn [ss_mem app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E8, E9.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
pose proof (st_ok_add_region' tfibsegs E _ _ crtA_kcell HS2 ltac:(vm_compute; reflexivity)
  ltac:(cbn [restrict ms_mem]; exact (crtA_kcell_ok E W3 (ms_mem ms3)
    (crt_rom SK B IMG cx _ ly3 S3 U3 W3 (ms_mem ms3) md3 HB HJ HARU))) DK) as HSR.
change (st_ok tfibsegs E (crtA_ssR 0x81d80 crtA_cs1a [crtA_kcell]) (restrict (w_H W3) ms3)) in HSR.
assert (Hrun : sym_run_toN tfibsegs crt_tbl FUEL PC_malloc (crtA_ssR 0x81d80 crtA_cs1a [crtA_kcell]) =
  (crtA_ssC2, RS_running)) by (vm_compute; reflexivity).
apply (crtA_run_slots 0x81d80 PC_malloc crtA_cs1a [crtA_kcell] crtA_ssC2 cx E _ ly3 S3 U3 W3 ms3 md3 _ Hrun
  ltac:(repeat constructor; cbn; lia) HB HE HJ HARU HSR).
intros ms mat HSC HJC HARUC HSB.
set (mdC := with_vm_backing (m_vm_lazy md3) mat md3) in *.
(* the call site *)
assert (G : forall (q : bv 5) n, sr_get (ss_regs crtA_ssC2) q = SOff n 0 -> YK11.getr (ms_regs ms) q = ew E n)
  by (intros q n Hq; exact (crt_reg_atom E (w_H W3) ms crtA_ssC2 q n HSC Hq)).
assert (Q1 : YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 0x81da4)
  by exact (fsw_reg_lit (w_H W3) E crtA_ssC2 ms 1%bv 0x81da4 HSC ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (Q2 : YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 (crt_sp1 cx))
  by (rewrite (G 2%bv 2%nat ltac:(vm_compute; reflexivity)); apply crtA_reg_eq; [exact E2 | rewrite <- E2; apply u64_range]).
assert (Q3 : YK11.getr (ms_regs ms) 3%bv = YK11.getr (c_regs cx) 3%bv)
  by (rewrite (G 3%bv 3%nat ltac:(vm_compute; reflexivity)); exact E3).
assert (Q4 : YK11.getr (ms_regs ms) 4%bv = YK11.getr (c_regs cx) 4%bv)
  by (rewrite (G 4%bv 4%nat ltac:(vm_compute; reflexivity)); exact E4).
assert (Q8 : YK11.getr (ms_regs ms) 8%bv = Z_to_bv 64 (spZ (c_regs cx)))
  by (rewrite (G 8%bv 8%nat ltac:(vm_compute; reflexivity)); apply crtA_reg_eq; [exact E8 | rewrite <- E8; apply u64_range]).
assert (Q9 : YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 (crt_sp1 cx))
  by (rewrite (G 9%bv 9%nat ltac:(vm_compute; reflexivity)); apply crtA_reg_eq; [exact E9 | rewrite <- E9; apply u64_range]).
(* B: SF is s10 = x26 (A: s3 = x19) *)
assert (Q26 : YK11.getr (ms_regs ms) 26%bv = Z_to_bv 64 (crt_SF cx))
  by (rewrite (G 26%bv 26%nat ltac:(vm_compute; reflexivity)); apply crtA_reg_eq; [exact E26 | rewrite <- E26; apply u64_range]).
destruct (crtA_En_denot E (crtA_blen cx) E20 ltac:(unfold crtA_blen in *; lia)) as (D6 & D10).
assert (Q10 : YK11.getr (ms_regs ms) 10%bv = w64 (crtA_En cx + 1)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtA_ssC2 ms 10%bv HSC).
  replace (sr_get (ss_regs crtA_ssC2) 10%bv) with (SAlu ALU_ADD crtA_sv6 (SLit 1)) by (vm_compute; reflexivity).
  exact D10. }
(* B: En is s11 = x27 (0x81d98 `andi s11, a0, -4`; A: s6 = x22) *)
assert (Q27 : YK11.getr (ms_regs ms) 27%bv = w64 (crtA_En cx)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtA_ssC2 ms 27%bv HSC).
  replace (sr_get (ss_regs crtA_ssC2) 27%bv) with crtA_sv6 by (vm_compute; reflexivity). exact D6. }
(* the frame at the call: the run kept every byte below alloc_ceiling *)
destruct HFO as (Hfrs & Hnin & Hflag).
destruct (crt_F_facts SK B cx _ _ _ _ _ _ _ HJ HARU Hfrs) as (_ & HF4096 & HFceil & _).
assert (Hflag' : rdword (aview tfibsegs (w_H W3) (ms_mem ms)) (crt_F cx + fs_frame_bytes 3 - 8) = Some (crt_FL cx)).
{ rewrite <- Hflag. apply rdword_ext. intros i Hi. rewrite crt_frame3 in *.
  exact (aview_below (w_H W3) (ms_mem ms3) (ms_mem ms) alloc_ceiling (crt_F cx + 512 - 8 + i) HSB ltac:(lia)). }
destruct (crt_saved_words cx E crtA_ssC2 ms W3 1 HE HSC ltac:(vm_compute; reflexivity)) as (Hw8 & Hw16).
assert (HSV : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (spZ (c_regs cx))) crt_sv_chunks)
  by exact (crtA_region_chunks E crtA_ssC2 (w_H W3) ms 1 crt_s0_region 8 _ HSC ltac:(vm_compute; reflexivity)
    eq_refl E8).
(* B: the slot region after `sd a0, 0x18(s1)` is [0x18 := a0 (atom 10); 0x50 := F] (A: [0x30 := a0; 0x10; 0x50]) *)
assert (HSL : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (crt_sp1 cx))
  [YP09.mkChunk 24 (CVal 8 (SOff 10 0)); YP09.mkChunk 80 (CVal 8 (SOff 47 0))]).
{ pose proof (crtA_region_chunks E crtA_ssC2 (w_H W3) ms 2 (crt_slot_region
    [YP09.mkChunk 24 (CVal 8 (SOff 10 0)); YP09.mkChunk 80 (CVal 8 (SOff 47 0))])
    9 _ HSC ltac:(vm_compute; reflexivity) eq_refl E9) as Hc. exact Hc. }
assert (V48 : sv_denot E (SOff 48 0) = sv_denot E (SOff 10 0))
  by (rewrite !fsw_SOff0, (crt_E_text cx E HE), E10; reflexivity).
assert (HCS1 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (crt_sp1 cx)) crtA_cs1b).
{ inversion HSL as [|? ? H24 HSL']; subst. inversion HSL' as [|? ? H80 _]; subst.
  constructor; [exact (crtA_chunk_swap _ _ _ _ _ _ _ V48 H24)|].
  constructor; [exact H80 | constructor]. }
(* the malloc *)
pose proof (crt_mkst (w_H W3) E crtA_ssC2 ms HSC ltac:(vm_compute; reflexivity)) as Ems.
replace (ss_pc crtA_ssC2) with PC_malloc in Ems by (vm_compute; reflexivity).
rewrite Ems.
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
assert (HL : 0 <= crtA_blen cx <= 2359298) by (unfold crtA_blen in *; lia).
assert (HEn : 0 <= crtA_En cx /\ crtA_En cx + 1 = FSH_Fn_writer.enc_size (crtA_blen cx))
  by (unfold crtA_En, FSH_Fn_writer.enc_size; split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]|]; lia).
assert (HEnb : FSH_Fn_writer.enc_size (crtA_blen cx) <= 3145734)
  by (unfold FSH_Fn_writer.enc_size; clear - HL; Z.div_mod_to_equations; lia).
apply (crtA_malloc_call (fun res => res) 49 cx E _ ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) mdC (crtA_En cx + 1) 0x81da4
  crtA_cs1b _ HB ltac:(lia)
  ltac:(intros res n' Hn'; replace n' with (32 + (n' - 32))%nat at 1 by lia;
        rewrite (crt_E_extra cx E (n' - 32) HE ltac:(unfold crt_nextra; lia)); apply crtA_extra_with; lia)
  HJC HARUC Hfrs Hnin Hflag' Q1 ltac:(lia) eq_refl Q2 Q3 Q4 Q8 Q9 Q26 Q10
  ltac:(unfold MALLOC_MAX; lia)
  ltac:(rewrite (crtA_bb _ _ _ _ _ Hab); cbn [bsum fold_right fst snd];
        unfold LIVE_check_round_trip, LIVE_MAX, HEAD in *; lia)
  ltac:(unfold EV_preset_base64_encode, EV_check_round_trip in *; lia)
  Hw8 Hw16 HSV HCS1
  ltac:(unfold crtA_atomlt, crtA_cs1b; repeat (apply Forall_cons; [do 4 eexists; split; [reflexivity | lia]|]);
        apply Forall_nil)
  ltac:(unfold crtA_cs1b; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil)).
intros res ly' S' W' regs' mem' md' HJ' HARU' HFO' HE' HS' HP' Hres Hr4 Hab' HJc HK.
apply (NEXT (crt_with cx (c_pos cx) (c_text cx) res) (Ereg regs' (crt_extra (crt_with cx (c_pos cx) (c_text cx) res)))
  (EV_preset_base64_encode + 1) ly' S' U3 W' (mkst regs' (Z_to_bv 64 0x81da4) mem' (seg_rom tfibsegs)) md'
  HB HE' HJ' HARU' HFO'); [|exact HS'].
assert (KP : forall r : bv 5, acallee_saved (bv_unsigned r) -> YK11.getr regs' r = YK11.getr (ms_regs ms) r)
  by (intros r Hr; exact (fsw_pres _ _ r HP' Hr)).
split; [|split; [reflexivity | split; [exact Hres | cbn [ms_regs mkst]; rewrite (KP 27%bv ltac:(crtA_cs)); exact Q27]]].
change (crtA_core cx ([] ++ [(res, crtA_En cx + 1)]) ly' S' U3 W' (mkst regs' (Z_to_bv 64 0x81da4) mem' (seg_rom tfibsegs))).
apply (crtA_core_move cx [] [(res, crtA_En cx + 1)] ly3 S3 U3 W3 ms3 ly' S' W' _ Hcore Hab').
- apply (crtA_mk_trans W3 W3 W' (ms_mem ms3) (ms_mem ms) mem').
  + exact (crtA_mk_run cx [] ly3 S3 U3 W3 ms3 md3 (ms_mem ms) Hcore HARU HSB).
  + exact (crtA_mk_malloc cx [] ly3 S3 U3 W3 ms3 (ms_mem ms) mdC ly' S' W' mem' md' res _ _ _ _ Hcore HARUC HARU' HJc
      Hab' HK).
- intros r Hr. cbn [ms_regs mkst]. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
  [ rewrite (KP 18%bv ltac:(crtA_cs)), (G 18%bv 18%nat ltac:(vm_compute; reflexivity)); symmetry;
    exact (crt_reg_atom E _ ms3 _ 18%bv 18 HS eq_refl)
  | rewrite (KP 20%bv ltac:(crtA_cs)), (G 20%bv 20%nat ltac:(vm_compute; reflexivity)); symmetry;
    exact (crt_reg_atom E _ ms3 _ 20%bv 20 HS eq_refl)
  | rewrite (KP 21%bv ltac:(crtA_cs)), (G 21%bv 21%nat ltac:(vm_compute; reflexivity)); symmetry;
    exact (crt_reg_atom E _ ms3 _ 21%bv 21 HS eq_refl)
  | rewrite (KP 22%bv ltac:(crtA_cs)), (G 22%bv 22%nat ltac:(vm_compute; reflexivity)); symmetry;
    exact (crt_reg_atom E _ ms3 _ 22%bv 22 HS eq_refl)
  | rewrite (KP 19%bv ltac:(crtA_cs)), (G 19%bv 19%nat ltac:(vm_compute; reflexivity)); symmetry;
    exact (crt_reg_atom E _ ms3 _ 19%bv 19 HS eq_refl)
  | rewrite (KP 25%bv ltac:(crtA_cs)), (G 25%bv 25%nat ltac:(vm_compute; reflexivity)); symmetry;
    exact (crt_reg_atom E _ ms3 _ 25%bv 25 HS eq_refl) ].
Qed.

(* ================= segment 3: B 0x81da4 -> strlen (input) -> 0x81db0 (A 0x81ca8 -> 0x81cb4) =================
   B 0x81da4 `mv s7, a0` (want; A: s10), 0x81da8 `mv a0, s9` (t), 0x81dac `jal __wrap_strlen` (PC_strlen 0x426c4; a
   runtime call: FSH_crt_site's crt_rt_call, whose post keeps every byte outside the callee's stack window). t is cstr_ok
   at the call from the entry's block and bytes (the journal's block clause) and from crt_base's last conjunct, which
   keeps the input clear of every user-poisoned head of the entry's U; the text's head is a different live block's. The
   return is re-seated by crtA_reseat (a Theorem Labs lane's a23_reseat, a working branch d1bbf1448b5 FSH_crt_segA23.v:130-251,
   renamed; B text: lib/B/FSH_crt_segB0.v crtB0_reseat - SF register x26, B's crt_E, env agreement 32 <= n < 51). *)
Lemma crtA_reseat : forall cx E k ly' S' U' (W' : world tfibsegs) regs' mem' md' r cs1 csF,
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
destruct (frames_bounds tfibsegs B (AR_laws_ok tfibsegs B) ly' S' W' (unpoison U' mem') md' 3 (c_pos cx) HAR' Hin3')
  as (HF0 & HFc & HFapp).
rewrite Efr' in HF0, HFc, HFapp. rewrite crt_frame3 in HFc, HFapp.
assert (HFrng : 0 <= crt_F cx < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds (crt_F cx) HFrng) as (HS1b & HS2b).
destruct (al_frames _ _ (AR_laws_ok tfibsegs B) ly' S' W' (unpoison U' mem') md' 3 (c_pos cx) HAR' Hin3')
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
(* B: crt_E has nineteen extra atoms 32 .. 50 (A: eighteen, < 50) *)
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
  apply (FSW_frame.fsw_apresent_notowned B ly' S' U' W' mem' md' _ HARU'); [lia | exact Hno | exact Hp]. }
assert (ROframe : region_ok tfibsegs E' (mrestrict (w_H W') mem') (crt_frame_region csF)).
{ unfold region_ok, crt_frame_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E47v.
  split; [lia|]. split; [rewrite crt_frame3; lia|]. split.
  - intros o Ho. rewrite crt_frame3 in Ho.
    apply (apresent_writable tfibsegs). destruct (Hfp' (crt_F cx + o) ltac:(lia)) as (Hp & Hno).
    apply (FSW_frame.fsw_apresent_notowned B ly' S' U' W' mem' md' _ HARU'); [lia | exact Hno | exact Hp].
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

(* a block's bytes clear of every range of U are addressable on the machine's memory (FSW_rd.fsw_block_body_addressable
   with the head clause replaced by U-disjointness) *)
Lemma crtA_body_addressable_U : forall ly S U (W : world tfibsegs) mem md P n z len,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  In (P, n) (ablocks B ly S) -> P <= z -> 0 <= len -> z + len <= P + req_size n ->
  (forall r, In r U -> z + len <= fst r \/ fst r + snd r <= z) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF z len.
Proof.
intros ly S U W mem md P n z len HARU FH Hin Hz Hl Hn HUo.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof (YCbq.range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem) md P n z len HAR Hin ltac:(lia) Hn)
  as HRA.
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md P n HAR Hin) as (HP16 & HP4096 & HPc & _).
pose proof asan_consts as (C1 & _).
intros x Hx. destruct (HRA x Hx) as (s & Es & Hok). exists s. split; [|exact Hok].
assert (NI : in_ush U (bv_unsigned (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x))) = false).
{ rewrite wz by (unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
  apply FSW_rd.fsw_head_ush_out; [lia|]. intros (h & q) Hr. cbn [fst snd].
  destruct (FH (h, q) Hr) as (E16 & m & Hm & M16). cbn [fst snd] in E16, Hm. subst q.
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md h m HAR Hm) as (Hh16 & _).
  split; [reflexivity|].
  split; [apply Z.mod_divide in Hh16 as [k Hk]; [|lia]; rewrite Hk; replace (k * 16) with ((k * 2) * 8) by lia;
          apply Z_mod_mult|].
  destruct (HUo (h, 16) Hr) as [D|D]; cbn [fst snd] in D; lia. }
rewrite <- (aview_unpoison_out tfibsegs (w_H W) U mem _ NI). exact Es.
Qed.
(* a string inside a live block and clear of every range of U is cstr_ok (FSH_crt_cstr.crt_cstr_of_block with the
   head clause replaced by U-disjointness) *)
Lemma crtA_cstr_of_block_U : forall ly S U (W : world tfibsegs) mem md p (l : list Z) b m,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  In (b, m) (ablocks B ly S) -> b <= p -> p + Z.of_nat (length l) + 1 <= b + m ->
  (forall r, In r U -> p + Z.of_nat (length l) + 1 <= fst r \/ fst r + snd r <= p) ->
  zbytes_at tfibsegs W mem p (l ++ [0]) -> ~ In 0 l ->
  cstr_ok tfibsegs W mem p l.
Proof.
intros ly S U W mem md p l b m HARU FH Hin Hb Hbm HUo Hz Hnz.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof HARU as (_ & _ & PO).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md b m HAR Hin) as (_ & H4096 & Hc & Happ & _ & _ & Hmax).
unfold MALLOC_MAX in Hmax.
assert (Hm : 0 < m) by lia.
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
rewrite Hrq in Hc, Happ.
pose proof (proj1 (@YM05.alloc_ceiling_value rc)) as HCV.
split; [split; [exact Hz|]|].
{ apply Forall_forall. intros c Hc0 E. subst c. exact (Hnz Hc0). }
split; [lia|]. split; [lia|]. split; [lia|].
split.
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd.
  destruct Happ as (_ & [Hlo | (Hh1 & Hh2)]); [left | right]; lia. }
split.
{ apply (crtA_body_addressable_U ly S U W mem md b m p (Z.of_nat (length l) + 1) HARU FH Hin); [lia | lia | lia |].
  intros r Hr. destruct (HUo r Hr) as [D|D]; [left | right]; lia. }
split.
{ destruct (al_shadow _ _ LAWS ly S W (unpoison U mem) md b m HAR Hin) as (_ & Hhv). rewrite Hrq in Hhv.
  intros s Hs. eapply FSW_strkit.aview_unpoison_vis; [exact PO|].
  exact (FSW_strkit.shadow_hull_vis_sub _ b m p (Z.of_nat (length l) + 1) Hhv ltac:(lia) ltac:(lia) ltac:(lia) s Hs). }
intros a Ha. eapply FSW_strkit.aview_unpoison_vis; [exact PO|].
apply (FSW_strkit.block_word_tail_vis B ly S W (unpoison U mem) md b m HAR Hin Hm).
pose proof (FSW_strkit.word_end_mono (p + Z.of_nat (length l)) (b + m - 1) ltac:(lia)). lia.
Qed.
Lemma crtA_zs_app0 : forall tb, HState.zs (tb ++ [Z_to_bv 8 0]) = HState.zs tb ++ [0].
Proof. intros tb. unfold HState.zs. rewrite map_app. reflexivity. Qed.
Lemma crtA_zs_nonul : forall tb, ~ In (Z_to_bv 8 0) tb -> ~ In 0 (HState.zs tb).
Proof.
intros tb Hn Hin. unfold HState.zs in Hin. apply in_map_iff in Hin as (b & Hb & Hin).
assert (Eb : b = Z_to_bv 8 0) by (apply bv_eq; rewrite Hb; reflexivity). subst b. exact (Hn Hin).
Qed.
(* the stack window a runtime call writes lies above every byte the boundaries keep (no STK_* numeral: the two
   bounds are checked by computation) *)
Lemma crtA_rt_low : forall cx, crt_base B cx -> 0 <= STK_RT_STR /\ alloc_ceiling + STK_RT_STR <= crt_sp1 cx.
Proof.
intros cx HB. destruct (crtA_spf cx HB) as (_ & Hc & _ & _ & Hs & _).
assert (H1 : (0 <=? STK_RT_STR) && (STK_RT_STR + 208 <=? STK_check_round_trip) = true) by (vm_compute; reflexivity).
apply andb_prop in H1 as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* MEASURED by the engine on B: at the strlen call ra = 0x81db0, a0 = s9 (atom 25), s7 = x23 = a0 (atom 10, want; A:
   s10 = x26), every other register its own atom; the regions are [s0; s1 slots crtA_cs1b], unchanged *)
Definition crtA_ssC3 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL PC_strlen (crtA_ssR 0x81da4 crtA_cs1b [])).

Lemma crtA_seg3 : crt_from SK B (crt_ss_ret 0x81db0 crtA_cs1b crt_csF) crtA_INV_81cb4 ->
  crt_from SK B (crt_ss_ret 0x81da4 crtA_cs1b crt_csF) crtA_INV_81ca8.
Proof.
intros NEXT cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFO HINV HS.
destruct HINV as (Hcore & -> & Ha0 & Hs27).
pose proof Hcore as (Hg & Hab & HU & Hh & H4 & Hrb & Hz & R18 & R20 & R21 & R22 & R19 & R25).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
pose proof HB as ((HPRE & HRO) & Hheads & Htop & Hfrl & Hr10 & Hr11 & Hr12 & Htext & Hnonul & Htblen & Htwin & Htblk
  & Hdec & Hbd0 & Hbody & Hrb0 & Hstat & Hquiet & Hlive0 & Hcells & Hsp47 & Hnev0 & Hbb0 & HTU0).
destruct (crtA_spf cx HB) as (Hal16 & Hceil0 & H47 & HS0 & Hsp1 & Hm32 & Hm16).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). destruct (crtA_rt_low cx HB) as (Hrt0 & Hlow).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
(* the run to the call: no store *)
pose proof (st_ok_submem tfibsegs E _ _ _ HS (crtA_sub2 0x81da4 crtA_cs1b crt_csF) ltac:(vm_compute; reflexivity)) as HS2.
change (st_ok tfibsegs E (crtA_ssR 0x81da4 crtA_cs1b []) (restrict (w_H W3) ms3)) in HS2.
assert (Hrun : sym_run_toN tfibsegs crt_tbl FUEL PC_strlen (crtA_ssR 0x81da4 crtA_cs1b []) = (crtA_ssC3, RS_running))
  by (vm_compute; reflexivity).
apply (crtA_run_slots 0x81da4 PC_strlen crtA_cs1b [] crtA_ssC3 cx E _ ly3 S3 U3 W3 ms3 md3 _ Hrun (Forall_nil _)
  HB HE HJ HARU HS2).
intros ms mat HSC HJC HARUC HSB.
set (mdC := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (G : forall (q : bv 5) n, sr_get (ss_regs crtA_ssC3) q = SOff n 0 -> YK11.getr (ms_regs ms) q = ew E n)
  by (intros q n Hq; exact (crt_reg_atom E (w_H W3) ms crtA_ssC3 q n HSC Hq)).
assert (GB : forall (q : bv 5) n, Z.of_nat n = bv_unsigned q -> sr_get (ss_regs (crt_ss_ret 0x81da4 crtA_cs1b crt_csF)) q = SOff n 0 ->
  ew E n = YK11.getr (ms_regs ms3) q)
  by (intros q n _ Hq; symmetry; exact (crt_reg_atom E (w_H W3) ms3 _ q n HS Hq)).
(* the input's block and bytes at the call *)
destruct Htblk as (pt & kt & Hpt & Hpt1 & Hpt2).
pose proof (proj1 HJC) as HAR3.
assert (Hpt3 : In (pt, kt) (ablocks B ly3 S3)) by (rewrite Hab; apply in_or_app; left; exact Hpt).
pose proof (crtA_mk_blk (c_ly cx) (c_S cx) (c_U cx) (c_W cx) (c_mem cx) (c_md cx) ly3 S3 U3 W3 (ms_mem ms) mdC _
  STK_check_round_trip (spZ (c_regs cx)) [(3, c_pos cx)] pt kt (fsw_ARU B _ _ _ _ _ _ _ _ _ HPRE) HARUC HJC Hpt Hpt3)
  as KT.
assert (Hkt : kt <= req_size kt) by (unfold req_size; destruct (Z.eqb_spec kt 0); lia).
assert (HzT : zbytes_at tfibsegs W3 (ms_mem ms) (c_t cx) (HState.zs (c_tb cx) ++ [0])).
{ rewrite <- crtA_zs_app0. apply (crtA_mk_zbytes _ _ _ _ _ _ _ KT); [|exact Htext].
  intros i Hi. unfold HState.zs in Hi. rewrite length_map, length_app in Hi. cbn [length] in Hi. lia. }
assert (HUo : forall r, In r U3 -> c_t cx + Z.of_nat (length (HState.zs (c_tb cx))) + 1 <= fst r \/
    fst r + snd r <= c_t cx).
{ unfold HState.zs. rewrite length_map. rewrite HU. intros r Hr. apply in_app_or in Hr as [Hr | [<- | []]].
  - rewrite Forall_forall in HTU0. exact (HTU0 r Hr).
  - destruct (in_split _ _ Hpt) as (l1 & l2 & El).
    assert (EA : ablocks B ly3 S3 = l1 ++ (pt, kt) :: (l2 ++ (c_text cx - HEAD,
        FSH_Fn_writer.enc_size (crtA_blen cx) + HEAD) :: [(c_want cx, crtA_En cx + 1)])).
    { rewrite Hab, El, <- app_assoc. reflexivity. }
    pose proof (sep_blocks_pos tfibsegs B LAWS ly3 S3 W3 _ _ _ _ l1 l2 _ HAR3 EA) as D.
    unfold zdisjoint, block_rng in D. cbn [fst snd] in D |- *.
    assert (Hrt : FSH_Fn_writer.enc_size (crtA_blen cx) + HEAD <= req_size (FSH_Fn_writer.enc_size (crtA_blen cx) + HEAD))
      by (unfold req_size; destruct (Z.eqb_spec (FSH_Fn_writer.enc_size (crtA_blen cx) + HEAD) 0); lia).
    assert (He1 : 1 <= FSH_Fn_writer.enc_size (crtA_blen cx)).
    { unfold FSH_Fn_writer.enc_size, crtA_blen. pose proof (Zle_0_nat (length (c_bs cx))).
      pose proof (Z.div_pos (Z.of_nat (length (c_bs cx)) + 2) 3 ltac:(lia) ltac:(lia)). lia. }
    unfold HEAD in *. lia. }
assert (HC : cstr_ok tfibsegs W3 (ms_mem ms) (c_t cx) (HState.zs (c_tb cx))).
{ apply (crtA_cstr_of_block_U ly3 S3 U3 W3 (ms_mem ms) mdC (c_t cx) (HState.zs (c_tb cx)) pt kt HARUC
    ltac:(rewrite HU; rewrite HU in Hh; exact Hh) Hpt3 Hpt1 ltac:(unfold HState.zs; rewrite length_map; lia) HUo HzT
    (crtA_zs_nonul _ Hnonul)). }
assert (E25 : bv_unsigned (ew E 25) = c_t cx).
{ rewrite (GB 25%bv 25%nat eq_refl ltac:(vm_compute; reflexivity)), R25. apply wz.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) Hpt3) as (_ & A1 & A2 & _). lia. }
(* the call *)
pose proof (crt_mkst (w_H W3) E crtA_ssC3 ms HSC ltac:(vm_compute; reflexivity)) as Ems.
replace (ss_pc crtA_ssC3) with PC_strlen in Ems by (vm_compute; reflexivity).
rewrite Ems in HSC |- *.
apply (crt_rt_call SK B crtA_ssC3 0x81db0 25 cx E _ ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) mdC (HState.zs (c_tb cx)) _
  RT IMG HB HE ltac:(vm_compute; reflexivity) ltac:(lia)
  ltac:(apply ret_ok_even; rewrite (wz 0x81db0) by lia; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) HSC ltac:(rewrite E25; exact HC) HJC HARUC).
intros regs2 mem2 md2 HJ2 HARU2 HP2 Ha2 Hfr2 Hgr2.
(* the kept bytes: everything below the callee's stack window *)
assert (KR : forall a, 0 <= a < alloc_ceiling ->
  aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) (ms_mem ms) a)
  by (intros a Ha; apply Hfr2; lia).
assert (KS : forall a, crt_sp1 cx <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) (ms_mem ms) a)
  by (intros a Ha; apply Hfr2; lia).
assert (KP : forall r : bv 5, acallee_saved (bv_unsigned r) -> YK11.getr regs2 r = YK11.getr (ms_regs ms) r)
  by (intros r Hr; exact (fsw_pres _ _ r HP2 Hr)).
(* the boundary at B 0x81db0 *)
destruct HFO as (Hfrs & Hnin & Hflag).
destruct (crt_F_facts SK B cx _ _ _ _ _ _ _ HJ HARU Hfrs) as (_ & HF4096 & HFceil & _).
assert (Hflag2 : rdword (aview tfibsegs (w_H W3) mem2) (crt_F cx + fs_frame_bytes 3 - 8) = Some (crt_FL cx)).
{ rewrite <- Hflag. apply rdword_ext. intros i Hi. rewrite crt_frame3 in *.
  rewrite (KR (crt_F cx + 512 - 8 + i) ltac:(lia)).
  exact (aview_below (w_H W3) (ms_mem ms3) (ms_mem ms) alloc_ceiling (crt_F cx + 512 - 8 + i) HSB ltac:(lia)). }
assert (CM : forall c base, (forall i, 0 <= i < YP09.c_len c -> (0 <= base + YP09.c_off c + i < alloc_ceiling \/
    crt_sp1 cx <= base + YP09.c_off c + i < 2 ^ 64)) ->
  YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) base c ->
  YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) mem2) base c).
{ intros c base Hr Hc. apply (chunk_ok_mbyte E (mrestrict (w_H W3) (ms_mem ms))); [|exact Hc].
  intros i Hi. apply mbyte_of_aview. destruct (Hr i Hi) as [Hlo | Hhi]; [exact (KR _ Hlo) | exact (KS _ Hhi)]. }
assert (HSV : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) mem2) (spZ (c_regs cx))) crt_sv_chunks).
{ pose proof (crtA_region_chunks E crtA_ssC3 (w_H W3) _ 0 crt_s0_region 8 _ HSC ltac:(vm_compute; reflexivity)
    eq_refl E8) as Hc. cbn [ms_mem mkst] in Hc.
  pose proof crt_sv_in as Hin1. rewrite Forall_forall in Hc, Hin1 |- *. intros c Hcin.
  apply CM; [| exact (Hc c Hcin)]. intros i Hi. destruct (Hin1 c Hcin) as (Ho1 & Ho2). right. lia. }
assert (HCS1 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) mem2) (crt_sp1 cx)) crtA_cs1b).
{ pose proof (crtA_region_chunks E crtA_ssC3 (w_H W3) _ 1 (crt_slot_region crtA_cs1b) 9 _ HSC
    ltac:(vm_compute; reflexivity) eq_refl E9) as Hc. cbn [ms_mem mkst] in Hc.
  rewrite Forall_forall in Hc |- *. intros c Hcin.
  apply CM; [| exact (Hc c Hcin)]. intros i Hi. right.
  unfold crtA_cs1b in Hcin. cbn [In] in Hcin. destruct Hcin as [<-|[<-|[]]]; cbn in Hi |- *; lia. }
assert (HCSF : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) mem2) (crt_F cx)) crt_csF).
{ pose proof (al_flag _ _ LAWS _ _ _ _ _ 3 (c_pos cx) (proj1 HARU2) ltac:(rewrite Hfrs; left; reflexivity))
    as (_ & _ & Hflapp & _).
  pose proof HJ2 as (_ & HlyC & _).
  rewrite (crt_FL_ly cx _ ly3 HlyC) in Hflapp.
  unfold crt_csF. rewrite crt_frame3. constructor; [|constructor].
  apply (chunk_ok_val tfibsegs E _ (crt_F cx) (512 - 8) 8 (SOff 46 0) (crt_FL cx));
    [rewrite fsw_SOff0, (crt_E_FL cx E HE); reflexivity
    | unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Hflapp; change (8 * Z.of_N 8) with 64; lia
    | cbn; lia |].
  replace (crt_F cx + (512 - 8)) with (crt_F cx + fs_frame_bytes 3 - 8) by (rewrite crt_frame3; lia).
  exact (val_mem_of_rdword tfibsegs (w_H W3) mem2 _ _ Hflag2). }
assert (QR : forall (q : bv 5) n, acallee_saved (bv_unsigned q) -> sr_get (ss_regs crtA_ssC3) q = SOff n 0 ->
  YK11.getr regs2 q = ew E n) by (intros q n Hq Hs; rewrite (KP q Hq); exact (G q n Hs)).
destruct (crtA_reseat cx E (EV_preset_base64_encode + CRT_EV_WRAP) ly3 S3 U3 W3 regs2 mem2 md2 0x81db0 crtA_cs1b crt_csF
  HE Hal16 ltac:(lia) Hceil0 H47 HJ2 HARU2 ltac:(rewrite Hfrs; left; reflexivity)
  ltac:(rewrite (QR 2%bv 2%nat ltac:(crtA_cs) ltac:(vm_compute; reflexivity)); apply crtA_reg_eq; [exact E2 | rewrite <- E2; apply u64_range])
  ltac:(rewrite (QR 3%bv 3%nat ltac:(crtA_cs) ltac:(vm_compute; reflexivity)); exact E3)
  ltac:(rewrite (QR 4%bv 4%nat ltac:(crtA_cs) ltac:(vm_compute; reflexivity)); exact E4)
  ltac:(rewrite (QR 8%bv 8%nat ltac:(crtA_cs) ltac:(vm_compute; reflexivity)); apply crtA_reg_eq; [exact E8 | rewrite <- E8; apply u64_range])
  ltac:(rewrite (QR 9%bv 9%nat ltac:(crtA_cs) ltac:(vm_compute; reflexivity)); apply crtA_reg_eq; [exact E9 | rewrite <- E9; apply u64_range])
  ltac:(rewrite (QR 26%bv 26%nat ltac:(crtA_cs) ltac:(vm_compute; reflexivity)); apply crtA_reg_eq; [exact E26 | rewrite <- E26; apply u64_range])
  HSV HCS1 HCSF
  ltac:(unfold crtA_cs1b; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil)
  ltac:(unfold crt_csF; rewrite crt_frame3; apply Forall_cons; [cbn; lia | apply Forall_nil])
  ltac:(unfold crt_atom_chunks, crtA_cs1b; repeat (apply Forall_cons; [do 4 eexists; split; [reflexivity | lia]|]);
        apply Forall_nil)
  ltac:(unfold crt_atom_chunks, crt_csF; apply Forall_cons; [do 4 eexists; split; [reflexivity | lia] | apply Forall_nil])
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (HE2 & HS2').
apply (NEXT cx (Ereg regs2 (crt_extra cx)) _ ly3 S3 U3 W3 (mkst regs2 (Z_to_bv 64 0x81db0) mem2 (seg_rom tfibsegs)) md2
  HB HE2 HJ2 HARU2 ltac:(split; [exact Hfrs | split; [exact Hnin | exact Hflag2]])); [|exact HS2'].
split; [|split; [reflexivity|]].
- rewrite <- (app_nil_r [(c_want cx, crtA_En cx + 1)]).
  apply (crtA_core_move cx [(c_want cx, crtA_En cx + 1)] [] ly3 S3 U3 W3 ms3 ly3 S3 W3 _ Hcore
    ltac:(rewrite app_nil_r; reflexivity)).
  + apply (crtA_mk_trans W3 W3 W3 (ms_mem ms3) (ms_mem ms) mem2).
    * exact (crtA_mk_run cx _ ly3 S3 U3 W3 ms3 md3 (ms_mem ms) Hcore HARU HSB).
    * apply crtA_mk_av. intros a Ha. cbn [ms_mem mkst]. apply KR.
      destruct Ha as [Ht | Hs].
      -- pose proof (crtA_txt_blk _ _ _ _ _ _ _ Hcore) as Hin.
         destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) Hin) as (_ & A1 & A2 & _).
         pose proof (crtA_txt_req cx a Ht). lia.
      -- pose proof (fs_segs_img a (crt_pstat_img a Hs)) as Hi. unfold FS_IMG_END in Hi. lia.
  + intros r Hr. cbn [ms_regs mkst]. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    [ rewrite (QR 18%bv 18%nat ltac:(crtA_cs) ltac:(vm_compute; reflexivity)); exact (GB 18%bv 18%nat eq_refl ltac:(vm_compute; reflexivity))
    | rewrite (QR 20%bv 20%nat ltac:(crtA_cs) ltac:(vm_compute; reflexivity)); exact (GB 20%bv 20%nat eq_refl ltac:(vm_compute; reflexivity))
    | rewrite (QR 21%bv 21%nat ltac:(crtA_cs) ltac:(vm_compute; reflexivity)); exact (GB 21%bv 21%nat eq_refl ltac:(vm_compute; reflexivity))
    | rewrite (QR 22%bv 22%nat ltac:(crtA_cs) ltac:(vm_compute; reflexivity)); exact (GB 22%bv 22%nat eq_refl ltac:(vm_compute; reflexivity))
    | rewrite (QR 19%bv 19%nat ltac:(crtA_cs) ltac:(vm_compute; reflexivity)); exact (GB 19%bv 19%nat eq_refl ltac:(vm_compute; reflexivity))
    | rewrite (QR 25%bv 25%nat ltac:(crtA_cs) ltac:(vm_compute; reflexivity)); exact (GB 25%bv 25%nat eq_refl ltac:(vm_compute; reflexivity)) ].
- cbn [ms_regs mkst]. split.
  + rewrite Ha2. unfold HState.zs. rewrite length_map. reflexivity.
  + split.
    * (* B: En stays in s11 = x27 (A: s6 = x22) *)
      rewrite (QR 27%bv 27%nat ltac:(crtA_cs) ltac:(vm_compute; reflexivity)),
        (GB 27%bv 27%nat eq_refl ltac:(vm_compute; reflexivity)). exact Hs27.
    * (* B: want is s7 = x23, `mv s7, a0` at 0x81da4 (A: s10 = x26) *)
      rewrite (QR 23%bv 10%nat ltac:(crtA_cs) ltac:(vm_compute; reflexivity)),
        (GB 10%bv 10%nat eq_refl ltac:(vm_compute; reflexivity)). exact Ha0.
Qed.

(* ================= segment 4: B 0x81db0 -> malloc (same) -> 0x81db8 (A 0x81cb4 -> 0x81cbc) =================
   B 0x81db0 `addi a0, a0, 1` (|tb| + 1), 0x81db4 `jal __wrap_malloc` (PC_malloc 0x530e4). The record does not move
   (c_want was picked at 0x81da4): crtA_malloc_call at nb = 50 with w := c_want (B's atom 50 = En is past nb: the slot
   chunks read atoms 47 / 48 only). Ported from d25a984c903 check_round_trip_sd1.v (the second malloc of St1 -> St0).
   MEASURED by the engine on B: at the call ra = 0x81db8, a0 = SOff 10 1, every other register its own atom, the regions
   [s0; s1 slots crtA_cs1b] unchanged. *)
Definition crtA_ssC4 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL PC_malloc (crtA_ssR 0x81db0 crtA_cs1b [])).
Lemma crtA_extra_same : forall cx j, (j < 18)%nat ->
  nth j (crt_extra cx) (Z_to_bv 64 0) = nth j (crt_extra (crt_with cx (c_pos cx) (c_text cx) (c_want cx))) (Z_to_bv 64 0).
Proof. intros cx j Hj. do 18 (destruct j as [|j]; [reflexivity|]). lia. Qed.

Lemma crtA_seg4 : crt_from SK B (crt_ss_ret 0x81db8 crtA_cs1b crt_csF) crtA_INV_81cbc ->
  crt_from SK B (crt_ss_ret 0x81db0 crtA_cs1b crt_csF) crtA_INV_81cb4.
Proof.
intros NEXT cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFO HINV HS.
destruct HINV as (Hcore & -> & Ha0 & Hs27 & Hs23).
pose proof Hcore as (Hg & Hab & HU & Hh & H4 & Hrb & Hz & R18 & R20 & R21 & R22 & R19 & R25).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
pose proof HB as ((HPRE & HRO) & Hheads & Htop & Hfrl & Hr10 & Hr11 & Hr12 & Htext & Hnonul & Htblen & Htwin & Htblk
  & Hdec & Hbd0 & Hbody & Hrb0 & Hstat & Hquiet & Hlive0 & Hcells & Hsp47 & Hnev0 & Hbb0 & HTU0).
destruct (crtA_len (c_tb cx) (c_bs cx) Hdec Htblen) as (Hok & Hlen & Henc).
destruct (crtA_spf cx HB) as (Hal16 & Hceil0 & H47 & HS0 & Hsp1 & Hm32 & Hm16).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (E10 : ew E 10 = w64 (Z.of_nat (length (c_tb cx))))
  by (rewrite <- (crt_reg_atom E _ ms3 _ 10%bv 10 HS eq_refl); exact Ha0).
(* the run to the call: no store *)
pose proof (st_ok_submem tfibsegs E _ _ _ HS (crtA_sub2 0x81db0 crtA_cs1b crt_csF) ltac:(vm_compute; reflexivity)) as HS2.
change (st_ok tfibsegs E (crtA_ssR 0x81db0 crtA_cs1b []) (restrict (w_H W3) ms3)) in HS2.
assert (Hrun : sym_run_toN tfibsegs crt_tbl FUEL PC_malloc (crtA_ssR 0x81db0 crtA_cs1b []) = (crtA_ssC4, RS_running))
  by (vm_compute; reflexivity).
apply (crtA_run_slots 0x81db0 PC_malloc crtA_cs1b [] crtA_ssC4 cx E _ ly3 S3 U3 W3 ms3 md3 _ Hrun (Forall_nil _)
  HB HE HJ HARU HS2).
intros ms mat HSC HJC HARUC HSB.
set (mdC := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (G : forall (q : bv 5) n, sr_get (ss_regs crtA_ssC4) q = SOff n 0 -> YK11.getr (ms_regs ms) q = ew E n)
  by (intros q n Hq; exact (crt_reg_atom E (w_H W3) ms crtA_ssC4 q n HSC Hq)).
assert (Q1 : YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 0x81db8)
  by exact (fsw_reg_lit (w_H W3) E crtA_ssC4 ms 1%bv 0x81db8 HSC ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (Q2 : YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 (crt_sp1 cx))
  by (rewrite (G 2%bv 2%nat ltac:(vm_compute; reflexivity)); apply crtA_reg_eq; [exact E2 | rewrite <- E2; apply u64_range]).
assert (Q3 : YK11.getr (ms_regs ms) 3%bv = YK11.getr (c_regs cx) 3%bv)
  by (rewrite (G 3%bv 3%nat ltac:(vm_compute; reflexivity)); exact E3).
assert (Q4 : YK11.getr (ms_regs ms) 4%bv = YK11.getr (c_regs cx) 4%bv)
  by (rewrite (G 4%bv 4%nat ltac:(vm_compute; reflexivity)); exact E4).
assert (Q8 : YK11.getr (ms_regs ms) 8%bv = Z_to_bv 64 (spZ (c_regs cx)))
  by (rewrite (G 8%bv 8%nat ltac:(vm_compute; reflexivity)); apply crtA_reg_eq; [exact E8 | rewrite <- E8; apply u64_range]).
assert (Q9 : YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 (crt_sp1 cx))
  by (rewrite (G 9%bv 9%nat ltac:(vm_compute; reflexivity)); apply crtA_reg_eq; [exact E9 | rewrite <- E9; apply u64_range]).
(* B: SF is s10 = x26 (A: s3 = x19) *)
assert (Q26 : YK11.getr (ms_regs ms) 26%bv = Z_to_bv 64 (crt_SF cx))
  by (rewrite (G 26%bv 26%nat ltac:(vm_compute; reflexivity)); apply crtA_reg_eq; [exact E26 | rewrite <- E26; apply u64_range]).
assert (Q10 : YK11.getr (ms_regs ms) 10%bv = w64 (Z.of_nat (length (c_tb cx)) + 1)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtA_ssC4 ms 10%bv HSC).
  replace (sr_get (ss_regs crtA_ssC4) 10%bv) with (SOff 10 1) by (vm_compute; reflexivity).
  rewrite denot_lit_U, U_SOff, E10. unfold w64. f_equal. rewrite wz by lia. unfold zcanon, M64. apply Z.mod_small. lia. }
(* the frame at the call *)
destruct HFO as (Hfrs & Hnin & Hflag).
destruct (crt_F_facts SK B cx _ _ _ _ _ _ _ HJ HARU Hfrs) as (_ & HF4096 & HFceil & _).
assert (Hflag' : rdword (aview tfibsegs (w_H W3) (ms_mem ms)) (crt_F cx + fs_frame_bytes 3 - 8) = Some (crt_FL cx)).
{ rewrite <- Hflag. apply rdword_ext. intros i Hi. rewrite crt_frame3 in *.
  exact (aview_below (w_H W3) (ms_mem ms3) (ms_mem ms) alloc_ceiling (crt_F cx + 512 - 8 + i) HSB ltac:(lia)). }
destruct (crt_saved_words cx E crtA_ssC4 ms W3 0 HE HSC ltac:(vm_compute; reflexivity)) as (Hw8 & Hw16).
assert (HSV : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (spZ (c_regs cx))) crt_sv_chunks)
  by exact (crtA_region_chunks E crtA_ssC4 (w_H W3) ms 0 crt_s0_region 8 _ HSC ltac:(vm_compute; reflexivity)
    eq_refl E8).
assert (HCS1 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (crt_sp1 cx)) crtA_cs1b)
  by exact (crtA_region_chunks E crtA_ssC4 (w_H W3) ms 1 (crt_slot_region crtA_cs1b) 9 _ HSC
    ltac:(vm_compute; reflexivity) eq_refl E9).
(* the malloc *)
pose proof (crt_mkst (w_H W3) E crtA_ssC4 ms HSC ltac:(vm_compute; reflexivity)) as Ems.
replace (ss_pc crtA_ssC4) with PC_malloc in Ems by (vm_compute; reflexivity).
rewrite Ems.
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
assert (HL : 0 <= crtA_blen cx <= 2359298) by (unfold crtA_blen in *; lia).
assert (HEnb : FSH_Fn_writer.enc_size (crtA_blen cx) <= 3145734)
  by (unfold FSH_Fn_writer.enc_size; clear - HL; Z.div_mod_to_equations; lia).
assert (HEn : crtA_En cx + 1 = FSH_Fn_writer.enc_size (crtA_blen cx)) by reflexivity.
assert (HEn0 : 0 <= crtA_En cx) by (unfold crtA_En; apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia).
apply (crtA_malloc_call (fun _ => c_want cx) 50 cx E _ ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) mdC
  (Z.of_nat (length (c_tb cx)) + 1) 0x81db8 crtA_cs1b _ HB ltac:(lia)
  ltac:(intros res n' Hn'; replace n' with (32 + (n' - 32))%nat at 1 by lia;
        rewrite (crt_E_extra cx E (n' - 32) HE ltac:(unfold crt_nextra; lia)); apply crtA_extra_same; lia)
  HJC HARUC Hfrs Hnin Hflag' Q1 ltac:(lia) eq_refl Q2 Q3 Q4 Q8 Q9 Q26 Q10
  ltac:(unfold MALLOC_MAX; lia)
  ltac:(rewrite (crtA_bb _ _ _ _ _ Hab); cbn [bsum fold_right fst snd];
        unfold LIVE_check_round_trip, LIVE_MAX, HEAD in *; lia)
  ltac:(unfold EV_preset_base64_encode, CRT_EV_WRAP, EV_check_round_trip in *; lia)
  Hw8 Hw16 HSV HCS1
  ltac:(unfold crtA_atomlt, crtA_cs1b; repeat (apply Forall_cons; [do 4 eexists; split; [reflexivity | lia]|]);
        apply Forall_nil)
  ltac:(unfold crtA_cs1b; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil)).
intros res ly' S' W' regs' mem' md' HJ' HARU' HFO' HE' HS' HP' Hres Hr4 Hab' HJc HK.
apply (NEXT (crt_with cx (c_pos cx) (c_text cx) (c_want cx))
  (Ereg regs' (crt_extra (crt_with cx (c_pos cx) (c_text cx) (c_want cx))))
  (EV_preset_base64_encode + CRT_EV_WRAP + 1) ly' S' U3 W' (mkst regs' (Z_to_bv 64 0x81db8) mem' (seg_rom tfibsegs)) md'
  HB HE' HJ' HARU' HFO'); [|exact HS'].
assert (KP : forall r : bv 5, acallee_saved (bv_unsigned r) -> YK11.getr regs' r = YK11.getr (ms_regs ms) r)
  by (intros r Hr; exact (fsw_pres _ _ r HP' Hr)).
exists res. split; [|split; [unfold CRT_EV_WRAP; lia | split; [exact Hres | split]]].
- change (crtA_core cx ([(c_want cx, crtA_En cx + 1)] ++ [(res, Z.of_nat (length (c_tb cx)) + 1)]) ly' S' U3 W'
    (mkst regs' (Z_to_bv 64 0x81db8) mem' (seg_rom tfibsegs))).
  apply (crtA_core_move cx _ [(res, Z.of_nat (length (c_tb cx)) + 1)] ly3 S3 U3 W3 ms3 ly' S' W' _ Hcore Hab').
  + apply (crtA_mk_trans W3 W3 W' (ms_mem ms3) (ms_mem ms) mem').
    * exact (crtA_mk_run cx _ ly3 S3 U3 W3 ms3 md3 (ms_mem ms) Hcore HARU HSB).
    * exact (crtA_mk_malloc cx _ ly3 S3 U3 W3 ms3 (ms_mem ms) mdC ly' S' W' mem' md' res _ _ _ _ Hcore HARUC HARU' HJc
        Hab' HK).
  + intros r Hr. cbn [ms_regs mkst]. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    [ rewrite (KP 18%bv ltac:(crtA_cs)), (G 18%bv 18%nat ltac:(vm_compute; reflexivity)); symmetry;
      exact (crt_reg_atom E _ ms3 _ 18%bv 18 HS eq_refl)
    | rewrite (KP 20%bv ltac:(crtA_cs)), (G 20%bv 20%nat ltac:(vm_compute; reflexivity)); symmetry;
      exact (crt_reg_atom E _ ms3 _ 20%bv 20 HS eq_refl)
    | rewrite (KP 21%bv ltac:(crtA_cs)), (G 21%bv 21%nat ltac:(vm_compute; reflexivity)); symmetry;
      exact (crt_reg_atom E _ ms3 _ 21%bv 21 HS eq_refl)
    | rewrite (KP 22%bv ltac:(crtA_cs)), (G 22%bv 22%nat ltac:(vm_compute; reflexivity)); symmetry;
      exact (crt_reg_atom E _ ms3 _ 22%bv 22 HS eq_refl)
    | rewrite (KP 19%bv ltac:(crtA_cs)), (G 19%bv 19%nat ltac:(vm_compute; reflexivity)); symmetry;
      exact (crt_reg_atom E _ ms3 _ 19%bv 19 HS eq_refl)
    | rewrite (KP 25%bv ltac:(crtA_cs)), (G 25%bv 25%nat ltac:(vm_compute; reflexivity)); symmetry;
      exact (crt_reg_atom E _ ms3 _ 25%bv 25 HS eq_refl) ].
- (* B: En in s11 = x27 (A: s6 = x22) *)
  cbn [ms_regs mkst]. rewrite (KP 27%bv ltac:(crtA_cs)), (G 27%bv 27%nat ltac:(vm_compute; reflexivity)),
    <- (crt_reg_atom E _ ms3 _ 27%bv 27 HS eq_refl). exact Hs27.
- (* B: want in s7 = x23 (A: s10 = x26) *)
  cbn [ms_regs mkst]. rewrite (KP 23%bv ltac:(crtA_cs)), (G 23%bv 23%nat ltac:(vm_compute; reflexivity)),
    <- (crt_reg_atom E _ ms3 _ 23%bv 23 HS eq_refl). exact Hs23.
Qed.

(* ================= segment 5's exit: the static block facts of crt_l5_mem / crt_keepA =================
   At B 0x81db8 (A 0x81cbc) the walk's three blocks (text, want, same) sit on top of the entry's, each one live and pairwise
   separated by AR (YCbq.sep_blocks_pos). Everything crt_l5_mem and crt_keepA ask that is not a byte of memory - the
   bounds, the five separations, the two shadow-band exclusions, the stack-window exclusion, the frame separation and
   the window's writability and awr_byte arm - follows from that and from crt_base. ---- *)

(* ================= segment 5's exit: the static block facts of crt_l5_mem / crt_keepA =================
   At B 0x81db8 (A 0x81cbc) the walk's three blocks (text, want, same) sit on top of the entry's, each one live and
   pairwise separated by AR (YCbq.sep_blocks_pos). Everything crt_l5_mem and crt_keepA ask that is not a byte of memory -
   the bounds, the five separations, the two shadow-band exclusions, the stack-window exclusion, the frame separation
   and the window's writability and awr_byte arm - follows from that and from crt_base.
   PART C of the B twin (a Theorem Labs lane): A lines 2508-3122 of a working branch 6ae0548ca1d lib/A/FSH_crt_segA.v.
   B pcs (MEASURED, crt.B.s; A in brackets) and the non-mechanical changes of this part:
     segment 5        0x81db8 .. 0x81e18 [0x81cbc .. 0x81d0c], l = 0 bypass 0x81dd8 `beqz s4` -> 0x820a4
                      [0x81cdc -> 0x81f58]
     its stores       0x81db8 `sb zero, 0x38(s10)` (the n cell's granule; SF = s10 = atom 26, A: s3 = atom 19),
                      0x81dbc `sd zero, 0x1c0(s6)` (the n cell; F = s6, A: s7), 0x81dc0 `sd s7, 0x30(s1)` (want = s7,
                      A: 0x81cc8 `sd s10, 0x38(s1)`), 0x81dd4 `sd s6, 0x10(s1)` (F; A stores slot 0x10 in segment 1),
                      loop arm only: 0x81ddc `sd s11, 0x28(s1)` (En) and 0x81de0 `sd s3, 0x38(s1)` (F); A has no
                      loop-only spill (A 0x81cc0 `sd s7, 0x28(s1)` is on both arms)
     its tests        0x81dc4 `beqz s7` / 0x81dcc `beqz a0` (want / same non-null) [0x81ccc / 0x81cd4], and the UBSan
                      pointer-overflow test 0x81e10 `bltu a4, a3` (a4 = ~bd, a3 = 0; never taken; A has none)
   - crtA_ss5 re-seats x22 and x19 (both F on B: 0x81c20 `mv s6, s3`) to SOff 47 0, x23 (want) to SOff 49 0 and x27
     (En, 0x81d98) to SOff 50 0, so the engine names the frame region, the slot words and the En spill by the walk's
     atoms (A re-seats x23 = F and x26 = want only).
   - crtA_ss5a also carries the condition `bgeu ~bd, 0` (YP06.add_cond, true for every bd), so the engine decides the
     UBSan test 0x81e10 not taken.
   - the two arms leave DIFFERENT slot lists: crtA_cs5 (loop arm, six chunks = crt_cs1L's) and crtA_cs5z (bypass, four
     chunks = crt_cs1e's); the loop arm's boundary is crt_ss_ret 0x81e18 crt_cs1L crt_csF (lib/B/FSH_crt_base.v:153-166,
     0x82098 / 0x820a0 read the two spills back), the bypass's crt_ss_ret 0x820a4 crt_cs1e crt_csF. crtA_exit5 is
     generic in the measured list cs5 and the boundary's list cs1 (A: one list crtA_cs5 and crt_cs1e).
   - on the loop arm 0x81e08 `ld s6, 0x30(s1)` and 0x81e0c `mv s3, s6` overwrite F with want, so crtA_core's x22 / x19
     conjuncts do not hold at 0x81e18: crtA_exit5 carries the core's three memory facts (fs_glob, text's fs_rblock and
     zbytes_at) with crtA_mk_glob / crtA_mk_rblock / crtA_mk_zbytes directly (A: crtA_core_move with x23 = F), and
     takes only the registers crt6_keepA reads (x20 x21 x24 x25).
   - crt_INV_81d0c's B register clauses (x19 = x22 = x31 = want, x13 = 0, x15 = bd + 1, x14 = ~bd, x17 = -1, x16 = 103,
     x5 = 25, x6 = 51, x7 = 61, x29 = 207) and crt_INV_81f58's (x27 = En = 0, x22 = x19 = F) are read off the engine's
     final states; ~bd is the engine's SAlu ALU_XOR (SOff 21 0) (SLit (-1)) (crtA_U_not).
   - the SF atom is 26 everywhere (crtA_run_ret's shadow region, crtA_shadow5, crtA_reseat's x26). ---- *)
Lemma crtA_blk_sep : forall ly S (W : world tfibsegs) mem md x y,
  AR tfibsegs B ly S W mem md -> In x (ablocks B ly S) -> In y (ablocks B ly S) -> x <> y ->
  zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W mem md x y HAR Hx Hy Hne.
destruct (in_split _ _ Hx) as (l1 & l2 & E1). rewrite E1 in Hy.
apply in_app_or in Hy as [Hy | [Hy | Hy]]; [| exfalso; exact (Hne Hy) |].
- destruct (in_split _ _ Hy) as (m1 & m2 & E2). rewrite E2, <- app_assoc in E1. cbn [app] in E1.
  pose proof (sep_blocks_pos tfibsegs B (AR_laws_ok tfibsegs B) ly S W mem md y x m1 m2 l2 HAR E1) as D.
  unfold zdisjoint in D |- *. lia.
- destruct (in_split _ _ Hy) as (m1 & m2 & E2). rewrite E2 in E1.
  exact (sep_blocks_pos tfibsegs B (AR_laws_ok tfibsegs B) ly S W mem md x y l1 m1 m2 HAR E1).
Qed.
(* a block that joins the list after the entry's is not one of the entry's (a block is never disjoint from itself) *)
Lemma crtA_blk_new : forall ly3 S3 (W3 : world tfibsegs) mem md ly S x l,
  AR tfibsegs B ly3 S3 W3 mem md -> ablocks B ly3 S3 = ablocks B ly S ++ l -> In x l -> 0 <= snd x ->
  ~ In x (ablocks B ly S).
Proof.
intros ly3 S3 W3 mem md ly S x l HAR E Hx Hs Hin.
destruct (in_split _ _ Hin) as (l1 & l2 & E1). destruct (in_split _ _ Hx) as (m1 & m2 & E2).
assert (EA : ablocks B ly3 S3 = l1 ++ x :: (l2 ++ m1) ++ x :: m2)
  by (rewrite E, E1, E2, <- !app_assoc; reflexivity).
pose proof (sep_blocks_pos tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 mem md x x l1 (l2 ++ m1) m2 HAR EA) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D.
destruct (req_size_pos (snd x) Hs) as (R1 & R2). lia.
Qed.
(* two live blocks at one address are one block *)
Lemma crtA_addr_uniq : forall ly S (W : world tfibsegs) mem md p m m',
  AR tfibsegs B ly S W mem md -> In (p, m) (ablocks B ly S) -> In (p, m') (ablocks B ly S) -> m = m'.
Proof.
intros ly S W mem md p m m' HAR H1 H2.
destruct (al_blocks _ _ (AR_laws_ok tfibsegs B) _ _ _ _ _ _ _ HAR H1) as (_ & _ & _ & _ & _ & _ & Hm).
destruct (al_blocks _ _ (AR_laws_ok tfibsegs B) _ _ _ _ _ _ _ HAR H2) as (_ & _ & _ & _ & _ & _ & Hm').
destruct (Z.eq_dec m m') as [E|Hne]; [exact E|exfalso].
pose proof (crtA_blk_sep ly S W mem md (p, m) (p, m') HAR H1 H2 ltac:(injection 1; lia)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D.
pose proof (req_size_pos m ltac:(lia)) as (R1 & _). pose proof (req_size_pos m' ltac:(lia)) as (R2 & _). lia.
Qed.
(* a block whose window a boundary writes meets no user-poisoned head of U3: every head is a live block's first 16
   bytes, so it is either past the window (AR's block separation) or the window's own block's head, which the window
   either starts after (bd) or which is not in U3 at all (want, same: new blocks, and U3 holds only the entry's heads
   and the text's) *)
Lemma crtA_U_miss : forall cx blks ly3 S3 U3 (W3 : world tfibsegs) ms3 mm mdd p m z len,
  crtA_core cx blks ly3 S3 U3 W3 ms3 -> AR tfibsegs B ly3 S3 W3 mm mdd ->
  In (p, m) (ablocks B ly3 S3) -> p <= z -> 0 <= len -> z + len <= p + req_size m ->
  (p + 16 <= z \/ ~ In (p, 16) U3) ->
  forall r, In r U3 -> z + len <= fst r \/ fst r + snd r <= z.
Proof.
intros cx blks ly3 S3 U3 W3 ms3 mm mdd p m z len Hcore HAR Hin Hpz Hl Hzm Hown (x, y) Hxy.
pose proof Hcore as (_ & _ & _ & Hh & _).
destruct (Hh (x, y) Hxy) as (H16 & m' & Hin' & Hm'). cbn [fst snd] in H16, Hin', Hm' |- *. subst y.
destruct (Z.eq_dec x p) as [->|Hne].
- right. destruct Hown as [H|H]; [lia | exfalso; apply H].
  exact Hxy.
- pose proof (crtA_blk_sep ly3 S3 W3 mm mdd (p, m) (x, m') HAR Hin Hin' ltac:(injection 1; lia)) as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.
(* a block that is not one of the entry's, and is not the text's, has no head in U3 *)
Lemma crtA_U_fresh : forall cx blks ly3 S3 U3 (W3 : world tfibsegs) ms3 mm mdd p m,
  crtA_core cx blks ly3 S3 U3 W3 ms3 -> AR tfibsegs B ly3 S3 W3 mm mdd ->
  FSupoisonU.fs_heads B (c_ly cx) (c_S cx) (c_U cx) ->
  In (p, m) (ablocks B ly3 S3) -> ~ In (p, m) (ablocks B (c_ly cx) (c_S cx)) ->
  m <> FSH_Fn_writer.enc_size (crtA_blen cx) + HEAD ->
  ~ In (p, 16) U3.
Proof.
intros cx blks ly3 S3 U3 W3 ms3 mm mdd p m Hcore HAR FH Hin Hnew Hnm Hbad.
pose proof Hcore as (_ & Hab & HU & _ & _ & _ & _ & _).
rewrite HU in Hbad. apply in_app_or in Hbad as [Hb | [Hb | []]].
- destruct (FH (p, 16) Hb) as (_ & m3 & Hin3 & _). cbn [fst snd] in Hin3.
  assert (Hin3' : In (p, m3) (ablocks B ly3 S3)) by (rewrite Hab; apply in_or_app; left; exact Hin3).
  rewrite <- (crtA_addr_uniq ly3 S3 W3 mm mdd p m m3 HAR Hin Hin3') in Hin3. exact (Hnew Hin3).
- injection Hb as Hb1.
  assert (HinT : In (c_text cx - HEAD, FSH_Fn_writer.enc_size (crtA_blen cx) + HEAD) (ablocks B ly3 S3))
    by (rewrite Hab; apply in_or_app; right; left; reflexivity).
  rewrite Hb1 in HinT.
  exact (Hnm (crtA_addr_uniq ly3 S3 W3 mm mdd p m _ HAR Hin HinT)).
Qed.

(* a live block that is not one of the entry's: its bytes are writable, and each is awr_byte's temporary-block arm *)
Lemma crtA_window : forall cx ly3 S3 U3 (W3 : world tfibsegs) mem md p n,
  ARU tfibsegs B ly3 S3 U3 W3 mem md ->
  In (p, n) (ablocks B ly3 S3) -> ~ In (p, n) (ablocks B (c_ly cx) (c_S cx)) ->
  forall a, p <= a < p + n ->
    writable_at tfibsegs (mrestrict (w_H W3) mem) a /\
    awr_byte tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (ablocks B (c_ly cx) (c_S cx))
      (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)) a.
Proof.
intros cx ly3 S3 U3 W3 mem md p n HARU Hin Hnew a Ha.
pose proof (ARU_AR tfibsegs B ly3 S3 U3 W3 mem md HARU) as HAR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ (AR_laws_ok tfibsegs B) _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hceil & _ & Hpres & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as (_ & Hrq).
destruct (Hpres a ltac:(lia)) as (Hp & Hno).
split.
- apply (YCbq.apresent_writable tfibsegs).
  apply (FSW_frame.fsw_apresent_notowned B ly3 S3 U3 W3 mem md a HARU); [lia | exact Hno | exact Hp].
- left. right. right. left. exists p, n. split; [exact Hin | split; [exact Hnew | lia]].
Qed.
(* the n cell's granule after B 0x81db8 `sb zero, 0x38(s10)` (A 0x81cbc `sb zero, 0x38(s3)`): the frame's shadow byte
   56 is 0, so every byte of [F + 0x1c0, F + 0x1c8) is addressable (one granule, F being 32-aligned) *)
Lemma crtA_shadow56 : forall F x, F mod 32 = 0 -> F + 0x1c0 <= x < F + 0x1c0 + 8 ->
  shadow_of_addr SHADOW_OFF x = shadow_addr F + 56.
Proof.
intros F x HF Hx. unfold shadow_of_addr, shadow_addr, SHADOW_OFF.
Z.div_mod_to_equations. lia.
Qed.
Lemma crtA_ncell_ra : forall E (W : world tfibsegs) mem cx,
  crt_F cx mod 32 = 0 ->
  YP09.chunk_ok tfibsegs E (mrestrict (w_H W) mem) (crt_SF cx) (YP09.mkChunk 56 (CVal 1 (SLit 0))) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (crt_F cx + 0x1c0) 8.
Proof.
intros E W mem cx HF Hc x Hx.
pose proof (val_of_chunk_ok tfibsegs E (mrestrict (w_H W) mem) (crt_SF cx) 56 1 (SLit 0) 0 Hc
  ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
cbn [N.to_nat Pos.to_nat Pos.iter_op] in Hv.
specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
exists 0. split; [|left; reflexivity].
rewrite (crtA_shadow56 (crt_F cx) x HF Hx). unfold crt_SF in Hv. unfold aview. rewrite Hv. reflexivity.
Qed.

(* the run from a boundary state whose memory is crt_ss_ret's four regions: it writes only the stack window, the frame
   and the frame's shadow (crt_awr_ok), so every byte below alloc_ceiling outside the frame and its shadow survives.
   B: the shadow region's base is atom 26 (s10; A: atom 19) *)
Lemma crtA_run_ret : forall ss stop ssC cs csF cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3
  (Q : world tfibsegs -> config -> Prop),
  sym_run_toN tfibsegs crt_tbl FUEL stop ss = (ssC, RS_running) ->
  ss_mem ss = ss_mem (crt_ss_ret 0 cs csF) ->
  crt_base B cx -> crt_E cx E ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  frames S3 = (3, c_pos cx) :: frames (c_S cx) ->
  st_ok tfibsegs E ss (restrict (w_H W3) ms3) ->
  (forall ms mat, st_ok tfibsegs E ssC (restrict (w_H W3) ms) ->
     ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
       (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms))
       (with_vm_backing (m_vm_lazy md3) mat md3) k ->
     ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) ->
     (forall a, 0 <= a < alloc_ceiling -> ~ (crt_F cx <= a < crt_F cx + 512) ->
        ~ (crt_SF cx <= a < crt_SF cx + 64) -> ms_mem ms (Z_to_bv 64 a) = ms_mem ms3 (Z_to_bv 64 a)) ->
     SRr tfibsegs W3 (mkCfg ms (with_vm_backing (m_vm_lazy md3) mat md3)) Q) ->
  SRr tfibsegs W3 (mkCfg ms3 md3) Q.
Proof.
intros ss stop ssC cs csF cx E k ly3 S3 U3 W3 ms3 md3 Q HRUN Hmem HB HE HJ HARU Hfrs HS K.
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
destruct (crtA_spf cx HB) as (Hal16 & Hceil0 & H47 & HS0 & Hsp1 & Hm32 & Hm16).
pose proof crt_STK_eq as FS; unfold crt_STK in FS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (crt_F_facts SK B cx ly3 S3 U3 W3 (ms_mem ms3) md3 k HJ HARU Hfrs)
  as (HFal & HF4096 & HFceil & HFapp & HSF1 & HSF2).
assert (Efr : frame_addr ly3 3 (c_pos cx) = crt_F cx).
{ unfold crt_F, frame_addr. pose proof HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  rewrite EF. reflexivity. }
eapply (fsw_run_to_AJU (SK := SK) B crt_tbl crt_tbl_ok W3 FUEL stop E ss ssC RS_running ms3
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS HRUN I HARU HJ).
- rewrite Hmem. exact (crt_awr_ok B cx E ly3 S3 cs csF HE Hal16 ltac:(lia) Efr ltac:(lia)).
- intros ms mat HSC HJC HARUC HF HFr HG. apply (K ms mat HSC HJC HARUC).
  intros a Ha HnF HnS. apply HF. rewrite (wz a) by (pose proof (@alloc_ceiling_lt rc); lia).
  intros (rg & Hin & Hr). rewrite Hmem in Hin.
  cbn [ss_mem crt_ss_ret fss_ret_s0_args crt_ret_regions] in Hin.
  assert (E47 : bv_unsigned (ew E 47) = crt_F cx) by (rewrite (crt_E_F cx E HE); apply wz; lia).
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
    cbn [crt_s0_region fs_ret_s0_region crt_slot_region crt_frame_region crt_shadow_region
         YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [rewrite E8 in Hr | rewrite E9 in Hr | rewrite E47 in Hr; rewrite crt_frame3 in Hr
     | rewrite E26 in Hr; rewrite crt_frame3 in Hr]; cbn in Hr; lia.
Qed.

Lemma crtA_forall_incl : forall {X : Type} (P : X -> Prop) l l', Forall P l -> incl l' l -> Forall P l'.
Proof. intros X P l l' H Hi. rewrite Forall_forall in H |- *. intros x Hx. exact (H x (Hi x Hx)). Qed.
(* the flag word of a boundary's frame chunk, read back *)
Lemma crtA_flag_of_chunk : forall E (W : world tfibsegs) mem cx,
  0 <= crt_FL cx < 2 ^ 64 -> crt_E cx E ->
  YP09.chunk_ok tfibsegs E (mrestrict (w_H W) mem) (crt_F cx) (YP09.mkChunk 504 (CVal 8 (SOff 46 0))) ->
  rdword (aview tfibsegs (w_H W) mem) (crt_F cx + fs_frame_bytes 3 - 8) = Some (crt_FL cx).
Proof.
intros E W mem cx HFL HE Hc.
replace (crt_F cx + fs_frame_bytes 3 - 8) with (crt_F cx + 504) by (rewrite crt_frame3; lia).
apply (YF0x.val_mem_rdword (w_H W) mem _ _ HFL).
exact (val_of_chunk_ok tfibsegs E (mrestrict (w_H W) mem) (crt_F cx) 504 8 (SOff 46 0) (crt_FL cx) Hc
  ltac:(rewrite fsw_SOff0, (crt_E_FL cx E HE); reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
(* the bytes the boundaries keep (text's block and the four statics) lie below alloc_ceiling and off the frame and its
   shadow, so a run of segment 5 keeps them *)
Lemma crtA_mk_run5 : forall cx blks ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 m',
  crtA_core cx blks ly3 S3 U3 W3 ms3 -> ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  In (3, c_pos cx) (frames S3) -> frame_addr ly3 3 (c_pos cx) = crt_F cx ->
  4096 <= crt_F cx -> crt_F cx + 512 <= alloc_ceiling ->
  (forall a, 0 <= a < alloc_ceiling -> ~ (crt_F cx <= a < crt_F cx + 512) ->
     ~ (crt_SF cx <= a < crt_SF cx + 64) -> m' (Z_to_bv 64 a) = ms_mem ms3 (Z_to_bv 64 a)) ->
  crtA_mk W3 W3 (ms_mem ms3) m' (crtA_kept cx).
Proof.
intros cx blks ly3 S3 U3 W3 ms3 md3 m' Hc HARU Hin3 Efr HF0 HFc HK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 HARU) as HAR.
assert (HSFb : crt_SF cx = SHADOW_OFF + crt_F cx / 8) by reflexivity.
apply crtA_mk_raw. intros a Ha. apply HK.
- destruct Ha as [Ht | Hs].
  + pose proof (crtA_txt_blk _ _ _ _ _ _ _ Hc) as Hin.
    destruct (FSW_rd.fsw_ablock_low B ly3 S3 W3 _ _ _ _ HAR Hin) as (A1 & A2 & A3).
    pose proof (crtA_txt_req cx a Ht). lia.
  + pose proof (fs_segs_img a (crt_pstat_img a Hs)) as Hi. unfold FS_IMG_END in Hi. lia.
- destruct Ha as [Ht | Hs].
  + pose proof (crtA_txt_blk _ _ _ _ _ _ _ Hc) as Hin.
    pose proof (sep_block_frame tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 _ _ _ _ 3 (c_pos cx) HAR Hin Hin3) as D.
    unfold zdisjoint, block_rng, frame_rng in D. cbn [fst snd] in D. rewrite Efr, crt_frame3 in D.
    pose proof (crtA_txt_req cx a Ht). lia.
  + intros Hfr. refine (frm_img tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 _ md3 3 (c_pos cx) a HAR Hin3 _
      (crt_pstat_img a Hs)). rewrite Efr, crt_frame3. lia.
- rewrite HSFb.
  assert (Hq : crt_F cx / 8 < 2 ^ 44 - 64) by (apply Z.div_lt_upper_bound; lia).
  assert (Hq0 : 0 <= crt_F cx / 8) by (apply Z.div_pos; lia).
  destruct Ha as [Ht | Hs].
  + pose proof (crtA_txt_blk _ _ _ _ _ _ _ Hc) as Hin.
    pose proof (FSW_rd.fsw_ablock_off_shadow B ly3 S3 W3 _ _ _ _ HAR Hin a ltac:(exact (crtA_txt_req cx a Ht))) as Hsh.
    unfold SHADOW_OFF in *. lia.
  + pose proof (fs_segs_img a (crt_pstat_img a Hs)) as Hi. unfold FS_IMG_END, SHADOW_OFF in *. lia.
Qed.

(* B only: `not a4, s5` (B 0x81de8, xori a4, s5, -1), which the engine keeps as SAlu ALU_XOR (SOff 21 0) (SLit (-1)),
   is 2 ^ 64 - 1 - bd (the text of lib/B/FSW_past_nul.v pn_lxor_ones / pn_U_not, renamed) *)
Lemma crtA_lxor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx. change (2 ^ 64 - 1) with (Z.ones 64).
assert (HL : Z.land (Z.lxor x (Z.ones 64)) x = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 64) as [Hl|Hh].
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x i); reflexivity.
  - assert (Hb : Z.testbit x i = false).
    { rewrite <- (Z.mod_small x (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. }
    rewrite Hb. apply andb_false_r. }
pose proof (Z.add_nocarry_lxor _ _ HL) as Hs.
rewrite (Z.lxor_comm (Z.lxor x (Z.ones 64)) x), <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in Hs.
lia.
Qed.
Lemma crtA_U_not : forall E k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  YP0e.U E (SAlu ALU_XOR (SOff k 0) (SLit (-1))) = 2 ^ 64 - 1 - v.
Proof.
intros E k v H Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E k v H Hv), U_SLit.
change (zcanon (-1)) with (2 ^ 64 - 1). rewrite crtA_lxor_ones by exact Hv. apply zcanon_id. unfold M64. lia.
Qed.

(* ================= segment 5: B 0x81db8 -> 0x81e18, and the l = 0 bypass to 0x820a4 (A 0x81cbc -> 0x81d0c / 0x81f58)
   0x81db8 `sb zero, 0x38(s10)` (the n cell's granule), 0x81dbc `sd zero, 0x1c0(s6)` (the n cell), 0x81dc0
   `sd s7, 0x30(s1)` (want), the two null tests of want and same (decided by their blocks' 4096 <= _), 0x81dd0
   `ld a0, 0x30(s1)`, 0x81dd4 `sd s6, 0x10(s1)`, then 0x81dd8 `beqz s4`: at 1 <= |bs| the run falls through to the two
   loop spills (0x81ddc `sd s11, 0x28(s1)`, 0x81de0 `sd s3, 0x38(s1)`), the loop's registers 0x81de4 .. 0x81e14 and the
   UBSan test 0x81e10 to the encode loop's head 0x81e18; at |bs| = 0 it jumps to 0x820a4. The boundary state names the
   frame by atom 47 (s6 and s3), want by atom 49 (s7) and En by atom 50 (s11), so the engine finds the frame region,
   the slot words and the En spill; the branch is decided by atom 20's fact in the first arm and by s4 = 0 in the second,
   the UBSan test by the condition crtA_ss5a carries. The arms leave crt_ss_ret's four regions with crt_cs1L's
   (loop) / crt_cs1e's (bypass) slots, the frame's flag word and the n cell's shadow byte, so crtA_reseat re-seats them
   onto the walk's boundary state. ---- *)
Definition crtA_setr (ss : sstate) (r : bv 5) (v : sv) : sstate :=
  mkSST (ss_pc ss) (sr_set (ss_regs ss) r v) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition crtA_ss5 : sstate :=
  add_atom (add_atom
    (crtA_setr (crtA_setr (crtA_setr (crtA_setr (crt_ss_ret 0x81db8 crtA_cs1b crt_csF)
       22%bv (SOff 47 0)) 19%bv (SOff 47 0)) 23%bv (SOff 49 0)) 27%bv (SOff 50 0))
    49 (mkAF 4096 (2 ^ 47) 0)) 10 (mkAF 4096 (2 ^ 47) 0).
Definition crtA_ubsan5 : acond := mkAC BC_GEU (SAlu ALU_XOR (SOff 21 0) (SLit (-1))) (SLit 0).
Definition crtA_ss5a : sstate := add_cond (add_atom crtA_ss5 20 (mkAF 1 3145728 0)) crtA_ubsan5.
Definition crtA_ss5z : sstate := crtA_setr crtA_ss5 20%bv (SLit 0).
Definition crtA_ssC5a : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x81e18 crtA_ss5a).
Definition crtA_ssC5z : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x820a4 crtA_ss5z).
(* the slots each arm leaves (MEASURED, the engine's order): the loop arm's six (crt_cs1L's set) and the bypass's four
   (crt_cs1e's set); A has one list for both arms *)
Definition crtA_cs5 : list YP09.chunk :=
  [YP09.mkChunk 56 (CVal 8 (SOff 47 0)); YP09.mkChunk 40 (CVal 8 (SOff 50 0)); YP09.mkChunk 16 (CVal 8 (SOff 47 0));
   YP09.mkChunk 48 (CVal 8 (SOff 49 0)); YP09.mkChunk 24 (CVal 8 (SOff 48 0)); YP09.mkChunk 80 (CVal 8 (SOff 47 0))].
Definition crtA_cs5z : list YP09.chunk :=
  [YP09.mkChunk 16 (CVal 8 (SOff 47 0)); YP09.mkChunk 48 (CVal 8 (SOff 49 0)); YP09.mkChunk 24 (CVal 8 (SOff 48 0));
   YP09.mkChunk 80 (CVal 8 (SOff 47 0))].
Definition crtA_csF5 : list YP09.chunk :=
  [YP09.mkChunk 448 (CVal 8 (SLit 0)); YP09.mkChunk 504 (CVal 8 (SOff 46 0))].
Definition crtA_shadow5 : YP09.region :=
  YP09.mkRegion (Some 26%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 1 (SLit 0))].

(* ---- a Theorem Labs lane's crt6_keepA (lib/B/FSH_crt_keepA0.v, the B twin of a working branch ff3fb23bb7b): the
   whole memory and arithmetic content of crt_keepA and crt_l5_mem at A0's exit state, from the blocks A0 hands it.
   crtA_exit5 below applies it. ---- *)

(* the boundary state of B 0x81db8 with s6 / s3 named by the frame atom, s7 by want's and s11 by En's, and the three
   atom facts the two null tests and the branch read *)
Lemma crtA_ss5_ok : forall cx E ly3 S3 U3 (W3 : world tfibsegs) ms3 same,
  crt_E cx E ->
  crtA_core cx [(c_want cx, crtA_En cx + 1); (same, Z.of_nat (length (c_tb cx)) + 1)] ly3 S3 U3 W3 ms3 ->
  YK11.getr (ms_regs ms3) 10%bv = w64 same -> YK11.getr (ms_regs ms3) 23%bv = w64 (c_want cx) ->
  YK11.getr (ms_regs ms3) 27%bv = w64 (crtA_En cx) ->
  st_ok tfibsegs E (crt_ss_ret 0x81db8 crtA_cs1b crt_csF) (restrict (w_H W3) ms3) ->
  4096 <= c_want cx <= 2 ^ 47 -> 4096 <= same <= 2 ^ 47 ->
  st_ok tfibsegs E crtA_ss5 (restrict (w_H W3) ms3).
Proof.
intros cx E ly3 S3 U3 W3 ms3 same HE Hcore Ha0 Hs7 Hs11 HS Hw Hs.
pose proof Hcore as (_ & _ & _ & _ & _ & _ & _ & R18 & R20 & R21 & R22 & R19 & R25).
assert (A22 : ew E 22 = w64 (crt_F cx))
  by (rewrite <- (crt_reg_atom E (w_H W3) ms3 _ 22%bv 22 HS eq_refl); exact R22).
assert (A19 : ew E 19 = w64 (crt_F cx))
  by (rewrite <- (crt_reg_atom E (w_H W3) ms3 _ 19%bv 19 HS eq_refl); exact R19).
assert (A23 : ew E 23 = w64 (c_want cx))
  by (rewrite <- (crt_reg_atom E (w_H W3) ms3 _ 23%bv 23 HS eq_refl); exact Hs7).
assert (A27 : ew E 27 = w64 (crtA_En cx))
  by (rewrite <- (crt_reg_atom E (w_H W3) ms3 _ 27%bv 27 HS eq_refl); exact Hs11).
assert (A10 : ew E 10 = w64 same)
  by (rewrite <- (crt_reg_atom E (w_H W3) ms3 _ 10%bv 10 HS eq_refl); exact Ha0).
pose proof (crtA_st_set_reg E (crt_ss_ret 0x81db8 crtA_cs1b crt_csF) (restrict (w_H W3) ms3) 22%bv (SOff 47 0) HS
  ltac:(vm_compute; reflexivity)
  ltac:(lazymatch goal with |- _ = sv_denot _ (sr_get ?rs ?q) =>
          replace (sr_get rs q) with (SOff 22 0) by (vm_compute; reflexivity) end;
        rewrite !fsw_SOff0, (crt_E_F cx E HE), A22; reflexivity)) as H1.
pose proof (crtA_st_set_reg E _ (restrict (w_H W3) ms3) 19%bv (SOff 47 0) H1
  ltac:(vm_compute; reflexivity)
  ltac:(lazymatch goal with |- _ = sv_denot _ (sr_get ?rs ?q) =>
          replace (sr_get rs q) with (SOff 19 0) by (vm_compute; reflexivity) end;
        rewrite !fsw_SOff0, (crt_E_F cx E HE), A19; reflexivity)) as H2.
pose proof (crtA_st_set_reg E _ (restrict (w_H W3) ms3) 23%bv (SOff 49 0) H2
  ltac:(vm_compute; reflexivity)
  ltac:(lazymatch goal with |- _ = sv_denot _ (sr_get ?rs ?q) =>
          replace (sr_get rs q) with (SOff 23 0) by (vm_compute; reflexivity) end;
        rewrite !fsw_SOff0, (crt_E_want cx E HE), A23; reflexivity)) as H3.
pose proof (crtA_st_set_reg E _ (restrict (w_H W3) ms3) 27%bv (SOff 50 0) H3
  ltac:(vm_compute; reflexivity)
  ltac:(lazymatch goal with |- _ = sv_denot _ (sr_get ?rs ?q) =>
          replace (sr_get rs q) with (SOff 27 0) by (vm_compute; reflexivity) end;
        rewrite !fsw_SOff0, (crt_E_En cx E HE), A27; reflexivity)) as H4.
pose proof (YP03.st_ok_add_fact tfibsegs E _ (restrict (w_H W3) ms3) 49 (mkAF 4096 (2 ^ 47) 0) H4
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2];
        rewrite (crt_E_want cx E HE), (wz (c_want cx)) by lia;
        split; [lia | split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]])) as H5.
exact (YP03.st_ok_add_fact tfibsegs E _ (restrict (w_H W3) ms3) 10 (mkAF 4096 (2 ^ 47) 0) H5
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite A10; unfold w64; rewrite (wz same) by lia;
        split; [lia | split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]])).
Qed.

(* what both arms leave at their boundary: the walk's record re-seated (crtA_reseat), the frame's flag word, the n
   cell's granule, and - through a Theorem Labs lane's crt6_keepA - crt_keepA and crt_l5_mem. B: generic in the measured slot
   list cs5 and the boundary's slot list cs1 (crt_cs1L on the loop arm, crt_cs1e on the bypass); the core's memory
   facts are carried by crtA_mk_* directly, since the loop arm overwrites the core's x22 / x19 *)
Lemma crtA_exit5 : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 ssC ms md same r cs5 cs1,
  crt_base B cx -> crt_E cx E ->
  crtA_core cx [(c_want cx, crtA_En cx + 1); (same, Z.of_nat (length (c_tb cx)) + 1)] ly3 S3 U3 W3 ms3 ->
  k = EV_preset_base64_encode + 2 * CRT_EV_WRAP ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 -> crt_frame_ok cx S3 W3 ms3 ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms)) md k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms) md ->
  (forall a, 0 <= a < alloc_ceiling -> ~ (crt_F cx <= a < crt_F cx + 512) ->
     ~ (crt_SF cx <= a < crt_SF cx + 64) -> ms_mem ms (Z_to_bv 64 a) = ms_mem ms3 (Z_to_bv 64 a)) ->
  st_ok tfibsegs E ssC (restrict (w_H W3) ms) -> ss_resv ssC = None -> ss_pc ssC = r -> 0 <= r < 2 ^ 64 ->
  nth_error (ss_mem ssC) 0 = Some crt_s0_region ->
  nth_error (ss_mem ssC) 1 = Some (crt_slot_region cs5) ->
  nth_error (ss_mem ssC) 2 = Some (crt_frame_region crtA_csF5) ->
  nth_error (ss_mem ssC) 3 = Some crtA_shadow5 ->
  incl cs1 cs5 ->
  Forall (fun c => 0x10 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= 0x58) cs1 ->
  crt_atom_chunks cs1 -> YP09.region_wf (crt_slot_region cs1) = true ->
  sr_get (ss_regs ssC) 2%bv = SOff 2 0 -> sr_get (ss_regs ssC) 3%bv = SOff 3 0 ->
  sr_get (ss_regs ssC) 4%bv = SOff 4 0 -> sr_get (ss_regs ssC) 8%bv = SOff 8 0 ->
  sr_get (ss_regs ssC) 9%bv = SOff 9 0 -> sr_get (ss_regs ssC) 26%bv = SOff 26 0 ->
  YK11.getr (ms_regs ms) 20%bv = w64 (Z.of_nat (length (c_bs cx))) ->
  YK11.getr (ms_regs ms) 21%bv = w64 (c_bd cx) ->
  YK11.getr (ms_regs ms) 24%bv = w64 same ->
  YK11.getr (ms_regs ms) 25%bv = w64 (c_t cx) ->
  crt_E cx (Ereg (ms_regs ms) (crt_extra cx)) /\
  st_ok tfibsegs (Ereg (ms_regs ms) (crt_extra cx)) (crt_ss_ret r cs1 crt_csF)
    (restrict (w_H W3) (mkst (ms_regs ms) (Z_to_bv 64 r) (ms_mem ms) (seg_rom tfibsegs))) /\
  crt_frame_ok cx S3 W3 ms /\
  crt_keepA B cx same k ly3 S3 U3 W3 ms /\
  (1 <= Z.of_nat (length (c_bs cx)) -> crt_l5_mem B cx ly3 S3 W3 (ms_mem ms)).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 ssC ms md same r cs5 cs1 HB HE Hcore -> HARU HFO HJ HJC HARUC HK HSC Hres Hpc Hr
  Hm0 Hm1 Hm2 Hm3 HI1 HR1 HA1 HW1 Q2 Q3 Q4 Q8 Q9 Q26 G20 G21 G24 G25.
pose proof Hcore as (Hg & Hab & HU & Hh & H4 & Hrb & Hz & R18 & R20 & R21 & R22 & R19 & R25).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
destruct (crtA_spf cx HB) as (Hal16 & Hceil0 & H47 & HS0 & Hsp1 & Hm32 & Hm16).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof crt_STK_eq as FS; unfold crt_STK in FS.
destruct HFO as (Hfrs & Hnin & Hflag).
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 (ms_mem ms3) md3 _ HJ HARU Hfrs)
  as (HFal & HF4096 & HFceil & HFapp & HSF1 & HSF2).
assert (Efr : frame_addr ly3 3 (c_pos cx) = crt_F cx).
{ unfold crt_F, frame_addr. pose proof HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  rewrite EF. reflexivity. }
assert (E47 : bv_unsigned (ew E 47) = crt_F cx) by (rewrite (crt_E_F cx E HE); apply wz; lia).
(* the chunks the run leaves *)
assert (HSV : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (spZ (c_regs cx))) crt_sv_chunks)
  by exact (crtA_region_chunks E ssC (w_H W3) ms 0 crt_s0_region 8 _ HSC Hm0 eq_refl E8).
assert (HC5 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (crt_sp1 cx)) cs5)
  by exact (crtA_region_chunks E ssC (w_H W3) ms 1 (crt_slot_region cs5) 9 _ HSC Hm1 eq_refl E9).
assert (HCF5 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (crt_F cx)) crtA_csF5)
  by exact (crtA_region_chunks E ssC (w_H W3) ms 2 (crt_frame_region crtA_csF5) 47 _ HSC Hm2 eq_refl E47).
assert (HSH : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (crt_SF cx))
  [YP09.mkChunk 56 (CVal 1 (SLit 0))])
  by exact (crtA_region_chunks E ssC (w_H W3) ms 3 crtA_shadow5 26 _ HSC Hm3 eq_refl E26).
assert (Ecsf : crt_csF = [YP09.mkChunk 504 (CVal 8 (SOff 46 0))])
  by (unfold crt_csF; rewrite crt_frame3; reflexivity).
assert (HCS1 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (crt_sp1 cx)) cs1)
  by exact (crtA_forall_incl _ cs5 cs1 HC5 HI1).
assert (HCSF : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (crt_F cx)) crt_csF)
  by (rewrite Ecsf; apply (crtA_forall_incl _ crtA_csF5); [exact HCF5 | intros c Hc; cbn in Hc |- *; tauto]).
(* the flag word and the n cell's granule *)
assert (HFLr : 0 <= crt_FL cx < 2 ^ 64).
{ pose proof (al_flag _ _ (AR_laws_ok tfibsegs B) _ _ _ _ _ 3 (c_pos cx) (proj1 HJ) Hin3) as (_ & _ & Hfl & _).
  pose proof HJ as (_ & Hly & _). rewrite (crt_FL_ly cx _ ly3 Hly) in Hfl.
  unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Hfl. lia. }
assert (Hflag' : rdword (aview tfibsegs (w_H W3) (ms_mem ms)) (crt_F cx + fs_frame_bytes 3 - 8) = Some (crt_FL cx)).
{ apply (crtA_flag_of_chunk E W3 (ms_mem ms) cx HFLr HE).
  rewrite Forall_forall in HCF5. apply HCF5. cbn. tauto. }
assert (HN : range_addressable (aview tfibsegs (w_H W3) (ms_mem ms)) SHADOW_OFF (crt_F cx + 0x1c0) 8).
{ apply (crtA_ncell_ra E W3 (ms_mem ms) cx HFal). rewrite Forall_forall in HSH. apply HSH. cbn. tauto. }
assert (HFO' : crt_frame_ok cx S3 W3 ms) by (split; [exact Hfrs | split; [exact Hnin | exact Hflag']]).
(* the core's memory facts across the run (B: not the whole core, whose x22 / x19 the loop arm overwrites) *)
pose proof (crtA_mk_run5 cx _ ly3 S3 U3 W3 ms3 md3 (ms_mem ms) Hcore HARU Hin3 Efr ltac:(lia) ltac:(lia) HK) as HK5.
pose proof (check_round_trip_loops.enc_len_Z (c_bs cx)) as HL.
assert (Hl0 : 0 <= crtA_blen cx) by (unfold crtA_blen; lia).
assert (Hg' : exists peak, fs_glob tfibsegs W3 (ms_mem ms) (c_live cx + FSH_Fn_writer.enc_size (crtA_blen cx)) peak
    (c_cnt cx + 1) SIZE_MAXZ)
  by (destruct Hg as (peak & Hg); exists peak; exact (crtA_mk_glob _ _ _ _ _ _ _ _ _ HK5 (fun a Ha => or_intror Ha) Hg)).
assert (Hrb' : fs_rblock tfibsegs B ly3 S3 W3 (ms_mem ms) (c_text cx) (FSH_Fn_writer.enc_size (crtA_blen cx))).
{ apply (crtA_mk_rblock W3 W3 (ms_mem ms3) (ms_mem ms) (crtA_kept cx) ly3 S3 ly3 S3 _ _ HK5);
    [| intros Hin; exact Hin | exact Hrb].
  intros j Hj. left. unfold crtA_txt, FSH_Fn_writer.enc_size, HEAD in *. pose proof (Z.div_pos (crtA_blen cx + 2) 3).
  lia. }
assert (Hz' : zbytes_at tfibsegs W3 (ms_mem ms) (c_text cx) (WriterSpec.b64_enc (c_bs cx) ++ [0])).
{ apply (crtA_mk_zbytes W3 W3 (ms_mem ms3) (ms_mem ms) (crtA_kept cx) _ _ HK5); [|exact Hz].
  intros i Hi. left. rewrite length_app in Hi. cbn [length] in Hi. rewrite Nat2Z.inj_add, HL in Hi.
  unfold crtA_txt, FSH_Fn_writer.enc_size, HEAD, crtA_blen in *. lia. }
(* the input's bytes at the exit, from the entry's block *)
pose proof HB as ((HPRE & HRO) & Hheads & Htop & Hfrl & Hr10 & Hr11 & Hr12 & Htext & Hnonul & Htblen & Htwin & Htblk
  & Hdec & Hbd0 & Hbody & Hrb0 & Hstat & Hquiet & Hlive0 & Hcells & Hsp47 & Hnev0 & Hbb0 & HTU0).
destruct Htblk as (pt & kt & Hpt & Hpt1 & Hpt2).
assert (Hpt3 : In (pt, kt) (ablocks B ly3 S3)) by (rewrite Hab; apply in_or_app; left; exact Hpt).
pose proof (crtA_mk_blk (c_ly cx) (c_S cx) (c_U cx) (c_W cx) (c_mem cx) (c_md cx) ly3 S3 U3 W3 (ms_mem ms) md _
  STK_check_round_trip (spZ (c_regs cx)) [(3, c_pos cx)] pt kt (fsw_ARU B _ _ _ _ _ _ _ _ _ HPRE) HARUC HJC Hpt Hpt3)
  as KT.
assert (Hkt : kt <= req_size kt) by (unfold req_size; destruct (Z.eqb_spec kt 0); lia).
assert (HZT : zbytes_at tfibsegs W3 (ms_mem ms) (c_t cx) (HState.zs (c_tb cx ++ [Z_to_bv 8 0]))).
{ apply (crtA_mk_zbytes _ _ _ _ _ _ _ KT); [|exact Htext].
  intros i Hi. unfold HState.zs in Hi. rewrite length_map, length_app in Hi. cbn [length] in Hi. lia. }
(* the re-seated boundary *)
destruct (crtA_reseat cx E _ ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) md r cs1 crt_csF HE Hal16 ltac:(lia)
  ltac:(lia) H47 HJC HARUC Hin3
  ltac:(rewrite (crt_reg_atom E (w_H W3) ms ssC 2%bv 2 HSC Q2); apply crtA_reg_eq;
        [exact E2 | rewrite <- E2; apply u64_range])
  ltac:(rewrite (crt_reg_atom E (w_H W3) ms ssC 3%bv 3 HSC Q3); exact E3)
  ltac:(rewrite (crt_reg_atom E (w_H W3) ms ssC 4%bv 4 HSC Q4); exact E4)
  ltac:(rewrite (crt_reg_atom E (w_H W3) ms ssC 8%bv 8 HSC Q8); apply crtA_reg_eq;
        [exact E8 | rewrite <- E8; apply u64_range])
  ltac:(rewrite (crt_reg_atom E (w_H W3) ms ssC 9%bv 9 HSC Q9); apply crtA_reg_eq;
        [exact E9 | rewrite <- E9; apply u64_range])
  ltac:(rewrite (crt_reg_atom E (w_H W3) ms ssC 26%bv 26 HSC Q26); apply crtA_reg_eq;
        [exact E26 | rewrite <- E26; apply u64_range])
  HSV HCS1 HCSF HR1
  ltac:(rewrite Ecsf; apply Forall_cons; [cbn; rewrite crt_frame3; lia | apply Forall_nil])
  HA1
  ltac:(rewrite Ecsf; unfold crt_atom_chunks; apply Forall_cons;
        [do 4 eexists; split; [reflexivity | lia] | apply Forall_nil])
  HW1 ltac:(rewrite Ecsf; vm_compute; reflexivity)) as (HE' & HS').
split; [exact HE'|]. split; [exact HS'|]. split; [exact HFO'|].
(* a Theorem Labs lane's bundle *)
apply (FSH_crt_keepA0.crt6_keepA SK B cx same ly3 S3 U3 W3 ms md HB
  ltac:(rewrite Hab; unfold crtA_En, crtA_blen; reflexivity) HU Hh HARUC HJC HFO'
  ltac:(unfold crtA_blen in Hrb'; exact Hrb') ltac:(unfold crtA_blen in Hz'; exact Hz') HZT
  ltac:(unfold crtA_blen in Hg'; exact Hg') HN
  ltac:(split; [exact G20 | split; [exact G21 | split; [exact G24 | exact G25]]])).
Qed.

Lemma crtA_seg5 :
  crt_from SK B (crt_ss_ret 0x81e18 crt_cs1L crt_csF) (crtA_and (crt_INV_81d0c B) (crt_R5 B)) ->
  crt_from SK B (crt_ss_ret 0x820a4 crt_cs1e crt_csF) (crtA_and (crt_INV_81f58 B) (crt_R5 B)) ->
  crt_from SK B (crt_ss_ret 0x81db8 crtA_cs1b crt_csF) crtA_INV_81cbc.
Proof.
intros N1 N0 cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFO HINV HS.
destruct HINV as (same & Hcore & -> & Ha0 & Hs11 & Hs7).
pose proof Hcore as (Hg & Hab & HU & Hh & H4 & Hrb & Hz & R18 & R20 & R21 & R22 & R19 & R25).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
pose proof HB as ((HPRE & HRO) & Hheads & Htop & Hfrl & Hr10 & Hr11 & Hr12 & Htext & Hnonul & Htblen & Htwin & Htblk
  & Hdec & Hbd0 & Hbody & Hrb0 & Hstat & Hquiet & Hlive0 & Hcells & Hsp47 & Hnev0 & Hbb0 & HTU0).
destruct (crtA_len (c_tb cx) (c_bs cx) Hdec Htblen) as (Hok & Hlen & Henc).
destruct (crtA_spf cx HB) as (Hal16 & Hceil0 & H47 & HS0 & Hsp1 & Hm32 & Hm16).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof crt_STK_eq as FS; unfold crt_STK in FS.
pose proof (ARU_AR tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 HARU) as HAR3.
pose proof HFO as HFOc. destruct HFOc as (Hfrs & Hnin & Hflag).
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
(* the two new blocks *)
assert (HEn0 : 0 <= crtA_En cx)
  by (unfold crtA_En, crtA_blen; apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia).
assert (HinW : In (c_want cx, crtA_En cx + 1) (ablocks B ly3 S3))
  by (rewrite Hab; apply in_or_app; right; right; left; reflexivity).
assert (HinS : In (same, Z.of_nat (length (c_tb cx)) + 1) (ablocks B ly3 S3))
  by (rewrite Hab; apply in_or_app; right; right; right; left; reflexivity).
assert (HnewW : ~ In (c_want cx, crtA_En cx + 1) (ablocks B (c_ly cx) (c_S cx)))
  by (apply (crtA_blk_new ly3 S3 W3 _ _ (c_ly cx) (c_S cx) _ _ HAR3 Hab);
      [cbn; tauto | cbn [snd]; lia]).
assert (HnewS : ~ In (same, Z.of_nat (length (c_tb cx)) + 1) (ablocks B (c_ly cx) (c_S cx)))
  by (apply (crtA_blk_new ly3 S3 W3 _ _ (c_ly cx) (c_S cx) _ _ HAR3 Hab);
      [cbn; tauto | cbn [snd]; lia]).
destruct (FSW_rd.fsw_ablock_low B ly3 S3 W3 _ _ _ _ HAR3 HinW) as (BW1 & BW2 & BW3).
destruct (FSW_rd.fsw_ablock_low B ly3 S3 W3 _ _ _ _ HAR3 HinS) as (BS1 & BS2 & BS3).
assert (A20 : ew E 20 = w64 (Z.of_nat (length (c_bs cx))))
  by (rewrite <- (crt_reg_atom E (w_H W3) ms3 _ 20%bv 20 HS eq_refl); exact R20).
assert (A18 : ew E 18 = w64 SHADOW_OFF)
  by (rewrite <- (crt_reg_atom E (w_H W3) ms3 _ 18%bv 18 HS eq_refl); exact R18).
assert (Hbd : 4096 <= c_bd cx /\ c_bd cx + 1 < 2 ^ 64).
{ destruct Hrb0 as (kk & (Hin & _ & _ & _) & Hkk).
  destruct (FSW_rd.fsw_ablock_low B (c_ly cx) (c_S cx) (c_W cx) _ _ _ _
    (ARU_AR tfibsegs B _ _ _ _ _ _ (fsw_ARU B _ _ _ _ _ _ _ _ _ HPRE)) Hin) as (D1 & D2 & D3).
  unfold HEAD in *. pose proof (Zle_0_nat (length (c_bs cx))). lia. }
assert (A21 : ew E 21 = w64 (c_bd cx))
  by (rewrite <- (crt_reg_atom E (w_H W3) ms3 _ 21%bv 21 HS eq_refl); exact R21).
assert (A25 : ew E 25 = w64 (c_t cx))
  by (rewrite <- (crt_reg_atom E (w_H W3) ms3 _ 25%bv 25 HS eq_refl); exact R25).
assert (A10 : ew E 10 = w64 same)
  by (rewrite <- (crt_reg_atom E (w_H W3) ms3 _ 10%bv 10 HS eq_refl); exact Ha0).
assert (A47 : ew E 47 = w64 (crt_F cx)) by exact (crt_E_F cx E HE).
pose proof (crtA_ss5_ok cx E ly3 S3 U3 W3 ms3 same HE Hcore Ha0 Hs7 Hs11 HS ltac:(lia) ltac:(lia)) as HS5.
destruct (Z_le_gt_dec 1 (Z.of_nat (length (c_bs cx)))) as [Hl1 | Hl0].
- (* ---- 1 <= |bs|: the run falls through to the encode loop's head B 0x81e18 ---- *)
  assert (HSa : st_ok tfibsegs E crtA_ss5a (restrict (w_H W3) ms3)).
  { unfold crtA_ss5a, crtA_ubsan5.
    apply (YP06.st_ok_add_cond tfibsegs E _ _ BC_GEU (SAlu ALU_XOR (SOff 21 0) (SLit (-1))) (SLit 0)).
    - exact (YP03.st_ok_add_fact tfibsegs E crtA_ss5 _ 20 (mkAF 1 3145728 0) HS5
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite A20; unfold w64;
              rewrite (wz (Z.of_nat (length (c_bs cx)))) by lia;
              split; [lia | split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]])).
    - (* the UBSan test 0x81e10 `bltu ~bd, 0` is never taken: ~bd >= 0 *)
      rewrite branch_geu_U, (U_SLit E 0), (zcanon_id 0) by (unfold M64; lia).
      pose proof (U_range E (SAlu ALU_XOR (SOff 21 0) (SLit (-1)))) as HUr.
      apply negb_true_iff, Z.ltb_ge. lia. }
  apply (crtA_run_ret crtA_ss5a 0x81e18 crtA_ssC5a crtA_cs1b crt_csF cx E _ ly3 S3 U3 W3 ms3 md3 _
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HB HE HJ HARU Hfrs HSa).
  intros ms mat HSC HJC HARUC HK.
  assert (G : forall (q : bv 5) n, sr_get (ss_regs crtA_ssC5a) q = SOff n 0 -> YK11.getr (ms_regs ms) q = ew E n)
    by (intros q n Hq; exact (crt_reg_atom E (w_H W3) ms crtA_ssC5a q n HSC Hq)).
  destruct (crtA_exit5 cx E _ ly3 S3 U3 W3 ms3 md3 crtA_ssC5a ms (with_vm_backing (m_vm_lazy md3) mat md3) same
    0x81e18 crtA_cs5 crt_cs1L HB HE Hcore eq_refl HARU HFO HJ HJC HARUC HK HSC ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity)
    ltac:(intros c Hc; cbn in Hc |- *; tauto)
    ltac:(unfold crt_cs1L; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil)
    ltac:(unfold crt_atom_chunks, crt_cs1L; repeat (apply Forall_cons; [do 4 eexists; split; [reflexivity | lia]|]);
          apply Forall_nil)
    ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(rewrite (G 20%bv 20%nat ltac:(vm_compute; reflexivity)); exact A20)
    ltac:(rewrite (G 21%bv 21%nat ltac:(vm_compute; reflexivity)); exact A21)
    ltac:(rewrite (G 24%bv 10%nat ltac:(vm_compute; reflexivity)); exact A10)
    ltac:(rewrite (G 25%bv 25%nat ltac:(vm_compute; reflexivity)); exact A25))
    as (HE' & HS' & HFO' & HKA & HL5).
  pose proof (crt_mkst (w_H W3) E crtA_ssC5a ms HSC ltac:(vm_compute; reflexivity)) as Ems.
  replace (ss_pc crtA_ssC5a) with 531992 in Ems by (vm_compute; reflexivity).
  rewrite Ems.
  apply (N1 cx (Ereg (ms_regs ms) (crt_extra cx)) _ ly3 S3 U3 W3
    (mkst (ms_regs ms) (Z_to_bv 64 531992) (ms_mem ms) (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md3) mat md3)
    HB HE' HJC HARUC HFO'); [|exact HS'].
  split.
  + (* crt_INV_81d0c's B registers, read off the engine's state at 0x81e18 *)
    unfold crt_INV_81d0c. cbn zeta. cbn [ms_regs ms_mem mkst].
    split; [rewrite (G 19%bv 49%nat ltac:(vm_compute; reflexivity)); exact (crt_E_want cx E HE)|].
    split; [rewrite (G 22%bv 49%nat ltac:(vm_compute; reflexivity)); exact (crt_E_want cx E HE)|].
    split; [rewrite (G 31%bv 49%nat ltac:(vm_compute; reflexivity)); exact (crt_E_want cx E HE)|].
    split; [exact (fsw_reg_lit (w_H W3) E crtA_ssC5a ms 13%bv 0 HSC ltac:(vm_compute; reflexivity) ltac:(lia))|].
    split.
    { rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtA_ssC5a ms 15%bv HSC).
      replace (sr_get (ss_regs crtA_ssC5a) 15%bv) with (SOff 21 1) by (vm_compute; reflexivity).
      rewrite denot_lit_U, U_SOff, A21. unfold w64. f_equal. rewrite (wz (c_bd cx)) by lia.
      unfold zcanon, M64. apply Z.mod_small. lia. }
    split; [rewrite (G 20%bv 20%nat ltac:(vm_compute; reflexivity)); exact A20|].
    split; [rewrite (G 21%bv 21%nat ltac:(vm_compute; reflexivity)); exact A21|].
    split; [rewrite (G 18%bv 18%nat ltac:(vm_compute; reflexivity)); exact A18|].
    split.
    { rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crtA_ssC5a ms 14%bv HSC).
      replace (sr_get (ss_regs crtA_ssC5a) 14%bv) with (SAlu ALU_XOR (SOff 21 0) (SLit (-1)))
        by (vm_compute; reflexivity).
      rewrite denot_lit_U, (crtA_U_not E 21 (c_bd cx) A21 ltac:(lia)). reflexivity. }
    split; [exact (fsw_reg_lit (w_H W3) E crtA_ssC5a ms 17%bv (2 ^ 64 - 1) HSC ltac:(vm_compute; reflexivity)
              ltac:(lia))|].
    split; [exact (fsw_reg_lit (w_H W3) E crtA_ssC5a ms 16%bv 103 HSC ltac:(vm_compute; reflexivity) ltac:(lia))|].
    split; [exact (fsw_reg_lit (w_H W3) E crtA_ssC5a ms 5%bv 25 HSC ltac:(vm_compute; reflexivity) ltac:(lia))|].
    split; [exact (fsw_reg_lit (w_H W3) E crtA_ssC5a ms 6%bv 51 HSC ltac:(vm_compute; reflexivity) ltac:(lia))|].
    split; [exact (fsw_reg_lit (w_H W3) E crtA_ssC5a ms 7%bv 61 HSC ltac:(vm_compute; reflexivity) ltac:(lia))|].
    split; [exact (fsw_reg_lit (w_H W3) E crtA_ssC5a ms 29%bv 207 HSC ltac:(vm_compute; reflexivity) ltac:(lia))|].
    exact (HL5 Hl1).
  + exists same. split; [|exact HKA].
    cbn [ms_regs mkst]. rewrite (G 25%bv 25%nat ltac:(vm_compute; reflexivity)). exact A25.
- (* ---- |bs| = 0: 0x81dd8 `beqz s4` jumps to 0x820a4 ---- *)
  assert (Hbs : c_bs cx = []) by (destruct (c_bs cx) as [|b l]; [reflexivity | cbn in Hl0; lia]).
  assert (HEnz : crtA_En cx = 0) by (unfold crtA_En, crtA_blen; rewrite Hbs; reflexivity).
  assert (HSz : st_ok tfibsegs E crtA_ss5z (restrict (w_H W3) ms3)).
  { exact (crtA_st_set_reg E crtA_ss5 _ 20%bv (SLit 0) HS5 ltac:(vm_compute; reflexivity)
      ltac:(replace (sr_get (ss_regs crtA_ss5) 20%bv) with (SOff 20 0) by (vm_compute; reflexivity);
            rewrite fsw_SOff0, A20, Hbs; cbn [length Z.of_nat]; unfold w64;
            rewrite denot_lit_U, U_SLit; reflexivity)). }
  apply (crtA_run_ret crtA_ss5z 0x820a4 crtA_ssC5z crtA_cs1b crt_csF cx E _ ly3 S3 U3 W3 ms3 md3 _
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HB HE HJ HARU Hfrs HSz).
  intros ms mat HSC HJC HARUC HK.
  assert (G : forall (q : bv 5) n, sr_get (ss_regs crtA_ssC5z) q = SOff n 0 -> YK11.getr (ms_regs ms) q = ew E n)
    by (intros q n Hq; exact (crt_reg_atom E (w_H W3) ms crtA_ssC5z q n HSC Hq)).
  assert (G20 : YK11.getr (ms_regs ms) 20%bv = w64 (Z.of_nat (length (c_bs cx))))
    by (rewrite Hbs; cbn [length Z.of_nat];
        exact (fsw_reg_lit (w_H W3) E crtA_ssC5z ms 20%bv 0 HSC ltac:(vm_compute; reflexivity) ltac:(lia))).
  destruct (crtA_exit5 cx E _ ly3 S3 U3 W3 ms3 md3 crtA_ssC5z ms (with_vm_backing (m_vm_lazy md3) mat md3) same
    0x820a4 crtA_cs5z crt_cs1e HB HE Hcore eq_refl HARU HFO HJ HJC HARUC HK HSC ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity)
    ltac:(intros c Hc; cbn in Hc |- *; tauto)
    ltac:(unfold crt_cs1e; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil)
    ltac:(unfold crt_atom_chunks, crt_cs1e; repeat (apply Forall_cons; [do 4 eexists; split; [reflexivity | lia]|]);
          apply Forall_nil)
    ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    G20
    ltac:(rewrite (G 21%bv 21%nat ltac:(vm_compute; reflexivity)); exact A21)
    ltac:(rewrite (G 24%bv 10%nat ltac:(vm_compute; reflexivity)); exact A10)
    ltac:(rewrite (G 25%bv 25%nat ltac:(vm_compute; reflexivity)); exact A25))
    as (HE' & HS' & HFO' & HKA & _).
  (* want's window at the exit *)
  pose proof (crtA_window cx ly3 S3 U3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3)
    (c_want cx) (crtA_En cx + 1) HARUC HinW HnewW) as HW.
  assert (HUo : forall r, In r U3 -> c_want cx + crtA_En cx + 1 <= fst r \/ fst r + snd r <= c_want cx + crtA_En cx).
  { apply (crtA_U_miss cx _ ly3 S3 U3 W3 ms3 _ _ (c_want cx) (crtA_En cx + 1) (c_want cx + crtA_En cx) 1
      Hcore HAR3 HinW ltac:(lia) ltac:(lia) ltac:(lia)).
    right. apply (crtA_U_fresh cx _ ly3 S3 U3 W3 ms3 _ _ (c_want cx) (crtA_En cx + 1) Hcore HAR3 Hheads HinW HnewW).
    unfold FSH_Fn_writer.enc_size, crtA_En, crtA_blen, HEAD. lia. }
  assert (HRA : range_addressable (aview tfibsegs (w_H W3) (ms_mem ms)) SHADOW_OFF (c_want cx + crtA_En cx) 1).
  { apply (crtA_body_addressable_U ly3 S3 U3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3)
      (c_want cx) (crtA_En cx + 1) (c_want cx + crtA_En cx) 1 HARUC Hh HinW ltac:(lia) ltac:(lia) ltac:(lia) HUo). }
  pose proof (FSW_rd.fsw_ablock_off_shadow B ly3 S3 W3 _ _ _ _ HAR3 HinW) as HSHW.
  pose proof (sep_block_frame tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 _ _ _ _ 3 (c_pos cx) HAR3 HinW Hin3) as HDF.
  unfold zdisjoint, block_rng, frame_rng in HDF. cbn [fst snd] in HDF.
  pose proof HJ as (_ & HlyJ & _).
  assert (Efr : frame_addr ly3 3 (c_pos cx) = crt_F cx)
    by (unfold crt_F, frame_addr; destruct HlyJ as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
  rewrite Efr, crt_frame3 in HDF.
  pose proof (crt_mkst (w_H W3) E crtA_ssC5z ms HSC ltac:(vm_compute; reflexivity)) as Ems.
  replace (ss_pc crtA_ssC5z) with 532644 in Ems by (vm_compute; reflexivity).
  rewrite Ems.
  apply (N0 cx (Ereg (ms_regs ms) (crt_extra cx)) _ ly3 S3 U3 W3
    (mkst (ms_regs ms) (Z_to_bv 64 532644) (ms_mem ms) (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md3) mat md3)
    HB HE' HJC HARUC HFO'); [|exact HS'].
  split.
  + (* crt_INV_81f58's B clauses: a0 = want + En, s2, s11 = En = 0, s6 = s3 = F, and want's NUL byte *)
    unfold crt_INV_81f58. cbn zeta. cbn [ms_regs ms_mem mkst].
    assert (HEq : (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4 = 0)
      by (unfold crtA_En, crtA_blen in HEnz; exact HEnz).
    assert (HR1 : 1 <= req_size (crtA_En cx + 1)) by (destruct (req_size_pos (crtA_En cx + 1) ltac:(lia)); lia).
    rewrite HEq, !Z.add_0_r.
    split; [rewrite (G 10%bv 49%nat ltac:(vm_compute; reflexivity)); exact (crt_E_want cx E HE)|].
    split; [rewrite (G 18%bv 18%nat ltac:(vm_compute; reflexivity)); exact A18|].
    split; [rewrite (G 27%bv 50%nat ltac:(vm_compute; reflexivity)), (crt_E_En cx E HE); unfold crt_En;
            rewrite HEq; reflexivity|].
    split; [rewrite (G 22%bv 47%nat ltac:(vm_compute; reflexivity)); exact A47|].
    split; [rewrite (G 19%bv 47%nat ltac:(vm_compute; reflexivity)); exact A47|].
    split; [rewrite Hbs; replace (WriterSpec.b64_enc []) with (@nil Z) by (vm_compute; reflexivity);
            intros j Hj; cbn in Hj; lia|].
    split; [lia|].
    split; [lia|].
    split; [intros a Ha; apply HSHW; lia|].
    split; [intros a Ha; unfold HState.in_window; lia|].
    split; [rewrite crt_frame3; lia|].
    split; [rewrite HEnz, Z.add_0_r in HRA; exact HRA|].
    destruct (HW (c_want cx) ltac:(lia)) as (HWw & HWa).
    split; [exact HWw | exact HWa].
  + exists same. split; [|exact HKA].
    cbn [ms_regs mkst]. rewrite (G 25%bv 25%nat ltac:(vm_compute; reflexivity)). exact A25.
Qed.
(* ================= lane A0's entry theorem =================
   The walk from check_round_trip's entry B 0x81b9c (A 0x81a9c) to the encode loop's head B 0x81e18 (A 0x81d0c), and,
   at |bs| = 0, to B 0x820a4 (A 0x81f58). Its two premises are the lanes that follow: L5 at crt_ss_ret 0x81e18
   crt_cs1L crt_csF (B: the loop arm's spills; A: crt_cs1e) and segment 6 at crt_ss_ret 0x820a4 crt_cs1e crt_csF, each
   beside crt_R5. Composed: crtA_to_81c84 <- crtA_seg2 <- crtA_seg3 <- crtA_seg4 <- crtA_seg5. ---- *)
Theorem crtA_from_entry :
  crt_from SK B (crt_ss_ret 0x81e18 crt_cs1L crt_csF) (crtA_and (crt_INV_81d0c B) (crt_R5 B)) ->
  crt_from SK B (crt_ss_ret 0x820a4 crt_cs1e crt_csF) (crtA_and (crt_INV_81f58 B) (crt_R5 B)) ->
  forall cx, crt_base B cx ->
  SRr tfibsegs (c_W cx) (cfg_at tfibsegs A_check_round_trip (c_regs cx) (c_mem cx) (c_md cx)) (crt_post SK B cx).
Proof.
intros N1 N0.
exact (crtA_to_81c84 (crtA_seg2 (crtA_seg3 (crtA_seg4 (crtA_seg5 N1 N0))))).
Qed.
End W.

Print Assumptions crtA_from_entry.
