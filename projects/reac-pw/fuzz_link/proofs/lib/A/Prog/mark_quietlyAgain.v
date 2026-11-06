(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the tail of pcap_source_open (fuzz_pcap.asan-ubsan 0x811e0, listing offset
   AF_pcap_source_open = 0xa58, 246 instructions) on libreac v1.9.0's ASan+UBSan build: lib/A's PcapSourceOpenB.v, the
   walk from the two semantic cuts of lib/B/Prog/PcapSourceOpenPh.v to the return. op_from_null and op_from_read prove
   `op_from op_gi_null` and `op_from op_gi_read`, i.e. lib/A's image-generic post tpcap_source_open_post (with
   topen_kept, lib/A/Prog/PcapSourceOpenDefs.v) at this image (SEGS = pa_segs, the relro window pa_relro_lo /
   pa_relro_hi of the lib/B PAImg instance PI); PcapSourceOpen.v (the head) composes them. At ossv/recipes 25e3d17bdb50 (2026-10-29), this image had no released
   proof (rule 24, a Theorem Labs lane, 22:35Z); the released v1.8 UBSan proof lib/U/Prog/pcap_source_open.v is the guard
   template only.

   The paths, at this image's pcs:
   - the empty input (cut 0x813f8, f = NULL): a0 := -1, `j 0x81474`, the epilogue without the buffer re-poison;
   - the short read (cut 0x8138c, kr <> 24): `bne a0,s9` to 0x81400, the shadow test of ps (0x81400 `lbu`, 0x81404
     `bnez`), f = ps->f (0x81408), the fclose wrapper's call (0x8140c), the second shadow test (0x81410, 0x81414
     `beqz` to 0x8145c), ps->f := NULL (0x8145c), a0 := -1, the epilogue from 0x81464 (op_fclose);
   - kr = 24: the UBSan guard G6 (below), the magic of the four header bytes F + 32 .. F + 35 (0x81398..0x813c4, the
     top byte through `slliw`, magic_U), then 0xd4c3b2a1 (0x813c8 `beq` to 0x81420: ps->swapped := 1, a0 := 0,
     `j 0x81464`), 0xa1b2c3d4 (0x813d4 `bne` falls to 0x813d8: ps->swapped := 0, a0 := 0, `j 0x81464`), or the bad
     magic (0x81444: as the short read, fclose at 0x81450);
   - the epilogue (op_epi): the buffer out of scope (0x81464..0x81470, 3 shadow bytes 0xf8), the retired magic
     0x45e0360e at F (0x8147c); 0x81480 `beqz s2` NOT taken (s2 = F >= 4096, atom 18's fact), so the machine-frame
     arm 0x814d4..0x81500 is dead; F's 16 shadow bytes 0xf5 (0x81484..0x814c4); the flag through `ld a1,0x78(s2)` and
     `sb zero,0(a1)` (0x814c8, 0x814cc), which gives the frame back (lib/B/Prog/PcapFrame.v aj_flag_store_pi:
     astack_free_law, frame_flag_lawP); the restores and `ret` (0x81504..0x81538).
   The two guards on ps (G5, 0x812f8 and 0x81300 / 0x81304) are before the cuts, in the head.

   THE GUARD G6. 0x81390 `addi a0,zero,-3`, 0x81394 `bgeu s4,a0` branches to the `unimp` at 0x8153c when the header
   buffer s4 = F + 32 lies within 3 bytes of 2^64. The symbolic run decides it, NOT taken: decide_cond2
   (Reusable/YP0e.v:932) maps BC_GEU to the negation of decide_ltu2 (:922), and decide_ltu (Reusable/YP0m.v:673) finds
   atom 20 (s4) below the literal 2^64 - 3 from its range fact [4128, 0x7fffff800020] (rd_facts), which rd_entry
   proves from frames_bounds on the class-1 frame (F + 128 <= alloc_ceiling <= 0x7fffff800000). Templates: the released
   UBSan proof of the v1.8 image, proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_open.v on origin/ossv/recipes
   c8557374ad2e, open_mid :286 (premise bv_unsigned sp0 < 2 ^ 63 at :291, frame bounds :295-299), which decides the
   guard at :410-412; and the earlier walk of this image, on a working branch
   (a8ccd33b1a7) pcap_source_open_tl.v (sha256 4aaa5af08467; internal record) pso_rdchk :36-67 (premise bv_unsigned s4 < 2 ^ 64 - 3 at :44,
   `step; step; if_false` at :65).

   THE REPORT PATHS are proved unreachable; no run steps into one. Every shadow test of ps in this stretch
   (0x81400 / 0x81404 and 0x81410 / 0x81414 on the short read, 0x81444 / 0x81448 and 0x81454 / 0x81458 on the bad
   magic, 0x813e4 / 0x813e8 and 0x8142c / 0x81430 on ps + 8 before the slow checks 0x81570 / 0x81584) is decided by
   the shadow entry of ps (rd_SH: ps's 24 bytes addressable; shent_rd_ok from op_pre's range_addressable, kept to the
   cut by op_mid's topen_kept and across fclose by its journal, shok_transfer), so the token run reads a 0 shadow byte
   and takes the non-report successor: the report calls 0x8141c, 0x81580, 0x81594 and 0x815a0..0x815b4 are never
   reached.

   The callees are Section hypotheses of their exact statement types: the fclose wrapper AFCLOSE, of
   lib/A/Stdio/PFclose.v's image-generic afclose_source_spec (= afclose_source_spec_stk PFCLOSE_STK) at this image,
   bound as lib/B/Prog/PcapSourceClose.v binds it (its data-buffer premise from op_pre's input block); the file meter
   FM (lib/A/Stdio/PSourceMeter.v asrc_file_meter); the frame give-back laws astack_free_law (Reusable/YG0d.v:301) and
   frame_flag_lawP (Reusable/YCbq.v:797) with model_laws; the meter laws (Reusable/YC5d.v ameter_laws,
   ameter_fs_laws); ASIL (lib/A/Stdio/PSourceMeta.v asource_img_laws). The stream predicates' frame lemmas are copied
   from lib/B/Prog/PcapSourceClose.v (not required). getr / mkst / seg_rom come from YK11; nothing from lib/Lib is
   imported. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpenB.v, with its module paths, module names and numbers changed; 660 of its 725 lines of code are new or changed and 1681 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_entry.v, with its module paths, module names and numbers changed; 368 of its 431 lines of code are new or changed and 662 lines of the source are left out. *)
(* mark_quietly (fuzz_link.c:153-164) on image A (fuzz_link.asan 0x883d4, 124 bytes; listing
   (internal path) (internal record, sha256 83bb83545bf3)), the later arm: the walk of
   mark_quietly_c.v `mark_quietly_acontract_again` (aleaf_fx, K = 24608, EV = 0).

   The walk on link's program tables (LinkWalk.v run instance paj_run_x over the caller's journal ajournal_gx):
   - entry state mqa_ss: the 32-byte frame (stack_region 32) and g_sink as one 8-byte chunk at its object
     A_OBJ 29 (0x62fec0) over the fresh atom 32 = sink (1 <= sink, so `bnez a1` at +0x24 is decided);
   - run 1, +0x00 .. +0x4c: the frame stores, s0 := a1, s2 := the auipc value A_HI 68 (0x6303ec), the load of
     g_sink at +0x1c through A_OBJ 29, s1 := a0, `bnez a1` taken; the run stops at +0x4c `ld a0, -0x52c(s2)`,
     the same 8 bytes through the base atom A_HI 68;
   - the region of g_sink is re-based on A_HI 68 (offset -0x52c);
   - run 2, +0x4c .. +0x50: a0 := sink, the call of wrapper_rewind (0x430d4), lifted onto the journal by
     mark_quietlyRw.v aj_gx_rewind_at over LinkMfDefs.v arewind_mf_realizes, its premises from
     mark_quietlyArg.v mqa_rw_args;
   - run 3, +0x54 .. +0x70: a0 := s1, a1 := s0, ra / s0 / s1 / s2 reloaded, the frame popped, the tail jump to
     reac_served_mark (0x895a8);
   - the tail: reac_served_mark's contract (Section hypothesis RSM) at the jump state, its premises and the
     caller's Post from mark_quietlyRsm.v, composed by LinkWalkMkTail.v apostF_tail.

   Section hypotheses: LAWS (AR_laws), TL (PALib), LV (LinkVals), TB (PcapSyms; instance AD2l.PcapB_syms),
   HSEGS (pa_segs = tfibsegs), RW (the rewind wrapper's contract, LinkMfDefs.v; discharge `link_arewind_ok`),
   RSM (reac_served_mark's contract; discharge reac_served_mark_aproof).
   The stack-guard cells the rewind contract reads: LinkWalkMkCr.v link_guard_got / link_guard_val.

   Proves function mark_quietly (image A, the asan build), later arm. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkErrno LinkWalkErrnoInst LinkWalkSide LinkWalkMkTail LinkWalkMkCr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import mark_quietlyRw.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c mark_quietly_c mark_quietlyDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import mark_quietlyArg mark_quietlyRsm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- the entry state ---------------------------------------------------- *)
Definition mqa_gs_obj : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 29)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition mqa_gs_hi : YP09.region :=
  YP09.mkRegion (Some (A_HI 68)) (-0x52c) (-0x524) 0 0 [YP09.mkChunk (-0x52c) (CVal 8 (SOff 32 0))].
Definition mqa_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF 1 (2 ^ 64 - 1) 0);
           (A_OBJ 29, mkAF LA_G_SINK LA_G_SINK 0)] [] [].
Definition mqa_ss : sstate := mkSS AF_mark_quietly sr_atoms [stack_region 32; mqa_gs_obj] None mqa_facts.
Definition mqa_extra (sink : Z) : list word := [Z_to_bv 64 sink].
Definition mqa_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Ltac zrng := try change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); try change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32);
  try change (Z.of_N 8) with 8; try change (Z.of_N 4) with 4; lia.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.

Lemma mqa_vals : VAL (A_OBJ 29) = LA_G_SINK /\ VAL (A_HI 68) = 0x6303ec /\ BASE = 0x821cc /\
  pa_sigma LS___interceptor_trampoline_rewind = LA_W_REWIND /\ pa_sigma LS_reac_served_mark = REAC_SERVED_MARK_A.
Proof.
  split; [rewrite (lv_obj LV 29) by (unfold link_nobj; lia); reflexivity|].
  split; [rewrite (lv_hi LV 68) by (unfold link_nhi; lia); reflexivity|].
  split; [exact (lv_text LV)|].
  split; rewrite (lv_sigma LV); reflexivity.
Qed.

(* THE ENTRY STATE *)
Lemma mqa_entry : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) sink,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - 32 -> spZ regs <= sp0 ->
  au64_at SEGS (rdW W memc) LA_G_SINK sink -> 1 <= sink < 2 ^ 64 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (mqa_extra sink))) mqa_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_mark_quietly)) memc (seg_rom SEGS))).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs sink HJ H16 Hwlo Hwhi Hgs Hsk.
destruct HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct mqa_vals as (V29 & _ & _ & _ & _).
set (E := Eimg (Ereg regs (mqa_extra sink))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (mqa_extra sink)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 sink) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Eg : ew E (A_OBJ 29) = Z_to_bv 64 LA_G_SINK)
  by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V29; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VBv : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
rewrite restrict_mkst_fx. unfold mqa_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, mqa_gs_obj.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + fold E. rewrite (VBv _ _ Eg) by (unfold LA_G_SINK; lia).
    split; [unfold LA_G_SINK; lia|]. split; [unfold LA_G_SINK; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ LA_G_SINK 0 8 (SOff 32 0) sink);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |].
    rewrite Z.add_0_r. exact Hgs.
- apply pairwise_disjoint_of_extents.
  unfold stack_region, mqa_gs_obj, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  fold E. rewrite (VBv _ _ Eg) by (unfold LA_G_SINK; lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold LA_G_SINK.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [mqa_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite Usp, E32, Eg.
  rewrite !unsigned_lit_small by (unfold LA_G_SINK; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold LA_G_SINK.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* keeping some of the regions of a symbolic state *)
Lemma st_ok_pi_keep : forall E ss ms rs,
  st_ok_pi SEGS VAL E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof. intros E ss ms rs HS Hs Hw. exact (st_ok_submem SEGS E (abs_ss VAL ss) ms rs HS Hs Hw). Qed.

(* link's memory FILE with k bytes pending is a fact about the block's first AMF_ZEROED bytes only *)
Lemma amf_k_agree : forall (m m' : word -> option byte) f k,
  (forall a, f <= a < f + AMF_ZEROED -> mbyte SEGS m' a = mbyte SEGS m a) ->
  LinkMfDefs.amf_k SEGS link_amf m f k -> LinkMfDefs.amf_k SEGS link_amf m' f k.
Proof.
  intros m m' f k HA.
  assert (Hv : forall off n v, 0 <=? off = true -> off + Z.of_nat n <=? 272 = true ->
            val_mem SEGS m (f + off) n v -> val_mem SEGS m' (f + off) n v).
  { intros off n v H0 H1 H kk Hkk. apply Z.leb_le in H0, H1.
    rewrite HA by (unfold AMF_ZEROED; lia). exact (H kk Hkk). }
  intros ((Hp0 & Hp1 & Hp2 & Hst & Hfl & Hom & Hwi & Hck) & Hwn).
  unfold amemfile_static, amemfile_flags, amemfile_omode, amemfile_window, amemfile_cookie,
    LinkMfDefs.amf_win in *.
  unfold AMF_COOKIE, AMF_BUF, AMF_BUFSIZ in *.
  split; [split; [exact Hp0 | split; [exact Hp1 | split; [exact Hp2 | split; [|split; [|split; [|split]]]]]] |].
  - repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat split; (apply Hv; [reflexivity | reflexivity | assumption]).
  - destruct Hfl as [Hfl | Hfl]; [left | right]; (apply Hv; [reflexivity | reflexivity | exact Hfl]).
  - destruct Hom as [Hom | Hom]; [left | right]; (apply Hv; [reflexivity | reflexivity | exact Hom]).
  - destruct Hwi as (W8 & W16 & [(Wa & Wb & Wc) | (kq & Hkq & Wa & Wb & Wc)]);
      (split; [apply Hv; [reflexivity | reflexivity | assumption]
              | split; [apply Hv; [reflexivity | reflexivity | assumption] |]]).
    + left. repeat split; (apply Hv; [reflexivity | reflexivity | assumption]).
    + right. exists kq. split; [exact Hkq|]. repeat split; (apply Hv; [reflexivity | reflexivity | assumption]).
  - destruct Hck as (pos & len & Hpl & Hls & Hc1 & Hc2). exists pos, len.
    split; [exact Hpl|]. split; [exact Hls|]. split; (apply Hv; [reflexivity | reflexivity | assumption]).
  - destruct Hwn as [(Hk0 & Wa & Wb & Wc) | (Hk & Wa & Wb & Wc)]; [left | right];
      (split; [assumption|]); repeat split; (apply Hv; [reflexivity | reflexivity | assumption]).
Qed.

(* ==========================================================================
   The walk of the later arm
   ========================================================================== *)
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.
Hypothesis RW : arewind_mf_realizes SEGS B link_amf LA_W_REWIND.
Hypothesis RSM : reac_served_mark_acontract SK SEGS PCAP_RLO PCAP_RHI B.

(* the run's write permission: its frame *)
Ltac mqa_awr :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_x_cons;
    [ intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first
      [ lia
      | lazymatch type of Ha with context [ew _ 2%nat] =>
          match goal with U : bv_unsigned (ew _ 2%nat) = _ |- _ => rewrite U in Ha end;
          left; split; [left; lia | lia] end ]
    | ]);
  apply awr_ok_x_nil.

(* the bytes a run left as they were: every byte outside the frame (YC4b.v kept_of_frame) *)
Ltac mqa_kept HFr sp UN :=
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => sp - 32 <= a < sp) HFr
    ltac:(intros ?bb ?wlo ?whi ?aa ?Hin ?Hrr; vm_compute in Hin;
          repeat (destruct Hin as [?Hq | Hin];
                  [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbv beta;
                   first
                   [ clear - Hrr; lia
                   | match goal with U : bv_unsigned (ew _ 2%nat) = _ |- _ =>
                       rewrite U in Hrr; clear - Hrr; lia end ] |]);
          destruct Hin)) as UN.

(* chain a run's kept bytes and growth onto those since the entry *)
Ltac mqa_fold UN HGc UNk HG W memc sp :=
  lazymatch type of UNk with forall a, _ -> _ -> aview _ _ ?mN a = aview _ _ ?mO a =>
    let UN' := fresh "UN" in
    assert (UN' : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 32 <= a < sp) ->
              aview SEGS (w_H W) mN a = aview SEGS (w_H W) memc a)
      by (intros ?a ?Ha ?Hz; rewrite (UNk _ Ha Hz); exact (UN _ Ha Hz));
    clear UN UNk; rename UN' into UN end;
  lazymatch type of HG with mem_grows _ (mrestrict _ ?mN) =>
    let HG' := fresh "HGc" in
    assert (HG' : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mN))
      by (eapply mem_grows_trans; [exact HGc | exact HG]);
    clear HGc HG; rename HG' into HGc end.

Theorem mark_quietly_aproof_again : mark_quietly_acontract_again SK SEGS PCAP_RLO PCAP_RHI B.
Proof.
unfold mark_quietly_acontract_again, aleaf_fx.
intros sink G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HRD HFRM HP.
pose proof HA as HA0.
destruct HA as (HJ & HGX & HROD & Hret & Hra4 & Hgp & Htp & H16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hnro).
pose proof HP as HP0.
destruct HP as (HinF & Hgs & Hsk0 & Hcom & (kf & Hmf) & Hsay & Hofl & Hblk & Hsdw & Hsdr & Hsda & Hsdh).
assert (HK : MARK_QUIETLY_AK = 24608) by reflexivity.
assert (HKR : REAC_SERVED_MARK_AK = 9504) by reflexivity.
assert (HARW : ARW_STK = 4256) by reflexivity.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJ as HJ0.
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct mqa_vals as (V29 & V68 & VB & Vrw & Vrsm).
pose proof (pal_env B TL) as ENV. pose proof (proj1 ENV) as [Ee0 Ee1].
pose proof (link_errno_not_static B TB) as ERRF.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc sink AMF_BLOCK HAR HinF) as (Hsk16 & Hsk4096 & Hskc & _).
assert (Hreq : 1304 <= req_size AMF_BLOCK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hskr : 1 <= sink < 2 ^ 64) by (clear - Hsk4096 Hskc Hreq C1b; lia).
assert (Hceil0 : alloc_ceiling <= spZ regs - MARK_QUIETLY_AK) by (clear - Hwlo Hceil Hslo; lia).
pose proof (mqa_entry G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs sink HJ H16
  ltac:(rewrite HK in Hwlo; clear - Hwlo; lia) Hwhi Hgs Hskr) as HS.
replace (cfg_at SEGS MARK_QUIETLY_A regs memc mdc)
  with (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_mark_quietly)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, MARK_QUIETLY_A, AF_mark_quietly; rewrite VB; reflexivity).
remember (Eimg (Ereg regs (mqa_extra sink))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (mqa_extra sink)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 sink) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E388 : ew E (A_HI 68) = Z_to_bv 64 0x6303ec)
  by (subst E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); rewrite V68; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (mqa_extra sink)) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U388 : bv_unsigned (ew E (A_HI 68)) = 0x6303ec) by (rewrite E388; apply unsigned_lit_small; lia).
clear HEdef EL.
assert (SHOK : sh_ok SEGS (SLit SHADOW_OFF) [] E (mrestrict (w_H W) memc)) by constructor.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
          aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by reflexivity.
assert (HGc : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
pose proof (paj_run_x SK B LAWS G HGX XO OUT) as RUN.
(* run 1, +0x00 .. +0x4c: the frame, s0 / s1 / s2, g_sink through A_OBJ 29, `bnez a1` taken *)
paj_run_tok RUN HS HJ SHOK mqa_span.
{ mqa_awr. }
mqa_kept HFr (spZ regs) UNk. clear HF HFr. mqa_fold UN HGc UNk HG W memc (spZ regs).
(* the run stopped at +0x4c `ld a0, -0x52c(s2)`: g_sink again, through the base atom A_HI 68; the region of
   g_sink is re-based on it *)
lazymatch type of HS with st_ok_pi _ _ _ (mkSS ?pc1 ?rg1 [?r0; ?r1] ?rv1 ?fc1) (restrict _ ?ms1) =>
  pose (S1 := mkSS pc1 rg1 [r0] rv1 fc1);
  assert (HSk : st_ok_pi SEGS VAL E S1 (restrict (w_H W) ms1))
    by (exact (st_ok_pi_keep E (mkSS pc1 rg1 [r0; r1] rv1 fc1) (restrict (w_H W) ms1) [r0] HS
          ltac:(cbn [ss_mem]; submem_tac) ltac:(vm_compute; reflexivity)));
  assert (HS2 : st_ok_pi SEGS VAL E (add_atom (mkSS (ss_pc S1) (ss_regs S1) (mqa_gs_hi :: ss_mem S1)
                  (ss_resv S1) (ss_facts S1)) (A_HI 68) (mkAF 0x6303ec 0x6303ec 0)) (restrict (w_H W) ms1));
  [ apply st_ok_pi_add_fact;
    [ apply st_ok_pi_add_region;
      [ exact HSk
      | vm_compute; reflexivity
      | unfold region_ok, mqa_gs_hi;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
        rewrite U388; split; [lia|]; split; [lia|]; split; [intros ?o ?Ho; lia|];
        constructor; [|constructor];
        apply (chunk_ok_val SEGS E _ 0x6303ec (-0x52c) 8 (SOff 32 0) sink);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |];
        replace (0x6303ec + -0x52c) with LA_G_SINK by (unfold LA_G_SINK; lia);
        change (N.to_nat 8) with 8%nat; cbn [ms_mem restrict];
        intros kk Hkk;
        rewrite (mbyte_of_aview SEGS _ _ _ _ _ (UN (LA_G_SINK + Z.of_nat kk)
                   ltac:(unfold LA_G_SINK; clear - Hkk; lia)
                   ltac:(unfold LA_G_SINK; clear - Hkk Hceil0 C1a HK; lia)));
        exact (Hgs kk Hkk)
      | apply all_disjoint_of_extents; unfold mqa_gs_hi, extent_of_region, S1;
        cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val];
        repeat match goal with U : bv_unsigned (ew _ ?n) = _ |- context [ew _ ?n] => rewrite U end;
        cbn [zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia ]
    | unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U388; rewrite Z.pow_0_r, Z.mod_1_r; lia ]
  | ];
  clear HS HSk; rename ms1 into msA
end.
lazymatch type of HS2 with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS2 end.
(* run 2, +0x4c .. +0x50: a0 := sink, the call of wrapper_rewind *)
paj_run_tok RUN HS2 HJ SHOK mqa_span.
{ mqa_awr. }
mqa_kept HFr (spZ regs) UNk. clear HF HFr. mqa_fold UN HGc UNk HG W memc (spZ regs).
rename HS2 into HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into ms2 end.
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (10%bv : bv 5) R10.
rewrite Usp in R2. rewrite E3 in R3. rewrite E4 in R4. rewrite E32 in R10.
assert (Usp2 : spZ (ms_regs ms2) = spZ regs - 32)
  by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; rewrite HK in Hceil0; lia).
(* the rewind: its premises, then its lift onto the journal *)
destruct (mqa_rw_args B LAWS TB HSEGS sink lyc Sc W memc (ms_mem ms2) mdc regs (ms_regs ms2)
  G XO OUT STK sp0 FP ly S own HAR Hceil0 HP0 Hajw UN HGc Usp2)
  as (kk & fl & om & wend & wpos & wbase & pos & len & pb & Hk1 & Hdyn1 & Hpend1 & Hlen1 & Hbuf1 & Haf1 & Has1).
pose proof HJ as (_ & _ & (memS2 & HJ2i & _) & _). pose proof HJ2i as (HAR2 & _).
assert (Hg1 : rdword (aview SEGS (w_H W) (ms_mem ms2)) LinkMfDefs.LA_GOT_GUARD = Some LinkMfDefs.LA_GUARD)
  by (eapply link_guard_got; eassumption).
assert (Hg2 : exists g, rdword (aview SEGS (w_H W) (ms_mem ms2)) LinkMfDefs.LA_GUARD = Some g)
  by (eapply link_guard_val; eassumption).
eapply SRr_bind.
{ apply (aj_gx_rewind_at SK SEGS B LAWS pa_segs_low ENV ERRF (pa_sigma LS___interceptor_trampoline_rewind)
    ltac:(rewrite Vrw; exact RW)
    G XO OUT W (ms_regs ms2) (ms_mem ms2) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (getr (ms_regs ms2) 1)
    sink kk fl om wend wpos wbase pos len pb HGX HJ);
  [ rewrite Usp2; lia
  | rewrite Usp2, HARW; rewrite HK in Hwlo; lia
  | rewrite Usp2; lia
  | rewrite R3; exact Hgp
  | rewrite R4; exact Htp
  | reflexivity
  | rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite R10; reflexivity
  | exact HinF | exact Hk1 | exact Hdyn1 | exact Hpend1 | exact Hlen1 | exact Hbuf1
  | exact Hg1 | exact Hg2 | exact Haf1 | exact Has1 ]. }
cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hsm3 & Hk3 & Hdyn3 & UN3 & Hgr3 & Hwin3).
assert (Hab : amf_buf link_amf = LA_G_SAID /\ amf_size link_amf = SAID_SIZE) by (split; reflexivity).
pose proof (ts_errno B TB) as HerrB.
assert (Herrv : TFIB_ERRNO = 0x631b6c) by reflexivity.
jafter_call_keep_pi HS 40%nat regs3 (mrestrict (w_H W) mem3) HP3 [1]%nat HS3.
match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil]. split.
  - intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite Usp in Ha.
    apply (mbyte_of_aview SEGS). destruct Hab as [Hab1 Hab2].
    apply UN3; rewrite ?Usp2, ?HARW, ?Hab1, ?Hab2, ?HerrB, ?Herrv;
      unfold LA_G_SAID, SAID_SIZE, AMF_ZEROED in *; rewrite ?HK in *; lia.
  - intros a Ha Hw. apply (writable_kept (segs := SEGS) (w_H W) (ms_mem ms2) mem3); [exact (Hgr3 a) | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E 40 (map (getr regs3) CLOB)) as E' eqn:HE' in HS.
assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall n, (n < 40)%nat -> ew E' n = ew E n) by (intros n Hn; rewrite HE'; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE' : env_agree 32 (Ereg regs (mqa_extra sink)) E') by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
assert (E1' : ew E' 1 = getr regs 1) by (rewrite OLD by lia; exact E1).
assert (E10' : ew E' 10 = getr regs 10) by (rewrite OLD by lia; exact E10).
assert (E11' : ew E' 11 = getr regs 11) by (rewrite OLD by lia; exact E11).
clear HE' OLD.
assert (SHOK3 : sh_ok SEGS (SLit SHADOW_OFF) [] E' (mrestrict (w_H W) mem3)) by constructor.
(* the agreement since the entry, outside mqa_X *)
assert (UNX : forall a, 0 <= a < 2 ^ 64 -> ~ mqa_X B (spZ regs) sink a ->
          aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) memc a).
{ intros a Ha Hx. unfold mqa_X in Hx. destruct Hab as [Hab1 Hab2].
  rewrite (UN3 a Ha); [| rewrite Usp2, HARW; intros Hc; apply Hx; left; rewrite HK; lia
                       | intros Hc; apply Hx; right; left; exact Hc
                       | rewrite Hab1, Hab2; intros Hc; apply Hx; right; right; left; exact Hc
                       | intros Hc; apply Hx; right; right; right; exact Hc].
  apply UN; [exact Ha | intros Hc; apply Hx; left; rewrite HK; lia]. }
assert (HGX3 : forall a, apresent (w_H W) memc a -> apresent (w_H W) mem3 a)
  by (intros a Hp; apply Hgr3; exact (apresent_grows _ _ _ _ HGc Hp)).
clear UN HGc.
(* run 3, +0x54 .. +0x70: a0 := s1, a1 := s0, the reloads, the pop, the tail jump to reac_served_mark *)
rewrite R1.
paj_run_tok RUN HS HJ3 SHOK3 mqa_span.
{ mqa_awr. }
mqa_kept HFr (spZ regs) UNk. clear HF HFr.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into ms4 end.
assert (UNj : forall a, 0 <= a < 2 ^ 64 -> ~ mqa_X B (spZ regs) sink a ->
          aview SEGS (w_H W) (ms_mem ms4) a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hx; rewrite (UNk a Ha ltac:(intros Hc; apply Hx; left; rewrite HK; lia)); exact (UNX a Ha Hx)).
assert (HGj : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms4) a)
  by (intros a Hp; exact (apresent_grows _ _ _ _ HG (HGX3 a Hp))).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (E2' : ew E' 2 = getr regs 2).
{ apply bv_eq. rewrite Usp'. reflexivity. }
rewrite E1' in Q1. rewrite E2' in Q2. rewrite E10' in Q10. rewrite E11' in Q11.
assert (Hspj : spZ (ms_regs ms4) = spZ regs) by (unfold spZ; rewrite Q2; reflexivity).
assert (Ha0j : aarg (ms_regs ms4) 0 = aarg regs 0)
  by (unfold aarg, argZ; replace (Z_to_bv 5 (10 + 0)) with (10%bv : bv 5) by (apply bv_eq; reflexivity);
      rewrite Q10; reflexivity).
assert (Ha1j : aarg (ms_regs ms4) 1 = aarg regs 1)
  by (unfold aarg, argZ; replace (Z_to_bv 5 (10 + 1)) with (11%bv : bv 5) by (apply bv_eq; reflexivity);
      rewrite Q11; reflexivity).
pose proof (aregs_preserved_of_st_ok SEGS _ E' _ _ regs (mqa_extra sink) HS HAE' ltac:(vm_compute; reflexivity)) as HPj.
pose proof HJ3 as (_ & _ & (memS4 & HJ4i & _) & _).
pose proof HJ4i as (HAR4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
(* the FILE after the rewind, at the jump (run 3 wrote only its frame) *)
assert (Hkj : LinkMfDefs.amf_k SEGS link_amf (rdW W (ms_mem ms4)) sink 0).
{ apply (amf_k_agree (rdW W mem3)); [|exact Hk3].
  intros a Ha. apply (mbyte_of_aview SEGS). apply UNk; [unfold AMF_ZEROED in Ha; lia|].
  unfold AMF_ZEROED in Ha. rewrite HK in Hceil0. lia. }
(* the inclusion of reac_served_mark's write set in this function's *)
assert (HE21 : forall a, inFP (reac_served_mark_awr sink (ms_regs ms4) (rdW W (ms_mem ms4))) a ->
                 inFP (mark_quietly_awr_again sink regs (rdW W memc)) a).
{ intros a (r & Hr & Hra). unfold reac_served_mark_awr in Hr. rewrite Ha0j in Hr.
  exists r. split; [|exact Hra]. unfold mark_quietly_awr_again. cbn [In] in Hr |- *.
  destruct Hr as [<- | [<- | [<- | []]]]; tauto. }
assert (Hagj : mqa_agree B (spZ regs) sink W memc (ms_mem ms4))
  by (split; [exact UNj | exact (mem_grows_of_apresent _ _ _ HGj)]).
rewrite Vrsm.
apply (apostF_tail SK SEGS B MARK_QUIETLY_AK 0 _ REAC_SERVED_MARK_AK 0
  (fun a => inFP (reac_served_mark_awr sink (ms_regs ms4) (rdW W (ms_mem ms4))) a)
  G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Sc W (ms_mem ms4)
  (with_vm_backing (m_vm_lazy md3) mat1 md3) k (ms_regs ms4) _
  (fun ly2 S2 W2 regs2 mem2 md2 => S2 = set_fs (st_fs S2) Sc /\
     Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
     reac_served_mark_apost SEGS sink (ms_regs ms4) (rdW W (ms_mem ms4)) regs2 (rdW W2 mem2))).
- reflexivity.
- exact Q1.
- exact HPj.
- rewrite Hspj, HK, HKR. lia.
- rewrite Hspj. lia.
- exact Hceil0.
- reflexivity.
- repeat rewrite (proj1 (wvb_fds_fs _ _ _)). rewrite (same_but_materialized_wvb _ _ Hsm3).
  repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
- repeat rewrite (proj2 (wvb_fds_fs _ _ _)). rewrite (same_but_materialized_wvb _ _ Hsm3).
  repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
- eapply mqa_akept with (mdc := mdc); try eassumption.
  intros a Ha. apply Hpres4. rewrite HK in Hwlo, Ha. lia.
- eapply (ashadow_kept_AR SK); first [exact LAWS | exact pa_segs_low | exact HAR | exact HAR4].
- intros b n Hb. exact Hb.
- exact HE21.
- intros ly2 S2 W2 regs2 mem2 md2 Hle HK2 (Hs2 & Hperm & Hpost).
  split; [exact Hs2|]. split; [exact Hperm|].
  eapply mqa_q with (mdc := mdc) (memc := memc) (regs := regs); eassumption.
-
  apply (RSM sink G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms4) _ k (ms_regs ms4)).
  + split; [exact HJ3|].
    split; [exact HGX|].
    split; [eapply mqa_arodata with (sink := sink) (lyc := lyc) (Sc := Sc) (memc := memc) (mdc := mdc) (regs := regs);
            eassumption|].
    split; [rewrite Q1; exact Hret|].
    split; [unfold raZ; rewrite Q1; exact Hra4|].
    split; [pose proof (HPj 3 ltac:(unfold acallee_saved; lia)) as G3;
            replace (Z_to_bv 5 3) with (3%bv : bv 5) in G3 by (apply bv_eq; reflexivity);
            rewrite G3; exact Hgp|].
    split; [pose proof (HPj 4 ltac:(unfold acallee_saved; lia)) as G4;
            replace (Z_to_bv 5 4) with (4%bv : bv 5) in G4 by (apply bv_eq; reflexivity);
            rewrite G4; exact Htp|].
    split; [rewrite Hspj; exact H16|].
    split; [rewrite Hspj, HKR; rewrite HK in Hwlo; lia|].
    split; [rewrite Hspj; exact Hwhi|].
    split; [exact Hev|].
    split; [exact Hside|].
    split; [intros a Ha; apply Hajw; apply HE21; exact Ha|].
    intros a Ha; apply Hnro; apply HE21; exact Ha.
  + eapply mqa_rsm_rd with (lyc := lyc) (Sc := Sc) (memc := memc) (mdc := mdc) (regs := regs); eassumption.
  + exact HFRM.
  + eapply mqa_rsm_pre with (memc := memc) (mdc := mdc) (regs := regs); eassumption.
Qed.

End w.

About mark_quietly_aproof_again.
Print Assumptions mark_quietly_aproof_again.
