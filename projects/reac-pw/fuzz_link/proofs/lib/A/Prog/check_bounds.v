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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_entry.v; 281 of its 350 lines of code are new or changed and 656 lines of the source are left out. *)
(* check_bounds on image A (fuzz_link.asan 0x868ac, listing offset AF_check_bounds = 0x46e0; listing
   (internal path) (internal record, sha256 fbb55f0071c4)): the walk of its contract
   lib/A/Prog/check_bounds_c.v `check_bounds_acontract` (link_amem.v `aleaf_rd`, K = 32 + ESTACK = 4128, EV 0,
   SIDE [], write set []).

   +0x00..+0x10 push the 32-byte frame (ra, s0, s1, s2); +0x14..+0x24 s0 := cap, s2 := the shadow base (the .got word
   and its cell), s1 := buf; +0x28..+0x30 wrapper_memchr(buf, 0, cap) (0x43060), lifted by LinkWalkMemchr.v
   aj_gx_memchrM_at; +0x34 `beqz a0` to the abort path: refuted, since bs holds a NUL among the cap bytes memchr
   reads (cb_found); +0x38..+0x48 the instrumented check of buf + cap (the shadow entry cb_SH over atom 33, which
   the alias of cb_facts names: 33 = buf + cap = s1 + s0); +0x4c..+0x54 the guard byte 0x5a (the region cb_guard)
   makes `bne` fall through; +0x58..+0x6c restore, pop, ret. The run and memchr write only [sp - 4128, sp)
   (LinkWalkNoWrite.v), so the Post (True) closes with lf_finish0.

   Section hypotheses: LAWS, TL (PALib), LV (LinkVals) are the image instance's facts; MEMCHR (the memchr wrapper's
   contract, MemchrDef.v amemchr_realizesM at memchr's word constants [0x10360, 0x10380)) is discharged on the image
   by lib/A/Rt/RtClosed.v `link_memchrM_closed`; MC_RO (those 32 bytes are read-only image bytes the runtime does not
   own) by LinkWalkMemchr.v `link_mc_ro`; both in check_bounds_aproof_img.

   Proves check_bounds (kind: function proof). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNoWrite LinkWalkMemchr check_bounds_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import MemchrDef ConstsViewDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtClosed.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the entry state: the frame, the .got word of the shadow base and its cell; atom 33 = buf + cap (the alias) *)
Definition cb_aE : sv := SAlu ALU_ADD (SOff 10 0) (SOff 11 0).
Definition cb_regions : smem := [stack_region 32; got_regionP; bcell_regionP 32].
Definition cb_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 1 (2 ^ 47 - 1) 0)] []
    [(cb_aE, SOff 33 0)].
Definition cb_ss : sstate := mkSS AF_check_bounds sr_atoms cb_regions None cb_facts.
Definition cb_extra (regs : bvmap 5 word) : list word := map (Z_to_bv 64) [SB; aarg regs 0 + aarg regs 1].
(* after memchr: the guard byte at atom 33, and its shadow entry *)
Definition cb_guard : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 1 1 [YP09.mkChunk 0 (CVal 1 (SLit 0x5a))].
Definition cb_SH : list shent := [mkSHE 33 0 1].

Ltac zrng := try change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); try change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32);
  try change (2 ^ (8 * Z.of_N 1)) with (2 ^ 8);
  try change (Z.of_N 8) with 8; try change (Z.of_N 4) with 4; try change (Z.of_N 1) with 1; lia.

Lemma cb_grows_of_present : forall H m m',
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
intros H m m' Hp x Hx. unfold mrestrict in *. destruct (H x) eqn:Eh; [exact Hx|].
destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
assert (Ha : apresent H m (bv_unsigned x)).
{ unfold apresent. rewrite Z_to_bv_bv_unsigned. split; [exact Eh | exists b; exact Em]. }
destruct (Hp _ Ha) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

Lemma cb_shadow_low : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_addr x < 2 ^ 46 - 2 ^ 20.
Proof. intros x Hx. unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. Qed.

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
Hypothesis MEMCHR : amemchr_realizesM SEGS B 0x10360 0x10380 (pa_sigma LS___interceptor_trampoline_memchr).
Hypothesis MC_RO : forall a, 0x10360 <= a < 0x10380 -> in_rom SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4).

Lemma cb_vals : VAL (A_OBJ 1) = 0xa19d0 /\ VAL (A_OBJ 64) = 0xaa438 /\ BASE = 0x821cc.
Proof.
  split; [rewrite (lv_obj LV 1) by (unfold link_nobj; lia); reflexivity|].
  split; [rewrite (lv_obj LV 64) by (unfold link_nobj; lia); reflexivity|].
  exact (lv_text LV).
Qed.

(* THE ENTRY STATE *)
Lemma cb_entry : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - 32 -> spZ regs <= sp0 ->
  1 <= aarg regs 0 + aarg regs 1 <= 2 ^ 47 - 1 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (cb_extra regs))) cb_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_bounds)) memc (seg_rom SEGS))).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ H16 Hwlo Hwhi Hbc.
destruct HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL) in Kgot. rewrite (pal_cell B TL) in Kgot, Kcell.
destruct cb_vals as (V1 & V64 & VB).
rewrite V1, V64 in Kgot. rewrite V64 in Kcell.
pose proof (bv_unsigned_in_range 64 (getr regs 10)) as R10. pose proof (bv_unsigned_in_range 64 (getr regs 11)) as R11.
change (bv_modulus 64) with (2 ^ 64) in R10, R11.
assert (A0 : aarg regs 0 = bv_unsigned (getr regs 10)) by reflexivity.
assert (A1 : aarg regs 1 = bv_unsigned (getr regs 11)) by reflexivity.
set (E := Eimg (Ereg regs (cb_extra regs))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cb_extra regs)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (aarg regs 0 + aarg regs 1))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 0xa19d0)
  by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V1; reflexivity).
assert (Ecell : ew E (A_OBJ 64) = Z_to_bv 64 0xaa438)
  by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V64; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VBv : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
rewrite restrict_mkst_fx. unfold cb_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold cb_regions, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + fold E. rewrite (VBv _ _ Egot) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xa19d0 0 8 (SOff (A_OBJ 64) 0) 0xaa438);
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
  + fold E. rewrite (VBv _ _ Ecell) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xaa438 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zrng | zrng |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
- apply pairwise_disjoint_of_extents.
  unfold cb_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  fold E. rewrite (VBv _ _ Egot), (VBv _ _ Ecell) by lia.
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [cb_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite Usp, E32, E33.
    rewrite !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
  + cbn [cb_facts f_alias alias_ok]. split; [|exact I]. fold E.
    apply bv_eq. change (U E cb_aE = U E (SOff 33 0)). unfold cb_aE.
    rewrite U_SAlu, !lf_U_reg, E10, E11, E33. cbn [zalu_raw].
    rewrite unsigned_lit_small by lia. rewrite <- A0, <- A1. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.

Theorem check_bounds_aproof : forall rlo rhi, check_bounds_acontract SK SEGS rlo rhi B.
Proof.
intros rlo rhi. unfold check_bounds_acontract, aleaf_rd, check_bounds_apost, check_bounds_awr.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HRd HPre.
destruct HA as (HJ & HGX & HROD & Hret & Hra4 & Hgp & Htp & H16 & Hwlo & Hwhi & Hev & Hside & Hajw & _).
destruct HPre as (bs & Hb0 & Hcap & [[Hab _] Hbl] & HIn & Hamr & Hra & Hhull & Hapf).
unfold CHECK_BOUNDS_AK, CHECK_BOUNDS_AFRAME in *. change ESTACK with 4096 in *.
unfold YK0s.ret_ok in Hret. unfold apart_frame in Hapf.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJ as HJ0.
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (bv_unsigned_in_range 64 (getr regs 10)) as R10r. pose proof (bv_unsigned_in_range 64 (getr regs 11)) as R11r.
change (bv_modulus 64) with (2 ^ 64) in R10r, R11r.
assert (A0 : aarg regs 0 = bv_unsigned (getr regs 10)) by reflexivity.
assert (A1 : aarg regs 1 = bv_unsigned (getr regs 11)) by reflexivity.
set (buf := aarg regs 0) in *. set (cap := aarg regs 1) in *.
assert (Hbufp : 0 < buf) by lia.
assert (Hbc : 1 <= buf + cap <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
destruct cb_vals as (V1 & V64 & VB).
pose proof (cb_entry G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ H16 ltac:(lia) Hwhi Hbc) as HS.
replace (cfg_at SEGS CHECK_BOUNDS_A regs memc mdc)
  with (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_check_bounds)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, CHECK_BOUNDS_A, AF_check_bounds; rewrite VB; reflexivity).
remember (Eimg (Ereg regs (cb_extra regs))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cb_extra regs)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (buf + cap)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (HAE : env_agree 32 (Ereg regs (cb_extra regs)) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HEdef EL.
(* the bytes of the buffer and the guard, as memchr and the code read them *)
assert (Hbyte : forall i, 0 <= i <= cap -> exists b, mbyte SEGS (rdW W memc) (buf + i) = Some b /\
          (i = cap -> b = zb GUARD_BYTE)).
{ intros i Hi. destruct Hab as (_ & _ & Hn).
  pose proof (Hn (Z.to_nat i) ltac:(rewrite length_app; cbn [length]; lia)) as Hi'.
  rewrite Z2Nat.id in Hi' by lia. rewrite Hi'.
  destruct (Z.eq_dec i cap) as [->|Hne].
  - rewrite nth_error_app2 by lia. replace (Z.to_nat cap - length bs)%nat with 0%nat by lia.
    exists (zb GUARD_BYTE). split; [reflexivity | intros _; reflexivity].
  - rewrite nth_error_app1 by lia. destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Eb.
    + exists b. split; [reflexivity | intros H; lia].
    + apply nth_error_None in Eb. lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) memc)) by constructor.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ lf_Zs 4128 (spZ regs) a ->
          aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by reflexivity.
assert (HGc : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
pose proof (paj_run_x SK B LAWS G HGX XO OUT) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
(* +0x00 .. +0x30: the frame, the shadow base, the arguments of memchr *)
paj_run_tok RUN HS HJ SHOK Bspan; [lf_awr |].
lf_kept HFr W 4128 (spZ regs) UNk. clear HF HFr. lf_fold UN HGc UNk HG W memc 4128 (spZ regs).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into ms1 end.
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (12%bv : bv 5) R12.
rewrite Usp in R2.
assert (Usp1 : spZ (ms_regs ms1) = spZ regs - 32)
  by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
(* bytes outside [sp - 4128, sp) at the call are the entry's *)
assert (Hout : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 4128 <= a < spZ regs) ->
          aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply UN; [exact Ha | unfold lf_Zs; exact Hn]).
assert (Hshout : forall x, 0 <= x < 2 ^ 47 -> ~ (spZ regs - 4128 <= shadow_addr x < spZ regs))
  by (intros x Hx; pose proof (cb_shadow_low x Hx); lia).
eapply SRr_bind.
{ eapply (aj_gx_memchrM_at SK SEGS B LAWS pa_segs_low 0x10360 0x10380 _ MEMCHR G XO OUT W (ms_regs ms1)
    (ms_mem ms1) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k buf 0 cap _ HGX HJ).
  - rewrite Usp1. lia.
  - rewrite Usp1. change ESTACK with 4096. lia.
  - rewrite Usp1. lia.
  - rewrite R3, E3. exact Hgp.
  - rewrite R4, E4. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; lia.
  - rewrite R10, E10. unfold w64. rewrite A0. symmetry. apply Z_to_bv_bv_unsigned.
  - rewrite R11. reflexivity.
  - rewrite R12, E11. unfold w64. rewrite A1. symmetry. apply Z_to_bv_bv_unsigned.
  - lia.
  - lia.
  - exact Hbufp.
  - lia.
  - intros a Ha. rewrite Usp1. change ESTACK with 4096. split.
    + rewrite Hout by lia. rewrite <- (ard_aview SEGS). unfold ard.
      destruct (Hbyte (a - buf) ltac:(lia)) as (b & Hb & _). replace (buf + (a - buf)) with a in Hb by lia.
      rewrite Hb. discriminate.
    + lia.
  - unfold amem_range in *. exact Hamr.
  - apply (ra_shadow_eq (ard SEGS (rdW W memc))); [intros x Hx; apply Hra; lia|].
    intros x Hx. rewrite (ard_aview SEGS). apply Hout; [pose proof (cb_shadow_low x ltac:(lia)); lia | apply Hshout; lia].
  - intros Hn s Hs. pose proof (cb_shadow_low buf ltac:(lia)) as S0. pose proof (cb_shadow_low (buf + cap - 1) ltac:(lia)) as S1.
    rewrite Hout; [rewrite <- (ard_aview SEGS); exact (Hhull s Hs) | |].
    + unfold shadow_addr, SHADOW_OFF in *. lia.
    + unfold shadow_addr, SHADOW_OFF in *. lia.
  - apply (consts_view_keep SEGS 0x10360 0x10380 W memc).
    + exact (aconsts_of_aro SEGS B rlo rhi W memc 0x10360 0x10380 MC_RO HROD).
    + intros a Ha. apply Hout; lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (kk & Hfb & H10) & Hkeep & Hpres2 & Hsm).
(* memchr finds the NUL: kk < cap *)
assert (Hkk : kk < cap).
{ destruct Hfb as (Hk0 & Hbefore & _). destruct (Z_lt_le_dec kk cap) as [H|H]; [exact H|].
  exfalso. apply In_nth_error in HIn as (i & Hi).
  assert (Hil : (i < length bs)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  destruct (Hbefore (Z.of_nat i) ltac:(lia)) as (b & Hb & Hne).
  rewrite Hout in Hb by lia. rewrite <- (ard_aview SEGS) in Hb. unfold ard in Hb.
  destruct Hab as (_ & _ & Hn). rewrite (Hn i ltac:(rewrite length_app; cbn [length]; lia)) in Hb.
  rewrite nth_error_app1 in Hb by lia. rewrite Hi in Hb. cbn in Hb. injection Hb as <-. apply Hne. reflexivity. }
assert (HP2' : aregs_preserved (ms_regs ms1) regs2) by exact HP2.
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2' [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  unfold region_kept. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]. rewrite Usp. split.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hkeep; [lia|]. rewrite Usp1. change ESTACK with 4096. lia.
  - intros a Ha Hw. apply (writable_kept (segs := SEGS) (w_H W) (ms_mem ms1) mem2); [intros Hp; exact (Hpres2 _ Hp) | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall n, (n < 40)%nat -> ew E' n = ew E n) by (intros n Hn; rewrite HE'; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE' : env_agree 32 (Ereg regs (cb_extra regs)) E') by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (E1' : ew E' 1 = getr regs 1) by (rewrite OLD by lia; exact E1).
assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
assert (E32' : ew E' 32 = Z_to_bv 64 SB) by (rewrite OLD by lia; exact E32).
assert (E33' : ew E' 33 = Z_to_bv 64 (buf + cap)) by (rewrite OLD by lia; exact E33).
assert (E44 : ew E' 44 = getr regs2 10) by (rewrite HE'; reflexivity).
assert (Ug : bv_unsigned (ew E' 33) = buf + cap) by (rewrite E33'; apply unsigned_lit_small; lia).
clear HE' OLD.
(* the memory after memchr outside [sp - 4128, sp) is the entry's *)
assert (Hout2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 4128 <= a < spZ regs) ->
          aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a).
{ intros a Ha Hn. rewrite Hkeep; [apply Hout; assumption | exact Ha | rewrite Usp1; change ESTACK with 4096; lia]. }
assert (HGc2 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2))
  by (eapply mem_grows_trans; [exact HGc | apply cb_grows_of_present; exact Hpres2]).
clear UN HGc.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ lf_Zs 4128 (spZ regs) a ->
          aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hz; apply Hout2; [exact Ha | exact Hz]).
rename HGc2 into HGc.
(* the guard byte: a region at atom 33, and its shadow entry *)
lazymatch type of HS with st_ok_pi _ _ _ ?ss2 (restrict _ ?ms2) =>
  assert (HS3 : st_ok_pi SEGS VAL E' (mkSS (ss_pc ss2) (ss_regs ss2) (cb_guard :: ss_mem ss2) (ss_resv ss2) (ss_facts ss2))
             (restrict (w_H W) ms2))
end.
{ apply st_ok_pi_add_region; [exact HS | vm_compute; reflexivity | |].
  - unfold region_ok, cb_guard. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Ug. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E' _ (buf + cap) 0 1 (SLit 0x5a) 0x5a); [reflexivity | zrng | zrng |].
    intros j Hj. assert (j = 0%nat) by lia. subst j. cbn [ms_mem restrict mkst].
    change (Z.of_nat 0) with 0. rewrite !Z.add_0_r.
    destruct (Hbyte cap ltac:(lia)) as (b & Hb & Hg). rewrite (Hg eq_refl) in Hb.
    rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) memc mem2 (buf + cap)); [rewrite Hb; reflexivity|].
    apply Hout2; [lia | lia].
  - apply all_disjoint_of_extents. unfold cb_guard, extent_of_region.
    cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Ug, Usp'.
    cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia. }
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
assert (SHOK3 : sh_ok SEGS (SOff 32 0) cb_SH E' (mrestrict (w_H W) mem2)).
{ unfold cb_SH. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite (U_atom E' 32 SB E32') by (unfold SB; lia). rewrite (U_atom E' 33 (buf + cap) E33') by lia.
  rewrite ?Z.add_0_r, ?Z.sub_0_r. split.
  - rewrite <- (aview_rd_of SEGS). change SB with SHADOW_OFF.
    apply (ra_shadow_eq (ard SEGS (rdW W memc))); [intros x Hx; apply Hra; lia|].
    intros x Hx. rewrite (ard_aview SEGS). apply Hout2; [pose proof (cb_shadow_low x ltac:(lia)); lia | apply Hshout; lia].
  - intros a Ha. unfold amem_range, SB, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
clear SHOK.
(* +0x34 `beqz a0`: memchr's result is buf + kk, not 0 *)
psrr_branch_tok RUN BR HS SHOK3 Bspan.
- exfalso. rewrite branch_eq_U, lf_U_reg, U_SLit, E44, H10 in Hc.
  rewrite (proj2 (Z.ltb_lt kk cap) Hkk) in Hc. destruct Hfb as (Hk0 & _).
  unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia. change (zcanon 0) with 0 in Hc.
  apply Z.eqb_eq in Hc. lia.
- (* +0x38 .. +0x6c: the check of buf + cap, the guard, restore, pop, ret *)
  paj_run_tok RUN HS HJ2 SHOK3 Bspan; [lf_awr |].
  lf_kept HFr W 4128 (spZ regs) UNk. clear HF HFr. lf_fold UN HGc UNk HG W memc 4128 (spZ regs).
  lazymatch type of HS with st_ok_pi _ _ ?Ef _ _ =>
    assert (HAEf : env_agree 32 (Ereg regs (cb_extra regs)) Ef)
      by (split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE' nn Hnn) | exact (proj2 HAE')])
  end.
  lf_ret PI LAWS W regs (cb_extra regs) HS HAEf E1' Hret HJ0 HJ2 Hwlo Hwhi UN HGc.
Qed.
End w.

(* LAWS, MEMCHR and MC_RO discharged on the image's segments: lib/Reusable/YG0q.v AR_laws_ok, lib/A/Rt/RtClosed.v
   link_memchrM_closed and LinkWalkMemchr.v link_mc_ro, from the image's asyms record (lib/A/AF0m.v PcapSyms; on the
   image lib/A/AD2l.v PcapB_syms) *)
Section img. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
Context {PI : PAImg link_listing}.
Theorem check_bounds_aproof_img : forall B, PALib B -> LinkVals -> AF0m.PcapSyms B -> pa_segs = AB1v.tfibsegs ->
  forall rlo rhi, check_bounds_acontract SK pa_segs rlo rhi B.
Proof.
intros B TL LV TS Hsegs.
assert (LAWS : AR_laws pa_segs B) by (rewrite Hsegs; exact (YG0q.AR_laws_ok AB1v.tfibsegs B)).
apply (check_bounds_aproof SK B LAWS TL LV).
- rewrite (lv_sigma LV). cbn [link_sigma]. rewrite Hsegs. exact (RtClosed.link_memchrM_closed B TS).
- rewrite Hsegs. exact (link_mc_ro B TS).
Qed.
End img.

Print Assumptions check_bounds_aproof.
Print Assumptions check_bounds_aproof_img.
