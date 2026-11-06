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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_entry.v; 107 of its 168 lines of code are new or changed and 664 lines of the source are left out. *)
(* check_socket on image A (fuzz_link.asan 0x86734, listing offset AF_check_socket = 0x4568; listing
   (internal path) (internal record, sha256 4590cb3f5380)): the walk of its contract
   lib/A/Prog/check_socket_c.v `check_socket_acontract` (link_amem.v `aleaf`, K = 16, EV 0, SIDE [], write set []).

   +0x00..+0x04 push the 16-byte frame and save ra; +0x08..+0x14 a1 := g_nl + 0x40000; +0x18 lw open, +0x1c `bnez`;
   +0x20 lw opened, +0x24 lw closed, +0x28 `bne`; +0x2c..+0x34 lw misuse, +0x38 `bnez` (each branch to the abort
   path +0x48); +0x3c..+0x44 restore ra, pop, ret. The entry state (cs_ss) holds g_nl's four fields as the Pre gives
   them: open and misuse as the literal 0, opened and closed as the one atom 33. So the run decides the three
   branches itself and goes straight to the `ret`: the abort path is never reached. The run writes only the frame
   (LinkWalkNoWrite.v), so the Post (True) closes with lf_finish0.

   Section hypotheses: LAWS, LV (LinkVals) are the image instance's facts (LAWS is YG0q.AR_laws_ok at the image's
   segments: check_socket_aproof_img).

   Proves check_socket (kind: function proof). *)
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
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNoWrite LinkWalkNlk check_socket_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the entry state: the frame, and g_nl's four fields (read only) *)
Definition cs_nl : YP09.region := YP09.mkRegion (Some (A_OBJ 2)) 0x40214 0x40224 0x40224 0x40224
  [YP09.mkChunk 0x40214 (CVal 4 (SLit 0)); YP09.mkChunk 0x40218 (CVal 4 (SOff 33 0));
   YP09.mkChunk 0x4021c (CVal 4 (SOff 33 0)); YP09.mkChunk 0x40220 (CVal 4 (SLit 0))].
Definition cs_regions : smem := [stack_region 16; cs_nl].
Definition cs_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (A_OBJ 2, mkAF LA_G_NL LA_G_NL 0)] [] [].
Definition cs_ss : sstate := mkSS AF_check_socket sr_atoms cs_regions None cs_facts.
Definition cs_extra (bs : list byte) : list word := map (Z_to_bv 64) [SB; nk_opened bs].

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
Hypothesis LV : LinkVals.

Lemma cs_entry : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) bs,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - 16 -> spZ regs <= sp0 ->
  anlk_at SEGS (rdW W memc) LA_G_NL bs ->
  nk_open bs = 0 -> nk_opened bs = nk_closed bs -> nk_misuse bs = 0 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (cs_extra bs))) cs_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_socket)) memc (seg_rom SEGS))).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bs HJ H16 Hwlo Hwhi HNK Hop Hoc Hmi.
destruct HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (V2 : VAL (A_OBJ 2) = LA_G_NL) by (rewrite (lv_obj LV 2) by (unfold link_nobj; lia); reflexivity).
assert (Hfld : forall off v, 0 <= off -> off + 4 <= NK_SIZE -> rdn bs off 4 = v ->
          val_mem SEGS (rdW W memc) (LA_G_NL + off) 4 v).
{ intros off v H0 H1 <-. exact (anlk_field SEGS (rdW W memc) LA_G_NL bs off 4 HNK H0 H1). }
assert (Ropd : 0 <= nk_opened bs < 2 ^ 32).
{ unfold nk_opened, fld_u32, rdn. pose proof (bytes_le_to_Z_nonneg (slice bs NK_OPENED 4)) as R0.
  pose proof (bytes_le_to_Z_bound (slice bs NK_OPENED 4)) as R1.
  assert (L : (length (slice bs NK_OPENED 4) <= 4)%nat) by (unfold slice; rewrite length_firstn; lia).
  assert (P : 2 ^ (8 * Z.of_nat (length (slice bs NK_OPENED 4))) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  set (q := 2 ^ (8 * Z.of_nat (length (slice bs NK_OPENED 4)))) in *. lia. }
set (E := Eimg (Ereg regs (cs_extra bs))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cs_extra bs)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (nk_opened bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Eg : ew E (A_OBJ 2) = Z_to_bv 64 LA_G_NL)
  by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V2; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VBv : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
rewrite restrict_mkst_fx. unfold cs_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold cs_regions, stack_region, cs_nl.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + fold E. rewrite (VBv _ _ Eg) by (unfold LA_G_NL; lia).
    split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ LA_G_NL 0x40214 4 (SLit 0) 0);
        [cbn [sv_denot]; reflexivity | zrng | zrng |].
      apply Hfld; [lia | unfold NK_SIZE; lia | exact Hop].
    * apply (chunk_ok_val SEGS E _ LA_G_NL 0x40218 4 (SOff 33 0) (nk_opened bs));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |].
      apply Hfld; [lia | unfold NK_SIZE; lia | reflexivity].
    * apply (chunk_ok_val SEGS E _ LA_G_NL 0x4021c 4 (SOff 33 0) (nk_opened bs));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |].
      apply Hfld; [lia | unfold NK_SIZE; lia | exact (eq_sym Hoc)].
    * apply (chunk_ok_val SEGS E _ LA_G_NL 0x40220 4 (SLit 0) 0);
        [cbn [sv_denot]; reflexivity | zrng | zrng |].
      apply Hfld; [lia | unfold NK_SIZE; lia | exact Hmi].
- apply pairwise_disjoint_of_extents.
  unfold cs_regions, stack_region, cs_nl, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  fold E. rewrite (VBv _ _ Eg) by (unfold LA_G_NL; lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold LA_G_NL.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [cs_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite Usp, E32, E33, Eg.
  rewrite !unsigned_lit_small by (unfold SB, LA_G_NL; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, LA_G_NL.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

Theorem check_socket_aproof : forall rlo rhi, check_socket_acontract SK SEGS rlo rhi B.
Proof.
intros rlo rhi. unfold check_socket_acontract, aleaf, check_socket_apost, check_socket_awr.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HPre.
destruct HA as (HJ & HGX & HROD & Hret & Hra4 & Hgp & Htp & H16 & Hwlo & Hwhi & Hev & Hside & Hajw & _).
destruct HPre as (bs & HNK & Hop & Hoc & Hmi).
unfold CHECK_SOCKET_AK, CHECK_SOCKET_AFRAME in *. unfold YK0s.ret_ok in Hret.
pose proof HJ as HJ0.
pose proof (cs_entry G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bs HJ H16 Hwlo Hwhi HNK
  Hop Hoc Hmi) as HS.
replace (cfg_at SEGS CHECK_SOCKET_A regs memc mdc)
  with (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_check_socket)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, CHECK_SOCKET_A, AF_check_socket; rewrite (lv_text LV); reflexivity).
remember (Eimg (Ereg regs (cs_extra bs))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cs_extra bs)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (HAE : env_agree 32 (Ereg regs (cs_extra bs)) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HEdef EL.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) memc)) by constructor.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ lf_Zs 16 (spZ regs) a ->
          aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by reflexivity.
assert (HGc : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
pose proof (paj_run_x SK B LAWS G HGX XO OUT) as RUN.
(* +0x00 .. +0x44: the frame, the three loads and branches (decided by the entry state), restore, pop, ret *)
paj_run_tok RUN HS HJ SHOK Bspan; [lf_awr |].
lf_kept HFr W 16 (spZ regs) UNk. clear HF HFr. lf_fold UN HGc UNk HG W memc 16 (spZ regs).
lf_ret PI LAWS W regs (cs_extra bs) HS HAE E1 Hret HJ0 HJ Hwlo Hwhi UN HGc.
Qed.
End w.

(* LAWS discharged on the image's segments (lib/Reusable/YG0q.v AR_laws_ok) *)
Section img. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
Context {PI : PAImg link_listing}.
Theorem check_socket_aproof_img : forall B, LinkVals -> pa_segs = AB1v.tfibsegs ->
  forall rlo rhi, check_socket_acontract SK pa_segs rlo rhi B.
Proof.
intros B LV Hsegs.
assert (LAWS : AR_laws pa_segs B) by (rewrite Hsegs; exact (YG0q.AR_laws_ok AB1v.tfibsegs B)).
exact (check_socket_aproof SK B LAWS LV).
Qed.
End img.

Print Assumptions check_socket_aproof.
Print Assumptions check_socket_aproof_img.
