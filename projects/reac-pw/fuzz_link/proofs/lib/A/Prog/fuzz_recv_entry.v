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
(* fuzz_recv on image A (fuzz_link.asan 0x823cc, listing offset AF_fuzz_recv = 0x200; listing
   (internal path) (internal record, sha256 549eae89aefb)): the entry piece of its walk, from
   the call to the call of ___errno_location at +0x220 (the queue is empty) or to the call of checked_memcpy at +0xd0 (a
   chunk is handed out). It ends at the statements RV_AT_ERRNO and RV_AT_MEMCPY of lib/A/Prog/fuzz_recv_defs.v.

   - the entry state rv_e_ss: the 96-byte frame, the .got word of the shadow base and its cell, and g_nl as two
     regions with narrow write windows: [0x40200, 0x4020c) with n_chunks, next, end_errno (window: next) and
     [0x40214, 0x40224) with open, misuse (window: misuse); the fields between keep their bytes;
   - the run stops at +0x4c `bne a0, 7`; from there the frame region is read only (the frame words are stored);
   - three paths (a0 <> 7; a0 = 7 and open = 0; a0 = 7 and open <> 0) run to +0x84 `bge next, n_chunks`; on each
     path the walk reads misuse back, drops the region of open and misuse and the branch conditions, and joins the one
     state rv_bge_ss;
   - from rv_bge_ss (rv_bge_ok): next >= n_chunks runs to the call +0x220 (RV_AT_ERRNO); next < n_chunks runs to
     +0xa4 with the instrumented check of the 8-byte load of chunk_len[next] as an obligation (g_nl's shadow bytes),
     makes a0 a fresh atom with an 8-byte region that holds chunk_len[next], runs to +0xa8 `bltu s2, s0`, and both arms
     run to the call +0xd0 (RV_AT_MEMCPY).
   Proves no function (kind: segment lemma). *)
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
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlk LinkWalkErrno fuzz_recv_c fuzz_recv_defs fuzz_recv_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- the symbolic states of the entry piece ---------------------------------------------------------------- *)
(* g_nl's fields n_chunks, next, end_errno (atoms 33..35; window: next) and open, misuse (atoms 36, 37; window:
   misuse); the region base is g_nl's image atom A_OBJ 2 *)
Definition rv_Ra : YP09.region := YP09.mkRegion (Some (A_OBJ 2)) 0x40200 0x4020c 0x40204 0x40208
  [YP09.mkChunk 0x40200 (CVal 4 (SOff 33 0)); YP09.mkChunk 0x40204 (CVal 4 (SOff 34 0));
   YP09.mkChunk 0x40208 (CVal 4 (SOff 35 0))].
Definition rv_Rb : YP09.region := YP09.mkRegion (Some (A_OBJ 2)) 0x40214 0x40224 0x40220 0x40224
  [YP09.mkChunk 0x40214 (CVal 4 (SOff 36 0)); YP09.mkChunk 0x40220 (CVal 4 (SOff 37 0))].
(* sp, the shadow base (atom 32), the five fields, g_nl's address *)
Definition rv_e_atoms : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0);
   (33%nat, mkAF 0 64 0); (34%nat, mkAF 0 64 0); (35%nat, mkAF 0 (2 ^ 31 - 1) 0);
   (36%nat, mkAF 0 1 0); (37%nat, mkAF 0 1 0); (A_OBJ 2, mkAF LA_G_NL LA_G_NL 0)].
Definition rv_e_ss : sstate :=
  mkSS AF_fuzz_recv sr_atoms [stack_region 96; got_regionP; bcell_regionP 32; rv_Ra; rv_Rb] None
    (mkFacts rv_e_atoms [] []).
(* the frame after the prologue, read only *)
Definition rv_fr_e : YP09.region := YP09.mkRegion (Some 2%nat) (-96) 0 0 0
  [YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
   YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
(* the join at +0x84 `bge next, n_chunks`: s0 = len, s1 = buf, a1 = g, a2 = next, a4 = g + 0x40000, a5 = n_chunks,
   s3 = the shadow base *)
Definition rv_regs_bge : list sv :=
  [SLit 0; SOff 1 0; SOff 2 (-96); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 12 0; SOff 11 0;
   SLit 262144; SOff 243 0; SOff 34 0; SOff 305 0; SOff 243 262144; SOff 33 0; SOff 16 0; SOff 17 0;
   SOff 18 0; SOff 32 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0;
   SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition rv_bge_ss : sstate :=
  mkSS (AF_fuzz_recv + 0x84) rv_regs_bge [rv_fr_e; got_regionP; bcell_regionP 32; rv_Ra] None
    (mkFacts rv_e_atoms [] []).
(* +0xa4: a0 = the address of chunk_len[next] (atom 520), its 8 bytes (atom 521) *)
Definition rv_pR : YP09.region := YP09.mkRegion (Some 520%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 521 0))].
(* the values of the atoms 32..37 *)
Definition rv_xe (bs : list byte) : list word :=
  map (Z_to_bv 64) [SB; nk_n_chunks bs; nk_next bs; nk_end_errno bs; nk_open bs; nk_misuse bs].

Lemma submem_firstn : forall n (l : smem), submem (firstn n l) l.
Proof.
  induction n as [|n IH]; intros l; [apply submem_nil|].
  destruct l as [|r l]; [apply submem_nil|]. cbn [firstn]. apply submem_keep; [apply subregion_refl | apply IH].
Qed.

Lemma den_of_U : forall E v z, U E v = z -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z H. unfold U in H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma den_atom0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hv. rewrite Z.add_0_r. reflexivity. Qed.

(* a signed compare of two small values *)
Lemma rv_ge : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (x <? y).
Proof.
  intros E a b x y Ha Hb Hx Hy. rewrite Ha, Hb. cbn [branch_taken]. rewrite bv_lts_signed.
  rewrite !signed_of_small by (rewrite unsigned_lit_small by lia; unfold half64; lia).
  rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

(* the address of chunk_len[next] (+0x88..+0x90) and of the chunk (+0xb8..+0xc4) *)
Lemma rv_den_cl : forall E x, ew E 34 = Z_to_bv 64 x -> bv_unsigned (ew E 243) = LA_G_NL -> 0 <= x <= 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 34 0) (SLit 3)) (SLit 262144)) (SOff 243 0)) =
  Z_to_bv 64 (LA_G_NL + NK_CHUNK_LEN + 8 * x).
Proof.
  intros E x H34 Hg Hx. apply den_of_U.
  rewrite !U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 34 x H34) by lia. rewrite !U_lit by lia.
  rewrite U_SOff, Hg, Z.add_0_r. change (Z.land 3 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  unfold zcanon, M64, LA_G_NL, NK_CHUNK_LEN. rewrite !(Z.mod_small _ (2 ^ 64)); lia.
Qed.

Lemma rv_den_src : forall E x, ew E 34 = Z_to_bv 64 x -> bv_unsigned (ew E 243) = LA_G_NL -> 0 <= x <= 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL (SOff 34 0) (SLit 12)) (SOff 243 0)) =
  Z_to_bv 64 (LA_G_NL + NL_CHUNK_MAX * x).
Proof.
  intros E x H34 Hg Hx. apply den_of_U.
  rewrite !U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 34 x H34) by lia. rewrite !U_lit by lia.
  rewrite U_SOff, Hg, Z.add_0_r. change (Z.land 12 63) with 12. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 12) with 4096.
  unfold zcanon, M64, LA_G_NL, NL_CHUNK_MAX. rewrite !(Z.mod_small _ (2 ^ 64)); lia.
Qed.

Ltac rv_zrng := try change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); try change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32);
  try change (Z.of_N 8) with 8; try change (Z.of_N 4) with 4; lia.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ link_listing PI).
#[local] Abbreviation VAL := (@pa_val _ link_listing PI).
#[local] Abbreviation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
Hypothesis ERRF : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).

Lemma rv_vals : VAL (A_OBJ 1) = 0xa19d0 /\ VAL (A_OBJ 2) = LA_G_NL /\ VAL (A_OBJ 64) = 0xaa438 /\ BASE = 0x821cc.
Proof.
  split; [rewrite (lv_obj LV 1) by (unfold link_nobj; lia); reflexivity|].
  split; [rewrite (lv_obj LV 2) by (unfold link_nobj; lia); reflexivity|].
  split; [rewrite (lv_obj LV 64) by (unfold link_nobj; lia); reflexivity|].
  exact (lv_text LV).
Qed.

Lemma st_ok_pi_region : forall E ss ms i r,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof. intros E ss ms i r HS Hi. exact (st_ok_region_nth (segs := SEGS) E (abs_ss VAL ss) ms i r HS Hi). Qed.

(* the frame region read only *)
Lemma st_ok_pi_ro : forall E ss ms r rs,
  st_ok_pi SEGS VAL E ss ms -> ss_mem ss = r :: rs ->
  regions_wf (YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) 0 0 (YP09.r_chunks r) :: rs) = true ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss)
    (YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) 0 0 (YP09.r_chunks r) :: rs) (ss_resv ss)
    (ss_facts ss)) ms.
Proof.
  intros E ss ms r rs HS Hm Hwf. unfold st_ok_pi, abs_ss in *.
  refine (st_ok_submem SEGS E _ ms _ HS _ Hwf).
  cbn [setpc ss_mem]. rewrite Hm. apply submem_keep; [|apply submem_refl].
  unfold subregion. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. intros x Hx; exact Hx.
Qed.

(* THE JOIN: the first four regions, the atom facts, no branch condition *)
Lemma st_ok_pi_join : forall E ss ms,
  st_ok_pi SEGS VAL E ss ms -> regions_wf (firstn 4 (ss_mem ss)) = true ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (firstn 4 (ss_mem ss)) (ss_resv ss)
    (mkFacts (f_atoms (ss_facts ss)) [] [])) ms.
Proof.
  intros E ss ms HS Hwf. unfold st_ok_pi, abs_ss in *.
  pose proof (st_ok_prune SEGS E _ ms [] [] HS) as HP.
  exact (st_ok_submem SEGS E _ ms (firstn 4 (ss_mem ss)) HP (submem_firstn 4 (ss_mem ss)) Hwf).
Qed.

(* a0 a fresh atom *)
Lemma st_ok_pi_abs10 : forall E ss (H : word -> bool) ms n,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> ss_atoms_lt n ss = true ->
  st_ok_pi SEGS VAL (ewset E n (getr (ms_regs ms) 10%bv))
    (mkSS (ss_pc ss) (sr_set (ss_regs ss) 10%bv (SOff n 0)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) (restrict H ms).
Proof.
  intros E ss H ms n HS Hn. unfold st_ok_pi, abs_ss in *.
  exact (st_ok_abstract_reg SEGS n E (setpc ss (BASE + ss_pc ss)) (restrict H ms) 10%bv HS
    ltac:(destruct ss; exact Hn) eq_refl).
Qed.

(* a further fresh atom *)
Lemma st_ok_pi_ext : forall E ss ms n v,
  st_ok_pi SEGS VAL E ss ms -> ss_atoms_lt n ss = true -> st_ok_pi SEGS VAL (ewset E n v) ss ms.
Proof.
  intros E ss ms n v HS Hn. unfold st_ok_pi, abs_ss in *.
  exact (st_ok_agree SEGS n E (ewset E n v) _ ms HS (env_agree_ewset E n v) ltac:(destruct ss; exact Hn)).
Qed.

Lemma rv_img_ewset : forall E n v, img_env VAL A_LIM E -> (A_LIM <= n)%nat -> img_env VAL A_LIM (ewset E n v).
Proof. intros E n v HE Hn a Ha. rewrite ew_ewset_other by lia. exact (HE a Ha). Qed.

Section cc.
Variable c : rvc.
Hypothesis HC : rv_call SK B c.
#[local] Abbreviation W := (c_W c).
#[local] Abbreviation memc := (c_memc c).
#[local] Abbreviation regs0 := (c_regs0 c).
#[local] Abbreviation bs := (c_bs c).

(* ---- what the walk takes from the call's premises ---- *)
Lemma rv_HJ : ajournal_gx SEGS B (c_G c) (c_XO c) (c_OUT c) (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c)
  (c_mem0 c) (c_md0 c) (c_own c) (c_lyc c) (c_Sc c) W memc (c_mdc c) (c_k c).
Proof. exact (proj1 (proj1 HC)). Qed.

Lemma rv_HGX : gx_ok SEGS B (c_G c).
Proof. exact (proj1 (proj2 (proj1 HC))). Qed.

Lemma rv_ajw : forall a, inFP (fuzz_recv_awr regs0 (rdW W memc)) a ->
  ajw B (c_G c) (c_XO c) (c_OUT c) (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_lyc c) (c_Sc c) (c_own c) a.
Proof. destruct HC as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _) & _). exact H. Qed.

Lemma rv_buf_def : forall i, 0 <= i < rv_len c -> aview SEGS (w_H W) memc (rv_buf c + i) <> None.
Proof.
  intros i Hi. destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (junk & Hl & (_ & _ & Hb) & _) & _).
  rewrite <- (ard_aview SEGS W memc). unfold ard.
  unfold rv_len in Hi. unfold rv_buf.
  replace (aarg regs0 1 + i) with (aarg regs0 1 + Z.of_nat (Z.to_nat i)) by lia.
  rewrite Hb by lia.
  destruct (nth_error junk (Z.to_nat i)) eqn:En; [discriminate|]. apply nth_error_None in En. lia.
Qed.

(* the environments of the walk: the registers at the call, the shadow base and the five fields *)
Definition rv_env_ok (E : env) : Prop :=
  img_env VAL A_LIM E /\
  (forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs0 r) /\
  ew E 32 = Z_to_bv 64 SB /\ ew E 33 = Z_to_bv 64 (nk_n_chunks bs) /\ ew E 34 = Z_to_bv 64 (nk_next bs) /\
  ew E 35 = Z_to_bv 64 (nk_end_errno bs) /\ ew E 36 = Z_to_bv 64 (nk_open bs) /\
  ew E 37 = Z_to_bv 64 (nk_misuse bs).

Lemma rv_E0_ok : rv_env_ok (Eimg (Ereg regs0 (rv_xe bs))).
Proof.
  split; [apply Eimg_env|].
  split; [intros n r Hn Hr; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs0 _ n r Hr)|].
  split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs0 _ 0)|].
  split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs0 _ 1)|].
  split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs0 _ 2)|].
  split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs0 _ 3)|].
  split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs0 _ 4)|].
  rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs0 _ 5).
Qed.

Lemma rv_env_facts : forall E, rv_env_ok E ->
  bv_unsigned (ew E 243) = LA_G_NL /\ bv_unsigned (ew E 242) = 0xa19d0 /\ bv_unsigned (ew E 305) = 0xaa438 /\
  bv_unsigned (ew E 2) = rv_sp c /\
  ew E 10 = Z_to_bv 64 (aarg regs0 0) /\ ew E 11 = Z_to_bv 64 (rv_buf c) /\ ew E 12 = Z_to_bv 64 (rv_len c).
Proof.
  intros E (HEI & ER & _). destruct rv_vals as (V1 & V2 & V64 & _).
  split; [rewrite (HEI 243%nat) by (unfold A_TEXT, A_LIM; lia); exact V2|].
  split; [rewrite (HEI 242%nat) by (unfold A_TEXT, A_LIM; lia); exact V1|].
  split; [rewrite (HEI 305%nat) by (unfold A_TEXT, A_LIM; lia); exact V64|].
  split; [rewrite (ER 2%nat 2%bv) by (lia || reflexivity); reflexivity|].
  split; [rewrite (ER 10%nat (Z_to_bv 5 (10 + 0))) by (lia || reflexivity);
          unfold aarg, argZ; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [rewrite (ER 11%nat (Z_to_bv 5 (10 + 1))) by (lia || reflexivity);
          unfold rv_buf, aarg, argZ; symmetry; apply Z_to_bv_bv_unsigned|].
  rewrite (ER 12%nat (Z_to_bv 5 (10 + 2))) by (lia || reflexivity).
  unfold rv_len, aarg, argZ; symmetry; apply Z_to_bv_bv_unsigned.
Qed.

(* ---- THE ENTRY STATE ---- *)
Lemma rv_entry_st :
  st_ok_pi SEGS VAL (Eimg (Ereg regs0 (rv_xe bs))) rv_e_ss
    (restrict (w_H W) (mkst regs0 (Z_to_bv 64 (BASE + AF_fuzz_recv)) memc (seg_rom SEGS))).
Proof.
pose proof rv_HJ as HJ.
destruct HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
destruct (rv_sp_bounds SK B c HC) as (Hceil & Hlo & Hhi & H47 & H16 & HXO').
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS (c_lyc c) (c_Sc c) W memc (c_mdc c) HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL) in Kgot. rewrite (pal_cell B TL) in Kgot, Kcell.
destruct rv_vals as (V1 & V2 & V64 & VB).
rewrite V1, V64 in Kgot. rewrite V64 in Kcell.
pose proof HC as (_ & HNK & WF & _).
pose proof WF as (Wnc & Wnx & Wns & Wni & Wop & Won & Wcl & Wmi & Wee & Wse & Wsd & _ & _).
unfold NL_CHUNKS in Wnc.
pose proof HNK as [[Hab Hwr] HL].
assert (Hfld : forall off v, 0 <= off -> off + 4 <= NK_SIZE -> rdn bs off 4 = v ->
          val_mem SEGS (rdW W memc) (LA_G_NL + off) 4 v).
{ intros off v H0 H1 <-. exact (anlk_field SEGS (rdW W memc) LA_G_NL bs off 4 HNK H0 H1). }
pose proof rv_E0_ok as HE.
pose proof (rv_env_facts _ HE) as (Ug & Ugot & Ucell & Usp & _).
destruct HE as (HEI & ER & E32 & E33 & E34 & E35 & E36 & E37).
set (E := Eimg (Ereg regs0 (rv_xe bs))) in *.
assert (VBv : forall n v, bv_unsigned (ew E n) = v -> base_val E (Some n) = v) by (intros n v Hn; exact Hn).
unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in *.
rewrite restrict_mkst_fx. unfold rv_e_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_regionP, bcell_regionP, rv_Ra, rv_Rb. change (A_OBJ 1) with 242%nat.
  change (A_OBJ 2) with 243%nat. change (A_OBJ 64) with 305%nat.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VBv _ _ Usp). split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VBv _ _ Ugot). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xa19d0 0 8 (SOff 305 0) 0xaa438);
      [apply den_atom0; [apply bv_eq; rewrite Ucell, unsigned_lit_small by lia; reflexivity | lia] | rv_zrng | rv_zrng |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
  + rewrite (VBv _ _ Ucell). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xaa438 0 8 (SOff 32 0) SB);
      [apply den_atom0; [exact E32 | unfold SB; lia] | unfold SB; rv_zrng | rv_zrng |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
  + rewrite (VBv _ _ Ug). split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|].
    split; [intros o Ho; apply Hwr; rewrite HL; unfold NK_SIZE; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ LA_G_NL 0x40200 4 (SOff 33 0) (nk_n_chunks bs));
        [apply den_atom0; [exact E33 | lia] | rv_zrng | rv_zrng |].
      apply Hfld; [lia | unfold NK_SIZE; lia | reflexivity].
    * apply (chunk_ok_val SEGS E _ LA_G_NL 0x40204 4 (SOff 34 0) (nk_next bs));
        [apply den_atom0; [exact E34 | lia] | rv_zrng | rv_zrng |].
      apply Hfld; [lia | unfold NK_SIZE; lia | reflexivity].
    * apply (chunk_ok_val SEGS E _ LA_G_NL 0x40208 4 (SOff 35 0) (nk_end_errno bs));
        [apply den_atom0; [exact E35 | lia] | rv_zrng | rv_zrng |].
      apply Hfld; [lia | unfold NK_SIZE; lia | reflexivity].
  + rewrite (VBv _ _ Ug). split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|].
    split; [intros o Ho; apply Hwr; rewrite HL; unfold NK_SIZE; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ LA_G_NL 0x40214 4 (SOff 36 0) (nk_open bs));
        [apply den_atom0; [exact E36 | lia] | rv_zrng | rv_zrng |].
      apply Hfld; [lia | unfold NK_SIZE; lia | reflexivity].
    * apply (chunk_ok_val SEGS E _ LA_G_NL 0x40220 4 (SOff 37 0) (nk_misuse bs));
        [apply den_atom0; [exact E37 | lia] | rv_zrng | rv_zrng |].
      apply Hfld; [lia | unfold NK_SIZE; lia | reflexivity].
- apply pairwise_disjoint_of_extents.
  unfold stack_region, got_regionP, bcell_regionP, rv_Ra, rv_Rb, extent_of_region.
  change (A_OBJ 1) with 242%nat. change (A_OBJ 2) with 243%nat. change (A_OBJ 64) with 305%nat.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VBv _ _ Usp), (VBv _ _ Ugot), (VBv _ _ Ucell), (VBv _ _ Ug).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold LA_G_NL.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  unfold rv_e_atoms. change (A_OBJ 2) with 243%nat. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, Ug, E32, E33, E34, E35, E36, E37.
  unfold nk_n_chunks, nk_next, nk_end_errno, nk_open, nk_misuse in *.
  rewrite !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, LA_G_NL.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* ---- the bytes a run of the entry piece writes ---- *)
(* g_nl's next and misuse *)
Definition rv_zg (a : Z) : Prop :=
  (LA_G_NL + NK_NEXT <= a < LA_G_NL + NK_NEXT + 4) \/ (LA_G_NL + NK_MISUSE <= a < LA_G_NL + NK_MISUSE + 4).
(* g_nl's next *)
Definition rv_zn (a : Z) : Prop := LA_G_NL + NK_NEXT <= a < LA_G_NL + NK_NEXT + 4.
(* the prologue: the frame and the two fields *)
Definition rv_zs (a : Z) : Prop := (rv_sp c - 96 <= a < rv_sp c) \/ rv_zg a.
(* the buffer as at the call *)
Definition rv_bufk (mem : word -> option byte) : Prop :=
  forall i, 0 <= i < rv_len c -> aview SEGS (w_H W) mem (rv_buf c + i) = aview SEGS (w_H W) memc (rv_buf c + i).

Lemma rv_zn_g : forall a, rv_zn a -> rv_zg a.
Proof. intros a H. left. exact H. Qed.
Lemma rv_zg_g : forall a, rv_zg a -> rv_zg a.
Proof. intros a H. exact H. Qed.

(* rv_inv after the prologue, and the buffer *)
Lemma rv_inv_first : forall regs1 mem1 md1,
  ajournal_gx SEGS B (c_G c) (c_XO c) (c_OUT c) (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c)
    (c_md0 c) (c_own c) (c_lyc c) (c_Sc c) W mem1 md1 (c_k c) ->
  m_fds md1 = m_fds (c_mdc c) -> m_fs md1 = m_fs (c_mdc c) ->
  getr regs1 2 = w64 (rv_sp c - 96) -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
  getr regs1 26 = getr regs0 26 -> getr regs1 27 = getr regs0 27 ->
  Forall (fun p => val_mem SEGS (rdW W mem1) (rv_sp c - 96 + fst p) 8 (bv_unsigned (snd p))) (rv_frame_vals c) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ rv_zs a -> aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) memc a) ->
  mem_grows (rdW W memc) (rdW W mem1) ->
  rv_inv SK B c regs1 mem1 md1 /\ rv_bufk mem1.
Proof.
  intros regs1 mem1 md1 HJ Hfd Hfs R2 R3 R4 R26 R27 HFV UN HG.
  destruct (rv_sp_bounds SK B c HC) as (Hceil & Hlo & Hhi & H47 & H16 & HXO).
  destruct (rv_pre_facts SK B TL c HC) as (Hb0 & Hlen & Hamr & Hbg & Hbf & Hef & Heg & He0 & He1).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  split.
  - unfold rv_inv.
    refine (conj HJ (conj Hfd (conj Hfs (conj R2 (conj R3 (conj R4 (conj R26 (conj R27 (conj HFV (conj _ _)))))))))).
    + intros a Ha Hw He. apply UN; [exact Ha|]. unfold rv_zs, rv_zg. intros [H|[H|H]].
      * apply Hw. unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK. lia.
      * apply He. unfold rv_ewr. tauto.
      * apply He. unfold rv_ewr. tauto.
    + intros a Hp. exact (apresent_grows _ _ _ _ HG Hp).
  - intros i Hi. apply UN.
    + unfold amem_range in Hamr. lia.
    + unfold rv_zs, rv_zg, apart_gnl, apart_frame, rv_sp, LA_G_NL, NK_NEXT, NK_MISUSE, NK_SIZE, FUZZ_RECV_AK,
        FUZZ_RECV_AFRAME, ESTACK in *.
      lia.
Qed.

(* rv_inv after a later run that writes only next / misuse, and the buffer *)
Lemma rv_inv_next : forall regs mem md regs' mem' md' (Zs : Z -> Prop),
  rv_inv SK B c regs mem md -> rv_bufk mem ->
  ajournal_gx SEGS B (c_G c) (c_XO c) (c_OUT c) (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c)
    (c_md0 c) (c_own c) (c_lyc c) (c_Sc c) W mem' md' (c_k c) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, Zs a -> rv_zg a) ->
  mem_grows (rdW W mem) (rdW W mem') ->
  getr regs' 2 = w64 (rv_sp c - 96) -> getr regs' 3 = getr regs0 3 -> getr regs' 4 = getr regs0 4 ->
  getr regs' 26 = getr regs0 26 -> getr regs' 27 = getr regs0 27 ->
  rv_inv SK B c regs' mem' md' /\ rv_bufk mem'.
Proof.
  intros regs mem md regs' mem' md' Zs HI HB HJ' Hfd Hfs UN HZ HG R2 R3 R4 R26 R27.
  destruct (rv_pre_facts SK B TL c HC) as (Hb0 & Hlen & Hamr & Hbg & Hbf & Hef & Heg & He0 & He1).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HI as (_ & _ & _ & S2 & S3 & S4 & S26 & S27 & _).
  split.
  - apply (rv_inv_step SK B TL c HC regs mem md regs' mem' md' Zs HI HJ' Hfd Hfs UN).
    + intros a Ha. right. destruct (HZ a Ha) as [H|H]; unfold rv_ewr; tauto.
    + intros a Hp. exact (apresent_grows _ _ _ _ HG Hp).
    + congruence.
    + congruence.
    + congruence.
    + congruence.
    + congruence.
  - intros i Hi.
    assert (Hr : 0 <= rv_buf c + i < 2 ^ 64) by (unfold amem_range in Hamr; lia).
    assert (Hz : ~ Zs (rv_buf c + i)).
    { intros HZa. destruct (HZ _ HZa) as [H|H];
        unfold apart_gnl, rv_buf, rv_len, LA_G_NL, NK_NEXT, NK_MISUSE, NK_SIZE in *; lia. }
    rewrite (UN _ Hr Hz). exact (HB i Hi).
Qed.

(* the frame word at offset od of the frame, from a chunk of the stack region *)
Lemma rv_fword : forall E m cs lo hi wlo whi od (n : nat) (w : word),
  region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 2) = rv_sp c ->
  In (YP09.mkChunk (od - 96) (CVal 8 (SOff n 0))) cs -> ew E n = w ->
  val_mem SEGS m (rv_sp c - 96 + od) 8 (bv_unsigned w).
Proof.
  intros E m cs lo hi wlo whi od n w HR Hsp Hin Hn.
  replace (rv_sp c - 96 + od) with (rv_sp c + (od - 96)) by lia.
  refine (field_of_region E m 2 (rv_sp c) cs lo hi wlo whi (od - 96) 8%N (SOff n 0) (bv_unsigned w) HR Hsp Hin _ _ _).
  - cbn [sv_denot]. rewrite Hn, Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
    change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia.
Qed.

(* ---- tactics of the piece ---- *)
(* the run's write permission: the frame, g_nl's next and misuse (the contract's write set) *)
Ltac rv_awr :=
  lazymatch goal with |- awr_ok_xe _ _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_xe_cons;
    [ intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ewset ew Nat.eqb] in Ha;
      first
      [ lia
      | lazymatch type of Ha with context [ew _ 2%nat] =>
          match goal with U : bv_unsigned (ew _ 2%nat) = _ |- _ => rewrite U in Ha end;
          destruct (rv_sp_bounds SK B c HC) as (? & ? & ? & ? & ? & ?);
          unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in *;
          left; left; split; [left; lia | lia] end
      | lazymatch type of Ha with context [ew _ 243%nat] =>
          match goal with U : bv_unsigned (ew _ 243%nat) = _ |- _ => rewrite U in Ha end;
          left; apply rv_ajw; exists (LA_G_NL + NK_NEXT, LA_G_NL + NK_MISUSE + 4);
          split; [left; reflexivity | cbn [fst snd]; unfold NK_NEXT, NK_MISUSE; lia] end ]
    | ]);
  apply awr_ok_xe_nil.

(* the bytes a run left as they were: every byte outside its write windows *)
Ltac rv_win :=
  let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let aa := fresh "aa" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
  intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
  repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
          [ injection Hq as <- <- <-; cbn [base_val ewset ew Nat.eqb] in Hrr;
            repeat match goal with U : bv_unsigned (ew _ ?n) = _ |- _ =>
              lazymatch type of Hrr with context [ew _ n] => rewrite U in Hrr end end;
            cbv [rv_zs rv_zg rv_zn LA_G_NL NK_NEXT NK_MISUSE] in Hrr |- *; lia
          | ]);
  destruct Hin.
Ltac rv_kept HFr Zs UN :=
  lazymatch type of HFr with frame_of ?E0 ?rs _ _ =>
    let HW := fresh "HW" in
    assert (HW : forall b wlo whi a, In (b, wlo, whi) (windows rs) ->
                 base_val E0 b + wlo <= a < base_val E0 b + whi -> Zs a) by rv_win;
    pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ Zs HFr HW) as UN; clear HW
  end.

(* the descriptors and the file system across a run *)
Ltac rv_wvb := first [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
                     | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity ].

(* sp, gp, tp, s10, s11 at the end of a run, as R2 R3 R4 R26 R27 *)
Ltac rv_r5 HS Usp ER R2 R3 R4 R26 R27 :=
  prreg HS (2%bv : bv 5) R2; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4;
  prreg HS (26%bv : bv 5) R26; prreg HS (27%bv : bv 5) R27;
  rewrite Usp in R2; replace (rv_sp c + -96) with (rv_sp c - 96) in R2 by lia;
  rewrite (ER 3%nat 3%bv) in R3 by (lia || reflexivity);
  rewrite (ER 4%nat 4%bv) in R4 by (lia || reflexivity);
  rewrite (ER 26%nat 26%bv) in R26 by (lia || reflexivity);
  rewrite (ER 27%nat 27%bv) in R27 by (lia || reflexivity).

(* a 4-byte field the run left in a region at g_nl *)
Ltac rv_den := cbn [sv_denot ewset ew Nat.eqb];
  repeat match goal with Eq : ew ?E0 ?n = Z_to_bv 64 _ |- context [ew ?E0 ?n] => rewrite Eq end;
  rewrite ?unsigned_lit_small by lia; rewrite ?Z.add_0_r; reflexivity.
Ltac rv_vfield HR U :=
  eapply (field_of_region (segs := SEGS) _ _ _ _ _ _ _ _ _ _ 4%N);
  [ exact HR | exact U | repeat (first [left; reflexivity | right]) | rv_den | rv_zrng | rv_zrng ].

Ltac rv_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ =>
  let v := eval vm_compute in s in change s with v in HS end.

(* ---- FROM THE JOIN +0x84 TO THE TWO CALLS ---- *)
Lemma rv_bge_ok : RV_AT_ERRNO SK B c -> RV_AT_MEMCPY SK B c ->
  forall E ms md, rv_env_ok E ->
  st_ok_pi SEGS VAL E rv_bge_ss (restrict (w_H W) ms) ->
  rv_inv SK B c (ms_regs ms) (ms_mem ms) md -> rv_bufk (ms_mem ms) ->
  val_mem SEGS (rdW W (ms_mem ms)) (LA_G_NL + NK_MISUSE) 4 (rv_msu c) ->
  rv_goal SK B c (mkCfg ms md).
Proof.
intros HERR HCPY E ms md HE HS HI HB HMI.
pose proof (rv_env_facts _ HE) as (Ug & Ugot & Ucell & Usp & E10 & E11 & E12).
destruct HE as (HEI & ER & E32 & E33 & E34 & E35 & E36 & E37).
pose proof HI as (HJ & _).
destruct (rv_sp_bounds SK B c HC) as (Hceil & Hwlo & Hwhi & H47 & H16 & HXO).
destruct (rv_pre_facts SK B TL c HC) as (Hb0 & Hlen & Hamr & Hbg & Hbf & Hef & Heg & He0 & He1).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HC as (_ & HNK & WF & HRAg & _).
pose proof WF as (Wnc & Wnx & _ & _ & Wop & _ & _ & Wmi & Wee & _ & _ & Wcl & _).
unfold NL_CHUNKS, NL_CHUNK_MAX in Wnc, Wcl.
assert (Hlen' : rv_len c < 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia).
assert (Hlen0 : 4096 <= rv_len c) by (unfold NL_CHUNK_MAX in Hlen; exact Hlen).
unfold rv_goal.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) (ms_mem ms))) by constructor.
pose proof (paj_run_xe SK B LAWS (pal_env B TL) ERRF (c_G c) rv_HGX (c_XO c) (c_OUT c)) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* next >= n_chunks: +0x21c s0 := end_errno, the call of ___errno_location at +0x220 *)
  rewrite (rv_ge E (SOff 34 0) (SOff 33 0) (nk_next bs) (nk_n_chunks bs)) in Hc
    by first [apply den_atom0; [assumption | lia] | lia].
  apply negb_true_iff, Z.ltb_ge in Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [rv_awr |].
  rv_kept HFr rv_zn UNk. clear HF HFr.
  pmkst HS.
  rv_r5 HS Usp ER R2 R3 R4 R26 R27.
  prreg HS (1%bv : bv 5) R1. prreg HS (8%bv : bv 5) R8. prreg HS (19%bv : bv 5) R19.
  pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 3 _ HS eq_refl) as HRa.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?d) _ =>
    destruct (rv_inv_next (ms_regs ms) (ms_mem ms) md r m d rv_zn HI HB HJ ltac:(rv_wvb) ltac:(rv_wvb) UNk rv_zn_g HG
      R2 R3 R4 R26 R27) as (HI2 & HB2)
  end.
  apply HERR.
  + exact HI2.
  + exact Hc.
  + exact R1.
  + rewrite R8, E35. reflexivity.
  + rewrite R19, E32. reflexivity.
  + rv_vfield HRa Ug.
  + apply (val_mem_kept (w_H W) (ms_mem ms)); [|exact HMI].
    intros k Hk. cbn in Hk. apply UNk; [unfold LA_G_NL, NK_MISUSE; lia|].
    unfold rv_zn, LA_G_NL, NK_NEXT, NK_MISUSE. lia.
  + intros i Hi. rewrite (HB2 i Hi). exact (rv_buf_def i Hi).
- (* next < n_chunks: +0x88..+0xa0 the address of chunk_len[next] and the instrumented check of its 8-byte load *)
  rewrite (rv_ge E (SOff 34 0) (SOff 33 0) (nk_next bs) (nk_n_chunks bs)) in Hc
    by first [apply den_atom0; [assumption | lia] | lia].
  apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hlt.
  assert (Hcl : 0 <= rv_clen c <= 4096) by (unfold rv_clen; apply Wcl; lia).
  paj_run_tok RUN HS HJ SHOK Bspan; [ | rv_awr |].
  { (* g_nl's shadow bytes are as at the call *)
    rewrite (U_atom E 32 SB E32) by (unfold SB; lia).
    assert (Ua : U E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 34 0) (SLit 3)) (SLit 262144)) (SOff 243 0)) =
                 LA_G_NL + NK_CHUNK_LEN + 8 * nk_next bs).
    { unfold U. rewrite (rv_den_cl E (nk_next bs) E34 Ug) by lia. apply unsigned_lit_small.
      unfold LA_G_NL, NK_CHUNK_LEN. lia. }
    rewrite Ua. rewrite <- aview_rd_of. change SB with SHADOW_OFF.
    apply (rv_ra_kept SK B TL c HC (ms_regs ms) (ms_mem ms) md); [exact HI | unfold LA_G_NL, NK_CHUNK_LEN; lia |
      unfold LA_G_NL, NK_CHUNK_LEN, kHighMemEnd; lia |].
    rewrite <- (ard_aview SEGS W memc).
    intros x Hx. apply HRAg. unfold LA_G_NL, NK_CHUNK_LEN, NK_SIZE in *. lia. }
  rv_kept HFr rv_zn UN1. clear HF HFr.
  lazymatch type of HS with st_ok_pi _ _ (ewset E 512 ?ww) _ (restrict _ ?mm) => rename ww into w0; rename mm into ms1 end.
  lazymatch type of HG with mem_grows _ _ => rename HG into HG1 end.
  (* +0xa4: a0 := the address of chunk_len[next], a fresh atom 520 with an 8-byte region over atom 521 *)
  lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss2 (restrict _ _) =>
    pose proof (st_ok_pi_restrict_reg (w_H W) E1 ss2 ms1 (10%bv : bv 5) HS) as R10;
    let e := eval vm_compute in (sr_get (ss_regs ss2) (10%bv : bv 5)) in
    change (sr_get (ss_regs ss2) (10%bv : bv 5)) with e in R10;
    pose proof (st_ok_pi_abs10 E1 ss2 (w_H W) ms1 520 HS ltac:(vm_compute; reflexivity)) as HS1
  end.
  rewrite (rv_den_cl (ewset E 512 w0) (nk_next bs)) in R10 by first [exact E34 | exact Ug | lia].
  rewrite R10 in HS1. clear HS.
  pose proof (st_ok_pi_ext _ _ _ 521 (Z_to_bv 64 (rv_clen c)) HS1 ltac:(vm_compute; reflexivity)) as HS2. clear HS1.
  assert (Up : bv_unsigned (Z_to_bv 64 (LA_G_NL + NK_CHUNK_LEN + 8 * nk_next bs)) =
               LA_G_NL + NK_CHUNK_LEN + 8 * nk_next bs)
    by (apply unsigned_lit_small; unfold LA_G_NL, NK_CHUNK_LEN; lia).
  (* chunk_len[next] at the run's end memory: as at the call *)
  assert (Vcl : val_mem SEGS (rdW W (ms_mem ms1)) (LA_G_NL + NK_CHUNK_LEN + 8 * nk_next bs + 0) 8 (rv_clen c)).
  { rewrite Z.add_0_r. pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & UNc & _).
    apply (val_mem_kept (w_H W) memc).
    - intros k Hk. cbn in Hk.
      rewrite (UN1 (LA_G_NL + NK_CHUNK_LEN + 8 * nk_next bs + k) ltac:(unfold LA_G_NL, NK_CHUNK_LEN; lia)
        ltac:(unfold rv_zn, LA_G_NL, NK_CHUNK_LEN, NK_NEXT; lia)).
      apply UNc; [unfold LA_G_NL, NK_CHUNK_LEN; lia | |].
      + unfold rv_sp, FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK, LA_G_NL, NK_CHUNK_LEN in *. lia.
      + unfold rv_ewr, apart_gnl, rv_buf, rv_len, LA_G_NL, NK_CHUNK_LEN, NK_NEXT, NK_MISUSE, NK_SIZE in *. lia.
    - replace (LA_G_NL + NK_CHUNK_LEN + 8 * nk_next bs) with (LA_G_NL + (NK_CHUNK_LEN + 8 * nk_next bs)) by lia.
      exact (anlk_field SEGS (rdW W memc) LA_G_NL bs (NK_CHUNK_LEN + 8 * nk_next bs) 8 HNK
        ltac:(unfold NK_CHUNK_LEN; lia) ltac:(unfold NK_CHUNK_LEN, NK_SIZE; lia)). }
  assert (HRp : region_ok SEGS (ewset (ewset (ewset E 512 w0) 520 (Z_to_bv 64 (LA_G_NL + NK_CHUNK_LEN + 8 * nk_next bs)))
                  521 (Z_to_bv 64 (rv_clen c))) (rdW W (ms_mem ms1)) rv_pR).
  { unfold region_ok, rv_pR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ewset ew Nat.eqb].
    rewrite Up. split; [unfold LA_G_NL, NK_CHUNK_LEN; lia|]. split; [unfold LA_G_NL, NK_CHUNK_LEN; lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ _ 0 8 (SOff 521 0) (rv_clen c)); [rv_den | rv_zrng | rv_zrng | exact Vcl]. }
  assert (HDp : all_disjoint (ewset (ewset (ewset E 512 w0) 520 (Z_to_bv 64 (LA_G_NL + NK_CHUNK_LEN + 8 * nk_next bs)))
                  521 (Z_to_bv 64 (rv_clen c))) rv_pR [rv_fr_e; got_regionP; bcell_regionP 32; rv_Ra]).
  { apply all_disjoint_of_extents. unfold rv_pR, rv_fr_e, got_regionP, bcell_regionP, rv_Ra, extent_of_region.
    change (A_OBJ 1) with 242%nat. change (A_OBJ 2) with 243%nat. change (A_OBJ 64) with 305%nat.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val ewset ew Nat.eqb].
    rewrite Up, Usp, Ugot, Ucell, Ug.
    cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold LA_G_NL, NK_CHUNK_LEN, FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in *.
    repeat split; lia. }
  pose proof (st_ok_pi_add_region _ _ _ rv_pR HS2 ltac:(vm_compute; reflexivity) HRp HDp) as HS3. clear HS2.
  pose proof (st_ok_pi_add_fact _ _ _ 520 (mkAF 0x61cac0 0x61cec0 3) HS3
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2 ewset ew Nat.eqb]; rewrite Up; unfold LA_G_NL, NK_CHUNK_LEN; lia))
    as HS4. clear HS3.
  pose proof (st_ok_pi_add_fact _ _ _ 521 (mkAF 0 4096 0) HS4
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2 ewset ew Nat.eqb]; rewrite unsigned_lit_small by lia;
          rewrite Z.pow_0_r, Z.mod_1_r; lia))
    as HS5. clear HS4.
  rv_norm HS5.
  assert (HEI2 : img_env VAL A_LIM (ewset (ewset (ewset E 512 w0) 520 (Z_to_bv 64 (LA_G_NL + NK_CHUNK_LEN + 8 * nk_next bs)))
                  521 (Z_to_bv 64 (rv_clen c))))
    by (repeat apply rv_img_ewset; first [exact HEI | unfold A_LIM; lia]).
  assert (SHOK2 : sh_ok SEGS (SOff 32 0) []
                  (ewset (ewset (ewset E 512 w0) 520 (Z_to_bv 64 (LA_G_NL + NK_CHUNK_LEN + 8 * nk_next bs)))
                    521 (Z_to_bv 64 (rv_clen c))) (mrestrict (w_H W) (ms_mem ms1))) by constructor.
  clear SHOK. rename SHOK2 into SHOK. rename HS5 into HS.
  (* +0xa4 ld s2 := chunk_len[next], to +0xa8 `bltu s2, s0` *)
  paj_run_tok RUN HS HJ SHOK Bspan; [rv_awr |].
  rv_kept HFr rv_zn UN2. clear HF HFr.
  lazymatch type of HG with mem_grows (mrestrict _ (ms_mem ms1)) _ => rename HG into HG2 end.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mm) => rename mm into ms2 end.
  assert (E521 : ew (ewset (ewset (ewset E 512 w0) 520 (Z_to_bv 64 (LA_G_NL + NK_CHUNK_LEN + 8 * nk_next bs)))
                  521 (Z_to_bv 64 (rv_clen c))) 521 = Z_to_bv 64 (rv_clen c)) by apply ew_ewset_same.
  psrr_branch_tok RUN BR HS SHOK Bspan;
    rewrite branch_ltu_U, (U_atom _ 521 (rv_clen c) E521) in Hc by lia;
    rewrite (U_atom _ 12 (rv_len c)) in Hc by (first [cbn [ewset ew Nat.eqb]; exact E12 | lia]);
    [apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc];
    (paj_run_tok RUN HS HJ SHOK Bspan; [rv_awr |]);
    rv_kept HFr rv_zn UN3; clear HF HFr;
    lazymatch type of HG with mem_grows (mrestrict _ (ms_mem ms2)) _ => rename HG into HG3 end;
    pmkst HS;
    rv_r5 HS Usp ER R2 R3 R4 R26 R27;
    prreg HS (1%bv : bv 5) R1; prreg HS (8%bv : bv 5) R8; prreg HS (9%bv : bv 5) R9;
    prreg HS (10%bv : bv 5) R10'; prreg HS (12%bv : bv 5) R12; prreg HS (18%bv : bv 5) R18;
    prreg HS (19%bv : bv 5) R19;
    pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 4 _ HS eq_refl) as HRa;
    lazymatch type of HS with st_ok _ ?E3 ?ss3 (restrict _ ?ms3) =>
      pose proof (st_ok_restrict_reg SEGS (w_H W) E3 ss3 ms3 (11%bv : bv 5) HS) as R11;
      let e := eval vm_compute in (sr_get (ss_regs ss3) (11%bv : bv 5)) in
      change (sr_get (ss_regs ss3) (11%bv : bv 5)) with e in R11;
      rewrite (rv_den_src E3 (nk_next bs)) in R11 by first [cbn [ewset ew Nat.eqb]; first [exact E34 | exact Ug] | lia];
      assert (UNc : forall a, 0 <= a < 2 ^ 64 -> ~ rv_zn a ->
                aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) (ms_mem ms) a)
        by (intros ?a ?Ha ?Hz; rewrite (UN3 _ Ha Hz), (UN2 _ Ha Hz), (UN1 _ Ha Hz); reflexivity);
      assert (HGc : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms3)))
        by (eapply mem_grows_trans; [eapply mem_grows_trans; [exact HG1 | exact HG2] | exact HG3])
    end;
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?d) _ =>
      destruct (rv_inv_next (ms_regs ms) (ms_mem ms) md r m d rv_zn HI HB HJ ltac:(rv_wvb) ltac:(rv_wvb) UNc rv_zn_g HGc
        R2 R3 R4 R26 R27) as (HI2 & HB2)
    end;
    (apply HCPY;
     [ exact HI2 | exact Hlt | exact R1
     | rewrite R10', E11; reflexivity
     | exact R11
     |
     | split; [rewrite R8, E12; reflexivity|]; split; [rewrite R9, E11; reflexivity|];
       split; [|rewrite R19, E32; reflexivity]
     | rv_vfield HRa Ug
     | apply (val_mem_kept (w_H W) (ms_mem ms)); [|exact HMI];
       intros k Hk; cbn in Hk; apply UNc; [unfold LA_G_NL, NK_MISUSE; lia|];
       unfold rv_zn, LA_G_NL, NK_NEXT, NK_MISUSE; lia
     | intros i Hi; exact (HB2 i Hi) ]).
  + (* chunk_len < len *) rewrite R12. cbn [ewset ew Nat.eqb]. reflexivity.
  + rewrite R18. cbn [ewset ew Nat.eqb]. reflexivity.
  + (* chunk_len >= len: s2 := len = chunk_len *)
    assert (Heq : rv_len c = rv_clen c) by lia.
    rewrite R12, E12, Heq. reflexivity.
  + assert (Heq : rv_len c = rv_clen c) by lia.
    rewrite R18, E12, Heq. reflexivity.
Qed.

(* a path of the entry piece ends: kept bytes, registers, rv_inv and the buffer at its end state *)
Ltac rv_path HS HI HB UN HG HF HFr HJ Usp ER :=
  rv_kept HFr rv_zg UN; clear HF HFr;
  let R2 := fresh "R2" in let R3 := fresh "R3" in let R4 := fresh "R4" in
  let R26 := fresh "R26" in let R27 := fresh "R27" in
  rv_r5 HS Usp ER R2 R3 R4 R26 R27;
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mm) =>
    let HI' := fresh "HI" in let HB' := fresh "HB" in
    destruct (rv_inv_next _ _ _ (ms_regs mm) (ms_mem mm) _ rv_zg HI HB HJ ltac:(rv_wvb) ltac:(rv_wvb) UN
      rv_zg_g HG R2 R3 R4 R26 R27) as (HI' & HB');
    clear HI HB HG UN R2 R3 R4 R26 R27; rename HI' into HI; rename HB' into HB
  end.

(* ---- THE ENTRY PIECE ---- *)
Lemma rv_entry_ok : RV_AT_ERRNO SK B c -> RV_AT_MEMCPY SK B c ->
  rv_goal SK B c (mkCfg (mkst regs0 (Z_to_bv 64 (BASE + AF_fuzz_recv)) memc (seg_rom SEGS)) (c_mdc c)).
Proof.
intros HERR HCPY.
pose proof rv_entry_st as HS.
pose proof rv_E0_ok as HE.
set (E := Eimg (Ereg regs0 (rv_xe bs))) in *. clearbody E.
pose proof (rv_env_facts _ HE) as (Ug & Ugot & Ucell & Usp & E10 & E11 & E12).
pose proof HE as (HEI & ER & E32 & E33 & E34 & E35 & E36 & E37).
pose proof rv_HJ as HJ.
destruct (rv_sp_bounds SK B c HC) as (Hceil & Hwlo & Hwhi & H47 & H16 & HXO).
destruct (rv_pre_facts SK B TL c HC) as (Hb0 & Hlen & Hamr & Hbg & Hbf & Hef & Heg & He0 & He1).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HC as (_ & HNK & WF & _).
pose proof WF as (Wnc & Wnx & _ & _ & Wop & _ & _ & Wmi & Wee & _).
unfold NL_CHUNKS in Wnc.
assert (Ha0 : 0 <= aarg regs0 0 < 2 ^ 64)
  by (unfold aarg, argZ; pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 (10 + 0)))) as Hr;
      change (bv_modulus 64) with (2 ^ 64) in Hr; lia).
unfold rv_goal.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) memc)) by constructor.
pose proof (paj_run_xe SK B LAWS (pal_env B TL) ERRF (c_G c) rv_HGX (c_XO c) (c_OUT c)) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
(* +0x00 .. +0x48: the frame, s0 := len, s1 := buf, a3 := the .got word, a1 := g, to `bne a0, 7` *)
paj_run_tok RUN HS HJ SHOK Bspan; [rv_awr |].
rv_kept HFr rv_zs UNk. clear HF HFr.
rv_r5 HS Usp ER R2 R3 R4 R26 R27.
pose proof (st_ok_pi_region _ _ _ 0 _ HS eq_refl) as HR0.
assert (HFV : Forall (fun p => val_mem SEGS (rdW W (ms_mem ms)) (rv_sp c - 96 + fst p) 8 (bv_unsigned (snd p)))
                (rv_frame_vals c)).
{ unfold rv_frame_vals. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  (eapply rv_fword; [exact HR0 | exact Usp | repeat (first [left; reflexivity | right]) | apply ER; [lia | reflexivity]]). }
clear HR0.
destruct (rv_inv_first (ms_regs ms) (ms_mem ms) _ HJ ltac:(rv_wvb) ltac:(rv_wvb) R2 R3 R4 R26 R27 HFV UNk HG)
  as (HI & HB).
clear HFV UNk HG R2 R3 R4 R26 R27.
pose proof (st_ok_pi_ro _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) as HS'. clear HS. rename HS' into HS.
rv_norm HS.
rename ms into ms0.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* a0 <> 7: +0x60..+0x6c misuse := 1, +0x70..+0x80 to `bge` *)
  rewrite branch_ne_U, (U_atom E 10 (aarg regs0 0) E10 Ha0), U_lit in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [rv_awr |].
  rv_path HS HI HB UN1 HG HF HFr HJ Usp ER.
  pose proof (st_ok_pi_region _ _ _ 4 _ HS eq_refl) as HRb.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mm) =>
    assert (HMI : val_mem SEGS (rdW W (ms_mem mm)) (LA_G_NL + NK_MISUSE) 4 (rv_msu c))
      by (replace (rv_msu c) with 1 by (unfold rv_msu, NL_FD; rewrite (proj2 (Z.eqb_neq _ _) Hc); reflexivity);
          rv_vfield HRb Ug)
  end.
  pose proof (st_ok_pi_join _ _ _ HS ltac:(vm_compute; reflexivity)) as HSj.
  exact (rv_bge_ok HERR HCPY E _ _ HE HSj HI HB HMI).
- (* a0 = 7: +0x50..+0x58 lw open, `bnez open` *)
  rewrite branch_ne_U, (U_atom E 10 (aarg regs0 0) E10 Ha0), U_lit in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [rv_awr |].
  rv_path HS HI HB UN1 HG HF HFr HJ Usp ER.
  psrr_branch_tok RUN BR HS SHOK Bspan;
    rewrite branch_ne_U, (U_atom E 36 (nk_open bs) E36), U_lit in Hc0 by lia.
  + (* open <> 0: misuse kept *)
    apply negb_true_iff, Z.eqb_neq in Hc0.
    paj_run_tok RUN HS HJ SHOK Bspan; [rv_awr |].
    rv_path HS HI HB UN2 HG HF HFr HJ Usp ER.
    pose proof (st_ok_pi_region _ _ _ 4 _ HS eq_refl) as HRb.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mm) =>
      assert (HMI : val_mem SEGS (rdW W (ms_mem mm)) (LA_G_NL + NK_MISUSE) 4 (rv_msu c))
        by (replace (rv_msu c) with (nk_misuse bs)
              by (unfold rv_msu, NL_FD; rewrite Hc, Z.eqb_refl, (proj2 (Z.eqb_neq _ _) Hc0); reflexivity);
            rv_vfield HRb Ug)
    end.
    pose proof (st_ok_pi_join _ _ _ HS ltac:(vm_compute; reflexivity)) as HSj.
    exact (rv_bge_ok HERR HCPY E _ _ HE HSj HI HB HMI).
  + (* open = 0: misuse := 1 *)
    apply negb_false_iff, Z.eqb_eq in Hc0.
    paj_run_tok RUN HS HJ SHOK Bspan; [rv_awr |].
    rv_path HS HI HB UN2 HG HF HFr HJ Usp ER.
    pose proof (st_ok_pi_region _ _ _ 4 _ HS eq_refl) as HRb.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mm) =>
      assert (HMI : val_mem SEGS (rdW W (ms_mem mm)) (LA_G_NL + NK_MISUSE) 4 (rv_msu c))
        by (replace (rv_msu c) with 1 by (unfold rv_msu, NL_FD; rewrite Hc, Hc0; reflexivity);
            rv_vfield HRb Ug)
    end.
    pose proof (st_ok_pi_join _ _ _ HS ltac:(vm_compute; reflexivity)) as HSj.
    exact (rv_bge_ok HERR HCPY E _ _ HE HSj HI HB HMI).
Qed.
End cc.

(* THE COMPOSITION: fuzz_recv's contract from the entry piece and the statements RV_AT_ERRNO, RV_AT_MEMCPY of the
   part files (lib/A/Prog/fuzz_recv.v gives them from fuzz_recv_err.v, fuzz_recv_cp.v and the pieces behind) *)
Theorem rv_compose :
  (forall c, rv_call SK B c -> RV_AT_ERRNO SK B c) ->
  (forall c, rv_call SK B c -> RV_AT_MEMCPY SK B c) ->
  forall rlo rhi, fuzz_recv_acontract SK SEGS rlo rhi B.
Proof.
intros HERR HCPY rlo rhi. unfold fuzz_recv_acontract, aleaf.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HP.
destruct HP as (bs & HP).
pose (c := mkRVC G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bs rlo rhi).
assert (HC : rv_call SK B c) by exact (conj HA HP).
replace (cfg_at SEGS FUZZ_RECV_A regs memc mdc)
  with (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_fuzz_recv)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, FUZZ_RECV_A, AF_fuzz_recv; rewrite (lv_text LV); reflexivity).
exact (rv_entry_ok c HC (HERR c HC) (HCPY c HC)).
Qed.
End w.
