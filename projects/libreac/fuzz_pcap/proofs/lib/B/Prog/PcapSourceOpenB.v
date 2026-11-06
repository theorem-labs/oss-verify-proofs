From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h YC85 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PSourceMeter PFclose PFmemopenISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapFuzzFopenDefs PcapSourceOpenDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceOpenPh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the pcs of the tail, as listing offsets (address - 0x80788) ---- *)
Definition OP_SHORT : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_open + 0x220) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.   (* 0x81400 `lbu a0,0(s8)`: the target of 0x8138c `bne a0,s9` (short read) *)
Definition OP_BAD : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_open + 0x264) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.     (* 0x81444 `lbu a0,0(s8)`: the target of 0x813d4 `bne a0,a1` (bad magic) *)
Definition OP_EPI : Z := Eval compute in ((Symbols.AsanUbsan.s_pcap_source_open + 0x284) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.     (* 0x81464 `addi a1,zero,-8`: the epilogue with the buffer in scope *)
Lemma OP_TAIL_pin : pcap_text + OP_SHORT = (symaddr (Symbols.AsanUbsan.s_pcap_source_open + 0x220)%Z) /\ pcap_text + OP_BAD = (symaddr (Symbols.AsanUbsan.s_pcap_source_open + 0x264)%Z) /\ pcap_text + OP_EPI = (symaddr (Symbols.AsanUbsan.s_pcap_source_open + 0x284)%Z).
Proof. repeat split; reflexivity. Qed.

(* ---- the symbolic states of the tail ---------------------------------------------------------------------- *)
(* Atoms: the registers at the cut are atoms 0..31; the extra atoms are 32 the shadow base, 33 the frame's flag
   address FL, 34..37 the four header bytes, 38 the caller's ra, 39..48 the caller's s0, s1, s2..s9 (the machine
   frame's saved values, 0x811e8..0x81210), 49 ps->f. *)
Definition SB_OP : Z := 0x7fff8000.
Definition OBx : sv := SOff 32 0.
Definition OPspan : Z * Z := (SB_OP, SB_OP + 2 ^ 44 - 1).
Definition op_extra (FL c0 c1 c2 c3 f : Z) (regs : bvmap 5 word) : list word :=
  [w64 SB_OP; w64 FL; w64 c0; w64 c1; w64 c2; w64 c3; getr regs 1; getr regs 8; getr regs 9;
   getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25;
   w64 f].
(* The machine frame (0x811e0 `addi sp,sp,-0x60`), based at s0 = the entry sp: ra at -8, s0 at -16, s1 at -24,
   s2 .. s9 at -32 .. -88. Read only: the tail only restores from it (0x81508..0x81530). *)
Definition mf_chunks : list YP09.chunk :=
  [YP09.mkChunk (-8) (CVal 8 (SOff 38 0)); YP09.mkChunk (-16) (CVal 8 (SOff 39 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 40 0)); YP09.mkChunk (-32) (CVal 8 (SOff 41 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 42 0)); YP09.mkChunk (-48) (CVal 8 (SOff 43 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 44 0)); YP09.mkChunk (-64) (CVal 8 (SOff 45 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 46 0)); YP09.mkChunk (-80) (CVal 8 (SOff 47 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 48 0))].
Definition r_mf : YP09.region := YP09.mkRegion (Some 8%nat) (-96) 0 0 0 mf_chunks.
(* The frame F (s2 = s6, atom 18): its first word, written with the retired magic (0x8147c), and its last word,
   the flag address (0x814c8). *)
Definition r_F0 : YP09.region := YP09.mkRegion (Some 18%nat) 0 8 0 8 [].
Definition r_F120 : YP09.region := YP09.mkRegion (Some 18%nat) 120 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 33 0))].
(* F's 16 shadow bytes (s5, atom 21), the flag byte (atom 33). *)
Definition r_SH : YP09.region := YP09.mkRegion (Some 21%nat) 0 16 0 16 [].
Definition r_FL : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 1 [].
(* The caller's struct ps (s3, atom 19), f at +0. *)
Definition r_ps (wlo whi : Z) : YP09.region := YP09.mkRegion (Some 19%nat) 0 24 wlo whi [YP09.mkChunk 0 (CVal 8 (SOff 49 0))].
(* The first four bytes of the header buffer F + 32 (s4, atom 20), read at 0x81398..0x813a4. *)
Definition r_hdr : YP09.region := YP09.mkRegion (Some 20%nat) 0 4 0 0
  [YP09.mkChunk 0 (CVal 1 (SOff 34 0)); YP09.mkChunk 1 (CVal 1 (SOff 35 0));
   YP09.mkChunk 2 (CVal 1 (SOff 36 0)); YP09.mkChunk 3 (CVal 1 (SOff 37 0))].

(* The epilogue's state (0x813f8 or 0x81464 .. 0x81538): s6 is read as s2 (one base atom for F). *)
Definition epi_sr : list sv := sr_set sr_atoms 22%bv (SOff 18 0).
Definition epi_facts : facts :=
  mkFacts [(18%nat, HPTR 6); (33%nat, HPTR 0); (21%nat, mkAF SB_OP (SB_OP + 2 ^ 44) 3)] [] [].
Definition ss_epi (pc : Z) : sstate := mkSS pc epi_sr [r_mf; r_F0; r_F120; r_SH; r_FL] None epi_facts.

(* The token states of the read cut and of the two fclose paths (0x8138c, 0x81400, 0x81444): s4 = F + 32 (atom
   20), s7 the shadow base (atom 32), s8 = ps's shadow, computed as the head's `srli s8,s3,3; add s8,s8,s7`
   (0x81308, 0x8130c) computes it, so that the shadow checks of ps (0x81400, 0x81410, 0x81444, 0x81454) and of
   ps + 8 (0x813dc..0x813e4, 0x81424..0x8142c) are decided by ps's shadow entry; s9 = 24 (0x81380). Every window is
   empty: until a path splits, the memory is the cut's. *)
Definition op_sr (s4 s9 : sv) : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 22%bv (SOff 18 0)) 23%bv (SOff 32 0))
    24%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 32 0))) 20%bv s4) 25%bv s9.
Definition rd_sr : list sv := op_sr (SOff 20 0) (SLit 24).
Definition rd_facts : facts :=
  mkFacts [(18%nat, HPTR 6); (19%nat, HPTR 3); (20%nat, mkAF 4128 140737479966752 5); (32%nat, mkAF SB_OP SB_OP 0)] [] [].
Definition ss_rd (pc : Z) : sstate := mkSS pc rd_sr [r_mf; r_ps 0 0; r_F120] None rd_facts.
Definition rd_SH : list shent := [mkSHE 19 0 24].

Lemma wvb_fds_fs : forall l X m, m_fds (with_vm_backing l X m) = m_fds m /\ m_fs (with_vm_backing l X m) = m_fs m.
Proof. intros l X [fd [maps lazy mat] io fs proc lim tm]. split; reflexivity. Qed.

Lemma w64_unsigned : forall x : word, w64 (bv_unsigned x) = x.
Proof. intros x. unfold w64. apply Z_to_bv_bv_unsigned. Qed.

Lemma w64_m1 : w64 (-1) = Z_to_bv 64 18446744073709551615.
Proof. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.


Lemma div8_of_mul64 : forall a, a mod 64 = 0 -> a / 8 = 8 * (a / 64) /\ a = 64 * (a / 64).
Proof.
intros a H. pose proof (Z_div_mod_eq_full a 64) as E. rewrite H, Z.add_0_r in E. split; [|exact E].
symmetry. apply (Z.div_unique a 8 (8 * (a / 64)) 0); [left; lia | lia].
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Section d.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation VAL := (@pa_val _ pcap_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* A symbolic state over a machine state given by its fields (pa_entry_st_ok_full's form, for a mid-walk state). *)
Lemma pa_mid_st_ok : forall E pc sr (rs : smem) (G : facts) H (ms : machine_state),
  ms_fregs ms = fp_regs -> ms_pc_val ms = Z_to_bv 64 (BASE + pc) -> ms_svc_pending ms = None -> ms_resv ms = None ->
  ms_fcsr ms = fp_csr -> ms_rom ms = seg_rom SEGS ->
  regs_ok E sr (ms_regs ms) -> regions_wf rs = true -> Forall (region_ok SEGS E (mrestrict H (ms_mem ms))) rs ->
  pairwise_disjoint E rs -> facts_ok E G ->
  st_ok_pi SEGS VAL E (mkSS pc sr rs None G) (restrict H ms).
Proof.
intros E pc sr rs G H ms H1 H2 H3 H4 H5 H6 Hsr Hwf Hrs Hpd HG.
unfold st_ok_pi, abs_ss, setpc, st_ok. cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem
  ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
split; [exact Hsr|]. split; [| exact HG]. split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
Qed.

Lemma ly_F_journal : forall B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  (forall c q, frame_addr ly' c q = frame_addr ly c q) /\ (forall c q, flag_addr ly' c q = flag_addr ly c q).
Proof.
intros B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k (_ & Hly & _).
destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr, flag_addr. rewrite EF. split; reflexivity.
Qed.

(* ---- the stream predicates read only their footprint ---------------------- *)
Lemma vm_frame : forall (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte SEGS m' x = mbyte SEGS m x) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v Hfr Hv k Hk. rewrite Hfr by lia. exact (Hv k Hk). Qed.

Ltac vmf Hfr H := eapply vm_frame; [| exact H]; intros ?x ?Hx; apply Hfr.

Lemma asource_none_frame : forall K (m m' : word -> option byte),
  (forall a, asrc_env_addr K a -> mbyte SEGS m' a = mbyte SEGS m a) ->
  asource_none SEGS K m -> asource_none SEGS K m'.
Proof.
intros K m m' Hfr ((Hth & Hnl & Hlk & Hmode & Hms & (cv & Hcv & Hc)) & Hhead).
unfold asource_none, asrc_stdio_env, as_ofl_head in *.
split; [split; [|split; [|split; [|split; [|split]]]]|].
- vmf Hfr Hth. unfold asrc_env_addr. cbn in Hx. lia.
- vmf Hfr Hnl. unfold asrc_env_addr. cbn in Hx. lia.
- vmf Hfr Hlk. unfold asrc_env_addr. cbn in Hx. lia.
- apply (garr8_frame SEGS m m' _ _ Hmode). intros x Hx. apply Hfr. unfold asrc_env_addr.
  cbn [length src_mode_Z app] in Hx. cbn in Hx. lia.
- apply (garr8_frame SEGS m m' _ _ Hms). intros x Hx. apply Hfr. unfold asrc_env_addr.
  cbn [length src_modeset_Z app] in Hx. cbn in Hx. lia.
- exists cv. split; [exact Hcv|]. vmf Hfr Hc. unfold asrc_env_addr. cbn in Hx. lia.
- vmf Hfr Hhead. unfold asrc_env_addr. cbn in Hx. lia.
Qed.

Lemma asource_at_frame : forall K (m m' : word -> option byte) f b C p,
  (forall a, (f <= a < f + SRC_FILE_BLOCK) \/ (b <= a < b + Z.of_nat (length C)) \/ asrc_env_addr K a ->
     mbyte SEGS m' a = mbyte SEGS m a) ->
  asource_at SEGS K m f b C p -> asource_at SEGS K m' f b C p.
Proof.
intros K m m' f b C p Hfr (Wn & cpos & fl & md & H). cbv zeta in H.
destruct H as (Hp0 & Hp1 & Hp2 & Hn63 & Hwrap & Hcp & HW & Hbok & Hgb & Hst & Hwin & Hfl & Hfl24 & Hmd & Hcpos & Henv & Hhead & Hf0).
assert (HF : forall x, f <= x < f + SRC_FILE_BLOCK -> mbyte SEGS m' x = mbyte SEGS m x) by (intros x Hx; apply Hfr; left; exact Hx).
assert (HE : forall x, asrc_env_addr K x -> mbyte SEGS m' x = mbyte SEGS m x) by (intros x Hx; apply Hfr; right; right; exact Hx).
destruct Hst as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S168 &
  S18 & S19 & S20 & Sf & Sal & Sb & Sdisj).
exists Wn, cpos, fl, md. cbv zeta.
split; [exact Hp0|]. split; [exact Hp1|]. split; [exact Hp2|]. split; [exact Hn63|]. split; [exact Hwrap|].
split; [exact Hcp|]. split; [exact HW|].
split; [exact Hbok|].
split; [apply (garr8_frame SEGS m m' _ _ Hgb); intros x Hx; apply Hfr; right; left; exact Hx|].
split.
{ unfold source_static, SRC_COOKIE_OFF, SRC_BUF_OFF, SRC_BUFSIZ, SRC_MODE_R, U32M1 in *.
  split; [vmf HF S1; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S2; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S3; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S4; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S5; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S6; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S7; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S8; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S9; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S10; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S11; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S12; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S13; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S14; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S15; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S16; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S17; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S168; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S18; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S19; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S20; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [exact Sf|]. split; [exact Sal|]. split; [exact Sb | exact Sdisj]. }
split.
{ unfold source_window, SRC_BUF_OFF, SRC_BUFSIZ in *. destruct Hwin as [(-> & W1 & W2) | (i & Hi0 & Hi1 & W1 & W2 & W3)].
  - left. split; [reflexivity|]. split; [vmf HF W1 | vmf HF W2]; unfold SRC_FILE_BLOCK; cbn in Hx; lia.
  - right. exists i. split; [exact Hi0|]. split; [exact Hi1|].
    split; [vmf HF W1; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
    split; [vmf HF W2; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
    apply (garr8_frame SEGS m m' _ _ W3). intros x Hx. apply HF. unfold SRC_FILE_BLOCK. lia. }
split.
{ unfold source_flags in *. destruct Hfl as [Hfl1 Hfl2]. split; [|exact Hfl2]. vmf HF Hfl1. unfold SRC_FILE_BLOCK. cbn in Hx. lia. }
split; [exact Hfl24|].
split.
{ unfold source_mode in *. destruct Hmd as [Hmd1 Hmd2]. split; [|exact Hmd2]. vmf HF Hmd1. unfold SRC_FILE_BLOCK. cbn in Hx. lia. }
split; [vmf HF Hcpos; unfold SRC_COOKIE_OFF, SRC_FILE_BLOCK in *; cbn in Hx; lia|].
split.
{ unfold asrc_stdio_env in *. destruct Henv as (Hth & Hnl & Hlk & Hmode & Hms & (cv & Hcv & Hc)).
  split; [vmf HE Hth; unfold asrc_env_addr; cbn in Hx; lia|].
  split; [vmf HE Hnl; unfold asrc_env_addr; cbn in Hx; lia|].
  split; [vmf HE Hlk; unfold asrc_env_addr; cbn in Hx; lia|].
  split; [apply (garr8_frame SEGS m m' _ _ Hmode); intros x Hx; apply HE; unfold asrc_env_addr; cbn in Hx; lia|].
  split; [apply (garr8_frame SEGS m m' _ _ Hms); intros x Hx; apply HE; unfold asrc_env_addr; cbn in Hx; lia|].
  exists cv. split; [exact Hcv|]. vmf HE Hc. unfold asrc_env_addr. cbn in Hx. lia. }
split; [vmf HE Hhead; unfold asrc_env_addr, as_ofl_head in *; cbn in Hx; lia | exact Hf0].
Qed.

Lemma ra_frame : forall (rd rd' : Z -> option Z) a n,
  range_addressable rd SHADOW_OFF a n ->
  (forall x, a <= x < a + n -> rd' (shadow_of_addr SHADOW_OFF x) = rd (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable rd' SHADOW_OFF a n.
Proof. intros rd rd' a n HR Hk x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s. rewrite Hk by exact Hx. split; [exact Hs | exact Ho]. Qed.

Section e.
Variable B : asyms.
Variable K : asource_syms.
Variable MT : ameter_ops.
Variable FM_RA : Z.
Variable CTX : list (list Z).
Variable roimg : (word -> option byte) -> Prop.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Hypothesis FM : asrc_file_meter SK SEGS B MT.
Variables ra_fc1 ra_fc2 : Z.
(* The fclose wrapper's contract (lib/A/Stdio/PFclose.v's image-generic afclose_source_spec at this image), as in
   PcapSourceClose.v:203; its data-buffer premise comes from op_pre's input block. *)
Hypothesis AFCLOSE : afclose_source_spec SK SEGS B K (SIGMA PS___interceptor_trampoline_fclose) ra_fc1 ra_fc2
  pa_relro_lo pa_relro_hi.
Hypothesis HUfc1 : In [pc_free_ra0 (as_code B); ra_fc1] (as_universe B).
Hypothesis HUfc2 : In [pc_free_ra0 (as_code B); ra_fc2] (as_universe B).
Hypothesis ASIL : asource_img_laws SK SEGS B K.
Let RUN := paj_run (PI := PI) B LAWS.
Let RUNTO := paj_run_to (PI := PI) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_pcap) (PI := PI).
Let RUNF := aj_flag_store_pi (PL := PL_pcap) (PI := PI) B LAWS ML ASF FFL.

(* ---- the epilogue --------------------------------------------------------------------------------------- *)
(* The symbolic state of the epilogue from the facts every path has there. *)
Lemma epi_entry : forall (cx : ocx) fpos ly3 S3 W3 (ms : machine_state) md3 kk pc,
  op_pre SK B K MT FM_RA CTX roimg cx ->
  ajournal SEGS B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
    ((OP_CID, fpos) :: o_own cx) ly3 S3 W3 (ms_mem ms) md3 kk ->
  ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs ->
  ms_fcsr ms = fp_csr -> ms_pc_val ms = w64 (BASE + pc) ->
  getr (ms_regs ms) 8 = w64 (spZ (o_regs cx)) -> getr (ms_regs ms) 18 = w64 (oF cx fpos) ->
  getr (ms_regs ms) 22 = w64 (oF cx fpos) -> getr (ms_regs ms) 21 = w64 (oSH cx fpos) ->
  rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (o_regs cx) - 8) = Some (raZ (o_regs cx)) ->
  (forall j, 0 <= j < 10 ->
     rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (o_regs cx) - 16 - 8 * j) =
     Some (bv_unsigned (getr (o_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))) ->
  rdword (aview SEGS (w_H W3) (ms_mem ms)) (oF cx fpos + OP_FLAGPTR) = Some (oFL cx fpos) ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms) (op_extra (oFL cx fpos) 0 0 0 0 0 (o_regs cx)))) (ss_epi pc)
    (restrict (w_H W3) ms).
Proof.
intros cx fpos ly3 S3 W3 ms md3 kk pc HPRE HJ Hrv Hsvc Hrom Hfr Hfcsr Hpc R8 R18 R22 R21 Hra Hsav HFL.
destruct cx as [STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos].
unfold oSH, oFL, oF, op_pre in *. cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k
  o_regs o_ch o_ps o_n o_b o_M o_C o_cid o_pos] in *.
destruct HPRE as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _).
pose proof HJ as (HAR3 & _ & _ & _ & _ & Hfrs3 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct (ly_F_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [EFA3 EFL3].
destruct (ly_F_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as [EFAc EFLc].
assert (EFA : forall c q, frame_addr ly3 c q = frame_addr lyc c q) by (intros c q; rewrite EFA3, EFAc; reflexivity).
assert (EFL : forall c q, flag_addr ly3 c q = flag_addr lyc c q) by (intros c q; rewrite EFL3, EFLc; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TPCAP_SOURCE_OPEN_STK = 18736) by reflexivity.
unfold OP_CID in *.
assert (Hin3 : In (1, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms) md3 1 fpos HAR3 Hin3) as (HF4096 & HFceil & HFapp).
pose proof (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms) md3 1 fpos HAR3 Hin3) as (HFa64 & _ & _).
destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms) md3 1 fpos HAR3 Hin3) as (_ & _ & HFpres & HFSpres).
destruct (FFL ly3 S3 W3 (ms_mem ms) md3 1 fpos HAR3 Hin3) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & _ & HFLceil)).
rewrite EFA in HF4096, HFceil, HFapp, HFa64, HFpres, HFSpres. rewrite EFL in HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLceil.
set (F := frame_addr lyc 1 fpos) in *. set (FL := flag_addr lyc 1 fpos) in *.
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in HFSpres.
unfold in_app, app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, HFLapp.
assert (HFLF : FL + 1 <= F \/ F + 128 <= FL).
{ destruct (Z_lt_ge_dec FL F) as [H|H]; [left; lia|].
  destruct (Z_lt_ge_dec FL (F + 128)) as [H'|H']; [|right; lia].
  exfalso. apply (proj2 (HFpres FL ltac:(lia))). exact HFLo. }
assert (HF8 : (SHADOW_OFF + F / 8) mod 8 = 0).
{ unfold SHADOW_OFF. pose proof (Z_div_mod_eq_full F 64) as D. rewrite HFa64, Z.add_0_r in D.
  assert (F / 8 = 8 * (F / 64)) as ->.
  { rewrite D at 1. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z.div_mul. lia. }
  rewrite Z.add_mod by lia. rewrite (Z.mul_comm 8), Z.mod_mul by lia. reflexivity. }
assert (HF8b : 0 <= F / 8 /\ F / 8 + 16 <= 2 ^ 44).
{ split; [apply Z.div_pos; lia|]. assert (F / 8 <= (2 ^ 47 - 128) / 8) by (apply Z.div_le_mono; lia).
  change ((2 ^ 47 - 128) / 8) with (2 ^ 44 - 16) in H. lia. }
set (E := Eimg (Ereg (ms_regs ms) (op_extra FL 0 0 0 0 0 regs))).
assert (EL : forall nn, (nn < A_TEXT)%nat -> ew E nn = ew (Ereg (ms_regs ms) (op_extra FL 0 0 0 0 0 regs)) nn)
  by (intros nn Hn; subst E; apply Eimg_low; exact Hn).
assert (EX : forall j, (j < 18)%nat -> ew E (32 + j) = nth j (op_extra FL 0 0 0 0 0 regs) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E8 : ew E 8 = w64 (spZ regs)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 8 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = w64 F) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 18 18%bv eq_refl); exact R18).
assert (E21 : ew E 21 = w64 (SHADOW_OFF + F / 8)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 21 21%bv eq_refl); exact R21).
assert (E33 : ew E 33 = w64 FL) by exact (EX 1%nat ltac:(lia)).
assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply u64_range).
assert (U8 : bv_unsigned (ew E 8) = spZ regs) by (rewrite E8; apply unsigned_lit_small; exact Hsp64).
assert (U18 : bv_unsigned (ew E 18) = F) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF + F / 8) by (rewrite E21; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = FL) by (rewrite E33; apply unsigned_lit_small; lia).
assert (Hsp_lo : alloc_ceiling + 18736 <= spZ regs) by lia.
assert (Hsp_hi : spZ regs <= 2 ^ 47) by lia.
assert (EXa : forall a, (32 <= a < 50)%nat -> ew E a = nth (a - 32) (op_extra FL 0 0 0 0 0 regs) (Z_to_bv 64 0))
  by (intros a Ha; replace a with (32 + (a - 32))%nat at 1 by lia; apply EX; lia).
assert (HSV : forall j, (j < 11)%nat ->
  val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (spZ regs + (-8 - 8 * Z.of_nat j)) 8 (bv_unsigned (ew E (38 + j)))).
{ intros j Hj. apply (val_mem_of_rdword SEGS). rewrite (EXa (38 + j)%nat ltac:(lia)).
  replace (38 + j - 32)%nat with (6 + j)%nat by lia.
  destruct j as [|j].
  - cbn [nth Nat.add op_extra]. replace (spZ regs + (-8 - 8 * Z.of_nat 0)) with (spZ regs - 8) by lia. exact Hra.
  - pose proof (Hsav (Z.of_nat j) ltac:(lia)) as Hs.
    replace (spZ regs + (-8 - 8 * Z.of_nat (S j))) with (spZ regs - 16 - 8 * Z.of_nat j) by lia. rewrite Hs. f_equal.
    do 10 (destruct j as [|j]; [reflexivity|]). lia. }
assert (HB : forall j, 0 <= bv_unsigned (ew E j) < 2 ^ 64) by (intros j; apply u64_range).
apply (ast_ok_pi_set_reg_fp E (mkSS pc sr_atoms [r_mf; r_F0; r_F120; r_SH; r_FL] None epi_facts) _ 22%bv (SOff 18 0));
  [| vm_compute; reflexivity | cbn [sv_denot ms_regs restrict]; rewrite E18, R22; unfold w64; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned].
apply pa_mid_st_ok; [exact Hfr | exact Hpc | exact Hsvc | exact Hrv | exact Hfcsr | exact Hrom
  | apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | | | ].
- unfold r_mf, r_F0, r_F120, r_SH, r_FL, mf_chunks.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff ?a 0))) =>
      let j := eval cbv in (a - 38)%nat in
      apply (chunk_ok_val SEGS E _ (spZ regs) o 8 (SOff a 0) (bv_unsigned (ew E a)));
      [ cbn [sv_denot]; rewrite Z.add_0_r; reflexivity | exact (HB a) | lia
      | replace (spZ regs + o) with (spZ regs + (-8 - 8 * Z.of_nat j)) by (simpl; lia); exact (HSV j ltac:(lia)) ] end.
  + rewrite U18. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (F + o) ltac:(lia))).
  + rewrite U18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ F 120 8 (SOff 33 0) FL);
    [ cbn [sv_denot]; rewrite E33, Z.add_0_r; apply Z_to_bv_bv_unsigned | lia | lia |].
    exact (val_mem_of_rdword SEGS _ _ _ _ HFL).
  + rewrite U21. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). unfold shadow_addr in HFSpres. exact (proj1 (HFSpres o ltac:(lia))).
  + rewrite U33. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. replace (FL + o) with FL by lia. apply (apresent_writable SEGS). exact HFLp.
- apply pairwise_disjoint_of_extents. unfold r_mf, r_F0, r_F120, r_SH, r_FL, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U8, U18, U21, U33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold SHADOW_OFF in *.
  revert Hsp_lo Hsp_hi C1 HF4096 HFceil HFapp HFLapp HFL4096 HFLceil HFLF HF8b. clear. intros. repeat split; lia.
- split; [|split; exact I]. cbn [epi_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
  rewrite U18, U33, U21. change (2 ^ 6) with 64. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
  unfold SB_OP, SHADOW_OFF in *.
  revert C1 HF4096 HFceil HFa64 HFL4096 HFLceil HF8 HF8b. clear. intros.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

Ltac epi_wr U18 U21 U33 EFA EFL F FL fpos :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); cbn [ss_epi ss_mem In] in Hin; unfold r_mf, r_F0, r_F120, r_SH, r_FL in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U18, ?U21, ?U33 in Hr|]);
  [ lia
  | left; right; right; right; exists 1, fpos; split; [left; reflexivity|]; left;
    unfold in_zr; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes 1) with 128; fold F; lia
  | lia
  | left; right; right; right; exists 1, fpos; split; [left; reflexivity|]; right;
    unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes 1 / 8) with 16; fold F; lia
  | right; rewrite EFL; fold FL; lia
  | destruct Hin ].
Ltac epi_flag EFL FL U33 :=
  let msr := fresh "msr" in let HSr := fresh "HSr" in let HR := fresh "HR" in let V := fresh "V" in
  let V0 := fresh "V0" in
  intros msr HSr; rewrite EFL; fold FL;
  lazymatch type of HSr with st_ok_pi _ _ ?Ex _ _ =>
  pose proof (st_ok_pi_region_nth Ex _ msr 4 (YP09.mkRegion (Some 33%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) HSr eq_refl) as HR;
  pose proof (field_of_region Ex (ms_mem msr) 33 FL _ 0 1 0 1 0 1%N (SLit 0) 0 HR U33 ltac:(left; reflexivity) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)) as V end;
  pose proof (V 0%nat ltac:(lia)) as V0; rewrite !Z.add_0_r in V0; exact V0.
Ltac epi_cont a0tac RET Hcont LAWS Hraw U8 U18 U21 U33 F FL E38 E8 E3 E4 E26 E27 E39 E40 E41 E42 E43 E44 E45 E46 E47 E48 :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msc) |- _ =>
  lazymatch goal with HFr : frame_of _ (ss_mem ?ss0) (mrestrict _ (ms_mem ?ms0)) _ |- _ =>
  let Q1 := fresh "Q1" in
  prreg HS (1%bv : bv 5) Q1;
  eapply (RET _ _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)); intros ?mat';
  rewrite Q1, E38, Hraw;
  apply Hcont;
  [ apply (ajournal_materialize _ _ LAWS pa_segs_low); assumption
  | apply aregs_preserved_eqs;
    lazymatch goal with |- getr _ ?r = _ =>
      let Qr := fresh "Qr" in prreg HS r Qr; rewrite Qr;
      first [ exact E8 | exact E3 | exact E4 | exact E26 | exact E27 | exact E39 | exact E40 | exact E41 | exact E42
            | exact E43 | exact E44 | exact E45 | exact E46 | exact E47 | exact E48 ] end
  | let Q10 := fresh "Q10" in prreg HS (10%bv : bv 5) Q10; rewrite Q10; a0tac
  | let a := fresh "a" in let Ha := fresh "Ha" in let Hn1 := fresh "Hn1" in let Hn2 := fresh "Hn2" in
    let Hn3 := fresh "Hn3" in
    intros a Ha Hn1 Hn2 Hn3;
    apply (kept_of_frame (segs := SEGS) Ex (ss_mem ss0) (w_H _) (ms_mem ms0) (ms_mem msc)
             (fun a => (F <= a < F + 8) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16) \/ a = FL) HFr);
    [ let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let aa := fresh "aa" in
      let HinW := fresh "HinW" in let HrrW := fresh "HrrW" in let HqW := fresh "HqW" in
      intros bb wlo whi aa HinW HrrW; vm_compute in HinW;
      repeat (destruct HinW as [HqW | HinW];
              [injection HqW as <- <- <-; cbn [base_val] in HrrW; rewrite ?U8, ?U18, ?U21, ?U33 in HrrW; lia|]);
      destruct HinW
    | exact Ha
    | intros [?H|[?H|?H]]; [exact (Hn1 H) | exact (Hn2 H) | exact (Hn3 H)] ]
  | rewrite !(proj1 (wvb_fds_fs _ _ _)); reflexivity
  | rewrite !(proj2 (wvb_fds_fs _ _ _)); reflexivity ]
  end end.

(* The epilogue, from the empty input's cut 0x813f8 (a0 := -1, `j 0x81474`) or from 0x81464 (the buffer out of
   scope, 3 shadow bytes 0xf8): the retired magic at F (0x8147c); 0x81480 `beqz s2` NOT taken (s2 = F >= 4096,
   atom 18's fact), so the machine-frame arm 0x814d4..0x81500 is dead; the 16 shadow bytes 0xf5 (0x81484..0x814c4);
   the flag through `ld a1,0x78(s2)` and `sb zero,0(a1)` (0x814c8, 0x814cc), which gives the frame back
   (PcapFrame.v aj_flag_store_pi: astack_free_law, frame_flag_lawP); the restores and `ret` (0x81504..0x81538). *)
Lemma op_epi : forall (cx : ocx) fpos ly3 S3 W3 (ms : machine_state) md3 kk pc r0 (Q : world SEGS -> config -> Prop),
  op_pre SK B K MT FM_RA CTX roimg cx ->
  ajournal SEGS B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
    ((OP_CID, fpos) :: o_own cx) ly3 S3 W3 (ms_mem ms) md3 kk ->
  ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs ->
  ms_fcsr ms = fp_csr -> ms_pc_val ms = w64 (BASE + pc) ->
  (pc = OP_CUT_NULL /\ r0 = -1) \/ (pc = OP_EPI /\ getr (ms_regs ms) 10 = w64 r0) ->
  getr (ms_regs ms) 8 = w64 (spZ (o_regs cx)) -> getr (ms_regs ms) 18 = w64 (oF cx fpos) ->
  getr (ms_regs ms) 22 = w64 (oF cx fpos) -> getr (ms_regs ms) 21 = w64 (oSH cx fpos) ->
  getr (ms_regs ms) 3 = getr (o_regs cx) 3 -> getr (ms_regs ms) 4 = getr (o_regs cx) 4 ->
  getr (ms_regs ms) 26 = getr (o_regs cx) 26 -> getr (ms_regs ms) 27 = getr (o_regs cx) 27 ->
  rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (o_regs cx) - 8) = Some (raZ (o_regs cx)) ->
  (forall j, 0 <= j < 10 ->
     rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (o_regs cx) - 16 - 8 * j) =
     Some (bv_unsigned (getr (o_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))) ->
  rdword (aview SEGS (w_H W3) (ms_mem ms)) (oF cx fpos + OP_FLAGPTR) = Some (oFL cx fpos) ->
  (forall mem2 md2 regs2,
     ajournal SEGS B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
       (o_own cx) ly3 (stack_free_state OP_CID fpos S3) W3 mem2 md2 kk ->
     aregs_preserved (o_regs cx) regs2 -> getr regs2 10 = w64 r0 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (oF cx fpos <= a < oF cx fpos + 8) -> ~ (oSH cx fpos <= a < oSH cx fpos + 16) ->
        a <> oFL cx fpos -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms) a) ->
     m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
     Q W3 (mkCfg (mkst regs2 (getr (o_regs cx) 1) mem2 (seg_rom SEGS)) md2)) ->
  SRr SEGS W3 (mkCfg ms md3) Q.
Proof.
intros cx fpos ly3 S3 W3 ms md3 kk pc r0 Q HPRE HJ Hrv Hsvc Hrom Hfr Hfcsr Hpc Hr0 R8 R18 R22 R21 R3 R4 R26 R27
  Hra Hsav HFL Hcont.
pose proof (epi_entry cx fpos ly3 S3 W3 ms md3 kk pc HPRE HJ Hrv Hsvc Hrom Hfr Hfcsr Hpc R8 R18 R22 R21 Hra Hsav HFL) as HS.
destruct cx as [STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos].
unfold oSH, oFL, oF, op_pre in *. cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k
  o_regs o_ch o_ps o_n o_b o_M o_C o_cid o_pos] in *.
destruct HPRE as (HJc & _ & Hraw & _).
pose proof HJ as (HAR3 & _ & _ & _ & _ & Hfrs3 & _).
destruct (ly_F_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [EFA3 EFL3].
destruct (ly_F_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as [EFAc EFLc].
assert (EFA : forall c q, frame_addr ly3 c q = frame_addr lyc c q) by (intros c q; rewrite EFA3, EFAc; reflexivity).
assert (EFL : forall c q, flag_addr ly3 c q = flag_addr lyc c q) by (intros c q; rewrite EFL3, EFLc; reflexivity).
clear EFA3 EFL3 EFAc EFLc.
unfold OP_CID in *.
assert (Hin3 : In (1, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms) md3 1 fpos HAR3 Hin3) as (HF4096 & HFceil & _).
destruct (FFL ly3 S3 W3 (ms_mem ms) md3 1 fpos HAR3 Hin3) as (_ & _ & _ & (HFL4096 & _ & HFLceil)).
rewrite EFA in HF4096, HFceil. rewrite EFL in HFL4096, HFLceil.
set (F := frame_addr lyc 1 fpos) in *. set (FL := flag_addr lyc 1 fpos) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
change (fs_frame_bytes 1) with 128 in *.
remember (Eimg (Ereg (ms_regs ms) (op_extra FL 0 0 0 0 0 regs))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall nn, (nn < A_TEXT)%nat -> ew E nn = ew (Ereg (ms_regs ms) (op_extra FL 0 0 0 0 0 regs)) nn)
  by (intros nn Hn; subst E; apply Eimg_low; exact Hn).
assert (EX : forall a, (32 <= a < 50)%nat -> ew E a = nth (a - 32) (op_extra FL 0 0 0 0 0 regs) (Z_to_bv 64 0))
  by (intros a Ha; rewrite EL by (unfold A_TEXT; lia); replace a with (32 + (a - 32))%nat at 1 by lia;
      apply ew_Ereg_extra).
assert (ER : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> (nn < 32)%nat -> ew E nn = getr (ms_regs ms) r)
  by (intros nn r Hr Hn; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hr).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (ER 3%nat 3%bv eq_refl) by lia; exact R3).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (ER 4%nat 4%bv eq_refl) by lia; exact R4).
assert (E26 : ew E 26 = getr regs 26) by (rewrite (ER 26%nat 26%bv eq_refl) by lia; exact R26).
assert (E27 : ew E 27 = getr regs 27) by (rewrite (ER 27%nat 27%bv eq_refl) by lia; exact R27).
assert (E8 : ew E 8 = getr regs 2) by (rewrite (ER 8%nat 8%bv eq_refl) by lia; rewrite R8; unfold spZ; apply w64_unsigned).
assert (E10 : ew E 10 = getr (ms_regs ms) 10) by (apply ER; [reflexivity | lia]).
assert (E18 : ew E 18 = w64 F) by (rewrite (ER 18%nat 18%bv eq_refl) by lia; exact R18).
assert (E21 : ew E 21 = w64 (SHADOW_OFF + F / 8)) by (rewrite (ER 21%nat 21%bv eq_refl) by lia; exact R21).
assert (E33 : ew E 33 = w64 FL) by (rewrite (EX 33%nat) by lia; reflexivity).
assert (E38 : ew E 38 = getr regs 1) by (rewrite (EX 38%nat) by lia; reflexivity).
assert (E39 : ew E 39 = getr regs 8) by (rewrite (EX 39%nat) by lia; reflexivity).
assert (E40 : ew E 40 = getr regs 9) by (rewrite (EX 40%nat) by lia; reflexivity).
assert (E41 : ew E 41 = getr regs 18) by (rewrite (EX 41%nat) by lia; reflexivity).
assert (E42 : ew E 42 = getr regs 19) by (rewrite (EX 42%nat) by lia; reflexivity).
assert (E43 : ew E 43 = getr regs 20) by (rewrite (EX 43%nat) by lia; reflexivity).
assert (E44 : ew E 44 = getr regs 21) by (rewrite (EX 44%nat) by lia; reflexivity).
assert (E45 : ew E 45 = getr regs 22) by (rewrite (EX 45%nat) by lia; reflexivity).
assert (E46 : ew E 46 = getr regs 23) by (rewrite (EX 46%nat) by lia; reflexivity).
assert (E47 : ew E 47 = getr regs 24) by (rewrite (EX 47%nat) by lia; reflexivity).
assert (E48 : ew E 48 = getr regs 25) by (rewrite (EX 48%nat) by lia; reflexivity).
assert (U18 : bv_unsigned (ew E 18) = F) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF + F / 8).
{ rewrite E21. apply unsigned_lit_small. assert (0 <= F / 8 <= F) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  unfold SHADOW_OFF. lia. }
assert (U33 : bv_unsigned (ew E 33) = FL) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = spZ regs) by (rewrite E8; reflexivity).
clear HEdef EL EX ER.
destruct Hr0 as [[-> ->] | [-> R10]];
paj_run_flag_sh RUNF HS HJ;
[ lia | epi_wr U18 U21 U33 EFA EFL F FL fpos | epi_flag EFL FL U33
| epi_cont ltac:(rewrite w64_m1; reflexivity) RET Hcont LAWS Hraw U8 U18 U21 U33 F FL E38 E8 E3 E4 E26 E27 E39 E40 E41 E42 E43 E44 E45 E46 E47 E48
| lia | epi_wr U18 U21 U33 EFA EFL F FL fpos | epi_flag EFL FL U33
| epi_cont ltac:(rewrite E10; exact R10) RET Hcont LAWS Hraw U8 U18 U21 U33 F FL E38 E8 E3 E4 E26 E27 E39 E40 E41 E42 E43 E44 E45 E46 E47 E48 ].
Qed.

(* The bytes the tail writes besides ps (F's frame, its 16 shadow bytes, its flag) are none of the caller's:
   below the allocator's ceiling, outside the image, the heap blocks, the caller's frames and their shadows. *)
Lemma tail_apart : forall (cx : ocx) fpos ly3 S3 W3 mem3 md3 kk a,
  op_pre SK B K MT FM_RA CTX roimg cx ->
  ajournal SEGS B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
    ((OP_CID, fpos) :: o_own cx) ly3 S3 W3 mem3 md3 kk ->
  (oF cx fpos <= a < oF cx fpos + 128) \/ (oSH cx fpos <= a < oSH cx fpos + 16) \/ a = oFL cx fpos ->
  4096 <= a < alloc_ceiling /\ ~ in_img SEGS a /\
  (forall b m, In (b, m) (ablocks B ly3 S3) -> ~ (b <= a < b + req_size m)) /\
  (forall c q, In (c, q) (frames (o_Sc cx)) ->
     ~ in_zr a (frame_rng (o_lyc cx) (c, q)) /\ ~ in_zr a (shadow_addr (frame_addr (o_lyc cx) c q), fs_frame_bytes c / 8)).
Proof.
intros cx fpos ly3 S3 W3 mem3 md3 kk a HPRE HJ Ha.
destruct cx as [STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos].
unfold oSH, oFL, oF, op_pre in *. cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k
  o_regs o_ch o_ps o_n o_b o_M o_C o_cid o_pos] in *.
destruct HPRE as (HJc & _).
pose proof HJ as (HAR3 & _ & _ & _ & _ & Hfrs3 & _).
pose proof HJc as (_ & _ & _ & _ & _ & Hfrsc & _).
destruct (ly_F_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [EFA3 EFL3].
destruct (ly_F_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as [EFAc EFLc].
assert (EFA : forall c q, frame_addr ly3 c q = frame_addr lyc c q) by (intros c q; rewrite EFA3, EFAc; reflexivity).
assert (EFL : forall c q, flag_addr ly3 c q = flag_addr lyc c q) by (intros c q; rewrite EFL3, EFLc; reflexivity).
clear EFA3 EFL3 EFAc EFLc.
unfold OP_CID in *.
assert (Hfrs : frames S3 = (1, fpos) :: frames Sc) by (rewrite Hfrs3, Hfrsc; reflexivity).
assert (Hin3 : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 1 fpos HAR3 Hin3) as (HF4096 & HFceil & HFapp).
pose proof (frame_al64 SEGS B ly3 S3 W3 mem3 md3 1 fpos HAR3 Hin3) as (HFa64 & _ & _).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 1 fpos HAR3 Hin3) as (_ & _ & HFpres & _).
destruct (FFL ly3 S3 W3 mem3 md3 1 fpos HAR3 Hin3) as (_ & HFLo & (HFLapp & HFLimg) & (HFL4096 & _ & HFLceil)).
rewrite EFA in HF4096, HFceil, HFapp, HFa64, HFpres. rewrite EFL in HFLo, HFLapp, HFLimg, HFL4096, HFLceil.
set (F := frame_addr lyc 1 fpos) in *. set (FL := flag_addr lyc 1 fpos) in *.
change (fs_frame_bytes 1) with 128 in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, HFLapp.
destruct (div8_of_mul64 F HFa64) as [EF8 EF64].
assert (HFr : 0 <= F / 64) by (apply Z.div_pos; lia).
split; [unfold SHADOW_OFF in Ha; lia|]. split.
{ destruct Ha as [Ha | [Ha | ->]].
  - exact (frm_img SEGS B LAWS ly3 S3 W3 mem3 md3 1 fpos a HAR3 Hin3 ltac:(rewrite EFA; change (fs_frame_bytes 1) with 128; fold F; lia)).
  - intros Hi. pose proof (pa_segs_low a Hi). unfold SHADOW_OFF, kLowMemEnd in *. lia.
  - exact HFLimg. }
split.
{ intros b0 m0 Hb Hr.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 b0 m0 HAR3 Hb) as (_ & Hb4096 & Hbceil & Hbia & Hbp & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbia.
  destruct Ha as [Ha | [Ha | ->]].
  - pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 b0 m0 1 fpos HAR3 Hb Hin3) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. rewrite EFA in D. change (fs_frame_bytes 1) with 128 in D. fold F in D. lia.
  - unfold SHADOW_OFF in Ha. lia.
  - exact (proj2 (Hbp FL Hr) HFLo). }
intros c q Hcq.
assert (Hcq3 : In (c, q) (frames S3)) by (rewrite Hfrs; right; exact Hcq).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 c q HAR3 Hcq3) as (Hc4096 & Hcceil & Hcapp).
pose proof (frame_al64 SEGS B ly3 S3 W3 mem3 md3 c q HAR3 Hcq3) as (Hca64 & Hcb64 & Hcb).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 c q HAR3 Hcq3) as (_ & _ & HCpres & _).
rewrite EFA in Hc4096, Hcceil, Hcapp, Hca64, HCpres.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hcapp.
destruct (in_split _ _ Hcq) as (l2 & l3 & El).
pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 mem3 md3 (1, fpos) (c, q) [] l2 l3 HAR3
  ltac:(rewrite Hfrs, El; reflexivity)) as D.
unfold zdisjoint, frame_rng in D. cbn [fst snd] in D. rewrite !EFA in D. change (fs_frame_bytes 1) with 128 in D. fold F in D.
set (Fc := frame_addr lyc c q) in *. set (nc := fs_frame_bytes c) in *.
destruct (div8_of_mul64 Fc Hca64) as [EFc8 EFc64].
destruct (div8_of_mul64 nc Hcb64) as [Enc8 Enc64].
assert (HFcr : 0 <= Fc / 64) by (apply Z.div_pos; lia).
assert (Hncr : 1 <= nc / 64) by lia.
unfold frame_rng, in_zr, shadow_addr. cbn [fst snd]. fold Fc nc.
destruct Ha as [Ha | [Ha | ->]]; unfold SHADOW_OFF in *.
- split; lia.
- split; [lia|]. rewrite EFc8, Enc8, EF8 in *. lia.
- split.
  + intros Hr. exact (proj2 (HCpres FL Hr) HFLo).
  + lia.
Qed.

(* The kept clauses survive a run that writes only addresses in Zs, each below the ceiling, outside the image and,
   inside a block or a frame of the caller, in Ek. *)
Lemma topen_kept_upd : forall lyc Sc W memc mdc W2 m2 m2' slo shi (Ek Zs : Z -> Prop),
  AR SEGS B lyc Sc W memc mdc ->
  topen_kept SK SEGS B lyc Sc W memc W2 m2 slo shi Ek ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W2) m2' a = aview SEGS (w_H W2) m2 a) ->
  (forall a, Zs a -> a < alloc_ceiling /\ ~ in_img SEGS a /\
     (forall b m, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> Ek a) /\
     (forall cid pos, In (cid, pos) (frames Sc) ->
        (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
        Ek a)) ->
  (forall a, slo <= a < shi -> apresent (w_H W2) m2' a) ->
  topen_kept SK SEGS B lyc Sc W memc W2 m2' slo shi Ek.
Proof.
intros lyc Sc W memc mdc W2 m2 m2' slo shi Ek Zs HAR (K1 & K2 & K3 & K4 & K5 & K6) UN HZ Hp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (NZc : forall a, alloc_ceiling <= a -> ~ Zs a) by (intros a Ha HZa; pose proof (proj1 (HZ a HZa)); lia).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hn. rewrite UN by (first [lia | exact (NZc a ltac:(lia))]). exact (K1 a Ha Hn).
- intros b0 m0 i Hb Hi HnE.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m0 HAR Hb) as (_ & Hb4096 & Hbceil & _).
  rewrite UN; [exact (K2 b0 m0 i Hb Hi HnE) | lia |].
  intros HZa. apply HnE. exact (proj1 (proj2 (proj2 (HZ _ HZa))) b0 m0 Hb ltac:(lia)).
- intros a Hi Hno He Hof. pose proof (pa_segs_low a Hi) as Hr. unfold kLowMemEnd in Hr.
  rewrite UN; [exact (K3 a Hi Hno He Hof) | lia |]. intros HZa. exact (proj1 (proj2 (HZ a HZa)) Hi).
- intros cid pos a Hin Hr HnE.
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hg4096 & Hgceil & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as Hse.
  rewrite UN; [exact (K4 cid pos a Hin Hr HnE) | unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr; destruct Hr; lia |].
  intros HZa. exact (HnE (proj2 (proj2 (proj2 (HZ a HZa))) cid pos Hin Hr)).
- intros a Ha Hn Hpa. eapply (apresent_transfer SEGS); [lia | intros Him; pose proof (pa_segs_low a Him); lia | | exact (K5 a Ha Hn Hpa)].
  apply UN; [lia | exact (NZc a ltac:(lia))].
- exact Hp.
Qed.

(* The stream's environment lies in the image (asil_env). *)
Lemma src_env_img : forall a, asrc_env_addr K a -> 0x10000 <= a < pcap_img_end.
Proof. intros a Ha. exact (pa_img_range a (proj1 (asil_env _ _ _ _ ASIL a Ha))). Qed.

Lemma mo_le_open_free : forall Sc S3 fpos x, mo_le MT Sc S3 x -> x <= OPEN_METER MT ->
  mo_le MT Sc (stack_free_state OP_CID fpos S3) (OPEN_METER MT).
Proof.
intros Sc S3 fpos x H Hx. unfold stack_free_state. apply (mo_le_set_fs_r MT MLAWF).
exact (mo_le_mono MT MLAW _ _ _ _ H Hx).
Qed.

Lemma open_meter_ge : 0 <= mo_free MT /\ mo_malloc MT SRC_FILE_BLOCK <= OPEN_METER MT.
Proof.
pose proof (mo_free_nonneg MT MLAW) as H1. split; [exact H1|]. unfold OPEN_METER. lia.
Qed.

(* ---- the empty input: 0x813f8 `addi a0,zero,-1`, `j 0x81474`, the epilogue ---------------------------------- *)
Theorem op_from_null : op_from SK B K MT FM_RA CTX roimg (op_gi_null SK B K MT).
Proof.
unfold op_from. intros cx fpos ly3 S3 W3 ms3 md3 HPRE HGI.
destruct HGI as (Hpc & Hmid & Hn0 & Hab & Hnone & Hmo).
pose proof Hmid as (Hrv & Hsvc & Hrom & Hfr & Hfcsr & HJ & Hkk & Hnev & Hfrs3 & Hnin & HfsS & R2 & R8 & R9 & R18 & R19 &
  R20 & R21 & R22 & R23 & R24 & R25 & R3 & R4 & R26 & R27 & Hra & Hsav & HMG & HO10 & HO11 & HFLP & Hlsh & Hsh &
  Vf & V12 & V16 & V20 & V8 & HKEPT & Hfds & Hfs & Hmeta & Hrod & Hch).
eapply (op_epi cx fpos ly3 S3 W3 ms3 md3 (o_k cx + 1) OP_CUT_NULL (-1) _ HPRE HJ Hrv Hsvc Hrom Hfr Hfcsr Hpc
  (or_introl (conj eq_refl eq_refl)) R8 R18 R22 R21 R3 R4 R26 R27 Hra Hsav HFLP).
intros mem2 md2 regs2 HJ2 HP2 Ha0 UN Hfds2 Hfs2.
pose proof (fun a => tail_apart cx fpos ly3 S3 W3 (ms_mem ms3) md3 (o_k cx + 1) a HPRE HJ) as HAP.
destruct cx as [STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos].
unfold op_post, tpcap_source_open_post, oSH, oFL, oF, op_pre in *.
cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k
  o_regs o_ch o_ps o_n o_b o_M o_C o_cid o_pos] in *.
destruct HPRE as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & Hown & Hfa1 & Hfa2 & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & HnC & _).
pose proof HJc as (HAR & _ & _ & _ & _ & Hfrsc & _).
pose proof HJ2 as (_ & _ & _ & _ & _ & Hfrs2 & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
unfold OP_CID in *.
set (F := frame_addr lyc 1 fpos) in *. set (FL := flag_addr lyc 1 fpos) in *.
set (Zs := fun a => (F <= a < F + 8) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16) \/ a = FL).
assert (HZ : forall a, Zs a -> 4096 <= a < alloc_ceiling /\ ~ in_img SEGS a /\
  (forall b m, In (b, m) (ablocks B ly3 S3) -> ~ (b <= a < b + req_size m)) /\
  (forall c q, In (c, q) (frames Sc) ->
     ~ in_zr a (frame_rng lyc (c, q)) /\ ~ in_zr a (shadow_addr (frame_addr lyc c q), fs_frame_bytes c / 8))).
{ intros a HZa. apply HAP. unfold Zs in HZa. lia. }
assert (UN' : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha HnZ. apply UN; [exact Ha | intros H; apply HnZ; left; exact H | intros H; apply HnZ; right; left; exact H
  | intros H; apply HnZ; right; right; exact H]. }
assert (Hps : forall a, ps <= a < ps + 24 -> ~ Zs a).
{ intros a Ha HZa. destruct (HZ a HZa) as (_ & _ & _ & Hfr2). apply (proj1 (Hfr2 cid pos Hin)).
  unfold frame_rng, in_zr. cbn [fst snd]. lia. }
assert (Hps64 : forall a, ps <= a < ps + 24 -> 0 <= a < 2 ^ 64).
{ destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (H1 & H2 & _).
  pose proof asan_consts as (C1 & _). intros a Ha. lia. }
assert (MB : forall a, ps <= a < ps + 24 -> mbyte SEGS (rdW W3 mem2) a = mbyte SEGS (rdW W3 (ms_mem ms3)) a).
{ intros a Ha. apply (mbyte_of_aview SEGS). apply UN'; [exact (Hps64 a Ha) | exact (Hps a Ha)]. }
exists ly3, (stack_free_state 1 fpos S3), regs2, mem2, md2.
split; [reflexivity|].
split; [exact HP2|].
split; [rewrite Hfrs2, Hfrsc; reflexivity|].
split; [rewrite Hfds2; exact Hfds|].
split; [rewrite Hfs2; exact Hfs|].
split.
{ apply (topen_kept_upd lyc Sc W memc mdc W3 (ms_mem ms3) mem2 _ _ _ Zs HAR HKEPT UN').
  - intros a HZa. destruct (HZ a HZa) as (Ha & Hi & Hb & Hf). split; [lia|]. split; [exact Hi|]. split.
    + intros b0 m0 Hb0 Hr. exfalso. apply (Hb b0 m0); [rewrite Hab; exact Hb0 | exact Hr].
    + intros c q Hcq Hr. exfalso. destruct (Hf c q Hcq) as [Hf1 Hf2]. destruct Hr; contradiction.
  - intros a Ha. apply Hpres2. assert (HTS : TPCAP_SOURCE_OPEN_STK = 18736) by reflexivity. lia. }
split; [apply (mo_le_open_free Sc S3 fpos 0 Hmo); pose proof open_meter_ge; unfold OPEN_METER in *;
        pose proof (mo_malloc_nonneg MT MLAW SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)); lia|].
split; [vmf MB V12; lia|].
split; [vmf MB V16; lia|].
split; [vmf MB V20; lia|].
right.
split; [eapply (ajournal_mono_k SEGS B); [exact HJ2 | unfold EV_OPEN, EV_FUZZ_FOPEN; lia]|].
split; [exact Ha0|].
split; [unfold pcap_goodZ; rewrite <- HnC, Hn0; reflexivity|].
split; [vmf MB Vf; lia|].
split; [intros i Hi; rewrite UN' by (first [exact (Hps64 (ps + i) ltac:(lia)) | exact (Hps (ps + i) ltac:(lia))]); exact (V8 i Hi)|].
split; [unfold ablocks; rewrite blocks_stack_free_state; fold (ablocks B ly3 S3); rewrite Hab; apply Permutation_refl|].
apply (asource_none_frame K (rdW W3 (ms_mem ms3))); [|exact Hnone].
intros a Ha. pose proof (src_env_img a Ha) as Hk. apply (mbyte_of_aview SEGS). apply UN'; [assert (HIE : pcap_img_end = (symaddr ImgPages.AsanUbsan.top)) by reflexivity; lia|].
intros HZa. apply (proj1 (proj2 (HZ a HZa))). destruct (asil_env _ _ _ _ ASIL a Ha) as [Hi _]. exact Hi.
Qed.

Lemma shent_rd_ok : forall Ex (m : word -> option byte) ps,
  U Ex OBx = SHADOW_OFF -> U Ex (SOff 19 0) = ps ->
  (4096 <= ps /\ (ps + 24 <= kLowShadowBeg \/ kHighMemBeg <= ps)) ->
  range_addressable (YCbn.rd_of SEGS m) SHADOW_OFF ps 24 ->
  sh_ok SEGS OBx rd_SH Ex m.
Proof.
intros Ex m ps HB Hq Hz HR. unfold sh_ok, rd_SH. apply Forall_cons; [|apply Forall_nil].
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq. split.
- rewrite Z.add_0_r. exact HR.
- intros a Ha. cbn in Ha. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* The token state of a read path, at any pc with the cut's registers and memory. *)
Lemma rd_entry : forall (cx : ocx) fpos ly3 S3 W3 (ms : machine_state) md3 f pc,
  op_pre SK B K MT FM_RA CTX roimg cx ->
  op_mid SK B K cx fpos f (oF cx fpos + OP_HDR) 24 OSH_in 1 ly3 S3 W3 ms md3 ->
  ms_pc_val ms = w64 (BASE + pc) -> 0 <= f < 2 ^ 64 ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms) (op_extra (oFL cx fpos) (nth 0 (o_C cx) 0) (nth 1 (o_C cx) 0)
      (nth 2 (o_C cx) 0) (nth 3 (o_C cx) 0) f (o_regs cx)))) (ss_rd pc) (restrict (w_H W3) ms) /\
  sh_ok SEGS OBx rd_SH (Eimg (Ereg (ms_regs ms) (op_extra (oFL cx fpos) (nth 0 (o_C cx) 0) (nth 1 (o_C cx) 0)
      (nth 2 (o_C cx) 0) (nth 3 (o_C cx) 0) f (o_regs cx)))) (mrestrict (w_H W3) (ms_mem ms)).
Proof.
intros cx fpos ly3 S3 W3 ms md3 f pc HPRE Hmid Hpc Hf64.
destruct cx as [STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos].
unfold op_mid, oSH, oFL, oF, op_pre, osp1 in *. cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k
  o_regs o_ch o_ps o_n o_b o_M o_C o_cid o_pos] in *.
destruct Hmid as (Hrv & Hsvc & Hrom & Hfr & Hfcsr & HJ & Hkk & Hnev & Hfrs3 & Hnin & HfsS & R2 & R8 & R9 & R18 & R19 &
  R20 & R21 & R22 & R23 & R24 & R25 & R3 & R4 & R26 & R27 & Hra & Hsav & HMG & HO10 & HO11 & HFLP & Hlsh & Hsh &
  Vf & V12 & V16 & V20 & V8 & HKEPT & Hfds & Hfs & Hmeta & Hrod & Hch).
destruct HPRE as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & Hown & Hfa1 & Hfa2 & _ & Hps8 & Hsh0 & _).
pose proof HJ as (HAR3 & _ & _ & _ & _ & Hfrs3' & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof HJc as (HAR & _ & _ & _ & _ & Hfrsc & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct (ly_F_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [EFA3 EFL3].
destruct (ly_F_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as [EFAc EFLc].
assert (EFA : forall c q, frame_addr ly3 c q = frame_addr lyc c q) by (intros c q; rewrite EFA3, EFAc; reflexivity).
assert (EFL : forall c q, flag_addr ly3 c q = flag_addr lyc c q) by (intros c q; rewrite EFL3, EFLc; reflexivity).
clear EFA3 EFL3 EFAc EFLc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TPCAP_SOURCE_OPEN_STK = 18736) by reflexivity.
unfold OP_CID, OP_HDR in *.
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
assert (Hin3 : In (1, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (Hinc3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hin).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms) md3 1 fpos HAR3 Hin3) as (HF4096 & HFceil & HFapp).
pose proof (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms) md3 1 fpos HAR3 Hin3) as (HFa64 & _ & _).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hc4096 & Hcceil & Hcapp).
destruct (in_split _ _ Hin) as (l2 & l3 & El).
pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms) md3 (1, fpos) (cid, pos) [] l2 l3 HAR3
  ltac:(rewrite Hfrs3, El; reflexivity)) as DFc.
unfold zdisjoint, frame_rng in DFc. cbn [fst snd] in DFc. rewrite !EFA in DFc.
rewrite EFA in HF4096, HFceil, HFapp, HFa64.
set (F := frame_addr lyc 1 fpos) in *. set (FL := flag_addr lyc 1 fpos) in *.
change (fs_frame_bytes 1) with 128 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, Hcapp.
set (E := Eimg (Ereg (ms_regs ms) (op_extra FL (nth 0 C 0) (nth 1 C 0) (nth 2 C 0) (nth 3 C 0) f regs))).
assert (EL : forall nn, (nn < A_TEXT)%nat -> ew E nn = ew (Ereg (ms_regs ms) (op_extra FL (nth 0 C 0) (nth 1 C 0) (nth 2 C 0) (nth 3 C 0) f regs)) nn)
  by (intros nn Hn; subst E; apply Eimg_low; exact Hn).
assert (EX : forall a, (32 <= a < 50)%nat -> ew E a = nth (a - 32) (op_extra FL (nth 0 C 0) (nth 1 C 0) (nth 2 C 0) (nth 3 C 0) f regs) (Z_to_bv 64 0))
  by (intros a Ha; rewrite EL by (unfold A_TEXT; lia); replace a with (32 + (a - 32))%nat at 1 by lia;
      apply ew_Ereg_extra).
assert (ER : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> (nn < 32)%nat -> ew E nn = getr (ms_regs ms) r)
  by (intros nn r Hr Hn; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hr).
assert (E8 : ew E 8 = w64 (spZ regs)) by (rewrite (ER 8%nat 8%bv eq_refl) by lia; exact R8).
assert (E18 : ew E 18 = w64 F) by (rewrite (ER 18%nat 18%bv eq_refl) by lia; exact R18).
assert (E19 : ew E 19 = w64 ps) by (rewrite (ER 19%nat 19%bv eq_refl) by lia; exact R19).
assert (E20 : ew E 20 = w64 (F + 32)) by (rewrite (ER 20%nat 20%bv eq_refl) by lia; exact R20).
assert (E32 : ew E 32 = w64 SB_OP) by (rewrite (EX 32%nat) by lia; reflexivity).
assert (E33 : ew E 33 = w64 FL) by (rewrite (EX 33%nat) by lia; reflexivity).
assert (E49 : ew E 49 = w64 f) by (rewrite (EX 49%nat) by lia; reflexivity).
assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply u64_range).
assert (U8 : bv_unsigned (ew E 8) = spZ regs) by (rewrite E8; apply unsigned_lit_small; exact Hsp64).
assert (U18 : bv_unsigned (ew E 18) = F) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = ps) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = F + 32) by (rewrite E20; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SB_OP) by (rewrite E32; apply unsigned_lit_small; unfold SB_OP; lia).
assert (Hsp_lo : alloc_ceiling + 18736 <= spZ regs) by lia.
assert (Hsp_hi : spZ regs <= 2 ^ 47) by lia.
assert (HSV : forall j, (j < 11)%nat ->
  val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (spZ regs + (-8 - 8 * Z.of_nat j)) 8 (bv_unsigned (ew E (38 + j)))).
{ intros j Hj. apply (val_mem_of_rdword SEGS). rewrite (EX (38 + j)%nat ltac:(lia)).
  replace (38 + j - 32)%nat with (6 + j)%nat by lia.
  destruct j as [|j].
  - cbn [nth Nat.add op_extra]. replace (spZ regs + (-8 - 8 * Z.of_nat 0)) with (spZ regs - 8) by lia. exact Hra.
  - pose proof (Hsav (Z.of_nat j) ltac:(lia)) as Hs.
    replace (spZ regs + (-8 - 8 * Z.of_nat (S j))) with (spZ regs - 16 - 8 * Z.of_nat j) by lia. rewrite Hs. f_equal.
    do 10 (destruct j as [|j]; [reflexivity|]). lia. }
assert (HB : forall j, 0 <= bv_unsigned (ew E j) < 2 ^ 64) by (intros j; apply u64_range).
split.
- apply (ast_ok_pi_set_reg_fp E (mkSS pc (sr_set (sr_set (sr_set (sr_set sr_atoms 22%bv (SOff 18 0)) 23%bv (SOff 32 0))
      24%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 32 0))) 20%bv (SOff 20 0)) [r_mf; r_ps 0 0; r_F120] None rd_facts)
      _ 25%bv (SLit 24));
    [| vm_compute; reflexivity | cbn [sv_denot ms_regs restrict]; rewrite R25; reflexivity].
  apply (ast_ok_pi_set_reg_fp E (mkSS pc (sr_set (sr_set (sr_set sr_atoms 22%bv (SOff 18 0)) 23%bv (SOff 32 0))
      24%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 32 0))) [r_mf; r_ps 0 0; r_F120] None rd_facts)
      _ 20%bv (SOff 20 0));
    [| vm_compute; reflexivity | cbn [sv_denot ms_regs restrict]; rewrite E20, R20; unfold w64; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned].
  apply (ast_ok_pi_set_reg_fp E (mkSS pc (sr_set (sr_set sr_atoms 22%bv (SOff 18 0)) 23%bv (SOff 32 0)) [r_mf; r_ps 0 0; r_F120] None rd_facts)
      _ 24%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 32 0)));
    [| vm_compute; reflexivity | cbn [ms_regs restrict]; rewrite R24;
       rewrite (denot_shx E 19 32 0 ps SB_OP E19 E32) by (unfold SB_OP; lia); unfold w64, SB_OP, SHADOW_OFF; f_equal; f_equal; f_equal; lia].
  apply (ast_ok_pi_set_reg_fp E (mkSS pc (sr_set sr_atoms 22%bv (SOff 18 0)) [r_mf; r_ps 0 0; r_F120] None rd_facts)
      _ 23%bv (SOff 32 0));
    [| vm_compute; reflexivity | cbn [sv_denot ms_regs restrict]; rewrite E32, R23; reflexivity].
  apply (ast_ok_pi_set_reg_fp E (mkSS pc sr_atoms [r_mf; r_ps 0 0; r_F120] None rd_facts) _ 22%bv (SOff 18 0));
    [| vm_compute; reflexivity | cbn [sv_denot ms_regs restrict]; rewrite E18, R22; unfold w64; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned].
  apply pa_mid_st_ok; [exact Hfr | exact Hpc | exact Hsvc | exact Hrv | exact Hfcsr | exact Hrom
    | apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | | | ].
  + unfold r_mf, r_ps, r_F120, mf_chunks.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff ?a 0))) =>
        let j := eval cbv in (a - 38)%nat in
        apply (chunk_ok_val SEGS E _ (spZ regs) o 8 (SOff a 0) (bv_unsigned (ew E a)));
        [ cbn [sv_denot]; rewrite Z.add_0_r; reflexivity | exact (HB a) | lia
        | replace (spZ regs + o) with (spZ regs + (-8 - 8 * Z.of_nat j)) by (simpl; lia); exact (HSV j ltac:(lia)) ] end.
    * rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ ps 0 8 (SOff 49 0) f);
      [ cbn [sv_denot]; rewrite E49, Z.add_0_r; apply Z_to_bv_bv_unsigned | lia | lia |].
      rewrite Z.add_0_r. exact Vf.
    * rewrite U18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ F 120 8 (SOff 33 0) FL);
      [ cbn [sv_denot]; rewrite E33, Z.add_0_r; apply Z_to_bv_bv_unsigned
      | pose proof (FFL ly3 S3 W3 (ms_mem ms) md3 1 fpos HAR3 Hin3) as (_ & _ & _ & (Hq & _ & Hq2));
        rewrite EFL in Hq, Hq2; fold FL in Hq, Hq2; lia | lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ HFLP).
  + apply pairwise_disjoint_of_extents. unfold r_mf, r_ps, r_F120, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U8, U18, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hsp_lo Hsp_hi C1 HF4096 HFceil HFapp Hcceil Hc4096 Hfa1 Hfa2 DFc. clear. intros. repeat split; lia.
  + split; [|split; exact I]. cbn [rd_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite U18, U19, U20, U32. change (2 ^ 6) with 64. change (2 ^ 3) with 8. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
    assert (H32 : (F + 32) mod 32 = 0).
    { destruct (div8_of_mul64 F HFa64) as [_ EF]. set (q := F / 64) in EF. rewrite EF.
      replace (64 * q + 32) with ((2 * q + 1) * 32) by lia. apply Z.mod_mul. lia. }
    unfold SB_OP in *.
    revert C1 HF4096 HFceil HFa64 H32 Hc4096 Hcceil Hfa1 Hfa2 Hps8. clear. intros.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- apply (shent_rd_ok _ _ ps).
  + unfold OBx. rewrite (U_atom _ 32 SB_OP E32) by (unfold SB_OP; lia). reflexivity.
  + rewrite (U_atom _ 19 ps E19) by lia. reflexivity.
  + unfold kLowShadowBeg. lia.
  + rewrite <- (aview_rd_of SEGS). apply (ra_frame (aview SEGS (w_H W) memc)); [exact Hsh0|].
    intros x Hx. unfold shadow_of_addr.
    pose proof HKEPT as (_ & _ & _ & G4 & _).
    pose proof (frame_al64 SEGS B lyc Sc W memc mdc cid pos HAR Hin) as (Hfa64 & Hfb64 & Hfb).
    set (Fc := frame_addr lyc cid pos) in *. set (nc := fs_frame_bytes cid) in *.
    destruct (div8_of_mul64 Fc Hfa64) as [Efa8 Efa64]. destruct (div8_of_mul64 nc Hfb64) as [Efb8 Efb64].
    set (qa := Fc / 64) in *. set (qb := nc / 64) in *.
    assert (Hx8 : 8 * qa <= x / 8 < 8 * qa + 8 * qb).
    { split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia. }
    rewrite (G4 cid pos (SHADOW_OFF + x / 8) Hin); [reflexivity | |].
    * right. unfold in_zr, shadow_addr. cbn [fst snd]. fold Fc nc. rewrite Efa8, Efb8. lia.
    * unfold SHADOW_OFF. intros Hq. unfold kLowShadowBeg in *. lia.
Qed.

Lemma in_asource_fp : forall f a, inFP (asource_fp f) a -> (f <= a < f + SRC_FILE_BLOCK) \/ (0 <= a < 1).
Proof.
intros f a (r & Hr & Ha). unfold asource_fp, YI16.sink_token in Hr.
destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; [left | right]; lia.
Qed.

(* The kept clauses across fclose's journal: its window lies in the call's window, the caller's blocks survive and
   are outside its footprint, the caller's frames are frames of its start state, at the same addresses. *)
Lemma topen_kept_call : forall lyc Sc W memc mdc ly3 S3 W3 m3 md3 ly4 S4 W4 m4 md4 s1 f slo shi (Ek : Z -> Prop),
  AR SEGS B lyc Sc W memc mdc ->
  topen_kept SK SEGS B lyc Sc W memc W3 m3 slo shi Ek ->
  ajournal SEGS B PFCLOSE_STK s1 (asource_fp f) ly3 S3 W3 m3 md3 [] ly4 S4 W4 m4 md4 2 ->
  slo <= s1 - PFCLOSE_STK -> s1 <= shi ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly3 S3) /\ In (b, m) (ablocks B ly4 S4)) ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ inFP (asource_fp f) (b + i)) ->
  (forall c q, In (c, q) (frames Sc) -> In (c, q) (frames S3)) ->
  (forall c q, frame_addr ly3 c q = frame_addr lyc c q) ->
  (forall c q a, In (c, q) (frames Sc) ->
     (in_zr a (frame_rng lyc (c, q)) \/ in_zr a (shadow_addr (frame_addr lyc c q), fs_frame_bytes c / 8)) ->
     ~ inFP (asource_fp f) a) ->
  (forall a, slo <= a < shi -> apresent (w_H W4) m4 a) ->
  topen_kept SK SEGS B lyc Sc W memc W4 m4 slo shi Ek.
Proof.
intros lyc Sc W memc mdc ly3 S3 W3 m3 md3 ly4 S4 W4 m4 md4 s1 f slo shi Ek HAR (K1 & K2 & K3 & K4 & K5 & K6) HJ1 Hlo Hhi
  Hbl HbF Hfr EFA HfF Hp.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hn. rewrite G1 by lia. exact (K1 a Ha Hn).
- intros b0 m0 i Hb Hi HnE. destruct (Hbl b0 m0 Hb) as [Hb3 Hb4].
  rewrite (G2 b0 m0 i Hb3 Hb4 Hi (HbF b0 m0 i Hb Hi)). exact (K2 b0 m0 i Hb Hi HnE).
- intros a Hi Hno He Hof. rewrite (G3 a Hi Hno He (fp_spares_off _ a Hof)). exact (K3 a Hi Hno He Hof).
- intros cid pos a Hin Hr HnE. rewrite (G4 cid pos a (Hfr cid pos Hin)); [exact (K4 cid pos a Hin Hr HnE) | |].
  + unfold frame_rng in *. rewrite !EFA. exact Hr.
  + exact (HfF cid pos a Hin Hr).
- intros a Ha Hn Hpa. eapply (apresent_transfer SEGS); [lia | intros Him; pose proof (pa_segs_low a Him); lia | | exact (K5 a Ha Hn Hpa)].
  apply G1; lia.
- exact Hp.
Qed.

(* The shadow entry of ps carries over to a new memory and environment that keep ps's shadow and the two atoms. *)
Lemma shok_transfer : forall E E' (m m' : word -> option byte) ps,
  sh_ok SEGS OBx rd_SH E m -> U E' OBx = U E OBx -> U E' (SOff 19 0) = U E (SOff 19 0) -> U E (SOff 19 0) = ps ->
  U E OBx = SHADOW_OFF ->
  (forall x, ps <= x < ps + 24 -> YCbn.rd_of SEGS m' (SHADOW_OFF + x / 8) = YCbn.rd_of SEGS m (SHADOW_OFF + x / 8)) ->
  sh_ok SEGS OBx rd_SH E' m'.
Proof.
intros E E' m m' ps HS EB E19 U19 UB Hk. unfold sh_ok, rd_SH in *. apply Forall_inv in HS.
apply Forall_cons; [|apply Forall_nil].
destruct HS as [HR HA]. unfold shent_ok, app_apart in *. cbn [she_m she_lo she_hi] in *. rewrite EB, E19. split; [|exact HA].
rewrite UB, U19 in HR |- *. apply (ra_frame _ _ _ _ HR). intros x Hx. unfold shadow_of_addr. apply Hk. lia.
Qed.

(* The machine frame's saved words and F's flag word, read back from the regions r_mf and r_F120 of a state. *)
Lemma mf_rdwords : forall E ss (ms : machine_state) H (regs : bvmap 5 word) sp F FL i0 i2,
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  nth_error (ss_mem ss) i0 = Some r_mf -> nth_error (ss_mem ss) i2 = Some r_F120 ->
  bv_unsigned (ew E 8) = sp -> bv_unsigned (ew E 18) = F -> bv_unsigned (ew E 33) = FL ->
  (forall j, (j < 11)%nat -> ew E (38 + j) = nth (6 + j) (op_extra 0 0 0 0 0 0 regs) (Z_to_bv 64 0)) ->
  rdword (aview SEGS H (ms_mem ms)) (sp - 8) = Some (raZ regs) /\
  (forall j, 0 <= j < 10 ->
     rdword (aview SEGS H (ms_mem ms)) (sp - 16 - 8 * j) =
     Some (bv_unsigned (getr regs (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))) /\
  rdword (aview SEGS H (ms_mem ms)) (F + OP_FLAGPTR) = Some FL.
Proof.
intros E ss ms H regs sp F FL i0 i2 HS H0 H2 U8 U18 U33 EX.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) i0 r_mf HS H0) as R0.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) i2 r_F120 HS H2) as R2.
cbn [restrict ms_mem] in R0, R2.
assert (HV : forall j, (j < 11)%nat -> val_mem SEGS (mrestrict H (ms_mem ms)) (sp + (-8 - 8 * Z.of_nat j)) 8
                         (bv_unsigned (nth (6 + j) (op_extra 0 0 0 0 0 0 regs) (Z_to_bv 64 0)))).
{ intros j Hj. rewrite <- (EX j Hj).
  apply (field_of_region E _ 8 sp mf_chunks (-96) 0 0 0 (-8 - 8 * Z.of_nat j) 8 (SOff (38 + j) 0)); [exact R0 | exact U8 | | | apply u64_range | lia].
  - do 11 (destruct j as [|j]; [cbn; tauto|]). lia.
  - cbn [sv_denot]. rewrite Z.add_0_r. reflexivity. }
split; [|split].
- replace (sp - 8) with (sp + (-8 - 8 * Z.of_nat 0)) by lia. apply (rdword_of_val_mem SEGS); [exact (HV 0%nat ltac:(lia)) | apply u64_range].
- intros j Hj. replace (sp - 16 - 8 * j) with (sp + (-8 - 8 * Z.of_nat (S (Z.to_nat j)))) by lia.
  rewrite (rdword_of_val_mem SEGS _ _ _ _ (HV (S (Z.to_nat j)) ltac:(lia)) (u64_range _)). f_equal.
  assert (Hj' : (Z.to_nat j < 10)%nat) by lia.
  replace j with (Z.of_nat (Z.to_nat j)) by lia. clear Hj HV EX.
  remember (Z.to_nat j) as jj. clear Heqjj.
  do 10 (destruct jj as [|jj]; [reflexivity|]). lia.
- apply (rdword_of_val_mem SEGS); [| rewrite <- U33; apply u64_range].
  apply (field_of_region E _ 18 F [YP09.mkChunk 120 (CVal 8 (SOff 33 0))] 120 128 0 0 120 8 (SOff 33 0)); [exact R2 | exact U18 | left; reflexivity | | rewrite <- U33; apply u64_range | lia].
  cbn [sv_denot]. rewrite Z.add_0_r, U33. reflexivity.
Qed.

Lemma ablocks_last_notin : forall ly3 S3 W3 mem3 md3 l x, AR SEGS B ly3 S3 W3 mem3 md3 ->
  ablocks B ly3 S3 = l ++ [x] -> 0 < req_size (snd x) -> ~ In x l.
Proof.
intros ly3 S3 W3 mem3 md3 l x HAR Hab Hpos Hin. destruct (in_split _ _ Hin) as (l1 & l2 & El).
pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 mem3 md3 x x l1 l2 [] HAR ltac:(rewrite Hab, El, <- app_assoc; reflexivity)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.

Lemma nth_firstn_lt : forall (l : list Z) k j, (j < k)%nat -> nth j (firstn k l) 0 = nth j l 0.
Proof.
intros l k. revert l. induction k as [|k IH]; intros l j Hj; [lia|].
destruct l as [|x l]; cbn; [destruct j; reflexivity|]. destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.

(* op_mid moves to a state with the same registers and memory (a run that wrote nothing). *)
Definition mid_regs : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma op_mid_move : forall (cx : ocx) fpos f s4v s9v sh kk ly3 S3 W3 (ms ms' : machine_state) md md',
  op_mid SK B K cx fpos f s4v s9v sh kk ly3 S3 W3 ms md ->
  ms_resv ms' = None -> ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs ->
  ms_fcsr ms' = fp_csr ->
  (forall r, In r mid_regs -> getr (ms_regs ms') r = getr (ms_regs ms) r) -> ms_mem ms' = ms_mem ms ->
  ajournal SEGS B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
    ((OP_CID, fpos) :: o_own cx) ly3 S3 W3 (ms_mem ms') md' (o_k cx + kk) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  op_mid SK B K cx fpos f s4v s9v sh kk ly3 S3 W3 ms' md'.
Proof.
intros cx fpos f s4v s9v sh kk ly3 S3 W3 ms ms' md md' Hmid H1 H2 H3 H4 H5 HR EM HJ' Hfd Hfs.
unfold op_mid in *.
destruct Hmid as (_ & _ & _ & _ & _ & _ & Hkk & Hnev & Hfrs3 & Hnin & HfsS & R2 & R8 & R9 & R18 & R19 &
  R20 & R21 & R22 & R23 & R24 & R25 & R3 & R4 & R26 & R27 & Hra & Hsav & HMG & HO10 & HO11 & HFLP & Hlsh & Hsh &
  Vf & V12 & V16 & V20 & V8 & HKEPT & Hfds & Hfs0 & Hmeta & Hrod & Hch).
rewrite EM in HJ' |- *.
rewrite (HR 2%bv), (HR 3%bv), (HR 4%bv), (HR 8%bv), (HR 9%bv), (HR 18%bv), (HR 19%bv), (HR 20%bv), (HR 21%bv),
  (HR 22%bv), (HR 23%bv), (HR 24%bv), (HR 25%bv), (HR 26%bv), (HR 27%bv) by (cbn; tauto).
repeat (split; [eassumption|]).
split; [rewrite Hfd; exact Hfds|]. split; [rewrite Hfs; exact Hfs0|]. repeat (split; [eassumption|]). exact Hch.
Qed.

(* osp1 is 32-aligned, at most 127 below the entry sp. *)
Lemma osp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 127 <= 32 * ((x - 96) / 32) <= x - 96 /\ (32 * ((x - 96) / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod (x - 96) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (x - 96) 32 ltac:(lia)) as M.
split; [lia|]. replace (32 * ((x - 96) / 32)) with ((2 * ((x - 96) / 32)) * 16) by lia. apply Z.mod_mul. lia.
Qed.

Ltac ro_awr :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|] ].

Lemma land_low_shift : forall a b k, 0 <= k -> 0 <= a < 2 ^ k -> Z.land a (Z.shiftl b k) = 0.
Proof.
intros a b k Hk Ha. apply Z.bits_inj_0. intros i. rewrite Z.land_spec.
destruct (Z_lt_le_dec i k) as [Hi|Hi].
- destruct (Z_lt_le_dec i 0) as [Hn|Hn]; [rewrite Z.testbit_neg_r by lia; reflexivity|].
  rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
- rewrite <- (Z.mod_small a (2 ^ k)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma lor_shift_add : forall a b k, 0 <= k -> 0 <= a < 2 ^ k -> Z.lor a (Z.shiftl b k) = a + Z.shiftl b k.
Proof.
intros a b k Hk Ha. rewrite <- Z.lxor_lor by (apply land_low_shift; assumption).
rewrite Z.add_nocarry_lxor; [reflexivity | apply land_low_shift; assumption].
Qed.

(* The magic as the code computes it (0x81398..0x813c0): the four header bytes, little-endian, the top byte through
   `slliw` (sign-extended from bit 31). *)
Definition magic_sv : sv :=
  SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 35 0)) (SLit 8)) (SExt false 8 (SOff 34 0)))
    (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 36 0)) (SLit 16)) (SAluw ALU_SLL (SExt false 8 (SOff 37 0)) (SLit 24))).

Lemma magic_U : forall E c0 c1 c2 c3,
  bv_unsigned (ew E 34) = c0 -> bv_unsigned (ew E 35) = c1 -> bv_unsigned (ew E 36) = c2 -> bv_unsigned (ew E 37) = c3 ->
  0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= c3 < 256 ->
  U E magic_sv = c0 + 256 * c1 + 65536 * c2 + 16777216 * c3 + (if c3 <? 128 then 0 else 18446744069414584320).
Proof.
intros E c0 c1 c2 c3 H0 H1 H2 H3 R0 R1 R2 R3. unfold magic_sv.
assert (X : forall a c, bv_unsigned (ew E a) = c -> 0 <= c < 256 -> U E (SExt false 8 (SOff a 0)) = c).
{ intros a c Ha Hc. rewrite U_SExt, U_SOff, Ha, Z.add_0_r. rewrite (zcanon_id c) by (unfold M64; lia).
  change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. apply zcanon_id. unfold M64; lia. }
assert (UW : U E (SAluw ALU_SLL (SExt false 8 (SOff 37 0)) (SLit 24)) = Z.shiftl (c3 + (if c3 <? 128 then 0 else 1099511627520)) 24).
{ rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite (X 37%nat c3 H3 R3), U_SLit. change (zcanon 24 mod 2 ^ 32) with 24. change (Z.land 24 31) with 24.
  rewrite (Z.mod_small c3) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_mul_pow2 by lia.
  unfold bv_swrap, bv_wrap, bv_modulus, bv_half_modulus. change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ Z.of_N 64) with 18446744073709551616.
  try change (2 ^ (Z.of_N 32 - 1)) with 2147483648. try change (bv_modulus 32 / 2) with 2147483648.
  try change (bv_modulus 32) with 4294967296. try change (bv_modulus 64) with 18446744073709551616.
  destruct (Z.ltb_spec c3 128).
  - rewrite (Z.mod_small (c3 * 2 ^ 24 + 2147483648)) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_unique (c3 * 2 ^ 24 + 2147483648) 4294967296 1 (c3 * 2 ^ 24 + 2147483648 - 4294967296)) by lia.
    rewrite <- (Z.mod_unique (c3 * 2 ^ 24 + 2147483648 - 4294967296 - 2147483648) 18446744073709551616 (-1)
      (c3 * 2 ^ 24 + 2147483648 - 4294967296 - 2147483648 + 18446744073709551616)) by lia.
    lia. }
set (w := c3 + (if c3 <? 128 then 0 else 1099511627520)) in UW.
assert (Hw : 0 <= w < 1099511627776) by (subst w; destruct (Z.ltb_spec c3 128); lia).
assert (UA : U E (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 35 0)) (SLit 8)) (SExt false 8 (SOff 34 0))) = c0 + 256 * c1).
{ rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SAlu; cbn [zalu_raw]; rewrite (X 35%nat c1 H1 R1), (X 34%nat c0 H0 R0), U_SLit.
  change (zcanon 8) with 8. change (Z.land 8 63) with 8.
  rewrite (zcanon_id (Z.shiftl c1 8)) by (rewrite Z.shiftl_mul_pow2 by lia; unfold M64; lia).
  rewrite Z.lor_comm, lor_shift_add by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite zcanon_id by (unfold M64; lia). lia. }
assert (UB : U E (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 36 0)) (SLit 16)) (SAluw ALU_SLL (SExt false 8 (SOff 37 0)) (SLit 24))) = 65536 * c2 + 16777216 * w).
{ rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SAlu; cbn [zalu_raw]; rewrite UW, (X 36%nat c2 H2 R2), U_SLit.
  change (zcanon 16) with 16. change (Z.land 16 63) with 16.
  rewrite (zcanon_id (Z.shiftl c2 16)) by (rewrite Z.shiftl_mul_pow2 by lia; unfold M64; lia).
  replace (Z.shiftl w 24) with (Z.shiftl (Z.shiftl w 8) 16) by (rewrite Z.shiftl_shiftl by lia; reflexivity).
  rewrite <- Z.shiftl_lor, lor_shift_add by lia. rewrite !Z.shiftl_mul_pow2 by lia. rewrite zcanon_id by (unfold M64; lia). lia. }
rewrite U_SAlu; cbn [zalu_raw]; rewrite UA, UB.
replace (65536 * c2 + 16777216 * w) with (Z.shiftl (c2 + 256 * w) 16) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
rewrite lor_shift_add by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite zcanon_id by (unfold M64; lia).
subst w. destruct (Z.ltb_spec c3 128); lia.
Qed.

(* ---- the two closing paths: the short read (0x81400) and the bad magic (0x81444) ----------------------------- *)
(* `lbu a0,0(s8)` and the shadow test of ps (0 by ps's shadow entry, so the report calls are dead), f = ps->f, the
   fclose wrapper's call (0x8140c / 0x81450) through AFCLOSE, the second shadow test, ps->f := NULL (0x8145c),
   a0 := -1, and the epilogue from 0x81464. *)
Lemma op_fclose : forall (cx : ocx) fpos ly3 S3 W3 (ms : machine_state) md3 f kr pc,
  op_pre SK B K MT FM_RA CTX roimg cx ->
  pc = OP_SHORT \/ pc = OP_BAD ->
  ms_pc_val ms = w64 (BASE + pc) ->
  op_mid SK B K cx fpos f (oF cx fpos + OP_HDR) 24 OSH_in 1 ly3 S3 W3 ms md3 ->
  1 <= o_n cx -> 4096 <= f -> f mod 16 = 0 ->
  ablocks B ly3 S3 = ablocks B (o_lyc cx) (o_Sc cx) ++ [(f, SRC_FILE_BLOCK)] ->
  asource_at SEGS K (rdW W3 (ms_mem ms)) f (o_b cx) (o_C cx) kr ->
  (forall x, inFP (asource_fp f) x -> inFP (o_FP cx) x \/ in_tmp_block (ablocks B (o_ly cx) (o_S cx)) (ablocks B ly3 S3) x) ->
  mo_le MT (o_Sc cx) S3 (mo_malloc MT SRC_FILE_BLOCK) ->
  pcap_goodZ (o_C cx) = false ->
  SRr SEGS W3 (mkCfg ms md3) (op_post SK B K MT cx).
Proof.
intros cx fpos ly3 S3 W3 ms md3 f kr pc HPRE Hpcs Hpc Hmid Hn1 Hf4096 Hf16 Hab HSRC HFPinc Hmo Hgood.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfin3 : In (f, SRC_FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
pose proof Hmid as (Hrv & Hsvc & Hrom & Hfr & Hfcsr & HJ & Hkk & Hnev & Hfrs3 & Hnin & HfsS & R2 & R8 & R9 & R18 & R19 &
  R20 & R21 & R22 & R23 & R24 & R25 & R3 & R4 & R26 & R27 & Hra & Hsav & HMG & HO10 & HO11 & HFLP & Hlsh & Hsh &
  Vf & V12 & V16 & V20 & V8 & HKEPT & Hfds & Hfs & Hmeta & Hrod & Hch).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms) md3 f SRC_FILE_BLOCK (proj1 HJ) Hfin3) as (_ & _ & Hfceil & Hfia & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Hfceil, Hfia.
destruct (rd_entry cx fpos ly3 S3 W3 ms md3 f pc HPRE Hmid Hpc ltac:(lia)) as [HS SHOK].
pose proof (fun a => tail_apart cx fpos ly3 S3 W3 (ms_mem ms) md3 (o_k cx + 1) a HPRE HJ) as HAP.
pose proof HPRE as HPRE0.
destruct cx as [STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos].
unfold op_mid, oSH, oFL, oF, osp1 in *. unfold op_pre in HPRE.
cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k
  o_regs o_ch o_ps o_n o_b o_M o_C o_cid o_pos] in *.
destruct HPRE as (HJc & HROD & Hraw & Hra4 & Hgp & Htp & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & Hown & Hfa1 & Hfa2 & _ &
  Hps8 & Hsh0 & _ & _ & _ & _ & _ & _ & _ & _ & HnC & _ & Hinput & _ & HEV & _).
pose proof HJc as (HAR & _ & _ & _ & _ & Hfrsc & _).
pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct (ly_F_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [EFA3 EFL3].
destruct (ly_F_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as [EFAc EFLc].
assert (EFA : forall c q, frame_addr ly3 c q = frame_addr lyc c q) by (intros c q; rewrite EFA3, EFAc; reflexivity).
assert (EFL : forall c q, flag_addr ly3 c q = flag_addr lyc c q) by (intros c q; rewrite EFL3, EFLc; reflexivity).
clear EFA3 EFL3 EFAc EFLc.
assert (HTS : TPCAP_SOURCE_OPEN_STK = 18736) by reflexivity.
unfold OP_CID, OP_HDR in *.
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
assert (Hin3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hin).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hc4096 & Hcceil & Hcapp).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hcapp, Hfia.
set (F := frame_addr lyc 1 fpos) in *. set (FL := flag_addr lyc 1 fpos) in *.
set (sp1 := 32 * ((spZ regs - OPEN_FRAME) / 32)) in *.
assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply u64_range).
destruct (osp1_facts (spZ regs) ltac:(lia) Hal16) as (Hsp1r & Hsp1al).
change OPEN_FRAME with 96 in sp1. fold sp1 in Hsp1r, Hsp1al.
remember (Eimg (Ereg (ms_regs ms) (op_extra FL (nth 0 C 0) (nth 1 C 0) (nth 2 C 0) (nth 3 C 0) f regs))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall nn, (nn < A_TEXT)%nat -> ew E nn = ew (Ereg (ms_regs ms) (op_extra FL (nth 0 C 0) (nth 1 C 0) (nth 2 C 0) (nth 3 C 0) f regs)) nn)
  by (intros nn Hn; subst E; apply Eimg_low; exact Hn).
assert (EX : forall a, (32 <= a < 50)%nat -> ew E a = nth (a - 32) (op_extra FL (nth 0 C 0) (nth 1 C 0) (nth 2 C 0) (nth 3 C 0) f regs) (Z_to_bv 64 0))
  by (intros a Ha; rewrite EL by (unfold A_TEXT; lia); replace a with (32 + (a - 32))%nat at 1 by lia; apply ew_Ereg_extra).
assert (ER : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> (nn < 32)%nat -> ew E nn = getr (ms_regs ms) r)
  by (intros nn r Hr Hn; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hr).
assert (E2 : ew E 2 = w64 sp1) by (rewrite (ER 2%nat 2%bv eq_refl) by lia; exact R2).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (ER 3%nat 3%bv eq_refl) by lia; exact R3).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (ER 4%nat 4%bv eq_refl) by lia; exact R4).
assert (E8 : ew E 8 = w64 (spZ regs)) by (rewrite (ER 8%nat 8%bv eq_refl) by lia; exact R8).
assert (E18 : ew E 18 = w64 F) by (rewrite (ER 18%nat 18%bv eq_refl) by lia; exact R18).
assert (E19 : ew E 19 = w64 ps) by (rewrite (ER 19%nat 19%bv eq_refl) by lia; exact R19).
assert (E21 : ew E 21 = w64 (SHADOW_OFF + F / 8)) by (rewrite (ER 21%nat 21%bv eq_refl) by lia; exact R21).
assert (E26 : ew E 26 = getr regs 26) by (rewrite (ER 26%nat 26%bv eq_refl) by lia; exact R26).
assert (E27 : ew E 27 = getr regs 27) by (rewrite (ER 27%nat 27%bv eq_refl) by lia; exact R27).
assert (E32 : ew E 32 = w64 SB_OP) by (rewrite (EX 32%nat) by lia; reflexivity).
assert (E33 : ew E 33 = w64 FL) by (rewrite (EX 33%nat) by lia; reflexivity).
assert (E49 : ew E 49 = w64 f) by (rewrite (EX 49%nat) by lia; reflexivity).
assert (EXR : forall j, (j < 11)%nat -> ew E (38 + j) = nth (6 + j) (op_extra 0 0 0 0 0 0 regs) (Z_to_bv 64 0)).
{ intros j Hj. rewrite (EX (38 + j)%nat) by lia. replace (38 + j - 32)%nat with (6 + j)%nat by lia.
  do 11 (destruct j as [|j]; [reflexivity|]). lia. }
clear HEdef EL EX ER.
(* the frames and the FILE block are apart *)
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms) md3 f SRC_FILE_BLOCK cid pos HAR3 Hfin3 Hin3) as DfP.
assert (HinF3 : In (1, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms) md3 f SRC_FILE_BLOCK 1 fpos HAR3 Hfin3 HinF3) as DfF.
unfold zdisjoint in DfP, DfF. cbn [fst snd] in DfP, DfF. rewrite EFA in DfP, DfF. change (req_size SRC_FILE_BLOCK) with 1304 in DfP, DfF.
change (fs_frame_bytes 1) with 128 in DfF. fold F in DfF.
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms) md3 1 fpos HAR3 HinF3) as (HF4096 & HFceil & HFapp).
rewrite EFA in HF4096, HFceil, HFapp. change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp. fold F in HF4096, HFceil, HFapp.
assert (U8 : bv_unsigned (ew E 8) = spZ regs) by (rewrite E8; apply unsigned_lit_small; exact Hsp64).
assert (U18 : bv_unsigned (ew E 18) = F) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = ps) by (rewrite E19; apply unsigned_lit_small; lia).
destruct (FFL ly3 S3 W3 (ms_mem ms) md3 1 fpos HAR3 HinF3) as (_ & _ & _ & (HFL4096 & _ & HFLceil)).
rewrite EFL in HFL4096, HFLceil. fold FL in HFL4096, HFLceil.
assert (U33 : bv_unsigned (ew E 33) = FL) by (rewrite E33; apply unsigned_lit_small; lia).
(* to the call of fclose *)
destruct Hpcs as [-> | ->]; (paj_run_tok RUN HS HJ SHOK OPspan; [ ro_awr | ]).
all: idtac.
all: assert (EM : ms_mem ms0 = ms_mem ms) by
  (apply functional_extensionality; intros x; apply HF; intros (r & Hin' & Hr);
   cbn [ss_rd ss_mem In] in Hin'; unfold r_mf, r_ps, r_F120 in Hin';
   repeat (destruct Hin' as [<- | Hin']; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia |]); destruct Hin').
all: pmkst HS.
all: prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
  prreg HS (8%bv : bv 5) Q8; prreg HS (10%bv : bv 5) Q10.
all: rewrite EM in HJ |- *.
all: assert (HPf : Permutation (ablocks B ly3 S3) ((f, SRC_FILE_BLOCK) :: ablocks B lyc Sc))
  by (rewrite Hab; apply Permutation_sym, Permutation_cons_append).
all: assert (Hinb : In (b, Z.of_nat (length C)) (ablocks B ly3 S3))
  by (rewrite Hab; apply in_or_app; left; rewrite <- HnC; exact (proj1 (Hinput Hn1))).
all: assert (HEVf : st_nev S3 + 2 <= EV_MAX) by (unfold EV_OPEN, EV_FUZZ_FOPEN in HEV; lia).
all: pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO; pose proof (@pa_B_ok _ _ PI) as HBOK.
all: (lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  assert (Q10' : getr rg 10 = Z_to_bv 64 f) by (rewrite Q10, E49; reflexivity);
  eapply SRr_bind;
  [ eapply (cl_callS B LAWS W3 rg mm _ STK sp0 FP ly S0 W0 mem0 md0 ((1, fpos) :: own) ly3 S3 mdq (k + 1) PFCLOSE_STK
      (asource_fp f) 2 (sp1 - sp0) _ ((spZ regs, raZ regs, s0Z regs) :: ch)
      (fun ly4 S4 W4 regs4 mem4 md4 => getr regs4 10 = Z_to_bv 64 0 /\ Permutation (ablocks B ly4 S4) (ablocks B lyc Sc) /\
         frames S4 = frames S3 /\ asource_none SEGS K (rdW W4 mem4) /\ m_fds md4 = m_fds mdq /\ m_fs md4 = m_fs mdq) HJ);
    [ unfold spZ at 1; rewrite Q2, E2; unfold w64; rewrite unsigned_lit_small by lia; lia
    | rewrite Zminus_mod, Hsp1al, Hsp0al; reflexivity
    | lia
    | unfold PFCLOSE_STK; lia
    | unfold PFCLOSE_STK; lia
    | rewrite Q3, E3; exact Hgp
    | rewrite Q4, E4; exact Htp
    | exact Q1
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | rewrite unsigned_lit_small by lia; lia
    | replace (sp0 + (sp1 - sp0)) with sp1 by lia; unfold s0Z; rewrite Q8, E8; unfold w64; rewrite unsigned_lit_small by lia;
      exact Hch
    | intros HPRE1; eapply SRr_mono;
      [ eapply (AFCLOSE W3 ly3 S3 rg mm mdq _ f b M C kr (ablocks B lyc Sc) HPRE1 Q10' HPf HSRC Hinb Hmeta
          (fun a Ha Ho He => Hrod a Ha Ho He) HEVf HUfc1 HUfc2)
      | cbv beta; intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ1 & HP & Ha0 & HPm & Hfr4 & HSN & HGB & HFD & HFS);
        exists ly4, S4, regs4, mem4, md4; split; [rewrite Q1; reflexivity|];
        split; [exact HJ1|]; split; [exact HP|];
        exact (conj Ha0 (conj HPm (conj Hfr4 (conj HSN (conj HFD HFS))))) ]
    | exact HFPinc ]
  | ] end).
all: cbv beta; intros W4 c4 Hwle (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 & Ha04 & HPerm4 & Hfrs4 & HSN4 & HFD4 & HFS4).
all: replace (sp0 + (sp1 - sp0)) with sp1 in HJc4 by lia.

all: jafter_call_keep_hi HS 512%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1; 2]%nat HS2.
all: (match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end).
all: try (cbn [ms_mem restrict]; rewrite EM;
  pose proof HJc4 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _);
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
  [ split;
    [ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U8; intros a Ha;
      apply (mbyte_of_aview SEGS); apply G1; unfold PFCLOSE_STK; lia
    | cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha; lia ]
  | apply (region_kept_frame_sub (segs := SEGS) B E PFCLOSE_STK sp1 (asource_fp f) ly3 S3 W3 (ms_mem ms) _ ly4 S4 W4 mem4 md4 2
      19 ps 0 24 0 0 _ cid pos HJc4 U19 Hin3);
    [ rewrite EFA; lia | rewrite EFA; lia
    | intros a Ha Hf; destruct (in_asource_fp f a Hf) as [H|H]; unfold SRC_FILE_BLOCK in H; lia
    | intros a Ha; lia ]
  | apply (region_kept_frame_sub (segs := SEGS) B E PFCLOSE_STK sp1 (asource_fp f) ly3 S3 W3 (ms_mem ms) _ ly4 S4 W4 mem4 md4 2
      18 F 120 128 0 0 _ 1 fpos HJc4 U18 HinF3);
    [ rewrite EFA; fold F; lia | rewrite EFA; fold F; change (fs_frame_bytes 1) with 128; lia
    | intros a Ha Hf; destruct (in_asource_fp f a Hf) as [H|H]; unfold SRC_FILE_BLOCK in H; lia
    | intros a Ha; lia ] ]).

all: clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS.
all: remember (havoc E 512 (map (getr regs4) CLOB)) as E' eqn:HE' in HS.
all: assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
all: assert (OLD : forall nn, (nn < 512)%nat -> ew E' nn = ew E nn) by (intros nn Hnn; rewrite HE'; apply YN3v.ew_havoc_old; exact Hnn).
all: clear HE'.
all: assert (U19' : bv_unsigned (ew E' 19) = ps) by (rewrite OLD by lia; exact U19).
all: pose proof HJ4 as (HAR4 & _ & _ & _ & _ & Hfrs4' & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
all: assert (HPS4 : forall a, ps <= a < ps + 24 -> apresent (w_H W4) mem4 a)
  by (intros a Ha; refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ4 _));
      right; right; right; exists cid, pos; split; [right; exact Hown|]; left; unfold in_zr; cbn [fst snd];
      destruct (ly_F_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as [EFA4 _];
      destruct (ly_F_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as [EFAc _]; rewrite EFA4, <- EFAc; lia).
(* ps->f := NULL (0x8145c) writes ps[0, 8): the window of ps's region opens after the call *)
all: (lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
  pose proof (ast_ok_pi_set_region E' ssx msx 1 (r_ps 0 0) (r_ps 0 8) HS eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E' (ms_mem msx) (r_ps 0 0) 0 8 (st_ok_pi_region_nth E' ssx msx 1 (r_ps 0 0) HS eq_refl)
       ltac:(intros o Ho; unfold r_ps; cbn [YP09.r_base base_val restrict ms_mem mkst]; rewrite U19'; apply (apresent_writable SEGS); apply HPS4; lia)))
    as HS3 end).
all: clear HS; rename HS3 into HS.
all: (lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end).
all: assert (SHOK2 : sh_ok SEGS OBx rd_SH E' (rdW W4 mem4)).
all: try (apply (shok_transfer E E' (rdW W3 (ms_mem ms)) (rdW W4 mem4) ps);
  [ rewrite <- EM; exact SHOK
  | unfold OBx, U; cbn [sv_denot]; rewrite OLD by lia; reflexivity
  | unfold U; cbn [sv_denot]; rewrite OLD by lia; reflexivity
  | rewrite (U_atom _ 19 ps E19) by lia; reflexivity
  | unfold OBx; rewrite (U_atom _ 32 SB_OP E32) by (unfold SB_OP; lia); reflexivity
  | intros x Hx; rewrite <- !(aview_rd_of SEGS);
    pose proof HJc4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G4 & _);
    pose proof (frame_al64 SEGS B lyc Sc W memc mdc cid pos HAR Hin) as (Hfa64 & Hfb64 & Hfb);
    set (Fc := frame_addr lyc cid pos) in *; set (nc := fs_frame_bytes cid) in *;
    destruct (div8_of_mul64 Fc Hfa64) as [Efa8 Efa64]; destruct (div8_of_mul64 nc Hfb64) as [Efb8 Efb64];
    set (qa := Fc / 64) in *; set (qb := nc / 64) in *;
    assert (Hx8 : 8 * qa <= x / 8 < 8 * qa + 8 * qb) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia);
    apply (G4 cid pos (SHADOW_OFF + x / 8) Hin3);
    [ right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA; fold Fc nc; rewrite Efa8, Efb8; lia
    | intros Hf; destruct (in_asource_fp f _ Hf) as [H|H]; unfold SRC_FILE_BLOCK, SHADOW_OFF in H; lia ] ]).

all: assert (EFA4 : forall c q, frame_addr ly4 c q = frame_addr lyc c q) by
  (intros c q; destruct (ly_F_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as [E4a _];
   destruct (ly_F_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as [Eca _]; rewrite E4a, Eca; reflexivity).
all: (paj_run_to_tok RUNTO HS HJ4 SHOK2 OPspan OP_EPI;
  [ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
    eapply awr_ok_cons_gen; [reflexivity | exact U19' | cbn [YP09.r_wlo YP09.r_whi]; intros ?a ?Ha;
      right; right; right; exists cid, pos; split; [right; exact Hown|]; left; unfold in_zr; cbn [fst snd]; rewrite EFA4; lia |];
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]; apply awr_ok_nil
  | ]).

all: assert (U8' : bv_unsigned (ew E' 8) = spZ regs) by (rewrite OLD by lia; exact U8).
all: assert (U18' : bv_unsigned (ew E' 18) = F) by (rewrite OLD by lia; exact U18).
all: assert (U33' : bv_unsigned (ew E' 33) = FL) by (rewrite OLD by lia; exact U33).
all: assert (EXR' : forall j, (j < 11)%nat -> ew E' (38 + j) = nth (6 + j) (op_extra 0 0 0 0 0 0 regs) (Z_to_bv 64 0))
  by (intros j Hj; rewrite OLD by lia; exact (EXR j Hj)).
all: (lazymatch type of HS with st_ok_pi _ _ _ ?ss5 (restrict _ ?ms5) =>
  destruct (mf_rdwords E' ss5 ms5 (w_H W4) regs (spZ regs) F FL 0 2 HS eq_refl eq_refl U8' U18' U33' EXR') as (Rra & Rsav & RFL);
  pose proof HS as (Hf5 & Hpc5 & Hsv5 & Hrv5 & Hfc5 & Hrom5 & _);
  cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom abs_ss setpc ss_pc ss_resv resv_denot] in Hf5, Hpc5, Hsv5, Hrv5, Hfc5, Hrom5
  end).
all: prreg HS (8%bv : bv 5) T8; prreg HS (18%bv : bv 5) T18; prreg HS (22%bv : bv 5) T22; prreg HS (21%bv : bv 5) T21;
  prreg HS (3%bv : bv 5) T3; prreg HS (4%bv : bv 5) T4; prreg HS (26%bv : bv 5) T26; prreg HS (27%bv : bv 5) T27;
  prreg HS (10%bv : bv 5) T10.
all: rewrite ?OLD in T8, T18, T22, T21, T3, T4, T26, T27 by lia.
all: (lazymatch goal with |- SRr _ _ (mkCfg ?ms5 ?md5) _ =>
  assert (T10' : getr (ms_regs ms5) 10 = w64 (-1)) by (rewrite T10, w64_m1; reflexivity);
  assert (T8' : getr (ms_regs ms5) 8 = w64 (spZ regs)) by (rewrite T8; exact E8);
  assert (T18' : getr (ms_regs ms5) 18 = w64 F) by (rewrite T18; exact E18);
  assert (T22' : getr (ms_regs ms5) 22 = w64 F) by (rewrite T22; exact E18);
  assert (T21' : getr (ms_regs ms5) 21 = w64 (SHADOW_OFF + F / 8)) by (rewrite T21; exact E21);
  assert (T3' : getr (ms_regs ms5) 3 = getr regs 3) by (rewrite T3; exact E3);
  assert (T4' : getr (ms_regs ms5) 4 = getr regs 4) by (rewrite T4; exact E4);
  assert (T26' : getr (ms_regs ms5) 26 = getr regs 26) by (rewrite T26; exact E26);
  assert (T27' : getr (ms_regs ms5) 27 = getr regs 27) by (rewrite T27; exact E27);
  apply (op_epi (mkOCX STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos) fpos ly4 S4 W4 ms5 md5
    (k + 1 + 2) OP_EPI (-1) _ HPRE0 HJ4 Hrv5 Hsv5 Hrom5 Hf5 Hfc5 Hpc5 (or_intror (conj eq_refl T10'))
    T8' T18' T22' T21' T3' T4' T26' T27' Rra Rsav RFL) end).

all: intros mem2 md2 regs2 HJ2 HP2 Ha0 UN Hfds2 Hfs2.
all: unfold op_post, tpcap_source_open_post, oSH, oFL, oF in *.
all: cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k
  o_regs o_ch o_ps o_n o_b o_M o_C o_cid o_pos] in *.
all: unfold OP_CID in *; fold F FL in UN.
all: (lazymatch type of HFr0 with frame_of _ ?rsP _ (rdW _ (ms_mem ?m5)) =>
  assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (ps <= a < ps + 8) -> aview SEGS (w_H W4) (ms_mem m5) a = aview SEGS (w_H W4) mem4 a)
  by (intros a Ha Hn; apply (kept_of_frame (segs := SEGS) E' rsP (w_H W4) mem4 (ms_mem m5) (fun a => ps <= a < ps + 8) HFr0);
      [ intros bb wlo whi aa HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW; rewrite ?U19' in HrrW; lia|]);
        destruct HinW
      | exact Ha | exact Hn ]) end).
all: pose proof HJc4 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
all: assert (NT : forall a, ps <= a < ps + 24 -> ~ ((F <= a < F + 128) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16) \/ a = FL))
  by (intros a Ha HT; destruct (HAP a HT) as (_ & _ & _ & Hfr2); apply (proj1 (Hfr2 cid pos Hin));
      unfold frame_rng, in_zr; cbn [fst snd]; lia).
all: assert (Hps64 : forall a, ps <= a < ps + 24 -> 0 <= a < 2 ^ 64) by (intros a Ha; lia).
all: assert (UNps : forall a, ps <= a < ps + 24 -> aview SEGS (w_H W4) mem2 a = aview SEGS (w_H W4) (ms_mem ms1) a)
  by (intros a Ha; apply UN; [exact (Hps64 a Ha) | intros H; apply (NT a Ha); left; lia | intros H; apply (NT a Ha); right; left; exact H
      | intros H; apply (NT a Ha); right; right; exact H]).
all: assert (KMps : forall a, ps + 8 <= a < ps + 24 -> aview SEGS (w_H W4) mem2 a = aview SEGS (w_H W3) (ms_mem ms) a)
  by (intros a Ha; rewrite UNps by lia; rewrite KM2 by lia;
      apply (G4 cid pos a Hin3); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA; lia
      | intros Hf; destruct (in_asource_fp f a Hf) as [H|H]; unfold SRC_FILE_BLOCK in H; lia]).
all: assert (MBps : forall a, ps + 8 <= a < ps + 24 -> mbyte SEGS (rdW W4 mem2) a = mbyte SEGS (rdW W3 (ms_mem ms)) a)
  by (intros a Ha; apply (mbyte_of_aview SEGS); exact (KMps a Ha)).
all: assert (Hnotf : ~ In (f, SRC_FILE_BLOCK) (ablocks B lyc Sc))
  by (apply (ablocks_last_notin ly3 S3 W3 (ms_mem ms) md3 _ _ HAR3 Hab); cbn [snd]; change (req_size SRC_FILE_BLOCK) with 1304; lia).
all: assert (KT1 : topen_kept SK SEGS B lyc Sc W memc W4 mem4 (spZ regs - TPCAP_SOURCE_OPEN_STK) (spZ regs) (fun a => ps <= a < ps + 22)).
all: try (apply (topen_kept_call lyc Sc W memc mdc ly3 S3 W3 (ms_mem ms) _ ly4 S4 W4 mem4 md4 sp1 f _ _ _ HAR HKEPT HJc4);
  [ unfold PFCLOSE_STK; lia
  | lia
  | intros b0 m0 Hb; split; [rewrite Hab; apply in_or_app; left; exact Hb | exact (Permutation_in _ (Permutation_sym HPerm4) Hb)]
  | intros b0 m0 i Hb Hi Hf;
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m0 HAR Hb) as (_ & Hb4096 & _);
    destruct (in_asource_fp f _ Hf) as [H|H]; [|lia];
    assert (Hne : (b0, m0) <> (f, SRC_FILE_BLOCK)) by (intros Heq; rewrite Heq in Hb; exact (Hnotf Hb));
    pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 (ms_mem ms) md3 b0 m0 f SRC_FILE_BLOCK HAR3
      ltac:(rewrite Hab; apply in_or_app; left; exact Hb) Hfin3 Hne) as D;
    unfold zdisjoint in D; cbn [fst snd] in D; change (req_size SRC_FILE_BLOCK) with 1304 in D; unfold SRC_FILE_BLOCK in H; lia
  | intros c q Hcq; rewrite Hfrs3; right; exact Hcq
  | exact EFA
  | intros c q a Hcq Hr Hf;
    assert (Hcq3 : In (c, q) (frames S3)) by (rewrite Hfrs3; right; exact Hcq);
    destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc c q HAR Hcq) as (Hg4096 & Hgceil & Hgapp);
    pose proof (fs_frame_bytes_nonneg c) as Hnn;
    pose proof (shadow_addr_bounds (frame_addr lyc c q) ltac:(lia)) as Hsb1;
    pose proof (shadow_addr_bounds (frame_addr lyc c q + fs_frame_bytes c) ltac:(lia)) as Hsb2;
    pose proof (shadow_range_end (frame_addr lyc c q) (fs_frame_bytes c) Hnn) as Hse;
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms) md3 f SRC_FILE_BLOCK c q HAR3 Hfin3 Hcq3) as Dff;
    unfold zdisjoint in Dff; cbn [fst snd] in Dff; rewrite EFA in Dff; change (req_size SRC_FILE_BLOCK) with 1304 in Dff;
    unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr;
    destruct (in_asource_fp f _ Hf) as [H|H]; unfold SRC_FILE_BLOCK in H; destruct Hr; lia
  | intros a Ha; apply Hpres4; lia ]).

all: pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & _).
all: pose proof HJ2 as (_ & _ & _ & _ & _ & Hfrs2 & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
all: assert (HFfr : forall a, ps <= a < ps + 8 -> ~ in_img SEGS a /\ a < alloc_ceiling)
  by (intros a Ha; split; [exact (frm_img SEGS B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(lia)) | lia]).
all: (lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m5) =>
  assert (KT2 : topen_kept SK SEGS B lyc Sc W memc W4 (ms_mem m5) (spZ regs - TPCAP_SOURCE_OPEN_STK) (spZ regs) (fun a => ps <= a < ps + 22))
  by (apply (topen_kept_upd lyc Sc W memc mdc W4 mem4 (ms_mem m5) _ _ _ (fun a => ps <= a < ps + 8) HAR KT1);
      [ intros a Ha Hn; exact (KM2 a Ha Hn)
      | intros a Ha; destruct (HFfr a Ha) as [Hi Hc]; split; [exact Hc|]; split; [exact Hi|];
        split; [intros b0 m0 _ _; lia | intros c q _ _; lia]
      | intros a Ha; apply Hpres5; lia ]) end).
all: assert (KT3 : topen_kept SK SEGS B lyc Sc W memc W4 mem2 (spZ regs - TPCAP_SOURCE_OPEN_STK) (spZ regs) (fun a => ps <= a < ps + 22)).
all: try (apply (topen_kept_upd lyc Sc W memc mdc W4 _ mem2 _ _ _
     (fun a => (F <= a < F + 8) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16) \/ a = FL) HAR KT2);
  [ intros a Ha HnZ; apply UN; [exact Ha | intros H; apply HnZ; left; exact H | intros H; apply HnZ; right; left; exact H
    | intros H; apply HnZ; right; right; exact H]
  | intros a HZa; destruct (HAP a ltac:(destruct HZa as [H|[H|H]]; [left; lia | right; left; exact H | right; right; exact H]))
      as (Ha & Hi & Hb & Hf2);
    split; [lia|]; split; [exact Hi|]; split;
    [ intros b0 m0 Hb0 Hr; exfalso; apply (Hb b0 m0); [rewrite Hab; apply in_or_app; left; exact Hb0 | exact Hr]
    | intros c q Hcq Hr; exfalso; destruct (Hf2 c q Hcq) as [Hf3 Hf4]; destruct Hr; contradiction ]
  | intros a Ha; apply Hpres2; lia ]).
all: assert (Hm2 : mo_le MT S3 S4 (mo_free MT + mo_free MT)) by (eapply (asfm_close _ _ _ _ FM); [exact HJc4 | exact HPf | exact HPerm4]).
all: (lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?m5) =>
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W4) m5) 1
    (YP09.mkRegion (Some 19%nat) 0 24 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))]) HS eq_refl) as HRps;
  cbn [restrict ms_mem] in HRps;
  pose proof (field_of_region Ex _ 19 ps _ 0 24 0 8 0 8%N (SLit 0) 0 HRps U19' ltac:(left; reflexivity) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)) as Vps0;
  rewrite Z.add_0_r in Vps0 end).
all: exists ly4, (stack_free_state 1 fpos S4), regs2, mem2, md2.
all: split; [reflexivity|].
all: split; [exact HP2|].
all: split; [rewrite Hfrs2, Hfrsc; reflexivity|].
all: split; [rewrite Hfds2, !(proj1 (wvb_fds_fs _ _ _)), HFD4, !(proj1 (wvb_fds_fs _ _ _)); exact Hfds|].
all: split; [rewrite Hfs2, !(proj2 (wvb_fds_fs _ _ _)), HFS4, !(proj2 (wvb_fds_fs _ _ _)); exact Hfs|].
all: split; [exact KT3|].
all: split; [apply (mo_le_open_free Sc S4 fpos _ (mo_le_trans MT MLAW _ _ _ _ _ Hmo Hm2)); unfold OPEN_METER; lia|].
all: split; [vmf MBps V12; lia|].
all: split; [vmf MBps V16; lia|].
all: split; [vmf MBps V20; lia|].
all: right.
all: split; [eapply (ajournal_mono_k SEGS B); [exact HJ2 | unfold EV_OPEN, EV_FUZZ_FOPEN; lia]|].
all: split; [exact Ha0|].
all: split; [exact Hgood|].
all: split; [eapply vm_frame; [|exact Vps0]; intros x Hx; apply (mbyte_of_aview SEGS); apply UNps; lia|].
all: split; [intros i Hi; rewrite KMps by lia; exact (V8 i Hi)|].
all: split; [unfold ablocks; rewrite blocks_stack_free_state; fold (ablocks B ly4 S4); exact HPerm4|].
all: assert (HIE : pcap_img_end = (symaddr ImgPages.AsanUbsan.top)) by reflexivity.
all: (lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m5) =>
  apply (asource_none_frame K (rdW W4 (ms_mem m5)));
  [ intros a Ha; pose proof (src_env_img a Ha) as Hk; destruct (asil_env _ _ _ _ ASIL a Ha) as [Hi _];
    apply (mbyte_of_aview SEGS); apply UN; [lia | | |];
    [ intros H; destruct (HAP a ltac:(left; lia)) as (_ & Hni & _); exact (Hni Hi)
    | intros H; destruct (HAP a ltac:(right; left; exact H)) as (_ & Hni & _); exact (Hni Hi)
    | intros H; destruct (HAP a ltac:(right; right; exact H)) as (_ & Hni & _); exact (Hni Hi) ]
  | apply (asource_none_frame K (rdW W4 mem4)); [| exact HSN4];
    intros a Ha; pose proof (src_env_img a Ha) as Hk; destruct (asil_env _ _ _ _ ASIL a Ha) as [Hi _];
    apply (mbyte_of_aview SEGS); apply KM2; [lia|]; intros H; exact (proj1 (HFfr a H) Hi) ] end).
Qed.

(* A run whose regions all have empty windows leaves the memory as it was. *)
Ltac frame_same HF EQ :=
  lazymatch type of HF with frame_of _ _ (ms_mem ?a) (ms_mem ?b) =>
    assert (EQ : ms_mem b = ms_mem a) by
      (apply functional_extensionality; intros x; apply HF; intros (r & Hin' & Hr); vm_compute in Hin';
       repeat (destruct Hin' as [<- | Hin']; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia |]); destruct Hin') end.

(* ---- the read cut: 0x8138c `bne a0,s9` and the header ----------------------------------------------------- *)
Theorem op_from_read : op_from SK B K MT FM_RA CTX roimg (op_gi_read SK B K MT).
Proof.
intros cx fpos ly3 S3 W3 ms md3 HPRE HGI.
destruct HGI as (f & kr & Hpc & Hmid & Hn1 & Hf4096 & Hf16 & Hab & R10 & Hkr & Hhdr & HSRC & HFPinc & Hmo).
pose proof Hmid as Hmid0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfin3 : In (f, SRC_FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
pose proof Hmid as (Hrv & Hsvc & Hrom & Hfr & Hfcsr & HJ & Hkk & Hnev & Hfrs3 & Hnin & HfsS & R2 & R8 & R9 & R18 & R19 &
  R20 & R21 & R22 & R23 & R24 & R25 & R3 & R4 & R26 & R27 & Hra & Hsav & HMG & HO10 & HO11 & HFLP & Hlsh & Hsh &
  Vf & V12 & V16 & V20 & V8 & HKEPT & Hfds & Hfs & Hmeta & Hrod & Hch).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms) md3 f SRC_FILE_BLOCK (proj1 HJ) Hfin3) as (_ & _ & Hfceil & Hfia & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Hfceil, Hfia.
destruct (rd_entry cx fpos ly3 S3 W3 ms md3 f OP_CUT_READ HPRE Hmid Hpc ltac:(lia)) as [HS SHOK].
pose proof (fun a => tail_apart cx fpos ly3 S3 W3 (ms_mem ms) md3 (o_k cx + 1) a HPRE HJ) as HAP.
pose proof HPRE as HPRE0.
destruct cx as [STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos].
unfold oSH, oFL, oF, osp1 in *. unfold op_mid in Hmid. unfold op_pre in HPRE.
cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k
  o_regs o_ch o_ps o_n o_b o_M o_C o_cid o_pos] in *.
destruct HPRE as (HJc & HROD & Hraw & Hra4 & Hgp & Htp & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & Hown & Hfa1 & Hfa2 & _ &
  Hps8 & Hsh0 & _ & _ & _ & _ & _ & _ & _ & _ & HnC & _ & Hinput & _ & HEV & _).
pose proof HJc as (HAR & _ & _ & _ & _ & Hfrsc & _).
pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct (ly_F_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [EFA3 EFL3].
destruct (ly_F_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as [EFAc EFLc].
assert (EFA : forall c q, frame_addr ly3 c q = frame_addr lyc c q) by (intros c q; rewrite EFA3, EFAc; reflexivity).
assert (EFL : forall c q, flag_addr ly3 c q = flag_addr lyc c q) by (intros c q; rewrite EFL3, EFLc; reflexivity).
clear EFA3 EFL3 EFAc EFLc.
assert (HTS : TPCAP_SOURCE_OPEN_STK = 18736) by reflexivity.
unfold OP_CID, OP_HDR in *.
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
assert (Hin3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hin).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hc4096 & Hcceil & Hcapp).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hcapp, Hfia.
set (F := frame_addr lyc 1 fpos) in *. set (FL := flag_addr lyc 1 fpos) in *.
set (sp1 := 32 * ((spZ regs - OPEN_FRAME) / 32)) in *.
assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply u64_range).
destruct (osp1_facts (spZ regs) ltac:(lia) Hal16) as (Hsp1r & Hsp1al).
change OPEN_FRAME with 96 in sp1. fold sp1 in Hsp1r, Hsp1al.
remember (Eimg (Ereg (ms_regs ms) (op_extra FL (nth 0 C 0) (nth 1 C 0) (nth 2 C 0) (nth 3 C 0) f regs))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall nn, (nn < A_TEXT)%nat -> ew E nn = ew (Ereg (ms_regs ms) (op_extra FL (nth 0 C 0) (nth 1 C 0) (nth 2 C 0) (nth 3 C 0) f regs)) nn)
  by (intros nn Hn; subst E; apply Eimg_low; exact Hn).
assert (EX : forall a, (32 <= a < 50)%nat -> ew E a = nth (a - 32) (op_extra FL (nth 0 C 0) (nth 1 C 0) (nth 2 C 0) (nth 3 C 0) f regs) (Z_to_bv 64 0))
  by (intros a Ha; rewrite EL by (unfold A_TEXT; lia); replace a with (32 + (a - 32))%nat at 1 by lia; apply ew_Ereg_extra).
assert (ER : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> (nn < 32)%nat -> ew E nn = getr (ms_regs ms) r)
  by (intros nn r Hr Hn; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hr).
assert (E2 : ew E 2 = w64 sp1) by (rewrite (ER 2%nat 2%bv eq_refl) by lia; exact R2).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (ER 3%nat 3%bv eq_refl) by lia; exact R3).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (ER 4%nat 4%bv eq_refl) by lia; exact R4).
assert (E8 : ew E 8 = w64 (spZ regs)) by (rewrite (ER 8%nat 8%bv eq_refl) by lia; exact R8).
assert (E18 : ew E 18 = w64 F) by (rewrite (ER 18%nat 18%bv eq_refl) by lia; exact R18).
assert (E19 : ew E 19 = w64 ps) by (rewrite (ER 19%nat 19%bv eq_refl) by lia; exact R19).
assert (E21 : ew E 21 = w64 (SHADOW_OFF + F / 8)) by (rewrite (ER 21%nat 21%bv eq_refl) by lia; exact R21).
assert (E26 : ew E 26 = getr regs 26) by (rewrite (ER 26%nat 26%bv eq_refl) by lia; exact R26).
assert (E27 : ew E 27 = getr regs 27) by (rewrite (ER 27%nat 27%bv eq_refl) by lia; exact R27).
assert (E32 : ew E 32 = w64 SB_OP) by (rewrite (EX 32%nat) by lia; reflexivity).
assert (E33 : ew E 33 = w64 FL) by (rewrite (EX 33%nat) by lia; reflexivity).
assert (E49 : ew E 49 = w64 f) by (rewrite (EX 49%nat) by lia; reflexivity).
assert (EXR : forall j, (j < 11)%nat -> ew E (38 + j) = nth (6 + j) (op_extra 0 0 0 0 0 0 regs) (Z_to_bv 64 0)).
{ intros j Hj. rewrite (EX (38 + j)%nat) by lia. replace (38 + j - 32)%nat with (6 + j)%nat by lia.
  do 11 (destruct j as [|j]; [reflexivity|]). lia. }
assert (E10 : ew E 10 = w64 kr) by (rewrite (ER 10%nat 10%bv eq_refl) by lia; exact R10).
assert (E20 : ew E 20 = w64 (F + 32)) by (rewrite (ER 20%nat 20%bv eq_refl) by lia; exact R20).
assert (E34 : ew E 34 = w64 (nth 0 C 0)) by (rewrite (EX 34%nat) by lia; reflexivity).
assert (E35 : ew E 35 = w64 (nth 1 C 0)) by (rewrite (EX 35%nat) by lia; reflexivity).
assert (E36 : ew E 36 = w64 (nth 2 C 0)) by (rewrite (EX 36%nat) by lia; reflexivity).
assert (E37 : ew E 37 = w64 (nth 3 C 0)) by (rewrite (EX 37%nat) by lia; reflexivity).
clear HEdef EL EX ER.
(* the frames and the FILE block are apart *)
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms) md3 f SRC_FILE_BLOCK cid pos HAR3 Hfin3 Hin3) as DfP.
assert (HinF3 : In (1, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms) md3 f SRC_FILE_BLOCK 1 fpos HAR3 Hfin3 HinF3) as DfF.
unfold zdisjoint in DfP, DfF. cbn [fst snd] in DfP, DfF. rewrite EFA in DfP, DfF. change (req_size SRC_FILE_BLOCK) with 1304 in DfP, DfF.
change (fs_frame_bytes 1) with 128 in DfF. fold F in DfF.
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms) md3 1 fpos HAR3 HinF3) as (HF4096 & HFceil & HFapp).
rewrite EFA in HF4096, HFceil, HFapp. change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp. fold F in HF4096, HFceil, HFapp.
assert (U8 : bv_unsigned (ew E 8) = spZ regs) by (rewrite E8; apply unsigned_lit_small; exact Hsp64).
assert (U18 : bv_unsigned (ew E 18) = F) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = ps) by (rewrite E19; apply unsigned_lit_small; lia).
destruct (FFL ly3 S3 W3 (ms_mem ms) md3 1 fpos HAR3 HinF3) as (_ & _ & _ & (HFL4096 & _ & HFLceil)).
rewrite EFL in HFL4096, HFLceil. fold FL in HFL4096, HFLceil.
assert (U33 : bv_unsigned (ew E 33) = FL) by (rewrite E33; apply unsigned_lit_small; lia).

destruct (Hinput Hn1) as (Hinb0 & Hgb0 & Hbok).
assert (HCb : forall j, 0 <= nth j C 0 < 256).
{ intros j. destruct (Nat.lt_ge_cases j (length C)) as [Hj|Hj].
  - exact (proj1 (Forall_forall _ _) Hbok _ (nth_In C 0 Hj)).
  - rewrite nth_overflow by exact Hj. lia. }
destruct (in_split _ _ Hin) as (l2 & l3 & El).
pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms) md3 (1, fpos) (cid, pos) [] l2 l3 HAR3
  ltac:(rewrite Hfrs3, El; reflexivity)) as DFc.
unfold zdisjoint, frame_rng in DFc. cbn [fst snd] in DFc. rewrite !EFA in DFc. change (fs_frame_bytes 1) with 128 in DFc. fold F in DFc.
assert (Hkr24 : 1 <= kr <= 24) by lia.
assert (U10 : U E (SOff 10 0) = kr) by (apply U_atom; [exact E10 | lia]).
pose proof HS as HS0.
(* 0x8138c `bne a0,s9`: kr <> 24 is the short read, to 0x81400 *)
psrr_branch_tok RUN BR HS SHOK OPspan.
- rewrite branch_ne_U, U10, U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hgood : pcap_goodZ C = false) by (unfold pcap_goodZ; replace (24 <=? Z.of_nat (length C)) with false; [reflexivity|];
    symmetry; apply Z.leb_gt; lia).
  paj_run_to_tok RUNTO HS HJ SHOK OPspan OP_SHORT; [ ro_awr | ].
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?m1) =>
    frame_same HF EM;
    assert (REG : forall r, In r mid_regs -> getr (ms_regs m1) r = getr (ms_regs ms) r) by
      (intros r Hr; rewrite (st_ok_pi_restrict_reg _ _ _ _ r HS), (st_ok_pi_restrict_reg _ _ _ _ r HS0);
       cbn [mid_regs In] in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr);
    pose proof HS as (Hf1 & Hpc1 & Hsv1 & Hrv1 & Hfc1 & Hrom1 & _);
    cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom abs_ss setpc ss_pc ss_resv resv_denot] in Hf1, Hpc1, Hsv1, Hrv1, Hfc1, Hrom1;
    apply (op_fclose (mkOCX STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos) fpos ly3 S3 W3 m1 _
      f kr OP_SHORT HPRE0 (or_introl eq_refl) Hpc1
      (op_mid_move _ fpos f _ 24 OSH_in 1 ly3 S3 W3 ms m1 md3 _ Hmid0 Hrv1 Hsv1 Hrom1 Hf1 Hfc1 REG EM HJ
         (proj1 (wvb_fds_fs _ _ _)) (proj2 (wvb_fds_fs _ _ _)))
      Hn1 Hf4096 Hf16 Hab ltac:(rewrite EM; exact HSRC) HFPinc Hmo Hgood)
  end.

- rewrite branch_ne_U, U10, U_lit in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc. subst kr. rename Hc into H24.
  assert (Hn24 : 24 <= n) by lia.
  replace (Z.to_nat (Z.min 24 n)) with 24%nat in Hhdr by lia.
  assert (Hc4 : forall j, (j < 4)%nat -> val_mem SEGS (rdW W3 (ms_mem ms)) (F + 32 + Z.of_nat j) 1 (nth j C 0)).
  { intros j Hj. rewrite <- (nth_firstn_lt C 24 j) by lia. apply (Hhdr j). rewrite length_firstn. lia. }
  assert (U20 : bv_unsigned (ew E 20) = F + 32) by (rewrite E20; apply unsigned_lit_small; lia).
  (* the first four header bytes, F + 32 .. F + 35 (s4, 0x81398..0x813a4), as a region *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    pose proof (st_ok_pi_add_region Ex ssx msx r_hdr HS eq_refl
      ltac:(unfold region_ok, r_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val restrict ms_mem];
            rewrite U20; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
            repeat apply Forall_cons; try apply Forall_nil;
            lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 1 (SOff ?a 0))) =>
              let j := eval cbv in (a - 34)%nat in
              apply (chunk_ok_val SEGS Ex _ (F + 32) o 1 (SOff a 0) (nth j C 0));
              [ cbn [sv_denot]; rewrite Z.add_0_r; first [rewrite E34 | rewrite E35 | rewrite E36 | rewrite E37]; apply Z_to_bv_bv_unsigned
              | pose proof (HCb j); lia | lia
              | replace (F + 32 + o) with (F + 32 + Z.of_nat j) by (simpl; lia); exact (Hc4 j ltac:(lia)) ] end)
      ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
            cbn [all_disjoint]; unfold extent_disjoint, r_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
            rewrite U20, U8, U19, U18; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp;
            repeat split; lia)) as HS2 end.
  clear HS. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
  (* G6: 0x81390 `addi a0,zero,-3`, 0x81394 `bgeu s4,a0` (to the `unimp` at 0x8153c) is decided by this run, NOT taken:
     decide_cond2 (Reusable/YP0e.v:932) on BC_GEU, decide_ltu2 (:922) / decide_ltu (Reusable/YP0m.v:673) with atom 20
     (s4 = F + 32) in [4128, 0x7fffff800020] (rd_facts) below the literal 2^64 - 3. Template: lib/U/Prog/
     pcap_source_open.v:410-412 at c8557374ad2e (premise :291 sp0 < 2^63, frame bounds :295-299); a working branch
     pcap_source_open_tl.v:65 (sha256 4aaa5af08467; internal record) (premise :44 s4 < 2^64 - 3). *)
  paj_run_tok RUN HS HJ SHOK OPspan; [ ro_awr | ].
  frame_same HF EQ0. clear HF HFr HG.
  set (c0 := nth 0 C 0) in *. set (c1 := nth 1 C 0) in *. set (c2 := nth 2 C 0) in *. set (c3 := nth 3 C 0) in *.
  assert (HM : U E magic_sv = c0 + 256 * c1 + 65536 * c2 + 16777216 * c3 + (if c3 <? 128 then 0 else 18446744069414584320)).
  { pose proof (HCb 0%nat) as B0. pose proof (HCb 1%nat) as B1. pose proof (HCb 2%nat) as B2. pose proof (HCb 3%nat) as B3.
    apply magic_U;
    [ rewrite E34; apply unsigned_lit_small; lia | rewrite E35; apply unsigned_lit_small; lia
    | rewrite E36; apply unsigned_lit_small; lia | rewrite E37; apply unsigned_lit_small; lia | lia | lia | lia | lia ]. }
  assert (HMZ : pcap_magicZ C = c0 + 256 * c1 + 65536 * c2 + 16777216 * c3) by (unfold pcap_magicZ; lia).
  assert (HlenC : (24 <=? Z.of_nat (length C)) = true) by (apply Z.leb_le; lia).
  pose proof (HCb 3%nat) as B3. fold c3 in B3. pose proof (HCb 0%nat) as B0. fold c0 in B0.
  pose proof (HCb 1%nat) as B1. fold c1 in B1. pose proof (HCb 2%nat) as B2. fold c2 in B2.
  (* 0x813c8 `beq a0,a1`: the swapped magic 0xd4c3b2a1, to 0x81420 *)
  psrr_branch_tok RUN BR HS SHOK OPspan.
  2: (fold magic_sv in Hc; rewrite branch_eq_U, HM, U_lit in Hc by lia; apply Z.eqb_neq in Hc;
      paj_run_tok RUN HS HJ SHOK OPspan; [ ro_awr | ];
      frame_same HF EQ1; clear HF HFr HG;
      (* 0x813d4 `bne a0,a1`: not the classic magic 0xa1b2c3d4 either, to 0x81444 *)
      psrr_branch_tok RUN BR HS SHOK OPspan).
  (* 0x81444: the bad magic *)
  2: (fold magic_sv in Hc0; rewrite branch_ne_U, HM, U_lit in Hc0 by lia; apply negb_true_iff, Z.eqb_neq in Hc0;
      assert (Hgood : pcap_goodZ C = false) by
        (unfold pcap_goodZ; rewrite HlenC, HMZ; cbn [andb]; apply orb_false_intro; apply Z.eqb_neq;
         case_eq (c3 <? 128); intros Hb; rewrite Hb in Hc, Hc0; first [apply Z.ltb_lt in Hb | apply Z.ltb_ge in Hb]; lia);
      paj_run_to_tok RUNTO HS HJ SHOK OPspan OP_BAD; [ ro_awr | ];
      lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?m1) =>
        frame_same HF EQ2; clear HF HFr HG;
        assert (EM : ms_mem m1 = ms_mem ms) by congruence;
        assert (REG : forall r, In r mid_regs -> getr (ms_regs m1) r = getr (ms_regs ms) r) by
          (intros r Hr; rewrite (st_ok_pi_restrict_reg _ _ _ _ r HS), (st_ok_pi_restrict_reg _ _ _ _ r HS0);
           cbn [mid_regs In] in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr);
        pose proof HS as (Hf1 & Hpc1 & Hsv1 & Hrv1 & Hfc1 & Hrom1 & _);
        cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom abs_ss setpc ss_pc ss_resv resv_denot] in Hf1, Hpc1, Hsv1, Hrv1, Hfc1, Hrom1;
        apply (op_fclose (mkOCX STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos) fpos ly3 S3 W3 m1 _
          f (Z.min 24 n) OP_BAD HPRE0 (or_intror eq_refl) Hpc1
          (op_mid_move _ fpos f _ 24 OSH_in 1 ly3 S3 W3 ms m1 md3 _ Hmid0 Hrv1 Hsv1 Hrom1 Hf1 Hfc1 REG EM HJ
             (proj1 (wvb_fds_fs _ _ _)) (proj2 (wvb_fds_fs _ _ _)))
          Hn1 Hf4096 Hf16 Hab ltac:(rewrite EM; exact HSRC) HFPinc Hmo Hgood)
      end).
  (* the two good magics: pcap_goodZ C and pcap_swZ C *)
  1: (fold magic_sv in Hc; rewrite branch_eq_U, HM, U_lit in Hc by lia; apply Z.eqb_eq in Hc;
      assert (HMv : pcap_magicZ C = 3569595041) by (rewrite HMZ; case_eq (c3 <? 128); intros Hb; rewrite Hb in Hc;
        first [apply Z.ltb_lt in Hb | apply Z.ltb_ge in Hb]; lia);
      assert (Hgood : pcap_goodZ C = true) by (unfold pcap_goodZ; rewrite HlenC, HMv; reflexivity);
      assert (Hsw : pcap_swZ C = 1) by (unfold pcap_swZ; rewrite HMv; reflexivity)).
  2: (fold magic_sv in Hc0; rewrite branch_ne_U, HM, U_lit in Hc0 by lia; apply negb_false_iff, Z.eqb_eq in Hc0;
      assert (HMv : pcap_magicZ C = 2712847316) by (rewrite HMZ; case_eq (c3 <? 128); intros Hb; rewrite Hb in Hc0;
        first [apply Z.ltb_lt in Hb | apply Z.ltb_ge in Hb]; lia);
      assert (Hgood : pcap_goodZ C = true) by (unfold pcap_goodZ; rewrite HlenC, HMv; reflexivity);
      assert (Hsw : pcap_swZ C = 0) by (unfold pcap_swZ; rewrite HMv; reflexivity)).
  (* ps->swapped (0x8143c / 0x813f0) writes ps[8, 12): the window of ps's region opens *)
  all: (lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?m1) =>
    assert (HPS1 : forall a, ps <= a < ps + 24 -> apresent (w_H W3) (ms_mem m1) a)
      by (intros a Ha; refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ _));
          right; right; right; exists cid, pos; split; [right; exact Hown|]; left; unfold in_zr; cbn [fst snd];
          rewrite EFA; lia);
    pose proof (ast_ok_pi_set_region Ex ssx (restrict (w_H W3) m1) 2 (r_ps 0 0) (r_ps 8 12) HS eq_refl eq_refl
      ltac:(vm_compute; reflexivity)
      (region_ok_rewindow SEGS Ex _ (r_ps 0 0) 8 12 (st_ok_pi_region_nth Ex ssx _ 2 (r_ps 0 0) HS eq_refl)
         ltac:(intros o Ho; unfold r_ps; cbn [YP09.r_base base_val restrict ms_mem]; rewrite U19;
               apply (apresent_writable SEGS); apply HPS1; lia))) as HS3 end).
  all: clear HS; rename HS3 into HS.
  all: (lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end).
  all: (paj_run_to_tok RUNTO HS HJ SHOK OPspan OP_EPI;
    [ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
        let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
      eapply awr_ok_cons_gen; [reflexivity | exact U19 | cbn [YP09.r_wlo YP09.r_whi]; intros ?a ?Ha;
        right; right; right; exists cid, pos; split; [right; exact Hown|]; left; unfold in_zr; cbn [fst snd]; rewrite EFA; lia |];
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]; apply awr_ok_nil
    | ]).
  all: (lazymatch type of HFr with frame_of _ ?rsP (rdW _ (ms_mem ?mp)) (rdW _ (ms_mem ?m5)) =>
    assert (EMp : ms_mem mp = ms_mem ms) by congruence;
    assert (KMr : forall a, 0 <= a < 2 ^ 64 -> ~ (ps + 8 <= a < ps + 12) ->
                    aview SEGS (w_H W3) (ms_mem m5) a = aview SEGS (w_H W3) (ms_mem ms) a)
      by (intros a Ha Hn; rewrite <- EMp;
          apply (kept_of_frame (segs := SEGS) _ rsP (w_H W3) (ms_mem mp) (ms_mem m5) (fun a => ps + 8 <= a < ps + 12) HFr);
          [ intros bb wlo whi aa HinW HrrW; vm_compute in HinW;
            repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW; rewrite ?U19 in HrrW; lia|]);
            destruct HinW
          | exact Ha | exact Hn ]) end).
  all: (lazymatch type of HS with st_ok_pi _ _ _ ?ss5 (restrict _ ?ms5) =>
    destruct (mf_rdwords E ss5 ms5 (w_H W3) regs (spZ regs) F FL 1 3 HS eq_refl eq_refl U8 U18 U33 EXR) as (Rra & Rsav & RFL);
    pose proof HS as (Hf5 & Hpc5 & Hsv5 & Hrv5 & Hfc5 & Hrom5 & _);
    cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom abs_ss setpc ss_pc ss_resv resv_denot] in Hf5, Hpc5, Hsv5, Hrv5, Hfc5, Hrom5
    end).
  all: prreg HS (8%bv : bv 5) T8; prreg HS (18%bv : bv 5) T18; prreg HS (22%bv : bv 5) T22; prreg HS (21%bv : bv 5) T21;
    prreg HS (3%bv : bv 5) T3; prreg HS (4%bv : bv 5) T4; prreg HS (26%bv : bv 5) T26; prreg HS (27%bv : bv 5) T27;
    prreg HS (10%bv : bv 5) T10.
  all: (lazymatch goal with |- SRr _ _ (mkCfg ?ms5 ?md5) _ =>
    assert (T10' : getr (ms_regs ms5) 10 = w64 0) by (rewrite T10; reflexivity);
    assert (T8' : getr (ms_regs ms5) 8 = w64 (spZ regs)) by (rewrite T8; exact E8);
    assert (T18' : getr (ms_regs ms5) 18 = w64 F) by (rewrite T18; exact E18);
    assert (T22' : getr (ms_regs ms5) 22 = w64 F) by (rewrite T22; exact E18);
    assert (T21' : getr (ms_regs ms5) 21 = w64 (SHADOW_OFF + F / 8)) by (rewrite T21; exact E21);
    assert (T3' : getr (ms_regs ms5) 3 = getr regs 3) by (rewrite T3; exact E3);
    assert (T4' : getr (ms_regs ms5) 4 = getr regs 4) by (rewrite T4; exact E4);
    assert (T26' : getr (ms_regs ms5) 26 = getr regs 26) by (rewrite T26; exact E26);
    assert (T27' : getr (ms_regs ms5) 27 = getr regs 27) by (rewrite T27; exact E27);
    apply (op_epi (mkOCX STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos) fpos ly3 S3 W3 ms5 md5
      (k + 1) OP_EPI 0 _ HPRE0 HJ Hrv5 Hsv5 Hrom5 Hf5 Hfc5 Hpc5 (or_intror (conj eq_refl T10'))
      T8' T18' T22' T21' T3' T4' T26' T27' Rra Rsav RFL) end).
  all: intros mem2 md2 regs2 HJ2 HP2 Ha0 UN Hfds2 Hfs2.
  all: unfold op_post, tpcap_source_open_post, oSH, oFL, oF in *.
  all: cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k
    o_regs o_ch o_ps o_n o_b o_M o_C o_cid o_pos] in *.
  all: unfold OP_CID in *; fold F FL in UN.
  all: pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & _).
  all: pose proof HJ2 as (_ & _ & _ & _ & _ & Hfrs2 & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  all: assert (NT : forall a, ps <= a < ps + 24 -> ~ ((F <= a < F + 128) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16) \/ a = FL))
    by (intros a Ha HT; destruct (HAP a HT) as (_ & _ & _ & Hfr2); apply (proj1 (Hfr2 cid pos Hin));
        unfold frame_rng, in_zr; cbn [fst snd]; lia).
  all: (lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss5 (restrict _ ?m5) =>
    assert (UN5 : forall a, 0 <= a < 2 ^ 64 -> ~ ((F <= a < F + 128) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16) \/ a = FL) ->
                    aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem m5) a)
      by (intros a Ha HnT; apply UN; [exact Ha | intros H; apply HnT; left; lia | intros H; apply HnT; right; left; exact H
          | intros H; apply HnT; right; right; exact H]);
    assert (MBc : forall a, 0 <= a < 2 ^ 64 -> ~ ((F <= a < F + 128) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16) \/ a = FL) ->
                    ~ (ps + 8 <= a < ps + 12) -> mbyte SEGS (rdW W3 mem2) a = mbyte SEGS (rdW W3 (ms_mem ms)) a)
      by (intros a Ha HnT Hn8; apply (mbyte_of_aview SEGS); rewrite UN5 by assumption; apply KMr; assumption);
    (* ps->swapped, from the store's chunk *)
    let r2 := eval vm_compute in (nth 2 (ss_mem ss5) r_mf) in
    lazymatch r2 with YP09.mkRegion _ _ _ _ _ ?cs =>
    lazymatch cs with context [YP09.mkChunk 8 (CVal 4 (SLit ?v))] =>
      pose proof (st_ok_pi_region_nth Ex ss5 (restrict (w_H W3) m5) 2 r2 HS eq_refl) as HRps;
      cbn [restrict ms_mem] in HRps;
      pose proof (field_of_region Ex _ 19 ps cs 0 24 8 12 8 4%N (SLit v) v HRps U19 ltac:(cbn; tauto) eq_refl
        ltac:(cbn; lia) ltac:(cbn; lia)) as Vsw end end;
    assert (Hsw' : val_mem SEGS (rdW W3 mem2) (ps + 8) 4 (pcap_swZ C))
      by (rewrite Hsw; eapply vm_frame; [|exact Vsw]; intros x Hx; apply (mbyte_of_aview SEGS); apply UN5;
          [lia | intros HT; exact (NT x ltac:(lia) HT)])
    end).
  all: assert (HnFp : forall a, F <= a < F + 128 -> ~ (ps <= a < ps + 24)) by (intros a Ha Hp; exact (NT a Hp (or_introl Ha))).

  all: (lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m5) =>
    assert (KT1 : topen_kept SK SEGS B lyc Sc W memc W3 (ms_mem m5) (spZ regs - TPCAP_SOURCE_OPEN_STK) (spZ regs) (fun a => ps <= a < ps + 22))
      by (apply (topen_kept_upd lyc Sc W memc mdc W3 (ms_mem ms) (ms_mem m5) _ _ _ (fun a => ps + 8 <= a < ps + 12) HAR HKEPT);
          [ intros a Ha Hn; exact (KMr a Ha Hn)
          | intros a Ha; split; [lia|]; split; [exact (frm_img SEGS B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(lia))|];
            split; [intros b0 m0 _ _; lia | intros c q _ _; lia]
          | intros a Ha; apply Hpres5; lia ]) end).
  all: assert (KT2 : topen_kept SK SEGS B lyc Sc W memc W3 mem2 (spZ regs - TPCAP_SOURCE_OPEN_STK) (spZ regs) (fun a => ps <= a < ps + 22)).
  all: try (apply (topen_kept_upd lyc Sc W memc mdc W3 _ mem2 _ _ _
       (fun a => (F <= a < F + 8) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16) \/ a = FL) HAR KT1);
    [ intros a Ha HnZ; apply UN; [exact Ha | intros H; apply HnZ; left; exact H | intros H; apply HnZ; right; left; exact H
      | intros H; apply HnZ; right; right; exact H]
    | intros a HZa; destruct (HAP a ltac:(destruct HZa as [H|[H|H]]; [left; lia | right; left; exact H | right; right; exact H]))
        as (Ha & Hi & Hb & Hf2);
      split; [lia|]; split; [exact Hi|]; split;
      [ intros b0 m0 Hb0 Hr; exfalso; apply (Hb b0 m0); [rewrite Hab; apply in_or_app; left; exact Hb0 | exact Hr]
      | intros c q Hcq Hr; exfalso; destruct (Hf2 c q Hcq) as [Hf3 Hf4]; destruct Hr; contradiction ]
    | intros a Ha; apply Hpres2; lia ]).
  all: assert (Hps_rng : 4096 <= ps /\ ps + 24 <= alloc_ceiling /\ alloc_ceiling <= 140737479966720) by (clear - Hfa1 Hfa2 Hc4096 Hcceil C1; lia).
  all: assert (MBps : forall a, ps <= a < ps + 8 \/ ps + 12 <= a < ps + 24 -> mbyte SEGS (rdW W3 mem2) a = mbyte SEGS (rdW W3 (ms_mem ms)) a)
    by (intros a Ha; apply MBc; [clear - Ha Hps_rng; lia | intros HT; exact (NT a ltac:(clear - Ha; lia) HT) | clear - Ha; lia]).
  all: destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b n HAR Hinb0) as (_ & Hb4096 & Hbceil & _).
  all: pose proof (req_size_pos n ltac:(clear - Hn1; lia)) as [_ Hreqb].
  all: pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc b n cid pos HAR Hinb0 Hin) as Dbf.
  all: unfold zdisjoint in Dbf; cbn [fst snd] in Dbf.
  all: assert (Hinb3 : In (b, n) (ablocks B ly3 S3)) by (rewrite Hab; apply in_or_app; left; exact Hinb0).
  all: assert (HIE : pcap_img_end = (symaddr ImgPages.AsanUbsan.top)) by reflexivity.
  all: rewrite H24 in HSRC.
  all: exists ly3, (stack_free_state 1 fpos S3), regs2, mem2, md2.
  all: split; [reflexivity|].
  all: split; [exact HP2|].
  all: split; [rewrite Hfrs2, Hfrsc; reflexivity|].
  all: split; [rewrite Hfds2, !(proj1 (wvb_fds_fs _ _ _)); exact Hfds|].
  all: split; [rewrite Hfs2, !(proj2 (wvb_fds_fs _ _ _)); exact Hfs|].
  all: split; [exact KT2|].
  all: split; [apply (mo_le_open_free Sc S3 fpos _ Hmo); unfold OPEN_METER; pose proof (mo_free_nonneg MT MLAW); clear - H; lia|].
  all: split; [eapply vm_frame; [|exact V12]; intros x Hx; apply MBps; right; clear - Hx; cbn in Hx; lia|].
  all: split; [eapply vm_frame; [|exact V16]; intros x Hx; apply MBps; right; clear - Hx; cbn in Hx; lia|].
  all: split; [eapply vm_frame; [|exact V20]; intros x Hx; apply MBps; right; clear - Hx; cbn in Hx; lia|].
  all: left.
  all: split; [eapply (ajournal_mono_k SEGS B); [exact HJ2 | unfold EV_FUZZ_FOPEN; clear; lia]|].
  all: split; [exact Ha0|].
  all: split; [exact Hgood|].
  all: exists f.
  all: split; [clear - Hf4096; lia|].
  all: split; [exact Hf16|].
  all: split; [unfold ablocks; rewrite blocks_stack_free_state; fold (ablocks B ly3 S3); exact Hab|].
  all: split; [eapply vm_frame; [|exact Vf]; intros x Hx; apply MBps; left; clear - Hx; cbn in Hx; lia|].
  all: split; [exact Hsw'|].
  all: split; [|unfold stack_free_state; apply (mo_le_set_fs_r MT MLAWF); exact Hmo].
  all: apply (asource_at_frame K (rdW W3 (ms_mem ms)) (rdW W3 mem2) f b C 24); [|exact HSRC].
  all: intros a Ha; unfold SRC_FILE_BLOCK in Ha.
  all: assert (Hlen : Z.of_nat (length C) = n) by (clear - HnC; lia).
  all: destruct Ha as [Ha | [Ha | Ha]].
  1,4: (apply MBc;
       [ clear - Ha Hf4096 Hfceil C1; lia
       | intros HT; destruct (HAP a HT) as (_ & _ & Hbb & _); apply (Hbb f SRC_FILE_BLOCK Hfin3);
         change (req_size SRC_FILE_BLOCK) with 1304; clear - Ha; lia
       | clear - Ha DfP Hfa1 Hfa2; lia ]).
  1,3: (rewrite Hlen in Ha; apply MBc;
       [ clear - Ha Hb4096 Hbceil Hreqb C1; lia
       | intros HT; destruct (HAP a HT) as (_ & _ & Hbb & _); apply (Hbb b n Hinb3); clear - Ha Hreqb; lia
       | clear - Ha Dbf Hfa1 Hfa2 Hreqb; lia ]).
  all: (pose proof (src_env_img a Ha) as Hk; destruct (asil_env _ _ _ _ ASIL a Ha) as [Hi _];
        apply MBc; [rewrite HIE in Hk; clear - Hk; lia | intros HT; destruct (HAP a HT) as (_ & Hni & _); exact (Hni Hi)
        | intros Hp; exact (frm_img SEGS B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(clear - Hp Hfa1 Hfa2; lia) Hi)]).
Qed.


End e.
End d.
End b.

(* The sink-head instance is explicit on every exported theorem (a Theorem Labs lane, 21:57Z), as in lib/B/Prog/PcapSourceClose.v:663-671:
   the only global sink_head instance in this closure is the plain build's, so a caller names this image's head. *)
Arguments op_from_null {fx rc} SK {PI}.
Arguments op_from_read {fx rc} SK {PI}.
Arguments op_fclose {fx rc} SK {PI}.
Arguments op_epi {fx rc} SK {PI}.
Arguments epi_entry {fx rc} SK {PI}.
Arguments rd_entry {fx rc} SK {PI}.
Arguments op_mid_move {fx rc} SK {PI}.
Arguments tail_apart {rc} SK {PI}.
Arguments topen_kept_upd {rc} SK {PI}.
Arguments topen_kept_call {rc} SK {PI}.
Arguments src_env_img {rc} SK {PI}.
Arguments ly_F_journal {rc} SK {PI}.

(* GUARD: SK must stay explicit. SK is passed by position; were it implicit again, the positional SK
   would land on the next argument and this file would stop compiling. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) =>
  op_from_null (fx:=fx) (rc:=rc) SK (PI:=PI)).
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) =>
  op_from_read (fx:=fx) (rc:=rc) SK (PI:=PI)).
