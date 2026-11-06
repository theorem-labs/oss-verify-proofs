(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B's walk of pcap_source_open in the asan-ubsan instance of fuzz_pcap
   (libreac v1.9.0; pin fuzz_pcap.asan-ubsan, sha256 9e66f771f22a...; function at 0x811e0 =
   BASE + AF_pcap_source_open, AF = 0xa58), proving lib/A's image-generic contract tpcap_source_open_specX
   (lib/A/Prog/PcapSourceOpenDefs.v) at SEGS = pa_segs, rlo / rhi = pa_relro_lo / pa_relro_hi,
   apath / alen / afile = VAL (A_OBJ 3) / VAL (A_OBJ 4) / VAL (A_OBJ 2) (0x20d00 "<fuzz-input>", g_file_len
   0x5d3e40, g_file 0x5d3e60), with FM_RA and roimg as parameters. At ossv/recipes 25e3d17bdb50 (2026-10-29), there was no released proof of this function at
   this image (rule 24 lookup, a Theorem Labs lane, 22:35Z): the v1.8 ubsan proof (lib/U/Prog/pcap_source_open.v at
   origin/ossv/recipes c8557374ad2e) serves only as the template for the UBSan guards.

   The code. Up to the fopen call it is lib/A's ASan code byte for byte at
   other pcs (asan 0x8145c.. = asan-ubsan 0x811e0..): the prologue saves ra, s0 .. s9 (0x811e0..0x81210) and
   realigns s1 = sp = (sp - 96) & -32 (0x81218); the use-after-return flag is read through the GOT (0x81228
   auipc / 0x8122c ld, listing object 0 = 0x99750) from the runtime cell at 0x81234 (object 16 = 0xa17c0): the
   walk takes it as 1 (the kit's AR_const_law through al_const, with uar_cell_regionP (A_OBJ 16) holding SLit 1;
   the pin's file holds 0 and the runtime sets 1 at init), so 0x81240 `beqz a2` is not taken;
   __asan_stack_malloc_1(0x60) at 0x81248 returns the class-1 frame F (aj_stack_malloc_atS, YC85.v:292), whose
   two caller premises are discharged at op_to_call's frame request: count_cid 1 (frames Sc) < fs_frames 1 from
   op_pre's length (frames Sc) <= 7 through count_cid_le_length and 8 <= fs_frames 1, and the apath premise by
   op_SMP (stack_malloc_progressP from lib/Reusable/YG05.v:70, as cgif_file_fuzzer lib/A/ACed.v:129-130), so
   F >= 4096, 0x8125c `bnez s2` is taken and the machine-frame arm 0x81260..0x81278 is dead; then *(s1) = F
   (0x8127c), the header (0x41b58ab3, objects 10 and 11; 0x812a4..0x812ac), the twelve shadow bytes
   (0x812b8..0x812e4: 0xf1 x4, 0xf8 x3, 0xf3 x5), the mode literal "rb" (object 12, 0x812e8 / 0x812ec; HMODE)
   and the call of libreac_fuzz_fopen (0x812f4) through cl_callS (YC85.v:383) with FOPEN as the callee.

   The cut. This file walks the head: entry -> op_to_call (a Qed checkpoint at the call, op_at_call) ->
   head_to_fopen, which makes the call and establishes PcapSourceOpenPhF.v's op_fopen_ret at the return
   0x812f8. From there PcapSourceOpenPhM.v (op_from_fopen) walks to the two cuts of PcapSourceOpenPh.v and
   PcapSourceOpenB.v (op_from_null / op_from_read) to the return; pb_pcap_source_openX composes the three.
   The three UBSan guards are therefore decided outside this file, at these pcs and against these template lines:
   in PcapSourceOpenPhM.v 0x812f8 `beqz s3` (ps = 0, not taken: ps >= 4096 from op_pre's frame bounds; template
   :114 / :334, premise :93 / :290) and 0x81300 / 0x81304 `andi a0,s3,7; bnez a0` (ps mod 8 <> 0, not taken:
   op_pre's ps mod 8 = 0; template :115 / :335); in PcapSourceOpenB.v 0x81390 / 0x81394 `addi a0,zero,-3;
   bgeu s4,a0` (F + 32 >=u 2^64 - 3, not taken: F + 128 <= alloc_ceiling < 2^47; template :408-412, premise
   :291 and :295-299); all three
   go to the `unimp` at 0x8153c, and every ASan report path 0x81540..0x815b4 is dead because ps's 24 bytes are
   addressable and ps mod 8 = 0. In the head, op_at_call carries what those walks need: ps unwritten and still
   range_addressable, and op_fopen_ret's FILE-block footprint fact for the fclose of the tail.

   The callee hypotheses, used at this image as Section hypotheses: FOPEN : tlibreac_fuzz_fopen_specX
   (lib/A/Prog/PcapFuzzFopenDefs.v), AFREAD : afread_spec (lib/A/Stdio/PFreadISpec.v:138), AFCLOSE :
   afclose_source_spec (lib/A/Stdio/PFclose.v:209), ASM1 : astack_malloc_realizes (lib/Reusable/YG0d.v:285),
   ASF : astack_free_law (lib/Reusable/YG0d.v:301) and FFL : frame_flag_lawP (lib/Reusable/YCbq.v:797), the meter laws MLAW / MLAWF /
   FM, ASIL : asource_img_laws, and the kit's LAWS / TL / TLF / ML. Four instance obligations beyond the kit:
   ROK (roimg reads only image bytes outside the runtime's statics, errno and the open-file list head; applied at
   the fopen call to carry roimg from the entry memory across the prologue and the frame setup), HPATH (the path
   literal's shadow, as a law of every AR state: the frame request's kept clauses do not keep a global's shadow,
   YG0n.v:241 makes it aowned; discharged by the instance through AR_zshadow_law, YG0d.v:435-438), HGX (g_file_len
   and g_file are image bytes outside the runtime's statics and errno; the gx_ok shape of
   lib/A/Prog/PcapEntryDefs.v:366, 395, discharged by the harness), and RO : ro_below_ofl (as
   lib/A/Prog/PcapHarnessTail.v:37). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpen.v, with its module paths, module names and numbers changed; 574 of its 653 lines of code are new or changed and 1472 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_writeHead.v, with its module names changed; 369 of its 474 lines of code are new or changed and 548 lines of the source are left out. *)
(* nl_error on image A (fuzz_link.asan 0x86e4c, listing (internal path)
   (internal record, sha256 7ca564e0b716)): the walk of lib/A/Prog/nl_error_c.v `nl_error_acontract`, `nl_error_aproof`.

   The entry (this file): +0x00..+0x78, one token run (the 160-byte frame, `sd zero, 0(sp)`, the 13 saves,
   s0 := sp, `andi sp, sp, -0x20` (the alias of the seated facts names the realigned sp1 by atom 33), s1 := sp1,
   the cut into sp1 + 24, s7 := code, s2 := w, the two .got words, the side-stack switch cell (1, so `beqz a1` at
   +0x70 is not taken: the real-stack arm +0x84 is dead), s10 := the shadow base, s3 := 4096, a0 := 0x60), then
   frame_alloc_1 (0x3da88) through LinkWalkSide.v aj_gx_stack_malloc_at: it returns the class-1 side frame F
   (pos) on top of own, F >= 4096 (so `bnez s4` at +0x90 is taken: the real-stack arm +0x94 is dead), F's zeroed
   shadow, its flag word, and the kept clause of the call. The join JE at +0x7c (nl_error_defs.v ne_JEi) is then
   built from those facts, and the phases of nl_error_head.v, nl_error_puts.v, nl_error_mid.v, nl_error_tail.v
   carry it to the Post (the exit's `beqz s2` at +0x56c is dead since s2 = F >= 4096).

   w's shadow across frame_alloc_1: LinkWalkShadow.v shadow_transport (every class of byte a caller may write keeps
   its shadow facts; the image's by img_sh_eq). w's bytes across it: LinkWalkSide.v ajw_kept_call.

   The Section hypotheses: LAWS, LV, TL, TB, HSEGS (the instance's facts) and the callee contracts of
   link-a/plan/PLAN.md (internal record, sha256 2ce66196196e): frame_alloc_1 (ASM1), checked_memset (AMEMSET),
   checked_memcpy (AMEMCPY). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j YI0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal PaJournalFs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide LinkWalkShadow PcapRelro nl_error_c
nl_error_defs nl_error_kit nl_error_head nl_error_puts nl_error_mid nl_error_tail.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the symbolic entry state ----
   Atoms 0..31: the entry registers; 32: the shadow base; 33: the realigned sp1 = (sp - 160) & -32. Regions: the
   probe word sp - 160 and the 13 saves [sp - 104, sp) (both at the entry sp, atom 2), the cut's slot and F's spill
   slot [sp1 + 24, sp1 + 56), the shadow base's .got word and cell, the switch's .got word and cell. *)
Definition ne_facts0 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF (2 ^ 46 - 176) (2 ^ 47) 5)] []
    [(SAlu ALU_AND (SOff 2 (-160)) (SLit (-32)), SOff 33 0)].
Definition ne_ss0 : sstate :=
  mkSS AF_nl_error sr_atoms
    [YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [];
     YP09.mkRegion (Some 2%nat) (-160) (-152) (-160) (-152) [];
     YP09.mkRegion (Some 33%nat) 24 56 24 56 [];
     got_regionP; bcell_regionP 32; uar_got_regionP (A_OBJ 65); uar_cell_regionP (A_OBJ 65)]
    None ne_facts0.
Definition ne_extra0 (sp1 : Z) : list word := [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 sp1].

(* a byte writable at m1 is writable at m2 when its byte, if m1 holds it, is still visible at m2, and it is in no
   read-only segment (its view then comes from m2 or from a writable segment) *)
Lemma ne_writable_keep : forall segs (H : word -> bool) (m1 m2 : word -> option byte) a,
  0 <= a < 2 ^ 64 ->
  writable_at segs (mrestrict H m1) a ->
  (mbyte segs (mrestrict H m1) a <> None -> mbyte segs (mrestrict H m2) a <> None) ->
  ~ (exists s, In s segs /\ seg_writable s = false /\ Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s)) ->
  writable_at segs (mrestrict H m2) a.
Proof.
  intros segs H m1 m2 a Ha Hw1 Hm Hro. unfold writable_at, wview in *.
  destruct (mrestrict H m2 (Z_to_bv 64 a)) as [b2|] eqn:E2; [discriminate|].
  destruct (mrestrict H m1 (Z_to_bv 64 a)) as [b1|] eqn:E1; [|exact Hw1].
  assert (Hm2 : mbyte segs (mrestrict H m2) a <> None) by (apply Hm; unfold mbyte; rewrite E1; discriminate).
  unfold mbyte in Hm2. rewrite E2 in Hm2.
  unfold seg_rom, memory_read in Hm2. change (Z.of_N 1) with 1 in Hm2.
  destruct (find_segment segs (bv_unsigned (Z_to_bv 64 a)) 1) as [seg|] eqn:F; [|exfalso; exact (Hm2 eq_refl)].
  destruct (seg_readable seg); [|exfalso; exact (Hm2 eq_refl)].
  change (N.to_nat 1) with 1%nat in Hm2. cbn [segment_read_bytes] in Hm2.
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base seg))))
    as [bb|] eqn:Eb; [|exfalso; exact (Hm2 eq_refl)].
  destruct (seg_writable seg) eqn:Ew; [discriminate|].
  exfalso. destruct (find_segment_some_spec _ _ _ _ F) as (Hin & Hlo & Hhi).
  rewrite unsigned_lit_small in Hlo, Hhi by exact Ha.
  apply Hro. exists seg. split; [exact Hin|]. split; [exact Ew|]. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TL : PALib B.
(* the certificate of link's image: lib/A/AF0m.v PcapSyms *)
Hypothesis TB : AF0m.PcapSyms B.
(* the segments the listing is certified against (lib/A/AB1v.v tfibsegs); the link PAImg instance has it by
   reflexivity *)
Hypothesis HSEGS : pa_segs = AB1v.tfibsegs.
(* the callees (the table of link-a/plan/PLAN.md (internal record, sha256 2ce66196196e)): frame_alloc_1 (0x3da88), checked_memset (0x53214), checked_memcpy (0x52d78) *)
Hypothesis ASM1 : astack_malloc_realizes pa_segs B 1.
Hypothesis AMEMSET : aintrin_realizes pa_segs B OSet (pa_sigma LS___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes pa_segs B OCpy (pa_sigma LS___asan_memcpy).

Let errno_low := pal_env B TL.

Lemma ne_segs_img : forall a, in_img pa_segs a -> 0x10000 <= a < pcap_img_end.
Proof.
  intros a (sg & Hin & Hr). rewrite HSEGS in Hin. rewrite img_end_val.
  cbv [AB1v.tfibsegs] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn in Hr; lia |]). destruct Hin.
Qed.

Lemma ne_obj_vals :
  pa_val (A_OBJ 0) = 0xa1a28 /\ pa_val (A_OBJ 1) = 0xa19d0 /\ pa_val (A_OBJ 64) = 0xaa438 /\
  pa_val (A_OBJ 65) = 0xaa440 /\ pa_val A_TEXT = 0x821cc.
Proof.
  repeat split; first [rewrite (lv_text LV); reflexivity | rewrite (lv_obj LV) by (vm_compute; lia); reflexivity].
Qed.

(* frame_alloc_1's entry in the certificate's code table is the listing's call target *)
Lemma ne_hsm1 : pc_stack_malloc (as_code B) 1 = pa_sigma LS___asan_stack_malloc_1.
Proof. rewrite (AF0m.ts_code B TB), (lv_sigma LV). reflexivity. Qed.

(* a value chunk of the i-th region of a state *)
Lemma ne_chunk_nth_val : forall (H : word -> bool) E' s1 ms1 i r off sz e b v,
  st_ok SEGS E' s1 (restrict H ms1) -> nth_error (ss_mem s1) i = Some r ->
  base_val E' (YP09.r_base r) = b -> In (YP09.mkChunk off (CVal sz e)) (YP09.r_chunks r) ->
  sv_denot E' e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N sz) -> Z.of_N sz <= 8 ->
  val_mem SEGS (mrestrict H (ms_mem ms1)) (b + off) (N.to_nat sz) v.
Proof.
  intros H E' s1 ms1 i r off sz e b v HS Hi Hb Hin He Hv Hsz.
  pose proof (st_ok_region_nth (segs := SEGS) E' s1 (restrict H ms1) i r HS Hi) as (_ & _ & _ & Hcs).
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hb in Hck.
  exact (val_of_chunk_ok SEGS E' _ b off sz e v Hck He Hv Hsz).
Qed.

Lemma ne_val_kept : forall (H : word -> bool) m1 m2 a n v,
  (forall k, (k < n)%nat -> aview SEGS H m2 (a + Z.of_nat k) = aview SEGS H m1 (a + Z.of_nat k)) ->
  val_mem SEGS (mrestrict H m1) a n v -> val_mem SEGS (mrestrict H m2) a n v.
Proof.
  intros H m1 m2 a n v HK V k Hk. rewrite <- (V k Hk). apply (mbyte_of_aview SEGS). exact (HK k Hk).
Qed.

(* The entry state, from the journal at the call. *)
Lemma ne_entry_st : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - NL_ERROR_AK -> spZ regs <= sp0 ->
  st_ok_pi pa_segs pa_val (Eimg (Ereg regs (ne_extra0 (32 * ((spZ regs - 160) / 32))))) ne_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_nl_error)) memc (seg_rom pa_segs))).
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hal16 Hwlo Hwhi.
  pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : NL_ERROR_AK = 4272) by reflexivity. rewrite HK in Hwlo.
  destruct (aj_gx_const_cells SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc
    mdc k HJ)
    as (Kuar & Kguar & Kcell & Kgot).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
  rewrite (pal_got_uar B TL), (pal_uar_cell B TL) in Kguar. rewrite (pal_uar_cell B TL) in Kuar.
  destruct ne_obj_vals as (V0 & V1 & V64 & V65 & _).
  set (sp1 := 32 * ((spZ regs - 160) / 32)).
  destruct (sp1_facts (spZ regs - 160) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
    as (Hsp1r & Hsp1al32 & Hsp1al16).
  fold sp1 in Hsp1r, Hsp1al32, Hsp1al16.
  set (E := Eimg (Ereg regs (ne_extra0 sp1))).
  assert (EL : forall nn, (nn < A_TEXT)%nat -> ew E nn = ew (Ereg regs (ne_extra0 sp1)) nn)
    by (intros nn Hn; subst E; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 sp1)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (EO : forall i, (i < 66)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (pa_val (A_OBJ i)))
    by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (U33 : bv_unsigned (ew E 33) = sp1) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (VB : forall nn v, ew E nn = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some nn) = v).
  { intros nn v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
  pose proof (EO 0%nat ltac:(lia)) as EO0. pose proof (EO 1%nat ltac:(lia)) as EO1.
  pose proof (EO 64%nat ltac:(lia)) as EO64. pose proof (EO 65%nat ltac:(lia)) as EO65.
  rewrite V0 in EO0, Kguar. rewrite V1 in EO1, Kgot. rewrite V64 in EO64, Kgot, Kcell.
  rewrite V65 in EO65, Kguar, Kuar.
  rewrite restrict_mkst_fx. unfold ne_ss0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable pa_segs). apply Hpres. lia.
    + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable pa_segs). apply Hpres. lia.
    + cbn [base_val]. fold E. rewrite U33. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable pa_segs). apply Hpres. lia.
    + fold E. rewrite (VB (A_OBJ 1) 0xa19d0 EO1 ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val pa_segs E _ 0xa19d0 0 8 (SOff (A_OBJ 64) 0) 0xaa438);
        [cbn [sv_denot]; rewrite EO64, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword pa_segs (w_H W) memc _ _ Kgot).
    + fold E. rewrite (VB (A_OBJ 64) 0xaa438 EO64 ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val pa_segs E _ 0xaa438 0 8 (SOff 32 0) SHADOW_OFF);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; reflexivity | cbn; unfold SHADOW_OFF; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword pa_segs (w_H W) memc _ _ Kcell).
    + fold E. rewrite (VB (A_OBJ 0) 0xa1a28 EO0 ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val pa_segs E _ 0xa1a28 0 8 (SOff (A_OBJ 65) 0) 0xaa440);
        [cbn [sv_denot]; rewrite EO65, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword pa_segs (w_H W) memc _ _ Kguar).
    + fold E. rewrite (VB (A_OBJ 65) 0xaa440 EO65 ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val pa_segs E _ 0xaa440 0 4 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 pa_segs (w_H W) memc _ _ Kuar).
  - apply pairwise_disjoint_of_extents.
    unfold got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    fold E. rewrite (VB (A_OBJ 1) 0xa19d0 EO1 ltac:(lia)), (VB (A_OBJ 64) 0xaa438 EO64 ltac:(lia)),
      (VB (A_OBJ 0) 0xa1a28 EO0 ltac:(lia)), (VB (A_OBJ 65) 0xaa440 EO65 ltac:(lia)).
    cbn [base_val]. rewrite Usp, U33.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1a Hwlo Hwhi HSTK HXO Hsp1r. clear. intros. repeat split; lia.
  - split; [|split; [exact I|]].
    + cbn [ne_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      fold E. rewrite Usp, U33, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      revert Hslo Hshi H47 Hceil C1a Hwlo Hwhi HSTK HXO Hal16 Hsp1r Hsp1al32.
      clear. unfold SHADOW_OFF. intros. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
    + cbn [ne_facts0 f_alias alias_ok]. split; [|exact I]. fold E.
      rewrite (denot_and_m32 E 2 (spZ regs) (-160)); [| rewrite E2; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned
        | lia | lia | unfold spZ; apply getr_rng].
      cbn [sv_denot]. rewrite E33, Z.add_0_r, unsigned_lit_small by lia. fold sp1.
      replace (spZ regs + -160) with (spZ regs - 160) by lia. reflexivity.
Qed.


Lemma ne_svE : forall regs extra (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r ->
  sv_denot (Eimg (Ereg regs extra)) (SOff n 0) = getr regs r.
Proof.
  intros regs extra n r H. cbn [sv_denot]. rewrite (ew_Eimg_Ereg_nat regs extra n r H), Z.add_0_r.
  apply Z_to_bv_bv_unsigned.
Qed.

(* THE ENTRY: +0x00 .. frame_alloc_1 .. the join JE at +0x7c *)
Lemma ne_entry : forall POST, ne_from SK B POST NE_JE (ne_JEi SK B) -> forall cx, ne_base SK B cx ->
  SRr SEGS (n_W cx) (mkCfg (mkst (n_regs cx) (Z_to_bv 64 (BASE + AF_nl_error)) (n_memc cx) (seg_rom SEGS)) (n_mdc cx))
    (POST cx).
Proof.
  intros POST HN cx HB.
  pose proof (ne_base_facts SK B cx HB) as (Hw0 & Hw47 & Hwapp & Hal16 & Hceil & Hsp47 & Hwin0 & Hwin1 & Hap &
    Hn0 & Hcut' & Hcut64 & Hs1r & Hs1a).
  pose proof HB as (HPRE & HNLW & HWF & _ & _ & HAM & HRA & HHV).
  pose proof HPRE as (HJ & HGok & _ & Hraw & Hra4 & Hgp & Htp & _ & Hwlo & Hwhi & _ & Hside & Hajw & Hnro).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK, NW_SIZE in Hceil, Hwin0, Hap, Hw47, Hwapp.
  pose proof HJ as HJ0.
  pose proof (ajournal_gx_AR pa_segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  pose proof (aj_gx_present SK pa_segs B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HJpres.
  pose proof (ne_entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (n_regs cx) HJ Hal16 Hwlo Hwhi) as HS.
  set (E := Eimg (Ereg (n_regs cx) (ne_extra0 (32 * ((spZ (n_regs cx) - 160) / 32))))) in HS.
  assert (HEI : img_env pa_val A_LIM E) by (unfold E; apply Eimg_env).
  assert (EL : forall nn, (nn < A_TEXT)%nat -> ew E nn = ew (Ereg (n_regs cx) (ne_extra0 (ne_sp1 cx))) nn)
    by (intros nn Hn; unfold E; apply Eimg_low; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (n_regs cx) _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (ne_sp1 cx))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (n_regs cx) _ 1)).
  assert (Usp : bv_unsigned (ew E 2) = ne_sp cx)
    by (unfold E; rewrite (ew_Eimg_Ereg_nat (n_regs cx) _ 2 2%bv eq_refl); reflexivity).
  assert (U33 : bv_unsigned (ew E 33) = ne_sp1 cx) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (SHOK : sh_ok pa_segs ne_Bx (@nil shent) E (mrestrict (w_H (n_W cx)) (n_memc cx))) by (apply Forall_nil).
  pose (RUN := paj_run_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
  (* ---- +0x00 .. +0x78: the prologue, the cut, the .got words, the switch test, up to frame_alloc_1 ---- *)
  paj_run_tok RUN HS HJ SHOK ne_span.
  { unfold ne_ss0. cbn [ss_mem].
    repeat (apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val got_regionP
        bcell_regionP uar_got_regionP uar_cell_regionP] in Hx;
      first [lia | rewrite ?Usp, ?U33 in Hx; left; split; [left; lia | lia]] |]).
    apply awr_ok_x_nil. }
  pmkst HS.
  lazymatch type of HJ with ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ => set (mdT := mdx) in * end.
  assert (FDT : m_fds mdT = m_fds (n_mdc cx) /\ m_fs mdT = m_fs (n_mdc cx))
    by (unfold mdT; repeat rewrite (proj1 (wvb_fds_fs _ _ _)); repeat rewrite (proj2 (wvb_fds_fs _ _ _)); split; reflexivity).
  (* the registers at frame_alloc_1's entry *)
  assert (RA : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (AF_nl_error + NE_JE))).
  { ne_reg HS (1%bv : bv 5). cbn [sv_denot]. rewrite (img_env_codeptr _ HEI). reflexivity. }
  assert (R2 : getr (ms_regs ms) 2 = w64 (ne_sp1 cx)) by (ne_reg HS (2%bv : bv 5); apply sv_off0; exact E33).
  assert (R3 : getr (ms_regs ms) 3 = getr (n_regs cx) 3) by (ne_reg HS (3%bv : bv 5); exact (ne_svE _ _ 3 3%bv eq_refl)).
  assert (R4 : getr (ms_regs ms) 4 = getr (n_regs cx) 4) by (ne_reg HS (4%bv : bv 5); exact (ne_svE _ _ 4 4%bv eq_refl)).
  assert (R8 : getr (ms_regs ms) 8 = w64 (ne_sp cx)).
  { ne_reg HS (8%bv : bv 5). unfold E. rewrite (ne_svE _ _ 2 2%bv eq_refl). unfold w64, ne_sp, spZ. symmetry.
    apply Z_to_bv_bv_unsigned. }
  assert (R9 : getr (ms_regs ms) 9 = w64 (ne_sp1 cx)) by (ne_reg HS (9%bv : bv 5); apply sv_off0; exact E33).
  assert (R18 : getr (ms_regs ms) 18 = w64 (ne_w cx)).
  { ne_reg HS (18%bv : bv 5). unfold E. rewrite (ne_svE _ _ 10 10%bv eq_refl). unfold w64, ne_w, aarg, argZ. symmetry.
    apply Z_to_bv_bv_unsigned. }
  assert (R19 : getr (ms_regs ms) 19 = w64 4096) by (ne_reg HS (19%bv : bv 5); reflexivity).
  assert (R22 : getr (ms_regs ms) 22 = getr (n_regs cx) 22) by (ne_reg HS (22%bv : bv 5); exact (ne_svE _ _ 22 22%bv eq_refl)).
  assert (R23 : getr (ms_regs ms) 23 = getr (n_regs cx) 11) by (ne_reg HS (23%bv : bv 5); exact (ne_svE _ _ 11 11%bv eq_refl)).
  assert (R26 : getr (ms_regs ms) 26 = w64 SHADOW_OFF) by (ne_reg HS (26%bv : bv 5); apply sv_off0; exact E32).
  assert (SP : spZ (ms_regs ms) = ne_sp1 cx) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
  (* the saves and the cut's slot at the call *)
  assert (SV : Forall (fun ok : Z * bv 5 => val_mem SEGS (rdW (n_W cx) (ms_mem ms)) (ne_sp cx + fst ok) 8
                 (bv_unsigned (getr (n_regs cx) (snd ok)))) ne_saves).
  { let T := type of HS in let T' := eval unfold st_ok_pi in T in
    lazymatch T' with st_ok _ ?E' ?s1 (restrict _ ?ms1) =>
    unfold ne_saves; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    lazymatch goal with |- val_mem _ _ (_ + ?o) _ (bv_unsigned (getr _ ?r)) =>
      let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
      exact (ne_chunk_of_val (w_H (n_W cx)) E' s1 ms1 2 o 8%N (SOff n 0) (ne_sp cx)
        (bv_unsigned (getr (n_regs cx) r)) HS ltac:(vm_compute; reflexivity) Usp
        ltac:(unfold E; rewrite (ne_svE _ _ n r eq_refl); symmetry; apply Z_to_bv_bv_unsigned)
        ltac:(change (2 ^ (8 * Z.of_N 8)) with (bv_modulus 64); apply bv_unsigned_in_range)
        ltac:(cbn; lia))
    end end. }
  assert (SC : val_mem SEGS (rdW (n_W cx) (ms_mem ms)) (ne_sp1 cx + 24) 8 (ne_cut cx)).
  { let T := type of HS in let T' := eval unfold st_ok_pi in T in
    lazymatch T' with st_ok _ ?E' ?s1 (restrict _ ?ms1) =>
      exact (ne_chunk_of_val (w_H (n_W cx)) E' s1 ms1 33 24 8%N (SOff 12 0) (ne_sp1 cx) (ne_cut cx) HS
        ltac:(vm_compute; reflexivity) U33
        ltac:(unfold E; rewrite (ne_svE _ _ 12 12%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned)
        ltac:(change (2 ^ (8 * Z.of_N 8)) with (bv_modulus 64); apply bv_unsigned_in_range)
        ltac:(cbn; lia))
    end. }
  (* what the run kept: everything outside [sp - 176, sp) *)
  pose proof (kept_of_frame (segs := pa_segs) E (ss_mem ne_ss0) (w_H (n_W cx)) (n_memc cx) (ms_mem ms)
    (fun a => ne_sp cx - 176 <= a < ne_sp cx) HFr
    ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
          repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                  rewrite ?Usp, ?U33 in HrrW; cbv beta; lia|]); destruct HinW)) as UN1.
  clear HS SHOK HFr.
  (* ---- +0x78: frame_alloc_1(0x60), the class-1 side frame pos on top of own ---- *)
  eapply (SRr_bind SEGS).
  { eapply (aj_gx_stack_malloc_at SK pa_segs B LAWS pa_segs_low errno_low 1 ASM1 ltac:(lia)
      (pa_sigma LS___asan_stack_malloc_1) (n_G cx) (n_XO cx) (n_OUT cx) (n_W cx) (ms_regs ms) (ms_mem ms)
      (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx) (n_own cx) (n_lyc cx)
      (n_Sc cx) _ (n_k cx) (getr (ms_regs ms) 1) ne_hsm1 HJ).
    - rewrite SP. rewrite Zmod_divides in Hs1a by lia. destruct Hs1a as [q Hq]. rewrite Hq.
      apply Zmod_divides; [lia|]. exists (2 * q). lia.
    - rewrite SP. unfold ESTACK. lia.
    - rewrite SP. lia.
    - rewrite R3. exact Hgp.
    - rewrite R4. exact Htp.
    - reflexivity.
    - rewrite RA. apply ret_ok_codeptr_v; [cbv [AF_nl_error NE_JE]; lia | reflexivity].
    - exact (aside_room_take (n_Sc cx) [(1, 1)] 1 1 Hside ltac:(left; reflexivity) ltac:(lia)). }
  cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2
    & Hbb2 & HfS & HF4096 & HFceil & Hz & Hflag & HKc & Hsbm & Hraw2).
  rewrite SP in HKc, Hraw2. unfold ESTACK in HKc, Hraw2.
  rewrite RA.
  change (frame_addr (n_lyc cx) 1 pos) with (ne_F cx pos) in *.
  change (fs_frame_bytes 1) with 128 in *.
  pose proof (ajournal_gx_AR pa_segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  assert (Hfin2 : In (1, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  pose proof HAR2 as (M2 & _).
  destruct (frame_facts B (n_lyc cx) S2 _ 1 pos M2 Hfin2) as (Cc & Cp & _).
  pose proof (frame_al64 pa_segs B (n_lyc cx) S2 (n_W cx) mem2 md2 1 pos HAR2 Hfin2) as (HF64 & _ & _).
  destruct (frames_bounds pa_segs B LAWS (n_lyc cx) S2 (n_W cx) mem2 md2 1 pos HAR2 Hfin2) as (_ & _ & HFapp).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR2 Hfin2) as (_ & _ & HFpres & HFSpres).
  destruct (al_flag _ _ LAWS _ _ _ _ _ 1 pos HAR2 Hfin2) as (_ & _ & HFLapp & HFLceil).
  change (frame_addr (n_lyc cx) 1 pos) with (ne_F cx pos) in *.
  change (flag_addr (n_lyc cx) 1 pos) with (ne_FL cx pos) in *.
  change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  destruct (same_but_materialized_fs _ _ Hsbm) as [Hfds2 Hfs2].
  (* the kept chain: memc -> the call (the run) -> mem2 (frame_alloc_1) *)
  set (slo := ne_sp cx - 4272).
  assert (Hslo_c : alloc_ceiling <= slo) by (unfold slo; lia).
  assert (K0 : akept pa_segs B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_W cx) (n_memc cx) slo (ne_sp cx)
                 (fun _ => False)).
  { apply (akept_refl SK pa_segs B LAWS pa_segs_low). intros a Ha. apply HJpres. unfold slo in Ha. lia. }
  assert (K1 : akept pa_segs B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_W cx) (ms_mem ms) slo (ne_sp cx)
                 (fun _ => False)).
  { eapply (akept_step SK pa_segs B LAWS pa_segs_low (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx)
      (n_W cx) (n_memc cx) (n_W cx) (ms_mem ms) slo (ne_sp cx) (fun _ => False) (fun _ => False)
      (fun a => ne_sp cx - 176 <= a < ne_sp cx) HAR Hslo_c ltac:(lia) K0 UN1).
    - intros a _ Hp. eapply apresent_grows; [exact HG | exact Hp].
    - intros a H; exact H.
    - intros a Ha. right. unfold slo. cbv beta in Ha. lia. }
  assert (K2 : akept pa_segs B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_W cx) mem2 slo (ne_sp cx)
                 (fun _ => False)).
  { eapply (akept_trans SK pa_segs B LAWS pa_segs_low (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_Sc cx) (n_W cx)
      (ms_mem ms) (n_W cx) mem2 slo (ne_sp cx) (ne_sp1 cx - 4096) (ne_sp1 cx) (fun _ => False) (fun _ => False)
      (fun _ => False) Hslo_c ltac:(lia) K1
      (akept_of_acall_kept SK pa_segs B LAWS pa_segs_low (n_lyc cx) (n_Sc cx) (n_W cx) (ms_mem ms) (n_W cx) mem2
         (ne_sp1 cx - 4096) (ne_sp1 cx) (fun _ => False) (fun _ => False) HKc (fun a H => H))).
    - unfold slo; lia.
    - lia.
    - intros bb mm H; exact H.
    - intros f H; exact H.
    - intros a H; exact H.
    - intros a H; exact H. }
  (* w's bytes are kept: the run never writes them, nor frame_alloc_1 (ajw_kept_call) *)
  assert (HWin : forall a, ne_w cx <= a < ne_w cx + NW_SIZE -> inFP (ne_Wr cx) a).
  { intros a Ha. exists (ne_w cx, ne_w cx + NW_SIZE). split; [left; reflexivity | cbn [fst snd]; lia]. }
  assert (VW : forall a, ne_w cx <= a < ne_w cx + NW_SIZE ->
            aview SEGS (w_H (n_W cx)) mem2 a = aview SEGS (w_H (n_W cx)) (n_memc cx) a).
  { intros a Ha. unfold NW_SIZE in Ha.
    rewrite (ajw_kept_call SK pa_segs B LAWS pa_segs_low (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx)
      (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx) (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx)
      (ms_mem ms) mdT (n_k cx) S2 (n_W cx) mem2 md2 (ne_sp1 cx - 4096) (ne_sp1 cx) a HGok HJ HAR2 ltac:(lia) HKc
      Hraw2 (Hajw a (HWin a ltac:(unfold NW_SIZE; lia))) ltac:(lia)).
    apply UN1; [lia | cbv beta; lia]. }
  (* F is apart from w *)
  assert (Happw : forall a, ne_w cx <= a < ne_w cx + NW_SIZE -> a < kLowMemEnd \/ kHighMemBeg <= a).
  { intros a Ha. unfold NW_SIZE, SHADOW_OFF in *. rewrite C5. lia. }
  assert (HwF : ne_w cx + NW_SIZE <= ne_F cx pos \/ ne_F cx pos + 128 <= ne_w cx).
  { destruct (Z_le_gt_dec (ne_w cx + NW_SIZE) (ne_F cx pos)) as [H1|H1]; [left; exact H1|].
    destruct (Z_le_gt_dec (ne_F cx pos + 128) (ne_w cx)) as [H2|H2]; [right; exact H2|].
    exfalso.
    assert (NS : forall a, ne_w cx <= a < ne_w cx + NW_SIZE -> ne_F cx pos <= a < ne_F cx pos + 128 -> False).
    { intros a Ha HaF.
      apply (ajw_not_side SK pa_segs B LAWS ne_segs_img (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx)
        (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx) (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx)
        (n_memc cx) (n_mdc cx) (n_k cx) 1 pos a HGok HJ0 Cc Cp Hnin (Hajw a (HWin a Ha)) (Happw a Ha)).
      left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128.
      change (frame_addr (n_lyc cx) 1 pos) with (ne_F cx pos). exact HaF. }
    destruct (Z_le_gt_dec (ne_w cx) (ne_F cx pos)) as [H3|H3].
    + apply (NS (ne_F cx pos)); unfold NW_SIZE in *; lia.
    + apply (NS (ne_w cx)); unfold NW_SIZE in *; lia. }
  apply (HN cx pos S2 mem2 regs2 mem2 md2 HB).
  - (* the frame's context *)
    unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp, HFLapp.
    split; [exact Hnin|]. split; [exact Hfrs2|]. split; [exact HfS|].
    split; [exact HF4096|]. split; [exact HF64|]. split; [exact HFceil|].
    split; [unfold kLowShadowBeg, kHighMemBeg; lia|]. split; [lia|]. split; [exact HwF|].
    unfold ne_sp. fold slo. exact K2.
  - (* the join JE *)
    split.
    + split; [exact HJ2|]. split; [rewrite Hfds2; exact (proj1 FDT)|]. split; [rewrite Hfs2; exact (proj2 FDT)|].
      assert (PR : forall r, In r ne_saved_regs -> getr regs2 r = getr (ms_regs ms) r)
        by (intros r Hr; exact (ne_preserved_r _ _ HP2 r Hr)).
      split; [rewrite PR by (cbn; tauto); exact R2|].
      split; [rewrite PR by (cbn; tauto); exact R3|].
      split; [rewrite PR by (cbn; tauto); exact R4|].
      split; [rewrite PR by (cbn; tauto); exact R8|].
      split; [rewrite PR by (cbn; tauto); exact R9|].
      split; [rewrite PR by (cbn; tauto); exact R26|].
      split.
      { apply Forall_forall. intros [o r] Hin. pose proof (proj1 (Forall_forall _ _) SV (o, r) Hin) as V.
        assert (Ho : -104 <= o <= -8)
          by (unfold ne_saves in Hin; cbn in Hin; repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia|]); destruct Hin).
        cbn [fst snd] in V |- *. apply (ne_val_kept _ (ms_mem ms) mem2 _ 8 _); [|exact V].
        intros kk Hkk. destruct HKc as (KC1 & _). apply KC1; lia. }
      split.
      { apply (ne_val_kept _ (ms_mem ms) mem2 _ 8 _); [|exact SC].
        intros kk Hkk. destruct HKc as (KC1 & _). apply KC1; lia. }
      split.
      { pose proof (nlw_fields_of_anlw SEGS (rdW (n_W cx) (n_memc cx)) (ne_w cx) (n_bs cx) HNLW HWF) as NF.
        apply (nlw_fields_agree SEGS _ _ _ _ _ NF). intros i Hi.
        assert (Hv : aview SEGS (w_H (n_W cx)) mem2 (ne_w cx + i) = aview SEGS (w_H (n_W cx)) (n_memc cx) (ne_w cx + i))
          by (apply VW; lia).
        assert (Hmb : mbyte SEGS (rdW (n_W cx) mem2) (ne_w cx + i) = mbyte SEGS (rdW (n_W cx) (n_memc cx)) (ne_w cx + i))
          by (apply (mbyte_of_aview SEGS); exact Hv).
        split; [exact Hmb|]. intros Hw1.
        apply (ne_writable_keep SEGS (w_H (n_W cx)) (n_memc cx) mem2 (ne_w cx + i)); [unfold NW_SIZE in *; lia | exact Hw1 | |].
        - intros Hm. rewrite Hmb. exact Hm.
        - intros Hro. apply (Hnro (ne_w cx + i) (HWin (ne_w cx + i) ltac:(unfold NW_SIZE in *; lia))). left. exact Hro. }
      split; [lia|].
      assert (TR : range_addressable (aview SEGS (w_H (n_W cx)) mem2) SHADOW_OFF (ne_w cx) NW_SIZE /\
                   shadow_hull_vis (aview SEGS (w_H (n_W cx)) mem2) (ne_w cx) NW_SIZE).
      { rewrite <- (aview_rd_of SEGS) in HRA, HHV.
        apply (shadow_transport pa_segs B LAWS TB ne_segs_img (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx)
          (n_lyc cx) S2 (n_W cx) mem2 md2 slo (ne_sp cx) (fun _ => False) (ne_w cx) NW_SIZE HAR HAR2 eq_refl eq_refl);
          [ intros bb mm Hbm; rewrite Eab; exact Hbm | exact K2 | intros c q s _ _ [] | unfold NW_SIZE; lia | | exact HRA | exact HHV ].
        intros x Hx. exact (sclass_of_ajw SK pa_segs B LAWS (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx)
          (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx) (n_own cx) (n_lyc cx) (n_Sc cx)
          (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx) x HGok HJ0 (Hajw x (HWin x Hx)) (Happw x Hx)). }
      split; [exact (proj1 TR)|]. split; [exact (proj2 TR)|].
      split; [replace (ne_F cx pos + 120) with (ne_F cx pos + 128 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)|].
      split; [intros i Hi; exact (proj1 (HFpres (ne_F cx pos + i) ltac:(lia)))|].
      split; [reflexivity|].
      split.
      { intros i Hi. unfold ne_shZ. rewrite nth_repeat.
        pose proof (Hz (Z.of_nat i) ltac:(lia)) as Hzi. unfold shadow_of_addr in Hzi. exact Hzi. }
      split; [intros i Hi; exact (proj1 (HFSpres i Hi))|].
      split; [intros a _ _; reflexivity|].
      intros a Ha; exact Ha.
    + unfold ne_rvE. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      * exact Ha0.
      * rewrite (ne_preserved_r _ _ HP2) by (cbn; tauto). exact R18.
      * rewrite (ne_preserved_r _ _ HP2) by (cbn; tauto). exact R19.
      * rewrite (ne_preserved_r _ _ HP2) by (cbn; tauto). exact R23.
      * rewrite (ne_preserved_r _ _ HP2) by (cbn; tauto). exact R22.
Qed.

(* THE CONTRACT *)
Theorem nl_error_aproof : nl_error_acontract SK pa_segs PCAP_RLO PCAP_RHI B.
Proof.
  unfold nl_error_acontract, aleaf.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HPRE
    (bs & HNLW & HWF & HAP & HCUT & HAM & HRA & HHV).
  set (cx := mkNECX G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bs).
  assert (HB : ne_base SK B cx) by (exact (conj HPRE (conj HNLW (conj HWF (conj HAP (conj HCUT (conj HAM (conj HRA HHV)))))))).
  change (SRr pa_segs W (cfg_at pa_segs NL_ERROR_A regs memc mdc) (ne_post SK B cx)).
  assert (HCFG : cfg_at pa_segs NL_ERROR_A regs memc mdc
               = mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_nl_error)) memc (seg_rom pa_segs)) mdc).
  { unfold cfg_at. rewrite (lv_text LV). reflexivity. }
  rewrite HCFG. clear HCFG.
  (* the phase chain, from the exit back to the entry *)
  assert (P8 : ne_from SK B (ne_post SK B) NE_J8 (ne_J6i SK B)) by (eapply ne_ph_J8; eassumption).
  assert (P8c : ne_from SK B (ne_post SK B) NE_J8c (ne_J8ci SK B)) by (eapply ne_ph_J8c; eassumption).
  assert (P7 : ne_from SK B (ne_post SK B) NE_J7 (ne_J6i SK B)) by (eapply ne_ph_J7; eassumption).
  assert (P6 : ne_from SK B (ne_post SK B) NE_J6 (ne_J6i SK B)) by (eapply ne_ph_J6; eassumption).
  assert (P6c : ne_from SK B (ne_post SK B) NE_J6c (ne_J6ci SK B)) by (eapply ne_ph_J6c; eassumption).
  assert (P5b : ne_from SK B (ne_post SK B) NE_J5b (ne_J5bi SK B)) by (eapply ne_ph_J5b; eassumption).
  assert (P5c : ne_from SK B (ne_post SK B) NE_J5c (ne_J5ci SK B)) by (eapply ne_ph_J5c; eassumption).
  assert (P5 : ne_from SK B (ne_post SK B) NE_J5 (ne_J5i SK B)) by (eapply ne_ph_J5; eassumption).
  assert (P4 : ne_from SK B (ne_post SK B) NE_J4 (ne_JA SK B)) by (eapply ne_ph_J4; eassumption).
  assert (P3 : ne_from SK B (ne_post SK B) NE_J3 (ne_JA SK B)) by (eapply ne_ph_J3; eassumption).
  assert (P2 : ne_from SK B (ne_post SK B) NE_J2 (ne_JA SK B)) by (eapply ne_ph_J2; eassumption).
  assert (P1 : ne_from SK B (ne_post SK B) NE_J1 (ne_JA SK B)) by (eapply ne_ph_J1; eassumption).
  assert (P0 : ne_from SK B (ne_post SK B) NE_J0 (ne_J0i SK B)) by (eapply ne_ph_J0; eassumption).
  assert (PE : ne_from SK B (ne_post SK B) NE_JE (ne_JEi SK B)) by (eapply ne_ph_JE; eassumption).
  exact (ne_entry (ne_post SK B) PE cx HB).
Qed.

End b.
End a.
