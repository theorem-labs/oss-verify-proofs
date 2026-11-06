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
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpen.v, with its module paths, module names and numbers changed; 501 of its 581 lines of code are new or changed and 1471 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_writeHead.v, with its module paths and module names changed; 968 of its 1102 lines of code are new or changed and 447 lines of the source are left out. *)
(* nl_talk (reac_link_alias.c:37-93) on image A (fuzz_link.asan 0x88974, listing
   (internal path) (internal record, sha256 628c2741aace)): the ENTRY phase of the walk,
   +0x00 (NT_entry) -> +0x1a0 (NT_sock). It proves `nt_start` (lib/A/Prog/nl_talk_defs.v) from
   `nt_from POST (nt_sock_inv B)`.

   WHAT THE CODE DOES HERE:
   - +0x00 .. +0x38  the 192-byte machine frame (`addi sp, sp, -0xc0`), the probe `sd zero, 0(sp)`, ra and
     s0..s11 saved at sp0 - 8 .. sp0 - 104;
   - +0x3c .. +0x44  s0 := sp0; `andi sp, sp, -0x20` (the realigned sp1 = nt_sp1 sp0, an atom of its own from
     here on); s1 := sp;
   - +0x48 .. +0x78  the two kind slots spilled (0x30(s1), 0x38(s1)), the side-stack switch (.got+0xb8 -> the
     cell) and the shadow base (.got+0x60 -> the cell, into s5); `beqz a2` +0x78 is decided by the switch
     cell's region (AR's const law: 1), so the real-stack arm +0x90..+0xbc is not entered;
   - +0x7c .. +0x84  frame_alloc_9(16672) (0x3e15c), through LinkWalkSide.v aj_gx_stack_malloc_sz_at;
   - +0x88 .. +0xc0  s4 := s2 := F; `bnez s4` +0x98 decided by F >= 4096 (the post's frames_bounds clause),
     so the second entry to the real-stack arm is not taken either; slot 0x50(s1) := F;
   - +0xc4 .. +0xf0  the frame's header (the live magic 0x41b58ab3 at F, the descriptor at F + 8, the pc at
     F + 16) and s8 := shadow(F);
   - +0xf4 .. +0x114 the four 0xf1 bytes of the left redzone at shadow(F), s3 := shadow(F) + 4, and the call
     meta_fill_f8(shadow(F) + 4, 2048) (0x55f94), through aj_gx_set_shadow_at;
   - +0x118 .. +0x19c the 32 0xf3 bytes of the right redzone at shadow(F) + 2052 .. + 2084.

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 AsStackSz SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkPi LinkWalkSide LinkWalkShadow LinkWalkCall LinkWalkWseg.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_talk_c nl_talk_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ==========================================================================
   0. Computed facts about image A's segments (reached at pa_segs through HSEGS)
   ========================================================================== *)

(* an interval that one segment of the image covers *)
Definition nte_cov_b (segs : list Segment) (lo hi : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs.

Lemma nte_in_img_of_cov : forall segs lo hi a,
  nte_cov_b segs lo hi = true -> lo <= a < hi -> YG0d.in_img segs a.
Proof.
  intros segs lo hi a H Ha. unfold nte_cov_b in H. apply existsb_exists in H as (s & Hin & Hb).
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hin | lia].
Qed.

Lemma nte_gnl_cov : nte_cov_b tfibsegs LA_G_NL (LA_G_NL + NK_SIZE) = true.
Proof. vm_compute. reflexivity. Qed.

(* no range of the runtime's statics meets [lo, hi) *)
Definition nte_miss_b (l : list (Z * Z)) (lo hi : Z) : bool :=
  forallb (fun r => (hi <=? fst r) || (fst r + snd r <=? lo)) l.

Lemma nte_miss_ok : forall l lo hi a,
  nte_miss_b l lo hi = true -> lo <= a < hi -> ~ Exists (in_zr a) l.
Proof.
  intros l lo hi a H Ha HE. unfold nte_miss_b in H. rewrite forallb_forall in H.
  apply Exists_exists in HE as (r & Hin & Hr). pose proof (H r Hin) as Hb.
  unfold in_zr in Hr. apply orb_true_iff in Hb as [Hb | Hb]; apply Z.leb_le in Hb; lia.
Qed.

(* the image test, as a boolean (so the walk needs no excluded middle) *)
Definition nte_inimg_b (segs : list Segment) (a : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs.

Lemma nte_inimg_true : forall segs a, nte_inimg_b segs a = true -> YG0d.in_img segs a.
Proof.
  intros segs a H. apply existsb_exists in H as (s & Hin & Hb).
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists s. split; [exact Hin | lia].
Qed.

Lemma nte_inimg_false : forall segs a, nte_inimg_b segs a = false -> ~ YG0d.in_img segs a.
Proof.
  intros segs a H (s & Hin & Hr).
  assert (Hex : nte_inimg_b segs a = true).
  { apply existsb_exists. exists s. split; [exact Hin|].
    apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite H in Hex. discriminate.
Qed.

Lemma nte_gnl_owned : nte_miss_b Tfib_owned_static LA_G_NL (LA_G_NL + NK_SIZE) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nte_errno_val : TFIB_ERRNO = 6495084.
Proof. vm_compute. reflexivity. Qed.

Lemma nte_gnl_errno : TFIB_ERRNO + 4 <= LA_G_NL \/ LA_G_NL + NK_SIZE <= TFIB_ERRNO.
Proof. right. rewrite nte_errno_val. unfold LA_G_NL, NK_SIZE. lia. Qed.

Lemma nte_gnl_wr_rng : 0xa1000 <= LA_G_NL /\ LA_G_NL + NK_SIZE <= 0x654000.
Proof. unfold LA_G_NL, NK_SIZE. lia. Qed.

(* ==========================================================================
   1. The symbolic entry state
   ========================================================================== *)

Definition nte_Bx : sv := SOff 32 0.
Definition nte_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition nte_saves : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [].
Definition nte_probe : YP09.region := YP09.mkRegion (Some 2%nat) (-192) (-184) (-192) (-184) [].
Definition nte_spill : YP09.region := YP09.mkRegion (Some 60%nat) 0 88 0 88 [].
Definition nte_hd : YP09.region := YP09.mkRegion (Some 68%nat) 0 24 0 24 [].
Definition nte_sha : YP09.region := YP09.mkRegion (Some 90%nat) 0 4 0 4 [].
Definition nte_shc : YP09.region := YP09.mkRegion (Some 90%nat) 2052 2084 2052 2084 [].

Definition nte_regions : smem :=
  [nte_saves; nte_probe; got_regionP; bcell_regionP 32; uar_got_regionP (A_OBJ 65); uar_cell_regionP (A_OBJ 65)].
Definition nte_facts0 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition nte_ss0 : sstate := mkSS NT_entry sr_atoms nte_regions None nte_facts0.

(* the relro window and g_nl, against the image's segments *)
Lemma nte_relro_cov : nte_cov_b tfibsegs PCAP_RLO PCAP_RHI = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nte_gnl_ro_free : ro_free_b tfibsegs PCAP_RLO PCAP_RHI LA_G_NL (LA_G_NL + NK_SIZE) = true.
Proof. vm_compute. reflexivity. Qed.

(* a one-byte literal chunk at offset `off` of a region's chunk list, as a boolean *)
Definition nte_hasb (cs : list YP09.chunk) (off z : Z) : bool :=
  existsb (fun c => match c with
                    | YP09.mkChunk o (CVal w (SLit z')) => (o =? off) && N.eqb w 1 && (z' =? z)
                    | _ => false
                    end) cs.

Lemma nte_hasb_in : forall cs off z, nte_hasb cs off z = true -> In (YP09.mkChunk off (CVal 1 (SLit z))) cs.
Proof.
  intros cs off z H. unfold nte_hasb in H. apply existsb_exists in H as (c & Hin & Hc).
  destruct c as [o v]. destruct v as [w e | | |]; try discriminate Hc.
  destruct e; try discriminate Hc.
  apply andb_true_iff in Hc as [Hc H3]. apply andb_true_iff in Hc as [H1 H2].
  apply Z.eqb_eq in H1. apply N.eqb_eq in H2. apply Z.eqb_eq in H3. subst. exact Hin.
Qed.

(* the bytes the walk's runs may store after frame_alloc_9: the window, the frame's header and the two redzone
   ranges of its shadow *)
Definition nte_Zf (sp F SH x : Z) : Prop :=
  (sp - 8448 <= x < sp) \/ (F <= x < F + 24) \/ (SH <= x < SH + 4) \/ (SH + 2052 <= x < SH + 2084).

(* the kept-window obligation of YC4b.v kept_of_frame for a run's regions *)
Ltac nte_win_tac :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi x Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [ injection Hq as <- <- <-; cbn [base_val] in Hrr;
      repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => rewrite H in Hrr end;
      cbv beta;
      first [ lia
            | unfold nte_Zf; first [ left; lia | right; left; lia | right; right; left; lia
                                   | right; right; right; lia ] ] |]);
  destruct Hin.

(* the region at index i of a state, its region_ok at the state's memory *)
Ltac nte_region HS i HR :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss ?ms =>
    let r := eval vm_compute in (nth_error (ss_mem ss) i) in
    lazymatch r with Some ?rr =>
      pose proof (st_ok_pi_region_nth E ss ms i rr HS ltac:(vm_compute; reflexivity)) as HR;
      cbn [ms_mem restrict] in HR end end.

Ltac nte_in := cbn [In]; repeat (first [left; reflexivity | right]).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TL : PALib B.
Hypothesis TB : PcapSyms B.                    (* instance AD2l.PcapB_syms *)
Hypothesis HSEGS : pa_segs = tfibsegs.         (* LinkImgInst.v pi_link_segs *)

(* the two runtime entries this phase calls *)
Hypothesis ASM9 : astack_malloc_sz_realizes pa_segs B (pa_sigma LS___asan_stack_malloc_9) NT_CID.
                                               (* lib/A/Rt/StackSideInst.v link_stack_malloc_9 *)
Hypothesis ASF8 : aset_shadow_realizes pa_segs B (pa_sigma LS___asan_set_shadow_f8) 0xf8.
                                               (* lib/A/Rt/SetShadow.v link_set_shadow_f8 *)

Let errno_low := pal_env B TL.

(* ==========================================================================
   2. Small transport lemmas
   ========================================================================== *)

Lemma nte_abytes_keep : forall (W1 W2 : world SEGS) m1 m2 a bs,
  abytes SEGS (rdW W1 m1) a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) ->
     aview SEGS (w_H W2) m2 (a + i) = aview SEGS (w_H W1) m1 (a + i)) ->
  abytes SEGS (rdW W2 m2) a bs.
Proof.
  intros W1 W2 m1 m2 a bs (H0 & H1 & H2) Hk. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H2 i Hi). apply (YCbq.mbyte_of_aview SEGS). apply Hk. lia.
Qed.

Lemma nte_wr_img : forall (m : word -> option byte) a,
  667648 <= a < 6635520 -> writable_at SEGS m a.
Proof. intros m a Ha. rewrite HSEGS. apply wseg_writable_tfib_rng. lia. Qed.

Lemma nte_in_img_gnl : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> YG0d.in_img SEGS a.
Proof. intros a Ha. rewrite HSEGS. exact (nte_in_img_of_cov tfibsegs _ _ a nte_gnl_cov Ha). Qed.

(* a buffer byte of the caller: writable at any later memory the walk reaches *)
Lemma nte_wr_keep : forall (H1 H2 : word -> bool) (m1 m2 : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a ->
  aview SEGS H2 m2 a = aview SEGS H1 m1 a ->
  writable_at SEGS (mrestrict H1 m1) a -> writable_at SEGS (mrestrict H2 m2) a.
Proof.
  intros H1 H2 m1 m2 a Ha Hro Hav Hw.
  destruct (nte_inimg_b SEGS a) eqn:Hib;
    [pose proof (nte_inimg_true SEGS a Hib) as Hi | pose proof (nte_inimg_false SEGS a Hib) as Hi].
  - rewrite HSEGS. apply wseg_writable_tfib. destruct Hi as (s & Hin & Hr).
    exists s. split; [rewrite <- HSEGS; exact Hin|].
    split; [|exact Hr].
    destruct (seg_writable s) eqn:Hsw; [reflexivity|].
    exfalso. apply Hro. left. exists s. split; [exact Hin | split; [exact Hsw | exact Hr]].
  - apply (YCbq.apresent_writable SEGS).
    apply (YCbq.apresent_transfer SEGS H1 H2 m1 m2 a Ha Hi Hav).
    destruct (H1 (Z_to_bv 64 a)) eqn:Hh.
    + exfalso. apply Hw. unfold wview, mrestrict. rewrite Hh.
      rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite Z.mod_small by lia. rewrite (YCbq.find_segment_none SEGS a Hi). reflexivity.
    + destruct (m1 (Z_to_bv 64 a)) as [b|] eqn:Hm.
      * split; [exact Hh | exists b; exact Hm].
      * exfalso. apply Hw. unfold wview, mrestrict. rewrite Hh, Hm.
        rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
        rewrite Z.mod_small by lia. rewrite (YCbq.find_segment_none SEGS a Hi). reflexivity.
Qed.

(* the 64-byte alignment and the bounds of a frame of the state *)
Lemma nte_frame_bounds : forall ly S W mem md fp,
  AR SEGS B ly S W mem md -> In (NT_CID, fp) (frames S) ->
  0 <= NT_CID <= 10 /\ 0 <= fp < fs_frames NT_CID /\
  frame_addr ly NT_CID fp mod 64 = 0 /\
  4096 <= frame_addr ly NT_CID fp /\ frame_addr ly NT_CID fp + 32768 <= alloc_ceiling /\
  in_app (frame_addr ly NT_CID fp) 32768.
Proof.
  intros ly S W mem md fp HAR Hin.
  pose proof HAR as [M _].
  destruct (frame_facts B ly S _ NT_CID fp M Hin) as (Hc & Hp & _).
  destruct (frame_al64 SEGS B ly S W mem md NT_CID fp HAR Hin) as (H64 & _ & _).
  destruct (frames_bounds SEGS B LAWS ly S W mem md NT_CID fp HAR Hin) as (H1 & H2 & H3).
  change (fs_frame_bytes NT_CID) with 32768 in H2, H3.
  split; [exact Hc|]. split; [exact Hp|]. split; [exact H64|].
  split; [lia|]. split; [lia|]. exact H3.
Qed.

(* ==========================================================================
   2b. Reading the end state, and what the steps keep
   ========================================================================== *)

Lemma nte_u64 : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. exact (bv_unsigned_in_range 64 w). Qed.

Lemma nte_sv_off : forall E n d v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n d) = Z_to_bv 64 (v + d).
Proof. intros E n d v H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hv. reflexivity. Qed.

Lemma nte_wvb_fds : forall l X m, m_fds (with_vm_backing l X m) = m_fds m.
Proof. intros l X m. exact (proj1 (wvb_fds_fs l X m)). Qed.

Lemma nte_wvb_fs : forall l X m, m_fs (with_vm_backing l X m) = m_fs m.
Proof. intros l X m. exact (proj2 (wvb_fds_fs l X m)). Qed.

Lemma nte_sbm_fds : forall md md', same_but_materialized md md' -> m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof. intros md md' H. unfold same_but_materialized in H. rewrite H. exact (wvb_fds_fs _ _ _). Qed.

(* a word of a region's 8-byte chunk *)
Lemma nte_rd_at : forall E (H : word -> bool) (mm : word -> option byte) n b cs lo hi wlo whi off e v a,
  region_ok SEGS E (mrestrict H mm) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> a = b + off ->
  rdword (aview SEGS H mm) a = Some v.
Proof.
  intros E H mm n b cs lo hi wlo whi off e v a HR Hb Hin He Hv ->.
  apply (rdword_of_val_mem SEGS H mm (b + off) v); [|exact Hv].
  apply (field_of_region (segs := SEGS) E (mrestrict H mm) n b cs lo hi wlo whi off 8 e v HR Hb Hin He).
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
  - change (Z.of_N 8) with 8. lia.
Qed.

(* a saved register's word in the saves region (base atom 2) *)
Ltac nte_save HR U off e SVR :=
  eapply (nte_rd_at _ _ _ 2 _ _ _ _ _ _ off e _ _ HR U);
  [ nte_in | apply SVR; [lia | vm_compute; reflexivity] | apply nte_u64 | lia ].

(* the bytes of a run of one-byte literal chunks of a region *)
Lemma nte_bytes_at : forall E (H : word -> bool) (mm : word -> option byte) n b cs lo hi wlo whi off0 len z v,
  region_ok SEGS E (mrestrict H mm) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b ->
  forallb (fun k => nte_hasb cs (off0 + Z.of_nat k) z) (seq 0 len) = true ->
  0 <= z < 2 ^ 64 -> z mod 256 = v ->
  forall i, 0 <= i < Z.of_nat len -> aview SEGS H mm (b + off0 + i) = Some v.
Proof.
  intros E H mm n b cs lo hi wlo whi off0 len z v HR Hb Hall Hz Hv i Hi.
  rewrite forallb_forall in Hall.
  assert (Hk : In (Z.to_nat i) (seq 0 len)) by (apply in_seq; lia).
  pose proof (nte_hasb_in cs _ z (Hall _ Hk)) as Hin.
  rewrite Z2Nat.id in Hin by lia.
  rewrite <- Hv, <- Z.add_assoc.
  apply aview_of_val_mem1; [|apply Z.mod_pos_bound; lia].
  pose proof (field_of_region_any (segs := SEGS) E (mrestrict H mm) n b cs lo hi wlo whi (off0 + i) 1 (SLit z)
    HR Hb Hin ltac:(cbn; lia)) as Hval.
  cbn [sv_denot] in Hval. rewrite unsigned_lit_small in Hval by lia.
  change (N.to_nat 1) with 1%nat in Hval. change (2 ^ (8 * Z.of_N 1)) with 256 in Hval. exact Hval.
Qed.

(* a word whose eight bytes a step keeps *)
Lemma nte_rdword_kept : forall (H : word -> bool) (m m' : word -> option byte) a v,
  (forall i, 0 <= i < 8 -> aview SEGS H m' (a + i) = aview SEGS H m (a + i)) ->
  rdword (aview SEGS H m) a = Some v -> rdword (aview SEGS H m') a = Some v.
Proof.
  intros H m m' a v Hk Hr. unfold rdword in *.
  pose proof (Hk 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
  rewrite K0, (Hk 1 ltac:(lia)), (Hk 2 ltac:(lia)), (Hk 3 ltac:(lia)), (Hk 4 ltac:(lia)), (Hk 5 ltac:(lia)),
    (Hk 6 ltac:(lia)), (Hk 7 ltac:(lia)).
  exact Hr.
Qed.

(* n present bytes are a buffer *)
Lemma nte_abuf_present : forall (H : word -> bool) (m : word -> option byte) a n,
  (forall i, 0 <= i < n -> apresent H m (a + i)) -> 0 <= a -> a + n <= 2 ^ 64 -> 0 <= n ->
  abuf SEGS (mrestrict H m) a n.
Proof.
  intros H m a n Hp Ha Han Hn.
  exists (abytes_of SEGS (mrestrict H m) a (Z.to_nat n)). rewrite abytes_of_length.
  split; [lia|]. split.
  - apply abytes_of_abytes; [exact Ha | lia |].
    intros i Hi. destruct (Hp (Z.of_nat i) ltac:(lia)) as (Hh & bb & Hbb).
    exists bb. unfold mbyte, mrestrict. cbv beta. rewrite Hh, Hbb. reflexivity.
  - intros i Hi. rewrite abytes_of_length in Hi. apply (apresent_writable SEGS). apply Hp. lia.
Qed.

(* the kept clause of the whole phase, from its three legs: the runs before frame_alloc_9 (they write only the
   window), the call (YCbq.v acall_kept), and the steps after it (they write the window and X) *)
Lemma nte_akept_build : forall lyc Sc (W : world SEGS) memc mdc m0 m2 mf slo shi s1 (X E : Z -> Prop),
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  (forall a, slo <= a < shi -> apresent (w_H W) memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> aview SEGS (w_H W) m0 a = aview SEGS (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) m0 a) ->
  acall_kept SEGS B lyc Sc W m0 W m2 (s1 - ESTACK) s1 (fun _ => False) ->
  slo <= s1 - ESTACK -> s1 <= shi ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ X a -> aview SEGS (w_H W) mf a = aview SEGS (w_H W) m2 a) ->
  (forall a, apresent (w_H W) m2 a -> apresent (w_H W) mf a) ->
  (forall a, X a -> E a) ->
  akept SEGS B lyc Sc W memc W mf slo shi E.
Proof.
  intros lyc Sc W memc mdc m0 m2 mf slo shi s1 X E HAR Hslo Hshi Hwin UN0 P0 HC Hs1 Hs2 UNf Pf HXE.
  assert (A0 : akept SEGS B lyc Sc W memc W m0 slo shi (fun _ => False)).
  { apply (akept_step SK SEGS B LAWS pa_segs_low lyc Sc W memc mdc W memc W m0 slo shi
      (fun _ => False) (fun _ => False) (fun a => slo <= a < shi) HAR Hslo Hshi).
    - exact (akept_refl SK SEGS B LAWS pa_segs_low lyc Sc W memc slo shi (fun _ => False) Hwin).
    - intros a Ha Hn. exact (UN0 a Ha Hn).
    - intros a _ Hp. exact (P0 a Hp).
    - intros a Ha. exact Ha.
    - intros a Ha. right. exact Ha. }
  assert (A1 : akept SEGS B lyc Sc W memc W m2 slo shi (fun _ => False)).
  { apply (akept_trans SK SEGS B LAWS pa_segs_low lyc Sc W memc Sc W m0 W m2 slo shi (s1 - ESTACK) s1
      (fun _ => False) (fun _ => False) (fun _ => False) Hslo Hshi A0
      (akept_of_acall_kept SK SEGS B LAWS pa_segs_low lyc Sc W m0 W m2 (s1 - ESTACK) s1
         (fun _ => False) (fun _ => False) HC (fun a Ha => Ha)) Hs1 Hs2).
    - intros b m Hb. exact Hb.
    - intros f Hf. exact Hf.
    - intros a Ha. exact Ha.
    - intros a Ha. exact Ha. }
  apply (akept_step SK SEGS B LAWS pa_segs_low lyc Sc W memc mdc W m2 W mf slo shi
    (fun _ => False) E (fun a => (slo <= a < shi) \/ X a) HAR Hslo Hshi A1).
  - intros a Ha Hn. apply UNf; [exact Ha | intros H; apply Hn; left; exact H | intros H; apply Hn; right; exact H].
  - intros a _ Hp. exact (Pf a Hp).
  - intros a [].
  - intros a [H | H]; [right; exact H | left; exact (HXE a H)].
Qed.

(* a byte the caller's journal lets the call write (apre's ajw), in the application's memory, outside the
   call's window and outside errno, is a byte akept keeps and AR pins (link_amem.v akb) *)
Lemma nte_akb_of_ajw : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k slo shi a,
  gx_ok SEGS B G ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajw B G XO OUT STK sp0 FP ly S lyc Sc own a ->
  (a < kLowMemEnd \/ kHighMemBeg <= a) -> ~ (slo <= a < shi) -> ~ (as_errno B <= a < as_errno B + 4) ->
  akb SEGS B lyc Sc slo shi a.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k slo shi a HG HJ Hw Happ Hwin Herr.
  destruct (ajournal_gx_row SK SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ)
    as (Hrlo & Hrhi & Hr1 & Hr2).
  pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (HAR & _ & _ & _ & _ & Hfrs & _).
  destruct Hw as [(Haw & Hno) | [HGa | (_ & Hout)]].
  - destruct Haw as [Hs | [(_ & b & n & Hin & Hr) | [(b & n & Hin & _ & Hr) | (c & q & Hin & Hr)]]].
    + left. split; [lia | exact Hwin].
    + right; left. exists b, n. split; [exact Hin | exact Hr].
    + right; left. exists b, n. split; [exact Hin | exact Hr].
    + assert (Hcq : In (c, q) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
      destruct Hr as [Hr | Hr].
      * right; right; right. exists c, q. split; [exact Hcq | exact Hr].
      * exfalso. destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc c q HAR Hcq) as (Hf4096 & Hfceil & _).
        pose proof (fs_frame_bytes_nonneg c) as Hnn. pose proof asan_consts as ((C1a & C1b) & _).
        unfold in_zr, shadow_addr in Hr. cbn [fst snd] in Hr.
        unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg in *. lia.
  - right; right; left. destruct (HG a HGa) as (Hi & Hns). split; [exact Hi | split; [exact Hns | exact Herr]].
  - left. split; [lia | exact Hwin].
Qed.

Lemma nte_relro_img : forall a, PCAP_RLO <= a < PCAP_RHI -> YG0d.in_img SEGS a.
Proof. intros a Ha. rewrite HSEGS. exact (nte_in_img_of_cov tfibsegs _ _ a nte_relro_cov Ha). Qed.

Lemma nte_gnl_not_ro : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a.
Proof. intros a Ha. rewrite HSEGS. exact (not_ro_of_free tfibsegs PCAP_RLO PCAP_RHI _ _ a nte_gnl_ro_free Ha). Qed.

(* What the caller's memory looks like at NT_sock, from the phase's kept clause: the read-only bytes, g_nl, the
   request and the two buffers are the call's. *)
Lemma nte_mem_final : forall cx fpos S1 (W1 : world SEGS) mem1 md1 (mf : word -> option byte),
  nt_base SK B cx ->
  AR SEGS B (n_lyc cx) S1 W1 mem1 md1 -> frames S1 = (NT_CID, fpos) :: frames (n_Sc cx) ->
  ablocks B (n_lyc cx) S1 = ablocks B (n_lyc cx) (n_Sc cx) ->
  akept SEGS B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_W cx) mf (spZ (n_regs cx) - NL_TALK_AK)
    (spZ (n_regs cx)) (fun a => False \/ aside_rng (n_lyc cx) NT_CID fpos a) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H (n_W cx)) mf) /\
  anlk_at SEGS (rdW (n_W cx) mf) LA_G_NL (n_kbs cx) /\
  abytes SEGS (rdW (n_W cx) mf) (n_req cx) (n_reqb cx) /\
  nt_bufs_same cx (rdW (n_W cx) mf).
Proof.
  intros cx fpos S1 W1 mem1 md1 mf HB HAR1 Hfrs1 Eab1 HK.
  pose proof HB as (HPRE & HRD & HAPRE & HNLK & HREQ & HRLEN & _ & _).
  pose proof HPRE as (HJ & HGok & HROD & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & Hro).
  pose proof (akept_drop_side SK SEGS B LAWS pa_segs_low (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_W cx) mf
    (spZ (n_regs cx) - NL_TALK_AK) (spZ (n_regs cx)) (fun _ => False) S1 W1 mem1 md1 NT_CID fpos HAR1 Hfrs1 Eab1 HK)
    as HK0.
  assert (KEEP : forall a, akb SEGS B (n_lyc cx) (n_Sc cx) (spZ (n_regs cx) - NL_TALK_AK) (spZ (n_regs cx)) a ->
    aview SEGS (w_H (n_W cx)) mf a = aview SEGS (w_H (n_W cx)) (n_memc cx) a).
  { intros a Ha.
    exact (akept_akb_gx SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ HK0 Ha (fun H => H)). }
  split.
  { intros a Hro' Hns Her. rewrite (KEEP a); [exact (HROD a Hro' Hns Her)|].
    right; right; left. split; [|split; [exact Hns | exact Her]].
    destruct Hro' as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (nte_relro_img a Hr)]. }
  destruct HNLK as ((Hab & Haw) & Hlen).
  assert (KG : forall i, 0 <= i < Z.of_nat (length (n_kbs cx)) ->
    aview SEGS (w_H (n_W cx)) mf (LA_G_NL + i) = aview SEGS (w_H (n_W cx)) (n_memc cx) (LA_G_NL + i)).
  { intros i Hi. rewrite Hlen in Hi. apply KEEP. right; right; left.
    split; [apply nte_in_img_gnl; lia|]. split.
    - rewrite (ts_owned B TB). apply (nte_miss_ok _ LA_G_NL (LA_G_NL + NK_SIZE)); [exact nte_gnl_owned | lia].
    - rewrite (ts_errno B TB). pose proof nte_gnl_errno. lia. }
  split.
  { split; [|exact Hlen]. split.
    - exact (nte_abytes_keep (n_W cx) (n_W cx) (n_memc cx) mf LA_G_NL (n_kbs cx) Hab KG).
    - intros i Hi. pose proof nte_gnl_wr_rng as Hgr.
      apply (nte_wr_keep (w_H (n_W cx)) (w_H (n_W cx)) (n_memc cx) mf).
      + rewrite Hlen in Hi. lia.
      + apply nte_gnl_not_ro. rewrite Hlen in Hi. lia.
      + exact (KG i Hi).
      + exact (Haw i Hi). }
  split.
  { apply (nte_abytes_keep (n_W cx) (n_W cx) (n_memc cx) mf (n_req cx) (n_reqb cx) HREQ).
    intros i Hi. apply KEEP. apply HRD. unfold n_Rd, nl_talk_ard, rd_ivl. unfold n_req, n_len in *. lia. }
  destruct HAPRE as (kbs' & req' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbk & Hba
    & Hek & Hea & _ & Hkf & Haf & Hck & Hca).
  assert (KB : forall p cap, (p <> 0 -> apart (as_errno B) 4 p cap) ->
      (p <> 0 -> apart_frame (n_regs cx) NL_TALK_AK p cap /\ apart_gnl LA_G_NL p cap) ->
      (p <> 0 -> 1 <= cap -> achk SEGS (n_m cx) p cap) ->
      (forall a, p <> 0 -> p <= a < p + cap -> inFP (n_Wr cx) a) ->
      p <> 0 -> 1 <= cap -> forall a, p <= a < p + cap ->
      aview SEGS (w_H (n_W cx)) mf a = aview SEGS (w_H (n_W cx)) (n_memc cx) a /\
      ~ in_roP SEGS PCAP_RLO PCAP_RHI a).
  { intros p cap He Hf Hc Hw Hp Hcap a Ha.
    destruct (Hc Hp Hcap) as (Hmr & _ & _). destruct (Hf Hp) as (Hfr & _). pose proof (He Hp) as He'.
    pose proof (Hw a Hp Ha) as Hwa. split; [|exact (Hro a Hwa)].
    apply KEEP. apply (nte_akb_of_ajw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HGok HJ (Hajw a Hwa)).
    - unfold amem_range in Hmr. lia.
    - unfold apart_frame in Hfr. lia.
    - unfold apart in He'. lia. }
  assert (WK : forall a, n_kind cx <> 0 -> n_kind cx <= a < n_kind cx + n_kindn cx -> inFP (n_Wr cx) a).
  { intros a Hk Ha. exists (aivl (n_kind cx) (n_kindn cx)). split.
    - unfold n_Wr, nl_talk_awr. right; left. reflexivity.
    - unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) Hk). cbn [fst snd]. lia. }
  assert (WA : forall a, n_alias cx <> 0 -> n_alias cx <= a < n_alias cx + n_aliasn cx -> inFP (n_Wr cx) a).
  { intros a Hk Ha. exists (aivl (n_alias cx) (n_aliasn cx)). split.
    - unfold n_Wr, nl_talk_awr. right; right; left. reflexivity.
    - unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) Hk). cbn [fst snd]. lia. }
  pose proof (KB (n_kind cx) (n_kindn cx) Hek Hkf Hck WK) as KBK.
  pose proof (KB (n_alias cx) (n_aliasn cx) Hea Haf Hca WA) as KBA.
  unfold nt_bufs_same. split; [|split; [|split]].
  - intros Hk s Hs (Hsb & Hnz). split; [|exact Hnz].
    apply (nte_abytes_keep (n_W cx) (n_W cx) (n_memc cx) mf (n_kind cx) (s ++ [zb 0]) Hsb).
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    exact (proj1 (KBK Hk ltac:(lia) (n_kind cx + i) ltac:(lia))).
  - intros Hk s Hs (Hsb & Hnz). split; [|exact Hnz].
    apply (nte_abytes_keep (n_W cx) (n_W cx) (n_memc cx) mf (n_alias cx) (s ++ [zb 0]) Hsb).
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    exact (proj1 (KBA Hk ltac:(lia) (n_alias cx + i) ltac:(lia))).
  - intros Hk Hc. destruct (Hbk Hk Hc) as (junk & Hjl & Hjb & Hjw). exists junk. split; [exact Hjl|].
    fold (n_kindn cx) in Hjl. split.
    + apply (nte_abytes_keep (n_W cx) (n_W cx) (n_memc cx) mf (n_kind cx) junk Hjb).
      intros i Hi. exact (proj1 (KBK Hk Hc (n_kind cx + i) ltac:(lia))).
    + intros i Hi. destruct (KBK Hk Hc (n_kind cx + i) ltac:(lia)) as (Hv & Hnro).
      apply (nte_wr_keep (w_H (n_W cx)) (w_H (n_W cx)) (n_memc cx) mf); [| exact Hnro | exact Hv | exact (Hjw i Hi)].
      destruct Hjb as (Hj0 & Hj1 & _). fold (n_kind cx) in Hj0. fold (n_kind cx) in Hj1. lia.
  - intros Hk Hc. destruct (Hba Hk Hc) as (junk & Hjl & Hjb & Hjw). exists junk. split; [exact Hjl|].
    fold (n_aliasn cx) in Hjl. split.
    + apply (nte_abytes_keep (n_W cx) (n_W cx) (n_memc cx) mf (n_alias cx) junk Hjb).
      intros i Hi. exact (proj1 (KBA Hk Hc (n_alias cx + i) ltac:(lia))).
    + intros i Hi. destruct (KBA Hk Hc (n_alias cx + i) ltac:(lia)) as (Hv & Hnro).
      apply (nte_wr_keep (w_H (n_W cx)) (w_H (n_W cx)) (n_memc cx) mf); [| exact Hnro | exact Hv | exact (Hjw i Hi)].
      destruct Hjb as (Hj0 & Hj1 & _). fold (n_alias cx) in Hj0. fold (n_alias cx) in Hj1. lia.
Qed.

(* ==========================================================================
   3. The entry state
   ========================================================================== *)

Lemma nte_obj_vals :
  pa_val (A_OBJ 0) = 0xa1a28 /\ pa_val (A_OBJ 1) = 0xa19d0 /\ pa_val (A_OBJ 64) = 0xaa438 /\
  pa_val (A_OBJ 65) = 0xaa440 /\ pa_val A_TEXT = 0x821cc.
Proof.
  repeat split;
    first [rewrite (lv_text LV); reflexivity | rewrite (lv_obj LV) by (vm_compute; lia); reflexivity].
Qed.

(* the two image objects of the frame's header (+0xd8, +0xdc), and the function's address *)
Lemma nte_obj_hd :
  pa_val (A_OBJ 39) = 0x201ef /\ pa_val (A_OBJ 40) = 0x88974 /\ link_text + AF_nl_talk = 0x88974.
Proof.
  split; [|split]; first [rewrite (lv_obj LV) by (vm_compute; lia); reflexivity | reflexivity].
Qed.

Lemma nte_entry_st : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - NL_TALK_AK -> spZ regs <= sp0 ->
  st_ok_pi pa_segs pa_val (Eimg (Ereg regs [w64 SHADOW_OFF])) nte_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + NT_entry)) memc (seg_rom pa_segs))).
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hal16 Hwlo Hwhi.
  pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : NL_TALK_AK = 8448) by reflexivity. rewrite HK in Hwlo.
  destruct (aj_gx_const_cells SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc
    mdc k HJ) as (Kuar & Kguar & Kcell & Kgot).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
  rewrite (pal_got_uar B TL), (pal_uar_cell B TL) in Kguar. rewrite (pal_uar_cell B TL) in Kuar.
  destruct nte_obj_vals as (V0 & V1 & V64 & V65 & _).
  set (E := Eimg (Ereg regs [w64 SHADOW_OFF])).
  assert (EL : forall nn, (nn < A_TEXT)%nat -> ew E nn = ew (Ereg regs [w64 SHADOW_OFF]) nn)
    by (intros nn Hn; subst E; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (EO : forall i, (i < 66)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (pa_val (A_OBJ i)))
    by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (VB : forall nn v, ew E nn = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some nn) = v).
  { intros nn v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
  pose proof (EO 0%nat ltac:(lia)) as EO0. pose proof (EO 1%nat ltac:(lia)) as EO1.
  pose proof (EO 64%nat ltac:(lia)) as EO64. pose proof (EO 65%nat ltac:(lia)) as EO65.
  rewrite V0 in EO0, Kguar. rewrite V1 in EO1, Kgot. rewrite V64 in EO64, Kgot, Kcell.
  rewrite V65 in EO65, Kguar, Kuar.
  rewrite restrict_mkst_fx. unfold nte_ss0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold nte_regions, nte_saves, nte_probe, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable pa_segs). apply Hpres. lia.
    + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
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
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; unfold SHADOW_OFF; lia | cbn; lia |].
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
    unfold nte_regions, nte_saves, nte_probe, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP,
      extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    fold E. rewrite (VB (A_OBJ 1) 0xa19d0 EO1 ltac:(lia)), (VB (A_OBJ 64) 0xaa438 EO64 ltac:(lia)),
      (VB (A_OBJ 0) 0xa1a28 EO0 ltac:(lia)), (VB (A_OBJ 65) 0xaa440 EO65 ltac:(lia)).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1a Hwlo Hwhi HSTK HXO. clear. intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [nte_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1a Hwlo Hwhi HSTK HXO Hal16.
    clear. unfold SHADOW_OFF. intros. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* ==========================================================================
   4. The walk
   ========================================================================== *)

(* The walk: the entry state; the prologue to the realignment (NT_mv); the realigned stack pointer as the atom 60;
   the region surgery (the prologue's probe region dropped, the spill region [s1, s1 + 88) added); the run to the
   call of frame_alloc_9 (0x889f8), through LinkWalkSide.v `aj_gx_stack_malloc_sz_at`; the frame F as the atom 68
   and its header region; the PLAIN-engine runs after the call (with the frame's region in the state the token
   engine's static check `sh_static_ok` is false: F's range fact [4096, 2 ^ 47 - 8192] meets the shadow span, and
   `in_app F 32768` does not say which side of it F is on; the phase makes no instrumented load); s8 as the atom
   90 = shadow(F) and the two shadow regions; the call of meta_fill_f8 (0x55f94) through `aj_gx_set_shadow_at`;
   the run to NT_sock; and `nt_sock_inv`, assembled from the end state's registers and regions, the three posts
   and the phase's kept clause (`nte_akept_build`, `nte_mem_final`).
   The real-stack arms are refuted on the way: `beqz a2` (+0x78) by the switch cell's chunk value 1 (AR's const
   law, `aj_gx_const_cells`), `bnez s4` (+0x98) by 4096 <= F (the frame_alloc_9 post, `frames_bounds`). *)

Theorem nt_entry : forall POST, nt_from SK B POST (nt_sock_inv B) -> nt_start SK B POST.
Proof.
intros POST HNEXT cx HB.
pose proof HB as HB0.
unfold nt_base in HB.
destruct HB as (HPRE & HRD & HAPRE & HNLK & HREQ & HRLEN & HE0r & HE0sp).
destruct HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hro).
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx. pose proof pa_B_ok as HBASE.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HK : NL_TALK_AK = 8448) by reflexivity.
pose proof HJ as (HSTKj & HXOj & (memS0 & HJi0 & _) & _).
pose proof HJi0 as (HAR0 & _ & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hsp_lo : alloc_ceiling + 8448 <= spZ (n_regs cx)) by lia.
assert (Hsp_hi : spZ (n_regs cx) <= 2 ^ 47) by lia.
destruct (nt_sp1_range (spZ (n_regs cx)) ltac:(unfold NL_TALK_AFRAME; lia) Hal16) as (Hs1r & Hs1m32 & Hs1m16).
assert (Hs1v : n_sp1 cx = nt_sp1 (spZ (n_regs cx))) by reflexivity.
rewrite <- Hs1v in Hs1r, Hs1m32, Hs1m16. unfold NL_TALK_AFRAME in Hs1r.
(* ---- the entry state ---- *)
assert (HS : st_ok_pi pa_segs pa_val (Eimg (Ereg (n_regs cx) [w64 SHADOW_OFF])) nte_ss0
  (restrict (w_H (n_W cx)) (mkst (n_regs cx) (Z_to_bv 64 (BASE + NT_entry)) (n_memc cx) (seg_rom pa_segs)))).
{ apply (nte_entry_st (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx)
    (n_k cx) (n_regs cx));
  [exact HJ | exact Hal16 | exact Hwlo | exact Hwhi]. }
remember (Eimg (Ereg (n_regs cx) [w64 SHADOW_OFF])) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (n_regs cx) r)
  by (intros q r Hq; rewrite HEdef; apply ew_Eimg_Ereg_nat; exact Hq).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite HEdef, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (n_regs cx) _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ (n_regs cx)) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (Esp0 : ew E 2 = Z_to_bv 64 (spZ (n_regs cx)))
  by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
clear HEdef.
assert (SHOK : sh_ok pa_segs nte_Bx (@nil shent) E (rdW (n_W cx) (n_memc cx))) by constructor.
unfold cfg_at.
pose (RUN := paj_run_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
pose (RUNTO := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
pose (BR := paj_branch (PI := PI)).
pose (RET := paj_ret_at (PL := PL_link) (PI := PI)).
(* ---- R1: the prologue, up to the realignment (NT_mv = +0x44) ---- *)
paj_run_to_tok RUNTO HS HJ SHOK nte_span NT_mv.
{ unfold nte_ss0, nte_regions, nte_saves, nte_probe, got_regionP, bcell_regionP, uar_got_regionP,
    uar_cell_regionP; cbn [ss_mem].
  repeat (apply awr_ok_x_cons;
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros aa Haa;
      first [ lia | rewrite Usp in Haa; left; split; [left; lia | lia] ] | ]).
  apply awr_ok_x_nil. }
pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun x => spZ (n_regs cx) - 8448 <= x < spZ (n_regs cx))
  HFr ltac:(nte_win_tac)) as UN1.
pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P1.
clear HF HFr HG.
(* the realigned stack pointer becomes the atom 60 *)
prreg_raw HS (2%bv : bv 5) R2.
rewrite (denot_and_m32 E 2 (spZ (n_regs cx)) (-192) Esp0) in R2 by lia.
replace (spZ (n_regs cx) + -192) with (spZ (n_regs cx) - 192) in R2 by lia.
change (32 * ((spZ (n_regs cx) - 192) / 32)) with (n_sp1 cx) in R2.
pose proof (st_ok_pi_havoc_hi 60 E _ _ [Z_to_bv 64 (n_sp1 cx)] HS ltac:(vm_compute; reflexivity)) as HS1.
clear HS; rename HS1 into HS.
remember (havoc E 60 [Z_to_bv 64 (n_sp1 cx)]) as E1 eqn:HE1 in HS.
assert (HEI1 : img_env pa_val A_LIM E1)
  by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall nn, (nn < 60)%nat -> ew E1 nn = ew E nn)
  by (intros nn Hnn; rewrite HE1; apply YN3v.ew_havoc_old; exact Hnn).
assert (E60 : ew E1 60 = Z_to_bv 64 (n_sp1 cx))
  by (rewrite HE1; exact (ew_havoc_new E 60 [Z_to_bv 64 (n_sp1 cx)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
clear HE1.
assert (U60 : bv_unsigned (ew E1 60) = n_sp1 cx) by (rewrite E60; apply unsigned_lit_small; lia).
assert (U1sp : bv_unsigned (ew E1 2) = spZ (n_regs cx)) by (rewrite OLD1 by lia; exact Usp).
assert (EOBJ : forall i, (A_TEXT <= i < A_LIM)%nat -> bv_unsigned (ew E1 i) = pa_val i).
{ intros i Hi. rewrite (img_env_atomP E1 i HEI1 Hi). apply unsigned_lit_small. apply pa_val_range. }
assert (V241 : bv_unsigned (ew E1 241%nat) = 0xa1a28)
  by (rewrite (EOBJ 241%nat ltac:(unfold A_TEXT, A_LIM; lia)); exact (proj1 nte_obj_vals)).
assert (V242 : bv_unsigned (ew E1 242%nat) = 0xa19d0)
  by (rewrite (EOBJ 242%nat ltac:(unfold A_TEXT, A_LIM; lia)); exact (proj1 (proj2 nte_obj_vals))).
assert (V305 : bv_unsigned (ew E1 305%nat) = 0xaa438)
  by (rewrite (EOBJ 305%nat ltac:(unfold A_TEXT, A_LIM; lia)); exact (proj1 (proj2 (proj2 nte_obj_vals)))).
assert (V306 : bv_unsigned (ew E1 306%nat) = 0xaa440)
  by (rewrite (EOBJ 306%nat ltac:(unfold A_TEXT, A_LIM; lia));
      exact (proj1 (proj2 (proj2 (proj2 nte_obj_vals))))).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(rewrite (sv_off0 E1 60 (n_sp1 cx) E60); symmetry; exact R2)) as HS1 end.
clear HS; rename HS1 into HS.
add_fact HS 60%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U60; change (2 ^ 5) with 32;
        split; [lia|]; split; [lia | lia]).
(* the prologue's probe region is dropped (it meets the spill region when sp1 = sp0 - 208) *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  let rs := eval vm_compute in (pick (ss_mem ssx) [0;2;3;4;5]%nat) in
  pose proof (st_ok_pi_submem Ev ssx msx rs HS ltac:(submem_tac) ltac:(vm_compute; reflexivity)) as HS1 end.
clear HS; rename HS1 into HS. norm_pi HS.
(* ... and the spill region [s1, s1 + 88) is added *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ nte_spill HS eq_refl
  ltac:(unfold region_ok, nte_spill;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U60; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable pa_segs);
        eapply (aj_gx_present SK pa_segs B LAWS pa_segs_low); [exact HJ | lia])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
          let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, nte_spill;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite ?U60, ?U1sp, ?V241, ?V242, ?V305, ?V306; repeat split; lia)) as HS1 end.
clear HS; rename HS1 into HS. norm_pi HS.
(* ---- R2: up to the call of frame_alloc_9 (0x889f8) ---- *)
clear SHOK.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict (w_H ?Wx) ?msx) =>
  assert (SHOK : sh_ok pa_segs nte_Bx (@nil shent) Ev (mrestrict (w_H Wx) (ms_mem msx))) by constructor end.
paj_run_tok RUN HS HJ SHOK nte_span.
{ unfold nte_spill; cbn [ss_mem].
  repeat (apply awr_ok_x_cons;
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros aa Haa;
      first [ lia
            | rewrite U60 in Haa; left; split; [left; lia | lia]
            | rewrite U1sp in Haa; left; split; [left; lia | lia] ] | ]).
  apply awr_ok_x_nil. }
pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun x => spZ (n_regs cx) - 8448 <= x < spZ (n_regs cx))
  HFr ltac:(nte_win_tac)) as UN2.
pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P2.
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
  assert (UN12 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ (n_regs cx) - 8448 <= x < spZ (n_regs cx)) ->
    aview pa_segs (w_H (n_W cx)) (ms_mem msx) x = aview pa_segs (w_H (n_W cx)) (n_memc cx) x)
    by (intros x Hx Hw; rewrite (UN2 x Hx Hw); exact (UN1 x Hx Hw));
  assert (P12 : forall x, apresent (w_H (n_W cx)) (n_memc cx) x -> apresent (w_H (n_W cx)) (ms_mem msx) x)
    by (intros x Hp; exact (P2 x (P1 x Hp))) end.
clear UN1 UN2 P1 P2.
(* ---- frame_alloc_9(16672) at 0x889f8 ---- *)
pmkst HS.
clear R2.
sreg HS (1%bv : bv 5) Q1. sreg HS (2%bv : bv 5) Q2. sreg HS (3%bv : bv 5) Q3.
sreg HS (4%bv : bv 5) Q4. sreg HS (10%bv : bv 5) Q10.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
  assert (Hra : getr (ms_regs msx) 1 = Z_to_bv 64 (BASE + 26672))
    by (rewrite Q1; apply (codeptr_val E1 26672 HEI1));
  assert (Hsp2 : spZ (ms_regs msx) = n_sp1 cx)
    by (unfold spZ; rewrite Q2, (sv_off0 E1 60 (n_sp1 cx) E60); apply unsigned_lit_small; lia);
  assert (Hgp2 : getr (ms_regs msx) 3 = w64 (as_gp B))
    by (rewrite Q3, (sv_off0 E1 3 (bv_unsigned (getr (n_regs cx) 3))
          ltac:(rewrite OLD1 by lia; rewrite (EE 3%nat 3%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned));
        rewrite Z_to_bv_bv_unsigned; exact Hgp);
  assert (Htp2 : getr (ms_regs msx) 4 = w64 (as_tp B))
    by (rewrite Q4, (sv_off0 E1 4 (bv_unsigned (getr (n_regs cx) 4))
          ltac:(rewrite OLD1 by lia; rewrite (EE 4%nat 4%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned));
        rewrite Z_to_bv_bv_unsigned; exact Htp);
  assert (Hn2 : getr (ms_regs msx) 10 = w64 NT_FSZ) by (rewrite Q10; reflexivity) end.
eapply SRr_bind.
{ eapply (aj_gx_stack_malloc_sz_at SK pa_segs B LAWS pa_segs_low errno_low
      (pa_sigma LS___asan_stack_malloc_9) NT_CID ASM9 ltac:(unfold NT_CID; lia));
  [ exact HJ
  | rewrite Hsp2; exact Hs1m16
  | rewrite Hsp2; change ESTACK with 4096; lia
  | rewrite Hsp2; lia
  | exact Hgp2
  | exact Htp2
  | exact Hra
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | exact Hn2
  | change (fs_frame_bytes NT_CID) with 32768; unfold NT_FSZ; lia
  | unfold NT_FSZ; lia
  | exact (aside_room_take (n_Sc cx) NL_TALK_ASIDE NT_CID 1 Hside ltac:(left; reflexivity) ltac:(lia)) ]. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HPR2 & Ha0 & Eab2 & Hfrs2 & Hnin2
  & Hnev2 & Hbb2 & (fS2 & ES2) & HF4096 & HFceil & Hz2 & Hflag2 & HK2 & Hsbm2 & Hraw2).
(* ---- after the call: the saves and the spills kept, a0 = F the atom 68 ---- *)
assert (HFR9 : In (NT_CID, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (ajournal_gx_AR pa_segs B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx)
  (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fpos) :: n_own cx) (n_lyc cx) S2
  (n_W cx) mem2 md2 (n_k cx) HJ2) as HAR2.
destruct (nte_frame_bounds (n_lyc cx) S2 (n_W cx) mem2 md2 fpos HAR2 HFR9)
  as (HC9 & HP9 & HFal & HF4096' & HFceil' & HFapp).
jafter_call_keep_pi HS 64%nat regs2 (rdW (n_W cx) mem2) HPR2 [0;1]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
  [ rewrite ?U60, ?U1sp; intros aa Haa; apply (YCbq.mbyte_of_aview pa_segs); apply (proj1 HK2);
    [lia | rewrite Hsp2; change ESTACK with 4096; lia]
  | rewrite ?U60, ?U1sp; intros aa Haa Hwaa;
    apply (writable_kept (w_H (n_W cx)) (ms_mem ms0) mem2 aa);
    [ intros Hp; apply (proj1 (proj2 (proj2 (proj2 (proj2 HK2)))));
      [lia | rewrite Hsp2; change ESTACK with 4096; lia | exact Hp]
    | exact Hwaa ]
  | rewrite ?U60, ?U1sp; intros aa Haa; apply (YCbq.mbyte_of_aview pa_segs); apply (proj1 HK2);
    [lia | rewrite Hsp2; change ESTACK with 4096; lia]
  | rewrite ?U60, ?U1sp; intros aa Haa Hwaa;
    apply (writable_kept (w_H (n_W cx)) (ms_mem ms0) mem2 aa);
    [ intros Hp; apply (proj1 (proj2 (proj2 (proj2 (proj2 HK2)))));
      [lia | rewrite Hsp2; change ESTACK with 4096; lia | exact Hp]
    | exact Hwaa ] ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E1 64 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEIa : img_env pa_val A_LIM E2)
  by (rewrite HE2; apply img_env_havoc; [exact HEI1 | cbv; lia]).
assert (OLDa : forall nn, (nn < 64)%nat -> ew E2 nn = ew E1 nn)
  by (intros nn Hnn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hnn).
assert (E68 : ew E2 68 = w64 (frame_addr (n_lyc cx) NT_CID fpos)).
{ rewrite HE2, <- Ha0.
  exact (ew_havoc_new E1 64 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0) ltac:(cbn; lia)). }
assert (U68 : bv_unsigned (ew E2 68) = frame_addr (n_lyc cx) NT_CID fpos)
  by (rewrite E68; unfold w64; apply unsigned_lit_small; lia).
assert (U60a : bv_unsigned (ew E2 60) = n_sp1 cx) by (rewrite OLDa by lia; exact U60).
assert (U2spa : bv_unsigned (ew E2 2) = spZ (n_regs cx)) by (rewrite OLDa by lia; exact U1sp).
destruct (al_frames _ _ LAWS (n_lyc cx) S2 (n_W cx) mem2 md2 NT_CID fpos HAR2 HFR9)
  as (_ & _ & HFpres & HSHpres).
add_fact HS 68%nat (mkAF 4096 140737479966720 6)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U68; change (2 ^ 6) with 64;
        split; [lia|]; split; [exact HFal | lia]).
(* the frame's header region [F, F + 24) *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ nte_hd HS eq_refl
  ltac:(unfold region_ok, nte_hd;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U68; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable pa_segs);
        exact (proj1 (HFpres (frame_addr (n_lyc cx) NT_CID fpos + o)
                 ltac:(change (fs_frame_bytes NT_CID) with 32768; lia))))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
          let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, nte_hd;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite ?U68, ?U60a, ?U2spa; repeat split; lia)) as HS1 end.
clear HS; rename HS1 into HS. norm_pi HS.
(* ---- R3 (+0x88 .. +0xf4), on the PLAIN engine (the frame's region is in the state now) ---- *)
pose (RUNTOP := paj_run_to_plain_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) =>
  let r := eval vm_compute in (sym_run_toN_pi link_tpi FUEL (AF_nl_talk + 0xf4) ssx) in
  lazymatch r with
  | (?ss3, ?st3) =>
    assert (Hrun3 : sym_run_toN_pi link_tpi FUEL (AF_nl_talk + 0xf4) ssx = (ss3, st3))
      by (vm_compute; reflexivity);
    eapply (RUNTOP Wx FUEL (AF_nl_talk + 0xf4) Ev ssx ss3 st3 msx);
    [ exact HEIa | exact HS | exact Hrun3 | exact I | exact HJ2 | | ]
  end end.
{ cbn [ss_mem].
  repeat (apply awr_ok_x_cons;
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros aa Haa;
      first [ lia
            | rewrite U68 in Haa; left; eapply (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low);
              [ exact HJ2 | left; reflexivity
              | left; unfold in_zr, frame_rng; cbn [fst snd];
                change (fs_frame_bytes NT_CID) with 32768; lia ]
            | rewrite U60a in Haa; left; split; [left; lia | lia]
            | rewrite U2spa in Haa; left; split; [left; lia | lia] ] | ]).
  apply awr_ok_x_nil. }
clear HS HJ2 Hrun3.
intros ms3 mat3 HS HJ3 HF3 HFr3 HG3.
cbn [ms_mem mkst] in HF3, HFr3, HG3, HJ3.
set (F := frame_addr (n_lyc cx) NT_CID fpos) in *.
set (SH := shadow_of_addr SHADOW_OFF F).
assert (EF : nF cx fpos = F) by reflexivity.
assert (ESH : shadow_addr F = SH) by reflexivity.
assert (ESH' : nSH cx fpos = SH) by reflexivity.
assert (HSHv : SH = SHADOW_OFF + F / 8) by reflexivity.
change (fs_frame_bytes NT_CID) with 32768 in HFpres.
change (fs_frame_bytes NT_CID / 8) with 4096 in HSHpres. rewrite ESH in HSHpres.
pose proof HFapp as HFapp'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp'.
destruct (div8_of_mul64 F HFal) as (Ed8 & Ed64).
assert (HSHlo : SHADOW_OFF + 512 <= SH) by (rewrite HSHv; unfold SHADOW_OFF; lia).
assert (HSHhi : SH + 4096 <= SHADOW_OFF + 2 ^ 44) by (rewrite HSHv; unfold SHADOW_OFF; lia).
assert (HSHr : 0 <= SH /\ SH + 4096 < 2 ^ 64) by (clear - HSHlo HSHhi; unfold SHADOW_OFF in *; lia).
assert (HSHsp : SH + 4096 <= spZ (n_regs cx) - 8448)
  by (clear - HSHhi Hsp_lo C1a; unfold SHADOW_OFF in *; lia).
assert (HFsp : F + 32768 <= spZ (n_regs cx) - 8448) by lia.
assert (DFS : F + 32768 <= SH \/ SH + 4096 <= F)
  by (clear - HSHlo HSHhi HFapp'; unfold SHADOW_OFF in *; lia).
assert (HSHal : SH mod 4 = 0).
{ rewrite HSHv. unfold SHADOW_OFF. rewrite Ed8.
  replace (2147450880 + 8 * (F / 64)) with ((536862720 + 2 * (F / 64)) * 4) by lia.
  apply Z_mod_mult. }
(* what R3 kept *)
pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (nte_Zf (spZ (n_regs cx)) F SH) HFr3 ltac:(nte_win_tac))
  as UN3.
pose proof (fun x Hp => apresent_grows _ _ _ x HG3 Hp) as P3.
clear HF3 HFr3 HG3.
(* ---- s8 := shadow(F), the atom 90 with its range fact ---- *)
assert (E32a : ew E2 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDa by lia; rewrite OLD1 by lia; exact E32).
prreg_raw HS (24%bv : bv 5) R24.
rewrite (denot_shadow_cell E2 68 32 F SHADOW_OFF E68 ltac:(lia) E32a
          ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)) in R24.
pose proof (st_ok_pi_havoc_hi 90 E2 _ _ [Z_to_bv 64 SH] HS ltac:(vm_compute; reflexivity)) as HS1.
clear HS; rename HS1 into HS.
remember (havoc E2 90 [Z_to_bv 64 SH]) as E3 eqn:HE3 in HS.
assert (HEIb : img_env pa_val A_LIM E3)
  by (rewrite HE3; apply img_env_havoc; [exact HEIa | cbn [length]; unfold A_TEXT; lia]).
assert (OLDb : forall nn, (nn < 90)%nat -> ew E3 nn = ew E2 nn)
  by (intros nn Hnn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hnn).
assert (E90 : ew E3 90 = Z_to_bv 64 SH)
  by (rewrite HE3; exact (ew_havoc_new E2 90 [Z_to_bv 64 SH] 0 (Z_to_bv 64 0) ltac:(cbn [length]; lia))).
clear HE3.
assert (U90 : bv_unsigned (ew E3 90) = SH) by (rewrite E90; apply unsigned_lit_small; lia).
assert (U68b : bv_unsigned (ew E3 68) = F) by (rewrite OLDb by lia; exact U68).
assert (U60b : bv_unsigned (ew E3 60) = n_sp1 cx) by (rewrite OLDb by lia; exact U60a).
assert (U2spb : bv_unsigned (ew E3 2) = spZ (n_regs cx)) by (rewrite OLDb by lia; exact U2spa).
assert (E60b : ew E3 60 = Z_to_bv 64 (n_sp1 cx)) by (rewrite OLDb, OLDa by lia; exact E60).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (24%bv : bv 5) (SOff 90 0) HS ltac:(vm_compute; reflexivity)
    ltac:(rewrite (sv_off0 E3 90 _ E90); symmetry; exact R24)) as HS1 end.
clear HS; rename HS1 into HS.
add_fact HS 90%nat (mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 2)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U90; change (2 ^ 2) with 4;
        split; [lia|]; split; [exact HSHal | lia]).
(* the left redzone's shadow [SH, SH + 4), present by al_frames' shadow clause *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ nte_sha HS eq_refl
  ltac:(unfold region_ok, nte_sha;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U90; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable pa_segs); apply P3;
        exact (proj1 (HSHpres o ltac:(lia))))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
          let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, nte_sha;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite ?U90, ?U68b, ?U60b, ?U2spb; repeat split; lia)) as HS1 end.
clear HS; rename HS1 into HS. norm_pi HS.
(* ---- +0xf4 .. the call of meta_fill_f8 (0x88a88): the four 0xf1 bytes, s3, a0, a1 ---- *)
pose (RUNC := paj_run_call_plain_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) =>
  let r := eval vm_compute in (sym_runN_pi link_tpi FUEL ssx) in
  lazymatch r with
  | (?ss4, PRS_call ?s4) =>
    assert (Hrun4 : sym_runN_pi link_tpi FUEL ssx = (ss4, PRS_call s4)) by (vm_compute; reflexivity);
    eapply (RUNC Wx FUEL Ev ssx ss4 s4 msx); [exact HEIb | exact HS | exact Hrun4 | exact HJ3 | | ]
  | ?x => fail "the run to meta_fill_f8 ends at" x
  end end.
{ cbn [ss_mem].
  repeat (apply awr_ok_x_cons;
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros aa Haa;
      first [ lia
            | rewrite U90 in Haa; left; eapply (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low);
              [ exact HJ3 | left; reflexivity
              | right; unfold in_zr; cbn [fst snd]; fold F; rewrite ESH;
                change (fs_frame_bytes NT_CID / 8) with 4096; lia ]
            | rewrite U68b in Haa; left; eapply (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low);
              [ exact HJ3 | left; reflexivity
              | left; unfold in_zr, frame_rng; cbn [fst snd]; fold F;
                change (fs_frame_bytes NT_CID) with 32768; lia ]
            | rewrite U60b in Haa; left; split; [left; lia | lia]
            | rewrite U2spb in Haa; left; split; [left; lia | lia] ] | ]).
  apply awr_ok_x_nil. }
clear HS HJ3 Hrun4.
intros ms4 mat4 HS HJ4 HF4 HFr4 HG4.
cbn [ms_mem mkst] in HF4, HFr4, HG4, HJ4.
pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (nte_Zf (spZ (n_regs cx)) F SH) HFr4 ltac:(nte_win_tac))
  as UN4.
pose proof (fun x Hp => apresent_grows _ _ _ x HG4 Hp) as P4.
clear HF4 HFr4 HG4.
(* ---- meta_fill_f8(shadow(F) + 4, 2048) (0x55f94), LinkWalkSide.v aj_gx_set_shadow_at ---- *)
pmkst HS.
sreg HS (1%bv : bv 5) Q1c. sreg HS (2%bv : bv 5) Q2c. sreg HS (3%bv : bv 5) Q3c.
sreg HS (4%bv : bv 5) Q4c. sreg HS (10%bv : bv 5) Q10c. sreg HS (11%bv : bv 5) Q11c.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
  assert (Hmra : getr (ms_regs msx) 1 = Z_to_bv 64 (BASE + 26816))
    by (rewrite Q1c; apply (codeptr_val E3 26816 HEIb));
  assert (Hmsp : spZ (ms_regs msx) = n_sp1 cx)
    by (unfold spZ; rewrite Q2c, (sv_off0 E3 60 (n_sp1 cx) E60b); apply unsigned_lit_small; lia);
  assert (Hmgp : getr (ms_regs msx) 3 = w64 (as_gp B))
    by (rewrite Q3c, (sv_off0 E3 3 (bv_unsigned (getr (n_regs cx) 3))
          ltac:(rewrite OLDb, OLDa, OLD1 by lia; rewrite (EE 3%nat 3%bv eq_refl); symmetry;
                apply Z_to_bv_bv_unsigned));
        rewrite Z_to_bv_bv_unsigned; exact Hgp);
  assert (Hmtp : getr (ms_regs msx) 4 = w64 (as_tp B))
    by (rewrite Q4c, (sv_off0 E3 4 (bv_unsigned (getr (n_regs cx) 4))
          ltac:(rewrite OLDb, OLDa, OLD1 by lia; rewrite (EE 4%nat 4%bv eq_refl); symmetry;
                apply Z_to_bv_bv_unsigned));
        rewrite Z_to_bv_bv_unsigned; exact Htp);
  assert (Hma0 : getr (ms_regs msx) 10 = w64 (SH + 4))
    by (rewrite Q10c, (nte_sv_off E3 90 4 SH E90 ltac:(lia)); reflexivity);
  assert (Hma1 : getr (ms_regs msx) 11 = w64 2048) by (rewrite Q11c; reflexivity) end.
eapply SRr_bind.
{ eapply (aj_gx_set_shadow_at SK pa_segs B LAWS pa_segs_low (pa_sigma LS___asan_set_shadow_f8) 0xf8 ASF8
    (n_G cx) (n_XO cx) (n_OUT cx) (n_W cx) _ _ (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fpos) :: n_own cx) (n_lyc cx) S2 _ (n_k cx) NT_CID fpos
    (SH + 4) 2048 _ HGok HJ4);
  [ left; reflexivity | exact Hma0 | exact Hma1 | lia
  | fold F; rewrite ESH; lia
  | fold F; rewrite ESH; change (fs_frame_bytes NT_CID / 8) with 4096; lia
  | rewrite Hmsp; exact Hs1m16 | rewrite Hmsp; change ESTACK with 4096; lia | rewrite Hmsp; lia
  | exact Hmgp | exact Hmtp | exact Hmra | apply ret_ok_codeptr_v; [lia | reflexivity] ]. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Hf8 & Hkeep5 & Hpres5 & Hsbm5).
jafter_call_keep_pi HS 96%nat regs5 (rdW (n_W cx) mem5) HP5 [0;1;2;3]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
  rewrite ?U90, ?U68b, ?U60b, ?U2spb;
  first [ intros aa Haa Hwaa; apply (writable_kept (w_H (n_W cx)) (ms_mem ms4) mem5 aa);
          [exact (Hpres5 aa) | exact Hwaa]
        | intros aa Haa; apply (YCbq.mbyte_of_aview pa_segs); apply Hkeep5; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E3 96 (map (getr regs5) CLOB)) as E4 eqn:HE4 in HS.
assert (HEIc : img_env pa_val A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEIb | cbv; lia]).
assert (OLDc : forall nn, (nn < 96)%nat -> ew E4 nn = ew E3 nn)
  by (intros nn Hnn; rewrite HE4; apply YN3v.ew_havoc_old; exact Hnn).
clear HE4.
assert (U90c : bv_unsigned (ew E4 90) = SH) by (rewrite OLDc by lia; exact U90).
assert (U68c : bv_unsigned (ew E4 68) = F) by (rewrite OLDc by lia; exact U68b).
assert (U60c : bv_unsigned (ew E4 60) = n_sp1 cx) by (rewrite OLDc by lia; exact U60b).
assert (U2spc : bv_unsigned (ew E4 2) = spZ (n_regs cx)) by (rewrite OLDc by lia; exact U2spb).
(* the right redzone's shadow [SH + 2052, SH + 2084) *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ nte_shc HS eq_refl
  ltac:(unfold region_ok, nte_shc;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U90c; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable pa_segs); apply Hpres5, P4, P3;
        exact (proj1 (HSHpres o ltac:(lia))))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
          let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, nte_shc;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite ?U90c, ?U68c, ?U60c, ?U2spc; repeat split; lia)) as HS1 end.
clear HS; rename HS1 into HS. norm_pi HS.
(* ---- +0x118 .. NT_sock (+0x1a0): the 32 0xf3 bytes ---- *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) =>
  let r := eval vm_compute in (sym_run_toN_pi link_tpi FUEL NT_sock ssx) in
  lazymatch r with
  | (?ss6, ?st6) =>
    assert (Hrun6 : sym_run_toN_pi link_tpi FUEL NT_sock ssx = (ss6, st6)) by (vm_compute; reflexivity);
    eapply (RUNTOP Wx FUEL NT_sock Ev ssx ss6 st6 msx);
    [ exact HEIc | exact HS | exact Hrun6 | exact I | exact HJ5 | | ]
  end end.
{ cbn [ss_mem].
  repeat (apply awr_ok_x_cons;
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros aa Haa;
      first [ lia
            | rewrite U90c in Haa; left; eapply (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low);
              [ exact HJ5 | left; reflexivity
              | right; unfold in_zr; cbn [fst snd]; fold F; rewrite ESH;
                change (fs_frame_bytes NT_CID / 8) with 4096; lia ]
            | rewrite U68c in Haa; left; eapply (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low);
              [ exact HJ5 | left; reflexivity
              | left; unfold in_zr, frame_rng; cbn [fst snd]; fold F;
                change (fs_frame_bytes NT_CID) with 32768; lia ]
            | rewrite U60c in Haa; left; split; [left; lia | lia]
            | rewrite U2spc in Haa; left; split; [left; lia | lia] ] | ]).
  apply awr_ok_x_nil. }
clear HS HJ5 Hrun6.
intros ms6 mat6 HS HJ6 HF6 HFr6 HG6.
cbn [ms_mem mkst] in HF6, HFr6, HG6, HJ6.
pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (nte_Zf (spZ (n_regs cx)) F SH) HFr6 ltac:(nte_win_tac))
  as UN6.
pose proof (fun x Hp => apresent_grows _ _ _ x HG6 Hp) as P6.
clear HF6 HFr6 HG6.
(* ==== the cut NT_sock: nt_sock_inv ==== *)
assert (EOLD : forall nn, (nn < 60)%nat -> ew E4 nn = ew E nn)
  by (intros nn Hnn; rewrite OLDc, OLDb, OLDa, OLD1 by lia; reflexivity).
assert (SVR : forall nn (r : bv 5), (nn < 60)%nat -> Z.of_nat nn = bv_unsigned r ->
          sv_denot E4 (SOff nn 0) = Z_to_bv 64 (bv_unsigned (getr (n_regs cx) r))).
{ intros nn r Hn Hr. apply sv_off0. rewrite (EOLD nn Hn), (EE nn r Hr). symmetry. apply Z_to_bv_bv_unsigned. }
assert (E68c : ew E4 68 = Z_to_bv 64 F) by (rewrite OLDc, OLDb by lia; exact E68).
assert (E90c : ew E4 90 = Z_to_bv 64 SH) by (rewrite OLDc by lia; exact E90).
assert (E60c : ew E4 60 = Z_to_bv 64 (n_sp1 cx)) by (rewrite OLDc by lia; exact E60b).
(* the memory after frame_alloc_9: only the window, the header and the frame's shadow moved *)
assert (UNP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (n_regs cx) - 8448 <= a < spZ (n_regs cx)) ->
  ~ (F <= a < F + 24) -> ~ (SH <= a < SH + 2084) ->
  aview pa_segs (w_H (n_W cx)) (ms_mem ms6) a = aview pa_segs (w_H (n_W cx)) mem2 a).
{ intros a Ha H1 H2 H3.
  rewrite (UN6 a Ha ltac:(unfold nte_Zf; lia)), (Hkeep5 a Ha ltac:(lia)), (UN4 a Ha ltac:(unfold nte_Zf; lia)).
  exact (UN3 a Ha ltac:(unfold nte_Zf; lia)). }
assert (PP : forall a, apresent (w_H (n_W cx)) mem2 a -> apresent (w_H (n_W cx)) (ms_mem ms6) a)
  by (intros a Hp; exact (P6 a (Hpres5 a (P4 a (P3 a Hp))))).
(* the phase's kept clause *)
rewrite Hsp2 in HK2.
assert (AKF : akept pa_segs B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_W cx) (ms_mem ms6)
  (spZ (n_regs cx) - NL_TALK_AK) (spZ (n_regs cx)) (fun a => False \/ aside_rng (n_lyc cx) NT_CID fpos a)).
{ rewrite HK.
  apply (nte_akept_build (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (ms_mem ms0) mem2 (ms_mem ms6)
    (spZ (n_regs cx) - 8448) (spZ (n_regs cx)) (n_sp1 cx)
    (fun a => (F <= a < F + 24) \/ (SH <= a < SH + 2084)) _ HAR0).
  - lia.
  - lia.
  - intros a Ha. apply Hpres0. rewrite HK in Hwlo. lia.
  - exact UN12.
  - exact P12.
  - exact HK2.
  - change ESTACK with 4096. lia.
  - lia.
  - intros a Ha Hw HX. apply UNP; [exact Ha | exact Hw | intros H; apply HX; left; exact H
                                  | intros H; apply HX; right; exact H].
  - exact PP.
  - intros a [Ha | Ha]; right; unfold aside_rng, in_zr, frame_rng; cbn [fst snd]; fold F; rewrite ?ESH;
      change (fs_frame_bytes NT_CID) with 32768; [left; lia | right; left; lia]. }
destruct (nte_mem_final cx fpos S2 (n_W cx) mem2 md2 (ms_mem ms6) HB0 HAR2 Hfrs2 Eab2 AKF)
  as (HRODf & HNLKf & HREQf & HBUFf).
(* the end state's regions and registers *)
nte_region HS 0%nat HRshc. nte_region HS 1%nat HRsha. nte_region HS 2%nat HRhd.
nte_region HS 3%nat HRsp. nte_region HS 4%nat HRsv.
try clear Q1. try clear Q2. try clear Q3. try clear Q4. try clear Q10.
prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
prreg HS (18%bv : bv 5) Q18. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Hms6.
eapply (HNEXT cx fpos (n_k cx) (n_lyc cx) S2 (n_W cx)); [exact HB0 | exact HJ6 | exact Hfrs2 |].
unfold nt_sock_inv.
split.
{ rewrite Hms6. unfold nt_shape. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
  repeat split; reflexivity. }
split.
{ unfold nt_regs.
  split; [rewrite Q2; exact E60c|].
  split; [rewrite Q8, EOLD by lia; exact Esp0|].
  split; [rewrite Q9; exact E60c|].
  split; [rewrite Q18; exact E68c|].
  split; [rewrite Q21, EOLD by lia; exact E32|].
  split; [rewrite Q24; exact E90c|].
  split; [rewrite Q3, EOLD by lia; exact (EE 3%nat 3%bv eq_refl)|].
  rewrite Q4, EOLD by lia; exact (EE 4%nat 4%bv eq_refl). }
split.
{ unfold nt_saved, nt_at. split.
  - eapply (nte_rd_at E4 _ _ 2 _ _ _ _ _ _ (-8) (SOff 1 0) _ _ HRsv U2spc);
      [nte_in | unfold raZ; apply SVR; [lia | vm_compute; reflexivity] | unfold raZ; apply nte_u64 | lia].
  - intros j Hj.
    assert (Hjc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/
                  j = 10 \/ j = 11) by lia.
    destruct Hjc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]].
    + nte_save HRsv U2spc (-16) (SOff 8 0) SVR.
    + nte_save HRsv U2spc (-24) (SOff 9 0) SVR.
    + nte_save HRsv U2spc (-32) (SOff 18 0) SVR.
    + nte_save HRsv U2spc (-40) (SOff 19 0) SVR.
    + nte_save HRsv U2spc (-48) (SOff 20 0) SVR.
    + nte_save HRsv U2spc (-56) (SOff 21 0) SVR.
    + nte_save HRsv U2spc (-64) (SOff 22 0) SVR.
    + nte_save HRsv U2spc (-72) (SOff 23 0) SVR.
    + nte_save HRsv U2spc (-80) (SOff 24 0) SVR.
    + nte_save HRsv U2spc (-88) (SOff 25 0) SVR.
    + nte_save HRsv U2spc (-96) (SOff 26 0) SVR.
    + nte_save HRsv U2spc (-104) (SOff 27 0) SVR. }
split.
{ unfold nt_header, nt_at. rewrite EF. destruct nte_obj_hd as (V39 & V40 & VT).
  split; [|split; [|split]].
  - eapply (nte_rd_at E4 _ _ 68 _ _ _ _ _ _ 0 (SLit 1102416563) _ _ HRhd U68c);
      [nte_in | reflexivity | unfold NT_MAGIC; lia | lia].
  - eapply (nte_rd_at E4 _ _ 68 _ _ _ _ _ _ 8 (SOff 280 0) _ _ HRhd U68c);
      [nte_in | | lia | lia].
    apply sv_off0. rewrite (img_env_atomP E4 280 HEIc ltac:(unfold A_TEXT, A_LIM; lia)).
    exact (f_equal (Z_to_bv 64) V39).
  - rewrite VT. eapply (nte_rd_at E4 _ _ 68 _ _ _ _ _ _ 16 (SOff 281 0) _ _ HRhd U68c);
      [nte_in | | lia | lia].
    apply sv_off0. rewrite (img_env_atomP E4 281 HEIc ltac:(unfold A_TEXT, A_LIM; lia)).
    exact (f_equal (Z_to_bv 64) V40).
  - change (fs_frame_bytes NT_CID) with 32768. change (fs_frame_bytes NT_CID) with 32768 in Hflag2.
    apply (nte_rdword_kept (w_H (n_W cx)) mem2 (ms_mem ms6)); [|exact Hflag2].
    intros i Hi. apply UNP; lia. }
split.
{ unfold nt_slots0, nt_at, NS_KIND, NS_KINDN, NS_F. rewrite EF. split; [|split].
  - eapply (nte_rd_at E4 _ _ 60 _ _ _ _ _ _ 48 (SOff 12 0) _ _ HRsp U60c);
      [nte_in | unfold n_kind, aarg, argZ; apply SVR; [lia | vm_compute; reflexivity]
      | unfold n_kind, aarg, argZ; apply nte_u64 | lia].
  - eapply (nte_rd_at E4 _ _ 60 _ _ _ _ _ _ 56 (SOff 13 0) _ _ HRsp U60c);
      [nte_in | unfold n_kindn, aarg, argZ; apply SVR; [lia | vm_compute; reflexivity]
      | unfold n_kindn, aarg, argZ; apply nte_u64 | lia].
  - eapply (nte_rd_at E4 _ _ 60 _ _ _ _ _ _ 80 (SOff 68 0) _ _ HRsp U60c);
      [nte_in | exact (sv_off0 E4 68 F E68c) | lia | lia]. }
split; [rewrite Q19, U90c; reflexivity|].
split; [rewrite Q20; exact E68c|].
split.
{ rewrite Q23, EOLD by lia. rewrite (EE 15%nat (Z_to_bv 5 (10 + 5)) ltac:(vm_compute; reflexivity)).
  unfold n_aliasn, aarg, argZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ rewrite Q25, EOLD by lia. rewrite (EE 14%nat (Z_to_bv 5 (10 + 4)) ltac:(vm_compute; reflexivity)).
  unfold n_alias, aarg, argZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ rewrite Q26, EOLD by lia. rewrite (EE 11%nat (Z_to_bv 5 (10 + 1)) ltac:(vm_compute; reflexivity)).
  unfold n_len, aarg, argZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ rewrite Q27, EOLD by lia. rewrite (EE 10%nat (Z_to_bv 5 (10 + 0)) ltac:(vm_compute; reflexivity)).
  unfold n_req, aarg, argZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ unfold nt_frame_shadow. rewrite ESH'. split; [|split].
  - intros i Hi. replace (SH + i) with (SH + 0 + i) by lia.
    apply (nte_bytes_at E4 _ _ 90 SH _ _ _ _ _ 0 4 18446744073709551601 241 HRsha U90c);
      [vm_compute; reflexivity | lia | reflexivity | lia].
  - intros i Hi. rewrite (UN6 (SH + 4 + i) ltac:(lia) ltac:(unfold nte_Zf; lia)). exact (Hf8 i Hi).
  - intros i Hi.
    apply (nte_bytes_at E4 _ _ 90 SH _ _ _ _ _ 2052 32 18446744073709551603 243 HRshc U90c);
      [vm_compute; reflexivity | lia | reflexivity | lia]. }
split.
{ unfold nt_jbk. split; [reflexivity|].
  split; [rewrite Eab2; apply Permutation_refl|].
  split; [rewrite ES2; reflexivity|].
  split; [exact Hfrs2|]. split; [exact Hnin2|]. split; [intros c p; reflexivity|].
  split; [exists S2, (n_W cx), mem2, md2; split; [exact HAR2|]; split; [exact Hfrs2 | exact Eab2]|].
  destruct (nte_sbm_fds _ _ Hsbm5) as (F5a & F5b). destruct (nte_sbm_fds _ _ Hsbm2) as (F2a & F2b).
  rewrite ?nte_wvb_fds in F5a. rewrite ?nte_wvb_fds in F2a. rewrite ?nte_wvb_fds.
  rewrite ?nte_wvb_fs in F5b. rewrite ?nte_wvb_fs in F2b. rewrite ?nte_wvb_fs.
  split; congruence. }
split.
{ unfold nt_kept. split; [exact AKF|]. split; [exact HRODf | intros a []]. }
split; [exact HNLKf|]. split; [exact HREQf|]. split; [exact HBUFf|].
unfold nBUF, NT_BUFOFF, NT_BUFLEN. rewrite EF.
apply nte_abuf_present; [| lia | lia | lia].
intros i Hi. apply PP. exact (proj1 (HFpres (F + 32 + i) ltac:(lia))).
Qed.

End b.
End a.

About nt_entry.
Print Assumptions nt_entry.
