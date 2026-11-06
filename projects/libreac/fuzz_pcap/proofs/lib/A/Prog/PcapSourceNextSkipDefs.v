(* pcap_source_next (0x8181c) on the ASan build of libreac v1.9.0: the entry predicates of the skip
   phase (lib/A/Prog/PcapSourceNextSkip.v), over the shared middle state nx_mid of
   PcapSourceNextDefs.v.

   NP_sk1 (0x81ac0) is reached from the header phase (lib/A/Prog/PcapSourceNextHdrB.v) when the record at q is longer than
   the caller's buffer: the header fread returned 16 (`bne a0,a1` 0x819c4 not taken, so q + 16 <= |C|
   and the stream is at q + 16), incl = the header's bytes 8..11 is not 0 (`beqz s9` 0x81a2c not
   taken), ps->orig := orig (`sw a3,0(t2)` 0x81ab8), and cap < incl (`bgeu s7,s11` 0x81abc not taken,
   s11 = incl zero-extended, 0x81aac / 0x81ab0). The model's kind of the record is then KBig0
   (cap = 0), KBig or KCutBig (nxs_kind_big in the walk).

   NP_sk0 (0x81ac4) is the head of the skip loop: r bytes of the record are still to read, the
   stream is at q + 16 + incl - r, and s9's low word is r (`subw s9,s9,s11` 0x81af8 keeps it).

   Registers at both cuts (the hand-off's register map, next.dis (sha256 06286410ee55; internal record)): s4 = buf, s5 = ps, s6 = -1
   (`addi s6,zero,-1` 0x819bc), s7 = cap, s10 = F + 32 (the loop head needs it back), and s9 whose
   low 32 bits are the bytes still to read (s9 may carry a sign extension above them: `slliw`
   0x819f4 / 0x81a20, `subw` 0x81af8; every use reads the low word: `slli/srli` 0x81aac, 0x81ac4,
   `subw`, and `bnez s9` 0x81afc after the `subw`). s2, s3 (nx_body0) and s8 (nx_mid) as everywhere.

   Every number is read from the pinned fuzz_pcap.asan image
   (sha256 b7a91d9b1fb0017d...). *)
(* Modified by Theorem Labs, 2026-10: nxs_vm_frame (a copy of lib/A/Prog/PcapSourceClose.v's vm_frame at SEGS) and
   nxs_ra_frame (a copy of ra_frame) deleted; their uses name lib/A/Prog/PcapSourceCloseSpec.v's vm_frame_segs and
   ra_frame. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PFreadM PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextKit.
(* The image-free frame lemmas vm_frame_segs and ra_frame, Required without Import and used qualified. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceCloseSpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YI13 YI01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.

(* The model's incl of the record at q, for this call's stream and byte order. *)
Definition nx_incl (cx : ncx) (q : Z) : Z := PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q.

(* What both cuts of the skip phase share, for the record at q with r bytes still to read: the
   turn's start q is one the record loop may go on from (nx_next_ok R), the model's chain clause at
   q, the header facts (q + 16 <= |C|, incl <> 0, cap < incl), the middle state at pc with `ph` in
   scope, the stream at q + 16 + incl - r, ps->orig = orig q (nx_ol (Some q)), vtag / vid / ts the
   caller's, and the registers. *)
Definition nx_skip_at (R : ncx -> Z -> Prop) (pc r : Z)
  (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
  (md3 : Model) : Prop :=
  exists q lh,
    nx_next_ok R cx q /\
    nx_chain_inv (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh /\
    q + 16 <= Z.of_nat (length (n_C cx)) /\
    nx_incl cx q <> 0 /\ n_cap cx < nx_incl cx q /\
    0 < r <= nx_incl cx q /\
    nx_mid B MT KS cx fp pc NSH_ph (nx_E cx) (q + 16 + nx_incl cx q - r) (nx_ol cx (Some q))
      (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W3 ms3 md3 /\
    getr (ms_regs ms3) 20 = w64 (n_buf cx) /\
    getr (ms_regs ms3) 21 = w64 (n_ps cx) /\
    getr (ms_regs ms3) 22 = w64 (-1) /\
    getr (ms_regs ms3) 23 = w64 (n_cap cx) /\
    bv_unsigned (getr (ms_regs ms3) 25) mod 2 ^ 32 = r /\
    getr (ms_regs ms3) 26 = w64 (nF cx fp + NO_PH).

(* NP_sk1 (0x81ac0, `beqz s7`): the whole record is still to read (r = incl), the stream is at
   q + 16. *)
Definition nx_sk1_inv (R : ncx -> Z -> Prop)
  (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
  (md3 : Model) : Prop :=
  exists q lh,
    nx_next_ok R cx q /\
    nx_chain_inv (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh /\
    q + 16 <= Z.of_nat (length (n_C cx)) /\
    nx_incl cx q <> 0 /\ n_cap cx < nx_incl cx q /\
    nx_mid B MT KS cx fp NP_sk1 NSH_ph (nx_E cx) (q + 16) (nx_ol cx (Some q))
      (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W3 ms3 md3 /\
    getr (ms_regs ms3) 20 = w64 (n_buf cx) /\
    getr (ms_regs ms3) 21 = w64 (n_ps cx) /\
    getr (ms_regs ms3) 22 = w64 (-1) /\
    getr (ms_regs ms3) 23 = w64 (n_cap cx) /\
    bv_unsigned (getr (ms_regs ms3) 25) mod 2 ^ 32 = nx_incl cx q /\
    getr (ms_regs ms3) 26 = w64 (nF cx fp + NO_PH).

(* NP_sk0 (0x81ac4), the skip loop's invariant: r bytes still to read, 0 < cap (the `beqz s7` at
   0x81ac0 was not taken). The loop is proved by induction on r. *)
Definition nx_sk0_inv (R : ncx -> Z -> Prop) (r : Z)
  (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
  (md3 : Model) : Prop :=
  n_cap cx <> 0 /\ nx_skip_at R NP_sk0 r cx fp k2 ly3 S3 W3 ms3 md3.

End c.

(* ---------------------------------------------------------------------------------------------- *)
(* Byte-level helpers for the fread steps into the caller's buffer (0x81af0 here, 0x81bd4 in the    *)
(* record phase).                                                                                   *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma nxs_ps_at_frame : forall (m m' : word -> option byte) ps h sw lol lvt lvid pad,
  (forall x, ps <= x < ps + PS_LEN -> mbyte SEGS m' x = mbyte SEGS m x) ->
  nx_ps_at SEGS m ps h sw lol lvt lvid pad -> nx_ps_at SEGS m' ps h sw lol lvt lvid pad.
Proof.
intros m m' ps h sw lol lvt lvid pad Hfr Hps. unfold nx_ps_at in *. destruct Hps as (V1 & V2 & V3 & V4 & V5 & G & Hl).
unfold PS_LEN, PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF in *.
split; [apply (PcapSourceCloseSpec.vm_frame_segs _ m); [intros x Hx; apply Hfr; clear - Hx; lia | exact V1]|].
split; [apply (PcapSourceCloseSpec.vm_frame_segs _ m); [intros x Hx; apply Hfr; clear - Hx; lia | exact V2]|].
split; [apply (PcapSourceCloseSpec.vm_frame_segs _ m); [intros x Hx; apply Hfr; clear - Hx; lia | exact V3]|].
split; [apply (PcapSourceCloseSpec.vm_frame_segs _ m); [intros x Hx; apply Hfr; clear - Hx; lia | exact V4]|].
split; [apply (PcapSourceCloseSpec.vm_frame_segs _ m); [intros x Hx; apply Hfr; clear - Hx; lia | exact V5]|].
split; [|exact Hl]. apply (garr8_frame SEGS m m' _ _ G). intros x Hx. apply Hfr. rewrite Hl in Hx. clear - Hx. cbn [length] in Hx. lia.
Qed.

Lemma nxs_mbyte_present : forall H (m : word -> option byte) a,
  apresent H m a -> exists b, mbyte SEGS (mrestrict H m) a = Some b.
Proof. intros H m a [Hh [b Hb]]. exists b. unfold mbyte, mrestrict. rewrite Hh, Hb. reflexivity. Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* The call site of a fread into the caller's buffer, from a state of this call's journal          *)
(* ---------------------------------------------------------------------------------------------- *)

Section f.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.

(* Every byte the call may write lies below the allocator's ceiling: the struct and the timestamp
   cell in the caller's side-stack frames, the buffer and the FILE in heap blocks. The body's own
   stack window lies above it. *)
Lemma nx_E_below : forall cx, nx_base SK B KS cx -> n_h cx <> 0 ->
  (forall a, nx_E cx a -> 4096 <= a < alloc_ceiling) /\
  alloc_ceiling + NX_STK <= spZ (n_regs cx) /\ spZ (n_regs cx) <= 2 ^ 47.
Proof.
intros cx HB Hh. pose proof HB as HB'. unfold nx_base in HB'.
destruct HB' as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & _ & _ & _ & Hps4 & _ & _
  & Hown & Hfa1 & Hfa2 & _ & _ & _ & _ & _ & Hbuf & Hts & Hstr & _).
pose proof HJ0 as (HAR0 & _ & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct (Hbuf Hh) as (Hinb & Hb4096 & _).
destruct (Hstr Hh) as (Hinh & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hinb) as (_ & _ & Hbc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hinh) as (_ & Hh4096 & Hhc & _).
pose proof (req_size_bounds (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as (_ & _ & Hrb & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Hhc.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ (n_cid cx) (n_pos cx) HAR0
  ltac:(rewrite Hfrs0; apply in_or_app; left; exact Hown)) as (_ & Hpc & _).
split; [|unfold NX_STK in *; lia].
intros a HE. unfold nx_E, nx_wrset in HE.
destruct HE as [HE | [HE | [(Hts0 & HE) | (_ & HE)]]].
- unfold PS_LEN in *. lia.
- lia.
- destruct (Hts Hh Hts0) as (_ & _ & Ht4 & _ & _ & (tc & tp & Htin & Ht1 & Ht2) & _).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ tc tp HAR0
    ltac:(rewrite Hfrs0; apply in_or_app; left; exact Htin)) as (_ & Htc & _). lia.
- unfold SRC_FILE_BLOCK in *. lia.
Qed.

(* The frame-pointer chain a callee of the body is handed (sp = the realigned stack pointer, s0 =
   the caller's sp): the body's own record (the caller's sp, ra, s0, saved at sp - 8 / sp - 16 by
   0x81824 / 0x81828) on top of the caller's chain, which nx_kept keeps. *)
Lemma nx_achain_call : forall cx fp k2 ly3 S3 W3 m md3,
  nx_base SK B KS cx -> n_h cx <> 0 ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 m md3 k2 ->
  nx_kept SEGS NX_STK B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 m (spZ (n_regs cx)) (nx_E cx) ->
  rdword (aview SEGS (w_H W3) m) (spZ (n_regs cx) - 8) = Some (raZ (n_regs cx)) ->
  rdword (aview SEGS (w_H W3) m) (spZ (n_regs cx) - 16) = Some (s0Z (n_regs cx)) ->
  achain ly3 (aview SEGS (w_H W3) m) (n_sp1 cx) (spZ (n_regs cx)) (nx_ch cx).
Proof.
intros cx fp k2 ly3 S3 W3 m md3 HB Hh HJ HK H8 H16.
destruct (nx_E_below cx HB Hh) as (HEb & Hspc & Hsp47).
unfold NX_STK, AFREAD_STK in Hspc.
pose proof HB as HB'. unfold nx_base in HB'.
destruct HB' as (HJ0 & _ & _ & Hra4 & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & Hch & _).
pose proof HJ0 as (_ & Hly0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & _ & _ & _ & Hhi47 & _ & _ & Htopst).
pose proof HJ as (_ & Hly & _).
assert (Etop : ly_top ly3 = ly_top (n_lyc cx)).
{ destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & E1 & _). destruct Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & E2 & _). congruence. }
assert (Etop0 : ly_top (n_lyc cx) = ly_top (n_ly cx)) by (destruct Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & E2 & _); exact E2).
assert (Ehi0 : ly_stk_hi (n_lyc cx) = ly_stk_hi (n_ly cx)) by (destruct Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E2 & _); exact E2).
assert (Hsp1 : n_sp1 cx + 224 <= spZ (n_regs cx)).
{ unfold n_sp1, nx_sp1, NX_MFRAME. pose proof (Z.mul_div_le (spZ (n_regs cx) - 224) 32 ltac:(lia)). lia. }
assert (Hal8 : spZ (n_regs cx) mod 8 = 0).
{ pose proof (Z_div_mod_eq_full (spZ (n_regs cx)) 16) as Ed. rewrite Hal16, Z.add_0_r in Ed.
  rewrite Ed. replace (16 * (spZ (n_regs cx) / 16)) with ((2 * (spZ (n_regs cx) / 16)) * 8) by lia.
  apply Z.mod_mul. lia. }
destruct HK as (K1 & _).
assert (Kab : forall a, spZ (n_regs cx) <= a < 2 ^ 64 -> aview SEGS (w_H W3) m a = aview SEGS (w_H (n_W cx)) (n_memc cx) a).
{ intros a Ha. apply K1; [lia | unfold NX_STK, AFREAD_STK; lia |]. intros HE. pose proof (HEb a HE). lia. }
apply (achain_ly_top (n_lyc cx)); [exact Etop|].
unfold nx_ch. destruct (Z.ltb_spec (spZ (n_regs cx) + 16) (ly_top (n_lyc cx))) as [Hlt|Hge].
- apply (achain_push (n_lyc cx) (aview SEGS (w_H (n_W cx)) (n_memc cx)) _ (spZ (n_regs cx)) (s0Z (n_regs cx))
    (raZ (n_regs cx)) (n_ch cx) (n_sp1 cx) Hch); [ lia | exact Kab | exact H8 | exact H16 | exact Hra4 | lia | exact Hal8 | lia | lia].
- left. split; [right; left; lia | reflexivity].
Qed.

(* What afread_spec asks of the call fread(buf, 1, n, h), 0 < n <= cap, made from a state of this
   call's journal with sp = the realigned stack pointer: the blocks, the stream's FILE right, and the
   destination (a live block: the caller's buffer). *)
Lemma nx_fread_buf_pre : forall cx fp k2 ly3 S3 W3 m md3 n,
  nx_base SK B KS cx -> n_h cx <> 0 ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 m md3 k2 ->
  ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx) ->
  0 < n <= n_cap cx ->
  In (n_h cx, SRC_FILE_BLOCK) (ablocks B ly3 S3) /\
  In (n_b cx, Z.of_nat (length (n_C cx))) (ablocks B ly3 S3) /\
  (n_b cx + Z.of_nat (length (n_C cx)) <= n_sp1 cx - AFREAD_STK \/ n_sp1 cx <= n_b cx) /\
  rread_wr_ok B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) ly3 S3 ((NX_CID, fp) :: n_own cx)
    AFREAD_STK (n_sp1 cx) (n_h cx) SRC_FILE_BLOCK /\
  0 <= n <= 2 ^ 26 /\
  rread_dest SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) ((NX_CID, fp) :: n_own cx) ly3 S3 W3 m
    AFREAD_STK (n_sp1 cx) (n_buf cx) n (n_h cx) (n_b cx) (Z.of_nat (length (n_C cx))).
Proof.
intros cx fp k2 ly3 S3 W3 m md3 n HB Hh HJ Hab Hn.
destruct (nx_E_below cx HB Hh) as (HEb & Hspc & Hsp47).
pose proof HB as HB'. unfold nx_base in HB'.
destruct HB' as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & _ & Hbuf & _ & Hstr & _).
destruct (Hbuf Hh) as (Hinb & Hb4096 & Hb63 & _ & _ & Hcap & Hbwr & _).
destruct (Hstr Hh) as (Hinh & HinC & _ & HlC & _ & Dbh & Dbb & _ & _ & _ & Hfph).
pose proof HJ as (HAR & Hly & _).
pose proof HJ0 as (HAR0 & Hly0 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HinbS : In (n_buf cx, nx_bufn (n_cap cx)) (ablocks B ly3 S3)) by (rewrite Hab; exact Hinb).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HinbS) as (_ & _ & Hbceil & Hbapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 HinC) as (_ & _ & HCceil & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hinh) as (_ & _ & Hhceil & _).
pose proof (req_size_bounds (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as (_ & _ & Hrb & _).
pose proof (req_size_bounds (Z.of_nat (length (n_C cx))) ltac:(lia)) as (_ & _ & HrC & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
assert (Hbn : n <= nx_bufn (n_cap cx)) by (unfold nx_bufn; lia).
assert (Hsp1 : spZ (n_regs cx) - 256 < n_sp1 cx <= spZ (n_regs cx) - 224).
{ unfold n_sp1, nx_sp1, NX_MFRAME. pose proof (Z.mul_div_le (spZ (n_regs cx) - 224) 32 ltac:(lia)).
  pose proof (Z_div_mod_eq_full (spZ (n_regs cx) - 224) 32). pose proof (Z.mod_pos_bound (spZ (n_regs cx) - 224) 32 ltac:(lia)). lia. }
unfold NX_STK, AFREAD_STK in *.
assert (EFA : forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p).
{ intros c p. rewrite (frame_addr_layout_le _ _ _ Hly c p). symmetry. exact (frame_addr_layout_le _ _ _ Hly0 c p). }
split; [rewrite Hab; exact Hinh|].
split; [rewrite Hab; exact HinC|].
split; [left; lia|].
split.
{ intros a Ha. split; [|unfold SRC_FILE_BLOCK in Ha; lia].
  assert (HfpA : inFP (asource_fp (n_h cx)) a)
    by (unfold asource_fp; exists (n_h cx, n_h cx + SRC_FILE_BLOCK); split; [left; reflexivity | cbn [fst snd]; lia]).
  destruct (Hfph a HfpA) as [Hx | Hx].
  - right. left. split; [exact Hx|]. exists (n_h cx), SRC_FILE_BLOCK. split; [rewrite Hab; exact Hinh|].
    change (req_size SRC_FILE_BLOCK) with 1304. unfold SRC_FILE_BLOCK in Ha. lia.
  - apply awr_byte_of_tmp. rewrite Hab. exact Hx. }
split; [unfold NX_CAP_MAX in Hcap; lia|].
unfold rread_dest.
split; [destruct Dbh; [left | right]; lia|].
split; [destruct Dbb; [left | right]; lia|].
split; [lia|].
split; [unfold in_app, amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia|].
split; [right; right; exists (n_buf cx), (nx_bufn (n_cap cx)); split; [exact HinbS | lia]|].
split.
{ intros a Ha. split; [|lia].
  destruct (Hbwr a ltac:(lia)) as [Haw _].
  eapply awr_byte_weaken; [| | | exact Haw].
  - intros x Hx. rewrite Hab. exact Hx.
  - intros x Hx. right. exact Hx.
  - exact EFA. }
split; [apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR HinbS); lia|].
intros Hn0. apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR HinbS); lia.
Qed.

(* After the call: the middle state's memory part from the state at the call (W3, m) to the state
   after it (W2, m2), given what afread_spec's post keeps (rread_kept, the shadow band) and the
   bytes it read (R, j of them, at the head of the buffer). *)
Lemma nx_fread_buf_post : forall cx fp k2 ly3 S3 W3 m md3 W2 m2 md2 n j ol vt vid tv R,
  nx_base SK B KS cx -> n_h cx <> 0 ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 m md3 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx) ->
  0 < n <= n_cap cx ->
  rread_kept SEGS B AFREAD_STK ly3 S3 W3 m W2 m2 (n_sp1 cx) (rread_wrset (n_h cx) (n_buf cx) n) ->
  (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview SEGS (w_H W2) m2 s = aview SEGS (w_H W3) m s) ->
  AR SEGS B ly3 S3 W2 m2 md2 ->
  garr8 SEGS (rdW W2 m2) (n_buf cx) R -> Z.of_nat (length R) = j -> 0 <= j <= n ->
  nx_kept SEGS NX_STK B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 m (spZ (n_regs cx)) (nx_E cx) ->
  nx_ps_at SEGS (rdW W3 m) (n_ps cx) (n_h cx) (n_sw cx) ol vt vid (n_pad cx) ->
  range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (n_ps cx) PS_LEN ->
  (n_ts cx <> 0 ->
     val_mem SEGS (rdW W3 m) (n_ts cx) 8 tv /\ range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (n_ts cx) 8) ->
  nx_kept SEGS NX_STK B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W2 m2 (spZ (n_regs cx)) (nx_E cx) /\
  nx_ps_at SEGS (rdW W2 m2) (n_ps cx) (n_h cx) (n_sw cx) ol vt vid (n_pad cx) /\
  range_addressable (aview SEGS (w_H W2) m2) SHADOW_OFF (n_ps cx) PS_LEN /\
  (forall bj0, garr8 SEGS (rdW W3 m) (n_buf cx) bj0 -> length bj0 = length (n_bj cx) ->
     exists bj', garr8 SEGS (rdW W2 m2) (n_buf cx) bj' /\ length bj' = length (n_bj cx) /\
       firstn (Z.to_nat j) bj' = R /\ skipn (Z.to_nat n) bj' = skipn (Z.to_nat n) bj0) /\
  (n_ts cx <> 0 ->
     val_mem SEGS (rdW W2 m2) (n_ts cx) 8 tv /\ range_addressable (aview SEGS (w_H W2) m2) SHADOW_OFF (n_ts cx) 8).
Proof.
intros cx fp k2 ly3 S3 W3 m md3 W2 m2 md2 n j ol vt vid tv R HB Hh HJ HFR Hab Hn HK HSB HAR2 HR HlR Hj
  (O1 & O2 & O3 & O4 & O5 & O6) Hps Hpsra Hts.
destruct HK as (A1 & A2 & A3 & A4 & A5 & A6).
destruct (nx_E_below cx HB Hh) as (HEb & Hspc & Hsp47).
pose proof HB as HB'. unfold nx_base in HB'.
destruct HB' as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & _ & _ & Hps8 & Hps4 & Hps47 & Hpsam
  & Hown & Hfa1 & Hfa2 & _ & _ & _ & _ & _ & Hbuf & Htsb & Hstr & _).
destruct (Hbuf Hh) as (Hinb & Hb4096 & Hb63 & _ & Hlbj & Hcap & _ & Dbps).
destruct (Hstr Hh) as (Hinh & HinC & _ & HlC & _ & Dbh & Dbb & Dph & Dpb & Dts & _).
pose proof HJ as (HAR3 & Hly & _).
pose proof HJ0 as (HAR0 & Hly0 & _ & _ & _ & Hfrs0 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EFA : forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p).
{ intros c p. rewrite (frame_addr_layout_le _ _ _ Hly c p). symmetry. exact (frame_addr_layout_le _ _ _ Hly0 c p). }
assert (HFc : forall c p, In (c, p) (frames (n_Sc cx)) -> In (c, p) (frames S3)) by (intros c p H; rewrite HFR; right; exact H).
assert (HOc : forall c p, In (c, p) (n_own cx) -> In (c, p) (frames (n_Sc cx)))
  by (intros c p H; rewrite Hfrs0; apply in_or_app; left; exact H).
assert (Hsp1 : spZ (n_regs cx) - 256 < n_sp1 cx <= spZ (n_regs cx) - 224).
{ unfold n_sp1, nx_sp1, NX_MFRAME.
  pose proof (Z.mul_div_le (spZ (n_regs cx) - 224) 32 ltac:(clear; lia)) as M1.
  pose proof (Z_div_mod_eq_full (spZ (n_regs cx) - 224) 32) as M2.
  pose proof (Z.mod_pos_bound (spZ (n_regs cx) - 224) 32 ltac:(clear; lia)) as M3.
  revert M1 M2 M3. clear. intros. lia. }
assert (Hbn : n <= nx_bufn (n_cap cx)) by (unfold nx_bufn; revert Hn; clear; intros; lia).
assert (WE : forall a, rread_wrset (n_h cx) (n_buf cx) n a -> nx_E cx a).
{ intros a [Ha|Ha]; unfold nx_E, nx_wrset;
    [right; right; right; split; [exact Hh | exact Ha] | right; left; revert Ha Hbn; clear; intros; lia]. }
unfold NX_STK, AFREAD_STK in *.
(* the struct's and the timestamp cell's bytes: in the caller's frames, off the FILE and the buffer *)
assert (KF : forall c p x0 len, In (c, p) (n_own cx) -> frame_addr (n_lyc cx) c p <= x0 ->
  x0 + len <= frame_addr (n_lyc cx) c p + fs_frame_bytes c ->
  (x0 + len <= n_h cx \/ n_h cx + SRC_FILE_BLOCK <= x0) -> (n_buf cx + nx_bufn (n_cap cx) <= x0 \/ x0 + len <= n_buf cx) ->
  forall x, x0 <= x < x0 + len -> mbyte SEGS (rdW W2 m2) x = mbyte SEGS (rdW W3 m) x).
{ intros c p x0 len Hin H1 H2 D1 D2 x Hx. apply (mbyte_of_aview SEGS).
  assert (HRng : in_zr x (frame_rng (n_lyc cx) (c, p)) \/
               in_zr x (shadow_addr (frame_addr (n_lyc cx) c p), fs_frame_bytes c / 8)).
  { left. unfold in_zr, frame_rng. cbn [fst snd]. revert H1 H2 Hx. clear. intros. lia. }
  assert (HnW : ~ rread_wrset (n_h cx) (n_buf cx) n x).
  { unfold rread_wrset. intros [X|X].
    - revert X Hx D1. unfold SRC_FILE_BLOCK. clear. intros. lia.
    - revert X Hx D2 Hbn. clear. intros. lia. }
  apply (A4 c p x (HFc c p (HOc c p Hin))); [|exact HnW].
  unfold in_zr, frame_rng in HRng |- *. cbn [fst snd] in HRng |- *. rewrite !EFA. exact HRng. }
assert (KS0 : forall x, kLowMemEnd <= shadow_of_addr SHADOW_OFF x < kHighShadowEnd ->
  aview SEGS (w_H W2) m2 (shadow_of_addr SHADOW_OFF x) = aview SEGS (w_H W3) m (shadow_of_addr SHADOW_OFF x))
  by (intros x Hx; apply HSB; exact Hx).
split.
{ (* nx_kept *)
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw HnE. transitivity (aview SEGS (w_H W3) m a).
    + apply A1; [exact Ha | revert Hw Hsp1; clear; intros; lia | intros X; apply HnE; apply WE; exact X].
    + apply O1; [exact Ha | exact Hw | exact HnE].
  - intros b mm i Hin Hi HnE. transitivity (aview SEGS (w_H W3) m (b + i)).
    + apply (A2 b mm i); [rewrite Hab; exact Hin | exact Hi | intros X; apply HnE; apply WE; exact X].
    + apply (O2 b mm i Hin Hi HnE).
  - intros a Hi Hno He. transitivity (aview SEGS (w_H W3) m a); [apply A3; assumption | apply O3; assumption].
  - intros c p a Hin Hr HnE. transitivity (aview SEGS (w_H W3) m a).
    + apply (A4 c p a (HFc c p Hin)); [|intros X; apply HnE; apply WE; exact X].
      unfold in_zr, frame_rng in *. cbn [fst snd] in *. rewrite !EFA. exact Hr.
    + apply (O4 c p a Hin Hr HnE).
  - intros a Ha Hw Hp. apply A5; [exact Ha | revert Hw Hsp1; clear; intros; lia | exact (O5 a Ha Hw Hp)].
  - intros a Ha. destruct (Z_lt_le_dec a (n_sp1 cx - 8192)) as [Hlo|Hlo]; [|destruct (Z_lt_le_dec a (n_sp1 cx)) as [Hhi|Hhi]].
    + apply A5; [revert Ha Hspc Hsp1 Hsp47; clear; intros; lia | revert Hlo; clear; intros; lia | exact (O6 a Ha)].
    + apply A6. revert Hlo Hhi; clear; intros; lia.
    + apply A5; [revert Ha Hspc Hsp1 Hsp47; clear; intros; lia | revert Hhi; clear; intros; lia | exact (O6 a Ha)]. }
split.
{ apply (nxs_ps_at_frame (rdW W3 m)); [|exact Hps].
  intros x Hx. apply (KF (n_cid cx) (n_pos cx) (n_ps cx) PS_LEN Hown Hfa1 Hfa2 Dph Dbps x Hx). }
split.
{ apply (PcapSourceCloseSpec.ra_frame (aview SEGS (w_H W3) m)); [exact Hpsra|].
  intros x Hx. apply KS0. unfold shadow_of_addr, SHADOW_OFF, PS_LEN in *.
  assert (Hx8 : 0 <= x / 8 < 2 ^ 44)
    by (revert Hx Hps4 Hps47; unfold PS_LEN; clear; intros; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  revert Hx8; clear; unfold kLowMemEnd, kHighShadowEnd; intros; lia. }
split.
{ intros bj0 Hbj0 Hl0.
  pose (L := length (n_bj cx)).
  assert (HL : Z.of_nat L = nx_bufn (n_cap cx)) by exact Hlbj.
  assert (Hl0' : length bj0 = L) by exact Hl0.
  assert (Hnl : (Z.to_nat n <= L)%nat) by (revert HL Hbn Hn; clear; intros; lia).
  set (tail := skipn (Z.to_nat n) bj0).
  assert (Hlt : length tail = (L - Z.to_nat n)%nat) by (unfold tail; rewrite length_skipn, Hl0'; reflexivity).
  assert (Gt0 : garr8 SEGS (rdW W3 m) (n_buf cx + n) tail).
  { pose proof (YI01.garr8_sub SEGS (rdW W3 m) (n_buf cx) bj0 (Z.to_nat n) (L - Z.to_nat n) Hbj0) as G.
    rewrite firstn_all2 in G by (rewrite length_skipn, Hl0'; clear; lia).
    rewrite Z2Nat.id in G by (revert Hn; clear; intros; lia). exact G. }
  assert (HinbS : In (n_buf cx, nx_bufn (n_cap cx)) (ablocks B ly3 S3)) by (rewrite Hab; exact Hinb).
  assert (Hrb2 : req_size (nx_bufn (n_cap cx)) = nx_bufn (n_cap cx))
    by (unfold req_size, nx_bufn; destruct (Z.max (n_cap cx) 1 =? 0) eqn:Hz; [apply Z.eqb_eq in Hz; revert Hz; clear; lia | reflexivity]).
  assert (Htl : forall x, n_buf cx + n <= x < n_buf cx + Z.of_nat L ->
    mbyte SEGS (rdW W2 m2) x = mbyte SEGS (rdW W3 m) x).
  { intros x Hx. apply (mbyte_of_aview SEGS).
    replace x with (n_buf cx + (x - n_buf cx)) by (revert Hx; clear; intros; lia).
    apply (A2 (n_buf cx) (nx_bufn (n_cap cx)) (x - n_buf cx) HinbS);
      [rewrite Hrb2; revert Hx HL Hn; clear; intros; lia|].
    unfold rread_wrset. intros [X|X].
    - revert X Hx Dbh HL Hbn Hn. unfold SRC_FILE_BLOCK. clear. intros. lia.
    - revert X Hx Hn. clear. intros. lia. }
  assert (Gt : garr8 SEGS (rdW W2 m2) (n_buf cx + n) tail).
  { apply (garr8_frame SEGS (rdW W3 m) (rdW W2 m2) _ _ Gt0). intros x Hx. rewrite Hlt in Hx.
    apply Htl. revert Hx Hnl Hn; clear; intros.
    rewrite Nat2Z.inj_sub in Hx by exact Hnl. rewrite Z2Nat.id in Hx by lia. lia. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 HinbS) as (_ & _ & _ & _ & Hbpres & _).
  destruct (YI13.garr8_of_readable SEGS (rdW W2 m2) (n_buf cx + j) (Z.to_nat (n - j))) as (M & HlM & GM).
  { intros a Ha. rewrite Z2Nat.id in Ha by (revert Hj; clear; intros; lia).
    apply nxs_mbyte_present.
    assert (Hin2 : n_buf cx <= a < n_buf cx + req_size (nx_bufn (n_cap cx)))
      by (rewrite Hrb2; revert Ha Hj Hn HL Hbn; clear; intros; lia).
    exact (proj1 (Hbpres a Hin2)). }
  exists (R ++ M ++ tail).
  assert (HlR' : length R = Z.to_nat j) by (revert HlR Hj; clear; intros; lia).
  split.
  { apply garr8_app. split; [exact HR|]. apply garr8_app. split.
    - rewrite HlR'. rewrite Z2Nat.id by (revert Hj; clear; intros; lia). exact GM.
    - rewrite HlR', HlM.
      replace (n_buf cx + Z.of_nat (Z.to_nat j) + Z.of_nat (Z.to_nat (n - j))) with (n_buf cx + n)
        by (revert Hj; clear; intros; lia).
      exact Gt. }
  split; [rewrite !length_app, HlR', HlM, Hlt; revert Hnl Hj Hn; clear; intros; lia|].
  split; [rewrite firstn_app, HlR', Nat.sub_diag, firstn_O, app_nil_r; apply firstn_all2; rewrite HlR'; clear; lia|].
  rewrite skipn_app, HlR'. rewrite skipn_all2 by (rewrite HlR'; revert Hj Hn; clear; intros; lia). cbn [app].
  rewrite skipn_app, HlM. rewrite skipn_all2 by (rewrite HlM; revert Hj Hn; clear; intros; lia). cbn [app].
  replace (Z.to_nat n - Z.to_nat j - Z.to_nat (n - j))%nat with 0%nat by (revert Hj Hn; clear; intros; lia).
  reflexivity. }
intros Hts0. destruct (Hts Hts0) as (Hv & Hra).
destruct (Htsb Hh Hts0) as (_ & Hts8 & Hts4 & Hts47 & _ & (tc & tp & Htin & Ht1 & Ht2) & _ & _ & _ & Dbt).
destruct (Dts Hts0) as (Dth & _).
split.
- apply (PcapSourceCloseSpec.vm_frame_segs _ (rdW W3 m)); [|exact Hv].
  intros x Hx. apply (KF tc tp (n_ts cx) 8 Htin Ht1 Ht2 Dth Dbt x). revert Hx; clear; intros; lia.
- apply (PcapSourceCloseSpec.ra_frame (aview SEGS (w_H W3) m)); [exact Hra|].
  intros x Hx. apply KS0. unfold shadow_of_addr, SHADOW_OFF in *.
  assert (Hx8 : 0 <= x / 8 < 2 ^ 44)
    by (revert Hx Hts4 Hts47; clear; intros; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  revert Hx8; clear; unfold kLowMemEnd, kHighShadowEnd; intros; lia.
Qed.

End f.

End b.
End a.
