(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths, module names and numbers changed; 1300 of its 1492 lines of code are new or changed and 739 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: ported from a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v (ge_seat / ge_land) to libreac/fuzz_pcap's pcap_source_next: the region list, the atoms, the spill slots and the frame (class 0, its header and flag word) are this function's; nx_land0 / nx_land, the struct's region, the shadow entry, the first-seat environment and the kept-relation step are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapSourceNextSeat.v, with its module paths and module names changed; 932 of its 1007 lines of code are new or changed and 1417 lines of the source are left out. *)
(* pcap_source_next (fuzz_pcap.asan-ubsan 0x815b8, listing offset AF_pcap_source_next = 0xe30) on the ASan+UBSan
   build of libreac v1.9.0: the phase from the head of the record loop NP_loop (0x8174c) to the return of the fread
   of the 16-byte record header, NP_hd_ra (0x81770). The lib/A twin is lib/A/Prog/PcapSourceNextHdrA.v;
   this file walks lib/B's image, with lib/B's registers and cut pcs (lib/B/Prog/PcapSourceNextDefs.v).

   Every number is read from the pinned fuzz_pcap.asan-ubsan image
   (sha256 9e66f771f22af67a...; symbols from its unstripped twin, capstone 5; the annotated disassembly
   nxb-next.dis (sha256 7213b94e2690; internal record)). The nine slots of the phase:
     0x8174c sb zero,4(s9)    0x81750 sb zero,5(s9)   the header `ph` (F+32..F+47) in scope
     0x81754 lbu a0,0(s10)    0x81758 bnez a0,0x81bf8 the shadow check of ps (an 8-byte load)
     0x8175c ld a3,0(s5)                              a3 := ps->f = h
     0x81760 addi a1,zero,1   0x81764 addi a2,zero,0x10   0x81768 mv a0,s3 (= F + 32)
     0x8176c jal __interceptor_trampoline_fread       fread(F + 32, 1, 16, h), returns to 0x81770
   The branch at 0x81758 goes to the error path 0x81bf8 (`mv a0,s5; jal __asan_report_load8`). It is not taken:
   the shadow byte of ps is 0, because the caller's ps is addressable for 8 bytes and 8-aligned (an aligned
   granule whose last byte is addressable has shadow 0, YG0v.saddr_ok); the walk proves this from the premises of
   nx_mid, no stack constant budgets that path.

   The fread is the wrapper's contract afread_spec (lib/A/Stdio/PFreadISpec.v) at the site whose return address is
   NP_hd_ra. That statement is in the CALLER-JOURNAL form: it extends this call's own journal instead of starting a
   fresh one, so the destination F + 32 -- which lies in the class-0 frame THIS call took -- is covered by the
   premise rread_dest's rread_at / rread_wr_ok (PFreadM.v; the frame arm), and no frame-aware journal composition is
   needed here. *)
(* Modified by Theorem Labs, 2026-10: hdA_vm_frame / hdA_src_frame / hdA_ra_frame (a renamed copy of
   lib/B/Prog/PcapSourceClose.v's vm_frame / asource_at_frame / ra_frame) deleted; their uses name
   lib/A/Prog/PcapSourceCloseSpec.v's vm_frame_segs / asource_at_frame_segs / ra_frame. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YE01 YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h YC85 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadM PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextKit.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextHdrBDefs.
(* The image-free frame lemmas, Required without Import and used qualified. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceCloseSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Image-free facts about the frame's shadow                                                        *)
(* ---------------------------------------------------------------------------------------------- *)

(* The frame's class: 64 bytes, 8 shadow bytes. *)
Lemma hdA_fsb : fs_frame_bytes NX_CID = 64.
Proof. vm_compute. reflexivity. Qed.

(* An 8-aligned granule all of whose bytes are addressable has shadow byte 0: a partial granule's shadow byte s
   satisfies x mod 8 < s for every addressable x (YG0v.saddr_ok), which the last byte a + 7 refutes. *)
Lemma hdA_gran0 : forall (rd : Z -> option Z) a, a mod 8 = 0 ->
  range_addressable rd SHADOW_OFF a 8 -> rd (shadow_of_addr SHADOW_OFF a) = Some 0.
Proof.
intros rd a Ha HR. destruct (HR (a + 7) ltac:(lia)) as (s & Hs & Hok).
pose proof (Z.div_mod a 8 ltac:(lia)) as Hdm.
rewrite (shadow_of_addr_same_granule SHADOW_OFF a (a + 7) ltac:(lia)) in Hs.
destruct Hok as [-> | (H1 & H2)]; [exact Hs|].
assert (E : (a + 7) mod 8 = 7) by (rewrite Zplus_mod, Ha; reflexivity).
lia.
Qed.

(* With the shadow bytes 4 and 5 of an 8-aligned frame F zero (0x8174c, 0x81750), the 16 bytes F + 32 .. F + 47
   are addressable: they are the granules 4 and 5. *)
Lemma hdA_ph_ra : forall (rd : Z -> option Z) F, F mod 8 = 0 ->
  rd (shadow_of_addr SHADOW_OFF F + 4) = Some 0 -> rd (shadow_of_addr SHADOW_OFF F + 5) = Some 0 ->
  range_addressable rd SHADOW_OFF (F + NO_PH) NX_PH_LEN.
Proof.
intros rd F HF H4 H5 x Hx. unfold NO_PH, NX_PH_LEN in Hx. exists 0. split; [|left; reflexivity].
replace x with (F + (x - F)) by lia. rewrite shadow_of_addr_aligned_off by exact HF.
destruct (Z_lt_dec x (F + 40)) as [Hl|Hl].
- assert (Hq : (x - F) / 8 = 4) by (symmetry; apply Z.div_unique with (r := x - F - 32); lia).
  rewrite Hq. exact H4.
- assert (Hq : (x - F) / 8 = 5) by (symmetry; apply Z.div_unique with (r := x - F - 40); lia).
  rewrite Hq. exact H5.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The symbolic state of the phase                                                                  *)
(* ---------------------------------------------------------------------------------------------- *)

(* A 64-aligned region and its eight-to-one shadow: where a byte's shadow byte lies, and that the shadows of two
   apart 64-aligned regions are apart (every frame of a state is 64-aligned, PcapFrame.frame_al64). *)
Lemma hdA_div64 : forall f, f mod 64 = 0 -> f = 64 * (f / 64) /\ f / 8 = 8 * (f / 64).
Proof.
intros f Hf. pose proof (Z.div_mod f 64 ltac:(lia)) as D. rewrite Hf, Z.add_0_r in D.
split; [exact D|]. rewrite D at 1. replace (64 * (f / 64)) with ((8 * (f / 64)) * 8) by lia.
apply Z.div_mul. lia.
Qed.

Lemma hdA_sh_in : forall f n x, f mod 64 = 0 -> n mod 64 = 0 -> 0 <= n -> f <= x < f + n ->
  shadow_addr f <= shadow_of_addr SHADOW_OFF x < shadow_addr f + n / 8.
Proof.
intros f n x Hf Hn Hn0 Hx.
destruct (hdA_div64 f Hf) as (Ef & Ef8). destruct (hdA_div64 n Hn) as (En & En8).
unfold shadow_addr, shadow_of_addr. rewrite Ef8.
assert (Hlo : 8 * (f / 64) <= x / 8).
{ replace (8 * (f / 64)) with ((64 * (f / 64)) / 8)
    by (replace (64 * (f / 64)) with ((8 * (f / 64)) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
  apply Z.div_le_mono; lia. }
assert (Hhi : x / 8 < 8 * (f / 64) + 8 * (n / 64)).
{ apply Z.div_lt_upper_bound; lia. }
rewrite En8. lia.
Qed.

Lemma hdA_shr_disj : forall f n g m, f mod 64 = 0 -> n mod 64 = 0 -> 0 <= n ->
  g mod 64 = 0 -> m mod 64 = 0 -> 0 <= m -> (f + n <= g \/ g + m <= f) ->
  shadow_addr f + n / 8 <= shadow_addr g \/ shadow_addr g + m / 8 <= shadow_addr f.
Proof.
intros f n g m Hf Hn Hn0 Hg Hm Hm0 Hd.
destruct (hdA_div64 f Hf) as (Ef & Ef8). destruct (hdA_div64 n Hn) as (En & En8).
destruct (hdA_div64 g Hg) as (Eg & Eg8). destruct (hdA_div64 m Hm) as (Em & Em8).
unfold shadow_addr. rewrite Ef8, Eg8, En8, Em8. lia.
Qed.

(* Three regions are enough for these nine slots: the two shadow bytes of `ph` that 0x8174c / 0x81750 write
   (base s9 = x25, the frame's shadow address), the shadow byte of ps that 0x81754 reads (base s10 = x26), and the
   FILE pointer ps->f that 0x8175c loads (base s5 = x21, the atom 32 = h as its value). The atoms 0..31 are the
   registers at the loop head and 32 is h (hdA_extra). *)
Definition hdA_regions : YP09.smem :=
  [ YP09.mkRegion (Some 25%nat) 4 6 4 6 [];
    YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
    YP09.mkRegion (Some 21%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))] ].
Definition hdA_ss : sstate := mkSS NP_loop sr_atoms hdA_regions None (mkFacts [] [] []).
Definition hdA_extra (h : Z) : list word := [w64 h].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation VAL := (@pa_val _ pcap_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* A byte the walk reads as a chunk: aview gives the value, the region wants the byte. *)
Lemma hdA_mbyte : forall (H : word -> bool) (m : word -> option byte) a v, 0 <= v < 256 ->
  aview SEGS H m a = Some v -> mbyte SEGS (mrestrict H m) a = Some (Z_to_bv 8 v).
Proof.
intros H m a v Hv Ha. unfold aview, option_map in Ha.
destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:E; [|discriminate].
injection Ha as Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. rewrite <- Hb. symmetry. apply Z.mod_small.
pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr. lia.
Qed.

(* The value of a byte the walk pinned as a chunk. *)
Lemma hdA_aview_byte : forall (H : word -> bool) (m : word -> option byte) a b,
  mbyte SEGS (mrestrict H m) a = Some b -> aview SEGS H m a = Some (bv_unsigned b).
Proof. intros H m a b Hb. unfold aview. rewrite Hb. reflexivity. Qed.

(* A one-byte chunk whose value is the literal 0. *)
Lemma hdA_byte0 : forall (E : env) (H : word -> bool) (m : word -> option byte) n b cs lo hi wlo whi od,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 (SLit 0))) cs ->
  aview SEGS H m (b + od) = Some 0.
Proof.
intros E H m n b cs lo hi wlo whi od HR Hn Hin.
pose proof (field_of_region E (mrestrict H m) n b cs lo hi wlo whi od 1%N (SLit 0) 0 HR Hn Hin
  ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
pose proof (HV 0%nat ltac:(cbn; lia)) as H0. cbn [Z.of_nat YO0f.le_byte] in H0.
rewrite Z.add_0_r in H0.
rewrite (hdA_aview_byte H m (b + od) _ H0). reflexivity.
Qed.

(* A register of the symbolic state whose value is an atom, a literal, or a code pointer. *)
Lemma hdA_reg_atom : forall (E : env) ss (H : word -> bool) ms (r : bv 5) n v,
  st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w64 v ->
  0 <= v < 2 ^ 64 -> getr (ms_regs ms) r = w64 v.
Proof.
intros E ss H ms r n v HS Hsr Hn Hv. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hsr.
cbn [sv_denot]. rewrite Hn. unfold w64. rewrite unsigned_lit_small by exact Hv.
rewrite Z.add_0_r. reflexivity.
Qed.

Lemma hdA_reg_lit : forall (E : env) ss (H : word -> bool) ms (r : bv 5) v,
  st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit v -> getr (ms_regs ms) r = Z_to_bv 64 v.
Proof.
intros E ss H ms r v HS Hsr. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hsr. reflexivity.
Qed.

(* A register the run did not write: its atom is its own entry register. *)
Lemma hdA_reg_same : forall ss (H : word -> bool) ms (r : bv 5) (n : nat) (regs0 : bvmap 5 word) extra,
  st_ok SEGS (Eimg (Ereg regs0 extra)) ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 ->
  Z.of_nat n = bv_unsigned r -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros ss H ms r n regs0 extra HS Hsr Hn.
rewrite (st_ok_restrict_reg SEGS H _ ss ms r HS), Hsr. cbn [sv_denot].
rewrite (ew_Eimg_Ereg_nat regs0 extra n r Hn), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma hdA_reg_pc : forall (E : env) ss (H : word -> bool) ms (r : bv 5) k,
  img_env VAL A_LIM E -> st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff A_TEXT k ->
  getr (ms_regs ms) r = w64 (BASE + k).
Proof.
intros E ss H ms r k HEI HS Hsr. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hsr.
exact (codeptr_val E k HEI).
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.

(* ---- the facts of one phase state ---- *)

Section d.
Variable cx : ncx.
Variables fp k2 : Z.
Variable ly3 : alayout.
Variable S3 : astate.
Variable W3 : world SEGS.
Variable ms3 : machine_state.
Variable md3 : Model.
Hypothesis HB : nx_base SK B KS cx.
Hypothesis HJ : ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx)
  (n_md0 cx) ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2.
Hypothesis HFR : frames S3 = (NX_CID, fp) :: frames (n_Sc cx).

Lemma hdA_AR3 : AR SEGS B ly3 S3 W3 (ms_mem ms3) md3.
Proof. exact (proj1 HJ). Qed.

(* The layouts of the caller's start, of the caller's call state and of this state place the frames alike. *)
Lemma hdA_fa : forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p.
Proof.
intros c p. pose proof HJ as (_ & Hly & _). pose proof (proj1 HB) as (_ & Hlyc & _).
unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _).
destruct Hlyc as (_ & _ & _ & _ & _ & EFc & _). rewrite EF, EFc. reflexivity.
Qed.

Lemma hdA_fin : In (NX_CID, fp) (frames S3).
Proof. rewrite HFR. left. reflexivity. Qed.

(* This call's own frame: where it lies. *)
Lemma hdA_F : 4096 <= nF cx fp /\ nF cx fp + 64 <= alloc_ceiling /\ nF cx fp mod 64 = 0 /\
  in_app (nF cx fp) 64.
Proof.
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 NX_CID fp hdA_AR3 hdA_fin)
  as (H1 & H2 & H3).
pose proof (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 NX_CID fp hdA_AR3 hdA_fin) as (H64 & _ & _).
rewrite hdA_fsb in H2, H3. unfold nF. rewrite hdA_fa in H1, H2, H3, H64.
split; [exact H1|]. split; [exact H2|]. split; [exact H64 | exact H3].
Qed.

(* The caller's struct: its frame is one of the caller's own. *)
Lemma hdA_psf : In (n_cid cx, n_pos cx) (frames (n_Sc cx)) /\
  frame_addr ly3 (n_cid cx) (n_pos cx) <= n_ps cx /\
  n_ps cx + PS_LEN <= frame_addr ly3 (n_cid cx) (n_pos cx) + fs_frame_bytes (n_cid cx).
Proof.
pose proof HB as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  Hown & Hle1 & Hle2 & _).
pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
split; [rewrite Hfrs; apply in_or_app; left; exact Hown|].
rewrite hdA_fa. split; [exact Hle1 | exact Hle2].
Qed.

Lemma hdA_ps : 4096 <= n_ps cx /\ n_ps cx + PS_LEN <= alloc_ceiling /\ in_app (n_ps cx) PS_LEN.
Proof.
destruct hdA_psf as (Hin & Hle1 & Hle2).
assert (Hin3 : In (n_cid cx, n_pos cx) (frames S3)) by (rewrite HFR; right; exact Hin).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (n_cid cx) (n_pos cx) hdA_AR3 Hin3)
  as (H1 & H2 & H3).
split; [lia|]. split; [lia|]. eapply in_app_sub; [exact H3 | lia | unfold PS_LEN; lia | lia].
Qed.

(* This call's frame and the caller's struct are apart (distinct frames of one state). *)
Lemma hdA_sep : n_ps cx + PS_LEN <= nF cx fp \/ nF cx fp + 64 <= n_ps cx.
Proof.
destruct hdA_psf as (Hin & Hle1 & Hle2).
destruct (in_split _ _ Hin) as (l1 & l2 & El).
assert (Hd : zdisjoint (frame_rng ly3 (NX_CID, fp)) (frame_rng ly3 (n_cid cx, n_pos cx))).
{ eapply (sep_frames_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ [] l1 l2 hdA_AR3).
  rewrite HFR, El. reflexivity. }
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite hdA_fsb in Hd.
pose proof (fs_frame_bytes_nonneg (n_cid cx)) as Hnn. unfold nF. rewrite <- (hdA_fa NX_CID fp). lia.
Qed.

(* The frame's shadow bytes and the shadow byte of ps are apart: the granules of `ph` (F + 32 .. F + 47) are the
   frame's shadow bytes 4 and 5, and ps lies outside the frame (hdA_sep). *)
Lemma hdA_shsep :
  shadow_of_addr SHADOW_OFF (n_ps cx) + 1 <= nSH cx fp + 4 \/
  nSH cx fp + 6 <= shadow_of_addr SHADOW_OFF (n_ps cx).
Proof.
destruct hdA_F as (HF0 & HFc & HF64 & _).
pose proof hdA_sep as Hsep.
set (t := nF cx fp / 64) in *.
assert (EF : nF cx fp = 64 * t) by (subst t; pose proof (Z.div_mod (nF cx fp) 64 ltac:(lia)); lia).
assert (E8 : nF cx fp / 8 = 8 * t)
  by (rewrite EF; replace (64 * t) with ((8 * t) * 8) by lia; apply Z.div_mul; lia).
unfold nSH, shadow_of_addr in *. rewrite E8.
destruct Hsep as [Hs | Hs].
- left.
  assert (Hd : n_ps cx / 8 <= 8 * t - 3).
  { replace (8 * t - 3) with ((64 * t - 24) / 8)
      by (replace (64 * t - 24) with ((8 * t - 3) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    apply Z.div_le_mono; [lia | unfold PS_LEN in Hs; lia]. }
  lia.
- right.
  assert (Hd : 8 * t + 8 <= n_ps cx / 8).
  { replace (8 * t + 8) with ((64 * t + 64) / 8)
      by (replace (64 * t + 64) with ((8 * t + 8) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    apply Z.div_le_mono; lia. }
  lia.
Qed.

(* ---- the seat: the symbolic state of the loop head ---- *)

#[local] Abbreviation EE := (Eimg (Ereg (ms_regs ms3) (hdA_extra (n_h cx)))).

Lemma hdA_seat : forall q lh,
  nx_loop_inv B MT KS cx fp q lh k2 ly3 S3 W3 ms3 md3 ->
  st_ok_pi SEGS VAL EE hdA_ss (restrict (w_H W3) ms3) /\
  awr_ok EE hdA_regions (n_STK cx) (n_sp0 cx) (n_FP cx) (ablocks B (n_ly cx) (n_S cx))
    (ablocks B ly3 S3) ly3 ((NX_CID, fp) :: n_own cx).
Proof.
intros q lh HL.
destruct HL as (HM & R19 & R20 & HCH).
destruct HM as (HBD & R21 & R23 & R26 & R27 & HJBK & HKEPT & HEsub & Hh0 & HPS & HRA & HSRC & Hqr & HBJ & HTS).
destruct HBD as (HB0 & HSLOTS).
destruct HB0 as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HREGS & HSAVED & HHDR & HFLW & HSHA & HSHLEN & R25 & HFK).
pose proof hdA_F as (HF0 & HFc & HF64 & HFapp).
pose proof hdA_ps as (HP0 & HPc & HPapp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HF8 : nF cx fp mod 8 = 0)
  by (pose proof (Z.div_mod (nF cx fp) 64 ltac:(lia)) as D; rewrite HF64, Z.add_0_r in D;
      rewrite D; replace (64 * (nF cx fp / 64)) with ((8 * (nF cx fp / 64)) * 8) by lia;
      apply Z.mod_mul; lia).
assert (HPS8 : n_ps cx mod 8 = 0)
  by (pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _); exact H).
assert (ESH : nSH cx fp = shadow_addr (nF cx fp)) by reflexivity.
assert (ESP : shadow_of_addr SHADOW_OFF (n_ps cx) = shadow_addr (n_ps cx)) by reflexivity.
pose proof (shadow_addr_bounds (nF cx fp) ltac:(lia)) as HSB1.
pose proof (shadow_addr_bounds (nF cx fp + 64) ltac:(lia)) as HSB2.
pose proof (shadow_addr_bounds (n_ps cx) ltac:(unfold PS_LEN in *; lia)) as HSB3.
pose proof (shadow_addr_bounds (n_ps cx + PS_LEN) ltac:(unfold PS_LEN in *; lia)) as HSB4.
assert (ESH8 : shadow_addr (nF cx fp + 64) = nSH cx fp + 8).
{ unfold nSH. change (shadow_addr (nF cx fp + 64)) with (shadow_of_addr SHADOW_OFF (nF cx fp + 64)).
  replace (nF cx fp + 64) with (nF cx fp + 8 * 8) by lia. apply shadow_of_addr_add8. }
assert (ESP3 : shadow_addr (n_ps cx + PS_LEN) = shadow_of_addr SHADOW_OFF (n_ps cx) + 3).
{ change (shadow_addr (n_ps cx + PS_LEN)) with (shadow_of_addr SHADOW_OFF (n_ps cx + PS_LEN)).
  replace (n_ps cx + PS_LEN) with (n_ps cx + 8 * 3) by (unfold PS_LEN; lia).
  apply shadow_of_addr_add8. }
assert (E21 : ew EE 21 = w64 (n_ps cx))
  by (rewrite (ew_Eimg_Ereg_nat (ms_regs ms3) _ 21%nat (21%bv : bv 5) ltac:(vm_compute; reflexivity)); exact R21).
assert (E25 : ew EE 25 = w64 (nSH cx fp))
  by (rewrite (ew_Eimg_Ereg_nat (ms_regs ms3) _ 25%nat (25%bv : bv 5) ltac:(vm_compute; reflexivity)); exact R25).
assert (E26 : ew EE 26 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx)))
  by (rewrite (ew_Eimg_Ereg_nat (ms_regs ms3) _ 26%nat (26%bv : bv 5) ltac:(vm_compute; reflexivity)); exact R26).
assert (E32 : ew EE 32 = w64 (n_h cx)).
{ rewrite Eimg_low by (unfold A_TEXT; lia).
  replace 32%nat with (32 + 0)%nat by lia. rewrite ew_Ereg_extra. reflexivity. }
assert (Hh64 : 0 <= n_h cx < 2 ^ 64)
  by (pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _); exact H).
assert (U21 : bv_unsigned (ew EE 21) = n_ps cx)
  by (rewrite E21; apply unsigned_lit_small; unfold PS_LEN in *; lia).
assert (U25 : bv_unsigned (ew EE 25) = nSH cx fp)
  by (rewrite E25; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew EE 26) = shadow_of_addr SHADOW_OFF (n_ps cx))
  by (rewrite E26; apply unsigned_lit_small; rewrite ESP; lia).
assert (BV21 : base_val EE (Some 21%nat) = n_ps cx) by exact U21.
assert (BV25 : base_val EE (Some 25%nat) = nSH cx fp) by exact U25.
assert (BV26 : base_val EE (Some 26%nat) = shadow_of_addr SHADOW_OFF (n_ps cx)) by exact U26.
assert (HZ : aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF (n_ps cx)) = Some 0).
{ apply (hdA_gran0 _ (n_ps cx) HPS8).
  eapply range_addressable_sub; [exact HRA | lia | unfold PS_LEN; lia]. }
assert (Hms3 : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + NP_loop)) (ms_mem ms3) (seg_rom SEGS)).
{ clear - Hpc Hresv Hsvc Hrom Hfregs Hfcsr.
  destruct ms3 as [rg fr pcv svp rv fc mm rm];
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity. }
split.
- replace (restrict (w_H W3) ms3)
    with (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + NP_loop)) (ms_mem ms3) (seg_rom SEGS)))
    by (rewrite <- Hms3; reflexivity).
  rewrite restrict_mkst_fx. unfold hdA_ss. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold hdA_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite BV25. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS).
      refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (nSH cx fp + o) HJ _)).
      apply awr_byte_own_head_shadow. rewrite hdA_fa.
      change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp).
      rewrite <- ESH, hdA_fsb. change (64 / 8) with 8. lia.
    * rewrite BV26. split; [rewrite ESP; lia|]. split; [rewrite ESP; lia|].
      split; [intros o Ho; exfalso; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS EE _ (shadow_of_addr SHADOW_OFF (n_ps cx)) 0 1%N (SLit 0) 0);
        [reflexivity | cbn; lia | cbn; lia |].
      intros k Hk. assert (Hk0 : k = 0%nat) by lia. subst k. cbn [Z.of_nat le_byte].
      rewrite !Z.add_0_r. exact (hdA_mbyte (w_H W3) (ms_mem ms3) _ 0 ltac:(lia) HZ).
    * rewrite BV21. split; [lia|]. split; [unfold PS_LEN in *; lia|].
      split; [intros o Ho; exfalso; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS EE _ (n_ps cx) 0 8%N (SOff 32 0) (n_h cx));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      rewrite Z.add_0_r. change (N.to_nat 8) with 8%nat.
      pose proof (proj1 HPS) as HPf. unfold PS_F_OFF in HPf. rewrite Z.add_0_r in HPf. exact HPf.
  + unfold hdA_regions. cbn [pairwise_disjoint all_disjoint].
    unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite BV21, BV25, BV26.
    pose proof hdA_shsep as Hsh. rewrite ESP in *.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighShadowEnd, PS_LEN in *.
    repeat split; lia.
  + unfold facts_ok. cbn [ss_facts f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I|]. split; exact I.
- unfold hdA_regions.
  eapply awr_ok_cons_gen with (n := 25%nat) (b := nSH cx fp); [reflexivity | exact U25 | |].
  + cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply awr_byte_own_head_shadow.
    rewrite hdA_fa. change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp).
    rewrite <- ESH, hdA_fsb. change (64 / 8) with 8. lia.
  + apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_nil.
Qed.

(* ---- the caller's bytes lie below the heap ceiling, the stack above it ---- *)

(* Every byte the call may write (nx_E: the struct, the buffer, the timestamp cell, the FILE block) lies under
   alloc_ceiling: the first and the third are in frames of the caller, the other two are live blocks. *)
Lemma hdA_notE : n_h cx <> 0 -> forall a, alloc_ceiling <= a -> ~ nx_E cx a.
Proof.
intros Hh0 a Ha HE.
pose proof HB as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbuf & Hts & Hstream & _).
pose proof (proj1 HJ0) as HARc.
pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
destruct hdA_ps as (_ & HPc & _).
destruct HE as [HE | [HE | [[Hts0 HE] | [Hh HE]]]].
- unfold PS_LEN in *. lia.
- destruct (Hbuf Hh0) as (Hin & _ & _ & _ & _ & _ & _ & _).
  destruct (al_blocks _ _ LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) _ _ HARc Hin)
    as (_ & _ & Hceil & _).
  pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as (_ & Hrq). lia.
- destruct (Hts Hh0 Hts0) as (_ & _ & _ & _ & _ & (tcid & tpos & Hin & Hle1 & Hle2) & _).
  assert (Hin' : In (tcid, tpos) (frames (n_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
  destruct (frames_bounds SEGS B LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) tcid tpos HARc Hin')
    as (_ & Hfc & _). lia.
- destruct (Hstream Hh0) as (Hin & _).
  destruct (al_blocks _ _ LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) _ _ HARc Hin)
    as (_ & _ & Hceil & _).
  pose proof (req_size_pos SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)) as (_ & Hrq). lia.
Qed.

(* ---- the frame chain this call hands to the fread wrapper ---- *)

(* The chain at the realigned stack pointer, with this call's own frame record on top of the caller's (nx_ch).
   The two words of the record are the saved ra and s0 of the machine frame (nsaved); the caller's chain is
   nx_base's, moved to this state by nx_kept (the body writes nothing at or above the caller's sp). *)
Lemma hdA_chain : forall (rd : Z -> option Z),
  n_h cx <> 0 ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> rd a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  nsaved cx W3 ms3 ->
  nx_kept SEGS NX_STK_B B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 (ms_mem ms3) (spZ (n_regs cx))
    (nx_E cx) ->
  achain ly3 rd (n_sp1 cx) (spZ (n_regs cx)) (nx_ch cx).
Proof.
intros rd Hh0 Hrd HSAVED HKEPT.
destruct HSAVED as (Hra_sv & Hsv). destruct HKEPT as (HK1 & _).
pose proof HB as (HJ0 & _ & _ & P4 & _ & _ & _ & _ & _ & _ & P11 & P12 & P13 & P14 & _).
pose proof HJ0 as (_ & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof HJ as (_ & Hly3 & _).
destruct Hstk0 as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
assert (Etop3 : ly_top ly3 = ly_top (n_ly cx))
  by (destruct Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & E & _); exact E).
assert (Etopc : ly_top (n_lyc cx) = ly_top (n_ly cx))
  by (destruct Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & E & _); exact E).
assert (HSP : alloc_ceiling + NX_STK_B <= spZ (n_regs cx)) by lia.
assert (HSPhi : spZ (n_regs cx) <= 2 ^ 47) by lia.
pose proof (NX_STK_B_frame (spZ (n_regs cx)) P11) as ((Hsp1lo & Hsp1hi) & Hsp1al).
assert (ESP1 : n_sp1 cx = nx_sp1 (spZ (n_regs cx))) by reflexivity.
assert (HSTKB : NX_STK_B = 272 + AFREAD_STK) by reflexivity.
assert (HAF : AFREAD_STK = 8192) by reflexivity.
unfold NX_MFRAME in Hsp1hi.
assert (Hw8 : rdword rd (spZ (n_regs cx) - 8) = Some (raZ (n_regs cx))).
{ rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) rd (spZ (n_regs cx) - 8)
    ltac:(intros k Hk; apply Hrd; lia)). exact Hra_sv. }
assert (Hw16 : rdword rd (spZ (n_regs cx) - 16) = Some (s0Z (n_regs cx))).
{ rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) rd (spZ (n_regs cx) - 16)
    ltac:(intros k Hk; apply Hrd; lia)).
  pose proof (Hsv 0 ltac:(lia)) as H0. cbn [Z.ltb Z.compare] in H0.
  replace (spZ (n_regs cx) - 16 - 8 * 0) with (spZ (n_regs cx) - 16) in H0 by lia.
  replace (Z_to_bv 5 (8 + 0)) with (8%bv : bv 5) in H0 by (apply bv_eq; vm_compute; reflexivity).
  exact H0. }
assert (HSP8 : spZ (n_regs cx) mod 8 = 0).
{ pose proof (Z.div_mod (spZ (n_regs cx)) 16 ltac:(lia)) as D. rewrite P11, Z.add_0_r in D.
  rewrite D. replace (16 * (spZ (n_regs cx) / 16)) with ((2 * (spZ (n_regs cx) / 16)) * 8) by lia.
  apply Z.mod_mul. lia. }
unfold nx_ch.
destruct (Z.ltb_spec (spZ (n_regs cx) + 16) (ly_top (n_lyc cx))) as [Hlt | Hge].
- right.
  split; [unfold n_sp1 in *; lia|].
  split; [lia|]. split; [exact HSP8|]. split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact HSP8|]. split; [exact Hw8|]. split; [exact Hw16|].
    split; [exact P4|].
    destruct (bad_next (spZ (n_regs cx)) (ly_top ly3) (s0Z (n_regs cx))) eqn:HBN.
    * destruct P14 as [(_ & Hnil) | (Q1 & Q2 & Q3 & Q4 & Q5)]; [exact Hnil|].
      exfalso. unfold bad_next in HBN.
      apply Bool.orb_true_elim in HBN as [HBN | HBN];
        [apply Bool.orb_true_elim in HBN as [HBN | HBN]|].
      -- apply Z.leb_le in HBN. lia.
      -- apply Z.leb_le in HBN. lia.
      -- apply Bool.negb_true_iff, Z.eqb_neq in HBN. lia.
    * destruct P14 as [(Hbad & Hnil) | (Q1 & Q2 & Q3 & Q4 & Q5)].
      -- exfalso. unfold bad_next in HBN.
         apply Bool.orb_false_elim in HBN as [HBN HBN3].
         apply Bool.orb_false_elim in HBN as [HBN1 HBN2].
         apply Z.leb_gt in HBN1. apply Z.leb_gt in HBN2.
         apply Bool.negb_false_iff, Z.eqb_eq in HBN3.
         destruct Hbad as [Hb | [Hb | Hb]]; lia.
      -- eapply (fpchain_ext (rdword (aview SEGS (w_H (n_W cx)) (n_memc cx))));
           [| lia | rewrite Etop3, <- Etopc; exact Q4].
         intros a Ha1 Ha2. apply rdword_ext. intros k Hk.
         rewrite (Hrd (a + k) ltac:(lia)). apply HK1; [lia | lia|].
         apply hdA_notE; [exact Hh0 | lia].
  + destruct P14 as [(_ & Hnil) | (Q1 & Q2 & Q3 & Q4 & Q5)].
    * rewrite Hnil. apply Forall_cons; [cbn; unfold n_sp1 in *; lia | apply Forall_nil].
    * apply Forall_cons; [cbn; unfold n_sp1 in *; lia|].
      eapply Forall_impl; [|exact Q5]. intros r Hr. cbn beta in Hr. unfold n_sp1 in *. lia.
- left. split; [right; left; lia | reflexivity].
Qed.

(* The facts of this state the phase uses, in one lemma (so that one application gives them all). *)
Lemma hdA_facts :
  (forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p) /\
  In (NX_CID, fp) (frames S3) /\
  (4096 <= nF cx fp /\ nF cx fp + 64 <= alloc_ceiling /\ nF cx fp mod 64 = 0 /\ in_app (nF cx fp) 64) /\
  (In (n_cid cx, n_pos cx) (frames (n_Sc cx)) /\
   frame_addr ly3 (n_cid cx) (n_pos cx) <= n_ps cx /\
   n_ps cx + PS_LEN <= frame_addr ly3 (n_cid cx) (n_pos cx) + fs_frame_bytes (n_cid cx)) /\
  (4096 <= n_ps cx /\ n_ps cx + PS_LEN <= alloc_ceiling /\ in_app (n_ps cx) PS_LEN) /\
  (n_ps cx + PS_LEN <= nF cx fp \/ nF cx fp + 64 <= n_ps cx) /\
  AR SEGS B ly3 S3 W3 (ms_mem ms3) md3.
Proof.
split; [exact hdA_fa|]. split; [exact hdA_fin|]. split; [exact hdA_F|].
split; [exact hdA_psf|]. split; [exact hdA_ps|]. split; [exact hdA_sep | exact hdA_AR3].
Qed.

End d.
(* ---------------------------------------------------------------------------------------------- *)
(* The phase: the loop head to the return of the header fread                                       *)
(* ---------------------------------------------------------------------------------------------- *)

(* The stream's environment lies in the image (asil_env), as in the close walk. *)
Hypothesis ASIL : @asource_img_laws SK SEGS B KS.
(* The fread wrapper's contract at its trampoline (0x8176c calls it; lib/A/Stdio/PFreadISpec.v). *)
Hypothesis H_fread :
  afread_spec SK SEGS B KS (@pa_sigma _ pcap_listing PI PS___interceptor_trampoline_fread).

Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.

#[local] Abbreviation POST := (nx_post SK B MT KS).

(* A callee-saved register is the caller's. *)
Lemma hdA_keep : forall (regs regs' : bvmap 5 word) (r : bv 5) (z : Z),
  aregs_preserved regs regs' -> bv_unsigned r = z -> acallee_saved z -> getr regs' r = getr regs r.
Proof.
intros regs regs' r z HP Hz Hcs. pose proof (HP z Hcs) as H. rewrite <- Hz, Z_to_bv_bv_unsigned in H. exact H.
Qed.

(* lia over this phase's large context: div / mod stay atoms (the Kit's setting; every division fact the proof
   needs is stated explicitly). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Theorem nxb_hdA_ph : forall R : ncx -> Z -> Prop,
  nx_from SK B KS POST (nx_hdra_inv B MT KS R) ->
  nx_from SK B KS POST
    (fun cx fp k2 ly3 S3 W3 ms3 md3 =>
       exists q lh, nx_next_ok R cx q /\ nx_loop_inv B MT KS cx fp q lh k2 ly3 S3 W3 ms3 md3).
Proof.
intros R HNEXT cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR (q & lh & Hnext & HL).
pose proof (hdA_seat cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR q lh HL) as (HS & HW).
pose proof (hdA_facts cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR) as
  (EFA & HFIN & (HF0 & HFc & HF64 & HFapp) & (HPSin & HPSle1 & HPSle2) & (HP0 & HPc & HPapp) & HSEP & HAR3).
pose proof (hdA_notE cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR) as HNOTE.
pose proof (hdA_chain cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR) as HCHAIN.
pose proof HL as (HM & R19 & R20 & HCH).
pose proof HM as (HBD & R21 & R23 & R26 & R27 & HJBK & HKEPT & HEsub & Hh0 & HPSAT & HRA & HSRC & Hqr & HBJ & HTS).
pose proof HBD as (HB0 & HSLOTS).
pose proof HB0 as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HREGS & HSAVED & HHDR & HFLW & HSHA & HSHLEN & R25 & HFK).
pose proof HREGS as (RG2 & RG8 & RG9 & RG3 & RG4).
pose proof HJBK as (HEK & HABL & HMO & HFDS & HFSS).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HJ0 & _ & _ & P4 & P5 & P6 & _ & _ & _ & _ & P11 & P12 & P13 & P14 & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hh64 & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbuf & Hts & Hstream & _).
pose proof HJ0 as (HARc & _ & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
destruct Hstk0 as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
destruct (Hstream Hh0) as (Hinh & Hinb & _ & HClen & Hpq & Hdbufh & Hdbufb & Hdpsh & Hdpsb & Hdts & HFPinc).
destruct (al_blocks _ _ LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) _ _ HARc Hinh)
  as (_ & Hh4096 & Hhceil & Hhapp & _).
destruct (al_blocks _ _ LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) _ _ HARc Hinb)
  as (_ & Hb4096 & Hbceil & Hbapp & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil, Hhapp.
pose proof (req_size_pos (Z.of_nat (length (n_C cx))) ltac:(clear; lia)) as (_ & Hrqb).
(* the numbers of this state *)
assert (HSP : alloc_ceiling + NX_STK_B <= spZ (n_regs cx)) by (clear - Hceil Hslo P12; lia).
pose proof (NX_STK_B_frame (spZ (n_regs cx)) P11) as ((Hsp1lo & Hsp1hi) & Hsp1al).
change (nx_sp1 (spZ (n_regs cx))) with (n_sp1 cx) in Hsp1lo, Hsp1hi, Hsp1al.
unfold NX_MFRAME in Hsp1hi.
assert (HSTKB : NX_STK_B = 272 + AFREAD_STK) by reflexivity.
assert (HAF : AFREAD_STK = 8192) by reflexivity.
assert (HSP1_16 : n_sp1 cx mod 16 = 0).
{ clear - Hsp1al. pose proof (Z.div_mod (n_sp1 cx) 32 ltac:(lia)) as D. rewrite Hsp1al, Z.add_0_r in D.
  rewrite D. replace (32 * (n_sp1 cx / 32)) with ((2 * (n_sp1 cx / 32)) * 16) by lia.
  apply Z.mod_mul. lia. }
assert (HF8 : nF cx fp mod 8 = 0).
{ clear - HF64. destruct (hdA_div64 (nF cx fp) HF64) as (D & _). rewrite D.
  replace (64 * (nF cx fp / 64)) with ((8 * (nF cx fp / 64)) * 8) by lia. apply Z.mod_mul. lia. }
assert (ESH : nSH cx fp = shadow_addr (nF cx fp)) by reflexivity.
assert (HSH8 : nSH cx fp mod 8 = 0).
{ clear - HF64. destruct (hdA_div64 (nF cx fp) HF64) as (_ & E8). unfold nSH, shadow_of_addr. rewrite E8.
  replace (SHADOW_OFF + 8 * (nF cx fp / 64)) with ((268431360 + nF cx fp / 64) * 8)
    by (unfold SHADOW_OFF; lia).
  apply Z.mod_mul. lia. }
assert (HSHlo : nSH cx fp + 8 < alloc_ceiling).
{ clear - HF0 HFc C1. pose proof (Z.mul_div_le (nF cx fp) 8 ltac:(lia)) as Hm.
  unfold nSH, shadow_of_addr, SHADOW_OFF. lia. }
assert (HSHpres : forall i, 0 <= i < 8 ->
  aview SEGS (w_H W3) (ms_mem ms3) (nSH cx fp + i) = Some (nth (Z.to_nat i) NSH_entry 0)).
{ intros i Hi. assert (Hi' : (Z.to_nat i < length NSH_entry)%nat) by (clear - Hi; cbn [length NSH_entry]; lia).
  pose proof (HSHA (Z.to_nat i) Hi') as H. rewrite Z2Nat.id in H by (clear - Hi; lia). exact H. }
(* the atoms of the seat, which the run keeps *)
assert (HEI : img_env VAL A_LIM (Eimg (Ereg (ms_regs ms3) (hdA_extra (n_h cx))))) by apply Eimg_env.
assert (E25 : ew (Eimg (Ereg (ms_regs ms3) (hdA_extra (n_h cx)))) 25 = w64 (nSH cx fp))
  by (rewrite (ew_Eimg_Ereg_nat (ms_regs ms3) _ 25%nat (25%bv : bv 5) ltac:(vm_compute; reflexivity)); exact R25).
assert (U25 : bv_unsigned (ew (Eimg (Ereg (ms_regs ms3) (hdA_extra (n_h cx)))) 25) = nSH cx fp).
{ rewrite E25. apply unsigned_lit_small. clear - HSHlo C1 HF0.
  pose proof (Z.div_pos (nF cx fp) 8 ltac:(lia) ltac:(lia)) as Hd.
  unfold nSH, shadow_of_addr, SHADOW_OFF in *. lia. }
(* the run of the nine slots, to the fread call *)
paj_run_shc RUNP RUNC HS HJ.
- exact HW.
- (* the registers at the call *)
  assert (G2 : getr (ms_regs ms) 2 = getr (ms_regs ms3) 2)
    by (eapply hdA_reg_same; [exact HS | vm_compute; reflexivity | vm_compute; reflexivity]).
  assert (G3 : getr (ms_regs ms) 3 = getr (ms_regs ms3) 3)
    by (eapply hdA_reg_same; [exact HS | vm_compute; reflexivity | vm_compute; reflexivity]).
  assert (G4 : getr (ms_regs ms) 4 = getr (ms_regs ms3) 4)
    by (eapply hdA_reg_same; [exact HS | vm_compute; reflexivity | vm_compute; reflexivity]).
  assert (G8 : getr (ms_regs ms) 8 = getr (ms_regs ms3) 8)
    by (eapply hdA_reg_same; [exact HS | vm_compute; reflexivity | vm_compute; reflexivity]).
  assert (G9 : getr (ms_regs ms) 9 = getr (ms_regs ms3) 9)
    by (eapply hdA_reg_same; [exact HS | vm_compute; reflexivity | vm_compute; reflexivity]).
  assert (G19 : getr (ms_regs ms) 19 = getr (ms_regs ms3) 19)
    by (eapply hdA_reg_same; [exact HS | vm_compute; reflexivity | vm_compute; reflexivity]).
  assert (G20 : getr (ms_regs ms) 20 = getr (ms_regs ms3) 20)
    by (eapply hdA_reg_same; [exact HS | vm_compute; reflexivity | vm_compute; reflexivity]).
  assert (G21 : getr (ms_regs ms) 21 = getr (ms_regs ms3) 21)
    by (eapply hdA_reg_same; [exact HS | vm_compute; reflexivity | vm_compute; reflexivity]).
  assert (G23 : getr (ms_regs ms) 23 = getr (ms_regs ms3) 23)
    by (eapply hdA_reg_same; [exact HS | vm_compute; reflexivity | vm_compute; reflexivity]).
  assert (G25 : getr (ms_regs ms) 25 = getr (ms_regs ms3) 25)
    by (eapply hdA_reg_same; [exact HS | vm_compute; reflexivity | vm_compute; reflexivity]).
  assert (G26 : getr (ms_regs ms) 26 = getr (ms_regs ms3) 26)
    by (eapply hdA_reg_same; [exact HS | vm_compute; reflexivity | vm_compute; reflexivity]).
  assert (G27 : getr (ms_regs ms) 27 = getr (ms_regs ms3) 27)
    by (eapply hdA_reg_same; [exact HS | vm_compute; reflexivity | vm_compute; reflexivity]).
  assert (G1 : getr (ms_regs ms) 1 = w64 (BASE + NP_hd_ra))
    by (eapply (hdA_reg_pc _ _ (w_H W3) ms (1%bv : bv 5) NP_hd_ra HEI HS); vm_compute; reflexivity).
  assert (G10 : getr (ms_regs ms) 10 = w64 (nF cx fp + NO_PH)).
  { eapply (hdA_reg_atom _ _ (w_H W3) ms (10%bv : bv 5) 19%nat);
      [exact HS | vm_compute; reflexivity | | clear - HF0 HFc C1; unfold NO_PH; lia].
    rewrite (ew_Eimg_Ereg_nat (ms_regs ms3) _ 19%nat (19%bv : bv 5) ltac:(vm_compute; reflexivity)).
    exact R19. }
  assert (G11 : getr (ms_regs ms) 11 = w64 1)
    by (eapply hdA_reg_lit; [exact HS | vm_compute; reflexivity]).
  assert (G12 : getr (ms_regs ms) 12 = w64 NX_PH_LEN)
    by (eapply hdA_reg_lit; [exact HS | vm_compute; reflexivity]).
  assert (G13 : getr (ms_regs ms) 13 = w64 (n_h cx)).
  { eapply (hdA_reg_atom _ _ (w_H W3) ms (13%bv : bv 5) 32%nat);
      [exact HS | vm_compute; reflexivity | | clear - Hh64; lia].
    rewrite Eimg_low by (unfold A_TEXT; clear; lia).
    replace 32%nat with (32 + 0)%nat by reflexivity. rewrite ew_Ereg_extra. reflexivity. }
  assert (ESPms : spZ (ms_regs ms) = n_sp1 cx).
  { unfold spZ. rewrite G2, RG2. apply unsigned_lit_small.
    clear - HSP Hsp1lo Hsp1hi P13 Hshi H47 C1. unfold NX_STK_B, AFREAD_STK in *. lia. }
  assert (ES0ms : s0Z (ms_regs ms) = spZ (n_regs cx)).
  { unfold s0Z. rewrite G8, RG8. apply unsigned_lit_small.
    clear - HSP P13 Hshi H47 C1. unfold NX_STK_B, AFREAD_STK in *. lia. }
  (* the two shadow bytes the run wrote *)
  pose proof HS as HSm.
  destruct HSm as (_ & _ & _ & _ & _ & _ & _ & (_ & HRS & _) & _).
  assert (HR0 : region_ok SEGS (Eimg (Ereg (ms_regs ms3) (hdA_extra (n_h cx))))
    (mrestrict (w_H W3) (ms_mem ms))
    (YP09.mkRegion (Some 25%nat) 4 6 4 6
      [YP09.mkChunk 5 (CVal 1 (SLit 0)); YP09.mkChunk 4 (CVal 1 (SLit 0))])).
  { eapply (proj1 (Forall_forall _ _) HRS). vm_compute. left. reflexivity. }
  assert (HZ4 : aview SEGS (w_H W3) (ms_mem ms) (nSH cx fp + 4) = Some 0)
    by (apply (hdA_byte0 _ (w_H W3) (ms_mem ms) 25%nat (nSH cx fp) _ 4 6 4 6 4 HR0 U25);
        cbn [In]; right; left; reflexivity).
  assert (HZ5 : aview SEGS (w_H W3) (ms_mem ms) (nSH cx fp + 5) = Some 0)
    by (apply (hdA_byte0 _ (w_H W3) (ms_mem ms) 25%nat (nSH cx fp) _ 4 6 4 6 5 HR0 U25);
        cbn [In]; left; reflexivity).
  (* what the run kept *)
  assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) ->
    aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha Hn.
    apply (aview_kept_out (Eimg (Ereg (ms_regs ms3) (hdA_extra (n_h cx)))) hdA_regions (w_H W3)
      (ms_mem ms3) (ms_mem ms) HFr a Ha).
    intros (r & Hin & Hr). unfold hdA_regions in Hin. cbn [In] in Hin.
    destruct Hin as [<- | [<- | [<- | []]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
      first [ change (base_val (Eimg (Ereg (ms_regs ms3) (hdA_extra (n_h cx)))) (Some 25%nat)) with
                (bv_unsigned (ew (Eimg (Ereg (ms_regs ms3) (hdA_extra (n_h cx)))) 25)) in Hr;
              rewrite U25 in Hr; clear - Hr Hn; lia
            | clear - Hr; lia ]. }
  (* ---- the places this phase meets ---- *)
  assert (HSHband : kLowMemEnd <= nSH cx fp /\ nSH cx fp + 8 < kHighShadowEnd).
  { pose proof (shadow_addr_bounds (nF cx fp) ltac:(clear - HFc HF0 C1 C4; lia)) as (B1 & _).
    pose proof (shadow_addr_bounds (nF cx fp + 64) ltac:(clear - HFc HF0 C1 C4; lia)) as (_ & B2).
    assert (E64 : shadow_addr (nF cx fp + 64) = nSH cx fp + 8).
    { change (shadow_addr (nF cx fp + 64)) with (shadow_of_addr SHADOW_OFF (nF cx fp + 64)).
      replace (nF cx fp + 64) with (nF cx fp + 8 * 8) by (clear; lia). apply shadow_of_addr_add8. }
    rewrite <- ESH in B1. rewrite E64 in B2. split; [exact B1 | exact B2]. }
  (* an application byte is not one of this frame's shadow bytes *)
  assert (HSHapp : forall a n x, in_app a n -> a <= x < a + n -> ~ (nSH cx fp <= x < nSH cx fp + 8)).
  { intros a n x (Ha0 & Ha) Hx Hc. destruct HSHband as (B1 & B2).
    unfold kLowShadowBeg, kHighMemBeg in Ha. rewrite C2 in B2. rewrite C5 in B1.
    destruct Ha as [Ha | (Ha & _)]; clear - Ha Hx Hc B1 B2; lia. }
  assert (HWIN : alloc_ceiling + AFREAD_STK <= n_sp1 cx)
    by (clear - HSP Hsp1lo; unfold NX_STK_B, AFREAD_STK in *; lia).
  assert (HNE' : forall a, alloc_ceiling <= a -> ~ rread_wrset (n_h cx) (nF cx fp + NO_PH) NX_PH_LEN a).
  { intros a Ha [H | H]; unfold SRC_FILE_BLOCK, NO_PH, NX_PH_LEN in *; clear - Ha H Hhceil HFc; lia. }
  assert (HDFh : nF cx fp + 64 <= n_h cx \/ n_h cx + 1304 <= nF cx fp).
  { assert (Hin3 : In (n_h cx, SRC_FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite HABL; exact Hinh).
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ NX_CID fp HAR3 Hin3 HFIN) as D.
    unfold zdisjoint, frame_rng in D. cbn [fst snd] in D. rewrite hdA_fsb, EFA in D.
    change (req_size SRC_FILE_BLOCK) with 1304 in D.
    change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp) in D. clear - D. lia. }
  assert (HDFb : nF cx fp + 64 <= n_b cx \/ n_b cx + Z.of_nat (length (n_C cx)) <= nF cx fp).
  { assert (Hin3 : In (n_b cx, Z.of_nat (length (n_C cx))) (ablocks B ly3 S3)) by (rewrite HABL; exact Hinb).
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ NX_CID fp HAR3 Hin3 HFIN) as D.
    unfold zdisjoint, frame_rng in D. cbn [fst snd] in D. rewrite hdA_fsb, EFA in D.
    clear - D Hrqb. change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp) in D. lia. }
  assert (HIMG : forall a, 0x10000 <= a < pcap_img_end -> ~ (nSH cx fp <= a < nSH cx fp + 8)).
  { intros a Ha Hc. destruct HSHband as (B1 & _). rewrite C5 in B1.
    unfold pcap_img_end, YImgTop.IMG_TOP in Ha. clear - Ha Hc B1; lia. }
  assert (HSRCm : asource_at SEGS KS (rdW W3 (ms_mem ms)) (n_h cx) (n_b cx) (n_C cx) q).
  { apply (PcapSourceCloseSpec.asource_at_frame_segs _ KS (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms)) (n_h cx) (n_b cx) (n_C cx) q);
      [|exact HSRC].
    intros a Ha. apply (mbyte_of_aview SEGS).
    destruct Ha as [Ha | [Ha | Ha]].
    - apply HOUT; [unfold SRC_FILE_BLOCK in Ha; clear - Ha Hh4096 Hhceil C1; lia|].
      intros Hc. apply (HSHapp _ _ a Hhapp ltac:(unfold SRC_FILE_BLOCK in Ha; clear - Ha; lia)). clear - Hc; lia.
    - apply HOUT; [clear - Ha Hb4096 Hbceil Hrqb C1; lia|].
      intros Hc. apply (HSHapp _ _ a Hbapp ltac:(clear - Ha Hrqb; lia)). clear - Hc; lia.
    - pose proof (pa_img_range a (proj1 (asil_env _ _ _ _ ASIL a Ha))) as Hi.
      apply HOUT; [unfold pcap_img_end, YImgTop.IMG_TOP in Hi; clear - Hi; lia|].
      intros Hc. apply (HIMG a Hi). clear - Hc; lia. }
  assert (ESHd4 : shadow_addr (nF cx fp + NO_PH) = nSH cx fp + 4).
  { unfold NO_PH. change (shadow_addr (nF cx fp + 32)) with (shadow_of_addr SHADOW_OFF (nF cx fp + 32)).
    replace (nF cx fp + 32) with (nF cx fp + 8 * 4) by (clear; lia). apply shadow_of_addr_add8. }
  assert (ESHd5 : shadow_addr (nF cx fp + NO_PH + NX_PH_LEN - 1) = nSH cx fp + 5).
  { unfold NO_PH, NX_PH_LEN.
    change (shadow_addr (nF cx fp + 32 + 16 - 1)) with (shadow_of_addr SHADOW_OFF (nF cx fp + 32 + 16 - 1)).
    assert (Q : (nF cx fp + 8 * 5) / 8 = nF cx fp / 8 + 5).
    { replace (nF cx fp + 8 * 5) with (nF cx fp + 5 * 8) by (clear; lia). apply Z.div_add. clear; lia. }
    pose proof (Z.div_mod (nF cx fp) 8 ltac:(clear; lia)) as D. rewrite HF8, Z.add_0_r in D.
    rewrite (shadow_of_addr_same_granule SHADOW_OFF (nF cx fp + 8 * 5) (nF cx fp + 32 + 16 - 1)).
    - apply shadow_of_addr_add8.
    - rewrite Q. clear - D. lia. }
  (* ---- the call of fread(F + 32, 1, 16, h) ---- *)
  pmkst HS.
  eapply SRr_bind.
  { apply (H_fread (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
      ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) k2
      (ms_regs ms) (nx_ch cx) (nF cx fp + NO_PH) NX_PH_LEN (n_h cx) (n_b cx) q (n_C cx)).
    split.
    { (* the call inside the caller's journal *)
      split; [exact HJ|].
      split; [rewrite G1; apply ret_ok_codeptr_v; [unfold NP_hd_ra; clear; lia | reflexivity]|].
      split.
      { unfold raZ. rewrite G1. pose proof pa_B_ok as HBo. pose proof pa_base_lo as HBl. unfold w64.
        rewrite unsigned_lit_small by (unfold NP_hd_ra; clear - HBo; lia). clear - HBl. unfold NP_hd_ra. lia. }
      split; [rewrite G3, RG3; exact P5|].
      split; [rewrite G4, RG4; exact P6|].
      split; [rewrite ESPms; exact HSP1_16|].
      split; [rewrite ESPms; clear - P12 Hsp1lo; unfold NX_STK_B, AFREAD_STK in *; lia|].
      split; [rewrite ESPms; clear - P13 Hsp1hi; lia|].
      rewrite ESPms, ES0ms. apply HCHAIN; [exact Hh0 | | exact HSAVED | exact HKEPT].
      intros a Ha. apply HOUT; [clear - Ha C1; lia|]. clear - Ha HSHlo; lia. }
    split; [rewrite G10; reflexivity|].
    split; [rewrite G11; reflexivity|].
    split; [rewrite G12; reflexivity|].
    split; [rewrite G13; reflexivity|].
    split; [rewrite HABL; exact Hinh|].
    split; [rewrite HABL; exact Hinb|].
    split; [left; rewrite ESPms; clear - Hbceil Hrqb HWIN; lia|].
    split; [exact HSRCm|].
    split.
    { (* the right to write the FILE block *)
      intros a Ha. split.
      - assert (HinFP : inFP (asource_fp (n_h cx)) a)
          by (exists (n_h cx, n_h cx + SRC_FILE_BLOCK); split; [left; reflexivity | cbn [fst snd]; exact Ha]).
        destruct (HFPinc a HinFP) as [Hf | Ht].
        + right. left. split; [exact Hf|]. exists (n_h cx), SRC_FILE_BLOCK. split; [rewrite HABL; exact Hinh|].
          change (req_size SRC_FILE_BLOCK) with 1304. unfold SRC_FILE_BLOCK in Ha. clear - Ha. lia.
        + right. right. left. rewrite HABL. exact Ht.
      - rewrite ESPms. unfold SRC_FILE_BLOCK in Ha. clear - Ha Hhceil HWIN. lia. }
    split; [unfold NX_PH_LEN; clear; lia|].
    (* the destination F + 32 .. F + 47 *)
    split; [unfold NO_PH, NX_PH_LEN, SRC_FILE_BLOCK; clear - HDFh; lia|].
    split; [unfold NO_PH, NX_PH_LEN; clear - HDFb; lia|].
    split; [unfold NO_PH; clear - HF0; lia|].
    split.
    { unfold amem_range, NO_PH, NX_PH_LEN. destruct HFapp as (_ & HFa).
      unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFa. rewrite C5, C4, C3.
      clear - HFa HFc C1. lia. }
    split.
    { left. exists NX_CID, fp. split; [exact HFIN|]. intros a Ha.
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA, hdA_fsb.
      change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp). unfold NO_PH, NX_PH_LEN in Ha. clear - Ha. lia. }
    split.
    { intros a Ha. split.
      - apply awr_byte_own_head. rewrite EFA, hdA_fsb. change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp).
        unfold NO_PH, NX_PH_LEN in Ha. clear - Ha. lia.
      - rewrite ESPms. unfold NO_PH, NX_PH_LEN in Ha. clear - Ha HFc HWIN. lia. }
    split; [exact (hdA_ph_ra _ (nF cx fp) HF8 HZ4 HZ5)|].
    intros _ s Hs. rewrite ESHd4, ESHd5 in Hs.
    assert (D4 : (nSH cx fp + 4) / 8 * 8 = nSH cx fp /\ (nSH cx fp + 5) / 8 * 8 = nSH cx fp).
    { pose proof (Z.div_mod (nSH cx fp) 8 ltac:(clear; lia)) as D. rewrite HSH8, Z.add_0_r in D.
      split; rewrite D at 1.
      - replace (8 * (nSH cx fp / 8) + 4) with (4 + (nSH cx fp / 8) * 8) by (clear; lia).
        rewrite Z.div_add by (clear; lia). change (4 / 8) with 0. clear - D. lia.
      - replace (8 * (nSH cx fp / 8) + 5) with (5 + (nSH cx fp / 8) * 8) by (clear; lia).
        rewrite Z.div_add by (clear; lia). change (5 / 8) with 0. clear - D. lia. }
    destruct D4 as (D4 & D5). rewrite D4, D5 in Hs.
    destruct (Z.eq_dec s (nSH cx fp + 4)) as [-> | N4]; [rewrite HZ4; discriminate|].
    destruct (Z.eq_dec s (nSH cx fp + 5)) as [-> | N5]; [rewrite HZ5; discriminate|].
    rewrite HOUT by (clear - Hs N4 N5 HSHband C2 C5; destruct HSHband; lia).
    replace s with (nSH cx fp + (s - nSH cx fp)) by (clear; lia).
    rewrite (HSHpres (s - nSH cx fp) ltac:(clear - Hs; lia)). discriminate. }
  (* ---- the return, NP_hd_ra ---- *)
  intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HK2 & HQ).
  unfold afread_post in HQ. cbv zeta in HQ.
  destruct HQ as (-> & -> & Ha0 & HGA & HSRC2 & _ & _ & HFD2 & HFS2 & HSB2).
  destruct HK2 as (K1 & K2 & K3 & K4 & K5 & K6).
  rewrite ESPms in K1, K5, K6.
  (* the callee-saved registers are the loop head's *)
  assert (Kr : forall (r : bv 5) z, bv_unsigned r = z -> acallee_saved z -> getr regs2 r = getr (ms_regs ms) r)
    by (intros r z H1 H2; exact (hdA_keep _ _ r z HP2 H1 H2)).
  assert (WVB : m_fds (with_vm_backing (m_vm_lazy md3) mat md3) = m_fds md3 /\
                m_fs (with_vm_backing (m_vm_lazy md3) mat md3) = m_fs md3)
    by (clear; destruct md3 as [fd [maps lazy mt] io fs proc lim tm]; split; reflexivity).
  (* what the run and the call kept *)
  assert (TR1 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (n_sp1 cx - AFREAD_STK <= a < n_sp1 cx) ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha Hw. rewrite (K1 a Ha Hw (HNE' a (proj1 Ha))).
    apply HOUT; [clear - Ha C1; lia | clear - Ha HSHlo; lia]. }
  assert (TRO : forall a, nF cx fp <= a < nF cx fp + 64 ->
    ~ (nF cx fp + NO_PH <= a < nF cx fp + NO_PH + NX_PH_LEN) ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha Hn. rewrite (K4 NX_CID fp a HFIN).
    - apply HOUT; [clear - Ha HF0 HFc C1; lia|].
      intros Hc. apply (HSHapp _ _ a HFapp Ha). clear - Hc; lia.
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA, hdA_fsb. exact Ha.
    - intros [H | H]; [unfold SRC_FILE_BLOCK in H; clear - H Ha HDFh; lia | exact (Hn H)]. }
  assert (TROS : forall i, 0 <= i < 8 ->
    aview SEGS (w_H W2) mem2 (nSH cx fp + i) = aview SEGS (w_H W3) (ms_mem ms) (nSH cx fp + i)).
  { intros i Hi. apply (K4 NX_CID fp _ HFIN).
    - right. unfold in_zr. cbn [fst snd]. rewrite EFA, hdA_fsb.
      change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp). rewrite <- ESH. change (64 / 8) with 8.
      clear - Hi. lia.
    - intros [H | H].
      + apply (HSHapp _ _ (nSH cx fp + i) Hhapp H). clear - Hi; lia.
      + apply (HSHapp _ _ (nSH cx fp + i) HFapp ltac:(unfold NO_PH, NX_PH_LEN in H; clear - H; lia)).
        clear - Hi; lia. }
  assert (TRF : forall cid pos a, In (cid, pos) (frames (n_Sc cx)) ->
    (in_zr a (frame_rng (n_lyc cx) (cid, pos)) \/
     in_zr a (shadow_addr (frame_addr (n_lyc cx) cid pos), fs_frame_bytes cid / 8)) ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros cid pos a Hin HaT.
    assert (Hin3 : In (cid, pos) (frames S3)) by (rewrite HFR; right; exact Hin).
    destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 cid pos HAR3 Hin3) as (Hg0 & Hgc & Hgapp).
    pose proof (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 cid pos HAR3 Hin3) as (Hg64 & Hgs64 & Hgs).
    destruct (in_split _ _ Hin) as (l1 & l2 & El).
    assert (Hd : zdisjoint (frame_rng ly3 (NX_CID, fp)) (frame_rng ly3 (cid, pos))).
    { eapply (sep_frames_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ [] l1 l2 HAR3).
      rewrite HFR, El. reflexivity. }
    assert (Hinh3 : In (n_h cx, SRC_FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite HABL; exact Hinh).
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ cid pos HAR3 Hinh3 Hin3) as D.
    unfold zdisjoint, frame_rng in Hd, D. cbn [fst snd] in Hd, D. rewrite hdA_fsb, !EFA in Hd. rewrite EFA in D.
    change (req_size SRC_FILE_BLOCK) with 1304 in D.
    rewrite EFA in Hg0, Hgc, Hgapp, Hg64.
    change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp) in Hd.
    assert (Ha : (frame_addr (n_lyc cx) cid pos <= a < frame_addr (n_lyc cx) cid pos + fs_frame_bytes cid) \/
                 (shadow_addr (frame_addr (n_lyc cx) cid pos) <= a <
                  shadow_addr (frame_addr (n_lyc cx) cid pos) + fs_frame_bytes cid / 8))
      by (unfold in_zr, frame_rng in HaT; cbn [fst snd] in HaT; exact HaT).
    set (g := frame_addr (n_lyc cx) cid pos) in *.
    pose proof (fs_frame_bytes_nonneg cid) as Hnn.
    pose proof (hdA_shr_disj (nF cx fp) 64 g (fs_frame_bytes cid) HF64 eq_refl ltac:(clear; lia)
      Hg64 Hgs64 Hnn ltac:(clear - Hd; lia)) as Hsd.
    rewrite <- ESH in Hsd. change (64 / 8) with 8 in Hsd.
    pose proof (shadow_addr_bounds g ltac:(clear - Hg0 Hgc C1 C4 Hnn; lia)) as (Hb1 & _).
    pose proof (shadow_range_end g (fs_frame_bytes cid) Hnn) as Hre.
    pose proof (shadow_addr_bounds (g + fs_frame_bytes cid) ltac:(clear - Hg0 Hgc C1 C4 Hnn; lia)) as (_ & Hb2).
    rewrite C5 in Hb1. rewrite C2 in Hb2.
    pose proof (HSHapp _ _ a Hgapp) as Happ.
    rewrite (K4 cid pos a Hin3).
    - apply HOUT.
      + destruct Ha as [Ha | Ha]; clear - Ha Hg0 Hgc C1 Hb1 Hb2 Hre Hnn; lia.
      + intros Hc. destruct Ha as [Ha | Ha].
        * apply Happ; [exact Ha | clear - Hc; lia].
        * clear - Ha Hc Hsd. lia.
    - destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA; fold g; exact Ha.
    - intros [H | H].
      + unfold SRC_FILE_BLOCK in H.
        destruct Ha as [Ha | Ha].
        * clear - Ha H D. lia.
        * destruct Hhapp as (_ & Hha). unfold kLowShadowBeg, kHighMemBeg in Hha.
          clear - Ha H Hha Hb1 Hb2 Hre. lia.
      + unfold NO_PH, NX_PH_LEN in H.
        destruct Ha as [Ha | Ha].
        * clear - Ha H Hd. lia.
        * destruct HFapp as (_ & Hfa). unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfa.
          clear - Ha H Hfa Hb1 Hb2 Hre HFc C1. lia. }
  assert (TRB : forall b0 m0 i, In (b0, m0) (ablocks B (n_lyc cx) (n_Sc cx)) -> 0 <= i < req_size m0 ->
    ~ (n_h cx <= b0 + i < n_h cx + SRC_FILE_BLOCK) ->
    aview SEGS (w_H W2) mem2 (b0 + i) = aview SEGS (w_H W3) (ms_mem ms3) (b0 + i)).
  { intros b0 m0 i Hin Hi Hnf.
    assert (Hin3 : In (b0, m0) (ablocks B ly3 S3)) by (rewrite HABL; exact Hin).
    destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ HAR3 Hin3) as (_ & Hb0 & Hbc & Hbapp0 & _).
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ NX_CID fp HAR3 Hin3 HFIN) as D.
    unfold zdisjoint, frame_rng in D. cbn [fst snd] in D. rewrite hdA_fsb, EFA in D.
    change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp) in D.
    rewrite (K2 b0 m0 i Hin3 Hi).
    - apply HOUT; [clear - Hi Hb0 Hbc C1; lia|].
      intros Hc. apply (HSHapp _ _ (b0 + i) Hbapp0 ltac:(clear - Hi; lia)). clear - Hc; lia.
    - intros [H | H]; [exact (Hnf H)|]. unfold NO_PH, NX_PH_LEN in H. clear - H Hi D. lia. }
  assert (TRI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Hi Ho He. pose proof (pa_img_range a Hi) as Hr.
    rewrite (K3 a Hi Ho He). apply HOUT; [unfold pcap_img_end, YImgTop.IMG_TOP in Hr; clear - Hr; lia|].
    intros Hc. apply (HIMG a Hr). clear - Hc; lia. }
  (* ---- the entry predicate of the next phase, at NP_hd_ra ---- *)
  set (ms2 := mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)).
  assert (MR : ms_regs ms2 = regs2) by reflexivity.
  assert (MM : ms_mem ms2 = mem2) by reflexivity.
  apply (HNEXT cx fp k2 ly3 S3 W2 ms2 md2 HB HJ2 HFR).
  (* the registers at the return *)
  assert (Q2 : getr regs2 2 = w64 (n_sp1 cx))
    by (rewrite (Kr 2%bv 2 ltac:(reflexivity) ltac:(unfold acallee_saved; clear; lia)), G2; exact RG2).
  assert (Q3 : getr regs2 3 = getr (n_regs cx) 3)
    by (rewrite (Kr 3%bv 3 ltac:(reflexivity) ltac:(unfold acallee_saved; clear; lia)), G3; exact RG3).
  assert (Q4 : getr regs2 4 = getr (n_regs cx) 4)
    by (rewrite (Kr 4%bv 4 ltac:(reflexivity) ltac:(unfold acallee_saved; clear; lia)), G4; exact RG4).
  assert (Q8 : getr regs2 8 = w64 (spZ (n_regs cx)))
    by (rewrite (Kr 8%bv 8 ltac:(reflexivity) ltac:(unfold acallee_saved; clear; lia)), G8; exact RG8).
  assert (Q9 : getr regs2 9 = w64 (n_sp1 cx))
    by (rewrite (Kr 9%bv 9 ltac:(reflexivity) ltac:(unfold acallee_saved; clear; lia)), G9; exact RG9).
  assert (Q19 : getr regs2 19 = w64 (nF cx fp + NO_PH))
    by (rewrite (Kr 19%bv 19 ltac:(reflexivity) ltac:(unfold acallee_saved; clear; lia)), G19; exact R19).
  assert (Q20 : getr regs2 20 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF)))
    by (rewrite (Kr 20%bv 20 ltac:(reflexivity) ltac:(unfold acallee_saved; clear; lia)), G20; exact R20).
  assert (Q21 : getr regs2 21 = w64 (n_ps cx))
    by (rewrite (Kr 21%bv 21 ltac:(reflexivity) ltac:(unfold acallee_saved; clear; lia)), G21; exact R21).
  assert (Q23 : getr regs2 23 = w64 (n_cap cx))
    by (rewrite (Kr 23%bv 23 ltac:(reflexivity) ltac:(unfold acallee_saved; clear; lia)), G23; exact R23).
  assert (Q25 : getr regs2 25 = w64 (nSH cx fp))
    by (rewrite (Kr 25%bv 25 ltac:(reflexivity) ltac:(unfold acallee_saved; clear; lia)), G25; exact R25).
  assert (Q26 : getr regs2 26 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx)))
    by (rewrite (Kr 26%bv 26 ltac:(reflexivity) ltac:(unfold acallee_saved; clear; lia)), G26; exact R26).
  assert (Q27 : getr regs2 27 = w64 (n_ps cx + PS_SW_OFF))
    by (rewrite (Kr 27%bv 27 ltac:(reflexivity) ltac:(unfold acallee_saved; clear; lia)), G27; exact R27).
  (* the memory at the return *)
  assert (HSL : forall off v, 0 <= off < 152 -> nslot cx W3 ms3 off v -> nslot cx W2 ms2 off v).
  { intros off v Hoff Hs. unfold nslot in *. rewrite MM, <- Hs. apply rdword_ext. intros k Hk.
    apply TR1; clear - Hoff Hk HSP Hsp1lo Hsp1hi P13 Hshi H47 HWIN C1; unfold NX_STK_B, AFREAD_STK in *; lia. }
  assert (HSV : forall a v, spZ (n_regs cx) - 104 <= a <= spZ (n_regs cx) - 8 ->
    rdword (aview SEGS (w_H W3) (ms_mem ms3)) a = Some v -> rdword (aview SEGS (w_H W2) (ms_mem ms2)) a = Some v).
  { intros a v Ha Hv. rewrite MM, <- Hv. apply rdword_ext. intros k Hk.
    apply TR1; clear - Ha Hk HSP Hsp1hi P13 Hshi H47 C1; unfold NX_STK_B, AFREAD_STK in *; lia. }
  assert (HFW : forall a v, (nF cx fp <= a /\ a + 8 <= nF cx fp + 24) \/ a = nF cx fp + NX_FLAGPTR ->
    rdword (aview SEGS (w_H W3) (ms_mem ms3)) a = Some v -> rdword (aview SEGS (w_H W2) (ms_mem ms2)) a = Some v).
  { intros a v Ha Hv. rewrite MM, <- Hv. apply rdword_ext. intros k Hk.
    apply TRO; unfold NX_FLAGPTR, NO_PH, NX_PH_LEN in *; clear - Ha Hk; lia. }
  assert (HSHN : nshadow cx fp W2 ms2 NSH_ph).
  { intros i Hi. change (length NSH_ph) with 8%nat in Hi. rewrite MM.
    rewrite (TROS (Z.of_nat i) ltac:(clear - Hi; lia)).
    destruct (Nat.eq_dec i 4) as [-> | N4]; [change (Z.of_nat 4) with 4; rewrite HZ4; reflexivity|].
    destruct (Nat.eq_dec i 5) as [-> | N5]; [change (Z.of_nat 5) with 5; rewrite HZ5; reflexivity|].
    rewrite HOUT by (destruct HSHband as (SB1 & SB2); rewrite C2 in SB2; rewrite C5 in SB1;
                     clear - Hi N4 N5 SB1 SB2; lia).
    rewrite (HSHpres (Z.of_nat i) ltac:(clear - Hi; lia)), Nat2Z.id.
    destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try reflexivity; exfalso; clear - Hi N4 N5; lia. }
  assert (HKEPT2 : nx_kept SEGS NX_STK_B B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W2 mem2
    (spZ (n_regs cx)) (nx_E cx)).
  { destruct HKEPT as (H1 & H2 & H3 & H4 & H5 & H6).
    split; [|split; [|split; [|split; [|split]]]].
    - intros a Ha Hw HnE. rewrite TR1; [exact (H1 a Ha Hw HnE) | exact Ha |].
      clear - Hw HSP Hsp1lo Hsp1hi. unfold NX_STK_B, AFREAD_STK in *. lia.
    - intros b0 m0 i Hin Hi HnE. rewrite (TRB b0 m0 i Hin Hi); [exact (H2 b0 m0 i Hin Hi HnE)|].
      intros Hf. apply HnE. right. right. right. split; [exact Hh0 | exact Hf].
    - intros a Hi Ho He. rewrite (TRI a Hi Ho He). exact (H3 a Hi Ho He).
    - intros cid pos a Hin Ha HnE. rewrite (TRF cid pos a Hin Ha). exact (H4 cid pos a Hin Ha HnE).
    - intros a Ha Hw Hp. pose proof (H5 a Ha Hw Hp) as Hp3.
      eapply (apresent_transfer SEGS); [clear - Ha C1; lia | | | exact Hp3].
      + intros Him. pose proof (pa_segs_low a Him) as Hl. clear - Ha Hl C1 C5. lia.
      + apply TR1; [exact Ha|]. clear - Hw HSP Hsp1lo Hsp1hi. unfold NX_STK_B, AFREAD_STK in *. lia.
    - intros a Ha.
      destruct (Z_lt_le_dec a (n_sp1 cx - AFREAD_STK)) as [Hlo | Hlo];
        [| destruct (Z_lt_le_dec a (n_sp1 cx)) as [Hhi | Hhi]; [apply K6; clear - Hlo Hhi; lia |]].
      + eapply (apresent_transfer SEGS); [ | | | exact (H6 a Ha)].
        * clear - Ha HSP P13 Hshi H47 C1. unfold NX_STK_B, AFREAD_STK in *. lia.
        * intros Him. pose proof (pa_segs_low a Him) as Hl. clear - Ha Hl HSP C1 C5. lia.
        * apply TR1; [clear - Ha HSP P13 Hshi H47 C1; unfold NX_STK_B, AFREAD_STK in *; lia | clear - Hlo; lia].
      + eapply (apresent_transfer SEGS); [ | | | exact (H6 a Ha)].
        * clear - Ha HSP P13 Hshi H47 C1. unfold NX_STK_B, AFREAD_STK in *. lia.
        * intros Him. pose proof (pa_segs_low a Him) as Hl. clear - Ha Hl HSP C1 C5. lia.
        * apply TR1; [clear - Ha HSP P13 Hshi H47 C1; unfold NX_STK_B, AFREAD_STK in *; lia | clear - Hhi; lia]. }
  assert (HPSM : forall a, n_ps cx <= a < n_ps cx + PS_LEN ->
    mbyte SEGS (rdW W2 mem2) a = mbyte SEGS (rdW W3 (ms_mem ms3)) a).
  { intros a Ha. apply (mbyte_of_aview SEGS). apply (TRF (n_cid cx) (n_pos cx) a HPSin).
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EFA. clear - Ha HPSle1 HPSle2. lia. }
  assert (HPSS : forall x, n_ps cx <= x < n_ps cx + PS_LEN ->
    aview SEGS (w_H W2) mem2 (shadow_of_addr SHADOW_OFF x) =
    aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF x)).
  { intros x Hx. apply (TRF (n_cid cx) (n_pos cx) _ HPSin). right. unfold in_zr. cbn [fst snd].
    assert (Hin3 : In (n_cid cx, n_pos cx) (frames S3)) by (rewrite HFR; right; exact HPSin).
    pose proof (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 _ _ HAR3 Hin3) as (G64 & Gs64 & _).
    rewrite EFA in G64. pose proof (fs_frame_bytes_nonneg (n_cid cx)) as Hnn.
    apply (hdA_sh_in _ _ x G64 Gs64 Hnn). rewrite <- EFA. clear - Hx HPSle1 HPSle2. lia. }
  (* the predicate *)
  exists q, lh. split; [exact Hnext|].
  split.
  { split.
    { split.
      { split; [exact G1|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|].
        split; [unfold nregs; rewrite MR; split; [exact Q2|]; split; [exact Q8|]; split; [exact Q9|];
                split; [exact Q3 | exact Q4]|].
        split.
        { destruct HSAVED as (S1 & S2). split.
          - apply HSV; [clear; lia | exact S1].
          - intros j Hj. apply HSV; [clear - Hj; lia | exact (S2 j Hj)]. }
        split.
        { destruct HHDR as (H1 & H2 & H3).
          split; [apply HFW; [left; clear; lia | exact H1]|].
          split; [apply HFW; [left; clear; lia | exact H2] | apply HFW; [left; clear; lia | exact H3]]. }
        split; [apply HFW; [right; reflexivity | exact HFLW]|].
        split; [exact HSHN|]. split; [reflexivity|].
        split; [rewrite MR; exact Q25|].
        apply HSL; [unfold NS_FK; clear; lia | exact HFK]. }
      destruct HSLOTS as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12).
      repeat (split; [apply HSL;
        [unfold NS_FK, NS_F0, NS_BUF, NS_TS, NS_SB, NS_PS12, NS_SH12, NS_OFF8, NS_OFF12, NS_PH4, NS_PH8, NS_PH12;
         clear; lia | eassumption]|]).
      apply HSL;
        [unfold NS_FK, NS_F0, NS_BUF, NS_TS, NS_SB, NS_PS12, NS_SH12, NS_OFF8, NS_OFF12, NS_PH4, NS_PH8, NS_PH12;
         clear; lia | eassumption]. }
    rewrite MR, MM.
    split; [exact Q21|]. split; [exact Q23|]. split; [exact Q26|]. split; [exact Q27|].
    split.
    { split; [exact HEK|]. split; [exact HABL|]. split; [exact HMO|].
      split; [rewrite HFD2, (proj1 WVB); exact HFDS | rewrite HFS2, (proj2 WVB); exact HFSS]. }
    split; [exact HKEPT2|]. split; [exact HEsub|]. split; [exact Hh0|].
    split.
    { destruct HPSAT as (V1 & V2 & V3 & V4 & V5 & V6 & V7).
      unfold PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF in *.
      split; [eapply PcapSourceCloseSpec.vm_frame_segs; [|exact V1]; intros x Hx; apply HPSM; unfold PS_LEN; cbn in Hx; clear - Hx;
              unfold PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF in Hx; lia|].
      split; [eapply PcapSourceCloseSpec.vm_frame_segs; [|exact V2]; intros x Hx; apply HPSM; unfold PS_LEN; cbn in Hx; clear - Hx;
              unfold PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF in Hx; lia|].
      split; [eapply PcapSourceCloseSpec.vm_frame_segs; [|exact V3]; intros x Hx; apply HPSM; unfold PS_LEN; cbn in Hx; clear - Hx;
              unfold PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF in Hx; lia|].
      split; [eapply PcapSourceCloseSpec.vm_frame_segs; [|exact V4]; intros x Hx; apply HPSM; unfold PS_LEN; cbn in Hx; clear - Hx;
              unfold PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF in Hx; lia|].
      split; [eapply PcapSourceCloseSpec.vm_frame_segs; [|exact V5]; intros x Hx; apply HPSM; unfold PS_LEN; cbn in Hx; clear - Hx;
              unfold PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF in Hx; lia|].
      split; [|exact V7].
      apply (garr8_frame SEGS _ _ _ _ V6). intros x Hx. rewrite V7 in Hx. apply HPSM.
      unfold PS_LEN. cbn in Hx. clear - Hx. lia. }
    split; [exact (PcapSourceCloseSpec.ra_frame _ _ _ _ HRA HPSS)|].
    split; [exact HSRC2|].
    split; [unfold nx_hk, NX_PH_LEN; clear - Hqr; lia|].
    split.
    { destruct (Hbuf Hh0) as (Hinbuf & _ & _ & _ & Hlenbj & _ & _ & _).
      destruct HBJ as (bj' & Hgbj & Hlbj). exists bj'. split; [|exact Hlbj].
      apply (garr8_frame SEGS _ _ _ _ Hgbj). intros a Ha. apply (mbyte_of_aview SEGS).
      rewrite Hlbj in Ha.
      pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; clear; lia)) as (_ & Hrq).
      replace a with (n_buf cx + (a - n_buf cx)) by (clear; lia).
      apply (TRB (n_buf cx) (nx_bufn (n_cap cx)) (a - n_buf cx) Hinbuf); [clear - Ha Hlenbj Hrq; lia|].
      unfold SRC_FILE_BLOCK in *. clear - Ha Hlenbj Hdbufh. lia. }
    intros Hts0. destruct (HTS Hts0) as (TV & TRA).
    destruct (Hts Hh0 Hts0) as (_ & _ & _ & _ & _ & (tcid & tpos & Htin & Ht1 & Ht2) & _).
    assert (Htin' : In (tcid, tpos) (frames (n_Sc cx))) by (rewrite Hfrs0; apply in_or_app; left; exact Htin).
    assert (Htin3 : In (tcid, tpos) (frames S3)) by (rewrite HFR; right; exact Htin').
    split.
    - eapply PcapSourceCloseSpec.vm_frame_segs; [|exact TV]. intros x Hx. apply (mbyte_of_aview SEGS).
      apply (TRF tcid tpos x Htin'). left. unfold in_zr, frame_rng. cbn [fst snd]. cbn in Hx.
      clear - Hx Ht1 Ht2. lia.
    - apply (PcapSourceCloseSpec.ra_frame _ _ _ _ TRA). intros x Hx. apply (TRF tcid tpos _ Htin'). right.
      unfold in_zr. cbn [fst snd].
      pose proof (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 _ _ HAR3 Htin3) as (G64 & Gs64 & _).
      rewrite EFA in G64. pose proof (fs_frame_bytes_nonneg tcid) as Hnn.
      apply (hdA_sh_in _ _ x G64 Gs64 Hnn). clear - Hx Ht1 Ht2. lia. }
  split; [rewrite MR; exact Ha0|].
  split; [rewrite MM; exact HGA|].
  split; [rewrite MR; exact Q19|].
  split; [rewrite MR; exact Q20|].
  split; [exact Hqr | exact HCH].
Qed.

End c.
End b.
End a.

(* SK is explicit at every use (a Theorem Labs lane ruling 21:57Z; as lib/B/Prog/PcapSourceNextDefs.v): the closure's only global
   sink_head instance is the PLAIN build's, so an inferred SK would make the stream facts vacuous. *)
Arguments nxb_hdA_ph {fx rc} SK {PI}.
Arguments hdA_notE {rc} SK {PI}.
Arguments hdA_chain {rc} SK {PI}.
(* GUARD: SK is passed by position; were it implicit again, it would land on B and these lines would not compile. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) (B : asyms) =>
  nxb_hdA_ph (fx := fx) (rc := rc) SK (PI := PI) B).
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) (B : asyms) =>
  (hdA_notE (rc := rc) SK (PI := PI) B, hdA_chain (rc := rc) SK (PI := PI) B)).
