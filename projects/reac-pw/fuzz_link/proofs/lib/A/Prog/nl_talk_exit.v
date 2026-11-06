(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_td.v, with its module paths, module names and numbers changed; 1190 of its 1221 lines of code are new or changed and 321 lines of the source are left out. *)
(* nl_talk on image A (fuzz_link.asan 0x88974; listing (internal path)
   (internal record, sha256 628c2741aace)): the EXIT phase of the walk (lib/A/Prog/nl_talk_defs.v fixes its two boundaries).

   nt_exit : nt_from POST nt_tail_inv -> nt_from POST nt_exit_inv, the run from NT_exit (+0x4dc) to NT_tail (+0x4f8):
     +0x4dc ld a0, 0x28(s1)            the socket (7)
     +0x4e0 jal fuzz_close              fuzz_close_acontract under SRr_bind: open := 0, closed := closed + 1, misuse
                                        kept (a0 = 7 and open = 1)
     +0x4e4 a1 := 2048; +0x4ec ld a0, 0x18(s1) (the frame's shadow + 4); +0x4f0 jal meta_fill_f8 (LinkWalkSide.v
                                        aj_gx_set_shadow_at: the 16384-byte buffer unusable again)
     +0x4f4 ld s4, 0x20(s1)             the frame
   nt_tail : nt_from (nt_post SK B) nt_tail_inv, the run from NT_tail to the `ret` (+0x56c):
     +0x4f8 .. +0x500 the retired magic 0x45e0360e at s2 (the frame's first word)
     +0x504 beqz s4                     not taken: s4 is the frame address, at least 4096 (the fact on its atom
                                        decides the branch in the engine; the arm +0x51c..+0x528 is never reached)
     +0x508 .. +0x514 a1 := 16672, a0 := s4, jal frame_release_9 (LinkWalkSide.v aj_gx_stack_free_at)
     +0x518 j +0x52c; +0x52c a0 := s11; +0x530 sp := s0 - 192; +0x534 .. +0x564 ra, s0 .. s11 read back;
     +0x568 sp += 192; +0x56c ret (LinkPaLib.v paj_ret_at)
   and the whole Post at the `ret` by LinkWalkSide.v apost_side_gen.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 SetShadowDef StackFreeDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkSide LinkWalkPi.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import fuzz_close_c nl_talk_c nl_talk_defs nl_talk_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. Pure helpers
   ========================================================================== *)

(* A run whose regions have no write window leaves the memory as it was. *)
Lemma ne_frame_nowrite : forall E (rs : smem) (m m' : word -> option byte),
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  frame_of E rs m m' -> m' = m.
Proof.
  intros E rs m m' Hw HF. apply functional_extensionality. intros x. apply HF.
  intros (r & Hin & Ha). pose proof (proj1 (forallb_forall _ rs) Hw r Hin) as Hr.
  apply Z.leb_le in Hr. lia.
Qed.

(* A byte the step left as it was (aview, across two worlds), as mbyte. *)
Lemma ne_mbyte_of_aview : forall segs (H H' : word -> bool) (m m' : word -> option byte) a,
  aview segs H' m' a = aview segs H m a -> mbyte segs (mrestrict H' m') a = mbyte segs (mrestrict H m) a.
Proof.
  intros segs H H' m m' a E. unfold aview in E.
  destruct (mbyte segs (mrestrict H' m') a) as [b'|], (mbyte segs (mrestrict H m) a) as [b|];
    cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* A read-only region (no write window) is kept when its bytes are (aview, across two worlds). *)
Lemma ne_region_kept_ro : forall segs E (H H' : word -> bool) (m m' : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b -> whi <= wlo ->
  (forall a, b + lo <= a < b + hi -> aview segs H' m' a = aview segs H m a) ->
  region_kept segs E (mrestrict H m) (mrestrict H' m') (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
  intros segs E H H' m m' n b lo hi wlo whi cs Hn Hw Hav.
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
  - apply ne_mbyte_of_aview. apply Hav. exact Ha.
  - lia.
Qed.

(* A machine word kept across a step whose eight bytes did not change. *)
Lemma ne_rdword_kept : forall (rd rd' : Z -> option Z) a v,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
  rdword rd a = Some v -> rdword rd' a = Some v.
Proof.
  intros rd rd' a v Hk Hr. unfold rdword in *.
  replace a with (a + 0) at 1 by lia.
  rewrite (Hk 0 ltac:(lia)), (Hk 1 ltac:(lia)), (Hk 2 ltac:(lia)), (Hk 3 ltac:(lia)),
    (Hk 4 ltac:(lia)), (Hk 5 ltac:(lia)), (Hk 6 ltac:(lia)), (Hk 7 ltac:(lia)).
  rewrite Z.add_0_r. exact Hr.
Qed.

(* Two byte lists that agree at every index of [o, o + n), both long enough, have the same slice there. *)
Lemma ne_slice_eq : forall (bs bs' : list byte) o n, 0 <= o -> 0 <= n ->
  o + n <= Z.of_nat (length bs) -> o + n <= Z.of_nat (length bs') ->
  (forall i, o <= i < o + n -> nth_error bs' (Z.to_nat i) = nth_error bs (Z.to_nat i)) ->
  slice bs' o n = slice bs o n.
Proof.
  intros bs bs' o n Ho Hn H1 H2 Hk.
  apply lw_list_ext.
  - rewrite !lw_slice_length by lia. reflexivity.
  - intros k Hkl. rewrite lw_slice_length in Hkl by lia.
    rewrite !lw_slice_nth by lia.
    replace (Z.to_nat o + k)%nat with (Z.to_nat (o + Z.of_nat k)) by lia. apply Hk. lia.
Qed.

Lemma ne_rdn_eq : forall (bs bs' : list byte) o n, 0 <= o -> 0 <= n ->
  o + n <= Z.of_nat (length bs) -> o + n <= Z.of_nat (length bs') ->
  (forall i, o <= i < o + n -> nth_error bs' (Z.to_nat i) = nth_error bs (Z.to_nat i)) ->
  rdn bs' o n = rdn bs o n.
Proof.
  intros bs bs' o n Ho Hn H1 H2 Hk. apply rdn_agree; [lia | lia | lia | lia |].
  intros k Hkl. replace (Z.to_nat o + k)%nat with (Z.to_nat (o + Z.of_nat k)) by lia. apply Hk. lia.
Qed.

(* g_nl lies in one loaded segment, in no read-only segment, and in no runtime-owned static (computations over the
   image's segments and over the instance's owned-static table). *)
Lemma ne_gnl_img_b : existsb (fun s => (Z.of_N (seg_base s) <=? LA_G_NL) &&
    (LA_G_NL + NK_SIZE <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ne_gnl_rw_b : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? LA_G_NL) ||
    (LA_G_NL + NK_SIZE <=? Z.of_N (seg_base s))) tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ne_gnl_own_b : forallb (fun r : Z * Z => (fst r + snd r <=? LA_G_NL) || (LA_G_NL + NK_SIZE <=? fst r))
    Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

(* the relro window [PCAP_RLO, PCAP_RHI) lies in one loaded segment of image A *)
Lemma ne_relro_b : existsb (fun s => (Z.of_N (seg_base s) <=? PCAP_RLO) &&
    (PCAP_RHI <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ne_gnl_img : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> in_img tfibsegs a.
Proof.
  intros a Ha. destruct (proj1 (existsb_exists _ _) ne_gnl_img_b) as (s & Hin & Hs).
  cbv beta in Hs. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hin | lia].
Qed.

Lemma ne_gnl_not_ro_seg : forall s a, In s tfibsegs -> seg_writable s = false ->
  Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s) -> LA_G_NL <= a < LA_G_NL + NK_SIZE -> False.
Proof.
  intros s a Hin Hw Hs Ha. pose proof (proj1 (forallb_forall _ _) ne_gnl_rw_b s Hin) as H.
  cbv beta in H. rewrite Hw in H. cbn [orb] in H. apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma ne_gnl_not_owned : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ Exists (in_zr a) Tfib_owned_static.
Proof.
  intros a Ha Hx. apply Exists_exists in Hx as (r & Hin & Hr). unfold in_zr in Hr.
  pose proof (proj1 (forallb_forall _ _) ne_gnl_own_b r Hin) as H.
  cbv beta in H. apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

(* The journal's window lies above the allocator's ceiling and below 2 ^ 47 (LinkWalkCall.v aj_window_bounds). *)
Lemma ne_aj_bounds : forall segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  alloc_ceiling <= sp0 - STK /\ sp0 + XO <= 2 ^ 47 /\ 0 <= STK /\ 0 <= XO.
Proof.
  intros segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k (H0 & H1 & (memS & HJ & _) & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _). lia.
Qed.

(* The frames the journal's owner took are frames of the current state (LinkWalkCall.v aj_own_frames). *)
Lemma ne_aj_own : forall segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  forall c q, In (c, q) own -> In (c, q) (frames Sc).
Proof.
  intros segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k (_ & _ & (memS & HJ & _) & _) c q Hin.
  pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. apply in_or_app. left. exact Hin.
Qed.

(* ajw at a later state of the same journal whose blocks and owned frames include the call's (LinkWalkCall.v ajw_mono). *)
Lemma ne_ajw_mono : forall B G XO OUT STK sp0 FP ly S lyc Sc own lyc' Sc' own' a,
  ajw B G XO OUT STK sp0 FP ly S lyc Sc own a ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B lyc' Sc')) ->
  (forall x, In x own -> In x own') ->
  (forall c q, frame_addr lyc' c q = frame_addr lyc c q) ->
  ajw B G XO OUT STK sp0 FP ly S lyc' Sc' own' a.
Proof.
  intros B G XO OUT STK sp0 FP ly S lyc Sc own lyc' Sc' own' a Hw Hbl Hown Hfa.
  destruct Hw as [(Haw & Hno) | [HGa | Hout]]; [left | right; left; exact HGa | right; right; exact Hout].
  split; [|exact Hno].
  destruct Haw as [Hs | [(Hf & b & n & Hin & Hr) | [(b & n & Hin & Hn0 & Hr) | (c & q & Hin & Hr)]]].
  - left. exact Hs.
  - right; left. split; [exact Hf|]. exists b, n. split; [exact (Hbl b n Hin) | exact Hr].
  - right; right; left. exists b, n. split; [exact (Hbl b n Hin)|]. split; [exact Hn0 | exact Hr].
  - right; right; right. exists c, q. split; [exact (Hown _ Hin)|]. rewrite !Hfa. exact Hr.
Qed.

(* ==========================================================================
   2. The phase lemmas
   ========================================================================== *)

Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.
Hypothesis CLOSE : fuzz_close_acontract SK SEGS PCAP_RLO PCAP_RHI B.
Hypothesis MF8 : aset_shadow_realizes SEGS B (pa_sigma LS___asan_set_shadow_f8) 0xf8.
Hypothesis SFREE : astack_free_realizes SEGS B (pa_sigma LS___asan_stack_free_9) 9.

(* every byte of the relro window is an image byte (ne_relro_b at SEGS = tfibsegs) *)
Lemma RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Proof.
  intros a Ha. rewrite HSEGS. destruct (proj1 (existsb_exists _ _) ne_relro_b) as (s & Hin & Hs).
  cbv beta in Hs. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hin | lia].
Qed.

(* A byte the step left as it was (aview, across two worlds) stays writable, when it lies in no read-only segment:
   either the later memory holds it, or the segment it lies in is writable and has the byte (wview). *)
Lemma ne_writable_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a ->
  aview SEGS H' m' a = aview SEGS H m a -> writable_at SEGS (mrestrict H m) a ->
  writable_at SEGS (mrestrict H' m') a.
Proof.
  intros H H' m m' a Ha Hro Hav Hw. unfold writable_at, wview in *.
  destruct (mrestrict H' m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [discriminate|].
  destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:E; [|exact Hw].
  unfold aview, mbyte in Hav. rewrite E, E' in Hav. cbn [option_map] in Hav.
  unfold seg_rom, memory_read in Hav.
  change (Z.of_N 1) with 1 in Hav.
  destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 a)) 1) as [seg|] eqn:Hf; [|discriminate].
  destruct (find_segment_hit _ _ _ _ Hf) as (Hin & Hlo & Hhi).
  rewrite unsigned_lit_small in Hlo, Hhi by lia.
  destruct (seg_writable seg) eqn:Hsw.
  - destruct (seg_readable seg); [|discriminate].
    change (N.to_nat 1) with 1%nat in Hav. cbn [segment_read_bytes] in Hav.
    destruct (segment_byte_at (seg_bytes seg) _); [discriminate | discriminate].
  - exfalso. apply Hro. left. exists seg. split; [exact Hin|]. split; [exact Hsw | lia].
Qed.

Lemma ne_vals : BASE = 0x821cc /\ pa_sigma LS_fuzz_close = 0x8267c /\
  pa_sigma LS___asan_set_shadow_f8 = 0x55f94 /\ pa_sigma LS___asan_stack_free_9 = 0x3e2d4.
Proof.
  split; [exact (lv_text LV)|].
  split; [rewrite (lv_sigma LV); reflexivity|].
  split; [rewrite (lv_sigma LV); reflexivity|].
  rewrite (lv_sigma LV); reflexivity.
Qed.

(* g_nl's bytes, in the forms akept's image clause and the read-only set need. *)
Lemma ne_gnl_facts : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ in_roP SEGS PCAP_RLO PCAP_RHI a /\ a < kLowMemEnd.
Proof.
  intros a Ha. rewrite (ts_owned B TB). split; [rewrite HSEGS; exact (ne_gnl_img a Ha)|].
  split; [exact (ne_gnl_not_owned a Ha)|].
  split.
  - intros [(s & Hin & Hw & Hs) | Hr].
    + rewrite HSEGS in Hin. exact (ne_gnl_not_ro_seg s a Hin Hw Hs Ha).
    + unfold PCAP_RLO, PCAP_RHI, LA_G_NL, NK_SIZE in *. lia.
  - unfold LA_G_NL, NK_SIZE, kLowMemEnd in *. lia.
Qed.

(* A read-only byte is an image byte, so it lies below kLowMemEnd = SHADOW_OFF. *)
Lemma ne_ro_img : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> in_img SEGS a.
Proof.
  intros a [(s & Hin & _ & Hs) | Hr]; [exists s; split; [exact Hin | exact Hs] | exact (RELRO_IMG a Hr)].
Qed.

(* arodata_okP moves across a step that keeps every read-only byte outside the runtime's statics and errno. *)
Lemma ne_ro_kept : forall (rd rd' : Z -> option Z),
  arodata_okP SEGS PCAP_RLO PCAP_RHI B rd ->
  (forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> rd' a = rd a) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B rd'.
Proof. intros rd rd' HR HK a Hro Hno Her. rewrite (HK a Hro Hno Her). exact (HR a Hro Hno Her). Qed.

(* The spill slots the exit phase reads (+0x4dc, +0x4ec, +0x4f4): the frame's shadow + 4 at s1 + 24, the frame at
   s1 + 32, the socket at s1 + 40. Atoms: 9 = s1, 18 = s2 (the frame), 24 = s8 (the frame's shadow), 21 = s5 (the
   shadow base). *)
Definition ne_spill : YP09.region := YP09.mkRegion (Some 9%nat) 24 48 0 0
  [YP09.mkChunk 24 (CVal 8 (SOff 24 4)); YP09.mkChunk 32 (CVal 8 (SOff 18 0)); YP09.mkChunk 40 (CVal 8 (SLit 7))].
Definition ne_facts : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (21%nat, mkAF SB SB 0)] [] [].
Definition ne_ss : sstate := mkSS NT_exit sr_atoms [ne_spill] None ne_facts.

Ltac ne_nowrite HF :=
  lazymatch type of HF with frame_of ?Ex ?rs _ _ =>
    apply (ne_frame_nowrite Ex rs); [vm_compute; reflexivity | exact HF] end.

Ltac zrng := try change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); try change (Z.of_N 8) with 8; lia.

(* the numbers of the frame, from the journal at a cut *)
Lemma ne_frame_nums : forall cx fp ly3 S3 (W3 : world SEGS) mem3 md3,
  AR SEGS B ly3 S3 W3 mem3 md3 -> In (NT_CID, fp) (frames S3) ->
  (forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p) ->
  4096 <= nF cx fp /\ nF cx fp + 32768 <= alloc_ceiling /\ nF cx fp mod 32 = 0 /\
  nSH cx fp = SHADOW_OFF + nF cx fp / 8 /\
  (nF cx fp + 32768 <= SHADOW_OFF \/ SHADOW_OFF + alloc_ceiling / 8 <= nF cx fp) /\
  (forall a, nF cx fp <= a < nF cx fp + 32768 -> ~ in_img SEGS a).
Proof.
  intros cx fp ly3 S3 W3 mem3 md3 HAR Hin Hfa.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 NT_CID fp HAR Hin) as (Hf4096 & Hfceil & _).
  destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 NT_CID fp HAR Hin) as (Hal & Happ & _ & _).
  assert (EF : frame_addr ly3 NT_CID fp = nF cx fp) by (rewrite Hfa; reflexivity).
  rewrite EF in Hf4096, Hfceil, Hal, Happ. change (fs_frame_bytes NT_CID) with 32768 in *.
  split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [reflexivity|].
  split.
  - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF.
    destruct Happ as (_ & [Hlow | [Hhi1 Hhi2]]); [left; lia | right; lia].
  - intros a Ha Hi. rewrite <- EF in Ha.
    exact (frm_img SEGS B LAWS ly3 S3 W3 mem3 md3 NT_CID fp a HAR Hin ltac:(unfold in_zr, frame_rng; cbn [fst snd]; exact Ha) Hi).
Qed.

(* The entry state of the exit phase. *)
Lemma ne_entry : forall cx fp (W3 : world SEGS) (ms3 : machine_state),
  nt_shape NT_exit ms3 -> nt_regs cx fp ms3 ->
  nt_at W3 ms3 (n_sp1 cx + NS_SH4) (nSH cx fp + 4) -> nt_at W3 ms3 (n_sp1 cx + NS_FK) (nF cx fp) ->
  nt_at W3 ms3 (n_sp1 cx + NS_FD) NL_FD ->
  2 ^ 46 <= n_sp1 cx <= 2 ^ 47 - 64 -> n_sp1 cx mod 32 = 0 ->
  4096 <= nF cx fp < 2 ^ 47 -> nSH cx fp = SHADOW_OFF + nF cx fp / 8 ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) [])) ne_ss (restrict (w_H W3) ms3).
Proof.
  intros cx fp W3 ms3 Hshp Hrg H24 H32 H40 Hsp Hsp32 HF ESH.
  pose proof Hshp as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr).
  pose proof Hrg as (Rsp & Rs0 & Rs1 & Rs2 & Rs5 & Rs8 & Rgp & Rtp).
  set (E := Eimg (Ereg (ms_regs ms3) [])).
  assert (E9 : ew E 9 = w64 (n_sp1 cx)) by (unfold E; rewrite (ew_Eimg_Ereg_nat _ _ 9 (9%bv : bv 5) eq_refl); exact Rs1).
  assert (E18 : ew E 18 = w64 (nF cx fp)) by (unfold E; rewrite (ew_Eimg_Ereg_nat _ _ 18 (18%bv : bv 5) eq_refl); exact Rs2).
  assert (E21 : ew E 21 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Eimg_Ereg_nat _ _ 21 (21%bv : bv 5) eq_refl); exact Rs5).
  assert (E24 : ew E 24 = w64 (nSH cx fp)) by (unfold E; rewrite (ew_Eimg_Ereg_nat _ _ 24 (24%bv : bv 5) eq_refl); exact Rs8).
  assert (U9 : bv_unsigned (ew E 9) = n_sp1 cx) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
  assert (Ems3 : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + NT_exit)) (ms_mem ms3) (seg_rom SEGS)).
  { clear - Hpc Hresv Hsvc Hrom Hfregs Hfcsr.
    destruct ms3 as [rg fr pcv svp rv fc mm rm];
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
    subst. reflexivity. }
  rewrite Ems3. rewrite restrict_mkst_fx. unfold ne_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, ne_spill.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + assert (HSH : 0 <= nSH cx fp /\ nSH cx fp + 4 < 2 ^ 64) by (rewrite ESH; unfold SHADOW_OFF; lia).
      apply (chunk_ok_val SEGS E _ (n_sp1 cx) 24 8 (SOff 24 4) (nSH cx fp + 4)).
      * cbn [sv_denot]. rewrite E24. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * zrng.
      * exact (val_mem_of_rdword SEGS _ _ _ _ H24).
    + apply (chunk_ok_val SEGS E _ (n_sp1 cx) 32 8 (SOff 18 0) (nF cx fp)).
      * cbn [sv_denot]. rewrite E18. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
      * zrng.
      * zrng.
      * exact (val_mem_of_rdword SEGS _ _ _ _ H32).
    + apply (chunk_ok_val SEGS E _ (n_sp1 cx) 40 8 (SLit 7) NL_FD).
      * reflexivity.
      * unfold NL_FD. zrng.
      * zrng.
      * exact (val_mem_of_rdword SEGS _ _ _ _ H40).
  - cbn; tauto.
  - unfold facts_ok, ne_facts. cbn [f_atoms f_conds f_alias]. split; [|split; [exact I | exact I]].
    cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite U9, E21.
    unfold w64, SB, SHADOW_OFF. rewrite unsigned_lit_small by lia.
    split; [split; [lia|]; split; [change (2 ^ 5) with 32; exact Hsp32 | lia]|].
    split; [split; [lia|]; split; [reflexivity | lia]|]. exact I.
Qed.

(* an ajw byte of the call (nl_talk's write set) is kept by a later callee's akept, stated at the callee's call
   state, outside the callee's window and its exception set and errno *)
Lemma ne_ajw_kept : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    ly1 S1 (W1 : world SEGS) m1 (W2 : world SEGS) m2 slo shi (Ec : Z -> Prop) a,
  gx_ok SEGS B G ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajw B G XO OUT STK sp0 FP ly S lyc Sc own a ->
  akept SEGS B ly1 S1 W1 m1 W2 m2 slo shi Ec ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly1 S1)) ->
  (forall c q, In (c, q) (frames Sc) -> In (c, q) (frames S1)) ->
  (forall c q, frame_addr ly1 c q = frame_addr lyc c q) ->
  ~ (slo <= a < shi) -> ~ Ec a -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly1 S1 W1 m1 W2 m2 slo shi Ec a
    HG HJ Hw (K1 & K2 & K3 & K4 & _) Hbl Hfr Hfa Hwin HnE Herr.
  destruct (ne_aj_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (Hceil & H47 & HSTK & HXO).
  destruct Hw as [(Haw & Hno) | [HGa | (_ & Hout)]].
  - destruct Haw as [Hs | [(_ & b & n & Hin & Hr) | [(b & n & Hin & _ & Hr) | (c & q & Hin & Hr)]]].
    + apply K1; [lia | exact Hwin | exact HnE].
    + replace a with (b + (a - b)) by lia. apply (K2 b n (a - b) (Hbl b n Hin)); [lia|].
      replace (b + (a - b)) with a by lia. exact HnE.
    + replace a with (b + (a - b)) by lia. apply (K2 b n (a - b) (Hbl b n Hin)); [lia|].
      replace (b + (a - b)) with a by lia. exact HnE.
    + apply (K4 c q a (Hfr c q (ne_aj_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ c q Hin))); [|exact HnE].
      unfold frame_rng, in_zr. cbn [fst snd]. rewrite !Hfa. exact Hr.
  - destruct (HG a HGa) as (Hi & Hno). exact (K3 a Hi Hno Herr HnE).
  - apply K1; [lia | exact Hwin | exact HnE].
Qed.

(* The two buffers of nt_bufs_fin, when every byte of each (pointer not NULL, cap at least 1) is the same byte and
   writable at the later memory. *)
Lemma ne_bufs_frame : forall cx (m m' : word -> option byte),
  (n_kind cx <> 0 -> 1 <= n_kindn cx -> forall a, n_kind cx <= a < n_kind cx + n_kindn cx ->
     mbyte SEGS m' a = mbyte SEGS m a /\ (writable_at SEGS m a -> writable_at SEGS m' a)) ->
  (n_alias cx <> 0 -> 1 <= n_aliasn cx -> forall a, n_alias cx <= a < n_alias cx + n_aliasn cx ->
     mbyte SEGS m' a = mbyte SEGS m a /\ (writable_at SEGS m a -> writable_at SEGS m' a)) ->
  nt_bufs_fin cx m -> nt_bufs_fin cx m'.
Proof.
  intros cx m m' HK HA (F1 & F2 & F3 & F4 & F5 & F6).
  assert (Hstr : forall p n, (p <> 0 -> 1 <= n -> forall a, p <= a < p + n ->
            mbyte SEGS m' a = mbyte SEGS m a /\ (writable_at SEGS m a -> writable_at SEGS m' a)) ->
          p <> 0 -> forall s, Z.of_nat (length s) < n -> acstr_at SEGS m p s -> acstr_at SEGS m' p s).
  { intros p n Hk Hp s Hs (Hb & Hnz). split; [|exact Hnz].
    destruct Hb as (Hb0 & Hb1 & Hb2). split; [exact Hb0|]. split; [exact Hb1|].
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite (proj1 (Hk Hp ltac:(lia) (p + Z.of_nat i) ltac:(lia))). exact (Hb2 i ltac:(rewrite length_app; cbn [length]; lia)). }
  assert (Hbuf : forall p n, (p <> 0 -> 1 <= n -> forall a, p <= a < p + n ->
            mbyte SEGS m' a = mbyte SEGS m a /\ (writable_at SEGS m a -> writable_at SEGS m' a)) ->
          p <> 0 -> 1 <= n -> abuf SEGS m p n -> abuf SEGS m' p n).
  { intros p n Hk Hp Hn (junk & Hl & (Hb0 & Hb1 & Hb2) & Hw). exists junk. split; [exact Hl|].
    split; [split; [exact Hb0|]; split; [exact Hb1|]|].
    - intros i Hi. rewrite (proj1 (Hk Hp Hn (p + Z.of_nat i) ltac:(lia))). exact (Hb2 i Hi).
    - intros i Hi. apply (proj2 (Hk Hp Hn (p + i) ltac:(lia))). exact (Hw i Hi). }
  split.
  { intros pay Hp Hk Hn. apply (Hstr (n_kind cx) (n_kindn cx) HK Hk); [|exact (F1 pay Hp Hk Hn)].
    pose proof (cut_text_len pay (n_kindn cx) Hn). lia. }
  split.
  { intros pay Hp Hk Hn. apply (Hstr (n_alias cx) (n_aliasn cx) HA Hk); [|exact (F2 pay Hp Hk Hn)].
    pose proof (cut_text_len pay (n_aliasn cx) Hn). lia. }
  split.
  { intros Hn Hk s Hs Hc. exact (Hstr (n_kind cx) (n_kindn cx) HK Hk s Hs (F3 Hn Hk s Hs Hc)). }
  split.
  { intros Hn Hk s Hs Hc. exact (Hstr (n_alias cx) (n_aliasn cx) HA Hk s Hs (F4 Hn Hk s Hs Hc)). }
  split.
  { intros Hk Hn. exact (Hbuf (n_kind cx) (n_kindn cx) HK Hk Hn (F5 Hk Hn)). }
  { intros Hk Hn. exact (Hbuf (n_alias cx) (n_aliasn cx) HA Hk Hn (F6 Hk Hn)). }
Qed.

(* g_nl's byte list, kept when its bytes are and g_nl stays writable *)
Lemma ne_anlk_frame : forall (m m' : word -> option byte) bs,
  anlk_at SEGS m LA_G_NL bs ->
  (forall i, 0 <= i < NK_SIZE -> mbyte SEGS m' (LA_G_NL + i) = mbyte SEGS m (LA_G_NL + i)) ->
  anlk_at SEGS m' LA_G_NL bs.
Proof.
  intros m m' bs (((Hb0 & Hb1 & Hb2) & Hw) & Hl) Hk.
  split; [|exact Hl]. split; [split; [exact Hb0|]; split; [exact Hb1|]|].
  - intros i Hi. rewrite Hk by lia. exact (Hb2 i Hi).
  - intros i Hi. rewrite HSEGS. apply LA_G_NL_writable. unfold NK_SIZE in Hl. lia.
Qed.

(* a byte of one of the two buffers (pointer not NULL): a write-set byte, apart from errno, g_nl and the frame *)
Lemma ne_buf_byte : forall cx, nt_base SK B cx ->
  forall p n a, (p = n_kind cx /\ n = n_kindn cx \/ p = n_alias cx /\ n = n_aliasn cx) ->
  p <> 0 -> p <= a < p + n ->
  inFP (n_Wr cx) a /\ ~ (as_errno B <= a < as_errno B + 4) /\ (a < LA_G_NL \/ LA_G_NL + NK_SIZE <= a) /\
  (a < spZ (n_regs cx) - NL_TALK_AK \/ spZ (n_regs cx) <= a).
Proof.
  intros cx HB p n a Hpn Hp Ha.
  destruct HB as (_ & _ & HAP & _).
  destruct HAP as (kbs & req & HNLK & HWF & HOPEN & HOC & HCC & HRA & HHV & HERR & HRQ & HRL & HLEN & HMR & HRAQ
    & HHVQ & HFRQ & HGQ & HBK & HBA & HEK & HEA & HKA & HKF & HAF & HCK & HCA).
  unfold apart, apart_frame, apart_gnl in *.
  unfold n_Wr, nl_talk_awr. unfold n_kind, n_kindn, n_alias, n_aliasn in *.
  destruct Hpn as [(-> & ->) | (-> & ->)].
  - destruct (HKF Hp) as [Hf Hg]. pose proof (HEK Hp) as He.
    split; [|split; [lia | split; [lia | lia]]].
    exists (aivl (aarg (n_regs cx) 2) (aarg (n_regs cx) 3)). split; [right; left; reflexivity|].
    unfold aivl. cbn [fst snd]. destruct (Z.eqb_spec (aarg (n_regs cx) 2) 0); [contradiction | lia].
  - destruct (HAF Hp) as [Hf Hg]. pose proof (HEA Hp) as He.
    split; [|split; [lia | split; [lia | lia]]].
    exists (aivl (aarg (n_regs cx) 4) (aarg (n_regs cx) 5)). split; [right; right; left; reflexivity|].
    unfold aivl. cbn [fst snd]. destruct (Z.eqb_spec (aarg (n_regs cx) 4) 0); [contradiction | lia].
Qed.

(* the call of fuzz_close, in the shape the run leaves (pc = the symbol's address) *)
Lemma ne_close_call : forall (W : world SEGS) regs mem md Q,
  SRr SEGS W (cfg_at SEGS FUZZ_CLOSE_A regs mem md) Q ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (pa_sigma LS_fuzz_close)) mem (seg_rom SEGS)) md) Q.
Proof. intros W regs mem md Q H. unfold cfg_at, w64, FUZZ_CLOSE_A in H. rewrite (proj1 (proj2 ne_vals)). exact H. Qed.

(* inFP of fuzz_close's write set is inFP of nl_talk's (g_nl's open .. misuse words lie in g_nl's range) *)
Lemma ne_close_wr : forall cx regs m a, inFP (fuzz_close_awr regs m) a -> inFP (n_Wr cx) a /\
  LA_G_NL + NK_OPEN <= a < LA_G_NL + NK_MISUSE + 4.
Proof.
  intros cx regs m a (r & Hin & Hr). destruct Hin as [<- | []]. cbn [fst snd] in Hr.
  split; [|exact Hr].
  exists (LA_G_NL, LA_G_NL + NK_N_SENT + 4). split; [left; reflexivity|].
  cbn [fst snd]. unfold NK_OPEN, NK_MISUSE, NK_N_SENT in *. lia.
Qed.

(* An ajw byte of the call is none of the bytes of a side frame taken after the call (its range, its shadow, its
   flag byte): the frame is not a frame of the call's state, so it is apart from the call's blocks and frames, below
   the stack window and outside the image. *)
Lemma ne_ajw_not_side : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    ly1 S1 (W1 : world SEGS) mem1 md1 cid pos a,
  gx_ok SEGS B G ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  AR SEGS B ly1 S1 W1 mem1 md1 -> frames S1 = (cid, pos) :: frames Sc ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly1 S1)) ->
  (forall c q, frame_addr ly1 c q = frame_addr lyc c q) ->
  (forall c q, flag_addr ly1 c q = flag_addr lyc c q) ->
  ajw B G XO OUT STK sp0 FP ly S lyc Sc own a ->
  ~ aside_rng lyc cid pos a.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly1 S1 W1 mem1 md1 cid pos a
    HG HJ HAR1 Hfrs1 Hbl Hfa Hfl Hw Hs.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (ne_aj_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (Hceil & H47 & HSTK & HXO).
  assert (Hin1 : In (cid, pos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
  assert (Hs1 : aside_rng ly1 cid pos a)
    by (unfold aside_rng, frame_rng in *; cbn [fst snd] in *; rewrite !Hfa, !Hfl; exact Hs).
  destruct (aside_rng_low SK SEGS B LAWS pa_segs_low ly1 S1 W1 mem1 md1 cid pos a HAR1 Hin1 Hs1) as (Hlow & Hnimg).
  destruct (frames_bounds SEGS B LAWS ly1 S1 W1 mem1 md1 cid pos HAR1 Hin1) as (Hf4 & Hfc & _).
  destruct (al_frames _ _ LAWS ly1 S1 W1 mem1 md1 cid pos HAR1 Hin1) as (_ & Happ & Hfp & Hfsp).
  destruct (al_flag _ _ LAWS ly1 S1 W1 mem1 md1 cid pos HAR1 Hin1) as (_ & Hfo & _ & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  pose proof (shadow_addr_bounds (frame_addr ly1 cid pos) ltac:(lia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr ly1 cid pos + fs_frame_bytes cid) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr ly1 cid pos) (fs_frame_bytes cid) Hnn) as Hse.
  destruct Hw as [(Haw & Hno) | [HGa | (_ & Hout)]].
  2: { exact (Hnimg (proj1 (HG a HGa))). }
  2: { lia. }
  destruct Haw as [Hst | [(_ & b & n & Hin & Hr) | [(b & n & Hin & _ & Hr) | (c & q & Hin & Hr)]]].
  - lia.
  - pose proof (Hbl b n Hin) as Hb1.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR1 Hb1) as (_ & H4096 & Hbc & Hbapp & Hpo & _ & _).
    destruct Hs1 as [Hr1 | [Hr1 | Hr1]].
    + pose proof (sep_block_frame SEGS B LAWS ly1 S1 W1 mem1 md1 b n cid pos HAR1 Hb1 Hin1) as Hd.
      unfold zdisjoint, in_zr, frame_rng in Hd, Hr1. cbn [fst snd] in Hd, Hr1. lia.
    + pose proof (in_app_addr _ _ a Hbapp ltac:(lia)) as Hap. unfold app_addr in Hap.
      unfold in_zr in Hr1. cbn [fst snd] in Hr1. unfold kLowShadowBeg, ASAN_CEIL in Hap. lia.
    + exact (proj2 (Hpo a ltac:(lia)) (eq_ind_r (fun x => aowned B ly1 S1 x) Hfo Hr1)).
  - pose proof (Hbl b n Hin) as Hb1.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR1 Hb1) as (_ & H4096 & Hbc & Hbapp & Hpo & _ & _).
    destruct Hs1 as [Hr1 | [Hr1 | Hr1]].
    + pose proof (sep_block_frame SEGS B LAWS ly1 S1 W1 mem1 md1 b n cid pos HAR1 Hb1 Hin1) as Hd.
      unfold zdisjoint, in_zr, frame_rng in Hd, Hr1. cbn [fst snd] in Hd, Hr1. lia.
    + pose proof (in_app_addr _ _ a Hbapp ltac:(lia)) as Hap. unfold app_addr in Hap.
      unfold in_zr in Hr1. cbn [fst snd] in Hr1. unfold kLowShadowBeg, ASAN_CEIL in Hap. lia.
    + exact (proj2 (Hpo a ltac:(lia)) (eq_ind_r (fun x => aowned B ly1 S1 x) Hfo Hr1)).
  - assert (Hcq : In (c, q) (frames Sc)) by exact (ne_aj_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ c q Hin).
    assert (Hin' : In (c, q) (frames S1)) by (rewrite Hfrs1; right; exact Hcq).
    apply in_split in Hcq as (l2 & l3 & El).
    pose proof (sep_frames_pos SEGS B LAWS ly1 S1 W1 mem1 md1 (cid, pos) (c, q) [] l2 l3 HAR1
      ltac:(rewrite Hfrs1, El; reflexivity)) as Hd.
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
    destruct (frames_bounds SEGS B LAWS ly1 S1 W1 mem1 md1 c q HAR1 Hin') as (Hf4' & Hfc' & _).
    destruct (al_frames _ _ LAWS ly1 S1 W1 mem1 md1 c q HAR1 Hin') as (_ & Happ' & Hfb' & Hfsh').
    pose proof (fs_frame_bytes_nonneg c) as Hnn'.
    pose proof (shadow_addr_bounds (frame_addr ly1 c q) ltac:(lia)) as Hsb1'.
    pose proof (shadow_addr_bounds (frame_addr ly1 c q + fs_frame_bytes c) ltac:(lia)) as Hsb2'.
    pose proof (shadow_range_end (frame_addr ly1 c q) (fs_frame_bytes c) Hnn') as Hse'.
    rewrite <- !Hfa in Hr.
    unfold in_zr in Hr. cbn [fst snd] in Hr.
    clear Hs. destruct Hs1 as [Hs | [Hs | Hs]]; unfold in_zr, frame_rng in Hs; cbn [fst snd] in Hs.
    + destruct Hr as [Hr | Hr].
      * lia.
      * pose proof (in_app_addr _ _ a Happ ltac:(lia)) as Hap. unfold app_addr, kLowShadowBeg, ASAN_CEIL in Hap. lia.
    + destruct Hr as [Hr | Hr].
      * pose proof (in_app_addr _ _ a Happ' ltac:(lia)) as Hap. unfold app_addr, kLowShadowBeg, ASAN_CEIL in Hap. lia.
      * destruct Hd as [Hd | Hd].
        -- pose proof (shadow_mono _ _ Hd). lia.
        -- pose proof (shadow_mono _ _ Hd). lia.
    + subst a. destruct Hr as [Hr | Hr].
      * exact (proj2 (Hfb' _ Hr) Hfo).
      * specialize (Hfsh' (flag_addr ly1 cid pos - shadow_addr (frame_addr ly1 c q)) ltac:(lia)).
        replace (shadow_addr (frame_addr ly1 c q) + (flag_addr ly1 cid pos - shadow_addr (frame_addr ly1 c q)))
          with (flag_addr ly1 cid pos) in Hfsh' by lia.
        exact (proj2 Hfsh' Hfo).
Qed.

Lemma nt_exit : forall POST, nt_from SK B POST (nt_tail_inv B) -> nt_from SK B POST (nt_exit_inv B).
Proof.
intros POST HT cx fp k2 ly3 S3 W3 ms3 md3 HB HJ3 Hfr3 HI.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct ne_vals as (VB & Vcl & Vmf & Vsf).
pose proof HB as (HPRE & HRD & HAP & HNLK0 & HRQ & HRL & HE0 & HE2).
pose proof HPRE as (HJ0 & HGX & HROD & Hret & Hra4 & Hgp & Htp & H16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hnro).
destruct HI as (Hshp & Hrg & Hsv & Hhd & Hsl24 & Hsl32 & Hsl40 & R27 & Hfsh & Hjbk & Hkp & (bs & Hnl & Hgo) & Hows & Hbf).
pose proof Hjbk as (Hk2 & Hperm & Hsfs & Hfrs3 & Hnin & Hfa & Hwit & Hfds3 & Hfs3).
pose proof Hkp as (HK3 & HRO3 & _).
pose proof Hrg as (Rsp & Rs0 & Rs1 & Rs2 & Rs5 & Rs8 & Rgp & Rtp).
destruct (ne_aj_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as (Hceil0 & H47 & HSTK & HXO).
rewrite NL_TALK_AK_val in Hwlo.
pose proof (nt_sp1_range (spZ (n_regs cx)) ltac:(unfold NL_TALK_AFRAME; lia) H16) as Hsp1.
change (nt_sp1 (spZ (n_regs cx))) with (n_sp1 cx) in Hsp1. unfold NL_TALK_AFRAME in Hsp1.
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (HAR0 & _).
assert (Hin3 : In (NT_CID, fp) (frames S3)) by (rewrite Hfr3; left; reflexivity).
destruct (ne_frame_nums cx fp ly3 S3 W3 (ms_mem ms3) md3 HAR3 Hin3 Hfa) as (HF4096 & HFceil & HF32 & ESH & HFsh & HFimg).
(* the model facts of the exchange *)
assert (Hown : k_sock (n_K0 cx) = 0 /\ k_send (n_K0 cx) = 0).
{ unfold talk_owes in Hows. apply andb_prop in Hows as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. auto. }
destruct Hown as [Hks Hksd].
destruct (nt_talk_loop (n_K0 cx) Hks Hksd) as (_ & _ & Hafter & _).
assert (Hsend_after : k_send (talk_after (n_K0 cx)) = 0) by (rewrite Hafter; reflexivity).
assert (Hsock0 : nk_socket_errno (n_kbs cx) = 0) by exact Hks.
pose proof Hgo as (WFbs & Gch & Gnc & Gee & Gni & Gse & Gsd & Gop & Gmi & Gon & Gcl & Gnx & Gst & Gns).
(* g_nl at the call: kbs = n_kbs, and the closed counter has room *)
destruct HAP as (kbs & req & HNLK & HWF & HOPEN & HOC & HCC & HRA & HHV & HERR & HRQ' & HRL' & HLEN & HMR & HRAQ
  & HHVQ & HFRQ & HGQ & HBK & HBA & HEK & HEA & HKA & HKF & HAF & HCK & HCA).
assert (Ekbs : kbs = n_kbs cx).
{ destruct HNLK as ((HA1 & _) & HL1). destruct HNLK0 as ((HA2 & _) & HL2).
  exact (nt_abytes_unique _ _ _ _ HA1 HA2 ltac:(lia)). }
subst kbs.
(* ---- the run from NT_exit to the call of fuzz_close (+0x4e0) ---- *)
pose proof (ne_entry cx fp W3 ms3 Hshp Hrg Hsl24 Hsl32 Hsl40 ltac:(lia) ltac:(lia)
  ltac:(lia) ESH) as HS.
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EW : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
  by (intros n r Hn; subst E; exact (ew_Eimg_Ereg_nat _ _ n r Hn)).
clear HEdef.
assert (SHOK : sh_ok SEGS (SOff 21 0) [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
pose proof (paj_run_x SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUN.
pose proof (paj_run_to_x SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUNTO.
paj_run_tok RUN HS HJ3 SHOK Bspan.
1: { intros a (r & Hin & Ha). vm_compute in Hin. destruct Hin as [<- | []]. cbn in Ha. lia. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into ms1 end.
assert (Emem1 : ms_mem ms1 = ms_mem ms3) by ne_nowrite HF.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (10%bv : bv 5) R10.
rewrite (EW 2%nat (2%bv : bv 5) eq_refl), Rsp in R2.
rewrite (EW 3%nat (3%bv : bv 5) eq_refl), Rgp in R3.
rewrite (EW 4%nat (4%bv : bv 5) eq_refl), Rtp in R4.
assert (Usp1 : spZ (ms_regs ms1) = n_sp1 cx) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Ha0 : aarg (ms_regs ms1) 0 = NL_FD).
{ unfold aarg, argZ. replace (Z_to_bv 5 (10 + 0)) with (10%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite R10. reflexivity. }
(* ---- fuzz_close (+0x4e0), fuzz_close_acontract under SRr_bind ---- *)
apply ne_close_call. eapply SRr_bind.
{ apply (CLOSE (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx)
    (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms1) _ k2 (ms_regs ms1)).
  - unfold apre. split; [exact HJ3|]. split; [exact HGX|]. split; [rewrite Emem1; exact HRO3|].
    split; [rewrite R1; apply ret_ok_codeptr_v; lia|].
    split; [unfold raZ; rewrite R1, VB, unsigned_lit_small by lia; lia|].
    split; [rewrite R3; exact Hgp|]. split; [rewrite R4; exact Htp|].
    split; [rewrite Usp1; lia|]. split; [unfold FUZZ_CLOSE_AK; rewrite Usp1; lia|].
    split; [rewrite Usp1; lia|]. split; [rewrite Hk2; exact Hev|]. split; [unfold aside_room; constructor|].
    split.
    + intros a Ha. destruct (ne_close_wr cx _ _ a Ha) as [Hw _].
      apply (ne_ajw_mono B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
        (n_lyc cx) (n_Sc cx) (n_own cx)); [exact (Hajw a Hw)| | |exact Hfa].
      * intros b m Hb. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hb.
      * intros x Hx. right. exact Hx.
    + intros a Ha. destruct (ne_close_wr cx _ _ a Ha) as [Hw _]. exact (Hnro a Hw).
  - exists bs. split; [rewrite Emem1; exact Hnl|]. split; [exact WFbs|]. rewrite Gcl. exact HCC. }
cbv beta. intros W2 c2 HW2 (ly4 & S4 & regs2 & mem2 & md2 & -> & HJ4 & HP4 & Hfr4 & Hfds4 & Hfs4 & HK4 & _ & ES4 & Eab4 & HCP).
rewrite Z.add_0_r in HJ4.
unfold FUZZ_CLOSE_AK in HK4. rewrite Usp1, Z.sub_0_r in HK4.
pose proof HK4 as (K41 & K42 & K43 & K44 & K45 & K46).
(* the frame addresses at ly4 *)
assert (EFA4 : forall c q, frame_addr ly4 c q = frame_addr (n_lyc cx) c q).
{ intros c q. rewrite (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ4)).
  rewrite (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ0)). reflexivity. }
assert (U9 : bv_unsigned (ew E 9) = n_sp1 cx)
  by (rewrite (EW 9%nat (9%bv : bv 5) eq_refl), Rs1; unfold w64; apply unsigned_lit_small; lia).
(* the spill region after the call: fuzz_close kept the stack (akept clause 1) *)
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP4 [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  apply (ne_region_kept_ro SEGS E (w_H W3) (w_H W2) (ms_mem ms1) mem2 9 (n_sp1 cx)); [exact U9 | lia |].
  intros a Ha. apply K41; [lia | lia |].
  intros Hc. destruct (ne_close_wr cx _ _ a Hc) as [_ Hc2]. unfold LA_G_NL, NK_OPEN, NK_MISUSE in Hc2. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs2) CLOB)) as E2 eqn:HE2def in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2def; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (EW2 : forall n, (n < 40)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2def; apply ew_havoc_old; exact Hn).
clear HE2def.
assert (SHOK2 : sh_ok SEGS (SOff 21 0) [] E2 (mrestrict (w_H W2) mem2)) by constructor.
rewrite R1.
(* ---- +0x4e4 .. +0x4f0: a1 := 2048, a0 := the frame's shadow + 4, the call of meta_fill_f8 ---- *)
paj_run_tok RUN HS HJ4 SHOK2 Bspan.
1: { intros a (r & Hin & Ha). vm_compute in Hin. destruct Hin as [<- | []]. cbn in Ha. lia. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into ms2 end.
assert (Emem2 : ms_mem ms2 = mem2) by ne_nowrite HF.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) R1b. prreg HS (2%bv : bv 5) R2b. prreg HS (3%bv : bv 5) R3b. prreg HS (4%bv : bv 5) R4b.
prreg HS (10%bv : bv 5) R10b. prreg HS (11%bv : bv 5) R11b.
rewrite (EW2 24%nat ltac:(lia)), (EW 24%nat (24%bv : bv 5) eq_refl), Rs8 in R10b.
unfold w64 in R10b. rewrite unsigned_lit_small in R10b by (rewrite ESH; unfold SHADOW_OFF; lia).
rewrite (EW2 2%nat ltac:(lia)), (EW 2%nat (2%bv : bv 5) eq_refl), Rsp in R2b.
rewrite (EW2 3%nat ltac:(lia)), (EW 3%nat (3%bv : bv 5) eq_refl), Rgp in R3b.
rewrite (EW2 4%nat ltac:(lia)), (EW 4%nat (4%bv : bv 5) eq_refl), Rtp in R4b.
assert (Usp2 : spZ (ms_regs ms2) = n_sp1 cx) by (unfold spZ; rewrite R2b; unfold w64; apply unsigned_lit_small; lia).
(* ---- meta_fill_f8 (+0x4f0): LinkWalkSide.v aj_gx_set_shadow_at ---- *)
eapply SRr_bind.
{ apply (aj_gx_set_shadow_at SK SEGS B LAWS pa_segs_low (pa_sigma LS___asan_set_shadow_f8) 248 MF8
    (n_G cx) (n_XO cx) (n_OUT cx) W2 (ms_regs ms2) (ms_mem ms2) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly4 S4 _ k2 NT_CID fp (nSH cx fp + 4) 2048
    (getr (ms_regs ms2) 1) HGX HJ4 (or_introl eq_refl)).
  - exact R10b.
  - exact R11b.
  - lia.
  - rewrite EFA4. change (frame_addr (n_lyc cx) NT_CID fp) with (nF cx fp). unfold shadow_addr. rewrite ESH. lia.
  - rewrite EFA4. change (frame_addr (n_lyc cx) NT_CID fp) with (nF cx fp). unfold shadow_addr. rewrite ESH.
    change (fs_frame_bytes NT_CID / 8) with 4096. lia.
  - rewrite Usp2. lia.
  - rewrite Usp2. unfold ESTACK. lia.
  - rewrite Usp2. lia.
  - rewrite R3b. exact Hgp.
  - rewrite R4b. exact Htp.
  - reflexivity.
  - rewrite R1b. apply ret_ok_codeptr_v; lia. }
cbv beta. intros W2' c2 _ (-> & regs3 & mem3 & md3' & -> & HJ5 & HP5 & Hset5 & Hun5 & Hpres5 & Hsbm5).
rewrite Emem2 in Hun5, Hpres5.
jafter_call_keep_pi HS 60%nat regs3 (mrestrict (w_H W2) mem3) HP5 [0]%nat HS3.
match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. rewrite Emem2. apply Forall_cons; [|apply Forall_nil].
  assert (U9b : bv_unsigned (ew E2 9) = n_sp1 cx) by (rewrite (EW2 9%nat ltac:(lia)); exact U9).
  apply (ne_region_kept_ro SEGS E2 (w_H W2) (w_H W2) mem2 mem3 9 (n_sp1 cx)); [exact U9b | lia |].
  intros a Ha. apply Hun5; [lia|]. rewrite ESH. unfold SHADOW_OFF. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E2 60 (map (getr regs3) CLOB)) as E3 eqn:HE3def in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3def; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (EW3 : forall n, (n < 60)%nat -> ew E3 n = ew E2 n) by (intros n Hn; rewrite HE3def; apply ew_havoc_old; exact Hn).
clear HE3def.
assert (SHOK3 : sh_ok SEGS (SOff 21 0) [] E3 (mrestrict (w_H W2) mem3)) by constructor.
rewrite R1b.
(* ---- +0x4f4: s4 := the frame, to NT_tail ---- *)
paj_run_to_tok RUNTO HS HJ5 SHOK3 Bspan NT_tail.
1: { intros a (r & Hin & Ha). vm_compute in Hin. destruct Hin as [<- | []]. cbn in Ha. lia. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms4 end.
assert (Emem4 : ms_mem ms4 = mem3) by ne_nowrite HF.
clear HF HFr HG.
assert (EWF : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E3 n = getr (ms_regs ms3) r).
{ intros n r Hn Hr. rewrite (EW3 n ltac:(lia)), (EW2 n ltac:(lia)). exact (EW n r Hr). }
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
rewrite (EWF 2%nat (2%bv : bv 5) ltac:(lia) eq_refl) in Q2. rewrite (EWF 3%nat (3%bv : bv 5) ltac:(lia) eq_refl) in Q3.
rewrite (EWF 4%nat (4%bv : bv 5) ltac:(lia) eq_refl) in Q4. rewrite (EWF 8%nat (8%bv : bv 5) ltac:(lia) eq_refl) in Q8.
rewrite (EWF 9%nat (9%bv : bv 5) ltac:(lia) eq_refl) in Q9. rewrite (EWF 18%nat (18%bv : bv 5) ltac:(lia) eq_refl) in Q18.
rewrite (EWF 18%nat (18%bv : bv 5) ltac:(lia) eq_refl) in Q20. rewrite (EWF 21%nat (21%bv : bv 5) ltac:(lia) eq_refl) in Q21.
rewrite (EWF 24%nat (24%bv : bv 5) ltac:(lia) eq_refl) in Q24. rewrite (EWF 27%nat (27%bv : bv 5) ltac:(lia) eq_refl) in Q27.
pose proof (st_ok_pi_restrict_mkst (w_H W2) _ _ ms4 HS eq_refl) as Ems4. cbn [ss_pc] in Ems4.
destruct (ms_shape_mkst SEGS ms4 _ _ _ Ems4) as (Hrv4 & Hsc4 & Hrom4 & Hfrg4 & Hfcs4 & Hpc4).
(* ---- what the phase kept ---- *)
assert (Hgnl_not_close : forall a, (a < LA_G_NL \/ LA_G_NL + NK_SIZE <= a) ->
          ~ inFP (fuzz_close_awr (ms_regs ms1) (rdW W3 (ms_mem ms1))) a).
{ intros a Ha Hc. destruct (ne_close_wr cx _ _ a Hc) as [_ Hc2]. unfold NK_OPEN, NK_MISUSE, NK_SIZE in *. lia. }
assert (UNst : forall a, alloc_ceiling <= a < 2 ^ 64 ->
          aview SEGS (w_H W2) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite Emem4. rewrite (Hun5 a ltac:(lia) ltac:(rewrite ESH; unfold SHADOW_OFF; lia)).
  rewrite (K41 a Ha ltac:(lia) (Hgnl_not_close a ltac:(unfold LA_G_NL, NK_SIZE; lia))). rewrite Emem1. reflexivity. }
assert (UNfr : forall a, nF cx fp <= a < nF cx fp + 32768 ->
          aview SEGS (w_H W2) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite Emem4.
  rewrite (Hun5 a ltac:(lia) ltac:(rewrite ESH; destruct HFsh; unfold SHADOW_OFF in *; lia)).
  assert (Hna : ~ inFP (fuzz_close_awr (ms_regs ms1) (rdW W3 (ms_mem ms1))) a).
  { intros Hc. destruct (ne_close_wr cx _ _ a Hc) as [_ Hc2].
    destruct (ne_gnl_facts a ltac:(unfold NK_OPEN, NK_MISUSE, NK_SIZE in *; lia)) as (Hi & _). exact (HFimg a Ha Hi). }
  rewrite (K44 NT_CID fp a Hin3); [rewrite Emem1; reflexivity | | exact Hna].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa. change (frame_addr (n_lyc cx) NT_CID fp) with (nF cx fp).
  change (fs_frame_bytes NT_CID) with 32768. lia. }
pose proof (ne_gnl_facts) as GF.
(* g_nl after fuzz_close *)
destruct (HCP bs ltac:(rewrite Emem1; exact Hnl)) as (bs' & Hnl' & WF' & HR10' & Hop' & Hon' & Hcl' & Hmi').
assert (Lbs : Z.of_nat (length bs) = NK_SIZE) by (destruct Hnl as (_ & L); exact L).
assert (Lbs' : Z.of_nat (length bs') = NK_SIZE) by (destruct Hnl' as (_ & L); exact L).
assert (Hout : forall i, 0 <= i < NK_SIZE -> ~ (NK_OPEN <= i < NK_MISUSE + 4) ->
          nth_error bs' (Z.to_nat i) = nth_error bs (Z.to_nat i)).
{ intros i Hi Hni.
  destruct Hnl' as (((_ & _ & B2') & _) & _). destruct Hnl as (((_ & _ & B2) & _) & _).
  rewrite <- (B2' (Z.to_nat i) ltac:(lia)), <- (B2 (Z.to_nat i) ltac:(lia)).
  rewrite Z2Nat.id by lia. rewrite <- Emem1. apply ne_mbyte_of_aview.
  destruct (GF (LA_G_NL + i) ltac:(lia)) as (Hi1 & Hi2 & _ & _).
  apply (K43 (LA_G_NL + i) Hi1 Hi2).
  - destruct HERR as (_ & _ & _ & _ & Hge). unfold apart_gnl in Hge. unfold NK_SIZE in *. lia.
  - intros Hc. destruct (ne_close_wr cx _ _ _ Hc) as [_ Hc2]. lia. }
assert (Frd : forall o n, 0 <= o -> 0 <= n -> o + n <= NK_SIZE -> o + n <= NK_OPEN -> rdn bs' o n = rdn bs o n).
{ intros o n H0 H1 H2 H3. apply ne_rdn_eq; [lia | lia | lia | lia |]. intros i Hi. apply Hout; [lia | lia]. }
assert (Frd2 : forall o n, NK_MISUSE + 4 <= o -> 0 <= n -> o + n <= NK_SIZE -> rdn bs' o n = rdn bs o n).
{ intros o n H0 H1 H2. apply ne_rdn_eq; [unfold NK_MISUSE in *; lia | lia | lia | lia |].
  intros i Hi. apply Hout; [unfold NK_MISUSE in *; lia | lia]. }
assert (Fch : nk_chunks bs' = nk_chunks bs).
{ apply (nt_nk_chunks_keep bs bs' WFbs). apply ne_slice_eq; [lia | unfold NK_NEXT; lia | unfold NK_NEXT, NK_SIZE in *; lia
    | unfold NK_NEXT, NK_SIZE in *; lia |].
  intros i Hi. apply Hout; unfold NK_NEXT, NK_SIZE, NK_OPEN, NK_MISUSE in *; lia. }
assert (Fst : nk_sent bs' = nk_sent bs).
{ apply (nt_nk_sent_keep bs bs' WFbs). apply ne_slice_eq; [unfold NK_SENT; lia | unfold NK_SENT, NK_N_SENT; lia
    | unfold NK_SENT, NK_N_SENT, NK_SIZE in *; lia | unfold NK_SENT, NK_N_SENT, NK_SIZE in *; lia |].
  intros i Hi. apply Hout; unfold NK_SENT, NK_N_SENT, NK_SIZE, NK_OPEN, NK_MISUSE in *; lia. }
assert (Fee : nk_end_errno bs' = nk_end_errno bs)
  by (unfold nk_end_errno, fld_u32; apply Frd; unfold NK_END_ERRNO, NK_SIZE, NK_OPEN; lia).
assert (Fse : nk_socket_errno bs' = nk_socket_errno bs)
  by (unfold nk_socket_errno, fld_u32; apply Frd; unfold NK_SOCKET_ERRNO, NK_SIZE, NK_OPEN; lia).
assert (Fsd : nk_send_errno bs' = nk_send_errno bs)
  by (unfold nk_send_errno, fld_u32; apply Frd; unfold NK_SEND_ERRNO, NK_SIZE, NK_OPEN; lia).
assert (Fnx : nk_next bs' = nk_next bs)
  by (unfold nk_next, fld_u32; apply Frd; unfold NK_NEXT, NK_SIZE, NK_OPEN; lia).
assert (Fni : nk_n_if bs' = nk_n_if bs)
  by (unfold nk_n_if, fld_u32; apply Frd2; unfold NK_N_IF, NK_SIZE, NK_MISUSE; lia).
assert (Fns : nk_n_sent bs' = nk_n_sent bs)
  by (unfold nk_n_sent, fld_u32; apply Frd2; unfold NK_N_SENT, NK_SIZE, NK_MISUSE; lia).
assert (Hfin : nt_gnl_fin cx bs').
{ unfold nt_gnl_fin.
  split; [exact WF'|].
  split; [rewrite Fch; exact Gch|].
  split; [rewrite Fee; exact Gee|].
  split; [rewrite Fni; exact Gni|].
  split; [rewrite Fse; exact Gse|].
  split; [rewrite Fsd, Gsd, Hsend_after; reflexivity|].
  split; [rewrite Fnx; exact Gnx|].
  split; [rewrite Fst; exact Gst|].
  split; [rewrite Fns, Fst; exact Gns|].
  split; [exact Hop'|].
  split; [rewrite Hmi', Ha0, Gop; exact Gmi|].
  split; [rewrite Hon', Hcl', Gon, Gcl; lia|].
  split; [intros Hne; exfalso; exact (Hne Hsock0)|].
  intros _. rewrite Hon', Gon. reflexivity. }
assert (Hnl4 : anlk_at SEGS (rdW W2 (ms_mem ms4)) LA_G_NL bs').
{ apply (ne_anlk_frame (rdW W2 mem2)); [exact Hnl'|]. intros i Hi.
  rewrite Emem4. apply ne_mbyte_of_aview. apply Hun5; [unfold LA_G_NL, NK_SIZE in *; lia|].
  rewrite ESH. unfold SHADOW_OFF, LA_G_NL, NK_SIZE in *. lia. }
(* the caller's buffers *)
assert (Hfl3 : forall c q, flag_addr ly3 c q = flag_addr (n_lyc cx) c q).
{ intros c q. rewrite (proj2 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ3)).
  rewrite (proj2 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ0)). reflexivity. }
assert (UNbuf : forall p0 n0 a, (p0 = n_kind cx /\ n0 = n_kindn cx \/ p0 = n_alias cx /\ n0 = n_aliasn cx) ->
          p0 <> 0 -> p0 <= a < p0 + n0 -> 0 <= a < 2 ^ 64 ->
          aview SEGS (w_H W2) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a /\
          ~ in_roP SEGS PCAP_RLO PCAP_RHI a).
{ intros p0 n0 a Hpn Hp Ha Hab.
  destruct (ne_buf_byte cx HB p0 n0 a Hpn Hp Ha) as (HwFP & Herr & Hgnl & Hfrm).
  split; [|exact (Hnro a HwFP)].
  pose proof (Hajw a HwFP) as Hw.
  assert (Hns : ~ aside_rng (n_lyc cx) NT_CID fp a).
  { apply (ne_ajw_not_side (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
      (n_W0 cx) (n_mem0 cx) (n_md0 cx) (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx)
      ly3 S3 W3 (ms_mem ms3) md3 NT_CID fp a HGX HJ0 HAR3 Hfr3); [| exact Hfa | exact Hfl3 | exact Hw].
    intros b m Hb. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hb. }
  rewrite Emem4. rewrite Hun5.
  2: { lia. }
  2: { intros Hq. apply Hns. right; left. unfold in_zr. cbn [fst snd].
       change (frame_addr (n_lyc cx) NT_CID fp) with (nF cx fp). unfold shadow_addr. rewrite ESH in Hq.
       change (fs_frame_bytes NT_CID / 8) with 4096. lia. }
  rewrite (ne_ajw_kept (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
      (n_W0 cx) (n_mem0 cx) (n_md0 cx) (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx)
      ly3 S3 W3 (ms_mem ms1) W2 mem2 (n_sp1 cx) (n_sp1 cx) _ a HGX HJ0 Hw HK4).
  - rewrite Emem1. reflexivity.
  - intros b m Hb. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hb.
  - intros c q Hc. rewrite Hfr3. right. exact Hc.
  - exact Hfa.
  - lia.
  - exact (Hgnl_not_close a Hgnl).
  - exact Herr. }
assert (Hbf4 : nt_bufs_fin cx (rdW W2 (ms_mem ms4))).
{ pose proof Hbf as (_ & _ & _ & _ & Hb5 & Hb6).
  apply (ne_bufs_frame cx (rdW W3 (ms_mem ms3))); [| | exact Hbf].
  - intros Hk Hn a Ha. destruct (Hb5 Hk Hn) as (junk & Hjl & (Hj0 & Hj1 & _) & _).
    destruct (UNbuf (n_kind cx) (n_kindn cx) a (or_introl (conj eq_refl eq_refl)) Hk Ha ltac:(lia)) as [Hav Hro].
    split; [exact (ne_mbyte_of_aview _ _ _ _ _ _ Hav)|].
    apply (ne_writable_of_aview _ _ _ _ a); [lia | exact Hro | exact Hav].
  - intros Hk Hn a Ha. destruct (Hb6 Hk Hn) as (junk & Hjl & (Hj0 & Hj1 & _) & _).
    destruct (UNbuf (n_alias cx) (n_aliasn cx) a (or_intror (conj eq_refl eq_refl)) Hk Ha ltac:(lia)) as [Hav Hro].
    split; [exact (ne_mbyte_of_aview _ _ _ _ _ _ Hav)|].
    apply (ne_writable_of_aview _ _ _ _ a); [lia | exact Hro | exact Hav]. }
(* the kept clause *)
rewrite <- Emem1 in HK3.
assert (HKc1 : akept SEGS B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W2 mem2
          (spZ (n_regs cx) - NL_TALK_AK) (spZ (n_regs cx)) (fun a => n_E cx a \/ aside_rng (n_lyc cx) NT_CID fp a)).
{ apply (akept_trans_ly SK SEGS B LAWS pa_segs_low (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) ly3 S3 W3 (ms_mem ms1)
    W2 mem2 (spZ (n_regs cx) - NL_TALK_AK) (spZ (n_regs cx)) (n_sp1 cx) (n_sp1 cx) (fun a => n_E cx a \/ aside_rng (n_lyc cx) NT_CID fp a)
    (fun a => inFP (fuzz_close_awr (ms_regs ms1) (rdW W3 (ms_mem ms1))) a) (fun a => n_E cx a \/ aside_rng (n_lyc cx) NT_CID fp a)); [rewrite NL_TALK_AK_val; lia | lia | exact HK3 | exact HK4
    | rewrite NL_TALK_AK_val; lia | lia | | | exact Hfa | intros a H; exact H |].
  - intros b m Hb. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hb.
  - intros f Hf. rewrite Hfr3. right. exact Hf.
  - intros a Ha. left. exact (proj1 (ne_close_wr cx _ _ a Ha)). }
assert (HKc2 : akept SEGS B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W2 (ms_mem ms4)
          (spZ (n_regs cx) - NL_TALK_AK) (spZ (n_regs cx)) (fun a => n_E cx a \/ aside_rng (n_lyc cx) NT_CID fp a)).
{ rewrite Emem4.
  apply (akept_step SK SEGS B LAWS pa_segs_low (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) W2 mem2 W2 mem3
    (spZ (n_regs cx) - NL_TALK_AK) (spZ (n_regs cx)) (fun a => n_E cx a \/ aside_rng (n_lyc cx) NT_CID fp a) (fun a => n_E cx a \/ aside_rng (n_lyc cx) NT_CID fp a)
    (fun a => nSH cx fp + 4 <= a < nSH cx fp + 4 + 2048) HAR0); [rewrite NL_TALK_AK_val; lia | lia | exact HKc1
    | intros a Ha Hn; exact (Hun5 a Ha Hn) | intros a _ Hp; exact (Hpres5 a Hp) | intros a H; exact H |].
  intros a Ha. left. right. right. left. unfold in_zr. cbn [fst snd].
  change (frame_addr (n_lyc cx) NT_CID fp) with (nF cx fp). unfold shadow_addr. rewrite ESH in Ha.
  change (fs_frame_bytes NT_CID / 8) with 4096. lia. }
assert (HRO4 : arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms4))).
{ apply (ne_ro_kept _ _ HRO3). intros a Hro Hno Her.
  pose proof (ne_ro_img a Hro) as Hi. pose proof (pa_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite Emem4, Hun5 by (try lia; rewrite ESH; unfold SHADOW_OFF; lia).
  rewrite (K43 a Hi Hno Her); [rewrite Emem1; reflexivity|].
  intros Hc. destruct (ne_close_wr cx _ _ a Hc) as [_ Hc2].
  destruct (GF a ltac:(unfold NK_OPEN, NK_MISUSE, NK_SIZE in *; lia)) as (_ & _ & Hnr & _). exact (Hnr Hro). }
(* ---- the boundary NT_tail ---- *)
assert (Hfr4' : frames S4 = (NT_CID, fp) :: frames (n_Sc cx)) by (rewrite Hfr4; exact Hfr3).
apply (HT cx fp k2 ly4 S4 W2 ms4 _ HB HJ5 Hfr4').
unfold nt_tail_inv.
split.
{ unfold nt_shape. split; [rewrite Hpc4; reflexivity|]. split; [exact Hrv4|]. split; [exact Hsc4|].
  split; [exact Hrom4|]. split; [exact Hfrg4 | exact Hfcs4]. }
split.
{ unfold nt_regs. rewrite Q2, Q8, Q9, Q18, Q21, Q24, Q3, Q4. exact Hrg. }
split.
{ destruct Hsv as (Hsv0 & Hsv1). split.
  - eapply ne_rdword_kept; [intros i Hi; apply UNst; lia | exact Hsv0].
  - intros j Hj. eapply ne_rdword_kept; [intros i Hi; apply UNst; lia | exact (Hsv1 j Hj)]. }
split.
{ unfold nt_header. destruct Hhd as (Hh0 & Hh8 & Hh16 & Hhf). change (fs_frame_bytes NT_CID) with 32768 in *.
  split; [eapply ne_rdword_kept; [intros i Hi; apply UNfr; lia | exact Hh0]|].
  split; [eapply ne_rdword_kept; [intros i Hi; apply UNfr; lia | exact Hh8]|].
  split; [eapply ne_rdword_kept; [intros i Hi; apply UNfr; lia | exact Hh16]|].
  eapply ne_rdword_kept; [intros i Hi; apply UNfr; lia | exact Hhf]. }
split; [rewrite Q20; exact Rs2|].
split; [rewrite Q27; exact R27|].
split.
{ unfold nt_jbk. split; [exact Hk2|]. split; [exact (Permutation_trans Eab4 Hperm)|].
  split; [exact (set_fs_trans S3 S4 (n_Sc cx) Hsfs ES4)|]. split; [exact Hfr4'|]. split; [exact Hnin|].
  split; [exact EFA4|]. split; [exact Hwit|].
  split.
  - rewrite (proj1 (wvb_fds_fs _ _ _)), (same_but_materialized_wvb _ _ Hsbm5).
    repeat rewrite (proj1 (wvb_fds_fs _ _ _)). rewrite Hfds4. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). exact Hfds3.
  - rewrite (proj2 (wvb_fds_fs _ _ _)), (same_but_materialized_wvb _ _ Hsbm5).
    repeat rewrite (proj2 (wvb_fds_fs _ _ _)). rewrite Hfs4. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). exact Hfs3. }
split; [split; [exact HKc2|]; split; [exact HRO4 | intros a H; exact H]|].
split; [exists bs'; split; [exact Hnl4 | exact Hfin]|].
exact Hbf4.
Qed.


(* ---- the tail: its entry state ---- *)

(* Atoms: 8 = s0 (the entry sp), 18 = s2 (the frame, written at +0x500), 20 = s4 (the frame; its fact decides
   `beqz s4` at +0x504), 21 = s5 (the shadow base), 540 .. 552 the entry values of ra, s0, s1, s2 .. s11, which
   the epilogue reloads from the machine frame (+0x534 .. +0x564: ra at sp0 - 8, s0 at sp0 - 16, .., s11 at
   sp0 - 104). *)
Definition nl_saved_chunks : list YP09.chunk :=
  [ YP09.mkChunk (-104) (CVal 8 (SOff 552 0)); YP09.mkChunk (-96) (CVal 8 (SOff 551 0));
    YP09.mkChunk (-88) (CVal 8 (SOff 550 0)); YP09.mkChunk (-80) (CVal 8 (SOff 549 0));
    YP09.mkChunk (-72) (CVal 8 (SOff 548 0)); YP09.mkChunk (-64) (CVal 8 (SOff 547 0));
    YP09.mkChunk (-56) (CVal 8 (SOff 546 0)); YP09.mkChunk (-48) (CVal 8 (SOff 545 0));
    YP09.mkChunk (-40) (CVal 8 (SOff 544 0)); YP09.mkChunk (-32) (CVal 8 (SOff 543 0));
    YP09.mkChunk (-24) (CVal 8 (SOff 542 0)); YP09.mkChunk (-16) (CVal 8 (SOff 541 0));
    YP09.mkChunk (-8) (CVal 8 (SOff 540 0)) ].
Definition nl_frame : YP09.region := YP09.mkRegion (Some 18%nat) 0 8 0 8 [].
Definition nl_saved : YP09.region := YP09.mkRegion (Some 8%nat) (-104) 0 0 0 nl_saved_chunks.
Definition nl_facts : facts := mkFacts [(18%nat, HPTR 5); (20%nat, HPTR 0); (21%nat, mkAF SB SB 0)] [] [].
Definition nl_ss : sstate := mkSS NT_tail sr_atoms [nl_frame; nl_saved] None nl_facts.

Definition nl_env (cx : ntcx) (ms3 : machine_state) : env :=
  havoc (Eimg (Ereg (ms_regs ms3) [])) 540
    [getr (n_regs cx) 1; getr (n_regs cx) 8; getr (n_regs cx) 9; getr (n_regs cx) 18;
     getr (n_regs cx) 19; getr (n_regs cx) 20; getr (n_regs cx) 21; getr (n_regs cx) 22;
     getr (n_regs cx) 23; getr (n_regs cx) 24; getr (n_regs cx) 25; getr (n_regs cx) 26;
     getr (n_regs cx) 27].

(* A saved-register chunk from the word the invariant gives (PcapSourceNextExit.v nx_saved_chunk). *)
Lemma nl_saved_chunk : forall (E : env) (H : word -> bool) (mem : word -> option byte) n sp off (w : word),
  ew E n = w -> rdword (aview SEGS H mem) (sp + off) = Some (bv_unsigned w) ->
  YP09.chunk_ok SEGS E (mrestrict H mem) sp (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
  intros E H mem n sp off w Hn Hr.
  apply (chunk_ok_val SEGS E (mrestrict H mem) sp off 8 (SOff n 0) (bv_unsigned w)).
  - cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (bv_unsigned_in_range 64 w) as Q. change (bv_modulus 64) with (2 ^ 64) in Q.
    change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Q.
  - cbn; lia.
  - exact (val_mem_of_rdword SEGS _ _ _ _ Hr).
Qed.

Lemma nl_entry : forall cx fp (W3 : world SEGS) (ms3 : machine_state),
  nt_shape NT_tail ms3 -> nt_regs cx fp ms3 -> nt_saved cx W3 ms3 ->
  getr (ms_regs ms3) 20 = w64 (nF cx fp) ->
  4096 <= nF cx fp -> nF cx fp mod 32 = 0 -> nF cx fp + 32768 <= alloc_ceiling ->
  alloc_ceiling <= spZ (n_regs cx) - 104 -> spZ (n_regs cx) <= 2 ^ 47 ->
  (forall a, nF cx fp <= a < nF cx fp + 8 -> apresent (w_H W3) (ms_mem ms3) a) ->
  st_ok_pi SEGS VAL (nl_env cx ms3) nl_ss (restrict (w_H W3) ms3).
Proof.
  intros cx fp W3 ms3 Hshp Hrg Hsv R20 HF HF32 HFc HFsp Hsp47 HFp.
  pose proof Hshp as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr).
  pose proof Hrg as (Rsp & Rs0 & Rs1 & Rs2 & Rs5 & Rs8 & Rgp & Rtp).
  pose proof Hsv as (Hra_sv & Hsv').
  set (E := nl_env cx ms3).
  assert (EWlow : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E, nl_env. rewrite ew_havoc_old by lia. exact (ew_Eimg_Ereg_nat _ _ n r Hr). }
  assert (E8 : ew E 8 = w64 (spZ (n_regs cx))) by (rewrite (EWlow 8%nat (8%bv : bv 5) ltac:(lia) eq_refl); exact Rs0).
  assert (E18 : ew E 18 = w64 (nF cx fp)) by (rewrite (EWlow 18%nat (18%bv : bv 5) ltac:(lia) eq_refl); exact Rs2).
  assert (E20 : ew E 20 = w64 (nF cx fp)) by (rewrite (EWlow 20%nat (20%bv : bv 5) ltac:(lia) eq_refl); exact R20).
  assert (E21 : ew E 21 = w64 SHADOW_OFF) by (rewrite (EWlow 21%nat (21%bv : bv 5) ltac:(lia) eq_refl); exact Rs5).
  pose proof (bv_unsigned_in_range 64 (getr (n_regs cx) 2)) as Hsprng. change (bv_modulus 64) with (2 ^ 64) in Hsprng.
  fold (spZ (n_regs cx)) in Hsprng.
  assert (U8 : bv_unsigned (ew E 8) = spZ (n_regs cx)) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
  assert (U18 : bv_unsigned (ew E 18) = nF cx fp) by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew E 20) = nF cx fp) by (rewrite E20; unfold w64; apply unsigned_lit_small; lia).
  assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF) by (rewrite E21; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (ES : forall j, (j < 13)%nat -> ew E (540 + j) = nth j
    [getr (n_regs cx) 1; getr (n_regs cx) 8; getr (n_regs cx) 9; getr (n_regs cx) 18;
     getr (n_regs cx) 19; getr (n_regs cx) 20; getr (n_regs cx) 21; getr (n_regs cx) 22;
     getr (n_regs cx) 23; getr (n_regs cx) 24; getr (n_regs cx) 25; getr (n_regs cx) 26;
     getr (n_regs cx) 27] (Z_to_bv 64 0)).
  { intros j Hj. unfold E, nl_env. apply ew_havoc_new. cbn [length]. lia. }
  assert (Ems3 : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + NT_tail)) (ms_mem ms3) (seg_rom SEGS)).
  { clear - Hpc Hresv Hsvc Hrom Hfregs Hfcsr.
    destruct ms3 as [rg fr pcv svp rv fc mm rm];
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
    subst. reflexivity. }
  rewrite Ems3. rewrite restrict_mkst_fx. unfold nl_ss. apply pa_entry_st_ok_full.
  - unfold E, nl_env. apply (regs_ok_agree 32 (Eimg (Ereg (ms_regs ms3) []))).
    + apply (env_agree_havoc_ge 32 540 _ _ _ ltac:(lia) (env_agree_refl 32 _)).
    + vm_compute. reflexivity.
    + apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, nl_frame.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E. rewrite U18.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply HFp. lia.
    + unfold region_ok, nl_saved.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E. rewrite U8.
      split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
      unfold nl_saved_chunks.
      apply Forall_cons; [apply (nl_saved_chunk E _ _ 552%nat _ _ _ (ES 12%nat ltac:(lia)));
        replace (spZ (n_regs cx) + -104) with (spZ (n_regs cx) - 16 - 8 * 11) by lia; exact (Hsv' 11 ltac:(lia))|].
      apply Forall_cons; [apply (nl_saved_chunk E _ _ 551%nat _ _ _ (ES 11%nat ltac:(lia)));
        replace (spZ (n_regs cx) + -96) with (spZ (n_regs cx) - 16 - 8 * 10) by lia; exact (Hsv' 10 ltac:(lia))|].
      apply Forall_cons; [apply (nl_saved_chunk E _ _ 550%nat _ _ _ (ES 10%nat ltac:(lia)));
        replace (spZ (n_regs cx) + -88) with (spZ (n_regs cx) - 16 - 8 * 9) by lia; exact (Hsv' 9 ltac:(lia))|].
      apply Forall_cons; [apply (nl_saved_chunk E _ _ 549%nat _ _ _ (ES 9%nat ltac:(lia)));
        replace (spZ (n_regs cx) + -80) with (spZ (n_regs cx) - 16 - 8 * 8) by lia; exact (Hsv' 8 ltac:(lia))|].
      apply Forall_cons; [apply (nl_saved_chunk E _ _ 548%nat _ _ _ (ES 8%nat ltac:(lia)));
        replace (spZ (n_regs cx) + -72) with (spZ (n_regs cx) - 16 - 8 * 7) by lia; exact (Hsv' 7 ltac:(lia))|].
      apply Forall_cons; [apply (nl_saved_chunk E _ _ 547%nat _ _ _ (ES 7%nat ltac:(lia)));
        replace (spZ (n_regs cx) + -64) with (spZ (n_regs cx) - 16 - 8 * 6) by lia; exact (Hsv' 6 ltac:(lia))|].
      apply Forall_cons; [apply (nl_saved_chunk E _ _ 546%nat _ _ _ (ES 6%nat ltac:(lia)));
        replace (spZ (n_regs cx) + -56) with (spZ (n_regs cx) - 16 - 8 * 5) by lia; exact (Hsv' 5 ltac:(lia))|].
      apply Forall_cons; [apply (nl_saved_chunk E _ _ 545%nat _ _ _ (ES 5%nat ltac:(lia)));
        replace (spZ (n_regs cx) + -48) with (spZ (n_regs cx) - 16 - 8 * 4) by lia; exact (Hsv' 4 ltac:(lia))|].
      apply Forall_cons; [apply (nl_saved_chunk E _ _ 544%nat _ _ _ (ES 4%nat ltac:(lia)));
        replace (spZ (n_regs cx) + -40) with (spZ (n_regs cx) - 16 - 8 * 3) by lia; exact (Hsv' 3 ltac:(lia))|].
      apply Forall_cons; [apply (nl_saved_chunk E _ _ 543%nat _ _ _ (ES 3%nat ltac:(lia)));
        replace (spZ (n_regs cx) + -32) with (spZ (n_regs cx) - 16 - 8 * 2) by lia; exact (Hsv' 2 ltac:(lia))|].
      apply Forall_cons; [apply (nl_saved_chunk E _ _ 542%nat _ _ _ (ES 2%nat ltac:(lia)));
        replace (spZ (n_regs cx) + -24) with (spZ (n_regs cx) - 16 - 8 * 1) by lia; exact (Hsv' 1 ltac:(lia))|].
      apply Forall_cons; [apply (nl_saved_chunk E _ _ 541%nat _ _ _ (ES 1%nat ltac:(lia)));
        replace (spZ (n_regs cx) + -16) with (spZ (n_regs cx) - 16 - 8 * 0) by lia; exact (Hsv' 0 ltac:(lia))|].
      apply Forall_cons; [apply (nl_saved_chunk E _ _ 540%nat _ _ _ (ES 0%nat ltac:(lia)));
        replace (spZ (n_regs cx) + -8) with (spZ (n_regs cx) - 8) by lia; exact Hra_sv|].
      apply Forall_nil.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val nl_frame nl_saved]. fold E. rewrite U18, U8.
    repeat split; lia.
  - unfold facts_ok, nl_facts. cbn [f_atoms f_conds f_alias]. split; [|split; [exact I | exact I]].
    cbn [atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2]. fold E. rewrite U18, U20, U21.
    pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
    unfold SB, SHADOW_OFF. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat split; try lia.
Qed.

(* presence grows with the memory (AFel.v apresent_grows) *)
Lemma ne_apresent_grows : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
  intros H m m' a HG (Hh & b & Hb). split; [exact Hh|].
  specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh, Hb in HG.
  destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply HG; [discriminate | reflexivity]].
Qed.

Lemma nt_tail : nt_from SK B (nt_post SK B) (nt_tail_inv B).
Proof.
intros cx fp k2 ly3 S3 W3 ms3 md3 HB HJ3 Hfr3 HI.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct ne_vals as (VB & Vcl & Vmf & Vsf).
pose proof HB as (HPRE & HRD & HAP & HNLK0 & HRQ & HRL & HE0 & HE2).
pose proof HPRE as (HJ0 & HGX & HROD & Hret & Hra4 & Hgp & Htp & H16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hnro).
destruct HI as (Hshp & Hrg & Hsv & Hhd & R20 & R27 & Hjbk & Hkp & (bs & Hnl & Hgf) & Hbf).
pose proof Hjbk as (Hk2 & Hperm & Hsfs & Hfrs3 & Hnin & Hfa & Hwit & Hfds3 & Hfs3).
pose proof Hkp as (HK3 & HRO3 & _).
pose proof Hrg as (Rsp & Rs0 & Rs1 & Rs2 & Rs5 & Rs8 & Rgp & Rtp).
destruct (ne_aj_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as (Hceil0 & H47 & HSTK & HXO).
rewrite NL_TALK_AK_val in Hwlo.
pose proof (nt_sp1_range (spZ (n_regs cx)) ltac:(unfold NL_TALK_AFRAME; lia) H16) as Hsp1.
change (nt_sp1 (spZ (n_regs cx))) with (n_sp1 cx) in Hsp1. unfold NL_TALK_AFRAME in Hsp1.
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (HAR0 & _).
assert (Hin3 : In (NT_CID, fp) (frames S3)) by (rewrite Hfr3; left; reflexivity).
destruct (ne_frame_nums cx fp ly3 S3 W3 (ms_mem ms3) md3 HAR3 Hin3 Hfa) as (HF4096 & HFceil & HF32 & ESH & HFsh & HFimg).
assert (Hfl3 : forall c q, flag_addr ly3 c q = flag_addr (n_lyc cx) c q).
{ intros c q. rewrite (proj2 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ3)).
  rewrite (proj2 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ0)). reflexivity. }
destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 NT_CID fp HAR3 Hin3) as (_ & _ & HFp & _).
destruct (al_flag _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 NT_CID fp HAR3 Hin3) as (_ & _ & _ & HFLc).
destruct (aside_rng_low SK SEGS B LAWS pa_segs_low ly3 S3 W3 (ms_mem ms3) md3 NT_CID fp (flag_addr ly3 NT_CID fp)
  HAR3 Hin3 (or_intror (or_intror eq_refl))) as (_ & HFLimg).
assert (EFA : frame_addr ly3 NT_CID fp = nF cx fp) by (rewrite Hfa; reflexivity).
rewrite EFA in HFp. change (fs_frame_bytes NT_CID) with 32768 in HFp.
destruct HAP as (kbs & req & HNLK & HWF & HOPEN & HOC & HCC & HRA & HHV & HERR & HRQ' & HRL' & HLEN & HMR & HRAQ
  & HHVQ & HFRQ & HGQ & HBK & HBA & HEK & HEA & HKA & HKF & HAF & HCK & HCA).
pose proof (ne_gnl_facts) as GF.
(* ---- the run from NT_tail to the call of frame_release_9 (+0x514) ---- *)
pose proof (nl_entry cx fp W3 ms3 Hshp Hrg Hsv R20 HF4096 HF32 HFceil ltac:(lia) ltac:(lia)
  (fun a Ha => proj1 (HFp a ltac:(lia)))) as HS.
remember (nl_env cx ms3) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold nl_env; apply img_env_havoc_hi; [apply Eimg_env | unfold A_LIM; lia]).
assert (EW : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
{ intros n r Hn Hr. subst E. unfold nl_env. rewrite ew_havoc_old by lia. exact (ew_Eimg_Ereg_nat _ _ n r Hr). }
assert (ES : forall j, (j < 13)%nat -> ew E (540 + j) = nth j
    [getr (n_regs cx) 1; getr (n_regs cx) 8; getr (n_regs cx) 9; getr (n_regs cx) 18;
     getr (n_regs cx) 19; getr (n_regs cx) 20; getr (n_regs cx) 21; getr (n_regs cx) 22;
     getr (n_regs cx) 23; getr (n_regs cx) 24; getr (n_regs cx) 25; getr (n_regs cx) 26;
     getr (n_regs cx) 27] (Z_to_bv 64 0)).
{ intros j Hj. subst E. unfold nl_env. apply ew_havoc_new. cbn [length]. lia. }
clear HEdef.
assert (U18 : bv_unsigned (ew E 18) = nF cx fp)
  by (rewrite (EW 18%nat (18%bv : bv 5) ltac:(lia) eq_refl), Rs2; unfold w64; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = spZ (n_regs cx))
  by (rewrite (EW 8%nat (8%bv : bv 5) ltac:(lia) eq_refl), Rs0; unfold w64; apply unsigned_lit_small; lia).
(* the run writes the frame's first word (an uninstrumented store into the left redzone), so it goes through the
   plain engine (LinkWalkSide.v paj_run_call_plain_x), not the shadow-token one *)
pose proof (paj_run_call_plain_x SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUNC.
lazymatch type of RUNC with context [sym_runN_pi ?tpi _ _] =>
  let r := eval vm_compute in (sym_runN_pi tpi FUEL nl_ss) in
  lazymatch r with (?ssx, ?stx) =>
    assert (Hrun : sym_runN_pi tpi FUEL nl_ss = (ssx, stx)) by (vm_compute; reflexivity) end end.
eapply (RUNC W3 FUEL E nl_ss _ _ ms3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ3).
{ intros a (r & Hin & Ha). vm_compute in Hin. destruct Hin as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [|lia].
  rewrite U18 in Ha. left.
  eapply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low); [exact HJ3 | left; reflexivity |].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes NT_CID) with 32768. lia. }
clear HS HJ3. intros ms1 mat HS HJ3 HF HFr HG.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into ms1 end.
assert (UN1 : forall a, 0 <= a < 2 ^ 64 -> ~ (nF cx fp <= a < nF cx fp + 8) ->
          aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ apply (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem ms1) _ HFr).
  intros b wlo whi a Hin Ha. vm_compute in Hin.
  destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Ha; [rewrite U18 in Ha; lia | lia]. }
assert (HG1 := HG). clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
rewrite (EW 20%nat (20%bv : bv 5) ltac:(lia) eq_refl), R20 in R10.
rewrite (EW 2%nat (2%bv : bv 5) ltac:(lia) eq_refl), Rsp in R2.
rewrite (EW 3%nat (3%bv : bv 5) ltac:(lia) eq_refl), Rgp in R3.
rewrite (EW 4%nat (4%bv : bv 5) ltac:(lia) eq_refl), Rtp in R4.
assert (Usp1 : spZ (ms_regs ms1) = n_sp1 cx) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
(* ---- frame_release_9 (+0x514): LinkWalkSide.v aj_gx_stack_free_at ---- *)
eapply SRr_bind.
{ apply (aj_gx_stack_free_at SK SEGS B LAWS pa_segs_low (pa_sigma LS___asan_stack_free_9) 9 SFREE ltac:(lia)
    (n_G cx) (n_XO cx) (n_OUT cx) W3 (ms_regs ms1) (ms_mem ms1) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) (n_own cx) ly3 S3 _ k2 fp 16672 (getr (ms_regs ms1) 1) HJ3).
  - rewrite R10. change 9 with NT_CID. rewrite EFA. reflexivity.
  - exact R11.
  - change (fs_frame_bytes 9) with 32768. lia.
  - reflexivity.
  - change 9 with NT_CID. rewrite EFA, Hfl3. change (fs_frame_bytes NT_CID) with 32768.
    destruct Hhd as (_ & _ & _ & Hhf). change (fs_frame_bytes NT_CID) with 32768 in Hhf.
    eapply ne_rdword_kept; [intros i Hi; apply UN1; lia | exact Hhf].
  - rewrite Usp1. lia.
  - rewrite Usp1. unfold ESTACK. lia.
  - rewrite Usp1. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ4 & HP4 & Hsh4 & Hun4 & Hwp4 & Hpr4 & Hsbm4).
change 9 with NT_CID in Hun4, Hpr4, HJ4. rewrite EFA, Hfl3 in Hun4. rewrite Usp1 in Hun4.
change (StackFreeDef.sf_span NT_CID 16672) with 2084 in Hun4.
assert (U8' : bv_unsigned (ew E 8) = spZ (n_regs cx)) by exact U8.
jafter_call_keep_pi HS 60%nat regs2 (mrestrict (w_H W3) mem2) HP4 [1]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  apply (ne_region_kept_ro SEGS E (w_H W3) (w_H W3) (ms_mem ms1) mem2 8 (spZ (n_regs cx))); [exact U8 | lia |].
  intros a Ha. apply Hun4; [lia | | | unfold ESTACK; lia].
  - unfold shadow_addr. rewrite <- ESH. rewrite ESH. unfold SHADOW_OFF. lia.
  - rewrite Hfl3 in HFLc. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 60 (map (getr regs2) CLOB)) as E2 eqn:HE2def in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2def; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (EW2 : forall n, (n < 60)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2def; apply ew_havoc_old; exact Hn).
assert (EW2' : forall n, (76 <= n)%nat -> ew E2 n = ew E n)
  by (intros n Hn; rewrite HE2def; apply ew_havoc_above; cbn [length map CLOB]; lia).
clear HE2def.
rewrite R1.
(* ---- +0x518 .. the `ret`: a0 := s11, the epilogue ---- *)
pose proof (paj_run_plain_x SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUNP.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
lazymatch type of RUNP with context [sym_runN_pi ?tpi _ _] =>
  let r := eval vm_compute in (sym_runN_pi tpi FUEL ssx) in
  lazymatch r with (?ssy, ?sty) =>
    assert (Hrun2 : sym_runN_pi tpi FUEL ssx = (ssy, sty)) by (vm_compute; reflexivity) end end end.
eapply (RUNP W3 FUEL E2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI2 HS Hrun2 I HJ4).
{ intros a (r & Hin & Ha). vm_compute in Hin. destruct Hin as [<- | []]. cbn in Ha. lia. }
clear HS HJ4. intros ms5 mat5 HS HJ5 HF HFr HG.
assert (Emem5 : ms_mem ms5 = mem2) by ne_nowrite HF.
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1.
prreg HS (2%bv : bv 5) Q2.
prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9.
prreg HS (10%bv : bv 5) Q10.
prreg HS (18%bv : bv 5) Q18.
prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22.
prreg HS (23%bv : bv 5) Q23.
prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26.
prreg HS (27%bv : bv 5) Q27.
assert (E540 : ew E 540 = getr (n_regs cx) 1) by exact (ES 0%nat ltac:(lia)).
assert (E541 : ew E 541 = getr (n_regs cx) 8) by exact (ES 1%nat ltac:(lia)).
assert (E542 : ew E 542 = getr (n_regs cx) 9) by exact (ES 2%nat ltac:(lia)).
assert (E543 : ew E 543 = getr (n_regs cx) 18) by exact (ES 3%nat ltac:(lia)).
assert (E544 : ew E 544 = getr (n_regs cx) 19) by exact (ES 4%nat ltac:(lia)).
assert (E545 : ew E 545 = getr (n_regs cx) 20) by exact (ES 5%nat ltac:(lia)).
assert (E546 : ew E 546 = getr (n_regs cx) 21) by exact (ES 6%nat ltac:(lia)).
assert (E547 : ew E 547 = getr (n_regs cx) 22) by exact (ES 7%nat ltac:(lia)).
assert (E548 : ew E 548 = getr (n_regs cx) 23) by exact (ES 8%nat ltac:(lia)).
assert (E549 : ew E 549 = getr (n_regs cx) 24) by exact (ES 9%nat ltac:(lia)).
assert (E550 : ew E 550 = getr (n_regs cx) 25) by exact (ES 10%nat ltac:(lia)).
assert (E551 : ew E 551 = getr (n_regs cx) 26) by exact (ES 11%nat ltac:(lia)).
assert (E552 : ew E 552 = getr (n_regs cx) 27) by exact (ES 12%nat ltac:(lia)).
destruct Hwit as (S1 & W1 & mem1 & md1 & HAR1 & HfrS1 & HabS1).
assert (Hin1 : In (NT_CID, fp) (frames S1)) by (rewrite HfrS1; left; reflexivity).
(* ---- what the tail kept: every byte outside the side frame's bytes and the call's stack window ---- *)
assert (UNall : forall a, 0 <= a < 2 ^ 64 -> ~ aside_rng (n_lyc cx) NT_CID fp a ->
          ~ (spZ (n_regs cx) - NL_TALK_AK <= a < spZ (n_regs cx)) ->
          aview SEGS (w_H W3) (ms_mem ms5) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hns Hnw. rewrite Emem5. rewrite NL_TALK_AK_val in Hnw.
  rewrite Hun4.
  - apply UN1; [exact Ha|]. intros Hf. apply Hns. left. unfold in_zr, frame_rng. cbn [fst snd].
    change (frame_addr (n_lyc cx) NT_CID fp) with (nF cx fp). change (fs_frame_bytes NT_CID) with 32768. lia.
  - exact Ha.
  - intros Hq. apply Hns. right. left. unfold in_zr. cbn [fst snd].
    change (frame_addr (n_lyc cx) NT_CID fp) with (nF cx fp). change (fs_frame_bytes NT_CID / 8) with 4096. lia.
  - intros Hq. apply Hns. right. right. exact Hq.
  - unfold ESTACK. lia. }
(* an image byte is neither *)
assert (UNimg : forall a, in_img SEGS a ->
          aview SEGS (w_H W3) (ms_mem ms5) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Hi. pose proof (pa_segs_low a Hi) as Hlow. rewrite C5 in Hlow.
  apply UNall; [lia | | rewrite NL_TALK_AK_val; lia].
  intros Hs. exact (proj2 (aside_rng_low SK SEGS B LAWS pa_segs_low (n_lyc cx) S1 W1 mem1 md1 NT_CID fp a
    HAR1 Hin1 Hs) Hi). }
(* the caller's buffers: write-set bytes outside the window, so not the side frame's (ne_ajw_not_side) *)
assert (UNbuf : forall p0 n0 a, (p0 = n_kind cx /\ n0 = n_kindn cx \/ p0 = n_alias cx /\ n0 = n_aliasn cx) ->
          p0 <> 0 -> p0 <= a < p0 + n0 -> 0 <= a < 2 ^ 64 ->
          aview SEGS (w_H W3) (ms_mem ms5) a = aview SEGS (w_H W3) (ms_mem ms3) a /\
          ~ in_roP SEGS PCAP_RLO PCAP_RHI a).
{ intros p0 n0 a Hpn Hp Ha Hab.
  destruct (ne_buf_byte cx HB p0 n0 a Hpn Hp Ha) as (HwFP & Herr & Hgnl & Hfrm).
  split; [|exact (Hnro a HwFP)].
  pose proof (Hajw a HwFP) as Hw.
  assert (Hns : ~ aside_rng (n_lyc cx) NT_CID fp a).
  { apply (ne_ajw_not_side (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
      (n_W0 cx) (n_mem0 cx) (n_md0 cx) (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx)
      ly3 S3 W3 (ms_mem ms3) md3 NT_CID fp a HGX HJ0 HAR3 Hfr3); [| exact Hfa | exact Hfl3 | exact Hw].
    intros b m Hb. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hb. }
  apply UNall; [exact Hab | exact Hns | lia]. }
(* ---- the `ret` (+0x56c) ---- *)
assert (Hraw : v_jalr (getr (ms_regs ms5) 1) 0 = getr (n_regs cx) 1).
{ rewrite Q1, (EW2' 540%nat ltac:(lia)), E540. exact Hret. }
eapply (paj_ret_at (PL := PL_link) (PI := PI) W3 E2 _ ms5 _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. rewrite Hraw.
set (mdf := with_vm_backing _ mat' _).
unfold nt_post.
apply (apost_side_gen SK SEGS B LAWS pa_segs_low NL_TALK_AK 0 (n_E cx) (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx)
  (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx) (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx)
  (n_memc cx) (n_mdc cx) (n_k cx) (n_regs cx) (ms_regs ms5) ly3 (stack_free_state NT_CID fp S3) W3 (ms_mem ms5) mdf
  k2 NT_CID fp S1 W1 mem1 md1).
- exact HJ0.
- unfold mdf. exact (ajournal_gx_materialize SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5).
- rewrite Hk2. lia.
- unfold mdf. rewrite (proj1 (wvb_fds_fs _ _ _)), (proj1 (wvb_fds_fs _ _ _)).
  rewrite (same_but_materialized_wvb _ _ Hsbm4), (proj1 (wvb_fds_fs _ _ _)), (proj1 (wvb_fds_fs _ _ _)).
  exact Hfds3.
- unfold mdf. rewrite (proj2 (wvb_fds_fs _ _ _)), (proj2 (wvb_fds_fs _ _ _)).
  rewrite (same_but_materialized_wvb _ _ Hsbm4), (proj2 (wvb_fds_fs _ _ _)), (proj2 (wvb_fds_fs _ _ _)).
  exact Hfs3.
- (* the callee-saved registers, sp, gp and tp: the epilogue's reloads from nt_saved *)
  apply aregs_preserved_eqs.
  + rewrite Q2, (EW2 8%nat ltac:(lia)), (EW 8%nat (8%bv : bv 5) ltac:(lia) eq_refl), Rs0.
    unfold w64, spZ. apply Z_to_bv_bv_unsigned.
  + rewrite Q3, (EW2 3%nat ltac:(lia)), (EW 3%nat (3%bv : bv 5) ltac:(lia) eq_refl). exact Rgp.
  + rewrite Q4, (EW2 4%nat ltac:(lia)), (EW 4%nat (4%bv : bv 5) ltac:(lia) eq_refl). exact Rtp.
  + rewrite Q8, (EW2' 541%nat ltac:(lia)). exact E541.
  + rewrite Q9, (EW2' 542%nat ltac:(lia)). exact E542.
  + rewrite Q18, (EW2' 543%nat ltac:(lia)). exact E543.
  + rewrite Q19, (EW2' 544%nat ltac:(lia)). exact E544.
  + rewrite Q20, (EW2' 545%nat ltac:(lia)). exact E545.
  + rewrite Q21, (EW2' 546%nat ltac:(lia)). exact E546.
  + rewrite Q22, (EW2' 547%nat ltac:(lia)). exact E547.
  + rewrite Q23, (EW2' 548%nat ltac:(lia)). exact E548.
  + rewrite Q24, (EW2' 549%nat ltac:(lia)). exact E549.
  + rewrite Q25, (EW2' 550%nat ltac:(lia)). exact E550.
  + rewrite Q26, (EW2' 551%nat ltac:(lia)). exact E551.
  + rewrite Q27, (EW2' 552%nat ltac:(lia)). exact E552.
- exact HAR1.
- exact HfrS1.
- exact HabS1.
- (* the kept clause: nt_kept's, across the tail's writes (all in the side frame or the window) *)
  apply (akept_step SK SEGS B LAWS pa_segs_low (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) W3 (ms_mem ms3)
    W3 (ms_mem ms5) (spZ (n_regs cx) - NL_TALK_AK) (spZ (n_regs cx))
    (fun a => n_E cx a \/ aside_rng (n_lyc cx) NT_CID fp a) (fun a => n_E cx a \/ aside_rng (n_lyc cx) NT_CID fp a)
    (fun a => aside_rng (n_lyc cx) NT_CID fp a \/ (spZ (n_regs cx) - NL_TALK_AK <= a < spZ (n_regs cx))) HAR0).
  + rewrite NL_TALK_AK_val. lia.
  + lia.
  + exact HK3.
  + intros a Ha Hx. apply UNall; [exact Ha | intros H; apply Hx; left; exact H | intros H; apply Hx; right; exact H].
  + intros a Ha Hp. rewrite Emem5. apply Hpr4; [exact Ha|]. exact (ne_apresent_grows _ _ _ _ HG1 Hp).
  + intros a H. exact H.
  + intros a [H|H]; [left; right; exact H | right; exact H].
- cbv beta. split.
  { exact (set_fs_trans S3 (stack_free_state NT_CID fp S3) (n_Sc cx) Hsfs (stack_free_state_set_fs NT_CID fp S3)). }
  split.
  { unfold stack_free_state. rewrite ablocks_set_fs. exact Hperm. }
  (* nl_talk_apost: g_nl's bytes and the request's bytes at the entry memory are the context's *)
  intros kbs' req' Hk' Hr' Hl'.
  assert (Ekbs : kbs' = n_kbs cx).
  { destruct Hk' as ((HA1 & _) & HL1). destruct HNLK0 as ((HA2 & _) & HL2).
    exact (nt_abytes_unique _ _ _ _ HA1 HA2 ltac:(lia)). }
  assert (Ereq : req' = n_reqb cx).
  { unfold n_len in HRL. exact (nt_abytes_unique _ _ _ _ Hr' HRQ ltac:(lia)). }
  subst kbs' req'. cbv zeta. change (nk_kstate (n_kbs cx)) with (n_K0 cx).
  split.
  { rewrite Q10, (EW2 27%nat ltac:(lia)), (EW 27%nat (27%bv : bv 5) ltac:(lia) eq_refl). exact R27. }
  split.
  { exists bs. split; [|exact Hgf].
    apply (ne_anlk_frame (rdW W3 (ms_mem ms3))); [exact Hnl|]. intros i Hi.
    apply ne_mbyte_of_aview. apply UNimg.
    exact (proj1 (GF (LA_G_NL + i) ltac:(lia))). }
  assert (Hbf5 : nt_bufs_fin cx (rdW W3 (ms_mem ms5))).
  { pose proof Hbf as (_ & _ & _ & _ & Hb5 & Hb6).
    apply (ne_bufs_frame cx (rdW W3 (ms_mem ms3))); [| | exact Hbf].
    - intros Hk Hn a Ha. destruct (Hb5 Hk Hn) as (junk & Hjl & (Hj0 & Hj1 & _) & _).
      destruct (UNbuf (n_kind cx) (n_kindn cx) a (or_introl (conj eq_refl eq_refl)) Hk Ha ltac:(lia)) as [Hav Hro].
      split; [exact (ne_mbyte_of_aview _ _ _ _ _ _ Hav)|].
      apply (ne_writable_of_aview _ _ _ _ a); [lia | exact Hro | exact Hav].
    - intros Hk Hn a Ha. destruct (Hb6 Hk Hn) as (junk & Hjl & (Hj0 & Hj1 & _) & _).
      destruct (UNbuf (n_alias cx) (n_aliasn cx) a (or_intror (conj eq_refl eq_refl)) Hk Ha ltac:(lia)) as [Hav Hro].
      split; [exact (ne_mbyte_of_aview _ _ _ _ _ _ Hav)|].
      apply (ne_writable_of_aview _ _ _ _ a); [lia | exact Hro | exact Hav]. }
  destruct Hbf5 as (F1 & F2 & F3 & F4 & F5 & F6).
  split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5 | exact F6].
Qed.

End b.
End a.

About nt_exit.
Print Assumptions nt_exit.
About nt_tail.
Print Assumptions nt_tail.
