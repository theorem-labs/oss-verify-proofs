From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: lib/B twin of lib/A/Prog/PcapEntryTop.v (a working branch 9be46202615) for fuzz_pcap.asan-ubsan (libreac v1.9.0; the pinned fuzz_pcap.asan-ubsan image, sha256 9e66f771f22af67a..., the image the build loads as AsanUbsan; symbols from its unstripped twin fuzz_pcap, sha256 c969d83cdd5943a8..., fuzz_pcap.nm.txt (sha256 49b2ad826669; internal record) / fuzz_pcap.readelf.txt (sha256 13e925e26aa1; internal record) beside it): the code table of the program code lib/B/Prog/PcapList.v lists (0x80788 .. 0x81dc8, 1424 words), the value table over lib/B/Prog/PcapAddr.v, the instance PI_pcap of lib/B/Prog/PcapPa.PAImg with its named equalities at this image's MEASURED values, the image facts the lib/B walk lanes take as Section hypotheses (HHI8, HG42, HGW, HGSRC, ro_below_ofl), and the composition of the lib/B phase lemmas into lib/B/Prog/PcapEntry.v's tfib_lib_contract_x_all_B. No numeral is an asan (lib/A) value. *)
(* The asan-ubsan build's entry contract for fuzz_pcap: PcapEntry.tfib_lib_contract_x_all_B, from the walks of
   LLVMFuzzerTestOneInput (0x80818) phase by phase (lib/B/Prog/PcapEntry{Entry,Open,Skip,Rec,End,Tail}.v).

   Every phase is proved by its lane and used directly; each lane's own Section premises (the callee contracts, the
   runtime rules and the core's B) become premises of Section top below, in one place, except the image facts this
   file discharges at PI_pcap. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require PcapEntry PcapEntryDefs PcapEntryPhases.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require
  PcapEntryCalls PcapEntryEntry PcapEntryOpen PcapEntrySkip PcapEntryRec PcapEntryEnd PcapEntryTail PcapSourceClose.
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01 YC5d YM05 YO09 YO05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd YImgTop YG0p.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import
PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapRelro PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PSourceMeter.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require PFclose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require Import PSourceK.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require OutForm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require PWalk.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journalG.
(* seg_wbyte and writable_of_seg (lib/AllocCut.v:264, :277), for the writable segment of G_HARNESS_U. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require AllocCut.
From OSSVerify.libreac.fuzz_pcap.images Require AsanUbsan.
(* lib/B's entry names last, over their namesakes in the Requires above (c_regs, ...). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapEntry PcapEntryDefs PcapEntryPhases.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The listing's image: fuzz_pcap.asan-ubsan v1.9.0                                                *)
(* ---------------------------------------------------------------------------------------------- *)

(* The code table: every word of the program code the listing covers, from libreac_fuzz_fopen to the last word of
   pcap_source_close, counted from Symbols.v (v1.9.0: 0x80788, size 0x90, to 0x81d4c, size 0x7c, so the span ends at
   0x81dc8: 0x1640 bytes, 1424 words), the length of PcapList.pcap_listing (PcapList.pcap_nslots). *)
Definition pcap_lib_count : nat :=
  symwords Symbols.AsanUbsan.s_libreac_fuzz_fopen (Symbols.AsanUbsan.s_pcap_source_close + Symbols.AsanUbsan.Size.s_pcap_source_close).
Lemma pcap_lib_count_len : length pcap_listing = pcap_lib_count.
Proof. vm_compute. reflexivity. Qed.
Definition pcaptbl : ctable :=
  Eval vm_compute in (build_table AsanUbsan.M.loaded_segments pcap_text pcap_lib_count TEmpty).
Lemma pcaptbl_eq : pcaptbl = build_table AsanUbsan.M.loaded_segments pcap_text pcap_lib_count TEmpty.
Proof. vm_cast_no_check (eq_refl pcaptbl). Qed.
Lemma pcaptbl_ok : table_ok AsanUbsan.M.loaded_segments pcaptbl.
Proof. rewrite pcaptbl_eq. apply build_table_ok0. cbv. discriminate. Qed.

(* The value table: the listing's base, its 17 objects and its 29 auipc values (PcapAddr.v). *)
Definition pcap_val (a : nat) : Z :=
  if (a =? A_TEXT)%nat then pcap_text else if (a <? A_HI 0)%nat then pcap_obj (a - A_OBJ 0) else pcap_hi (a - A_HI 0).

Lemma pcap_lib_check : pi_check psym (clookup pcaptbl) pcap_val pcap_sigma pcap_listing = true.
Proof. vm_compute. reflexivity. Qed.

Ltac zlit := lazymatch goal with |- 0 <= ?x < _ => let v := eval vm_compute in x in change x with v end; lia.
Lemma pcap_val_range : forall a, 0 <= pcap_val a < 2 ^ 64.
Proof.
  intros a. unfold pcap_val. destruct (Nat.eqb a A_TEXT); [zlit|].
  destruct (Nat.ltb a (A_HI 0)).
  - unfold pcap_obj. generalize (a - A_OBJ 0)%nat as m. intros m. do 18 (destruct m as [|m]; [zlit|]). zlit.
  - unfold pcap_hi. generalize (a - A_HI 0)%nat as m. intros m. do 30 (destruct m as [|m]; [zlit|]). zlit.
Qed.

Lemma pcap_B_ok : 0 <= pcap_val A_TEXT /\ pcap_val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ pcap_val A_TEXT mod 4 = 0.
Proof. unfold pcap_val, pcap_text, A_TEXT. cbn. split; [lia|]. split; [lia | reflexivity]. Qed.

Lemma pcap_wx : wx_segs_nowrap AsanUbsan.M.loaded_segments.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* The four loaded segments, page-aligned in the image module (the PT_LOADs of fuzz_pcap.readelf.txt:66-69 (sha256 13e925e26aa1; internal record): 0x10000
   +0x1efc0 R, 0x2ffc0 +0x681a0 R E, 0x99160 +0x1ea0 RW, 0x9b3f0 +0x55ac80 RW): (0x10000, 0x1f000), (0x2f000,
   0x6a000), (0x99000, 0x2000), (0x9b000, 0x55c000). *)
Lemma pcap_segs_low : forall a, in_img AsanUbsan.M.loaded_segments a -> 0 <= a < kLowMemEnd.
Proof.
  intros a (sg & Hin & Hr). unfold kLowMemEnd.
  assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
    (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) AsanUbsan.M.loaded_segments)).
  { exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) AsanUbsan.M.loaded_segments sg Hin). }
  remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
  vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.

Lemma pcap_img_range : forall a, in_img AsanUbsan.M.loaded_segments a -> 0x10000 <= a < pcap_img_end.
Proof.
  intros a (sg & Hin & Hr). unfold pcap_img_end, IMG_TOP.
  assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
    (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) AsanUbsan.M.loaded_segments)).
  { exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) AsanUbsan.M.loaded_segments sg Hin). }
  remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
  vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.

(* lib/B/Prog/PcapRelro.v's window: .data.rel.ro 0x99198 .. .got end 0x9a3f0 (fuzz_pcap.readelf.txt:34-36 (sha256 13e925e26aa1; internal record)). *)
Lemma pcap_relro_img : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img AsanUbsan.M.loaded_segments a.
Proof.
  intros a Ha. destruct pcap_relro_in_image as (s & Hs & H1 & H2 & H3). exists s. split; [exact Hs | lia].
Qed.

(* The six program functions the listing calls (PcapPa.pcap_xcalls: libreac_fuzz_fopen, pcap_source_open / _next /
   _close, rd32, rd_u32) sit at pcap_text + their listing offsets. *)
Lemma pcap_xcalls_ok : forall s k, In (s, k) pcap_xcalls -> pcap_sigma s = pcap_val A_TEXT + k.
Proof.
  intros s k H.
  assert (Hb : forallb (fun p => Z.eqb (pcap_sigma (fst p)) (pcap_val A_TEXT + snd p)) pcap_xcalls = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. apply Z.eqb_eq. exact (Hb (s, k) H).
Qed.

Lemma pcap_obj_img : forall i, (i < 17)%nat -> 0x10000 <= pcap_val (A_OBJ i) /\ pcap_val (A_OBJ i) + 8 <= pcap_img_end.
Proof.
  intros i Hi. unfold pcap_img_end, IMG_TOP.
  do 17 (destruct i as [|i]; [unfold pcap_val, pcap_obj, A_OBJ, A_TEXT, A_HI; cbn; lia|]). exfalso; lia.
Qed.

Section inst. Context {rc : YM05.RunCeil}.

Lemma pcap_img_cover : forall ly S md, ALedger AsanUbsan.M.loaded_segments ly S md ->
  fst (ly_img ly) <= 0x10000 /\ pcap_img_end <= fst (ly_img ly) + snd (ly_img ly).
Proof.
  intros ly S md LG. unfold pcap_img_end, IMG_TOP. split.
  - destruct (al_img _ _ _ _ LG AsanUbsan.AsanUbsan_segment_000 ltac:(left; reflexivity)) as [H _]. cbn in H. lia.
  - destruct (al_img _ _ _ _ LG AsanUbsan.AsanUbsan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H].
    cbn in H. lia.
Qed.

(* The listing's image instance: fuzz_pcap.asan-ubsan v1.9.0, its read-only window lib/B/Prog/PcapRelro.v's. *)
Definition PI_pcap : PAImg pcap_listing := {|
  pa_segs := AsanUbsan.M.loaded_segments;
  pa_tbl := pcaptbl;
  pa_tbl_ok := pcaptbl_ok;
  pa_val := pcap_val;
  pa_sigma := pcap_sigma;
  pa_cert := pcap_lib_check;
  pa_B_ok := pcap_B_ok;
  pa_val_range := pcap_val_range;
  pa_wx := pcap_wx;
  pa_segs_low := pcap_segs_low;
  pa_img_range := pcap_img_range;
  pa_img_cover := pcap_img_cover;
  pa_obj_img := pcap_obj_img;
  pa_relro_lo := PCAP_RLO;
  pa_relro_hi := PCAP_RHI;
  pa_relro_img := pcap_relro_img;
  pa_xcalls := pcap_xcalls_ok |}.

(* ---- the instance's named equalities, at this image's measured values ---- *)
Lemma pi_pcap_segs : @pa_segs rc pcap_listing PI_pcap = AsanUbsan.M.loaded_segments.
Proof. reflexivity. Qed.
(* g_file: object 2, nm `b g_file` 0x5d3e60 (PcapAddr.v pcap_obj 2; PcapEntry.v G_HARNESS_U). *)
Lemma pi_pcap_obj2 : @pa_val rc pcap_listing PI_pcap (A_OBJ 2) = (symaddr Symbols.AsanUbsan.s_g_file).
Proof. vm_compute. reflexivity. Qed.
(* g_file_len: object 4, nm `b g_file_len` 0x5d3e40 (PcapAddr.v pcap_obj 4; PcapEntry.v G_HARNESS_U). *)
Lemma pi_pcap_obj4 : @pa_val rc pcap_listing PI_pcap (A_OBJ 4) = (symaddr Symbols.AsanUbsan.s_g_file_len).
Proof. vm_compute. reflexivity. Qed.
Lemma pi_pcap_relro : @pa_relro_lo rc pcap_listing PI_pcap = PCAP_RLO /\ @pa_relro_hi rc pcap_listing PI_pcap = PCAP_RHI.
Proof. split; reflexivity. Qed.
(* The walk lanes' HHI8 (lib/B/Prog/PcapEntryEntry.v:479, PcapEntryEnd.v:346): g_file_len is the auipc value 8
   (0x5d39a8, `auipc s8,0x553` 0x809a8) + 0x498 (`sd s6,0x498(s8)` 0x809ac). *)
Lemma pi_pcap_glen : @pa_val rc pcap_listing PI_pcap (A_HI 8) + PE_GLEN_LO = @pa_val rc pcap_listing PI_pcap (A_OBJ 4).
Proof. vm_compute. reflexivity. Qed.
(* The walk lanes' HG42 (PcapEntryEntry.v:480): g_file_len [0x5d3e40, +8) ends below g_file 0x5d3e60. *)
Lemma pi_pcap_g42 : @pa_val rc pcap_listing PI_pcap (A_OBJ 4) + 8 <= @pa_val rc pcap_listing PI_pcap (A_OBJ 2) \/
  @pa_val rc pcap_listing PI_pcap (A_OBJ 2) + 8 <= @pa_val rc pcap_listing PI_pcap (A_OBJ 4).
Proof. left. rewrite pi_pcap_obj4, pi_pcap_obj2. lia. Qed.
Lemma pi_pcap_text : @pa_val rc pcap_listing PI_pcap A_TEXT = pcap_text.
Proof. reflexivity. Qed.
Lemma pi_pcap_pe_G : @pe_G rc PI_pcap = G_HARNESS_U.
Proof. vm_compute. reflexivity. Qed.
(* The entry slot of the listing is LLVMFuzzerTestOneInput (nm `T` 0x80818, size 0x848). *)
Lemma pi_pcap_entry : @pa_val rc pcap_listing PI_pcap A_TEXT + PP_entry = A_LLVMF.
Proof. vm_compute. reflexivity. Qed.

End inst.

(* ---- the harness's globals on this image ---- *)

(* The 16 bytes of G_HARNESS_U (.bss g_file_len [0x5d3e40, +8) and g_file [0x5d3e60, +8); .bss is 0x9e100 +0x557f70,
   fuzz_pcap.readelf.txt:39 (sha256 13e925e26aa1; internal record), inside the RW PT_LOAD 0x9b3f0 +0x55ac80). *)
Definition pcap_G_harness_bytes : list Z :=
  flat_map (fun r => map (fun i => fst r + Z.of_nat i) (seq 0 (Z.to_nat (snd r)))) G_HARNESS_U.
Lemma pcap_G_harness_bytes_in : forall a, inG G_HARNESS_U a -> In a pcap_G_harness_bytes.
Proof.
  intros a Ha. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Har). unfold in_zr in Har.
  unfold pcap_G_harness_bytes. apply in_flat_map. exists r. split; [exact Hr|]. cbv beta.
  apply in_map_iff. exists (Z.to_nat (a - fst r)). cbv beta. split; [lia | apply in_seq; lia].
Qed.

(* They lie in a writable segment: AllocCut.seg_wbyte (the segment byte, read only when seg_writable) reads each of
   them, so AllocCut.writable_of_seg gives writable_at at every memory (a Theorem Labs lane's HGW form,
   a working branch). *)
Lemma pcap_G_harness_writable : forall a, inG G_HARNESS_U a ->
  forall m, writable_at AsanUbsan.M.loaded_segments m a.
Proof.
  intros a Ha m.
  assert (HC : forallb (fun x => match AllocCut.seg_wbyte AsanUbsan.M.loaded_segments (Z_to_bv 64 x) with
                                 | Some _ => true | None => false end) pcap_G_harness_bytes = true)
    by (clear; vm_compute; reflexivity).
  pose proof (pcap_G_harness_bytes_in a Ha) as Hin.
  rewrite forallb_forall in HC. specialize (HC a Hin). cbv beta in HC.
  destruct (AllocCut.seg_wbyte AsanUbsan.M.loaded_segments (Z_to_bv 64 a)) as [b|] eqn:E; [|discriminate].
  exact (AllocCut.writable_of_seg _ m a b E).
Qed.

(* HGW_B: the walk lanes' HGW (a Theorem Labs lane, lib/B/Prog/PcapEntryOpen.v:2915; a Theorem Labs lane's Entry walk) at PI_pcap: the segment
   view of every byte of pe_G, through a memory that holds none of them, is a byte. *)
Lemma HGW_B {rc : YM05.RunCeil} : forall a, inG (@pe_G rc PI_pcap) a ->
  wview (@pa_segs rc pcap_listing PI_pcap) (fun _ => None) (Z_to_bv 64 a) <> None.
Proof.
  intros a Ha. rewrite pi_pcap_pe_G in Ha. exact (pcap_G_harness_writable a Ha (fun _ => None)).
Qed.

(* The bytes of G_HARNESS_U are image bytes (segment 3), outside every read-only segment and the RELRO window, and
   outside pcap_KS's AddrHashMap meta cell (0xa1008, PSourceK.v:79) and stream environment cells (PSourceK.v:67-81:
   threaded 0x5f4a21, need_locks 0x5f4a23, ofl_lock [0x5f4e80, +16), mode [0x20d40, +3), rwa [0x20026, +4), canary
   [0x5f47d0, +8)), and below the open-file-list head 0x5f4e88 (PSourceK.pcap_KS_head). *)
Definition pcap_in_seg_b (a : Z) (s : Segment) : bool :=
  (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s)).
Lemma pcap_G_img : forall a, inG G_HARNESS_U a -> in_img AsanUbsan.M.loaded_segments a.
Proof.
  intros a Ha.
  assert (HC : forallb (fun x => existsb (pcap_in_seg_b x) AsanUbsan.M.loaded_segments) pcap_G_harness_bytes = true)
    by (clear; vm_compute; reflexivity).
  rewrite forallb_forall in HC. specialize (HC a (pcap_G_harness_bytes_in a Ha)).
  apply existsb_exists in HC as (s & Hs & Hb). unfold pcap_in_seg_b in Hb.
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists s. split; [exact Hs | lia].
Qed.
Lemma pcap_G_not_ro : forall a, inG G_HARNESS_U a -> ~ in_roP AsanUbsan.M.loaded_segments PCAP_RLO PCAP_RHI a.
Proof.
  intros a Ha.
  assert (HC : forallb (fun x => forallb (fun s => seg_writable s || negb (pcap_in_seg_b x s))
                                   AsanUbsan.M.loaded_segments) pcap_G_harness_bytes = true)
    by (clear; vm_compute; reflexivity).
  rewrite forallb_forall in HC. specialize (HC a (pcap_G_harness_bytes_in a Ha)).
  intros [(s & Hs & Hw & Hr) | Hrel].
  - rewrite forallb_forall in HC. specialize (HC s Hs). rewrite Hw in HC. cbn [orb] in HC.
    unfold pcap_in_seg_b in HC. apply negb_true_iff in HC. apply andb_false_iff in HC as [HC|HC];
      [apply Z.leb_gt in HC | apply Z.ltb_ge in HC]; lia.
  - unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Har).
    unfold PCAP_RLO, PCAP_RHI in Hrel.
    destruct Hr as [<- | [<- | []]]; unfold in_zr in Har; cbn [fst snd] in Har; lia.
Qed.
Lemma pcap_G_not_meta : forall a, inG G_HARNESS_U a -> ~ (as_meta_mem pcap_KS <= a < as_meta_mem pcap_KS + 8).
Proof.
  intros a Ha. cbn [pcap_KS as_meta_mem]. unfold PCAP_META_MEM.
  unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Har).
  destruct Hr as [<- | [<- | []]]; unfold in_zr in Har; cbn [fst snd] in Har; lia.
Qed.
Lemma pcap_G_not_ofl : forall a, inG G_HARNESS_U a -> ~ (as_ofl_head pcap_KS <= a < as_ofl_head pcap_KS + 8).
Proof.
  intros a Ha. rewrite pcap_KS_head.
  unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Har).
  destruct Hr as [<- | [<- | []]]; unfold in_zr in Har; cbn [fst snd] in Har; lia.
Qed.
(* The walk lanes' HGSRC (a Theorem Labs lane, lib/B/Prog/PcapEntryOpen.v:2919) at PI_pcap and pcap_KS. *)
Lemma pcap_G_harness_src {rc : YM05.RunCeil} : forall a, inG (@pe_G rc PI_pcap) a -> ~ asrc_env_addr pcap_KS a.
Proof.
  intros a Ha. rewrite pi_pcap_pe_G in Ha.
  unfold asrc_env_addr. cbn [pcap_KS as_threaded as_need_locks as_ofl_lock as_mode as_rwa as_canary].
  unfold PCAP_THREADED, PCAP_NEED_LOCKS, PCAP_OFL_LOCK, PCAP_MODE, PCAP_RWA, PCAP_CANARY.
  unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Har).
  destruct Hr as [<- | [<- | []]]; unfold in_zr in Har; cbn [fst snd] in Har; lia.
Qed.

(* The walk lanes' class ro_below_ofl (PcapBase.v:23; lib/B PcapEntryOpen.v:2136, PcapEntryEnd.v:1481,
   PcapEntryTail.v:137) at this image, for a sink head whose open-file list head is pcap_KS's (0x5f4e88): the
   read-only segments end at 0x99000 and the RELRO window at 0x9a3f0. *)
Lemma pcap_ro_below (SK : YI16.sink_head) : @YI16.sk_ofl_head SK = (symaddr Symbols.AsanUbsan.s_ofl_head) ->
  @ro_below_ofl AsanUbsan.M.loaded_segments PCAP_RLO PCAP_RHI SK.
Proof.
  intros HSK a Hro. rewrite HSK.
  assert (HC : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? (symaddr Symbols.AsanUbsan.s_ofl_head)))
                 AsanUbsan.M.loaded_segments = true)
    by (clear; vm_compute; reflexivity).
  destruct Hro as [(s & Hs & Hw & Hr) | Hrel].
  - rewrite forallb_forall in HC. specialize (HC s Hs). rewrite Hw in HC. cbn [orb] in HC.
    apply Z.leb_le in HC. lia.
  - unfold PCAP_RLO, PCAP_RHI in Hrel. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The contract from the walks                                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

Section top.
Context {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
#[local] Abbreviation SEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation PIp := (@PI_pcap rc).
(* The lanes' SEGS / BASE / RLO / RHI at PI_pcap, written as the lanes write them. *)
#[local] Abbreviation PSEGS := (@pa_segs rc pcap_listing PIp).
#[local] Abbreviation VALp a := (@pa_val rc pcap_listing PIp a).
#[local] Abbreviation RLOp := (@pa_relro_lo rc pcap_listing PIp).
#[local] Abbreviation RHIp := (@pa_relro_hi rc pcap_listing PIp).
#[local] Abbreviation POSTP fx := (@pe_post fx rc SK PIp B MT pcap_KS).
#[local] Abbreviation PFROM fx GI := (@pe_from rc SK PIp B MT pcap_KS (POSTP fx) GI).
#[local] Abbreviation GIx X fx := (X fx rc PIp B MT pcap_KS).

(* ====================== THE PREMISES NOT DISCHARGED IN THIS FILE (one place) ====================== *)

(* (1) The meter. Row 11 instantiates MT := YCbp.ameter_triv and XM_LIB = XN_LIB := fun _ => 0: MTL by
       YCbp.ameter_triv_laws, HXM by PcapEntryDefs.pe_need_triv_budget, HXMN by lia; MTF is the lanes' (Tail's) meter
       law across the file system. *)
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis HXM : forall n, pe_need MT n <= XM_LIB n.
Hypothesis HXMN : forall n, XM_LIB n <= XN_LIB n.

(* (2) The core's B (the asan-ubsan TfibB) and the runtime rules, exactly as the lanes' Section premises state them
       (PcapEntryEntry.v:152-159, PcapEntryOpen.v:124-129, PcapEntryTail.v:131-141): LAWS, TL, TLF, ML, ASF, FFL, and
       the fx-indexed rules ASM1 (astack_malloc_realizes 1), AMALLOC4, AFREE4 (Reusable/YC5d.v, cgif core), which the
       contract needs at every FPState. *)
Hypothesis LAWS : AR_laws PSEGS B.
Hypothesis TL : @PALib rc pcap_listing PIp B.
Hypothesis TLF : @PALibF rc pcap_listing PIp B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law PSEGS B.
Hypothesis FFL : frame_flag_lawP PSEGS B.
Hypothesis ASM1 : forall fx : YK11.FPState, @astack_malloc_realizes fx rc PSEGS B 1.
Hypothesis AMALLOC4 : forall fx : YK11.FPState, @amalloc04_rule fx rc SK PSEGS B MT.
Hypothesis AFREE4 : forall fx : YK11.FPState, @afree04_rule fx rc SK PSEGS B MT.
(* pe_base's B-dependent conjuncts at G_HARNESS_U (lib/A/PcapGHarness.v's facts pcap_G_harness_gx_ok / _pe_bytes, here only
   their B-dependent halves; the image halves are pcap_G_img, pcap_G_not_ro, pcap_G_not_meta above): no byte of the
   harness's globals is an allocator static of B or errno. *)
Hypothesis HGOS : forall a, inG G_HARNESS_U a -> ~ Exists (in_zr a) (as_owned_static B).
Hypothesis HGERR : forall a, inG G_HARNESS_U a -> ~ (as_errno B <= a < as_errno B + 4).
(* pe_base's two trace conjuncts (PcapEntryDefs.v:512-515): this image has no trace universe yet (PcapEntryDefs.v:487:
   pc_malloc_ra0 = 0x52ec4, pc_free_ra0 = 0x52d64, BASE = 0x80788, spine [0x80684]); stated in pe_base's own form for
   a call from target_run (the twin of lib/A's ACejSites.llvmf_site_in over ACej.Tfib_universe). *)
Hypothesis HTRM : forall cx : @ecx rc PIp, raZ (c_regs cx) = RA_LLVMF ->
  forall regsT : bvmap 5 word, In (raZ regsT - VALp A_TEXT) PE_MALLOC_SITES ->
  In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (pch cx)) (as_universe B).
Hypothesis HTRF : forall cx : @ecx rc PIp, raZ (c_regs cx) = RA_LLVMF ->
  forall regsT : bvmap 5 word, In (raZ regsT - VALp A_TEXT) PE_FREE_SITES ->
  In (call_trace0 (pc_free_ra0 (as_code B)) regsT (pch cx)) (as_universe B).

(* (3) pcap_KS (lib/B/Stdio/PSourceK.v) at B: its image laws (PSourceMeta.asource_img_laws) and the file meter
       (PSourceMeter.asrc_file_meter), as the lanes take them. *)
Hypothesis ASIL : asource_img_laws SK PSEGS B pcap_KS.
Hypothesis AFM : @asrc_file_meter rc SK PSEGS B MT.

(* (4) The callee contracts the proved lanes take, at PI_pcap:
       - the fclose wrapper and its two free traces (PcapEntryEnd.v:336-340, PcapSourceClose.v:116-122): with them
         pcap_source_close's contract is PROVED here (PcapSourceClose.pb_pcap_source_closeX), not assumed;
       - pcap_source_next's contract at its window NSTK (PcapEntryOpen.v:2140-2143, PcapEntryTail.v:1839-1841;
         lib/A/Prog/PcapSourceNextSpec.v, a Theorem Labs lane);
       - __asan_memcpy / __asan_memset at their entries (aintrin_realizes, Reusable/YG0d.v:318;
         PcapEntryOpen.v:2940-2941);
       - pcap_source_open's contract and its call-site facts at each of its two call sites: PP_K2 (cut A,
         PcapEntryOpen.v:2942-2955: HOPEN, HROI_K2, HCTX_K2, HFMU_K2 over FM_RA_K2 / CTX_K2 / ROI_K2) and PP_K7 (R1,
         PcapEntryTail.v:2419-2432: OPENS, HROI, HCTX, HFMU over FM_RA / CTX / ROI). Each lane quantifies its own
         FM_RA / CTX / ROI, and the open contract is not monotone in CTX or ROI, so the two sites keep separate
         variables (a discharger may pass the same three to both); HPATH names no variable and is shared.
         lib/B/Prog/PcapSourceOpen.v pb_pcap_source_openX_of gives the contract, whose own premises are open. *)
Variables ra_fc1 ra_fc2 : Z.
Hypothesis AFCLOSE : forall fx : YK11.FPState,
  @PFclose.afclose_source_spec fx rc SK PSEGS B pcap_KS
    (@pa_sigma rc pcap_listing PIp PS___interceptor_trampoline_fclose) ra_fc1 ra_fc2 RLOp RHIp.
Hypothesis HUfc1 : In [pc_free_ra0 (as_code B); ra_fc1] (as_universe B).
Hypothesis HUfc2 : In [pc_free_ra0 (as_code B); ra_fc2] (as_universe B).
Variable NSTK : Z.
Hypothesis HNSTK : 0 <= NSTK <= 32368.
Hypothesis HNEXT : forall fx : YK11.FPState,
  @PcapEntryCalls.AN.tpcap_source_next_specX fx rc SK PSEGS RLOp RHIp NSTK B MT pcap_KS
    (VALp A_TEXT + AF_pcap_source_next).
Hypothesis HMCPY : forall fx : YK11.FPState,
  @aintrin_realizes fx rc PSEGS B OCpy (@pa_sigma rc pcap_listing PIp PS___asan_memcpy).
Hypothesis HMSET : forall fx : YK11.FPState,
  @aintrin_realizes fx rc PSEGS B OSet (@pa_sigma rc pcap_listing PIp PS___asan_memset).
(* The bcmp interceptor at its trampoline (abcmp_realizes, Reusable/YG0d.v:353), for the record checks' three bcmp
   calls (0x80c94, 0x80cc4, 0x80d40; lib/B/Prog/PcapEntryRec.v:722). *)
Hypothesis ABCMP : forall fx : YK11.FPState,
  @abcmp_realizes fx rc PSEGS B (@pa_sigma rc pcap_listing PIp PS___interceptor_trampoline_bcmp).
Variable FM_RA_K2 : Z.
Variable CTX_K2 : list (list Z).
Variable ROI_K2 : (word -> option byte) -> Prop.
Hypothesis HOPEN : forall fx : YK11.FPState,
  @PcapEntryCalls.AO.tpcap_source_open_specX fx rc SK PSEGS RLOp RHIp (VALp (A_OBJ 3)) (VALp (A_OBJ 4))
    (VALp (A_OBJ 2)) ROI_K2 B pcap_KS MT FM_RA_K2 CTX_K2 (VALp A_TEXT + AF_pcap_source_open).
Hypothesis HROI_K2 : forall (W : world PSEGS) mem,
  arodata_okP PSEGS RLOp RHIp B (aview PSEGS (w_H W) mem) -> ROI_K2 (mrestrict (w_H W) mem).
Hypothesis HCTX_K2 : In [VALp A_TEXT + PP_K2; RA_LLVMF] CTX_K2 /\ In [VALp A_TEXT + PP_K2] CTX_K2.
Hypothesis HFMU_K2 : In [pc_malloc_ra0 (as_code B)] (as_universe B) /\
  (forall c, In c CTX_K2 -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
     flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (FM_RA_K2 :: c))) (as_universe B)).
Variable FM_RA : Z.
Variable CTX : list (list Z).
Variable ROI : (word -> option byte) -> Prop.
Hypothesis OPENS : forall fx : YK11.FPState,
  @PcapEntryCalls.AO.tpcap_source_open_specX fx rc SK PSEGS RLOp RHIp (VALp (A_OBJ 3)) (VALp (A_OBJ 4))
    (VALp (A_OBJ 2)) ROI B pcap_KS MT FM_RA CTX (VALp A_TEXT + AF_pcap_source_open).
Hypothesis HROI : forall (W : world PSEGS) mem,
  arodata_okP PSEGS RLOp RHIp B (aview PSEGS (w_H W) mem) -> ROI (mrestrict (w_H W) mem).
Hypothesis HPATH : forall ly S0 (W : world PSEGS) mem md, AR PSEGS B ly S0 W mem md ->
  range_addressable (aview PSEGS (w_H W) mem) SHADOW_OFF (VALp (A_OBJ 3)) 13 /\
  shadow_hull_vis (aview PSEGS (w_H W) mem) (VALp (A_OBJ 3)) 13.
Hypothesis HCTX : In [VALp A_TEXT + PP_K7; RA_LLVMF] CTX /\ In [VALp A_TEXT + PP_K7] CTX.
Hypothesis HFMU : In [pc_malloc_ra0 (as_code B)] (as_universe B) /\
  (forall c, In c CTX -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
     flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (FM_RA :: c))) (as_universe B)).

(* ========================================================================================== *)

(* The composition: the proved lane lemmas, from the end of the walk back to its first slot. Every phase is proved;
   what remains open is the premises above. ro_below_ofl is the contract's: its pre fixes the sink head's ofl head
   (pcap_ro_below). *)
Lemma pcap_entry_start : forall fx : YK11.FPState, @ro_below_ofl SEGS PCAP_RLO PCAP_RHI SK ->
  @pe_start fx rc SK PIp B MT pcap_KS (POSTP fx).
Proof.
  intros fx HRO.
  (* pcap_source_close at this image, proved (lib/B/Prog/PcapSourceClose.v). *)
  pose proof (@PcapSourceClose.pb_pcap_source_closeX fx rc SK PIp B pcap_KS MT LAWS TL ra_fc1 ra_fc2 (AFCLOSE fx)
    HUfc1 HUfc2 ASIL AFM) as CLOSE.
  (* L6 Tail: PP_K6 -> R1 .. R7 -> pe_post; PP_K12r and PP_leave -> pe_post. *)
  pose proof (@PcapEntryTail.pe_from_K6_post fx rc SK PIp B MT pcap_KS LAWS TL MTL ASIL (AFREE4 fx) CLOSE HRO ML ASF
    FFL MTF NSTK HNSTK (HNEXT fx) FM_RA CTX ROI (OPENS fx) HROI HPATH HCTX HFMU) as H6.
  pose proof (@PcapEntryTail.pe_from_K12r_post fx rc SK PIp B MT pcap_KS LAWS MTL ASIL ML ASF FFL MTF) as H12r.
  pose proof (@PcapEntryTail.pe_from_leave_post fx rc SK PIp B MT pcap_KS LAWS MTL ASIL ML ASF FFL MTF) as HLV.
  (* L5 End: PP_K5 -> the end-of-walk loop -> pcap_source_close -> PP_K6. *)
  pose proof (@PcapEntryEnd.pe_from_K5_K6 fx rc SK PIp B MT pcap_KS LAWS TL ASIL AFM ra_fc1 ra_fc2 (AFCLOSE fx)
    HUfc1 HUfc2 pi_pcap_glen (POSTP fx) MTL HRO H6) as H5.
  (* L3 / L4, the record loop, closed by the measure |F| - s10 (PcapEntryRec.pe_recloop); its NSTK_OK is HNSTK. *)
  pose proof (@PcapEntryRec.pe_recloop fx rc SK PIp B MT pcap_KS LAWS TL ASIL (ABCMP fx) HRO NSTK HNSTK MTL (HNEXT fx)
    (POSTP fx) H5) as H4.
  (* L3 Skip: PP_KD -> PP_K4 / PP_K5. *)
  pose proof (@PcapEntrySkip.pe_from_KD fx rc SK PIp B MT pcap_KS LAWS ASIL (POSTP fx) H4 H5) as HD.
  (* L2 Open, all five cuts proved (PcapEntryOpen.pe_from_open): PP_K1 -> A -> M -> B_acc / B_ref -> C -> PP_KD,
     PP_K12r. Its image facts HG42 / HGW / HGSRC are pi_pcap_g42, HGW_B and pcap_G_harness_src above. *)
  pose proof (@PcapEntryOpen.pe_from_open fx rc SK PIp B MT pcap_KS LAWS TL MTL ASIL (AFREE4 fx) (AMALLOC4 fx) HRO
    NSTK HNSTK (HNEXT fx) (@pi_pcap_g42 rc) (@HGW_B rc) (@pcap_G_harness_src rc) (HMCPY fx) (HMSET fx)
    FM_RA_K2 CTX_K2 ROI_K2 (HOPEN fx) HROI_K2 HPATH HCTX_K2 HFMU_K2 (POSTP fx) HD H12r) as HK1.
  (* L1 Entry: PP_entry -> GI_SM (pe_start_SM) -> E / EARLY (PcapEntryEntry.pe_from_SM_ok) -> PP_K1 / PP_leave. Its
     image facts HHI8 / HG42 / HGW / HGSRC are pi_pcap_glen, pi_pcap_g42, HGW_B and pcap_G_harness_src above. *)
  pose proof (@PcapEntryEntry.pe_from_SM_ok fx rc SK PIp B MT pcap_KS LAWS TL MTL ASIL (AMALLOC4 fx)
    (@pi_pcap_glen rc) (@pi_pcap_g42 rc) (@HGW_B rc) (@pcap_G_harness_src rc)) as HSM.
  exact (@PcapEntryEntry.pe_start_entry_of fx rc SK PIp B MT pcap_KS LAWS TL TLF ML (ASM1 fx) AFM ASIL HSM
    (POSTP fx) HK1 HLV).
Qed.

(* The context of the call, as the entry contract hands it over. *)
Definition top_cx (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (p : Z) (pl : list byte) (M T : Z) : @ecx rc PIp :=
  mkECX (PI := PIp) ly S W regs mem md p pl (pe_sp1 (spZ regs)) (Ereg regs []) M T.

(* gx_ok for the harness's globals: image bytes (pcap_G_img) outside B's statics (HGOS). *)
Lemma pcap_G_gx : gx_ok SEGS B G_HARNESS_U.
Proof. intros a Ha. exact (conj (pcap_G_img a Ha) (HGOS a Ha)). Qed.

(* pe_base from the contract's pre at the lib/B instance. *)
Lemma pe_base_of_pre : forall ly S (W : world SEGS) regs mem md p n pl M,
  @PEG.tfib_lib_pre_x rc SK SEGS PCAP_RLO PCAP_RHI RA_LLVMF A_EMPTY LLVMF_STK B MT XM_LIB pcap_KS
    regs ly S W mem md p n pl M ->
  pe_base SK B MT pcap_KS (top_cx ly S W regs mem md p pl M (XM_LIB n)).
Proof.
  intros ly S W regs mem md p n pl M HPRE.
  unfold PEG.tfib_lib_pre_x in HPRE.
  destruct HPRE as (HFN & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr & Hev & Hlive & HROS & HSRC & HHEAD & HFD & HNAMES &
                    HSORT & HAM & HMOK).
  pose proof (HTRM (top_cx ly S W regs mem md p pl M (XM_LIB n)) Hra) as HTR1.
  pose proof (HTRF (top_cx ly S W regs mem md p pl M (XM_LIB n)) Hra) as HTR2.
  unfold top_cx in HTR1, HTR2. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_pl c_sp1 c_E0 c_M c_T] in HTR1, HTR2.
  unfold pe_base, top_cx, c_n. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_pl c_sp1 c_E0 c_M c_T].
  rewrite <- Hnpl.
  split; [exact HFN|]. split; [exact Hra|]. split; [exact Hp|]. split; [exact Hn|].
  split; [exact Hpn|]. split; [exact HPL|]. split; [exact Hfr|].
  split; [exact Hev|]. split; [exact Hlive|].
  split; [exact HROS|].
  split; [exact HSRC|]. split; [exact HHEAD|]. split; [exact HAM|].
  split; [reflexivity|].
  split; [intros m0 r Hm0; exact (ew_Ereg_nat regs _ m0 r Hm0)|].
  split; [exact (f_equal (fun w => bv_unsigned w) (ew_Ereg_nat regs [] 2 (2%bv : bv 5) eq_refl))|].
  split; [exact HMOK|]. split; [exact (HXM n)|].
  split; [rewrite pi_pcap_pe_G; exact pcap_G_gx|].
  (* The per-byte conjunct: the image facts above, B's errno (HGERR) and the open-file-list head. AOFL_HEAD is the
     sink head's field, fixed by the pre: as_ofl_head pcap_KS = AOFL_HEAD, and as_ofl_head pcap_KS = 0x5f4e88
     (PSourceK.pcap_KS_head); G_HARNESS_U is .bss [0x5d3e40, 0x5d3e48) and [0x5d3e60, 0x5d3e68). *)
  split.
  { intros a Ha. rewrite pi_pcap_pe_G in Ha.
    split; [exact (pcap_G_not_ro a Ha)|]. split; [exact (pcap_G_not_meta a Ha)|]. split; [exact (HGERR a Ha)|].
    rewrite <- HHEAD. exact (pcap_G_not_ofl a Ha). }
  exact (conj HTR1 HTR2).
Qed.

Lemma top_notG : forall a, 0 <= a < 2 ^ 64 -> ~ inG G_HARNESS_U a ->
  inGb G_HARNESS_U (bv_unsigned (Z_to_bv 64 a)) = false.
Proof. intros a Ha Hn. rewrite unsigned_lit_small by lia. apply inGb_false. exact Hn. Qed.

(* The meta region at the end of a gx journal (lib/A/Prog/PcapEntryTop.v top_meta_end, at this image). *)
Lemma top_meta_end : forall (W : world SEGS) mem memS ly S md own ly' S' W' mem' md' k STK sp0 FP M,
  asrc_meta_inv SEGS pcap_KS ly (mrestrict (w_H W) mem) M ->
  ajournal SEGS B STK sp0 FP ly S W memS md own ly' S' W' mem' md' k ->
  gagree G_HARNESS_U (w_H W) mem memS ->
  asrc_meta_inv SEGS pcap_KS ly' (mrestrict (w_H W') mem') M.
Proof.
  intros W mem memS ly S md own ly' S' W' mem' md' k STK sp0 FP M (HX & Himg & Hp & Hm & H0 & H47 & Hal & HZ) HJ HAG.
  pose proof HJ as (HAR' & Hly & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _ & _ & _ & _ & F5 & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
  assert (HX' : In (M, AMETA_SIZE) (ly_extra ly')) by (rewrite Eextra; exact HX).
  split; [exact HX'|]. split; [exact Himg|]. split; [exact (asrc_meta_ptr_of_AR SK SEGS B pcap_KS ASIL _ _ _ _ _ HAR')|].
  split.
  - eapply val_mem_frame; [|exact Hm]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply mbyte_kept_of_aview.
    destruct (asil_meta _ _ _ _ ASIL x ltac:(lia)) as (Hi & Hns & He & Hlt).
    rewrite (F3 x Hi Hns He) by (apply fp_spares_below; exact Hlt).
    apply (aview_gagree SEGS G_HARNESS_U _ _ _ x HAG). apply top_notG.
    + pose proof (pcap_segs_low x Hi). unfold kLowMemEnd in *. lia.
    + intros Hin. apply (pcap_G_not_meta x Hin). lia.
  - split; [exact H0|]. split; [exact H47|]. split; [exact Hal|].
    intros a Ha. rewrite <- (HZ a Ha). apply mbyte_kept_of_aview.
    rewrite F5.
    + apply (aview_gagree SEGS G_HARNESS_U _ _ _ a HAG). apply top_notG; [unfold AMETA_SIZE in *; lia|].
      intros Hin. pose proof (pcap_G_img a Hin) as Hi. pose proof (Himg a Hi). lia.
    + apply Exists_exists. exists (M, AMETA_SIZE). split; [exact HX | unfold in_zr; cbn [fst snd]; lia].
    + intros He. pose proof (asil_errno_img _ _ _ _ ASIL a He) as Hi.
      destruct (AR_extra_law_ok SEGS B ly' S' W' mem' md' a HAR'
        ltac:(apply Exists_exists; exists (M, AMETA_SIZE); split; [exact HX' | unfold in_zr; cbn [fst snd]; lia]))
        as (_ & _ & _ & _ & Hni & _).
      exact (Hni Hi).
Qed.

(* pe_post to the contract's post at the lib/B instance, with l := LL 0 (m_fs md) (PWalk.OUT pl). *)
Lemma post_of_pe_post : forall (fx : YK11.FPState) ly S (W : world SEGS) regs mem md p n pl M W' c',
  @PEG.tfib_lib_pre_x rc SK SEGS PCAP_RLO PCAP_RHI RA_LLVMF A_EMPTY LLVMF_STK B MT XM_LIB pcap_KS
    regs ly S W mem md p n pl M ->
  POSTP fx (top_cx ly S W regs mem md p pl M (XM_LIB n)) W' c' ->
  exists ly' S' regs' mem' md' k, c' = @cfg_at fx SEGS RA_LLVMF regs' mem' md' /\
    @PEG.tfib_lib_post_x rc SK SEGS LLVMF_STK G_HARNESS_U B MT XN_LIB pcap_KS regs ly S W mem md p n pl M
      (LL 0 (m_fs md) (OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.OUT pl)) ly' S' W' regs' mem' md' k.
Proof.
  intros fx ly S W regs mem md p n pl M W' c' HPRE HPOST.
  unfold PEG.tfib_lib_pre_x in HPRE.
  destruct HPRE as (HFN & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr & Hev & Hlive & HROS & HSRC & HHEAD & HFD & HNAMES &
                    HSORT & HAM & HMOK).
  unfold pe_post, top_cx in HPOST. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_pl c_T] in HPOST.
  destruct HPOST as (ly' & S' & regs' & mem' & md' & k & Ec & HJ & Hk & HPR & Ha0 & HPerm & Efds & Efs & HSRC' & HMLE &
                     HFkeep).
  exists ly', S', regs', mem', md', k. split.
  { rewrite Ec. unfold cfg_at. f_equal. f_equal. all: try reflexivity.
    unfold w64. rewrite <- Hra. unfold raZ. symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof HJ as (_ & _ & (memS & HJi & HAG) & _).
  unfold PEG.tfib_lib_post_x. cbn [ll_fs ll_ret ll_out].
  split; [exact HJ|].
  split; [exact Hk|]. split; [exact HPR|]. split; [exact Ha0|]. split; [exact HPerm|].
  split; [intros fd; rewrite Efds; reflexivity|].
  split; [rewrite Efds; exact HNAMES|].
  split; [exact Efs|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HSORT|].
  split; [exact HSRC'|].
  split; [exact (top_meta_end W mem memS ly S md [] ly' S' W' mem' md' k _ _ _ M HAM HJi HAG)|].
  split; [exact (mle_weaken MT S S' (XM_LIB n) (XN_LIB n) MTL HMLE (HXMN n))|].
  intros i Hi. apply HFkeep. unfold c_n. cbn [c_pl]. lia.
Qed.

(* Row 11, asan-ubsan: the entry contract at the lib/B instance. *)
Theorem pcap_entry_top : tfib_lib_contract_x_all_B SK B MT XM_LIB XN_LIB pcap_KS.
Proof.
  unfold tfib_lib_contract_x_all_B, PEG.tfib_lib_contract_x_all, PEG.tfib_lib_contract_x.
  intros fx ly S W regs mem md p n pl M K HAI HPRE HK.
  pose proof (pe_base_of_pre ly S W regs mem md p n pl M HPRE) as HB.
  (* The pre fixes the sink head's open-file list head at pcap_KS's, so the read-only data lies below it. *)
  assert (HRO : @ro_below_ofl SEGS PCAP_RLO PCAP_RHI SK).
  { apply pcap_ro_below. pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHEAD & _).
    unfold AOFL_HEAD in HHEAD. rewrite pcap_KS_head in HHEAD. symmetry. exact HHEAD. }
  change (@LIBK (OSSVerify.Proofs.libreac.fuzz_pcap.lib.OutForm.out_shape
            OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.OUT) pl (m_fs md) K)
    with (wr ch_stderr (OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.OUT pl)
            (K (LL 0 (m_fs md) (OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.OUT pl)))).
  set (l0 := LL 0 (m_fs md) (OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.OUT pl)).
  rewrite pcap_OUT_nil. unfold wr. cbn [map].
  assert (HS : srealizes SEGS (@cfg_at fx SEGS A_LLVMF regs mem md) (K l0)).
  { refine (pcap_entry_start fx HRO (top_cx ly S W regs mem md p pl M (XM_LIB n)) HB HAI (K l0) _).
    intros W' c' Hwle HAI' HPOST.
    apply (HK l0 W' c' Hwle HAI').
    exact (post_of_pe_post fx ly S W regs mem md p n pl M W' c' HPRE HPOST). }
  eapply srz_conseq; [exact HS|]. apply t_eq_sym. apply t_emit_nil_eq. exact (srealizes_nonempty SEGS _ _ HS).
Qed.

End top.
(* SK stays explicit on the exported theorem (a Theorem Labs lane, 21:57Z): the only global sink_head instance in this
   closure is the plain build's. *)
Arguments pcap_entry_top {rc} SK.
