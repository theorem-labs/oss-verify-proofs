From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_pcap (v1.9.0, ASan build) from proofs/cgif/cgif_file_fuzzer/lib/A/ACef.v, A/AI12.v and A/ACbj.v (the listing's image instance, in the form libreac/fuzz_grant's lib/A/Prog/GrantImg.v gives it, a working branch) and A/ACfh.v, A/ACfj.v and A/ACfi.v (the bridge from the entry walk to the contract, in the form libreac/fuzz_grant's lib/A/Prog/GrantLibX.v gives it): the code table of fuzz_pcap.asan's program code (0x80738, 1521 words, the span of PcapList.pcap_listing), the value table over PcapAddr.v, the instance PI_pcap of PcapPa.PAImg with its named equalities, pe_base from the contract's pre, the composition of the harness walks into pe_start, and pe_post to the contract's post. The meta region at the end is a Theorem Labs lane's h_meta_gx (a working branch 4259db10ddc), restated over explicit premises. *)
(* The ASan build's entry contract for fuzz_pcap, row 11: PcapEntryA.tfib_lib_contract_x_all_A, proved from the walks of
   LLVMFuzzerTestOneInput (0x807c8) phase by phase.

   Everything not on a working branch yet is a Section hypothesis of Section top, in ONE place below, with
   the lane or owner that discharges it. KS is PSourceK.pcap_KS (the meta cell of pe_base's per-byte conjunct is
   computed from it in a Theorem Labs lane's pcap_G_harness_pe_bytes). The callee theorems (pcap_source_open / _next / _close,
   libreac_fuzz_fopen) and the runtime rules enter through the walk hypotheses: each walk hypothesis is its lane
   lemma's type at PI_pcap and POST := pe_post with the lane's own Section premises applied, and the comment beside it
   names those premises (a Theorem Labs lane, 2026-10-29: the open / fopen / next statement files diverged across branches when this
   file was written; CLOSE is treated the same way for uniformity).

   Discharges: a Theorem Labs lane's two lemmas are on a working branch 4e35129c9d1 (a working branch 3c32fe5f906 is retired), lib/A/PcapGHarness.v
   (pcap_G_harness_gx_ok B TB, pcap_G_harness_pe_bytes B TB, from PcapSyms B, A/AF0m.v); its third, pcap_hg_img_laws,
   discharges two premises of lib/A/Prog/PcapSourceOpen.v (HGRO and HGX, the fields hg_ro and hg_glob of the hg_img_laws record that pcap_hg_img_laws proves) and enters through pe_A / tail_R1. The instance equality pi_pcap_glen is the
   harness lanes' HGLEN. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapEntry PcapEntryA PcapEntryDefs PcapEntryPhases.
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase PcapRelro PcapRelroA.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PSourceK.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require OutForm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require PWalk.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require ACej.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journal.
(* seg_wbyte and writable_of_seg (lib/AllocCut.v:264, :277), for pe_base's writable conjunct over G_HARNESS. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require AllocCut.
From OSSVerify.libreac.fuzz_pcap.images Require Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapEntry PcapEntryA PcapEntryDefs PcapEntryPhases.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The listing's image: fuzz_pcap.asan v1.9.0 (GrantImg.v's form)                                  *)
(* ---------------------------------------------------------------------------------------------- *)

(* The code table: every word of the program code the listing covers, from libreac_fuzz_fopen to the last word of
   pcap_source_close, counted from Symbols.v (v1.9.0: 0x80738 to 0x81ef8, 1521 words), the length of
   PcapList.pcap_listing. *)
Definition pcap_lib_count : nat :=
  symwords Symbols.Asan.s_libreac_fuzz_fopen (Symbols.Asan.s_pcap_source_close + Symbols.Asan.Size.s_pcap_source_close).
Definition pcaptbl : ctable :=
  Eval vm_compute in (build_table Asan.M.loaded_segments pcap_text pcap_lib_count TEmpty).
Lemma pcaptbl_eq : pcaptbl = build_table Asan.M.loaded_segments pcap_text pcap_lib_count TEmpty.
Proof. vm_cast_no_check (eq_refl pcaptbl). Qed.
Lemma pcaptbl_ok : table_ok Asan.M.loaded_segments pcaptbl.
Proof. rewrite pcaptbl_eq. apply build_table_ok0. cbv. discriminate. Qed.

(* The value table: the listing's base, its 17 objects and its 27 auipc values (PcapAddr.v). *)
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
  - unfold pcap_hi. generalize (a - A_HI 0)%nat as m. intros m. do 28 (destruct m as [|m]; [zlit|]). zlit.
Qed.

Lemma pcap_B_ok : 0 <= pcap_val A_TEXT /\ pcap_val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ pcap_val A_TEXT mod 4 = 0.
Proof. unfold pcap_val, pcap_text, A_TEXT. cbn. split; [lia|]. split; [lia | reflexivity]. Qed.

Lemma pcap_wx : wx_segs_nowrap Asan.M.loaded_segments.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* The four loaded segments, page-aligned in the image module: (0x10000, 0x1f000), (0x2f000, 0x6a000),
   (0x99000, 0x2000), (0x9b000, 0x55c000). *)
Lemma pcap_segs_low : forall a, in_img Asan.M.loaded_segments a -> 0 <= a < kLowMemEnd.
Proof.
  intros a (sg & Hin & Hr). unfold kLowMemEnd.
  assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
    (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) Asan.M.loaded_segments)).
  { exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) Asan.M.loaded_segments sg Hin). }
  remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
  vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.

Lemma pcap_img_range : forall a, in_img Asan.M.loaded_segments a -> 0x10000 <= a < pcap_img_end.
Proof.
  intros a (sg & Hin & Hr). unfold pcap_img_end, IMG_TOP.
  assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
    (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) Asan.M.loaded_segments)).
  { exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) Asan.M.loaded_segments sg Hin). }
  remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
  vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.

Lemma pcap_relro_img : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img Asan.M.loaded_segments a.
Proof.
  intros a Ha. destruct pcap_relro_in_image as (s & Hs & H1 & H2 & H3). exists s. split; [exact Hs | lia].
Qed.

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

Lemma pcap_img_cover : forall ly S md, ALedger Asan.M.loaded_segments ly S md ->
  fst (ly_img ly) <= 0x10000 /\ pcap_img_end <= fst (ly_img ly) + snd (ly_img ly).
Proof.
  intros ly S md LG. unfold pcap_img_end, IMG_TOP. split.
  - destruct (al_img _ _ _ _ LG Asan.Asan_segment_000 ltac:(left; reflexivity)) as [H _]. cbn in H. lia.
  - destruct (al_img _ _ _ _ LG Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H]. cbn in H. lia.
Qed.

(* The listing's image instance: fuzz_pcap.asan v1.9.0, its read-only window PcapRelro.v's. *)
Definition PI_pcap : PAImg pcap_listing := {|
  pa_segs := Asan.M.loaded_segments;
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

(* ---- the instance's named equalities (a Theorem Labs lane ruling 00:36Z) ---- *)
Lemma pi_pcap_segs : @pa_segs rc pcap_listing PI_pcap = Asan.M.loaded_segments.
Proof. reflexivity. Qed.
Lemma pi_pcap_obj2 : @pa_val rc pcap_listing PI_pcap (A_OBJ 2) = (symaddr Symbols.Asan.s_g_file).
Proof. vm_compute. reflexivity. Qed.
Lemma pi_pcap_obj4 : @pa_val rc pcap_listing PI_pcap (A_OBJ 4) = (symaddr Symbols.Asan.s_g_file_len).
Proof. vm_compute. reflexivity. Qed.
Lemma pi_pcap_relro : @pa_relro_lo rc pcap_listing PI_pcap = PCAP_RLO /\ @pa_relro_hi rc pcap_listing PI_pcap = PCAP_RHI.
Proof. split; reflexivity. Qed.
(* The harness lanes' HGLEN: g_file_len is the auipc value 8 (0x5d3928) + 0x618 (0x80938, 0x809a4, 0x80d1c). *)
Lemma pi_pcap_glen : @pa_val rc pcap_listing PI_pcap (A_HI 8) + PE_GLEN_LO = @pa_val rc pcap_listing PI_pcap (A_OBJ 4).
Proof. vm_compute. reflexivity. Qed.
Lemma pi_pcap_text : @pa_val rc pcap_listing PI_pcap A_TEXT = pcap_text.
Proof. reflexivity. Qed.
Lemma pi_pcap_pe_G : @pe_G rc PI_pcap = G_HARNESS.
Proof. vm_compute. reflexivity. Qed.
(* The entry slot of the listing is LLVMFuzzerTestOneInput. *)
Lemma pi_pcap_entry : @pa_val rc pcap_listing PI_pcap A_TEXT + PP_entry = A_LLVMF.
Proof. vm_compute. reflexivity. Qed.

End inst.

(* The 16 bytes of G_HARNESS (.bss g_file_len [0x5d3f40, +8) and g_file [0x5d3f60, +8)) lie in a writable segment of
   the image: AllocCut.seg_wbyte (the segment byte, read only when seg_writable) reads each of them, so
   AllocCut.writable_of_seg gives writable_at at every memory. *)
Definition pcap_G_harness_bytes : list Z :=
  flat_map (fun r => map (fun i => fst r + Z.of_nat i) (seq 0 (Z.to_nat (snd r)))) G_HARNESS.
Lemma pcap_G_harness_writable : forall a, inG G_HARNESS a -> forall m, writable_at Asan.M.loaded_segments m a.
Proof.
  intros a Ha m.
  assert (HC : forallb (fun x => match AllocCut.seg_wbyte Asan.M.loaded_segments (Z_to_bv 64 x) with
                                 | Some _ => true | None => false end) pcap_G_harness_bytes = true)
    by (clear; vm_compute; reflexivity).
  assert (Hin : In a pcap_G_harness_bytes).
  { unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Har). unfold in_zr in Har.
    unfold pcap_G_harness_bytes. apply in_flat_map. exists r. split; [exact Hr|]. cbv beta.
    apply in_map_iff. exists (Z.to_nat (a - fst r)). cbv beta. split; [lia | apply in_seq; lia]. }
  rewrite forallb_forall in HC. specialize (HC a Hin). cbv beta in HC.
  destruct (AllocCut.seg_wbyte Asan.M.loaded_segments (Z_to_bv 64 a)) as [b|] eqn:E; [|discriminate].
  exact (AllocCut.writable_of_seg _ m a b E).
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
Local Notation SEGS := Asan.M.loaded_segments.
Local Notation PIp := (@PI_pcap rc).
Local Notation POSTP fx := (@pe_post fx rc SK PIp B MT pcap_KS).
Local Notation PFROM fx GI := (@pe_from rc SK PIp B MT pcap_KS (POSTP fx) GI).
Local Notation GIx X fx := (X fx rc PIp B MT pcap_KS).

(* ===================== THE OBLIGATIONS NOT YET DISCHARGED (one place) ===================== *)

(* (1) The meter. Row 11 instantiates MT := YCbp.ameter_triv and XM_LIB = XN_LIB := fun _ => 0:
       MTL by YCbp.ameter_triv_laws, HXM by PcapEntryDefs.pe_need_triv_budget, HXMN by lia. *)
Hypothesis MTL : ameter_laws MT.
Hypothesis HXM : forall n, pe_need MT n <= XM_LIB n.
Hypothesis HXMN : forall n, XM_LIB n <= XN_LIB n.

(* (2) The core's B (a Theorem Labs lane). pcap_G_harness_gx_ok and pcap_G_harness_pe_bytes: a working branch
       4e35129c9d1 lib/A/PcapGHarness.v, at B with PcapSyms B (A/AF0m.v), tfibsegs = Asan.M.loaded_segments; discharged at
       the instance (lib/A/Prog/PcapEntryInst.v, B := PcapB), with PcapB's facts from core's lib/A/PcapBFacts.v (e4f3f52f52b).
       HMRA / HFRA / HUNIV: B's allocator trace starts and its trace universe (the core's B; a Theorem Labs lane's
       ACej.Tfib_universe, a working branch). *)
Hypothesis pcap_G_harness_gx_ok : gx_ok SEGS B G_HARNESS.
Hypothesis pcap_G_harness_pe_bytes : forall a, inG G_HARNESS a ->
  ~ in_roP SEGS PCAP_RLO PCAP_RHI a /\ ~ (as_meta_mem pcap_KS <= a < as_meta_mem pcap_KS + 8) /\
  ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HMRA : pc_malloc_ra0 (as_code B) = (symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z).
Hypothesis HFRA : pc_free_ra0 (as_code B) = (symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z).
Hypothesis HUNIV : as_universe B = ACej.Tfib_universe.

(* (3) pcap_KS's image laws at B (PSourceMeta.asource_img_laws; the owner of PSourceK.pcap_KS with the core's B). *)
Hypothesis ASIL : asource_img_laws SK SEGS B pcap_KS.

(* (4) The harness walks, at PI_pcap and POST := pe_post. Lane premises are named as each lane's Section
       declares them; LAWS = AR_laws SEGS B, TL = PALib B, RO = ro_below_ofl SEGS pa_relro_lo pa_relro_hi (all core),
       NEXT = tpcap_source_next_specX SK SEGS pa_relro_lo pa_relro_hi NX_STK B MT KS (BASE + AF_pcap_source_next)
       (a working branch lib/A/Prog/PcapSourceNextDefs.v),
       CLOSE = tpcap_source_close_specX SK SEGS pa_relro_lo pa_relro_hi B KS MT (BASE + AF_pcap_source_close)
       (a Theorem Labs lane, a working branch lib/A/Prog/PcapSourceClose.v),
       OPEN = tpcap_source_open_specX (a Theorem Labs lane, a working branch lib/A/Prog/PcapSourceOpenDefs.v) with
       FOPEN (a Theorem Labs lane, lib/A/Prog/PcapFuzzFopenDefs.v) and HGRO / HGX (the fields hg_ro / hg_glob of lib/A/PcapGHarness.v's pcap_hg_img_laws), the runtime rules
       amalloc04_rule / afree04_rule (Reusable/YC5d.v, cgif core), aintrin_realizes / abcmp_realizes /
       astack_malloc_realizes / astack_free_law / frame_flag_lawP (Reusable/YG0d.v, cgif core), and HGLEN
       (pi_pcap_glen above). *)

(* a Theorem Labs lane (entry, E, EARLY): from PP_entry, the frame on the side stack (0x80838) and either the copy of
   the file (malloc 0x80940, NULL test 0x8094c) to PP_K1, or the early return of a 2^26+ input (0x808f0) to PP_leave.
   Not written yet: provisional name and form, not found in a working branch (4259db10ddc + worktree) at
   2026-10-29T02:30Z. Expected premises: astack_malloc_realizes 1, amalloc04_rule, LAWS, TL. *)
Hypothesis pe_E : forall fx : YK11.FPState,
  PFROM fx (GIx (@GI_K1) fx) -> PFROM fx (GIx (@GI_leave) fx) -> @pe_start fx rc SK PIp B MT pcap_KS (POSTP fx).
(* a Theorem Labs lane (A): PP_K1 -> __asan_memcpy 0x80968, __asan_memset 0x8098c -> pcap_source_open 0x8099c -> PP_K2.
   Not written yet (provisional, as above). Expected premises: aintrin_realizes OCpy / OSet, OPEN, FOPEN, HGRO / HGX, HGLEN. *)
Hypothesis pe_A : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K2) fx) -> PFROM fx (GIx (@GI_K1) fx).
(* a Theorem Labs lane (B_acc, B_ref): PP_K2 accept -> malloc 0x80ab8 -> PP_K3; refuse -> free 0x80a84 -> PP_K12r.
   Not written yet (provisional, as above). Expected premises: amalloc04_rule, afree04_rule. *)
Hypothesis pe_B : forall fx : YK11.FPState,
  PFROM fx (GIx (@GI_K3) fx) -> PFROM fx (GIx (@GI_K12r) fx) -> PFROM fx (GIx (@GI_K2) fx).
(* a Theorem Labs lane (C): pe_C, a working branch 4259db10ddc lib/A/Prog/PcapHarnessA.v:832.
   Its Section premises: LAWS, TL, MTL, NEXT, RO, ASIL. *)
Hypothesis pe_C : forall fx : YK11.FPState, PFROM fx (GIx (@GI_KD) fx) -> PFROM fx (GIx (@GI_K3) fx).
(* a Theorem Labs lane (Walk): PP_KD -> PP_K5 through PP_K4, PP_KR, PP_KL2 (bcmp 0x80d8c / 0x80da8 / 0x80e08, next
   0x80fa0). Its loop lemma pe_KL2_at is in a working branch's uncommitted PcapHarnessWalk.v; the phase lemma
   is not written yet (provisional name). Its draft Section premises: LAWS, TL, HGX (gx_ok of pe_G), NEXT (draft). *)
Hypothesis pe_Walk : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K5) fx) -> PFROM fx (GIx (@GI_KD) fx).
(* a Theorem Labs lane (W, R1 .. R7, BT): a working branch 33a8d8aa2c3 lib/A/Prog/PcapHarnessTail.v.
   Its Section premises: LAWS, TL, MLAWS (ameter_laws MT), ASIL, AFREE (afree04_rule), CLOSE, HRO (RO),
   ML (model_laws (as_universe B)), ASF (astack_free_law), FFL (frame_flag_lawP), MFSL (ameter_fs_laws MT).
   tail_W, tail_R1, tail_R2, tail_R4 are not written yet (provisional names; W needs CLOSE, R1 OPEN, R2 / R4 NEXT). *)
Hypothesis tail_W : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K6) fx) -> PFROM fx (GIx (@GI_K5) fx).
Hypothesis tail_R1 : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K7) fx) -> PFROM fx (GIx (@GI_K6) fx).
Hypothesis tail_R2 : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K8) fx) -> PFROM fx (GIx (@GI_K7) fx).
Hypothesis tail_R3 : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K9) fx) -> PFROM fx (GIx (@GI_K8) fx).
Hypothesis tail_R4 : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K10) fx) -> PFROM fx (GIx (@GI_K9) fx).
Hypothesis tail_R5 : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K11) fx) -> PFROM fx (GIx (@GI_K10) fx).
Hypothesis tail_R6 : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K12) fx) -> PFROM fx (GIx (@GI_K11) fx).
Hypothesis tail_R7 : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K12r) fx) -> PFROM fx (GIx (@GI_K12) fx).
Hypothesis tail_K12r : forall fx : YK11.FPState, PFROM fx (GIx (@GI_leave) fx) -> PFROM fx (GIx (@GI_K12r) fx).
Hypothesis tail_leave : forall fx : YK11.FPState,
  @pe_from_ret rc SK PIp B MT pcap_KS (POSTP fx) (GIx (@GI_ret) fx) -> PFROM fx (GIx (@GI_leave) fx).
Hypothesis tail_ret : forall fx : YK11.FPState,
  @pe_from_ret rc SK PIp B MT pcap_KS (POSTP fx) (GIx (@GI_ret) fx).

(* ========================================================================================== *)

(* The composition: the walks, chained from the `ret` back to the first slot. *)
Lemma pcap_entry_start : forall fx : YK11.FPState, @pe_start fx rc SK PIp B MT pcap_KS (POSTP fx).
Proof.
  intros fx.
  pose proof (tail_leave fx (tail_ret fx)) as HLV.
  pose proof (tail_K12r fx HLV) as H12r.
  pose proof (tail_R7 fx H12r) as H12.
  pose proof (tail_R6 fx H12) as H11.
  pose proof (tail_R5 fx H11) as H10.
  pose proof (tail_R4 fx H10) as H9.
  pose proof (tail_R3 fx H9) as H8.
  pose proof (tail_R2 fx H8) as H7.
  pose proof (tail_R1 fx H7) as H6.
  pose proof (tail_W fx H6) as H5.
  pose proof (pe_Walk fx H5) as HD.
  pose proof (pe_C fx HD) as H3.
  pose proof (pe_B fx H3 H12r) as H2.
  pose proof (pe_A fx H2) as H1.
  exact (pe_E fx H1 HLV).
Qed.

(* The context of the call, as the entry contract hands it over (GrantLibX.v grant_cx). *)
Definition top_cx (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (p : Z) (pl : list byte) (M T : Z) : @ecx rc PIp :=
  mkECX (PI := PIp) ly S W regs mem md p pl (pe_sp1 (spZ regs)) (Ereg regs []) M T.

(* pe_base from the contract's pre at the lib/A instance. *)
Lemma pe_base_of_pre : forall ly S (W : world SEGS) regs mem md p n pl M,
  @tfib_lib_pre_x rc SK SEGS PCAP_RLO PCAP_RHI RA_LLVMF A_EMPTY LLVMF_STK B MT XM_LIB pcap_KS
    regs ly S W mem md p n pl M ->
  pe_base SK B MT pcap_KS (top_cx ly S W regs mem md p pl M (XM_LIB n)).
Proof.
  intros ly S W regs mem md p n pl M HPRE.
  unfold tfib_lib_pre_x in HPRE.
  destruct HPRE as (HFN & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr & Hev & Hlive & HROS & HSRC & HHEAD & HFD & HNAMES &
                    HSORT & HAM & HMOK).
  pose proof (pe_traces_of_sites B (top_cx ly S W regs mem md p pl M (XM_LIB n)) Hra pi_pcap_text HMRA HFRA HUNIV)
    as HTR.
  unfold top_cx in HTR. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_pl c_sp1 c_E0 c_M c_T] in HTR.
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
  split; [rewrite pi_pcap_pe_G; exact pcap_G_harness_gx_ok|].
  (* The per-byte conjunct: a Theorem Labs lane's three facts, the open-file-list head (a Theorem Labs lane's clause), the stream
     environment and the writable segment. AOFL_HEAD is the sink head's field, fixed by the pre: as_ofl_head pcap_KS =
     AOFL_HEAD with as_ofl_head pcap_KS = 0x5f4f88 (PSourceK.pcap_KS_head: musl's ofl_head, ofl_lock 0x5f4f80 + 8, in
     musl's .data); the environment cells are PSourceK.pcap_KS's fields (threaded 0x5f4b21, need_locks 0x5f4b23,
     ofl_lock [0x5f4f80, +16), mode [0x20d40, +3), rwa [0x20026, +4), canary [0x5f48d0, +8)); G_HARNESS is .bss
     [0x5d3f40, 0x5d3f48) and [0x5d3f60, 0x5d3f68); writable_at is pcap_G_harness_writable. *)
  split.
  { intros a Ha. rewrite pi_pcap_pe_G in Ha.
    destruct (pcap_G_harness_pe_bytes a Ha) as (G1 & G2 & G3).
    pose proof (pcap_G_harness_writable a Ha) as GW.
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
    rewrite <- HHEAD, pcap_KS_head.
    unfold asrc_env_addr. cbn [pcap_KS as_threaded as_need_locks as_ofl_lock as_mode as_rwa as_canary].
    unfold PCAP_THREADED, PCAP_NEED_LOCKS, PCAP_OFL_LOCK, PCAP_MODE, PCAP_RWA, PCAP_CANARY.
    unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Har).
    split; [|split; [|exact GW]];
      destruct Hr as [<- | [<- | []]]; unfold in_zr in Har; cbn [fst snd] in Har; lia. }
  (* g_file_len (object 4, 0x5d3f40) + 8 <= g_file (object 2, 0x5d3f60): the instance's named equalities. *)
  split; [rewrite pi_pcap_obj4, pi_pcap_obj2; lia|].
  exact HTR.
Qed.

Lemma top_notG : forall a, 0 <= a < 2 ^ 64 -> ~ inG G_HARNESS a -> inGb G_HARNESS (bv_unsigned (Z_to_bv 64 a)) = false.
Proof. intros a Ha Hn. rewrite unsigned_lit_small by lia. apply inGb_false. exact Hn. Qed.

(* The meta region at the end of a gx journal: PSourceMeta.asrc_meta_inv_kept's argument, from the caller's memory
   through the journal's start memory memS (a Theorem Labs lane's h_meta_gx, a working branch 4259db10ddc
   lib/A/Prog/PcapHarnessA.v:176-204, over these premises instead of pe_base). *)
Lemma top_meta_end : forall (W : world SEGS) mem memS ly S md own ly' S' W' mem' md' k STK sp0 FP M,
  asrc_meta_inv SEGS pcap_KS ly (mrestrict (w_H W) mem) M ->
  ajournal SEGS B STK sp0 FP ly S W memS md own ly' S' W' mem' md' k ->
  gagree G_HARNESS (w_H W) mem memS ->
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
    apply (aview_gagree SEGS G_HARNESS _ _ _ x HAG). apply top_notG.
    + pose proof (pcap_segs_low x Hi). unfold kLowMemEnd in *. lia.
    + intros Hin. apply (proj1 (proj2 (pcap_G_harness_pe_bytes x Hin))). lia.
  - split; [exact H0|]. split; [exact H47|]. split; [exact Hal|].
    intros a Ha. rewrite <- (HZ a Ha). apply mbyte_kept_of_aview.
    rewrite F5.
    + apply (aview_gagree SEGS G_HARNESS _ _ _ a HAG). apply top_notG; [unfold AMETA_SIZE in *; lia|].
      intros Hin. destruct (pcap_G_harness_gx_ok a Hin) as [Hi _]. pose proof (Himg a Hi). lia.
    + apply Exists_exists. exists (M, AMETA_SIZE). split; [exact HX | unfold in_zr; cbn [fst snd]; lia].
    + intros He. pose proof (asil_errno_img _ _ _ _ ASIL a He) as Hi.
      destruct (AR_extra_law_ok SEGS B ly' S' W' mem' md' a HAR'
        ltac:(apply Exists_exists; exists (M, AMETA_SIZE); split; [exact HX' | unfold in_zr; cbn [fst snd]; lia]))
        as (_ & _ & _ & _ & Hni & _).
      exact (Hni Hi).
Qed.

(* pe_post to the contract's post at the lib/A instance, with l := LL 0 (m_fs md) (PWalk.OUT pl). *)
Lemma post_of_pe_post : forall (fx : YK11.FPState) ly S (W : world SEGS) regs mem md p n pl M W' c',
  @tfib_lib_pre_x rc SK SEGS PCAP_RLO PCAP_RHI RA_LLVMF A_EMPTY LLVMF_STK B MT XM_LIB pcap_KS
    regs ly S W mem md p n pl M ->
  POSTP fx (top_cx ly S W regs mem md p pl M (XM_LIB n)) W' c' ->
  exists ly' S' regs' mem' md' k, c' = @cfg_at fx SEGS RA_LLVMF regs' mem' md' /\
    @tfib_lib_post_x rc SK SEGS LLVMF_STK G_HARNESS B MT XN_LIB pcap_KS regs ly S W mem md p n pl M
      (LL 0 (m_fs md) (OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.OUT pl)) ly' S' W' regs' mem' md' k.
Proof.
  intros fx ly S W regs mem md p n pl M W' c' HPRE HPOST.
  unfold tfib_lib_pre_x in HPRE.
  destruct HPRE as (HFN & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr & Hev & Hlive & HROS & HSRC & HHEAD & HFD & HNAMES &
                    HSORT & HAM & HMOK).
  unfold pe_post, top_cx in HPOST. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_pl c_T] in HPOST.
  destruct HPOST as (ly' & S' & regs' & mem' & md' & k & Ec & HJ & Hk & HPR & Ha0 & HPerm & Efds & Efs & HSRC' & HMLE &
                     HFkeep).
  exists ly', S', regs', mem', md', k. split.
  { rewrite Ec. unfold cfg_at. f_equal. f_equal. all: try reflexivity.
    unfold w64. rewrite <- Hra. unfold raZ. symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof HJ as (_ & _ & (memS & HJi & HAG) & _).
  unfold tfib_lib_post_x. cbn [ll_fs ll_ret ll_out].
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

(* Row 11: the ASan build's entry contract at the lib/A instance. *)
Theorem pcap_entry_top : tfib_lib_contract_x_all_A SK B MT XM_LIB XN_LIB pcap_KS.
Proof.
  unfold tfib_lib_contract_x_all_A, tfib_lib_contract_x_all, tfib_lib_contract_x.
  intros fx ly S W regs mem md p n pl M K HAI HPRE HK.
  pose proof (pe_base_of_pre ly S W regs mem md p n pl M HPRE) as HB.
  change (@LIBK (OSSVerify.Proofs.libreac.fuzz_pcap.lib.OutForm.out_shape
            OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.OUT) pl (m_fs md) K)
    with (wr ch_stderr (OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.OUT pl)
            (K (LL 0 (m_fs md) (OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.OUT pl)))).
  set (l0 := LL 0 (m_fs md) (OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.OUT pl)).
  rewrite pcap_OUT_nil. unfold wr. cbn [map].
  assert (HS : srealizes SEGS (@cfg_at fx SEGS A_LLVMF regs mem md) (K l0)).
  { refine (pcap_entry_start fx (top_cx ly S W regs mem md p pl M (XM_LIB n)) HB HAI (K l0) _).
    intros W' c' Hwle HAI' HPOST.
    apply (HK l0 W' c' Hwle HAI').
    exact (post_of_pe_post fx ly S W regs mem md p n pl M W' c' HPRE HPOST). }
  eapply srz_conseq; [exact HS|]. apply t_eq_sym. apply t_emit_nil_eq. exact (srealizes_nonempty SEGS _ _ HS).
Qed.

End top.
